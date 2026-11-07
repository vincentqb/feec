module

public import Feec.TimeStepping.Convergence
public import Feec.ForMathlib.Calculus.SecondDifference

/-!
# The leapfrog scheme under a CFL condition

For a bounded **skew** operator `L` (`⟪L x, y⟫ = -⟪x, L y⟫`, e.g. a discrete Hodge wave operator
`Lₕ = dₕ - dₕ*`) the explicit two-step **leapfrog** scheme `uₙ₊₂ = uₙ + 2 τ L uₙ₊₁` (`IsLeapfrog`)
conserves the modified energy `Eₙ = ‖uₙ₊₁‖² + ‖uₙ‖² - 2 τ re ⟪L uₙ, uₙ₊₁⟫` (`leapfrogEnergy`), which
under the **CFL condition** `τ ‖L‖ ≤ c < 1` is equivalent to `‖uₙ₊₁‖² + ‖uₙ‖²`
(`leapfrogEnergy_ge`, `leapfrogEnergy_le`). On finite element spaces `‖Lₕ‖ ≲ h⁻¹` (inverse
estimates), so the condition is `τ ≲ h`: the scheme is stable and second order only under it, with
constants independent of `L`.

## Main results

* `leapfrogEnergy_succ`: the energy identity `Eₙ₊₁ = Eₙ + re ⟪rₙ, eₙ₊₂ + eₙ⟫` for the perturbed
  recursion `eₙ₊₂ = eₙ + 2 τ L eₙ₊₁ + rₙ`;
* **`norm_leapfrog_le`** (stability, `rₙ = 0`):
  `√(1 - c) ‖uₙ‖ ≤ √((1 + c) (‖u₀‖² + ‖u₁‖²))`;
* `norm_succ_le_of_leapfrog`, `norm_le_of_leapfrog` (stability plus consistency, the recursion
  needed only up to the step bounded):
  `√(1 - c) ‖eₙ₊₁‖ ≤ √((1 + c) (‖e₀‖² + ‖e₁‖²)) + Σ_{k<n} ‖rₖ‖ / √(1 - c)`;
* **`norm_leapfrog_sub_exp_le`** (second order): for leapfrog iterates `uₙ` and the exact flow
  `e^{tL} x`, at `t = n τ`,
  `√(1 - c) ‖uₙ - e^{tL} x‖ ≤ √((1 + c) (‖u₀ - x‖² + ‖u₁ - e^{τL} x‖²))`
  `+ t τ² ‖L³ x‖ / (3 √(1 - c))`
  (the residual of the exact orbit is `(e^{τL} - e^{-τL} - 2 τ L) e^{(k+1)τL} x = O(τ³ ‖L³ x‖)`,
  `norm_exp_sub_exp_neg_le`);
* `norm_centredDifference_le`: the centred difference remainder
  `‖f(m + τ) - f(m - τ) - 2 τ f'(m)‖ ≤ τ³ sup ‖f'''‖ / 3`, for comparison trajectories;
* **leapfrog with prescribed boundary degrees of freedom** (`IsDirichletLeapfrogStep`): on a
  finite element space `V` with the fields `V₀` of vanishing boundary DOFs, the step
  `uₙ₊₂ - gₙ₊₂ ∈ V₀`, `⟪uₙ₊₂ - uₙ, v⟫ = 2 τ ⟪A uₙ₊₁, v⟫` on `V₀` is uniquely solvable for every
  `τ` (`existsUnique_isDirichletLeapfrogStep`), and against comparison fields with the same
  boundary DOFs the error obeys the CFL estimate of the skew operator `P₀ A P₀`, `τ ‖A‖ ≤ c < 1`
  (`norm_succ_sub_le_of_isDirichletLeapfrogStep`).

## References

* [P. Joly, *Variational Methods for Time-Dependent Wave Propagation Problems*][Joly2003]
  (leapfrog for second-order hyperbolic problems: discrete energy, CFL stability)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open NormedSpace Finset Set

@[expose] public noncomputable section

namespace Feec.TimeStepping

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  {L : X →L[𝕜] X} {τ c : ℝ}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- `u` is a **leapfrog sequence** for `u' = L u` with time step `τ`:
`uₙ₊₂ = uₙ + 2 τ L uₙ₊₁`. [Joly2003] -/
def IsLeapfrog (L : X →L[𝕜] X) (τ : ℝ) (u : ℕ → X) : Prop :=
  ∀ n, u (n + 2) = u n + ((2 * τ : ℝ) : 𝕜) • L (u (n + 1))

/-- The **modified energy** `‖b‖² + ‖a‖² - 2 τ re ⟪L a, b⟫` of two consecutive leapfrog states
`a = uₙ`, `b = uₙ₊₁`. -/
def leapfrogEnergy (L : X →L[𝕜] X) (τ : ℝ) (a b : X) : ℝ :=
  ‖b‖ ^ 2 + ‖a‖ ^ 2 - 2 * τ * RCLike.re ⟪L a, b⟫

/-- **The leapfrog energy identity**: for skew `L` and `b' = a + 2 τ L b + r`,
`E(b, b') = E(a, b) + re ⟪r, b' + a⟫`; for `r = 0` the energy is conserved. -/
theorem leapfrogEnergy_succ (hL : ∀ x y, ⟪L x, y⟫ = -⟪x, L y⟫) {a b b' r : X}
    (h : b' = a + ((2 * τ : ℝ) : 𝕜) • L b + r) :
    leapfrogEnergy L τ b b' = leapfrogEnergy L τ a b + RCLike.re ⟪r, b' + a⟫ := by
  have h1 := re_inner_sub_add (𝕜 := 𝕜) b' a
  have hd : b' - a = ((2 * τ : ℝ) : 𝕜) • L b + r := by rw [h]; abel
  rw [hd, inner_add_left, inner_smul_left, RCLike.conj_ofReal, _root_.map_add,
    RCLike.re_ofReal_mul, inner_add_right, _root_.map_add] at h1
  have h2 : RCLike.re ⟪L a, b⟫ = -RCLike.re ⟪L b, a⟫ := by
    rw [hL, _root_.map_neg, inner_re_symm]
  unfold leapfrogEnergy
  rw [h2]
  linarith

/-- **CFL coercivity**: `τ ≥ 0`, `τ ‖L‖ ≤ c` give `(1 - c)(‖a‖² + ‖b‖²) ≤ E(a, b)`. -/
theorem leapfrogEnergy_ge (hτ : 0 ≤ τ) (hc : τ * ‖L‖ ≤ c) (a b : X) :
    (1 - c) * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤ leapfrogEnergy L τ a b := by
  have h1 : RCLike.re ⟪L a, b⟫ ≤ ‖L‖ * ‖a‖ * ‖b‖ :=
    (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (L.le_opNorm a) (norm_nonneg _)))
  have h2 : 2 * ‖a‖ * ‖b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have h3 : 2 * τ * RCLike.re ⟪L a, b⟫ ≤ c * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    calc 2 * τ * RCLike.re ⟪L a, b⟫ ≤ 2 * τ * (‖L‖ * ‖a‖ * ‖b‖) := by gcongr
      _ = (τ * ‖L‖) * (2 * ‖a‖ * ‖b‖) := by ring
      _ ≤ c * (2 * ‖a‖ * ‖b‖) := by gcongr
      _ ≤ c * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
        gcongr; exact (mul_nonneg hτ (norm_nonneg _)).trans hc
  unfold leapfrogEnergy
  linarith

/-- **CFL upper bound**: `τ ≥ 0`, `τ ‖L‖ ≤ c` give `E(a, b) ≤ (1 + c)(‖a‖² + ‖b‖²)`. -/
theorem leapfrogEnergy_le (hτ : 0 ≤ τ) (hc : τ * ‖L‖ ≤ c) (a b : X) :
    leapfrogEnergy L τ a b ≤ (1 + c) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h1 : -RCLike.re ⟪L a, b⟫ ≤ ‖L‖ * ‖a‖ * ‖b‖ :=
    (neg_le_abs _).trans ((RCLike.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (L.le_opNorm a) (norm_nonneg _))))
  have h2 : 2 * ‖a‖ * ‖b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have h3 : -(2 * τ * RCLike.re ⟪L a, b⟫) ≤ c * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    calc -(2 * τ * RCLike.re ⟪L a, b⟫) = 2 * τ * -RCLike.re ⟪L a, b⟫ := by ring
      _ ≤ 2 * τ * (‖L‖ * ‖a‖ * ‖b‖) := by gcongr
      _ = (τ * ‖L‖) * (2 * ‖a‖ * ‖b‖) := by ring
      _ ≤ c * (2 * ‖a‖ * ‖b‖) := by gcongr
      _ ≤ c * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
        gcongr; exact (mul_nonneg hτ (norm_nonneg _)).trans hc
  unfold leapfrogEnergy
  linarith

/-- `a² ≤ b² + m (a + b)` with `a, b, m ≥ 0` gives `a ≤ b + m`. -/
private theorem le_add_of_sq_le {a b m : ℝ} (hb : 0 ≤ b) (hm : 0 ≤ m)
    (h : a ^ 2 ≤ b ^ 2 + m * (a + b)) : a ≤ b + m := by
  nlinarith

/-- **Stability plus consistency for leapfrog, up to step `n`** under the CFL condition
`τ ‖L‖ ≤ c < 1`: for skew `L` and `eₖ₊₂ = eₖ + 2 τ L eₖ₊₁ + rₖ` for `k < n`,
`√(1 - c) ‖eₙ₊₁‖ ≤ √((1 + c)(‖e₀‖² + ‖e₁‖²)) + Σ_{k<n} ‖rₖ‖ / √(1 - c)`. [Joly2003] -/
theorem norm_succ_le_of_leapfrog (hL : ∀ x y, ⟪L x, y⟫ = -⟪x, L y⟫) (hτ : 0 ≤ τ)
    (hc : τ * ‖L‖ ≤ c) (hc1 : c < 1) {e r : ℕ → X} {n : ℕ}
    (he : ∀ k < n, e (k + 2) = e k + ((2 * τ : ℝ) : 𝕜) • L (e (k + 1)) + r k) :
    √(1 - c) * ‖e (n + 1)‖ ≤
      √((1 + c) * (‖e 0‖ ^ 2 + ‖e 1‖ ^ 2)) + (∑ k ∈ range n, ‖r k‖) / √(1 - c) := by
  set s := √(1 - c)
  have hs : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = 1 - c := Real.sq_sqrt (by linarith)
  set En : ℕ → ℝ := fun k => leapfrogEnergy L τ (e k) (e (k + 1))
  have hEge : ∀ k, (1 - c) * (‖e k‖ ^ 2 + ‖e (k + 1)‖ ^ 2) ≤ En k := fun k =>
    leapfrogEnergy_ge hτ hc _ _
  have hE0 : ∀ k, 0 ≤ En k := fun k => (by
    have := hEge k
    have : 0 ≤ (1 - c) * (‖e k‖ ^ 2 + ‖e (k + 1)‖ ^ 2) := by
      apply mul_nonneg <;> [linarith; positivity]
    linarith)
  -- `s ‖e k‖ ≤ √(E k)` and `s ‖e (k + 1)‖ ≤ √(E k)`
  have hfst : ∀ k, s * ‖e k‖ ≤ √(En k) := fun k => by
    rw [Real.le_sqrt (by positivity) (hE0 k), mul_pow, hs2]
    nlinarith [hEge k, sq_nonneg ‖e (k + 1)‖]
  have hsnd : ∀ k, s * ‖e (k + 1)‖ ≤ √(En k) := fun k => by
    rw [Real.le_sqrt (by positivity) (hE0 k), mul_pow, hs2]
    nlinarith [hEge k, sq_nonneg ‖e k‖]
  have key : ∀ m ≤ n, √(En m) ≤ √(En 0) + (∑ k ∈ range m, ‖r k‖) / s := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      have hstep := leapfrogEnergy_succ hL (he m (by omega))
      have hb : RCLike.re ⟪r m, e (m + 2) + e m⟫ ≤ ‖r m‖ / s * (√(En (m + 1)) + √(En m)) := by
        refine (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
        have h1 := hsnd (m + 1)
        have h2 := hfst m
        have hn : ‖e (m + 2) + e m‖ ≤ (√(En (m + 1)) + √(En m)) / s := by
          rw [le_div_iff₀ hs]
          calc ‖e (m + 2) + e m‖ * s ≤ (‖e (m + 2)‖ + ‖e m‖) * s := by
                gcongr; exact norm_add_le _ _
            _ = s * ‖e (m + 1 + 1)‖ + s * ‖e m‖ := by ring
            _ ≤ _ := add_le_add h1 h2
        calc ‖r m‖ * ‖e (m + 2) + e m‖ ≤ ‖r m‖ * ((√(En (m + 1)) + √(En m)) / s) := by gcongr
          _ = _ := by ring
      have hsq : √(En (m + 1)) ^ 2 ≤ √(En m) ^ 2 + ‖r m‖ / s * (√(En (m + 1)) + √(En m)) := by
        rw [Real.sq_sqrt (hE0 _), Real.sq_sqrt (hE0 _)]
        have : En (m + 1) = En m + RCLike.re ⟪r m, e (m + 2) + e m⟫ := hstep
        linarith
      have := le_add_of_sq_le (Real.sqrt_nonneg _) (by positivity) hsq
      rw [sum_range_succ, add_div]
      linarith [ih (by omega)]
  have h0 : √(En 0) ≤ √((1 + c) * (‖e 0‖ ^ 2 + ‖e 1‖ ^ 2)) :=
    Real.sqrt_le_sqrt (leapfrogEnergy_le hτ hc _ _)
  linarith [hsnd n, key n le_rfl]

/-- **Stability plus consistency for leapfrog** under the CFL condition `τ ‖L‖ ≤ c < 1`: for
skew `L` and `eₙ₊₂ = eₙ + 2 τ L eₙ₊₁ + rₙ`,
`√(1 - c) ‖eₙ‖ ≤ √((1 + c)(‖e₀‖² + ‖e₁‖²)) + Σ_{k<n} ‖rₖ‖ / √(1 - c)`. [Joly2003] -/
theorem norm_le_of_leapfrog (hL : ∀ x y, ⟪L x, y⟫ = -⟪x, L y⟫) (hτ : 0 ≤ τ)
    (hc : τ * ‖L‖ ≤ c) (hc1 : c < 1) {e r : ℕ → X}
    (he : ∀ n, e (n + 2) = e n + ((2 * τ : ℝ) : 𝕜) • L (e (n + 1)) + r n) (n : ℕ) :
    √(1 - c) * ‖e n‖ ≤
      √((1 + c) * (‖e 0‖ ^ 2 + ‖e 1‖ ^ 2)) + (∑ k ∈ range n, ‖r k‖) / √(1 - c) := by
  have hs : 0 ≤ √(1 - c) := Real.sqrt_nonneg _
  have hr : ∀ m, 0 ≤ (∑ k ∈ range m, ‖r k‖) / √(1 - c) := fun m => by positivity
  cases n with
  | zero =>
    have : √(1 - c) * ‖e 0‖ ≤ √((1 + c) * (‖e 0‖ ^ 2 + ‖e 1‖ ^ 2)) := by
      rw [show √(1 - c) * ‖e 0‖ = √((1 - c) * ‖e 0‖ ^ 2) by
        rw [Real.sqrt_mul (by linarith), Real.sqrt_sq (norm_nonneg _)]]
      have hc0 : 0 ≤ c := (mul_nonneg hτ (norm_nonneg L)).trans hc
      have h0 := mul_nonneg hc0 (sq_nonneg ‖e 0‖)
      have h1 := mul_nonneg hc0 (sq_nonneg ‖e 1‖)
      have h2 := sq_nonneg ‖e 1‖
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith [hr 0]
  | succ m =>
    have hmono : (∑ k ∈ range m, ‖r k‖) / √(1 - c) ≤ (∑ k ∈ range (m + 1), ‖r k‖) / √(1 - c) :=
      div_le_div_of_nonneg_right (by rw [sum_range_succ]; linarith [norm_nonneg (r m)]) hs
    linarith [norm_succ_le_of_leapfrog hL hτ hc hc1 (n := m) fun k _ => he k]

/-- **Stability of leapfrog** under the CFL condition `τ ‖L‖ ≤ c < 1`:
`√(1 - c) ‖uₙ‖ ≤ √((1 + c)(‖u₀‖² + ‖u₁‖²))`, uniformly in `n` and in the skew `L`.
[Joly2003] -/
theorem norm_leapfrog_le (hL : ∀ x y, ⟪L x, y⟫ = -⟪x, L y⟫) (hτ : 0 ≤ τ) (hc : τ * ‖L‖ ≤ c)
    (hc1 : c < 1) {u : ℕ → X} (hu : IsLeapfrog L τ u) (n : ℕ) :
    √(1 - c) * ‖u n‖ ≤ √((1 + c) * (‖u 0‖ ^ 2 + ‖u 1‖ ^ 2)) := by
  have := norm_le_of_leapfrog hL hτ hc hc1 (r := fun _ => 0) (fun n => by simpa using hu n) n
  simpa using this

section Exp

variable [CompleteSpace X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

/-- The leapfrog residual of the exact flow:
`‖e^{τL} y - e^{-τL} y - 2 τ L y‖ ≤ τ³/3 ‖L³ y‖` for skew `L`, `τ ≥ 0`. -/
theorem norm_exp_sub_exp_neg_le (hL : ∀ x y, ⟪L x, y⟫ = -⟪x, L y⟫) (hτ : 0 ≤ τ) (y : X) :
    ‖exp ((τ : 𝕜) • L) y - exp (((-τ : ℝ) : 𝕜) • L) y - ((2 * τ : ℝ) : 𝕜) • L y‖ ≤
      τ ^ 3 / 3 * ‖(L ^ 3) y‖ := by
  have hre : ∀ x, RCLike.re ⟪L x, x⟫ = 0 := fun x => by
    have h1 : RCLike.re ⟪L x, x⟫ = -RCLike.re ⟪x, L x⟫ := by rw [hL x x, _root_.map_neg]
    have h2 := inner_re_symm (𝕜 := 𝕜) x (L x)
    linarith
  have hd : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0 := fun x => (hre x).le
  have hd' : ∀ x, RCLike.re ⟪(-L) x, x⟫ ≤ 0 := fun x => by
    rw [neg_apply, inner_neg_left, _root_.map_neg, hre, neg_zero]
  have T : ∀ M : X →L[𝕜] X, (∀ x, RCLike.re ⟪M x, x⟫ ≤ 0) →
      ‖exp ((τ : 𝕜) • M) y - (y + τ • M y + (τ ^ 2 / 2) • (M ^ 2) y)‖ ≤
        τ ^ 3 / 6 * ‖(M ^ 3) y‖ := fun M hM => by
    have h := norm_exp_sub_taylor_le hM 3 hτ y
    have e : ∑ j ∈ range 3, (τ ^ j / j.factorial) • (M ^ j) y =
        y + τ • M y + (τ ^ 2 / 2) • (M ^ 2) y := by
      simp [sum_range_succ, Nat.factorial]
    rw [e] at h
    convert h using 2
    norm_num [Nat.factorial]
  have h1 := T L hd
  have h2 := T (-L) hd'
  have e2 : exp (((-τ : ℝ) : 𝕜) • L) = exp ((τ : 𝕜) • -L) := by
    rw [smul_neg, ← neg_smul, RCLike.ofReal_neg]
  have hn : ‖(-(L ^ 3)) y‖ = ‖(L ^ 3) y‖ := by rw [neg_apply, norm_neg]
  rw [show (-L) ^ 3 = -(L ^ 3) from Odd.neg_pow ⟨1, rfl⟩ L, show (-L) ^ 2 = L ^ 2 from neg_sq L,
    hn, neg_apply] at h2
  rw [e2]
  have e : exp ((τ : 𝕜) • L) y - exp ((τ : 𝕜) • -L) y - ((2 * τ : ℝ) : 𝕜) • L y =
      (exp ((τ : 𝕜) • L) y - (y + τ • L y + (τ ^ 2 / 2) • (L ^ 2) y)) -
        (exp ((τ : 𝕜) • -L) y - (y + τ • -(L y) + (τ ^ 2 / 2) • (L ^ 2) y)) := by
    simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    push_cast
    module
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  linarith

/-- **Second-order convergence of leapfrog** under the CFL condition `τ ‖L‖ ≤ c < 1`: for skew
`L`, leapfrog iterates `uₙ` and the exact flow, at `t = n τ`,
`√(1 - c) ‖uₙ - e^{tL} x‖ ≤ √((1 + c)(‖u₀ - x‖² + ‖u₁ - e^{τL} x‖²)) + t τ² ‖L³ x‖ / (3 √(1 - c))`,
uniformly in the skew `L`. [Joly2003] -/
theorem norm_leapfrog_sub_exp_le (hL : ∀ x y, ⟪L x, y⟫ = -⟪x, L y⟫) (hτ : 0 ≤ τ)
    (hc : τ * ‖L‖ ≤ c) (hc1 : c < 1) {u : ℕ → X} (hu : IsLeapfrog L τ u) (x : X) (n : ℕ) :
    √(1 - c) * ‖u n - exp (((n * τ : ℝ) : 𝕜) • L) x‖ ≤
      √((1 + c) * (‖u 0 - x‖ ^ 2 + ‖u 1 - exp ((τ : 𝕜) • L) x‖ ^ 2)) +
        n * τ * τ ^ 2 * ‖(L ^ 3) x‖ / (3 * √(1 - c)) := by
  have hd : ∀ z, RCLike.re ⟪L z, z⟫ ≤ 0 := fun z => by
    have h1 : RCLike.re ⟪L z, z⟫ = -RCLike.re ⟪z, L z⟫ := by rw [hL z z, _root_.map_neg]
    have h2 := inner_re_symm (𝕜 := 𝕜) z (L z)
    linarith
  set w : ℕ → X := fun k => exp (((k * τ : ℝ) : 𝕜) • L) x
  set r : ℕ → X := fun k => w k + ((2 * τ : ℝ) : 𝕜) • L (w (k + 1)) - w (k + 2)
  have he : ∀ k, (u (k + 2) - w (k + 2)) =
      (u k - w k) + ((2 * τ : ℝ) : 𝕜) • L (u (k + 1) - w (k + 1)) + r k := fun k => by
    rw [hu k]; simp only [r, _root_.map_sub, smul_sub]; abel
  have hr : ∀ k, ‖r k‖ ≤ τ ^ 3 / 3 * ‖(L ^ 3) x‖ := fun k => by
    have hk : 0 ≤ ((k + 1 : ℕ) : ℝ) * τ := by positivity
    have e1 : w (k + 2) = exp ((τ : 𝕜) • L) (w (k + 1)) := by
      simp only [w]
      rw [show (((k + 2 : ℕ) : ℝ) * τ) = τ + ((k + 1 : ℕ) : ℝ) * τ by push_cast; ring,
        ContinuousLinearMap.exp_ofReal_smul_add]
      rfl
    have e0 : w k = exp (((-τ : ℝ) : 𝕜) • L) (w (k + 1)) := by
      simp only [w]
      rw [show ((k : ℝ) * τ) = -τ + ((k + 1 : ℕ) : ℝ) * τ by push_cast; ring,
        ContinuousLinearMap.exp_ofReal_smul_add]
      rfl
    have e3 : (L ^ 3) (w (k + 1)) = exp ((((k + 1 : ℕ) * τ : ℝ) : 𝕜) • L) ((L ^ 3) x) :=
      congrArg (fun C : X →L[𝕜] X => C x)
        ((ContinuousLinearMap.commute_exp_ofReal_smul L (((k + 1 : ℕ) : ℝ) * τ)).pow_left 3).eq
    have : r k = -(exp ((τ : 𝕜) • L) (w (k + 1)) - exp (((-τ : ℝ) : 𝕜) • L) (w (k + 1)) -
        ((2 * τ : ℝ) : 𝕜) • L (w (k + 1))) := by
      simp only [r]; rw [e1, ← e0]; abel
    rw [this, norm_neg]
    refine (norm_exp_sub_exp_neg_le hL hτ _).trans ?_
    rw [e3]
    gcongr
    exact LumerPhillips.norm_exp_smul_apply_le hd hk _
  have h := norm_le_of_leapfrog hL hτ hc hc1 (e := fun k => u k - w k) he n
  have hw0 : w 0 = x := by simp [w]
  have hw1 : w 1 = exp ((τ : 𝕜) • L) x := by simp [w]
  rw [hw0, hw1] at h
  have hs : 0 < √(1 - c) := Real.sqrt_pos.2 (by linarith)
  have hsum : (∑ k ∈ range n, ‖r k‖) / √(1 - c) ≤ n * τ * τ ^ 2 * ‖(L ^ 3) x‖ / (3 * √(1 - c)) := by
    rw [div_le_div_iff₀ hs (by positivity)]
    have : ∑ k ∈ range n, ‖r k‖ ≤ n * (τ ^ 3 / 3 * ‖(L ^ 3) x‖) := by
      calc ∑ k ∈ range n, ‖r k‖ ≤ ∑ _k ∈ range n, τ ^ 3 / 3 * ‖(L ^ 3) x‖ :=
            sum_le_sum fun k _ => hr k
        _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
    nlinarith
  linarith

end Exp

/-! ### The centred difference -/

section CentredDifference

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **The centred difference remainder** of the leapfrog step: for `f` with derivatives
`f₁, f₂, f₃` on `[m - τ, m + τ]` and `‖f₃‖ ≤ B`,
`‖f(m + τ) - f(m - τ) - 2 τ f₁(m)‖ ≤ τ³ B / 3`. -/
theorem norm_centredDifference_le {f f₁ f₂ f₃ : ℝ → Y} {m τ B : ℝ} (hτ : 0 ≤ τ)
    (h1 : ∀ t ∈ Icc (m - τ) (m + τ), HasDerivAt f (f₁ t) t)
    (h2 : ∀ t ∈ Icc (m - τ) (m + τ), HasDerivAt f₁ (f₂ t) t)
    (h3 : ∀ t ∈ Icc (m - τ) (m + τ), HasDerivAt f₂ (f₃ t) t)
    (hB : ∀ t ∈ Icc (m - τ) (m + τ), ‖f₃ t‖ ≤ B) :
    ‖f (m + τ) - f (m - τ) - (2 * τ) • f₁ m‖ ≤ τ ^ 3 * B / 3 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB m ⟨by linarith, by linarith⟩)
  have hmem : ∀ s ∈ Icc 0 τ, m + s ∈ Icc (m - τ) (m + τ) ∧ m - s ∈ Icc (m - τ) (m + τ) :=
    fun s hs => ⟨⟨by linarith [hs.1, hs.2], by linarith [hs.2]⟩,
      ⟨by linarith [hs.2], by linarith [hs.1]⟩⟩
  have hp : ∀ {g g' : ℝ → Y}, (∀ t ∈ Icc (m - τ) (m + τ), HasDerivAt g (g' t) t) →
      ∀ s ∈ Icc 0 τ, HasDerivAt (fun s => g (m + s) + g (m - s))
        (g' (m + s) - g' (m - s)) s := fun {g g'} hg s hs => by
    have e1 := (hg (m + s) (hmem s hs).1).scomp s ((hasDerivAt_id' s).const_add m)
    have e2 := (hg (m - s) (hmem s hs).2).scomp s ((hasDerivAt_id' s).const_sub m)
    convert e1.add e2 using 1 <;> first | rfl | simp [sub_eq_add_neg]
  have hm : ∀ {g g' : ℝ → Y}, (∀ t ∈ Icc (m - τ) (m + τ), HasDerivAt g (g' t) t) →
      ∀ s ∈ Icc 0 τ, HasDerivAt (fun s => g (m + s) - g (m - s))
        (g' (m + s) + g' (m - s)) s := fun {g g'} hg s hs => by
    have e1 := (hg (m + s) (hmem s hs).1).scomp s ((hasDerivAt_id' s).const_add m)
    have e2 := (hg (m - s) (hmem s hs).2).scomp s ((hasDerivAt_id' s).const_sub m)
    convert e1.sub e2 using 1 <;> first | rfl | simp [sub_eq_add_neg]
  -- `‖f₂(m + s) - f₂(m - s)‖ ≤ 2 s B`
  have hd2 : ∀ s ∈ Ico 0 τ, ‖f₂ (m + s) - f₂ (m - s)‖ ≤ (2 * B) * (s - 0) ^ 1 := by
    intro s hs
    have := norm_image_le_of_norm_deriv_le_pow (g := fun s => f₂ (m + s) - f₂ (m - s))
      (g' := fun s => f₃ (m + s) + f₃ (m - s)) (c := 2 * B) 0
      (fun s hs => (hm h3 s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hm h3 s (Ico_subset_Icc_self hs)).hasDerivWithinAt) (by simp)
      (fun s hs => by
        have hs' := Ico_subset_Icc_self hs
        rw [pow_zero, mul_one, two_mul]
        exact (norm_add_le _ _).trans (add_le_add (hB _ (hmem s hs').1) (hB _ (hmem s hs').2)))
      s (Ico_subset_Icc_self hs)
    simpa using this
  -- `‖f₁(m + s) + f₁(m - s) - 2 f₁(m)‖ ≤ s² B`
  have hd1 : ∀ s ∈ Ico 0 τ, ‖f₁ (m + s) + f₁ (m - s) - (2 : ℝ) • f₁ m‖ ≤ B * (s - 0) ^ 2 := by
    intro s hs
    have := norm_image_le_of_norm_deriv_le_pow
      (g := fun s => f₁ (m + s) + f₁ (m - s) - (2 : ℝ) • f₁ m)
      (g' := fun s => f₂ (m + s) - f₂ (m - s)) (c := 2 * B) 1
      (fun s hs => ((hp h2 s hs).sub_const _).continuousAt.continuousWithinAt)
      (fun s hs => ((hp h2 s (Ico_subset_Icc_self hs)).sub_const _).hasDerivWithinAt)
      (by simp only [add_zero, sub_zero]; module) hd2 s (Ico_subset_Icc_self hs)
    refine this.trans (le_of_eq ?_)
    ring
  have hg := norm_image_le_of_norm_deriv_le_pow
    (g := fun s => f (m + s) - f (m - s) - (2 * s) • f₁ m)
    (g' := fun s => f₁ (m + s) + f₁ (m - s) - (2 : ℝ) • f₁ m) (c := B) 2
    (fun s hs => ((hm h1 s hs).sub
      (((hasDerivAt_id s).const_mul 2).smul_const (f₁ m))).continuousAt.continuousWithinAt)
    (fun s hs => ((hm h1 s (Ico_subset_Icc_self hs)).sub
      (((hasDerivAt_id s).const_mul 2).smul_const (f₁ m))).hasDerivWithinAt.congr_deriv
        (by simp))
    (by simp) hd1 τ ⟨hτ, le_rfl⟩
  refine hg.trans (le_of_eq ?_)
  push_cast
  ring

end CentredDifference

/-! ### Leapfrog with prescribed boundary degrees of freedom -/

section DirichletLeapfrog

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {V₀ : Submodule ℝ V} {A : V →ₗ[ℝ] V}

/-- One **leapfrog step with prescribed boundary degrees of freedom**: on a finite element space
`V` with the subspace `V₀` of the fields with vanishing boundary DOFs, the step `(u, u') ↦ u''`
with boundary values `g''` (any field with the prescribed boundary DOFs, e.g. an interpolant of
the exact solution) is `u'' − g'' ∈ V₀` and `⟪u'' − u, v⟫ = 2 τ ⟪A u', v⟫` for all `v ∈ V₀`,
`⟪A u, v⟫` the bilinear form of the scheme. It is explicit: one solve with the mass matrix of
`V₀`, for every time step (`existsUnique_isDirichletLeapfrogStep`). [Joly2003] -/
def IsDirichletLeapfrogStep (V₀ : Submodule ℝ V) (A : V →ₗ[ℝ] V) (τ : ℝ) (g'' u u' u'' : V) :
    Prop :=
  u'' - g'' ∈ V₀ ∧ ∀ v ∈ V₀, ⟪u'' - u, v⟫ = 2 * τ * ⟪A u', v⟫

/-- **Well-posedness of the leapfrog step**, for every time step: `u'' = g'' + P₀ (u + 2 τ A u' − g'')`
with `P₀` the orthogonal projection onto `V₀`. -/
theorem existsUnique_isDirichletLeapfrogStep (τ : ℝ) (g'' u u' : V) :
    ∃! u'', IsDirichletLeapfrogStep V₀ A τ g'' u u' u'' := by
  refine ⟨g'' + V₀.starProjection (u + (2 * τ) • A u' - g''),
    ⟨by rw [add_sub_cancel_left]; exact Submodule.starProjection_apply_mem _ _, fun v hv => ?_⟩,
    fun w hw => ?_⟩
  · have e := Submodule.inner_starProjection_left_eq_right (K := V₀) (u + (2 * τ) • A u' - g'') v
    rw [Submodule.starProjection_eq_self_iff.2 hv] at e
    rw [show g'' + V₀.starProjection (u + (2 * τ) • A u' - g'') - u =
      V₀.starProjection (u + (2 * τ) • A u' - g'') - (u - g'') by abel, inner_sub_left, e]
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
    ring
  · set w₀ := g'' + V₀.starProjection (u + (2 * τ) • A u' - g'')
    have hd : w - w₀ ∈ V₀ := by
      have := V₀.sub_mem hw.1 (show w₀ - g'' ∈ V₀ by
        rw [add_sub_cancel_left]; exact Submodule.starProjection_apply_mem _ _)
      rwa [sub_sub_sub_cancel_right] at this
    have h0 : ∀ v ∈ V₀, ⟪w - w₀, v⟫ = 0 := fun v hv => by
      have e := Submodule.inner_starProjection_left_eq_right (K := V₀) (u + (2 * τ) • A u' - g'') v
      rw [Submodule.starProjection_eq_self_iff.2 hv] at e
      have e2 := hw.2 v hv
      rw [show w - w₀ = (w - u) - (V₀.starProjection (u + (2 * τ) • A u' - g'') - (u - g'')) by
        simp only [w₀]; abel, inner_sub_left, e2, inner_sub_left, e]
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
    exact sub_eq_zero.1 (inner_self_eq_zero.1 (h0 _ hd))

/-- The **interior operator** `P₀ A P₀` of the scheme, as a continuous operator on `V`: it is skew
when `A` is, and `‖P₀ A P₀‖ ≤ ‖A‖`. -/
def interiorOp (V₀ : Submodule ℝ V) (A : V →ₗ[ℝ] V) : V →L[ℝ] V :=
  V₀.starProjection ∘L LinearMap.toContinuousLinearMap A ∘L V₀.starProjection

theorem norm_interiorOp_le : ‖interiorOp V₀ A‖ ≤ ‖LinearMap.toContinuousLinearMap A‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _) V₀.starProjection_norm_le).trans ?_
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_of_le_one_right (norm_nonneg _) V₀.starProjection_norm_le

theorem inner_interiorOp (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (x y : V) :
    ⟪interiorOp V₀ A x, y⟫ = -⟪x, interiorOp V₀ A y⟫ := by
  simp only [interiorOp, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
  rw [Submodule.inner_starProjection_left_eq_right, hA,
    Submodule.inner_starProjection_left_eq_right]

/-- **Error of the leapfrog scheme with prescribed boundary DOFs** under the CFL condition
`τ ‖A‖ ≤ c < 1` for skew `A`: let `uₖ` be the iterates up to step `n + 1`, with boundary data
`gₖ₊₂`, and let comparison fields `ũₖ` (e.g. interpolants of the exact solution) have the same
boundary DOFs and solve the scheme up to the residuals `ρₖ`,
`⟪ũₖ₊₂ − ũₖ, v⟫ = 2 τ ⟪A ũₖ₊₁, v⟫ + ⟪ρₖ, v⟫` on `V₀`. Then
`√(1 − c) ‖uₙ₊₁ − ũₙ₊₁‖ ≤ √((1 + c)(‖u₀ − ũ₀‖² + ‖u₁ − ũ₁‖²)) + Σ_{k<n} ‖ρₖ‖ / √(1 − c)`:
the errors `eₖ ∈ V₀` follow the leapfrog recursion of the skew operator `P₀ A P₀` with the
residuals `−P₀ ρₖ` (`norm_succ_le_of_leapfrog`). [Joly2003] -/
theorem norm_succ_sub_le_of_isDirichletLeapfrogStep (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫)
    {τ c : ℝ} (hτ : 0 ≤ τ) (hc : τ * ‖LinearMap.toContinuousLinearMap A‖ ≤ c) (hc1 : c < 1)
    {g u ũ ρ : ℕ → V} {n : ℕ}
    (h : ∀ k < n, IsDirichletLeapfrogStep V₀ A τ (g (k + 2)) (u k) (u (k + 1)) (u (k + 2)))
    (hũ : ∀ k < n, ũ (k + 2) - g (k + 2) ∈ V₀) (h0 : u 0 - ũ 0 ∈ V₀) (h1 : u 1 - ũ 1 ∈ V₀)
    (hρ : ∀ k < n, ∀ v ∈ V₀, ⟪ũ (k + 2) - ũ k, v⟫ = 2 * τ * ⟪A (ũ (k + 1)), v⟫ + ⟪ρ k, v⟫) :
    √(1 - c) * ‖u (n + 1) - ũ (n + 1)‖ ≤
      √((1 + c) * (‖u 0 - ũ 0‖ ^ 2 + ‖u 1 - ũ 1‖ ^ 2)) +
        (∑ k ∈ range n, ‖ρ k‖) / √(1 - c) := by
  set P := V₀.starProjection
  set L := interiorOp V₀ A
  set e : ℕ → V := fun k => u k - ũ k
  set r : ℕ → V := fun k => -P (ρ k)
  -- the errors stay in `V₀`
  have hmem : ∀ k ≤ n + 1, e k ∈ V₀ := by
    intro k hk
    rcases k with _ | _ | k
    · exact h0
    · exact h1
    · have := V₀.sub_mem (h k (by omega)).1 (hũ k (by omega))
      rwa [sub_sub_sub_cancel_right] at this
  have hPe : ∀ k ≤ n + 1, P (e k) = e k := fun k hk =>
    Submodule.starProjection_eq_self_iff.2 (hmem k hk)
  have hrec : ∀ k < n, e (k + 2) = e k + ((2 * τ : ℝ) : ℝ) • L (e (k + 1)) + r k := by
    intro k hk
    have hx : e (k + 2) - e k ∈ V₀ := V₀.sub_mem (hmem _ (by omega)) (hmem _ (by omega))
    have hy : ((2 * τ : ℝ) : ℝ) • L (e (k + 1)) + r k ∈ V₀ :=
      V₀.add_mem (V₀.smul_mem _ (Submodule.starProjection_apply_mem _ _))
        (V₀.neg_mem (Submodule.starProjection_apply_mem _ _))
    have hin : ∀ v ∈ V₀, ⟪e (k + 2) - e k - (((2 * τ : ℝ) : ℝ) • L (e (k + 1)) + r k), v⟫ = 0 := by
      intro v hv
      have hPv : P v = v := Submodule.starProjection_eq_self_iff.2 hv
      have e1 := (h k hk).2 v hv
      have e2 := hρ k hk v hv
      have hL : ⟪L (e (k + 1)), v⟫ = ⟪A (e (k + 1)), v⟫ := by
        simp only [L, interiorOp, ContinuousLinearMap.comp_apply,
          LinearMap.coe_toContinuousLinearMap']
        rw [hPe _ (by omega), Submodule.inner_starProjection_left_eq_right, hPv]
      have hr : ⟪r k, v⟫ = -⟪ρ k, v⟫ := by
        simp only [r, inner_neg_left]
        rw [Submodule.inner_starProjection_left_eq_right, hPv]
      have hd : e (k + 2) - e k = (u (k + 2) - u k) - (ũ (k + 2) - ũ k) := by
        simp only [e]; abel
      rw [inner_sub_left, inner_add_left, real_inner_smul_left, hL, hr, hd, inner_sub_left, e1,
        e2, show e (k + 1) = u (k + 1) - ũ (k + 1) from rfl, map_sub, inner_sub_left]
      ring
    have h' := sub_eq_zero.1 (inner_self_eq_zero.1 (hin _ (V₀.sub_mem hx hy)))
    rw [add_assoc, ← h']; abel
  have hLs : ∀ x y, ⟪L x, y⟫ = -⟪x, L y⟫ := inner_interiorOp hA
  have hLc : τ * ‖L‖ ≤ c := (mul_le_mul_of_nonneg_left norm_interiorOp_le hτ).trans hc
  have key := norm_succ_le_of_leapfrog (𝕜 := ℝ) hLs hτ hLc hc1 (e := e) (r := r) hrec
  have hsum : ∑ k ∈ range n, ‖r k‖ ≤ ∑ k ∈ range n, ‖ρ k‖ := sum_le_sum fun k _ => by
    simp only [r, norm_neg]
    exact (P.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) V₀.starProjection_norm_le)
  have hs : 0 < √(1 - c) := Real.sqrt_pos.2 (by linarith)
  have : (∑ k ∈ range n, ‖r k‖) / √(1 - c) ≤ (∑ k ∈ range n, ‖ρ k‖) / √(1 - c) :=
    div_le_div_of_nonneg_right hsum hs.le
  linarith

end DirichletLeapfrog

end Feec.TimeStepping
