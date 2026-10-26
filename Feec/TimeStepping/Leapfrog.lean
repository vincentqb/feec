module

public import Feec.TimeStepping.Convergence

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
* `norm_le_of_leapfrog` (stability plus consistency):
  `√(1 - c) ‖eₙ‖ ≤ √((1 + c) (‖e₀‖² + ‖e₁‖²)) + Σ_{k<n} ‖rₖ‖ / √(1 - c)`;
* **`norm_leapfrog_sub_exp_le`** (second order): for leapfrog iterates `uₙ` and the exact flow
  `e^{tL} x`, at `t = n τ`,
  `√(1 - c) ‖uₙ - e^{tL} x‖ ≤ √((1 + c) (‖u₀ - x‖² + ‖u₁ - e^{τL} x‖²))`
  `+ t τ² ‖L³ x‖ / (3 √(1 - c))`
  (the residual of the exact orbit is `(e^{τL} - e^{-τL} - 2 τ L) e^{(k+1)τL} x = O(τ³ ‖L³ x‖)`,
  `norm_exp_sub_exp_neg_le`).

## References

* [P. Joly, *Variational Methods for Time-Dependent Wave Propagation Problems*][Joly2003]
  (leapfrog for second-order hyperbolic problems: discrete energy, CFL stability)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open NormedSpace Finset

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

/-- `re ⟪x - y, x + y⟫ = ‖x‖² - ‖y‖²`. -/
private theorem re_inner_sub_add (x y : X) :
    RCLike.re ⟪x - y, x + y⟫ = ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
  rw [inner_sub_left, inner_add_right, inner_add_right, _root_.map_sub, _root_.map_add,
    _root_.map_add, inner_self_eq_norm_sq, inner_self_eq_norm_sq, inner_re_symm y x]
  ring

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

/-- **Stability plus consistency for leapfrog** under the CFL condition `τ ‖L‖ ≤ c < 1`: for
skew `L` and `eₙ₊₂ = eₙ + 2 τ L eₙ₊₁ + rₙ`,
`√(1 - c) ‖eₙ‖ ≤ √((1 + c)(‖e₀‖² + ‖e₁‖²)) + Σ_{k<n} ‖rₖ‖ / √(1 - c)`. [Joly2003] -/
theorem norm_le_of_leapfrog (hL : ∀ x y, ⟪L x, y⟫ = -⟪x, L y⟫) (hτ : 0 ≤ τ)
    (hc : τ * ‖L‖ ≤ c) (hc1 : c < 1) {e r : ℕ → X}
    (he : ∀ n, e (n + 2) = e n + ((2 * τ : ℝ) : 𝕜) • L (e (n + 1)) + r n) (n : ℕ) :
    √(1 - c) * ‖e n‖ ≤
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
  have key : ∀ m, √(En m) ≤ √(En 0) + (∑ k ∈ range m, ‖r k‖) / s := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hstep := leapfrogEnergy_succ hL (he m)
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
      linarith
  have h0 : √(En 0) ≤ √((1 + c) * (‖e 0‖ ^ 2 + ‖e 1‖ ^ 2)) :=
    Real.sqrt_le_sqrt (leapfrogEnergy_le hτ hc _ _)
  linarith [hfst n, key n]

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
        C0Group.exp_ofReal_smul_add]
      rfl
    have e0 : w k = exp (((-τ : ℝ) : 𝕜) • L) (w (k + 1)) := by
      simp only [w]
      rw [show ((k : ℝ) * τ) = -τ + ((k + 1 : ℕ) : ℝ) * τ by push_cast; ring,
        C0Group.exp_ofReal_smul_add]
      rfl
    have e3 : (L ^ 3) (w (k + 1)) = exp ((((k + 1 : ℕ) * τ : ℝ) : 𝕜) • L) ((L ^ 3) x) :=
      congrArg (fun C : X →L[𝕜] X => C x)
        ((C0Group.commute_exp_ofReal_smul L (((k + 1 : ℕ) : ℝ) * τ)).pow_left 3).eq
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

end Feec.TimeStepping
