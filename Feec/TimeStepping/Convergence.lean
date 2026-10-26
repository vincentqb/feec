module

public import Feec.TimeStepping.Theta
public import Feec.ForMathlib.LinearPMap.Bounded

/-!
# Convergence of one-step schemes: stability and consistency

A one-step scheme `uₙ₊₁ = P uₙ + gₙ` for `u' = L u + f` converges when it is **stable**
(`‖Pᵏ‖ ≤ M`) and **consistent** with the exact flow: the classical "stability plus consistency
implies convergence" ([Thomee2006], Ch. 7; [BrennerThomee1979]). This file proves it in two
layers.

* **Any normed space, any comparison sequence** (`sub_eq_sum_of_step`, the discrete Duhamel
  formula, and `norm_sub_le_of_step`): for `Uₖ₊₁ = P Uₖ + gₖ` and any `wₖ`,
  `‖Uₙ - wₙ‖ ≤ M (‖U₀ - w₀‖ + Σₖ<ₙ ‖wₖ₊₁ - P wₖ - gₖ‖)`: the error is at most the initial error
  plus the accumulated consistency defects. This is the discrete counterpart of
  `Feec.HilbertComplex.norm_sub_le_of_defect_of_dissipative` ("best approximation plus
  consistency"), and the operator form of `TimeStepping.norm_sub_le_sum_of_isDirichletCNStep`.
* **Bounded dissipative generators** (`re ⟪L x, x⟫ ≤ 0`, so `e^{tL}` is a contraction for `t ≥ 0`):
  the Taylor remainder `‖e^{tL} y - Σ_{j<p} tʲ/j! Lʲ y‖ ≤ tᵖ/p! ‖Lᵖ y‖`
  (`norm_exp_sub_taylor_le`); a scheme `P` is **consistent of order `p` with constant `K`**
  (`IsConsistent`) if `‖P y - e^{τL} y‖ ≤ K τ^{p+1} ‖L^{p+1} y‖`, which follows from an expansion
  `P = Σ_{j≤p} τʲ/j! Lʲ + τ^{p+1} ρ L^{p+1}` with `‖ρ‖ ≤ K₀` (`isConsistent_of_eq`, `K = K₀ + 1/(p+1)!`);
  and **`norm_pow_apply_sub_exp_le`**: stability and consistency of order `p` give the global error
  `‖Pⁿ y - e^{nτL} y‖ ≤ M K (n τ) τᵖ ‖L^{p+1} y‖`. All constants are independent of `L`: on finite
  element spaces they are uniform in the mesh.

## θ-schemes for bounded generators

`ContinuousLinearMap.isMDissipative_toPMap_top`: a bounded dissipative operator on a Hilbert space
is m-dissipative, so `Feec.TimeStepping.thetaStep` applies to it. For real `θ > 0` and `τ > 0`,
`r_θ(τ L) = 1 + τ L + θ τ² W L²` with `W = (1 - θ τ L)⁻¹`, `‖W‖ ≤ 1` (`exists_thetaStep_apply_eq`); for
`θ = 1/2`, `r_{1/2}(τ L) = 1 + τ L + τ²/2 L² + τ³/4 W L³` (`exists_thetaStep_half_apply_eq`). Hence
(`isConsistent_thetaStep`, `isConsistent_thetaStep_half`) the θ-scheme is consistent of order `1`
with `K = θ + 1/2`, and Crank–Nicolson of order `2` with `K = 5/12`, and:

* **`norm_implicitEuler_pow_sub_exp_le`**: implicit Euler, `‖(1 - τ L)⁻ⁿ y - e^{tL} y‖ ≤ 3/2 t τ ‖L² y‖`;
* **`norm_cayley_pow_sub_exp_le`**: Crank–Nicolson (`cayley`),
  `‖cayley(L, τ/2)ⁿ y - e^{tL} y‖ ≤ 5/12 t τ² ‖L³ y‖`;
* `norm_thetaStep_pow_sub_exp_le`: the θ-scheme, `re θ ≥ 1/2`, `‖·‖ ≤ (θ + 1/2) t τ ‖L² y‖`;

at `t = n τ`, for every bounded dissipative `L`, the rate of [BrennerThomee1979] (smooth data).
`thetaStep_mem_of_mapsTo`: a closed subspace `K` with `L K ⊆ K` is kept by the θ-scheme (discrete
constraint propagation, for instance for a discrete Gauss law).

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
  (order `p` rational schemes: `O(t τᵖ ‖A^{p+1} x‖)`)
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7
  (single step methods: stability and consistency), Ch. 8–9
* [R. Hersh, T. Kato, *High-Accuracy Stable Difference Schemes for Well-Posed Initial-Value Problems*][HershKato1979]
  (stability and accuracy of rational approximations of semigroups)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 4.18 (constraint propagation, here at the discrete level)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Feec.Operator NormedSpace Finset

@[expose] public noncomputable section

namespace Feec.TimeStepping

/-! ### Stability plus consistency: the discrete Duhamel formula -/

section Duhamel

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {P : X →L[𝕜] X} {U g w : ℕ → X}

/-- **The discrete Duhamel formula**: for `Uₖ₊₁ = P Uₖ + gₖ` and any comparison sequence `wₖ`,
`Uₙ - wₙ = Pⁿ (U₀ - w₀) + Σ_{j<n} Pʲ dₙ₋₁₋ⱼ` with the defects `dₖ = P wₖ + gₖ - wₖ₊₁`. -/
theorem sub_eq_sum_of_step (hU : ∀ k, U (k + 1) = P (U k) + g k) (n : ℕ) :
    U n - w n = (P ^ n) (U 0 - w 0) +
      ∑ j ∈ range n, (P ^ j) (P (w (n - 1 - j)) + g (n - 1 - j) - w (n - j)) := by
  have hm : ∀ (Q : X →L[𝕜] X) (x : X), (P * Q) x = P (Q x) := fun _ _ => rfl
  induction n with
  | zero => simp
  | succ n ih =>
    have hidx : ∀ j ∈ range n,
        (P ^ (j + 1)) (P (w (n + 1 - 1 - (j + 1))) + g (n + 1 - 1 - (j + 1)) - w (n + 1 - (j + 1)))
          = P ((P ^ j) (P (w (n - 1 - j)) + g (n - 1 - j) - w (n - j))) := by
      intro j _
      rw [show n + 1 - 1 - (j + 1) = n - 1 - j by omega, show n + 1 - (j + 1) = n - j by omega,
        pow_succ', hm]
    rw [sum_range_succ', sum_congr rfl hidx, ← map_sum, hU n, pow_succ', hm]
    simp only [pow_zero, Nat.sub_zero, add_tsub_cancel_right, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_apply]
    rw [← add_assoc, ← _root_.map_add, ← ih, _root_.map_sub]
    abel

/-- **Stability plus consistency gives convergence**: if `‖Pᵏ‖ ≤ M` for `k ≤ n` and
`Uₖ₊₁ = P Uₖ + gₖ`, then for every comparison sequence `wₖ`,
`‖Uₙ - wₙ‖ ≤ M (‖U₀ - w₀‖ + Σ_{k<n} ‖wₖ₊₁ - P wₖ - gₖ‖)`. [Thomee2006], Ch. 7 -/
theorem norm_sub_le_of_step {M : ℝ} {n : ℕ} (hP : ∀ k ≤ n, ‖P ^ k‖ ≤ M)
    (hU : ∀ k, U (k + 1) = P (U k) + g k) :
    ‖U n - w n‖ ≤ M * (‖U 0 - w 0‖ + ∑ k ∈ range n, ‖w (k + 1) - P (w k) - g k‖) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hP 0 (Nat.zero_le _))
  rw [sub_eq_sum_of_step hU n, mul_add, mul_sum]
  refine (norm_add_le _ _).trans (add_le_add (((P ^ n).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hP n le_rfl) (norm_nonneg _))) ?_)
  refine (norm_sum_le _ _).trans ?_
  rw [← sum_range_reflect (fun k => M * ‖w (k + 1) - P (w k) - g k‖) n]
  refine sum_le_sum fun j hj => ?_
  have hj' : j < n := mem_range.1 hj
  rw [show n - 1 - j + 1 = n - j by omega]
  have e : ‖w (n - j) - P (w (n - 1 - j)) - g (n - 1 - j)‖ =
      ‖P (w (n - 1 - j)) + g (n - 1 - j) - w (n - j)‖ := by
    rw [← norm_neg]; congr 1; abel
  rw [e]
  exact ((P ^ j).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hP j hj'.le) (norm_nonneg _))

/-- Powers of a contraction are contractions. -/
theorem norm_pow_le_one {P : X →L[𝕜] X} (hP : ‖P‖ ≤ 1) (n : ℕ) : ‖P ^ n‖ ≤ 1 := by
  induction n with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    rw [pow_succ]
    exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (P ^ n), norm_nonneg P])

end Duhamel

/-! ### Bounded dissipative generators: Taylor remainders and consistency -/

section Bounded

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [CompleteSpace X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] {L : X →L[𝕜] X}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **The Taylor remainder of a contraction semigroup**: for bounded dissipative `L`, `t ≥ 0`,
`‖e^{tL} y - Σ_{j<p} tʲ/j! Lʲ y‖ ≤ tᵖ/p! ‖Lᵖ y‖` (the derivative of the order-`p + 1` remainder
in `t` is the order-`p` remainder of `L y`). -/
theorem norm_exp_sub_taylor_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) (p : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (y : X) :
    ‖exp ((t : 𝕜) • L) y - ∑ j ∈ range p, (t ^ j / j.factorial) • (L ^ j) y‖ ≤
      t ^ p / p.factorial * ‖(L ^ p) y‖ := by
  induction p generalizing y t with
  | zero => simpa using LumerPhillips.norm_exp_smul_apply_le hL ht y
  | succ p ih =>
    set F : ℝ → X := fun s => exp ((s : 𝕜) • L) y -
      ∑ j ∈ range (p + 1), (s ^ j / j.factorial) • (L ^ j) y
    set G : ℝ → X := fun s => exp ((s : 𝕜) • L) (L y) -
      ∑ j ∈ range p, (s ^ j / j.factorial) • (L ^ j) (L y)
    have hF : ∀ s, F s = exp ((s : 𝕜) • L) y - y -
        ∑ j ∈ range p, (s ^ (j + 1) / (j + 1).factorial) • (L ^ j) (L y) := fun s => by
      simp only [F, sum_range_succ', pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
        one_smul, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
      rw [sub_add_eq_sub_sub_swap]
      congr 2
    have hd : ∀ s, HasDerivAt F (G s) s := fun s => by
      have he : HasDerivAt (fun s : ℝ => exp ((s : 𝕜) • L) y) (exp ((s : 𝕜) • L) (L y)) s := by
        have := C0Group.hasDerivAt_exp_ofReal_smul_apply L y s
        rwa [show L (exp ((s : 𝕜) • L) y) = exp ((s : 𝕜) • L) (L y) from
          congrArg (fun C : X →L[𝕜] X => C y) (C0Group.commute_exp_ofReal_smul L s).eq] at this
      have hsum : HasDerivAt
          (fun s : ℝ => ∑ j ∈ range p, (s ^ (j + 1) / (j + 1).factorial) • (L ^ j) (L y))
          (∑ j ∈ range p, (s ^ j / j.factorial) • (L ^ j) (L y)) s := by
        have := HasDerivAt.sum (u := range p) (x := s)
          (A := fun j (s : ℝ) => (s ^ (j + 1) / (j + 1).factorial) • (L ^ j) (L y))
          (A' := fun j => (s ^ j / j.factorial) • (L ^ j) (L y)) fun j _ => by
            have h := ((hasDerivAt_pow (j + 1) s).div_const ((j + 1).factorial : ℝ)).smul_const
              ((L ^ j) (L y))
            convert h using 2
            rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
            have : (j.factorial : ℝ) ≠ 0 := by positivity
            field_simp
        convert this using 1
        ext s'; simp
      have := (he.sub_const y).sub hsum
      rw [show F = fun s : ℝ => exp ((s : 𝕜) • L) y - y -
        ∑ j ∈ range p, (s ^ (j + 1) / (j + 1).factorial) • (L ^ j) (L y) from funext hF]
      exact this
    have hB : ∀ s, HasDerivAt (fun s : ℝ => s ^ (p + 1) / (p + 1).factorial * ‖(L ^ (p + 1)) y‖)
        (s ^ p / p.factorial * ‖(L ^ (p + 1)) y‖) s := fun s => by
      have h := ((hasDerivAt_pow (p + 1) s).div_const ((p + 1).factorial : ℝ)).mul_const
        ‖(L ^ (p + 1)) y‖
      convert h using 1
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
      have : (p.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := t) (f := F)
      (f' := G) (fun s _ => (hd s).continuousAt.continuousWithinAt)
      (fun s _ => (hd s).hasDerivWithinAt) (B := fun s =>
        s ^ (p + 1) / (p + 1).factorial * ‖(L ^ (p + 1)) y‖)
      (by simp [F, sum_range_succ']) hB (fun s hs => by
        have := ih hs.1 (L y)
        rwa [show (L ^ p) (L y) = (L ^ (p + 1)) y by rw [pow_succ]; rfl] at this)
      ⟨ht, le_rfl⟩
    exact key

/-- A scheme `P` is **consistent of order `p` with constant `K`** with the flow `e^{τL}`:
`‖P y - e^{τL} y‖ ≤ K τ^{p+1} ‖L^{p+1} y‖` for every `y`. [Thomee2006], Ch. 7 -/
def IsConsistent (L P : X →L[𝕜] X) (τ : ℝ) (p : ℕ) (K : ℝ) : Prop :=
  ∀ y, ‖P y - exp ((τ : 𝕜) • L) y‖ ≤ K * τ ^ (p + 1) * ‖(L ^ (p + 1)) y‖

/-- **Consistency from an expansion**: `P = Σ_{j≤p} τʲ/j! Lʲ + τ^{p+1} ρ L^{p+1}` with `‖ρ‖ ≤ K₀`
is consistent of order `p` with constant `K₀ + 1/(p+1)!`. [Thomee2006], Ch. 7 -/
theorem isConsistent_of_eq (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {P ρ : X →L[𝕜] X} {τ : ℝ}
    (hτ : 0 ≤ τ) {p : ℕ} {K₀ : ℝ} (hρ : ‖ρ‖ ≤ K₀)
    (hP : ∀ y, P y = ∑ j ∈ range (p + 1), (τ ^ j / j.factorial) • (L ^ j) y +
      τ ^ (p + 1) • ρ ((L ^ (p + 1)) y)) :
    IsConsistent L P τ p (K₀ + 1 / (p + 1).factorial) := by
  intro y
  have h1 := norm_exp_sub_taylor_le hL (p + 1) hτ y
  have h2 : ‖τ ^ (p + 1) • ρ ((L ^ (p + 1)) y)‖ ≤ τ ^ (p + 1) * (K₀ * ‖(L ^ (p + 1)) y‖) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    gcongr
    exact (ρ.le_opNorm _).trans (mul_le_mul_of_nonneg_right hρ (norm_nonneg _))
  have e : P y - exp ((τ : 𝕜) • L) y = τ ^ (p + 1) • ρ ((L ^ (p + 1)) y) -
      (exp ((τ : 𝕜) • L) y - ∑ j ∈ range (p + 1), (τ ^ j / j.factorial) • (L ^ j) y) := by
    rw [hP]; abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_sub_rev] at h1
  calc _ ≤ τ ^ (p + 1) * (K₀ * ‖(L ^ (p + 1)) y‖) +
        τ ^ (p + 1) / (p + 1).factorial * ‖(L ^ (p + 1)) y‖ := add_le_add h2 (by
          rwa [norm_sub_rev] at h1)
    _ = _ := by ring

/-- **Stability and consistency of order `p` give the rate `M K t τᵖ`**: if `‖Pᵏ‖ ≤ M` for
`k ≤ n` and `P` is consistent of order `p` with constant `K`, then
`‖Pⁿ y - e^{nτL} y‖ ≤ M K (n τ) τᵖ ‖L^{p+1} y‖`. [BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem norm_pow_apply_sub_exp_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {P : X →L[𝕜] X} {M : ℝ}
    {n : ℕ} (hP : ∀ k ≤ n, ‖P ^ k‖ ≤ M) {τ : ℝ} (hτ : 0 ≤ τ) {p : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hc : IsConsistent L P τ p K) (y : X) :
    ‖(P ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤ M * K * (n * τ) * τ ^ p * ‖(L ^ (p + 1)) y‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hP 0 (Nat.zero_le _))
  set w : ℕ → X := fun k => exp (((k * τ : ℝ) : 𝕜) • L) y
  have h := norm_sub_le_of_step (U := fun k => (P ^ k) y) (g := fun _ => 0) (w := w) hP
    (fun k => by simp [pow_succ'])
  have hw0 : (P ^ 0) y - w 0 = 0 := by simp [w]
  have hdef : ∀ k, ‖w (k + 1) - P (w k) - 0‖ ≤ K * τ ^ (p + 1) * ‖(L ^ (p + 1)) y‖ := by
    intro k
    have hk : 0 ≤ (k : ℝ) * τ := by positivity
    have e1 : w (k + 1) = exp ((τ : 𝕜) • L) (w k) := by
      simp only [w]
      rw [show (((k + 1 : ℕ) * τ : ℝ)) = τ + k * τ by push_cast; ring,
        C0Group.exp_ofReal_smul_add]
      rfl
    have e2 : (L ^ (p + 1)) (w k) = exp (((k * τ : ℝ) : 𝕜) • L) ((L ^ (p + 1)) y) :=
      congrArg (fun C : X →L[𝕜] X => C y)
        ((C0Group.commute_exp_ofReal_smul L (k * τ)).pow_left (p + 1)).eq
    rw [sub_zero, e1, norm_sub_rev]
    refine (hc (w k)).trans ?_
    rw [e2]
    have hK' : 0 ≤ K * τ ^ (p + 1) := by positivity
    exact mul_le_mul_of_nonneg_left (LumerPhillips.norm_exp_smul_apply_le hL hk _) hK'
  refine h.trans ?_
  rw [hw0, norm_zero, zero_add]
  calc M * ∑ k ∈ range n, ‖w (k + 1) - P (w k) - 0‖
      ≤ M * ∑ _k ∈ range n, K * τ ^ (p + 1) * ‖(L ^ (p + 1)) y‖ :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => hdef k) hM
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-! ### θ-schemes of bounded dissipative operators -/

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
/-- **A bounded dissipative operator on a Hilbert space is m-dissipative** (closed, everywhere
defined, with dissipative adjoint), so the θ-schemes of `Feec.TimeStepping.Theta` apply to it. -/
theorem _root_.ContinuousLinearMap.isMDissipative_toPMap_top (L : X →L[𝕜] X)
    (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) : ((L : X →ₗ[𝕜] X).toPMap ⊤).IsMDissipative := by
  refine IsDissipative.isMDissipative_of_adjoint (fun x => hL x) ?_ L.isClosed_toPMap_top ?_
  · simp [dense_univ]
  · rw [L.adjoint_toPMap_top]
    intro x
    change RCLike.re ⟪ContinuousLinearMap.adjoint L x, (x : X)⟫ ≤ 0
    rw [ContinuousLinearMap.adjoint_inner_left, inner_re_symm]
    exact hL x

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
/-- The resolvent `R = (λ - L)⁻¹`, `λ = (θ τ)⁻¹`, of a bounded dissipative `L` (real `θ, τ > 0`):
`λ R y - L R y = y`, `R L = L R`, `‖λ R‖ ≤ 1`, and the θ-scheme is `(θ² τ)⁻¹ R - (1 - θ)/θ`. -/
private theorem thetaStep_resolvent (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {θ τ : ℝ} (hθ : 0 < θ)
    (hτ : 0 < τ) :
    let R := resolvent ((L : X →ₗ[𝕜] X).toPMap ⊤) ((θ : 𝕜) * (τ : 𝕜))⁻¹
    (∀ y, ((θ : 𝕜) * (τ : 𝕜))⁻¹ • R y - L (R y) = y) ∧ (∀ y, R (L y) = L (R y)) ∧
      ‖((θ : 𝕜) * (τ : 𝕜))⁻¹ • R‖ ≤ 1 := by
  intro R
  have hA := L.isMDissipative_toPMap_top hL
  have hμ : 0 < (θ * τ)⁻¹ := by positivity
  have e : ((θ : 𝕜) * (τ : 𝕜))⁻¹ = (((θ * τ)⁻¹ : ℝ) : 𝕜) := by push_cast; rfl
  have hR : IsResolvent ((L : X →ₗ[𝕜] X).toPMap ⊤) ((θ : 𝕜) * (τ : 𝕜))⁻¹ R := by
    rw [e]; exact e ▸ hA.isResolvent hμ
  have h1 : ∀ y, ((θ : 𝕜) * (τ : 𝕜))⁻¹ • R y - L (R y) = y := hR.sub_apply
  refine ⟨h1, fun y => ?_, ?_⟩
  · have h2 : R (((θ : 𝕜) * (τ : 𝕜))⁻¹ • y - L y) = y := hR.apply_sub ⟨y, trivial⟩
    rw [_root_.map_sub, _root_.map_smul] at h2
    exact sub_right_injective (h2.trans (h1 y).symm)
  · rw [norm_smul]
    have hn : ‖R‖ ≤ ((θ * τ)⁻¹)⁻¹ := by
      have := hA.norm_resolvent_le hμ
      rwa [← e] at this
    rw [e, RCLike.norm_ofReal, abs_of_pos hμ]
    calc (θ * τ)⁻¹ * ‖R‖ ≤ (θ * τ)⁻¹ * ((θ * τ)⁻¹)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hμ.ne'

/-- **The θ-scheme of a bounded dissipative operator, expanded to first order**: for real
`θ > 0`, `τ > 0`, `r_θ(τ L) y = y + τ L y + τ² (θ W) (L² y)` with `W = (1 - θ τ L)⁻¹`,
`‖θ W‖ ≤ θ`. -/
theorem exists_thetaStep_apply_eq (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {θ τ : ℝ} (hθ : 0 < θ)
    (hτ : 0 < τ) : ∃ ρ : X →L[𝕜] X, ‖ρ‖ ≤ θ ∧ ∀ y,
      thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ y =
        ∑ j ∈ range 2, (τ ^ j / j.factorial) • (L ^ j) y + τ ^ 2 • ρ ((L ^ 2) y) := by
  obtain ⟨h1, h2, h3⟩ := thetaStep_resolvent (𝕜 := 𝕜) hL hθ hτ
  set R := resolvent ((L : X →ₗ[𝕜] X).toPMap ⊤) ((θ : 𝕜) * (τ : 𝕜))⁻¹
  refine ⟨((θ : 𝕜) * ((θ : 𝕜) * (τ : 𝕜))⁻¹) • R, ?_, fun y => ?_⟩
  · rw [mul_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos hθ]
    exact mul_le_of_le_one_right hθ.le h3
  have hθ' : (θ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hθ.ne'
  have hτ' : (τ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hτ.ne'
  have hL1 : L (R y) = ((θ : 𝕜) * (τ : 𝕜))⁻¹ • R y - y := by
    have h := h1 y; generalize R y = r at h ⊢; rw [← h]; abel
  have hL2 : R ((L ^ 2) y) =
      ((θ : 𝕜) * (τ : 𝕜))⁻¹ • (((θ : 𝕜) * (τ : 𝕜))⁻¹ • R y - y) - L y := by
    rw [show (L ^ 2) y = L (L y) by simp [pow_succ], h2, h2, hL1, _root_.map_sub,
      _root_.map_smul, hL1]
  simp only [thetaStep, sum_range_succ, sum_range_zero, _root_.sub_apply, _root_.smul_apply,
    pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, one_smul,
    zero_add, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
  rw [hL2]
  simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  match_scalars <;> field_simp <;> ring

/-- **Crank–Nicolson of a bounded dissipative operator, expanded to second order**: for
`τ > 0`, `r_{1/2}(τ L) y = y + τ L y + τ²/2 L² y + τ³ (W/4) (L³ y)` with `W = (1 - τ L / 2)⁻¹`,
`‖W/4‖ ≤ 1/4`. -/
theorem exists_thetaStep_half_apply_eq (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {τ : ℝ}
    (hτ : 0 < τ) : ∃ ρ : X →L[𝕜] X, ‖ρ‖ ≤ 1 / 4 ∧ ∀ y,
      thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) ((1 / 2 : ℝ) : 𝕜) τ y =
        ∑ j ∈ range 3, (τ ^ j / j.factorial) • (L ^ j) y + τ ^ 3 • ρ ((L ^ 3) y) := by
  obtain ⟨h1, h2, h3⟩ := thetaStep_resolvent (𝕜 := 𝕜) hL (θ := 1 / 2) (by norm_num) hτ
  set R := resolvent ((L : X →ₗ[𝕜] X).toPMap ⊤) (((1 / 2 : ℝ) : 𝕜) * (τ : 𝕜))⁻¹
  refine ⟨((1 / 4 : 𝕜) * (((1 / 2 : ℝ) : 𝕜) * (τ : 𝕜))⁻¹) • R, ?_, fun y => ?_⟩
  · rw [mul_smul, norm_smul]
    have : ‖(1 / 4 : 𝕜)‖ = 1 / 4 := by
      rw [show (1 / 4 : 𝕜) = ((1 / 4 : ℝ) : 𝕜) by push_cast; rfl, RCLike.norm_ofReal]
      norm_num
    rw [this]
    exact mul_le_of_le_one_right (by norm_num) h3
  have hτ' : (τ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hτ.ne'
  set c : 𝕜 := (((1 / 2 : ℝ) : 𝕜) * (τ : 𝕜))⁻¹
  have hL1 : L (R y) = c • R y - y := by
    have h := h1 y; generalize R y = r at h ⊢; rw [← h]; abel
  have hL3 : R ((L ^ 3) y) = c • (c • (c • R y - y) - L y) - L (L y) := by
    rw [show (L ^ 3) y = L (L (L y)) by simp [pow_succ], h2, h2, h2, hL1, _root_.map_sub,
      _root_.map_smul, hL1, _root_.map_sub, _root_.map_smul, _root_.map_sub, _root_.map_smul,
      hL1]
  simp only [thetaStep, sum_range_succ, sum_range_zero, _root_.sub_apply, _root_.smul_apply,
    pow_zero, pow_one, Nat.factorial, Nat.cast_one, Nat.succ_eq_add_one, div_one, one_smul,
    zero_add, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
  rw [hL3, show (L ^ 2) y = L (L y) by simp [pow_succ]]
  simp only [c, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  match_scalars <;> field_simp <;> ring

/-- **The θ-scheme is consistent of order `1`** with constant `θ + 1/2` (real `θ > 0`, `τ > 0`),
uniformly in the bounded dissipative `L`. [Thomee2006], Ch. 7 -/
theorem isConsistent_thetaStep (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {θ τ : ℝ} (hθ : 0 < θ)
    (hτ : 0 < τ) :
    IsConsistent L (thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ) τ 1 (θ + 1 / 2) := by
  obtain ⟨ρ, hρ, hP⟩ := exists_thetaStep_apply_eq (𝕜 := 𝕜) hL hθ hτ
  have := isConsistent_of_eq hL hτ.le hρ hP
  rwa [show θ + 1 / 2 = θ + 1 / ((1 + 1).factorial : ℝ) by norm_num [Nat.factorial]]

/-- **Crank–Nicolson is consistent of order `2`** with constant `5/12` (`τ > 0`), uniformly in
the bounded dissipative `L`. [Thomee2006], Ch. 7 -/
theorem isConsistent_thetaStep_half (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {τ : ℝ} (hτ : 0 < τ) :
    IsConsistent L (thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) ((1 / 2 : ℝ) : 𝕜) τ) τ 2 (5 / 12) := by
  obtain ⟨ρ, hρ, hP⟩ := exists_thetaStep_half_apply_eq (𝕜 := 𝕜) hL hτ
  have := isConsistent_of_eq hL hτ.le hρ hP
  rwa [show (5 / 12 : ℝ) = 1 / 4 + 1 / ((2 + 1).factorial : ℝ) by norm_num [Nat.factorial]]

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
/-- The θ-scheme of a bounded dissipative operator is power bounded by `1` (`re θ ≥ 1/2`,
`τ > 0`). -/
theorem norm_thetaStep_pow_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {θ : 𝕜}
    (hθ : 1 / 2 ≤ RCLike.re θ) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) :
    ‖thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ ^ n‖ ≤ 1 :=
  norm_pow_le_one (norm_thetaStep_le (L.isMDissipative_toPMap_top hL) hθ hτ) n

/-- **The global error of the θ-scheme** (`1/2 ≤ θ`, real): at `t = n τ`,
`‖r_θ(τ L)ⁿ y - e^{tL} y‖ ≤ (θ + 1/2) t τ ‖L² y‖` for every bounded dissipative `L`.
[BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem norm_thetaStep_pow_sub_exp_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {θ τ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hτ : 0 < τ) (n : ℕ) (y : X) :
    ‖(thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤
      (θ + 1 / 2) * (n * τ) * τ * ‖(L ^ 2) y‖ := by
  have := norm_pow_apply_sub_exp_le hL (n := n) (M := 1)
    (fun k _ => norm_thetaStep_pow_le hL (by simpa using hθ) hτ k) hτ.le (by linarith)
    (isConsistent_thetaStep hL (by linarith) hτ) y
  simpa using this

/-- **The global error of implicit Euler**: at `t = n τ`,
`‖(1 - τ L)⁻ⁿ y - e^{tL} y‖ ≤ 3/2 t τ ‖L² y‖` for every bounded dissipative `L`.
[Thomee2006], Ch. 7 -/
theorem norm_implicitEuler_pow_sub_exp_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {τ : ℝ}
    (hτ : 0 < τ) (n : ℕ) (y : X) :
    ‖(thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) 1 τ ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤
      3 / 2 * (n * τ) * τ * ‖(L ^ 2) y‖ := by
  have := norm_thetaStep_pow_sub_exp_le (𝕜 := 𝕜) hL (θ := 1) (by norm_num) hτ n y
  norm_num at this ⊢
  exact this

/-- **The global error of Crank–Nicolson** (`cayley` with half step `τ/2`): at `t = n τ`,
`‖cayley(L, τ/2)ⁿ y - e^{tL} y‖ ≤ 5/12 t τ² ‖L³ y‖` for every bounded dissipative `L`.
[BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem norm_cayley_pow_sub_exp_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {τ : ℝ} (hτ : 0 < τ)
    (n : ℕ) (y : X) :
    ‖(cayley ((L : X →ₗ[𝕜] X).toPMap ⊤) (τ / 2) ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤
      5 / 12 * (n * τ) * τ ^ 2 * ‖(L ^ 3) y‖ := by
  rw [cayley_half_eq_thetaStep]
  have := norm_pow_apply_sub_exp_le hL (n := n) (M := 1)
    (fun k _ => norm_thetaStep_pow_le hL (by rw [RCLike.ofReal_re]) hτ k) hτ.le (by norm_num)
    (isConsistent_thetaStep_half hL hτ) y
  simpa using this

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
/-- **Discrete constraint propagation for closed invariant subspaces**: if `L K ⊆ K` for a closed
`K` (for instance a subspace of a finite element space), then `r_θ(τ L) K ⊆ K` (`re θ > 0`,
`τ > 0`): the part of `L` in `K` is bounded and dissipative, so the resolvent equation is solvable
within `K`. [QuennevilleBelair2015], Prop 4.18 -/
theorem thetaStep_mem_of_mapsTo (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {K : Submodule 𝕜 X}
    (hKc : IsClosed (K : Set X)) (hLK : ∀ x ∈ K, L x ∈ K) {θ : 𝕜} (hθ : 0 < RCLike.re θ)
    {τ : ℝ} (hτ : 0 < τ) {u : X} (hu : u ∈ K) :
    thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ u ∈ K := by
  have : CompleteSpace K := hKc.completeSpace_coe
  set LK : K →L[𝕜] K := (L.comp K.subtypeL).codRestrict K fun x => hLK x x.2
  have hLK' : ∀ x : K, RCLike.re ⟪LK x, x⟫ ≤ 0 := fun x => by
    rw [Submodule.coe_inner]; exact hL x
  have hz := re_inv_mul_pos hθ hτ
  have hRK := (LK.isMDissipative_toPMap_top hLK').isResolvent_of_re_pos hz
  have hR := (L.isMDissipative_toPMap_top hL).isResolvent_of_re_pos hz
  refine thetaStep_mem (fun y hy => ?_) hu
  set x : K := resolvent ((LK : K →ₗ[𝕜] K).toPMap ⊤) (θ * (τ : 𝕜))⁻¹ ⟨y, hy⟩
  have hx : (θ * (τ : 𝕜))⁻¹ • (x : X) - L x = y := congrArg Subtype.val (hRK.sub_apply ⟨y, hy⟩)
  have h2 : resolvent ((L : X →ₗ[𝕜] X).toPMap ⊤) (θ * (τ : 𝕜))⁻¹
      ((θ * (τ : 𝕜))⁻¹ • (x : X) - L x) = x := hR.apply_sub ⟨(x : X), trivial⟩
  rw [hx] at h2
  rw [h2]
  exact x.2

end Bounded

end Feec.TimeStepping
