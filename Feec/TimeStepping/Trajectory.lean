module

public import Feec.TimeStepping.Convergence
public import Feec.ForMathlib.Calculus.SecondDifference

/-!
# Consistency of one-step schemes along trajectories

`Feec.TimeStepping.IsConsistent` measures a scheme `P` against the flow `e^{τL}` in operator form,
`‖P y - e^{τL} y‖ ≤ K τ^{p+1} ‖L^{p+1} y‖`, so the global error of `Pⁿ v` is controlled by
`‖L^{p+1} v‖`. On finite element spaces `‖Lₕ‖` grows as `h → 0`, and a bound on `‖Lₕ^{p+1} vₕ‖`
uniform in `h` is not available for the usual discrete initial values. The classical way out
([Thomee2006], Ch. 1 and 7) tests the scheme on a **smooth comparison trajectory** instead (the
Ritz projection of the exact solution): the local error of `P` on a curve `q` is the quadrature
remainder of `q`, bounded by its `(p + 1)`-st time derivative, plus the defect `q' - L q`. This
file states that property and proves it for the θ-schemes.

## Main results

* **Quadrature remainders** with right derivatives (`norm_thetaRule_le`, `norm_trapezoid_le`): for
  `f` with right derivatives `f₁, f₂(, f₃)` on `[a, b)`,
  `‖f(b) - f(a) - (b - a) (θ f₁(b) + (1 - θ) f₁(a))‖ ≤ (θ + 1/2) (b - a)² sup ‖f₂‖` (`θ ≥ 0`) and
  `‖f(b) - f(a) - (b - a)/2 (f₁(b) + f₁(a))‖ ≤ (b - a)³/12 sup ‖f₃‖` (the sharp constant).
* `norm_le_norm_sub_smul_apply`: `‖e‖ ≤ ‖e - c L e‖` for dissipative `L` and `c ≥ 0`.
* `IsTrajConsistent L P τ p K`: for every curve `q₀` on `[a, a + τ]` with right derivatives
  `q₁, …, q_{p+1}`, `‖q_{p+1}‖ ≤ B` and `‖q₁ - L q₀‖ ≤ D`,
  `‖q₀(a + τ) - P q₀(a)‖ ≤ K τ^{p+1} B + τ D`.
* `norm_sub_thetaStep_le`: the local error of the θ-scheme (`0 < θ ≤ 1`) is at most the θ-rule
  remainder plus `τ D`; hence **`isTrajConsistent_thetaStep`** (order `1`, `K = θ + 1/2`) and
  **`isTrajConsistent_thetaStep_half`** (Crank–Nicolson, order `2`, `K = 1/12`), uniformly in the
  bounded dissipative `L`.

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 1 (the
  Ritz projection of the exact solution as comparison function, backward Euler and
  Crank–Nicolson), Ch. 7 (single step methods)
* [M. F. Wheeler, *A priori L₂ error estimates for Galerkin approximations to parabolic partial differential equations*][Wheeler1973]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set

@[expose] public noncomputable section

namespace Feec.TimeStepping

/-! ### Quadrature remainders with right derivatives -/

section Quadrature

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **The θ-rule remainder** (`θ ≥ 0`): for `f` with right derivatives `f₁`, `f₂` on `[a, b)`
and `‖f₂‖ ≤ B`, `‖f(b) - f(a) - (b - a) (θ f₁(b) + (1 - θ) f₁(a))‖ ≤ (θ + 1/2) (b - a)² B`. -/
theorem norm_thetaRule_le {f f₁ f₂ : ℝ → X} {a b θ B : ℝ} (hab : a ≤ b) (hθ : 0 ≤ θ)
    (hf : ContinuousOn f (Icc a b)) (hf₁ : ContinuousOn f₁ (Icc a b))
    (h1 : ∀ t ∈ Ico a b, HasDerivWithinAt f (f₁ t) (Ici t) t)
    (h2 : ∀ t ∈ Ico a b, HasDerivWithinAt f₁ (f₂ t) (Ici t) t)
    (hB : ∀ t ∈ Ico a b, ‖f₂ t‖ ≤ B) :
    ‖f b - f a - (b - a) • (θ • f₁ b + (1 - θ) • f₁ a)‖ ≤ (θ + 1 / 2) * (b - a) ^ 2 * B := by
  have hd : ∀ t ∈ Icc a b, ‖f₁ t - f₁ a‖ ≤ B * (t - a) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment hf₁ h2 hB
  have hg := norm_image_le_of_norm_deriv_le_pow (g := fun t => f t - f a - (t - a) • f₁ a)
    (g' := fun t => f₁ t - f₁ a) (c := B) 1
    ((hf.sub continuousOn_const).sub ((continuousOn_id.sub continuousOn_const).smul
      continuousOn_const))
    (fun t ht => by
      have := ((h1 t ht).sub_const (f a)).sub
        ((((hasDerivAt_id t).sub_const a).hasDerivWithinAt).smul_const (f₁ a))
      exact this.congr_deriv (by simp))
    (by simp) (fun t ht => by rw [pow_one]; exact hd t (Ico_subset_Icc_self ht))
    b ⟨hab, le_rfl⟩
  have hb := hd b ⟨hab, le_rfl⟩
  have e : f b - f a - (b - a) • (θ • f₁ b + (1 - θ) • f₁ a) =
      (f b - f a - (b - a) • f₁ a) - ((b - a) * θ) • (f₁ b - f₁ a) := by module
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.2 hab) hθ)]
  have : (b - a) * θ * ‖f₁ b - f₁ a‖ ≤ (b - a) * θ * (B * (b - a)) :=
    mul_le_mul_of_nonneg_left hb (mul_nonneg (sub_nonneg.2 hab) hθ)
  have hg' : ‖f b - f a - (b - a) • f₁ a‖ ≤ B * (b - a) ^ 2 / 2 := by
    convert hg using 2; norm_num
  nlinarith

/-- **The backward Euler remainder**: for `f` with derivatives `f₁`, `f₂` on `[a, a + τ]` and
`‖f₂‖ ≤ B`, `‖f(a + τ) - f(a) - τ f₁(a + τ)‖ ≤ 3/2 τ² B` (`norm_thetaRule_le`, `θ = 1`). -/
theorem norm_sub_sub_smul_le {f f₁ f₂ : ℝ → X} {a τ B : ℝ} (hτ : 0 ≤ τ)
    (hf : ∀ t ∈ Icc a (a + τ), HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Icc a (a + τ), HasDerivAt f₁ (f₂ t) t) (hB : ∀ t ∈ Icc a (a + τ), ‖f₂ t‖ ≤ B) :
    ‖f (a + τ) - f a - τ • f₁ (a + τ)‖ ≤ 3 / 2 * τ ^ 2 * B := by
  have hq := norm_thetaRule_le (f := f) (f₁ := f₁) (f₂ := f₂) (θ := 1) (B := B)
    (le_add_of_nonneg_right hτ) zero_le_one
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf₁ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => (hf₁ t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hB t (Ico_subset_Icc_self ht))
  simp only [add_sub_cancel_left, one_smul, sub_self, zero_smul, add_zero] at hq
  convert hq using 2; norm_num

/-- **The trapezoidal (Crank–Nicolson) remainder**, with the sharp constant: for `f` with right
derivatives `f₁`, `f₂`, `f₃` on `[a, b)` and `‖f₃‖ ≤ B`,
`‖f(b) - f(a) - (b - a)/2 (f₁(b) + f₁(a))‖ ≤ (b - a)³ B / 12`. -/
theorem norm_trapezoid_le {f f₁ f₂ f₃ : ℝ → X} {a b B : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hf₁ : ContinuousOn f₁ (Icc a b))
    (hf₂ : ContinuousOn f₂ (Icc a b))
    (h1 : ∀ t ∈ Ico a b, HasDerivWithinAt f (f₁ t) (Ici t) t)
    (h2 : ∀ t ∈ Ico a b, HasDerivWithinAt f₁ (f₂ t) (Ici t) t)
    (h3 : ∀ t ∈ Ico a b, HasDerivWithinAt f₂ (f₃ t) (Ici t) t)
    (hB : ∀ t ∈ Ico a b, ‖f₃ t‖ ≤ B) :
    ‖f b - f a - ((b - a) / 2) • (f₁ b + f₁ a)‖ ≤ (b - a) ^ 3 * B / 12 := by
  have hc : ∀ t, HasDerivAt (fun t : ℝ => (t - a) / 2) (1 / 2) t := fun t => by
    simpa using ((hasDerivAt_id t).sub_const a).div_const 2
  have hcc : ContinuousOn (fun t : ℝ => (t - a) / 2) (Icc a b) :=
    (continuousOn_id.sub continuousOn_const).div_const 2
  -- `k = g'`, with `k' = -((t - a)/2) f₃`
  have hk := norm_image_le_of_norm_deriv_le_pow
    (g := fun t => (1 / 2 : ℝ) • (f₁ t - f₁ a) - ((t - a) / 2) • f₂ t)
    (g' := fun t => -(((t - a) / 2) • f₃ t)) (c := B / 2) 1
    (((hf₁.sub continuousOn_const).const_smul _).sub (hcc.smul hf₂))
    (fun t ht => by
      have e1 := ((h2 t ht).sub_const (f₁ a)).const_smul (1 / 2 : ℝ)
      have e2 := (hc t).hasDerivWithinAt.smul (h3 t ht)
      exact (e1.sub e2).congr_deriv (by module))
    (by simp)
    (fun t ht => by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1]), pow_one]
      have := hB t ht
      have : 0 ≤ (t - a) / 2 := by linarith [ht.1]
      nlinarith)
  have hg := norm_image_le_of_norm_deriv_le_pow
    (g := fun t => f t - f a - ((t - a) / 2) • (f₁ t + f₁ a))
    (g' := fun t => (1 / 2 : ℝ) • (f₁ t - f₁ a) - ((t - a) / 2) • f₂ t) (c := B / 4) 2
    ((hf.sub continuousOn_const).sub (hcc.smul (hf₁.add continuousOn_const)))
    (fun t ht => by
      have e1 := (h1 t ht).sub_const (f a)
      have e2 := (hc t).hasDerivWithinAt.smul ((h2 t ht).add_const (f₁ a))
      exact (e1.sub e2).congr_deriv (by module))
    (by simp)
    (fun t ht => (hk t (Ico_subset_Icc_self ht)).trans_eq (by ring))
    b ⟨hab, le_rfl⟩
  exact hg.trans_eq (by ring)

end Quadrature

/-! ### Consistency along trajectories -/

section Bounded

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] {L : X →L[𝕜] X}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
/-- `1 - c L` does not decrease norms for dissipative `L` and `c ≥ 0`: `‖e‖ ≤ ‖e - c L e‖`. -/
theorem norm_le_norm_sub_smul_apply (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {c : ℝ} (hc : 0 ≤ c)
    (e : X) : ‖e‖ ≤ ‖e - (c : 𝕜) • L e‖ := by
  have h1 : ‖e‖ ^ 2 ≤ RCLike.re ⟪e - (c : 𝕜) • L e, e⟫ := by
    rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal, _root_.map_sub,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    nlinarith [hL e]
  have h2 := re_inner_le_norm (𝕜 := 𝕜) (e - (c : 𝕜) • L e) e
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg (e - (c : 𝕜) • L e)]

/-- A scheme `P` is **consistent of order `p` with constant `K` along trajectories** of
`u' = L u` with time step `τ`: for every curve `q 0` on `[a, a + τ]` with right derivatives
`q 1, …, q (p + 1)` (`q j` the `j`-th), `‖q (p + 1)‖ ≤ B` and defect `‖q 1 - L (q 0)‖ ≤ D`,
`‖q 0 (a + τ) - P (q 0 a)‖ ≤ K τ^{p+1} B + τ D`. [Thomee2006], Ch. 1 and 7 -/
def IsTrajConsistent (L P : X →L[𝕜] X) (τ : ℝ) (p : ℕ) (K : ℝ) : Prop :=
  ∀ (q : ℕ → ℝ → X) (a B D : ℝ),
    (∀ j ≤ p, ContinuousOn (q j) (Icc a (a + τ))) →
    (∀ j ≤ p, ∀ t ∈ Ico a (a + τ), HasDerivWithinAt (q j) (q (j + 1) t) (Ici t) t) →
    (∀ t ∈ Ico a (a + τ), ‖q (p + 1) t‖ ≤ B) →
    (∀ t ∈ Icc a (a + τ), ‖q 1 t - L (q 0 t)‖ ≤ D) →
    ‖q 0 (a + τ) - P (q 0 a)‖ ≤ K * τ ^ (p + 1) * B + τ * D

variable [CompleteSpace X]

/-- **The local error of the θ-scheme** (`0 < θ ≤ 1`, `τ > 0`, `L` bounded dissipative): for
states `y`, `u` with velocities `y₁`, `u₁` and defects `‖y₁ - L y‖, ‖u₁ - L u‖ ≤ D`,
`‖y - r_θ(τ L) u‖ ≤ ‖y - u - τ (θ y₁ + (1 - θ) u₁)‖ + τ D`: the θ-rule remainder plus the
defect. -/
theorem norm_sub_thetaStep_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {θ τ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hτ : 0 < τ) {y u y₁ u₁ : X} {D : ℝ} (hy : ‖y₁ - L y‖ ≤ D)
    (hu : ‖u₁ - L u‖ ≤ D) :
    ‖y - thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ u‖ ≤
      ‖y - u - τ • (θ • y₁ + (1 - θ) • u₁)‖ + τ * D := by
  set u' := thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ u
  obtain ⟨_, hs⟩ := isThetaStep_thetaStep_of_isMDissipative (L.isMDissipative_toPMap_top hL)
    (θ := (θ : 𝕜)) (by rwa [RCLike.ofReal_re]) hτ u
  change u' - u = (τ : 𝕜) • L ((θ : 𝕜) • u' + (1 - (θ : 𝕜)) • u) at hs
  -- `e = y - u'` solves `(1 - θ τ L) e = r` with `r` the local residual
  have he : (y - u') - ((θ * τ : ℝ) : 𝕜) • L (y - u') =
      (y - u - τ • (θ • y₁ + (1 - θ) • u₁)) +
        τ • (θ • (y₁ - L y) + (1 - θ) • (u₁ - L u)) := by
    simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜), _root_.map_sub, _root_.map_add,
      _root_.map_smul, smul_sub, smul_add] at hs ⊢
    push_cast
    linear_combination (norm := module) -hs
  refine (norm_le_norm_sub_smul_apply hL (mul_nonneg hθ.le hτ.le) (y - u')).trans ?_
  rw [he]
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hτ.le
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hθ,
    abs_of_nonneg (by linarith)]
  nlinarith

/-- **The θ-scheme is consistent of order `1` along trajectories** with constant `θ + 1/2`
(`0 < θ ≤ 1`, `τ > 0`), uniformly in the bounded dissipative `L`. [Thomee2006], Ch. 1 -/
theorem isTrajConsistent_thetaStep (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {θ τ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hτ : 0 < τ) :
    IsTrajConsistent L (thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ) τ 1 (θ + 1 / 2) := by
  intro q a B D hc hd hB hD
  have hab : a ≤ a + τ := by linarith
  refine (norm_sub_thetaStep_le hL hθ hθ1 hτ (hD _ ⟨hab, le_rfl⟩) (hD _ ⟨le_rfl, hab⟩)).trans ?_
  have hq := norm_thetaRule_le (f := q 0) (f₁ := q 1) (f₂ := q 2) hab hθ.le (hc 0 (by omega))
    (hc 1 le_rfl) (hd 0 (by omega)) (hd 1 le_rfl) hB
  rw [add_sub_cancel_left] at hq
  linarith

/-- **Crank–Nicolson is consistent of order `2` along trajectories** with constant `1/12`
(`τ > 0`), uniformly in the bounded dissipative `L`. [Thomee2006], Ch. 1 -/
theorem isTrajConsistent_thetaStep_half (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {τ : ℝ}
    (hτ : 0 < τ) :
    IsTrajConsistent L (thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) ((1 / 2 : ℝ) : 𝕜) τ) τ 2
      (1 / 12) := by
  intro q a B D hc hd hB hD
  have hab : a ≤ a + τ := by linarith
  refine (norm_sub_thetaStep_le hL (by norm_num) (by norm_num) hτ (hD _ ⟨hab, le_rfl⟩)
    (hD _ ⟨le_rfl, hab⟩)).trans ?_
  have hq := norm_trapezoid_le (f := q 0) (f₁ := q 1) (f₂ := q 2) (f₃ := q 3) hab
    (hc 0 (by omega)) (hc 1 (by omega)) (hc 2 le_rfl) (hd 0 (by omega)) (hd 1 (by omega))
    (hd 2 le_rfl) hB
  rw [add_sub_cancel_left] at hq
  have e : q 0 (a + τ) - q 0 a - τ • ((1 / 2 : ℝ) • q 1 (a + τ) + (1 - 1 / 2 : ℝ) • q 1 a) =
      q 0 (a + τ) - q 0 a - (τ / 2) • (q 1 (a + τ) + q 1 a) := by module
  rw [e]
  linarith

end Bounded

end Feec.TimeStepping
