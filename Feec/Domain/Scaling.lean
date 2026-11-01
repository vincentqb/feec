module

public import Feec.Domain.Affine
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Rescaled test fields: homogeneous operators of positive order are unbounded

Let `B` be a constant-coefficient operator homogeneous of order `r > 0` on a finite-dimensional
real space `E` (`ℝⁿ`) and `ψ` a smooth compactly supported field with `B ψ ≠ 0`. Concentrating
`ψ` at a point `x₀`, `ψₐ = ψ (a (· - x₀))`, multiplies `‖ψ‖_{L²}` by `a^{-n/2}` and `‖B ψ‖_{L²}`
by `a^{r - n/2}` (the chain rule `ConstCoeffOp.apply_comp_aff` and the change of variables
`integral_comp_aff`). So on every nonempty open `Ω`, for every `C`, some rescaling of `ψ` is a
test field on `Ω` with `‖B ψₐ‖ > C ‖ψₐ‖` (**`ConstCoeffOp.exists_lt_norm_testField_comp_aff`**):
no bound `‖B φ‖ ≤ C ‖φ‖` holds on the test fields of `Ω` that a second homogeneous operator
annihilates along with `ψ`. This is the scaling argument that fixes the exponent of the
Gagliardo–Nirenberg–Sobolev inequality ([Evans2010], §5.6.1), here showing that a space defined by
some first derivatives is not one defined by all of them, e.g. `H(curl) ⊄ H¹` (`ψ = ∇χ`); it is
used for the connecting maps of the `L²` BGG diagrams in `Feec.Domain.BGGRealization`.

The nonvanishing of `B ψ` is checked through `fderiv_apply_ne_zero`: a nonzero compactly
supported `C¹` function has nonzero directional derivatives (it is constant along the lines on
which the derivative vanishes, and these leave its support).

## Main results

* `fderiv_apply_ne_zero`, `IsTest.fderiv_apply_ne_zero`, `exists_isTest_univ_ne_zero`,
  `norm_sq_testField`, `integral_comp_aff`.
* **`ConstCoeffOp.exists_lt_norm_testField_comp_aff`**.

## References

* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.6.1 (the scaling argument)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (change of variables in Sobolev spaces)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff ComplexConjugate
open MeasureTheory Set Metric

@[expose] public noncomputable section

namespace Feec.Domain

/-! ### Directional derivatives of compactly supported functions -/

section Deriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **A nonzero compactly supported differentiable function has nonzero directional
derivatives**: if `∂ᵥ f = 0`, then `f` is constant along the lines `x + ℝ v`, which leave its
support. -/
theorem fderiv_apply_ne_zero {f : E → F} (hf : Differentiable ℝ f) (hc : HasCompactSupport f)
    (hf0 : f ≠ 0) {v : E} (hv : v ≠ 0) : (fun x => fderiv ℝ f x v) ≠ 0 := by
  intro h
  refine hf0 (funext fun x => ?_)
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  set t := (R + ‖x‖ + 1) / ‖v‖
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + s • v) v) s :=
    fun s => (hf (x + s • v)).hasFDerivAt.comp_hasDerivAt s
      (by simpa using ((hasDerivAt_id s).smul_const v).const_add x)
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => by rw [(hd s).deriv]; simpa using congrFun h (x + s • v)) t 0
  simp only [zero_smul, add_zero] at hconst
  rw [Pi.zero_apply, ← hconst]
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have hle := mem_closedBall_zero_iff.1 (hR hmem)
  have htv : ‖t • v‖ ≤ ‖x + t • v‖ + ‖x‖ := by
    calc ‖t • v‖ = ‖(x + t • v) - x‖ := by rw [add_sub_cancel_left]
      _ ≤ _ := norm_sub_le _ _
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hle
  have ht : 0 < t := div_pos (by linarith [norm_nonneg x]) hv'
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, div_mul_cancel₀ _ hv'.ne'] at htv
  linarith

/-- The directional derivatives of a nonzero test function are nonzero. -/
theorem IsTest.fderiv_apply_ne_zero {Ω : Set E} {f : E → F} (hf : IsTest Ω f) (hf0 : f ≠ 0)
    {v : E} (hv : v ≠ 0) : (fun x => fderiv ℝ f x v) ≠ 0 :=
  Feec.Domain.fderiv_apply_ne_zero hf.differentiable hf.hasCompactSupport hf0 hv

variable (E) in
/-- A nonzero test function on a finite-dimensional space (a smooth bump). -/
theorem exists_isTest_univ_ne_zero [FiniteDimensional ℝ E] (𝕜 : Type*) [RCLike 𝕜] :
    ∃ χ : E → 𝕜, IsTest univ χ ∧ χ ≠ 0 := by
  let f : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun x => (f x : 𝕜), IsTest.ofReal ⟨f.contDiff, f.hasCompactSupport, subset_univ _⟩,
    fun h => ?_⟩
  have h0 := congrFun h 0
  rw [f.one_of_mem_closedBall (mem_closedBall_self zero_le_one)] at h0
  simp at h0

end Deriv

/-! ### `L²` norms of test fields and of their rescalings -/

section Norm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] {𝕜 : Type*} [RCLike 𝕜]
  {Ω : Set E} {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] in
/-- `‖φ‖²_{L²(Ω)} = Σᵢ ∫_E |φᵢ|²` for a test field `φ` (the integrand vanishes off `Ω`). -/
theorem norm_sq_testField {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) :
    ‖testField hφ‖ ^ 2 = ∑ i, ∫ x, ‖φ i x‖ ^ 2 := by
  have h := inner_testField_toL2F hφ fun i => (hφ i).memLp
  change ⟪testField hφ, testField hφ⟫_𝕜 = _ at h
  rw [@norm_sq_eq_re_inner 𝕜, h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [RCLike.conj_mul, ← RCLike.ofReal_pow]
  rw [integral_ofReal, RCLike.ofReal_re]

/-- **Change of variables along `aff a b`**: `∫ g (a x + b) dx = |a|^{-n} ∫ g`. -/
theorem integral_comp_aff {a : ℝ} (ha : a ≠ 0) (b : E) (g : E → ℝ) :
    ∫ x, g (aff a b x) = (jac (E := E) a)⁻¹ * ∫ y, g y := by
  have h := (measurePreserving_aff ha b).integral_comp
    (affHomeomorph ha b).measurableEmbedding g
  rw [integral_smul_measure, ENNReal.toReal_ofReal (jac_pos ha).le, smul_eq_mul] at h
  rw [← h, inv_mul_cancel_left₀ (jac_pos ha).ne']

/-- **Homogeneous operators of positive order are unbounded on rescaled test fields.** If `B` is
homogeneous of order `r > 0` and `B ψ ≠ 0` for a smooth compactly supported field `ψ`, then on
every nonempty open `Ω`, for every `C`, a rescaling `ψ ∘ aff a b` (`a > 0`) of `ψ` is a test
field on `Ω` with `C ‖ψ ∘ aff a b‖ < ‖B (ψ ∘ aff a b)‖` in `L²(Ω)`. -/
theorem ConstCoeffOp.exists_lt_norm_testField_comp_aff (hΩ : IsOpen Ω) (hne : Ω.Nonempty)
    {κ : Type*} [Fintype κ] {B : ConstCoeffOp E 𝕜 ι κ} {r : ℕ} (hB : B.IsHomogeneous r)
    (hr : 0 < r) {ψ : ι → E → 𝕜} (hψ : IsTestField univ ψ) (hBψ : B.apply ψ ≠ 0) (C : ℝ) :
    ∃ (a : ℝ) (b : E) (hφ : IsTestField Ω fun i x => ψ i (aff a b x)),
      C * ‖testField hφ‖ < ‖testField (B.isTestField_apply hφ)‖ := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  obtain ⟨R, hR⟩ := (isCompact_iUnion fun i => (hψ i).hasCompactSupport.isCompact).isBounded
    |>.subset_closedBall 0
  set S₀ := ∑ i, ∫ y, ‖ψ i y‖ ^ 2
  set S₁ := ∑ j, ∫ y, ‖B.apply ψ j y‖ ^ 2
  have hS₀ : 0 ≤ S₀ := Finset.sum_nonneg fun i _ => integral_nonneg fun _ => by positivity
  have hS₁ : 0 < S₁ := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hBψ
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hj
    have hBj := B.isTestField_apply hψ j
    refine Finset.sum_pos' (fun j _ => integral_nonneg fun _ => by positivity)
      ⟨j, Finset.mem_univ _, ?_⟩
    refine (hBj.continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hBj.hasCompactSupport.comp_left (g := fun z : 𝕜 => ‖z‖ ^ 2) (by simp))
      (fun _ => by positivity) (x := y) ?_
    simpa using hy
  set C' := max C 0
  set a := max 1 (max (R / ρ + 1) (C' ^ 2 * S₀ / S₁ + 1))
  have ha1 : 1 ≤ a := le_max_left _ _
  have ha : 0 < a := one_pos.trans_le ha1
  have haR : R / ρ < a := by
    have := le_max_left (R / ρ + 1) (C' ^ 2 * S₀ / S₁ + 1)
    linarith [le_max_right 1 (max (R / ρ + 1) (C' ^ 2 * S₀ / S₁ + 1))]
  have haC : C' ^ 2 * S₀ / S₁ < a := by
    have := le_max_right (R / ρ + 1) (C' ^ 2 * S₀ / S₁ + 1)
    linarith [le_max_right 1 (max (R / ρ + 1) (C' ^ 2 * S₀ / S₁ + 1))]
  set b : E := -(a • x₀)
  have hsub : aff a b ⁻¹' closedBall 0 R ⊆ Ω := fun x hx => by
    refine hball (mem_ball_iff_norm.2 ?_)
    have hx' : ‖a • (x - x₀)‖ ≤ R := by
      simpa [aff, b, smul_sub, sub_eq_add_neg] using mem_closedBall_zero_iff.1 hx
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hx'
    rw [div_lt_iff₀ hρ] at haR
    nlinarith [norm_nonneg (x - x₀)]
  have hφ : IsTestField Ω fun i x => ψ i (aff a b x) := fun i =>
    (IsTest.comp_aff' ha.ne' b rfl ⟨(hψ i).contDiff, (hψ i).hasCompactSupport,
      (subset_iUnion (fun i => tsupport (ψ i)) i).trans hR⟩).mono hsub
  refine ⟨a, b, hφ, ?_⟩
  have hj : 0 < jac (E := E) a := jac_pos ha.ne'
  have hu : ‖testField hφ‖ ^ 2 = (jac (E := E) a)⁻¹ * S₀ := by
    rw [norm_sq_testField, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => integral_comp_aff ha.ne' b fun y => ‖ψ i y‖ ^ 2
  have hv : ‖testField (B.isTestField_apply hφ)‖ ^ 2 = a ^ (2 * r) * ((jac (E := E) a)⁻¹ * S₁) := by
    rw [norm_sq_testField, ConstCoeffOp.apply_comp_aff hB (fun i => (hψ i).contDiff) a b,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [norm_mul, RCLike.norm_ofReal, mul_pow, abs_pow, abs_of_pos ha, ← pow_mul,
      mul_comm r 2]
    rw [integral_const_mul, integral_comp_aff ha.ne' b fun y => ‖B.apply ψ j y‖ ^ 2]
  have hC : C ≤ C' := le_max_left _ _
  have hC0 : 0 ≤ C' := le_max_right _ _
  refine (mul_le_mul_of_nonneg_right hC (norm_nonneg _)).trans_lt ?_
  refine (pow_lt_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
  rw [mul_pow, hu, hv]
  have hapow : a ≤ a ^ (2 * r) := le_self_pow₀ ha1 (by omega)
  have key : C' ^ 2 * S₀ < a ^ (2 * r) * S₁ := by
    rw [div_lt_iff₀ hS₁] at haC
    nlinarith
  have hjinv : 0 < (jac (E := E) a)⁻¹ := inv_pos.2 hj
  nlinarith

end Norm

end Feec.Domain
