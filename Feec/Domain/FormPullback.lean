module

public import Feec.Domain.DeRham
public import Feec.HilbertComplex.Transport

/-!
# Pullback of `L²` differential forms along invertible affine maps

Let `T x = A x + b` be an affine map of `ℝⁿ` with `A` invertible, `Ω' ⊆ ℝⁿ` open and
`Ω = T⁻¹(Ω')`. The composition `f ↦ f ∘ T` is a bounded isomorphism `L²(Ω') ≃ L²(Ω)`:
`T` is measure preserving from `|det A| · volume` to `volume` (`measurePreserving_affMap`), so
`‖f ∘ T‖ = |det A|^{-1/2} ‖f‖` (`norm_affPull`). A field pullback with a constant fibre matrix
`C`, `(T^* u)_s = Σ_t C_{st} u_t ∘ T` (`fieldPull`), is then a bounded operator
`L²(Ω'; ℝ^ι) → L²(Ω; ℝ^κ)` with `‖T^* u‖ ≤ |det A|^{-1/2} (Σ_{s,t} |C_{st}|) ‖u‖`
(`norm_fieldPull_le`), invertible with inverse the field pullback along `T⁻¹` when the fibre
matrices are inverse to each other (`fieldPullEquiv`).

For `k`-forms the fibre matrix of the pullback is the matrix of `k × k` minors of `A`
(`Feec.ExteriorFibre.pullback` in `Feec.FiniteElement.SmoothForm`); that it intertwines the
exterior derivative of smooth forms, `d (T^* φ) = T^* (d φ)`, is a classical computation done
there (`Feec.FiniteElement.extDeriv_affinePullback_apply`). This module takes the fibre matrices
as data, together with the classical intertwining (`IsDIntertwining`), and proves the `L²`
statements, for every constant-coefficient operator `P` with a classical intertwining
`P (T^* φ) = T^* (P' φ)` (`IsPullIntertwining`; `d`, and the gradient in
`Feec.Domain.RegularDecomposition`):

* `T^*` maps test forms to test forms (`fieldPull_testField`), and its `L²` adjoint on test forms
  is the pushforward `(T^♯ ψ)_t = |det A|⁻¹ Σ_s C_{st} ψ_s ∘ T⁻¹` (`inner_fieldPull_testField`);
* **`T^*` maps `D(P'_min)` into `D(P_min)` and `D(P'_max)` into `D(P_max)` and intertwines the
  realizations** (`fieldPull_mem_minimal_domain`, `minimal_fieldPull`,
  `fieldPull_mem_maximal_domain`): `P_min` is the closure of `P` on test fields, and `P_max` is
  tested against test fields, on which the pushforward intertwines the formal adjoints by duality
  (`testField_push_formalAdj`); for `d` this is `IsDIntertwining.isPullIntertwining`;
* with an inverse pullback, **the de Rham complexes `HΛ(Ω)` and `H̊Λ(Ω)` are the transports of
  `HΛ(Ω')` and `H̊Λ(Ω')` along `T^*`** (`maximalComplex_eq_transport`,
  `minimalComplex_eq_transport`): `d_Ω = T^* d_{Ω'} (T^*)⁻¹` with the same domains.

## References

* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
  (affine-equivalent families, change of variables)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4 (pullback of `L²` forms, the de Rham complex under bi-Lipschitz maps)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (change of variables in Sobolev spaces)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff ENNReal
open MeasureTheory Set Filter Topology Module

@[expose] public noncomputable section

namespace Feec.Domain

variable {n : ℕ}

/-! ### The affine map `x ↦ A x + b` -/

section AffMap

variable (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)

/-- The affine map `x ↦ A x + b`. -/
def affMap (x : Fin n → ℝ) : Fin n → ℝ := A.mulVec x + b

theorem affMap_apply (x : Fin n → ℝ) (i : Fin n) :
    affMap A b x i = ∑ j, A i j * x j + b i := by
  simp [affMap, Matrix.mulVec, dotProduct]

theorem affMap_eq_toLin' : affMap A b = fun x => Matrix.toLin' A x + b := by
  funext x; simp [affMap, Matrix.toLin'_apply]

theorem continuous_affMap : Continuous (affMap A b) := by
  rw [affMap_eq_toLin']
  exact (Matrix.toLin' A).continuous_of_finiteDimensional.add continuous_const

theorem contDiff_affMap {r : WithTop ℕ∞} : ContDiff ℝ r (affMap A b) := by
  rw [affMap_eq_toLin']
  exact (Matrix.toLin' A).toContinuousLinearMap.contDiff.add contDiff_const

theorem hasFDerivAt_affMap (x : Fin n → ℝ) :
    HasFDerivAt (affMap A b) (Matrix.toLin' A).toContinuousLinearMap x := by
  rw [affMap_eq_toLin']
  exact (Matrix.toLin' A).toContinuousLinearMap.hasFDerivAt.add_const b

/-- The translation part `-A⁻¹ b` of the inverse map. -/
def affInvShift : Fin n → ℝ := -(A⁻¹.mulVec b)

variable {A}

theorem affMap_inv_affMap (hA : IsUnit A.det) (x : Fin n → ℝ) :
    affMap A⁻¹ (affInvShift A b) (affMap A b x) = x := by
  simp [affMap, affInvShift, Matrix.mulVec_add, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul A hA]

theorem affMap_affMap_inv (hA : IsUnit A.det) (y : Fin n → ℝ) :
    affMap A b (affMap A⁻¹ (affInvShift A b) y) = y := by
  simp [affMap, affInvShift, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_neg,
    Matrix.mul_nonsing_inv A hA]

/-- `x ↦ A x + b` as a homeomorphism. -/
def affHomeo (hA : IsUnit A.det) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) where
  toFun := affMap A b
  invFun := affMap A⁻¹ (affInvShift A b)
  left_inv := affMap_inv_affMap b hA
  right_inv := affMap_affMap_inv b hA
  continuous_toFun := continuous_affMap A b
  continuous_invFun := continuous_affMap _ _

@[simp] theorem coe_affHomeo (hA : IsUnit A.det) : ⇑(affHomeo b hA) = affMap A b := rfl

/-- `x ↦ A x + b` as a measurable equivalence. -/
def affMeasEquiv (hA : IsUnit A.det) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) where
  toEquiv := (affHomeo b hA).toEquiv
  measurable_toFun := (continuous_affMap A b).measurable
  measurable_invFun := (continuous_affMap _ _).measurable

@[simp] theorem coe_affMeasEquiv (hA : IsUnit A.det) : ⇑(affMeasEquiv b hA) = affMap A b := rfl

theorem preimage_inv_preimage (hA : IsUnit A.det) (Ω : Set (Fin n → ℝ)) :
    affMap A⁻¹ (affInvShift A b) ⁻¹' (affMap A b ⁻¹' Ω) = Ω := by
  ext y; simp only [mem_preimage, affMap_affMap_inv b hA]

theorem preimage_preimage_inv (hA : IsUnit A.det) (Ω : Set (Fin n → ℝ)) :
    affMap A b ⁻¹' (affMap A⁻¹ (affInvShift A b) ⁻¹' Ω) = Ω := by
  ext y; simp only [mem_preimage, affMap_inv_affMap b hA]

theorem isUnit_det_inv (hA : IsUnit A.det) : IsUnit (A⁻¹).det := by
  rw [Matrix.det_nonsing_inv]; exact hA.ringInverse

/-- **`x ↦ A x + b` is measure preserving from `|det A| · volume` to `volume`.** -/
theorem measurePreserving_affMap (hA : IsUnit A.det) :
    MeasurePreserving (affMap A b) (ENNReal.ofReal |A.det| • volume) volume := by
  refine ⟨(continuous_affMap A b).measurable, ?_⟩
  have hdet : LinearMap.det (Matrix.toLin' A) = A.det := LinearMap.det_toLin' A
  have hdet0 : LinearMap.det (Matrix.toLin' A) ≠ 0 := by rw [hdet]; exact hA.ne_zero
  have hlin : Measure.map (Matrix.toLin' A) (volume : Measure (Fin n → ℝ)) =
      ENNReal.ofReal |(A.det)⁻¹| • volume := by
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℝ)) hdet0
    rwa [hdet] at this
  have htr : Measure.map (fun y : Fin n → ℝ => y + b) (volume : Measure (Fin n → ℝ)) = volume :=
    map_add_right_eq_self volume b
  have hm : Measurable (Matrix.toLin' A) := (Matrix.toLin' A).continuous_of_finiteDimensional.measurable
  have hcomp : Measure.map (affMap A b) (volume : Measure (Fin n → ℝ)) =
      Measure.map (fun y => y + b) (Measure.map (Matrix.toLin' A) volume) := by
    rw [Measure.map_map (measurable_add_const b) hm, affMap_eq_toLin']; rfl
  rw [Measure.map_smul (hf := (continuous_affMap A b).measurable.aemeasurable), hcomp, hlin,
    Measure.map_smul (hf := (measurable_add_const b).aemeasurable), htr, smul_smul,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  rw [show |A.det| * |(A.det)⁻¹| = 1 by
    rw [abs_inv, mul_inv_cancel₀ (abs_ne_zero.2 hA.ne_zero)], ENNReal.ofReal_one, one_smul]

theorem measurePreserving_affMap_restrict (hA : IsUnit A.det) {Ω' : Set (Fin n → ℝ)}
    (hΩ' : MeasurableSet Ω') :
    MeasurePreserving (affMap A b)
      (ENNReal.ofReal |A.det| • volume.restrict (affMap A b ⁻¹' Ω')) (volume.restrict Ω') := by
  rw [← Measure.restrict_smul]
  exact (measurePreserving_affMap b hA).restrict_preimage hΩ'

theorem abs_det_pos (hA : IsUnit A.det) : 0 < |A.det| := abs_pos.2 hA.ne_zero

end AffMap

/-! ### The pullback of scalar `L²` functions -/

section Pull

variable {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) (b : Fin n → ℝ)
  {Ω Ω' : Set (Fin n → ℝ)} (hΩ' : MeasurableSet Ω') (hT : affMap A b ⁻¹' Ω' = Ω)
include hA hΩ' hT

theorem memLp_comp_affMap (f : L2 ℝ Ω') :
    MemLp (fun x => (f : (Fin n → ℝ) → ℝ) (affMap A b x)) 2 (volume.restrict Ω) := by
  subst hT
  have h1 := (Lp.memLp f).comp_measurePreserving (measurePreserving_affMap_restrict b hA hΩ')
  have h2 := h1.smul_measure (c := (ENNReal.ofReal |A.det|)⁻¹)
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (abs_det_pos hA)).ne')
  rwa [smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 (abs_det_pos hA)).ne'
    ENNReal.ofReal_ne_top, one_smul] at h2

omit hΩ' in
theorem ae_comp_affMap (hΩ' : MeasurableSet Ω') {p : (Fin n → ℝ) → Prop}
    (h : ∀ᵐ y ∂volume.restrict Ω', p y) : ∀ᵐ x ∂volume.restrict Ω, p (affMap A b x) := by
  subst hT
  have := (measurePreserving_affMap_restrict b hA hΩ').quasiMeasurePreserving.ae h
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.2 (abs_det_pos hA)).ne').1 this

/-- The pullback `f ↦ f ∘ T` as a linear map `L²(Ω') → L²(Ω)`, `Ω = T⁻¹ Ω'`. -/
def affPullₗ : L2 ℝ Ω' →ₗ[ℝ] L2 ℝ Ω where
  toFun f := (memLp_comp_affMap hA b hΩ' hT f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_comp_affMap hA b hΩ' hT (f + g)).coeFn_toLp,
      (memLp_comp_affMap hA b hΩ' hT f).coeFn_toLp, (memLp_comp_affMap hA b hΩ' hT g).coeFn_toLp,
      Lp.coeFn_add ((memLp_comp_affMap hA b hΩ' hT f).toLp _)
        ((memLp_comp_affMap hA b hΩ' hT g).toLp _),
      ae_comp_affMap hA b hT hΩ' (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
    rw [h4, Pi.add_apply, h1, h2, h3, h5, Pi.add_apply]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_comp_affMap hA b hΩ' hT (c • f)).coeFn_toLp,
      (memLp_comp_affMap hA b hΩ' hT f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_comp_affMap hA b hΩ' hT f).toLp _),
      ae_comp_affMap hA b hT hΩ' (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
    rw [RingHom.id_apply, h3, Pi.smul_apply, h1, h2, h4, Pi.smul_apply]

theorem coeFn_affPullₗ (f : L2 ℝ Ω') :
    (affPullₗ hA b hΩ' hT f : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω]
      fun x => (f : (Fin n → ℝ) → ℝ) (affMap A b x) :=
  (memLp_comp_affMap hA b hΩ' hT f).coeFn_toLp

/-- **Change of variables**: `∫_Ω g(T x) dx = |det A|⁻¹ ∫_{Ω'} g(y) dy` for `Ω = T⁻¹ Ω'`. -/
theorem setIntegral_comp_affMap (g : (Fin n → ℝ) → ℝ) :
    ∫ x in Ω, g (affMap A b x) = |A.det|⁻¹ * ∫ y in Ω', g y := by
  subst hT
  have hmp := measurePreserving_affMap_restrict b hA hΩ'
  have e2 := hmp.integral_comp' (f := affMeasEquiv b hA) g
  rw [integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at e2
  rw [← e2, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (abs_det_pos hA).ne', one_mul]
  rfl

/-- **The pullback scales inner products by `|det A|⁻¹`.** -/
theorem inner_affPullₗ (f g : L2 ℝ Ω') :
    ⟪affPullₗ hA b hΩ' hT f, affPullₗ hA b hΩ' hT g⟫_ℝ = |A.det|⁻¹ * ⟪f, g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  have e1 : ∫ x, ⟪(affPullₗ hA b hΩ' hT f : (Fin n → ℝ) → ℝ) x,
      (affPullₗ hA b hΩ' hT g : (Fin n → ℝ) → ℝ) x⟫_ℝ ∂volume.restrict Ω =
      ∫ x in Ω, (fun y => ⟪(f : (Fin n → ℝ) → ℝ) y, (g : (Fin n → ℝ) → ℝ) y⟫_ℝ)
        (affMap A b x) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_affPullₗ hA b hΩ' hT f, coeFn_affPullₗ hA b hΩ' hT g] with x h1 h2
    rw [h1, h2]
  rw [e1]
  exact setIntegral_comp_affMap hA b hΩ' hT
    (fun y => ⟪(f : (Fin n → ℝ) → ℝ) y, (g : (Fin n → ℝ) → ℝ) y⟫_ℝ)

theorem norm_affPullₗ (f : L2 ℝ Ω') :
    ‖affPullₗ hA b hΩ' hT f‖ = Real.sqrt |A.det|⁻¹ * ‖f‖ := by
  have h := inner_affPullₗ hA b hΩ' hT f f
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [← Real.sqrt_sq (norm_nonneg (affPullₗ hA b hΩ' hT f)), h,
    Real.sqrt_mul (inv_nonneg.2 (abs_nonneg _)), Real.sqrt_sq (norm_nonneg f)]

/-- The pullback `f ↦ f ∘ T` as a continuous linear map `L²(Ω') → L²(Ω)`. -/
def affPull : L2 ℝ Ω' →L[ℝ] L2 ℝ Ω :=
  (affPullₗ hA b hΩ' hT).mkContinuous (Real.sqrt |A.det|⁻¹) fun f =>
    (norm_affPullₗ hA b hΩ' hT f).le

theorem coeFn_affPull (f : L2 ℝ Ω') :
    (affPull hA b hΩ' hT f : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω]
      fun x => (f : (Fin n → ℝ) → ℝ) (affMap A b x) :=
  coeFn_affPullₗ hA b hΩ' hT f

theorem norm_affPull (f : L2 ℝ Ω') : ‖affPull hA b hΩ' hT f‖ = Real.sqrt |A.det|⁻¹ * ‖f‖ :=
  norm_affPullₗ hA b hΩ' hT f

/-- **Change of variables in pairings**: `∫_Ω (f ∘ T) (h ∘ T) = |det A|⁻¹ ∫_{Ω'} f h`. -/
theorem setIntegral_affPull_mul (f : L2 ℝ Ω') (h : (Fin n → ℝ) → ℝ) :
    ∫ x in Ω, (affPull hA b hΩ' hT f : (Fin n → ℝ) → ℝ) x * h (affMap A b x) =
      |A.det|⁻¹ * ∫ y in Ω', (f : (Fin n → ℝ) → ℝ) y * h y := by
  have e1 : ∫ x in Ω, (affPull hA b hΩ' hT f : (Fin n → ℝ) → ℝ) x * h (affMap A b x) =
      ∫ x in Ω, (fun y => (f : (Fin n → ℝ) → ℝ) y * h y) (affMap A b x) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_affPull hA b hΩ' hT f] with x h1
    rw [h1]
  rw [e1]
  exact setIntegral_comp_affMap hA b hΩ' hT (fun y => (f : (Fin n → ℝ) → ℝ) y * h y)

end Pull

theorem measurableSet_of_affMap {A : Matrix (Fin n) (Fin n) ℝ} (b : Fin n → ℝ)
    {Ω Ω' : Set (Fin n → ℝ)} (hΩ' : MeasurableSet Ω') (hT : affMap A b ⁻¹' Ω' = Ω) :
    MeasurableSet Ω := hT ▸ (continuous_affMap A b).measurable hΩ'

theorem preimage_inv_of_affMap {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det)
    (b : Fin n → ℝ) {Ω Ω' : Set (Fin n → ℝ)} (hT : affMap A b ⁻¹' Ω' = Ω) :
    affMap A⁻¹ (affInvShift A b) ⁻¹' Ω = Ω' := hT ▸ preimage_inv_preimage b hA Ω'

/-- Pulling back along `T` and then along `T⁻¹` is the identity. -/
theorem affPull_affPull_inv {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) (b : Fin n → ℝ)
    {Ω Ω' : Set (Fin n → ℝ)} (hΩ' : MeasurableSet Ω') (hT : affMap A b ⁻¹' Ω' = Ω)
    (f : L2 ℝ Ω) :
    affPull hA b hΩ' hT (affPull (isUnit_det_inv hA) (affInvShift A b) (measurableSet_of_affMap b hΩ' hT)
      (preimage_inv_of_affMap hA b hT) f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_affPull hA b hΩ' hT _,
    ae_comp_affMap hA b hT hΩ' (coeFn_affPull (isUnit_det_inv hA) (affInvShift A b)
      (measurableSet_of_affMap b hΩ' hT) (preimage_inv_of_affMap hA b hT) f)] with x h1 h2
  rw [h1, h2, affMap_inv_affMap b hA]

/-- Pulling back along `T⁻¹` and then along `T` is the identity. -/
theorem affPull_inv_affPull {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) (b : Fin n → ℝ)
    {Ω Ω' : Set (Fin n → ℝ)} (hΩ' : MeasurableSet Ω') (hT : affMap A b ⁻¹' Ω' = Ω)
    (f : L2 ℝ Ω') :
    affPull (isUnit_det_inv hA) (affInvShift A b) (measurableSet_of_affMap b hΩ' hT)
      (preimage_inv_of_affMap hA b hT) (affPull hA b hΩ' hT f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_affPull (isUnit_det_inv hA) (affInvShift A b)
      (measurableSet_of_affMap b hΩ' hT) (preimage_inv_of_affMap hA b hT) _,
    ae_comp_affMap (isUnit_det_inv hA) (affInvShift A b) (preimage_inv_of_affMap hA b hT)
      (measurableSet_of_affMap b hΩ' hT) (coeFn_affPull hA b hΩ' hT f)] with y h1 h2
  rw [h1, h2, affMap_affMap_inv b hA]

/-! ### Field pullbacks with constant fibre matrices -/

section FieldPull

variable {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) (b : Fin n → ℝ)
  {Ω Ω' : Set (Fin n → ℝ)} (hΩ' : MeasurableSet Ω') (hT : affMap A b ⁻¹' Ω' = Ω)
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The field pullback** `(T^* u)_s = Σ_t C_{st} u_t ∘ T`, `L²(Ω'; ℝ^ι) → L²(Ω; ℝ^κ)`, for a
constant fibre matrix `C`. For `k`-forms with `C` the matrix of `k × k` minors of `A` it is the
pullback of forms (`Feec.FiniteElement.affinePullback` pointwise). -/
def fieldPull (C : κ → ι → ℝ) : L2F ℝ Ω' ι →L[ℝ] L2F ℝ Ω κ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => L2 ℝ Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun s => ∑ t, C s t • (affPull hA b hΩ' hT).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => L2 ℝ Ω') t))

omit [Fintype κ] in
theorem fieldPull_apply (C : κ → ι → ℝ) (u : L2F ℝ Ω' ι) (s : κ) :
    fieldPull hA b hΩ' hT C u s = ∑ t, C s t • affPull hA b hΩ' hT (u t) := by
  simp [fieldPull]

omit [Fintype κ] in
/-- The components of `T^* u` are `Σ_t C_{st} u_t ∘ T` almost everywhere. -/
theorem coeFn_fieldPull (C : κ → ι → ℝ) (u : L2F ℝ Ω' ι) (s : κ) :
    (fieldPull hA b hΩ' hT C u s : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω]
      fun x => ∑ t, C s t * (u t : (Fin n → ℝ) → ℝ) (affMap A b x) := by
  rw [fieldPull_apply]
  have hs : ∀ t, ((C s t • affPull hA b hΩ' hT (u t) : L2 ℝ Ω) : (Fin n → ℝ) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => C s t * (u t : (Fin n → ℝ) → ℝ) (affMap A b x) := fun t => by
    filter_upwards [Lp.coeFn_smul (C s t) (affPull hA b hΩ' hT (u t)),
      coeFn_affPull hA b hΩ' hT (u t)] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ fun t => C s t • affPull hA b hΩ' hT (u t),
    ae_all_iff.2 hs] with x h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun t _ => h2 t

omit [Fintype κ] in
/-- `‖v‖ ≤ Σᵢ ‖vᵢ‖` in `L²(Ω; ℝ^κ)`. -/
theorem L2F.norm_le_sum_norm' [Fintype κ] (v : L2F ℝ Ω κ) : ‖v‖ ≤ ∑ s, ‖v s‖ := by
  rw [PiLp.norm_eq_of_L2]
  calc √(∑ s, ‖v s‖ ^ 2) ≤ √((∑ s, ‖v s‖) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _)
    _ = ∑ s, ‖v s‖ := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- **The field pullback is bounded**: `‖T^* u‖ ≤ |det A|^{-1/2} (Σ_{s,t} |C_{st}|) ‖u‖`. -/
theorem norm_fieldPull_le (C : κ → ι → ℝ) (u : L2F ℝ Ω' ι) :
    ‖fieldPull hA b hΩ' hT C u‖ ≤
      (Real.sqrt |A.det|⁻¹ * ∑ s, ∑ t, |C s t|) * ‖u‖ := by
  have h0 : 0 ≤ Real.sqrt |A.det|⁻¹ := Real.sqrt_nonneg _
  have hs : ∀ s, ‖fieldPull hA b hΩ' hT C u s‖ ≤
      ∑ t, |C s t| * (Real.sqrt |A.det|⁻¹ * ‖u‖) := fun s => by
    rw [fieldPull_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [norm_smul, norm_affPull, Real.norm_eq_abs]
    have := PiLp.norm_apply_le u t
    gcongr
  refine (L2F.norm_le_sum_norm' _).trans ((Finset.sum_le_sum fun s _ => hs s).trans_eq ?_)
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  ring

/-- The inverse pullback, along `T⁻¹ y = A⁻¹ y - A⁻¹ b`, from `L²(Ω)` to `L²(Ω')`. -/
abbrev fieldPullInv (C' : ι → κ → ℝ) : L2F ℝ Ω κ →L[ℝ] L2F ℝ Ω' ι :=
  fieldPull (isUnit_det_inv hA) (affInvShift A b) (measurableSet_of_affMap b hΩ' hT)
    (preimage_inv_of_affMap hA b hT) C'

theorem fieldPullInv_fieldPull [DecidableEq ι] {C : κ → ι → ℝ} {C' : ι → κ → ℝ}
    (h : ∀ s r, ∑ t, C' s t * C t r = if s = r then 1 else 0) (u : L2F ℝ Ω' ι) :
    fieldPullInv hA b hΩ' hT C' (fieldPull hA b hΩ' hT C u) = u := by
  refine (WithLp.ext_iff 2).2 (funext fun s => ?_)
  change fieldPull _ _ _ _ C' (fieldPull hA b hΩ' hT C u) s = u s
  simp only [fieldPull_apply, map_sum, map_smul, Finset.smul_sum, smul_smul,
    affPull_inv_affPull hA b hΩ' hT]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem fieldPull_fieldPullInv [DecidableEq ι] {C : ι → κ → ℝ} {C' : κ → ι → ℝ}
    (h : ∀ s r, ∑ t, C s t * C' t r = if s = r then 1 else 0) (u : L2F ℝ Ω ι) :
    fieldPull hA b hΩ' hT C (fieldPullInv hA b hΩ' hT C' u) = u := by
  refine (WithLp.ext_iff 2).2 (funext fun s => ?_)
  change fieldPull hA b hΩ' hT C (fieldPull _ _ _ _ C' u) s = u s
  simp only [fieldPull_apply, map_sum, map_smul, Finset.smul_sum, smul_smul,
    affPull_affPull_inv hA b hΩ' hT]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- **The field pullback as an isomorphism** `L²(Ω'; ℝ^ι) ≃ L²(Ω; ℝ^ι)`, for mutually inverse
fibre matrices `C`, `C'`; the inverse is the field pullback along `T⁻¹` with `C'`. -/
def fieldPullEquiv [DecidableEq ι] (C C' : ι → ι → ℝ) (h₁ : ∀ s r, ∑ t, C s t * C' t r = if s = r then 1 else 0)
    (h₂ : ∀ s r, ∑ t, C' s t * C t r = if s = r then 1 else 0) :
    L2F ℝ Ω' ι ≃L[ℝ] L2F ℝ Ω ι :=
  ContinuousLinearEquiv.equivOfInverse (fieldPull hA b hΩ' hT C) (fieldPullInv hA b hΩ' hT C')
    (fieldPullInv_fieldPull hA b hΩ' hT h₂) (fieldPull_fieldPullInv hA b hΩ' hT h₁)

@[simp] theorem coe_fieldPullEquiv [DecidableEq ι] (C C' : ι → ι → ℝ) (h₁ h₂) :
    ⇑(fieldPullEquiv hA b hΩ' hT C C' h₁ h₂) = fieldPull hA b hΩ' hT C := rfl

@[simp] theorem coe_fieldPullEquiv_symm [DecidableEq ι] (C C' : ι → ι → ℝ) (h₁ h₂) :
    ⇑(fieldPullEquiv hA b hΩ' hT C C' h₁ h₂).symm = fieldPullInv hA b hΩ' hT C' := rfl

end FieldPull

/-! ### Test fields -/

section Test

variable {A : Matrix (Fin n) (Fin n) ℝ} (b : Fin n → ℝ) {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The pointwise pullback `(T^* φ)_s (x) = Σ_t C_{st} φ_t (A x + b)` of a field. -/
def pullFun (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (C : κ → ι → ℝ)
    (φ : ι → (Fin n → ℝ) → ℝ) : κ → (Fin n → ℝ) → ℝ :=
  fun s x => ∑ t, C s t * φ t (affMap A b x)

/-- The pointwise pushforward `(T^♯ ψ)_t (y) = |det A|⁻¹ Σ_s C_{st} ψ_s (T⁻¹ y)`, the adjoint of
the pullback (`inner_fieldPull_testField`). -/
def pushFun (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (C : κ → ι → ℝ)
    (ψ : κ → (Fin n → ℝ) → ℝ) : ι → (Fin n → ℝ) → ℝ :=
  fun t y => |A.det|⁻¹ * ∑ s, C s t * ψ s (affMap A⁻¹ (affInvShift A b) y)

theorem _root_.Feec.Domain.IsTest.comp_affMap (hA : IsUnit A.det) {Ω' : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hf : IsTest Ω' f) :
    IsTest (affMap A b ⁻¹' Ω') (fun x => f (affMap A b x)) where
  contDiff := hf.contDiff.comp (contDiff_affMap A b)
  hasCompactSupport := hf.hasCompactSupport.comp_homeomorph (affHomeo b hA)
  tsupport_subset := by
    have e : tsupport (fun x => f (affMap A b x)) = affHomeo b hA ⁻¹' tsupport f := by
      rw [tsupport, tsupport, Homeomorph.preimage_closure]
      rfl
    rw [e]
    exact preimage_mono hf.tsupport_subset

omit [Fintype κ] in
theorem _root_.Feec.Domain.IsTestField.pullFun (hA : IsUnit A.det) {Ω Ω' : Set (Fin n → ℝ)}
    (hT : affMap A b ⁻¹' Ω' = Ω) (C : κ → ι → ℝ) {φ : ι → (Fin n → ℝ) → ℝ}
    (hφ : IsTestField Ω' φ) : IsTestField Ω (pullFun A b C φ) := fun s =>
  hT ▸ IsTest.sum _ fun t _ => ((hφ t).comp_affMap b hA).const_mul (C s t)

omit [Fintype ι] in
theorem _root_.Feec.Domain.IsTestField.pushFun (hA : IsUnit A.det) {Ω Ω' : Set (Fin n → ℝ)}
    (hT : affMap A b ⁻¹' Ω' = Ω) (C : κ → ι → ℝ) {ψ : κ → (Fin n → ℝ) → ℝ}
    (hψ : IsTestField Ω ψ) : IsTestField Ω' (pushFun A b C ψ) := fun t => by
  have h := IsTest.sum (Ω := Ω') Finset.univ fun s _ =>
    (((preimage_inv_of_affMap hA b hT) ▸ (hψ s).comp_affMap (affInvShift A b)
      (isUnit_det_inv hA)) : IsTest Ω' _).const_mul (C s t)
  exact h.const_mul _

variable (hA : IsUnit A.det) {Ω Ω' : Set (Fin n → ℝ)} (hΩ' : MeasurableSet Ω')
  (hT : affMap A b ⁻¹' Ω' = Ω)

omit [Fintype κ] in
/-- **The pullback of a test field is the test field of the pointwise pullback.** -/
theorem fieldPull_testField (C : κ → ι → ℝ) {φ : ι → (Fin n → ℝ) → ℝ}
    (hφ : IsTestField Ω' φ) :
    fieldPull hA b hΩ' hT C (testField hφ) = testField (hφ.pullFun b hA hT C) := by
  refine eq_testField _ fun s => ?_
  rw [fieldPull_apply]
  have hs : ∀ t, ((C s t • affPull hA b hΩ' hT (testField hφ t) : L2 ℝ Ω) : (Fin n → ℝ) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => C s t * φ t (affMap A b x) := fun t => by
    filter_upwards [Lp.coeFn_smul (C s t) (affPull hA b hΩ' hT (testField hφ t)),
      coeFn_affPull hA b hΩ' hT (testField hφ t),
      ae_comp_affMap hA b hT hΩ' (coeFn_testField hφ t)] with x h1 h2 h3
    rw [h1, Pi.smul_apply, h2, h3, smul_eq_mul]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ fun t => C s t • affPull hA b hΩ' hT
    (testField hφ t), ae_all_iff.2 hs] with x h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun t _ => h2 t

/-- **The adjoint of the pullback on test fields is the pushforward**:
`⟪T^* u, ψ⟫_{L²(Ω)} = ⟪u, T^♯ ψ⟫_{L²(Ω')}` for every test field `ψ` on `Ω` (change of variables). -/
theorem inner_fieldPull_testField (C : κ → ι → ℝ) (u : L2F ℝ Ω' ι)
    {ψ : κ → (Fin n → ℝ) → ℝ} (hψ : IsTestField Ω ψ) :
    ⟪fieldPull hA b hΩ' hT C u, testField hψ⟫_ℝ =
      ⟪u, testField (hψ.pushFun b hA hT C)⟫_ℝ := by
  set c := affInvShift A b
  have hψ' : ∀ s, IsTest Ω' fun y => ψ s (affMap A⁻¹ c y) := fun s =>
    (preimage_inv_of_affMap hA b hT) ▸ (hψ s).comp_affMap c (isUnit_det_inv hA)
  -- each term: `⟪u_t ∘ T, ψ_s⟫ = |det A|⁻¹ ∫_{Ω'} u_t (ψ_s ∘ T⁻¹)`
  have key : ∀ t s, ⟪affPull hA b hΩ' hT (u t), toL2 (hψ s)⟫_ℝ =
      |A.det|⁻¹ * ∫ y in Ω', (u t : (Fin n → ℝ) → ℝ) y * ψ s (affMap A⁻¹ c y) := by
    intro t s
    rw [inner_toL2]
    simp only [conj_trivial]
    have e : ∫ x in Ω, (affPull hA b hΩ' hT (u t) : (Fin n → ℝ) → ℝ) x * ψ s x =
        ∫ x in Ω, (affPull hA b hΩ' hT (u t) : (Fin n → ℝ) → ℝ) x *
          (fun y => ψ s (affMap A⁻¹ c y)) (affMap A b x) := by
      simp only [c, affMap_inv_affMap b hA]
    rw [e]
    exact setIntegral_affPull_mul hA b hΩ' hT (u t) (fun y => ψ s (affMap A⁻¹ c y))
  rw [L2F.inner_def, L2F.inner_def]
  simp only [testField_apply, fieldPull_apply, sum_inner, real_inner_smul_left, key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [inner_toL2]
  simp only [conj_trivial, pushFun]
  have hint : ∀ s, Integrable (fun y => (u t : (Fin n → ℝ) → ℝ) y * ψ s (affMap A⁻¹ c y))
      (volume.restrict Ω') := fun s => by
    simpa using integrable_conj_mul (u t) (hψ' s).memLp
  have e2 : (fun y => (u t : (Fin n → ℝ) → ℝ) y * (|A.det|⁻¹ * ∑ s, C s t *
      ψ s (affMap A⁻¹ (affInvShift A b) y))) =
      fun y => ∑ s, (|A.det|⁻¹ * C s t) * ((u t : (Fin n → ℝ) → ℝ) y * ψ s (affMap A⁻¹ c y)) := by
    funext y
    simp only [Finset.mul_sum, c]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [e2, integral_finsetSum _ fun s _ => (hint s).const_mul _]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_const_mul]
  ring

end Test

/-! ### Intertwining constant-coefficient operators -/

section Intertwining

variable (A : Matrix (Fin n) (Fin n) ℝ) {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ]
  [Fintype ι'] [Fintype κ']

/-- **Classical intertwining** of constant-coefficient operators by fibre matrices: for every
translation `b` and every smooth field `φ`, `P (T^* φ) = T^* (P' φ)` pointwise, `T x = A x + b`,
with fibre matrix `C` on the fields and `C'` on the values (`pullFun`). `P'` acts on the target
of `T`, `P` on its source. -/
def IsPullIntertwining (P : ConstCoeffOp (Fin n → ℝ) ℝ ι κ)
    (P' : ConstCoeffOp (Fin n → ℝ) ℝ ι' κ') (C : ι → ι' → ℝ) (C' : κ → κ' → ℝ) : Prop :=
  ∀ (b : Fin n → ℝ) (φ : ι' → (Fin n → ℝ) → ℝ), (∀ t, ContDiff ℝ ∞ (φ t)) →
    P.apply (pullFun A b C φ) = pullFun A b C' (P'.apply φ)

/-- **Classical intertwining of `d`** by fibre matrices `C k` on `k`-forms: for every translation
`b` and every smooth `k`-form `φ`, `d (T^* φ) = T^* (d φ)` pointwise, `T x = A x + b`. For the
matrices of minors of `A` this is `Feec.FiniteElement.extDeriv_affinePullback_apply`. -/
def IsDIntertwining (C : ∀ k : ℤ, formIdx n k → formIdx n k → ℝ) : Prop :=
  ∀ (b : Fin n → ℝ) (k : ℤ) (φ : formIdx n k → (Fin n → ℝ) → ℝ), (∀ t, ContDiff ℝ ∞ (φ t)) →
    (extDerivOp ℝ n k).apply (pullFun A b (C k) φ) =
      pullFun A b (C (k + 1)) ((extDerivOp ℝ n k).apply φ)

variable {A}

/-- In each degree `k`, `IsDIntertwining A C` is the classical intertwining of `d` on `k`-forms
with the fibre matrices `C k` on the forms and `C (k + 1)` on the values. -/
theorem IsDIntertwining.isPullIntertwining {C : ∀ k : ℤ, formIdx n k → formIdx n k → ℝ}
    (hC : IsDIntertwining A C) (k : ℤ) :
    IsPullIntertwining A (extDerivOp ℝ n k) (extDerivOp ℝ n k) (C k) (C (k + 1)) :=
  fun b φ hφ => hC b k φ hφ

variable {P : ConstCoeffOp (Fin n → ℝ) ℝ ι κ} {P' : ConstCoeffOp (Fin n → ℝ) ℝ ι' κ'}
  {C : ι → ι' → ℝ} {C' : κ → κ' → ℝ} (hP : IsPullIntertwining A P P' C C')
  (hA : IsUnit A.det) (b : Fin n → ℝ) {Ω Ω' : Set (Fin n → ℝ)} (hΩo : IsOpen Ω)
  (hΩo' : IsOpen Ω') (hT : affMap A b ⁻¹' Ω' = Ω)
include hP

omit [Fintype κ] in
/-- The pullback maps the test graph of `P'` on `Ω'` into the test graph of `P` on `Ω`. -/
theorem fieldPull_mem_testGraph {p : L2F ℝ Ω' ι' × L2F ℝ Ω' κ'} (hp : p ∈ P'.testGraph Ω') :
    (fieldPull hA b hΩo'.measurableSet hT C p.1, fieldPull hA b hΩo'.measurableSet hT C' p.2) ∈
      P.testGraph Ω := by
  obtain ⟨φ, hφ, rfl⟩ := hp
  refine ⟨pullFun A b C φ, hφ.pullFun b hA hT C, ?_⟩
  simp only [fieldPull_testField]
  refine Prod.ext rfl (testField_congr _ _ ?_)
  exact (hP b φ fun t => (hφ t).contDiff).symm

include hΩo in
/-- **The pullback maps the graph of `P'_min` into the graph of `P_min`.** -/
theorem fieldPull_mem_graph_minimal {p : L2F ℝ Ω' ι' × L2F ℝ Ω' κ'}
    (hp : p ∈ (P'.minimal Ω').graph) :
    (fieldPull hA b hΩo'.measurableSet hT C p.1, fieldPull hA b hΩo'.measurableSet hT C' p.2) ∈
      (P.minimal Ω).graph := by
  rw [P'.minimal_graph hΩo'] at hp
  rw [P.minimal_graph hΩo]
  set L := (fieldPull hA b hΩo'.measurableSet hT C).prodMap
    (fieldPull hA b hΩo'.measurableSet hT C')
  have hsub : (P'.testGraph Ω' : Set _) ⊆ L ⁻¹' ((P.testGraph Ω).topologicalClosure : Set _) :=
    fun q hq => Submodule.le_topologicalClosure _ (fieldPull_mem_testGraph hP hA b hΩo' hT hq)
  have hcl : IsClosed (L ⁻¹' ((P.testGraph Ω).topologicalClosure : Set _)) :=
    (Submodule.isClosed_topologicalClosure _).preimage L.continuous
  have hp' : p ∈ closure (P'.testGraph Ω' : Set _) := by
    rw [← Submodule.topologicalClosure_coe]; exact hp
  exact closure_minimal hsub hcl hp'

include hΩo in
/-- **`T^*` maps `D(P'_min)` into `D(P_min)`.** -/
theorem fieldPull_mem_minimal_domain (u : (P'.minimal Ω').domain) :
    fieldPull hA b hΩo'.measurableSet hT C u ∈ (P.minimal Ω).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (fieldPull_mem_graph_minimal hP hA b hΩo hΩo' hT ((P'.minimal Ω').mem_graph u))

include hΩo in
/-- **`T^*` intertwines the minimal realizations**: `P_min (T^* u) = T^* (P'_min u)`. -/
theorem minimal_fieldPull (u : (P'.minimal Ω').domain) :
    P.minimal Ω ⟨_, fieldPull_mem_minimal_domain hP hA b hΩo hΩo' hT u⟩ =
      fieldPull hA b hΩo'.measurableSet hT C' (P'.minimal Ω' u) :=
  ((LinearPMap.image_iff _).2 (fieldPull_mem_graph_minimal hP hA b hΩo hΩo' hT
    ((P'.minimal Ω').mem_graph u))).symm

include hΩo' in
/-- **The pushforward intertwines the formal adjoints on test fields** (by duality from the
classical intertwining): `P'ᵗ (T^♯ ψ) = T^♯ (Pᵗ ψ)`. -/
theorem testField_push_formalAdj {ψ : κ → (Fin n → ℝ) → ℝ} (hψ : IsTestField Ω ψ) :
    testField (P'.formalAdj.isTestField_apply (hψ.pushFun b hA hT C')) =
      testField ((P.formalAdj.isTestField_apply hψ).pushFun b hA hT C) := by
  refine L2F.ext_of_forall_inner_testField hΩo' fun χ hχ => ?_
  suffices key : ⟪testField hχ, testField (P'.formalAdj.isTestField_apply
        (hψ.pushFun b hA hT C'))⟫_ℝ = ⟪testField hχ,
        testField ((P.formalAdj.isTestField_apply hψ).pushFun b hA hT C)⟫_ℝ by
    simpa only [real_inner_comm (testField hχ)] using key
  calc ⟪testField hχ, testField (P'.formalAdj.isTestField_apply
        (hψ.pushFun b hA hT C'))⟫_ℝ
      = ⟪testField (P'.isTestField_apply hχ), testField (hψ.pushFun b hA hT C')⟫_ℝ :=
        (P'.inner_testField_apply_testField hχ _).symm
    _ = ⟪fieldPull hA b hΩo'.measurableSet hT C' (testField (P'.isTestField_apply hχ)),
          testField hψ⟫_ℝ :=
        (inner_fieldPull_testField b hA hΩo'.measurableSet hT C' _ hψ).symm
    _ = ⟪testField (P.isTestField_apply (hχ.pullFun b hA hT C)), testField hψ⟫_ℝ := by
        rw [fieldPull_testField]
        congr 1
        exact testField_congr _ _ (hP b χ fun t => (hχ t).contDiff).symm
    _ = ⟪testField (hχ.pullFun b hA hT C),
          testField (P.formalAdj.isTestField_apply hψ)⟫_ℝ :=
        P.inner_testField_apply_testField _ hψ
    _ = ⟪fieldPull hA b hΩo'.measurableSet hT C (testField hχ),
          testField (P.formalAdj.isTestField_apply hψ)⟫_ℝ := by
        rw [fieldPull_testField]
    _ = _ := inner_fieldPull_testField b hA hΩo'.measurableSet hT C _ _

include hΩo in
/-- **`T^*` maps `D(P'_max)` into `D(P_max)` and intertwines the maximal realizations**:
`P_max (T^* u) = T^* (P'_max u)`. -/
theorem fieldPull_mem_maximal_domain (u : (P'.maximal Ω').domain) :
    ∃ h : fieldPull hA b hΩo'.measurableSet hT C u ∈ (P.maximal Ω).domain,
      P.maximal Ω ⟨_, h⟩ = fieldPull hA b hΩo'.measurableSet hT C' (P'.maximal Ω' u) := by
  have key : ∀ ψ : κ → (Fin n → ℝ) → ℝ, ∀ hψ : IsTestField Ω ψ,
      ⟪fieldPull hA b hΩo'.measurableSet hT C' (P'.maximal Ω' u), testField hψ⟫_ℝ =
        ⟪fieldPull hA b hΩo'.measurableSet hT C u,
          testField (P.formalAdj.isTestField_apply hψ)⟫_ℝ := by
    intro ψ hψ
    rw [inner_fieldPull_testField, inner_fieldPull_testField,
      P'.maximal_inner_testField hΩo' u (hψ.pushFun b hA hT C'),
      testField_push_formalAdj hP hA b hΩo' hT hψ]
  have hmem := (P.mem_maximal_domain_iff hΩo).2 ⟨_, key⟩
  exact ⟨hmem, P.maximal_apply_eq hΩo ⟨_, hmem⟩ key⟩

end Intertwining

/-! ### The pullback of `k`-forms and the transport of the de Rham complexes -/

/-- **Fibre data of the pullback of forms along `x ↦ A x + b`**: in every degree `k` the fibre
matrix `C k` of `T^*` and the fibre matrix `Cinv k` of `(T⁻¹)^*`, inverse to each other, both
intertwining `d` classically. For the matrices of `k × k` minors of `A` and of `A⁻¹` this is
built in `Feec.Models.Parallelepiped.FiniteElement`. -/
structure FormPullData (A : Matrix (Fin n) (Fin n) ℝ) where
  /-- the fibre matrices of `T^*` -/
  C : ∀ k : ℤ, formIdx n k → formIdx n k → ℝ
  /-- the fibre matrices of `(T⁻¹)^*` -/
  Cinv : ∀ k : ℤ, formIdx n k → formIdx n k → ℝ
  isDIntertwining : IsDIntertwining A C
  isDIntertwining_inv : IsDIntertwining A⁻¹ Cinv
  mul_inv : ∀ k s r, ∑ t, C k s t * Cinv k t r = if s = r then 1 else 0
  inv_mul : ∀ k s r, ∑ t, Cinv k s t * C k t r = if s = r then 1 else 0

namespace FormPullData

variable {A : Matrix (Fin n) (Fin n) ℝ} (D : FormPullData A) (hA : IsUnit A.det)
  (b : Fin n → ℝ) {Ω Ω' : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩo' : IsOpen Ω')
  (hT : affMap A b ⁻¹' Ω' = Ω)

/-- **The `L²` pullback of `k`-forms** `T^* : L²(Ω'; Λᵏ) ≃ L²(Ω; Λᵏ)`, `Ω = T⁻¹ Ω'`. -/
def equiv (k : ℤ) : L2F ℝ Ω' (formIdx n k) ≃L[ℝ] L2F ℝ Ω (formIdx n k) :=
  fieldPullEquiv hA b hΩo'.measurableSet hT (D.C k) (D.Cinv k) (D.mul_inv k) (D.inv_mul k)

@[simp] theorem coe_equiv (k : ℤ) :
    ⇑(D.equiv hA b hΩo' hT k) = fieldPull hA b hΩo'.measurableSet hT (D.C k) := rfl

@[simp] theorem coe_equiv_symm (k : ℤ) :
    ⇑(D.equiv hA b hΩo' hT k).symm = fieldPullInv hA b hΩo'.measurableSet hT (D.Cinv k) := rfl

/-- `‖T^* u‖ ≤ |det A|^{-1/2} (Σ_{s,t} |C_{st}|) ‖u‖`. -/
theorem norm_equiv_le (k : ℤ) (u : L2F ℝ Ω' (formIdx n k)) :
    ‖D.equiv hA b hΩo' hT k u‖ ≤
      (Real.sqrt |A.det|⁻¹ * ∑ s, ∑ t, |D.C k s t|) * ‖u‖ :=
  norm_fieldPull_le hA b _ hT _ u

/-- `‖(T^*)⁻¹ v‖ ≤ |det A|^{1/2} (Σ_{s,t} |Cinv_{st}|) ‖v‖`. -/
theorem norm_equiv_symm_le (k : ℤ) (v : L2F ℝ Ω (formIdx n k)) :
    ‖(D.equiv hA b hΩo' hT k).symm v‖ ≤
      (Real.sqrt |(A⁻¹).det|⁻¹ * ∑ s, ∑ t, |D.Cinv k s t|) * ‖v‖ :=
  norm_fieldPull_le (isUnit_det_inv hA) _ _ _ _ v

include hΩo in
/-- **`T^*` maps `HΛᵏ(Ω')` onto `HΛᵏ(Ω)`**: `u ∈ D(d_max)` iff `T^* u ∈ D(d_max)`. -/
theorem mem_maximal_domain_iff (k : ℤ) {u : L2F ℝ Ω' (formIdx n k)} :
    D.equiv hA b hΩo' hT k u ∈ ((extDerivOp ℝ n k).maximal Ω).domain ↔
      u ∈ ((extDerivOp ℝ n k).maximal Ω').domain := by
  constructor
  · intro h
    obtain ⟨h', -⟩ := fieldPull_mem_maximal_domain (D.isDIntertwining_inv.isPullIntertwining k)
      (isUnit_det_inv hA) (affInvShift A b) hΩo' hΩo (preimage_inv_of_affMap hA b hT) ⟨_, h⟩
    have e : fieldPull (isUnit_det_inv hA) (affInvShift A b) hΩo.measurableSet
        (preimage_inv_of_affMap hA b hT) (D.Cinv k) (D.equiv hA b hΩo' hT k u) = u :=
      (D.equiv hA b hΩo' hT k).symm_apply_apply u
    exact e ▸ h'
  · intro h
    exact (fieldPull_mem_maximal_domain (D.isDIntertwining.isPullIntertwining k) hA b hΩo hΩo' hT
      ⟨u, h⟩).1

include hΩo in
/-- **`T^*` maps `H̊Λᵏ(Ω')` onto `H̊Λᵏ(Ω)`**. -/
theorem mem_minimal_domain_iff (k : ℤ) {u : L2F ℝ Ω' (formIdx n k)} :
    D.equiv hA b hΩo' hT k u ∈ ((extDerivOp ℝ n k).minimal Ω).domain ↔
      u ∈ ((extDerivOp ℝ n k).minimal Ω').domain := by
  constructor
  · intro h
    have h' := fieldPull_mem_minimal_domain (D.isDIntertwining_inv.isPullIntertwining k)
      (isUnit_det_inv hA) (affInvShift A b) hΩo' hΩo (preimage_inv_of_affMap hA b hT) ⟨_, h⟩
    have e : fieldPull (isUnit_det_inv hA) (affInvShift A b) hΩo.measurableSet
        (preimage_inv_of_affMap hA b hT) (D.Cinv k) (D.equiv hA b hΩo' hT k u) = u :=
      (D.equiv hA b hΩo' hT k).symm_apply_apply u
    exact e ▸ h'
  · intro h
    exact fieldPull_mem_minimal_domain (D.isDIntertwining.isPullIntertwining k) hA b hΩo hΩo' hT
      ⟨u, h⟩

end FormPullData

/-- A partial map whose domain and values are the conjugates of those of `H.d i j` by `e` is the
transported differential. -/
theorem eq_transportD_of_conj {ι : Type*} {c : ComplexShape ι} {W W' : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
    [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace ℝ (W' i)]
    (H : HilbertComplex ℝ c W) (e : ∀ i, W i ≃L[ℝ] W' i) {i j : ι} (T : W' i →ₗ.[ℝ] W' j)
    (hdom : ∀ y, y ∈ T.domain ↔ (e i).symm y ∈ (H.d i j).domain)
    (hval : ∀ (x : (H.d i j).domain) (h : e i x ∈ T.domain), T ⟨e i x, h⟩ = e j (H.d i j x)) :
    T = HilbertComplex.transportD H e (fun _ _ => 1) i j := by
  refine LinearPMap.ext (Submodule.ext fun y => (hdom y).trans Iff.rfl) fun y hy hy' => ?_
  rw [HilbertComplex.transportD_apply, one_smul]
  have hx : (e i).symm y ∈ (H.d i j).domain := (hdom y).1 hy
  have e1 := hval ⟨_, hx⟩ (by simpa using hy)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at e1
  exact e1

namespace FormPullData

variable {A : Matrix (Fin n) (Fin n) ℝ} (D : FormPullData A) (hA : IsUnit A.det)
  (b : Fin n → ℝ) {Ω Ω' : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩo' : IsOpen Ω')
  (hT : affMap A b ⁻¹' Ω' = Ω)

/-- **`HΛ(Ω)` is the transport of `HΛ(Ω')` along the pullback `T^*`**: `d_Ω = T^* d_{Ω'} (T^*)⁻¹`
in every degree, with `D(d_Ω) = T^* D(d_{Ω'})`. -/
theorem maximalComplex_eq_transport :
    (deRham ℝ n).maximalComplex hΩo = ((deRham ℝ n).maximalComplex hΩo').transport
      (fun k => D.equiv hA b hΩo' hT k) (fun _ _ => 1) (fun _ _ => one_ne_zero) := by
  refine HilbertComplex.ext_d (funext fun i => funext fun j => ?_)
  by_cases hij : i + 1 = j
  · subst hij
    refine eq_transportD_of_conj ((deRham ℝ n).maximalComplex hΩo')
      (fun k => D.equiv hA b hΩo' hT k) _ (fun y => ?_) fun x h => ?_
    · rw [deRham_maximalComplex_d, deRham_maximalComplex_d]
      conv_lhs => rw [← (D.equiv hA b hΩo' hT i).apply_symm_apply y]
      exact D.mem_maximal_domain_iff hA b hΩo hΩo' hT i
    · have hx : x.1 ∈ ((extDerivOp ℝ n i).maximal Ω').domain := by
        rw [← deRham_maximalComplex_d (𝕜 := ℝ) hΩo' i]; exact x.2
      obtain ⟨h', hv⟩ := fieldPull_mem_maximal_domain
        (D.isDIntertwining.isPullIntertwining i) hA b hΩo hΩo' hT ⟨_, hx⟩
      refine ((LinearPMap.apply_eq_of_eq (deRham_maximalComplex_d hΩo i) _ ⟨_, h'⟩ rfl).trans
        hv).trans ?_
      exact congrArg _ (LinearPMap.apply_eq_of_eq (deRham_maximalComplex_d hΩo' i) x
        ⟨_, hx⟩ rfl).symm
  · have hr : ¬ (ComplexShape.up ℤ).Rel i j := by simpa using hij
    exact (((deRham ℝ n).maximalComplex hΩo).shape i j hr).trans
      ((((deRham ℝ n).maximalComplex hΩo').transport (fun k => D.equiv hA b hΩo' hT k)
        (fun _ _ => 1) (fun _ _ => one_ne_zero)).shape i j hr).symm

/-- **`H̊Λ(Ω)` is the transport of `H̊Λ(Ω')` along the pullback `T^*`.** -/
theorem minimalComplex_eq_transport :
    (deRham ℝ n).minimalComplex hΩo = ((deRham ℝ n).minimalComplex hΩo').transport
      (fun k => D.equiv hA b hΩo' hT k) (fun _ _ => 1) (fun _ _ => one_ne_zero) := by
  refine HilbertComplex.ext_d (funext fun i => funext fun j => ?_)
  by_cases hij : i + 1 = j
  · subst hij
    refine eq_transportD_of_conj ((deRham ℝ n).minimalComplex hΩo')
      (fun k => D.equiv hA b hΩo' hT k) _ (fun y => ?_) fun x h => ?_
    · rw [deRham_minimalComplex_d, deRham_minimalComplex_d]
      conv_lhs => rw [← (D.equiv hA b hΩo' hT i).apply_symm_apply y]
      exact D.mem_minimal_domain_iff hA b hΩo hΩo' hT i
    · have hx : x.1 ∈ ((extDerivOp ℝ n i).minimal Ω').domain := by
        rw [← deRham_minimalComplex_d (𝕜 := ℝ) hΩo' i]; exact x.2
      have h' := fieldPull_mem_minimal_domain (D.isDIntertwining.isPullIntertwining i) hA b hΩo
        hΩo' hT ⟨_, hx⟩
      refine ((LinearPMap.apply_eq_of_eq (deRham_minimalComplex_d hΩo i) _ ⟨_, h'⟩ rfl).trans
        (minimal_fieldPull (D.isDIntertwining.isPullIntertwining i) hA b hΩo hΩo' hT
          ⟨_, hx⟩)).trans ?_
      exact congrArg _ (LinearPMap.apply_eq_of_eq (deRham_minimalComplex_d hΩo' i) x
        ⟨_, hx⟩ rfl).symm
  · have hr : ¬ (ComplexShape.up ℤ).Rel i j := by simpa using hij
    exact (((deRham ℝ n).minimalComplex hΩo).shape i j hr).trans
      ((((deRham ℝ n).minimalComplex hΩo').transport (fun k => D.equiv hA b hΩo' hT k)
        (fun _ _ => 1) (fun _ _ => one_ne_zero)).shape i j hr).symm

end FormPullData

end Feec.Domain
