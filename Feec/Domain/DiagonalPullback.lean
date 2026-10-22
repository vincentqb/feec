module

public import Feec.Domain.Affine
public import Feec.Domain.Complexes
public import Feec.Domain.Operators

/-!
# Diagonal changes of variables

`Feec.Domain.Affine` treats the dilations `T x = a • x + b` of `E`: they rescale every direction
by the same factor, so a homogeneous constant-coefficient operator `A` of order `r` satisfies
`A (f ∘ T) = a^r (A f) ∘ T`. This file treats the **diagonal** affine maps of `ℝⁿ`,
`T x = d * x + b` (pointwise product, `dᵢ ≠ 0`), which map boxes with unequal sides onto each
other. Now each variable is rescaled by its own factor and the operator changes:
`A (f ∘ T) = (A_d f) ∘ T`, where `A_d = diagScale d A` is the operator with every direction `v`
replaced by `d * v` (`∂ᵢ ↦ dᵢ ∂ᵢ`; `apply_comp_diagAff`). No homogeneity is needed.

The pull-back `f ↦ f ∘ T` is a scaled unitary `L²(Ω'; 𝕜^ι) ≃ L²(Ω; 𝕜^ι)`, `Ω = T⁻¹ Ω'`,
`⟪f ∘ T, g ∘ T⟫ = |∏ dᵢ|⁻¹ ⟪f, g⟫` (`pullDiagF`, `inner_pullDiagF`), and it carries the
realizations of `A_d` on `Ω'` to those of `A` on `Ω`:

* `ConstCoeffOp.minimal_pullDiag`: `A_min,Ω = P (A_d)_min,Ω' P⁻¹` (test graphs correspond);
  `ConstCoeffComplex.diagScale` is again a complex.

A second, purely algebraic, tool: if a constant-coefficient operator `B` is a **conjugate of `A`
by constant diagonal fibre scalings**, `B (w • ψ) = w' • A ψ` on smooth fields, then
`B_min = (w' •) A_min (w •)⁻¹` (`ConstCoeffOp.minimal_eq_conj_scaleF`). For the row-wise
gradient and curl on `ℝ³` the rescaled operators are of this kind
(`gradOp_diagScale_apply`, `curlOp_diagScale_apply`): `grad_d σ = (grad σ) D` and
`curl_d (E D) = det D · (curl E) D⁻¹` for `D = diag d`, which is how the grad–curl complex of a
box is compared with the one of the cube in `Feec.Models.Box`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the cube complexes, here extended to boxes)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (change of variables in Sobolev spaces)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff ENNReal ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology Module

@[expose] public noncomputable section

namespace Feec.Domain

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### The diagonal affine map -/

/-- The diagonal linear map `v ↦ d * v` of `ℝⁿ`. -/
def diagCLM (d : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => d i • ContinuousLinearMap.proj i

@[simp] theorem diagCLM_apply (d v : Fin n → ℝ) : diagCLM d v = d * v := by
  funext i; simp [diagCLM]

/-- The diagonal affine map `x ↦ d * x + b`. -/
def diagAff (d b : Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ := d * x + b

theorem diagAff_apply (d b x : Fin n → ℝ) (i : Fin n) : diagAff d b x i = d i * x i + b i := rfl

variable {d : Fin n → ℝ}

theorem inv_ne_zero_pi (hd : ∀ i, d i ≠ 0) : ∀ i, d⁻¹ i ≠ 0 := fun i => by
  rw [Pi.inv_apply]; exact inv_ne_zero (hd i)

theorem diagAff_inv (hd : ∀ i, d i ≠ 0) (b x : Fin n → ℝ) :
    diagAff d⁻¹ (-(d⁻¹ * b)) (diagAff d b x) = x := by
  funext i
  simp only [diagAff_apply, Pi.inv_apply, Pi.neg_apply, Pi.mul_apply]
  field_simp [hd i]
  ring

theorem diagAff_inv' (hd : ∀ i, d i ≠ 0) (b y : Fin n → ℝ) :
    diagAff d b (diagAff d⁻¹ (-(d⁻¹ * b)) y) = y := by
  funext i
  simp only [diagAff_apply, Pi.inv_apply, Pi.neg_apply, Pi.mul_apply]
  field_simp [hd i]
  ring

theorem diagAff_eq (d b : Fin n → ℝ) : diagAff d b = fun x => diagCLM d x + b := by
  funext x; simp [diagAff]

theorem continuous_diagAff (d b : Fin n → ℝ) : Continuous (diagAff d b) := by
  rw [diagAff_eq]; exact (diagCLM d).continuous.add continuous_const

theorem contDiff_diagAff (d b : Fin n → ℝ) : ContDiff ℝ ∞ (diagAff d b) := by
  rw [diagAff_eq]; exact (diagCLM d).contDiff.add contDiff_const

theorem hasFDerivAt_diagAff (d b x : Fin n → ℝ) : HasFDerivAt (diagAff d b) (diagCLM d) x := by
  rw [diagAff_eq]; exact (diagCLM d).hasFDerivAt.add_const b

/-- `diagAff d b` as a homeomorphism (`dᵢ ≠ 0`). -/
def diagHomeomorph (hd : ∀ i, d i ≠ 0) (b : Fin n → ℝ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) where
  toFun := diagAff d b
  invFun := diagAff d⁻¹ (-(d⁻¹ * b))
  left_inv := diagAff_inv hd b
  right_inv := diagAff_inv' hd b
  continuous_toFun := continuous_diagAff d b
  continuous_invFun := continuous_diagAff _ _

theorem preimage_diagAff_inv (hd : ∀ i, d i ≠ 0) (b : Fin n → ℝ) (Ω' : Set (Fin n → ℝ)) :
    diagAff d⁻¹ (-(d⁻¹ * b)) ⁻¹' (diagAff d b ⁻¹' Ω') = Ω' := by
  ext y; simp only [mem_preimage, diagAff_inv' hd b]

/-- The Jacobian `|∏ dᵢ|` of `diagAff d b`. -/
def jacD (d : Fin n → ℝ) : ℝ := |∏ i, d i|

theorem jacD_pos (hd : ∀ i, d i ≠ 0) : 0 < jacD d :=
  abs_pos.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd i)

theorem det_diagCLM (d : Fin n → ℝ) :
    LinearMap.det (diagCLM d : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = ∏ i, d i := by
  have : (diagCLM d : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = Matrix.toLin' (Matrix.diagonal d) := by
    refine LinearMap.ext fun v => ?_
    funext i
    simp [Matrix.mulVec_diagonal]
  rw [this, LinearMap.det_toLin', Matrix.det_diagonal]

/-- **`diagAff d b` is measure preserving from `|∏ dᵢ| · volume` to `volume`.** -/
theorem measurePreserving_diagAff (hd : ∀ i, d i ≠ 0) (b : Fin n → ℝ) :
    MeasurePreserving (diagAff d b) (ENNReal.ofReal (jacD d) • volume) volume := by
  refine ⟨(continuous_diagAff d b).measurable, ?_⟩
  have hdet0 : LinearMap.det (diagCLM d : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≠ 0 := by
    rw [det_diagCLM]; exact Finset.prod_ne_zero_iff.2 fun i _ => hd i
  have hlin : Measure.map (fun x : Fin n → ℝ => diagCLM d x) volume =
      ENNReal.ofReal |(∏ i, d i)⁻¹| • volume := by
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℝ)) hdet0
    rw [det_diagCLM] at this
    convert this using 2
  have htr : Measure.map (fun y : Fin n → ℝ => y + b) (volume : Measure (Fin n → ℝ)) = volume :=
    map_add_right_eq_self volume b
  have hcomp : Measure.map (diagAff d b) (volume : Measure (Fin n → ℝ)) =
      Measure.map (fun y => y + b) (Measure.map (fun x : Fin n → ℝ => diagCLM d x) volume) := by
    rw [Measure.map_map (measurable_add_const b) (diagCLM d).continuous.measurable, diagAff_eq]
    rfl
  rw [Measure.map_smul (hf := (continuous_diagAff d b).measurable.aemeasurable), hcomp, hlin,
    Measure.map_smul (hf := (measurable_add_const b).aemeasurable), htr, smul_smul,
    ← ENNReal.ofReal_mul (jacD_pos hd).le]
  rw [show jacD d * |(∏ i, d i)⁻¹| = 1 by
    rw [jacD, abs_inv, mul_inv_cancel₀ (abs_pos.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd i)).ne'],
    ENNReal.ofReal_one, one_smul]

theorem measurePreserving_diagAff_restrict (hd : ∀ i, d i ≠ 0) (b : Fin n → ℝ)
    {Ω' : Set (Fin n → ℝ)} (hΩ' : MeasurableSet Ω') :
    MeasurePreserving (diagAff d b)
      (ENNReal.ofReal (jacD d) • volume.restrict (diagAff d b ⁻¹' Ω')) (volume.restrict Ω') := by
  rw [← Measure.restrict_smul]
  exact (measurePreserving_diagAff hd b).restrict_preimage hΩ'

/-! ### The pull-back on `L²` -/

theorem memLp_comp_diagAff (hd : ∀ i, d i ≠ 0) (b : Fin n → ℝ) {Ω Ω' : Set (Fin n → ℝ)}
    (hΩ' : MeasurableSet Ω') (hT : diagAff d b ⁻¹' Ω' = Ω) (f : L2 𝕜 Ω') :
    MemLp (fun x => (f : (Fin n → ℝ) → 𝕜) (diagAff d b x)) 2 (volume.restrict Ω) := by
  subst hT
  have h1 := (Lp.memLp f).comp_measurePreserving (measurePreserving_diagAff_restrict hd b hΩ')
  have h2 := h1.smul_measure (c := (ENNReal.ofReal (jacD d))⁻¹)
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (jacD_pos hd)).ne')
  rwa [smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 (jacD_pos hd)).ne'
    ENNReal.ofReal_ne_top, one_smul] at h2

theorem ae_comp_diagAff (hd : ∀ i, d i ≠ 0) (b : Fin n → ℝ) {Ω Ω' : Set (Fin n → ℝ)}
    (hΩ' : MeasurableSet Ω') (hT : diagAff d b ⁻¹' Ω' = Ω) {p : (Fin n → ℝ) → Prop}
    (h : ∀ᵐ y ∂volume.restrict Ω', p y) : ∀ᵐ x ∂volume.restrict Ω, p (diagAff d b x) := by
  subst hT
  have := (measurePreserving_diagAff_restrict hd b hΩ').quasiMeasurePreserving.ae h
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.2 (jacD_pos hd)).ne').1 this

section Pull

variable (hd : ∀ i, d i ≠ 0) (b : Fin n → ℝ) {Ω Ω' : Set (Fin n → ℝ)} (hΩ' : MeasurableSet Ω')
  (hT : diagAff d b ⁻¹' Ω' = Ω)
include hd hΩ' hT

/-- The pull-back `f ↦ f ∘ T` as a linear map `L²(Ω') → L²(Ω)`, `Ω = T⁻¹ Ω'`. -/
def pullDiagₗ : L2 𝕜 Ω' →ₗ[𝕜] L2 𝕜 Ω where
  toFun f := (memLp_comp_diagAff hd b hΩ' hT f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_comp_diagAff hd b hΩ' hT (f + g)).coeFn_toLp,
      (memLp_comp_diagAff hd b hΩ' hT f).coeFn_toLp, (memLp_comp_diagAff hd b hΩ' hT g).coeFn_toLp,
      Lp.coeFn_add ((memLp_comp_diagAff hd b hΩ' hT f).toLp _)
        ((memLp_comp_diagAff hd b hΩ' hT g).toLp _),
      ae_comp_diagAff hd b hΩ' hT (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
    rw [h4, Pi.add_apply, h1, h2, h3, h5, Pi.add_apply]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_comp_diagAff hd b hΩ' hT (c • f)).coeFn_toLp,
      (memLp_comp_diagAff hd b hΩ' hT f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_comp_diagAff hd b hΩ' hT f).toLp _),
      ae_comp_diagAff hd b hΩ' hT (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
    rw [RingHom.id_apply, h3, Pi.smul_apply, h1, h2, h4, Pi.smul_apply]

theorem coeFn_pullDiagₗ (f : L2 𝕜 Ω') :
    (pullDiagₗ hd b hΩ' hT f : (Fin n → ℝ) → 𝕜) =ᵐ[volume.restrict Ω]
      fun x => (f : (Fin n → ℝ) → 𝕜) (diagAff d b x) :=
  (memLp_comp_diagAff hd b hΩ' hT f).coeFn_toLp

/-- **Change of variables**: `∫_Ω (g ∘ T) = |∏ dᵢ|⁻¹ ∫_{Ω'} g`. -/
theorem setIntegral_comp_diagAff (g : (Fin n → ℝ) → 𝕜) :
    ∫ x in Ω, g (diagAff d b x) = (((jacD d)⁻¹ : ℝ) : 𝕜) * ∫ y in Ω', g y := by
  subst hT
  have hmp := measurePreserving_diagAff_restrict hd b hΩ'
  have e2 := hmp.integral_comp' (f := MeasurableEquiv.mk ⟨diagAff d b, diagAff d⁻¹ (-(d⁻¹ * b)),
    diagAff_inv hd b, diagAff_inv' hd b⟩ (continuous_diagAff d b).measurable
    (continuous_diagAff _ _).measurable) g
  rw [integral_smul_measure] at e2
  have hj : ((ENNReal.ofReal (jacD d)).toReal) = jacD d := ENNReal.toReal_ofReal (jacD_pos hd).le
  rw [hj] at e2
  have hjne : (jacD d : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (jacD_pos hd).ne'
  rw [← e2, RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_eq_mul, RCLike.ofReal_inv, ← mul_assoc,
    inv_mul_cancel₀ hjne, one_mul]
  rfl

/-- **The pull-back scales inner products by `|∏ dᵢ|⁻¹`.** -/
theorem inner_pullDiagₗ (f g : L2 𝕜 Ω') :
    ⟪pullDiagₗ hd b hΩ' hT f, pullDiagₗ hd b hΩ' hT g⟫_𝕜 =
      (((jacD d)⁻¹ : ℝ) : 𝕜) * ⟪f, g⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def]
  have e1 : ∫ x, ⟪(pullDiagₗ hd b hΩ' hT f : (Fin n → ℝ) → 𝕜) x,
      (pullDiagₗ hd b hΩ' hT g : (Fin n → ℝ) → 𝕜) x⟫_𝕜 ∂volume.restrict Ω =
      ∫ x in Ω, (fun y => ⟪(f : (Fin n → ℝ) → 𝕜) y, (g : (Fin n → ℝ) → 𝕜) y⟫_𝕜)
        (diagAff d b x) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_pullDiagₗ hd b hΩ' hT f, coeFn_pullDiagₗ hd b hΩ' hT g] with x h1 h2
    rw [h1, h2]
  rw [e1]
  exact setIntegral_comp_diagAff hd b hΩ' hT
    (fun y => ⟪(f : (Fin n → ℝ) → 𝕜) y, (g : (Fin n → ℝ) → 𝕜) y⟫_𝕜)

theorem norm_pullDiagₗ (f : L2 𝕜 Ω') :
    ‖pullDiagₗ hd b hΩ' hT f‖ = Real.sqrt (jacD d)⁻¹ * ‖f‖ := by
  have h := inner_pullDiagₗ hd b hΩ' hT f f
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖pullDiagₗ hd b hΩ' hT f‖ ^ 2 = (jacD d)⁻¹ * ‖f‖ ^ 2 := by exact_mod_cast h
  rw [← Real.sqrt_sq (norm_nonneg (pullDiagₗ hd b hΩ' hT f)), h',
    Real.sqrt_mul (inv_nonneg.2 (jacD_pos hd).le), Real.sqrt_sq (norm_nonneg f)]

/-- The pull-back as a continuous linear map. -/
def pullDiag : L2 𝕜 Ω' →L[𝕜] L2 𝕜 Ω :=
  (pullDiagₗ hd b hΩ' hT).mkContinuous (Real.sqrt (jacD d)⁻¹) fun f =>
    (norm_pullDiagₗ hd b hΩ' hT f).le

theorem pullDiag_apply (f : L2 𝕜 Ω') : pullDiag hd b hΩ' hT f = pullDiagₗ hd b hΩ' hT f := rfl

end Pull

/-- Pulling back along `T` and then along a right inverse `T'` of `T` is the identity. -/
theorem pullDiag_pullDiag {d d' : Fin n → ℝ} (hd : ∀ i, d i ≠ 0) (hd' : ∀ i, d' i ≠ 0)
    {b b' : Fin n → ℝ} {Ω Ω' : Set (Fin n → ℝ)} (hΩ' : MeasurableSet Ω') (hΩ : MeasurableSet Ω)
    (hT : diagAff d b ⁻¹' Ω' = Ω) (hT' : diagAff d' b' ⁻¹' Ω = Ω')
    (hcomp : ∀ y, diagAff d b (diagAff d' b' y) = y) (f : L2 𝕜 Ω') :
    pullDiag hd' b' hΩ hT' (pullDiag hd b hΩ' hT f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_pullDiagₗ hd' b' hΩ hT' (pullDiag hd b hΩ' hT f),
    ae_comp_diagAff hd' b' hΩ hT' (coeFn_pullDiagₗ hd b hΩ' hT f)] with y h1 h2
  rw [pullDiag_apply, h1, pullDiag_apply, h2, hcomp]

section PullF

variable (hd : ∀ i, d i ≠ 0) (b : Fin n → ℝ) {Ω Ω' : Set (Fin n → ℝ)} (hΩ' : MeasurableSet Ω')
  (hT : diagAff d b ⁻¹' Ω' = Ω)
include hd hΩ' hT

omit hd in
theorem measurableSet_of_diagAff : MeasurableSet Ω :=
  hT ▸ (continuous_diagAff d b).measurable hΩ'

omit hΩ' in
theorem preimage_inv_of_diagAff : diagAff d⁻¹ (-(d⁻¹ * b)) ⁻¹' Ω = Ω' :=
  hT ▸ preimage_diagAff_inv hd b Ω'

variable (ι : Type*) [Fintype ι]

/-- **The pull-back of `L²` fields** `u ↦ u ∘ T`, `L²(Ω'; 𝕜^ι) ≃ L²(Ω; 𝕜^ι)`, `Ω = T⁻¹ Ω'`;
a scaled unitary (`inner_pullDiagF`), with inverse the pull-back along `T⁻¹`. -/
def pullDiagF : L2F 𝕜 Ω' ι ≃L[𝕜] L2F 𝕜 Ω ι :=
  (PiLp.continuousLinearEquiv 2 𝕜 _).trans
    ((ContinuousLinearEquiv.piCongrRight fun _ : ι =>
      ContinuousLinearEquiv.equivOfInverse (pullDiag hd b hΩ' hT)
        (pullDiag (inv_ne_zero_pi hd) (-(d⁻¹ * b)) (measurableSet_of_diagAff b hΩ' hT)
          (preimage_inv_of_diagAff hd b hT))
        (pullDiag_pullDiag hd (inv_ne_zero_pi hd) hΩ' _ hT _ (diagAff_inv' hd b))
        (pullDiag_pullDiag (inv_ne_zero_pi hd) hd _ hΩ' _ hT (diagAff_inv hd b))).trans
      (PiLp.continuousLinearEquiv 2 𝕜 _).symm)

variable {ι}

omit [Fintype ι] in
theorem pullDiagF_apply (u : L2F 𝕜 Ω' ι) (i : ι) :
    pullDiagF hd b hΩ' hT ι u i = pullDiag hd b hΩ' hT (u i) := rfl

omit [Fintype ι] in
theorem pullDiagF_symm_apply (u : L2F 𝕜 Ω ι) :
    (pullDiagF hd b hΩ' hT ι).symm u =
      pullDiagF (inv_ne_zero_pi hd) (-(d⁻¹ * b)) (measurableSet_of_diagAff b hΩ' hT)
        (preimage_inv_of_diagAff hd b hT) ι u := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  refine WithLp.ofLp_injective 2 (funext fun i => ?_)
  change u i = pullDiag hd b hΩ' hT (pullDiag (inv_ne_zero_pi hd) (-(d⁻¹ * b))
    (measurableSet_of_diagAff b hΩ' hT) (preimage_inv_of_diagAff hd b hT) (u i))
  rw [pullDiag_pullDiag (inv_ne_zero_pi hd) hd _ hΩ' _ hT (diagAff_inv hd b)]

/-- **The pull-back scales the inner products of fields by `|∏ dᵢ|⁻¹`.** -/
theorem inner_pullDiagF (u v : L2F 𝕜 Ω' ι) :
    ⟪pullDiagF hd b hΩ' hT ι u, pullDiagF hd b hΩ' hT ι v⟫_𝕜 =
      (((jacD d)⁻¹ : ℝ) : 𝕜) * ⟪u, v⟫_𝕜 := by
  rw [L2F.inner_def, L2F.inner_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => inner_pullDiagₗ hd b hΩ' hT (u i) (v i)

omit hΩ' [Fintype ι] in
/-- Test functions pull back to test functions. -/
theorem _root_.Feec.Domain.IsTest.comp_diagAff {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : (Fin n → ℝ) → F} (hf : IsTest Ω' f) :
    IsTest Ω (fun x => f (diagAff d b x)) := by
  subst hT
  refine ⟨hf.contDiff.comp (contDiff_diagAff d b),
    hf.hasCompactSupport.comp_isClosedEmbedding (diagHomeomorph hd b).isClosedEmbedding, ?_⟩
  change tsupport (f ∘ diagHomeomorph hd b) ⊆ _
  rw [tsupport_comp_eq_preimage]
  exact preimage_mono hf.tsupport_subset

omit hΩ' [Fintype ι] in
theorem _root_.Feec.Domain.IsTestField.comp_diagAff {φ : ι → (Fin n → ℝ) → 𝕜}
    (hφ : IsTestField Ω' φ) : IsTestField Ω (fun i x => φ i (diagAff d b x)) := fun i =>
  IsTest.comp_diagAff hd b hT (hφ i)

omit [Fintype ι] in
/-- The pull-back of a test field is the composed test field. -/
theorem pullDiagF_testField {φ : ι → (Fin n → ℝ) → 𝕜} (hφ : IsTestField Ω' φ) :
    pullDiagF hd b hΩ' hT ι (testField hφ) = testField (hφ.comp_diagAff hd b hT) := by
  refine WithLp.ofLp_injective 2 (funext fun i => ?_)
  change pullDiag hd b hΩ' hT (testField hφ i) = testField (hφ.comp_diagAff hd b hT) i
  refine Lp.ext ?_
  filter_upwards [coeFn_pullDiagₗ hd b hΩ' hT (testField hφ i),
    ae_comp_diagAff hd b hΩ' hT (coeFn_testField hφ i),
    coeFn_testField (hφ.comp_diagAff hd b hT) i] with x h1 h2 h3
  rw [pullDiag_apply, h1, h2, h3]

end PullF

/-! ### The chain rule and the rescaled operator -/

/-- **Chain rule** for iterated directional derivatives along `T x = d * x + b`:
`∂^{vs} (f ∘ T) = (∂^{d * vs} f) ∘ T`. -/
theorem iterDeriv_comp_diagAff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (Fin n → ℝ) → F} (hf : ContDiff ℝ ∞ f) (d b : Fin n → ℝ) (vs : List (Fin n → ℝ)) :
    iterDeriv vs (fun x => f (diagAff d b x)) =
      fun x => iterDeriv (vs.map (diagCLM d)) f (diagAff d b x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    rw [iterDeriv_cons, ih, List.map_cons, iterDeriv_cons]
    have hg : Differentiable ℝ (iterDeriv (vs.map (diagCLM d)) f) :=
      (contDiff_iterDeriv hf _).differentiable (by simp)
    have h := (hg (diagAff d b x)).hasFDerivAt.comp x (hasFDerivAt_diagAff d b x)
    show fderiv ℝ (iterDeriv (vs.map (diagCLM d)) f ∘ diagAff d b) x v = _
    rw [h.fderiv]
    rfl

namespace ConstCoeffOp

variable {ι κ : Type*}

/-- **The rescaled operator** `A_d`: every direction `v` of `A` replaced by `d * v`
(`∂ᵢ ↦ dᵢ ∂ᵢ`), so that `A (f ∘ T) = (A_d f) ∘ T` for `T x = d * x + b`. -/
def diagScale (d : Fin n → ℝ) (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) :
    ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ where
  coeff j i := (A.coeff j i).map fun t => (t.1.map (diagCLM d), t.2)

theorem applyEntry_comp_diagAff (P : List (List (Fin n → ℝ) × 𝕜)) {f : (Fin n → ℝ) → 𝕜}
    (hf : ContDiff ℝ ∞ f) (d b : Fin n → ℝ) :
    applyEntry P (fun x => f (diagAff d b x)) =
      fun x => applyEntry (P.map fun t => (t.1.map (diagCLM d), t.2)) f (diagAff d b x) := by
  induction P with
  | nil => funext x; simp
  | cons t P ih =>
    rw [applyEntry_cons, List.map_cons, applyEntry_cons, ih, iterDeriv_comp_diagAff hf]

/-- **Chain rule** for a constant-coefficient operator: `A (f ∘ T) = (A_d f) ∘ T`. -/
theorem apply_comp_diagAff [Fintype ι] (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ)
    {f : ι → (Fin n → ℝ) → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i)) (d b : Fin n → ℝ) :
    A.apply (fun i x => f i (diagAff d b x)) =
      fun j x => (diagScale d A).apply f j (diagAff d b x) := by
  funext j x
  simp only [apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [applyEntry_comp_diagAff _ (hf i)]
  rfl

/-- The rescalings compose: `(A_d)_{d'} = A_{d d'}`. -/
theorem diagScale_diagScale (d d' : Fin n → ℝ) (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) :
    diagScale d' (diagScale d A) = diagScale (d * d') A := by
  simp only [diagScale, List.map_map]
  congr 1
  funext j i
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, List.map_map, Prod.mk.injEq, and_true]
  refine List.map_congr_left fun v _ => ?_
  funext k
  simp only [Function.comp_apply, diagCLM_apply, Pi.mul_apply]
  ring

theorem diagScale_one (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) : diagScale 1 A = A := by
  have h1 : ∀ l : List (Fin n → ℝ), l.map (diagCLM (1 : Fin n → ℝ)) = l := fun l => by
    conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left fun v _ => by simp
  have h2 : ∀ P : List (List (Fin n → ℝ) × 𝕜),
      P.map (fun t => (t.1.map (diagCLM (1 : Fin n → ℝ)), t.2)) = P := fun P => by
    conv_rhs => rw [← List.map_id P]
    exact List.map_congr_left fun t _ => by simp [h1]
  cases A
  simp only [diagScale, h2]

/-! ### Minimal and maximal realizations under diagonal maps -/

section Realization

variable [Fintype ι] [Fintype κ] {A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ} {d : Fin n → ℝ}
  (hd : ∀ i, d i ≠ 0) (b : Fin n → ℝ) {Ω Ω' : Set (Fin n → ℝ)} (hΩ' : MeasurableSet Ω')
  (hT : diagAff d b ⁻¹' Ω' = Ω)
include hd hΩ' hT

omit [Fintype κ] in
theorem pullDiagF_mem_testGraph {ψ : ι → (Fin n → ℝ) → 𝕜} (hψ : IsTestField Ω' ψ) :
    (pullDiagF hd b hΩ' hT ι (testField hψ),
      pullDiagF hd b hΩ' hT κ (testField ((diagScale d A).isTestField_apply hψ))) ∈
      A.testGraph Ω := by
  refine ⟨_, hψ.comp_diagAff hd b hT, ?_⟩
  rw [pullDiagF_testField, pullDiagF_testField]
  refine Prod.ext rfl (testField_congr _ _ ?_)
  rw [apply_comp_diagAff A (fun i => (hψ i).contDiff)]

/-- The homeomorphism `(u, w) ↦ (P⁻¹ u, P⁻¹ w)` of graphs. -/
def graphHomeomorphDiag : L2F 𝕜 Ω ι × L2F 𝕜 Ω κ ≃ₜ L2F 𝕜 Ω' ι × L2F 𝕜 Ω' κ :=
  (pullDiagF hd b hΩ' hT ι).symm.toHomeomorph.prodCongr (pullDiagF hd b hΩ' hT κ).symm.toHomeomorph

omit [Fintype ι] [Fintype κ] in
theorem graphHomeomorphDiag_apply (p : L2F 𝕜 Ω ι × L2F 𝕜 Ω κ) :
    graphHomeomorphDiag hd b hΩ' hT p =
      ((pullDiagF hd b hΩ' hT ι).symm p.1, (pullDiagF hd b hΩ' hT κ).symm p.2) := rfl

omit [Fintype κ] in
/-- **Test graphs correspond** under the pull-back: those of `A` on `Ω` and of `A_d` on `Ω'`. -/
theorem testGraph_eq_preimage_diag :
    (A.testGraph Ω : Set (L2F 𝕜 Ω ι × L2F 𝕜 Ω κ)) =
      graphHomeomorphDiag hd b hΩ' hT ⁻¹' ((diagScale d A).testGraph Ω' : Set _) := by
  ext p
  simp only [mem_preimage, SetLike.mem_coe, graphHomeomorphDiag_apply]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    have hΩ := measurableSet_of_diagAff b hΩ' hT
    have hT' := preimage_inv_of_diagAff hd b hT
    have hψ : IsTestField Ω' (fun i x => φ i (diagAff d⁻¹ (-(d⁻¹ * b)) x)) :=
      hφ.comp_diagAff (inv_ne_zero_pi hd) (-(d⁻¹ * b)) hT'
    refine ⟨_, hψ, ?_⟩
    rw [pullDiagF_symm_apply, pullDiagF_symm_apply, pullDiagF_testField, pullDiagF_testField]
    refine Prod.ext rfl (testField_congr _ _ ?_)
    have hc := apply_comp_diagAff (diagScale d A) (fun i => (hφ i).contDiff) d⁻¹ (-(d⁻¹ * b))
    rw [diagScale_diagScale] at hc
    have h1 : d * d⁻¹ = 1 := by funext i; simp [hd i]
    rw [h1, diagScale_one] at hc
    rw [hc]
  · rintro ⟨ψ, hψ, h⟩
    have h1 : p.1 = pullDiagF hd b hΩ' hT ι (testField hψ) :=
      ((pullDiagF hd b hΩ' hT ι).symm_apply_eq).1 (congrArg Prod.fst h)
    have h2 : p.2 = pullDiagF hd b hΩ' hT κ
        (testField ((diagScale d A).isTestField_apply hψ)) :=
      ((pullDiagF hd b hΩ' hT κ).symm_apply_eq).1 (congrArg Prod.snd h)
    rw [show p = (p.1, p.2) from rfl, h1, h2]
    exact pullDiagF_mem_testGraph hd b hΩ' hT hψ

/-- **The minimal realization under a diagonal change of variables**:
`A_min,Ω = P (A_d)_min,Ω' P⁻¹`, `P u = u ∘ T`. -/
theorem minimal_pullDiag (hΩo' : IsOpen Ω') :
    A.minimal Ω = ((diagScale d A).minimal Ω').conjScaled (pullDiagF hd b hΩ' hT ι)
      (pullDiagF hd b hΩ' hT κ) 1 := by
  have hΩo : IsOpen Ω := hT ▸ hΩo'.preimage (continuous_diagAff d b)
  refine LinearPMap.eq_of_eq_graph (Submodule.ext fun p => ?_)
  rw [LinearPMap.mem_graph_conjScaled one_ne_zero, inv_one, one_smul, A.minimal_graph hΩo,
    (diagScale d A).minimal_graph hΩo', ← SetLike.mem_coe, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe,
    testGraph_eq_preimage_diag hd b hΩ' hT, ← Homeomorph.preimage_closure]
  rfl

end Realization

/-! ### Conjugation by constant diagonal fibre scalings -/

section Scale

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Multiplication by a nonzero scalar, as an isomorphism. -/
def scaleL (c : 𝕜) (hc : c ≠ 0) : X ≃L[𝕜] X :=
  ContinuousLinearEquiv.equivOfInverse (c • ContinuousLinearMap.id 𝕜 X)
    (c⁻¹ • ContinuousLinearMap.id 𝕜 X) (fun x => by simp [smul_smul, hc])
    (fun x => by simp [smul_smul, hc])

@[simp] theorem scaleL_apply (c : 𝕜) (hc : c ≠ 0) (x : X) : scaleL c hc x = c • x := rfl

@[simp] theorem scaleL_symm_apply (c : 𝕜) (hc : c ≠ 0) (x : X) :
    (scaleL c hc).symm x = c⁻¹ • x := rfl

end Scale

variable {Ω : Set (Fin n → ℝ)}

/-- The constant diagonal scaling `u ↦ (wᵢ uᵢ)ᵢ` of `L²(Ω; 𝕜^ι)`. -/
def scaleF (w : ι → 𝕜) (hw : ∀ i, w i ≠ 0) : L2F 𝕜 Ω ι ≃L[𝕜] L2F 𝕜 Ω ι :=
  (PiLp.continuousLinearEquiv 2 𝕜 _).trans
    ((ContinuousLinearEquiv.piCongrRight fun i => scaleL (w i) (hw i)).trans
      (PiLp.continuousLinearEquiv 2 𝕜 _).symm)

@[simp] theorem scaleF_apply (w : ι → 𝕜) (hw : ∀ i, w i ≠ 0) (u : L2F 𝕜 Ω ι) (i : ι) :
    scaleF w hw u i = w i • u i := rfl

@[simp] theorem scaleF_symm_apply (w : ι → 𝕜) (hw : ∀ i, w i ≠ 0) (u : L2F 𝕜 Ω ι) (i : ι) :
    (scaleF w hw).symm u i = (w i)⁻¹ • u i := rfl

theorem _root_.Feec.Domain.IsTestField.scale {w : ι → 𝕜} {φ : ι → (Fin n → ℝ) → 𝕜}
    (hφ : IsTestField Ω φ) :
    IsTestField Ω (fun i => w i • φ i) := fun i => (hφ i).smul (w i)

theorem scaleF_testField {w : ι → 𝕜} (hw : ∀ i, w i ≠ 0) {φ : ι → (Fin n → ℝ) → 𝕜}
    (hφ : IsTestField Ω φ) : scaleF w hw (testField hφ) = testField (hφ.scale (w := w)) := by
  refine WithLp.ofLp_injective 2 (funext fun i => ?_)
  change w i • testField hφ i = testField (hφ.scale (w := w)) i
  rw [testField_apply, testField_apply]
  exact (toL2_smul (w i) (hφ i)).symm

variable [Fintype ι] [Fintype κ]

/-- **Conjugation by constant diagonal fibre scalings**: if `B (w • ψ) = w' • A ψ` on smooth
fields (`wᵢ, w'ⱼ ≠ 0`), then `B_min = (w' •) A_min (w •)⁻¹`. -/
theorem minimal_eq_conj_scaleF {A B : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ} {w : ι → 𝕜} {w' : κ → 𝕜}
    (hw : ∀ i, w i ≠ 0) (hw' : ∀ j, w' j ≠ 0)
    (hAB : ∀ ψ : ι → (Fin n → ℝ) → 𝕜, (∀ i, ContDiff ℝ ∞ (ψ i)) →
      B.apply (fun i => w i • ψ i) = fun j => w' j • A.apply ψ j) (hΩ : IsOpen Ω) :
    B.minimal Ω = (A.minimal Ω).conjScaled (scaleF w hw) (scaleF w' hw') 1 := by
  let G : L2F 𝕜 Ω ι × L2F 𝕜 Ω κ ≃ₜ L2F 𝕜 Ω ι × L2F 𝕜 Ω κ :=
    (scaleF w hw).symm.toHomeomorph.prodCongr (scaleF w' hw').symm.toHomeomorph
  have hw0 : ∀ i, (w i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hw i)
  have hset : (B.testGraph Ω : Set (L2F 𝕜 Ω ι × L2F 𝕜 Ω κ)) =
      G ⁻¹' (A.testGraph Ω : Set _) := by
    ext p
    simp only [mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      have hψ : IsTestField Ω (fun i => (w i)⁻¹ • φ i) := hφ.scale
      refine ⟨_, hψ, ?_⟩
      have e1 : (scaleF w hw).symm (testField hφ) = testField hψ := by
        refine WithLp.ofLp_injective 2 (funext fun i => ?_)
        change (w i)⁻¹ • testField hφ i = testField hψ i
        rw [testField_apply, testField_apply]
        exact (toL2_smul _ (hφ i)).symm
      have hφ' : φ = fun i => w i • (fun i => (w i)⁻¹ • φ i) i := by
        funext i x
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← mul_assoc, mul_inv_cancel₀ (hw i), one_mul]
      have e2 : (scaleF w' hw').symm (testField (B.isTestField_apply hφ)) =
          testField (A.isTestField_apply hψ) := by
        refine WithLp.ofLp_injective 2 (funext fun j => ?_)
        change (w' j)⁻¹ • testField (B.isTestField_apply hφ) j =
          testField (A.isTestField_apply hψ) j
        rw [testField_apply, ← toL2_smul]
        refine congrArg (fun f => f j) (congrArg WithLp.ofLp (testField_congr
          ((B.isTestField_apply hφ).scale (w := fun j => (w' j)⁻¹)) _ ?_))
        conv_lhs => rw [hφ', hAB _ fun i => (hψ i).contDiff]
        funext j x
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ (hw' j), one_mul]
      exact Prod.ext e1 e2
    · rintro ⟨ψ, hψ, h⟩
      have h1 : p.1 = scaleF w hw (testField hψ) :=
        ((scaleF w hw).symm_apply_eq).1 (congrArg Prod.fst h)
      have h2 : p.2 = scaleF w' hw' (testField (A.isTestField_apply hψ)) :=
        ((scaleF w' hw').symm_apply_eq).1 (congrArg Prod.snd h)
      refine ⟨_, hψ.scale (w := w), ?_⟩
      rw [show p = (p.1, p.2) from rfl, h1, h2, scaleF_testField, scaleF_testField]
      refine Prod.ext rfl (testField_congr _ _ ?_)
      rw [hAB _ fun i => (hψ i).contDiff]
  refine LinearPMap.eq_of_eq_graph (Submodule.ext fun p => ?_)
  rw [LinearPMap.mem_graph_conjScaled one_ne_zero, inv_one, one_smul, B.minimal_graph hΩ,
    A.minimal_graph hΩ, ← SetLike.mem_coe, ← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Submodule.topologicalClosure_coe, hset, ← Homeomorph.preimage_closure]
  rfl

end ConstCoeffOp

/-! ### Complexes under diagonal maps -/

namespace ConstCoeffComplex

variable (C : ConstCoeffComplex (Fin n → ℝ) 𝕜)

/-- **The rescaled complex** `A_d k`: a complex again (`A_d (A_d f) = (A (A (f ∘ T))) ∘ T⁻¹`
for `T x = d * x`). -/
abbrev diagScale (hd : ∀ i, d i ≠ 0) : ConstCoeffComplex (Fin n → ℝ) 𝕜 where
  ι := C.ι
  fintype := C.fintype
  A k := ConstCoeffOp.diagScale d (C.A k)
  comp k f hf := by
    have hinv : ∀ y, diagAff d 0 (diagAff d⁻¹ 0 y) = y := fun y => by
      funext i; simp [diagAff_apply, hd i]
    have hg : ∀ i, ContDiff ℝ ∞ (fun x => f i (diagAff d 0 x)) := fun i =>
      (hf i).comp (contDiff_diagAff d 0)
    have h1 := ConstCoeffOp.apply_comp_diagAff (C.A k) hf d 0
    have hAd : ∀ j, ContDiff ℝ ∞ ((ConstCoeffOp.diagScale d (C.A k)).apply f j) := fun j =>
      (ConstCoeffOp.diagScale d (C.A k)).contDiff_apply hf j
    have h2 := ConstCoeffOp.apply_comp_diagAff (C.A (k + 1)) hAd d 0
    rw [← h1, C.comp k _ hg] at h2
    funext j y
    have := congrFun (congrFun h2 j) (diagAff d⁻¹ 0 y)
    rw [hinv] at this
    exact this.symm

@[simp] theorem diagScale_A (hd : ∀ i, d i ≠ 0) (k : ℤ) :
    (C.diagScale hd).A k = ConstCoeffOp.diagScale d (C.A k) := rfl

variable (hd : ∀ i, d i ≠ 0) (b : Fin n → ℝ) {Ω Ω' : Set (Fin n → ℝ)} (hΩ' : IsOpen Ω')
  (hΩ : IsOpen Ω) (hT : diagAff d b ⁻¹' Ω' = Ω)
include hT

end ConstCoeffComplex

/-! ### The row-wise gradient and curl -/

section GradCurl

theorem mul_coordDir (d : Fin n → ℝ) (k : Fin n) : d * coordDir k = d k • coordDir k := by
  funext j
  by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem fderiv_mul_coordDir {f : (Fin n → ℝ) → 𝕜} (d : Fin n → ℝ) (k : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ f x (d * coordDir k) = (d k : 𝕜) * fderiv ℝ f x (coordDir k) := by
  rw [mul_coordDir, ContinuousLinearMap.map_smul, RCLike.real_smul_eq_coe_mul]

/-- The rescaled gradient: `(grad_d f)_{ij} = d_j ∂_j f_i`. -/
theorem gradOp_diagScale_apply {m : ℕ} (d : Fin n → ℝ) (f : Fin m → (Fin n → ℝ) → 𝕜)
    (ij : Fin m × Fin n) (x : Fin n → ℝ) :
    (ConstCoeffOp.diagScale d (gradOp n m)).apply f ij x =
      (d ij.2 : 𝕜) * fderiv ℝ (f ij.1) x (coordDir ij.2) := by
  simp [ConstCoeffOp.apply, ConstCoeffOp.diagScale, gradOp, apply_ite (List.map _),
    ConstCoeffOp.applyEntry_ite, iterDeriv_singleton, fderiv_mul_coordDir]

/-- The rescaled row-wise curl:
`(curl_d Φ)_{ik} = d_{k+1} ∂_{k+1} Φ_{i,k+2} − d_{k+2} ∂_{k+2} Φ_{i,k+1}`. -/
theorem curlOp_diagScale_apply {m : ℕ} (d : Fin 3 → ℝ) (Φ : Fin m × Fin 3 → (Fin 3 → ℝ) → 𝕜)
    (ik : Fin m × Fin 3) (x : Fin 3 → ℝ) :
    (ConstCoeffOp.diagScale d (curlOp m)).apply Φ ik x =
      (d (ik.2 + 1) : 𝕜) * fderiv ℝ (Φ (ik.1, ik.2 + 2)) x (coordDir (ik.2 + 1)) -
        (d (ik.2 + 2) : 𝕜) * fderiv ℝ (Φ (ik.1, ik.2 + 1)) x (coordDir (ik.2 + 2)) := by
  obtain ⟨i, k⟩ := ik
  simp only [ConstCoeffOp.apply, ConstCoeffOp.diagScale, curlOp, apply_ite (List.map _),
    List.map_cons, List.map_nil, ConstCoeffOp.applyEntry_ite, ConstCoeffOp.applyEntry_singleton,
    ConstCoeffOp.applyEntry_nil', Fintype.sum_prod_type, iterDeriv_singleton, diagCLM_apply,
    fderiv_mul_coordDir]
  simp only [Fin.sum_univ_three]
  fin_cases k <;> simp [Finset.sum_add_distrib] <;> ring

/-- **`grad_d σ = (grad σ) D`**: the rescaled gradient is the gradient followed by the column
scaling `(a, b) ↦ d_b`. -/
theorem gradOp_diagScale_smul (d : Fin n → ℝ) {m : ℕ} (ψ : Fin m → (Fin n → ℝ) → 𝕜) :
    (ConstCoeffOp.diagScale d (gradOp n m)).apply (fun i => (1 : 𝕜) • ψ i) =
      fun ij => (d ij.2 : 𝕜) • (gradOp n m).apply ψ ij := by
  funext ij x
  rw [gradOp_diagScale_apply, Pi.smul_apply, gradOp_apply, one_smul, smul_eq_mul]

/-- **`curl_d (E D) = det D · (curl E) D⁻¹`** entrywise: with the column scalings
`(a, b) ↦ d_b` on the argument and `(a, b) ↦ d_{b+1} d_{b+2}` on the value. -/
theorem curlOp_diagScale_smul (d : Fin 3 → ℝ) {m : ℕ} {ψ : Fin m × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (hψ : ∀ p, Differentiable ℝ (ψ p)) :
    (ConstCoeffOp.diagScale d (curlOp m)).apply (fun p => (d p.2 : 𝕜) • ψ p) =
      fun p => ((d (p.2 + 1) * d (p.2 + 2) : ℝ) : 𝕜) • (curlOp m).apply ψ p := by
  funext p x
  rw [curlOp_diagScale_apply, Pi.smul_apply, curlOp_apply, fderiv_const_smul (hψ _ x),
    fderiv_const_smul (hψ _ x)]
  simp only [smul_apply, smul_eq_mul]
  push_cast
  ring

end GradCurl

end Feec.Domain
