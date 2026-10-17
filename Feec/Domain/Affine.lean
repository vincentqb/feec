module

public import Feec.Domain.Complexes
public import Feec.HilbertComplex.Transport

/-!
# Affine changes of variables

Let `T x = a • x + b` with `a ≠ 0` be an affine map of `E` (`ℝⁿ`), `Ω' ⊆ E` measurable (open
for the realizations) and `Ω = T⁻¹(Ω')`. The pull-back `f ↦ f ∘ T` is a **scaled unitary**
`L²(Ω'; 𝕜^ι) ≃ L²(Ω; 𝕜^ι)`:
`⟪f ∘ T, g ∘ T⟫ = |a|^{-n} ⟪f, g⟫` (`pullF`, `inner_pullF`). A constant-coefficient operator `A`
homogeneous of order `r` satisfies the chain rule `A (f ∘ T) = a^r (A f) ∘ T`
(`apply_comp_aff`), so the pull-back carries its realizations to each other with the chain-rule
factor `a^r`:

* `minimal_pull`: `A_min,Ω = a^r · P A_min,Ω' P⁻¹` (closures of the test graphs correspond);
* `maximal_pull`: `A_max,Ω = a^r · P A_max,Ω' P⁻¹` (by duality,
  `LinearPMap.adjoint_conjScaled`).

For a complex of homogeneous operators the minimal (and maximal) complex on `Ω` is the transport
of the one on `Ω'` (`minimalComplex_pull`, `maximalComplex_pull`), and the pull-back is a
`Feec.HilbertComplex.ScaledEmbedding` between them (`scaledEmbeddingMinimal`), with scale
`|a|^{-n}` and chain-rule factors `a^{r_k}`. This transports every reducing subcomplex, hence
constraint propagation, from one domain to its affine images (e.g. from `(0, ½)³` to every open
cube).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the cube complexes under dilations and translations)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (change of variables in Sobolev spaces)
-/

open scoped InnerProductSpace ContDiff ENNReal ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology Module

@[expose] public noncomputable section

/-! ### Adjoints of scaled conjugations -/

namespace LinearPMap

variable {𝕜 : Type*} [RCLike 𝕜] {E₁ F₁ E₂ F₂ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

/-- The scaled conjugation `κ • e₂ ∘ T ∘ e₁⁻¹` of a partial map, on `e₁ D(T)`. -/
def conjScaled (T : E₁ →ₗ.[𝕜] F₁) (e₁ : E₁ ≃L[𝕜] E₂) (e₂ : F₁ ≃L[𝕜] F₂) (κ : 𝕜) :
    E₂ →ₗ.[𝕜] F₂ where
  domain := T.domain.comap (e₁.symm : E₂ →ₗ[𝕜] E₁)
  toFun := κ • ((e₂ : F₁ →ₗ[𝕜] F₂).comp (T.toFun.comp
    ((e₁.symm : E₂ →ₗ[𝕜] E₁).restrict (p := T.domain.comap (e₁.symm : E₂ →ₗ[𝕜] E₁))
      (q := T.domain) fun _ hy => hy)))

variable {T : E₁ →ₗ.[𝕜] F₁} {e₁ : E₁ ≃L[𝕜] E₂} {e₂ : F₁ ≃L[𝕜] F₂} {κ : 𝕜}

theorem mem_conjScaled_domain {y : E₂} :
    y ∈ (T.conjScaled e₁ e₂ κ).domain ↔ e₁.symm y ∈ T.domain := Iff.rfl

theorem conjScaled_apply (y : (T.conjScaled e₁ e₂ κ).domain) :
    T.conjScaled e₁ e₂ κ y = κ • e₂ (T ⟨e₁.symm y, y.2⟩) := rfl

theorem mem_graph_conjScaled (hκ : κ ≠ 0) {p : E₂ × F₂} :
    p ∈ (T.conjScaled e₁ e₂ κ).graph ↔ (e₁.symm p.1, κ⁻¹ • e₂.symm p.2) ∈ T.graph := by
  rw [mem_graph_iff, mem_graph_iff]
  constructor
  · rintro ⟨y, hy1, hy2⟩
    refine ⟨⟨_, y.2⟩, by simp [← hy1], ?_⟩
    rw [← hy2, conjScaled_apply, _root_.map_smul, ContinuousLinearEquiv.symm_apply_apply,
      inv_smul_smul₀ hκ]
    rfl
  · rintro ⟨x, hx1, hx2⟩
    have hx1' : (x : E₁) = e₁.symm p.1 := hx1
    have hp : p.1 ∈ (T.conjScaled e₁ e₂ κ).domain := show e₁.symm p.1 ∈ _ from hx1' ▸ x.2
    refine ⟨⟨p.1, hp⟩, rfl, ?_⟩
    have e2 : T ⟨e₁.symm p.1, hp⟩ = κ⁻¹ • e₂.symm p.2 := by
      rw [← show T x = κ⁻¹ • e₂.symm p.2 from hx2]
      exact apply_congr' _ _ _ hx1'.symm
    change κ • e₂ (T ⟨e₁.symm p.1, hp⟩) = p.2
    rw [e2, _root_.map_smul, ContinuousLinearEquiv.apply_symm_apply, smul_inv_smul₀ hκ]

theorem dense_conjScaled_domain (hd : Dense (T.domain : Set E₁)) :
    Dense ((T.conjScaled e₁ e₂ κ).domain : Set E₂) :=
  hd.preimage e₁.symm.toHomeomorph.isOpenMap

variable [CompleteSpace E₁] [CompleteSpace E₂]

/-- **Adjoints of scaled conjugations** by isometries scaling the inner products by the same
`s > 0`: `(κ e₂ T e₁⁻¹)† = conj κ · e₁ T† e₂⁻¹`. -/
theorem adjoint_conjScaled {s : ℝ} (hs : 0 < s)
    (he₁ : ∀ x y : E₁, ⟪e₁ x, e₁ y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (he₂ : ∀ x y : F₁, ⟪e₂ x, e₂ y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜) (hκ : κ ≠ 0)
    (hd : Dense (T.domain : Set E₁)) :
    (T.conjScaled e₁ e₂ κ)† = (T†).conjScaled e₂ e₁ (conj κ) := by
  have hs' : (s : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hs.ne'
  have hfa := adjoint_isFormalAdjoint hd
  have hle : (T†).conjScaled e₂ e₁ (conj κ) ≤ (T.conjScaled e₁ e₂ κ)† := by
    refine IsFormalAdjoint.le_adjoint (dense_conjScaled_domain hd) fun x y => ?_
    rw [conjScaled_apply, conjScaled_apply]
    have hy : (y : F₂) = e₂ (e₂.symm y) := (e₂.apply_symm_apply _).symm
    have hx : (x : E₂) = e₁ (e₁.symm x) := (e₁.apply_symm_apply _).symm
    have h1 := hfa ⟨e₂.symm y, y.2⟩ ⟨e₁.symm x, x.2⟩
    conv_lhs => rw [hy]
    conv_rhs => rw [hx]
    rw [inner_smul_left, he₂, inner_smul_right, he₁]
    rw [← inner_conj_symm, ← h1, inner_conj_symm]
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  change e₂.symm y ∈ (T†).domain
  set z := (T.conjScaled e₁ e₂ κ)† ⟨y, hy⟩
  refine mem_adjoint_domain_of_exists _ ⟨conj κ⁻¹ • e₁.symm z, fun x => ?_⟩
  have hx : e₁.symm (e₁ x) ∈ T.domain := by
    rw [ContinuousLinearEquiv.symm_apply_apply]; exact x.2
  have h2 := adjoint_isFormalAdjoint (dense_conjScaled_domain (T := T) (e₁ := e₁) (e₂ := e₂)
    (κ := κ) hd) ⟨y, hy⟩ ⟨e₁ x, hx⟩
  rw [conjScaled_apply, apply_congr' T hx x.2 (e₁.symm_apply_apply x)] at h2
  change ⟪z, e₁ x⟫_𝕜 = ⟪y, κ • e₂ (T x)⟫_𝕜 at h2
  rw [inner_smul_right, show (y : F₂) = e₂ (e₂.symm y) from (e₂.apply_symm_apply _).symm,
    he₂, show z = e₁ (e₁.symm z) from (e₁.apply_symm_apply _).symm, he₁] at h2
  have h3 : ⟪e₁.symm z, (x : E₁)⟫_𝕜 = κ * ⟪e₂.symm y, T x⟫_𝕜 :=
    mul_left_cancel₀ hs' (h2.trans (by ring))
  rw [inner_smul_left, RCLike.conj_conj, h3, ← mul_assoc, inv_mul_cancel₀ hκ, one_mul]

end LinearPMap

namespace Feec.Domain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
  {𝕜 : Type*} [RCLike 𝕜]

/-! ### The affine map and its measure -/

/-- The affine map `x ↦ a • x + b`. -/
def aff (a : ℝ) (b : E) (x : E) : E := a • x + b

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem aff_inv {a : ℝ} (ha : a ≠ 0) (b : E) (x : E) :
    aff a⁻¹ (-(a⁻¹ • b)) (aff a b x) = x := by
  simp [aff, smul_add, smul_smul, inv_mul_cancel₀ ha]

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem aff_inv' {a : ℝ} (ha : a ≠ 0) (b : E) (y : E) :
    aff a b (aff a⁻¹ (-(a⁻¹ • b)) y) = y := by
  simp [aff, smul_add, smul_smul, mul_inv_cancel₀ ha]

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem continuous_aff (a : ℝ) (b : E) : Continuous (aff a b) :=
  (continuous_const_smul a).add continuous_const

/-- The Jacobian `|a|ⁿ` of `aff a b`. -/
def jac (a : ℝ) : ℝ := |a| ^ finrank ℝ E

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem jac_pos {a : ℝ} (ha : a ≠ 0) : 0 < jac (E := E) a := pow_pos (abs_pos.2 ha) _

/-- **`aff a b` is measure preserving from `|a|ⁿ · volume` to `volume`.** -/
theorem measurePreserving_aff {a : ℝ} (ha : a ≠ 0) (b : E) :
    MeasurePreserving (aff a b) (ENNReal.ofReal (jac (E := E) a) • volume) volume := by
  refine ⟨(continuous_aff a b).measurable, ?_⟩
  have hdet : LinearMap.det (a • LinearMap.id : E →ₗ[ℝ] E) = a ^ finrank ℝ E := by
    simp [LinearMap.det_smul]
  have hdet0 : LinearMap.det (a • LinearMap.id : E →ₗ[ℝ] E) ≠ 0 := by
    rw [hdet]; exact pow_ne_zero _ ha
  have hlin : Measure.map (fun x : E => a • x) volume =
      ENNReal.ofReal |(a ^ finrank ℝ E)⁻¹| • volume := by
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E) hdet0
    rw [hdet] at this
    convert this using 2
  have htr : Measure.map (fun y : E => y + b) (volume : Measure E) = volume :=
    map_add_right_eq_self volume b
  have hcomp : Measure.map (aff a b) (volume : Measure E) =
      Measure.map (fun y => y + b) (Measure.map (fun x : E => a • x) volume) := by
    rw [Measure.map_map (measurable_add_const b) (measurable_const_smul a)]; rfl
  rw [Measure.map_smul (hf := (continuous_aff a b).measurable.aemeasurable), hcomp, hlin,
    Measure.map_smul (hf := (measurable_add_const b).aemeasurable), htr, smul_smul,
    ← ENNReal.ofReal_mul (jac_pos ha).le]
  rw [show jac (E := E) a * |(a ^ finrank ℝ E)⁻¹| = 1 by
    rw [jac, abs_inv, abs_pow, mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.2 ha))],
    ENNReal.ofReal_one, one_smul]

theorem measurePreserving_aff_restrict {a : ℝ} (ha : a ≠ 0) (b : E) {Ω' : Set E}
    (hΩ' : MeasurableSet Ω') :
    MeasurePreserving (aff a b) (ENNReal.ofReal (jac (E := E) a) • volume.restrict (aff a b ⁻¹' Ω'))
      (volume.restrict Ω') := by
  rw [← Measure.restrict_smul]
  exact (measurePreserving_aff ha b).restrict_preimage hΩ'

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem preimage_aff_inv {a : ℝ} (ha : a ≠ 0) (b : E) (Ω' : Set E) :
    aff a⁻¹ (-(a⁻¹ • b)) ⁻¹' (aff a b ⁻¹' Ω') = Ω' := by
  ext y; simp only [mem_preimage, aff_inv' ha b]

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem jac_inv (a : ℝ) : jac (E := E) a⁻¹ = (jac (E := E) a)⁻¹ := by
  rw [jac, jac, abs_inv, inv_pow]

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem contDiff_aff (a : ℝ) (b : E) : ContDiff ℝ ∞ (aff a b) :=
  (contDiff_id.const_smul a).add contDiff_const

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem hasFDerivAt_aff (a : ℝ) (b : E) (x : E) :
    HasFDerivAt (aff a b) (a • ContinuousLinearMap.id ℝ E) x :=
  ((hasFDerivAt_id x).const_smul a).add_const b

/-- `aff a b` as a homeomorphism (`a ≠ 0`). -/
def affHomeomorph {a : ℝ} (ha : a ≠ 0) (b : E) : E ≃ₜ E where
  toFun := aff a b
  invFun := aff a⁻¹ (-(a⁻¹ • b))
  left_inv := aff_inv ha b
  right_inv := aff_inv' ha b
  continuous_toFun := continuous_aff a b
  continuous_invFun := continuous_aff _ _

/-! ### The pull-back on `L²` -/

theorem memLp_comp_aff {a : ℝ} (ha : a ≠ 0) (b : E) {Ω Ω' : Set E} (hΩ' : MeasurableSet Ω')
    (hT : aff a b ⁻¹' Ω' = Ω) (f : L2 𝕜 Ω') :
    MemLp (fun x => (f : E → 𝕜) (aff a b x)) 2 (volume.restrict Ω) := by
  subst hT
  have h1 := (Lp.memLp f).comp_measurePreserving (measurePreserving_aff_restrict ha b hΩ')
  have h2 := h1.smul_measure (c := (ENNReal.ofReal (jac (E := E) a))⁻¹)
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (jac_pos ha)).ne')
  rwa [smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 (jac_pos ha)).ne'
    ENNReal.ofReal_ne_top, one_smul] at h2

theorem ae_comp_aff {a : ℝ} (ha : a ≠ 0) (b : E) {Ω Ω' : Set E} (hΩ' : MeasurableSet Ω')
    (hT : aff a b ⁻¹' Ω' = Ω) {p : E → Prop} (h : ∀ᵐ y ∂volume.restrict Ω', p y) :
    ∀ᵐ x ∂volume.restrict Ω, p (aff a b x) := by
  subst hT
  have := (measurePreserving_aff_restrict ha b hΩ').quasiMeasurePreserving.ae h
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.2 (jac_pos ha)).ne').1 this

section Pull

variable {a : ℝ} (ha : a ≠ 0) (b : E) {Ω Ω' : Set E} (hΩ' : MeasurableSet Ω')
  (hT : aff a b ⁻¹' Ω' = Ω)
include ha hΩ' hT

/-- The pull-back `f ↦ f ∘ T` as a linear map `L²(Ω') → L²(Ω)`, `Ω = T⁻¹ Ω'`. -/
def pullₗ : L2 𝕜 Ω' →ₗ[𝕜] L2 𝕜 Ω where
  toFun f := (memLp_comp_aff ha b hΩ' hT f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_comp_aff ha b hΩ' hT (f + g)).coeFn_toLp,
      (memLp_comp_aff ha b hΩ' hT f).coeFn_toLp, (memLp_comp_aff ha b hΩ' hT g).coeFn_toLp,
      Lp.coeFn_add ((memLp_comp_aff ha b hΩ' hT f).toLp _)
        ((memLp_comp_aff ha b hΩ' hT g).toLp _),
      ae_comp_aff ha b hΩ' hT (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
    rw [h4, Pi.add_apply, h1, h2, h3, h5, Pi.add_apply]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_comp_aff ha b hΩ' hT (c • f)).coeFn_toLp,
      (memLp_comp_aff ha b hΩ' hT f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_comp_aff ha b hΩ' hT f).toLp _),
      ae_comp_aff ha b hΩ' hT (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
    rw [RingHom.id_apply, h3, Pi.smul_apply, h1, h2, h4, Pi.smul_apply]

theorem coeFn_pullₗ (f : L2 𝕜 Ω') :
    (pullₗ ha b hΩ' hT f : E → 𝕜) =ᵐ[volume.restrict Ω] fun x => (f : E → 𝕜) (aff a b x) :=
  (memLp_comp_aff ha b hΩ' hT f).coeFn_toLp

/-- **The pull-back scales inner products by `|a|^{-n}`.** -/
theorem inner_pullₗ (f g : L2 𝕜 Ω') :
    ⟪pullₗ ha b hΩ' hT f, pullₗ ha b hΩ' hT g⟫_𝕜 =
      (((jac (E := E) a)⁻¹ : ℝ) : 𝕜) * ⟪f, g⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def]
  have e1 : ∫ x, ⟪(pullₗ ha b hΩ' hT f : E → 𝕜) x, (pullₗ ha b hΩ' hT g : E → 𝕜) x⟫_𝕜
      ∂volume.restrict Ω =
      ∫ x, ⟪(f : E → 𝕜) (aff a b x), (g : E → 𝕜) (aff a b x)⟫_𝕜 ∂volume.restrict Ω := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_pullₗ ha b hΩ' hT f, coeFn_pullₗ ha b hΩ' hT g] with x h1 h2
    rw [h1, h2]
  rw [e1]
  subst hT
  have hmp := measurePreserving_aff_restrict ha b hΩ' (E := E)
  have e2 := hmp.integral_comp' (f := MeasurableEquiv.mk ⟨aff a b, aff a⁻¹ (-(a⁻¹ • b)),
    aff_inv ha b, aff_inv' ha b⟩ (continuous_aff a b).measurable (continuous_aff _ _).measurable)
    (fun y => ⟪(f : E → 𝕜) y, (g : E → 𝕜) y⟫_𝕜)
  rw [integral_smul_measure] at e2
  have hj : ((ENNReal.ofReal (jac (E := E) a)).toReal) = jac (E := E) a :=
    ENNReal.toReal_ofReal (jac_pos ha).le
  rw [hj] at e2
  have hjne : (jac (E := E) a : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (jac_pos ha).ne'
  rw [← e2, RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_eq_mul, RCLike.ofReal_inv, ← mul_assoc,
    inv_mul_cancel₀ hjne, one_mul]
  rfl

theorem norm_pullₗ (f : L2 𝕜 Ω') :
    ‖pullₗ ha b hΩ' hT f‖ = Real.sqrt (jac (E := E) a)⁻¹ * ‖f‖ := by
  have h := inner_pullₗ ha b hΩ' hT f f
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖pullₗ ha b hΩ' hT f‖ ^ 2 = (jac (E := E) a)⁻¹ * ‖f‖ ^ 2 := by exact_mod_cast h
  rw [← Real.sqrt_sq (norm_nonneg (pullₗ ha b hΩ' hT f)), h',
    Real.sqrt_mul (inv_nonneg.2 (jac_pos ha).le), Real.sqrt_sq (norm_nonneg f)]

/-- The pull-back as a continuous linear map. -/
def pull : L2 𝕜 Ω' →L[𝕜] L2 𝕜 Ω :=
  (pullₗ ha b hΩ' hT).mkContinuous (Real.sqrt (jac (E := E) a)⁻¹) fun f =>
    (norm_pullₗ ha b hΩ' hT f).le

theorem pull_apply (f : L2 𝕜 Ω') : pull ha b hΩ' hT f = pullₗ ha b hΩ' hT f := rfl

end Pull

/-- Pulling back along `T` and then along a right inverse `T'` of `T` is the identity. -/
theorem pull_pull {a a' : ℝ} (ha : a ≠ 0) (ha' : a' ≠ 0) {b b' : E} {Ω Ω' : Set E}
    (hΩ' : MeasurableSet Ω') (hΩ : MeasurableSet Ω) (hT : aff a b ⁻¹' Ω' = Ω)
    (hT' : aff a' b' ⁻¹' Ω = Ω') (hcomp : ∀ y, aff a b (aff a' b' y) = y) (f : L2 𝕜 Ω') :
    pull ha' b' hΩ hT' (pull ha b hΩ' hT f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_pullₗ ha' b' hΩ hT' (pull ha b hΩ' hT f),
    ae_comp_aff ha' b' hΩ hT' (coeFn_pullₗ ha b hΩ' hT f)] with y h1 h2
  rw [pull_apply, h1, pull_apply, h2, hcomp]

section PullE

variable {a : ℝ} (ha : a ≠ 0) (b : E) {Ω Ω' : Set E} (hΩ' : MeasurableSet Ω')
  (hT : aff a b ⁻¹' Ω' = Ω)
include ha hΩ' hT

omit [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] ha in
theorem measurableSet_of_aff : MeasurableSet Ω := hT ▸ (continuous_aff a b).measurable hΩ'

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] hΩ' in
theorem preimage_inv_of_aff : aff a⁻¹ (-(a⁻¹ • b)) ⁻¹' Ω = Ω' := hT ▸ preimage_aff_inv ha b Ω'

variable (ι : Type*) [Fintype ι]

/-- **The pull-back of `L²` fields** `u ↦ u ∘ T`, `L²(Ω'; 𝕜^ι) ≃ L²(Ω; 𝕜^ι)`, `Ω = T⁻¹ Ω'`;
a scaled unitary (`inner_pullF`), with inverse the pull-back along `T⁻¹` (`pullF_symm_apply`). -/
def pullF : L2F 𝕜 Ω' ι ≃L[𝕜] L2F 𝕜 Ω ι :=
  (PiLp.continuousLinearEquiv 2 𝕜 _).trans
    ((ContinuousLinearEquiv.piCongrRight fun _ : ι =>
      ContinuousLinearEquiv.equivOfInverse (pull ha b hΩ' hT)
        (pull (inv_ne_zero ha) (-(a⁻¹ • b)) (measurableSet_of_aff b hΩ' hT)
          (preimage_inv_of_aff ha b hT))
        (pull_pull ha (inv_ne_zero ha) hΩ' _ hT _ (aff_inv' ha b))
        (pull_pull (inv_ne_zero ha) ha _ hΩ' _ hT (aff_inv ha b))).trans
      (PiLp.continuousLinearEquiv 2 𝕜 _).symm)

variable {ι}

omit [Fintype ι] in
theorem pullF_apply (u : L2F 𝕜 Ω' ι) (i : ι) :
    pullF ha b hΩ' hT ι u i = pull ha b hΩ' hT (u i) := rfl

omit [Fintype ι] in
theorem pullF_symm_apply (u : L2F 𝕜 Ω ι) :
    (pullF ha b hΩ' hT ι).symm u =
      pullF (inv_ne_zero ha) (-(a⁻¹ • b)) (measurableSet_of_aff b hΩ' hT)
        (preimage_inv_of_aff ha b hT) ι u := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  refine WithLp.ofLp_injective 2 (funext fun i => ?_)
  change u i = pull ha b hΩ' hT (pull (inv_ne_zero ha) (-(a⁻¹ • b)) (measurableSet_of_aff b hΩ' hT)
    (preimage_inv_of_aff ha b hT) (u i))
  rw [pull_pull (inv_ne_zero ha) ha _ hΩ' _ hT (aff_inv ha b)]

/-- **The pull-back scales the inner products of fields by `|a|^{-n}`.** -/
theorem inner_pullF (u v : L2F 𝕜 Ω' ι) :
    ⟪pullF ha b hΩ' hT ι u, pullF ha b hΩ' hT ι v⟫_𝕜 =
      (((jac (E := E) a)⁻¹ : ℝ) : 𝕜) * ⟪u, v⟫_𝕜 := by
  rw [L2F.inner_def, L2F.inner_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => inner_pullₗ ha b hΩ' hT (u i) (v i)

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] hΩ' [Fintype ι] in
/-- Test fields pull back to test fields. -/
theorem _root_.Feec.Domain.IsTest.comp_aff' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : IsTest Ω' f) : IsTest Ω (fun x => f (aff a b x)) := by
  subst hT
  refine ⟨hf.contDiff.comp (contDiff_aff a b),
    hf.hasCompactSupport.comp_isClosedEmbedding (affHomeomorph ha b).isClosedEmbedding, ?_⟩
  change tsupport (f ∘ affHomeomorph ha b) ⊆ _
  rw [tsupport_comp_eq_preimage]
  exact preimage_mono hf.tsupport_subset

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] hΩ' [Fintype ι] in
theorem _root_.Feec.Domain.IsTestField.comp_aff {φ : ι → E → 𝕜} (hφ : IsTestField Ω' φ) :
    IsTestField Ω (fun i x => φ i (aff a b x)) := fun i =>
  IsTest.comp_aff' ha b hT (hφ i)

omit [Fintype ι] in
/-- The pull-back of a test field is the composed test field. -/
theorem pullF_testField {φ : ι → E → 𝕜} (hφ : IsTestField Ω' φ) :
    pullF ha b hΩ' hT ι (testField hφ) = testField (hφ.comp_aff ha b hT) := by
  refine WithLp.ofLp_injective 2 (funext fun i => ?_)
  change pull ha b hΩ' hT (testField hφ i) = testField (hφ.comp_aff ha b hT) i
  refine Lp.ext ?_
  filter_upwards [coeFn_pullₗ ha b hΩ' hT (testField hφ i),
    ae_comp_aff ha b hΩ' hT (coeFn_testField hφ i),
    coeFn_testField (hφ.comp_aff ha b hT) i] with x h1 h2 h3
  rw [pull_apply, h1, h2, h3]

end PullE

/-! ### The chain rule -/

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- **Chain rule** for iterated directional derivatives along `T x = a • x + b`:
`∂^{vs} (f ∘ T) = a^{#vs} (∂^{vs} f) ∘ T`. -/
theorem iterDeriv_comp_aff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ ∞ f) (a : ℝ) (b : E) (vs : List E) :
    iterDeriv vs (fun x => f (aff a b x)) =
      fun x => a ^ vs.length • iterDeriv vs f (aff a b x) := by
  induction vs with
  | nil => funext x; simp
  | cons v vs ih =>
    funext x
    rw [iterDeriv_cons, ih, iterDeriv_cons]
    have hg : Differentiable ℝ (iterDeriv vs f) :=
      (contDiff_iterDeriv hf vs).differentiable (by simp)
    have h := ((hg (aff a b x)).hasFDerivAt.comp x (hasFDerivAt_aff a b x)).const_smul
      (a ^ vs.length)
    have e : fderiv ℝ (fun x => a ^ vs.length • iterDeriv vs f (aff a b x)) x = _ := h.fderiv
    show fderiv ℝ (fun x => a ^ vs.length • iterDeriv vs f (aff a b x)) x v =
      a ^ (vs.length + 1) • fderiv ℝ (iterDeriv vs f) (aff a b x) v
    rw [e]
    simp [pow_succ, smul_smul]

namespace ConstCoeffOp

variable {ι κ : Type*}

/-- `A` is **homogeneous of order `r`**: every term has exactly `r` derivatives. -/
def IsHomogeneous (A : ConstCoeffOp E 𝕜 ι κ) (r : ℕ) : Prop :=
  ∀ j i, ∀ t ∈ A.coeff j i, t.1.length = r

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
theorem IsHomogeneous.formalAdj {A : ConstCoeffOp E 𝕜 ι κ} {r : ℕ} (h : A.IsHomogeneous r) :
    A.formalAdj.IsHomogeneous r := by
  intro i j t ht
  change t ∈ adjEntry (A.coeff j i) at ht
  simp only [adjEntry, List.mem_map] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  simpa using h j i t' ht'

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem applyEntry_comp_aff {P : List (List E × 𝕜)} {r : ℕ} (hP : ∀ t ∈ P, t.1.length = r)
    {f : E → 𝕜} (hf : ContDiff ℝ ∞ f) (a : ℝ) (b : E) :
    applyEntry P (fun x => f (aff a b x)) =
      fun x => ((a ^ r : ℝ) : 𝕜) * applyEntry P f (aff a b x) := by
  induction P with
  | nil => funext x; simp
  | cons t P ih =>
    rw [applyEntry_cons, applyEntry_cons, ih fun s hs => hP s (List.mem_cons_of_mem _ hs),
      iterDeriv_comp_aff hf, hP t List.mem_cons_self]
    funext x
    show t.2 * (a ^ r • iterDeriv t.1 f (aff a b x)) +
        ((a ^ r : ℝ) : 𝕜) * applyEntry P f (aff a b x) =
      ((a ^ r : ℝ) : 𝕜) * (t.2 * iterDeriv t.1 f (aff a b x) + applyEntry P f (aff a b x))
    rw [RCLike.real_smul_eq_coe_mul]
    ring

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- **Chain rule** for a homogeneous operator of order `r`: `A (f ∘ T) = a^r (A f) ∘ T`. -/
theorem apply_comp_aff [Fintype ι] {A : ConstCoeffOp E 𝕜 ι κ} {r : ℕ} (hA : A.IsHomogeneous r)
    {f : ι → E → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i)) (a : ℝ) (b : E) :
    A.apply (fun i x => f i (aff a b x)) =
      fun j x => ((a ^ r : ℝ) : 𝕜) * A.apply f j (aff a b x) := by
  funext j x
  simp only [apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [applyEntry_comp_aff (hA j i) (hf i)]

/-! ### Minimal and maximal realizations under affine maps -/

section Graph

variable [Fintype ι] [Fintype κ]

variable (ι κ) in
/-- The homeomorphism `(u, w) ↦ (P⁻¹ u, a^{-r} P⁻¹ w)` of graphs. -/
def graphHomeomorph (r : ℕ) {a : ℝ} (ha : a ≠ 0) (b : E) {Ω Ω' : Set E}
    (hΩ' : MeasurableSet Ω') (hT : aff a b ⁻¹' Ω' = Ω) :
    L2F 𝕜 Ω ι × L2F 𝕜 Ω κ ≃ₜ L2F 𝕜 Ω' ι × L2F 𝕜 Ω' κ :=
  (pullF ha b hΩ' hT ι).symm.toHomeomorph.prodCongr
    ((pullF ha b hΩ' hT κ).symm.toHomeomorph.trans
      (Homeomorph.smulOfNeZero (((a ^ r : ℝ) : 𝕜))⁻¹
        (inv_ne_zero (RCLike.ofReal_ne_zero.2 (pow_ne_zero r ha)))))

omit [Fintype ι] in
theorem graphHomeomorph_apply (r : ℕ) {a : ℝ} (ha : a ≠ 0) (b : E) {Ω Ω' : Set E}
    (hΩ' : MeasurableSet Ω') (hT : aff a b ⁻¹' Ω' = Ω) (p : L2F 𝕜 Ω ι × L2F 𝕜 Ω κ) :
    graphHomeomorph ι κ r ha b hΩ' hT p =
      ((pullF ha b hΩ' hT ι).symm p.1, (((a ^ r : ℝ) : 𝕜))⁻¹ • (pullF ha b hΩ' hT κ).symm p.2) :=
  rfl

end Graph

section Realization

variable [Fintype ι] [Fintype κ] {A : ConstCoeffOp E 𝕜 ι κ} {r : ℕ} (hA : A.IsHomogeneous r)
  {a : ℝ} (ha : a ≠ 0) (b : E) {Ω Ω' : Set E} (hΩ' : MeasurableSet Ω') (hT : aff a b ⁻¹' Ω' = Ω)
include hA ha hΩ' hT

omit [Fintype κ] in
theorem pullF_mem_testGraph {ψ : ι → E → 𝕜} (hψ : IsTestField Ω' ψ) :
    (pullF ha b hΩ' hT ι (testField hψ),
      ((a ^ r : ℝ) : 𝕜) • pullF ha b hΩ' hT κ (testField (A.isTestField_apply hψ))) ∈
      A.testGraph Ω := by
  refine ⟨_, hψ.comp_aff ha b hT, ?_⟩
  rw [pullF_testField, pullF_testField, ← testField_smul]
  refine Prod.ext rfl (testField_congr _ _ ?_)
  rw [apply_comp_aff hA (fun i => (hψ i).contDiff)]
  rfl

/-- **Test graphs correspond** under the pull-back. -/
theorem testGraph_eq_preimage :
    (A.testGraph Ω : Set (L2F 𝕜 Ω ι × L2F 𝕜 Ω κ)) =
      graphHomeomorph (𝕜 := 𝕜) ι κ r ha b hΩ' hT ⁻¹' (A.testGraph Ω' : Set _) := by
  have hκ : ((a ^ r : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (pow_ne_zero r ha)
  ext p
  simp only [mem_preimage, SetLike.mem_coe, graphHomeomorph_apply]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    have hΩ := measurableSet_of_aff b hΩ' hT
    have hT' := preimage_inv_of_aff ha b hT
    have h := pullF_mem_testGraph hA (inv_ne_zero ha) (-(a⁻¹ • b)) hΩ hT' hφ
    rw [pullF_symm_apply, pullF_symm_apply]
    convert h using 3
    push_cast
    rw [inv_pow]
  · rintro ⟨ψ, hψ, h⟩
    have h1 : p.1 = pullF ha b hΩ' hT ι (testField hψ) :=
      ((pullF ha b hΩ' hT ι).symm_apply_eq).1 (congrArg Prod.fst h)
    have h2 : p.2 =
        ((a ^ r : ℝ) : 𝕜) • pullF ha b hΩ' hT κ (testField (A.isTestField_apply hψ)) := by
      have := congrArg Prod.snd h
      simp only at this
      rw [← this, _root_.map_smul, ContinuousLinearEquiv.apply_symm_apply, smul_inv_smul₀ hκ]
    rw [show p = (p.1, p.2) from rfl, h1, h2]
    exact pullF_mem_testGraph hA ha b hΩ' hT hψ

/-- **The minimal realization under an affine change of variables**:
`A_min,Ω = a^r · P A_min,Ω' P⁻¹`, `P u = u ∘ T`. -/
theorem minimal_pull (hΩo' : IsOpen Ω') :
    A.minimal Ω = (A.minimal Ω').conjScaled (pullF ha b hΩ' hT ι) (pullF ha b hΩ' hT κ)
      ((a ^ r : ℝ) : 𝕜) := by
  have hκ : ((a ^ r : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (pow_ne_zero r ha)
  have hΩo : IsOpen Ω := hT ▸ hΩo'.preimage (continuous_aff a b)
  refine LinearPMap.eq_of_eq_graph (Submodule.ext fun p => ?_)
  rw [LinearPMap.mem_graph_conjScaled hκ, A.minimal_graph hΩo, A.minimal_graph hΩo',
    ← SetLike.mem_coe, ← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Submodule.topologicalClosure_coe, testGraph_eq_preimage hA ha b hΩ' hT,
    ← Homeomorph.preimage_closure]
  rfl

/-- **The maximal realization under an affine change of variables**:
`A_max,Ω = a^r · P A_max,Ω' P⁻¹` (by duality from `minimal_pull`). -/
theorem maximal_pull (hΩo' : IsOpen Ω') :
    A.maximal Ω = (A.maximal Ω').conjScaled (pullF ha b hΩ' hT ι) (pullF ha b hΩ' hT κ)
      ((a ^ r : ℝ) : 𝕜) := by
  have hκ : ((a ^ r : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (pow_ne_zero r ha)
  rw [maximal, maximal, minimal_pull hA.formalAdj ha b hΩ' hT hΩo',
    LinearPMap.adjoint_conjScaled (inv_pos.2 (jac_pos ha)) (inner_pullF ha b hΩ' hT)
      (inner_pullF ha b hΩ' hT) hκ (A.formalAdj.dense_minimal_domain hΩo'), RCLike.conj_ofReal]

end Realization

end ConstCoeffOp

/-! ### Complexes under affine maps -/

namespace ConstCoeffComplex

/-- The chain-rule factors `a^{r k}` of a complex of homogeneous operators of orders `r k`. -/
def chainFactor (a : ℝ) (r : ℤ → ℕ) (i j : ℤ) : 𝕜 := if i + 1 = j then ((a ^ r i : ℝ) : 𝕜) else 1

theorem chainFactor_ne_zero {a : ℝ} (ha : a ≠ 0) (r : ℤ → ℕ) (i j : ℤ) :
    chainFactor (𝕜 := 𝕜) a r i j ≠ 0 := by
  unfold chainFactor
  split_ifs
  · exact RCLike.ofReal_ne_zero.2 (pow_ne_zero _ ha)
  · exact one_ne_zero

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem transportD_eq_conjScaled {ι : Type*} {c : ComplexShape ι} {W W' : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)]
    [∀ i, CompleteSpace (W' i)] (H : HilbertComplex 𝕜 c W) (e : ∀ i, W i ≃L[𝕜] W' i)
    (κ : ι → ι → 𝕜) (i j : ι) :
    HilbertComplex.transportD H e κ i j = (H.d i j).conjScaled (e i) (e j) (κ i j) := rfl

variable (C : ConstCoeffComplex E 𝕜) {r : ℤ → ℕ} (hC : ∀ k, (C.A k).IsHomogeneous (r k))
  {a : ℝ} (ha : a ≠ 0) (b : E) {Ω Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ : IsOpen Ω)
  (hT : aff a b ⁻¹' Ω' = Ω)
include hC ha hT

/-- **The minimal complex on `Ω = T⁻¹ Ω'` is the transport of the one on `Ω'`** along the
pull-back, with the chain-rule factors `a^{r k}`. -/
theorem minimalComplex_pull :
    C.minimalComplex hΩ = (C.minimalComplex hΩ').transport
      (fun k => pullF (𝕜 := 𝕜) ha b hΩ'.measurableSet hT (C.ι k)) (chainFactor a r)
      (chainFactor_ne_zero ha r) := by
  refine HilbertComplex.ext_d (funext fun i => funext fun j => ?_)
  by_cases h : i + 1 = j
  · subst h
    rw [HilbertComplex.transport_d, transportD_eq_conjScaled, minimalComplex_d, minimalComplex_d,
      chainFactor, ite_eq_left rfl]
    exact ConstCoeffOp.minimal_pull (hC i) ha b hΩ'.measurableSet hT hΩ'
  · rw [(C.minimalComplex hΩ).shape i j h, HilbertComplex.transport_d,
      HilbertComplex.transportD_eq_zero ((C.minimalComplex hΩ').shape i j h)]

/-- **The maximal complex on `Ω = T⁻¹ Ω'` is the transport of the one on `Ω'`.** -/
theorem maximalComplex_pull :
    C.maximalComplex hΩ = (C.maximalComplex hΩ').transport
      (fun k => pullF (𝕜 := 𝕜) ha b hΩ'.measurableSet hT (C.ι k)) (chainFactor a r)
      (chainFactor_ne_zero ha r) := by
  refine HilbertComplex.ext_d (funext fun i => funext fun j => ?_)
  by_cases h : i + 1 = j
  · subst h
    rw [HilbertComplex.transport_d, transportD_eq_conjScaled, maximalComplex_d, maximalComplex_d,
      chainFactor, ite_eq_left rfl]
    exact ConstCoeffOp.maximal_pull (hC i) ha b hΩ'.measurableSet hT hΩ'
  · rw [(C.maximalComplex hΩ).shape i j h, HilbertComplex.transport_d,
      HilbertComplex.transportD_eq_zero ((C.maximalComplex hΩ').shape i j h)]

/-- **The pull-back is a scaled embedding between the minimal complexes** on `Ω'` and on
`Ω = T⁻¹ Ω'`: scale `|a|^{-n}`, chain-rule factors `a^{r k}`. -/
def scaledEmbeddingMinimal :
    HilbertComplex.ScaledEmbedding (C.minimalComplex hΩ') (C.minimalComplex hΩ) := by
  rw [C.minimalComplex_pull hC ha b hΩ' hΩ hT]
  exact HilbertComplex.ScaledEmbedding.ofTransport _ _ _ _ (fun _ => (jac (E := E) a)⁻¹)
    (fun _ => inv_pos.2 (jac_pos ha)) fun k => inner_pullF ha b hΩ'.measurableSet hT

/-- **The pull-back is a scaled embedding between the maximal complexes.** -/
def scaledEmbeddingMaximal :
    HilbertComplex.ScaledEmbedding (C.maximalComplex hΩ') (C.maximalComplex hΩ) := by
  rw [C.maximalComplex_pull hC ha b hΩ' hΩ hT]
  exact HilbertComplex.ScaledEmbedding.ofTransport _ _ _ _ (fun _ => (jac (E := E) a)⁻¹)
    (fun _ => inv_pos.2 (jac_pos ha)) fun k => inner_pullF ha b hΩ'.measurableSet hT

end ConstCoeffComplex

end Feec.Domain
