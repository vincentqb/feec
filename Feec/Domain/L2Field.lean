module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# `L²` fields on an open subset of a finite-dimensional real space

Let `E` be a finite-dimensional real normed space with an additive Haar measure `volume` (for
instance `ℝⁿ = Fin n → ℝ` or `EuclideanSpace ℝ (Fin n)`), `Ω ⊆ E` open, and `𝕜 = ℝ` or `ℂ`.

* `Feec.Domain.IsTest Ω f`: `f ∈ C_c^∞(Ω; F)` (smooth, compact support inside `Ω`), for any
  real normed codomain `F`; closed under sums, scalars, continuous linear maps and directional
  derivatives (`IsTest.fderiv_apply`).
* `Feec.Domain.L2 𝕜 Ω = L²(Ω; 𝕜)` and the component model `Feec.Domain.L2F 𝕜 Ω ι =
  ⊕ₗ²_{i ∈ ι} L²(Ω; 𝕜)` of `L²(Ω; 𝕜^ι)` (`ι` a finite index set: vector, matrix, symmetric
  matrix, … components).
* `toL2`, `testField`: test functions and test fields as `L²` classes, with
  `inner_testField : ⟪u, φ⟫ = Σᵢ ∫_Ω conj (uᵢ) φᵢ`.
* `L2.eq_zero_of_forall_inner_toL2`, `L2F.eq_zero_of_forall_inner_testField` (fundamental lemma
  of the calculus of variations, no boundedness of `Ω`) and `dense_testFieldSub` (test fields are
  dense in `L²(Ω; 𝕜^ι)`).
* `memLp_of_continuous`: on a bounded `Ω`, continuous functions on `E` are in `L²(Ω)`.
* **Bochner bridge** `piL2Equiv μ ι : L²(μ; EuclideanSpace 𝕜 ι) ≃ₗᵢ ⊕ₗ²_{i ∈ ι} L²(μ; 𝕜)`
  (any measure, componentwise), so the component model is the Bochner space `L²(Ω; 𝕜^ι)`.

## References

* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §4.4 (density of `C_c^∞`), §9.1

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff ENNReal ComplexConjugate
open MeasureTheory Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Domain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Test functions -/

section Test

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `f ∈ C_c^∞(Ω; F)`: smooth, compactly supported, with support inside `Ω`. -/
structure IsTest (Ω : Set E) (f : E → F) : Prop where
  contDiff : ContDiff ℝ ∞ f
  hasCompactSupport : HasCompactSupport f
  tsupport_subset : tsupport f ⊆ Ω

namespace IsTest

variable {Ω : Set E} {f g : E → F}

theorem continuous (hf : IsTest Ω f) : Continuous f := hf.contDiff.continuous

theorem differentiable (hf : IsTest Ω f) : Differentiable ℝ f :=
  hf.contDiff.differentiable (by simp)

theorem eq_zero_of_notMem (hf : IsTest Ω f) {x : E} (hx : x ∉ Ω) : f x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hf.tsupport_subset h)

theorem zero : IsTest Ω (0 : E → F) := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

theorem add (hf : IsTest Ω f) (hg : IsTest Ω g) : IsTest Ω (f + g) :=
  ⟨hf.contDiff.add hg.contDiff, hf.hasCompactSupport.add hg.hasCompactSupport,
    (tsupport_add f g).trans (union_subset hf.tsupport_subset hg.tsupport_subset)⟩

theorem comp_clm (hf : IsTest Ω f) (L : F →L[ℝ] G) : IsTest Ω (fun x => L (f x)) :=
  ⟨L.contDiff.comp hf.contDiff, hf.hasCompactSupport.comp_left L.map_zero,
    (tsupport_comp_subset L.map_zero f).trans hf.tsupport_subset⟩

theorem neg (hf : IsTest Ω f) : IsTest Ω (-f) :=
  ⟨hf.contDiff.neg, hf.hasCompactSupport.neg, (tsupport_neg f).trans_subset hf.tsupport_subset⟩

theorem sub (hf : IsTest Ω f) (hg : IsTest Ω g) : IsTest Ω (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] (c : 𝕜)
    (hf : IsTest Ω f) : IsTest Ω (c • f) :=
  ⟨hf.contDiff.const_smul c, hf.hasCompactSupport.smul_left,
    (tsupport_smul_subset_right _ f).trans hf.tsupport_subset⟩

theorem const_mul {𝕜 : Type*} [RCLike 𝕜] {f : E → 𝕜} (c : 𝕜) (hf : IsTest Ω f) :
    IsTest Ω (fun x => c * f x) := hf.smul c

theorem sum {α : Type*} (s : Finset α) {f : α → E → F} (hf : ∀ a ∈ s, IsTest Ω (f a)) :
    IsTest Ω (fun x => ∑ a ∈ s, f a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact IsTest.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

/-- The directional derivative `∂_v f` of a test function is a test function. -/
theorem fderiv_apply (hf : IsTest Ω f) (v : E) : IsTest Ω (fun x => fderiv ℝ f x v) where
  contDiff := (hf.contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  hasCompactSupport := HasCompactSupport.fderiv_apply ℝ hf.hasCompactSupport _
  tsupport_subset := (tsupport_fderiv_apply_subset _ _).trans hf.tsupport_subset

theorem mono {Ω' : Set E} (hf : IsTest Ω f) (h : Ω ⊆ Ω') : IsTest Ω' f :=
  ⟨hf.contDiff, hf.hasCompactSupport, hf.tsupport_subset.trans h⟩

/-- A real test function, as a `𝕜`-valued one. -/
theorem ofReal {𝕜 : Type*} [RCLike 𝕜] {g : E → ℝ} (hg : IsTest Ω g) :
    IsTest Ω (fun x => (g x : 𝕜)) :=
  hg.comp_clm (RCLike.ofRealCLM (K := 𝕜))

/-- The complex conjugate of a test function. -/
theorem conjugate {𝕜 : Type*} [RCLike 𝕜] {f : E → 𝕜} (hf : IsTest Ω f) :
    IsTest Ω (fun x => conj (f x)) :=
  hf.comp_clm (RCLike.conjCLE (K := 𝕜)).toContinuousLinearMap

end IsTest

/-- A test field `φ ∈ C_c^∞(Ω; F^ι)`: every component is a test function. -/
def IsTestField (Ω : Set E) {ι : Type*} (φ : ι → E → F) : Prop := ∀ i, IsTest Ω (φ i)

namespace IsTestField

variable {Ω : Set E} {ι : Type*} {φ ψ : ι → E → F}

theorem zero : IsTestField Ω (0 : ι → E → F) := fun _ => IsTest.zero

theorem add (hφ : IsTestField Ω φ) (hψ : IsTestField Ω ψ) : IsTestField Ω (φ + ψ) :=
  fun i => (hφ i).add (hψ i)

theorem smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] (c : 𝕜)
    (hφ : IsTestField Ω φ) : IsTestField Ω (c • φ) := fun i => (hφ i).smul c

theorem single [DecidableEq ι] (i : ι) {g : E → F} (hg : IsTest Ω g) :
    IsTestField Ω (Pi.single i g) := by
  intro j
  by_cases h : j = i
  · subst h; simpa using hg
  · simpa [h] using (IsTest.zero : IsTest Ω (0 : E → F))

end IsTestField

end Test

/-! ## `L²` spaces on a domain -/

section L2

variable [MeasureSpace E] {𝕜 : Type*} [RCLike 𝕜] {Ω : Set E}

variable (𝕜 Ω) in
/-- `L²(Ω; 𝕜)`, for the measure `volume` restricted to `Ω`. -/
abbrev L2 := Lp 𝕜 2 (volume.restrict Ω)

variable (𝕜 Ω) in
/-- `L²(Ω; 𝕜^ι)` in the component model: the `ℓ²`-sum of `#ι` copies of `L²(Ω; 𝕜)`. -/
abbrev L2F (ι : Type*) := PiLp 2 (fun _ : ι => L2 𝕜 Ω)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A function vanishing off `Ω` has the same integral over `Ω` and over `E`. -/
theorem integral_restrict_of_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ∀ x, x ∉ Ω → f x = 0) :
    ∫ x, f x ∂volume.restrict Ω = ∫ x, f x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero hf

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `⟪u, f⟫_{L²(Ω)} = ∫_Ω conj u · f` for a function `f ∈ L²(Ω)`. -/
theorem inner_toLp (u : L2 𝕜 Ω) {f : E → 𝕜} (hf : MemLp f 2 (volume.restrict Ω)) :
    ⟪u, hf.toLp f⟫_𝕜 = ∫ x, conj (u x) * f x ∂volume.restrict Ω := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, RCLike.inner_apply]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Products `conj u · f`, `u, f ∈ L²(Ω)`, are integrable on `Ω`. -/
theorem integrable_conj_mul (u : L2 𝕜 Ω) {f : E → 𝕜} (hf : MemLp f 2 (volume.restrict Ω)) :
    Integrable (fun x => conj (u x) * f x) (volume.restrict Ω) := by
  refine (L2.integrable_inner u (hf.toLp f)).congr ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, RCLike.inner_apply]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `⟪u, v⟫ = Σᵢ ⟪uᵢ, vᵢ⟫` in `L²(Ω; 𝕜^ι)`. -/
theorem L2F.inner_def {ι : Type*} [Fintype ι] (u v : L2F 𝕜 Ω ι) :
    ⟪u, v⟫_𝕜 = ∑ i, ⟪u i, v i⟫_𝕜 := PiLp.inner_apply u v

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem L2F.continuous_apply {ι : Type*} (i : ι) : Continuous fun u : L2F 𝕜 Ω ι => u i :=
  (PiLp.proj (𝕜 := 𝕜) 2 (fun _ : ι => L2 𝕜 Ω) i).continuous

section Test

variable [BorelSpace E] [IsFiniteMeasureOnCompacts (volume : Measure E)]

/-- Test functions are in `L²(Ω)` (no boundedness of `Ω` needed). -/
theorem IsTest.memLp {f : E → 𝕜} (hf : IsTest Ω f) : MemLp f 2 (volume.restrict Ω) :=
  (hf.continuous.memLp_of_hasCompactSupport hf.hasCompactSupport).restrict _

/-- A test function as an element of `L²(Ω)`. -/
def toL2 {f : E → 𝕜} (hf : IsTest Ω f) : L2 𝕜 Ω := hf.memLp.toLp f

theorem coeFn_toL2 {f : E → 𝕜} (hf : IsTest Ω f) :
    (toL2 hf : E → 𝕜) =ᵐ[volume.restrict Ω] f := hf.memLp.coeFn_toLp

/-- `⟪u, f⟫_{L²(Ω)} = ∫_Ω conj u · f` for a test function `f`. -/
theorem inner_toL2 (u : L2 𝕜 Ω) {f : E → 𝕜} (hf : IsTest Ω f) :
    ⟪u, toL2 hf⟫_𝕜 = ∫ x, conj (u x) * f x ∂volume.restrict Ω :=
  inner_toLp u hf.memLp

theorem toL2_congr {f g : E → 𝕜} (hf : IsTest Ω f) (hg : IsTest Ω g) (h : f = g) :
    toL2 hf = toL2 hg := by subst h; rfl

theorem toL2_add {f g : E → 𝕜} (hf : IsTest Ω f) (hg : IsTest Ω g) :
    toL2 (hf.add hg) = toL2 hf + toL2 hg := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toL2 (hf.add hg), coeFn_toL2 hf, coeFn_toL2 hg,
    Lp.coeFn_add (toL2 hf) (toL2 hg)] with x h1 h2 h3 h4
  simp only [h1, h4, Pi.add_apply, h2, h3]

theorem toL2_smul (c : 𝕜) {f : E → 𝕜} (hf : IsTest Ω f) :
    toL2 (hf.smul c) = c • toL2 hf := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toL2 (hf.smul c), coeFn_toL2 hf, Lp.coeFn_smul c (toL2 hf)]
    with x h1 h2 h3
  simp only [h1, h3, Pi.smul_apply, h2]

theorem toL2_zero : toL2 (IsTest.zero : IsTest Ω (0 : E → 𝕜)) = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toL2 (IsTest.zero : IsTest Ω (0 : E → 𝕜)),
    Lp.coeFn_zero 𝕜 2 (volume.restrict Ω)] with x h1 h2
  rw [h1, h2]

/-- A test field as an element of `L²(Ω; 𝕜^ι)`. -/
def testField {ι : Type*} {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) : L2F 𝕜 Ω ι :=
  WithLp.toLp 2 fun i => toL2 (hφ i)

@[simp] theorem testField_apply {ι : Type*} {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) (i : ι) :
    testField hφ i = toL2 (hφ i) := rfl

theorem coeFn_testField {ι : Type*} {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) (i : ι) :
    (testField hφ i : E → 𝕜) =ᵐ[volume.restrict Ω] φ i := coeFn_toL2 (hφ i)

/-- `⟪u, φ⟫ = Σᵢ ∫_Ω conj uᵢ · φᵢ`. -/
theorem inner_testField {ι : Type*} [Fintype ι] (u : L2F 𝕜 Ω ι) {φ : ι → E → 𝕜}
    (hφ : IsTestField Ω φ) :
    ⟪u, testField hφ⟫_𝕜 = ∑ i, ∫ x, conj (u i x) * φ i x ∂volume.restrict Ω := by
  rw [L2F.inner_def]
  exact Finset.sum_congr rfl fun i _ => inner_toL2 _ (hφ i)

/-- An `L²` field equal a.e. on `Ω` to a test field is that test field. -/
theorem eq_testField {ι : Type*} {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) {u : L2F 𝕜 Ω ι}
    (h : ∀ i, (u i : E → 𝕜) =ᵐ[volume.restrict Ω] φ i) : u = testField hφ :=
  (WithLp.ext_iff 2).2 (funext fun i => Lp.ext ((h i).trans (coeFn_testField hφ i).symm))


theorem testField_add {ι : Type*} {φ ψ : ι → E → 𝕜} (hφ : IsTestField Ω φ)
    (hψ : IsTestField Ω ψ) : testField (hφ.add hψ) = testField hφ + testField hψ :=
  (WithLp.ext_iff 2).2 (funext fun i => toL2_add (hφ i) (hψ i))

theorem testField_smul {ι : Type*} (c : 𝕜) {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) :
    testField (hφ.smul c) = c • testField hφ :=
  (WithLp.ext_iff 2).2 (funext fun i => toL2_smul c (hφ i))

theorem testField_zero {ι : Type*} : testField (IsTestField.zero : IsTestField Ω (0 : ι → E → 𝕜)) = 0 :=
  (WithLp.ext_iff 2).2 (funext fun _ => toL2_zero)

variable (𝕜 Ω) in
/-- The subspace `C_c^∞(Ω; 𝕜^ι)` of `L²(Ω; 𝕜^ι)`. -/
def testFieldSub (ι : Type*) : Submodule 𝕜 (L2F 𝕜 Ω ι) where
  carrier := {u | ∃ φ : ι → E → 𝕜, ∃ hφ : IsTestField Ω φ, u = testField hφ}
  zero_mem' := ⟨0, IsTestField.zero, testField_zero.symm⟩
  add_mem' := by
    rintro _ _ ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
    exact ⟨φ + ψ, hφ.add hψ, (testField_add hφ hψ).symm⟩
  smul_mem' := by
    rintro c _ ⟨φ, hφ, rfl⟩
    exact ⟨c • φ, hφ.smul c, (testField_smul c hφ).symm⟩

theorem testField_mem_testFieldSub {ι : Type*} {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) :
    testField hφ ∈ testFieldSub 𝕜 Ω ι := ⟨φ, hφ, rfl⟩

end Test

end L2

/-! ## The fundamental lemma and density of test fields -/

section Density

variable [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [IsFiniteMeasureOnCompacts (volume : Measure E)] {𝕜 : Type*} [RCLike 𝕜] {Ω : Set E}

/-- **Fundamental lemma of the calculus of variations** in `L²(Ω)`, `Ω` open (bounded or not):
`u = 0` if `∫_Ω conj u · g = 0` for every real test function `g`. -/
theorem L2.eq_zero_of_forall_integral (hΩ : IsOpen Ω) (u : L2 𝕜 Ω)
    (h : ∀ g : E → ℝ, IsTest Ω g → ∫ x, conj (u x) * (g x : 𝕜) ∂volume.restrict Ω = 0) :
    u = 0 := by
  have hloc : LocallyIntegrableOn (u : E → 𝕜) Ω volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp u).locallyIntegrable one_le_two)
  have hae := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgs => by
    have hgt : IsTest Ω g := ⟨hg, hgc, hgs⟩
    rw [← integral_restrict_of_eq_zero (Ω := Ω) fun x hx => by
      simp [hgt.eq_zero_of_notMem hx]]
    have e : (fun x => g x • (u x : 𝕜)) = fun x => conj (conj (u x) * (g x : 𝕜)) := by
      funext x
      simp [RCLike.real_smul_eq_coe_mul, mul_comm]
    rw [e, integral_conj, h g hgt, map_zero]
  refine Lp.ext ?_
  filter_upwards [(ae_restrict_iff' hΩ.measurableSet).2 hae,
    Lp.coeFn_zero 𝕜 2 (volume.restrict Ω)] with x hx h0
  rw [hx, h0, Pi.zero_apply]

/-- `u = 0` if `u ⊥ C_c^∞(Ω)` (`Ω` open). -/
theorem L2.eq_zero_of_forall_inner_toL2 (hΩ : IsOpen Ω) (u : L2 𝕜 Ω)
    (h : ∀ g : E → 𝕜, ∀ hg : IsTest Ω g, ⟪u, toL2 hg⟫_𝕜 = 0) : u = 0 :=
  L2.eq_zero_of_forall_integral hΩ u fun g hg => by
    rw [← inner_toL2 u hg.ofReal]; exact h _ _

/-- An `L²` field orthogonal to every test field vanishes (`Ω` open). -/
theorem L2F.eq_zero_of_forall_inner_testField (hΩ : IsOpen Ω) {ι : Type*} [Fintype ι]
    (u : L2F 𝕜 Ω ι) (h : ∀ φ : ι → E → 𝕜, ∀ hφ : IsTestField Ω φ, ⟪u, testField hφ⟫_𝕜 = 0) :
    u = 0 := by
  classical
  refine (WithLp.ext_iff 2).2 (funext fun i => ?_)
  refine L2.eq_zero_of_forall_inner_toL2 hΩ (u i) fun g hg => ?_
  have e := h _ (IsTestField.single i hg)
  rw [L2F.inner_def, Finset.sum_eq_single i] at e
  · rw [← e, testField_apply]
    congr 1
    exact toL2_congr _ _ (by simp)
  · intro j _ hj
    rw [testField_apply, show toL2 (IsTestField.single i hg j) = 0 from ?_, inner_zero_right]
    rw [← toL2_zero (Ω := Ω)]
    exact toL2_congr _ _ (by simp [hj])
  · simp

theorem L2F.ext_of_forall_inner_testField (hΩ : IsOpen Ω) {ι : Type*} [Fintype ι]
    {u v : L2F 𝕜 Ω ι}
    (h : ∀ φ : ι → E → 𝕜, ∀ hφ : IsTestField Ω φ, ⟪u, testField hφ⟫_𝕜 = ⟪v, testField hφ⟫_𝕜) :
    u = v :=
  sub_eq_zero.1 (L2F.eq_zero_of_forall_inner_testField hΩ _ fun φ hφ => by
    rw [inner_sub_left, h φ hφ, sub_self])

/-- **`C_c^∞(Ω; 𝕜^ι)` is dense in `L²(Ω; 𝕜^ι)`** (`Ω` open, bounded or not). -/
theorem dense_testFieldSub (hΩ : IsOpen Ω) (ι : Type*) [Fintype ι] :
    Dense (testFieldSub 𝕜 Ω ι : Set (L2F 𝕜 Ω ι)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro v hv
  refine L2F.eq_zero_of_forall_inner_testField hΩ v fun φ hφ => ?_
  exact (Submodule.mem_orthogonal' _ _).1 hv _ (testField_mem_testFieldSub hφ)

end Density

/-! ## Continuous functions on bounded domains -/

section Bounded

variable [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [IsFiniteMeasureOnCompacts (volume : Measure E)] {Ω : Set E}

/-- On a bounded `Ω`, continuous functions on `E` are in `L²(Ω)`. -/
theorem memLp_of_continuous (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    {F : Type*} [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) :
    MemLp f 2 (volume.restrict Ω) := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  have : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.2 (hb.measure_lt_top).ne
  obtain ⟨C, hC⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C
    (ae_restrict_of_forall_mem hΩ fun x hx => hC x (subset_closure hx))

end Bounded

/-! ## The Bochner model -/

section Bochner

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) {𝕜 : Type*} [RCLike 𝕜]
  (ι : Type*) [Fintype ι]

/-- Componentwise map `L²(μ; 𝕜^ι) → ⊕ₗ² L²(μ; 𝕜)`. -/
def toPiL2 : Lp (EuclideanSpace 𝕜 ι) 2 μ →ₗ[𝕜] PiLp 2 (fun _ : ι => Lp 𝕜 2 μ) :=
  (WithLp.linearEquiv 2 𝕜 (ι → Lp 𝕜 2 μ)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun i =>
      ((EuclideanSpace.proj i : EuclideanSpace 𝕜 ι →L[𝕜] 𝕜).compLpL 2 μ).toLinearMap

variable {μ ι}

theorem toPiL2_apply (f : Lp (EuclideanSpace 𝕜 ι) 2 μ) (i : ι) :
    (toPiL2 μ ι f i : α → 𝕜) =ᵐ[μ] fun x => f x i := by
  change ((EuclideanSpace.proj i : EuclideanSpace 𝕜 ι →L[𝕜] 𝕜).compLp f : α → 𝕜) =ᵐ[μ] _
  filter_upwards [(EuclideanSpace.proj i : EuclideanSpace 𝕜 ι →L[𝕜] 𝕜).coeFn_compLp f] with x hx
  rw [hx]
  rfl

theorem inner_toPiL2 (f g : Lp (EuclideanSpace 𝕜 ι) 2 μ) :
    ⟪toPiL2 μ ι f, toPiL2 μ ι g⟫_𝕜 = ⟪f, g⟫_𝕜 := by
  rw [PiLp.inner_apply, L2.inner_def]
  simp only [L2.inner_def]
  rw [← integral_finsetSum]
  · refine integral_congr_ae ?_
    have h1 := ae_all_iff.2 fun i => toPiL2_apply f i
    have h2 := ae_all_iff.2 fun i => toPiL2_apply g i
    filter_upwards [h1, h2] with x hx hy
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx i, hy i]
  · exact fun i _ => L2.integrable_inner _ _

theorem toPiL2_surjective : Function.Surjective (toPiL2 μ ι (𝕜 := 𝕜)) := by
  intro g
  have hm : MemLp (fun x => (WithLp.toLp 2 fun i => g i x : EuclideanSpace 𝕜 ι)) 2 μ :=
    MemLp.of_eval_piLp fun i => Lp.memLp (g i)
  refine ⟨hm.toLp _, (WithLp.ext_iff 2).2 (funext fun i => Lp.ext ?_)⟩
  filter_upwards [toPiL2_apply (hm.toLp _) i, hm.coeFn_toLp] with x h1 h2
  rw [h1, h2]

variable (μ ι 𝕜) in
/-- **Bochner bridge** `L²(μ; 𝕜^ι) ≃ₗᵢ ⊕ₗ²_{i ∈ ι} L²(μ; 𝕜)`, componentwise, for any measure. -/
def piL2Equiv : Lp (EuclideanSpace 𝕜 ι) 2 μ ≃ₗᵢ[𝕜] PiLp 2 (fun _ : ι => Lp 𝕜 2 μ) :=
  LinearIsometryEquiv.ofSurjective
    (LinearMap.isometryOfInner (toPiL2 μ ι (𝕜 := 𝕜)) (inner_toPiL2 (𝕜 := 𝕜)))
    (toPiL2_surjective (𝕜 := 𝕜))

end Bochner

end Feec.Domain
