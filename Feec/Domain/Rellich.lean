module

public import Feec.Domain.Affine
public import Feec.HilbertComplex.EigenDenseKernel

/-!
# Rellich compactness passes to subdomains and to affine images

For a constant-coefficient operator `A` (`Feec.Domain.ConstCoeffOp`) the compact embedding of
the minimal domain `D(A_min(Ω)) ↪ L²(Ω)` (`Feec.Operator.HasCompactBall (A.minimal Ω)`: the
unit box `‖u‖, ‖A u‖ ≤ 1` lies in a compact set) is

* **monotone in the domain** (`ConstCoeffOp.hasCompactBall_minimal_of_subset`): for open
  `Ω ⊆ Ω'` the extension by zero `L²(Ω) → L²(Ω')` (`extendZeroF`, an isometry) maps
  `D(A_min(Ω))` into `D(A_min(Ω'))` with `A_min(Ω') (ẽu) = (A_min(Ω) u)~`
  (`ConstCoeffOp.extendZeroF_mem_minimal`: `C_c^∞(Ω) ⊆ C_c^∞(Ω')`, then graph closure), and an
  isometry is a closed embedding;
* **invariant under affine changes of variables** for homogeneous `A`
  (`ConstCoeffOp.hasCompactBall_minimal_pull`, from `ConstCoeffOp.minimal_pull`).

The graph-closure step of the extension holds in general
(`ConstCoeffOp.mem_minimal_of_mapsTo_testGraph`): bounded maps sending test graphs to test graphs
send minimal domains to minimal domains. With the reindexing of components
(`compF`) the same lemma splits a field of `D(A_min)` into components (used for `H̊¹(Ω; ℝᵐ)` in
`Feec.Models.BoundedDomain.Compactness`).

Hence (`ConstCoeffOp.hasCompactBall_minimal_of_subset_preimage`) a compact embedding on one open
set `Ω'` gives one on every open `Ω ⊆ T⁻¹(Ω')`, `T x = a x + b`; in particular from the cube on
every bounded open set. This is the reduction of Rellich's theorem on bounded open sets to the
cube, [Evans2010], §5.7, Thm 1 (for `W₀^{1,p}` no regularity of `∂Ω` is needed); the cube itself
is treated in `Feec.Models.BoundedDomain.Compactness`.

## References

* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.7 (Rellich–Kondrachov)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.3 (Rellich's theorem), §9.4 (extension by zero of `W₀^{1,p}`)
-/

open scoped InnerProductSpace ENNReal Topology
open MeasureTheory Set Filter

@[expose] public noncomputable section

namespace Feec.Domain

variable {E : Type*} [MeasureSpace E] {𝕜 : Type*} [RCLike 𝕜] {Ω Ω' : Set E}

/-! ### Extension by zero between nested domains -/

section Extend

variable (hΩ : MeasurableSet Ω) (hsub : Ω ⊆ Ω')
include hΩ

theorem memLp_indicator_restrict (f : L2 𝕜 Ω) :
    MemLp (Ω.indicator (f : E → 𝕜)) 2 (volume.restrict Ω') :=
  ((memLp_indicator_iff_restrict hΩ.nullMeasurableSet).2 (Lp.memLp f)).restrict Ω'

/-- The extension by zero `L²(Ω) → L²(Ω')`. -/
def extendZero (f : L2 𝕜 Ω) : L2 𝕜 Ω' := (memLp_indicator_restrict hΩ f).toLp _

theorem coeFn_extendZero (f : L2 𝕜 Ω) :
    (extendZero (Ω' := Ω') hΩ f : E → 𝕜) =ᵐ[volume.restrict Ω'] Ω.indicator (f : E → 𝕜) :=
  (memLp_indicator_restrict hΩ f).coeFn_toLp

/-- An a.e. identity on `Ω` holds a.e. on `Ω'` for the extensions by zero. -/
theorem indicator_ae_eq_of_ae_eq {f g : E → 𝕜} (h : f =ᵐ[volume.restrict Ω] g) :
    Ω.indicator f =ᵐ[volume.restrict Ω'] Ω.indicator g := by
  refine ae_restrict_of_ae ?_
  filter_upwards [(ae_restrict_iff' hΩ).1 h] with x hx
  by_cases hxΩ : x ∈ Ω
  · rw [indicator_of_mem hxΩ, indicator_of_mem hxΩ, hx hxΩ]
  · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxΩ]

theorem extendZero_add (f g : L2 𝕜 Ω) :
    extendZero (Ω' := Ω') hΩ (f + g) = extendZero hΩ f + extendZero hΩ g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_extendZero hΩ (f + g), coeFn_extendZero (Ω' := Ω') hΩ f,
    coeFn_extendZero (Ω' := Ω') hΩ g, Lp.coeFn_add (extendZero (Ω' := Ω') hΩ f)
      (extendZero hΩ g), indicator_ae_eq_of_ae_eq (Ω' := Ω') hΩ (Lp.coeFn_add f g)]
    with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, h5]
  by_cases hx : x ∈ Ω <;> simp [hx]

theorem extendZero_smul (c : 𝕜) (f : L2 𝕜 Ω) :
    extendZero (Ω' := Ω') hΩ (c • f) = c • extendZero hΩ f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_extendZero hΩ (c • f), coeFn_extendZero (Ω' := Ω') hΩ f,
    Lp.coeFn_smul c (extendZero (Ω' := Ω') hΩ f),
    indicator_ae_eq_of_ae_eq (Ω' := Ω') hΩ (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h2, h4]
  by_cases hx : x ∈ Ω <;> simp [hx]

include hsub in
/-- **The extension by zero is an isometry.** -/
theorem norm_extendZero (f : L2 𝕜 Ω) : ‖extendZero (Ω' := Ω') hΩ f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_extendZero hΩ f),
    eLpNorm_indicator_eq_eLpNorm_restrict hΩ.nullMeasurableSet, Measure.restrict_restrict hΩ,
    inter_eq_left.2 hsub]

variable {ι : Type*} [Fintype ι]

/-- The extension by zero of fields `L²(Ω; 𝕜^ι) → L²(Ω'; 𝕜^ι)`, `Ω ⊆ Ω'`, a linear isometry. -/
def extendZeroF : L2F 𝕜 Ω ι →ₗᵢ[𝕜] L2F 𝕜 Ω' ι where
  toFun u := WithLp.toLp 2 fun i => extendZero hΩ (u i)
  map_add' u v := PiLp.ext fun i => extendZero_add hΩ (u i) (v i)
  map_smul' c u := PiLp.ext fun i => extendZero_smul hΩ c (u i)
  norm_map' u := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.toLp_apply, norm_extendZero hΩ hsub]

theorem extendZeroF_apply (u : L2F 𝕜 Ω ι) (i : ι) :
    extendZeroF (𝕜 := 𝕜) hΩ hsub u i = extendZero hΩ (u i) := rfl

end Extend

/-! ### Reindexing the components of a field -/

section Reindex

variable {ι ι' : Type*}

/-- **Reindexing of components** `L²(Ω; 𝕜^ι) → L²(Ω; 𝕜^ι')`, `(compF σ u)_j = u_{σ j}`. -/
def compF (σ : ι' → ι) : L2F 𝕜 Ω ι →L[𝕜] L2F 𝕜 Ω ι' :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι' => L2 𝕜 Ω)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun j => PiLp.proj 2 (fun _ : ι => L2 𝕜 Ω) (σ j)

theorem compF_apply (σ : ι' → ι) (u : L2F 𝕜 Ω ι) (j : ι') : compF σ u j = u (σ j) := rfl

end Reindex

section Test

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] {ι : Type*} [Fintype ι]

/-- The extension by zero of a test field of `Ω` is the same test field on `Ω'`. -/
theorem extendZeroF_testField (hΩ : MeasurableSet Ω) (hsub : Ω ⊆ Ω') {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) :
    extendZeroF hΩ hsub (testField hφ) = testField fun i => (hφ i).mono hsub := by
  refine PiLp.ext fun i => Lp.ext ?_
  rw [extendZeroF_apply]
  filter_upwards [coeFn_extendZero (Ω' := Ω') hΩ (testField hφ i),
    indicator_ae_eq_of_ae_eq (Ω' := Ω') hΩ (coeFn_testField hφ i),
    coeFn_testField (fun i => (hφ i).mono hsub) i] with x h1 h2 h3
  rw [h1, h2, h3]
  by_cases hx : x ∈ Ω
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, (hφ i).eq_zero_of_notMem hx]

omit [Fintype ι] in
/-- The reindexing of a test field is the reindexed test field. -/
theorem compF_testField {ι' : Type*} (σ : ι' → ι)
    {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) :
    compF σ (testField hφ) = testField (φ := fun j => φ (σ j)) fun j => hφ (σ j) := rfl

end Test



/-! ### The minimal realization under extension by zero -/

namespace ConstCoeffOp

open Feec.Operator

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] {ι κ : Type*} [Fintype ι] [Fintype κ] (A : ConstCoeffOp E 𝕜 ι κ)

/-- **Extension by zero maps `D(A_min(Ω))` into `D(A_min(Ω'))`** for open `Ω ⊆ Ω'`, commuting
with `A`: the test graph of `Ω` maps into the test graph of `Ω'`, and the extension is
continuous. -/
theorem extendZeroF_mem_minimal (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hsub : Ω ⊆ Ω')
    (u : (A.minimal Ω).domain) :
    ∃ h : extendZeroF hΩ.measurableSet hsub (u : L2F 𝕜 Ω ι) ∈ (A.minimal Ω').domain,
      A.minimal Ω' ⟨_, h⟩ = extendZeroF hΩ.measurableSet hsub (A.minimal Ω u) := by
  set J := extendZeroF (𝕜 := 𝕜) (ι := ι) hΩ.measurableSet hsub
  set J' := extendZeroF (𝕜 := 𝕜) (ι := κ) hΩ.measurableSet hsub
  set Φ : L2F 𝕜 Ω ι × L2F 𝕜 Ω κ → L2F 𝕜 Ω' ι × L2F 𝕜 Ω' κ := Prod.map J J'
  have hΦ : Continuous Φ := J.continuous.prodMap J'.continuous
  have hmaps : MapsTo Φ (A.testGraph Ω : Set _) (A.testGraph Ω' : Set _) := by
    rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨φ, fun i => (hφ i).mono hsub, ?_⟩
    change (J (testField hφ), J' (testField (A.isTestField_apply hφ))) = _
    rw [extendZeroF_testField, extendZeroF_testField]
  have hmem := A.mem_closure_minimal hΩ u
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hmem
  have hgr : Φ ((u : L2F 𝕜 Ω ι), A.minimal Ω u) ∈ (A.minimal Ω').graph := by
    rw [A.minimal_graph hΩ', ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact map_mem_closure hΦ hmem hmaps
  exact ⟨LinearPMap.mem_domain_of_mem_graph hgr,
    ((LinearPMap.image_iff (LinearPMap.mem_domain_of_mem_graph hgr)).2 hgr).symm⟩

/-- **Minimal domains along maps of test graphs**: continuous linear maps `Φ`, `Ψ` sending the
test graph of `A` on `Ω` into the test graph of `B` on `Ω'` send `D(A_min(Ω))` into
`D(B_min(Ω'))`, with `B_min (Φ u) = Ψ (A_min u)` (graph closure). -/
theorem mem_minimal_of_mapsTo_testGraph {ι' κ' : Type*} [Fintype ι'] [Fintype κ']
    {B : ConstCoeffOp E 𝕜 ι' κ'} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (Φ : L2F 𝕜 Ω ι →L[𝕜] L2F 𝕜 Ω' ι') (Ψ : L2F 𝕜 Ω κ →L[𝕜] L2F 𝕜 Ω' κ')
    (hmaps : ∀ (φ : ι → E → 𝕜) (hφ : IsTestField Ω φ),
      (Φ (testField hφ), Ψ (testField (A.isTestField_apply hφ))) ∈ B.testGraph Ω')
    (u : (A.minimal Ω).domain) :
    ∃ h : Φ u ∈ (B.minimal Ω').domain, B.minimal Ω' ⟨_, h⟩ = Ψ (A.minimal Ω u) := by
  set F : L2F 𝕜 Ω ι × L2F 𝕜 Ω κ → L2F 𝕜 Ω' ι' × L2F 𝕜 Ω' κ' := Prod.map Φ Ψ
  have hF : Continuous F := Φ.continuous.prodMap Ψ.continuous
  have hm : MapsTo F (A.testGraph Ω : Set _) (B.testGraph Ω' : Set _) := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact hmaps φ hφ
  have hmem := A.mem_closure_minimal hΩ u
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hmem
  have hgr : F ((u : L2F 𝕜 Ω ι), A.minimal Ω u) ∈ (B.minimal Ω').graph := by
    rw [B.minimal_graph hΩ', ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact map_mem_closure hF hmem hm
  exact ⟨LinearPMap.mem_domain_of_mem_graph hgr,
    ((LinearPMap.image_iff (LinearPMap.mem_domain_of_mem_graph hgr)).2 hgr).symm⟩

/-- **Compactness of the minimal domain is monotone in the domain**: for open `Ω ⊆ Ω'`, a
compact embedding `D(A_min(Ω')) ↪ L²(Ω')` gives one of `D(A_min(Ω)) ↪ L²(Ω)`. -/
theorem hasCompactBall_minimal_of_subset (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hsub : Ω ⊆ Ω')
    (h : HasCompactBall (A.minimal Ω')) : HasCompactBall (A.minimal Ω) := by
  set J := extendZeroF (𝕜 := 𝕜) (ι := ι) hΩ.measurableSet hsub
  refine h.of_isClosedEmbedding J.toContinuousLinearMap J.isometry.isClosedEmbedding zero_le_one
    fun x => ?_
  obtain ⟨hx, e⟩ := A.extendZeroF_mem_minimal hΩ hΩ' hsub x
  refine ⟨hx, ?_⟩
  change ‖A.minimal Ω' ⟨J x, hx⟩‖ ≤ 1 * ‖A.minimal Ω x‖
  rw [e, one_mul, LinearIsometry.norm_map]

variable {A}

/-- **Compactness of the minimal domain under affine maps**: for `A` homogeneous of order `r`,
`T x = a x + b` (`a ≠ 0`) and `Ω = T⁻¹(Ω')`, a compact embedding on `Ω'` gives one on `Ω`
(`A_min,Ω = a^r P A_min,Ω' P⁻¹`, `ConstCoeffOp.minimal_pull`). -/
theorem hasCompactBall_minimal_pull {r : ℕ} (hA : A.IsHomogeneous r) {a : ℝ} (ha : a ≠ 0)
    (b : E) (hΩo' : IsOpen Ω') (hT : aff a b ⁻¹' Ω' = Ω)
    (h : HasCompactBall (A.minimal Ω')) : HasCompactBall (A.minimal Ω) := by
  have hΩ' := hΩo'.measurableSet
  have hpull := minimal_pull hA ha b hΩ' hT hΩo'
  set e₁ := pullF (𝕜 := 𝕜) ha b hΩ' hT ι
  set e₂ := pullF (𝕜 := 𝕜) ha b hΩ' hT κ
  set κ0 : 𝕜 := ((a ^ r : ℝ) : 𝕜)
  have hκ : κ0 ≠ 0 := RCLike.ofReal_ne_zero.2 (pow_ne_zero r ha)
  refine h.of_isClosedEmbedding e₁.symm.toContinuousLinearMap
    e₁.symm.toHomeomorph.isClosedEmbedding (C := ‖κ0‖⁻¹ * ‖e₂.symm.toContinuousLinearMap‖)
    (by positivity) fun x => ?_
  obtain ⟨hx, ex⟩ := LinearPMap.exists_mem_apply_eq_of_eq hpull x
  refine ⟨hx, ?_⟩
  rw [LinearPMap.conjScaled_apply] at ex
  have e2 : A.minimal Ω' ⟨e₁.symm x, hx⟩ = κ0⁻¹ • e₂.symm (A.minimal Ω x) := by
    rw [← ex, _root_.map_smul, ContinuousLinearEquiv.symm_apply_apply, inv_smul_smul₀ hκ]
  change ‖A.minimal Ω' ⟨e₁.symm x, hx⟩‖ ≤ _
  rw [e2, norm_smul, norm_inv, mul_assoc]
  gcongr
  exact ContinuousLinearMap.le_opNorm e₂.symm.toContinuousLinearMap _

/-- **Compactness of the minimal domain on subdomains of affine images**: if
`D(A_min(Ω')) ↪ L²(Ω')` is compact and `Ω ⊆ T⁻¹(Ω')` is open (`T x = a x + b`, `a ≠ 0`, `A`
homogeneous), then `D(A_min(Ω)) ↪ L²(Ω)` is compact. -/
theorem hasCompactBall_minimal_of_subset_preimage {r : ℕ} (hA : A.IsHomogeneous r) {a : ℝ}
    (ha : a ≠ 0) (b : E) (hΩo : IsOpen Ω) (hΩo' : IsOpen Ω') (hsub : Ω ⊆ aff a b ⁻¹' Ω')
    (h : HasCompactBall (A.minimal Ω')) : HasCompactBall (A.minimal Ω) :=
  A.hasCompactBall_minimal_of_subset hΩo (hΩo'.preimage (continuous_aff a b)) hsub
    (hasCompactBall_minimal_pull hA ha b hΩo' rfl h)

end ConstCoeffOp

end Feec.Domain
