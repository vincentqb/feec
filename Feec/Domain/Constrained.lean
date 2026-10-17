module

public import Feec.Domain.Complexes

/-!
# Realizations along isometric embeddings: constrained and scalar fields

Many operators of the bounded-domain models act between **constrained** field spaces: `curl` on
symmetric matrix fields with trace-free values, the Hessian of a scalar field with symmetric
values, `div div` on symmetric fields. They are realizations of a constant-coefficient operator
`A : 𝕜^ι → 𝕜^κ` between Hilbert spaces `X ↪ L²(Ω; 𝕜^ι)`, `Y ↪ L²(Ω; 𝕜^κ)` embedded
isometrically (`Jx`, `Jy`): closed subspaces (`Submodule.subtypeₗᵢ`), scalar fields
(`L2.toL2F`), or the whole space.

* `ConstCoeffOp.testGraphVia A Jx Jy`: `{(x, y) | Jx x = φ, Jy y = A φ, φ ∈ C_c^∞}`;
* `ConstCoeffOp.minimalVia A Jx Jy`: its closure, closed when the `Y`-valued test fields are
  dense in `Y` (`ConstCoeffOp.DenseVia`), densely defined when the `X`-valued test fields in its
  domain are dense in `X`;
* `minimalVia_graph_map`: `Jy (A_via x) = A_min (Jx x)`, i.e. `A_via ⊆ A_min` through the
  embeddings;
* `mem_adjoint_minimalVia_domain_iff`: `D(A_via†)` is the weak domain tested against the
  constrained test fields (no boundary condition);
* `Submodule.comap_topologicalClosure_map`: the closure of a graph may be taken in the ambient
  space and pulled back (the form used by the hand-built closures of the models).

## References

* [Arnold2018], §6.2; [AFW2010], §2 (complexes with values in subspaces of matrices)
-/

open scoped InnerProductSpace ContDiff ENNReal ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology

@[expose] public noncomputable section

/-- **Closures commute with closed linear embeddings**: for a linear map `L : M → N` that is a
closed embedding and a submodule `G ⊆ M`, `L⁻¹ (cl (L G)) = cl G`. -/
theorem Submodule.comap_topologicalClosure_map {𝕜 M N : Type*} [RCLike 𝕜]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] [NormedAddCommGroup N] [NormedSpace 𝕜 N]
    (L : M →ₗ[𝕜] N) (hL : IsClosedEmbedding L) (G : Submodule 𝕜 M) :
    (G.map L).topologicalClosure.comap L = G.topologicalClosure := by
  ext x
  change L x ∈ ((G.map L).topologicalClosure : Set N) ↔ x ∈ (G.topologicalClosure : Set M)
  rw [Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe, Submodule.map_coe,
    hL.closure_image_eq]
  exact hL.injective.mem_set_image

/-- The adjoint identity on a graph point: `⟪T† y, x⟫ = ⟪y, z⟫` for `(x, z) ∈ graph T`. -/
theorem LinearPMap.adjoint_inner_of_mem_graph {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E)) (y : T†.domain) {p : E × F}
    (hp : p ∈ T.graph) : ⟪T† y, p.1⟫_𝕜 = ⟪(y : F), p.2⟫_𝕜 := by
  obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).1 hp
  rw [← hx1, ← hx2]
  exact LinearPMap.adjoint_isFormalAdjoint hT y x

namespace Feec.Domain

/-! ## Scalar fields as one-component fields -/

section Scalar

variable {E : Type*} [MeasureSpace E] {𝕜 : Type*} [RCLike 𝕜] {Ω : Set E}

variable (𝕜 Ω) in
/-- `L²(Ω; 𝕜) ≃ L²(Ω; 𝕜^{Unit})`: a scalar field as a one-component field. -/
def L2.toL2F : L2 𝕜 Ω →ₗᵢ[𝕜] L2F 𝕜 Ω Unit :=
  LinearMap.isometryOfInner
    { toFun := fun u => WithLp.toLp 2 fun _ => u
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    fun u v => by simp [PiLp.inner_apply]; rfl

@[simp] theorem L2.toL2F_apply (u : L2 𝕜 Ω) (i : Unit) : L2.toL2F 𝕜 Ω u i = u := rfl

theorem L2.toL2F_surjective : Function.Surjective (L2.toL2F 𝕜 Ω) := fun v =>
  ⟨v (), (WithLp.ext_iff 2).2 (funext fun _ => rfl)⟩

end Scalar

namespace ConstCoeffOp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
  {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ] {Ω : Set E}
  {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
  (A : ConstCoeffOp E 𝕜 ι κ) (Jx : X →ₗᵢ[𝕜] L2F 𝕜 Ω ι) (Jy : Y →ₗᵢ[𝕜] L2F 𝕜 Ω κ)

/-- The constrained test graph `{(x, y) | Jx x = φ, Jy y = A φ, φ ∈ C_c^∞(Ω)}`. -/
def testGraphVia : Submodule 𝕜 (X × Y) where
  carrier := {p | ∃ φ : ι → E → 𝕜, ∃ hφ : IsTestField Ω φ,
    Jx p.1 = testField hφ ∧ Jy p.2 = testField (A.isTestField_apply hφ)}
  zero_mem' := ⟨0, IsTestField.zero, by
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
    exact ⟨testField_zero.symm, by
      rw [testField_congr _ IsTestField.zero A.apply_zero, testField_zero]⟩⟩
  add_mem' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨φ, hφ, h1, h2⟩ ⟨ψ, hψ, h1', h2'⟩
    simp only at h1 h1' h2 h2'
    refine ⟨φ + ψ, hφ.add hψ, ?_, ?_⟩
    · rw [Prod.fst_add, map_add, h1, h1', testField_add]
    · rw [Prod.snd_add, map_add, h2, h2', testField_congr _ ((A.isTestField_apply hφ).add
        (A.isTestField_apply hψ))
        (A.apply_add (fun i => (hφ i).contDiff) fun i => (hψ i).contDiff), testField_add]
  smul_mem' := by
    rintro c ⟨x, y⟩ ⟨φ, hφ, h1, h2⟩
    simp only at h1 h2
    refine ⟨c • φ, hφ.smul c, ?_, ?_⟩
    · rw [Prod.smul_fst, map_smul, h1, testField_smul]
    · rw [Prod.smul_snd, map_smul, h2, testField_congr _ ((A.isTestField_apply hφ).smul c)
        (A.apply_smul c fun i => (hφ i).contDiff), testField_smul]

/-- The constrained test elements of `Y` are dense: `y ⊥ Jy⁻¹ (C_c^∞)` forces `y = 0`. -/
def DenseVia (Jy : Y →ₗᵢ[𝕜] L2F 𝕜 Ω κ) : Prop :=
  ∀ y : Y, (∀ (ψ : κ → E → 𝕜) (hψ : IsTestField Ω ψ) (y' : Y), Jy y' = testField hψ →
    ⟪y', y⟫_𝕜 = 0) → y = 0

/-- The graph-closure identity through the embeddings: for `(x, y)` in the closure of the
constrained test graph and `y' ∈ Y` with `Jy y' = ψ ∈ C_c^∞`, `⟪y', y⟫ = ⟪Aᵗ ψ, Jx x⟫`. -/
theorem closure_testGraphVia_inner {p : X × Y} (hp : p ∈ (A.testGraphVia Jx Jy).topologicalClosure)
    {ψ : κ → E → 𝕜} (hψ : IsTestField Ω ψ) {y' : Y} (hy' : Jy y' = testField hψ) :
    ⟪y', p.2⟫_𝕜 = ⟪testField (A.formalAdj.isTestField_apply hψ), Jx p.1⟫_𝕜 := by
  let S : Set (X × Y) := {q | ⟪y', q.2⟫_𝕜 = ⟪testField (A.formalAdj.isTestField_apply hψ), Jx
      q.1⟫_𝕜}
  have hS : IsClosed S := isClosed_eq (continuous_const.inner continuous_snd)
    (continuous_const.inner (Jx.continuous.comp continuous_fst))
  have hsub : (A.testGraphVia Jx Jy : Set (X × Y)) ⊆ S := by
    rintro ⟨x, y⟩ ⟨φ, hφ, h1, h2⟩
    change ⟪y', y⟫_𝕜 = _
    rw [← Jy.inner_map_map, hy', h2, h1, ← inner_conj_symm,
      A.inner_testField_apply_testField hφ hψ, inner_conj_symm]
  exact closure_minimal hsub hS hp

theorem testGraphVia_closable (hY : DenseVia Jy) :
    ∀ p ∈ (A.testGraphVia Jx Jy).topologicalClosure, p.1 = 0 → p.2 = 0 := by
  rintro ⟨x, y⟩ hp (h0 : x = 0)
  subst h0
  refine hY y fun ψ hψ y' hy' => ?_
  rw [A.closure_testGraphVia_inner Jx Jy hp hψ hy']
  simp

/-- The **constrained minimal realization** `A_via : X → Y`, the closure of `A` on the
constrained test fields. -/
def minimalVia : X →ₗ.[𝕜] Y := (A.testGraphVia Jx Jy).topologicalClosure.toLinearPMap

theorem minimalVia_graph (hY : DenseVia Jy) :
    (A.minimalVia Jx Jy).graph = (A.testGraphVia Jx Jy).topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ (A.testGraphVia_closable Jx Jy hY)

theorem mem_closure_minimalVia (hY : DenseVia Jy) (x : (A.minimalVia Jx Jy).domain) :
    ((x : X), A.minimalVia Jx Jy x) ∈ (A.testGraphVia Jx Jy).topologicalClosure :=
  Submodule.mem_graph_toLinearPMap (A.testGraphVia_closable Jx Jy hY) x

theorem isClosed_minimalVia (hY : DenseVia Jy) : (A.minimalVia Jx Jy).IsClosed := by
  rw [LinearPMap.IsClosed, A.minimalVia_graph Jx Jy hY]
  exact Submodule.isClosed_topologicalClosure _

theorem mem_graph_minimalVia (hY : DenseVia Jy) {p : X × Y} (hp : p ∈ A.testGraphVia Jx Jy) :
    p ∈ (A.minimalVia Jx Jy).graph := by
  rw [A.minimalVia_graph Jx Jy hY]
  exact Submodule.le_topologicalClosure _ hp

theorem dense_minimalVia_domain (hY : DenseVia Jy)
    (hX : Dense {x : X | ∃ y : Y, (x, y) ∈ A.testGraphVia Jx Jy}) :
    Dense ((A.minimalVia Jx Jy).domain : Set X) :=
  hX.mono fun x hx => by
    obtain ⟨y, h⟩ := hx
    exact LinearPMap.mem_domain_of_mem_graph (A.mem_graph_minimalVia Jx Jy hY h)

/-- The constrained realization is densely defined when the `X`-valued test fields are dense
and `A` maps them to `Y`-valued test fields. -/
theorem dense_minimalVia_domain_of [CompleteSpace X] (hY : DenseVia Jy) (hX : DenseVia Jx)
    (hA : ∀ (φ : ι → E → 𝕜) (hφ : IsTestField Ω φ) (x : X), Jx x = testField hφ →
      ∃ y : Y, Jy y = testField (A.isTestField_apply hφ)) :
    Dense ((A.minimalVia Jx Jy).domain : Set X) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro z hz
  refine hX z fun φ hφ x hx => ?_
  obtain ⟨y, hy⟩ := hA φ hφ x hx
  exact (Submodule.mem_orthogonal' _ _).1 hz x
    (LinearPMap.mem_domain_of_mem_graph (A.mem_graph_minimalVia Jx Jy hY ⟨φ, hφ, hx, hy⟩))
    |> fun h => by rwa [inner_eq_zero_symm] at h

/-- **`A_via ⊆ A_min` through the embeddings**: `Jx x ∈ D(A_min)` and `A_min (Jx x) = Jy (A_via
x)`. -/
theorem minimalVia_graph_map (hΩ : IsOpen Ω) (hY : DenseVia Jy) (x : (A.minimalVia Jx Jy).domain) :
    (Jx x, Jy (A.minimalVia Jx Jy x)) ∈ (A.minimal Ω).graph := by
  rw [A.minimal_graph hΩ]
  let f : X × Y →L[𝕜] L2F 𝕜 Ω ι × L2F 𝕜 Ω κ :=
    (Jx.toContinuousLinearMap.comp (ContinuousLinearMap.fst 𝕜 X Y)).prod
      (Jy.toContinuousLinearMap.comp (ContinuousLinearMap.snd 𝕜 X Y))
  have hsub : (A.testGraphVia Jx Jy : Set (X × Y)) ⊆
      f ⁻¹' ((A.testGraph Ω).topologicalClosure : Set _) := by
    rintro ⟨x', y'⟩ ⟨φ, hφ, h1, h2⟩
    refine Submodule.le_topologicalClosure _ ⟨φ, hφ, ?_⟩
    simp only [f, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      LinearIsometry.coe_toContinuousLinearMap, h1, h2]
  exact closure_minimal hsub ((Submodule.isClosed_topologicalClosure _).preimage f.continuous)
    (A.mem_closure_minimalVia Jx Jy hY x)

/-- **The adjoint of a constrained realization is weak**: `v ∈ D(A_via†)` iff there is `w ∈ X`
with `⟪w, x⟫ = ⟪v, y⟫` for every constrained test pair `(x, y)`. -/
theorem mem_adjoint_minimalVia_domain_iff [CompleteSpace X] (hY : DenseVia Jy)
    (hd : Dense ((A.minimalVia Jx Jy).domain : Set X)) {v : Y} :
    v ∈ (A.minimalVia Jx Jy)†.domain ↔
      ∃ w : X, ∀ p ∈ A.testGraphVia Jx Jy, ⟪w, p.1⟫_𝕜 = ⟪v, p.2⟫_𝕜 := by
  constructor
  · rintro hv
    refine ⟨(A.minimalVia Jx Jy)† ⟨v, hv⟩, fun p hp => ?_⟩
    obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).1 (A.mem_graph_minimalVia Jx Jy hY hp)
    have := LinearPMap.adjoint_isFormalAdjoint hd ⟨v, hv⟩ x
    rw [hx1, hx2] at this
    exact this
  · rintro ⟨w, hw⟩
    refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨w, fun x => ?_⟩
    let S : Set (X × Y) := {q | ⟪w, q.1⟫_𝕜 = ⟪v, q.2⟫_𝕜}
    have hS : IsClosed S := isClosed_eq (continuous_const.inner continuous_fst)
      (continuous_const.inner continuous_snd)
    exact closure_minimal (fun q hq => hw q hq) hS (A.mem_closure_minimalVia Jx Jy hY x)

/-- The value of `A_via†` is the weak one. -/
theorem adjoint_minimalVia_apply_eq [CompleteSpace X] (hY : DenseVia Jy)
    (hd : Dense ((A.minimalVia Jx Jy).domain : Set X)) (v : (A.minimalVia Jx Jy)†.domain)
    {w : X} (hw : ∀ p ∈ A.testGraphVia Jx Jy, ⟪w, p.1⟫_𝕜 = ⟪(v : Y), p.2⟫_𝕜) :
    (A.minimalVia Jx Jy)† v = w := by
  refine LinearPMap.adjoint_apply_eq hd v fun x => ?_
  let S : Set (X × Y) := {q | ⟪w, q.1⟫_𝕜 = ⟪(v : Y), q.2⟫_𝕜}
  have hS : IsClosed S := isClosed_eq (continuous_const.inner continuous_fst)
    (continuous_const.inner continuous_snd)
  exact closure_minimal (fun q hq => hw q hq) hS (A.mem_closure_minimalVia Jx Jy hY x)

/-! ### Complexes of constrained realizations -/

section Complex

variable {μ : Type*} [Fintype μ] {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace 𝕜 Z]
  {B : ConstCoeffOp E 𝕜 κ μ} (Jz : Z →ₗᵢ[𝕜] L2F 𝕜 Ω μ)

/-- `R(A_via) ⊆ D(B_via)` and `B_via A_via = 0` when `B A = 0` and `A` maps `X`-valued test
fields to `Y`-valued ones. -/
theorem minimalVia_graph_mem (hAB : A.IsComplexPair B) (hY : DenseVia Jy)
    (hZ : DenseVia Jz) (x : (A.minimalVia Jx Jy).domain) :
    (A.minimalVia Jx Jy x, (0 : Z)) ∈ (B.minimalVia Jy Jz).graph := by
  let S : Set (X × Y) := {p | (p.2, (0 : Z)) ∈ (B.minimalVia Jy Jz).graph}
  have hS : IsClosed S :=
    (B.isClosed_minimalVia Jy Jz hZ).preimage (continuous_snd.prodMk continuous_const)
  have hsub : (A.testGraphVia Jx Jy : Set (X × Y)) ⊆ S := by
    rintro ⟨x', y'⟩ ⟨φ, hφ, h1, h2⟩
    refine B.mem_graph_minimalVia Jy Jz hZ ⟨A.apply φ, A.isTestField_apply hφ, h2, ?_⟩
    rw [map_zero, testField_congr _ IsTestField.zero (hAB φ fun i => (hφ i).contDiff),
      testField_zero]
  exact closure_minimal hsub hS (A.mem_closure_minimalVia Jx Jy hY x)

theorem minimalVia_mapsTo (hAB : A.IsComplexPair B) (hY : DenseVia Jy)
    (hZ : DenseVia Jz) (x : (A.minimalVia Jx Jy).domain) :
    (A.minimalVia Jx Jy x : Y) ∈ (B.minimalVia Jy Jz).domain :=
  LinearPMap.mem_domain_of_mem_graph (minimalVia_graph_mem A Jx Jy Jz hAB hY hZ x)

theorem minimalVia_comp (hAB : A.IsComplexPair B) (hY : DenseVia Jy)
    (hZ : DenseVia Jz) (x : (A.minimalVia Jx Jy).domain) :
    B.minimalVia Jy Jz ⟨_, minimalVia_mapsTo A Jx Jy Jz hAB hY hZ x⟩ = 0 :=
  ((LinearPMap.image_iff _).2 (minimalVia_graph_mem A Jx Jy Jz hAB hY hZ x)).symm

end Complex

/-! ### Density of constrained test fields -/

/-- **Constrained test fields are dense** when the constraint is the range of a self-adjoint
continuous `P` preserving test fields: if `P u ∈ R(J)`, `P (J y) = J y`, `⟪P u, v⟫ = ⟪u, P v⟫`
and `P` maps test fields to test fields, then the `Y`-valued test fields are dense in `Y`. -/
theorem denseVia_of_proj (hΩ : IsOpen Ω) (J : Y →ₗᵢ[𝕜] L2F 𝕜 Ω κ) (P : L2F 𝕜 Ω κ →L[𝕜] L2F 𝕜 Ω κ)
    (hPJ : ∀ y, P (J y) = J y) (hPsa : ∀ u v, ⟪P u, v⟫_𝕜 = ⟪u, P v⟫_𝕜)
    (hPt : ∀ (ψ : κ → E → 𝕜) (hψ : IsTestField Ω ψ), ∃ (ψ' : κ → E → 𝕜) (hψ' : IsTestField Ω ψ')
      (y' : Y), P (testField hψ) = testField hψ' ∧ J y' = testField hψ') :
    DenseVia J := by
  intro y hy
  have h0 : J y = 0 := by
    refine L2F.eq_zero_of_forall_inner_testField hΩ (J y) fun ψ hψ => ?_
    obtain ⟨ψ', hψ', y', hP, hJ⟩ := hPt ψ hψ
    have := hy ψ' hψ' y' hJ
    rw [← J.inner_map_map, hJ, ← hP, hPsa, hPJ] at this
    rw [← inner_conj_symm, this, map_zero]
  exact J.injective (by rw [h0, map_zero])

/-- **Surjective embeddings have dense test fields** (e.g. the identity, `L2.toL2F`, or a
reindexing of components). -/
theorem denseVia_of_surjective (hΩ : IsOpen Ω) (J : Y →ₗᵢ[𝕜] L2F 𝕜 Ω κ)
    (hJ : Function.Surjective J) : DenseVia J := by
  intro y hy
  have h0 : J y = 0 := by
    refine L2F.eq_zero_of_forall_inner_testField hΩ (J y) fun ψ hψ => ?_
    obtain ⟨y', hy'⟩ := hJ (testField hψ)
    have := hy ψ hψ y' hy'
    rw [← J.inner_map_map, hy'] at this
    rw [← inner_conj_symm, this, map_zero]
  exact J.injective (by rw [h0, map_zero])

/-- **The adjoint of a constrained realization through the ambient adjoint**: if
`Jy v ∈ D((A_min)†)` and `w ∈ X` represents `(A_min)† (Jy v)` along `Jx` (for a closed subspace
`X`, its orthogonal projection), then `v ∈ D(A_via†)` and `A_via† v = w`. -/
theorem adjoint_minimalVia_of_mem [CompleteSpace X] (hΩ : IsOpen Ω) (hY : DenseVia Jy)
    (hd : Dense ((A.minimalVia Jx Jy).domain : Set X)) {v : Y}
    (hv : Jy v ∈ (A.minimal Ω)†.domain) {w : X}
    (hw : ∀ x : X, ⟪w, x⟫_𝕜 = ⟪(A.minimal Ω)† ⟨Jy v, hv⟩, Jx x⟫_𝕜) :
    ∃ h : v ∈ (A.minimalVia Jx Jy)†.domain, (A.minimalVia Jx Jy)† ⟨v, h⟩ = w := by
  have key : ∀ x : (A.minimalVia Jx Jy).domain,
      ⟪w, (x : X)⟫_𝕜 = ⟪v, A.minimalVia Jx Jy x⟫_𝕜 := by
    intro x
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 (A.minimalVia_graph_map Jx Jy hΩ hY x)
    simp only at hy1 hy2
    have e := LinearPMap.adjoint_isFormalAdjoint (A.dense_minimal_domain hΩ) ⟨Jy v, hv⟩ y
    rw [hw, ← hy1, e, hy2]
    exact Jy.inner_map_map _ _
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨w, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq hd ⟨v, hmem⟩ key⟩

/-- **`A_via ≤ A_min` read on values**: `A_min (Jx x) = Jy (A_via x)`. -/
theorem minimal_apply_minimalVia (hΩ : IsOpen Ω) (hY : DenseVia Jy)
    (x : (A.minimalVia Jx Jy).domain) (h : Jx x ∈ (A.minimal Ω).domain) :
    A.minimal Ω ⟨Jx x, h⟩ = Jy (A.minimalVia Jx Jy x) := by
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 (A.minimalVia_graph_map Jx Jy hΩ hY x)
  simp only at hy1 hy2
  rw [← hy2]
  congr 1
  exact Subtype.ext hy1.symm

end ConstCoeffOp

end Feec.Domain
