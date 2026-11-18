module

public import Solution.Box
public import Feec.Models.StarShaped.EigenDense
public import Feec.Counterexamples.BallEigenfields

/-!
# The grad–curl system with the electric boundary conditions: evolutions and invariant cores

The challenge's system (4.14) on an open `Ω` is `Feec.Models.BoundedDomain.gradCurl` through the
state map `gcState` (`gcWave_iff` of `Solution.Box`), and its graph is the graph of the generator
of the wave group (`gc_graph_iff`). So every evolution of the challenge's system is the wave
group conjugated by the state map (`gc_eq_of_isEvolution`, from `eq_group_of_isEvolution` of
`Solution.Engine`), and its invariant core is `Feec`'s `coreSub` (`gc_mem_invariantCore_iff`).
The electric and magnetic fields carry `L²(TSD)`, `L²(TSD₀)`, `H̊(curl)`, `H(curl)`, the adjoint of
the curl and the eigenfields to those of `Feec` (`mem_dom_iff`, `mem_domMax_iff`, `isTSD₀_iff`,
`isEigenfield_iff`), and the verdicts are those of `Feec.Counterexamples.BoundedDomainTSD`
(`electric_of`), `Feec.Models.BoundedDomain.not_coreSub_le_stationary_iff` with
`Feec.Models.StarShaped.StarDomain.eigenDense_gradCurl` (`starShaped_of`),
`Feec.Counterexamples.BallEigenfields.eq_zero_of_isEigenfield_of_contDiff_ball` (`ball_of`) and
`Feec.Counterexamples.BoxStationary.mem_invariantCore_tsd_iff_box` (`box_of`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 ((4.14), Prop 4.17)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set MeasureTheory Filter Topology

@[expose] public noncomputable section

namespace FEEC

open Feec Feec.Domain Feec.Models.BoundedDomain Feec.Counterexamples.BoundedDomainTSD
open Feec.HilbertComplex (totalSub)
open Feec.ShortHilbertComplex (W3 family3 mk3 mem_totalSub_family3 inj₁ inj₂)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-! ### Conjugate evolutions -/

section Conj

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] (Φ : X →L[ℝ] Y) {A : SetRel X X} {B : SetRel Y Y}

/-- A strong solution of `A` mapped by `Φ` is one of `B` if `Φ` maps `A` into `B`. -/
theorem IsStrongSolution.map (hAB : ∀ x v, (x, v) ∈ A → (Φ x, Φ v) ∈ B) {I : Set ℝ}
    {u : ℝ → X} (hu : IsStrongSolution A I u) : IsStrongSolution B I fun t => Φ (u t) :=
  ⟨Φ.continuous.comp_continuousOn hu.1, fun t ht => by
    obtain ⟨v, hv, hd⟩ := hu.2 t ht
    exact ⟨Φ v, hAB _ _ hv, Φ.hasFDerivAt.comp_hasDerivWithinAt t hd⟩⟩

/-- An evolution conjugated by mutually inverse maps carrying the graphs into each other. -/
theorem IsEvolution.conj (Ψ : Y →L[ℝ] X) (hΦΨ : ∀ y, Φ (Ψ y) = y)
    (hAB : ∀ x v, (x, v) ∈ A → (Φ x, Φ v) ∈ B) (hBA : ∀ y w, (y, w) ∈ B → (Ψ y, Ψ w) ∈ A)
    {I : Set ℝ} {S : ℝ → X →L[ℝ] X} (hS : IsEvolution ℝ A I S) :
    IsEvolution ℝ B I fun t => Φ ∘L S t ∘L Ψ :=
  ⟨fun y => by simp [hS.1, hΦΨ], fun y w hyw => (hS.2 _ _ (hBA _ _ hyw)).map Φ hAB⟩

end Conj

/-! ### Adjoints under unitary maps -/

section Adjoint

variable {E F E' F' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup E']
  [InnerProductSpace ℝ E'] [CompleteSpace E'] [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
  [CompleteSpace F']

omit [CompleteSpace F] in
/-- **The graph of the adjoint**: `T† y = z` iff `⟪z, x⟫ = ⟪y, T x⟫` on `D(T)`. -/
theorem mem_graph_adjoint_iff {T : E →ₗ.[ℝ] F} (hT : Dense (T.domain : Set E)) (y : F) (z : E) :
    (y, z) ∈ T†.graph ↔ ∀ x : T.domain, ⟪z, (x : E)⟫ = ⟪y, T x⟫ := by
  constructor
  · intro h x
    obtain ⟨hy, e⟩ := apply_of_mem_graph h
    rw [← e]
    exact LinearPMap.adjoint_isFormalAdjoint hT ⟨y, hy⟩ x
  · intro h
    have hy := LinearPMap.mem_adjoint_domain_of_exists y ⟨z, h⟩
    exact (LinearPMap.mem_graph_iff _).2
      ⟨⟨y, hy⟩, rfl, LinearPMap.adjoint_apply_eq hT ⟨y, hy⟩ h⟩

omit [CompleteSpace F] [CompleteSpace F'] in
/-- **Adjoints under unitary maps**: if `e`, `f` carry the graph of `T` onto that of `T'`, they
carry the graph of `T†` onto that of `T'†`. -/
theorem mem_graph_adjoint_iff_of (e : E ≃ₗᵢ[ℝ] E') (f : F ≃ₗᵢ[ℝ] F') {T : E →ₗ.[ℝ] F}
    {T' : E' →ₗ.[ℝ] F'} (hT : Dense (T.domain : Set E)) (hT' : Dense (T'.domain : Set E'))
    (h : ∀ x y, (x, y) ∈ T.graph ↔ (e x, f y) ∈ T'.graph) (y : F) (z : E) :
    (y, z) ∈ T†.graph ↔ (f y, e z) ∈ T'†.graph := by
  rw [mem_graph_adjoint_iff hT, mem_graph_adjoint_iff hT']
  constructor
  · intro H x'
    obtain ⟨hx, ex⟩ := apply_of_mem_graph ((h (e.symm x') (f.symm (T' x'))).2 (by simp))
    calc ⟪e z, (x' : E')⟫ = ⟪e z, e (e.symm x')⟫ := by rw [LinearIsometryEquiv.apply_symm_apply]
      _ = ⟪z, ((⟨_, hx⟩ : T.domain) : E)⟫ := LinearIsometryEquiv.inner_map_map e _ _
      _ = ⟪y, T ⟨_, hx⟩⟫ := H _
      _ = ⟪f y, T' x'⟫ := by rw [ex, ← LinearIsometryEquiv.inner_map_map f,
          LinearIsometryEquiv.apply_symm_apply]
  · intro H x
    obtain ⟨hx, ex⟩ := apply_of_mem_graph ((h x (T x)).1 (T.mem_graph x))
    calc ⟪z, (x : E)⟫ = ⟪e z, e x⟫ := (LinearIsometryEquiv.inner_map_map e _ _).symm
      _ = ⟪f y, T' ⟨_, hx⟩⟫ := H ⟨_, hx⟩
      _ = ⟪y, T x⟫ := by rw [ex, LinearIsometryEquiv.inner_map_map]

end Adjoint

/-! ### The grad–curl system -/

section GradCurl

variable {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω)

/-- The inverse of the state map. -/
abbrev gcInv : PiLp 2 (W3 (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix)) →L[ℝ]
    L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2 :=
  stateInvL field0 fieldE fieldB

omit hΩ in
theorem gcState_gcInv (y : PiLp 2 (W3 (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))) :
    gcState (gcInv y) = y :=
  stateL_stateInvL _ _ _ y

omit hΩ in
theorem gcInv_gcState (U : L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) : gcInv (gcState U) = U :=
  stateInvL_stateL _ _ _ U

/-- The wave group of `Feec`'s grad–curl complex. -/
abbrev gcGroup : C0Group ℝ (PiLp 2 (W3 (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))) :=
  (gradCurl ℝ hΩ).toHilbertComplex.waveGroup

/-- **The graph of the challenge's system is that of the generator**, through the state map. -/
theorem gc_graph_iff (U V : L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) :
    (U, V) ∈ gradCurlWave Ω ↔ (gcState U, gcState V) ∈ (gcGroup hΩ).generator.graph := by
  rw [HilbertComplex.generator_waveGroup, LinearPMap.mem_graph_iff]
  change gcWave U V ↔ _
  rw [gcWave_iff hΩ]
  constructor
  · rintro ⟨h, e⟩; exact ⟨⟨_, h⟩, rfl, e⟩
  · rintro ⟨y, hy, e⟩
    have hy' : (y : PiLp 2 (W3 (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))) = gcState U := hy
    refine ⟨hy' ▸ y.2, ?_⟩
    have hyy : (⟨gcState U, hy' ▸ y.2⟩ : (gradCurl ℝ hΩ).wave.domain) = y := Subtype.ext hy'.symm
    rw [hyy]; exact e

theorem gc_graph_inv (y w : PiLp 2 (W3 (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix)))
    (h : (y, w) ∈ (gcGroup hΩ).generator.graph) : (gcInv y, gcInv w) ∈ gradCurlWave Ω := by
  rw [gc_graph_iff hΩ, gcState_gcInv, gcState_gcInv]; exact h

/-- **The system (4.14) has an evolution**: the wave group conjugated by the state map. -/
theorem gc_isEvolution :
    IsEvolution ℝ (gradCurlWave Ω) univ fun t => gcInv ∘L (gcGroup hΩ).S t ∘L gcState :=
  (isEvolution_group (gcGroup hΩ)).conj gcInv gcState gcInv_gcState
    (fun y w h => gc_graph_inv hΩ y w h) fun U V h => (gc_graph_iff hΩ U V).1 h

/-- **Every evolution of the system (4.14) is the wave group**, through the state map. -/
theorem gc_eq_of_isEvolution {S : ℝ → (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) →L[ℝ]
    (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2)} (hS : IsEvolution ℝ (gradCurlWave Ω) univ S) (t : ℝ)
    (x : L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) :
    S t x = gcInv ((gcGroup hΩ).S t (gcState x)) := by
  have hS' := hS.conj gcState gcInv gcState_gcInv (fun U V h => (gc_graph_iff hΩ U V).1 h)
    fun y w h => gc_graph_inv hΩ y w h
  have e := eq_group_of_isEvolution (gcGroup hΩ) (gcGroup hΩ).dense_domain_generator hS'
  have e' := congrArg (fun S' : ℝ → _ →L[ℝ] _ => S' t (gcState x)) e
  simp only [ContinuousLinearMap.comp_apply, gcInv_gcState] at e'
  rw [← e', gcInv_gcState]

omit hΩ in
/-- **The constraint is `Feec`'s `{0} × L²(TSD) × L²(TSD)`**, through the state map. -/
theorem gc_mem_tsd_iff (W : L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) :
    gcState W ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ Ω (Fin 3))) (tsd Ω) (tsd Ω)) ↔
      W ∈ tsdConstraint Ω := by
  rw [mem_totalSub_family3]
  change -field0 W.1 ∈ (⊥ : Submodule ℝ (L2F ℝ Ω (Fin 3))) ∧ fieldE W.2.1 ∈ tsd Ω ∧
    fieldB W.2.2 ∈ tsd Ω ↔ _
  rw [Submodule.mem_bot, neg_eq_zero, LinearIsometryEquiv.map_eq_zero_iff]
  simp only [tsdConstraint, mem_ofPred_eq, isTSD_iff, toIx_mat1, toIx_mat2]

/-- **The invariant core is `Feec`'s `coreSub`**, through the state map. -/
theorem gc_mem_invariantCore_iff {S : ℝ → (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) →L[ℝ]
    (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2)} (hS : IsEvolution ℝ (gradCurlWave Ω) univ S)
    (x : L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) :
    x ∈ invariantCore S (tsdConstraint Ω) ↔
      gcState x ∈ (gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω) := by
  rw [ShortHilbertComplex.coreSub, C0Group.mem_invariantCore]
  simp only [invariantCore, mem_ofPred_eq, gc_eq_of_isEvolution hΩ hS, ← gc_mem_tsd_iff,
    gcState_gcInv]

/-- The stationary data of the system: `L U = 0`. -/
theorem gc_mem_stationary_iff (U : L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) :
    (U, 0) ∈ gradCurlWave Ω ↔ gcState U ∈ (gradCurl ℝ hΩ).stationary :=
  (gc_stationary hΩ U).symm

omit hΩ in
theorem gcState_apply_one (U : L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) :
    (gcState U 1 : L2F ℝ Ω Ix) = fieldE U.2.1 := rfl

omit hΩ in
theorem gcState_magnetic (ρ : L2Vec Ω 2) :
    gcState ((0, 0, ρ) : L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) =
      inj₂ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) (fieldB ρ) := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · change -field0 (0 : L2Vec Ω 0) = (0 : L2F ℝ Ω (Fin 3)); simp
  · change fieldE (0 : L2Vec Ω 1) = (0 : L2F ℝ Ω Ix); simp
  · rfl

/-- A magnetic datum `B ∈ D(d₁†)` with `d₁† B = 0` is stationary. -/
theorem inj₂_mem_stationary {B : L2F ℝ Ω Ix} (hB : B ∈ ((gradCurl ℝ hΩ).d₁†).domain)
    (h0 : (gradCurl ℝ hΩ).d₁† ⟨B, hB⟩ = 0) :
    inj₂ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) B ∈
      (gradCurl ℝ hΩ).stationary := by
  refine ShortHilbertComplex.mem_stationary_of_wave_eq_zero
    ⟨_, ShortHilbertComplex.inj₂_mem_wave_domain (S := gradCurl ℝ hΩ) hB⟩ ?_
  rw [ShortHilbertComplex.wave_inj₂ (S := gradCurl ℝ hΩ) ⟨B, hB⟩, h0, neg_zero, map_zero]

/-! ### Fields, domains, `L²(TSD₀)` and eigenfields -/

/-- **`H̊Λ¹(Ω)³` is `H̊(curl, Ω; ℝ³ˣ³)`** through the electric field. -/
theorem mem_dom_iff (u : L2Vec Ω 1) :
    u ∈ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain ↔
      fieldE u ∈ (gradCurl ℝ hΩ).d₁.domain := by
  constructor
  · intro h
    exact LinearPMap.mem_domain_of_mem_graph
      ((mem_graph_curl_iff hΩ u _).1 (LinearPMap.mem_graph _ ⟨u, h⟩))
  · intro h
    have hg := (gradCurl ℝ hΩ).d₁.mem_graph ⟨_, h⟩
    rw [← LinearIsometryEquiv.apply_symm_apply fieldB ((gradCurl ℝ hΩ).d₁ ⟨_, h⟩)] at hg
    exact LinearPMap.mem_domain_of_mem_graph ((mem_graph_curl_iff hΩ u _).2 hg)

include hΩ in
/-- **`HΛ¹(Ω)³` is `H(curl, Ω; ℝ³ˣ³)`** through the electric field: the rows of `curl E` are the
`d uₐ`, and the row-wise curl is formally self-adjoint (`curlOp_formalAdj_apply`), so its maximal
realization is that of its formal adjoint. -/
theorem mem_domMax_iff (u : L2Vec Ω 1) :
    u ∈ (vecOp fun _ => dMax Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain ↔
      fieldE u ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain := by
  constructor
  · intro h
    rw [fieldE_eq_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    have hu : u a ∈ ((extDerivOp ℝ 3 1).maximal Ω).domain := by rw [← dMax_eq]; exact h a
    exact (ConstCoeffOp.maximal_ofMatrixCLM_of_comm hΩ
      (A := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj) (B := extDerivOp ℝ 3 1)
      (M := matE a) (M' := matB a)
      (fun f _ => by rw [curlOp_formalAdj_apply]; exact curlOp_matE a f) ⟨_, hu⟩).1
  · intro h a
    have h' := (ConstCoeffOp.maximal_ofMatrixCLM_of_comm hΩ (A := extDerivOp ℝ 3 1)
      (B := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj) (M := (matE a).transpose)
      (M' := (matB a).transpose)
      (fun f _ => by rw [curlOp_formalAdj_apply]; exact extDerivOp_matE_transpose a f)
      ⟨_, h⟩).1
    rw [ofMatrixCLM_matE_transpose] at h'
    change u a ∈ (dMax Ω 1).domain
    rw [dMax_eq]; exact h'

/-- The curl through the fields: `curl (E u) = B (d u)`. -/
theorem curl_fieldE (u : (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain)
    (h : fieldE (u : L2Vec Ω 1) ∈ (gradCurl ℝ hΩ).d₁.domain) :
    (gradCurl ℝ hΩ).d₁ ⟨_, h⟩ = fieldB ((vecOp fun _ => dMin Ω 1) u) := by
  obtain ⟨h', e⟩ := apply_of_mem_graph
    ((mem_graph_curl_iff hΩ u _).1 (LinearPMap.mem_graph _ u))
  exact e

omit hΩ in
theorem toIx_injective : Function.Injective (toIx (Ω := Ω)) := fun E E' h => by
  funext a b
  exact congrArg (fun F : L2F ℝ Ω Ix => F (a, b)) h

omit hΩ in
theorem mat1_eq_mat2_iff (w : L2Vec Ω 1) (ρ : L2Vec Ω 2) : mat1 w = mat2 ρ ↔ fieldE w = fieldB ρ :=
  ⟨fun h => by rw [← toIx_mat1, ← toIx_mat2, h], fun h => toIx_injective (by
    rw [toIx_mat1, toIx_mat2, h])⟩

/-- **`L²(TSD₀)`** through the electric field. -/
theorem isTSD₀_iff (hb : Bornology.IsBounded Ω) (u : L2Vec Ω 1) :
    IsTSD₀ (mat1 u) ↔ fieldE u ∈ tsd₀ Ω hΩ hb := by
  rw [mem_tsd₀, IsTSD₀, isTSD_iff, toIx_mat1]
  refine and_congr Iff.rfl ⟨fun h φ hφ => ?_, fun h a φ hφ => ?_⟩
  · rw [Fintype.sum_prod_type]
    exact Finset.sum_eq_zero fun a _ => h a (φ a) (hφ a)
  · have e := h (fun i => if i = a then φ else 0) fun i => by
      by_cases hi : i = a
      · simp only [hi, ite_true]; exact hφ
      · simp only [hi, ite_false]; exact contDiff_const
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a] at e
    · simp only [ite_true, fieldE_apply] at e
      exact e
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      simp [hb]
    · simp

include hΩ in
theorem dense_vecOp_dMin : Dense ((vecOp fun _ => dMin Ω 1 :
    L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain : Set (L2Vec Ω 1)) :=
  dense_bgg_dt1 hΩ

/-- **The adjoint of the curl** through the fields. -/
theorem mem_graph_adjoint_curl_iff (y : L2Vec Ω 2) (z : L2Vec Ω 1) :
    (y, z) ∈ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2)†.graph ↔
      (fieldB y, fieldE z) ∈ ((gradCurl ℝ hΩ).d₁†).graph :=
  mem_graph_adjoint_iff_of fieldE fieldB (dense_vecOp_dMin hΩ) (gradCurl ℝ hΩ).dense₁
    (fun x y => mem_graph_curl_iff hΩ x y) y z

/-- **Eigenfields** through the electric field. -/
theorem isEigenfield_iff (ξ : ℝ) (v : L2Vec Ω 1) :
    IsEigenfield Ω ξ v ↔ (gradCurl ℝ hΩ).IsEigenfield ξ (fieldE v) := by
  constructor
  · rintro ⟨h1, h2, e⟩
    have h1' := (mem_dom_iff hΩ v).1 h1
    have hc := curl_fieldE hΩ ⟨v, h1⟩ h1'
    have hg := (mem_graph_adjoint_curl_iff hΩ ((vecOp fun _ => dMin Ω 1) ⟨v, h1⟩) ((ξ ^ 2) • v)).1
      (by rw [← e]; exact LinearPMap.mem_graph _ ⟨_, h2⟩)
    rw [← hc] at hg
    obtain ⟨h3, e3⟩ := apply_of_mem_graph hg
    refine ⟨h1', h3, ?_⟩
    rw [e3, map_smul]; rfl
  · rintro ⟨h1', h3, e⟩
    have h1 := (mem_dom_iff hΩ v).2 h1'
    have hc := curl_fieldE hΩ ⟨v, h1⟩ h1'
    have hg : (fieldB ((vecOp fun _ => dMin Ω 1) ⟨v, h1⟩), fieldE ((ξ ^ 2) • v)) ∈
        ((gradCurl ℝ hΩ).d₁†).graph := by
      rw [← hc, map_smul]
      convert LinearPMap.mem_graph _ ⟨_, h3⟩ using 2
      exact e.symm
    obtain ⟨h2, e2⟩ := apply_of_mem_graph ((mem_graph_adjoint_curl_iff hΩ _ _).2 hg)
    exact ⟨h1, h2, e2⟩

/-- `curl v ∉ H̊(curl)`, read through the fields. -/
theorem curl_not_mem_iff (v : L2Vec Ω 1) :
    (∀ h, ¬∃ w ∈ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain,
        mat1 w = mat2 ((vecOp fun _ => dMin Ω 1) ⟨v, h⟩)) ↔
      ∀ h1 : fieldE v ∈ (gradCurl ℝ hΩ).d₁.domain,
        ((gradCurl ℝ hΩ).d₁ ⟨fieldE v, h1⟩ : L2F ℝ Ω Ix) ∉
          ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain := by
  constructor
  · intro H h1 hm
    have h := (mem_dom_iff hΩ v).2 h1
    refine H h ⟨fieldE.symm ((gradCurl ℝ hΩ).d₁ ⟨fieldE v, h1⟩), (mem_dom_iff hΩ _).2 (by simpa
      using hm), ?_⟩
    rw [mat1_eq_mat2_iff, LinearIsometryEquiv.apply_symm_apply, curl_fieldE hΩ ⟨v, h⟩ h1]
  · rintro H h ⟨w, hw, e⟩
    have h1 := (mem_dom_iff hΩ v).1 h
    refine H h1 ?_
    rw [curl_fieldE hΩ ⟨v, h⟩ h1, ← (mat1_eq_mat2_iff _ _).1 e]
    exact (mem_dom_iff hΩ w).1 hw

end GradCurl

end FEEC
