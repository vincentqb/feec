module

public import Solution.Bridge
public import Solution.Wedge
public import Feec.Models.Cube.BGGCohomology

/-!
# The Hessian, elasticity and div–div diagrams of the challenge on the cube

The stacked diagrams of the challenge on the cube are `Feec`'s BGG diagrams of forms
(`Feec.FiniteElement.hessianFormData`, `divDivFormData` and `elasticityFormData` on
`Feec.Models.Cube.FEM.cubeDomain 3`): `dMax` is `Feec`'s maximal exterior derivative (`dMax_eq`),
`vecOp` of it is the product complex `Feec.HilbertComplex.pi` (`vecOp_eq_piD`), and `wedge`,
`dxVec`, `crossWedge` are `Feec.FiniteElement.wsL2`, `dxVecL2`, `crossL2` (`wedge_eq`,
`dxWedge_eq`, `dxVec_eq`, `crossWedge_eq`).

For analytic BGG data `D` of `Feec` on `ℤ`, the graph spaces of the rows carry the bounded maps
`graphD` (`(u, du) ↦ (du, 0)`) and `graphS` (`(φ, d̃φ) ↦ (Sφ, -S d̃φ)`), a stacked diagram of
the domain complexes of the challenge (`toDomainDiagram`), whose rows have the cohomology of the
rows of `D` (`graphHomologyEquiv`, from `Feec.HilbertComplex.cohomologyEquivOfIso`); `s` is bounded
below where `S` is in two consecutive degrees (`antilipschitz_graphS`, as
`Feec.BGG.HilbertData.antilipschitz_domainS`) and onto modulo `d` where the rows split
(`sup_range_eq_top_of_exists`, as `Feec.BGG.HilbertData.regularDecomposition_of_forall_exists`).
In the lowest degree of the rows, `[(σ, φ)] ↦ u`, `σ = (u, du)`, is an isomorphism of the
cohomology of the BGG complex onto the `u ∈ D(dⁱ)` with `d u = S v` for some closed `v`
(`cohomologyIs_toDomainDiagram`, from `FEEC.BGG.exists_bgg_homology_lowCycles`).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3, §4.1, Theorem 6

Bibliography: [references.bib](../../../docs/references.bib)
-/

open CategoryTheory
open scoped InnerProductSpace

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement LinearPMap

/-! ### Graph spaces -/

section Graph

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

theorem graph2_eq (A : E →ₗ.[ℝ] F) : graph2 A = A.graphL2 := rfl

/-- `D(A) ≃ Γ(A)`, `x ↦ (x, A x)`. -/
def graphEquiv (A : E →ₗ.[ℝ] F) : A.domain ≃ₗ[ℝ] graph2 A where
  toFun x := A.toGraphSpace x
  invFun v := ⟨A.graphFst v, by
    obtain ⟨x, rfl, -, -⟩ := A.exists_toGraphSpace_eq v
    exact x.2⟩
  map_add' x y := Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext rfl (A.map_add x y)))
  map_smul' c x := Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext rfl (A.map_smul c x)))
  left_inv _ := rfl
  right_inv v := A.graphFst_injective rfl

@[simp] theorem graphEquiv_fst (A : E →ₗ.[ℝ] F) (x : A.domain) :
    ((graphEquiv A x : WithLp 2 (E × F)).ofLp).1 = x := rfl

@[simp] theorem graphEquiv_snd (A : E →ₗ.[ℝ] F) (x : A.domain) :
    ((graphEquiv A x : WithLp 2 (E × F)).ofLp).2 = A x := rfl

/-- A point of a graph is determined by its first component. -/
theorem graph2_ext {A : E →ₗ.[ℝ] F} {v w : graph2 A}
    (h : ((v : WithLp 2 (E × F)).ofLp).1 = ((w : WithLp 2 (E × F)).ofLp).1) : v = w :=
  A.graphFst_injective h

end Graph

/-! ### The stacked diagram of the domain complexes of analytic BGG data -/

section Domain

variable {E Et : ℤ → Type} [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℝ (E k)]
  [∀ k, CompleteSpace (E k)] [∀ k, NormedAddCommGroup (Et k)] [∀ k, InnerProductSpace ℝ (Et k)]
  [∀ k, CompleteSpace (Et k)]

/-- `(u, du) ↦ (du, 0)` on the graph spaces of a Hilbert complex. -/
def graphD (H : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) E) (k : ℤ) :
    graph2 (H.d k (k + 1)) →L[ℝ] graph2 (H.d (k + 1) (k + 1 + 1)) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (E (k + 1)) (E (k + 1 + 1))).symm.toContinuousLinearMap ∘L
    ((H.d k (k + 1)).graphSnd.prod 0)).codRestrict _ fun v => by
      obtain ⟨x, rfl, -, -⟩ := (H.d k (k + 1)).exists_toGraphSpace_eq v
      rw [graph2_eq, mem_graphL2]
      exact (LinearPMap.mem_graph_iff _).2 ⟨⟨_, H.mapsTo k (k + 1) (k + 1 + 1) x⟩, rfl,
        H.d_comp_d k (k + 1) (k + 1 + 1) x⟩

theorem graphD_fst (H : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) E) (k : ℤ)
    (v : graph2 (H.d k (k + 1))) :
    ((graphD H k v : WithLp 2 (E (k + 1) × E (k + 1 + 1))).ofLp).1 =
      ((v : WithLp 2 (E k × E (k + 1))).ofLp).2 := rfl

theorem graphD_graphD (H : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) E) (k : ℤ)
    (v : graph2 (H.d k (k + 1))) : graphD H (k + 1) (graphD H k v) = 0 := by
  refine graph2_ext ?_
  change (((graphD H k v : WithLp 2 (E (k + 1) × E (k + 1 + 1))).ofLp).2 : E (k + 1 + 1)) = 0
  rfl

/-- `(φ, d̃φ) ↦ (Sφ, -S d̃φ)` from the graph spaces of the bottom row to those of the top row. -/
def graphS (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et) (k : ℤ) :
    graph2 (D.Ht.d k (k + 1)) →L[ℝ] graph2 (D.H.d (k + 1) (k + 1 + 1)) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (E (k + 1)) (E (k + 1 + 1))).symm.toContinuousLinearMap ∘L
    ((D.S k (k + 1) ∘L (D.Ht.d k (k + 1)).graphFst).prod
      (-(D.S (k + 1) (k + 1 + 1) ∘L (D.Ht.d k (k + 1)).graphSnd)))).codRestrict _ fun v => by
      obtain ⟨φ, rfl, -, -⟩ := (D.Ht.d k (k + 1)).exists_toGraphSpace_eq v
      rw [graph2_eq, mem_graphL2]
      exact (LinearPMap.mem_graph_iff _).2 ⟨⟨_, D.S_mapsTo k (k + 1) (k + 1 + 1) φ⟩, rfl,
        D.anticomm k (k + 1) (k + 1 + 1) φ⟩

/-- **The stacked diagram of the domain complexes** of analytic BGG data on `ℤ`. -/
def toDomainDiagram (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et) :
    BGG.DomainDiagram (fun k => D.H.d k (k + 1)) (fun k => D.Ht.d k (k + 1))
      (fun k => D.S k (k + 1)) where
  d := graphD D.H
  dt := graphD D.Ht
  s := graphS D
  fst_d _ _ := rfl
  fst_dt _ _ := rfl
  fst_s _ _ := rfl
  d_d := graphD_graphD D.H
  dt_dt := graphD_graphD D.Ht
  d_s k v := by
    refine graph2_ext ?_
    change (((graphS D k v : WithLp 2 (E (k + 1) × E (k + 1 + 1))).ofLp).2 : E (k + 1 + 1)) =
      -D.S (k + 1) (k + 1 + 1) ((graphD D.Ht k v : WithLp 2 (Et (k + 1) × Et (k + 1 + 1))).ofLp).1
    rfl

/-- **`s` is bounded below where `S` is, in two consecutive degrees**: `‖(φ, d̃φ)‖² ≤
max(K₁, K₂)² (‖Sφ‖² + ‖S d̃φ‖²)`. -/
theorem antilipschitz_graphS (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et) {k : ℤ}
    {K₁ K₂ : NNReal} (h₁ : AntilipschitzWith K₁ (D.S k (k + 1)))
    (h₂ : AntilipschitzWith K₂ (D.S (k + 1) (k + 1 + 1))) :
    AntilipschitzWith (max K₁ K₂) (graphS D k) := by
  refine (graphS D k).antilipschitz_of_bound fun v => ?_
  set x := (v : WithLp 2 (Et k × Et (k + 1)))
  have hv : ‖v‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 x
  have hs : ‖graphS D k v‖ ^ 2 =
      ‖D.S k (k + 1) x.fst‖ ^ 2 + ‖D.S (k + 1) (k + 1 + 1) x.snd‖ ^ 2 := by
    rw [← norm_neg (D.S (k + 1) (k + 1 + 1) x.snd)]
    exact WithLp.prod_norm_sq_eq_of_L2 (graphS D k v : WithLp 2 (E (k + 1) × E (k + 1 + 1)))
  have b₁ := ((D.S k (k + 1)).bound_of_antilipschitz h₁ x.fst).trans
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 (le_max_left K₁ K₂)) (norm_nonneg _))
  have b₂ := ((D.S (k + 1) (k + 1 + 1)).bound_of_antilipschitz h₂ x.snd).trans
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 (le_max_right K₁ K₂)) (norm_nonneg _))
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [hv, mul_pow, hs, mul_add, ← mul_pow, ← mul_pow]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) b₁ 2) (pow_le_pow_left₀ (norm_nonneg _) b₂ 2)

/-- **`s` is onto modulo `d` where the rows split**: if every `u ∈ D(dᵏ⁺¹)` is `dᵏ p + Sᵏ φ`, then
`R(dᵏ) + R(sᵏ) = Γ(dᵏ⁺¹)` in the graph spaces. -/
theorem sup_range_eq_top_of_exists (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et)
    {k : ℤ} (h : ∀ u ∈ (D.H.d (k + 1) (k + 1 + 1)).domain,
      ∃ (p : (D.H.d k (k + 1)).domain) (φ : (D.Ht.d k (k + 1)).domain),
        D.H.d k (k + 1) p + D.S k (k + 1) φ = u) :
    LinearMap.range ((toDomainDiagram D).d k :
        graph2 (D.H.d k (k + 1)) →ₗ[ℝ] graph2 (D.H.d (k + 1) (k + 1 + 1))) ⊔
      LinearMap.range ((toDomainDiagram D).s k :
        graph2 (D.Ht.d k (k + 1)) →ₗ[ℝ] graph2 (D.H.d (k + 1) (k + 1 + 1))) = ⊤ := by
  refine eq_top_iff.2 fun w _ => ?_
  obtain ⟨u, rfl, -, -⟩ := (D.H.d (k + 1) (k + 1 + 1)).exists_toGraphSpace_eq w
  obtain ⟨p, φ, e⟩ := h u u.2
  have hmem := Submodule.add_mem_sup
    (LinearMap.mem_range_self ((toDomainDiagram D).d k :
      graph2 (D.H.d k (k + 1)) →ₗ[ℝ] graph2 (D.H.d (k + 1) (k + 1 + 1)))
      (graphEquiv (D.H.d k (k + 1)) p))
    (LinearMap.mem_range_self ((toDomainDiagram D).s k :
      graph2 (D.Ht.d k (k + 1)) →ₗ[ℝ] graph2 (D.H.d (k + 1) (k + 1 + 1)))
      (graphEquiv (D.Ht.d k (k + 1)) φ))
  have he : (D.H.d (k + 1) (k + 1 + 1)).toGraphSpace u =
      (toDomainDiagram D).d k (graphEquiv (D.H.d k (k + 1)) p) +
        (toDomainDiagram D).s k (graphEquiv (D.Ht.d k (k + 1)) φ) :=
    graph2_ext (A := D.H.d (k + 1) (k + 1 + 1)) e.symm
  rw [he]
  exact hmem

/-- `D(d i (c.next i)) ≃ Γ(d i (i + 1))`. -/
def graphDomainEquiv (H : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) E) (i : ℤ) :
    (H.d i ((ComplexShape.up ℤ).next i)).domain ≃ₗ[ℝ] graph2 (H.d i (i + 1)) :=
  (LinearEquiv.ofEq _ _ (by rw [CochainComplex.next])).trans (graphEquiv (H.d i (i + 1)))

/-- **The homology of the bounded complex of the graph spaces is the cohomology of the Hilbert
complex** (`Feec.HilbertComplex.cohomologyEquivOfIso`). -/
def graphHomologyEquiv (H : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) E) (i : ℤ) :
    H.cohomology i ≃ₗ[ℝ] (BGG.ofBounded (graphD H) (graphD_graphD H)).homology i :=
  Feec.HilbertComplex.cohomologyEquivOfIso
    (Feec.HilbertComplex.toModuleCatIso H _ (graphDomainEquiv H) fun i j x => by
      by_cases hij : i + 1 = j
      · subst hij
        rw [BGG.ofBounded_d_succ]
        refine graph2_ext ?_
        change (H.domainMap i (i + 1) x : E (i + 1)) = H.d i (i + 1) ⟨x, _⟩
        rw [Feec.HilbertComplex.coe_domainMap]
      · rw [HomologicalComplex.shape _ i j hij]
        have h0 : H.domainMap i j x = 0 := Subtype.ext (by
          rw [Feec.HilbertComplex.coe_domainMap]
          exact H.apply_eq_zero_of_not_rel hij _)
        rw [h0, _root_.map_zero]
        rfl) i

/-- `s` is one-to-one where `S` is. -/
theorem injective_graphS (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et) {k : ℤ}
    (h : Function.Injective (D.S k (k + 1))) : Function.Injective (graphS D k) := fun _ _ hvw =>
  graph2_ext (h (congrArg (fun x : graph2 (D.H.d (k + 1) (k + 1 + 1)) =>
    ((x : WithLp 2 (E (k + 1) × E (k + 1 + 1))).ofLp).1) hvw))

/-- A graph over a zero space is zero. -/
theorem subsingleton_graph2 {F G : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [Subsingleton F] (A : F →ₗ.[ℝ] G) :
    Subsingleton (graph2 A) :=
  ⟨fun _ _ => graph2_ext (Subsingleton.elim _ _)⟩

theorem graphD_toGraphSpace_eq_zero_iff (H : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) E) (k : ℤ)
    (x : (H.d k (k + 1)).domain) :
    graphD H k ((H.d k (k + 1)).toGraphSpace x) = 0 ↔ H.d k (k + 1) x = 0 :=
  ⟨fun h => congrArg (fun p : graph2 (H.d (k + 1) (k + 1 + 1)) =>
    ((p : WithLp 2 (E (k + 1) × E (k + 1 + 1))).ofLp).1) h, fun h => graph2_ext h⟩

theorem graphS_toGraphSpace_eq_iff (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et) (k : ℤ)
    (w : (D.Ht.d k (k + 1)).domain) (x : (D.H.d k (k + 1)).domain) :
    graphS D k ((D.Ht.d k (k + 1)).toGraphSpace w) =
        graphD D.H k ((D.H.d k (k + 1)).toGraphSpace x) ↔
      D.S k (k + 1) w = D.H.d k (k + 1) x :=
  ⟨fun h => congrArg (fun p : graph2 (D.H.d (k + 1) (k + 1 + 1)) =>
    ((p : WithLp 2 (E (k + 1) × E (k + 1 + 1))).ofLp).1) h, fun h => graph2_ext h⟩

/-- **The lowest cocycles of the stacked diagram of the domain complexes, in `L²`**: `σ = (u, du)`
has `dσ ∈ S N(d̃)` iff `d u = S v` for some `v ∈ N(d̃)`. -/
theorem mem_lowCycles_toDomainDiagram (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et)
    (i : ℤ) (σ : graph2 (D.H.d i (i + 1))) :
    σ ∈ (BGG.toData (toDomainDiagram D).toHom).lowCycles i ↔
      ∃ hu : (D.H.d i (i + 1)).graphFst σ ∈ (D.H.d i (i + 1)).domain,
        ∃ v ∈ (D.Ht.d i (i + 1)).ker,
          D.S i (i + 1) v = D.H.d i (i + 1) ⟨(D.H.d i (i + 1)).graphFst σ, hu⟩ := by
  obtain ⟨x, rfl, -, -⟩ := (D.H.d i (i + 1)).exists_toGraphSpace_eq σ
  have ed : (BGG.toData (toDomainDiagram D).toHom).d i (i + 1) =
      (graphD D.H i : graph2 (D.H.d i (i + 1)) →ₗ[ℝ] graph2 (D.H.d (i + 1) (i + 1 + 1))) :=
    BGG.ofBounded_d_succ i
  have edt : (BGG.toData (toDomainDiagram D).toHom).dt i (i + 1) =
      (graphD D.Ht i : graph2 (D.Ht.d i (i + 1)) →ₗ[ℝ] graph2 (D.Ht.d (i + 1) (i + 1 + 1))) :=
    BGG.ofBounded_d_succ i
  have eS : (BGG.toData (toDomainDiagram D).toHom).S i (i + 1) =
      (graphS D i : graph2 (D.Ht.d i (i + 1)) →ₗ[ℝ] graph2 (D.H.d (i + 1) (i + 1 + 1))) :=
    BGG.conn_ofBoundedHom _ _ i
  refine (Feec.BGG.Data.mem_lowCycles _).trans ⟨?_, ?_⟩
  · rintro ⟨φ, hφ, hSφ⟩
    obtain ⟨w, rfl, -, -⟩ := (D.Ht.d i (i + 1)).exists_toGraphSpace_eq φ
    refine ⟨x.2, w, LinearPMap.mem_ker_iff.2 ⟨w, rfl,
      (graphD_toGraphSpace_eq_zero_iff D.Ht i w).1 ((LinearMap.congr_fun edt _).symm.trans hφ)⟩,
      (graphS_toGraphSpace_eq_iff D i w x).1 ?_⟩
    exact (LinearMap.congr_fun eS _).symm.trans (hSφ.trans (LinearMap.congr_fun ed _))
  · rintro ⟨_hu, v, hv, hSv⟩
    obtain ⟨w, rfl, hw⟩ := LinearPMap.mem_ker_iff.1 hv
    refine ⟨(D.Ht.d i (i + 1)).toGraphSpace w,
      (LinearMap.congr_fun edt _).trans ((graphD_toGraphSpace_eq_zero_iff D.Ht i w).2 hw), ?_⟩
    exact (LinearMap.congr_fun eS _).trans (((graphS_toGraphSpace_eq_iff D i w x).2 hSv).trans
      (LinearMap.congr_fun ed _).symm)

/-- **The cohomology of the BGG complex of the domain complexes in the lowest degree**, in `L²`
(`FEEC.BGG.exists_bgg_homology_lowCycles`): `[(σ, φ)] ↦ u`, `σ = (u, du)`, is an isomorphism of
`Hⁱ` onto the `u ∈ D(dⁱ)` with `d u = S v` for some `v ∈ N(d̃ⁱ)`. -/
theorem cohomologyIs_toDomainDiagram (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et)
    {i J : ℤ} (hiJ : i ≤ J) [Subsingleton (E (i - 1))] [Subsingleton (Et (i - 1))]
    (hS : J = i → Function.Injective (D.S i (i + 1)))
    (hS' : i + 2 ≤ J → Function.Injective (D.S (i + 1) (i + 1 + 1))) :
    (toDomainDiagram D).CohomologyIs J i {u | ∃ hu : u ∈ (D.H.d i (i + 1)).domain,
      ∃ v ∈ (D.Ht.d i (i + 1)).ker, D.S i (i + 1) v = D.H.d i (i + 1) ⟨u, hu⟩} := by
  have := subsingleton_graph2 (D.H.d (i - 1) (i - 1 + 1))
  have := subsingleton_graph2 (D.Ht.d (i - 1) (i - 1 + 1))
  obtain ⟨f, hf, hrange, hfz⟩ := BGG.exists_bgg_homology_lowCycles (toDomainDiagram D).toHom hiJ
    (fun h => injective_graphS D (hS h)) (fun h => injective_graphS D (hS' h))
  let g : (BGG.ofBounded (toDomainDiagram D).d (toDomainDiagram D).d_d).X i →ₗ[ℝ] E i :=
    (D.H.d i (i + 1)).graphFst.toLinearMap
  have hg : Function.Injective g := (D.H.d i (i + 1)).graphFst_injective
  refine ⟨g ∘ₗ f, hg.comp hf, ?_, fun z y h => ?_⟩
  swap
  · show g (f _) = _
    rw [hfz z y h]
    rfl
  ext u
  constructor
  · rintro ⟨h, rfl⟩
    exact (mem_lowCycles_toDomainDiagram D i (f h)).1 (by rw [← hrange]; exact ⟨h, rfl⟩)
  · intro hu
    obtain ⟨h, hh⟩ : (D.H.d i (i + 1)).toGraphSpace ⟨u, hu.1⟩ ∈ LinearMap.range f := by
      rw [hrange]; exact (mem_lowCycles_toDomainDiagram D i _).2 hu
    exact ⟨h, congrArg g hh⟩

end Domain

/-! ### The diagrams of the challenge are those of `Feec` -/

section Identify

variable {n : ℕ}

/-- `vecOp` of a constant family is the product complex of `Feec`. -/
theorem vecOp_eq_piD {W : ℤ → Type} [∀ k, NormedAddCommGroup (W k)]
    [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    (H : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) W) {k : ℤ} {A : W k →ₗ.[ℝ] W (k + 1)}
    (hA : H.d k (k + 1) = A) :
    (vecOp fun _ : Fin n => A) = (H.pi (Fin n)).d k (k + 1) := by
  subst hA
  refine LinearPMap.ext ?_ fun x hx hx' => PiLp.ext fun a => ?_
  · ext v
    rw [Feec.HilbertComplex.pi_d, Feec.HilbertComplex.piD_domain,
      Feec.HilbertComplex.mem_piDomain]
    rfl
  · rw [Feec.HilbertComplex.pi_d_apply]
    rfl

/-- The exterior product with `dxₐ` of the challenge is `Feec`'s. -/
theorem dxWedge_eq (Ω : Set (Fin n → ℝ)) (k : ℤ) (a : Fin n) :
    dxWedge Ω k a = dxL2 (Ω := Ω) k a := by
  unfold dxWedge dxL2
  rw [wedge_eq]

/-- The div–div connecting map of the challenge is `Feec`'s. -/
theorem dxVec_eq (Ω : Set (Fin n → ℝ)) (k : ℤ) : dxVec Ω k = dxVecL2 (Ω := Ω) k := by
  unfold dxVec dxVecL2
  simp only [dxWedge_eq]

/-- The elasticity connecting map of the challenge is `Feec`'s. -/
theorem crossWedge_eq (Ω : Set (Fin 3 → ℝ)) (k : ℤ) : crossWedge Ω k = crossL2 (Ω := Ω) k := by
  unfold crossWedge crossL2
  simp only [dxWedge_eq]

/-- `dMax` on the cube is `Feec`'s `HΛ(Q)`. -/
theorem dMax_cube_eq (k : ℤ) :
    (formRow 3 (Feec.Models.Cube.FEM.isOpen_cubeDomain 3)).d k (k + 1) = dMax (cube 3) k :=
  (formRow_d _ k).trans (dMax_eq (cube 3) k).symm

/-- `vecOp` of `dMax` on the cube is `Feec`'s `HΛ(Q) ⊗ ℝ³`. -/
theorem vecOp_cube_eq (k : ℤ) :
    (vecRow 3 (Feec.Models.Cube.FEM.isOpen_cubeDomain 3)).d k (k + 1) =
      vecOp fun _ : Fin 3 => dMax (cube 3) k :=
  (vecOp_eq_piD _ (dMax_cube_eq k)).symm

end Identify

end FEEC
