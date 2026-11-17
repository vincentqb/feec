module

public import Solution.MirrorFEM
public import Solution.CubeSpaces

/-!
# The spaces of the mirror scheme are the challenge's

On a mesh `M` of `Ω`, the glued space `V_{h,Γ}ᵏ` of `Feec.FiniteElement.polyElement n S`
(degrees of freedom single-valued on shared faces and vanishing on the faces contained in a
vertex set of `Γ`) is the space of finite element pieces whose tangential traces vanish on these
faces (`mem_VPartial_iff`). On the Freudenthal meshes of the cube with
`Γ = partialFaces J`, vanishing traces on all faces lying in a face `{y_j = 0}`, `{y_j = ½}`,
`j ∈ J`, of the cube is vanishing traces on the facets lying there (`femSpace`): every such
face lies in a facet of some simplex lying in the same face of the cube (`exists_planeFacet`),
and traces are single-valued (`isFemPieces_iff_partial`). So the spaces of `mirrorQ` are
`femSpace ∅` of `topSeq` and `femSpace {a}` of `bottomSeq` (`mirrorQ_spaces`), and
`femSpace univ` is the space with vanishing boundary traces (`femSpace_univ_eq`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.3, Table 6.1
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3, §5

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set Finset

@[expose] public noncomputable section

/-! ### Faces in a face of the cube lie in a facet in that face (Freudenthal meshes) -/

namespace Feec.Models.Cube.FEM

open Feec.Mesh

variable {n : ℕ}

/-- **A nonempty face of a mesh simplex lying in a face of the cube lies in a facet, in that face,
of a mesh simplex** (the boundary facets of `exists_boundaryFacet_of_lower`,
`exists_boundaryFacet_of_upper`). -/
theorem exists_planeFacet {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T)
    (hgne : g.Nonempty) {i : Fin n} (hg : (∀ v ∈ g, v i = 0) ∨ ∀ v ∈ g, v i = 1 / 2) :
    ∃ T'' ∈ (mesh n N).simplices, ∃ F ⊆ vertexSet T'', F.card = n ∧
      ((∀ v ∈ F, v i = 0) ∨ ∀ v ∈ F, v i = 1 / 2) ∧ g ⊆ F := by
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  rcases hg with h | h
  · obtain ⟨T'', hT'', F, hF, hFT, hgF, hF0⟩ := exists_boundaryFacet_of_lower m σ i hgT h hgne
    exact ⟨T'', hT'', F, hFT, hF.1.1, Or.inl hF0, hgF⟩
  · obtain ⟨T'', hT'', F, hF, hFT, hgF, hF0⟩ := exists_boundaryFacet_of_upper m σ i hgT h hgne
    exact ⟨T'', hT'', F, hFT, hF.1.1, Or.inr hF0, hgF⟩

end Feec.Models.Cube.FEM

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)

variable {n : ℕ}

/-! ### The glued spaces with vanishing degrees of freedom on `Γ` -/

section Partial

variable (S : PolySeq) (M : SimplicialMesh n) (Ω : Set (Fin n → ℝ)) (hdom : M.domain = Ω)
  (Γ : Set (Finset (Fin n → ℝ)))

/-- **The glued space `V_{h,Γ}ᵏ` is the space of finite element pieces with vanishing traces on
the faces contained in a vertex set of `Γ`.** -/
theorem mem_VPartial_iff {k : ℤ} (u : L2Form Ω k) :
    u ∈ (polyElement n S.toFeec).VPartial (M.toFeec Ω hdom) Γ k ↔
      ∃ p, IsFemPieces Ω M S k u p ∧ ∀ T ∈ M.simplices, ∀ g ⊆ vertexSet T, (∃ F ∈ Γ, g ⊆ F) →
        ∀ x ∈ convexHull ℝ (g : Set (Fin n → ℝ)), TraceEq g k.toNat (p T x) 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    set w : (polyElement n S.toFeec).Piecewise (M.toFeec Ω hdom) k.toNat := v.1 with hw
    have hv1 : w ∈ (polyElement n S.toFeec).globalSpace (M.toFeec Ω hdom) k.toNat :=
      (polyElement n S.toFeec).globalSpacePartial_le (M.toFeec Ω hdom) Γ k.toNat v.2
    have hpieces := isFemPieces_glue S M Ω hdom ⟨w, hv1⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    refine ⟨_, hpieces, fun T hT g hgT hgΓ x hx => ?_⟩
    rw [LocalElement.extendPW_of_mem _ (M.toFeec Ω hdom) _ hT, traceEq_iff]
    rcases g.eq_empty_or_nonempty with rfl | hne
    · simp at hx
    obtain ⟨j, hj⟩ : ∃ j, #g = j + 1 := ⟨#g - 1, by have := hne.card_pos; omega⟩
    have hgT' : g ⊆ Feec.Mesh.vertexSet T := by rw [← vertexSet_eq]; exact hgT
    obtain ⟨F, hF, hgF⟩ := hgΓ
    exact S.toFeec.tangentialTraceEq_of_dof_eq_face hgT' hj (w ⟨T, hT⟩).2
      (Submodule.zero_mem _) (fun g' hg' i => by
        have h := v.2.2 ⟨T, hT⟩ g' (hg'.trans hgT') ⟨F, hF, hg'.trans hgF⟩ i
        exact h.trans (map_zero _).symm) x hx
  · rintro ⟨p, hp, hb⟩
    refine ⟨⟨ofPieces S M Ω hdom p hp.1, ⟨ofPieces_mem S M Ω hdom hp,
      fun T g hgT hgΓ i => ?_⟩⟩, glue_ofPieces S M Ω hdom hp⟩
    rw [LocalElement.localDof_apply]
    have hgT' : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) := by
      rw [vertexSet_eq]; exact hgT
    have h := S.toFeec.dof_congr i
      (w := ⟨p T, S.toFeec.space_le_contForms n k.toNat
        ((mem_space_iff S (T := T) _ _).2 (hp.1 T T.2))⟩)
      (η := 0) fun x hx => (traceEq_iff _ _ _ _).1 (hb T T.2 g hgT' hgΓ x hx)
    exact h.trans (map_zero _)

end Partial

/-- The partial spaces of a `Feec` mesh of `Q`, transported to `Ω`, are the challenge's. -/
theorem partialSubcomplexOfEq_V (S : PolySeq) (m : Feec.Mesh.SimplicialMesh 3)
    {Ω : Set (Fin 3 → ℝ)} (h : m.domain = Ω) (hM : m.domain = Feec.Models.Cube.Geometry.Q (Fin 3))
    (hΩ : IsOpen Ω) (hΩQ : Ω ⊆ Feec.Models.Cube.Geometry.Q (Fin 3)) (J : Finset (Fin 3)) (k : ℤ) :
    (SetLike.coe ((partialSubcomplexOfEq h _ _ hΩ hΩQ J
      (subcomplexPart (polyElement 3 S.toFeec) m hM J)).V k) : Set (L2Form Ω k)) =
      {u | ∃ p, IsFemPieces Ω (SimplicialMesh.ofFeec m) S k u p ∧
        ∀ T ∈ (SimplicialMesh.ofFeec m).simplices, ∀ g ⊆ vertexSet T,
          (∃ F ∈ partialFaces 3 J, g ⊆ F) →
            ∀ x ∈ convexHull ℝ (g : Set (Fin 3 → ℝ)), TraceEq g k.toNat (p T x) 0} := by
  obtain ⟨T, d, h1, h2, h3⟩ := m
  subst h
  ext u
  exact mem_VPartial_iff S (SimplicialMesh.ofFeec ⟨T, d, h1, h2, h3⟩) _ rfl _ u

/-- **Vanishing traces on the faces in the faces `{y_j ∈ {0, ½}}`, `j ∈ J`, of the cube are
vanishing traces on the facets there** (Freudenthal meshes). -/
theorem isFemPieces_iff_partial (S : PolySeq) (N : ℕ) (J : Finset (Fin 3)) (k : ℤ)
    (u : L2Form (cube 3) k) :
    (∃ p, IsFemPieces (cube 3) (cubeMesh N) S k u p ∧
      ∀ T ∈ (cubeMesh N).simplices, ∀ g ⊆ vertexSet T, (∃ F ∈ partialFaces 3 J, g ⊆ F) →
        ∀ x ∈ convexHull ℝ (g : Set (Fin 3 → ℝ)), TraceEq g k.toNat (p T x) 0) ↔
      u ∈ femSpace J (cubeMesh N) S k := by
  refine ⟨fun ⟨p, hp, hb⟩ => ⟨p, hp, fun T hT F hFT _ hF => hb T hT F hFT ⟨F, hF, subset_rfl⟩⟩,
    fun ⟨p, hp, hb⟩ => ⟨p, hp, fun T hT g hgT ⟨F, ⟨j, hj, hFj⟩, hgF⟩ x hx => ?_⟩⟩
  rcases g.eq_empty_or_nonempty with rfl | hne
  · simp at hx
  have hgj : (∀ v ∈ g, v j = 0) ∨ ∀ v ∈ g, v j = 1 / 2 :=
    hFj.imp (fun h v hv => h v (hgF hv)) fun h v hv => h v (hgF hv)
  have hgT' : g ⊆ Feec.Mesh.vertexSet T := by rw [← vertexSet_eq]; exact hgT
  obtain ⟨T'', hT'', F', hF'T, hF'c, hF'j, hgF'⟩ := exists_planeFacet hT hgT' hne hgj
  have hF'T' : F' ⊆ vertexSet T'' := by rw [vertexSet_eq]; exact hF'T
  -- the trace of `p T''` vanishes on `F'`, hence on `g`
  have h1 := (traceEq_iff _ _ _ _).1 (hb T'' hT'' F' hF'T' hF'c ⟨j, hj, hF'j⟩ x
    (convexHull_mono (Finset.coe_subset.2 hgF') hx))
  -- the traces of `p T` and `p T''` agree on `g ⊆ T ∩ T''`
  have hg2 : g ⊆ vertexSet T ∩ vertexSet T'' := Finset.subset_inter hgT (hgF'.trans hF'T')
  have h2 := (traceEq_iff _ _ _ _).1 (hp.2.2 T hT T'' hT'' x
    (convexHull_mono (Finset.coe_subset.2 hg2) hx))
  rw [traceEq_iff]
  exact fun V hV => ((h2.mono hg2) V hV).trans ((h1.mono hgF') V hV)

/-- **The spaces of `polyPartial` are the challenge's `femSpace`.** -/
theorem polyPartial_V_eq (S : PolySeq) (N : ℕ) (J : Finset (Fin 3)) (k : ℤ) :
    (SetLike.coe ((polyPartial 3 S.toFeec N J).V k) : Set (L2Form (cube 3) k)) =
      femSpace J (cubeMesh N) S k := by
  have h := partialSubcomplexOfEq_V S (mesh 3 N) (mesh_domain 3 N) (mesh_domain_eq_Q N)
    (isOpen_cubeDomain 3) (cubeDomain_subset_Q 3) J k
  ext u
  have hu := congrArg (u ∈ ·) h
  simp only [eq_iff_iff] at hu
  exact hu.trans (isFemPieces_iff_partial S N J k u)

/-- **With vanishing traces on all faces, `femSpace` is the space with vanishing boundary
traces** (Freudenthal meshes, `Feec.Models.Cube.FEM.polyPartial_univ_V`). -/
theorem femSpace_univ_eq (S : PolySeq) (N : ℕ) (k : ℤ) :
    femSpace Finset.univ (cubeMesh N) S k = femSpaceMinOn (cubeDomain 3) (cubeMesh N) S k := by
  rw [← polyPartial_V_eq]
  exact (congrArg (fun P => (SetLike.coe P : Set (L2Form (cube 3) k)))
    (polyPartial_univ_V S.toFeec N k)).trans (polyMin_V_eq S N k)

section Spaces

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- **The spaces of `mirrorQ` are the elements of Table 6.1 with the mirror conditions.** -/
theorem mirrorQ_spaces (N : ℕ) :
    ((mirrorQ hT hB N).V0 : Set W0) = femSpace ∅ (cubeMesh N) topSeq 0 ∧
      ((mirrorQ hT hB N).V1 : Set W1) = femSpace ∅ (cubeMesh N) topSeq 1 ∧
      ((mirrorQ hT hB N).V2 : Set W2) = femSpace ∅ (cubeMesh N) topSeq 2 ∧
      ((mirrorQ hT hB N).Vt0 : Set (Wv W0)) =
        {v | ∀ a, v a ∈ femSpace {a} (cubeMesh N) bottomSeq 0} ∧
      ((mirrorQ hT hB N).Vt1 : Set (Wv W1)) =
        {v | ∀ a, v a ∈ femSpace {a} (cubeMesh N) bottomSeq 1} ∧
      ((mirrorQ hT hB N).Vt2 : Set (Wv W2)) =
        {v | ∀ a, v a ∈ femSpace {a} (cubeMesh N) bottomSeq 2} := by
  have hT' := fun k => polyPartial_V_eq topSeq N ∅ k
  have hB' := fun a k => polyPartial_V_eq bottomSeq N {a} k
  rw [topSeq_toFeec] at hT'
  rw [bottomSeq_toFeec] at hB'
  refine ⟨hT' 0, hT' 1, hT' 2, ?_, ?_, ?_⟩ <;>
  · ext v
    exact forall_congr' fun a => by rw [← hB']; rfl

end Spaces

end FEEC
