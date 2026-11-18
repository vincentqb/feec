module

public import Solution.Mesh
public import Solution.Poly
public import Solution.Trace

/-!
# The finite element spaces of the challenge are those of `Feec`

On a mesh `M` of `Ω`, the glued spaces `Vₕᵏ`, `V̊ₕᵏ` of the element family
`Feec.FiniteElement.polyElement n S` of an admissible sequence (piecewise fields whose degrees of
freedom agree on shared faces, resp. also vanish on boundary faces) are the spaces `femSpace` of
the challenge with no facet and with the boundary facets (`mem_V_iff`, `mem_V₀_iff`). These are the
spaces of finite element pieces (`femSpace_empty`), resp. those whose traces vanish on the facets of
a single simplex (`mem_boundaryFacets_iff`): degrees of freedom agree on a face
iff the tangential traces do (`Feec.FiniteElement.PolySeq.dof_congr` and trace determination on
faces of every dimension, `Feec.FiniteElement.PolySeq.tangentialTraceEq_of_dof_eq_face`), and the
glued field is the element field almost everywhere on each simplex (the frontiers of simplices are
null).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3, §5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6, 7

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set Finset

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.ExteriorFibre

variable {n : ℕ}

/-- Almost every point of a simplex lies in its interior. -/
theorem ae_mem_interior (Ω : Set (Fin n → ℝ)) (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    ∀ᵐ x ∂volume.restrict (Ω ∩ T.closedInterior), x ∈ interior T.closedInterior := by
  have h0 := Convex.addHaar_frontier volume (Feec.Mesh.convex_closedInterior T)
  have h1 : ∀ᵐ x ∂volume, x ∉ frontier T.closedInterior := measure_eq_zero_iff_ae_notMem.1 h0
  have h2 : ∀ᵐ x ∂volume.restrict (Ω ∩ T.closedInterior), x ∈ T.closedInterior :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right
      (ae_restrict_mem T.isCompact_closedInterior.isClosed.measurableSet)
  filter_upwards [ae_restrict_of_ae h1, h2] with x hx hx'
  by_contra hi
  exact hx ⟨subset_closure hx', hi⟩

/-- Functions agreeing almost everywhere on every `Ω ∩ T` agree almost everywhere on `Ω`. -/
theorem ae_eq_of_simplices (M : Feec.Mesh.SimplicialMesh n) {f g : (Fin n → ℝ) → ℝ}
    (h : ∀ T ∈ M.simplices, f =ᵐ[volume.restrict (M.domain ∩ T.closedInterior)] g) :
    f =ᵐ[volume.restrict M.domain] g := by
  have e : M.domain = ⋃ T ∈ M.simplices, M.domain ∩ T.closedInterior := by
    refine Subset.antisymm (fun x hx => ?_) (iUnion₂_subset fun _ _ => inter_subset_left)
    have : x ∈ ⋃ T ∈ M.simplices, T.closedInterior := by
      rw [M.biUnion_closedInterior]; exact subset_closure hx
    obtain ⟨T, hT, hxT⟩ := mem_iUnion₂.1 this
    exact mem_iUnion₂.2 ⟨T, hT, hx, hxT⟩
  change ∀ᵐ x ∂volume.restrict M.domain, f x = g x
  rw [e, ae_restrict_biUnion_finset_iff]
  exact h

section Glue

variable (E : LocalElement n) (M : Feec.Mesh.SimplicialMesh n)

/-- **The glued field is the element field almost everywhere on each simplex.** -/
theorem glue_ae_eq {k : ℤ} (v : E.Piecewise M k.toNat) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ M.simplices) (s : formIdx n k) :
    ⇑((E.glue M k v) s) =ᵐ[volume.restrict (M.domain ∩ T.closedInterior)]
      fun x => E.extendPW M v T x s.1 := by
  have h1 : ⇑((E.glue M k v) s) =ᵐ[volume.restrict M.domain]
      pieceFun M fun T => formComp (k := k) (E.extendPW M v T) s :=
    coeFn_pieceL2 M M.domain (fun T => formComp (k := k) (E.extendPW M v T))
      (fun T hT s => continuous_formComp (E.contDiff_extendPW M v hT).continuous s) s
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left h1,
    ae_mem_interior M.domain T] with x hx hx'
  rw [hx, pieceFun_of_mem_interior M _ hT hx']
  rfl

end Glue

variable [NeZero n] (S : PolySeq) (M : SimplicialMesh n) (Ω : Set (Fin n → ℝ))
  (hdom : M.domain = Ω)

omit [NeZero n] in
theorem mem_space_iff {T : Affine.Simplex ℝ (Fin n → ℝ) n} (k : ℕ) (w : FormField n) :
    w ∈ (polyElement n S.toFeec).space T k ↔ w ∈ S.space n k := by
  change w ∈ S.toFeec.space n k ↔ _
  rw [S.space_eq]

omit [NeZero n] in
/-- The traces on the common faces of two simplices of a global field agree. -/
theorem traceEq_of_mem_globalSpace {k : ℕ}
    {v : (polyElement n S.toFeec).Piecewise (M.toFeec Ω hdom) k}
    (hv : v ∈ (polyElement n S.toFeec).globalSpace (M.toFeec Ω hdom) k)
    {T T' : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) (hT' : T' ∈ M.simplices) :
    ∀ x ∈ convexHull ℝ ((vertexSet T ∩ vertexSet T' : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)),
      TraceEq (vertexSet T ∩ vertexSet T') k ((v ⟨T, hT⟩ : FormField n) x)
        ((v ⟨T', hT'⟩ : FormField n) x) := by
  intro x hx
  rw [traceEq_iff]
  rcases (vertexSet T ∩ vertexSet T').eq_empty_or_nonempty with hc | hc
  · rw [hc] at hx; simp at hx
  obtain ⟨j, hj⟩ : ∃ j, #(vertexSet T ∩ vertexSet T') = j + 1 :=
    ⟨#(vertexSet T ∩ vertexSet T') - 1, by have := hc.card_pos; omega⟩
  have hcT : vertexSet T ∩ vertexSet T' ⊆ Feec.Mesh.vertexSet T := by
    rw [← vertexSet_eq]; exact inter_subset_left
  have hcT' : vertexSet T ∩ vertexSet T' ⊆ Feec.Mesh.vertexSet T' := by
    rw [← vertexSet_eq]; exact inter_subset_right
  exact S.toFeec.tangentialTraceEq_of_dof_eq_face hcT hj (v ⟨T, hT⟩).2 (v ⟨T', hT'⟩).2
    (fun g hg i => hv ⟨T, hT⟩ ⟨T', hT'⟩ g (hg.trans hcT) (hg.trans hcT') i) x hx

/-- The piecewise field of finite element pieces `p`. -/
def ofPieces {k : ℤ} (p : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n)
    (hp : ∀ T ∈ M.simplices, p T ∈ S.space n k.toNat) :
    (polyElement n S.toFeec).Piecewise (M.toFeec Ω hdom) k.toNat :=
  fun T => ⟨p T, (mem_space_iff S k.toNat _).2 (hp T T.2)⟩

omit [NeZero n] in
theorem ofPieces_mem {k : ℤ} {u : L2Form Ω k} {p : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n}
    (hp : IsFemPieces Ω M S k u p) :
    ofPieces S M Ω hdom p hp.1 ∈ (polyElement n S.toFeec).globalSpace (M.toFeec Ω hdom) k.toNat := by
  intro T T' g hg hg' i
  rw [LocalElement.localDof_apply, LocalElement.localDof_apply]
  refine S.toFeec.dof_congr i fun x hx => ?_
  rw [← vertexSet_eq] at hg hg'
  have hgc : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) ∩
      vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) := subset_inter hg hg'
  exact ((traceEq_iff _ _ _ _).1 (hp.2.2 T T.2 T' T'.2 x
    (convexHull_mono (Finset.coe_subset.2 hgc) hx))).mono hgc

omit [NeZero n] in
theorem glue_ofPieces {k : ℤ} {u : L2Form Ω k} {p : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n}
    (hp : IsFemPieces Ω M S k u p) :
    (polyElement n S.toFeec).glue (M.toFeec Ω hdom) k (ofPieces S M Ω hdom p hp.1) = u := by
  refine PiLp.ext fun s => Lp.ext ?_
  refine ae_eq_of_simplices (M.toFeec Ω hdom) fun T hT =>
    (glue_ae_eq _ (M.toFeec Ω hdom) _ hT s).trans ?_
  rw [LocalElement.extendPW_of_mem _ (M.toFeec Ω hdom) _ hT]
  exact (hp.2.1 T hT s).symm

omit [NeZero n] in
theorem isFemPieces_glue {k : ℤ}
    (v : (polyElement n S.toFeec).globalSpace (M.toFeec Ω hdom) k.toNat) :
    IsFemPieces Ω M S k ((polyElement n S.toFeec).glue (M.toFeec Ω hdom) k v)
      ((polyElement n S.toFeec).extendPW (M.toFeec Ω hdom) v.1) := by
  refine ⟨fun T hT => ?_, fun T hT s => glue_ae_eq _ (M.toFeec Ω hdom) v.1 hT s,
    fun T hT T' hT' => ?_⟩
  · rw [LocalElement.extendPW_of_mem _ (M.toFeec Ω hdom) _ hT, ← mem_space_iff S (T := T)]
    exact (v.1 ⟨T, hT⟩).2
  · rw [LocalElement.extendPW_of_mem _ (M.toFeec Ω hdom) _ hT,
      LocalElement.extendPW_of_mem _ (M.toFeec Ω hdom) _ hT']
    exact traceEq_of_mem_globalSpace S M Ω hdom v.2 hT hT'

omit [NeZero n] in
/-- **With no facet, `femSpace` is the space of finite element pieces**, `S_k(M)` without boundary
condition. -/
theorem femSpace_empty (k : ℤ) : femSpace Ω M S ∅ k = {u | ∃ p, IsFemPieces Ω M S k u p} := by
  ext u
  exact ⟨fun ⟨p, hp, _⟩ => ⟨p, hp⟩, fun ⟨p, hp⟩ => ⟨p, hp, fun _ _ _ _ _ h => by simp at h⟩⟩

omit [NeZero n] in
/-- **A facet `F` of a simplex `T` of the mesh is a boundary facet iff `T` is its only simplex**,
so `femSpace` with the boundary facets has vanishing traces on the facets of a single simplex. -/
theorem mem_boundaryFacets_iff {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices)
    {F : Finset (Fin n → ℝ)} (hFT : F ⊆ vertexSet T) :
    F ∈ M.boundaryFacets ↔ F.card = n ∧ ∀ T' ∈ M.simplices, F ⊆ vertexSet T' → T' = T := by
  change F.card = n ∧ (∃! T, T ∈ M.simplices ∧ F ⊆ vertexSet T) ↔ _
  refine and_congr_right fun _ => ⟨fun ⟨T₀, _, hu⟩ T' hT' hFT' => ?_,
    fun h => ⟨T, ⟨hT, hFT⟩, fun T' hT' => h T' hT'.1 hT'.2⟩⟩
  rw [hu T' ⟨hT', hFT'⟩, hu T ⟨hT, hFT⟩]

omit [NeZero n] in
/-- **The glued space `Vₕᵏ` is the finite element space of the challenge.** -/
theorem mem_V_iff {k : ℤ} (u : L2Form Ω k) :
    u ∈ (polyElement n S.toFeec).V (M.toFeec Ω hdom) k ↔ u ∈ femSpace Ω M S ∅ k := by
  rw [femSpace_empty]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, isFemPieces_glue S M Ω hdom v⟩
  · rintro ⟨p, hp⟩
    exact ⟨⟨_, ofPieces_mem S M Ω hdom hp⟩, glue_ofPieces S M Ω hdom hp⟩

omit [NeZero n] in
/-- A facet of a single simplex of the mesh is a boundary facet. -/
theorem isBoundaryFacet_of {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices)
    {F : Finset (Fin n → ℝ)} (hFT : F ⊆ vertexSet T) (hF : F.card = n)
    (hu : ∀ T' ∈ M.simplices, F ⊆ vertexSet T' → T' = T) :
    (M.toFeec Ω hdom).IsBoundaryFacet F := by
  rw [Feec.Mesh.SimplicialMesh.isBoundaryFacet_iff]
  refine ⟨⟨hF, T, hT, by rw [← vertexSet_eq]; exact hFT⟩, Finset.card_eq_one.2 ⟨T, ?_⟩⟩
  ext T'
  rw [Feec.Mesh.SimplicialMesh.mem_cofaces, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩; exact hu T' h1 (by rw [vertexSet_eq]; exact h2)
  · rintro rfl; exact ⟨hT, by rw [← vertexSet_eq]; exact hFT⟩

omit [NeZero n] in
/-- A boundary facet lies in a single simplex. -/
theorem eq_of_isBoundaryFacet {F : Finset (Fin n → ℝ)} (hF : (M.toFeec Ω hdom).IsBoundaryFacet F)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) (hFT : F ⊆ vertexSet T) :
    ∀ T' ∈ M.simplices, F ⊆ vertexSet T' → T' = T := by
  rw [Feec.Mesh.SimplicialMesh.isBoundaryFacet_iff] at hF
  obtain ⟨T₀, hT₀⟩ := Finset.card_eq_one.1 hF.2
  have hmem : ∀ T' ∈ M.simplices, F ⊆ vertexSet T' → T' = T₀ := fun T' h1 h2 => by
    have : T' ∈ (M.toFeec Ω hdom).cofaces F :=
      (Feec.Mesh.SimplicialMesh.mem_cofaces _).2 ⟨h1, by rw [← vertexSet_eq]; exact h2⟩
    rw [hT₀] at this; exact Finset.mem_singleton.1 this
  intro T' h1 h2
  rw [hmem T' h1 h2, hmem T hT hFT]

omit [NeZero n] in
/-- **The glued space `V̊ₕᵏ` is the finite element space with vanishing boundary traces.** -/
theorem mem_V₀_iff {k : ℤ} (u : L2Form Ω k) :
    u ∈ (polyElement n S.toFeec).V₀ (M.toFeec Ω hdom) k ↔
      u ∈ femSpace Ω M S M.boundaryFacets k := by
  constructor
  · rintro ⟨v, rfl⟩
    set w : (polyElement n S.toFeec).Piecewise (M.toFeec Ω hdom) k.toNat := v.1 with hw
    have hv1 : w ∈ (polyElement n S.toFeec).globalSpace (M.toFeec Ω hdom) k.toNat :=
      (polyElement n S.toFeec).globalSpace₀_le (M.toFeec Ω hdom) k.toNat v.2
    have hpieces := isFemPieces_glue S M Ω hdom ⟨w, hv1⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    refine ⟨_, hpieces, fun T hT F hFT hF hΓ x hx => ?_⟩
    rw [LocalElement.extendPW_of_mem _ (M.toFeec Ω hdom) _ hT, traceEq_iff]
    exact (polyElement n S.toFeec).tangentialTraceEq_zero_of_mem_globalSpace₀ (M.toFeec Ω hdom)
      v.2 (isBoundaryFacet_of M Ω hdom hT hFT hF ((mem_boundaryFacets_iff M hT hFT).1 hΓ).2)
      ⟨T, hT⟩ (by rw [← vertexSet_eq]; exact hFT) x hx
  · rintro ⟨p, hp, hb⟩
    refine ⟨⟨ofPieces S M Ω hdom p hp.1, ⟨ofPieces_mem S M Ω hdom hp,
      fun T F hF hFT g hg i => ?_⟩⟩, glue_ofPieces S M Ω hdom hp⟩
    rw [LocalElement.localDof_apply]
    have hFT' : F ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) := by
      rw [vertexSet_eq]; exact hFT
    have h := S.toFeec.dof_congr i
      (w := ⟨p T, S.toFeec.space_le_contForms n k.toNat ((mem_space_iff S (T := T) _ _).2 (hp.1 T T.2))⟩)
      (η := 0) fun x hx => by
      have := hb T T.2 F hFT' hF.1.1 ((mem_boundaryFacets_iff M T.2 hFT').2
        ⟨hF.1.1, eq_of_isBoundaryFacet M Ω hdom hF T.2 hFT'⟩) x
        (convexHull_mono (Finset.coe_subset.2 hg) hx)
      exact ((traceEq_iff _ _ _ _).1 this).mono hg
    exact h.trans (map_zero _)

end FEEC
