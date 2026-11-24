module

public import Solution.Dof
public import Solution.Spaces
public import Feec.FiniteElement.PolyAssembly
public import Feec.FiniteElement.PolyComplex

/-!
# The bridge for the assembly

`FEEC.assembly` from `Feec.FiniteElement.PolyAssembly`, for the admissible sequence `S.toFeec`
and the mesh `M.toFeec`: conformity by moments is
`Feec.FiniteElement.PolySeq.tangentialTraceEq_tfae` on the common vertices of two simplices
(through `traceEq_iff`, `faceMoment_eq` and `PolySeq.testForms_eq`); an assignment of moments is
taken on every simplex by exactly one form
(`Feec.FiniteElement.PolySeq.existsUnique_vertexMoment_eq`), these forms have single-valued
traces (conformity by moments) and glue to an element of the finite element space
(`ofPieces_mem_of_traceEq`, `isFemPieces_glue`), which is unique, a finite element form being
almost everywhere its pieces (`Feec.FiniteElement.ae_eq_restrict_domain_iff`); the pieces are
unique by the injectivity of the gluing (`Feec.FiniteElement.LocalElement.glue_injective`); and
the finite element space is the glued space of `Feec.FiniteElement.polyElement`
(`mem_V_iff`), of dimension `Feec.FiniteElement.LocalElement.finrank_V` counted by
`Feec.FiniteElement.PolySeq.card_globalDofIdx` (the faces through `SimplicialMesh.faces_eq`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2 (Theorem 5.7)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set Finset

@[expose] public noncomputable section

namespace FEEC

open Feec.FiniteElement

variable {n : ℕ}

theorem assembly_of_feec (M : SimplicialMesh n) (S : PolySeq) (k : ℕ) :
    (∀ p : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n, (∀ T ∈ M.simplices, p T ∈ S.space n k) →
      List.TFAE [∀ T ∈ M.simplices, ∀ T' ∈ M.simplices,
          ∀ x ∈ convexHull ℝ ((vertexSet T ∩ vertexSet T' : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)),
            TraceEq (vertexSet T ∩ vertexSet T') k (p T x) (p T' x),
        ∀ T ∈ M.simplices, ∀ T' ∈ M.simplices, ∀ m,
          ∀ g ∈ (vertexSet T ∩ vertexSet T').powersetCard (m + 1),
            ∀ v : Fin (m + 1) → Fin n → ℝ, Set.range v = g → ∀ η ∈ S.testForms k m,
              faceMoment v η (p T) = faceMoment v η (p T'),
        ∀ T ∈ M.simplices, ∀ T' ∈ M.simplices, ∀ m,
          ∀ g ∈ (vertexSet T ∩ vertexSet T').powersetCard (m + 1),
            ∃ v : Fin (m + 1) → Fin n → ℝ, Set.range v = g ∧ ∀ η ∈ S.testForms k m,
              faceMoment v η (p T) = faceMoment v η (p T')]) ∧
    (∀ v : ∀ m, Finset (Fin n → ℝ) → Fin (m + 1) → Fin n → ℝ,
      (∀ m, ∀ g ∈ M.faces m, Set.range (v m g) = g) →
      ∀ c : ∀ m, Finset (Fin n → ℝ) → Module.Dual ℝ (S.testForms k m),
        ∃! u : L2Form M.domain k, ∃ p, IsFemPieces M.domain M S k u p ∧
          ∀ T ∈ M.simplices, ∀ m, ∀ g ∈ (vertexSet T).powersetCard (m + 1),
            ∀ η : S.testForms k m, faceMoment (v m g) η (p T) = c m g η) ∧
    (IsOpen M.domain → (∀ (u : L2Form M.domain k) p p', IsFemPieces M.domain M S k u p →
        IsFemPieces M.domain M S k u p' → ∀ T ∈ M.simplices, p T = p' T) ∧
      ∃ V : Submodule ℝ (L2Form M.domain k), FiniteDimensional ℝ V ∧
        (V : Set (L2Form M.domain k)) = femSpace M.domain M S ∅ k ∧
        Module.finrank ℝ V =
          ∑ m ∈ Finset.range (n + 1), (M.faces m).card * Module.finrank ℝ (S.testForms k m)) := by
  refine ⟨fun p hp => ?_, fun v hv c => ?_, fun hΩ => ?_⟩
  · have hw : ∀ T ∈ M.simplices, p T ∈ S.toFeec.space n k := fun T hT => by
      rw [← S.space_eq]; exact hp T hT
    have key : ∀ T ∈ M.simplices, ∀ T' ∈ M.simplices, List.TFAE
        [∀ x ∈ convexHull ℝ ((vertexSet T ∩ vertexSet T' : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)),
          TangentialTraceEq (vertexSet T ∩ vertexSet T') k (p T x) (p T' x),
        ∀ m, ∀ g ∈ (vertexSet T ∩ vertexSet T').powersetCard (m + 1),
          ∀ q : Fin (m + 1) → Fin n → ℝ, Set.range q = g → ∀ η ∈ S.toFeec.test k m,
            vertexMoment q η (p T) = vertexMoment q η (p T'),
        ∀ m, ∀ g ∈ (vertexSet T ∩ vertexSet T').powersetCard (m + 1),
          ∃ q : Fin (m + 1) → Fin n → ℝ, Set.range q = g ∧ ∀ η ∈ S.toFeec.test k m,
            vertexMoment q η (p T) = vertexMoment q η (p T')] := fun T hT T' hT' =>
      S.toFeec.tangentialTraceEq_tfae (by rw [← vertexSet_eq]; exact inter_subset_left)
        (hw T hT) (hw T' hT')
    simp only [traceEq_iff, faceMoment_eq, S.testForms_eq]
    tfae_have 1 → 2 := fun h T hT T' hT' => ((key T hT T' hT').out 1 2).1 (h T hT T' hT')
    tfae_have 2 → 3 := fun h T hT T' hT' => ((key T hT T' hT').out 2 3).1 (h T hT T' hT')
    tfae_have 3 → 1 := fun h T hT T' hT' => ((key T hT T' hT').out 3 1).1 (h T hT T' hT')
    tfae_finish
  · classical
    set E := polyElement n S.toFeec
    set M' := M.toFeec M.domain rfl
    let c' : ∀ m, Finset (Fin n → ℝ) → Module.Dual ℝ (S.toFeec.test k m) := fun m g =>
      (c m g).comp (LinearEquiv.ofEq _ _ (S.testForms_eq k m).symm).toLinearMap
    have hvT : ∀ T ∈ M.simplices, ∀ m, ∀ g ∈ (Feec.Mesh.vertexSet T).powersetCard (m + 1),
        Set.range (v m g) = g := fun T hT m g hg =>
      hv m g (Finset.mem_biUnion.2 ⟨T, hT, by rwa [vertexSet_eq]⟩)
    have hmom : ∀ (T : Affine.Simplex ℝ (Fin n → ℝ) n) (w : FormField n),
        (∀ m, ∀ g ∈ (vertexSet T).powersetCard (m + 1), ∀ η : S.testForms k m,
          faceMoment (v m g) η w = c m g η) ↔
        ∀ m, ∀ g ∈ (Feec.Mesh.vertexSet T).powersetCard (m + 1), ∀ η : S.toFeec.test k m,
          vertexMoment (v m g) η w = c' m g η := fun T w => by
      rw [vertexSet_eq]
      refine forall_congr' fun m => forall₂_congr fun g _ => ⟨fun h η => ?_, fun h η => ?_⟩
      · have := h (LinearEquiv.ofEq _ _ (S.testForms_eq k m).symm η)
        rw [faceMoment_eq] at this
        exact this
      · have := h (LinearEquiv.ofEq _ _ (S.testForms_eq k m) η)
        rw [faceMoment_eq]
        exact this
    choose w hw hwu using fun T (hT : T ∈ M.simplices) =>
      S.toFeec.existsUnique_vertexMoment_eq T k (hvT T hT) c'
    let p : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n := fun T =>
      if hT : T ∈ M.simplices then (w T hT : FormField n) else 0
    have hpT : ∀ T (hT : T ∈ M.simplices), p T = w T hT := fun T hT => dite_eq_left hT
    have hpS : ∀ T ∈ M.simplices, p T ∈ S.space n (k : ℤ).toNat := fun T hT => by
      rw [hpT T hT, S.space_eq]; exact (w T hT).2
    have htr : ∀ T ∈ M.simplices, ∀ T' ∈ M.simplices,
        ∀ x ∈ convexHull ℝ ((vertexSet T ∩ vertexSet T' : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)),
          TraceEq (vertexSet T ∩ vertexSet T') (k : ℤ).toNat (p T x) (p T' x) := by
      intro T hT T' hT' x hx
      rw [traceEq_iff]
      have hg : vertexSet T ∩ vertexSet T' ⊆ Feec.Mesh.vertexSet T := by
        rw [← vertexSet_eq]; exact inter_subset_left
      have hg' : vertexSet T ∩ vertexSet T' ⊆ Feec.Mesh.vertexSet T' := by
        rw [← vertexSet_eq]; exact inter_subset_right
      have hw1 : p T ∈ S.toFeec.space n k := by rw [hpT T hT]; exact (w T hT).2
      have hw2 : p T' ∈ S.toFeec.space n k := by rw [hpT T' hT']; exact (w T' hT').2
      have key := (S.toFeec.tangentialTraceEq_tfae hg hw1 hw2).out 3 1
      refine key.1 (fun m g hgc => ?_) x hx
      obtain ⟨hgc1, hgc2⟩ := mem_powersetCard.1 hgc
      have h1 : g ∈ (Feec.Mesh.vertexSet T).powersetCard (m + 1) :=
        mem_powersetCard.2 ⟨hgc1.trans hg, hgc2⟩
      have h2 : g ∈ (Feec.Mesh.vertexSet T').powersetCard (m + 1) :=
        mem_powersetCard.2 ⟨hgc1.trans hg', hgc2⟩
      refine ⟨v m g, hvT T hT m g h1, fun η hη => ?_⟩
      rw [hpT T hT, hpT T' hT']
      exact (hw T hT m g h1 ⟨η, hη⟩).trans (hw T' hT' m g h2 ⟨η, hη⟩).symm
    have hmem := ofPieces_mem_of_traceEq S M M.domain rfl hpS htr
    refine ⟨E.glue M' k (ofPieces S M M.domain rfl p hpS),
      ⟨_, isFemPieces_glue S M M.domain rfl ⟨_, hmem⟩, fun T hT m g hg η => ?_⟩, ?_⟩
    · rw [LocalElement.extendPW_of_mem _ M' _ hT]
      change faceMoment (v m g) η (p T) = c m g η
      rw [hpT T hT]
      exact (hmom T _).2 (hw T hT) m g hg η
    · rintro u' ⟨p', hp', hp'c⟩
      have hpp : ∀ T ∈ M.simplices, p' T = p T := fun T hT =>
        (congrArg Subtype.val (hwu T hT ⟨p' T, by rw [← S.space_eq]; exact hp'.1 T hT⟩
          ((hmom T (p' T)).1 (hp'c T hT)))).trans (hpT T hT).symm
      refine PiLp.ext fun s => Lp.ext ((ae_eq_restrict_domain_iff M').2 fun T hT => ?_)
      have h2 := LocalElement.glue_ae_eq E M' (ofPieces S M M.domain rfl p hpS) hT s
      refine (hp'.2.1 T hT s).trans ?_
      rw [hpp T hT]
      exact h2.symm
  · set E := polyElement n S.toFeec
    set M' := M.toFeec M.domain rfl
    refine ⟨fun u p p' hp hp' T hT => ?_, E.V M' k,
      inferInstanceAs (FiniteDimensional ℝ (E.V M' k)), ?_, ?_⟩
    · have h0 := E.glue_injective M' hΩ k (a₁ := ofPieces S M M.domain rfl p hp.1)
        (a₂ := ofPieces S M M.domain rfl p' hp'.1)
        (by rw [glue_ofPieces S M M.domain rfl hp, glue_ofPieces S M M.domain rfl hp'])
      exact congrArg Subtype.val (congrFun h0 ⟨T, hT⟩)
    · ext u
      exact mem_V_iff S M M.domain rfl u
    · have h1 := E.finrank_V M' hΩ k
      rw [PolySeq.card_globalDofIdx] at h1
      refine h1.trans (sum_congr rfl fun m _ => ?_)
      rw [← SimplicialMesh.faces_eq M M.domain rfl m, Set.ncard_coe_finset, S.testForms_eq]

end FEEC
