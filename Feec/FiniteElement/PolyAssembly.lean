module

public import Feec.FiniteElement.PolyElement

/-!
# Assembly of the polynomial families from their face moments

For an admissible sequence `S`, the face moments against the test forms of `S` determine the
tangential traces and are unisolvent, for every choice of enumerations of the faces.

## Main results

* `PolySeq.tangentialTraceEq_tfae`: conformity by moments.
* `PolySeq.existsUnique_vertexMoment_eq`: exactly one form of `S_k` has prescribed face moments.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]

Bibliography: [references.bib](../../docs/references.bib)
-/

open MeasureTheory Set Finset

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh

variable {n : ℕ}

namespace PolySeq

variable (S : PolySeq)

theorem vertexMoment_comp_perm_eq {k m : ℕ} {q : Fin (m + 1) → Fin n → ℝ} {ω ω' : FormField n}
    (h : ∀ η ∈ S.test k m, vertexMoment q η ω = vertexMoment q η ω')
    (π : Equiv.Perm (Fin (m + 1))) {η : FormField m} (hη : η ∈ S.test k m) :
    vertexMoment (q ∘ π) η ω = vertexMoment (q ∘ π) η ω' := by
  rw [vertexMoment_comp_perm, vertexMoment_comp_perm, h _ (S.affinePullback_mem_test _ _ k hη)]

theorem vertexMoment_lexEnum_eq {g : Finset (Fin n → ℝ)} {k m : ℕ} (hc : #g = m + 1)
    {q : Fin (m + 1) → Fin n → ℝ} (hq : Set.range q = g) {ω ω' : FormField n}
    (h : ∀ η ∈ S.test k m, vertexMoment q η ω = vertexMoment q η ω') {η : FormField m}
    (hη : η ∈ S.test k m) :
    vertexMoment (lexEnum g m) η ω = vertexMoment (lexEnum g m) η ω' := by
  obtain ⟨π, hπ⟩ := exists_lexEnum_eq_comp_perm hc hq
  rw [hπ]
  exact S.vertexMoment_comp_perm_eq h π hη

/-- **Conformity by moments**: forms of `S_k` have the same tangential trace on a face `g` iff
their moments on the faces of `g` agree, along one or every enumeration. [AFW2010], §5.2 -/
theorem tangentialTraceEq_tfae {T : Affine.Simplex ℝ (Fin n → ℝ) n} {g : Finset (Fin n → ℝ)}
    (hg : g ⊆ vertexSet T) {k : ℕ} {w w' : FormField n} (hw : w ∈ S.space n k)
    (hw' : w' ∈ S.space n k) :
    List.TFAE [∀ x ∈ convexHull ℝ (g : Set (Fin n → ℝ)), TangentialTraceEq g k (w x) (w' x),
      ∀ m, ∀ g' ∈ g.powersetCard (m + 1), ∀ q : Fin (m + 1) → Fin n → ℝ, Set.range q = g' →
        ∀ η ∈ S.test k m, vertexMoment q η w = vertexMoment q η w',
      ∀ m, ∀ g' ∈ g.powersetCard (m + 1), ∃ q : Fin (m + 1) → Fin n → ℝ, Set.range q = g' ∧
        ∀ η ∈ S.test k m, vertexMoment q η w = vertexMoment q η w'] := by
  tfae_have 1 → 2 := fun h m g' hg' q hq η _ => vertexMoment_congr q
    (fun l => (mem_powersetCard.1 hg').1
      (Finset.mem_coe.1 (show q l ∈ (g' : Set (Fin n → ℝ)) from hq ▸ Set.mem_range_self l)))
    η (PolyKind.isDeg_of_mem_space hw) (PolyKind.isDeg_of_mem_space hw') h
  tfae_have 2 → 3 := fun h m g' hg' => ⟨lexEnum g' m, range_lexEnum (mem_powersetCard.1 hg').2,
    h m g' hg' _ (range_lexEnum (mem_powersetCard.1 hg').2)⟩
  tfae_have 3 → 1 := fun h => by
    rcases g.eq_empty_or_nonempty with rfl | hne
    · intro x hx
      simp at hx
    obtain ⟨j, hj⟩ : ∃ j, #g = j + 1 := ⟨#g - 1, by have := hne.card_pos; omega⟩
    refine S.tangentialTraceEq_of_dof_eq_face hg hj hw hw' fun g' hg' i => ?_
    have hc : #g' = #g' - 1 + 1 := by have := card_pos.2 i.2; omega
    obtain ⟨q, hq, hqe⟩ := h (#g' - 1) g' (mem_powersetCard.2 ⟨hg', hc⟩)
    rw [S.dof_apply, S.dof_apply]
    change vertexMoment _ _ (degField k w) = vertexMoment _ _ (degField k w')
    rw [degField_eq_self (PolyKind.isDeg_of_mem_space hw),
      degField_eq_self (PolyKind.isDeg_of_mem_space hw')]
    exact S.vertexMoment_lexEnum_eq hc hq hqe (S.testBasis k _ i.1).2
  tfae_finish

theorem eq_zero_of_vertexMoment_eq_zero (T : Affine.Simplex ℝ (Fin n → ℝ) n) {k : ℕ}
    {w : FormField n} (hw : w ∈ S.space n k)
    (h : ∀ m, ∀ g ∈ (vertexSet T).powersetCard (m + 1), ∃ q : Fin (m + 1) → Fin n → ℝ,
      Set.range q = g ∧ ∀ η ∈ S.test k m, vertexMoment q η w = 0) : w = 0 := by
  classical
  suffices hu : (⟨w, hw⟩ : S.space n k) = 0 from congrArg Subtype.val hu
  refine (isUnisolvent_iff_forall_eq_zero _ (S.card_sigma_dofIdx T k).symm).1
    (S.isUnisolvent_dof T k) ⟨w, hw⟩ fun p => ?_
  obtain ⟨⟨g, hgT⟩, i⟩ := p
  have hc : #g = #g - 1 + 1 := by have := card_pos.2 (show g.Nonempty from i.2); omega
  obtain ⟨q, hq, hq0⟩ := h (#g - 1) g (mem_powersetCard.2 ⟨mem_powerset.1 hgT, hc⟩)
  have h0 : ∀ η ∈ S.test k (#g - 1), vertexMoment q η w = vertexMoment q η 0 := fun η hη => by
    rw [hq0 η hη]
    simpa using (vertexMoment_smul_left q η 0 0).symm
  change S.dof g k i ⟨w, S.space_le_contForms n k hw⟩ = 0
  rw [S.dof_apply]
  change vertexMoment (lexEnum g (#g - 1)) _ (degField k w) = 0
  rw [degField_eq_self (PolyKind.isDeg_of_mem_space hw),
    S.vertexMoment_lexEnum_eq hc hq h0 (S.testBasis k _ i.1).2]
  simpa using vertexMoment_smul_left (lexEnum g (#g - 1)) _ 0 0

/-- **Prescribed moments**: for enumerations of the faces of an `n`-simplex and functionals on
their test forms, exactly one form of `S_k` has these moments. -/
theorem existsUnique_vertexMoment_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ)
    {q : ∀ m, Finset (Fin n → ℝ) → Fin (m + 1) → Fin n → ℝ}
    (hq : ∀ m, ∀ g ∈ (vertexSet T).powersetCard (m + 1), Set.range (q m g) = g)
    (c : ∀ m, Finset (Fin n → ℝ) → Module.Dual ℝ (S.test k m)) :
    ∃! w : S.space n k, ∀ m, ∀ g ∈ (vertexSet T).powersetCard (m + 1), ∀ η : S.test k m,
      vertexMoment (q m g) η w = c m g η := by
  classical
  have hlt : ∀ {m} {g : Finset (Fin n → ℝ)}, g ∈ (vertexSet T).powersetCard (m + 1) →
      m < n + 1 := fun {m g} hg => by
    obtain ⟨h1, h2⟩ := mem_powersetCard.1 hg
    have := Finset.card_le_card h1
    rw [h2, card_vertexSet] at this
    omega
  let ι := Σ m : Fin (n + 1), ((vertexSet T).powersetCard (m + 1) : Finset (Finset (Fin n → ℝ)))
  let B : ∀ i : ι, S.space n k →ₗ[ℝ] Module.Dual ℝ (S.test k i.1) := fun i =>
    LinearMap.mk₂ ℝ (fun (w : S.space n k) (η : S.test k i.1) => vertexMoment (q i.1 i.2) η w)
      (fun w₁ w₂ η => vertexMoment_add_left _ (PolyKind.contDiff_of_mem_test η.2).continuous
        (PolyKind.contDiff_of_mem_space w₁.2).continuous
        (PolyKind.contDiff_of_mem_space w₂.2).continuous)
      (fun a w η => vertexMoment_smul_left _ _ a _)
      (fun w η₁ η₂ => vertexMoment_add_right _ (PolyKind.contDiff_of_mem_test η₁.2).continuous
        (PolyKind.contDiff_of_mem_test η₂.2).continuous
        (PolyKind.contDiff_of_mem_space w.2).continuous)
      (fun a w η => vertexMoment_smul_right _ _ a _)
  let Φ : S.space n k →ₗ[ℝ] ∀ i : ι, Module.Dual ℝ (S.test k i.1) := LinearMap.pi B
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine Subtype.ext (S.eq_zero_of_vertexMoment_eq_zero T w.2 fun m g hg =>
      ⟨q m g, hq m g hg, fun η hη => ?_⟩)
    exact LinearMap.congr_fun (congr_fun hw ⟨⟨m, hlt hg⟩, ⟨g, hg⟩⟩) ⟨η, hη⟩
  have hdim : Module.finrank ℝ (S.space n k) =
      Module.finrank ℝ (∀ i : ι, Module.Dual ℝ (S.test k i.1)) := by
    rw [Module.finrank_pi_fintype, PolyKind.finrank_space_eq_sum _ (S.one_le_deg k),
      Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range
        (fun m => (n + 1).choose (m + 1) * Module.finrank ℝ (S.test k m)) (n + 1)]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Subspace.dual_finrank_eq]
    rw [Finset.sum_coe_sort ((vertexSet T).powersetCard (m + 1))
      (fun _ => Module.finrank ℝ (S.test k m)), Finset.sum_const, card_powersetCard,
      card_vertexSet, smul_eq_mul]
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
    fun i => c i.1 i.2
  refine ⟨w, fun m g hg η => ?_, fun w' hw' => hinj ?_⟩
  · exact LinearMap.congr_fun (congr_fun hw ⟨⟨m, hlt hg⟩, ⟨g, hg⟩⟩) η
  · exact (funext fun i => LinearMap.ext fun η => hw' i.1 i.2 i.2.2 η).trans hw.symm

end PolySeq

end Feec.FiniteElement
