module

public import Feec.FiniteElement.PolyElement

/-!
# Assembly of the polynomial families from their face moments

For an admissible sequence `S` (`Feec.FiniteElement.PolySeq`), the moments
`ω ↦ ∫_{T̂_m} F_q^* ω ∧ η` along vertex families `q` (`Feec.FiniteElement.vertexMoment`) against
the test forms `η ∈ S.test k m` are the degrees of freedom of the element family
`Feec.FiniteElement.polyElement n S`. Along points of a face they only see the tangential traces
on the face (`vertexMoment_congr`), and their agreement against all test forms survives a
reordering of the points (`PolySeq.vertexMoment_comp_perm_eq`, `PolySeq.vertexMoment_lexEnum_eq`:
the test forms are affinely invariant). Hence:

* **conformity by moments** ([AFW2010], §5.2): for two forms of `S_k` and a face `g` of an
  `n`-simplex, the agreement of the tangential traces on `g`, of the moments on every face of `g`
  along every enumeration of its vertices, and along one enumeration, are equivalent
  (`PolySeq.tangentialTraceEq_tfae`);
* **unisolvence along any orderings**: a form of `S_k` whose moments vanish on every face of an
  `n`-simplex, along one enumeration of the face, is zero
  (`PolySeq.eq_zero_of_vertexMoment_eq_zero`), and for every enumeration of the faces and every
  assignment of a linear functional on the test forms to each face exactly one form of `S_k` has
  these moments (`PolySeq.existsUnique_vertexMoment_eq`).

Together with the dimension of the glued spaces (`LocalElement.finrank_V`) and the number of the
global degrees of freedom (`PolySeq.card_globalDofIdx`, in `Feec.FiniteElement.PolyComplex`),
they assemble the finite element spaces of `S` from the face moments.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §4.5–4.6, §5.1
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2 (Theorem 5.5; the spaces defined by single-valued moments)

Bibliography: [references.bib](../../docs/references.bib)
-/

open MeasureTheory Set Finset

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh

variable {n : ℕ}

namespace PolySeq

variable (S : PolySeq)

/-- **Moments along a reordering**: if the moments of `ω` and `ω'` along `q` agree against all test
forms on `m`-faces, so do those along `q ∘ π` (`vertexMoment_comp_perm`: the reordering maps the
test forms by an affine map of `ℝᵐ`, which preserves them, `PolySeq.affinePullback_mem_test`). -/
theorem vertexMoment_comp_perm_eq {k m : ℕ} {q : Fin (m + 1) → Fin n → ℝ} {ω ω' : FormField n}
    (h : ∀ η ∈ S.test k m, vertexMoment q η ω = vertexMoment q η ω')
    (π : Equiv.Perm (Fin (m + 1))) {η : FormField m} (hη : η ∈ S.test k m) :
    vertexMoment (q ∘ π) η ω = vertexMoment (q ∘ π) η ω' := by
  rw [vertexMoment_comp_perm, vertexMoment_comp_perm, h _ (S.affinePullback_mem_test _ _ k hη)]

/-- If the moments of `ω` and `ω'` along an enumeration of `g` agree against all test forms, so do
those along the lexicographic enumeration of `g`. -/
theorem vertexMoment_lexEnum_eq {g : Finset (Fin n → ℝ)} {k m : ℕ} (hc : #g = m + 1)
    {q : Fin (m + 1) → Fin n → ℝ} (hq : Set.range q = g) {ω ω' : FormField n}
    (h : ∀ η ∈ S.test k m, vertexMoment q η ω = vertexMoment q η ω') {η : FormField m}
    (hη : η ∈ S.test k m) :
    vertexMoment (lexEnum g m) η ω = vertexMoment (lexEnum g m) η ω' := by
  obtain ⟨π, hπ⟩ := exists_lexEnum_eq_comp_perm hc hq
  rw [hπ]
  exact S.vertexMoment_comp_perm_eq h π hη

/-- **Conformity by moments** ([AFW2010], §5.2): for two forms of `S_k` and a face `g` of an
`n`-simplex `T`, the following are equivalent: their tangential traces on `g` agree; their moments
on every face of `g`, along every enumeration of its vertices, agree against all test forms; and
along one enumeration of each face of `g` (the degrees of freedom of the faces of `g` determine the
trace, `tangentialTraceEq_of_dof_eq_face`, and the reorderings act on the test forms,
`vertexMoment_lexEnum_eq`). -/
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

/-- **Unisolvence along any orderings**: a form of `S_k` whose moments vanish on every face `g` of
an `n`-simplex `T`, along one enumeration of `g` and against all test forms, is zero
(`isUnisolvent_dof`, the enumerations being reordered by `vertexMoment_comp_perm_eq`). -/
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

/-- **Prescribed moments on a simplex**: for an enumeration `q m g` of the vertices of every
`m`-face `g` of an `n`-simplex `T` and a linear functional `c m g` on the test forms of each face,
exactly one form `w` of `S_k` has the moments `∫_{T̂_m} F_{q m g}^* w ∧ η = c m g η`: the moments
are injective (`eq_zero_of_vertexMoment_eq_zero`) and as many as the dimension
(`PolyKind.finrank_space_eq_sum`). -/
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
