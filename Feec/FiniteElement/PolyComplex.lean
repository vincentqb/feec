module

public import Feec.Algebra.PolynomialFormClassical
public import Feec.FiniteElement.AffineInvariantForm
public import Feec.FiniteElement.PolyElement

/-!
# Higher-order finite element complexes on meshes

For an admissible sequence `S`, `polyElement n S` assembles subcomplexes of `HΛ(Ω)` on meshes of an
open `Ω ⊆ ℝⁿ` and, with vanishing boundary DOFs, of `H̊Λ(Ω)` for strictly star-shaped `Ω`.

## Main results

* `PolySeq.exists_extDeriv_eq`: exactness of the polynomial complex in positive degree.
* `PolySeq.finrank_globalSpace`: the dimension of the global spaces.
* `whitneySubcomplex_eq_trimmed`: the Whitney complex is the trimmed complex of degree one.
* `PolySeq.finrank_V₀_freudenthalMesh_pos_of_two_le`: `V̊ₕᵏ ≠ 0` for `k ≤ n` at level `N ≥ 2`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [D. N. Arnold, A. Logg, *Periodic table of the finite elements*][ArnoldLogg2014]

Bibliography: [references.bib](../../docs/references.bib)
-/

open MeasureTheory Set Finset

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh Feec.Domain

variable {n : ℕ}

namespace PolySeq

/-- The admissible sequence of the kinds `κ` ending in `P_sΛⁿ`. [ArnoldLogg2014] -/
def ofKinds (n : ℕ) (κ : ℕ → PolyKind) (s : ℕ) : PolySeq where
  kind k := if k < n then κ k else .trimmed
  deg k := s + 1 + #{j ∈ Finset.Ioo k n | κ j = .full}
  one_le_deg _ := by omega
  transition k := by
    by_cases hk : k + 1 < n
    · have hI : Finset.Ioo k n = insert (k + 1) (Finset.Ioo (k + 1) n) := by
        ext j; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega
      rw [hI, Finset.filter_insert]
      cases h : κ (k + 1)
      · refine Or.inr ⟨by simp [hk], ?_⟩
        simp only [↓reduceIte]
        rw [Finset.card_insert_of_notMem (by simp)]
        omega
      · exact Or.inl ⟨by simp [hk], by simp⟩
    · have h0 : ∀ i, k ≤ i → Finset.Ioo i n = ∅ := fun i hi => by
        ext j; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
      rw [h0 k le_rfl, h0 (k + 1) (by omega)]
      exact Or.inl ⟨by simp [hk], rfl⟩

variable {κ : ℕ → PolyKind} {s : ℕ}

theorem ofKinds_kind_of_lt {k : ℕ} (hk : k < n) : (ofKinds n κ s).kind k = κ k := by
  simp [ofKinds, hk]

theorem ofKinds_deg (k : ℕ) :
    (ofKinds n κ s).deg k = s + 1 + #{j ∈ Finset.Ioo k n | κ j = .full} := rfl

theorem ofKinds_space_top : (ofKinds n κ s).space n n = polySpace n s n := by
  change (if n < n then κ n else .trimmed).space n (s + 1 + #{j ∈ Finset.Ioo n n | κ j = .full})
    n = _
  simp only [lt_irrefl, ↓reduceIte, Finset.Ioo_self, Finset.filter_empty, Finset.card_empty,
    add_zero, PolyKind.space_trimmed]
  rw [polyMinusSpace_top (by omega), Nat.add_sub_cancel]

/-- The trimmed sequence `P_r⁻Λ⁰ → P_r⁻Λ¹ → ⋯ → P_r⁻Λⁿ` (`r ≥ 1`). -/
def trimmed (r : ℕ) (hr : 1 ≤ r) : PolySeq where
  kind _ := .trimmed
  deg _ := r
  one_le_deg _ := hr
  transition _ := Or.inl ⟨rfl, rfl⟩

theorem trimmed_eq_ofKinds {r : ℕ} (hr : 1 ≤ r) :
    trimmed r hr = ofKinds n (fun _ => .trimmed) (r - 1) := by
  ext k
  · simp only [trimmed, ofKinds, ite_self]
  · simp only [trimmed, ofKinds, reduceCtorEq, Finset.filter_false, Finset.card_empty, add_zero]
    omega

/-- The full sequence `P_rΛ⁰ → P_{r-1}Λ¹ → ⋯ → P_{r-n}Λⁿ` on `ℝⁿ` (`n ≤ r`). -/
def full (n r : ℕ) (_hr : n ≤ r) : PolySeq := ofKinds n (fun _ => .full) (r - n)

theorem full_kind {r : ℕ} (hr : n ≤ r) {k : ℕ} (hk : k < n) : (full n r hr).kind k = .full :=
  ofKinds_kind_of_lt hk

theorem full_deg {r : ℕ} (hr : n ≤ r) {k : ℕ} (hk : k < n) : (full n r hr).deg k = r - k := by
  rw [full, ofKinds_deg, Finset.filter_true_of_mem fun _ _ => rfl, Nat.card_Ioo]
  omega

theorem full_space {r : ℕ} (hr : n ≤ r) {k : ℕ} (hk : k ≤ n) :
    (full n r hr).space n k = polySpace n (r - k) k := by
  rcases hk.lt_or_eq with hk | rfl
  · change ((full n r hr).kind k).space n ((full n r hr).deg k) k = _
    rw [full_kind hr hk, full_deg hr hk, PolyKind.space_full]
  · rw [full, ofKinds_space_top]

/-- The sequence `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ² → P₁⁻Λ³`. [QuennevilleBelair2015], Tables 5.1, 6.1 -/
def lowestOrder : PolySeq where
  kind k := if k = 0 then .full else .trimmed
  deg _ := 1
  one_le_deg _ := le_rfl
  transition _ := Or.inl ⟨by simp, rfl⟩

/-- The sequence `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³`. [QuennevilleBelair2015], Tables 5.1, 6.1 -/
def lagrangeP2 : PolySeq where
  kind k := if k = 0 ∨ k = 2 then .full else .trimmed
  deg k := if k ≤ 1 then 2 else 1
  one_le_deg k := by split_ifs <;> omega
  transition k := by
    rcases k with _ | _ | _ | k
    · exact Or.inl ⟨by simp, rfl⟩
    · exact Or.inr ⟨by simp, rfl⟩
    · exact Or.inl ⟨by simp, rfl⟩
    · exact Or.inl ⟨by simp, by simp⟩

@[simp] theorem lagrangeP2_kind_zero : lagrangeP2.kind 0 = .full := rfl
@[simp] theorem lagrangeP2_kind_one : lagrangeP2.kind 1 = .trimmed := rfl
@[simp] theorem lagrangeP2_kind_two : lagrangeP2.kind 2 = .full := rfl
@[simp] theorem lagrangeP2_kind_three : lagrangeP2.kind 3 = .trimmed := rfl
@[simp] theorem lagrangeP2_deg_zero : lagrangeP2.deg 0 = 2 := rfl
@[simp] theorem lagrangeP2_deg_one : lagrangeP2.deg 1 = 2 := rfl
@[simp] theorem lagrangeP2_deg_two : lagrangeP2.deg 2 = 1 := rfl
@[simp] theorem lagrangeP2_deg_three : lagrangeP2.deg 3 = 1 := rfl

theorem lowestOrder_eq_ofKinds (hn : 1 ≤ n) :
    lowestOrder = ofKinds n (fun k => if k = 0 then .full else .trimmed) 0 := by
  ext k
  · simp only [lowestOrder, ofKinds]
    split_ifs <;> first | rfl | omega
  · simp only [lowestOrder, ofKinds, zero_add, left_eq_add, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, Finset.mem_Ioo]
    intro j hj
    simp [show j ≠ 0 by omega]

theorem lagrangeP2_eq_ofKinds :
    lagrangeP2 = ofKinds 3 (fun k => if k = 0 ∨ k = 2 then .full else .trimmed) 0 := by
  ext k
  · rcases k with _ | _ | _ | k
    · rfl
    · rfl
    · rfl
    · simp [lagrangeP2, ofKinds]
  · rcases k with _ | _ | _ | k
    · decide
    · decide
    · decide
    · simp only [lagrangeP2, ofKinds, Finset.Ioo_eq_empty (show ¬(k + 3 < 3) by omega),
        Finset.filter_empty, Finset.card_empty]
      simp

end PolySeq


namespace PolyKind

variable {K : Type*} [Field K] [CharZero K]

theorem form_eq_sup (κ : PolyKind) {r k : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) :
    κ.form K (n := n) r k =
      (Koszul.polyForm K (Fin n) (κ.dDeg r + 1) (k - 1)).map (Koszul.extDerivₗ K (Fin n)) ⊔
        (Koszul.polyForm K (Fin n) (r - 1) (k + 1)).map (Koszul.koszulₗ K (Fin n)) := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  cases κ
  · exact (sup_eq_polyForm hk).symm
  · exact (sup_eq_polyFormMinus hk).symm

theorem isAffineInvariant_form (κ : PolyKind) {r k : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) :
    IsAffineInvariant (κ.form K (n := n) r k) := by
  rw [κ.form_eq_sup hr hk]
  exact isAffineInvariant_sup hk (κ.le_dDeg r)

end PolyKind

namespace PolySeq

section CommRing

variable (K : Type*) [CommRing K] (S : PolySeq)

/-- The polynomial forms `P_{r_k}Λᵏ(Kⁿ)` or `P_{r_k}⁻Λᵏ(Kⁿ)` of the sequence in degree `k`. -/
abbrev form (k : ℕ) : Submodule K (Koszul.PolyForm K (Fin n)) := (S.kind k).form K (S.deg k) k

/-- The test forms over `K` of the degree-`k` degrees of freedom on `m`-faces. -/
abbrev testForm (k m : ℕ) : Submodule K (Koszul.PolyForm K (Fin m)) :=
  (S.kind k).testForm K (S.deg k) k m

variable {K}

theorem space_eq_map_form (k : ℕ) : S.space n k = (S.form ℝ k).map (evalForm n) :=
  PolyKind.space_eq_map_form _ _ _

theorem test_eq_map_testForm (k m : ℕ) : S.test k m = (S.testForm ℝ k m).map (evalForm m) :=
  PolyKind.test_eq_map_testForm _ _ _ _

theorem extDeriv_mem_form {k : ℕ} {ω : Koszul.PolyForm K (Fin n)} (hω : ω ∈ S.form K k) :
    Koszul.extDeriv ω ∈ S.form K (k + 1) :=
  (S.kind k).extDeriv_mem_form (S.transition k) hω

theorem isAdmissible : PolyKind.IsAdmissible S.kind S.deg := ⟨S.one_le_deg 0, S.transition⟩

end CommRing

variable {K : Type*} [Field K] [CharZero K] (S : PolySeq)

/-- **The polynomial complex of an admissible sequence is exact** in positive degree, over every
field of characteristic `0`. [AFW2010], §5.1.4, (71), (72); [ArnoldLogg2014] -/
theorem exists_extDeriv_eq {k : ℕ} {ω : Koszul.PolyForm K (Fin n)} (hω : ω ∈ S.form K (k + 1))
    (hd : Koszul.extDeriv ω = 0) : ∃ η ∈ S.form K k, Koszul.extDeriv η = ω :=
  (S.kind k).exists_extDeriv_eq (S.transition k) hω hd

theorem mem_polyForm_zero_of_extDeriv_eq_zero {ω : Koszul.PolyForm K (Fin n)}
    (hω : ω ∈ S.form K 0) (hd : Koszul.extDeriv ω = 0) : ω ∈ Koszul.polyForm K (Fin n) 0 0 :=
  (S.kind 0).mem_polyForm_zero_of_extDeriv_eq_zero hω hd

theorem finrank_form_eq_sum (k : ℕ) :
    Module.finrank K (S.form K (n := n) k) =
      ∑ m ∈ range (n + 1), (n + 1).choose (m + 1) * Module.finrank K (S.testForm K k m) :=
  (S.kind k).finrank_form_eq_sum (S.one_le_deg k) k

theorem isAffineInvariant_form {k : ℕ} (hk : 1 ≤ k) : IsAffineInvariant (S.form K (n := n) k) :=
  (S.kind k).isAffineInvariant_form (S.one_le_deg k) hk

end PolySeq

theorem finrank_polySpace_three_zero (r : ℕ) :
    6 * Module.finrank ℝ (polySpace 3 r 0) = (r + 1) * (r + 2) * (r + 3) := by
  rw [← PolyKind.space_full, PolyKind.finrank_space_eq_finrank_form]
  exact Koszul.finrank_polyForm_three_zero (Fintype.card_fin 3) r

theorem finrank_polySpace_three_one (r : ℕ) :
    2 * Module.finrank ℝ (polySpace 3 r 1) = (r + 1) * (r + 2) * (r + 3) := by
  rw [← PolyKind.space_full, PolyKind.finrank_space_eq_finrank_form]
  exact Koszul.finrank_polyForm_three_one (Fintype.card_fin 3) r

theorem finrank_polySpace_three_two (r : ℕ) :
    2 * Module.finrank ℝ (polySpace 3 r 2) = (r + 1) * (r + 2) * (r + 3) := by
  rw [← PolyKind.space_full, PolyKind.finrank_space_eq_finrank_form]
  exact Koszul.finrank_polyForm_three_two (Fintype.card_fin 3) r

theorem finrank_polySpace_three_three (r : ℕ) :
    6 * Module.finrank ℝ (polySpace 3 r 3) = (r + 1) * (r + 2) * (r + 3) := by
  rw [← PolyKind.space_full, PolyKind.finrank_space_eq_finrank_form]
  exact Koszul.finrank_polyForm_three_three (Fintype.card_fin 3) r

theorem finrank_polyMinusSpace_three_one {r : ℕ} (hr : 1 ≤ r) :
    2 * Module.finrank ℝ (polyMinusSpace 3 r 1) = r * (r + 2) * (r + 3) := by
  rw [← PolyKind.space_trimmed, PolyKind.finrank_space_eq_finrank_form]
  exact Koszul.finrank_polyFormMinus_three_one (Fintype.card_fin 3) hr

theorem finrank_polyMinusSpace_three_two {r : ℕ} (hr : 1 ≤ r) :
    2 * Module.finrank ℝ (polyMinusSpace 3 r 2) = r * (r + 1) * (r + 3) := by
  rw [← PolyKind.space_trimmed, PolyKind.finrank_space_eq_finrank_form]
  exact Koszul.finrank_polyFormMinus_three_two (Fintype.card_fin 3) hr

theorem finrank_polySpace_two_zero (r : ℕ) :
    2 * Module.finrank ℝ (polySpace 2 r 0) = (r + 1) * (r + 2) := by
  rw [← PolyKind.space_full, PolyKind.finrank_space_eq_finrank_form]
  exact Koszul.finrank_polyForm_two_zero (Fintype.card_fin 2) r

theorem finrank_polySpace_two_one (r : ℕ) :
    Module.finrank ℝ (polySpace 2 r 1) = (r + 1) * (r + 2) := by
  rw [← PolyKind.space_full, PolyKind.finrank_space_eq_finrank_form]
  exact Koszul.finrank_polyForm_two_one (Fintype.card_fin 2) r

theorem finrank_polySpace_two_two (r : ℕ) :
    2 * Module.finrank ℝ (polySpace 2 r 2) = (r + 1) * (r + 2) := by
  rw [← PolyKind.space_full, PolyKind.finrank_space_eq_finrank_form]
  exact Koszul.finrank_polyForm_two_two (Fintype.card_fin 2) r

theorem finrank_polyMinusSpace_two_one {r : ℕ} (hr : 1 ≤ r) :
    Module.finrank ℝ (polyMinusSpace 2 r 1) = r * (r + 2) := by
  rw [← PolyKind.space_trimmed, PolyKind.finrank_space_eq_finrank_form]
  exact Koszul.finrank_polyFormMinus_two_one (Fintype.card_fin 2) hr

namespace PolySeq

theorem _root_.Feec.FiniteElement.polyMinusSpace_one_eq_p1MinusForms (k : ℕ) :
    polyMinusSpace n 1 k = p1MinusForms n k := by
  rw [polyMinusSpace, ← whitneySpace_refVertex_eq_map_polyFormMinus]
  exact le_antisymm (whitneySpace_le_p1MinusForms _ k) (p1MinusForms_le_whitneySpace_refVertex k)

theorem _root_.Feec.FiniteElement.eq_single_of_mem_testSpaceMinus_one {k : ℕ} {η : FormField k}
    (hη : η ∈ testSpaceMinus 1 k k) : η = fun _ => Pi.single ∅ (η 0 ∅) := by
  rw [testSpaceMinus_eq ⟨le_rfl, by omega⟩, show 1 + k - k - 1 = 0 by omega, Nat.sub_self] at hη
  obtain ⟨Ω, ⟨hdeg, htot⟩, rfl⟩ := hη
  funext x s
  by_cases hs : s = ∅
  · subst hs
    rw [Pi.single_eq_same, evalForm_apply, evalForm_apply,
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 (htot ∅))]
    simp
  · rw [Pi.single_eq_of_ne hs, evalForm_apply, hdeg s (by simpa using hs), map_zero]

theorem _root_.Feec.FiniteElement.degMoment_eq_mul_simplexIntegral {k : ℕ}
    (q : Fin (k + 1) → Fin n → ℝ) {η : FormField k} (hη : η ∈ testSpaceMinus 1 k k)
    (hc : Continuous η) (ω : contForms n) :
    degMoment k q η hc ω = η 0 ∅ * simplexIntegral q ω := by
  have hw : ∀ α : Finset (Fin k) → ℝ, wedgeForm α (Pi.single ∅ (η 0 ∅)) = η 0 ∅ • α := fun α => by
    rw [show (Pi.single ∅ (η 0 ∅) : Finset (Fin k) → ℝ) = η 0 ∅ • Pi.single ∅ 1 by
      rw [← Pi.single_smul, smul_eq_mul, mul_one], wedgeForm_smul_right, wedgeForm_one_right]
  rw [degMoment_apply, vertexMoment_eq_integral, simplexIntegral, ← integral_const_mul]
  congr 1
  funext x
  rw [eq_single_of_mem_testSpaceMinus_one hη]
  simp only [wedgeField, hw, Pi.smul_apply, smul_eq_mul, affinePullback_apply,
    pullback_degField_univ, Pi.single_eq_same]

theorem card_eq_of_trimmed_one_dofIdx {g : Finset (Fin n → ℝ)} {k : ℕ}
    (i : (trimmed 1 le_rfl).DofIdx g k) : #g = k + 1 := by
  have h1 := card_pos.2 i.2
  by_contra h
  have h0 : Module.finrank ℝ ((trimmed 1 le_rfl).test k (#g - 1)) = 0 := by
    change Module.finrank ℝ (testSpaceMinus 1 k (#g - 1)) = 0
    rw [testSpaceMinus_eq_bot (show ¬(k ≤ #g - 1 ∧ #g - 1 < 1 + k) by omega), finrank_bot]
  have := i.1.isLt
  omega

theorem degMoment_eq_smul_whitneyFaceDof {g : Finset (Fin n → ℝ)} {k m : ℕ} (hm : m = k)
    (hg : #g = k + 1) {η : FormField m} (hη : η ∈ testSpaceMinus 1 k m) (hη0 : η ≠ 0)
    (hc : Continuous η) :
    ∃ c : ℝ, c ≠ 0 ∧ degMoment k (lexEnum g m) η hc = c • whitneyFaceDof g k := by
  subst hm
  have hc0 : η 0 ∅ ≠ 0 := fun h => hη0 (by
    rw [eq_single_of_mem_testSpaceMinus_one hη, h]; funext x s; simp)
  obtain ⟨ε, hε, hεeq⟩ := exists_sign_simplexIntegral_eq (lexEnum_injective hg)
    (injective_faceEnum hg) (by rw [range_lexEnum hg, range_faceEnum hg])
  refine ⟨η 0 ∅ * ε, mul_ne_zero hc0 (by rcases hε with rfl | rfl <;> norm_num),
    LinearMap.ext fun ω => ?_⟩
  rw [degMoment_eq_mul_simplexIntegral _ hη, LinearMap.smul_apply, whitneyFaceDof_apply, hεeq,
    smul_eq_mul, mul_assoc]

theorem trimmed_one_dof_eq {g : Finset (Fin n → ℝ)} {k : ℕ}
    (i : (trimmed 1 le_rfl).DofIdx g k) :
    ∃ c : ℝ, c ≠ 0 ∧ (trimmed 1 le_rfl).dof g k i = c • whitneyFaceDof g k := by
  have hg := card_eq_of_trimmed_one_dofIdx i
  exact degMoment_eq_smul_whitneyFaceDof (by omega) hg ((trimmed 1 le_rfl).testBasis k _ i.1).2
    (fun h => ((trimmed 1 le_rfl).testBasis k _).ne_zero i.1 (Subtype.ext h)) _

end PolySeq

theorem whitneyElement_equivalent_trimmed :
    (whitneyElement n).Equivalent (polyElement n (PolySeq.trimmed 1 le_rfl)) where
  space_eq T k :=
    (whitneySpace_eq_p1MinusForms T k).trans (polyMinusSpace_one_eq_p1MinusForms k).symm
  span_dof_eq g k := by
    by_cases hg : #g = k + 1
    · have : Nonempty ((whitneyElement n).DofIdx g k) := ⟨⟨(), hg⟩⟩
      have hW : Set.range ((whitneyElement n).dof g k) = {whitneyFaceDof g k} := Set.range_const
      have hpos : 0 < Module.finrank ℝ ((PolySeq.trimmed 1 le_rfl).test k (#g - 1)) := by
        change 0 < Module.finrank ℝ (testSpaceMinus 1 k (#g - 1))
        rw [finrank_testSpaceMinus le_rfl]
        simp only [show k ≤ #g - 1 ∧ #g - 1 < 1 + k by omega, and_self, ↓reduceIte,
          show #g - 1 - k = 0 by omega]
        simp
      set i₀ : (PolySeq.trimmed 1 le_rfl).DofIdx g k := ⟨⟨0, hpos⟩, card_pos.1 (by omega)⟩
      obtain ⟨c, hc, h₀⟩ := PolySeq.trimmed_one_dof_eq i₀
      rw [hW]
      refine le_antisymm ?_ (Submodule.span_le.2 ?_)
      · rw [Submodule.span_singleton_le_iff_mem, show whitneyFaceDof g k =
          c⁻¹ • (PolySeq.trimmed 1 le_rfl).dof g k i₀ by rw [h₀, smul_smul, inv_mul_cancel₀ hc,
            one_smul]]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i₀, rfl⟩)
      · rintro _ ⟨i, rfl⟩
        obtain ⟨c, -, h⟩ := PolySeq.trimmed_one_dof_eq i
        change (PolySeq.trimmed 1 le_rfl).dof g k i ∈ _
        rw [h]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · have : IsEmpty ((whitneyElement n).DofIdx g k) := ⟨fun i => hg i.2⟩
      have : IsEmpty ((polyElement n (PolySeq.trimmed 1 le_rfl)).DofIdx g k) :=
        ⟨fun i => hg (PolySeq.card_eq_of_trimmed_one_dofIdx i)⟩
      rw [Set.range_eq_empty, Set.range_eq_empty]

namespace PolySeq

variable (S : PolySeq)

theorem card_sigma_dofIdx_eq_sum (F : Finset (Finset (Fin n → ℝ)))
    (hF : ∀ g ∈ F, #g ≤ n + 1) (k : ℕ) :
    Fintype.card (Σ g : F, S.DofIdx (g : Finset (Fin n → ℝ)) k) =
      ∑ m ∈ range (n + 1), #(F.filter fun g => #g = m + 1) *
        Module.finrank ℝ (S.test k m) := by
  classical
  rw [Fintype.card_sigma]
  simp only [card_dofIdx]
  rw [Finset.sum_coe_sort F (fun g => if g.Nonempty then
    Module.finrank ℝ (S.test k (#g - 1)) else 0), ← sum_filter]
  rw [← sum_fiberwise_of_maps_to (s := F.filter fun g => g.Nonempty) (t := range (n + 1))
    (g := fun g => #g - 1) (fun g hg => by
      have h1 := hF g (mem_filter.1 hg).1
      have h2 := card_pos.2 (mem_filter.1 hg).2
      simp only [Finset.mem_range]; omega)]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_congr rfl fun g hg => by rw [(mem_filter.1 hg).2], sum_const, smul_eq_mul,
    filter_filter]
  congr 2
  refine filter_congr fun g _ => ?_
  rw [← card_pos]
  omega

end PolySeq

theorem card_le_of_mem_meshFaces (M : SimplicialMesh n) {g : Finset (Fin n → ℝ)}
    (hg : g ∈ LocalElement.meshFaces M) : #g ≤ n + 1 := by
  obtain ⟨T, -, hgT⟩ := (LocalElement.mem_meshFaces M).1 hg
  exact (Finset.card_le_card hgT).trans (card_vertexSet T).le

namespace PolySeq

variable (S : PolySeq) (M : SimplicialMesh n)

theorem card_globalDofIdx (k : ℕ) :
    Fintype.card ((polyElement n S).GlobalDofIdx M k) =
      ∑ m ∈ range (n + 1), (M.faces m).ncard * Module.finrank ℝ (S.test k m) := by
  classical
  refine (S.card_sigma_dofIdx_eq_sum _ (fun g hg => card_le_of_mem_meshFaces M hg) k).trans ?_
  refine sum_congr rfl fun m _ => ?_
  rw [← coe_filter_meshFaces M m, Set.ncard_coe_finset]

/-- **`dim Λ_hᵏ(M) = Σ_{m ≤ n} #{m-faces of M} · dim(test forms on m-faces)`** for the global
`P_{r_k}Λᵏ` (resp. `P_{r_k}⁻Λᵏ`) space. [AFW2006], Thms 4.9, 4.13, §5.1 -/
theorem finrank_globalSpace (k : ℕ) :
    Module.finrank ℝ ((polyElement n S).globalSpace M k) =
      ∑ m ∈ range (n + 1), (M.faces m).ncard * Module.finrank ℝ (S.test k m) := by
  rw [LocalElement.finrank_globalSpace, card_globalDofIdx]

/-- The faces of `M` not contained in a boundary facet. -/
def interiorFaces (M : SimplicialMesh n) : Finset (Finset (Fin n → ℝ)) := by
  classical
  exact (LocalElement.meshFaces M).filter fun g => ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F

theorem mem_interiorFaces {g : Finset (Fin n → ℝ)} :
    g ∈ interiorFaces M ↔
      g ∈ LocalElement.meshFaces M ∧ ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F := by
  classical
  unfold interiorFaces; exact mem_filter

theorem card_interiorDofIdx (k : ℕ) :
    Fintype.card ((polyElement n S).InteriorDofIdx M k) =
      ∑ m ∈ range (n + 1), {g | g ∈ M.faces m ∧ ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F}.ncard *
        Module.finrank ℝ (S.test k m) := by
  classical
  have e : (polyElement n S).InteriorDofIdx M k ≃
      Σ g : interiorFaces M, S.DofIdx (g : Finset (Fin n → ℝ)) k :=
    { toFun := fun p => ⟨⟨p.1.1.1, (mem_interiorFaces M).2 ⟨p.1.1.2, p.2⟩⟩, p.1.2⟩
      invFun := fun q => ⟨⟨⟨q.1.1, ((mem_interiorFaces M).1 q.1.2).1⟩, q.2⟩,
        ((mem_interiorFaces M).1 q.1.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, S.card_sigma_dofIdx_eq_sum _ (fun g hg => card_le_of_mem_meshFaces M
    ((mem_interiorFaces M).1 hg).1) k]
  refine sum_congr rfl fun m _ => ?_
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext g
  simp only [coe_filter, mem_interiorFaces, LocalElement.mem_meshFaces,
    SimplicialMesh.faces, Set.mem_ofPred_eq]
  tauto

theorem finrank_globalSpace₀ (k : ℕ) :
    Module.finrank ℝ ((polyElement n S).globalSpace₀ M k) =
      ∑ m ∈ range (n + 1), {g | g ∈ M.faces m ∧ ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F}.ncard *
        Module.finrank ℝ (S.test k m) := by
  rw [LocalElement.finrank_globalSpace₀, card_interiorDofIdx]

theorem finrank_V₀ (hΩ : IsOpen M.domain) (k : ℕ) :
    Module.finrank ℝ ((polyElement n S).V₀ M k) =
      ∑ m ∈ range (n + 1), {g | g ∈ M.faces m ∧ ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F}.ncard *
        Module.finrank ℝ (S.test k m) := by
  rw [LocalElement.finrank_V₀ _ M hΩ, card_interiorDofIdx]

theorem finrank_test (k m : ℕ) :
    Module.finrank ℝ (S.test k m) = (S.kind k).testDim (S.deg k) k m :=
  PolyKind.finrank_test _ (S.one_le_deg k) k m

theorem mem_globalSpace_iff (hM : LocalElement.FacetConnected M) {k : ℕ}
    {u : (polyElement n S).Piecewise M k} :
    u ∈ (polyElement n S).globalSpace M k ↔ ∀ F ∈ M.facets, ∀ T T' : M.simplices,
      F ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) →
        F ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) →
          ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)),
            TangentialTraceEq F k ((u T : FormField n) x) ((u T' : FormField n) x) :=
  (polyElement n S).mem_globalSpace_iff M hM (inferInstanceAs (IsEmpty (S.DofIdx ∅ k)))

/-- The finite element subcomplex `Vₕ ⊆ HΛ(Ω)` of `S` on a mesh of an open `Ω ⊆ ℝⁿ`. -/
def subcomplex [NeZero n] (hΩ : IsOpen M.domain) :
    ((deRham ℝ n).maximalComplex hΩ).Subcomplex :=
  (polyElement n S).subcomplex M hΩ

/-- The subcomplex `V̊ₕ ⊆ H̊Λ(Ω)` with vanishing boundary DOFs, for `Ω` strictly star-shaped. -/
def subcomplexMin [NeZero n] (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain) :
    ((deRham ℝ n).minimalComplex hΩ).Subcomplex :=
  (polyElement n S).subcomplexMin M hΩ x₀ hstar

instance [NeZero n] (hΩ : IsOpen M.domain) (k : ℤ) :
    FiniteDimensional ℝ ((S.subcomplex M hΩ).V k) :=
  inferInstanceAs (FiniteDimensional ℝ ((polyElement n S).V M k))

instance [NeZero n] (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain)
    (k : ℤ) : FiniteDimensional ℝ ((S.subcomplexMin M hΩ x₀ hstar).V k) :=
  inferInstanceAs (FiniteDimensional ℝ ((polyElement n S).V₀ M k))

/-- `subcomplexMin` on the level-`N` Freudenthal mesh of a cube. -/
def freudenthalSubcomplexMin [NeZero n] (b : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (N : ℕ)
    [NeZero N] :
    ((deRham ℝ n).minimalComplex (isOpen_freudenthalMesh_domain b s hs N)).Subcomplex :=
  S.subcomplexMin (freudenthalMesh b s hs N) (isOpen_freudenthalMesh_domain b s hs N) _
    (add_smul_sub_mem_of_convex (isOpen_freudenthalMesh_domain b s hs N)
      (convex_freudenthalMesh_domain b s hs N) (center_mem_freudenthalMesh_domain b s hs N))

end PolySeq

/-- **The Whitney complex is the trimmed complex of degree one**, `P₁⁻Λ⁰ → ⋯ → P₁⁻Λⁿ`, on every
conforming mesh: `whitneySubcomplex = (PolySeq.trimmed 1).subcomplex`. [AFW2006], §3–4 -/
theorem whitneySubcomplex_eq_trimmed [NeZero n] (M : SimplicialMesh n) (hΩ : IsOpen M.domain) :
    whitneySubcomplex M hΩ = (PolySeq.trimmed 1 le_rfl).subcomplex M hΩ :=
  whitneyElement_equivalent_trimmed.subcomplex_eq M hΩ

theorem whitneySubcomplexMin_eq_trimmed [NeZero n] (M : SimplicialMesh n) (hΩ : IsOpen M.domain)
    (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain) :
    whitneySubcomplexMin M hΩ x₀ hstar = (PolySeq.trimmed 1 le_rfl).subcomplexMin M hΩ x₀ hstar :=
  whitneyElement_equivalent_trimmed.subcomplexMin_eq M hΩ x₀ hstar

namespace LocalElement

variable (E : LocalElement n) (M : SimplicialMesh n)

theorem not_isBoundaryDof_of_mem_convexHull (hΩ : IsOpen M.domain) {k : ℕ}
    (p : E.GlobalDofIdx M k) {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ ((p.1 : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)))
    (hxΩ : x ∈ M.domain) : ¬ E.IsBoundaryDof M p := by
  rintro ⟨F, hF, hpF⟩
  have h := hF.2.2 (convexHull_mono (Finset.coe_subset.2 hpF) hx)
  exact h.2 (interior_mono subset_closure (hΩ.interior_eq.symm ▸ hxΩ))

theorem finrank_V₀_pos (hΩ : IsOpen M.domain) {k : ℕ} {g : Finset (Fin n → ℝ)}
    (hg : g ∈ meshFaces M) (i : E.DofIdx g k) {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ (g : Set (Fin n → ℝ))) (hxΩ : x ∈ M.domain) :
    0 < Module.finrank ℝ (E.V₀ M k) := by
  rw [E.finrank_V₀ M hΩ k]
  exact Fintype.card_pos_iff.2
    ⟨⟨⟨⟨g, hg⟩, i⟩, E.not_isBoundaryDof_of_mem_convexHull M hΩ ⟨⟨g, hg⟩, i⟩ hx hxΩ⟩⟩

end LocalElement

theorem exists_finset_zero_last_mem {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) :
    ∃ f : Finset (Fin (n + 1)), 0 ∈ f ∧ Fin.last n ∈ f ∧ #f = d + 1 := by
  classical
  have hne : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  set u := Finset.univ \ {0, Fin.last n}
  have hu : #u = n - 1 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, card_pair hne]
    omega
  obtain ⟨t, htu, htc⟩ := exists_subset_card_eq (show d - 1 ≤ #u by omega)
  have h0t : (0 : Fin (n + 1)) ∉ t := fun h => by
    have := htu h; simp [u] at this
  have hlt : Fin.last n ∉ t := fun h => by
    have := htu h; simp [u] at this
  refine ⟨insert 0 (insert (Fin.last n) t), mem_insert_self _ _,
    mem_insert_of_mem (mem_insert_self _ _), ?_⟩
  rw [card_insert_of_notMem (by simp [hne, h0t]), card_insert_of_notMem hlt, htc]
  omega

theorem exists_meshFace_freudenthalMesh {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s) {N : ℕ} [NeZero N]
    {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) :
    ∃ g ∈ LocalElement.meshFaces (freudenthalMesh b s hs N), #g = d + 1 ∧
      ∃ x ∈ convexHull ℝ (g : Set (Fin n → ℝ)), x ∈ (freudenthalMesh b s hs N).domain := by
  classical
  obtain ⟨f, hf0, hfl, hfc⟩ := exists_finset_zero_last_mem hd1 hdn
  set T₀ := mapEquiv (boxMap b (s / N) (freudenthalScale_ne_zero hs N))
    (freudenthalSimplex (finLattice (0 : Fin n → Fin N)) 1)
  have hT₀ : T₀ ∈ (freudenthalMesh b s hs N).simplices :=
    mem_freudenthalMesh_simplices.2 ⟨0, 1, rfl⟩
  have hpts : ∀ j, T₀.points j = b + (s / N) • kuhnVertex 1 j := fun j => by
    have : latticePoint (finLattice (0 : Fin n → Fin N)) = 0 := by
      funext i; simp [finLattice]
    simp [T₀, this]
  have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hh : 0 < s / N := div_pos hs (by linarith)
  have hhs : s / N ≤ s := div_le_self hs.le hN
  set g := f.image T₀.points
  refine ⟨g, (LocalElement.mem_meshFaces _).2 ⟨T₀, hT₀, fun x hx => ?_⟩, ?_, ?_⟩
  · obtain ⟨j, -, rfl⟩ := mem_image.1 hx
    exact points_mem_vertexSet T₀ j
  · rw [card_image_of_injective _ T₀.independent.injective, hfc]
  · refine ⟨(1 / 2 : ℝ) • T₀.points 0 + (1 / 2 : ℝ) • T₀.points (Fin.last n),
      convex_convexHull ℝ _ (subset_convexHull ℝ _ (mem_coe.2 (mem_image_of_mem _ hf0)))
        (subset_convexHull ℝ _ (mem_coe.2 (mem_image_of_mem _ hfl))) (by norm_num) (by norm_num)
        (by norm_num), ?_⟩
    rw [freudenthalMesh_domain]
    intro i _
    simp only [hpts, kuhnVertex_zero, kuhnVertex_last, smul_zero, add_zero, Pi.add_apply,
      Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, Set.mem_Ioo]
    constructor <;> nlinarith

namespace PolySeq

variable (S : PolySeq)

theorem finrank_V₀_freudenthalMesh_pos [NeZero n] {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s) {N : ℕ}
    [NeZero N] {k d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n)
    (hdim : 0 < Module.finrank ℝ (S.test k d)) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) k) := by
  obtain ⟨g, hg, hgc, x, hx, hxΩ⟩ := exists_meshFace_freudenthalMesh (b := b) hs (N := N) hd1 hdn
  have hgd : #g - 1 = d := by omega
  have hne : g.Nonempty := card_pos.1 (by omega)
  have hdim' : 0 < Module.finrank ℝ (S.test k (#g - 1)) := by rw [hgd]; exact hdim
  exact (polyElement n S).finrank_V₀_pos _ (isOpen_freudenthalMesh_domain b s hs N) hg
    (⟨⟨0, hdim'⟩, hne⟩ : S.DofIdx g k) hx hxΩ

theorem _root_.Feec.FiniteElement.PolyKind.testDim_self_pos (κ : PolyKind) {r : ℕ} (hr : 1 ≤ r)
    (k : ℕ) : 0 < κ.testDim r k k := by
  cases κ <;>
  · simp only [PolyKind.testDim, le_refl, true_and, show k < r + k by omega, ↓reduceIte,
      Nat.sub_self, Nat.choose_zero_right, mul_one]
    exact Nat.choose_pos (by omega)

theorem finrank_V₀_freudenthalMesh_pos_of_one_le [NeZero n] {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s)
    {N : ℕ} [NeZero N] {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) k) :=
  S.finrank_V₀_freudenthalMesh_pos hs hk1 hkn
    (by rw [finrank_test]; exact PolyKind.testDim_self_pos _ (S.one_le_deg k) k)

theorem finrank_V₀_freudenthalMesh_pos_zero [NeZero n] {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s)
    {N : ℕ} [NeZero N] (h2 : 2 ≤ S.deg 0) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) 0) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  refine S.finrank_V₀_freudenthalMesh_pos hs le_rfl hn ?_
  rw [finrank_test]
  cases h : S.kind 0 <;>
  · simp only [PolyKind.testDim, zero_le, true_and, show 1 < S.deg 0 + 0 by omega, ↓reduceIte,
      Nat.sub_zero]
    refine Nat.mul_pos (Nat.choose_pos (by omega)) ?_
    rw [Nat.choose_one_right]
    omega

theorem lagrangeP2_V₀_ne_bot (N k : ℕ) (hk : k ≤ 3) :
    (polyElement 3 lagrangeP2).V₀ (freudenthalMesh 0 (1 / 2) (by norm_num) (N + 1)) k ≠ ⊥ := by
  intro h
  have hpos : 0 < Module.finrank ℝ
      ((polyElement 3 lagrangeP2).V₀ (freudenthalMesh 0 (1 / 2) (by norm_num) (N + 1)) k) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact lagrangeP2.finrank_V₀_freudenthalMesh_pos_zero _ (by simp)
    · exact lagrangeP2.finrank_V₀_freudenthalMesh_pos_of_one_le _ hk1 hk
  rw [h, finrank_bot] at hpos
  exact lt_irrefl 0 hpos

end PolySeq

theorem finrank_whitney_V₀_freudenthalMesh_pos [NeZero n] {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s)
    {N : ℕ} [NeZero N] {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    0 < Module.finrank ℝ ((whitneyElement n).V₀ (freudenthalMesh b s hs N) k) := by
  obtain ⟨g, hg, hgc, x, hx, hxΩ⟩ := exists_meshFace_freudenthalMesh (b := b) hs (N := N) hk1 hkn
  exact (whitneyElement n).finrank_V₀_pos _ (isOpen_freudenthalMesh_domain b s hs N) hg
    (⟨(), hgc⟩ : WhitneyDofIdx g k) hx hxΩ

theorem exists_vertex_freudenthalMesh {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s) {N : ℕ} [NeZero N]
    (hN : 2 ≤ N) :
    ∃ g ∈ LocalElement.meshFaces (freudenthalMesh b s hs N), #g = 0 + 1 ∧
      ∃ x ∈ convexHull ℝ (g : Set (Fin n → ℝ)), x ∈ (freudenthalMesh b s hs N).domain := by
  classical
  set m : Fin n → Fin N := fun _ => ⟨1, by omega⟩
  set T₁ := mapEquiv (boxMap b (s / N) (freudenthalScale_ne_zero hs N))
    (freudenthalSimplex (finLattice m) 1)
  have hT₁ : T₁ ∈ (freudenthalMesh b s hs N).simplices :=
    mem_freudenthalMesh_simplices.2 ⟨m, 1, rfl⟩
  have hpt : T₁.points 0 = b + (s / N) • (1 : Fin n → ℝ) := by
    have : latticePoint (finLattice m) = 1 := by
      funext i; simp [finLattice, m]
    simp [T₁, this]
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : 0 < s / N := div_pos hs (by linarith)
  have hhs : s / N < s := div_lt_self hs (by linarith)
  refine ⟨{T₁.points 0}, (LocalElement.mem_meshFaces _).2 ⟨T₁, hT₁, fun x hx => ?_⟩,
    card_singleton _, T₁.points 0, subset_convexHull ℝ _ (by simp), ?_⟩
  · rw [mem_singleton.1 hx]
    exact points_mem_vertexSet T₁ 0
  · rw [freudenthalMesh_domain, hpt]
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, Set.mem_Ioo]
    constructor <;> linarith

namespace PolySeq

theorem finrank_V₀_freudenthalMesh_pos_zero_of_two_le (S : PolySeq) [NeZero n] {b : Fin n → ℝ}
    {s : ℝ} (hs : 0 < s) {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) 0) := by
  obtain ⟨g, hg, hgc, x, hx, hxΩ⟩ := exists_vertex_freudenthalMesh (b := b) hs hN
  have hdim : 0 < Module.finrank ℝ (S.test 0 (#g - 1)) := by
    rw [hgc, finrank_test]; exact PolyKind.testDim_self_pos _ (S.one_le_deg 0) 0
  exact (polyElement n S).finrank_V₀_pos _ (isOpen_freudenthalMesh_domain b s hs N) hg
    (⟨⟨0, hdim⟩, card_pos.1 (by omega)⟩ : S.DofIdx g 0) hx hxΩ

/-- **`V̊ₕᵏ ≠ 0` in every degree `k ≤ n`** on the Freudenthal meshes of level `N ≥ 2`, for every
admissible sequence. -/
theorem finrank_V₀_freudenthalMesh_pos_of_two_le (S : PolySeq) [NeZero n] {b : Fin n → ℝ}
    {s : ℝ} (hs : 0 < s) {N : ℕ} [NeZero N] (hN : 2 ≤ N) {k : ℕ} (hkn : k ≤ n) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact S.finrank_V₀_freudenthalMesh_pos_zero_of_two_le hs hN
  · exact S.finrank_V₀_freudenthalMesh_pos_of_one_le hs hk1 hkn

end PolySeq

end Feec.FiniteElement
