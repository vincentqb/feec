module

public import Feec.Algebra.PolynomialFormDim
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Nat.Choose.Sum

/-!
# The two families `P_rΛᵏ`, `P_r⁻Λᵏ` of the periodic table, over a field

The kinds `PolyKind` of polynomial forms, the admissible transitions between consecutive form
degrees ([AFW2006], §5; [AFW2010], §5.2), and the shape spaces and test forms as polynomial forms
over a commutative ring.

## Main results

* `PolyKind.exists_extDeriv_eq`: exactness along an admissible transition.
* `PolyKind.finrank_form_eq_sum`: the dimension of the shape spaces is the number of DOFs, `r ≥ 1`.
* `PolyKind.IsAdmissible.exists_extDeriv_eq`: exactness of admissible sequences in positive degree.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset

@[expose] public noncomputable section

namespace Feec.FiniteElement

variable {n : ℕ}

theorem sum_choose_mul_choose_eq {n r k : ℕ} (hk : k ≤ n) (hr : 1 ≤ r) :
    ∑ m ∈ range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then (r - 1).choose (m - k) else 0) = (n + r).choose (n - k) := by
  have h1 : ∀ m ∈ range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then (r - 1).choose (m - k) else 0) =
      if k ≤ m then (n + 1).choose (m + 1) * (r - 1).choose (m - k) else 0 := by
    intro m _
    by_cases hkm : k ≤ m
    · by_cases hmr : m < r + k
      · simp [hkm, hmr]
      · simp [hkm, hmr, Nat.choose_eq_zero_of_lt (show r - 1 < m - k by omega)]
    · simp [hkm]
  rw [sum_congr rfl h1, ← sum_filter, show (range (n + 1)).filter (fun m => k ≤ m) = Ico k (n + 1)
    by ext m; simp; omega, sum_Ico_eq_sum_range,
    show n + r = (r - 1) + (n + 1) by omega, Nat.add_choose_eq,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, show n + 1 - k = (n - k).succ by omega]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n - k := by simp at hi; omega
  rw [mul_comm, show k + i - k = i by omega]
  congr 1
  exact Nat.choose_symm_of_eq_add (by omega)

/-- The two families of polynomial forms: the full spaces `P_rΛᵏ` and the trimmed `P_r⁻Λᵏ`. -/
inductive PolyKind
  /-- `P_rΛᵏ` -/
  | full
  /-- `P_r⁻Λᵏ` -/
  | trimmed
  deriving DecidableEq

namespace PolyKind

/-- The dimension of the test space of the family on `m`-faces. -/
def testDim (κ : PolyKind) (r k m : ℕ) : ℕ :=
  (match κ with
    | full => (r + k).choose r
    | trimmed => (r + k - 1).choose (r - 1)) *
  if k ≤ m ∧ m < r + k then (r - 1).choose (m - k) else 0

/-- The admissible transitions from `P_rΛᵏ` or `P_r⁻Λᵏ` to `P_r⁻Λᵏ⁺¹` or `P_{r-1}Λᵏ⁺¹`. -/
def Transition (r : ℕ) (κ' : PolyKind) (r' : ℕ) : Prop :=
  (κ' = trimmed ∧ r' = r) ∨ (κ' = full ∧ r' + 1 = r)

section CommRing

variable (K : Type*) [CommRing K]

/-- The polynomial forms `P_rΛᵏ(Kⁿ)` or `P_r⁻Λᵏ(Kⁿ)` of the family over `K`. -/
def form : PolyKind → ℕ → ℕ → Submodule K (Koszul.PolyForm K (Fin n))
  | full, r, k => Koszul.polyForm K (Fin n) r k
  | trimmed, r, k => Koszul.polyFormMinus K (Fin n) r k

/-- The test forms over `K` of the degrees of freedom of the family on `m`-faces. -/
def testForm : PolyKind → ℕ → ℕ → (m : ℕ) → Submodule K (Koszul.PolyForm K (Fin m))
  | full, r, k, m =>
    if k ≤ m ∧ m < r + k then Koszul.polyFormMinus K (Fin m) (r + k - m) (m - k) else ⊥
  | trimmed, r, k, m =>
    if k ≤ m ∧ m < r + k then Koszul.polyForm K (Fin m) (r + k - m - 1) (m - k) else ⊥

variable {K}

@[simp] theorem form_full (r k : ℕ) : full.form K (n := n) r k = Koszul.polyForm K (Fin n) r k :=
  rfl

@[simp] theorem form_trimmed (r k : ℕ) :
    trimmed.form K (n := n) r k = Koszul.polyFormMinus K (Fin n) r k :=
  rfl

theorem testForm_full {r k m : ℕ} (h : k ≤ m ∧ m < r + k) :
    full.testForm K r k m = Koszul.polyFormMinus K (Fin m) (r + k - m) (m - k) := by
  simp only [testForm, h, and_self, ↓reduceIte]

theorem testForm_trimmed {r k m : ℕ} (h : k ≤ m ∧ m < r + k) :
    trimmed.testForm K r k m = Koszul.polyForm K (Fin m) (r + k - m - 1) (m - k) := by
  simp only [testForm, h, and_self, ↓reduceIte]

theorem testForm_eq_bot (κ : PolyKind) {r k m : ℕ} (h : ¬(k ≤ m ∧ m < r + k)) :
    κ.testForm K r k m = ⊥ := by
  cases κ <;> simp only [testForm, h, ↓reduceIte]

theorem form_le_polyForm (κ : PolyKind) (r k : ℕ) :
    κ.form K r k ≤ Koszul.polyForm K (Fin n) r k := by
  cases κ
  · exact le_rfl
  · exact Koszul.polyFormMinus_le_polyForm r k

theorem polyFormMinus_le_form (κ : PolyKind) (r k : ℕ) :
    Koszul.polyFormMinus K (Fin n) r k ≤ κ.form K r k := by
  cases κ
  · exact Koszul.polyFormMinus_le_polyForm r k
  · exact le_rfl

theorem form_le_polyFormMinus {r : ℕ} {κ' : PolyKind} {r' : ℕ} (ht : Transition r κ' r')
    (k : ℕ) : κ'.form K r' k ≤ Koszul.polyFormMinus K (Fin n) r k := by
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact le_rfl
  · simpa using Koszul.polyForm_le_polyFormMinus (R := K) (d := Fin n) (r := r' + 1) (by omega) k

theorem extDeriv_mem_form (κ : PolyKind) {r : ℕ} {κ' : PolyKind} {r' : ℕ}
    (ht : Transition r κ' r') {k : ℕ} {ω : Koszul.PolyForm K (Fin n)} (hω : ω ∈ κ.form K r k) :
    Koszul.extDeriv ω ∈ κ'.form K r' (k + 1) := by
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases κ
    · exact Koszul.extDeriv_mem_polyFormMinus_of_mem_polyForm hω
    · exact Koszul.extDeriv_mem_polyFormMinus hω
  · have h : Koszul.extDeriv ω ∈ Koszul.polyForm K (Fin n) (r' + 1 - 1) (k + 1) := by
      cases κ
      · exact Koszul.extDeriv_mem_polyForm hω
      · exact Koszul.extDeriv_mem_polyForm_of_mem_polyFormMinus hω
    simpa using h

end CommRing

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- **Exactness along an admissible transition** (`K` of characteristic `0`): a closed form of the
target space is `d η` with `η` in the source space. [AFW2010], §5.1.4, (72) -/
theorem exists_extDeriv_eq (κ : PolyKind) {r : ℕ} {κ' : PolyKind} {r' : ℕ}
    (ht : Transition r κ' r') {k : ℕ} {ω : Koszul.PolyForm K (Fin n)}
    (hω : ω ∈ κ'.form K r' (k + 1)) (hd : Koszul.extDeriv ω = 0) :
    ∃ η ∈ κ.form K r k, Koszul.extDeriv η = ω := by
  obtain ⟨η, hη, he⟩ :=
    Koszul.exists_extDeriv_eq_of_mem_polyFormMinus (form_le_polyFormMinus ht _ hω) hd
  exact ⟨η, κ.polyFormMinus_le_form r k hη, he⟩

theorem mem_polyForm_zero_of_extDeriv_eq_zero (κ : PolyKind) {r : ℕ}
    {ω : Koszul.PolyForm K (Fin n)} (hω : ω ∈ κ.form K r 0) (hd : Koszul.extDeriv ω = 0) :
    ω ∈ Koszul.polyForm K (Fin n) 0 0 :=
  Koszul.mem_polyForm_zero_of_extDeriv_eq_zero (κ.form_le_polyForm r 0 hω).1 hd

theorem finrank_testForm (κ : PolyKind) {r : ℕ} (hr : 1 ≤ r) (k m : ℕ) :
    Module.finrank K (κ.testForm K r k m) = κ.testDim r k m := by
  by_cases h : k ≤ m ∧ m < r + k
  · cases κ
    · rw [testForm_full h, Koszul.finrank_polyFormMinus (by omega), Fintype.card_fin,
        show r + k - m + m = r + k by omega, show r + k - m + (m - k) = r by omega]
      simp only [testDim, h.1, h.2, and_self, ↓reduceIte]
    · rw [testForm_trimmed h, Koszul.finrank_polyForm, Fintype.card_fin,
        show r + k - m - 1 + m = r + k - 1 by omega, show r + k - m - 1 + (m - k) = r - 1 by omega]
      simp only [testDim, h.1, h.2, and_self, ↓reduceIte]
  · rw [κ.testForm_eq_bot h, finrank_bot]
    cases κ <;> simp [testDim, h]

/-- **`dim P_rΛᵏ(Kⁿ)` (resp. `P_r⁻Λᵏ(Kⁿ)`) is the number of degrees of freedom** of a simplex,
for `r ≥ 1`, over every field of characteristic `0`. [AFW2006], Thms 4.9, 4.13 -/
theorem finrank_form_eq_sum (κ : PolyKind) {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    Module.finrank K (κ.form K (n := n) r k) =
      ∑ m ∈ range (n + 1), (n + 1).choose (m + 1) * Module.finrank K (κ.testForm K r k m) := by
  simp only [κ.finrank_testForm hr]
  by_cases hk : k ≤ n
  · cases κ
    · rw [form_full, Koszul.finrank_polyForm, Fintype.card_fin]
      simp only [testDim, mul_left_comm _ ((r + k).choose r)]
      rw [← mul_sum, sum_choose_mul_choose_eq hk hr, ← @Nat.choose_symm_add r k,
        Nat.choose_symm_of_eq_add (show n + r = (n - k) + (r + k) by omega), add_comm n r,
        mul_comm]
    · rw [form_trimmed, Koszul.finrank_polyFormMinus hr, Fintype.card_fin]
      simp only [testDim, mul_left_comm _ ((r + k - 1).choose (r - 1))]
      rw [← mul_sum, sum_choose_mul_choose_eq hk hr,
        Nat.choose_symm_of_eq_add (show r + k - 1 = (r - 1) + k by omega),
        Nat.choose_symm_of_eq_add (show n + r = (n - k) + (r + k) by omega), add_comm n r,
        mul_comm]
  · have h0 : (r + n).choose (r + k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    refine Eq.trans ?_ (sum_eq_zero fun m hm => ?_).symm
    · cases κ
      · rw [form_full, Koszul.finrank_polyForm, Fintype.card_fin, h0, zero_mul]
      · rw [form_trimmed, Koszul.finrank_polyFormMinus hr, Fintype.card_fin, h0, zero_mul]
    · simp only [Finset.mem_range] at hm
      simp [testDim, show ¬k ≤ m by omega]

end Field

/-- An admissible sequence of spaces of polynomial forms. [AFW2006], §3.5, (5.13) -/
structure IsAdmissible (κ : ℕ → PolyKind) (r : ℕ → ℕ) : Prop where
  one_le : 1 ≤ r 0
  transition (k : ℕ) : Transition (r k) (κ (k + 1)) (r (k + 1))

namespace IsAdmissible

variable {κ : ℕ → PolyKind} {r : ℕ → ℕ} (h : IsAdmissible κ r)
include h

theorem extDeriv_mem {K : Type*} [CommRing K] {k : ℕ} {ω : Koszul.PolyForm K (Fin n)}
    (hω : ω ∈ (κ k).form K (r k) k) : Koszul.extDeriv ω ∈ (κ (k + 1)).form K (r (k + 1)) (k + 1) :=
  (κ k).extDeriv_mem_form (h.transition k) hω

variable {K : Type*} [Field K] [CharZero K]

/-- **The polynomial complex of an admissible sequence is exact** in positive degree, over every
field of characteristic `0`. [AFW2006], §3.5, (5.13); [AFW2010], §5.1.4, (72) -/
theorem exists_extDeriv_eq {k : ℕ} {ω : Koszul.PolyForm K (Fin n)}
    (hω : ω ∈ (κ (k + 1)).form K (r (k + 1)) (k + 1)) (hd : Koszul.extDeriv ω = 0) :
    ∃ η ∈ (κ k).form K (r k) k, Koszul.extDeriv η = ω :=
  (κ k).exists_extDeriv_eq (h.transition k) hω hd

end IsAdmissible

/-- The degree `r'` of the `d`-part `dP_{r'+1}Λ^{k-1}`: `r` for `P_rΛᵏ`, `r - 1` for `P_r⁻Λᵏ`. -/
def dDeg : PolyKind → ℕ → ℕ
  | full, r => r
  | trimmed, r => r - 1

theorem le_dDeg (κ : PolyKind) (r : ℕ) : r - 1 ≤ κ.dDeg r := by
  cases κ <;> simp [dDeg]

end PolyKind

end Feec.FiniteElement
