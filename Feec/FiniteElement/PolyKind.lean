module

public import Feec.Algebra.PolynomialFormDim
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Nat.Choose.Sum

/-!
# The two families `P_rΛᵏ`, `P_r⁻Λᵏ` of the periodic table, over a field

The algebraic layer of the element families of `Feec.FiniteElement.PolyElement`: the kinds
`Feec.FiniteElement.PolyKind` (`full`: `P_rΛᵏ`, `trimmed`: `P_r⁻Λᵏ`), the admissible transitions
`PolyKind.Transition` between consecutive form degrees ([AFW2006], §5; [AFW2010], §5.2), and the
shape spaces and test forms of the degrees of freedom as spaces of polynomial forms
(`Feec.Koszul.PolyForm`) over a commutative ring `K` (`PolyKind.form`, `PolyKind.testForm`). Only
`Feec.Algebra` is imported: the form fields over `ℝ` are their evaluations
(`PolyKind.space_eq_map_form` in `Feec.FiniteElement.PolyElement`).

## Main results

* `PolyKind.extDeriv_mem_form`: `d` maps the source space into the target space of an admissible
  transition, over every commutative ring;
* `PolyKind.exists_extDeriv_eq`, `PolyKind.mem_polyForm_zero_of_extDeriv_eq_zero`: exactness along
  a transition and constant closed `0`-forms, over every field of characteristic `0`;
* `PolyKind.finrank_testForm`, `PolyKind.finrank_form_eq_sum`: **`dim = #DOF`**,
  `dim P_rΛᵏ(Kⁿ) = Σ_{m ≤ n} C(n+1, m+1) dim(test forms on m-faces)` and likewise for `P_r⁻Λᵏ`
  ([AFW2006], Thms 4.9, 4.13), via the Vandermonde identity `sum_choose_mul_choose_eq`;
* `PolyKind.IsAdmissible`: the admissible sequences of [AFW2006], §3.5, (5.13), including those
  whose degree reaches `0` (a full space `P_0Λᵏ`, then `0`; `PolyKind.form₀`), their polynomial
  complexes (`IsAdmissible.extDeriv_mem`) and exactness (`IsAdmissible.exists_extDeriv_eq`,
  `IsAdmissible.mem_polyForm_zero_of_extDeriv_eq_zero`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3 (§3.5), §4 (Thms 4.9, 4.13), §5 (§5.5, (5.13))
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.1.4, §5.2

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset

@[expose] public noncomputable section

namespace Feec.FiniteElement

variable {n : ℕ}

/-- The binomial identity behind the dimension count of the degrees of freedom ([AFW2006],
Thm 4.9): `Σ_{m=k}^{n} (n+1 choose m+1) (r-1 choose m-k) = (n + r choose n - k)`. -/
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

/-! ### The two polynomial families -/

/-- The two families of polynomial differential forms of finite element exterior calculus: the
full spaces `P_rΛᵏ` and the trimmed spaces `P_r⁻Λᵏ` ([AFW2006], §3). -/
inductive PolyKind
  /-- `P_rΛᵏ` -/
  | full
  /-- `P_r⁻Λᵏ` -/
  | trimmed
  deriving DecidableEq

namespace PolyKind

/-- The dimension of the test space: `C(r+k, r) C(r-1, m-k)` for `P_rΛᵏ`, `C(r+k-1, r-1)
C(r-1, m-k)` for `P_r⁻Λᵏ`, when `k ≤ m < r + k`, and `0` otherwise. -/
def testDim (κ : PolyKind) (r k m : ℕ) : ℕ :=
  (match κ with
    | full => (r + k).choose r
    | trimmed => (r + k - 1).choose (r - 1)) *
  if k ≤ m ∧ m < r + k then (r - 1).choose (m - k) else 0

/-- **The admissible transitions** `Xᵏ → Yᵏ⁺¹` of the two families ([AFW2006], §5; [AFW2010],
§5.2): from `P_rΛᵏ` or `P_r⁻Λᵏ` the exterior derivative maps into `P_r⁻Λᵏ⁺¹` and into
`P_{r-1}Λᵏ⁺¹`. The condition on the target `(κ', r')` does not depend on the kind of the
source. -/
def Transition (r : ℕ) (κ' : PolyKind) (r' : ℕ) : Prop :=
  (κ' = trimmed ∧ r' = r) ∨ (κ' = full ∧ r' + 1 = r)

section CommRing

variable (K : Type*) [CommRing K]

/-- The polynomial forms of the family over `K`, `P_rΛᵏ(Kⁿ)` or `P_r⁻Λᵏ(Kⁿ)`, in
`Koszul.PolyForm`. -/
def form : PolyKind → ℕ → ℕ → Submodule K (Koszul.PolyForm K (Fin n))
  | full, r, k => Koszul.polyForm K (Fin n) r k
  | trimmed, r, k => Koszul.polyFormMinus K (Fin n) r k

/-- The test forms over `K` of the degrees of freedom of the family on `m`-faces:
`P⁻_{r+k-m}Λ^{m-k}(Kᵐ)` for `P_rΛᵏ` and `P_{r+k-m-1}Λ^{m-k}(Kᵐ)` for `P_r⁻Λᵏ`, when
`k ≤ m < r + k`, and `0` otherwise ([AFW2006], Thms 4.9, 4.13). -/
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

/-- `P_r⁻Λᵏ ⊆ P_rΛᵏ` (`r ≥ 1`): both families lie in `P_rΛᵏ`. -/
theorem form_le_polyForm (κ : PolyKind) {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    κ.form K r k ≤ Koszul.polyForm K (Fin n) r k := by
  cases κ
  · exact le_rfl
  · exact Koszul.polyFormMinus_le_polyForm hr k

/-- Both families contain `P_r⁻Λᵏ` (`r ≥ 1`). -/
theorem polyFormMinus_le_form (κ : PolyKind) {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    Koszul.polyFormMinus K (Fin n) r k ≤ κ.form K r k := by
  cases κ
  · exact Koszul.polyFormMinus_le_polyForm hr k
  · exact le_rfl

/-- The target `P_r⁻Λᵏ` or `P_{r-1}Λᵏ` of an admissible transition from degree `r` lies in
`P_r⁻Λᵏ`. -/
theorem form_le_polyFormMinus {r : ℕ} {κ' : PolyKind} {r' : ℕ} (ht : Transition r κ' r')
    (k : ℕ) : κ'.form K r' k ≤ Koszul.polyFormMinus K (Fin n) r k := by
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact le_rfl
  · simpa using Koszul.polyForm_le_polyFormMinus (R := K) (d := Fin n) (r' + 1) k

/-- **`d` along an admissible transition**, over every commutative ring: `d P_rΛᵏ` and
`d P_r⁻Λᵏ` lie in `P_{r-1}Λᵏ⁺¹ ⊆ P_r⁻Λᵏ⁺¹`. [AFW2006], §5; [AFW2010], §5.2 -/
theorem extDeriv_mem_form (κ : PolyKind) {r : ℕ} {κ' : PolyKind} {r' : ℕ}
    (ht : Transition r κ' r') {k : ℕ} {ω : Koszul.PolyForm K (Fin n)} (hω : ω ∈ κ.form K r k) :
    Koszul.extDeriv ω ∈ κ'.form K r' (k + 1) := by
  have h : Koszul.extDeriv ω ∈ Koszul.polyForm K (Fin n) (r - 1) (k + 1) := by
    cases κ
    · exact Koszul.extDeriv_mem_polyForm hω
    · exact Koszul.extDeriv_mem_polyForm_sub_one_of_mem_polyFormMinus hω
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Koszul.polyForm_le_polyFormMinus _ _ h
  · simpa using h

end CommRing

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- **Exactness along an admissible transition** (`K` of characteristic `0`, `r ≥ 1`): a closed
form of the target space is `d η` with `η` in the source space (in `P_r⁻Λᵏ`).
[AFW2010], §5.1.4, (72) -/
theorem exists_extDeriv_eq (κ : PolyKind) {r : ℕ} (hr : 1 ≤ r) {κ' : PolyKind} {r' : ℕ}
    (ht : Transition r κ' r') {k : ℕ} {ω : Koszul.PolyForm K (Fin n)}
    (hω : ω ∈ κ'.form K r' (k + 1)) (hd : Koszul.extDeriv ω = 0) :
    ∃ η ∈ κ.form K r k, Koszul.extDeriv η = ω :=
  let ⟨η, hη, he⟩ :=
    Koszul.exists_extDeriv_eq_of_mem_polyFormMinus hr (form_le_polyFormMinus ht _ hω) hd
  ⟨η, κ.polyFormMinus_le_form hr k hη, he⟩

/-- **The closed `0`-forms are the constants** (`K` of characteristic `0`, `r ≥ 1`). -/
theorem mem_polyForm_zero_of_extDeriv_eq_zero (κ : PolyKind) {r : ℕ} (hr : 1 ≤ r)
    {ω : Koszul.PolyForm K (Fin n)} (hω : ω ∈ κ.form K r 0) (hd : Koszul.extDeriv ω = 0) :
    ω ∈ Koszul.polyForm K (Fin n) 0 0 :=
  Koszul.mem_polyForm_zero_of_extDeriv_eq_zero (κ.form_le_polyForm hr 0 hω).1 hd

/-- `dim` of the test forms, over every field of characteristic `0`. -/
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
`Σ_{m ≤ n} C(n+1, m+1) dim(test forms on m-faces)`, over every field of characteristic `0`
([AFW2006], Thms 4.9, 4.13). -/
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

/-! ### Admissible sequences of polynomial form spaces

An admissible sequence of [AFW2006], §3.5, (5.13) chooses in every form degree a full or a trimmed
space along admissible transitions. Its degree may reach `0` before the top form degree, at a full
space `P_0Λᵏ`; every later space is then `P_0⁻Λ = 0` (`form₀`, `IsAdmissible`). The sequences of
the element families keep `r_k ≥ 1` (`Feec.FiniteElement.PolySeq`, `PolySeq.isAdmissible`). -/

section Seq

variable (K : Type*) [CommRing K]

/-- The polynomial forms of the family over `K` with the convention `P_0⁻Λᵏ = 0` of [AFW2006],
§3.3: `form`, except `P_0⁻Λᵏ` (`Koszul.polyFormMinus` truncates `r - 1` at `0`). -/
def form₀ : PolyKind → ℕ → ℕ → Submodule K (Koszul.PolyForm K (Fin n))
  | full, r, k => Koszul.polyForm K (Fin n) r k
  | trimmed, 0, _ => ⊥
  | trimmed, r + 1, k => Koszul.polyFormMinus K (Fin n) (r + 1) k

variable {K}

theorem form₀_of_one_le (κ : PolyKind) {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    κ.form₀ K (n := n) r k = κ.form K r k := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  cases κ <;> rfl

/-- **An admissible sequence** of spaces of polynomial forms ([AFW2006], §3.5, (5.13)): in every
form degree `k` the space `P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` of the family `κ k` (`form₀`), `r_0 ≥ 1`,
consecutive degrees related by admissible transitions. The degree reaches `0` only at a full space
`P_0Λᵏ`, after which every space is `P_0⁻Λ = 0`. -/
structure IsAdmissible (κ : ℕ → PolyKind) (r : ℕ → ℕ) : Prop where
  one_le : 1 ≤ r 0
  transition (k : ℕ) : Transition (r k) (κ (k + 1)) (r (k + 1))

end Seq

section SeqField

variable {K : Type*} [Field K]

/-- **`d` along an admissible transition**, with `P_0⁻Λ = 0`: `d` maps `κ.form₀ K r k` into
`κ'.form₀ K r' (k + 1)` (from `r = 0` the target is `0` and the source consists of constant
forms). -/
theorem extDeriv_mem_form₀ (κ : PolyKind) {r : ℕ} {κ' : PolyKind} {r' : ℕ}
    (ht : Transition r κ' r') {k : ℕ} {ω : Koszul.PolyForm K (Fin n)} (hω : ω ∈ κ.form₀ K r k) :
    Koszul.extDeriv ω ∈ κ'.form₀ K r' (k + 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 : ω ∈ Koszul.polyForm K (Fin n) 0 k := by
      cases κ
      · exact hω
      · rw [(Submodule.mem_bot K).1 hω]; exact zero_mem _
    rw [Koszul.extDeriv_eq_zero_of_mem_polyForm_zero h0]
    exact zero_mem _
  · have h := κ.extDeriv_mem_form (K := K) ht (by rwa [← κ.form₀_of_one_le hr])
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rwa [form₀_of_one_le _ hr]
    · exact h

/-- **Exactness along an admissible transition**, with `P_0⁻Λ = 0` (`K` of characteristic `0`):
a closed form of `κ'.form₀ K r' (k + 1)` is `d η`, `η ∈ κ.form₀ K r k`. -/
theorem exists_extDeriv_eq_of_mem_form₀ [CharZero K] (κ : PolyKind) {r : ℕ} {κ' : PolyKind}
    {r' : ℕ} (ht : Transition r κ' r') {k : ℕ} {ω : Koszul.PolyForm K (Fin n)}
    (hω : ω ∈ κ'.form₀ K r' (k + 1)) (hd : Koszul.extDeriv ω = 0) :
    ∃ η ∈ κ.form₀ K r k, Koszul.extDeriv η = ω := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · obtain ⟨rfl, rfl⟩ : κ' = trimmed ∧ r' = 0 := ht.resolve_right (by omega)
    exact ⟨0, zero_mem _, by rw [Koszul.extDeriv_zero, (Submodule.mem_bot K).1 hω]⟩
  · rw [κ.form₀_of_one_le hr]
    refine κ.exists_extDeriv_eq hr ht ?_ hd
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rwa [form₀_of_one_le _ hr] at hω
    · exact hω

namespace IsAdmissible

variable {κ : ℕ → PolyKind} {r : ℕ → ℕ} (h : IsAdmissible κ r)
include h

/-- **The polynomial complex of an admissible sequence**: `d` maps each space into the next. -/
theorem extDeriv_mem {k : ℕ} {ω : Koszul.PolyForm K (Fin n)} (hω : ω ∈ (κ k).form₀ K (r k) k) :
    Koszul.extDeriv ω ∈ (κ (k + 1)).form₀ K (r (k + 1)) (k + 1) :=
  (κ k).extDeriv_mem_form₀ (h.transition k) hω

/-- **The polynomial complex of an admissible sequence is exact** in positive degree, over every
field of characteristic `0`. [AFW2006], §3.5, (5.13); [AFW2010], §5.1.4, (72) -/
theorem exists_extDeriv_eq [CharZero K] {k : ℕ} {ω : Koszul.PolyForm K (Fin n)}
    (hω : ω ∈ (κ (k + 1)).form₀ K (r (k + 1)) (k + 1)) (hd : Koszul.extDeriv ω = 0) :
    ∃ η ∈ (κ k).form₀ K (r k) k, Koszul.extDeriv η = ω :=
  (κ k).exists_extDeriv_eq_of_mem_form₀ (h.transition k) hω hd

/-- **The closed `0`-forms of an admissible sequence are the constants**, over every field of
characteristic `0`. -/
theorem mem_polyForm_zero_of_extDeriv_eq_zero [CharZero K] {ω : Koszul.PolyForm K (Fin n)}
    (hω : ω ∈ (κ 0).form₀ K (r 0) 0) (hd : Koszul.extDeriv ω = 0) :
    ω ∈ Koszul.polyForm K (Fin n) 0 0 :=
  (κ 0).mem_polyForm_zero_of_extDeriv_eq_zero h.one_le
    (by rwa [← (κ 0).form₀_of_one_le h.one_le]) hd

/-- The space of degree `0` lies in `P_{r_0}Λ⁰` and contains the constants. -/
theorem polyForm_zero_le_form₀_le :
    Koszul.polyForm K (Fin n) 0 0 ≤ (κ 0).form₀ K (r 0) 0 ∧
      (κ 0).form₀ K (r 0) 0 ≤ Koszul.polyForm K (Fin n) (r 0) 0 := by
  rw [(κ 0).form₀_of_one_le h.one_le]
  exact ⟨(Koszul.polyForm_mono (Nat.zero_le _) 0).trans
    ((Koszul.polyForm_le_polyFormMinus _ 0).trans ((κ 0).polyFormMinus_le_form h.one_le 0)),
    (κ 0).form_le_polyForm h.one_le 0⟩

end IsAdmissible

end SeqField

/-- The degree `r'` of the `d`-part `dP_{r'+1}Λ^{k-1}` of the family: `r` for `P_rΛᵏ`, `r - 1`
for `P_r⁻Λᵏ`. -/
def dDeg : PolyKind → ℕ → ℕ
  | full, r => r
  | trimmed, r => r - 1

theorem le_dDeg (κ : PolyKind) (r : ℕ) : r - 1 ≤ κ.dDeg r := by
  cases κ <;> simp [dDeg]

end PolyKind

end Feec.FiniteElement
