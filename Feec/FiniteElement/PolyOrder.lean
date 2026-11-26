module

public import Feec.FiniteElement.PolyInterpolation
public import Feec.FiniteElement.PolyComplex

/-!
# The polynomial order of an admissible sequence

An admissible sequence `S` reproduces the polynomial forms of degree `s` if `P_sΛᵏ` lies in its
space in every form degree (`PolyOrder`), or in the form degrees `j` and `j + 1` (`PolyOrderAt`).
-/

@[expose] public noncomputable section

namespace Feec.FiniteElement

variable {n : ℕ}

namespace PolySeq

variable (S : PolySeq)

theorem polySpace_le_space {k s : ℕ} (hs : s + 1 ≤ S.deg k) :
    polySpace n s k ≤ S.space n k := by
  change polySpace n s k ≤ (S.kind k).space n (S.deg k) k
  cases S.kind k
  · exact polySpace_mono (by omega)
  · exact (polySpace_mono (by omega)).trans (polySpace_le_polyMinusSpace (by omega) k)

theorem polySpace_le_space_of_full {k s : ℕ} (hk : S.kind k = .full) (hs : s ≤ S.deg k) :
    polySpace n s k ≤ S.space n k := by
  change polySpace n s k ≤ (S.kind k).space n (S.deg k) k
  rw [hk]
  exact polySpace_mono hs

theorem polySpace_zero_le_space (k : ℕ) : polySpace n 0 k ≤ S.space n k :=
  S.polySpace_le_space (by have := S.one_le_deg k; omega)

end PolySeq

theorem degPartField_taylorPoly_mem {k s : ℕ} (w : FormField n) (x₀ : Fin n → ℝ) :
    degPartField k (taylorPoly w x₀ (s + 1)) ∈ polySpace n s k :=
  degPartField_mem_polySpace (taylorPoly_mem_polyFunctions w x₀ s) k

variable (n) in
/-- `S` reproduces the polynomial forms of degree `s` in every form degree. -/
def PolyOrder (S : PolySeq) (s : ℕ) : Prop := ∀ k, polySpace n s k ≤ S.space n k

theorem polyOrder_zero (S : PolySeq) : PolyOrder n S 0 := S.polySpace_zero_le_space

variable (n) in
/-- `S` reproduces `P_sΛ` in the form degrees `j` and `j + 1` (vacuous for `j < 0`). -/
def PolyOrderAt (S : PolySeq) (s : ℕ) (j : ℤ) : Prop :=
  ∀ k : ℕ, (k : ℤ) = j → polySpace n s k ≤ S.space n k ∧ polySpace n s (k + 1) ≤ S.space n (k + 1)

theorem PolyOrder.polyOrderAt {S : PolySeq} {s : ℕ} (h : PolyOrder n S s) (j : ℤ) :
    PolyOrderAt n S s j := fun k _ => ⟨h k, h (k + 1)⟩

theorem lagrangeP2_polyOrderAt_zero : PolyOrderAt n PolySeq.lagrangeP2 1 0 := by
  intro k hk
  obtain rfl : k = 0 := by exact_mod_cast hk
  exact ⟨PolySeq.polySpace_le_space_of_full _ (by simp) (by simp),
    PolySeq.polySpace_le_space _ (by simp)⟩

theorem lagrangeP2_polyOrderAt_one : PolyOrderAt n PolySeq.lagrangeP2 1 1 := by
  intro k hk
  obtain rfl : k = 1 := by exact_mod_cast hk
  exact ⟨PolySeq.polySpace_le_space _ (by simp),
    PolySeq.polySpace_le_space_of_full _ (by simp) (by simp)⟩

theorem lagrangeP2_polyOrderAt_window : ∀ i : Fin 2, PolyOrderAt n PolySeq.lagrangeP2 1 (0 + i) :=
  fun i => by
    fin_cases i
    · simpa using lagrangeP2_polyOrderAt_zero (n := n)
    · simpa using lagrangeP2_polyOrderAt_one (n := n)

end Feec.FiniteElement
