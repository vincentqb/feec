module

public import Feec.FiniteElement.PolyInterpolation
public import Feec.FiniteElement.PolyComplex

/-!
# The polynomial order of an admissible sequence

An admissible sequence `S` (`Feec.FiniteElement.PolySeq`, local spaces `P_{r_k}Λᵏ` or
`P_{r_k}⁻Λᵏ`) **reproduces polynomial forms of degree `s`** if `P_sΛᵏ ⊆ P(T)ᵏ` in every form
degree (`PolyOrder`), or only in the degrees `j, j + 1` that the interpolation error in the graph
norm of degree `j` uses (`PolyOrderAt`); its canonical interpolant is then of order `h^{s+1}`
([AFW2006], §5; [Arnold2018], Ch. 7).

* `PolySeq.polySpace_le_space`, `PolySeq.polySpace_le_space_of_full`: `P_sΛᵏ ⊆ P_{r_k}(⁻)Λᵏ`
  for `s + 1 ≤ r_k`, resp. `s ≤ r_k` for the full family; hence every sequence has order `0`
  (`PolySeq.polySpace_zero_le_space`, `polyOrder_zero`);
* the bottom row `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` (`PolySeq.lagrangeP2`) has order `1` in the form
  degrees `0, 1, 2` (`lagrangeP2_polyOrderAt_zero`, `lagrangeP2_polyOrderAt_one`,
  `lagrangeP2_polyOrderAt_window`);
* the degree-`k` part of the Taylor polynomial of order `s` of a form lies in `P_sΛᵏ`
  (`degPartField_taylorPoly_mem`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5 (the polynomial spaces `P_rΛᵏ`, `P_r⁻Λᵏ`)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (approximation
  estimates)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.FiniteElement

variable {n : ℕ}

namespace PolySeq

variable (S : PolySeq)

/-- `P_sΛᵏ ⊆ P_{r_k}Λᵏ` and `⊆ P_{r_k}⁻Λᵏ` for `s + 1 ≤ r_k`. -/
theorem polySpace_le_space {k s : ℕ} (hs : s + 1 ≤ S.deg k) :
    polySpace n s k ≤ S.space n k := by
  change polySpace n s k ≤ (S.kind k).space n (S.deg k) k
  cases S.kind k
  · exact polySpace_mono (by omega)
  · exact (polySpace_mono (by omega)).trans (polySpace_le_polyMinusSpace (S.deg k) k)

/-- `P_sΛᵏ ⊆ P_{r_k}Λᵏ` for `s ≤ r_k` when the sequence uses the full family in degree `k`. -/
theorem polySpace_le_space_of_full {k s : ℕ} (hk : S.kind k = .full) (hs : s ≤ S.deg k) :
    polySpace n s k ≤ S.space n k := by
  change polySpace n s k ≤ (S.kind k).space n (S.deg k) k
  rw [hk]
  exact polySpace_mono hs

/-- `P_0Λᵏ ⊆ P(T)ᵏ` for every admissible sequence (`1 ≤ r_k`). -/
theorem polySpace_zero_le_space (k : ℕ) : polySpace n 0 k ≤ S.space n k :=
  S.polySpace_le_space (by have := S.one_le_deg k; omega)

end PolySeq

theorem degPartField_taylorPoly_mem {k s : ℕ} (w : FormField n) (x₀ : Fin n → ℝ) :
    degPartField k (taylorPoly w x₀ (s + 1)) ∈ polySpace n s k :=
  degPartField_mem_polySpace (taylorPoly_mem_polyFunctions w x₀ s) k

/-! ### The approximation order of an admissible sequence -/

variable (n) in
/-- The sequence `S` **reproduces polynomial forms of degree `s`** in every form degree:
`P_sΛᵏ ⊆ P(T)ᵏ` for all `k`, so that its canonical interpolant is of order `h^{s+1}`. -/
def PolyOrder (S : PolySeq) (s : ℕ) : Prop := ∀ k, polySpace n s k ≤ S.space n k

/-- Every admissible sequence has order `h` (`s = 0`). -/
theorem polyOrder_zero (S : PolySeq) : PolyOrder n S 0 := S.polySpace_zero_le_space

variable (n) in
/-- **Degreewise order**: `S` reproduces polynomial forms of degree `s` in the form degrees `j`
and `j + 1` (vacuous for `j < 0`), which is all the interpolation error in the graph norm of
degree `j` uses. -/
def PolyOrderAt (S : PolySeq) (s : ℕ) (j : ℤ) : Prop :=
  ∀ k : ℕ, (k : ℤ) = j → polySpace n s k ≤ S.space n k ∧ polySpace n s (k + 1) ≤ S.space n (k + 1)

/-- An order in every degree is an order in each degree. -/
theorem PolyOrder.polyOrderAt {S : PolySeq} {s : ℕ} (h : PolyOrder n S s) (j : ℤ) :
    PolyOrderAt n S s j := fun k _ => ⟨h k, h (k + 1)⟩

/-- The bottom row `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` reproduces `P₁` in the form degrees `0, 1`. -/
theorem lagrangeP2_polyOrderAt_zero : PolyOrderAt n PolySeq.lagrangeP2 1 0 := by
  intro k hk
  obtain rfl : k = 0 := by exact_mod_cast hk
  exact ⟨PolySeq.polySpace_le_space_of_full _ (by simp) (by simp),
    PolySeq.polySpace_le_space _ (by simp)⟩

/-- The bottom row `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` reproduces `P₁` in the form degrees `1, 2`. -/
theorem lagrangeP2_polyOrderAt_one : PolyOrderAt n PolySeq.lagrangeP2 1 1 := by
  intro k hk
  obtain rfl : k = 1 := by exact_mod_cast hk
  exact ⟨PolySeq.polySpace_le_space _ (by simp),
    PolySeq.polySpace_le_space_of_full _ (by simp) (by simp)⟩

/-- The bottom row reproduces `P₁` on the window `0, 1` (form degrees `0, 1, 2`). -/
theorem lagrangeP2_polyOrderAt_window : ∀ i : Fin 2, PolyOrderAt n PolySeq.lagrangeP2 1 (0 + i) :=
  fun i => by
    fin_cases i
    · simpa using lagrangeP2_polyOrderAt_zero (n := n)
    · simpa using lagrangeP2_polyOrderAt_one (n := n)

end Feec.FiniteElement
