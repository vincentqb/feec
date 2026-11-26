module

public import Feec.HilbertComplex.Approximation.HeatFEEC
public import Feec.Models.ConformingFamilies
public import Feec.Models.Cube.DeRhamIdentFEM

/-!
# The heat FEEC theorem on the cube

The heat FEEC theorem holds for the Hodge heat equation of `HΛ⁰(Q) → ⋯ → HΛⁿ(Q)` on
`Q = (0, ½)ⁿ`, with a nonzero datum in its core (`FEM.crown_heat_nonvacuous`).
-/

open Filter Topology

@[expose] public noncomputable section

namespace Feec.Models.Cube.FEM

open Feec.HilbertComplex Feec.FiniteElement
open Feec.Domain (L2F formIdx)

variable (n : ℕ)

/-- The window `HΛ⁰(Q) → ⋯ → HΛⁿ(Q)` of `HΛ(Q)`: all its nonzero spaces. -/
abbrev heatWindow := (complex n).window 0 (n + 1)

theorem hasCompactProperty_heatWindow : (heatWindow n).HasCompactProperty :=
  hasCompactProperty_window hasCompactProperty 0 (n + 1)
    (DeRhamIdent.hlow _ _ (by norm_num)) (DeRhamIdent.hhigh _ _ (by simp))

theorem closedRangeAt_heatWindow (i : Fin (n + 1)) : (heatWindow n).ClosedRangeAt i :=
  ((hasCompactProperty_heatWindow n) i).closed_and_fredholm.1

instance (i : Fin (n + 1)) : FiniteDimensional ℝ ((heatWindow n).harmonic i) :=
  ((hasCompactProperty_heatWindow n) i).closed_and_fredholm.2.2.1

theorem exists_mem_heatCore_data_ne_zero {κ : Type*} (F : (heatWindow n).ConstrainedFEEC κ)
    (hb : ∀ i, F.IsGraphBounded i) :
    ∃ x ∈ (F.heatCore (closedRangeAt_heatWindow n) hb).Data, x ≠ 0 := by
  have : Nontrivial (L2F ℝ (cubeDomain n) (formIdx n (0 + (((0 : Fin (n + 1)) : ℕ) : ℤ)))) := by
    rw [show (0 : ℤ) + (((0 : Fin (n + 1)) : ℕ) : ℤ) = 0 by simp]
    exact ⟨⟨oneForm n, 0, oneForm_ne_zero⟩⟩
  exact F.exists_mem_heatCore_data_ne_zero _ hb

variable [NeZero n]

/-- **The finite element complexes of `S` on the window**, a constrained FEEC discretization. -/
def heatFamily (S : PolySeq) : (heatWindow n).ConstrainedFEEC ℕ :=
  ((polyFamily n S).window 0 (n + 1)).withConstraint ⊤
    (by rw [Submodule.top_coe]; exact isClosed_univ)

theorem isGraphBounded_heatFamily (S : PolySeq) : ∀ i, (heatFamily n S).IsGraphBounded i :=
  ((polyFamily n S).window 0 (n + 1)).isGraphBounded_toSubcomplexFamily

/-- **The heat FEEC theorem on the cube**, with a nonzero datum in its core `D(Δ²)`. -/
theorem crown_heat_nonvacuous (S : PolySeq) :
    (heatFamily n S).toHeat.Verdict ((heatFamily n S).heatCore (closedRangeAt_heatWindow n)
        (isGraphBounded_heatFamily n S)) ∧
      ∃ x ∈ ((heatFamily n S).heatCore (closedRangeAt_heatWindow n)
        (isGraphBounded_heatFamily n S)).Data, x ≠ 0 :=
  ⟨(heatFamily n S).heatFEEC _ _, exists_mem_heatCore_data_ne_zero n _ _⟩

end Feec.Models.Cube.FEM
