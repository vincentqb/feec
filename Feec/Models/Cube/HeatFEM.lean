module

public import Feec.HilbertComplex.Approximation.HeatFEEC
public import Feec.Models.ConformingFamilies
public import Feec.Models.Cube.DeRhamIdentFEM

/-!
# The heat FEEC theorem on the cube

The window `HΛ⁰(Q) → ⋯ → HΛⁿ(Q)` of the de Rham complex of the cube `Q = (0, ½)ⁿ`
(`FEM.heatWindow n`, all its nonzero spaces) has the compactness property
(`hasCompactProperty_heatWindow`, from that of `HΛ(Q)` on `ℤ`,
`HilbertComplex.hasCompactProperty_window`), hence closed range and finite-dimensional harmonic
forms in every degree. The finite element complexes of every admissible sequence `S` on the
Freudenthal meshes (`FEM.polyFamily`), restricted to the window, are a constrained FEEC
discretization (`FEM.heatFamily n S`, constraint `⊤`), so the heat FEEC theorem
(`ConstrainedFEEC.heatFEEC_verdict`) holds for the Hodge heat equation on the cube, and it is not
vacuous: its core `D(Δ²)` contains nonzero data (`crown_heat_nonvacuous`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.4 (Thm 3.9), §5 (the spaces `P_rΛ`, `P_r⁻Λ`)
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]
  (the Hodge heat equation in FEEC)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Filter Topology

@[expose] public noncomputable section

namespace Feec.Models.Cube.FEM

open Feec.HilbertComplex Feec.FiniteElement
open Feec.Domain (L2F formIdx)

variable (n : ℕ)

/-- The window `HΛ⁰(Q) → ⋯ → HΛⁿ(Q)` of `HΛ(Q)`: all its nonzero spaces. -/
abbrev heatWindow := (complex n).window 0 (n + 1)

/-- **The compactness property of the window** (the spaces of `HΛ(Q)` outside it are zero). -/
theorem hasCompactProperty_heatWindow : (heatWindow n).HasCompactProperty :=
  hasCompactProperty_window hasCompactProperty 0 (n + 1)
    (DeRhamIdent.hlow _ _ (by norm_num)) (DeRhamIdent.hhigh _ _ (by simp))

theorem closedRangeAt_heatWindow (i : Fin (n + 1)) : (heatWindow n).ClosedRangeAt i :=
  ((hasCompactProperty_heatWindow n) i).closed_and_fredholm.1

instance (i : Fin (n + 1)) : FiniteDimensional ℝ ((heatWindow n).harmonic i) :=
  ((hasCompactProperty_heatWindow n) i).closed_and_fredholm.2.2.1

variable [NeZero n]

/-- **The finite element complexes of an admissible sequence `S` on the window**, a constrained
FEEC discretization of the window with the trivial constraint `⊤`. -/
def heatFamily (S : PolySeq) : (heatWindow n).ConstrainedFEEC ℕ :=
  ((polyFamily n S).window 0 (n + 1)).withConstraint ⊤
    (by rw [Submodule.top_coe]; exact isClosed_univ)

/-- **The heat FEEC theorem on the cube, not vacuously**: for every admissible sequence `S`, the
heat FEEC verdict holds for the Hodge heat equation of the window `HΛ⁰(Q) → ⋯ → HΛⁿ(Q)` and its
core `D(Δ²)` contains a nonzero datum. -/
theorem crown_heat_nonvacuous (S : PolySeq) :
    (heatFamily n S).toHeat.Verdict ((heatFamily n S).heatCore (closedRangeAt_heatWindow n)) ∧
      ∃ x ∈ ((heatFamily n S).heatCore (closedRangeAt_heatWindow n)).Data, x ≠ 0 := by
  refine ⟨(heatFamily n S).heatFEEC_verdict _, ?_⟩
  have hd : Dense (((heatFamily n S).heatCore (closedRangeAt_heatWindow n)).Data :
      Set (PiLp 2 fun i : Fin (n + 1) => L2F ℝ (cubeDomain n) (formIdx n (0 + ((i : ℕ) : ℤ))))) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 ((heatFamily n S).dense_heatCore_data _)
  have : Nontrivial (L2F ℝ (cubeDomain n) (formIdx n (0 + (((0 : Fin (n + 1)) : ℕ) : ℤ)))) := by
    rw [show (0 : ℤ) + (((0 : Fin (n + 1)) : ℕ) : ℤ) = 0 by simp]
    exact ⟨⟨oneForm n, 0, oneForm_ne_zero⟩⟩
  obtain ⟨v, hv⟩ :=
    exists_ne (0 : L2F ℝ (cubeDomain n) (formIdx n (0 + (((0 : Fin (n + 1)) : ℕ) : ℤ))))
  set y : PiLp 2 fun i : Fin (n + 1) => L2F ℝ (cubeDomain n) (formIdx n (0 + ((i : ℕ) : ℤ))) :=
    PiLp.single 2 0 v
  have hy : y ≠ 0 := fun h => hv (by simpa [y] using congrArg (fun z => z 0) h)
  exact hd.exists_mem_open isOpen_ne ⟨y, hy⟩

end Feec.Models.Cube.FEM
