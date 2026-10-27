import Feec.Instances.Corollaries

/-!
# Regression tests: the slip Stokes witness on the cube

The cube instance of slip Stokes flow (`Feec.Instances.Corollaries.Cube.FEM.slipStokes`) exhibited
a nonzero datum of the constraint `ker 𝐝†` only in degree `0` (the constant `0`-form, through the
helper `exists_ne_zero_window`); it now exhibits a nonzero velocity field in degree `1` for
`n ≥ 2` (`Feec.HilbertComplex.exists_mem_orthogonal_cycles_inf_domain`,
`Feec.Domain.maximalComplex_cycles_one_ne_top`). The theorems `slip_old_*` state the deleted
results verbatim and derive them from the new API.

This file is part of the `FeecCheck` library, not of `Feec`.
-/

open Set LinearPMap

namespace FeecCheck.SlipStokes

open Feec Feec.HilbertComplex Feec.Instances.Corollaries Feec.Models.Cube.FEM Feec.FiniteElement
open Feec.Domain (L2F formIdx)

variable (n : ℕ)

/-- The old `Cube.FEM.exists_ne_zero_window`: the constant `0`-form, nonzero, in the first degree
of a window `HΛ⁰(Q) → ⋯`. -/
theorem slip_old_exists_ne_zero_window (m : ℕ) :
    ∃ v : L2F ℝ (cubeDomain n) (formIdx n (0 + (((0 : Fin (m + 1)) : ℕ) : ℤ))), v ≠ 0 := by
  rw [show (0 : ℤ) + (((0 : Fin (m + 1)) : ℕ) : ℤ) = 0 by simp]
  exact ⟨oneForm n, oneForm_ne_zero⟩

/-- The old `Cube.FEM.slipStokes`, every `n ≥ 1`: the conclusions of `slipStokes` for the window
`HΛ⁰(Q) → ⋯ → HΛⁿ(Q)` and a nonzero datum of `ker 𝐝†`, in degree `0`. -/
theorem slip_old_slipStokes [NeZero n] (S : PolySeq) :
    ((slipStokesFEEC (polyFamily n S) 0 (n + 1)).toHeat.Verdict
        ((slipStokesFEEC (polyFamily n S) 0 (n + 1)).heatCore (closedRangeAt_heatWindow n)) ∧
      (slipStokesFEEC (polyFamily n S) 0 (n + 1)).toHeat.Keeps
        (slipStokesFEEC (polyFamily n S) 0 (n + 1)).toHeat.K) ∧
      ∃ x ∈ ((heatWindow n).totalD†).ker, x ≠ 0 := by
  classical
  obtain ⟨V, hK, -⟩ := Feec.Instances.Corollaries.slipStokes (polyFamily n S) 0 (n + 1)
    (closedRangeAt_heatWindow n)
  obtain ⟨v, hv⟩ := slip_old_exists_ne_zero_window n n
  refine ⟨⟨V, hK⟩, PiLp.single 2 0 v,
    (heatWindow n).single_mem_ker_adjoint_totalD (fun j => by simp) v, fun h => hv ?_⟩
  simpa using congrArg (fun z => z 0) h

end FeecCheck.SlipStokes
