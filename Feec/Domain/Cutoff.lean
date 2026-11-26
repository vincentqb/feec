module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.Support

/-!
# Smooth cut-offs

The derivative `dχ` of the smooth transition `χ = Real.smoothTransition` is nonnegative,
continuous, supported in `[0, 1]` and bounded.
-/

@[expose] public noncomputable section

open Set

namespace Feec.Domain

/-- `χ'`, the derivative of the smooth transition. -/
def dχ (s : ℝ) : ℝ := deriv Real.smoothTransition s

theorem dχ_nonneg (s : ℝ) : 0 ≤ dχ s := Real.smoothTransition.monotone.deriv_nonneg

theorem hasDerivAt_χ (s : ℝ) : HasDerivAt Real.smoothTransition (dχ s) s :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero s).hasDerivAt

theorem continuous_dχ : Continuous dχ :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

theorem dχ_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : dχ s = 0 := by
  have h := hasDerivAt_χ s
  have hl : HasDerivWithinAt Real.smoothTransition 0 (Iic s) s :=
    (hasDerivWithinAt_const s (Iic s) (0 : ℝ)).congr
      (fun y hy => Real.smoothTransition.zero_of_nonpos (le_trans hy hs))
      (Real.smoothTransition.zero_of_nonpos hs)
  exact (uniqueDiffWithinAt_Iic s).eq_deriv _ (h.hasDerivWithinAt) hl

theorem dχ_eq_zero_of_one_le {s : ℝ} (hs : 1 ≤ s) : dχ s = 0 := by
  have h := hasDerivAt_χ s
  have hl : HasDerivWithinAt Real.smoothTransition 0 (Ici s) s :=
    (hasDerivWithinAt_const s (Ici s) (1 : ℝ)).congr
      (fun y hy => Real.smoothTransition.one_of_one_le (le_trans hs hy))
      (Real.smoothTransition.one_of_one_le hs)
  exact (uniqueDiffWithinAt_Ici s).eq_deriv _ (h.hasDerivWithinAt) hl

theorem exists_abs_dχ_le : ∃ D, ∀ s, |dχ s| ≤ D := by
  have hc : HasCompactSupport dχ := HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ))
    (b := 1)) fun s hs => by
      rw [mem_Icc, not_and_or, not_le, not_le] at hs
      rcases hs with hs | hs
      · exact dχ_eq_zero_of_nonpos hs.le
      · exact dχ_eq_zero_of_one_le hs.le
  obtain ⟨D, hD⟩ := continuous_dχ.bounded_above_of_compact_support hc
  exact ⟨D, fun s => by simpa using hD s⟩

end Feec.Domain
