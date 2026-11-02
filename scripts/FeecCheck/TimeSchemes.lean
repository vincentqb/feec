module

public import Feec.HilbertComplex.Approximation.FullyDiscrete

/-!
# Regression test: the time schemes of a dissipative FEEC discretization

`Feec.HilbertComplex.DissipFEEC.TimeScheme` was a structure of its own, with the lemmas
`DissipFEEC.TimeScheme.M_nonneg` and `DissipFEEC.TimeScheme.stable_le`. It is now the time scheme
`Feec.TimeStepping.TimeScheme F.L` of the discrete generators (the schemes of the Banach FEEC
discretization `F.toBanachFEEC`), and the two lemmas are those of `Feec.TimeStepping.TimeScheme`.
Below, the old constructor (the same ten fields) and the two lemmas are stated verbatim and
derived from the new API.

This file is part of the `FeecCheck` library, not of `Feec`.

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

universe u

namespace FeecCheck.TimeSchemes

open Feec Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E} {κ : Type*} (F : DissipFEEC.{u} A κ)

/-- The earlier structure `DissipFEEC.TimeScheme`, field by field ([Thomee2006], Ch. 7). -/
def timeScheme_old (τ : κ → ℝ) (τ_pos : ∀ h, 0 < τ h) (P : ∀ h, F.X h →L[𝕜] F.X h)
    (M : ℝ → ℝ) (stable : ∀ (T : ℝ) (h : κ) (n : ℕ), (n : ℝ) * τ h ≤ T → ‖P h ^ n‖ ≤ M T)
    (p : ℕ) (p_pos : 0 < p) (K : ℝ) (K_nonneg : 0 ≤ K)
    (consistent : ∀ h, TimeStepping.IsConsistent (F.L h) (P h) (τ h) p K) : F.TimeScheme :=
  ⟨τ, τ_pos, P, M, stable, p, p_pos, K, K_nonneg, consistent⟩

variable {F} (Θ : F.TimeScheme)

/-- The earlier `DissipFEEC.TimeScheme.M_nonneg`. -/
theorem M_nonneg_old {T : ℝ} (hT : 0 ≤ T) (h : κ) : 0 ≤ Θ.M T :=
  Θ.M_nonneg hT h

/-- The earlier `DissipFEEC.TimeScheme.stable_le`. -/
theorem stable_le_old {T : ℝ} (h : κ) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ∀ k ≤ n, ‖Θ.P h ^ k‖ ≤ Θ.M T :=
  Θ.stable_le h hn

end FeecCheck.TimeSchemes
