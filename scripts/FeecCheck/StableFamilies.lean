module

public import Feec.TimeStepping.BanachFEEC

/-!
# Regression test: the discrete half of a Banach FEEC discretization

`Feec.TimeStepping.BanachFEEC` was a structure of its own, with the discrete resolvents and
rational schemes in its namespace (`BanachFEEC.M_nonneg`, `BanachFEEC.res`,
`BanachFEEC.norm_res_pow_le`, `BanachFEEC.step`, `BanachFEEC.norm_step_pow_le`,
`BanachFEEC.norm_step_pow_sub_exp_le`, `BanachFEEC.backwardEuler`). It now extends the uniformly
stable family `Feec.TimeStepping.StableFamily` (the same discrete fields and a field
`M_nonneg`, defaulted from `‖S(0)‖ ≤ M`), and these results are those of the family. Below, the
old constructor (the same fields, without `M_nonneg`) and the old statements are stated verbatim
and derived from the new API.

This file is part of the `FeecCheck` library, not of `Feec`.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

universe u

namespace FeecCheck.StableFamilies

open Feec Feec.TimeStepping NormedSpace

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {G : C0Semigroup 𝕜 E} {κ : Type*}

/-- The earlier constructor of `BanachFEEC`, field by field (no `M_nonneg`). -/
def banachFEEC_old (l : Filter κ) (X : κ → Type u) [∀ h, NormedAddCommGroup (X h)]
    [∀ h, NormedSpace 𝕜 (X h)] [∀ h, CompleteSpace (X h)] [∀ h, NormedSpace ℝ (X h)]
    [∀ h, IsScalarTower ℝ 𝕜 (X h)] (L : ∀ h, X h →L[𝕜] X h) (incl : ∀ h, X h →L[𝕜] E)
    (proj : ∀ h, E →L[𝕜] X h) (proj_incl : ∀ h x, proj h (incl h x) = x)
    (bound : ∃ C, ∀ h, ‖incl h‖ ≤ C ∧ ‖proj h‖ ≤ C) (M : ℝ)
    (norm_S_le : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M)
    (norm_exp_le : ∀ h (t : ℝ), 0 ≤ t → ‖exp ((t : 𝕜) • L h)‖ ≤ M) : BanachFEEC.{u} G κ where
  l := l
  X := X
  L := L
  incl := incl
  proj := proj
  proj_incl := proj_incl
  bound := bound
  M := M
  norm_S_le := norm_S_le
  norm_exp_le := norm_exp_le

variable (B : BanachFEEC.{u} G κ)

/-- The earlier `BanachFEEC.M_nonneg`. -/
theorem M_nonneg_old : 0 ≤ B.M := B.M_nonneg

/-- The earlier `BanachFEEC.norm_res_pow_le` (Hille–Yosida stability of backward Euler). -/
theorem norm_res_pow_le_old {τ : ℝ} (hτ : 0 < τ) (h : κ) (n : ℕ) : ‖B.res τ h ^ n‖ ≤ B.M :=
  B.norm_res_pow_le hτ h n

/-- The earlier `BanachFEEC.norm_step_pow_le` ([BrennerThomee1979]). -/
theorem norm_step_pow_le_old {r : RationalScheme} (hr : r.IsAStable) {τ : ℝ} (hτ : 0 < τ)
    (h : κ) (n : ℕ) : ‖B.step r τ h ^ n‖ ≤ B.M * (1 + r.sqrtConst * √n) :=
  B.norm_step_pow_le hr hτ h n

/-- The earlier `BanachFEEC.norm_step_pow_sub_exp_le` ([BrennerThomee1979]). -/
theorem norm_step_pow_sub_exp_le_old {r : RationalScheme} (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (h : κ) (n : ℕ) (v : B.X h) :
    ‖(B.step r τ h ^ n) v - exp (((n * τ : ℝ) : 𝕜) • B.L h) v‖ ≤
      r.sharpConst p * B.M * (n * τ) * τ ^ p * ‖(B.L h ^ (p + 1)) v‖ :=
  B.norm_step_pow_sub_exp_le hr hp hτ h n v

/-- The earlier `BanachFEEC.backwardEuler`, a time scheme of `B`. -/
def backwardEuler_old (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) : B.TimeScheme := B.backwardEuler τ hτ

end FeecCheck.StableFamilies
