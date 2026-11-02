module

public import Feec.TimeStepping.BanachFEEC

/-!
# Regression test: the discrete half of a Banach FEEC discretization

`Feec.TimeStepping.BanachFEEC` was a structure of its own, with the discrete resolvents and
rational schemes in its namespace (`BanachFEEC.M_nonneg`, `BanachFEEC.discrete`,
`BanachFEEC.norm_discrete_S_le`, `BanachFEEC.norm_discrete_S_le_exp`, `BanachFEEC.res`,
`BanachFEEC.res_apply_sub`, `BanachFEEC.norm_res_pow_le`, `BanachFEEC.step`,
`BanachFEEC.step_theta_one`, `BanachFEEC.norm_step_pow_le`, `BanachFEEC.norm_step_pow_sub_exp_le`,
`BanachFEEC.rationalScheme`, `BanachFEEC.backwardEuler`). It now extends the uniformly
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

/-- The earlier `BanachFEEC.discrete`: the discrete semigroups `e^{tLₕ}`. -/
abbrev discrete_old (h : κ) : C0Semigroup 𝕜 (B.X h) := (C0Group.ofBounded (B.L h)).toC0Semigroup

theorem discrete_old_eq (h : κ) : discrete_old B h = B.discrete h := rfl

/-- The earlier `BanachFEEC.norm_discrete_S_le`. -/
theorem norm_discrete_S_le_old (h : κ) (t : ℝ) (ht : 0 ≤ t) : ‖(B.discrete h).S t‖ ≤ B.M :=
  B.norm_discrete_S_le h t ht

/-- The earlier `BanachFEEC.norm_discrete_S_le_exp`. -/
theorem norm_discrete_S_le_exp_old (h : κ) (t : ℝ) (ht : 0 ≤ t) :
    ‖(B.discrete h).S t‖ ≤ B.M * Real.exp (0 * t) :=
  B.norm_discrete_S_le_exp h t ht

/-- The earlier `BanachFEEC.res_apply_sub`. -/
theorem res_apply_sub_old {τ : ℝ} (hτ : 0 < τ) (h : κ) :
    ∀ x y, (x, y) ∈ (B.discrete h).generator.graph → B.res τ h (x - (τ : 𝕜) • y) = x :=
  B.res_apply_sub hτ h

/-- The earlier `BanachFEEC.step_theta_one`. -/
theorem step_theta_one_old (τ : ℝ) (h : κ) :
    B.step (RationalScheme.theta 1 one_pos) τ h = B.res τ h :=
  B.step_theta_one τ h

/-- The earlier `BanachFEEC.rationalScheme`, a time scheme of `B`. -/
def rationalScheme_old (r : RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p)
    (hp0 : 0 < p) (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) (Ms : ℝ → ℝ)
    (hMs : ∀ (T : ℝ) (h : κ) (n : ℕ), (n : ℝ) * τ h ≤ T → ‖B.step r (τ h) h ^ n‖ ≤ Ms T) :
    B.TimeScheme :=
  B.rationalScheme r hr hp hp0 τ hτ Ms hMs

/-- The earlier `BanachFEEC.backwardEuler`, a time scheme of `B`. -/
def backwardEuler_old (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) : B.TimeScheme := B.backwardEuler τ hτ

end FeecCheck.StableFamilies
