module

public import Feec.TimeStepping.RungeKutta
public import Feec.TimeStepping.Convergence

/-!
# Regression test: implicit Euler and the dissipative time averages

`Feec.TimeStepping` stated a few specializations that are now derived on demand:

* implicit Euler as the θ-scheme `θ = 1`: `thetaStep_one` (`r_1(τ A) = τ⁻¹ R(τ⁻¹)`) and its
  global error `norm_implicitEuler_pow_sub_exp_le` (the case `θ = 1` of
  `Feec.TimeStepping.norm_thetaStep_pow_sub_exp_le`);
* implicit Euler as the one-stage Radau IIA method: the Butcher tableau
  `ButcherTableau.implicitEuler`, its rational scheme `RationalScheme.implicitEuler`, equal to
  `RationalScheme.theta 1`, A-stable and of order `1` (`isAStable_theta`, `hasOrder_theta`);
* the time averages of a bounded dissipative generator: `norm_timeAvg_le`,
  `norm_pow_timeAvg_iterate_le` (smoothing, `(2/δ)ᵏ`) and `norm_timeAvg_iterate_sub_le`, the case
  `M = 1` of the `_of_norm_exp_le` versions.

Below, each is stated verbatim and derived from the current API.

This file is part of the `FeecCheck` library, not of `Feec`.

## References

* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.5
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Polynomial Matrix NormedSpace

@[expose] public noncomputable section

namespace FeecCheck.ThetaSchemes

open Feec Feec.TimeStepping

section Unbounded

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The earlier `Feec.TimeStepping.thetaStep_one`: implicit Euler is the θ-scheme with `θ = 1`,
`r_1(τ A) = (1 - τ A)⁻¹ = τ⁻¹ R(τ⁻¹)`. -/
theorem thetaStep_one_old (A : E →ₗ.[𝕜] E) (τ : ℝ) :
    thetaStep A 1 τ = ((τ : 𝕜))⁻¹ • Operator.resolvent A ((τ : 𝕜))⁻¹ := by
  simp [thetaStep]

end Unbounded

section Bounded

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [CompleteSpace X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] {L : X →L[𝕜] X}

/-- The earlier `Feec.TimeStepping.norm_implicitEuler_pow_sub_exp_le`: at `t = n τ`,
`‖(1 - τ L)⁻ⁿ y - e^{tL} y‖ ≤ 3/2 t τ ‖L² y‖` for every bounded dissipative `L`
([Thomee2006], Ch. 7). -/
theorem norm_implicitEuler_pow_sub_exp_le_old (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {τ : ℝ}
    (hτ : 0 < τ) (n : ℕ) (y : X) :
    ‖(thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) 1 τ ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤
      3 / 2 * (n * τ) * τ * ‖(L ^ 2) y‖ := by
  have := norm_thetaStep_pow_sub_exp_le (𝕜 := 𝕜) hL (θ := 1) (by norm_num) hτ n y
  norm_num at this ⊢
  exact this

/-- The earlier `Feec.TimeStepping.norm_timeAvg_le`: `‖A_δ y‖ ≤ ‖y‖` for dissipative `L`. -/
theorem norm_timeAvg_le_old (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {δ : ℝ} (hδ : 0 < δ) (y : X) :
    ‖timeAvg L δ y‖ ≤ ‖y‖ := by
  simpa using norm_timeAvg_le_of_norm_exp_le (fun s hs => norm_exp_le_one hL hs.1) hδ y

/-- The earlier `Feec.TimeStepping.norm_pow_timeAvg_iterate_le` (smoothing):
`‖Lᵏ A_δᵏ y‖ ≤ (2/δ)ᵏ ‖y‖`, uniformly in the bounded dissipative `L`. -/
theorem norm_pow_timeAvg_iterate_le_old (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {δ : ℝ}
    (hδ : 0 < δ) (k : ℕ) (y : X) : ‖(L ^ k) ((timeAvg L δ)^[k] y)‖ ≤ (2 / δ) ^ k * ‖y‖ := by
  simpa [one_add_one_eq_two] using
    norm_pow_timeAvg_iterate_le_of_norm_exp_le (norm_exp_le_one hL hδ.le) hδ k y

/-- The earlier `Feec.TimeStepping.norm_timeAvg_iterate_sub_le`:
`‖A_δᵏ y - y‖ ≤ k ‖A_δ y - y‖`. -/
theorem norm_timeAvg_iterate_sub_le_old (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {δ : ℝ}
    (hδ : 0 < δ) (k : ℕ) (y : X) : ‖(timeAvg L δ)^[k] y - y‖ ≤ k * ‖timeAvg L δ y - y‖ := by
  simpa using
    norm_timeAvg_iterate_sub_le_of_norm_exp_le (fun s hs => norm_exp_le_one hL hs.1) hδ k y

end Bounded

/-! ### Implicit Euler as a Runge–Kutta method -/

/-- The earlier `ButcherTableau.implicitEuler`, the one-stage Radau IIA method
([HairerWanner1996], §IV.5). -/
def implicitEulerTableau_old : ButcherTableau 1 := ⟨!![1], ![1]⟩

/-- The earlier `ButcherTableau.implicitEuler_stability`. -/
theorem implicitEuler_stability_old :
    implicitEulerTableau_old.stabilityNum = (RationalScheme.theta 1 one_pos).num ∧
      implicitEulerTableau_old.stabilityDen = (RationalScheme.theta 1 one_pos).den :=
  ⟨Polynomial.funext fun x => by
    rw [ButcherTableau.eval_stabilityNum, det_fin_one]
    simp [implicitEulerTableau_old, RationalScheme.theta],
   Polynomial.funext fun x => by
    rw [ButcherTableau.eval_stabilityDen, det_fin_one]
    simp [implicitEulerTableau_old, RationalScheme.theta]⟩

/-- The earlier `RationalScheme.implicitEuler`, `r(z) = 1/(1 - z)`. -/
def implicitEuler_old : RationalScheme :=
  implicitEulerTableau_old.toRationalScheme
    (by rw [implicitEuler_stability_old.1, implicitEuler_stability_old.2]
        exact (RationalScheme.theta 1 one_pos).natDegree_num_le)
    (by rw [implicitEuler_stability_old.2]
        exact (RationalScheme.theta 1 one_pos).aeval_den_ne_zero)

/-- The earlier `RationalScheme.implicitEuler_eq_theta`. -/
theorem implicitEuler_eq_theta_old : implicitEuler_old = RationalScheme.theta 1 one_pos :=
  RationalScheme.ext implicitEuler_stability_old.1 implicitEuler_stability_old.2

/-- The earlier `RationalScheme.isAStable_implicitEuler`. -/
theorem isAStable_implicitEuler_old : implicitEuler_old.IsAStable := by
  rw [implicitEuler_eq_theta_old]; exact RationalScheme.isAStable_theta (by norm_num)

/-- The earlier `RationalScheme.hasOrder_implicitEuler`. -/
theorem hasOrder_implicitEuler_old : implicitEuler_old.HasOrder 1 := by
  rw [implicitEuler_eq_theta_old]; exact RationalScheme.hasOrder_theta one_pos

end FeecCheck.ThetaSchemes
