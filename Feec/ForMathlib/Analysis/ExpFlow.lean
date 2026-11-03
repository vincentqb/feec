module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Derivatives along the flow of a bounded operator

For a bounded operator `L` on a Banach space over `𝕜` (`ℝ` or `ℂ`, with the real structure),

* `ContinuousLinearMap.hasDerivAt_exp_ofReal_smul_apply`: `(d/dt) e^{tL} x = L e^{tL} x`;
* `ContinuousLinearMap.hasDerivAt_exp_sub_smul_apply` (**the product rule along the flow**): for a
  curve `U` with derivative `U'` at `s`, `r ↦ e^{(t - r)L} U(r)` has derivative
  `e^{(t - s)L} (U' - L U(s))` at `s`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open NormedSpace Filter Topology

@[expose] public noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

/-- An `𝕜`-derivative along the real axis is an `ℝ`-derivative. -/
theorem HasDerivAt.comp_ofReal_rclike {f : 𝕜 → X} {f' : X} {t : ℝ}
    (h : HasDerivAt f f' (t : 𝕜)) : HasDerivAt (fun s : ℝ => f s) f' t := by
  have h1 := (h.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (RCLike.ofRealCLM (K := 𝕜)).hasDerivAt
  simpa [Function.comp_def] using h1

namespace ContinuousLinearMap

variable [CompleteSpace X]

/-- `ℚ`-algebra structure on operators, for `NormedSpace.exp`. -/
local instance instNormedAlgebraRatExpFlow : NormedAlgebra ℚ (X →L[𝕜] X) :=
  NormedAlgebra.restrictScalars ℚ 𝕜 _

/-- `(d/dt) e^{tL} x = L e^{tL} x`. -/
theorem hasDerivAt_exp_ofReal_smul_apply (L : X →L[𝕜] X) (x : X) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp ((s : 𝕜) • L) x) (L (exp ((t : 𝕜) • L) x)) t := by
  have h := HasDerivAt.clm_apply (hasDerivAt_exp_smul_const' (𝕂 := 𝕜) L (t : 𝕜))
    (hasDerivAt_const (t : 𝕜) x)
  simp only [_root_.map_zero, add_zero, mul_apply_eq_comp] at h
  exact h.comp_ofReal_rclike

/-- **The product rule along the flow**: for a bounded `L` and a curve `U` with derivative `U'`
at `s`, `r ↦ e^{(t - r)L} U(r)` has derivative `e^{(t - s)L} (U' - L U(s))` at `s`. -/
theorem hasDerivAt_exp_sub_smul_apply (L : X →L[𝕜] X) (t : ℝ) {U : ℝ → X} {U' : X} {s : ℝ}
    (hU : HasDerivAt U U' s) :
    HasDerivAt (fun r => exp (((t - r : ℝ) : 𝕜) • L) (U r))
      (exp (((t - s : ℝ) : 𝕜) • L) (U' - L (U s))) s := by
  set E : ℝ → X →L[𝕜] X := fun r => exp (((t - r : ℝ) : 𝕜) • L)
  have hE : Continuous E := exp_continuous.comp (by fun_prop)
  -- the part along the curve
  have h1 : HasDerivAt (fun r => E r (U r - U s)) (E s U') s := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hp : Tendsto (fun r => (E r, slope U s r)) (𝓝[≠] s) (𝓝 (E s, U')) :=
      ((hE.tendsto s).mono_left nhdsWithin_le_nhds).prodMk_nhds (hasDerivAt_iff_tendsto_slope.1 hU)
    refine ((isBoundedBilinearMap_apply.continuous.tendsto (E s, U')).comp hp).congr fun r => ?_
    simp only [Function.comp_apply, slope_def_module, sub_self, _root_.map_zero, sub_zero,
      ContinuousLinearMap.map_smul_of_tower]
  -- the part along the flow
  have h2 : HasDerivAt (fun r => E r (U s)) (-(E s (L (U s)))) s := by
    have hh : HasDerivAt (fun r : ℝ => t - r) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have h := (hasDerivAt_exp_ofReal_smul_apply L (U s) (t - s)).scomp s hh
    have hc : L (E s (U s)) = E s (L (U s)) :=
      congrArg (fun T : X →L[𝕜] X => T (U s))
        (((Commute.refl L).smul_right ((t - s : ℝ) : 𝕜)).exp_right).eq
    exact h.congr_deriv (by rw [hc, neg_one_smul])
  refine ((h1.add h2).congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)).congr_deriv ?_
  · simp only [Pi.add_apply]
    rw [← _root_.map_add, sub_add_cancel]
  · rw [_root_.map_sub, sub_eq_add_neg]

end ContinuousLinearMap
