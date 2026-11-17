module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Quasi-optimality of a bounded projection

`ContinuousLinearMap.norm_sub_apply_le_of_apply_eq`: if `P` fixes `u` and `‖P‖ ≤ C`, then
`‖y - P y‖ ≤ (1 + C) ‖y - u‖` for every `y`. For a projection `P` onto a subspace `V` this bounds
the error of `P` by `1 + ‖P‖` times the best approximation from `V`, which turns a Jackson
estimate for the best approximation into one for a uniformly bounded family of projections
([AFW2010], §3.3).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public section

/-- **A bounded projection is quasi-optimal**: if `P u = u` and `‖P‖ ≤ C`, then
`‖y - P y‖ ≤ (1 + C) ‖y - u‖`, as `y - P y = (y - u) - P (y - u)`. -/
theorem ContinuousLinearMap.norm_sub_apply_le_of_apply_eq {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (P : E →L[𝕜] E)
    {C : ℝ} (hC : ‖P‖ ≤ C) {u : E} (hu : P u = u) (y : E) :
    ‖y - P y‖ ≤ (1 + C) * ‖y - u‖ := by
  have e : y - P y = (y - u) - P (y - u) := by rw [map_sub, hu]; abel
  rw [e]
  calc ‖(y - u) - P (y - u)‖ ≤ ‖y - u‖ + ‖P (y - u)‖ := norm_sub_le _ _
    _ ≤ ‖y - u‖ + C * ‖y - u‖ := by gcongr; exact P.le_of_opNorm_le hC _
    _ = (1 + C) * ‖y - u‖ := by ring
