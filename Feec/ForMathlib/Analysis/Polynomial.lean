module

public import Mathlib.Analysis.Polynomial.Basic

/-!
# Rational functions bounded towards infinity

**`Polynomial.natDegree_le_of_norm_div_le`**: over a normed field, if `‖P(z)/Q(z)‖ ≤ C` along a
filter converging to infinity (for instance along the imaginary axis of `ℂ`), then
`deg P ≤ deg Q`: the rational function `P/Q` is bounded at infinity. It is the contrapositive of
`Polynomial.isLittleO_cobounded_of_degree_lt`. It shows that a stability function bounded on the
imaginary axis has `deg P ≤ deg Q` ([HairerWanner1996], §IV.3).

## References

* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Filter Bornology Asymptotics

@[expose] public section

namespace Polynomial

variable {𝕜 : Type*} [NormedField 𝕜] {P Q : 𝕜[X]}

/-- **A rational function bounded towards infinity is bounded at infinity**: if, eventually along
a nontrivial filter `l` converging to infinity, `Q(z) ≠ 0` and `‖P(z)/Q(z)‖ ≤ C`, then
`deg P ≤ deg Q`. -/
theorem natDegree_le_of_norm_div_le {l : Filter 𝕜} [l.NeBot] (hl : l ≤ cobounded 𝕜) {C : ℝ}
    (hQ : ∀ᶠ z in l, Q.eval z ≠ 0) (hC : ∀ᶠ z in l, ‖P.eval z / Q.eval z‖ ≤ C) :
    P.natDegree ≤ Q.natDegree := by
  by_contra h
  have hP : P ≠ 0 := by rintro rfl; simp at h
  have ho := (isLittleO_cobounded_of_degree_lt (degree_lt_degree (not_le.1 h))).mono hl
  have hc : (0 : ℝ) < (|C| + 1)⁻¹ := by positivity
  obtain ⟨z, hz, hQz, hCz⟩ := ((ho.bound hc).and (hQ.and hC)).exists
  have hq : 0 < ‖Q.eval z‖ := norm_pos_iff.2 hQz
  rw [norm_div, div_le_iff₀ hq] at hCz
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)] at hz
  nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C) hq.le]

end Polynomial
