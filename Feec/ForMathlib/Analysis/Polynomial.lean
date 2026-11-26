module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Rational functions bounded towards infinity

Over a normed field, if `‖P(z)/Q(z)‖ ≤ C` along a filter converging to infinity, then
`deg P ≤ deg Q`, as for the stability functions of [HairerWanner1996], §IV.3; a polynomial that is
`O(zⁿ)` at `0` is divisible by `Xⁿ`.

## References

* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Filter Bornology Asymptotics Topology

@[expose] public section

namespace Polynomial

variable {𝕜 : Type*} [NormedField 𝕜] {P Q : 𝕜[X]}

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

theorem X_pow_dvd_of_isBigO {𝕂 : Type*} [NontriviallyNormedField 𝕂] {P : 𝕂[X]} {n : ℕ}
    (h : (fun z => P.eval z) =O[𝓝 0] fun z => z ^ n) : X ^ n ∣ P := by
  rcases eq_or_ne P 0 with rfl | hP
  · exact dvd_zero _
  obtain ⟨U, hPU, hU⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP 0
  simp only [map_zero, sub_zero] at hPU hU
  set m := rootMultiplicity 0 P
  rcases le_or_gt n m with hm | hm
  · exact (pow_dvd_pow X hm).trans ⟨U, hPU⟩
  have hU0 : U.eval 0 ≠ 0 := by rwa [X_dvd_iff, coeff_zero_eq_eval_zero] at hU
  obtain ⟨c, hc⟩ := h.bound
  have hb : (fun z => U.eval z) =O[𝓝[≠] 0] fun z => z ^ (n - m) := by
    refine IsBigO.of_bound c ?_
    filter_upwards [nhdsWithin_le_nhds hc, self_mem_nhdsWithin] with z hz hz0
    have hzm : 0 < ‖z‖ ^ m := pow_pos (norm_pos_iff.2 hz0) m
    rw [hPU, eval_mul, eval_pow, eval_X, norm_mul, norm_pow, norm_pow,
      ← Nat.add_sub_cancel' hm.le, pow_add, mul_left_comm] at hz
    rw [norm_pow]
    exact le_of_mul_le_mul_left hz hzm
  have h0 : Tendsto (fun z : 𝕂 => z ^ (n - m)) (𝓝[≠] 0) (𝓝 0) :=
    ((continuous_pow _).tendsto' 0 0 (zero_pow (by omega))).mono_left nhdsWithin_le_nhds
  exact absurd (tendsto_nhds_unique
    (((Polynomial.continuous U).tendsto 0).mono_left nhdsWithin_le_nhds) (hb.trans_tendsto h0)) hU0

end Polynomial
