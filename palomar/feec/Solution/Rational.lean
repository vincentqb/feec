module

public import Solution.Defs
public import Feec.TimeStepping.Rational
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The rational schemes of the challenge are those of `Feec`

The challenge states A-stability of `r = P/Q` on the closed left half-plane and the order through
`r(z) - e^z = O(z^{p+1})` (`FEEC.IsAStable`, `FEEC.HasOrder`, the text shared with
`palomar/timestepping`). An A-stable `P/Q` is a `Feec.TimeStepping.RationalScheme`
(`FEEC.IsAStable.scheme`, through `Feec.TimeStepping.RationalScheme.ofBounded`: `deg P ≤ deg Q`
follows from the bound on the imaginary axis), A-stable in the sense of `Feec` (the imaginary
axis), of the same order (`Feec.TimeStepping.RationalScheme.hasOrder_of_isBigO`), with the same
operators `r(L)` (`FEEC.IsAStable.rationalApply_eq`).

The challenge's notions are those of its earlier text, a structure `n/d` with `deg n ≤ deg d` and
no pole in `re z ≤ 0`, A-stable on the imaginary axis, of order `p` when `X^{p+1}` divides
`n - d Tₚ`: `FEEC.isAStable_iff` (the converse through the maximum modulus principle on the disc,
`Complex.norm_le_of_forall_mem_frontier_norm_le`, and the Cayley transform `w ↦ (w - 1)/(w + 1)`
of the disc onto the left half-plane, `Feec.TimeStepping.RationalScheme.eval_cayley`) and
`FEEC.hasOrder_iff`.

## References

* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Polynomial Asymptotics Filter Topology

@[expose] public noncomputable section

namespace FEEC

variable {P Q : ℝ[X]}

theorem IsAStable.aeval_ne_zero (hr : IsAStable P Q) : ∀ z : ℂ, z.re ≤ 0 → aeval z Q ≠ 0 :=
  fun z hz => (hr z hz).1

theorem IsAStable.norm_le (hr : IsAStable P Q) (y : ℝ) :
    ‖aeval (y * Complex.I) P / aeval (y * Complex.I) Q‖ ≤ 1 :=
  (hr _ (by simp)).2

/-- An A-stable `P/Q` as a rational scheme of `Feec`. -/
def IsAStable.scheme (hr : IsAStable P Q) : Feec.TimeStepping.RationalScheme :=
  Feec.TimeStepping.RationalScheme.ofBounded P Q hr.aeval_ne_zero hr.norm_le

theorem IsAStable.scheme_isAStable (hr : IsAStable P Q) : hr.scheme.IsAStable := hr.norm_le

theorem IsAStable.scheme_hasOrder (hr : IsAStable P Q) {p : ℕ} (hp : HasOrder P Q p) :
    hr.scheme.HasOrder p :=
  hr.scheme.hasOrder_of_isBigO hp

/-- `r(L)` of the challenge is `Feec`'s `r.apply L`. -/
theorem IsAStable.rationalApply_eq {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] (hr : IsAStable P Q) (L : V →L[𝕜] V) :
    rationalApply P Q L = hr.scheme.apply L := rfl

/-- **A-stability on the imaginary axis is A-stability** for a scheme of `Feec` (no pole in
`re z ≤ 0`, `deg n ≤ deg d`): the maximum modulus principle for `ñ/d̃` on the closed unit disc,
`r(z) = ñ(w)/d̃(w)` for `w = (1 + z)/(1 - z)`. -/
theorem isAStable_of_scheme (r : Feec.TimeStepping.RationalScheme) (hr : r.IsAStable) :
    IsAStable r.num r.den := by
  have hdiff : ∀ w : ℂ, ‖w‖ ≤ 1 →
      DifferentiableAt ℂ (fun w => aeval w r.cnum / aeval w r.cden) w := fun w hw =>
    (Polynomial.differentiable_aeval _ w).div (Polynomial.differentiable_aeval _ w)
      (r.aeval_cden_ne_zero hw)
  have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ≠ -1 → ‖aeval ζ r.cnum / aeval ζ r.cden‖ ≤ 1 :=
    fun ζ hζ hζ1 => by rw [r.eval_cayley hζ hζ1]; exact hr _
  have hre : ∀ y : ℝ, ∀ c : ℂ, c.re ≠ 0 → c + y * Complex.I ≠ 0 := fun y c hc h => hc (by
    simpa using congrArg Complex.re h)
  have hne : ∀ y : ℝ, (1 : ℂ) - y * Complex.I ≠ 0 := fun y h =>
    hre (-y) 1 one_ne_zero (by rw [← h]; push_cast; ring)
  -- `-1` is the limit of the points `(1 + y i)/(1 - y i)`, `y → ∞`, of the unit circle
  have hm1 : ‖aeval (-1 : ℂ) r.cnum / aeval (-1) r.cden‖ ≤ 1 := by
    have h0 : Tendsto (fun y : ℝ => 2 / (1 - y * Complex.I)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hn : Tendsto (fun y : ℝ => ‖(1 : ℂ) - y * Complex.I‖) atTop atTop :=
        tendsto_atTop_mono (fun y => (le_abs_self y).trans (by
          simpa using Complex.abs_im_le_norm ((1 : ℂ) - y * Complex.I))) tendsto_id
      simpa [norm_div] using (tendsto_const_nhds (x := ‖(2 : ℂ)‖)).div_atTop hn
    have hlim : Tendsto (fun y : ℝ => (1 + y * Complex.I) / (1 - y * Complex.I)) atTop
        (𝓝 (-1)) := by
      have := (tendsto_const_nhds (x := (-1 : ℂ))).add h0
      rw [add_zero] at this
      refine this.congr fun y => ?_
      field_simp [hne y]
      ring
    have hb : ∀ y : ℝ, ‖aeval ((1 + y * Complex.I) / (1 - y * Complex.I)) r.cnum /
        aeval ((1 + y * Complex.I) / (1 - y * Complex.I)) r.cden‖ ≤ 1 := fun y => by
      refine hcirc _ ?_ fun h => ?_
      · have hc : (1 : ℂ) - y * Complex.I = (starRingEnd ℂ) (1 + y * Complex.I) := by
          rw [map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
        rw [norm_div, hc, RCLike.norm_conj]
        exact div_self (norm_ne_zero_iff.2 (hre y 1 one_ne_zero))
      · rw [div_eq_iff (hne y)] at h
        have := congrArg Complex.re h
        simp at this
        norm_num at this
    exact le_of_tendsto ((hdiff _ (by simp)).continuousAt.norm.tendsto.comp hlim)
      (Eventually.of_forall hb)
  intro z hz
  refine ⟨r.aeval_den_ne_zero z hz, ?_⟩
  have h1z : (1 : ℂ) - z ≠ 0 := fun h => by
    have := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hw1 : (1 + z) / (1 - z) + 1 ≠ 0 := by
    rw [div_add_one h1z, show 1 + z + (1 - z) = (2 : ℂ) by ring]
    exact div_ne_zero two_ne_zero h1z
  have hwz : ((1 + z) / (1 - z) - 1) / ((1 + z) / (1 - z) + 1) = z := by
    rw [div_sub_one h1z, div_add_one h1z, div_div_div_cancel_right₀ h1z,
      show 1 + z - (1 - z) = 2 * z by ring, show 1 + z + (1 - z) = (2 : ℂ) by ring,
      mul_div_cancel_left₀ z two_ne_zero]
  have hwm : (1 + z) / (1 - z) ≠ -1 := fun h => hw1 (by rw [h]; ring)
  have hwn : ‖(1 + z) / (1 - z)‖ ≤ 1 := by
    have e := Feec.TimeStepping.re_cayley_inv ((1 + z) / (1 - z))
    rw [hwz] at e
    have hpos : 0 < ‖(1 + z) / (1 - z) + 1‖ ^ 2 := pow_pos (norm_pos_iff.2 hw1) 2
    rw [e] at hz
    have := (div_le_iff₀ hpos).1 hz
    nlinarith [norm_nonneg ((1 + z) / (1 - z))]
  have hval : aeval z r.num / aeval z r.den =
      aeval ((1 + z) / (1 - z)) r.cnum / aeval ((1 + z) / (1 - z)) r.cden := by
    rw [Feec.TimeStepping.RationalScheme.cnum, Feec.TimeStepping.RationalScheme.cden,
      Feec.TimeStepping.aeval_cayleyPoly_complex r.natDegree_num_le hwm,
      Feec.TimeStepping.aeval_cayleyPoly_complex le_rfl hwm, hwz,
      mul_div_mul_left _ _ (pow_ne_zero _ hw1)]
  rw [hval]
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ) 1)
    (f := fun w => aeval w r.cnum / aeval w r.cden) Metric.isBounded_ball
    (DifferentiableOn.diffContOnCl fun v hv => (hdiff v ?_).differentiableWithinAt) (C := 1)
    (fun ζ hζ => ?_) ?_
  · rw [closure_ball (0 : ℂ) one_ne_zero, Metric.mem_closedBall, dist_zero_right] at hv
    exact hv
  · rw [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere_zero_iff_norm] at hζ
    by_cases h : ζ = -1
    · rw [h]; exact hm1
    · exact hcirc ζ hζ h
  · rw [closure_ball (0 : ℂ) one_ne_zero, Metric.mem_closedBall, dist_zero_right]; exact hwn

/-- **A-stability is that of the earlier challenge**: `P/Q` is A-stable on the closed left
half-plane iff `deg P ≤ deg Q`, `Q` has no zero for `re z ≤ 0` and `|P(iy)/Q(iy)| ≤ 1`. -/
theorem isAStable_iff : IsAStable P Q ↔ P.natDegree ≤ Q.natDegree ∧
    (∀ z : ℂ, z.re ≤ 0 → aeval z Q ≠ 0) ∧
      ∀ y : ℝ, ‖aeval (y * Complex.I) P / aeval (y * Complex.I) Q‖ ≤ 1 :=
  ⟨fun hr => ⟨hr.scheme.natDegree_num_le, hr.aeval_ne_zero, hr.norm_le⟩,
    fun h => isAStable_of_scheme ⟨P, Q, h.1, h.2.1⟩ h.2.2⟩

/-- **The order from the divisibility** `X^{m+1} ∣ P - Q Tₘ` (`Tₘ` the Taylor polynomial of the
exponential), for `Q(0) ≠ 0`. -/
theorem hasOrder_of_dvd (hq : aeval (0 : ℂ) Q ≠ 0) {m : ℕ}
    (h : X ^ (m + 1) ∣ P - Q * Feec.TimeStepping.expTaylor m) : HasOrder P Q m := by
  obtain ⟨g, hg⟩ := h
  have hd0 : ∀ᶠ z : ℂ in 𝓝 0, aeval z Q ≠ 0 :=
    ((Polynomial.continuous_aeval Q).tendsto 0).eventually_ne hq
  have hexp : (fun z : ℂ => aeval z (Feec.TimeStepping.expTaylor m) - Complex.exp z) =O[𝓝 0]
      fun z => z ^ (m + 1) := by
    refine IsBigO.of_bound ((m + 1).succ * ((m + 1).factorial * (m + 1 : ℕ) : ℝ)⁻¹) ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) one_pos] with z hz
    rw [mem_closedBall_zero_iff] at hz
    have e : aeval z (Feec.TimeStepping.expTaylor m) =
        ∑ j ∈ Finset.range (m + 1), z ^ j / j.factorial := by
      simp [Feec.TimeStepping.expTaylor, div_eq_inv_mul]
    rw [e, norm_sub_rev, norm_pow]
    exact (Complex.exp_bound hz (Nat.succ_pos m)).trans_eq (mul_comm _ _)
  have hg' : (fun z : ℂ => aeval z g / aeval z Q) =O[𝓝 0] fun _ => (1 : ℂ) :=
    (((Polynomial.continuous_aeval g).tendsto 0).div
      ((Polynomial.continuous_aeval Q).tendsto 0) hq).isBigO_one ℂ
  have hmul := (isBigO_refl (fun z : ℂ => z ^ (m + 1)) (𝓝 0)).mul hg'
  simp only [mul_one] at hmul
  refine (hmul.add hexp).congr' ?_ EventuallyEq.rfl
  filter_upwards [hd0] with z hz
  have e := congrArg (aeval z) hg
  simp only [map_sub, map_mul, map_pow, aeval_X] at e
  have hp : aeval z P = aeval z Q * aeval z (Feec.TimeStepping.expTaylor m) +
      z ^ (m + 1) * aeval z g := by
    linear_combination e
  rw [hp, add_div, mul_div_cancel_left₀ _ hz]
  ring

/-- **The order is that of the earlier challenge**: for A-stable `P/Q`, `r(z) - e^z = O(z^{p+1})`
iff `X^{p+1}` divides `P - Q Tₚ`. -/
theorem hasOrder_iff (hr : IsAStable P Q) {p : ℕ} :
    HasOrder P Q p ↔ X ^ (p + 1) ∣ P - Q * Feec.TimeStepping.expTaylor p :=
  ⟨hr.scheme_hasOrder, hasOrder_of_dvd (hr.aeval_ne_zero 0 (by simp))⟩

end FEEC
