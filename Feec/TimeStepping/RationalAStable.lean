module

public import Feec.TimeStepping.RationalHillePhillips
public import Feec.ForMathlib.Analysis.HalfLinePowers

/-!
# The `√n` stability bound for every A-stable rational scheme

For every A-stable rational scheme `r` and every bounded semigroup `‖S(t)‖ ≤ M` on a complex Banach
space, `‖r(τA)ⁿ‖ ≤ M (1 + C_r √n)`, through the decay of the Hille–Phillips measure of `r`.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Polynomial MeasureTheory Unitization Metric

@[expose] public noncomputable section

namespace Feec

namespace TimeStepping

namespace RationalScheme

variable (r : RationalScheme)

/-- `P(s) = sᴺ n(1 - 1/s)` as a complex polynomial, `N = deg d`. -/
def numPoly : ℂ[X] := resolventEval r.den.natDegree (r.num.map (algebraMap ℝ ℂ)) X

theorem resolventEval_num_X :
    resolventEval r.den.natDegree (r.num.map (algebraMap ℝ ℂ)) (X : ℂ[X]) = r.numPoly := rfl

theorem resolventEval_den_X :
    resolventEval r.den.natDegree (r.den.map (algebraMap ℝ ℂ)) (X : ℂ[X]) = r.denPoly := rfl

theorem fourier_hpMeasure_eq_div (ξ : ℝ) :
    HalfLineAlgebra.fourier ξ r.hpMeasure =
      r.numPoly.eval (HalfLineAlgebra.fourier ξ HalfLineAlgebra.resolvent) /
        r.denPoly.eval (HalfLineAlgebra.fourier ξ HalfLineAlgebra.resolvent) := by
  rw [map_hpMeasure, resolventEval_eq_eval _ (r.num.map _), resolventEval_eq_eval _ (r.den.map _),
    resolventEval_num_X, resolventEval_den_X, coe_aeval_eq_eval,
    Ring.inverse_eq_inv', div_eq_mul_inv]

theorem fst_hpMeasure_eq_div : r.hpMeasure.fst = r.numPoly.eval 0 / r.denPoly.eval 0 := by
  have h := r.map_hpMeasure (fstHom ℂ HalfLineKernel)
  rw [show fstHom ℂ HalfLineKernel HalfLineAlgebra.resolvent = 0 from rfl,
    resolventEval_eq_eval _ (r.num.map _), resolventEval_eq_eval _ (r.den.map _),
    resolventEval_num_X, resolventEval_den_X, coe_aeval_eq_eval,
    Ring.inverse_eq_inv', ← div_eq_mul_inv] at h
  exact h

theorem eval_denPoly_ne_zero {s : ℂ} (hs : ‖s - 1 / 2‖ ≤ 1 / 2) : r.denPoly.eval s ≠ 0 := by
  rcases eq_or_ne s 0 with rfl | hs0
  · exact r.eval_denPoly_zero_ne_zero
  rw [denPoly, eval_resolventEval_X (natDegree_map_le) hs0, eval_map_algebraMap]
  refine mul_ne_zero (pow_ne_zero _ hs0) (r.aeval_den_ne_zero _ ?_)
  have hn : 0 < Complex.normSq s := Complex.normSq_pos.2 hs0
  have h2 : (s.re - 1 / 2) ^ 2 + s.im ^ 2 ≤ (1 / 2) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hs 2
    rw [Complex.sq_norm, Complex.normSq_apply] at this
    simp at this
    nlinarith [this]
  rw [Complex.sub_re, Complex.one_re, Complex.inv_re, sub_nonpos, le_div_iff₀ hn, one_mul,
    Complex.normSq_apply]
  nlinarith [h2]

theorem exists_decay : ∃ C₁ C₂ : ℝ, ∀ ξ,
    ‖HalfLineAlgebra.fourier ξ r.hpMeasure - r.hpMeasure.fst‖ ≤
        C₁ * ‖HalfLineAlgebra.fourier ξ HalfLineAlgebra.resolvent‖ ∧
      ‖HalfLineAlgebra.moment r.hpMeasure ξ‖ ≤
        C₂ * ‖HalfLineAlgebra.fourier ξ HalfLineAlgebra.resolvent‖ ^ 2 := by
  set P := r.numPoly
  set Q := r.denPoly
  set K : Set ℂ := closedBall (1 / 2) (1 / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hQ : ∀ s ∈ K, Q.eval s ≠ 0 := fun s hs =>
    r.eval_denPoly_ne_zero (mem_closedBall_iff_norm.1 hs)
  have hq0 : Q.eval 0 ≠ 0 := r.eval_denPoly_zero_ne_zero
  obtain ⟨T, hT⟩ : X ∣ P * C (Q.eval 0) - C (P.eval 0) * Q := by
    rw [X_dvd_iff, coeff_sub, coeff_mul_C, coeff_C_mul, coeff_zero_eq_eval_zero,
      coeff_zero_eq_eval_zero]
    ring
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn
    (f := fun s => T.eval s / (Q.eval s * Q.eval 0))
    ((T.continuous.continuousOn).div (Q.continuous.continuousOn.mul continuousOn_const)
      fun s hs => mul_ne_zero (hQ s hs) hq0)
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn
    (f := fun s => (P.derivative.eval s * Q.eval s - P.eval s * Q.derivative.eval s) / Q.eval s ^ 2)
    (((P.derivative.continuous.continuousOn.mul Q.continuous.continuousOn).sub
      (P.continuous.continuousOn.mul Q.derivative.continuous.continuousOn)).div
      (Q.continuous.continuousOn.pow 2) fun s hs => pow_ne_zero _ (hQ s hs))
  refine ⟨C₁, C₂, fun ξ => ⟨?_, ?_⟩⟩
  · have hs := mem_closedBall_iff_norm.2 (HalfLineAlgebra.norm_fourier_resolvent_sub_half ξ)
    rw [fourier_hpMeasure_eq_div, fst_hpMeasure_eq_div]
    generalize HalfLineAlgebra.fourier ξ HalfLineAlgebra.resolvent = s at hs ⊢
    have hTs := congrArg (Polynomial.eval s) hT
    simp only [eval_sub, eval_mul, eval_C, eval_X] at hTs
    have hQs := hQ s hs
    have e : P.eval s / Q.eval s - P.eval 0 / Q.eval 0 =
        s * (T.eval s / (Q.eval s * Q.eval 0)) := by
      field_simp
      linear_combination hTs
    rw [e, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC₁ s hs) (norm_nonneg _)
  · have hs := mem_closedBall_iff_norm.2 (HalfLineAlgebra.norm_fourier_resolvent_sub_half ξ)
    have hR := ((P.hasDerivAt _).div (Q.hasDerivAt _) (hQ _ hs)).comp ξ
      (HalfLineAlgebra.hasDerivAt_fourier_resolvent ξ)
    have hfun : (fun ξ => HalfLineAlgebra.fourier ξ r.hpMeasure) =
        (fun s => P.eval s / Q.eval s) ∘
          fun ξ => HalfLineAlgebra.fourier ξ HalfLineAlgebra.resolvent :=
      funext r.fourier_hpMeasure_eq_div
    have huniq := ((HalfLineAlgebra.hasDerivAt_fourier r.hpMeasure ξ).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq hfun.symm)).unique hR
    have hc : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
    generalize HalfLineAlgebra.fourier ξ HalfLineAlgebra.resolvent = s at hs huniq ⊢
    have e : HalfLineAlgebra.moment r.hpMeasure ξ =
        (P.derivative.eval s * Q.eval s - P.eval s * Q.derivative.eval s) / Q.eval s ^ 2 * s ^ 2 :=
      mul_left_cancel₀ hc (by rw [huniq]; ring)
    rw [e, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hC₂ _ hs) (by positivity)

/-- The constant `C_r` of the `√n` bound for an A-stable scheme. -/
def sqrtConst : ℝ :=
  HalfLineAlgebra.powerConst (Classical.choose r.exists_decay)
    (Classical.choose (Classical.choose_spec r.exists_decay))

theorem sqrtConst_nonneg : 0 ≤ r.sqrtConst := HalfLineAlgebra.powerConst_nonneg _ _

/-- **The total variation of `μ_rⁿ` is at most `1 + C_r √n` for every A-stable `r`.**
[BrennerThomee1979] -/
theorem variation_hpMeasure_pow_le_sqrtConst {r : RationalScheme} (hr : r.IsAStable) (n : ℕ) :
    (r.hpMeasure ^ n).variation ≤ 1 + r.sqrtConst * √n :=
  have h := Classical.choose_spec (Classical.choose_spec r.exists_decay)
  HalfLineAlgebra.variation_pow_le _ (norm_fourier_hpMeasure_le hr) (fun ξ => (h ξ).1)
    (fun ξ => (h ξ).2) n

/-! ### Bounded semigroups on Banach spaces -/

section Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (G : C0Semigroup ℂ E) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M)

/-- **Brenner–Thomée's stability bound for every A-stable rational scheme**: for a bounded semigroup
`‖S(t)‖ ≤ M` on a complex Banach space, `‖r(τA)ⁿ‖ ≤ M (1 + C_r √n)`. [BrennerThomee1979] -/
theorem norm_resolventStep_pow_le_of_isAStable {r : RationalScheme} (hr : r.IsAStable) {τ : ℝ}
    (hτ : 0 ≤ τ) (n : ℕ) :
    ‖r.resolventStep (G.laplaceResolvent hM τ hτ) ^ n‖ ≤ M * (1 + r.sqrtConst * √n) := by
  rw [← r.hillePhillips_hpMeasure G hM hτ, ← map_pow]
  exact ((G.dilate τ hτ).norm_hillePhillips_le _ _).trans (mul_le_mul_of_nonneg_left
    (variation_hpMeasure_pow_le_sqrtConst hr n) ((norm_nonneg _).trans (hM 0 le_rfl)))

end Semigroup

end RationalScheme

end TimeStepping

end Feec
