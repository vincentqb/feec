module

public import Feec.TimeStepping.RationalHillePhillips
public import Feec.ForMathlib.Analysis.HalfLinePowers

/-!
# The `√n` stability bound for every A-stable rational scheme

`Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_le` gives Brenner–Thomée's bound
`‖r(τA)ⁿ‖ ≤ M (1 + C √n)` for strongly A-stable `r` (`|r(∞)| < 1`). Here it is extended to
**every A-stable rational scheme**, in particular to those with `|r(∞)| = 1`: Crank–Nicolson
and the Gauss methods, which are symmetric and never strongly A-stable
(`RationalScheme.IsSymmetric.not_isStronglyAStable`).

The Hille–Phillips measure `μ_r` (`RationalScheme.hpMeasure`) has `μ̂_r = R(ν̂)` with
`R = P/Q`, `P(s) = sᴺ n(1 - 1/s)`, `Q(s) = sᴺ d(1 - 1/s)` (`fourier_hpMeasure_eq_div`), and `Q`
has no zeros on the closed disc `|s - 1/2| ≤ 1/2`, the image of `re z ≤ 0` and `z = ∞`
(`eval_denPoly_ne_zero`). By compactness, `μ̂_r - r(∞) = O(ν̂)` and `μ̂_r' = O(ν̂²)`
(**`RationalScheme.exists_decay`**, for every rational scheme), the hypotheses of the power bound
`Feec.HalfLineAlgebra.variation_pow_le`, which holds whether or not `|r(∞)| < 1`. Hence, for a
bounded semigroup `‖S(t)‖ ≤ M` on a complex Banach space and A-stable `r`,
**`‖r(τA)ⁿ‖ ≤ M (1 + C_r √n)`** (`norm_resolventStep_pow_le_of_isAStable`,
`C_r = RationalScheme.sqrtConst`) [BrennerThomee1979]; this covers every symmetric scheme,
A-stable but not strongly A-stable.

The constant `C_r` is not explicit: it comes from the bounds of `R'` and `(R - R(0))/s` on the
disc; the strongly A-stable bound `RationalScheme.norm_resolventStep_pow_le` keeps the explicit
`RationalScheme.stabilityConst`. The bound on real Banach spaces
(`RationalScheme.norm_resolventStep_pow_le_of_resolvent_of_isAStable`) and the error bound with
its `√n` loss (`RationalScheme.norm_resolventStep_pow_sub_S_le_of_resolvent_of_isAStable`,
`RationalScheme.IsSymmetric.norm_resolventStep_pow_sub_S_le_of_resolvent`), over `ℝ` or `ℂ`, are
in `Feec.TimeStepping.RationalHillePhillipsReal`; that error bound is of order `p - 1/2` at fixed
`nτ`, weaker by `√n` than Brenner–Thomée's smooth-data estimate
`RationalScheme.norm_resolventStep_pow_sub_S_le_sharp` (`Feec.TimeStepping.RationalSharp`), which
needs no stability bound.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [E. Hille, R. S. Phillips, *Functional Analysis and Semi-Groups*][HillePhillips1957]

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

/-- `μ̂_r(ξ) = P(s)/Q(s)` at `s = ν̂(ξ)`. -/
theorem fourier_hpMeasure_eq_div (ξ : ℝ) :
    HalfLineAlgebra.fourier ξ r.hpMeasure =
      r.numPoly.eval (HalfLineAlgebra.fourier ξ HalfLineAlgebra.resolvent) /
        r.denPoly.eval (HalfLineAlgebra.fourier ξ HalfLineAlgebra.resolvent) := by
  rw [map_hpMeasure, resolventEval_eq_eval _ (r.num.map _), resolventEval_eq_eval _ (r.den.map _),
    resolventEval_num_X, resolventEval_den_X, coe_aeval_eq_eval,
    Ring.inverse_eq_inv', div_eq_mul_inv]

/-- The atom `r(∞) = P(0)/Q(0)`. -/
theorem fst_hpMeasure_eq_div : r.hpMeasure.fst = r.numPoly.eval 0 / r.denPoly.eval 0 := by
  have h := r.map_hpMeasure (fstHom ℂ HalfLineKernel)
  rw [show fstHom ℂ HalfLineKernel HalfLineAlgebra.resolvent = 0 from rfl,
    resolventEval_eq_eval _ (r.num.map _), resolventEval_eq_eval _ (r.den.map _),
    resolventEval_num_X, resolventEval_den_X, coe_aeval_eq_eval,
    Ring.inverse_eq_inv', ← div_eq_mul_inv] at h
  exact h

/-- **`Q` has no zeros in the closed disc `|s - 1/2| ≤ 1/2`**, the image of the closed left
half-plane `re z ≤ 0` and of `z = ∞` under `s = 1/(1 - z)`. -/
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

/-- **The decay of `μ_r` at high frequencies**: `|μ̂_r(ξ) - r(∞)| ≤ C₁ |ν̂(ξ)|` and
`|μ̂_r'(ξ)| ≤ 2π C₂ |ν̂(ξ)|²`, for every rational scheme: `μ̂_r = R(ν̂)` with `R = P/Q` analytic
on the closed disc `|s - 1/2| ≤ 1/2`, so `R(s) - R(0) = s T(s)/(Q(s) Q(0))` and `R'` are bounded
there, and `ν̂' = -2πi ν̂²`. -/
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

/-- **The constant of the `√n` bound for an A-stable scheme**,
`HalfLineAlgebra.powerConst C₁ C₂` for the decay constants of `exists_decay`. -/
def sqrtConst : ℝ :=
  HalfLineAlgebra.powerConst (Classical.choose r.exists_decay)
    (Classical.choose (Classical.choose_spec r.exists_decay))

theorem sqrtConst_nonneg : 0 ≤ r.sqrtConst := HalfLineAlgebra.powerConst_nonneg _ _

/-- **The total variation of `μ_rⁿ` is at most `1 + C √n` for every A-stable `r`**, including
`|r(∞)| = 1` (`HalfLineAlgebra.variation_pow_le`). [BrennerThomee1979] -/
theorem variation_hpMeasure_pow_le_sqrtConst {r : RationalScheme} (hr : r.IsAStable) (n : ℕ) :
    (r.hpMeasure ^ n).variation ≤ 1 + r.sqrtConst * √n :=
  have h := Classical.choose_spec (Classical.choose_spec r.exists_decay)
  HalfLineAlgebra.variation_pow_le _ (norm_fourier_hpMeasure_le hr) (fun ξ => (h ξ).1)
    (fun ξ => (h ξ).2) n

/-! ### Bounded semigroups on Banach spaces -/

section Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (G : C0Semigroup ℂ E) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M)

/-- **Brenner–Thomée's stability bound for every A-stable rational scheme**
[BrennerThomee1979]: for `r` A-stable (`|r(iy)| ≤ 1`; `|r(∞)| = 1` allowed, e.g. Crank–Nicolson
and the Gauss methods) and a bounded semigroup, `‖S(t)‖ ≤ M`, on a complex Banach space,
`‖r(τA)ⁿ‖ ≤ M (1 + C_r √n)` for all `τ ≥ 0` and `n`, with `C_r` depending only on `r`
(`RationalScheme.sqrtConst`, not explicit). -/
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
