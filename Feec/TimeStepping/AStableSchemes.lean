module

public import Feec.TimeStepping.RungeKutta
public import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Which rational schemes are A-stable, and of which order

A rational scheme `r = n/d` (`Feec.TimeStepping.RationalScheme`, `d` without zeros in the closed
left half-plane) is A-stable (`RationalScheme.IsAStable`) if `|r(iy)| ≤ 1` on the imaginary axis. By
the maximum principle this is the usual condition `|r(z)| ≤ 1` on the closed left half-plane
([HairerWanner1996], §IV.3), so that the definition is the usual one.

## Main results

* `norm_div_le_of_re_nonpos`: **the maximum principle in the left half-plane**: a complex
  rational function `p/q` without poles in the closed left half-plane and bounded by `C` on the
  imaginary axis is bounded by `C` on the closed left half-plane (Phragmén–Lindelöf,
  `PhragmenLindelof.right_half_plane_of_bounded_on_real`; `p/q` is bounded there since
  `deg p ≤ deg q`, `natDegree_le_of_norm_div_imaginary_le`);
* `RationalScheme.norm_eval_le_supNorm_of_re_nonpos`: `|r(z)| ≤ sup_y |r(iy)|` for `re z ≤ 0`, so
  `r` is A-stable iff `|r| ≤ 1` on the closed left half-plane
  (`RationalScheme.isAStable_iff_forall_re_nonpos`);
* **the θ-schemes** `r_θ(z) = (1 + (1 - θ) z)/(1 - θ z)`, exactly: A-stable iff `θ ≥ 1/2`
  (`RationalScheme.isAStable_theta_iff`; for `θ < 1/2`, `|r_θ(i)| > 1`,
  `one_half_le_of_norm_theta_le`), and of order `m` iff `m ≤ 1`, or `m = 2` and `θ = 1/2`
  (`RationalScheme.hasOrder_theta_iff`, from `X_pow_dvd_theta_iff` for every real `θ`:
  `r_θ(z) - e^z = (θ - 1/2) z² + (θ² - 1/6) z³ + O(z⁴)`);
* **the exact orders of the Runge–Kutta instances** of `Feec.TimeStepping.RungeKutta`: the
  two-stage Gauss–Legendre, Radau IIA and SDIRK methods have orders exactly `4`, `3` and `2`
  (`RationalScheme.not_hasOrder_gaussLegendre2`, `RationalScheme.not_hasOrder_radauIIA2`,
  `RationalScheme.not_hasOrder_sdirk2`).

## References

* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996],
  §IV.3 (A-stability, the maximum principle, the θ-methods), §IV.5, §IV.6

Bibliography: [references.bib](../../docs/references.bib)
-/

open Polynomial Filter Asymptotics

@[expose] public noncomputable section

namespace Feec.TimeStepping

/-! ### The maximum principle in the left half-plane -/

/-- **The maximum principle in the left half-plane**: a complex rational function `p/q` without
poles in the closed left half-plane, with `|p(iy)/q(iy)| ≤ C` on the imaginary axis, satisfies
`|p(z)/q(z)| ≤ C` on the closed left half-plane. It is bounded there (`deg p ≤ deg q` by the
bound on the axis, `natDegree_le_of_norm_div_imaginary_le`, then
`exists_norm_div_le_of_isClosed`), so that Phragmén–Lindelöf
(`PhragmenLindelof.right_half_plane_of_bounded_on_real`) applies to `w ↦ p(-w)/q(-w)` in the
right half-plane. [HairerWanner1996], §IV.3 -/
theorem norm_div_le_of_re_nonpos {p q : ℂ[X]} (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0) {C : ℝ}
    (hC : ∀ y : ℝ, ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖ ≤ C) {z : ℂ}
    (hz : z.re ≤ 0) : ‖p.eval z / q.eval z‖ ≤ C := by
  obtain ⟨B, hB⟩ := exists_norm_div_le_of_isClosed (natDegree_le_of_norm_div_imaginary_le hq hC)
    (isClosed_le Complex.continuous_re continuous_const) hq
  set f : ℂ → ℂ := fun w => p.eval (-w) / q.eval (-w) with hf_def
  have hf : ∀ w : ℂ, 0 ≤ w.re → ‖f w‖ ≤ B := fun w hw => hB (-w) (by simpa using hw)
  have hd : DiffContOnCl ℂ f {w : ℂ | 0 < w.re} := by
    refine DifferentiableOn.diffContOnCl fun w hw => ?_
    rw [Complex.closure_setOfPred_lt_re] at hw
    have hq0 : q.eval (-w) ≠ 0 := hq _ (by simpa using hw)
    exact (((p.differentiable (-w)).comp w differentiableAt_id.neg).div
      ((q.differentiable (-w)).comp w differentiableAt_id.neg) hq0).differentiableWithinAt
  have hexp : ∃ c < (2 : ℝ), ∃ B',
      f =O[Bornology.cobounded ℂ ⊓ Filter.principal {w : ℂ | 0 < w.re}]
        fun w => Real.exp (B' * ‖w‖ ^ c) := by
    refine ⟨0, two_pos, 0, IsBigO.of_bound B (eventually_inf_principal.2 (.of_forall
      fun w hw => ?_))⟩
    simpa using hf w (le_of_lt hw)
  have hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖f x‖ :=
    isBoundedUnder_of_eventually_le (a := B) ((eventually_ge_atTop 0).mono fun x hx =>
      hf x (by simpa using hx))
  have him : ∀ y : ℝ, ‖f (y * Complex.I)‖ ≤ C := fun y => by
    have e : -((y : ℂ) * Complex.I) = ((-y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hf_def]
    simp only
    rw [e]
    exact hC (-y)
  have h := PhragmenLindelof.right_half_plane_of_bounded_on_real hd hexp hre him
    (z := -z) (by simpa using hz)
  simpa [hf_def] using h

namespace RationalScheme

variable (r : RationalScheme)

/-- **The maximum principle for a rational scheme**: `|r(z)| ≤ sup_y |r(iy)|` on the closed left
half-plane (`norm_div_le_of_re_nonpos`). -/
theorem norm_eval_le_supNorm_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) : ‖r.eval z‖ ≤ r.supNorm := by
  have h := norm_div_le_of_re_nonpos (p := r.num.map (algebraMap ℝ ℂ))
    (q := r.den.map (algebraMap ℝ ℂ))
    (fun w hw => by rw [eval_map_algebraMap]; exact r.aeval_den_ne_zero w hw)
    (C := r.supNorm) (fun y => by
      simpa only [RationalScheme.eval, eval_map_algebraMap] using r.norm_eval_le_supNorm y) hz
  simpa only [RationalScheme.eval, eval_map_algebraMap] using h

/-- **A-stability on the closed left half-plane** ([HairerWanner1996], §IV.3): `r` is A-stable
(`|r(iy)| ≤ 1` on the imaginary axis) iff `|r(z)| ≤ 1` for `re z ≤ 0`. -/
theorem isAStable_iff_forall_re_nonpos : r.IsAStable ↔ ∀ z : ℂ, z.re ≤ 0 → ‖r.eval z‖ ≤ 1 :=
  ⟨fun h _ hz => (r.norm_eval_le_supNorm_of_re_nonpos hz).trans (r.isAStable_iff.1 h),
    fun h y => h _ (by simp)⟩

end RationalScheme

/-! ### The θ-schemes, exactly -/

/-- **`|r_θ(i)| ≤ 1` only for `θ ≥ 1/2`**, for real `θ`: `|1 + (1 - θ) i|² = 1 + (1 - θ)²` and
`|1 - θ i|² = 1 + θ²`. -/
theorem one_half_le_of_norm_theta_le {θ : ℝ}
    (h : ‖aeval Complex.I (1 + C (1 - θ) * X : ℝ[X]) /
      aeval Complex.I (1 - C θ * X : ℝ[X])‖ ≤ 1) : 1 / 2 ≤ θ := by
  simp only [map_add, map_one, map_mul, aeval_C, aeval_X, map_sub, Complex.coe_algebraMap] at h
  have hd : (1 : ℂ) - θ * Complex.I ≠ 0 := fun h0 => by
    simpa using congrArg Complex.re h0
  rw [norm_div, div_le_one (norm_pos_iff.2 hd)] at h
  have h2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 h
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h2
  simp at h2
  nlinarith

/-- The coefficients of the Taylor polynomial `Tₘ = ∑_{j ≤ m} Xʲ/j!` of the exponential. -/
theorem coeff_expTaylor (m d : ℕ) :
    (expTaylor m).coeff d = if d ≤ m then 1 / (d.factorial : ℝ) else 0 := by
  simp only [expTaylor, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- The coefficients of `(1 + (1 - θ) X) - (1 - θ X) Tₘ` from `X²` on. -/
private theorem coeff_theta_sub_add_two (θ : ℝ) (m d : ℕ) :
    ((1 + C (1 - θ) * X) - (1 - C θ * X) * expTaylor m : ℝ[X]).coeff (d + 2) =
      θ * (expTaylor m).coeff (d + 1) - (expTaylor m).coeff (d + 2) := by
  rw [sub_mul, one_mul, mul_assoc, coeff_sub, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul,
    coeff_X_mul, coeff_one, coeff_X, ite_eq_right (by omega), ite_eq_right (by omega)]
  ring

/-- **The orders of the θ-schemes**: for real `θ`, `X^{m+1}` divides
`(1 + (1 - θ) X) - (1 - θ X) Tₘ` iff `m ≤ 1`, or `m = 2` and `θ = 1/2`. The coefficients of `1`
and `X` vanish for `m ≥ 1`, those of `X²` and `X³` are `θ - 1/2` (for `m ≥ 2`) and `θ/2 - 1/6`
(for `m ≥ 3`). -/
theorem X_pow_dvd_theta_iff (θ : ℝ) (m : ℕ) :
    X ^ (m + 1) ∣ (1 + C (1 - θ) * X) - (1 - C θ * X) * expTaylor m ↔
      m ≤ 1 ∨ θ = 1 / 2 ∧ m = 2 := by
  have h0 : ((1 + C (1 - θ) * X) - (1 - C θ * X) * expTaylor m : ℝ[X]).coeff 0 = 0 := by
    rw [sub_mul, one_mul, mul_assoc, coeff_sub, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul,
      coeff_X_mul_zero, coeff_one_zero, coeff_X_zero, coeff_expTaylor, ite_eq_left (Nat.zero_le _)]
    simp
  have h1 : 1 ≤ m →
      ((1 + C (1 - θ) * X) - (1 - C θ * X) * expTaylor m : ℝ[X]).coeff 1 = 0 := fun hm => by
    rw [sub_mul, one_mul, mul_assoc, coeff_sub, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul,
      coeff_X_mul, coeff_one, coeff_X, coeff_expTaylor, coeff_expTaylor, ite_eq_left hm,
      ite_eq_left (Nat.zero_le _)]
    simp
  have h2 := coeff_theta_sub_add_two θ m 0
  have h3 := coeff_theta_sub_add_two θ m 1
  simp only [zero_add, coeff_expTaylor] at h2 h3
  rw [X_pow_dvd_iff]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hm2 : 2 ≤ m := by omega
    have e2 := h 2 (by omega)
    rw [h2, ite_eq_left (by omega), ite_eq_left hm2] at e2
    have hθ : θ = 1 / 2 := by norm_num at e2; linarith
    have hm3 : 3 ≤ m := by
      by_contra h3'
      exact hc.2 hθ (by omega)
    have e3 := h 3 (by omega)
    rw [h3, ite_eq_left (by omega), ite_eq_left hm3, hθ] at e3
    norm_num [Nat.factorial] at e3
  · rintro (hm | ⟨rfl, rfl⟩) d hd
    · interval_cases m <;> interval_cases d
      · exact h0
      · exact h0
      · exact h1 le_rfl
    · interval_cases d
      · exact h0
      · exact h1 (by norm_num)
      · rw [h2, ite_eq_left (by norm_num), ite_eq_left (by norm_num)]
        norm_num [Nat.factorial]

namespace RationalScheme

/-- **The θ-scheme is A-stable exactly for `θ ≥ 1/2`** ([HairerWanner1996], §IV.3). -/
theorem isAStable_theta_iff {θ : ℝ} (hθ : 0 < θ) : (theta θ hθ).IsAStable ↔ 1 / 2 ≤ θ := by
  refine ⟨fun h => one_half_le_of_norm_theta_le ?_, isAStable_theta⟩
  have := h 1
  rwa [Complex.ofReal_one, one_mul] at this

/-- **The orders of the θ-schemes**: `r_θ` has order `m` iff `m ≤ 1`, or `m = 2` and `θ = 1/2`
(Crank–Nicolson); no θ-scheme has order `3`. -/
theorem hasOrder_theta_iff {θ : ℝ} (hθ : 0 < θ) {m : ℕ} :
    (theta θ hθ).HasOrder m ↔ m ≤ 1 ∨ θ = 1 / 2 ∧ m = 2 :=
  X_pow_dvd_theta_iff θ m

/-! ### The exact orders of the Runge–Kutta instances -/

/-- **The two-stage Gauss–Legendre method has order exactly `4`**: the coefficient of `X⁵` in
`n - d T₅` is `-1/720`. -/
theorem not_hasOrder_gaussLegendre2 : ¬ gaussLegendre2.HasOrder 5 := by
  change ¬ X ^ 6 ∣ ButcherTableau.gaussLegendre2.stabilityNum -
    ButcherTableau.gaussLegendre2.stabilityDen * expTaylor 5
  rw [ButcherTableau.gaussLegendre2_stabilityNum, ButcherTableau.gaussLegendre2_stabilityDen,
    X_pow_dvd_iff]
  intro h
  have := h 5 (by norm_num)
  simp only [sub_mul, add_mul, one_mul, mul_assoc, coeff_sub, coeff_add, coeff_C_mul,
    coeff_X_mul, coeff_X_pow_mul', coeff_one, coeff_X, coeff_expTaylor] at this
  norm_num [Nat.factorial] at this

/-- **The two-stage Radau IIA method has order exactly `3`**: the coefficient of `X⁴` in
`n - d T₄` is `-1/72`. -/
theorem not_hasOrder_radauIIA2 : ¬ radauIIA2.HasOrder 4 := by
  change ¬ X ^ 5 ∣ ButcherTableau.radauIIA2.stabilityNum -
    ButcherTableau.radauIIA2.stabilityDen * expTaylor 4
  rw [ButcherTableau.radauIIA2_stabilityNum, ButcherTableau.radauIIA2_stabilityDen,
    X_pow_dvd_iff]
  intro h
  have := h 4 (by norm_num)
  simp only [sub_mul, add_mul, one_mul, mul_assoc, coeff_sub, coeff_add, coeff_C_mul,
    coeff_X_mul, coeff_X_pow_mul', coeff_one, coeff_X, coeff_expTaylor] at this
  norm_num [Nat.factorial] at this

/-- **The two-stage SDIRK method has order exactly `2`**: the coefficient of `X³` in `n - d T₃`
is `γ - γ² - 1/6 = √2/2 - 2/3 ≠ 0` (`γ² = 2γ - 1/2`). -/
theorem not_hasOrder_sdirk2 : ¬ sdirk2.HasOrder 3 := by
  change ¬ X ^ 4 ∣ ButcherTableau.sdirk2.stabilityNum -
    ButcherTableau.sdirk2.stabilityDen * expTaylor 3
  rw [ButcherTableau.sdirk2_stabilityNum, ButcherTableau.sdirk2_stabilityDen, X_pow_dvd_iff]
  intro h
  have := h 3 (by norm_num)
  simp only [sub_mul, add_mul, one_mul, mul_assoc, coeff_sub, coeff_add, coeff_C_mul,
    coeff_X_mul, coeff_X_pow_mul', coeff_one, coeff_X, coeff_expTaylor] at this
  norm_num [Nat.factorial] at this
  have hγ := ButcherTableau.sdirk2Coeff_sq
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold ButcherTableau.sdirk2Coeff at hγ this
  nlinarith [Real.sqrt_nonneg 2]

end RationalScheme

end Feec.TimeStepping
