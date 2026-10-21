module

public import Feec.Semigroup.Orbit
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# Bounded perturbations of strongly continuous semigroups (Dyson–Phillips)

For a strongly continuous semigroup `G` on a Banach space over `𝕜 = ℝ` or `ℂ`, with generator
`A`, and a bounded operator `B`, the operator `A + B` (domain `D(A)`, written `B +ᵥ A`) generates
a strongly continuous semigroup `G.perturb B`, and it is the only one:

* `C0Semigroup.dysonPhillips G B n`: the Dyson–Phillips terms `S₀(t) = S(t)`,
  `S_{n+1}(t) x = ∫₀ᵗ S(t - r) B S_n(r) x dr`, with
  `‖S_n(t) x‖ ≤ M^{n+1} ‖B‖ⁿ tⁿ/n! e^{ωt} ‖x‖` when `‖S t‖ ≤ M e^{ωt}`
  (`norm_dysonPhillips_le`);
* `C0Semigroup.perturb G B`: `S'(t) = Σₙ S_n(t)`, the unique solution of the Volterra equation
  `S'(t) x = S(t) x + ∫₀ᵗ S(t - r) B S'(r) x dr` (`perturb_S_apply_eq`,
  `eqOn_zero_of_volterra`);
* **`C0Semigroup.generator_perturb`**: `(G.perturb B).generator = B +ᵥ G.generator`;
* `C0Semigroup.norm_perturb_le`: `‖S t‖ ≤ M e^{ωt}` gives `‖S' t‖ ≤ M e^{(ω + M‖B‖)t}`;
* `C0Semigroup.dense_domain_generator`: the generator of a semigroup is densely defined.

`C0Semigroup.S` is defined at negative times too, where it carries no information; uniqueness is
therefore stated on `t ≥ 0` (`Set.EqOn _ _ (Ici 0)`).

The orbit calculus used here (`C0Semigroup.extS`, joint continuity, convolutions) lives in
`Feec.Semigroup.Orbit`. Uniqueness of the perturbed semigroup (`C0Semigroup.eqOn_perturb`,
`C0Semigroup.existsUnique_generator_eq_vadd`, `C0Semigroup.eqOn_of_generator_eq`) uses Duhamel's
formula and is in `Feec.Evolution.Perturbation`.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.1 (Thm 3.1.1: bounded perturbations; Dyson–Phillips series)
* [K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*][EngelNagel2000],
  §III.1 (Thm III.1.3)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter Topology MeasureTheory LinearPMap

@[expose] public noncomputable section

namespace Feec

/-! ### Derivative of a parametric integral at `0` -/

section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `h ↦ ∫₀ʰ g h r dr` has derivative `g 0 0` at `0` when `g` is jointly continuous at
`(0, 0)`. -/
theorem hasDerivAt_integral_param_zero {g : ℝ → ℝ → E}
    (hg : ContinuousAt (fun p : ℝ × ℝ => g p.1 p.2) (0, 0))
    (hint : ∀ h, IntervalIntegrable (g h) volume 0 h) :
    HasDerivAt (fun h => ∫ r in (0 : ℝ)..h, g h r) (g 0 0) 0 := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hg c hc
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
  simp only [intervalIntegral.integral_same, sub_zero]
  have e : (∫ r in (0 : ℝ)..h, g h r) - h • g 0 0 = ∫ r in (0 : ℝ)..h, (g h r - g 0 0) := by
    rw [intervalIntegral.integral_sub (hint h) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero]
  rw [e]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := c) fun r hr => ?_).trans ?_
  · have hr' : |r| ≤ |h| := by
      rcases mem_uIoc.1 hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_pos h1, abs_of_pos (h1.trans_le h2)]; exact h2
      · rw [abs_of_nonpos h2, abs_of_neg (h1.trans_le h2)]; linarith
    have hd : dist ((h, r) : ℝ × ℝ) (0, 0) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
      exact max_lt hh (hr'.trans_lt hh)
    have := hδg hd
    rw [dist_eq_norm] at this
    exact this.le
  · rw [sub_zero, Real.norm_eq_abs, mul_comm]

end Deriv

namespace C0Semigroup

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E)

/-! ### Density of the domain -/

/-- **The generator of a semigroup is densely defined**: `h⁻¹ ∫₀ʰ S σ x dσ ∈ D(A)` tends to
`x` as `h → 0⁺`. -/
theorem dense_domain_generator : Dense (G.generator.domain : Set E) := by
  intro x
  have hd := ((G.continuous_extS_apply x).integral_hasStrictDerivAt 0 0).hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have hd' := hd.mono_left (nhdsWithin_mono _
    (fun h (hh : h ∈ Ioi (0 : ℝ)) => (ne_of_gt hh : h ≠ 0) : Ioi (0 : ℝ) ⊆ {0}ᶜ))
  rw [G.extS_of_nonneg le_rfl, S_zero_apply] at hd'
  refine mem_closure_of_tendsto hd' ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  rw [slope_def_module, intervalIntegral.integral_same, sub_zero, sub_zero,
    G.integral_extS_eq hh.le]
  exact Submodule.smul_of_tower_mem _ _
    (LinearPMap.mem_domain_of_mem_graph (G.integral_mem_graph_S hh.le x))

variable (B : E →L[𝕜] E)

/-! ### The Dyson–Phillips terms -/

/-- The Dyson–Phillips terms `S₀(t) x = S(t) x`, `S_{n+1}(t) x = ∫₀ᵗ S(t - r) B S_n(r) x dr`
(with `S` extended by `S 0` to negative times, `extS`). -/
def dysonPhillips : ℕ → ℝ → E → E
  | 0, t, x => G.extS t x
  | n + 1, t, x => ∫ r in (0 : ℝ)..t, G.extS (t - r) (B (dysonPhillips n r x))

omit [CompleteSpace E] [IsScalarTower ℝ 𝕜 E] in
@[simp] theorem dysonPhillips_zero (t : ℝ) (x : E) : G.dysonPhillips B 0 t x = G.extS t x := rfl

omit [CompleteSpace E] [IsScalarTower ℝ 𝕜 E] in
theorem dysonPhillips_succ (n : ℕ) (t : ℝ) (x : E) :
    G.dysonPhillips B (n + 1) t x =
      ∫ r in (0 : ℝ)..t, G.extS (t - r) (B (G.dysonPhillips B n r x)) := rfl

omit [IsScalarTower ℝ 𝕜 E] in
theorem continuous_dysonPhillips (n : ℕ) (x : E) :
    Continuous fun t => G.dysonPhillips B n t x := by
  induction n with
  | zero => exact G.continuous_extS_apply x
  | succ n ih =>
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun t r => G.extS (t - r) (B (G.dysonPhillips B n r x)))
      (G.continuous_extS_uncurry.comp ((continuous_fst.sub continuous_snd).prodMk
        (B.continuous.comp (ih.comp continuous_snd)))) continuous_id

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem continuous_extS_comp {y : ℝ → E} (hy : Continuous y) (t : ℝ) :
    Continuous fun r => G.extS (t - r) (y r) :=
  G.continuous_extS_uncurry.comp ((continuous_const.sub continuous_id).prodMk hy)

omit [IsScalarTower ℝ 𝕜 E] in
theorem dysonPhillips_add (n : ℕ) (t : ℝ) (x y : E) :
    G.dysonPhillips B n t (x + y) = G.dysonPhillips B n t x + G.dysonPhillips B n t y := by
  induction n generalizing t with
  | zero => exact _root_.map_add _ x y
  | succ n ih =>
    simp only [dysonPhillips_succ]
    have hi : ∀ z, IntervalIntegrable (fun r => G.extS (t - r) (B (G.dysonPhillips B n r z)))
        volume 0 t := fun z =>
      (G.continuous_extS_comp (B.continuous.comp (G.continuous_dysonPhillips B n z)) t
        ).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add (hi x) (hi y)]
    congr 1
    funext r
    rw [ih, _root_.map_add, _root_.map_add]

omit [CompleteSpace E] in
theorem dysonPhillips_smul (n : ℕ) (t : ℝ) (c : 𝕜) (x : E) :
    G.dysonPhillips B n t (c • x) = c • G.dysonPhillips B n t x := by
  induction n generalizing t with
  | zero => exact _root_.map_smul _ c x
  | succ n ih =>
    simp only [dysonPhillips_succ]
    rw [← intervalIntegral.integral_smul]
    congr 1
    funext r
    rw [ih, _root_.map_smul, _root_.map_smul]

omit [CompleteSpace E] [IsScalarTower ℝ 𝕜 E] in
/-- **Bound on the Dyson–Phillips terms**: if `‖S τ‖ ≤ M e^{ωτ}` on `[0,T]`, then
`‖S_n(t) x‖ ≤ M^{n+1} ‖B‖ⁿ tⁿ/n! e^{ωt} ‖x‖` on `[0,T]`. -/
theorem norm_dysonPhillips_le {T M ω : ℝ} (hM : 0 ≤ M)
    (hS : ∀ τ ∈ Icc 0 T, ‖G.S τ‖ ≤ M * Real.exp (ω * τ)) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x : E) :
    ‖G.dysonPhillips B n t x‖ ≤
      M ^ (n + 1) * ‖B‖ ^ n * t ^ n / n.factorial * Real.exp (ω * t) * ‖x‖ := by
  induction n generalizing t with
  | zero =>
    simp only [dysonPhillips_zero, G.extS_of_nonneg ht.1, zero_add, pow_one, pow_zero, mul_one,
      Nat.factorial_zero, Nat.cast_one, div_one]
    exact ((G.S t).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hS t ht) (norm_nonneg _))
  | succ n ih =>
    rw [dysonPhillips_succ]
    set K := M ^ (n + 2) * ‖B‖ ^ (n + 1) / n.factorial * Real.exp (ω * t) * ‖x‖
    have hb : ∀ᵐ r ∂volume, r ∈ Ioc 0 t →
        ‖G.extS (t - r) (B (G.dysonPhillips B n r x))‖ ≤ K * r ^ n := by
      refine Eventually.of_forall fun r hr => ?_
      have hr' : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.trans ht.2⟩
      have htr : t - r ∈ Icc 0 T := ⟨sub_nonneg.2 hr.2, by linarith [hr.1, ht.2]⟩
      rw [G.extS_of_nonneg htr.1]
      calc ‖G.S (t - r) (B (G.dysonPhillips B n r x))‖
          ≤ M * Real.exp (ω * (t - r)) * (‖B‖ * ‖G.dysonPhillips B n r x‖) :=
            ((G.S _).le_opNorm _).trans (mul_le_mul (hS _ htr) (B.le_opNorm _) (by positivity)
              (by positivity))
        _ ≤ M * Real.exp (ω * (t - r)) * (‖B‖ * (M ^ (n + 1) * ‖B‖ ^ n * r ^ n / n.factorial *
              Real.exp (ω * r) * ‖x‖)) := by gcongr; exact ih hr'
        _ = K * r ^ n := by
            simp only [K]
            rw [show ω * t = ω * (t - r) + ω * r by ring, Real.exp_add]
            ring
    refine (intervalIntegral.norm_integral_le_of_norm_le ht.1 hb
      ((continuous_const.mul (continuous_pow n)).intervalIntegrable _ _)).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
    simp only [K]
    push_cast
    field_simp
    ring

omit [IsScalarTower ℝ 𝕜 E] in
/-- Uniform bounds on `[0,T]`. -/
theorem exists_norm_dysonPhillips_le (T : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ n, ∀ t ∈ Icc 0 T, ∀ x : E,
      ‖G.dysonPhillips B n t x‖ ≤ C * (C * ‖B‖ * T) ^ n / n.factorial * ‖x‖ := by
  obtain ⟨C, hC0, hC⟩ := G.exists_bound T
  refine ⟨C, hC0, fun n t ht x => ?_⟩
  have h := G.norm_dysonPhillips_le B (ω := 0) hC0 (fun τ hτ => by simpa using hC τ hτ) n ht x
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  refine h.trans ?_
  have : t ^ n ≤ T ^ n := pow_le_pow_left₀ ht.1 ht.2 n
  calc C ^ (n + 1) * ‖B‖ ^ n * t ^ n / n.factorial * ‖x‖
      ≤ C ^ (n + 1) * ‖B‖ ^ n * T ^ n / n.factorial * ‖x‖ := by gcongr
    _ = C * (C * ‖B‖ * T) ^ n / n.factorial * ‖x‖ := by rw [mul_pow, mul_pow]; ring

omit [IsScalarTower ℝ 𝕜 E] in
theorem summable_dysonPhillips {t : ℝ} (ht : 0 ≤ t) (x : E) :
    Summable fun n => G.dysonPhillips B n t x := by
  obtain ⟨C, hC0, hC⟩ := G.exists_norm_dysonPhillips_le B t
  refine Summable.of_norm_bounded (g := fun n => C * (C * ‖B‖ * t) ^ n / n.factorial * ‖x‖) ?_
    fun n => hC n t ⟨ht, le_rfl⟩ x
  have := (Real.summable_pow_div_factorial (C * ‖B‖ * t)).mul_left C
  simpa [mul_div_assoc] using this.mul_right ‖x‖

/-! ### The perturbed semigroup -/

/-- The perturbed semigroup `S'(t) = Σₙ S_n(t)` (`t ≥ 0`; `S'(t) = 1` for `t < 0`). -/
def perturbS (t : ℝ) : E →L[𝕜] E :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun x => ∑' n, G.dysonPhillips B n (max t 0) x
      map_add' := fun x y => by
        simp only [dysonPhillips_add]
        exact (G.summable_dysonPhillips B (le_max_right t 0) x).tsum_add
          (G.summable_dysonPhillips B (le_max_right t 0) y)
      map_smul' := fun c x => by
        simp only [dysonPhillips_smul, RingHom.id_apply]
        exact (G.summable_dysonPhillips B (le_max_right t 0) x).tsum_const_smul c }
    (by
      obtain ⟨C, hC0, hC⟩ := G.exists_norm_dysonPhillips_le B (max t 0)
      refine ⟨C * Real.exp (C * ‖B‖ * max t 0), fun x => ?_⟩
      have hs := (G.summable_dysonPhillips B (le_max_right t 0) x).hasSum
      have hg : HasSum (fun n => C * (C * ‖B‖ * max t 0) ^ n / n.factorial * ‖x‖)
          (C * Real.exp (C * ‖B‖ * max t 0) * ‖x‖) := by
        have := ((NormedSpace.expSeries_div_hasSum_exp (C * ‖B‖ * max t 0)).mul_left C).mul_right
          ‖x‖
        rw [← Real.exp_eq_exp_ℝ] at this
        simpa [mul_div_assoc] using this
      exact hs.norm_le_of_bounded hg fun n => hC n _ ⟨le_max_right t 0, le_rfl⟩ x)

theorem perturbS_apply (t : ℝ) (x : E) :
    G.perturbS B t x = ∑' n, G.dysonPhillips B n (max t 0) x := rfl

theorem hasSum_perturbS {t : ℝ} (ht : 0 ≤ t) (x : E) :
    HasSum (fun n => G.dysonPhillips B n t x) (G.perturbS B t x) := by
  rw [perturbS_apply, max_eq_left ht]
  exact (G.summable_dysonPhillips B ht x).hasSum

theorem continuous_perturbS_apply (x : E) : Continuous fun t => G.perturbS B t x := by
  have hT : ∀ T, ContinuousOn (fun t => G.perturbS B t x) (Iic T) := by
    intro T
    obtain ⟨C, -, hC⟩ := G.exists_norm_dysonPhillips_le B (max T 0)
    refine continuousOn_tsum (u := fun n => C * (C * ‖B‖ * max T 0) ^ n / n.factorial * ‖x‖)
      (fun n => ((G.continuous_dysonPhillips B n x).comp
        (continuous_id.max continuous_const)).continuousOn) ?_ fun n t ht =>
        hC n _ ⟨le_max_right t 0, max_le_max_right 0 ht⟩ x
    have := (Real.summable_pow_div_factorial (C * ‖B‖ * max T 0)).mul_left C
    simpa [mul_div_assoc] using this.mul_right ‖x‖
  rw [continuous_iff_continuousAt]
  intro t
  exact (hT (t + 1)).continuousAt (Iic_mem_nhds (by linarith))

theorem perturbS_zero : G.perturbS B 0 = 1 := by
  ext x
  rw [perturbS_apply, max_self, tsum_eq_single 0 fun n hn => ?_]
  · simp [G.extS_of_nonneg le_rfl]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [dysonPhillips_succ]

/-- **The Volterra equation**: `S'(t) x = S(t) x + ∫₀ᵗ S(t - r) B S'(r) x dr` for `t ≥ 0`. -/
theorem perturbS_eq {t : ℝ} (ht : 0 ≤ t) (x : E) :
    G.perturbS B t x = G.S t x + ∫ r in (0 : ℝ)..t, G.extS (t - r) (B (G.perturbS B r x)) := by
  have hs := G.hasSum_perturbS B ht x
  rw [← hs.tsum_eq, (G.summable_dysonPhillips B ht x).tsum_eq_zero_add, dysonPhillips_zero,
    G.extS_of_nonneg ht]
  congr 1
  obtain ⟨C, hC0, hC⟩ := G.exists_norm_dysonPhillips_le B t
  obtain ⟨C', hC'0, hC'⟩ := G.exists_bound_extS t
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun n r => G.extS (t - r) (B (G.dysonPhillips B n r x)))
    (f := fun r => G.extS (t - r) (B (G.perturbS B r x)))
    (fun n _ => C' * ‖B‖ * (C * (C * ‖B‖ * t) ^ n / n.factorial * ‖x‖))
    (fun n => ((G.continuous_extS_comp (B.continuous.comp (G.continuous_dysonPhillips B n x)) t)
      ).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun r hr => by
      rw [uIoc_of_le ht] at hr
      calc ‖G.extS (t - r) (B (G.dysonPhillips B n r x))‖
          ≤ C' * (‖B‖ * ‖G.dysonPhillips B n r x‖) :=
            ((G.extS _).le_opNorm _).trans (mul_le_mul (hC' _ (by linarith [hr.1]))
              (B.le_opNorm _) (by positivity) hC'0)
        _ ≤ C' * (‖B‖ * (C * (C * ‖B‖ * t) ^ n / n.factorial * ‖x‖)) := by
            gcongr; exact hC n r ⟨hr.1.le, hr.2⟩ x
        _ = _ := by ring)
    (Eventually.of_forall fun r _ => by
      have := (Real.summable_pow_div_factorial (C * ‖B‖ * t)).mul_left C
      simpa [mul_div_assoc] using (this.mul_right ‖x‖).mul_left (C' * ‖B‖))
    intervalIntegrable_const
    (Eventually.of_forall fun r hr => by
      rw [uIoc_of_le ht] at hr
      exact (G.hasSum_perturbS B hr.1.le x).mapL ((G.extS (t - r)).comp B))
  exact h.tsum_eq

omit [IsScalarTower ℝ 𝕜 E] in
/-- **Uniqueness for the Volterra equation**: a continuous solution of
`V t = ∫₀ᵗ S(t - r) B V(r) dr` on `[0,T]` vanishes there. -/
theorem eqOn_zero_of_volterra {V : ℝ → E} {T : ℝ} (hV : ContinuousOn V (Icc 0 T))
    (h : ∀ t ∈ Icc 0 T, V t = ∫ r in (0 : ℝ)..t, G.extS (t - r) (B (V r))) :
    ∀ t ∈ Icc 0 T, V t = 0 := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hV
  obtain ⟨C, hC0, hC⟩ := G.exists_bound_extS T
  have key : ∀ n : ℕ, ∀ t ∈ Icc 0 T, ‖V t‖ ≤ K * (C * ‖B‖ * t) ^ n / n.factorial := by
    intro n
    induction n with
    | zero => intro t ht; simpa using hK t ht
    | succ n ih =>
      intro t ht
      rw [h t ht]
      have hb : ∀ᵐ r ∂volume, r ∈ Ioc 0 t → ‖G.extS (t - r) (B (V r))‖ ≤
          C * ‖B‖ * (K * (C * ‖B‖) ^ n / n.factorial) * r ^ n := by
        refine Eventually.of_forall fun r hr => ?_
        calc ‖G.extS (t - r) (B (V r))‖ ≤ C * (‖B‖ * ‖V r‖) :=
              ((G.extS _).le_opNorm _).trans (mul_le_mul (hC _ (by linarith [hr.1, ht.2]))
                (B.le_opNorm _) (by positivity) hC0)
          _ ≤ C * (‖B‖ * (K * (C * ‖B‖ * r) ^ n / n.factorial)) := by
              gcongr; exact ih r ⟨hr.1.le, hr.2.trans ht.2⟩
          _ = _ := by rw [mul_pow]; ring
      refine (intervalIntegral.norm_integral_le_of_norm_le ht.1 hb
        ((continuous_const.mul (continuous_pow n)).intervalIntegrable _ _)).trans (le_of_eq ?_)
      rw [intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
      push_cast
      field_simp
      ring
  intro t ht
  have hlim : Tendsto (fun n : ℕ => K * ((C * ‖B‖ * t) ^ n / n.factorial)) atTop (𝓝 (K * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (C * ‖B‖ * t)).const_mul K
  rw [mul_zero] at hlim
  have : ‖V t‖ ≤ 0 := ge_of_tendsto' hlim fun n => by
    rw [← mul_div_assoc]; exact key n t ht
  exact norm_le_zero_iff.1 this

/-- The semigroup law for `S'`. -/
theorem perturbS_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    G.perturbS B (s + t) = G.perturbS B s * G.perturbS B t := by
  ext x
  change G.perturbS B (s + t) x = G.perturbS B s (G.perturbS B t x)
  set U := G.perturbS B
  have hUc : ∀ y, Continuous fun r => U r y := G.continuous_perturbS_apply B
  have hint : ∀ (y : ℝ → E), Continuous y → ∀ (τ a b : ℝ),
      IntervalIntegrable (fun r => G.extS (τ - r) (B (y r))) volume a b := fun y hy τ a b =>
    (G.continuous_extS_comp (B.continuous.comp hy) τ).intervalIntegrable a b
  -- `U (σ + t) x = S σ (U t x) + ∫₀^σ S(σ - r) B U(r + t) x dr`
  have hshift : ∀ σ, 0 ≤ σ → U (σ + t) x =
      G.S σ (U t x) + ∫ r in (0 : ℝ)..σ, G.extS (σ - r) (B (U (r + t) x)) := by
    intro σ hσ
    rw [G.perturbS_eq B (by linarith) x, ← intervalIntegral.integral_add_adjacent_intervals
      (hint _ (hUc x) _ 0 t) (hint _ (hUc x) _ t (σ + t)), G.perturbS_eq B ht x, _root_.map_add,
      G.S_add_apply hσ ht, add_assoc]
    congr 1
    have e1 : ∫ r in (0 : ℝ)..t, G.extS (σ + t - r) (B (U r x)) =
        G.S σ (∫ r in (0 : ℝ)..t, G.extS (t - r) (B (U r x))) := by
      rw [← (G.S σ).intervalIntegral_comp_comm (hint _ (hUc x) _ 0 t)]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le ht] at hr
      rw [G.extS_of_nonneg (by linarith [hr.2]), G.extS_of_nonneg (by linarith [hr.2]),
        show σ + t - r = σ + (t - r) by ring, G.S_add_apply hσ (by linarith [hr.2])]
    have e2 : ∫ r in t..σ + t, G.extS (σ + t - r) (B (U r x)) =
        ∫ r in (0 : ℝ)..σ, G.extS (σ - r) (B (U (r + t) x)) := by
      have h := intervalIntegral.integral_comp_add_right
        (fun r => G.extS (σ + t - r) (B (U r x))) t (a := 0) (b := σ)
      rw [zero_add] at h
      rw [← h]
      refine intervalIntegral.integral_congr fun r _ => ?_
      rw [show σ + t - (r + t) = σ - r by ring]
    rw [e1, e2]
  set V : ℝ → E := fun σ => U (σ + t) x - U σ (U t x)
  have hVc : Continuous V := ((hUc x).comp (continuous_id.add continuous_const)).sub (hUc _)
  have hVeq : ∀ T, ∀ σ ∈ Icc 0 T, V σ = ∫ r in (0 : ℝ)..σ, G.extS (σ - r) (B (V r)) := by
    intro T σ hσ
    simp only [V]
    have h1 : IntervalIntegrable (fun r => G.extS (σ - r) (B (U (r + t) x))) volume 0 σ :=
      hint _ ((hUc x).comp (continuous_id.add continuous_const)) _ 0 σ
    have h2 : IntervalIntegrable (fun r => G.extS (σ - r) (B (U r (U t x)))) volume 0 σ :=
      hint _ (hUc _) _ 0 σ
    rw [hshift σ hσ.1, G.perturbS_eq B hσ.1 (U t x), add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub h1 h2]
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [_root_.map_sub, _root_.map_sub]
  have := G.eqOn_zero_of_volterra B hVc.continuousOn (hVeq s) s ⟨hs, le_rfl⟩
  exact sub_eq_zero.1 this

/-- **The perturbed semigroup** `G.perturb B`, generated by `A + B` (`generator_perturb`). -/
def perturb : C0Semigroup 𝕜 E where
  S := G.perturbS B
  map_zero := G.perturbS_zero B
  map_add _ _ hs ht := G.perturbS_add B hs ht
  strongCont x := (G.continuous_perturbS_apply B x).continuousOn

@[simp] theorem perturb_S : (G.perturb B).S = G.perturbS B := rfl

/-- The Volterra equation for `G.perturb B`. -/
theorem perturb_S_apply_eq {t : ℝ} (ht : 0 ≤ t) (x : E) :
    (G.perturb B).S t x =
      G.S t x + ∫ r in (0 : ℝ)..t, G.extS (t - r) (B ((G.perturb B).S r x)) :=
  G.perturbS_eq B ht x

/-- The Duhamel term of the perturbation has derivative `B x` at `0`. -/
theorem hasDerivAt_perturb_integral (x : E) :
    HasDerivAt (fun h => ∫ r in (0 : ℝ)..h, G.extS (h - r) (B (G.perturbS B r x))) (B x) 0 := by
  have hj : Continuous fun p : ℝ × ℝ => G.extS (p.1 - p.2) (B (G.perturbS B p.2 x)) :=
    G.continuous_extS_uncurry.comp ((continuous_fst.sub continuous_snd).prodMk
      (B.continuous.comp ((G.continuous_perturbS_apply B x).comp continuous_snd)))
  have h := hasDerivAt_integral_param_zero
    (g := fun h r => G.extS (h - r) (B (G.perturbS B r x))) hj.continuousAt
    fun h => (G.continuous_extS_comp (B.continuous.comp (G.continuous_perturbS_apply B x)) h
      ).intervalIntegrable _ _
  simpa [G.extS_of_nonneg le_rfl, perturbS_zero] using h

/-- **The generator of the perturbed semigroup is `A + B`** (domain `D(A)`). -/
theorem generator_perturb :
    (G.perturb B).generator = (B : E →ₗ[𝕜] E) +ᵥ G.generator := by
  set Φ : E → ℝ → E := fun x h => ∫ r in (0 : ℝ)..h, G.extS (h - r) (B (G.perturbS B r x))
  have hΦ : ∀ x, HasDerivWithinAt (Φ x) (B x) (Ici 0) 0 := fun x =>
    (G.hasDerivAt_perturb_integral B x).hasDerivWithinAt
  have hU : ∀ x, ∀ h ∈ Ici (0 : ℝ), (G.perturb B).S h x = G.S h x + Φ x h := fun x h hh =>
    G.perturb_S_apply_eq B hh x
  have hdom : (G.perturb B).generator.domain = ((B : E →ₗ[𝕜] E) +ᵥ G.generator).domain := by
    ext x
    rw [vadd_domain]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y - B x, (hy.sub (hΦ x)).congr_of_mem (fun h hh => ?_) self_mem_Ici⟩
      change G.S h x = (G.perturb B).S h x - Φ x h
      rw [hU x h hh, add_sub_cancel_right]
    · rintro ⟨y, hy⟩
      exact ⟨y + B x, (hy.add (hΦ x)).congr_of_mem (fun h hh => hU x h hh) self_mem_Ici⟩
  refine LinearPMap.ext hdom fun x hx hx' => ?_
  have hd : HasDerivWithinAt (fun h => (G.perturb B).S h x)
      (G.generator ⟨x, hx'⟩ + B x) (Ici 0) 0 :=
    ((G.hasDerivWithinAt_generator ⟨x, hx'⟩).add (hΦ x)).congr_of_mem
      (fun h hh => hU x h hh) self_mem_Ici
  rw [(G.perturb B).generator_apply_eq (x := ⟨x, hx⟩) hd, vadd_apply, add_comm]
  rfl

/-- **Growth bound**: if `‖S t‖ ≤ M e^{ωt}` for `t ≥ 0`, then
`‖S' t‖ ≤ M e^{(ω + M‖B‖)t}`. -/
theorem norm_perturb_le {M ω : ℝ} (hM : 0 ≤ M) (hS : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M * Real.exp (ω * t))
    {t : ℝ} (ht : 0 ≤ t) : ‖(G.perturb B).S t‖ ≤ M * Real.exp ((ω + M * ‖B‖) * t) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have hs := G.hasSum_perturbS B ht x
  have hg : HasSum (fun n => M ^ (n + 1) * ‖B‖ ^ n * t ^ n / n.factorial * Real.exp (ω * t) * ‖x‖)
      (M * Real.exp ((ω + M * ‖B‖) * t) * ‖x‖) := by
    have := (((NormedSpace.expSeries_div_hasSum_exp (M * ‖B‖ * t)).mul_left
      (M * Real.exp (ω * t))).mul_right ‖x‖)
    rw [← Real.exp_eq_exp_ℝ] at this
    convert this using 1
    · funext n; rw [mul_pow, mul_pow, pow_succ]; ring
    · rw [add_mul, Real.exp_add]; ring_nf
  exact hs.norm_le_of_bounded hg fun n =>
    G.norm_dysonPhillips_le B (T := t) hM (fun τ hτ => hS τ hτ.1) n ⟨ht, le_rfl⟩ x

end C0Semigroup

end Feec
