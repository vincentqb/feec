module

public import Feec.Domain.Mollify
public import Feec.Domain.Cutoff
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Finite speed of propagation for symmetric hyperbolic systems

Let `E` be a finite-dimensional real inner product space (`ℝⁿ`) with Haar measure, `ι` a finite set
of components, and `β : ι → ι → E` symmetric (`β j i = β i j`). The constant-coefficient
**symmetric hyperbolic system**

  `∂ₜ wⱼ = Σᵢ ∂_{β j i} wᵢ`

(Maxwell, acoustics, linear elastodynamics, the Einstein–Bianchi violation system, …) has
**speed** `c ≥ 0` if `|Σ_{j,i} wⱼ wᵢ L (β j i)| ≤ c ‖L‖ |w|²` for every covector `L`.

* `cone_energy` (classical solutions): if `w` solves the system on the ball `B(x, R)` for
  `t ∈ (0, T)` and `w(0) = 0` on `B(x, R)`, then `w(t) = 0` on `B(x, R - c t)`. Proof: the energy
  `e(s) = ∫ χ(R - c s - √(δ² + |y - x|²)) |w(s, y)|² dy` is nonincreasing, since
  `∂ₜ |w|² = Σ_{ji} ∂_{β j i} (wⱼ wᵢ)` (symmetry) and the flux is controlled by the speed.

## References

* [L. C. Evans, *Partial Differential Equations*][Evans2010], §7.3.2 (symmetric hyperbolic systems,
  domain of dependence)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §3.5 (Prop 3.6), §4.10 (interior propagation)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff InnerProductSpace Convolution

namespace Feec.Domain

namespace FiniteSpeed

/-! ## Symmetric hyperbolic operators and weak solutions -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

/-- The first-order operator `(P w)ⱼ = Σᵢ ∂_{β j i} wᵢ`. -/
def hypOp (β : ι → ι → E) : ConstCoeffOp E ℝ ι ι where
  coeff j i := [([β j i], 1)]

theorem hypOp_apply (β : ι → ι → E) (f : ι → E → ℝ) (j : ι) (y : E) :
    (hypOp β).apply f j y = ∑ i, fderiv ℝ (f i) y (β j i) := by
  simp [ConstCoeffOp.apply, hypOp, ConstCoeffOp.applyEntry, iterDeriv_singleton]

/-- The formal adjoint `(Pᵗ ψ)ᵢ = -Σⱼ ∂_{β j i} ψⱼ`. -/
theorem hypOp_formalAdj_apply (β : ι → ι → E) (f : ι → E → ℝ) (i : ι) (y : E) :
    (hypOp β).formalAdj.apply f i y = -∑ j, fderiv ℝ (f j) y (β j i) := by
  simp [ConstCoeffOp.apply, ConstCoeffOp.formalAdj, hypOp, ConstCoeffOp.adjEntry,
    ConstCoeffOp.applyEntry, iterDeriv_singleton]

variable [MeasureSpace E] [BorelSpace E] [IsFiniteMeasureOnCompacts (volume : Measure E)]

/-- `W : [0, T] → L²(Ω; ℝ^ι)` is a **weak solution** of `∂ₜ W = P W`: continuous, and
`∂ₜ ⟪W, ψ⟫ = ⟪W, Pᵗ ψ⟫` for every test field `ψ ∈ C_c^∞(Ω; ℝ^ι)` (no boundary condition). -/
structure IsWeakSolution (β : ι → ι → E) (Ω : Set E) (T : ℝ) (W : ℝ → L2F ℝ Ω ι) : Prop where
  cont : ContinuousOn W (Icc 0 T)
  deriv : ∀ t ∈ Icc 0 T, ∀ (ψ : ι → E → ℝ) (hψ : IsTestField Ω ψ),
    HasDerivWithinAt (fun s => ⟪W s, testField hψ⟫_ℝ)
      ⟪W t, testField ((hypOp β).formalAdj.isTestField_apply hψ)⟫_ℝ (Icc 0 T) t

end Operator

end FiniteSpeed

namespace FiniteSpeed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The regularized distance and the cone weight -/

/-- The regularized distance `q(y) = √(δ² + |y - x|²)`. -/
def qd (x : E) (δ : ℝ) (y : E) : ℝ := Real.sqrt (δ ^ 2 + ‖y - x‖ ^ 2)

variable {x : E} {δ : ℝ}

omit [InnerProductSpace ℝ E] in
theorem qd_pos (hδ : 0 < δ) (y : E) : 0 < qd x δ y := Real.sqrt_pos.2 (by positivity)

omit [InnerProductSpace ℝ E] in
theorem norm_le_qd (y : E) : ‖y - x‖ ≤ qd x δ y := by
  rw [qd, Real.le_sqrt (norm_nonneg _) (by positivity)]
  nlinarith [sq_nonneg δ]

omit [InnerProductSpace ℝ E] in
theorem qd_lt_of_lt {y : E} {r : ℝ} (h : ‖y - x‖ < r) : ∃ δ > 0, qd x δ y < r := by
  have hr : 0 < r := (norm_nonneg _).trans_lt h
  set d := r ^ 2 - ‖y - x‖ ^ 2
  have hd : 0 < d := by nlinarith [norm_nonneg (y - x)]
  refine ⟨Real.sqrt (d / 2), Real.sqrt_pos.2 (by positivity), ?_⟩
  rw [qd, Real.sq_sqrt (by positivity), Real.sqrt_lt' hr]
  linarith

theorem hasFDerivAt_qd (hδ : 0 < δ) (y : E) :
    HasFDerivAt (qd x δ) ((qd x δ y)⁻¹ • innerSL ℝ (y - x)) y := by
  have hg : HasFDerivAt (fun y : E => δ ^ 2 + ‖y - x‖ ^ 2)
      (2 • (innerSL ℝ (y - x)).comp (ContinuousLinearMap.id ℝ E)) y :=
    (((hasFDerivAt_id y).sub_const x).norm_sq).const_add _
  have h := hg.sqrt (by positivity)
  refine HasFDerivAt.congr_fderiv (f := qd x δ) h ?_
  ext v
  have hq := qd_pos (x := x) hδ y
  rw [show Real.sqrt (δ ^ 2 + ‖y - x‖ ^ 2) = qd x δ y from rfl]
  simp
  field_simp

theorem contDiff_qd (hδ : 0 < δ) : ContDiff ℝ ∞ (qd x δ) := by
  unfold qd
  refine ContDiff.sqrt (contDiff_const.add ((contDiff_id.sub contDiff_const).norm_sq ℝ)) fun y => ?_
  positivity

theorem continuous_qd (hδ : 0 < δ) : Continuous (qd x δ) := (contDiff_qd hδ).continuous

/-- `|∇q| ≤ 1`. -/
theorem norm_fderiv_qd_le (hδ : 0 < δ) (y : E) : ‖fderiv ℝ (qd x δ) y‖ ≤ 1 := by
  have hq := qd_pos (x := x) hδ y
  rw [(hasFDerivAt_qd hδ y).fderiv, norm_smul, innerSL_apply_norm, Real.norm_of_nonneg
    (inv_nonneg.2 hq.le), inv_mul_le_iff₀ hq, mul_one]
  exact norm_le_qd y

/-- The cone weight `ψ(s, y) = χ(R - c s - q(y))`. -/
def wt (x : E) (δ c R s : ℝ) (y : E) : ℝ := Real.smoothTransition (R - c * s - qd x δ y)

variable {c R : ℝ}

omit [InnerProductSpace ℝ E] in
theorem wt_nonneg (s : ℝ) (y : E) : 0 ≤ wt x δ c R s y := Real.smoothTransition.nonneg _

omit [InnerProductSpace ℝ E] in
theorem wt_le_one (s : ℝ) (y : E) : wt x δ c R s y ≤ 1 := Real.smoothTransition.le_one _

omit [InnerProductSpace ℝ E] in
theorem wt_pos {s : ℝ} {y : E} (h : qd x δ y < R - c * s) : 0 < wt x δ c R s y :=
  Real.smoothTransition.pos_of_pos (by linarith)

omit [InnerProductSpace ℝ E] in
/-- Off the ball `B(x, R)` the weight and its time derivative vanish for `s ≥ 0`. -/
theorem wt_far (hc : 0 ≤ c) {s : ℝ} (hs : 0 ≤ s) {y : E} (hy : R ≤ ‖y - x‖) :
    wt x δ c R s y = 0 ∧ dχ (R - c * s - qd x δ y) = 0 := by
  have h1 := norm_le_qd (δ := δ) (x := x) y
  have h2 : 0 ≤ c * s := mul_nonneg hc hs
  exact ⟨Real.smoothTransition.zero_of_nonpos (by linarith), dχ_eq_zero_of_nonpos (by linarith)⟩

theorem contDiff_wt (hδ : 0 < δ) (s : ℝ) : ContDiff ℝ ∞ (wt x δ c R s) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_qd hδ))

theorem hasFDerivAt_wt (hδ : 0 < δ) (s : ℝ) (y : E) :
    HasFDerivAt (wt x δ c R s) (-(dχ (R - c * s - qd x δ y)) • fderiv ℝ (qd x δ) y) y := by
  have h := (hasDerivAt_χ (R - c * s - qd x δ y)).comp_hasFDerivAt y
    ((hasFDerivAt_const (R - c * s) y).sub ((contDiff_qd hδ).differentiable (by simp) y).hasFDerivAt)
  exact h.congr_fderiv (by simp [neg_smul])

/-- `|∇ψ| ≤ χ'`. -/
theorem norm_fderiv_wt_le (hδ : 0 < δ) (s : ℝ) (y : E) :
    ‖fderiv ℝ (wt x δ c R s) y‖ ≤ dχ (R - c * s - qd x δ y) := by
  rw [(hasFDerivAt_wt hδ s y).fderiv, norm_smul, norm_neg, Real.norm_of_nonneg (dχ_nonneg _)]
  calc dχ (R - c * s - qd x δ y) * ‖fderiv ℝ (qd x δ) y‖ ≤ dχ (R - c * s - qd x δ y) * 1 :=
        mul_le_mul_of_nonneg_left (norm_fderiv_qd_le hδ y) (dχ_nonneg _)
    _ = _ := mul_one _

omit [InnerProductSpace ℝ E] in
theorem hasDerivAt_wt_time (s : ℝ) (y : E) :
    HasDerivAt (fun s => wt x δ c R s y) (-(c * dχ (R - c * s - qd x δ y))) s := by
  have := (hasDerivAt_χ (R - c * s - qd x δ y)).comp s
    ((((hasDerivAt_id s).const_mul c).const_sub R).sub_const (qd x δ y))
  refine HasDerivAt.congr_deriv (f := fun s => wt x δ c R s y) this ?_
  simp [mul_comm]

theorem fderiv_wt_far (hδ : 0 < δ) (hc : 0 ≤ c) {s : ℝ} (hs : 0 ≤ s) {y : E}
    (hy : R ≤ ‖y - x‖) : fderiv ℝ (wt x δ c R s) y = 0 := by
  rw [(hasFDerivAt_wt hδ s y).fderiv, (wt_far hc hs hy).2]
  simp


/-! ## The energy estimate on cones -/

section Energy

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] {ι : Type*} [Fintype ι]

/-- A **symmetric hyperbolic system** `∂ₜ wⱼ = Σᵢ ∂_{β j i} wᵢ` with speed `c`: `β` is symmetric and
`|Σ_{j,i} wⱼ wᵢ L (β j i)| ≤ c ‖L‖ |w|²` for every covector `L`. -/
structure IsSymmHyperbolic (β : ι → ι → E) (c : ℝ) : Prop where
  symm : ∀ j i, β j i = β i j
  nonneg : 0 ≤ c
  speed : ∀ (L : E →L[ℝ] ℝ) (w : ι → ℝ),
    |∑ j, ∑ i, w j * w i * L (β j i)| ≤ c * ‖L‖ * ∑ j, w j ^ 2

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- `∂ₜ |w|² = Σ_{j,i} ∂_{β j i} (wⱼ wᵢ)` along solutions (symmetry of `β`). -/
theorem two_sum_mul_eq_sum_fderiv_mul {β : ι → ι → E} (hβ : ∀ j i, β j i = β i j)
    {f : ι → E → ℝ} {y : E} (hf : ∀ i, DifferentiableAt ℝ (f i) y) :
    2 * ∑ j, f j y * ∑ i, fderiv ℝ (f i) y (β j i) =
      ∑ j, ∑ i, fderiv ℝ (fun z => f j z * f i z) y (β j i) := by
  have e : ∀ j i, fderiv ℝ (fun z => f j z * f i z) y (β j i) =
      f j y * fderiv ℝ (f i) y (β j i) + f i y * fderiv ℝ (f j) y (β j i) := by
    intro j i
    rw [fderiv_fun_mul (hf j) (hf i)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  simp only [e, Finset.sum_add_distrib]
  have hswap : ∑ j, ∑ i, f i y * fderiv ℝ (f j) y (β j i) =
      ∑ j, ∑ i, f j y * fderiv ℝ (f i) y (β j i) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hβ i j]
  rw [hswap, ← two_mul]
  simp only [Finset.mul_sum]

/-- **Energy estimate on cones** (finite speed of propagation, classical form). Let `w` solve
the symmetric hyperbolic system `∂ₜ wⱼ = Σᵢ ∂_{β j i} wᵢ` (speed `c`) on the ball `B(x, R)` for
`t ∈ (0, T)`, with `w(s, ·) ∈ C¹` and `w`, `∂_β w` bounded. If `w(0) = 0` on `B(x, R)`, then
`w(t) = 0` on `B(x, R - c t)` for `t ∈ [0, T]`. -/
theorem cone_energy {β : ι → ι → E} {c : ℝ} (hβ : IsSymmHyperbolic β c) {T : ℝ}
    {w : ℝ → ι → E → ℝ} (hsm : ∀ s ∈ Icc 0 T, ∀ i, ContDiff ℝ 1 (w s i))
    (hcont : ∀ i y, ContinuousOn (fun s => w s i y) (Icc 0 T))
    (hbd : ∃ A, ∀ s ∈ Icc 0 T, ∀ i y, |w s i y| ≤ A ∧ ∀ j, |fderiv ℝ (w s i) y (β j i)| ≤ A)
    {x : E} {R : ℝ}
    (heq : ∀ s ∈ Ioo 0 T, ∀ y, ‖y - x‖ < R → ∀ j,
      HasDerivAt (fun s => w s j y) (∑ i, fderiv ℝ (w s i) y (β j i)) s)
    (h0 : ∀ y, ‖y - x‖ < R → ∀ i, w 0 i y = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) {y : E} (hy : ‖y - x‖ < R - c * t) (i₀ : ι) : w t i₀ y = 0 := by
  have hc := hβ.nonneg
  obtain ⟨δ, hδ, hqy⟩ := qd_lt_of_lt hy
  obtain ⟨A, hA⟩ := hbd
  obtain ⟨D, hD⟩ := exists_abs_dχ_le
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 ⟨le_rfl, ht.1.trans ht.2⟩ i₀ y).1
  set ψ : ℝ → E → ℝ := fun s => wt x δ c R s with hψ
  set N : ℝ → E → ℝ := fun s y => ∑ j, w s j y ^ 2 with hN
  set Q : ℝ → E → ℝ := fun s y => 2 * ∑ j, w s j y * ∑ i, fderiv ℝ (w s i) y (β j i) with hQ
  set F : ℝ → E → ℝ := fun s y => ψ s y * N s y with hF
  set F' : ℝ → E → ℝ := fun s y =>
    -(c * dχ (R - c * s - qd x δ y)) * N s y + ψ s y * Q s y with hF'
  set K : ℝ := Fintype.card ι * A ^ 2
  set K' : ℝ := 2 * (Fintype.card ι * A * (Fintype.card ι * A))
  -- pointwise facts
  have Nnn : ∀ s y, 0 ≤ N s y := fun s y => Finset.sum_nonneg fun j _ => sq_nonneg _
  have Nle : ∀ s ∈ Icc 0 T, ∀ y, N s y ≤ K := fun s hs y => by
    calc N s y ≤ ∑ _j : ι, A ^ 2 := Finset.sum_le_sum fun j _ => by
          have := (hA s hs j y).1
          nlinarith [abs_nonneg (w s j y), sq_abs (w s j y)]
      _ = K := by simp [K]
  have Qle : ∀ s ∈ Icc 0 T, ∀ y, |Q s y| ≤ K' := fun s hs y => by
    have h1 : ∀ j, |∑ i, fderiv ℝ (w s i) y (β j i)| ≤ Fintype.card ι * A := fun j => by
      calc |∑ i, fderiv ℝ (w s i) y (β j i)| ≤ ∑ i, |fderiv ℝ (w s i) y (β j i)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : ι, A := Finset.sum_le_sum fun i _ => (hA s hs i y).2 j
        _ = Fintype.card ι * A := by simp
    rw [hQ, abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    calc |∑ j, w s j y * ∑ i, fderiv ℝ (w s i) y (β j i)|
        ≤ ∑ j, |w s j y * ∑ i, fderiv ℝ (w s i) y (β j i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ι, A * (Fintype.card ι * A) := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul (hA s hs j y).1 (h1 j) (abs_nonneg _) hA0
      _ = Fintype.card ι * A * (Fintype.card ι * A) := by simp [mul_assoc]
  have far : ∀ s, 0 ≤ s → ∀ y, R ≤ ‖y - x‖ → ψ s y = 0 ∧ dχ (R - c * s - qd x δ y) = 0 :=
    fun s hs y hy => wt_far hc hs hy
  have F0 : ∀ s, 0 ≤ s → ∀ y, R ≤ ‖y - x‖ → F s y = 0 := fun s hs y hy => by
    simp only [hF, (far s hs y hy).1, zero_mul]
  have F'0 : ∀ s, 0 ≤ s → ∀ y, R ≤ ‖y - x‖ → F' s y = 0 := fun s hs y hy => by
    simp only [hF', (far s hs y hy).1, (far s hs y hy).2, mul_zero, neg_zero, zero_mul, add_zero]
  have cψ : ∀ s, Continuous (ψ s) := fun s => (contDiff_wt hδ s).continuous
  have cw : ∀ s ∈ Icc 0 T, ∀ i, Continuous (w s i) := fun s hs i => (hsm s hs i).continuous
  have cN : ∀ s ∈ Icc 0 T, Continuous (N s) := fun s hs =>
    continuous_finsetSum _ fun j _ => (cw s hs j).pow 2
  have cdw : ∀ s ∈ Icc 0 T, ∀ i (v : E), Continuous fun y => fderiv ℝ (w s i) y v :=
    fun s hs i v => ((hsm s hs i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cQ : ∀ s ∈ Icc 0 T, Continuous (Q s) := fun s hs =>
    continuous_const.mul (continuous_finsetSum _ fun j _ => (cw s hs j).mul
      (continuous_finsetSum _ fun i _ => cdw s hs i _))
  have cF : ∀ s ∈ Icc 0 T, Continuous (F s) := fun s hs => (cψ s).mul (cN s hs)
  have cdχ : ∀ s, Continuous fun y => dχ (R - c * s - qd x δ y) := fun s =>
    continuous_dχ.comp (continuous_const.sub (continuous_qd hδ))
  have cF' : ∀ s ∈ Icc 0 T, Continuous (F' s) := fun s hs =>
    ((continuous_const.mul (cdχ s)).neg.mul (cN s hs)).add ((cψ s).mul (cQ s hs))
  -- integrability: everything vanishes off `closedBall x R`
  have intOff : ∀ {g : E → ℝ}, Continuous g → (∀ y, R ≤ ‖y - x‖ → g y = 0) → Integrable g := by
    intro g hg hg0
    have : HasCompactSupport g := HasCompactSupport.intro (isCompact_closedBall x R) fun y hy => by
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hy
      exact hg0 y hy.le
    exact hg.integrable_of_hasCompactSupport this
  set bound : E → ℝ := (Metric.closedBall x R).indicator fun _ => K + c * D * K + K' with hbdd
  have hbound : Integrable bound :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const (measure_closedBall_lt_top).ne)
  have Fbd : ∀ s ∈ Icc 0 T, ∀ y, ‖F s y‖ ≤ bound y := fun s hs y => by
    by_cases hyb : y ∈ Metric.closedBall x R
    · rw [hbdd, indicator_of_mem hyb, Real.norm_eq_abs, abs_mul, abs_of_nonneg (wt_nonneg _ _),
        abs_of_nonneg (Nnn s y)]
      have h1 := wt_le_one (x := x) (δ := δ) (c := c) (R := R) s y
      have h2 := Nle s hs y
      have h3 : 0 ≤ K' := le_trans (abs_nonneg _) (Qle s hs y)
      have h4 : 0 ≤ c * D * K := mul_nonneg (mul_nonneg hc hD0) ((Nnn s y).trans h2)
      have h5 : ψ s y * N s y ≤ 1 * K :=
        mul_le_mul h1 h2 (Nnn s y) zero_le_one
      linarith
    · rw [hbdd, indicator_of_notMem hyb, F0 s hs.1 y (by
        rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hyb; exact hyb.le), norm_zero]
  have F'bd : ∀ s ∈ Icc 0 T, ∀ y, ‖F' s y‖ ≤ bound y := fun s hs y => by
    by_cases hyb : y ∈ Metric.closedBall x R
    · rw [hbdd, indicator_of_mem hyb, Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_neg, abs_mul, abs_of_nonneg hc, abs_of_nonneg (wt_nonneg _ _),
        abs_of_nonneg (Nnn s y)]
      have h1 : c * |dχ (R - c * s - qd x δ y)| * N s y ≤ c * D * K :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hD _) hc) (Nle s hs y) (Nnn s y)
          (mul_nonneg hc hD0)
      have h2 : ψ s y * |Q s y| ≤ 1 * K' :=
        mul_le_mul (wt_le_one _ _) (Qle s hs y) (abs_nonneg _) zero_le_one
      have h3 : 0 ≤ K := (Nnn s y).trans (Nle s hs y)
      linarith
    · rw [hbdd, indicator_of_notMem hyb, F'0 s hs.1 y (by
        rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hyb; exact hyb.le), norm_zero]
  -- step 1: continuity of the energy
  have hcontE : ContinuousOn (fun s => ∫ y, F s y) (Icc 0 T) := by
    refine continuousOn_of_dominated (bound := bound) (fun s hs => (cF s hs).aestronglyMeasurable)
      (fun s hs => Eventually.of_forall (Fbd s hs)) hbound (Eventually.of_forall fun y => ?_)
    have hψc : Continuous fun s => ψ s y :=
      Real.smoothTransition.continuous.comp ((continuous_const.sub
        (continuous_const.mul continuous_id)).sub continuous_const)
    have hNc : ContinuousOn (fun s => N s y) (Icc 0 T) :=
      continuousOn_finsetSum _ fun j _ => (hcont j y).pow 2
    exact hψc.continuousOn.mul hNc
  -- step 2: the derivative of the energy is nonpositive
  have hderiv : ∀ s ∈ Ioo 0 T, HasDerivAt (fun s => ∫ y, F s y) (∫ y, F' s y) s ∧
      ∫ y, F' s y ≤ 0 := by
    intro s hs
    have hsI : s ∈ Icc 0 T := Ioo_subset_Icc_self hs
    have hdif : ∀ᵐ y ∂volume, ∀ s' ∈ Ioo 0 T, HasDerivAt (F · y) (F' s' y) s' := by
      refine Eventually.of_forall fun y s' hs' => ?_
      by_cases hyR : ‖y - x‖ < R
      · have hNd : HasDerivAt (fun s => N s y) (Q s' y) s' := by
          have := HasDerivAt.fun_sum (u := Finset.univ) (A := fun j s => w s j y ^ 2)
            (A' := fun j => 2 * w s' j y * ∑ i, fderiv ℝ (w s' i) y (β j i)) (x := s')
            (fun j _ => by
              have h := (heq s' hs' y hyR j).mul (heq s' hs' y hyR j)
              have e : (fun s => w s j y ^ 2) = fun s => w s j y * w s j y :=
                funext fun s => sq _
              rw [e]
              convert h using 1
              ring)
          refine this.congr_deriv ?_
          simp only [hQ, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring_nf
        exact (hasDerivAt_wt_time s' y).mul hNd
      · rw [not_lt] at hyR
        rw [show F' s' y = 0 from F'0 s' hs'.1.le y hyR]
        refine (hasDerivAt_const s' (0 : ℝ)).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds hs'.1] with s'' hs''
        simp only [hF, (far s'' (le_of_lt hs'') y hyR).1, zero_mul]
    have hmeas : ∀ᶠ s' in 𝓝 s, AEStronglyMeasurable (F s') volume := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs'
      exact (cF s' (Ioo_subset_Icc_self hs')).aestronglyMeasurable
    obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := bound)
      (Ioo_mem_nhds hs.1 hs.2) hmeas (intOff (cF s hsI) (F0 s hs.1.le))
      (cF' s hsI).aestronglyMeasurable
      (Eventually.of_forall fun y s' hs' => F'bd s' (Ioo_subset_Icc_self hs') y) hbound hdif
    refine ⟨hd, ?_⟩
    have dw : ∀ i, Differentiable ℝ (w s i) := fun i => (hsm s hsI i).differentiable one_ne_zero
    set L : E → (E →L[ℝ] ℝ) := fun y => fderiv ℝ (ψ s) y with hL
    set g : ι → ι → E → ℝ := fun j i z => w s j z * w s i z with hg
    have cg : ∀ j i, ContDiff ℝ 1 (g j i) := fun j i => (hsm s hsI j).mul (hsm s hsI i)
    have cL : ∀ v, Continuous fun y => L y v := fun v =>
      ((contDiff_wt hδ s).continuous_fderiv (by simp)).clm_apply continuous_const
    have L0 : ∀ y, R ≤ ‖y - x‖ → L y = 0 := fun y hy => fderiv_wt_far hδ hc hs.1.le hy
    have i1 : ∀ j i, Integrable fun y => ψ s y * fderiv ℝ (g j i) y (β j i) := fun j i =>
      intOff ((cψ s).mul (((cg j i).continuous_fderiv one_ne_zero).clm_apply continuous_const))
        fun y hy => by simp [(far s hs.1.le y hy).1]
    have i2 : ∀ j i, Integrable fun y => L y (β j i) * g j i y := fun j i =>
      intOff ((cL _).mul (cg j i).continuous) fun y hy => by simp [L0 y hy]
    have hP0 : ∀ j i, ∫ y, (ψ s y * fderiv ℝ (g j i) y (β j i) + L y (β j i) * g j i y) = 0 :=
      fun j i => by
        rw [integral_add (i1 j i) (i2 j i), integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (i2 j i) (i1 j i) (intOff ((cψ s).mul (cg j i).continuous) fun y hy => by
            simp [(far s hs.1.le y hy).1])
          (fun y _ => (contDiff_wt hδ s).differentiable (by simp) y)
          (fun y _ => (cg j i).differentiable one_ne_zero y)]
        ring
    set G : E → ℝ := fun y => -(c * dχ (R - c * s - qd x δ y)) * N s y -
      ∑ j, ∑ i, L y (β j i) * g j i y with hG
    have cG : Continuous G := ((continuous_const.mul (cdχ s)).neg.mul (cN s hsI)).sub
      (continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun i _ =>
        (cL _).mul (cg j i).continuous)
    have intG : Integrable G := intOff cG fun y hy => by
      simp [hG, (far s hs.1.le y hy).2, L0 y hy]
    have hsplit : ∀ y, F' s y = G y + ∑ j, ∑ i,
        (ψ s y * fderiv ℝ (g j i) y (β j i) + L y (β j i) * g j i y) := fun y => by
      have e := two_sum_mul_eq_sum_fderiv_mul hβ.symm (f := w s) (y := y) (fun i => dw i y)
      simp only [hF', hQ, hG, Finset.sum_add_distrib]
      rw [e, Finset.mul_sum]
      simp only [Finset.mul_sum]
      ring
    have iji : ∀ j i, Integrable fun y =>
        ψ s y * fderiv ℝ (g j i) y (β j i) + L y (β j i) * g j i y := fun j i =>
      (i1 j i).add (i2 j i)
    have iSj : ∀ j, Integrable fun y => ∑ i,
        (ψ s y * fderiv ℝ (g j i) y (β j i) + L y (β j i) * g j i y) := fun j =>
      integrable_finsetSum _ fun i _ => iji j i
    have iS : Integrable fun y => ∑ j, ∑ i,
        (ψ s y * fderiv ℝ (g j i) y (β j i) + L y (β j i) * g j i y) :=
      integrable_finsetSum _ fun j _ => iSj j
    have hS0 : ∫ y, ∑ j, ∑ i,
        (ψ s y * fderiv ℝ (g j i) y (β j i) + L y (β j i) * g j i y) = 0 := by
      rw [integral_finsetSum _ fun j _ => iSj j]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [integral_finsetSum _ fun i _ => iji j i]
      exact Finset.sum_eq_zero fun i _ => hP0 j i
    rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add intG iS, hS0, add_zero]
    refine integral_nonpos fun y => ?_
    have hsp := hβ.speed (L y) (fun j => w s j y)
    have hLn : ‖L y‖ ≤ dχ (R - c * s - qd x δ y) := norm_fderiv_wt_le hδ s y
    have e2 : ∑ j, ∑ i, L y (β j i) * g j i y = ∑ j, ∑ i, w s j y * w s i y * L y (β j i) :=
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by simp only [hg]; ring
    have hNn := Nnn s y
    have hb : c * ‖L y‖ * N s y ≤ c * dχ (R - c * s - qd x δ y) * N s y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLn hc) hNn
    simp only [hG, Pi.zero_apply, e2]
    have := neg_abs_le (∑ j, ∑ i, w s j y * w s i y * L y (β j i))
    have hsp' : |∑ j, ∑ i, w s j y * w s i y * L y (β j i)| ≤ c * ‖L y‖ * N s y := hsp
    nlinarith
  -- step 3: monotonicity and conclusion
  have hanti : AntitoneOn (fun s => ∫ y, F s y) (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hcontE (fun t' ht' => ?_) fun t' ht' => ?_
    · rw [interior_Icc] at ht'
      exact (hderiv t' ht').1.differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht'
      rw [(hderiv t' ht').1.deriv]
      exact (hderiv t' ht').2
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hF0 : ∀ y, F 0 y = 0 := fun y => by
    by_cases hyR : ‖y - x‖ < R
    · simp [hF, hN, h0 y hyR]
    · exact F0 0 le_rfl y (not_lt.1 hyR)
  have he0 : ∫ y, F 0 y = 0 := by simp [hF0]
  have Fnn : ∀ s y, 0 ≤ F s y := fun s y => mul_nonneg (wt_nonneg _ _) (Nnn s y)
  have het : ∫ y, F t y = 0 :=
    le_antisymm (he0 ▸ hanti h0T ht ht.1) (integral_nonneg (Fnn t))
  have hFt : F t = 0 := by
    have hae := (integral_eq_zero_iff_of_nonneg (Fnn t) (intOff (cF t ht) (F0 t ht.1))).1 het
    exact (Continuous.ae_eq_iff_eq volume (cF t ht) continuous_zero).1 hae
  have hFy := congrFun hFt y
  simp only [hF, Pi.zero_apply, mul_eq_zero] at hFy
  have hNy : N t y = 0 := hFy.resolve_left (wt_pos hqy).ne'
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (w t j y)).1 hNy i₀
    (Finset.mem_univ _)
  exact pow_eq_zero_iff (two_ne_zero) |>.1 this

end Energy


/-! ## Weak `L²` solutions: mollification and the domain of dependence -/

section Weak

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [(volume : Measure E).IsNegInvariant]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bumps with radii `2/(n+2) → 0`. -/
def bumpSeq (n : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / (n + 2)
  rOut := 2 / (n + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
omit [InnerProductSpace ℝ E] in
theorem tendsto_bumpSeq_rOut : Tendsto (fun n => (bumpSeq (E := E) n).rOut) atTop (𝓝 0) := by
  simp only [bumpSeq]
  exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

variable {Ω : Set E}

/-- The reflected kernel `t ↦ h (y - t)` as an element of `L²(Ω)`. -/
def kerL2 (Ω : Set E) {h : E → ℝ} (hh : IsTest (univ : Set E) h) (y : E) : L2 ℝ Ω :=
  (((hh.comp_sub y).continuous.memLp_of_hasCompactSupport
    (hh.comp_sub y).hasCompactSupport).restrict Ω).toLp _

omit [FiniteDimensional ℝ E] [DecidableEq ι] in
theorem norm_kerL2_le {h : E → ℝ} (hh : IsTest (univ : Set E) h) (y : E) :
    ‖kerL2 Ω hh y‖ ≤ (eLpNorm h 2 volume).toReal := by
  rw [kerL2, Lp.norm_toLp]
  have e : eLpNorm (fun t => h (y - t)) 2 volume = eLpNorm h 2 volume :=
    eLpNorm_comp_measurePreserving (g := h) (f := fun t => y - t)
      hh.continuous.aestronglyMeasurable (Measure.measurePreserving_sub_left volume y)
  rw [← e]
  exact ENNReal.toReal_mono ((hh.comp_sub y).continuous.memLp_of_hasCompactSupport
    (hh.comp_sub y).hasCompactSupport).eLpNorm_ne_top
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

omit [FiniteDimensional ℝ E] [DecidableEq ι] in
omit [(volume : Measure E).IsNegInvariant] in
/-- Convolution of a zero extension with a smooth compactly supported kernel is an `L²(Ω)`
pairing with the reflected kernel. -/
theorem indicator_convolution_eq_inner (hΩ : MeasurableSet Ω) (u : L2 ℝ Ω) {h : E → ℝ}
    (hh : IsTest (univ : Set E) h) (y : E) :
    (Ω.indicator (u : E → ℝ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) y =
      ⟪u, kerL2 Ω hh y⟫_ℝ := by
  rw [convolution_apply_mul, kerL2, inner_toLp]
  simp only [RCLike.conj_to_real]
  rw [← integral_indicator hΩ]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Ω <;> simp [ht]

omit [FiniteDimensional ℝ E] [DecidableEq ι] in
theorem abs_indicator_convolution_le (hΩ : MeasurableSet Ω) (u : L2 ℝ Ω) {h : E → ℝ}
    (hh : IsTest (univ : Set E) h) (y : E) :
    |(Ω.indicator (u : E → ℝ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) y| ≤
      ‖u‖ * (eLpNorm h 2 volume).toReal := by
  rw [indicator_convolution_eq_inner hΩ u hh y]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (norm_kerL2_le hh y) (norm_nonneg _))


omit [(volume : Measure E).IsNegInvariant] [DecidableEq ι] in
omit [BorelSpace E] in
theorem locallyIntegrable_indicator (hΩ : MeasurableSet Ω) (u : L2 ℝ Ω) :
    LocallyIntegrable (Ω.indicator (u : E → ℝ)) volume :=
  ((memLp_indicator_iff_restrict hΩ.nullMeasurableSet).2 (Lp.memLp u)).locallyIntegrable
    (by norm_num)

/-- **Mollified weak solutions vanish on cones.** If `W` is a weak solution of a symmetric
hyperbolic system with speed `c`, `B(x, R + r) ⊆ Ω` (`r` the bump radius) and `W(0) = 0` a.e. on
`B(x, R + r)`, then the mollification `W(t) ⋆ ρ` vanishes on `B(x, R - c t)`. -/
theorem IsWeakSolution.molli_eq_zero {β : ι → ι → E} {c : ℝ} (hβ : IsSymmHyperbolic β c)
    {T : ℝ} {W : ℝ → L2F ℝ Ω ι} (hW : IsWeakSolution β Ω T W) (hΩ : IsOpen Ω)
    (φ : ContDiffBump (0 : E)) {x : E} {R : ℝ} (hball : Metric.ball x (R + φ.rOut) ⊆ Ω)
    (h0 : ∀ i, ∀ᵐ y ∂volume.restrict (Metric.ball x (R + φ.rOut)), W 0 i y = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) {y : E} (hy : ‖y - x‖ < R - c * t) (i₀ : ι) :
    molli φ (Ω.indicator (W t i₀ : E → ℝ)) y = 0 := by
  set ρ := φ.normed volume with hρd
  have hρ : IsTest (univ : Set E) ρ := ⟨φ.contDiff_normed, φ.hasCompactSupport_normed, subset_univ _⟩
  have hli : ∀ s i, LocallyIntegrable (Ω.indicator (W s i : E → ℝ)) volume := fun s i =>
    locallyIntegrable_indicator hΩ.measurableSet (W s i)
  set w : ℝ → ι → E → ℝ := fun s i => molli φ (Ω.indicator (W s i : E → ℝ)) with hw
  have hwconv : ∀ s i, w s i = Ω.indicator (W s i : E → ℝ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ρ := fun s i => rfl
  have hwinner : ∀ s i z, w s i z = ⟪W s i, kerL2 Ω hρ z⟫_ℝ := fun s i z => by
    rw [hwconv]; exact indicator_convolution_eq_inner hΩ.measurableSet _ hρ z
  -- a uniform bound on `‖W s‖`
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hW.cont).isBounded.exists_norm_le
  have hM' : ∀ s ∈ Icc 0 T, ∀ i, ‖W s i‖ ≤ M := fun s hs i =>
    (PiLp.norm_apply_le (W s) i).trans (hM _ ⟨s, hs, rfl⟩)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM' t ht i₀)
  set C : ℝ := (eLpNorm ρ 2 volume).toReal +
    ∑ j, ∑ i, (eLpNorm (fun z => fderiv ℝ ρ z (β j i)) 2 volume).toReal with hC
  have hdρ : ∀ v : E, IsTest (univ : Set E) (fun z => fderiv ℝ ρ z v) := fun v => hρ.fderiv_apply v
  refine cone_energy (w := w) (x := x) (R := R) hβ (T := T) (fun s _ i => ?_) (fun i z => ?_) ?_
    (fun s hs z hz j => ?_) (fun z hz i => ?_) ht hy i₀
  · exact (contDiff_molli φ (hli s i)).of_le (by simp)
  · simp only [hwinner]
    exact ((PiLp.continuous_apply 2 _ i).comp_continuousOn hW.cont).inner continuousOn_const
  · refine ⟨M * C, fun s hs i z => ⟨?_, fun j => ?_⟩⟩
    · rw [hwconv]
      refine (abs_indicator_convolution_le hΩ.measurableSet _ hρ z).trans ?_
      refine mul_le_mul (hM' s hs i) ?_ ENNReal.toReal_nonneg hM0
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
        ENNReal.toReal_nonneg)
    · rw [hwconv, fderiv_convolution_apply hρ (hli s i)]
      refine (abs_indicator_convolution_le hΩ.measurableSet _ (hdρ _) z).trans ?_
      refine mul_le_mul (hM' s hs i) ?_ ENNReal.toReal_nonneg hM0
      refine le_add_of_nonneg_of_le ENNReal.toReal_nonneg ?_
      refine (Finset.single_le_sum (f := fun i => (eLpNorm (fun z => fderiv ℝ ρ z (β j i)) 2
        volume).toReal) (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ i)).trans ?_
      exact Finset.single_le_sum (f := fun j => ∑ i, (eLpNorm (fun z => fderiv ℝ ρ z (β j i)) 2
        volume).toReal) (fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
        (Finset.mem_univ j)
  · -- the classical equation from the weak one
    have hsI : s ∈ Icc 0 T := Ioo_subset_Icc_self hs
    have hsupp : tsupport (fun t' => ρ (z - t')) ⊆ Ω := by
      refine (tsupport_comp_subset_preimage ρ (f := fun t' : E => z - t')
        (continuous_const.sub continuous_id)).trans ?_
      intro t' ht'
      rw [mem_preimage, φ.tsupport_normed_eq, Metric.mem_closedBall, dist_zero_right] at ht'
      refine hball ?_
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖t' - x‖ ≤ ‖t' - z‖ + ‖z - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < φ.rOut + R := by
          rw [norm_sub_rev]; linarith
        _ = R + φ.rOut := add_comm _ _
    have hψt : IsTest Ω (fun t' => ρ (z - t')) :=
      ⟨(hρ.comp_sub z).contDiff, (hρ.comp_sub z).hasCompactSupport, hsupp⟩
    have hψ : IsTestField Ω (Pi.single j fun t' => ρ (z - t')) := IsTestField.single j hψt
    have hd := (hW.deriv s hsI _ hψ).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have e1 : (fun s => ⟪W s, testField hψ⟫_ℝ) = fun s => w s j z := by
      funext s'
      rw [hwinner, L2F.inner_def, Finset.sum_eq_single j]
      · congr 1
        rw [testField_apply, toL2, kerL2]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun t' => by simp)
      · intro i _ hij
        rw [testField_apply, show toL2 (hψ i) = 0 from by
          rw [← toL2_zero (Ω := Ω)]; exact toL2_congr _ _ (by simp [hij]), inner_zero_right]
      · simp
    rw [e1] at hd
    refine hd.congr_deriv ?_
    rw [← hypOp_apply β (fun i => w s i) j z]
    have e2 := ConstCoeffOp.apply_convolution (hypOp β) hρ (hli s) j z
    simp only [hwconv]
    rw [e2, L2F.inner_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [testField_apply, inner_toL2]
    simp only [RCLike.conj_to_real]
    rw [← integral_indicator hΩ.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun t' => ?_)
    by_cases ht' : t' ∈ Ω <;> simp [ht']
  · -- vanishing initial data
    rw [hwinner, kerL2, inner_toLp]
    simp only [RCLike.conj_to_real]
    refine integral_eq_zero_of_ae ?_
    have hb : ∀ᵐ t' ∂volume, t' ∈ Metric.ball x (R + φ.rOut) → W 0 i t' = 0 :=
      (ae_restrict_iff' measurableSet_ball).1 (h0 i)
    filter_upwards [ae_restrict_of_ae hb] with t' ht'
    by_cases hin : t' ∈ Metric.ball x (R + φ.rOut)
    · rw [ht' hin, zero_mul]; rfl
    · have : ρ (z - t') = 0 := by
        by_contra hne
        have hmem : z - t' ∈ Function.support ρ := hne
        rw [hρd, φ.support_normed_eq, Metric.mem_ball, dist_zero_right] at hmem
        apply hin
        rw [Metric.mem_ball, dist_eq_norm]
        calc ‖t' - x‖ ≤ ‖t' - z‖ + ‖z - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ < φ.rOut + R := by rw [norm_sub_rev]; linarith
          _ = R + φ.rOut := add_comm _ _
      rw [this, mul_zero]; rfl


/-- **Finite speed of propagation for weak `L²` solutions** of a constant-coefficient symmetric
hyperbolic system with speed `c` (Maxwell, acoustics, elastodynamics, the Einstein–Bianchi
violation system): if `B(x, R) ⊆ Ω` and `W(0) = 0` a.e. on `B(x, R)`, then `W(t) = 0` a.e. on
`B(x, R - c t)` for every `t ∈ [0, T]`. No boundary condition and no boundedness of `Ω` enter.
[QuennevilleBelair2015], Prop 3.6 -/
theorem IsWeakSolution.ae_eq_zero_of_ball {β : ι → ι → E} {c : ℝ} (hβ : IsSymmHyperbolic β c)
    {T : ℝ} {W : ℝ → L2F ℝ Ω ι} (hW : IsWeakSolution β Ω T W) (hΩ : IsOpen Ω) {x : E} {R : ℝ}
    (hball : Metric.ball x R ⊆ Ω) (h0 : ∀ i, ∀ᵐ y ∂volume.restrict (Metric.ball x R), W 0 i y = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) (i : ι) :
    ∀ᵐ y ∂volume.restrict (Metric.ball x (R - c * t)), W t i y = 0 := by
  have hct : 0 ≤ c * t := mul_nonneg hβ.nonneg ht.1
  have hS : Metric.ball x (R - c * t) ⊆ Ω :=
    (Metric.ball_subset_ball (by linarith)).trans hball
  -- eventually in `n`, the mollification vanishes at every point of the smaller ball
  have hev : ∀ y ∈ Metric.ball x (R - c * t), ∀ᶠ n in atTop,
      molli (bumpSeq n) (Ω.indicator (W t i : E → ℝ)) y = 0 := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hgap : 0 < R - c * t - ‖y - x‖ := by linarith
    filter_upwards [(tendsto_order.1 (tendsto_bumpSeq_rOut (E := E))).2 _ hgap] with n hn
    refine hW.molli_eq_zero hβ hΩ (bumpSeq n) (R := R - (bumpSeq n).rOut) ?_ (fun j => ?_) ht
      (by linarith) i
    · rw [sub_add_cancel]; exact hball
    · rw [sub_add_cancel]; exact h0 j
  have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    (φ := bumpSeq (E := E)) (l := atTop) (K := 2) (tendsto_bumpSeq_rOut (E := E))
    (Eventually.of_forall fun n => by simp only [bumpSeq]; ring_nf; rfl)
    (locallyIntegrable_indicator hΩ.measurableSet (W t i))
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hconv] with y hy hyS
  simp only [← molli_eq_normed_convolution] at hy
  have h0' : Tendsto (fun n => molli (bumpSeq n) (Ω.indicator (W t i : E → ℝ)) y) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (by filter_upwards [hev y hyS] with n hn using hn.symm)
  have := tendsto_nhds_unique hy h0'
  rwa [indicator_of_mem (hS hyS)] at this

end Weak

/-! ## Transport along a measure-preserving linear isomorphism

`ℝⁿ = Fin n → ℝ` carries the sup norm, so its balls are cubes. Weak solutions on an open subset of
a normed space `F` are transported to the Euclidean space `E` along a measure-preserving linear
isomorphism `e : F ≃ E` (e.g. `WithLp.toLp 2`), where finite speed of propagation holds on
Euclidean balls; the conclusion holds on the preimages `e⁻¹ B(e x, R)` of Euclidean balls. -/

section Transport

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
  [IsFiniteMeasureOnCompacts (volume : Measure F)] {ι : Type*} [Fintype ι]
  [MeasureSpace E] [BorelSpace E] [IsFiniteMeasureOnCompacts (volume : Measure E)]
  (e : F ≃L[ℝ] E) {Ω : Set F}

omit [MeasureSpace F] [BorelSpace F] [IsFiniteMeasureOnCompacts (volume : Measure F)]
  [MeasureSpace E] [BorelSpace E] [IsFiniteMeasureOnCompacts (volume : Measure E)] in
theorem _root_.Feec.Domain.IsTest.comp_continuousLinearEquiv {ψ : E → ℝ}
    (hψ : IsTest (e.symm ⁻¹' Ω) ψ) : IsTest Ω (ψ ∘ e) := by
  refine ⟨hψ.contDiff.comp e.contDiff, hψ.hasCompactSupport.comp_homeomorph e.toHomeomorph, ?_⟩
  refine (tsupport_comp_subset_preimage ψ e.continuous).trans fun y hy => ?_
  have := hψ.tsupport_subset hy
  simpa using this

omit [MeasureSpace F] [BorelSpace F] [IsFiniteMeasureOnCompacts (volume : Measure F)]
  [MeasureSpace E] [BorelSpace E] [IsFiniteMeasureOnCompacts (volume : Measure E)] [Fintype ι] in
theorem _root_.Feec.Domain.IsTestField.comp_continuousLinearEquiv {ψ : ι → E → ℝ}
    (hψ : IsTestField (e.symm ⁻¹' Ω) ψ) : IsTestField Ω (fun i => ψ i ∘ e) :=
  fun i => (hψ i).comp_continuousLinearEquiv e

omit [MeasureSpace F] [BorelSpace F] [MeasureSpace E] [BorelSpace E]
  [IsFiniteMeasureOnCompacts (volume : Measure F)] [IsFiniteMeasureOnCompacts (volume : Measure E)] in
/-- `Pᵗ` commutes with the change of variables: `(P_{eβ}ᵗ ψ) ∘ e = P_βᵗ (ψ ∘ e)`. -/
theorem hypOp_formalAdj_apply_comp (β : ι → ι → F) (ψ : ι → E → ℝ) (i : ι) (y : F) :
    (hypOp fun j i => e (β j i)).formalAdj.apply ψ i (e y) =
      (hypOp β).formalAdj.apply (fun j => ψ j ∘ e) i y := by
  rw [hypOp_formalAdj_apply, hypOp_formalAdj_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e.comp_right_fderiv]
  rfl

variable (he' : MeasurePreserving e.symm volume volume)

/-- `u ↦ u ∘ e⁻¹ : L²(Ω) → L²(e Ω)`. -/
def transportL2 (hΩ : MeasurableSet Ω) : L2 ℝ Ω →ₗᵢ[ℝ] L2 ℝ (e.symm ⁻¹' Ω) :=
  Lp.compMeasurePreservingₗᵢ ℝ e.symm (he'.restrict_preimage hΩ)

/-- Componentwise `u ↦ u ∘ e⁻¹ : L²(Ω; ℝ^ι) → L²(e Ω; ℝ^ι)`. -/
def transportL2F (hΩ : MeasurableSet Ω) (u : L2F ℝ Ω ι) : L2F ℝ (e.symm ⁻¹' Ω) ι :=
  WithLp.toLp 2 fun i => transportL2 e he' hΩ (u i)

omit [BorelSpace F] [IsFiniteMeasureOnCompacts (volume : Measure F)] [Fintype ι] [BorelSpace E]
  [IsFiniteMeasureOnCompacts (volume : Measure E)] in
theorem continuous_transportL2F (hΩ : MeasurableSet Ω) :
    Continuous (transportL2F (ι := ι) e he' hΩ) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    (transportL2 e he' hΩ).continuous.comp (PiLp.continuous_apply 2 _ i))

omit [BorelSpace F] [IsFiniteMeasureOnCompacts (volume : Measure F)] [Fintype ι] [BorelSpace E]
  [IsFiniteMeasureOnCompacts (volume : Measure E)] in
theorem coeFn_transportL2F (hΩ : MeasurableSet Ω) (u : L2F ℝ Ω ι) (i : ι) :
    (transportL2F e he' hΩ u i : E → ℝ) =ᵐ[volume.restrict (e.symm ⁻¹' Ω)] (u i) ∘ e.symm :=
  Lp.coeFn_compMeasurePreserving _ _

/-- **Change of variables for the test pairing**: `⟪u ∘ e⁻¹, ψ⟫_{e Ω} = ⟪u, ψ ∘ e⟫_Ω`. -/
theorem inner_transportL2F_testField (hΩ : MeasurableSet Ω) (u : L2F ℝ Ω ι) {ψ : ι → E → ℝ}
    (hψ : IsTestField (e.symm ⁻¹' Ω) ψ) :
    ⟪transportL2F e he' hΩ u, testField hψ⟫_ℝ =
      ⟪u, testField (hψ.comp_continuousLinearEquiv e)⟫_ℝ := by
  rw [L2F.inner_def, L2F.inner_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [testField_apply, testField_apply, inner_toL2, inner_toL2]
  have hmp := he'.restrict_preimage (μa := volume) (μb := volume) hΩ
  rw [integral_congr_ae ((coeFn_transportL2F e he' hΩ u i).mono fun x hx => by
    simp only; rw [hx])]
  have := hmp.integral_comp e.symm.toHomeomorph.measurableEmbedding
    (fun y => (starRingEnd ℝ) ((u i : F → ℝ) y) * ψ i (e y))
  simpa [Function.comp] using this

/-- **Weak solutions transport**: if `W` solves `∂ₜ W = P_β W` weakly on `Ω`, then `W ∘ e⁻¹` solves
`∂ₜ W' = P_{eβ} W'` weakly on `e Ω`. -/
theorem IsWeakSolution.transport {β : ι → ι → F} {T : ℝ} {W : ℝ → L2F ℝ Ω ι}
    (hW : IsWeakSolution β Ω T W) (hΩ : MeasurableSet Ω) :
    IsWeakSolution (fun j i => e (β j i)) (e.symm ⁻¹' Ω) T
      (fun s => transportL2F e he' hΩ (W s)) := by
  refine ⟨(continuous_transportL2F e he' hΩ).comp_continuousOn hW.cont, fun t ht ψ hψ => ?_⟩
  have hd := hW.deriv t ht _ (hψ.comp_continuousLinearEquiv e)
  simp only [inner_transportL2F_testField e he' hΩ _ hψ]
  convert hd using 1
  rw [inner_transportL2F_testField e he' hΩ]
  congr 2
  funext i y
  exact hypOp_formalAdj_apply_comp e β ψ i y

end Transport

section TransportBall

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
  [IsFiniteMeasureOnCompacts (volume : Measure F)] {ι : Type*} [Fintype ι] [DecidableEq ι]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [(volume : Measure E).IsNegInvariant] (e : F ≃L[ℝ] E) {Ω : Set F}

/-- **Finite speed of propagation on preimages of Euclidean balls** for weak solutions on an
open subset of a normed space `F` (such as `ℝⁿ` with the sup norm): if `e⁻¹ B(e x, R) ⊆ Ω` and
`W(0) = 0` a.e. there, then `W(t) = 0` a.e. on `e⁻¹ B(e x, R - c t)`, for the speed `c` of the
transported system. -/
theorem IsWeakSolution.ae_eq_zero_of_preimage_ball (he : MeasurePreserving e volume volume)
    (he' : MeasurePreserving e.symm volume volume)
    {β : ι → ι → F} {c : ℝ} (hβ : IsSymmHyperbolic (fun j i => e (β j i)) c) {T : ℝ}
    {W : ℝ → L2F ℝ Ω ι} (hW : IsWeakSolution β Ω T W) (hΩ : IsOpen Ω) {x : F} {R : ℝ}
    (hball : e ⁻¹' Metric.ball (e x) R ⊆ Ω)
    (h0 : ∀ i, ∀ᵐ y ∂volume.restrict (e ⁻¹' Metric.ball (e x) R), W 0 i y = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) (i : ι) :
    ∀ᵐ y ∂volume.restrict (e ⁻¹' Metric.ball (e x) (R - c * t)), W t i y = 0 := by
  have hm := hΩ.measurableSet
  have hW' := hW.transport e he' hm
  have hΩ' : IsOpen (e.symm ⁻¹' Ω) := hΩ.preimage e.symm.continuous
  have hball' : Metric.ball (e x) R ⊆ e.symm ⁻¹' Ω := fun z hz =>
    hball (show e (e.symm z) ∈ Metric.ball (e x) R by simpa using hz)
  -- initial data on the Euclidean side
  have h0' : ∀ j, ∀ᵐ z ∂volume.restrict (Metric.ball (e x) R),
      transportL2F e he' hm (W 0) j z = 0 := by
    intro j
    have hB : MeasurableSet (Metric.ball (e x) R) := measurableSet_ball
    have h1 : ∀ᵐ z ∂volume.restrict (Metric.ball (e x) R),
        (transportL2F e he' hm (W 0) j : E → ℝ) z = (W 0 j : F → ℝ) (e.symm z) :=
      ae_restrict_of_ae_restrict_of_subset hball' (coeFn_transportL2F e he' hm (W 0) j)
    have hmp : MeasurePreserving e.symm (volume.restrict (Metric.ball (e x) R))
        (volume.restrict (e ⁻¹' Metric.ball (e x) R)) := by
      have := he'.restrict_preimage (μa := volume) (μb := volume) (hB.preimage e.continuous.measurable)
      simpa [Set.preimage_preimage] using this
    have h2 := hmp.quasiMeasurePreserving.ae (h0 j)
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2]
  have hv := hW'.ae_eq_zero_of_ball hβ hΩ' hball' h0' ht i
  -- back to `F`
  have hB : MeasurableSet (Metric.ball (e x) (R - c * t)) := measurableSet_ball
  have hsub : Metric.ball (e x) (R - c * t) ⊆ e.symm ⁻¹' Ω :=
    (Metric.ball_subset_ball (by nlinarith [hβ.nonneg, ht.1])).trans hball'
  have h1 : ∀ᵐ z ∂volume.restrict (Metric.ball (e x) (R - c * t)), (W t i : F → ℝ) (e.symm z) = 0 := by
    filter_upwards [hv, ae_restrict_of_ae_restrict_of_subset hsub
      (coeFn_transportL2F e he' hm (W t) i)] with z hz1 hz2
    rw [← hz1, hz2]; rfl
  have hmp : MeasurePreserving e (volume.restrict (e ⁻¹' Metric.ball (e x) (R - c * t)))
      (volume.restrict (Metric.ball (e x) (R - c * t))) := he.restrict_preimage hB
  filter_upwards [hmp.quasiMeasurePreserving.ae h1] with y hy
  simpa using hy

end TransportBall

end FiniteSpeed

end Feec.Domain
