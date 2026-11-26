module

public import Feec.ForMathlib.Analysis.HalfLineAlgebra
import Feec.ForMathlib.Analysis.Inequalities

/-!
# Powers of measures on the half-line whose atom may have modulus one

For `μ = a δ₀ + g` with `|μ̂| ≤ 1`, `|μ̂(ξ) - a| ≤ C₁ |ν̂(ξ)|` and `|μ̂'(ξ)| ≤ 2π C₂ |ν̂(ξ)|²`,
where `ν̂(ξ) = 1/(1 + 2πiξ)`, the density `gₙ` of `μⁿ` satisfies `∫ |gₙ| ≤ C √n` for every
`|a| ≤ 1` (after [BrennerThomee1979]).

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set Filter FourierTransform Unitization

@[expose] public noncomputable section

namespace Feec

namespace HalfLineAlgebra

/-! ### The first moment in Fourier variables -/

/-- The Fourier transform `(i/2π) μ̂'` of the first moment `t g(t)` of the density of `μ`. -/
def moment (μ : HalfLineAlgebra) (ξ : ℝ) : ℂ := 𝓕 (fun t : ℝ => t • μ.snd t) ξ

theorem hasDerivAt_fourier (μ : HalfLineAlgebra) (ξ : ℝ) :
    HasDerivAt (fun ξ => fourier ξ μ) (-2 * Real.pi * Complex.I * moment μ ξ) ξ := by
  have h := (Real.hasDerivAt_fourier μ.snd.integrable μ.snd.integrable_smul ξ).const_add μ.fst
  rw [fourier_neg_two_pi_smul, Pi.smul_apply, smul_eq_mul] at h
  convert h using 1
  · ext ξ
    exact fourier_apply ξ μ
  · rfl

theorem moment_mul (μ ν : HalfLineAlgebra) (ξ : ℝ) :
    moment (μ * ν) ξ = moment μ ξ * fourier ξ ν + fourier ξ μ * moment ν ξ := by
  have h1 := hasDerivAt_fourier (μ * ν) ξ
  have h2 := (hasDerivAt_fourier μ ξ).mul (hasDerivAt_fourier ν ξ)
  simp only [map_mul] at h1
  have hc : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  exact mul_left_cancel₀ hc (by linear_combination h1.unique h2)

theorem moment_one (ξ : ℝ) : moment 1 ξ = 0 := by
  simp [moment, snd_one, Real.fourier_eq]

theorem moment_sub (μ ν : HalfLineAlgebra) (ξ : ℝ) :
    moment (μ - ν) ξ = moment μ ξ - moment ν ξ := by
  have h1 := hasDerivAt_fourier (μ - ν) ξ
  have h2 := (hasDerivAt_fourier μ ξ).sub (hasDerivAt_fourier ν ξ)
  simp only [map_sub] at h1
  have hc : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  exact mul_left_cancel₀ hc (by linear_combination h1.unique h2)

theorem norm_moment_pow_le {μ : HalfLineAlgebra} {ξ : ℝ} (hσ : ‖fourier ξ μ‖ ≤ 1) (n : ℕ) :
    ‖moment (μ ^ n) ξ‖ ≤ n * ‖moment μ ξ‖ := by
  induction n with
  | zero => simp [moment_one]
  | succ n ih =>
    rw [pow_succ, moment_mul, map_pow]
    calc ‖moment (μ ^ n) ξ * fourier ξ μ + fourier ξ μ ^ n * moment μ ξ‖
        ≤ ‖moment (μ ^ n) ξ‖ * 1 + 1 * ‖moment μ ξ‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
          · exact mul_le_mul_of_nonneg_left hσ (norm_nonneg _)
          · have : ‖fourier ξ μ ^ n‖ ≤ 1 := by
              rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hσ
            exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ ≤ (n + 1 : ℕ) * ‖moment μ ξ‖ := by push_cast; nlinarith [norm_nonneg (moment μ ξ)]

theorem integral_norm_snd_pow_four_le {μ : HalfLineAlgebra} (hμ : μ.fst = 0) :
    (∫ t, ‖μ.snd t‖) ^ 4 ≤
      4 * Real.pi ^ 2 * (∫ ξ, ‖fourier ξ μ‖ ^ 2) * ∫ ξ, ‖moment μ ξ‖ ^ 2 := by
  have h1 : ∀ ξ, fourier ξ μ = 𝓕 (μ.snd : ℝ → ℂ) ξ := fun ξ => by
    rw [fourier_apply, hμ, zero_add]
  simp_rw [h1, moment]
  rw [MemLp.integral_norm_fourier_sq μ.snd.integrable μ.snd.memLp_two,
    MemLp.integral_norm_fourier_sq μ.snd.integrable_smul μ.snd.memLp_two_smul]
  exact MemLp.integral_norm_pow_four_le μ.snd.memLp_two μ.snd.memLp_two_smul

/-! ### Exponential measures -/

private theorem add_two_pi_mul_I_ne_zero {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    (c : ℂ) + 2 * Real.pi * ξ * Complex.I ≠ 0 := fun h => by
  have := congrArg Complex.re h
  simp at this; linarith

private theorem hasDerivAt_inv_add (c ξ : ℝ) (hc : 0 < c) :
    HasDerivAt (fun ξ : ℝ => ((c : ℂ) + 2 * Real.pi * ξ * Complex.I)⁻¹)
      (-2 * Real.pi * Complex.I * ((c : ℂ) + 2 * Real.pi * ξ * Complex.I)⁻¹ ^ 2) ξ := by
  have hne := add_two_pi_mul_I_ne_zero hc ξ
  have hf : HasDerivAt (fun ξ : ℝ => (c : ℂ) + 2 * Real.pi * ξ * Complex.I)
      (2 * Real.pi * Complex.I) ξ := by
    have := (((Complex.ofRealCLM.hasDerivAt (x := ξ)).const_mul (2 * Real.pi : ℂ)).mul_const
      Complex.I).const_add (c : ℂ)
    simpa using this
  convert hf.inv hne using 1
  field_simp

/-- The exponential measure `ν_c = c e^{-ct} dt`, `c > 0`, with `ν̂_c(ξ) = c/(c + 2πiξ)`. -/
def expMeasure (c : ℝ) (hc : 0 < c) : HalfLineAlgebra :=
  inr ((c : ℂ) • HalfLineKernel.exp c (by simpa using hc))

theorem fst_expMeasure (c : ℝ) (hc : 0 < c) : (expMeasure c hc).fst = 0 := fst_inr _ _

theorem fourier_expMeasure (c : ℝ) (hc : 0 < c) (ξ : ℝ) :
    fourier ξ (expMeasure c hc) = c * ((c : ℂ) + 2 * Real.pi * ξ * Complex.I)⁻¹ := by
  rw [fourier_apply, expMeasure, fst_inr, snd_inr, zero_add]
  rw [show 𝓕 (((c : ℂ) • HalfLineKernel.exp c (by simpa using hc) : HalfLineKernel) : ℝ → ℂ) ξ =
    HalfLineKernel.fourierChar ξ ((c : ℂ) • HalfLineKernel.exp c (by simpa using hc)) from rfl,
    map_smul, HalfLineKernel.fourierChar_apply, HalfLineKernel.coe_exp,
    HalfLineKernel.fourier_expFun (by simpa using hc), smul_eq_mul]

theorem moment_expMeasure (c : ℝ) (hc : 0 < c) (ξ : ℝ) :
    moment (expMeasure c hc) ξ = c * ((c : ℂ) + 2 * Real.pi * ξ * Complex.I)⁻¹ ^ 2 := by
  have h1 := hasDerivAt_fourier (expMeasure c hc) ξ
  have h2 := (hasDerivAt_inv_add c ξ hc).const_mul (c : ℂ)
  simp_rw [fourier_expMeasure] at h1
  have hc' : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  exact mul_left_cancel₀ hc' (by linear_combination h1.unique h2)

/-! ### The weights `(c² + (2πξ)²)⁻¹` -/

/-- `w_c(ξ) = (c² + (2πξ)²)⁻¹ = ‖(c + 2πiξ)⁻¹‖²`. -/
def weight (c ξ : ℝ) : ℝ := (c ^ 2 + (2 * Real.pi * ξ) ^ 2)⁻¹

theorem norm_inv_add_sq (c ξ : ℝ) :
    ‖((c : ℂ) + 2 * Real.pi * ξ * Complex.I)⁻¹‖ ^ 2 = weight c ξ := by
  rw [norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply, weight]
  simp; ring_nf

theorem weight_pos {c : ℝ} (hc : 0 < c) (ξ : ℝ) : 0 < weight c ξ := by
  unfold weight; positivity

theorem sq_mul_weight_le_one {c : ℝ} (hc : 0 < c) (ξ : ℝ) : c ^ 2 * weight c ξ ≤ 1 := by
  unfold weight
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  nlinarith [sq_nonneg (2 * Real.pi * ξ)]

theorem sq_two_pi_mul_weight_le_one {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    (2 * Real.pi * ξ) ^ 2 * weight c ξ ≤ 1 := by
  unfold weight
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  nlinarith [sq_nonneg c]

theorem weight_le {c : ℝ} (hc : 0 < c) (ξ : ℝ) : weight c ξ ≤ (c ^ 2)⁻¹ := by
  exact inv_anti₀ (by positivity) (le_add_of_nonneg_right (sq_nonneg _))

theorem weight_anti {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (ξ : ℝ) : weight d ξ ≤ weight c ξ := by
  unfold weight
  gcongr

theorem integrable_weight {c : ℝ} (hc : 0 < c) : Integrable (weight c) := by
  have hT : c / (2 * Real.pi) ≠ 0 := by positivity
  refine ((integrable_inv_one_add_sq.comp_div hT).const_mul (c ^ 2)⁻¹).congr
    (Eventually.of_forall fun ξ => ?_)
  simp only [weight]
  rw [← mul_inv]
  congr 1
  field_simp

theorem integral_weight {c : ℝ} (hc : 0 < c) : ∫ ξ, weight c ξ = 1 / (2 * c) := by
  have hT : 0 < c / (2 * Real.pi) := by positivity
  have h : weight c = fun ξ => (c ^ 2)⁻¹ * (1 + (ξ / (c / (2 * Real.pi))) ^ 2)⁻¹ := by
    ext ξ
    rw [weight, ← mul_inv]
    congr 1
    field_simp
  rw [h, integral_const_mul, MemLp.integral_inv_one_add_div_sq hT]
  field_simp

theorem norm_fourier_expMeasure_sq (c : ℝ) (hc : 0 < c) (ξ : ℝ) :
    ‖fourier ξ (expMeasure c hc)‖ ^ 2 = c ^ 2 * weight c ξ := by
  rw [fourier_expMeasure, norm_mul, mul_pow, norm_inv_add_sq, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

theorem norm_moment_expMeasure_sq (c : ℝ) (hc : 0 < c) (ξ : ℝ) :
    ‖moment (expMeasure c hc) ξ‖ ^ 2 = c ^ 2 * weight c ξ ^ 2 := by
  rw [moment_expMeasure, norm_mul, mul_pow, norm_pow, ← pow_mul, mul_comm 2 2, pow_mul,
    norm_inv_add_sq, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem norm_one_sub_fourier_expMeasure_sq (c : ℝ) (hc : 0 < c) (ξ : ℝ) :
    ‖fourier ξ (1 - expMeasure c hc)‖ ^ 2 = (2 * Real.pi * ξ) ^ 2 * weight c ξ := by
  have h : fourier ξ (1 - expMeasure c hc) =
      (2 * Real.pi * ξ : ℝ) * Complex.I * ((c : ℂ) + 2 * Real.pi * ξ * Complex.I)⁻¹ := by
    rw [map_sub, map_one, fourier_expMeasure]
    field_simp [add_two_pi_mul_I_ne_zero hc ξ]
    push_cast; ring
  rw [h, norm_mul, norm_mul, mul_pow, mul_pow, norm_inv_add_sq, Complex.norm_I, one_pow,
    mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem norm_fourier_expMeasure_sub_sq (c : ℝ) (hc : 0 < c) (ξ : ℝ) :
    ‖fourier ξ (expMeasure (2 * c) (by positivity) - expMeasure c hc)‖ ^ 2 =
      c ^ 2 * (2 * Real.pi * ξ) ^ 2 * weight (2 * c) ξ * weight c ξ := by
  have h : fourier ξ (expMeasure (2 * c) (by positivity) - expMeasure c hc) =
      c * ((2 * Real.pi * ξ : ℝ) * Complex.I) *
        ((((2 * c : ℝ) : ℂ) + 2 * Real.pi * ξ * Complex.I)⁻¹ *
          ((c : ℂ) + 2 * Real.pi * ξ * Complex.I)⁻¹) := by
    have h1 := add_two_pi_mul_I_ne_zero hc ξ
    have h2 := add_two_pi_mul_I_ne_zero (show 0 < 2 * c by positivity) ξ
    rw [map_sub, fourier_expMeasure, fourier_expMeasure]
    push_cast at h2 ⊢
    have h3 : (c : ℂ) + Real.pi * ξ * Complex.I ≠ 0 := fun h => h2 (by linear_combination 2 * h)
    field_simp
    ring
  rw [h, norm_mul, norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow, mul_pow,
    norm_inv_add_sq, norm_inv_add_sq, Complex.norm_I, one_pow, mul_one, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

/-! ### The pieces of a Littlewood–Paley decomposition -/

theorem integral_norm_snd_mul_pow_four_le {x m : HalfLineAlgebra} (hx : x.fst = 0)
    {GA GB : ℝ → ℝ} (hA : Integrable GA) (hB : Integrable GB)
    (hGA : ∀ ξ, ‖fourier ξ x * fourier ξ m‖ ^ 2 ≤ GA ξ)
    (hGB : ∀ ξ, ‖moment x ξ * fourier ξ m + fourier ξ x * moment m ξ‖ ^ 2 ≤ GB ξ) :
    (∫ t, ‖(x * m).snd t‖) ^ 4 ≤ 4 * Real.pi ^ 2 * (∫ ξ, GA ξ) * ∫ ξ, GB ξ := by
  have h0 : (x * m).fst = 0 := by rw [fst_mul, hx, zero_mul]
  refine (integral_norm_snd_pow_four_le h0).trans ?_
  simp_rw [map_mul, moment_mul]
  have i1 : ∫ ξ, ‖fourier ξ x * fourier ξ m‖ ^ 2 ≤ ∫ ξ, GA ξ :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) hA
      (Eventually.of_forall hGA)
  have i2 : ∫ ξ, ‖moment x ξ * fourier ξ m + fourier ξ x * moment m ξ‖ ^ 2 ≤ ∫ ξ, GB ξ :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) hB
      (Eventually.of_forall hGB)
  have n1 : 0 ≤ ∫ ξ, ‖fourier ξ x * fourier ξ m‖ ^ 2 := integral_nonneg fun _ => by positivity
  have n2 : 0 ≤ ∫ ξ, ‖moment x ξ * fourier ξ m + fourier ξ x * moment m ξ‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left i1 (by positivity)) i2 n2
    (mul_nonneg (by positivity) (n1.trans i1))

section Pieces

variable {x : HalfLineAlgebra} {α β : ℝ} (hx : x.fst = 0)
include hx

theorem integral_norm_snd_mul_low_pow_four_le (hβ : 0 ≤ β) (hx2 : ∀ ξ, ‖fourier ξ x‖ ^ 2 ≤ 4)
    (hxβ : ∀ ξ, ‖moment x ξ‖ ^ 2 ≤ β * weight 1 ξ ^ 2) :
    (∫ t, ‖(x * expMeasure 1 one_pos).snd t‖) ^ 4 ≤ 8 * Real.pi ^ 2 * (β + 4) := by
  have h := integral_norm_snd_mul_pow_four_le hx ((integrable_weight one_pos).const_mul 4)
    ((integrable_weight one_pos).const_mul (2 * β + 8)) (GA := fun ξ => 4 * weight 1 ξ)
    (GB := fun ξ => (2 * β + 8) * weight 1 ξ) (m := expMeasure 1 one_pos) (fun ξ => ?_)
    (fun ξ => ?_)
  · rw [integral_const_mul, integral_const_mul, integral_weight one_pos] at h
    exact h.trans_eq (by ring)
  · rw [norm_mul, mul_pow, norm_fourier_expMeasure_sq, one_pow, one_mul]
    exact mul_le_mul_of_nonneg_right (hx2 ξ) (weight_pos one_pos ξ).le
  · have w0 := (weight_pos one_pos ξ).le
    have w1 : weight 1 ξ ≤ 1 := by simpa using sq_mul_weight_le_one one_pos ξ
    refine (norm_add_sq_le_two_mul _ _).trans ?_
    rw [norm_mul, norm_mul, mul_pow, mul_pow, norm_fourier_expMeasure_sq,
      norm_moment_expMeasure_sq, one_pow, one_mul, one_mul]
    calc 2 * (‖moment x ξ‖ ^ 2 * weight 1 ξ) + 2 * (‖fourier ξ x‖ ^ 2 * weight 1 ξ ^ 2)
        ≤ 2 * (β * weight 1 ξ ^ 2 * weight 1 ξ) + 2 * (4 * weight 1 ξ ^ 2) := by
          gcongr
          · exact hxβ ξ
          · exact hx2 ξ
      _ = (2 * β * (weight 1 ξ * weight 1 ξ) + 8 * weight 1 ξ) * weight 1 ξ := by ring
      _ ≤ (2 * β * (1 * 1) + 8 * 1) * weight 1 ξ := by gcongr
      _ = _ := by ring

theorem integral_norm_snd_mul_mid_pow_four_le (hβ : 0 ≤ β) (hx2 : ∀ ξ, ‖fourier ξ x‖ ^ 2 ≤ 4)
    (hxβ : ∀ ξ, ‖moment x ξ‖ ^ 2 ≤ β * weight 1 ξ ^ 2) {c : ℝ} (hc : 0 < c) :
    (∫ t, ‖(x * (expMeasure (2 * c) (by positivity) - expMeasure c hc)).snd t‖) ^ 4 ≤
      4 * Real.pi ^ 2 * (β / (2 * c) + 32) := by
  have hc2 : 0 < 2 * c := by positivity
  have h := integral_norm_snd_mul_pow_four_le hx ((integrable_weight hc).const_mul (4 * c ^ 2))
    (((integrable_weight one_pos).const_mul (β / (2 * c ^ 2))).add
      ((integrable_weight hc).const_mul 32))
    (GA := fun ξ => 4 * c ^ 2 * weight c ξ)
    (GB := fun ξ => β / (2 * c ^ 2) * weight 1 ξ + 32 * weight c ξ)
    (m := expMeasure (2 * c) hc2 - expMeasure c hc) (fun ξ => ?_) (fun ξ => ?_)
  · rw [integral_const_mul, integral_add ((integrable_weight one_pos).const_mul _)
      ((integrable_weight hc).const_mul _), integral_const_mul, integral_const_mul,
      integral_weight hc, integral_weight one_pos] at h
    refine h.trans_eq ?_
    field_simp
    ring
  · have a1 := sq_two_pi_mul_weight_le_one hc2 ξ
    have w0 := (weight_pos hc ξ).le
    have w2 := (weight_pos hc2 ξ).le
    rw [norm_mul, mul_pow, norm_fourier_expMeasure_sub_sq]
    calc ‖fourier ξ x‖ ^ 2 * (c ^ 2 * (2 * Real.pi * ξ) ^ 2 * weight (2 * c) ξ * weight c ξ)
        = ‖fourier ξ x‖ ^ 2 * ((2 * Real.pi * ξ) ^ 2 * weight (2 * c) ξ) *
            (c ^ 2 * weight c ξ) := by ring
      _ ≤ 4 * 1 * (c ^ 2 * weight c ξ) := by gcongr; exact hx2 ξ
      _ = _ := by ring
  · have a1 := sq_two_pi_mul_weight_le_one one_pos ξ
    have a2 := sq_mul_weight_le_one hc ξ
    have a3 := sq_mul_weight_le_one hc2 ξ
    have a4 := weight_le hc2 ξ
    have a5 := weight_anti hc (by linarith : c ≤ 2 * c) ξ
    have w0 := (weight_pos hc ξ).le
    have w1 := (weight_pos one_pos ξ).le
    have w2 := (weight_pos hc2 ξ).le
    have hm : ‖moment (expMeasure (2 * c) hc2 - expMeasure c hc) ξ‖ ^ 2 ≤
        2 * ((2 * c) ^ 2 * weight (2 * c) ξ ^ 2) + 2 * (c ^ 2 * weight c ξ ^ 2) := by
      rw [moment_sub, sub_eq_add_neg, ← norm_moment_expMeasure_sq (2 * c) hc2 ξ,
        ← norm_moment_expMeasure_sq c hc ξ,
        ← norm_neg (moment (expMeasure c hc) ξ)]
      exact norm_add_sq_le_two_mul _ _
    refine (norm_add_sq_le_two_mul _ _).trans ?_
    rw [norm_mul, norm_mul, mul_pow, mul_pow, norm_fourier_expMeasure_sub_sq]
    calc 2 * (‖moment x ξ‖ ^ 2 *
            (c ^ 2 * (2 * Real.pi * ξ) ^ 2 * weight (2 * c) ξ * weight c ξ)) +
          2 * (‖fourier ξ x‖ ^ 2 * ‖moment (expMeasure (2 * c) hc2 - expMeasure c hc) ξ‖ ^ 2)
        ≤ 2 * (β * weight 1 ξ ^ 2 *
            (c ^ 2 * (2 * Real.pi * ξ) ^ 2 * weight (2 * c) ξ * weight c ξ)) +
          2 * (4 * (2 * ((2 * c) ^ 2 * weight (2 * c) ξ ^ 2) + 2 * (c ^ 2 * weight c ξ ^ 2))) := by
          gcongr
          · exact hxβ ξ
          · exact hx2 ξ
      _ = 2 * β * weight 1 ξ * (((2 * Real.pi * ξ) ^ 2 * weight 1 ξ) * (c ^ 2 * weight c ξ) *
            weight (2 * c) ξ) +
          16 * (((2 * c) ^ 2 * weight (2 * c) ξ) * weight (2 * c) ξ +
            (c ^ 2 * weight c ξ) * weight c ξ) := by ring
      _ ≤ 2 * β * weight 1 ξ * (1 * 1 * ((2 * c) ^ 2)⁻¹) +
          16 * (1 * weight c ξ + 1 * weight c ξ) := by gcongr
      _ = _ := by field_simp; ring

theorem integral_norm_snd_mul_high_pow_four_le (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hxα : ∀ ξ, ‖fourier ξ x‖ ^ 2 ≤ α * weight 1 ξ)
    (hxβ : ∀ ξ, ‖moment x ξ‖ ^ 2 ≤ β * weight 1 ξ ^ 2) {Λ : ℝ} (hΛ : 0 < Λ) :
    (∫ t, ‖(x * (1 - expMeasure Λ hΛ)).snd t‖) ^ 4 ≤
      2 * Real.pi ^ 2 * α * (α + β) / Λ ^ 3 := by
  have h := integral_norm_snd_mul_pow_four_le hx ((integrable_weight hΛ).const_mul α)
    ((integrable_weight one_pos).const_mul (2 * (β + α) / Λ ^ 2))
    (GA := fun ξ => α * weight Λ ξ) (GB := fun ξ => 2 * (β + α) / Λ ^ 2 * weight 1 ξ)
    (m := 1 - expMeasure Λ hΛ) (fun ξ => ?_) (fun ξ => ?_)
  · rw [integral_const_mul, integral_const_mul, integral_weight hΛ, integral_weight one_pos] at h
    refine h.trans_eq ?_
    field_simp
    ring
  · have a1 := sq_two_pi_mul_weight_le_one one_pos ξ
    have wΛ := (weight_pos hΛ ξ).le
    rw [norm_mul, mul_pow, norm_one_sub_fourier_expMeasure_sq]
    calc ‖fourier ξ x‖ ^ 2 * ((2 * Real.pi * ξ) ^ 2 * weight Λ ξ)
        ≤ α * weight 1 ξ * ((2 * Real.pi * ξ) ^ 2 * weight Λ ξ) := by gcongr; exact hxα ξ
      _ = α * ((2 * Real.pi * ξ) ^ 2 * weight 1 ξ) * weight Λ ξ := by ring
      _ ≤ α * 1 * weight Λ ξ := by gcongr
      _ = _ := by ring
  · have a1 := sq_two_pi_mul_weight_le_one one_pos ξ
    have a2 := sq_mul_weight_le_one hΛ ξ
    have a4 := weight_le hΛ ξ
    have w1 := (weight_pos one_pos ξ).le
    have wΛ := (weight_pos hΛ ξ).le
    refine (norm_add_sq_le_two_mul _ _).trans ?_
    rw [norm_mul, norm_mul, mul_pow, mul_pow, norm_one_sub_fourier_expMeasure_sq, moment_sub,
      moment_one, zero_sub, norm_neg, norm_moment_expMeasure_sq]
    calc 2 * (‖moment x ξ‖ ^ 2 * ((2 * Real.pi * ξ) ^ 2 * weight Λ ξ)) +
          2 * (‖fourier ξ x‖ ^ 2 * (Λ ^ 2 * weight Λ ξ ^ 2))
        ≤ 2 * (β * weight 1 ξ ^ 2 * ((2 * Real.pi * ξ) ^ 2 * weight Λ ξ)) +
          2 * (α * weight 1 ξ * (Λ ^ 2 * weight Λ ξ ^ 2)) := by
          gcongr
          · exact hxβ ξ
          · exact hxα ξ
      _ = 2 * weight 1 ξ * (β * ((2 * Real.pi * ξ) ^ 2 * weight 1 ξ) * weight Λ ξ +
            α * (Λ ^ 2 * weight Λ ξ) * weight Λ ξ) := by ring
      _ ≤ 2 * weight 1 ξ * (β * 1 * (Λ ^ 2)⁻¹ + α * 1 * (Λ ^ 2)⁻¹) := by gcongr
      _ = _ := by field_simp

end Pieces

/-! ### The `√n` bound -/

theorem expMeasure_congr {c d : ℝ} (h : c = d) (hc : 0 < c) (hd : 0 < d) :
    expMeasure c hc = expMeasure d hd := by
  subst h; rfl

theorem integral_norm_snd_add_le (y z : HalfLineAlgebra) :
    ∫ t, ‖(y + z).snd t‖ ≤ (∫ t, ‖y.snd t‖) + ∫ t, ‖z.snd t‖ := by
  rw [← integral_add y.snd.integrable.norm z.snd.integrable.norm]
  refine integral_mono (y + z).snd.integrable.norm ?_ fun t => ?_
  · exact y.snd.integrable.norm.add z.snd.integrable.norm
  · simp only [snd_add, HalfLineKernel.coe_add, Pi.add_apply]
    exact norm_add_le _ _

theorem integral_norm_snd_sum_le {ι : Type*} (s : Finset ι) (y : ι → HalfLineAlgebra) :
    ∫ t, ‖(∑ i ∈ s, y i).snd t‖ ≤ ∑ i ∈ s, ∫ t, ‖(y i).snd t‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HalfLineKernel.coe_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (integral_norm_snd_add_le _ _).trans (add_le_add_right ih _)

private theorem norm_pow_sub_pow_le_mul {σ a : ℂ} (hσ : ‖σ‖ ≤ 1) (ha : ‖a‖ ≤ 1) (n : ℕ) :
    ‖σ ^ n - a ^ n‖ ≤ n * ‖σ - a‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : σ ^ (n + 1) - a ^ (n + 1) = σ * (σ ^ n - a ^ n) + a ^ n * (σ - a) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖σ‖ * ‖σ ^ n - a ^ n‖ ≤ n * ‖σ - a‖ :=
      (mul_le_of_le_one_left (norm_nonneg _) hσ).trans ih
    have h2 : ‖a‖ ^ n * ‖σ - a‖ ≤ ‖σ - a‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ha)
    push_cast; linarith

theorem norm_fourier_resolvent_sq (ξ : ℝ) : ‖fourier ξ resolvent‖ ^ 2 = weight 1 ξ := by
  rw [fourier_resolvent, ← norm_inv_add_sq]
  simp

theorem hasDerivAt_fourier_resolvent (ξ : ℝ) :
    HasDerivAt (fun ξ => fourier ξ resolvent)
      (-2 * Real.pi * Complex.I * fourier ξ resolvent ^ 2) ξ := by
  simpa [fourier_resolvent] using hasDerivAt_inv_add 1 ξ one_pos

theorem norm_fourier_resolvent_sub_half (ξ : ℝ) : ‖fourier ξ resolvent - 1 / 2‖ ≤ 1 / 2 := by
  rw [fourier_resolvent]
  have hne : (1 : ℂ) + 2 * Real.pi * ξ * Complex.I ≠ 0 := by
    simpa using add_two_pi_mul_I_ne_zero one_pos ξ
  have e : (1 + 2 * Real.pi * ξ * Complex.I)⁻¹ - 1 / 2 =
      (starRingEnd ℂ) (1 + 2 * Real.pi * ξ * Complex.I) /
        (2 * (1 + 2 * Real.pi * ξ * Complex.I)) := by
    simp only [map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    field_simp
    ring
  rw [e, norm_div, norm_mul, Complex.norm_conj, Complex.norm_two]
  rw [div_le_iff₀ (by simpa using hne)]
  linarith

/-- The ratio `ρ = 2^{-1/4}` of the dyadic sum. -/
def dyadicRatio : ℝ := √(√(1 / 2))

theorem dyadicRatio_pow_four : dyadicRatio ^ 4 = 1 / 2 := by
  rw [dyadicRatio, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
    Real.sq_sqrt (by norm_num)]

theorem dyadicRatio_nonneg : 0 ≤ dyadicRatio := Real.sqrt_nonneg _

theorem dyadicRatio_lt_one : dyadicRatio < 1 := by
  rw [dyadicRatio, Real.sqrt_lt' one_pos, one_pow, Real.sqrt_lt' one_pos]
  norm_num

theorem norm_fst_le_one (μ : HalfLineAlgebra) (hσ : ∀ ξ, ‖fourier ξ μ‖ ≤ 1) {C₁ : ℝ}
    (h1 : ∀ ξ, ‖fourier ξ μ - μ.fst‖ ≤ C₁ * ‖fourier ξ resolvent‖) : ‖μ.fst‖ ≤ 1 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set ξ := (|C₁| + 1) / (2 * Real.pi * ε)
  have hξ : 0 < ξ := by positivity
  have hν : ‖fourier ξ resolvent‖ ≤ 1 / (2 * Real.pi * ξ) := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [norm_fourier_resolvent_sq, div_pow, one_pow, le_div_iff₀ (by positivity), mul_comm]
    exact sq_two_pi_mul_weight_le_one one_pos ξ
  have e : 1 / (2 * Real.pi * ξ) = ε / (|C₁| + 1) := by
    simp only [ξ]; field_simp
  calc ‖μ.fst‖ ≤ ‖fourier ξ μ‖ + ‖fourier ξ μ - μ.fst‖ := by
        have := norm_sub_le (fourier ξ μ) (fourier ξ μ - μ.fst)
        rwa [sub_sub_cancel] at this
    _ ≤ 1 + |C₁| * (1 / (2 * Real.pi * ξ)) := by
        gcongr
        · exact hσ ξ
        · exact (h1 ξ).trans (mul_le_mul (le_abs_self _) hν (norm_nonneg _) (abs_nonneg _))
    _ ≤ 1 + ε := by
        rw [e, mul_div_assoc']
        gcongr
        rw [div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg C₁]

/-- The constant `C = K₀ + K₁/(1 - ρ) + K₂` of the `√n` bound. -/
def powerConst (C₁ C₂ : ℝ) : ℝ :=
  √(√(8 * Real.pi ^ 2 * (C₂ ^ 2 + 4))) +
    √(√(4 * Real.pi ^ 2 * (C₂ ^ 2 / 2 + 32))) / (1 - dyadicRatio) +
      √(√(2 * Real.pi ^ 2 * C₁ ^ 2 * (C₁ ^ 2 + C₂ ^ 2)))

theorem powerConst_nonneg (C₁ C₂ : ℝ) : 0 ≤ powerConst C₁ C₂ := by
  have : 0 < 1 - dyadicRatio := by linarith [dyadicRatio_lt_one]
  unfold powerConst
  positivity

private theorem sqrt_sqrt_pow_four {K : ℝ} (hK : 0 ≤ K) : √(√K) ^ 4 = K := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hK]

private theorem sqrt_pow_four (n : ℕ) : √(n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- If `|μ̂| ≤ 1`, `|μ̂(ξ) - a| ≤ C₁ |ν̂(ξ)|` and `|μ̂'(ξ)| ≤ 2π C₂ |ν̂(ξ)|²`, the density `gₙ` of
`μⁿ` satisfies `∫ |gₙ| ≤ C √n`, `C = powerConst C₁ C₂`. -/
theorem integral_norm_pow_snd_le (μ : HalfLineAlgebra) (hσ : ∀ ξ, ‖fourier ξ μ‖ ≤ 1)
    {C₁ C₂ : ℝ} (h1 : ∀ ξ, ‖fourier ξ μ - μ.fst‖ ≤ C₁ * ‖fourier ξ resolvent‖)
    (h2 : ∀ ξ, ‖moment μ ξ‖ ≤ C₂ * ‖fourier ξ resolvent‖ ^ 2) (n : ℕ) :
    ∫ t, ‖(μ ^ n).snd t‖ ≤ powerConst C₁ C₂ * √n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [snd_one, HalfLineKernel.coe_zero]
  have ha : ‖μ.fst‖ ≤ 1 := norm_fst_le_one μ hσ h1
  -- the measure `x = gₙ dt`
  set x : HalfLineAlgebra := inr (μ ^ n).snd
  have hx : x.fst = 0 := fst_inr _ _
  have hxf : ∀ ξ, fourier ξ x = fourier ξ μ ^ n - μ.fst ^ n := fun ξ => by
    have h := fourier_apply ξ (μ ^ n)
    rw [map_pow, show (μ ^ n).fst = μ.fst ^ n from map_pow (fstHom ℂ HalfLineKernel) μ n] at h
    rw [fourier_apply, fst_inr, snd_inr, zero_add]
    linear_combination -h
  have hxm : ∀ ξ, moment x ξ = moment (μ ^ n) ξ := fun _ => rfl
  have hx2 : ∀ ξ, ‖fourier ξ x‖ ^ 2 ≤ 4 := fun ξ => by
    rw [hxf]
    have : ‖fourier ξ μ ^ n - μ.fst ^ n‖ ≤ 2 := (norm_sub_le _ _).trans (by
      rw [norm_pow, norm_pow]
      linarith [pow_le_one₀ (n := n) (norm_nonneg _) (hσ ξ),
        pow_le_one₀ (n := n) (norm_nonneg _) ha])
    nlinarith [norm_nonneg (fourier ξ μ ^ n - μ.fst ^ n)]
  have hxα : ∀ ξ, ‖fourier ξ x‖ ^ 2 ≤ (n ^ 2 * C₁ ^ 2) * weight 1 ξ := fun ξ => by
    rw [hxf, ← norm_fourier_resolvent_sq, show (n : ℝ) ^ 2 * C₁ ^ 2 * ‖fourier ξ resolvent‖ ^ 2 =
      (n * (C₁ * ‖fourier ξ resolvent‖)) ^ 2 by ring]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_pow_sub_pow_le_mul (hσ ξ) ha n).trans
      (mul_le_mul_of_nonneg_left (h1 ξ) (Nat.cast_nonneg _))) 2
  have hxβ : ∀ ξ, ‖moment x ξ‖ ^ 2 ≤ (n ^ 2 * C₂ ^ 2) * weight 1 ξ ^ 2 := fun ξ => by
    rw [hxm, ← norm_fourier_resolvent_sq, show (n : ℝ) ^ 2 * C₂ ^ 2 *
      (‖fourier ξ resolvent‖ ^ 2) ^ 2 = (n * (C₂ * ‖fourier ξ resolvent‖ ^ 2)) ^ 2 by ring]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_moment_pow_le (hσ ξ) n).trans
      (mul_le_mul_of_nonneg_left (h2 ξ) (Nat.cast_nonneg _))) 2
  have hα : (0 : ℝ) ≤ n ^ 2 * C₁ ^ 2 := by positivity
  have hβ : (0 : ℝ) ≤ n ^ 2 * C₂ ^ 2 := by positivity
  -- the Littlewood–Paley decomposition
  set J := Nat.log 2 n + 1
  set f : ℕ → HalfLineAlgebra := fun j => expMeasure (2 ^ j) (by positivity)
  have hf : ∀ j, f (j + 1) = expMeasure (2 * 2 ^ j) (by positivity) := fun j =>
    expMeasure_congr (pow_succ' 2 j) _ _
  have hdec : x = x * f 0 + ∑ j ∈ Finset.range J, x * (f (j + 1) - f j) + x * (1 - f J) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub, ← mul_add, ← mul_add]
    simp
  have hsnd : (μ ^ n).snd = x.snd := (snd_inr _ _).symm
  rw [hsnd, hdec]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hnn : (n : ℝ) ≤ n ^ 2 := by nlinarith
  -- the three bounds
  have hlow : ∫ t, ‖(x * f 0).snd t‖ ≤ √(√(8 * Real.pi ^ 2 * (C₂ ^ 2 + 4))) * √n := by
    have h := integral_norm_snd_mul_low_pow_four_le hx hβ hx2 hxβ
    rw [show f 0 = expMeasure 1 one_pos from expMeasure_congr (pow_zero 2) _ _] at ⊢
    refine le_of_pow_le_pow_left₀ four_ne_zero (by positivity) ?_
    rw [mul_pow, sqrt_sqrt_pow_four (by positivity), sqrt_pow_four]
    refine h.trans ?_
    nlinarith [sq_nonneg C₂, Real.pi_pos, sq_nonneg (n : ℝ)]
  have hmid : ∀ j ∈ Finset.range J, ∫ t, ‖(x * (f (j + 1) - f j)).snd t‖ ≤
      √(√(4 * Real.pi ^ 2 * (C₂ ^ 2 / 2 + 32))) * √n * dyadicRatio ^ j := by
    intro j hj
    have hc : (0 : ℝ) < 2 ^ j := by positivity
    have hjn : (2 : ℝ) ^ j ≤ n := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
      exact_mod_cast this.trans (Nat.pow_log_le_self 2 hn.ne')
    have h := integral_norm_snd_mul_mid_pow_four_le hx hβ hx2 hxβ hc
    rw [hf]
    refine le_of_pow_le_pow_left₀ four_ne_zero (by
      have := dyadicRatio_nonneg; positivity) ?_
    rw [mul_pow, mul_pow, sqrt_sqrt_pow_four (by positivity), sqrt_pow_four, ← pow_mul,
      mul_comm j 4, pow_mul, dyadicRatio_pow_four]
    refine h.trans ?_
    have e : ((1 : ℝ) / 2) ^ j = (2 ^ j)⁻¹ := by rw [one_div, inv_pow]
    rw [e]
    have h32 : (32 : ℝ) ≤ 32 * (n ^ 2 * (2 ^ j)⁻¹) := by
      rw [← div_eq_mul_inv, le_mul_iff_one_le_right (by norm_num), one_le_div hc]
      linarith
    calc 4 * Real.pi ^ 2 * (n ^ 2 * C₂ ^ 2 / (2 * 2 ^ j) + 32)
        ≤ 4 * Real.pi ^ 2 * (n ^ 2 * C₂ ^ 2 / (2 * 2 ^ j) + 32 * (n ^ 2 * (2 ^ j)⁻¹)) := by
          gcongr
      _ = _ := by field_simp
  have hhigh : ∫ t, ‖(x * (1 - f J)).snd t‖ ≤
      √(√(2 * Real.pi ^ 2 * C₁ ^ 2 * (C₁ ^ 2 + C₂ ^ 2))) * √n := by
    have hΛ : (0 : ℝ) < 2 ^ J := by positivity
    have hnΛ : (n : ℝ) ≤ 2 ^ J := by exact_mod_cast (Nat.lt_pow_succ_log_self one_lt_two n).le
    have h := integral_norm_snd_mul_high_pow_four_le hx hα hβ hxα hxβ hΛ
    refine le_of_pow_le_pow_left₀ four_ne_zero (by positivity) ?_
    rw [mul_pow, sqrt_sqrt_pow_four (by positivity), sqrt_pow_four]
    refine h.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h3 : (n : ℝ) ^ 3 ≤ (2 ^ J) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnΛ 3
    have hK : 0 ≤ 2 * Real.pi ^ 2 * C₁ ^ 2 * (C₁ ^ 2 + C₂ ^ 2) := by positivity
    calc 2 * Real.pi ^ 2 * (n ^ 2 * C₁ ^ 2) * (n ^ 2 * C₁ ^ 2 + n ^ 2 * C₂ ^ 2)
        = 2 * Real.pi ^ 2 * C₁ ^ 2 * (C₁ ^ 2 + C₂ ^ 2) * (n * n ^ 3) := by ring
      _ ≤ 2 * Real.pi ^ 2 * C₁ ^ 2 * (C₁ ^ 2 + C₂ ^ 2) * (n ^ 2 * (2 ^ J) ^ 3) := by
          gcongr
      _ = _ := by ring
  -- the dyadic sum
  have hgeom : ∑ j ∈ Finset.range J, dyadicRatio ^ j ≤ 1 / (1 - dyadicRatio) := by
    have := geom_sum_Ico_le_of_lt_one dyadicRatio_nonneg dyadicRatio_lt_one (m := 0) (n := J)
    rwa [pow_zero, ← Finset.range_eq_Ico] at this
  have h1ρ : 0 < 1 - dyadicRatio := by linarith [dyadicRatio_lt_one]
  calc ∫ t, ‖(x * f 0 + ∑ j ∈ Finset.range J, x * (f (j + 1) - f j) + x * (1 - f J)).snd t‖
      ≤ (∫ t, ‖(x * f 0).snd t‖) + (∑ j ∈ Finset.range J, ∫ t, ‖(x * (f (j + 1) - f j)).snd t‖) +
          ∫ t, ‖(x * (1 - f J)).snd t‖ := by
        refine (integral_norm_snd_add_le _ _).trans (add_le_add_left ?_ _)
        exact (integral_norm_snd_add_le _ _).trans (add_le_add_right
          (integral_norm_snd_sum_le _ _) _)
    _ ≤ √(√(8 * Real.pi ^ 2 * (C₂ ^ 2 + 4))) * √n +
          (∑ j ∈ Finset.range J, √(√(4 * Real.pi ^ 2 * (C₂ ^ 2 / 2 + 32))) * √n * dyadicRatio ^ j) +
          √(√(2 * Real.pi ^ 2 * C₁ ^ 2 * (C₁ ^ 2 + C₂ ^ 2))) * √n := by
        gcongr with j hj
        · exact hmid j hj
    _ = √(√(8 * Real.pi ^ 2 * (C₂ ^ 2 + 4))) * √n +
          √(√(4 * Real.pi ^ 2 * (C₂ ^ 2 / 2 + 32))) * √n *
            (∑ j ∈ Finset.range J, dyadicRatio ^ j) +
          √(√(2 * Real.pi ^ 2 * C₁ ^ 2 * (C₁ ^ 2 + C₂ ^ 2))) * √n := by
        rw [Finset.mul_sum]
    _ ≤ √(√(8 * Real.pi ^ 2 * (C₂ ^ 2 + 4))) * √n +
          √(√(4 * Real.pi ^ 2 * (C₂ ^ 2 / 2 + 32))) * √n * (1 / (1 - dyadicRatio)) +
          √(√(2 * Real.pi ^ 2 * C₁ ^ 2 * (C₁ ^ 2 + C₂ ^ 2))) * √n := by
        gcongr
    _ = powerConst C₁ C₂ * √n := by
        rw [powerConst]; field_simp

/-- If `|μ̂| ≤ 1`, `|μ̂(ξ) - a| ≤ C₁ |ν̂(ξ)|` and `|μ̂'(ξ)| ≤ 2π C₂ |ν̂(ξ)|²`, the total variation
of `μⁿ` is at most `1 + C √n`, `C = powerConst C₁ C₂`. -/
theorem variation_pow_le (μ : HalfLineAlgebra) (hσ : ∀ ξ, ‖fourier ξ μ‖ ≤ 1)
    {C₁ C₂ : ℝ} (h1 : ∀ ξ, ‖fourier ξ μ - μ.fst‖ ≤ C₁ * ‖fourier ξ resolvent‖)
    (h2 : ∀ ξ, ‖moment μ ξ‖ ≤ C₂ * ‖fourier ξ resolvent‖ ^ 2) (n : ℕ) :
    (μ ^ n).variation ≤ 1 + powerConst C₁ C₂ * √n := by
  have ha := norm_fst_le_one μ hσ h1
  rw [variation, show (μ ^ n).fst = μ.fst ^ n from map_pow (fstHom ℂ HalfLineKernel) μ n,
    norm_pow]
  exact add_le_add (pow_le_one₀ (norm_nonneg _) ha) (integral_norm_pow_snd_le μ hσ h1 h2 n)

end HalfLineAlgebra

end Feec
