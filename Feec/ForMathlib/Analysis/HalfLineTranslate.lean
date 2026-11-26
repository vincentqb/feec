module

public import Feec.ForMathlib.Analysis.HalfLineAlgebra
public import Feec.ForMathlib.Analysis.Fourier.GeomSumMultiplier

/-!
# Translations, the Taylor kernel, and Brenner–Thomée's error kernel

Translations `(δ_s ⋆ f)(t) = f(t - s)` of kernels on the half-line, the Taylor kernel
`eₚ(t) = (1 - t)ᵖ/p!` on `[0, 1]`, and the error kernel `kₙ = Σ_{j<n} δ_{n-1-j} ⋆ μʲ ⋆ h` of
[BrennerThomee1979], with `∫ |kₙ| ≤ K n` when `|μ̂| ≤ 1` and `z^{p+1} ĥ = μ̂ - e^z`
(`z = -2πiξ`).

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set Finset Filter FourierTransform Unitization
open scoped Real

@[expose] public noncomputable section

namespace Feec

theorem eq_sum_add_integral_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (p : ℕ) {f : ℕ → ℝ → F} (hc : ∀ j ≤ p + 1, ContinuousOn (f j) (Icc 0 1))
    (hd : ∀ j ≤ p, ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (f j) (f (j + 1) s) s) :
    f 0 1 = ∑ j ∈ range (p + 1), ((j.factorial : ℝ)⁻¹) • f j 0 +
      ∫ s in (0 : ℝ)..1, ((1 - s) ^ p / p.factorial) • f (p + 1) s := by
  induction p with
  | zero =>
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one (hc 0 (by omega))
      (fun s hs => hd 0 le_rfl s hs) ((hc 1 le_rfl).intervalIntegrable_of_Icc zero_le_one)
    simp [this]
  | succ p ih =>
    rw [ih (fun j hj => hc j (by omega)) (fun j hj => hd j (by omega)), sum_range_succ _ (p + 1),
      add_assoc]
    congr 1
    set c : ℝ → ℝ := fun s => (1 - s) ^ (p + 1) / (p + 1).factorial
    set φ : ℝ → F := fun s => c s • f (p + 1) s
    have hcd : ∀ s, HasDerivAt c (-((1 - s) ^ p / p.factorial)) s := fun s => by
      have h := (((hasDerivAt_id s).const_sub 1).pow (p + 1)).div_const ((p + 1).factorial : ℝ)
      convert h using 1
      · ext x; simp [c]
      · rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
        have : (p.factorial : ℝ) ≠ 0 := by positivity
        simp only [id]
        field_simp
    have hφd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt φ (c s • f (p + 2) s +
        (-((1 - s) ^ p / p.factorial)) • f (p + 1) s) s := fun s hs =>
      (hcd s).smul (hd (p + 1) le_rfl s hs)
    have hcont : ContinuousOn φ (Icc 0 1) :=
      (Continuous.continuousOn (by fun_prop)).smul (hc (p + 1) (by omega))
    have hi1 : IntervalIntegrable (fun s => c s • f (p + 2) s) volume 0 1 :=
      ((Continuous.continuousOn (by fun_prop)).smul (hc (p + 2) le_rfl)).intervalIntegrable_of_Icc
        zero_le_one
    have hi2 : IntervalIntegrable (fun s => (-((1 - s) ^ p / p.factorial : ℝ)) • f (p + 1) s)
        volume 0 1 :=
      ((Continuous.continuousOn (by fun_prop)).smul
        (hc (p + 1) (by omega))).intervalIntegrable_of_Icc zero_le_one
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hφd
      (hi1.add hi2)
    rw [intervalIntegral.integral_add hi1 hi2] at h
    simp only [φ, c, sub_self, ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, zero_div, zero_smul, sub_zero, one_pow, zero_sub, neg_smul,
      intervalIntegral.integral_neg] at h
    rw [one_div] at h
    linear_combination (norm := module) -h

namespace HalfLineKernel

/-- Translation by `s ≥ 0`, the action of `δ_s`: `(δ_s ⋆ f)(t) = f(t - s)`. -/
def translate (s : ℝ) (hs : 0 ≤ s) (f : HalfLineKernel) : HalfLineKernel where
  toFun t := f (t - s)
  memLp_one := f.memLp_one.comp_measurePreserving (measurePreserving_sub_right volume s)
  memLp_top := f.memLp_top.comp_measurePreserving (measurePreserving_sub_right volume s)
  memLp_one_smul := by
    have h := (f.memLp_one_smul.comp_measurePreserving (measurePreserving_sub_right volume s)).add
      ((f.memLp_one.comp_measurePreserving (measurePreserving_sub_right volume s)).const_smul
        (s : ℂ))
    refine h.ae_eq (ae_of_all _ fun t => ?_)
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast; ring
  memLp_top_smul := by
    have h := (f.memLp_top_smul.comp_measurePreserving (measurePreserving_sub_right volume s)).add
      ((f.memLp_top.comp_measurePreserving (measurePreserving_sub_right volume s)).const_smul
        (s : ℂ))
    refine h.ae_eq (ae_of_all _ fun t => ?_)
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast; ring
  eq_zero_of_neg t ht := f.eq_zero_of_neg _ (by linarith)

@[simp] theorem translate_apply {s : ℝ} (hs : 0 ≤ s) (f : HalfLineKernel) (t : ℝ) :
    translate s hs f t = f (t - s) := rfl

theorem fourier_comp_add_right (f : ℝ → ℂ) (c ξ : ℝ) :
    𝓕 (fun t => f (t + c)) ξ = Complex.exp (-(GeomSum.symb ξ * c)) * 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul]
  rw [← integral_sub_right_eq_self (fun v => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) •
    f (v + c)) c]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [smul_eq_mul, sub_add_cancel, GeomSum.symb, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

theorem fourier_translate {s : ℝ} (hs : 0 ≤ s) (f : HalfLineKernel) (ξ : ℝ) :
    𝓕 (translate s hs f : ℝ → ℂ) ξ = Complex.exp (GeomSum.symb ξ * s) * 𝓕 (f : ℝ → ℂ) ξ := by
  rw [show (translate s hs f : ℝ → ℂ) = fun t => f (t + -s) from funext fun t => by
    simp [sub_eq_add_neg], fourier_comp_add_right]
  congr 2
  push_cast; ring

theorem integral_norm_translate {s : ℝ} (hs : 0 ≤ s) (f : HalfLineKernel) :
    ∫ t, ‖translate s hs f t‖ = ∫ t, ‖f t‖ :=
  integral_sub_right_eq_self (fun t => ‖f t‖) s

/-- `(1 - t)ᵖ/p!` on `[0, 1]`, zero elsewhere. -/
def taylorFun (p : ℕ) : ℝ → ℂ :=
  indicator (Icc 0 1) fun t => (((1 - t) ^ p / p.factorial : ℝ) : ℂ)

theorem norm_taylorFun_le (p : ℕ) (t : ℝ) : ‖taylorFun p t‖ ≤ 1 := by
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · rw [taylorFun, indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by have := ht.2; positivity)]
    have h1 : (1 - t) ^ p ≤ 1 := pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])
    have h2 : (1 : ℝ) ≤ p.factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 p.factorial_ne_zero
    exact div_le_one_of_le₀ (h1.trans h2) (by positivity)
  · simp [taylorFun, indicator_of_notMem ht]

theorem norm_smul_taylorFun_le (p : ℕ) (t : ℝ) :
    ‖t • taylorFun p t‖ ≤ (Icc (0 : ℝ) 1).indicator 1 t := by
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem ht, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, Pi.one_apply]
    simpa using mul_le_mul ht.2 (norm_taylorFun_le p t) (norm_nonneg _) zero_le_one
  · simp [taylorFun, indicator_of_notMem ht]

theorem aestronglyMeasurable_taylorFun (p : ℕ) : AEStronglyMeasurable (taylorFun p) :=
  (Continuous.aestronglyMeasurable (by fun_prop)).indicator measurableSet_Icc

theorem integrable_indicator_Icc : Integrable ((Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
  (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))

/-- The Taylor kernel `eₚ(t) = (1 - t)ᵖ/p!` on `[0, 1]`. -/
def taylor (p : ℕ) : HalfLineKernel where
  toFun := taylorFun p
  memLp_one := memLp_one_iff_integrable.2 (integrable_indicator_Icc.mono'
    (aestronglyMeasurable_taylorFun p) (ae_of_all _ fun t => by
      by_cases ht : t ∈ Icc (0 : ℝ) 1
      · rw [indicator_of_mem ht, Pi.one_apply]; exact norm_taylorFun_le p t
      · simp [taylorFun, indicator_of_notMem ht]))
  memLp_top := memLp_top_of_bound (aestronglyMeasurable_taylorFun p) 1
    (ae_of_all _ (norm_taylorFun_le p))
  memLp_one_smul := memLp_one_iff_integrable.2 (integrable_indicator_Icc.mono'
    (continuous_id.aestronglyMeasurable.smul (aestronglyMeasurable_taylorFun p))
    (ae_of_all _ (norm_smul_taylorFun_le p)))
  memLp_top_smul := memLp_top_of_bound
    (continuous_id.aestronglyMeasurable.smul (aestronglyMeasurable_taylorFun p)) 1
    (ae_of_all _ fun t => (norm_smul_taylorFun_le p t).trans (by
      by_cases ht : t ∈ Icc (0 : ℝ) 1
      · rw [indicator_of_mem ht]; rfl
      · rw [indicator_of_notMem ht]; norm_num))
  eq_zero_of_neg t ht := indicator_of_notMem (fun h => by linarith [h.1]) _

theorem taylor_apply (p : ℕ) (t : ℝ) : taylor p t = taylorFun p t := rfl

theorem integral_smul_taylor {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (p : ℕ)
    (g : ℝ → F) :
    ∫ t, taylor p t • g t = ∫ s in (0 : ℝ)..1, ((1 - s) ^ p / p.factorial : ℝ) • g s := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · simp only [taylor_apply, taylorFun, indicator_of_mem ht, Complex.coe_smul]
  · simp [taylor_apply, taylorFun, indicator_of_notMem ht]

theorem symb_pow_mul_fourier_taylor (p : ℕ) (ξ : ℝ) :
    GeomSum.symb ξ ^ (p + 1) * 𝓕 (taylor p : ℝ → ℂ) ξ =
      Complex.exp (GeomSum.symb ξ) -
        ∑ j ∈ range (p + 1), GeomSum.symb ξ ^ j / j.factorial := by
  set z := GeomSum.symb ξ
  have hF : 𝓕 (taylor p : ℝ → ℂ) ξ = ∫ t, taylor p t • Complex.exp (z * t) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [smul_eq_mul, z, GeomSum.symb]
    rw [mul_comm]; congr 2; push_cast; ring
  have key := eq_sum_add_integral_of_hasDerivAt (F := ℂ) p
    (f := fun j s => z ^ j * Complex.exp (z * s))
    (fun j _ => Continuous.continuousOn (by fun_prop)) (fun j _ s _ => by
      have := ((((hasDerivAt_id' s).ofReal_comp).const_mul z).cexp).const_mul (z ^ j)
      convert this using 1
      push_cast; ring)
  rw [hF, integral_smul_taylor, ← intervalIntegral.integral_const_mul]
  simp only [mul_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one, Complex.ofReal_one,
    pow_zero, one_mul] at key
  rw [key]
  rw [show (∑ j ∈ range (p + 1), ((j.factorial : ℝ)⁻¹) • z ^ j) =
    ∑ j ∈ range (p + 1), z ^ j / j.factorial from sum_congr rfl fun j _ => by
      rw [Complex.real_smul, div_eq_inv_mul]; push_cast; ring]
  simp only [add_sub_cancel_left]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [Complex.real_smul]
  ring

end HalfLineKernel

namespace HalfLineAlgebra

/-- Brenner–Thomée's error kernel `kₙ = Σ_{j<n} δ_{n-1-j} ⋆ μʲ ⋆ h`. -/
def errorKernel (μ : HalfLineAlgebra) (h : HalfLineKernel) (n : ℕ) : HalfLineKernel :=
  ∑ j ∈ range n, HalfLineKernel.translate ((n - 1 - j : ℕ) : ℝ) (Nat.cast_nonneg _)
    (μ ^ j * inr h).snd

theorem fourier_snd_mul_inr (μ : HalfLineAlgebra) (h : HalfLineKernel) (ξ : ℝ) :
    𝓕 ((μ * inr h).snd : ℝ → ℂ) ξ = fourier ξ μ * 𝓕 (h : ℝ → ℂ) ξ := by
  have e := map_mul (fourier ξ) μ (inr h)
  rw [fourier_apply, fourier_apply, fourier_apply] at e
  rw [fourier_apply ξ μ]
  simpa using e

theorem coe_sum (s : Finset ℕ) (f : ℕ → HalfLineKernel) :
    ((∑ j ∈ s, f j : HalfLineKernel) : ℝ → ℂ) = ∑ j ∈ s, (f j : ℝ → ℂ) :=
  map_sum (⟨⟨fun f : HalfLineKernel => (f : ℝ → ℂ), rfl⟩, fun _ _ => rfl⟩ :
    HalfLineKernel →+ (ℝ → ℂ)) f s

theorem fourier_errorKernel (μ : HalfLineAlgebra) (h : HalfLineKernel) (n : ℕ) (ξ : ℝ) :
    𝓕 (errorKernel μ h n : ℝ → ℂ) ξ = ∑ j ∈ range n,
      Complex.exp (GeomSum.symb ξ * (n - 1 - j : ℕ)) * (fourier ξ μ ^ j * 𝓕 (h : ℝ → ℂ) ξ) := by
  have e : (errorKernel μ h n : ℝ → ℂ) = ∑ j ∈ range n,
      (HalfLineKernel.translate ((n - 1 - j : ℕ) : ℝ) (Nat.cast_nonneg _) (μ ^ j * inr h).snd :
        ℝ → ℂ) := coe_sum _ _
  have hfc : ∀ f : HalfLineKernel, 𝓕 (f : ℝ → ℂ) ξ = HalfLineKernel.fourierChar ξ f :=
    fun _ => rfl
  rw [hfc, errorKernel, map_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [← hfc, HalfLineKernel.fourier_translate, fourier_snd_mul_inr, map_pow,
    Complex.ofReal_natCast]

theorem memLp_comp_add (f : HalfLineKernel) (c : ℝ) :
    Integrable (fun t => f (t + c)) ∧ MemLp (fun t => f (t + c)) 2 ∧
      Integrable (fun t : ℝ => t • f (t + c)) ∧ MemLp (fun t : ℝ => t • f (t + c)) 2 := by
  have hm := measurePreserving_add_right (volume : Measure ℝ) c
  have e : (fun t : ℝ => t • f (t + c)) =
      (fun t : ℝ => (t + c) • f (t + c)) - (c : ℂ) • fun t => f (t + c) := by
    ext t; simp only [Pi.sub_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast; ring
  have h1 : Integrable fun t => f (t + c) :=
    memLp_one_iff_integrable.1 (f.memLp_one.comp_measurePreserving hm)
  have h2 : MemLp (fun t => f (t + c)) 2 := f.memLp_two.comp_measurePreserving hm
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [e]
    exact (memLp_one_iff_integrable.1 (f.memLp_one_smul.comp_measurePreserving hm)).sub
      (h1.smul (c : ℂ))
  · rw [e]; exact (f.memLp_two_smul.comp_measurePreserving hm).sub (h2.const_smul _)

/-- The constant `K = geomSumConst p W₀ W₁ Q₁` of the error kernel bound. -/
def errorConst (μ : HalfLineAlgebra) (h : HalfLineKernel) (p : ℕ) : ℝ :=
  geomSumConst p (∫ t, ‖h t‖) (2 * π * ((∫ t, ‖h t‖) + ∫ t, ‖t • h t‖))
    (2 * π * (1 + ∫ t, ‖t • μ.snd t‖))

theorem norm_fourier_smul_le (f : HalfLineKernel) (ξ : ℝ) :
    ‖𝓕 (fun t : ℝ => (-2 * π * Complex.I * t) • f t) ξ‖ ≤ 2 * π * ∫ t, ‖t • f t‖ := by
  refine (Real.norm_fourier_le_integral_norm _ _).trans_eq ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [norm_smul, norm_neg, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, abs_of_pos Real.pi_pos, smul_eq_mul,
    norm_mul]
  ring

/-- If `|μ̂| ≤ 1` and `z^{p+1} ĥ = μ̂ - e^z`, then `∫ |kₙ| ≤ K n`, `K = errorConst μ h p`
([BrennerThomee1979]). -/
theorem integral_norm_errorKernel_le (μ : HalfLineAlgebra) (hσ : ∀ ξ, ‖fourier ξ μ‖ ≤ 1)
    (h : HalfLineKernel) {p : ℕ}
    (hh : ∀ ξ, GeomSum.symb ξ ^ (p + 1) * 𝓕 (h : ℝ → ℂ) ξ =
      fourier ξ μ - Complex.exp (GeomSum.symb ξ)) (n : ℕ) :
    ∫ t, ‖errorKernel μ h n t‖ ≤ errorConst μ h p * n := by
  set k := errorKernel μ h n
  obtain ⟨h1, h2, h3, h4⟩ := memLp_comp_add k n
  rw [← integral_add_right_eq_self (fun t => ‖k t‖) (n : ℝ)]
  set e : ℝ → ℂ := fun ξ => Complex.exp (-GeomSum.symb ξ)
  have he : ∀ ξ, ‖e ξ‖ = 1 := fun ξ => by
    simp [e, GeomSum.symb, Complex.norm_exp]
  have hed : ∀ ξ, HasDerivAt e (2 * π * Complex.I * e ξ) ξ := fun ξ => by
    have := (GeomSum.hasDerivAt_symb ξ).neg.cexp
    convert this using 1; simp [e]; ring
  set g := μ.snd
  have hg := Real.hasDerivAt_fourier g.integrable g.integrable_smul
  have hhd := Real.hasDerivAt_fourier h.integrable h.integrable_smul
  set w : ℝ → ℂ := fun ξ => e ξ * 𝓕 (h : ℝ → ℂ) ξ
  set q : ℝ → ℂ := fun ξ => e ξ * fourier ξ μ
  have hfμ : ∀ ξ, fourier ξ μ = μ.fst + 𝓕 (g : ℝ → ℂ) ξ := fun ξ => fourier_apply ξ μ
  refine MeasureTheory.Integrable.integral_norm_le_of_fourier_eq_geom_sum h1 h2 h3 h4
    (w := w) (q := q) (p := p)
    (w' := fun ξ => 2 * π * Complex.I * e ξ * 𝓕 (h : ℝ → ℂ) ξ +
      e ξ * 𝓕 (fun t : ℝ => (-2 * π * Complex.I * t) • h t) ξ)
    (q' := fun ξ => 2 * π * Complex.I * e ξ * fourier ξ μ +
      e ξ * 𝓕 (fun t : ℝ => (-2 * π * Complex.I * t) • g t) ξ)
    (fun ξ => (hed ξ).mul (hhd ξ))
    (fun ξ => by
      have := (hed ξ).mul ((hg ξ).const_add μ.fst)
      convert this using 1
      · ext x; simp [q, hfμ]
      · simp [hfμ])
    (fun ξ => by simp only [q, norm_mul, he, one_mul]; exact hσ ξ)
    (fun ξ => by
      simp only [q, w]
      have : e ξ * Complex.exp (GeomSum.symb ξ) = 1 := by
        simp only [e, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
      linear_combination (-e ξ) * hh ξ + this)
    (fun ξ => by
      simp only [w, norm_mul, he, one_mul]; exact Real.norm_fourier_le_integral_norm _ _)
    (fun ξ => by
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul, he, mul_one, one_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I]
      have := Real.norm_fourier_le_integral_norm (h : ℝ → ℂ) ξ
      have := norm_fourier_smul_le h ξ
      nlinarith [Real.pi_pos])
    (fun ξ => by
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul, he, mul_one, one_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I]
      have := hσ ξ
      have := norm_fourier_smul_le g ξ
      nlinarith [Real.pi_pos])
    (fun ξ => ?_)
  rw [HalfLineKernel.fourier_comp_add_right, fourier_errorKernel, mul_sum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < n := mem_range.1 hj
  simp only [w, q, mul_pow]
  have : Complex.exp (-(GeomSum.symb ξ * n)) * Complex.exp (GeomSum.symb ξ * (n - 1 - j : ℕ)) =
      e ξ * e ξ ^ j := by
    simp only [e, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  linear_combination (fourier ξ μ ^ j * 𝓕 (h : ℝ → ℂ) ξ) * this

end HalfLineAlgebra

end Feec
