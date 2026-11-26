module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Feec.ForMathlib.Analysis.Carlson
public import Feec.ForMathlib.Analysis.Fourier.Plancherel

/-!
# The convolution algebra of the half-line

Kernels on the half-line, `g : ℝ → ℂ` vanishing on `(-∞, 0)` with `g` and `t g` in `L¹ ∩ L^∞`, form
a commutative non-unital `ℂ`-algebra under convolution; its unitization `Feec.HalfLineAlgebra`,
the measures `a δ₀ + g(t) dt` on `[0, ∞)`, carries the Fourier–Stieltjes characters and the total
variation.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set Filter ContinuousLinearMap FourierTransform
open scoped Convolution ENNReal

@[expose] public noncomputable section

namespace Feec

/-! ### Convolution of `L¹` and `L^∞` functions on `ℝ` -/

section Conv

variable {𝕜 E E' F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup E'] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜 F] [NormedSpace ℝ F] (L : E →L[𝕜] E' →L[𝕜] F) {f : ℝ → E} {g : ℝ → E'}

omit [NormedSpace ℝ F] in
theorem convolutionExists_of_memLp (hf : MemLp f 1) (hg : MemLp g ⊤) : ConvolutionExists f g L :=
  ConvolutionExists.of_memLp_memLp L hf hg

theorem memLp_top_convolution (hf : MemLp f 1) (hg : MemLp g ⊤) : MemLp (f ⋆[L] g) ⊤ := by
  refine memLp_top_of_bound (hf.aestronglyMeasurable.convolution L hg.aestronglyMeasurable)
    (‖L‖ₑ * eLpNorm f 1 volume * eLpNorm g ⊤ volume).toReal (Eventually.of_forall fun x => ?_)
  rw [← toReal_enorm]
  exact ENNReal.toReal_mono (by finiteness [hf.eLpNorm_ne_top, hg.eLpNorm_ne_top])
    (enorm_convolution_le L hf.aestronglyMeasurable hg.aestronglyMeasurable x)

theorem memLp_one_convolution (hf : MemLp f 1) (hg : MemLp g 1) : MemLp (f ⋆[L] g) 1 :=
  memLp_one_iff_integrable.2 ((memLp_one_iff_integrable.1 hf).integrable_convolution L
    (memLp_one_iff_integrable.1 hg))

theorem convolution_eq_zero_of_neg (hf : ∀ t < 0, f t = 0) (hg : ∀ t < 0, g t = 0) {x : ℝ}
    (hx : x < 0) : (f ⋆[L] g) x = 0 := by
  rw [convolution_def]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  rcases lt_or_ge t 0 with ht | ht
  · simp [hf t ht]
  · simp [hg (x - t) (by linarith)]

end Conv

theorem smul_convolution_apply {f g : ℝ → ℂ} {x : ℝ}
    (h1 : ConvolutionExistsAt (fun t : ℝ => t • f t) g x (mul ℂ ℂ))
    (h2 : ConvolutionExistsAt f (fun t : ℝ => t • g t) x (mul ℂ ℂ)) :
    x • (f ⋆[mul ℂ ℂ] g) x =
      ((fun t : ℝ => t • f t) ⋆[mul ℂ ℂ] g) x + (f ⋆[mul ℂ ℂ] fun t : ℝ => t • g t) x := by
  simp only [convolution_def]
  rw [← integral_add h1 h2, ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [mul_apply', Complex.real_smul]
  push_cast
  ring

/-! ### Kernels on the half-line -/

/-- A kernel on the half-line: `g : ℝ → ℂ` vanishing on `(-∞, 0)`, with `g`, `t g` in `L¹ ∩ L^∞`. -/
structure HalfLineKernel where
  /-- the kernel as a function -/
  toFun : ℝ → ℂ
  memLp_one : MemLp toFun 1
  memLp_top : MemLp toFun ⊤
  memLp_one_smul : MemLp (fun t : ℝ => t • toFun t) 1
  memLp_top_smul : MemLp (fun t : ℝ => t • toFun t) ⊤
  eq_zero_of_neg : ∀ t < 0, toFun t = 0

namespace HalfLineKernel

instance : CoeFun HalfLineKernel fun _ => ℝ → ℂ := ⟨toFun⟩

@[ext] theorem ext {f g : HalfLineKernel} (h : ∀ t, f t = g t) : f = g := by
  cases f; cases g; congr; funext t; exact h t

theorem coe_injective : Function.Injective fun f : HalfLineKernel => (f : ℝ → ℂ) :=
  fun _ _ h => ext fun t => congrFun h t

theorem integrable (f : HalfLineKernel) : Integrable f := memLp_one_iff_integrable.1 f.memLp_one

theorem integrable_smul (f : HalfLineKernel) : Integrable fun t : ℝ => t • f t :=
  memLp_one_iff_integrable.1 f.memLp_one_smul

theorem _root_.MeasureTheory.MemLp.memLp_two_of_one_top {g : ℝ → ℂ} (h1 : MemLp g 1)
    (h2 : MemLp g ⊤) : MemLp g 2 := by
  have hC : ∀ᵐ t, ‖g t‖ ≤ (eLpNorm g ⊤ volume).toReal := by
    filter_upwards [ae_le_eLpNormEssSup (μ := volume) (f := g)] with t ht
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono h2.eLpNorm_ne_top (by rw [eLpNorm_exponent_top] <;> first | exact ht | exact h1.aestronglyMeasurable)
  refine (memLp_two_iff_integrable_sq_norm h1.aestronglyMeasurable).2
    (((memLp_one_iff_integrable.1 h1).norm.const_mul (eLpNorm g ⊤ volume).toReal).mono'
      (h1.aestronglyMeasurable.norm.pow 2) ?_)
  filter_upwards [hC] with t ht
  rw [Real.norm_of_nonneg (by positivity), sq]
  exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)

theorem memLp_two (f : HalfLineKernel) : MemLp f 2 := f.memLp_one.memLp_two_of_one_top f.memLp_top

theorem memLp_two_smul (f : HalfLineKernel) : MemLp (fun t : ℝ => t • f t) 2 :=
  f.memLp_one_smul.memLp_two_of_one_top f.memLp_top_smul

instance : Zero HalfLineKernel where
  zero := ⟨0, MemLp.zero, MemLp.zero, by simp, by simp, fun _ _ => rfl⟩

instance : Add HalfLineKernel where
  add f g := ⟨f + g, f.memLp_one.add g.memLp_one, f.memLp_top.add g.memLp_top,
    (f.memLp_one_smul.add g.memLp_one_smul).ae_eq (ae_of_all _ fun t => by simp [smul_add]),
    (f.memLp_top_smul.add g.memLp_top_smul).ae_eq (ae_of_all _ fun t => by simp [smul_add]),
    fun t ht => by simp [f.eq_zero_of_neg t ht, g.eq_zero_of_neg t ht]⟩

instance : SMul ℂ HalfLineKernel where
  smul c f := ⟨c • (f : ℝ → ℂ), f.memLp_one.const_smul c, f.memLp_top.const_smul c,
    (f.memLp_one_smul.const_smul c).ae_eq (ae_of_all _ fun t => by simp; ring),
    (f.memLp_top_smul.const_smul c).ae_eq (ae_of_all _ fun t => by simp; ring),
    fun t ht => by simp [f.eq_zero_of_neg t ht]⟩

instance : Neg HalfLineKernel where neg f := (-1 : ℂ) • f

instance : Sub HalfLineKernel where sub f g := f + -g

instance : SMul ℕ HalfLineKernel where smul n f := (n : ℂ) • f

instance : SMul ℤ HalfLineKernel where smul n f := (n : ℂ) • f

@[simp] theorem coe_zero : ((0 : HalfLineKernel) : ℝ → ℂ) = 0 := rfl
@[simp] theorem coe_add (f g : HalfLineKernel) : ((f + g : HalfLineKernel) : ℝ → ℂ) = f + g := rfl
@[simp] theorem coe_smul (c : ℂ) (f : HalfLineKernel) :
    ((c • f : HalfLineKernel) : ℝ → ℂ) = c • (f : ℝ → ℂ) := rfl
@[simp] theorem coe_neg (f : HalfLineKernel) : ((-f : HalfLineKernel) : ℝ → ℂ) = -f := by
  change (-1 : ℂ) • (f : ℝ → ℂ) = _; simp
@[simp] theorem coe_sub (f g : HalfLineKernel) : ((f - g : HalfLineKernel) : ℝ → ℂ) = f - g := by
  change (f : ℝ → ℂ) + ((-g : HalfLineKernel) : ℝ → ℂ) = _; simp [sub_eq_add_neg]
@[simp] theorem coe_nsmul (n : ℕ) (f : HalfLineKernel) :
    ((n • f : HalfLineKernel) : ℝ → ℂ) = n • (f : ℝ → ℂ) := by
  change (n : ℂ) • (f : ℝ → ℂ) = _; ext; simp
@[simp] theorem coe_zsmul (n : ℤ) (f : HalfLineKernel) :
    ((n • f : HalfLineKernel) : ℝ → ℂ) = n • (f : ℝ → ℂ) := by
  change (n : ℂ) • (f : ℝ → ℂ) = _; ext; simp

instance : AddCommGroup HalfLineKernel :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    (fun _ _ => coe_zsmul _ _)

instance : Module ℂ HalfLineKernel :=
  coe_injective.module ℂ ⟨⟨fun f : HalfLineKernel => (f : ℝ → ℂ), coe_zero⟩, coe_add⟩ coe_smul

/-- Convolution of functions `ℝ → ℂ`. -/
abbrev conv (f g : ℝ → ℂ) : ℝ → ℂ := f ⋆[mul ℂ ℂ] g

theorem convolutionExists (f g : HalfLineKernel) : ConvolutionExists f g (mul ℂ ℂ) :=
  convolutionExists_of_memLp _ f.memLp_one g.memLp_top

theorem smul_conv (f g : HalfLineKernel) :
    (fun x : ℝ => x • conv f g x) = conv (fun t : ℝ => t • f t) g + conv f fun t : ℝ => t • g t :=
  funext fun x => smul_convolution_apply
    (convolutionExists_of_memLp _ f.memLp_one_smul g.memLp_top x)
    (convolutionExists_of_memLp _ f.memLp_one g.memLp_top_smul x)

theorem memLp_one_smul_conv (f g : HalfLineKernel) :
    MemLp (fun x : ℝ => x • conv f g x) 1 := by
  rw [smul_conv]
  exact (memLp_one_convolution _ f.memLp_one_smul g.memLp_one).add
    (memLp_one_convolution _ f.memLp_one g.memLp_one_smul)

theorem memLp_top_smul_conv (f g : HalfLineKernel) :
    MemLp (fun x : ℝ => x • conv f g x) ⊤ := by
  rw [smul_conv]
  exact (memLp_top_convolution _ f.memLp_one_smul g.memLp_top).add
    (memLp_top_convolution _ f.memLp_one g.memLp_top_smul)

instance : Mul HalfLineKernel where
  mul f g := ⟨conv f g, memLp_one_convolution _ f.memLp_one g.memLp_one,
    memLp_top_convolution _ f.memLp_one g.memLp_top, memLp_one_smul_conv f g,
    memLp_top_smul_conv f g, fun _ hx => convolution_eq_zero_of_neg _ f.eq_zero_of_neg g.eq_zero_of_neg hx⟩

@[simp] theorem coe_mul (f g : HalfLineKernel) :
    ((f * g : HalfLineKernel) : ℝ → ℂ) = conv f g := rfl

theorem conv_comm (f g : ℝ → ℂ) : conv f g = conv g f :=
  convolution_symm _ (ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => by
    simp only [flip_apply, mul_apply']; ring)

theorem conv_assoc (f g k : HalfLineKernel) : conv (conv f g) k = conv f (conv g k) := by
  ext x₀
  refine convolution_assoc (mul ℂ ℂ) (mul ℂ ℂ) (mul ℂ ℂ) (mul ℂ ℂ) (fun x y z => mul_assoc x y z)
    f.memLp_one.aestronglyMeasurable g.memLp_one.aestronglyMeasurable
    k.memLp_one.aestronglyMeasurable (Eventually.of_forall fun y => convolutionExists f g y)
    (Eventually.of_forall fun y =>
      convolutionExists_of_memLp _ g.memLp_one.norm k.memLp_top.norm y)
    (convolutionExists_of_memLp _ f.memLp_one.norm
      (memLp_top_convolution _ g.memLp_one.norm k.memLp_top.norm) x₀)

instance : NonUnitalCommRing HalfLineKernel where
  left_distrib f g k := ext fun x => (convolutionExists f g x).distrib_add (convolutionExists f k x)
  right_distrib f g k := ext fun x =>
    (convolutionExists f k x).add_distrib (convolutionExists g k x)
  zero_mul f := ext fun x => by simp
  mul_zero f := ext fun x => by simp
  mul_assoc f g k := ext fun x => congrFun (conv_assoc f g k) x
  mul_comm f g := ext fun x => congrFun (conv_comm f g) x

instance : IsScalarTower ℂ HalfLineKernel HalfLineKernel where
  smul_assoc c f g := ext fun x => by
    change conv (c • (f : ℝ → ℂ)) g x = c • conv f g x
    simp only [conv, smul_convolution]; rfl

instance : SMulCommClass ℂ HalfLineKernel HalfLineKernel where
  smul_comm c f g := ext fun x => by
    change c • conv f g x = conv f (c • (g : ℝ → ℂ)) x
    simp only [conv, convolution_smul]; rfl

/-- The Fourier transform at `ξ`, a character of the kernel algebra. -/
def fourierChar (ξ : ℝ) : HalfLineKernel →ₙₐ[ℂ] ℂ where
  toFun f := 𝓕 (f : ℝ → ℂ) ξ
  map_smul' c f := congrFun (VectorFourier.fourierIntegral_const_smul _ _ _ (f : ℝ → ℂ) c) ξ
  map_zero' := by simp [Real.fourier_eq]
  map_add' f g := congrFun (VectorFourier.fourierIntegral_add Real.continuous_fourierChar
    continuous_inner f.integrable g.integrable) ξ
  map_mul' f g := Real.fourier_mul_convolution_eq f.integrable g.integrable ξ

@[simp] theorem fourierChar_apply (ξ : ℝ) (f : HalfLineKernel) :
    fourierChar ξ f = 𝓕 (f : ℝ → ℂ) ξ := rfl

/-! #### Exponential kernels -/

theorem mul_exp_neg_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    t * Real.exp (-(c * t)) ≤ 2 / c * Real.exp (-(c / 2 * t)) := by
  have h1 : c / 2 * t ≤ Real.exp (c / 2 * t) := (Real.add_one_le_exp _).trans' (by linarith)
  have h2 : Real.exp (-(c * t)) = Real.exp (-(c / 2 * t)) * Real.exp (-(c / 2 * t)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (-(c / 2 * t)) * Real.exp (c / 2 * t) = 1 := by
    rw [← Real.exp_add]; simp
  rw [h2, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  calc t * Real.exp (-(c / 2 * t)) = 2 / c * (c / 2 * t) * Real.exp (-(c / 2 * t)) := by
        field_simp
    _ ≤ 2 / c * Real.exp (c / 2 * t) * Real.exp (-(c / 2 * t)) := by gcongr
    _ = 2 / c := by rw [mul_assoc, mul_comm (Real.exp _), h3, mul_one]

/-- The function `t ↦ e^{-ζt}` on `(0, ∞)`, zero elsewhere. -/
def expFun (ζ : ℂ) : ℝ → ℂ := indicator (Ioi 0) fun t => Complex.exp (-ζ * t)

theorem norm_expFun_le {ζ : ℂ} (hζ : 0 < ζ.re) (t : ℝ) : ‖expFun ζ t‖ ≤ 1 := by
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [expFun, indicator_of_mem ht, Complex.norm_exp]
    simpa using mul_nonneg hζ.le (le_of_lt ht)
  · simp [expFun, indicator_of_notMem ht]

theorem norm_smul_expFun_le {ζ : ℂ} (hζ : 0 < ζ.re) (t : ℝ) :
    ‖t • expFun ζ t‖ ≤ (Ioi (0 : ℝ)).indicator (fun t => 2 / ζ.re * Real.exp (-(ζ.re / 2) * t)) t := by
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [expFun, indicator_of_mem ht, indicator_of_mem ht, norm_smul, Complex.norm_exp,
      Real.norm_of_nonneg (le_of_lt ht)]
    simpa [neg_mul] using mul_exp_neg_le hζ t
  · simp [expFun, indicator_of_notMem ht]

theorem aestronglyMeasurable_expFun (ζ : ℂ) : AEStronglyMeasurable (expFun ζ) :=
  (Continuous.aestronglyMeasurable (by fun_prop)).indicator measurableSet_Ioi

theorem integrable_expFun {ζ : ℂ} (hζ : 0 < ζ.re) : Integrable (expFun ζ) :=
  (integrable_indicator_iff measurableSet_Ioi).2
    (integrableOn_exp_mul_complex_Ioi (by simpa using hζ) 0)

/-- The exponential kernel `e_ζ(t) = e^{-ζt}` (`t > 0`), for `re ζ > 0`. -/
def exp (ζ : ℂ) (hζ : 0 < ζ.re) : HalfLineKernel where
  toFun := expFun ζ
  memLp_one := memLp_one_iff_integrable.2 (integrable_expFun hζ)
  memLp_top := memLp_top_of_bound (aestronglyMeasurable_expFun ζ) 1
    (ae_of_all _ (norm_expFun_le hζ))
  memLp_one_smul := by
    refine memLp_one_iff_integrable.2 (Integrable.mono' ?_
      (continuous_id.aestronglyMeasurable.smul (aestronglyMeasurable_expFun ζ))
      (ae_of_all _ (norm_smul_expFun_le hζ)))
    exact (integrable_indicator_iff measurableSet_Ioi).2
      ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _)
  memLp_top_smul := memLp_top_of_bound
    (continuous_id.aestronglyMeasurable.smul (aestronglyMeasurable_expFun ζ)) (2 / ζ.re)
    (ae_of_all _ fun t => (norm_smul_expFun_le hζ t).trans (by
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem ht]
        refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
        have := mul_nonneg hζ.le (le_of_lt ht)
        nlinarith
      · rw [indicator_of_notMem ht]; positivity))
  eq_zero_of_neg t ht := indicator_of_notMem (notMem_Ioi.2 ht.le) _

@[simp] theorem coe_exp {ζ : ℂ} (hζ : 0 < ζ.re) : (exp ζ hζ : ℝ → ℂ) = expFun ζ := rfl

theorem fourier_expFun {ζ : ℂ} (hζ : 0 < ζ.re) (ξ : ℝ) :
    𝓕 (expFun ζ) ξ = (ζ + 2 * Real.pi * ξ * Complex.I)⁻¹ := by
  have ha : (-(ζ + 2 * Real.pi * ξ * Complex.I)).re < 0 := by simpa using hζ
  rw [Real.fourier_real_eq_integral_exp_smul]
  have : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) • expFun ζ v) =
      (Ioi 0).indicator fun v : ℝ => Complex.exp (-(ζ + 2 * Real.pi * ξ * Complex.I) * v) := by
    ext v
    by_cases hv : v ∈ Ioi (0 : ℝ)
    · rw [expFun, indicator_of_mem hv, indicator_of_mem hv, smul_eq_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    · simp [expFun, indicator_of_notMem hv]
  rw [this, integral_indicator measurableSet_Ioi, integral_exp_mul_complex_Ioi ha]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [div_neg, neg_div, neg_neg, one_div]

theorem sub_smul_conv_expFun {η ζ : ℂ} :
    (ζ - η) • conv (expFun η) (expFun ζ) = expFun η - expFun ζ := by
  ext x
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, conv, convolution_def, mul_apply']
  rcases le_or_gt x 0 with hx | hx
  · have h0 : ∀ t, expFun η t * expFun ζ (x - t) = 0 := fun t => by
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · rw [expFun, expFun, indicator_of_notMem (show x - t ∉ Ioi 0 by
          simp only [mem_Ioi, not_lt]; linarith [mem_Ioi.1 ht]), mul_zero]
      · rw [expFun, indicator_of_notMem ht, zero_mul]
    simp only [h0, integral_zero, mul_zero]
    simp [expFun, indicator_of_notMem (notMem_Ioi.2 hx)]
  · set φ : ℝ → ℂ := fun t => Complex.exp (-η * t) * Complex.exp (-ζ * (x - t))
    have h1 : (fun t => expFun η t * expFun ζ (x - t)) = (Ioo 0 x).indicator φ := by
      ext t
      by_cases ht : t ∈ Ioo 0 x
      · rw [indicator_of_mem ht, expFun, expFun, indicator_of_mem (mem_Ioi.2 ht.1),
          indicator_of_mem (mem_Ioi.2 (sub_pos.2 ht.2))]
        simp [φ]
      · rw [indicator_of_notMem ht]
        rcases le_or_gt t 0 with h | h
        · rw [expFun, indicator_of_notMem (notMem_Ioi.2 h), zero_mul]
        · rw [show expFun ζ (x - t) = 0 from indicator_of_notMem (show x - t ∉ Ioi 0 by
            simp only [mem_Ioi, sub_pos, not_lt]; exact not_lt.1 fun h' => ht ⟨h, h'⟩) _,
            mul_zero]
    have hd : ∀ t ∈ uIcc 0 x, HasDerivAt φ ((ζ - η) * φ t) t := fun t _ => by
      have := (((hasDerivAt_id (t : ℂ)).const_mul (-η)).cexp.mul
        (((hasDerivAt_id (t : ℂ)).const_sub (x : ℂ)).const_mul (-ζ)).cexp).comp_ofReal
      convert this using 1 <;> simp [φ]; ring
    rw [h1, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← integral_const_mul,
      ← intervalIntegral.integral_of_le hx.le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((Continuous.intervalIntegrable (by fun_prop) _ _))]
    simp [φ, expFun, indicator_of_mem (mem_Ioi.2 hx)]

theorem exp_one_mul_exp {s : ℂ} (hs : s ≠ 0) (hζ : 0 < (1 - s⁻¹).re) :
    exp 1 (by simp) * exp (1 - s⁻¹) hζ = s • (exp (1 - s⁻¹) hζ - exp 1 (by simp)) := by
  have h := sub_smul_conv_expFun (η := 1) (ζ := 1 - s⁻¹)
  ext t
  have ht := congrFun h t
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_sub_cancel_left] at ht
  simp only [coe_mul, coe_exp, coe_smul, coe_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [show expFun (1 - s⁻¹) t - expFun 1 t = -(expFun 1 t - expFun (1 - s⁻¹) t) by ring, ← ht]
  field_simp

end HalfLineKernel

/-! ### The half-line algebra -/

/-- The half-line algebra `ℂ ⊕ K`: the measures `a δ₀ + g(t) dt` on `[0, ∞)` under convolution. -/
abbrev HalfLineAlgebra := Unitization ℂ HalfLineKernel

namespace HalfLineAlgebra

open Unitization

/-- The Fourier–Stieltjes transform `a δ₀ + g ↦ a + 𝓕 g (ξ)`, a character. -/
def fourier (ξ : ℝ) : HalfLineAlgebra →ₐ[ℂ] ℂ := lift (HalfLineKernel.fourierChar ξ)

theorem fourier_apply (ξ : ℝ) (μ : HalfLineAlgebra) :
    fourier ξ μ = μ.fst + 𝓕 (μ.snd : ℝ → ℂ) ξ := by
  simp [fourier]

/-- The total variation `|a| + ∫ |g|` of `a δ₀ + g`. -/
def variation (μ : HalfLineAlgebra) : ℝ := ‖μ.fst‖ + ∫ t, ‖μ.snd t‖

/-- The resolvent measure `ν = e^{-t} dt`, with Fourier–Stieltjes transform `1/(1 + 2πiξ)`. -/
def resolvent : HalfLineAlgebra := inr (HalfLineKernel.exp 1 (by simp))

theorem fourier_resolvent (ξ : ℝ) :
    fourier ξ resolvent = (1 + 2 * Real.pi * ξ * Complex.I)⁻¹ := by
  simp [fourier_apply, resolvent, HalfLineKernel.fourier_expFun]

theorem isUnit_algebraMap_sub_resolvent {s : ℂ} (hs : s ≠ 0) (hζ : 0 < (1 - s⁻¹).re) :
    IsUnit (algebraMap ℂ HalfLineAlgebra s - resolvent) := by
  set E : HalfLineAlgebra := inr (HalfLineKernel.exp (1 - s⁻¹) hζ)
  have h : resolvent * E = algebraMap ℂ HalfLineAlgebra s * (E - resolvent) := by
    rw [resolvent, ← inr_mul, HalfLineKernel.exp_one_mul_exp hs hζ, inr_smul, inr_sub,
      Algebra.smul_def]
  have hs' : algebraMap ℂ HalfLineAlgebra s * algebraMap ℂ HalfLineAlgebra s⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hs, map_one]
  refine IsUnit.of_mul_eq_one (algebraMap ℂ HalfLineAlgebra s⁻¹ *
    (1 + algebraMap ℂ HalfLineAlgebra s⁻¹ * E)) ?_
  linear_combination (-(algebraMap ℂ HalfLineAlgebra s⁻¹) ^ 2) * h +
    (1 + algebraMap ℂ HalfLineAlgebra s⁻¹ * resolvent) * hs'

theorem fourier_neg_two_pi_smul (f : ℝ → ℂ) :
    𝓕 (fun t : ℝ => (-2 * Real.pi * Complex.I * t) • f t) =
      (-2 * Real.pi * Complex.I) • 𝓕 (fun t : ℝ => t • f t) := by
  have h : (fun t : ℝ => (-2 * Real.pi * Complex.I * t) • f t) =
      (-2 * Real.pi * Complex.I) • fun t : ℝ => t • f t := by
    ext t
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    ring
  rw [h]
  exact VectorFourier.fourierIntegral_const_smul _ _ _ _ _

theorem norm_pow_sub_pow_le {σ a : ℂ} (hσ : ‖σ‖ ≤ 1) (ha : ‖a‖ < 1) (n : ℕ) :
    ‖σ ^ n - a ^ n‖ ≤ ‖σ - a‖ / (1 - ‖a‖) := by
  rw [← (Commute.all σ a).geom_sum₂_mul n, norm_mul, div_eq_mul_inv, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖∑ i ∈ Finset.range n, σ ^ i * a ^ (n - 1 - i)‖
      ≤ ∑ i ∈ Finset.range n, ‖a‖ ^ (n - 1 - i) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, norm_pow, norm_pow]
        exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) hσ)
    _ = ∑ i ∈ Finset.range n, ‖a‖ ^ i := Finset.sum_range_reflect (fun i => ‖a‖ ^ i) n
    _ ≤ ‖a‖ ^ 0 / (1 - ‖a‖) := by
        rw [Finset.range_eq_Ico]; exact geom_sum_Ico_le_of_lt_one (norm_nonneg _) ha
    _ = (1 - ‖a‖)⁻¹ := by rw [pow_zero, one_div]

theorem integral_norm_pow_snd_sq_le (μ : HalfLineAlgebra) (ha : ‖μ.fst‖ < 1)
    (hσ : ∀ ξ, ‖fourier ξ μ‖ ≤ 1) (n : ℕ) :
    ∫ t, ‖(μ ^ n).snd t‖ ^ 2 ≤ (∫ t, ‖μ.snd t‖ ^ 2) / (1 - ‖μ.fst‖) ^ 2 ∧
      ∫ t, ‖t • (μ ^ n).snd t‖ ^ 2 ≤ n ^ 2 * ∫ t, ‖t • μ.snd t‖ ^ 2 := by
  set a := μ.fst
  set g := μ.snd
  set gn := (μ ^ n).snd
  have ha0 : 0 < 1 - ‖a‖ := by linarith
  have hfst : (μ ^ n).fst = a ^ n := map_pow (fstHom ℂ HalfLineKernel) μ n
  have hF : ∀ ξ, 𝓕 (gn : ℝ → ℂ) ξ = (a + 𝓕 (g : ℝ → ℂ) ξ) ^ n - a ^ n := fun ξ => by
    have := map_pow (fourier ξ) μ n
    rw [fourier_apply, fourier_apply, hfst] at this
    linear_combination this
  have sq_int : ∀ f : HalfLineKernel, Integrable fun ξ => ‖𝓕 (f : ℝ → ℂ) ξ‖ ^ 2 := fun f =>
    (memLp_two_iff_integrable_sq_norm (f.memLp_two.fourier f.integrable).aestronglyMeasurable).1
      (f.memLp_two.fourier f.integrable)
  have sq_int' : ∀ f : HalfLineKernel, Integrable fun ξ => ‖𝓕 (fun t : ℝ => t • f t) ξ‖ ^ 2 :=
    fun f => (memLp_two_iff_integrable_sq_norm
      (f.memLp_two_smul.fourier f.integrable_smul).aestronglyMeasurable).1
      (f.memLp_two_smul.fourier f.integrable_smul)
  constructor
  · rw [← MemLp.integral_norm_fourier_sq gn.integrable gn.memLp_two,
      ← MemLp.integral_norm_fourier_sq g.integrable g.memLp_two, ← integral_div]
    refine integral_mono (sq_int gn) ((sq_int g).div_const _) fun ξ => ?_
    have hσ' : ‖a + 𝓕 (g : ℝ → ℂ) ξ‖ ≤ 1 := by simpa [fourier_apply] using hσ ξ
    have := norm_pow_sub_pow_le hσ' ha n
    rw [add_sub_cancel_left, ← hF] at this
    dsimp only
    rw [← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  · rw [← MemLp.integral_norm_fourier_sq gn.integrable_smul gn.memLp_two_smul,
      ← MemLp.integral_norm_fourier_sq g.integrable_smul g.memLp_two_smul, ← integral_const_mul]
    refine integral_mono (sq_int' gn) ((sq_int' g).const_mul _) fun ξ => ?_
    -- differentiate `ĝₙ = (a + ĝ)ⁿ - aⁿ`
    have hd1 := Real.hasDerivAt_fourier gn.integrable gn.integrable_smul ξ
    have hd2 := (((Real.hasDerivAt_fourier g.integrable g.integrable_smul ξ).const_add a).pow
      n).sub_const (a ^ n)
    have hfun : 𝓕 (gn : ℝ → ℂ) = fun ξ => (a + 𝓕 (g : ℝ → ℂ) ξ) ^ n - a ^ n := funext hF
    rw [hfun] at hd1
    have heq := hd1.unique hd2
    rw [fourier_neg_two_pi_smul, fourier_neg_two_pi_smul, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul] at heq
    have hc : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
    have heq' : 𝓕 (fun t : ℝ => t • (gn : ℝ → ℂ) t) ξ =
        n * (a + 𝓕 (g : ℝ → ℂ) ξ) ^ (n - 1) * 𝓕 (fun t : ℝ => t • (g : ℝ → ℂ) t) ξ :=
      mul_left_cancel₀ hc (by linear_combination heq)
    have hσ' : ‖a + 𝓕 (g : ℝ → ℂ) ξ‖ ≤ 1 := by simpa [fourier_apply] using hσ ξ
    dsimp only
    rw [heq', norm_mul, norm_mul, norm_pow, Complex.norm_natCast, mul_pow, mul_pow]
    calc (n : ℝ) ^ 2 * (‖a + 𝓕 (g : ℝ → ℂ) ξ‖ ^ (n - 1)) ^ 2 *
          ‖𝓕 (fun t : ℝ => t • (g : ℝ → ℂ) t) ξ‖ ^ 2
        ≤ (n : ℝ) ^ 2 * 1 * ‖𝓕 (fun t : ℝ => t • (g : ℝ → ℂ) t) ξ‖ ^ 2 := by
          gcongr
          exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) hσ')
      _ = _ := by ring

/-- Brenner–Thomée's bound: for `μ = a δ₀ + g` with `|a| < 1` and `|μ̂| ≤ 1`, the density `gₙ` of
`μⁿ` satisfies `(∫ |gₙ|)⁴ ≤ 4π² ‖g‖₂² ‖t g‖₂² n² / (1 - |a|)²` ([BrennerThomee1979]). -/
theorem integral_norm_pow_snd_pow_four_le (μ : HalfLineAlgebra) (ha : ‖μ.fst‖ < 1)
    (hσ : ∀ ξ, ‖fourier ξ μ‖ ≤ 1) (n : ℕ) :
    (∫ t, ‖(μ ^ n).snd t‖) ^ 4 ≤ 4 * Real.pi ^ 2 * (∫ t, ‖μ.snd t‖ ^ 2) *
      (∫ t, ‖t • μ.snd t‖ ^ 2) / (1 - ‖μ.fst‖) ^ 2 * n ^ 2 := by
  obtain ⟨h1, h2⟩ := integral_norm_pow_snd_sq_le μ ha hσ n
  refine (MemLp.integral_norm_pow_four_le (μ ^ n).snd.memLp_two
    (μ ^ n).snd.memLp_two_smul).trans ?_
  calc 4 * Real.pi ^ 2 * (∫ t, ‖(μ ^ n).snd t‖ ^ 2) * ∫ t, ‖t • (μ ^ n).snd t‖ ^ 2
      ≤ 4 * Real.pi ^ 2 * ((∫ t, ‖μ.snd t‖ ^ 2) / (1 - ‖μ.fst‖) ^ 2) *
          (n ^ 2 * ∫ t, ‖t • μ.snd t‖ ^ 2) := by
        gcongr
    _ = _ := by ring

end HalfLineAlgebra

end Feec
