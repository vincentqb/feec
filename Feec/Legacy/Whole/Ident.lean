module

public import Feec.Legacy.Whole.Weak

/-!
# Identification of the `ℝ³` Fourier model with physical fields

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

`Feec.Legacy.Whole.Basic` models fields on `ℝ³` by their Fourier transforms (Plancherel,
`Feec.Legacy.Whole.fieldFourierW`) and defines `H¹`, `H(div)` and `L²(TSD)` on the Fourier side, as
weighted-`L²` and fibrewise conditions. `Feec.Legacy.Whole.Weak` identified the Fourier `H(curl)`
with the weak-derivative `H(curl)`. This file does the same for the remaining spaces of
Prop 4.17, so that the constraint space `L²(TSD)` of `Feec.Legacy.Whole.whole_Kc_propagates` is identified
with the physical space of symmetric, trace-free, weakly divergence-free `L²` matrix fields.

## Main results

* `mem_mulDomain_iff_weak`: a generic statement. If a Schwartz-level differential operator `D`
  has Fourier symbol `m(ξ)*` (`𝓕 (D φ) = m* 𝓕 φ`), with `m` continuous, then for `f, g ∈ L²`:
  `𝓕 f` lies in the domain of the multiplier `m` with `m 𝓕 f = 𝓕 g` iff `⟪f, D φ⟫ = ⟪g, φ⟫` for
  every Schwartz `φ`, i.e. `g` is the weak `D*`-derivative of `f`.
* `gradSch`, `divSch`: the gradient `(∇ψ)_{ab} = ∂_b ψ_a` and the row-wise divergence
  `(div A)_a = ∂_b A_{ab}` of Schwartz fields (`gradSch_apply`, `Feec.Fourier.Weak.firstOrder`), with Fourier
  symbols `gradSym (2πξ)`, `divSym (2πξ)` (`fourier_gradSch`, `Feec.Fourier.Weak.fourier_formalAdjointOp`).
* **`mem_Hdiv_iff_weak`**: `𝓕 f ∈ H(div)` with `div (𝓕 f) = 𝓕 g` iff `div f = g` weakly,
  `⟪f, ∇ψ⟫ = -⟪g, ψ⟫`. **`Feec.Models.Euclidean.GradCurl.mem_domain_grad_iff_weak`**: `𝓕 u ∈ H¹` with `∇ (𝓕 u) = 𝓕 G` iff `∇u = G`
  weakly, `⟪u, div A⟫ = -⟪G, A⟫`.
* `fieldFourierW_compLp`: the `L²` Fourier transform commutes with pointwise complex-linear maps
  (proved on Schwartz fields and extended by density).
* **`fourier_mem_L2TSD_iff`**: `𝓕 f ∈ L²(TSD)` iff `f(x)` is symmetric and trace-free for a.e.
  `x` and `div f = 0` weakly; `L2TSD_eq_image` is the set form.

## References

* [QuennevilleBelair2015], §3.4, §4.10 (the spaces of Prop 4.17)
* Mathlib, `Mathlib.Analysis.Fourier.LpSpace` (Plancherel),
  `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier`,
  `Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff`
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal Topology SchwartzMap FourierTransform ContDiff
open MeasureTheory Set Filter

namespace Feec.Legacy.WholeIdent

open Feec.Legacy.Torus Feec.Legacy.Whole Feec.Legacy.WholeWeak

section Generic

variable {P Q : Type*} [Fintype P] [Fintype Q]

/-- The Fourier transform of a Schwartz field commutes with complex-linear post-composition. -/
theorem fourier_postcompG (L : EuclideanSpace ℂ P →L[ℂ] EuclideanSpace ℂ Q)
    (ψ : 𝓢(Freq, EuclideanSpace ℂ P)) (ξ : Freq) :
    𝓕 (SchwartzMap.postcompCLM L ψ) ξ = L (𝓕 ψ ξ) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have : (SchwartzMap.postcompCLM L ψ : Freq → EuclideanSpace ℂ Q) = fun x => L (ψ x) :=
    funext fun x => SchwartzMap.postcompCLM_apply L ψ x
  rw [this, Real.fourier_eq, Real.fourier_eq, ← L.integral_comp_comm]
  · congr 1; funext v; rw [Circle.smul_def, Circle.smul_def, map_smul]
  · exact (Real.fourierIntegral_convergent_iff ξ).2 ψ.integrable

/-- **The `L²` Fourier transform commutes with pointwise complex-linear maps**:
`𝓕 (L ∘ f) = L ∘ 𝓕 f` for `f ∈ L²(ℝ³; ℂᴾ)` (Schwartz fields, then density). -/
theorem fieldFourierW_compLp (L : EuclideanSpace ℂ P →L[ℂ] EuclideanSpace ℂ Q)
    (f : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq)) :
    fieldFourierW Q (L.compLp f) = L.compLp (fieldFourierW P f) := by
  have hc1 : Continuous fun f : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq) =>
      fieldFourierW Q (L.compLp f) :=
    (fieldFourierW Q).continuous.comp (L.compLpL 2 volume).continuous
  have hc2 : Continuous fun f : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq) =>
      L.compLp (fieldFourierW P f) :=
    (L.compLpL 2 volume).continuous.comp (fieldFourierW P).continuous
  refine DenseRange.induction_on
    (SchwartzMap.denseRange_toLpCLM (F := EuclideanSpace ℂ P) (μ := (volume : Measure Freq))
      (p := 2) ENNReal.ofNat_ne_top) f (isClosed_eq hc1 hc2) ?_
  intro φ
  simp only [SchwartzMap.toLpCLM_apply]
  have h1 : L.compLp (φ.toLp 2) = (SchwartzMap.postcompCLM L φ).toLp 2 := by
    refine Lp.ext ?_
    filter_upwards [L.coeFn_compLp (φ.toLp 2), φ.coeFn_toLp 2 volume,
      (SchwartzMap.postcompCLM L φ).coeFn_toLp 2 volume] with ξ h1 h2 h3
    rw [h1, h2, h3, SchwartzMap.postcompCLM_apply]
  rw [h1, fieldFourierW_toLp, fieldFourierW_toLp]
  refine Lp.ext ?_
  filter_upwards [(𝓕 (SchwartzMap.postcompCLM L φ)).coeFn_toLp 2 volume,
    L.coeFn_compLp ((𝓕 φ).toLp 2), (𝓕 φ).coeFn_toLp 2 volume] with ξ h1 h2 h3
  rw [h1, h2, h3, fourier_postcompG]

/-- A continuous symbol applied to an `L²` field is locally integrable. -/
theorem locallyIntegrable_symbol {m : Freq → EuclideanSpace ℂ P →L[ℝ] EuclideanSpace ℂ Q}
    (hm : Continuous m) (F : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq)) :
    LocallyIntegrable (fun ξ => m ξ (F ξ)) volume := by
  refine (locallyIntegrable_iff).2 fun K hK => ?_
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hm.continuousOn
  have hF : IntegrableOn F K volume :=
    ((Lp.memLp F).locallyIntegrable (by norm_num)).integrableOn_isCompact hK
  refine Integrable.mono' (hF.norm.const_mul C)
    (aestronglyMeasurable_apply hm.stronglyMeasurable.aestronglyMeasurable
      (Lp.aestronglyMeasurable F)).restrict ?_
  refine (ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun ξ hξ => ?_)
  exact ((m ξ).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC ξ hξ) (norm_nonneg _))

/-- **Generic weak identification of Fourier multiplier domains on `ℝ³`.** Let `m` be a
continuous symbol and `D` a map on Schwartz fields with `𝓕 (D φ) = m(ξ)* 𝓕 φ` (so `D` is the
formal adjoint of the operator with symbol `m`). For `f, g ∈ L²`, `𝓕 f` lies in the domain of
the multiplier `m` with `m 𝓕 f = 𝓕 g` iff `⟪f, D φ⟫ = ⟪g, φ⟫` for every Schwartz `φ` (real `L²`
inner products). -/
theorem mem_mulDomain_iff_weak {m : Freq → EuclideanSpace ℂ P →L[ℝ] EuclideanSpace ℂ Q}
    (hm : Continuous m) (D : 𝓢(Freq, EuclideanSpace ℂ Q) → 𝓢(Freq, EuclideanSpace ℂ P))
    (hD : ∀ φ ξ, 𝓕 (D φ) ξ = ContinuousLinearMap.adjoint (m ξ) (𝓕 φ ξ))
    (f : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq))
    (g : Lp (EuclideanSpace ℂ Q) 2 (volume : Measure Freq)) :
    (∃ h : fieldFourierW P f ∈ mulDomain volume m,
        mulOp volume m ⟨fieldFourierW P f, h⟩ = fieldFourierW Q g) ↔
      ∀ φ : 𝓢(Freq, EuclideanSpace ℂ Q), ⟪f, (D φ).toLp 2⟫ = ⟪g, φ.toLp 2⟫ := by
  set F := fieldFourierW P f
  set G := fieldFourierW Q g
  have key : ∀ φ : 𝓢(Freq, EuclideanSpace ℂ Q), ⟪f, (D φ).toLp 2⟫ = ∫ ξ, ⟪m ξ (F ξ), 𝓕 φ ξ⟫ := fun φ => by
    rw [← inner_fieldFourierW P, fieldFourierW_toLp, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(𝓕 (D φ)).coeFn_toLp 2 volume] with ξ h
    rw [h, hD, ContinuousLinearMap.adjoint_inner_right]
  have key' : ∀ φ : 𝓢(Freq, EuclideanSpace ℂ Q), ⟪g, φ.toLp 2⟫ = ∫ ξ, ⟪G ξ, 𝓕 φ ξ⟫ := fun φ => by
    rw [← inner_fieldFourierW Q, fieldFourierW_toLp, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(𝓕 φ).coeFn_toLp 2 volume] with ξ h
    rw [h]
  constructor
  · rintro ⟨h, hc⟩ φ
    rw [key, key']
    refine integral_congr_ae ?_
    filter_upwards [coeFn_mulOp volume m ⟨F, h⟩] with ξ h1
    rw [← hc, h1]
  · intro hw
    have hloc := locallyIntegrable_symbol hm F
    have hGloc : LocallyIntegrable (G : Freq → EuclideanSpace ℂ Q) volume :=
      (Lp.memLp G).locallyIntegrable (by norm_num)
    have hae : (fun ξ => m ξ (F ξ)) =ᵐ[volume] (G : Freq → EuclideanSpace ℂ Q) := by
      refine ae_eq_of_integral_contDiff_smul_eq hloc hGloc fun χ hχ hχs => ?_
      have hi1 := hloc.integrable_smul_left_of_hasCompactSupport hχ.continuous hχs
      have hi2 := hGloc.integrable_smul_left_of_hasCompactSupport hχ.continuous hχs
      refine ext_inner_left ℝ fun M₀ => ?_
      rw [← integral_inner hi1, ← integral_inner hi2]
      have hs : HasCompactSupport fun ξ => χ ξ • M₀ := hχs.smul_right
      have hd : ContDiff ℝ ∞ fun ξ => χ ξ • M₀ := hχ.smul contDiff_const
      set ψ : 𝓢(Freq, EuclideanSpace ℂ Q) := hs.toSchwartzMap hd
      have hψ : ∀ ξ, ψ ξ = χ ξ • M₀ := fun ξ => rfl
      have h := hw (𝓕⁻ ψ)
      rw [key, key'] at h
      simp only [FourierTransform.fourier_fourierInv_eq, hψ] at h
      have e : ∀ (x : EuclideanSpace ℂ Q) (ξ : Freq), ⟪M₀, χ ξ • x⟫ = ⟪x, χ ξ • M₀⟫ :=
        fun x ξ => by rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm]
      simp only [e]
      exact h
    have hmem : F ∈ mulDomain volume m := (Lp.memLp G).ae_eq hae.symm
    refine ⟨hmem, Lp.ext ?_⟩
    filter_upwards [coeFn_mulOp volume m ⟨F, hmem⟩, hae] with ξ h1 h2
    rw [h1, ← h2]

end Generic

section GradDiv

/-- The coefficient map `v ↦ v e_cᵀ` of `∂_c` in the gradient. -/
def gradC (c : Fin 3) : Vec3 →L[ℂ] Mat3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => mat fun a b => if b = c then v a else 0
      map_add' := fun u v => by ext ⟨a, b⟩; by_cases h : b = c <;> simp [h]
      map_smul' := fun z v => by ext ⟨a, b⟩; by_cases h : b = c <;> simp [h] }

theorem gradC_apply (c : Fin 3) (v : Vec3) (a b : Fin 3) :
    gradC c v (a, b) = if b = c then v a else 0 := rfl

/-- The coefficient map `M ↦ M e_c` (column `c`) of `∂_c` in the row-wise divergence. -/
def divC (c : Fin 3) : Mat3 →L[ℂ] Vec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => vec fun a => M (a, c)
      map_add' := fun M N => by ext a; simp
      map_smul' := fun z M => by ext a; simp }

/-- **The gradient of a Schwartz vector field**, `(∇ψ)_{ab} = ∂_b ψ_a` (`gradSch_apply`). -/
def gradSch (ψ : 𝓢(Freq, Vec3)) : 𝓢(Freq, Mat3) :=
  ∑ c : Fin 3, SchwartzMap.postcompCLM (gradC c) (LineDeriv.lineDerivOp (ev c) ψ)

theorem gradSch_apply (ψ : 𝓢(Freq, Vec3)) (x : Freq) (a b : Fin 3) :
    gradSch ψ x (a, b) = fderiv ℝ ψ x (ev b) a := by
  simp only [gradSch, sum_apply, SchwartzMap.postcompCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp [gradC_apply]

theorem hasTemperateGrowth_inner_ev (c : Fin 3) :
    (fun x : Freq => inner ℝ x (ev c)).HasTemperateGrowth :=
  ((innerSL ℝ).flip (ev c)).hasTemperateGrowth

/-- `𝓕 (∇ψ)(ξ) = i 𝓕ψ(ξ) (2πξ)ᵀ`: the gradient is the multiplier `gradSym (2πξ)` of
`Feec.Legacy.Whole.gradW`. -/
theorem fourier_gradSch (ψ : 𝓢(Freq, Vec3)) (ξ : Freq) :
    𝓕 (gradSch ψ) ξ = gradSym (freqW ξ) (𝓕 ψ ξ) := by
  rw [gradSch, ← SchwartzMap.fourierTransformCLM_apply ℂ, map_sum, sum_apply]
  simp only [SchwartzMap.fourierTransformCLM_apply, fourier_postcompG,
    SchwartzMap.fourier_lineDerivOp_eq, _root_.smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_inner_ev _)]
  ext ⟨a, b⟩
  fin_cases b <;>
    simp [gradC_apply, gradSym_apply, freqW, Fin.sum_univ_three, ev,
      EuclideanSpace.inner_single_right] <;> ring

theorem fourier_neg_apply {P : Type*} [Fintype P] (φ : 𝓢(Freq, EuclideanSpace ℂ P)) (ξ : Freq) :
    𝓕 (-φ) ξ = -𝓕 φ ξ := by
  rw [← SchwartzMap.fourierTransformCLM_apply ℂ, map_neg]; rfl

theorem toLp_neg {P : Type*} [Fintype P] (φ : 𝓢(Freq, EuclideanSpace ℂ P)) :
    (-φ).toLp 2 = -(φ.toLp 2) :=
  map_neg (SchwartzMap.toLpCLM ℝ (EuclideanSpace ℂ P) 2 (volume : Measure Freq)) φ

/-- `div* = -grad` fibrewise. -/
theorem adjoint_divSym (ζ : Freq) : ContinuousLinearMap.adjoint (divSym ζ) = -gradSym ζ := by
  rw [show divSym ζ = -ContinuousLinearMap.adjoint (gradSym ζ) by rw [adjoint_gradSym, neg_neg],
    map_neg, ContinuousLinearMap.adjoint_adjoint]

/-- The row-wise divergence on `ℝ³` (Fourier side), with domain `H(div)`;
`grad* = -divW` (`Feec.Legacy.Whole.coeFn_adjoint_gradW`). -/
def divW : Whole.L2M →ₗ.[ℝ] Whole.L2V := mulOp volume fun ξ => divSym (freqW ξ)

/-- **The Fourier `H(div)` is the weak-derivative `H(div)` on `ℝ³`.** For `f ∈ L²(ℝ³; ℂ³ˣ³)` and
`g ∈ L²(ℝ³; ℂ³)`: `𝓕 f ∈ H(div)` with `div (𝓕 f) = 𝓕 g` (the multiplier `divW`) iff
`div f = g` weakly, i.e. `⟪f, ∇ψ⟫ = -⟪g, ψ⟫` for every Schwartz vector field `ψ`, with
`(∇ψ)_{ab} = ∂_b ψ_a` and `(div f)_a = ∂_b f_{ab}` (real `L²` inner products). -/
theorem mem_Hdiv_iff_weak (f : Lp Mat3 2 (volume : Measure Freq))
    (g : Lp Vec3 2 (volume : Measure Freq)) :
    (∃ h : matrixFourierW f ∈ Whole.Hdiv, divW ⟨matrixFourierW f, h⟩ = vectorFourierW g) ↔
      ∀ ψ : 𝓢(Freq, Vec3), ⟪f, (gradSch ψ).toLp 2⟫ = -⟪g, ψ.toLp 2⟫ := by
  have h := mem_mulDomain_iff_weak (continuous_divSym.comp continuous_freqW)
    (fun ψ => gradSch (-ψ)) (fun ψ ξ => by
      simp only [Function.comp_apply]
      rw [fourier_gradSch, fourier_neg_apply, adjoint_divSym, _root_.map_neg, _root_.neg_apply])
    f g
  refine h.trans ⟨fun H ψ => ?_, fun H ψ => ?_⟩
  · have := H (-ψ)
    rw [neg_neg, toLp_neg, inner_neg_right] at this
    exact this
  · rw [H, toLp_neg, inner_neg_right, neg_neg]

end GradDiv

section TSD

/-- The defect from being symmetric and trace-free: `M - Mᵀ + (tr M) I` (zero iff `M ∈ tsd 0`,
`mem_tsd_zero_iff_defect`). -/
def tsdDefect : Mat3 →L[ℂ] Mat3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => mat fun a b => M (a, b) - M (b, a) + if a = b then ∑ c, M (c, c) else 0
      map_add' := fun M N => by
        ext ⟨a, b⟩; by_cases h : a = b <;> simp [h, Finset.sum_add_distrib]; ring
      map_smul' := fun z M => by
        ext ⟨a, b⟩; by_cases h : a = b <;> simp [h, ← Finset.mul_sum]; ring }

theorem tsdDefect_apply (M : Mat3) (a b : Fin 3) :
    tsdDefect M (a, b) = M (a, b) - M (b, a) + if a = b then ∑ c, M (c, c) else 0 := rfl

/-- `M` is symmetric and trace-free iff `tsdDefect M = 0`. -/
theorem mem_tsd_zero_iff_defect {M : Mat3} : M ∈ tsd 0 ↔ tsdDefect M = 0 := by
  rw [mem_tsd_zero]
  constructor
  · rintro ⟨hs, ht⟩
    ext ⟨a, b⟩
    by_cases h : a = b <;> simp [tsdDefect_apply, h, hs a b, ht]
  · intro h
    have e : ∀ a b, M (a, b) - M (b, a) + (if a = b then ∑ c, M (c, c) else 0) = 0 :=
      fun a b => by rw [← tsdDefect_apply, h]; rfl
    have ht : ∑ c, M (c, c) = 0 := by simpa using e 0 0
    refine ⟨fun a b => ?_, ht⟩
    have := e a b
    rw [ht] at this
    simp only [ite_self, add_zero] at this
    exact sub_eq_zero.1 this

/-- A pointwise complex-linear condition on an `L²` field transfers to its Fourier transform. -/
theorem ae_ker_iff_fourier {P Q : Type*} [Fintype P] [Fintype Q]
    (L : EuclideanSpace ℂ P →L[ℂ] EuclideanSpace ℂ Q)
    (f : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq)) :
    (∀ᵐ x ∂(volume : Measure Freq), L (f x) = 0) ↔
      ∀ᵐ ξ ∂(volume : Measure Freq), L (fieldFourierW P f ξ) = 0 := by
  have e : ∀ g : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq),
      (∀ᵐ x ∂(volume : Measure Freq), L (g x) = 0) ↔ L.compLp g = 0 := fun g => by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    constructor
    · intro h
      filter_upwards [h, L.coeFn_compLp g, Lp.coeFn_zero (EuclideanSpace ℂ Q) 2
        (volume : Measure Freq)] with x h1 h2 h3
      rw [h2, h1, Pi.zero_apply]
    · intro h
      filter_upwards [h, L.coeFn_compLp g] with x h1 h2
      rw [← h2, h1, Pi.zero_apply]
  rw [e, e, ← fieldFourierW_compLp, LinearIsometryEquiv.map_eq_zero_iff]

/-- `divSym ζ M = 0` iff `M ζ = 0`. -/
theorem divSym_eq_zero_iff {ζ : Freq} {M : Mat3} :
    divSym ζ M = 0 ↔ ∀ a, ∑ b, M (a, b) * ζ b = 0 := by
  constructor
  · intro h a
    have := congrArg (fun v : Vec3 => v a) h
    simpa [divSym_apply] using this
  · intro h; ext a; simp [divSym_apply, h a]

/-- `M ∈ tsd ζ` iff `M` is symmetric, trace-free and `div_ζ M = 0`. -/
theorem mem_tsd_iff_divSym {ζ : Freq} {M : Mat3} : M ∈ tsd ζ ↔ M ∈ tsd 0 ∧ divSym ζ M = 0 := by
  rw [divSym_eq_zero_iff, mem_tsd_zero, mem_tsd]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- Weakly divergence-free physical fields are exactly those with `div_{2πξ} 𝓕 f = 0` a.e. -/
theorem weak_div_zero_iff (f : Lp Mat3 2 (volume : Measure Freq)) :
    (∀ ψ : 𝓢(Freq, Vec3), ⟪f, (gradSch ψ).toLp 2⟫ = 0) ↔
      ∀ᵐ ξ ∂(volume : Measure Freq), divSym (freqW ξ) (matrixFourierW f ξ) = 0 := by
  have h := mem_Hdiv_iff_weak f 0
  simp only [inner_zero_left, neg_zero, _root_.map_zero] at h
  rw [← h]
  constructor
  · rintro ⟨hm, hz⟩
    filter_upwards [coeFn_mulOp volume (fun ξ => divSym (freqW ξ)) ⟨_, hm⟩,
      Lp.coeFn_zero Vec3 2 (volume : Measure Freq)] with ξ h1 h2
    have := h1.symm.trans (congrArg (fun u : Whole.L2V => (u : Freq → Vec3) ξ) hz)
    rw [this, h2, Pi.zero_apply]
  · intro hz
    have hm : matrixFourierW f ∈ Whole.Hdiv :=
      (MemLp.zero (ε := Vec3)).ae_eq (by filter_upwards [hz] with ξ h; exact h.symm)
    refine ⟨hm, Lp.ext ?_⟩
    filter_upwards [coeFn_mulOp volume (fun ξ => divSym (freqW ξ)) ⟨_, hm⟩, hz,
      Lp.coeFn_zero Vec3 2 (volume : Measure Freq)] with ξ h1 h2 h3
    change (divW ⟨_, hm⟩ : Freq → Vec3) ξ = _
    rw [h3]
    exact h1.trans h2

/-- **The constraint space of Prop 4.17 on `ℝ³` is the physical TSD space.** For
`f ∈ L²(ℝ³; ℂ³ˣ³)`: `𝓕 f ∈ L²(TSD)` (the fibrewise space `Feec.Legacy.Whole.L2TSD` used by
`Feec.Legacy.Whole.whole_Kc_propagates`) iff `f(x)` is symmetric and trace-free for a.e. `x`
(`f x ∈ tsd 0`, `Feec.Legacy.Torus.mem_tsd_zero`) and `div f = 0` weakly
(`⟪f, ∇ψ⟫ = 0` for every Schwartz vector field `ψ`, `(div f)_a = ∂_b f_{ab}`). -/
theorem fourier_mem_L2TSD_iff (f : Lp Mat3 2 (volume : Measure Freq)) :
    matrixFourierW f ∈ Whole.L2TSD ↔
      (∀ᵐ x ∂(volume : Measure Freq), f x ∈ tsd 0) ∧
        ∀ ψ : 𝓢(Freq, Vec3), ⟪f, (gradSch ψ).toLp 2⟫ = 0 := by
  have h1 : (∀ᵐ x ∂(volume : Measure Freq), f x ∈ tsd 0) ↔
      ∀ᵐ ξ ∂(volume : Measure Freq), matrixFourierW f ξ ∈ tsd 0 := by
    simp only [mem_tsd_zero_iff_defect]
    exact ae_ker_iff_fourier tsdDefect f
  rw [h1, weak_div_zero_iff, ← eventually_and, Whole.mem_fibreSub]
  exact eventually_congr (Eventually.of_forall fun ξ => mem_tsd_iff_divSym)

/-- Set form: `L²(TSD) = 𝓕 {f ∈ L² | f symmetric, trace-free, weakly divergence-free}`. -/
theorem L2TSD_eq_image :
    (Whole.L2TSD : Set Whole.L2M) = matrixFourierW ''
      {f | (∀ᵐ x ∂(volume : Measure Freq), f x ∈ tsd 0) ∧
        ∀ ψ : 𝓢(Freq, Vec3), ⟪f, (gradSch ψ).toLp 2⟫ = 0} := by
  ext A
  constructor
  · intro hA
    refine ⟨matrixFourierW.symm A, ?_, LinearIsometryEquiv.apply_symm_apply _ _⟩
    rw [Set.mem_ofPred_eq, ← fourier_mem_L2TSD_iff, LinearIsometryEquiv.apply_symm_apply]
    exact hA
  · rintro ⟨f, hf, rfl⟩
    exact (fourier_mem_L2TSD_iff f).2 hf

end TSD

end Feec.Legacy.WholeIdent
