module

public import Feec.Ch4.Whole
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# `H(curl)` on `ℝ³`: the Fourier multiplier is the weak curl

`Feec.Ch4.Whole` models matrix fields on `ℝ³` by their Fourier transforms (Plancherel,
`Feec.Whole.matrixFourierW`) and defines `H(curl)` as the domain of the Fourier multiplier
`Feec.Whole.curlW` (`Â ↦ i (2πξ × Â_a)_a`). This file proves that this is the weak-derivative
`H(curl)`: the analogue on `ℝ³` of `Feec.TorusWeak.matrixFourier_mem_Hcurl_iff` on `𝕋³`.

## Main results

* `curlSch`: the thesis' row-wise curl `(curl φ)_{ab} = ε_{bcd} ∂_c φ_{ad}` on Schwartz matrix
  fields (`curlSch_apply`), built from Mathlib's line derivatives.
* `fourier_curlSch`: `𝓕 (curl φ) = curlSym (2πξ) (𝓕 φ)`, from Mathlib's
  `SchwartzMap.fourier_lineDerivOp_eq` and `fourier_postcomp` (the Fourier transform commutes
  with complex-linear post-composition).
* **`mem_Hcurl_iff_weak`**: for `f, g ∈ L²(ℝ³; ℂ³ˣ³)`, `𝓕 f ∈ H(curl)` with `curl (𝓕 f) = 𝓕 g`
  iff `⟪f, curl φ⟫ = ⟪g, φ⟫` for all Schwartz `φ` (real `L²` inner products); and
  `fourier_mem_Hcurl_iff` (`𝓕 f ∈ H(curl)` iff `f` has a weak curl in `L²`).

The converse direction uses test fields `𝓕⁻¹ (χ M₀)`, `χ ∈ C_c^∞`, the local integrability of
`curl_{2πξ} F(ξ)` (`locallyIntegrable_curl`), and Mathlib's fundamental lemma
`ae_eq_of_integral_contDiff_smul_eq`.

Scope: only `H(curl)` is identified here. `H¹`, `H(div)` and `L²(TSD)` are identified in
`Feec.Ch4.WholeIdent` (by a generic version of the argument below). The spaces of
`Feec.Ch4.WholeSym` (complex (4.16)) are not identified with physical fields.

## References

* [QuennevilleBelair2015], §3.4, §4.10 (the row-wise curl and `H(curl)`)
* Mathlib, `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier` (Fourier transform of
  derivatives of Schwartz functions), `Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff`
  (fundamental lemma of the calculus of variations)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal Topology SchwartzMap FourierTransform ContDiff
open MeasureTheory Set Filter

namespace Feec.WholeWeak

open Feec.Torus Feec.Whole

section Schwartz

/-- The curl symbol coefficient `M ↦ (ξ × M_a)_a` as a complex-linear map (the same formula as
`Feec.Torus.curlR`, `curlC_apply`). -/
def curlC (ξ : Freq) : Mat3 →L[ℂ] Mat3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => mat fun a => cross ξ fun d => M (a, d)
      map_add' := fun M N => by
        ext ⟨a, b⟩; fin_cases b <;> simp [cross] <;> ring
      map_smul' := fun c M => by
        ext ⟨a, b⟩; fin_cases b <;> simp [cross] <;> ring }

theorem curlC_apply (ξ : Freq) (M : Mat3) : curlC ξ M = curlR ξ M := rfl

/-- The coordinate vectors `e_c` of `ℝ³`. -/
abbrev ev (c : Fin 3) : Freq := EuclideanSpace.single c 1

/-- **The thesis' row-wise curl of a Schwartz matrix field**,
`(curl φ)_{ab} = ε_{bcd} ∂_c φ_{ad}` (`curlSch_apply`), as `∑_c (e_c × ·)_{rows} ∂_c φ`. -/
def curlSch (φ : 𝓢(Freq, Mat3)) : 𝓢(Freq, Mat3) :=
  ∑ c : Fin 3, SchwartzMap.postcompCLM (curlC (ev c)) (LineDeriv.lineDerivOp (ev c) φ)

/-- The entries of `curlSch φ`: `(curl φ)_{ab}(x) = ∑_{c,d} ε_{bcd} ∂_c φ_{ad}(x)`. -/
theorem curlSch_apply (φ : 𝓢(Freq, Mat3)) (x : Freq) (a b : Fin 3) :
    curlSch φ x (a, b) = ∑ c, ∑ d, (eps3 b c d : ℂ) * (fderiv ℝ φ x (ev c)) (a, d) := by
  simp only [curlSch, sum_apply, SchwartzMap.postcompCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, curlC_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [curlR_apply_eps3]
  simp [Fin.sum_univ_three, ev, Constraints.eps3_apply]

/-- The Fourier transform commutes with complex-linear post-composition. -/
theorem fourier_postcomp (L : Mat3 →L[ℂ] Mat3) (ψ : 𝓢(Freq, Mat3)) (ξ : Freq) :
    𝓕 (SchwartzMap.postcompCLM L ψ) ξ = L (𝓕 ψ ξ) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have : (SchwartzMap.postcompCLM L ψ : Freq → Mat3) = fun x => L (ψ x) :=
    funext fun x => SchwartzMap.postcompCLM_apply L ψ x
  rw [this, Real.fourier_eq, Real.fourier_eq, ← L.integral_comp_comm]
  · congr 1; funext v; rw [Circle.smul_def, Circle.smul_def, map_smul]
  · exact (Real.fourierIntegral_convergent_iff ξ).2 ψ.integrable

/-- **Fourier transform of the curl**: `𝓕 (curl φ)(ξ) = i (2πξ × 𝓕φ(ξ)_a)_a`, i.e. the curl is
the Fourier multiplier `curlSym (freqW ξ)` used by `Feec.Whole.curlW`. -/
theorem fourier_curlSch (φ : 𝓢(Freq, Mat3)) (ξ : Freq) :
    𝓕 (curlSch φ) ξ = curlSym (freqW ξ) (𝓕 φ ξ) := by
  have hT : ∀ c : Fin 3, (fun x : Freq => inner ℝ x (ev c)).HasTemperateGrowth := fun c =>
    ((innerSL ℝ).flip (ev c)).hasTemperateGrowth
  rw [curlSch, ← SchwartzMap.fourierTransformCLM_apply ℂ, map_sum, sum_apply]
  simp only [SchwartzMap.fourierTransformCLM_apply, fourier_postcomp,
    SchwartzMap.fourier_lineDerivOp_eq, _root_.smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply (hT _)]
  ext ⟨a, b⟩
  fin_cases b <;>
    simp [curlC_apply, curlR_apply, cross, curlSym_apply, jM_apply, freqW, Fin.sum_univ_three,
      ev, EuclideanSpace.inner_single_right] <;> ring

end Schwartz

section Weak

/-- `curl_ξ` is symmetric for the real inner product. -/
theorem inner_curlSym_symm (ξ : Freq) (A B : Mat3) : ⟪curlSym ξ A, B⟫ = ⟪A, curlSym ξ B⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_curlSym]

/-- `ξ ↦ curl_{2πξ} F(ξ)` is locally integrable for `F ∈ L²` (the symbol is locally bounded). -/
theorem locallyIntegrable_curl (F : Whole.L2M) :
    LocallyIntegrable (fun ξ => curlSym (freqW ξ) (F ξ)) volume := by
  refine (locallyIntegrable_iff).2 fun K hK => ?_
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((continuous_curlSym.comp continuous_freqW).continuousOn)
  have hF : IntegrableOn F K volume :=
    ((Lp.memLp F).locallyIntegrable (by norm_num)).integrableOn_isCompact hK
  refine Integrable.mono' (hF.norm.const_mul C)
    (aestronglyMeasurable_apply stronglyMeasurable_curlW.aestronglyMeasurable
      (Lp.aestronglyMeasurable F)).restrict ?_
  refine (ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun ξ hξ => ?_)
  exact ((curlSym (freqW ξ)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hC ξ hξ) (norm_nonneg _))

/-- The Fourier transform of a Schwartz field, as an element of `L2M`. -/
def fourierLp (φ : 𝓢(Freq, Mat3)) : Whole.L2M := (𝓕 φ : 𝓢(Freq, Mat3)).toLp 2

theorem coeFn_fourierLp (φ : 𝓢(Freq, Mat3)) :
    fourierLp φ =ᵐ[volume] fun ξ => 𝓕 φ ξ := (𝓕 φ : 𝓢(Freq, Mat3)).coeFn_toLp 2 volume

/-- Fourier transforms of Schwartz fields lie in `H(curl)`, where `curlW` acts as the Fourier
transform of the Schwartz curl. -/
theorem fourier_mem_Hcurl (φ : 𝓢(Freq, Mat3)) : fourierLp φ ∈ Whole.Hcurl := by
  refine (Lp.memLp (fourierLp (curlSch φ))).ae_eq ?_
  filter_upwards [coeFn_fourierLp φ, coeFn_fourierLp (curlSch φ)] with ξ h h'
  rw [h, h', fourier_curlSch]

theorem fourier_mem_domain (φ : 𝓢(Freq, Mat3)) : fourierLp φ ∈ curlW.domain := by
  rw [curlW_domain]; exact fourier_mem_Hcurl φ

theorem curlW_fourier (φ : 𝓢(Freq, Mat3)) :
    curlW ⟨fourierLp φ, fourier_mem_domain φ⟩ = fourierLp (curlSch φ) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_curlW ⟨fourierLp φ, fourier_mem_domain φ⟩,
    coeFn_fourierLp φ, coeFn_fourierLp (curlSch φ)] with ξ h1 h2 h3
  rw [h1, h3, fourier_curlSch]
  exact congrArg _ h2

/-- `curl` is symmetric on `H(curl)`: `⟪curl A, B⟫ = ⟪A, curl B⟫`. -/
theorem inner_curlW_symm (A B : curlW.domain) :
    ⟪curlW A, (B : Whole.L2M)⟫ = ⟪(A : Whole.L2M), curlW B⟫ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_curlW A, coeFn_curlW B] with ξ h1 h2
  rw [h1, h2, inner_curlSym_symm]

/-- **The Fourier `H(curl)` is the weak-derivative `H(curl)` on `ℝ³`.** For physical matrix
fields `f, g ∈ L²(ℝ³; ℂ³ˣ³)` with Fourier transforms `F = 𝓕 f`, `G = 𝓕 g` (Plancherel,
`Feec.Whole.matrixFourierW`): `F ∈ H(curl)` with `curl F = G` (the Fourier multiplier
`Feec.Whole.curlW`) iff `curl f = g` weakly, i.e. `⟪f, curl φ⟫ = ⟪g, φ⟫` for every Schwartz
field `φ`, with the thesis' row-wise curl `(curl φ)_{ab} = ε_{bcd} ∂_c φ_{ad}`
(`curlSch_apply`), which is formally self-adjoint. The inner products are the real `L²` inner
products `Re ∫ ⟨·,·⟩`.

The proof of `←` tests against `φ = 𝓕⁻¹ (χ M₀)` with `χ` smooth and compactly supported, and
concludes with the fundamental lemma of the calculus of variations
(`ae_eq_of_integral_contDiff_smul_eq`); no core property of the Schwartz space is needed. -/
theorem mem_Hcurl_iff_weak (f g : Lp Mat3 2 (volume : Measure Freq)) :
    (∃ h : matrixFourierW f ∈ Whole.Hcurl, curlW ⟨matrixFourierW f, h⟩ = matrixFourierW g) ↔
      ∀ φ : 𝓢(Freq, Mat3), ⟪f, (curlSch φ).toLp 2⟫ = ⟪g, φ.toLp 2⟫ := by
  have hF : ∀ φ : 𝓢(Freq, Mat3), matrixFourierW (φ.toLp 2) = fourierLp φ :=
    fun φ => fieldFourierW_toLp _ φ
  have key : ∀ φ : 𝓢(Freq, Mat3), ⟪f, (curlSch φ).toLp 2⟫ =
      ⟪matrixFourierW f, curlW ⟨fourierLp φ, fourier_mem_domain φ⟩⟫ := fun φ => by
    rw [curlW_fourier, ← hF, matrixFourierW, inner_fieldFourierW]
  have key' : ∀ φ : 𝓢(Freq, Mat3), ⟪g, φ.toLp 2⟫ = ⟪matrixFourierW g, fourierLp φ⟫ :=
    fun φ => by rw [← hF, matrixFourierW, inner_fieldFourierW]
  constructor
  · rintro ⟨h, hc⟩ φ
    rw [key, key', ← hc]
    exact (inner_curlW_symm ⟨_, h⟩ ⟨fourierLp φ, fourier_mem_domain φ⟩).symm
  · intro hw
    set F := matrixFourierW f
    set G := matrixFourierW g
    have hloc := locallyIntegrable_curl F
    have hGloc : LocallyIntegrable (G : Freq → Mat3) volume :=
      (Lp.memLp G).locallyIntegrable (by norm_num)
    have hae : (fun ξ => curlSym (freqW ξ) (F ξ)) =ᵐ[volume] (G : Freq → Mat3) := by
      refine ae_eq_of_integral_contDiff_smul_eq hloc hGloc fun χ hχ hχs => ?_
      have hi1 := hloc.integrable_smul_left_of_hasCompactSupport hχ.continuous hχs
      have hi2 := hGloc.integrable_smul_left_of_hasCompactSupport hχ.continuous hχs
      refine ext_inner_left ℝ fun M₀ => ?_
      rw [← integral_inner hi1, ← integral_inner hi2]
      have hs : HasCompactSupport fun ξ => χ ξ • M₀ := hχs.smul_right
      have hd : ContDiff ℝ ∞ fun ξ => χ ξ • M₀ := hχ.smul contDiff_const
      set ψ : 𝓢(Freq, Mat3) := hs.toSchwartzMap hd
      have hψ : ∀ ξ, ψ ξ = χ ξ • M₀ := fun ξ => rfl
      have h := hw (𝓕⁻ ψ)
      rw [key, key'] at h
      rw [L2.inner_def, L2.inner_def] at h
      have e1 : ∫ ξ, ⟪M₀, χ ξ • curlSym (freqW ξ) (F ξ)⟫ =
          ∫ ξ, ⟪F ξ, curlW ⟨fourierLp (𝓕⁻ ψ), fourier_mem_domain (𝓕⁻ ψ)⟩ ξ⟫ := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_curlW ⟨fourierLp (𝓕⁻ ψ), fourier_mem_domain (𝓕⁻ ψ)⟩,
          coeFn_fourierLp (𝓕⁻ ψ)] with ξ h1 h2
        rw [h1]
        rw [h2, FourierTransform.fourier_fourierInv_eq, hψ, _root_.map_smul,
          real_inner_smul_right, real_inner_smul_right, ← inner_curlSym_symm, real_inner_comm]
      have e2 : ∫ ξ, ⟪M₀, χ ξ • G ξ⟫ = ∫ ξ, ⟪G ξ, fourierLp (𝓕⁻ ψ) ξ⟫ := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_fourierLp (𝓕⁻ ψ)] with ξ h2
        rw [h2, FourierTransform.fourier_fourierInv_eq, hψ, real_inner_smul_right,
          real_inner_smul_right, real_inner_comm]
      rw [e1, e2]
      convert h using 3
    have hmem : F ∈ Whole.Hcurl := (Lp.memLp G).ae_eq hae.symm
    refine ⟨hmem, Lp.ext ?_⟩
    filter_upwards [coeFn_curlW ⟨F, hmem⟩, hae] with ξ h1 h2
    rw [h1, ← h2]

/-- **Physical `H(curl)` on `ℝ³`**: `𝓕 f ∈ H(curl)` iff `f` has a weak curl in `L²`. -/
theorem fourier_mem_Hcurl_iff (f : Lp Mat3 2 (volume : Measure Freq)) :
    matrixFourierW f ∈ Whole.Hcurl ↔
      ∃ g : Lp Mat3 2 (volume : Measure Freq),
        ∀ φ : 𝓢(Freq, Mat3), ⟪f, (curlSch φ).toLp 2⟫ = ⟪g, φ.toLp 2⟫ := by
  constructor
  · intro h
    refine ⟨matrixFourierW.symm (curlW ⟨_, h⟩), (mem_Hcurl_iff_weak _ _).1 ⟨h, ?_⟩⟩
    rw [LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨g, hg⟩
    exact ((mem_Hcurl_iff_weak f g).2 hg).1

end Weak

end Feec.WholeWeak
