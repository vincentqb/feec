module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Feec.Ch4.Torus

/-!
# The Fourier-weight Sobolev spaces on `𝕋³` are the weak-derivative Sobolev spaces

`Feec.Ch4.Torus` models the periodic complex `H¹(𝕋³; V) → H(curl; 𝕋³, M) → L²(𝕋³; M)` of
[QuennevilleBelair2015, §4.10] (the periodic analogue of the complexes of §4.2, (4.2)) on the
Fourier side: `H¹`, `H(curl)`, `H(div)` are weighted-`ℓ²` conditions (`mulDomain`), and `grad`,
`curl`, `div` are Fourier multipliers with `ξ = 2πk`. Its module docstring notes that the
identification of these multipliers with weak derivatives of `L²(𝕋³)` functions was not
formalized there. This file proves that identification, with the honest definition of weak
derivative: test functions are *all* smooth functions on `𝕋³`, not only trigonometric
polynomials.

## Definitions

* `proj : ℝ³ → 𝕋³` is the covering map. `IsSmooth φ` means the `ℤ³`-periodic lift `φ ∘ proj` is
  `C^∞`. `partialT c φ x = d/dt φ(x + t e_c)|_{t=0}`; on smooth `φ` it is the classical partial
  derivative of the lift (`partialT_proj`).
* `HasWeakPartial j f g` (`g = ∂_j f` weakly) means `∫ f ∂_j φ = -∫ g φ` for every smooth `φ`.
  This is the analogue on `𝕋³` of the definition in [Brezis2011, §9.1]. It uses the bilinear pairing (no complex
  conjugation), as for distributions.
* More generally, `IsWeakFO α f g` (`g = Σ_{c,p} α_{cp} ∂_c f_p` weakly). Special cases are the
  weak gradient `IsWeakGrad` (`G_{ab} = ∂_b u_a`), the weak row-wise curl `IsWeakCurl`
  (`(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}`, the convention of `Feec.curl`) and the weak row-wise
  divergence `IsWeakDiv` (`(div A)_a = ∂_b A_{ab}`).

The measure on `𝕋³` is the one of `Feec.Torus.fieldFourier`, the normalized Haar measure, which
equals Mathlib's default `volume` (`Feec.Torus.volume_unitAddTorus_eq`). The normalization does
not affect the definition of weak derivatives.

## Main results

* Integration by parts on `𝕋³`: `integral_partialT_eq_zero` (`∫ ∂_c φ = 0`, by differentiating
  translation invariance of Haar measure under the integral sign) and hence
  `mFourierCoeff_partialT`: `(∂_c φ)^(k) = 2πi k_c φ̂(k)` for `C¹` functions. Also
  `isSmooth_mFourier` (characters are test functions), `partialT_mFourier`, and the Parseval
  pairing `hasSum_pairing`: `∫ f ψ = Σ_k ψ̂(-k) f̂(k)`.
* `isWeakFO_iff`: `g = Σ α_{cp} ∂_c f_p` weakly iff `ĝ(k) = Σ α_{cp} 2πi k_c f̂_p(k)` for all `k`.
* Scalar case: `hasWeakPartial_iff` (`(∂_j f)^(k) = 2πi k_j f̂(k)`), `HasWeakPartial.unique`, and
  **`exists_hasWeakPartial_iff`**: `f` has a weak `∂_j f ∈ L²` iff
  `Σ_k |2πk_j|² |f̂(k)|² < ∞`.
* Fields: `isWeakGrad_iff`, `isWeakCurl_iff`, `isWeakDiv_iff` give the Fourier coefficients of
  the weak operators as the symbols `gradSym`, `curlSym`, `divSym` of `Feec.Ch4.Torus`.
* The Sobolev spaces of `Feec.Ch4.Torus` (through `vectorFourier`/`matrixFourier`):
  - `vectorFourier_mem_gradT_domain_iff`, `exists_isWeakGrad_iff`: `H¹(𝕋³; ℂ³) = D(gradT)` is
    the set of fields with a weak gradient in `L²`.
  - `matrixFourier_mem_Hcurl_iff`: `Hcurl` is the set of fields with a weak curl in `L²`.
  - `matrixFourier_mem_Hdiv_iff`: `Hdiv` is the set of fields with a weak divergence in `L²`.
  - `matrixFourier_mem_H1M_iff`: `H1M` is the set of fields all of whose entries have all weak
    first partial derivatives in `L²`.
* The multipliers are the weak operators: `gradT_vectorFourier`, `curlT_matrixFourier`,
  `divT_matrixFourier` (`divT` is the Fourier multiplier `i A ξ` on `Hdiv`), and
  `adjoint_gradT_matrixFourier` (`grad* = -div` with the weak divergence).

No analytic hypotheses are assumed. Everything is proved from Mathlib's multivariate Fourier
series (`UnitAddTorus.mFourierBasis`, Parseval) and the dominated differentiation theorem.

## References

* [QuennevilleBelair2015], §4.2 ((4.2): `H¹`, `H(curl)`, `H(div)`), §4.10 (the complex
  `H¹(V) → H(curl; M) → L²(M)`)
* [Brezis2011], §9.1 (weak derivatives and the Sobolev spaces `W^{1,p}`)
* [AFW2010], [Arnold2018] (Hilbert complexes of Sobolev spaces)
-/

@[expose] public noncomputable section

open scoped ENNReal
open MeasureTheory Complex LinearPMap

namespace Feec.TorusWeak

open Feec.Torus

attribute [local instance] Feec.Torus.instMeasureSpaceUnitAddCircle_feec

/-- The flat torus `𝕋³ = ℝ³/ℤ³`. -/
abbrev T3 := UnitAddTorus (Fin 3)

/-- `L²(𝕋³; ℂ)`. -/
abbrev L2T := Lp ℂ 2 (volume : Measure T3)

/-- The local Haar measure on `ℝ/ℤ` is an additive Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The local Haar measure on `ℝ/ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The covering map `ℝ³ → 𝕋³`. -/
def proj (y : Fin 3 → ℝ) : T3 := fun i => (y i : UnitAddCircle)

/-- `proj` is additive. -/
theorem proj_add (y z : Fin 3 → ℝ) : proj (y + z) = proj y + proj z := by
  funext i; simp [proj]

/-- `proj 0 = 0`. -/
theorem proj_zero : proj 0 = 0 := by funext i; simp [proj]

/-- `proj` is an open quotient map (product of the quotient maps `ℝ → ℝ/ℤ`). -/
theorem isOpenQuotientMap_proj : IsOpenQuotientMap proj :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

/-- `proj` is surjective. -/
theorem proj_surjective : Function.Surjective proj := isOpenQuotientMap_proj.surjective

/-- A function on `𝕋³` is continuous if its periodic lift is. -/
theorem continuous_of_comp_proj {φ : T3 → ℂ} (h : Continuous (φ ∘ proj)) : Continuous φ :=
  isOpenQuotientMap_proj.isQuotientMap.continuous_iff.2 h

/-- Continuous functions on the compact torus are integrable. -/
theorem integrable_of_continuous {φ : T3 → ℂ} (h : Continuous φ) : Integrable φ :=
  h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace φ)

/-- `Pi.single c t = t • e_c`. -/
theorem single_eq_smul (c : Fin 3) (t : ℝ) :
    (Pi.single c t : Fin 3 → ℝ) = t • (Pi.single c (1 : ℝ) : Fin 3 → ℝ) := by
  ext i; by_cases h : i = c <;> simp [h]

/-- The partial derivative `∂_c φ (x) = d/dt φ(x + t e_c)|_{t=0}` of a function on `𝕋³`. -/
def partialT (c : Fin 3) (φ : T3 → ℂ) (x : T3) : ℂ :=
  deriv (fun t : ℝ => φ (x + proj (Pi.single c t))) 0

/-- Smooth functions on `𝕋³`: those whose `ℤ³`-periodic lift to `ℝ³` is `C^∞`. -/
def IsSmooth (φ : T3 → ℂ) : Prop := ContDiff ℝ (⊤ : ℕ∞) (φ ∘ proj)

/-- Chain rule along `t ↦ proj (y + t e_c)`. -/
theorem hasDerivAt_lift {φ : T3 → ℂ} (hφ : Differentiable ℝ (φ ∘ proj)) (c : Fin 3)
    (y : Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => φ (proj y + proj (Pi.single c t)))
      (fderiv ℝ (φ ∘ proj) (y + Pi.single c s) (Pi.single c 1)) s := by
  have h1 : HasDerivAt (fun t : ℝ => y + t • (Pi.single c (1 : ℝ) : Fin 3 → ℝ))
      (Pi.single c 1) s := by
    simpa using ((hasDerivAt_id s).smul_const (Pi.single c (1 : ℝ) : Fin 3 → ℝ)).const_add y
  have h2 := (hφ (y + s • Pi.single c 1)).hasFDerivAt.comp_hasDerivAt s h1
  rw [single_eq_smul c s]
  convert h2 using 1
  funext t
  simp [Function.comp, ← proj_add, single_eq_smul c t]

/-- For a differentiable lift, `∂_c φ (proj y)` is the classical partial derivative
`D(φ ∘ proj)(y) e_c` of the periodic lift. -/
theorem partialT_proj {φ : T3 → ℂ} (hφ : Differentiable ℝ (φ ∘ proj)) (c : Fin 3)
    (y : Fin 3 → ℝ) : partialT c φ (proj y) = fderiv ℝ (φ ∘ proj) y (Pi.single c 1) := by
  unfold partialT
  simpa using (hasDerivAt_lift hφ c y 0).deriv

/-- `t ↦ φ(x + t e_c)` has derivative `∂_c φ (x + t e_c)` at every `t`. -/
theorem hasDerivAt_translate {φ : T3 → ℂ} (hφ : Differentiable ℝ (φ ∘ proj)) (c : Fin 3)
    (x : T3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (x + proj (Pi.single c s)))
      (partialT c φ (x + proj (Pi.single c t))) t := by
  obtain ⟨y, rfl⟩ := proj_surjective x
  rw [← proj_add, partialT_proj hφ]
  exact hasDerivAt_lift hφ c y t

/-- `∂_c φ` is continuous for `C¹` lifts. -/
theorem continuous_partialT {φ : T3 → ℂ} (hφ : ContDiff ℝ 1 (φ ∘ proj)) (c : Fin 3) :
    Continuous (partialT c φ) := by
  apply continuous_of_comp_proj
  have hd : Differentiable ℝ (φ ∘ proj) := hφ.differentiable one_ne_zero
  have : partialT c φ ∘ proj = fun y => fderiv ℝ (φ ∘ proj) y (Pi.single c 1) :=
    funext fun y => partialT_proj hd c y
  rw [this]
  exact (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- `∫_{𝕋³} ∂_c φ = 0` for `C¹` lifts: differentiate the translation invariance
`∫ φ(x + t e_c) dx = ∫ φ` under the integral sign. -/
theorem integral_partialT_eq_zero {φ : T3 → ℂ} (hφ : ContDiff ℝ 1 (φ ∘ proj)) (c : Fin 3) :
    ∫ x, partialT c φ x = 0 := by
  have hd : Differentiable ℝ (φ ∘ proj) := hφ.differentiable one_ne_zero
  have hc : Continuous φ := continuous_of_comp_proj hφ.continuous
  have hc' := continuous_partialT hφ c
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖partialT c φ x‖ ≤ C :=
    ⟨‖(⟨_, hc'⟩ : C(T3, ℂ))‖, fun x => (⟨_, hc'⟩ : C(T3, ℂ)).norm_coe_le_norm x⟩
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (0 : ℝ))
    (F := fun t x => φ (x + proj (Pi.single c t)))
    (F' := fun t x => partialT c φ (x + proj (Pi.single c t))) (bound := fun _ => C)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      (hc.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    (integrable_of_continuous (hc.comp (continuous_id.add continuous_const)))
    (hc'.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t _ => hC _) (integrable_const C)
    (Filter.Eventually.of_forall fun x t _ => hasDerivAt_translate hd c x t)
  have hconst : (fun t : ℝ => ∫ x, φ (x + proj (Pi.single c t))) = fun _ => ∫ x, φ x :=
    funext fun t => integral_add_right_eq_self φ _
  rw [hconst] at key
  have := key.2.unique (hasDerivAt_const _ _)
  simpa [proj_zero] using this

/-- Product rule for `∂_c`. -/
theorem partialT_mul {φ ψ : T3 → ℂ} (hφ : Differentiable ℝ (φ ∘ proj))
    (hψ : Differentiable ℝ (ψ ∘ proj)) (c : Fin 3) (x : T3) :
    partialT c (fun x => φ x * ψ x) x = partialT c φ x * ψ x + φ x * partialT c ψ x := by
  have := ((hasDerivAt_translate hφ c x 0).mul (hasDerivAt_translate hψ c x 0)).deriv
  simp only [Pi.single_zero, proj_zero, add_zero] at this
  unfold partialT at this ⊢
  exact this

/-- The characters in coordinates: `e_n(proj y) = exp(2πi n·y)`. -/
theorem mFourier_proj (n : Fin 3 → ℤ) (y : Fin 3 → ℝ) :
    UnitAddTorus.mFourier n (proj y) = cexp (2 * Real.pi * I * ∑ i, (n i : ℂ) * (y i : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, proj, fourier_coe_apply,
    Finset.mul_sum, ← Complex.exp_sum]
  congr 1; refine Finset.sum_congr rfl fun i _ => ?_; push_cast; ring

/-- `e_n ∘ proj = exp(2πi n·y)`. -/
theorem mFourier_comp_proj (n : Fin 3 → ℤ) :
    UnitAddTorus.mFourier n ∘ proj =
      fun y => cexp (2 * Real.pi * I * ∑ i, (n i : ℂ) * (y i : ℂ)) :=
  funext (mFourier_proj n)

/-- The characters `e_n` are smooth test functions. -/
theorem isSmooth_mFourier (n : Fin 3 → ℤ) : IsSmooth (UnitAddTorus.mFourier n) := by
  unfold IsSmooth
  rw [mFourier_comp_proj]
  refine Complex.contDiff_exp.comp (contDiff_const.mul ?_)
  refine ContDiff.sum fun i _ => contDiff_const.mul ?_
  exact Complex.ofRealCLM.contDiff.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).contDiff

/-- `∂_c e_n = 2πi n_c e_n`. -/
theorem partialT_mFourier (n : Fin 3 → ℤ) (c : Fin 3) (x : T3) :
    partialT c (UnitAddTorus.mFourier n) x =
      2 * Real.pi * I * n c * UnitAddTorus.mFourier n x := by
  obtain ⟨y, rfl⟩ := proj_surjective x
  unfold partialT
  have hfun : (fun t : ℝ => UnitAddTorus.mFourier n (proj y + proj (Pi.single c t))) =
      fun t : ℝ => cexp (2 * Real.pi * I * ∑ i, (n i : ℂ) * (y i : ℂ) +
        2 * Real.pi * I * n c * (t : ℂ)) := by
    funext t
    rw [← proj_add, mFourier_proj]
    congr 1
    simp only [Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single c (fun i _ hi => by simp [hi]) (by simp)]
    simp; ring
  rw [hfun, mFourier_proj]
  have h : HasDerivAt (fun t : ℝ => cexp (2 * Real.pi * I * ∑ i, (n i : ℂ) * (y i : ℂ) +
      2 * Real.pi * I * n c * (t : ℂ)))
      (cexp (2 * Real.pi * I * ∑ i, (n i : ℂ) * (y i : ℂ) + 2 * Real.pi * I * n c * ((0:ℝ) : ℂ))
        * (2 * Real.pi * I * n c * 1)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul _ |>.const_add _).cexp
  rw [h.deriv]; simp; ring

open UnitAddTorus in
/-- **Integration by parts on `𝕋³`**: `(∂_c φ)^(k) = 2πi k_c φ̂(k)` for `C¹` functions. -/
theorem mFourierCoeff_partialT {φ : T3 → ℂ} (hφ : ContDiff ℝ 1 (φ ∘ proj)) (c : Fin 3)
    (k : Fin 3 → ℤ) :
    mFourierCoeff (partialT c φ) k = 2 * Real.pi * I * k c * mFourierCoeff φ k := by
  have he : ContDiff ℝ 1 (mFourier (-k) ∘ proj) :=
    (isSmooth_mFourier (-k)).of_le (by exact_mod_cast le_top)
  have hψ : ContDiff ℝ 1 ((fun x => mFourier (-k) x * φ x) ∘ proj) := he.mul hφ
  have h0 := integral_partialT_eq_zero hψ c
  have hpt : ∀ x, partialT c (fun x => mFourier (-k) x * φ x) x =
      (-(2 * Real.pi * I * k c)) * (mFourier (-k) x * φ x) + mFourier (-k) x * partialT c φ x :=
    fun x => by
      rw [partialT_mul (he.differentiable one_ne_zero) (hφ.differentiable one_ne_zero),
        partialT_mFourier]
      simp only [Pi.neg_apply, Int.cast_neg]; ring
  have hcφ : Continuous φ := continuous_of_comp_proj hφ.continuous
  simp_rw [hpt] at h0
  have i1 : Integrable fun x => -(2 * Real.pi * I * k c) * (mFourier (-k) x * φ x) :=
    integrable_of_continuous (continuous_const.mul ((mFourier (-k)).continuous.mul hcφ))
  have i2 : Integrable fun x => mFourier (-k) x * partialT c φ x :=
    integrable_of_continuous ((mFourier (-k)).continuous.mul (continuous_partialT hφ c))
  rw [integral_add i1 i2, integral_const_mul] at h0
  simp only [mFourierCoeff, smul_eq_mul]
  linear_combination h0

/-- `L²` functions times bounded continuous functions are integrable on `𝕋³`. -/
theorem integrable_mul_continuous (f : L2T) {ψ : T3 → ℂ} (hψ : Continuous ψ) :
    Integrable (fun x => f x * ψ x) :=
  ((Lp.memLp f).integrable one_le_two).mul_bdd hψ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (⟨ψ, hψ⟩ : C(T3, ℂ)).norm_coe_le_norm x)

open UnitAddTorus in
/-- **Parseval pairing** (no complex conjugation): `∫ f ψ = Σ_k ψ̂(-k) f̂(k)`. -/
theorem hasSum_pairing (f : L2T) {ψ : T3 → ℂ} (hψ : Continuous ψ) :
    HasSum (fun k => mFourierCoeff ψ (-k) * mFourierCoeff f k) (∫ x, f x * ψ x) := by
  let g : C(T3, ℂ) := ⟨fun x => (starRingEnd ℂ) (ψ x), continuous_conj.comp hψ⟩
  have h := hasSum_prod_mFourierCoeff (g.toLp 2 volume ℂ) f
  have h1 : ∀ i, (starRingEnd ℂ) (mFourierCoeff (g.toLp 2 volume ℂ : T3 → ℂ) i) =
      mFourierCoeff ψ (-i) := fun i => by
    rw [mFourierCoeff_toLp, mFourierCoeff, mFourierCoeff, ← integral_conj]
    congr 1; funext t
    simp [g, neg_neg, mFourier_neg]
  have h2 : ∫ t, (starRingEnd ℂ) ((g.toLp 2 volume ℂ : T3 → ℂ) t) * f t = ∫ x, f x * ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := volume) g] with t ht
    rw [ht]; simp [g, mul_comm]
  simp_rw [h1, h2] at h
  exact h

/-- `IsSmooth` functions are `C¹` (in the lift). -/
theorem IsSmooth.contDiff_one {φ : T3 → ℂ} (h : IsSmooth φ) : ContDiff ℝ 1 (φ ∘ proj) :=
  h.of_le (by exact_mod_cast le_top)

/-- `IsSmooth` functions are continuous on `𝕋³`. -/
theorem IsSmooth.continuous {φ : T3 → ℂ} (h : IsSmooth φ) : Continuous φ :=
  continuous_of_comp_proj (show ContDiff ℝ _ (φ ∘ proj) from h).continuous

section FirstOrder

variable {P : Type*} [Fintype P]

/-- **Weak constant-coefficient first-order operators.** `g = Σ_{c,p} α_{cp} ∂_c f_p` holds
weakly (in the sense of distributions) if `∫ Σ_{c,p} α_{cp} f_p ∂_c φ = -∫ g φ` for every smooth
`φ` on `𝕋³`. -/
def IsWeakFO (α : Fin 3 → P → ℂ) (f : P → L2T) (g : L2T) : Prop :=
  ∀ φ : T3 → ℂ, IsSmooth φ →
    ∫ x, ∑ c, ∑ p, α c p * (f p x * partialT c φ x) = -∫ x, g x * φ x

/-- The integral in `IsWeakFO` splits into the pairings `∫ f_p ∂_c φ`. -/
theorem integral_sum_fo (α : Fin 3 → P → ℂ) (f : P → L2T) {φ : T3 → ℂ} (hφ : IsSmooth φ) :
    ∫ x, ∑ c, ∑ p, α c p * (f p x * partialT c φ x) =
      ∑ c, ∑ p, α c p * ∫ x, f p x * partialT c φ x := by
  have hi : ∀ c p, Integrable fun x => f p x * partialT c φ x := fun c p =>
    integrable_mul_continuous (f p) (continuous_partialT hφ.contDiff_one c)
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun p _ => (hi c p).const_mul _]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun p _ => (hi c p).const_mul _]
  exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _

open UnitAddTorus in
/-- **Fourier characterization of weak first-order operators**: `g = Σ α_{cp} ∂_c f_p` weakly
iff `ĝ(k) = Σ α_{cp} 2πi k_c f̂_p(k)` for all `k ∈ ℤ³`. -/
theorem isWeakFO_iff (α : Fin 3 → P → ℂ) (f : P → L2T) (g : L2T) :
    IsWeakFO α f g ↔ ∀ k, mFourierCoeff g k =
      ∑ c, ∑ p, α c p * (2 * Real.pi * I * k c * mFourierCoeff (f p) k) := by
  constructor
  · intro h k
    have := h _ (isSmooth_mFourier (-k))
    rw [integral_sum_fo α f (isSmooth_mFourier (-k))] at this
    have hc : ∀ c p, ∫ x, f p x * partialT c (mFourier (-k)) x =
        -(2 * Real.pi * I * k c * mFourierCoeff (f p) k) := fun c p => by
      simp_rw [partialT_mFourier, mFourierCoeff, smul_eq_mul]
      rw [neg_mul_eq_neg_mul, ← integral_const_mul]
      congr 1; funext x; simp only [Pi.neg_apply, Int.cast_neg]; ring
    have hg : ∫ x, g x * mFourier (-k) x = mFourierCoeff g k := by
      simp_rw [mFourierCoeff, smul_eq_mul, mul_comm]
    simp_rw [hc, hg] at this
    simp only [mul_neg, Finset.sum_neg_distrib, neg_inj] at this
    exact this.symm
  · intro h φ hφ
    rw [integral_sum_fo α f hφ]
    have hs : ∀ c p, HasSum (fun k => -(2 * Real.pi * I * k c) * mFourierCoeff φ (-k) *
        mFourierCoeff (f p) k) (∫ x, f p x * partialT c φ x) := fun c p => by
      convert hasSum_pairing (f p) (continuous_partialT hφ.contDiff_one c) using 2 with k
      rw [mFourierCoeff_partialT hφ.contDiff_one]
      simp only [Pi.neg_apply, Int.cast_neg]; ring
    have htot : HasSum (fun k => ∑ c, ∑ p, α c p *
        (-(2 * Real.pi * I * k c) * mFourierCoeff φ (-k) * mFourierCoeff (f p) k))
        (∑ c, ∑ p, α c p * ∫ x, f p x * partialT c φ x) :=
      hasSum_sum fun c _ => hasSum_sum fun p _ => (hs c p).mul_left _
    have hg := (hasSum_pairing g hφ.continuous).neg
    refine htot.unique (hg.congr_fun fun k => ?_)
    rw [h k, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring

end FirstOrder

section Scalar

open UnitAddTorus

/-- The `L²` function with prescribed Fourier coefficients `a ∈ ℓ²(ℤ³)` (inverse Fourier). -/
def ofCoeff (a : lp (fun _ : Fin 3 → ℤ => ℂ) 2) : L2T := mFourierBasis.repr.symm a

/-- The Fourier coefficients of `ofCoeff a` are `a`. -/
@[simp] theorem mFourierCoeff_ofCoeff (a : lp (fun _ : Fin 3 → ℤ => ℂ) 2) (k : Fin 3 → ℤ) :
    mFourierCoeff (ofCoeff a : T3 → ℂ) k = a k := by
  rw [ofCoeff, ← mFourierBasis_repr, LinearIsometryEquiv.apply_symm_apply]

/-- `L²` functions are determined by their Fourier coefficients. -/
theorem eq_of_mFourierCoeff_eq {f g : L2T}
    (h : ∀ k, mFourierCoeff (f : T3 → ℂ) k = mFourierCoeff (g : T3 → ℂ) k) : f = g := by
  apply (mFourierBasis (d := Fin 3)).repr.injective
  ext k
  rw [mFourierBasis_repr, mFourierBasis_repr, h]

/-- **Weak partial derivative** on `𝕋³`: `g = ∂_j f` in `L²` if `∫ f ∂_j φ = -∫ g φ` for every
smooth (`C^∞`) function `φ` on `𝕋³`. -/
def HasWeakPartial (j : Fin 3) (f g : L2T) : Prop :=
  ∀ φ : T3 → ℂ, IsSmooth φ → ∫ x, f x * partialT j φ x = -∫ x, g x * φ x

/-- `HasWeakPartial` is the special case `α_c = δ_{cj}` of `IsWeakFO`. -/
theorem hasWeakPartial_iff_isWeakFO (j : Fin 3) (f g : L2T) :
    HasWeakPartial j f g ↔
      IsWeakFO (fun c (_ : Unit) => if c = j then (1 : ℂ) else 0) (fun _ => f) g := by
  unfold HasWeakPartial IsWeakFO
  simp [ite_mul]

/-- **Fourier characterization of the weak partial derivative**:
`g = ∂_j f` weakly iff `ĝ(k) = 2πi k_j f̂(k)` for all `k ∈ ℤ³`. -/
theorem hasWeakPartial_iff (j : Fin 3) (f g : L2T) :
    HasWeakPartial j f g ↔ ∀ k, mFourierCoeff (g : T3 → ℂ) k =
      2 * Real.pi * I * k j * mFourierCoeff (f : T3 → ℂ) k := by
  rw [hasWeakPartial_iff_isWeakFO, isWeakFO_iff]
  simp

/-- Weak partial derivatives are unique. -/
theorem HasWeakPartial.unique {j : Fin 3} {f g₁ g₂ : L2T} (h₁ : HasWeakPartial j f g₁)
    (h₂ : HasWeakPartial j f g₂) : g₁ = g₂ :=
  eq_of_mFourierCoeff_eq fun k => by
    rw [(hasWeakPartial_iff j f g₁).1 h₁ k, (hasWeakPartial_iff j f g₂).1 h₂ k]

/-- **Weak `∂_j`-differentiability in `L²` is the Fourier-weight condition**:
`f` has a weak derivative `∂_j f ∈ L²` iff `Σ_k |2π k_j|² |f̂(k)|² < ∞`. -/
theorem exists_hasWeakPartial_iff (j : Fin 3) (f : L2T) :
    (∃ g, HasWeakPartial j f g) ↔
      Summable fun k : Fin 3 → ℤ =>
        (2 * Real.pi * k j) ^ 2 * ‖mFourierCoeff (f : T3 → ℂ) k‖ ^ 2 := by
  have hn : ∀ k : Fin 3 → ℤ, ‖2 * Real.pi * I * k j * mFourierCoeff (f : T3 → ℂ) k‖ ^ 2 =
      (2 * Real.pi * k j) ^ 2 * ‖mFourierCoeff (f : T3 → ℂ) k‖ ^ 2 := fun k => by
    rw [norm_mul, mul_pow]
    congr 1
    rw [show (2 * Real.pi * I * k j : ℂ) = ((2 * Real.pi * k j : ℝ) : ℂ) * I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  constructor
  · rintro ⟨g, hg⟩
    have := (hasSum_sq_mFourierCoeff g).summable
    simp_rw [(hasWeakPartial_iff j f g).1 hg, hn] at this
    exact this
  · intro hs
    have hm : Memℓp (fun k : Fin 3 → ℤ => 2 * Real.pi * I * k j * mFourierCoeff (f : T3 → ℂ) k) 2 :=
      memℓp_gen (by simp only [ENNReal.toReal_ofNat, Real.rpow_two, hn]; exact hs)
    refine ⟨ofCoeff ⟨_, hm⟩, (hasWeakPartial_iff j f _).2 fun k => ?_⟩
    rw [mFourierCoeff_ofCoeff]

end Scalar

section Fields

open UnitAddTorus

/-- `L²` vector fields `𝕋³ → ℂ³` (the physical-side model of `L2V`). -/
abbrev VField := PiLp 2 fun _ : Fin 3 => L2T

/-- `L²` matrix fields `𝕋³ → ℂ³ˣ³` (the physical-side model of `L2M`). -/
abbrev MField := PiLp 2 fun _ : Fin 3 × Fin 3 => L2T

/-- Entries of `freq k = 2πk`. -/
theorem freq_apply (k : Z3) (c : Fin 3) : freq k c = 2 * Real.pi * k c := rfl

/-- `vectorFourier u k a` is the `k`-th Fourier coefficient of `u_a`. -/
theorem vectorFourier_apply' (u : VField) (k : Z3) (a : Fin 3) :
    vectorFourier u k a = mFourierCoeff (u a : T3 → ℂ) k :=
  fieldFourier_apply _ u k a

/-- **Weak gradient**: `G = ∇u`, `G_{ab} = ∂_b u_a`, in the weak sense. -/
def IsWeakGrad (u : VField) (G : MField) : Prop := ∀ a b, HasWeakPartial b (u a) (G (a, b))

/-- **Weak row-wise curl** `(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}` (thesis convention, `Feec.curl`):
`∫ Σ_{c,d} ε_{bcd} A_{ad} ∂_c φ = -∫ C_{ab} φ` for all smooth `φ`. -/
def IsWeakCurl (A C : MField) : Prop :=
  ∀ a b, ∀ φ : T3 → ℂ, IsSmooth φ →
    ∫ x, ∑ c, ∑ d, (eps3 b c d : ℂ) * (A (a, d) x * partialT c φ x) = -∫ x, C (a, b) x * φ x

/-- **Weak row-wise divergence** `(div A)_a = Σ_b ∂_b A_{ab}`:
`∫ Σ_b A_{ab} ∂_b φ = -∫ D_a φ` for all smooth `φ`. -/
def IsWeakDiv (A : MField) (D : VField) : Prop :=
  ∀ a, ∀ φ : T3 → ℂ, IsSmooth φ → ∫ x, ∑ b, A (a, b) x * partialT b φ x = -∫ x, D a x * φ x

/-- The weak gradient in Fourier variables: `Ĝ(k) = i û(k) ξ_kᵀ` (`gradSym`). -/
theorem isWeakGrad_iff (u : VField) (G : MField) :
    IsWeakGrad u G ↔ ∀ k, matrixFourier G k = gradSym (freq k) (vectorFourier u k) := by
  simp only [IsWeakGrad, hasWeakPartial_iff]
  constructor
  · intro h k; ext ⟨a, b⟩
    rw [matrixFourier_apply, h a b k, gradSym_apply, vectorFourier_apply', freq_apply]
    push_cast; ring
  · intro h a b k
    have := congrArg (fun M : Mat3 => M (a, b)) (h k)
    simp only [matrixFourier_apply, gradSym_apply, vectorFourier_apply', freq_apply] at this
    rw [this]; push_cast; ring

/-- The weak curl in Fourier variables: `Ĉ(k) = curlSym ξ_k Â(k)`. -/
theorem isWeakCurl_iff (A C : MField) :
    IsWeakCurl A C ↔ ∀ k, matrixFourier C k = curlSym (freq k) (matrixFourier A k) := by
  have e : ∀ a b, (∀ φ : T3 → ℂ, IsSmooth φ →
      ∫ x, ∑ c, ∑ d, (eps3 b c d : ℂ) * (A (a, d) x * partialT c φ x) =
        -∫ x, C (a, b) x * φ x) ↔ ∀ k, mFourierCoeff (C (a, b) : T3 → ℂ) k =
        ∑ c, ∑ d, (eps3 b c d : ℂ) *
          (2 * Real.pi * I * k c * mFourierCoeff (A (a, d) : T3 → ℂ) k) :=
    fun a b => isWeakFO_iff (fun c d => (eps3 b c d : ℂ)) (fun d => A (a, d)) (C (a, b))
  have hs : ∀ k a b, curlSym (freq k) (matrixFourier A k) (a, b) =
      ∑ c, ∑ d, (eps3 b c d : ℂ) * (2 * Real.pi * I * k c * mFourierCoeff (A (a, d) : T3 → ℂ) k) :=
    fun k a b => by
      rw [curlSym_apply, jM_apply, curlR_apply_eps3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [matrixFourier_apply, freq_apply]; push_cast; ring
  unfold IsWeakCurl
  simp only [e]
  constructor
  · intro h k; ext ⟨a, b⟩
    rw [matrixFourier_apply, h a b k, hs]
  · intro h a b k
    rw [← hs, ← h k, matrixFourier_apply]

/-- The weak divergence in Fourier variables: `D̂(k) = divSym ξ_k Â(k) = i Â(k) ξ_k`. -/
theorem isWeakDiv_iff (A : MField) (D : VField) :
    IsWeakDiv A D ↔ ∀ k, vectorFourier D k = divSym (freq k) (matrixFourier A k) := by
  have e : ∀ a, (∀ φ : T3 → ℂ, IsSmooth φ →
      ∫ x, ∑ b, A (a, b) x * partialT b φ x = -∫ x, D a x * φ x) ↔
      ∀ k, mFourierCoeff (D a : T3 → ℂ) k = ∑ c, ∑ b, (if c = b then (1 : ℂ) else 0) *
        (2 * Real.pi * I * k c * mFourierCoeff (A (a, b) : T3 → ℂ) k) := fun a => by
    rw [← isWeakFO_iff]
    unfold IsWeakFO
    simp [ite_mul]
  have hs : ∀ k a, divSym (freq k) (matrixFourier A k) a = ∑ c, ∑ b,
      (if c = b then (1 : ℂ) else 0) *
        (2 * Real.pi * I * k c * mFourierCoeff (A (a, b) : T3 → ℂ) k) := fun k a => by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      divSym_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [matrixFourier_apply, freq_apply]; push_cast; ring
  unfold IsWeakDiv
  simp only [e]
  constructor
  · intro h k; ext a
    rw [vectorFourier_apply', h a k, hs]
  · intro h a k
    rw [← hs, ← h k, vectorFourier_apply']

end Fields

section Sobolev

open UnitAddTorus

/-- The periodic row-wise divergence on the Fourier side, `A ↦ (i Â(k) ξ_k)_k`, with domain
`Hdiv`; `gradT† = -divT` (`adjoint_gradT`). -/
def divT : L2M →ₗ.[ℝ] L2V := mulOp fun k => divSym (freq k)

/-- The domain of `divT` is `Hdiv`. -/
theorem divT_domain : divT.domain = Hdiv := rfl

/-- The domain of `gradT` (`H¹(𝕋³; ℂ³)` on the Fourier side). -/
theorem gradT_domain : gradT.domain = mulDomain fun k => gradSym (freq k) := rfl

/-- **`H¹(𝕋³; ℂ³)` is the weak-gradient space**: the Fourier-defined domain of `grad` consists
exactly of the `L²` vector fields with a weak gradient in `L²`. -/
theorem vectorFourier_mem_gradT_domain_iff (u : VField) :
    vectorFourier u ∈ gradT.domain ↔ ∃ G, IsWeakGrad u G := by
  rw [gradT_domain, mem_mulDomain]
  constructor
  · intro h
    refine ⟨matrixFourier.symm ⟨_, h⟩, (isWeakGrad_iff _ _).2 fun k => ?_⟩
    rw [LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨G, hG⟩
    rw [show (fun k => gradSym (freq k) _) = ((matrixFourier G : _) : Z3 → _) from
      funext fun k => ((isWeakGrad_iff u G).1 hG k).symm]
    exact lp.memℓp _

/-- A weak gradient exists iff every component has every weak partial derivative in `L²`. -/
theorem exists_isWeakGrad_iff (u : VField) :
    (∃ G, IsWeakGrad u G) ↔ ∀ a b, ∃ g, HasWeakPartial b (u a) g := by
  constructor
  · rintro ⟨G, hG⟩ a b; exact ⟨_, hG a b⟩
  · intro h
    choose g hg using h
    exact ⟨WithLp.toLp 2 fun p => g p.1 p.2, fun a b => hg a b⟩

/-- **The Fourier multiplier `gradT` is the weak gradient.** -/
theorem gradT_vectorFourier {u : VField} {G : MField} (h : IsWeakGrad u G)
    (hu : vectorFourier u ∈ gradT.domain) : gradT ⟨vectorFourier u, hu⟩ = matrixFourier G :=
  lp.ext <| funext fun k => ((isWeakGrad_iff u G).1 h k).symm

/-- **`H(curl; 𝕋³)` is the weak-curl space**: `Hcurl` (Fourier weights) consists exactly of the
`L²` matrix fields with a weak row-wise curl in `L²`. -/
theorem matrixFourier_mem_Hcurl_iff (A : MField) :
    matrixFourier A ∈ Hcurl ↔ ∃ C, IsWeakCurl A C := by
  rw [Hcurl, mem_mulDomain]
  constructor
  · intro h
    refine ⟨matrixFourier.symm ⟨_, h⟩, (isWeakCurl_iff _ _).2 fun k => ?_⟩
    rw [LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨C, hC⟩
    rw [show (fun k => curlSym (freq k) _) = ((matrixFourier C : _) : Z3 → _) from
      funext fun k => ((isWeakCurl_iff A C).1 hC k).symm]
    exact lp.memℓp _

/-- **The Fourier multiplier `curlT` is the weak curl.** -/
theorem curlT_matrixFourier {A C : MField} (h : IsWeakCurl A C)
    (hA : matrixFourier A ∈ curlT.domain) : curlT ⟨matrixFourier A, hA⟩ = matrixFourier C :=
  lp.ext <| funext fun k => ((isWeakCurl_iff A C).1 h k).symm

/-- **`H(div; 𝕋³)` is the weak-divergence space.** -/
theorem matrixFourier_mem_Hdiv_iff (A : MField) :
    matrixFourier A ∈ Hdiv ↔ ∃ D, IsWeakDiv A D := by
  rw [Hdiv, mem_mulDomain]
  constructor
  · intro h
    refine ⟨vectorFourier.symm ⟨_, h⟩, (isWeakDiv_iff _ _).2 fun k => ?_⟩
    rw [LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨D, hD⟩
    rw [show (fun k => divSym (freq k) _) = ((vectorFourier D : _) : Z3 → _) from
      funext fun k => ((isWeakDiv_iff A D).1 hD k).symm]
    exact lp.memℓp _

/-- **The Fourier multiplier `divT` is the weak divergence.** -/
theorem divT_matrixFourier {A : MField} {D : VField} (h : IsWeakDiv A D)
    (hA : matrixFourier A ∈ divT.domain) : divT ⟨matrixFourier A, hA⟩ = vectorFourier D :=
  lp.ext <| funext fun k => ((isWeakDiv_iff A D).1 h k).symm

/-- The Hilbert adjoint of the periodic gradient is minus the weak divergence:
`grad* A = -div A` for `A ∈ D(grad*) = H(div)`. -/
theorem adjoint_gradT_matrixFourier {A : MField} {D : VField} (h : IsWeakDiv A D)
    (hA : matrixFourier A ∈ gradT†.domain) : gradT† ⟨matrixFourier A, hA⟩ = -vectorFourier D := by
  have key : ∀ (T : L2M →ₗ.[ℝ] L2V), T = (mulOp fun k => -divSym (freq k)) →
      ∀ hx : matrixFourier A ∈ T.domain, T ⟨matrixFourier A, hx⟩ = -vectorFourier D := by
    rintro T rfl hx
    refine lp.ext <| funext fun k => ?_
    rw [mulOp_apply]
    simp only [_root_.neg_apply, lp.coeFn_neg, Pi.neg_apply]
    rw [(isWeakDiv_iff A D).1 h k]
  exact key _ adjoint_gradT hA

/-- A finite double sum of nonnegative sequences is summable iff each one is. -/
theorem summable_sum_sum_iff {P Q : Type*} [Fintype P] [Fintype Q] {F : Z3 → P → Q → ℝ}
    (hF : ∀ k p q, 0 ≤ F k p q) :
    (Summable fun k => ∑ p, ∑ q, F k p q) ↔ ∀ p q, Summable fun k => F k p q := by
  constructor
  · intro h p q
    refine h.of_nonneg_of_le (fun k => hF k p q) fun k => ?_
    calc F k p q ≤ ∑ q', F k p q' :=
          Finset.single_le_sum (fun q' _ => hF k p q') (Finset.mem_univ q)
      _ ≤ ∑ p', ∑ q', F k p' q' :=
          Finset.single_le_sum (f := fun p' => ∑ q', F k p' q')
            (fun p' _ => Finset.sum_nonneg fun q' _ => hF k p' q') (Finset.mem_univ p)
  · intro h
    exact summable_sum fun p _ => summable_sum fun q _ => h p q

/-- **`H¹(𝕋³; ℂ³ˣ³)` is the weak-`H¹` space**: `H1M` (the weight `|ξ_k|`) consists exactly of
the `L²` matrix fields all of whose entries have all three weak partial derivatives in `L²`. -/
theorem matrixFourier_mem_H1M_iff (A : MField) :
    matrixFourier A ∈ H1M ↔ ∀ p c, ∃ g, HasWeakPartial c (A p) g := by
  simp_rw [exists_hasWeakPartial_iff]
  rw [H1M, mem_mulDomain, memℓp_gen_iff (by norm_num)]
  have e : ∀ k, ‖(‖freq k‖ • ContinuousLinearMap.id ℝ Mat3) ((matrixFourier A : L2M) k)‖ ^
      (2 : ℝ≥0∞).toReal = ∑ p, ∑ c, (2 * Real.pi * k c) ^ 2 *
        ‖mFourierCoeff (A p : T3 → ℂ) k‖ ^ 2 := fun k => by
    rw [ENNReal.toReal_ofNat, Real.rpow_two, _root_.smul_apply,
      ContinuousLinearMap.id_apply, norm_smul, norm_norm, mul_pow, norm_sq_freq,
      EuclideanSpace.norm_sq_eq, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
    rw [freq_apply, matrixFourier_apply]
  rw [show (fun k => ‖(‖freq k‖ • ContinuousLinearMap.id ℝ Mat3) ((matrixFourier A : L2M) k)‖ ^
      (2 : ℝ≥0∞).toReal) = _ from funext e]
  exact summable_sum_sum_iff fun _ _ _ => by positivity

end Sobolev

end Feec.TorusWeak
