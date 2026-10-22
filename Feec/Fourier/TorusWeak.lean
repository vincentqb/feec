module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Analytic.Uniqueness
public import Feec.Fourier.Torus
public import Feec.Fourier.Weak

/-!
# Fourier multipliers on `𝕋ᵈ` are weak derivatives

The torus model of a constant-coefficient complex (`Feec.Fourier.Torus.complex`) defines its
Sobolev spaces as domains of multiplication operators on the Fourier coefficients. This file
identifies them with the weak-derivative spaces of `L²(𝕋ᵈ)`, in any dimension and for every
first-order constant-coefficient operator between fields with values in `ℂᴾ` and `ℂ^Q`, with the
honest definition of weak derivative: the test functions are **all** smooth functions on `𝕋ᵈ`
(not only trigonometric polynomials). It is the periodic counterpart of `Feec.Fourier.Weak`.

## Definitions

* `proj : ℝᵈ → 𝕋ᵈ`, the covering map. `IsSmooth φ`: the `ℤᵈ`-periodic lift `φ ∘ proj` is `C^∞`.
  `partialT c φ x = d/dt φ(x + t e_c)|_{t=0}`; on smooth `φ` it is the classical partial
  derivative of the lift (`partialT_proj`).
* `IsWeakFO α f g` (`g = Σ_{c,p} α_{cp} ∂_c f_p` weakly): `∫ Σ α_{cp} f_p ∂_c φ = -∫ g φ` for every
  smooth `φ` (the bilinear pairing of distributions). `HasWeakPartial j f g` is the scalar case
  `g = ∂_j f`.
* `IsWeak m f g` for a first-order symbol `m` (`Feec.Fourier.Weak.IsLinear`, `m ξ = Σ ξ_c m(e_c)`):
  `g = D f` weakly, `D = -i Σ_c m(e_c) ∂_c` the operator with symbol `m`.

The measure on `𝕋ᵈ` is the normalized Haar measure of `Feec.Fourier.Torus.fieldFourier`.

## Main results

* Integration by parts on `𝕋ᵈ`: `integral_partialT_eq_zero`, `mFourierCoeff_partialT`
  (`(∂_c φ)^(k) = 2πi k_c φ̂(k)`); the characters are test functions
  (`isSmooth_mFourier`); Parseval pairing `hasSum_pairing`.
* `isWeakFO_iff`: Fourier characterization of weak first-order operators. Scalar case:
  `hasWeakPartial_iff`, `HasWeakPartial.unique`.
* Fields: **`isWeak_iff`** (`(D f)^(k) = m(2πk) f̂(k)`), `IsWeak.unique`,
  **`mem_graph_iff_isWeak`**: the graph of the Fourier multiplier `m(2πk)` is the weak graph of
  `D`.
* Real fields: `mFourierCoeff_star`, `star_eq_self_iff`, **`fieldFourier_fixed_iff`** (a field is
  real iff its coefficients are fixed by `u ↦ conj u(-k)`), `IsWeak.star_eq_self` (an operator
  with a real symbol maps real fields to real fields).
* Trigonometric polynomials: **`eq_zero_of_ae_eq_zero_of_finite`**: a trigonometric polynomial
  vanishing a.e. on a nonempty open set of `𝕋ᵈ` is zero (analytic continuation of its lift).

## References

* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.1 (weak derivatives)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the periodic complex)
* Mathlib, `Mathlib.Analysis.Fourier.AddCircleMulti`

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped ENNReal InnerProductSpace ComplexConjugate Topology
open MeasureTheory Complex Set Filter

namespace Feec.Fourier.TorusWeak

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.Torus.fieldFourier`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The local Haar measure on `ℝ/ℤ` is an additive Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The local Haar measure on `ℝ/ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

/-! ### The covering map and smooth functions -/

/-- The covering map `ℝᵈ → 𝕋ᵈ`. -/
def proj (y : d → ℝ) : UnitAddTorus d := fun i => (y i : UnitAddCircle)

omit [Fintype d] in
theorem proj_add (y z : d → ℝ) : proj (y + z) = proj y + proj z := by
  funext i; simp [proj]

omit [Fintype d] in
theorem proj_zero : proj (0 : d → ℝ) = 0 := by funext i; simp [proj]

omit [Fintype d] in
/-- `proj` is an open quotient map (product of the quotient maps `ℝ → ℝ/ℤ`). -/
theorem isOpenQuotientMap_proj : IsOpenQuotientMap (proj (d := d)) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

omit [Fintype d] in
theorem proj_surjective : Function.Surjective (proj (d := d)) :=
  isOpenQuotientMap_proj.surjective

omit [Fintype d] in
/-- A function on `𝕋ᵈ` is continuous if its periodic lift is. -/
theorem continuous_of_comp_proj {E : Type*} [TopologicalSpace E] {φ : UnitAddTorus d → E}
    (h : Continuous (φ ∘ proj)) : Continuous φ :=
  isOpenQuotientMap_proj.isQuotientMap.continuous_iff.2 h

/-- Continuous functions on the compact torus are integrable. -/
theorem integrable_of_continuous {φ : UnitAddTorus d → ℂ} (h : Continuous φ) : Integrable φ :=
  h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace φ)

variable [DecidableEq d]

omit [Fintype d] in
theorem single_eq_smul (c : d) (t : ℝ) :
    (Pi.single c t : d → ℝ) = t • (Pi.single c (1 : ℝ) : d → ℝ) := by
  ext i; by_cases h : i = c <;> simp [h]

/-- The partial derivative `∂_c φ (x) = d/dt φ(x + t e_c)|_{t=0}` of a function on `𝕋ᵈ`. -/
def partialT (c : d) (φ : UnitAddTorus d → ℂ) (x : UnitAddTorus d) : ℂ :=
  deriv (fun t : ℝ => φ (x + proj (Pi.single c t))) 0

/-- Smooth functions on `𝕋ᵈ`: those whose `ℤᵈ`-periodic lift to `ℝᵈ` is `C^∞`. -/
def IsSmooth (φ : UnitAddTorus d → ℂ) : Prop := ContDiff ℝ (⊤ : ℕ∞) (φ ∘ proj)

/-- Chain rule along `t ↦ proj (y + t e_c)`. -/
theorem hasDerivAt_lift {φ : UnitAddTorus d → ℂ} (hφ : Differentiable ℝ (φ ∘ proj)) (c : d)
    (y : d → ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => φ (proj y + proj (Pi.single c t)))
      (fderiv ℝ (φ ∘ proj) (y + Pi.single c s) (Pi.single c 1)) s := by
  have h1 : HasDerivAt (fun t : ℝ => y + t • (Pi.single c (1 : ℝ) : d → ℝ))
      (Pi.single c 1) s := by
    simpa using ((hasDerivAt_id s).smul_const (Pi.single c (1 : ℝ) : d → ℝ)).const_add y
  have h2 := (hφ (y + s • Pi.single c 1)).hasFDerivAt.comp_hasDerivAt s h1
  rw [single_eq_smul c s]
  convert h2 using 1
  funext t
  simp [Function.comp, ← proj_add, single_eq_smul c t]

/-- For a differentiable lift, `∂_c φ (proj y)` is the classical partial derivative of the lift. -/
theorem partialT_proj {φ : UnitAddTorus d → ℂ} (hφ : Differentiable ℝ (φ ∘ proj)) (c : d)
    (y : d → ℝ) : partialT c φ (proj y) = fderiv ℝ (φ ∘ proj) y (Pi.single c 1) := by
  unfold partialT
  simpa using (hasDerivAt_lift hφ c y 0).deriv

theorem hasDerivAt_translate {φ : UnitAddTorus d → ℂ} (hφ : Differentiable ℝ (φ ∘ proj)) (c : d)
    (x : UnitAddTorus d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (x + proj (Pi.single c s)))
      (partialT c φ (x + proj (Pi.single c t))) t := by
  obtain ⟨y, rfl⟩ := proj_surjective x
  rw [← proj_add, partialT_proj hφ]
  exact hasDerivAt_lift hφ c y t

theorem continuous_partialT {φ : UnitAddTorus d → ℂ} (hφ : ContDiff ℝ 1 (φ ∘ proj)) (c : d) :
    Continuous (partialT c φ) := by
  apply continuous_of_comp_proj
  have hd : Differentiable ℝ (φ ∘ proj) := hφ.differentiable one_ne_zero
  have : partialT c φ ∘ proj = fun y => fderiv ℝ (φ ∘ proj) y (Pi.single c 1) :=
    funext fun y => partialT_proj hd c y
  rw [this]
  exact (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- `∫_{𝕋ᵈ} ∂_c φ = 0` for `C¹` lifts: differentiate the translation invariance of Haar measure
under the integral sign. -/
theorem integral_partialT_eq_zero {φ : UnitAddTorus d → ℂ} (hφ : ContDiff ℝ 1 (φ ∘ proj))
    (c : d) : ∫ x, partialT c φ x = 0 := by
  have hd : Differentiable ℝ (φ ∘ proj) := hφ.differentiable one_ne_zero
  have hc : Continuous φ := continuous_of_comp_proj hφ.continuous
  have hc' := continuous_partialT hφ c
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖partialT c φ x‖ ≤ C :=
    ⟨‖(⟨_, hc'⟩ : C(UnitAddTorus d, ℂ))‖,
      fun x => (⟨_, hc'⟩ : C(UnitAddTorus d, ℂ)).norm_coe_le_norm x⟩
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
theorem partialT_mul {φ ψ : UnitAddTorus d → ℂ} (hφ : Differentiable ℝ (φ ∘ proj))
    (hψ : Differentiable ℝ (ψ ∘ proj)) (c : d) (x : UnitAddTorus d) :
    partialT c (fun x => φ x * ψ x) x = partialT c φ x * ψ x + φ x * partialT c ψ x := by
  have := ((hasDerivAt_translate hφ c x 0).mul (hasDerivAt_translate hψ c x 0)).deriv
  simp only [Pi.single_zero, proj_zero, add_zero] at this
  unfold partialT at this ⊢
  exact this

omit [DecidableEq d] in
/-- The characters in coordinates: `e_n(proj y) = exp(2πi n·y)`. -/
theorem mFourier_proj (n : d → ℤ) (y : d → ℝ) :
    UnitAddTorus.mFourier n (proj y) = cexp (2 * Real.pi * I * ∑ i, (n i : ℂ) * (y i : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, proj, fourier_coe_apply,
    Finset.mul_sum, ← Complex.exp_sum]
  congr 1; refine Finset.sum_congr rfl fun i _ => ?_; push_cast; ring

omit [DecidableEq d] in
theorem mFourier_comp_proj (n : d → ℤ) :
    UnitAddTorus.mFourier n ∘ proj =
      fun y => cexp (2 * Real.pi * I * ∑ i, (n i : ℂ) * (y i : ℂ)) :=
  funext (mFourier_proj n)

omit [DecidableEq d] in
/-- The characters `e_n` are smooth test functions. -/
theorem isSmooth_mFourier (n : d → ℤ) : IsSmooth (UnitAddTorus.mFourier n) := by
  unfold IsSmooth
  rw [mFourier_comp_proj]
  refine Complex.contDiff_exp.comp (contDiff_const.mul ?_)
  refine ContDiff.sum fun i _ => contDiff_const.mul ?_
  exact Complex.ofRealCLM.contDiff.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : d => ℝ) i).contDiff

/-- `∂_c e_n = 2πi n_c e_n`. -/
theorem partialT_mFourier (n : d → ℤ) (c : d) (x : UnitAddTorus d) :
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
/-- **Integration by parts on `𝕋ᵈ`**: `(∂_c φ)^(k) = 2πi k_c φ̂(k)` for `C¹` functions. -/
theorem mFourierCoeff_partialT {φ : UnitAddTorus d → ℂ} (hφ : ContDiff ℝ 1 (φ ∘ proj)) (c : d)
    (k : d → ℤ) :
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

omit [DecidableEq d] in
/-- `L²` functions times continuous functions are integrable on `𝕋ᵈ`. -/
theorem integrable_mul_continuous (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    {ψ : UnitAddTorus d → ℂ} (hψ : Continuous ψ) : Integrable (fun x => f x * ψ x) :=
  ((Lp.memLp f).integrable one_le_two).mul_bdd hψ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (⟨ψ, hψ⟩ : C(UnitAddTorus d, ℂ)).norm_coe_le_norm x)

omit [DecidableEq d] in
open UnitAddTorus in
/-- **Parseval pairing** (no complex conjugation): `∫ f ψ = Σ_k ψ̂(-k) f̂(k)`. -/
theorem hasSum_pairing (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) {ψ : UnitAddTorus d → ℂ}
    (hψ : Continuous ψ) :
    HasSum (fun k => mFourierCoeff ψ (-k) * mFourierCoeff f k) (∫ x, f x * ψ x) := by
  let g : C(UnitAddTorus d, ℂ) := ⟨fun x => (starRingEnd ℂ) (ψ x), continuous_conj.comp hψ⟩
  have h := hasSum_prod_mFourierCoeff (g.toLp 2 volume ℂ) f
  have h1 : ∀ i, (starRingEnd ℂ) (mFourierCoeff (g.toLp 2 volume ℂ : UnitAddTorus d → ℂ) i) =
      mFourierCoeff ψ (-i) := fun i => by
    rw [mFourierCoeff_toLp, mFourierCoeff, mFourierCoeff, ← integral_conj]
    congr 1; funext t
    simp [g, neg_neg, mFourier_neg]
  have h2 : ∫ t, (starRingEnd ℂ) ((g.toLp 2 volume ℂ : UnitAddTorus d → ℂ) t) * f t =
      ∫ x, f x * ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := volume) g] with t ht
    rw [ht]; simp [g, mul_comm]
  simp_rw [h1, h2] at h
  exact h

omit [DecidableEq d] in
theorem IsSmooth.contDiff_one {φ : UnitAddTorus d → ℂ} (h : IsSmooth φ) :
    ContDiff ℝ 1 (φ ∘ proj) :=
  h.of_le (by exact_mod_cast le_top)

omit [DecidableEq d] in
theorem IsSmooth.continuous {φ : UnitAddTorus d → ℂ} (h : IsSmooth φ) : Continuous φ :=
  continuous_of_comp_proj (show ContDiff ℝ _ (φ ∘ proj) from h).continuous

/-! ### Weak first-order operators on components -/

section FirstOrder

variable {P : Type*} [Fintype P]

/-- **Weak constant-coefficient first-order operators** on components: `g = Σ_{c,p} α_{cp} ∂_c f_p`
weakly if `∫ Σ_{c,p} α_{cp} f_p ∂_c φ = -∫ g φ` for every smooth `φ` on `𝕋ᵈ`. -/
def IsWeakFO (α : d → P → ℂ) (f : P → Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) : Prop :=
  ∀ φ : UnitAddTorus d → ℂ, IsSmooth φ →
    ∫ x, ∑ c, ∑ p, α c p * (f p x * partialT c φ x) = -∫ x, g x * φ x

theorem integral_sum_fo (α : d → P → ℂ) (f : P → Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    {φ : UnitAddTorus d → ℂ} (hφ : IsSmooth φ) :
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
iff `ĝ(k) = Σ α_{cp} 2πi k_c f̂_p(k)` for all `k ∈ ℤᵈ`. -/
theorem isWeakFO_iff (α : d → P → ℂ) (f : P → Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
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

/-! ### Scalar functions -/

section Scalar

open UnitAddTorus

/-- The `L²` function with prescribed Fourier coefficients `a ∈ ℓ²(ℤᵈ)` (inverse Fourier). -/
def ofCoeff (a : lp (fun _ : d → ℤ => ℂ) 2) : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) :=
  mFourierBasis.repr.symm a

omit [DecidableEq d] in
/-- `L²` functions are determined by their Fourier coefficients. -/
theorem eq_of_mFourierCoeff_eq {f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (h : ∀ k, mFourierCoeff (f : UnitAddTorus d → ℂ) k = mFourierCoeff (g : UnitAddTorus d → ℂ) k) :
    f = g := by
  apply (mFourierBasis (d := d)).repr.injective
  ext k
  rw [mFourierBasis_repr, mFourierBasis_repr, h]

/-- **Weak partial derivative** on `𝕋ᵈ`: `g = ∂_j f` in `L²` if `∫ f ∂_j φ = -∫ g φ` for every
smooth `φ`. -/
def HasWeakPartial (j : d) (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) : Prop :=
  ∀ φ : UnitAddTorus d → ℂ, IsSmooth φ → ∫ x, f x * partialT j φ x = -∫ x, g x * φ x

theorem hasWeakPartial_iff_isWeakFO (j : d) (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    HasWeakPartial j f g ↔
      IsWeakFO (fun c (_ : Unit) => if c = j then (1 : ℂ) else 0) (fun _ => f) g := by
  unfold HasWeakPartial IsWeakFO
  simp [ite_mul]

/-- **Fourier characterization of the weak partial derivative**:
`g = ∂_j f` weakly iff `ĝ(k) = 2πi k_j f̂(k)` for all `k`. -/
theorem hasWeakPartial_iff (j : d) (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    HasWeakPartial j f g ↔ ∀ k, mFourierCoeff (g : UnitAddTorus d → ℂ) k =
      2 * Real.pi * I * k j * mFourierCoeff (f : UnitAddTorus d → ℂ) k := by
  rw [hasWeakPartial_iff_isWeakFO, isWeakFO_iff]
  simp

theorem HasWeakPartial.unique {j : d} {f g₁ g₂ : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (h₁ : HasWeakPartial j f g₁) (h₂ : HasWeakPartial j f g₂) : g₁ = g₂ :=
  eq_of_mFourierCoeff_eq fun k => by
    rw [(hasWeakPartial_iff j f g₁).1 h₁ k, (hasWeakPartial_iff j f g₂).1 h₂ k]

omit [Fintype d] [DecidableEq d] in
theorem norm_sq_freq_mul (j : d) (k : d → ℤ) (z : ℂ) :
    ‖2 * Real.pi * I * k j * z‖ ^ 2 = (2 * Real.pi * k j) ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  congr 1
  rw [show (2 * Real.pi * I * k j : ℂ) = ((2 * Real.pi * k j : ℝ) : ℂ) * I by push_cast; ring,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The `L²` class of a continuous function on `𝕋ᵈ`. -/
def toL2 {φ : UnitAddTorus d → ℂ} (hφ : Continuous φ) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus d)) :=
  (⟨φ, hφ⟩ : C(UnitAddTorus d, ℂ)).toLp 2 volume ℂ

omit [DecidableEq d] in
theorem mFourierCoeff_toL2 {φ : UnitAddTorus d → ℂ} (hφ : Continuous φ) (k : d → ℤ) :
    mFourierCoeff (toL2 hφ : UnitAddTorus d → ℂ) k = mFourierCoeff φ k :=
  mFourierCoeff_toLp (⟨φ, hφ⟩ : C(UnitAddTorus d, ℂ)) k

omit [DecidableEq d] in
theorem toL2_ae_eq {φ : UnitAddTorus d → ℂ} (hφ : Continuous φ) :
    (toL2 hφ : UnitAddTorus d → ℂ) =ᵐ[volume] φ :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := volume) (⟨φ, hφ⟩ : C(UnitAddTorus d, ℂ))

omit [DecidableEq d] in
/-- Fourier coefficients of the complex conjugate: `(f̄)^(k) = conj f̂(-k)`. -/
theorem mFourierCoeff_star (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : d → ℤ) :
    mFourierCoeff ((star f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) : UnitAddTorus d → ℂ) k =
      (starRingEnd ℂ) (mFourierCoeff (f : UnitAddTorus d → ℂ) (-k)) := by
  rw [mFourierCoeff, mFourierCoeff, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_star f] with x hx
  rw [hx]
  simp [mFourier_neg, smul_eq_mul]

omit [DecidableEq d] in
/-- An `L²` function is real-valued (`f̄ = f`) iff `f̂(-k) = conj f̂(k)` for all `k`. -/
theorem star_eq_self_iff (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    star f = f ↔ ∀ k, mFourierCoeff (f : UnitAddTorus d → ℂ) (-k) =
      (starRingEnd ℂ) (mFourierCoeff (f : UnitAddTorus d → ℂ) k) := by
  constructor
  · intro h k
    have := mFourierCoeff_star f (-k)
    rwa [h, neg_neg] at this
  · intro h
    refine eq_of_mFourierCoeff_eq fun k => ?_
    have := h (-k)
    rw [neg_neg] at this
    rw [mFourierCoeff_star, this]

end Scalar

/-! ### Trigonometric polynomials vanishing on an open set -/

section TrigPoly

open UnitAddTorus

omit [DecidableEq d] in
/-- An `ℓ²` sequence with finite support is a finite sum of single modes. -/
theorem eq_sum_single_of_finite {f : lp (fun _ : d → ℤ => ℂ) 2} (S : Finset (d → ℤ))
    (hS : ∀ k ∉ S, f k = 0) : f = ∑ k ∈ S, lp.single 2 k (f k) := by
  ext j
  have : ((∑ k ∈ S, lp.single 2 k (f k) : lp (fun _ : d → ℤ => ℂ) 2) : (d → ℤ) → ℂ) j =
      ∑ k ∈ S, (lp.single 2 k (f k) : (d → ℤ) → ℂ) j := by
    change lp.evalCLM ℂ (fun _ : d → ℤ => ℂ) 2 j (∑ k ∈ S, lp.single 2 k (f k)) =
      ∑ k ∈ S, lp.evalCLM ℂ (fun _ : d → ℤ => ℂ) 2 j (lp.single 2 k (f k))
    exact map_sum _ _ _
  rw [this]
  by_cases hj : j ∈ S
  · rw [Finset.sum_eq_single j (fun k _ hk => by simp [lp.single_apply, Ne.symm hk])
      (fun h => absurd hj h)]
    simp
  · rw [hS j hj, Finset.sum_eq_zero fun k hk => ?_]
    have : j ≠ k := fun h => hj (h ▸ hk)
    simp [lp.single_apply, this]

/-- The trigonometric polynomial with coefficients `f` on the finite set `S`. -/
def trigPoly (f : lp (fun _ : d → ℤ => ℂ) 2) (S : Finset (d → ℤ)) : C(UnitAddTorus d, ℂ) :=
  ∑ k ∈ S, f k • mFourier k

omit [DecidableEq d] in
/-- A finitely supported coefficient sequence is the `L²` class of its trigonometric polynomial. -/
theorem ofCoeff_eq_toLp {f : lp (fun _ : d → ℤ => ℂ) 2} (S : Finset (d → ℤ))
    (hS : ∀ k ∉ S, f k = 0) : ofCoeff f = (trigPoly f S).toLp 2 volume ℂ := by
  classical
  conv_lhs => rw [eq_sum_single_of_finite S hS]
  rw [ofCoeff, map_sum, trigPoly, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : lp.single 2 k (f k) = f k • lp.single (E := fun _ : d → ℤ => ℂ) 2 k 1 := by
    rw [← lp.single_smul]; simp
  rw [this, map_smul, HilbertBasis.repr_symm_single, coe_mFourierBasis, map_smul]

omit [DecidableEq d] in
/-- The lift of a trigonometric polynomial to `ℝᵈ` is real-analytic. -/
theorem analyticOnNhd_trigPoly_proj (f : lp (fun _ : d → ℤ => ℂ) 2) (S : Finset (d → ℤ)) :
    AnalyticOnNhd ℝ (fun y => trigPoly f S (proj y)) univ := by
  intro y _
  have e : (fun y => trigPoly f S (proj y)) =
      fun y => ∑ k ∈ S, f k * cexp (2 * Real.pi * I * ∑ i, (k i : ℂ) * (y i : ℂ)) := by
    funext y
    simp only [trigPoly, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mFourier_proj]
  rw [e]
  refine Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul ?_
  have hl : AnalyticAt ℝ (fun y : d → ℝ => 2 * Real.pi * I * ∑ i, (k i : ℂ) * (y i : ℂ)) y := by
    refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul ?_)
    exact (Complex.ofRealCLM.analyticAt _).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : d => ℝ) i).analyticAt y)
  have hc : AnalyticAt ℝ cexp (2 * Real.pi * I * ∑ i, (k i : ℂ) * (y i : ℂ)) :=
    (analyticAt_cexp (z := 2 * Real.pi * I * ∑ i, (k i : ℂ) * (y i : ℂ))).restrictScalars
      (𝕜 := ℝ) (𝕜' := ℂ) (E := ℂ) (F := ℂ)
  exact AnalyticAt.comp (f := fun y : d → ℝ => 2 * Real.pi * I * ∑ i, (k i : ℂ) * (y i : ℂ))
    (g := cexp) hc hl

omit [DecidableEq d] in
/-- **A trigonometric polynomial vanishing a.e. on a nonempty open set of `𝕋ᵈ` is zero**: it is
continuous, so it vanishes on the open set, and its lift to `ℝᵈ` is real-analytic. -/
theorem eq_zero_of_ae_eq_zero_of_finite {f : lp (fun _ : d → ℤ => ℂ) 2} (S : Finset (d → ℤ))
    (hS : ∀ k ∉ S, f k = 0) {U : Set (UnitAddTorus d)} (hU : IsOpen U) (hne : U.Nonempty)
    (hf : (ofCoeff f : UnitAddTorus d → ℂ) =ᵐ[volume.restrict U] 0) : f = 0 := by
  have hg := ofCoeff_eq_toLp S hS
  set h := trigPoly f S
  have h1 : (ofCoeff f : UnitAddTorus d → ℂ) =ᵐ[volume] h := by
    rw [hg]; exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := volume) h
  have hae : (h : UnitAddTorus d → ℂ) =ᵐ[volume.restrict U] 0 :=
    EventuallyEq.trans (EventuallyEq.symm (ae_restrict_of_ae h1 :
      (ofCoeff f : UnitAddTorus d → ℂ) =ᵐ[volume.restrict U] h)) hf
  have hon : EqOn (h : UnitAddTorus d → ℂ) 0 U :=
    Measure.eqOn_open_of_ae_eq hae hU h.continuous.continuousOn continuousOn_const
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨y₀, rfl⟩ := proj_surjective x₀
  have hV : proj ⁻¹' U ∈ 𝓝 y₀ := (hU.preimage isOpenQuotientMap_proj.continuous).mem_nhds hx₀
  have hev : (fun y => h (proj y)) =ᶠ[𝓝 y₀] 0 :=
    Filter.mem_of_superset hV fun y hy => hon hy
  have hall := (analyticOnNhd_trigPoly_proj f S).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ y₀) hev
  have h0 : h = 0 := by
    ext x
    obtain ⟨y, rfl⟩ := proj_surjective x
    exact hall (mem_univ y)
  have : ofCoeff f = 0 := by rw [hg, h0, map_zero]
  rw [ofCoeff] at this
  simpa using congrArg mFourierBasis.repr this

end TrigPoly

/-! ### Fields and first-order operators -/

section Fields

open UnitAddTorus

variable {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P]

variable (d P) in
/-- `L²` fields on `𝕋ᵈ` with values in `ℂᴾ`, componentwise (the physical side of
`Feec.Fourier.Torus.fieldFourier`). -/
abbrev Field := PiLp 2 fun _ : P => Lp ℂ 2 (volume : Measure (UnitAddTorus d))

/-- The Fourier coefficients of a field. -/
abbrev coeff (f : Field d P) : (d → ℤ) → EuclideanSpace ℂ P :=
  (Torus.fieldFourier d P f : (d → ℤ) → EuclideanSpace ℂ P)

omit [DecidableEq d] [DecidableEq P] in
theorem coeff_apply (f : Field d P) (k : d → ℤ) (p : P) :
    coeff f k p = mFourierCoeff (f p : UnitAddTorus d → ℂ) k :=
  Torus.fieldFourier_apply f k p

/-- **Weak constant-coefficient first-order operators on fields**: `g = D f` weakly, with
`D = -i Σ_c m(e_c) ∂_c` the operator whose symbol is the first-order symbol `m`
(`Feec.Fourier.Weak.IsLinear`): for every output component `q`,
`g_q = Σ_{c,p} (-i m(e_c)_{qp}) ∂_c f_p` in the sense of distributions on `𝕋ᵈ`. -/
def IsWeak (m : EuclideanSpace ℝ d → EuclideanSpace ℂ P →L[ℂ] EuclideanSpace ℂ Q)
    (f : Field d P) (g : Field d Q) : Prop :=
  ∀ q, IsWeakFO (fun c p => -I * m (EuclideanSpace.single c 1) (EuclideanSpace.single p 1) q)
    (fun p => f p) (g q)

omit [Fintype Q] in
theorem apply_eq_sum (L : EuclideanSpace ℂ P →L[ℂ] EuclideanSpace ℂ Q) (v : EuclideanSpace ℂ P)
    (q : Q) : L v q = ∑ p, v p * L (EuclideanSpace.single p 1) q := by
  classical
  have hv : v = ∑ p, v p • EuclideanSpace.single p (1 : ℂ) := by
    ext r; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul]

/-- **Fourier characterization of weak first-order operators**: `g = D f` weakly iff
`ĝ(k) = m(2πk) f̂(k)` for every `k ∈ ℤᵈ`. -/
theorem isWeak_iff {m : EuclideanSpace ℝ d → EuclideanSpace ℂ P →L[ℂ] EuclideanSpace ℂ Q}
    (hm : Weak.IsLinear m) (f : Field d P) (g : Field d Q) :
    IsWeak m f g ↔ ∀ k, coeff g k = m (Torus.freq k) (coeff f k) := by
  have key : ∀ k q, m (Torus.freq k) (coeff f k) q =
      ∑ c, ∑ p, (-I * m (EuclideanSpace.single c 1) (EuclideanSpace.single p 1) q) *
        (2 * Real.pi * I * k c * mFourierCoeff (f p : UnitAddTorus d → ℂ) k) := by
    intro k q
    rw [hm (Torus.freq k)]
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul, Torus.freq_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [apply_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [coeff_apply]
    have hI : I * I = -1 := I_mul_I
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * (k c : ℂ) *
      mFourierCoeff (f p : UnitAddTorus d → ℂ) k *
        m (EuclideanSpace.single c 1) (EuclideanSpace.single p 1) q) * hI
  simp only [IsWeak, isWeakFO_iff]
  constructor
  · intro h k
    ext q
    rw [coeff_apply, h q k, key]
  · intro h q k
    rw [← coeff_apply, h k, key]

theorem IsWeak.unique {m : EuclideanSpace ℝ d → EuclideanSpace ℂ P →L[ℂ] EuclideanSpace ℂ Q}
    (hm : Weak.IsLinear m) {f : Field d P} {g₁ g₂ : Field d Q} (h₁ : IsWeak m f g₁)
    (h₂ : IsWeak m f g₂) : g₁ = g₂ :=
  (Torus.fieldFourier d Q).injective <| Lp.ext_count fun k => by
    change coeff g₁ k = coeff g₂ k
    rw [(isWeak_iff hm f g₁).1 h₁ k, (isWeak_iff hm f g₂).1 h₂ k]

/-- **The torus Fourier multiplier of a first-order symbol is its weak realization**: the
coefficients of `f` lie in the domain of the multiplier `m(2πk)`, with image the coefficients of
`g`, iff `g = D f` weakly. -/
theorem mem_graph_iff_isWeak
    {m : EuclideanSpace ℝ d → EuclideanSpace ℂ P →L[ℂ] EuclideanSpace ℂ Q}
    (hm : Weak.IsLinear m) (f : Field d P) (g : Field d Q) :
    (∃ h : Torus.fieldFourier d P f ∈ Operator.mulDomain Measure.count fun k => m (Torus.freq k),
        Operator.mulOp Measure.count (fun k => m (Torus.freq k)) ⟨_, h⟩ =
          Torus.fieldFourier d Q g) ↔ IsWeak m f g := by
  rw [isWeak_iff hm]
  constructor
  · rintro ⟨h, hg⟩ k
    have := Operator.coeFn_mulOp_count (fun k => m (Torus.freq k)) ⟨_, h⟩ k
    rw [hg] at this
    exact this
  · intro hg
    have hmem : Torus.fieldFourier d P f ∈ Operator.mulDomain Measure.count
        fun k => m (Torus.freq k) := by
      change MemLp _ 2 _
      rw [show (fun k => m (Torus.freq k) (coeff f k)) = coeff g from
        funext fun k => (hg k).symm]
      exact Lp.memLp _
    refine ⟨hmem, Lp.ext_count fun k => ?_⟩
    rw [Operator.coeFn_mulOp_count]
    exact (hg k).symm

/-! ### Real fields -/

omit [DecidableEq d] [DecidableEq P] in
theorem coeFn_conjLp_count (u : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ)))
    (k : d → ℤ) :
    (conjLp (E := EuclideanSpace ℂ P) Reflection.count_neg entryConj u :
      (d → ℤ) → EuclideanSpace ℂ P) k = entryConj (u (-k)) :=
  Measure.ae_count_iff.1 (coeFn_conjLp _ _ u) k

omit [DecidableEq d] [DecidableEq P] in
/-- **Real fields**: the coefficients of `f` are fixed by the reflection-conjugation
`u ↦ conj u(-k)` iff every component of `f` is real-valued. -/
theorem fieldFourier_fixed_iff (f : Field d P) :
    conjLp (E := EuclideanSpace ℂ P) Reflection.count_neg entryConj (Torus.fieldFourier d P f) =
      Torus.fieldFourier d P f ↔
      ∀ p, star (f p) = f p := by
  simp only [star_eq_self_iff]
  constructor
  · intro h p k
    have := congrArg (fun u : Lp (EuclideanSpace ℂ P) 2 Measure.count => u (-k) p) h
    simp only [coeFn_conjLp_count, entryConj_apply, neg_neg] at this
    rw [← coeff_apply, ← coeff_apply]
    exact this.symm
  · intro h
    refine Lp.ext_count fun k => ?_
    ext p
    rw [coeFn_conjLp_count, entryConj_apply]
    change (starRingEnd ℂ) (coeff f (-k) p) = coeff f k p
    rw [coeff_apply, coeff_apply, h p k, RCLike.conj_conj]

/-- **Operators with real symbols preserve real fields**: if `m(-ξ) (conj v) = conj (m ξ v)` and
`g = D f` weakly with `f` real, then `g` is real. -/
theorem IsWeak.star_eq_self
    {m : EuclideanSpace ℝ d → EuclideanSpace ℂ P →L[ℂ] EuclideanSpace ℂ Q}
    (hm : Weak.IsLinear m) (hreal : ∀ ξ v, m (-ξ) (entryConj v) = entryConj (m ξ v))
    {f : Field d P} {g : Field d Q} (h : IsWeak m f g) (hf : ∀ p, star (f p) = f p) :
    ∀ q, star (g q) = g q := by
  rw [← fieldFourier_fixed_iff] at hf ⊢
  have hf' : ∀ k, entryConj (coeff f (-k)) = coeff f k := fun k => by
    rw [← coeFn_conjLp_count]; exact congrArg (fun u : Lp (EuclideanSpace ℂ P) 2 Measure.count => u k) hf
  have hg := (isWeak_iff hm f g).1 h
  refine Lp.ext_count fun k => ?_
  rw [coeFn_conjLp_count]
  change entryConj (coeff g (-k)) = coeff g k
  have hf'' : coeff f (-k) = entryConj (coeff f k) := by rw [← hf' k, entryConj_entryConj]
  rw [hg, hg, Torus.freq_neg, hf'', hreal, entryConj_entryConj]

end Fields

end Feec.Fourier.TorusWeak
