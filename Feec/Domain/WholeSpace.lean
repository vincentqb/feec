module

public import Feec.Domain.DeRham
public import Feec.Domain.Mollify

/-!
# On the whole space, minimal = maximal

Let `E` be a finite-dimensional real normed space with an additive Haar measure (`ℝⁿ`) and `A` a
constant-coefficient operator of any order (`Feec.Domain.ConstCoeffOp`). Then

  `A_min(E) = A_max(E)` (`ConstCoeffOp.minimal_univ_eq_maximal_univ`):

`C_c^∞(E)` is dense in the graph norm of the weak (maximal) realization (weak = strong for
constant coefficients on `ℝⁿ`, in the sense of Friedrichs' identity of weak and strong
extensions; cf. [Brezis2011], §9.1); on `ℝⁿ` there is no boundary, so
`H̊ = H`. In particular the minimal and maximal realizations of every complex of
constant-coefficient operators on `E` coincide
(`ConstCoeffComplex.minimalComplex_univ_eq_maximalComplex_univ`), e.g. the de Rham complex,
`H̊Λᵏ(ℝⁿ) = HΛᵏ(ℝⁿ)` (`deRham_minimalComplex_univ_eq_maximalComplex_univ`).

Moreover (`ConstCoeffOp.mem_minimal_of_support_subset`): if `u ∈ D(A_max(E))` vanishes a.e.
outside a compact subset of an open `Ω`, then `u|_Ω ∈ D(A_min(Ω))` and `A_min(u|_Ω) = (A u)|_Ω`.
The same holds starting from `Ω` (`ConstCoeffOp.mem_minimal_of_maximal_of_support_subset`): an
element of `D(A_max(Ω))` vanishing a.e. outside a compact subset of `Ω` lies in `D(A_min(Ω))`
(its extension by zero, `extendL2F`, lies in `D(A_max(E))`). Restriction maps `D(A_max(E))` into
`D(A_max(Ω))` (`ConstCoeffOp.restrictL2F_mem_maximal`).

## Proof

1. **Mollification** (`kconv`): `(k ⋆ f)(x) = ∫ k(x - t) f(t) dt` with a real smooth compactly
   supported kernel `k`. It is smooth with `∂^{vs}(k ⋆ f) = (∂^{vs} k) ⋆ f` (`iterDeriv_kconv`),
   bounded on `L²` by **Young's inequality** `‖k ⋆ f‖₂ ≤ ‖k‖₁ ‖f‖₂` (`eLpNorm_kconv_le`), and
   for the normalized bumps `ρ_m` (radius `→ 0`) `ρ_m ⋆ f → f` in `L²` (`tendsto_eLpNorm_kconv_sub`).
   For `u ∈ D(A_max)`, `A (ρ ⋆ u) = ρ ⋆ A_max u` pointwise (`ConstCoeffOp.apply_kconv`).
2. **Cut-off** (`cutoff`): `χ_R = χ(·/R)` with `χ = 1` on the unit ball; by the Leibniz rule
   for iterated directional derivatives (`iterDeriv_mul`, a sum over the splittings of the
   list of directions) and the uniform bounds on `∂^a χ_R` (`R ≥ 1`), every derivative of
   `(1 - χ_R) g` is dominated by the tails `1_{|x| ≥ R} ∂^b g`, which tend to `0` in `L²` when all
   derivatives of `g` are in `L²` (`tendsto_eLpNorm_iterDeriv_tcut_mul`).
3. Mollify first (all derivatives of `ρ ⋆ u` are in `L²` by Young), then cut off.

## References

* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §4.4 (convolution and regularization), §9.1 (density of `C_c^∞(ℝⁿ)` by mollification and
  cut-off)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (`HΛᵏ` and `H̊Λᵏ`)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff ENNReal ComplexConjugate Convolution Topology LinearPMap
open MeasureTheory Set Filter

@[expose] public noncomputable section

namespace Feec.Domain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  {𝕜 : Type*} [RCLike 𝕜]

/-! ## Convolution with a real kernel -/

variable (𝕜) in
/-- The bilinear map `(a, r) ↦ r a`, `𝕜 × ℝ → 𝕜`. -/
abbrev smulFlip : 𝕜 →L[ℝ] ℝ →L[ℝ] 𝕜 := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜).flip

/-- Convolution of a `𝕜`-valued function with a real kernel: `(k ⋆ f)(x) = ∫ k(x - t) f(t) dt`. -/
def kconv (k : E → ℝ) (f : E → 𝕜) : E → 𝕜 := f ⋆[smulFlip 𝕜, volume] k

omit [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
omit [NormedSpace ℝ E] in
theorem kconv_apply (k : E → ℝ) (f : E → 𝕜) (x : E) :
    kconv k f x = ∫ t, (k (x - t) : 𝕜) * f t := by
  simp [kconv, convolution_def, RCLike.real_smul_eq_coe_mul]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
/-- The convolution integrand is integrable (`k` continuous with compact support, `f` locally
integrable). -/
theorem integrable_kconv_integrand {k : E → ℝ} (hk : Continuous k) (hks : HasCompactSupport k)
    {f : E → 𝕜} (hf : LocallyIntegrable f volume) (x : E) :
    Integrable (fun t => (k (x - t) : 𝕜) * f t) := by
  have h := hks.convolutionExists_right (smulFlip 𝕜) hf hk x
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp [RCLike.real_smul_eq_coe_mul]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
theorem kconv_sub {k : E → ℝ} (hk : Continuous k) (hks : HasCompactSupport k) {f g : E → 𝕜}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) :
    kconv k (f - g) = kconv k f - kconv k g := by
  funext x
  simp only [kconv_apply, Pi.sub_apply, mul_sub]
  exact integral_sub (integrable_kconv_integrand hk hks hf x)
    (integrable_kconv_integrand hk hks hg x)

omit [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
omit [NormedSpace ℝ E] in
theorem kconv_congr_ae (k : E → ℝ) {f g : E → 𝕜} (h : f =ᵐ[volume] g) : kconv k f = kconv k g := by
  funext x
  simp only [kconv_apply]
  exact integral_congr_ae (h.mono fun t ht => by simp only [ht])

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
theorem continuous_kconv {k : E → ℝ} (hk : Continuous k) (hks : HasCompactSupport k)
    {f : E → 𝕜} (hf : LocallyIntegrable f volume) : Continuous (kconv k f) :=
  hks.continuous_convolution_right _ hf hk

/-- **Young's inequality** for `L² ⋆ L¹` (squared, `lintegral` form): by Cauchy–Schwarz against
the measure `|k(x - t)| dt` of total mass `‖k‖₁`, `|(k ⋆ f)(x)|² ≤ ‖k‖₁ ∫ |k(x - t)| |f(t)|² dt`,
and Tonelli. -/
theorem lintegral_sq_kconv_le {k : E → ℝ} (hk : Continuous k) (hks : HasCompactSupport k)
    {f : E → 𝕜}
    (hf : AEStronglyMeasurable f volume) :
    ∫⁻ x, ‖kconv k f x‖ₑ ^ (2 : ℝ) ≤ (∫⁻ t, ‖k t‖ₑ) ^ 2 * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
  set K := ∫⁻ t, ‖k t‖ₑ with hK
  have hKtop : K ≠ ⊤ := (hk.integrable_of_hasCompactSupport hks).hasFiniteIntegral.ne
  have hkm : ∀ x, Measurable fun t : E => ‖k (x - t)‖ₑ := fun x =>
    (hk.measurable.comp (measurable_const.sub measurable_id)).enorm
  have hint : ∀ x, ∫⁻ t, ‖k (x - t)‖ₑ = K := fun x =>
    lintegral_sub_left_eq_self (fun t => ‖k t‖ₑ) x
  have key : ∀ x, ‖kconv k f x‖ₑ ^ (2 : ℝ) ≤ K * ∫⁻ t, ‖k (x - t)‖ₑ * ‖f t‖ₑ ^ (2 : ℝ) := by
    intro x
    set ν := volume.withDensity fun t : E => ‖k (x - t)‖ₑ
    have hν : ν univ = K := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hint]
    have hfν : AEStronglyMeasurable f ν :=
      hf.mono_ac (withDensity_absolutelyContinuous _ _)
    have h1 : ‖kconv k f x‖ₑ ≤ ∫⁻ t, ‖f t‖ₑ ∂ν := by
      rw [kconv_apply, lintegral_withDensity_eq_lintegral_mul₀ (hkm x).aemeasurable hf.enorm]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun t => ?_
      simp only [Pi.mul_apply, enorm_mul]
      congr 1
      rw [← enorm_norm, RCLike.norm_ofReal, ← Real.norm_eq_abs, enorm_norm]
    have h2 : ∫⁻ t, ‖f t‖ₑ ∂ν ≤ (∫⁻ t, ‖f t‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) * K ^ (1 / (2 : ℝ)) := by
      have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hfν
      rw [hν, eLpNorm_one_eq_lintegral_enorm,
        eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hfν] at this
      refine this.trans (le_of_eq ?_)
      norm_num
      all_goals exact hfν
    have h3 := ENNReal.rpow_le_rpow (h1.trans h2) (by norm_num : (0 : ℝ) ≤ 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      show 1 / (2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one,
      lintegral_withDensity_eq_lintegral_mul₀ (hkm x).aemeasurable
        (hf.enorm.pow_const _)] at h3
    rw [mul_comm K]
    exact h3
  calc ∫⁻ x, ‖kconv k f x‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ x, K * ∫⁻ t, ‖k (x - t)‖ₑ * ‖f t‖ₑ ^ (2 : ℝ) := lintegral_mono key
    _ = K * ∫⁻ x, ∫⁻ t, ‖k (x - t)‖ₑ * ‖f t‖ₑ ^ (2 : ℝ) := lintegral_const_mul' _ _ hKtop
    _ = K * ∫⁻ t, ∫⁻ x, ‖k (x - t)‖ₑ * ‖f t‖ₑ ^ (2 : ℝ) := by
      congr 1
      refine lintegral_lintegral_swap ?_
      refine AEMeasurable.mul ?_ ((hf.enorm.pow_const _).comp_snd)
      exact (hk.measurable.comp (measurable_fst.sub measurable_snd)).enorm.aemeasurable
    _ = K * ∫⁻ t, K * ‖f t‖ₑ ^ (2 : ℝ) := by
      congr 1
      refine lintegral_congr fun t => ?_
      rw [lintegral_mul_const' _ _ (by simp),
        lintegral_sub_right_eq_self (fun y => ‖k y‖ₑ) t]
    _ = K ^ 2 * ∫⁻ t, ‖f t‖ₑ ^ (2 : ℝ) := by
      rw [lintegral_const_mul' _ _ hKtop, ← mul_assoc, sq]

/-- **Young's inequality** `‖k ⋆ f‖₂ ≤ ‖k‖₁ ‖f‖₂`. -/
theorem eLpNorm_kconv_le {k : E → ℝ} (hk : Continuous k) (hks : HasCompactSupport k)
    {f : E → 𝕜} (hf : AEStronglyMeasurable f volume) :
    eLpNorm (kconv k f) 2 volume ≤ eLpNorm k 1 volume * eLpNorm f 2 volume := by
  have hm : AEStronglyMeasurable (kconv k f) volume := hf.convolution _ hk.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    eLpNorm_one_eq_lintegral_enorm]
  simp only [ENNReal.toReal_ofNat]
  calc (∫⁻ x, ‖kconv k f x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
      ≤ ((∫⁻ t, ‖k t‖ₑ) ^ 2 * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (lintegral_sq_kconv_le hk hks hf) (by norm_num)
    _ = (∫⁻ t, ‖k t‖ₑ) * (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num
  all_goals exact hk.aestronglyMeasurable

theorem memLp_kconv {k : E → ℝ} (hk : Continuous k) (hks : HasCompactSupport k) {f : E → 𝕜}
    (hf : MemLp f 2 volume) : MemLp (kconv k f) 2 volume := by
  refine (eLpNorm_kconv_le hk hks hf.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top ?_ hf.eLpNorm_lt_top)
  exact (hk.memLp_of_hasCompactSupport hks).eLpNorm_lt_top

/-! ### Derivatives of convolutions -/

omit [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
theorem contDiff_kconv {k : E → ℝ} (hk : IsTest (univ : Set E) k) {f : E → 𝕜}
    (hf : LocallyIntegrable f volume) : ContDiff ℝ ∞ (kconv k f) :=
  hk.hasCompactSupport.contDiff_convolution_right _ hf hk.contDiff

/-- `∂_v (k ⋆ f) = (∂_v k) ⋆ f`. -/
theorem fderiv_kconv {k : E → ℝ} (hk : IsTest (univ : Set E) k) {f : E → 𝕜}
    (hf : LocallyIntegrable f volume) (y v : E) :
    fderiv ℝ (kconv k f) y v = kconv (fun x => fderiv ℝ k x v) f y := by
  have hk1 : ContDiff ℝ 1 k := hk.contDiff.of_le (by simp)
  have hd := hk.hasCompactSupport.hasFDerivAt_convolution_right (smulFlip 𝕜) hf hk1 y
  rw [kconv, hd.fderiv, convolution_precompR_apply _ hf (hk.hasCompactSupport.fderiv ℝ)
    (hk1.continuous_fderiv one_ne_zero)]
  rfl

/-- `∂^{vs} (k ⋆ f) = (∂^{vs} k) ⋆ f`. -/
theorem iterDeriv_kconv {k : E → ℝ} (hk : IsTest (univ : Set E) k) {f : E → 𝕜}
    (hf : LocallyIntegrable f volume) (vs : List E) :
    iterDeriv vs (kconv k f) = kconv (iterDeriv vs k) f := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext y
    rw [iterDeriv_cons]
    simp only
    rw [ih, fderiv_kconv (hk.iterDeriv vs) hf]
    rfl

/-- All derivatives of `k ⋆ f` are in `L²` (`f ∈ L²`, Young). -/
theorem memLp_iterDeriv_kconv {k : E → ℝ} (hk : IsTest (univ : Set E) k) {f : E → 𝕜}
    (hf : MemLp f 2 volume) (vs : List E) : MemLp (iterDeriv vs (kconv k f)) 2 volume := by
  rw [iterDeriv_kconv hk (hf.locallyIntegrable (by norm_num))]
  exact memLp_kconv (hk.iterDeriv vs).continuous (hk.iterDeriv vs).hasCompactSupport hf

/-! ### Constant-coefficient operators commute with convolution -/

omit [FiniteDimensional ℝ E] in
theorem memLp_of_isTest {Ω : Set E} {f : E → 𝕜} (hf : IsTest Ω f) : MemLp f 2 volume :=
  hf.continuous.memLp_of_hasCompactSupport hf.hasCompactSupport

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- `conj f · g` is integrable for `f, g ∈ L²`. -/
theorem integrable_conj_mul_of_memLp {f g : E → 𝕜} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) : Integrable (fun x => conj (f x) * g x) :=
  hf.star.integrable_mul hg

/-- One entry of `A` applied to `k ⋆ f` is the pairing of `f` with the formal adjoint entry
applied to the reflected kernel `k(y - ·)`. -/
theorem applyEntry_kconv (P : List (List E × 𝕜)) {k : E → ℝ} (hk : IsTest (univ : Set E) k)
    {f : E → 𝕜} (hf : MemLp f 2 volume) (y : E) :
    ConstCoeffOp.applyEntry P (kconv k f) y =
      conj (∫ t, conj (f t) * ConstCoeffOp.applyEntry (ConstCoeffOp.adjEntry P)
        (fun s => ((k (y - s) : ℝ) : 𝕜)) t) := by
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hky : IsTest (univ : Set E) (fun s => ((k (y - s) : ℝ) : 𝕜)) := (hk.comp_sub y).ofReal
  induction P with
  | nil => simp [ConstCoeffOp.applyEntry, ConstCoeffOp.adjEntry]
  | cons t P ih =>
    obtain ⟨vs, c⟩ := t
    have hder : iterDeriv vs.reverse (fun s => ((k (y - s) : ℝ) : 𝕜)) =
        fun s => (((-1) ^ vs.length * iterDeriv vs k (y - s) : ℝ) : 𝕜) := by
      rw [show (fun s => ((k (y - s) : ℝ) : 𝕜)) = fun s =>
          (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) ((fun s => k (y - s)) s) from rfl,
        iterDeriv_comp_clm _ (hk.comp_sub y).contDiff, iterDeriv_comp_sub hk.contDiff y,
        iterDeriv_reverse hk.contDiff, List.length_reverse]
      rfl
    have hterm : ∀ s, conj (f s) * ConstCoeffOp.applyEntry
        (ConstCoeffOp.adjEntry ((vs, c) :: P)) (fun s => ((k (y - s) : ℝ) : 𝕜)) s =
        conj c * (conj (f s) * ((iterDeriv vs k (y - s) : ℝ) : 𝕜)) +
          conj (f s) * ConstCoeffOp.applyEntry (ConstCoeffOp.adjEntry P)
            (fun s => ((k (y - s) : ℝ) : 𝕜)) s := by
      intro s
      simp only [ConstCoeffOp.adjEntry, List.map_cons]
      rw [ConstCoeffOp.applyEntry_cons]
      simp only [ConstCoeffOp.adjEntry] at *
      rw [hder]
      push_cast
      have h1 : ((-1 : 𝕜) ^ vs.length) * ((-1) ^ vs.length) = 1 := by
        rw [← mul_pow]; norm_num
      linear_combination (conj c * conj (f s) * ((iterDeriv vs k (y - s) : ℝ) : 𝕜)) * h1
    have hint1 : Integrable (fun s => conj (f s) * ((iterDeriv vs k (y - s) : ℝ) : 𝕜)) :=
      integrable_conj_mul_of_memLp hf (memLp_of_isTest ((hk.iterDeriv vs).comp_sub y).ofReal)
    have hint2 : Integrable (fun s => conj (f s) * ConstCoeffOp.applyEntry
        (ConstCoeffOp.adjEntry P) (fun s => ((k (y - s) : ℝ) : 𝕜)) s) :=
      integrable_conj_mul_of_memLp hf (memLp_of_isTest (IsTest.applyEntry _ hky))
    rw [ConstCoeffOp.applyEntry_cons]
    simp only
    rw [iterDeriv_kconv hk hfl, ih, integral_congr_ae (Eventually.of_forall hterm),
      integral_add (hint1.const_mul _) hint2, integral_const_mul, map_add, map_mul,
      RCLike.conj_conj, ← integral_conj, kconv_apply]
    have e : ∫ t, ((iterDeriv vs k (y - t) : ℝ) : 𝕜) * f t =
        ∫ t, conj (conj (f t) * ((iterDeriv vs k (y - t) : ℝ) : 𝕜)) :=
      integral_congr_ae (Eventually.of_forall fun t => by
        simp only [map_mul, RCLike.conj_conj, RCLike.conj_ofReal]; ring)
    rw [e]
    simp only [integral_conj]

/-- **`A` commutes with convolution on `D(A_max(E))`**: if `A u = w` in the sense of
distributions on `E`, then `A (k ⋆ u) = k ⋆ w` pointwise, for a real test kernel `k`. -/
theorem ConstCoeffOp.apply_kconv {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : ConstCoeffOp E 𝕜 ι κ) {k : E → ℝ} (hk : IsTest (univ : Set E) k)
    {u : ι → E → 𝕜} (hu : ∀ i, MemLp (u i) 2 volume) {w : κ → E → 𝕜}
    (hweak : ∀ ψ : κ → E → 𝕜, IsTestField (univ : Set E) ψ →
      ∑ j, ∫ x, conj (w j x) * ψ j x = ∑ i, ∫ x, conj (u i x) * A.formalAdj.apply ψ i x) :
    A.apply (fun i => kconv k (u i)) = fun j => kconv k (w j) := by
  funext j y
  set ψ₀ : E → 𝕜 := fun s => ((k (y - s) : ℝ) : 𝕜) with hψ₀d
  have hψ₀ : IsTest (univ : Set E) ψ₀ := (hk.comp_sub y).ofReal
  have h := hweak (Pi.single j ψ₀) (IsTestField.single j hψ₀)
  have hL : ∑ j', ∫ x, conj (w j' x) * (Pi.single j ψ₀ : κ → E → 𝕜) j' x =
      ∫ x, conj (w j x) * ψ₀ x := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'; simp [Pi.single_eq_of_ne hj']
    · simp
  have hR : ∀ i, A.formalAdj.apply (Pi.single j ψ₀) i =
      ConstCoeffOp.applyEntry (ConstCoeffOp.adjEntry (A.coeff j i)) ψ₀ := by
    intro i; funext t
    simp only [ConstCoeffOp.apply, ConstCoeffOp.formalAdj]
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      rw [Pi.single_eq_of_ne hj']
      exact congrFun (ConstCoeffOp.applyEntry_zero _) t
    · simp
  simp only [ConstCoeffOp.apply]
  rw [show (∑ i, ConstCoeffOp.applyEntry (A.coeff j i) (kconv k (u i)) y) =
      conj (∑ i, ∫ x, conj (u i x) * A.formalAdj.apply (Pi.single j ψ₀) i x) from ?_]
  · rw [← h, hL, ← integral_conj, kconv_apply]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [hψ₀d, mul_comm]
  · rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [applyEntry_kconv _ hk (hu i), hR i]

/-! ### Convergence of mollifications in `L²` -/

/-- The normalized bumps have `L¹` norm `1`. -/
theorem eLpNorm_normed_one (φ : ContDiffBump (0 : E)) : eLpNorm (φ.normed volume) 1 volume = 1 := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  have e : ∀ x, ‖φ.normed volume x‖ₑ = ENNReal.ofReal (φ.normed volume x) := fun x =>
    Real.enorm_of_nonneg (φ.nonneg_normed x)
  simp only [e]
  rw [← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
    (Eventually.of_forall φ.nonneg_normed), φ.integral_normed, ENNReal.ofReal_one]
  all_goals exact φ.continuous_normed.aestronglyMeasurable

/-- Pointwise and support estimates for a continuous compactly supported `g`: `ρ ⋆ g` is
uniformly close to `g`, with support in a fixed ball, once the bump radius is small. -/
theorem eLpNorm_kconv_sub_le_of_continuous {g : E → 𝕜} (hgc : Continuous g)
    (hgs : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ φ : ContDiffBump (0 : E), φ.rOut < η →
      eLpNorm (kconv (φ.normed volume) g - g) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨R, hR0, hR⟩ : ∃ R > 0, tsupport g ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := hgs.isCompact.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  have hsupp : ∀ x, g x ≠ 0 → ‖x‖ ≤ R := fun x hx => by
    simpa using hR (subset_tsupport _ hx)
  set K := Metric.closedBall (0 : E) (R + 1)
  have hK : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  set M := (volume K).toReal
  have hKM : volume K ^ (1 / ENNReal.toReal 2) = ENNReal.ofReal (Real.sqrt M) := by
    rw [← ENNReal.ofReal_toReal hK, Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg
      ENNReal.toReal_nonneg (by norm_num)]
    norm_num
    rfl
  set ε' := ε / (Real.sqrt M + 1)
  have hε' : 0 < ε' := by positivity
  have hε'M : ε' * Real.sqrt M ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg M]
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1
    (hgs.uniformContinuous_of_continuous hgc) ε' hε'
  refine ⟨min 1 δ, by positivity, fun φ hφ => ?_⟩
  have hφ1 : φ.rOut < 1 := hφ.trans_le (min_le_left _ _)
  have hφδ : φ.rOut < δ := hφ.trans_le (min_le_right _ _)
  have hgl : LocallyIntegrable g volume := hgc.locallyIntegrable
  have hflip : kconv (φ.normed volume) g =
      φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g := by
    rw [kconv, ← convolution_flip]
    simp only [smulFlip, ContinuousLinearMap.flip_flip]
  have hpt : ∀ x, dist (kconv (φ.normed volume) g x) (g x) ≤ ε' := by
    intro x
    rw [hflip]
    refine φ.dist_normed_convolution_le hgc.aestronglyMeasurable fun z hz => ?_
    exact (hδg (lt_of_lt_of_le (Metric.mem_ball.1 hz) hφδ.le)).le
  have hs1 : Function.support (kconv (φ.normed volume) g) ⊆ K := by
    intro x hx
    obtain ⟨u, hu, v, hv, huv⟩ := support_convolution_subset _ hx
    rw [φ.support_normed_eq] at hv
    have hu' := hsupp u hu
    have hv' : ‖v‖ < φ.rOut := by simpa using hv
    rw [Metric.mem_closedBall, dist_zero_right, ← huv]
    calc ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le _ _
      _ ≤ R + 1 := by linarith
  have hs2 : Function.support g ⊆ K := fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right]; linarith [hsupp x hx]
  have hmeas : AEStronglyMeasurable (kconv (φ.normed volume) g - g) volume :=
    ((continuous_kconv φ.continuous_normed φ.hasCompactSupport_normed hgl).sub
      hgc).aestronglyMeasurable
  refine (eLpNorm_sub_le_of_dist_bdd volume (by norm_num)
    measurableSet_closedBall.nullMeasurableSet hε'.le hmeas hpt hs1 hs2).trans ?_
  rw [hKM, ← ENNReal.ofReal_mul hε'.le]
  exact ENNReal.ofReal_le_ofReal hε'M

/-- The bumps `ρ_m` of radii `1/(m+2) < 1/(m+1)`. -/
def bumpSeq (m : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / ((m : ℝ) + 2)
  rOut := 1 / ((m : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem tendsto_bumpSeq_rOut :
    Tendsto (fun m => (bumpSeq m : ContDiffBump (0 : E)).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem isTest_bumpSeq (m : ℕ) : IsTest (univ : Set E) ((bumpSeq m).normed volume) :=
  ⟨(bumpSeq m).contDiff_normed, (bumpSeq m).hasCompactSupport_normed, subset_univ _⟩

/-- **Mollification converges in `L²`**: `ρ_m ⋆ f → f` for `f ∈ L²(E; 𝕜)`. -/
theorem tendsto_eLpNorm_kconv_sub {f : E → 𝕜} (hf : MemLp f 2 volume) :
    Tendsto (fun m => eLpNorm (kconv ((bumpSeq m).normed volume) f - f) 2 volume) atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  have hδ3 : 0 < δ / 3 := by positivity
  obtain ⟨g, hgs, hgd, hfg⟩ := hf.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hδ3
  have hgc : Continuous g := hgd.continuous
  have hgm : MemLp g 2 volume := hgc.memLp_of_hasCompactSupport hgs
  obtain ⟨η, hη, hηg⟩ := eLpNorm_kconv_sub_le_of_continuous hgc hgs hδ3
  filter_upwards [(tendsto_bumpSeq_rOut (E := E)).eventually (gt_mem_nhds hη)] with m hm
  set ρ := (bumpSeq m : ContDiffBump (0 : E)).normed volume
  have hρc : Continuous ρ := (bumpSeq m).continuous_normed
  have hρs : HasCompactSupport ρ := (bumpSeq m).hasCompactSupport_normed
  have hfgm : MemLp (f - g) 2 volume := hf.sub hgm
  have hli : LocallyIntegrable (f - g) volume := hfgm.locallyIntegrable (by norm_num)
  have hgl : LocallyIntegrable g volume := hgc.locallyIntegrable
  have e : kconv ρ f - f = kconv ρ (f - g) + (kconv ρ g - g) + -(f - g) := by
    rw [kconv_sub hρc hρs (hf.locallyIntegrable (by norm_num)) hgl]
    abel
  have b1 : eLpNorm (kconv ρ (f - g)) 2 volume ≤ ENNReal.ofReal (δ / 3) := by
    refine (eLpNorm_kconv_le hρc hρs hfgm.aestronglyMeasurable).trans ?_
    rw [eLpNorm_normed_one, one_mul]
    exact hfg
  rw [e]
  calc eLpNorm (kconv ρ (f - g) + (kconv ρ g - g) + -(f - g)) 2 volume
      ≤ eLpNorm (kconv ρ (f - g) + (kconv ρ g - g)) 2 volume + eLpNorm (-(f - g)) 2 volume :=
        eLpNorm_add_le (by norm_num)
    _ ≤ (eLpNorm (kconv ρ (f - g)) 2 volume + eLpNorm (kconv ρ g - g) 2 volume) +
          eLpNorm (f - g) 2 volume := by
        rw [eLpNorm_neg]
        gcongr
        exact eLpNorm_add_le (by norm_num)
    _ ≤ (ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3)) + ENNReal.ofReal (δ / 3) := by
        gcongr
        exact hηg _ hm
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add hδ3.le hδ3.le, ← ENNReal.ofReal_add (by positivity) hδ3.le]
        congr 1; ring
    _ ≤ ε := hδε.le

/-! ## The Leibniz rule for iterated directional derivatives -/

/-- The splittings of a list of directions between two factors: `∂^{v :: vs} (θ g)` distributes
`∂_v` on either factor of each term of `∂^{vs} (θ g)`. -/
def splits : List E → List (List E × List E)
  | [] => [([], [])]
  | v :: vs => (splits vs).flatMap fun p => [(v :: p.1, p.2), (p.1, v :: p.2)]

section ListSums

variable {α : Type*} {G : Type*} [NormedAddCommGroup G]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem sum_map_flatMap {β : Type*} (l : List α) (f : α → List β) (h : β → G) :
    ((l.flatMap f).map h).sum = (l.map fun a => ((f a).map h).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E]
  [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem norm_list_sum_le (L : List α) (F : α → G) :
    ‖(L.map F).sum‖ ≤ (L.map fun a => ‖F a‖).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (by linarith)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E]
  [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem list_sum_le_sum (L : List α) {F F' : α → ℝ} (h : ∀ a ∈ L, F a ≤ F' a) :
    (L.map F).sum ≤ (L.map F').sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E]
  [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem list_sum_nonneg (L : List α) {F : α → ℝ} (h : ∀ a ∈ L, 0 ≤ F a) : 0 ≤ (L.map F).sum := by
  simpa using list_sum_le_sum L (F := fun _ => 0) h

end ListSums

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem contDiff_list_sum {α : Type*} (L : List α) {F : α → E → 𝕜}
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) : ContDiff ℝ ∞ (fun x => (L.map fun a => F a x).sum) := by
  induction L with
  | nil => simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : E => (0 : 𝕜))
  | cons a L ih => simpa using (hF a).add ih

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem fderiv_list_sum {α : Type*} (L : List α) {F : α → E → 𝕜} (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (x v : E) :
    fderiv ℝ (fun x => (L.map fun a => F a x).sum) x v = (L.map fun a => fderiv ℝ (F a) x v).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [fderiv_fun_add ((hF a).differentiable (by simp) x)
      ((contDiff_list_sum L hF).differentiable (by simp) x)]
    simp [ih]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- **Leibniz rule**: `∂^{vs} (θ g) = Σ_{(a, b) ∈ splits vs} ∂^a θ · ∂^b g`. -/
theorem iterDeriv_mul {θ g : E → 𝕜} (hθ : ContDiff ℝ ∞ θ) (hg : ContDiff ℝ ∞ g) (vs : List E) :
    iterDeriv vs (fun x => θ x * g x) =
      fun x => ((splits vs).map fun p => iterDeriv p.1 θ x * iterDeriv p.2 g x).sum := by
  induction vs with
  | nil => funext x; simp [splits]
  | cons v vs ih =>
    funext x
    rw [iterDeriv_cons, ih]
    simp only
    rw [fderiv_list_sum (splits vs)
      (F := fun (p : List E × List E) x => iterDeriv p.1 θ x * iterDeriv p.2 g x)
      (fun p => (contDiff_iterDeriv hθ p.1).mul (contDiff_iterDeriv hg p.2)),
      splits, sum_map_flatMap]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    rw [fderiv_fun_mul ((contDiff_iterDeriv hθ p.1).differentiable (by simp) x)
      ((contDiff_iterDeriv hg p.2).differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, iterDeriv_cons]
    ring

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem norm_iterDeriv_mul_le {θ g : E → 𝕜} (hθ : ContDiff ℝ ∞ θ) (hg : ContDiff ℝ ∞ g)
    (vs : List E) (x : E) :
    ‖iterDeriv vs (fun x => θ x * g x) x‖ ≤
      ((splits vs).map fun p => ‖iterDeriv p.1 θ x‖ * ‖iterDeriv p.2 g x‖).sum := by
  rw [iterDeriv_mul hθ hg]
  refine (norm_list_sum_le _ _).trans (le_of_eq ?_)
  simp only [norm_mul]

/-! ## Cut-offs -/

/-- The cut-off profile: `χ = 1` on the closed unit ball, supported in the ball of radius `2`. -/
def cutBump : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cut-off `χ_R(x) = χ(x / R)`. -/
def cutoff (R : ℝ) : E → ℝ := dil 0 R⁻¹ (cutBump : ContDiffBump (0 : E))

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem cutoff_apply (R : ℝ) (x : E) : cutoff R x = (cutBump : ContDiffBump (0 : E)) (R⁻¹ • x) := by
  simp [cutoff, dil]

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem contDiff_cutoff (R : ℝ) : ContDiff ℝ ∞ (cutoff (E := E) R) :=
  contDiff_dil 0 _ (cutBump : ContDiffBump (0 : E)).contDiff

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : cutoff R x = 1 := by
  rw [cutoff_apply]
  refine ContDiffBump.one_of_mem_closedBall _ ?_
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
  change R⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ hR]; linarith

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem hasCompactSupport_cutoff {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutoff (E := E) R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R)) fun x hx => ?_
  rw [cutoff_apply]
  refine ContDiffBump.zero_of_le_dist _ ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
  change 2 ≤ R⁻¹ * ‖x‖
  rw [le_inv_mul_iff₀ hR]; linarith

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- **Uniform bounds on the derivatives of the cut-offs** `χ_R`, `R ≥ 1`. -/
theorem exists_bound_iterDeriv_cutoff :
    ∃ M : List E → ℝ, ∀ a, 0 ≤ M a ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : E, |iterDeriv a (cutoff R) x| ≤ M a := by
  have hT : IsTest (univ : Set E) ((cutBump : ContDiffBump (0 : E)) : E → ℝ) :=
    ⟨(cutBump : ContDiffBump (0 : E)).contDiff, (cutBump : ContDiffBump (0 : E)).hasCompactSupport,
      subset_univ _⟩
  have hb := fun a : List E =>
    (hT.iterDeriv a).continuous.bounded_above_of_compact_support (hT.iterDeriv a).hasCompactSupport
  choose M hM using hb
  refine ⟨M, fun a => ⟨(norm_nonneg _).trans (hM a 0), fun R hR x => ?_⟩⟩
  rw [cutoff, iterDeriv_dil 0 R⁻¹ (cutBump : ContDiffBump (0 : E)).contDiff a]
  simp only [abs_mul, abs_pow]
  have h1 : |R⁻¹| ^ a.length ≤ 1 := by
    refine pow_le_one₀ (abs_nonneg _) ?_
    rw [abs_inv, abs_of_pos (by linarith)]
    exact inv_le_one_of_one_le₀ hR
  calc |R⁻¹| ^ a.length * |iterDeriv a ((cutBump : ContDiffBump (0 : E)) : E → ℝ)
        (0 + R⁻¹ • (x - 0))|
      ≤ 1 * M a := mul_le_mul h1 (by simpa using hM a _) (abs_nonneg _) zero_le_one
    _ = M a := one_mul _

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem iterDeriv_const_bound (c : ℝ) (a : List E) :
    ∃ c' : ℝ, iterDeriv a (fun _ : E => c) = (fun _ => c') ∧ |c'| ≤ |c| := by
  induction a with
  | nil => exact ⟨c, rfl, le_rfl⟩
  | cons v a ih =>
    obtain ⟨c', h, -⟩ := ih
    refine ⟨0, ?_, by simp⟩
    funext x
    rw [iterDeriv_cons, h]
    simp

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem iterDeriv_eventuallyEq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {x : E} (h : f =ᶠ[𝓝 x] g) (a : List E) :
    iterDeriv a f =ᶠ[𝓝 x] iterDeriv a g := by
  induction a with
  | nil => exact h
  | cons v a ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    simp only [iterDeriv_cons, hy]

variable (𝕜) in
/-- `1 - χ_R`, as a `𝕜`-valued function. -/
def tcut (R : ℝ) (x : E) : 𝕜 := ((1 - cutoff R x : ℝ) : 𝕜)

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem contDiff_tcut (R : ℝ) : ContDiff ℝ ∞ (tcut 𝕜 (E := E) R) :=
  (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp (contDiff_const.sub (contDiff_cutoff R))

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem iterDeriv_tcut (R : ℝ) (a : List E) :
    iterDeriv a (tcut 𝕜 (E := E) R) = fun x =>
      ((iterDeriv a (fun _ : E => (1 : ℝ)) x - iterDeriv a (cutoff R) x : ℝ) : 𝕜) := by
  have hc : ContDiff ℝ ∞ ((-1 : ℝ) • cutoff (E := E) R) := (contDiff_cutoff R).const_smul (-1 : ℝ)
  have h1 : ContDiff ℝ ∞ (fun _ : E => (1 : ℝ)) := contDiff_const
  rw [show tcut 𝕜 (E := E) R = fun x => (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜)
      ((((fun _ : E => (1 : ℝ)) + (-1 : ℝ) • cutoff R) : E → ℝ) x) from by
    funext x; simp [tcut, sub_eq_add_neg],
    iterDeriv_comp_clm _ (f := ((fun _ : E => (1 : ℝ)) + (-1 : ℝ) • cutoff R)) (h1.add hc),
    iterDeriv_add h1 hc, iterDeriv_smul (-1 : ℝ) (contDiff_cutoff R)]
  funext x
  simp [sub_eq_add_neg]

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem iterDeriv_tcut_eq_zero {R : ℝ} (hR : 0 < R) (a : List E) {x : E} (hx : ‖x‖ < R) :
    iterDeriv a (tcut 𝕜 (E := E) R) x = 0 := by
  have h : tcut 𝕜 (E := E) R =ᶠ[𝓝 x] 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using hx : x ∈ Metric.ball (0 : E) R)]
      with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    simp [tcut, cutoff_eq_one hR hy.le]
  rw [(iterDeriv_eventuallyEq h a).eq_of_nhds, iterDeriv_zero]
  rfl

/-! ## Limits in `L²` -/

section Tendsto

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The `L²` tails `1_{|x| ≥ R} h` of `h ∈ L²(E)` tend to `0` as `R → ∞`. -/
theorem tendsto_eLpNorm_indicator_tail {h : E → F} (hh : MemLp h 2 volume) :
    Tendsto (fun R : ℝ => eLpNorm ({x | R ≤ ‖x‖}.indicator h) 2 volume) atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  obtain ⟨g, hgs, -, hhg⟩ := hh.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hδ
  obtain ⟨R₀, hR₀⟩ := hgs.isCompact.isBounded.subset_closedBall 0
  filter_upwards [eventually_gt_atTop R₀] with R hR
  have e : {x | R ≤ ‖x‖}.indicator h = {x | R ≤ ‖x‖}.indicator (h - g) := by
    funext x
    by_cases hx : R ≤ ‖x‖
    · have : g x = 0 := by
        by_contra hgx
        have := hR₀ (subset_tsupport _ hgx)
        rw [Metric.mem_closedBall, dist_zero_right] at this
        linarith
      simp [Set.indicator_of_mem (show x ∈ {x : E | R ≤ ‖x‖} from hx), this]
    · simp [Set.indicator_of_notMem (show x ∉ {x : E | R ≤ ‖x‖} from hx)]
  rw [e]
  exact (eLpNorm_indicator_le _
    (measurableSet_le measurable_const measurable_norm).nullMeasurableSet).trans (hhg.trans hδε.le)

variable {α : Type*} {l : Filter α}

omit [NormedSpace ℝ F] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
omit [NormedAddCommGroup E] in
theorem tendsto_eLpNorm_add_of {f g : α → E → F}
    (hf : Tendsto (fun a => eLpNorm (f a) 2 volume) l (𝓝 0))
    (hg : Tendsto (fun a => eLpNorm (g a) 2 volume) l (𝓝 0)) :
    Tendsto (fun a => eLpNorm (f a + g a) 2 volume) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hf.add hg)
    (fun _ => zero_le) fun _ => eLpNorm_add_le (by norm_num)

omit [NormedSpace ℝ F] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
omit [NormedAddCommGroup E] in
theorem tendsto_eLpNorm_list_sum {β : Type*} (L : List β) {f : β → α → E → F}
    (h : ∀ b ∈ L, Tendsto (fun a => eLpNorm (f b a) 2 volume) l (𝓝 0)) :
    Tendsto (fun a => eLpNorm (fun x => (L.map fun b => f b a x).sum) 2 volume) l (𝓝 0) := by
  induction L with
  | nil => simpa using tendsto_const_nhds
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact tendsto_eLpNorm_add_of (f := fun a => f b a)
      (g := fun a x => (L.map fun b => f b a x).sum) (h b List.mem_cons_self)
      (ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

omit [NormedSpace ℝ F] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
omit [NormedAddCommGroup E] in
theorem tendsto_eLpNorm_finset_sum {β : Type*} (s : Finset β) {f : β → α → E → F}
    (h : ∀ b ∈ s, Tendsto (fun a => eLpNorm (f b a) 2 volume) l (𝓝 0)) :
    Tendsto (fun a => eLpNorm (fun x => ∑ b ∈ s, f b a x) 2 volume) l (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | insert b s hb ih =>
    simp only [Finset.sum_insert hb]
    exact tendsto_eLpNorm_add_of (f := fun a => f b a) (g := fun a x => ∑ b ∈ s, f b a x)
      (h b (Finset.mem_insert_self b s)) (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
omit [NormedAddCommGroup E] in
theorem tendsto_eLpNorm_const_smul (c : ℝ) {f : α → E → F}
    (h : Tendsto (fun a => eLpNorm (f a) 2 volume) l (𝓝 0)) :
    Tendsto (fun a => eLpNorm (fun x => c • f a x) 2 volume) l (𝓝 0) := by
  have e : ∀ a, eLpNorm (fun x => c • f a x) 2 volume = ‖c‖ₑ * eLpNorm (f a) 2 volume :=
    fun a => eLpNorm_const_smul c (f a) 2 volume
  simp only [e]
  simpa using ENNReal.Tendsto.const_mul h (Or.inr enorm_ne_top)

omit [NormedSpace ℝ F] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
omit [NormedAddCommGroup E] in
theorem tendsto_eLpNorm_const_mul (c : 𝕜) {f : α → E → 𝕜}
    (h : Tendsto (fun a => eLpNorm (f a) 2 volume) l (𝓝 0)) :
    Tendsto (fun a => eLpNorm (fun x => c * f a x) 2 volume) l (𝓝 0) := by
  have e : ∀ a, eLpNorm (fun x => c * f a x) 2 volume = ‖c‖ₑ * eLpNorm (f a) 2 volume :=
    fun a => eLpNorm_const_smul c (f a) 2 volume
  simp only [e]
  simpa using ENNReal.Tendsto.const_mul h (Or.inr enorm_ne_top)

omit [NormedSpace ℝ F] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
omit [NormedAddCommGroup E] in
theorem tendsto_eLpNorm_of_norm_le {G : Type*} [NormedAddCommGroup G] {f : α → E → F}
    {g : α → E → G} (hf : ∀ a, AEStronglyMeasurable (f a) volume) (hfg : ∀ a x, ‖f a x‖ ≤ ‖g a x‖)
    (h : Tendsto (fun a => eLpNorm (g a) 2 volume) l (𝓝 0)) :
    Tendsto (fun a => eLpNorm (f a) 2 volume) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    fun a => eLpNorm_mono (hf a) (hfg a)

end Tendsto

/-- **The cut-off error vanishes in `L²`**: if every derivative of the smooth `g` is in `L²(E)`,
then every derivative of `(1 - χ_R) g` tends to `0` in `L²(E)` as `R → ∞` (`R = m + 1`). -/
theorem tendsto_eLpNorm_iterDeriv_tcut_mul {g : E → 𝕜} (hg : ContDiff ℝ ∞ g)
    (hgL : ∀ l : List E, MemLp (iterDeriv l g) 2 volume) (vs : List E) :
    Tendsto (fun m : ℕ => eLpNorm (iterDeriv vs (fun x => tcut 𝕜 ((m : ℝ) + 1) x * g x)) 2 volume)
      atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := exists_bound_iterDeriv_cutoff (E := E)
  have hR : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  refine tendsto_eLpNorm_of_norm_le (g := fun (m : ℕ) (x : E) => ((splits vs).map fun p =>
    (1 + M p.1) * ‖{y : E | (m : ℝ) + 1 ≤ ‖y‖}.indicator (iterDeriv p.2 g) x‖).sum)
    (fun m => (contDiff_iterDeriv ((contDiff_tcut _).mul hg) vs).continuous.aestronglyMeasurable)
    (fun m x => ?_) ?_
  · have hR1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [m.cast_nonneg (α := ℝ)]
    refine (norm_iterDeriv_mul_le (contDiff_tcut _) hg vs x).trans ?_
    refine le_trans ?_ (Real.le_norm_self _)
    refine list_sum_le_sum _ fun p _ => ?_
    by_cases hx : (m : ℝ) + 1 ≤ ‖x‖
    · rw [Set.indicator_of_mem (show x ∈ {y : E | (m : ℝ) + 1 ≤ ‖y‖} from hx)]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [iterDeriv_tcut, RCLike.norm_ofReal]
      obtain ⟨c', hc', hc'1⟩ := iterDeriv_const_bound (E := E) 1 p.1
      rw [hc']
      calc |c' - iterDeriv p.1 (cutoff ((m : ℝ) + 1)) x|
          ≤ |c'| + |iterDeriv p.1 (cutoff ((m : ℝ) + 1)) x| := abs_sub _ _
        _ ≤ 1 + M p.1 := add_le_add (by simpa using hc'1) ((hM p.1).2 _ hR1 x)
    · rw [iterDeriv_tcut_eq_zero (by positivity) p.1 (not_le.1 hx), norm_zero, zero_mul]
      exact mul_nonneg (by linarith [(hM p.1).1]) (norm_nonneg _)
  · refine tendsto_eLpNorm_list_sum (splits vs) (f := fun p (m : ℕ) x => (1 + M p.1) *
      ‖{y : E | (m : ℝ) + 1 ≤ ‖y‖}.indicator (iterDeriv p.2 g) x‖) fun p _ => ?_
    have h := tendsto_eLpNorm_const_smul (l := atTop) (1 + M p.1) (f := fun (m : ℕ) (x : E) =>
      ‖{y : E | (m : ℝ) + 1 ≤ ‖y‖}.indicator (iterDeriv p.2 g) x‖) ?_
    · simpa [smul_eq_mul] using h
    · refine ((tendsto_eLpNorm_indicator_tail (hgL p.2)).comp hR).congr fun m => ?_
      exact (eLpNorm_norm _ ((contDiff_iterDeriv hg p.2).continuous.aestronglyMeasurable.indicator
        (measurableSet_le measurable_const measurable_norm))).symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- Convergence in `L²(Ω; 𝕜^ι)` from componentwise convergence of representatives. -/
theorem tendsto_toL2F {Ω : Set E} {ι : Type*} [Fintype ι] {F : ℕ → ι → E → 𝕜}
    (hF : ∀ m i, MemLp (F m i) 2 (volume.restrict Ω)) (v : L2F 𝕜 Ω ι)
    (h : ∀ i, Tendsto (fun m => eLpNorm (F m i - (v i : E → 𝕜)) 2 (volume.restrict Ω)) atTop
      (𝓝 0)) :
    Tendsto (fun m => toL2F (hF m)) atTop (𝓝 v) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hi : ∀ i, Tendsto (fun m => dist (toL2F (hF m) i) (v i)) atTop (𝓝 0) := by
    intro i
    have e : ∀ m, dist (toL2F (hF m) i) (v i) =
        (eLpNorm (F m i - (v i : E → 𝕜)) 2 (volume.restrict Ω)).toReal := by
      intro m
      rw [Lp.dist_def]
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hF m i).coeFn_toLp] with x hx
      simp [toL2F, hx]
    simp only [e]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (h i)
    rw [ENNReal.toReal_zero] at this
    exact this
  have := (Real.continuous_sqrt.tendsto _).comp (tendsto_finsetSum (Finset.univ : Finset ι)
    fun i _ => (hi i).pow 2)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
    Real.sqrt_zero] at this
  refine this.congr fun m => ?_
  rw [PiLp.dist_eq_of_L2]
  rfl

/-! ## Minimal = maximal on the whole space -/

namespace ConstCoeffOp

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Cut-off step**: a smooth field all of whose derivatives are in `L²(E)` lies, with its image
under `A`, in the closure of the test graph of `A` on `E`. -/
theorem mem_closure_testGraph_univ (A : ConstCoeffOp E 𝕜 ι κ) {g : ι → E → 𝕜}
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (hgL : ∀ i (l : List E), MemLp (iterDeriv l (g i)) 2 volume)
    (h1 : ∀ i, MemLp (g i) 2 (volume.restrict univ))
    (h2 : ∀ j, MemLp (A.apply g j) 2 (volume.restrict univ)) :
    (toL2F h1, toL2F h2) ∈ (A.testGraph univ).topologicalClosure := by
  set T : ℕ → ι → E → 𝕜 := fun m i x => tcut 𝕜 ((m : ℝ) + 1) x * g i x with hTd
  set φ : ℕ → ι → E → 𝕜 := fun m i x => ((cutoff ((m : ℝ) + 1) x : ℝ) : 𝕜) * g i x with hφd
  have hpos : ∀ m : ℕ, (0 : ℝ) < (m : ℝ) + 1 := fun m => by positivity
  have hcut : ∀ m : ℕ, ContDiff ℝ ∞ (fun x : E => ((cutoff ((m : ℝ) + 1) x : ℝ) : 𝕜)) := fun m =>
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp (contDiff_cutoff _)
  have hφ : ∀ m, IsTestField (univ : Set E) (φ m) := fun m i =>
    ⟨(hcut m).mul (hg i),
      (((hasCompactSupport_cutoff (hpos m)).comp_left (g := fun r : ℝ => (r : 𝕜))
        (by simp)).mul_right),
      subset_univ _⟩
  have hT : ∀ m i, ContDiff ℝ ∞ (T m i) := fun m i => (contDiff_tcut _).mul (hg i)
  have hφT : ∀ m, φ m = g + (-1 : 𝕜) • T m := fun m => by
    funext i x
    simp only [hφd, hTd, tcut, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast; ring
  have hAφ : ∀ m j x, A.apply (φ m) j x - A.apply g j x = -A.apply (T m) j x := by
    intro m j x
    rw [hφT m, A.apply_add (f := g) (g := (-1 : 𝕜) • T m) hg fun i => (hT m i).const_smul (-1 : 𝕜),
      A.apply_smul _ (hT m)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hT0 : ∀ i, Tendsto (fun m => eLpNorm (T m i) 2 volume) atTop (𝓝 0) := fun i =>
    tendsto_eLpNorm_iterDeriv_tcut_mul (hg i) (hgL i) []
  have hAT : ∀ j, Tendsto (fun m => eLpNorm (A.apply (T m) j) 2 volume) atTop (𝓝 0) := by
    intro j
    refine tendsto_eLpNorm_finset_sum Finset.univ (f := fun i m x =>
      applyEntry (A.coeff j i) (T m i) x) fun i _ => ?_
    refine tendsto_eLpNorm_list_sum (A.coeff j i) (f := fun t m x =>
      t.2 * iterDeriv t.1 (T m i) x) fun t _ => ?_
    exact tendsto_eLpNorm_const_mul t.2 (tendsto_eLpNorm_iterDeriv_tcut_mul (hg i) (hgL i) t.1)
  have hlim : Tendsto (fun m => (testField (hφ m), testField (A.isTestField_apply (hφ m)))) atTop
      (𝓝 (toL2F h1, toL2F h2)) := by
    refine Tendsto.prodMk_nhds ?_ ?_
    · refine tendsto_toL2F (F := φ) (fun m i => (hφ m i).memLp) _ fun i => ?_
      have hae : ((toL2F h1) i : E → 𝕜) =ᵐ[volume.restrict univ] g i := (h1 i).coeFn_toLp
      have e : ∀ m, eLpNorm (φ m i - ((toL2F h1) i : E → 𝕜)) 2 (volume.restrict univ) =
          eLpNorm (T m i) 2 volume := by
        intro m
        rw [eLpNorm_congr_ae (EventuallyEq.rfl.sub hae), Measure.restrict_univ, ← eLpNorm_neg]
        congr 1
        funext x
        have := congrFun (congrFun (hφT m) i) x
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
        simp only [Pi.sub_apply, Pi.neg_apply, this]
        ring
      simp only [e]
      exact hT0 i
    · refine tendsto_toL2F (F := fun m => A.apply (φ m))
        (fun m j => (A.isTestField_apply (hφ m) j).memLp) _ fun j => ?_
      have hae : ((toL2F h2) j : E → 𝕜) =ᵐ[volume.restrict univ] A.apply g j := (h2 j).coeFn_toLp
      have e : ∀ m, eLpNorm (A.apply (φ m) j - ((toL2F h2) j : E → 𝕜)) 2 (volume.restrict univ) =
          eLpNorm (A.apply (T m) j) 2 volume := by
        intro m
        rw [eLpNorm_congr_ae (EventuallyEq.rfl.sub hae), Measure.restrict_univ, ← eLpNorm_neg]
        congr 1
        funext x
        simp only [Pi.sub_apply, Pi.neg_apply, hAφ m j x, neg_neg]
      simp only [e]
      exact hAT j
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
    (Eventually.of_forall fun m => Submodule.le_topologicalClosure _ ⟨φ m, hφ m, rfl⟩)

omit [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [Fintype ι] in
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem memLp_univ_iff {f : E → 𝕜} : MemLp f 2 (volume.restrict univ) ↔ MemLp f 2 volume := by
  rw [Measure.restrict_univ]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [Fintype ι] in
omit [NormedAddCommGroup E] in
theorem eLpNorm_restrict_univ (f : E → 𝕜) :
    eLpNorm f 2 (volume.restrict univ) = eLpNorm f 2 volume := by
  rw [Measure.restrict_univ]

/-- The weak identity defining `D(A_max(E))`, as integrals over `E`. -/
theorem maximal_univ_weak (A : ConstCoeffOp E 𝕜 ι κ) (u : (A.maximal univ).domain)
    (ψ : κ → E → 𝕜) (hψ : IsTestField (univ : Set E) ψ) :
    ∑ j, ∫ x, conj ((A.maximal univ u : L2F 𝕜 univ κ) j x) * ψ j x =
      ∑ i, ∫ x, conj ((u : L2F 𝕜 univ ι) i x) * A.formalAdj.apply ψ i x := by
  have h := A.maximal_inner_testField isOpen_univ u hψ
  rw [inner_testField, inner_testField] at h
  simpa only [Measure.restrict_univ] using h

/-- **Mollification step**: for `u ∈ D(A_max(E))`, the graph point `(u, A_max u)` is a limit of
graph points `(ρ_m ⋆ u, ρ_m ⋆ A_max u)` of smooth fields all of whose derivatives are in `L²`;
with the cut-off step, it lies in the closure of the test graph. -/
theorem mem_closure_testGraph_of_mem_maximal_univ (A : ConstCoeffOp E 𝕜 ι κ)
    (u : (A.maximal univ).domain) :
    ((u : L2F 𝕜 univ ι), A.maximal univ u) ∈ (A.testGraph univ).topologicalClosure := by
  classical
  set w : L2F 𝕜 univ κ := A.maximal univ u
  have hu : ∀ i, MemLp ((u : L2F 𝕜 univ ι) i : E → 𝕜) 2 volume := fun i =>
    memLp_univ_iff.1 (Lp.memLp _)
  have hw : ∀ j, MemLp (w j : E → 𝕜) 2 volume := fun j => memLp_univ_iff.1 (Lp.memLp _)
  set g : ℕ → ι → E → 𝕜 := fun m i => kconv ((bumpSeq m).normed volume) ((u : L2F 𝕜 univ ι) i)
    with hgd
  have hgs : ∀ m i, ContDiff ℝ ∞ (g m i) := fun m i =>
    contDiff_kconv (isTest_bumpSeq m) ((hu i).locallyIntegrable (by norm_num))
  have hgL : ∀ m i (l : List E), MemLp (iterDeriv l (g m i)) 2 volume := fun m i l =>
    memLp_iterDeriv_kconv (isTest_bumpSeq m) (hu i) l
  have hAg : ∀ m, A.apply (g m) = fun j => kconv ((bumpSeq m).normed volume) (w j : E → 𝕜) :=
    fun m => A.apply_kconv (isTest_bumpSeq m) hu (A.maximal_univ_weak u)
  have h1 : ∀ m i, MemLp (g m i) 2 (volume.restrict univ) := fun m i =>
    memLp_univ_iff.2 (hgL m i [])
  have h2 : ∀ m j, MemLp (A.apply (g m) j) 2 (volume.restrict univ) := fun m j => by
    rw [hAg m]
    exact memLp_univ_iff.2 (memLp_kconv (bumpSeq m).continuous_normed
      (bumpSeq m).hasCompactSupport_normed (hw j))
  have hmem : ∀ m, (toL2F (h1 m), toL2F (h2 m)) ∈ (A.testGraph univ).topologicalClosure :=
    fun m => A.mem_closure_testGraph_univ (hgs m) (hgL m) (h1 m) (h2 m)
  have hlim : Tendsto (fun m => (toL2F (h1 m), toL2F (h2 m))) atTop
      (𝓝 ((u : L2F 𝕜 univ ι), w)) := by
    refine Tendsto.prodMk_nhds (tendsto_toL2F _ _ fun i => ?_) (tendsto_toL2F _ _ fun j => ?_)
    · simp only [eLpNorm_restrict_univ]
      exact tendsto_eLpNorm_kconv_sub (hu i)
    · simp only [eLpNorm_restrict_univ, hAg]
      exact tendsto_eLpNorm_kconv_sub (hw j)
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim (Eventually.of_forall hmem)

/-- **`A_min(E) = A_max(E)`**: on the whole space, for a constant-coefficient operator of any
order, the closure of `A` on `C_c^∞(E)` is the weak (distributional) realization: `H̊ = H`. -/
theorem minimal_univ_eq_maximal_univ (A : ConstCoeffOp E 𝕜 ι κ) :
    A.minimal univ = A.maximal univ := by
  refine le_antisymm (A.minimal_le_maximal isOpen_univ) (LinearPMap.le_of_le_graph ?_)
  rintro ⟨x, y⟩ hxy
  rw [LinearPMap.mem_graph_iff] at hxy
  obtain ⟨u, rfl, rfl⟩ := hxy
  rw [A.minimal_graph isOpen_univ]
  exact A.mem_closure_testGraph_of_mem_maximal_univ u

/-- `D(A_max(E)) = D(A_min(E))`. -/
theorem maximal_univ_domain_eq (A : ConstCoeffOp E 𝕜 ι κ) :
    (A.maximal univ).domain = (A.minimal univ).domain := by
  rw [A.minimal_univ_eq_maximal_univ]

/-- The restriction to `Ω` of an `L²(E)` field. -/
def restrictL2F (Ω : Set E) (v : L2F 𝕜 (univ : Set E) ι) : L2F 𝕜 Ω ι :=
  toL2F (ψ := fun i => (v i : E → 𝕜)) fun i =>
    (memLp_univ_iff.1 (Lp.memLp (v i) : MemLp (v i : E → 𝕜) 2 (volume.restrict univ))).restrict Ω

omit [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
omit [Fintype ι] in
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem coeFn_restrictL2F (Ω : Set E) (v : L2F 𝕜 (univ : Set E) ι) (i : ι) :
    (restrictL2F Ω v i : E → 𝕜) =ᵐ[volume.restrict Ω] v i :=
  ((memLp_univ_iff.1 (Lp.memLp (v i) : MemLp (v i : E → 𝕜) 2 (volume.restrict univ))).restrict
    Ω).coeFn_toLp

omit [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `L²(E)` convergence of representatives gives convergence of the restrictions in `L²(Ω)`. -/
theorem tendsto_restrictL2F {Ω : Set E} (F : ℕ → ι → E → 𝕜) (v : L2F 𝕜 (univ : Set E) ι)
    (hF : ∀ m i, MemLp (F m i) 2 (volume.restrict Ω))
    (h : ∀ i, Tendsto (fun m => eLpNorm (F m i - (v i : E → 𝕜)) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun m => toL2F (hF m)) atTop (𝓝 (restrictL2F Ω v)) := by
  refine tendsto_toL2F hF _ fun i => ?_
  have e : ∀ m, eLpNorm (F m i - (restrictL2F Ω v i : E → 𝕜)) 2 (volume.restrict Ω) =
      eLpNorm (F m i - (v i : E → 𝕜)) 2 (volume.restrict Ω) := fun m =>
    eLpNorm_congr_ae (EventuallyEq.rfl.sub (coeFn_restrictL2F Ω v i))
  rw [show (fun m => eLpNorm (F m i - (restrictL2F Ω v i : E → 𝕜)) 2 (volume.restrict Ω)) =
    fun m => eLpNorm (F m i - (v i : E → 𝕜)) 2 (volume.restrict Ω) from funext e]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h i) (fun _ => zero_le)
    fun m => eLpNorm_mono_measure _ Measure.restrict_le_self

/-- **Compactly supported elements of `D(A_max(E))` restrict into `D(A_min(Ω))`**: if
`u ∈ D(A_max(E))` vanishes a.e. outside a compact `K ⊆ Ω` (`Ω` open), then
`u|_Ω ∈ D(A_min(Ω))` and `A_min (u|_Ω) = (A_max u)|_Ω`. (The mollifications `ρ_m ⋆ u` are test
fields on `Ω` once the bump radius is below `dist(K, ∂Ω)`, and converge in the graph norm.) -/
theorem mem_minimal_of_support_subset (A : ConstCoeffOp E 𝕜 ι κ) {Ω : Set E} (hΩ : IsOpen Ω)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (u : (A.maximal univ).domain)
    (hu : ∀ i, ∀ᵐ x, x ∉ K → (u : L2F 𝕜 univ ι) i x = 0) :
    ∃ h : restrictL2F Ω (u : L2F 𝕜 univ ι) ∈ (A.minimal Ω).domain,
      A.minimal Ω ⟨_, h⟩ = restrictL2F Ω (A.maximal univ u) := by
  classical
  have : ProperSpace E := FiniteDimensional.proper_real E
  set w : L2F 𝕜 univ κ := A.maximal univ u
  have hu2 : ∀ i, MemLp ((u : L2F 𝕜 univ ι) i : E → 𝕜) 2 volume := fun i =>
    memLp_univ_iff.1 (Lp.memLp _)
  have hw : ∀ j, MemLp (w j : E → 𝕜) 2 volume := fun j => memLp_univ_iff.1 (Lp.memLp _)
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  set g : ℕ → ι → E → 𝕜 := fun m i => kconv ((bumpSeq m).normed volume) ((u : L2F 𝕜 univ ι) i)
    with hgd
  have hgL : ∀ m i (l : List E), MemLp (iterDeriv l (g m i)) 2 volume := fun m i l =>
    memLp_iterDeriv_kconv (isTest_bumpSeq m) (hu2 i) l
  have hAg : ∀ m, A.apply (g m) = fun j => kconv ((bumpSeq m).normed volume) (w j : E → 𝕜) :=
    fun m => A.apply_kconv (isTest_bumpSeq m) hu2 (A.maximal_univ_weak u)
  -- support of the mollifications
  have hsupp : ∀ m, (bumpSeq m : ContDiffBump (0 : E)).rOut < δ → ∀ i,
      tsupport (g m i) ⊆ Metric.cthickening δ K := by
    intro m hm i
    have hind : g m i = kconv ((bumpSeq m).normed volume) (K.indicator ((u : L2F 𝕜 univ ι) i)) := by
      refine kconv_congr_ae _ ?_
      filter_upwards [hu i] with x hx
      by_cases hxK : x ∈ K
      · rw [Set.indicator_of_mem hxK]
      · rw [Set.indicator_of_notMem hxK, hx hxK]
    refine closure_minimal ?_ Metric.isClosed_cthickening
    intro x hx
    rw [hind] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := support_convolution_subset _ hx
    rw [(bumpSeq m).support_normed_eq] at hb
    have haK : a ∈ K := by
      by_contra h
      exact ha (Set.indicator_of_notMem h _)
    refine Metric.mem_cthickening_of_dist_le x a δ K haK ?_
    rw [← hab, dist_eq_norm, add_sub_cancel_left]
    have : ‖b‖ < (bumpSeq (E := E) m).rOut := by simpa using hb
    linarith
  have hφ : ∀ m, (bumpSeq m : ContDiffBump (0 : E)).rOut < δ → IsTestField Ω (g m) :=
    fun m hm i =>
      ⟨contDiff_kconv (isTest_bumpSeq m) ((hu2 i).locallyIntegrable (by norm_num)),
        hK.cthickening.of_isClosed_subset (isClosed_tsupport _) (hsupp m hm i),
        (hsupp m hm i).trans hδΩ⟩
  have h1 : ∀ m i, MemLp (g m i) 2 (volume.restrict Ω) := fun m i => (hgL m i []).restrict Ω
  have h2 : ∀ m j, MemLp (A.apply (g m) j) 2 (volume.restrict Ω) := fun m j => by
    rw [hAg m]
    exact (memLp_kconv (bumpSeq m).continuous_normed (bumpSeq m).hasCompactSupport_normed
      (hw j)).restrict Ω
  have hmem : ∀ᶠ m in atTop, (toL2F (h1 m), toL2F (h2 m)) ∈ A.testGraph Ω := by
    filter_upwards [(tendsto_bumpSeq_rOut (E := E)).eventually (gt_mem_nhds hδ)] with m hm
    exact ⟨g m, hφ m hm, rfl⟩
  have hlim : Tendsto (fun m => (toL2F (h1 m), toL2F (h2 m))) atTop
      (𝓝 (restrictL2F Ω (u : L2F 𝕜 univ ι), restrictL2F Ω w)) := by
    refine Tendsto.prodMk_nhds (tendsto_restrictL2F g _ h1 fun i => ?_)
      (tendsto_restrictL2F _ w h2 fun j => ?_)
    · exact tendsto_eLpNorm_kconv_sub (hu2 i)
    · simp only [hAg]
      exact tendsto_eLpNorm_kconv_sub (hw j)
  have hgr : (restrictL2F Ω (u : L2F 𝕜 univ ι), restrictL2F Ω w) ∈ (A.minimal Ω).graph := by
    rw [A.minimal_graph hΩ]
    exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
      (hmem.mono fun m hm => Submodule.le_topologicalClosure _ hm)
  exact ⟨LinearPMap.mem_domain_of_mem_graph hgr,
    ((LinearPMap.image_iff (LinearPMap.mem_domain_of_mem_graph hgr)).2 hgr).symm⟩

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [Fintype κ] in
/-- `A f` at `x` only depends on the germ of `f` at `x`. -/
theorem apply_congr_nhds (A : ConstCoeffOp E 𝕜 ι κ) {f g : ι → E → 𝕜} {x : E}
    (h : ∀ i, f i =ᶠ[𝓝 x] g i) (j : κ) : A.apply f j x = A.apply g j x := by
  simp only [apply, applyEntry]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine List.map_congr_left fun t _ => ?_
  rw [(iterDeriv_eventuallyEq (h i) t.1).eq_of_nhds]

omit [FiniteDimensional ℝ E] in
/-- Against a test field of `Ω`, the inner product of a restriction is the inner product on `E`. -/
theorem inner_restrictL2F_testField {Ω : Set E} (v : L2F 𝕜 (univ : Set E) ι)
    {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) (hφ' : IsTestField (univ : Set E) φ) :
    ⟪restrictL2F Ω v, testField hφ⟫_𝕜 = ⟪v, testField hφ'⟫_𝕜 := by
  rw [inner_testField, inner_testField]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [setIntegral_univ, ← integral_restrict_of_eq_zero (Ω := Ω) fun x hx => by
    rw [(hφ i).eq_zero_of_notMem hx, mul_zero]]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_restrictL2F Ω v i] with x hx
  rw [hx]

/-- **Restriction maps `D(A_max(E))` into `D(A_max(Ω))`**, and `A_max(u|_Ω) = (A_max u)|_Ω`. -/
theorem restrictL2F_mem_maximal (A : ConstCoeffOp E 𝕜 ι κ) {Ω : Set E} (hΩ : IsOpen Ω)
    (u : (A.maximal univ).domain) :
    ∃ h : restrictL2F Ω (u : L2F 𝕜 univ ι) ∈ (A.maximal Ω).domain,
      A.maximal Ω ⟨_, h⟩ = restrictL2F Ω (A.maximal univ u) := by
  have key : ∀ φ : κ → E → 𝕜, ∀ hφ : IsTestField Ω φ,
      ⟪restrictL2F Ω (A.maximal univ u), testField hφ⟫_𝕜 =
        ⟪restrictL2F Ω (u : L2F 𝕜 univ ι), testField (A.formalAdj.isTestField_apply hφ)⟫_𝕜 := by
    intro φ hφ
    have hφ' : IsTestField (univ : Set E) φ := fun j => (hφ j).mono (subset_univ Ω)
    rw [inner_restrictL2F_testField _ hφ hφ', inner_restrictL2F_testField _
      (A.formalAdj.isTestField_apply hφ) (A.formalAdj.isTestField_apply hφ')]
    exact A.maximal_inner_testField isOpen_univ u hφ'
  have hmem := (A.mem_maximal_domain_iff hΩ).2 ⟨_, key⟩
  exact ⟨hmem, A.maximal_apply_eq hΩ ⟨_, hmem⟩ key⟩

/-- The extension by zero to `E` of an `L²(Ω)` field. -/
def extendL2F {Ω : Set E} (hΩ : MeasurableSet Ω) (v : L2F 𝕜 Ω ι) : L2F 𝕜 (univ : Set E) ι :=
  toL2F (ψ := fun i => Ω.indicator (v i : E → 𝕜)) fun i =>
    memLp_univ_iff.2 ((memLp_indicator_iff_restrict hΩ.nullMeasurableSet).2 (Lp.memLp (v i)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [Fintype ι] in
theorem coeFn_extendL2F {Ω : Set E} (hΩ : MeasurableSet Ω) (v : L2F 𝕜 Ω ι) (i : ι) :
    (extendL2F hΩ v i : E → 𝕜) =ᵐ[volume] Ω.indicator (v i : E → 𝕜) := by
  have h := (memLp_univ_iff.2 ((memLp_indicator_iff_restrict hΩ.nullMeasurableSet).2
    (Lp.memLp (v i)))).coeFn_toLp
  filter_upwards [(ae_restrict_iff' MeasurableSet.univ).1 h] with x hx using hx (mem_univ x)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [Fintype ι] in
/-- Restricting the extension by zero gives back the field. -/
theorem restrictL2F_extendL2F {Ω : Set E} (hΩ : MeasurableSet Ω) (v : L2F 𝕜 Ω ι) :
    restrictL2F Ω (extendL2F hΩ v) = v := by
  refine PiLp.ext fun i => Lp.ext ?_
  filter_upwards [coeFn_restrictL2F Ω (extendL2F hΩ v) i,
    ae_restrict_of_ae (coeFn_extendL2F hΩ v i), ae_restrict_mem hΩ] with x h1 h2 h3
  rw [h1, h2, indicator_of_mem h3]

omit [FiniteDimensional ℝ E] in
/-- `⟪ũ, φ⟫_{L²(E)} = Σᵢ ∫_Ω conj uᵢ φᵢ` for the extension by zero `ũ`. -/
theorem inner_extendL2F_testField {Ω : Set E} (hΩ : MeasurableSet Ω) (v : L2F 𝕜 Ω ι)
    {φ : ι → E → 𝕜} (hφ : IsTestField (univ : Set E) φ) :
    ⟪extendL2F hΩ v, testField hφ⟫_𝕜 = ∑ i, ∫ x, conj (v i x) * φ i x ∂volume.restrict Ω := by
  rw [inner_testField]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [setIntegral_univ, ← integral_indicator hΩ]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_extendL2F hΩ v i] with x hx
  rw [hx]
  by_cases h : x ∈ Ω <;> simp [h]

/-- **Compactly supported elements of `D(A_max(Ω))` lie in `D(A_min(Ω))`**: if `u ∈ D(A_max(Ω))`
vanishes a.e. outside a compact `K ⊆ Ω` (`Ω` open), then `u ∈ D(A_min(Ω))` (and `A_min u = A_max u`).
With a cut-off `χ ∈ C_c^∞(Ω)` equal to `1` near `K`, the extension by zero `ũ` satisfies
`A_max(E) ũ = (χ A_max u)~` (test against `χ ψ`), so `mem_minimal_of_support_subset` applies. -/
theorem mem_minimal_of_maximal_of_support_subset (A : ConstCoeffOp E 𝕜 ι κ) {Ω : Set E}
    (hΩ : IsOpen Ω) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (u : (A.maximal Ω).domain)
    (hu : ∀ i, ∀ᵐ x ∂volume.restrict Ω, x ∉ K → (u : L2F 𝕜 Ω ι) i x = 0) :
    ∃ h : (u : L2F 𝕜 Ω ι) ∈ (A.minimal Ω).domain, A.minimal Ω ⟨_, h⟩ = A.maximal Ω u := by
  classical
  have : ProperSpace E := FiniteDimensional.proper_real E
  have hΩm := hΩ.measurableSet
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨χ, hχs, hχr, hχsupp, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (Metric.isOpen_thickening (δ := δ) (E := K)) (Metric.isClosed_cthickening (δ := δ / 2) (E := K))
    (Metric.cthickening_subset_thickening' hδ (by linarith) K)
  have hχts : tsupport χ ⊆ Metric.cthickening δ K := by
    rw [tsupport, hχsupp]; exact Metric.closure_thickening_subset_cthickening δ K
  have hχT : IsTest Ω (fun x => (χ x : 𝕜)) :=
    IsTest.ofReal ⟨hχs, hK.cthickening.of_isClosed_subset (isClosed_tsupport _) hχts,
      hχts.trans hδΩ⟩
  have hχle : ∀ x, ‖(χ x : 𝕜)‖ ≤ 1 := fun x => by
    have := hχr (mem_range_self x)
    rw [RCLike.norm_ofReal, abs_of_nonneg this.1]; exact this.2
  -- the cut-off of a test field of `E` is a test field of `Ω`
  have hcut : ∀ {φ : κ → E → 𝕜}, IsTestField (univ : Set E) φ →
      IsTestField Ω (fun j x => (χ x : 𝕜) * φ j x) := fun hφ j =>
    ⟨hχT.contDiff.mul (hφ j).contDiff, hχT.hasCompactSupport.mul_right,
      tsupport_mul_subset_left.trans hχT.tsupport_subset⟩
  set w : L2F 𝕜 Ω κ := A.maximal Ω u
  have hχw : ∀ j, MemLp (fun x => (χ x : 𝕜) * w j x) 2 (volume.restrict Ω) := fun j =>
    (Lp.memLp (w j)).of_le (hχT.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _))
      (Eventually.of_forall fun x => by
        rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hχle x))
  set U := extendL2F hΩm (u : L2F 𝕜 Ω ι)
  set W := extendL2F hΩm (toL2F hχw)
  have key : ∀ ψ : κ → E → 𝕜, ∀ hψ : IsTestField (univ : Set E) ψ,
      ⟪W, testField hψ⟫_𝕜 = ⟪U, testField (A.formalAdj.isTestField_apply hψ)⟫_𝕜 := by
    intro ψ hψ
    have e1 : ⟪W, testField hψ⟫_𝕜 = ⟪w, testField (hcut hψ)⟫_𝕜 := by
      rw [inner_extendL2F_testField, inner_testField]
      refine Finset.sum_congr rfl fun j _ => integral_congr_ae ?_
      filter_upwards [(hχw j).coeFn_toLp] with x hx
      simp only [toL2F] at hx ⊢
      rw [hx, map_mul, RCLike.conj_ofReal]; ring
    have e2 : ⟪(u : L2F 𝕜 Ω ι), testField (A.formalAdj.isTestField_apply (hcut hψ))⟫_𝕜 =
        ⟪U, testField (A.formalAdj.isTestField_apply hψ)⟫_𝕜 := by
      rw [inner_extendL2F_testField, inner_testField]
      refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
      filter_upwards [hu i] with x hx
      by_cases hxK : x ∈ K
      · congr 1
        refine A.formalAdj.apply_congr_nhds (fun j => ?_) i
        filter_upwards [Metric.isOpen_thickening.mem_nhds
          (Metric.self_subset_thickening (half_pos hδ) K hxK)] with y hy
        rw [(hχ1 y).1 (Metric.thickening_subset_cthickening _ _ hy), RCLike.ofReal_one, one_mul]
      · rw [hx hxK, map_zero, zero_mul, zero_mul]
    rw [e1, A.maximal_inner_testField hΩ u (hcut hψ), e2]
  have hU := (A.mem_maximal_domain_iff isOpen_univ).2 ⟨W, key⟩
  have hsupp : ∀ i, ∀ᵐ x, x ∉ K → (U : L2F 𝕜 univ ι) i x = 0 := fun i => by
    filter_upwards [coeFn_extendL2F hΩm (u : L2F 𝕜 Ω ι) i, (ae_restrict_iff' hΩm).1 (hu i)]
      with x h1 h2 hxK
    rw [h1]
    by_cases hxΩ : x ∈ Ω
    · rw [indicator_of_mem hxΩ, h2 hxΩ hxK]
    · rw [indicator_of_notMem hxΩ]
  obtain ⟨h, -⟩ := A.mem_minimal_of_support_subset hΩ hK hKΩ ⟨U, hU⟩ hsupp
  have h' : (u : L2F 𝕜 Ω ι) ∈ (A.minimal Ω).domain := by
    simpa only [U, restrictL2F_extendL2F] using h
  exact ⟨h', (A.minimal_le_maximal hΩ).2 rfl⟩

end ConstCoeffOp

/-- **The minimal and maximal complexes of `E` coincide**, for every complex of
constant-coefficient operators. -/
theorem ConstCoeffComplex.minimalComplex_univ_eq_maximalComplex_univ
    (C : ConstCoeffComplex E 𝕜) :
    C.minimalComplex isOpen_univ = C.maximalComplex isOpen_univ := by
  have h : (fun k => (C.A k).minimal univ) = fun k => (C.A k).maximal univ :=
    funext fun k => (C.A k).minimal_univ_eq_maximal_univ
  unfold ConstCoeffComplex.minimalComplex ConstCoeffComplex.maximalComplex
  congr 1

/-- **`H̊Λᵏ(ℝⁿ) = HΛᵏ(ℝⁿ)`**: the minimal and maximal exterior derivatives of `ℝⁿ` coincide. -/
theorem extDerivOp_minimal_univ_eq_maximal_univ (n : ℕ) (k : ℤ) :
    (extDerivOp 𝕜 n k).minimal univ = (extDerivOp 𝕜 n k).maximal univ :=
  (extDerivOp 𝕜 n k).minimal_univ_eq_maximal_univ

/-- **The minimal and maximal de Rham complexes of `ℝⁿ` coincide.** -/
theorem deRham_minimalComplex_univ_eq_maximalComplex_univ (n : ℕ) :
    (deRham 𝕜 n).minimalComplex isOpen_univ = (deRham 𝕜 n).maximalComplex isOpen_univ :=
  (deRham 𝕜 n).minimalComplex_univ_eq_maximalComplex_univ

end Feec.Domain
