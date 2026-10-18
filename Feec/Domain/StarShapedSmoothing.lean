module

public import Feec.Domain.Mollify
public import Feec.Domain.DeRham

/-!
# Smoothing operators on domains star-shaped with respect to a ball

Let `Ω ⊆ E = ℝⁿ` be open and bounded. For a centre `x₀`, a factor `c ≥ ½` and a bump `φ`, the
**smoother** `R` maps `u ∈ L²(Ω)` to the restriction to `Ω` of
`x ↦ (ū ⋆ ρ_φ)(x₀ + c (x - x₀))`, `ū` the zero extension (`smoothExt`, `smoothL2`). It is
smooth on all of `E`, linear, bounded on `L²(Ω)` by `2ⁿ` (by `1` if `c ≥ 1`)
(`norm_smoothL2_le`, `norm_smoothL2_le_of_one_le`), and converges strongly to the identity as
`c → 1` and the bump radius `→ 0` (`exists_norm_smoothL2_sub_lt`). On fields
`u ∈ L²(Ω; ℝ^ι)` it acts componentwise with a scalar weight `a` (`smoothField`).

If `Ω` is star-shaped with respect to every point of a ball `B(x₀, s)`, `R` commutes with
constant-coefficient operators, up to the chain-rule factor of the dilation, in both families of
realizations:

* **minimal (zero trace) family**, `c > 1` and bump radius `< s (c - 1) / 2`: `R u` is a test
  field on `Ω` (`isTestField_smoothExt`), and for a row-homogeneous `A` (orders `k j`) and
  `u ∈ D(A_min)`, `R u ∈ D(A_min)` with `A_min (R_a u) = R_{a c^k} (A_min u)`
  (`smoothField_mem_minimal_domain`, `minimal_smoothField`). The key identity is that the zero
  extension of `u ∈ D(A_min)` satisfies `A ū = (A_min u)‾` in `𝒟'(E)`
  (`sum_integral_indicator_formalAdj_eq`).
* **maximal (no boundary condition) family**, `½ ≤ c < 1` and bump radius `< s (1 - c) / 4`:
  only points whose `φ`-ball lies in `Ω` are sampled, and for `u ∈ D(A_max)`,
  `R u ∈ D(A_max)` with `A_max (R_a u) = R_{a c^k} (A_max u)`
  (`smoothField_mem_maximal_domain`, `maximal_smoothField`); `R u` is smooth on `E`, in
  particular on a neighbourhood of `cl Ω`.

For the de Rham complex (`Feec.Domain.deRham`), `d` is homogeneous of order one, so the
**pullback of `k`-forms by the dilation** `x ↦ x₀ + c (x - x₀)`, which multiplies the
coefficients of a `k`-form by `cᵏ`, commutes **exactly** with `d`: the weights `cᵏ` on `k`-forms
give `d_min (cᵏ R ω) = c^{k+1} R (d_min ω)` (`deRham_minimal_smoothField`) and likewise for
`d_max` (`deRham_maximal_smoothField`). These are the smoothers `R_ε` of [AFW2010], §5.4 and
[ChristiansenWinther2008] in the case of a domain star-shaped with respect to a ball (cubes,
convex domains).

## Main definitions

* `Feec.Domain.SmoothingParam`: centre, factor `c ≥ ½` and bump.
* `Feec.Domain.smoothExt`: `x ↦ (ū ⋆ ρ)(x₀ + c (x - x₀))`.
* `Feec.Domain.smoothL2`: the smoother on `L²(Ω)`; `Feec.Domain.smoothField`: on `L²(Ω; ℝ^ι)`
  with a weight.

## Main results

* `norm_smoothL2_le`, `norm_smoothL2_le_of_one_le`, `norm_smoothField_le`: `L²` bounds.
* `exists_norm_smoothL2_sub_lt`, `exists_norm_smoothField_sub_lt`: strong convergence.
* `isTestField_smoothExt`, **`smoothField_mem_minimal_domain`**, **`minimal_smoothField`**.
* **`smoothField_mem_maximal_domain`**, **`maximal_smoothField`**.
* **`deRham_minimal_smoothField`**, **`deRham_maximal_smoothField`**: exact commutation with `d`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.4 (smoothing by dilation and mollification; pullbacks commute with `d`)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  Ch. 4 (convolution and mollifiers)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (smoothed projections)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Convolution NNReal

namespace Feec.Domain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-! ## The scalar smoother -/

variable (E) in
/-- **Smoothing parameters**: the centre `x₀` of the dilation, the factor `c ≥ ½` and the bump
`φ` of the mollifier. -/
structure SmoothingParam where
  /-- the centre of the dilation -/
  center : E
  /-- the dilation factor -/
  factor : ℝ
  half_le_factor : 1 / 2 ≤ factor
  /-- the bump of the mollifier -/
  bump : ContDiffBump (0 : E)

namespace SmoothingParam

variable (p : SmoothingParam E)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem factor_pos : 0 < p.factor := by linarith [p.half_le_factor]

end SmoothingParam

variable (Ω : Set E) (p : SmoothingParam E)

/-- The smoothed zero extension `x ↦ (ū ⋆ ρ_φ)(x₀ + c (x - x₀))`, `ū = 1_Ω u`. -/
def smoothExt (f : E → ℝ) : E → ℝ :=
  dil p.center p.factor (molli p.bump (Ω.indicator f))

variable {Ω p}

theorem contDiff_smoothExt {f : E → ℝ} (hf : LocallyIntegrable (Ω.indicator f) volume) :
    ContDiff ℝ ∞ (smoothExt Ω p f) :=
  contDiff_dil _ _ (contDiff_molli _ hf)

theorem eLpNorm_smoothExt_le {f : E → ℝ} (hf : MemLp (Ω.indicator f) 2 volume) :
    eLpNorm (smoothExt Ω p f) 2 volume ≤
      2 ^ Module.finrank ℝ E * eLpNorm (Ω.indicator f) 2 volume :=
  (eLpNorm_dil_le_of_half_le _ p.half_le_factor
    (continuous_molli _ (hf.locallyIntegrable (by norm_num))).aestronglyMeasurable).trans
    (by gcongr; exact eLpNorm_molli_le _ hf)

theorem eLpNorm_smoothExt_le_of_one_le (hc : 1 ≤ p.factor) {f : E → ℝ}
    (hf : MemLp (Ω.indicator f) 2 volume) :
    eLpNorm (smoothExt Ω p f) 2 volume ≤ eLpNorm (Ω.indicator f) 2 volume :=
  (eLpNorm_dil_le _ hc
    (continuous_molli _ (hf.locallyIntegrable (by norm_num))).aestronglyMeasurable).trans
    (eLpNorm_molli_le _ hf)

theorem memLp_smoothExt {f : E → ℝ} (hf : MemLp (Ω.indicator f) 2 volume) :
    MemLp (smoothExt Ω p f) 2 volume :=
  lt_of_le_of_lt (eLpNorm_smoothExt_le hf)
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) hf.eLpNorm_lt_top)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- The zero extension of `u ∈ L²(Ω)` is in `L²(E)`. -/
theorem memLp_indicator (hΩ : MeasurableSet Ω) (u : L2 ℝ Ω) :
    MemLp (Ω.indicator (u : E → ℝ)) 2 volume :=
  (memLp_indicator_iff_restrict hΩ.nullMeasurableSet).2 (Lp.memLp u)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem eLpNorm_indicator_eq_norm (hΩ : MeasurableSet Ω) (u : L2 ℝ Ω) :
    (eLpNorm (Ω.indicator (u : E → ℝ)) 2 volume).toReal = ‖u‖ := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hΩ.nullMeasurableSet, Lp.norm_def]

theorem memLp_smoothExt_restrict (hΩ : MeasurableSet Ω) (u : L2 ℝ Ω) :
    MemLp (smoothExt Ω p (u : E → ℝ)) 2 (volume.restrict Ω) :=
  (memLp_smoothExt (memLp_indicator hΩ u)).restrict Ω

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- Zero extensions of a.e. equal functions are a.e. equal. -/
theorem indicator_ae_eq_of_restrict (hΩ : MeasurableSet Ω) {f g : E → ℝ}
    (h : f =ᵐ[volume.restrict Ω] g) : Ω.indicator f =ᵐ[volume] Ω.indicator g := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hΩ] at h
  filter_upwards [h] with x hx
  by_cases hxΩ : x ∈ Ω
  · rw [indicator_of_mem hxΩ, indicator_of_mem hxΩ, hx hxΩ]
  · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxΩ]

theorem molli_congr_ae (φ : ContDiffBump (0 : E)) {f g : E → ℝ} (h : f =ᵐ[volume] g) :
    molli φ f = molli φ g :=
  convolution_congr _ h (ae_eq_refl _)

theorem smoothExt_congr_ae (hΩ : MeasurableSet Ω) {f g : E → ℝ}
    (h : f =ᵐ[volume.restrict Ω] g) : smoothExt Ω p f = smoothExt Ω p g := by
  rw [smoothExt, smoothExt, molli_congr_ae _ (indicator_ae_eq_of_restrict hΩ h)]

theorem smoothExt_add {f g : E → ℝ} (hf : LocallyIntegrable (Ω.indicator f) volume)
    (hg : LocallyIntegrable (Ω.indicator g) volume) :
    smoothExt Ω p (f + g) = smoothExt Ω p f + smoothExt Ω p g := by
  rw [smoothExt, indicator_add', molli_add _ hf hg, dil_add]; rfl

omit [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem smoothExt_smul (a : ℝ) (f : E → ℝ) :
    smoothExt Ω p (a • f) = a • smoothExt Ω p f := by
  have h : Ω.indicator (a • f) = a • Ω.indicator f := by
    funext x; by_cases hx : x ∈ Ω <;> simp [hx]
  rw [smoothExt, h, molli, smul_convolution]; rfl

theorem smoothExt_coe_add (hΩ : MeasurableSet Ω) (u v : L2 ℝ Ω) :
    smoothExt Ω p ((u + v : L2 ℝ Ω) : E → ℝ) = smoothExt Ω p u + smoothExt Ω p v := by
  rw [smoothExt_congr_ae hΩ (Lp.coeFn_add u v),
    smoothExt_add ((memLp_indicator hΩ u).locallyIntegrable (by norm_num))
      ((memLp_indicator hΩ v).locallyIntegrable (by norm_num))]

theorem smoothExt_coe_smul (hΩ : MeasurableSet Ω) (a : ℝ) (u : L2 ℝ Ω) :
    smoothExt Ω p ((a • u : L2 ℝ Ω) : E → ℝ) = a • smoothExt Ω p u := by
  rw [smoothExt_congr_ae hΩ (Lp.coeFn_smul a u), smoothExt_smul]

theorem norm_toLp_smoothExt_le (hΩ : MeasurableSet Ω) (u : L2 ℝ Ω) :
    ‖(memLp_smoothExt_restrict (p := p) hΩ u).toLp _‖ ≤ 2 ^ Module.finrank ℝ E * ‖u‖ := by
  rw [Lp.norm_toLp, ← eLpNorm_indicator_eq_norm hΩ u]
  have h := (eLpNorm_mono_measure (smoothExt Ω p (u : E → ℝ))
    (Measure.restrict_le_self (μ := volume) (s := Ω))).trans
    (eLpNorm_smoothExt_le (p := p) (memLp_indicator hΩ u))
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp)
    (memLp_indicator hΩ u).eLpNorm_ne_top) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at h'

/-- **The smoother on `L²(Ω)`**: `R u = (ū ⋆ ρ)(x₀ + c (· - x₀))|_Ω`, bounded by `2ⁿ`. -/
def smoothL2 (p : SmoothingParam E) (hΩ : MeasurableSet Ω) : L2 ℝ Ω →L[ℝ] L2 ℝ Ω :=
  LinearMap.mkContinuous
    { toFun := fun u => (memLp_smoothExt_restrict (p := p) hΩ u).toLp _
      map_add' := fun u v => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
        rw [smoothExt_coe_add hΩ]
      map_smul' := fun a u => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
        rw [smoothExt_coe_smul hΩ] }
    (2 ^ Module.finrank ℝ E) fun u => norm_toLp_smoothExt_le hΩ u

theorem smoothL2_apply (hΩ : MeasurableSet Ω) (u : L2 ℝ Ω) :
    smoothL2 p hΩ u = (memLp_smoothExt_restrict (p := p) hΩ u).toLp _ := rfl

theorem coeFn_smoothL2 (hΩ : MeasurableSet Ω) (u : L2 ℝ Ω) :
    (smoothL2 p hΩ u : E → ℝ) =ᵐ[volume.restrict Ω] smoothExt Ω p (u : E → ℝ) :=
  (memLp_smoothExt_restrict (p := p) hΩ u).coeFn_toLp

/-- `‖R u‖ ≤ 2ⁿ ‖u‖`. -/
theorem norm_smoothL2_le (hΩ : MeasurableSet Ω) (u : L2 ℝ Ω) :
    ‖smoothL2 p hΩ u‖ ≤ 2 ^ Module.finrank ℝ E * ‖u‖ :=
  norm_toLp_smoothExt_le hΩ u

/-- **`R` is an `L²(Ω)`-contraction for `c ≥ 1`.** -/
theorem norm_smoothL2_le_of_one_le (hΩ : MeasurableSet Ω) (hc : 1 ≤ p.factor) (u : L2 ℝ Ω) :
    ‖smoothL2 p hΩ u‖ ≤ ‖u‖ := by
  rw [smoothL2_apply, Lp.norm_toLp, ← eLpNorm_indicator_eq_norm hΩ u]
  refine ENNReal.toReal_mono (memLp_indicator hΩ u).eLpNorm_ne_top ?_
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
    (eLpNorm_smoothExt_le_of_one_le hc (memLp_indicator hΩ u))

/-- `‖R u - u‖_{L²(Ω)} ≤ ‖R̃ ū - ū‖_{L²(E)}`. -/
theorem norm_smoothL2_sub_le (hΩ : MeasurableSet Ω) (u : L2 ℝ Ω) :
    ‖smoothL2 p hΩ u - u‖ ≤
      (eLpNorm (smoothExt Ω p (u : E → ℝ) - Ω.indicator (u : E → ℝ)) 2 volume).toReal := by
  have hm : MemLp (smoothExt Ω p (u : E → ℝ) - Ω.indicator (u : E → ℝ)) 2 volume :=
    (memLp_smoothExt (memLp_indicator hΩ u)).sub (memLp_indicator hΩ u)
  rw [Lp.norm_def]
  refine ENNReal.toReal_mono hm.eLpNorm_ne_top ?_
  calc eLpNorm (⇑(smoothL2 p hΩ u - u)) 2 (volume.restrict Ω)
      = eLpNorm (smoothExt Ω p (u : E → ℝ) - Ω.indicator (u : E → ℝ)) 2 (volume.restrict Ω) := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [Lp.coeFn_sub (smoothL2 p hΩ u) u, coeFn_smoothL2 (p := p) hΩ u,
          indicator_ae_eq_restrict (μ := volume) (f := (u : E → ℝ))
            hΩ.nullMeasurableSet] with x h1 h2 h3
        rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3]
    _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self

/-- **Strong convergence of the smoother**: for `u ∈ L²(Ω)` and `ε > 0`, `‖R u - u‖ < ε` once
`|c - 1|` and the bump radius are small enough (both families: `c < 1` allowed). -/
theorem exists_norm_smoothL2_sub_lt (hΩ : MeasurableSet Ω) (x₀ : E) (u : L2 ℝ Ω) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ η > 0, ∀ p : SmoothingParam E, p.center = x₀ → |p.factor - 1| < η → p.bump.rOut < η →
      ‖smoothL2 p hΩ u - u‖ < ε := by
  obtain ⟨η, hη, -, hηP⟩ :=
    eLpNorm_dil_molli_sub_le_of_abs x₀ (memLp_indicator hΩ u) (half_pos hε)
  refine ⟨η, hη, fun p hp hc hr => ?_⟩
  have h := hηP p.factor hc p.bump hr
  rw [← hp] at h
  refine (norm_smoothL2_sub_le hΩ u).trans_lt ((ENNReal.toReal_le_of_le_ofReal
    (half_pos hε).le h).trans_lt (half_lt_self hε))

/-! ## Fields -/

section Field

variable {ι : Type*}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- A componentwise bound `‖v i‖ ≤ K ‖u i‖` gives `‖v‖ ≤ K ‖u‖` in `L²(Ω; ℝ^ι)`. -/
theorem L2F.norm_le_of_forall [Fintype ι] {u v : L2F ℝ Ω ι} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i, ‖v i‖ ≤ K * ‖u i‖) : ‖v‖ ≤ K * ‖u‖ := by
  have hsq : ‖v‖ ^ 2 ≤ (K * ‖u‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (h i) 2
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

/-- **The smoother on fields** with weights `w`: `(R_w u)ᵢ = wᵢ R uᵢ`. For `k`-forms the weight
`cᵏ` makes `R_w` the pullback by the dilation followed by mollification
(`deRham_minimal_smoothField`). -/
def smoothField [Fintype ι] (p : SmoothingParam E) (hΩ : MeasurableSet Ω) (w : ι → ℝ) :
    L2F ℝ Ω ι →L[ℝ] L2F ℝ Ω ι :=
  LinearMap.mkContinuous
    { toFun := fun u => WithLp.toLp 2 fun i => w i • smoothL2 p hΩ (u i)
      map_add' := fun u v => by
        refine (WithLp.ext_iff 2).2 (funext fun i => ?_)
        simp [smul_add]
      map_smul' := fun a u => by
        refine (WithLp.ext_iff 2).2 (funext fun i => ?_)
        simp [smul_comm (w i) a] }
    ((∑ i, |w i|) * 2 ^ Module.finrank ℝ E) fun u => by
      refine L2F.norm_le_of_forall
        (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)) fun i => ?_
      change ‖w i • smoothL2 p hΩ (u i)‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs, mul_assoc]
      have hw : |w i| ≤ ∑ i, |w i| :=
        Finset.single_le_sum (f := fun i => |w i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      exact mul_le_mul hw (norm_smoothL2_le hΩ (u i)) (norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _)

variable [Fintype ι]

@[simp] theorem smoothField_apply (hΩ : MeasurableSet Ω) (w : ι → ℝ) (u : L2F ℝ Ω ι) (i : ι) :
    smoothField p hΩ w u i = w i • smoothL2 p hΩ (u i) := rfl

/-- `‖R_a u‖ ≤ |a| 2ⁿ ‖u‖` (constant weight). -/
theorem norm_smoothField_le (hΩ : MeasurableSet Ω) (a : ℝ) (u : L2F ℝ Ω ι) :
    ‖smoothField p hΩ (fun _ => a) u‖ ≤ |a| * 2 ^ Module.finrank ℝ E * ‖u‖ := by
  refine L2F.norm_le_of_forall (by positivity) fun i => ?_
  rw [smoothField_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_smoothL2_le hΩ (u i)) (abs_nonneg a)

/-- `‖R_a u‖ ≤ |a| ‖u‖` for `c ≥ 1` (constant weight). -/
theorem norm_smoothField_le_of_one_le (hΩ : MeasurableSet Ω) (hc : 1 ≤ p.factor) (a : ℝ)
    (u : L2F ℝ Ω ι) : ‖smoothField p hΩ (fun _ => a) u‖ ≤ |a| * ‖u‖ := by
  refine L2F.norm_le_of_forall (abs_nonneg a) fun i => ?_
  rw [smoothField_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_smoothL2_le_of_one_le hΩ hc (u i)) (abs_nonneg a)

/-- **Strong convergence of the field smoother**: `R_a u → u` as `c → 1`, the bump radius `→ 0`
and `a → 1`. -/
theorem exists_norm_smoothField_sub_lt (hΩ : MeasurableSet Ω) (x₀ : E) (u : L2F ℝ Ω ι) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ η > 0, ∀ p : SmoothingParam E, p.center = x₀ → |p.factor - 1| < η → p.bump.rOut < η →
      ∀ a : ℝ, |a - 1| < η → ‖smoothField p hΩ (fun _ => a) u - u‖ < ε := by
  set N : ℝ := (Fintype.card ι : ℝ) + 1 with hN
  have hN0 : 0 < N := by positivity
  set ε' := ε / N with hε'd
  have hε' : 0 < ε' := by positivity
  have hex := fun i => exists_norm_smoothL2_sub_lt hΩ x₀ (u i) (half_pos hε')
  choose η hη hηP using hex
  set M : ℝ := 2 ^ Module.finrank ℝ E * (‖u‖ + 1)
  have hM : 0 < M := by positivity
  set T : Finset ℝ := insert (ε' / (2 * M)) (Finset.univ.image η)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  set η₀ := T.min' hT
  have hη₀M : η₀ ≤ ε' / (2 * M) := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hη₀i : ∀ i, η₀ ≤ η i := fun i =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hη₀ : 0 < η₀ := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · positivity
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hη i
  refine ⟨η₀, hη₀, fun p hp hc hr a ha => ?_⟩
  have hcomp : ∀ i, ‖(smoothField p hΩ (fun _ => a) u - u) i‖ ≤ ε' := by
    intro i
    have e : (smoothField p hΩ (fun _ => a) u - u) i =
        (a - 1) • smoothL2 p hΩ (u i) + (smoothL2 p hΩ (u i) - u i) := by
      rw [PiLp.sub_apply, smoothField_apply, sub_smul, one_smul]; abel
    have h1 := hηP i p hp (hc.trans_le (hη₀i i)) (hr.trans_le (hη₀i i))
    have h2 : ‖(a - 1) • smoothL2 p hΩ (u i)‖ ≤ ε' / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |a - 1| * ‖smoothL2 p hΩ (u i)‖ ≤ (ε' / (2 * M)) * (2 ^ Module.finrank ℝ E * ‖u‖) :=
            mul_le_mul (ha.le.trans hη₀M) ((norm_smoothL2_le hΩ (u i)).trans
              (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u i) (by positivity)))
              (norm_nonneg _) (by positivity)
        _ ≤ (ε' / (2 * M)) * M := by
            gcongr; simp only [M]; gcongr; linarith
        _ = ε' / 2 := by field_simp
    rw [e]
    calc _ ≤ ‖(a - 1) • smoothL2 p hΩ (u i)‖ + ‖smoothL2 p hΩ (u i) - u i‖ := norm_add_le _ _
      _ ≤ ε' / 2 + ε' / 2 := add_le_add h2 h1.le
      _ = ε' := by ring
  rw [← dist_eq_norm, PiLp.dist_eq_of_L2, Real.sqrt_lt' hε]
  calc ∑ i, dist (smoothField p hΩ (fun _ => a) u i) (u i) ^ 2 ≤ ∑ _i : ι, ε' ^ 2 := by
        refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ dist_nonneg ?_ 2
        rw [dist_eq_norm, ← PiLp.sub_apply]; exact hcomp i
    _ = (Fintype.card ι : ℝ) * ε' ^ 2 := by simp
    _ < ε ^ 2 := by
        rw [hε'd, div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
        have : (Fintype.card ι : ℝ) < N ^ 2 := by rw [hN]; nlinarith
        nlinarith [sq_nonneg ε, sq_pos_of_pos hε]

end Field

/-! ## Commutation with constant-coefficient operators -/

section Commute

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [Fintype ι] [Fintype κ] in
/-- `∫_Ω f g = ∫_E 1_Ω f · g`. -/
theorem integral_restrict_mul_eq (hΩ : MeasurableSet Ω) (f g : E → ℝ) :
    ∫ x, f x * g x ∂volume.restrict Ω = ∫ x, Ω.indicator f x * g x := by
  rw [← integral_indicator hΩ]
  congr 1; funext x
  by_cases hx : x ∈ Ω <;> simp [hx]

/-- **Zero extensions of `D(A_min)`**: for `u ∈ D(A_min)`, `A ū = (A_min u)‾` in `𝒟'(E)`, i.e.
`Σᵢ ∫_E ūᵢ (Aᵗ ψ)ᵢ = Σⱼ ∫_E (A_min u)‾ⱼ ψⱼ` for every `ψ ∈ C_c^∞(E; ℝ^κ)` (Green's formula with
no boundary term, `ConstCoeffOp.minimal_green`). -/
theorem sum_integral_indicator_formalAdj_eq (hΩ : IsOpen Ω) (A : ConstCoeffOp E ℝ ι κ)
    (u : (A.minimal Ω).domain) {ψ : κ → E → ℝ} (hψ : IsTestField (univ : Set E) ψ) :
    ∑ i, ∫ x, Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ)) x * A.formalAdj.apply ψ i x =
      ∑ j, ∫ x, Ω.indicator ((A.minimal Ω u j : E → ℝ)) x * ψ j x := by
  have hψm : ∀ j, MemLp (ψ j) 2 (volume.restrict Ω) := fun j =>
    ((hψ j).continuous.memLp_of_hasCompactSupport (hψ j).hasCompactSupport).restrict Ω
  have hAψ := A.formalAdj.isTestField_apply hψ
  have hAψm : ∀ i, MemLp (A.formalAdj.apply ψ i) 2 (volume.restrict Ω) := fun i =>
    ((hAψ i).continuous.memLp_of_hasCompactSupport (hAψ i).hasCompactSupport).restrict Ω
  have h := A.minimal_green hΩ A.isOrderLE_order u
    (fun j => (hψ j).contDiff.of_le (by exact_mod_cast le_top)) hψm hAψm
  rw [inner_toL2F, inner_toL2F] at h
  simp only [conj_trivial, integral_restrict_mul_eq hΩ.measurableSet] at h
  exact h.symm

/-- The mollified zero extension of `u ∈ D(A_min)`: `A (ū ⋆ ρ) = (A_min u)‾ ⋆ ρ` everywhere. -/
theorem apply_molli_indicator_of_minimal [DecidableEq κ] (hΩ : IsOpen Ω)
    (A : ConstCoeffOp E ℝ ι κ) (φ : ContDiffBump (0 : E)) (u : (A.minimal Ω).domain) (j : κ)
    (y : E) :
    A.apply (fun i => molli φ (Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ)))) j y =
      molli φ (Ω.indicator ((A.minimal Ω u j : E → ℝ))) y := by
  have hρ : IsTest (univ : Set E) (φ.normed volume) :=
    ⟨φ.contDiff_normed, φ.hasCompactSupport_normed, subset_univ _⟩
  have hl : ∀ i, LocallyIntegrable (Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ))) volume :=
    fun i => (memLp_indicator hΩ.measurableSet _).locallyIntegrable (by norm_num)
  have e := ConstCoeffOp.apply_convolution A hρ hl j y
  rw [show (fun i => molli φ (Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ)))) = fun i =>
    Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      φ.normed volume from rfl, e,
    sum_integral_indicator_formalAdj_eq hΩ A u (IsTestField.single j (hρ.comp_sub y)),
    Finset.sum_eq_single j]
  · simp [molli_apply]
  · intro j' _ hj'
    simp [Pi.single_eq_of_ne hj']
  · simp

/-- **The smoother commutes with a row-homogeneous operator on `D(A_min)`** (pointwise form):
`A (a R̃ u)ⱼ = a c^{kⱼ} R̃ (A_min u)ⱼ`, by the chain rule for the dilation (`apply_dil`). -/
theorem apply_smoothExt_of_minimal [DecidableEq κ] (hΩ : IsOpen Ω) {A : ConstCoeffOp E ℝ ι κ}
    {k : κ → ℕ} (hA : A.IsRowHomogeneous k) (u : (A.minimal Ω).domain) (a : ℝ) (j : κ) (x : E) :
    A.apply (fun i => a • smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ))) j x =
      a * p.factor ^ k j * smoothExt Ω p ((A.minimal Ω u j : E → ℝ)) x := by
  have hl : ∀ i, LocallyIntegrable (Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ))) volume :=
    fun i => (memLp_indicator hΩ.measurableSet _).locallyIntegrable (by norm_num)
  have hsm : ∀ i, ContDiff ℝ ∞ (smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ))) := fun i =>
    contDiff_smoothExt (hl i)
  rw [show (fun i => a • smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ))) =
    a • (fun i => smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ))) from rfl, A.apply_smul a hsm]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (fun i => smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ))) = fun i =>
    dil p.center p.factor (molli p.bump (Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ)))) from rfl,
    ConstCoeffOp.apply_dil hA p.center p.factor (fun i => contDiff_molli _ (hl i)) j x,
    apply_molli_indicator_of_minimal hΩ A p.bump u j]
  simp only [smoothExt, dil]
  ring

/-- The mollified zero extension of `u ∈ D(A_max)` at a point `y` whose `φ`-ball lies in `Ω`:
`A (ū ⋆ ρ)(y) = ((A_max u)‾ ⋆ ρ)(y)` (only values in `Ω` are sampled). -/
theorem apply_molli_indicator_of_maximal [DecidableEq κ] (hΩ : IsOpen Ω)
    (A : ConstCoeffOp E ℝ ι κ) (φ : ContDiffBump (0 : E)) (u : (A.maximal Ω).domain) (j : κ)
    {y : E} (hy : Metric.closedBall y φ.rOut ⊆ Ω) :
    A.apply (fun i => molli φ (Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ)))) j y =
      molli φ (Ω.indicator ((A.maximal Ω u j : E → ℝ))) y := by
  have hρ : IsTest (univ : Set E) (φ.normed volume) :=
    ⟨φ.contDiff_normed, φ.hasCompactSupport_normed, subset_univ _⟩
  have hl : ∀ i, LocallyIntegrable (Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ))) volume :=
    fun i => (memLp_indicator hΩ.measurableSet _).locallyIntegrable (by norm_num)
  have hker := isTest_comp_sub_of_closedBall_subset hρ φ.tsupport_normed_eq.subset hy
  have hψ := IsTestField.single j hker
  have h := A.maximal_inner_testField hΩ u hψ
  rw [inner_testField, inner_testField] at h
  simp only [conj_trivial, integral_restrict_mul_eq hΩ.measurableSet] at h
  have e := ConstCoeffOp.apply_convolution A hρ hl j y
  rw [show (fun i => molli φ (Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ)))) = fun i =>
    Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      φ.normed volume from rfl, e, ← h, Finset.sum_eq_single j]
  · simp [molli_apply]
  · intro j' _ hj'
    simp [Pi.single_eq_of_ne hj']
  · simp

end Commute

/-! ## The two families of smoothers -/

namespace SmoothingParam

/-- Parameters of the **minimal (zero trace) family** for `Ω` star-shaped with respect to
`B(x₀, s)`: centre `x₀`, `c > 1` and bump radius `< s (c - 1) / 2` (dilation towards the
centre: the smoothed field is a test field on `Ω`). -/
structure IsMinimal (p : SmoothingParam E) (x₀ : E) (s : ℝ) : Prop where
  center_eq : p.center = x₀
  one_lt_factor : 1 < p.factor
  rOut_lt : p.bump.rOut < s * (p.factor - 1) / 2

/-- Parameters of the **maximal (no boundary condition) family**: centre `x₀`, `½ ≤ c < 1` and
bump radius `< s (1 - c) / 4` (expansion about the centre: only values in `Ω` are sampled at
points of `cl Ω`). -/
structure IsMaximal (p : SmoothingParam E) (x₀ : E) (s : ℝ) : Prop where
  center_eq : p.center = x₀
  factor_lt_one : p.factor < 1
  rOut_lt : p.bump.rOut < s * (1 - p.factor) / 4

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- Minimal-family parameters exist with `c` and the bump radius arbitrarily close to `1`, `0`. -/
theorem exists_isMinimal (x₀ : E) {s : ℝ} (hs : 0 < s) {η : ℝ} (hη : 0 < η) :
    ∃ p : SmoothingParam E, p.IsMinimal x₀ s ∧ |p.factor - 1| < η ∧ p.bump.rOut < η := by
  set c := 1 + η / 2
  set r := min (η / 2) (s * (c - 1) / 4)
  have hc1 : 0 < c - 1 := by simp only [c]; linarith
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  refine ⟨⟨x₀, c, by simp only [c]; linarith, ⟨r / 2, r, by positivity, by linarith⟩⟩,
    ⟨rfl, by simp only [c]; linarith, ?_⟩, ?_, ?_⟩
  · change r < _
    exact (min_le_right _ _).trans_lt (by simp only [c]; nlinarith)
  · change |c - 1| < η
    rw [abs_lt]; constructor <;> simp only [c] <;> linarith
  · change r < η
    exact (min_le_left _ _).trans_lt (by linarith)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- Maximal-family parameters exist with `c` and the bump radius arbitrarily close to `1`, `0`. -/
theorem exists_isMaximal (x₀ : E) {s : ℝ} (hs : 0 < s) {η : ℝ} (hη : 0 < η) :
    ∃ p : SmoothingParam E, p.IsMaximal x₀ s ∧ |p.factor - 1| < η ∧ p.bump.rOut < η := by
  set t := min η (1 / 2)
  have ht : 0 < t := lt_min hη (by norm_num)
  have ht2 : t ≤ 1 / 2 := min_le_right _ _
  set c := 1 - t / 2
  set r := min (η / 2) (s * (1 - c) / 8)
  have hc1 : 0 < 1 - c := by simp only [c]; linarith
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  refine ⟨⟨x₀, c, by simp only [c]; linarith, ⟨r / 2, r, by positivity, by linarith⟩⟩,
    ⟨rfl, by simp only [c]; linarith, ?_⟩, ?_, ?_⟩
  · change r < _
    exact (min_le_right _ _).trans_lt (by simp only [c]; nlinarith)
  · change |c - 1| < η
    have : t ≤ η := min_le_left _ _
    rw [abs_lt]; constructor <;> simp only [c] <;> linarith
  · change r < η
    exact (min_le_left _ _).trans_lt (by linarith)

end SmoothingParam

section Families

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {x₀ : E} {s : ℝ}

/-- **Minimal family: the smoothed zero extension is a test function on `Ω`.** -/
theorem isTest_smoothExt (hb : Bornology.IsBounded Ω)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (hp : p.IsMinimal x₀ s)
    {f : E → ℝ} (hf : LocallyIntegrable (Ω.indicator f) volume) : IsTest Ω (smoothExt Ω p f) := by
  have h := isTest_dil_molli_indicator hb hstar hf hp.one_lt_factor p.bump hp.rOut_lt
  rwa [← hp.center_eq] at h

omit [Fintype ι] in
/-- Minimal family: `R_a u` is the test field `a R̃ u`. -/
theorem isTestField_smoothExt (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (hp : p.IsMinimal x₀ s)
    (a : ℝ) (u : L2F ℝ Ω ι) :
    IsTestField Ω fun i => a • smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ)) := fun i =>
  (isTest_smoothExt hb hstar hp
    ((memLp_indicator hΩ.measurableSet (u i)).locallyIntegrable (by norm_num))).smul a

theorem smoothField_eq_testField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (hp : p.IsMinimal x₀ s)
    (a : ℝ) (u : L2F ℝ Ω ι) :
    smoothField p hΩ.measurableSet (fun _ => a) u =
      testField (isTestField_smoothExt hΩ hb hstar hp a u) := rfl

/-- **Minimal family: `R_a` maps `L²(Ω; ℝ^ι)` into `D(A_min)`** (into `C_c^∞(Ω)`). -/
theorem smoothField_mem_minimal_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (hp : p.IsMinimal x₀ s)
    (A : ConstCoeffOp E ℝ ι κ) (a : ℝ) (u : L2F ℝ Ω ι) :
    smoothField p hΩ.measurableSet (fun _ => a) u ∈ (A.minimal Ω).domain := by
  rw [smoothField_eq_testField hΩ hb hstar hp]
  exact A.testField_mem_minimal_domain hΩ _

/-- **Minimal family: `R` commutes with a row-homogeneous `A_min` up to the chain-rule factor**:
`A_min (R_a u) = R_{a c^k} (A_min u)` for `u ∈ D(A_min)` (rows of order `kⱼ`). -/
theorem minimal_smoothField [DecidableEq κ] (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (hp : p.IsMinimal x₀ s)
    {A : ConstCoeffOp E ℝ ι κ} {k : κ → ℕ} (hA : A.IsRowHomogeneous k) (a : ℝ)
    (u : (A.minimal Ω).domain) :
    A.minimal Ω ⟨smoothField p hΩ.measurableSet (fun _ => a) u,
        smoothField_mem_minimal_domain hΩ hb hstar hp A a u⟩ =
      smoothField p hΩ.measurableSet (fun j => a * p.factor ^ k j) (A.minimal Ω u) := by
  have hΦ := isTestField_smoothExt hΩ hb hstar hp a (u : L2F ℝ Ω ι)
  have e : (⟨smoothField p hΩ.measurableSet (fun _ => a) u,
      smoothField_mem_minimal_domain hΩ hb hstar hp A a u⟩ : (A.minimal Ω).domain) =
      ⟨testField hΦ, A.testField_mem_minimal_domain hΩ hΦ⟩ := rfl
  rw [e, A.minimal_testField hΩ hΦ]
  refine (WithLp.ext_iff 2).2 (funext fun j => ?_)
  change toL2 (A.isTestField_apply hΦ j) = (a * p.factor ^ k j) • smoothL2 p hΩ.measurableSet _
  rw [smoothL2_apply, ← MemLp.toLp_const_smul]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  exact apply_smoothExt_of_minimal hΩ hA u a j x

/-- Maximal family, pointwise: at every point of `cl Ω`,
`A (a R̃ u)ⱼ = a c^{kⱼ} R̃ (A_max u)ⱼ` for `u ∈ D(A_max)`. -/
theorem apply_smoothExt_of_maximal [DecidableEq κ] (hΩ : IsOpen Ω)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (hp : p.IsMaximal x₀ s)
    {A : ConstCoeffOp E ℝ ι κ} {k : κ → ℕ} (hA : A.IsRowHomogeneous k)
    (u : (A.maximal Ω).domain) (a : ℝ) (j : κ) {x : E} (hx : x ∈ closure Ω) :
    A.apply (fun i => a • smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ))) j x =
      a * p.factor ^ k j * smoothExt Ω p ((A.maximal Ω u j : E → ℝ)) x := by
  have hl : ∀ i, LocallyIntegrable (Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ))) volume :=
    fun i => (memLp_indicator hΩ.measurableSet _).locallyIntegrable (by norm_num)
  have hsm : ∀ i, ContDiff ℝ ∞ (smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ))) := fun i =>
    contDiff_smoothExt (hl i)
  have hball : Metric.closedBall (p.center + p.factor • (x - p.center)) p.bump.rOut ⊆ Ω := by
    have h := closedBall_dil_subset_of_starBall hstar p.half_le_factor hp.factor_lt_one
      hp.rOut_lt hx
    rwa [← hp.center_eq] at h
  rw [show (fun i => a • smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ))) =
    a • (fun i => smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ))) from rfl, A.apply_smul a hsm]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (fun i => smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ))) = fun i =>
    dil p.center p.factor (molli p.bump (Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ)))) from rfl,
    ConstCoeffOp.apply_dil hA p.center p.factor (fun i => contDiff_molli _ (hl i)) j x,
    apply_molli_indicator_of_maximal hΩ A p.bump u j hball]
  simp only [smoothExt, dil]
  ring

theorem memLp_apply_smoothExt_of_maximal [DecidableEq κ] (hΩ : IsOpen Ω)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (hp : p.IsMaximal x₀ s)
    {A : ConstCoeffOp E ℝ ι κ} {k : κ → ℕ} (hA : A.IsRowHomogeneous k)
    (u : (A.maximal Ω).domain) (a : ℝ) (j : κ) :
    MemLp (A.apply (fun i => a • smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ))) j) 2
      (volume.restrict Ω) := by
  refine ((memLp_smoothExt_restrict (p := p) hΩ.measurableSet (A.maximal Ω u j)).const_smul
    (a * p.factor ^ k j)).ae_eq ?_
  refine ae_restrict_of_forall_mem hΩ.measurableSet fun x hx => ?_
  rw [apply_smoothExt_of_maximal hΩ hstar hp hA u a j (subset_closure hx)]
  simp only [Pi.smul_apply, smul_eq_mul]

/-- **Maximal family: `R_a` maps `D(A_max)` into `D(A_max)`** for a row-homogeneous `A`. -/
theorem smoothField_mem_maximal_domain [DecidableEq κ] (hΩ : IsOpen Ω)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (hp : p.IsMaximal x₀ s)
    {A : ConstCoeffOp E ℝ ι κ} {k : κ → ℕ} (hA : A.IsRowHomogeneous k) (a : ℝ)
    (u : (A.maximal Ω).domain) :
    smoothField p hΩ.measurableSet (fun _ => a) u ∈ (A.maximal Ω).domain := by
  have hl : ∀ i, LocallyIntegrable (Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ))) volume :=
    fun i => (memLp_indicator hΩ.measurableSet _).locallyIntegrable (by norm_num)
  obtain ⟨h, -⟩ := A.smooth_mem_maximal_domain hΩ A.isOrderLE_order
    (ψ := fun i => a • smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ)))
    (fun i => ((contDiff_smoothExt (hl i)).const_smul a).of_le (by exact_mod_cast le_top))
    (fun i => (memLp_smoothExt_restrict hΩ.measurableSet ((u : L2F ℝ Ω ι) i)).const_smul a)
    (memLp_apply_smoothExt_of_maximal hΩ hstar hp hA u a)
  exact h

/-- **Maximal family: `R` commutes with a row-homogeneous `A_max` up to the chain-rule factor**:
`A_max (R_a u) = R_{a c^k} (A_max u)` for `u ∈ D(A_max)`. -/
theorem maximal_smoothField [DecidableEq κ] (hΩ : IsOpen Ω)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (hp : p.IsMaximal x₀ s)
    {A : ConstCoeffOp E ℝ ι κ} {k : κ → ℕ} (hA : A.IsRowHomogeneous k) (a : ℝ)
    (u : (A.maximal Ω).domain) :
    A.maximal Ω ⟨smoothField p hΩ.measurableSet (fun _ => a) u,
        smoothField_mem_maximal_domain hΩ hstar hp hA a u⟩ =
      smoothField p hΩ.measurableSet (fun j => a * p.factor ^ k j) (A.maximal Ω u) := by
  have hl : ∀ i, LocallyIntegrable (Ω.indicator (((u : L2F ℝ Ω ι) i : E → ℝ))) volume :=
    fun i => (memLp_indicator hΩ.measurableSet _).locallyIntegrable (by norm_num)
  obtain ⟨h, hv⟩ := A.smooth_mem_maximal_domain hΩ A.isOrderLE_order
    (ψ := fun i => a • smoothExt Ω p (((u : L2F ℝ Ω ι) i : E → ℝ)))
    (fun i => ((contDiff_smoothExt (hl i)).const_smul a).of_le (by exact_mod_cast le_top))
    (fun i => (memLp_smoothExt_restrict hΩ.measurableSet ((u : L2F ℝ Ω ι) i)).const_smul a)
    (memLp_apply_smoothExt_of_maximal hΩ hstar hp hA u a)
  refine hv.trans ((WithLp.ext_iff 2).2 (funext fun j => ?_))
  show (memLp_apply_smoothExt_of_maximal hΩ hstar hp hA u a j).toLp _ =
    (a * p.factor ^ k j) • smoothL2 p hΩ.measurableSet _
  rw [smoothL2_apply, ← MemLp.toLp_const_smul]
  refine MemLp.toLp_congr _ _ (ae_restrict_of_forall_mem hΩ.measurableSet fun x hx => ?_)
  rw [apply_smoothExt_of_maximal hΩ hstar hp hA u a j (subset_closure hx)]
  simp only [Pi.smul_apply, smul_eq_mul]

end Families

/-! ## The de Rham complex: pullback by the dilation commutes with `d` -/

section DeRham

variable {n : ℕ} {Ω : Set (Fin n → ℝ)} {x₀ : Fin n → ℝ} {s : ℝ}
  (p : SmoothingParam (Fin n → ℝ))

/-- The exterior derivative is homogeneous of order one. -/
theorem extDerivOp_isRowHomogeneous (k : ℤ) :
    (extDerivOp ℝ n k).IsRowHomogeneous fun _ => 1 := by
  intro t r term hterm
  simp only [extDerivOp, List.mem_map] at hterm
  obtain ⟨j, -, rfl⟩ := hterm
  rfl

theorem factor_zpow_mul_factor (k : ℤ) :
    (fun _ : formIdx n (k + 1) => p.factor ^ k * p.factor ^ 1) = fun _ => p.factor ^ (k + 1) := by
  funext _
  rw [pow_one, zpow_add_one₀ p.factor_pos.ne']

/-- **The pullback of `k`-forms by the dilation commutes exactly with `d_min`**: with the
weights `cᵏ` on `k`-forms (`ω ↦ cᵏ (ω ∘ dil)` is the pullback of `ω` by `x ↦ x₀ + c (x - x₀)`),
`d_min (cᵏ R ω) = c^{k+1} R (d_min ω)` on `H̊Λᵏ(Ω)` ([AFW2010], §5.4). -/
theorem deRham_minimal_smoothField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (hp : p.IsMinimal x₀ s)
    (k : ℤ) (u : ((extDerivOp ℝ n k).minimal Ω).domain) :
    (extDerivOp ℝ n k).minimal Ω ⟨smoothField p hΩ.measurableSet (fun _ => p.factor ^ k) u,
        smoothField_mem_minimal_domain hΩ hb hstar hp _ _ _⟩ =
      smoothField p hΩ.measurableSet (fun _ => p.factor ^ (k + 1))
        ((extDerivOp ℝ n k).minimal Ω u) := by
  rw [minimal_smoothField hΩ hb hstar hp (extDerivOp_isRowHomogeneous k), factor_zpow_mul_factor]

/-- **The pullback of `k`-forms by the dilation commutes exactly with `d_max`** (maximal
family, `c < 1`): `d_max (cᵏ R ω) = c^{k+1} R (d_max ω)` on `HΛᵏ(Ω)`. -/
theorem deRham_maximal_smoothField (hΩ : IsOpen Ω)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (hp : p.IsMaximal x₀ s)
    (k : ℤ) (u : ((extDerivOp ℝ n k).maximal Ω).domain) :
    (extDerivOp ℝ n k).maximal Ω ⟨smoothField p hΩ.measurableSet (fun _ => p.factor ^ k) u,
        smoothField_mem_maximal_domain hΩ hstar hp (extDerivOp_isRowHomogeneous k) _ u⟩ =
      smoothField p hΩ.measurableSet (fun _ => p.factor ^ (k + 1))
        ((extDerivOp ℝ n k).maximal Ω u) := by
  rw [maximal_smoothField hΩ hstar hp (extDerivOp_isRowHomogeneous k), factor_zpow_mul_factor]

end DeRham

end Feec.Domain
