module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Pi
public import Feec.Ch4.Box

/-!
# A nonzero element of `K*` on the box: the constant field `diag(1, -1, 0)`

`Feec.Box.mem_Kmax_boxTSD_iff` identifies the largest invariant subspace `K*` of
`K = {0} × L²(TSD) × L²(TSD)` on the box `Q = (0, ½)³` with the thesis' boundary conditions: it
consists of the stationary data `(0, 0, B₀)`, `B₀ ∈ L²(TSD)` curl-free. This file shows that
`K*` is not zero, by exhibiting the constant field `B₀ = diag(1, -1, 0)` on `Q` in the parity
model: its magnetic-slot extension (`B_{aa}` odd in `x_a`, even in the other variables) has
entries `sq(x₀)`, `-sq(x₁)`, `0`, with `sq` the square wave `sign(sin 2πx)` (`sqWave`).

## Main results

* `mFourierCoeff_axisSq`: the Fourier coefficients of `x ↦ sq(x_a)` on `𝕋³` are
  `ŝq(k_a)` on the axis `k_c = 0` (`c ≠ a`) and `0` off it (Fubini over the product measure);
  `fourierCoeff_sqWave_neg`: `ŝq` is odd (`sq` is odd and Haar measure on `ℝ/ℤ` is
  negation-invariant).
* `staticB_mem_boxTSD`: `staticB ∈ boxTSD (-1)` (parities, symmetric, trace-free and
  divergence-free on `Q`), `curlSym_staticB`: it is curl-free, `staticB_ne_zero`.
* **`staticB_mem_Kmax`**: `(0, 0, staticB) ∈ K*`, so `K* ≠ 0`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace InnerProductSpace ENNReal ComplexConjugate
open MeasureTheory Set Filter Topology Complex

namespace Feec.Box

open Feec.Torus Feec.TorusWeak Feec.Constraints UnitAddTorus

attribute [local instance] Feec.Torus.instMeasureSpaceUnitAddCircle_feec

/-- The local Haar measure on `ℝ/ℤ` is an additive Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The local Haar measure on `ℝ/ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The square wave -/

/-- The square wave `sq(x) = sign(sin 2πx)` on `ℝ/ℤ`: `1` on `(0, ½)`, `-1` on `(½, 1)`. -/
def sqWave (x : UnitAddCircle) : ℂ :=
  if 0 < (fourier 1 x).im then 1 else if (fourier 1 x).im < 0 then -1 else 0

theorem measurable_sqWave : Measurable sqWave := by
  have hc : Measurable fun x : UnitAddCircle => (fourier 1 x).im :=
    Complex.measurable_im.comp (fourier 1).continuous.measurable
  refine Measurable.ite (measurableSet_lt measurable_const hc) measurable_const
    (Measurable.ite (measurableSet_lt hc measurable_const) measurable_const measurable_const)

theorem norm_sqWave_le (x : UnitAddCircle) : ‖sqWave x‖ ≤ 1 := by
  unfold sqWave; split_ifs <;> simp

/-- `sq` is odd. -/
theorem sqWave_neg (x : UnitAddCircle) : sqWave (-x) = -sqWave x := by
  have h : (fourier 1 (-x)).im = -(fourier 1 x).im := by
    rw [fourier_apply, smul_neg, fourier_neg', conj_im]
  unfold sqWave
  rw [h]
  split_ifs <;> first | (exfalso; linarith) | norm_num

/-- `sq = 1` on `(0, ½)`. -/
theorem sqWave_coe {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) : sqWave (t : UnitAddCircle) = 1 := by
  have h : (fourier 1 (t : UnitAddCircle)).im = Real.sin (2 * Real.pi * t) := by
    rw [fourier_coe_apply]
    have : 2 * (Real.pi : ℂ) * I * ((1 : ℤ) : ℂ) * (t : ℂ) / ((1 : ℝ) : ℂ) =
        ((2 * Real.pi * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_ofReal_mul_I_im]
  have hs : 0 < Real.sin (2 * Real.pi * t) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, ht.1])
      (by nlinarith [Real.pi_pos, ht.2])
  unfold sqWave
  rw [h]
  simp only [hs, ↓reduceIte]

/-- `∫ e_m = δ_{m0}` on `ℝ/ℤ`. -/
theorem integral_fourier (m : ℤ) :
    ∫ y : UnitAddCircle, fourier m y = if m = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.1 (orthonormal_fourier (T := 1))) 0 m
  rw [ContinuousMap.inner_toLp] at h
  simp only [fourier_zero, map_one, mul_one] at h
  rw [show (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle from rfl, h]
  simp [eq_comm]

theorem fourier_neg_arg (m : ℤ) (t : UnitAddCircle) : fourier m (-t) = fourier (-m) t := by
  rw [fourier_apply, fourier_apply, smul_neg, neg_smul]

/-- **`ŝq` is odd**: `ŝq(-n) = -ŝq(n)`. -/
theorem fourierCoeff_sqWave_neg (n : ℤ) : fourierCoeff sqWave (-n) = -fourierCoeff sqWave n := by
  set g : UnitAddCircle → ℂ := fun t => fourier (-n) t • sqWave t
  have key : (fun t => fourier (-(-n)) t • sqWave t) = fun t => -g (-t) := by
    funext t
    simp only [g, sqWave_neg, smul_neg, neg_neg, fourier_neg_arg]
  unfold fourierCoeff
  rw [key, integral_neg, integral_neg_eq_self g AddCircle.haarAddCircle]

/-! ## The square wave on one coordinate of `𝕋³` -/

/-- `x ↦ sq(x_a)` on `𝕋³`. -/
def axisSq (a : Fin 3) (x : T3) : ℂ := sqWave (x a)

theorem memLp_axisSq (a : Fin 3) : MemLp (axisSq a) 2 volume :=
  MemLp.of_bound ((measurable_sqWave.comp (measurable_pi_apply a)).aestronglyMeasurable) 1
    (ae_of_all _ fun _ => norm_sqWave_le _)

/-- The `L²` class of `x ↦ sq(x_a)`. -/
def axisSqL (a : Fin 3) : L2T := (memLp_axisSq a).toLp _

theorem axisSqL_ae (a : Fin 3) : (axisSqL a : T3 → ℂ) =ᵐ[volume] axisSq a :=
  (memLp_axisSq a).coeFn_toLp

/-- **Fourier coefficients of `sq(x_a)`**: `ŝq(k_a)` if `k_c = 0` for `c ≠ a`, else `0`. -/
theorem mFourierCoeff_axisSq (a : Fin 3) (k : Z3) :
    mFourierCoeff (axisSq a) k = if ∀ c, c ≠ a → k c = 0 then fourierCoeff sqWave (k a) else 0 := by
  have e : (fun x : T3 => mFourier (-k) x • axisSq a x) =
      fun x => ∏ i, (fourier (-k i) (x i) * if i = a then sqWave (x i) else 1) := by
    funext x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ a]
    simp [mFourier, axisSq, smul_eq_mul]
  rw [mFourierCoeff, e, integral_fintype_prod_volume_eq_prod
    (fun i y => fourier (-k i) y * if i = a then sqWave y else 1)]
  have hother : ∀ i, i ≠ a →
      ∫ y : UnitAddCircle, (fourier (-k i) y * if i = a then sqWave y else 1) =
      if k i = 0 then 1 else 0 := by
    intro i hi
    simp only [hi, ↓reduceIte, mul_one]
    rw [integral_fourier]
    simp
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
  have ha : ∫ y : UnitAddCircle, (fourier (-k a) y * if a = a then sqWave y else 1) =
      fourierCoeff sqWave (k a) := by
    simp only [↓reduceIte]
    rfl
  rw [ha, Finset.prod_congr rfl fun i hi => hother i (Finset.ne_of_mem_erase hi)]
  split_ifs with h
  · rw [Finset.prod_eq_one fun i hi => by simp [h i (Finset.ne_of_mem_erase hi)], mul_one]
  · push Not at h
    obtain ⟨c, hc, hk⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hc, Finset.mem_univ c⟩) (by simp [hk]), mul_zero]

theorem mFourierCoeff_axisSqL (a : Fin 3) (k : Z3) :
    mFourierCoeff (axisSqL a : T3 → ℂ) k =
      if ∀ c, c ≠ a → k c = 0 then fourierCoeff sqWave (k a) else 0 := by
  rw [← mFourierCoeff_axisSq]
  exact integral_congr_ae ((axisSqL_ae a).mono fun x hx => by simp [hx])

/-- The Fourier coefficients of `sq(x_a)`. -/
def axisCoef (a : Fin 3) (k : Z3) : ℂ :=
  if ∀ c, c ≠ a → k c = 0 then fourierCoeff sqWave (k a) else 0

theorem repr_axisSqL (a : Fin 3) (k : Z3) : mFourierBasis.repr (axisSqL a) k = axisCoef a k := by
  rw [mFourierBasis_repr, mFourierCoeff_axisSqL]; rfl

theorem refl_apply_self (i : Fin 3) (k : Z3) : refl i k i = -k i := by simp [refl]

theorem refl_apply_ne {i c : Fin 3} (h : c ≠ i) (k : Z3) : refl i k c = k c := by
  simp [refl, Function.update_of_ne h]

/-- **Parity of the coefficients**: `sq(x_a)` is odd in `x_a` and even in the other variables. -/
theorem axisCoef_refl (a i : Fin 3) (k : Z3) :
    axisCoef a (refl i k) = (if i = a then -1 else 1) * axisCoef a k := by
  have hcond : (∀ c, c ≠ a → refl i k c = 0) ↔ (∀ c, c ≠ a → k c = 0) := by
    refine forall_congr' fun c => imp_congr_right fun _ => ?_
    by_cases hc : c = i
    · subst hc; rw [refl_apply_self, neg_eq_zero]
    · rw [refl_apply_ne hc]
  unfold axisCoef
  by_cases hia : i = a
  · subst hia
    rw [refl_apply_self, fourierCoeff_sqWave_neg]
    by_cases hC : ∀ c, c ≠ i → k c = 0 <;> simp [hcond, hC]
  · rw [refl_apply_ne (Ne.symm hia)]
    simp only [hcond, hia, ↓reduceIte, one_mul]

/-- `ξ_c ŝq(k_a) = 0` on the support for `c ≠ a`: the coefficients live on the `a`-axis. -/
theorem freq_mul_axisCoef {a c : Fin 3} (h : c ≠ a) (k : Z3) :
    (freq k c : ℂ) * axisCoef a k = 0 := by
  unfold axisCoef
  split_ifs with hk
  · simp [freq, hk c h]
  · rw [mul_zero]

/-! ## The field `diag(1, -1, 0)` -/

/-- The entries (as `L²(𝕋³)` functions) of the magnetic-slot extension of `diag(1, -1, 0)`:
`sq(x₀)`, `-sq(x₁)`, `0`. -/
def staticEntry (p : Fin 3 × Fin 3) : L2T :=
  if p = (0, 0) then axisSqL 0 else if p = (1, 1) then -axisSqL 1 else 0

/-- **The constant field `diag(1, -1, 0)` on `Q`**, extended with the magnetic-slot parities
(`ParRow (-1)`), on the Fourier side. -/
def staticB : L2M := matrixFourier (WithLp.toLp 2 staticEntry)

theorem entry_staticB (p : Fin 3 × Fin 3) :
    entry p staticB = mFourierBasis.repr (staticEntry p) := by
  ext k
  rw [entry_apply, staticB]
  obtain ⟨a, b⟩ := p
  rw [matrixFourier_apply, ← mFourierBasis_repr]

theorem ofCoeff_entry_staticB (p : Fin 3 × Fin 3) : ofCoeff (entry p staticB) = staticEntry p := by
  rw [entry_staticB, ofCoeff, LinearIsometryEquiv.symm_apply_apply]

theorem repr_symm_entry_staticB (p : Fin 3 × Fin 3) :
    mFourierBasis.repr.symm (entry p staticB) = staticEntry p := ofCoeff_entry_staticB p

theorem staticEntry_00 : staticEntry (0, 0) = axisSqL 0 := by simp [staticEntry]

theorem staticEntry_11 : staticEntry (1, 1) = -axisSqL 1 := by simp [staticEntry]

theorem staticEntry_other {p : Fin 3 × Fin 3} (h0 : p ≠ (0, 0)) (h1 : p ≠ (1, 1)) :
    staticEntry p = 0 := by simp [staticEntry, h0, h1]

theorem staticB_apply (k : Z3) (a b : Fin 3) :
    staticB k (a, b) = if (a, b) = (0, 0) then axisCoef 0 k
      else if (a, b) = (1, 1) then -axisCoef 1 k else 0 := by
  rw [← entry_apply, entry_staticB, staticEntry]
  split_ifs
  · exact repr_axisSqL 0 k
  · rw [_root_.map_neg]; simp [repr_axisSqL]
  · simp

/-- `staticB` has the magnetic-slot parities. -/
theorem staticB_mem_ParRow : staticB ∈ ParRow (-1) := by
  intro i k a b
  rw [staticB_apply, staticB_apply]
  fin_cases a <;> fin_cases b <;> fin_cases i <;> simp [axisCoef_refl, colSign]

/-- `partialT c φ` vanishes off the support of `φ`. -/
theorem partialT_eq_zero_of_notMem {φ : T3 → ℂ} {x : T3} (hx : x ∉ tsupport φ) (c : Fin 3) :
    partialT c φ x = 0 := by
  have h0 := notMem_tsupport_iff_eventuallyEq.1 hx
  have hcont : Continuous fun t : ℝ => x + proj (Pi.single c t) :=
    continuous_const.add (isOpenQuotientMap_proj.continuous.comp
      (continuous_single (A := fun _ : Fin 3 => ℝ) c))
  have hx0 : (fun t : ℝ => x + proj (Pi.single c t)) 0 = x := by simp [proj_zero]
  have hev : (fun t : ℝ => φ (x + proj (Pi.single c t))) =ᶠ[𝓝 0] fun _ => 0 := by
    have := hcont.tendsto 0
    rw [Pi.single_zero, proj_zero, add_zero] at this
    exact this.eventually h0
  rw [partialT, hev.deriv_eq]
  simp

/-- `∫ sq(x_a) ∂_a φ = 0` for test functions supported in the box (there `sq(x_a) = 1`). -/
theorem integral_axisSqL_mul_partialT (a : Fin 3) {φ : T3 → ℂ} (hφ : IsSmooth φ)
    (hs : tsupport φ ⊆ boxSet) :
    ∫ x, (axisSqL a : T3 → ℂ) x * partialT a φ x = 0 := by
  rw [← integral_partialT_eq_zero hφ.contDiff_one a]
  refine integral_congr_ae ((axisSqL_ae a).mono fun x hx => ?_)
  dsimp only
  rw [hx]
  by_cases hm : x ∈ tsupport φ
  · obtain ⟨t, ht, e⟩ := (hs hm) a (mem_univ a)
    rw [axisSq, ← e, sqWave_coe ht, one_mul]
  · rw [partialT_eq_zero_of_notMem hm, mul_zero]

theorem staticB_mem_boxSym : staticB ∈ boxSym := by
  rw [mem_boxSym]
  intro a b
  have : staticEntry (a, b) = staticEntry (b, a) := by
    unfold staticEntry
    fin_cases a <;> fin_cases b <;> simp
  rw [entry_staticB, entry_staticB, this, sub_self]
  exact boxZero.zero_mem

theorem staticB_mem_boxTr : staticB ∈ boxTr := by
  rw [mem_boxTr, ZeroOnBox]
  have e : ofCoeff (∑ a : Fin 3, entry (a, a) staticB) = axisSqL 0 + -axisSqL 1 + 0 := by
    rw [ofCoeff, _root_.map_sum, Fin.sum_univ_three, repr_symm_entry_staticB,
      repr_symm_entry_staticB, repr_symm_entry_staticB, staticEntry_00, staticEntry_11,
      staticEntry_other (by decide) (by decide)]
  rw [e]
  have h1 := ae_restrict_of_ae (μ := volume) (s := boxSet) (axisSqL_ae 0)
  have h2 := ae_restrict_of_ae (μ := volume) (s := boxSet) (axisSqL_ae 1)
  have h3 := ae_restrict_of_ae (μ := volume) (s := boxSet)
    (Lp.coeFn_add (axisSqL 0 + -axisSqL 1) (0 : L2T))
  have h4 := ae_restrict_of_ae (μ := volume) (s := boxSet) (Lp.coeFn_add (axisSqL 0) (-axisSqL 1))
  have h5 := ae_restrict_of_ae (μ := volume) (s := boxSet) (Lp.coeFn_neg (axisSqL 1))
  have h6 := ae_restrict_of_ae (μ := volume) (s := boxSet) (Lp.coeFn_zero ℂ 2 (volume : Measure T3))
  filter_upwards [h1, h2, h3, h4, h5, h6, ae_restrict_mem measurableSet_boxSet]
    with x e1 e2 e3 e4 e5 e6 hx
  rw [e3, Pi.add_apply, e4, Pi.add_apply, e5, Pi.neg_apply, e6, e1, e2]
  obtain ⟨t0, ht0, e0⟩ := hx 0 (mem_univ 0)
  obtain ⟨t1, ht1, e1'⟩ := hx 1 (mem_univ 1)
  simp only [axisSq, ← e0, ← e1', sqWave_coe ht0, sqWave_coe ht1, Pi.zero_apply]
  ring

theorem staticB_mem_boxDiv : staticB ∈ boxDiv := by
  rw [mem_boxDiv]
  intro a φ hφ hs
  simp only [ofCoeff_entry_staticB]
  have hz : ∀ b, ∫ x, ((0 : L2T) : T3 → ℂ) x * partialT b φ x = 0 := fun b => by
    rw [integral_congr_ae ((Lp.coeFn_zero ℂ 2 (volume : Measure T3)).mono fun x hx => by
      dsimp only; rw [hx, Pi.zero_apply, zero_mul] :
        (fun x => ((0 : L2T) : T3 → ℂ) x * partialT b φ x) =ᵐ[volume] 0)]
    simp
  have hneg : ∫ x, ((-axisSqL 1 : L2T) : T3 → ℂ) x * partialT 1 φ x = 0 := by
    rw [integral_congr_ae ((Lp.coeFn_neg (axisSqL 1)).mono fun x hx => by
      dsimp only; rw [hx, Pi.neg_apply, neg_mul] :
        (fun x => ((-axisSqL 1 : L2T) : T3 → ℂ) x * partialT 1 φ x)
        =ᵐ[volume] fun x => -((axisSqL 1 : T3 → ℂ) x * partialT 1 φ x)), integral_neg,
      integral_axisSqL_mul_partialT 1 hφ hs, neg_zero]
  rw [Fin.sum_univ_three]
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by fin_cases a <;> simp) with rfl | rfl | rfl
  · rw [staticEntry_00, staticEntry_other (by decide) (by decide),
      staticEntry_other (by decide) (by decide), integral_axisSqL_mul_partialT 0 hφ hs, hz, hz]
    simp
  · rw [staticEntry_11, staticEntry_other (by decide) (by decide),
      staticEntry_other (by decide) (by decide), hneg, hz, hz]
    simp
  · rw [staticEntry_other (by decide) (by decide), staticEntry_other (by decide) (by decide),
      staticEntry_other (by decide) (by decide), hz, hz, hz]
    simp

/-- `staticB` lies in `L²(TSD)` on the box. -/
theorem staticB_mem_boxTSD : staticB ∈ boxTSD (-1) :=
  ⟨⟨⟨staticB_mem_ParRow, staticB_mem_boxSym⟩, staticB_mem_boxTr⟩, staticB_mem_boxDiv⟩

/-- `staticB` is curl-free. -/
theorem curlSym_staticB (k : Z3) : curlSym (freq k) (staticB k) = 0 := by
  have h01 := freq_mul_axisCoef (a := 0) (c := 1) (by decide) k
  have h02 := freq_mul_axisCoef (a := 0) (c := 2) (by decide) k
  have h10 := freq_mul_axisCoef (a := 1) (c := 0) (by decide) k
  have h12 := freq_mul_axisCoef (a := 1) (c := 2) (by decide) k
  ext ⟨a, b⟩
  simp only [curlSym_apply, jM_apply, curlR_apply, cross, staticB_apply]
  fin_cases a <;> fin_cases b <;> simp [h01, h02, h10, h12]

/-- `staticB ≠ 0`: its `(0, 0)` entry is `sq(x₀)`, which is `1` on the box. -/
theorem staticB_ne_zero : staticB ≠ 0 := by
  intro h
  have h1 : axisSqL 0 = 0 := by
    have := ofCoeff_entry_staticB (0, 0)
    rw [h, _root_.map_zero, ofCoeff, _root_.map_zero] at this
    simpa [staticEntry] using this.symm
  have hae : axisSq 0 =ᵐ[volume] 0 := by
    have := axisSqL_ae 0
    rw [h1] at this
    exact this.symm.trans (Lp.coeFn_zero ℂ 2 (volume : Measure T3))
  have hpos : 0 < volume boxSet := by
    refine isOpen_boxSet.measure_pos volume ⟨proj fun _ => 1 / 4, proj_mem_boxSet fun _ => ?_⟩
    constructor <;> norm_num
  have hnull : volume {x | axisSq 0 x ≠ 0} = 0 :=
    ae_iff.1 (hae.mono fun x hx => by simpa using hx)
  refine hpos.ne' (measure_mono_null (fun x hx => ?_) hnull)
  obtain ⟨t, ht, e⟩ := hx 0 (mem_univ 0)
  change axisSq 0 x ≠ 0
  rw [axisSq, ← e, sqWave_coe ht]
  exact one_ne_zero

/-- **`K*` is not zero**: the stationary datum `(0, 0, diag(1, -1, 0))` lies in the largest
invariant subspace of `K = {0} × L²(TSD) × L²(TSD)` on the box with the thesis' boundary
conditions. Together with `Feec.Box.mem_Kmax_boxTSD_iff`: `K*` is nonzero and consists of
stationary data only.

See [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem staticB_mem_Kmax :
    ini L2V (0 : L2M) staticB ∈ Kmax periodicGroup (Kc L2V (boxTSD 1) (boxTSD (-1))) ∧
      ini L2V (0 : L2M) staticB ≠ 0 := by
  refine ⟨(mem_Kmax_boxTSD_iff _).2 ⟨staticB, staticB_mem_boxTSD, curlSym_staticB, rfl⟩,
    fun h => staticB_ne_zero ?_⟩
  have := congrArg (fun x => (HilbertComplex2.tot L2V L2M L2M x).2.2) h
  simpa [tot_ini] using this

end Feec.Box
