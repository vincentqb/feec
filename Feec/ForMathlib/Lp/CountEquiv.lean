module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# `ℓᵖ` as `Lᵖ` of the counting measure

On a countable type `α` with measurable singletons, `ℓᵖ(α; E)` and `Lᵖ(α, count; E)` are the same
space: `lp.equivLpCount` is a linear isometric equivalence, the identity on functions.
-/

open scoped ENNReal NNReal
open MeasureTheory Measure

@[expose] public noncomputable section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
variable {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}

theorem eLpNorm_count_eq_tsum (hp0 : p ≠ 0) (hpt : p ≠ ∞) (f : α → E) :
    eLpNorm f p count = (∑' a, ‖f a‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt AEStronglyMeasurable.of_discrete,
    lintegral_count]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] in
theorem tsum_enorm_rpow_eq (hp : 0 < p.toReal) (f : α → E) :
    ∑' a, ‖f a‖ₑ ^ p.toReal = ∑' a, ((‖f a‖₊ ^ p.toReal : ℝ≥0) : ℝ≥0∞) := by
  congr 1; funext a
  rw [ENNReal.coe_rpow_of_nonneg _ hp.le, enorm_eq_nnnorm]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] in
theorem summable_nnnorm_rpow_iff {r : ℝ} (f : α → E) :
    Summable (fun a => ‖f a‖₊ ^ r) ↔ Summable fun a => ‖f a‖ ^ r := by
  rw [← NNReal.summable_coe]
  simp only [NNReal.coe_rpow, coe_nnnorm]

theorem memLp_count_iff (hp0 : p ≠ 0) {f : α → E} : MemLp f p count ↔ Memℓp f p := by
  rw [memLp_iff]
  rcases eq_or_ne p ∞ with rfl | hpt
  · rw [memℓp_infty_iff, eLpNorm_exponent_top, eLpNormEssSup_count]
    simp only [enorm_eq_nnnorm]
    rw [ENNReal.iSup_coe_lt_top]
    constructor
    · rintro ⟨C, hC⟩
      exact ⟨C, by rintro _ ⟨a, rfl⟩; exact_mod_cast hC ⟨a, rfl⟩⟩
    · rintro ⟨C, hC⟩
      refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
      rintro _ ⟨a, rfl⟩
      change ‖f a‖ ≤ max C 0
      exact (hC ⟨a, rfl⟩).trans (le_max_left _ _)
    · exact AEStronglyMeasurable.of_discrete
  · have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
    rw [memℓp_gen_iff hp, ← summable_nnnorm_rpow_iff, ← ENNReal.tsum_coe_ne_top_iff_summable,
      ← tsum_enorm_rpow_eq hp, eLpNorm_count_eq_tsum hp0 hpt,
      ENNReal.rpow_lt_top_iff_of_pos (by positivity), lt_top_iff_ne_top]

omit [MeasurableSingletonClass α] [Countable α] in
theorem Lp.ext_count {f g : Lp E p (count : Measure α)} (h : ∀ a, f a = g a) : f = g :=
  Lp.ext (ae_count_iff.2 h)

omit [MeasurableSingletonClass α] [Countable α] in
theorem Lp.coeFn_eq_count_iff {f : Lp E p (count : Measure α)} {g : α → E} :
    (f : α → E) =ᵐ[count] g ↔ ⇑f = g := by
  rw [Filter.EventuallyEq, ae_count_iff, funext_iff]

omit [MeasurableSingletonClass α] [Countable α] in
theorem MemLp.coeFn_toLp_count {f : α → E} (hf : MemLp f p count) : ⇑(hf.toLp f) = f :=
  Lp.coeFn_eq_count_iff.1 hf.coeFn_toLp

theorem Lp.norm_count_eq [Fact (1 ≤ p)] (f : lp (fun _ : α => E) p) (hf : MemLp (⇑f) p count) :
    ‖hf.toLp f‖ = ‖f‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  rw [Lp.norm_toLp]
  rcases eq_or_ne p ∞ with rfl | hpt
  · rw [eLpNorm_exponent_top, eLpNormEssSup_count, lp.norm_eq_ciSup]
    simp only [enorm_eq_nnnorm]
    have hb : BddAbove (Set.range fun a => ‖f a‖₊) := by
      obtain ⟨C, hC⟩ := memℓp_infty_iff.1 (lp.memℓp f)
      refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
      rintro _ ⟨a, rfl⟩
      change ‖f a‖ ≤ max C 0
      exact (hC ⟨a, rfl⟩).trans (le_max_left _ _)
    rw [← ENNReal.coe_iSup hb, ENNReal.coe_toReal, NNReal.coe_iSup]
    · rfl
    · exact AEStronglyMeasurable.of_discrete
  · have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
    rw [eLpNorm_count_eq_tsum hp0 hpt, tsum_enorm_rpow_eq hp, lp.norm_eq_tsum_rpow hp,
      ← ENNReal.coe_tsum ((summable_nnnorm_rpow_iff _).2 ((memℓp_gen_iff hp).1 (lp.memℓp f))),
      ← ENNReal.coe_rpow_of_nonneg _ (by positivity), ENNReal.coe_toReal, NNReal.coe_rpow,
      NNReal.coe_tsum]
    simp only [NNReal.coe_rpow, coe_nnnorm]

end MeasureTheory

namespace lp

open MeasureTheory

variable (𝕜 : Type*) [NormedField 𝕜]
variable (α : Type*) [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem memLp_count (f : lp (fun _ : α => E) p) : MemLp (⇑f) p (count : Measure α) :=
  (memLp_count_iff (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne').2 (lp.memℓp f)

theorem memℓp_count (g : Lp E p (count : Measure α)) : Memℓp (⇑g) p :=
  (memLp_count_iff (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne').1 (Lp.memLp g)

/-- The linear isometric equivalence `ℓᵖ(α; E) ≃ₗᵢ Lᵖ(α, count; E)`, the identity on functions. -/
def equivLpCount : lp (fun _ : α => E) p ≃ₗᵢ[𝕜] Lp E p (count : Measure α) where
  toFun f := (memLp_count α E p f).toLp f
  invFun g := ⟨⇑g, memℓp_count α E p g⟩
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add ((memLp_count α E p f).toLp f) ((memLp_count α E p g).toLp g)]
      with a h
    rw [h, Pi.add_apply, (memLp_count α E p _).coeFn_toLp_count,
      (memLp_count α E p _).coeFn_toLp_count, (memLp_count α E p _).coeFn_toLp_count]
    rfl
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_smul c ((memLp_count α E p f).toLp f)] with a h
    rw [RingHom.id_apply, h, Pi.smul_apply, (memLp_count α E p _).coeFn_toLp_count,
      (memLp_count α E p _).coeFn_toLp_count, lp.coeFn_smul, Pi.smul_apply]
  left_inv f := by
    ext a
    change ((memLp_count α E p f).toLp f : α → E) a = f a
    rw [(memLp_count α E p _).coeFn_toLp_count]
  right_inv g := by
    refine Lp.ext_count fun a => ?_
    rw [(memLp_count α E p _).coeFn_toLp_count]
  norm_map' f := Lp.norm_count_eq f (memLp_count α E p f)

variable {𝕜 α E p}

@[simp] theorem coeFn_equivLpCount (f : lp (fun _ : α => E) p) :
    ⇑(equivLpCount 𝕜 α E p f) = ⇑f :=
  (memLp_count α E p f).coeFn_toLp_count

@[simp] theorem equivLpCount_symm_apply (g : Lp E p (count : Measure α)) (a : α) :
    (equivLpCount 𝕜 α E p).symm g a = g a := rfl

end lp
