module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Carlson's inequality on the line

**Carlson's inequality** bounds the `L¹` norm of a function on `ℝ` by the `L²` norms of `g` and
`t g`: if `g` and `t ↦ t • g t` are square integrable, then `g` is integrable and

  `(∫ ‖g‖)⁴ ≤ 4π² (∫ ‖g‖²) (∫ ‖t g‖²)`.

The proof is one pointwise inequality, `‖g‖ ≤ (λ/2)(1 + t²/T²)‖g‖² + 1/(2λ (1 + t²/T²))`
(AM–GM), integrated (`∫ (1 + t²/T²)⁻¹ = π T`) and optimized in `λ` and `T`
(`sq_le_four_mul_of_forall_le`). Through Plancherel's theorem it bounds the total variation of a
measure by the `L²` norms of its Fourier transform and of the derivative of the Fourier
transform; this is the estimate behind Brenner–Thomée's stability bound `‖r(τA)ⁿ‖ ≤ C √n`
(`Feec.HalfLineAlgebra.integral_norm_pow_snd_pow_four_le`).

## Main results

* `sq_le_four_mul_of_forall_le`: `c ≤ α s + β / s` for all `s > 0` gives `c² ≤ 4 α β`;
* **`MeasureTheory.MemLp.integral_norm_pow_four_le`** (Carlson): the inequality above;
  `MeasureTheory.MemLp.integrable_of_mul` (integrability).

## References

* [L. Larsson, L. Maligranda, J. Pečarić, L.-E. Persson, *Multiplicative Inequalities of Carlson Type and Interpolation*][LarssonMaligrandaPecaricPersson2006],
  Ch. 1 (Carlson's inequality)
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Real

@[expose] public noncomputable section

/-- **Optimizing `α s + β / s`**: if `0 ≤ c ≤ α s + β / s` for all `s > 0`, with `α, β ≥ 0`, then
`c² ≤ 4 α β`. -/
theorem sq_le_four_mul_of_forall_le {c α β : ℝ} (hc : 0 ≤ c) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h : ∀ s > 0, c ≤ α * s + β / s) : c ^ 2 ≤ 4 * α * β := by
  rcases hc.eq_or_lt with rfl | hc
  · nlinarith [mul_nonneg hα hβ]
  rcases hα.eq_or_lt with rfl | hα
  · have := h (2 * β / c + 1) (by positivity)
    rw [zero_mul, zero_add, le_div_iff₀ (by positivity),
      show c * (2 * β / c + 1) = 2 * β + c by field_simp] at this
    linarith
  have := h (c / (2 * α)) (by positivity)
  rw [show α * (c / (2 * α)) = c / 2 by field_simp, div_div_eq_mul_div] at this
  have h2 : c / 2 ≤ β * (2 * α) / c := by linarith
  rw [le_div_iff₀ hc] at h2
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace MeasureTheory.MemLp

/-- The pointwise inequality behind Carlson's: `‖v‖ ≤ (λ/2)(‖v‖² + ‖t v‖²/T²) + 1/(2λ(1 + (t/T)²))`. -/
theorem norm_le_carlson {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T) (t : ℝ) (v : E) :
    ‖v‖ ≤ lam / 2 * (‖v‖ ^ 2 + ‖t • v‖ ^ 2 / T ^ 2) + 1 / (2 * lam) * (1 + (t / T) ^ 2)⁻¹ := by
  set w := 1 + (t / T) ^ 2
  have hw : 0 < w := by positivity
  have hv : ‖v‖ ^ 2 + ‖t • v‖ ^ 2 / T ^ 2 = w * ‖v‖ ^ 2 := by
    simp only [w]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; field_simp
  rw [hv]
  have key : 0 ≤ (lam * w * ‖v‖ - 1) ^ 2 / (2 * lam * w) := by positivity
  have : lam / 2 * (w * ‖v‖ ^ 2) + 1 / (2 * lam) * w⁻¹ - ‖v‖ =
      (lam * w * ‖v‖ - 1) ^ 2 / (2 * lam * w) := by
    field_simp; ring
  linarith

/-- `∫ (1 + (t/T)²)⁻¹ = π T`. -/
theorem integral_inv_one_add_div_sq {T : ℝ} (hT : 0 < T) :
    ∫ t : ℝ, (1 + (t / T) ^ 2)⁻¹ = π * T := by
  rw [Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) T, integral_univ_inv_one_add_sq,
    abs_of_pos hT, smul_eq_mul, mul_comm]

variable {g : ℝ → E}

/-- A function with `g` and `t g` square integrable is integrable. -/
theorem integrable_of_mul (hg : MemLp g 2) (hg' : MemLp (fun t : ℝ => t • g t) 2) :
    Integrable g := by
  have h1 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have h2 := (memLp_two_iff_integrable_sq_norm hg'.aestronglyMeasurable).1 hg'
  have h3 : Integrable fun t : ℝ => (1 + (t / 1) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_div one_ne_zero
  refine Integrable.mono' (((h1.add (h2.div_const (1 ^ 2))).const_mul (1 / 2)).add
    (h3.const_mul (1 / (2 * 1)))) hg.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  exact norm_le_carlson one_pos one_pos t (g t)

/-- **Carlson's inequality** on `ℝ`: `(∫ ‖g‖)⁴ ≤ 4π² (∫ ‖g‖²) (∫ ‖t g‖²)`.
[LarssonMaligrandaPecaricPersson2006], Ch. 1 -/
theorem integral_norm_pow_four_le (hg : MemLp g 2) (hg' : MemLp (fun t : ℝ => t • g t) 2) :
    (∫ t, ‖g t‖) ^ 4 ≤ 4 * π ^ 2 * (∫ t, ‖g t‖ ^ 2) * ∫ t, ‖t • g t‖ ^ 2 := by
  set I := ∫ t, ‖g t‖
  set a := ∫ t, ‖g t‖ ^ 2
  set b := ∫ t, ‖t • g t‖ ^ 2
  have h1 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have h2 := (memLp_two_iff_integrable_sq_norm hg'.aestronglyMeasurable).1 hg'
  have ha : 0 ≤ a := integral_nonneg fun _ => by positivity
  have hb : 0 ≤ b := integral_nonneg fun _ => by positivity
  have hI : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  -- for each `T`, `I² ≤ π (T a + b / T)`
  have hT : ∀ T > 0, I ^ 2 / π ≤ a * T + b / T := by
    intro T hT
    have h3 : Integrable fun t : ℝ => (1 + (t / T) ^ 2)⁻¹ :=
      integrable_inv_one_add_sq.comp_div hT.ne'
    have hlam : ∀ lam > 0, I ≤ (a + b / T ^ 2) / 2 * lam + π * T / 2 / lam := by
      intro lam hlam
      have h12 : Integrable fun t : ℝ => ‖g t‖ ^ 2 + ‖t • g t‖ ^ 2 / T ^ 2 :=
        h1.add (h2.div_const _)
      have hi : Integrable fun t : ℝ => lam / 2 * (‖g t‖ ^ 2 + ‖t • g t‖ ^ 2 / T ^ 2) +
          1 / (2 * lam) * (1 + (t / T) ^ 2)⁻¹ :=
        (h12.const_mul _).add (h3.const_mul _)
      have hval : ∫ t : ℝ, (lam / 2 * (‖g t‖ ^ 2 + ‖t • g t‖ ^ 2 / T ^ 2) +
          1 / (2 * lam) * (1 + (t / T) ^ 2)⁻¹) = lam / 2 * (a + b / T ^ 2) +
          1 / (2 * lam) * (π * T) := by
        rw [integral_add (h12.const_mul _) (h3.const_mul _),
          integral_const_mul, integral_const_mul, integral_add h1 (h2.div_const _), integral_div,
          integral_inv_one_add_div_sq hT]
      have := integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg (g t)) hi
        (Filter.Eventually.of_forall fun t => norm_le_carlson hlam hT t (g t))
      rw [hval] at this
      calc I ≤ _ := this
        _ = _ := by field_simp
    have := sq_le_four_mul_of_forall_le hI (by positivity) (by positivity) hlam
    rw [div_le_iff₀ pi_pos]
    have hT2 : 4 * ((a + b / T ^ 2) / 2) * (π * T / 2) = (a * T + b / T) * π := by
      field_simp; ring
    linarith
  have := sq_le_four_mul_of_forall_le (by positivity) ha hb hT
  rw [div_pow, div_le_iff₀ (by positivity)] at this
  calc I ^ 4 = (I ^ 2) ^ 2 := by ring
    _ ≤ _ := by nlinarith [pi_pos]

end MeasureTheory.MemLp
