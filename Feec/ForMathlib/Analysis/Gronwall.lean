module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A square-root Gronwall inequality

If `Q ≥ 0` is continuous on `[a, b]` and `Q²` has right derivative `q' ≤ F Q` on `[a, b)`, with
`F ≥ 0` the right derivative of a continuous `G`, then `Q t ≤ Q a + (G t − G a) / 2`.

Only `Q²` is assumed differentiable: this is the form needed for `Q = ‖e‖`, which fails to be
differentiable where `e` vanishes. The proof compares `√(Q² + ε²)` with
`√(Q a ² + ε²) + (G − G a)/2` and lets `ε → 0`.

* `le_add_half_sub_of_sq_deriv_le_mul`: the primitive form.
* `le_add_half_integral_of_sq_deriv_le_mul`: the integral form `Q t ≤ Q a + ½ ∫ₐᵗ F`.
* `ContinuousOn.exists_continuous_eqOn_Icc`, `ContinuousOn.intervalIntegral_primitive_Icc`:
  extension of a function continuous on `[a, b]`, and its primitive.
-/

open Set

@[expose] public noncomputable section

/-- **Square-root Gronwall inequality**, primitive form. If `Q ≥ 0` is continuous on `[a,b]`,
`Q²` has right derivative `q'` on `[a,b)`, `G` is continuous on `[a,b]` with right derivative
`F ≥ 0` on `[a,b)`, and `q' ≤ F Q`, then `Q t ≤ Q a + (G t − G a)/2` on `[a,b]`.
Thesis: Lemma 4.12 (corrected). -/
theorem le_add_half_sub_of_sq_deriv_le_mul {Q q' F G : ℝ → ℝ} {a b : ℝ}
    (hQc : ContinuousOn Q (Icc a b)) (hQ0 : ∀ t ∈ Icc a b, 0 ≤ Q t)
    (hq : ∀ t ∈ Ico a b, HasDerivWithinAt (fun s => Q s ^ 2) (q' t) (Ici t) t)
    (hGc : ContinuousOn G (Icc a b))
    (hG : ∀ t ∈ Ico a b, HasDerivWithinAt G (F t) (Ici t) t)
    (hF : ∀ t ∈ Ico a b, 0 ≤ F t)
    (hle : ∀ t ∈ Ico a b, q' t ≤ F t * Q t) :
    ∀ t ∈ Icc a b, Q t ≤ Q a + (G t - G a) / 2 := by
  intro t ht
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set f : ℝ → ℝ := fun s => Real.sqrt (Q s ^ 2 + ε ^ 2)
  have hpos : ∀ s, 0 < Q s ^ 2 + ε ^ 2 := fun s => by positivity
  have hfc : ContinuousOn f (Icc a b) :=
    ((hQc.pow 2).add continuousOn_const).sqrt
  have hf' : ∀ s ∈ Ico a b,
      HasDerivWithinAt f (q' s / (2 * Real.sqrt (Q s ^ 2 + ε ^ 2))) (Ici s) s := by
    intro s hs
    have := ((hq s hs).add_const (ε ^ 2)).sqrt (hpos s).ne'
    simpa using this
  have hB : ContinuousOn (fun s => Real.sqrt (Q a ^ 2 + ε ^ 2) + (G s - G a) / 2) (Icc a b) :=
    continuousOn_const.add ((hGc.sub continuousOn_const).div_const 2)
  have hB' : ∀ s ∈ Ico a b, HasDerivWithinAt
      (fun s => Real.sqrt (Q a ^ 2 + ε ^ 2) + (G s - G a) / 2) (F s / 2) (Ici s) s := by
    intro s hs
    simpa using (((hG s hs).sub_const (G a)).div_const 2).const_add (Real.sqrt (Q a ^ 2 + ε ^ 2))
  have bound : ∀ s ∈ Ico a b, q' s / (2 * Real.sqrt (Q s ^ 2 + ε ^ 2)) ≤ F s / 2 := by
    intro s hs
    have hQs : Q s ≤ Real.sqrt (Q s ^ 2 + ε ^ 2) := by
      calc Q s = Real.sqrt (Q s ^ 2) := (Real.sqrt_sq (hQ0 s (Ico_subset_Icc_self hs))).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
    rw [div_le_iff₀ (by positivity)]
    calc q' s ≤ F s * Q s := hle s hs
      _ ≤ F s * Real.sqrt (Q s ^ 2 + ε ^ 2) := mul_le_mul_of_nonneg_left hQs (hF s hs)
      _ = F s / 2 * (2 * Real.sqrt (Q s ^ 2 + ε ^ 2)) := by ring
  have key := image_le_of_deriv_right_le_deriv_boundary hfc hf' (by simp [f]) hB hB' bound ht
  have hQt : Q t ≤ f t := by
    calc Q t = Real.sqrt (Q t ^ 2) := (Real.sqrt_sq (hQ0 t ht)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  have hQa := hQ0 a ⟨le_rfl, ht.1.trans ht.2⟩
  have hsq0 : Real.sqrt (Q a ^ 2 + ε ^ 2) ≤ Q a + ε := by
    rw [Real.sqrt_le_left]
    · nlinarith
    · positivity
  linarith

/-- A function continuous on `[a,b]` (`a ≤ b`) agrees on `[a,b]` with a continuous function on
`ℝ` (constant outside `[a,b]`). -/
theorem ContinuousOn.exists_continuous_eqOn_Icc {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hFc : ContinuousOn F (Icc a b)) :
    ∃ F₁ : ℝ → ℝ, Continuous F₁ ∧ EqOn F₁ F (Icc a b) := by
  refine ⟨fun s => F (projIcc a b hab s), ?_, fun s hs => by simp [projIcc_of_mem hab hs]⟩
  exact hFc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    fun s => (projIcc a b hab s).2

/-- Primitive of a function continuous on `[a,b]`: `t ↦ ∫ₐᵗ F` is continuous on `[a,b]` with
right derivative `F t` on `[a,b)`. -/
theorem ContinuousOn.intervalIntegral_primitive_Icc {F : ℝ → ℝ} {a b : ℝ}
    (hFc : ContinuousOn F (Icc a b)) :
    ContinuousOn (fun t => ∫ s in a..t, F s) (Icc a b) ∧
      ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => ∫ s in a..t, F s) (F t) (Ici t) t := by
  rcases lt_or_ge b a with hab | hab
  · exact ⟨by simp [Icc_eq_empty (not_le.2 hab)],
      fun t ht => absurd (ht.1.trans_lt ht.2) (lt_asymm hab)⟩
  obtain ⟨F₁, hF₁, hEq⟩ := hFc.exists_continuous_eqOn_Icc hab
  have hI : ∀ t ∈ Icc a b, ∫ s in a..t, F s = ∫ s in a..t, F₁ s := by
    intro t ht
    refine intervalIntegral.integral_congr fun s hs => (hEq ?_).symm
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hd : ∀ t, HasDerivAt (fun t => ∫ s in a..t, F₁ s) (F₁ t) t := fun t =>
    (hF₁.integral_hasStrictDerivAt a t).hasDerivAt
  refine ⟨?_, fun t ht => ?_⟩
  · refine (continuous_iff_continuousAt.2 fun t => (hd t).continuousAt).continuousOn.congr ?_
    exact fun t ht => hI t ht
  · have ht' : t ∈ Icc a b := Ico_subset_Icc_self ht
    rw [← hEq ht']
    refine (hd t).hasDerivWithinAt.congr_of_eventuallyEq ?_ (hI t ht')
    filter_upwards [Icc_mem_nhdsGE ht.2] with s hs
    exact hI s ⟨ht.1.trans hs.1, hs.2⟩

/-- **Square-root Gronwall inequality**, integral form: `Q t ≤ Q a + ½ ∫ₐᵗ F` for `F ≥ 0`
continuous on `[a,b]` and `d/dt Q² ≤ F Q` on `[a,b)`.
Thesis: Lemma 4.12 (corrected). -/
theorem le_add_half_integral_of_sq_deriv_le_mul {Q q' F : ℝ → ℝ} {a b : ℝ}
    (hQc : ContinuousOn Q (Icc a b)) (hQ0 : ∀ t ∈ Icc a b, 0 ≤ Q t)
    (hq : ∀ t ∈ Ico a b, HasDerivWithinAt (fun s => Q s ^ 2) (q' t) (Ici t) t)
    (hFc : ContinuousOn F (Icc a b)) (hF : ∀ t ∈ Ico a b, 0 ≤ F t)
    (hle : ∀ t ∈ Ico a b, q' t ≤ F t * Q t) :
    ∀ t ∈ Icc a b, Q t ≤ Q a + (1 / 2) * ∫ s in a..t, F s := by
  intro t ht
  obtain ⟨hGc, hG⟩ := hFc.intervalIntegral_primitive_Icc
  have := le_add_half_sub_of_sq_deriv_le_mul hQc hQ0 hq hGc hG hF hle t ht
  simp only [intervalIntegral.integral_same, sub_zero] at this
  linarith
