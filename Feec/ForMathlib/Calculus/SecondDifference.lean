module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Polynomial growth from derivative bounds, and the second difference

* `norm_image_le_of_norm_deriv_le_pow`: `‖g(t)‖ ≤ c (t - a)ᵐ⁺¹ / (m + 1)` on `[a, b]` from
  `g(a) = 0` and `‖g'(t)‖ ≤ c (t - a)ᵐ` (right derivatives);
* `abs_secondDiff_sub_le`: the truncation error of the centred second difference,
  `|g(h) - 2 g(0) + g(-h) - h² g''(0)| ≤ B h⁴ / 12` for `|g⁗| ≤ B` on `[-h, h]`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set

@[expose] public noncomputable section

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `‖g(t)‖ ≤ c (t - a)ᵐ⁺¹ / (m + 1)` on `[a, b]` from `g(a) = 0` and `‖g'(t)‖ ≤ c (t - a)ᵐ`. -/
theorem norm_image_le_of_norm_deriv_le_pow {g g' : ℝ → X} {a b c : ℝ} (m : ℕ)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (ha : g a = 0) (hb : ∀ t ∈ Ico a b, ‖g' t‖ ≤ c * (t - a) ^ m) :
    ∀ t ∈ Icc a b, ‖g t‖ ≤ c * (t - a) ^ (m + 1) / (m + 1) := by
  refine fun t ht => image_norm_le_of_norm_deriv_right_le_deriv_boundary hg hg'
    (B := fun s => c * (s - a) ^ (m + 1) / (m + 1)) (by simp [ha]) (fun s => ?_) hb ht
  refine ((((hasDerivAt_id' s).sub_const a).pow (m + 1)).const_mul c |>.div_const
    ((m : ℝ) + 1)).congr_deriv ?_
  rw [Nat.add_sub_cancel]
  push_cast
  field_simp

end

/-- **The second difference**: for `g` with derivatives `g₁, …, g₄` on `[-h, h]` and
`|g₄| ≤ B`, `|g(h) - 2 g(0) + g(-h) - h² g₂(0)| ≤ B h⁴ / 12`. -/
theorem abs_secondDiff_sub_le {g g₁ g₂ g₃ g₄ : ℝ → ℝ} {h B : ℝ} (hh : 0 ≤ h)
    (h₀ : ∀ t ∈ Icc (-h) h, HasDerivAt g (g₁ t) t) (h₁ : ∀ t ∈ Icc (-h) h, HasDerivAt g₁ (g₂ t) t)
    (h₂ : ∀ t ∈ Icc (-h) h, HasDerivAt g₂ (g₃ t) t) (h₃ : ∀ t ∈ Icc (-h) h, HasDerivAt g₃ (g₄ t) t)
    (hB : ∀ t ∈ Icc (-h) h, |g₄ t| ≤ B) :
    |g h - 2 * g 0 + g (-h) - h ^ 2 * g₂ 0| ≤ B * h ^ 4 / 12 := by
  have hI : ∀ t ∈ Icc 0 h, t ∈ Icc (-h) h ∧ -t ∈ Icc (-h) h := fun t ht =>
    ⟨⟨by linarith [ht.1], ht.2⟩, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩
  have hneg : ∀ t, HasDerivAt (fun x : ℝ => -x) (-1) t := fun t => (hasDerivAt_id' t).neg
  -- the even and odd parts and their derivatives
  set φ₀ : ℝ → ℝ := fun t => g t + g (-t) - 2 * g 0 - t ^ 2 * g₂ 0
  set φ₁ : ℝ → ℝ := fun t => g₁ t - g₁ (-t) - 2 * t * g₂ 0
  set φ₂ : ℝ → ℝ := fun t => g₂ t + g₂ (-t) - 2 * g₂ 0
  set φ₃ : ℝ → ℝ := fun t => g₃ t - g₃ (-t)
  set φ₄ : ℝ → ℝ := fun t => g₄ t + g₄ (-t)
  have d₀ : ∀ t ∈ Icc 0 h, HasDerivAt φ₀ (φ₁ t) t := fun t ht => by
    have := (((h₀ t (hI t ht).1).add ((h₀ (-t) (hI t ht).2).comp t (hneg t))).sub_const
      (2 * g 0)).sub ((hasDerivAt_pow 2 t).mul_const (g₂ 0))
    exact this.congr_deriv (by simp only [φ₁]; ring)
  have d₁ : ∀ t ∈ Icc 0 h, HasDerivAt φ₁ (φ₂ t) t := fun t ht => by
    have := (((h₁ t (hI t ht).1).sub ((h₁ (-t) (hI t ht).2).comp t (hneg t))).sub
      (((hasDerivAt_id t).const_mul 2).mul_const (g₂ 0)))
    exact this.congr_deriv (by simp only [φ₂]; ring)
  have d₂ : ∀ t ∈ Icc 0 h, HasDerivAt φ₂ (φ₃ t) t := fun t ht => by
    have := ((h₂ t (hI t ht).1).add ((h₂ (-t) (hI t ht).2).comp t (hneg t))).sub_const (2 * g₂ 0)
    exact this.congr_deriv (by simp only [φ₃]; ring)
  have d₃ : ∀ t ∈ Icc 0 h, HasDerivAt φ₃ (φ₄ t) t := fun t ht => by
    have := (h₃ t (hI t ht).1).sub ((h₃ (-t) (hI t ht).2).comp t (hneg t))
    exact this.congr_deriv (by simp only [φ₄]; ring)
  have c : ∀ {f f' : ℝ → ℝ}, (∀ t ∈ Icc 0 h, HasDerivAt f (f' t) t) → ContinuousOn f (Icc 0 h) ∧
      ∀ t ∈ Ico 0 h, HasDerivWithinAt f (f' t) (Ici t) t := fun hf =>
    ⟨fun t ht => (hf t ht).continuousAt.continuousWithinAt,
      fun t ht => (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt⟩
  have A := norm_image_le_of_norm_deriv_le_pow (c := 2 * B) 0 (c d₃).1 (c d₃).2 (by simp [φ₃])
    fun t ht => by
      have := hI t (Ico_subset_Icc_self ht)
      simp only [pow_zero, mul_one, Real.norm_eq_abs, φ₄]
      exact (abs_add_le _ _).trans (by linarith [hB t this.1, hB (-t) this.2])
  have B₂ := norm_image_le_of_norm_deriv_le_pow (c := 2 * B) 1 (c d₂).1 (c d₂).2 (by simp [φ₂]; ring)
    fun t ht => (A t (Ico_subset_Icc_self ht)).trans (le_of_eq (by push_cast; ring))
  have C := norm_image_le_of_norm_deriv_le_pow (c := B) 2 (c d₁).1 (c d₁).2 (by simp [φ₁])
    fun t ht => (B₂ t (Ico_subset_Icc_self ht)).trans (le_of_eq (by push_cast; ring))
  have D := norm_image_le_of_norm_deriv_le_pow (c := B / 3) 3 (c d₀).1 (c d₀).2 (by simp [φ₀]; ring)
    fun t ht => (C t (Ico_subset_Icc_self ht)).trans (le_of_eq (by push_cast; ring))
  have := D h ⟨hh, le_rfl⟩
  rw [Real.norm_eq_abs] at this
  calc |g h - 2 * g 0 + g (-h) - h ^ 2 * g₂ 0| = |φ₀ h| := by congr 1; simp only [φ₀]; ring
    _ ≤ _ := this
    _ = B * h ^ 4 / 12 := by push_cast; ring

