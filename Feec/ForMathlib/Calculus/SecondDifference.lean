module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Feec.ForMathlib.Calculus.Partial

/-!
# Polynomial growth from derivative bounds, and the second difference

* `norm_image_le_of_norm_deriv_le_pow`: `‖g(t)‖ ≤ c (t - a)ᵐ⁺¹ / (m + 1)` on `[a, b]` from
  `g(a) = 0` and `‖g'(t)‖ ≤ c (t - a)ᵐ` (right derivatives);
* `abs_secondDiff_sub_le`: the truncation error of the centred second difference,
  `|g(h) - 2 g(0) + g(-h) - h² g''(0)| ≤ B h⁴ / 12` for `|g⁗| ≤ B` on `[-h, h]`;
* `abs_taylor_one_le`: `|g(1) - g(0) - g'(0)| ≤ M / 2` for `|g''| ≤ M` on `[0, 1]`;
* along the lines of `ℝⁿ` (`hasDerivAt_comp_line`, `hasDerivAt_comp_add_smul_single`): Taylor's
  formula along an axis (`abs_axis_taylor_le`), the second difference along an axis
  (`abs_axis_secondDiff_le`) and its truncation error for `C⁴` functions
  (`abs_partialDeriv_sub_secondDiff_le`).

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

/-! ### Taylor's formula along the lines of `ℝⁿ` -/

namespace Feec

variable {n : ℕ}

/-- `|g(1) - g(0) - g'(0)| ≤ M / 2` for `|g''| ≤ M` on `[0, 1]`. -/
theorem abs_taylor_one_le {g g₁ g₂ : ℝ → ℝ} {M : ℝ}
    (h₀ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (g₁ t) t)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g₁ (g₂ t) t) (hM : ∀ t ∈ Icc (0 : ℝ) 1, |g₂ t| ≤ M) :
    |g 1 - g 0 - g₁ 0| ≤ M / 2 := by
  have c : ∀ {f f' : ℝ → ℝ}, (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t) →
      ContinuousOn f (Icc 0 1) ∧ ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Ici t) t :=
    fun hf => ⟨fun t ht => (hf t ht).continuousAt.continuousWithinAt,
      fun t ht => (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt⟩
  have d₁ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => g₁ t - g₁ 0) (g₂ t) t :=
    fun t ht => (h₁ t ht).sub_const _
  have d₀ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => g t - g 0 - t * g₁ 0) (g₁ t - g₁ 0) t :=
    fun t ht => (((h₀ t ht).sub_const _).sub ((hasDerivAt_id t).mul_const _)).congr_deriv
      (by simp)
  have A := norm_image_le_of_norm_deriv_le_pow (c := M) 0 (c d₁).1 (c d₁).2 (by simp)
    fun t ht => by simpa using hM t (Ico_subset_Icc_self ht)
  have B := norm_image_le_of_norm_deriv_le_pow (c := M) 1 (c d₀).1 (c d₀).2 (by simp)
    fun t ht => (A t (Ico_subset_Icc_self ht)).trans (le_of_eq (by ring))
  have := B 1 ⟨zero_le_one, le_rfl⟩
  simp only [Real.norm_eq_abs, one_mul, sub_zero, one_pow, mul_one] at this
  convert this using 2
  norm_num

/-- `t ↦ f(x + t v)` has derivative `Σᵢ vᵢ ∂ᵢ f(x + t v)`. -/
theorem hasDerivAt_comp_line {f : (Fin n → ℝ) → ℝ} {x v : Fin n → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (x + t • v)) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (∑ i, v i * partialDeriv i f (x + t • v)) t := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have := hf.hasFDerivAt.comp_hasDerivAt t hl
  rwa [fderiv_apply_eq_sum_partialDeriv] at this

/-- `r ↦ f(x + r eₗ)` has derivative `∂ₗ f(x + t eₗ)` at `t`. -/
theorem hasDerivAt_comp_add_smul_single {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (x : Fin n → ℝ)
    (l : Fin n) (t : ℝ) :
    HasDerivAt (fun r : ℝ => f (x + r • Pi.single l 1))
      (partialDeriv l f (x + t • Pi.single l 1)) t := by
  have hl : HasDerivAt (fun r : ℝ => x + r • (Pi.single l 1 : Fin n → ℝ)) (Pi.single l 1) t := by
    simpa using ((hasDerivAt_id t).smul_const (Pi.single l (1 : ℝ) : Fin n → ℝ)).const_add x
  exact (hf _).hasFDerivAt.comp_hasDerivAt t hl

theorem sum_smul_single_mul (l : Fin n) (t : ℝ) (F : Fin n → ℝ) :
    ∑ i, (t • Pi.single l 1 : Fin n → ℝ) i * F i = t * F l := by
  rw [Finset.sum_eq_single l]
  · simp
  · intro i _ hi; simp [hi]
  · simp

/-- **Taylor along an axis**: `|f(x + t eₗ) - f(x) - t ∂ₗf(x)| ≤ B t² / 2` for `|∂ₗ²f| ≤ B` on
the segment. -/
theorem abs_axis_taylor_le {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (x : Fin n → ℝ)
    (l : Fin n) (t : ℝ) {B : ℝ}
    (hB : ∀ τ ∈ uIcc 0 t, |partialDeriv l (partialDeriv l f) (x + τ • Pi.single l 1)| ≤ B) :
    |f (x + t • Pi.single l 1) - f x - t * partialDeriv l f x| ≤ B * t ^ 2 / 2 := by
  have hd1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (partialDeriv l f) :=
    (hf.partialDeriv (m := 1) (by norm_num) l).differentiable (by norm_num)
  set v : Fin n → ℝ := t • Pi.single l 1
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • v = x + (τ * t) • Pi.single l 1 := fun τ _ => by
    simp [v, smul_smul]
  have hmem : ∀ τ ∈ Icc (0 : ℝ) 1, τ * t ∈ uIcc 0 t := fun τ hτ => by
    rw [Set.mem_uIcc]
    rcases le_total 0 t with ht | ht
    · left; exact ⟨mul_nonneg hτ.1 ht, by nlinarith [hτ.2]⟩
    · right; exact ⟨by nlinarith [hτ.2], mul_nonpos_of_nonneg_of_nonpos hτ.1 ht⟩
  have := abs_taylor_one_le (g := fun τ => f (x + τ • v))
    (g₁ := fun τ => t * partialDeriv l f (x + τ • v))
    (g₂ := fun τ => t * (t * partialDeriv l (partialDeriv l f) (x + τ • v))) (M := B * t ^ 2)
    (fun τ _ => by
      have := hasDerivAt_comp_line (v := v) (hd1 (x + τ • v))
      rwa [sum_smul_single_mul] at this)
    (fun τ _ => by
      have := hasDerivAt_comp_line (v := v) (hd2 (x + τ • v))
      rw [sum_smul_single_mul] at this
      exact this.const_mul t)
    (fun τ hτ => by
      have h := hB _ (hmem τ hτ)
      rw [← hseg τ hτ] at h
      rw [abs_mul, abs_mul, ← mul_assoc, abs_mul_abs_self]
      nlinarith [sq_nonneg t])
  simpa [v] using this

/-- **The second difference**: `|f(x + h eₗ) - 2 f(x) + f(x - h eₗ)| ≤ B h²`. -/
theorem abs_axis_secondDiff_le {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (x : Fin n → ℝ)
    (l : Fin n) {h B : ℝ}
    (hB : ∀ τ ∈ Icc (-|h|) |h|, |partialDeriv l (partialDeriv l f) (x + τ • Pi.single l 1)| ≤ B) :
    |f (x + h • Pi.single l 1) - 2 * f x + f (x + (-h) • Pi.single l 1)| ≤ B * h ^ 2 := by
  have sub : ∀ t, |t| = |h| → uIcc 0 t ⊆ Icc (-|h|) |h| := fun t ht τ hτ => by
    rw [← ht]
    rcases Set.mem_uIcc.1 hτ with h1 | h1 <;> constructor <;>
      cases abs_cases t <;> linarith [h1.1, h1.2]
  have h1 := abs_axis_taylor_le hf x l h fun τ hτ => hB τ (sub h rfl hτ)
  have h2 := abs_axis_taylor_le hf x l (-h) fun τ hτ => hB τ (sub (-h) (abs_neg h) hτ)
  calc |f (x + h • Pi.single l 1) - 2 * f x + f (x + (-h) • Pi.single l 1)|
      = |(f (x + h • Pi.single l 1) - f x - h * partialDeriv l f x) +
          (f (x + (-h) • Pi.single l 1) - f x - -h * partialDeriv l f x)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by nlinarith [neg_sq h])

/-- **The truncation error of the second difference**: for `u ∈ C⁴` with `|∂ₗ⁴u| ≤ B` on
`x + [-h, h] eₗ`, `|∂ₗ²u(x) - (u(x + h eₗ) - 2 u(x) + u(x - h eₗ)) / h²| ≤ B h² / 12`. -/
theorem abs_partialDeriv_sub_secondDiff_le {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 4 u) {h B : ℝ}
    (hh : 0 < h) (x : Fin n → ℝ) (l : Fin n)
    (hB : ∀ t ∈ Icc (-h) h, |(partialDeriv l)^[4] u (x + t • Pi.single l 1)| ≤ B) :
    |partialDeriv l (partialDeriv l u) x -
        (u (x + h • Pi.single l 1) - 2 * u x + u (x + (-h) • Pi.single l 1)) / h ^ 2| ≤
      B * h ^ 2 / 12 := by
  have hd : ∀ k : ℕ, k ≤ 3 → Differentiable ℝ ((partialDeriv l)^[k] u) := by
    intro k hk
    have : ∀ k ≤ 4, ContDiff ℝ (4 - k : ℕ) ((partialDeriv l)^[k] u) := by
      intro k hk
      induction k with
      | zero => simpa using hu
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (ih (by omega)).partialDeriv (by norm_cast; omega) l
    exact (this k (by omega)).differentiable (by norm_cast; omega)
  set g : ℕ → ℝ → ℝ := fun k t => (partialDeriv l)^[k] u (x + t • Pi.single l 1)
  have hg : ∀ k ≤ 3, ∀ t, HasDerivAt (g k) (g (k + 1) t) t := fun k hk t => by
    have := hasDerivAt_comp_add_smul_single (hd k hk) x l t
    simpa [g, Function.iterate_succ_apply'] using this
  have key := abs_secondDiff_sub_le (g := g 0) (g₁ := g 1) (g₂ := g 2) (g₃ := g 3)
    (g₄ := g 4) (B := B) hh.le (fun t _ => hg 0 (by omega) t) (fun t _ => hg 1 (by omega) t)
    (fun t _ => hg 2 (by omega) t) (fun t _ => hg 3 le_rfl t) hB
  simp only [g, Function.iterate_zero, id, zero_smul, add_zero, Function.iterate_succ,
    Function.comp] at key
  have hh2 : 0 < h ^ 2 := by positivity
  rw [show partialDeriv l (partialDeriv l u) x -
      (u (x + h • Pi.single l 1) - 2 * u x + u (x + (-h) • Pi.single l 1)) / h ^ 2 =
      -(u (x + h • Pi.single l 1) - 2 * u x + u (x + (-h) • Pi.single l 1) -
        h ^ 2 * partialDeriv l (partialDeriv l u) x) / h ^ 2 by field_simp; ring,
    abs_div, abs_neg, abs_of_pos hh2, div_le_iff₀ hh2]
  calc _ ≤ B * h ^ 4 / 12 := key
    _ = B * h ^ 2 / 12 * h ^ 2 := by ring

end Feec
