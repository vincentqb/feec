module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Elementary inequalities used in a priori estimates

* `mul_le_sq_div_add_mul_sq_div`: Young's inequality `xy ≤ x²/(2θ) + θy²/2` (`θ > 0`);
* `Finset.le_mul_sum_sq_of_mul_le_sum_mul`: the absorption step of an a priori estimate;
* `norm_add_sq_le_two_mul`, `norm_sub_sq_le_two_mul`, `norm_add₃_sq_le_three_mul`: squared
  triangle inequalities;
* `Submodule.norm_le_of_mem_orthogonal_of_sub_mem`: minimum-norm principle.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

/-- **Young's inequality** with a parameter: `x y ≤ x² / (2θ) + θ y² / 2` for `θ > 0`. -/
theorem mul_le_sq_div_add_mul_sq_div (x y : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    x * y ≤ x ^ 2 / (2 * θ) + θ * y ^ 2 / 2 := by
  have h := sq_nonneg (x - θ * y)
  have : x * y = (x ^ 2 + θ ^ 2 * y ^ 2 - (x - θ * y) ^ 2) / (2 * θ) := by
    rw [eq_div_iff (by positivity)]; ring
  rw [this, div_le_iff₀ (by positivity)]
  have : (x ^ 2 / (2 * θ) + θ * y ^ 2 / 2) * (2 * θ) = x ^ 2 + θ ^ 2 * y ^ 2 := by
    rw [add_mul, div_mul_cancel₀ _ (by positivity)]; ring
  rw [this]; linarith

/-- **Absorption.** If `κ N ≤ Σᵢ Dᵢ Lᵢ` with `κ, K > 0` and `Lᵢ² ≤ K N` for every `i ∈ s`, then
`N ≤ (#s + 1) K / κ² · Σᵢ Dᵢ²`. -/
theorem Finset.le_mul_sum_sq_of_mul_le_sum_mul {ι : Type*} (s : Finset ι) (D L : ι → ℝ)
    {κ K N : ℝ} (hκ : 0 < κ) (hK : 0 < K)
    (hL : ∀ i ∈ s, L i ^ 2 ≤ K * N) (h : κ * N ≤ ∑ i ∈ s, D i * L i) :
    N ≤ (s.card + 1) * K / κ ^ 2 * ∑ i ∈ s, D i ^ 2 := by
  rcases lt_or_ge N 0 with hN | hN
  · refine hN.le.trans ?_
    have := Finset.sum_nonneg (fun i (_ : i ∈ s) => sq_nonneg (D i))
    positivity
  set m : ℝ := s.card + 1 with hm_def
  have hm : 0 < m := by positivity
  set θ := κ / (m * K) with hθ_def
  have hθ : 0 < θ := by positivity
  have hterm : ∀ i ∈ s, D i * L i ≤ D i ^ 2 / (2 * θ) + θ * (K * N) / 2 := fun i hi => by
    have h1 := mul_le_sq_div_add_mul_sq_div (D i) (L i) hθ
    have h2 := mul_le_mul_of_nonneg_left (hL i hi) hθ.le
    linarith
  have hsum := (h.trans (Finset.sum_le_sum hterm))
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div] at hsum
  set S := ∑ i ∈ s, D i ^ 2
  have hθK : θ * K = κ / m := by rw [hθ_def]; field_simp
  have hcard : (s.card : ℝ) * (θ * (K * N) / 2) ≤ κ * N / 2 := by
    have : (s.card : ℝ) * (θ * (K * N) / 2) = (s.card / m) * (κ * N / 2) := by
      rw [← mul_assoc θ, hθK]; field_simp
    rw [this]
    have hc : (s.card : ℝ) / m ≤ 1 := by rw [div_le_one hm]; linarith
    have := mul_nonneg hκ.le hN
    nlinarith
  have h3 : κ * N / 2 ≤ S / (2 * θ) := by linarith
  have h4 : S / (2 * θ) = m * K / κ * S / 2 := by rw [hθ_def]; field_simp
  rw [h4] at h3
  rw [show m * K / κ ^ 2 * S = (m * K / κ * S / 2) * 2 / κ by field_simp]
  rw [le_div_iff₀ hκ]
  linarith

/-- `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
theorem norm_add_sq_le_two_mul {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have := norm_add_le x y
  nlinarith [norm_nonneg (x + y), sq_nonneg (‖x‖ - ‖y‖)]

/-- `‖x - y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
theorem norm_sub_sq_le_two_mul {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  simpa [sub_eq_add_neg] using norm_add_sq_le_two_mul x (-y)

/-- `‖x + y + z‖² ≤ 3(‖x‖² + ‖y‖² + ‖z‖²)`. -/
theorem norm_add₃_sq_le_three_mul {E : Type*} [SeminormedAddCommGroup E] (x y z : E) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h1 := norm_add_le (x + y) z
  have h2 := norm_add_le x y
  nlinarith [norm_nonneg (x + y + z), sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖),
    sq_nonneg (‖y‖ - ‖z‖), norm_nonneg x, norm_nonneg y, norm_nonneg z, norm_nonneg (x + y)]

/-- **Minimum-norm principle**: if `u ⊥ K` and `u' - u ∈ K` then `‖u‖ ≤ ‖u'‖`. -/
theorem Submodule.norm_le_of_mem_orthogonal_of_sub_mem {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {K : Submodule 𝕜 E} {u u' : E}
    (hu : u ∈ Kᗮ) (h : u' - u ∈ K) : ‖u‖ ≤ ‖u'‖ := by
  have h0 : inner 𝕜 u (u' - u) = 0 := Submodule.inner_left_of_mem_orthogonal h hu
  have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u (u' - u) h0
  rw [add_sub_cancel] at hsq
  nlinarith [norm_nonneg u, norm_nonneg u', mul_self_nonneg ‖u' - u‖]
