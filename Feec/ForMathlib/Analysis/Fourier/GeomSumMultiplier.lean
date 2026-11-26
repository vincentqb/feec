module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Feec.ForMathlib.Analysis.Carlson
public import Feec.ForMathlib.Analysis.Fourier.Plancherel

/-!
# An `L¹` bound for functions with a geometric-sum Fourier transform

If `ψ` and `t ψ` lie in `L¹ ∩ L²` and `𝓕 ψ = w Σ_{j<n} qʲ` with `|q| ≤ 1`, `q = 1 + z^{p+1} w`
(`z = -2πiξ`) and bounds on `w`, `w'` and `q'`, then `∫ |ψ| ≤ K n` ([BrennerThomee1979]).

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../../../docs/references.bib)
-/

open MeasureTheory Finset FourierTransform
open scoped Real

@[expose] public noncomputable section

namespace Feec

namespace GeomSum

/-- The symbol `z = -2πiξ`. -/
def symb (ξ : ℝ) : ℂ := -(2 * π * ξ * Complex.I)

theorem norm_symb (ξ : ℝ) : ‖symb ξ‖ = 2 * π * |ξ| := by
  simp [symb, abs_of_pos Real.pi_pos]

theorem norm_two_pi_I : ‖-(2 * (π : ℂ) * Complex.I)‖ = 2 * π := by
  simp [abs_of_pos Real.pi_pos]

theorem hasDerivAt_symb (ξ : ℝ) : HasDerivAt symb (-(2 * π * Complex.I)) ξ := by
  have h := ((((hasDerivAt_id ξ).ofReal_comp).const_mul (2 * (π : ℂ))).mul_const Complex.I).neg
  convert h using 1
  · ext y; simp [symb]
  · simp

/-- `D = 2π (p+1) W₀ + W₁ + Q₁`, the constant of `|q'| ≤ D |z|ᵖ`. -/
def derivConst (p : ℕ) (W₀ W₁ Q₁ : ℝ) : ℝ := 2 * π * (p + 1) * W₀ + W₁ + Q₁

/-- `B₁ = 2 (W₁ + (W₀ + 1) D + 4π (p+1))`. -/
def derivBound (p : ℕ) (W₀ W₁ Q₁ : ℝ) : ℝ :=
  2 * (W₁ + (W₀ + 1) * derivConst p W₀ W₁ Q₁ + 4 * π * (p + 1))

variable {p n : ℕ} {w q w' q' : ℝ → ℂ} {W₀ W₁ Q₁ : ℝ}

theorem norm_deriv_le (hw : ∀ ξ, HasDerivAt w (w' ξ) ξ) (hq : ∀ ξ, HasDerivAt q (q' ξ) ξ)
    (hqw : ∀ ξ, q ξ = 1 + symb ξ ^ (p + 1) * w ξ) (hW₀ : ∀ ξ, ‖w ξ‖ ≤ W₀)
    (hW₁ : ∀ ξ, ‖w' ξ‖ ≤ W₁) (hQ₁ : ∀ ξ, ‖q' ξ‖ ≤ Q₁) (ξ : ℝ) :
    ‖q' ξ‖ ≤ derivConst p W₀ W₁ Q₁ * ‖symb ξ‖ ^ p := by
  have h0 : 0 ≤ W₀ := (norm_nonneg _).trans (hW₀ 0)
  have h1 : 0 ≤ W₁ := (norm_nonneg _).trans (hW₁ 0)
  have h2 : 0 ≤ Q₁ := (norm_nonneg _).trans (hQ₁ 0)
  set a := ‖symb ξ‖
  have ha : 0 ≤ a := norm_nonneg _
  rcases le_total a 1 with hle | hle
  · have hd : HasDerivAt q ((p + 1 : ℕ) * symb ξ ^ p * -(2 * π * Complex.I) * w ξ +
        symb ξ ^ (p + 1) * w' ξ) ξ := by
      have := (((hasDerivAt_symb ξ).pow (p + 1)).mul (hw ξ)).const_add 1
      rw [show q = fun ξ => 1 + symb ξ ^ (p + 1) * w ξ from funext hqw]
      convert this using 1
      simp
    rw [(hq ξ).unique hd]
    have e1 : ‖((p + 1 : ℕ) : ℂ) * symb ξ ^ p * -(2 * π * Complex.I) * w ξ‖ =
        (p + 1) * a ^ p * (2 * π) * ‖w ξ‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast, norm_two_pi_I]
      push_cast; ring
    have e2 : ‖symb ξ ^ (p + 1) * w' ξ‖ = a ^ (p + 1) * ‖w' ξ‖ := by
      rw [norm_mul, norm_pow]
    refine (norm_add_le _ _).trans ?_
    rw [e1, e2]
    have hap : a ^ (p + 1) ≤ a ^ p := pow_le_pow_of_le_one ha hle (Nat.le_succ p)
    calc (p + 1) * a ^ p * (2 * π) * ‖w ξ‖ + a ^ (p + 1) * ‖w' ξ‖
        ≤ (p + 1) * a ^ p * (2 * π) * W₀ + a ^ p * W₁ := by
          have hw1 : a ^ (p + 1) * ‖w' ξ‖ ≤ a ^ p * W₁ :=
            (mul_le_mul_of_nonneg_right hap (norm_nonneg _)).trans
              (mul_le_mul_of_nonneg_left (hW₁ ξ) (pow_nonneg ha p))
          have hw0 : (p + 1) * a ^ p * (2 * π) * ‖w ξ‖ ≤ (p + 1) * a ^ p * (2 * π) * W₀ :=
            mul_le_mul_of_nonneg_left (hW₀ ξ) (by positivity)
          linarith
      _ ≤ derivConst p W₀ W₁ Q₁ * a ^ p := by
          unfold derivConst
          nlinarith [pow_nonneg ha p, Real.pi_pos]
  · calc ‖q' ξ‖ ≤ Q₁ := hQ₁ ξ
      _ ≤ Q₁ * a ^ p := le_mul_of_one_le_right h2 (one_le_pow₀ hle)
      _ ≤ derivConst p W₀ W₁ Q₁ * a ^ p := by
          gcongr
          unfold derivConst
          have : 0 ≤ 2 * π * (p + 1) * W₀ := by positivity
          linarith

theorem norm_sum_pow_le {x : ℂ} (hx : ‖x‖ ≤ 1) (n : ℕ) : ‖∑ j ∈ range n, x ^ j‖ ≤ n := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j ∈ range n, ‖x ^ j‖ ≤ ∑ _j ∈ range n, (1 : ℝ) :=
        sum_le_sum fun j _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    _ = n := by simp

variable {lam : ℝ}

theorem pow_lam_mul (hlam : lam ^ (p + 1) = n) (ξ : ℝ) :
    (lam * ‖symb ξ‖) ^ (p + 1) = n * ‖symb ξ‖ ^ (p + 1) := by
  rw [mul_pow, hlam]

theorem norm_geomSum_le (hq1 : ∀ ξ, ‖q ξ‖ ≤ 1) (hqw : ∀ ξ, q ξ = 1 + symb ξ ^ (p + 1) * w ξ)
    (hW₀ : ∀ ξ, ‖w ξ‖ ≤ W₀) (hlam : lam ^ (p + 1) = n) (hlam1 : 1 ≤ lam) (ξ : ℝ) :
    (1 + lam * ‖symb ξ‖) * ‖w ξ * ∑ j ∈ range n, q ξ ^ j‖ ≤ (2 * W₀ + 4) * n := by
  have h0 : 0 ≤ W₀ := (norm_nonneg _).trans (hW₀ 0)
  set t := lam * ‖symb ξ‖
  have ht : 0 ≤ t := mul_nonneg (by linarith) (norm_nonneg _)
  set F := w ξ * ∑ j ∈ range n, q ξ ^ j
  have hF : ‖F‖ ≤ W₀ * n := by
    rw [norm_mul]
    exact mul_le_mul (hW₀ ξ) (norm_sum_pow_le (hq1 ξ) n) (norm_nonneg _) h0
  rcases le_total t 1 with hle | hle
  · nlinarith [norm_nonneg F]
  · -- `z^{p+1} F = qⁿ - 1`
    have hzF : symb ξ ^ (p + 1) * F = q ξ ^ n - 1 := by
      rw [← geom_sum_mul, show q ξ - 1 = symb ξ ^ (p + 1) * w ξ by rw [hqw ξ]; ring]
      simp only [F]; ring
    have h2 : ‖symb ξ‖ ^ (p + 1) * ‖F‖ ≤ 2 := by
      rw [← norm_pow, ← norm_mul, hzF]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, norm_one]
      linarith [pow_le_one₀ (norm_nonneg _) (hq1 ξ) (n := n)]
    have h3 : t * ‖F‖ ≤ 2 * n := by
      have : t ^ (p + 1) * ‖F‖ ≤ 2 * n := by
        rw [pow_lam_mul hlam]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      exact (mul_le_mul_of_nonneg_right (le_self_pow₀ hle (Nat.succ_ne_zero p))
        (norm_nonneg _)).trans this
    nlinarith [norm_nonneg F, Nat.cast_nonneg (α := ℝ) n]

theorem norm_deriv_geomSum_le (hw : ∀ ξ, HasDerivAt w (w' ξ) ξ)
    (hq : ∀ ξ, HasDerivAt q (q' ξ) ξ) (hq1 : ∀ ξ, ‖q ξ‖ ≤ 1)
    (hqw : ∀ ξ, q ξ = 1 + symb ξ ^ (p + 1) * w ξ) (hW₀ : ∀ ξ, ‖w ξ‖ ≤ W₀)
    (hW₁ : ∀ ξ, ‖w' ξ‖ ≤ W₁) (hQ₁ : ∀ ξ, ‖q' ξ‖ ≤ Q₁) (hlam : lam ^ (p + 1) = n)
    (hlam1 : 1 ≤ lam) {F' : ℝ → ℂ}
    (hF : ∀ ξ, HasDerivAt (fun ξ => w ξ * ∑ j ∈ range n, q ξ ^ j) (F' ξ) ξ) (ξ : ℝ) :
    (1 + lam * ‖symb ξ‖) * ‖F' ξ‖ ≤ derivBound p W₀ W₁ Q₁ * (n * lam) := by
  have h0 : 0 ≤ W₀ := (norm_nonneg _).trans (hW₀ 0)
  have h1 : 0 ≤ W₁ := (norm_nonneg _).trans (hW₁ 0)
  have h2 : 0 ≤ Q₁ := (norm_nonneg _).trans (hQ₁ 0)
  set D := derivConst p W₀ W₁ Q₁
  have hD : 0 ≤ D := by unfold D derivConst; positivity
  have hqD := norm_deriv_le hw hq hqw hW₀ hW₁ hQ₁ ξ
  set a := ‖symb ξ‖
  have ha : 0 ≤ a := norm_nonneg _
  set t := lam * a
  have ht : 0 ≤ t := mul_nonneg (by linarith) ha
  have hn : (n : ℝ) ≤ n * lam := le_mul_of_one_le_right (Nat.cast_nonneg _) hlam1
  have hnl : 0 ≤ (n : ℝ) * lam := (Nat.cast_nonneg _).trans hn
  have hpi := Real.pi_pos
  rcases le_total t 1 with hle | hle
  · -- the product rule: `F' = w' S + w S'`
    set S := ∑ j ∈ range n, q ξ ^ j
    set S' := ∑ j ∈ range n, (j : ℂ) * q ξ ^ (j - 1) * q' ξ
    have hS : HasDerivAt (fun ξ => ∑ j ∈ range n, q ξ ^ j) S' ξ := by
      have := HasDerivAt.sum (u := range n) fun j _ => (hq ξ).pow j
      convert this using 1
      ext x; simp [Finset.sum_apply]
    rw [(hF ξ).unique ((hw ξ).mul hS)]
    have hS1 : ‖S‖ ≤ n := norm_sum_pow_le (hq1 ξ) n
    have hS2 : ‖S'‖ ≤ n * (n * ‖q' ξ‖) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j ∈ range n, ‖(j : ℂ) * q ξ ^ (j - 1) * q' ξ‖
          ≤ ∑ _j ∈ range n, (n * ‖q' ξ‖ : ℝ) := sum_le_sum fun j hj => by
            rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
            have hj' : (j : ℝ) ≤ n := by exact_mod_cast (mem_range.1 hj).le
            have hp : ‖q ξ‖ ^ (j - 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) (hq1 ξ)
            calc (j : ℝ) * ‖q ξ‖ ^ (j - 1) * ‖q' ξ‖ ≤ n * 1 * ‖q' ξ‖ := by gcongr
              _ = _ := by ring
        _ = _ := by simp
    -- `n² aᵖ ≤ n λ`
    have hlp : 0 < lam ^ p := pow_pos (by linarith) p
    have hna : (n : ℝ) * (n * a ^ p) ≤ n * lam := by
      refine le_of_mul_le_mul_left ?_ hlp
      have : lam ^ p * ((n : ℝ) * (n * a ^ p)) = n * n * t ^ p := by rw [mul_pow]; ring
      rw [this, show lam ^ p * ((n : ℝ) * lam) = n * lam ^ (p + 1) by ring, hlam]
      have : t ^ p ≤ 1 := pow_le_one₀ ht hle
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hb : ‖w' ξ * S + w ξ * S'‖ ≤ (W₁ + W₀ * D) * (n * lam) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      calc ‖w' ξ‖ * ‖S‖ + ‖w ξ‖ * ‖S'‖ ≤ W₁ * n + W₀ * (n * (n * (D * a ^ p))) := by
            gcongr
            · exact hW₁ ξ
            · exact hW₀ ξ
            · exact hS2.trans (by gcongr)
        _ ≤ W₁ * (n * lam) + W₀ * (D * (n * lam)) := by
            have e : (n : ℝ) * (n * (D * a ^ p)) = D * (n * (n * a ^ p)) := by ring
            have h3 : (n : ℝ) * (n * (D * a ^ p)) ≤ D * (n * lam) :=
              e ▸ mul_le_mul_of_nonneg_left hna hD
            have := mul_le_mul_of_nonneg_left h3 h0
            have := mul_le_mul_of_nonneg_left hn h1
            linarith
        _ = _ := by ring
    calc (1 + t) * ‖w' ξ * S + w ξ * S'‖ ≤ 2 * ((W₁ + W₀ * D) * (n * lam)) := by
          nlinarith [norm_nonneg (w' ξ * S + w ξ * S')]
      _ ≤ derivBound p W₀ W₁ Q₁ * (n * lam) := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ hnl
          show 2 * (W₁ + W₀ * D) ≤ 2 * (W₁ + (W₀ + 1) * D + 4 * π * (p + 1))
          have : 0 ≤ 4 * π * (p + 1) := by positivity
          nlinarith
  · -- differentiate `z^{p+1} F = qⁿ - 1`
    set F := w ξ * ∑ j ∈ range n, q ξ ^ j
    have hzF : ∀ ξ, symb ξ ^ (p + 1) * (w ξ * ∑ j ∈ range n, q ξ ^ j) = q ξ ^ n - 1 := by
      intro ξ
      rw [← geom_sum_mul, show q ξ - 1 = symb ξ ^ (p + 1) * w ξ by rw [hqw ξ]; ring]
      ring
    have hd1 : HasDerivAt (fun ξ => symb ξ ^ (p + 1) * (w ξ * ∑ j ∈ range n, q ξ ^ j))
        ((p + 1 : ℕ) * symb ξ ^ p * -(2 * π * Complex.I) * F + symb ξ ^ (p + 1) * F' ξ) ξ := by
      convert ((hasDerivAt_symb ξ).pow (p + 1)).mul (hF ξ) using 1
      simp [F]
    have hd2 : HasDerivAt (fun ξ => symb ξ ^ (p + 1) * (w ξ * ∑ j ∈ range n, q ξ ^ j))
        (n * q ξ ^ (n - 1) * q' ξ) ξ := by
      convert ((hq ξ).pow n).sub_const 1 using 1
      ext x; simp [hzF x]
    have heq := hd1.unique hd2
    -- `|z|^{p+1} |F| ≤ 2`
    have hF2 : a ^ (p + 1) * ‖F‖ ≤ 2 := by
      rw [← norm_pow, ← norm_mul, hzF]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, norm_one]
      linarith [pow_le_one₀ (norm_nonneg _) (hq1 ξ) (n := n)]
    have hz : symb ξ ^ (p + 1) * F' ξ = n * q ξ ^ (n - 1) * q' ξ -
        (p + 1 : ℕ) * symb ξ ^ p * -(2 * π * Complex.I) * F := by
      linear_combination heq
    have hnq : ‖(n : ℂ) * q ξ ^ (n - 1) * q' ξ‖ ≤ n * (D * a ^ p) := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      have : ‖q ξ‖ ^ (n - 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) (hq1 ξ)
      calc (n : ℝ) * ‖q ξ‖ ^ (n - 1) * ‖q' ξ‖ ≤ n * 1 * (D * a ^ p) := by gcongr
        _ = _ := by ring
    have hpF : ‖((p + 1 : ℕ) : ℂ) * symb ξ ^ p * -(2 * π * Complex.I) * F‖ =
        (p + 1) * (2 * π) * (a ^ p * ‖F‖) := by
      rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast, norm_two_pi_I]
      push_cast; ring
    -- `a^{p+1} (a |F'|) ≤ a^{p+1} n (D + 4π(p+1))`
    have hap : 0 < a := by
      by_contra h
      have : a = 0 := le_antisymm (not_lt.1 h) ha
      simp [t, this] at hle
      linarith
    have key : a ^ (p + 1) * (a * ‖F' ξ‖) ≤ a ^ (p + 1) * (n * (D + 4 * π * (p + 1))) := by
      have e1 : a ^ (p + 1) * (a * ‖F' ξ‖) = a * ‖symb ξ ^ (p + 1) * F' ξ‖ := by
        rw [norm_mul, norm_pow]; ring
      rw [e1, hz]
      have h3 : a * ‖(n : ℂ) * q ξ ^ (n - 1) * q' ξ -
          ((p + 1 : ℕ) : ℂ) * symb ξ ^ p * -(2 * π * Complex.I) * F‖ ≤
          a * (n * (D * a ^ p)) + (p + 1) * (2 * π) * (a ^ (p + 1) * ‖F‖) := by
        refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) ha).trans ?_
        rw [hpF, mul_add, show a * ((p + 1) * (2 * π) * (a ^ p * ‖F‖)) =
          (p + 1) * (2 * π) * (a ^ (p + 1) * ‖F‖) by ring]
        exact add_le_add_left (mul_le_mul_of_nonneg_left hnq ha) _
      refine h3.trans ?_
      have h4 : 1 ≤ n * a ^ (p + 1) := by
        rw [← pow_lam_mul hlam]; exact one_le_pow₀ hle
      have h5 : (p + 1) * (2 * π) * (a ^ (p + 1) * ‖F‖) ≤ (p + 1) * (2 * π) * 2 := by gcongr
      have h6 : a * (n * (D * a ^ p)) = a ^ (p + 1) * (n * D) := by ring
      have h7 : 4 * π * (p + 1) * 1 ≤ 4 * π * (p + 1) * (n * a ^ (p + 1)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      have h8 : a ^ (p + 1) * (n * (D + 4 * π * (p + 1))) =
          a ^ (p + 1) * (n * D) + 4 * π * (p + 1) * (n * a ^ (p + 1)) := by ring
      rw [h6, h8]
      linarith
    have hk : a * ‖F' ξ‖ ≤ n * (D + 4 * π * (p + 1)) :=
      le_of_mul_le_mul_left key (pow_pos hap _)
    have : t * ‖F' ξ‖ ≤ lam * (n * (D + 4 * π * (p + 1))) := by
      calc t * ‖F' ξ‖ = lam * (a * ‖F' ξ‖) := by simp only [t]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hk (by linarith)
    calc (1 + t) * ‖F' ξ‖ ≤ 2 * (t * ‖F' ξ‖) := by nlinarith [norm_nonneg (F' ξ)]
      _ ≤ 2 * (lam * (n * (D + 4 * π * (p + 1)))) := by linarith
      _ ≤ derivBound p W₀ W₁ Q₁ * (n * lam) := by
          unfold derivBound
          have : (0 : ℝ) ≤ W₁ + W₀ * D := by positivity
          nlinarith

theorem integral_norm_sq_le {G : ℝ → ℂ} {B : ℝ} (hlam : 0 < lam)
    (hG : ∀ ξ, (1 + lam * ‖symb ξ‖) * ‖G ξ‖ ≤ B) : ∫ ξ, ‖G ξ‖ ^ 2 ≤ B ^ 2 / (2 * lam) := by
  set T := (2 * π * lam)⁻¹
  have hT : 0 < T := by positivity
  have hpt : ∀ ξ, ‖G ξ‖ ^ 2 ≤ B ^ 2 * (1 + (ξ / T) ^ 2)⁻¹ := fun ξ => by
    have e : lam * ‖symb ξ‖ = |ξ / T| := by
      rw [norm_symb, abs_div, abs_of_pos hT]; simp only [T]; field_simp
    have h := hG ξ
    rw [e] at h
    have h1 : 0 < 1 + |ξ / T| := by positivity
    have h2 : 1 + (ξ / T) ^ 2 ≤ (1 + |ξ / T|) ^ 2 := by
      nlinarith [abs_nonneg (ξ / T), sq_abs (ξ / T)]
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ‖G ξ‖ ^ 2 * (1 + (ξ / T) ^ 2) ≤ ‖G ξ‖ ^ 2 * (1 + |ξ / T|) ^ 2 := by gcongr
      _ = ((1 + |ξ / T|) * ‖G ξ‖) ^ 2 := by ring
      _ ≤ B ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  have hint : Integrable fun ξ : ℝ => B ^ 2 * (1 + (ξ / T) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_div hT.ne').const_mul _
  calc ∫ ξ, ‖G ξ‖ ^ 2 ≤ ∫ ξ, B ^ 2 * (1 + (ξ / T) ^ 2)⁻¹ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity) hint
          (Filter.Eventually.of_forall hpt)
    _ = B ^ 2 / (2 * lam) := by
        rw [integral_const_mul, MemLp.integral_inv_one_add_div_sq hT]
        simp only [T]; field_simp

end GeomSum

/-- The constant `K = √((2W₀ + 4) B₁/2)` of the geometric-sum bound. -/
def geomSumConst (p : ℕ) (W₀ W₁ Q₁ : ℝ) : ℝ :=
  √((2 * W₀ + 4) * GeomSum.derivBound p W₀ W₁ Q₁ / 2)

open GeomSum in
/-- If `ψ` and `t ψ` lie in `L¹ ∩ L²` and `𝓕 ψ = w Σ_{j<n} qʲ` with `|q| ≤ 1`,
`q = 1 + z^{p+1} w`, `|w| ≤ W₀`, `|w'| ≤ W₁` and `|q'| ≤ Q₁`, then `∫ |ψ| ≤ K n`,
`K = geomSumConst p W₀ W₁ Q₁`. -/
theorem _root_.MeasureTheory.Integrable.integral_norm_le_of_fourier_eq_geom_sum {ψ : ℝ → ℂ}
    (hψ : Integrable ψ) (hψ2 : MemLp ψ 2) (htψ : Integrable fun t : ℝ => t • ψ t)
    (htψ2 : MemLp (fun t : ℝ => t • ψ t) 2) {p n : ℕ} {w q w' q' : ℝ → ℂ} {W₀ W₁ Q₁ : ℝ}
    (hw : ∀ ξ, HasDerivAt w (w' ξ) ξ) (hq : ∀ ξ, HasDerivAt q (q' ξ) ξ) (hq1 : ∀ ξ, ‖q ξ‖ ≤ 1)
    (hqw : ∀ ξ, q ξ = 1 + symb ξ ^ (p + 1) * w ξ) (hW₀ : ∀ ξ, ‖w ξ‖ ≤ W₀)
    (hW₁ : ∀ ξ, ‖w' ξ‖ ≤ W₁) (hQ₁ : ∀ ξ, ‖q' ξ‖ ≤ Q₁)
    (hF : ∀ ξ, 𝓕 ψ ξ = w ξ * ∑ j ∈ range n, q ξ ^ j) :
    ∫ t, ‖ψ t‖ ≤ geomSumConst p W₀ W₁ Q₁ * n := by
  have h0 : 0 ≤ W₀ := (norm_nonneg _).trans (hW₀ 0)
  have h1 : 0 ≤ W₁ := (norm_nonneg _).trans (hW₁ 0)
  have h2 : 0 ≤ Q₁ := (norm_nonneg _).trans (hQ₁ 0)
  have hB₁ : 0 ≤ derivBound p W₀ W₁ Q₁ := by
    unfold derivBound derivConst; have := Real.pi_pos; positivity
  have hK : 0 ≤ geomSumConst p W₀ W₁ Q₁ := Real.sqrt_nonneg _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `𝓕 ψ = 0`, so `ψ = 0` in `L²`
    have h := MemLp.integral_norm_fourier_sq hψ hψ2
    simp only [hF, range_zero, sum_empty, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero] at h
    have hz : ∀ᵐ t, ‖ψ t‖ ^ 2 = 0 := by
      have := (integral_eq_zero_iff_of_nonneg (fun t => by positivity)
        ((memLp_two_iff_integrable_sq_norm hψ2.aestronglyMeasurable).1 hψ2)).1 h.symm
      filter_upwards [this] with t ht using ht
    rw [integral_eq_zero_of_ae (hz.mono fun t ht => by simpa using ht)]
    simp
  set lam : ℝ := (n : ℝ) ^ ((p + 1 : ℕ) : ℝ)⁻¹
  have hlam : lam ^ (p + 1) = n :=
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (Nat.succ_ne_zero p)
  have hlam1 : 1 ≤ lam := Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  have hlam0 : 0 < lam := by linarith
  set F' : ℝ → ℂ := 𝓕 fun t : ℝ => (-2 * π * Complex.I * t) • ψ t
  have hFd : ∀ ξ, HasDerivAt (fun ξ => w ξ * ∑ j ∈ range n, q ξ ^ j) (F' ξ) ξ := fun ξ => by
    rw [show (fun ξ => w ξ * ∑ j ∈ range n, q ξ ^ j) = 𝓕 ψ from funext fun ξ => (hF ξ).symm]
    exact Real.hasDerivAt_fourier hψ htψ ξ
  -- the two `L²` bounds
  have hI1 : ∫ ξ, ‖𝓕 ψ ξ‖ ^ 2 ≤ ((2 * W₀ + 4) * n) ^ 2 / (2 * lam) :=
    integral_norm_sq_le hlam0 fun ξ => by
      rw [hF]; exact norm_geomSum_le hq1 hqw hW₀ hlam hlam1 ξ
  have hI2 : ∫ ξ, ‖F' ξ‖ ^ 2 ≤ (derivBound p W₀ W₁ Q₁ * (n * lam)) ^ 2 / (2 * lam) :=
    integral_norm_sq_le hlam0 fun ξ =>
      norm_deriv_geomSum_le hw hq hq1 hqw hW₀ hW₁ hQ₁ hlam hlam1 hFd ξ
  -- `F' = -2πi 𝓕 (t ψ)`
  have hF' : ∀ ξ, ‖F' ξ‖ = 2 * π * ‖𝓕 (fun t : ℝ => t • ψ t) ξ‖ := fun ξ => by
    have h : (fun t : ℝ => (-2 * π * Complex.I * t) • ψ t) =
        (-2 * π * Complex.I) • fun t : ℝ => t • ψ t := by
      ext t
      simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
      ring
    simp only [F', h]
    rw [show 𝓕 ((-2 * π * Complex.I) • fun t : ℝ => t • ψ t) =
      (-2 * π * Complex.I) • 𝓕 (fun t : ℝ => t • ψ t) from
        VectorFourier.fourierIntegral_const_smul _ _ _ _ _, Pi.smul_apply, norm_smul]
    simp [abs_of_pos Real.pi_pos]
  have hT : ∫ t, ‖t • ψ t‖ ^ 2 = (∫ ξ, ‖F' ξ‖ ^ 2) / (4 * π ^ 2) := by
    rw [← MemLp.integral_norm_fourier_sq htψ htψ2, ← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hF', mul_pow]
    field_simp
    ring
  have hC := MemLp.integral_norm_pow_four_le hψ2 htψ2
  rw [hT, ← MemLp.integral_norm_fourier_sq hψ hψ2] at hC
  have hpi := Real.pi_pos
  have hA : 0 ≤ ∫ ξ, ‖𝓕 ψ ξ‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hB : 0 ≤ ∫ ξ, ‖F' ξ‖ ^ 2 := integral_nonneg fun _ => by positivity
  have h4 : (∫ t, ‖ψ t‖) ^ 4 ≤ (geomSumConst p W₀ W₁ Q₁ * n) ^ 4 := by
    refine hC.trans ?_
    have e : 4 * π ^ 2 * (∫ ξ, ‖𝓕 ψ ξ‖ ^ 2) * ((∫ ξ, ‖F' ξ‖ ^ 2) / (4 * π ^ 2)) =
        (∫ ξ, ‖𝓕 ψ ξ‖ ^ 2) * ∫ ξ, ‖F' ξ‖ ^ 2 := by field_simp
    rw [e]
    have hK4 : geomSumConst p W₀ W₁ Q₁ ^ 4 = ((2 * W₀ + 4) * derivBound p W₀ W₁ Q₁ / 2) ^ 2 := by
      rw [geomSumConst, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
    calc (∫ ξ, ‖𝓕 ψ ξ‖ ^ 2) * ∫ ξ, ‖F' ξ‖ ^ 2
        ≤ (((2 * W₀ + 4) * n) ^ 2 / (2 * lam)) *
            ((derivBound p W₀ W₁ Q₁ * (n * lam)) ^ 2 / (2 * lam)) :=
          mul_le_mul hI1 hI2 hB (by positivity)
      _ = (geomSumConst p W₀ W₁ Q₁ * n) ^ 4 := by
          rw [mul_pow (geomSumConst p W₀ W₁ Q₁), hK4]; field_simp
  exact (pow_le_pow_iff_left₀ (integral_nonneg fun _ => norm_nonneg _) (by positivity)
    (by norm_num : 4 ≠ 0)).1 h4

end Feec
