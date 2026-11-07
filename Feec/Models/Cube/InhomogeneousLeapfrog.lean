module

public import Feec.Models.Cube.InhomogeneousError
public import Feec.FiniteElement.GlobalInverseEstimate
public import Feec.TimeStepping.Leapfrog

/-!
# The explicit leapfrog Whitney scheme under a CFL condition

The fully discrete scheme of [QuennevilleBelair2015], Ch. 7 with the explicit leapfrog rule in
place of Crank–Nicolson: on the Whitney row `Vₕ = P₁Λ⁰ × P₁⁻Λ¹ × P₁⁻Λ²` of the level-`(N + 1)`
Freudenthal mesh of `Q = (0, ½)³`, with the boundary degrees of freedom of every step taken from
the exact solution, `uₙ₊₂ − gₙ₊₂ ∈ V̊ₕ`, `⟪uₙ₊₂ − uₙ, v⟫ = 2 Δt ⟪A uₙ₊₁, v⟫` on `V̊ₕ`
(`TimeStepping.IsDirichletLeapfrogStep`), `A = 𝐝ₕ − 𝐝ₕ*`. Unlike Crank–Nicolson (stable for every
time step), leapfrog is stable only under a **CFL condition** `Δt ‖A‖ ≤ c < 1`, and the inverse
estimate makes it concrete: `h ‖𝐝ₕ v‖ ≤ K ‖v‖` on `Vₕ` (`exists_mul_norm_discreteD_whitneyRow_le`,
from `Feec.FiniteElement.exists_mul_norm_glue_dPiecewise_le_whitney`), so `‖A‖ ≤ 2 K / h`
(`norm_discreteWave_le`) and `2 K Δt ≤ c h` is a CFL condition.

## The error argument

As for Crank–Nicolson (`Feec.Models.Cube.InhomogeneousError`), the comparison fields
`ũₙ = wₙ − q (emb wₙ − U(tₙ))` with the boundary correction `q` keep the boundary DOFs of the
interpolants `wₙ`, are no farther from `U(tₙ)`, and are orthogonal to `emb (D V̊ₕ)`; with the
centred difference remainder `TimeStepping.norm_centredDifference_le` they solve the leapfrog
scheme up to residuals `‖ρₙ‖ ≤ Δt (L₃ Δt² / 3 + 4 a)` (`exists_leapfrog_comparison`). The CFL
estimate of `TimeStepping.norm_succ_sub_le_of_isDirichletLeapfrogStep` then gives
`(1 − c) ‖emb u_M − U(t_M)‖ ≤ 3 a + T (L₃ Δt² / 3 + 4 a)` from `u₀ = w₀`, `u₁ = w₁`
(`norm_leapfrog_error_le`).

## Main results

* `norm_discreteD_le`, `norm_discreteWave_le`: on a finite element subcomplex, a bound `K` on the
  discrete differentials `Vₕⁱ → Vₕʲ` bounds `‖𝐝ₕ‖ ≤ K` and `‖𝐝ₕ − 𝐝ₕ*‖ ≤ 2 K`.
* **`exists_mul_norm_discreteD_whitneyRow_le`**: the inverse estimate
  `h_N ‖𝐝ₕ v‖ ≤ K ‖v‖` on the Whitney row, `K` independent of `N`.
* `norm_leapfrog_error_le`, `norm_leapfrog_error_le_of_eq`: the abstract error estimate.
* **`RowSolution.whitney_leapfrog_error_le_row`**: for a smooth `RowSolution` with bound `L`,
  `2 K Δt ≤ c h_N`, `0 ≤ c < 1`, the leapfrog iterates from `u₀ = Π_h U(0)`, `u₁ = Π_h U(Δt)` with
  the boundary DOFs of `Π_h U(tₙ)` satisfy
  `‖u_M − U(t_M)‖ ≤ C L (1 + T) (h_N + Δt²) / (1 − c)`, `C = leapfrogConst`.
* **`whitney_leapfrog_stable`**: with vanishing boundary DOFs,
  `√(1 − c) ‖uₙ₊₁‖ ≤ √((1 + c) (‖u₀‖² + ‖u₁‖²))` under the same CFL condition.

## References

* [P. Joly, *Variational Methods for Time-Dependent Wave Propagation Problems*][Joly2003]
  (leapfrog, discrete energy, CFL condition)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.2 (inverse
  inequalities)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter MeasureTheory

namespace Feec.Models.Cube.Inhomogeneous

/-! ## The error of the leapfrog scheme with Dirichlet DOFs, abstractly -/

section Abstract

variable {V X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] {emb : V →ₗ[ℝ] X} {D : V →ₗ[ℝ] V}
  {V₀ : Submodule ℝ V}

/-- **Comparison fields and residuals of the Dirichlet leapfrog scheme**, abstractly, in the
setting of `exists_comparison_consistency`: the comparison fields `ũₙ = wₙ − q δₙ` have the
boundary DOFs of `wₙ`, are no farther from `U(tₙ)` than `wₙ`, and solve the leapfrog scheme with
step `Δt` up to residuals `ρₙ` with `‖ρₙ‖ ≤ Δt (L₃ Δt² / 3 + 4 a)` (the centred difference
remainder, the time differences of the interpolation error, and `‖emb (D wₙ₊₁) − DU(tₙ₊₁)‖`; the
adjoint terms vanish by the boundary correction). -/
theorem exists_leapfrog_comparison (hemb : ∀ x y, ⟪emb x, emb y⟫ = ⟪x, y⟫)
    (hD₀ : ∀ v ∈ V₀, D v ∈ V₀) (hDD : ∀ v ∈ V₀, D (D v) = 0) {A : V →ₗ[ℝ] V}
    (hA : ∀ x y, ⟪A x, y⟫ = ⟪D x, y⟫ - ⟪x, D y⟫) {Δt T L₃ a : ℝ} (hΔt : 0 < Δt)
    {U U₁ U₂ U₃ DU : ℝ → X} (hU₁ : ∀ t, HasDerivAt U (U₁ t) t)
    (hU₂ : ∀ t, HasDerivAt U₁ (U₂ t) t) (hU₃ : ∀ t, HasDerivAt U₂ (U₃ t) t)
    (hL₃ : ∀ t ∈ Icc 0 T, ‖U₃ t‖ ≤ L₃)
    (hweak : ∀ t ∈ Icc 0 T, ∀ v ∈ V₀, ⟪U₁ t, emb v⟫ = ⟪DU t, emb v⟫ - ⟪U t, emb (D v)⟫)
    {w : ℕ → V}
    (hA2 : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (D (w n)) - DU (n * Δt)‖ ≤ a)
    (hA3 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * Δt ≤ T →
      ‖(emb (w (n + 1)) - U ((n + 1 : ℕ) * Δt)) - (emb (w n) - U (n * Δt))‖ ≤ a * Δt) :
    ∃ ũ ρ : ℕ → V, (∀ n, ũ n - w n ∈ V₀) ∧
      (∀ n : ℕ, ‖ũ n - w n‖ ≤ ‖emb (w n) - U (n * Δt)‖) ∧
      (∀ n : ℕ, ‖emb (ũ n) - U (n * Δt)‖ ≤ ‖emb (w n) - U (n * Δt)‖) ∧
      (∀ n, ∀ v ∈ V₀, ⟪ũ (n + 2) - ũ n, v⟫ = 2 * Δt * ⟪A (ũ (n + 1)), v⟫ + ⟪ρ n, v⟫) ∧
      (∀ n : ℕ, ((n + 2 : ℕ) : ℝ) * Δt ≤ T → ‖ρ n‖ ≤ Δt * (L₃ * Δt ^ 2 / 3 + 4 * a)) := by
  set δ : ℕ → X := fun n => emb (w n) - U (n * Δt)
  set ũ : ℕ → V := fun n => w n - bdryCorr emb D V₀ (δ n)
  set z : ℕ → V := fun n => ũ (n + 2) - ũ n - (2 * Δt) • A (ũ (n + 1))
  set ρ : ℕ → V := fun n => V₀.starProjection (z n)
  have hqV₀ : ∀ y, bdryCorr emb D V₀ y ∈ V₀ := fun y => bdrySub_le hD₀ (bdryCorr_mem y)
  have hDũ : ∀ n, D (ũ n) = D (w n) := fun n => by
    simp only [ũ, map_sub, D_eq_zero_of_mem_bdrySub hDD (bdryCorr_mem _), sub_zero]
  have hρc : ∀ n : ℕ, emb (ũ n) - U (n * Δt) = δ n - emb (bdryCorr emb D V₀ (δ n)) :=
    fun n => by simp only [ũ, δ, map_sub]; abel
  have horth : ∀ n : ℕ, ∀ v ∈ V₀, ⟪U (n * Δt) - emb (ũ n), emb (D v)⟫ = 0 := fun n v hv => by
    have h := inner_sub_bdryCorr (D := D) (V₀ := V₀) hemb (δ n) (Submodule.mem_map_of_mem hv)
    rw [← neg_sub, inner_neg_left, hρc, h, neg_zero]
  have hρz : ∀ n, ∀ v ∈ V₀, ⟪ρ n, v⟫ = ⟪z n, v⟫ := fun n v hv => by
    simp only [ρ]
    rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 hv]
  refine ⟨ũ, ρ, fun n => ?_, fun n => ?_, fun n => ?_, fun n v hv => ?_, fun n hn => ?_⟩
  · simp only [ũ, sub_sub_cancel_left]
    exact V₀.neg_mem (hqV₀ _)
  · simp only [ũ, sub_sub_cancel_left, norm_neg]
    exact (norm_sub_bdryCorr_le hemb (δ n)).2
  · rw [hρc]; exact (norm_sub_bdryCorr_le hemb (δ n)).1
  · rw [hρz n v hv]
    simp only [z, inner_sub_left, real_inner_smul_left]
    ring
  -- the bound on `ρₙ`
  set ε := Δt * (L₃ * Δt ^ 2 / 3 + 4 * a)
  have hn0 : (0 : ℝ) ≤ n * Δt := mul_nonneg (Nat.cast_nonneg n) hΔt.le
  have hc1 : ((n + 1 : ℕ) : ℝ) * Δt = n * Δt + Δt := by push_cast; ring
  have hc2 : ((n + 2 : ℕ) : ℝ) * Δt = n * Δt + Δt + Δt := by push_cast; ring
  have hn1T : ((n + 1 : ℕ) : ℝ) * Δt ≤ T := by rw [hc1]; rw [hc2] at hn; linarith
  have hnT : (n : ℝ) * Δt ≤ T := by rw [hc1] at hn1T; linarith
  have hm : ((n + 1 : ℕ) : ℝ) * Δt ∈ Icc 0 T := ⟨by positivity, hn1T⟩
  -- the centred difference at `tₙ₊₁`
  have hTay : ‖U (((n + 1 : ℕ) : ℝ) * Δt + Δt) - U (((n + 1 : ℕ) : ℝ) * Δt - Δt) -
      (2 * Δt) • U₁ (((n + 1 : ℕ) : ℝ) * Δt)‖ ≤ Δt ^ 3 * L₃ / 3 :=
    TimeStepping.norm_centredDifference_le hΔt.le (fun t _ => hU₁ t) (fun t _ => hU₂ t)
      (fun t _ => hU₃ t) fun t ht => hL₃ t ⟨by rw [hc1] at ht; linarith [ht.1],
        by rw [hc1] at ht; rw [hc2] at hn; linarith [ht.2]⟩
  rw [show ((n + 1 : ℕ) : ℝ) * Δt + Δt = ((n + 2 : ℕ) : ℝ) * Δt by rw [hc1, hc2],
    show ((n + 1 : ℕ) : ℝ) * Δt - Δt = (n : ℝ) * Δt by rw [hc1]; ring] at hTay
  -- `⟪zₙ, v⟫ ≤ ε ‖v‖` on `V̊ₕ`
  have key : ∀ v ∈ V₀, ⟪z n, v⟫ ≤ ε * ‖v‖ := by
    intro v hv
    set Tn := U (((n + 2 : ℕ) : ℝ) * Δt) - U (n * Δt) - (2 * Δt) • U₁ (((n + 1 : ℕ) : ℝ) * Δt)
    set ρc : ℕ → X := fun k => δ k - emb (bdryCorr emb D V₀ (δ k))
    set e1 := emb (D (w (n + 1))) - DU (((n + 1 : ℕ) : ℝ) * Δt)
    have hρd : ρc (n + 2) - ρc n =
        (δ (n + 2) - δ n) - emb (bdryCorr emb D V₀ (δ (n + 2) - δ n)) := by
      simp only [ρc, map_sub]; abel
    have hδ : ‖δ (n + 2) - δ n‖ ≤ 2 * a * Δt := by
      have h1 := hA3 (n + 1) hn
      have h0 := hA3 n hn1T
      have e : δ (n + 2) - δ n = (δ (n + 1 + 1) - δ (n + 1)) + (δ (n + 1) - δ n) := by abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      simp only [δ] at h1 h0 ⊢
      push_cast at h1 h0 ⊢
      linarith
    have hρb : ‖ρc (n + 2) - ρc n‖ ≤ 2 * a * Δt := by
      rw [hρd]; exact (norm_sub_bdryCorr_le hemb _).1.trans hδ
    have hw1 := hweak _ hm v hv
    have o1 := horth (n + 1) v hv
    have hu2 : emb (ũ (n + 2)) = U (((n + 2 : ℕ) : ℝ) * Δt) + ρc (n + 2) := by
      simp only [ρc]; rw [← hρc (n + 2)]; abel
    have hu0 : emb (ũ n) = U (n * Δt) + ρc n := by simp only [ρc]; rw [← hρc n]; abel
    have hid : ⟪z n, v⟫ = ⟪Tn, emb v⟫ + ⟪ρc (n + 2) - ρc n, emb v⟫ - 2 * Δt * ⟪e1, emb v⟫ := by
      have i1 : ⟪ũ (n + 2) - ũ n, v⟫ = ⟪emb (ũ (n + 2)) - emb (ũ n), emb v⟫ := by
        rw [← hemb, map_sub]
      have i2 : ⟪D (ũ (n + 1)), v⟫ = ⟪emb (D (w (n + 1))), emb v⟫ := by rw [hDũ, ← hemb]
      have i3 : ⟪ũ (n + 1), D v⟫ = ⟪U (((n + 1 : ℕ) : ℝ) * Δt), emb (D v)⟫ := by
        rw [← hemb]
        rw [inner_sub_left] at o1
        linarith
      simp only [z, inner_sub_left, real_inner_smul_left, hA, i1, i2, i3]
      simp only [Tn, e1, inner_sub_left, real_inner_smul_left, hu2, hu0, inner_add_left, hw1]
      ring
    rw [hid]
    have hy : ‖emb v‖ = ‖v‖ := norm_emb hemb v
    have b1 : ⟪Tn, emb v⟫ ≤ Δt ^ 3 * L₃ / 3 * ‖v‖ := by
      rw [← hy]
      exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hTay (norm_nonneg _))
    have b2 : ⟪ρc (n + 2) - ρc n, emb v⟫ ≤ 2 * a * Δt * ‖v‖ := by
      rw [← hy]
      exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hρb (norm_nonneg _))
    have b3 : -(2 * Δt * ⟪e1, emb v⟫) ≤ 2 * Δt * a * ‖v‖ := by
      have h1 := abs_real_inner_le_norm e1 (emb v)
      have h2 := neg_abs_le ⟪e1, emb v⟫
      have h3 : ‖e1‖ * ‖emb v‖ ≤ a * ‖emb v‖ :=
        mul_le_mul_of_nonneg_right (hA2 (n + 1) hn1T) (norm_nonneg _)
      rw [hy] at h3 h1
      have : 0 ≤ 2 * Δt := by linarith
      nlinarith
    have : ε * ‖v‖ = Δt ^ 3 * L₃ / 3 * ‖v‖ + 2 * a * Δt * ‖v‖ + 2 * Δt * a * ‖v‖ := by
      simp only [ε]; ring
    linarith
  have hρmem : ρ n ∈ V₀ := Submodule.starProjection_apply_mem _ _
  have hρρ : ‖ρ n‖ ^ 2 = ⟪z n, ρ n⟫ := by
    rw [← real_inner_self_eq_norm_sq]; exact hρz n _ hρmem
  have hk := key _ hρmem
  rw [← hρρ] at hk
  rcases (norm_nonneg (ρ n)).eq_or_lt with h0 | hpos
  · rw [← h0]
    have : 0 ≤ L₃ := (norm_nonneg _).trans (hL₃ _ ⟨hn0, hnT⟩)
    have ha : 0 ≤ a := (norm_nonneg _).trans (hA2 n hnT)
    positivity
  · nlinarith

/-- **Error of the Dirichlet leapfrog scheme under the CFL condition**, abstractly: in the setting
of `exists_leapfrog_comparison`, with `Δt ‖A‖ ≤ c < 1`, `‖emb wₙ − U(tₙ)‖ ≤ a`, the iterates
`uₙ` of the scheme started from `u₀ = w₀`, `u₁ = w₁` with the boundary DOFs of `wₙ` satisfy, for
`M Δt ≤ T`, `(1 − c) ‖emb u_M − U(t_M)‖ ≤ 3 a + T (L₃ Δt² / 3 + 4 a)`. -/
theorem norm_leapfrog_error_le (hemb : ∀ x y, ⟪emb x, emb y⟫ = ⟪x, y⟫)
    (hD₀ : ∀ v ∈ V₀, D v ∈ V₀) (hDD : ∀ v ∈ V₀, D (D v) = 0) {A : V →ₗ[ℝ] V}
    (hA : ∀ x y, ⟪A x, y⟫ = ⟪D x, y⟫ - ⟪x, D y⟫) {Δt T L₃ a c : ℝ} (hΔt : 0 < Δt)
    (hc : Δt * ‖LinearMap.toContinuousLinearMap A‖ ≤ c) (hc1 : c < 1)
    {U U₁ U₂ U₃ DU : ℝ → X} (hU₁ : ∀ t, HasDerivAt U (U₁ t) t)
    (hU₂ : ∀ t, HasDerivAt U₁ (U₂ t) t) (hU₃ : ∀ t, HasDerivAt U₂ (U₃ t) t)
    (hL₃ : ∀ t ∈ Icc 0 T, ‖U₃ t‖ ≤ L₃)
    (hweak : ∀ t ∈ Icc 0 T, ∀ v ∈ V₀, ⟪U₁ t, emb v⟫ = ⟪DU t, emb v⟫ - ⟪U t, emb (D v)⟫)
    {w : ℕ → V}
    (hA1 : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (w n) - U (n * Δt)‖ ≤ a)
    (hA2 : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (D (w n)) - DU (n * Δt)‖ ≤ a)
    (hA3 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * Δt ≤ T →
      ‖(emb (w (n + 1)) - U ((n + 1 : ℕ) * Δt)) - (emb (w n) - U (n * Δt))‖ ≤ a * Δt)
    {M : ℕ} (hM : (M : ℝ) * Δt ≤ T) {u g : ℕ → V}
    (hstep : ∀ k, k + 2 ≤ M → TimeStepping.IsDirichletLeapfrogStep V₀ A Δt (g (k + 2)) (u k)
      (u (k + 1)) (u (k + 2)))
    (hg : ∀ k, k + 2 ≤ M → g (k + 2) - w (k + 2) ∈ V₀) (hu0 : u 0 = w 0) (hu1 : u 1 = w 1) :
    (1 - c) * ‖emb (u M) - U (M * Δt)‖ ≤ 3 * a + T * (L₃ * Δt ^ 2 / 3 + 4 * a) := by
  obtain ⟨ũ, ρ, hũw, hũn, hũe, hρ, hρb⟩ :=
    exists_leapfrog_comparison hemb hD₀ hDD hA hΔt hU₁ hU₂ hU₃ hL₃ hweak hA2 hA3
  have hT0 : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg M) hΔt.le).trans hM
  have hL0 : 0 ≤ L₃ := (norm_nonneg _).trans (hL₃ 0 ⟨le_rfl, hT0⟩)
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (hA1 0 (by simpa using hT0))
  have hc0 : 0 ≤ c := (mul_nonneg hΔt.le (norm_nonneg _)).trans hc
  set Y := L₃ * Δt ^ 2 / 3 + 4 * a
  have hY : 0 ≤ Y := by positivity
  have hfin : ∀ m : ℕ, (m : ℝ) * Δt ≤ T → ‖emb (ũ m) - U (m * Δt)‖ ≤ a := fun m hm =>
    (hũe m).trans (hA1 m hm)
  rcases M with _ | n
  · rw [hu0]
    have := hA1 0 (by simpa using hT0)
    have h1 : (1 - c) * ‖emb (w 0) - U ((0 : ℕ) * Δt)‖ ≤ a := by
      have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ 1 - c)
      nlinarith
    have : 0 ≤ T * Y := mul_nonneg hT0 hY
    linarith
  · -- the CFL estimate of `TimeStepping.norm_succ_sub_le_of_isDirichletLeapfrogStep`
    have hAs : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫ := fun x y => by
      have h1 := hA x y
      have h2 := hA y x
      have c1 := real_inner_comm (A y) x
      have c2 := real_inner_comm (D y) x
      have c3 := real_inner_comm y (D x)
      linarith
    have hmem : ∀ k, u k - ũ k = (u k - w k) - (ũ k - w k) := fun k => by abel
    have h0 : u 0 - ũ 0 ∈ V₀ := by rw [hmem, hu0, sub_self, zero_sub]; exact V₀.neg_mem (hũw 0)
    have h1 : u 1 - ũ 1 ∈ V₀ := by rw [hmem, hu1, sub_self, zero_sub]; exact V₀.neg_mem (hũw 1)
    have key := TimeStepping.norm_succ_sub_le_of_isDirichletLeapfrogStep (V₀ := V₀) (n := n)
      (g := g) (u := u) (ũ := ũ) (ρ := ρ) hAs hΔt.le hc hc1
      (fun k hk => hstep k (by omega))
      (fun k hk => by
        have := V₀.sub_mem (hũw (k + 2)) (hg k (by omega))
        rwa [sub_sub_sub_cancel_right] at this)
      h0 h1 (fun k _ => hρ k)
    have hΔT : (1 : ℝ) * Δt ≤ T := by
      have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      nlinarith
    have he0 : ‖u 0 - ũ 0‖ ≤ a := by
      rw [hu0, ← norm_neg, neg_sub]; exact (hũn 0).trans (hA1 0 (by simpa using hT0))
    have he1 : ‖u 1 - ũ 1‖ ≤ a := by
      rw [hu1, ← norm_neg, neg_sub]; exact (hũn 1).trans (hA1 1 (by exact_mod_cast hΔT))
    have hstart : √((1 + c) * (‖u 0 - ũ 0‖ ^ 2 + ‖u 1 - ũ 1‖ ^ 2)) ≤ 2 * a := by
      rw [show 2 * a = √((2 * a) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      refine Real.sqrt_le_sqrt ?_
      have := pow_le_pow_left₀ (norm_nonneg _) he0 2
      have := pow_le_pow_left₀ (norm_nonneg _) he1 2
      nlinarith
    have hsum : ∑ k ∈ Finset.range n, ‖ρ k‖ ≤ T * Y := by
      calc ∑ k ∈ Finset.range n, ‖ρ k‖ ≤ ∑ _k ∈ Finset.range n, Δt * Y :=
            Finset.sum_le_sum fun k hk => hρb k (by
              have : k + 2 ≤ n + 1 := by have := Finset.mem_range.1 hk; omega
              exact (mul_le_mul_of_nonneg_right (by exact_mod_cast this) hΔt.le).trans hM)
        _ = n * Δt * Y := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        _ ≤ T * Y := by
            refine mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right ?_ hΔt.le).trans hM) hY
            exact_mod_cast Nat.le_succ n
    set s := √(1 - c)
    have hs : 0 < s := Real.sqrt_pos.2 (by linarith)
    have hs1 : s ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    have hs2 : s ^ 2 = 1 - c := Real.sq_sqrt (by linarith)
    -- `(1 - c) ‖u_M - ũ_M‖ ≤ 2 a + T Y`
    have he : (1 - c) * ‖u (n + 1) - ũ (n + 1)‖ ≤ 2 * a + T * Y := by
      have h2 : s * ‖u (n + 1) - ũ (n + 1)‖ ≤ 2 * a + T * Y / s := by
        refine key.trans (add_le_add hstart (div_le_div_of_nonneg_right hsum hs.le))
      have h3 : s * (s * ‖u (n + 1) - ũ (n + 1)‖) ≤ s * (2 * a) + T * Y := by
        have := mul_le_mul_of_nonneg_left h2 hs.le
        rwa [mul_add, mul_div_cancel₀ _ hs.ne'] at this
      rw [← hs2]
      nlinarith [mul_le_mul_of_nonneg_right hs1 (by positivity : (0 : ℝ) ≤ 2 * a)]
    have hsplit : emb (u (n + 1)) - U ((n + 1 : ℕ) * Δt) =
        emb (u (n + 1) - ũ (n + 1)) + (emb (ũ (n + 1)) - U ((n + 1 : ℕ) * Δt)) := by
      rw [map_sub]; abel
    rw [hsplit]
    have hn := norm_add_le (emb (u (n + 1) - ũ (n + 1))) (emb (ũ (n + 1)) - U ((n + 1 : ℕ) * Δt))
    rw [norm_emb hemb] at hn
    have hfa := hfin (n + 1) hM
    have h1c : 0 ≤ 1 - c := by linarith
    have := mul_le_mul_of_nonneg_left hn h1c
    have : (1 - c) * ‖emb (ũ (n + 1)) - U ((n + 1 : ℕ) * Δt)‖ ≤ a := by
      have := mul_le_mul_of_nonneg_left hfa h1c
      nlinarith
    nlinarith

/-- `norm_leapfrog_error_le` in the form `K (1 + T) (h + Δt²) / (1 − c)`: if `4 a ≤ K h` and
`L₃ / 3 ≤ K`. -/
theorem norm_leapfrog_error_le_of_eq (hemb : ∀ x y, ⟪emb x, emb y⟫ = ⟪x, y⟫)
    (hD₀ : ∀ v ∈ V₀, D v ∈ V₀) (hDD : ∀ v ∈ V₀, D (D v) = 0) {A : V →ₗ[ℝ] V}
    (hA : ∀ x y, ⟪A x, y⟫ = ⟪D x, y⟫ - ⟪x, D y⟫) {Δt T L₃ a c : ℝ} (hΔt : 0 < Δt)
    (hc : Δt * ‖LinearMap.toContinuousLinearMap A‖ ≤ c) (hc1 : c < 1)
    {U U₁ U₂ U₃ DU : ℝ → X} (hU₁ : ∀ t, HasDerivAt U (U₁ t) t)
    (hU₂ : ∀ t, HasDerivAt U₁ (U₂ t) t) (hU₃ : ∀ t, HasDerivAt U₂ (U₃ t) t)
    (hL₃ : ∀ t ∈ Icc 0 T, ‖U₃ t‖ ≤ L₃)
    (hweak : ∀ t ∈ Icc 0 T, ∀ v ∈ V₀, ⟪U₁ t, emb v⟫ = ⟪DU t, emb v⟫ - ⟪U t, emb (D v)⟫)
    {w : ℕ → V}
    (hA1 : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (w n) - U (n * Δt)‖ ≤ a)
    (hA2 : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (D (w n)) - DU (n * Δt)‖ ≤ a)
    (hA3 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * Δt ≤ T →
      ‖(emb (w (n + 1)) - U ((n + 1 : ℕ) * Δt)) - (emb (w n) - U (n * Δt))‖ ≤ a * Δt)
    {M : ℕ} (hM : (M : ℝ) * Δt ≤ T) {u g : ℕ → V}
    (hstep : ∀ k, k + 2 ≤ M → TimeStepping.IsDirichletLeapfrogStep V₀ A Δt (g (k + 2)) (u k)
      (u (k + 1)) (u (k + 2)))
    (hg : ∀ k, k + 2 ≤ M → g (k + 2) - w (k + 2) ∈ V₀) (hu0 : u 0 = w 0) (hu1 : u 1 = w 1)
    {K h : ℝ} (hKa : 4 * a ≤ K * h) (hKL : L₃ / 3 ≤ K) :
    ‖emb (u M) - U (M * Δt)‖ ≤ K * (1 + T) * (h + Δt ^ 2) / (1 - c) := by
  have he := norm_leapfrog_error_le hemb hD₀ hDD hA hΔt hc hc1 hU₁ hU₂ hU₃ hL₃ hweak hA1 hA2 hA3
    hM hstep hg hu0 hu1
  have hT0 : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg M) hΔt.le).trans hM
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (hA1 0 (by simpa using hT0))
  have hL0 : 0 ≤ L₃ := (norm_nonneg _).trans (hL₃ 0 ⟨le_rfl, hT0⟩)
  have hK0 : 0 ≤ K := (by linarith : 0 ≤ L₃ / 3).trans hKL
  have hd2 : 0 ≤ Δt ^ 2 := sq_nonneg _
  have key : 3 * a + T * (L₃ * Δt ^ 2 / 3 + 4 * a) ≤ K * (1 + T) * (h + Δt ^ 2) := by
    have h1 : L₃ * Δt ^ 2 / 3 ≤ K * Δt ^ 2 := by nlinarith
    have h2 : T * (L₃ * Δt ^ 2 / 3 + 4 * a) ≤ T * (K * Δt ^ 2 + K * h) :=
      mul_le_mul_of_nonneg_left (by linarith) hT0
    have h3 : 0 ≤ K * Δt ^ 2 := mul_nonneg hK0 hd2
    nlinarith
  rw [le_div_iff₀ (by linarith), mul_comm]
  linarith

end Abstract

/-! ## The norm of the discrete wave operator -/

section DiscreteNorm

open HilbertComplex

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex ℝ c W} (S : H.Subcomplex) [∀ i, FiniteDimensional ℝ (S.V i)]

omit [∀ i, FiniteDimensional ℝ (S.V i)] in
/-- **A bound on the discrete differentials bounds `𝐝ₕ`**: if `‖dₕ y‖ ≤ K ‖y‖` for every
`dₕ : Vₕⁱ → Vₕʲ`, then `‖𝐝ₕ x‖ ≤ K ‖x‖` on `Vₕ = ∏ Vₕⁱ` (each `Vₕⁱ` has at most one successor). -/
theorem norm_discreteD_le {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ i j (y : S.V i), ‖S.dLin i j y‖ ≤ K * ‖y‖)
    (x : DState S) : ‖discreteD S x‖ ≤ K * ‖x‖ := by
  classical
  have hj : ∀ j, ∑ i, S.dLin i j (x i) = S.dLin (c.prev j) j (x (c.prev j)) := fun j =>
    Finset.sum_eq_single (c.prev j) (fun i _ hi => by
      rw [S.dLin_eq_zero_of_not_rel fun h => hi (c.prev_eq' h).symm]; rfl) (by simp)
  have hsq : ∀ j, ‖discreteD S x j‖ ^ 2 ≤
      if c.Rel (c.prev j) j then K ^ 2 * ‖x (c.prev j)‖ ^ 2 else 0 := fun j => by
    change ‖∑ i, S.dLin i j (x i)‖ ^ 2 ≤ _
    rw [hj]
    split_ifs with hr
    · rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hK _ _ _) 2
    · rw [S.dLin_eq_zero_of_not_rel hr]; simp
  have hinj : Set.InjOn c.prev {j | c.Rel (c.prev j) j} := fun j hj j' hj' h =>
    c.next_eq (show c.Rel (c.prev j) j from hj) (h ▸ (show c.Rel (c.prev j') j' from hj'))
  have hsum : ∑ j, ‖discreteD S x j‖ ^ 2 ≤ K ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
    calc ∑ j, ‖discreteD S x j‖ ^ 2
        ≤ ∑ j, if c.Rel (c.prev j) j then K ^ 2 * ‖x (c.prev j)‖ ^ 2 else 0 :=
          Finset.sum_le_sum fun j _ => hsq j
      _ = ∑ j ∈ Finset.univ.filter (fun j => c.Rel (c.prev j) j), K ^ 2 * ‖x (c.prev j)‖ ^ 2 :=
          (Finset.sum_filter _ _).symm
      _ = ∑ i ∈ (Finset.univ.filter (fun j => c.Rel (c.prev j) j)).image c.prev,
            K ^ 2 * ‖x i‖ ^ 2 :=
          (Finset.sum_image (s := Finset.univ.filter fun j => c.Rel (c.prev j) j) (g := c.prev)
            (f := fun i => K ^ 2 * ‖x i‖ ^ 2) fun j hj j' hj' h =>
              hinj (Finset.mem_filter.1 hj).2 (Finset.mem_filter.1 hj').2 h).symm
      _ ≤ ∑ i, K ^ 2 * ‖x i‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
      _ = K ^ 2 * ∑ i, ‖x i‖ ^ 2 := by rw [Finset.mul_sum]
  have h2 : (‖discreteD S x‖) ^ 2 ≤ (K * ‖x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2]
    exact hsum
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- **The discrete wave operator is bounded by twice the discrete differential**:
`‖𝐝ₕ x‖ ≤ K ‖x‖` gives `‖(𝐝ₕ − 𝐝ₕ*) x‖ ≤ 2 K ‖x‖`. -/
theorem norm_discreteWave_le {K : ℝ} (hK0 : 0 ≤ K) (hD : ∀ x, ‖discreteD S x‖ ≤ K * ‖x‖)
    (x : DState S) : ‖discreteWave S x‖ ≤ 2 * K * ‖x‖ := by
  set y := discreteWave S x
  have h : ‖y‖ ^ 2 ≤ 2 * K * ‖x‖ * ‖y‖ := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪discreteWave S x, y⟫ ≤ _
    rw [inner_discreteWave]
    have h1 := real_inner_le_norm (discreteD S x) y
    have h2 := neg_le_abs ⟪x, discreteD S y⟫
    have h3 := abs_real_inner_le_norm x (discreteD S y)
    have h4 := mul_le_mul_of_nonneg_right (hD x) (norm_nonneg y)
    have h5 := mul_le_mul_of_nonneg_left (hD y) (norm_nonneg x)
    nlinarith
  rcases (norm_nonneg y).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith

/-- `‖𝐝ₕ − 𝐝ₕ*‖ ≤ 2 K` as an operator norm. -/
theorem opNorm_discreteWave_le {K : ℝ} (hK0 : 0 ≤ K) (hD : ∀ x, ‖discreteD S x‖ ≤ K * ‖x‖) :
    ‖LinearMap.toContinuousLinearMap (discreteWave S)‖ ≤ 2 * K :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => norm_discreteWave_le S hK0 hD x

end DiscreteNorm

/-! ## The inverse estimate on the Whitney row -/

section InverseEstimate

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Mesh HilbertComplex

theorem apply_of_eq {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {f g : E →ₗ.[ℝ] F} (h : f = g) (y : f.domain) (z : g.domain) (hz : (z : E) = y) :
    f y = g z := by
  subst h; rw [show z = y from Subtype.ext hz]

/-- A bound `B ‖d y‖ ≤ K ‖y‖` on the spaces of a subcomplex of `HΛ(M.domain)` holds for the
subcomplex transported along `M.domain = Ω`. -/
theorem mul_norm_d_le_of_maximalSubcomplexOfEq {n : ℕ} {M : SimplicialMesh n}
    {Ω : Set (Fin n → ℝ)} (h : M.domain = Ω) (hM : IsOpen M.domain) (hΩ : IsOpen Ω)
    (S : ((deRham ℝ n).maximalComplex hM).Subcomplex) {B K : ℝ}
    (hS : ∀ (a b : ℤ) (y : (((deRham ℝ n).maximalComplex hM).d a b).domain), y.1 ∈ S.V a →
      B * ‖((deRham ℝ n).maximalComplex hM).d a b y‖ ≤ K * ‖y.1‖)
    (a b : ℤ) (y : (((deRham ℝ n).maximalComplex hΩ).d a b).domain)
    (hy : y.1 ∈ ((deRham ℝ n).maximalSubcomplexOfEq h hM hΩ S).V a) :
    B * ‖((deRham ℝ n).maximalComplex hΩ).d a b y‖ ≤ K * ‖y.1‖ := by
  subst h
  exact hS a b y hy

theorem subsingleton_L2F_of_lt {n : ℕ} (S : Set (Fin n → ℝ)) {j : ℤ} (hj : (n : ℤ) < j) :
    Subsingleton (L2F ℝ S (formIdx n j)) := by
  constructor
  intro x y
  refine PiLp.ext fun s => absurd s.2 ?_
  have : (s.1.card : ℤ) ≤ n := by exact_mod_cast (Finset.card_le_univ s.1).trans (by simp)
  omega

theorem diam_mesh_simplex {n : ℕ} [NeZero n] (N : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) : diam T = meshSize N := by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  rw [diam_freudenthalMesh_simplex 0 (by positivity : (0 : ℝ) < 1 / 2 / ((N + 1 : ℕ) : ℝ))]
  unfold meshSize
  push_cast
  rfl

theorem interior_subset_mesh_domain {n : ℕ} (N : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) : _root_.interior T.closedInterior ⊆ (mesh n N).domain := by
  have hc : Convex ℝ (mesh n N).domain := by rw [mesh_domain]; exact convex_cubeDomain n
  have hne : (_root_.interior (mesh n N).domain).Nonempty := by
    rw [(isOpen_mesh_domain n N).interior_eq, mesh_domain]
    exact ⟨_, center_mem_cubeDomain n⟩
  calc _root_.interior T.closedInterior ⊆ _root_.interior (closure (mesh n N).domain) :=
        interior_mono ((mesh n N).closedInterior_subset_closure hT)
    _ = (mesh n N).domain := by
        rw [hc.interior_closure_eq_interior_of_nonempty_interior hne,
          (isOpen_mesh_domain n N).interior_eq]

/-- **The inverse estimate on the Whitney complexes of the Freudenthal meshes of the cube**:
`h_N ‖d y‖ ≤ K ‖y‖` for every `y ∈ Vₕᵃ` and every differential `d : HΛᵃ(Q) → HΛᵇ(Q)` (`d = 0`
unless `b = a + 1`), one `K` for all `N`, `a`, `b`. -/
theorem exists_mul_norm_d_whitney_le :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) (a b : ℤ) (y : ((complex 3).d a b).domain),
      y.1 ∈ (whitney 3 N).V a → meshSize N * ‖(complex 3).d a b y‖ ≤ K * ‖y.1‖ := by
  have hloc := fun k : ℕ =>
    exists_mul_norm_glue_dPiecewise_le_whitney (n := 3) k (C := max 3 2) (c := 1)
      (by positivity) one_pos
  choose K hK0 hK using hloc
  refine ⟨K 0 + K 1 + K 2, by have := hK0 0; have := hK0 1; have := hK0 2; positivity,
    fun N => mul_norm_d_le_of_maximalSubcomplexOfEq (mesh_domain 3 N) (isOpen_mesh_domain 3 N)
      (isOpen_cubeDomain 3) _ fun a b y hy => ?_⟩
  set Mh := mesh 3 N
  have hKs : 0 ≤ K 0 + K 1 + K 2 := by have := hK0 0; have := hK0 1; have := hK0 2; positivity
  by_cases hab : a + 1 = b
  swap
  · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hab), norm_zero, mul_zero]
    positivity
  subst hab
  rcases lt_or_ge a 0 with ha | ha
  · have := LocalElement.subsingleton_L2F_of_neg (n := 3) Mh.domain ha
    have hy0 : y = 0 :=
      Subtype.ext (@Subsingleton.elim (L2F ℝ Mh.domain (formIdx 3 a)) this _ _)
    rw [hy0, LinearPMap.map_zero, norm_zero, mul_zero]
    exact mul_nonneg hKs (norm_nonneg _)
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = k := ⟨a.toNat, (Int.toNat_of_nonneg ha).symm⟩
  obtain ⟨u, hu⟩ := hy
  obtain ⟨hd, hval⟩ := (whitneyElement 3).glue_mem_maximal Mh (isOpen_mesh_domain 3 N) k u
  rw [apply_of_eq (deRham_maximalComplex_d (isOpen_mesh_domain 3 N) (k : ℤ)) y ⟨_, hd⟩ hu]
  erw [hval]
  have hu' : (whitneyElement 3).glue Mh k u.1 = y.1 := hu
  rw [← hu']
  have hS : IsShapeRegular (Mh.simplices : Set (Affine.Simplex ℝ (Fin 3 → ℝ) 3)) (max 3 2) 1 :=
    fun T hT => isShapeRegular_freudenthalMesh 0 (1 / 2) (by norm_num) T ⟨N, hT⟩
  have hb := hK k Mh (fun T hT => interior_subset_mesh_domain N hT) hS (meshSize_pos N)
    (fun T hT => (diam_mesh_simplex N hT).ge) u.1
  rcases lt_or_ge k 3 with hk | hk
  · have hle : K k ≤ K 0 + K 1 + K 2 := by
      interval_cases k <;> linarith [hK0 0, hK0 1, hK0 2]
    exact hb.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))
  · have := subsingleton_L2F_of_lt (n := 3) Mh.domain (j := (k : ℤ) + 1) (by omega)
    refine le_trans (le_of_eq ?_) (mul_nonneg hKs (norm_nonneg _))
    rw [mul_eq_zero]
    exact Or.inr (norm_eq_zero.2
      (@Subsingleton.elim (L2F ℝ Mh.domain (formIdx 3 ((k : ℤ) + 1))) this _ _))

/-- **The inverse estimate on the Whitney row** `P₁Λ⁰ × P₁⁻Λ¹ × P₁⁻Λ²` of the level-`(N + 1)`
Freudenthal mesh: `h_N ‖𝐝ₕ v‖ ≤ K ‖v‖`, `K` independent of `N`. -/
theorem exists_mul_norm_discreteD_whitneyRow_le :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) (x : DState (whitneyRow N)),
      meshSize N * ‖discreteD (whitneyRow N) x‖ ≤ K * ‖x‖ := by
  obtain ⟨K, hK0, hK⟩ := exists_mul_norm_d_whitney_le
  refine ⟨K, hK0, fun N x => ?_⟩
  have hh := meshSize_pos N
  have hd : ∀ (i j : Fin 3) (y : (whitneyRow N).V i),
      ‖(whitneyRow N).dLin i j y‖ ≤ K / meshSize N * ‖y‖ := fun i j y => by
    rw [div_mul_eq_mul_div, le_div_iff₀ hh, mul_comm]
    exact hK N _ _ ⟨_, (whitneyRow N).le_domain i j y.2⟩ y.2
  have := norm_discreteD_le (whitneyRow N) (by positivity) hd x
  rw [div_mul_eq_mul_div, le_div_iff₀ hh, mul_comm] at this
  exact this

end InverseEstimate

/-! ## The leapfrog Whitney scheme on the cube -/

section WhitneyLeapfrog

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.ExteriorFibre HilbertComplex

variable {T L : ℝ}

/-- The constant of `RowSolution.whitney_leapfrog_error_le_row`: `12 Σᵢ Bᵢ + Σᵢ #Λⁱ |Q|^{1/2}`,
independent of `N`, `Δt`, `T`, `c` and the solution. -/
def leapfrogConst : ℝ := 12 * rowBound + rowL2Const

/-- **`O(h + Δt²)` convergence of the leapfrog Whitney scheme with Dirichlet DOFs under the CFL
condition** ([Joly2003]; [QuennevilleBelair2015], Ch. 7): with `K` the constant of the inverse
estimate `exists_mul_norm_discreteD_whitneyRow_le`, `0 ≤ c < 1` and `2 K Δt ≤ c h_N`, for a smooth
`RowSolution` with bound `L` the leapfrog iterates of the Whitney row from `u₀ = Π_h U(0)`,
`u₁ = Π_h U(Δt)` with the boundary DOFs of `Π_h U(tₙ)` prescribed at every step satisfy
`‖u_M − U(t_M)‖ ≤ C L (1 + T) (h_N + Δt²) / (1 − c)` for `M Δt ≤ T`, `C = leapfrogConst`. -/
theorem RowSolution.whitney_leapfrog_error_le_row (X : RowSolution T L) (N : ℕ) {K : ℝ}
    (hK0 : 0 ≤ K)
    (hK : ∀ x : DState (whitneyRow N), meshSize N * ‖discreteD (whitneyRow N) x‖ ≤ K * ‖x‖)
    {Δt c : ℝ} (hΔt : 0 < Δt) (hc1 : c < 1) (hcfl : 2 * K * Δt ≤ c * meshSize N) (hL0 : 0 ≤ L)
    {M : ℕ} (hM : (M : ℝ) * Δt ≤ T) {u g : ℕ → DState (whitneyRow N)}
    (hstep : ∀ k, k + 2 ≤ M → TimeStepping.IsDirichletLeapfrogStep (whitneyInterior N)
      (discreteWave (whitneyRow N)) Δt (g (k + 2)) (u k) (u (k + 1)) (u (k + 2)))
    (hg : ∀ k, k + 2 ≤ M → g (k + 2) - X.interp N ((k + 2 : ℕ) * Δt) ∈ whitneyInterior N)
    (hu0 : u 0 = X.interp N 0) (hu1 : u 1 = X.interp N Δt) :
    ‖dEmb (whitneyRow N) (u M) - X.field (M * Δt)‖ ≤
      leapfrogConst * L * (1 + T) * (meshSize N + Δt ^ 2) / (1 - c) := by
  have hh := meshSize_pos N
  have hB := rowBound_nonneg
  have hR := rowL2Const_nonneg
  have hx0 : 0 ≤ rowBound * L * meshSize N := mul_nonneg (mul_nonneg hB hL0) hh.le
  have hmem : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → (n : ℝ) * Δt ∈ Icc 0 T := fun n hn =>
    ⟨mul_nonneg (Nat.cast_nonneg n) hΔt.le, hn⟩
  -- the CFL condition `Δt ‖A‖ ≤ c`
  have hD : ∀ x : DState (whitneyRow N), ‖discreteD (whitneyRow N) x‖ ≤ K / meshSize N * ‖x‖ :=
    fun x => by rw [div_mul_eq_mul_div, le_div_iff₀ hh, mul_comm]; exact hK x
  have hc : Δt * ‖LinearMap.toContinuousLinearMap (discreteWave (whitneyRow N))‖ ≤ c := by
    have := opNorm_discreteWave_le (whitneyRow N) (by positivity) hD
    calc Δt * ‖LinearMap.toContinuousLinearMap (discreteWave (whitneyRow N))‖
        ≤ Δt * (2 * (K / meshSize N)) := mul_le_mul_of_nonneg_left this hΔt.le
      _ = 2 * K * Δt / meshSize N := by ring
      _ ≤ c := by rw [div_le_iff₀ hh]; exact hcfl
  have hA3 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * Δt ≤ T →
      ‖(dEmb (whitneyRow N) (X.interp N ((n + 1 : ℕ) * Δt)) - X.field ((n + 1 : ℕ) * Δt)) -
        (dEmb (whitneyRow N) (X.interp N (n * Δt)) - X.field (n * Δt))‖ ≤
        3 * (rowBound * L * meshSize N) * Δt := by
    intro n hn
    have hn1 : (n : ℝ) * Δt ≤ ((n + 1 : ℕ) : ℝ) * Δt := by push_cast; nlinarith
    have hd : |((n + 1 : ℕ) : ℝ) * Δt - n * Δt| = Δt := by
      rw [show ((n + 1 : ℕ) : ℝ) * Δt - n * Δt = Δt by push_cast; ring, abs_of_pos hΔt]
    have := X.norm_interp_sub_sub_le N (hmem n (hn1.trans hn)) (hmem (n + 1) hn) hL0
    rw [hd] at this
    refine this.trans ?_
    have : 0 ≤ rowBound * L * meshSize N * Δt := mul_nonneg hx0 hΔt.le
    nlinarith
  exact norm_leapfrog_error_le_of_eq (emb := dEmb (whitneyRow N))
    (D := discreteD (whitneyRow N)) (V₀ := whitneyInterior N) (A := discreteWave (whitneyRow N))
    (T := T) (L₃ := rowL2Const * L) (a := 3 * (rowBound * L * meshSize N))
    (w := fun n => X.interp N (n * Δt)) (M := M) (u := u) (g := g) (U := X.field)
    (U₁ := X.field₁) (U₂ := X.field₂) (U₃ := X.field₃)
    (DU := fun t => rowComplex.totalD ⟨X.field t, X.field_mem_totalDomain t⟩)
    (Δt := Δt) (K := leapfrogConst * L) (h := meshSize N) (inner_dEmb (whitneyRow N))
    (fun v hv => discreteD_mem_interior (whitneyRow N) rowComplexMin_d_le
      ((whitneyMin 3 N).window 0 3) hv)
    (fun v _ => discreteD_discreteD (whitneyRow N) v) (inner_discreteWave (whitneyRow N)) hΔt hc
    hc1 X.hasDerivAt_field X.hasDerivAt_field₁ X.hasDerivAt_field₂
    (fun t ht => X.norm_field₃_le ht hL0)
    (fun t _ v hv => (inner_of_mem_graph_waveMax (whitneyRow N) rowComplexMin_d_le
      ((whitneyMin 3 N).window 0 3) (X.mem_graph_waveMax t) hv).choose_spec)
    (fun n hn => (X.norm_interp_sub_le N (hmem n hn) hL0).trans (by linarith))
    (fun n hn => X.norm_d_interp_sub_le N (hmem n hn) hL0)
    hA3 hM hstep hg (hu0.trans (congrArg (X.interp N) (by simp)))
    (hu1.trans (congrArg (X.interp N) (by simp)))
    (by rw [leapfrogConst]; nlinarith [mul_nonneg (mul_nonneg hR hL0) hh.le])
    (by rw [leapfrogConst]; nlinarith [mul_nonneg hR hL0, mul_nonneg hB hL0])

/-- **Stability of the leapfrog Whitney scheme under the CFL condition**: with vanishing boundary
DOFs (`gₙ = 0`, `u₀, u₁ ∈ V̊ₕ`) and `2 K Δt ≤ c h_N`, `0 ≤ c < 1`,
`√(1 − c) ‖uₙ₊₁‖ ≤ √((1 + c) (‖u₀‖² + ‖u₁‖²))` for every step `n`. [Joly2003] -/
theorem whitney_leapfrog_stable (N : ℕ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x : DState (whitneyRow N), meshSize N * ‖discreteD (whitneyRow N) x‖ ≤ K * ‖x‖)
    {Δt c : ℝ} (hΔt : 0 ≤ Δt) (hc1 : c < 1) (hcfl : 2 * K * Δt ≤ c * meshSize N) {n : ℕ}
    {u : ℕ → DState (whitneyRow N)}
    (hstep : ∀ k < n, TimeStepping.IsDirichletLeapfrogStep (whitneyInterior N)
      (discreteWave (whitneyRow N)) Δt 0 (u k) (u (k + 1)) (u (k + 2)))
    (hu0 : u 0 ∈ whitneyInterior N) (hu1 : u 1 ∈ whitneyInterior N) :
    √(1 - c) * ‖u (n + 1)‖ ≤ √((1 + c) * (‖u 0‖ ^ 2 + ‖u 1‖ ^ 2)) := by
  have hh := meshSize_pos N
  have hD : ∀ x : DState (whitneyRow N), ‖discreteD (whitneyRow N) x‖ ≤ K / meshSize N * ‖x‖ :=
    fun x => by rw [div_mul_eq_mul_div, le_div_iff₀ hh, mul_comm]; exact hK x
  have hc : Δt * ‖LinearMap.toContinuousLinearMap (discreteWave (whitneyRow N))‖ ≤ c := by
    have := opNorm_discreteWave_le (whitneyRow N) (by positivity) hD
    calc Δt * ‖LinearMap.toContinuousLinearMap (discreteWave (whitneyRow N))‖
        ≤ Δt * (2 * (K / meshSize N)) := mul_le_mul_of_nonneg_left this hΔt
      _ = 2 * K * Δt / meshSize N := by ring
      _ ≤ c := by rw [div_le_iff₀ hh]; exact hcfl
  have hAs : ∀ x y : DState (whitneyRow N), ⟪discreteWave (whitneyRow N) x, y⟫ =
      -⟪x, discreteWave (whitneyRow N) y⟫ := fun x y => by
    have h1 := inner_discreteWave (whitneyRow N) x y
    have h2 := inner_discreteWave (whitneyRow N) y x
    have c1 := real_inner_comm (discreteWave (whitneyRow N) y) x
    have c2 := real_inner_comm (discreteD (whitneyRow N) y) x
    have c3 := real_inner_comm y (discreteD (whitneyRow N) x)
    linarith
  have h := TimeStepping.norm_succ_sub_le_of_isDirichletLeapfrogStep (V₀ := whitneyInterior N)
    (n := n) (g := fun _ => 0) (u := u) (ũ := fun _ => 0) (ρ := fun _ => 0) hAs hΔt hc hc1
    hstep (fun _ _ => by simp) (by simpa using hu0) (by simpa using hu1)
    (fun _ _ v _ => by simp)
  simpa using h

end WhitneyLeapfrog

end Feec.Models.Cube.Inhomogeneous
