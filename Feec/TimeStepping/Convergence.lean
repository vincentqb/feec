module

public import Feec.TimeStepping.Theta
public import Feec.ForMathlib.LinearPMap.Bounded

/-!
# Convergence of one-step schemes: stability and consistency

Stability plus consistency gives convergence of one-step schemes: on normed spaces, for strongly
continuous semigroups (Lax–Richtmyer), and for bounded generators, with smoothing by time averages.

## Main results

* `norm_sub_le_of_step`: stability plus consistency gives convergence.
* `C0Semigroup.norm_pow_apply_sub_S_le`: the Lax–Richtmyer theorem for semigroups.
* `norm_pow_apply_sub_exp_le_of_norm_exp_le`: the rate `Mₛ K M t τᵖ` for bounded generators.
* `thetaStep_mem_of_mapsTo`: for dissipative `L`, `re θ > 0` and `τ > 0`, `r_θ(τ L)` keeps closed
  `L`-invariant subspaces.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7, Ch. 9
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 4.18

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Feec.Operator NormedSpace Finset

@[expose] public noncomputable section

namespace Feec.TimeStepping

/-! ### Stability plus consistency: the discrete Duhamel formula -/

section Duhamel

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {P : X →L[𝕜] X} {U g w : ℕ → X}

theorem sub_eq_sum_of_step (hU : ∀ k, U (k + 1) = P (U k) + g k) (n : ℕ) :
    U n - w n = (P ^ n) (U 0 - w 0) +
      ∑ j ∈ range n, (P ^ j) (P (w (n - 1 - j)) + g (n - 1 - j) - w (n - j)) := by
  have hm : ∀ (Q : X →L[𝕜] X) (x : X), (P * Q) x = P (Q x) := fun _ _ => rfl
  induction n with
  | zero => simp
  | succ n ih =>
    have hidx : ∀ j ∈ range n,
        (P ^ (j + 1)) (P (w (n + 1 - 1 - (j + 1))) + g (n + 1 - 1 - (j + 1)) - w (n + 1 - (j + 1)))
          = P ((P ^ j) (P (w (n - 1 - j)) + g (n - 1 - j) - w (n - j))) := by
      intro j _
      rw [show n + 1 - 1 - (j + 1) = n - 1 - j by omega, show n + 1 - (j + 1) = n - j by omega,
        pow_succ', hm]
    rw [sum_range_succ', sum_congr rfl hidx, ← map_sum, hU n, pow_succ', hm]
    simp only [pow_zero, Nat.sub_zero, add_tsub_cancel_right, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_apply]
    rw [← add_assoc, ← _root_.map_add, ← ih, _root_.map_sub]
    abel

/-- **Stability plus consistency gives convergence**: if `Uₖ₊₁ = P Uₖ + gₖ` and `‖Pᵏ‖ ≤ M` for
`k ≤ n`, then for all `wₖ`, `‖Uₙ - wₙ‖ ≤ M (‖U₀ - w₀‖ + Σ_{k<n} ‖wₖ₊₁ - P wₖ - gₖ‖)`.
[Thomee2006], Ch. 7 -/
theorem norm_sub_le_of_step {M : ℝ} {n : ℕ} (hP : ∀ k ≤ n, ‖P ^ k‖ ≤ M)
    (hU : ∀ k, U (k + 1) = P (U k) + g k) :
    ‖U n - w n‖ ≤ M * (‖U 0 - w 0‖ + ∑ k ∈ range n, ‖w (k + 1) - P (w k) - g k‖) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hP 0 (Nat.zero_le _))
  rw [sub_eq_sum_of_step hU n, mul_add, mul_sum]
  refine (norm_add_le _ _).trans (add_le_add ((P ^ n).le_of_opNorm_le (hP n le_rfl) _) ?_)
  refine (norm_sum_le _ _).trans ?_
  rw [← sum_range_reflect (fun k => M * ‖w (k + 1) - P (w k) - g k‖) n]
  refine sum_le_sum fun j hj => ?_
  have hj' : j < n := mem_range.1 hj
  rw [show n - 1 - j + 1 = n - j by omega]
  have e : ‖w (n - j) - P (w (n - 1 - j)) - g (n - 1 - j)‖ =
      ‖P (w (n - 1 - j)) + g (n - 1 - j) - w (n - j)‖ := by
    rw [← norm_neg]; congr 1; abel
  rw [e]
  exact (P ^ j).le_of_opNorm_le (hP j hj'.le) _

theorem norm_pow_le_pow {P : X →L[𝕜] X} {a : ℝ} (hP : ‖P‖ ≤ a) (k : ℕ) : ‖P ^ k‖ ≤ a ^ k := by
  induction k with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih hP (norm_nonneg _) ((norm_nonneg _).trans ih))

theorem norm_pow_le_one {P : X →L[𝕜] X} (hP : ‖P‖ ≤ 1) (n : ℕ) : ‖P ^ n‖ ≤ 1 := by
  simpa using norm_pow_le_pow hP n

end Duhamel

end Feec.TimeStepping

/-! ### Semigroups: Taylor's formula and the Lax–Richtmyer theorem -/

namespace Feec.C0Semigroup

open Set (Icc Ico Ici)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E)

theorem norm_S_sub_taylor_le {T M : ℝ} (hM : ∀ t ∈ Icc 0 T, ‖G.S t‖ ≤ M) (p : ℕ) :
    ∀ {u : ℕ → E}, (∀ j < p, (u j, u (j + 1)) ∈ G.generator.graph) → ∀ {t : ℝ}, t ∈ Icc 0 T →
      ‖G.S t (u 0) - ∑ j ∈ range p, (t ^ j / j.factorial) • u j‖ ≤
        M * (t ^ p / p.factorial) * ‖u p‖ := by
  induction p with
  | zero =>
    intro u _ t ht
    simpa using (G.S t).le_of_opNorm_le (hM t ht) (u 0)
  | succ p ih =>
    intro u hu t ht
    set F : ℝ → E := fun s => G.S s (u 0) - ∑ j ∈ range (p + 1), (s ^ j / j.factorial) • u j
    set F' : ℝ → E := fun s => G.S s (u 1) - ∑ j ∈ range p, (s ^ j / j.factorial) • u (j + 1)
    have hF : ∀ s, F s = G.S s (u 0) - u 0 -
        ∑ j ∈ range p, (s ^ (j + 1) / (j + 1).factorial) • u (j + 1) := fun s => by
      simp only [F, sum_range_succ', pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
        one_smul]
      abel
    obtain ⟨hx, hAx⟩ := LinearPMap.mem_graph_iff_exists.1 (hu 0 (Nat.succ_pos p))
    have hsum : ∀ s : ℝ, HasDerivAt
        (fun s : ℝ => ∑ j ∈ range p, (s ^ (j + 1) / (j + 1).factorial) • u (j + 1))
        (∑ j ∈ range p, (s ^ j / j.factorial) • u (j + 1)) s := fun s => by
      have := HasDerivAt.sum (u := range p) (x := s)
        (A := fun j (s : ℝ) => (s ^ (j + 1) / (j + 1).factorial) • u (j + 1))
        (A' := fun j => (s ^ j / j.factorial) • u (j + 1)) fun j _ => by
          have h := ((hasDerivAt_pow (j + 1) s).div_const ((j + 1).factorial : ℝ)).smul_const
            (u (j + 1))
          convert h using 2
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
          have : (j.factorial : ℝ) ≠ 0 := by positivity
          field_simp
      convert this using 1
      ext s'; simp
    have hd : ∀ s ∈ Ico 0 t, HasDerivWithinAt F (F' s) (Ici s) s := fun s hs => by
      have h1 := G.hasDerivWithinAt_Ici_apply ⟨u 0, hx⟩ hs.1
      rw [hAx] at h1
      exact ((h1.sub_const (u 0)).sub (hsum s).hasDerivWithinAt).congr (fun y _ => hF y) (hF s)
    have hc : ContinuousOn F (Icc 0 t) := by
      rw [show F = fun s : ℝ => G.S s (u 0) - u 0 -
        ∑ j ∈ range p, (s ^ (j + 1) / (j + 1).factorial) • u (j + 1) from funext hF]
      exact (((G.strongCont (u 0)).mono Set.Icc_subset_Ici_self).sub continuousOn_const).sub
        (continuous_iff_continuousAt.2 fun s => (hsum s).continuousAt).continuousOn
    have hB : ∀ s, HasDerivAt (fun s : ℝ => M * (s ^ (p + 1) / (p + 1).factorial) * ‖u (p + 1)‖)
        (M * (s ^ p / p.factorial) * ‖u (p + 1)‖) s := fun s => by
      have h := (((hasDerivAt_pow (p + 1) s).div_const ((p + 1).factorial : ℝ)).const_mul
        M).mul_const ‖u (p + 1)‖
      convert h using 1
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
      have : (p.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary hc hd (by simp [F, sum_range_succ'])
      hB (fun s hs => ?_) ⟨ht.1, le_rfl⟩
    exact ih (u := fun j => u (j + 1)) (fun j hj => hu (j + 1) (by omega))
      ⟨hs.1, hs.2.le.trans ht.2⟩

/-- **Lax–Richtmyer for semigroups** ([Thomee2006], Ch. 9; [BrennerThomee1979]): stability `Mₛ`,
`‖S(t)‖ ≤ M` on `[0, nτ]` and consistency of order `p` with constant `K` give
`‖Pⁿ u₀ - S(nτ) u₀‖ ≤ Mₛ K M nτ τᵖ ‖u_{p+1}‖`. -/
theorem norm_pow_apply_sub_S_le {P : E →L[𝕜] E} {n : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) {Ms M K : ℝ}
    {p : ℕ} (hK : 0 ≤ K) (hP : ∀ k ≤ n, ‖P ^ k‖ ≤ Ms) (hS : ∀ t ∈ Icc 0 (n * τ), ‖G.S t‖ ≤ M)
    (hc : ∀ v : ℕ → E, (∀ j < p + 1, (v j, v (j + 1)) ∈ G.generator.graph) →
      ‖P (v 0) - G.S τ (v 0)‖ ≤ K * τ ^ (p + 1) * ‖v (p + 1)‖)
    {u : ℕ → E} (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖(P ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤ Ms * K * M * (n * τ) * τ ^ p * ‖u (p + 1)‖ := by
  have hMs : 0 ≤ Ms := (norm_nonneg _).trans (hP 0 (Nat.zero_le _))
  set w : ℕ → E := fun k => G.S (k * τ) (u 0)
  have h := TimeStepping.norm_sub_le_of_step (U := fun k => (P ^ k) (u 0)) (g := fun _ => 0)
    (w := w) hP (fun k => by simp [pow_succ'])
  have hw0 : (P ^ 0) (u 0) - w 0 = 0 := by simp [w]
  have hdef : ∀ k ∈ range n, ‖w (k + 1) - P (w k) - 0‖ ≤ K * τ ^ (p + 1) * (M * ‖u (p + 1)‖) := by
    intro k hk
    have hk' : (k : ℝ) < n := by exact_mod_cast mem_range.1 hk
    have hkτ : 0 ≤ (k : ℝ) * τ := by positivity
    have hkn : (k : ℝ) * τ ∈ Icc 0 (n * τ) :=
      ⟨hkτ, mul_le_mul_of_nonneg_right hk'.le hτ⟩
    have e1 : w (k + 1) = G.S τ (w k) := by
      simp only [w]
      rw [show (((k + 1 : ℕ) : ℝ) * τ) = τ + k * τ by push_cast; ring,
        G.S_add_apply hτ hkτ]
    rw [sub_zero, e1, norm_sub_rev]
    refine (hc (fun j => G.S (k * τ) (u j)) fun j hj => G.S_mem_graph (hu j hj) hkτ).trans ?_
    have hn : ‖G.S (k * τ) (u (p + 1))‖ ≤ M * ‖u (p + 1)‖ :=
      (G.S _).le_of_opNorm_le (hS _ hkn) _
    exact mul_le_mul_of_nonneg_left hn (by positivity)
  refine h.trans ?_
  rw [hw0, norm_zero, zero_add]
  calc Ms * ∑ k ∈ range n, ‖w (k + 1) - P (w k) - 0‖
      ≤ Ms * ∑ _k ∈ range n, K * τ ^ (p + 1) * (M * ‖u (p + 1)‖) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hdef) hMs
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; ring

end Feec.C0Semigroup

namespace Feec.TimeStepping

/-! ### Consistency and smoothing on Banach spaces -/

section Normed

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] {L : X →L[𝕜] X}

/-- `P` is consistent of order `p` with constant `K`: `‖P y - e^{τL} y‖ ≤ K τ^{p+1} ‖L^{p+1} y‖`. -/
def IsConsistent (L P : X →L[𝕜] X) (τ : ℝ) (p : ℕ) (K : ℝ) : Prop :=
  ∀ y, ‖P y - exp ((τ : 𝕜) • L) y‖ ≤ K * τ ^ (p + 1) * ‖(L ^ (p + 1)) y‖

variable [CompleteSpace X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

/-- **The rate on a Banach space** ([BrennerThomee1979]; [Thomee2006], Ch. 7): for `‖e^{tL}‖ ≤ M`
and `τ ≥ 0`, stability `Mₛ` and consistency `(p, K)` give
`‖Pⁿ y - e^{nτL} y‖ ≤ Mₛ K M (n τ) τᵖ ‖L^{p+1} y‖`. -/
theorem norm_pow_apply_sub_exp_le_of_norm_exp_le {M : ℝ}
    (hL : ∀ t : ℝ, 0 ≤ t → ‖exp ((t : 𝕜) • L)‖ ≤ M) {P : X →L[𝕜] X} {Ms : ℝ} {n : ℕ}
    (hP : ∀ k ≤ n, ‖P ^ k‖ ≤ Ms) {τ : ℝ} (hτ : 0 ≤ τ) {p : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hc : IsConsistent L P τ p K) (y : X) :
    ‖(P ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤
      Ms * K * M * (n * τ) * τ ^ p * ‖(L ^ (p + 1)) y‖ := by
  have h := (C0Group.ofBounded L).toC0Semigroup.norm_pow_apply_sub_S_le hτ hK hP
    (fun t ht => hL t ht.1) (fun v hv => by
      rw [C0Group.eq_pow_apply_of_chain hv (p + 1) le_rfl]
      exact hc (v 0))
    (u := fun j => (L ^ j) y) (fun j _ => C0Group.pow_apply_mem_graph_generator_ofBounded L y j)
  simpa using h

/-! #### Smoothing by time averages -/

/-- The **time average** `A_δ y = δ⁻¹ ∫₀^δ e^{sL} y ds`. -/
def timeAvg (L : X →L[𝕜] X) (δ : ℝ) (y : X) : X :=
  δ⁻¹ • ∫ s in (0 : ℝ)..δ, exp ((s : 𝕜) • L) y

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
theorem continuous_exp_apply (L : X →L[𝕜] X) (y : X) :
    Continuous fun s : ℝ => exp ((s : 𝕜) • L) y :=
  (ContinuousLinearMap.continuous_exp_ofReal_smul L).clm_apply continuous_const

omit [IsScalarTower ℝ 𝕜 X] in
theorem timeAvg_sub (L : X →L[𝕜] X) (δ : ℝ) (y z : X) :
    timeAvg L δ (y - z) = timeAvg L δ y - timeAvg L δ z := by
  unfold timeAvg
  simp only [_root_.map_sub]
  rw [intervalIntegral.integral_sub ((continuous_exp_apply L y).intervalIntegrable _ _)
    ((continuous_exp_apply L z).intervalIntegrable _ _), smul_sub]

theorem apply_timeAvg (L : X →L[𝕜] X) (δ : ℝ) (y : X) :
    L (timeAvg L δ y) = timeAvg L δ (L y) := by
  unfold timeAvg
  rw [L.map_smul_of_tower, ← ContinuousLinearMap.intervalIntegral_comp_comm L
    ((continuous_exp_apply L y).intervalIntegrable _ _)]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  exact congrArg (fun C : X →L[𝕜] X => C y) (ContinuousLinearMap.commute_exp_ofReal_smul L s).eq

theorem apply_timeAvg_eq (L : X →L[𝕜] X) (δ : ℝ) (y : X) :
    L (timeAvg L δ y) = δ⁻¹ • (exp ((δ : 𝕜) • L) y - y) := by
  unfold timeAvg
  rw [L.map_smul_of_tower, ← ContinuousLinearMap.intervalIntegral_comp_comm L
    ((continuous_exp_apply L y).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => ContinuousLinearMap.hasDerivAt_exp_ofReal_smul_apply L y s)
      ((L.continuous.comp (continuous_exp_apply L y)).intervalIntegrable _ _)]
  simp

omit [IsScalarTower ℝ 𝕜 X] in
theorem norm_timeAvg_sub_le {δ η : ℝ} (hδ : 0 < δ) {y : X}
    (h : ∀ s ∈ Set.Icc 0 δ, ‖exp ((s : 𝕜) • L) y - y‖ ≤ η) : ‖timeAvg L δ y - y‖ ≤ η := by
  have e : timeAvg L δ y - y = δ⁻¹ • ∫ s in (0 : ℝ)..δ, (exp ((s : 𝕜) • L) y - y) := by
    unfold timeAvg
    rw [intervalIntegral.integral_sub ((continuous_exp_apply L y).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const, smul_sub, smul_smul,
      sub_zero, inv_mul_cancel₀ hδ.ne', one_smul]
  rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ)
    (f := fun s : ℝ => exp ((s : 𝕜) • L) y - y) (C := η) fun s hs => by
      rw [Set.uIoc_of_le hδ.le] at hs
      exact h s ⟨hs.1.le, hs.2⟩
  rw [sub_zero, abs_of_pos hδ] at h2
  calc δ⁻¹ * ‖∫ s in (0 : ℝ)..δ, (exp ((s : 𝕜) • L) y - y)‖ ≤ δ⁻¹ * (η * δ) := by gcongr
    _ = η := by field_simp

omit [CompleteSpace X] [IsScalarTower ℝ 𝕜 X] in
theorem norm_timeAvg_le_of_norm_exp_le {M δ : ℝ}
    (hL : ∀ s ∈ Set.Icc 0 δ, ‖exp ((s : 𝕜) • L)‖ ≤ M) (hδ : 0 < δ) (y : X) :
    ‖timeAvg L δ y‖ ≤ M * ‖y‖ := by
  unfold timeAvg
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ)
    (f := fun s : ℝ => exp ((s : 𝕜) • L) y) (C := M * ‖y‖) fun s hs => by
      rw [Set.uIoc_of_le hδ.le] at hs
      exact (exp ((s : 𝕜) • L)).le_of_opNorm_le (hL s ⟨hs.1.le, hs.2⟩) y
  rw [sub_zero, abs_of_pos hδ] at h
  calc δ⁻¹ * ‖∫ s in (0 : ℝ)..δ, exp ((s : 𝕜) • L) y‖ ≤ δ⁻¹ * (M * ‖y‖ * δ) := by gcongr
    _ = M * ‖y‖ := by field_simp

theorem norm_apply_timeAvg_le_of_norm_exp_le {M δ : ℝ} (hL : ‖exp ((δ : 𝕜) • L)‖ ≤ M)
    (hδ : 0 < δ) (y : X) : ‖L (timeAvg L δ y)‖ ≤ (M + 1) / δ * ‖y‖ := by
  rw [apply_timeAvg_eq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
  have h1 := norm_sub_le (exp ((δ : 𝕜) • L) y) y
  have h2 := (exp ((δ : 𝕜) • L)).le_of_opNorm_le hL y
  calc δ⁻¹ * ‖exp ((δ : 𝕜) • L) y - y‖ ≤ δ⁻¹ * ((M + 1) * ‖y‖) := by gcongr; linarith
    _ = _ := by ring

theorem norm_pow_timeAvg_iterate_le_of_norm_exp_le {M δ : ℝ} (hL : ‖exp ((δ : 𝕜) • L)‖ ≤ M)
    (hδ : 0 < δ) (k : ℕ) (y : X) :
    ‖(L ^ k) ((timeAvg L δ)^[k] y)‖ ≤ ((M + 1) / δ) ^ k * ‖y‖ := by
  have hcomm : ∀ j (u : X), L ((timeAvg L δ)^[j] u) = (timeAvg L δ)^[j] (L u) := by
    intro j
    induction j with
    | zero => intro u; rfl
    | succ j ih => intro u; rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
        apply_timeAvg]
  have hM : 0 ≤ (M + 1) / δ := by
    have := (norm_nonneg _).trans hL
    positivity
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    change ‖(L ^ k) (L _)‖ ≤ ((M + 1) / δ) ^ (k + 1) * ‖y‖
    rw [hcomm, pow_succ ((M + 1) / δ)]
    refine (ih _).trans ?_
    calc ((M + 1) / δ) ^ k * ‖L (timeAvg L δ y)‖ ≤ ((M + 1) / δ) ^ k * ((M + 1) / δ * ‖y‖) := by
          gcongr; exact norm_apply_timeAvg_le_of_norm_exp_le hL hδ y
      _ = _ := by ring

omit [IsScalarTower ℝ 𝕜 X] in
theorem norm_timeAvg_iterate_sub_le_of_norm_exp_le {M δ : ℝ}
    (hL : ∀ s ∈ Set.Icc 0 δ, ‖exp ((s : 𝕜) • L)‖ ≤ M) (hδ : 0 < δ) (k : ℕ) (y : X) :
    ‖(timeAvg L δ)^[k] y - y‖ ≤ (∑ j ∈ range k, M ^ j) * ‖timeAvg L δ y - y‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hL 0 ⟨le_rfl, hδ.le⟩)
  have hsub : ∀ j (a b : X), (timeAvg L δ)^[j] a - (timeAvg L δ)^[j] b =
      (timeAvg L δ)^[j] (a - b) := by
    intro j
    induction j with
    | zero => intro a b; rfl
    | succ j ih => intro a b; rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, ih, timeAvg_sub]
  have hnorm : ∀ j (a : X), ‖(timeAvg L δ)^[j] a‖ ≤ M ^ j * ‖a‖ := by
    intro j
    induction j with
    | zero => intro a; simp
    | succ j ih =>
      intro a
      rw [Function.iterate_succ_apply]
      refine (ih _).trans ?_
      calc M ^ j * ‖timeAvg L δ a‖ ≤ M ^ j * (M * ‖a‖) := by
            gcongr; exact norm_timeAvg_le_of_norm_exp_le hL hδ a
        _ = _ := by ring
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    calc ‖(timeAvg L δ)^[k] (timeAvg L δ y) - y‖ ≤
        ‖(timeAvg L δ)^[k] (timeAvg L δ y) - (timeAvg L δ)^[k] y‖ +
          ‖(timeAvg L δ)^[k] y - y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ M ^ k * ‖timeAvg L δ y - y‖ + (∑ j ∈ range k, M ^ j) * ‖timeAvg L δ y - y‖ := by
        gcongr
        rw [hsub]; exact hnorm _ _
      _ = _ := by rw [sum_range_succ]; ring

end Normed

/-! ### Bounded dissipative generators: Taylor remainders and consistency -/

section Bounded

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [CompleteSpace X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] {L : X →L[𝕜] X}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem norm_exp_le_one (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖(C0Group.ofBounded L).S t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using LumerPhillips.norm_exp_smul_apply_le hL ht x

theorem re_inner_le_zero_of_norm_exp_le_one
    (hL : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L)‖ ≤ 1) (x : X) :
    RCLike.re ⟪L x, x⟫ ≤ 0 := by
  have h := C0Semigroup.IsContraction.isDissipative_generator
    (G := (C0Group.ofBounded L).toC0Semigroup) (fun t ht => by simpa using hL t ht)
    ⟨x, C0Group.mem_domain_generator_ofBounded L x⟩
  have e : (C0Group.ofBounded L).toC0Semigroup.generator
      ⟨x, C0Group.mem_domain_generator_ofBounded L x⟩ = L x :=
    C0Group.generator_ofBounded_apply L ⟨x, C0Group.mem_domain_generator_ofBounded L x⟩
  rwa [e] at h

theorem norm_exp_sub_taylor_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) (p : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (y : X) :
    ‖exp ((t : 𝕜) • L) y - ∑ j ∈ range p, (t ^ j / j.factorial) • (L ^ j) y‖ ≤
      t ^ p / p.factorial * ‖(L ^ p) y‖ := by
  have h := (C0Group.ofBounded L).toC0Semigroup.norm_S_sub_taylor_le (T := t)
    (fun s hs => norm_exp_le_one hL hs.1) p (u := fun j => (L ^ j) y)
    (fun j _ => C0Group.pow_apply_mem_graph_generator_ofBounded L y j) ⟨ht, le_rfl⟩
  simpa using h

theorem isConsistent_of_eq (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {P ρ : X →L[𝕜] X} {τ : ℝ}
    (hτ : 0 ≤ τ) {p : ℕ} {K₀ : ℝ} (hρ : ‖ρ‖ ≤ K₀)
    (hP : ∀ y, P y = ∑ j ∈ range (p + 1), (τ ^ j / j.factorial) • (L ^ j) y +
      τ ^ (p + 1) • ρ ((L ^ (p + 1)) y)) :
    IsConsistent L P τ p (K₀ + 1 / (p + 1).factorial) := by
  intro y
  have h1 := norm_exp_sub_taylor_le hL (p + 1) hτ y
  have h2 : ‖τ ^ (p + 1) • ρ ((L ^ (p + 1)) y)‖ ≤ τ ^ (p + 1) * (K₀ * ‖(L ^ (p + 1)) y‖) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    gcongr
    exact ρ.le_of_opNorm_le hρ _
  have e : P y - exp ((τ : 𝕜) • L) y = τ ^ (p + 1) • ρ ((L ^ (p + 1)) y) -
      (exp ((τ : 𝕜) • L) y - ∑ j ∈ range (p + 1), (τ ^ j / j.factorial) • (L ^ j) y) := by
    rw [hP]; abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_sub_rev] at h1
  calc _ ≤ τ ^ (p + 1) * (K₀ * ‖(L ^ (p + 1)) y‖) +
        τ ^ (p + 1) / (p + 1).factorial * ‖(L ^ (p + 1)) y‖ := add_le_add h2 (by
          rwa [norm_sub_rev] at h1)
    _ = _ := by ring

theorem norm_pow_apply_sub_exp_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {P : X →L[𝕜] X} {M : ℝ}
    {n : ℕ} (hP : ∀ k ≤ n, ‖P ^ k‖ ≤ M) {τ : ℝ} (hτ : 0 ≤ τ) {p : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hc : IsConsistent L P τ p K) (y : X) :
    ‖(P ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤ M * K * (n * τ) * τ ^ p * ‖(L ^ (p + 1)) y‖ := by
  simpa using norm_pow_apply_sub_exp_le_of_norm_exp_le (fun t ht => norm_exp_le_one hL ht) hP hτ
    hK hc y

/-! ### θ-schemes of bounded dissipative operators -/

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
theorem _root_.ContinuousLinearMap.isMDissipative_toPMap_top (L : X →L[𝕜] X)
    (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) : ((L : X →ₗ[𝕜] X).toPMap ⊤).IsMDissipative := by
  refine IsDissipative.isMDissipative_of_adjoint (fun x => hL x) ?_ L.isClosed_toPMap_top ?_
  · simp [dense_univ]
  · rw [L.adjoint_toPMap_top]
    intro x
    change RCLike.re ⟪ContinuousLinearMap.adjoint L x, (x : X)⟫ ≤ 0
    rw [ContinuousLinearMap.adjoint_inner_left, inner_re_symm]
    exact hL x

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
theorem norm_thetaStep_pow_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {θ : 𝕜}
    (hθ : 1 / 2 ≤ RCLike.re θ) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) :
    ‖thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ ^ n‖ ≤ 1 :=
  norm_pow_le_one (norm_thetaStep_le (L.isMDissipative_toPMap_top hL) hθ hτ) n

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
/-- **Discrete constraint propagation for closed invariant subspaces**: if `L K ⊆ K` for a closed
`K` and dissipative `L`, then `r_θ(τ L) K ⊆ K` (`re θ > 0`, `τ > 0`).
[QuennevilleBelair2015], Prop 4.18 (adapted) -/
theorem thetaStep_mem_of_mapsTo (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {K : Submodule 𝕜 X}
    (hKc : IsClosed (K : Set X)) (hLK : ∀ x ∈ K, L x ∈ K) {θ : 𝕜} (hθ : 0 < RCLike.re θ)
    {τ : ℝ} (hτ : 0 < τ) {u : X} (hu : u ∈ K) :
    thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ u ∈ K := by
  have : CompleteSpace K := hKc.completeSpace_coe
  set LK : K →L[𝕜] K := (L.comp K.subtypeL).codRestrict K fun x => hLK x x.2
  have hLK' : ∀ x : K, RCLike.re ⟪LK x, x⟫ ≤ 0 := fun x => by
    rw [Submodule.coe_inner]; exact hL x
  have hz := re_inv_mul_pos hθ hτ
  have hRK := (LK.isMDissipative_toPMap_top hLK').isResolvent_of_re_pos hz
  have hR := (L.isMDissipative_toPMap_top hL).isResolvent_of_re_pos hz
  refine thetaStep_mem (fun y hy => ?_) hu
  set x : K := resolvent ((LK : K →ₗ[𝕜] K).toPMap ⊤) (θ * (τ : 𝕜))⁻¹ ⟨y, hy⟩
  have hx : (θ * (τ : 𝕜))⁻¹ • (x : X) - L x = y := congrArg Subtype.val (hRK.sub_apply ⟨y, hy⟩)
  have h2 : resolvent ((L : X →ₗ[𝕜] X).toPMap ⊤) (θ * (τ : 𝕜))⁻¹
      ((θ * (τ : 𝕜))⁻¹ • (x : X) - L x) = x := hR.apply_sub ⟨(x : X), trivial⟩
  rw [hx] at h2
  rw [h2]
  exact x.2

end Bounded

end Feec.TimeStepping
