module

public import Feec.TimeStepping.Theta
public import Feec.ForMathlib.LinearPMap.Bounded

/-!
# Convergence of one-step schemes: stability and consistency

A one-step scheme `uₙ₊₁ = P uₙ + gₙ` for `u' = L u + f` converges when it is **stable**
(`‖Pᵏ‖ ≤ M`) and **consistent** with the exact flow: the classical "stability plus consistency
implies convergence" ([Thomee2006], Ch. 7; [BrennerThomee1979]). This file proves it in two
layers.

* **Any normed space, any comparison sequence** (`sub_eq_sum_of_step`, the discrete Duhamel
  formula, and `norm_sub_le_of_step`): for `Uₖ₊₁ = P Uₖ + gₖ` and any `wₖ`,
  `‖Uₙ - wₙ‖ ≤ M (‖U₀ - w₀‖ + Σₖ<ₙ ‖wₖ₊₁ - P wₖ - gₖ‖)`: the error is at most the initial error
  plus the accumulated consistency defects. This is the discrete counterpart of
  `Feec.HilbertComplex.norm_sub_le_of_defect_of_dissipative` ("best approximation plus
  consistency"), and the operator form of `TimeStepping.norm_sub_le_sum_of_isDirichletCNStep`.
* **Strongly continuous semigroups on Banach spaces** (`C0Semigroup.norm_S_sub_taylor_le`,
  Taylor's formula `‖S(t) x - Σ_{j<p} tʲ/j! Aʲ x‖ ≤ M tᵖ/p! ‖Aᵖ x‖` on `D(Aᵖ)` for `‖S‖ ≤ M`,
  and **`C0Semigroup.norm_pow_apply_sub_S_le`**, Lax–Richtmyer: `‖Pᵏ‖ ≤ Mₛ` and consistency of
  order `p` on `D(A^{p+1})` give `‖Pⁿ x - S(nτ) x‖ ≤ Mₛ K M nτ τᵖ ‖A^{p+1} x‖`). The bounded
  case is `S(t) = e^{tL}`: a scheme `P` is **consistent of order `p` with constant `K`**
  (`IsConsistent`) if `‖P y - e^{τL} y‖ ≤ K τ^{p+1} ‖L^{p+1} y‖`, and for `‖e^{tL}‖ ≤ M`,
  `‖Pⁿ y - e^{nτL} y‖ ≤ Mₛ K M (n τ) τᵖ ‖L^{p+1} y‖`
  (`norm_pow_apply_sub_exp_le_of_norm_exp_le`), on every Banach space.
* **Bounded dissipative generators** (`re ⟪L x, x⟫ ≤ 0`, so `e^{tL}` is a contraction for `t ≥ 0`):
  the Taylor remainder `‖e^{tL} y - Σ_{j<p} tʲ/j! Lʲ y‖ ≤ tᵖ/p! ‖Lᵖ y‖`
  (`norm_exp_sub_taylor_le`); consistency of order `p` follows from an expansion
  `P = Σ_{j≤p} τʲ/j! Lʲ + τ^{p+1} ρ L^{p+1}` with `‖ρ‖ ≤ K₀` (`isConsistent_of_eq`,
  `K = K₀ + 1/(p+1)!`);
  and **`norm_pow_apply_sub_exp_le`**: stability and consistency of order `p` give the global error
  `‖Pⁿ y - e^{nτL} y‖ ≤ M K (n τ) τᵖ ‖L^{p+1} y‖` (the Banach-space bound at `‖e^{tL}‖ ≤ 1`).
  All constants are independent of `L`: on finite element spaces they are uniform in the mesh.

## θ-schemes for bounded generators

`ContinuousLinearMap.isMDissipative_toPMap_top`: a bounded dissipative operator on a Hilbert space
is m-dissipative, so `Feec.TimeStepping.thetaStep` applies to it. For real `θ > 0` and `τ > 0`,
`r_θ(τ L) = 1 + τ L + θ τ² W L²` with `W = (1 - θ τ L)⁻¹`, `‖W‖ ≤ 1`
(`exists_thetaStep_apply_eq`); for
`θ = 1/2`, `r_{1/2}(τ L) = 1 + τ L + τ²/2 L² + τ³/4 W L³` (`exists_thetaStep_half_apply_eq`). Hence
(`isConsistent_thetaStep`, `isConsistent_thetaStep_half`) the θ-scheme is consistent of order `1`
with `K = θ + 1/2`, and Crank–Nicolson of order `2` with `K = 5/12`, and:

* **`norm_implicitEuler_pow_sub_exp_le`**: implicit Euler,
  `‖(1 - τ L)⁻ⁿ y - e^{tL} y‖ ≤ 3/2 t τ ‖L² y‖`;
* **`norm_cayley_pow_sub_exp_le`**: Crank–Nicolson (`cayley`),
  `‖cayley(L, τ/2)ⁿ y - e^{tL} y‖ ≤ 5/12 t τ² ‖L³ y‖`;
* `norm_thetaStep_pow_sub_exp_le`: the θ-scheme, `re θ ≥ 1/2`, `‖·‖ ≤ (θ + 1/2) t τ ‖L² y‖`;

at `t = n τ`, for every bounded dissipative `L`, the rate of [BrennerThomee1979] (smooth data).
`thetaStep_mem_of_mapsTo`: a closed subspace `K` with `L K ⊆ K` is kept by the θ-scheme (discrete
constraint propagation, for instance for a discrete Gauss law).

The constants come from bounding the two remainders separately and are not sharp: the leading
error constant of Crank–Nicolson is `1/12` (`e^z - r_{1/2}(z) = -z³/12 + O(z⁴)`), not `5/12`.

**Smoothing** (`timeAvg`, `norm_pow_timeAvg_iterate_le_of_norm_exp_le`,
`norm_timeAvg_iterate_sub_le_of_norm_exp_le`): on a Banach space with `‖e^{sL}‖ ≤ M`, the time
average `A_δ y = δ⁻¹ ∫₀^δ e^{sL} y ds` satisfies `‖Lᵏ A_δᵏ y‖ ≤ ((M + 1)/δ)ᵏ ‖y‖` and
`‖A_δᵏ y - y‖ ≤ (Σ_{j<k} Mʲ) sup_{s ≤ δ} ‖e^{sL} y - y‖`, uniformly in `L` (for dissipative `L`,
`M = 1`: `(2/δ)ᵏ` and `k`, `norm_pow_timeAvg_iterate_le`, `norm_timeAvg_iterate_sub_le`); it
turns the rate for smooth data into convergence for all data (downstream:
`Feec.TimeStepping.BanachFEEC.TimeScheme.converges`, and through it
`Feec.HilbertComplex.DissipFEEC.TimeScheme.converges`).

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
  (order `p` rational schemes: `O(t τᵖ ‖A^{p+1} x‖)`)
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7
  (single step methods: stability and consistency), Ch. 8–9
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.2 (the orbit calculus behind Taylor's formula)
* [R. Hersh, T. Kato, *High-Accuracy Stable Difference Schemes for Well-Posed Initial-Value Problems*][HershKato1979]
  (stability and accuracy of rational approximations of semigroups)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 4.18 (constraint propagation, here at the discrete level)

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

/-- **The discrete Duhamel formula**: for `Uₖ₊₁ = P Uₖ + gₖ` and any comparison sequence `wₖ`,
`Uₙ - wₙ = Pⁿ (U₀ - w₀) + Σ_{j<n} Pʲ dₙ₋₁₋ⱼ` with the defects `dₖ = P wₖ + gₖ - wₖ₊₁`. -/
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

/-- **Stability plus consistency gives convergence**: if `‖Pᵏ‖ ≤ M` for `k ≤ n` and
`Uₖ₊₁ = P Uₖ + gₖ`, then for every comparison sequence `wₖ`,
`‖Uₙ - wₙ‖ ≤ M (‖U₀ - w₀‖ + Σ_{k<n} ‖wₖ₊₁ - P wₖ - gₖ‖)`. [Thomee2006], Ch. 7 -/
theorem norm_sub_le_of_step {M : ℝ} {n : ℕ} (hP : ∀ k ≤ n, ‖P ^ k‖ ≤ M)
    (hU : ∀ k, U (k + 1) = P (U k) + g k) :
    ‖U n - w n‖ ≤ M * (‖U 0 - w 0‖ + ∑ k ∈ range n, ‖w (k + 1) - P (w k) - g k‖) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hP 0 (Nat.zero_le _))
  rw [sub_eq_sum_of_step hU n, mul_add, mul_sum]
  refine (norm_add_le _ _).trans (add_le_add (((P ^ n).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hP n le_rfl) (norm_nonneg _))) ?_)
  refine (norm_sum_le _ _).trans ?_
  rw [← sum_range_reflect (fun k => M * ‖w (k + 1) - P (w k) - g k‖) n]
  refine sum_le_sum fun j hj => ?_
  have hj' : j < n := mem_range.1 hj
  rw [show n - 1 - j + 1 = n - j by omega]
  have e : ‖w (n - j) - P (w (n - 1 - j)) - g (n - 1 - j)‖ =
      ‖P (w (n - 1 - j)) + g (n - 1 - j) - w (n - j)‖ := by
    rw [← norm_neg]; congr 1; abel
  rw [e]
  exact ((P ^ j).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hP j hj'.le) (norm_nonneg _))

/-- `‖Pᵏ‖ ≤ aᵏ` for `‖P‖ ≤ a`. -/
theorem norm_pow_le_pow {P : X →L[𝕜] X} {a : ℝ} (hP : ‖P‖ ≤ a) (k : ℕ) : ‖P ^ k‖ ≤ a ^ k := by
  induction k with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih hP (norm_nonneg _) ((norm_nonneg _).trans ih))

/-- Powers of a contraction are contractions. -/
theorem norm_pow_le_one {P : X →L[𝕜] X} (hP : ‖P‖ ≤ 1) (n : ℕ) : ‖P ^ n‖ ≤ 1 := by
  simpa using norm_pow_le_pow hP n

end Duhamel

end Feec.TimeStepping

/-! ### Semigroups: Taylor's formula and the Lax–Richtmyer theorem -/

namespace Feec.C0Semigroup

open Set (Icc Ico Ici)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E)

/-- **Taylor's formula for a semigroup**: for a chain `u₀, …, u_p` in the graph of the generator
(`u₀ ∈ D(Aᵖ)`, `uⱼ = Aʲ u₀`) and `‖S(s)‖ ≤ M` on `[0, T]`,
`‖S(t) u₀ - Σ_{j<p} tʲ/j! uⱼ‖ ≤ M tᵖ/p! ‖u_p‖` for `t ∈ [0, T]`. [Pazy1983], §1.2 -/
theorem norm_S_sub_taylor_le {T M : ℝ} (hM : ∀ t ∈ Icc 0 T, ‖G.S t‖ ≤ M) (p : ℕ) :
    ∀ {u : ℕ → E}, (∀ j < p, (u j, u (j + 1)) ∈ G.generator.graph) → ∀ {t : ℝ}, t ∈ Icc 0 T →
      ‖G.S t (u 0) - ∑ j ∈ range p, (t ^ j / j.factorial) • u j‖ ≤
        M * (t ^ p / p.factorial) * ‖u p‖ := by
  induction p with
  | zero =>
    intro u _ t ht
    simpa using ((G.S t).le_opNorm (u 0)).trans
      (mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _))
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

/-- **Lax–Richtmyer for semigroups**: if `‖Pᵏ‖ ≤ Mₛ` for `k ≤ n`, `‖S(t)‖ ≤ M` on `[0, nτ]`, and
`P` is consistent of order `p` on `D(A^{p+1})`, `‖P v₀ - S(τ) v₀‖ ≤ K τ^{p+1} ‖v_{p+1}‖` for every
chain `v` in the graph of the generator, then
`‖Pⁿ u₀ - S(nτ) u₀‖ ≤ Mₛ K M nτ τᵖ ‖u_{p+1}‖` for every chain `u`. [Thomee2006], Ch. 9;
[BrennerThomee1979] -/
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
      ((G.S _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hS _ hkn) (norm_nonneg _))
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

/-- A scheme `P` is **consistent of order `p` with constant `K`** with the flow `e^{τL}`:
`‖P y - e^{τL} y‖ ≤ K τ^{p+1} ‖L^{p+1} y‖` for every `y`. [Thomee2006], Ch. 7 -/
def IsConsistent (L P : X →L[𝕜] X) (τ : ℝ) (p : ℕ) (K : ℝ) : Prop :=
  ∀ y, ‖P y - exp ((τ : 𝕜) • L) y‖ ≤ K * τ ^ (p + 1) * ‖(L ^ (p + 1)) y‖

variable [CompleteSpace X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

/-- **Stability and consistency of order `p` give the rate `Mₛ K M t τᵖ` on a Banach space**:
if `‖e^{tL}‖ ≤ M` for `t ≥ 0`, `‖Pᵏ‖ ≤ Mₛ` for `k ≤ n` and `P` is consistent of order `p` with
constant `K`, then `‖Pⁿ y - e^{nτL} y‖ ≤ Mₛ K M (n τ) τᵖ ‖L^{p+1} y‖`: the semigroup `e^{tL}`
case of `C0Semigroup.norm_pow_apply_sub_S_le`. [BrennerThomee1979]; [Thomee2006], Ch. 7 -/
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

/-- The **time average** `A_δ y = δ⁻¹ ∫₀^δ e^{sL} y ds`, with `L A_δ = δ⁻¹ (e^{δL} - 1)`
(`apply_timeAvg_eq`): for `‖e^{sL}‖ ≤ M` on `[0, δ]`, `‖A_δ‖ ≤ M` and `‖L A_δ‖ ≤ (M + 1)/δ`
(`norm_apply_timeAvg_le_of_norm_exp_le`), so `A_δ` smooths discrete data uniformly in `L`. -/
def timeAvg (L : X →L[𝕜] X) (δ : ℝ) (y : X) : X :=
  δ⁻¹ • ∫ s in (0 : ℝ)..δ, exp ((s : 𝕜) • L) y

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
theorem continuous_exp_apply (L : X →L[𝕜] X) (y : X) :
    Continuous fun s : ℝ => exp ((s : 𝕜) • L) y :=
  (C0Group.continuous_exp_ofReal_smul L).clm_apply continuous_const

omit [IsScalarTower ℝ 𝕜 X] in
theorem timeAvg_sub (L : X →L[𝕜] X) (δ : ℝ) (y z : X) :
    timeAvg L δ (y - z) = timeAvg L δ y - timeAvg L δ z := by
  unfold timeAvg
  simp only [_root_.map_sub]
  rw [intervalIntegral.integral_sub ((continuous_exp_apply L y).intervalIntegrable _ _)
    ((continuous_exp_apply L z).intervalIntegrable _ _), smul_sub]

/-- `L A_δ y = A_δ (L y)`. -/
theorem apply_timeAvg (L : X →L[𝕜] X) (δ : ℝ) (y : X) :
    L (timeAvg L δ y) = timeAvg L δ (L y) := by
  unfold timeAvg
  rw [L.map_smul_of_tower, ← ContinuousLinearMap.intervalIntegral_comp_comm L
    ((continuous_exp_apply L y).intervalIntegrable _ _)]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  exact congrArg (fun C : X →L[𝕜] X => C y) (C0Group.commute_exp_ofReal_smul L s).eq

/-- `L A_δ y = δ⁻¹ (e^{δL} y - y)` (the fundamental theorem of calculus). -/
theorem apply_timeAvg_eq (L : X →L[𝕜] X) (δ : ℝ) (y : X) :
    L (timeAvg L δ y) = δ⁻¹ • (exp ((δ : 𝕜) • L) y - y) := by
  unfold timeAvg
  rw [L.map_smul_of_tower, ← ContinuousLinearMap.intervalIntegral_comp_comm L
    ((continuous_exp_apply L y).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => C0Group.hasDerivAt_exp_ofReal_smul_apply L y s)
      ((L.continuous.comp (continuous_exp_apply L y)).intervalIntegrable _ _)]
  simp

omit [IsScalarTower ℝ 𝕜 X] in
/-- `‖A_δ y - y‖ ≤ η` when `‖e^{sL} y - y‖ ≤ η` on `[0, δ]`. -/
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
/-- `‖A_δ y‖ ≤ M ‖y‖` when `‖e^{sL}‖ ≤ M` on `[0, δ]`, `δ > 0`. -/
theorem norm_timeAvg_le_of_norm_exp_le {M δ : ℝ}
    (hL : ∀ s ∈ Set.Icc 0 δ, ‖exp ((s : 𝕜) • L)‖ ≤ M) (hδ : 0 < δ) (y : X) :
    ‖timeAvg L δ y‖ ≤ M * ‖y‖ := by
  unfold timeAvg
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ)
    (f := fun s : ℝ => exp ((s : 𝕜) • L) y) (C := M * ‖y‖) fun s hs => by
      rw [Set.uIoc_of_le hδ.le] at hs
      exact ((exp ((s : 𝕜) • L)).le_opNorm y).trans
        (mul_le_mul_of_nonneg_right (hL s ⟨hs.1.le, hs.2⟩) (norm_nonneg _))
  rw [sub_zero, abs_of_pos hδ] at h
  calc δ⁻¹ * ‖∫ s in (0 : ℝ)..δ, exp ((s : 𝕜) • L) y‖ ≤ δ⁻¹ * (M * ‖y‖ * δ) := by gcongr
    _ = M * ‖y‖ := by field_simp

/-- `‖L A_δ y‖ ≤ (M + 1)/δ ‖y‖` when `‖e^{δL}‖ ≤ M`, `δ > 0` (`L A_δ = δ⁻¹ (e^{δL} - 1)`). -/
theorem norm_apply_timeAvg_le_of_norm_exp_le {M δ : ℝ} (hL : ‖exp ((δ : 𝕜) • L)‖ ≤ M)
    (hδ : 0 < δ) (y : X) : ‖L (timeAvg L δ y)‖ ≤ (M + 1) / δ * ‖y‖ := by
  rw [apply_timeAvg_eq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
  have h1 := norm_sub_le (exp ((δ : 𝕜) • L) y) y
  have h2 := ((exp ((δ : 𝕜) • L)).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right hL (norm_nonneg y))
  calc δ⁻¹ * ‖exp ((δ : 𝕜) • L) y - y‖ ≤ δ⁻¹ * ((M + 1) * ‖y‖) := by gcongr; linarith
    _ = _ := by ring

/-- **Smoothing on a Banach space**: `‖Lᵏ A_δᵏ y‖ ≤ ((M + 1)/δ)ᵏ ‖y‖` when `‖e^{δL}‖ ≤ M`,
uniformly in the bounded `L`. -/
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
/-- `‖A_δᵏ y - y‖ ≤ (Σ_{j<k} Mʲ) ‖A_δ y - y‖` when `‖e^{sL}‖ ≤ M` on `[0, δ]` (`‖A_δ‖ ≤ M` and
linearity). -/
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

/-- `‖e^{tL}‖ ≤ 1` for bounded dissipative `L` and `t ≥ 0`. -/
theorem norm_exp_le_one (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖(C0Group.ofBounded L).S t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using LumerPhillips.norm_exp_smul_apply_le hL ht x

/-- **The Taylor remainder of a contraction semigroup**: for bounded dissipative `L`, `t ≥ 0`,
`‖e^{tL} y - Σ_{j<p} tʲ/j! Lʲ y‖ ≤ tᵖ/p! ‖Lᵖ y‖`, Taylor's formula for the semigroup
`e^{tL}` (`C0Semigroup.norm_S_sub_taylor_le`). -/
theorem norm_exp_sub_taylor_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) (p : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (y : X) :
    ‖exp ((t : 𝕜) • L) y - ∑ j ∈ range p, (t ^ j / j.factorial) • (L ^ j) y‖ ≤
      t ^ p / p.factorial * ‖(L ^ p) y‖ := by
  have h := (C0Group.ofBounded L).toC0Semigroup.norm_S_sub_taylor_le (T := t)
    (fun s hs => norm_exp_le_one hL hs.1) p (u := fun j => (L ^ j) y)
    (fun j _ => C0Group.pow_apply_mem_graph_generator_ofBounded L y j) ⟨ht, le_rfl⟩
  simpa using h

/-- **Consistency from an expansion**: `P = Σ_{j≤p} τʲ/j! Lʲ + τ^{p+1} ρ L^{p+1}` with `‖ρ‖ ≤ K₀`
is consistent of order `p` with constant `K₀ + 1/(p+1)!`. [Thomee2006], Ch. 7 -/
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
    exact (ρ.le_opNorm _).trans (mul_le_mul_of_nonneg_right hρ (norm_nonneg _))
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

/-- **Stability and consistency of order `p` give the rate `M K t τᵖ`**: if `‖Pᵏ‖ ≤ M` for
`k ≤ n` and `P` is consistent of order `p` with constant `K`, then
`‖Pⁿ y - e^{nτL} y‖ ≤ M K (n τ) τᵖ ‖L^{p+1} y‖`: the contraction case `‖e^{tL}‖ ≤ 1` of
`norm_pow_apply_sub_exp_le_of_norm_exp_le`. [BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem norm_pow_apply_sub_exp_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {P : X →L[𝕜] X} {M : ℝ}
    {n : ℕ} (hP : ∀ k ≤ n, ‖P ^ k‖ ≤ M) {τ : ℝ} (hτ : 0 ≤ τ) {p : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hc : IsConsistent L P τ p K) (y : X) :
    ‖(P ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤ M * K * (n * τ) * τ ^ p * ‖(L ^ (p + 1)) y‖ := by
  simpa using norm_pow_apply_sub_exp_le_of_norm_exp_le (fun t ht => norm_exp_le_one hL ht) hP hτ
    hK hc y

/-! ### Smoothing by time averages of dissipative generators -/

/-- `‖A_δ y‖ ≤ ‖y‖` for dissipative `L`, `δ > 0`. -/
theorem norm_timeAvg_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {δ : ℝ} (hδ : 0 < δ) (y : X) :
    ‖timeAvg L δ y‖ ≤ ‖y‖ := by
  simpa using norm_timeAvg_le_of_norm_exp_le (fun s hs => norm_exp_le_one hL hs.1) hδ y

/-- **Smoothing**: `‖Lᵏ A_δᵏ y‖ ≤ (2/δ)ᵏ ‖y‖`, uniformly in the bounded dissipative `L`. -/
theorem norm_pow_timeAvg_iterate_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {δ : ℝ} (hδ : 0 < δ)
    (k : ℕ) (y : X) : ‖(L ^ k) ((timeAvg L δ)^[k] y)‖ ≤ (2 / δ) ^ k * ‖y‖ := by
  simpa [one_add_one_eq_two] using
    norm_pow_timeAvg_iterate_le_of_norm_exp_le (norm_exp_le_one hL hδ.le) hδ k y

/-- `‖A_δᵏ y - y‖ ≤ k ‖A_δ y - y‖` (contraction and linearity). -/
theorem norm_timeAvg_iterate_sub_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {δ : ℝ} (hδ : 0 < δ)
    (k : ℕ) (y : X) : ‖(timeAvg L δ)^[k] y - y‖ ≤ k * ‖timeAvg L δ y - y‖ := by
  simpa using
    norm_timeAvg_iterate_sub_le_of_norm_exp_le (fun s hs => norm_exp_le_one hL hs.1) hδ k y

/-! ### θ-schemes of bounded dissipative operators -/

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
/-- **A bounded dissipative operator on a Hilbert space is m-dissipative** (closed, everywhere
defined, with dissipative adjoint), so the θ-schemes of `Feec.TimeStepping.Theta` apply to it. -/
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
/-- The resolvent `R = (λ - L)⁻¹`, `λ = (θ τ)⁻¹`, of a bounded dissipative `L` (real `θ, τ > 0`):
`λ R y - L R y = y`, `R L = L R`, `‖λ R‖ ≤ 1`, and the θ-scheme is `(θ² τ)⁻¹ R - (1 - θ)/θ`. -/
private theorem thetaStep_resolvent (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {θ τ : ℝ} (hθ : 0 < θ)
    (hτ : 0 < τ) :
    let R := resolvent ((L : X →ₗ[𝕜] X).toPMap ⊤) ((θ : 𝕜) * (τ : 𝕜))⁻¹
    (∀ y, ((θ : 𝕜) * (τ : 𝕜))⁻¹ • R y - L (R y) = y) ∧ (∀ y, R (L y) = L (R y)) ∧
      ‖((θ : 𝕜) * (τ : 𝕜))⁻¹ • R‖ ≤ 1 := by
  intro R
  have hA := L.isMDissipative_toPMap_top hL
  have hμ : 0 < (θ * τ)⁻¹ := by positivity
  have e : ((θ : 𝕜) * (τ : 𝕜))⁻¹ = (((θ * τ)⁻¹ : ℝ) : 𝕜) := by push_cast; rfl
  have hR : IsResolvent ((L : X →ₗ[𝕜] X).toPMap ⊤) ((θ : 𝕜) * (τ : 𝕜))⁻¹ R := by
    rw [e]; exact e ▸ hA.isResolvent hμ
  have h1 : ∀ y, ((θ : 𝕜) * (τ : 𝕜))⁻¹ • R y - L (R y) = y := hR.sub_apply
  refine ⟨h1, fun y => ?_, ?_⟩
  · have h2 : R (((θ : 𝕜) * (τ : 𝕜))⁻¹ • y - L y) = y := hR.apply_sub ⟨y, trivial⟩
    rw [_root_.map_sub, _root_.map_smul] at h2
    exact sub_right_injective (h2.trans (h1 y).symm)
  · rw [norm_smul]
    have hn : ‖R‖ ≤ ((θ * τ)⁻¹)⁻¹ := by
      have := hA.norm_resolvent_le hμ
      rwa [← e] at this
    rw [e, RCLike.norm_ofReal, abs_of_pos hμ]
    calc (θ * τ)⁻¹ * ‖R‖ ≤ (θ * τ)⁻¹ * ((θ * τ)⁻¹)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hμ.ne'

/-- **The θ-scheme of a bounded dissipative operator, expanded to first order**: for real
`θ > 0`, `τ > 0`, `r_θ(τ L) y = y + τ L y + τ² (θ W) (L² y)` with `W = (1 - θ τ L)⁻¹`,
`‖θ W‖ ≤ θ`. -/
theorem exists_thetaStep_apply_eq (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {θ τ : ℝ} (hθ : 0 < θ)
    (hτ : 0 < τ) : ∃ ρ : X →L[𝕜] X, ‖ρ‖ ≤ θ ∧ ∀ y,
      thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ y =
        ∑ j ∈ range 2, (τ ^ j / j.factorial) • (L ^ j) y + τ ^ 2 • ρ ((L ^ 2) y) := by
  obtain ⟨h1, h2, h3⟩ := thetaStep_resolvent (𝕜 := 𝕜) hL hθ hτ
  set R := resolvent ((L : X →ₗ[𝕜] X).toPMap ⊤) ((θ : 𝕜) * (τ : 𝕜))⁻¹
  refine ⟨((θ : 𝕜) * ((θ : 𝕜) * (τ : 𝕜))⁻¹) • R, ?_, fun y => ?_⟩
  · rw [mul_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos hθ]
    exact mul_le_of_le_one_right hθ.le h3
  have hθ' : (θ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hθ.ne'
  have hτ' : (τ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hτ.ne'
  have hL1 : L (R y) = ((θ : 𝕜) * (τ : 𝕜))⁻¹ • R y - y := by
    have h := h1 y; generalize R y = r at h ⊢; rw [← h]; abel
  have hL2 : R ((L ^ 2) y) =
      ((θ : 𝕜) * (τ : 𝕜))⁻¹ • (((θ : 𝕜) * (τ : 𝕜))⁻¹ • R y - y) - L y := by
    rw [show (L ^ 2) y = L (L y) by simp [pow_succ], h2, h2, hL1, _root_.map_sub,
      _root_.map_smul, hL1]
  simp only [thetaStep, sum_range_succ, sum_range_zero, _root_.sub_apply, _root_.smul_apply,
    pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, one_smul,
    zero_add, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
  rw [hL2]
  simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  match_scalars <;> field_simp <;> ring

/-- **Crank–Nicolson of a bounded dissipative operator, expanded to second order**: for
`τ > 0`, `r_{1/2}(τ L) y = y + τ L y + τ²/2 L² y + τ³ (W/4) (L³ y)` with `W = (1 - τ L / 2)⁻¹`,
`‖W/4‖ ≤ 1/4`. -/
theorem exists_thetaStep_half_apply_eq (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {τ : ℝ}
    (hτ : 0 < τ) : ∃ ρ : X →L[𝕜] X, ‖ρ‖ ≤ 1 / 4 ∧ ∀ y,
      thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) ((1 / 2 : ℝ) : 𝕜) τ y =
        ∑ j ∈ range 3, (τ ^ j / j.factorial) • (L ^ j) y + τ ^ 3 • ρ ((L ^ 3) y) := by
  obtain ⟨h1, h2, h3⟩ := thetaStep_resolvent (𝕜 := 𝕜) hL (θ := 1 / 2) (by norm_num) hτ
  set R := resolvent ((L : X →ₗ[𝕜] X).toPMap ⊤) (((1 / 2 : ℝ) : 𝕜) * (τ : 𝕜))⁻¹
  refine ⟨((1 / 4 : 𝕜) * (((1 / 2 : ℝ) : 𝕜) * (τ : 𝕜))⁻¹) • R, ?_, fun y => ?_⟩
  · rw [mul_smul, norm_smul]
    have : ‖(1 / 4 : 𝕜)‖ = 1 / 4 := by
      rw [show (1 / 4 : 𝕜) = ((1 / 4 : ℝ) : 𝕜) by push_cast; rfl, RCLike.norm_ofReal]
      norm_num
    rw [this]
    exact mul_le_of_le_one_right (by norm_num) h3
  have hτ' : (τ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hτ.ne'
  set c : 𝕜 := (((1 / 2 : ℝ) : 𝕜) * (τ : 𝕜))⁻¹
  have hL1 : L (R y) = c • R y - y := by
    have h := h1 y; generalize R y = r at h ⊢; rw [← h]; abel
  have hL3 : R ((L ^ 3) y) = c • (c • (c • R y - y) - L y) - L (L y) := by
    rw [show (L ^ 3) y = L (L (L y)) by simp [pow_succ], h2, h2, h2, hL1, _root_.map_sub,
      _root_.map_smul, hL1, _root_.map_sub, _root_.map_smul, _root_.map_sub, _root_.map_smul,
      hL1]
  simp only [thetaStep, sum_range_succ, sum_range_zero, _root_.sub_apply, _root_.smul_apply,
    pow_zero, pow_one, Nat.factorial, Nat.cast_one, Nat.succ_eq_add_one, div_one, one_smul,
    zero_add, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
  rw [hL3, show (L ^ 2) y = L (L y) by simp [pow_succ]]
  simp only [c, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  match_scalars <;> field_simp <;> ring

/-- **The θ-scheme is consistent of order `1`** with constant `θ + 1/2` (real `θ > 0`, `τ > 0`),
uniformly in the bounded dissipative `L`. [Thomee2006], Ch. 7 -/
theorem isConsistent_thetaStep (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {θ τ : ℝ} (hθ : 0 < θ)
    (hτ : 0 < τ) :
    IsConsistent L (thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ) τ 1 (θ + 1 / 2) := by
  obtain ⟨ρ, hρ, hP⟩ := exists_thetaStep_apply_eq (𝕜 := 𝕜) hL hθ hτ
  have := isConsistent_of_eq hL hτ.le hρ hP
  rwa [show θ + 1 / 2 = θ + 1 / ((1 + 1).factorial : ℝ) by norm_num [Nat.factorial]]

/-- **Crank–Nicolson is consistent of order `2`** with constant `5/12` (`τ > 0`), uniformly in
the bounded dissipative `L`. [Thomee2006], Ch. 7 -/
theorem isConsistent_thetaStep_half (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {τ : ℝ} (hτ : 0 < τ) :
    IsConsistent L (thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) ((1 / 2 : ℝ) : 𝕜) τ) τ 2 (5 / 12) := by
  obtain ⟨ρ, hρ, hP⟩ := exists_thetaStep_half_apply_eq (𝕜 := 𝕜) hL hτ
  have := isConsistent_of_eq hL hτ.le hρ hP
  rwa [show (5 / 12 : ℝ) = 1 / 4 + 1 / ((2 + 1).factorial : ℝ) by norm_num [Nat.factorial]]

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
/-- The θ-scheme of a bounded dissipative operator is power bounded by `1` (`re θ ≥ 1/2`,
`τ > 0`). -/
theorem norm_thetaStep_pow_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {θ : 𝕜}
    (hθ : 1 / 2 ≤ RCLike.re θ) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) :
    ‖thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ ^ n‖ ≤ 1 :=
  norm_pow_le_one (norm_thetaStep_le (L.isMDissipative_toPMap_top hL) hθ hτ) n

/-- **The global error of the θ-scheme** (`1/2 ≤ θ`, real): at `t = n τ`,
`‖r_θ(τ L)ⁿ y - e^{tL} y‖ ≤ (θ + 1/2) t τ ‖L² y‖` for every bounded dissipative `L`.
[BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem norm_thetaStep_pow_sub_exp_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {θ τ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hτ : 0 < τ) (n : ℕ) (y : X) :
    ‖(thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) θ τ ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤
      (θ + 1 / 2) * (n * τ) * τ * ‖(L ^ 2) y‖ := by
  have := norm_pow_apply_sub_exp_le hL (n := n) (M := 1)
    (fun k _ => norm_thetaStep_pow_le hL (by simpa using hθ) hτ k) hτ.le (by linarith)
    (isConsistent_thetaStep hL (by linarith) hτ) y
  simpa using this

/-- **The global error of implicit Euler**: at `t = n τ`,
`‖(1 - τ L)⁻ⁿ y - e^{tL} y‖ ≤ 3/2 t τ ‖L² y‖` for every bounded dissipative `L`.
[Thomee2006], Ch. 7 -/
theorem norm_implicitEuler_pow_sub_exp_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {τ : ℝ}
    (hτ : 0 < τ) (n : ℕ) (y : X) :
    ‖(thetaStep ((L : X →ₗ[𝕜] X).toPMap ⊤) 1 τ ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤
      3 / 2 * (n * τ) * τ * ‖(L ^ 2) y‖ := by
  have := norm_thetaStep_pow_sub_exp_le (𝕜 := 𝕜) hL (θ := 1) (by norm_num) hτ n y
  norm_num at this ⊢
  exact this

/-- **The global error of Crank–Nicolson** (`cayley` with half step `τ/2`): at `t = n τ`,
`‖cayley(L, τ/2)ⁿ y - e^{tL} y‖ ≤ 5/12 t τ² ‖L³ y‖` for every bounded dissipative `L`.
[BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem norm_cayley_pow_sub_exp_le (hL : ∀ x, RCLike.re ⟪L x, x⟫ ≤ 0) {τ : ℝ} (hτ : 0 < τ)
    (n : ℕ) (y : X) :
    ‖(cayley ((L : X →ₗ[𝕜] X).toPMap ⊤) (τ / 2) ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤
      5 / 12 * (n * τ) * τ ^ 2 * ‖(L ^ 3) y‖ := by
  rw [cayley_half_eq_thetaStep]
  have := norm_pow_apply_sub_exp_le hL (n := n) (M := 1)
    (fun k _ => norm_thetaStep_pow_le hL (by rw [RCLike.ofReal_re]) hτ k) hτ.le (by norm_num)
    (isConsistent_thetaStep_half hL hτ) y
  simpa using this

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
/-- **Discrete constraint propagation for closed invariant subspaces**: if `L K ⊆ K` for a closed
`K` (for instance a subspace of a finite element space), then `r_θ(τ L) K ⊆ K` (`re θ > 0`,
`τ > 0`): the part of `L` in `K` is bounded and dissipative, so the resolvent equation is solvable
within `K`. [QuennevilleBelair2015], Prop 4.18 -/
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
