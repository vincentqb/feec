module

public import Feec.TimeStepping.StableFamily

/-!
# The fully discrete FEEC theorem on Banach spaces

A **Banach FEEC discretization** (`Feec.TimeStepping.BanachFEEC G κ`) of a strongly continuous
semigroup `S(t)` on a Banach space `E` over `𝕜 = ℝ` or `ℂ` (generator `A`): a uniformly stable
family (`Feec.TimeStepping.StableFamily`: Banach spaces `Xₕ`, bounded generators `Lₕ`,
`‖e^{tLₕ}‖ ≤ M` for `t ≥ 0`, uniformly in `h`), uniformly bounded reading maps `ιₕ : Xₕ → E`
with uniformly bounded left inverses `πₕ`, and `‖S(t)‖ ≤ M` with the same `M`. No inner product, dissipativity or
compatibility of `ιₕ` with anything is assumed; the semidiscrete solution is `ιₕ e^{tLₕ} v`
(`BanachFEEC.sol`). Every dissipative FEEC discretization of a Hilbert space is one, with `M = 1`
(`Feec.HilbertComplex.DissipFEEC.toBanachFEEC`): the fully discrete FEEC theorem
(`Feec.HilbertComplex.dissipFEEC_fullyDiscrete`) takes its fields `rate_iterates` and
`converges_iterates` from this one, its temporal errors and `rate_uniform_iterates` from the
Banach-space bounds of `Feec.TimeStepping.TimeScheme`; its rates along smooth comparisons and
its forced and lifted iterates are Hilbert-side. The crown
(`Feec.HilbertComplex.ConformingFamily.feec`) states this theorem for its discretizations; there,
dissipative on Hilbert spaces, it gives Banach-route constants, not new rates (von Neumann's
inequality gives the stronger `‖r(τLₕ)ⁿ‖ ≤ 1`). Its new content is only for estimates in norms in
which the family is not Hilbert-contractive (e.g. the maximum norm).

The module lives in `Feec.TimeStepping` (it needs only semigroups and time schemes, no Hilbert
structure); the Hilbert layer imports it. The results on the discrete spaces alone (backward
Euler, the rational schemes through the resolvent, the errors along trajectories) are those of the
underlying stable family (`Feec.TimeStepping.stableFamily`), whose maximum-norm instance is the
lumped-mass heat equation on the cube (`Feec.Models.Cube.MaxNormHeat`).

## Main results

**`banachFEEC`** (statement `BanachFEEC.Verdict`): for every Banach FEEC discretization,

1. (**every time scheme**, `Feec.TimeStepping.TimeScheme`: power bounded by `M(T)`, consistent of
   order `p` with constant `K`, uniformly in `h`) the iterates `ιₕ Pₕⁿ v` are stable,
   `‖ιₕ Pₕⁿ v‖ ≤ ‖ιₕ‖ M(T) ‖v‖`; their temporal error is
   `‖ιₕ e^{tₙ Lₕ} v - ιₕ Pₕⁿ v‖ ≤ ‖ιₕ‖ M(T) K M tₙ τₕᵖ ‖Lₕ^{p+1} v‖`; the fully discrete error is
   the semidiscrete error plus the temporal error; and (**Lax–Brenner–Thomée**) wherever the
   semidiscrete solutions from `vₕ` converge to `S(t) x`, uniformly on bounded time intervals,
   the fully discrete ones converge to `S(tₙ) x` as `τₕ → 0`, uniformly over the
   time levels `tₙ ∈ [0, T]`, with no smoothness of `vₕ` (the data are smoothed by time averages,
   `Feec.TimeStepping.timeAvg`);
2. (**backward Euler**) the discrete resolvents `Rₕ = (1 - τLₕ)⁻¹` (`StableFamily.res`) satisfy
   `‖Rₕⁿ‖ ≤ M` for every `τ > 0`, `n` and `h`, by the Hille–Yosida estimates
   (`Feec.TimeStepping.norm_pow_le_of_generator`): backward Euler is a time scheme of every Banach
   FEEC discretization (`StableFamily.backwardEuler`), so 1 gives it convergence for every datum;
3. (**every A-stable rational scheme** `r`, `r(τLₕ)` through `Rₕ`, `StableFamily.step`)
   Brenner–Thomée's stability bound `‖r(τLₕ)ⁿ‖ ≤ M (1 + C'_r √n)`, `C'_r = sqrtConst r`
   (`Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_le_of_resolvent_of_isAStable`,
   `|r(∞)| = 1` included) and, for `r` of order `p`, the **sharp temporal error**
   `‖ιₕ e^{nτLₕ} v - ιₕ r(τLₕ)ⁿ v‖ ≤ ‖ιₕ‖ C_r M nτ τᵖ ‖Lₕ^{p+1} v‖` with no `√n` loss and
   `C_r = sharpConst r p` (Brenner–Thomée's smooth-data estimate,
   `Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent`), so the
   fully discrete error is the semidiscrete error plus this; the same bounds hold for the exact
   semigroup, `‖r(τA)ⁿ‖ ≤ M (1 + C'_r √n)` and
   `‖r(τA)ⁿ x - S(nτ) x‖ ≤ C_r M nτ τᵖ ‖A^{p+1} x‖` on `D(A^{p+1})`, for `r(τA)` through every
   `R` with `R (x - τ A x) = x` on `D(A)`.

All constants depend on `r`, `p` and `M` only, so they are independent of `h` (the bounds
contain `‖Lₕ^{p+1} v‖`, which need not be bounded in `h`). A rational scheme is a time scheme
when its powers are bounded uniformly (`StableFamily.rationalScheme`, consistent of order `p` with
constant `C_r M`): `M(T) = M` for backward Euler; for every A-stable `r` and dissipative `Lₕ` on
Hilbert spaces `M(T) = 1` by von Neumann's inequality, which is the scheme
`Feec.HilbertComplex.DissipFEEC.rationalScheme`. For an A-stable `r` without such
a bound, `√n` grows as `τ → 0` at fixed `T = nτ` and 1 does not apply; the convergence for all
data is then not claimed (on Banach spaces it fails in general, [BrennerThomee1979]).

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [A. Gomilko, Y. Tomilov, *Rational Approximation of Operator Semigroups via the B-Calculus*][GomilkoTomilov2024],
  Thm 1.1
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7–9
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.5 (the Hille–Yosida estimates), §3.4 (approximation of semigroups)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter Topology Metric NormedSpace Finset

@[expose] public noncomputable section

universe u

namespace Feec.TimeStepping

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A **Banach FEEC discretization** of a strongly continuous semigroup `G` on `E`: a uniformly
stable family (`Feec.TimeStepping.StableFamily`: Banach spaces `Xₕ` with bounded generators `Lₕ`,
`‖e^{tLₕ}‖ ≤ M` for `t ≥ 0`, uniformly in `h`), uniformly bounded `ιₕ : Xₕ → E` and
`πₕ : E → Xₕ` with `πₕ ιₕ = 1`, and `‖S(t)‖ ≤ M` for `t ≥ 0` (the same `M`).
[Pazy1983], §3.4 -/
structure BanachFEEC (G : C0Semigroup 𝕜 E) (κ : Type*) extends StableFamily.{u} 𝕜 κ where
  /-- the filter along which the discretization is refined -/
  l : Filter κ
  /-- the maps reading discrete states in `E` -/
  incl : ∀ h, X h →L[𝕜] E
  /-- their left inverses -/
  proj : ∀ h, E →L[𝕜] X h
  proj_incl : ∀ h x, proj h (incl h x) = x
  bound : ∃ C, ∀ h, ‖incl h‖ ≤ C ∧ ‖proj h‖ ≤ C
  norm_S_le : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M
  M_nonneg := (norm_nonneg _).trans (norm_S_le 0 le_rfl)

namespace BanachFEEC

variable {G : C0Semigroup 𝕜 E} {κ : Type*} (B : BanachFEEC.{u} G κ)

/-- A nonnegative uniform bound of `‖ιₕ‖`, `‖πₕ‖`. -/
def boundConst : ℝ := max B.bound.choose 0

theorem boundConst_nonneg : 0 ≤ B.boundConst := le_max_right _ _

theorem norm_incl_le (h : κ) : ‖B.incl h‖ ≤ B.boundConst :=
  (B.bound.choose_spec h).1.trans (le_max_left _ _)

theorem norm_proj_le (h : κ) : ‖B.proj h‖ ≤ B.boundConst :=
  (B.bound.choose_spec h).2.trans (le_max_left _ _)

/-- **Stability of the reading map**: `‖v‖ ≤ C ‖ιₕ v‖` (from `πₕ ιₕ = 1`). -/
theorem norm_le_norm_incl (h : κ) (v : B.X h) : ‖v‖ ≤ B.boundConst * ‖B.incl h v‖ :=
  calc ‖v‖ = ‖B.proj h (B.incl h v)‖ := by rw [B.proj_incl]
    _ ≤ _ := (B.proj h).le_of_opNorm_le (B.norm_proj_le h) _

/-- The semidiscrete solution `ιₕ e^{tLₕ} v`. -/
def sol (h : κ) (v : B.X h) (t : ℝ) : E := B.incl h (exp ((t : 𝕜) • B.L h) v)

/-! ### Time schemes -/

/-- A **time scheme** of `B`: a time scheme (`Feec.TimeStepping.TimeScheme`) of its discrete
generators, power bounded and consistent uniformly in `h`. -/
abbrev TimeScheme := TimeStepping.TimeScheme B.L

variable {B}

/-- The **fully discrete solution** `ιₕ Pₕⁿ v` at the time level `tₙ = n τₕ`. -/
def TimeScheme.sol (Θ : B.TimeScheme) (h : κ) (v : B.X h) (n : ℕ) : E :=
  B.incl h ((Θ.P h ^ n) v)

namespace TimeScheme

variable (Θ : B.TimeScheme)

/-- **Stability**: `‖ιₕ Pₕⁿ v‖ ≤ ‖ιₕ‖ M(T) ‖v‖` for `n τₕ ≤ T`. -/
theorem norm_sol_le {T : ℝ} (h : κ) (v : B.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖Θ.sol h v n‖ ≤ ‖B.incl h‖ * Θ.M T * ‖v‖ := by
  rw [mul_assoc]
  refine ((B.incl h).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact (Θ.P h ^ n).le_of_opNorm_le (Θ.stable T h n hn) v

/-- **The temporal error**: `‖ιₕ e^{tₙ Lₕ} v - ιₕ Pₕⁿ v‖ ≤ ‖ιₕ‖ M(T) K M tₙ τₕᵖ ‖Lₕ^{p+1} v‖` for
`tₙ ≤ T`. [BrennerThomee1979] -/
theorem norm_sol_sub_sol_le {T : ℝ} (h : κ) (v : B.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖B.sol h v (n * Θ.τ h) - Θ.sol h v n‖ ≤
      ‖B.incl h‖ * (Θ.M T * Θ.K * B.M * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(B.L h ^ (Θ.p + 1)) v‖) := by
  rw [BanachFEEC.sol, TimeScheme.sol, ← _root_.map_sub]
  refine ((B.incl h).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  simpa using Θ.norm_exp_sub_pow_le (B.norm_exp_le h) v v hn

/-- **The fully discrete error is the semidiscrete error plus the temporal error**: for every
target `y` (the exact value `S(tₙ) x`), `‖y - ιₕ Pₕⁿ v‖ ≤ ‖y - ιₕ e^{tₙ Lₕ} v‖`
`+ ‖ιₕ‖ M(T) K M tₙ τₕᵖ ‖Lₕ^{p+1} v‖`. [Thomee2006], Ch. 7 -/
theorem norm_sub_sol_le (y : E) {T : ℝ} (h : κ) (v : B.X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖y - Θ.sol h v n‖ ≤ ‖y - B.sol h v (n * Θ.τ h)‖ +
      ‖B.incl h‖ * (Θ.M T * Θ.K * B.M * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(B.L h ^ (Θ.p + 1)) v‖) :=
  (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add le_rfl (Θ.norm_sol_sub_sol_le h v hn))

/-- **Fully discrete convergence for every datum** (the Lax equivalence theorem in the
Brenner–Thomée form, on Banach spaces): if the semidiscrete solutions `ιₕ e^{tLₕ} vₕ` converge to
`S(t) x` uniformly on every `[0, T]` (so `ιₕ vₕ → x`, at `t = 0`), then for time steps `τₕ → 0`
the fully discrete solutions converge to `S(tₙ) x`, uniformly over the time levels
`tₙ = n τₕ ∈ [0, T]`. No discrete smoothness of `vₕ` is assumed: `vₕ` is compared with the
smoothed `wₕ = A_δ^{p+1} vₕ` (`timeAvg`), `‖Lₕ^{p+1} wₕ‖ ≤ ((M + 1)/δ)^{p+1} ‖vₕ‖`, and
`‖vₕ - wₕ‖` is small uniformly in `h` because the semidiscrete orbits are uniformly continuous at
`0` (from the semidiscrete convergence and the stability `‖v‖ ≤ C ‖ιₕ v‖`).
[BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem converges {x : E} {v : ∀ h, B.X h}
    (hsd : ∀ T, TendstoUniformlyOn (fun h t => B.sol h (v h) t) (fun t => G.S t x) B.l (Icc 0 T))
    (hτ : Tendsto Θ.τ B.l (𝓝 0)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in B.l, ∀ n : ℕ, (n : ℝ) * Θ.τ h ∈ Icc 0 T →
      ‖G.S (n * Θ.τ h) x - Θ.sol h (v h) n‖ < ε := by
  have hv : Tendsto (fun h => B.incl h (v h)) B.l (𝓝 x) := by
    simpa [BanachFEEC.sol] using (hsd 0).tendsto_at (left_mem_Icc.2 le_rfl)
  set T' := max T 1
  set C := B.boundConst
  have hC := B.boundConst_nonneg
  set ML := B.M
  have hML : 0 ≤ ML := B.M_nonneg
  set M := max (Θ.M T) 0
  have hM0 : 0 ≤ M := le_max_right _ _
  set k := Θ.p + 1
  set Sk := ∑ j ∈ range k, ML ^ j
  have hSk : 0 ≤ Sk := sum_nonneg fun j _ => pow_nonneg hML j
  set B' := C * (ML + M) * Sk * C * 3
  have hB : 0 ≤ B' := by positivity
  set β := ε / (4 * (B' + 1))
  have hβ : 0 < β := by positivity
  have hS00 : G.S 0 x = x := C0Semigroup.S_zero_apply G x
  obtain ⟨δ₀, hδ₀, hcont⟩ := Metric.continuousWithinAt_iff.1
    (((G.strongCont x) 0 (Set.mem_Ici.2 le_rfl)).mono
      (Icc_subset_Ici_self : Icc (0 : ℝ) T' ⊆ Ici 0)) β hβ
  set δ := min (δ₀ / 2) 1
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hS0 : ∀ s ∈ Icc 0 δ, ‖G.S s x - x‖ < β := fun s hs => by
    have h1 := hcont (x := s) ⟨hs.1, hs.2.trans (hδ1.trans (le_max_right _ _))⟩ (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      linarith [min_le_left (δ₀ / 2) 1, hs.2])
    rwa [dist_eq_norm, hS00] at h1
  set Gδ := ((ML + 1) / δ) ^ k
  have hG : 0 ≤ Gδ := by positivity
  set D := C * M * Θ.K * ML * max T 0 * Gδ * (C * (‖x‖ + 1))
  have hK := Θ.K_nonneg
  have hD : 0 ≤ D := by positivity
  set γ := ε / (4 * (D + 1))
  have hγ : 0 < γ := by positivity
  have hc := Metric.tendstoUniformlyOn_iff.1 (hsd T') (min (ε / 2) β) (lt_min (half_pos hε) hβ)
  have hp : Tendsto (fun h => Θ.τ h ^ Θ.p) B.l (𝓝 0) := by
    simpa [zero_pow Θ.p_pos.ne'] using hτ.pow Θ.p
  filter_upwards [hc, Metric.tendsto_nhds.1 hv β hβ, Metric.tendsto_nhds.1 hv 1 one_pos,
    (tendsto_order.1 hp).2 γ hγ] with h h1 h2 h3 h4 n hn
  have hT0 : 0 ≤ T := hn.1.trans hn.2
  have hMT : Θ.M T ≤ M := le_max_left _ _
  have hMT0 := Θ.M_nonneg hT0 h
  -- the semidiscrete error
  have e1 : ‖G.S (n * Θ.τ h) x - B.sol h (v h) (n * Θ.τ h)‖ < ε / 2 := by
    have := h1 _ ⟨hn.1, hn.2.trans (le_max_left _ _)⟩
    rw [dist_eq_norm] at this
    exact this.trans_le (min_le_left _ _)
  -- the size of the data
  have hvb : ‖v h‖ ≤ C * (‖x‖ + 1) := by
    refine (B.norm_le_norm_incl h _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    have := norm_le_norm_add_norm_sub' (B.incl h (v h)) x
    rw [← dist_eq_norm] at this
    linarith [h3]
  -- the smoothed datum
  have hcl : ∀ s ∈ Icc 0 δ, ‖exp ((s : 𝕜) • B.L h) (v h) - v h‖ ≤ C * (3 * β) := by
    intro s hs
    refine (B.norm_le_norm_incl h _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [_root_.map_sub, show B.incl h (exp ((s : 𝕜) • B.L h) (v h)) = B.sol h (v h) s from rfl]
    have a1 := h1 s ⟨hs.1, hs.2.trans (hδ1.trans (le_max_right _ _))⟩
    rw [dist_eq_norm] at a1
    have a2 := hS0 s hs
    have a3 : ‖x - B.incl h (v h)‖ < β := by rw [norm_sub_rev, ← dist_eq_norm]; exact h2
    have e : B.sol h (v h) s - B.incl h (v h) = -(G.S s x - B.sol h (v h) s) + (G.S s x - x) +
        (x - B.incl h (v h)) := by abel
    rw [e]
    refine (norm_add₃_le).trans ?_
    rw [norm_neg]
    linarith [a1.trans_le (min_le_right _ _)]
  -- the temporal error
  have e2 : ‖B.sol h (v h) (n * Θ.τ h) - Θ.sol h (v h) n‖ < ε / 2 := by
    rw [BanachFEEC.sol, TimeScheme.sol, ← _root_.map_sub]
    refine ((B.incl h).le_opNorm _).trans_lt ?_
    have hX := Θ.norm_exp_sub_pow_le_of_timeAvg (B.norm_exp_le h) (v h) hn.2 hδ hcl
    have ht : (n : ℝ) * Θ.τ h ≤ max T 0 := hn.2.trans (le_max_left _ _)
    have hτp : 0 ≤ Θ.τ h ^ Θ.p := pow_nonneg (Θ.τ_pos h).le _
    have b1 : (ML + Θ.M T) * (Sk * (C * (3 * β))) ≤ (ML + M) * (Sk * (C * (3 * β))) := by
      gcongr
    have b2 : Θ.M T * Θ.K * ML * (n * Θ.τ h) * Θ.τ h ^ Θ.p * (Gδ * ‖v h‖) ≤
        M * Θ.K * ML * max T 0 * γ * (Gδ * (C * (‖x‖ + 1))) := by
      have c1 : Θ.M T * Θ.K * ML ≤ M * Θ.K * ML :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMT hK) hML
      have c2 : Θ.M T * Θ.K * ML * (n * Θ.τ h) ≤ M * Θ.K * ML * max T 0 :=
        mul_le_mul c1 ht hn.1 (by positivity)
      have c3 : Θ.M T * Θ.K * ML * (n * Θ.τ h) * Θ.τ h ^ Θ.p ≤ M * Θ.K * ML * max T 0 * γ :=
        mul_le_mul c2 h4.le hτp (by positivity)
      exact mul_le_mul c3 (mul_le_mul_of_nonneg_left hvb hG) (by positivity) (by positivity)
    have hι := B.norm_incl_le h
    calc ‖B.incl h‖ * ‖exp (((n * Θ.τ h : ℝ) : 𝕜) • B.L h) (v h) - (Θ.P h ^ n) (v h)‖
        ≤ C * ((ML + M) * (Sk * (C * (3 * β))) +
            M * Θ.K * ML * max T 0 * γ * (Gδ * (C * (‖x‖ + 1)))) :=
          mul_le_mul hι (hX.trans (add_le_add b1 b2)) (norm_nonneg _) hC
      _ = B' * β + D * γ := by simp only [B', D]; ring
      _ < ε / 4 + ε / 4 := by
          apply add_lt_add
          · calc B' * β < (B' + 1) * β := by nlinarith
              _ = ε / 4 := by simp only [β]; field_simp
          · calc D * γ < (D + 1) * γ := by nlinarith
              _ = ε / 4 := by simp only [γ]; field_simp
      _ = ε / 2 := by ring
  calc _ ≤ ‖G.S (n * Θ.τ h) x - B.sol h (v h) (n * Θ.τ h)‖ +
        ‖B.sol h (v h) (n * Θ.τ h) - Θ.sol h (v h) n‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add e1 e2
    _ = ε := add_halves ε

end TimeScheme

/-! ### Rational schemes -/

variable (B)

/-- The sharp temporal error of `ιₕ r(τLₕ)ⁿ v`, read through `ιₕ`. -/
theorem norm_sol_sub_step_le {r : RationalScheme} (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p)
    {τ : ℝ} (hτ : 0 < τ) (h : κ) (v : B.X h) (n : ℕ) :
    ‖B.sol h v (n * τ) - B.incl h ((B.step r τ h ^ n) v)‖ ≤
      ‖B.incl h‖ * (r.sharpConst p * B.M * (n * τ) * τ ^ p * ‖(B.L h ^ (p + 1)) v‖) := by
  rw [BanachFEEC.sol, ← _root_.map_sub]
  refine ((B.incl h).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [norm_sub_rev]
  exact B.norm_step_pow_sub_exp_le hr hp hτ h n v

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Brenner–Thomée's stability bound for the exact semigroup**: for every A-stable `r`,
`τ > 0` and `R` with `R (x - τ A x) = x` on `D(A)`, `‖r(τA)ⁿ‖ ≤ M (1 + C'_r √n)`.
[BrennerThomee1979] -/
theorem norm_resolventStep_pow_le {r : RationalScheme} (hr : r.IsAStable) {τ : ℝ} (hτ : 0 < τ)
    {R : E →L[𝕜] E} (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x)
    (n : ℕ) : ‖r.resolventStep R ^ n‖ ≤ B.M * (1 + r.sqrtConst * √n) :=
  RationalScheme.norm_resolventStep_pow_le_of_resolvent_of_isAStable G B.norm_S_le hr hτ hR n

/-- **Brenner–Thomée's smooth-data estimate for the exact semigroup**: for every A-stable `r` of
order `p`, `τ > 0`, `R` with `R (x - τ A x) = x` on `D(A)` and `x ∈ D(A^{p+1})` (a chain `u` in
the graph of `A`), `‖r(τA)ⁿ x - S(nτ) x‖ ≤ C_r M nτ τᵖ ‖A^{p+1} x‖`. [BrennerThomee1979];
[GomilkoTomilov2024], Thm 1.1(ii) -/
theorem norm_resolventStep_pow_sub_S_le {r : RationalScheme} (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖(r.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
      r.sharpConst p * B.M * (n * τ) * τ ^ p * ‖u (p + 1)‖ :=
  RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent G B.norm_S_le hr hp hτ hR n hu

/-! ### The verdict -/

/-- The conclusions of the fully discrete FEEC theorem on Banach spaces (`banachFEEC`): for
every time scheme, stability, temporal error, the error as semidiscrete plus temporal error, and
convergence wherever the semidiscrete solutions converge; the Hille–Yosida stability of backward
Euler; for every A-stable rational scheme, Brenner–Thomée's stability bound and the sharp
temporal error, discrete (with constants independent of `h`) and exact. -/
structure Verdict : Prop where
  /-- the iterates of every time scheme are stable on every horizon `[0, T]` -/
  stable_iterates (Θ : B.TimeScheme) {T : ℝ} (h : κ) (v : B.X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) : ‖Θ.sol h v n‖ ≤ ‖B.incl h‖ * Θ.M T * ‖v‖
  /-- the temporal error of every time scheme against the semidiscrete solution -/
  temporal_iterates (Θ : B.TimeScheme) {T : ℝ} (h : κ) (v : B.X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) : ‖B.sol h v (n * Θ.τ h) - Θ.sol h v n‖ ≤
      ‖B.incl h‖ * (Θ.M T * Θ.K * B.M * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(B.L h ^ (Θ.p + 1)) v‖)
  /-- the fully discrete error is the semidiscrete error plus the temporal error -/
  rate_iterates (Θ : B.TimeScheme) (y : E) {T : ℝ} (h : κ) (v : B.X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) : ‖y - Θ.sol h v n‖ ≤ ‖y - B.sol h v (n * Θ.τ h)‖ +
      ‖B.incl h‖ * (Θ.M T * Θ.K * B.M * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(B.L h ^ (Θ.p + 1)) v‖)
  /-- convergence over the time levels in `[0, T]` as `τₕ → 0`, for every family whose
  semidiscrete solutions converge (Lax–Brenner–Thomée) -/
  converges_iterates (Θ : B.TimeScheme) {x : E} {v : ∀ h, B.X h}
    (hsd : ∀ T, TendstoUniformlyOn (fun h t => B.sol h (v h) t) (fun t => G.S t x) B.l (Icc 0 T))
    (hτ : Tendsto Θ.τ B.l (𝓝 0)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in B.l, ∀ n : ℕ, (n : ℝ) * Θ.τ h ∈ Icc 0 T → ‖G.S (n * Θ.τ h) x - Θ.sol h (v h) n‖ < ε
  /-- backward Euler is stable, `‖(1 - τLₕ)⁻ⁿ‖ ≤ M` (Hille–Yosida) -/
  stable_backwardEuler {τ : ℝ} (hτ : 0 < τ) (h : κ) (n : ℕ) : ‖B.res τ h ^ n‖ ≤ B.M
  /-- Brenner–Thomée's stability bound for every A-stable rational scheme -/
  stable_rational (r : RationalScheme) (hr : r.IsAStable) {τ : ℝ} (hτ : 0 < τ) (h : κ) (n : ℕ) :
    ‖B.step r τ h ^ n‖ ≤ B.M * (1 + r.sqrtConst * √n)
  /-- the sharp temporal error of every A-stable rational scheme of order `p` -/
  temporal_rational (r : RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ}
    (hτ : 0 < τ) (h : κ) (v : B.X h) (n : ℕ) :
    ‖B.sol h v (n * τ) - B.incl h ((B.step r τ h ^ n) v)‖ ≤
      ‖B.incl h‖ * (r.sharpConst p * B.M * (n * τ) * τ ^ p * ‖(B.L h ^ (p + 1)) v‖)
  /-- the fully discrete error of every A-stable rational scheme: the semidiscrete error plus the
  sharp temporal error -/
  rate_rational (r : RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) (y : E)
    {τ : ℝ} (hτ : 0 < τ) (h : κ) (v : B.X h) (n : ℕ) :
    ‖y - B.incl h ((B.step r τ h ^ n) v)‖ ≤ ‖y - B.sol h v (n * τ)‖ +
      ‖B.incl h‖ * (r.sharpConst p * B.M * (n * τ) * τ ^ p * ‖(B.L h ^ (p + 1)) v‖)
  /-- Brenner–Thomée's stability bound for the exact semigroup -/
  exact_stable_rational (r : RationalScheme) (hr : r.IsAStable) {τ : ℝ} (hτ : 0 < τ)
    {R : E →L[𝕜] E} (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x)
    (n : ℕ) : ‖r.resolventStep R ^ n‖ ≤ B.M * (1 + r.sqrtConst * √n)
  /-- the sharp error of every A-stable rational scheme for the exact semigroup on
  `D(A^{p+1})` -/
  exact_rational (r : RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ}
    (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖(r.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
      r.sharpConst p * B.M * (n * τ) * τ ^ p * ‖u (p + 1)‖

end BanachFEEC

/-- **The fully discrete FEEC theorem on Banach spaces.** For a Banach FEEC discretization `B`
of a semigroup `S(t)` (exact and discrete semigroups bounded by `M`, uniformly bounded reading
maps with uniformly bounded left inverses): the iterates of every time scheme are stable, have
temporal error `‖ιₕ‖ M(T) K M tₙ τₕᵖ ‖Lₕ^{p+1} v‖` and converge wherever the semidiscrete
solutions converge; backward Euler is stable by Hille–Yosida; every A-stable rational scheme
satisfies Brenner–Thomée's stability bound `M (1 + C'_r √n)` and the sharp error
`C_r M nτ τᵖ ‖·^{p+1}‖`, for the discrete semigroups (constants independent of `h`) and for the
exact one.
[BrennerThomee1979]; [Thomee2006], Ch. 7–9; [Pazy1983], §1.5 -/
theorem banachFEEC [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    {G : C0Semigroup 𝕜 E} {κ : Type*} (B : BanachFEEC.{u} G κ) : B.Verdict where
  stable_iterates Θ _ h v _ hn := Θ.norm_sol_le h v hn
  temporal_iterates Θ _ h v _ hn := Θ.norm_sol_sub_sol_le h v hn
  rate_iterates Θ y _ h v _ hn := Θ.norm_sub_sol_le y h v hn
  converges_iterates Θ _ _ hsd hτ T _ hε := Θ.converges hsd hτ T hε
  stable_backwardEuler hτ h n := B.norm_res_pow_le hτ h n
  stable_rational _ hr _ hτ h n := B.norm_step_pow_le hr hτ h n
  temporal_rational _ hr _ hp _ hτ h v n := B.norm_sol_sub_step_le hr hp hτ h v n
  rate_rational _ hr _ hp _ _ hτ h v n := (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add le_rfl (B.norm_sol_sub_step_le hr hp hτ h v n))
  exact_stable_rational _ hr _ hτ _ hR n := B.norm_resolventStep_pow_le hr hτ hR n
  exact_rational _ hr _ hp _ hτ _ hR n _ hu := B.norm_resolventStep_pow_sub_S_le hr hp hτ hR n hu

end Feec.TimeStepping
