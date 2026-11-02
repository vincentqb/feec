module

public import Feec.HilbertComplex.Approximation.BanachFEEC
public import Feec.HilbertComplex.Approximation.Ritz
public import Feec.HilbertComplex.Approximation.SkewFEEC
public import Feec.TimeStepping.BlockMatrix
public import Feec.TimeStepping.Leapfrog
public import Feec.TimeStepping.Trajectory
public import Feec.TimeStepping.Forced
public import Feec.Evolution.BoundaryLifting

/-!
# The fully discrete FEEC theorem

A semidiscrete FEEC discretization `F : DissipFEEC A κ` (discrete Hilbert spaces `Xₕ`, bounded
dissipative generators `Lₕ`, reading maps `ιₕ`) is made fully discrete by a **time scheme**
(`DissipFEEC.TimeScheme`, the time schemes `Feec.TimeStepping.TimeScheme` of the `Lₕ`): time steps
`τₕ > 0` and one-step operators `Pₕ` on `Xₕ`, power bounded by `M(T)` (`‖Pₕⁿ‖ ≤ M(T)` for
`n τₕ ≤ T`) and consistent of order `p` with constant `K` with the discrete flows,
`‖Pₕ y - e^{τₕ Lₕ} y‖ ≤ K τₕ^{p+1} ‖Lₕ^{p+1} y‖` (`TimeStepping.IsConsistent`), with `M`, `K`, `p`
independent of `h`. The fully discrete solution at `tₙ = n τₕ` is `ιₕ Pₕⁿ v` (`TimeScheme.sol`).
The scheme is any operator family: implicit (A-stable, unconditionally stable) or explicit (stable
under a CFL condition `τₕ ‖Lₕ‖ ≤ c`, which then enters through `τₕ`).

**The Banach layer is upstream.** Forgetting the inner products, `F` is a Banach FEEC
discretization with `M = 1` (`DissipFEEC.toBanachFEEC`: the Lumer–Phillips semigroup and the
flows of the dissipative `Lₕ` are contractions), and its time schemes are those of
`F.toBanachFEEC`. The rate 3 (semidiscrete rate plus temporal error) and the convergence 4 are
the fields `rate_iterates` and `converges_iterates` of the fully discrete FEEC theorem on Banach
spaces (`Feec.HilbertComplex.banachFEEC`) for `F.toBanachFEEC`, and the temporal errors of 2 and 7
are the Banach-space bounds `Feec.TimeStepping.TimeScheme.norm_exp_sub_pow_le` and
`Feec.TimeStepping.TimeScheme.norm_exp_sub_pow_le_of_timeAvg` at `‖e^{tLₕ}‖ ≤ 1`; the
semidiscrete inputs (the rate classes, the cores, `dissipFEEC_rate`, `dissipFEEC_converges`) are
Hilbert-space results.

## Main results

**`dissipFEEC_fullyDiscrete`** (statement `DissipFEEC.TimeScheme.Verdict`, extending the
semidiscrete `DissipFEEC.Verdict`): for every time scheme `Θ` of `F` and orbit-consistent core `Z`,
besides the semidiscrete conclusions, at the time levels `tₙ = n τₕ ≤ T`,

1. (**stability**) `‖ιₕ Pₕⁿ v‖ ≤ ‖ιₕ‖ M(T) ‖v‖`, uniformly in `h`;
2. (**temporal error**) `‖ιₕ e^{tₙ Lₕ} v - ιₕ Pₕⁿ v‖ ≤ ‖ιₕ‖ M(T) K tₙ τₕᵖ ‖Lₕ^{p+1} v‖`;
3. (**rate**) for data in a rate class, the error at `tₙ` is the spatial rate of the semidiscrete
   verdict plus the temporal error:
   `‖S(tₙ) x - ιₕ Pₕⁿ v‖ ≤ (C + ‖ιₕ‖ C' tₙ) hᵅ ‖x‖_c + ‖ιₕ‖ ‖pₕ(0) - v‖`
   `+ ‖ιₕ‖ M(T) K tₙ τₕᵖ ‖Lₕ^{p+1} v‖`;
4. (**convergence**, Lax–Brenner–Thomée) on the closure of the core, for every family
   `ιₕ vₕ → x` and `τₕ → 0`, the fully discrete solutions converge to `S(tₙ) x` uniformly over
   the time levels `tₙ ∈ [0, T]` (no smoothness of `vₕ`: the data are smoothed by time averages,
   `Feec.TimeStepping.timeAvg`);
5. (**constraint residual**) for a kept `K`, `dist(ιₕ Pₕⁿ v, K) ≤ ‖S(tₙ) x - ιₕ Pₕⁿ v‖`, so it is
   bounded by 3 and tends to `0` with 4;
6. (**rate from static estimates**, `TimeScheme.norm_S_sub_sol_le_of_smooth`) for a scheme
   consistent along trajectories (`TimeScheme.IsTrajConsistent`, constant `K`) and a rate class
   whose comparison is smooth of order `p + 1` (`DissipFEEC.Comparison.Smooth`: time derivatives
   `D j`, the `(p + 1)`-st bounded by `B x` uniformly in `h`),
   `‖S(tₙ) x - ιₕ Pₕⁿ v‖ ≤ C hᵅ ‖x‖_c + ‖ιₕ‖ M(T) (‖pₕ(0) - v‖ + tₙ (K τₕᵖ B x + C' hᵅ ‖x‖_c))`.
   The temporal term of 3, `‖Lₕ^{p+1} v‖`, is not uniform in `h` for the usual initial values
   (for an elliptic or heat Ritz projection `Lₕ Rₕ ≠ Rₕ A`, and `‖Lₕ‖ → ∞`); here the scheme is
   tested on the comparison trajectory instead (`norm_p_sub_pow_le`, the discrete Duhamel formula
   `TimeStepping.norm_sub_le_of_step` with the local errors of `TimeStepping.IsTrajConsistent`).
   **Ritz projections are smooth** (`DissipFEEC.Ritz.smooth`): `D j = Rₕ ℓ(S(t) Aʲ x)` on data
   with `Aʲ x` in the lift for `j ≤ p`, `B x = C sup ‖ℓ(S(t) A^{p+1} x)‖`; for the identity lift
   `B x = C ‖A^{p+1} x‖`, so the fully discrete error is `O(hᵅ + τₕᵖ)` in the graph norm of
   `D(A^{p+1})` from the static estimates of the Ritz projection alone.
7. (**rate for every datum, uniform in `h`**, `TimeScheme.norm_S_sub_sol_le_uniform`) for every
   time scheme (consistency in the sense of `TimeStepping.IsConsistent` suffices) and every datum
   `x ∈ D(A)` of a rate class, from `v = pₕ(0)`,
   `‖S(tₙ) x - ιₕ Pₕⁿ pₕ(0)‖ = O(hᵅ + τₕ^{p/(p+2)})` uniformly in `h`. The scheme is tested on the
   smoothed `A_δ^{p+1} pₕ(0)` (`TimeScheme.norm_exp_sub_pow_le_of_timeAvg`,
   `‖Lₕ^{p+1} A_δ^{p+1}‖ ≤ (2/δ)^{p+1}`), which is `O(hᵅ + δ ‖A x‖)`-close to `pₕ(0)` because the
   semidiscrete orbit from `pₕ(0)` is `O(hᵅ)`-close to the exact one
   (`TimeScheme.norm_S_sub_sol_le_of_timeAvg`); `δ = τₕ^{p/(p+2)}` balances `δ` against
   `τₕᵖ δ^{-(p+1)}`. The order in `τ` is not sharp: 6 gives `τₕᵖ` for smoother data.
8. (**forcing**, `TimeScheme.norm_sub_forcedSol_le`) the forced iterates `Wₙ₊₁ = Pₕ Wₙ + gₙ`
   (`TimeScheme.forcedSol`, `Feec.TimeStepping.forcedIter`) satisfy, for every target `y` and
   every comparison `wₖ`, `‖y - ιₕ Wₙ‖ ≤ ‖y - ιₕ wₙ‖ + ‖ιₕ‖ M(T) (‖v - w₀‖ + Σ_{k<n} ‖dₖ‖)`,
   `dₖ = wₖ₊₁ - Pₕ wₖ - gₖ` (the discrete Duhamel formula);
9. (**inhomogeneous boundary data**, `TimeScheme.norm_sub_lifted_le`) for `A ≤ A_max` and a
   lifting `G`, the solution with the boundary values of `G` is `G` plus the mild solution with
   the forcing `f - G' + A_max G` (`Feec.Evolution.IsBoundarySolution.eq_add_mild`), and the
   lifted iterates `Gₕ,ₙ + ιₕ Wₙ` have error at most `‖G(tₙ) - Gₕ,ₙ‖` plus the error of 8 for
   the mild solution. The Crank–Nicolson scheme with prescribed boundary DOFs of the thesis has
   the same structure, a forced Crank–Nicolson scheme of a compression
   (`Feec.TimeStepping.eq_add_forcedIter_of_isDirichletCNStep`); its identification with a
   time scheme of a conforming window is open.

   8 and 9 are stability statements against arbitrary comparisons: no consistency bound for a
   discretized load (e.g. `gₖ ≈ τ Πₕ f(tₖ)`) is proved, so forced problems carry no rate, fully
   discrete or semidiscrete.

**Schemes** (`DissipFEEC.thetaScheme`, `DissipFEEC.crankNicolson`): the θ-scheme, `θ ≥ 1/2` real,
`M = 1`, order `1`, `K = θ + 1/2` (implicit Euler `θ = 1`, `K = 3/2`), and Crank–Nicolson with
`Pₕ = cayley(Lₕ, τₕ/2)` literally (`Feec.TimeStepping.cayley`), `M = 1`, order `2`, `K = 5/12`; both
unconditionally stable (`TimeStepping.norm_thetaStep_le`); along trajectories
(`thetaScheme_isTrajConsistent`, `crankNicolson_isTrajConsistent`) the θ-scheme, `θ ≤ 1`, is
consistent of order `1` with `K = θ + 1/2` and Crank–Nicolson of order `2` with the sharp
`K = 1/12`. **Discrete constraint propagation**:
`thetaScheme_pow_mem`, `crankNicolson_pow_mem`: a closed subspace `Kₕ ⊆ Xₕ` with `Lₕ Kₕ ⊆ Kₕ` is
kept by every iterate. **Energy conservation**: for a skew FEEC discretization,
`SkewFEEC.norm_crankNicolson_pow_apply`: `‖Pₕⁿ v‖ = ‖v‖`. **The linear systems of
Crank–Nicolson**: in a basis of `Xₕ`, the iterate `Pₕ v` is the unique solution of the signed
system `diag(ε) (M + (τₕ/2) K) w = diag(ε) (M - (τₕ/2) K) c(v)` (Gram matrix `M`, stiffness `K`
of `Lₕ`; `DissipFEEC.crankNicolson_signed_mulVec_iff`), Hermitian for a skew discretization and
signs adapted to the basis, so MINRES solves it (`SkewFEEC.crankNicolson_signed`,
`Feec.TimeStepping.BlockMatrix`). **Explicit leapfrog** (a two-step scheme,
outside `TimeScheme`): `SkewFEEC.norm_S_sub_leapfrog_le` (any first step `u₁`) and
`SkewFEEC.norm_S_sub_leapfrog_euler_le` (`u₁ = v + τ Lₕ v`): under the CFL condition
`τ ‖Lₕ‖ ≤ c < 1` the error is the semidiscrete rate plus a second-order temporal error.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 1 (the
  Ritz projection of the exact solution as comparison), Ch. 7–9 (fully discrete schemes: spatial
  plus temporal error)
* [M. F. Wheeler, *A priori L₂ error estimates for Galerkin approximations to parabolic partial differential equations*][Wheeler1973]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 8 (time discretization of
  Hodge evolution problems)
* [P. Joly, *Variational Methods for Time-Dependent Wave Propagation Problems*][Joly2003]
  (leapfrog: discrete energy and CFL stability)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7 (Crank–Nicolson for the Einstein–Bianchi system)
* [C. C. Paige, M. A. Saunders, *Solution of sparse indefinite systems of linear equations*][PaigeSaunders1975]
  (MINRES)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology Metric NormedSpace

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace DissipFEEC

variable {A : E →ₗ.[𝕜] E} {κ : Type*} (F : DissipFEEC.{u} A κ)

/-- A **time scheme** for the dissipative FEEC discretization `F`: a time scheme
(`Feec.TimeStepping.TimeScheme`) of its discrete generators, i.e. time steps `τₕ > 0` and one-step
operators `Pₕ` on the discrete spaces, power bounded on every horizon `[0, T]` by `M T`
(`‖Pₕⁿ‖ ≤ M T` for `n τₕ ≤ T`, so quasi-contractive schemes, `M T = e^{ωT}`, are admitted) and
consistent of order `p ≥ 1` with constant `K` with the discrete flows `e^{τₕ Lₕ}`, all uniformly in
`h`; the same schemes as those of the Banach FEEC discretization `F.toBanachFEEC`.
[Thomee2006], Ch. 7 -/
abbrev TimeScheme := TimeStepping.TimeScheme F.L

/-- **A dissipative FEEC discretization is a Banach FEEC discretization**: forget the inner
products; the exact flow (Lumer–Phillips) and the discrete flows `e^{tLₕ}` (dissipative `Lₕ`) are
contractions, so `M = 1`. -/
abbrev toBanachFEEC [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    BanachFEEC.{u} F.isMDissipative.semigroup κ where
  l := F.l
  X := F.X
  L := F.L
  incl := F.incl
  proj := F.proj
  proj_incl := F.proj_incl
  bound := F.bound
  M := 1
  norm_S_le := F.isMDissipative.isContraction_semigroup
  norm_exp_le h _ ht := TimeStepping.norm_exp_le_one (F.dissipative h) ht

@[simp] theorem toBanachFEEC_M [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    F.toBanachFEEC.M = 1 := rfl

/-- `‖e^{tLₕ}‖ ≤ 1` for `t ≥ 0` (dissipative `Lₕ`). -/
theorem norm_exp_le_one (h : κ) (t : ℝ) (ht : 0 ≤ t) : ‖exp ((t : 𝕜) • F.L h)‖ ≤ 1 :=
  TimeStepping.norm_exp_le_one (F.dissipative h) ht

variable {F}

/-- The **fully discrete solution** `ιₕ Pₕⁿ v` at the time level `tₙ = n τₕ`. -/
def TimeScheme.sol (Θ : F.TimeScheme) (h : κ) (v : F.X h) (n : ℕ) : E :=
  F.incl h ((Θ.P h ^ n) v)

/-- The time scheme `Θ` is **consistent of order `p` along trajectories** with constant `K`,
uniformly in `h` (`TimeStepping.IsTrajConsistent`). -/
abbrev TimeScheme.IsTrajConsistent (Θ : F.TimeScheme) (K : ℝ) : Prop :=
  ∀ h, TimeStepping.IsTrajConsistent (F.L h) (Θ.P h) (Θ.τ h) Θ.p K

/-- A comparison `𝒞` on `[0, T]` is **smooth of order `q`** on the data `Data`: its trajectories
have right derivatives of every order `< q`, `D j` the `j`-th (`D 0 = pₕ`, `D 1 = pₕ'`), and the
`q`-th is bounded by `B x` uniformly in `h` and `t ∈ [0, T]`. -/
structure Comparison.Smooth {T : ℝ} (𝒞 : F.Comparison T) (q : ℕ) where
  /-- the smooth data -/
  Data : Set E
  /-- the time derivatives of the trajectories -/
  D : ℕ → E → ∀ h, ℝ → F.X h
  D_zero : ∀ x ∈ Data, ∀ h t, D 0 x h t = 𝒞.p x h t
  D_one : ∀ x ∈ Data, ∀ h t, D 1 x h t = 𝒞.p' x h t
  continuousOn : ∀ x ∈ Data, ∀ h, ∀ j < q, ContinuousOn (D j x h) (Icc 0 T)
  hasDerivWithinAt : ∀ x ∈ Data, ∀ h, ∀ j < q, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (D j x h) (D (j + 1) x h t) (Ici t) t
  /-- the bound of the `q`-th derivative -/
  B : E → ℝ
  bound : ∀ x ∈ Data, ∀ h, ∀ t ∈ Icc 0 T, ‖D q x h t‖ ≤ B x

/-- A smooth comparison stays smooth when restricted to part of its data. -/
def Comparison.Smooth.restrict {T : ℝ} {𝒞 : F.Comparison T} {q : ℕ} (Sm : 𝒞.Smooth q)
    (S : Set E) (hS : S ⊆ 𝒞.Data) : (𝒞.restrict S hS).Smooth q where
  Data := Sm.Data
  D := Sm.D
  D_zero := Sm.D_zero
  D_one := Sm.D_one
  continuousOn := Sm.continuousOn
  hasDerivWithinAt := Sm.hasDerivWithinAt
  B := Sm.B
  bound := Sm.bound

namespace TimeScheme

variable (Θ : F.TimeScheme)

/-- **1. Stability**: `‖ιₕ Pₕⁿ v‖ ≤ ‖ιₕ‖ M(T) ‖v‖` for `n τₕ ≤ T`. -/
theorem norm_sol_le {T : ℝ} (h : κ) (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖Θ.sol h v n‖ ≤ ‖F.incl h‖ * Θ.M T * ‖v‖ := by
  rw [mul_assoc]
  refine ((F.incl h).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact ((Θ.P h ^ n).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (Θ.stable T h n hn) (norm_nonneg _))

/-- The temporal error in `Xₕ` against any smoother datum `w`:
`‖e^{tₙ Lₕ} v - Pₕⁿ v‖ ≤ (1 + M(T)) ‖v - w‖ + M(T) K tₙ τₕᵖ ‖Lₕ^{p+1} w‖` (the contraction case,
`M_L = 1`, of `Feec.TimeStepping.TimeScheme.norm_exp_sub_pow_le`). -/
theorem norm_exp_sub_pow_le {T : ℝ} (h : κ) (v w : F.X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖exp (((n * Θ.τ h : ℝ) : 𝕜) • F.L h) v - (Θ.P h ^ n) v‖ ≤
      (1 + Θ.M T) * ‖v - w‖ +
        Θ.M T * Θ.K * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(F.L h ^ (Θ.p + 1)) w‖ := by
  simpa using TimeStepping.TimeScheme.norm_exp_sub_pow_le Θ (F.norm_exp_le_one h) v w hn

/-- **The temporal error of a slowly varying datum**: if `‖e^{sLₕ} u - u‖ ≤ η` for `s ∈ [0, δ]`,
then `‖e^{tₙ Lₕ} u - Pₕⁿ u‖ ≤ (1 + M(T)) (p + 1) η + M(T) K tₙ τₕᵖ (2/δ)^{p+1} ‖u‖` for `tₙ ≤ T`:
`u` is compared with the smoothed `A_δ^{p+1} u` (`TimeStepping.timeAvg`), so no power of `Lₕ`
enters (the contraction case of `Feec.TimeStepping.TimeScheme.norm_exp_sub_pow_le_of_timeAvg`).
[BrennerThomee1979] -/
theorem norm_exp_sub_pow_le_of_timeAvg {T δ η : ℝ} (h : κ) (u : F.X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) (hδ : 0 < δ)
    (hη : ∀ s ∈ Icc 0 δ, ‖exp ((s : 𝕜) • F.L h) u - u‖ ≤ η) :
    ‖exp (((n * Θ.τ h : ℝ) : 𝕜) • F.L h) u - (Θ.P h ^ n) u‖ ≤
      (1 + Θ.M T) * ((Θ.p + 1) * η) +
        Θ.M T * Θ.K * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ((2 / δ) ^ (Θ.p + 1) * ‖u‖) := by
  simpa [one_add_one_eq_two] using
    TimeStepping.TimeScheme.norm_exp_sub_pow_le_of_timeAvg Θ (F.norm_exp_le_one h) u hn hδ hη

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **2. The temporal error**: `‖ιₕ e^{tₙ Lₕ} v - ιₕ Pₕⁿ v‖ ≤ ‖ιₕ‖ M(T) K tₙ τₕᵖ ‖Lₕ^{p+1} v‖`
for `tₙ ≤ T` (the Banach-space bound `Feec.TimeStepping.TimeScheme.norm_exp_sub_pow_le` at
`‖e^{tLₕ}‖ ≤ 1`). [BrennerThomee1979] -/
theorem norm_sol_sub_sol_le {T : ℝ} (h : κ) (v : F.X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖F.sol h v (n * Θ.τ h) - Θ.sol h v n‖ ≤
      ‖F.incl h‖ * (Θ.M T * Θ.K * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(F.L h ^ (Θ.p + 1)) v‖) := by
  rw [DissipFEEC.sol, TimeScheme.sol, ← _root_.map_sub]
  refine ((F.incl h).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  have := Θ.norm_exp_sub_pow_le h v v hn
  simpa [DissipFEEC.group] using this

/-- **3. The fully discrete rate**: the spatial rate of the semidiscrete verdict plus the temporal
error, at every time level `tₙ ∈ [0, T]`. [Thomee2006], Ch. 7 -/
theorem norm_S_sub_sol_le {T : ℝ} (R : F.RateClass T) {x : E} (hx : x ∈ R.Data) (h : κ)
    (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T) :
    ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * (n * Θ.τ h)) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * ‖R.p x h 0 - v‖ +
        ‖F.incl h‖ * (Θ.M T * Θ.K * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(F.L h ^ (Θ.p + 1)) v‖) := by
  have h1 := dissipFEEC_rate F R hx h v hn
  have h2 := (banachFEEC F.toBanachFEEC).rate_iterates Θ (F.S (n * Θ.τ h) x) h v hn.2
  rw [toBanachFEEC_M, mul_one] at h2
  exact h2.trans (add_le_add h1 le_rfl)

/-- **4. Fully discrete convergence for every datum** (the Lax equivalence theorem in the
Brenner–Thomée form): on the closure of the core, for every family `ιₕ vₕ → x` and time steps
`τₕ → 0`, the fully discrete solutions converge to `S(tₙ) x`, uniformly over the time levels
`tₙ = n τₕ ∈ [0, T]`. No discrete smoothness of `vₕ` is assumed: `vₕ` is compared with the
smoothed `wₕ = A_δ^{p+1} vₕ` (`TimeStepping.timeAvg`), `‖Lₕ^{p+1} wₕ‖ ≤ (2/δ)^{p+1} ‖vₕ‖`, and
`‖vₕ - wₕ‖` is small uniformly in `h` because the semidiscrete orbits are uniformly continuous at
`0` (from the semidiscrete convergence and the stability `‖v‖ ≤ C ‖ιₕ v‖`): the Banach-space
theorem (`BanachFEEC.TimeScheme.converges`, field `converges_iterates` of `banachFEEC`) for
`F.toBanachFEEC`, with the semidiscrete convergence of `dissipFEEC_converges`.
[BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem converges (Z : F.Core) {x : E} (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h}
    (hv : F.Converges v x) (hτ : Tendsto Θ.τ F.l (𝓝 0)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in F.l, ∀ n : ℕ, (n : ℝ) * Θ.τ h ∈ Icc 0 T →
      ‖F.S (n * Θ.τ h) x - Θ.sol h (v h) n‖ < ε :=
  (banachFEEC F.toBanachFEEC).converges_iterates Θ
    (fun T' => dissipFEEC_converges F Z T' hx hv) hτ T hε

/-- **5. The constraint residual** of a kept `K` is at most the fully discrete error from any
`x ∈ K`. -/
theorem infDist_sol_le (hK : F.Keeps F.K) {x : E} (hxK : x ∈ F.K) (h : κ) (v : F.X h) (n : ℕ) :
    infDist (Θ.sol h v n) F.K ≤ ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖ := by
  rw [norm_sub_rev, ← dist_eq_norm]
  exact infDist_le_dist_of_mem (hK _ (mul_nonneg (Nat.cast_nonneg n) (Θ.τ_pos h).le) x hxK)

/-- **5. The constraint residual tends to `0`**: for a kept `K`, `x ∈ K` in the closure of the
core, `ιₕ vₕ → x` and `τₕ → 0`, `dist(ιₕ Pₕⁿ vₕ, K) → 0` uniformly over the time levels in
`[0, T]`. -/
theorem residual_tendsto (hK : F.Keeps F.K) (Z : F.Core) {x : E} (hxK : x ∈ F.K)
    (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h} (hv : F.Converges v x)
    (hτ : Tendsto Θ.τ F.l (𝓝 0)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in F.l, ∀ n : ℕ, (n : ℝ) * Θ.τ h ∈ Icc 0 T → infDist (Θ.sol h (v h) n) F.K < ε := by
  filter_upwards [Θ.converges Z hx hv hτ T hε] with h hh n hn
  exact (Θ.infDist_sol_le hK hxK h (v h) n).trans_lt (hh n hn)

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **The temporal error along a smooth comparison**: for a scheme consistent of order `p` along
trajectories with constant `K` and a comparison smooth of order `p + 1` with defect `≤ δ` on
`[0, T]`, `‖pₕ(tₙ) - Pₕⁿ v‖ ≤ M(T) (‖pₕ(0) - v‖ + tₙ (K τₕᵖ B x + δ))` for `tₙ ≤ T`: no power of
`Lₕ` enters, only the time derivatives of the comparison. [Thomee2006], Ch. 1 and 7 -/
theorem norm_p_sub_pow_le {K : ℝ} (hΘ : Θ.IsTrajConsistent K) {T : ℝ} {𝒞 : F.Comparison T}
    (Sm : 𝒞.Smooth (Θ.p + 1)) {x : E} (hx : x ∈ Sm.Data) (h : κ) (v : F.X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) {δ : ℝ} (hδ : ∀ t ∈ Icc 0 T, ‖𝒞.defect x h t‖ ≤ δ) :
    ‖𝒞.p x h (n * Θ.τ h) - (Θ.P h ^ n) v‖ ≤
      Θ.M T * (‖𝒞.p x h 0 - v‖ + n * Θ.τ h * (K * Θ.τ h ^ Θ.p * Sm.B x + δ)) := by
  have hτ := Θ.τ_pos h
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg n) hτ.le).trans hn
  have key := TimeStepping.norm_sub_le_of_step (P := Θ.P h) (U := fun k => (Θ.P h ^ k) v)
    (g := fun _ => 0) (w := fun k => 𝒞.p x h (k * Θ.τ h)) (Θ.stable_le h hn)
    (fun k => by rw [pow_succ', add_zero]; rfl)
  simp only [pow_zero, one_apply_eq_self, Nat.cast_zero, zero_mul, sub_zero] at key
  rw [norm_sub_rev]
  refine key.trans (mul_le_mul_of_nonneg_left (add_le_add (by rw [norm_sub_rev]) ?_)
    (Θ.M_nonneg hT h))
  have hstep : ∀ k ∈ Finset.range n, ‖𝒞.p x h ((k + 1 : ℕ) * Θ.τ h) - Θ.P h (𝒞.p x h (k * Θ.τ h))‖
      ≤ K * Θ.τ h ^ (Θ.p + 1) * Sm.B x + Θ.τ h * δ := fun k hk => by
    have hk0 : (0 : ℝ) ≤ k * Θ.τ h := mul_nonneg (Nat.cast_nonneg k) hτ.le
    have hk1 : (k : ℝ) * Θ.τ h + Θ.τ h ≤ T := by
      have : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Finset.mem_range.1 hk
      push_cast at this
      nlinarith
    have hIcc : Icc ((k : ℝ) * Θ.τ h) (k * Θ.τ h + Θ.τ h) ⊆ Icc 0 T := Icc_subset_Icc hk0 hk1
    have := hΘ h (fun j => Sm.D j x h) (k * Θ.τ h) (Sm.B x) δ
      (fun j hj => (Sm.continuousOn x hx h j (Nat.lt_succ_of_le hj)).mono hIcc)
      (fun j hj t ht => Sm.hasDerivWithinAt x hx h j (Nat.lt_succ_of_le hj) t
        ⟨hk0.trans ht.1, ht.2.trans_le hk1⟩)
      (fun t ht => Sm.bound x hx h t (hIcc (Ico_subset_Icc_self ht)))
      (fun t ht => by
        rw [Sm.D_one x hx, Sm.D_zero x hx]; exact hδ t (hIcc ht))
    rw [Sm.D_zero x hx, Sm.D_zero x hx] at this
    rwa [show ((k + 1 : ℕ) : ℝ) * Θ.τ h = k * Θ.τ h + Θ.τ h by push_cast; ring]
  refine (Finset.sum_le_sum hstep).trans_eq ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- **6. The fully discrete rate from static estimates**: for a scheme consistent of order `p`
along trajectories with constant `K` (`thetaScheme_isTrajConsistent`,
`crankNicolson_isTrajConsistent`) and a rate class whose comparison is smooth of order `p + 1`
(`Ritz.smooth`), at `tₙ ∈ [0, T]`,
`‖S(tₙ) x - ιₕ Pₕⁿ v‖ ≤ C hᵅ ‖x‖_c + ‖ιₕ‖ M(T) (‖pₕ(0) - v‖ + tₙ (K τₕᵖ B x + C' hᵅ ‖x‖_c))`:
`O(hᵅ + τₕᵖ)` uniformly in `h`, with no bound on `‖Lₕ^{p+1} v‖`. [Thomee2006], Ch. 1 and 7;
[Wheeler1973] -/
theorem norm_S_sub_sol_le_of_smooth {K : ℝ} (hΘ : Θ.IsTrajConsistent K) {T : ℝ}
    (R : F.RateClass T) (Sm : R.toComparison.Smooth (Θ.p + 1)) {x : E} (hx : x ∈ R.Data)
    (hxs : x ∈ Sm.Data) (h : κ) (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T) :
    ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤ R.C * R.meshSize h ^ R.α * R.classNorm x +
      ‖F.incl h‖ * Θ.M T * (‖R.p x h 0 - v‖ +
        n * Θ.τ h * (K * Θ.τ h ^ Θ.p * Sm.B x + R.C' * R.meshSize h ^ R.α * R.classNorm x)) := by
  have h1 := R.approx x hx h _ hn
  have h2 := Θ.norm_p_sub_pow_le hΘ Sm hxs h v hn.2 (fun t ht => R.consistency x hx h t ht)
  calc _ ≤ ‖F.S (n * Θ.τ h) x - F.incl h (R.p x h (n * Θ.τ h))‖ +
        ‖F.incl h (R.p x h (n * Θ.τ h)) - Θ.sol h v n‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      refine add_le_add h1 ?_
      rw [TimeScheme.sol, ← _root_.map_sub, mul_assoc]
      exact ((F.incl h).le_opNorm _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))

/-- The consistency bound of a rate class is nonnegative on its data. -/
theorem _root_.Feec.HilbertComplex.DissipFEEC.RateClass.C'_mul_nonneg {T : ℝ} (R : F.RateClass T)
    (hT : 0 ≤ T) {x : E} (hx : x ∈ R.Data) (h : κ) :
    0 ≤ R.C' * (R.meshSize h ^ R.α * R.classNorm x) := by
  have := (norm_nonneg _).trans (R.consistency x hx h 0 ⟨le_rfl, hT⟩)
  rwa [mul_assoc] at this

/-- **7. The fully discrete rate for every datum of a rate class in `D(A)`, by smoothing**: for
`0 < δ ≤ T` and `tₙ ∈ [0, T]`, with `e = hᵅ ‖x‖_c`, `C_F` the uniform bound of `F`
(`DissipFEEC.boundConst`) and `pₕ = pₕ(0)`,
`‖S(tₙ) x - ιₕ Pₕⁿ v‖ ≤ (C + ‖ιₕ‖ C' tₙ) e + ‖ιₕ‖ (M(T) ‖pₕ - v‖`
`+ (1 + M(T)) (p + 1) C_F ((2C + ‖ιₕ‖ C' δ) e + δ ‖A x‖) + M(T) K tₙ τₕᵖ (2/δ)^{p+1} ‖pₕ‖)`.
The scheme is tested on `A_δ^{p+1} pₕ` (`norm_exp_sub_pow_le_of_timeAvg`); the semidiscrete
orbit from `pₕ` moves by at most `C_F ((2C + ‖ιₕ‖ C' δ) e + δ ‖A x‖)` on `[0, δ]` because it is
`O(e)`-close to `S(s) x` and `‖S(s) x - x‖ ≤ s ‖A x‖`. Every term is uniform in `h`: no power
of `Lₕ` and no smoothness of the comparison enter. [BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem norm_S_sub_sol_le_of_timeAvg {T : ℝ} (R : F.RateClass T) {x : E} (hx : x ∈ R.Data)
    (hxA : x ∈ A.domain) (h : κ) (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T) {δ : ℝ}
    (hδ : 0 < δ) (hδT : δ ≤ T) :
    ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * (n * Θ.τ h)) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * (Θ.M T * ‖R.p x h 0 - v‖ +
          (1 + Θ.M T) * ((Θ.p + 1) * (F.boundConst *
            ((2 * R.C + ‖F.incl h‖ * R.C' * δ) * (R.meshSize h ^ R.α * R.classNorm x) +
              δ * ‖genExt A x‖))) +
          Θ.M T * Θ.K * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ((2 / δ) ^ (Θ.p + 1) * ‖R.p x h 0‖)) := by
  set u := R.p x h 0
  set e := R.meshSize h ^ R.α * R.classNorm x
  have hT : 0 ≤ T := hδ.le.trans hδT
  have hM := Θ.M_nonneg hT h
  have hι := norm_nonneg (F.incl h)
  have hC'e : 0 ≤ R.C' * e := R.C'_mul_nonneg hT hx h
  have hS0 : F.S 0 x = x := by rw [S_def, C0Semigroup.S_zero_apply]
  have hu : ‖x - F.incl h u‖ ≤ R.C * e := by
    have := R.approx x hx h 0 ⟨le_rfl, hT⟩
    rwa [hS0, mul_assoc] at this
  -- the semidiscrete orbit from `pₕ(0)` moves slowly on `[0, δ]`
  have hη : ∀ s ∈ Icc 0 δ, ‖exp ((s : 𝕜) • F.L h) u - u‖ ≤
      F.boundConst * ((2 * R.C + ‖F.incl h‖ * R.C' * δ) * e + δ * ‖genExt A x‖) := by
    intro s hs
    refine (F.norm_le_norm_incl h _).trans (mul_le_mul_of_nonneg_left ?_ F.boundConst_nonneg)
    have a1 := dissipFEEC_rate F R hx h u ⟨hs.1, hs.2.trans hδT⟩
    rw [sub_self, norm_zero, mul_zero, add_zero] at a1
    have a2 : ‖F.S s x - x‖ ≤ s * ‖genExt A x‖ := by
      have := LumerPhillips.norm_lpS_sub_le_of_le F.isMDissipative ⟨x, hxA⟩ le_rfl hs.1
      rwa [LumerPhillips.lpS_zero, sub_zero, ← genExt_of_mem hxA] at this
    have e1 : F.incl h (exp ((s : 𝕜) • F.L h) u - u) =
        -(F.S s x - F.sol h u s) + (F.S s x - x) + (x - F.incl h u) := by
      rw [_root_.map_sub, show F.sol h u s = F.incl h (exp ((s : 𝕜) • F.L h) u) from rfl]; abel
    rw [e1]
    refine (norm_add₃_le).trans ?_
    rw [norm_neg]
    have b1 : ‖F.incl h‖ * R.C' * s * e ≤ ‖F.incl h‖ * R.C' * δ * e := by
      have := mul_le_mul_of_nonneg_left hs.2 (mul_nonneg hι hC'e)
      linarith
    have b2 := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg (genExt A x))
    nlinarith
  have h1 := dissipFEEC_rate F R hx h u hn
  rw [sub_self, norm_zero, mul_zero, add_zero] at h1
  have h2 := Θ.norm_exp_sub_pow_le_of_timeAvg h u hn.2 hδ hη
  have h3 : ‖(Θ.P h ^ n) (u - v)‖ ≤ Θ.M T * ‖u - v‖ :=
    ((Θ.P h ^ n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (Θ.stable T h n hn.2) (norm_nonneg _))
  have e2 : F.S (n * Θ.τ h) x - Θ.sol h v n = (F.S (n * Θ.τ h) x - F.sol h u (n * Θ.τ h)) +
      F.incl h (exp (((n * Θ.τ h : ℝ) : 𝕜) • F.L h) u - (Θ.P h ^ n) u + (Θ.P h ^ n) (u - v)) := by
    rw [_root_.map_add, _root_.map_sub, _root_.map_sub (Θ.P h ^ n), TimeScheme.sol,
      show F.sol h u (n * Θ.τ h) = F.incl h (exp (((n * Θ.τ h : ℝ) : 𝕜) • F.L h) u) from rfl]
    simp only [_root_.map_sub]
    abel
  rw [e2]
  refine (norm_add_le _ _).trans (add_le_add h1 ?_)
  refine ((F.incl h).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ hι)
  refine (norm_add_le _ _).trans ?_
  linarith

/-- **7. The fully discrete rate, uniform in `h`, for every datum of a rate class in `D(A)`**:
`norm_S_sub_sol_le_of_timeAvg` at `δ = τₕ^θ`, `θ = p/(p + 2)`: for `τₕ^θ ≤ T` and
`tₙ ∈ [0, T]`, with `e = hᵅ ‖x‖_c` and `pₕ = pₕ(0)`,
`‖S(tₙ) x - ιₕ Pₕⁿ v‖ ≤ (C + ‖ιₕ‖ C' tₙ) e + ‖ιₕ‖ (M(T) ‖pₕ - v‖`
`+ (1 + M(T)) (p + 1) C_F (2C + ‖ιₕ‖ C' T) e`
`+ τₕ^θ ((1 + M(T)) (p + 1) C_F ‖A x‖ + M(T) K tₙ 2^{p+1} ‖pₕ‖))`,
so `O(hᵅ + τₕ^{p/(p+2)})` uniformly in `h` from `v = pₕ(0)` (`‖ιₕ‖ ≤ C_F`, `‖pₕ(0)‖` is bounded
by `C_F (‖x‖ + C e)`): for every time scheme, with no smoothness beyond `x ∈ D(A)`. The order
`p/(p + 2)` is not sharp. [BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem norm_S_sub_sol_le_uniform {T : ℝ} (R : F.RateClass T) {x : E} (hx : x ∈ R.Data)
    (hxA : x ∈ A.domain) (h : κ) (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T)
    (hτT : Θ.τ h ^ ((Θ.p : ℝ) / (Θ.p + 2)) ≤ T) :
    ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * (n * Θ.τ h)) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * (Θ.M T * ‖R.p x h 0 - v‖ +
          (1 + Θ.M T) * (Θ.p + 1) * F.boundConst * (2 * R.C + ‖F.incl h‖ * R.C' * T) *
            (R.meshSize h ^ R.α * R.classNorm x) +
          Θ.τ h ^ ((Θ.p : ℝ) / (Θ.p + 2)) * ((1 + Θ.M T) * (Θ.p + 1) * F.boundConst *
            ‖genExt A x‖ + Θ.M T * Θ.K * (n * Θ.τ h) * 2 ^ (Θ.p + 1) * ‖R.p x h 0‖)) := by
  set θ : ℝ := (Θ.p : ℝ) / (Θ.p + 2)
  set δ := Θ.τ h ^ θ
  have hτ := Θ.τ_pos h
  have hδ : 0 < δ := Real.rpow_pos_of_pos hτ θ
  have hT : 0 ≤ T := hδ.le.trans hτT
  have key := Θ.norm_S_sub_sol_le_of_timeAvg R hx hxA h v hn hδ hτT
  -- `τᵖ (2/δ)^{p+1} = 2^{p+1} τ^θ`
  have hpow : Θ.τ h ^ Θ.p * (2 / δ) ^ (Θ.p + 1) = 2 ^ (Θ.p + 1) * δ := by
    have hp2 : (Θ.p : ℝ) + 2 ≠ 0 := by positivity
    have e : (Θ.p : ℝ) = θ * (Θ.p + 1 : ℕ) + θ := by
      simp only [θ]; push_cast; field_simp; ring
    rw [div_pow, ← Real.rpow_natCast (Θ.τ h) Θ.p, ← Real.rpow_natCast δ, ← Real.rpow_mul hτ.le,
      e, Real.rpow_add hτ]
    field_simp
    rfl
  have hC'e := R.C'_mul_nonneg hT hx h
  have hM := Θ.M_nonneg hT h
  have hι := norm_nonneg (F.incl h)
  have hF := F.boundConst_nonneg
  refine key.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hι))
  have b1 : ‖F.incl h‖ * R.C' * δ * (R.meshSize h ^ R.α * R.classNorm x) ≤
      ‖F.incl h‖ * R.C' * T * (R.meshSize h ^ R.α * R.classNorm x) := by
    have := mul_le_mul_of_nonneg_left hτT (mul_nonneg hι hC'e)
    linarith
  have b2 := mul_le_mul_of_nonneg_left b1
    (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + Θ.M T) (by positivity : (0 : ℝ) ≤ Θ.p + 1)) hF)
  have e3 : Θ.M T * Θ.K * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ((2 / δ) ^ (Θ.p + 1) * ‖R.p x h 0‖) =
      Θ.M T * Θ.K * (n * Θ.τ h) * ‖R.p x h 0‖ * (Θ.τ h ^ Θ.p * (2 / δ) ^ (Θ.p + 1)) := by ring
  rw [e3, hpow]
  nlinarith

/-- The **forced fully discrete solution** `ιₕ Wₙ`: the forced iterates `W₀ = v`,
`Wₙ₊₁ = Pₕ Wₙ + gₙ` (`TimeStepping.forcedIter`) of the scheme with the load `g`. -/
def forcedSol (h : κ) (v : F.X h) (g : ℕ → F.X h) (n : ℕ) : E :=
  F.incl h (TimeStepping.forcedIter (Θ.P h) v g n)

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- Without load, the forced solution is the fully discrete solution. -/
@[simp] theorem forcedSol_zero_load (h : κ) (v : F.X h) (n : ℕ) :
    Θ.forcedSol h v 0 n = Θ.sol h v n := by
  simp [forcedSol, sol]

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **8. Forced iterates**: for every target `y` (the exact value at `tₙ`) and every comparison
sequence `wₖ` in `Xₕ`,
`‖y - ιₕ Wₙ‖ ≤ ‖y - ιₕ wₙ‖ + ‖ιₕ‖ M(T) (‖v - w₀‖ + Σ_{k<n} ‖wₖ₊₁ - Pₕ wₖ - gₖ‖)` for
`tₙ ≤ T` (the discrete Duhamel formula, `TimeStepping.norm_forcedIter_sub_le`). This is
stability only: the load `g` is arbitrary, and no consistency bound ties it to a forcing.
[Thomee2006], Ch. 8 -/
theorem norm_sub_forcedSol_le {T : ℝ} (h : κ) (v : F.X h) (g w : ℕ → F.X h) (y : E) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖y - Θ.forcedSol h v g n‖ ≤ ‖y - F.incl h (w n)‖ + ‖F.incl h‖ *
      (Θ.M T * (‖v - w 0‖ + ∑ k ∈ Finset.range n, ‖w (k + 1) - Θ.P h (w k) - g k‖)) := by
  have h1 := TimeStepping.norm_forcedIter_sub_le (v := v) (g := g) (Θ.stable_le h hn) w
  have h2 : ‖F.incl h (w n) - Θ.forcedSol h v g n‖ ≤
      ‖F.incl h‖ * ‖TimeStepping.forcedIter (Θ.P h) v g n - w n‖ := by
    rw [forcedSol, ← _root_.map_sub, norm_sub_rev]
    exact (F.incl h).le_opNorm _
  calc ‖y - Θ.forcedSol h v g n‖
      ≤ ‖y - F.incl h (w n)‖ + ‖F.incl h (w n) - Θ.forcedSol h v g n‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by gcongr; exact h2.trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))

/-- **9. Inhomogeneous boundary data**: for `A ≤ A_max`, a lifting `G` (`G' = DG`,
`A_max G = AG`) on `[0, T]` and a solution `U` of `U' = A_max U + f` with the boundary values of
`G` and continuous `f - G' + A_max G`, the lifted iterates `Gₕ,ₙ + ιₕ Wₙ` (any discrete lifting
`Gₕ,ₙ`, `Wₙ` forced by `g`) satisfy
`‖U(tₙ) - (Gₕ,ₙ + ιₕ Wₙ)‖ ≤ ‖G(tₙ) - Gₕ,ₙ‖ + (forced error of 8)` for the mild solution
`U - G = S(·)(U(0) - G(0)) + ∫₀^· S(· - s)(f - G' + A_max G)(s) ds`
(`Feec.Evolution.IsBoundarySolution.eq_add_mild`). [QuennevilleBelair2015], Ch. 7 -/
theorem norm_sub_lifted_le {Amax : E →ₗ.[𝕜] E} (hle : A ≤ Amax) {T : ℝ} {G DG AG f U : ℝ → E}
    (hG : Evolution.IsLifting Amax (Icc 0 T) G DG AG)
    (hU : Evolution.IsBoundarySolution Amax A (Icc 0 T) f G U)
    (hc : ContinuousOn (f - DG + AG) (Icc 0 T)) (h : κ) (Gh : ℕ → E) (v : F.X h)
    (g w : ℕ → F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T) :
    ‖U (n * Θ.τ h) - (Gh n + Θ.forcedSol h v g n)‖ ≤ ‖G (n * Θ.τ h) - Gh n‖ +
      (‖Evolution.mild F.S 0 (U 0 - G 0) (f - DG + AG) (n * Θ.τ h) - F.incl h (w n)‖ +
        ‖F.incl h‖ * (Θ.M T * (‖v - w 0‖ +
          ∑ k ∈ Finset.range n, ‖w (k + 1) - Θ.P h (w k) - g k‖))) := by
  rw [hU.eq_add_mild F.isMDissipative.semigroup F.isMDissipative.generator_semigroup hle hG hc _
    hn, add_sub_add_comm]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (Θ.norm_sub_forcedSol_le h v g w _ hn.2))

/-- The conclusions of the fully discrete FEEC theorem (`dissipFEEC_fullyDiscrete`) for the
time scheme `Θ` and the core `Z`: the semidiscrete verdict, and stability, temporal error, rate,
convergence and constraint residuals of the iterates `ιₕ Pₕⁿ v`, and their rate along smooth
comparisons and, uniformly in `h`, for every datum of a rate class in `D(A)`; the error of
forced iterates and of lifted iterates for inhomogeneous boundary data. -/
structure Verdict (Z : F.Core) : Prop extends toDissip : F.Verdict Z where
  /-- the iterates are stable on every horizon `[0, T]` -/
  stable_iterates {T : ℝ} (h : κ) (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖Θ.sol h v n‖ ≤ ‖F.incl h‖ * Θ.M T * ‖v‖
  /-- the temporal error against the semidiscrete solution -/
  temporal_iterates {T : ℝ} (h : κ) (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖F.sol h v (n * Θ.τ h) - Θ.sol h v n‖ ≤
      ‖F.incl h‖ * (Θ.M T * Θ.K * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(F.L h ^ (Θ.p + 1)) v‖)
  /-- the fully discrete rate: spatial rate plus temporal error -/
  rate_iterates {T : ℝ} (R : F.RateClass T) {x : E} (hx : x ∈ R.Data) (h : κ) (v : F.X h)
    {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T) : ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * (n * Θ.τ h)) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * ‖R.p x h 0 - v‖ +
        ‖F.incl h‖ * (Θ.M T * Θ.K * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(F.L h ^ (Θ.p + 1)) v‖)
  /-- convergence over the time levels in `[0, T]` for every convergent family, as `τₕ → 0` -/
  converges_iterates {x : E} (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h}
    (hv : F.Converges v x) (hτ : Tendsto Θ.τ F.l (𝓝 0)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in F.l, ∀ n : ℕ, (n : ℝ) * Θ.τ h ∈ Icc 0 T →
      ‖F.S (n * Θ.τ h) x - Θ.sol h (v h) n‖ < ε
  /-- the residual of a kept constraint is at most the fully discrete error -/
  residual_le_iterates (hK : F.Keeps F.K) {x : E} (hxK : x ∈ F.K) (h : κ) (v : F.X h) (n : ℕ) :
    infDist (Θ.sol h v n) F.K ≤ ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖
  /-- the residual of a kept constraint tends to `0` over the time levels in `[0, T]` -/
  residual_tendsto_iterates (hK : F.Keeps F.K) {x : E} (hxK : x ∈ F.K)
    (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h} (hv : F.Converges v x)
    (hτ : Tendsto Θ.τ F.l (𝓝 0)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in F.l, ∀ n : ℕ, (n : ℝ) * Θ.τ h ∈ Icc 0 T → infDist (Θ.sol h (v h) n) F.K < ε
  /-- the fully discrete rate along a smooth comparison: spatial rate plus `O(τₕᵖ)`, uniformly -/
  rate_smooth_iterates {K : ℝ} (hΘ : Θ.IsTrajConsistent K) {T : ℝ} (R : F.RateClass T)
    (Sm : R.toComparison.Smooth (Θ.p + 1)) {x : E} (hx : x ∈ R.Data) (hxs : x ∈ Sm.Data) (h : κ)
    (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T) :
    ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤ R.C * R.meshSize h ^ R.α * R.classNorm x +
      ‖F.incl h‖ * Θ.M T * (‖R.p x h 0 - v‖ +
        n * Θ.τ h * (K * Θ.τ h ^ Θ.p * Sm.B x + R.C' * R.meshSize h ^ R.α * R.classNorm x))
  /-- the fully discrete rate for every datum of a rate class in `D(A)`: spatial rate plus
  `O(τₕ^{p/(p+2)})`, uniformly in `h`, for every time scheme -/
  rate_uniform_iterates {T : ℝ} (R : F.RateClass T) {x : E} (hx : x ∈ R.Data)
    (hxA : x ∈ A.domain) (h : κ) (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T)
    (hτT : Θ.τ h ^ ((Θ.p : ℝ) / (Θ.p + 2)) ≤ T) :
    ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * (n * Θ.τ h)) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * (Θ.M T * ‖R.p x h 0 - v‖ +
          (1 + Θ.M T) * (Θ.p + 1) * F.boundConst * (2 * R.C + ‖F.incl h‖ * R.C' * T) *
            (R.meshSize h ^ R.α * R.classNorm x) +
          Θ.τ h ^ ((Θ.p : ℝ) / (Θ.p + 2)) * ((1 + Θ.M T) * (Θ.p + 1) * F.boundConst *
            ‖genExt A x‖ + Θ.M T * Θ.K * (n * Θ.τ h) * 2 ^ (Θ.p + 1) * ‖R.p x h 0‖))
  /-- the forced iterates `Wₙ₊₁ = Pₕ Wₙ + gₙ` against every comparison sequence: the comparison
  error plus the stability constant times the initial and the summed consistency errors
  (stability only; no rate for a discretized load) -/
  forced_iterates {T : ℝ} (h : κ) (v : F.X h) (g w : ℕ → F.X h) (y : E) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖y - Θ.forcedSol h v g n‖ ≤ ‖y - F.incl h (w n)‖ + ‖F.incl h‖ *
      (Θ.M T * (‖v - w 0‖ + ∑ k ∈ Finset.range n, ‖w (k + 1) - Θ.P h (w k) - g k‖))
  /-- inhomogeneous boundary data: the solution is the lifting plus the mild solution with the
  forcing `f - G' + A_max G`, and the lifted iterates have the lifting error plus the forced
  error -/
  lifted_iterates {Amax : E →ₗ.[𝕜] E} (hle : A ≤ Amax) {T : ℝ} {G DG AG f U : ℝ → E}
    (hG : Evolution.IsLifting Amax (Icc 0 T) G DG AG)
    (hU : Evolution.IsBoundarySolution Amax A (Icc 0 T) f G U)
    (hc : ContinuousOn (f - DG + AG) (Icc 0 T)) (h : κ) (Gh : ℕ → E) (v : F.X h)
    (g w : ℕ → F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T) :
    ‖U (n * Θ.τ h) - (Gh n + Θ.forcedSol h v g n)‖ ≤ ‖G (n * Θ.τ h) - Gh n‖ +
      (‖Evolution.mild F.S 0 (U 0 - G 0) (f - DG + AG) (n * Θ.τ h) - F.incl h (w n)‖ +
        ‖F.incl h‖ * (Θ.M T * (‖v - w 0‖ +
          ∑ k ∈ Finset.range n, ‖w (k + 1) - Θ.P h (w k) - g k‖)))

end TimeScheme

/-- **The fully discrete FEEC theorem.** For a dissipative FEEC discretization `F` with an
orbit-consistent core `Z` and a time scheme `Θ` (power bounded by `M(T)` on `[0, T]`, consistent
of order `p ≥ 1` with constant `K`, uniformly in `h`): the semidiscrete verdict holds, and the
iterates `ιₕ Pₕⁿ v` are stable, have temporal error `‖ιₕ‖ M(T) K tₙ τₕᵖ ‖Lₕ^{p+1} v‖`, converge at
the spatial rate plus the temporal error, converge on the closure of the core for every
convergent family as `τₕ → 0`, and have constraint residuals bounded by the error and tending to
`0`; for schemes consistent along trajectories and smooth comparisons, the rate is
`O(hᵅ + τₕᵖ)` uniformly in `h`, and for every scheme and every datum of a rate class in `D(A)` it
is `O(hᵅ + τₕ^{p/(p+2)})` uniformly in `h`; forced iterates have the comparison error plus the
summed consistency defects, and inhomogeneous boundary data reduce to forcing by a lifting.
[BrennerThomee1979]; [Thomee2006], Ch. 7–9; [Arnold2018],
Ch. 8 -/
theorem _root_.Feec.HilbertComplex.dissipFEEC_fullyDiscrete [CompleteSpace E] [NormedSpace ℝ E]
    [IsScalarTower ℝ 𝕜 E] (Z : F.Core) (Θ : F.TimeScheme) : Θ.Verdict Z where
  toDissip := dissipFEEC F Z
  stable_iterates := fun h v _ hn => Θ.norm_sol_le h v hn
  temporal_iterates := fun h v _ hn => Θ.norm_sol_sub_sol_le h v hn
  rate_iterates := fun R _ hx h v _ hn => Θ.norm_S_sub_sol_le R hx h v hn
  converges_iterates := fun hx _ hv hτ T _ hε => Θ.converges Z hx hv hτ T hε
  residual_le_iterates := fun hK _ hxK h v n => Θ.infDist_sol_le hK hxK h v n
  residual_tendsto_iterates := fun hK _ hxK hx _ hv hτ T _ hε =>
    Θ.residual_tendsto hK Z hxK hx hv hτ T hε
  rate_smooth_iterates := fun hΘ _ R Sm _ hx hxs h v _ hn =>
    Θ.norm_S_sub_sol_le_of_smooth hΘ R Sm hx hxs h v hn
  rate_uniform_iterates := fun R _ hx hxA h v _ hn hτT =>
    Θ.norm_S_sub_sol_le_uniform R hx hxA h v hn hτT
  forced_iterates := fun h v g w y _ hn => Θ.norm_sub_forcedSol_le h v g w y hn
  lifted_iterates := fun hle _ _ _ _ _ _ hG hU hc h Gh v g w _ hn =>
    Θ.norm_sub_lifted_le hle hG hU hc h Gh v g w hn

/-! ### θ-schemes and Crank–Nicolson -/

variable (F)

/-- **The θ-scheme** (`θ ≥ 1/2` real) as a time scheme: `Pₕ = r_θ(τₕ Lₕ)`, unconditionally
stable (`M = 1`), order `1` with `K = θ + 1/2`; `θ = 1` is implicit Euler.
[Thomee2006], Ch. 7 -/
def thetaScheme (θ : ℝ) (hθ : 1 / 2 ≤ θ) (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) : F.TimeScheme where
  τ := τ
  τ_pos := hτ
  P h := TimeStepping.thetaStep ((F.L h : F.X h →ₗ[𝕜] F.X h).toPMap ⊤) θ (τ h)
  M _ := 1
  stable _ h n _ :=
    TimeStepping.norm_thetaStep_pow_le (F.dissipative h) (by simpa using hθ) (hτ h) n
  p := 1
  p_pos := one_pos
  K := θ + 1 / 2
  K_nonneg := by linarith
  consistent h := TimeStepping.isConsistent_thetaStep (F.dissipative h) (by linarith) (hτ h)

/-- **Crank–Nicolson** as a time scheme: `Pₕ = cayley(Lₕ, τₕ/2)` (`Feec.TimeStepping.cayley`),
unconditionally stable (`M = 1`), order `2` with `K = 5/12`. [QuennevilleBelair2015], Ch. 7;
[Thomee2006], Ch. 7 -/
def crankNicolson (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) : F.TimeScheme where
  τ := τ
  τ_pos := hτ
  P h := TimeStepping.cayley ((F.L h : F.X h →ₗ[𝕜] F.X h).toPMap ⊤) (τ h / 2)
  M _ := 1
  stable _ h n _ := by
    rw [TimeStepping.cayley_half_eq_thetaStep]
    exact TimeStepping.norm_thetaStep_pow_le (F.dissipative h)
      (by rw [RCLike.ofReal_re]) (hτ h) n
  p := 2
  p_pos := two_pos
  K := 5 / 12
  K_nonneg := by norm_num
  consistent h := by
    rw [TimeStepping.cayley_half_eq_thetaStep]
    exact TimeStepping.isConsistent_thetaStep_half (F.dissipative h) (hτ h)

/-- **Discrete constraint propagation for the θ-scheme**: a closed subspace `Kₕ ⊆ Xₕ` with
`Lₕ Kₕ ⊆ Kₕ` is kept by every iterate `Pₕⁿ`. [QuennevilleBelair2015], Prop 4.18 -/
theorem thetaScheme_pow_mem {θ : ℝ} (hθ : 1 / 2 ≤ θ) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ)
    {Kh : Submodule 𝕜 (F.X h)} (hKc : IsClosed (Kh : Set (F.X h)))
    (hLK : ∀ x ∈ Kh, F.L h x ∈ Kh) {v : F.X h} (hv : v ∈ Kh) (n : ℕ) :
    ((F.thetaScheme θ hθ τ hτ).P h ^ n) v ∈ Kh := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ']
    exact TimeStepping.thetaStep_mem_of_mapsTo (F.dissipative h) hKc hLK
      (by rw [RCLike.ofReal_re]; linarith) (hτ h) ih

/-- **Discrete constraint propagation for Crank–Nicolson**: a closed subspace `Kₕ ⊆ Xₕ` with
`Lₕ Kₕ ⊆ Kₕ` is kept by every iterate. [QuennevilleBelair2015], Prop 4.18 -/
theorem crankNicolson_pow_mem {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ)
    {Kh : Submodule 𝕜 (F.X h)} (hKc : IsClosed (Kh : Set (F.X h)))
    (hLK : ∀ x ∈ Kh, F.L h x ∈ Kh) {v : F.X h} (hv : v ∈ Kh) (n : ℕ) :
    ((F.crankNicolson τ hτ).P h ^ n) v ∈ Kh := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ']
    change TimeStepping.cayley _ (τ h / 2) _ ∈ Kh
    rw [TimeStepping.cayley_half_eq_thetaStep]
    exact TimeStepping.thetaStep_mem_of_mapsTo (F.dissipative h) hKc hLK
      (by rw [RCLike.ofReal_re]; norm_num) (hτ h) ih

/-- **The θ-scheme is consistent of order `1` along trajectories** (`1/2 ≤ θ ≤ 1`) with constant
`θ + 1/2`, uniformly in `h`. [Thomee2006], Ch. 1 -/
theorem thetaScheme_isTrajConsistent {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ ≤ 1) {τ : κ → ℝ}
    (hτ : ∀ h, 0 < τ h) : (F.thetaScheme θ hθ τ hτ).IsTrajConsistent (θ + 1 / 2) := fun h =>
  TimeStepping.isTrajConsistent_thetaStep (F.dissipative h) (by linarith) hθ1 (hτ h)

/-- **Crank–Nicolson is consistent of order `2` along trajectories** with constant `1/12`,
uniformly in `h`. [Thomee2006], Ch. 1 -/
theorem crankNicolson_isTrajConsistent {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) :
    (F.crankNicolson τ hτ).IsTrajConsistent (1 / 12) := fun h => by
  change TimeStepping.IsTrajConsistent _ (TimeStepping.cayley _ (τ h / 2)) _ 2 _
  rw [TimeStepping.cayley_half_eq_thetaStep]
  exact TimeStepping.isTrajConsistent_thetaStep_half (F.dissipative h) (hτ h)

/-! ### Ritz projections are smooth comparisons -/

section Ritz

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G] [IsScalarTower ℝ 𝕜 G]
  {F} {Λ : F.Lift G}

/-- **A Ritz projection is a smooth comparison**: on data `S` whose iterates `Aʲ x`, `j < q`, are
data of the lift, the trajectory `pₕ(t) = Rₕ ℓ(S(t) x)` has the right derivatives
`Rₕ ℓ(S(t) Aʲ x)`, and with `‖Rₕ‖ ≤ C` and `‖ℓ(S(t) A^q x)‖ ≤ B x` on `[0, T]` the `q`-th is
bounded by `C B x`, uniformly in `h`. For the identity lift (`Lift.ofDomain`), `S = D(A^q)` and
`B x = ‖A^q x‖` (`S(t)` is a contraction, `norm_S_apply_le`): the temporal error of
`TimeScheme.norm_S_sub_sol_le_of_smooth` is `K τₕᵖ C ‖A^{p+1} x‖`. [Wheeler1973] -/
def Ritz.smooth (𝓡 : F.Ritz Λ) (T : ℝ) (q : ℕ) (S : Set E)
    (hS : ∀ x ∈ S, ∀ j < q, (genExt A)^[j] x ∈ Λ.Data) {C : ℝ} (hC : ∀ h, ‖𝓡.R h‖ ≤ C)
    (B : E → ℝ) (hB : ∀ x ∈ S, ∀ t ∈ Icc 0 T, ‖Λ.lift (F.S t ((genExt A)^[q] x))‖ ≤ B x) :
    (𝓡.cmp T).Smooth q where
  Data := S
  D j x h t := 𝓡.R h (Λ.lift (F.S t ((genExt A)^[j] x)))
  D_zero _ _ _ _ := rfl
  D_one _ _ _ _ := rfl
  continuousOn x hx h j hj := (𝓡.R h).continuous.comp_continuousOn
    ((Λ.continuousOn _ (hS x hx j hj)).mono Icc_subset_Ici_self)
  hasDerivWithinAt x hx h j hj t ht := by
    have hd := Λ.hasDerivWithinAt _ (hS x hx j hj) t ht.1
    rw [← Function.iterate_succ_apply' (genExt A)] at hd
    exact ((𝓡.R h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hd
  B x := C * B x
  bound x hx h t ht := ((𝓡.R h).le_opNorm _).trans
    (mul_le_mul (hC h) (hB x hx t ht) (norm_nonneg _) ((norm_nonneg _).trans (hC h)))

end Ritz

end DissipFEEC

/-- **Energy conservation of fully discrete Crank–Nicolson** for a skew FEEC discretization:
`‖Pₕⁿ v‖ = ‖v‖` (the Cayley transform of the skew `Lₕ` is unitary, `norm_cayley_pow_apply`).
[QuennevilleBelair2015], Ch. 7 -/
theorem SkewFEEC.norm_crankNicolson_pow_apply [CompleteSpace E] {A : E →ₗ.[𝕜] E} {κ : Type*}
    (F : SkewFEEC.{u} A κ) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ) (v : F.X h) (n : ℕ) :
    ‖((F.crankNicolson τ hτ).P h ^ n) v‖ = ‖v‖ :=
  TimeStepping.norm_cayley_pow_apply
    ((F.L h).isSkewAdjoint_toPMap_top_iff.2 (C0Group.adjoint_eq_neg_of_skew (F.skew h))) _ n v

open Matrix in
/-- **The Crank–Nicolson iterate in a basis**: for a basis `b` of `Xₕ` (finite-dimensional), with
Gram (mass) matrix `M`, the stiffness `K` of `Lₕ` (`TimeStepping.stiffness`, `M c' = -K c` for
`ξₕ' = Lₕ ξₕ`) and signs `ε i = ±1`, the signed system
`diag(ε) (M + (τₕ/2) K) w = diag(ε) (M - (τₕ/2) K) c(v)` has the coefficients of the iterate
`Pₕ v` of `DissipFEEC.crankNicolson` as its unique solution. [QuennevilleBelair2015], Ch. 7 -/
theorem DissipFEEC.crankNicolson_signed_mulVec_iff {A : E →ₗ.[𝕜] E} {κ : Type*}
    (F : DissipFEEC.{u} A κ) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ) {n : Type*} [Fintype n]
    [DecidableEq n] (b : Module.Basis n 𝕜 (F.X h)) (ε : n → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (v : F.X h) (w : n → 𝕜) :
    (Matrix.diagonal (fun i => (ε i : 𝕜)) * (Matrix.gram 𝕜 b +
          ((τ h / 2 : ℝ) : 𝕜) • TimeStepping.stiffness b (F.L h))) *ᵥ w =
        (Matrix.diagonal (fun i => (ε i : 𝕜)) * (Matrix.gram 𝕜 b -
          ((τ h / 2 : ℝ) : 𝕜) • TimeStepping.stiffness b (F.L h))) *ᵥ b.equivFun v ↔
      w = b.equivFun ((F.crankNicolson τ hτ).P h v) := by
  have hA := (F.L h).isMDissipative_toPMap_top (F.dissipative h)
  have hs : 0 < τ h / 2 := half_pos (hτ h)
  have hP : TimeStepping.IsCNStep _ (τ h / 2) v ((F.crankNicolson τ hτ).P h v) :=
    TimeStepping.isCNStep_cayley (hA.isResolvent_of_re_pos (by
      rw [← RCLike.ofReal_inv, RCLike.ofReal_re]; positivity)) hs.ne' v
  rw [TimeStepping.diagonal_mul_mulVec_iff_isCNStep b _ _ _ fun i => by exact_mod_cast hε i]
  refine ⟨fun hw => ?_, fun hw => hw ▸ by simpa using hP⟩
  rw [← hw.unique hA.dissipative hs.le hP, LinearEquiv.apply_symm_apply]

open Matrix in
/-- **MINRES for fully discrete Crank–Nicolson** of a skew FEEC discretization: for a basis `b`
of `Xₕ` and signs `ε i = ±1` such that basis functions of different signs are orthogonal and
`Lₕ` couples only basis functions of opposite signs (a basis adapted to the parity of the form
degree, `Lₕ = dₕ - dₕ*`), the signed matrix `diag(ε) (M + (τₕ/2) K)` is Hermitian and the
coefficients of the iterate `Pₕ v` are the unique solution of its system
(`TimeStepping.isHermitian_signed_cn`, `DissipFEEC.crankNicolson_signed_mulVec_iff`).
[QuennevilleBelair2015], Ch. 7; [PaigeSaunders1975] -/
theorem SkewFEEC.crankNicolson_signed [CompleteSpace E] {A : E →ₗ.[𝕜] E} {κ : Type*}
    (F : SkewFEEC.{u} A κ) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ) {n : Type*} [Fintype n]
    [DecidableEq n] (b : Module.Basis n 𝕜 (F.X h)) (ε : n → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (hMε : ∀ i j, ⟪b i, b j⟫_𝕜 ≠ 0 → ε i = ε j)
    (hKε : ∀ i j, ⟪b i, F.L h (b j)⟫_𝕜 ≠ 0 → ε i = -ε j) (v : F.X h) :
    (Matrix.diagonal (fun i => (ε i : 𝕜)) * (Matrix.gram 𝕜 b +
        ((τ h / 2 : ℝ) : 𝕜) • TimeStepping.stiffness b (F.L h))).IsHermitian ∧
      ∀ w, (Matrix.diagonal (fun i => (ε i : 𝕜)) * (Matrix.gram 𝕜 b +
          ((τ h / 2 : ℝ) : 𝕜) • TimeStepping.stiffness b (F.L h))) *ᵥ w =
        (Matrix.diagonal (fun i => (ε i : 𝕜)) * (Matrix.gram 𝕜 b -
          ((τ h / 2 : ℝ) : 𝕜) • TimeStepping.stiffness b (F.L h))) *ᵥ b.equivFun v ↔
      w = b.equivFun ((F.crankNicolson τ hτ).P h v) :=
  ⟨TimeStepping.isHermitian_signed_cn b (F.skew h) ε hMε hKε _,
    F.toDissipFEEC.crankNicolson_signed_mulVec_iff hτ h b ε hε v⟩

/-- **Explicit leapfrog for a skew FEEC discretization, under the CFL condition**
`τ ‖Lₕ‖ ≤ c < 1` (on finite element spaces `‖Lₕ‖ ≲ h⁻¹`, so `τ ≲ h`): with `u₀ = v` and any
first step `u₁`, the error at `tₙ = n τ ∈ [0, T]` is the semidiscrete rate plus
`‖ιₕ‖ (√(1 + c) ‖u₁ - e^{τ Lₕ} v‖ / √(1 - c) + tₙ τ² ‖Lₕ³ v‖ / (3 (1 - c)))`. [Joly2003] -/
theorem SkewFEEC.norm_S_sub_leapfrog_le [CompleteSpace E] [NormedSpace ℝ E]
    [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E} {κ : Type*} (F : SkewFEEC.{u} A κ) {T : ℝ}
    (R : F.RateClass T) {x : E} (hx : x ∈ R.Data) (h : κ) (v : F.X h) {τ c : ℝ} (hτ : 0 ≤ τ)
    (hc : τ * ‖F.L h‖ ≤ c) (hc1 : c < 1) {w : ℕ → F.X h}
    (hw : TimeStepping.IsLeapfrog (F.L h) τ w) (h0 : w 0 = v) {n : ℕ}
    (hn : (n : ℝ) * τ ∈ Icc 0 T) :
    ‖F.S (n * τ) x - F.incl h (w n)‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * (n * τ)) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * ‖R.p x h 0 - v‖ +
        ‖F.incl h‖ * (√(1 + c) * ‖w 1 - exp ((τ : 𝕜) • F.L h) v‖ / √(1 - c) +
          n * τ * τ ^ 2 * ‖(F.L h ^ 3) v‖ / (3 * (1 - c))) := by
  have hr := dissipFEEC_rate F.toDissipFEEC R hx h v hn
  have hl := TimeStepping.norm_leapfrog_sub_exp_le (F.skew h) hτ hc hc1 hw v n
  rw [h0, sub_self, norm_zero, zero_pow two_ne_zero, zero_add] at hl
  have hc0 : 0 ≤ c := (mul_nonneg hτ (norm_nonneg _)).trans hc
  rw [Real.sqrt_mul (by linarith), Real.sqrt_sq (norm_nonneg _)] at hl
  have hs : 0 < √(1 - c) := Real.sqrt_pos.2 (by linarith)
  have hss : √(1 - c) * √(1 - c) = 1 - c := Real.mul_self_sqrt (by linarith)
  set d := ‖w 1 - exp ((τ : 𝕜) • F.L h) v‖
  set b := n * τ * τ ^ 2 * ‖(F.L h ^ 3) v‖
  have ht : ‖w n - exp (((n * τ : ℝ) : 𝕜) • F.L h) v‖ ≤ √(1 + c) * d / √(1 - c) +
      b / (3 * (1 - c)) := by
    have hE : ‖w n - exp (((n * τ : ℝ) : 𝕜) • F.L h) v‖ ≤
        (√(1 + c) * d + b / (3 * √(1 - c))) / √(1 - c) := by
      rw [le_div_iff₀ hs]; linarith
    refine hE.trans_eq ?_
    rw [show 3 * (1 - c) = 3 * (√(1 - c) * √(1 - c)) by rw [hss]]
    field_simp
  have hsol : F.sol h v (n * τ) = F.incl h (exp (((n * τ : ℝ) : 𝕜) • F.L h) v) := rfl
  calc ‖F.S (n * τ) x - F.incl h (w n)‖ ≤ ‖F.S (n * τ) x - F.sol h v (n * τ)‖ +
        ‖F.sol h v (n * τ) - F.incl h (w n)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      refine add_le_add hr ?_
      rw [hsol, ← _root_.map_sub]
      refine ((F.incl h).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rwa [norm_sub_rev]

/-- **Leapfrog started by one forward Euler step** `u₁ = v + τ Lₕ v` (the practical start, local
error `τ²/2 ‖Lₕ² v‖`): under the CFL condition `τ ‖Lₕ‖ ≤ c < 1` the error at `tₙ ∈ [0, T]` is the
semidiscrete rate plus `‖ιₕ‖ (√(1 + c) τ² ‖Lₕ² v‖ / (2 √(1 - c)) + tₙ τ² ‖Lₕ³ v‖ / (3 (1 - c)))`:
second order. [Joly2003] -/
theorem SkewFEEC.norm_S_sub_leapfrog_euler_le [CompleteSpace E] [NormedSpace ℝ E]
    [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E} {κ : Type*} (F : SkewFEEC.{u} A κ) {T : ℝ}
    (R : F.RateClass T) {x : E} (hx : x ∈ R.Data) (h : κ) (v : F.X h) {τ c : ℝ} (hτ : 0 ≤ τ)
    (hc : τ * ‖F.L h‖ ≤ c) (hc1 : c < 1) {w : ℕ → F.X h}
    (hw : TimeStepping.IsLeapfrog (F.L h) τ w) (h0 : w 0 = v)
    (h1 : w 1 = v + (τ : 𝕜) • F.L h v) {n : ℕ} (hn : (n : ℝ) * τ ∈ Icc 0 T) :
    ‖F.S (n * τ) x - F.incl h (w n)‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * (n * τ)) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * ‖R.p x h 0 - v‖ +
        ‖F.incl h‖ * (√(1 + c) * (τ ^ 2 / 2 * ‖(F.L h ^ 2) v‖) / √(1 - c) +
          n * τ * τ ^ 2 * ‖(F.L h ^ 3) v‖ / (3 * (1 - c))) := by
  have hd : ‖w 1 - exp ((τ : 𝕜) • F.L h) v‖ ≤ τ ^ 2 / 2 * ‖(F.L h ^ 2) v‖ := by
    have := TimeStepping.norm_exp_sub_taylor_le (F.dissipative h) 2 hτ v
    have e : ∑ j ∈ Finset.range 2, (τ ^ j / j.factorial) • (F.L h ^ j) v =
        v + (τ : 𝕜) • F.L h v := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp only [pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
        div_one, one_smul, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
      rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    rw [e, show ((2 : ℕ).factorial : ℝ) = 2 by norm_num [Nat.factorial]] at this
    rwa [norm_sub_rev, h1]
  refine (F.norm_S_sub_leapfrog_le R hx h v hτ hc hc1 hw h0 hn).trans ?_
  gcongr


end Feec.HilbertComplex
