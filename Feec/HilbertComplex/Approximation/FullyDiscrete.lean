module

public import Feec.TimeStepping.BanachFEEC
public import Feec.HilbertComplex.Approximation.Ritz
public import Feec.HilbertComplex.Approximation.SkewFEEC
public import Feec.TimeStepping.BlockMatrix
public import Feec.TimeStepping.Leapfrog
public import Feec.TimeStepping.Trajectory
public import Feec.TimeStepping.Forced
public import Feec.Evolution.BoundaryLifting

/-!
# The fully discrete FEEC theorem

Time schemes for a dissipative FEEC discretization, power bounded and consistent uniformly in `h`:
the fully discrete solutions `ιₕ Pₕⁿ v` have the semidiscrete error plus a temporal error.

## Main results

* `dissipFEEC_fullyDiscrete`: the fully discrete FEEC theorem.
* `DissipFEEC.TimeScheme.norm_S_sub_sol_le_of_smooth`: from `v = pₕ(0)`, `O(hᵅ + τₕᵖ)`.
* `DissipFEEC.TimeScheme.norm_S_sub_sol_le_uniform`: from `v = pₕ(0)`, `O(hᵅ + τₕ^{p/(p+2)})`.
* `SkewFEEC.norm_crankNicolson_pow_apply`: energy conservation of Crank–Nicolson.
* `SkewFEEC.norm_S_sub_leapfrog_le`: explicit leapfrog under a CFL condition.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006]
* [M. F. Wheeler, *A priori L₂ error estimates for Galerkin approximations to parabolic partial differential equations*][Wheeler1973]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018]
* [P. Joly, *Variational Methods for Time-Dependent Wave Propagation Problems*][Joly2003]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

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

/-- A time scheme of `F`: power bounded one-step operators `Pₕ`, consistent uniformly in `h`. -/
abbrev TimeScheme := TimeStepping.TimeScheme F.L

/-- A dissipative FEEC discretization as a Banach FEEC discretization, with `M = 1`. -/
abbrev toBanachFEEC [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    TimeStepping.BanachFEEC.{u} F.isMDissipative.semigroup κ where
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

theorem norm_exp_le_one (h : κ) (t : ℝ) (ht : 0 ≤ t) : ‖exp ((t : 𝕜) • F.L h)‖ ≤ 1 :=
  TimeStepping.norm_exp_le_one (F.dissipative h) ht

variable {F}

/-- The **fully discrete solution** `ιₕ Pₕⁿ v` at the time level `tₙ = n τₕ`. -/
def TimeScheme.sol (Θ : F.TimeScheme) (h : κ) (v : F.X h) (n : ℕ) : E :=
  F.incl h ((Θ.P h ^ n) v)

/-- `Θ` is consistent of order `p` along trajectories with constant `K`, uniformly in `h`. -/
abbrev TimeScheme.IsTrajConsistent (Θ : F.TimeScheme) (K : ℝ) : Prop :=
  ∀ h, TimeStepping.IsTrajConsistent (F.L h) (Θ.P h) (Θ.τ h) Θ.p K

/-- A comparison smooth of order `q`: right derivatives `D j`, the `q`-th bounded by `B x`. -/
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

theorem norm_sol_le {T : ℝ} (h : κ) (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖Θ.sol h v n‖ ≤ ‖F.incl h‖ * Θ.M T * ‖v‖ := by
  rw [mul_assoc]
  refine ((F.incl h).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact ((Θ.P h ^ n).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (Θ.stable T h n hn) (norm_nonneg _))

theorem norm_exp_sub_pow_le {T : ℝ} (h : κ) (v w : F.X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖exp (((n * Θ.τ h : ℝ) : 𝕜) • F.L h) v - (Θ.P h ^ n) v‖ ≤
      (1 + Θ.M T) * ‖v - w‖ +
        Θ.M T * Θ.K * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(F.L h ^ (Θ.p + 1)) w‖ := by
  simpa using TimeStepping.TimeScheme.norm_exp_sub_pow_le Θ (F.norm_exp_le_one h) v w hn

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
theorem norm_sol_sub_sol_le {T : ℝ} (h : κ) (v : F.X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖F.sol h v (n * Θ.τ h) - Θ.sol h v n‖ ≤
      ‖F.incl h‖ * (Θ.M T * Θ.K * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(F.L h ^ (Θ.p + 1)) v‖) := by
  rw [DissipFEEC.sol, TimeScheme.sol, ← _root_.map_sub]
  refine ((F.incl h).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  have := Θ.norm_exp_sub_pow_le h v v hn
  simpa [DissipFEEC.group] using this

theorem norm_S_sub_sol_le {T : ℝ} (R : F.RateClass T) {x : E} (hx : x ∈ R.Data) (h : κ)
    (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T) :
    ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * (n * Θ.τ h)) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * ‖R.p x h 0 - v‖ +
        ‖F.incl h‖ * (Θ.M T * Θ.K * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(F.L h ^ (Θ.p + 1)) v‖) := by
  have h1 := dissipFEEC_rate F R hx h v hn
  have h2 := (TimeStepping.banachFEEC F.toBanachFEEC).rate_iterates Θ (F.S (n * Θ.τ h) x) h v hn.2
  rw [toBanachFEEC_M, mul_one] at h2
  exact h2.trans (add_le_add h1 le_rfl)

theorem converges (Z : F.Core) {x : E} (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h}
    (hv : F.Converges v x) (hτ : Tendsto Θ.τ F.l (𝓝 0)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in F.l, ∀ n : ℕ, (n : ℝ) * Θ.τ h ∈ Icc 0 T →
      ‖F.S (n * Θ.τ h) x - Θ.sol h (v h) n‖ < ε :=
  (TimeStepping.banachFEEC F.toBanachFEEC).converges_iterates Θ
    (fun T' => dissipFEEC_converges F Z T' hx hv) hτ T hε

theorem infDist_sol_le (hK : F.Keeps F.K) {x : E} (hxK : x ∈ F.K) (h : κ) (v : F.X h) (n : ℕ) :
    infDist (Θ.sol h v n) F.K ≤ ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖ := by
  rw [norm_sub_rev, ← dist_eq_norm]
  exact infDist_le_dist_of_mem (hK _ (mul_nonneg (Nat.cast_nonneg n) (Θ.τ_pos h).le) x hxK)

theorem residual_tendsto (hK : F.Keeps F.K) (Z : F.Core) {x : E} (hxK : x ∈ F.K)
    (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h} (hv : F.Converges v x)
    (hτ : Tendsto Θ.τ F.l (𝓝 0)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in F.l, ∀ n : ℕ, (n : ℝ) * Θ.τ h ∈ Icc 0 T → infDist (Θ.sol h (v h) n) F.K < ε := by
  filter_upwards [Θ.converges Z hx hv hτ T hε] with h hh n hn
  exact (Θ.infDist_sol_le hK hxK h (v h) n).trans_lt (hh n hn)

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
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

/-- **The fully discrete rate from static estimates**: for schemes consistent along trajectories and
smooth comparisons, from `v = pₕ(0)`, the spatial rate plus `O(τₕᵖ)`. [Thomee2006], Ch. 1, 7 -/
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

theorem _root_.Feec.HilbertComplex.DissipFEEC.RateClass.C'_mul_nonneg {T : ℝ} (R : F.RateClass T)
    (hT : 0 ≤ T) {x : E} (hx : x ∈ R.Data) (h : κ) :
    0 ≤ R.C' * (R.meshSize h ^ R.α * R.classNorm x) := by
  have := (norm_nonneg _).trans (R.consistency x hx h 0 ⟨le_rfl, hT⟩)
  rwa [mul_assoc] at this

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

/-- **The fully discrete rate for every datum of a rate class in `D(A)`**: from `v = pₕ(0)`, the
error is `O(hᵅ + τₕ^{p/(p+2)})`, uniformly in `h`. [BrennerThomee1979]; [Thomee2006], Ch. 7 -/
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

/-- The forced fully discrete solution `ιₕ Wₙ`: `W₀ = v`, `Wₙ₊₁ = Pₕ Wₙ + gₙ`. -/
def forcedSol (h : κ) (v : F.X h) (g : ℕ → F.X h) (n : ℕ) : E :=
  F.incl h (TimeStepping.forcedIter (Θ.P h) v g n)

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
@[simp] theorem forcedSol_zero_load (h : κ) (v : F.X h) (n : ℕ) :
    Θ.forcedSol h v 0 n = Θ.sol h v n := by
  simp [forcedSol, sol]

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
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

/-- The conclusions of the fully discrete FEEC theorem for the time scheme `Θ` and the core `Z`. -/
structure Verdict (Z : F.Core) : Prop extends toDissip : F.Verdict Z where
  /-- stability on every horizon `[0, T]` -/
  stable_iterates {T : ℝ} (h : κ) (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖Θ.sol h v n‖ ≤ ‖F.incl h‖ * Θ.M T * ‖v‖
  /-- the temporal error -/
  temporal_iterates {T : ℝ} (h : κ) (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖F.sol h v (n * Θ.τ h) - Θ.sol h v n‖ ≤
      ‖F.incl h‖ * (Θ.M T * Θ.K * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(F.L h ^ (Θ.p + 1)) v‖)
  /-- the spatial rate plus the temporal error -/
  rate_iterates {T : ℝ} (R : F.RateClass T) {x : E} (hx : x ∈ R.Data) (h : κ) (v : F.X h)
    {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T) : ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * (n * Θ.τ h)) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * ‖R.p x h 0 - v‖ +
        ‖F.incl h‖ * (Θ.M T * Θ.K * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(F.L h ^ (Θ.p + 1)) v‖)
  /-- convergence on the closure of the core as `τₕ → 0` -/
  converges_iterates {x : E} (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h}
    (hv : F.Converges v x) (hτ : Tendsto Θ.τ F.l (𝓝 0)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in F.l, ∀ n : ℕ, (n : ℝ) * Θ.τ h ∈ Icc 0 T →
      ‖F.S (n * Θ.τ h) x - Θ.sol h (v h) n‖ < ε
  /-- the residual of a kept constraint is at most the error -/
  residual_le_iterates (hK : F.Keeps F.K) {x : E} (hxK : x ∈ F.K) (h : κ) (v : F.X h) (n : ℕ) :
    infDist (Θ.sol h v n) F.K ≤ ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖
  /-- the residual of a kept constraint tends to `0` -/
  residual_tendsto_iterates (hK : F.Keeps F.K) {x : E} (hxK : x ∈ F.K)
    (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h} (hv : F.Converges v x)
    (hτ : Tendsto Θ.τ F.l (𝓝 0)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in F.l, ∀ n : ℕ, (n : ℝ) * Θ.τ h ∈ Icc 0 T → infDist (Θ.sol h (v h) n) F.K < ε
  /-- the rate along a smooth comparison -/
  rate_smooth_iterates {K : ℝ} (hΘ : Θ.IsTrajConsistent K) {T : ℝ} (R : F.RateClass T)
    (Sm : R.toComparison.Smooth (Θ.p + 1)) {x : E} (hx : x ∈ R.Data) (hxs : x ∈ Sm.Data) (h : κ)
    (v : F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T) :
    ‖F.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤ R.C * R.meshSize h ^ R.α * R.classNorm x +
      ‖F.incl h‖ * Θ.M T * (‖R.p x h 0 - v‖ +
        n * Θ.τ h * (K * Θ.τ h ^ Θ.p * Sm.B x + R.C' * R.meshSize h ^ R.α * R.classNorm x))
  /-- the rate for every datum of a rate class in `D(A)` -/
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
  /-- the error of forced iterates -/
  forced_iterates {T : ℝ} (h : κ) (v : F.X h) (g w : ℕ → F.X h) (y : E) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖y - Θ.forcedSol h v g n‖ ≤ ‖y - F.incl h (w n)‖ + ‖F.incl h‖ *
      (Θ.M T * (‖v - w 0‖ + ∑ k ∈ Finset.range n, ‖w (k + 1) - Θ.P h (w k) - g k‖))
  /-- the error of lifted iterates for inhomogeneous boundary data -/
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

/-- **The fully discrete FEEC theorem** `TimeScheme.Verdict` for an orbit-consistent core and a
time scheme. [BrennerThomee1979]; [Thomee2006], Ch. 7–9; [Arnold2018], Ch. 8 -/
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

/-- The θ-scheme `r_θ(τₕ Lₕ)`, `θ ≥ 1/2`: `M = 1`, order `1`, `K = θ + 1/2`. [Thomee2006], Ch. 7 -/
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

/-- Crank–Nicolson `Pₕ = cayley(Lₕ, τₕ/2)`: `M = 1`, order `2`, `K = 5/12`. [Thomee2006], Ch. 7 -/
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

theorem thetaScheme_isTrajConsistent {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ ≤ 1) {τ : κ → ℝ}
    (hτ : ∀ h, 0 < τ h) : (F.thetaScheme θ hθ τ hτ).IsTrajConsistent (θ + 1 / 2) := fun h =>
  TimeStepping.isTrajConsistent_thetaStep (F.dissipative h) (by linarith) hθ1 (hτ h)

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

/-- A Ritz projection `pₕ(t) = Rₕ ℓ(S(t) x)` is a smooth comparison. [Wheeler1973] -/
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
`‖Pₕⁿ v‖ = ‖v‖`. [QuennevilleBelair2015], Ch. 7 -/
theorem SkewFEEC.norm_crankNicolson_pow_apply [CompleteSpace E] {A : E →ₗ.[𝕜] E} {κ : Type*}
    (F : SkewFEEC.{u} A κ) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ) (v : F.X h) (n : ℕ) :
    ‖((F.crankNicolson τ hτ).P h ^ n) v‖ = ‖v‖ :=
  TimeStepping.norm_cayley_pow_apply
    ((F.L h).isSkewAdjoint_toPMap_top_iff.2 (C0Group.adjoint_eq_neg_of_skew (F.skew h))) _ n v

open Matrix in
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

/-- **Explicit leapfrog** for a skew FEEC discretization under the CFL condition `τ ‖Lₕ‖ ≤ c < 1`:
the semidiscrete rate plus `O(‖w₁ - e^{τ Lₕ} v‖ + tₙ τ² ‖Lₕ³ v‖)`. [Joly2003] -/
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
