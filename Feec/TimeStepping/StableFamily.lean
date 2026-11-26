module

public import Feec.TimeStepping.TimeScheme
public import Feec.TimeStepping.Trajectory
public import Feec.TimeStepping.RationalHillePhillipsReal
public import Feec.ForMathlib.Analysis.SubMarkov

/-!
# Uniformly stable families of bounded generators

Families of bounded generators with flows bounded uniformly in `h`: semidiscrete and temporal errors
of time schemes, backward Euler and A-stable rational schemes, with constants independent of `h`.

## Main results

* `StableFamily.norm_sub_res_pow_le_of_traj`: backward Euler along a `C²` trajectory.
* `StableFamily.norm_step_pow_le`: the stability bound `‖r(τLₕ)ⁿ‖ ≤ M (1 + C'_r √n)` for A-stable
  `r` and `τ > 0`.
* `StableFamily.norm_step_pow_sub_exp_le`: the temporal error of A-stable rational schemes.
* `stableFamily`: the fully discrete theorem for uniformly stable families.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [A. Gomilko, Y. Tomilov, *Rational Approximation of Operator Semigroups via the B-Calculus*][GomilkoTomilov2024],
  Thm 1.1
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.5

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter Topology NormedSpace Finset

@[expose] public noncomputable section

universe u

namespace Feec.TimeStepping

/-! ### Duhamel's formula for bounded generators -/

section Duhamel

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

/-- `ℚ`-algebra structure on operators, for the continuity of `NormedSpace.exp`. -/
local instance instNormedAlgebraRatStableFamily : NormedAlgebra ℚ (X →L[𝕜] X) :=
  NormedAlgebra.restrictScalars ℚ 𝕜 _

theorem norm_sub_exp_apply_le_of_defect {L : X →L[𝕜] X} {M : ℝ}
    (hL : ∀ s : ℝ, 0 ≤ s → ‖exp ((s : 𝕜) • L)‖ ≤ M) {U U' : ℝ → X} {t D : ℝ} (ht : 0 ≤ t)
    (hU : ∀ s ∈ Icc 0 t, HasDerivAt U (U' s) s) (hD : ∀ s ∈ Icc 0 t, ‖U' s - L (U s)‖ ≤ D)
    (v : X) : ‖U t - exp ((t : 𝕜) • L) v‖ ≤ M * ‖U 0 - v‖ + M * t * D := by
  set f : ℝ → X := fun r => exp (((t - r : ℝ) : 𝕜) • L) (U r)
  have hf : ∀ r ∈ Icc 0 t, HasDerivAt f (exp (((t - r : ℝ) : 𝕜) • L) (U' r - L (U r))) r :=
    fun r hr => L.hasDerivAt_exp_sub_smul_apply t (hU r hr)
  have hb : ∀ r ∈ Ico 0 t, ‖exp (((t - r : ℝ) : 𝕜) • L) (U' r - L (U r))‖ ≤ M * D := fun r hr =>
    ((exp (((t - r : ℝ) : 𝕜) • L)).le_opNorm _).trans (mul_le_mul (hL _ (sub_nonneg.2 hr.2.le))
      (hD r (Ico_subset_Icc_self hr)) (norm_nonneg _)
      ((norm_nonneg _).trans (hL 0 le_rfl)))
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := 0) (b := t)
    (fun r hr => (hf r hr).hasDerivWithinAt) hb t ⟨ht, le_rfl⟩
  have hft : f t = U t := by simp [f]
  have hf0 : f 0 = exp ((t : 𝕜) • L) (U 0) := by simp [f]
  rw [hft, hf0, sub_zero] at hmvt
  have e : U t - exp ((t : 𝕜) • L) v =
      (U t - exp ((t : 𝕜) • L) (U 0)) + exp ((t : 𝕜) • L) (U 0 - v) := by
    rw [_root_.map_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h2 := (exp ((t : 𝕜) • L)).le_of_opNorm_le (hL t ht) (U 0 - v)
  linarith

end Duhamel

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A uniformly stable family: Banach spaces `Xₕ`, bounded `Lₕ`, `‖e^{tLₕ}‖ ≤ M` for `t ≥ 0`. -/
structure StableFamily (𝕜 : Type*) [RCLike 𝕜] (κ : Type*) where
  /-- the discrete spaces -/
  X : κ → Type u
  [normedAddCommGroup : ∀ h, NormedAddCommGroup (X h)]
  [normedSpace : ∀ h, NormedSpace 𝕜 (X h)]
  [completeSpace : ∀ h, CompleteSpace (X h)]
  [normedSpaceReal : ∀ h, NormedSpace ℝ (X h)]
  [isScalarTower : ∀ h, IsScalarTower ℝ 𝕜 (X h)]
  /-- the discrete generators -/
  L : ∀ h, X h →L[𝕜] X h
  /-- the bound of the discrete semigroups -/
  M : ℝ
  M_nonneg : 0 ≤ M
  norm_exp_le : ∀ h (t : ℝ), 0 ≤ t → ‖exp ((t : 𝕜) • L h)‖ ≤ M

attribute [instance] StableFamily.normedAddCommGroup StableFamily.normedSpace
  StableFamily.completeSpace StableFamily.normedSpaceReal StableFamily.isScalarTower

namespace StableFamily

/-- **The family of sub-Markov generators** on `ℝ^{ι h}` with the maximum norm, with `M = 1`. -/
abbrev ofSubMarkov {κ : Type*} (ι : κ → Type) [∀ h, Fintype (ι h)]
    (L : ∀ h, (ι h → ℝ) →L[ℝ] (ι h → ℝ)) (hL : ∀ h, IsSubMarkovGenerator (L h)) :
    StableFamily ℝ κ where
  X h := ι h → ℝ
  L := L
  M := 1
  M_nonneg := zero_le_one
  norm_exp_le h t ht := by simpa using (hL h).norm_exp_smul_le_one ht

variable {κ : Type*} (F : StableFamily.{u} 𝕜 κ)

/-- A time scheme of `F`: a time scheme of its generators. -/
abbrev TimeScheme := TimeStepping.TimeScheme F.L

/-- The discrete semigroups `e^{tLₕ}`. -/
abbrev discrete (h : κ) : C0Semigroup 𝕜 (F.X h) := (C0Group.ofBounded (F.L h)).toC0Semigroup

theorem norm_discrete_S_le (h : κ) (t : ℝ) (ht : 0 ≤ t) : ‖(F.discrete h).S t‖ ≤ F.M :=
  F.norm_exp_le h t ht

theorem norm_discrete_S_le_exp (h : κ) (t : ℝ) (ht : 0 ≤ t) :
    ‖(F.discrete h).S t‖ ≤ F.M * Real.exp (0 * t) := by
  simpa using F.norm_discrete_S_le h t ht

/-! ### Trajectories -/

theorem norm_sub_exp_le_of_defect (h : κ) {U U' : ℝ → F.X h} {t D : ℝ} (ht : 0 ≤ t)
    (hU : ∀ s ∈ Icc 0 t, HasDerivAt U (U' s) s) (hD : ∀ s ∈ Icc 0 t, ‖U' s - F.L h (U s)‖ ≤ D)
    (v : F.X h) : ‖U t - exp ((t : 𝕜) • F.L h) v‖ ≤ F.M * ‖U 0 - v‖ + F.M * t * D :=
  norm_sub_exp_apply_le_of_defect (F.norm_exp_le h) ht hU hD v

theorem TimeScheme.norm_sub_pow_le {F : StableFamily.{u} 𝕜 κ} (Θ : F.TimeScheme) {T : ℝ}
    (h : κ) (v : F.X h) (W : ℕ → F.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖W n - (Θ.P h ^ n) v‖ ≤
      Θ.M T * (‖W 0 - v‖ + ∑ k ∈ range n, ‖W (k + 1) - Θ.P h (W k)‖) := by
  have H := norm_sub_le_of_step (P := Θ.P h) (U := fun k => (Θ.P h ^ k) v) (g := fun _ => 0)
    (w := W) (Θ.stable_le h hn) (fun k => by simp [pow_succ'])
  simp only [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, sub_zero] at H
  rw [norm_sub_rev (W n), norm_sub_rev (W 0)]
  exact H

/-! ### Backward Euler and the rational schemes -/

/-- **The discrete resolvent** `Rₕ = (1 - τLₕ)⁻¹ = τ⁻¹ (τ⁻¹ - Lₕ)⁻¹`. -/
def res (τ : ℝ) (h : κ) : F.X h →L[𝕜] F.X h :=
  (τ : 𝕜)⁻¹ • Operator.resolvent (F.discrete h).generator (τ : 𝕜)⁻¹

theorem res_apply_sub {τ : ℝ} (hτ : 0 < τ) (h : κ) :
    ∀ x y, (x, y) ∈ (F.discrete h).generator.graph → F.res τ h (x - (τ : 𝕜) • y) = x := by
  intro x y hxy
  have hR := (F.discrete h).isResolvent_resolvent_ofReal (F.norm_discrete_S_le_exp h)
    (inv_pos.2 hτ)
  rw [RCLike.ofReal_inv] at hR
  exact hR.inv_smul_apply_sub hτ.ne' hxy

theorem res_apply_sub_apply {τ : ℝ} (hτ : 0 < τ) (h : κ) (x : F.X h) :
    F.res τ h (x - (τ : 𝕜) • F.L h x) = x :=
  F.res_apply_sub hτ h x _ (C0Group.mem_graph_generator_ofBounded (F.L h) x)

theorem res_sub_smul_apply_res {τ : ℝ} (hτ : 0 < τ) (h : κ) (x : F.X h) :
    F.res τ h x - (τ : 𝕜) • F.L h (F.res τ h x) = x := by
  have hR := (F.discrete h).isResolvent_resolvent_ofReal (F.norm_discrete_S_le_exp h)
    (inv_pos.2 hτ)
  rw [RCLike.ofReal_inv] at hR
  have hτ' : (τ : 𝕜) ≠ 0 := by exact_mod_cast hτ.ne'
  have e := hR.sub_apply x
  have hA : ∀ y : (F.discrete h).generator.domain, (F.discrete h).generator y = F.L h y :=
    C0Group.generator_ofBounded_apply (F.L h)
  rw [hA] at e
  rw [res, _root_.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hτ', one_smul]
  exact e

theorem norm_res_pow_le {τ : ℝ} (hτ : 0 < τ) (h : κ) (n : ℕ) : ‖F.res τ h ^ n‖ ≤ F.M := by
  simpa using TimeStepping.norm_pow_le_of_generator (F.discrete h) (F.norm_discrete_S_le_exp h)
    hτ (by simp) (F.res_apply_sub hτ h) n

theorem norm_sub_res_apply_le {τ : ℝ} (hτ : 0 < τ) (h : κ) {U U₁ U₂ : ℝ → F.X h} {a B D : ℝ}
    (hU : ∀ s ∈ Icc a (a + τ), HasDerivAt U (U₁ s) s)
    (hU₁ : ∀ s ∈ Icc a (a + τ), HasDerivAt U₁ (U₂ s) s) (hB : ∀ s ∈ Icc a (a + τ), ‖U₂ s‖ ≤ B)
    (hD : ‖U₁ (a + τ) - F.L h (U (a + τ))‖ ≤ D) :
    ‖U (a + τ) - F.res τ h (U a)‖ ≤ F.M * (3 / 2 * τ ^ 2 * B + τ * D) := by
  have hq := norm_sub_sub_smul_le hτ.le hU hU₁ hB
  have e : U (a + τ) - F.res τ h (U a) = F.res τ h ((U (a + τ) - U a - τ • U₁ (a + τ)) +
      τ • (U₁ (a + τ) - F.L h (U (a + τ)))) := by
    have h1 := F.res_apply_sub_apply hτ h (U (a + τ))
    rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜)] at h1
    have e2 : (U (a + τ) - U a - τ • U₁ (a + τ)) + τ • (U₁ (a + τ) - F.L h (U (a + τ))) =
        (U (a + τ) - τ • F.L h (U (a + τ))) - U a := by
      rw [smul_sub]; abel
    rw [e2, _root_.map_sub, h1]
  rw [e]
  refine ((F.res τ h).le_opNorm _).trans ?_
  have hR : ‖F.res τ h‖ ≤ F.M := by simpa using F.norm_res_pow_le hτ h 1
  refine mul_le_mul hR ((norm_add_le _ _).trans ?_) (norm_nonneg _) F.M_nonneg
  rw [norm_smul, Real.norm_of_nonneg hτ.le]
  gcongr

/-- **Backward Euler along a `C²` trajectory** (`τ > 0`, `‖U''‖ ≤ B`, defect `D`;
[Thomee2006], Ch. 1): `‖U(nτ) - Rₕⁿ v‖ ≤ M ‖U(0) - v‖ + M² nτ (3/2 τ B + D)`. -/
theorem norm_sub_res_pow_le_of_traj {τ : ℝ} (hτ : 0 < τ) (h : κ) {U U₁ U₂ : ℝ → F.X h}
    {n : ℕ} {B D : ℝ} (hU : ∀ s ∈ Icc 0 (n * τ), HasDerivAt U (U₁ s) s)
    (hU₁ : ∀ s ∈ Icc 0 (n * τ), HasDerivAt U₁ (U₂ s) s) (hB : ∀ s ∈ Icc 0 (n * τ), ‖U₂ s‖ ≤ B)
    (hD : ∀ s ∈ Icc 0 (n * τ), ‖U₁ s - F.L h (U s)‖ ≤ D) (v : F.X h) :
    ‖U (n * τ) - (F.res τ h ^ n) v‖ ≤
      F.M * ‖U 0 - v‖ + F.M ^ 2 * (n * τ) * (3 / 2 * τ * B + D) := by
  have H := norm_sub_le_of_step (P := F.res τ h) (U := fun k => (F.res τ h ^ k) v)
    (g := fun _ => 0) (w := fun k => U (k * τ)) (fun k _ => F.norm_res_pow_le hτ h k)
    (n := n) (fun k => by simp [pow_succ'])
  simp only [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, sub_zero,
    Nat.cast_zero, zero_mul] at H
  have hk : ∀ k ∈ range n, ‖U ((k + 1 : ℕ) * τ) - F.res τ h (U (k * τ))‖ ≤
      F.M * (3 / 2 * τ ^ 2 * B + τ * D) := by
    intro k hk
    have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast mem_range.1 hk
    have hI : Icc ((k : ℝ) * τ) (k * τ + τ) ⊆ Icc 0 (n * τ) := Icc_subset_Icc (by positivity)
      (by nlinarith)
    have e : ((k + 1 : ℕ) : ℝ) * τ = k * τ + τ := by push_cast; ring
    rw [e]
    exact F.norm_sub_res_apply_le hτ h (fun s hs => hU s (hI hs)) (fun s hs => hU₁ s (hI hs))
      (fun s hs => hB s (hI hs)) (hD _ (hI ⟨by linarith, le_rfl⟩))
  have hsum := sum_le_sum hk
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  rw [norm_sub_rev, norm_sub_rev (U 0)]
  calc ‖(F.res τ h ^ n) v - U (n * τ)‖ ≤ F.M * (‖v - U 0‖ +
        ∑ k ∈ range n, ‖U ((k + 1 : ℕ) * τ) - F.res τ h (U (k * τ))‖) := H
    _ ≤ F.M * (‖v - U 0‖ + n * (F.M * (3 / 2 * τ ^ 2 * B + τ * D))) := by
        gcongr; exact F.M_nonneg
    _ = F.M * ‖v - U 0‖ + F.M ^ 2 * (n * τ) * (3 / 2 * τ * B + D) := by ring

/-- **The rational scheme** `r(τLₕ) = P(Rₕ) Q(Rₕ)⁻¹` through the discrete resolvent. -/
def step (r : RationalScheme) (τ : ℝ) (h : κ) : F.X h →L[𝕜] F.X h :=
  r.resolventStep (F.res τ h)

theorem step_theta_one (τ : ℝ) (h : κ) : F.step (RationalScheme.theta 1 one_pos) τ h = F.res τ h :=
  RationalScheme.resolventStep_theta_one _

/-- **Brenner–Thomée's stability bound**: for every A-stable `r` and `τ > 0`,
`‖r(τLₕ)ⁿ‖ ≤ M (1 + C'_r √n)`, `C'_r = sqrtConst r`, uniformly in `h`. [BrennerThomee1979] -/
theorem norm_step_pow_le {r : RationalScheme} (hr : r.IsAStable) {τ : ℝ} (hτ : 0 < τ) (h : κ)
    (n : ℕ) : ‖F.step r τ h ^ n‖ ≤ F.M * (1 + r.sqrtConst * √n) :=
  RationalScheme.norm_resolventStep_pow_le_of_resolvent_of_isAStable (F.discrete h)
    (F.norm_discrete_S_le h) hr hτ (F.res_apply_sub hτ h) n

/-- **The smooth-data temporal error**: for every A-stable `r` of order `p` and `τ > 0`,
`‖r(τLₕ)ⁿ v - e^{nτLₕ} v‖ ≤ C_r M nτ τᵖ ‖Lₕ^{p+1} v‖`. [BrennerThomee1979];
[GomilkoTomilov2024], Thm 1.1(ii) -/
theorem norm_step_pow_sub_exp_le {r : RationalScheme} (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (h : κ) (n : ℕ) (v : F.X h) :
    ‖(F.step r τ h ^ n) v - exp (((n * τ : ℝ) : 𝕜) • F.L h) v‖ ≤
      r.sharpConst p * F.M * (n * τ) * τ ^ p * ‖(F.L h ^ (p + 1)) v‖ := by
  rw [step]
  simpa using RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent (F.discrete h)
    (F.norm_discrete_S_le h) hr hp hτ (F.res_apply_sub hτ h) n (u := fun j => (F.L h ^ j) v)
    fun j _ => C0Group.pow_apply_mem_graph_generator_ofBounded (F.L h) v j

theorem norm_sub_step_pow_le_norm_sub_exp_add {r : RationalScheme} (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (h : κ) (W : F.X h) (n : ℕ) (v : F.X h) :
    ‖W - (F.step r τ h ^ n) v‖ ≤ ‖W - exp (((n * τ : ℝ) : 𝕜) • F.L h) v‖ +
      r.sharpConst p * F.M * (n * τ) * τ ^ p * ‖(F.L h ^ (p + 1)) v‖ :=
  (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add_right (by rw [norm_sub_rev]; exact F.norm_step_pow_sub_exp_le hr hp hτ h n v) _)

theorem norm_sub_step_pow_le_of_traj {r : RationalScheme} (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (h : κ) {U U' : ℝ → F.X h} {n : ℕ} {D : ℝ}
    (hU : ∀ s ∈ Icc 0 (n * τ), HasDerivAt U (U' s) s)
    (hD : ∀ s ∈ Icc 0 (n * τ), ‖U' s - F.L h (U s)‖ ≤ D) (v : F.X h) :
    ‖U (n * τ) - (F.step r τ h ^ n) v‖ ≤ F.M * ‖U 0 - v‖ + F.M * (n * τ) * D +
      r.sharpConst p * F.M * (n * τ) * τ ^ p * ‖(F.L h ^ (p + 1)) v‖ := by
  have := F.norm_sub_exp_le_of_defect h (by positivity) hU hD v
  linarith [F.norm_sub_step_pow_le_norm_sub_exp_add hr hp hτ h (U (n * τ)) n v]

/-- An A-stable rational scheme with uniformly bounded powers, as a time scheme of order `p`. -/
def rationalScheme (r : RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p)
    (hp0 : 0 < p) (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) (Ms : ℝ → ℝ)
    (hMs : ∀ (T : ℝ) (h : κ) (n : ℕ), (n : ℝ) * τ h ≤ T → ‖F.step r (τ h) h ^ n‖ ≤ Ms T) :
    F.TimeScheme where
  τ := τ
  τ_pos := hτ
  P h := F.step r (τ h) h
  M := Ms
  stable := hMs
  p := p
  p_pos := hp0
  K := r.sharpConst p * F.M
  K_nonneg := mul_nonneg (RationalScheme.sharpConst_nonneg hr hp) F.M_nonneg
  consistent h y := by
    have := F.norm_step_pow_sub_exp_le hr hp (hτ h) h 1 y
    rw [pow_one, Nat.cast_one, one_mul] at this
    calc _ ≤ _ := this
      _ = _ := by ring

/-- **Backward Euler as a time scheme**: `Pₕ = (1 - τₕLₕ)⁻¹`, stable with `M(T) = M`, order `1`. -/
def backwardEuler (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) : F.TimeScheme :=
  F.rationalScheme (RationalScheme.theta 1 one_pos)
    (RationalScheme.isAStable_theta (by norm_num)) (RationalScheme.hasOrder_theta one_pos)
    one_pos τ hτ (fun _ => F.M) fun _ h n _ => by
      rw [step_theta_one]; exact F.norm_res_pow_le (hτ h) h n

/-! ### The verdict -/

/-- The conclusions of `stableFamily`. -/
structure Verdict : Prop where
  semidiscrete_traj (h : κ) {U U' : ℝ → F.X h} {t D : ℝ} (ht : 0 ≤ t)
    (hU : ∀ s ∈ Icc 0 t, HasDerivAt U (U' s) s) (hD : ∀ s ∈ Icc 0 t, ‖U' s - F.L h (U s)‖ ≤ D)
    (v : F.X h) : ‖U t - exp ((t : 𝕜) • F.L h) v‖ ≤ F.M * ‖U 0 - v‖ + F.M * t * D
  temporal_iterates (Θ : F.TimeScheme) {T : ℝ} (h : κ) (v : F.X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖exp (((n * Θ.τ h : ℝ) : 𝕜) • F.L h) v - (Θ.P h ^ n) v‖ ≤
      Θ.M T * Θ.K * F.M * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(F.L h ^ (Θ.p + 1)) v‖
  traj_iterates (Θ : F.TimeScheme) {T : ℝ} (h : κ) (v : F.X h) (W : ℕ → F.X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖W n - (Θ.P h ^ n) v‖ ≤ Θ.M T * (‖W 0 - v‖ + ∑ k ∈ range n, ‖W (k + 1) - Θ.P h (W k)‖)
  stable_backwardEuler {τ : ℝ} (hτ : 0 < τ) (h : κ) (n : ℕ) : ‖F.res τ h ^ n‖ ≤ F.M
  traj_backwardEuler {τ : ℝ} (hτ : 0 < τ) (h : κ) {U U₁ U₂ : ℝ → F.X h} {n : ℕ} {B D : ℝ}
    (hU : ∀ s ∈ Icc 0 (n * τ), HasDerivAt U (U₁ s) s)
    (hU₁ : ∀ s ∈ Icc 0 (n * τ), HasDerivAt U₁ (U₂ s) s) (hB : ∀ s ∈ Icc 0 (n * τ), ‖U₂ s‖ ≤ B)
    (hD : ∀ s ∈ Icc 0 (n * τ), ‖U₁ s - F.L h (U s)‖ ≤ D) (v : F.X h) :
    ‖U (n * τ) - (F.res τ h ^ n) v‖ ≤
      F.M * ‖U 0 - v‖ + F.M ^ 2 * (n * τ) * (3 / 2 * τ * B + D)
  stable_rational (r : RationalScheme) (hr : r.IsAStable) {τ : ℝ} (hτ : 0 < τ) (h : κ) (n : ℕ) :
    ‖F.step r τ h ^ n‖ ≤ F.M * (1 + r.sqrtConst * √n)
  temporal_rational (r : RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ}
    (hτ : 0 < τ) (h : κ) (n : ℕ) (v : F.X h) :
    ‖(F.step r τ h ^ n) v - exp (((n * τ : ℝ) : 𝕜) • F.L h) v‖ ≤
      r.sharpConst p * F.M * (n * τ) * τ ^ p * ‖(F.L h ^ (p + 1)) v‖
  traj_rational (r : RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ}
    (hτ : 0 < τ) (h : κ) {U U' : ℝ → F.X h} {n : ℕ} {D : ℝ}
    (hU : ∀ s ∈ Icc 0 (n * τ), HasDerivAt U (U' s) s)
    (hD : ∀ s ∈ Icc 0 (n * τ), ‖U' s - F.L h (U s)‖ ≤ D) (v : F.X h) :
    ‖U (n * τ) - (F.step r τ h ^ n) v‖ ≤ F.M * ‖U 0 - v‖ + F.M * (n * τ) * D +
      r.sharpConst p * F.M * (n * τ) * τ ^ p * ‖(F.L h ^ (p + 1)) v‖

end StableFamily

/-- **The fully discrete theorem for uniformly stable families**: all the conclusions of
`StableFamily.Verdict` hold. [BrennerThomee1979]; [Thomee2006], Ch. 7; [Pazy1983], §1.5 -/
theorem stableFamily {κ : Type*} (F : StableFamily.{u} 𝕜 κ) : F.Verdict where
  semidiscrete_traj h _ _ _ _ ht hU hD v := F.norm_sub_exp_le_of_defect h ht hU hD v
  temporal_iterates Θ _ h v _ hn := by
    simpa using Θ.norm_exp_sub_pow_le (F.norm_exp_le h) v v hn
  traj_iterates Θ _ h v W _ hn := Θ.norm_sub_pow_le h v W hn
  stable_backwardEuler hτ h n := F.norm_res_pow_le hτ h n
  traj_backwardEuler hτ h _ _ _ _ _ _ hU hU₁ hB hD v :=
    F.norm_sub_res_pow_le_of_traj hτ h hU hU₁ hB hD v
  stable_rational _ hr _ hτ h n := F.norm_step_pow_le hr hτ h n
  temporal_rational _ hr _ hp _ hτ h n v := F.norm_step_pow_sub_exp_le hr hp hτ h n v
  traj_rational _ hr _ hp _ hτ h _ _ _ _ hU hD v := F.norm_sub_step_pow_le_of_traj hr hp hτ h hU hD v

end Feec.TimeStepping
