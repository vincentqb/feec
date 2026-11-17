module

public import Solution.Defs
public import Feec.TimeStepping.BanachFEEC
public import Feec.TimeStepping.RationalSemigroup
public import Feec.Models.Cube.FiniteDifferenceHeat

/-!
# The bridge from the challenge to `Feec`

The challenge is stated over Mathlib's polynomials and bounded operators. The dictionary:

* an A-stable `r = p/q` (`TimeStepping.IsAStable`, `|r| ≤ 1` on the closed left half-plane) is
  a `Feec.TimeStepping.RationalScheme` (`TimeStepping.IsAStable.scheme`, through
  `Feec.TimeStepping.RationalScheme.ofBounded`, whose `deg p ≤ deg q` follows from the bound on the
  imaginary axis), A-stable in the sense of `Feec` (the imaginary axis); `TimeStepping.HasOrder`
  gives the order of `Feec` (`Feec.TimeStepping.RationalScheme.hasOrder_of_isBigO`), and the
  converse holds (`TimeStepping.hasOrder_of_dvd`, for the examples);
* `TimeStepping.rationalOfResolvent` is `Feec.TimeStepping.RationalScheme.resolventStep`
  (`TimeStepping.resolventPoly_eq`), and for a bounded generator the resolvent form is
  `p(τL) q(τL)⁻¹` (`TimeStepping.step_eq`, from `Feec.TimeStepping.resolventEval_eq_mul_aeval`);
* a `TimeStepping.IsC0Semigroup` is a `Feec.C0Semigroup` (`TimeStepping.IsC0Semigroup.toC0`),
  whose generator has the graph `TimeStepping.generatorGraph` (`TimeStepping.mem_graph_iff`);
* the finite difference Laplacian is that of `Feec` (`TimeStepping.fdLaplacian_eq`).

`TimeStepping.enorm_le_iSup` and `TimeStepping.enorm_pow_le_iSup_pow` pass from real bounds to
suprema in `[0, ∞]`.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ENNReal Topology
open Polynomial Asymptotics Filter Set Feec.TimeStepping

@[expose] public noncomputable section

namespace TimeStepping

/-- **From real bounds to the supremum in `[0, ∞]`**: if every bound `C` of `‖f i‖` bounds
`‖a‖`, then `‖a‖ₑ ≤ sup_i ‖f i‖ₑ`. -/
theorem enorm_le_iSup {ι : Sort*} {M F : Type*} [SeminormedAddCommGroup M]
    [SeminormedAddCommGroup F] (a : M) (f : ι → F)
    (h : ∀ C : ℝ, (∀ i, ‖f i‖ ≤ C) → ‖a‖ ≤ C) : ‖a‖ₑ ≤ ⨆ i, ‖f i‖ₑ := by
  by_cases hs : (⨆ i, ‖f i‖ₑ) = ∞
  · rw [hs]; exact le_top
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal hs]
  refine ENNReal.ofReal_le_ofReal (h _ fun i => ?_)
  rw [← toReal_enorm]
  exact ENNReal.toReal_mono hs (le_iSup (fun i => ‖f i‖ₑ) i)

/-- **Powers**: if every bound `C` of `‖f i‖` bounds `‖a‖`, and `‖1‖ ≤ 1`, then
`‖aⁿ‖ₑ ≤ (sup_i ‖f i‖ₑ)ⁿ`. -/
theorem enorm_pow_le_iSup_pow {ι : Sort*} {M F : Type*} [SeminormedRing M]
    [SeminormedAddCommGroup F] (h1 : ‖(1 : M)‖ ≤ 1) (a : M) (f : ι → F)
    (h : ∀ C : ℝ, (∀ i, ‖f i‖ ≤ C) → ‖a‖ ≤ C) (n : ℕ) :
    ‖a ^ n‖ₑ ≤ (⨆ i, ‖f i‖ₑ) ^ n := by
  rcases n with _ | n
  · rw [pow_zero, pow_zero, ← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal h1
  calc ‖a ^ (n + 1)‖ₑ ≤ ‖a‖ₑ ^ (n + 1) := by
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (norm_pow_le' a n.succ_pos)
    _ ≤ (⨆ i, ‖f i‖ₑ) ^ (n + 1) := pow_le_pow_left' (enorm_le_iSup a f h) _

/-! ### Rational functions -/

section Rational

variable {p q : ℝ[X]}

theorem IsAStable.aeval_ne_zero (hr : IsAStable p q) : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0 :=
  fun z hz => (hr z hz).1

theorem IsAStable.norm_le (hr : IsAStable p q) (y : ℝ) :
    ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ ≤ 1 :=
  (hr _ (by simp)).2

/-- An A-stable `p/q` as a rational scheme of `Feec`. -/
def IsAStable.scheme (hr : IsAStable p q) : RationalScheme :=
  RationalScheme.ofBounded p q hr.aeval_ne_zero hr.norm_le

theorem IsAStable.scheme_isAStable (hr : IsAStable p q) : hr.scheme.IsAStable := hr.norm_le

theorem IsAStable.scheme_hasOrder (hr : IsAStable p q) {m : ℕ} (hm : HasOrder p q m) :
    hr.scheme.HasOrder m :=
  hr.scheme.hasOrder_of_isBigO hm

/-- **The order from the divisibility** `X^{m+1} ∣ p - q Tₘ` (`Tₘ` the Taylor polynomial of the
exponential), for `q(0) ≠ 0`. -/
theorem hasOrder_of_dvd (hq : aeval (0 : ℂ) q ≠ 0) {m : ℕ}
    (h : X ^ (m + 1) ∣ p - q * expTaylor m) : HasOrder p q m := by
  obtain ⟨g, hg⟩ := h
  have hd0 : ∀ᶠ z : ℂ in 𝓝 0, aeval z q ≠ 0 :=
    ((Polynomial.continuous_aeval q).tendsto 0).eventually_ne hq
  have hexp : (fun z : ℂ => aeval z (expTaylor m) - Complex.exp z) =O[𝓝 0]
      fun z => z ^ (m + 1) := by
    refine IsBigO.of_bound ((m + 1).succ * ((m + 1).factorial * (m + 1 : ℕ) : ℝ)⁻¹) ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) one_pos] with z hz
    rw [mem_closedBall_zero_iff] at hz
    have e : aeval z (expTaylor m) = ∑ j ∈ Finset.range (m + 1), z ^ j / j.factorial := by
      simp [expTaylor, div_eq_inv_mul]
    rw [e, norm_sub_rev, norm_pow]
    exact (Complex.exp_bound hz (Nat.succ_pos m)).trans_eq (mul_comm _ _)
  have hg' : (fun z : ℂ => aeval z g / aeval z q) =O[𝓝 0] fun _ => (1 : ℂ) :=
    (((Polynomial.continuous_aeval g).tendsto 0).div
      ((Polynomial.continuous_aeval q).tendsto 0) hq).isBigO_one ℂ
  have hmul := (isBigO_refl (fun z : ℂ => z ^ (m + 1)) (𝓝 0)).mul hg'
  simp only [mul_one] at hmul
  have hsum := hmul.add hexp
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards [hd0] with z hz
  have e := congrArg (aeval z) hg
  simp only [map_sub, map_mul, map_pow, aeval_X] at e
  have hp : aeval z p = aeval z q * aeval z (expTaylor m) + z ^ (m + 1) * aeval z g := by
    linear_combination e
  rw [hp, add_div, mul_div_cancel_left₀ _ hz]
  ring

end Rational

section Operators

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `P(R)` as written in the challenge is `Feec.TimeStepping.resolventEval`. -/
theorem resolventPoly_eq (N : ℕ) (p : ℝ[X]) (R : E →L[𝕜] E) :
    resolventEval N (p.map (algebraMap ℝ 𝕜)) R = resolventPoly N p R := by
  simp only [resolventEval, resolventPoly, coeff_map, RCLike.algebraMap_eq_ofReal]

theorem resolventStep_eq {p q : ℝ[X]} (hr : IsAStable p q) (R : E →L[𝕜] E) :
    hr.scheme.resolventStep R = rationalOfResolvent p q R := by
  show resolventEval q.natDegree (p.map (algebraMap ℝ 𝕜)) R *
    Ring.inverse (resolventEval q.natDegree (q.map (algebraMap ℝ 𝕜)) R) = _
  rw [resolventPoly_eq, resolventPoly_eq]; rfl

/-- A strongly continuous semigroup of the challenge is one of `Feec`. -/
def IsC0Semigroup.toC0 {S : ℝ → E →L[𝕜] E} (hS : IsC0Semigroup S) : Feec.C0Semigroup 𝕜 E :=
  ⟨S, hS.1, hS.2.1, hS.2.2⟩

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The generator of the challenge (right derivatives at `0`) is `Feec.C0Semigroup.generator`. -/
theorem mem_graph_iff (G : Feec.C0Semigroup 𝕜 E) {x y : E} :
    (x, y) ∈ G.generator.graph ↔ (x, y) ∈ generatorGraph G.S := by
  refine ⟨fun h => ?_, fun h => LinearPMap.mem_graph_iff_exists.2 ⟨⟨y, h⟩, G.generator_apply_eq h⟩⟩
  obtain ⟨hx, rfl⟩ := LinearPMap.mem_graph_iff_exists.1 h
  exact G.hasDerivWithinAt_generator ⟨x, hx⟩

end Operators

/-! ### Bounded generators -/

section Bounded

variable {𝕜 : Type*} [RCLike 𝕜]

variable {κ : Type*} (F : StableFamily 𝕜 κ) {τ : ℝ} (hτ : 0 < τ) (h : κ)
include hτ

theorem res_mul : F.res τ h * (1 - (τ : 𝕜) • F.L h) = 1 := by
  ext x
  simpa using F.res_apply_sub_apply hτ h x

theorem mul_res : (1 - (τ : 𝕜) • F.L h) * F.res τ h = 1 := by
  ext x
  simpa using F.res_sub_smul_apply_res hτ h x

/-- **For a bounded generator the resolvent form is `p(τL) q(τL)⁻¹`**, and `q(τL)` is
invertible. -/
theorem step_eq (r : RationalScheme) :
    IsUnit (aeval ((τ : 𝕜) • F.L h) (r.den.map (algebraMap ℝ 𝕜))) ∧
      F.step r τ h = rationalApply r.num r.den ((τ : 𝕜) • F.L h) := by
  set R := F.res τ h
  set L' := (τ : 𝕜) • F.L h
  have hS : R * (1 - L') = 1 := res_mul F hτ h
  have hS' : (1 - L') * R = 1 := mul_res F hτ h
  have hc : Commute R L' := by
    have e1 : R * L' = R - 1 := by
      calc R * L' = R - R * (1 - L') := by noncomm_ring
        _ = R - 1 := by rw [hS]
    have e2 : L' * R = R - 1 := by
      calc L' * R = R - (1 - L') * R := by noncomm_ring
        _ = R - 1 := by rw [hS']
    exact e1.trans e2.symm
  set N := r.den.natDegree
  have hn : (r.num.map (algebraMap ℝ 𝕜)).natDegree ≤ N :=
    (natDegree_map_le).trans r.natDegree_num_le
  have hd : (r.den.map (algebraMap ℝ 𝕜)).natDegree ≤ N := natDegree_map_le
  have hU : IsUnit (R ^ N) := IsUnit.pow N ⟨⟨R, 1 - L', hS, hS'⟩, rfl⟩
  have hcN : ∀ f : 𝕜[X], Commute (R ^ N) (aeval L' f) := fun f =>
    (commute_aeval hc.symm f).symm.pow_left N
  have hQ := r.isUnit_resolventEval_den_of_resolvent (F.discrete h) (F.norm_discrete_S_le h) hτ
    (F.res_apply_sub hτ h)
  rw [resolventEval_eq_mul_aeval hS hc hd] at hQ
  refine ⟨((hcN _).isUnit_mul_iff.1 hQ).2, ?_⟩
  show resolventEval N (r.num.map (algebraMap ℝ 𝕜)) R *
    Ring.inverse (resolventEval N (r.den.map (algebraMap ℝ 𝕜)) R) = _
  rw [resolventEval_eq_mul_aeval hS hc hn, resolventEval_eq_mul_aeval hS hc hd,
    Ring.mul_inverse_mul_of_commute hU (hcN _) (hcN _)]
  rfl

end Bounded

/-! ### The maximum norm -/

/-- The finite difference Laplacian of the challenge is `FiniteDifference.laplacian`. -/
theorem fdLaplacian_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Finset (ι → ℤ)) (h : ℝ) :
    fdLaplacian G h = FiniteDifference.laplacian G h := by
  ext U p
  simp only [fdLaplacian, FiniteDifference.laplacian_apply, FiniteDifference.zeroExt,
    LinearMap.coe_toContinuousLinearMap', LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

end TimeStepping
