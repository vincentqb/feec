module

public import Feec.HilbertComplex.Approximation.FullyDiscrete
public import Feec.TimeStepping.RationalSemigroup
public import Feec.TimeStepping.RationalQuasi
public import Feec.Semigroup.DissipativePerturbation
public import Feec.TimeStepping.RungeKutta

/-!
# A-stable rational schemes and Runge–Kutta methods as time schemes

Every A-stable rational scheme `r` of order `p ≥ 1`, in particular every A-stable Runge–Kutta
method, is an unconditionally stable time scheme `r(τₕ Lₕ)` of every dissipative discretization.

## Main results

* `DissipFEEC.norm_sol_sub_rationalScheme_sol_le`: the temporal error bound.
* `DissipFEEC.norm_step_pow_sub_S_le`: the time discretization of the exact problem.
* `DissipFEEC.exists_norm_step_pow_sub_perturb_le`: the same for bounded perturbations.
* `SkewFEEC.norm_rationalScheme_pow_apply`: energy conservation of symmetric schemes.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]
* [A. Gomilko, Y. Tomilov, *Rational Approximation of Operator Semigroups via the B-Calculus*][GomilkoTomilov2024]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996]
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

open TimeStepping

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E} {κ : Type*}

namespace DissipFEEC

variable (F : DissipFEEC.{u} A κ)

/-- An A-stable rational scheme as the time scheme `r(τₕ Lₕ)`. [VonNeumann1951] -/
def rationalScheme (r : RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p)
    (hp0 : 0 < p) (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) : F.TimeScheme where
  τ := τ
  τ_pos := hτ
  P h := r.apply ((τ h : 𝕜) • F.L h)
  M _ := 1
  stable _ h n _ :=
    norm_pow_le_one (r.norm_apply_le_one (RationalScheme.dissipative_smul (F.dissipative h)
      (hτ h).le) hr) n
  p := p
  p_pos := hp0
  K := (r.remainder p).supNorm + 1 / (p + 1).factorial
  K_nonneg := add_nonneg (r.remainder p).supNorm_nonneg (by positivity)
  consistent h := r.isConsistent (F.dissipative h) hp (hτ h).le

theorem rationalScheme_pow_mem {r : RationalScheme} (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) (hp0 : 0 < p) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ)
    {Kh : Submodule 𝕜 (F.X h)} (hKc : IsClosed (Kh : Set (F.X h)))
    (hLK : ∀ x ∈ Kh, F.L h x ∈ Kh) {v : F.X h} (hv : v ∈ Kh) (n : ℕ) :
    ((F.rationalScheme r hr hp hp0 τ hτ).P h ^ n) v ∈ Kh := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ']
    exact r.apply_mem_of_mapsTo (RationalScheme.dissipative_smul (F.dissipative h) (hτ h).le)
      hKc (fun x hx => Kh.smul_mem _ (hLK x hx)) ih

theorem thetaScheme_P_eq {θ : ℝ} (hθ : 1 / 2 ≤ θ) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ) :
    (F.thetaScheme θ hθ τ hτ).P h =
      (F.rationalScheme (RationalScheme.theta θ (by linarith)) (RationalScheme.isAStable_theta hθ)
        (RationalScheme.hasOrder_theta _) one_pos τ hτ).P h :=
  (RationalScheme.apply_theta (F.dissipative h) _ (hτ h)).symm

/-- The two-stage Gauss–Legendre method as a time scheme, of order `4`. [HairerWanner1996], §IV.5 -/
abbrev gaussLegendre2 (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) : F.TimeScheme :=
  F.rationalScheme RationalScheme.gaussLegendre2
    RationalScheme.isSymmetric_gaussLegendre2.isAStable RationalScheme.hasOrder_gaussLegendre2
    (by norm_num) τ hτ

/-- The two-stage Radau IIA method as a time scheme, of order `3`. [HairerWanner1996], §IV.5 -/
abbrev radauIIA2 (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) : F.TimeScheme :=
  F.rationalScheme RationalScheme.radauIIA2 RationalScheme.isAStable_radauIIA2
    RationalScheme.hasOrder_radauIIA2 (by norm_num) τ hτ

/-- The two-stage SDIRK method as a time scheme, of order `2`. [HairerWanner1996], §IV.6 -/
abbrev sdirk2 (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) : F.TimeScheme :=
  F.rationalScheme RationalScheme.sdirk2 RationalScheme.isAStable_sdirk2
    RationalScheme.hasOrder_sdirk2 (by norm_num) τ hτ

/-- **The time discretization of the exact problem**: for `x ∈ D(A^{p+1})`,
`‖r(τA)ⁿ x - S(nτ) x‖ ≤ K nτ τᵖ ‖A^{p+1} x‖`, `K` that of `rationalScheme`. [BrennerThomee1979] -/
theorem norm_step_pow_sub_S_le [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    (r : RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ)
    (n : ℕ) {x : E} (hx : x ∈ iterDomain A (p + 1)) :
    ‖(r.step A τ ^ n) x - F.S (n * τ) x‖ ≤
      ((r.remainder p).supNorm + 1 / (p + 1).factorial) * (n * τ) * τ ^ p *
        ‖(genExt A)^[p + 1] x‖ :=
  r.norm_step_pow_sub_semigroup_le F.isMDissipative hr hp hτ n (u := fun j => (genExt A)^[j] x)
    (mem_graph_of_mem_iterDomain hx)

/-- **The time discretization of the exact perturbed problem**: for bounded `B` and `‖B‖τ ≤ c₀`,
`‖r(τ(A + B))ⁿ x - S_B(nτ) x‖ ≤ K e^{κ‖B‖nτ} nτ τᵖ ‖(A + B)^{p+1} x‖`. [Pazy1983], §3.1 -/
theorem exists_norm_step_pow_sub_perturb_le [CompleteSpace E] [NormedSpace ℝ E]
    [IsScalarTower ℝ 𝕜 E] (r : RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K κ : ℝ, 0 ≤ K ∧ 0 ≤ κ ∧ ∀ (B : E →L[𝕜] E) {τ : ℝ}, 0 < τ →
      ‖B‖ * τ ≤ c₀ → ∀ (n : ℕ) {x : E}, x ∈ iterDomain ((B : E →ₗ[𝕜] E) +ᵥ A) (p + 1) →
        ‖(r.step ((B : E →ₗ[𝕜] E) +ᵥ A) τ ^ n) x -
            (F.isMDissipative.semigroup.perturb B).S (n * τ) x‖ ≤
          K * Real.exp (κ * ‖B‖ * (n * τ)) * (n * τ) * τ ^ p *
            ‖(genExt ((B : E →ₗ[𝕜] E) +ᵥ A))^[p + 1] x‖ := by
  obtain ⟨c₀, hc₀, K, κ, hK, hκ, h⟩ := r.exists_norm_step_pow_sub_le hr hp
  refine ⟨c₀, hc₀, K, κ, hK, hκ, fun B τ hτ hBτ n x hx => ?_⟩
  have hB : (((-(‖B‖ : 𝕜)) • (LinearMap.id : E →ₗ[𝕜] E)) +ᵥ
      ((B : E →ₗ[𝕜] E) +ᵥ A)).IsMDissipative := by
    have := F.isMDissipative.vadd_sub_smul B le_rfl
    rw [vadd_vadd]
    convert this using 2
    ext y
    simp [sub_eq_add_neg, add_comm]
  exact h (norm_nonneg B) hB _
    (by rw [C0Semigroup.generator_perturb, F.isMDissipative.generator_semigroup])
    hτ hBτ n (mem_graph_of_mem_iterDomain hx)

/-! ### The estimates with Brenner–Thomée's constant -/

section Banach

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

theorem toBanachFEEC_step (r : RationalScheme) {τ : ℝ} (hτ : 0 < τ) (h : κ) :
    F.toBanachFEEC.step r τ h = r.apply ((τ : 𝕜) • F.L h) := by
  have hg : (F.toBanachFEEC.discrete h).generator = ((F.L h : F.X h →ₗ[𝕜] F.X h).toPMap ⊤) :=
    C0Group.generator_ofBounded (F.L h)
  rw [StableFamily.step, StableFamily.res, hg, ← r.step_eq_resolventStep,
    r.step_toPMap (F.dissipative h) hτ]

/-- **The temporal error of an A-stable rational scheme** of order `p` is at most
`‖ιₕ‖ C_r tₙ τₕᵖ ‖Lₕ^{p+1} v‖`, `C_r = sharpConst r p`. [GomilkoTomilov2024], Thm 1.1(ii) -/
theorem norm_sol_sub_rationalScheme_sol_le (r : RationalScheme) (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) (hp0 : 0 < p) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ) (v : F.X h)
    (n : ℕ) :
    ‖F.sol h v (n * τ h) - (F.rationalScheme r hr hp hp0 τ hτ).sol h v n‖ ≤
      ‖F.incl h‖ * (r.sharpConst p * (n * τ h) * τ h ^ p * ‖(F.L h ^ (p + 1)) v‖) := by
  have H := (TimeStepping.banachFEEC F.toBanachFEEC).temporal_rational r hr hp (hτ h) h v n
  rw [toBanachFEEC_M, mul_one, F.toBanachFEEC_step r (hτ h)] at H
  exact H

theorem norm_step_pow_sub_S_le_brennerThomee (r : RationalScheme) (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {x : E} (hx : x ∈ iterDomain A (p + 1)) :
    ‖(r.step A τ ^ n) x - F.S (n * τ) x‖ ≤
      r.sharpConst p * (n * τ) * τ ^ p * ‖(genExt A)^[p + 1] x‖ := by
  have hR := F.isMDissipative.isResolvent (inv_pos.2 hτ)
  rw [RCLike.ofReal_inv] at hR
  have hgen := F.isMDissipative.generator_semigroup
  have H := (TimeStepping.banachFEEC F.toBanachFEEC).exact_rational r hr hp hτ
    (R := (τ : 𝕜)⁻¹ • Operator.resolvent A (τ : 𝕜)⁻¹)
    (fun x y hxy => hR.inv_smul_apply_sub hτ.ne' (by rwa [hgen] at hxy)) n
    (u := fun j => (genExt A)^[j] x) (by rw [hgen]; exact mem_graph_of_mem_iterDomain hx)
  rw [toBanachFEEC_M, mul_one, ← r.step_eq_resolventStep] at H
  exact H

end Banach

end DissipFEEC

/-- **Energy conservation of symmetric schemes** for a skew FEEC discretization: `‖Pₕⁿ v‖ = ‖v‖`.
[HairerWanner1996], §IV.3 -/
theorem SkewFEEC.norm_rationalScheme_pow_apply [CompleteSpace E] (F : SkewFEEC.{u} A κ)
    {r : RationalScheme} (hr : r.IsSymmetric) {p : ℕ} (hp : r.HasOrder p) (hp0 : 0 < p) {τ : κ → ℝ}
    (hτ : ∀ h, 0 < τ h) (h : κ) (v : F.X h) (n : ℕ) :
    ‖((F.rationalScheme r hr.isAStable hp hp0 τ hτ).P h ^ n) v‖ = ‖v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ← ih]
    refine hr.norm_apply_apply (fun x => ?_) _
    rw [smul_apply, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul,
      re_inner_self_eq_zero_of_skew (F.skew h) x, mul_zero]

end Feec.HilbertComplex
