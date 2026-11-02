module

public import Feec.HilbertComplex.Approximation.FullyDiscrete
public import Feec.TimeStepping.RationalSemigroup
public import Feec.TimeStepping.RationalQuasi
public import Feec.Semigroup.DissipativePerturbation
public import Feec.TimeStepping.RungeKutta

/-!
# A-stable rational schemes and Runge–Kutta methods as time schemes

Every A-stable rational scheme `r` of order `p ≥ 1` (`Feec.TimeStepping.RationalScheme`), in
particular every A-stable Runge–Kutta method through its stability function, is a time scheme of
every dissipative FEEC discretization (`DissipFEEC.rationalScheme`): `Pₕ = r(τₕ Lₕ)`,
**unconditionally stable** (`M = 1`, von Neumann's inequality,
`Feec.TimeStepping.RationalScheme.norm_apply_le_one`) and consistent of order `p` with the constant
`K = sup_y |ρ(iy)| + 1/(p+1)!` of its remainder `ρ = (r - Tₚ)/z^{p+1}`
(`Feec.TimeStepping.RationalScheme.isConsistent`), uniformly in `h`. The fully discrete FEEC
theorem (`Feec.HilbertComplex.dissipFEEC_fullyDiscrete`) then applies, and so the field `full` of
the FEEC theorem (`Feec.HilbertComplex.ConformingFamily.feec`): stability of the iterates, the
temporal error `‖ιₕ‖ K tₙ τₕᵖ ‖Lₕ^{p+1} v‖` (Brenner–Thomée), the rate, convergence for every datum
of the closure of the core as `h, τ → 0`, and the constraint residuals.

* `DissipFEEC.thetaScheme_P_eq`: the θ-schemes are the rational schemes `r_θ`;
* `DissipFEEC.gaussLegendre2` (order `4`), `DissipFEEC.radauIIA2` (order `3`),
  `DissipFEEC.sdirk2` (order `2`): the Runge–Kutta time schemes of
  `Feec.TimeStepping.RungeKutta`;
* `DissipFEEC.rationalScheme_pow_mem`: **discrete constraint propagation**, a closed subspace
  `Kₕ` with `Lₕ Kₕ ⊆ Kₕ` is kept by every iterate;
* `SkewFEEC.norm_rationalScheme_pow_apply`: **energy conservation** of symmetric schemes (the
  Gauss methods) for skew FEEC discretizations, `‖Pₕⁿ v‖ = ‖v‖`;
* `DissipFEEC.norm_step_pow_sub_S_le`: **the time discretization of the exact problem**, the
  Brenner–Thomée bound `‖r(τA)ⁿ x - S(nτ) x‖ ≤ K nτ τᵖ ‖A^{p+1} x‖` for the unbounded generator `A`
  and `x ∈ D(A^{p+1})` (`DissipFEEC.iterDomain`;
  `Feec.TimeStepping.RationalScheme.norm_step_pow_sub_semigroup_le`), with the constant `K` of the
  discrete schemes;
* `DissipFEEC.exists_norm_step_pow_sub_perturb_le`: **the same for every bounded perturbation**
  `A + B`, not necessarily dissipative, whose Dyson–Phillips semigroup grows like `e^{‖B‖t}`:
  `‖r(τ(A + B))ⁿ x - S_B(nτ) x‖ ≤ K e^{κ‖B‖nτ} nτ τᵖ ‖(A + B)^{p+1} x‖` for `‖B‖τ ≤ c₀`, with
  `c₀`, `K`, `κ` depending only on `r` (Brenner–Thomée for quasi-contractive semigroups,
  `Feec.TimeStepping.RationalScheme.exists_norm_step_pow_sub_le`).

**From the Banach layer** (`Feec.TimeStepping.banachFEEC` for `F.toBanachFEEC`, `M = 1`):

* `DissipFEEC.toBanachFEEC_step`: `r(τLₕ) = n(τLₕ) d(τLₕ)⁻¹`
  (`Feec.TimeStepping.RationalScheme.apply`) is the Banach scheme `P(Rₕ) Q(Rₕ)⁻¹`,
  `Rₕ = (1 - τLₕ)⁻¹`;
* `DissipFEEC.norm_sol_sub_rationalScheme_sol_le`: **the sharp temporal error**
  `‖ιₕ e^{tₙ Lₕ} v - ιₕ r(τₕLₕ)ⁿ v‖ ≤ ‖ιₕ‖ C_r tₙ τₕᵖ ‖Lₕ^{p+1} v‖` with Brenner–Thomée's
  constant `C_r = sharpConst r p` of the smooth-data estimate, independent of `h`;
* `DissipFEEC.norm_step_pow_sub_S_le_brennerThomee`: the same constant for the exact problem,
  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ C_r nτ τᵖ ‖A^{p+1} x‖` on `D(A^{p+1})`.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [M. Crouzeix, S. Larsson, S. Piskarev, V. Thomée, *The stability of rational approximations of analytic semigroups*][CrouzeixLarssonPiskarevThomee1993]
* [A. Gomilko, Y. Tomilov, *Rational Approximation of Operator Semigroups via the B-Calculus*][GomilkoTomilov2024],
  Thm 1.1
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996],
  §IV.3, §IV.5, §IV.6
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.1 (bounded perturbations)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 4.18 (constraint propagation, here at the discrete level)

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

/-- **An A-stable rational scheme of order `p ≥ 1` as a time scheme**: `Pₕ = r(τₕ Lₕ)`,
unconditionally stable (`M = 1`) and consistent of order `p` with
`K = sup_y |ρ(iy)| + 1/(p+1)!`, uniformly in `h`. [BrennerThomee1979];
[CrouzeixLarssonPiskarevThomee1993] -/
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

/-- **Discrete constraint propagation for rational schemes**: a closed subspace `Kₕ ⊆ Xₕ` with
`Lₕ Kₕ ⊆ Kₕ` is kept by every iterate `Pₕⁿ`. [QuennevilleBelair2015], Prop 4.18 -/
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

/-- **The θ-scheme is the rational scheme `r_θ`**: the one-step operators of
`DissipFEEC.thetaScheme` are those of `DissipFEEC.rationalScheme` for `RationalScheme.theta`
(their consistency constants differ: `θ + 1/2` from the expansion of the θ-step, and the
remainder bound of von Neumann's inequality). -/
theorem thetaScheme_P_eq {θ : ℝ} (hθ : 1 / 2 ≤ θ) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ) :
    (F.thetaScheme θ hθ τ hτ).P h =
      (F.rationalScheme (RationalScheme.theta θ (by linarith)) (RationalScheme.isAStable_theta hθ)
        (RationalScheme.hasOrder_theta _) one_pos τ hτ).P h :=
  (RationalScheme.apply_theta (F.dissipative h) _ (hτ h)).symm

/-- **The two-stage Gauss–Legendre method** as a time scheme: order `4`, unconditionally
stable. [HairerWanner1996], §IV.5 -/
abbrev gaussLegendre2 (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) : F.TimeScheme :=
  F.rationalScheme RationalScheme.gaussLegendre2
    RationalScheme.isSymmetric_gaussLegendre2.isAStable RationalScheme.hasOrder_gaussLegendre2
    (by norm_num) τ hτ

/-- **The two-stage Radau IIA method** as a time scheme: order `3`, unconditionally stable.
[HairerWanner1996], §IV.5 -/
abbrev radauIIA2 (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) : F.TimeScheme :=
  F.rationalScheme RationalScheme.radauIIA2 RationalScheme.isAStable_radauIIA2
    RationalScheme.hasOrder_radauIIA2 (by norm_num) τ hτ

/-- **The two-stage SDIRK method** as a time scheme: order `2`, unconditionally stable.
[HairerWanner1996], §IV.6 -/
abbrev sdirk2 (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) : F.TimeScheme :=
  F.rationalScheme RationalScheme.sdirk2 RationalScheme.isAStable_sdirk2
    RationalScheme.hasOrder_sdirk2 (by norm_num) τ hτ

/-- **The time discretization of the exact problem** (Brenner–Thomée for the unbounded
generator): for every A-stable rational scheme `r` of order `p`, `τ > 0`, `n` and
`x ∈ D(A^{p+1})` (`iterDomain`, the data of the rate classes `RegScale.domainPow`),
`‖r(τA)ⁿ x - S(nτ) x‖ ≤ K nτ τᵖ ‖A^{p+1} x‖` with the constant `K = sup_y |ρ(iy)| + 1/(p+1)!` of
`rationalScheme`. [BrennerThomee1979] -/
theorem norm_step_pow_sub_S_le [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    (r : RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ)
    (n : ℕ) {x : E} (hx : x ∈ iterDomain A (p + 1)) :
    ‖(r.step A τ ^ n) x - F.S (n * τ) x‖ ≤
      ((r.remainder p).supNorm + 1 / (p + 1).factorial) * (n * τ) * τ ^ p *
        ‖(genExt A)^[p + 1] x‖ :=
  r.norm_step_pow_sub_semigroup_le F.isMDissipative hr hp hτ n (u := fun j => (genExt A)^[j] x)
    (mem_graph_of_mem_iterDomain hx)

/-- **The time discretization of the exact perturbed problem** (Brenner–Thomée for
quasi-contractive semigroups): for every A-stable rational scheme `r` of order `p` there are
`c₀ > 0`, `K` and `κ`, depending only on `r`, such that for every bounded `B`, not necessarily
dissipative, every `τ > 0` with `‖B‖τ ≤ c₀`, every `n` and `x ∈ D((A + B)^{p+1})`,
`‖r(τ(A + B))ⁿ x - S_B(nτ) x‖ ≤ K e^{κ‖B‖nτ} nτ τᵖ ‖(A + B)^{p+1} x‖`, with `S_B` the
Dyson–Phillips perturbation of `S`, the semigroup generated by `A + B`. `A + B - ‖B‖` is
m-dissipative and `‖S_B(t)‖ ≤ e^{‖B‖t}`. [BrennerThomee1979]; [Pazy1983], §3.1 -/
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

/-! ### The sharp estimates, from the Banach layer -/

section Banach

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **The rational schemes are those of the Banach layer**: `r(τLₕ) = n(τLₕ) d(τLₕ)⁻¹`
(`Feec.TimeStepping.RationalScheme.apply`) is `r(τLₕ) = P(Rₕ) Q(Rₕ)⁻¹` through the resolvent
`Rₕ = (1 - τLₕ)⁻¹` of `F.toBanachFEEC` (`StableFamily.step`), for `τ > 0`. -/
theorem toBanachFEEC_step (r : RationalScheme) {τ : ℝ} (hτ : 0 < τ) (h : κ) :
    F.toBanachFEEC.step r τ h = r.apply ((τ : 𝕜) • F.L h) := by
  have hg : (F.toBanachFEEC.discrete h).generator = ((F.L h : F.X h →ₗ[𝕜] F.X h).toPMap ⊤) :=
    C0Group.generator_ofBounded (F.L h)
  rw [StableFamily.step, StableFamily.res, hg, ← r.step_eq_resolventStep,
    r.step_toPMap (F.dissipative h) hτ]

/-- **The sharp temporal error of every A-stable rational scheme** of order `p`:
`‖ιₕ e^{tₙ Lₕ} v - ιₕ r(τₕLₕ)ⁿ v‖ ≤ ‖ιₕ‖ C_r tₙ τₕᵖ ‖Lₕ^{p+1} v‖`, `C_r = sharpConst r p`
independent of `h` (Brenner–Thomée's smooth-data estimate on the Banach discretization
`F.toBanachFEEC`,
field `temporal_rational` of `banachFEEC`, with `M = 1`). [BrennerThomee1979];
[GomilkoTomilov2024], Thm 1.1(ii) -/
theorem norm_sol_sub_rationalScheme_sol_le (r : RationalScheme) (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) (hp0 : 0 < p) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ) (v : F.X h)
    (n : ℕ) :
    ‖F.sol h v (n * τ h) - (F.rationalScheme r hr hp hp0 τ hτ).sol h v n‖ ≤
      ‖F.incl h‖ * (r.sharpConst p * (n * τ h) * τ h ^ p * ‖(F.L h ^ (p + 1)) v‖) := by
  have H := (TimeStepping.banachFEEC F.toBanachFEEC).temporal_rational r hr hp (hτ h) h v n
  rw [toBanachFEEC_M, mul_one, F.toBanachFEEC_step r (hτ h)] at H
  exact H

/-- **The sharp time discretization of the exact problem**: for every A-stable rational scheme
`r` of order `p`, `τ > 0`, `n` and `x ∈ D(A^{p+1})`,
`‖r(τA)ⁿ x - S(nτ) x‖ ≤ C_r nτ τᵖ ‖A^{p+1} x‖`, `C_r = sharpConst r p` (Brenner–Thomée's
smooth-data estimate, field `exact_rational` of `banachFEEC` for `F.toBanachFEEC`, with
`R = (1 - τA)⁻¹`). [BrennerThomee1979]; [GomilkoTomilov2024], Thm 1.1(ii) -/
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

/-- **Energy conservation of symmetric schemes** (the Gauss methods) for a skew FEEC
discretization: `‖Pₕⁿ v‖ = ‖v‖`. [HairerWanner1996], §IV.3 -/
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
