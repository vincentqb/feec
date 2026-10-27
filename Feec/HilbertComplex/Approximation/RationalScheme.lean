module

public import Feec.HilbertComplex.Approximation.FullyDiscrete
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
  Gauss methods) for skew FEEC discretizations, `‖Pₕⁿ v‖ = ‖v‖`.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [M. Crouzeix, S. Larsson, S. Piskarev, V. Thomée, *The stability of rational approximations of analytic semigroups*][CrouzeixLarssonPiskarevThomee1993]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996],
  §IV.3, §IV.5, §IV.6
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
