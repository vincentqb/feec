module

public import Feec.HilbertComplex.SecondOrder

/-!
# The mixed and second-order weak wave equations are not equivalent

Thesis §4.8 claims that the mixed weak form `(u̇, v) = -(ρ, d v)`, `(ρ̇, μ) = (d u, μ)` of the
scalar wave equation is equivalent to the second-order weak form `(ü, v) = -(d u, d v)`. Under
natural boundary conditions this fails: whenever `ker d ≠ 0` (for `d = grad` on `H¹`: the
constants), `u(t) = (t - a) z` with `0 ≠ z ∈ ker d` solves the second-order form, but it is the
`u` of no mixed solution, because a mixed solution has `u̇ ⊥ ker d`.

The correct statement is `Feec.HodgeWave.IsSecondOrderWeak.exists_isMixedWeak`: second-order
solutions with `u̇(a) = -d* ρ₀` weakly are exactly the `u` of mixed solutions.

The second-order form is the standard non-mixed (Lagrange `P_r Λ⁰`) formulation, which the thesis
attributes to [Baker1976] and [Dupont1973] ([QuennevilleBelair2015], §4.8); those works treat the
second-order form on its own, and the failing claim is only the thesis' equivalence with the
mixed form.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.8
* [G. A. Baker, *Error estimates for finite element methods for second order hyperbolic equations*][Baker1976]
* [T. Dupont, *L²-estimates for Galerkin methods for second order hyperbolic equations*][Dupont1973]
-/

open scoped InnerProductSpace
open Set

@[expose] public noncomputable section

namespace Feec.Counterexamples.MixedWave

open HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀]
  [NormedSpace ℝ W₀] [IsScalarTower ℝ 𝕜 W₀] [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁]
  [NormedSpace ℝ W₁]

/-- **The §4.8 equivalence fails under natural boundary conditions**: for every `0 ≠ z ∈ ker d`
and every interval `[a, b]`, `u(t) = (t - a) z` solves the second-order weak form but is not the
`u` of any mixed weak solution. See [QuennevilleBelair2015], §4.8 (refuted); the second-order
form is the standard one of [Baker1976] and [Dupont1973], which is not at fault. -/
theorem not_isMixedWeak {d : W₀ →ₗ.[𝕜] W₁} {a b : ℝ} (hab : a ≤ b) (z : d.domain) (hz : d z = 0)
    (hz0 : (z : W₀) ≠ 0) :
    IsSecondOrderWeak d (Icc a b) (fun t => ((t - a : ℝ) : 𝕜) • z) (fun _ => (z : W₀)) ∧
      ¬ ∃ ρ ρ', IsMixedWeak d (Icc a b) (fun t => ((t - a : ℝ) : 𝕜) • z) (fun _ => (z : W₀))
        ρ ρ' := by
  refine ⟨⟨fun t _ => ?_, ?_, fun t _ v => ?_⟩,
    not_isMixedWeak_of_inner_ne_zero (left_mem_Icc.2 hab) z hz ?_⟩
  · have e : (fun s : ℝ => (((((s - a : ℝ) : 𝕜) • z : d.domain)) : W₀)) =
        fun s => (s - a) • (z : W₀) := funext fun s => by
      rw [Submodule.coe_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    rw [e]
    simpa using (((hasDerivAt_id t).sub_const a).smul_const (z : W₀)).hasDerivWithinAt
      (s := Icc a b)
  · simp only [LinearPMap.map_smul, hz, smul_zero]; exact continuousOn_const
  · simp only [LinearPMap.map_smul, hz, smul_zero, inner_zero_left, neg_zero]
    exact hasDerivWithinAt_const _ _ _
  · simpa using hz0

end Feec.Counterexamples.MixedWave
