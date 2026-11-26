module

public import Feec.HilbertComplex.SecondOrder

/-!
# The mixed and second-order weak wave equations are not equivalent

If `0 ≠ z ∈ ker d`, then `u(t) = (t - a) z` solves the second-order weak wave equation but is the
`u` of no solution of the mixed weak form of [QuennevilleBelair2015], §4.8 (`not_isMixedWeak`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.8

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set

@[expose] public noncomputable section

namespace Feec.Counterexamples.MixedWave

open HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀]
  [NormedSpace ℝ W₀] [IsScalarTower ℝ 𝕜 W₀] [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁]
  [NormedSpace ℝ W₁]

/-- For every `0 ≠ z ∈ ker d` and `a ≤ b`, `u(t) = (t - a) z` solves the second-order weak form on
`[a, b]` but is the `u` of no mixed weak solution. Cf. [QuennevilleBelair2015], §4.8 -/
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
