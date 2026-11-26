module

public import Feec.HilbertComplex.BGG.Discrete

/-!
# The discrete BGG mixed system needs exactness at `V_h¹`

Without exactness at `V_h¹`, the homogeneous discrete mixed system (5.6) of
[QuennevilleBelair2015], §5.2 can have a nonzero solution (`mixed_not_unique_of_not_exactTop`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.2

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace Feec.Counterexamples.DiscreteBGG

/-- Exactness at `V_h¹` cannot be dropped from `Feec.BGG.eq_zero_of_mixed_homogeneous`: over `ℝ`,
`(0, 0, 1, 1)` solves the homogeneous system. Cf. [QuennevilleBelair2015], Props 5.3–5.4 -/
theorem mixed_not_unique_of_not_exactTop :
    let dX0 : ℝ →ₗ[ℝ] ℝ := 0
    let dX1 : ℝ →ₗ[ℝ] ℝ := 0
    let dY0 : ℝ →ₗ[ℝ] ℝ := LinearMap.id
    let dY1 : ℝ →ₗ[ℝ] ℝ := 0
    let S0 : ℝ →ₗ[ℝ] ℝ := LinearMap.id
    let S1 : ℝ →ₗ[ℝ] ℝ := 0
    ((∀ ψ, dX1 (S0 ψ) = -S1 (dY0 ψ)) ∧ Function.Injective dY0 ∧
      (∀ u, dY1 u = 0 → ∃ χ, dY0 χ = u) ∧ Function.Surjective S0 ∧
      (∀ μ : ℝ, ∃ τ ψ, dX0 τ - S0 ψ = μ)) ∧
    ¬ (∀ μ, dX1 μ = 0 → ∃ ρ, dX0 ρ = μ) ∧
    ((∀ τ ψ : ℝ, ⟪(0 : ℝ), τ⟫ - ⟪(1 : ℝ), dY0 ψ⟫ - ⟪(1 : ℝ), dX0 τ - S0 ψ⟫ = 0) ∧
      (∀ v, ⟪dY0 0, v⟫ + ⟪S1 1, S1 v⟫ + ⟪dY1 1, dY1 v⟫ = 0) ∧
      (∀ μ, ⟪dX0 0 - S0 0, μ⟫ = 0) ∧ (1 : ℝ) ≠ 0) := by
  intro dX0 dX1 dY0 dY1 S0 S1
  refine ⟨⟨fun ψ => by simp [dX1, S1], fun a b h => h, fun u _ => ⟨u, rfl⟩,
    fun y => ⟨y, rfl⟩, fun μ => ⟨0, -μ, by simp [dX0, S0]⟩⟩, ?_, ?_⟩
  · intro h
    obtain ⟨ρ, hρ⟩ := h 1 rfl
    simp [dX0] at hρ
  · refine ⟨fun τ ψ => ?_, fun v => by simp [dY0, S1, dY1], fun μ => by simp [dX0, S0], one_ne_zero⟩
    simp [dX0, dY0, S0]

end Feec.Counterexamples.DiscreteBGG

namespace Feec.BGG

end Feec.BGG
