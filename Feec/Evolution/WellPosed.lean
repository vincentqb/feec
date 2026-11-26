module

public import Feec.Evolution.Duhamel
public import Feec.Semigroup.Stone

/-!
# Well-posedness of `U' = A U + F` for the generator of a strongly continuous semigroup

For the generator `A` of a strongly continuous semigroup, `U₀ ∈ D(A)` and admissible forcing,
`U' = A U + F`, `U a = U₀`, has a classical solution, given by Duhamel's formula, unique among
strong solutions.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983]
* [T. Cazenave, A. Haraux, *An Introduction to Semilinear Evolution Equations*][CazenaveHaraux1998]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter

@[expose] public noncomputable section

namespace Feec

namespace C0Semigroup

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E)

theorem isStrongSolution_unique {F U V : ℝ → E} {a b : ℝ}
    (hU : Evolution.IsStrongSolution G.generator (Icc a b) F U)
    (hV : Evolution.IsStrongSolution G.generator (Icc a b) F V) (hF : ContinuousOn F (Icc a b))
    (h0 : U a = V a) : EqOn U V (Icc a b) := fun t ht => by
  rw [hU.eq_mild hF t ht, hV.eq_mild hF t ht, h0]

/-- **Existence and uniqueness of classical solutions** for `U₀ ∈ D(A)` and admissible forcing.
[QuennevilleBelair2015], Thm 4.3 (adapted); [Pazy1983], Thm 4.1.3, Thm 4.2.4 -/
theorem existsUnique_classicalSolution {U₀ : E} (hU₀ : U₀ ∈ G.generator.domain) {F : ℝ → E}
    {a b : ℝ} (hF : Evolution.ForcingClass.admissible G.generator a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution G.generator (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution G.generator (Icc a b) F V →
        EqOn V U (Icc a b) :=
  ⟨_, G.mild_self a U₀ F, G.isClassicalSolution_mild hU₀ hF, fun V hV0 hV =>
    G.isStrongSolution_unique hV (G.isClassicalSolution_mild hU₀ hF).toIsStrongSolution hF.1
      (by rw [hV0, G.mild_self])⟩

theorem isClassicalSolution_orbit {U₀ : E} (hU₀ : U₀ ∈ G.generator.domain) (a b : ℝ) :
    Evolution.IsClassicalSolution G.generator (Icc a b) 0 fun t => G.S (t - a) U₀ := by
  have h := G.isClassicalSolution_mild hU₀ (F := 0) (a := a) (b := b)
    (Evolution.ForcingClass.contDomain.admissible
      ⟨fun _ _ => G.generator.domain.zero_mem, continuousOn_const, 0, continuousOn_const,
        fun _ _ => by convert G.generator.map_zero⟩)
  have e : Evolution.mild G.S a U₀ 0 = fun t => G.S (t - a) U₀ := by
    funext t; simp [Evolution.mild]
  rwa [e] at h

end C0Semigroup

namespace C0Group

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Group 𝕜 E)

theorem existsUnique_classicalSolution {U₀ : E} (hU₀ : U₀ ∈ G.generator.domain) {F : ℝ → E}
    {a b : ℝ} (hF : Evolution.ForcingClass.admissible G.generator a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution G.generator (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution G.generator (Icc a b) F V →
        EqOn V U (Icc a b) :=
  G.toC0Semigroup.existsUnique_classicalSolution hU₀ hF

end C0Group

end Feec

namespace LinearPMap.IsSkewAdjoint

open Feec

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E}

/-- **Existence and uniqueness for skew-adjoint `A`**, for `U₀ ∈ D(A)` and admissible forcing.
[QuennevilleBelair2015], Thm 4.3; [CazenaveHaraux1998], Prop 4.1.6, Cor 2.4.9 -/
theorem existsUnique_classicalSolution (hA : A.IsSkewAdjoint) {U₀ : E} (hU₀ : U₀ ∈ A.domain)
    {F : ℝ → E} {a b : ℝ} (hF : Evolution.ForcingClass.admissible A a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution A (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution A (Icc a b) F V → EqOn V U (Icc a b) := by
  have h := hA.group.existsUnique_classicalSolution (U₀ := U₀) (F := F) (a := a) (b := b)
  rw [hA.generator_group] at h
  exact h hU₀ hF

theorem isClassicalSolution_mild (hA : A.IsSkewAdjoint) {U₀ : E} (hU₀ : U₀ ∈ A.domain)
    {F : ℝ → E} {a b : ℝ} (hF : Evolution.ForcingClass.admissible A a b F) :
    Evolution.IsClassicalSolution A (Icc a b) F (Evolution.mild hA.group.S a U₀ F) := by
  have h := hA.group.toC0Semigroup.isClassicalSolution_mild (U₀ := U₀) (F := F) (a := a) (b := b)
  have hgen : hA.group.toC0Semigroup.generator = A := hA.generator_group
  rw [hgen] at h
  exact h hU₀ hF

end LinearPMap.IsSkewAdjoint
