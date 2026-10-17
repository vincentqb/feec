module

public import Feec.Evolution.Duhamel
public import Feec.Semigroup.Stone

/-!
# Well-posedness of `U' = A U + F` for the generator of a strongly continuous semigroup

For the generator `A` of a strongly continuous semigroup `G` on a Banach space over
`𝕜 = ℝ` or `ℂ`, an initial value `U₀ ∈ D(A)` and a forcing `F` in the admissible class
`C([a,b]; E) ∩ (W^{1,1}(a,b; E) ∪ L¹(a,b; D(A)))` (`Evolution.ForcingClass.admissible`), the
problem `U' = A U + F` on `[a,b]`, `U a = U₀`, has a classical solution, Duhamel's
`Evolution.mild G.S a U₀ F`, and it is unique among strong solutions.

## Main results

* `C0Semigroup.existsUnique_classicalSolution`: existence of a classical solution, uniqueness
  among strong solutions. Thesis: Thm 4.3 (for every semigroup generator; the thesis states it for
  skew-adjoint generators, i.e. unitary groups).
* `C0Semigroup.isStrongSolution_unique`: uniqueness for any semigroup generator (no
  dissipativity), from `Evolution.IsStrongSolution.eq_mild`.
* `C0Semigroup.isClassicalSolution_orbit`: the homogeneous case `t ↦ S(t - a) U₀`.
* `C0Semigroup.existsUnique_classicalSolution_contDomain`,
  `C0Semigroup.existsUnique_classicalSolution_of_C1`: the subclasses `C([a,b]; D(A))` and
  `C¹([a,b]; E)`.
* `C0Group.existsUnique_classicalSolution`: the same for groups.
* `LinearPMap.IsSkewAdjoint.existsUnique_classicalSolution`: for a skew-adjoint generator on a
  Hilbert space (Stone's group `LinearPMap.IsSkewAdjoint.group`). Thesis: Thm 4.3 as stated.

## References

* [Pazy1983], §4.1–4.2
* [CazenaveHaraux1998], Prop 4.1.6
* [QuennevilleBelair2015], §4.3 (Thm 4.3)
-/

open Set Filter

@[expose] public noncomputable section

namespace Feec

namespace C0Semigroup

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E)

/-- **Uniqueness for a semigroup generator**: strong solutions of `U' = A U + F` on `[a,b]` with
continuous forcing and the same value at `a` agree on `[a,b]`. No dissipativity is needed. -/
theorem isStrongSolution_unique {F U V : ℝ → E} {a b : ℝ}
    (hU : Evolution.IsStrongSolution G.generator (Icc a b) F U)
    (hV : Evolution.IsStrongSolution G.generator (Icc a b) F V) (hF : ContinuousOn F (Icc a b))
    (h0 : U a = V a) : EqOn U V (Icc a b) := fun t ht => by
  rw [hU.eq_mild hF t ht, hV.eq_mild hF t ht, h0]

/-- **Existence and uniqueness of classical solutions** (Thesis Thm 4.3, for every semigroup
generator): for `U₀ ∈ D(A)` and admissible forcing
`F ∈ C([a,b]; E) ∩ (W^{1,1}(a,b; E) ∪ L¹(a,b; D(A)))` there is a classical solution
`U ∈ C([a,b]; D(A)) ∩ C¹([a,b]; E)` of `U' = A U + F`, `U a = U₀` (Duhamel's formula
`Evolution.mild G.S a U₀ F`), and every strong solution with the same initial value agrees with
it on `[a,b]`. Cf. [Pazy1983], Thm 4.1.3, Thm 4.2.4, Cor 4.2.5,
[CazenaveHaraux1998], Prop 4.1.6. -/
theorem existsUnique_classicalSolution {U₀ : E} (hU₀ : U₀ ∈ G.generator.domain) {F : ℝ → E}
    {a b : ℝ} (hF : Evolution.ForcingClass.admissible G.generator a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution G.generator (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution G.generator (Icc a b) F V →
        EqOn V U (Icc a b) :=
  ⟨_, G.mild_self a U₀ F, G.isClassicalSolution_mild hU₀ hF, fun V hV0 hV =>
    G.isStrongSolution_unique hV (G.isClassicalSolution_mild hU₀ hF).toIsStrongSolution hF.1
      (by rw [hV0, G.mild_self])⟩

/-- The solution of `existsUnique_classicalSolution` is the mild solution. -/
theorem eqOn_mild_of_isStrongSolution {U₀ : E} {F V : ℝ → E} {a b : ℝ}
    (hF : ContinuousOn F (Icc a b)) (hV0 : V a = U₀)
    (hV : Evolution.IsStrongSolution G.generator (Icc a b) F V) :
    EqOn V (Evolution.mild G.S a U₀ F) (Icc a b) := fun t ht => by
  rw [hV.eq_mild hF t ht, hV0]

/-- **The homogeneous problem**: for `U₀ ∈ D(A)`, `t ↦ S(t - a) U₀` is a classical solution of
`U' = A U` on `[a,b]`. -/
theorem isClassicalSolution_orbit {U₀ : E} (hU₀ : U₀ ∈ G.generator.domain) (a b : ℝ) :
    Evolution.IsClassicalSolution G.generator (Icc a b) 0 fun t => G.S (t - a) U₀ := by
  have h := G.isClassicalSolution_mild hU₀ (F := 0) (a := a) (b := b)
    (Evolution.ForcingClass.contDomain.admissible
      ⟨fun _ _ => G.generator.domain.zero_mem, continuousOn_const, 0, continuousOn_const,
        fun _ _ => by convert G.generator.map_zero⟩)
  have e : Evolution.mild G.S a U₀ 0 = fun t => G.S (t - a) U₀ := by
    funext t; simp [Evolution.mild]
  rwa [e] at h

/-- Thesis Thm 4.3 for forcing in `C([a,b]; D(A))`. -/
theorem existsUnique_classicalSolution_contDomain {U₀ : E} (hU₀ : U₀ ∈ G.generator.domain)
    {F : ℝ → E} {a b : ℝ} (hF : Evolution.ForcingClass.contDomain G.generator a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution G.generator (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution G.generator (Icc a b) F V →
        EqOn V U (Icc a b) :=
  G.existsUnique_classicalSolution hU₀ hF.admissible

/-- Thesis Thm 4.3 for forcing in `C¹([a,b]; E)`. -/
theorem existsUnique_classicalSolution_of_C1 {U₀ : E} (hU₀ : U₀ ∈ G.generator.domain)
    {F F' : ℝ → E} {a b : ℝ} (hFc : ContinuousOn F (Icc a b)) (hF' : ContinuousOn F' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt F (F' t) t) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution G.generator (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution G.generator (Icc a b) F V →
        EqOn V U (Icc a b) :=
  G.existsUnique_classicalSolution hU₀ (Evolution.ForcingClass.admissible_of_C1 hFc hF' hd)

end C0Semigroup

namespace C0Group

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Group 𝕜 E)

/-- **Existence and uniqueness of classical solutions for a group generator**: the semigroup
statement `C0Semigroup.existsUnique_classicalSolution` for `G.toC0Semigroup`. -/
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

/-- **Thesis Thm 4.3, as stated**: for a skew-adjoint `A`, `U₀ ∈ D(A)` and admissible forcing
`F ∈ C([a,b]; E) ∩ (W^{1,1}(a,b; E) ∪ L¹(a,b; D(A)))`, there is a classical solution of
`U' = A U + F`, `U a = U₀` (Duhamel's formula for Stone's group), unique among strong
solutions. -/
theorem existsUnique_classicalSolution (hA : A.IsSkewAdjoint) {U₀ : E} (hU₀ : U₀ ∈ A.domain)
    {F : ℝ → E} {a b : ℝ} (hF : Evolution.ForcingClass.admissible A a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution A (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution A (Icc a b) F V → EqOn V U (Icc a b) := by
  have h := hA.group.existsUnique_classicalSolution (U₀ := U₀) (F := F) (a := a) (b := b)
  rw [hA.generator_group] at h
  exact h hU₀ hF

/-- For a skew-adjoint `A`, Duhamel's formula for Stone's group solves `U' = A U + F`. -/
theorem isClassicalSolution_mild (hA : A.IsSkewAdjoint) {U₀ : E} (hU₀ : U₀ ∈ A.domain)
    {F : ℝ → E} {a b : ℝ} (hF : Evolution.ForcingClass.admissible A a b F) :
    Evolution.IsClassicalSolution A (Icc a b) F (Evolution.mild hA.group.S a U₀ F) := by
  have h := hA.group.toC0Semigroup.isClassicalSolution_mild (U₀ := U₀) (F := F) (a := a) (b := b)
  have hgen : hA.group.toC0Semigroup.generator = A := hA.generator_group
  rw [hgen] at h
  exact h hU₀ hF

end LinearPMap.IsSkewAdjoint
