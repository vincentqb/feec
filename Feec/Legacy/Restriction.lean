module

public import Feec.Legacy.Existence

/-!
# Restriction to invariant subspaces and constraint propagation (Thesis §4.3)

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use.
Most of the original module was re-derived in the general layers (see
`docs/migration/map.tsv`); what remains is listed below.

## Contents

* `IsStrongSolution.continuousOn`: Strong solutions are continuous on `[0,T]`.
* `strongSolution_unique`: Uniqueness half of **Thesis Thm 4.3**: strong solutions of `U' = L U + F`, `U(0) = U₀` are unique on `[0,T]` for skew-symmetric `L`.
* `IsClassicalSolution`: Solution in the thesis' class `C⁰([0,T]; D(L)) ∩ C¹([0,T]; X)` (Thesis Thm 4.3): a strong solution with `t ↦ L U(t)` (hence `U` in the graph norm) and `t ↦ U'(t)` continuous on `[0,T]`.
* `IsClassicalSolution.toIsStrongSolution`
* `IsClassicalSolution.graph`
* `IsClassicalSolution.c1`
* `IsClassicalSolution.toEvolution`: A classical solution in the sense of `Feec.Evolution.IsClassicalSolution` (graph form, time set `Icc 0 T`).
* `IsClassicalSolution.of_evolution`
* `WellPosedClassical`: **Explicit hypothesis standing in for Thesis Thm 4.3** with the thesis' full regularity: classical solutions exist for initial data in `D(L)` and admissible forcing.

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3, Thm 4.4, Cor 4.5, constraints `K = ker M`), and
  §§4.9–4.11 (Props 4.16–4.19, where Cor 4.5 is applied)
* [CazenaveHaraux1998], Prop 4.1.6 and Cor 2.4.9 (the Hille–Yosida corollary cited by the
  thesis for Thm 4.3; enters here only as the hypotheses `WellPosedExistence` /
  `WellPosedClassical`)
* [Pazy1983], §1.10 (Stone's theorem) and Ch. 4 (inhomogeneous initial value problems):
  classical background for the existence hypothesis
-/

open scoped RealInnerProductSpace
open Set

@[expose] public noncomputable section

namespace Feec.Legacy

/-! ## Evolution: energy uniqueness, constraint propagation, Cor 4.5 -/

section Evolution
open LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {L : E →ₗ.[ℝ] E} {T : ℝ} {U₀ : E} {F U : ℝ → E}

/-- Strong solutions are continuous on `[0,T]`. -/
theorem IsStrongSolution.continuousOn (hU : IsStrongSolution L T U₀ F U) :
    ContinuousOn U (Icc 0 T) :=
  fun t ht => (hU.deriv t ht).continuousWithinAt

/-- Uniqueness half of **Thesis Thm 4.3**: strong solutions of `U' = L U + F`, `U(0) = U₀`
are unique on `[0,T]` for skew-symmetric `L`.

Remark (alternative elementary proof): the thesis obtains uniqueness from Hille–Yosida [16];
here it is proved directly by the energy method (energy identity
`d/dt ‖U - U'‖² = 2⟪L(U - U'), U - U'⟫ = 0`), which needs neither density nor skew-adjointness.
Since `IsStrongSolution` is weaker than the thesis' solution class
`C⁰(D(L)) ∩ C¹(X)`, this uniqueness statement is stronger than the thesis'.

See [QuennevilleBelair2015, Thm 4.3]; cf. [CazenaveHaraux1998], [Pazy1983, §1.10]. -/
theorem strongSolution_unique (L : E →ₗ.[ℝ] E) (hL : IsSkewSymm L) {T : ℝ} {U₀ : E}
    {F U U' : ℝ → E} (h : IsStrongSolution L T U₀ F U) (h' : IsStrongSolution L T U₀ F U') :
    EqOn U U' (Icc 0 T) :=
  h.unique hL.isDissipative h'

/-! ### Classical solutions (critic item 5) -/

/-- Solution in the thesis' class `C⁰([0,T]; D(L)) ∩ C¹([0,T]; X)` (Thesis Thm 4.3):
a strong solution with `t ↦ L U(t)` (hence `U` in the graph norm) and `t ↦ U'(t)` continuous on
`[0,T]`. The dependent maps are represented by continuous functions agreeing with them.
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, Ch. 4]. -/
structure IsClassicalSolution (L : E →ₗ.[ℝ] E) (T : ℝ) (U₀ : E) (F U : ℝ → E) : Prop
    extends IsStrongSolution L T U₀ F U where
  /-- `U ∈ C⁰([0,T]; D(L))`: `t ↦ L U(t)` is continuous. -/
  graph : ∃ G : ℝ → E, ContinuousOn G (Icc 0 T) ∧ ∀ t (ht : t ∈ Icc 0 T), L ⟨U t, mem t ht⟩ = G t
  /-- `U ∈ C¹([0,T]; X)`: `t ↦ U'(t) = L U(t) + F(t)` is continuous. -/
  c1 : ∃ G : ℝ → E, ContinuousOn G (Icc 0 T) ∧
    ∀ t (ht : t ∈ Icc 0 T), L ⟨U t, mem t ht⟩ + F t = G t

/-- A classical solution in the sense of `Feec.Evolution.IsClassicalSolution` (graph form,
time set `Icc 0 T`). -/
theorem IsClassicalSolution.toEvolution (hU : IsClassicalSolution L T U₀ F U) :
    Evolution.IsClassicalSolution L (Icc 0 T) F U :=
  let ⟨G, hGc, hG⟩ := hU.graph
  Evolution.IsClassicalSolution.iff.2 ⟨hU.mem, hU.deriv, G, hGc, hG⟩

theorem IsClassicalSolution.of_evolution (hU : Evolution.IsClassicalSolution L (Icc 0 T) F U)
    (h0 : U 0 = U₀) (hF : ContinuousOn F (Icc 0 T)) : IsClassicalSolution L T U₀ F U := by
  obtain ⟨hm, hd, G, hGc, hG⟩ := Evolution.IsClassicalSolution.iff.1 hU
  exact ⟨⟨hm, hd, h0⟩, ⟨G, hGc, hG⟩, ⟨G + F, hGc.add hF, fun t ht => by rw [hG t ht]; rfl⟩⟩

/-- **Explicit hypothesis standing in for Thesis Thm 4.3** with the thesis' full regularity:
classical solutions exist for initial data in `D(L)` and admissible forcing.
See [QuennevilleBelair2015, Thm 4.3], which cites [CazenaveHaraux1998, Prop 4.1.6, Cor 2.4.9];
cf. [Pazy1983, §1.10, Ch. 4]. -/
def WellPosedClassical (L : E →ₗ.[ℝ] E) (T : ℝ) (Adm : (ℝ → E) → Prop) : Prop :=
  ∀ U₀ ∈ L.domain, ∀ F, Adm F → ∃ U, IsClassicalSolution L T U₀ F U

end Evolution

end Feec.Legacy
