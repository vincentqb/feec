module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.Counterexamples.BallEigenDense
public import Feec.Counterexamples.BoundedBGG
public import Feec.Counterexamples.BoxStationary
public import Feec.Counterexamples.CubeStationary
public import Feec.Counterexamples.EveryBallSymTSD
public import Feec.Counterexamples.NonClosedRangeEuclidean
public import Feec.Counterexamples.PeriodicFamily
public import Feec.Counterexamples.PolynomialForms

/-!
# Sharpness of the crown's hypotheses

`CrownSharpness` collects what the counterexamples of the repository show about the hypotheses of
the FEEC theorem (`Feec.HilbertComplex.ConformingFamily.feec`,
`Feec.HilbertComplex.ConformingFamily.Verdict`); `crownSharpness` proves it. Each field is the
statement of a theorem, by reference (`type_of%`). Only closed range is shown to be *necessary*
(dropping it breaks a conclusion of the crown); for the reducing and subcomplex hypotheses the
entries show that they fail for the constraints and spaces of interest, so the crown does not
give the corresponding conclusions there.

* **Closed range** (the hypothesis `hcr` of `Verdict.static`). Closed range of `𝔅ᵏ` is necessary
  for the static verdict at `j → k`: its uniform discrete Poincaré inequality forces it
  (`Feec.HilbertComplex.ConformingFamily.StaticVerdict.closedRangeAt`). Finite-dimensional
  harmonic forms do not replace it: the periodic complex `ℓ² --A--> ℓ² --0--> ⋯`,
  `A = diag(1/(n+1))`, has `ℌᵏ = 0` and a conforming family (`Fredholm.periodicFamily`), and no
  conforming family of it has the static verdict in even degrees
  (`Fredholm.periodic_not_staticVerdict`, `Fredholm.periodicFamily_not_staticVerdict`;
  [QuennevilleBelair2015], §4.2 refuted, see `Feec.Counterexamples.Fredholm`). On the `L²` de Rham
  complex of `ℝᵈ` no conforming family can have it (`deRham_not_staticVerdict`); no conforming
  family of that complex is constructed in the repository, so this entry is conditional.
* **Reducing constraints** (`ConstrainedFEEC.Verdict.residual_le` and `residual_tendsto` assume
  that `K` reduces `L`; otherwise the departure clause `ConstrainedFEEC.Verdict.leaves` applies).
  The thesis' TSD constraint is left by a datum of `D(L) ∩ K`, so it does not reduce the wave
  operator: on every nonempty bounded open `Ω ⊆ ℝ³` for no grad–curl complex
  (`BoundedDomainTSD.tsd_not_propagates`) and no Hessian–curl complex
  (`BoundedSymTSD.tsd_not_propagates`), on every ball with the printed boundary conditions
  (`EveryBallSymTSD.tsd_not_propagates`), nor for the BGG weak-symmetry system
  (`BoundedBGG.bggComplex_verdict`). So for TSD only the departure branch of the crown applies.
  These complexes are not windows of conforming families here; the departure clause is exercised
  on the cube in `Feec.Instances.CrownNonVacuity`. The largest reducing subspace of TSD (its
  invariant core, where the residual clauses do apply) is characterized, not refuted: stationary
  data on cubes and boxes (`CubeStationary.mem_invariantCore_tsd_iff`,
  `BoxStationary.mem_invariantCore_tsd_iff_box`), and stationary on the ball iff there is no
  moving TSD eigenfield (`BallEigenDense.coreSub_le_stationary_ball3_iff`).
* **Subcomplexes** (a conforming family consists of subcomplexes): the natural pairs
  `P_{r+1}Λ⁰ × P_r⁻Λ¹` are not (`PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus`).

## Main definitions

* `CrownSharpness`.

## Main results

* **`crownSharpness`**; `deRham_not_staticVerdict`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2, §4.6, §4.10–4.11
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.Counterexamples

/-! ### The de Rham complex of `ℝᵈ` -/

/-- **No conforming family of the `L²` de Rham complex of `ℝᵈ` has the static verdict** in the
degrees `k < d`, along a nontrivial filter: the uniform discrete Poincaré inequality would close
`𝔅ᵏ⁺¹` (`ConformingFamily.StaticVerdict.closedRangeAt`, `deRham_not_closedRange`), although
`ℌ = 0`. The statement is conditional: no conforming family of this complex is constructed in the
repository. [QuennevilleBelair2015], §4.2 -/
theorem deRham_not_staticVerdict (d : Type*) [Fintype d] [LinearOrder d] [Nonempty d]
    {κ : Type*} (F : HilbertComplex.ConformingFamily (Models.Euclidean.DeRham.complex d) κ)
    [F.l.NeBot] {k : ℕ} (hk : k < Fintype.card d) : ¬ F.StaticVerdict k := fun hV =>
  ((deRham_not_closedRange d).2 k hk).1 (hV.closedRangeAt rfl)

/-! ### The sharpness of the crown -/

universe u v

/-- **What the counterexamples show about the crown's hypotheses** (`ConformingFamily.Verdict`):
closed range is necessary for the static verdict; the reducing hypothesis of the residual clauses
fails for the TSD constraint, so only the departure branch applies to it; the subcomplex
hypothesis fails for the pairs `P_{r+1}Λ⁰ × P_r⁻Λ¹`. Each field is the statement of the named
theorem. -/
structure CrownSharpness : Prop where
  /-- `Verdict.static`, closed range is necessary: no conforming family of the periodic complex
  (`ℌ = 0`) has the static verdict in even degrees -/
  closedRange : type_of% @Fredholm.periodic_not_staticVerdict.{u, v}
  /-- `Verdict.static`, closed range: the periodic complex has a conforming family, without the
  static verdict at `0` -/
  closedRange_family : type_of% @Fredholm.periodicFamily_not_staticVerdict.{u}
  /-- `Verdict.static`, closed range: no conforming family of the de Rham complex of `ℝᵈ` has
  the static verdict below the top degree (conditional: none is constructed) -/
  closedRange_euclidean : type_of% @deRham_not_staticVerdict.{u, v}
  /-- `Verdict.constrained`, reducing `K`: TSD is left on bounded domains (grad–curl), so it is
  not reducing and only `leaves` applies -/
  reducing_gradCurl : type_of% @BoundedDomainTSD.tsd_not_propagates
  /-- `Verdict.constrained`, reducing `K`: TSD is left on bounded domains (Hessian–curl) -/
  reducing_hessCurl : type_of% @BoundedSymTSD.tsd_not_propagates
  /-- `Verdict.constrained`, reducing `K`: TSD is left on every ball (printed boundary
  conditions) -/
  reducing_ball : type_of% @EveryBallSymTSD.tsd_not_propagates
  /-- `Verdict.constrained`, reducing `K`: TSD is left by the BGG weak-symmetry system -/
  reducing_bgg : type_of% @BoundedBGG.bggComplex_verdict
  /-- `Verdict.constrained`, where the residual clauses apply: the largest reducing part of TSD on
  a cube is the stationary data (a characterization) -/
  core_cube : type_of% @CubeStationary.mem_invariantCore_tsd_iff
  /-- the largest reducing part of TSD on a box is the stationary data (a characterization) -/
  core_box : type_of% @BoxStationary.mem_invariantCore_tsd_iff_box
  /-- on the ball it is stationary iff there is no moving TSD eigenfield (a characterization) -/
  core_ball : type_of% @BallEigenDense.coreSub_le_stationary_ball3_iff
  /-- `ConformingFamily.V`, subcomplexes: `P_{r+1}Λ⁰ × P_r⁻Λ¹` is not one -/
  subcomplex : type_of% @PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus.{u, v}

/-- **What the counterexamples show about the crown's hypotheses** (`CrownSharpness`). -/
theorem crownSharpness : CrownSharpness.{u, v} :=
  ⟨Fredholm.periodic_not_staticVerdict, Fredholm.periodicFamily_not_staticVerdict,
    deRham_not_staticVerdict, BoundedDomainTSD.tsd_not_propagates,
    BoundedSymTSD.tsd_not_propagates, EveryBallSymTSD.tsd_not_propagates,
    BoundedBGG.bggComplex_verdict, CubeStationary.mem_invariantCore_tsd_iff,
    BoxStationary.mem_invariantCore_tsd_iff_box, BallEigenDense.coreSub_le_stationary_ball3_iff,
    PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus⟩

end Feec.Counterexamples
