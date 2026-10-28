module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.Counterexamples.BallEigenDense
public import Feec.Counterexamples.BoundedBGG
public import Feec.Counterexamples.BoxStationary
public import Feec.Counterexamples.ConstrainedEvolution
public import Feec.Counterexamples.CubeStationary
public import Feec.Counterexamples.DiscreteBGG
public import Feec.Counterexamples.EveryBallSymTSD
public import Feec.Counterexamples.LinearizedGravity
public import Feec.Counterexamples.MixedWave
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

## Thesis corrections

`CrownCorrections` (proved by `crownCorrections`) collects the thesis claims that the crown
corrects or avoids, each by reference and each tied to the clause of the crown it bears on.

* **Stacked BGG families** (the discrete BGG complexes of the crown are those of stacked
  conforming families, `S Ṽₕ ⊆ Vₕ`, `πₕ S = S π̃ₕ`, `BGG.HilbertData.StackedFamily.bggVerdict`).
  The weak-symmetry discretization, with the discrete connecting map `Πₕ S`, is not one, and it
  loses what the crown gives: uniqueness for its discrete mixed system (5.6) needs exactness at
  `V_h¹`, which Props 5.3–5.4 assume but do not use
  (`DiscreteBGG.mixed_not_unique_of_not_exactTop`; for conforming families exactness comes with
  the cohomology isomorphisms of `Verdict.static`), and its semidiscrete system (6.3) has no
  solution for some data (`ConstrainedEvolution.not_forall_exists_discreteSolution`, Prop 6.2
  refuted; corrected by `Feec.BGG.exists_discreteSolution_iff`), whereas `Verdict.wave` is
  well-posed for every datum.
* **The wave formulation** (`Verdict.wave` is the first-order Hodge wave equation `ξ' = L ξ`, in
  weak form the mixed system `(u̇, v) = -(ρ, d v)`, `(ρ̇, μ) = (d u, μ)`). The second-order form
  `(ü, v) = -(d u, d v)` is not equivalent to it (§4.8): if `ker d ≠ 0` it has solutions that are
  the `u` of no mixed solution (`MixedWave.not_isMixedWeak`), and its solutions with
  `u̇(a) = -d* ρ₀` weakly are exactly those that are
  (`HodgeWave.IsSecondOrderWeak.exists_isMixedWeak`). So the crown's wave conclusions reach the
  second-order (Lagrange) form only under this compatibility condition.
* **The TT plane waves** (the exact modes of the Einstein–Bianchi instance on `𝕋³`,
  `Feec.Instances.EinsteinBianchi.GradCurl.planeWave_verdict`, are the TT waves `ttAmp f(k·x)`).
  A Lorentz-gauge plane wave reaches them by the gauge vector of `LinearizedGravity.exists_ttGauge`
  (Prop 2.6, corrected), not by the printed one
  (`LinearizedGravity.not_isTT_gaugeAmp_printed`, `not_isTT_gaugeAmp_printed_contra`); the field
  equation of Prop 2.4(b) on which Prop 2.5 rests is false as printed
  (`LinearizedGravity.not_Hjet_eq_neg_boxJ`, corrected by `Feec.LinearizedGravity.Hsym_lorentz`);
  and the tidal accelerations `aⁱ = -R^i₀ⱼ₀ vʲ` of the electric field `E` that the instance
  evolves are not those printed after (2.15) (`LinearizedGravity.not_accel_printed`).

The vacuum equivalence `G = 0 ⇔ Ric = 0` fails in dimension `2`
(`Feec.Counterexamples.Curvature`); the crown's physics lives in dimension `4` and never passes
through `G`, so it is not collected here.

## Main definitions

* `CrownSharpness`, `CrownCorrections`.

## Main results

* **`crownSharpness`**, **`crownCorrections`**; `deRham_not_staticVerdict`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §2.8, §4.2, §4.6, §4.8, §4.10–4.11, §5.2, §6.2
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

/-! ### Thesis corrections -/

/-- **What the thesis corrections show next to the crown** (`ConformingFamily.Verdict`): the
weak-symmetry discretization, which is not a stacked BGG family, has neither uniqueness without
exactness at `V_h¹` nor existence for every datum; the second-order wave form is not equivalent to
the first-order one of `Verdict.wave`, except under a compatibility condition; the TT plane waves
of the Einstein–Bianchi instance are reached by a corrected gauge, and the printed field equation
and tidal accelerations of §2.8 are false. Each field is the statement of the named theorem. -/
structure CrownCorrections : Prop where
  /-- stacked BGG families: without exactness at `V_h¹` the discrete mixed system (5.6) of the
  weak-symmetry complex is not uniquely solvable (Props 5.3–5.4) -/
  stacked_exact : type_of% @DiscreteBGG.mixed_not_unique_of_not_exactTop
  /-- stacked BGG families: the semidiscrete weak-symmetry system (6.3) has no solution for some
  data (Prop 6.2 refuted) -/
  stacked_wellPosed : type_of% @ConstrainedEvolution.not_forall_exists_discreteSolution
  /-- `Verdict.wave`, formulation: the second-order weak form has solutions that are the `u` of
  no mixed (first-order) solution when `ker d ≠ 0` (§4.8 refuted) -/
  wave_secondOrder : type_of% @MixedWave.not_isMixedWeak.{u, v, v}
  /-- `Verdict.wave`, formulation: second-order solutions with `u̇(a) = -d* ρ₀` weakly are the `u`
  of mixed solutions (§4.8, corrected) -/
  wave_secondOrder_compatible : type_of% @HodgeWave.IsSecondOrderWeak.exists_isMixedWeak.{u, v, v}
  /-- TT plane waves: the corrected gauge vector takes a Lorentz-gauge plane wave to a TT one
  (Prop 2.6, corrected) -/
  tt_gauge : type_of% @Feec.LinearizedGravity.exists_ttGauge
  /-- TT plane waves: the printed gauge vector (covariant reading) does not (Prop 2.6) -/
  tt_gauge_printed : type_of% @LinearizedGravity.not_isTT_gaugeAmp_printed
  /-- TT plane waves: nor does its contravariant reading (Prop 2.6) -/
  tt_gauge_printed_contra : type_of% @LinearizedGravity.not_isTT_gaugeAmp_printed_contra
  /-- TT plane waves: `H = -□h̄` in Lorentz gauge is false (Prop 2.4(b)) -/
  lorentz_printed : type_of% @LinearizedGravity.not_Hjet_eq_neg_boxJ
  /-- TT plane waves: the tidal accelerations printed after (2.15) are wrong -/
  accel_printed : type_of% @LinearizedGravity.not_accel_printed

/-- **What the thesis corrections show next to the crown** (`CrownCorrections`). -/
theorem crownCorrections : CrownCorrections.{u, v} :=
  ⟨DiscreteBGG.mixed_not_unique_of_not_exactTop,
    ConstrainedEvolution.not_forall_exists_discreteSolution, MixedWave.not_isMixedWeak,
    HodgeWave.IsSecondOrderWeak.exists_isMixedWeak, Feec.LinearizedGravity.exists_ttGauge,
    LinearizedGravity.not_isTT_gaugeAmp_printed,
    LinearizedGravity.not_isTT_gaugeAmp_printed_contra, LinearizedGravity.not_Hjet_eq_neg_boxJ,
    LinearizedGravity.not_accel_printed⟩

end Feec.Counterexamples
