module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.HilbertComplex.Approximation.CochainProjectionExistence
public import Feec.Counterexamples.BallEigenDense
public import Feec.Counterexamples.BoundedBGG
public import Feec.Counterexamples.BoxStationary
public import Feec.Counterexamples.ConstrainedEvolution
public import Feec.Counterexamples.CubeStationary
public import Feec.Counterexamples.Curvature
public import Feec.Counterexamples.DiscreteBGG
public import Feec.Counterexamples.EveryBallSymTSD
public import Feec.Counterexamples.LinearizedGravity
public import Feec.Counterexamples.MixedWave
public import Feec.Counterexamples.NonClosedRangeEuclidean
public import Feec.Counterexamples.PeriodicFamily
public import Feec.Counterexamples.PolynomialForms
public import Feec.Domain.BGGRealization

/-!
# Sharpness of the crown's hypotheses

`CrownSharpness` collects what the counterexamples of the repository show about the hypotheses of
the FEEC theorem (`Feec.HilbertComplex.ConformingFamily.feec`,
`Feec.HilbertComplex.ConformingFamily.Verdict`); `crownSharpness` proves it. Each field is the
statement of a theorem, by reference (`type_of%`). Only closed range is shown to be *necessary*
(dropping it breaks a conclusion of the crown); the bounded-projection hypothesis of the static
layer is characterized (it is equivalent to discrete stability); for the reducing and subcomplex
hypotheses the entries show that they fail for the constraints and spaces of interest, so the
crown does not give the corresponding conclusions there.

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
* **Bounded cochain projections** (the hypothesis of the static layer
  `SubcomplexFamily.staticFEEC` behind `Verdict.static`: projections bounded in the graph norm
  uniformly in `h`). It cannot be weakened beyond discrete stability, and discrete stability
  suffices: for a complex with closed range, uniformly bounded cochain projections exist iff the
  discrete Poincaré inequality and the harmonic bound `‖q‖ ≤ c ‖P_ℌ q‖` hold uniformly
  (`HilbertComplex.SubcomplexFamily.exists_isGraphBounded_iff`; [AFW2010], Thms 3.6, 3.7, (30)).
* **Right inverses of the connecting maps** (the hypothesis `Feec.BGG.Data.InjSurjWith` of the
  explicit-map fields of `Feec.BGG.HilbertData.BGGVerdict`, the analytic BGG verdict behind the
  crown's discrete BGG complexes, `BGG.HilbertData.StackedFamily.bggVerdict`). It fails between
  the `L²` domain complexes of the Hessian, elasticity and div-div diagrams on every nonempty
  open `Ω ⊆ ℝ³`, from every `J ≤ 0`, `1`, `2`: `Sᴶ` is not onto there
  (`Feec.Domain.hessianMaximalData_not_injSurjWith`, `elasticityMaximalData_not_injSurjWith`,
  `divDivMaximalData_not_injSurjWith`; e.g. `S⁰ = I : H¹(Ω; 𝕜³) → H(curl; Ω)`). So on `L²` these
  fields hold only vacuously; the explicit map is exercised on smooth fields
  (`Feec.Domain.smoothBGGVerdict`).

## Thesis corrections

`CrownCorrections` (proved by `crownCorrections`) collects the thesis claims that the crown
corrects or avoids, each by reference. The statements involve no crown object (no
`ConformingFamily`, `Verdict` or `StackedFamily`): the tie to the clause of the crown each bears
on is documentary, stated below.

* **Stacked BGG families** (the discrete BGG complexes of the crown are those of stacked
  conforming families, `S Ṽₕ ⊆ Vₕ`, `πₕ S = S π̃ₕ`, `BGG.HilbertData.StackedFamily.bggVerdict`).
  The weak-symmetry discretization, with the discrete connecting map `Πₕ S`, is not one, and it
  is not covered by it: uniqueness for its discrete mixed system (5.6) needs exactness at
  `V_h¹`, which Props 5.3–5.4 assume but do not use
  (`DiscreteBGG.mixed_not_unique_of_not_exactTop`; for a conforming family with closed range and
  finite-dimensional `ℌʲ`, `Verdict.static` gives `Hʲ(Vₕ) ≅ Hʲ`, so discrete exactness where the
  continuous complex is exact, and well-posedness of its own mixed Hodge Laplacian, not of (5.6)),
  and its semidiscrete system (6.3) has no
  solution for some data (`ConstrainedEvolution.not_forall_exists_discreteSolution`, Prop 6.2
  refuted; corrected by `Feec.BGG.exists_discreteSolution_iff`), whereas `Verdict.wave` is
  well-posed for every datum.
* **The wave formulation** (`Verdict.wave` discretizes the first-order Hodge wave equation
  `ξ' = L ξ`, whose weak form is the mixed system `(u̇, v) = -(ρ, d v)`, `(ρ̇, μ) = (d u, μ)`; that
  the strong orbits of the crown's wave group satisfy it is not proved here). For continuous weak
  solutions, the second-order form `(ü, v) = -(d u, d v)` and the mixed form agree exactly under
  the compatibility condition `u̇(a) = -d* ρ₀` (§4.8, corrected): its solutions satisfying it are
  the `u` of mixed solutions (`HodgeWave.IsSecondOrderWeak.exists_isMixedWeak`), those violating
  it on `ker d` are not (`HodgeWave.not_isMixedWeak_of_inner_ne_zero`), and if `ker d ≠ 0` such
  solutions exist (`MixedWave.not_isMixedWeak`). The mixed form is the one whose discretization
  `Verdict.wave` covers; nothing here transfers its conclusions to a Lagrange discretization of
  the second-order form.
* **The TT plane waves** (the exact modes of the Einstein–Bianchi instance on `𝕋³`,
  `Feec.Instances.EinsteinBianchi.GradCurl.planeWave_verdict`, are the TT waves `ttAmp f(k·x)`).
  A Lorentz-gauge plane wave reaches them by the gauge vector of
  `Feec.LinearizedGravity.exists_ttGauge`
  (Prop 2.6, corrected), not by the printed one
  (`LinearizedGravity.not_isTT_gaugeAmp_printed`, `not_isTT_gaugeAmp_printed_contra`); the field
  equation of Prop 2.4(b) on which Prop 2.5 rests is false as printed
  (`LinearizedGravity.not_Hjet_eq_neg_boxJ`, corrected by `Feec.LinearizedGravity.Hsym_lorentz`);
  and the tidal accelerations `aⁱ = -R^i₀ⱼ₀ vʲ` of the electric field `E` that the instance
  evolves are not those printed after (2.15) (`LinearizedGravity.not_accel_printed`).

* **The vacuum equation** (the TT plane waves solve `H = 0`, the linearized vacuum `G = 0`, by
  `Feec.LinearizedGravity.exists_ttGauge` and `Feec.LinearizedGravity.Hjet_eq_einstein`).
  `G = 0 ⇔ Ric = 0` holds in every dimension `n ≠ 2` (`Feec.CurvatureTensor.einstein_eq_zero_iff`)
  and the hypothesis is sharp: it fails in dimension `2`
  (`Curvature.exists_einstein_eq_zero_ne_zero_two`). The crown's physics is four-dimensional.

## Main definitions

* `CrownSharpness`, `CrownCorrections`.

## Main results

* **`crownSharpness`**, **`crownCorrections`**; `deRham_not_staticVerdict`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §2.4, §2.8, §4.2, §4.6, §4.8, §4.10–4.11, §5.2, §6.2
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3, Thms 3.6, 3.7
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

universe u v w

/-- **What the counterexamples show about the crown's hypotheses** (`ConformingFamily.Verdict`):
closed range is necessary for the static verdict; the reducing hypothesis of the residual clauses
fails for the TSD constraint, so only the departure branch applies to it; the subcomplex
hypothesis fails for the pairs `P_{r+1}Λ⁰ × P_r⁻Λ¹`; bounded cochain projections are equivalent
to discrete stability; the right inverses of the explicit BGG map do not exist between the `L²`
domains of the Hessian, elasticity and div-div diagrams. Each field is the statement of the named
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
  /-- `Verdict.static`, bounded projections (the hypothesis `SubcomplexFamily.IsGraphBounded` of
  `SubcomplexFamily.staticFEEC`): under closed range, a family of subcomplexes on `Vₕ` with
  uniformly graph-bounded projections exists iff the discrete Poincaré inequality and the
  harmonic bound hold uniformly (a characterization; [AFW2010], Thms 3.6, 3.7) -/
  projections : type_of% @HilbertComplex.SubcomplexFamily.exists_isGraphBounded_iff.{u, v, u, v}
  /-- `BGG.HilbertData.BGGVerdict`, right inverses of `Sᴶ` (`BGG.Data.InjSurjWith`): none exist
  between the `L²` domains of the Hessian diagram from any `J ≤ 0`, `S⁰ = I : H¹ → H(curl)` is
  not onto, so the explicit-map fields are vacuous there -/
  injSurjWith_hessian : type_of% @Domain.hessianMaximalData_not_injSurjWith.{u}
  /-- the same for the elasticity diagram from any `J ≤ 1` (`S¹ = T - tr`) -/
  injSurjWith_elasticity : type_of% @Domain.elasticityMaximalData_not_injSurjWith.{u}
  /-- the same for the div-div diagram from any `J ≤ 2` (`S² = I : H(div) → L²`) -/
  injSurjWith_divDiv : type_of% @Domain.divDivMaximalData_not_injSurjWith.{u}

/-- **What the counterexamples show about the crown's hypotheses** (`CrownSharpness`). -/
theorem crownSharpness : CrownSharpness.{u, v} :=
  ⟨Fredholm.periodic_not_staticVerdict, Fredholm.periodicFamily_not_staticVerdict,
    deRham_not_staticVerdict, BoundedDomainTSD.tsd_not_propagates,
    BoundedSymTSD.tsd_not_propagates, EveryBallSymTSD.tsd_not_propagates,
    BoundedBGG.bggComplex_verdict, CubeStationary.mem_invariantCore_tsd_iff,
    BoxStationary.mem_invariantCore_tsd_iff_box, BallEigenDense.coreSub_le_stationary_ball3_iff,
    PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus,
    HilbertComplex.SubcomplexFamily.exists_isGraphBounded_iff,
    Domain.hessianMaximalData_not_injSurjWith, Domain.elasticityMaximalData_not_injSurjWith,
    Domain.divDivMaximalData_not_injSurjWith⟩

/-! ### Thesis corrections -/

/-- **What the thesis corrections show next to the crown** (`ConformingFamily.Verdict`): the
weak-symmetry discretization, which is not a stacked BGG family, has neither uniqueness without
exactness at `V_h¹` nor existence for every datum; the second-order wave form is not equivalent to
the first-order one of `Verdict.wave`, except under a compatibility condition; the TT plane waves
of the Einstein–Bianchi instance are reached by a corrected gauge, and the printed field equation
and tidal accelerations of §2.8 are false; `G = 0 ⇔ Ric = 0` fails in dimension `2`. Each field
is the statement of the named theorem; none involves a crown object. -/
structure CrownCorrections : Prop where
  /-- stacked BGG families: without exactness at `V_h¹` the discrete mixed system (5.6) of the
  weak-symmetry complex is not uniquely solvable (Props 5.3–5.4) -/
  stacked_exact : type_of% @DiscreteBGG.mixed_not_unique_of_not_exactTop
  /-- stacked BGG families: the semidiscrete weak-symmetry system (6.3) has no solution for some
  data (Prop 6.2 refuted) -/
  stacked_wellPosed : type_of% @ConstrainedEvolution.not_forall_exists_discreteSolution
  /-- `Verdict.wave`, formulation: the second-order weak form has solutions that are the `u` of
  no mixed (first-order) solution when `ker d ≠ 0` (§4.8 refuted) -/
  wave_secondOrder : type_of% @MixedWave.not_isMixedWeak.{u, v, w}
  /-- `Verdict.wave`, formulation: second-order solutions with `u̇(a) = -d* ρ₀` weakly are the `u`
  of mixed solutions (§4.8, corrected) -/
  wave_secondOrder_compatible : type_of% @HodgeWave.IsSecondOrderWeak.exists_isMixedWeak.{u, v, w}
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
  /-- `Verdict.wave`, formulation: the compatibility condition is necessary, a second-order
  solution with `(u̇(a), z) ≠ 0` for some `z ∈ ker d` is the `u` of no mixed solution (§4.8) -/
  wave_secondOrder_necessary : type_of% @HodgeWave.not_isMixedWeak_of_inner_ne_zero.{u, v, w}
  /-- the vacuum equation: `G = 0 ⇔ Ric = 0` fails in dimension `2` (§2.4) -/
  vacuum_dim_two : type_of% @Curvature.exists_einstein_eq_zero_ne_zero_two.{u}

/-- **What the thesis corrections show next to the crown** (`CrownCorrections`). -/
theorem crownCorrections : CrownCorrections.{u, v, w} :=
  ⟨DiscreteBGG.mixed_not_unique_of_not_exactTop,
    ConstrainedEvolution.not_forall_exists_discreteSolution, MixedWave.not_isMixedWeak,
    HodgeWave.IsSecondOrderWeak.exists_isMixedWeak, Feec.LinearizedGravity.exists_ttGauge,
    LinearizedGravity.not_isTT_gaugeAmp_printed,
    LinearizedGravity.not_isTT_gaugeAmp_printed_contra, LinearizedGravity.not_Hjet_eq_neg_boxJ,
    LinearizedGravity.not_accel_printed, HodgeWave.not_isMixedWeak_of_inner_ne_zero,
    Curvature.exists_einstein_eq_zero_ne_zero_two⟩

end Feec.Counterexamples
