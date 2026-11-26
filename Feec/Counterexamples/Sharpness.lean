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
public import Feec.Counterexamples.PositiveCharacteristic
public import Feec.Domain.BGGRealization

/-!
# Sharpness of the hypotheses of the FEEC theorem

`CrownSharpness` collects, as statements of theorems, what the counterexamples show about the
hypotheses of `Feec.HilbertComplex.ConformingFamily.Verdict`; `CrownCorrections` collects the
counterexamples to statements of [QuennevilleBelair2015] and their adapted forms.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.Counterexamples

/-! ### The de Rham complex of `ℝᵈ` -/

/-- No conforming family of the `L²` de Rham complex of `ℝᵈ` along a nontrivial filter has the
static verdict in a degree `k < d`. -/
theorem deRham_not_staticVerdict (d : Type*) [Fintype d] [LinearOrder d] [Nonempty d]
    {κ : Type*} (F : HilbertComplex.ConformingFamily (Models.Euclidean.DeRham.complex d) κ)
    [F.l.NeBot] {k : ℕ} (hk : k < Fintype.card d) : ¬ F.StaticVerdict k := fun hV =>
  ((deRham_not_closedRange d).2 k hk).1 (hV.closedRangeAt rfl)

/-! ### Sharpness -/

universe u v w

/-- The sharpness of the hypotheses of `ConformingFamily.Verdict`, one theorem per field. -/
structure CrownSharpness : Prop where
  /-- closed range: the periodic complex -/
  closedRange : type_of% @Fredholm.periodic_not_staticVerdict.{u, v}
  /-- closed range: a family of the periodic complex -/
  closedRange_family : type_of% @Fredholm.periodicFamily_not_staticVerdict.{u}
  /-- closed range: the de Rham complex of `ℝᵈ` -/
  closedRange_euclidean : type_of% @deRham_not_staticVerdict.{u, v}
  /-- reducing `K`: grad–curl on bounded domains -/
  reducing_gradCurl : type_of% @BoundedDomainTSD.tsd_not_propagates
  /-- reducing `K`: Hessian–curl on bounded domains -/
  reducing_hessCurl : type_of% @BoundedSymTSD.tsd_not_propagates
  /-- reducing `K`: Hessian–curl on every ball -/
  reducing_ball : type_of% @EveryBallSymTSD.tsd_not_propagates
  /-- reducing `K`: the BGG weak-symmetry system -/
  reducing_bgg : type_of% @BoundedBGG.bggComplex_verdict
  /-- the invariant core of TSD on a cube -/
  core_cube : type_of% @CubeStationary.mem_invariantCore_tsd_iff
  /-- the invariant core of TSD on a box -/
  core_box : type_of% @BoxStationary.mem_invariantCore_tsd_iff_box
  /-- the invariant core of TSD on the ball -/
  core_ball : type_of% @BallEigenDense.coreSub_le_stationary_ball3_iff
  /-- subcomplexes: `P_{r+1}Λ⁰ × P_r⁻Λ¹` -/
  subcomplex : type_of% @PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus.{u, v}
  /-- bounded projections and uniform discrete stability -/
  projections : type_of% @HilbertComplex.SubcomplexFamily.exists_isGraphBounded_iff.{u, v, u, v}
  /-- right inverses of `Sᴶ`: the Hessian diagram -/
  injSurjWith_hessian : type_of% @Domain.hessianMaximalData_not_injSurjWith.{u}
  /-- the same, elasticity diagram -/
  injSurjWith_elasticity : type_of% @Domain.elasticityMaximalData_not_injSurjWith.{u}
  /-- the same, div-div diagram -/
  injSurjWith_divDiv : type_of% @Domain.divDivMaximalData_not_injSurjWith.{u}
  /-- characteristic `0`: exactness of closed polynomial forms -/
  charZero_exact : type_of% @PositiveCharacteristic.charZero_iff_closed_eq_exact.{u}

/-- Proof of `CrownSharpness`. -/
theorem crownSharpness : CrownSharpness.{u, v} :=
  ⟨Fredholm.periodic_not_staticVerdict, Fredholm.periodicFamily_not_staticVerdict,
    deRham_not_staticVerdict, BoundedDomainTSD.tsd_not_propagates,
    BoundedSymTSD.tsd_not_propagates, EveryBallSymTSD.tsd_not_propagates,
    BoundedBGG.bggComplex_verdict, CubeStationary.mem_invariantCore_tsd_iff,
    BoxStationary.mem_invariantCore_tsd_iff_box, BallEigenDense.coreSub_le_stationary_ball3_iff,
    PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus,
    HilbertComplex.SubcomplexFamily.exists_isGraphBounded_iff,
    Domain.hessianMaximalData_not_injSurjWith, Domain.elasticityMaximalData_not_injSurjWith,
    Domain.divDivMaximalData_not_injSurjWith, PositiveCharacteristic.charZero_iff_closed_eq_exact⟩

/-! ### Counterexamples and adapted statements -/

/-- Counterexamples to statements of [QuennevilleBelair2015] and adapted forms, one per field. -/
structure CrownCorrections : Prop where
  /-- (5.6) needs exactness at `V_h¹` (Props 5.3–5.4) -/
  stacked_exact : type_of% @DiscreteBGG.mixed_not_unique_of_not_exactTop
  /-- (6.3) is not solvable for all data (Prop 6.2) -/
  stacked_wellPosed : type_of% @ConstrainedEvolution.not_forall_exists_discreteSolution
  /-- second-order solutions without mixed counterpart (§4.8) -/
  wave_secondOrder : type_of% @MixedWave.not_isMixedWeak.{u, v, w}
  /-- second-order and mixed solutions under `u̇(a) = -d* ρ₀` (§4.8, adapted) -/
  wave_secondOrder_compatible : type_of% @HodgeWave.IsSecondOrderWeak.exists_isMixedWeak.{u, v, w}
  /-- a gauge vector reaching TT gauge (Prop 2.6, adapted) -/
  tt_gauge : type_of% @Feec.LinearizedGravity.exists_ttGauge
  /-- `BPrinted` does not reach TT gauge (Prop 2.6) -/
  tt_gauge_printed : type_of% @LinearizedGravity.not_isTT_gaugeAmp_printed
  /-- nor its contravariant reading (Prop 2.6) -/
  tt_gauge_printed_contra : type_of% @LinearizedGravity.not_isTT_gaugeAmp_printed_contra
  /-- `H ≠ -□h̄` for a Lorentz-gauge jet (Prop 2.4(b)) -/
  lorentz_printed : type_of% @LinearizedGravity.not_Hjet_eq_neg_boxJ
  /-- the tidal acceleration of a TT plane wave (§2.8) -/
  accel_printed : type_of% @LinearizedGravity.not_accel_printed
  /-- the compatibility condition is necessary (§4.8) -/
  wave_secondOrder_necessary : type_of% @HodgeWave.not_isMixedWeak_of_inner_ne_zero.{u, v, w}
  /-- `G = 0 ⇔ Ric = 0` fails in dimension `2` (§2.4) -/
  vacuum_dim_two : type_of% @Curvature.exists_einstein_eq_zero_ne_zero_two.{u}

/-- Proof of `CrownCorrections`. -/
theorem crownCorrections : CrownCorrections.{u, v, w} :=
  ⟨DiscreteBGG.mixed_not_unique_of_not_exactTop,
    ConstrainedEvolution.not_forall_exists_discreteSolution, MixedWave.not_isMixedWeak,
    HodgeWave.IsSecondOrderWeak.exists_isMixedWeak, Feec.LinearizedGravity.exists_ttGauge,
    LinearizedGravity.not_isTT_gaugeAmp_printed,
    LinearizedGravity.not_isTT_gaugeAmp_printed_contra, LinearizedGravity.not_Hjet_eq_neg_boxJ,
    LinearizedGravity.not_accel_printed, HodgeWave.not_isMixedWeak_of_inner_ne_zero,
    Curvature.exists_einstein_eq_zero_ne_zero_two⟩

end Feec.Counterexamples
