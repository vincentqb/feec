module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.Counterexamples.BallEigenDense
public import Feec.Counterexamples.BoundedBGG
public import Feec.Counterexamples.BoxStationary
public import Feec.Counterexamples.ClassicalRegularity
public import Feec.Counterexamples.ConstrainedEvolution
public import Feec.Counterexamples.CubeStationary
public import Feec.Counterexamples.DiscreteBGG
public import Feec.Counterexamples.EveryBallSymTSD
public import Feec.Counterexamples.MixedWave
public import Feec.Counterexamples.NonClosedRangeEuclidean
public import Feec.Counterexamples.PolynomialForms

/-!
# The crown is sharp

`CrownSharpness` collects, for the hypotheses of the FEEC theorem
(`Feec.HilbertComplex.ConformingFamily.feec`, `Feec.HilbertComplex.ConformingFamily.Verdict`) and
of the layer verdicts its fields are, a counterexample showing that the hypothesis cannot be
dropped or is not automatic; `crownSharpness` proves it. Each field is the statement of a theorem,
by reference (`type_of%`).

* **Closed range** (the hypothesis `hcr` of `Verdict.static`, and of `Verdict.heat`). It is
  necessary: the uniform discrete Poincaré inequality of a conforming family forces closed range
  (`Feec.HilbertComplex.ConformingFamily.StaticVerdict.closedRangeAt`). Finite-dimensional
  harmonic forms do not give it: the periodic complex `ℓ² --A--> ℓ² --0--> ℓ² --A--> ⋯` on
  `ComplexShape.up ℕ`, `A = diag(1/(n+1))`, has `ℌᵏ = 0` and a conforming family
  (`Fredholm.periodicFamily`, the truncations), but no conforming family of it has the static
  verdict in even degrees (`Fredholm.periodic_not_staticVerdict`,
  `Fredholm.periodicFamily_not_staticVerdict`; [QuennevilleBelair2015], §4.2 refuted, see
  `Feec.Counterexamples.Fredholm`). Nor does it hold for the `L²` de Rham complex of `ℝᵈ`
  (`deRham_not_staticVerdict`, `Feec.Counterexamples.NonClosedRangeEuclidean`).
* **Closed operators** (a Hilbert complex has closed differentials, so its cycles are closed): a
  densely defined operator can have a non-closed kernel (`exists_dense_not_isClosed_ker`).
* **Uniqueness in the static well-posedness** (`StaticVerdict.wellPosed` asserts unique
  solvability): solvability for every datum without uniqueness gives no inf-sup constant
  (`surjective_not_infSup`).
* **Reducing constraints** (the propagation clause `ConstrainedFEEC.Verdict.propagates_iff` and
  the residual clauses `residual_le`, `residual_tendsto` of `Verdict.constrained` need `K` to
  reduce `L`). The physical constraint does not: on every nonempty bounded open `Ω ⊆ ℝ³` the
  thesis' TSD constraint is left by a datum of `D(L) ∩ K`, so it reduces the wave operator of no
  grad–curl complex (`BoundedDomainTSD.tsd_not_propagates`), of no Hessian–curl complex
  (`BoundedSymTSD.tsd_not_propagates`), of the Hessian–curl complex with the printed boundary
  conditions on every ball (`EveryBallSymTSD.tsd_not_propagates`), nor of the BGG weak-symmetry
  system (`BoundedBGG.bggComplex_verdict`); the crown's departure clause `leaves` is the case that
  occurs. Its largest reducing part (the invariant core) consists of stationary data on cubes and
  boxes (`CubeStationary.mem_invariantCore_tsd_iff`, `BoxStationary.mem_invariantCore_tsd_iff_box`)
  and is decided by TSD eigenfields on the ball (`BallEigenDense.coreSub_le_stationary_ball3_iff`).
* **Rate classes** (the rate clauses take data of a rate class, in `D(L²)`, not only `D(L)`): a
  datum of `D(L) \ D(L²)` has no strong solution `C¹` into the graph space
  (`ClassicalRegularity.exists_datum_not_C1`), although the semidiscrete solutions still converge.
* **The mixed formulation** (the crown discretizes the first-order Hodge wave equation): the
  second-order weak form is not equivalent to it (`MixedWave.not_isMixedWeak`).
* **Subcomplexes** (a conforming family consists of subcomplexes): the pairs
  `P_{r+1}Λ⁰ × P_r⁻Λ¹` are not (`PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus`).
* **Outside the crown, BGG discretizations**: the discrete mixed system needs exactness at
  `V_h¹` (`DiscreteBGG.mixed_not_unique_of_not_exactTop`), and the semidiscrete system (6.3) is
  not solvable for every datum (`ConstrainedEvolution.not_forall_exists_discreteSolution`).

## Main definitions

* `Fredholm.periodicFamily`: the truncation family of the periodic complex.
* `CrownSharpness`.

## Main results

* **`crownSharpness`**; `Fredholm.periodic_not_staticVerdict`, `deRham_not_staticVerdict`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2, §4.6, §4.8, §4.10–4.11, Ch. 5–6
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.Counterexamples

/-! ### A conforming family of the periodic complex -/

namespace Fredholm

open Ell2 (L2)
open ClassicalRegularity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The truncation `P_N` is the orthogonal projection onto `span{e₀, …, e_{N-1}}`. -/
theorem starProjection_trunc (N : ℕ) (x : L2 𝕜) :
    (trunc 𝕜 N).starProjection x = truncSum 𝕜 N x := by
  refine Submodule.eq_starProjection_of_mem_orthogonal (truncSum_mem N x)
    ((Submodule.mem_orthogonal _ _).2 fun y hy => ?_)
  rw [lp.inner_eq_tsum]
  refine (tsum_congr fun m => ?_).trans tsum_zero
  rw [lp.coeFn_sub, Pi.sub_apply, truncSum_apply]
  split_ifs with h
  · rw [sub_self, inner_zero_right]
  · rw [hy m (not_lt.1 h), inner_zero_left]

/-- `A = diag(1/(n+1))` commutes with the truncations. -/
theorem diag_truncSum (N : ℕ) (x : L2 𝕜) : diag 𝕜 (truncSum 𝕜 N x) = truncSum 𝕜 N (diag 𝕜 x) :=
  lp.ext <| funext fun m => by
    simp only [diag_apply, truncSum_apply]
    split_ifs <;> simp

/-- Every differential of the periodic complex is an everywhere-defined `g ∈ {A, 0}`, and `g`
commutes with the truncations. -/
theorem periodic_d_eq (i j : ℕ) : ∃ g : L2 𝕜 →ₗ[𝕜] L2 𝕜, (periodic 𝕜).d i j = g.toPMap ⊤ ∧
    ∀ N x, g ((trunc 𝕜 N).starProjection x) = (trunc 𝕜 N).starProjection (g x) := by
  have h0 : (0 : L2 𝕜 →ₗ.[𝕜] L2 𝕜) = (0 : L2 𝕜 →ₗ[𝕜] L2 𝕜).toPMap ⊤ := rfl
  by_cases h : i + 1 = j
  · subst h
    rw [periodic_d_succ]
    rcases Nat.even_or_odd i with hi | hi
    · exact ⟨diag 𝕜, periodicD_of_even hi, fun N x => by
        simp only [ContinuousLinearMap.coe_coe, starProjection_trunc, diag_truncSum]⟩
    · exact ⟨0, (periodicD_of_odd hi).trans h0, fun N x => by simp⟩
  · exact ⟨0, ((periodic 𝕜).shape i j h).trans h0, fun N x => by simp⟩

variable (𝕜) in
/-- The truncation subcomplexes `span{e₀, …, e_{N-1}}` in every degree of the periodic complex. -/
def periodicTrunc (N : ℕ) : (periodic 𝕜).Subcomplex where
  V _ := trunc 𝕜 N
  le_domain i j x _ := by
    obtain ⟨g, hg, -⟩ := periodic_d_eq (𝕜 := 𝕜) i j
    rw [hg]; trivial
  mapsTo i j x hx := by
    obtain ⟨g, hg, hc⟩ := periodic_d_eq (𝕜 := 𝕜) i j
    rw [LinearPMap.apply_of_eq_toPMap hg, ← (trunc 𝕜 N).starProjection_eq_self_iff.2 hx, hc]
    exact (trunc 𝕜 N).starProjection_apply_mem _

variable (𝕜) in
/-- **A conforming family of the periodic complex** `ℓ² --A--> ℓ² --0--> ℓ² --A--> ⋯`: the
truncations `span{e₀, …, e_{N-1}}`, `N → ∞`, with the orthogonal projections onto them, of norm
`1`, which commute with `A`. So the crown applies to it, although the complex has no closed
range. -/
def periodicFamily : HilbertComplex.ConformingFamily (periodic 𝕜) ℕ where
  l := atTop
  V := periodicTrunc 𝕜
  finiteDimensional N _ := inferInstanceAs (FiniteDimensional 𝕜 (trunc 𝕜 N))
  π N :=
    { π := fun _ => (trunc 𝕜 N).starProjection
      mem := fun _ x => (trunc 𝕜 N).starProjection_apply_mem x
      proj := fun _ x hx => (trunc 𝕜 N).starProjection_eq_self_iff.2 hx
      comm := fun i j x => by
        obtain ⟨g, hg, hc⟩ := periodic_d_eq (𝕜 := 𝕜) i j
        rw [LinearPMap.apply_of_eq_toPMap hg, LinearPMap.apply_of_eq_toPMap hg]
        exact hc N x }
  bound_π := ⟨1, fun N _ x => by
    simpa using (trunc 𝕜 N).norm_starProjection_apply_le x⟩
  approx _ w := by
    refine squeeze_zero (fun _ => infDist_nonneg)
      (fun N => infDist_le_dist_of_mem ((trunc 𝕜 N).starProjection_apply_mem w)) ?_
    simpa [starProjection_trunc, dist_comm] using
      (tendsto_iff_dist_tendsto_zero.1 (tendsto_truncSum (𝕜 := 𝕜) w))

/-- The truncation family is refined along `N → ∞`. -/
instance : (periodicFamily 𝕜).l.NeBot := inferInstanceAs (atTop : Filter ℕ).NeBot

/-- **Without closed range the static verdict fails, although `ℌ = 0`**: no conforming family of
the periodic complex (along a nontrivial filter) has the static verdict at an even degree, since
its uniform discrete Poincaré inequality would close `𝔅ᵏ⁺¹ = R(A)`
(`ConformingFamily.StaticVerdict.closedRangeAt`). [QuennevilleBelair2015], §4.2; [AFW2010], §3.3 -/
theorem periodic_not_staticVerdict {κ : Type*}
    (F : HilbertComplex.ConformingFamily (periodic 𝕜) κ) [F.l.NeBot] {k : ℕ} (hk : Even k) :
    ¬ F.StaticVerdict k := fun hV =>
  periodic_not_closedRangeAt hk (hV.closedRangeAt rfl)

/-- The periodic complex has `ℌ = 0` and a conforming family without the static verdict at `0`. -/
theorem periodicFamily_not_staticVerdict :
    (∀ k, (periodic 𝕜).harmonic k = ⊥) ∧ ¬ (periodicFamily 𝕜).StaticVerdict 0 :=
  ⟨periodic_harmonic_eq_bot, periodic_not_staticVerdict _ ⟨0, rfl⟩⟩

end Fredholm

/-! ### The de Rham complex of `ℝᵈ` -/

/-- **No conforming family of the `L²` de Rham complex of `ℝᵈ` has the static verdict** in the
degrees `k < d`, along a nontrivial filter: the uniform discrete Poincaré inequality would close
`𝔅ᵏ⁺¹` (`ConformingFamily.StaticVerdict.closedRangeAt`, `deRham_not_closedRange`), although
`ℌ = 0`. [QuennevilleBelair2015], §4.2 -/
theorem deRham_not_staticVerdict (d : Type*) [Fintype d] [LinearOrder d] [Nonempty d]
    {κ : Type*} (F : HilbertComplex.ConformingFamily (Models.Euclidean.DeRham.complex d) κ)
    [F.l.NeBot] {k : ℕ} (hk : k < Fintype.card d) : ¬ F.StaticVerdict k := fun hV =>
  ((deRham_not_closedRange d).2 k hk).1 (hV.closedRangeAt rfl)

/-! ### The sharpness of the crown -/

universe u v

/-- **The sharpness of the FEEC theorem**: for each hypothesis of the crown
(`ConformingFamily.Verdict`) or of the layer verdict a field of it is, a counterexample showing
that it cannot be dropped, or that it fails for the complexes and constraints of interest. Each
field is the statement of the named theorem. -/
structure CrownSharpness : Prop where
  /-- `Verdict.static`, closed range: without it, no conforming family of the periodic complex
  (`ℌ = 0`) has the static verdict in even degrees -/
  closedRange : type_of% @Fredholm.periodic_not_staticVerdict.{u, v}
  /-- `Verdict.static`, closed range: and the periodic complex has a conforming family -/
  closedRange_family : type_of% @Fredholm.periodicFamily_not_staticVerdict.{u}
  /-- `Verdict.static`, closed range: it fails for the de Rham complex of `ℝᵈ` -/
  closedRange_euclidean : type_of% @deRham_not_staticVerdict.{u, v}
  /-- closed differentials (`HilbertComplex.closed`): a densely defined operator with a
  non-closed kernel -/
  closedOperators : type_of% @exists_dense_not_isClosed_ker.{u}
  /-- `StaticVerdict.wellPosed`, uniqueness: solvability alone gives no inf-sup constant -/
  wellPosed : type_of% @surjective_not_infSup.{u}
  /-- `Verdict.constrained`, `K` reducing `L`: TSD is left on bounded domains (grad–curl) -/
  reducing_gradCurl : type_of% @BoundedDomainTSD.tsd_not_propagates
  /-- `Verdict.constrained`, `K` reducing `L`: TSD is left on bounded domains (Hessian–curl) -/
  reducing_hessCurl : type_of% @BoundedSymTSD.tsd_not_propagates
  /-- `Verdict.constrained`, `K` reducing `L`: TSD is left on every ball (printed boundary
  conditions) -/
  reducing_ball : type_of% @EveryBallSymTSD.tsd_not_propagates
  /-- `Verdict.constrained`, `K` reducing `L`: TSD is left by the BGG weak-symmetry system -/
  reducing_bgg : type_of% @BoundedBGG.bggComplex_verdict
  /-- `Verdict.constrained`: the largest reducing part of TSD on a cube is stationary -/
  core_cube : type_of% @CubeStationary.mem_invariantCore_tsd_iff
  /-- `Verdict.constrained`: the largest reducing part of TSD on a box is stationary -/
  core_box : type_of% @BoxStationary.mem_invariantCore_tsd_iff_box
  /-- `Verdict.constrained`: on the ball it is stationary iff there is no moving TSD
  eigenfield -/
  core_ball : type_of% @BallEigenDense.coreSub_le_stationary_ball3_iff
  /-- `ConstrainedFEEC.Verdict.rate`, rate classes: `D(L)` data need not be `C¹` in the graph
  space -/
  regularity : type_of% @ClassicalRegularity.exists_datum_not_C1.{u}
  /-- `Verdict.wave`, the mixed formulation: the second-order weak form is not equivalent -/
  formulation : type_of% @MixedWave.not_isMixedWeak.{u, v, v}
  /-- `ConformingFamily.V`, subcomplexes: `P_{r+1}Λ⁰ × P_r⁻Λ¹` is not one -/
  subcomplex : type_of% @PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus.{u, v}
  /-- outside the crown (BGG): the discrete mixed system needs exactness at `V_h¹` -/
  bgg_exactness : type_of% @DiscreteBGG.mixed_not_unique_of_not_exactTop
  /-- outside the crown (BGG): the semidiscrete system needs compatible data -/
  bgg_compatibility : type_of% @ConstrainedEvolution.not_forall_exists_discreteSolution

/-- **The crown is sharp** (`CrownSharpness`). -/
theorem crownSharpness : CrownSharpness.{u, v} :=
  ⟨Fredholm.periodic_not_staticVerdict, Fredholm.periodicFamily_not_staticVerdict,
    deRham_not_staticVerdict, exists_dense_not_isClosed_ker, surjective_not_infSup,
    BoundedDomainTSD.tsd_not_propagates, BoundedSymTSD.tsd_not_propagates,
    EveryBallSymTSD.tsd_not_propagates, BoundedBGG.bggComplex_verdict,
    CubeStationary.mem_invariantCore_tsd_iff, BoxStationary.mem_invariantCore_tsd_iff_box,
    BallEigenDense.coreSub_le_stationary_ball3_iff, ClassicalRegularity.exists_datum_not_C1,
    MixedWave.not_isMixedWeak, PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus,
    DiscreteBGG.mixed_not_unique_of_not_exactTop,
    ConstrainedEvolution.not_forall_exists_discreteSolution⟩

end Feec.Counterexamples
