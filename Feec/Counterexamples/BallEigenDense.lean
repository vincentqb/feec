module

public import Feec.Counterexamples.BallEigenfields
public import Feec.Models.StarShaped.EigenDense

/-!
# A complete set of eigenvectors on the unit ball, and the stationarity of `K*`

`Feec.Counterexamples.BallEigenfields` decides whether the invariant core `K*` of
`K = {0} × L²(TSD) × L²(TSD)` on the unit ball `B = {|x| < 1}` (`BallSymTSD.ball3`) is stationary,
under two hypotheses: a complete set of eigenvectors of `L²` (`EigenDense`) and the regularity of
Maxwell eigenfields up to the boundary (`MaxwellEigenfieldRegularity`). This file discharges the
first one through Weber compactness on convex domains
(`Feec.Models.StarShaped.eigenDense_gradCurl_convex`, [Hiptmair2002], §4.1; [CostabelMcIntosh2010]).

## Main results

* `ball3_eq_euclBall`: `ball3` is the Euclidean ball `euclBall 0 1`; `convex_ball3`.
* **`eigenDense_gradCurl_ball3`**: `EigenDense` for `gradCurl` on `ball3`, unconditionally.
* **`coreSub_le_stationary_ball3_iff`**: `K* ⊆ stationary` on `ball3` iff there is no `ξ > 0` and
  nonzero TSD eigenfield `u` with `curl u ∉ H̊(curl)`, unconditionally
  (`Feec.Models.StarShaped.coreSub_le_stationary_ball_iff` transported to `ball3`).
* **`coreSub_le_stationary_ball3_of_maxwellRegularity`**: `K*` on `ball3` is stationary under the
  single documented hypothesis `MaxwellEigenfieldRegularity ball3` (regularity of Maxwell
  eigenfields up to the boundary, [Evans2010], §6.3; [GiraultRaviart1986], Ch. I, §3).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], §4.1
* [M. Costabel, A. McIntosh, *On Bogovskiĭ and Regularized Poincaré Integral Operators for de Rham Complexes on Lipschitz Domains*][CostabelMcIntosh2010]
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §6.3
* [V. Girault, P.-A. Raviart, *Finite Element Methods for Navier–Stokes Equations*][GiraultRaviart1986],
  Ch. I, §3
-/

@[expose] public noncomputable section

open MeasureTheory Set Feec.Domain Feec.Models.BoundedDomain Feec.Models.StarShaped
open Feec.Counterexamples.BallSymTSD (rho ball3 isOpen_ball3 isBounded_ball3)

namespace Feec.Counterexamples.BallEigenDense

-- Over `ℝ` the generic real structure on the window spaces duplicates the inner-product one.
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

open Feec.Counterexamples.BallEigenfields

/-- The unit ball `ball3 = {ρ < 1}` is the Euclidean ball `euclBall 0 1`. -/
theorem ball3_eq_euclBall : ball3 = euclBall 0 1 := by
  ext x
  simp [ball3, euclBall, rho, Fin.sum_univ_three, sq]

theorem convex_ball3 : Convex ℝ ball3 :=
  ball3_eq_euclBall ▸ convex_euclBall 0 1

/-- **A complete set of eigenvectors on the unit ball**, unconditionally. -/
theorem eigenDense_gradCurl_ball3 : (gradCurl ℝ isOpen_ball3).EigenDense :=
  eigenDense_gradCurl_convex isOpen_ball3 isBounded_ball3 convex_ball3

/-- **`K*` on the unit ball is stationary iff there is no TSD eigenfield violating the electric
boundary condition in the magnetic slot** ([QuennevilleBelair2015], §4.10, Prop 4.17), without
hypothesis: `coreSub_le_stationary_ball_iff` on `euclBall 0 1 = ball3`. -/
theorem coreSub_le_stationary_ball3_iff :
    (gradCurl ℝ isOpen_ball3).coreSub (tsd ball3) (tsd ball3) ≤
        (gradCurl ℝ isOpen_ball3).stationary ↔
      ¬ ∃ ξ : ℝ, 0 < ξ ∧ ∃ v : L2F ℝ ball3 Ix, v ≠ 0 ∧ v ∈ tsd ball3 ∧
        (gradCurl ℝ isOpen_ball3).IsEigenfield ξ v ∧
        ∀ h1 : v ∈ (gradCurl ℝ isOpen_ball3).d₁.domain,
          ((gradCurl ℝ isOpen_ball3).d₁ ⟨v, h1⟩ : L2F ℝ ball3 Ix) ∉
            ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal ball3).domain := by
  have key : ∀ (Ω : Set R3) (hΩ : IsOpen Ω), Ω = euclBall 0 1 →
      ((gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω) ≤ (gradCurl ℝ hΩ).stationary ↔
        ¬ ∃ ξ : ℝ, 0 < ξ ∧ ∃ v : L2F ℝ Ω Ix, v ≠ 0 ∧ v ∈ tsd Ω ∧
          (gradCurl ℝ hΩ).IsEigenfield ξ v ∧
          ∀ h1 : v ∈ (gradCurl ℝ hΩ).d₁.domain,
            ((gradCurl ℝ hΩ).d₁ ⟨v, h1⟩ : L2F ℝ Ω Ix) ∉
              ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain) := by
    rintro Ω hΩ rfl
    exact coreSub_le_stationary_ball_iff 0 1
  exact key ball3 isOpen_ball3 ball3_eq_euclBall

/-- **`K*` on the unit ball is stationary under Maxwell eigenfield regularity**: G3's conditional
result `coreSub_le_stationary_ball_of_maxwellRegularity` with its `EigenDense` hypothesis
discharged (`eigenDense_gradCurl_ball3`). The single remaining hypothesis,
`MaxwellEigenfieldRegularity ball3`, is boundary regularity of Maxwell eigenfields on the ball
([Evans2010], §6.3; [GiraultRaviart1986], Ch. I, §3), absent from Mathlib. -/
theorem coreSub_le_stationary_ball3_of_maxwellRegularity
    (hM : MaxwellEigenfieldRegularity ball3) :
    (gradCurl ℝ isOpen_ball3).coreSub (tsd ball3) (tsd ball3) ≤
      (gradCurl ℝ isOpen_ball3).stationary :=
  coreSub_le_stationary_ball_of_maxwellRegularity eigenDense_gradCurl_ball3 hM

end Feec.Counterexamples.BallEigenDense
