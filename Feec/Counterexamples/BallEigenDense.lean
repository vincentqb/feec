module

public import Feec.Counterexamples.BallEigenfields
public import Feec.Models.StarShaped.EigenDense

/-!
# A complete set of eigenvectors on the unit ball

On the unit ball, the eigenvectors of `L²` for the minimal grad–curl complex span a dense subspace
([Hiptmair2002], §4.1), so the invariant core `K*` of `{0} × L²(TSD) × L²(TSD)` is stationary iff
no nonzero TSD eigenfield `u` has `curl u ∉ H̊(curl)` (cf. [QuennevilleBelair2015], Prop 4.17).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], §4.1

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Feec.Domain Feec.Models.BoundedDomain Feec.Models.StarShaped
open Feec.Counterexamples.BallSymTSD (rho ball3 isOpen_ball3 isBounded_ball3)

namespace Feec.Counterexamples.BallEigenDense

-- Over `ℝ` the generic real structure on the window spaces duplicates the inner-product one.
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

open Feec.Counterexamples.BallEigenfields

theorem ball3_eq_euclBall : ball3 = euclBall 0 1 := by
  ext x
  simp [ball3, euclBall, rho, Fin.sum_univ_three, sq]

theorem convex_ball3 : Convex ℝ ball3 :=
  ball3_eq_euclBall ▸ convex_euclBall 0 1

/-- The eigenvectors of `L²` on the unit ball span a dense subspace. -/
theorem eigenDense_gradCurl_ball3 : (gradCurl ℝ isOpen_ball3).EigenDense :=
  eigenDense_gradCurl_convex isOpen_ball3 isBounded_ball3 convex_ball3

/-- On the unit ball, `K*` is stationary iff no nonzero TSD eigenfield `u` has
`curl u ∉ H̊(curl)`. -/
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

/-- On the unit ball, `K*` is stationary if `MaxwellEigenfieldRegularity` holds. -/
theorem coreSub_le_stationary_ball3_of_maxwellRegularity
    (hM : MaxwellEigenfieldRegularity ball3) :
    (gradCurl ℝ isOpen_ball3).coreSub (tsd ball3) (tsd ball3) ≤
      (gradCurl ℝ isOpen_ball3).stationary :=
  coreSub_le_stationary_ball_of_maxwellRegularity eigenDense_gradCurl_ball3 hM

end Feec.Counterexamples.BallEigenDense
