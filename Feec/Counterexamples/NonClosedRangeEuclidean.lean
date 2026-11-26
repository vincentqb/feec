module

public import Feec.Models.Euclidean.BGG
public import Feec.Models.Euclidean.DeRham
public import Feec.Models.Euclidean.GradCurl
public import Feec.Models.Euclidean.SymCurl

/-!
# Hilbert complexes on `ℝᵈ` without closed range

The `L²` de Rham complex of `ℝᵈ` and the grad–curl, Hessian–curl and BGG Hessian complexes of
`ℝ³` do not have closed range (cf. [QuennevilleBelair2015], §4.2).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Counterexamples

open Models.Euclidean

/-- The `L²` de Rham complex of `ℝᵈ` has no harmonic forms, and in the degrees `1 ≤ k ≤ d` its
range is not closed and its boundaries are not its cycles. -/
theorem deRham_not_closedRange (d : Type*) [Fintype d] [LinearOrder d] [Nonempty d] :
    (∀ k, (DeRham.complex d).harmonic k = ⊥) ∧
      ∀ k, k < Fintype.card d → ¬ (DeRham.complex d).ClosedRangeAt (k + 1) ∧
        (DeRham.complex d).boundaries (k + 1) ≠ (DeRham.complex d).cycles (k + 1) :=
  ⟨DeRham.harmonic_eq_bot, fun _ hk =>
    ⟨DeRham.not_closedRangeAt hk, DeRham.boundaries_ne_cycles hk⟩⟩

/-- Both differentials of the grad–curl and Hessian–curl complexes of `ℝ³` and the first of its
BGG Hessian complex do not have closed range. -/
theorem euclidean_not_closedRange :
    ¬ GradCurl.complex.ClosedRangeAt 1 ∧ ¬ GradCurl.complex.ClosedRangeAt 2 ∧
      ¬ SymCurl.complex.ClosedRangeAt 1 ∧ ¬ SymCurl.complex.ClosedRangeAt 2 ∧
      ¬ BGG.complex.ClosedRangeAt 1 :=
  ⟨GradCurl.not_closedRangeAt_one, GradCurl.not_closedRangeAt_two, SymCurl.not_closedRangeAt_one,
    SymCurl.not_closedRangeAt_two, BGG.not_closedRangeAt_one⟩

/-- No `C` gives `‖u‖ ≤ C ‖∇u‖` for all `u ∈ H¹(ℝ³) ∩ (ker ∇)ᗮ`. -/
theorem not_poincare_grad :
    ¬ ∃ C : ℝ, ∀ x : (GradCurl.complex.d 0 1).domain,
      (x : GradCurl.Space 0) ∈ (GradCurl.complex.cycles 0)ᗮ →
        ‖(x : GradCurl.Space 0)‖ ≤ C * ‖GradCurl.complex.d 0 1 x‖ := by
  rw [← GradCurl.complex.closedRangeAt_iff_poincare_of_rel
    (show ComplexShape.fin3.Rel 0 1 from rfl)]
  exact GradCurl.not_closedRangeAt_one

/-- No `C` gives `‖u‖ ≤ C ‖curl u‖` for all `u ∈ H(curl; ℝ³) ∩ (ker curl)ᗮ`. -/
theorem not_poincare_curl :
    ¬ ∃ C : ℝ, ∀ x : (GradCurl.complex.d 1 2).domain,
      (x : GradCurl.Space 1) ∈ (GradCurl.complex.cycles 1)ᗮ →
        ‖(x : GradCurl.Space 1)‖ ≤ C * ‖GradCurl.complex.d 1 2 x‖ := by
  rw [← GradCurl.complex.closedRangeAt_iff_poincare_of_rel
    (show ComplexShape.fin3.Rel 1 2 from rfl)]
  exact GradCurl.not_closedRangeAt_two

end Feec.Counterexamples
