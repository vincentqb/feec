module

public import Feec.Models.Euclidean.BGG
public import Feec.Models.Euclidean.DeRham
public import Feec.Models.Euclidean.GradCurl
public import Feec.Models.Euclidean.SymCurl

/-!
# Hilbert complexes on `ℝᵈ` without closed range

On the whole space the symbols of the differential operators degenerate at low frequencies, so
no Poincaré inequality holds and the closed-range hypothesis of the abstract theory (thesis §4.2,
Thm 4.2) fails for every complex of interest on `ℝᵈ`:

* the `L²` de Rham complex of `ℝᵈ` in every degree `1 ≤ k ≤ d`, which moreover has no harmonic
  forms and is not exact (`deRham_not_closedRange`);
* the grad–curl complex and the Hessian–curl complex (4.16) of `ℝ³`, at both differentials;
* the BGG weak-symmetry complex of `ℝ³` (the Hessian).

The proofs are `Feec.Fourier.Euclidean.not_closedRangeAt` (homogeneous nonzero symbols never
have closed range) applied in `Feec.Models.Euclidean.*`; this module states the refutations of
closed range together. Propagation of constraints on `ℝᵈ` (Props 4.17/4.19) does not need closed
range (`Feec.Models.Euclidean.GradCurl.tsd_propagates` and its siblings).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2 (closed Hilbert complexes, Thm 4.2), §4.10
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
  (closed range and Poincaré inequalities)
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992] (closed range and Poincaré
  inequalities)
-/

@[expose] public noncomputable section

namespace Feec.Counterexamples

open Models.Euclidean

/-- **The `L²` de Rham complex of `ℝᵈ` has no closed range** in the degrees `1 ≤ k ≤ d`: it has
no harmonic forms, yet the boundaries are dense in, but not equal to, the cycles. [QuennevilleBelair2015], §4.2 -/
theorem deRham_not_closedRange (d : Type*) [Fintype d] [LinearOrder d] [Nonempty d] :
    (∀ k, (DeRham.complex d).harmonic k = ⊥) ∧
      ∀ k, k < Fintype.card d → ¬ (DeRham.complex d).ClosedRangeAt (k + 1) ∧
        (DeRham.complex d).boundaries (k + 1) ≠ (DeRham.complex d).cycles (k + 1) :=
  ⟨DeRham.harmonic_eq_bot, fun _ hk =>
    ⟨DeRham.not_closedRangeAt hk, DeRham.boundaries_ne_cycles hk⟩⟩

/-- **No differential of the grad–curl, Hessian–curl or BGG Hessian complexes of `ℝ³` has
closed range.** [QuennevilleBelair2015], §4.2 -/
theorem euclidean_not_closedRange :
    ¬ GradCurl.complex.ClosedRangeAt 1 ∧ ¬ GradCurl.complex.ClosedRangeAt 2 ∧
      ¬ SymCurl.complex.ClosedRangeAt 1 ∧ ¬ SymCurl.complex.ClosedRangeAt 2 ∧
      ¬ BGG.complex.ClosedRangeAt 1 :=
  ⟨GradCurl.not_closedRangeAt_one, GradCurl.not_closedRangeAt_two, SymCurl.not_closedRangeAt_one,
    SymCurl.not_closedRangeAt_two, BGG.not_closedRangeAt_one⟩

/-- **No Poincaré inequality for the gradient on `ℝ³`**: there is no `C` with `‖u‖ ≤ C ‖∇u‖`
for `u ∈ H¹ ∩ (ker ∇)ᗮ`. [QuennevilleBelair2015], Thm 4.2 -/
theorem not_poincare_grad :
    ¬ ∃ C : ℝ, ∀ x : (GradCurl.complex.d 0 1).domain,
      (x : GradCurl.Space 0) ∈ (GradCurl.complex.cycles 0)ᗮ →
        ‖(x : GradCurl.Space 0)‖ ≤ C * ‖GradCurl.complex.d 0 1 x‖ := by
  rw [← GradCurl.complex.closedRangeAt_iff_poincare_of_rel
    (show ComplexShape.fin3.Rel 0 1 from rfl)]
  exact GradCurl.not_closedRangeAt_one

/-- **No Poincaré inequality for the curl on `ℝ³`**: there is no `C` with
`‖u‖ ≤ C ‖curl u‖` for `u ∈ H(curl) ∩ (ker curl)ᗮ`. [QuennevilleBelair2015], Thm 4.2 -/
theorem not_poincare_curl :
    ¬ ∃ C : ℝ, ∀ x : (GradCurl.complex.d 1 2).domain,
      (x : GradCurl.Space 1) ∈ (GradCurl.complex.cycles 1)ᗮ →
        ‖(x : GradCurl.Space 1)‖ ≤ C * ‖GradCurl.complex.d 1 2 x‖ := by
  rw [← GradCurl.complex.closedRangeAt_iff_poincare_of_rel
    (show ComplexShape.fin3.Rel 1 2 from rfl)]
  exact GradCurl.not_closedRangeAt_two

end Feec.Counterexamples
