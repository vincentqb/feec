module

public import Feec.Fourier.Euclidean
public import Feec.Fourier.BGGSymbol

/-!
# The BGG weak-symmetry complex on `ℝ³`: TSD constraints propagate

The complex (5.1) of the weakly symmetric formulation of [QuennevilleBelair2015], Ch. 6 on `ℝ³`,
on the Fourier side: the constraint space `K = {0} × L²(TSD) × ({0} × L²(TSD))` is a reducing
subcomplex, so TSD data stay TSD.

## Main results

* `tsd_existsUnique`: TSD propagation, with existence and uniqueness.
* `not_closedRangeAt_one`: the Hessian does not have closed range.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set Feec.Fourier Feec.Fourier.GradCurl Feec.Fourier.SymCurl
  Feec.Fourier.BGG Feec.ShortHilbertComplex

namespace Feec.Models.Euclidean.BGG

/-- The spaces `L²(ℝ³)`, `L²(ℝ³; ℂ³ˣ³)`, `L²(ℝ³; ℂ³ × ℂ³ˣ³)` of Fourier transforms. -/
abbrev Space (i : Fin 3) : Type :=
  Lp (W3 ℂ Mat VM i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))

/-- The BGG weak-symmetry complex (5.1) on `ℝ³`, on the Fourier side. -/
abbrev complex : HilbertComplex ℂ ComplexShape.fin3 Space :=
  Fourier.Euclidean.complex bggFamily

/-- The constraint space `K = {0} × L²(TSD) × ({0} × L²(TSD))`. -/
abbrev constraint (i : Fin 3) : Submodule ℂ (Space i) :=
  Operator.fibreSub volume fun x => bggK i (Fourier.Euclidean.scale x)

theorem fibreReducing : FibreReducing (Fourier.Euclidean.symbolComplex bggFamily)
    fun i x => bggK i (Fourier.Euclidean.scale x) :=
  BGG.isFibreReducing.toFibreReducing _ Fourier.Euclidean.scale _
    (aestronglyMeasurable_starProjection_bggK Fourier.Euclidean.measurable_scale)

instance (i : Fin 3) : (constraint i).HasOrthogonalProjection :=
  fibreReducing.hasOrthogonalProjection i

theorem reducingSubcomplex : complex.ReducingSubcomplex constraint :=
  fibreReducing.toReducingSubcomplex

theorem tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates hU h0 hF

theorem tsd_propagates_neg {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution (-complex.wave) (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates_neg hU h0 hF

/-- Data in `K ∩ D(L)` and admissible forcing in `K` give a classical solution, unique among
strong solutions, that stays in `K`. [QuennevilleBelair2015], §6.3 -/
theorem tsd_existsUnique {U₀ : PiLp 2 Space} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀K : U₀ ∈ HilbertComplex.totalSub constraint) {F : ℝ → PiLp 2 Space} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFK : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  fibreReducing.existsUnique_mem hU₀ hU₀K hF hFK

theorem waveGroup_mem (t : ℝ) {x : PiLp 2 Space} (hx : x ∈ HilbertComplex.totalSub constraint) :
    complex.waveGroup.S t x ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.waveGroup_mem t hx

theorem prev_one : ComplexShape.fin3.prev 1 = 0 := ComplexShape.fin3.prev_eq' rfl

/-- The whole-space Hessian does not have closed range. -/
theorem not_closedRangeAt_one : ¬ complex.ClosedRangeAt 1 := by
  have h1 : bggFamily.IsHomogeneous (ComplexShape.fin3.prev 1) 1 2 := by
    rw [prev_one]; exact bggFamily_isHomogeneous01
  have h2 : bggFamily.m (ComplexShape.fin3.prev 1) 1 ≠ 0 := by rw [prev_one]; exact hessM_ne_zero
  exact Fourier.Euclidean.not_closedRangeAt two_pos h1 h2

end Feec.Models.Euclidean.BGG
