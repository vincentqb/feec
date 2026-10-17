module

public import Feec.Fourier.Euclidean
public import Feec.Fourier.BGGSymbol

/-!
# The BGG weak-symmetry complex on `ℝ³`: TSD constraints propagate

The complex (5.1) of Thesis Ch. 6 on the whole space, on the Fourier side (Plancherel): the
whole-space instance of the symbol theory with `Feec.Fourier.BGG.bggFamily`. TSD data stay TSD,
`M` stays `0` and `B` stays TSD, with existence and uniqueness; on bounded domains with the
thesis' boundary conditions this fails, which locates the failure at the boundary.

## Main results

* `BGG.complex`, `BGG.constraint`, **`reducingSubcomplex`**.
* **`tsd_propagates`**, `tsd_propagates_neg`, **`tsd_existsUnique`**, `waveGroup_mem`.
* `not_closedRangeAt_one`: the whole-space Hessian does not have closed range.

## References

* [QuennevilleBelair2015], Ch. 5 (§5.1, (5.1)), Ch. 6 (§6.1, §6.3)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set Feec.Fourier Feec.Fourier.GradCurl Feec.Fourier.SymCurl
  Feec.Fourier.BGG Feec.ShortHilbertComplex

namespace Feec.Models.Euclidean.BGG

/-- The spaces `L²(ℝ³)`, `L²(ℝ³; ℂ³ˣ³)`, `L²(ℝ³; ℂ³ × ℂ³ˣ³)` of Fourier transforms. -/
abbrev Space (i : Fin 3) : Type :=
  Lp (W3 ℂ Mat VM i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))

/-- **The whole-space BGG weak-symmetry complex** (5.1) (Fourier side). -/
abbrev complex : HilbertComplex ℂ ComplexShape.fin3 Space :=
  Fourier.Euclidean.complex bggFamily

/-- **The constraint space** `K = {0} × L²(TSD) × ({0} × L²(TSD))`. -/
abbrev constraint (i : Fin 3) : Submodule ℂ (Space i) :=
  Operator.fibreSub volume fun x => bggK i (Fourier.Euclidean.scale x)

theorem fibreReducing : FibreReducing (Fourier.Euclidean.symbolComplex bggFamily)
    fun i x => bggK i (Fourier.Euclidean.scale x) :=
  BGG.isFibreReducing.toFibreReducing _ Fourier.Euclidean.scale _
    (aestronglyMeasurable_starProjection_bggK Fourier.Euclidean.measurable_scale)

instance (i : Fin 3) : (constraint i).HasOrthogonalProjection :=
  fibreReducing.hasOrthogonalProjection i

/-- **`K` is a reducing subcomplex** on `ℝ³`. Thesis: §6.3 -/
theorem reducingSubcomplex : complex.ReducingSubcomplex constraint :=
  fibreReducing.toReducingSubcomplex

/-- **TSD propagation for the BGG system on `ℝ³`**: strong solutions of `U' = L U + F` with data and forcing in `K`
stay in `K`. Thesis: §6.3 -/
theorem tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates hU h0 hF

/-- TSD propagation on `ℝ³` for `U' = -L U + F`. Thesis: §6.3 -/
theorem tsd_propagates_neg {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution (-complex.wave) (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates_neg hU h0 hF

/-- **TSD propagation on `ℝ³` with existence and uniqueness.** Thesis: §6.3 -/
theorem tsd_existsUnique {U₀ : PiLp 2 Space} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀K : U₀ ∈ HilbertComplex.totalSub constraint) {F : ℝ → PiLp 2 Space} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFK : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  fibreReducing.existsUnique_mem hU₀ hU₀K hF hFK

/-- The wave group preserves `K` for all times. Thesis: §6.3 -/
theorem waveGroup_mem (t : ℝ) {x : PiLp 2 Space} (hx : x ∈ HilbertComplex.totalSub constraint) :
    complex.waveGroup.S t x ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.waveGroup_mem t hx

/-! ### No closed range -/

theorem prev_one : ComplexShape.fin3.prev 1 = 0 := ComplexShape.fin3.prev_eq' rfl

theorem prev_two : ComplexShape.fin3.prev 2 = 1 := ComplexShape.fin3.prev_eq' rfl

/-- **The whole-space Hessian does not have closed range.** -/
theorem not_closedRangeAt_one : ¬ complex.ClosedRangeAt 1 := by
  have h1 : bggFamily.IsHomogeneous (ComplexShape.fin3.prev 1) 1 2 := by
    rw [prev_one]; exact bggFamily_isHomogeneous01
  have h2 : bggFamily.m (ComplexShape.fin3.prev 1) 1 ≠ 0 := by rw [prev_one]; exact hessM_ne_zero
  exact Fourier.Euclidean.not_closedRangeAt two_pos h1 h2

end Feec.Models.Euclidean.BGG
