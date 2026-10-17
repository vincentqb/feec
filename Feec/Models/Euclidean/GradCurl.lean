module

public import Feec.Fourier.Euclidean
public import Feec.Fourier.GradCurlSymbol

/-!
# The matrix grad–curl complex on `ℝ³`: TSD constraints propagate (Thesis Prop 4.17)

The complex `H¹(ℝ³; ℂ³) --grad--> H(curl; ℝ³, ℂ³ˣ³) --curl--> L²(ℝ³; ℂ³ˣ³)` with the row-wise curl,
on the Fourier side (Plancherel, `Feec.Fourier.Euclidean.fourier`): the whole-space instance of the
symbol theory with the fibre complex `Feec.Fourier.GradCurl.gradCurl`, the physical setting of an
isolated source.

## Main results

* `GradCurl.complex`, `GradCurl.constraint = {0} × L²(TSD) × L²(TSD)` and
  **`reducingSubcomplex`** (the fibre projection `ξ ↦ P_ξ` is discontinuous at `0` but measurable,
  `Feec.Fourier.GradCurl.measurable_starProjection_tsd`).
* **`tsd_propagates`**, `tsd_propagates_neg`, **`tsd_existsUnique`**, `waveGroup_mem`: Prop 4.17
  on `ℝ³`, with existence and uniqueness, forcing, any time interval.
* `not_closedRangeAt_one`, `not_closedRangeAt_two`: neither differential has closed range (no
  Poincaré inequality at low frequencies), which Prop 4.17 does not need.
* `starProjection_mem_H1`: the TSD projection maps `H(curl)` into `H¹`, with
  `‖|ξ| P_TSD A‖ ≤ ‖curl A‖`.
* `realStructure`, **`real_tsd_propagates`**, `real_tsd_existsUnique`, `waveGroup_realConj`:
  real fields (`Â(-ξ) = conj Â(ξ)`) stay real, together with the constraint
  (`Feec.Fourier.SymbolComplex.RealStructure`).

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17, (4.14))
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set Feec.Fourier Feec.Fourier.GradCurl Feec.ShortHilbertComplex

namespace Feec.Models.Euclidean.GradCurl

/-- The spaces `L²(ℝ³; ℂ³)`, `L²(ℝ³; ℂ³ˣ³)`, `L²(ℝ³; ℂ³ˣ³)` of Fourier transforms. -/
abbrev Space (i : Fin 3) : Type :=
  Lp (W3 Vec Mat Mat i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))

/-- **The whole-space grad–curl matrix complex** (Fourier side). -/
abbrev complex : HilbertComplex ℂ ComplexShape.fin3 Space :=
  Fourier.Euclidean.complex gradCurl

/-- **The constraint space** `K = {0} × L²(TSD) × L²(TSD)`. -/
abbrev constraint (i : Fin 3) : Submodule ℂ (Space i) :=
  Operator.fibreSub volume fun x => tsdK i (Fourier.Euclidean.scale x)

theorem fibreReducing : FibreReducing (Fourier.Euclidean.symbolComplex gradCurl)
    fun i x => tsdK i (Fourier.Euclidean.scale x) :=
  Fourier.Euclidean.fibreReducing isFibreReducing measurable_starProjection_tsdK

instance (i : Fin 3) : (constraint i).HasOrthogonalProjection :=
  fibreReducing.hasOrthogonalProjection i

/-- **`K` is a reducing subcomplex** on `ℝ³`. Thesis: Prop 4.17 -/
theorem reducingSubcomplex : complex.ReducingSubcomplex constraint :=
  fibreReducing.toReducingSubcomplex

/-- **Thesis Prop 4.17 on `ℝ³`**: strong solutions of `U' = L U + F` with data and forcing in `K`
stay in `K`. Thesis: Prop 4.17 -/
theorem tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates hU h0 hF

/-- Prop 4.17 on `ℝ³` for `U' = -L U + F`. Thesis: Prop 4.17 -/
theorem tsd_propagates_neg {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution (-complex.wave) (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates_neg hU h0 hF

/-- **Prop 4.17 on `ℝ³` with existence and uniqueness.** Thesis: Prop 4.17 -/
theorem tsd_existsUnique {U₀ : PiLp 2 Space} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀K : U₀ ∈ HilbertComplex.totalSub constraint) {F : ℝ → PiLp 2 Space} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFK : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  fibreReducing.existsUnique_mem hU₀ hU₀K hF hFK

/-- The wave group preserves `K` for all times. Thesis: Prop 4.17 -/
theorem waveGroup_mem (t : ℝ) {x : PiLp 2 Space} (hx : x ∈ HilbertComplex.totalSub constraint) :
    complex.waveGroup.S t x ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.waveGroup_mem t hx

/-! ### `H¹` regularity of the TSD projection -/

/-- **The TSD projection maps `H(curl)` into `H¹`**: `|ξ| P_TSD A ∈ L²` for `A ∈ H(curl)`, with
`‖|ξ| P_TSD A‖ ≤ ‖curl A‖` (fibrewise `Feec.Fourier.GradCurl.mul_norm_starProjection_le`). -/
theorem starProjection_mem_H1 (A : (complex.d 1 2).domain) :
    MemLp (fun k => ((‖Fourier.Euclidean.scale k‖ : ℝ) : ℂ) •
      ((constraint 1).starProjection (A : Space 1) : _ → Mat) k) 2 volume := by
  have hP := Operator.coeFn_starProjection_fibreSub (μ := volume)
    (fun k => tsdK 1 (Fourier.Euclidean.scale k)) (fibreReducing.meas 1) (A : Space 1)
  have hd := (Fourier.Euclidean.symbolComplex gradCurl).coeFn_d A
  refine MemLp.of_le (Lp.memLp (complex.d 1 2 A)) ((Complex.continuous_ofReal.comp
    (continuous_norm.comp Fourier.Euclidean.continuous_scale)).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable _)) ?_
  filter_upwards [hP, hd] with k h1 h2
  rw [h1, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact le_of_le_of_eq (mul_norm_starProjection_le _ _) (congrArg norm h2).symm

/-! ### Real fields -/

/-- **The real structure**: real fields are those with `Â(-ξ) = conj Â(ξ)`. -/
def realStructure : (Fourier.Euclidean.symbolComplex gradCurl).RealStructure (Reflection.neg volume) where
  cj := cjW3
  antilinear := cjW3_smul
  invol := cjW3_cjW3
  inner_cj := inner_cjW3
  symm i j x v := by
    change gradCurl.m i j (Fourier.Euclidean.scale (-x)) (cjW3 i v) = _
    rw [Fourier.Euclidean.scale_neg]; exact gradCurl_neg_cj i j _ v

/-- The conjugation `C u = conj (u ∘ (-·))` of the state space. -/
abbrev realConj : PiLp 2 Space →L[ℝ] PiLp 2 Space := realStructure.toConj.totalConj

/-- **Thesis Prop 4.17 for real fields**: real TSD data and forcing give a strong solution that
stays real and TSD. Thesis: Prop 4.17 -/
theorem real_tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint) (h0r : realConj (U a) = U a)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint)
    (hFr : ∀ t ∈ Icc a b, realConj (F t) = F t) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint ∧ realConj (U t) = U t :=
  fun t ht => ⟨tsd_propagates hU h0 hF t ht, realStructure.conj_eq hU h0r hFr t ht⟩

/-- **Prop 4.17 for real fields, with existence and uniqueness.** Thesis: Prop 4.17 -/
theorem real_tsd_existsUnique {U₀ : PiLp 2 Space} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀K : U₀ ∈ HilbertComplex.totalSub constraint) (hU₀r : realConj U₀ = U₀)
    {F : ℝ → PiLp 2 Space} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFK : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint)
    (hFr : ∀ t ∈ Icc a b, realConj (F t) = F t) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint ∧ realConj (U t) = U t) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V →
        EqOn V U (Icc a b) := by
  obtain ⟨U, hU0, hU, hUK, huniq⟩ := tsd_existsUnique hU₀ hU₀K hF hFK
  exact ⟨U, hU0, hU, fun t ht => ⟨hUK t ht,
    realStructure.conj_eq hU.toIsStrongSolution (hU0 ▸ hU₀r) hFr t ht⟩, huniq⟩

/-- The wave group maps real fields to real fields. -/
theorem waveGroup_realConj (t : ℝ) (x : PiLp 2 Space) :
    realConj (complex.waveGroup.S t x) = complex.waveGroup.S t (realConj x) :=
  realStructure.waveGroup_conj t x

/-! ### No closed range -/

theorem prev_one : ComplexShape.fin3.prev 1 = 0 := ComplexShape.fin3.prev_eq' rfl

theorem prev_two : ComplexShape.fin3.prev 2 = 1 := ComplexShape.fin3.prev_eq' rfl

/-- **The whole-space gradient does not have closed range.** -/
theorem not_closedRangeAt_one : ¬ complex.ClosedRangeAt 1 := by
  have h1 : gradCurl.IsHomogeneous (ComplexShape.fin3.prev 1) 1 1 := by
    rw [prev_one]; exact gradCurl_isHomogeneous01
  have h2 : gradCurl.m (ComplexShape.fin3.prev 1) 1 ≠ 0 := by rw [prev_one]; exact grad_ne_zero
  exact Fourier.Euclidean.not_closedRangeAt one_pos h1 h2

/-- **The whole-space row-wise curl does not have closed range.** -/
theorem not_closedRangeAt_two : ¬ complex.ClosedRangeAt 2 := by
  have h1 : gradCurl.IsHomogeneous (ComplexShape.fin3.prev 2) 2 1 := by
    rw [prev_two]; exact gradCurl_isHomogeneous12
  have h2 : gradCurl.m (ComplexShape.fin3.prev 2) 2 ≠ 0 := by rw [prev_two]; exact curl_ne_zero
  exact Fourier.Euclidean.not_closedRangeAt one_pos h1 h2

end Feec.Models.Euclidean.GradCurl
