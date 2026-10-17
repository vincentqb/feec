module

public import Feec.Fourier.Torus
public import Feec.Fourier.BGGSymbol

/-!
# The BGG weak-symmetry complex on `𝕋³`: TSD constraints propagate

The complex (5.1) of the weakly symmetric formulation of Thesis Ch. 6 (`S₀ = I`, `S₁ = 2 vskw`),
`H²(𝕋³) --grad grad--> H(curl; 𝕋³, ℂ³ˣ³) --(S₁, curl)--> L²(𝕋³; ℂ³) × L²(𝕋³; ℂ³ˣ³)`, on the Fourier
side: the torus instance of the symbol theory with `Feec.Fourier.BGG.bggFamily`. On every bounded
domain with the thesis' boundary conditions its Hodge wave equation does not propagate the TSD
constraint; on the torus it does.

## Main results

* `BGG.complex`, `BGG.constraint = {0} × L²(TSD) × ({0} × L²(TSD))` and **`reducingSubcomplex`**.
* **`tsd_propagates`**, `tsd_propagates_neg`, **`tsd_existsUnique`**, `waveGroup_mem`: TSD data
  stay TSD, the multiplier `M` stays `0`, and `B` stays TSD, with existence and uniqueness.
* **`closedRangeAt`**, `dual_closedRangeAt'`, **`hodge`**: closed range at every index (Poincaré
  constant `4`) and the Hodge decomposition without closures.

## References

* [QuennevilleBelair2015], Ch. 5 (§5.1, (5.1)), Ch. 6 (§6.1, §6.3), §3.4 (Lemma 3.5)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set Feec.Fourier Feec.Fourier.GradCurl Feec.Fourier.SymCurl
  Feec.Fourier.BGG Feec.ShortHilbertComplex

namespace Feec.Models.Torus.BGG

/-- The spaces `ℓ²(ℤ³; ℂ)`, `ℓ²(ℤ³; ℂ³ˣ³)`, `ℓ²(ℤ³; ℂ³ × ℂ³ˣ³)` of Fourier coefficients. -/
abbrev Space (i : Fin 3) : Type :=
  Lp (W3 ℂ Mat VM i) 2 (Measure.count : Measure (Fin 3 → ℤ))

/-- **The periodic BGG weak-symmetry complex** (5.1) (Fourier side). -/
abbrev complex : HilbertComplex ℂ ComplexShape.fin3 Space :=
  Fourier.Torus.complex bggFamily

/-- **The constraint space** `K = {0} × L²(TSD ∩ S) × L²(TSD ∩ T)`. -/
abbrev constraint (i : Fin 3) : Submodule ℂ (Space i) :=
  Operator.fibreSub Measure.count fun k => bggK i (Fourier.Torus.freq k)

/-- The fibrewise reducing family on the torus. -/
theorem fibreReducing :
    FibreReducing (Fourier.Torus.symbolComplex bggFamily)
      fun i k => bggK i (Fourier.Torus.freq k) :=
  Fourier.Torus.fibreReducing isFibreReducing

instance (i : Fin 3) : (constraint i).HasOrthogonalProjection :=
  fibreReducing.hasOrthogonalProjection i

/-- **`K` is a reducing subcomplex** (the projection hypothesis, proved).
Thesis: §6.3 -/
theorem reducingSubcomplex : complex.ReducingSubcomplex constraint :=
  fibreReducing.toReducingSubcomplex

/-- **TSD propagation for the BGG system on `𝕋³`**: strong solutions of `U' = L U + F` with data and forcing in
`K` stay in `K`. Thesis: §6.3 -/
theorem tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates hU h0 hF

/-- TSD propagation for the sign convention `U' = -L U + F` of Thesis (4.4). Thesis: §6.3 -/
theorem tsd_propagates_neg {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution (-complex.wave) (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates_neg hU h0 hF

/-- **TSD propagation on `𝕋³` with existence**: for `U₀ ∈ D(L) ∩ K` and admissible forcing in `K`, the
Hodge wave equation has a classical solution, unique among strong solutions, staying in `K`.
Thesis: §6.3 -/
theorem tsd_existsUnique {U₀ : PiLp 2 Space} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀K : U₀ ∈ HilbertComplex.totalSub constraint) {F : ℝ → PiLp 2 Space} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFK : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  fibreReducing.existsUnique_mem hU₀ hU₀K hF hFK

/-- The wave group of the periodic complex preserves `K` for all times (forward and backward).
Thesis: §6.3 -/
theorem waveGroup_mem (t : ℝ) {x : PiLp 2 Space} (hx : x ∈ HilbertComplex.totalSub constraint) :
    complex.waveGroup.S t x ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.waveGroup_mem t hx

/-! ### Closed range and the Hodge decomposition -/

theorem freq_cases (k : Fin 3 → ℤ) :
    Fourier.Torus.freq k = 0 ∨ 2 * Real.pi ≤ ‖Fourier.Torus.freq k‖ := by
  by_cases hk : k = 0
  · exact Or.inl (Fourier.Torus.freq_eq_zero_iff.2 hk)
  · exact Or.inr (Fourier.Torus.two_pi_le_norm_freq hk)

/-- **The periodic BGG complex has closed range** at every index (Poincaré constant `4`): at
`ξ = 0` the zeroth-order part `S₁` is still present, and controls the skew part
(`Feec.Fourier.BGG.bggFamily_gap`). Thesis: §6.3 -/
theorem closedRangeAt (i : Fin 3) : complex.ClosedRangeAt i :=
  (Fourier.Torus.symbolComplex bggFamily).closedRangeAt_of_gap (C := 4)
    (Filter.Eventually.of_forall fun k => bggFamily_gap _ _ (freq_cases k))

theorem dual_closedRangeAt {i j : Fin 3} (hij : ComplexShape.fin3.Rel i j) :
    complex.dual.ClosedRangeAt i :=
  (Fourier.Torus.symbolComplex bggFamily).dual_closedRangeAt_of_gap hij (C := 4)
    (Filter.Eventually.of_forall fun k => bggFamily_gap _ _ (freq_cases k))

theorem dual_closedRangeAt_two : complex.dual.ClosedRangeAt 2 := by
  have hn : ComplexShape.fin3.next 2 = 2 := ComplexShape.fin3.next_eq_self' 2 fun k h => by
    have : (2 : Fin 3).val + 1 = k.val := h
    have := k.isLt; omega
  have h0 : complex.d 2 (ComplexShape.fin3.next 2) = 0 := complex.shape _ _ (by
    rw [hn]; intro h; have : (2 : Fin 3).val + 1 = (2 : Fin 3).val := h; omega)
  rw [HilbertComplex.ClosedRangeAt, HilbertComplex.boundaries_dual, h0, LinearPMap.adjoint_zero]
  convert (isClosed_singleton (x := (0 : Space 2))) using 1
  ext y; constructor
  · rintro ⟨x, rfl⟩; rfl
  · rintro rfl; exact ⟨0, rfl⟩

theorem dual_closedRangeAt' (i : Fin 3) : complex.dual.ClosedRangeAt i := by
  fin_cases i
  · exact dual_closedRangeAt (j := 1) rfl
  · exact dual_closedRangeAt (j := 2) rfl
  · exact dual_closedRangeAt_two

/-- **Hodge decomposition without closures** for the periodic BGG complex at every index,
pairwise orthogonal. Thesis: §6.3 -/
theorem hodge (i : Fin 3) :
    complex.boundaries i ⊔ complex.harmonic i ⊔ complex.dual.boundaries i = ⊤ ∧
      complex.boundaries i ⟂ complex.harmonic i ∧
      complex.harmonic i ⟂ complex.dual.boundaries i ∧
      complex.boundaries i ⟂ complex.dual.boundaries i :=
  complex.hodge_of_closedRangeAt (closedRangeAt i) (dual_closedRangeAt' i)

end Feec.Models.Torus.BGG
