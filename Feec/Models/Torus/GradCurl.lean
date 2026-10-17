module

public import Feec.Fourier.Torus
public import Feec.Fourier.GradCurlSymbol

/-!
# The matrix grad–curl complex on `𝕋³`: TSD constraints propagate (Thesis Prop 4.17)

The complex `H¹(𝕋³; ℂ³) --grad--> H(curl; 𝕋³, ℂ³ˣ³) --curl--> L²(𝕋³; ℂ³ˣ³)` with the row-wise curl,
on the Fourier side (`Feec.Fourier.Torus.fieldFourier` identifies it with fields on `𝕋³`), is the
torus instance of the symbol theory with the fibre complex `Feec.Fourier.GradCurl.gradCurl`. Its
Hodge wave equation is the matrix system (4.14) of the Einstein–Bianchi formulation.

## Main results

* `GradCurl.complex`: the Hilbert complex, on the window `Fin 3`.
* `GradCurl.constraint`: `{0} × L²(TSD) × L²(TSD)` (symmetric, trace-free, divergence-free
  fields, fibrewise `Feec.Fourier.GradCurl.tsd`), and **`reducingSubcomplex`**: it is a reducing
  subcomplex. This is the thesis' "projection conjecture" `P_K D(L) ⊆ D(L)`, proved, together
  with `d P_K = P_K d`.
* **`tsd_propagates`**, `tsd_propagates_neg`: every strong solution of the Hodge wave equation
  with data and forcing in `K` stays in `K` (Prop 4.17, any time interval, with forcing);
  **`tsd_existsUnique`**: existence and uniqueness of the classical solution, which stays in `K`;
  `waveGroup_mem`: the wave group preserves `K` for all times.
* `closedRangeAt`, `dual_closedRangeAt`: closed range at every index, with the Poincaré constant
  `(2π)⁻¹` (`norm_le_of_mem_orthogonal`).
* `starProjection_eq_zero_of_mem_orthogonal`: fields whose Fourier coefficients are orthogonal
  to the TSD fibres (e.g. `A = c ξᵀ`, gradients) have zero TSD part, though `dev sym A ≠ 0` (the
  answer to the blueprint review's claimed counterexample: `P_TSD` is not pointwise).

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17, (4.14), (4.15))
* [ACBY1997] (the Einstein–Bianchi system)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set Feec.Fourier Feec.Fourier.GradCurl Feec.ShortHilbertComplex

namespace Feec.Models.Torus.GradCurl

/-- The spaces `ℓ²(ℤ³; ℂ³)`, `ℓ²(ℤ³; ℂ³ˣ³)`, `ℓ²(ℤ³; ℂ³ˣ³)` of Fourier coefficients. -/
abbrev Space (i : Fin 3) : Type :=
  Lp (W3 Vec Mat Mat i) 2 (Measure.count : Measure (Fin 3 → ℤ))

/-- **The periodic grad–curl matrix complex** (Fourier side). -/
abbrev complex : HilbertComplex ℂ ComplexShape.fin3 Space :=
  Fourier.Torus.complex gradCurl

/-- **The constraint space** `K = {0} × L²(TSD) × L²(TSD)`. -/
abbrev constraint (i : Fin 3) : Submodule ℂ (Space i) :=
  Operator.fibreSub Measure.count fun k => tsdK i (Fourier.Torus.freq k)

/-- The fibrewise reducing family on the torus. -/
theorem fibreReducing :
    FibreReducing (Fourier.Torus.symbolComplex gradCurl) fun i k => tsdK i (Fourier.Torus.freq k) :=
  Fourier.Torus.fibreReducing isFibreReducing

instance (i : Fin 3) : (constraint i).HasOrthogonalProjection :=
  fibreReducing.hasOrthogonalProjection i

/-- **`K` is a reducing subcomplex** (the projection hypothesis of Prop 4.17, proved).
Thesis: Prop 4.17 -/
theorem reducingSubcomplex : complex.ReducingSubcomplex constraint :=
  fibreReducing.toReducingSubcomplex

/-- **Thesis Prop 4.17 on `𝕋³`**: strong solutions of `U' = L U + F` with data and forcing in
`K = {0} × L²(TSD) × L²(TSD)` stay in `K`. Thesis: Prop 4.17 -/
theorem tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates hU h0 hF

/-- Prop 4.17 for the sign convention `U' = -L U + F` of Thesis (4.4). Thesis: Prop 4.17 -/
theorem tsd_propagates_neg {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution (-complex.wave) (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates_neg hU h0 hF

/-- **Prop 4.17 on `𝕋³` with existence**: for `U₀ ∈ D(L) ∩ K` and admissible forcing in `K`, the
Hodge wave equation has a classical solution, unique among strong solutions, staying in `K`.
Thesis: Prop 4.17 -/
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
Thesis: Prop 4.17 -/
theorem waveGroup_mem (t : ℝ) {x : PiLp 2 Space} (hx : x ∈ HilbertComplex.totalSub constraint) :
    complex.waveGroup.S t x ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.waveGroup_mem t hx

/-! ### Closed range -/

theorem gap (i j : Fin 3) {ξ : EuclideanSpace ℝ (Fin 3)} (hξ : 2 * Real.pi ≤ ‖ξ‖) :
    ∀ v ∈ (LinearMap.ker (gradCurl.m i j ξ : W3 Vec Mat Mat i →ₗ[ℂ] W3 Vec Mat Mat j))ᗮ,
      ‖v‖ ≤ (2 * Real.pi)⁻¹ * ‖gradCurl.m i j ξ v‖ := fun v hv =>
  le_inv_mul_of_mul_le (by positivity) hξ (norm_nonneg v) (gradCurl_gap i j ξ v hv)

/-- **The periodic grad–curl complex has closed range** at every index. -/
theorem closedRangeAt (i : Fin 3) : complex.ClosedRangeAt i :=
  Fourier.Torus.closedRangeAt_of_gap (gradCurl_m_zero _ _) fun _ hξ => gap _ _ hξ

theorem dual_closedRangeAt {i j : Fin 3} (hij : ComplexShape.fin3.Rel i j) :
    complex.dual.ClosedRangeAt i :=
  Fourier.Torus.dual_closedRangeAt_of_gap hij (gradCurl_m_zero _ _) fun _ hξ => gap _ _ hξ

/-- **Poincaré inequality** with constant `(2π)⁻¹` for both differentials. -/
theorem norm_le_of_mem_orthogonal {i j : Fin 3} (u : (complex.d i j).domain)
    (hu : (u : Space i) ∈ (complex.d i j).kerᗮ) :
    ‖(u : Space i)‖ ≤ (2 * Real.pi)⁻¹ * ‖complex.d i j u‖ := by
  refine (Fourier.Torus.symbolComplex gradCurl).norm_le_of_gap
    (Filter.Eventually.of_forall fun k => ?_) u hu
  by_cases hk : k = 0
  · subst hk
    intro v hv
    simp only [Fourier.Torus.symbolComplex_m, Fourier.Torus.freq_zero, gradCurl_m_zero] at hv ⊢
    rw [eq_zero_of_mem_orthogonal_ker_zero hv, norm_zero]
    positivity
  · exact gap _ _ (Fourier.Torus.two_pi_le_norm_freq hk)

/-! ### The TSD projection is not pointwise -/

/-- Fields whose coefficients are orthogonal to the TSD fibres have zero TSD part (for instance
`Â(k) = c_k ξ_kᵀ`, `Feec.Fourier.GradCurl.grad_mem_orthogonal`), even when their pointwise
symmetric trace-free part does not vanish. -/
theorem starProjection_eq_zero_of_mem_orthogonal {i : Fin 3} {A : Space i}
    (hA : ∀ k, A k ∈ (tsdK i (Fourier.Torus.freq k))ᗮ) :
    (constraint i).starProjection A = 0 := by
  refine Lp.ext_count fun k => ?_
  have h := Operator.coeFn_starProjection_fibreSub (μ := Measure.count)
    (fun k => tsdK i (Fourier.Torus.freq k)) AEStronglyMeasurable.of_discrete A
  rw [Measure.ae_count_iff.1 h k, Measure.ae_count_iff.1 (Lp.coeFn_zero (W3 Vec Mat Mat i) 2
    Measure.count) k]
  exact (Submodule.starProjection_apply_eq_zero_iff _).2 (hA k)

end Feec.Models.Torus.GradCurl
