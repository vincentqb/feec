module

public import Feec.Fourier.Torus
public import Feec.Fourier.SymCurlSymbol

/-!
# The strong-symmetry complex on `𝕋³`: TSD constraints propagate (Thesis Prop 4.19)

The complex (4.16) `H²(𝕋³) --grad grad--> H(curl; 𝕋³, S) --curl--> L²(𝕋³; T)` (`S` symmetric, `T`
trace-free matrices), on the Fourier side: the torus instance of the symbol theory with the fibre
complex `Feec.Fourier.SymCurl.symCurl`. Its adjoint complex is (4.17), `div div ← sym curl`, and
its Hodge wave equation is (4.18).

## Main results

* `SymCurl.complex`: the Hilbert complex, on the window `Fin 3`.
* `SymCurl.constraint = {0} × L²(TSD ∩ S) × L²(TSD ∩ T)` and **`reducingSubcomplex`**: the
  thesis' projection and density "conjectures" are not needed; the projection hypothesis holds.
* **`tsd_propagates`**, `tsd_propagates_neg`, **`tsd_existsUnique`**, `waveGroup_mem`: Prop 4.19 on
  `𝕋³`, with existence and uniqueness, forcing, any time interval.

## References

* [QuennevilleBelair2015], §4.11 (Prop 4.19, (4.16)–(4.18))
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set Feec.Fourier Feec.Fourier.GradCurl Feec.Fourier.SymCurl
  Feec.ShortHilbertComplex

namespace Feec.Models.Torus.SymCurl

/-- The spaces `ℓ²(ℤ³; ℂ)`, `ℓ²(ℤ³; S)`, `ℓ²(ℤ³; T)` of Fourier coefficients. -/
abbrev Space (i : Fin 3) : Type :=
  Lp (W3 ℂ Sym Tr i) 2 (Measure.count : Measure (Fin 3 → ℤ))

/-- **The periodic strong-symmetry complex** (4.16) (Fourier side). -/
abbrev complex : HilbertComplex ℂ ComplexShape.fin3 Space :=
  Fourier.Torus.complex symCurl

/-- **The constraint space** `K = {0} × L²(TSD ∩ S) × L²(TSD ∩ T)`. -/
abbrev constraint (i : Fin 3) : Submodule ℂ (Space i) :=
  Operator.fibreSub Measure.count fun k => SymCurl.tsdK i (Fourier.Torus.freq k)

/-- The fibrewise reducing family on the torus. -/
theorem fibreReducing :
    FibreReducing (Fourier.Torus.symbolComplex symCurl)
      fun i k => SymCurl.tsdK i (Fourier.Torus.freq k) :=
  Fourier.Torus.fibreReducing isFibreReducing

instance (i : Fin 3) : (constraint i).HasOrthogonalProjection :=
  fibreReducing.hasOrthogonalProjection i

/-- **`K` is a reducing subcomplex** (the projection hypothesis of Prop 4.19, proved).
Thesis: Prop 4.19 -/
theorem reducingSubcomplex : complex.ReducingSubcomplex constraint :=
  fibreReducing.toReducingSubcomplex

/-- **Thesis Prop 4.19 on `𝕋³`**: strong solutions of `U' = L U + F` with data and forcing in
`K` stay in `K`. Thesis: Prop 4.19 -/
theorem tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates hU h0 hF

/-- Prop 4.19 for the sign convention `U' = -L U + F` of Thesis (4.4). Thesis: Prop 4.19 -/
theorem tsd_propagates_neg {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution (-complex.wave) (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates_neg hU h0 hF

/-- **Prop 4.19 on `𝕋³` with existence**: for `U₀ ∈ D(L) ∩ K` and admissible forcing in `K`, the
Hodge wave equation has a classical solution, unique among strong solutions, staying in `K`.
Thesis: Prop 4.19 -/
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
Thesis: Prop 4.19 -/
theorem waveGroup_mem (t : ℝ) {x : PiLp 2 Space} (hx : x ∈ HilbertComplex.totalSub constraint) :
    complex.waveGroup.S t x ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.waveGroup_mem t hx

end Feec.Models.Torus.SymCurl
