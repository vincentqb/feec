module

public import Feec.Fourier.Torus
public import Feec.Fourier.SymCurlSymbol
public import Feec.Fourier.Reality

/-!
# The strong-symmetry complex on `𝕋³`: TSD constraints propagate

The complex (4.16) `H²(𝕋³) --grad grad--> H(curl; 𝕋³, S) --curl--> L²(𝕋³; T)` on the Fourier side:
it has closed range, and `K = {0} × L²(TSD ∩ S) × L²(TSD ∩ T)` is a reducing subcomplex, so TSD
data and forcing give TSD solutions.

## Main results

* `tsd_existsUnique`: TSD propagation, with existence and uniqueness.
* `closedRangeAt`, `hodge`, `hodge_real`: closed range and the Hodge decomposition without closures.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set Feec.Fourier Feec.Fourier.GradCurl Feec.Fourier.SymCurl
  Feec.ShortHilbertComplex

namespace Feec.Models.Torus.SymCurl

/-- The spaces `ℓ²(ℤ³; ℂ)`, `ℓ²(ℤ³; S)`, `ℓ²(ℤ³; T)` of Fourier coefficients. -/
abbrev Space (i : Fin 3) : Type :=
  Lp (W3 ℂ Sym Tr i) 2 (Measure.count : Measure (Fin 3 → ℤ))

/-- The periodic strong-symmetry complex (4.16), on the Fourier side. -/
abbrev complex : HilbertComplex ℂ ComplexShape.fin3 Space :=
  Fourier.Torus.complex symCurl

/-- The constraint space `K = {0} × L²(TSD ∩ S) × L²(TSD ∩ T)`. -/
abbrev constraint (i : Fin 3) : Submodule ℂ (Space i) :=
  Operator.fibreSub Measure.count fun k => SymCurl.tsdK i (Fourier.Torus.freq k)

theorem fibreReducing :
    FibreReducing (Fourier.Torus.symbolComplex symCurl)
      fun i k => SymCurl.tsdK i (Fourier.Torus.freq k) :=
  Fourier.Torus.fibreReducing isFibreReducing

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

/-- Data in `K ∩ D(L)` and admissible forcing in `K` give a classical solution, unique among strong
solutions, that stays in `K`. [QuennevilleBelair2015], Prop 4.19 (adapted) -/
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

/-- The periodic strong-symmetry complex has closed range at every index. -/
theorem closedRangeAt (i : Fin 3) : complex.ClosedRangeAt i :=
  Fourier.Torus.closedRangeAt_of_gap (symCurl_m_zero _ _) fun _ hξ => symCurl_gap _ _ hξ

theorem adjoint_d (i j : Fin 3) :
    (complex.d i j)† = Operator.mulOp Measure.count fun k =>
      ContinuousLinearMap.adjoint (symCurl.m i j (Fourier.Torus.freq k)) :=
  (Fourier.Torus.symbolComplex symCurl).adjoint_d i j

theorem dual_closedRangeAt {i j : Fin 3} (hij : ComplexShape.fin3.Rel i j) :
    complex.dual.ClosedRangeAt i :=
  Fourier.Torus.dual_closedRangeAt_of_gap hij (symCurl_m_zero _ _) fun _ hξ => symCurl_gap _ _ hξ

theorem dual_closedRangeAt' (i : Fin 3) : complex.dual.ClosedRangeAt i := by
  fin_cases i
  · exact dual_closedRangeAt (j := 1) rfl
  · exact dual_closedRangeAt (j := 2) rfl
  · exact complex.dual_closedRangeAt_of_forall_not_rel fun k h => by
      have : (2 : Fin 3).val + 1 = k.val := h
      have := k.isLt; omega

/-- The Hodge decomposition without closures at every index, pairwise orthogonal. -/
theorem hodge (i : Fin 3) :
    complex.boundaries i ⊔ complex.harmonic i ⊔ complex.dual.boundaries i = ⊤ ∧
      complex.boundaries i ⟂ complex.harmonic i ∧
      complex.harmonic i ⟂ complex.dual.boundaries i ∧
      complex.boundaries i ⟂ complex.dual.boundaries i :=
  complex.hodge_of_closedRangeAt (closedRangeAt i) (dual_closedRangeAt' i)

/-- The real structure: real fields are those with `Â(-ξ) = conj Â(ξ)`. -/
def realStructure : (Fourier.Torus.symbolComplex symCurl).RealStructure Reflection.count_neg where
  cj := SymCurl.cjW3
  antilinear := SymCurl.cjW3_smul
  invol := SymCurl.cjW3_cjW3
  inner_cj := SymCurl.inner_cjW3
  symm i j k v := by
    change symCurl.m i j (Fourier.Torus.freq (-k)) (SymCurl.cjW3 i v) = _
    rw [Fourier.Torus.freq_neg]; exact symCurl_neg_cj i j _ v

/-- The conjugation `C u = conj (u ∘ (-·))` of the state space. -/
abbrev realConj : PiLp 2 Space →L[ℝ] PiLp 2 Space := realStructure.toConj.totalConj

theorem real_tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint) (h0r : realConj (U a) = U a)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint)
    (hFr : ∀ t ∈ Icc a b, realConj (F t) = F t) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint ∧ realConj (U t) = U t :=
  realStructure.toConj.propagates_real reducingSubcomplex hU h0 h0r hF hFr

theorem real_tsd_existsUnique {U₀ : PiLp 2 Space} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀K : U₀ ∈ HilbertComplex.totalSub constraint) (hU₀r : realConj U₀ = U₀)
    {F : ℝ → PiLp 2 Space} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFK : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint)
    (hFr : ∀ t ∈ Icc a b, realConj (F t) = F t) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint ∧ realConj (U t) = U t) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  realStructure.toConj.existsUnique_mem_real reducingSubcomplex hU₀ hU₀K hU₀r hF hFK hFr

/-- A real field is `b + h + a` with `b ∈ R(d)`, `h` harmonic and `a ∈ R(d†)`, all three real. -/
theorem hodge_real {i : Fin 3} {x : Space i} (hx : realStructure.toConj.C i x = x) :
    ∃ b ∈ complex.boundaries i, ∃ h ∈ complex.harmonic i, ∃ a ∈ complex.dual.boundaries i,
      x = b + h + a ∧ realStructure.toConj.C i b = b ∧ realStructure.toConj.C i h = h ∧
        realStructure.toConj.C i a = a :=
  realStructure.toConj.hodge_real_of_closedRangeAt (closedRangeAt i) (dual_closedRangeAt' i) hx

end Feec.Models.Torus.SymCurl
