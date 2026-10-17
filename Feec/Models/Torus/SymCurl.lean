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
* **`closedRangeAt`**, `dual_closedRangeAt'`, **`hodge`**: closed range at every index (Poincaré
  constant `1`) and the Hodge decomposition without closures.
* `realStructure`, **`real_tsd_propagates`**, `real_tsd_existsUnique`, `waveGroup_realConj`:
  real fields (`Â(-ξ) = conj Â(ξ)`) stay real, together with the constraint
  (`Feec.Fourier.SymbolComplex.RealStructure`).

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

/-! ### Closed range and the Hodge decomposition -/

/-- **The periodic strong-symmetry complex has closed range** at every index (the thesis defers
this to its next chapter). The incoming gap of `curl` uses `|A ξ| ≤ ‖curl_ξ A‖` for symmetric `A`
with `ξᵀ A ξ = 0` (`Feec.Fourier.SymCurl.norm_div_le_norm_curl`). -/
theorem closedRangeAt (i : Fin 3) : complex.ClosedRangeAt i :=
  Fourier.Torus.closedRangeAt_of_gap (symCurl_m_zero _ _) fun _ hξ => symCurl_gap _ _ hξ

theorem dual_closedRangeAt {i j : Fin 3} (hij : ComplexShape.fin3.Rel i j) :
    complex.dual.ClosedRangeAt i :=
  Fourier.Torus.dual_closedRangeAt_of_gap hij (symCurl_m_zero _ _) fun _ hξ => symCurl_gap _ _ hξ

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

/-- **Hodge decomposition without closures** at every index (e.g. `L²(𝕋³; S)` is
`R(grad grad) ⊕ ℌ ⊕ R(sym curl)`), pairwise orthogonal. -/
theorem hodge (i : Fin 3) :
    complex.boundaries i ⊔ complex.harmonic i ⊔ complex.dual.boundaries i = ⊤ ∧
      complex.boundaries i ⟂ complex.harmonic i ∧
      complex.harmonic i ⟂ complex.dual.boundaries i ∧
      complex.boundaries i ⟂ complex.dual.boundaries i :=
  complex.hodge_of_closedRangeAt (closedRangeAt i) (dual_closedRangeAt' i)

/-! ### Real fields -/

/-- **The real structure**: real fields are those with `Â(-ξ) = conj Â(ξ)`. -/
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

/-- **Thesis Prop 4.19 for real fields**: real TSD data and forcing give a strong solution that
stays real and TSD. Thesis: Prop 4.19 -/
theorem real_tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint) (h0r : realConj (U a) = U a)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint)
    (hFr : ∀ t ∈ Icc a b, realConj (F t) = F t) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint ∧ realConj (U t) = U t :=
  fun t ht => ⟨tsd_propagates hU h0 hF t ht, realStructure.conj_eq hU h0r hFr t ht⟩

/-- **Prop 4.19 for real fields, with existence and uniqueness.** Thesis: Prop 4.19 -/
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

end Feec.Models.Torus.SymCurl
