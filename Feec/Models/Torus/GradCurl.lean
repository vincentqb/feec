module

public import Feec.Fourier.Torus
public import Feec.Fourier.GradCurlSymbol
public import Feec.Fourier.TorusWeak

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
* **`mem_domain_grad_iff_weak`**, **`mem_domain_curl_iff_weak`**,
  **`mem_domain_adjoint_grad_iff_weak`**: `H¹(𝕋³; ℂ³)`, `H(curl; 𝕋³)` and `H(div; 𝕋³)` of the Fourier
  model are the weak-derivative spaces of `L²(𝕋³)` fields tested against all smooth functions
  (`Feec.Fourier.TorusWeak`).
* `realStructure`, **`real_tsd_propagates`**, `real_tsd_existsUnique`: real fields (`Â(-ξ) = conj Â(ξ)`) stay real, together with the constraint
  (`Feec.Fourier.SymbolComplex.RealStructure`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17, (4.14), (4.15))
* [A. Anderson, Y. Choquet-Bruhat, J. W. York, Jr., *Einstein–Bianchi hyperbolic system for general relativity*][ACBY1997]
  (the Einstein–Bianchi system)

Bibliography: [references.bib](../../../docs/references.bib)
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
[QuennevilleBelair2015], Prop 4.17 -/
theorem reducingSubcomplex : complex.ReducingSubcomplex constraint :=
  fibreReducing.toReducingSubcomplex

/-- **Thesis Prop 4.17 on `𝕋³`**: strong solutions of `U' = L U + F` with data and forcing in
`K = {0} × L²(TSD) × L²(TSD)` stay in `K`. [QuennevilleBelair2015], Prop 4.17 -/
theorem tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates hU h0 hF

/-- Prop 4.17 for the sign convention `U' = -L U + F` of Thesis (4.4). [QuennevilleBelair2015], Prop 4.17 -/
theorem tsd_propagates_neg {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution (-complex.wave) (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates_neg hU h0 hF

/-- **Prop 4.17 on `𝕋³` with existence**: for `U₀ ∈ D(L) ∩ K` and admissible forcing in `K`, the
Hodge wave equation has a classical solution, unique among strong solutions, staying in `K`.
[QuennevilleBelair2015], Prop 4.17 -/
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
[QuennevilleBelair2015], Prop 4.17 -/
theorem waveGroup_mem (t : ℝ) {x : PiLp 2 Space} (hx : x ∈ HilbertComplex.totalSub constraint) :
    complex.waveGroup.S t x ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.waveGroup_mem t hx

/-! ### Real fields -/

/-- **The real structure**: real fields are those with `Â(-ξ) = conj Â(ξ)`. -/
def realStructure : (Fourier.Torus.symbolComplex gradCurl).RealStructure Reflection.count_neg where
  cj := cjW3
  antilinear := cjW3_smul
  invol := cjW3_cjW3
  inner_cj := inner_cjW3
  symm i j k v := by
    change gradCurl.m i j (Fourier.Torus.freq (-k)) (cjW3 i v) = _
    rw [Fourier.Torus.freq_neg]; exact gradCurl_neg_cj i j _ v

/-- The conjugation `C u = conj (u ∘ (-·))` of the state space. -/
abbrev realConj : PiLp 2 Space →L[ℝ] PiLp 2 Space := realStructure.toConj.totalConj

/-- **Thesis Prop 4.17 for real fields**: real TSD data and forcing give a strong solution that
stays real and TSD. [QuennevilleBelair2015], Prop 4.17 -/
theorem real_tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint) (h0r : realConj (U a) = U a)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint)
    (hFr : ∀ t ∈ Icc a b, realConj (F t) = F t) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint ∧ realConj (U t) = U t :=
  realStructure.toConj.propagates_real reducingSubcomplex hU h0 h0r hF hFr

/-- **Prop 4.17 for real fields, with existence and uniqueness.** [QuennevilleBelair2015], Prop 4.17 -/
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

/-! ### Weak derivatives on `𝕋³` -/

theorem grad_isLinear : Weak.IsLinear (gradCurl.m 0 1) := grad_eq_sum

theorem curl_isLinear : Weak.IsLinear (gradCurl.m 1 2) := curl_eq_sum

/-- The divergence symbol `grad_ξ* = div_ξ` is linear in the frequency. -/
theorem adjoint_grad_isLinear :
    Weak.IsLinear fun ξ => ContinuousLinearMap.adjoint (gradCurl.m 0 1 ξ) := fun ξ => by
  change ContinuousLinearMap.adjoint (grad ξ) = ∑ k, _ • ContinuousLinearMap.adjoint (grad _)
  rw [grad_eq_sum ξ, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal]

/-- **`H¹(𝕋³; ℂ³)` is the weak `H¹`**: the Fourier coefficients of `u` lie in `D(grad)` with
`grad û = Ĝ` iff `G = ∇u` weakly (`G_{ab} = ∂_b u_a`, tested against all smooth functions on
`𝕋³`). -/
theorem mem_domain_grad_iff_weak (u : TorusWeak.Field (Fin 3) (Fin 3))
    (G : TorusWeak.Field (Fin 3) (Fin 3 × Fin 3)) :
    (∃ h : Fourier.Torus.fieldFourier _ _ u ∈ (complex.d 0 1).domain,
        complex.d 0 1 ⟨_, h⟩ = Fourier.Torus.fieldFourier _ _ G) ↔
      TorusWeak.IsWeak (P := Fin 3) (Q := Fin 3 × Fin 3) (gradCurl.m 0 1) u G :=
  TorusWeak.mem_graph_iff_isWeak (P := Fin 3) (Q := Fin 3 × Fin 3) grad_isLinear u G

/-- **`H(curl; 𝕋³)` is the weak `H(curl)`**: the row-wise curl of the Fourier model is the weak
row-wise curl `(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}`. -/
theorem mem_domain_curl_iff_weak (A C : TorusWeak.Field (Fin 3) (Fin 3 × Fin 3)) :
    (∃ h : Fourier.Torus.fieldFourier _ _ A ∈ (complex.d 1 2).domain,
        complex.d 1 2 ⟨_, h⟩ = Fourier.Torus.fieldFourier _ _ C) ↔
      TorusWeak.IsWeak (P := Fin 3 × Fin 3) (Q := Fin 3 × Fin 3) (gradCurl.m 1 2) A C :=
  TorusWeak.mem_graph_iff_isWeak (P := Fin 3 × Fin 3) (Q := Fin 3 × Fin 3) curl_isLinear A C

/-- **`H(div; 𝕋³) = D(grad†)` is the weak `H(div)`**: `grad† = div` (the symbol `div_ξ`) is the
weak row-wise divergence. -/
theorem mem_domain_adjoint_grad_iff_weak (A : TorusWeak.Field (Fin 3) (Fin 3 × Fin 3))
    (D : TorusWeak.Field (Fin 3) (Fin 3)) :
    (∃ h : Fourier.Torus.fieldFourier _ _ A ∈ ((complex.d 0 1)†).domain,
        (complex.d 0 1)† ⟨_, h⟩ = Fourier.Torus.fieldFourier _ _ D) ↔
      TorusWeak.IsWeak (P := Fin 3 × Fin 3) (Q := Fin 3)
        (fun ξ => ContinuousLinearMap.adjoint (gradCurl.m 0 1 ξ)) A D := by
  have e := (Fourier.Torus.symbolComplex gradCurl).adjoint_d 0 1
  change (∃ h : _ ∈ ((Fourier.Torus.symbolComplex gradCurl).toHilbertComplex.d 0 1)†.domain,
    ((Fourier.Torus.symbolComplex gradCurl).toHilbertComplex.d 0 1)† ⟨_, h⟩ = _) ↔ _
  rw [e]
  exact TorusWeak.mem_graph_iff_isWeak (P := Fin 3 × Fin 3) (Q := Fin 3) adjoint_grad_isLinear A D

end Feec.Models.Torus.GradCurl
