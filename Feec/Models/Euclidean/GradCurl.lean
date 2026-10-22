module

public import Feec.Fourier.Euclidean
public import Feec.Fourier.GradCurlSymbol
public import Feec.Fourier.Weak

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
* **`mem_domain_grad_iff_weak`**, **`mem_domain_curl_iff_weak`**: `H¹` and `H(curl)` of the
  Fourier model are the weak-derivative spaces tested against all Schwartz fields (formal
  adjoints `-div` and the row-wise `curl`).
* **`fourier_mem_constraint_iff`**: the constraint space `L²(TSD)` is the Fourier image of the
  physical TSD fields: symmetric and trace-free a.e., and weakly
  divergence-free (`mem_ker_adjoint_grad_iff_weak`: `⟪f, ∇φ⟫ = 0` for all Schwartz `φ`).
* `realStructure`, **`real_tsd_propagates`**, `real_tsd_existsUnique`: real fields (`Â(-ξ) = conj Â(ξ)`) stay real, together with the constraint
  (`Feec.Fourier.SymbolComplex.RealStructure`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17, (4.14))

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open scoped FourierTransform SchwartzMap
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

/-- **`K` is a reducing subcomplex** on `ℝ³`. [QuennevilleBelair2015], Prop 4.17 -/
theorem reducingSubcomplex : complex.ReducingSubcomplex constraint :=
  fibreReducing.toReducingSubcomplex

/-- **Thesis Prop 4.17 on `ℝ³`**: strong solutions of `U' = L U + F` with data and forcing in `K`
stay in `K`. [QuennevilleBelair2015], Prop 4.17 -/
theorem tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates hU h0 hF

/-- Prop 4.17 on `ℝ³` for `U' = -L U + F`. [QuennevilleBelair2015], Prop 4.17 -/
theorem tsd_propagates_neg {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution (-complex.wave) (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates_neg hU h0 hF

/-- **Prop 4.17 on `ℝ³` with existence and uniqueness.** [QuennevilleBelair2015], Prop 4.17 -/
theorem tsd_existsUnique {U₀ : PiLp 2 Space} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀K : U₀ ∈ HilbertComplex.totalSub constraint) {F : ℝ → PiLp 2 Space} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFK : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  fibreReducing.existsUnique_mem hU₀ hU₀K hF hFK

/-- The wave group preserves `K` for all times. [QuennevilleBelair2015], Prop 4.17 -/
theorem waveGroup_mem (t : ℝ) {x : PiLp 2 Space} (hx : x ∈ HilbertComplex.totalSub constraint) :
    complex.waveGroup.S t x ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.waveGroup_mem t hx

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
stays real and TSD. [QuennevilleBelair2015], Prop 4.17 -/
theorem real_tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint) (h0r : realConj (U a) = U a)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint)
    (hFr : ∀ t ∈ Icc a b, realConj (F t) = F t) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint ∧ realConj (U t) = U t :=
  fun t ht => ⟨tsd_propagates hU h0 hF t ht, realStructure.conj_eq hU h0r hFr t ht⟩

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
        EqOn V U (Icc a b) := by
  obtain ⟨U, hU0, hU, hUK, huniq⟩ := tsd_existsUnique hU₀ hU₀K hF hFK
  exact ⟨U, hU0, hU, fun t ht => ⟨hUK t ht,
    realStructure.conj_eq hU.toIsStrongSolution (hU0 ▸ hU₀r) hFr t ht⟩, huniq⟩

/-! ### Weak derivatives -/

theorem grad_isLinear : Weak.IsLinear (gradCurl.m 0 1) := grad_eq_sum

theorem curl_isLinear : Weak.IsLinear (gradCurl.m 1 2) := curl_eq_sum

/-- **The Fourier `H¹` is the weak `H¹`**: `𝓕 u ∈ D(grad)` with `grad 𝓕 u = 𝓕 G` iff
`⟪u, grad* A⟫ = ⟪G, A⟫` for every Schwartz matrix field `A`, with `grad* = -div` the formal
adjoint. -/
theorem mem_domain_grad_iff_weak
    (u : Lp (W3 Vec Mat Mat 0) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))))
    (G : Lp (W3 Vec Mat Mat 1) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    (∃ h : 𝓕 u ∈ (complex.d 0 1).domain, complex.d 0 1 ⟨𝓕 u, h⟩ = 𝓕 G) ↔
      ∀ A : 𝓢(EuclideanSpace ℝ (Fin 3), W3 Vec Mat Mat 1),
        ⟪u, (Weak.formalAdjointOp (gradCurl.m 0 1) A).toLp 2⟫_ℂ = ⟪G, A.toLp 2⟫_ℂ :=
  Weak.mem_graph_iff_weak_of_isLinear grad_isLinear (gradCurl.cont 0 1) u G

/-- **The Fourier `H(curl)` is the weak `H(curl)`**: `𝓕 A ∈ D(curl)` with `curl 𝓕 A = 𝓕 B` iff
`⟪A, curl* φ⟫ = ⟪B, φ⟫` for every Schwartz matrix field `φ` (the row-wise curl is formally
self-adjoint). -/
theorem mem_domain_curl_iff_weak
    (A : Lp (W3 Vec Mat Mat 1) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))))
    (B : Lp (W3 Vec Mat Mat 2) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    (∃ h : 𝓕 A ∈ (complex.d 1 2).domain, complex.d 1 2 ⟨𝓕 A, h⟩ = 𝓕 B) ↔
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin 3), W3 Vec Mat Mat 2),
        ⟪A, (Weak.formalAdjointOp (gradCurl.m 1 2) φ).toLp 2⟫_ℂ = ⟪B, φ.toLp 2⟫_ℂ :=
  Weak.mem_graph_iff_weak_of_isLinear curl_isLinear (gradCurl.cont 1 2) A B

/-! ### The TSD constraint in physical variables -/

theorem adjoint_grad_eq : (complex.d 0 1)† = Operator.mulOp volume fun x =>
    ContinuousLinearMap.adjoint (gradCurl.m 0 1 (Fourier.Euclidean.scale x)) :=
  (Fourier.Euclidean.symbolComplex gradCurl).adjoint_d 0 1

/-- The kernel of `grad† = div` on the Fourier side: `div_{2πx} u(x) = 0` a.e. -/
theorem mem_ker_adjoint_grad_iff_ae {u : Space 1} :
    u ∈ ((complex.d 0 1)†).ker ↔
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
        div (Fourier.Euclidean.scale x) (u x) = 0 := by
  rw [adjoint_grad_eq, Operator.mem_ker_mulOp]
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun x => by
    change ContinuousLinearMap.adjoint (grad _) _ = 0 ↔ _
    rw [adjoint_grad])

/-- **Weakly divergence-free fields**: `𝓕 f ∈ ker grad†` iff `⟪f, ∇φ⟫ = 0` for every Schwartz
vector field `φ`, with `∇φ = Weak.symbolOp grad φ` the classical gradient
(`(∇φ)_{ab} = ∂_b φ_a`). -/
theorem mem_ker_adjoint_grad_iff_weak
    (f : Lp (W3 Vec Mat Mat 1) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    𝓕 f ∈ ((complex.d 0 1)†).ker ↔
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin 3), W3 Vec Mat Mat 0),
        ⟪f, (Weak.symbolOp (gradCurl.m 0 1) φ).toLp 2⟫_ℂ = 0 := by
  rw [adjoint_grad_eq]
  refine Weak.mem_ker_iff_weak ?_ (Weak.symbolOp (gradCurl.m 0 1)) (fun φ x => ?_) f
  · exact (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := W3 Vec Mat Mat 0)
      (F := W3 Vec Mat Mat 1)).continuous.comp
        ((gradCurl.cont 0 1).comp Fourier.Euclidean.continuous_scale)
  · rw [ContinuousLinearMap.adjoint_adjoint, Weak.fourier_symbolOp grad_isLinear]

/-- **The constraint space of Prop 4.17 on `ℝ³` is the physical TSD space**: `𝓕 f ∈ L²(TSD)` iff
`f(x)` is symmetric and trace-free for a.e. `x` and `div f = 0` weakly (`⟪f, ∇φ⟫ = 0` for every
Schwartz vector field `φ`).
See [QuennevilleBelair2015], §3.4, §4.10 (the spaces of Prop 4.17). -/
theorem fourier_mem_constraint_iff
    (f : Lp (W3 Vec Mat Mat 1) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    𝓕 f ∈ constraint 1 ↔
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))), f x ∈ tsd 0) ∧
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin 3), W3 Vec Mat Mat 0),
          ⟪f, (Weak.symbolOp (gradCurl.m 0 1) φ).toLp 2⟫_ℂ = 0 := by
  have h1 : (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))), f x ∈ tsd 0) ↔
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))), (𝓕 f : Space 1) x ∈ tsd 0 := by
    simp only [tsd_eq_ker 0]
    exact Weak.ae_map_eq_zero_iff_fourier (tsdMap 0) f
  rw [h1, ← mem_ker_adjoint_grad_iff_weak, mem_ker_adjoint_grad_iff_ae, ← Filter.eventually_and,
    Operator.mem_fibreSub]
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun x => mem_tsd_iff_div)

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
