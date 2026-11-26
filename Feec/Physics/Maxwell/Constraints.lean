module

public import Feec.HilbertComplex.Reducing
public import Feec.Models.Torus.DeRham
public import Feec.Models.Euclidean.DeRham
public import Feec.Domain.Complexes
public import Feec.Domain.Operators

/-!
# Maxwell's equations: the Gauss laws propagate

The Gauss laws `σ = 0`, `d†E = 0`, `dB = 0` of Maxwell's equations, the Hodge wave equation of a
window of a Hilbert complex, propagate for every complex and degree, on `𝕋ᵈ`, on `ℝᵈ` and on
every open `Ω ⊆ ℝ³` with either conductor ([QuennevilleBelair2015], Prop 4.16).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.Maxwell

universe u

/-! ### Every complex, every degree -/

section Window

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α]
  [CharZero α] {V : α → Type u} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] (H : HilbertComplex 𝕜 (ComplexShape.up α) V) (a : α)

/-- The Maxwell window `V a → V (a+1) → V (a+2)` of a complex on `ComplexShape.up α`. -/
abbrev window := (H.window a 3).toShort

/-- The magnetic Gauss law `dB = 0`: the kernel of `d : V (a+2) → V (a+3)`. -/
abbrev closedSub : Submodule 𝕜 (V (a + ((2 : Fin 3) : α))) :=
  (H.d (a + ((2 : Fin 3) : α)) (a + ((2 : Fin 3) : α) + 1)).ker

instance : (closedSub H a).HasOrthogonalProjection :=
  hasOrthogonalProjection_ker _ (H.closed _ _)

theorem d_mem_closedSub (x : (window H a).d₁.domain) : (window H a).d₁ x ∈ closedSub H a :=
  LinearPMap.mem_ker_iff.2 ⟨⟨_, H.mapsTo _ _ (a + ((2 : Fin 3) : α) + 1) x⟩, rfl,
    H.d_comp_d _ _ _ x⟩

/-- The total space `V a × V (a+1) × V (a+2)` of the Maxwell window. -/
abbrev Space := PiLp 2 (ShortHilbertComplex.W3 (V (a + ((0 : Fin 3) : α)))
  (V (a + ((1 : Fin 3) : α))) (V (a + ((2 : Fin 3) : α))))

/-- The Gauss-law constraint family `{0} × N(d†) × N(d)` of the Maxwell window. -/
abbrev gauss := (window H a).divFreeSub (closedSub H a)

variable [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]

/-- The Gauss laws `σ = 0`, `d†E = 0`, `dB = 0` propagate for strong solutions of Maxwell's
equations in degree `a` of any Hilbert complex. [QuennevilleBelair2015], Prop 4.16 -/
theorem gauss_propagates {t₀ t₁ : ℝ} {F U : ℝ → Space a (V := V)}
    (hU : Evolution.IsStrongSolution (window H a).wave (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ HilbertComplex.totalSub (gauss H a))
    (hF : ∀ t ∈ Icc t₀ t₁, F t ∈ HilbertComplex.totalSub (gauss H a)) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ HilbertComplex.totalSub (gauss H a) :=
  (window H a).divFree_propagates (closedSub H a) (d_mem_closedSub H a) hU h0 hF

theorem waveGroup_mem (t : ℝ) {x : Space a (V := V)}
    (hx : x ∈ HilbertComplex.totalSub (gauss H a)) :
    (window H a).toHilbertComplex.waveGroup.S t x ∈ HilbertComplex.totalSub (gauss H a) :=
  ((window H a).reducingSubcomplex_divFreeSub (closedSub H a) (d_mem_closedSub H a)).waveGroup_mem
    t hx

/-- Data in the domain and admissible forcing satisfying the Gauss laws give a classical solution,
unique among strong ones, which satisfies them. [QuennevilleBelair2015], Prop 4.16, Thm 4.3 -/
theorem gauss_existsUnique {U₀ : Space a (V := V)} (hU₀ : U₀ ∈ (window H a).wave.domain)
    (hU₀S : U₀ ∈ HilbertComplex.totalSub (gauss H a)) {F : ℝ → Space a (V := V)} {t₀ t₁ : ℝ}
    (hF : Evolution.ForcingClass.admissible (window H a).wave t₀ t₁ F)
    (hFS : ∀ t ∈ Icc t₀ t₁, F t ∈ HilbertComplex.totalSub (gauss H a)) :
    ∃ U, U t₀ = U₀ ∧ Evolution.IsClassicalSolution (window H a).wave (Icc t₀ t₁) F U ∧
      (∀ t ∈ Icc t₀ t₁, U t ∈ HilbertComplex.totalSub (gauss H a)) ∧
      ∀ W, W t₀ = U₀ → Evolution.IsStrongSolution (window H a).wave (Icc t₀ t₁) F W →
        EqOn W U (Icc t₀ t₁) :=
  ((window H a).reducingSubcomplex_divFreeSub (closedSub H a)
    (d_mem_closedSub H a)).existsUnique_mem hU₀ hU₀S hF hFS

end Window

/-! ### Periodic and whole-space Maxwell equations, any dimension and degree -/

section Models

variable (d : Type) [Fintype d] [LinearOrder d] (a : ℤ)

/-- On the torus `𝕋ᵈ`, in every dimension and degree, the Gauss laws propagate.
[QuennevilleBelair2015], Prop 4.16 -/
theorem torus_gauss_propagates {t₀ t₁ : ℝ}
    {F U : ℝ → Space a (V := Models.Torus.DeRham.L2Form d)}
    (hU : Evolution.IsStrongSolution (window (Models.Torus.DeRham.complex d) a).wave
      (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ HilbertComplex.totalSub (gauss (Models.Torus.DeRham.complex d) a))
    (hF : ∀ t ∈ Icc t₀ t₁, F t ∈ HilbertComplex.totalSub (gauss (Models.Torus.DeRham.complex d) a)) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ HilbertComplex.totalSub (gauss (Models.Torus.DeRham.complex d) a) :=
  gauss_propagates _ a hU h0 hF

/-- On `ℝᵈ`, in every dimension and degree, the Gauss laws propagate.
[QuennevilleBelair2015], Prop 4.16 -/
theorem euclidean_gauss_propagates {t₀ t₁ : ℝ}
    {F U : ℝ → Space a (V := Models.Euclidean.DeRham.L2Form d)}
    (hU : Evolution.IsStrongSolution (window (Models.Euclidean.DeRham.complex d) a).wave
      (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ HilbertComplex.totalSub (gauss (Models.Euclidean.DeRham.complex d) a))
    (hF : ∀ t ∈ Icc t₀ t₁,
      F t ∈ HilbertComplex.totalSub (gauss (Models.Euclidean.DeRham.complex d) a)) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ HilbertComplex.totalSub (gauss (Models.Euclidean.DeRham.complex d) a) :=
  gauss_propagates _ a hU h0 hF

end Models

/-! ### Perfect electric and magnetic conductors on a domain -/

section Conductor

open Feec.Domain

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω)

variable (𝕜) in
/-- Perfect electric conductor: the minimal complex `H̊¹(Ω) → H̊(curl, Ω) → L²(Ω)`, `Ω ⊆ ℝ³`. -/
def pec : ShortHilbertComplex 𝕜 (L2F 𝕜 Ω (Fin 1)) (L2F 𝕜 Ω (Fin 1 × Fin 3))
    (L2F 𝕜 Ω (Fin 1 × Fin 3)) :=
  ConstCoeffOp.shortMinimal (gradOp 3 1) (curlOp 1) hΩ isComplexPair_grad_curl

variable (𝕜) in
/-- Perfect magnetic conductor: the maximal complex `H¹(Ω) → H(curl, Ω) → L²(Ω)`. -/
def pmc : ShortHilbertComplex 𝕜 (L2F 𝕜 Ω (Fin 1)) (L2F 𝕜 Ω (Fin 1 × Fin 3))
    (L2F 𝕜 Ω (Fin 1 × Fin 3)) :=
  ConstCoeffOp.shortMaximal (gradOp 3 1) (curlOp 1) hΩ isComplexPair_grad_curl

variable (𝕜 Ω) in
/-- The magnetic Gauss law for a perfect electric conductor: `div B = 0` with `B · n = 0`. -/
abbrev magneticPEC : Submodule 𝕜 (L2F 𝕜 Ω (Fin 1 × Fin 3)) :=
  ((divOp 3 1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).minimal Ω).ker

variable (𝕜 Ω) in
/-- The magnetic Gauss law for a perfect magnetic conductor: `div B = 0`. -/
abbrev magneticPMC : Submodule 𝕜 (L2F 𝕜 Ω (Fin 1 × Fin 3)) :=
  ((divOp 3 1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).maximal Ω).ker

instance [h : Fact (IsOpen Ω)] : (magneticPEC 𝕜 Ω).HasOrthogonalProjection :=
  hasOrthogonalProjection_ker _ (ConstCoeffOp.isClosed_minimal _ h.out)

instance [h : Fact (IsOpen Ω)] : (magneticPMC 𝕜 Ω).HasOrthogonalProjection :=
  hasOrthogonalProjection_ker _ (ConstCoeffOp.isClosed_maximal _ h.out)

theorem curl_mem_magneticPEC (x : (pec 𝕜 hΩ).d₁.domain) :
    (pec 𝕜 hΩ).d₁ x ∈ magneticPEC 𝕜 Ω :=
  LinearPMap.mem_ker_iff.2 ⟨⟨_, ConstCoeffOp.minimal_mapsTo hΩ isComplexPair_curl_div x⟩, rfl,
    ConstCoeffOp.minimal_comp hΩ isComplexPair_curl_div x⟩

theorem curl_mem_magneticPMC (x : (pmc 𝕜 hΩ).d₁.domain) :
    (pmc 𝕜 hΩ).d₁ x ∈ magneticPMC 𝕜 Ω :=
  LinearPMap.mem_ker_iff.2 ⟨⟨_, ConstCoeffOp.maximal_mapsTo hΩ isComplexPair_curl_div x⟩, rfl,
    ConstCoeffOp.maximal_comp hΩ isComplexPair_curl_div x⟩

/-- With a perfect electric conductor on any open `Ω ⊆ ℝ³`, bounded or not, the Gauss laws
`σ = 0`, `div E = 0`, `div B = 0` (`B · n = 0`) propagate. [QuennevilleBelair2015], Prop 4.16 -/
theorem pec_gauss_propagates [Fact (IsOpen Ω)] {t₀ t₁ : ℝ}
    {F U : ℝ → PiLp 2 (ShortHilbertComplex.W3 (L2F 𝕜 Ω (Fin 1)) (L2F 𝕜 Ω (Fin 1 × Fin 3))
      (L2F 𝕜 Ω (Fin 1 × Fin 3)))}
    (hU : Evolution.IsStrongSolution (pec 𝕜 hΩ).wave (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ HilbertComplex.totalSub ((pec 𝕜 hΩ).divFreeSub (magneticPEC 𝕜 Ω)))
    (hF : ∀ t ∈ Icc t₀ t₁,
      F t ∈ HilbertComplex.totalSub ((pec 𝕜 hΩ).divFreeSub (magneticPEC 𝕜 Ω))) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ HilbertComplex.totalSub ((pec 𝕜 hΩ).divFreeSub (magneticPEC 𝕜 Ω)) :=
  (pec 𝕜 hΩ).divFree_propagates _ (curl_mem_magneticPEC hΩ) hU h0 hF

/-- With a perfect magnetic conductor on any open `Ω ⊆ ℝ³`, the Gauss laws propagate.
[QuennevilleBelair2015], Prop 4.16 -/
theorem pmc_gauss_propagates [Fact (IsOpen Ω)] {t₀ t₁ : ℝ}
    {F U : ℝ → PiLp 2 (ShortHilbertComplex.W3 (L2F 𝕜 Ω (Fin 1)) (L2F 𝕜 Ω (Fin 1 × Fin 3))
      (L2F 𝕜 Ω (Fin 1 × Fin 3)))}
    (hU : Evolution.IsStrongSolution (pmc 𝕜 hΩ).wave (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ HilbertComplex.totalSub ((pmc 𝕜 hΩ).divFreeSub (magneticPMC 𝕜 Ω)))
    (hF : ∀ t ∈ Icc t₀ t₁,
      F t ∈ HilbertComplex.totalSub ((pmc 𝕜 hΩ).divFreeSub (magneticPMC 𝕜 Ω))) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ HilbertComplex.totalSub ((pmc 𝕜 hΩ).divFreeSub (magneticPMC 𝕜 Ω)) :=
  (pmc 𝕜 hΩ).divFree_propagates _ (curl_mem_magneticPMC hΩ) hU h0 hF

end Conductor

end Feec.Maxwell
