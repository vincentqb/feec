module

public import Feec.Physics.Maxwell.Media
public import Feec.Domain.DeRham

/-!
# Maxwell's equations for differential forms on an open `Ω ⊆ ℝⁿ`

Maxwell's equations make sense in every dimension `n` and every degree: the electric field is a
`(k + 1)`-form `E`, the magnetic flux a `(k + 2)`-form `B`, the gauge field a `k`-form `σ`, and
the equations are the Hodge wave equation `σ' = −d†E`, `E' = dσ − d†B`, `B' = dE` of the three
consecutive degrees `k, k + 1, k + 2` of the `L²` de Rham complex of `Ω`
(`Feec.Domain.deRham`). With a **perfect electric conductor** (`Maxwell.pecForms`, tangential
trace of `E` vanishing) the complex is `H̊Λᵏ(Ω) → H̊Λᵏ⁺¹(Ω) → L²Λᵏ⁺²(Ω)`, the minimal
realizations of `d`.

The Gauss laws are `σ = 0`, `d†E = 0` (`d₀† = (dᵗ)_max`, `dᵗ = −δ` the codifferential) and
`dB = 0`. They propagate for every `n`, every `k` and every open `Ω` (bounded or not): an instance
of `ShortHilbertComplex.divFree_propagates`, with no closed-range, density or regularity
hypothesis.

For `n = 3`, `k = 0` the window is `H̊Λ⁰ → H̊Λ¹ → L²Λ²`: in degree `0` the exterior derivative
is the gradient (`Feec.Domain.extDerivOp_zero_apply`), and in degree `1` it is
`(dE)_{ij} = ∂ᵢEⱼ − ∂ⱼEᵢ` (`Feec.Domain.extDerivOp_one_apply_pair`), the curl in the `2`-form
coordinates `B₁₂, B₁₃, B₂₃`; this is the classical system of `Maxwell.pec` in form coordinates
(`Maxwell.pecForms_three_gauss_propagates`).

## Main results

* `Maxwell.pecForms_gauss_propagates`, `Maxwell.pecForms_three_gauss_propagates`.

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6 (the `L²` de Rham complex
  and its two boundary-condition families), Ch. 8 (evolution problems)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (`HΛᵏ`, `H̊Λᵏ`)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4 (the `L²` de Rham complex and its dual)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.9 (Prop 4.16: the divergence constraint propagates, both boundary conditions)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.Maxwell

open Feec.Domain ShortHilbertComplex HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (k : ℤ)

/-! ### The two boundary conditions -/

variable (𝕜) in
/-- **Perfect electric conductor** for `(k + 1)`-form electric fields:
`H̊Λᵏ(Ω) --d--> H̊Λᵏ⁺¹(Ω) --d--> L²Λᵏ⁺²(Ω)`, the minimal realizations of `d`. -/
def pecForms : ShortHilbertComplex 𝕜 (L2F 𝕜 Ω (formIdx n k)) (L2F 𝕜 Ω (formIdx n (k + 1)))
    (L2F 𝕜 Ω (formIdx n (k + 1 + 1))) :=
  ConstCoeffOp.shortMinimal (extDerivOp 𝕜 n k) (extDerivOp 𝕜 n (k + 1)) hΩ
    (isComplexPair_extDerivOp k)

variable (𝕜 Ω) in
/-- The magnetic Gauss law for PEC: `d_min B = 0` (`B` with vanishing tangential trace in the
next degree). -/
abbrev magneticPECForms : Submodule 𝕜 (L2F 𝕜 Ω (formIdx n (k + 1 + 1))) :=
  ((extDerivOp 𝕜 n (k + 1 + 1)).minimal Ω).ker

instance [h : Fact (IsOpen Ω)] : (magneticPECForms 𝕜 Ω k).HasOrthogonalProjection :=
  hasOrthogonalProjection_ker _ (ConstCoeffOp.isClosed_minimal _ h.out)

/-- `R(d_min) ⊆ N(d_min)`. -/
theorem d_mem_magneticPECForms (x : (pecForms 𝕜 hΩ k).d₁.domain) :
    (pecForms 𝕜 hΩ k).d₁ x ∈ magneticPECForms 𝕜 Ω k :=
  LinearPMap.mem_ker_iff.2
    ⟨⟨_, ConstCoeffOp.minimal_mapsTo hΩ (isComplexPair_extDerivOp (k + 1)) x⟩, rfl,
      ConstCoeffOp.minimal_comp hΩ (isComplexPair_extDerivOp (k + 1)) x⟩

/-! ### The Gauss laws propagate, every `n`, every `k` -/

section Propagation

variable [Fact (IsOpen Ω)]

/-- The total space `L²Λᵏ × L²Λᵏ⁺¹ × L²Λᵏ⁺²` of Maxwell's equations for forms. -/
abbrev FormSpace (𝕜 : Type*) [RCLike 𝕜] (Ω : Set (Fin n → ℝ)) (k : ℤ) :=
  PiLp 2 (W3 (L2F 𝕜 Ω (formIdx n k)) (L2F 𝕜 Ω (formIdx n (k + 1)))
    (L2F 𝕜 Ω (formIdx n (k + 1 + 1))))

/-- **Maxwell for forms with a perfect electric conductor** on any open `Ω ⊆ ℝⁿ`, any degree:
the Gauss laws `σ = 0`, `d†E = 0`, `dB = 0` propagate. -/
theorem pecForms_gauss_propagates {t₀ t₁ : ℝ} {F U : ℝ → FormSpace 𝕜 Ω k}
    (hU : Evolution.IsStrongSolution (pecForms 𝕜 hΩ k).wave (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ totalSub ((pecForms 𝕜 hΩ k).divFreeSub (magneticPECForms 𝕜 Ω k)))
    (hF : ∀ t ∈ Icc t₀ t₁,
      F t ∈ totalSub ((pecForms 𝕜 hΩ k).divFreeSub (magneticPECForms 𝕜 Ω k))) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ totalSub ((pecForms 𝕜 hΩ k).divFreeSub (magneticPECForms 𝕜 Ω k)) :=
  (pecForms 𝕜 hΩ k).divFree_propagates _ (d_mem_magneticPECForms hΩ k) hU h0 hF

/-- **The classical case** `n = 3`, `k = 0` (`E` a `1`-form, `B` a `2`-form,
`H̊Λ⁰ --d--> H̊Λ¹ --d--> L²Λ²`): the Gauss laws `σ = 0`, `δ E = 0`, `d_min B = 0` propagate for
a perfect electric conductor on any open `Ω ⊆ ℝ³`. Through the vector proxies
(`E ↦ (E₁, E₂, E₃)`, `B ↦ (B₂₃, −B₁₃, B₁₂)`) these are the laws `σ = 0`, `div E = 0`,
`div B = 0` with `B · n = 0` of `Maxwell.pec`; that identification is not formalized here. -/
theorem pecForms_three_gauss_propagates {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) [Fact (IsOpen Ω)]
    {t₀ t₁ : ℝ} {F U : ℝ → FormSpace 𝕜 Ω 0}
    (hU : Evolution.IsStrongSolution (pecForms 𝕜 hΩ 0).wave (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ totalSub ((pecForms 𝕜 hΩ 0).divFreeSub (magneticPECForms 𝕜 Ω 0)))
    (hF : ∀ t ∈ Icc t₀ t₁,
      F t ∈ totalSub ((pecForms 𝕜 hΩ 0).divFreeSub (magneticPECForms 𝕜 Ω 0))) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ totalSub ((pecForms 𝕜 hΩ 0).divFreeSub (magneticPECForms 𝕜 Ω 0)) :=
  pecForms_gauss_propagates hΩ 0 hU h0 hF

end Propagation

end Feec.Maxwell
