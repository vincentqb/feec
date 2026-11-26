module

public import Feec.Physics.Maxwell.Media
public import Feec.Domain.DeRham

/-!
# Maxwell's equations for differential forms on an open `Ω ⊆ ℝⁿ`

Maxwell's equations in every dimension `n` and degree `k`, as the Hodge wave equation of three
consecutive degrees of the `L²` de Rham complex of an open `Ω`; with a perfect electric conductor
the Gauss laws propagate (`pecForms_gauss_propagates`, `pecForms_three_gauss_propagates`).
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.Maxwell

open Feec.Domain ShortHilbertComplex HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (k : ℤ)

/-! ### The perfect electric conductor -/

variable (𝕜) in
/-- Perfect electric conductor for `(k + 1)`-form fields: `H̊Λᵏ(Ω) → H̊Λᵏ⁺¹(Ω) → L²Λᵏ⁺²(Ω)`. -/
def pecForms : ShortHilbertComplex 𝕜 (L2F 𝕜 Ω (formIdx n k)) (L2F 𝕜 Ω (formIdx n (k + 1)))
    (L2F 𝕜 Ω (formIdx n (k + 1 + 1))) :=
  ConstCoeffOp.shortMinimal (extDerivOp 𝕜 n k) (extDerivOp 𝕜 n (k + 1)) hΩ
    (isComplexPair_extDerivOp k)

variable (𝕜 Ω) in
/-- The magnetic Gauss law for a perfect electric conductor: `d_min B = 0`. -/
abbrev magneticPECForms : Submodule 𝕜 (L2F 𝕜 Ω (formIdx n (k + 1 + 1))) :=
  ((extDerivOp 𝕜 n (k + 1 + 1)).minimal Ω).ker

instance [h : Fact (IsOpen Ω)] : (magneticPECForms 𝕜 Ω k).HasOrthogonalProjection :=
  hasOrthogonalProjection_ker _ (ConstCoeffOp.isClosed_minimal _ h.out)

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

/-- With a perfect electric conductor on any open `Ω ⊆ ℝⁿ`, in any degree, the Gauss laws
`σ = 0`, `d†E = 0`, `dB = 0` propagate. -/
theorem pecForms_gauss_propagates {t₀ t₁ : ℝ} {F U : ℝ → FormSpace 𝕜 Ω k}
    (hU : Evolution.IsStrongSolution (pecForms 𝕜 hΩ k).wave (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ totalSub ((pecForms 𝕜 hΩ k).divFreeSub (magneticPECForms 𝕜 Ω k)))
    (hF : ∀ t ∈ Icc t₀ t₁,
      F t ∈ totalSub ((pecForms 𝕜 hΩ k).divFreeSub (magneticPECForms 𝕜 Ω k))) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ totalSub ((pecForms 𝕜 hΩ k).divFreeSub (magneticPECForms 𝕜 Ω k)) :=
  (pecForms 𝕜 hΩ k).divFree_propagates _ (d_mem_magneticPECForms hΩ k) hU h0 hF

/-- For `n = 3`, `k = 0` (`E` a `1`-form, `B` a `2`-form), the Gauss laws `σ = 0`, `δ E = 0`,
`d_min B = 0` propagate for a perfect electric conductor on any open `Ω ⊆ ℝ³`. -/
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
