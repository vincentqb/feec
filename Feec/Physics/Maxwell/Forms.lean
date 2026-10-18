module

public import Feec.Physics.Maxwell.Media
public import Feec.Domain.DeRham

/-!
# Maxwell's equations for differential forms on an open `Ω ⊆ ℝⁿ`

Maxwell's equations make sense in every dimension `n` and every degree: the electric field is a
`(k + 1)`-form `E`, the magnetic flux a `(k + 2)`-form `B`, the gauge field a `k`-form `σ`, and
the equations are the Hodge wave equation `σ' = −d†E`, `E' = dσ − d†B`, `B' = dE` of the three
consecutive degrees `k, k + 1, k + 2` of the `L²` de Rham complex of `Ω`
(`Feec.Domain.deRham`). The two boundary conditions are the two realizations of `d`:

* **perfect electric conductor** (`Maxwell.pecForms`, tangential trace of `E` vanishing):
  `H̊Λᵏ(Ω) → H̊Λᵏ⁺¹(Ω) → L²Λᵏ⁺²(Ω)`, the degrees `k, k + 1` of the minimal de Rham complex
  (`minimalComplex_d_eq_pecForms_d₀`, `minimalComplex_d_eq_pecForms_d₁`);
* **perfect magnetic conductor** (`Maxwell.pmcForms`): `HΛᵏ(Ω) → HΛᵏ⁺¹(Ω) → L²Λᵏ⁺²(Ω)`, the
  maximal complex.

The Gauss laws are `σ = 0`, `d†E = 0` (with `d₀† = (dᵗ)_max` for PEC and `(dᵗ)_min` for PMC,
`dᵗ = −δ` the codifferential: `pecForms_adjoint_d₀`, `pmcForms_adjoint_d₀`) and `dB = 0`. They
propagate for every `n`, every `k`, every open `Ω` (bounded or not), and in every linear medium:
these are instances of `ShortHilbertComplex.divFree_propagates` and
`Maxwell.Medium.gauss_propagates`, with no closed-range, density or regularity hypothesis.

For `n = 3`, `k = 0` the window is `H̊Λ⁰ → H̊Λ¹ → L²Λ²`: in degree `0` the exterior derivative
is the gradient (`Feec.Domain.extDerivOp_zero_apply`), and in degree `1` it is
`(dE)_{ij} = ∂ᵢEⱼ − ∂ⱼEᵢ` (`Maxwell.extDerivOp_one_apply`), the curl in the `2`-form
coordinates `B₁₂, B₁₃, B₂₃`; this is the classical system of `Maxwell.pec` in form coordinates
(`Maxwell.pecForms_three_gauss_propagates`). The identification of the two realizations through
the vector proxies (`E ↦ (E₁, E₂, E₃)`, `B ↦ (B₂₃, −B₁₃, B₁₂)`) is not formalized here.

## Main results

* `Maxwell.pecForms_gauss_propagates`, `Maxwell.pmcForms_gauss_propagates`,
  `Maxwell.pecForms_gauss_existsUnique`, `Maxwell.pmcForms_gauss_existsUnique`.
* `Maxwell.pecForms_medium_gauss_propagates`, `Maxwell.pmcForms_medium_gauss_propagates`: in a
  linear medium, `div (ε E) = 0` and `d (μ H) = 0` propagate.

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6 (the `L²` de Rham complex
  and its two boundary-condition families), Ch. 8 (evolution problems)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (`HΛᵏ`, `H̊Λᵏ`)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4 (the `L²` de Rham complex and its dual)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.9 (Prop 4.16: the divergence constraint propagates, both boundary conditions)
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

variable (𝕜) in
/-- **Perfect magnetic conductor** for `(k + 1)`-form electric fields:
`HΛᵏ(Ω) --d--> HΛᵏ⁺¹(Ω) --d--> L²Λᵏ⁺²(Ω)`, the maximal (weak) realizations of `d`. -/
def pmcForms : ShortHilbertComplex 𝕜 (L2F 𝕜 Ω (formIdx n k)) (L2F 𝕜 Ω (formIdx n (k + 1)))
    (L2F 𝕜 Ω (formIdx n (k + 1 + 1))) :=
  ConstCoeffOp.shortMaximal (extDerivOp 𝕜 n k) (extDerivOp 𝕜 n (k + 1)) hΩ
    (isComplexPair_extDerivOp k)

/-- PEC is the window `k, k + 1` of the minimal de Rham complex: first differential. -/
theorem minimalComplex_d_eq_pecForms_d₀ :
    ((deRham 𝕜 n).minimalComplex hΩ).d k (k + 1) = (pecForms 𝕜 hΩ k).d₀ :=
  deRham_minimalComplex_d hΩ k

/-- PEC is the window `k, k + 1` of the minimal de Rham complex: second differential. -/
theorem minimalComplex_d_eq_pecForms_d₁ :
    ((deRham 𝕜 n).minimalComplex hΩ).d (k + 1) (k + 1 + 1) = (pecForms 𝕜 hΩ k).d₁ :=
  deRham_minimalComplex_d hΩ (k + 1)

/-- PMC is the window `k, k + 1` of the maximal de Rham complex: first differential. -/
theorem maximalComplex_d_eq_pmcForms_d₀ :
    ((deRham 𝕜 n).maximalComplex hΩ).d k (k + 1) = (pmcForms 𝕜 hΩ k).d₀ :=
  deRham_maximalComplex_d hΩ k

/-- PMC is the window `k, k + 1` of the maximal de Rham complex: second differential. -/
theorem maximalComplex_d_eq_pmcForms_d₁ :
    ((deRham 𝕜 n).maximalComplex hΩ).d (k + 1) (k + 1 + 1) = (pmcForms 𝕜 hΩ k).d₁ :=
  deRham_maximalComplex_d hΩ (k + 1)

/-- The electric Gauss law for PEC is `(dᵗ)_max E = 0`: the adjoint of `d_min` is the weak
formal adjoint `dᵗ = −δ` (no boundary condition). -/
theorem pecForms_adjoint_d₀ :
    (pecForms 𝕜 hΩ k).d₀† = (extDerivOp 𝕜 n k).formalAdj.maximal Ω :=
  (extDerivOp 𝕜 n k).adjoint_minimal

/-- The electric Gauss law for PMC is `(dᵗ)_min E = 0` (normal trace vanishing). -/
theorem pmcForms_adjoint_d₀ :
    (pmcForms 𝕜 hΩ k).d₀† = (extDerivOp 𝕜 n k).formalAdj.minimal Ω :=
  (extDerivOp 𝕜 n k).adjoint_maximal hΩ

variable (𝕜 Ω) in
/-- The magnetic Gauss law for PEC: `d_min B = 0` (`B` with vanishing tangential trace in the
next degree). -/
abbrev magneticPECForms : Submodule 𝕜 (L2F 𝕜 Ω (formIdx n (k + 1 + 1))) :=
  ((extDerivOp 𝕜 n (k + 1 + 1)).minimal Ω).ker

variable (𝕜 Ω) in
/-- The magnetic Gauss law for PMC: `d_max B = 0`. -/
abbrev magneticPMCForms : Submodule 𝕜 (L2F 𝕜 Ω (formIdx n (k + 1 + 1))) :=
  ((extDerivOp 𝕜 n (k + 1 + 1)).maximal Ω).ker

instance [h : Fact (IsOpen Ω)] : (magneticPECForms 𝕜 Ω k).HasOrthogonalProjection :=
  hasOrthogonalProjection_ker _ (ConstCoeffOp.isClosed_minimal _ h.out)

instance [h : Fact (IsOpen Ω)] : (magneticPMCForms 𝕜 Ω k).HasOrthogonalProjection :=
  hasOrthogonalProjection_ker _ (ConstCoeffOp.isClosed_maximal _ h.out)

/-- `R(d_min) ⊆ N(d_min)`. -/
theorem d_mem_magneticPECForms (x : (pecForms 𝕜 hΩ k).d₁.domain) :
    (pecForms 𝕜 hΩ k).d₁ x ∈ magneticPECForms 𝕜 Ω k :=
  LinearPMap.mem_ker_iff.2
    ⟨⟨_, ConstCoeffOp.minimal_mapsTo hΩ (isComplexPair_extDerivOp (k + 1)) x⟩, rfl,
      ConstCoeffOp.minimal_comp hΩ (isComplexPair_extDerivOp (k + 1)) x⟩

/-- `R(d_max) ⊆ N(d_max)`. -/
theorem d_mem_magneticPMCForms (x : (pmcForms 𝕜 hΩ k).d₁.domain) :
    (pmcForms 𝕜 hΩ k).d₁ x ∈ magneticPMCForms 𝕜 Ω k :=
  LinearPMap.mem_ker_iff.2
    ⟨⟨_, ConstCoeffOp.maximal_mapsTo hΩ (isComplexPair_extDerivOp (k + 1)) x⟩, rfl,
      ConstCoeffOp.maximal_comp hΩ (isComplexPair_extDerivOp (k + 1)) x⟩

/-- **In degree `1`, `d` is the curl in `2`-form coordinates**: `(dE)_{ij} = ∂ᵢ Eⱼ − ∂ⱼ Eᵢ`
for `i < j` (any `n`). -/
theorem extDerivOp_one_apply (w : formIdx n 1 → (Fin n → ℝ) → 𝕜) {i j : Fin n} (hij : i < j)
    (x : Fin n → ℝ) :
    (extDerivOp 𝕜 n 1).apply w ⟨{i, j}, by rw [Finset.card_pair hij.ne]; norm_num⟩ x =
      fderiv ℝ (w ⟨{j}, by simp⟩) x (coordDir i) - fderiv ℝ (w ⟨{i}, by simp⟩) x (coordDir j) := by
  rw [extDerivOp_apply]
  simp only [extD]
  rw [Finset.sum_pair hij.ne]
  have e1 : ({i, j} : Finset (Fin n)).erase i = {j} := by
    rw [Finset.erase_insert (by simp [hij.ne])]
  have e2 : ({i, j} : Finset (Fin n)).erase j = {i} := by
    rw [Finset.erase_insert_of_ne hij.ne, Finset.erase_singleton, insert_empty_eq]
  have s1 : ({l ∈ ({i, j} : Finset (Fin n)) | l < i}) = ∅ := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      iff_false, not_and, not_lt]
    rintro (rfl | rfl)
    · exact le_rfl
    · exact hij.le
  have s2 : ({l ∈ ({i, j} : Finset (Fin n)) | l < j}) = {i} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · rfl
      · exact absurd h (lt_irrefl _)
    · rintro rfl
      exact ⟨Or.inl rfl, hij⟩
  rw [e1, e2, formExt_of_card w (by simp), formExt_of_card w (by simp)]
  simp [ExteriorFibre.sgn, s1, s2, sub_eq_add_neg]

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

/-- **Maxwell for forms with a perfect magnetic conductor** on any open `Ω ⊆ ℝⁿ`, any degree:
the Gauss laws propagate. -/
theorem pmcForms_gauss_propagates {t₀ t₁ : ℝ} {F U : ℝ → FormSpace 𝕜 Ω k}
    (hU : Evolution.IsStrongSolution (pmcForms 𝕜 hΩ k).wave (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ totalSub ((pmcForms 𝕜 hΩ k).divFreeSub (magneticPMCForms 𝕜 Ω k)))
    (hF : ∀ t ∈ Icc t₀ t₁,
      F t ∈ totalSub ((pmcForms 𝕜 hΩ k).divFreeSub (magneticPMCForms 𝕜 Ω k))) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ totalSub ((pmcForms 𝕜 hΩ k).divFreeSub (magneticPMCForms 𝕜 Ω k)) :=
  (pmcForms 𝕜 hΩ k).divFree_propagates _ (d_mem_magneticPMCForms hΩ k) hU h0 hF

/-- **Well-posedness in the Gauss-law subspace** (PEC, forms): for data in the domain satisfying
the Gauss laws and admissible forcing satisfying them, there is a unique classical solution, and
it satisfies the Gauss laws for all times. -/
theorem pecForms_gauss_existsUnique {U₀ : FormSpace 𝕜 Ω k}
    (hU₀ : U₀ ∈ (pecForms 𝕜 hΩ k).wave.domain)
    (hU₀S : U₀ ∈ totalSub ((pecForms 𝕜 hΩ k).divFreeSub (magneticPECForms 𝕜 Ω k)))
    {F : ℝ → FormSpace 𝕜 Ω k} {t₀ t₁ : ℝ}
    (hF : Evolution.ForcingClass.admissible (pecForms 𝕜 hΩ k).wave t₀ t₁ F)
    (hFS : ∀ t ∈ Icc t₀ t₁,
      F t ∈ totalSub ((pecForms 𝕜 hΩ k).divFreeSub (magneticPECForms 𝕜 Ω k))) :
    ∃ U, U t₀ = U₀ ∧ Evolution.IsClassicalSolution (pecForms 𝕜 hΩ k).wave (Icc t₀ t₁) F U ∧
      (∀ t ∈ Icc t₀ t₁, U t ∈ totalSub ((pecForms 𝕜 hΩ k).divFreeSub (magneticPECForms 𝕜 Ω k))) ∧
      ∀ W, W t₀ = U₀ → Evolution.IsStrongSolution (pecForms 𝕜 hΩ k).wave (Icc t₀ t₁) F W →
        EqOn W U (Icc t₀ t₁) :=
  ((pecForms 𝕜 hΩ k).reducingSubcomplex_divFreeSub _ (d_mem_magneticPECForms hΩ k)).existsUnique_mem
    hU₀ hU₀S hF hFS

/-- **Well-posedness in the Gauss-law subspace** (PMC, forms). -/
theorem pmcForms_gauss_existsUnique {U₀ : FormSpace 𝕜 Ω k}
    (hU₀ : U₀ ∈ (pmcForms 𝕜 hΩ k).wave.domain)
    (hU₀S : U₀ ∈ totalSub ((pmcForms 𝕜 hΩ k).divFreeSub (magneticPMCForms 𝕜 Ω k)))
    {F : ℝ → FormSpace 𝕜 Ω k} {t₀ t₁ : ℝ}
    (hF : Evolution.ForcingClass.admissible (pmcForms 𝕜 hΩ k).wave t₀ t₁ F)
    (hFS : ∀ t ∈ Icc t₀ t₁,
      F t ∈ totalSub ((pmcForms 𝕜 hΩ k).divFreeSub (magneticPMCForms 𝕜 Ω k))) :
    ∃ U, U t₀ = U₀ ∧ Evolution.IsClassicalSolution (pmcForms 𝕜 hΩ k).wave (Icc t₀ t₁) F U ∧
      (∀ t ∈ Icc t₀ t₁, U t ∈ totalSub ((pmcForms 𝕜 hΩ k).divFreeSub (magneticPMCForms 𝕜 Ω k))) ∧
      ∀ W, W t₀ = U₀ → Evolution.IsStrongSolution (pmcForms 𝕜 hΩ k).wave (Icc t₀ t₁) F W →
        EqOn W U (Icc t₀ t₁) :=
  ((pmcForms 𝕜 hΩ k).reducingSubcomplex_divFreeSub _ (d_mem_magneticPMCForms hΩ k)).existsUnique_mem
    hU₀ hU₀S hF hFS

/-- **Maxwell for forms in a linear medium, PEC**: the weighted Gauss laws `σ = 0`,
`d₀† (ε E) = 0`, `d_min (μ H) = 0` propagate, any `n`, any `k`. -/
theorem pecForms_medium_gauss_propagates
    (M : Medium 𝕜 (L2F 𝕜 Ω (formIdx n (k + 1))) (L2F 𝕜 Ω (formIdx n (k + 1 + 1))))
    {t₀ t₁ : ℝ} {F U : ℝ → FormSpace 𝕜 Ω k}
    (hU : Evolution.IsStrongSolution (M.maxwell (pecForms 𝕜 hΩ k)) (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ M.gauss (pecForms 𝕜 hΩ k) (magneticPECForms 𝕜 Ω k))
    (hF : ∀ t ∈ Icc t₀ t₁, F t ∈ M.gauss (pecForms 𝕜 hΩ k) (magneticPECForms 𝕜 Ω k)) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ M.gauss (pecForms 𝕜 hΩ k) (magneticPECForms 𝕜 Ω k) :=
  M.gauss_propagates _ (d_mem_magneticPECForms hΩ k) hU h0 hF

/-- **Maxwell for forms in a linear medium, PMC**: the weighted Gauss laws propagate. -/
theorem pmcForms_medium_gauss_propagates
    (M : Medium 𝕜 (L2F 𝕜 Ω (formIdx n (k + 1))) (L2F 𝕜 Ω (formIdx n (k + 1 + 1))))
    {t₀ t₁ : ℝ} {F U : ℝ → FormSpace 𝕜 Ω k}
    (hU : Evolution.IsStrongSolution (M.maxwell (pmcForms 𝕜 hΩ k)) (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ M.gauss (pmcForms 𝕜 hΩ k) (magneticPMCForms 𝕜 Ω k))
    (hF : ∀ t ∈ Icc t₀ t₁, F t ∈ M.gauss (pmcForms 𝕜 hΩ k) (magneticPMCForms 𝕜 Ω k)) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ M.gauss (pmcForms 𝕜 hΩ k) (magneticPMCForms 𝕜 Ω k) :=
  M.gauss_propagates _ (d_mem_magneticPMCForms hΩ k) hU h0 hF

/-- **The classical case** `n = 3`, `k = 0` (`E` a `1`-form, `B` a `2`-form,
`H̊Λ⁰ --grad--> H̊Λ¹ --curl--> L²Λ²`): the Gauss laws `σ = 0`, `div E = 0`, `div B = 0`
(`B · n = 0`) propagate for a perfect electric conductor on any open `Ω ⊆ ℝ³`, as for
`Maxwell.pec` (`Maxwell.pec_gauss_propagates`). -/
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
