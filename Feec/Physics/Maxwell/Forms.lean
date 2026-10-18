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
(`Maxwell.pecForms_three_gauss_propagates`). Through the vector proxies (`E ↦ (E₁, E₂, E₃)`,
`B ↦ (B₂₃, −B₁₃, B₁₂)`, `Maxwell.relabelL2F`) the PEC complex of forms *is* the complex of
`Maxwell.pec` (`Maxwell.pecForms_conj_eq_pec`, via `Maxwell.minimal_eq_conj_relabel`: minimal
realizations commute with signed relabellings of the components).

## Main results

* `Maxwell.pecForms_gauss_propagates`, `Maxwell.pmcForms_gauss_propagates`,
  `Maxwell.pecForms_gauss_existsUnique`, `Maxwell.pmcForms_gauss_existsUnique`.
* `Maxwell.pecForms_medium_gauss_propagates`, `Maxwell.pmcForms_medium_gauss_propagates`: in a
  linear medium, `div (ε E) = 0` and `d (μ H) = 0` propagate.
* `Maxwell.extDerivOp_one_apply`: `(dE)_{ij} = ∂ᵢEⱼ − ∂ⱼEᵢ`.
* `Maxwell.minimal_eq_conj_relabel`, `Maxwell.pecForms_conj_eq_pec`: for `n = 3`, `k = 0`,
  `(pecForms 0).conj U₀ U₁ U₂ = Maxwell.pec` for the proxy isomorphisms `Uᵢ`.

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

/-! ### Relabelling the components of a field -/

section Relabel

variable {m : ℕ} {Ω' : Set (Fin m → ℝ)} {ι ι' : Type} [Fintype ι] [Fintype ι']

/-- Relabel the components of a field by `π : ι' ≃ ι` with signs `c`: `(R φ)_j = c_j φ_{π j}`. -/
def relabelField (π : ι' ≃ ι) (c : ι' → 𝕜) (φ : ι → (Fin m → ℝ) → 𝕜) :
    ι' → (Fin m → ℝ) → 𝕜 :=
  fun j => c j • φ (π j)

omit [Fintype ι] [Fintype ι'] in
theorem isTestField_relabelField (π : ι' ≃ ι) (c : ι' → 𝕜) {φ : ι → (Fin m → ℝ) → 𝕜}
    (hφ : IsTestField Ω' φ) : IsTestField Ω' (relabelField π c φ) :=
  fun j => (hφ (π j)).smul (c j)

omit [Fintype ι] [Fintype ι'] in
/-- Relabelling back: `R_{π, c} R_{π⁻¹, c ∘ π⁻¹} = 1` for signs `c² = 1`. -/
theorem relabelField_relabelField_symm (π : ι' ≃ ι) {c : ι' → 𝕜} (hc : ∀ j, c j * c j = 1)
    (ψ : ι' → (Fin m → ℝ) → 𝕜) :
    relabelField π c (relabelField π.symm (fun i => c (π.symm i)) ψ) = ψ := by
  funext j x
  simp only [relabelField, Pi.smul_apply, Equiv.symm_apply_apply, smul_eq_mul, ← mul_assoc,
    hc, one_mul]

variable (Ω') in
/-- The diagonal sign operator `u ↦ (c_j u_j)_j` on `L²(Ω; 𝕜^ι')`. -/
def signL2F (c : ι' → 𝕜) : L2F 𝕜 Ω' ι' →L[𝕜] L2F 𝕜 Ω' ι' :=
  ((PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι' => L2 𝕜 Ω')).symm :
      (ι' → L2 𝕜 Ω') →L[𝕜] L2F 𝕜 Ω' ι').comp
    ((ContinuousLinearMap.pi fun j => c j • ContinuousLinearMap.proj j).comp
      (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι' => L2 𝕜 Ω') : L2F 𝕜 Ω' ι' →L[𝕜] ι' → L2 𝕜 Ω'))

omit [Fintype ι'] in
theorem signL2F_apply (c : ι' → 𝕜) (u : L2F 𝕜 Ω' ι') (j : ι') :
    signL2F Ω' c u j = c j • u j := rfl

omit [Fintype ι'] in
theorem signL2F_signL2F {c : ι' → 𝕜} (hc : ∀ j, c j * c j = 1) (u : L2F 𝕜 Ω' ι') :
    signL2F Ω' c (signL2F Ω' c u) = u :=
  PiLp.ext fun j => by rw [signL2F_apply, signL2F_apply, smul_smul, hc, one_smul]

variable (Ω') in
/-- The **relabelling isomorphism** `L²(Ω; 𝕜^ι) ≃ L²(Ω; 𝕜^ι')`, `(U u)_j = c_j u_{π j}`. -/
def relabelL2F (π : ι' ≃ ι) {c : ι' → 𝕜} (hc : ∀ j, c j * c j = 1) :
    L2F 𝕜 Ω' ι ≃L[𝕜] L2F 𝕜 Ω' ι' :=
  (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 (L2 𝕜 Ω') π.symm).toContinuousLinearEquiv.trans
    (ContinuousLinearEquiv.equivOfInverse (signL2F Ω' c) (signL2F Ω' c) (signL2F_signL2F hc)
      (signL2F_signL2F hc))

theorem relabelL2F_apply (π : ι' ≃ ι) {c : ι' → 𝕜} (hc : ∀ j, c j * c j = 1)
    (u : L2F 𝕜 Ω' ι) (j : ι') : relabelL2F Ω' π hc u j = c j • u (π j) := by
  change signL2F Ω' c (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 (L2 𝕜 Ω') π.symm u) j = _
  rw [signL2F_apply, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    Equiv.symm_symm]

theorem testField_relabelField (π : ι' ≃ ι) {c : ι' → 𝕜} (hc : ∀ j, c j * c j = 1)
    {φ : ι → (Fin m → ℝ) → 𝕜} (hφ : IsTestField Ω' φ) :
    testField (isTestField_relabelField π c hφ) = relabelL2F Ω' π hc (testField hφ) :=
  PiLp.ext fun j => by
    rw [testField_apply, relabelL2F_apply, testField_apply]
    exact toL2_smul (c j) (hφ (π j))

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

/-- **Minimal realizations commute with relabelling**: if `A' R_ι = R_κ A` on test fields, then
`A'_min = U_κ A_min U_ι⁻¹`. -/
theorem minimal_eq_conj_relabel (hΩ' : IsOpen Ω') {A : ConstCoeffOp (Fin m → ℝ) 𝕜 ι κ}
    {A' : ConstCoeffOp (Fin m → ℝ) 𝕜 ι' κ'} (πι : ι' ≃ ι) {cι : ι' → 𝕜}
    (hcι : ∀ j, cι j * cι j = 1) (πκ : κ' ≃ κ) {cκ : κ' → 𝕜} (hcκ : ∀ j, cκ j * cκ j = 1)
    (hA : ∀ φ : ι → (Fin m → ℝ) → 𝕜, IsTestField Ω' φ →
      A'.apply (relabelField πι cι φ) = relabelField πκ cκ (A.apply φ)) :
    A'.minimal Ω' = (A.minimal Ω').conj (relabelL2F Ω' πι hcι) (relabelL2F Ω' πκ hcκ) := by
  set Uι := relabelL2F Ω' πι hcι
  set Uκ := relabelL2F Ω' πκ hcκ
  set h : L2F 𝕜 Ω' ι × L2F 𝕜 Ω' κ ≃ₜ L2F 𝕜 Ω' ι' × L2F 𝕜 Ω' κ' :=
    Uι.toHomeomorph.prodCongr Uκ.toHomeomorph
  -- the test graphs correspond
  have hg : (A'.testGraph Ω' : Set (L2F 𝕜 Ω' ι' × L2F 𝕜 Ω' κ')) = h '' (A.testGraph Ω') := by
    ext p
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      set φ := relabelField πι.symm (fun i => cι (πι.symm i)) ψ
      have hφ : IsTestField Ω' φ := isTestField_relabelField _ _ hψ
      have e : relabelField πι cι φ = ψ := relabelField_relabelField_symm πι hcι ψ
      refine ⟨(testField hφ, testField (A.isTestField_apply hφ)), ⟨φ, hφ, rfl⟩, ?_⟩
      change (Uι (testField hφ), Uκ (testField (A.isTestField_apply hφ))) = _
      rw [← testField_relabelField πι hcι hφ, ← testField_relabelField πκ hcκ
        (A.isTestField_apply hφ)]
      refine Prod.ext (testField_congr _ _ e) (testField_congr _ _ ?_)
      rw [← hA φ hφ, e]
    · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
      refine ⟨relabelField πι cι φ, isTestField_relabelField πι cι hφ, ?_⟩
      change (Uι (testField hφ), Uκ (testField (A.isTestField_apply hφ))) = _
      rw [← testField_relabelField πι hcι hφ, ← testField_relabelField πκ hcκ
        (A.isTestField_apply hφ)]
      exact Prod.ext rfl (testField_congr _ _ (hA φ hφ).symm)
  refine LinearPMap.eq_of_eq_graph ?_
  ext p
  rw [A'.minimal_graph hΩ', mem_conj_graph_iff, A.minimal_graph hΩ']
  change p ∈ ((A'.testGraph Ω').topologicalClosure : Set _) ↔
    (Uι.symm p.1, Uκ.symm p.2) ∈ ((A.testGraph Ω').topologicalClosure : Set _)
  rw [Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe, hg, ← h.image_closure,
    h.image_eq_preimage_symm]
  rfl

end Relabel

/-! ### The classical case `n = 3`, `k = 0`: the vector proxies -/

section Proxy

/-- The proxy of `0`-forms on `ℝ³`: the scalar component. -/
def proxy₀ : Fin 1 ≃ formIdx 3 0 :=
  Equiv.ofBijective (fun _ => ⟨∅, by simp⟩) (by decide)

/-- The proxy of `1`-forms on `ℝ³`: `E = (E₁, E₂, E₃)`, `E_i = E_{{i}}`. -/
def proxy₁ : Fin 1 × Fin 3 ≃ formIdx 3 1 :=
  Equiv.ofBijective (fun p => ⟨{p.2}, by simp⟩) (by decide)

/-- The proxy of `2`-forms on `ℝ³` (the Hodge star): `B_k = ± B_{univ ∖ {k}}`. -/
def proxy₂ : Fin 1 × Fin 3 ≃ formIdx 3 2 :=
  Equiv.ofBijective (fun p => ⟨Finset.univ.erase p.2, by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp⟩) (by decide)

/-- The signs of the Hodge star in degree `2`: `B = (B₂₃, −B₁₃, B₁₂)`. -/
def sign₂ : Fin 1 × Fin 3 → 𝕜 := fun p => if p.2 = 1 then -1 else 1

theorem sign₂_mul_self (p : Fin 1 × Fin 3) : (sign₂ p : 𝕜) * sign₂ p = 1 := by
  unfold sign₂; split_ifs <;> simp

/-- In degree `0`, `d` is the gradient through the proxies. -/
theorem gradOp_relabel (φ : formIdx 3 0 → (Fin 3 → ℝ) → 𝕜) :
    (gradOp 3 1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply (relabelField proxy₀ (fun _ => 1) φ) =
      relabelField proxy₁ (fun _ => 1) ((extDerivOp 𝕜 3 0).apply φ) := by
  funext p x
  obtain ⟨i, j⟩ := p
  rw [gradOp_apply]
  simp only [relabelField, one_smul]
  exact (extDerivOp_zero_apply φ j x).symm

/-- In degree `1`, `d` is the curl through the proxies. -/
theorem curlOp_relabel (ψ : formIdx 3 1 → (Fin 3 → ℝ) → 𝕜) :
    (curlOp 1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply (relabelField proxy₁ (fun _ => 1) ψ) =
      relabelField proxy₂ sign₂ ((extDerivOp 𝕜 3 1).apply ψ) := by
  funext p x
  obtain ⟨i, k⟩ := p
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rw [curlOp_apply]
  simp only [relabelField, one_smul, Pi.smul_apply]
  fin_cases k
  · change fderiv ℝ (ψ (proxy₁ (0, 2))) x (coordDir 1) - fderiv ℝ (ψ (proxy₁ (0, 1))) x
        (coordDir 2) = sign₂ (0, 0) • (extDerivOp 𝕜 3 1).apply ψ (proxy₂ (0, 0)) x
    rw [show proxy₂ (0, 0) = ⟨{1, 2}, by decide⟩ from Subtype.ext (by decide),
      extDerivOp_one_apply ψ (by decide : (1 : Fin 3) < 2)]
    rw [show (sign₂ ((0 : Fin 1), (0 : Fin 3)) : 𝕜) = 1 by simp [sign₂], one_smul]
    rfl
  · change fderiv ℝ (ψ (proxy₁ (0, 0))) x (coordDir 2) - fderiv ℝ (ψ (proxy₁ (0, 2))) x
        (coordDir 0) = sign₂ (0, 1) • (extDerivOp 𝕜 3 1).apply ψ (proxy₂ (0, 1)) x
    rw [show proxy₂ (0, 1) = ⟨{0, 2}, by decide⟩ from Subtype.ext (by decide),
      extDerivOp_one_apply ψ (by decide : (0 : Fin 3) < 2)]
    rw [show (sign₂ ((0 : Fin 1), (1 : Fin 3)) : 𝕜) = -1 by simp [sign₂], neg_smul, one_smul,
      neg_sub]
    rfl
  · change fderiv ℝ (ψ (proxy₁ (0, 1))) x (coordDir 0) - fderiv ℝ (ψ (proxy₁ (0, 0))) x
        (coordDir 1) = sign₂ (0, 2) • (extDerivOp 𝕜 3 1).apply ψ (proxy₂ (0, 2)) x
    rw [show proxy₂ (0, 2) = ⟨{0, 1}, by decide⟩ from Subtype.ext (by decide),
      extDerivOp_one_apply ψ (by decide : (0 : Fin 3) < 1)]
    rw [show (sign₂ ((0 : Fin 1), (2 : Fin 3)) : 𝕜) = 1 by simp [sign₂], one_smul]
    rfl

/-- Short complexes with the same differentials are equal. -/
theorem shortComplex_ext {W₀ W₁ W₂ : Type*} [NormedAddCommGroup W₀]
    [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀] [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁]
    [CompleteSpace W₁] [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]
    {S S' : ShortHilbertComplex 𝕜 W₀ W₁ W₂} (h₀ : S.d₀ = S'.d₀) (h₁ : S.d₁ = S'.d₁) : S = S' := by
  cases S; cases S'; cases h₀; cases h₁; rfl

/-- **Consistency with `Maxwell.pec`**: for `n = 3`, `k = 0` the PEC complex of forms
`H̊Λ⁰ → H̊Λ¹ → L²Λ²`, transported through the vector proxies (`f ↦ f`, `E ↦ (E₁, E₂, E₃)`,
`B ↦ (B₂₃, −B₁₃, B₁₂)`), is the `grad`–`curl` complex `H̊¹ → H̊(curl) → L²` of
`Maxwell.pec`. -/
theorem pecForms_conj_eq_pec {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) :
    (pecForms 𝕜 hΩ 0).conj (relabelL2F Ω proxy₀ fun _ => one_mul (1 : 𝕜))
      (relabelL2F Ω proxy₁ fun _ => one_mul (1 : 𝕜)) (relabelL2F Ω proxy₂ sign₂_mul_self) =
      pec 𝕜 hΩ := by
  refine shortComplex_ext ?_ ?_
  · exact (minimal_eq_conj_relabel hΩ proxy₀ (fun _ => one_mul (1 : 𝕜)) proxy₁
      (fun _ => one_mul (1 : 𝕜)) fun φ _ => gradOp_relabel φ).symm
  · exact (minimal_eq_conj_relabel hΩ proxy₁ (fun _ => one_mul (1 : 𝕜)) proxy₂ sign₂_mul_self
      fun ψ _ => curlOp_relabel ψ).symm

end Proxy

end Feec.Maxwell
