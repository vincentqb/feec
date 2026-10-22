module

public import Feec.Models.BoundedDomain.SymCurl

/-!
# The minimal Hessian and the weak double divergence on a bounded domain

On an open `Ω ⊆ ℝ³` the Hessian `grad grad : 𝕜 → 𝕜³ˣ³` and the double divergence
`div div : 𝕜³ˣ³ → 𝕜` (`Feec.Domain.hessOp`, `Feec.Domain.divdivOp`) are formal adjoints
(`Feec.Domain.divdivOp_formalAdj`). Along the scalar embedding `L²(Ω) ↪ L²(Ω; 𝕜^{Unit})`
(`Feec.Domain.L2.toL2F`) their constrained realizations are

* `hessMin`: `grad grad` on `H̊²(Ω)`, the closure on `C_c^∞(Ω)`, closed and densely defined;
* `divdivMax = hessMin†`: the weak double divergence on `H(div div, Ω)`
  (`mem_divdivMax_domain_iff`), with
  `ker divdivMax = {B : ⟪B, ∇²φ⟫ = 0 for all φ ∈ C_c^∞(Ω)}` (`mem_ker_divdivMax_iff`).

The Hessian–curl complexes on symmetric fields are in `Feec.Models.BoundedDomain.SymCurl`; the
first operator of the BGG complex (5.1) is `hessMin` (`Feec.Models.BoundedDomain.BGG`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.3 (the BGG complex on a bounded domain, `H̊²`)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §8 (Hessian and div-div complexes)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ContDiff ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology Feec.Domain

namespace Feec.Models.BoundedDomain

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Set R3}

/-- The identity embedding has dense test fields. -/
theorem denseVia_id (hΩ : IsOpen Ω) {κ : Type*} [Fintype κ] :
    ConstCoeffOp.DenseVia (LinearIsometry.id : L2F 𝕜 Ω κ →ₗᵢ[𝕜] L2F 𝕜 Ω κ) :=
  ConstCoeffOp.denseVia_of_surjective hΩ _ fun y => ⟨y, rfl⟩

variable (𝕜) in
/-- **The minimal Hessian** `grad grad : H̊²(Ω) → L²(Ω; 𝕜³ˣ³)`, the closure of the Hessian on
`C_c^∞(Ω)`. -/
def hessMin (_hΩ : IsOpen Ω) : L2 𝕜 Ω →ₗ.[𝕜] L2F 𝕜 Ω Ix :=
  (hessOp 3).minimalVia (L2.toL2F 𝕜 Ω) LinearIsometry.id

theorem isClosed_hessMin (hΩ : IsOpen Ω) : (hessMin 𝕜 hΩ).IsClosed :=
  (hessOp 3).isClosed_minimalVia _ _ (denseVia_id hΩ)

theorem dense_hessMin_domain (hΩ : IsOpen Ω) : Dense ((hessMin 𝕜 hΩ).domain : Set (L2 𝕜 Ω)) :=
  (hessOp 3).dense_minimalVia_domain_of _ _ (denseVia_id hΩ) (denseVia_scalar hΩ)
    fun _ hφ _ _ => ⟨testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ), rfl⟩

variable (𝕜) in
/-- **The maximal (weak) double divergence** on `H(div div, Ω)`, `(grad grad on H̊²)†`. -/
abbrev divdivMax (hΩ : IsOpen Ω) : L2F 𝕜 Ω Ix →ₗ.[𝕜] L2 𝕜 Ω := (hessMin 𝕜 hΩ)†

/-- **`D(divdivMax) = H(div div, Ω)`**: a weak double divergence in `L²(Ω)`. -/
theorem mem_divdivMax_domain_iff (hΩ : IsOpen Ω) {B : L2F 𝕜 Ω Ix} :
    B ∈ (divdivMax 𝕜 hΩ).domain ↔ ∃ D : L2 𝕜 Ω,
      ∀ p ∈ (hessOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia (L2.toL2F 𝕜 Ω) LinearIsometry.id,
        ⟪D, p.1⟫_𝕜 = ⟪B, p.2⟫_𝕜 :=
  (hessOp 3).mem_adjoint_minimalVia_domain_iff _ _ (denseVia_id hΩ) (dense_hessMin_domain hΩ)

/-- `ker (grad grad)† = H(div div, 0)`: `B ⊥ ∇²φ` for every test function `φ`. -/
theorem mem_ker_divdivMax_iff (hΩ : IsOpen Ω) {B : L2F 𝕜 Ω Ix} :
    B ∈ (divdivMax 𝕜 hΩ).ker ↔ ∀ (φ : Unit → R3 → 𝕜) (hφ : IsTestField Ω φ),
      ⟪B, testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ)⟫_𝕜 = 0 := by
  constructor
  · intro hB φ hφ
    obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hB
    subst hy
    have hp : ((testField hφ () : L2 𝕜 Ω),
        testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ)) ∈
          (hessMin 𝕜 hΩ).graph :=
      (hessOp 3).mem_graph_minimalVia _ _ (denseVia_id hΩ)
        ⟨φ, hφ, (WithLp.ext_iff 2).2 (funext fun _ => rfl), rfl⟩
    have e := LinearPMap.adjoint_inner_of_mem_graph (T := hessMin 𝕜 hΩ) (dense_hessMin_domain hΩ)
      y hp
    simp only at e
    rw [hy0, inner_zero_left] at e
    exact e.symm
  · intro hB
    have key : ∀ p ∈ (hessOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia (L2.toL2F 𝕜 Ω)
        LinearIsometry.id, ⟪(0 : L2 𝕜 Ω), p.1⟫_𝕜 = ⟪B, p.2⟫_𝕜 := by
      rintro ⟨x, y⟩ ⟨φ, hφ, -, h2⟩
      simp only at h2
      rw [inner_zero_left]
      have h2' : y = testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ) := h2
      change 0 = ⟪B, y⟫_𝕜
      rw [h2', hB φ hφ]
    have hmem := (mem_divdivMax_domain_iff hΩ).2 ⟨0, key⟩
    exact LinearPMap.mem_ker_iff.2 ⟨⟨B, hmem⟩, rfl,
      (hessOp 3).adjoint_minimalVia_apply_eq _ _ (denseVia_id hΩ) (dense_hessMin_domain hΩ) _ key⟩

end Feec.Models.BoundedDomain
