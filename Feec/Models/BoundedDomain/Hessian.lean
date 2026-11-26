module

public import Feec.Models.BoundedDomain.SymCurl

/-!
# The minimal Hessian and the weak double divergence on a bounded domain

On an open `Ω ⊆ ℝ³`, the minimal Hessian `grad grad : H̊²(Ω) → L²(Ω; 𝕜³ˣ³)` (`hessMin`) and its
adjoint, the weak double divergence on `H(div div, Ω)` (`divdivMax`).
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ContDiff ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology Feec.Domain

namespace Feec.Models.BoundedDomain

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Set R3}

theorem denseVia_id (hΩ : IsOpen Ω) {κ : Type*} [Fintype κ] :
    ConstCoeffOp.DenseVia (LinearIsometry.id : L2F 𝕜 Ω κ →ₗᵢ[𝕜] L2F 𝕜 Ω κ) :=
  ConstCoeffOp.denseVia_of_surjective hΩ _ fun y => ⟨y, rfl⟩

variable (𝕜) in
/-- The minimal Hessian `grad grad : H̊²(Ω) → L²(Ω; 𝕜³ˣ³)`, the closure on `C_c^∞(Ω)`. -/
def hessMin (_hΩ : IsOpen Ω) : L2 𝕜 Ω →ₗ.[𝕜] L2F 𝕜 Ω Ix :=
  (hessOp 3).minimalVia (L2.toL2F 𝕜 Ω) LinearIsometry.id

theorem isClosed_hessMin (hΩ : IsOpen Ω) : (hessMin 𝕜 hΩ).IsClosed :=
  (hessOp 3).isClosed_minimalVia _ _ (denseVia_id hΩ)

theorem dense_hessMin_domain (hΩ : IsOpen Ω) : Dense ((hessMin 𝕜 hΩ).domain : Set (L2 𝕜 Ω)) :=
  (hessOp 3).dense_minimalVia_domain_of _ _ (denseVia_id hΩ) (denseVia_scalar hΩ)
    fun _ hφ _ _ => ⟨testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ), rfl⟩

variable (𝕜) in
/-- The weak double divergence on `H(div div, Ω)`, the adjoint of `hessMin`. -/
abbrev divdivMax (hΩ : IsOpen Ω) : L2F 𝕜 Ω Ix →ₗ.[𝕜] L2 𝕜 Ω := (hessMin 𝕜 hΩ)†

theorem mem_divdivMax_domain_iff (hΩ : IsOpen Ω) {B : L2F 𝕜 Ω Ix} :
    B ∈ (divdivMax 𝕜 hΩ).domain ↔ ∃ D : L2 𝕜 Ω,
      ∀ p ∈ (hessOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia (L2.toL2F 𝕜 Ω) LinearIsometry.id,
        ⟪D, p.1⟫_𝕜 = ⟪B, p.2⟫_𝕜 :=
  (hessOp 3).mem_adjoint_minimalVia_domain_iff _ _ (denseVia_id hΩ) (dense_hessMin_domain hΩ)

/-- `B ∈ ker divdivMax` iff `B ⊥ ∇²φ` for every test function `φ`. -/
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
