module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Diagonal operators on an orthogonal sum

The diagonal operator `(xᵢ) ↦ (σᵢ xᵢ)` of bounded operators `σᵢ` on the orthogonal sum `⊕₂ Wᵢ`;
it is dissipative when every `σᵢ` is.
-/

open scoped InnerProductSpace

@[expose] public noncomputable section

namespace PiLp

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]

/-- The diagonal operator `(xᵢ) ↦ (σᵢ xᵢ)` on `⊕₂ Wᵢ`. -/
def diagOp (σ : ∀ i, W i →L[𝕜] W i) : PiLp 2 W →L[𝕜] PiLp 2 W :=
  (PiLp.continuousLinearEquiv 2 𝕜 W).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun i => σ i ∘L ContinuousLinearMap.proj i) ∘L
      (PiLp.continuousLinearEquiv 2 𝕜 W).toContinuousLinearMap

@[simp] theorem diagOp_apply (σ : ∀ i, W i →L[𝕜] W i) (x : PiLp 2 W) (i : ι) :
    diagOp σ x i = σ i (x i) := rfl

theorem re_inner_diagOp_le [Fintype ι] {σ : ∀ i, W i →L[𝕜] W i} (hσ : ∀ i y, RCLike.re ⟪σ i y, y⟫_𝕜 ≤ 0)
    (x : PiLp 2 W) : RCLike.re ⟪diagOp σ x, x⟫_𝕜 ≤ 0 := by
  rw [PiLp.inner_apply, map_sum]
  exact Finset.sum_nonpos fun i _ => hσ i (x i)

end PiLp
