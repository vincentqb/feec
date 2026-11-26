module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Orthogonal projections onto the image of an isometry

For a linear isometry `ι : X → E` of Hilbert spaces, `‖y - ι ι* y‖ ≤ ‖y - ι v‖` for every `v`, and
`‖ι ι* y‖ ≤ ‖y‖`.
-/

open scoped InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {X E : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [CompleteSpace X] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {ι : X →L[𝕜] E}

theorem norm_sub_apply_adjoint_apply_le (hι : ∀ v, ‖ι v‖ = ‖v‖) (y : E) (v : X) :
    ‖y - ι (adjoint ι y)‖ ≤ ‖y - ι v‖ := by
  have hι' := (norm_map_iff_adjoint_comp_self ι).1 hι
  have h0 : ⟪y - ι (adjoint ι y), ι (adjoint ι y - v)⟫_𝕜 = 0 := by
    rw [← adjoint_inner_left, _root_.map_sub, ← comp_apply, hι', one_apply_eq_self, sub_self,
      inner_zero_left]
  have e : y - ι v = (y - ι (adjoint ι y)) + ι (adjoint ι y - v) := by
    rw [_root_.map_sub]; abel
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [← e] at hp
  nlinarith [norm_nonneg (y - ι v), norm_nonneg (y - ι (adjoint ι y)),
    mul_self_nonneg ‖ι (adjoint ι y - v)‖]

theorem norm_apply_adjoint_apply_le (hι : ∀ v, ‖ι v‖ = ‖v‖) (y : E) :
    ‖ι (adjoint ι y)‖ ≤ ‖y‖ := by
  rw [hι]
  refine ((adjoint ι).le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _) ?_)
  rw [LinearIsometryEquiv.norm_map]
  exact opNorm_le_bound _ zero_le_one fun v => by rw [hι, one_mul]

end ContinuousLinearMap
