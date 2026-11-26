module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Bounded operators and the closures `Aᗮᗮ` of subspaces

A bounded operator between Hilbert spaces carrying a subspace `A` into `B` carries `Aᗮᗮ` into
`Bᗮᗮ`, and `P_{Bᗮ} S P_{Aᗮ} = P_{Bᗮ} S`.
-/

@[expose] public section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
  (S : E →L[𝕜] F)

theorem map_mem_orthogonal_orthogonal {A : Submodule 𝕜 E} {B : Submodule 𝕜 F}
    (h : ∀ a ∈ A, S a ∈ B) {x : E} (hx : x ∈ Aᗮᗮ) : S x ∈ Bᗮᗮ :=
  (Submodule.mem_orthogonal _ _).2 fun w hw => by
    rw [← adjoint_inner_left]
    exact Submodule.inner_right_of_mem_orthogonal ((Submodule.mem_orthogonal _ _).2 fun a ha => by
      rw [adjoint_inner_right]
      exact Submodule.inner_right_of_mem_orthogonal (h a ha) hw) hx

theorem starProjection_orthogonal_apply_starProjection_orthogonal {A : Submodule 𝕜 E}
    {B : Submodule 𝕜 F} (h : ∀ a ∈ A, S a ∈ B) (x : E) :
    Bᗮ.starProjection (S (Aᗮ.starProjection x)) = Bᗮ.starProjection (S x) := by
  have hc := S.map_mem_orthogonal_orthogonal h (Aᗮ.sub_starProjection_mem_orthogonal x)
  rw [← sub_eq_zero, ← map_sub, ← map_sub, ← neg_sub, map_neg, map_neg, neg_eq_zero,
    Bᗮ.starProjection_apply_eq_zero_iff]
  exact hc

theorem apply_eq_zero_of_mem_orthogonal_orthogonal {A : Submodule 𝕜 E}
    (h : ∀ a ∈ A, S a = 0) {x : E} (hx : x ∈ Aᗮᗮ) : S x = 0 := by
  have := S.map_mem_orthogonal_orthogonal (B := ⊥) (fun a ha => (h a ha).symm ▸ zero_mem _) hx
  rwa [Submodule.bot_orthogonal_eq_top, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at this

end ContinuousLinearMap
