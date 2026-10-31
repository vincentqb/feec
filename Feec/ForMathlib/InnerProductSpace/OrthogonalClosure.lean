module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Bounded operators and the closures `Aᗮᗮ` of subspaces

In a Hilbert space `Aᗮᗮ` is the closure of a subspace `A`, so a bounded operator `S` carrying `A`
into `B` carries `Aᗮᗮ` into `Bᗮᗮ`; this is proved through the adjoint, `⟪w, S x⟫ = ⟪S* w, x⟫`.

## Main results

* `ContinuousLinearMap.map_mem_orthogonal_orthogonal`: `S A ⊆ B` implies `S Aᗮᗮ ⊆ Bᗮᗮ`.
* `ContinuousLinearMap.starProjection_orthogonal_apply_starProjection_orthogonal`:
  `P_{Bᗮ} S P_{Aᗮ} = P_{Bᗮ} S` when `S A ⊆ B`.
* `ContinuousLinearMap.apply_eq_zero_of_mem_orthogonal_orthogonal`: `S` vanishing on `A` vanishes
  on `Aᗮᗮ`.

## References

* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §1.3 (orthogonality relations, `Mᗮᗮ = cl M`)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
  (S : E →L[𝕜] F)

/-- **A bounded operator carrying `A` into `B` carries `Aᗮᗮ = cl A` into `Bᗮᗮ`**: for `w ∈ Bᗮ`,
`⟪w, S x⟫ = ⟪S* w, x⟫` and `S* w ∈ Aᗮ`. -/
theorem map_mem_orthogonal_orthogonal {A : Submodule 𝕜 E} {B : Submodule 𝕜 F}
    (h : ∀ a ∈ A, S a ∈ B) {x : E} (hx : x ∈ Aᗮᗮ) : S x ∈ Bᗮᗮ :=
  (Submodule.mem_orthogonal _ _).2 fun w hw => by
    rw [← adjoint_inner_left]
    exact Submodule.inner_right_of_mem_orthogonal ((Submodule.mem_orthogonal _ _).2 fun a ha => by
      rw [adjoint_inner_right]
      exact Submodule.inner_right_of_mem_orthogonal (h a ha) hw) hx

/-- **`P_{Bᗮ} S P_{Aᗮ} = P_{Bᗮ} S`** for a bounded operator `S` carrying `A` into `B`. -/
theorem starProjection_orthogonal_apply_starProjection_orthogonal {A : Submodule 𝕜 E}
    {B : Submodule 𝕜 F} (h : ∀ a ∈ A, S a ∈ B) (x : E) :
    Bᗮ.starProjection (S (Aᗮ.starProjection x)) = Bᗮ.starProjection (S x) := by
  have hc := S.map_mem_orthogonal_orthogonal h (Aᗮ.sub_starProjection_mem_orthogonal x)
  rw [← sub_eq_zero, ← map_sub, ← map_sub, ← neg_sub, map_neg, map_neg, neg_eq_zero,
    Bᗮ.starProjection_apply_eq_zero_iff]
  exact hc

/-- **A bounded operator vanishing on `A` vanishes on `Aᗮᗮ = cl A`.** -/
theorem apply_eq_zero_of_mem_orthogonal_orthogonal {A : Submodule 𝕜 E}
    (h : ∀ a ∈ A, S a = 0) {x : E} (hx : x ∈ Aᗮᗮ) : S x = 0 := by
  have := S.map_mem_orthogonal_orthogonal (B := ⊥) (fun a ha => (h a ha).symm ▸ zero_mem _) hx
  rwa [Submodule.bot_orthogonal_eq_top, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at this

end ContinuousLinearMap
