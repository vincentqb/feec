module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The isometry defect `1 - ι* ι` of a bounded operator

For a bounded operator `ι : X → E` of Hilbert spaces, the norms of the defect `1 - ι* ι`
([HolstStern2012], §3.3) are bounded through `⟪(1 - ι* ι) v, w⟫ = ⟪v, w⟫ - ⟪ι v, ι w⟫`.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {X E : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [CompleteSpace X] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  (ι : X →L[𝕜] E)

theorem inner_one_sub_adjoint_comp_self_apply (v w : X) :
    ⟪(1 - adjoint ι ∘L ι) v, w⟫_𝕜 = ⟪v, w⟫_𝕜 - ⟪ι v, ι w⟫_𝕜 := by
  change ⟪v - adjoint ι (ι v), w⟫_𝕜 = _
  rw [inner_sub_left, adjoint_inner_left]

theorem norm_one_sub_adjoint_comp_self_apply_le {v : X} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ w, ‖⟪v, w⟫_𝕜 - ⟪ι v, ι w⟫_𝕜‖ ≤ B * ‖w‖) : ‖(1 - adjoint ι ∘L ι) v‖ ≤ B := by
  set z := (1 - adjoint ι ∘L ι) v
  have h1 : ‖z‖ ^ 2 ≤ B * ‖z‖ := by
    have := h z
    rwa [← inner_one_sub_adjoint_comp_self_apply, inner_self_eq_norm_sq_to_K, norm_pow,
      RCLike.norm_ofReal, abs_norm] at this
  rcases (norm_nonneg z).eq_or_lt with hz | hz
  · rw [← hz]; exact hB
  · nlinarith

theorem opNorm_one_sub_adjoint_comp_self_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v w, ‖⟪v, w⟫_𝕜 - ⟪ι v, ι w⟫_𝕜‖ ≤ c * (‖v‖ * ‖w‖)) : ‖1 - adjoint ι ∘L ι‖ ≤ c :=
  opNorm_le_bound _ hc fun v =>
    norm_one_sub_adjoint_comp_self_apply_le ι (by positivity) fun w =>
      (h v w).trans_eq (by ring)

theorem le_opNorm_one_sub_adjoint_comp_self {v : X} (hv : v ≠ 0) {c : ℝ}
    (h : c * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 - ‖ι v‖ ^ 2) : c ≤ ‖1 - adjoint ι ∘L ι‖ := by
  have h1 : ‖v‖ ^ 2 - ‖ι v‖ ^ 2 = RCLike.re ⟪(1 - adjoint ι ∘L ι) v, v⟫_𝕜 := by
    rw [inner_one_sub_adjoint_comp_self_apply, map_sub, inner_self_eq_norm_sq,
      inner_self_eq_norm_sq]
  have h2 : RCLike.re ⟪(1 - adjoint ι ∘L ι) v, v⟫_𝕜 ≤ ‖1 - adjoint ι ∘L ι‖ * ‖v‖ ^ 2 :=
    (re_inner_le_norm _ _).trans (by
      rw [sq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right ((1 - adjoint ι ∘L ι).le_opNorm v) (norm_nonneg v))
  exact le_of_mul_le_mul_right (by linarith) (pow_pos (norm_pos_iff.2 hv) 2)

end ContinuousLinearMap
