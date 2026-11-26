module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The Moore–Penrose inverse of a bounded operator with closed range

For a bounded operator `S` between Hilbert spaces with closed range, the Moore–Penrose inverse
`S† = (S|_{N(S)ᗮ})⁻¹ P_{R(S)}` ([ArnoldHu2021], (29)) satisfies `S S† = P_{R(S)}`,
`S† S = P_{N(S)ᗮ}` and the four Penrose equations ([Penrose1955]).

## References

* [R. Penrose, *A generalized inverse for matrices*][Penrose1955]
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open Submodule

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (S : E →L[𝕜] F)

/-- A bounded operator restricted to the orthogonal complement of its kernel, onto its range. -/
def restrictKerOrthogonal : S.kerᗮ →L[𝕜] S.range :=
  (S ∘L S.kerᗮ.subtypeL).codRestrict (S.range) fun x => ⟨x, rfl⟩

variable {S} in
theorem coe_restrictKerOrthogonal_apply (x : S.kerᗮ) :
    (S.restrictKerOrthogonal x : F) = S x := rfl

theorem ker_restrictKerOrthogonal : S.restrictKerOrthogonal.ker = ⊥ :=
  LinearMap.ker_eq_bot'.2 fun x hx => Subtype.ext <| (Submodule.mem_bot 𝕜).1 <|
    S.ker.inf_orthogonal_eq_bot ▸ (⟨congrArg Subtype.val hx, x.2⟩ : (x : E) ∈ S.ker ⊓ S.kerᗮ)

theorem isClosed_range_of_hasOrthogonalProjection [S.range.HasOrthogonalProjection] :
    IsClosed (S.range : Set F) :=
  S.range.orthogonal_orthogonal ▸ S.rangeᗮ.isClosed_orthogonal

variable [CompleteSpace E]

theorem apply_starProjection_orthogonal_ker (x : E) :
    S (S.kerᗮ.starProjection x) = S x := by
  have h0 : S (S.ker.starProjection x) = 0 := S.ker.starProjection_apply_mem x
  conv_rhs => rw [← S.ker.starProjection_add_starProjection_orthogonal x, map_add, h0, zero_add]

theorem range_restrictKerOrthogonal : S.restrictKerOrthogonal.range = ⊤ :=
  LinearMap.range_eq_top.2 fun ⟨_, x, hx⟩ =>
    ⟨⟨_, S.kerᗮ.starProjection_apply_mem x⟩,
      Subtype.ext ((S.apply_starProjection_orthogonal_ker x).trans hx)⟩

variable [CompleteSpace F]

/-- The Moore–Penrose inverse `S† = (S|_{N(S)ᗮ})⁻¹ P_{R(S)}`, and `0` if the range is not closed. -/
def moorePenrose : F →L[𝕜] E :=
  open scoped Classical in
  if h : IsClosed (S.range : Set F) then
    haveI := h.completeSpace_coe
    S.kerᗮ.subtypeL ∘L
      ((ContinuousLinearEquiv.ofBijective S.restrictKerOrthogonal S.ker_restrictKerOrthogonal
        S.range_restrictKerOrthogonal).symm : S.range →L[𝕜] S.kerᗮ) ∘L
      S.range.orthogonalProjectionOnto
  else 0

variable {S}

theorem moorePenrose_apply_mem (y : F) : S.moorePenrose y ∈ S.kerᗮ := by
  unfold moorePenrose
  split_ifs
  · exact Subtype.coe_prop _
  · exact zero_mem _

theorem moorePenrose_apply_eq_zero {y : F} (hy : y ∈ S.rangeᗮ) :
    S.moorePenrose y = 0 := by
  unfold moorePenrose
  split_ifs with h
  · have := h.completeSpace_coe
    simp [S.range.orthogonalProjectionOnto_eq_zero_iff.2 hy]
  · rfl

variable [S.range.HasOrthogonalProjection]

theorem moorePenrose_apply_of_mem {x : E} (hx : x ∈ S.kerᗮ) :
    S.moorePenrose (S x) = x := by
  unfold moorePenrose
  split_ifs with h
  swap; · exact absurd S.isClosed_range_of_hasOrthogonalProjection h
  have := h.completeSpace_coe
  have e : S.range.orthogonalProjectionOnto (S x) =
      S.restrictKerOrthogonal ⟨x, hx⟩ :=
    S.range.orthogonalProjectionOnto_mem_subspace_eq_self ⟨S x, x, rfl⟩
  simp only [coe_comp, Function.comp_apply, e,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.ofBijective_symm_apply_apply]
  rfl

theorem apply_moorePenrose (y : F) : S (S.moorePenrose y) = S.range.starProjection y := by
  unfold moorePenrose
  split_ifs with h
  swap; · exact absurd S.isClosed_range_of_hasOrthogonalProjection h
  have := h.completeSpace_coe
  have := ContinuousLinearEquiv.ofBijective_apply_symm_apply S.restrictKerOrthogonal
    S.ker_restrictKerOrthogonal S.range_restrictKerOrthogonal
    (S.range.orthogonalProjectionOnto y)
  exact congrArg Subtype.val this

theorem moorePenrose_apply (x : E) :
    S.moorePenrose (S x) = S.kerᗮ.starProjection x := by
  rw [← S.apply_starProjection_orthogonal_ker x,
    moorePenrose_apply_of_mem (S.kerᗮ.starProjection_apply_mem x)]

theorem sub_moorePenrose_apply (x : E) :
    x - S.moorePenrose (S x) = S.ker.starProjection x := by
  rw [moorePenrose_apply, sub_eq_iff_eq_add', add_comm,
    S.ker.starProjection_add_starProjection_orthogonal]

theorem apply_moorePenrose_of_surjective (hS : Function.Surjective S) (y : F) :
    S (S.moorePenrose y) = y := by
  rw [apply_moorePenrose, S.range.starProjection_eq_self_iff]
  exact hS y

theorem moorePenrose_apply_of_injective (hS : Function.Injective S) (x : E) :
    S.moorePenrose (S x) = x :=
  moorePenrose_apply_of_mem (by
    rw [show S.ker = ⊥ from LinearMap.ker_eq_bot.2 hS, Submodule.bot_orthogonal_eq_top]
    trivial)

theorem comp_moorePenrose_comp : S ∘L S.moorePenrose ∘L S = S := by
  ext x
  exact (apply_moorePenrose (S x)).trans (S.range.starProjection_eq_self_iff.2 ⟨x, rfl⟩)

theorem moorePenrose_comp_comp_moorePenrose :
    S.moorePenrose ∘L S ∘L S.moorePenrose = S.moorePenrose := by
  ext y
  simp [moorePenrose_apply, S.kerᗮ.starProjection_eq_self_iff.2
    (moorePenrose_apply_mem y)]

theorem comp_moorePenrose : S ∘L S.moorePenrose = S.range.starProjection :=
  ext apply_moorePenrose

theorem moorePenrose_comp : S.moorePenrose ∘L S = S.kerᗮ.starProjection :=
  ext moorePenrose_apply

theorem isSelfAdjoint_comp_moorePenrose : IsSelfAdjoint (S ∘L S.moorePenrose) :=
  comp_moorePenrose (S := S) ▸ isSelfAdjoint_starProjection _

theorem isSelfAdjoint_moorePenrose_comp : IsSelfAdjoint (S.moorePenrose ∘L S) :=
  moorePenrose_comp (S := S) ▸ isSelfAdjoint_starProjection _

end ContinuousLinearMap
