module

public import Feec.HilbertComplex.Basic

/-!
# The dual Hilbert complex

The adjoints `(d j i)† : W i →ₗ.[𝕜] W j` of a Hilbert complex on `c` form a Hilbert complex on
the opposite shape `c.symm`, on the same spaces: no index transport is needed. By von Neumann's
`T†† = T` for closed densely defined `T`, dualizing twice gives back the complex.

## Main definitions

* `Feec.HilbertComplex.dual`: the dual complex, `H.dual.d i j = (H.d j i)†`.

## Main results

* `LinearPMap.adjoint_zero`: `0† = 0`.
* `HilbertComplex.dual_dual`: `H.dual.dual = H`.
* `HilbertComplex.cycles_dual`: the cycles of the dual are the kernels of the adjoints.

## References

* [QuennevilleBelair2015], §4.2 (dual complex, `V*_k`)
* [AFW2010], §3.1.2 (dual complex); [BruningLesch1992], Lemma 2.1
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The adjoint of the zero operator (domain `⊤`) is zero (domain `⊤`). -/
theorem adjoint_zero : (0 : E →ₗ.[𝕜] F)† = 0 := by
  have hD : Dense (((0 : E →ₗ.[𝕜] F)).domain : Set E) := by simp [zero_domain]
  have hdom : (0 : E →ₗ.[𝕜] F)†.domain = ⊤ := by
    rw [eq_top_iff]
    intro y _
    refine mem_adjoint_domain_of_exists y ⟨0, fun x => ?_⟩
    rw [inner_zero_left, apply_eq_zero_of_eq_zero rfl x, inner_zero_right]
  refine LinearPMap.ext hdom fun y hy _ => ?_
  rw [adjoint_apply_eq hD ⟨y, hy⟩ (x₀ := 0) fun x => by
    rw [inner_zero_left, apply_eq_zero_of_eq_zero rfl x, inner_zero_right]]
  rfl

/-- The adjoint of a partial map equal to `0` vanishes on its domain. -/
theorem adjoint_apply_eq_zero_of_eq_zero {T : E →ₗ.[𝕜] F} (h : T = 0) (y : T†.domain) :
    T† y = 0 := by
  subst h; exact apply_eq_zero_of_eq_zero adjoint_zero y

end LinearPMap

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

/-- The dual complex on `c.symm`: `d* i j = (d j i)†`. Thesis: §4.2 -/
def dual : HilbertComplex 𝕜 c.symm W where
  d i j := (H.d j i)†
  shape i j h := by
    change ¬ c.Rel j i at h
    rw [H.shape j i h, adjoint_zero]
  dense i j := H.dense_adjoint_domain j i
  closed i j := adjoint_isClosed (H.dense j i)
  mapsTo i j k x := H.adjoint_mapsTo k j i x
  d_comp_d i j k x := H.adjoint_comp_eq_zero k j i x

@[simp] theorem dual_d (i j : ι) : H.dual.d i j = (H.d j i)† := rfl

/-- `H** = H` (von Neumann's `T†† = T` for each differential). -/
theorem dual_dual : H.dual.dual = H := by
  cases H with
  | mk d shape dense closed mapsTo d_comp_d =>
    have hd : (fun i j => (d i j)††) = d := by
      funext i j; exact LinearPMap.adjoint_adjoint _ (dense i j) (closed i j)
    change HilbertComplex.mk (fun i j => (d i j)††) _ _ _ _ _ = _
    congr

theorem cycles_dual (i : ι) : H.dual.cycles i = ((H.d (c.prev i) i)†).ker := by
  rfl

theorem boundaries_dual (i : ι) :
    H.dual.boundaries i = LinearMap.range ((H.d i (c.next i))†).toFun := by
  rfl

end Feec.HilbertComplex
