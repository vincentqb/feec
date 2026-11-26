module

public import Feec.HilbertComplex.Basic

/-!
# The dual Hilbert complex

The adjoints `(d j i)†` of a Hilbert complex on `c` form a Hilbert complex on `c.symm`, on the same
spaces, and dualizing twice gives back the complex.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

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

theorem adjoint_apply_eq_zero_of_eq_zero {T : E →ₗ.[𝕜] F} (h : T = 0) (y : T†.domain) :
    T† y = 0 := by
  subst h; exact apply_eq_zero_of_eq_zero adjoint_zero y

end LinearPMap

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

/-- The dual complex on `c.symm`: `d* i j = (d j i)†`. [QuennevilleBelair2015], §4.2;
[BruningLesch1992], Lemma 2.1; [AFW2010], §3.1.2 -/
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

/-- `H** = H`. -/
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

theorem dual_closedRangeAt_of_forall_not_rel {i : ι} (h : ∀ j, ¬ c.Rel i j) :
    H.dual.ClosedRangeAt i := by
  rw [ClosedRangeAt, boundaries_dual, H.shape _ _ (h _), LinearPMap.adjoint_zero]
  convert (isClosed_singleton (x := (0 : W i))) using 1
  ext y; constructor
  · rintro ⟨x, rfl⟩; rfl
  · rintro rfl; exact ⟨0, rfl⟩

end Feec.HilbertComplex
