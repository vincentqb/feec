module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Feec foundation §A: unbounded operators

Skew-adjoint and skew-symmetric (possibly unbounded) operators, restriction to an invariant
subspace, and (4.1a) `(range T)ᗮ = ker T†`.

## References

* [QuennevilleBelair2015], §4.1 (unbounded operators, adjoints, (4.1a)), Thm 4.4 (the operator `L̃`)
* [Pazy1983], §1.10 (Stone's theorem)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open Set

namespace Feec

/-! ## §A. Unbounded operators -/

section Operators
open LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Skew-adjoint (possibly unbounded) operator: `A† = -A` (equal domains).
See [QuennevilleBelair2015, §4.1]; cf. [Pazy1983, §1.10] (Stone's theorem). -/
def IsSkewAdjoint [CompleteSpace E] (A : E →ₗ.[ℝ] E) : Prop := A† = -A

/-- Skew-symmetry on the domain: `⟪A x, y⟫ = -⟪x, A y⟫`. (Weaker than skew-adjoint;
enough for all energy/uniqueness/constraint-propagation arguments.)
See [QuennevilleBelair2015, §4.1] (skew-symmetric operators). -/
def IsSkewSymm (A : E →ₗ.[ℝ] E) : Prop :=
  ∀ x y : A.domain, ⟪A x, (y : E)⟫ = -⟪(x : E), A y⟫

/-- Restriction of `L` to an invariant subspace `K`, as an operator `K → K`
(domain `D(L) ∩ K`). Used by Thm 4.4. See [QuennevilleBelair2015, Thm 4.4] (the operator `L̃`). -/
def restrictTo (L : E →ₗ.[ℝ] E) (K : Submodule ℝ E)
    (hinv : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) : K →ₗ.[ℝ] K where
  domain := L.domain.comap K.subtype
  toFun :=
    { toFun := fun x => ⟨L ⟨(x : K), x.2⟩, hinv ⟨_, x.2⟩ (x : K).2⟩
      map_add' := fun x y => by ext; simp [← LinearPMap.map_add]; rfl
      map_smul' := fun c x => by ext; simp [← LinearPMap.map_smul]; rfl }

/-- (4.1a) `(range T)ᗮ = ker T†` for densely defined `T` (no closedness needed).
See [QuennevilleBelair2015, §4.1, (4.1a)] (stated there for closed `T`). -/
theorem orth_range_eq_ker_adjoint {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) :
    (LinearMap.range T.toFun)ᗮ = T†.ker := by
  ext y
  constructor
  · intro hy
    have key : ∀ x : T.domain, ⟪(0 : E), (x : E)⟫ = ⟪y, T x⟫ := fun x => by
      have := (Submodule.mem_orthogonal _ _).1 hy (T x) ⟨x, rfl⟩
      rw [inner_zero_left, real_inner_comm, this]
    have hmem : y ∈ T†.domain := mem_adjoint_domain_of_exists y ⟨0, key⟩
    rw [LinearPMap.mem_ker_iff]
    exact ⟨⟨y, hmem⟩, rfl, adjoint_apply_eq hT ⟨y, hmem⟩ key⟩
  · intro hy
    rw [LinearPMap.mem_ker_iff] at hy
    obtain ⟨y', rfl, hy0⟩ := hy
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    have := (adjoint_isFormalAdjoint hT) y' x
    rw [hy0] at this
    simpa [real_inner_comm] using this.symm

/-- Skew-adjoint ⇒ skew-symmetric. See [QuennevilleBelair2015, §4.1]. -/
theorem IsSkewAdjoint.isSkewSymm [CompleteSpace E] {L : E →ₗ.[ℝ] E}
    (hD : Dense (L.domain : Set E)) (hL : IsSkewAdjoint L) : IsSkewSymm L := by
  intro x y
  have hle : -L ≤ L† := hL ▸ le_rfl
  have hx : (x : E) ∈ L†.domain := hle.1 x.2
  have h1 := adjoint_isFormalAdjoint hD ⟨x, hx⟩ y
  have h2 : L† ⟨x, hx⟩ = -L x := (hle.2 (x := x) (y := ⟨x, hx⟩) rfl).symm
  rw [h2, inner_neg_left] at h1
  linarith

end Operators

end Feec
