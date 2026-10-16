module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Feec foundation §A: unbounded operators

Skew-adjoint and skew-symmetric (possibly unbounded) operators, closed kernels, reducing
subspaces, restriction to an invariant subspace, and (4.1a) `(range T)ᗮ = ker T†`.

## Main results

* `isClosed_ker`: the kernel of a closed operator is closed.
* `IsSkewAdjoint.dense_domain`: a skew-adjoint operator is densely defined, so density is never
  a separate hypothesis; `IsSkewAdjoint.isSkewSymmetric`.
* `IsSkewSymm.inner_self`: `⟪L x, x⟫ = 0`.
* `IsReducingPair` / `IsReducing`: `P_K D(T) ⊆ D(T)` and `T P_K = P_L T`, with
  `IsReducingPair.mapsTo` and `IsReducingPair.map_orthogonal_mem`.

## References

* [QuennevilleBelair2015], §4.1 (unbounded operators, adjoints, (4.1a)), Thm 4.4 (the operator `L̃`)
* [Pazy1983], §1.10 (Stone's theorem)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open Set

namespace Feec

/-! ## §A. Unbounded operators -/

/-! ## Closed kernels -/

section Kernel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `N(T) = {x | (x, 0) ∈ Γ(T)}` (auxiliary, Thesis §4.1). -/
theorem ker_eq_preimage_graph (T : E →ₗ.[ℝ] F) :
    (T.ker : Set E) = (fun x => (x, (0 : F))) ⁻¹' (T.graph : Set (E × F)) := by
  ext x
  simp only [SetLike.mem_coe, mem_preimage, LinearPMap.mem_ker_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨y, rfl, hy⟩; exact ⟨y, rfl, hy⟩
  · rintro ⟨y, hy, hy0⟩; exact ⟨y, hy.symm, hy0⟩

/-- The kernel of a **closed** unbounded operator is closed.

Thesis §4.2 (`Zᵏ` closed, used for `W = Z ⊕ Zᗮ`) and §4.3 (constraint propagation into `ker M`).
Thesis gap: the thesis (§4.3) asserts this for every "not-necessarily-bounded linear operator";
closedness of `T` is needed (see `exists_not_isClosed_ker`).

See [QuennevilleBelair2015, §4.2, §4.3]. -/
theorem isClosed_ker {T : E →ₗ.[ℝ] F} (hc : T.IsClosed) : IsClosed (T.ker : Set E) := by
  rw [ker_eq_preimage_graph]
  exact hc.preimage (continuous_id.prodMk continuous_const)

end Kernel


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

/-- A skew-adjoint operator (`A† = -A`) is densely defined. As for Mathlib's
`IsSelfAdjoint.dense_domain`, this is not part of the definition: the adjoint of a non-densely
defined operator is `0` on its domain, which forces `A = 0` on `D(A)`, hence `D(A) = E`.
So density is never a separate hypothesis next to skew-adjointness. -/
theorem IsSkewAdjoint.dense_domain [CompleteSpace E] {A : E →ₗ.[ℝ] E} (hA : IsSkewAdjoint A) :
    Dense (A.domain : Set E) := by
  by_contra h
  have hle : A† ≤ -A := hA ▸ le_rfl
  have hzero : ∀ x : A.domain, A x = 0 := by
    intro x
    have hx : (x : E) ∈ A†.domain := by rw [hA]; exact x.2
    have h2 : A† ⟨x, hx⟩ = (-A) x := hle.2 rfl
    rw [adjoint_apply_of_not_dense h, LinearPMap.neg_apply] at h2
    exact neg_eq_zero.1 h2.symm
  have htop : A.domain = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    have hy : y ∈ A†.domain := by
      rw [mem_adjoint_domain_iff]
      have : (innerₛₗ ℝ y).comp A.toFun = 0 := by
        ext x; simp [hzero x]
      rw [this]; exact continuous_zero
    rw [hA] at hy; exact hy
  exact h (by rw [htop]; simp [dense_univ])

/-- Skew-adjoint ⇒ skew-symmetric (density of the domain is automatic,
`IsSkewAdjoint.dense_domain`). See [QuennevilleBelair2015, §4.1]. -/
theorem IsSkewAdjoint.isSkewSymmetric [CompleteSpace E] {L : E →ₗ.[ℝ] E}
    (hL : IsSkewAdjoint L) : IsSkewSymm L := by
  intro x y
  have hle : -L ≤ L† := hL ▸ le_rfl
  have hx : (x : E) ∈ L†.domain := hle.1 x.2
  have h1 := adjoint_isFormalAdjoint hL.dense_domain ⟨x, hx⟩ y
  have h2 : L† ⟨x, hx⟩ = -L x := (hle.2 (x := x) (y := ⟨x, hx⟩) rfl).symm
  rw [h2, inner_neg_left] at h1
  linarith

/-- Skew-adjoint ⇒ skew-symmetric, with a (redundant) density hypothesis; see
`IsSkewAdjoint.isSkewSymmetric`. See [QuennevilleBelair2015, §4.1]. -/
theorem IsSkewAdjoint.isSkewSymm [CompleteSpace E] {L : E →ₗ.[ℝ] E}
    (_hD : Dense (L.domain : Set E)) (hL : IsSkewAdjoint L) : IsSkewSymm L :=
  hL.isSkewSymmetric

/-- Skew-symmetry gives `⟪L x, x⟫ = 0` (the energy identity). -/
theorem IsSkewSymm.inner_self {L : E →ₗ.[ℝ] E} (hL : IsSkewSymm L) (x : L.domain) :
    ⟪L x, (x : E)⟫ = 0 := by
  have h := hL x x
  have h2 : ⟪(x : E), L x⟫ = ⟪L x, (x : E)⟫ := real_inner_comm _ _
  linarith

/-! ### Reducing subspaces -/

/-- `T : E → F` is *reduced* by the pair `(K, L)` of closed subspaces: the projection `P_K`
preserves `D(T)` and `T P_K = P_L T` on `D(T)`. For `T : E → E` and `K = L` this is the usual
notion of a reducing subspace (`IsReducing`); it packages hypotheses (i) and (iii) of
[QuennevilleBelair2015, Thm 4.4] (equivalent to them for skew-adjoint operators,
`IsSkewAdjoint.isReducing_iff`). -/
structure IsReducingPair {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →ₗ.[ℝ] F) (K : Submodule ℝ E) (L : Submodule ℝ F)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] : Prop where
  /-- `P_K D(T) ⊆ D(T)`. -/
  proj_mem : ∀ x : T.domain, K.starProjection (x : E) ∈ T.domain
  /-- `T P_K = P_L T` on `D(T)`. -/
  comm : ∀ x : T.domain, T ⟨_, proj_mem x⟩ = L.starProjection (T x)

/-- `K` reduces `A : E → E`: `P_K D(A) ⊆ D(A)` and `A P_K = P_K A` on `D(A)`. -/
abbrev IsReducing (A : E →ₗ.[ℝ] E) (K : Submodule ℝ E) [K.HasOrthogonalProjection] : Prop :=
  IsReducingPair A K K

section IsReducingPair

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {T : E →ₗ.[ℝ] F} {K : Submodule ℝ E} {L : Submodule ℝ F}
  [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]

/-- A reducing pair maps `D(T) ∩ K` into `L` (hypothesis (iii) of Thm 4.4). -/
theorem IsReducingPair.mapsTo (h : IsReducingPair T K L) (x : T.domain) (hx : (x : E) ∈ K) :
    T x ∈ L := by
  have hx' : (⟨K.starProjection (x : E), h.proj_mem x⟩ : T.domain) = x :=
    Subtype.ext ((K.starProjection_eq_self_iff).2 hx)
  have e := h.comm x
  rw [hx'] at e
  rw [e]
  exact L.starProjection_apply_mem _

/-- A reducing pair maps `D(T) ∩ Kᗮ` into `Lᗮ`. -/
theorem IsReducingPair.map_orthogonal_mem (h : IsReducingPair T K L) (z : T.domain)
    (hz : (z : E) ∈ Kᗮ) : T z ∈ Lᗮ := by
  have h0 : (⟨K.starProjection (z : E), h.proj_mem z⟩ : T.domain) = 0 :=
    Subtype.ext ((Submodule.starProjection_apply_eq_zero_iff K).2 hz)
  have e := h.comm z
  rw [h0, LinearPMap.map_zero] at e
  exact (Submodule.starProjection_apply_eq_zero_iff L).1 e.symm

end IsReducingPair

end Operators

end Feec
