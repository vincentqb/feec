module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Feec.ForMathlib.LinearPMap.Basic

/-!
# Skew-symmetric, skew-adjoint and dissipative unbounded operators

Symmetric, skew-symmetric, skew-adjoint (`A† = -A`), dissipative (`re ⟪A x, x⟫ ≤ 0`) and
m-dissipative partial linear maps on an inner product space ([QuennevilleBelair2015], §4.1).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate
open Set

@[expose] public noncomputable section

namespace LinearPMap

section Neg

variable {R E F : Type*} [CommRing R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

theorem mem_graph_neg_iff {f : E →ₗ.[R] F} {x : E} {y : F} :
    (x, y) ∈ (-f).graph ↔ (x, -y) ∈ f.graph := by
  simp only [mem_graph_iff, neg_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, by simp⟩
  · rintro ⟨z, hz, h⟩; exact ⟨z, hz, by simp [h]⟩

theorem IsClosed.neg [TopologicalSpace E] [TopologicalSpace F] [ContinuousNeg F]
    {f : E →ₗ.[R] F} (hf : f.IsClosed) : (-f).IsClosed := by
  have : ((-f).graph : Set (E × F)) = (fun p : E × F => (p.1, -p.2)) ⁻¹' f.graph := by
    ext ⟨x, y⟩; exact mem_graph_neg_iff
  rw [LinearPMap.IsClosed, this]
  exact hf.preimage (continuous_fst.prodMk continuous_snd.neg)

end Neg

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Symmetry on the domain: `⟪A x, y⟫ = ⟪x, A y⟫`. -/
def IsSymmetric (A : E →ₗ.[𝕜] E) : Prop :=
  ∀ x y : A.domain, ⟪A x, (y : E)⟫_𝕜 = ⟪(x : E), A y⟫_𝕜

/-- Skew-symmetry on the domain: `⟪A x, y⟫ = -⟪x, A y⟫`. -/
def IsSkewSymmetric (A : E →ₗ.[𝕜] E) : Prop :=
  ∀ x y : A.domain, ⟪A x, (y : E)⟫_𝕜 = -⟪(x : E), A y⟫_𝕜

/-- Skew-adjoint operator: `A† = -A`, with equal domains. -/
def IsSkewAdjoint [CompleteSpace E] (A : E →ₗ.[𝕜] E) : Prop := A† = -A

/-- Dissipative operator: `re ⟪A x, x⟫ ≤ 0` on `D(A)`. -/
def IsDissipative (A : E →ₗ.[𝕜] E) : Prop := ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ 0

/-- m-dissipative operator: dissipative, and `μ - A` is onto for some `μ > 0`. -/
structure IsMDissipative (A : E →ₗ.[𝕜] E) : Prop where
  dissipative : A.IsDissipative
  surj : ∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : 𝕜) • (x : E) - A x = y

variable {A : E →ₗ.[𝕜] E}

theorem isSymmetric_iff_isFormalAdjoint : A.IsSymmetric ↔ A.IsFormalAdjoint A := Iff.rfl

theorem isSkewSymmetric_iff_isFormalAdjoint_neg : A.IsSkewSymmetric ↔ A.IsFormalAdjoint (-A) := by
  constructor
  · intro h x y
    rw [neg_apply, inner_neg_right]
    exact h x y
  · intro h x y
    have := h x y
    rw [neg_apply, inner_neg_right] at this
    exact this

theorem IsSkewSymmetric.re_inner_self (hA : A.IsSkewSymmetric) (x : A.domain) :
    RCLike.re ⟪A x, (x : E)⟫_𝕜 = 0 := by
  have h1 : RCLike.re ⟪A x, (x : E)⟫_𝕜 = -RCLike.re ⟪(x : E), A x⟫_𝕜 := by
    rw [hA x x]; simp
  have h2 : RCLike.re ⟪(x : E), A x⟫_𝕜 = RCLike.re ⟪A x, (x : E)⟫_𝕜 := inner_re_symm _ _
  linarith

theorem IsSkewSymmetric.neg (hA : A.IsSkewSymmetric) : (-A).IsSkewSymmetric := fun x y => by
  simp only [neg_apply, inner_neg_left, inner_neg_right, neg_inj]
  exact hA x y

theorem IsSkewSymmetric.isDissipative (hA : A.IsSkewSymmetric) : A.IsDissipative :=
  fun x => (hA.re_inner_self x).le

section Complete

variable [CompleteSpace E]

theorem adjoint_neg (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) : (-T)† = -T† := by
  have hT' : Dense ((-T).domain : Set E) := hT
  have hdom : (-T)†.domain = (-T†).domain := by
    ext y
    change y ∈ (-T)†.domain ↔ y ∈ T†.domain
    rw [mem_adjoint_domain_iff, mem_adjoint_domain_iff]
    have : (innerₛₗ 𝕜 y).comp (-T).toFun = -((innerₛₗ 𝕜 y).comp T.toFun) := by
      ext x; simp [neg_apply]
    rw [this, LinearMap.coe_neg]
    exact ⟨fun h => by simpa using h.neg, fun h => h.neg⟩
  refine LinearPMap.ext hdom fun y hy hy' => ?_
  refine adjoint_apply_eq hT' ⟨y, hy⟩ fun x => ?_
  have h := (adjoint_isFormalAdjoint hT) ⟨y, hy'⟩ x
  change ⟪-T† ⟨y, hy'⟩, (x : E)⟫_𝕜 = ⟪y, -T x⟫_𝕜
  rw [inner_neg_left, inner_neg_right, h]

theorem IsSkewAdjoint.dense_domain (hA : A.IsSkewAdjoint) : Dense (A.domain : Set E) := by
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
      have : (innerₛₗ 𝕜 y).comp A.toFun = 0 := by
        ext x; simp [hzero x]
      rw [this]; exact continuous_zero
    rw [hA] at hy; exact hy
  exact h (by rw [htop]; simp [dense_univ])

theorem IsSkewAdjoint.isSkewSymmetric (hA : A.IsSkewAdjoint) : A.IsSkewSymmetric := by
  intro x y
  have hle : -A ≤ A† := hA ▸ le_rfl
  have hx : (x : E) ∈ A†.domain := hle.1 x.2
  have h1 := adjoint_isFormalAdjoint hA.dense_domain ⟨x, hx⟩ y
  have h2 : A† ⟨x, hx⟩ = -A x := (hle.2 (x := x) (y := ⟨x, hx⟩) rfl).symm
  rw [h2, inner_neg_left] at h1
  rw [← neg_eq_iff_eq_neg, h1]

theorem IsSkewAdjoint.isClosed (hA : A.IsSkewAdjoint) : A.IsClosed := by
  have h : A = -A† := by rw [hA, neg_neg]
  rw [h]
  exact (adjoint_isClosed hA.dense_domain).neg

theorem IsSkewAdjoint.neg (hA : A.IsSkewAdjoint) : (-A).IsSkewAdjoint := by
  unfold IsSkewAdjoint
  rw [adjoint_neg A hA.dense_domain, hA]

theorem IsSkewAdjoint.isDissipative (hA : A.IsSkewAdjoint) : A.IsDissipative :=
  hA.isSkewSymmetric.isDissipative

theorem isSkewSymmetric_iff_neg_le_adjoint (hD : Dense (A.domain : Set E)) :
    A.IsSkewSymmetric ↔ -A ≤ A† := by
  constructor
  · intro hS
    exact (isSkewSymmetric_iff_isFormalAdjoint_neg.1 hS).le_adjoint hD
  · intro hle x y
    have hx : (x : E) ∈ A†.domain := hle.1 x.2
    have h1 := adjoint_isFormalAdjoint hD ⟨x, hx⟩ y
    have h2 : A† ⟨x, hx⟩ = -A x := (hle.2 (x := x) (y := ⟨x, hx⟩) rfl).symm
    rw [h2, inner_neg_left] at h1
    rw [← neg_eq_iff_eq_neg, h1]

theorem isSymmetric_iff_le_adjoint (hD : Dense (A.domain : Set E)) :
    A.IsSymmetric ↔ A ≤ A† := by
  constructor
  · intro h
    exact (isSymmetric_iff_isFormalAdjoint.1 h).le_adjoint hD
  · intro hle x y
    have hy : (y : E) ∈ A†.domain := hle.1 y.2
    have h1 := adjoint_isFormalAdjoint hD ⟨y, hy⟩ x
    have h2 : A† ⟨y, hy⟩ = A y := (hle.2 (x := y) (y := ⟨y, hy⟩) rfl).symm
    rw [h2] at h1
    have h1' : ⟪(y : E), A x⟫_𝕜 = ⟪A y, (x : E)⟫_𝕜 := h1.symm
    rw [← inner_conj_symm (A x) (y : E), h1', inner_conj_symm]

theorem isSkewAdjoint_iff_neg_le_adjoint :
    A.IsSkewAdjoint ↔ -A ≤ A† ∧ A†.domain ≤ A.domain := by
  constructor
  · intro h
    have h' : A† = -A := h
    rw [h']
    exact ⟨le_rfl, le_rfl⟩
  · rintro ⟨hle, hdom⟩
    exact (LinearPMap.eq_of_le_of_domain_le hle hdom).symm

theorem isSkewAdjoint_iff (hD : Dense (A.domain : Set E)) :
    A.IsSkewAdjoint ↔ A.IsSkewSymmetric ∧ A†.domain ≤ A.domain := by
  rw [isSkewAdjoint_iff_neg_le_adjoint, isSkewSymmetric_iff_neg_le_adjoint hD]

theorem isSelfAdjoint_iff_le_adjoint :
    IsSelfAdjoint A ↔ A ≤ A† ∧ A†.domain ≤ A.domain := by
  rw [isSelfAdjoint_def]
  constructor
  · intro h
    rw [h]
    exact ⟨le_rfl, le_rfl⟩
  · rintro ⟨hle, hdom⟩
    exact (LinearPMap.eq_of_le_of_domain_le hle hdom).symm

theorem isSelfAdjoint_iff (hD : Dense (A.domain : Set E)) :
    IsSelfAdjoint A ↔ A.IsSymmetric ∧ A†.domain ≤ A.domain := by
  rw [isSelfAdjoint_iff_le_adjoint, isSymmetric_iff_le_adjoint hD]

end Complete

end LinearPMap
