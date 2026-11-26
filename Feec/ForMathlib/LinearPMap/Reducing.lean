module

public import Feec.ForMathlib.LinearPMap.Skew
public import Feec.ForMathlib.LinearPMap.GraphSpace

/-!
# Reducing subspaces of unbounded operators, and restriction

Closed subspaces `(K, L)` reduce a partial linear map `T` when `P_K D(T) ⊆ D(T)` and
`T P_K = P_L T` on `D(T)`; the part of a skew-adjoint operator in a reducing subspace is
skew-adjoint.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `(K, L)` reduces `T`: `P_K D(T) ⊆ D(T)` and `T P_K = P_L T` on `D(T)`. -/
structure IsReducingPair (T : E →ₗ.[𝕜] F) (K : Submodule 𝕜 E) (L : Submodule 𝕜 F)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] : Prop where
  /-- `P_K D(T) ⊆ D(T)`. -/
  proj_mem : ∀ x : T.domain, K.starProjection (x : E) ∈ T.domain
  /-- `T P_K = P_L T` on `D(T)`. -/
  comm : ∀ x : T.domain, T ⟨_, proj_mem x⟩ = L.starProjection (T x)

/-- `K` reduces `A : E → E`: `P_K D(A) ⊆ D(A)` and `A P_K = P_K A` on `D(A)`. -/
abbrev IsReducing (A : E →ₗ.[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] : Prop :=
  A.IsReducingPair K K

section IsReducingPair

variable {T : E →ₗ.[𝕜] F} {K : Submodule 𝕜 E} {L : Submodule 𝕜 F}
  [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]

theorem IsReducingPair.mapsTo (h : T.IsReducingPair K L) (x : T.domain) (hx : (x : E) ∈ K) :
    T x ∈ L := by
  have hx' : (⟨K.starProjection (x : E), h.proj_mem x⟩ : T.domain) = x :=
    Subtype.ext ((K.starProjection_eq_self_iff).2 hx)
  have e := h.comm x
  rw [hx'] at e
  rw [e]
  exact L.starProjection_apply_mem _

theorem IsReducingPair.map_orthogonal_mem (h : T.IsReducingPair K L) (z : T.domain)
    (hz : (z : E) ∈ Kᗮ) : T z ∈ Lᗮ := by
  have h0 : (⟨K.starProjection (z : E), h.proj_mem z⟩ : T.domain) = 0 :=
    Subtype.ext ((Submodule.starProjection_apply_eq_zero_iff K).2 hz)
  have e := h.comm z
  rw [h0, LinearPMap.map_zero] at e
  exact (Submodule.starProjection_apply_eq_zero_iff L).1 e.symm

theorem IsReducingPair.orthogonal (h : T.IsReducingPair K L) : T.IsReducingPair Kᗮ Lᗮ := by
  have hmem : ∀ x : T.domain, Kᗮ.starProjection (x : E) ∈ T.domain := fun x => by
    rw [Submodule.starProjection_orthogonal_val]; exact T.domain.sub_mem x.2 (h.proj_mem x)
  refine ⟨hmem, fun x => ?_⟩
  have e : (⟨_, hmem x⟩ : T.domain) = x - ⟨_, h.proj_mem x⟩ := by
    ext; simp
  rw [e, LinearPMap.map_sub, h.comm, Submodule.starProjection_orthogonal_val]

theorem isReducingPair_top (T : E →ₗ.[𝕜] F) : T.IsReducingPair ⊤ ⊤ :=
  ⟨fun x => by simp [Submodule.starProjection_top], fun x => by simp [Submodule.starProjection_top]⟩

theorem IsReducingPair.adjoint [CompleteSpace E] (h : T.IsReducingPair K L)
    (hd : Dense (T.domain : Set E)) : T†.IsReducingPair L K := by
  have key : ∀ y : T†.domain, ∀ x : T.domain,
      ⟪K.starProjection (T† y), (x : E)⟫_𝕜 = ⟪L.starProjection (y : F), T x⟫_𝕜 := by
    intro y x
    rw [K.inner_starProjection_left_eq_right, L.inner_starProjection_left_eq_right, ← h.comm x]
    exact adjoint_isFormalAdjoint hd y ⟨_, h.proj_mem x⟩
  have hmem : ∀ y : T†.domain, L.starProjection (y : F) ∈ T†.domain := fun y =>
    mem_adjoint_domain_of_exists _ ⟨_, key y⟩
  exact ⟨hmem, fun y => adjoint_apply_eq hd ⟨_, hmem y⟩ (key y)⟩

theorem IsReducingPair.le_domain [FiniteDimensional 𝕜 K] (h : T.IsReducingPair K L)
    (hT : Dense (T.domain : Set E)) : K ≤ T.domain := by
  set M := T.domain.map (K.starProjection : E →ₗ[𝕜] E)
  have hMK : M ≤ K := by
    rintro _ ⟨x, -, rfl⟩; exact Submodule.starProjection_apply_mem K x
  have hMD : M ≤ T.domain := by
    rintro _ ⟨x, hx, rfl⟩; exact h.proj_mem ⟨x, hx⟩
  have : FiniteDimensional 𝕜 M := Submodule.finiteDimensional_of_le hMK
  have hclosed : _root_.IsClosed (M : Set E) := Submodule.closed_of_finiteDimensional M
  intro x hx
  have hxc : K.starProjection x ∈ _root_.closure (M : Set E) := by
    have h1 := image_closure_subset_closure_image (f := K.starProjection)
      (s := (T.domain : Set E)) K.starProjection.continuous
    rw [hT.closure_eq] at h1
    exact h1 ⟨x, Set.mem_univ _, rfl⟩
  rw [hclosed.closure_eq, Submodule.starProjection_eq_self_iff.2 hx] at hxc
  exact hMD hxc

end IsReducingPair

section Restrict

/-- The part of `A` in an invariant subspace `K`, with domain `D(A) ∩ K`. -/
def restrict (A : E →ₗ.[𝕜] E) (K : Submodule 𝕜 E)
    (hinv : ∀ x : A.domain, (x : E) ∈ K → A x ∈ K) : K →ₗ.[𝕜] K where
  domain := A.domain.comap K.subtype
  toFun :=
    { toFun := fun x => ⟨A ⟨(x : K), x.2⟩, hinv ⟨_, x.2⟩ (x : K).2⟩
      map_add' := fun x y => by ext; simp [← LinearPMap.map_add]; rfl
      map_smul' := fun c x => by ext; simp [← LinearPMap.map_smul]; rfl }

@[simp] theorem restrict_apply (A : E →ₗ.[𝕜] E) (K : Submodule 𝕜 E)
    (hinv : ∀ x : A.domain, (x : E) ∈ K → A x ∈ K) (x : (A.restrict K hinv).domain) :
    ((A.restrict K hinv x : K) : E) = A ⟨((x : K) : E), x.2⟩ := rfl

theorem dense_restrict_domain (A : E →ₗ.[𝕜] E) (hD : Dense (A.domain : Set E))
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (h1 : ∀ x : A.domain, K.starProjection (x : E) ∈ A.domain)
    (h3 : ∀ x : A.domain, (x : E) ∈ K → A x ∈ K) :
    Dense ((A.restrict K h3).domain : Set K) := by
  have hd : Dense ((K.orthogonalProjectionOnto) '' (A.domain : Set E)) :=
    (Function.Surjective.denseRange (f := (K.orthogonalProjectionOnto : E → K))
      (fun k : K => ⟨(k : E), K.orthogonalProjectionOnto_mem_subspace_eq_self k⟩)).dense_image
      (K.orthogonalProjectionOnto).continuous hD
  refine hd.mono ?_
  rintro _ ⟨x, hx, rfl⟩
  change ((K.orthogonalProjectionOnto x : K) : E) ∈ A.domain
  rw [← Submodule.starProjection_apply]
  exact h1 ⟨x, hx⟩

theorem hasOrthogonalProjection_ker [CompleteSpace E] {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] (M : E →ₗ.[𝕜] G) (hM : M.IsClosed) : M.ker.HasOrthogonalProjection := by
  have : CompleteSpace M.ker := (isClosed_ker hM).completeSpace_coe
  infer_instance

end Restrict

section Skew

variable {A : E →ₗ.[𝕜] E} {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]

theorem IsSkewSymmetric.map_orthogonal_mem (hA : A.IsSkewSymmetric)
    (hD : Dense (A.domain : Set E))
    (h1 : ∀ x : A.domain, K.starProjection (x : E) ∈ A.domain)
    (h3 : ∀ x : A.domain, (x : E) ∈ K → A x ∈ K)
    (z : A.domain) (hz : (z : E) ∈ Kᗮ) : A z ∈ Kᗮ := by
  have hDt := dense_restrict_domain A hD K h1 h3
  have hf : Continuous (fun k : K => ⟪(k : E), A z⟫_𝕜) :=
    continuous_subtype_val.inner continuous_const
  have := Continuous.ext_on hDt hf continuous_const (fun v hv => by
    have hv' : ((v : K) : E) ∈ A.domain := hv
    have hLv : A ⟨v, hv'⟩ ∈ K := h3 ⟨v, hv'⟩ v.2
    have e := hA z ⟨v, hv'⟩
    have e0 : ⟪(z : E), A ⟨v, hv'⟩⟫_𝕜 = 0 := Submodule.inner_left_of_mem_orthogonal hLv hz
    rw [e0, neg_zero] at e
    exact inner_eq_zero_symm.1 e)
  exact (Submodule.mem_orthogonal K _).2 fun k hk => congrFun this ⟨k, hk⟩

theorem IsSkewSymmetric.commute_proj (hA : A.IsSkewSymmetric) (hD : Dense (A.domain : Set E))
    (h1 : ∀ x : A.domain, K.starProjection (x : E) ∈ A.domain)
    (h3 : ∀ x : A.domain, (x : E) ∈ K → A x ∈ K) (x : A.domain) :
    A ⟨K.starProjection (x : E), h1 x⟩ = K.starProjection (A x) := by
  have hz : (x : E) - K.starProjection x ∈ A.domain := A.domain.sub_mem x.2 (h1 x)
  have hsplit : A x = A ⟨_, h1 x⟩ + A ⟨_, hz⟩ := by
    rw [← LinearPMap.map_add]; congr 1; ext; simp
  have hK : A ⟨_, h1 x⟩ ∈ K := h3 ⟨_, h1 x⟩ (K.starProjection_apply_mem _)
  have hKp : A ⟨_, hz⟩ ∈ Kᗮ :=
    hA.map_orthogonal_mem hD h1 h3 ⟨_, hz⟩ (K.sub_starProjection_mem_orthogonal _)
  rw [hsplit, _root_.map_add, (K.starProjection_eq_self_iff).2 hK,
    (Submodule.starProjection_apply_eq_zero_iff K).2 hKp, add_zero]

theorem IsSkewSymmetric.isReducing (hA : A.IsSkewSymmetric) (hD : Dense (A.domain : Set E))
    (h1 : ∀ x : A.domain, K.starProjection (x : E) ∈ A.domain)
    (h3 : ∀ x : A.domain, (x : E) ∈ K → A x ∈ K) : A.IsReducing K :=
  ⟨h1, hA.commute_proj hD h1 h3⟩

theorem IsSkewSymmetric.isReducing_iff (hA : A.IsSkewSymmetric)
    (hD : Dense (A.domain : Set E)) :
    A.IsReducing K ↔ (∀ x : A.domain, K.starProjection (x : E) ∈ A.domain) ∧
      ∀ x : A.domain, (x : E) ∈ K → A x ∈ K :=
  ⟨fun h => ⟨h.proj_mem, h.mapsTo⟩, fun h => hA.isReducing hD h.1 h.2⟩

variable [CompleteSpace E]

theorem IsSkewAdjoint.isReducing (hA : A.IsSkewAdjoint)
    (h1 : ∀ x : A.domain, K.starProjection (x : E) ∈ A.domain)
    (h3 : ∀ x : A.domain, (x : E) ∈ K → A x ∈ K) : A.IsReducing K :=
  hA.isSkewSymmetric.isReducing hA.dense_domain h1 h3

theorem IsSkewAdjoint.isReducing_iff (hA : A.IsSkewAdjoint) :
    A.IsReducing K ↔ (∀ x : A.domain, K.starProjection (x : E) ∈ A.domain) ∧
      ∀ x : A.domain, (x : E) ∈ K → A x ∈ K :=
  hA.isSkewSymmetric.isReducing_iff hA.dense_domain

/-- The part of a skew-adjoint operator in a reducing subspace is skew-adjoint
([QuennevilleBelair2015], Thm 4.4 (adapted)). -/
theorem IsSkewAdjoint.restrict (hA : A.IsSkewAdjoint) [CompleteSpace K] (hK : A.IsReducing K) :
    (A.restrict K hK.mapsTo).IsSkewAdjoint := by
  set At := A.restrict K hK.mapsTo with hAt
  have skew := hA.isSkewSymmetric
  have h1 := hK.proj_mem
  have hDt : Dense (At.domain : Set K) :=
    dense_restrict_domain A hA.dense_domain K h1 hK.mapsTo
  have hform : At.IsFormalAdjoint (-At) := by
    intro x y
    rw [LinearPMap.neg_apply, Submodule.coe_inner, Submodule.coe_inner, Submodule.coe_neg,
      inner_neg_right]
    exact skew ⟨_, x.2⟩ ⟨_, y.2⟩
  have hle : -At ≤ At† := hform.le_adjoint hDt
  refine (LinearPMap.eq_of_le_of_domain_le hle ?_).symm
  intro u hu
  have key : ∀ x : A.domain, ⟪((At† ⟨u, hu⟩ : K) : E), (x : E)⟫_𝕜 = ⟪(u : E), A x⟫_𝕜 := by
    intro x
    set px : At.domain := ⟨K.orthogonalProjectionOnto x, by
      change ((K.orthogonalProjectionOnto x : K) : E) ∈ A.domain
      rw [← Submodule.starProjection_apply]; exact h1 x⟩
    have hadj := LinearPMap.adjoint_isFormalAdjoint hDt ⟨u, hu⟩ px
    have hz : (x : E) - K.starProjection x ∈ A.domain := A.domain.sub_mem x.2 (h1 x)
    have hzK : (x : E) - K.starProjection x ∈ Kᗮ := K.sub_starProjection_mem_orthogonal _
    have hsplit : A x = A ⟨_, h1 x⟩ + A ⟨_, hz⟩ := by
      rw [← LinearPMap.map_add]; congr 1; ext; simp
    have e1 : ⟪(u : E), A ⟨_, hz⟩⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal u.2 (hK.map_orthogonal_mem ⟨_, hz⟩ hzK)
    have e2 : ⟪((At† ⟨u, hu⟩ : K) : E), (x : E)⟫_𝕜
        = ⟪((At† ⟨u, hu⟩ : K) : E), K.starProjection (x : E)⟫_𝕜 := by
      rw [← sub_eq_zero, ← inner_sub_right]
      exact Submodule.inner_right_of_mem_orthogonal (At† ⟨u, hu⟩).2 hzK
    rw [e2, hsplit, inner_add_right, e1, add_zero]
    have := hadj
    simp only [Submodule.coe_inner] at this
    convert this using 2 <;> rfl
  have hmem : (u : E) ∈ A†.domain := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  rw [hA] at hmem
  exact hmem

end Skew

end LinearPMap
