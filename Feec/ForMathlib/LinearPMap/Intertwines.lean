module

public import Feec.ForMathlib.LinearPMap.Reducing

/-!
# Intertwining bounded maps

`LinearPMap.Intertwines J A B`: `J D(A) ⊆ D(B)` and `B J = J A` on `D(A)`; adjoints and
skew-adjointness transfer along unitary equivalences.
-/

open scoped InnerProductSpace
open Set

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- `J` intertwines `A` with `B`: `J D(A) ⊆ D(B)` and `B J = J A` on `D(A)`. -/
structure Intertwines (J : E →L[𝕜] F) (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) : Prop where
  mapsTo : ∀ x : A.domain, J x ∈ B.domain
  comm : ∀ x : A.domain, B ⟨J x, mapsTo x⟩ = J (A x)

theorem Intertwines.id (A : E →ₗ.[𝕜] E) : Intertwines (ContinuousLinearMap.id 𝕜 E) A A :=
  ⟨fun x => x.2, fun _ => rfl⟩

theorem apply_congr' {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (T : M →ₗ.[R] N) {x y : M} (hx : x ∈ T.domain) (hy : y ∈ T.domain)
    (h : x = y) : T ⟨x, hx⟩ = T ⟨y, hy⟩ := by
  subst h; rfl

theorem Intertwines.comp {J : E →L[𝕜] F} {J' : F →L[𝕜] G} {A : E →ₗ.[𝕜] E}
    {B : F →ₗ.[𝕜] F} {C : G →ₗ.[𝕜] G} (h : Intertwines J A B) (h' : Intertwines J' B C) :
    Intertwines (J'.comp J) A C :=
  ⟨fun x => h'.mapsTo ⟨_, h.mapsTo x⟩, fun x => by
    calc C ⟨(J'.comp J) x, _⟩ = C ⟨J' (J x), h'.mapsTo ⟨_, h.mapsTo x⟩⟩ := rfl
      _ = J' (B ⟨J x, h.mapsTo x⟩) := h'.comm ⟨J x, h.mapsTo x⟩
      _ = (J'.comp J) (A x) := by rw [h.comm]; rfl⟩

variable {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {e : E ≃ₗᵢ[𝕜] F}

theorem Intertwines.mem_domain_iff
    (h : Intertwines (e : E →L[𝕜] F) A B)
    (h' : Intertwines (e.symm : F →L[𝕜] E) B A) {x : F} :
    x ∈ B.domain ↔ e.symm x ∈ A.domain := by
  constructor
  · exact fun hx => h'.mapsTo ⟨x, hx⟩
  · intro hx
    have := h.mapsTo ⟨_, hx⟩
    simpa using this

theorem Intertwines.symm_symm (h : Intertwines (e : E →L[𝕜] F) A B) :
    Intertwines (e.symm.symm : E →L[𝕜] F) A B := by
  rw [LinearIsometryEquiv.symm_symm]; exact h

theorem Intertwines.adjoint [CompleteSpace E] [CompleteSpace F]
    (h' : Intertwines (e.symm : F →L[𝕜] E) B A) (hB : Dense (B.domain : Set F)) :
    Intertwines (e : E →L[𝕜] F) A† B† := by
  have hA : Dense (A.domain : Set E) := by
    have : e.symm '' (B.domain : Set F) ⊆ (A.domain : Set E) := by
      rintro _ ⟨x, hx, rfl⟩; exact h'.mapsTo ⟨x, hx⟩
    exact (e.symm.surjective.denseRange.dense_image e.symm.continuous hB).mono this
  have key : ∀ y : A†.domain, ∀ x : B.domain, ⟪e (A† y), (x : F)⟫_𝕜 = ⟪e y, B x⟫_𝕜 := by
    intro y x
    have hx : e.symm (x : F) ∈ A.domain := h'.mapsTo x
    have h1 : A ⟨e.symm x, hx⟩ = e.symm (B x) := h'.comm x
    have h2 := (adjoint_isFormalAdjoint (T := A) hA) y ⟨_, hx⟩
    calc ⟪e (A† y), (x : F)⟫_𝕜 = ⟪A† y, e.symm x⟫_𝕜 := by
          rw [← e.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
      _ = ⟪(y : E), A ⟨e.symm x, hx⟩⟫_𝕜 := h2
      _ = ⟪e y, B x⟫_𝕜 := by
          rw [h1, ← e.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  have hmem : ∀ y : A†.domain, e y ∈ B†.domain := fun y =>
    mem_adjoint_domain_of_exists _ ⟨_, key y⟩
  exact ⟨hmem, fun y => adjoint_apply_eq hB ⟨_, hmem y⟩ (key y)⟩

theorem Intertwines.isSkewAdjoint [CompleteSpace E] [CompleteSpace F]
    (h : Intertwines (e : E →L[𝕜] F) A B)
    (h' : Intertwines (e.symm : F →L[𝕜] E) B A) (hA : A.IsSkewAdjoint) : B.IsSkewAdjoint := by
  have hAd := hA.dense_domain
  have hBd : Dense (B.domain : Set F) := by
    have : e '' (A.domain : Set E) ⊆ (B.domain : Set F) := by
      rintro _ ⟨x, hx, rfl⟩; exact h.mapsTo ⟨x, hx⟩
    exact (e.surjective.denseRange.dense_image e.continuous hAd).mono this
  have hadj := h'.adjoint hBd
  have hadj' := h.symm_symm.adjoint hAd
  have hA' : A† = -A := hA
  have hdA : ∀ {x : E}, x ∈ A†.domain ↔ x ∈ A.domain := by
    intro x; rw [hA']; rfl
  unfold IsSkewAdjoint
  refine LinearPMap.ext ?_ fun y hy hy' => ?_
  · ext y
    change y ∈ B†.domain ↔ y ∈ B.domain
    rw [h.mem_domain_iff h']
    constructor
    · intro hy
      exact hdA.1 (hadj'.mapsTo ⟨y, hy⟩)
    · intro hy
      have := hadj.mapsTo ⟨_, hdA.2 hy⟩
      simpa using this
  · have hy2 : e.symm y ∈ A†.domain := hadj'.mapsTo ⟨y, hy⟩
    have hyA : e.symm y ∈ A.domain := hdA.1 hy2
    have e1 := hadj.comm ⟨_, hy2⟩
    have e2 : A† ⟨_, hy2⟩ = -A ⟨_, hyA⟩ := by
      have := (LinearPMap.ext_iff.1 hA').2 (hf := hy2) (hg := hyA)
      rwa [neg_apply] at this
    have e3 := h.comm ⟨_, hyA⟩
    have hyy : e (e.symm y) = y := e.apply_symm_apply y
    have hm1 : e (e.symm y) ∈ B†.domain := by rw [hyy]; exact hy
    have hm2 : e (e.symm y) ∈ B.domain := by rw [hyy]; exact hy'
    calc B† ⟨y, hy⟩ = B† ⟨e (e.symm y), hm1⟩ := apply_congr' _ _ _ hyy.symm
      _ = e (A† ⟨_, hy2⟩) := e1
      _ = -e (A ⟨_, hyA⟩) := by rw [e2]; simp
      _ = -B ⟨e (e.symm y), hm2⟩ := congrArg Neg.neg e3.symm
      _ = (-B) ⟨y, hy'⟩ := by rw [neg_apply, apply_congr' B hm2 hy' hyy]

theorem Intertwines.isSkewAdjoint_iff [CompleteSpace E] [CompleteSpace F]
    (h : Intertwines (e : E →L[𝕜] F) A B)
    (h' : Intertwines (e.symm : F →L[𝕜] E) B A) :
    A.IsSkewAdjoint ↔ B.IsSkewAdjoint :=
  ⟨h.isSkewAdjoint h', h'.isSkewAdjoint (e := e.symm) h.symm_symm⟩

end LinearPMap
