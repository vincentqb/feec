module

public import Feec.HilbertComplex.Reducing

/-!
# Real solutions: antilinear conjugations

A **conjugation** of a Hilbert space over `𝕜 = ℝ` or `ℂ` is an `ℝ`-linear involution `C` with
`C (a • x) = conj a • C x` and `⟪C x, C y⟫ = ⟪y, x⟫` (e.g. pointwise complex conjugation of
fields, or `ξ ↦ conj f̂(-ξ)` on the Fourier side). Its fixed set `{x | C x = x}` (the real
fields) is an `ℝ`-subspace but **not** a `𝕜`-submodule, so it is not a reducing subspace; the
reality of solutions is a separate statement:

* `Evolution.IsStrongSolution.conj`: if `C` commutes with `A`, then `C ∘ U` solves the equation
  with forcing `C ∘ F`.
* `Evolution.IsStrongSolution.conj_eq`: hence, for a dissipative `A`, real data and real
  forcing give a real solution (uniqueness).
* `C0Group.IsIsometric.conj_S`: the group of a skew-adjoint generator commuting with `C`
  commutes with `C`.

For a Hilbert complex with conjugations commuting with the differentials
(`HilbertComplex.Conj`), the conjugations commute with the adjoints (`Conj.adjoint_comm`), the
total conjugation commutes with the wave operator (`Conj.wave_totalConj`), and the Hodge wave
equation has real solutions for real data (`Conj.conj_eq`, `Conj.totalConj_waveGroup`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (real fields on `ℝ³` from the Fourier side)
-/

open scoped InnerProductSpace ComplexConjugate
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec

/-! ### Operators commuting with an `ℝ`-linear map -/

section Operator

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] {A : E →ₗ.[𝕜] E} {I : Set ℝ} {F U : ℝ → E}

/-- An `ℝ`-linear bounded map `C` commutes with `A`: `C D(A) ⊆ D(A)` and `A C = C A`. -/
structure CommutesWith (C : E →L[ℝ] E) (A : E →ₗ.[𝕜] E) : Prop where
  mapsTo : ∀ x : A.domain, C x ∈ A.domain
  comm : ∀ x : A.domain, A ⟨C x, mapsTo x⟩ = C (A x)

/-- **Conjugated solutions**: if `C` commutes with `A`, then `C ∘ U` is a strong solution of
`V' = A V + C ∘ F` whenever `U` solves `U' = A U + F`. -/
theorem Evolution.IsStrongSolution.conj {C : E →L[ℝ] E} (hC : CommutesWith C A)
    (hU : Evolution.IsStrongSolution A I F U) :
    Evolution.IsStrongSolution A I (fun t => C (F t)) fun t => C (U t) := by
  refine Evolution.IsStrongSolution.of_deriv fun t ht => ⟨_, A.mem_graph ⟨_, hC.mapsTo
    ⟨_, hU.mem_domain ht⟩⟩, ?_⟩
  have hd := C.hasFDerivAt.comp_hasDerivWithinAt t (hU.hasDerivWithinAt ht)
  rw [hC.comm, ← _root_.map_add]
  exact hd

/-- **Reality of solutions**: for a dissipative `A` commuting with `C`, a strong solution on
`[a, b]` with `C (U a) = U a` and `C (F t) = F t` satisfies `C (U t) = U t`. -/
theorem Evolution.IsStrongSolution.conj_eq {C : E →L[ℝ] E} (hC : CommutesWith C A)
    (hA : A.IsDissipative) {a b : ℝ} (hU : Evolution.IsStrongSolution A (Icc a b) F U)
    (h0 : C (U a) = U a) (hF : ∀ t ∈ Icc a b, C (F t) = F t) :
    ∀ t ∈ Icc a b, C (U t) = U t := by
  have hV := (hU.conj hC).congr (fun _ _ => rfl) hF
  exact hV.unique hA hU h0

variable [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]

/-- The group of an isometric group whose generator commutes with `C` commutes with `C`. -/
theorem C0Group.IsIsometric.conj_S {G : C0Group 𝕜 E} (hG : G.IsIsometric) {C : E →L[ℝ] E}
    (hC : CommutesWith C G.generator) (t : ℝ) (x : E) : C (G.S t x) = G.S t (C x) := by
  set B := G.generator
  have hD : ∀ x : B.domain, C (G.S t x) = G.S t (C x) := by
    intro x
    have hm1 : ∀ s, C (G.S s x) ∈ B.domain := fun s => hC.mapsTo ⟨_, G.mapsTo_domain x s⟩
    have hm2 : ∀ s, G.S s (C x) ∈ B.domain := fun s => G.mapsTo_domain ⟨_, hC.mapsTo x⟩ s
    set e : ℝ → E := fun s => C (G.S s x) - G.S s (C x)
    have hmem : ∀ s, e s ∈ B.domain := fun s => B.domain.sub_mem (hm1 s) (hm2 s)
    have hde : ∀ s, HasDerivAt e (B ⟨e s, hmem s⟩) s := by
      intro s
      have h1 := C.hasFDerivAt.comp_hasDerivAt s (G.hasDerivAt_apply' x s)
      have h2 := G.hasDerivAt_apply' ⟨_, hC.mapsTo x⟩ s
      have e3 : (⟨e s, hmem s⟩ : B.domain) = ⟨C (G.S s x), hm1 s⟩ - ⟨G.S s (C x), hm2 s⟩ := rfl
      rw [e3, LinearPMap.map_sub, hC.comm ⟨_, G.mapsTo_domain x s⟩]
      exact h1.sub h2
    have h0 := hG.isSkewSymmetric_generator.eq_zero_of_hasDerivAt hmem hde
      (by simp [e, C0Group.S_zero_apply]) t
    exact sub_eq_zero.1 h0
  have := Continuous.ext_on G.dense_domain_generator (C.continuous.comp (G.S t).continuous)
    ((G.S t).continuous.comp C.continuous) (fun x hx => hD ⟨x, hx⟩)
  exact congrFun this x

end Operator

/-! ### Conjugations of Hilbert complexes -/

namespace HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] (H : HilbertComplex 𝕜 c W)

/-- **Conjugations of a Hilbert complex**: antilinear involutions `C i` of each `W i` with
`⟪C x, C y⟫ = ⟪y, x⟫`, preserving the domains and commuting with the differentials. -/
structure Conj where
  /-- the conjugations -/
  C : ∀ i, W i →L[ℝ] W i
  antilinear : ∀ i (a : 𝕜) (x : W i), C i (a • x) = conj a • C i x
  invol : ∀ i (x : W i), C i (C i x) = x
  inner_C : ∀ i (x y : W i), ⟪C i x, C i y⟫_𝕜 = ⟪y, x⟫_𝕜
  mapsTo : ∀ i j (x : (H.d i j).domain), C i x ∈ (H.d i j).domain
  comm : ∀ i j (x : (H.d i j).domain), H.d i j ⟨C i x, mapsTo i j x⟩ = C j (H.d i j x)

namespace Conj

variable {H} (K : H.Conj)

/-- The conjugations commute with the adjoints. -/
theorem adjoint_comm {i j : ι} (y : ((H.d i j)†).domain) :
    ∃ h : K.C j y ∈ ((H.d i j)†).domain, (H.d i j)† ⟨_, h⟩ = K.C i ((H.d i j)† y) := by
  have key : ∀ x : (H.d i j).domain,
      ⟪K.C i ((H.d i j)† y), (x : W i)⟫_𝕜 = ⟪K.C j y, H.d i j x⟫_𝕜 := by
    intro x
    have h1 := adjoint_isFormalAdjoint (H.dense i j) y ⟨_, K.mapsTo i j x⟩
    rw [K.comm i j x] at h1
    calc ⟪K.C i ((H.d i j)† y), (x : W i)⟫_𝕜
        = ⟪K.C i ((H.d i j)† y), K.C i (K.C i x)⟫_𝕜 := by rw [K.invol]
      _ = ⟪K.C i x, (H.d i j)† y⟫_𝕜 := K.inner_C _ _ _
      _ = conj ⟪(y : W j), K.C j (H.d i j x)⟫_𝕜 := by rw [← h1, inner_conj_symm]
      _ = conj ⟪K.C j (K.C j y), K.C j (H.d i j x)⟫_𝕜 := by rw [K.invol]
      _ = conj ⟪H.d i j x, K.C j y⟫_𝕜 := by rw [K.inner_C]
      _ = ⟪K.C j y, H.d i j x⟫_𝕜 := inner_conj_symm _ _
  have hmem : K.C j y ∈ ((H.d i j)†).domain := mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, adjoint_apply_eq (H.dense i j) ⟨_, hmem⟩ key⟩

/-- The total conjugation `(C x) i = C i (x i)` of `PiLp 2 W`. -/
def totalConj : PiLp 2 W →L[ℝ] PiLp 2 W :=
  ((PiLp.continuousLinearEquiv 2 ℝ W).symm : (∀ i, W i) →L[ℝ] PiLp 2 W).comp
    ((ContinuousLinearMap.pi fun i => (K.C i).comp (ContinuousLinearMap.proj i)).comp
      (PiLp.continuousLinearEquiv 2 ℝ W : PiLp 2 W →L[ℝ] ∀ i, W i))

theorem totalConj_apply (x : PiLp 2 W) (i : ι) : K.totalConj x i = K.C i (x i) := rfl

variable [Fintype ι]

/-- **The total conjugation commutes with the wave operator.** -/
theorem wave_totalConj : CommutesWith K.totalConj H.wave := by
  have hmem : ∀ x : H.wave.domain, K.totalConj (x : PiLp 2 W) ∈ H.wave.domain := fun x =>
    H.mem_wave_domain.2 ⟨fun i j => K.mapsTo i j ⟨_, x.2.1 i j⟩,
      fun i j => (K.adjoint_comm ⟨_, x.2.2 j i⟩).1⟩
  refine ⟨hmem, fun x => ?_⟩
  set x' : H.wave.domain := ⟨_, hmem x⟩
  change H.wave x' = K.totalConj (H.wave x)
  refine PiLp.ext fun j => ?_
  rw [wave_apply, totalConj_apply, wave_apply, _root_.map_sub, map_sum, map_sum]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun i _ => K.comm i j ⟨_, x.2.1 i j⟩)
    (Finset.sum_congr rfl fun k _ => (K.adjoint_comm ⟨_, x.2.2 k j⟩).2)

/-- **Real data give real solutions of the Hodge wave equation.** -/
theorem conj_eq {a b : ℝ} {F U : ℝ → PiLp 2 W}
    (hU : Evolution.IsStrongSolution H.wave (Icc a b) F U) (h0 : K.totalConj (U a) = U a)
    (hF : ∀ t ∈ Icc a b, K.totalConj (F t) = F t) : ∀ t ∈ Icc a b, K.totalConj (U t) = U t :=
  hU.conj_eq K.wave_totalConj H.isSkewAdjoint_wave.isDissipative h0 hF

variable [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- The wave group commutes with the total conjugation: it maps real data to real data. -/
theorem totalConj_waveGroup (t : ℝ) (x : PiLp 2 W) :
    K.totalConj (H.waveGroup.S t x) = H.waveGroup.S t (K.totalConj x) := by
  have h := K.wave_totalConj
  rw [← generator_waveGroup] at h
  exact H.isIsometric_waveGroup.conj_S h t x

end Conj

end HilbertComplex

end Feec
