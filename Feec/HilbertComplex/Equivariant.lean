module

public import Feec.HilbertComplex.Transport

/-!
# Symmetries of Hilbert complexes: equivariance and the method of images

A unitary action of a group `Γ` on a Hilbert complex (`HilbertComplex.Action`) commutes with
the differentials, hence with their adjoints, the wave operator and the wave group. For a
finite group, the fixed vectors form a **reducing subcomplex**: the orthogonal projection is the
group average, which commutes with every `d`. Its compression (`Action.fixedComplex`) is the
complex of `Γ`-symmetric fields, e.g. the fields on a cube obtained from periodic fields by
reflection (the **method of images**); constraint propagation holds there as soon as it holds
for the symmetric complex (`Action.propagates`).

## Main definitions

* `Feec.HilbertComplex.Action H Γ`, `Action.fixed`, `Action.avg`, `Action.totalAct`,
  `Action.fixedComplex`.

## Main results

* `Action.starProjection_fixed`: `P_{Fix} = |Γ|⁻¹ ∑_g act g` (finite `Γ`).
* **`Action.reducingSubcomplex_fixed`**; `Action.propagates`.
* `Action.adjoint_comm`, `Action.wave_totalAct`, `Action.totalAct_waveGroup`: the wave group is
  `Γ`-equivariant.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17 on the cube)
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

/-- A **unitary action** of a group `Γ` on a Hilbert complex: unitaries `act g i` of each `W i`,
a group action in `g`, preserving the domains and commuting with the differentials. -/
structure Action (Γ : Type*) [Group Γ] where
  /-- the unitaries -/
  act : Γ → ∀ i, W i ≃ₗᵢ[𝕜] W i
  act_one : ∀ i x, act 1 i x = x
  act_mul : ∀ g h i x, act (g * h) i x = act g i (act h i x)
  mapsTo : ∀ g i j (x : (H.d i j).domain), act g i x ∈ (H.d i j).domain
  comm : ∀ g i j (x : (H.d i j).domain),
    H.d i j ⟨act g i x, mapsTo g i j x⟩ = act g j (H.d i j x)

namespace Action

variable {H} {Γ : Type*} [Group Γ] (A : H.Action Γ)

@[simp] theorem act_inv_act (g : Γ) (i : ι) (x : W i) : A.act g⁻¹ i (A.act g i x) = x := by
  rw [← A.act_mul, inv_mul_cancel, A.act_one]

@[simp] theorem act_act_inv (g : Γ) (i : ι) (x : W i) : A.act g i (A.act g⁻¹ i x) = x := by
  rw [← A.act_mul, mul_inv_cancel, A.act_one]

/-- The `Γ`-fixed vectors of `W i`. -/
def fixed (i : ι) : Submodule 𝕜 (W i) where
  carrier := {x | ∀ g, A.act g i x = x}
  add_mem' hx hy g := by rw [_root_.map_add, hx g, hy g]
  zero_mem' g := _root_.map_zero _
  smul_mem' a x hx g := by rw [_root_.map_smul, hx g]

theorem mem_fixed {i : ι} {x : W i} : x ∈ A.fixed i ↔ ∀ g, A.act g i x = x := Iff.rfl

theorem isClosed_fixed (i : ι) : IsClosed (A.fixed i : Set (W i)) := by
  have e : (A.fixed i : Set (W i)) = ⋂ g, {x | A.act g i x = x} := by ext; simp [mem_fixed]
  rw [e]
  exact isClosed_iInter fun g => isClosed_eq (A.act g i).continuous continuous_id

instance (i : ι) : CompleteSpace (A.fixed i) := (A.isClosed_fixed i).completeSpace_coe

/-- The adjoints commute with the action: `act g D(d†) ⊆ D(d†)` and `d† act g = act g d†`. -/
theorem adjoint_comm (g : Γ) {i j : ι} (y : ((H.d i j)†).domain) :
    ∃ h : A.act g j y ∈ ((H.d i j)†).domain, (H.d i j)† ⟨_, h⟩ = A.act g i ((H.d i j)† y) := by
  have key : ∀ x : (H.d i j).domain,
      ⟪A.act g i ((H.d i j)† y), (x : W i)⟫_𝕜 = ⟪A.act g j y, H.d i j x⟫_𝕜 := by
    intro x
    have hx := A.mapsTo g⁻¹ i j x
    have h1 := adjoint_isFormalAdjoint (H.dense i j) y ⟨_, hx⟩
    rw [A.comm g⁻¹ i j x] at h1
    calc ⟪A.act g i ((H.d i j)† y), (x : W i)⟫_𝕜
        = ⟪A.act g i ((H.d i j)† y), A.act g i (A.act g⁻¹ i x)⟫_𝕜 := by rw [act_act_inv]
      _ = ⟪(H.d i j)† y, A.act g⁻¹ i x⟫_𝕜 := LinearIsometryEquiv.inner_map_map _ _ _
      _ = ⟪(y : W j), A.act g⁻¹ j (H.d i j x)⟫_𝕜 := h1
      _ = ⟪A.act g j y, A.act g j (A.act g⁻¹ j (H.d i j x))⟫_𝕜 :=
          (LinearIsometryEquiv.inner_map_map _ _ _).symm
      _ = ⟪A.act g j y, H.d i j x⟫_𝕜 := by rw [act_act_inv]
  have hmem : A.act g j y ∈ ((H.d i j)†).domain := mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, adjoint_apply_eq (H.dense i j) ⟨_, hmem⟩ key⟩

/-! ### Finite groups: the fixed subcomplex -/

section Finite

variable [Fintype Γ]

/-- The group average `|Γ|⁻¹ ∑_g act g`. -/
def avg (i : ι) (x : W i) : W i := (Fintype.card Γ : 𝕜)⁻¹ • ∑ g, A.act g i x

theorem act_avg (h : Γ) (i : ι) (x : W i) : A.act h i (A.avg i x) = A.avg i x := by
  simp only [avg, _root_.map_smul, map_sum, ← A.act_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft h) fun g => A.act g i x

theorem avg_mem (i : ι) (x : W i) : A.avg i x ∈ A.fixed i := fun h => A.act_avg h i x

theorem avg_of_mem {i : ι} {x : W i} (hx : x ∈ A.fixed i) : A.avg i x = x := by
  have hn : (Fintype.card Γ : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [avg, hx _, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    inv_mul_cancel₀ hn, one_smul]

theorem sub_avg_mem_orthogonal (i : ι) (x : W i) : x - A.avg i x ∈ (A.fixed i)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hn : (Fintype.card Γ : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hs : ∀ g, ⟪y, A.act g i x⟫_𝕜 = ⟪y, x⟫_𝕜 := fun g => by
    conv_lhs => rw [← hy g]
    exact LinearIsometryEquiv.inner_map_map _ _ _
  rw [inner_sub_right, avg, inner_smul_right, inner_sum, Finset.sum_congr rfl fun g _ => hs g,
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul 𝕜, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hn, one_mul, sub_self]

/-- **The projection onto the fixed vectors is the group average.** -/
theorem starProjection_fixed (i : ι) (x : W i) : (A.fixed i).starProjection x = A.avg i x :=
  Submodule.eq_starProjection_of_mem_orthogonal (A.avg_mem i x) (A.sub_avg_mem_orthogonal i x)

/-- **The fixed vectors of a finite unitary action form a reducing subcomplex.** -/
theorem reducingSubcomplex_fixed : H.ReducingSubcomplex A.fixed := by
  refine ⟨fun i j => ⟨fun x => ?_, fun x => ?_⟩⟩
  · rw [starProjection_fixed, avg]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => A.mapsTo g i j x)
  · have hm : ∀ g, A.act g i x ∈ (H.d i j).domain := fun g => A.mapsTo g i j x
    have e : (⟨(A.fixed i).starProjection (x : W i), by
        rw [starProjection_fixed, avg]
        exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => hm g)⟩ : (H.d i j).domain) =
        (Fintype.card Γ : 𝕜)⁻¹ • ∑ g, ⟨_, hm g⟩ := by
      ext; simp [starProjection_fixed, avg]
    rw [e, LinearPMap.map_smul, show (H.d i j (∑ g, ⟨_, hm g⟩) : W j) =
      ∑ g, H.d i j ⟨_, hm g⟩ from map_sum (H.d i j).toFun _ _, starProjection_fixed, avg]
    simp only [A.comm]

/-- **The method of images**: the complex of `Γ`-fixed fields, with the restricted
differentials. -/
abbrev fixedComplex : HilbertComplex 𝕜 c fun i => A.fixed i :=
  A.reducingSubcomplex_fixed.toHilbertComplex

variable [Fintype ι] [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- `Γ`-symmetric data and forcing give `Γ`-symmetric solutions of the Hodge wave equation. -/
theorem propagates {a b : ℝ} {F U : ℝ → PiLp 2 W}
    (hU : Evolution.IsStrongSolution H.wave (Icc a b) F U) (h0 : U a ∈ totalSub A.fixed)
    (hF : ∀ t ∈ Icc a b, F t ∈ totalSub A.fixed) : ∀ t ∈ Icc a b, U t ∈ totalSub A.fixed :=
  A.reducingSubcomplex_fixed.propagates hU h0 hF

end Finite

/-! ### Equivariance of the wave group -/

section Total

variable [Fintype ι]

/-- The action on the total space. -/
def totalAct (g : Γ) : PiLp 2 W ≃ₗᵢ[𝕜] PiLp 2 W :=
  LinearIsometryEquiv.piLpCongrRight 2 fun i => A.act g i

theorem totalAct_apply (g : Γ) (x : PiLp 2 W) (i : ι) : A.totalAct g x i = A.act g i (x i) := rfl

/-- The action commutes with the wave operator. -/
theorem wave_totalAct (g : Γ) :
    Intertwines ((A.totalAct g : PiLp 2 W ≃ₗᵢ[𝕜] PiLp 2 W) : PiLp 2 W →L[𝕜] PiLp 2 W)
      H.wave H.wave := by
  have hmem : ∀ x : H.wave.domain, A.totalAct g (x : PiLp 2 W) ∈ H.wave.domain := fun x =>
    H.mem_wave_domain.2 ⟨fun i j => A.mapsTo g i j ⟨_, x.2.1 i j⟩,
      fun i j => (A.adjoint_comm g ⟨_, x.2.2 j i⟩).1⟩
  refine ⟨hmem, fun x => ?_⟩
  set x' : H.wave.domain := ⟨_, hmem x⟩
  change H.wave x' = A.totalAct g (H.wave x)
  refine PiLp.ext fun j => ?_
  rw [wave_apply, totalAct_apply, wave_apply, _root_.map_sub, map_sum, map_sum]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun i _ => A.comm g i j ⟨_, x.2.1 i j⟩)
    (Finset.sum_congr rfl fun k _ => (A.adjoint_comm g ⟨_, x.2.2 k j⟩).2)

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The wave group is equivariant**: `act g ∘ e^{tL} = e^{tL} ∘ act g`. -/
theorem totalAct_waveGroup (g : Γ) (t : ℝ) (x : PiLp 2 W) :
    A.totalAct g (H.waveGroup.S t x) = H.waveGroup.S t (A.totalAct g x) := by
  have h := A.wave_totalAct g
  rw [← generator_waveGroup] at h
  exact H.isIsometric_waveGroup.intertwines_S _ h t x

end Total

end Action

end Feec.HilbertComplex
