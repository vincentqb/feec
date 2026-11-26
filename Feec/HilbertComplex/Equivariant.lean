module

public import Feec.HilbertComplex.Transport

/-!
# Symmetries of Hilbert complexes: equivariance and the method of images

A unitary action of a group on a Hilbert complex commutes with the differentials and their
adjoints; for a finite group the fixed vectors form a reducing subcomplex, the complex of symmetric
fields of the method of images.
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

/-- A unitary action of a group `Γ` on a Hilbert complex, commuting with the differentials. -/
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

theorem starProjection_fixed (i : ι) (x : W i) : (A.fixed i).starProjection x = A.avg i x :=
  Submodule.eq_starProjection_of_mem_orthogonal (fun h => A.act_avg h i x)
    (A.sub_avg_mem_orthogonal i x)

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

/-- **The method of images**: the complex of `Γ`-fixed fields. -/
abbrev fixedComplex : HilbertComplex 𝕜 c fun i => A.fixed i :=
  A.reducingSubcomplex_fixed.toHilbertComplex

/-- `K ∩ Fix i`, as a subspace of `Fix i`, has an orthogonal projection when `K` has one. -/
instance comap_subtype_hasOrthogonalProjection (i : ι) (K : Submodule 𝕜 (W i))
    [K.HasOrthogonalProjection] : (K.comap (A.fixed i).subtype).HasOrthogonalProjection := by
  have hc : IsClosed (K.comap (A.fixed i).subtype : Set (A.fixed i)) :=
    (K.isClosed_of_hasOrthogonalProjection).preimage continuous_subtype_val
  have : CompleteSpace (K.comap (A.fixed i).subtype) := hc.completeSpace_coe
  infer_instance

theorem reducingSubcomplex_comap_fixed {K : ∀ i, Submodule 𝕜 (W i)}
    [∀ i, (K i).HasOrthogonalProjection] (hK : H.ReducingSubcomplex K)
    (hA : ∀ g i, ∀ x ∈ K i, A.act g i x ∈ K i) :
    A.fixedComplex.ReducingSubcomplex fun i => (K i).comap (A.fixed i).subtype := by
  have hS : ∀ i (x : A.fixed i), ∃ y : A.fixed i,
      A.reducingSubcomplex_fixed.toScaledEmbedding.J i y = (K i).starProjection
        (A.reducingSubcomplex_fixed.toScaledEmbedding.J i x) := by
    intro i x
    refine ⟨⟨(K i).starProjection x, fun g => ?_⟩, rfl⟩
    have e : (K i).starProjection (A.act g i x) = A.act g i ((K i).starProjection x) := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
        (hA g i _ ((K i).starProjection_apply_mem x)) fun k hk => ?_
      rw [← A.act_act_inv g i k, ← _root_.map_sub, LinearIsometryEquiv.inner_map_map]
      exact (K i).starProjection_inner_eq_zero _ _ (hA g⁻¹ i k hk)
    change A.act g i ((K i).starProjection x) = (K i).starProjection x
    rw [← e, x.2 g]
  exact A.reducingSubcomplex_fixed.toScaledEmbedding.reducingSubcomplex_comap hK hS

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

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

end Total

end Action

/-! ### Actions generated by commuting involutions -/

/-- Commuting unitary involutions of a Hilbert complex, commuting with the differentials. -/
structure Involutions (κ : Type*) where
  /-- the involutions -/
  R : κ → ∀ i, W i ≃ₗᵢ[𝕜] W i
  invol : ∀ k i x, R k i (R k i x) = x
  comm : ∀ k l i x, R k i (R l i x) = R l i (R k i x)
  mapsTo : ∀ k i j (x : (H.d i j).domain), R k i x ∈ (H.d i j).domain
  comm_d : ∀ k i j (x : (H.d i j).domain),
    H.d i j ⟨R k i x, mapsTo k i j x⟩ = R k j (H.d i j x)

namespace Involutions

variable {H} {κ : Type*} (I : H.Involutions κ)

theorem fam_mul_self (k : κ) : I.R k * I.R k = 1 :=
  funext fun i => LinearIsometryEquiv.ext (I.invol k i)

theorem commute_fam (k l : κ) : Commute (I.R k) (I.R l) :=
  funext fun i => LinearIsometryEquiv.ext (I.comm k l i)

theorem fam_pow_val_add (k : κ) (a b : ZMod 2) :
    I.R k ^ (a + b).val = I.R k ^ a.val * I.R k ^ b.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ (by rw [sq]; exact I.fam_mul_self k)]

/-- The unitaries commuting with the complex, as a submonoid of `∏ i, U(W i)`. -/
def commSub : Submonoid (∀ i, W i ≃ₗᵢ[𝕜] W i) where
  carrier := {u | ∀ i j (x : (H.d i j).domain),
    ∃ h : u i x ∈ (H.d i j).domain, H.d i j ⟨u i x, h⟩ = u j (H.d i j x)}
  one_mem' i j x := ⟨x.2, rfl⟩
  mul_mem' {u v} hu hv i j x := by
    obtain ⟨hv1, hv2⟩ := hv i j x
    obtain ⟨hu1, hu2⟩ := hu i j ⟨_, hv1⟩
    refine ⟨hu1, ?_⟩
    change H.d i j ⟨u i (v i x), hu1⟩ = u j (v j (H.d i j x))
    rw [← hv2]; exact hu2

theorem R_mem_commSub (k : κ) : I.R k ∈ commSub (H := H) := fun i j x =>
  ⟨I.mapsTo k i j x, I.comm_d k i j x⟩

/-- The stabilizer of a vector, as a submonoid of `∏ i, U(W i)`. -/
def stab (i : ι) (x : W i) : Submonoid (∀ i, W i ≃ₗᵢ[𝕜] W i) where
  carrier := {u | u i x = x}
  one_mem' := rfl
  mul_mem' {u v} hu hv := by
    change u i (v i x) = x
    rw [show v i x = x from hv]; exact hu

variable [Fintype κ]

omit [Fintype κ] in
theorem pairwise_commute (s : Finset κ) (n : κ → ℕ) :
    (s : Set κ).Pairwise (Function.onFun Commute fun k => I.R k ^ n k) :=
  fun k _ l _ _ => (I.commute_fam k l).pow_pow _ _

/-- `∏_k R_k^{g_k}` for `g ∈ (ℤ/2)^κ`. -/
def prod (g : Multiplicative (κ → ZMod 2)) : ∀ i, W i ≃ₗᵢ[𝕜] W i :=
  Finset.univ.noncommProd (fun k => I.R k ^ (Multiplicative.toAdd g k).val)
    (I.pairwise_commute _ fun k => (Multiplicative.toAdd g k).val)

theorem prod_one : I.prod 1 = 1 := by
  refine (Finset.noncommProd_eq_pow_card _ _ _ 1 fun k _ => ?_).trans (one_pow _)
  simp

theorem prod_mul (g h : Multiplicative (κ → ZMod 2)) : I.prod (g * h) = I.prod g * I.prod h := by
  have e : (fun k => I.R k ^ (Multiplicative.toAdd (g * h) k).val) =
      (fun k => I.R k ^ (Multiplicative.toAdd g k).val) *
        fun k => I.R k ^ (Multiplicative.toAdd h k).val := by
    funext k
    rw [toAdd_mul, Pi.add_apply, I.fam_pow_val_add, Pi.mul_apply]
  unfold prod
  simp_rw [e]
  exact Finset.noncommProd_mul_distrib _ _ _ _
    fun k _ l _ _ => (I.commute_fam k l).pow_pow _ _

theorem prod_mem_commSub (g : Multiplicative (κ → ZMod 2)) : I.prod g ∈ commSub (H := H) :=
  Submonoid.noncommProd_mem _ _ _ _ fun k _ => Submonoid.pow_mem _ (I.R_mem_commSub k) _

set_option backward.isDefEq.respectTransparency false in
theorem prod_single [DecidableEq κ] (k : κ) :
    I.prod (Multiplicative.ofAdd (Pi.single k 1)) = I.R k := by
  unfold prod
  rw [← Finset.mul_noncommProd_erase _ (Finset.mem_univ k),
    Finset.noncommProd_eq_pow_card _ _ _ 1 fun l hl => by
      have hl' : l ≠ k := (Finset.mem_erase.1 hl).1
      simp [hl'], one_pow, mul_one]
  simp [ZMod.val_one]

/-- **The action of `(ℤ/2)^κ` generated by commuting involutions**: `g ↦ ∏_k R_k^{g_k}`. -/
def toAction : H.Action (Multiplicative (κ → ZMod 2)) where
  act g := I.prod g
  act_one i x := by rw [I.prod_one]; rfl
  act_mul g h i x := by rw [I.prod_mul]; rfl
  mapsTo g i j x := (I.prod_mem_commSub g i j x).1
  comm g i j x := (I.prod_mem_commSub g i j x).2

@[simp] theorem toAction_act (g : Multiplicative (κ → ZMod 2)) (i : ι) :
    I.toAction.act g i = I.prod g i := rfl

theorem mem_fixed_toAction [DecidableEq κ] {i : ι} {x : W i} :
    x ∈ I.toAction.fixed i ↔ ∀ k, I.R k i x = x := by
  constructor
  · intro hx k
    have := hx (Multiplicative.ofAdd (Pi.single k 1))
    rwa [toAction_act, I.prod_single] at this
  · intro hx g
    exact show I.prod g ∈ stab i x from Submonoid.noncommProd_mem (stab i x) _ _
      (I.pairwise_commute _ _) fun k _ =>
        Submonoid.pow_mem _ (show I.R k ∈ stab i x from hx k) _

end Involutions

end Feec.HilbertComplex
