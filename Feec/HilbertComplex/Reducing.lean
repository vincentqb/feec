module

public import Feec.HilbertComplex.Short
public import Feec.Evolution.Constrained
public import Feec.Evolution.WellPosed
public import Feec.Semigroup.Invariance

/-!
# Reducing subcomplexes and constraint propagation for the Hodge wave equation

A reducing subcomplex is a family of closed subspaces `S i ⊆ W i` reducing every differential; its
total subspace reduces the wave operator `L`, so solutions with data and forcing in it stay in it.
A closed subspace reduces `L` iff the wave group leaves it invariant; for a graded complex and a
grading-invariant `K` with `D(L) ∩ K` dense, forward invariance suffices.

## Main results

* `HilbertComplex.ReducingSubcomplex.propagates`: constraint propagation.
* `HilbertComplex.isReducing_iff_waveGroup_invariant`: reducing iff invariant under `e^{tL}`.
* `HilbertComplex.isReducing_iff_forall_isStrongSolution`: the converse for graded complexes.
* `ShortHilbertComplex.divFree_propagates`: the constraint `{0} × N(d₀†) × Y` propagates.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

/-! ### Reducing pairs of a single operator -/

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {K : Submodule 𝕜 E} {L : Submodule 𝕜 F} [K.HasOrthogonalProjection]
  [L.HasOrthogonalProjection]

theorem isReducingPair_zero (K : Submodule 𝕜 E) (L : Submodule 𝕜 F) [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] : (0 : E →ₗ.[𝕜] F).IsReducingPair K L :=
  ⟨fun _ => Submodule.mem_top, fun x => by
    rw [apply_eq_zero_of_eq_zero rfl, apply_eq_zero_of_eq_zero rfl x]; exact (_root_.map_zero L.starProjection).symm⟩

theorem isReducingPair_of_eq_zero {T : E →ₗ.[𝕜] F} (hT : T = 0) : T.IsReducingPair K L := by
  subst hT; exact isReducingPair_zero K L

theorem isReducingPair_of_orthogonal_le_ker {T : E →ₗ.[𝕜] F} (hK : Kᗮ ≤ T.ker)
    (hL : ∀ x : T.domain, T x ∈ L) : T.IsReducingPair K L := by
  have hz : ∀ x : T.domain, (x : E) - K.starProjection x ∈ T.ker := fun x =>
    hK (K.sub_starProjection_mem_orthogonal _)
  have hmem : ∀ x : T.domain, K.starProjection (x : E) ∈ T.domain := fun x => by
    have := T.domain.sub_mem x.2 (T.ker_le_domain (hz x))
    rwa [sub_sub_cancel] at this
  refine ⟨hmem, fun x => ?_⟩
  have e : (⟨_, hmem x⟩ : T.domain) = x - ⟨_, T.ker_le_domain (hz x)⟩ :=
    Subtype.ext (by simp)
  rw [e, LinearPMap.map_sub, (coe_mem_ker_iff (x := ⟨_, T.ker_le_domain (hz x)⟩)).1 (hz x),
    sub_zero, (L.starProjection_eq_self_iff).2 (hL x)]

theorem isReducingPair_of_le_ker {T : E →ₗ.[𝕜] F} (hK : K ≤ T.ker)
    (hL : ∀ x : T.domain, T x ∈ Lᗮ) : T.IsReducingPair K L := by
  have hk : ∀ x : T.domain, K.starProjection (x : E) ∈ T.ker := fun x =>
    hK (K.starProjection_apply_mem _)
  refine ⟨fun x => T.ker_le_domain (hk x), fun x => ?_⟩
  rw [(coe_mem_ker_iff (x := ⟨_, T.ker_le_domain (hk x)⟩)).1 (hk x),
    (Submodule.starProjection_apply_eq_zero_iff L).2 (hL x)]

variable {T T' : E →ₗ.[𝕜] F}

theorem IsReducingPair.add (h : T.IsReducingPair K L) (h' : T'.IsReducingPair K L) :
    (T + T').IsReducingPair K L := by
  refine ⟨fun x => Submodule.mem_inf.2 ⟨h.proj_mem ⟨x, (Submodule.mem_inf.1 x.2).1⟩,
    h'.proj_mem ⟨x, (Submodule.mem_inf.1 x.2).2⟩⟩, fun x => ?_⟩
  have e1 := h.comm ⟨x, (Submodule.mem_inf.1 x.2).1⟩
  have e2 := h'.comm ⟨x, (Submodule.mem_inf.1 x.2).2⟩
  change T ⟨_, h.proj_mem ⟨x, (Submodule.mem_inf.1 x.2).1⟩⟩ +
      T' ⟨_, h'.proj_mem ⟨x, (Submodule.mem_inf.1 x.2).2⟩⟩ =
    L.starProjection (T ⟨x, (Submodule.mem_inf.1 x.2).1⟩ + T' ⟨x, (Submodule.mem_inf.1 x.2).2⟩)
  rw [_root_.map_add, ← e1, ← e2]

theorem IsReducingPair.neg (h : T.IsReducingPair K L) : (-T).IsReducingPair K L :=
  ⟨fun x => h.proj_mem x, fun x => by
    change -(T ⟨_, h.proj_mem x⟩) = L.starProjection (-(T x))
    rw [_root_.map_neg, h.comm x]⟩

theorem IsReducingPair.sub (h : T.IsReducingPair K L) (h' : T'.IsReducingPair K L) :
    (T - T').IsReducingPair K L := by
  refine ⟨fun x => Submodule.mem_inf.2 ⟨h.proj_mem ⟨x, (Submodule.mem_inf.1 x.2).1⟩,
    h'.proj_mem ⟨x, (Submodule.mem_inf.1 x.2).2⟩⟩, fun x => ?_⟩
  have e1 := h.comm ⟨x, (Submodule.mem_inf.1 x.2).1⟩
  have e2 := h'.comm ⟨x, (Submodule.mem_inf.1 x.2).2⟩
  change T ⟨_, h.proj_mem ⟨x, (Submodule.mem_inf.1 x.2).1⟩⟩ -
      T' ⟨_, h'.proj_mem ⟨x, (Submodule.mem_inf.1 x.2).2⟩⟩ =
    L.starProjection (T ⟨x, (Submodule.mem_inf.1 x.2).1⟩ - T' ⟨x, (Submodule.mem_inf.1 x.2).2⟩)
  rw [_root_.map_sub, ← e1, ← e2]

end LinearPMap

/-! ### Intertwining isometric groups -/

namespace Feec.C0Group

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
  [CompleteSpace F]
  {G : C0Group 𝕜 E} {G' : C0Group 𝕜 F}

theorem IsIsometric.intertwines_S (hG' : G'.IsIsometric) (J : E →L[𝕜] F)
    (hJ : Intertwines J G.generator G'.generator) (t : ℝ) (x : E) :
    J (G.S t x) = G'.S t (J x) := by
  set B := G'.generator
  have hD : ∀ x : G.generator.domain, J (G.S t x) = G'.S t (J x) := by
    intro x
    have hm1 : ∀ s, J (G.S s x) ∈ B.domain := fun s => hJ.mapsTo ⟨_, G.mapsTo_domain x s⟩
    have hm2 : ∀ s, G'.S s (J x) ∈ B.domain := fun s => G'.mapsTo_domain ⟨_, hJ.mapsTo x⟩ s
    set e : ℝ → F := fun s => J (G.S s x) - G'.S s (J x)
    have hmem : ∀ s, e s ∈ B.domain := fun s => B.domain.sub_mem (hm1 s) (hm2 s)
    have hde : ∀ s, HasDerivAt e (B ⟨e s, hmem s⟩) s := by
      intro s
      have h1 := (J.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (G.hasDerivAt_apply' x s)
      have h2 := G'.hasDerivAt_apply' ⟨_, hJ.mapsTo x⟩ s
      have e1 : B ⟨J (G.S s x), hm1 s⟩ = J (G.generator ⟨G.S s x, G.mapsTo_domain x s⟩) :=
        hJ.comm ⟨_, G.mapsTo_domain x s⟩
      have e3 : (⟨e s, hmem s⟩ : B.domain) = ⟨J (G.S s x), hm1 s⟩ - ⟨G'.S s (J x), hm2 s⟩ := rfl
      rw [e3, LinearPMap.map_sub, e1]
      exact h1.sub h2
    have h0 := hG'.isSkewSymmetric_generator.eq_zero_of_hasDerivAt hmem hde (by simp [e, C0Group.S_zero_apply]) t
    exact sub_eq_zero.1 h0
  have := Continuous.ext_on G.dense_domain_generator (J.continuous.comp (G.S t).continuous)
    ((G'.S t).continuous.comp J.continuous) (fun x hx => hD ⟨x, hx⟩)
  exact congrFun this x

theorem IsIsometric.antiIntertwines_S (hG : G.IsIsometric) (J : E →L[𝕜] E)
    (hJ : Intertwines J G.generator (-G.generator)) (t : ℝ) (x : E) :
    J (G.S t x) = G.S (-t) (J x) := by
  set A := G.generator
  have hD : ∀ x : A.domain, J (G.S t x) = G.S (-t) (J x) := by
    intro x
    have hJm : ∀ y : A.domain, J y ∈ A.domain := hJ.mapsTo
    have hm1 : ∀ s, J (G.S s x) ∈ A.domain := fun s => hJm ⟨_, G.mapsTo_domain x s⟩
    have hm2 : ∀ s, G.S (-s) (J x) ∈ A.domain := fun s => G.mapsTo_domain ⟨_, hJm x⟩ (-s)
    set e : ℝ → E := fun s => J (G.S s x) - G.S (-s) (J x)
    have hmem : ∀ s, e s ∈ (-A).domain := fun s => A.domain.sub_mem (hm1 s) (hm2 s)
    have hde : ∀ s, HasDerivAt e ((-A) ⟨e s, hmem s⟩) s := by
      intro s
      have h1 := J.hasDerivAt_apply_of_hasDerivAt (G.hasDerivAt_apply' x s)
      have h2 := (G.hasDerivAt_apply' ⟨_, hJm x⟩ (-s)).scomp s (hasDerivAt_neg s)
      have e1 : (-A) ⟨J (G.S s x), hm1 s⟩ = J (A ⟨G.S s x, G.mapsTo_domain x s⟩) :=
        hJ.comm ⟨_, G.mapsTo_domain x s⟩
      have e3 : (⟨e s, hmem s⟩ : (-A).domain) =
          ⟨J (G.S s x), hm1 s⟩ - ⟨G.S (-s) (J x), hm2 s⟩ := rfl
      rw [e3, LinearPMap.map_sub, e1]
      refine (h1.sub h2).congr_deriv ?_
      rw [LinearPMap.neg_apply, neg_one_smul]
    have h0 := hG.isSkewSymmetric_generator.neg.eq_zero_of_hasDerivAt hmem hde (by simp [e, C0Group.S_zero_apply]) t
    exact sub_eq_zero.1 h0
  have := Continuous.ext_on G.dense_domain_generator (J.continuous.comp (G.S t).continuous)
    ((G.S (-t)).continuous.comp J.continuous) (fun x hx => hD ⟨x, hx⟩)
  exact congrFun this x

theorem IsIsometric.isReducing_of_forward_invariant (hG : G.IsIsometric) (R : E →L[𝕜] E)
    (hR : Intertwines R G.generator (-G.generator)) (hRR : ∀ x, R (R x) = x)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (hRK : ∀ x ∈ K, R x ∈ K)
    (hdense : ∀ k ∈ K, k ∈ closure ((G.generator.domain : Set E) ∩ K))
    (hfwd : ∀ t, 0 ≤ t → ∀ x ∈ G.generator.domain, x ∈ K → G.S t x ∈ K) :
    G.generator.IsReducing K := by
  have hall : ∀ t, ∀ x ∈ G.generator.domain, x ∈ K → G.S t x ∈ K := by
    intro t x hx hxK
    rcases le_total 0 t with ht | ht
    · exact hfwd t ht x hx hxK
    · have hRx : R x ∈ G.generator.domain := hR.mapsTo ⟨x, hx⟩
      have := hRK _ (hfwd (-t) (neg_nonneg.2 ht) _ hRx (hRK x hxK))
      rwa [hG.antiIntertwines_S R hR, neg_neg, hRR] at this
  have hKc : IsClosed (K : Set E) := by
    rw [← Submodule.orthogonal_orthogonal K]; exact Submodule.isClosed_orthogonal _
  refine hG.isReducing_of_invariant fun t k hk => ?_
  have : G.S t k ∈ closure (G.S t '' ((G.generator.domain : Set E) ∩ K)) :=
    mem_closure_image (G.S t).continuous.continuousAt (hdense k hk)
  refine closure_minimal ?_ hKc this
  rintro _ ⟨x, ⟨hxD, hxK⟩, rfl⟩
  exact hall t x hxD hxK

end Feec.C0Group

/-! ### The total subspace of a family of subspaces -/

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]

section TotalSub

/-- The subspace `∏ S i` of the total space `PiLp 2 W`. -/
def totalSub (S : ∀ i, Submodule 𝕜 (W i)) : Submodule 𝕜 (PiLp 2 W) where
  carrier := {x | ∀ i, x i ∈ S i}
  add_mem' hx hy i := (S i).add_mem (hx i) (hy i)
  zero_mem' i := (S i).zero_mem
  smul_mem' a _ hx i := (S i).smul_mem a (hx i)

variable {S : ∀ i, Submodule 𝕜 (W i)}

@[simp] theorem mem_totalSub {x : PiLp 2 W} : x ∈ totalSub S ↔ ∀ i, x i ∈ S i := Iff.rfl

theorem totalSub_mono {S' : ∀ i, Submodule 𝕜 (W i)} (h : ∀ i, S i ≤ S' i) :
    totalSub S ≤ totalSub S' := fun _ hx i => h i (hx i)

/-- The componentwise projection `∏ P_{S i}`. -/
def totalProj (S : ∀ i, Submodule 𝕜 (W i)) [∀ i, (S i).HasOrthogonalProjection]
    (x : PiLp 2 W) : PiLp 2 W :=
  WithLp.toLp 2 fun i => (S i).starProjection (x i)

theorem totalProj_apply [∀ i, (S i).HasOrthogonalProjection] (x : PiLp 2 W) (i : ι) :
    totalProj S x i = (S i).starProjection (x i) := rfl

variable [∀ i, (S i).HasOrthogonalProjection]

theorem totalProj_mem (x : PiLp 2 W) : totalProj S x ∈ totalSub S := fun i =>
  (S i).starProjection_apply_mem _

variable [Fintype ι]

theorem sub_totalProj_mem_orthogonal (x : PiLp 2 W) : x - totalProj S x ∈ (totalSub S)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro k hk
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [PiLp.sub_apply, totalProj_apply]
  exact Submodule.inner_right_of_mem_orthogonal (hk i) ((S i).sub_starProjection_mem_orthogonal _)

instance : (totalSub S).HasOrthogonalProjection :=
  ⟨fun x => ⟨_, totalProj_mem x, sub_totalProj_mem_orthogonal x⟩⟩

theorem totalSub_starProjection_apply (x : PiLp 2 W) (i : ι) :
    (totalSub S).starProjection x i = (S i).starProjection (x i) := by
  rw [Submodule.eq_starProjection_of_mem_orthogonal (totalProj_mem x)
    (sub_totalProj_mem_orthogonal x)]
  rfl

theorem isClosed_totalSub : IsClosed (totalSub S : Set (PiLp 2 W)) := by
  rw [← Submodule.orthogonal_orthogonal (totalSub S)]
  exact Submodule.isClosed_orthogonal _

end TotalSub

variable [∀ i, CompleteSpace (W i)]

/-! ### Reducing subcomplexes -/

variable (H : HilbertComplex 𝕜 c W)

/-- A reducing subcomplex: closed subspaces `S i ⊆ W i` reducing every differential. -/
structure ReducingSubcomplex (S : ∀ i, Submodule 𝕜 (W i)) [∀ i, (S i).HasOrthogonalProjection] :
    Prop where
  reduces : ∀ i j, (H.d i j).IsReducingPair (S i) (S j)

namespace ReducingSubcomplex

variable {H} {S : ∀ i, Submodule 𝕜 (W i)} [∀ i, (S i).HasOrthogonalProjection]

theorem of_rel (h : ∀ i j, c.Rel i j → (H.d i j).IsReducingPair (S i) (S j)) :
    H.ReducingSubcomplex S :=
  ⟨fun i j => by
    by_cases hij : c.Rel i j
    exacts [h i j hij, isReducingPair_of_eq_zero (H.shape i j hij)]⟩

theorem top : H.ReducingSubcomplex fun i => (⊤ : Submodule 𝕜 (W i)) :=
  ⟨fun _ _ => isReducingPair_top _⟩

theorem orthogonal (h : H.ReducingSubcomplex S) : H.ReducingSubcomplex fun i => (S i)ᗮ :=
  ⟨fun i j => (h.reduces i j).orthogonal⟩

theorem dual (h : H.ReducingSubcomplex S) : H.dual.ReducingSubcomplex S :=
  ⟨fun i j => (h.reduces j i).adjoint (H.dense j i)⟩

theorem mapsTo (h : H.ReducingSubcomplex S) {i j : ι} (x : (H.d i j).domain)
    (hx : (x : W i) ∈ S i) : H.d i j x ∈ S j :=
  (h.reduces i j).mapsTo x hx

variable [Fintype ι]

theorem isReducing_totalD (h : H.ReducingSubcomplex S) : H.totalD.IsReducing (totalSub S) := by
  have hmem : ∀ x : H.totalD.domain, (totalSub S).starProjection (x : PiLp 2 W) ∈
      H.totalD.domain := fun x i j => by
    rw [totalSub_starProjection_apply]
    exact (h.reduces i j).proj_mem ⟨_, x.2 i j⟩
  refine ⟨hmem, fun x => PiLp.ext fun j => ?_⟩
  rw [totalD_apply, totalSub_starProjection_apply, totalD_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (h.reduces i j).comm ⟨_, x.2 i j⟩]
  exact apply_congr' _ _ _ (totalSub_starProjection_apply _ _)

theorem isReducing_dual_totalD (h : H.ReducingSubcomplex S) :
    H.dual.totalD.IsReducing (totalSub S) :=
  h.dual.isReducing_totalD

theorem isReducing_wave (h : H.ReducingSubcomplex S) : H.wave.IsReducing (totalSub S) :=
  h.isReducing_totalD.sub h.isReducing_dual_totalD

theorem isReducing_neg_wave (h : H.ReducingSubcomplex S) : (-H.wave).IsReducing (totalSub S) :=
  h.isReducing_wave.neg

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **Constraint propagation**: strong solutions of `U' = L U + F` with `U a`, `F` in `∏ S i` stay
in `∏ S i`. [QuennevilleBelair2015], Props 4.16, 4.17, 4.19 (adapted) -/
theorem propagates (h : H.ReducingSubcomplex S) {a b : ℝ} {F U : ℝ → PiLp 2 W}
    (hU : Evolution.IsStrongSolution H.wave (Icc a b) F U) (h0 : U a ∈ totalSub S)
    (hF : ∀ t ∈ Icc a b, F t ∈ totalSub S) : ∀ t ∈ Icc a b, U t ∈ totalSub S :=
  hU.mem_of_isReducing H.isSkewAdjoint_wave.isDissipative h.isReducing_wave h0 hF

theorem propagates_neg (h : H.ReducingSubcomplex S) {a b : ℝ} {F U : ℝ → PiLp 2 W}
    (hU : Evolution.IsStrongSolution (-H.wave) (Icc a b) F U) (h0 : U a ∈ totalSub S)
    (hF : ∀ t ∈ Icc a b, F t ∈ totalSub S) : ∀ t ∈ Icc a b, U t ∈ totalSub S :=
  hU.mem_of_isReducing H.isSkewAdjoint_wave.neg.isDissipative h.isReducing_neg_wave h0 hF

theorem existsUnique_mem (h : H.ReducingSubcomplex S) {U₀ : PiLp 2 W} (hU₀ : U₀ ∈ H.wave.domain)
    (hU₀S : U₀ ∈ totalSub S) {F : ℝ → PiLp 2 W} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible H.wave a b F) (hFS : ∀ t ∈ Icc a b, F t ∈ totalSub S) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution H.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ totalSub S) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution H.wave (Icc a b) F V → EqOn V U (Icc a b) := by
  obtain ⟨U, hU0, hU, huniq⟩ := H.isSkewAdjoint_wave.existsUnique_classicalSolution hU₀ hF
  exact ⟨U, hU0, hU, h.propagates hU.toIsStrongSolution (hU0 ▸ hU₀S) hFS, huniq⟩

end ReducingSubcomplex

/-! ### The wave group -/

section WaveGroup

variable [Fintype ι] [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- The wave group `e^{tL}` of a finite Hilbert complex. -/
def waveGroup : C0Group 𝕜 (PiLp 2 W) := H.isSkewAdjoint_wave.group

theorem isIsometric_waveGroup : H.waveGroup.IsIsometric := H.isSkewAdjoint_wave.isIsometric_group

@[simp] theorem generator_waveGroup : H.waveGroup.generator = H.wave :=
  H.isSkewAdjoint_wave.generator_group

/-- **Reducing subspaces of `L` are the invariant subspaces of the wave group**: a closed `K`
reduces `L` iff `e^{tL} K ⊆ K` for every `t`. [QuennevilleBelair2015], Prop 4.17 -/
theorem isReducing_iff_waveGroup_invariant (K : Submodule 𝕜 (PiLp 2 W))
    [K.HasOrthogonalProjection] :
    H.wave.IsReducing K ↔ ∀ t, K.map (H.waveGroup.S t : PiLp 2 W →ₗ[𝕜] PiLp 2 W) ≤ K := by
  rw [← (H.isIsometric_waveGroup).isReducing_iff_invariant, generator_waveGroup]

theorem isReducing_invariantCore_waveGroup (K : Submodule 𝕜 (PiLp 2 W))
    [K.HasOrthogonalProjection] : H.wave.IsReducing (H.waveGroup.invariantCore K) := by
  have := H.isIsometric_waveGroup.isReducing_invariantCore (K := K)
  rwa [generator_waveGroup] at this

theorem le_invariantCore_waveGroup {K M : Submodule 𝕜 (PiLp 2 W)} [M.HasOrthogonalProjection]
    (hMK : M ≤ K) (hM : H.wave.IsReducing M) : M ≤ H.waveGroup.invariantCore K :=
  H.isIsometric_waveGroup.le_invariantCore_of_isReducing hMK (by rwa [generator_waveGroup])

namespace ReducingSubcomplex

variable {H} {S : ∀ i, Submodule 𝕜 (W i)} [∀ i, (S i).HasOrthogonalProjection]

theorem waveGroup_mem (h : H.ReducingSubcomplex S) (t : ℝ) {x : PiLp 2 W}
    (hx : x ∈ totalSub S) : H.waveGroup.S t x ∈ totalSub S :=
  C0Group.map_le_iff_forall.1 ((H.isReducing_iff_waveGroup_invariant _).1 h.isReducing_wave)
    t x hx

theorem invariantCore_eq (h : H.ReducingSubcomplex S) :
    H.waveGroup.invariantCore (totalSub S) = totalSub S :=
  C0Group.invariantCore_eq_self_iff.2 ((H.isReducing_iff_waveGroup_invariant _).1
    h.isReducing_wave)

end ReducingSubcomplex

end WaveGroup

/-! ### Gradings reverse time -/

section Reversal

/-- The sign `-1` on odd, `1` on even indices of a parity `p : ι → Bool`. -/
def paritySign (p : ι → Bool) (i : ι) : 𝕜 := if p i then -1 else 1

theorem paritySign_eq_neg {p : ι → Bool} {i j : ι} (h : p j ≠ p i) :
    (paritySign p i : 𝕜) = -paritySign p j := by
  unfold paritySign
  cases hi : p i <;> cases hj : p j <;> simp_all

theorem paritySign_mul_self (p : ι → Bool) (i : ι) :
    (paritySign p i : 𝕜) * paritySign p i = 1 := by
  unfold paritySign; split_ifs <;> simp

variable [Fintype ι]

variable (𝕜) in
/-- The grading operator `(R x) i = ± x i` of a parity `p : ι → Bool` (`-` where `p i`). -/
def reversal (p : ι → Bool) : PiLp 2 W ≃ₗᵢ[𝕜] PiLp 2 W :=
  LinearIsometryEquiv.piLpCongrRight 2 fun i =>
    if p i then LinearIsometryEquiv.neg 𝕜 else LinearIsometryEquiv.refl 𝕜 (W i)

omit [∀ i, CompleteSpace (W i)] in
theorem reversal_apply (p : ι → Bool) (x : PiLp 2 W) (i : ι) :
    reversal 𝕜 p x i = (paritySign p i : 𝕜) • x i := by
  simp only [reversal, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply, paritySign]
  split_ifs <;> simp

omit [∀ i, CompleteSpace (W i)] in
theorem reversal_reversal (p : ι → Bool) (x : PiLp 2 W) :
    reversal 𝕜 p (reversal 𝕜 p x) = x :=
  PiLp.ext fun i => by rw [reversal_apply, reversal_apply, smul_smul, paritySign_mul_self, one_smul]

theorem wave_reversal {p : ι → Bool} (hp : ∀ i j, c.Rel i j → p j ≠ p i) :
    Intertwines ((reversal 𝕜 p : PiLp 2 W ≃ₗᵢ[𝕜] PiLp 2 W) : PiLp 2 W →L[𝕜] PiLp 2 W) H.wave
      (-H.wave) := by
  have hmem : ∀ x : H.wave.domain, reversal 𝕜 p (x : PiLp 2 W) ∈ H.wave.domain := fun x => by
    refine H.mem_wave_domain.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [reversal_apply]; exact Submodule.smul_mem _ _ (x.2.1 i j)
    · rw [reversal_apply]; exact Submodule.smul_mem _ _ (x.2.2 j i)
  refine ⟨hmem, fun x => ?_⟩
  set x' : H.wave.domain := ⟨_, hmem x⟩
  change (-H.wave) x' = reversal 𝕜 p (H.wave x)
  refine PiLp.ext fun j => ?_
  have h1 : ∀ i, H.d i j ⟨(x' : PiLp 2 W) i, x'.2.1 i j⟩ =
      -((paritySign p j : 𝕜) • H.d i j ⟨(x : PiLp 2 W) i, x.2.1 i j⟩) := by
    intro i
    have e : H.d i j ⟨(x' : PiLp 2 W) i, x'.2.1 i j⟩ =
        (paritySign p i : 𝕜) • H.d i j ⟨(x : PiLp 2 W) i, x.2.1 i j⟩ := by
      rw [← LinearPMap.map_smul]; exact apply_congr' _ _ _ (reversal_apply _ _ _)
    rw [e]
    by_cases hij : c.Rel i j
    · rw [paritySign_eq_neg (hp i j hij), neg_smul]
    · rw [H.apply_eq_zero_of_not_rel hij, smul_zero, smul_zero, neg_zero]
  have h2 : ∀ k, (H.d j k)† ⟨(x' : PiLp 2 W) k, x'.2.2 k j⟩ =
      -((paritySign p j : 𝕜) • (H.d j k)† ⟨(x : PiLp 2 W) k, x.2.2 k j⟩) := by
    intro k
    have e : (H.d j k)† ⟨(x' : PiLp 2 W) k, x'.2.2 k j⟩ =
        (paritySign p k : 𝕜) • (H.d j k)† ⟨(x : PiLp 2 W) k, x.2.2 k j⟩ := by
      rw [← LinearPMap.map_smul]; exact apply_congr' _ _ _ (reversal_apply _ _ _)
    rw [e]
    by_cases hjk : c.Rel j k
    · rw [paritySign_eq_neg (hp j k hjk).symm, neg_smul]
    · rw [adjoint_apply_eq_zero_of_eq_zero (H.shape j k hjk), smul_zero, smul_zero, neg_zero]
  rw [LinearPMap.neg_apply, PiLp.neg_apply, wave_apply, reversal_apply, wave_apply]
  simp only [h1, h2, Finset.sum_neg_distrib, ← Finset.smul_sum, smul_sub]
  abel

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

theorem reversal_waveGroup {p : ι → Bool} (hp : ∀ i j, c.Rel i j → p j ≠ p i) (t : ℝ)
    (x : PiLp 2 W) : reversal 𝕜 p (H.waveGroup.S t x) = H.waveGroup.S (-t) (reversal 𝕜 p x) := by
  have h := H.wave_reversal hp
  rw [← generator_waveGroup] at h
  exact H.isIsometric_waveGroup.antiIntertwines_S _ h t x

theorem isReducing_iff_forall_nonneg {p : ι → Bool} (hp : ∀ i j, c.Rel i j → p j ≠ p i)
    (K : Submodule 𝕜 (PiLp 2 W)) [K.HasOrthogonalProjection]
    (hRK : ∀ x ∈ K, reversal 𝕜 p x ∈ K)
    (hdense : ∀ k ∈ K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ K)) :
    H.wave.IsReducing K ↔
      ∀ t, 0 ≤ t → ∀ x ∈ H.wave.domain, x ∈ K → H.waveGroup.S t x ∈ K := by
  refine ⟨fun h t _ x _ hx => C0Group.map_le_iff_forall.1
    ((H.isReducing_iff_waveGroup_invariant K).1 h) t x hx, fun h => ?_⟩
  have hR := H.wave_reversal (𝕜 := 𝕜) hp
  rw [← generator_waveGroup] at hR ⊢
  exact H.isIsometric_waveGroup.isReducing_of_forward_invariant _ hR (reversal_reversal p) K hRK
    (by rwa [generator_waveGroup]) (by rwa [generator_waveGroup])

/-- For a graded complex and a closed `R`-invariant `K` with `D(L) ∩ K` dense, `K` reduces `L` iff
solutions from `K` stay in `K`. [QuennevilleBelair2015], Prop 4.17 (adapted) -/
theorem isReducing_iff_forall_isStrongSolution {p : ι → Bool}
    (hp : ∀ i j, c.Rel i j → p j ≠ p i) (K : Submodule 𝕜 (PiLp 2 W)) [K.HasOrthogonalProjection]
    (hRK : ∀ x ∈ K, reversal 𝕜 p x ∈ K)
    (hdense : ∀ k ∈ K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ K)) :
    H.wave.IsReducing K ↔ ∀ (T : ℝ) (U : ℝ → PiLp 2 W), U 0 ∈ K →
      Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U → ∀ t ∈ Icc 0 T, U t ∈ K := by
  refine ⟨fun hK T U h0 hU => hU.mem_of_isReducing H.isSkewAdjoint_wave.isDissipative hK h0
    fun _ _ => K.zero_mem, fun h => ?_⟩
  refine (H.isReducing_iff_forall_nonneg hp K hRK hdense).2 fun t ht x hx hxK => ?_
  have hU := H.waveGroup.toC0Semigroup.isClassicalSolution_orbit (U₀ := x)
    (by rw [show H.waveGroup.toC0Semigroup.generator = H.wave from H.generator_waveGroup];
        exact hx) 0 t
  rw [show H.waveGroup.toC0Semigroup.generator = H.wave from H.generator_waveGroup] at hU
  simpa [sub_zero] using h t _ (by simpa using hxK) hU.toIsStrongSolution t ⟨ht, le_rfl⟩

end Reversal

end Feec.HilbertComplex

/-! ### Gradings of windows and of `ℤ` -/

theorem ComplexShape.window_parity {n : ℕ} {i j : Fin n} (h : (ComplexShape.window n).Rel i j) :
    decide (Odd j.val) ≠ decide (Odd i.val) := by
  rw [ComplexShape.window_rel] at h
  rw [← h]
  by_cases hi : Odd i.val <;> simp [hi, Nat.odd_add_one]

/-! ### The divergence constraint of a short complex (Prop 4.16) -/

namespace Feec.ShortHilbertComplex

universe u

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]
  (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂) (Y : Submodule 𝕜 W₂) [Y.HasOrthogonalProjection]

/-- The constraint family `{0} × N(d₀†) × Y`. [QuennevilleBelair2015], Prop 4.16 -/
def divFreeSub : ∀ i : Fin 3, Submodule 𝕜 (W3 W₀ W₁ W₂ i)
  | 0 => (⊥ : Submodule 𝕜 W₀)
  | 1 => ((S.d₀†).ker : Submodule 𝕜 W₁)
  | 2 => Y

instance instHasOrthogonalProjectionDivFreeSub :
    ∀ i, (S.divFreeSub Y i).HasOrthogonalProjection
  | 0 => inferInstanceAs (⊥ : Submodule 𝕜 W₀).HasOrthogonalProjection
  | 1 => (hasOrthogonalProjection_ker S.d₀† (adjoint_isClosed S.dense₀) :
      (S.d₀†).ker.HasOrthogonalProjection)
  | 2 => inferInstanceAs Y.HasOrthogonalProjection

theorem reducingSubcomplex_divFreeSub (hY : ∀ x : S.d₁.domain, S.d₁ x ∈ Y) :
    S.toHilbertComplex.ReducingSubcomplex (S.divFreeSub Y) := by
  have := hasOrthogonalProjection_ker S.d₀† (adjoint_isClosed S.dense₀)
  refine HilbertComplex.ReducingSubcomplex.of_rel fun i j hij => ?_
  fin_cases i <;> fin_cases j <;> simp at hij
  · change S.d₀.IsReducingPair (⊥ : Submodule 𝕜 W₀) (S.d₀†).ker
    refine isReducingPair_of_le_ker bot_le fun x => ?_
    rw [Submodule.mem_orthogonal]
    intro y hy
    obtain ⟨z, hz, hz0⟩ := mem_ker_iff.1 hy
    have h := adjoint_isFormalAdjoint S.dense₀ z x
    rw [hz0, inner_zero_left] at h
    rw [hz]; exact h.symm
  · change S.d₁.IsReducingPair (S.d₀†).ker Y
    exact isReducingPair_of_orthogonal_le_ker
      (S.toHilbertComplex.orthogonal_ker_adjoint_le_ker 0 1 2) hY

variable [NormedSpace ℝ W₀] [IsScalarTower ℝ 𝕜 W₀] [NormedSpace ℝ W₁] [IsScalarTower ℝ 𝕜 W₁]
  [NormedSpace ℝ W₂] [IsScalarTower ℝ 𝕜 W₂]

instance instNormedSpaceRealW3 : ∀ i, NormedSpace ℝ (W3 W₀ W₁ W₂ i)
  | 0 => inferInstanceAs (NormedSpace ℝ W₀)
  | 1 => inferInstanceAs (NormedSpace ℝ W₁)
  | 2 => inferInstanceAs (NormedSpace ℝ W₂)

instance instIsScalarTowerRealW3 : ∀ i, IsScalarTower ℝ 𝕜 (W3 W₀ W₁ W₂ i)
  | 0 => inferInstanceAs (IsScalarTower ℝ 𝕜 W₀)
  | 1 => inferInstanceAs (IsScalarTower ℝ 𝕜 W₁)
  | 2 => inferInstanceAs (IsScalarTower ℝ 𝕜 W₂)

/-- **Propagation of the divergence constraint**: for closed `Y ⊇ R(d₁)`, strong solutions with data
and forcing in `{0} × N(d₀†) × Y` stay there. [QuennevilleBelair2015], Prop 4.16 (adapted) -/
theorem divFree_propagates (hY : ∀ x : S.d₁.domain, S.d₁ x ∈ Y) {a b : ℝ}
    {F U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)} (hU : Evolution.IsStrongSolution S.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub (S.divFreeSub Y))
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub (S.divFreeSub Y)) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub (S.divFreeSub Y) :=
  (S.reducingSubcomplex_divFreeSub Y hY).propagates hU h0 hF

theorem divFree_propagates_neg (hY : ∀ x : S.d₁.domain, S.d₁ x ∈ Y) {a b : ℝ}
    {F U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)} (hU : Evolution.IsStrongSolution (-S.wave) (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub (S.divFreeSub Y))
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub (S.divFreeSub Y)) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub (S.divFreeSub Y) :=
  (S.reducingSubcomplex_divFreeSub Y hY).propagates_neg hU h0 hF

end Feec.ShortHilbertComplex
