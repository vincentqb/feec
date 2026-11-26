module

public import Feec.HilbertComplex.Approximation.DissipFEEC
public import Feec.Semigroup.Invariance

/-!
# The skew-adjoint FEEC theorem

A skew FEEC discretization of `ξ' = A ξ`, `A` skew-adjoint, is a dissipative FEEC discretization
with skew discrete generators; its exact flow extends to Stone's isometric group `U(t)`, `t ∈ ℝ`.

## Main results

* `skewFEEC`: the skew-adjoint FEEC theorem.
* `skewFEEC_isReducing_iff_invariant`: `K` reduces `A` iff `U(t) K ⊆ K` for every `t ∈ ℝ`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

/-! ### Skew bounded generators -/

section Bounded

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X] [NormedSpace ℝ X]
  [IsScalarTower ℝ 𝕜 X]

omit [CompleteSpace X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
theorem re_inner_self_eq_zero_of_skew {L : X →L[𝕜] X} (hL : ∀ x y, ⟪L x, y⟫_𝕜 = -⟪x, L y⟫_𝕜)
    (x : X) : RCLike.re ⟪L x, x⟫_𝕜 = 0 := by
  have : RCLike.re ⟪L x, x⟫_𝕜 = - RCLike.re ⟪L x, x⟫_𝕜 := by
    conv_rhs => rw [hL x x, _root_.map_neg, ← inner_conj_symm, RCLike.conj_re]
    simp
  linarith

theorem eq_ofBounded_of_hasDerivAt (L : X →L[𝕜] X) (hL : ∀ x y, ⟪L x, y⟫_𝕜 = -⟪x, L y⟫_𝕜)
    {u : ℝ → X} (hu : ∀ t, HasDerivAt u (L (u t)) t) (t : ℝ) :
    u t = (C0Group.ofBounded L).S t (u 0) := by
  have fwd : ∀ (L : X →L[𝕜] X), (∀ x y, ⟪L x, y⟫_𝕜 = -⟪x, L y⟫_𝕜) → ∀ u : ℝ → X,
      (∀ t, HasDerivAt u (L (u t)) t) → ∀ t, 0 ≤ t → u t = (C0Group.ofBounded L).S t (u 0) := by
    intro L hL u hu t ht
    have hc : Continuous u := continuous_iff_continuousAt.2 fun s => (hu s).continuousAt
    have h := norm_sub_le_of_defect_of_dissipative L
      (fun x => (re_inner_self_eq_zero_of_skew hL x).le) (ContinuousLinearMap.id 𝕜 X) (u := u)
      (p := u) (p' := fun s => L (u s)) (T := t) hc.continuousOn
      (L.continuous.comp hc).continuousOn (fun s _ => (hu s).hasDerivWithinAt) t ⟨ht, le_rfl⟩
    simp only [ContinuousLinearMap.id_apply, sub_self, norm_zero, intervalIntegral.integral_zero,
      mul_zero, add_zero, norm_le_zero_iff] at h
    exact (sub_eq_zero.1 h)
  rcases le_total 0 t with ht | ht
  · exact fwd L hL u hu t ht
  · have hL' : ∀ x y, ⟪(-L) x, y⟫_𝕜 = -⟪x, (-L) y⟫_𝕜 := fun x y => by
      simp only [_root_.neg_apply, inner_neg_left, inner_neg_right, hL]
    have hv : ∀ s, HasDerivAt (fun s => u (-s)) ((-L) (u (-s))) s := fun s => by
      have := (hu (-s)).scomp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using this
    have h := fwd (-L) hL' (fun s => u (-s)) hv (-t) (by linarith)
    simp only [neg_neg, neg_zero] at h
    rw [h, C0Group.ofBounded_S, C0Group.ofBounded_S]
    congr 2
    rw [RCLike.ofReal_neg, smul_neg, neg_smul, neg_neg]

end Bounded

/-! ### Skew FEEC discretizations -/

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A skew FEEC discretization: a dissipative one of a skew-adjoint `A` with skew `Lₕ`. -/
structure SkewFEEC (A : E →ₗ.[𝕜] E) (κ : Type*) extends DissipFEEC.{u} A κ where
  /-- the generator is skew-adjoint -/
  isSkewAdjoint : A.IsSkewAdjoint
  skew : ∀ h x y, ⟪L h x, y⟫_𝕜 = -⟪x, L h y⟫_𝕜
  isMDissipative := isSkewAdjoint.isMDissipative
  dissipative h x := (re_inner_self_eq_zero_of_skew (skew h) x).le

namespace SkewFEEC

variable {A : E →ₗ.[𝕜] E} {κ : Type*} (F : SkewFEEC.{u} A κ)

theorem norm_group_apply (h : κ) (t : ℝ) (v : F.X h) : ‖(F.group h).S t v‖ = ‖v‖ :=
  C0Group.isIsometric_ofBounded (F.skew h) t v

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The **exact group** `U(t)` of `F`, `t ∈ ℝ`: Stone's isometric group of `A`. -/
def U (t : ℝ) : E →L[𝕜] E := F.isSkewAdjoint.group.S t

theorem U_def (t : ℝ) : F.U t = F.isSkewAdjoint.group.S t := rfl

theorem S_eq_U {t : ℝ} (ht : 0 ≤ t) : F.S t = F.U t :=
  (F.isSkewAdjoint.eqOn_group_semigroup ht).symm

/-- `F` keeps `Q` in both time directions: `U(t) Q ⊆ Q` for every `t ∈ ℝ`. -/
abbrev Invariant (Q : Set E) : Prop := ∀ t, ∀ x ∈ Q, F.U t x ∈ Q

theorem exists_sol_ne {x : E} (hx : x ∈ A.domain) (h : κ) (v : F.X h)
    (hne : F.incl h (F.L h v) ≠ A ⟨x, hx⟩) : ∃ t, F.sol h v t ≠ F.U t x := by
  obtain ⟨t, ht, hne'⟩ := F.toDissipFEEC.exists_sol_ne hx h v hne
  exact ⟨t, by rwa [F.S_eq_U ht] at hne'⟩

end SkewFEEC

/-! ### The skew-adjoint FEEC theorem -/

section Main

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
variable {A : E →ₗ.[𝕜] E} {κ : Type*} (F : SkewFEEC.{u} A κ)

open SkewFEEC

/-- **Constraints propagate iff `K` is reducing**: `K` reduces `A` iff `U(t) K ⊆ K` for every
`t ∈ ℝ`. [QuennevilleBelair2015], Prop 4.17 (adapted) -/
theorem skewFEEC_isReducing_iff_invariant : A.IsReducing F.K ↔ F.Invariant F.K := by
  have h := F.isSkewAdjoint.isIsometric_group.isReducing_iff_invariant (K := F.K)
  rw [F.isSkewAdjoint.generator_group] at h
  exact h.trans C0Group.map_le_iff_forall

theorem skewFEEC_leaves_smooth_symm {Q : Set E} (hQc : IsClosed Q) (hQ : ¬ F.Invariant Q)
    (hD : F.SmoothDense Q) {T : ℝ} (hT : 0 < T) :
    ∃ x ∈ (A.domain : Set E) ∩ Q, ∃ t ∈ Icc (-T) T, F.U t x ∉ Q := by
  by_contra hc
  refine hQ fun t => F.isSkewAdjoint.group.toC0Semigroup.mem_of_dense hQc hD fun y hy => ?_
  have hg : F.isSkewAdjoint.group.generator.domain = A.domain := by
    rw [F.isSkewAdjoint.generator_group]
  have hmem : ∀ z ∈ (A.domain : Set E), ∀ s, F.isSkewAdjoint.group.S s z ∈ A.domain := fun z hz s =>
    hg ▸ F.isSkewAdjoint.group.mapsTo_domain ⟨z, hg ▸ hz⟩ s
  have hP := F.isSkewAdjoint.group.forall_of_forall_Icc_neg hT (P := (A.domain : Set E) ∩ Q)
    fun z hz s hs => ⟨hmem z hz.1 s, by_contra fun hout => hc ⟨z, hz, s, hs, hout⟩⟩
  exact (hP y hy t).2

/-- The conclusions of the skew-adjoint FEEC theorem for `F` and the core `Z`. -/
structure SkewFEEC.Verdict (Z : F.Core) : Prop extends
    toDissip : DissipFEEC.Verdict F.toDissipFEEC Z where
  /-- for `t ≥ 0` the semigroup is the group -/
  S_eq_U {t : ℝ} (ht : 0 ≤ t) : F.S t = F.U t
  /-- the group conserves the norm of every datum, for every `t ∈ ℝ` -/
  norm_U (t : ℝ) (x : E) : ‖F.U t x‖ = ‖x‖
  /-- `K` reduces `A` iff `U(t) K ⊆ K` for every `t ∈ ℝ` -/
  isReducing_iff_invariant : A.IsReducing F.K ↔ F.Invariant F.K
  /-- smooth data leave a closed set with a dense smooth part that the group does not keep -/
  leaves_smooth_symm {Q : Set E} (hQc : IsClosed Q) (hQ : ¬ F.Invariant Q) (hD : F.SmoothDense Q)
    {T : ℝ} (hT : 0 < T) : ∃ x ∈ (A.domain : Set E) ∩ Q, ∃ t ∈ Icc (-T) T, F.U t x ∉ Q

/-- **The skew-adjoint FEEC theorem** `SkewFEEC.Verdict`: the dissipative FEEC theorem and its
conclusions for `t ∈ ℝ`. [QuennevilleBelair2015], Thms 4.6, 4.7, Prop 4.17 (adapted) -/
theorem skewFEEC (Z : F.Core) : F.Verdict Z where
  toDissip := dissipFEEC F.toDissipFEEC Z
  S_eq_U := fun {_} ht => F.S_eq_U ht
  norm_U := F.isSkewAdjoint.isIsometric_group
  isReducing_iff_invariant := skewFEEC_isReducing_iff_invariant F
  leaves_smooth_symm := fun {_} hQc hQ hD {_} hT => skewFEEC_leaves_smooth_symm F hQc hQ hD hT

end Main

end Feec.HilbertComplex
