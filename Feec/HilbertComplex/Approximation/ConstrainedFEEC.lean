module

public import Feec.HilbertComplex.Approximation.StaticFEEC
public import Feec.HilbertComplex.InvariantCore

/-!
# The constrained FEEC theorem

Constrained FEEC discretizations of the Hodge wave equation of a Hilbert complex (families of
subcomplexes approximating in the graph norm, with a closed constraint), their semi-discrete
solutions, rate classes, and the verdict of the constrained FEEC theorem.

## Main results

* `constrainedFEEC_wellPosed`: well-posedness and energy conservation.
* `constrainedFEEC_propagates_iff`: `e^{tL} K ⊆ K` for all `t` iff `K` reduces `L`.
* `constrainedFEEC_discretePoincare`: the uniform discrete Poincaré inequality.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

open _root_.Feec.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

theorem ConformingFamily.dense {κ : Type*} {H : HilbertComplex 𝕜 c W} (F : ConformingFamily H κ) :
    ∀ x : PiLp 2 W, ∀ δ > 0, ∀ᶠ h in F.l, ∃ w ∈ totalSub (F.V h).V, ‖x - w‖ < δ := by
  intro x δ hδ
  set m : ℝ := (Fintype.card ι : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  set ε := δ / (m + 1)
  have hε : 0 < ε := div_pos hδ (by positivity)
  filter_upwards [Filter.eventually_all.2 fun i => F.eventually_exists_lt i (x i) hε] with h hh
  choose v hv hlt using hh
  refine ⟨WithLp.toLp 2 fun i => v i, fun i => hv i, ?_⟩
  refine (PiLp.norm_le_sum_norm _).trans_lt ?_
  have e : m * ε < δ := by
    have : m * ε = m / (m + 1) * δ := by simp only [ε]; field_simp
    rw [this]
    have h1 : m / (m + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  calc ∑ i, ‖(x - WithLp.toLp 2 fun i => v i) i‖ ≤ ∑ _i : ι, ε :=
        Finset.sum_le_sum fun i _ => by simpa using (hlt i).le
    _ = m * ε := by simp [m]
    _ < δ := e

/-- A **constrained FEEC discretization**: approximating subcomplexes and a closed constraint. -/
structure ConstrainedFEEC (H : HilbertComplex 𝕜 c W) (κ : Type*) extends SubcomplexFamily H κ where
  /-- the approximation property in the graph norm -/
  approximates : ∀ i, toSubcomplexFamily.Approximates i
  /-- the constraint subspace -/
  K : Submodule 𝕜 (PiLp 2 W)
  isClosed_K : IsClosed (K : Set (PiLp 2 W))

/-- A conforming family with a closed constraint, as a constrained FEEC discretization. -/
def ConformingFamily.withConstraint {κ : Type*} {H : HilbertComplex 𝕜 c W}
    (F : ConformingFamily H κ) (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W))) :
    ConstrainedFEEC H κ where
  toSubcomplexFamily := F.toSubcomplexFamily
  approximates := F.approximates_toSubcomplexFamily
  K := K
  isClosed_K := hK

theorem _root_.Feec.HodgeWave.norm_shiftedForm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (T : E →ₗ.[𝕜] E) : ‖HodgeWave.shiftedForm T‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_two fun ξ ψ => ?_
  rw [HodgeWave.shiftedForm_apply, HodgeWave.waveForm_apply]
  have hξ := norm_sq_graphSpace ξ
  have hψ := norm_sq_graphSpace ψ
  set x1 := ‖T.graphFst ξ‖
  set x2 := ‖T.graphSnd ξ‖
  set p1 := ‖T.graphFst ψ‖
  set p2 := ‖T.graphSnd ψ‖
  have h1 : ‖⟪T.graphFst ψ, T.graphFst ξ⟫_𝕜‖ ≤ p1 * x1 := norm_inner_le_norm _ _
  have h2 : ‖⟪T.graphSnd ψ, T.graphFst ξ⟫_𝕜‖ ≤ p2 * x1 := norm_inner_le_norm _ _
  have h3 : ‖⟪T.graphFst ψ, T.graphSnd ξ⟫_𝕜‖ ≤ p1 * x2 := norm_inner_le_norm _ _
  have hx1 : 0 ≤ x1 := norm_nonneg _
  have hx2 : 0 ≤ x2 := norm_nonneg _
  have hp1 : 0 ≤ p1 := norm_nonneg _
  have hp2 : 0 ≤ p2 := norm_nonneg _
  have hX := norm_nonneg ξ
  have hP := norm_nonneg ψ
  have a1 : p1 * x1 ≤ ‖ξ‖ * ‖ψ‖ := by
    have : p1 ≤ ‖ψ‖ := by nlinarith
    have : x1 ≤ ‖ξ‖ := by nlinarith
    nlinarith
  have a2 : p2 * x1 + p1 * x2 ≤ ‖ξ‖ * ‖ψ‖ := by
    refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
    rw [mul_pow, hξ, hψ]
    nlinarith [sq_nonneg (p2 * x2 - p1 * x1)]
  calc ‖⟪T.graphFst ψ, T.graphFst ξ⟫_𝕜 + (⟪T.graphSnd ψ, T.graphFst ξ⟫_𝕜 -
        ⟪T.graphFst ψ, T.graphSnd ξ⟫_𝕜)‖
      ≤ ‖⟪T.graphFst ψ, T.graphFst ξ⟫_𝕜‖ + (‖⟪T.graphSnd ψ, T.graphFst ξ⟫_𝕜‖ +
        ‖⟪T.graphFst ψ, T.graphSnd ξ⟫_𝕜‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ 2 * ‖ξ‖ * ‖ψ‖ := by linarith

/-- The uniform bound `C_P = √12 ‖A‖` of the elliptic projections of all subcomplexes of `H`. -/
def ellipticConst (H : HilbertComplex 𝕜 c W) : ℝ := ‖shiftedForm H.totalD‖ / ((1 / 2) / √3)

theorem ellipticConst_nonneg (H : HilbertComplex 𝕜 c W) : 0 ≤ ellipticConst H := by
  unfold ellipticConst; positivity

theorem ellipticConst_le (H : HilbertComplex 𝕜 c W) : ellipticConst H ≤ 4 * √3 := by
  unfold ellipticConst
  have h := HodgeWave.norm_shiftedForm_le H.totalD
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [div_le_iff₀ (by positivity)]
  have e : 4 * √3 * (1 / 2 / √3) = 2 := by field_simp; ring
  linarith

/-- The graph-space lift `x ↦ (x, 𝐝 x)` of `x ∈ D(L)`. -/
def waveLift (H : HilbertComplex 𝕜 c W) (x : H.wave.domain) : H.totalD.GraphSpace :=
  H.totalD.toGraphSpace ⟨x, (H.mem_wave_domain.1 x.2).1⟩

@[simp] theorem graphFst_waveLift (H : HilbertComplex 𝕜 c W) (x : H.wave.domain) :
    H.totalD.graphFst (waveLift H x) = x := rfl

namespace ConstrainedFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ)

instance : CompleteSpace F.K := F.isClosed_K.completeSpace_coe

instance : F.K.HasOrthogonalProjection := .ofCompleteSpace _

/-- The discrete spaces `Vₕ` in the graph space `Γ(𝐝)`. -/
abbrev Kh (h : κ) : Submodule 𝕜 H.totalD.GraphSpace := (F.V h).graphSub

/-! ### The total cochain projection -/

/-- The **total cochain projection** `Πₕ x = (πₕⁱ xⁱ)ᵢ` on `W = ⊕ Wⁱ`. -/
def piProj (h : κ) : PiLp 2 W →ₗ[𝕜] PiLp 2 W :=
  (WithLp.linearEquiv 2 𝕜 (∀ i, W i)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun i => (F.π h).π i ∘ₗ PiLp.projₗ 2 W i

omit [Fintype ι] in
@[simp] theorem piProj_apply (h : κ) (x : PiLp 2 W) (i : ι) :
    F.piProj h x i = (F.π h).π i (x i) := rfl

omit [Fintype ι] in
theorem piProj_mem (h : κ) (x : PiLp 2 W) : F.piProj h x ∈ totalSub (F.V h).V :=
  fun i => (F.π h).mem i _

omit [Fintype ι] in
theorem piProj_of_mem (h : κ) {x : PiLp 2 W} (hx : x ∈ totalSub (F.V h).V) :
    F.piProj h x = x :=
  PiLp.ext fun i => (F.π h).proj i _ (hx i)

theorem piProj_mem_domain (h : κ) (x : PiLp 2 W) : F.piProj h x ∈ H.totalD.domain :=
  fun i j => (F.V h).le_domain i j ((F.π h).mem i _)

theorem totalD_piProj (h : κ) (x : H.totalD.domain) :
    H.totalD ⟨F.piProj h x, F.piProj_mem_domain h x⟩ = F.piProj h (H.totalD x) := by
  refine PiLp.ext fun j => ?_
  rw [totalD_apply, piProj_apply, totalD_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => (F.π h).comm i j ⟨(x : PiLp 2 W) i, x.2 i j⟩

theorem dense_graph (ζ : H.totalD.GraphSpace) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ h in F.l, ∃ w ∈ (F.V h).graphSub, ‖ζ - w‖ < δ := by
  obtain ⟨x, rfl, -, -⟩ := H.totalD.exists_toGraphSpace_eq ζ
  set m : ℝ := (Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)
  have hm : 0 < m + 1 := by positivity
  set ε := δ / (m + 1)
  have hε : 0 < ε := div_pos hδ hm
  filter_upwards [Filter.eventually_all.2 fun i => (tendsto_order.1 (F.approximates i
    ((H.d i (c.next i)).toGraphSpace ⟨(x : PiLp 2 W) i, x.2 i _⟩))).2 ε hε] with h hh
  obtain ⟨w, hw, hle⟩ := (F.V h).exists_mem_graphSub_le_of_infDist x hh
  refine ⟨w, hw, hle.trans_lt ?_⟩
  have : m * ε < (m + 1) * ε := by nlinarith
  calc m * ε < (m + 1) * ε := this
    _ = δ := by simp only [ε]; field_simp

theorem dense (x : PiLp 2 W) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ h in F.l, ∃ w ∈ totalSub (F.V h).V, ‖x - w‖ < δ := by
  obtain ⟨y, hy, hxy⟩ := (H.dense_totalD_domain).exists_dist_lt x (half_pos hδ)
  filter_upwards [F.dense_graph (H.totalD.toGraphSpace ⟨y, hy⟩) (δ / 2) (half_pos hδ)] with h
    ⟨w, hw, hlt⟩
  refine ⟨H.totalD.graphFst w, hw, ?_⟩
  have h1 : ‖y - H.totalD.graphFst w‖ < δ / 2 := by
    rw [show y = H.totalD.graphFst (H.totalD.toGraphSpace ⟨y, hy⟩) from rfl,
      ← H.totalD.graphFst.map_sub]
    exact (norm_graphFst_le _).trans_lt hlt
  rw [dist_eq_norm] at hxy
  calc ‖x - H.totalD.graphFst w‖ ≤ ‖x - y‖ + ‖y - H.totalD.graphFst w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < δ / 2 + δ / 2 := add_lt_add hxy h1
    _ = δ := add_halves δ

theorem isApproximating : IsApproximating F.l F.Kh :=
  Subcomplex.isApproximating F.dense_graph

theorem norm_sub_ellipticProjection_le (h : κ) (ζ : H.totalD.GraphSpace) {w : H.totalD.GraphSpace}
    (hw : w ∈ F.Kh h) : ‖ζ - ellipticProjection (F.Kh h) ζ‖ ≤ (1 + ellipticConst H) * ‖ζ - w‖ :=
  Feec.HodgeWave.norm_sub_ellipticProjection_le H.totalD_mapsTo H.totalD_comp_totalD (F.Kh h)
    (fun _ hξ => (F.V h).graphD_mem_graphSub hξ) ζ hw

/-! ### The discrete solutions -/

section Discrete

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

theorem exists_discrete (h : κ) (ζ : H.totalD.GraphSpace) :
    ∃ ξh ξh' : ℝ → H.totalD.GraphSpace, ξh 0 = ellipticProjection (F.Kh h) ζ ∧
      IsSemidiscreteSolution (F.Kh h) univ ξh ξh' := by
  obtain ⟨ξh, ξh', h0, -, -, hs⟩ :=
    exists_isSemidiscreteSolution (F.Kh h) (ellipticProjection_mem (F.Kh h) ζ) 0
  exact ⟨ξh, ξh', h0, hs⟩

/-- The **semi-discrete solution** in `Vₕ` with `ξₕ(0) = Pₕ ζ` ([QuennevilleBelair2015], (4.10)). -/
def discrete (h : κ) (ζ : H.totalD.GraphSpace) : ℝ → H.totalD.GraphSpace :=
  (F.exists_discrete h ζ).choose

/-- The time derivative of `ConstrainedFEEC.discrete`. -/
def discreteDeriv (h : κ) (ζ : H.totalD.GraphSpace) : ℝ → H.totalD.GraphSpace :=
  (F.exists_discrete h ζ).choose_spec.choose

theorem discrete_zero (h : κ) (ζ : H.totalD.GraphSpace) :
    F.discrete h ζ 0 = ellipticProjection (F.Kh h) ζ :=
  (F.exists_discrete h ζ).choose_spec.choose_spec.1

theorem isSemidiscreteSolution_discrete (h : κ) (ζ : H.totalD.GraphSpace) (I : Set ℝ) :
    IsSemidiscreteSolution (F.Kh h) I (F.discrete h ζ) (F.discreteDeriv h ζ) :=
  (F.exists_discrete h ζ).choose_spec.choose_spec.2.mono (subset_univ I)

theorem eqOn_discrete (h : κ) (ζ : H.totalD.GraphSpace) {T : ℝ} {ξh ξh' : ℝ → H.totalD.GraphSpace}
    (hξh : IsSemidiscreteSolution (F.Kh h) (Icc 0 T) ξh ξh')
    (h0 : ξh 0 = ellipticProjection (F.Kh h) ζ) : EqOn ξh (F.discrete h ζ) (Icc 0 T) :=
  hξh.eqOn (F.isSemidiscreteSolution_discrete h ζ _) (h0.trans (F.discrete_zero h ζ).symm)

end Discrete

end ConstrainedFEEC

/-! ### Auxiliary facts on the wave group -/

section Aux

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] (H : HilbertComplex 𝕜 c W)

omit [Fintype ι] [∀ i, CompleteSpace (W i)] [∀ i, NormedSpace ℝ (W i)]
  [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
private theorem apply_of_eq' {A B : PiLp 2 W →ₗ.[𝕜] PiLp 2 W} (h : A = B) (x : A.domain) :
    A x = B ⟨x, h ▸ x.2⟩ := by
  subst h; rfl

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem mem_domain_sub_adjoint {x : PiLp 2 W} (hx : x ∈ H.wave.domain) :
    x ∈ (H.totalD - H.totalD†).domain := by
  rw [← wave_eq]; exact hx

theorem isClassicalSolution_waveGroup_orbit {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 fun t => H.waveGroup.S t x := by
  have hg : H.waveGroup.toC0Semigroup.generator = H.wave := H.generator_waveGroup
  have hO := H.waveGroup.toC0Semigroup.isClassicalSolution_orbit (U₀ := x) (by rw [hg]; exact hx)
    0 T
  rw [hg] at hO
  simpa using hO

theorem waveGroup_mem_domain {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (t : ℝ) :
    H.waveGroup.S t x ∈ H.wave.domain := by
  have hd : H.waveGroup.generator.domain = H.wave.domain := by rw [generator_waveGroup]
  have h2 : H.waveGroup.S t x ∈ H.waveGroup.generator.domain :=
    H.waveGroup.mapsTo_domain ⟨x, hd ▸ hx⟩ t
  rwa [hd] at h2

theorem hasDerivAt_waveGroup {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (t : ℝ) :
    HasDerivAt (fun s => H.waveGroup.S s x) (H.waveGroup.S t (H.wave ⟨x, hx⟩)) t := by
  have hg := H.generator_waveGroup
  have h := H.waveGroup.hasDerivAt_apply ⟨x, by rw [hg]; exact hx⟩ t
  rwa [apply_of_eq' hg] at h

theorem exists_isGraphSolution_waveGroup {x : PiLp 2 W} (hx : x ∈ H.wave.domain)
    (hLx : H.wave ⟨x, hx⟩ ∈ H.wave.domain) {b : ℝ} (hb : 0 < b) :
    ∃ ξ ξ' : ℝ → H.totalD.GraphSpace, IsGraphSolution (Icc 0 b) ξ ξ' ∧
      (∀ t, H.totalD.graphFst (ξ t) = H.waveGroup.S t x) ∧
      ∀ t ∈ Icc 0 b, H.totalD.graphFst (ξ' t) = H.waveGroup.S t (H.wave ⟨x, hx⟩) := by
  have h₀ := mem_domain_sub_adjoint H hx
  have e : H.wave ⟨x, hx⟩ = (H.totalD - H.totalD†) ⟨x, h₀⟩ := apply_of_eq' H.wave_eq _
  have hL₀ : (H.totalD - H.totalD†) ⟨x, h₀⟩ ∈ (H.totalD - H.totalD†).domain := by
    rw [← e]; exact mem_domain_sub_adjoint H hLx
  obtain ⟨ξ, ξ', hξ, hξS⟩ := Feec.HodgeWave.exists_isGraphSolution H.dense_totalDomain
    H.isClosed_totalD H.totalD_mapsTo H.totalD_comp_totalD h₀ hL₀ 0 b
  rw [HodgeWave.waveGroup_totalD] at hξS
  have hS : ∀ t, H.totalD.graphFst (ξ t) = H.waveGroup.S t x := fun t => by
    rw [hξS, sub_zero]
  refine ⟨ξ, ξ', hξ, hS, fun t ht => ?_⟩
  have h1 : HasDerivWithinAt (fun s => H.totalD.graphFst (ξ s)) (H.totalD.graphFst (ξ' t))
      (Icc 0 b) t :=
    (H.totalD.graphFst.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hξ.deriv t ht)
  have h2 : HasDerivWithinAt (fun s => H.totalD.graphFst (ξ s))
      (H.waveGroup.S t (H.wave ⟨x, hx⟩)) (Icc 0 b) t := by
    simp only [hS]
    exact (hasDerivAt_waveGroup H hx t).hasDerivWithinAt
  exact (uniqueDiffOn_Icc hb t ht).eq_deriv _ h1 h2

end Aux

/-! ### 1. Well-posedness -/

section Main

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ)

/-- **Well-posedness**: for `ξ₀ ∈ D(L)`, `e^{tL} ξ₀` is a classical solution, the only strong and
the only weak one, and conserves energy ([QuennevilleBelair2015], Thm 4.6, Thm 4.7). -/
theorem constrainedFEEC_wellPosed {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 (fun t => H.waveGroup.S t x) ∧
    (∀ U, U 0 = x → Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U →
      EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
    (∀ U, U 0 = x → HodgeWave.IsWeakSolution H (Icc 0 T) 0 U →
      EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
    ∀ t, ‖H.waveGroup.S t x‖ = ‖x‖ := by
  have hO := isClassicalSolution_waveGroup_orbit H hx T
  obtain ⟨U, hU0, -, hUs, hUw, -⟩ := HodgeWave.existsUnique_hom H hx 0 T
  have hOU : EqOn (fun t => H.waveGroup.S t x) U (Icc 0 T) :=
    hUs _ (by simp) hO.toIsStrongSolution
  refine ⟨hO, fun V hV0 hV => fun t ht => (hUs V hV0 hV ht).trans (hOU ht).symm,
    fun V hV0 hV => fun t ht => (hUw V hV0 hV ht).trans (hOU ht).symm,
    fun t => H.isIsometric_waveGroup t x⟩

/-! ### 2. Constraint propagation -/

/-- **Constraints propagate iff `K` is reducing**: `K` reduces `L` iff `e^{tL} K ⊆ K` for all `t`
([QuennevilleBelair2015], Prop 4.17 (adapted)). -/
theorem constrainedFEEC_propagates_iff :
    H.wave.IsReducing F.K ↔ ∀ t, ∀ x ∈ F.K, H.waveGroup.S t x ∈ F.K :=
  (H.isReducing_iff_waveGroup_invariant F.K).trans C0Group.map_le_iff_forall

theorem constrainedFEEC_propagates (hK : H.wave.IsReducing F.K) {T : ℝ} {U : ℝ → PiLp 2 W}
    (h0 : U 0 ∈ F.K) (hU : Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U) :
    ∀ t ∈ Icc 0 T, U t ∈ F.K :=
  hU.mem_of_isReducing H.isSkewAdjoint_wave.isDissipative hK h0 fun _ _ => F.K.zero_mem

theorem waveGroup_mem_of_dense {P : Set (PiLp 2 W)} {Q : Set (PiLp 2 W)} (hQ : IsClosed Q)
    (hdense : ∀ k ∈ Q, k ∈ closure (P ∩ Q)) {t : ℝ}
    (h : ∀ x ∈ P, x ∈ Q → H.waveGroup.S t x ∈ Q) : ∀ x ∈ Q, H.waveGroup.S t x ∈ Q := by
  intro x hx
  have hsub : P ∩ Q ⊆ (H.waveGroup.S t) ⁻¹' Q := fun y hy => h y hy.1 hy.2
  exact closure_minimal hsub (hQ.preimage (H.waveGroup.S t).continuous) (hdense x hx)

theorem constrainedFEEC_propagates_iff_domain
    (hdense : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) :
    H.wave.IsReducing F.K ↔
      ∀ t, ∀ x ∈ H.wave.domain, x ∈ F.K → H.waveGroup.S t x ∈ F.K := by
  rw [constrainedFEEC_propagates_iff]
  exact ⟨fun h t x _ hx => h t x hx,
    fun h t => waveGroup_mem_of_dense F.isClosed_K hdense (h t)⟩

theorem constrainedFEEC_propagates_iff_of_grading {p : ι → Bool}
    (hp : ∀ i j, c.Rel i j → p j ≠ p i) (hRK : ∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K)
    (hdense : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) :
    H.wave.IsReducing F.K ↔ ∀ (T : ℝ) (U : ℝ → PiLp 2 W), U 0 ∈ F.K →
      Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U → ∀ t ∈ Icc 0 T, U t ∈ F.K :=
  H.isReducing_iff_forall_isStrongSolution hp F.K hRK hdense

/-- A **rate class**: data whose orbits on `[0, T]` are approximated in `Γ(𝐝)` to order `C hᵅ`. -/
structure ConstrainedFEEC.RateClass (F : ConstrainedFEEC H κ) (T : ℝ) where
  /-- the data -/
  Data : Set (PiLp 2 W)
  /-- the norm of the class -/
  classNorm : PiLp 2 W → ℝ
  /-- the mesh size -/
  meshSize : κ → ℝ
  /-- the order -/
  α : ℝ
  /-- the constant -/
  C : ℝ
  mem_domain : ∀ x ∈ Data, x ∈ H.wave.domain
  mem_domain_sq : ∀ x (hx : x ∈ H.wave.domain), x ∈ Data → H.wave ⟨x, hx⟩ ∈ H.wave.domain
  approx : ∀ x ∈ Data, ∀ h, ∀ t ∈ Icc 0 T, ∀ v : H.totalD.GraphSpace,
    H.totalD.graphFst v = H.waveGroup.S t x →
      ∃ w ∈ F.Kh h, ‖v - w‖ ≤ C * meshSize h ^ α * classNorm x
  approx_deriv : ∀ x (hx : x ∈ H.wave.domain), x ∈ Data → ∀ h, ∀ t ∈ Icc 0 T,
    ∀ v : H.totalD.GraphSpace, H.totalD.graphFst v = H.waveGroup.S t (H.wave ⟨x, hx⟩) →
      ∃ w ∈ F.Kh h, ‖v - w‖ ≤ C * meshSize h ^ α * classNorm x

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem ConstrainedFEEC.RateClass.exists_mem_Kh_le_of_degreewise (F : ConstrainedFEEC H κ)
    {Reg : ∀ i, W i → Prop} {B : ι → ℝ} {r : κ → ℝ} {Λ : ℝ}
    (happ : ∀ h i (x : W i), Reg i x → ∃ v, ∃ hv : v ∈ (F.V h).V i,
      ‖x - v‖ ≤ B i * Λ * r h ∧ ∀ j (hxj : x ∈ (H.d i j).domain),
        ‖H.d i j ⟨x - v, Submodule.sub_mem _ hxj ((F.V h).le_domain i j hv)⟩‖ ≤ B i * Λ * r h)
    (hB : ∀ i, 0 ≤ B i) (hΛ : 0 ≤ Λ) (hr : ∀ h, 0 ≤ r h) (h : κ) {z : PiLp 2 W}
    (hz : ∀ i, Reg i (z i)) (v : H.totalD.GraphSpace) (hv : H.totalD.graphFst v = z) :
    ∃ w ∈ F.Kh h, ‖v - w‖ ≤ ((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)) *
      (∑ i, B i) * r h ^ (1 : ℝ) * Λ := by
  obtain ⟨y, rfl, -, -⟩ := H.totalD.exists_toGraphSpace_eq v
  obtain ⟨w, hw, hle⟩ := Subcomplex.exists_mem_graphSub_le (F.V h) y
    (ε := (∑ i, B i) * Λ * r h) fun i => by
      rw [show (y : PiLp 2 W) = z from hv]
      obtain ⟨u, hu, h1, h2⟩ := happ h _ _ (hz i)
      have hle : B i * Λ * r h ≤ (∑ i, B i) * Λ * r h :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := B) (fun _ _ => hB _) (Finset.mem_univ i)) hΛ) (hr h)
      exact ⟨u, hu, h1.trans hle, fun j hxj => (h2 j hxj).trans hle⟩
  refine ⟨w, hw, hle.trans_eq ?_⟩
  rw [Real.rpow_one]; ring

/-! ### 3. The constraint residual -/

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem ConstrainedFEEC.infDist_le_norm_sub {y z : PiLp 2 W} (hy : y ∈ F.K) :
    infDist z (F.K : Set (PiLp 2 W)) ≤ ‖y - z‖ := by
  rw [norm_sub_rev, ← dist_eq_norm]; exact infDist_le_dist_of_mem hy

/-! ### The discrete Poincaré inequality -/

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] [Fintype ι] in
/-- **The uniform discrete Poincaré inequality** for cochain projections bounded uniformly in `W`
([AFW2010], Thm 3.6; [Arnold2018], Thm 5.3). -/
theorem constrainedFEEC_discretePoincare (hπ : ∃ C, ∀ h i x, ‖(F.π h).π i x‖ ≤ C * ‖x‖)
    {i j : ι} (hij : c.Rel i j) {cP : ℝ}
    (hP : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖) :
    ∃ C, 0 ≤ C ∧ ∀ h, ∀ x (hx : x ∈ (F.V h).V i), (∀ y ∈ (F.V h).cyclesW i, ⟪y, x⟫_𝕜 = 0) →
      ‖x‖ ≤ C * cP * ‖H.d i j ⟨x, (F.V h).le_domain i j hx⟩‖ := by
  obtain ⟨C, hC⟩ := hπ
  refine ⟨max C 0, le_max_right _ _, fun h x hx hxo => ?_⟩
  exact (F.π h).norm_le_of_forall_inner_eq_zero hij hP (le_max_right _ _)
    (fun y => (hC h i y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
    hx hxo

/-! ### The verdict -/

/-- **The conclusions of the constrained FEEC theorem** for `F`. -/
structure ConstrainedFEEC.Verdict (F : ConstrainedFEEC H κ) : Prop where
  /-- well-posedness and energy conservation -/
  wellPosed {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 (fun t => H.waveGroup.S t x) ∧
    (∀ U, U 0 = x → Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U →
      EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
    (∀ U, U 0 = x → HodgeWave.IsWeakSolution H (Icc 0 T) 0 U →
      EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
    ∀ t, ‖H.waveGroup.S t x‖ = ‖x‖
  /-- `K` reduces `L` iff `e^{tL} K ⊆ K` for all `t` -/
  propagates_iff : H.wave.IsReducing F.K ↔ ∀ t, ∀ x ∈ F.K, H.waveGroup.S t x ∈ F.K
  /-- convergence for `ξ₀ ∈ D(L)`, uniformly on `[0, T]` -/
  converges (x : H.wave.domain) (T : ℝ) :
    TendstoUniformlyOn (fun h t => H.totalD.graphFst (F.discrete h (waveLift H x) t))
      (fun t => H.waveGroup.S t x) F.l (Icc 0 T)
  /-- convergence for `ξ₀ ∈ W` from every family with `ξₕ(0) → ξ₀` -/
  converges_of_tendsto (x : PiLp 2 W) {T : ℝ} (ξh ξh' : κ → ℝ → H.totalD.GraphSpace)
    (hξh : ∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h))
    (h0 : Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x)) :
    TendstoUniformlyOn (fun h t => H.totalD.graphFst (ξh h t)) (fun t => H.waveGroup.S t x) F.l
      (Icc 0 T)
  /-- such families exist -/
  exists_tendsto (x : PiLp 2 W) (T : ℝ) :
    ∃ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
      (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) ∧
      Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x)
  /-- the rate `(1 + C_P) (1 + t)² C hᵅ ‖ξ₀‖_class` on a rate class -/
  rate {T : ℝ} (R : F.RateClass T) {x : PiLp 2 W} (hxR : x ∈ R.Data) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖H.waveGroup.S t x -
        H.totalD.graphFst (F.discrete h (waveLift H ⟨x, R.mem_domain x hxR⟩) t)‖ ≤
      (1 + ellipticConst H) * (1 + t) ^ 2 * (R.C * R.meshSize h ^ R.α * R.classNorm x)
  /-- for reducing `K`, the residual is at most the error -/
  residual_le (hK : H.wave.IsReducing F.K) (x : H.wave.domain) (hxK : (x : PiLp 2 W) ∈ F.K)
    (h : κ) (t : ℝ) :
    infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t)) (F.K : Set (PiLp 2 W)) ≤
      ‖H.waveGroup.S t x - H.totalD.graphFst (F.discrete h (waveLift H x) t)‖
  /-- and tends to `0` uniformly on `[0, T]` -/
  residual_tendsto (hK : H.wave.IsReducing F.K) (x : H.wave.domain) (hxK : (x : PiLp 2 W) ∈ F.K)
    (T : ℝ) :
    TendstoUniformlyOn
      (fun h t => infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
        (F.K : Set (PiLp 2 W))) (fun _ => 0) F.l (Icc 0 T)
  /-- for non-reducing `K`, a datum of `K` or `Kᗮ` leaves it, with residuals of positive limit -/
  leaves (hK : ¬ H.wave.IsReducing F.K) {T : ℝ} (hT : 0 < T) :
    ∃ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ Q ∧ 0 < infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)) ∧
      ∀ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
        Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
        Tendsto (fun h => infDist (H.totalD.graphFst (ξh h t)) (Q : Set (PiLp 2 W))) F.l
          (𝓝 (infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W))))
  /-- with `D(L) ∩ K` dense in `K`, a datum of `D(L) ∩ K` leaves `K` at some `t ∈ [-T, T]` -/
  leaves_symm (hK : ¬ H.wave.IsReducing F.K)
    (hD : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) {T : ℝ} (hT : 0 < T) :
    ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc (-T) T,
      H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W))
  /-- on a graded complex, a datum of `D(L) ∩ K` leaves `K` forward in time -/
  leaves_graded {p : ι → Bool} (hp : ∀ i j, c.Rel i j → p j ≠ p i)
    (hRK : ∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K)
    (hD : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K))
    (hK : ¬ H.wave.IsReducing F.K) {T : ℝ} (hT : 0 < T) :
    ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) ∧
      Tendsto (fun h => infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
        (F.K : Set (PiLp 2 W))) F.l (𝓝 (infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)))) ∧
      ∀ᶠ h in F.l, infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) / 2 <
        infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t)) (F.K : Set (PiLp 2 W))
  /-- the discrete cohomology: eventually `Hⁱ(H) ≅ Hⁱ(Vₕ)` -/
  cohomology {i : ι} (hb : F.IsGraphBounded i) [FiniteDimensional 𝕜 (H.harmonic i)]
    (hi : H.ClosedRangeAt i) :
    ∀ᶠ h in F.l, Function.Bijective ((F.π h).cohomologyMap i)

variable {F} in
theorem ConstrainedFEEC.Verdict.residual_rate (V : F.Verdict) (hK : H.wave.IsReducing F.K)
    {T : ℝ} (R : F.RateClass T) {x : PiLp 2 W} (hxR : x ∈ R.Data) (hxK : x ∈ F.K) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    infDist (H.totalD.graphFst (F.discrete h (waveLift H ⟨x, R.mem_domain x hxR⟩) t))
        (F.K : Set (PiLp 2 W)) ≤
      (1 + ellipticConst H) * (1 + t) ^ 2 * (R.C * R.meshSize h ^ R.α * R.classNorm x) :=
  (F.infDist_le_norm_sub (V.propagates_iff.1 hK t x hxK)).trans (V.rate R hxR h ht)

end Main

/-! ### Non-vacuity -/

namespace ConstrainedFEEC

open ShortHilbertComplex

variable (𝕜) in
/-- The short complex `𝕜 --id--> 𝕜 → 0`. -/
def idShort : ShortHilbertComplex 𝕜 𝕜 𝕜 PUnit :=
  ShortHilbertComplex.ofOp (((ContinuousLinearMap.id 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜) : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤)
    (by simp [dense_univ]) (ContinuousLinearMap.id 𝕜 𝕜).isClosed_toPMap_top

variable (𝕜) in
/-- The complex `𝕜 --id--> 𝕜 → 0` on the window `Fin 3`. -/
abbrev idComplex : HilbertComplex 𝕜 ComplexShape.fin3 (W3 𝕜 𝕜 PUnit) :=
  (idShort 𝕜).toHilbertComplex

theorem idComplex_domain (i j : Fin 3) : ((idComplex 𝕜).d i j).domain = ⊤ := by
  fin_cases i <;> fin_cases j <;> rfl

theorem mem_idComplex_wave_domain (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    x ∈ (idComplex 𝕜).wave.domain := by
  refine (idShort 𝕜).mem_wave_domain.2 ⟨trivial, trivial, ?_, ?_⟩
  · change (x 1 : 𝕜) ∈ ((((ContinuousLinearMap.id 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜) : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤)†).domain
    rw [ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense _ (by simp [dense_univ])]
    trivial
  · rw [show (idShort 𝕜).d₁ = 0 from rfl, LinearPMap.adjoint_zero]
    trivial

instance instFiniteDimensionalW3 : ∀ i, FiniteDimensional 𝕜 (W3 𝕜 𝕜 PUnit i)
  | 0 => inferInstanceAs (FiniteDimensional 𝕜 𝕜)
  | 1 => inferInstanceAs (FiniteDimensional 𝕜 𝕜)
  | 2 => inferInstanceAs (FiniteDimensional 𝕜 PUnit)

variable (𝕜) in
/-- The whole complex as a subcomplex. -/
def topSub : (idComplex 𝕜).Subcomplex where
  V _ := ⊤
  le_domain i j := (idComplex_domain i j).ge
  mapsTo _ _ _ _ := Submodule.mem_top

variable (𝕜) in
/-- The identity cochain projection onto `topSub`. -/
def topProj : (topSub 𝕜).CochainProjection where
  π _ := LinearMap.id
  mem _ _ := Submodule.mem_top
  proj _ _ _ := rfl
  comm _ _ _ := rfl

variable (𝕜) in
/-- The conforming family of `𝕜 --id--> 𝕜 → 0` with `Vₕ = W` and `πₕ = id`. -/
def idFamily : ConformingFamily (idComplex 𝕜) ℕ where
  l := atTop
  V _ := topSub 𝕜
  π _ := topProj 𝕜
  bound_π := ⟨1, fun _ _ x => by simp [topProj]⟩
  approx i w := by
    rw [infDist_zero_of_mem (show w ∈ ((topSub 𝕜).V i : Set _) from Submodule.mem_top)]
    exact tendsto_const_nhds

variable (𝕜) in
/-- The constrained FEEC discretization of `𝕜 --id--> 𝕜 → 0` with `Vₕ = W` and `πₕ = id`. -/
def idFEEC (K : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit)))
    (hK : _root_.IsClosed (K : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) :
    ConstrainedFEEC (idComplex 𝕜) ℕ :=
  (idFamily 𝕜).withConstraint K hK

variable (𝕜) in
/-- The constraint `𝕜 × 0 × 0`. -/
abbrev firstSub : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit)) :=
  totalSub (family3 (⊤ : Submodule 𝕜 𝕜) (⊥ : Submodule 𝕜 𝕜) (⊥ : Submodule 𝕜 PUnit))

variable (𝕜) in
/-- The datum `(1, 0, 0)`. -/
def firstDatum : PiLp 2 (W3 𝕜 𝕜 PUnit) :=
  WithLp.toLp 2 fun i => match i with
    | 0 => (1 : 𝕜)
    | 1 => (0 : 𝕜)
    | 2 => PUnit.unit

theorem firstDatum_mem : firstDatum 𝕜 ∈ firstSub 𝕜 :=
  mem_totalSub_family3.2 ⟨Submodule.mem_top (R := 𝕜) (M := 𝕜),
    (Submodule.mem_bot (M := 𝕜) 𝕜).2 rfl, (Submodule.mem_bot (M := PUnit) 𝕜).2 rfl⟩

theorem not_isReducing_firstSub : ¬ (idComplex 𝕜).wave.IsReducing (firstSub 𝕜) := by
  intro h
  have hm := (((idComplex 𝕜).isSkewAdjoint_wave.isReducing_iff).1 h).2
    ⟨firstDatum 𝕜, mem_idComplex_wave_domain _⟩ firstDatum_mem
  have h1 : ((idComplex 𝕜).wave ⟨firstDatum 𝕜, mem_idComplex_wave_domain _⟩ : PiLp 2 _) 1 =
      (0 : 𝕜) := (Submodule.mem_bot (M := 𝕜) 𝕜).1 (mem_totalSub_family3.1 hm).2.1
  have e := (idShort 𝕜).wave_apply_one ⟨firstDatum 𝕜, mem_idComplex_wave_domain _⟩
  have e2 : (idShort 𝕜).d₁† ⟨(firstDatum 𝕜 : PiLp 2 (W3 𝕜 𝕜 PUnit)) 2,
      (mem_idComplex_wave_domain (firstDatum 𝕜)).2 2 1⟩ = 0 :=
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero rfl _
  rw [e2, sub_zero] at e
  have e1 : (idShort 𝕜).d₀ ⟨(firstDatum 𝕜 : PiLp 2 (W3 𝕜 𝕜 PUnit)) 0,
      (mem_idComplex_wave_domain (firstDatum 𝕜)).1 0 1⟩ = (1 : 𝕜) := rfl
  rw [e1] at e
  have : (1 : 𝕜) = 0 := e.symm.trans h1
  exact one_ne_zero this

theorem idRate_bound (N : ℕ) (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) {v : (idComplex 𝕜).totalD.GraphSpace} :
    ‖v - v‖ ≤ 1 * (1 / ((N : ℝ) + 1)) ^ (1 : ℝ) * ‖x‖ := by
  rw [sub_self, norm_zero]; positivity

/-- A rate class of `idFEEC 𝕜 (firstSub 𝕜)` with all of `W` as data, `h = 1/(N+1)` and `α = 1`. -/
def idRate (T : ℝ) : (idFEEC 𝕜 (firstSub 𝕜) isClosed_totalSub).RateClass T where
  Data := univ
  classNorm := norm
  meshSize N := 1 / ((N : ℝ) + 1)
  α := 1
  C := 1
  mem_domain x _ := mem_idComplex_wave_domain x
  mem_domain_sq _ _ _ := mem_idComplex_wave_domain _
  approx x _ N _ _ v _ := ⟨v, fun _ => Submodule.mem_top, idRate_bound N x⟩
  approx_deriv x _ _ N _ _ v _ := ⟨v, fun _ => Submodule.mem_top, idRate_bound N x⟩

end ConstrainedFEEC

end Feec.HilbertComplex
