module

public import Feec.Instances.EinsteinBianchiFEMComplex

/-!
# The discrete Gauss constraint of the scheme (6.5) and the TSD constraint

`Feec.Instances.EinsteinBianchi.FEM.hiddenGauss` is the constraint `σₕ = 0`, `uₕ ⊥ d̃ Φ(Vₕ⁰, 0)`
on the hidden space of the scheme (6.3)/(6.5) of [QuennevilleBelair2015], §6.2–6.3. It is
invariant under the generator `Lₕ = 𝐝ₕ - 𝐝ₕ*`, hence preserved exactly by the discrete solutions
(`Feec.Instances.EinsteinBianchi.FEM.waveGen_mem_hiddenGauss`). This file identifies it and
relates it to the TSD constraint.

**What it is.** For any BGG segment with `d̃ : Ṽ⁰ → Ṽ¹` injective and `S₀` onto:

* `mem_hiddenGauss_iff`: `x ∈ hiddenGauss ↔ σ = 0 ∧ u ⊥ d̃φ` for every `(σ', φ) ∈ Γ`
  (`dσ' = S₀φ`): the **discrete divergence constraint** `D₀* u = 0` for the first operator
  `D₀ = (0 d̃)` of the BGG complex (5.1) ([QuennevilleBelair2015], §5.1); with the top row exact
  at `V¹` (`mem_hiddenGauss_iff_ker_S1`, through `Feec.BGG.Segment.range_D0`,
  [QuennevilleBelair2015], Prop 5.1) it says `u ⊥ d̃φ` for the gradients with `S₁ d̃φ = 0`, the
  **weak symmetry** form of `div div u = 0` (cf. [AFW2007]);
* `hiddenGauss_eq_orthogonal`: `hiddenGauss = (Vₕ⁰ ⊕ 𝐝ₕ Vₕ⁰)ᗮ`, the Gauss law of the discrete
  differential space `(Xₕ, 𝐝ₕ)` (degree-`0` component and degree-`0` component of `𝐝ₕ*` vanish;
  cf. [HolstStern2012], §3); it reduces `Lₕ` (`waveGen_mem_hiddenGauss_orthogonal`);
* it is nontrivial: `hiddenGauss_ne_top` when `Vₕ⁰ ≠ 0`, `hiddenGauss_ne_bot` when `Vₕ² ≠ 0`;
  it does not constrain `M` or `ρ` (`stateNoU_mem_hiddenGauss`).

**Its limit.** For a discretization satisfying (5.4) ([QuennevilleBelair2015], §5.2, (5.4)),
projected constraint pairs are discrete constraint pairs (`proj_mem_Γh`), so
`⟪uₕ, Π̃¹ d̃φ⟫ = 0` and `|⟪uₕ, d̃φ⟫| ≤ ‖x‖ ‖d̃φ - Π̃¹ d̃φ‖` (`abs_inner_dt0_le`). The continuous
**Gauss constraint** `gaussSub` (`σ = 0`, `u ⊥ d̃φ` for `(σ', φ) ∈ Γ`, in a continuous energy space
into which the hidden states are read) is the degree-`0` part of TSD. For families whose
projections `Π̃¹` converge strongly:

* `eventually_abs_inner_le_of_mem_hiddenGauss`: the read discrete Gauss constraints converge
  **weakly** to `gaussSub`, uniformly on bounded sets (`|⟪rₕ x, y⟫| ≤ ε ‖x‖` eventually, for every
  `y ⊥ gaussSub`); `tendsto_inner_of_mem_hiddenGauss`, `mem_gaussSub_of_tendsto_inner`,
  `mem_gaussSub_of_tendsto`, `mem_gaussSub_of_tendsto_comp` (weak and strong limits of read
  bounded discrete Gauss states lie in `gaussSub`);
* `tendstoUniformly_inner_group`, `tendstoUniformly_inner_group_comp`: along the discrete
  solutions from bounded discrete Gauss data, uniformly in `t ∈ ℝ`, whether or not the scheme
  converges.

**Mirror boundary conditions** (`mirrorGauss`, `mirrorFE`, `mirrorEmb`):
`eventually_abs_inner_mirrorFE_le`, `tendsto_inner_mirrorFE`, `mem_mirrorGauss_of_tendsto`,
`tendstoUniformly_inner_mirrorEmb_group`. The real and imaginary parts of TSD states lie in
`mirrorGauss` (`mirrorRe_mem_mirrorGauss`, from the orthogonality of TSD fields to all bottom
gradients, `inner_rowsW1L_bD0`), so the Gauss residual is at most the TSD residual
(`infDist_mirrorRe_le`) and tends to `0` for TSD data
(`einsteinBianchi_mirrorFEM_gaussResidual`: the residual-`0` clause for the part of TSD that
`hiddenGauss` captures). TSD is strictly stronger: the multiplier states `(0, 0, Mₕ, 0)` are
discrete Gauss states read at distance `‖x‖` from `tsdQℝ` (`multiplierState_mirror`), and
eventually such nonzero states exist (`eventually_exists_mirrorHiddenGauss_infDist_eq`,
`eventually_mirrorHiddenGauss_ne_bot`). So `dist(ιₙ x, tsdQℝ)` does not tend to `0` on bounded
subsets of `hiddenGauss`, `ιₙ(hiddenGauss) ⊄ tsdQℝ`, and the residual-`0` clause of
`Feec.HilbertComplex.approxFEEC_ofComplexCrime` (item 3, which needs `ιₙ(Kₙ) ⊆ K`) does not apply
to `hiddenGauss` with `K = tsdQℝ`.

**The thesis' boundary conditions** (`cubeGauss`, `cubeFE`, `cubeEmb`):
`eventually_abs_inner_cubeFE_le`, `tendstoUniformly_inner_cubeEmb_group`, and
`standardCube_waveGroup_mem_cubeGauss`: if `ιₙ vₙ → ξ₀` with `vₙ ∈ hiddenGauss`, the exact solution
`e^{tL} ξ₀` lies in the continuous Gauss constraint for every `t ≥ 0` (through the convergence of
the scheme for every datum, from the verdict of the crime front
`ofComplexCrime (standardCubeComplex)`). The failure of TSD propagation for these boundary
conditions is not a failure of its degree-`0` part along such data.

**Not shown.** The convergence is weak: `dist(ιₙ x, gaussSub) → 0` uniformly on bounded subsets
of `hiddenGauss` would need a discrete compactness property, not formalized. Whether the datum
`(0, 0, (0, β))` that leaves `thesisTSD` is a limit of read discrete Gauss data, and `Vₕ⁰ ≠ 0` for
the concrete schemes (so `hiddenGauss ≠ ⊤` there), are not formalized.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.1 ((5.1), Prop 5.1), §5.2 ((5.4)), §6.2 ((6.3)), §6.3 ((6.5))
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3
* [D. N. Arnold, R. S. Falk, R. Winther, *Mixed finite element methods for linear elasticity with weakly imposed symmetry*][AFW2007]
  (weak symmetry)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi.FEM

open Feec.HilbertComplex Feec.BGG

section Generic

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  (D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2)

/-- The states `(σ, 0, M, ρ)` (no `u` component) are hidden states. -/
def stateNoU (σ : P0) (M : P2) (ρ : Pt2) : HiddenState D :=
  (⟨EState.mk σ 0 M ρ, fun ψ _ => by rw [EState.u_mk, inner_zero_left]⟩ : hiddenSpace D)

@[simp] theorem stateNoU_toEState (σ : P0) (M : P2) (ρ : Pt2) :
    (stateNoU D σ M ρ).toEState = EState.mk σ 0 M ρ := rfl

/-- The degree-`0` states `τ ↦ (τ, 0, 0, 0)`. -/
def incl0 : P0 →ₗ[ℝ] HiddenState D where
  toFun τ := stateNoU D τ 0 0
  map_add' τ τ' := HiddenState.toEState_injective (by
    rw [HiddenState.toEState_add, stateNoU_toEState, stateNoU_toEState,
      stateNoU_toEState, ← EState.mk_add, add_zero, add_zero, add_zero])
  map_smul' c τ := HiddenState.toEState_injective (by
    rw [RingHom.id_apply, HiddenState.toEState_smul, stateNoU_toEState, stateNoU_toEState,
      ← EState.mk_smul, smul_zero, smul_zero, smul_zero])

@[simp] theorem incl0_apply (τ : P0) : incl0 D τ = stateNoU D τ 0 0 := rfl

/-- The subspace `Vₕ⁰ ⊕ 0` of degree-`0` states. -/
def deg0 : Submodule ℝ (HiddenState D) := LinearMap.range (incl0 D)

variable [FiniteDimensional ℝ P1] [FiniteDimensional ℝ Pt0] [FiniteDimensional ℝ Pt1]
  (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)

/-- **The discrete Gauss constraint is the discrete divergence constraint `D₀* u = 0`**: `σ = 0`
and `u ⊥ d̃φ` for every `(σ', φ) ∈ Γ`, i.e. `u` is orthogonal to the range of the first operator
`(0 d̃) : Γ → Ṽ¹` of the complex (5.1) (`Φ(τ, 0)` and `ker S₀` span the second components of `Γ`,
and `u ⊥ d̃(ker S₀)` on the hidden space). -/
theorem mem_hiddenGauss_iff {x : HiddenState D} :
    x ∈ hiddenGauss D hdinj hS ↔
      x.toEState.σ = 0 ∧ ∀ p ∈ D.Γ, ⟪x.toEState.u, D.dt0 p.2⟫ = 0 := by
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun p hp => ?_⟩
    have hk : D.S0 (p.2 - phiMap D hdinj hS (p.1, 0)) = 0 := by
      rw [map_sub, S0_phiMap hdinj hS (p.1, 0), ← D.mem_Γ.1 hp, sub_self]
    have h := x.toEState_mem _ hk
    rw [map_sub, inner_sub_right, h1 p.1, sub_zero] at h
    exact h
  · rintro ⟨h0, h1⟩
    exact ⟨h0, fun τ => h1 (τ, phiMap D hdinj hS (τ, 0))
      (D.mem_Γ.2 (S0_phiMap hdinj hS (τ, 0)).symm)⟩

/-- **Weak symmetry form**: when the top row is exact at `V¹`, `x ∈ hiddenGauss` iff `σ = 0` and
`u ⊥ d̃φ` for every `φ` with `S₁ d̃φ = 0` (`R(0 d̃) = R(d̃) ∩ N(S₁)`, `Segment.range_D0`): `u` is
orthogonal to the discrete gradients whose skew part vanishes. -/
theorem mem_hiddenGauss_iff_ker_S1 (hT : D.ExactTop) {x : HiddenState D} :
    x ∈ hiddenGauss D hdinj hS ↔
      x.toEState.σ = 0 ∧ ∀ φ, D.S1 (D.dt0 φ) = 0 → ⟪x.toEState.u, D.dt0 φ⟫ = 0 := by
  rw [mem_hiddenGauss_iff]
  refine and_congr_right fun _ => ⟨fun h φ hφ => ?_, fun h p hp => h _ (D.S1_dt0_of_mem hp)⟩
  have hr : D.dt0 φ ∈ LinearMap.range D.D0 := by
    rw [D.range_D0 hT]
    exact ⟨⟨φ, rfl⟩, hφ⟩
  obtain ⟨p, hp⟩ := hr
  rw [← hp]
  exact h p.1 p.2

/-- **The discrete Gauss constraint does not involve `M`, `ρ`**: `(0, 0, M, ρ) ∈ hiddenGauss`. -/
theorem stateNoU_mem_hiddenGauss (M : P2) (ρ : Pt2) :
    stateNoU D 0 M ρ ∈ hiddenGauss D hdinj hS :=
  ⟨rfl, fun τ => by rw [stateNoU_toEState, EState.u_mk, inner_zero_left]⟩

/-- A state with `σ ≠ 0` is not a discrete Gauss state. -/
theorem stateNoU_not_mem_hiddenGauss {σ : P0} (hσ : σ ≠ 0) (M : P2) (ρ : Pt2) :
    stateNoU D σ M ρ ∉ hiddenGauss D hdinj hS := fun h => hσ h.1

/-- **The discrete Gauss constraint is a proper subspace** when `Vₕ⁰ ≠ 0`. -/
theorem hiddenGauss_ne_top [Nontrivial P0] : hiddenGauss D hdinj hS ≠ ⊤ := fun h => by
  obtain ⟨σ, hσ⟩ := exists_ne (0 : P0)
  exact stateNoU_not_mem_hiddenGauss D hdinj hS hσ 0 0 (h ▸ Submodule.mem_top)

/-- **The discrete Gauss constraint is nonzero** when `Vₕ² ≠ 0`. -/
theorem hiddenGauss_ne_bot [Nontrivial P2] : hiddenGauss D hdinj hS ≠ ⊥ := fun h => by
  obtain ⟨M, hM⟩ := exists_ne (0 : P2)
  have hm := stateNoU_mem_hiddenGauss D hdinj hS M 0
  rw [h, Submodule.mem_bot] at hm
  have := congrArg (fun x : HiddenState D => x.toEState.M) hm
  exact hM this

variable [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt2]

/-- **The discrete Gauss constraint is the orthogonal complement of the degree-`0` states and of
their image under `𝐝ₕ`**: `hiddenGauss = (Vₕ⁰ ⊕ 𝐝ₕ Vₕ⁰)ᗮ`, the kernel of the degree-`0`
component and of the degree-`0` component of `𝐝ₕ*` (the form of a Gauss law in a Hilbert
complex). -/
theorem hiddenGauss_eq_orthogonal :
    hiddenGauss D hdinj hS =
      (deg0 D ⊔ (deg0 D).map (diffGen D hdinj hS : HiddenState D →ₗ[ℝ] HiddenState D))ᗮ := by
  rw [← Submodule.inf_orthogonal]
  ext x
  rw [Submodule.mem_inf, Submodule.mem_orthogonal, Submodule.mem_orthogonal]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨τ, rfl⟩
      rw [← HiddenState.inner_toEState, EState.inner_def]
      simp [h0]
    · rintro _ ⟨_, ⟨τ, rfl⟩, rfl⟩
      rw [ContinuousLinearMap.coe_coe, inner_diffGen]
      simp only [incl0_apply, stateNoU_toEState, EState.σ_mk,
        EState.u_mk, map_zero, inner_zero_left, add_zero]
      rw [real_inner_comm, h1 τ, neg_zero]
  · rintro ⟨h0, h1⟩
    refine ⟨?_, fun τ => ?_⟩
    · refine ext_inner_left ℝ fun τ => ?_
      have := h0 _ ⟨τ, rfl⟩
      rw [← HiddenState.inner_toEState, EState.inner_def] at this
      simpa using this
    · have := h1 _ ⟨_, ⟨τ, rfl⟩, rfl⟩
      rw [ContinuousLinearMap.coe_coe, inner_diffGen] at this
      simp only [incl0_apply, stateNoU_toEState, EState.σ_mk,
        EState.u_mk, map_zero, inner_zero_left, add_zero, neg_eq_zero] at this
      rw [real_inner_comm]
      exact this

/-- **The discrete Gauss constraint reduces the generator of (6.5)**: its orthogonal complement
is invariant as well (`Lₕ` is skew). -/
theorem waveGen_mem_hiddenGauss_orthogonal {y : HiddenState D}
    (hy : y ∈ (hiddenGauss D hdinj hS)ᗮ) :
    waveGen D hdinj hS y ∈ (hiddenGauss D hdinj hS)ᗮ := by
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro x hx
  rw [real_inner_comm, waveGen_skew, real_inner_comm, hy _ (waveGen_mem_hiddenGauss D hdinj hS hx),
    neg_zero]

end Generic

/-! ### Discretizations: the discrete Gauss constraint tested on projected pairs -/

section Discrete

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} (Q : Discrete D)

/-- **Projected constraint pairs are discrete constraint pairs**: under (5.4)
(`Discrete.Compatible`), `(σ, φ) ∈ Γ` gives `(Π⁰σ, Π̃⁰φ) ∈ Γₕ`
(`d Π⁰σ = Π¹ dσ = Π¹ S⁰ φ = Π¹ S⁰ Π̃⁰ φ = S₀,ₕ Π̃⁰ φ`). -/
theorem proj_mem_Γh (h54 : Q.Compatible) {σ : V0} {φ : Vt0} (hΓ : D.d0 σ = D.S0 φ) :
    ((⟨Q.P0 σ, Q.P0_mem σ⟩ : Q.V0h), (⟨Q.Pt0 φ, Q.Pt0_mem φ⟩ : Q.Vt0h)) ∈ Q.toSegmentH.Γ := by
  rw [Segment.mem_Γ]
  refine Subtype.ext ?_
  change D.d0 (Q.P0 σ) = Q.S0h (Q.Pt0 φ)
  rw [Q.comm0, hΓ, Discrete.S0h_apply, h54]

variable [FiniteDimensional ℝ Q.V1h] [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h]
  (hdinj : Function.Injective Q.toSegmentH.dt0) (hS : Function.Surjective Q.toSegmentH.S0)

/-- The discrete Gauss constraint of the discrete BGG data of `Q` (`hiddenGauss` of
`Q.toSegmentH`). -/
abbrev discreteGauss : Submodule ℝ (HiddenState Q.toSegmentH) := hiddenGauss Q.toSegmentH hdinj hS

/-- **The discrete Gauss constraint tested on projected gradients**: for `x ∈ hiddenGauss` and
`(σ, φ) ∈ Γ`, `⟪uₕ, Π̃¹ d̃φ⟫ = 0`. -/
theorem inner_Pt1_dt0_eq_zero (h54 : Q.Compatible) {x : HiddenState Q.toSegmentH}
    (hx : x ∈ hiddenGauss Q.toSegmentH hdinj hS) {σ : V0} {φ : Vt0} (hΓ : D.d0 σ = D.S0 φ) :
    ⟪((x.toEState.u : Q.Vt1h) : Vt1), Q.Pt1 (D.dt0 φ)⟫ = 0 := by
  have h := ((mem_hiddenGauss_iff _ hdinj hS).1 hx).2 _ (proj_mem_Γh Q h54 hΓ)
  rw [← Q.commt0]
  exact h

/-- The group `e^{t Lₕ}` of the scheme (6.3)/(6.5) of `Q` without source. -/
abbrev discreteGroup [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.W2h]
    [FiniteDimensional ℝ Q.Wt2h] : C0Group ℝ (HiddenState Q.toSegmentH) :=
  waveGroupH Q.toSegmentH hdinj hS

theorem discreteGroup_mem [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.W2h]
    [FiniteDimensional ℝ Q.Wt2h] {v : HiddenState Q.toSegmentH} (hv : v ∈ discreteGauss Q hdinj hS)
    (t : ℝ) : (discreteGroup Q hdinj hS).S t v ∈ discreteGauss Q hdinj hS :=
  mem_of_invariant (waveGen Q.toSegmentH hdinj hS) (waveGen_skew _ _ _) _
    (fun _ hw => waveGen_mem_hiddenGauss _ _ _ hw) hv t

theorem norm_discreteGroup [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.W2h]
    [FiniteDimensional ℝ Q.Wt2h] (v : HiddenState Q.toSegmentH) (t : ℝ) :
    ‖(discreteGroup Q hdinj hS).S t v‖ = ‖v‖ :=
  C0Group.isIsometric_ofBounded (waveGen_skew _ _ _) t v

omit [FiniteDimensional ℝ Q.V1h] [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h] in
/-- The discrete multiplier states `(0, 0, Mₕ, 0)`. -/
abbrev multiplierState (M : Q.W2h) : HiddenState Q.toSegmentH := stateNoU Q.toSegmentH 0 M 0

theorem multiplierState_mem (M : Q.W2h) : multiplierState Q M ∈ discreteGauss Q hdinj hS :=
  stateNoU_mem_hiddenGauss _ hdinj hS M 0

omit [FiniteDimensional ℝ Q.V1h] [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h] in
theorem norm_multiplierState (M : Q.W2h) : ‖multiplierState Q M‖ = ‖M‖ := by
  rw [← HiddenState.norm_toEState, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EState.norm_sq,
    stateNoU_toEState, EState.σ_mk, EState.u_mk, EState.M_mk, EState.ρ_mk]
  simp

omit [FiniteDimensional ℝ Q.V1h] [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h] in
theorem multiplierState_ne_zero {M : Q.W2h} (hM : M ≠ 0) : multiplierState Q M ≠ 0 := fun h =>
  hM (by rw [← norm_eq_zero, ← norm_multiplierState Q M, h, norm_zero])

theorem discreteGauss_ne_bot {M : Q.W2h} (hM : M ≠ 0) : discreteGauss Q hdinj hS ≠ ⊥ :=
  (Submodule.ne_bot_iff _).2 ⟨_, multiplierState_mem Q hdinj hS M, multiplierState_ne_zero Q hM⟩

omit [FiniteDimensional ℝ Q.V1h] [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h] in
theorem norm_u_le (x : HiddenState Q.toSegmentH) :
    ‖((x.toEState.u : Q.Vt1h) : Vt1)‖ ≤ ‖x‖ := by
  change ‖x.toEState.u‖ ≤ _
  rw [← HiddenState.norm_toEState]
  have h := EState.norm_sq x.toEState
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  nlinarith [sq_nonneg ‖x.toEState.σ‖, sq_nonneg ‖x.toEState.M‖, sq_nonneg ‖x.toEState.ρ‖]

/-- **Consistency of the discrete Gauss law**: for `x ∈ hiddenGauss` and `(σ, φ) ∈ Γ`,
`|⟪uₕ, d̃φ⟫| ≤ ‖x‖ ‖d̃φ - Π̃¹ d̃φ‖`. -/
theorem abs_inner_dt0_le (h54 : Q.Compatible) {x : HiddenState Q.toSegmentH}
    (hx : x ∈ hiddenGauss Q.toSegmentH hdinj hS) {σ : V0} {φ : Vt0} (hΓ : D.d0 σ = D.S0 φ) :
    |⟪((x.toEState.u : Q.Vt1h) : Vt1), D.dt0 φ⟫| ≤ ‖x‖ * ‖D.dt0 φ - Q.Pt1 (D.dt0 φ)‖ := by
  have e : ⟪((x.toEState.u : Q.Vt1h) : Vt1), D.dt0 φ⟫ =
      ⟪((x.toEState.u : Q.Vt1h) : Vt1), D.dt0 φ - Q.Pt1 (D.dt0 φ)⟫ := by
    rw [inner_sub_right, inner_Pt1_dt0_eq_zero Q hdinj hS h54 hx hΓ, sub_zero]
  rw [e]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_u_le Q x) (norm_nonneg _))

end Discrete

/-! ### Families of discretizations: weak convergence of the discrete Gauss constraint -/

section Family

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  (D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2)
  {E0 E1 E2 E3 : Type*}
  [NormedAddCommGroup E0] [InnerProductSpace ℝ E0]
  [NormedAddCommGroup E1] [InnerProductSpace ℝ E1]
  [NormedAddCommGroup E2] [InnerProductSpace ℝ E2]
  [NormedAddCommGroup E3] [InnerProductSpace ℝ E3]
  (j1 : Vt1 →ₗ[ℝ] E1)

/-- The bottom `0`-forms `φ` with `S⁰φ ∈ d⁰V⁰`: the second components of `Γ`. -/
def gammaSnd : Submodule ℝ Vt0 := D.Γ.map (LinearMap.snd ℝ V0 Vt0)

variable {D} in
theorem mem_gammaSnd {φ : Vt0} : φ ∈ gammaSnd D ↔ ∃ σ, D.d0 σ = D.S0 φ := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, D.mem_Γ.1 hp⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨(σ, φ), D.mem_Γ.2 hσ, rfl⟩

/-- `(τ, φ) ↦ (τ, j₁ d̃φ, 0, 0)`, with values in a continuous energy space `E₀ × E₁ × E₂ × E₃`
into which `Ṽ¹` is read by `j₁`. -/
def gaussMap : E0 × Vt0 →ₗ[ℝ] EState E0 E1 E2 E3 where
  toFun q := EState.mk q.1 (j1 (D.dt0 q.2)) 0 0
  map_add' q q' := by
    rw [← EState.mk_add]
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_zero]
  map_smul' c q := by
    rw [RingHom.id_apply, ← EState.mk_smul]
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_zero]

/-- The complement of the continuous Gauss constraint: the states `(τ, j₁ d̃φ, 0, 0)`, `τ ∈ E₀`,
`φ ∈ gammaSnd`. -/
def gaussCompl : Submodule ℝ (EState E0 E1 E2 E3) :=
  (Submodule.prod ⊤ (gammaSnd D)).map (gaussMap D (E0 := E0) (E2 := E2) (E3 := E3) j1)

/-- **The continuous Gauss constraint**: `σ = 0` and `u ⊥ j₁ d̃φ` for every `(σ', φ) ∈ Γ`, i.e.
`D₀* u = 0` for the first operator `D₀ = (0 d̃)` of the BGG complex (5.1), read through `j₁`. -/
def gaussSub : Submodule ℝ (EState E0 E1 E2 E3) :=
  (gaussCompl D (E0 := E0) (E2 := E2) (E3 := E3) j1)ᗮ

theorem inner_gaussMap (τ : E0) (φ : Vt0) (a : EState E0 E1 E2 E3) :
    ⟪gaussMap D j1 (τ, φ), a⟫ = ⟪τ, a.σ⟫ + ⟪j1 (D.dt0 φ), a.u⟫ := by
  change ⟪EState.mk τ (j1 (D.dt0 φ)) 0 0, a⟫ = _
  rw [EState.inner_def]
  simp

theorem mem_gaussSub_iff {a : EState E0 E1 E2 E3} :
    a ∈ gaussSub D j1 ↔ a.σ = 0 ∧ ∀ φ ∈ gammaSnd D, ⟪a.u, j1 (D.dt0 φ)⟫ = 0 := by
  rw [gaussSub, Submodule.mem_orthogonal]
  constructor
  · intro h
    refine ⟨ext_inner_left ℝ fun τ => ?_, fun φ hφ => ?_⟩
    · have := h _ ⟨(τ, 0), ⟨Submodule.mem_top, (gammaSnd D).zero_mem⟩, rfl⟩
      rw [inner_gaussMap] at this
      simpa using this
    · have := h _ ⟨(0, φ), ⟨Submodule.mem_top, hφ⟩, rfl⟩
      rw [inner_gaussMap, inner_zero_left, zero_add] at this
      rw [real_inner_comm]
      exact this
  · rintro ⟨h0, h1⟩ _ ⟨⟨τ, φ⟩, ⟨-, hφ⟩, rfl⟩
    rw [inner_gaussMap, h0, inner_zero_right, zero_add, real_inner_comm]
    exact h1 φ hφ

variable {D} {κ : Type*} (l : Filter κ) (Q : κ → Discrete D)
  [∀ h, FiniteDimensional ℝ (Q h).V1h] [∀ h, FiniteDimensional ℝ (Q h).Vt0h]
  [∀ h, FiniteDimensional ℝ (Q h).Vt1h]
  (hdinj : ∀ h, Function.Injective (Q h).toSegmentH.dt0)
  (hS : ∀ h, Function.Surjective (Q h).toSegmentH.S0)

/-- **The read discrete Gauss constraints converge weakly to the continuous Gauss constraint,
uniformly on bounded sets.** Let `Qₕ` be discretizations satisfying (5.4) whose projections `Π̃¹`
converge strongly on `d̃(gammaSnd)`, and `rₕ` reading maps of the hidden states into a complete
continuous energy space, bounded by `1`, reading `σ` linearly (`j₀`) and `u` isometrically
(`j₁`). Then for every `y ⊥ gaussSub` and `ε > 0`, eventually `|⟪rₕ x, y⟫| ≤ ε ‖x‖` for every
`x ∈ hiddenGauss` (from `⟪uₕ, Π̃¹ d̃φ⟫ = 0` on `Γₕ`). -/
theorem eventually_abs_inner_le_of_mem_hiddenGauss [CompleteSpace (EState E0 E1 E2 E3)]
    (h54 : ∀ h, (Q h).Compatible)
    (hP : ∀ φ ∈ gammaSnd D, Tendsto (fun h => ‖D.dt0 φ - (Q h).Pt1 (D.dt0 φ)‖) l (𝓝 0))
    (j0 : V0 →ₗ[ℝ] E0) (hj1 : ∀ a b, ⟪j1 a, j1 b⟫ = ⟪a, b⟫)
    (r : ∀ h, HiddenState (Q h).toSegmentH → EState E0 E1 E2 E3)
    (hr0 : ∀ h x, (r h x).σ = j0 ((x.toEState.σ : (Q h).V0h) : V0))
    (hr1 : ∀ h x, (r h x).u = j1 ((x.toEState.u : (Q h).Vt1h) : Vt1))
    (hrn : ∀ h x, ‖r h x‖ ≤ ‖x‖)
    {y : EState E0 E1 E2 E3} (hy : y ∈ (gaussSub D (E0 := E0) (E2 := E2) (E3 := E3) j1)ᗮ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ h in l, ∀ x ∈ hiddenGauss (Q h).toSegmentH (hdinj h) (hS h),
      |⟪r h x, y⟫| ≤ ε * ‖x‖ := by
  have hcl : y ∈ closure
      (gaussCompl D (E0 := E0) (E2 := E2) (E3 := E3) j1 : Set (EState E0 E1 E2 E3)) := by
    rw [gaussSub, Submodule.orthogonal_orthogonal_eq_closure] at hy
    exact hy
  obtain ⟨g, hg, hyg⟩ := Metric.mem_closure_iff.1 hcl (ε / 2) (half_pos hε)
  obtain ⟨⟨τ, φ⟩, ⟨-, hφ⟩, rfl⟩ := hg
  obtain ⟨σ', hσ'⟩ := mem_gammaSnd.1 hφ
  filter_upwards [(hP φ hφ).eventually (gt_mem_nhds (half_pos hε))] with h hh x hx
  have h0 : (x.toEState.σ : (Q h).V0h) = 0 := hx.1
  have h1 : |⟪r h x, gaussMap D j1 (τ, φ)⟫| ≤ ‖x‖ * (ε / 2) := by
    rw [real_inner_comm, inner_gaussMap, hr0, hr1, h0, ZeroMemClass.coe_zero, map_zero,
      inner_zero_right, zero_add, hj1, real_inner_comm]
    exact (abs_inner_dt0_le (Q h) (hdinj h) (hS h) (h54 h) hx hσ').trans
      (mul_le_mul_of_nonneg_left hh.le (norm_nonneg x))
  have h2 : |⟪r h x, y - gaussMap D j1 (τ, φ)⟫| ≤ ‖x‖ * (ε / 2) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [dist_eq_norm] at hyg
    exact mul_le_mul (hrn h x) hyg.le (norm_nonneg _) (norm_nonneg _)
  have e : ⟪r h x, y⟫ = ⟪r h x, gaussMap D j1 (τ, φ)⟫ + ⟪r h x, y - gaussMap D j1 (τ, φ)⟫ := by
    rw [inner_sub_right]; ring
  rw [e]
  calc _ ≤ |⟪r h x, gaussMap D j1 (τ, φ)⟫| + |⟪r h x, y - gaussMap D j1 (τ, φ)⟫| :=
        abs_add_le _ _
    _ ≤ ‖x‖ * (ε / 2) + ‖x‖ * (ε / 2) := add_le_add h1 h2
    _ = ε * ‖x‖ := by ring

/-- **Bounded families of discrete Gauss states are read weakly into the continuous Gauss
constraint**: `⟪rₕ xₕ, y⟫ → 0` for every `y ⊥ gaussSub`. -/
theorem tendsto_inner_of_mem_hiddenGauss [CompleteSpace (EState E0 E1 E2 E3)]
    (h54 : ∀ h, (Q h).Compatible)
    (hP : ∀ φ ∈ gammaSnd D, Tendsto (fun h => ‖D.dt0 φ - (Q h).Pt1 (D.dt0 φ)‖) l (𝓝 0))
    (j0 : V0 →ₗ[ℝ] E0) (hj1 : ∀ a b, ⟪j1 a, j1 b⟫ = ⟪a, b⟫)
    (r : ∀ h, HiddenState (Q h).toSegmentH → EState E0 E1 E2 E3)
    (hr0 : ∀ h x, (r h x).σ = j0 ((x.toEState.σ : (Q h).V0h) : V0))
    (hr1 : ∀ h x, (r h x).u = j1 ((x.toEState.u : (Q h).Vt1h) : Vt1))
    (hrn : ∀ h x, ‖r h x‖ ≤ ‖x‖)
    {x : ∀ h, HiddenState (Q h).toSegmentH} (hx : ∀ h, x h ∈ hiddenGauss _ (hdinj h) (hS h))
    {c : ℝ} (hc : ∀ᶠ h in l, ‖x h‖ ≤ c)
    {y : EState E0 E1 E2 E3} (hy : y ∈ (gaussSub D (E0 := E0) (E2 := E2) (E3 := E3) j1)ᗮ) :
    Tendsto (fun h => ⟪r h (x h), y⟫) l (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hc1 : 0 < |c| + 1 := by positivity
  filter_upwards [eventually_abs_inner_le_of_mem_hiddenGauss j1 l Q hdinj hS h54 hP j0 hj1 r hr0
    hr1 hrn hy (div_pos hε hc1), hc] with h hh hch
  rw [Real.dist_eq, sub_zero]
  calc _ ≤ ε / (|c| + 1) * ‖x h‖ := hh _ (hx h)
    _ ≤ ε / (|c| + 1) * |c| :=
        mul_le_mul_of_nonneg_left (hch.trans (le_abs_self c)) (div_pos hε hc1).le
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hc1]
        nlinarith [abs_nonneg c]

/-- **Weak limits of read bounded families of discrete Gauss states satisfy the continuous Gauss
constraint.** -/
theorem mem_gaussSub_of_tendsto_inner [CompleteSpace (EState E0 E1 E2 E3)] [l.NeBot]
    (h54 : ∀ h, (Q h).Compatible)
    (hP : ∀ φ ∈ gammaSnd D, Tendsto (fun h => ‖D.dt0 φ - (Q h).Pt1 (D.dt0 φ)‖) l (𝓝 0))
    (j0 : V0 →ₗ[ℝ] E0) (hj1 : ∀ a b, ⟪j1 a, j1 b⟫ = ⟪a, b⟫)
    (r : ∀ h, HiddenState (Q h).toSegmentH → EState E0 E1 E2 E3)
    (hr0 : ∀ h x, (r h x).σ = j0 ((x.toEState.σ : (Q h).V0h) : V0))
    (hr1 : ∀ h x, (r h x).u = j1 ((x.toEState.u : (Q h).Vt1h) : Vt1))
    (hrn : ∀ h x, ‖r h x‖ ≤ ‖x‖)
    {x : ∀ h, HiddenState (Q h).toSegmentH} (hx : ∀ h, x h ∈ hiddenGauss _ (hdinj h) (hS h))
    {c : ℝ} (hc : ∀ᶠ h in l, ‖x h‖ ≤ c) {ξ : EState E0 E1 E2 E3}
    (hξ : ∀ z, Tendsto (fun h => ⟪r h (x h), z⟫) l (𝓝 ⟪ξ, z⟫)) :
    ξ ∈ gaussSub D (E0 := E0) (E2 := E2) (E3 := E3) j1 := by
  rw [gaussSub, Submodule.mem_orthogonal]
  intro g hg
  have hg' : g ∈ (gaussSub D (E0 := E0) (E2 := E2) (E3 := E3) j1)ᗮ :=
    Submodule.le_orthogonal_orthogonal _ hg
  have h0 := tendsto_inner_of_mem_hiddenGauss j1 l Q hdinj hS h54 hP j0 hj1 r hr0 hr1 hrn hx hc hg'
  rw [real_inner_comm]
  exact tendsto_nhds_unique (hξ g) h0

/-- Strong limits: if `rₕ xₕ → ξ` for a bounded family of discrete Gauss states, then
`ξ ∈ gaussSub`. -/
theorem mem_gaussSub_of_tendsto [CompleteSpace (EState E0 E1 E2 E3)] [l.NeBot]
    (h54 : ∀ h, (Q h).Compatible)
    (hP : ∀ φ ∈ gammaSnd D, Tendsto (fun h => ‖D.dt0 φ - (Q h).Pt1 (D.dt0 φ)‖) l (𝓝 0))
    (j0 : V0 →ₗ[ℝ] E0) (hj1 : ∀ a b, ⟪j1 a, j1 b⟫ = ⟪a, b⟫)
    (r : ∀ h, HiddenState (Q h).toSegmentH → EState E0 E1 E2 E3)
    (hr0 : ∀ h x, (r h x).σ = j0 ((x.toEState.σ : (Q h).V0h) : V0))
    (hr1 : ∀ h x, (r h x).u = j1 ((x.toEState.u : (Q h).Vt1h) : Vt1))
    (hrn : ∀ h x, ‖r h x‖ ≤ ‖x‖)
    {x : ∀ h, HiddenState (Q h).toSegmentH} (hx : ∀ h, x h ∈ hiddenGauss _ (hdinj h) (hS h))
    {c : ℝ} (hc : ∀ᶠ h in l, ‖x h‖ ≤ c) {ξ : EState E0 E1 E2 E3}
    (hξ : Tendsto (fun h => r h (x h)) l (𝓝 ξ)) :
    ξ ∈ gaussSub D (E0 := E0) (E2 := E2) (E3 := E3) j1 :=
  mem_gaussSub_of_tendsto_inner j1 l Q hdinj hS h54 hP j0 hj1 r hr0 hr1 hrn hx hc fun _ =>
    hξ.inner tendsto_const_nhds

/-- `mem_gaussSub_of_tendsto` through readings `ιₕ` with a continuous left inverse `R⁻¹` onto the
continuous energy space (`R⁻¹ ∘ ιₕ = rₕ`): if `ιₕ xₕ → X`, then `R⁻¹ X ∈ gaussSub`. -/
theorem mem_gaussSub_of_tendsto_comp [CompleteSpace (EState E0 E1 E2 E3)] [l.NeBot]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (h54 : ∀ h, (Q h).Compatible)
    (hP : ∀ φ ∈ gammaSnd D, Tendsto (fun h => ‖D.dt0 φ - (Q h).Pt1 (D.dt0 φ)‖) l (𝓝 0))
    (j0 : V0 →ₗ[ℝ] E0) (hj1 : ∀ a b, ⟪j1 a, j1 b⟫ = ⟪a, b⟫)
    (r : ∀ h, HiddenState (Q h).toSegmentH → EState E0 E1 E2 E3)
    (hr0 : ∀ h x, (r h x).σ = j0 ((x.toEState.σ : (Q h).V0h) : V0))
    (hr1 : ∀ h x, (r h x).u = j1 ((x.toEState.u : (Q h).Vt1h) : Vt1))
    (hrn : ∀ h x, ‖r h x‖ ≤ ‖x‖)
    (Rinv : F →L[ℝ] EState E0 E1 E2 E3) (ι : ∀ h, HiddenState (Q h).toSegmentH → F)
    (hι : ∀ h x, Rinv (ι h x) = r h x)
    {x : ∀ h, HiddenState (Q h).toSegmentH} (hx : ∀ h, x h ∈ hiddenGauss _ (hdinj h) (hS h))
    {c : ℝ} (hc : ∀ᶠ h in l, ‖x h‖ ≤ c) {X : F} (hX : Tendsto (fun h => ι h (x h)) l (𝓝 X)) :
    Rinv X ∈ gaussSub D (E0 := E0) (E2 := E2) (E3 := E3) j1 := by
  have h := (Rinv.continuous.tendsto X).comp hX
  have e : (Rinv ∘ fun h => ι h (x h)) = fun h => r h (x h) := funext fun h => hι h (x h)
  rw [e] at h
  exact mem_gaussSub_of_tendsto j1 l Q hdinj hS h54 hP j0 hj1 r hr0 hr1 hrn hx hc h

section Group

variable [∀ h, FiniteDimensional ℝ (Q h).V0h] [∀ h, FiniteDimensional ℝ (Q h).W2h]
  [∀ h, FiniteDimensional ℝ (Q h).Wt2h]

/-- **Along the discrete solutions, uniformly in time**: for bounded discrete Gauss data
`vₕ ∈ hiddenGauss`, the read discrete solutions `rₕ e^{t Lₕ} vₕ` converge weakly to the
continuous Gauss constraint uniformly in `t ∈ ℝ`: `⟪rₕ e^{t Lₕ} vₕ, y⟫ → 0` uniformly for every
`y ⊥ gaussSub` (`hiddenGauss` is invariant and `e^{t Lₕ}` is isometric). No convergence of the
scheme is used. -/
theorem tendstoUniformly_inner_group [CompleteSpace (EState E0 E1 E2 E3)]
    (h54 : ∀ h, (Q h).Compatible)
    (hP : ∀ φ ∈ gammaSnd D, Tendsto (fun h => ‖D.dt0 φ - (Q h).Pt1 (D.dt0 φ)‖) l (𝓝 0))
    (j0 : V0 →ₗ[ℝ] E0) (hj1 : ∀ a b, ⟪j1 a, j1 b⟫ = ⟪a, b⟫)
    (r : ∀ h, HiddenState (Q h).toSegmentH → EState E0 E1 E2 E3)
    (hr0 : ∀ h x, (r h x).σ = j0 ((x.toEState.σ : (Q h).V0h) : V0))
    (hr1 : ∀ h x, (r h x).u = j1 ((x.toEState.u : (Q h).Vt1h) : Vt1))
    (hrn : ∀ h x, ‖r h x‖ ≤ ‖x‖)
    {v : ∀ h, HiddenState (Q h).toSegmentH} (hv : ∀ h, v h ∈ hiddenGauss _ (hdinj h) (hS h))
    {c : ℝ} (hc : ∀ᶠ h in l, ‖v h‖ ≤ c)
    {y : EState E0 E1 E2 E3} (hy : y ∈ (gaussSub D (E0 := E0) (E2 := E2) (E3 := E3) j1)ᗮ) :
    TendstoUniformly
      (fun h t => ⟪r h ((waveGroupH (Q h).toSegmentH (hdinj h) (hS h)).S t (v h)), y⟫)
      (fun _ => 0) l := by
  refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
  have hc1 : 0 < |c| + 1 := by positivity
  filter_upwards [eventually_abs_inner_le_of_mem_hiddenGauss j1 l Q hdinj hS h54 hP j0 hj1 r hr0
    hr1 hrn hy (div_pos hε hc1), hc] with h hh hch t
  have hmem := mem_of_invariant (waveGen (Q h).toSegmentH (hdinj h) (hS h))
    (waveGen_skew _ _ _) (hiddenGauss _ (hdinj h) (hS h))
    (fun w hw => waveGen_mem_hiddenGauss _ _ _ hw) (hv h) t
  have hn : ‖(waveGroupH (Q h).toSegmentH (hdinj h) (hS h)).S t (v h)‖ = ‖v h‖ :=
    C0Group.isIsometric_ofBounded (waveGen_skew _ _ _) t (v h)
  rw [Real.dist_eq, zero_sub, abs_neg]
  calc _ ≤ ε / (|c| + 1) * ‖(waveGroupH (Q h).toSegmentH (hdinj h) (hS h)).S t (v h)‖ :=
        hh _ hmem
    _ ≤ ε / (|c| + 1) * |c| := by
        rw [hn]
        exact mul_le_mul_of_nonneg_left (hch.trans (le_abs_self c)) (div_pos hε hc1).le
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hc1]
        nlinarith [abs_nonneg c]

/-- `tendstoUniformly_inner_group` through an isometric identification `R` of the continuous
energy space with the state space of the continuous problem: `⟪ιₕ e^{t Lₕ} vₕ, R y⟫ → 0`
uniformly in `t ∈ ℝ` for readings `ιₕ = R ∘ rₕ`. -/
theorem tendstoUniformly_inner_group_comp [CompleteSpace (EState E0 E1 E2 E3)]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (h54 : ∀ h, (Q h).Compatible)
    (hP : ∀ φ ∈ gammaSnd D, Tendsto (fun h => ‖D.dt0 φ - (Q h).Pt1 (D.dt0 φ)‖) l (𝓝 0))
    (j0 : V0 →ₗ[ℝ] E0) (hj1 : ∀ a b, ⟪j1 a, j1 b⟫ = ⟪a, b⟫)
    (r : ∀ h, HiddenState (Q h).toSegmentH → EState E0 E1 E2 E3)
    (hr0 : ∀ h x, (r h x).σ = j0 ((x.toEState.σ : (Q h).V0h) : V0))
    (hr1 : ∀ h x, (r h x).u = j1 ((x.toEState.u : (Q h).Vt1h) : Vt1))
    (hrn : ∀ h x, ‖r h x‖ ≤ ‖x‖)
    (R : EState E0 E1 E2 E3 → F) (hR : ∀ a b, ⟪R a, R b⟫ = ⟪a, b⟫)
    (ι : ∀ h, HiddenState (Q h).toSegmentH → F) (hι : ∀ h x, ι h x = R (r h x))
    {v : ∀ h, HiddenState (Q h).toSegmentH} (hv : ∀ h, v h ∈ hiddenGauss _ (hdinj h) (hS h))
    {c : ℝ} (hc : ∀ᶠ h in l, ‖v h‖ ≤ c)
    {y : EState E0 E1 E2 E3} (hy : y ∈ (gaussSub D (E0 := E0) (E2 := E2) (E3 := E3) j1)ᗮ) :
    TendstoUniformly
      (fun h t => ⟪ι h ((discreteGroup (Q h) (hdinj h) (hS h)).S t (v h)), R y⟫)
      (fun _ => 0) l := by
  have e : (fun h t => ⟪ι h ((discreteGroup (Q h) (hdinj h) (hS h)).S t (v h)), R y⟫) =
      fun h t => ⟪r h ((waveGroupH (Q h).toSegmentH (hdinj h) (hS h)).S t (v h)), y⟫ :=
    funext fun h => funext fun t => by rw [hι, hR]
  rw [e]
  exact tendstoUniformly_inner_group j1 l Q hdinj hS h54 hP j0 hj1 r hr0 hr1 hrn hv hc hy

end Group

end Family

/-- Squeeze for uniform convergence to `0` of nonnegative functions. -/
theorem tendstoUniformlyOn_zero_of_le {ι α : Type*} {l : Filter ι} {s : Set α} {f g : ι → α → ℝ}
    (hf : TendstoUniformlyOn f (fun _ => 0) l s) (hg0 : ∀ i a, 0 ≤ g i a)
    (hgf : ∀ i a, g i a ≤ f i a) : TendstoUniformlyOn g (fun _ => 0) l s := by
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hf ε hε] with i hi a ha
  have h := hi a ha
  rw [dist_zero_left, Real.norm_eq_abs] at h ⊢
  rw [abs_of_nonneg (hg0 i a)]
  exact (hgf i a).trans_lt ((le_abs_self _).trans_lt h)

/-! ### Mirror boundary conditions -/

section Mirror

open Feec.Models.Cube.MirrorWeakSymmetry Feec.Models.Cube.RowWise
open Feec.Models.Cube.MirrorBGG (SpaceQ W2Q complexQ tsdQ)
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- **The continuous Gauss constraint of the mirror data**, in the real energy space
`L²Λ⁰ × (L²Λ¹)³ × L²Λ² × (L²Λ²)³`: `σ = 0` and `u ⊥ d̃φ` for every `(σ', φ) ∈ Γ`
(`grad σ' = φ`), the degree-`0` part of the TSD constraint. -/
abbrev mirrorGauss : Submodule ℝ REnergy :=
  gaussSub mirrorBGGSegment (E0 := W0) (E2 := W2) (E3 := Wv W2) bIncl1

theorem mem_mirrorGauss_iff {a : REnergy} :
    a ∈ mirrorGauss ↔ a.σ = 0 ∧ ∀ φ ∈ gammaSnd mirrorBGGSegment, ⟪a.u, bIncl1 (bD0 φ)⟫ = 0 :=
  mem_gaussSub_iff _ _

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 ∅
    Feec.FiniteElement.PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3,
    Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 {a} Feec.FiniteElement.PolySeq.lagrangeP2 ρ C)

/-- The discrete Gauss constraint of the mirror scheme at level `N`. -/
abbrev mirrorHiddenGauss (N : ℕ) : Submodule ℝ (mirrorHidden hT hB N) :=
  discreteGauss (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
    (mirrorWave_S0_surjective hT hB N)

/-- The bottom-row projections `Π̃¹` of the mirror scheme converge strongly. -/
theorem tendsto_norm_sub_mirrorPt1 (v : BU1) :
    Tendsto (fun N => ‖v - (mirrorFEM hT hB N).Pt1 v‖) atTop (𝓝 0) := by
  have h : ∀ a ∈ Finset.univ, Tendsto (fun N => ‖(v a : W1) - ((hB a).proj N).π 1 (v a)‖ ^ 2)
      atTop (𝓝 0) := fun a _ => by
    simpa using ((hB a).tendsto_norm_sub_proj 1 (v a : W1)).pow 2
  have hs := tendsto_finsetSum Finset.univ h
  rw [Finset.sum_const_zero] at hs
  have e : ∀ N, ‖v - (mirrorFEM hT hB N).Pt1 v‖ =
      √(∑ a, ‖(v a : W1) - ((hB a).proj N).π 1 (v a)‖ ^ 2) := fun N => by
    rw [← Real.sqrt_sq (norm_nonneg (v - _)), norm_sq_BU1]
    rfl
  have hl := (Real.continuous_sqrt.tendsto 0).comp hs
  rw [Real.sqrt_zero] at hl
  simp only [e]
  exact hl

/-- **The read discrete Gauss constraint of the mirror scheme converges weakly to the continuous
Gauss constraint, uniformly on bounded sets**: for every `y ⊥ mirrorGauss` and `ε > 0`,
eventually `|⟪ιₕ x, y⟫| ≤ ε ‖x‖` for all `x ∈ hiddenGauss` (`ιₕ = mirrorFE`, the reading map
of `mirrorFEMReal` before the identification with mirror states). -/
theorem eventually_abs_inner_mirrorFE_le {y : REnergy} (hy : y ∈ mirrorGaussᗮ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ x ∈ mirrorHiddenGauss hT hB N, |⟪mirrorFE hT hB N x, y⟫| ≤ ε * ‖x‖ :=
  eventually_abs_inner_le_of_mem_hiddenGauss bIncl1 atTop (mirrorFEM hT hB)
    (mirrorWave_dt0_injective hT hB) (mirrorWave_S0_surjective hT hB) (mirrorFEM_compatible hT hB)
    (fun φ _ => tendsto_norm_sub_mirrorPt1 hT hB (bD0 φ))
    ((TD0.domain.subtype : TU0 →ₗ[ℝ] W0)) (fun a b => (inner_BU1 a b).symm)
    (fun N => mirrorFE hT hB N) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun N x => (norm_mirrorFE hT hB N x).le) hy hε

/-- **Bounded families of discrete Gauss states of the mirror scheme are read weakly into the
continuous Gauss constraint.** -/
theorem tendsto_inner_mirrorFE {x : ∀ N, mirrorHidden hT hB N}
    (hx : ∀ N, x N ∈ mirrorHiddenGauss hT hB N) {c : ℝ} (hc : ∀ᶠ N in atTop, ‖x N‖ ≤ c)
    {y : REnergy}
    (hy : y ∈ mirrorGaussᗮ) : Tendsto (fun N => ⟪mirrorFE hT hB N (x N), y⟫) atTop (𝓝 0) :=
  tendsto_inner_of_mem_hiddenGauss bIncl1 atTop (mirrorFEM hT hB)
    (mirrorWave_dt0_injective hT hB) (mirrorWave_S0_surjective hT hB) (mirrorFEM_compatible hT hB)
    (fun φ _ => tendsto_norm_sub_mirrorPt1 hT hB (bD0 φ))
    ((TD0.domain.subtype : TU0 →ₗ[ℝ] W0)) (fun a b => (inner_BU1 a b).symm)
    (fun N => mirrorFE hT hB N) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun N x => (norm_mirrorFE hT hB N x).le) hx hc hy

/-- **Limits of read discrete Gauss states of the mirror scheme satisfy the continuous Gauss
constraint**: if `ιₕ xₕ → ξ` with `xₕ ∈ hiddenGauss` bounded, then `ξ ∈ mirrorGauss`. -/
theorem mem_mirrorGauss_of_tendsto {x : ∀ N, mirrorHidden hT hB N}
    (hx : ∀ N, x N ∈ mirrorHiddenGauss hT hB N) {c : ℝ} (hc : ∀ᶠ N in atTop, ‖x N‖ ≤ c)
    {ξ : REnergy}
    (hξ : Tendsto (fun N => mirrorFE hT hB N (x N)) atTop (𝓝 ξ)) : ξ ∈ mirrorGauss :=
  mem_gaussSub_of_tendsto bIncl1 atTop (mirrorFEM hT hB)
    (mirrorWave_dt0_injective hT hB) (mirrorWave_S0_surjective hT hB) (mirrorFEM_compatible hT hB)
    (fun φ _ => tendsto_norm_sub_mirrorPt1 hT hB (bD0 φ))
    ((TD0.domain.subtype : TU0 →ₗ[ℝ] W0)) (fun a b => (inner_BU1 a b).symm)
    (fun N => mirrorFE hT hB N) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun N x => (norm_mirrorFE hT hB N x).le) hx hc hξ

/-- `Rt` preserves the real inner products. -/
theorem inner_mirrorReEmb (a b : REnergy) : ⟪mirrorReEmb a, mirrorReEmb b⟫ = ⟪a, b⟫ :=
  LinearIsometry.inner_map_map (⟨mirrorReEmb.toLinearMap, norm_mirrorReEmb⟩ :
    REnergy →ₗᵢ[ℝ] PiLp 2 SpaceQ) a b

set_option maxHeartbeats 2000000 in
/-- **The discrete solutions of the mirror scheme from discrete Gauss data are read weakly into
the continuous Gauss constraint, uniformly in time**: for bounded `vₙ ∈ hiddenGauss` and every
`y ⊥ mirrorGauss`, `⟪ιₙ e^{t Lₙ} vₙ, Rt y⟫ → 0` uniformly in `t ∈ ℝ` (`ιₙ = mirrorEmb`,
`e^{t Lₙ} = waveGroupH`: the discrete solutions of `mirrorFEMReal`), whatever the limit behaviour
of `ιₙ vₙ`. -/
theorem tendstoUniformly_inner_mirrorEmb_group {v : ∀ N, mirrorHidden hT hB N}
    (hv : ∀ N, v N ∈ mirrorHiddenGauss hT hB N) {c : ℝ} (hc : ∀ᶠ N in atTop, ‖v N‖ ≤ c)
    {y : REnergy}
    (hy : y ∈ mirrorGaussᗮ) :
    TendstoUniformly (fun N t => ⟪mirrorEmb hT hB N ((discreteGroup (mirrorFEM hT hB N)
      (mirrorWave_dt0_injective hT hB N) (mirrorWave_S0_surjective hT hB N)).S t (v N)),
        mirrorReEmb y⟫) (fun _ => 0) atTop :=
  tendstoUniformly_inner_group_comp bIncl1 atTop (mirrorFEM hT hB)
    (mirrorWave_dt0_injective hT hB) (mirrorWave_S0_surjective hT hB) (mirrorFEM_compatible hT hB)
    (fun φ _ => tendsto_norm_sub_mirrorPt1 hT hB (bD0 φ))
    ((TD0.domain.subtype : TU0 →ₗ[ℝ] W0)) (fun a b => (inner_BU1 a b).symm)
    (fun N => mirrorFE hT hB N) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun N x => (norm_mirrorFE hT hB N x).le) mirrorReEmb inner_mirrorReEmb
    (fun N => mirrorEmb hT hB N) (fun _ _ => rfl) hv hc hy

/-! #### The TSD constraint lies in the continuous Gauss constraint -/

/-- **TSD fields are divergence-free against all bottom `0`-forms**: for `E ∈ tsdQ 1`,
`⟪Re E, d̃ψ⟫ = 0` for every `ψ ∈ ∏ₐ H_{a}Λ⁰(Q)` (the general-field version of
`Feec.Models.Cube.MirrorWeakSymmetry.inner_rowsBU_bD0`). -/
theorem inner_rowsW1L_bD0 {E : Feec.Models.Cube.Mirror.MQ} (hE : E ∈ tsdQ 1) (ψ : BU0) :
    ⟪rowsW1L E, bIncl1 (bD0 ψ)⟫ = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [rowsW1L_apply, bIncl1_apply, bD0_apply,
    ← LinearIsometryEquiv.inner_map_map
      (Feec.Models.Cube.MirrorWeakSymmetry.cQ (Feec.Domain.formIdx 3 ((1 : ℕ) : ℤ))),
    LinearIsometryEquiv.apply_symm_apply]
  obtain ⟨hψ, eψ⟩ := dPart_Q_of_cube (ψ a)
  have hE' : ∀ n, (Feec.Models.Cube.MirrorBGG.J₁ E : (Fin 3 → ℤ) → Feec.Fourier.GradCurl.Mat) n ∈
      Feec.Fourier.GradCurl.tsd (Feec.Fourier.Torus.freq n) := fun n =>
    MeasureTheory.Measure.ae_count_iff.1 (Feec.Operator.mem_fibreSub.1 hE) n
  have h := inner_rowRe_dPart_zero E hE' a ⟨_, hψ⟩
  calc _ = ⟪rowRe E a, (Feec.Models.Cube.DeRhamIdent.dPart (Feec.Models.Cube.Geometry.Q (Fin 3))
        {a} ((0 : ℕ) : ℤ) ⟨_, hψ⟩ :
        Feec.Domain.L2F ℝ (Feec.Models.Cube.Geometry.Q (Fin 3))
          (Feec.Domain.formIdx 3 ((1 : ℕ) : ℤ)))⟫ :=
          congrArg (fun z => ⟪rowRe E a, z⟫) eψ.symm
    _ = 0 := h

/-- **The real part of a mirror state** as a real forms state:
`y ↦ (Re σ, Re E (rows), Re M, ⋆Re B (rows))`, the left inverse of `Rt = mirrorReEmb`. -/
def mirrorRe : PiLp 2 SpaceQ →L[ℝ] REnergy :=
  EState.mkL.toContinuousLinearMap ∘L ((re0 ∘L slot0).prod ((rowsW1L ∘L slot1).prod
    ((reM ∘L slotM).prod (rowsW2L ∘L slotB))))

theorem mirrorRe_apply (y : PiLp 2 SpaceQ) :
    mirrorRe y = EState.mk (re0 (slot0 y)) (rowsW1L (slot1 y)) (reM (slotM y))
      (rowsW2L (slotB y)) := rfl

theorem norm_sq_mirrorRe_add (y : PiLp 2 SpaceQ) :
    ‖y‖ ^ 2 = ‖mirrorRe y‖ ^ 2 + ‖mirrorRe (-Complex.I • y)‖ ^ 2 := by
  have h := norm_sq_sub_mirrorReEmb y 0 0
  have z0 : (0 : REnergy).σ = 0 := rfl
  have z1 : (0 : REnergy).u = 0 := rfl
  have z2 : (0 : REnergy).M = 0 := rfl
  have z3 : (0 : REnergy).ρ = 0 := rfl
  simp only [map_zero, smul_zero, sub_zero, z0, z1, z2, z3] at h
  rw [EState.norm_sq, EState.norm_sq, mirrorRe_apply, mirrorRe_apply]
  simp only [EState.σ_mk, EState.u_mk, EState.M_mk, EState.ρ_mk, slot0_smul, slot1_smul,
    slotM_smul, slotB_smul]
  rw [h]

theorem norm_mirrorRe_le (y : PiLp 2 SpaceQ) : ‖mirrorRe y‖ ≤ ‖y‖ := by
  have h := norm_sq_mirrorRe_add y
  have h2 := sq_nonneg ‖mirrorRe (-Complex.I • y)‖
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

/-- **The real part of a TSD state satisfies the continuous Gauss constraint**: `σ = 0` and the
real rows of a TSD `E` are orthogonal to all of `d̃(∏ₐ H_{a}Λ⁰)` (a fortiori to `d̃(gammaSnd)`).
So `mirrorGauss` is a relaxation of TSD: it constrains `σ` and `u` only. -/
theorem mirrorRe_mem_mirrorGauss {y : PiLp 2 SpaceQ} (hy : y ∈ tsdQℝ) :
    mirrorRe y ∈ mirrorGauss := by
  refine mem_mirrorGauss_iff.2 ⟨?_, fun φ _ => inner_rowsW1L_bD0 (hy 1) φ⟩
  have h0 : slot0 y = 0 := Feec.Models.Cube.MirrorBGG.mem_tsdQ_zero.1 (hy 0)
  rw [mirrorRe_apply, EState.σ_mk, h0, map_zero]

theorem neg_I_smul_mem_tsdQℝ {y : PiLp 2 SpaceQ} (hy : y ∈ tsdQℝ) : -Complex.I • y ∈ tsdQℝ :=
  fun i => (tsdQ i).smul_mem (-Complex.I) (hy i)

/-- **The Gauss residual of the real and imaginary parts is at most the TSD residual**:
`dist(Re z, mirrorGauss) ≤ dist(z, tsdQℝ)` and `dist(Re(-i z), mirrorGauss) ≤ dist(z, tsdQℝ)`. -/
theorem infDist_mirrorRe_le (z : PiLp 2 SpaceQ) :
    infDist (mirrorRe z) (mirrorGauss : Set REnergy) ≤ infDist z (tsdQℝ : Set (PiLp 2 SpaceQ)) ∧
    infDist (mirrorRe (-Complex.I • z)) (mirrorGauss : Set REnergy) ≤
      infDist z (tsdQℝ : Set (PiLp 2 SpaceQ)) := by
  constructor
  · refine (le_infDist ⟨0, tsdQℝ.zero_mem⟩).2 fun w hw => ?_
    refine (infDist_le_dist_of_mem (mirrorRe_mem_mirrorGauss hw)).trans ?_
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact norm_mirrorRe_le _
  · refine (le_infDist ⟨0, tsdQℝ.zero_mem⟩).2 fun w hw => ?_
    refine (infDist_le_dist_of_mem (mirrorRe_mem_mirrorGauss (neg_I_smul_mem_tsdQℝ hw))).trans ?_
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← smul_sub]
    refine (norm_mirrorRe_le _).trans ?_
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]

/-! #### The read discrete Gauss constraint is not asymptotically inside TSD -/

/-- A multiplier state `(0, 0, M, 0)`, read as a mirror state, is at distance `‖M‖` from the TSD
constraint (which forces `M = 0`). -/
theorem infDist_mirrorReEmb_M (m : W2) :
    infDist (mirrorReEmb (EState.mk 0 0 m 0)) (tsdQℝ : Set (PiLp 2 SpaceQ)) = ‖m‖ := by
  set a : REnergy := EState.mk 0 0 m 0
  have ha : ‖mirrorReEmb a‖ = ‖m‖ := by
    rw [norm_mirrorReEmb, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EState.norm_sq]
    simp [a]
  have hM : ‖embM m‖ = ‖m‖ := by
    rw [← ha, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_spaceQ (mirrorReEmb a),
      slot0_mirrorReEmb, slot1_mirrorReEmb, slotM_mirrorReEmb, slotB_mirrorReEmb]
    simp [a]
  refine le_antisymm ?_ ((le_infDist ⟨0, tsdQℝ.zero_mem⟩).2 fun w hw => ?_)
  · have := infDist_le_dist_of_mem (x := mirrorReEmb a) (tsdQℝ.zero_mem)
    rwa [dist_zero_right, ha] at this
  · have hw2 : slotM w = 0 := (Feec.Models.Cube.MirrorBGG.mem_tsdQ_two.1 (hw 2)).1
    have h := norm_sq_spaceQ (mirrorReEmb a - w)
    have hs : slotM (mirrorReEmb a - w) = embM m := by
      rw [map_sub, slotM_mirrorReEmb, hw2, sub_zero]
      rfl
    rw [hs, hM] at h
    rw [dist_eq_norm]
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    nlinarith [sq_nonneg ‖slot0 (mirrorReEmb a - w)‖, sq_nonneg ‖slot1 (mirrorReEmb a - w)‖,
      sq_nonneg ‖slotB (mirrorReEmb a - w)‖]

/-- **The discrete multiplier states are discrete Gauss states read at distance `‖x‖` from TSD**:
for `M ∈ Vₕ²`, `x = (0, 0, M, 0) ∈ hiddenGauss` and `dist(ιₙ x, tsdQℝ) = ‖x‖`. -/
theorem multiplierState_mirror (N : ℕ) (M : (mirrorFEM hT hB N).W2h) :
    multiplierState (mirrorFEM hT hB N) M ∈ mirrorHiddenGauss hT hB N ∧
      infDist (mirrorEmb hT hB N (multiplierState (mirrorFEM hT hB N) M))
        (tsdQℝ : Set (PiLp 2 SpaceQ)) = ‖multiplierState (mirrorFEM hT hB N) M‖ :=
  ⟨multiplierState_mem _ _ _ M, (infDist_mirrorReEmb_M (M : W2)).trans
    (norm_multiplierState (mirrorFEM hT hB N) M).symm⟩

/-- A nonzero constant `2`-form on the cube. -/
theorem exists_W2_ne_zero : ∃ m : W2, m ≠ 0 :=
  ⟨Feec.Models.Cube.DeRhamIdent.constForm (Feec.Models.Cube.FEM.isOpen_cubeDomain 3).measurableSet
      (Feec.Models.Cube.FEM.isBounded_cubeDomain 3) (⟨{0, 1}, by decide⟩ : Feec.Domain.formIdx 3 2),
    Feec.Models.Cube.DeRhamIdent.constForm_ne_zero _ _
      (by rw [Feec.Models.Cube.FEM.cubeDomain_eq_Q]
          exact Feec.Models.Cube.DeRhamIdent.volume_Q_ne_zero) _⟩

/-- **Eventually `Vₕ² ≠ 0`** (the projections of a nonzero `2`-form converge to it). -/
theorem eventually_exists_W2h_ne_zero :
    ∀ᶠ N in atTop, ∃ M : (mirrorFEM hT hB N).W2h, M ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_W2_ne_zero
  have hm0 : 0 < ‖m‖ := norm_pos_iff.2 hm
  have ht : Tendsto (fun N => ‖m - (mirrorFEM hT hB N).P2 m‖) atTop (𝓝 0) :=
    hT.tendsto_norm_sub_proj 2 m
  filter_upwards [ht.eventually (gt_mem_nhds hm0)] with N hN
  refine ⟨⟨(mirrorFEM hT hB N).P2 m, (mirrorFEM hT hB N).P2_mem m⟩, fun h => ?_⟩
  have h' : (mirrorFEM hT hB N).P2 m = 0 := congrArg Subtype.val h
  rw [h', sub_zero] at hN
  exact lt_irrefl _ hN

/-- **The read discrete Gauss constraint does not converge to TSD**: eventually there are nonzero
discrete Gauss states `x` with `dist(ιₙ x, tsdQℝ) = ‖x‖` (the multiplier states). So
`infDist(ιₙ ·, tsdQℝ)` does not tend to `0` on bounded subsets of `hiddenGauss`, the reading of
`hiddenGauss` is not contained in `tsdQℝ`, and the residual-`0` clause of the complex-level theorem
(item 3 of `approxFEEC_ofComplexCrime`, which needs `ιₙ(Kₙ) ⊆ tsdQℝ`) does not apply to
`hiddenGauss`. The constraint that `hiddenGauss` approximates is `mirrorGauss` (weakly). -/
theorem eventually_exists_mirrorHiddenGauss_infDist_eq :
    ∀ᶠ N in atTop, ∃ x ∈ mirrorHiddenGauss hT hB N, x ≠ 0 ∧
      infDist (mirrorEmb hT hB N x) (tsdQℝ : Set (PiLp 2 SpaceQ)) = ‖x‖ :=
  (eventually_exists_W2h_ne_zero hT hB).mono fun N ⟨M, hM⟩ =>
    ⟨_, (multiplierState_mirror hT hB N M).1, multiplierState_ne_zero _ hM,
      (multiplierState_mirror hT hB N M).2⟩

/-- **The discrete Gauss constraint of the mirror scheme is eventually nonzero.** -/
theorem eventually_mirrorHiddenGauss_ne_bot : ∀ᶠ N in atTop, mirrorHiddenGauss hT hB N ≠ ⊥ :=
  (eventually_exists_W2h_ne_zero hT hB).mono fun N ⟨_, hM⟩ =>
    discreteGauss_ne_bot (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
      (mirrorWave_S0_surjective hT hB N) hM

/-- **The residual-`0` clause for the part of TSD captured by the discrete Gauss constraint**:
for every TSD datum and every family of discrete initial values of the mirror scheme read
convergent to it, the Gauss residuals `dist(Re ξₙ(t), mirrorGauss)` and
`dist(Re(-i ξₙ(t)), mirrorGauss)` of the real and imaginary parts of the discrete solutions tend
to `0` uniformly on `[0, T]` (they are bounded by the TSD residual, which tends to `0` by the
verdict of the crime front `ofComplexCrime (mirrorComplex)`). -/
theorem einsteinBianchi_mirrorFEM_gaussResidual {x : PiLp 2 SpaceQ} (hx : x ∈ tsdQℝ) (T : ℝ)
    (v : ∀ N, (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).X N)
    (hv : Tendsto (fun N => (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).incl N (v N)) atTop
      (𝓝 x)) :
    TendstoUniformlyOn (fun N t => infDist
        (mirrorRe ((ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N (v N) t))
        (mirrorGauss : Set REnergy)) (fun _ => 0) atTop (Icc 0 T) ∧
    TendstoUniformlyOn (fun N t => infDist
        (mirrorRe (-Complex.I • (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N (v N) t))
        (mirrorGauss : Set REnergy)) (fun _ => 0) atTop (Icc 0 T) := by
  have V := (approxFEEC_ofComplexCrime (mirrorComplex hT hB)).1
  have h := V.residual_tendsto (V.isReducing_iff.1 isReducing_tsdQℝ).1 hx
    ((mirrorEllCore_closure hT hB).ge hx) hv T
  exact ⟨tendstoUniformlyOn_zero_of_le h (fun _ _ => infDist_nonneg)
      (fun _ _ => (infDist_mirrorRe_le _).1),
    tendstoUniformlyOn_zero_of_le h (fun _ _ => infDist_nonneg)
      (fun _ _ => (infDist_mirrorRe_le _).2)⟩

end Mirror

/-! ### The thesis' boundary conditions -/

section Cube

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry Feec.Models.BoundedDomain Feec.EinsteinBianchi.MatrixModel
  Feec.EinsteinBianchi.BoundedConvergence Feec.EinsteinBianchi.BoundedFailure

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- **The continuous Gauss constraint of the thesis' data**, in the real energy space `CEnergy`:
`σ = 0` and `u ⊥ d̃φ` for every `(σ', φ) ∈ Γ` (`grad σ' = φ`). -/
abbrev cubeGauss : Submodule ℝ CEnergy :=
  gaussSub bggSegment (E0 := W0) (E2 := W2) (E3 := Wv W2) incl1

theorem inner_incl1 (a b : Wv U1) : ⟪incl1 a, incl1 b⟫ = ⟪a, b⟫ :=
  LinearIsometry.inner_map_map (⟨incl1, norm_incl1⟩ : Wv U1 →ₗᵢ[ℝ] Wv W1) a b

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- The discrete Gauss constraint of the thesis' scheme at level `N`. -/
abbrev cubeHiddenGauss (N : ℕ) : Submodule ℝ (cubeHidden hT hB N) :=
  discreteGauss (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
    (cubeWave_S0_surjective hT hB N)

/-- The bottom-row projections `Π̃¹` of the thesis' scheme converge strongly. -/
theorem tendsto_norm_sub_cubePt1 (v : Wv U1) :
    Tendsto (fun N => ‖v - (cubeFEM hT hB N).Pt1 v‖) atTop (𝓝 0) := by
  have h : ∀ a ∈ Finset.univ, Tendsto (fun N => ‖(v a : W1) - (hB.proj N).π 1 (v a)‖ ^ 2)
      atTop (𝓝 0) := fun a _ => by
    simpa using (hB.tendsto_norm_sub_proj 1 (v a : W1)).pow 2
  have hs := tendsto_finsetSum Finset.univ h
  rw [Finset.sum_const_zero] at hs
  have e : ∀ N, ‖v - (cubeFEM hT hB N).Pt1 v‖ =
      √(∑ a, ‖(v a : W1) - (hB.proj N).π 1 (v a)‖ ^ 2) := fun N => by
    rw [← Real.sqrt_sq (norm_nonneg (v - _)), PiLp.norm_sq_eq_of_L2]
    rfl
  have hl := (Real.continuous_sqrt.tendsto 0).comp hs
  rw [Real.sqrt_zero] at hl
  simp only [e]
  exact hl

theorem vecL_totalE_symm_cubeEmb (N : ℕ) (w : cubeHidden hT hB N) :
    vecL (totalE.symm (cubeEmb hT hB N w)) = cubeFE hT hB N w :=
  (congrArg vecL (totalE.symm_apply_apply _)).trans (vecL_vecInv _)

theorem standardCubeApprox_sol_eq (N : ℕ) (v : cubeHidden hT hB N) (t : ℝ) :
    (standardCubeApprox hT hB).sol N v t = cubeEmb hT hB N ((discreteGroup (cubeFEM hT hB N)
      (cubeWave_dt0_injective hT hB N) (cubeWave_S0_surjective hT hB N)).S t v) := rfl

/-- The forms state of a matrix-model state (the left inverse of `totalE ∘ vecInv`). -/
def cubeRead : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
    (W2B ℝ (cubeDomain 3))) →L[ℝ] CEnergy :=
  vecL ∘L totalE.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem cubeRead_cubeEmb (N : ℕ) (w : cubeHidden hT hB N) :
    cubeRead (cubeEmb hT hB N w) = cubeFE hT hB N w :=
  vecL_totalE_symm_cubeEmb hT hB N w

set_option maxHeartbeats 4000000 in
theorem standardCube_waveGroup_mem_cubeGauss {x : PiLp 2 (ShortHilbertComplex.W3
      (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))}
    {v : ∀ N, cubeHidden hT hB N} (hv : ∀ N, v N ∈ cubeHiddenGauss hT hB N)
    (hconv : Tendsto (fun N => cubeEmb hT hB N (v N)) atTop (𝓝 x)) {t : ℝ} (ht : 0 ≤ t) :
    cubeRead (matrixComplex.waveGroup.S t x) ∈ cubeGauss := by
  have hsol := ((approxFEEC_ofComplexCrime (standardCubeComplex hT hB)).1.converges
    ((standardCubeEllCore_closure hT hB).ge Submodule.mem_top) (v := v) hconv t).tendsto_at
    ⟨ht, le_rfl⟩
  rw [ApproxFEEC.S_eq_waveGroup _ ht] at hsol
  have hX : Tendsto (fun N => cubeEmb hT hB N ((discreteGroup (cubeFEM hT hB N)
      (cubeWave_dt0_injective hT hB N) (cubeWave_S0_surjective hT hB N)).S t (v N))) atTop
      (𝓝 (matrixComplex.waveGroup.S t x)) :=
    hsol.congr fun N => (standardCubeComplex_sol hT hB N (v N) t).trans
      (standardCubeApprox_sol_eq hT hB N (v N) t)
  have hb : ∀ᶠ N in atTop, ‖(discreteGroup (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N)).S t (v N)‖ ≤ ‖x‖ + 1 := by
    filter_upwards [hconv.norm.eventually (gt_mem_nhds (lt_add_one ‖x‖))] with N hN
    rw [norm_discreteGroup, ← norm_cubeEmb hT hB N]
    exact hN.le
  have hmem : ∀ N, (discreteGroup (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N)).S t (v N) ∈ cubeHiddenGauss hT hB N := fun N =>
    discreteGroup_mem _ _ _ (hv N) t
  exact mem_gaussSub_of_tendsto_comp incl1 atTop (cubeFEM hT hB)
    (cubeWave_dt0_injective hT hB) (cubeWave_S0_surjective hT hB) (cubeFEM_compatible hT hB)
    (fun φ _ => tendsto_norm_sub_cubePt1 hT hB (bggSegment.dt0 φ))
    ((D0.domain.subtype : U0 →ₗ[ℝ] W0)) inner_incl1
    (fun N => cubeFE hT hB N) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun N x => (norm_cubeFE hT hB N x).le) cubeRead
    (fun N => cubeEmb hT hB N) (cubeRead_cubeEmb hT hB) hmem hb hX

/-- `totalE ∘ vecInv` preserves the inner products. -/
theorem inner_totalE_vecInv (a b : CEnergy) :
    ⟪totalE (vecInv a), totalE (vecInv b)⟫ = ⟪a, b⟫ := by
  rw [LinearIsometryEquiv.inner_map_map]
  exact LinearIsometry.inner_map_map (⟨vecInv.toLinearMap, norm_vecInv⟩ :
    CEnergy →ₗᵢ[ℝ] WS) a b

set_option maxHeartbeats 4000000 in
/-- **The discrete solutions of the thesis' scheme from discrete Gauss data are read weakly into
the continuous Gauss constraint, uniformly in time**: for bounded `vₙ ∈ hiddenGauss` and every
`y ⊥ cubeGauss`, `⟪ιₙ e^{t Lₙ} vₙ, totalE (vecInv y)⟫ → 0` uniformly in `t ∈ ℝ`. -/
theorem tendstoUniformly_inner_cubeEmb_group {v : ∀ N, cubeHidden hT hB N}
    (hv : ∀ N, v N ∈ cubeHiddenGauss hT hB N) {c : ℝ} (hc : ∀ᶠ N in atTop, ‖v N‖ ≤ c)
    {y : CEnergy} (hy : y ∈ cubeGaussᗮ) :
    TendstoUniformly (fun N t => ⟪cubeEmb hT hB N ((discreteGroup (cubeFEM hT hB N)
      (cubeWave_dt0_injective hT hB N) (cubeWave_S0_surjective hT hB N)).S t (v N)),
        totalE (vecInv y)⟫) (fun _ => 0) atTop :=
  tendstoUniformly_inner_group_comp incl1 atTop (cubeFEM hT hB)
    (cubeWave_dt0_injective hT hB) (cubeWave_S0_surjective hT hB) (cubeFEM_compatible hT hB)
    (fun φ _ => tendsto_norm_sub_cubePt1 hT hB (bggSegment.dt0 φ))
    ((D0.domain.subtype : U0 →ₗ[ℝ] W0)) inner_incl1
    (fun N => cubeFE hT hB N) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun N x => (norm_cubeFE hT hB N x).le) (fun a => totalE (vecInv a)) inner_totalE_vecInv
    (fun N => cubeEmb hT hB N) (fun _ _ => rfl) hv hc hy

end Cube

end Feec.Instances.EinsteinBianchi.FEM
