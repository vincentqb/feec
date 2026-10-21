module

public import Feec.Instances.EinsteinBianchiFEMGenerator
public import Feec.HilbertComplex.BGG.Harmonic
public import Feec.Models.Cube.WeakSymmetryWave

/-!
# The elliptic projection (6.4) as a comparison trajectory of the generator of (6.3)

For the source-free scheme (6.3) of [QuennevilleBelair2015], §6.2, written as the skew generator
`Lₕ = waveGen` on the hidden space (`Feec.Instances.EinsteinBianchiFEMGenerator`), the dynamic
part `Πₕ(t)` of the elliptic projection (6.4) of an exact solution of (6.2) is a **comparison
trajectory with a consistency defect**, in the sense of the approximating FEEC theorem
(`Feec.HilbertComplex.ApproxFEEC.Comparison`):

* `Πₕ(t)` lies in the hidden space (`IsEllipticProjection.mem_hiddenSpace`; the data of (6.4)
  vanish on the tests `(0, ψ)` by the exact equation (6.2a));
* `⟪Lₕ Πₕ, y⟫ = ⟪Πₕ, y⟫ - G(y, Φ(y))` for hidden `y` (`IsEllipticProjection.inner_waveOp`; the
  mismatch `φₚ - Φ(σₚ, 0)` of the algebraic variable lies in `ker S₀,ₕ` and pairs to zero with
  hidden tests);
* with the exact equation, `⟪Πₕ' - Lₕ Πₕ, y⟫ = ⟪Πₕ' - ξ', y⟫ + ⟪ξ - Πₕ, y⟫`
  (`inner_ellDefect`), so the **consistency defect** is bounded by the projection errors of the
  exact state and of its time derivative (`norm_ellDefect_le`):
  `‖Πₕ' - Lₕ Πₕ‖ ≤ ‖ξ' - Πₕ'‖ + ‖ξ - Πₕ‖`;
* the projection errors obey the Strang bound of (6.4) modulo harmonic forms
  (`norm_sub_ellHidden_le`, from `Feec.BGG.HarmonicStability.strang_of_isEllipticProjection`).

The defect is not zero in general: `Lₕ` is built with `S₀,ₕ`, `S₁,ₕ`, the data of (6.4) with
`S₀`, `S₁` (the variational crime `S_h ≠ S`), and `Πₕ` is not the orthogonal projection.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2 ((6.3), (6.4), Prop 6.2)
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  Thm 3.9, Thm 3.10 (elliptic analogue: best approximation plus consistency)
-/

open scoped RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi.FEM

open Feec.BGG Feec.BGG.Discrete

/-! ### Horizons -/

theorem Icc_sub_Ico_add_one {T t : ℝ} (ht : t ∈ Icc 0 T) : t ∈ Ico 0 (T + 1) :=
  ⟨ht.1, by linarith [ht.2]⟩

theorem Ico_sub_Ico_add_one {T t : ℝ} (ht : t ∈ Ico 0 T) : t ∈ Ico 0 (T + 1) :=
  ⟨ht.1, by linarith [ht.2]⟩

theorem Icc_subset_Icc_add_one (T : ℝ) : Icc 0 T ⊆ Icc 0 (T + 1) :=
  Icc_subset_Icc le_rfl (by linarith)

/-! ### The elliptic projection of a discrete segment and the generator -/

section Segment

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}
  {G : Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0)} {x : ((P0 × Pt1 × P2 × Pt2) × Pt0) × P1}

/-- **The elliptic projection lies in the hidden space** when its data vanish on the tests
`(0, ψ)`, `ψ ∈ ker S₀,ₕ`. -/
theorem IsEllipticProjection.mem_hiddenSpace (hx : IsEllipticProjection D G 0 x)
    (hG : ∀ ψ, D.S0 ψ = 0 → G (0, ψ) = 0) : EState.mkL x.1.1 ∈ hiddenSpace D := by
  intro ψ hψ
  have e := hx.1 (0, ψ)
  rw [hG ψ hψ] at e
  simp only [energyInner, discreteSkewForm, Prod.fst_zero, Prod.snd_zero, inner_zero_right,
    map_zero, hψ, sub_zero] at e
  change ⟪x.1.1.2.1, D.dt0 ψ⟫ = 0
  linarith

variable [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P1] [FiniteDimensional ℝ P2]
  [FiniteDimensional ℝ Pt0] [FiniteDimensional ℝ Pt1] [FiniteDimensional ℝ Pt2]
  (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)

/-- **The generator against the elliptic projection**: for hidden `y`,
`⟪Lₕ Πₕ, y⟫ = ⟪Πₕ, y⟫ - G(y, Φ(y_σ, 0))`. The algebraic variable `φₚ` of the projection and
`Φ(σₚ, 0)` of the generator differ by an element of `ker S₀,ₕ`, which pairs to zero with the
hidden test. -/
theorem IsEllipticProjection.inner_waveOp (hx : IsEllipticProjection D G 0 x)
    (hmem : EState.mkL x.1.1 ∈ hiddenSpace D) {y : EState P0 Pt1 P2 Pt2}
    (hy : y ∈ hiddenSpace D) :
    ⟪waveOp D hdinj hS (EState.mkL x.1.1), y⟫ =
      ⟪EState.mkL x.1.1, y⟫ - G ((y.σ, y.u, y.M, y.ρ), phiMap D hdinj hS (y.σ, 0)) := by
  have e := hx.1 ((y.σ, y.u, y.M, y.ρ), phiMap D hdinj hS (y.σ, 0))
  rw [S0_phiMap hdinj hS, sub_self, inner_zero_right, sub_zero] at e
  have hW := FEM.inner_waveOp D hdinj hS hmem (y := y)
  have hq : D.S0 (x.1.2 - phiMap D hdinj hS (x.1.1.1, 0)) = 0 := by
    rw [map_sub, S0_phiMap hdinj hS]
    exact sub_eq_zero.2 (sub_eq_zero.1 hx.2).symm
  have h0 := hy _ hq
  rw [map_sub, inner_sub_right] at h0
  simp only [energyInner, discreteSkewForm] at e
  simp only [EState.mkL_apply, EState.σ_mk, EState.u_mk, EState.M_mk, EState.ρ_mk] at hW ⊢
  rw [hW, EState.inner_def]
  simp only [EState.σ_mk, EState.u_mk, EState.M_mk, EState.ρ_mk]
  have c1 := real_inner_comm (D.dt0 x.1.2) y.u
  have c2 := real_inner_comm (D.dt0 (phiMap D hdinj hS (x.1.1.1, 0))) y.u
  linarith

end Segment

/-! ### The elliptic projection of an exact solution -/

section Exact

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} (Q : Discrete D)

/-- The energy state of the continuous forms. -/
abbrev CState (V0 Vt1 W2 Wt2 : Type*) [NormedAddCommGroup V0] [NormedAddCommGroup Vt1]
    [NormedAddCommGroup W2] [NormedAddCommGroup Wt2] : Type _ := EState V0 Vt1 W2 Wt2

/-- The discrete energy states as continuous energy states (isometric). -/
def coeH : EState Q.V0h Q.Vt1h Q.W2h Q.Wt2h →L[ℝ] CState V0 Vt1 W2 Wt2 :=
  EState.mapL Q.V0h.subtypeL Q.Vt1h.subtypeL Q.W2h.subtypeL Q.Wt2h.subtypeL

theorem coeH_apply (a : EState Q.V0h Q.Vt1h Q.W2h Q.Wt2h) :
    coeH Q a = EState.mk (a.σ : V0) (a.u : Vt1) (a.M : W2) (a.ρ : Wt2) := rfl

@[simp] theorem coeH_σ (a : EState Q.V0h Q.Vt1h Q.W2h Q.Wt2h) : (coeH Q a).σ = (a.σ : V0) := rfl
@[simp] theorem coeH_u (a : EState Q.V0h Q.Vt1h Q.W2h Q.Wt2h) : (coeH Q a).u = (a.u : Vt1) := rfl
@[simp] theorem coeH_M (a : EState Q.V0h Q.Vt1h Q.W2h Q.Wt2h) : (coeH Q a).M = (a.M : W2) := rfl
@[simp] theorem coeH_ρ (a : EState Q.V0h Q.Vt1h Q.W2h Q.Wt2h) : (coeH Q a).ρ = (a.ρ : Wt2) := rfl

theorem inner_coeH (a b : EState Q.V0h Q.Vt1h Q.W2h Q.Wt2h) :
    ⟪coeH Q a, coeH Q b⟫ = ⟪a, b⟫ := by
  rw [EState.inner_def, EState.inner_def, coeH_apply, coeH_apply]
  simp only [EState.σ_mk, EState.u_mk, EState.M_mk, EState.ρ_mk, Submodule.coe_inner]

theorem norm_coeH (a : EState Q.V0h Q.Vt1h Q.W2h Q.Wt2h) : ‖coeH Q a‖ = ‖a‖ :=
  EState.norm_mapL (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) a

variable {T : ℝ} {g : ℝ → Vt1 →ₗ[ℝ] ℝ}

/-- The exact energy state `(σ, u, M, ρ)(t)`. -/
def exState (s : ExactWave D T g) (t : ℝ) : CState V0 Vt1 W2 Wt2 :=
  EState.mk (s.σ t) (s.u t) (s.M t) (s.ρ t)

/-- Its time derivative `(σ', u', M', ρ')(t)`. -/
def exState' (s : ExactWave D T g) (t : ℝ) : CState V0 Vt1 W2 Wt2 :=
  EState.mk (s.σ' t) (s.u' t) (s.M' t) (s.ρ' t)

@[simp] theorem exState_σ (s : ExactWave D T g) (t : ℝ) : (exState s t).σ = s.σ t := rfl
@[simp] theorem exState_u (s : ExactWave D T g) (t : ℝ) : (exState s t).u = s.u t := rfl
@[simp] theorem exState_M (s : ExactWave D T g) (t : ℝ) : (exState s t).M = s.M t := rfl
@[simp] theorem exState_ρ (s : ExactWave D T g) (t : ℝ) : (exState s t).ρ = s.ρ t := rfl
@[simp] theorem exState'_σ (s : ExactWave D T g) (t : ℝ) : (exState' s t).σ = s.σ' t := rfl
@[simp] theorem exState'_u (s : ExactWave D T g) (t : ℝ) : (exState' s t).u = s.u' t := rfl
@[simp] theorem exState'_M (s : ExactWave D T g) (t : ℝ) : (exState' s t).M = s.M' t := rfl
@[simp] theorem exState'_ρ (s : ExactWave D T g) (t : ℝ) : (exState' s t).ρ = s.ρ' t := rfl

/-- The error of a discrete energy state against the exact state, in components. -/
theorem norm_exState_sub_coeH_sq (s : ExactWave D T g) (t : ℝ)
    (p : EState Q.V0h Q.Vt1h Q.W2h Q.Wt2h) :
    ‖exState s t - coeH Q p‖ ^ 2 = ‖s.σ t - (p.σ : V0)‖ ^ 2 + ‖s.u t - (p.u : Vt1)‖ ^ 2 +
      ‖s.M t - (p.M : W2)‖ ^ 2 + ‖s.ρ t - (p.ρ : Wt2)‖ ^ 2 :=
  EState.norm_sq _

/-- The error of a discrete energy state against the time derivative, in components. -/
theorem norm_exState'_sub_coeH_sq (s : ExactWave D T g) (t : ℝ)
    (p : EState Q.V0h Q.Vt1h Q.W2h Q.Wt2h) :
    ‖exState' s t - coeH Q p‖ ^ 2 = ‖s.σ' t - (p.σ : V0)‖ ^ 2 + ‖s.u' t - (p.u : Vt1)‖ ^ 2 +
      ‖s.M' t - (p.M : W2)‖ ^ 2 + ‖s.ρ' t - (p.ρ : Wt2)‖ ^ 2 :=
  EState.norm_sq _

/-- The data of (6.4) of the exact state at time `t`. -/
abbrev ellData (s : ExactWave D T g) (t : ℝ) :
    Module.Dual ℝ ((Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h) :=
  Q.ellipticDataH (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) (s.ℓ t)

/-- The data of (6.4) of the time derivative. -/
abbrev ellData' (s : ExactWave D T g) (t : ℝ) :
    Module.Dual ℝ ((Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h) :=
  Q.ellipticDataH (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t) (s.ℓ' t)

/-- **The data of (6.4) along a source-free exact solution** are the energy pairing of
`ξ - ξ'` with the test: `G(t)(b, ψ) = ⟪ξ(t) - ξ'(t), b⟫` (the exact equations (6.2a)–(6.2d)). -/
theorem ellData_apply (s : ExactWave D T g) (hg : ∀ t ∈ Ico 0 T, ∀ v, g t v = 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) (b : Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) (ψ : Q.Vt0h) :
    ellData Q s t (b, ψ) = ⟪exState s t - exState' s t, coeH Q (EState.mkL b)⟫ := by
  have ha := s.ea t ht (b.1 : V0) (ψ : Vt0)
  have hb := s.eb t ht (b.2.1 : Vt1)
  have hc := s.ec t ht (b.2.2.1 : W2)
  have hd := s.ed t ht (b.2.2.2 : Wt2)
  rw [hg t ht] at hb
  rw [EState.inner_def, coeH_apply]
  simp only [exState, exState', EState.σ_sub, EState.u_sub, EState.M_sub, EState.ρ_sub,
    EState.σ_mk, EState.u_mk, EState.M_mk, EState.ρ_mk, EState.mkL_apply, inner_sub_left]
  change shiftedFormC D (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) (b.1 : V0) (ψ : Vt0)
    (b.2.1 : Vt1) (b.2.2.1 : W2) (b.2.2.2 : Wt2) - s.ℓ t (D.d0 (b.1 : V0) - D.S0 (ψ : Vt0)) = _
  simp only [shiftedFormC]
  linarith

/-- The data of (6.4) vanish on the tests `(0, ψ)` along the exact solution. -/
theorem ellData_zero (s : ExactWave D T g) (hg : ∀ t ∈ Ico 0 T, ∀ v, g t v = 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) (ψ : Q.Vt0h) : ellData Q s t (0, ψ) = 0 := by
  rw [ellData_apply Q s hg ht, map_zero, map_zero, inner_zero_right]

/-- So do the data of the time derivative (the derivative of a function vanishing on `[t, T)`). -/
theorem ellData'_zero (s : ExactWave D T g) (hg : ∀ t ∈ Ico 0 T, ∀ v, g t v = 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) (ψ : Q.Vt0h) : ellData' Q s t (0, ψ) = 0 := by
  have hT' : t ∈ Ico 0 ((t + T) / 2) := ⟨ht.1, by linarith [ht.2]⟩
  refine hasDerivWithinAt_Ici_eq_zero hT' (fun r hr => ellData_zero Q s hg
    ⟨hr.1, by linarith [hr.2, ht.2]⟩ ψ) (s.hasDerivWithinAt_ellipticDataH Q ht (0, ψ))

variable [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.V1h] [FiniteDimensional ℝ Q.W2h]
  [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h] [FiniteDimensional ℝ Q.Wt2h]
  (hdinj : Function.Injective Q.toSegmentH.dt0) (hS : Function.Surjective Q.toSegmentH.S0)

/-- The elliptic projection (6.4) of data `G`. -/
abbrev ellProj (G : Module.Dual ℝ ((Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h)) :
    ((Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h) × Q.V1h :=
  ellipticProjection Q.toSegmentH hdinj (exists_sub_eq_of_surjective hS) (ellipticRhs G 0)

/-- The orthogonal projection of energy states onto the hidden space. -/
def hiddenProjL : EState Q.V0h Q.Vt1h Q.W2h Q.Wt2h →L[ℝ] HiddenState Q.toSegmentH :=
  (hiddenSpace Q.toSegmentH).orthogonalProjectionOnto

/-- The read-out `x ↦ (hidden projection of) the energy state of x₁₁`. -/
def ellRead : (((Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h) × Q.V1h) →L[ℝ]
    HiddenState Q.toSegmentH :=
  hiddenProjL Q ∘L EState.mkL.toContinuousLinearMap ∘L
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))

/-- **The elliptic projection of data `G` as a hidden state.** -/
def ellHidden (G : Module.Dual ℝ ((Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h)) :
    HiddenState Q.toSegmentH :=
  ellRead Q (ellProj Q hdinj hS G)

/-- When the data vanish on `(0, ψ)`, the hidden state is the elliptic projection itself. -/
theorem toEState_ellHidden {G : Module.Dual ℝ ((Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h)}
    (hG : ∀ ψ, Q.toSegmentH.S0 ψ = 0 → G (0, ψ) = 0) :
    (ellHidden Q hdinj hS G).toEState = EState.mkL (ellProj Q hdinj hS G).1.1 := by
  have hx := isEllipticProjection_ellipticProjection hdinj (exists_sub_eq_of_surjective hS) G 0
  have hm := IsEllipticProjection.mem_hiddenSpace hx hG
  change (((hiddenSpace Q.toSegmentH).orthogonalProjectionOnto
    (EState.mkL (ellProj Q hdinj hS G).1.1) : hiddenSpace Q.toSegmentH) :
      EState Q.V0h Q.Vt1h Q.W2h Q.Wt2h) = _
  exact congrArg Subtype.val
    ((hiddenSpace Q.toSegmentH).orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, hm⟩)

/-- The elliptic hidden trajectory of an exact solution. -/
def ellTraj (s : ExactWave D T g) (t : ℝ) : HiddenState Q.toSegmentH :=
  ellHidden Q hdinj hS (ellData Q s t)

/-- Its time derivative. -/
def ellTraj' (s : ExactWave D T g) (t : ℝ) : HiddenState Q.toSegmentH :=
  ellHidden Q hdinj hS (ellData' Q s t)

theorem continuousOn_ellTraj (s : ExactWave D T g) :
    ContinuousOn (ellTraj Q hdinj hS s) (Icc 0 T) :=
  (ellRead Q).continuous.comp_continuousOn (continuousOn_ellipticProjection hdinj
    (exists_sub_eq_of_surjective hS) fun y => s.continuousOn_ellipticDataH Q y)

theorem continuousOn_ellTraj' (s : ExactWave D T g) :
    ContinuousOn (ellTraj' Q hdinj hS s) (Icc 0 T) :=
  (ellRead Q).continuous.comp_continuousOn (continuousOn_ellipticProjection hdinj
    (exists_sub_eq_of_surjective hS) fun y => s.continuousOn_ellipticDataH' Q y)

theorem hasDerivWithinAt_ellTraj (s : ExactWave D T g) {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (ellTraj Q hdinj hS s) (ellTraj' Q hdinj hS s t) (Ici t) t :=
  (ellRead Q).hasFDerivAt.comp_hasDerivWithinAt t (hasDerivWithinAt_ellipticProjection hdinj
    (exists_sub_eq_of_surjective hS) fun y => s.hasDerivWithinAt_ellipticDataH Q ht y)

theorem toEState_ellTraj (s : ExactWave D T g) (hg : ∀ t ∈ Ico 0 T, ∀ v, g t v = 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) : (ellTraj Q hdinj hS s t).toEState =
      EState.mkL (ellProj Q hdinj hS (ellData Q s t)).1.1 :=
  toEState_ellHidden Q hdinj hS fun ψ _ => ellData_zero Q s hg ht ψ

theorem toEState_ellTraj' (s : ExactWave D T g) (hg : ∀ t ∈ Ico 0 T, ∀ v, g t v = 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) : (ellTraj' Q hdinj hS s t).toEState =
      EState.mkL (ellProj Q hdinj hS (ellData' Q s t)).1.1 :=
  toEState_ellHidden Q hdinj hS fun ψ _ => ellData'_zero Q s hg ht ψ

omit [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.V1h] [FiniteDimensional ℝ Q.W2h]
  [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h] [FiniteDimensional ℝ Q.Wt2h] in
/-- Energy states read back from their components. -/
theorem mkL_tuple (y : EState Q.V0h Q.Vt1h Q.W2h Q.Wt2h) :
    EState.mkL (y.σ, y.u, y.M, y.ρ) = y := rfl

/-- **The consistency defect of the elliptic trajectory, weakly**: for hidden `y`,
`⟪Πₕ' - Lₕ Πₕ, y⟫ = ⟪Πₕ' - ξ', y⟫ + ⟪ξ - Πₕ, y⟫` (pairings in the continuous energy space). -/
theorem inner_ellDefect (s : ExactWave D T g) (hg : ∀ t ∈ Ico 0 T, ∀ v, g t v = 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) (y : HiddenState Q.toSegmentH) :
    ⟪ellTraj' Q hdinj hS s t - waveGen Q.toSegmentH hdinj hS (ellTraj Q hdinj hS s t), y⟫ =
      ⟪coeH Q (ellTraj' Q hdinj hS s t).toEState - exState' s t, coeH Q y.toEState⟫ +
        ⟪exState s t - coeH Q (ellTraj Q hdinj hS s t).toEState, coeH Q y.toEState⟫ := by
  have hx := isEllipticProjection_ellipticProjection hdinj (exists_sub_eq_of_surjective hS)
    (ellData Q s t) 0
  have hm := IsEllipticProjection.mem_hiddenSpace hx fun ψ _ => ellData_zero Q s hg ht ψ
  have hW := IsEllipticProjection.inner_waveOp hdinj hS hx hm y.toEState_mem
  have hE := ellData_apply Q s hg ht (y.toEState.σ, y.toEState.u, y.toEState.M, y.toEState.ρ)
    (phiMap Q.toSegmentH hdinj hS (y.toEState.σ, 0))
  rw [mkL_tuple] at hE
  rw [inner_sub_left, ← HiddenState.inner_toEState, ← HiddenState.inner_toEState,
    waveGen_toEState, toEState_ellTraj Q hdinj hS s hg ht]
  change ⟪(ellTraj' Q hdinj hS s t).toEState, y.toEState⟫ -
    ⟪waveOp Q.toSegmentH hdinj hS (EState.mkL (ellProj Q hdinj hS (ellData Q s t)).1.1),
      y.toEState⟫ = _
  rw [hW, hE, ← toEState_ellTraj Q hdinj hS s hg ht, inner_sub_left, inner_sub_left,
    inner_sub_left, inner_coeH, inner_coeH]
  ring

/-- **The consistency defect of the elliptic trajectory is bounded by the projection errors**:
`‖Πₕ' - Lₕ Πₕ‖ ≤ ‖ξ' - Πₕ'‖ + ‖ξ - Πₕ‖`. -/
theorem norm_ellDefect_le (s : ExactWave D T g) (hg : ∀ t ∈ Ico 0 T, ∀ v, g t v = 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    ‖ellTraj' Q hdinj hS s t - waveGen Q.toSegmentH hdinj hS (ellTraj Q hdinj hS s t)‖ ≤
      ‖exState' s t - coeH Q (ellTraj' Q hdinj hS s t).toEState‖ +
        ‖exState s t - coeH Q (ellTraj Q hdinj hS s t).toEState‖ := by
  set δ := ellTraj' Q hdinj hS s t - waveGen Q.toSegmentH hdinj hS (ellTraj Q hdinj hS s t)
  have h := inner_ellDefect Q hdinj hS s hg ht δ
  have hn : ‖coeH Q δ.toEState‖ = ‖δ‖ := (norm_coeH Q _).trans (HiddenState.norm_toEState δ)
  have h1 := real_inner_le_norm (coeH Q (ellTraj' Q hdinj hS s t).toEState - exState' s t)
    (coeH Q δ.toEState)
  have h2 := real_inner_le_norm (exState s t - coeH Q (ellTraj Q hdinj hS s t).toEState)
    (coeH Q δ.toEState)
  rw [hn, norm_sub_rev] at h1
  rw [hn] at h2
  rw [real_inner_self_eq_norm_sq] at h
  have hsq : ‖δ‖ ^ 2 ≤ (‖exState' s t - coeH Q (ellTraj' Q hdinj hS s t).toEState‖ +
      ‖exState s t - coeH Q (ellTraj Q hdinj hS s t).toEState‖) * ‖δ‖ := by
    rw [add_mul]; linarith
  rcases (norm_nonneg δ).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

omit [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.V1h] [FiniteDimensional ℝ Q.W2h]
  [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h] [FiniteDimensional ℝ Q.Wt2h] in
/-- The error of the hidden state against the exact state, in components. -/
theorem norm_sub_coeH_sq (a : CState V0 Vt1 W2 Wt2) (x : Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) :
    ‖a - coeH Q (EState.mkL x)‖ ^ 2 = ‖a.σ - x.1‖ ^ 2 + ‖a.u - x.2.1‖ ^ 2 +
      ‖a.M - x.2.2.1‖ ^ 2 + ‖a.ρ - x.2.2.2‖ ^ 2 := by
  rw [EState.norm_sq]; rfl

variable {Hh : Submodule ℝ Vt1} {Cp CS : ℝ} (HS : HarmonicStability D Hh Cp CS)
  (h54 : Q.Compatible)

include HS h54 in
/-- **The Strang bound for the elliptic trajectory**: if the exact state at `t` has Strang data
`≤ ε²` with consistency constants `K₀`, `K₁`, then `‖ξ(t) - Πₕ(t)‖ ≤ √(2(C + 1)) ε`. -/
theorem norm_sub_ellTraj_le (s : ExactWave D T g) (hg : ∀ t ∈ Ico 0 T, ∀ v, g t v = 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) {K0 K1 ε : ℝ}
    (hK0 : ∀ ψ ∈ Q.Vt0h, |s.ℓ t ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ v ∈ Q.Vt1h, |⟪s.M t, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hdata : Q.strangData (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) K0 K1 ≤ ε ^ 2) :
    ‖exState s t - coeH Q (ellTraj Q hdinj hS s t).toEState‖ ≤
      √(2 * (strangConst Cp + 1)) * |ε| := by
  have hx := isEllipticProjection_ellipticProjection hdinj (exists_sub_eq_of_surjective hS)
    (ellData Q s t) 0
  have hS' := (HS.strang_of_isEllipticProjection h54 (s.ee t (Ico_subset_Icc_self ht)) (s.ℓ t)
    hK0 hK1 hx).2
  have hC : 0 ≤ 2 * (strangConst Cp + 1) := by unfold strangConst; positivity
  rw [toEState_ellTraj Q hdinj hS s hg ht, ← Real.sqrt_sq (norm_nonneg _), norm_sub_coeH_sq,
    ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hC]
  exact Real.sqrt_le_sqrt (hS'.trans (mul_le_mul_of_nonneg_left hdata hC))

include HS h54 in
/-- **The Strang bound for the time derivative of the elliptic trajectory.** -/
theorem norm_sub_ellTraj'_le (s : ExactWave D T g) (hg : ∀ t ∈ Ico 0 T, ∀ v, g t v = 0)
    {t : ℝ} (ht : t ∈ Ico 0 T) {K0 K1 ε : ℝ}
    (hK0 : ∀ ψ ∈ Q.Vt0h, |s.ℓ' t ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ v ∈ Q.Vt1h, |⟪s.M' t, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hdata : Q.strangData (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t) K0 K1 ≤ ε ^ 2) :
    ‖exState' s t - coeH Q (ellTraj' Q hdinj hS s t).toEState‖ ≤
      √(2 * (strangConst Cp + 1)) * |ε| := by
  have hx := isEllipticProjection_ellipticProjection hdinj (exists_sub_eq_of_surjective hS)
    (ellData' Q s t) 0
  have hS' := (HS.strang_of_isEllipticProjection h54 (s.ee' t (Ico_subset_Icc_self ht))
    (s.ℓ' t) hK0 hK1 hx).2
  have hC : 0 ≤ 2 * (strangConst Cp + 1) := by unfold strangConst; positivity
  rw [toEState_ellTraj' Q hdinj hS s hg ht, ← Real.sqrt_sq (norm_nonneg _), norm_sub_coeH_sq,
    ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hC]
  exact Real.sqrt_le_sqrt (hS'.trans (mul_le_mul_of_nonneg_left hdata hC))

end Exact

end Feec.Instances.EinsteinBianchi.FEM
