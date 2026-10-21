module

public import Feec.Instances.EinsteinBianchiFEMGenerator
public import Feec.HilbertComplex.Approximation.ApproxOrthogonal
public import Feec.Instances.EinsteinBianchi

/-!
# The thesis' scheme (6.5) on the cube as an approximating FEEC discretization

The finite element scheme (6.5) of [QuennevilleBelair2015], §6.3, with the elements of Table 6.1
and the thesis' boundary conditions (`Feec.Models.Cube.WeakSymmetry.cubeWave`) is an
**approximating FEEC discretization** (`Feec.HilbertComplex.ApproxFEEC`) of the matrix model
`Feec.EinsteinBianchi.MatrixModel.matrixComplex` (the BGG complex (5.1) on `Q` with the thesis'
boundary conditions), with the TSD constraint
`Feec.Instances.EinsteinBianchi.thesisTSD = {0} × L²(TSD) × ({0} × L²(TSD))`:

* `Xₙ` = the hidden-constraint space of (6.5) (`HiddenState (cubeWave hT hB N)`), `Lₙ` = the
  generator of (6.5) without source (`waveGen`);
* `ιₙ` = `cubeEmb`: the discrete forms state `(σₕ, uₕ, Mₕ, ρₕ)` read in the forms model (energy
  vector `(−σ, u, M, ρ)` inverted, `vecInv`; `Γ̄ = L²Λ⁰` by
  `Feec.EinsteinBianchi.MatrixModel.Γbar_eq_top`) and transported to the matrix model
  (`totalE`); isometric, `πₙ = ιₙ*`.

The core `standardCubeCore` is `D(L²)` (dense) with the orbit comparison; its approximation
hypothesis is the model convergence theorem `Feec.Models.Cube.WeakSymmetry.cubeWave_converges`
(through `Feec.EinsteinBianchi.BoundedConvergence.exactOfStrong`). The constraint does not reduce
`L` (`Feec.Instances.EinsteinBianchi.not_isReducing_thesisTSD`), and by the converse part of the
approximating FEEC theorem the residuals of the discrete solutions from the TSD datum
`(0, 0, (0, β))` tend to a positive limit (`standardCube_residual_not_mem`).

**Faithfulness caveat.** The instance is faithful to `cubeWave` (the scheme (6.5) of
`Feec.Models.Cube.WeakSymmetry`, `S₀,ₕ = π¹S⁰` for the smoothed projections), not to the variant
with the canonical interpolant `Π`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 4.17, §6.3 ((6.5), Table 6.1)
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi.FEM

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

open Feec.HilbertComplex Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM
  Feec.EinsteinBianchi.MatrixModel Feec.EinsteinBianchi.BoundedFailure
  Feec.EinsteinBianchi.BoundedConvergence

/-- The real forms energy space `L²Λ⁰ × (L²Λ¹)³ × L²Λ² × (L²Λ²)³` of the cube. -/
abbrev CEnergy : Type := EState W0 (Wv W1) W2 (Wv W2)

/-- Shortcut instances (synthesis is expensive). -/
instance instIPS_W0c : InnerProductSpace ℝ W0 := inferInstance
instance instIPS_WvW1c : InnerProductSpace ℝ (Wv W1) := inferInstance
instance instIPS_CEnergy : InnerProductSpace ℝ CEnergy := inferInstance

/-! ### The forms model total space and energy vectors -/

/-- `Γ̄ = L²Λ⁰` as an isometric equivalence. -/
abbrev gammaTop : bggHilb.Γbar ≃ₗᵢ[ℝ] W0 :=
  LinearIsometryEquiv.ofTop (E := W0) bggHilb.Γbar Γbar_eq_top

/-- **The inverse of the energy vector** `vecL`: `(a, u, M, ρ) ↦ (-a, u, (M, ρ))`. -/
def vecInv : CEnergy →L[ℝ] WS :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (ShortHilbertComplex.W3 bggHilb.Γbar (Wv W1)
        (WithLp 2 (W2 × Wv W2)))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i => match i with
      | 0 => -(gammaTop.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          (show CEnergy →L[ℝ] W0 from
            (ContinuousLinearMap.fst ℝ W0 _) ∘L EState.mkL.symm.toContinuousLinearMap))
      | 1 => (show CEnergy →L[ℝ] Wv W1 from
          (ContinuousLinearMap.fst ℝ (Wv W1) _) ∘L (ContinuousLinearMap.snd ℝ W0 _) ∘L
            EState.mkL.symm.toContinuousLinearMap)
      | 2 => (WithLp.prodContinuousLinearEquiv 2 ℝ W2 (Wv W2)).symm.toContinuousLinearMap ∘L
          (ContinuousLinearMap.snd ℝ (Wv W1) _ ∘L (ContinuousLinearMap.snd ℝ W0 _) ∘L
            EState.mkL.symm.toContinuousLinearMap)

theorem comp0_vecInv (z : CEnergy) : comp0 (vecInv z) = -gammaTop.symm z.σ := rfl
theorem comp1_vecInv (z : CEnergy) : comp1 (vecInv z) = z.u := rfl
theorem compML_vecInv (z : CEnergy) : compML (vecInv z) = z.M := rfl
theorem compρL_vecInv (z : CEnergy) : compρL (vecInv z) = z.ρ := rfl

theorem vecL_apply (x : WS) :
    vecL x = EState.mk (-((comp0 x : bggHilb.Γbar) : W0)) (comp1 x) (compML x) (compρL x) := rfl

theorem vecL_vecInv (z : CEnergy) : vecL (vecInv z) = z := by
  refine EState.ext ?_ rfl rfl rfl
  change -((-gammaTop.symm z.σ : bggHilb.Γbar) : W0) = z.σ
  rw [Submodule.coe_neg, neg_neg]
  exact gammaTop.apply_symm_apply z.σ

theorem norm_sq_WS (x : WS) :
    ‖x‖ ^ 2 = ‖comp0 x‖ ^ 2 + ‖comp1 x‖ ^ 2 + ‖compML x‖ ^ 2 + ‖compρL x‖ ^ 2 := by
  have h1 : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ x
  have h2 : ‖comp2 x‖ ^ 2 = ‖compML x‖ ^ 2 + ‖compρL x‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 _
  have h3 : ∑ i, ‖x i‖ ^ 2 = ‖comp0 x‖ ^ 2 + ‖comp1 x‖ ^ 2 + ‖comp2 x‖ ^ 2 :=
    Fin.sum_univ_three (fun i => ‖x i‖ ^ 2)
  linarith

/-- The energy vector is isometric. -/
theorem norm_vecL (x : WS) : ‖vecL x‖ = ‖x‖ := by
  have h := EState.norm_sq (show CEnergy from vecL x)
  have q0 : ‖EState.σ (show CEnergy from vecL x)‖ ^ 2 = ‖comp0 x‖ ^ 2 :=
    congrArg (· ^ 2) (norm_neg ((comp0 x : bggHilb.Γbar) : W0))
  have q1 : ‖EState.u (show CEnergy from vecL x)‖ ^ 2 = ‖comp1 x‖ ^ 2 := rfl
  have q2 : ‖EState.M (show CEnergy from vecL x)‖ ^ 2 = ‖compML x‖ ^ 2 := rfl
  have q3 : ‖EState.ρ (show CEnergy from vecL x)‖ ^ 2 = ‖compρL x‖ ^ 2 := rfl
  have hx := norm_sq_WS x
  have hsq : ‖vecL x‖ ^ 2 = ‖x‖ ^ 2 := by linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

theorem norm_vecInv (z : CEnergy) : ‖vecInv z‖ = ‖z‖ :=
  (norm_vecL (vecInv z)).symm.trans (congrArg norm (vecL_vecInv z))

/-- `‖y - totalE (vecInv z)‖ = ‖vecL (totalE⁻¹ y) - z‖`. -/
theorem norm_sub_totalE_vecInv (y : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))) (z : CEnergy) :
    ‖y - totalE (vecInv z)‖ = ‖vecL (totalE.symm y) - z‖ := by
  have e1 : totalE.symm (y - totalE (vecInv z)) = totalE.symm y - vecInv z :=
    (LinearIsometryEquiv.map_sub _ _ _).trans
      (congrArg (totalE.symm y - ·) (totalE.symm_apply_apply _))
  have e2 : vecL (totalE.symm y - vecInv z) = vecL (totalE.symm y) - z :=
    (vecL.map_sub _ _).trans (congrArg (vecL (totalE.symm y) - ·) (vecL_vecInv z))
  exact ((totalE.symm.norm_map _).symm.trans (congrArg norm e1)).trans
    ((norm_vecL _).symm.trans (congrArg norm e2))

/-! ### The reading map -/

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- Shortcut instances for the finite element spaces (synthesis under binders is expensive). -/
instance instIPS_U0 : InnerProductSpace ℝ U0 := inferInstance
instance instIPS_U1 : InnerProductSpace ℝ U1 := inferInstance
instance instIPS_WvU0 : InnerProductSpace ℝ (Wv U0) := inferInstance
instance instIPS_WvU1 : InnerProductSpace ℝ (Wv U1) := inferInstance
instance instIPS_W2' : InnerProductSpace ℝ W2 := inferInstance
instance instIPS_WvW2' : InnerProductSpace ℝ (Wv W2) := inferInstance

/-- The hidden space of the thesis' scheme (6.5) at level `N`. -/
abbrev cubeHidden (N : ℕ) := HiddenState (cubeWave hT hB N)

/-- The discrete forms state as a continuous forms state (isometric). -/
def cubeFE (N : ℕ) : cubeHidden hT hB N →L[ℝ] CEnergy :=
  EState.mapL ((D0.domain.subtypeL) ∘L (cubeFEM hT hB N).V0h.subtypeL)
    (incl1CLM ∘L (cubeFEM hT hB N).Vt1h.subtypeL) (cubeFEM hT hB N).W2h.subtypeL
    (cubeFEM hT hB N).Wt2h.subtypeL ∘L HiddenState.subtypeL _

theorem norm_cubeFE0 (N : ℕ) (x : (cubeFEM hT hB N).V0h) :
    ‖((D0.domain.subtypeL) ∘L (cubeFEM hT hB N).V0h.subtypeL) x‖ = ‖x‖ := rfl

theorem norm_cubeFE1 (N : ℕ) (x : (cubeFEM hT hB N).Vt1h) :
    ‖(incl1CLM ∘L (cubeFEM hT hB N).Vt1h.subtypeL) x‖ = ‖x‖ := norm_incl1 (x : Wv U1)

theorem norm_cubeFE2 (N : ℕ) (x : (cubeFEM hT hB N).W2h) :
    ‖(cubeFEM hT hB N).W2h.subtypeL x‖ = ‖x‖ := rfl

theorem norm_cubeFE3 (N : ℕ) (x : (cubeFEM hT hB N).Wt2h) :
    ‖(cubeFEM hT hB N).Wt2h.subtypeL x‖ = ‖x‖ := rfl

set_option maxHeartbeats 4000000 in
theorem norm_cubeFE (N : ℕ) (v : cubeHidden hT hB N) : ‖cubeFE hT hB N v‖ = ‖v‖ :=
  (EState.norm_mapL (norm_cubeFE0 hT hB N) (norm_cubeFE1 hT hB N) (norm_cubeFE2 hT hB N)
    (norm_cubeFE3 hT hB N) v.toEState).trans (HiddenState.norm_toEState v)

/-- **The reading map of the thesis' scheme**: the discrete forms state read in the matrix model,
isometric. -/
def cubeEmb (N : ℕ) : cubeHidden hT hB N →L[ℝ] PiLp 2 (ShortHilbertComplex.W3
    (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))) :=
  totalE.toContinuousLinearEquiv.toContinuousLinearMap ∘L vecInv ∘L cubeFE hT hB N

theorem cubeEmb_apply (N : ℕ) (v : cubeHidden hT hB N) :
    cubeEmb hT hB N v = totalE (vecInv (cubeFE hT hB N v)) := rfl

theorem norm_cubeEmb (N : ℕ) (v : cubeHidden hT hB N) : ‖cubeEmb hT hB N v‖ = ‖v‖ :=
  ((totalE.norm_map _).trans (norm_vecInv _)).trans (norm_cubeFE hT hB N v)

theorem inner_cubeEmb (N : ℕ) (v w : cubeHidden hT hB N) :
    ⟪cubeEmb hT hB N v, cubeEmb hT hB N w⟫ = ⟪v, w⟫ :=
  LinearIsometry.inner_map_map (⟨(cubeEmb hT hB N).toLinearMap, norm_cubeEmb hT hB N⟩ :
    cubeHidden hT hB N →ₗᵢ[ℝ] PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
      (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))) v w

theorem inner_cubeEmb_adjoint (N : ℕ) (v : cubeHidden hT hB N)
    (y : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
      (W2B ℝ (cubeDomain 3)))) :
    ⟪cubeEmb hT hB N v, y⟫ = ⟪v, (cubeEmb hT hB N).adjoint y⟫ :=
  (ContinuousLinearMap.adjoint_inner_right (cubeEmb hT hB N) v y).symm

theorem adjoint_cubeEmb_apply (N : ℕ) (v : cubeHidden hT hB N) :
    (cubeEmb hT hB N).adjoint (cubeEmb hT hB N v) = v :=
  ext_inner_left ℝ fun w =>
    ((inner_cubeEmb_adjoint hT hB N w (cubeEmb hT hB N v)).symm).trans (inner_cubeEmb hT hB N w v)

theorem norm_cubeEmb_le (N : ℕ) : ‖cubeEmb hT hB N‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v =>
    (norm_cubeEmb hT hB N v).trans_le (one_mul _).ge

/-! ### The thesis' scheme as an approximating FEEC discretization -/

/-- **The thesis' scheme (6.5) on the cube as an approximating FEEC discretization** of the matrix
model with the TSD constraint `thesisTSD`: `X_N` = the hidden space, `L_N` = the generator of (6.5)
without source, `ι_N` = `cubeEmb`, `π_N = ι_N*`. -/
def standardCubeApprox : ApproxFEEC matrixComplex ℕ where
  K := thesisTSD
  isClosed_K := isClosed_thesisTSD
  l := atTop
  X N := cubeHidden hT hB N
  normedAddCommGroup _ := HiddenState.instNormedAddCommGroup _
  innerProductSpace _ := HiddenState.instInnerProductSpace _
  completeSpace _ := HiddenState.instCompleteSpace _
  normedSpaceReal _ := (HiddenState.instInnerProductSpace _).toNormedSpace
  isScalarTower _ := IsScalarTower.left _
  L N := waveGen (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
    (cubeWave_S0_surjective hT hB N)
  skew _ := waveGen_skew _ _ _
  incl := cubeEmb hT hB
  proj N := (cubeEmb hT hB N).adjoint
  proj_incl := adjoint_cubeEmb_apply hT hB
  bound := ⟨1, fun N => ⟨norm_cubeEmb_le hT hB N,
    (ContinuousLinearMap.adjoint.norm_map (cubeEmb hT hB N)).trans_le (norm_cubeEmb_le hT hB N)⟩⟩

theorem standardCubeApprox_K : (standardCubeApprox hT hB).K = thesisTSD := rfl

theorem standardCubeApprox_isOrthogonal : ApproxFEEC.IsOrthogonal (standardCubeApprox hT hB) where
  inner_incl N a b := inner_cubeEmb hT hB N a b
  inner_incl_left N a y := inner_cubeEmb_adjoint hT hB N a y

theorem cubeSource_zero (N : ℕ) (t : ℝ) : cubeSource hT hB N 0 t = 0 :=
  ext_inner_right ℝ fun v => (inner_cubeSource hT hB N 0 t v).trans
    ((inner_zero_left (incl1 (v : Wv U1))).trans (inner_zero_left v).symm)

/-- A solution of (6.5) with the (vanishing) projected source as a solution without source. -/
def cubeSourceFree (N : ℕ) {T : ℝ}
    (s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0)) :
    Feec.BGG.DiscreteSolution (cubeWave hT hB N) T 0 :=
  s.ofEqOn fun t _ => (cubeSource_zero hT hB N t).symm

/-- The discrete forms state of a solution of (6.5) read as a continuous forms state. -/
abbrev cState (N : ℕ) {T : ℝ} {g : ℝ → (cubeFEM hT hB N).Vt1h}
    (s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T g) (t : ℝ) : CEnergy :=
  EState.mk ((s.σ t : U0) : W0) (incl1 (s.u t : Wv U1)) (s.M t : W2) (s.ρ t : Wv W2)

theorem cState_eq_dvec (N : ℕ) {T : ℝ} {g : ℝ → (cubeFEM hT hB N).Vt1h}
    (s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T g) (t : ℝ) :
    cState hT hB N s t = dvec (cubeFEM hT hB N) s t := rfl

set_option maxHeartbeats 4000000 in
/-- **The discrete solution of `standardCubeApprox` is (6.5)**: from the initial state of a
solution `s` of (6.5) without source, `ιₙ e^{tLₙ} v` is the energy vector of `s` read in the
matrix model, on `[0, T]`. -/
theorem standardCube_sol_eq (N : ℕ) {T : ℝ} (hT0 : 0 ≤ T)
    (s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (standardCubeApprox hT hB).sol N (DiscreteSolution.hiddenInit hT0 s) t =
      totalE (vecInv (cState hT hB N s t)) :=
  congrArg (fun z => totalE (vecInv z)) (congrArg (EState.mapL ((D0.domain.subtypeL) ∘L
    (cubeFEM hT hB N).V0h.subtypeL) (incl1CLM ∘L (cubeFEM hT hB N).Vt1h.subtypeL)
    (cubeFEM hT hB N).W2h.subtypeL (cubeFEM hT hB N).Wt2h.subtypeL)
    (DiscreteSolution.eq_group (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N) hT0 s t ht))

set_option maxHeartbeats 4000000 in
/-- **The discrete solutions of `standardCubeApprox` are the scheme (6.5)**: every discrete
initial value is the initial state of a solution of (6.5) without source, whose energy vector,
read in the matrix model, is the discrete solution. -/
theorem standardCube_sol_eq_scheme (N : ℕ) {T : ℝ} (hT0 : 0 < T) (v : cubeHidden hT hB N) :
    ∃ s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T 0,
      DiscreteSolution.hiddenInit hT0.le s = v ∧
      ∀ t ∈ Icc 0 T,
        (standardCubeApprox hT hB).sol N v t = totalE (vecInv (cState hT hB N s t)) := by
  obtain ⟨s, hs, -⟩ := exists_discreteSolution_group (cubeWave_dt0_injective hT hB N)
    (cubeWave_S0_surjective hT hB N) hT0 v
  subst hs
  exact ⟨s, rfl, fun t ht => standardCube_sol_eq hT hB N hT0.le s ht⟩

end Feec.Instances.EinsteinBianchi.FEM
