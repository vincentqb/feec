module

public import Feec.Instances.EinsteinBianchiFEMCubeCore
public import Feec.Instances.EinsteinBianchiFEMElliptic

/-!
# The thesis' scheme (6.5) on the cube: convergence from best approximation plus consistency

For the approximating FEEC discretization `standardCubeApprox` of the thesis' scheme (6.5) with
the thesis' boundary conditions (`Feec.Instances.EinsteinBianchiFEMCube`), this file builds the
**elliptic core** `standardCubeEllCore`: data `D(L²)` (dense), with the elliptic projection (6.4)
of the classical solution `Feec.EinsteinBianchi.BoundedConvergence.exactOfStrong` of the orbit as
comparison trajectory (`Feec.Instances.EinsteinBianchi.FEM.ellTraj`). Its consistency defect
`Πₕ' - Lₕ Πₕ` (not shown to be nonzero) is bounded by the projection errors of the state and of
its time derivative (`norm_ellDefect_le`). The two hypotheses of the core are discharged by the
Strang bound of (6.4) (`norm_sub_ellTraj_le`, with `Feec.BGG.Stability` of the cube data,
`bggStability_curlPotentialConst`) and by the convergence of the smoothed projections
(`eventually_cubeClose`), of the consistency constants (`eventually_cubeFEM_K0`,
`eventually_cubeFEM_K1`); the model convergence theorem `cubeWave_converges` is not used. The
comparison of a datum on `[0, T]` uses the orbit on the horizon `T + 1`.

`einsteinBianchi_standardCube_approxFEEC_elliptic` is the verdict on this core.

**Faithfulness caveat.** As for `standardCubeApprox`: faithful to `cubeWave` (`S₀,ₕ = π¹S⁰` with
the smoothed projections), not to the canonical-interpolant variant. That the defect is nonzero
for some datum is not formalized.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2 ((6.4)), §6.3 ((6.5), Table 6.1)
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  Thm 3.9, Thm 3.10 (elliptic analogue)
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
open Feec.BGG.Discrete (strangConst)

/-! ### The orbit of a datum of `D(L²)` as a classical solution of (6.2) -/

set_option maxHeartbeats 4000000 in
/-- **The orbit of a datum of `D(L²)`**, read in the forms model, is a strong solution whose `L`
is a strong solution and whose `L²` is continuous, on `[0, T]`. -/
theorem exists_cubeOrbit {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (T : ℝ) : ∃ V : ℝ → WS, Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 V ∧
      Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 (fun t => waveOf (V t)) ∧
      ContinuousOn (fun t => waveOf (waveOf (V t))) (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, totalE.symm (matrixComplex.waveGroup.S t x) = V t := by
  obtain ⟨hx1, hx2⟩ := LinearPMap.mem_domainSq.1 hx
  have hy : totalE.symm x ∈ formsShort.wave.domain := wave_intertwines_symm.mapsTo ⟨x, hx1⟩
  have hAy : formsShort.wave ⟨totalE.symm x, hy⟩ ∈ formsShort.wave.domain :=
    (congrArg (· ∈ formsComplex.wave.domain) (wave_intertwines_symm.comm ⟨x, hx1⟩)).mpr
      (wave_intertwines_symm.mapsTo ⟨_, hx2⟩)
  have hA := formsShort.isSkewAdjoint_wave
  obtain ⟨Vy, hd, hd', hVy0, hVy, hWy', hXy'⟩ := exists_orbit_sq hA hy hAy (Icc 0 T)
  have hWy : Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 fun t => waveOf (Vy t) :=
    hWy'.congr (fun t _ => (waveOf_eq (hd t)).symm) fun _ _ => rfl
  have hXy : ContinuousOn (fun t => waveOf (waveOf (Vy t))) (Icc 0 T) := by
    refine hXy'.continuousOn.congr fun t _ => ?_
    change waveOf (waveOf (Vy t)) = formsShort.wave ⟨formsShort.wave ⟨Vy t, hd t⟩, hd' t⟩
    rw [waveOf_eq (hd t), waveOf_eq (hd' t)]
  have huniq : EqOn Vy (fun t => formsComplex.waveGroup.S t (totalE.symm x)) (Icc 0 T) :=
    (constrainedFEEC_wellPosed (H := formsComplex) hy T).2.1 Vy hVy0 hVy
  exact ⟨Vy, hVy, hWy, hXy, fun t ht => (totalE_symm_waveGroup t x).trans (huniq ht).symm⟩

/-- The orbit of `x ∈ D(L²)` in the forms model on `[0, T]`. -/
def cubeOrbit {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (T : ℝ) : ℝ → WS :=
  (exists_cubeOrbit hx T).choose

theorem cubeOrbit_spec {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (T : ℝ) :
    Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 (cubeOrbit hx T) ∧
      Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0
        (fun t => waveOf (cubeOrbit hx T t)) ∧
      ContinuousOn (fun t => waveOf (waveOf (cubeOrbit hx T t))) (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, totalE.symm (matrixComplex.waveGroup.S t x) = cubeOrbit hx T t :=
  (exists_cubeOrbit hx T).choose_spec

/-- **The classical solution of (6.2) of a datum of `D(L²)`** (cube data, no source). -/
def cubeExact {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (T : ℝ) : Feec.BGG.ExactWave bggSegment T (srcFun 0) :=
  exactOfStrong (cubeOrbit_spec hx T).1 (cubeOrbit_spec hx T).2.1 (cubeOrbit_spec hx T).2.2.1

theorem srcFun_zero_apply (t : ℝ) (v : Wv U1) : srcFun 0 t v = 0 := by
  rw [srcFun_apply, Pi.zero_apply, inner_zero_left]

theorem hg_cube (T : ℝ) : ∀ t ∈ Ico 0 T, ∀ v, srcFun 0 t v = 0 :=
  fun t _ v => srcFun_zero_apply t v

/-! ### The elliptic trajectory -/

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- The elliptic projection (6.4) at level `N` of the classical solution of `x` (horizon `T + 1`),
as a hidden state. -/
abbrev cEll (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (T t : ℝ) : cubeHidden hT hB N :=
  ellTraj (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N) (cubeWave_S0_surjective hT hB N)
    (cubeExact hx (T + 1)) t

/-- Its time derivative. -/
abbrev cEll' (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (T t : ℝ) : cubeHidden hT hB N :=
  ellTraj' (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N) (cubeWave_S0_surjective hT hB N)
    (cubeExact hx (T + 1)) t

/-- The projection error of the state. -/
abbrev cErr (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (T t : ℝ) : ℝ :=
  ‖exState (cubeExact hx (T + 1)) t - coeH (cubeFEM hT hB N) (cEll hT hB N hx T t).toEState‖

/-- The projection error of the time derivative. -/
abbrev cErr' (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (T t : ℝ) : ℝ :=
  ‖exState' (cubeExact hx (T + 1)) t - coeH (cubeFEM hT hB N) (cEll' hT hB N hx T t).toEState‖

set_option maxHeartbeats 1000000 in
/-- **The consistency defect** of the elliptic trajectory is bounded by the projection errors. -/
theorem norm_cEll_defect_le (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    {T t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖cEll' hT hB N hx T t - waveGen (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N) (cEll hT hB N hx T t)‖ ≤
      cErr' hT hB N hx T t + cErr hT hB N hx T t := by
  with_reducible_and_instances exact (norm_ellDefect_le (cubeFEM hT hB N)
    (cubeWave_dt0_injective hT hB N) (cubeWave_S0_surjective hT hB N) (cubeExact hx (T + 1))
    (hg_cube (T + 1)) (Icc_sub_Ico_add_one ht))

set_option maxHeartbeats 1000000 in
/-- The energy error of a hidden state against a classical solution, through the reading map of
the cube. -/
theorem norm_vec_sub_cubeFE (N : ℕ) {T : ℝ} (s : Feec.BGG.ExactWave bggSegment T (srcFun 0))
    (t : ℝ) (v : cubeHidden hT hB N) :
    ‖(exactWave_toSolution s).vec t - cubeFE hT hB N v‖ =
      ‖exState s t - coeH (cubeFEM hT hB N) v.toEState‖ := by
  have hL := EState.norm_sq (show CEnergy from (exactWave_toSolution s).vec t - cubeFE hT hB N v)
  have hR := norm_exState_sub_coeH_sq (cubeFEM hT hB N) s t v.toEState
  have e1 : ‖EState.σ (show CEnergy from (exactWave_toSolution s).vec t - cubeFE hT hB N v)‖ =
      ‖s.σ t - (v.toEState.σ : U0)‖ := by
    change ‖((s.σ t : U0) : W0) - (((v.toEState.σ : U0)) : W0)‖ = _
    rw [← Submodule.coe_sub]
    rfl
  have e2 : ‖EState.u (show CEnergy from (exactWave_toSolution s).vec t - cubeFE hT hB N v)‖ =
      ‖s.u t - (v.toEState.u : Wv U1)‖ := by
    change ‖incl1 (s.u t) - incl1 (v.toEState.u : Wv U1)‖ = _
    rw [← map_sub, norm_incl1]
  have e3 : ‖EState.M (show CEnergy from (exactWave_toSolution s).vec t - cubeFE hT hB N v)‖ =
      ‖s.M t - (v.toEState.M : W2)‖ := rfl
  have e4 : ‖EState.ρ (show CEnergy from (exactWave_toSolution s).vec t - cubeFE hT hB N v)‖ =
      ‖s.ρ t - (v.toEState.ρ : Wv W2)‖ := rfl
  have hsq := hL.trans ((congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (congrArg (· ^ 2) e1) (congrArg (· ^ 2) e2)) (congrArg (· ^ 2) e3))
      (congrArg (· ^ 2) e4)).trans hR.symm)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

set_option maxHeartbeats 4000000 in
/-- **The approximation error of the elliptic trajectory** through the reading map is its
projection error. -/
theorem norm_sub_cubeEmb_cEll (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    {T t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖matrixComplex.waveGroup.S t x - cubeEmb hT hB N (cEll hT hB N hx T t)‖ =
      cErr hT hB N hx T t := by
  have ht' : t ∈ Icc 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
  obtain ⟨hV, hW, hX, hEq⟩ := cubeOrbit_spec hx (T + 1)
  have e2 := hEq t ht'
  have e3 : vecL (cubeOrbit hx (T + 1) t) = (exactWave_toSolution (cubeExact hx (T + 1))).vec t :=
    (solutionOfStrong_vec_eq hV ht').symm.trans (exactOfStrong_vec hV hW hX ht').symm
  have h1 := norm_sub_totalE_vecInv (matrixComplex.waveGroup.S t x)
    (cubeFE hT hB N (cEll hT hB N hx T t))
  have h4 := norm_vec_sub_cubeFE hT hB N (cubeExact hx (T + 1)) t (cEll hT hB N hx T t)
  refine ((congrArg (fun y => ‖matrixComplex.waveGroup.S t x - y‖)
    (cubeEmb_apply hT hB N (cEll hT hB N hx T t))).trans h1).trans ?_
  refine (congrArg (fun z => ‖vecL z - cubeFE hT hB N (cEll hT hB N hx T t)‖) e2).trans ?_
  refine (congrArg (fun z => ‖z - cubeFE hT hB N (cEll hT hB N hx T t)‖) e3).trans ?_
  with_reducible_and_instances exact h4

/-! ### The comparison -/

theorem continuousOn_cEll (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (T : ℝ) : ContinuousOn (cEll hT hB N hx T) (Icc 0 T) := by
  with_reducible_and_instances exact
    ((continuousOn_ellTraj (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N) (cubeExact hx (T + 1))).mono (Icc_subset_Icc_add_one T))

theorem continuousOn_cEll' (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (T : ℝ) : ContinuousOn (cEll' hT hB N hx T) (Icc 0 T) := by
  with_reducible_and_instances exact
    ((continuousOn_ellTraj' (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N) (cubeExact hx (T + 1))).mono (Icc_subset_Icc_add_one T))

theorem hasDerivWithinAt_cEll (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    {T t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (cEll hT hB N hx T) (cEll' hT hB N hx T t) (Ici t) t := by
  with_reducible_and_instances exact
    (hasDerivWithinAt_ellTraj (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N) (cubeExact hx (T + 1)) (Ico_sub_Ico_add_one ht))

open Classical in
/-- The elliptic comparison trajectory of a datum (zero off `D(L²)`). -/
def cubeEllP (T : ℝ) (x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))) (N : ℕ) (t : ℝ) :
    (standardCubeApprox hT hB).X N :=
  if hx : x ∈ matrixComplex.wave.domainSq then cEll hT hB N hx T t else 0

open Classical in
/-- Its time derivative. -/
def cubeEllP' (T : ℝ) (x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))) (N : ℕ) (t : ℝ) :
    (standardCubeApprox hT hB).X N :=
  if hx : x ∈ matrixComplex.wave.domainSq then cEll' hT hB N hx T t else 0

theorem cubeEllP_of_mem (T : ℝ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (N : ℕ) : cubeEllP hT hB T x N = cEll hT hB N hx T :=
  funext fun _ => dite_eq_left hx

theorem cubeEllP'_of_mem (T : ℝ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (N : ℕ) : cubeEllP' hT hB T x N = cEll' hT hB N hx T :=
  funext fun _ => dite_eq_left hx

set_option maxHeartbeats 1000000 in
/-- **The elliptic comparison** of the thesis' scheme on `[0, T]`. -/
def cubeEllCmp (T : ℝ) : (standardCubeApprox hT hB).Comparison T where
  Data := matrixComplex.wave.domainSq
  p := cubeEllP hT hB T
  p' := cubeEllP' hT hB T
  continuousOn x hx N := by
    rw [cubeEllP_of_mem hT hB T hx]; exact continuousOn_cEll hT hB N hx T
  continuousOn' x hx N := by
    rw [cubeEllP'_of_mem hT hB T hx]; exact continuousOn_cEll' hT hB N hx T
  hasDerivWithinAt x hx N t ht := by
    rw [cubeEllP_of_mem hT hB T hx, cubeEllP'_of_mem hT hB T hx]
    exact hasDerivWithinAt_cEll hT hB N hx ht

set_option maxHeartbeats 1000000 in
theorem norm_cubeEllCmp_defect_le (T : ℝ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ
    (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))}
    (hx : x ∈ matrixComplex.wave.domainSq) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(cubeEllCmp hT hB T).defect x N t‖ ≤ cErr' hT hB N hx T t + cErr hT hB N hx T t := by
  have e : (cubeEllCmp hT hB T).defect x N t = cubeEllP' hT hB T x N t -
      (standardCubeApprox hT hB).L N (cubeEllP hT hB T x N t) := rfl
  rw [e, cubeEllP_of_mem hT hB T hx, cubeEllP'_of_mem hT hB T hx]
  exact norm_cEll_defect_le hT hB N hx ht

set_option maxHeartbeats 1000000 in
theorem norm_sub_cubeEllCmp_le (T : ℝ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ
    (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))}
    (hx : x ∈ matrixComplex.wave.domainSq) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖matrixComplex.waveGroup.S t x - (standardCubeApprox hT hB).incl N
      ((cubeEllCmp hT hB T).p x N t)‖ ≤ cErr hT hB N hx T t := by
  have e : (cubeEllCmp hT hB T).p x N t = cubeEllP hT hB T x N t := rfl
  rw [e, cubeEllP_of_mem hT hB T hx]
  exact (norm_sub_cubeEmb_cEll hT hB N hx ht).le

/-! ### Smallness of the projection errors -/

/-- The Strang constant `√(2 (C_p + 1))` of the cube data. -/
abbrev cubeStrangK : ℝ := √(2 * (strangConst (2 * Real.pi)⁻¹ + 1))

set_option maxHeartbeats 4000000 in
/-- **The projection errors tend to `0` uniformly on `[0, T]`** (the smoothed projections converge
on the compact trajectories, `eventually_cubeClose`; `K₀ → 0` on the represented multipliers,
`eventually_cubeFEM_K0`; `K₁ → 0`, `eventually_cubeFEM_K1`). -/
theorem eventually_cErr_le {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T, cErr hT hB N hx T t ≤ ε ∧ cErr' hT hB N hx T t ≤ ε := by
  set s := cubeExact hx (T + 1)
  obtain ⟨hV, hW, hX, -⟩ := cubeOrbit_spec hx (T + 1)
  have hmc := cubeCloseConst_nonneg C
  have hK : 0 ≤ cubeStrangK := Real.sqrt_nonneg _
  set θ := ε / (cubeStrangK * √(cubeCloseConst C + 2) + 1) with hθ
  have hden : 0 < cubeStrangK * √(cubeCloseConst C + 2) + 1 := by positivity
  have hθ0 : 0 < θ := div_pos hε hden
  have hθε : cubeStrangK * (√(cubeCloseConst C + 2) * θ) ≤ ε := by
    have e : θ * (cubeStrangK * √(cubeCloseConst C + 2) + 1) = ε := div_mul_cancel₀ _ hden.ne'
    nlinarith [Real.sqrt_nonneg (cubeCloseConst C + 2)]
  have hKc : IsCompact ((s.M '' Icc 0 (T + 1)) ∪ (s.M' '' Icc 0 (T + 1))) :=
    (isCompact_Icc.image_of_continuousOn s.cM).union (isCompact_Icc.image_of_continuousOn s.cM')
  have ev0 := eventually_cubeFEM_K0 hT hB (ℓ := s.ℓ)
    (a := fun t => aOf (cubeOrbit hx (T + 1) t)) (b := fun t => bOf (cubeOrbit hx (T + 1) t))
    (negComp0L.continuous.comp_continuousOn hW.continuousOn)
    (comp1L.continuous.comp_continuousOn hV.continuousOn)
    (exactOfStrong_isMultRep hV hW hX) hθ0
  have ev0' := eventually_cubeFEM_K0 hT hB (ℓ := s.ℓ')
    (a := fun t => aOf (waveOf (cubeOrbit hx (T + 1) t)))
    (b := fun t => bOf (waveOf (cubeOrbit hx (T + 1) t)))
    (negComp0L.continuous.comp_continuousOn hX)
    (comp1L.continuous.comp_continuousOn hW.continuousOn)
    (exactOfStrong_isMultRep' hV hW hX) hθ0
  have ev2 := eventually_cubeFEM_K1 hT hB hKc hθ0
  have ev3 := eventually_cubeClose hT hB (σ := s.σ) (φ := s.φ) (u := s.u) (M := s.M)
    (ρ := s.ρ) s.cσ s.cdφ s.cu s.cdu s.cM s.cρ s.cSu hθ0
  have ev4 := eventually_cubeClose hT hB (σ := s.σ') (φ := s.φ') (u := s.u') (M := s.M')
    (ρ := s.ρ') s.cσ' s.cdφ' s.cu' s.cdu' s.cM' s.cρ' s.cSu' hθ0
  filter_upwards [ev0, ev0', ev2, ev3, ev4] with N h0 h0' h2 h3 h4 t ht
  have ht' : t ∈ Icc 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
  have hdat : ∀ y : ℝ, y ≤ cubeCloseConst C * θ ^ 2 + θ ^ 2 + θ ^ 2 →
      y ≤ (√(cubeCloseConst C + 2) * θ) ^ 2 := fun y hy => by
    rw [mul_pow, Real.sq_sqrt (by linarith)]; nlinarith
  have hb : √(2 * (strangConst (2 * Real.pi)⁻¹ + 1)) * |√(cubeCloseConst C + 2) * θ| ≤ ε := by
    rw [abs_of_nonneg (by positivity)]; exact hθε
  have HS := bggStability_curlPotentialConst.toHarmonicStability
  refine ⟨?_, ?_⟩
  · have h := norm_sub_ellTraj_le (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N) HS (cubeFEM_compatible hT hB N) s (hg_cube (T + 1))
      (Icc_sub_Ico_add_one ht) (h0 t ht')
      (fun v hv => h2 (s.M t) (Or.inl (mem_image_of_mem _ ht')) v hv)
      (hdat _ (cubeFEM_strangData_le_of_close hT hB N (h3 t ht') θ θ))
    with_reducible_and_instances exact h.trans hb
  · have h := norm_sub_ellTraj'_le (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N) HS (cubeFEM_compatible hT hB N) s (hg_cube (T + 1))
      (Icc_sub_Ico_add_one ht) (h0' t ht')
      (fun v hv => h2 (s.M' t) (Or.inr (mem_image_of_mem _ ht')) v hv)
      (hdat _ (cubeFEM_strangData_le_of_close hT hB N (h4 t ht') θ θ))
    with_reducible_and_instances exact h.trans hb

/-! ### The elliptic core -/

set_option maxHeartbeats 4000000 in
/-- **The elliptic core of the thesis' scheme**: `D(L²)` with the elliptic projection (6.4) of the
classical solution of the orbit as comparison trajectory (bounded consistency defect);
no convergence theorem of the scheme is used. -/
def standardCubeEllCore : (standardCubeApprox hT hB).Core where
  Data := matrixComplex.wave.domainSq
  cmp T := cubeEllCmp hT hB T
  data_eq _ := rfl
  tendsto_approx T x hx := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [eventually_cErr_le hT hB hx T (half_pos hε)] with N h1 t ht
    rw [dist_eq_norm]
    have := norm_sub_cubeEllCmp_le hT hB T hx N ht
    linarith [(h1 t ht).1]
  tendsto_defect T x hx := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [eventually_cErr_le hT hB hx T (half_pos (half_pos hε))] with N h1 t ht
    rw [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have := norm_cubeEllCmp_defect_le hT hB T hx N ht
    linarith [(h1 t ht).1, (h1 t ht).2]

theorem standardCubeEllCore_data :
    (standardCubeEllCore hT hB).Data = matrixComplex.wave.domainSq := rfl

theorem dense_standardCubeEllCore : Dense ((standardCubeEllCore hT hB).Data : Set (PiLp 2
    (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
      (W2B ℝ (cubeDomain 3))))) :=
  matrixComplex.isSkewAdjoint_wave.dense_domainSq

/-- **The thesis' scheme (6.5) is an instance of the approximating FEEC theorem with the elliptic
core**: convergence from best approximation plus consistency, for every datum (the core is
dense). -/
theorem einsteinBianchi_standardCube_approxFEEC_elliptic :
    (standardCubeApprox hT hB).Verdict (standardCubeEllCore hT hB) :=
  approxFEEC _ _

end Feec.Instances.EinsteinBianchi.FEM
