module

public import Feec.Instances.EinsteinBianchiFEMCube

/-!
# The core of the thesis' scheme (6.5) on the cube

The core `standardCubeCore` of `standardCubeApprox` is `D(L²)` of the matrix model, with the
orbit comparison (`Feec.HilbertComplex.ApproxFEEC.orbitCore`); its approximation
hypothesis is the model convergence theorem `Feec.Models.Cube.WeakSymmetry.cubeWave_converges`,
applied to the classical solution `Feec.EinsteinBianchi.BoundedConvergence.exactOfStrong` of the
orbit read in the forms model (`standardCube_hconv`). The core is dense
(`dense_standardCubeCore`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.3 ((6.5), Table 6.1)
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

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- The matrix-model orbit read in the forms model is the forms-model orbit. -/
theorem totalE_symm_waveGroup (t : ℝ) (x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))) :
    totalE.symm (matrixComplex.waveGroup.S t x) = formsComplex.waveGroup.S t (totalE.symm x) := by
  have h := waveGroup_conj t (totalE.symm x)
  have h' : matrixComplex.waveGroup.S t x =
      totalE (formsComplex.waveGroup.S t (totalE.symm x)) :=
    (congrArg (matrixComplex.waveGroup.S t) (totalE.apply_symm_apply x).symm).trans h.symm
  exact (congrArg totalE.symm h').trans (totalE.symm_apply_apply _)

set_option maxHeartbeats 8000000 in
/-- **The model convergence of the thesis' scheme (6.5) for data of `D(L²)`**: for every `T > 0`
and `ε > 0`, for all large `N`, the scheme from the elliptic projection (6.4) of the exact initial
state (`Feec.Models.Cube.WeakSymmetry.cubeWave_converges` for the classical solution
`exactOfStrong` of the orbit) is within `ε` of `e^{tL} ξ₀` on `[0, T]`. -/
theorem standardCube_hconv : ∀ x ∈ matrixComplex.wave.domainSq, ∀ T : ℝ, 0 < T →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∃ v : (standardCubeApprox hT hB).X N,
      ∀ t ∈ Icc 0 T,
        ‖matrixComplex.waveGroup.S t x - (standardCubeApprox hT hB).sol N v t‖ ≤ ε := by
  intro x hx T hT0 ε hε
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
  have hrep : ∀ t ∈ Icc 0 T,
      IsMultRep ((exactOfStrong hVy hWy hXy).ℓ t) (aOf (Vy t)) (bOf (Vy t)) :=
    exactOfStrong_isMultRep hVy hWy hXy
  have hrep' : ∀ t ∈ Icc 0 T, IsMultRep ((exactOfStrong hVy hWy hXy).ℓ' t)
      (aOf (waveOf (Vy t))) (bOf (waveOf (Vy t))) := exactOfStrong_isMultRep' hVy hWy hXy
  have conv := cubeWave_converges hT hB hT0 (f := 0) continuousOn_const (exactOfStrong hVy hWy hXy)
    (a := fun t => aOf (Vy t)) (b := fun t => bOf (Vy t))
    (a' := fun t => aOf (waveOf (Vy t))) (b' := fun t => bOf (waveOf (Vy t)))
    (negComp0L.continuous.comp_continuousOn hWy.continuousOn)
    (comp1L.continuous.comp_continuousOn hVy.continuousOn)
    (negComp0L.continuous.comp_continuousOn hXy)
    (comp1L.continuous.comp_continuousOn hWy.continuousOn) hrep hrep' hε
  have huniq : EqOn Vy (fun t => formsComplex.waveGroup.S t (totalE.symm x)) (Icc 0 T) :=
    (constrainedFEEC_wellPosed (H := formsComplex) hy T).2.1 Vy hVy0 hVy
  filter_upwards [conv] with N hN
  obtain ⟨shy, -, hshy⟩ := hN
  refine ⟨DiscreteSolution.hiddenInit hT0.le (cubeSourceFree hT hB N shy), fun t ht => ?_⟩
  have e1 : (standardCubeApprox hT hB).sol N
      (DiscreteSolution.hiddenInit hT0.le (cubeSourceFree hT hB N shy)) t =
      totalE (vecInv (cState hT hB N (cubeSourceFree hT hB N shy) t)) :=
    standardCube_sol_eq hT hB N hT0.le _ ht
  have e2 : totalE.symm (matrixComplex.waveGroup.S t x) = Vy t :=
    (totalE_symm_waveGroup t x).trans (huniq ht).symm
  have e3 : vecL (Vy t) = (exactWave_toSolution (exactOfStrong hVy hWy hXy)).vec t :=
    (solutionOfStrong_vec_eq hVy ht).symm.trans (exactOfStrong_vec hVy hWy hXy ht).symm
  have e4 : cState hT hB N (cubeSourceFree hT hB N shy) t = dvec (cubeFEM hT hB N) shy t := rfl
  have e5 := norm_vec_sub_dvec (cubeFEM hT hB N) (exactOfStrong hVy hWy hXy) shy t
  calc ‖matrixComplex.waveGroup.S t x - (standardCubeApprox hT hB).sol N
        (DiscreteSolution.hiddenInit hT0.le (cubeSourceFree hT hB N shy)) t‖
      = ‖vecL (totalE.symm (matrixComplex.waveGroup.S t x)) -
          cState hT hB N (cubeSourceFree hT hB N shy) t‖ := by
        rw [e1]; exact norm_sub_totalE_vecInv _ _
    _ = ‖(exactWave_toSolution (exactOfStrong hVy hWy hXy)).vec t -
          dvec (cubeFEM hT hB N) shy t‖ := by rw [e2, e3, e4]
    _ ≤ ε := e5.trans_le (hshy t ht)

/-- **The core of the thesis' scheme**: `D(L²)` with the orbit comparison (zero consistency
defect); the approximation hypothesis is the model convergence `standardCube_hconv`. -/
def standardCubeCore : (standardCubeApprox hT hB).Core :=
  ApproxFEEC.orbitCore (standardCubeApprox_isOrthogonal hT hB) matrixComplex.wave.domainSq
    (standardCube_hconv hT hB)

theorem standardCubeCore_data : (standardCubeCore hT hB).Data = matrixComplex.wave.domainSq := rfl

/-- **The core is dense** (`D(L²)` is dense for the skew-adjoint `L`). -/
theorem dense_standardCubeCore : Dense ((standardCubeCore hT hB).Data : Set (PiLp 2
    (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
      (W2B ℝ (cubeDomain 3))))) :=
  matrixComplex.isSkewAdjoint_wave.dense_domainSq

theorem standardCubeCore_closure : (standardCubeCore hT hB).Data.topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    (dense_standardCubeCore hT hB).closure_eq]
  trivial

end Feec.Instances.EinsteinBianchi.FEM
