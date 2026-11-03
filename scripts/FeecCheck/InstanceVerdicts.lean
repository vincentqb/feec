module

public import Feec.Instances.EinsteinBianchi
public import Feec.Instances.EinsteinBianchiAbsorbing
public import Feec.Instances.EinsteinBianchiFEM

/-!
# Regression tests: the instance verdicts of the Einstein–Bianchi rows

The verdicts `TorusVerdict`, `TorusSobolevVerdict`, `MirrorVerdict`, `MirrorSobolevVerdict`,
`MirrorFEMVerdict`, `StandardCubeVerdict` (`Feec.Instances.EinsteinBianchi`) and
`AbsorbingVerdict` (`Feec.Instances.EinsteinBianchiAbsorbing`) were `Prop` conjunctions. They are
now structures: the spectral rows extend the verdict of the constrained FEEC theorem
(`ConstrainedFEEC.Verdict` of `torusFEEC`, `mirrorFEEC`), each Sobolev verdict extends its row,
the absorbing verdict extends the verdict of the dissipative FEEC theorem
(`DissipFEEC.Verdict` of `absorbingGalerkin`), and the two finite element rows, which are not
instances of a layer theorem, have named fields. The theorems `ebVerdict_old_*` state the old
conjunctions verbatim and derive them from the new structures: the consequences of the reducing
constraint (propagation, residual bounds) are read off the parent verdict and `isReducing`, and
the summaries `einsteinBianchi_constrainedFEEC_summary`, `einsteinBianchi_summary` no longer list
`TorusVerdict`, `MirrorVerdict` next to the Sobolev verdicts that extend them.

This file is part of the `FeecCheck` library, not of `Feec`.
-/

public section

open scoped InnerProductSpace Topology
open Set Filter Metric

namespace FeecCheck.InstanceVerdicts

open Feec Feec.HilbertComplex Feec.Instances.EinsteinBianchi

section Torus

open Feec.Models.Torus.BGG

/-- The old `TorusVerdict`. -/
theorem ebVerdict_old_torusVerdict :
    complex.wave.IsReducing (totalSub constraint) ∧
    (∀ t, ∀ x ∈ totalSub constraint, complex.waveGroup.S t x ∈ totalSub constraint) ∧
    (∀ T : ℝ, ∀ x : complex.wave.domain, TendstoUniformlyOn
      (fun N t => complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex x) t))
      (fun t => complex.waveGroup.S t x) atTop (Icc 0 T)) ∧
    (∀ x : complex.wave.domain, (x : PiLp 2 Space) ∈ totalSub constraint → ∀ T : ℝ,
      (∀ N t, infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex x) t))
          (totalSub constraint : Set (PiLp 2 Space)) ≤
        ‖complex.waveGroup.S t x -
          complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex x) t)‖) ∧
      TendstoUniformlyOn
        (fun N t => infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex x) t))
          (totalSub constraint : Set (PiLp 2 Space))) (fun _ => 0) atTop (Icc 0 T)) ∧
    ∀ (α T : ℝ) (x : PiLp 2 Space) (hx : x ∈ bandFamily.rateData α) (N : ℕ), ∀ t ∈ Icc 0 T,
      ‖complex.waveGroup.S t x -
          complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex ⟨x, hx.1⟩) t)‖ ≤
        (1 + ellipticConst complex) * (1 + t) ^ 2 *
          (1 * (1 / ((N : ℝ) + 1)) ^ α * bandFamily.rateNorm α x) ∧
      (x ∈ totalSub constraint →
        infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex ⟨x, hx.1⟩) t))
            (totalSub constraint : Set (PiLp 2 Space)) ≤
          (1 + ellipticConst complex) * (1 + t) ^ 2 *
            (1 * (1 / ((N : ℝ) + 1)) ^ α * bandFamily.rateNorm α x))
 :=
  have V := einsteinBianchi_torus_constrainedFEEC
  ⟨V.isReducing, V.propagates_iff.1 V.isReducing, fun T x => V.converges x T,
    fun x hx T => ⟨V.residual_le V.isReducing x hx, V.residual_tendsto V.isReducing x hx T⟩,
    fun α T _ hx N _ ht => ⟨V.rate (torusRate α T) hx N ht,
      fun hxK => V.residual_rate V.isReducing (torusRate α T) hx hxK N ht⟩⟩

/-- The old `TorusSobolevVerdict`. -/
theorem ebVerdict_old_torusSobolevVerdict :
  ∀ (x : PiLp 2 Space), x ∈ totalSub constraint → ∀ {s : ℝ}, 0 ≤ s → MemSobStateT (2 + s) x →
    x ∈ complex.wave.domain ∧ ∀ (hx : x ∈ complex.wave.domain) (N : ℕ) {T t : ℝ}, t ∈ Icc 0 T →
      ‖complex.waveGroup.S t x -
          complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex ⟨x, hx⟩) t)‖ ≤
        (1 + ellipticConst complex) * (1 + t) ^ 2 *
          ((1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobStateT (2 + s) x))) ∧
      infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex ⟨x, hx⟩) t))
          (totalSub constraint : Set (PiLp 2 Space)) ≤
        (1 + ellipticConst complex) * (1 + t) ^ 2 *
          ((1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobStateT (2 + s) x)))
 :=
  have V := einsteinBianchi_torus_constrainedFEEC_sobolev
  fun _ hK _ hs h => ⟨V.mem_domain_sobolev hK hs h, fun hx N _ _ ht =>
    ⟨V.rate_sobolev hK hs h hx N ht, V.tsd_residual_rate_sobolev hK hs h hx N ht⟩⟩

end Torus

section Mirror

open Feec.Models.Cube.MirrorBGG

/-- The old `MirrorVerdict`. -/
theorem ebVerdict_old_mirrorVerdict :
    complexQ.wave.IsReducing (totalSub tsdQ) ∧
    (∀ t, ∀ x ∈ totalSub tsdQ, complexQ.waveGroup.S t x ∈ totalSub tsdQ) ∧
    (∀ T : ℝ, ∀ x : complexQ.wave.domain, TendstoUniformlyOn
      (fun N t => complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ x) t))
      (fun t => complexQ.waveGroup.S t x) atTop (Icc 0 T)) ∧
    (∀ x : complexQ.wave.domain, (x : PiLp 2 SpaceQ) ∈ totalSub tsdQ → ∀ T : ℝ,
      (∀ N t, infDist (complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ x) t))
          (totalSub tsdQ : Set (PiLp 2 SpaceQ)) ≤
        ‖complexQ.waveGroup.S t x -
          complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ x) t)‖) ∧
      TendstoUniformlyOn
        (fun N t => infDist
          (complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ x) t))
          (totalSub tsdQ : Set (PiLp 2 SpaceQ))) (fun _ => 0) atTop (Icc 0 T)) ∧
    ∀ (α T : ℝ) (x : PiLp 2 SpaceQ) (hx : x ∈ bandFamilyQ.rateData α) (N : ℕ), ∀ t ∈ Icc 0 T,
      ‖complexQ.waveGroup.S t x -
          complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ ⟨x, hx.1⟩) t)‖ ≤
        (1 + ellipticConst complexQ) * (1 + t) ^ 2 *
          (1 * (1 / ((N : ℝ) + 1)) ^ α * bandFamilyQ.rateNorm α x) ∧
      (x ∈ totalSub tsdQ →
        infDist (complexQ.totalD.graphFst
            (mirrorFEEC.discrete N (waveLift complexQ ⟨x, hx.1⟩) t))
            (totalSub tsdQ : Set (PiLp 2 SpaceQ)) ≤
          (1 + ellipticConst complexQ) * (1 + t) ^ 2 *
            (1 * (1 / ((N : ℝ) + 1)) ^ α * bandFamilyQ.rateNorm α x))
 :=
  have V := einsteinBianchi_mirror_constrainedFEEC
  ⟨V.isReducing, V.propagates_iff.1 V.isReducing, fun T x => V.converges x T,
    fun x hx T => ⟨V.residual_le V.isReducing x hx, V.residual_tendsto V.isReducing x hx T⟩,
    fun α T _ hx N _ ht => ⟨V.rate (mirrorRate α T) hx N ht,
      fun hxK => V.residual_rate V.isReducing (mirrorRate α T) hx hxK N ht⟩⟩

/-- The old `MirrorSobolevVerdict`. -/
theorem ebVerdict_old_mirrorSobolevVerdict :
  ∀ (D : Models.Cube.MirrorWeakSymmetry.TSDDatum) {s : ℝ}, 0 ≤ s →
    Models.Cube.MirrorWeakSymmetry.MemSobState (2 + s) D.U₀ → ∀ (N : ℕ) {T t : ℝ},
    t ∈ Icc 0 T →
    ‖complexQ.waveGroup.S t D.U₀ -
        complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ ⟨D.U₀, D.mem⟩) t)‖ ≤
      (1 + ellipticConst complexQ) * (1 + t) ^ 2 * ((1 / ((N : ℝ) + 1)) ^ s *
        (3 * √(Models.Cube.MirrorWeakSymmetry.sobState (2 + s) D.U₀))) ∧
    infDist (complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ ⟨D.U₀, D.mem⟩) t))
        (totalSub tsdQ : Set (PiLp 2 SpaceQ)) ≤
      (1 + ellipticConst complexQ) * (1 + t) ^ 2 * ((1 / ((N : ℝ) + 1)) ^ s *
        (3 * √(Models.Cube.MirrorWeakSymmetry.sobState (2 + s) D.U₀)))
 :=
  have V := einsteinBianchi_mirror_constrainedFEEC_sobolev
  fun D _ hs h N _ _ ht =>
    ⟨V.rate_sobolev D hs h N ht, V.tsd_residual_rate_sobolev D hs h N ht⟩

end Mirror

section MirrorFEM

open Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.FEM (ParitySmoothingEstimates)
open Feec.FiniteElement (PolySeq)

/-- The old `MirrorFEMVerdict`. -/
theorem ebVerdict_old_mirrorFEMVerdict :
  (∃ (ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3) (C : ℝ),
      ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C ∧
        ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) ∧
    ∀ {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
      (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
      (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C),
      MirrorWaveFEMConvergence hT hB ∧ MirrorWaveFEMRate hT hB ∧ MirrorWaveFEMRateSobolev hT hB
 :=
  have V := mirrorFEMVerdict
  ⟨V.exists_estimates, fun hT hB => ⟨V.converges hT hB, V.rate hT hB, V.rate_sobolev hT hB⟩⟩

end MirrorFEM

section StandardBoundary

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry
  Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM Feec.EinsteinBianchi.MatrixModel
  Feec.EinsteinBianchi.BoundedFailure Feec.EinsteinBianchi.BoundedConvergence

/-- The old `StandardCubeVerdict`. -/
theorem ebVerdict_old_standardCubeVerdict :
    (betaDatum ∈ thesisTSD ∧ ¬ matrixComplex.wave.IsReducing thesisTSD) ∧
    (∀ (K : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
        (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) [K.HasOrthogonalProjection],
      betaDatum ∈ K → (∀ x ∈ K, (x 1 : L2F ℝ (cubeDomain 3) Ix) ∈ tsd (cubeDomain 3)) →
        ¬ matrixComplex.wave.IsReducing K) ∧
    ((∃ (p : ℕ → SmoothingParam (Fin 3 → ℝ)) (C : ℝ),
        PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C ∧
          PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) ∧
      ∀ {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
        (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
        (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) {T : ℝ} (hT0 : 0 < T),
        StandardCubeFailure hT hB hT0)
 :=
  have V := standardCubeVerdict
  ⟨⟨V.betaDatum_mem, V.not_isReducing⟩, fun K _ h0 hE => V.not_isReducing_of_mem K h0 hE,
    V.exists_estimates, fun hT hB _ hT0 => V.failure hT hB hT0⟩

end StandardBoundary

section Absorbing

open MeasureTheory Feec.Domain Feec.Models.BoundedDomain Feec.Models.Cube.Absorbing
  Feec.Models.Cube.Geometry

/-- The old `AbsorbingVerdict`. -/
theorem ebVerdict_old_absorbingVerdict :
    -- 1. well-posedness and radiation
    (absorbing.IsMDissipative ∧
      (∀ E B : C1Field, E.tan + B.flux = 0 →
        ∃ h : (WithLp.toLp 2 (E.l2, B.l2) : State) ∈ absorbing.domain,
          absorbing ⟨_, h⟩ = WithLp.toLp 2 (-B.curlL2, E.curlL2) ∧
            impedanceTriple.trace ⟨_, h⟩ = E.tan) ∧
      (∀ (u₀ : absorbing.domain) (t : ℝ), 0 ≤ t →
        ‖absorbingSemigroup.S t u₀‖ ^ 2 = ‖(u₀ : State)‖ ^ 2 -
          2 * ∫ s in (0 : ℝ)..t, ‖impedanceTriple.traceExt (absorbingSemigroup.S s u₀)‖ ^ 2) ∧
      ∃ u : absorbing.domain, ⟪absorbing u, (u : State)⟫_ℝ < 0) ∧
    -- 2. the constraint: Gauss laws and TSD on the domain of dependence, TSD not invariant
    ((∀ u₀ ∈ tsdPair, ∀ t, 0 ≤ t → ∀ φ : Fin 3 → R3 → ℝ, IsTestField (Q (Fin 3)) φ →
        (∑ ij : Ix, ∫ x in Q (Fin 3), (absorbingSemigroup.S t u₀).fst ij x *
          partialDeriv ij.2 (φ ij.1) x = 0) ∧
        ∑ ij : Ix, ∫ x in Q (Fin 3), (absorbingSemigroup.S t u₀).snd ij x *
          partialDeriv ij.2 (φ ij.1) x = 0) ∧
      (∀ u₀ ∈ tsdPair, ∀ t, 0 ≤ t → ∀ᵐ y ∂volume.restrict (depDomain (Q (Fin 3)) t),
        SymTF (absorbingSemigroup.S t u₀).fst y ∧ SymTF (absorbingSemigroup.S t u₀).snd y) ∧
      ¬ ∀ t, 0 ≤ t → ∀ x ∈ tsdPair, absorbingSemigroup.S t x ∈ tsdPair) ∧
    -- 3. finite speed
    (∀ (T : ℝ) (u₀ : State) (W : ℝ → State), IsWeakRowEB T W → W 0 = u₀ → ∀ t ∈ Icc 0 T,
      ∀ j, ∀ᵐ y ∂volume.restrict (depDomain (Q (Fin 3)) t),
        toField (absorbingSemigroup.S t u₀) j y = toField (W t) j y) ∧
    -- 4. the semi-discrete scheme
    ((absorbingGalerkinCore.Data.topologicalClosure = ⊤ ∧
        absorbingGalerkin.Verdict absorbingGalerkinCore) ∧
      (∀ (n : ℕ) (x : absorbingGalerkin.X n) (t : ℝ), 0 ≤ t →
        ‖absorbingGalerkin.sol n x t‖ ^ 2 = ‖absorbingGalerkin.incl n x‖ ^ 2 -
          2 * ∫ s in (0 : ℝ)..t,
            ‖galerkinData.Γh n ((C0Group.ofBounded (galerkinData.Lh n)).S s x).fst‖ ^ 2) ∧
      ∀ T : ℝ, 0 < T → ∃ x ∈ tsdPair, ∃ t ∈ Icc 0 T, absorbingSemigroup.S t x ∉ tsdPair ∧
        0 < infDist (absorbingSemigroup.S t x) (tsdPair : Set State) ∧
        Tendsto (fun n => absorbingGalerkin.incl n (absorbingGalerkin.proj n x)) atTop (𝓝 x) ∧
        ∀ v : ∀ n, absorbingGalerkin.X n,
          Tendsto (fun n => absorbingGalerkin.incl n (v n)) atTop (𝓝 x) →
          Tendsto (fun n => infDist (absorbingGalerkin.sol n (v n) t) (tsdPair : Set State))
            atTop (𝓝 (infDist (absorbingSemigroup.S t x) (tsdPair : Set State))))
 :=
  have V := absorbingVerdict
  ⟨⟨V.isMDissipative, V.smooth_mem_domain, V.energy_flux, V.exists_inner_neg⟩,
    ⟨V.gauss, V.symTF_depDomain, V.not_invariant⟩, V.eq_depDomain,
    ⟨⟨V.dense_core, V.toVerdict⟩, V.discrete_energy_flux, V.residual_not_invariant⟩⟩

end Absorbing

section Summary

/-- The old `einsteinBianchi_constrainedFEEC_summary`, verbatim. -/
theorem ebVerdict_old_constrainedFEEC_summary :
    (TorusVerdict ∧ TorusSobolevVerdict ∧ TorusNonvacuous) ∧
    (MirrorVerdict ∧ MirrorSobolevVerdict ∧ MirrorNonvacuous) ∧
    MirrorFEMVerdict ∧ StandardCubeVerdict :=
  have h := einsteinBianchi_constrainedFEEC_summary
  ⟨⟨h.1.1.toTorusVerdict, h.1⟩, ⟨h.2.1.1.toMirrorVerdict, h.2.1⟩, h.2.2⟩

open Feec.Instances Feec.Instances.EinsteinBianchi.FEM

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- The old `einsteinBianchi_summary`, verbatim. -/
theorem ebVerdict_old_summary :
    -- the constrained FEEC verdicts, with the approximating `ℝ³` row
    ((TorusVerdict ∧ TorusSobolevVerdict ∧ TorusNonvacuous) ∧ EuclideanBand.EuclideanEBVerdict ∧
      (MirrorVerdict ∧ MirrorSobolevVerdict ∧ MirrorNonvacuous) ∧ MirrorFEMVerdict ∧
      StandardCubeVerdict) ∧
    -- the scheme (6.5) with mirror boundary conditions
    ((∃ (ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3) (C : ℝ),
        Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 ∅ Feec.FiniteElement.PolySeq.lowestOrder
          ρ C ∧ ∀ a : Fin 3, Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 {a}
            Feec.FiniteElement.PolySeq.lagrangeP2 ρ C) ∧
      (Feec.Models.Cube.MirrorWeakSymmetry.cosDatum.U₀ ∈ mirrorL3Data ∧
        (∀ s, Feec.Models.Cube.MirrorWeakSymmetry.cosDatum.U₀ ∈ mirrorSobData s) ∧
        Feec.Models.Cube.MirrorWeakSymmetry.cosDatum.U₀ ∉
          Feec.Models.Cube.MirrorBGG.complexQ.waveGroup.stationary) ∧
      ∀ {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
        (hT : Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 ∅
          Feec.FiniteElement.PolySeq.lowestOrder ρ C)
        (hB : ∀ a : Fin 3, Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 {a}
          Feec.FiniteElement.PolySeq.lagrangeP2 ρ C), MirrorFEMApprox.Verdict hT hB) ∧
    -- the scheme (6.5) with the thesis' boundary conditions
    ((Feec.EinsteinBianchi.BoundedFailure.betaDatum ∈ thesisTSD ∧
        ¬ Feec.EinsteinBianchi.MatrixModel.matrixComplex.wave.IsReducing thesisTSD) ∧
      (∃ (p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)) (C : ℝ),
        Feec.Models.Cube.FEM.PolySmoothingEstimatesMin 3 Feec.FiniteElement.PolySeq.lowestOrder
          p C ∧ Feec.Models.Cube.FEM.PolySmoothingEstimatesMin 3
            Feec.FiniteElement.PolySeq.lagrangeP2 p C) ∧
      ∀ {p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
        (hT : Feec.Models.Cube.FEM.PolySmoothingEstimatesMin 3
          Feec.FiniteElement.PolySeq.lowestOrder p C)
        (hB : Feec.Models.Cube.FEM.PolySmoothingEstimatesMin 3
          Feec.FiniteElement.PolySeq.lagrangeP2 p C), StandardCubeApprox.Verdict hT hB) :=
  have h := einsteinBianchi_summary
  ⟨⟨⟨h.1.1.1.toTorusVerdict, h.1.1⟩, h.1.2.1, ⟨h.1.2.2.1.1.toMirrorVerdict, h.1.2.2.1⟩,
    h.1.2.2.2⟩, h.2⟩

end Summary

end FeecCheck.InstanceVerdicts
