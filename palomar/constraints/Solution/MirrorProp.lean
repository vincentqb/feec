module

public import Solution.MirrorChain
public import Feec.Models.Cube.MirrorWaveRegularity

/-!
# Mirror boundary conditions: propagation of the constraints

The strong solutions of the challenge's system from TSD data are the real parts of the orbits of
`Feec.Models.Cube.MirrorBGG.complexQ` from their complexifications (`isStrongSolution_realL`,
`forward`), which stay in the constraint (`MirrorBGG.propagatesQ`); the non-stationary datum
`cosStateQ` (or `-i cosStateQ`) gives a moving TSD solution (`eq_zero_of_realL`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec Feec.Domain Feec.Models.BoundedDomain
open Feec.Models.Cube.FEM (cubeDomain cubeDomain_eq_Q)
open Feec.Models.Cube.Geometry (Q)
open Feec.Models.Cube.RowWise (ofRealL reL)
open Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.Mirror (MQ)
open Feec.Models.Cube.MirrorBGG (SpaceQ complexQ tsdQ W2Q)
open Feec.HilbertComplex (totalSub)

/-- **The real part of an orbit from the constraint is a strong solution** of the challenge's
system. -/
theorem isStrongSolution_realL {x : PiLp 2 SpaceQ} (hx : x ∈ complexQ.wave.domain)
    (hc : x ∈ totalSub tsdQ) (T : ℝ) :
    IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T)
      fun t => realL (complexQ.waveGroup.S t x) := by
  have hX := complexQ.isStrongSolution_waveGroup hx T
  refine ⟨realL.continuous.comp_continuousOn hX.continuousOn, fun t ht => ⟨_,
    isWave_realL (x := ⟨_, hX.mem_domain ht⟩)
      (Feec.Models.Cube.MirrorBGG.propagatesQ hX (by simpa using hc)
        (fun _ _ => Submodule.zero_mem _) t ht),
    realL.hasFDerivAt.comp_hasDerivWithinAt t
      ((hX.hasDerivWithinAt ht).congr_deriv (add_zero _))⟩⟩

theorem realL_orbit_zero {X : MState} (h0 : X.1 = 0) (hM : X.2.2.1 = 0) :
    realL (complexQ.waveGroup.S 0 (cplx X)) = X := by
  simpa using realL_cplx h0 hM

/-- **A constrained state is zero if the real parts of it and of `-i` times it vanish.** -/
theorem eq_zero_of_realL {y : PiLp 2 SpaceQ} (hc : y ∈ totalSub tsdQ) (h : realL y = 0)
    (h' : realL (-Complex.I • y) = 0) : y = 0 := by
  obtain ⟨h0, -, hM, -⟩ := Feec.Models.Cube.MirrorBGG.mem_tsdQ_iff.1 hc
  have hE : ∀ (z : PiLp 2 SpaceQ), realL z = 0 → ∀ a, rowRe (show MQ from z 1) a = 0 :=
    fun z hz a =>
    (cQ _).symm.injective ((congrArg (fun Z : MState => Z.2.1 a) hz).trans (map_zero _).symm)
  have hB : ∀ (z : PiLp 2 SpaceQ), realL z = 0 → ∀ a,
      rowRe2 (WithLp.ofLp (z 2 : W2Q)).2 a = 0 := fun z hz a =>
    (cQ _).symm.injective ((congrArg (fun Z : MState => Z.2.2.2 a) hz).trans (map_zero _).symm)
  have hre1 : ∀ (z : PiLp 2 SpaceQ), realL z = 0 → ∀ p : Fin 3 × Fin 3,
      reL _ ((show MQ from z 1) p) = 0 := fun z hz p => by
    rw [← rowRe_eq1, hE z hz]; rfl
  have hre2 : ∀ (z : PiLp 2 SpaceQ), realL z = 0 → ∀ p : Fin 3 × Fin 3,
      reL _ ((WithLp.ofLp (z 2 : W2Q)).2 p) = 0 := fun z hz p => by
    have e := rowRe2_eq2 (WithLp.ofLp (z 2 : W2Q)).2 p.1 p.2
    rw [hB z hz] at e
    have hs : sg2 p.2 ≠ 0 := fun h0 => by simpa [h0] using sg2_mul_self p.2
    exact ((smul_eq_zero.1 e.symm).resolve_left hs)
  have h1 : (show MQ from y 1) = 0 := by
    refine PiLp.ext fun p => ?_
    rw [ofReal_decomp ((show MQ from y 1) p), hre1 y h p]
    have e := hre1 _ h' p
    change reL _ (-Complex.I • (show MQ from y 1) p) = 0 at e
    rw [e, map_zero, smul_zero, add_zero]
    rfl
  have h2 : (WithLp.ofLp (y 2 : W2Q)).2 = 0 := by
    refine PiLp.ext fun p => ?_
    rw [ofReal_decomp ((WithLp.ofLp (y 2 : W2Q)).2 p), hre2 y h p]
    have e := hre2 _ h' p
    change reL _ (-Complex.I • (WithLp.ofLp (y 2 : W2Q)).2 p) = 0 at e
    rw [e, map_zero, smul_zero, add_zero]
    rfl
  refine PiLp.ext fun i => ?_
  fin_cases i
  · exact h0
  · exact h1
  · change (y 2 : W2Q) = WithLp.toLp 2 (0, 0)
    rw [← hM, ← h2]
    rfl

/-- A chain `x, L x, L² x, L³ x` of constrained states with `Re L x ≠ 0` gives the non-vacuity
clause. -/
theorem exists_chain (x : complexQ.wave.domain) (hc : (x : PiLp 2 SpaceQ) ∈ totalSub tsdQ)
    (h1 : complexQ.wave x ∈ complexQ.wave.domain)
    (h2 : complexQ.wave ⟨_, h1⟩ ∈ complexQ.wave.domain) (hne : realL (complexQ.wave x) ≠ 0) :
    ∃ U₀ V₁ V₂ V₃, mirrorData.IsWave U₀ V₁ ∧ mirrorData.IsWave V₁ V₂ ∧
      mirrorData.IsWave V₂ V₃ ∧ IsTSDState U₀ ∧ V₁ ≠ 0 := by
  have hc1 := Feec.Models.Cube.MirrorBGG.reducingSubcomplexQ.isReducing_wave.mapsTo x hc
  have hc2 := Feec.Models.Cube.MirrorBGG.reducingSubcomplexQ.isReducing_wave.mapsTo ⟨_, h1⟩ hc1
  exact ⟨_, _, _, _, isWave_realL hc, isWave_realL (x := ⟨_, h1⟩) hc1,
    isWave_realL (x := ⟨_, h2⟩) hc2, isTSDState_realL hc, hne⟩

/-- **A moving TSD solution**: from `cosStateQ` or `-i cosStateQ`. -/
theorem exists_mirror_chain : ∃ U₀ V₁ V₂ V₃, mirrorData.IsWave U₀ V₁ ∧
    mirrorData.IsWave V₁ V₂ ∧ mirrorData.IsWave V₂ V₃ ∧ IsTSDState U₀ ∧ V₁ ≠ 0 := by
  set x : complexQ.wave.domain := ⟨_, cosDatum.mem⟩
  have hc : (x : PiLp 2 SpaceQ) ∈ totalSub tsdQ := cosDatum.tsd
  have h1 : complexQ.wave x ∈ complexQ.wave.domain := cosDatum.mem₂
  have h2 : complexQ.wave ⟨_, h1⟩ ∈ complexQ.wave.domain := cosDatum_LLU₀_mem
  have hne : complexQ.wave x ≠ 0 :=
    (HilbertComplex.wave_compress Feec.Models.Cube.Mirror.eight_pos
      Feec.Models.Cube.MirrorBGG.inner_J
      Feec.Models.Cube.MirrorBGG.reducingSubcomplex_range).apply_ne_zero x fun h0 =>
        Feec.Models.Cube.MirrorBGG.wave_cosState_ne ((LinearPMap.apply_congr' _ _ _
          Feec.Models.Cube.MirrorBGG.totalJ_cosStateQ.symm).trans h0)
  by_cases hr : realL (complexQ.wave x) = 0
  · set c : ℂ := -Complex.I
    have hcx : c • (x : PiLp 2 SpaceQ) ∈ totalSub tsdQ := Submodule.smul_mem _ c hc
    have ew : complexQ.wave (c • x) = c • complexQ.wave x := LinearPMap.map_smul _ _ _
    have h1' : complexQ.wave (c • x) ∈ complexQ.wave.domain := ew ▸ Submodule.smul_mem _ c h1
    have ew2 : complexQ.wave ⟨_, h1'⟩ = c • complexQ.wave ⟨_, h1⟩ :=
      (LinearPMap.apply_congr' _ _ (Submodule.smul_mem _ c h1) ew).trans
        (LinearPMap.map_smul _ c ⟨_, h1⟩)
    have h2' : complexQ.wave ⟨_, h1'⟩ ∈ complexQ.wave.domain := ew2 ▸ Submodule.smul_mem _ c h2
    refine exists_chain (c • x) hcx h1' h2' fun h0 => hne ?_
    have hc1 := Feec.Models.Cube.MirrorBGG.reducingSubcomplexQ.isReducing_wave.mapsTo x hc
    exact eq_zero_of_realL hc1 hr (by rw [← ew]; exact h0)
  · exact exists_chain x hc h1 h2 hr

/-- **Propagation of the constraints under mirror boundary conditions**
(the mirror clause of `FEEC.tsd_boundary_conditions`). -/
theorem mirror_tsd_propagates_of :
    (∀ T U U', IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T) U →
      IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T) U' → U 0 = U' 0 →
        EqOn U U' (Icc 0 T)) ∧
    (∀ U₀ V, mirrorData.IsWave U₀ V → IsTSDState U₀ → ∀ T,
      ∃ U, U 0 = U₀ ∧ IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T) U) ∧
    (∀ T U, IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T) U → IsTSDState (U 0) →
      ∀ t ∈ Icc 0 T, IsTSDState (U t)) ∧
    ∃ U₀ V₁ V₂ V₃, mirrorData.IsWave U₀ V₁ ∧ mirrorData.IsWave V₁ V₂ ∧
      mirrorData.IsWave V₂ V₃ ∧ IsTSDState U₀ ∧ V₁ ≠ 0 := by
  refine ⟨fun T U U' hU hU' h0 => WeakSymmetryData.isStrongSolution_unique hU hU' h0,
    fun U₀ V h hT T => ?_, fun T U hU hT t ht => ?_, exists_mirror_chain⟩
  · obtain ⟨hd, hc, -, -⟩ := forward h hT
    exact ⟨_, realL_orbit_zero hT.1 hT.2.1, isStrongSolution_realL hd hc T⟩
  · obtain ⟨V, hV, -⟩ := hU.2 0 (left_mem_Icc.2 (ht.1.trans ht.2))
    obtain ⟨hd, hc, -, -⟩ := forward hV hT
    have e := WeakSymmetryData.isStrongSolution_unique hU (isStrongSolution_realL hd hc T)
      (realL_orbit_zero hT.1 hT.2.1).symm ht
    rw [e]
    exact isTSDState_realL (Feec.Models.Cube.MirrorBGG.propagatesQ
      (complexQ.isStrongSolution_waveGroup hd T) (by simpa using hc)
      (fun _ _ => Submodule.zero_mem _) t ht)

end FEEC
