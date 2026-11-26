module

public import Feec.HilbertComplex.Approximation.FullyDiscrete
public import Feec.Instances.Maxwell
public import Feec.Instances.EinsteinBianchiFEMComplex
public import Feec.Models.Cube.AbsorbingGalerkin

/-!
# Fully discrete instances: Maxwell, Einstein–Bianchi, the absorbing problem

Corollaries of the fully discrete FEEC theorem `Feec.HilbertComplex.dissipFEEC_fullyDiscrete` for
the semidiscrete instances of the library, with any time steps `τₙ > 0`.

## Main results

* `maxwell_cubePMC_crankNicolson`, `maxwell_cubePEC_crankNicolson`: Maxwell's equations on the cube.
* `einsteinBianchi_mirror_crankNicolson`: the Einstein–Bianchi mirror scheme.
* `absorbing_implicitEuler`, `absorbing_crankNicolson`: the absorbing problem on the cube.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology Metric Feec.HilbertComplex
open Feec.Models.Cube.MirrorBGG (SpaceQ)

@[expose] public noncomputable section

namespace Feec.Instances.FullyDiscrete

/-! ### Maxwell's equations on the cube -/

section Maxwell

open Feec.Instances.Maxwell

variable (n : ℕ) [NeZero n] (a : ℤ) {τ : ℕ → ℝ} (hτ : ∀ N, 0 < τ N)

/-- **Maxwell (perfect magnetic conductor, cube), Crank–Nicolson in time**: the fully discrete
verdict and exact energy conservation. [QuennevilleBelair2015], Ch. 7; [Arnold2018], Ch. 8 -/
theorem maxwell_cubePMC_crankNicolson :
    ((ApproxFEEC.ofComplex (cubePMC n a).toComplex).crankNicolson τ hτ).Verdict
        (ApproxFEEC.ofComplexCore (cubePMC n a).toComplex) ∧
      ∀ N v k, ‖(((ApproxFEEC.ofComplex (cubePMC n a).toComplex).crankNicolson τ hτ).P N ^ k)
        v‖ = ‖v‖ :=
  ⟨dissipFEEC_fullyDiscrete _ _, SkewFEEC.norm_crankNicolson_pow_apply _ hτ⟩

/-- **Maxwell (perfect electric conductor, cube), Crank–Nicolson in time**: the fully discrete
verdict and exact energy conservation. [QuennevilleBelair2015], Ch. 7; [Arnold2018], Ch. 8 -/
theorem maxwell_cubePEC_crankNicolson :
    ((ApproxFEEC.ofComplex (cubePEC n a).toComplex).crankNicolson τ hτ).Verdict
        (ApproxFEEC.ofComplexCore (cubePEC n a).toComplex) ∧
      ∀ N v k, ‖(((ApproxFEEC.ofComplex (cubePEC n a).toComplex).crankNicolson τ hτ).P N ^ k)
        v‖ = ‖v‖ :=
  ⟨dissipFEEC_fullyDiscrete _ _, SkewFEEC.norm_crankNicolson_pow_apply _ hτ⟩

end Maxwell

/-! ### The Einstein–Bianchi mirror scheme -/

section EinsteinBianchi

open Feec.Instances.EinsteinBianchi.FEM Feec.Models.Cube.MirrorWeakSymmetry

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 ∅
    Feec.FiniteElement.PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3,
    Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 {a} Feec.FiniteElement.PolySeq.lagrangeP2 ρ C)
  {τ : ℕ → ℝ} (hτ : ∀ N, 0 < τ N)

set_option maxHeartbeats 1000000 in
/-- **The Einstein–Bianchi mirror scheme (6.5) with Crank–Nicolson**: the fully discrete verdict,
energy conservation and the discrete hidden Gauss constraint. [QuennevilleBelair2015], Ch. 7 -/
theorem einsteinBianchi_mirror_crankNicolson :
    ((mirrorFEMApprox hT hB).crankNicolson τ hτ).Verdict (mirrorEllCore hT hB) ∧
      (mirrorEllCore hT hB).Data.topologicalClosure = tsdQℝ ∧
      (∀ N v k, ‖(((mirrorFEMApprox hT hB).crankNicolson τ hτ).P N ^ k) v‖ = ‖v‖) ∧
      ∀ N {v : (mirrorFEMApprox hT hB).X N},
        v ∈ prodSub (hiddenGauss (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
          (mirrorWave_S0_surjective hT hB N)) → ∀ k,
        (((mirrorFEMApprox hT hB).crankNicolson τ hτ).P N ^ k) v ∈
          prodSub (hiddenGauss (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
            (mirrorWave_S0_surjective hT hB N)) := by
  refine ⟨dissipFEEC_fullyDiscrete _ _, mirrorEllCore_closure hT hB,
    SkewFEEC.norm_crankNicolson_pow_apply _ hτ, fun N v hv k => ?_⟩
  have hcl := Submodule.closed_of_finiteDimensional (prodSub (hiddenGauss (mirrorWave hT hB N)
    (mirrorWave_dt0_injective hT hB N) (mirrorWave_S0_surjective hT hB N)))
  refine DissipFEEC.crankNicolson_pow_mem (mirrorFEMApprox hT hB).toDissipFEEC hτ N
    (Kh := prodSub (hiddenGauss (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
      (mirrorWave_S0_surjective hT hB N)))
    hcl (fun w hw => ?_) hv k
  obtain ⟨⟨a, b⟩⟩ := w
  exact ⟨waveGen_mem_hiddenGauss _ _ _ hw.1, waveGen_mem_hiddenGauss _ _ _ hw.2⟩

set_option maxHeartbeats 1000000 in
/-- **The mirror scheme (6.5) with Crank–Nicolson at the complex level**, with the elliptic
initialization (6.4). [QuennevilleBelair2015], Ch. 7 -/
theorem einsteinBianchi_mirror_crankNicolson_rate :
    ((ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).crankNicolson τ hτ).Verdict
        (ApproxFEEC.ofComplexCrimeCore (mirrorComplex hT hB)) ∧
      (∀ (T : ℝ), 0 ≤ T → ∀ (x : PiLp 2 SpaceQ), x ∈ mirrorL3Data → ∀ N,
        (mirrorComplexRate hT hB T).p x N 0 = mirrorEllInit hT hB x N) ∧
      mirrorL3Data ⊆ complexQℝ.wave.domain :=
  ⟨dissipFEEC_fullyDiscrete _ _, fun T hT0 x hx N =>
    (galerkinRateClass_of_isOrthogonal_p (hfd := mirrorFEMApprox_finiteDimensional hT hB) _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx N ⟨le_rfl, by linarith⟩).trans
      (mirrorEllCmp_p_zero_eq_init hT hB (T + 1) x N),
    fun _ hx => LinearPMap.domainSq_le_domain hx.1.2⟩

end EinsteinBianchi

/-! ### The absorbing boundary problem on the cube -/

section Absorbing

open Feec.Models.Cube.Absorbing

variable {τ : ℕ → ℝ} (hτ : ∀ N, 0 < τ N)

/-- **The absorbing problem with implicit Euler**: the fully discrete verdict on the dense
Trotter–Kato core. [Thomee2006], Ch. 7 -/
theorem absorbing_implicitEuler :
    absorbingGalerkinCore.Data.topologicalClosure = ⊤ ∧
      (absorbingGalerkin.thetaScheme 1 (by norm_num) τ hτ).Verdict absorbingGalerkinCore :=
  ⟨absorbingGalerkin_verdict.1, dissipFEEC_fullyDiscrete _ _⟩

/-- **The absorbing problem with Crank–Nicolson**: the fully discrete verdict on the dense
Trotter–Kato core. [Thomee2006], Ch. 7 -/
theorem absorbing_crankNicolson :
    absorbingGalerkinCore.Data.topologicalClosure = ⊤ ∧
      (absorbingGalerkin.crankNicolson τ hτ).Verdict absorbingGalerkinCore :=
  ⟨absorbingGalerkin_verdict.1, dissipFEEC_fullyDiscrete _ _⟩

end Absorbing

end Feec.Instances.FullyDiscrete
