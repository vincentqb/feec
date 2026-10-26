module

public import Feec.HilbertComplex.Approximation.FullyDiscrete
public import Feec.Instances.Maxwell
public import Feec.Instances.EinsteinBianchiFEMComplex
public import Feec.Models.Cube.AbsorbingGalerkin

/-!
# Fully discrete instances: Maxwell, Einstein–Bianchi, the absorbing problem

Corollaries of the fully discrete FEEC theorem `Feec.HilbertComplex.dissipFEEC_fullyDiscrete`
for the semidiscrete instances of the library, with any time steps `τₙ > 0` (`n` the mesh level):

* `maxwell_cubePMC_crankNicolson`, `maxwell_cubePEC_crankNicolson`: Maxwell's equations on the cube
  `(0, ½)ⁿ` with perfect magnetic / electric conductor boundary conditions (Whitney forms of the
  Freudenthal meshes, smoothed projections), Crank–Nicolson in time: the fully discrete verdict
  (stability, temporal error `5/12 tₖ τₙ² ‖Lₙ³ v‖`, spatial plus temporal rate, convergence as
  `τₙ → 0`, Gauss-law residuals bounded by the error and tending to `0`) and exact energy
  conservation `‖Pₙᵏ v‖ = ‖v‖`;
* `einsteinBianchi_mirror_crankNicolson`: the mirror scheme (6.5) for the linearized
  Einstein–Bianchi system with Crank–Nicolson (the time discretization of [QuennevilleBelair2015],
  Ch. 7): the fully discrete verdict on the elliptic core (dense in the TSD states), energy
  conservation, and the **discrete hidden Gauss constraint kept exactly by every iterate**;
  `einsteinBianchi_mirror_crankNicolson_rate`: from the elliptic initialization (6.4), the error is
  the `O(h_N)` rate of `mirrorComplexRate` plus the temporal error `5/12 tₙ τ_N² ‖L_N³ Πₕ(0)‖`
  (a uniform-in-`N` bound of `‖L_N³ Πₕ(0)‖`, which would make this `O(h_N + τ_N²)`, is not
  proved);
* `absorbing_implicitEuler`, `absorbing_crankNicolson`: the absorbing (Silver–Müller) boundary
  problem on the cube, dissipative, with implicit Euler (order `1`, `K = 3/2`) and Crank–Nicolson
  (order `2`, `K = 5/12`): the fully discrete verdict, contraction of the iterates, convergence for
  every datum (the core is dense) and every convergent family of initial values as `τₙ → 0`.

The `O(h_N + Δt²)` estimate of the Crank–Nicolson scheme with inhomogeneous Dirichlet degrees of
freedom (`Feec.Models.Cube.InhomogeneousError`, the scheme as run by `fem4gr`) is a separate,
variational, estimate; its homogeneous case is the θ = 1/2 scheme
(`Feec.TimeStepping.isDirichletCNStep_top_iff`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7 (Crank–Nicolson for the Einstein–Bianchi system)
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7–9
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 8 (time discretization of
  Hodge evolution problems)

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
verdict and exact energy conservation of the iterates. [QuennevilleBelair2015], Ch. 7;
[Arnold2018], Ch. 8 -/
theorem maxwell_cubePMC_crankNicolson :
    ((ApproxFEEC.ofComplex (cubePMC n a).toComplex).crankNicolson τ hτ).Verdict
        (ApproxFEEC.ofComplexCore (cubePMC n a).toComplex) ∧
      ∀ N v k, ‖(((ApproxFEEC.ofComplex (cubePMC n a).toComplex).crankNicolson τ hτ).P N ^ k)
        v‖ = ‖v‖ :=
  ⟨dissipFEEC_fullyDiscrete _ _, SkewFEEC.norm_crankNicolson_pow_apply _ hτ⟩

/-- **Maxwell (perfect electric conductor, cube), Crank–Nicolson in time**: the fully discrete
verdict and exact energy conservation of the iterates. [QuennevilleBelair2015], Ch. 7;
[Arnold2018], Ch. 8 -/
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
/-- **The Einstein–Bianchi mirror scheme (6.5) with Crank–Nicolson** ([QuennevilleBelair2015],
Ch. 7): the fully discrete verdict on the elliptic core (whose closure is the TSD subspace),
exact energy conservation, and the discrete hidden Gauss constraint (`σₕ = 0`,
`uₕ ⊥ d̃ Φ(Vₕ⁰, 0)`, on real and imaginary parts) kept by every iterate. -/
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
/-- **Spatial `O(h)` plus temporal error for linearized gravity**: the mirror scheme (6.5) through
the complex-level front
end (`mirrorComplex`, whose discrete solutions are those of `mirrorFEMApprox`) with
Crank–Nicolson: the fully discrete verdict on its core, and the comparison initial values of the
`O(h)` rate class `mirrorComplexRate` (TSD data of `D(L³)`) are the elliptic initialization (6.4)
`Πₕ(0) = mirrorEllInit`. Hence, by `TimeScheme.Verdict.rate_iterates` with `v = Πₕ(0)`, at
`tₙ = n τ_N ∈ [0, T]`:
`‖S(tₙ) x - ι_N P_Nⁿ Πₕ(0)‖ ≤ (C + ‖ι_N‖ C' tₙ) h_N ‖x‖_{L³} + ‖ι_N‖ 5/12 tₙ τ_N² ‖L_N³ Πₕ(0)‖`.
This is `O(h_N + τ_N²)` only given a bound on `‖L_N³ Πₕ(0)‖` uniform in `N`, which is not proved
here. [QuennevilleBelair2015], Ch. 7 -/
theorem einsteinBianchi_mirror_crankNicolson_rate :
    ((ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).crankNicolson τ hτ).Verdict
        (ApproxFEEC.ofComplexCrimeCore (mirrorComplex hT hB)) ∧
      ∀ (T : ℝ), 0 ≤ T → ∀ (x : PiLp 2 SpaceQ), x ∈ mirrorL3Data → ∀ N,
        (mirrorComplexRate hT hB T).p x N 0 = mirrorEllInit hT hB x N :=
  ⟨dissipFEEC_fullyDiscrete _ _, fun T hT0 x hx N =>
    (galerkinRateClass_p (hfd := mirrorFEMApprox_finiteDimensional hT hB) _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ hx N ⟨le_rfl, by linarith⟩).trans
      (mirrorEllCmp_p_zero_eq_init hT hB (T + 1) x N)⟩

end EinsteinBianchi

/-! ### The absorbing boundary problem on the cube -/

section Absorbing

open Feec.Models.Cube.Absorbing

variable {τ : ℕ → ℝ} (hτ : ∀ N, 0 < τ N)

/-- **The absorbing problem with implicit Euler**: the fully discrete verdict (order `1`,
`K = 3/2`) on the dense Trotter–Kato core, so the iterates converge for every datum and every
convergent family of initial values as `τₙ → 0`. [Thomee2006], Ch. 7 -/
theorem absorbing_implicitEuler :
    absorbingGalerkinCore.Data.topologicalClosure = ⊤ ∧
      (absorbingGalerkin.thetaScheme 1 (by norm_num) τ hτ).Verdict absorbingGalerkinCore :=
  ⟨absorbingGalerkin_verdict.1, dissipFEEC_fullyDiscrete _ _⟩

/-- **The absorbing problem with Crank–Nicolson**: the fully discrete verdict (order `2`,
`K = 5/12`) on the dense Trotter–Kato core. [Thomee2006], Ch. 7 -/
theorem absorbing_crankNicolson :
    absorbingGalerkinCore.Data.topologicalClosure = ⊤ ∧
      (absorbingGalerkin.crankNicolson τ hτ).Verdict absorbingGalerkinCore :=
  ⟨absorbingGalerkin_verdict.1, dissipFEEC_fullyDiscrete _ _⟩

end Absorbing

end Feec.Instances.FullyDiscrete
