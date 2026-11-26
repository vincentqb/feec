module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.Numerics.PlaneWaveCubeError
public import Feec.Models.Cube.FiniteElementConvergence

/-!
# Inhomogeneous boundary data in the FEEC theorem: the runs of the thesis, Ch. 7

This file applies the fully discrete FEEC theorem with forcing and inhomogeneous boundary data to
the Whitney forms of the cube, and reads the Crank–Nicolson runs of [QuennevilleBelair2015], Ch. 7
as lifted forced Crank–Nicolson iterates.

## Main results

* `lifted`: the error of the lifted iterates is at most the lifting error plus the forced error.
* `planeWave_run`: the plane-wave run converges at the rate `O(h + Δt²)`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter

@[expose] public noncomputable section

namespace Feec.Instances.Lifting

open Feec.HilbertComplex Feec.Models.Cube Feec.Models.Cube.FEM Feec.Models.Cube.Inhomogeneous

theorem wave_le_rowWaveMax : rowComplexMin.wave ≤ waveMax rowComplexMin rowComplex :=
  wave_le_waveMax rowComplexMin_d_le

/-- The window `H̊Λ⁰ → H̊Λ¹ → L²Λ²` of the Whitney forms with vanishing boundary DOFs. -/
abbrev rowFEEC (K : Submodule ℝ RowSpace) (hK : IsClosed (K : Set RowSpace)) :
    ConstrainedFEEC rowComplexMin ℕ :=
  (FEM.whitneyFamilyMin 3).windowFEEC 0 3 K hK

/-- **The Ch. 7 boundary value problem in the FEEC theorem**: the error of the lifted iterates is
at most the lifting error plus the forced error. [QuennevilleBelair2015], Ch. 7 -/
theorem lifted (K : Submodule ℝ RowSpace) (hK : IsClosed (K : Set RowSpace))
    (Θ : (rowFEEC K hK).toApprox.TimeScheme) {T : ℝ} {G DG AG f U : ℝ → RowSpace}
    (hG : Evolution.IsLifting (waveMax rowComplexMin rowComplex) (Icc 0 T) G DG AG)
    (hU : Evolution.IsBoundarySolution (waveMax rowComplexMin rowComplex) rowComplexMin.wave
      (Icc 0 T) f G U)
    (hc : ContinuousOn (f - DG + AG) (Icc 0 T)) (N : ℕ) (Gh : ℕ → RowSpace)
    (v : (rowFEEC K hK).toApprox.X N) (g w : ℕ → (rowFEEC K hK).toApprox.X N) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ N ∈ Icc 0 T) :
    ‖U (n * Θ.τ N) - (Gh n + Θ.forcedSol N v g n)‖ ≤ ‖G (n * Θ.τ N) - Gh n‖ +
      (‖Evolution.mild (rowFEEC K hK).toApprox.S 0 (U 0 - G 0) (f - DG + AG) (n * Θ.τ N) -
          (rowFEEC K hK).toApprox.incl N (w n)‖ +
        Θ.M T * (‖v - w 0‖ + ∑ k ∈ Finset.range n, ‖w (k + 1) - Θ.P N (w k) - g k‖)) := by
  refine ((((whitneyFamilyMin 3).feec.full 0 3 K hK).wave Θ).lifted_iterates wave_le_rowWaveMax hG
    hU hc N Gh v g w hn).trans (add_le_add le_rfl (add_le_add le_rfl ?_))
  exact mul_le_of_le_one_left (mul_nonneg (Θ.M_nonneg (hn.1.trans hn.2) N)
    (add_nonneg (norm_nonneg (v - w 0))
      (Finset.sum_nonneg fun k _ => norm_nonneg (w (k + 1) - Θ.P N (w k) - g k))))
    ((rowFEEC K hK).norm_toApprox_incl_le N)

section RowSolution

variable {T L : ℝ} (X : RowSolution T L)

theorem isLifting_field (I : Set ℝ) :
    Evolution.IsLifting (waveMax rowComplexMin rowComplex) I X.field X.field₁ X.field₁ :=
  ⟨fun t _ => X.mem_graph_waveMax t, fun t _ => (X.hasDerivAt_field t).hasDerivWithinAt⟩

/-- **A smooth row solution solves the Ch. 7 problem with its own boundary values.** -/
theorem isBoundarySolution_field (I : Set ℝ) :
    Evolution.IsBoundarySolution (waveMax rowComplexMin rowComplex) rowComplexMin.wave I 0
      X.field X.field :=
  (Evolution.isBoundarySolution_iff wave_le_rowWaveMax (isLifting_field X I)).2 (by
    simpa using Evolution.IsStrongSolution.zero)

end RowSolution

section ThreeRows

open scoped RealInnerProductSpace

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex ℝ c W} (S : H.Subcomplex) [∀ i, FiniteDimensional ℝ (S.V i)]
  (V₀ : ∀ i, Submodule ℝ (W i))

theorem eq_add_forcedIter3 {s : ℝ} (hs : 0 < s) {M : ℕ} {g u : ℕ → DState3 S}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep (interior3 S V₀) (discreteWave3 S) s 0
      (g (n + 1)) (u n) (u (n + 1))) (hu0 : u 0 = g 0) :
    ∃ b : ℕ → interior3 S V₀,
      (∀ n, TimeStepping.IsDirichletCNStep (interior3 S V₀) (discreteWave3 S) s 0 (g (n + 1))
        (g n) (g (n + 1) + b n)) ∧
      ∀ n ≤ M, u n = g n +
        ((TimeStepping.forcedIter (TimeStepping.compressCN (interior3 S V₀) (discreteWave3 S) s)
          0 b n : interior3 S V₀) : DState3 S) := by
  have h0 : u 0 - g 0 ∈ interior3 S V₀ := by rw [hu0, sub_self]; exact Submodule.zero_mem _
  obtain ⟨b, hb, hu⟩ := TimeStepping.exists_eq_add_forcedIter_of_isDirichletCNStep
    (fun w _ => (inner_discreteWave3_self S w).le) hs hstep h0
  have e : (⟨_, h0⟩ : interior3 S V₀) = 0 := Subtype.ext (sub_eq_zero.2 hu0)
  rw [e] at hu
  exact ⟨b, hb, hu⟩

end ThreeRows

/-- **The Dirichlet Crank–Nicolson iterates of the Whitney forms are lifted forced Crank–Nicolson
iterates.** [QuennevilleBelair2015], Ch. 7 -/
theorem whitney_cn_eq_lifted {T L : ℝ} (X : Fin 3 → RowSolution T L) (N : ℕ) {Δt : ℝ}
    (hΔt : 0 < Δt) {M : ℕ} {u : ℕ → DState3 (whitneyRow N)}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep (whitneyInterior3 N)
      (discreteWave3 (whitneyRow N)) (Δt / 2) 0 (exactInterp X N ((n + 1 : ℕ) * Δt)) (u n)
        (u (n + 1)))
    (hu0 : u 0 = exactInterp X N 0) :
    ∃ b : ℕ → whitneyInterior3 N,
      (∀ n, TimeStepping.IsDirichletCNStep (whitneyInterior3 N) (discreteWave3 (whitneyRow N))
        (Δt / 2) 0 (exactInterp X N ((n + 1 : ℕ) * Δt)) (exactInterp X N (n * Δt))
          (exactInterp X N ((n + 1 : ℕ) * Δt) + b n)) ∧
      ∀ n ≤ M, u n = exactInterp X N (n * Δt) +
        ((TimeStepping.forcedIter
          (TimeStepping.compressCN (whitneyInterior3 N) (discreteWave3 (whitneyRow N)) (Δt / 2))
            0 b n : whitneyInterior3 N) : DState3 (whitneyRow N)) :=
  eq_add_forcedIter3 (whitneyRow N) _ (half_pos hΔt) (g := fun n => exactInterp X N (n * Δt))
    hstep (by simpa using hu0)

/-- **The Ch. 7 plane-wave run as a lifted forced Crank–Nicolson run**, converging at the rate
`O(h + Δt²)`. [QuennevilleBelair2015], Ch. 7 -/
theorem planeWave_run (Ap Ax w T : ℝ) (N : ℕ) {Δt : ℝ} (hΔt : 0 < Δt) {M : ℕ}
    (hM : (M : ℝ) * Δt ≤ T) {u : ℕ → DState3 (whitneyRow N)}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep (whitneyInterior3 N)
      (discreteWave3 (whitneyRow N)) (Δt / 2) 0
        (exactInterp (Numerics.PlaneWaveCube.planeWaveRows Ap Ax w T) N ((n + 1 : ℕ) * Δt))
        (u n) (u (n + 1)))
    (hu0 : u 0 = exactInterp (Numerics.PlaneWaveCube.planeWaveRows Ap Ax w T) N 0) :
    (∃ b : ℕ → whitneyInterior3 N,
      (∀ n, TimeStepping.IsDirichletCNStep (whitneyInterior3 N) (discreteWave3 (whitneyRow N))
        (Δt / 2) 0
          (exactInterp (Numerics.PlaneWaveCube.planeWaveRows Ap Ax w T) N ((n + 1 : ℕ) * Δt))
          (exactInterp (Numerics.PlaneWaveCube.planeWaveRows Ap Ax w T) N (n * Δt))
          (exactInterp (Numerics.PlaneWaveCube.planeWaveRows Ap Ax w T) N ((n + 1 : ℕ) * Δt) +
            b n)) ∧
      ∀ n ≤ M,
        u n = exactInterp (Numerics.PlaneWaveCube.planeWaveRows Ap Ax w T) N (n * Δt) +
          ((TimeStepping.forcedIter
            (TimeStepping.compressCN (whitneyInterior3 N) (discreteWave3 (whitneyRow N))
              (Δt / 2)) 0 b n :
            whitneyInterior3 N) : DState3 (whitneyRow N))) ∧
      ‖dEmb3 (whitneyRow N) (u M) -
          exactField (Numerics.PlaneWaveCube.planeWaveRows Ap Ax w T) (M * Δt)‖ ≤
        cnConst * Numerics.PlaneWaveCube.pwBound Ap Ax w * (1 + T) * (meshSize N + Δt ^ 2) :=
  ⟨whitney_cn_eq_lifted _ N hΔt hstep hu0,
    (Numerics.PlaneWaveCube.planeWave_cn_error_le Ap Ax w T N hΔt hM hstep hu0).1⟩

end Feec.Instances.Lifting
