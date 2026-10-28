module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.Numerics.PlaneWaveCubeError
public import Feec.Models.Cube.FiniteElementConvergence

/-!
# Inhomogeneous boundary data in the FEEC theorem: the runs of the thesis, Ch. 7

The fully discrete field of the FEEC theorem (`Feec.HilbertComplex.ConformingFamily.feec`,
field `full`) carries forcing and inhomogeneous boundary data
(`Feec.HilbertComplex.DissipFEEC.TimeScheme.Verdict.forced_iterates`, `lifted_iterates`): for a
lifting `G` of the boundary data, the solution is `G` plus the mild solution of the homogeneous
problem with the forcing `f − G' + L_max G` (`Feec.Evolution.IsBoundarySolution.eq_add_mild`), and
the lifted iterates `Gₕ,ₙ + ιₕ Wₙ`, `Wₙ₊₁ = Pₕ Wₙ + gₙ`, have error at most the lifting error plus
the forced error (the discrete Duhamel formula). This module reads the Crank–Nicolson runs of
[QuennevilleBelair2015], Ch. 7 (`Feec.Models.Cube.Inhomogeneous`) through it.

* **The Ch. 7 problem as a crown corollary** (`lifted`): on the cube `Q = (0, ½)³`, the window
  `H̊Λ⁰ → H̊Λ¹ → L²Λ²` of the Whitney family with vanishing boundary DOFs
  (`Feec.Models.Cube.FEM.whitneyFamilyMin`) with any closed constraint, the operator
  `L_max = 𝐝 − 𝐝_min†` without boundary conditions (`Inhomogeneous.waveMax`, `L ≤ L_max` by
  `wave_le_rowWaveMax`), every time scheme of the crown (Crank–Nicolson, the θ-schemes, the
  A-stable rational and Runge–Kutta schemes), every lifting and every solution with its boundary
  values: the lifted fully discrete error bound.
* **Smooth row solutions are exact liftings** (`isLifting_field`, `isBoundarySolution_field`):
  every smooth solution of one row of (4.14) (`Feec.Models.Cube.Inhomogeneous.RowSolution`, e.g.
  a row of the plane wave of Ch. 7, `Feec.Numerics.PlaneWaveCube.planeWaveRows`) solves
  `U' = L_max U` with its own boundary values, so it is an admissible lifting in `lifted` (with
  vanishing mild part).
* **The `fem4gr` scheme has the structure of a lifted forced Crank–Nicolson scheme**
  (`whitney_cn_eq_lifted`, `planeWave_run`): the Crank–Nicolson iterates `uₙ` with the boundary
  DOFs of the interpolated exact solution `Π_h U(tₙ)` (`TimeStepping.IsDirichletCNStep`) are
  `uₙ = Π_h U(tₙ) + Wₙ`, with `Wₙ` the forced iterates (`TimeStepping.forcedIter`) from `0` of the
  Crank–Nicolson step `cayley(A₀, Δt/2)` of the compression `A₀` of the scheme to the fields with
  vanishing boundary DOFs, and the load `bₙ ∈ V̊ₕ` the interior part of the Dirichlet step from
  the interpolant, `Π_h U(tₙ) ↦ Π_h U(tₙ₊₁) + bₙ`
  (`TimeStepping.exists_eq_add_forcedIter_of_isDirichletCNStep`); for the plane wave the run
  converges at the rate `O(h + Δt²)` (`Feec.Numerics.PlaneWaveCube.planeWave_cn_error_le`).

What is **not** proved here: the identification of the compression `A₀` of `fem4gr`'s matrix on
`V̊ₕ` with the discrete wave operator `Lₕ` of the crown's window of `whitneyFamilyMin` (both are
`𝐝ₕ − 𝐝ₕ*` on `V̊ₕ`, on isometric copies of `V̊ₕ`), which would make `Wₙ` literally the forced
iterates of the crown's `DissipFEEC.crankNicolson`, so the `fem4gr` iterates and `lifted` are not
yet the same statement; a consistency bound for the loads `bₙ`, which would give a forced rate; and
the link of the three-field step `TimeStepping.IsFullCNStep` (solved by MINRES after the signed
symmetrization of `Feec.TimeStepping.BlockMatrix`) to the crown's schemes; the crown's own
Crank–Nicolson iterates solve the signed system in every basis
(`Feec.HilbertComplex.SkewFEEC.crankNicolson_signed`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7 (the Crank–Nicolson runs with the boundary data of the exact solution), §4.3 (Thm 4.3)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §4.2 (inhomogeneous problems)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter

@[expose] public noncomputable section

namespace Feec.Instances.Lifting

open Feec.HilbertComplex Feec.Models.Cube Feec.Models.Cube.FEM Feec.Models.Cube.Inhomogeneous

/-- `L = 𝐝 − 𝐝† ≤ L_max = 𝐝 − 𝐝_min†` on the row `H̊Λ⁰ → H̊Λ¹ → L²Λ²` of the cube. -/
theorem wave_le_rowWaveMax : rowComplexMin.wave ≤ waveMax rowComplexMin rowComplex :=
  wave_le_waveMax rowComplexMin_d_le

/-- The conforming window `H̊Λ⁰ → H̊Λ¹ → L²Λ²` of the Whitney forms with vanishing boundary DOFs
on the cube, with the closed constraint `K`. -/
abbrev rowFEEC (K : Submodule ℝ RowSpace) (hK : IsClosed (K : Set RowSpace)) :
    ConstrainedFEEC rowComplexMin ℕ :=
  (FEM.whitneyFamilyMin 3).windowFEEC 0 3 K hK

/-- **The Ch. 7 boundary value problem in the FEEC theorem**: for every closed constraint, every
time scheme `Θ` of the conforming window of the Whitney forms with vanishing boundary DOFs, every
lifting `G` of boundary data for `L_max` and every solution `U` of `U' = L_max U + f` with the
boundary values of `G`, the lifted iterates `Gₕ,ₙ + ιₕ Wₙ` (`Wₙ₊₁ = Pₕ Wₙ + gₙ`) have error at
most the lifting error plus the forced error for the mild solution `U − G`
(`‖U(tₙ) − Gₕ,ₙ − ιₕ Wₙ‖ ≤ ‖G(tₙ) − Gₕ,ₙ‖ + ‖(U − G)(tₙ) − ιₕ wₙ‖ + M(T)(‖v − w₀‖ + Σ ‖dₖ‖)`),
from the field `full` of the FEEC theorem (`ιₕ` is an inclusion, `‖ιₕ‖ ≤ 1`).
[QuennevilleBelair2015], Ch. 7 -/
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

/-- **A smooth row solution is a lifting** for `L_max`, with `G' = L_max G`. -/
theorem isLifting_field (I : Set ℝ) :
    Evolution.IsLifting (waveMax rowComplexMin rowComplex) I X.field X.field₁ X.field₁ :=
  ⟨fun t _ => X.mem_graph_waveMax t, fun t _ => (X.hasDerivAt_field t).hasDerivWithinAt⟩

/-- **A smooth row solution solves the Ch. 7 problem with its own boundary values**: it is an
admissible lifting and solution in `lifted`, with vanishing mild part. -/
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

/-- **The three-row Dirichlet CN iterates are lifted forced Crank–Nicolson iterates**: started
from the lifting (`u₀ = g₀`), `uₙ = gₙ + Wₙ` for `n ≤ M`, `Wₙ` the forced iterates from `0` of
the Crank–Nicolson step of the compression of the row-wise scheme to `V̊ₕ`, with the loads `bₙ`
the interior parts of the Dirichlet steps from the lifting, `gₙ ↦ gₙ₊₁ + bₙ`. -/
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

/-- **The `fem4gr` iterates are lifted forced Crank–Nicolson iterates**: for three smooth row
solutions `X` and the Crank–Nicolson iterates `uₙ` on the three-row Whitney space with the
boundary DOFs of `Π_h U(tₙ)` prescribed, started from `Π_h U(0)`, `uₙ = Π_h U(tₙ) + Wₙ` for
`n ≤ M`, `Wₙ` the forced iterates from `0` of the Crank–Nicolson step of the compression of the
scheme to `V̊ₕ` with the loads `bₙ ∈ V̊ₕ` of the Dirichlet steps from the interpolant,
`Π_h U(tₙ) ↦ Π_h U(tₙ₊₁) + bₙ`. [QuennevilleBelair2015], Ch. 7 -/
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

/-- **The Ch. 7 plane-wave run as a lifted forced Crank–Nicolson run**: the iterates of
`Feec.Numerics.PlaneWaveCube.planeWave_cn_error_le` are the interpolated plane wave plus forced
Crank–Nicolson iterates of the compression on `V̊ₕ`, with the loads of the Dirichlet steps from
the interpolant (`whitney_cn_eq_lifted`), and they converge at the rate `O(h + Δt²)`.
[QuennevilleBelair2015], Ch. 7 -/
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
