module

public import Feec.Models.Cube.DeRhamIdentFEM
public import Feec.Models.Cube.WhitneyRate
public import Feec.Models.Cube.SmoothingEstimates
public import Feec.HilbertComplex.Approximation.StaticFEEC

/-!
# The Whitney finite element method on the cube as a conforming family

On the cube `Q = (0, ½)ⁿ` with the level-`(N + 1)` Freudenthal meshes (mesh size
`h_N = FEM.meshSize N = 1 / (2 (N + 1))`) and their lowest-order Whitney complexes
`FEM.whitney n N ⊆ HΛ(Q)` and `FEM.whitneyMin n N ⊆ H̊Λ(Q)` (vanishing boundary DOFs), the
hypotheses of the static FEEC theorem (`Feec.HilbertComplex.ConformingFamily.staticFEEC`) are
theorems:

* the smoothing estimates `FEM.SmoothingEstimates`, `FEM.SmoothingEstimatesMin`
  (`FEM.smoothingEstimates_exists`, `FEM.smoothingEstimatesMin_exists`,
  `Feec.Models.Cube.SmoothingEstimates`) make the Whitney complexes, with the smoothed projections
  `π_N = J_N⁻¹ Q_N`, **conforming families** (`SmoothingEstimates.family`,
  `SmoothingEstimatesMin.family`, `ConformingFamily.ofSmoothing`; with the estimates of
  `smoothingEstimates_exists`, `whitneyFamily`, `whitneyFamilyMin`), the approximation property
  being the density of the Whitney spaces (`tendsto_infDist_whitney`);
* the closed range of `HΛ(Q)` and `H̊Λ(Q)` (`closedRangeAt`, `closedRangeAt_min`, Poincaré
  constant `(2π)⁻¹`, `Feec.Models.Cube.DeRhamIdentFEM`) and the finite-dimensionality of their
  harmonic forms;
* the Whitney interpolation error for `C²` forms (`Feec.Models.Cube.WhitneyRate`) is a
  **Jackson estimate** of order `h_N` (`whitneyJackson`, `whitneyJacksonMin`).

So `(whitneyFamily n).staticFEEC closedRangeAt j` gives, with no hypothesis beyond the data of
the problem, the uniform discrete Poincaré inequality, the uniform well-posedness and stability of
the discrete mixed Hodge Laplacian, the vanishing harmonic gap, the discrete cohomology,
quasi-optimality and convergence, and its `rate` with `whitneyJackson n` the `O(h)` convergence
of the mixed method for `C²` solutions; the same for `H̊Λ(Q)` with `whitneyFamilyMin`.

The semi-discrete Hodge wave equation converges on every window: for `D(L)` data
(`exists_tendstoUniformlyOn_window_whitney` in `Feec.Models.Cube.WhitneyApprox`;
`exists_tendstoUniformlyOn_windowMin_whitney` here) and at the rate `O(h)` for `C²` solutions
(`norm_sub_le_meshSize_window_smooth`, `norm_sub_le_meshSize_windowMin_smooth` in
`Feec.Models.Cube.WhitneyRate`; these need no smoothed projection). Maxwell's equations (PMC and
PEC) are the instances `Feec.Instances.Maxwell.cubePMC`, `Feec.Instances.Maxwell.cubePEC` of the FEEC
theorem.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (discrete Poincaré inequality, Thm 3.6), Thm 3.8 (stability), Thm 3.9
  (quasi-optimality), §5.5 (smoothed projections)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (rates for smooth
  solutions)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.14 (convergence of the semi-discrete Hodge wave equation)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.HilbertComplex Filter Topology

variable {n : ℕ} [NeZero n]

/-! ### The Whitney forms as conforming families -/

variable {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ}

/-- **The conforming family of the smoothing estimates `hE`** ([AFW2010], §5.5): the Whitney
complexes of the Freudenthal meshes with the smoothed projections `π_N = J_N⁻¹ Q_N`
(`SmoothingEstimates.proj`), a conforming family of `HΛ(Q)` (`ConformingFamily.ofSmoothing`). -/
def SmoothingEstimates.family (hE : SmoothingEstimates n p C) : ConformingFamily (complex n) ℕ :=
  .ofSmoothing atTop (whitney n) (fun N => smoothed n N (p N) (hE.isMaximal N))
    (by norm_num : (1 / 2 : ℝ) < 1) hE.close hE.bound tendsto_infDist_whitney

/-- **The conforming family of the smoothing estimates `hE` with vanishing boundary DOFs**, a
conforming family of `H̊Λ(Q)`. -/
def SmoothingEstimatesMin.family (hE : SmoothingEstimatesMin n p C) :
    ConformingFamily (complexMin n) ℕ :=
  .ofSmoothing atTop (whitneyMin n) (fun N => smoothedMin n N (p N) (hE.isMinimal N))
    (by norm_num : (1 / 2 : ℝ) < 1) hE.close hE.bound tendsto_infDist_whitneyMin

variable (n)

/-- **The Whitney forms of the Freudenthal meshes of the cube** with the smoothed projections
(`smoothingEstimates_exists`), a conforming family of `HΛ(Q)`. -/
def whitneyFamily : ConformingFamily (complex n) ℕ :=
  (smoothingEstimates_exists (n := n)).choose_spec.choose_spec.family

/-- **The Whitney forms with vanishing boundary DOFs**, a conforming family of `H̊Λ(Q)`. -/
def whitneyFamilyMin : ConformingFamily (complexMin n) ℕ :=
  (smoothingEstimatesMin_exists (n := n)).choose_spec.choose_spec.family

@[simp] theorem whitneyFamily_V : (whitneyFamily n).V = whitney n := rfl

@[simp] theorem whitneyFamilyMin_V : (whitneyFamilyMin n).V = whitneyMin n := rfl

/-- **The Jackson estimate of the Whitney forms**: `C²` forms (`IsC2Form`) are approximated at
the order `h_N` with the constants `interpBound` (`IsC2Form.exists_mem_whitney_le`). -/
def whitneyJackson : (whitneyFamily n).Jackson Unit where
  meshSize := meshSize
  meshSize_nonneg N := (meshSize_pos N).le
  tendsto_meshSize := tendsto_meshSize
  Reg _ := IsC2Form
  ord _ := 1
  B _ := interpBound n
  B_nonneg _ := interpBound_nonneg n
  jackson _ N _ _ _ hL hx := by
    rw [Real.rpow_one, ← mul_assoc]; exact hx.exists_mem_whitney_le hL N

/-- **The Jackson estimate of the Whitney forms with vanishing boundary DOFs**: `C²` forms
vanishing outside `Q` (`IsC2FormMin`) at the order `h_N`. -/
def whitneyJacksonMin : (whitneyFamilyMin n).Jackson Unit where
  meshSize := meshSize
  meshSize_nonneg N := (meshSize_pos N).le
  tendsto_meshSize := tendsto_meshSize
  Reg _ := IsC2FormMin
  ord _ := 1
  B _ := interpBound n
  B_nonneg _ := interpBound_nonneg n
  jackson _ N _ _ _ hL hx := by
    rw [Real.rpow_one, ← mul_assoc]; exact hx.exists_mem_whitneyMin_le hL N

variable {n}

/-! ### The semi-discrete Hodge wave equation with vanishing traces -/

/-- **The windows of the Whitney complexes with vanishing traces are approximating** for the
semi-discrete Hodge wave equation of every window `H̊Λᵃ(Q) → ⋯ → H̊Λ^{a+m-1}(Q)`. -/
theorem isApproximating_windowMin_whitney (a : ℤ) (m : ℕ) :
    HodgeWave.IsApproximating atTop fun N => ((whitneyMin n N).window a m).graphSub :=
  Subcomplex.isApproximating (dense_windowMin a m)

/-- **Convergence of the semi-discrete Hodge wave equation with vanishing traces** on the cube
meshes, for every window of `H̊Λ(Q)` and `D(L)` data, unconditionally
([QuennevilleBelair2015], Thm 4.14): the semi-discrete Whitney solutions in `V̊ₕ` with
`ξₕ(t₀) = Pₕ x` converge to `e^{(t - t₀) L} x` uniformly on `[t₀, t₁]`. -/
theorem exists_tendstoUniformlyOn_windowMin_whitney (a : ℤ) (m : ℕ) (t₀ t₁ : ℝ)
    (x : ((complexMin n).window a m).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → ((complexMin n).window a m).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((whitneyMin n N).window a m).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitneyMin n N).window a m).graphSub)
        (((complexMin n).window a m).totalD.toGraphSpace
          ⟨x, (((complexMin n).window a m).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => ((complexMin n).window a m).totalD.graphFst (ξh N t))
        (fun t => ((complexMin n).window a m).waveGroup.S (t - t₀) x) atTop (Set.Icc t₀ t₁) :=
  HilbertComplex.HodgeWave.exists_tendstoUniformlyOn_ellipticProjection _
    (isApproximating_windowMin_whitney a m) t₀ t₁ x

end Feec.Models.Cube.FEM

