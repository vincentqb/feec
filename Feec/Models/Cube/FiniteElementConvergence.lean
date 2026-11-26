module

public import Feec.Models.Cube.DeRhamIdentFEM
public import Feec.Models.Cube.WhitneyRate
public import Feec.Models.Cube.SmoothingEstimates
public import Feec.HilbertComplex.Approximation.StaticFEEC

/-!
# The Whitney finite element method on the cube as a conforming family

The Whitney complexes of the Freudenthal meshes of `Q = (0, ½)ⁿ` with the smoothed projections are
conforming families of `HΛ(Q)` and `H̊Λ(Q)` (`FEM.whitneyFamily`, `FEM.whitneyFamilyMin`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.HilbertComplex Filter Topology

variable {n : ℕ} [NeZero n]

/-! ### The Whitney forms as conforming families -/

variable {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ}

/-- **The conforming family of the smoothing estimates `hE`** ([AFW2010], §5.5). -/
def SmoothingEstimates.family (hE : SmoothingEstimates n p C) : ConformingFamily (complex n) ℕ :=
  .ofSmoothing atTop (whitney n) (fun N => smoothed n N (p N) (hE.isMaximal N))
    (by norm_num : (1 / 2 : ℝ) < 1) hE.close hE.bound tendsto_infDist_whitney

/-- **The conforming family of the smoothing estimates `hE`** with vanishing boundary DOFs. -/
def SmoothingEstimatesMin.family (hE : SmoothingEstimatesMin n p C) :
    ConformingFamily (complexMin n) ℕ :=
  .ofSmoothing atTop (whitneyMin n) (fun N => smoothedMin n N (p N) (hE.isMinimal N))
    (by norm_num : (1 / 2 : ℝ) < 1) hE.close hE.bound tendsto_infDist_whitneyMin

variable (n)

/-- **The Whitney forms of the Freudenthal meshes**, a conforming family of `HΛ(Q)`. -/
def whitneyFamily : ConformingFamily (complex n) ℕ :=
  (smoothingEstimates_exists (n := n)).choose_spec.choose_spec.family

/-- **The Whitney forms with vanishing boundary DOFs**, a conforming family of `H̊Λ(Q)`. -/
def whitneyFamilyMin : ConformingFamily (complexMin n) ℕ :=
  (smoothingEstimatesMin_exists (n := n)).choose_spec.choose_spec.family

@[simp] theorem whitneyFamily_V : (whitneyFamily n).V = whitney n := rfl

@[simp] theorem whitneyFamilyMin_V : (whitneyFamilyMin n).V = whitneyMin n := rfl

/-- **The Jackson estimate of the Whitney forms**, of order `h_N` on `C²` forms. -/
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

/-- **The Jackson estimate of the Whitney forms with vanishing boundary DOFs**, of order `h_N`. -/
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

theorem isApproximating_windowMin_whitney (a : ℤ) (m : ℕ) :
    HodgeWave.IsApproximating atTop fun N => ((whitneyMin n N).window a m).graphSub :=
  Subcomplex.isApproximating (dense_windowMin a m)

/-- **Convergence of the semi-discrete Hodge wave equation with vanishing traces** for every
window of `H̊Λ(Q)` and `D(L)` data ([QuennevilleBelair2015], Thm 4.14). -/
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

