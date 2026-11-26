module

public import Feec.Physics.EinsteinBianchi.BoundedConvergence
public import Feec.ForMathlib.Analysis.DiagonalChoice

/-!
# Every state is the limit of initial states of the scheme (6.5)

For the semi-discrete scheme (6.5) of [QuennevilleBelair2015], §6.3 on `Q = (0, ½)³`, every point
of the total space of the forms model is the limit, in energy, of initial states of solutions of
(6.5) without source (`exists_tendsto_dvec`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi.BoundedConvergence

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM
  Feec.EinsteinBianchi.MatrixModel Feec.EinsteinBianchi.BoundedFailure

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

theorem nonempty_discreteSolution {T : ℝ} (hT0 : 0 < T) (N : ℕ) :
    Nonempty (Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0)) := by
  obtain ⟨s, -⟩ := (cubeWave_exists_iff_compatible_u hT hB N hT0
    (continuousOn_cubeSource hT hB N (continuousOn_const (c := (0 : Wv W1)))) 0 0 0 0).2
    fun _ _ => inner_zero_left _
  exact ⟨s⟩

set_option maxHeartbeats 8000000 in
theorem eventually_exists_dvec_lt {T : ℝ} (hT0 : 0 < T) (x : WS) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
      ‖vecL x - dvec (cubeFEM hT hB N) sh 0‖ < ε := by
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / 2 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hA := formsShort.isSkewAdjoint_wave
  have hδ : 0 < η / (‖vecL‖ + 1) := by positivity
  obtain ⟨y, hy, hAy, hyd⟩ := hA.exists_mem_domain_sq_lt x hδ
  obtain ⟨Vy, -, -, hVy0, hVy, -, -⟩ := exists_orbit_sq hA hy hAy (Icc 0 T)
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  have k0 : ‖vecL x - vecL y‖ < η := by
    rw [← map_sub]
    have h1 := vecL.le_opNorm (x - y)
    have h2 : ‖vecL‖ * ‖x - y‖ ≤ ‖vecL‖ * (η / (‖vecL‖ + 1)) :=
      mul_le_mul_of_nonneg_left hyd.le (norm_nonneg _)
    have h3 : ‖vecL‖ * (η / (‖vecL‖ + 1)) < η := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg vecL]
    linarith
  filter_upwards [eventually_exists_dvec_le hT hB hT0 hVy hη] with N ⟨sh, hsh⟩
  refine ⟨sh, ?_⟩
  have k2 : ‖vecL y - dvec (cubeFEM hT hB N) sh 0‖ ≤ η := by
    rw [← hVy0, ← solutionOfStrong_vec_eq hVy h0T]
    exact hsh 0 h0T
  calc ‖vecL x - dvec (cubeFEM hT hB N) sh 0‖
      ≤ ‖vecL x - vecL y‖ + ‖vecL y - dvec (cubeFEM hT hB N) sh 0‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < η + η := add_lt_add_of_lt_of_le k0 k2
    _ = ε := by rw [hηdef]; ring

/-- For every point `x` of the total space and `T > 0`, some solutions of (6.5) on `[0, T]` with
source `0` have initial energy vectors converging to that of `x`. [QuennevilleBelair2015], §6.3 -/
theorem exists_tendsto_dvec {T : ℝ} (hT0 : 0 < T) (x : WS) :
    ∃ sh : ∀ N, Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
      Tendsto (fun N => ‖vecL x - dvec (cubeFEM hT hB N) (sh N) 0‖) atTop (𝓝 0) :=
  exists_tendsto_zero_of_forall_eventually_exists_lt (nonempty_discreteSolution hT hB hT0)
    (fun _ _ => norm_nonneg _) fun _ hε => eventually_exists_dvec_lt hT hB hT0 x hε

end Feec.EinsteinBianchi.BoundedConvergence
