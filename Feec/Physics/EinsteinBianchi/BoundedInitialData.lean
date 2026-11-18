module

public import Feec.Physics.EinsteinBianchi.BoundedConvergence
public import Feec.ForMathlib.Analysis.DiagonalChoice

/-!
# Every state is the limit of initial states of the scheme (6.5)

[QuennevilleBelair2015], §6.3: the semi-discrete scheme (6.5) on `Q = (0, ½)³` with the elements
of Table 6.1 and the thesis' boundary conditions (`Feec.Models.Cube.WeakSymmetry.cubeWave`). Its
initial values are constrained: every solution has `uₕ(0) ⊥ d̃ψ` for `ψ ∈ ker S₀,ₕ`
(`Feec.BGG.DiscreteSolution.hidden_constraint`), and only such data have solutions
(`Feec.Models.Cube.WeakSymmetry.cubeWave_exists_iff_compatible_u`). The constraint does not
obstruct approximation: every point of the total space of the forms model is the limit, in
energy, of the initial states of solutions of (6.5) without source (`exists_tendsto_dvec`). So
the convergence of `Feec.EinsteinBianchi.BoundedConvergence.tendsto_of_isStrongSolution`, for
every family of solutions whose initial states converge, is a statement about every datum of
`D(L)`.

The proof approximates the point by `y ∈ D(L²)`
(`LinearPMap.IsSkewAdjoint.exists_mem_domain_sq_lt`), whose orbit is a classical solution of
(6.2) (`exactOfStrong`) approximated at all large `N` by the solution of (6.5) from its elliptic
projection (`Feec.Models.Cube.WeakSymmetry.cubeWave_converges`), and chooses the solutions level
by level (`exists_tendsto_zero_of_forall_eventually_exists_lt`).

## Main results

* `nonempty_discreteSolution`: (6.5) has solutions at every level (from the zero data).
* `eventually_exists_dvec_lt`: at all large levels some solution starts within `ε` of the point.
* **`exists_tendsto_dvec`**: solutions of (6.5) whose initial states converge to the point.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2 ((6.4)), §6.3 ((6.5), Table 6.1)

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

/-- **(6.5) has solutions on `[0, T]` at every level** (source `0`): the zero data satisfy the
compatibility condition of `cubeWave_exists_iff_compatible_u`. -/
theorem nonempty_discreteSolution {T : ℝ} (hT0 : 0 < T) (N : ℕ) :
    Nonempty (Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0)) := by
  obtain ⟨s, -⟩ := (cubeWave_exists_iff_compatible_u hT hB N hT0
    (continuousOn_cubeSource hT hB N (continuousOn_const (c := (0 : Wv W1)))) 0 0 0 0).2
    fun _ _ => inner_zero_left _
  exact ⟨s⟩

set_option maxHeartbeats 8000000 in
/-- **At all large levels, (6.5) has a solution starting within `ε` of a point** (source `0`, in
energy): approximate the point by `y ∈ D(L²)`; the solution of (6.5) from the elliptic projection
of `y` approximates the orbit of `y` (`cubeWave_converges`), in particular at `t = 0`. -/
theorem eventually_exists_dvec_lt {T : ℝ} (hT0 : 0 < T) (x : WS) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
      ‖vecL x - dvec (cubeFEM hT hB N) sh 0‖ < ε := by
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / 2 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hA := formsShort.isSkewAdjoint_wave
  have hδ : 0 < η / (‖vecL‖ + 1) := by positivity
  obtain ⟨y, hy, hAy, hyd⟩ := hA.exists_mem_domain_sq_lt x hδ
  obtain ⟨Vy, hd, hd', hVy0, hVy, hWy', hXy'⟩ := exists_orbit_sq hA hy hAy (Icc 0 T)
  have hWy : Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 fun t => waveOf (Vy t) :=
    hWy'.congr (fun t _ => (waveOf_eq (hd t)).symm) fun _ _ => rfl
  have hXy : ContinuousOn (fun t => waveOf (waveOf (Vy t))) (Icc 0 T) := by
    refine hXy'.continuousOn.congr fun t _ => ?_
    change waveOf (waveOf (Vy t)) = formsShort.wave ⟨formsShort.wave ⟨Vy t, hd t⟩, hd' t⟩
    rw [waveOf_eq (hd t), waveOf_eq (hd' t)]
  obtain ⟨sy, hsy⟩ : ∃ s, s = exactOfStrong hVy hWy hXy := ⟨_, rfl⟩
  have hrep : ∀ t ∈ Icc 0 T, IsMultRep (sy.ℓ t) (aOf (Vy t)) (bOf (Vy t)) := by
    rw [hsy]; exact exactOfStrong_isMultRep hVy hWy hXy
  have hrep' : ∀ t ∈ Icc 0 T,
      IsMultRep (sy.ℓ' t) (aOf (waveOf (Vy t))) (bOf (waveOf (Vy t))) := by
    rw [hsy]; exact exactOfStrong_isMultRep' hVy hWy hXy
  have conv := cubeWave_converges hT hB hT0 (f := 0) continuousOn_const sy
    (a := fun t => aOf (Vy t)) (b := fun t => bOf (Vy t))
    (a' := fun t => aOf (waveOf (Vy t))) (b' := fun t => bOf (waveOf (Vy t)))
    (negComp0L.continuous.comp_continuousOn hWy.continuousOn)
    (comp1L.continuous.comp_continuousOn hVy.continuousOn)
    (negComp0L.continuous.comp_continuousOn hXy)
    (comp1L.continuous.comp_continuousOn hWy.continuousOn)
    hrep hrep' hη
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  have e0 : (exactWave_toSolution sy).vec 0 = vecL y := by
    rw [hsy, exactOfStrong_vec hVy hWy hXy h0T, solutionOfStrong_vec_eq hVy h0T, hVy0]
  have k0 : ‖vecL x - vecL y‖ < η := by
    rw [← map_sub]
    have h1 := vecL.le_opNorm (x - y)
    have h2 : ‖vecL‖ * ‖x - y‖ ≤ ‖vecL‖ * (η / (‖vecL‖ + 1)) :=
      mul_le_mul_of_nonneg_left hyd.le (norm_nonneg _)
    have h3 : ‖vecL‖ * (η / (‖vecL‖ + 1)) < η := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg vecL]
    linarith
  filter_upwards [conv] with N hN
  obtain ⟨shy, -, hshy⟩ := hN
  refine ⟨shy, ?_⟩
  have k2 : ‖vecL y - dvec (cubeFEM hT hB N) shy 0‖ ≤ η := by
    rw [← e0, norm_vec_sub_dvec (cubeFEM hT hB N) sy shy 0]
    exact hshy 0 h0T
  calc ‖vecL x - dvec (cubeFEM hT hB N) shy 0‖
      ≤ ‖vecL x - vecL y‖ + ‖vecL y - dvec (cubeFEM hT hB N) shy 0‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < η + η := add_lt_add_of_lt_of_le k0 k2
    _ = ε := by rw [hηdef]; ring

/-- **Every state is the limit of initial states of (6.5)** ([QuennevilleBelair2015], §6.3,
(6.5), Table 6.1, thesis' boundary conditions; no hypothesis): for every point `x` of the total
space of the forms model and every `T > 0`, some solutions of (6.5) on `[0, T]` (source `0`) have
initial energy vectors converging to that of `x`, although their initial values `uₕ(0)` are
constrained (`Feec.BGG.DiscreteSolution.hidden_constraint`). With `tendsto_of_isStrongSolution`,
(6.5) converges along them from every datum of `D(L)`. -/
theorem exists_tendsto_dvec {T : ℝ} (hT0 : 0 < T) (x : WS) :
    ∃ sh : ∀ N, Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
      Tendsto (fun N => ‖vecL x - dvec (cubeFEM hT hB N) (sh N) 0‖) atTop (𝓝 0) :=
  exists_tendsto_zero_of_forall_eventually_exists_lt (nonempty_discreteSolution hT hB hT0)
    (fun _ _ => norm_nonneg _) fun _ hε => eventually_exists_dvec_lt hT hB hT0 x hε

end Feec.EinsteinBianchi.BoundedConvergence
