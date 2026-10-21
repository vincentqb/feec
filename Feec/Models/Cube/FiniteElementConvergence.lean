module

public import Feec.Models.Cube.DeRhamIdentRate
public import Feec.Models.Cube.SmoothingEstimates

/-!
# Convergence of the Whitney finite element method on the cube, with no hypotheses

On the cube `Q = (0, ½)ⁿ` with the level-`(N + 1)` Freudenthal meshes (mesh size
`h_N = FEM.meshSize N = 1 / (2 (N + 1))`) and their lowest-order Whitney complexes
`FEM.whitney n N ⊆ HΛ(Q)` and `FEM.whitneyMin n N ⊆ H̊Λ(Q)` (vanishing boundary DOFs), the three
hypotheses of `Feec.Models.Cube.FiniteElementMethod` are theorems:

* the smoothing estimates `FEM.SmoothingEstimates`, `FEM.SmoothingEstimatesMin`
  (`FEM.smoothingEstimates_exists`, `FEM.smoothingEstimatesMin_exists`,
  `Feec.Models.Cube.SmoothingEstimates`);
* the Poincaré inequalities of `HΛ(Q)` and `H̊Λ(Q)` with `c_P = (2π)⁻¹`
  (`FEM.norm_le_of_mem_orthogonal_cycles`, `FEM.norm_le_of_mem_orthogonal_cycles_min`,
  `Feec.Models.Cube.DeRhamIdentFEM`);
* the Whitney interpolation error for `C²` forms (`Feec.Models.Cube.WhitneyRate`).

Chaining them, this module states the finite element results with no hypothesis beyond the data
of the problem, for both families:

* **uniformly bounded smoothed cochain projections with vanishing harmonic gap**: `‖π_N‖ ≤ 2C`
  in `L²` and every graph norm, and `sup_{q ∈ ℌʲ, ‖q‖ ≤ 1} ‖q - π_N q‖ → 0` in every degree
  (`smoothedProjection_uniform`, `smoothedProjection_uniform_min`);
* **uniform discrete Poincaré inequality** (`discretePoincare`, `discretePoincare_min`);
* **uniform well-posedness and stability of the discrete mixed Hodge Laplacian**: for every `N`
  and every `fₕ ∈ Vₕʲ` the discrete mixed problem has a unique solution, bounded by `C ‖fₕ‖` with
  `C` independent of `N` (`mixed_wellPosed`, `mixed_wellPosed_min`);
* **quasi-optimality**: error `≤ K (E(σ) + E(u) + E(q) + μ_j(N) E(P_𝔅 u))` with `μ_j(N) → 0`
  (`mixed_quasiOptimal`, `mixed_quasiOptimal_min`);
* **`O(h)` convergence** of the discrete mixed solution to the solution `(σ, u, q)` of the mixed
  Hodge–Laplace problem when `σ`, `u`, its boundary part and `q` are `C²` with bound `L`
  (vanishing outside `Q` for `H̊Λ(Q)`): error `≤ K L h_N` with `K` depending only on `n` and the
  degrees (`mixed_rate_smooth`, `mixed_rate_smooth_min`);
* **the semi-discrete Hodge wave equation** on every window: convergence for `D(L)` data
  (`exists_tendstoUniformlyOn_window_whitney` in `Feec.Models.Cube.WhitneyApprox`;
  `exists_tendstoUniformlyOn_windowMin_whitney` here) and the `O(h)` rate for `C²` solutions
  (`norm_sub_le_meshSize_window_smooth`, `norm_sub_le_meshSize_windowMin_smooth` in
  `Feec.Models.Cube.WhitneyRate`; these need no smoothed projection). Maxwell's equations (PMC and
  PEC) are the instances of `Feec.Physics.Maxwell.CubeFEM`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (discrete Poincaré inequality, Thm 3.6), Thm 3.8 (stability), Thm 3.9
  (quasi-optimality), §5.4 (smoothed projections)
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

/-! ### The maximal family `HΛ(Q)` -/

/-- **Uniform discrete Poincaré inequality** on the Whitney complexes of the Freudenthal meshes
of the cube ([AFW2010], Thm 3.6), unconditionally: `‖x‖ ≤ c ‖d x‖` for `x ∈ Vₕⁱ ⊥ 𝔷ₕⁱ`, with
`c` independent of the mesh. -/
theorem discretePoincare : ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
    {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (whitney n N).V i),
    (∀ y ∈ (whitney n N).cyclesW i, inner ℝ y x = 0) →
      ‖x‖ ≤ c * ‖(complex n).d i j ⟨x, (whitney n N).le_domain i j hx⟩‖ := by
  obtain ⟨p, C, hE⟩ := smoothingEstimates_exists (n := n)
  exact ⟨2 * C * (2 * Real.pi)⁻¹, fun hij N _ hx hxo =>
    hE.norm_le_of_forall_inner_eq_zero' hij N hx hxo⟩

/-- **Uniform well-posedness and stability of the discrete mixed Hodge Laplacian** on the
Whitney complexes of the cube ([AFW2010], Thm 3.8), unconditionally: for every mesh and every
`fₕ ∈ Vₕʲ` the discrete mixed problem has a unique solution `xₕ`, and `‖xₕ‖ ≤ C ‖fₕ‖` with `C`
independent of the mesh. -/
theorem mixed_wellPosed : ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j →
    (ComplexShape.up ℤ).Rel j k → ∀ (N : ℕ) (f : (whitney n N).V j),
    (∃! x, (whitney n N).toHilbertComplex.mixedForm i j k x =
      (whitney n N).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (whitney n N).toHilbertComplex.MixedSpace i j,
      (whitney n N).toHilbertComplex.mixedForm i j k x =
        (whitney n N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  -- `obtain` on the existential times out here in `isDefEq`; eliminate it explicitly
  refine (smoothingEstimates_exists (n := n)).elim fun p hp => hp.elim fun C hE => ?_
  refine ⟨16 * (2 * C * 1) ^ 2, ?_⟩
  intro i j k hij hjk N f
  constructor
  · exact hE.existsUnique_mixed' hij hjk N f
  · intro x hx
    exact hE.norm_le_of_mixed' hij hjk N hx

/-- **`O(h)` convergence of the Whitney finite element method for the mixed Hodge Laplacian on
the cube** ([AFW2010], Thm 3.9; [Arnold2018], Ch. 7), unconditionally: if the solution
`(σ, u, q)` of the mixed problem with data `f`, the boundary part of `u`, and `q` are `C²` with
bound `L`, the discrete mixed solution on the level-`(N + 1)` Freudenthal mesh satisfies
`‖σ - σₕ‖ + ‖u - uₕ‖ + ‖q - qₕ‖ ≤ K L h_N`, with `K` depending only on `n` and the degrees. -/
theorem mixed_rate_smooth {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) : ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)}
    {σ : (complex n).domainSpace i} {u : (complex n).domainSpace j} {q : (complex n).harmonic j},
    (complex n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsC2Form i L ((complex n).domainIncl i σ) →
    IsC2Form j L ((complex n).domainIncl j u) →
    IsC2Form j L ((complex n).domainIncl j
      ((complex n).boundaryPart j ((complex n).domainIncl j u))) →
    IsC2Form j L (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N := by
  obtain ⟨p, C, hE⟩ := smoothingEstimates_exists (n := n)
  refine ⟨(1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
    ((1 + 2 * C) * (interpBound n i + interpBound n j)), fun hs L hL0 hσ hu hB hq N => ?_⟩
  refine (hE.norm_sub_le_meshSize_smooth' hij hjk hs hL0 hσ hu hB hq N).trans_eq ?_
  ring

/-- **Uniformly bounded smoothed cochain projections with vanishing harmonic gap** on the Whitney
complexes of the cube ([AFW2010], §5.4, Thm 3.9), unconditionally: for the smoothed projections
`π_N = J_N⁻¹ Q_N` of some admissible smoothing parameters (`SmoothingEstimates.proj`), `‖π_N‖ ≤ 2C`
in `L²` and in every graph norm, uniformly in `N`, and the harmonic gap
`sup_{q ∈ ℌʲ, ‖q‖ ≤ 1} ‖q - π_N q‖` tends to `0` in every degree. -/
theorem smoothedProjection_uniform : ∃ (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ)
    (hE : SmoothingEstimates n p C),
    (∀ N i x, ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖) ∧ (∀ N i j, (hE.proj N).IsGraphBounded i j (2 * C)) ∧
    ∀ j, Tendsto (fun N => (hE.proj N).harmonicGap j) atTop (𝓝 0) := by
  obtain ⟨p, C, hE⟩ := smoothingEstimates_exists (n := n)
  exact ⟨p, C, hE, hE.norm_proj_le, hE.isGraphBounded_proj,
    fun _ => hE.tendsto_harmonicGap_whitney⟩

/-- **Quasi-optimality of the Whitney method for the mixed Hodge Laplacian on the cube**
([AFW2010], Thm 3.9), unconditionally: there are a constant `K` and weights `μ_j(N) → 0` (the
harmonic gaps of the smoothed projections) such that for every solution `(σ, u, q)` of the mixed
problem and every mesh,
`‖σ - σₕ‖ + ‖u - uₕ‖ + ‖q - qₕ‖ ≤ K (E(σ) + E(u) + E(q) + μ_j(N) E(P_𝔅 u))`, where `E` is the
graph-norm distance to the Whitney spaces (`L²` distance to `ℌₕ` for `q`). -/
theorem mixed_quasiOptimal : ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j},
    (complex n).IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((whitney n N).domainSub i) +
        Metric.infDist u ((whitney n N).domainSub j) +
        Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitney n N).harmonicW j) +
        μ j N * Metric.infDist ((complex n).boundaryPart j ((complex n).domainIncl j u))
          ((whitney n N).domainSub j)) := by
  refine (smoothingEstimates_exists (n := n)).elim fun p hp => hp.elim fun C hE => ?_
  exact ⟨(1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C),
    fun j N => (hE.proj N).harmonicGap j, fun _ => hE.tendsto_harmonicGap_whitney,
    fun hij hjk _ _ _ _ hs N => hE.norm_sub_le_infDist' hij hjk hs N⟩

/-! ### The minimal family `H̊Λ(Q)` -/

/-- **Uniform discrete Poincaré inequality** on the Whitney complexes with vanishing boundary
DOFs ([AFW2010], Thm 3.6), unconditionally. -/
theorem discretePoincare_min : ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
    {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (whitneyMin n N).V i),
    (∀ y ∈ (whitneyMin n N).cyclesW i, inner ℝ y x = 0) →
      ‖x‖ ≤ c * ‖(complexMin n).d i j ⟨x, (whitneyMin n N).le_domain i j hx⟩‖ := by
  obtain ⟨p, C, hE⟩ := smoothingEstimatesMin_exists (n := n)
  exact ⟨2 * C * (2 * Real.pi)⁻¹, fun hij N _ hx hxo =>
    hE.norm_le_of_forall_inner_eq_zero' hij N hx hxo⟩

/-- **Uniform well-posedness and stability of the discrete mixed Hodge Laplacian with vanishing
traces** on the cube ([AFW2010], Thm 3.8), unconditionally. -/
theorem mixed_wellPosed_min : ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j →
    (ComplexShape.up ℤ).Rel j k → ∀ (N : ℕ) (f : (whitneyMin n N).V j),
    (∃! x, (whitneyMin n N).toHilbertComplex.mixedForm i j k x =
      (whitneyMin n N).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (whitneyMin n N).toHilbertComplex.MixedSpace i j,
      (whitneyMin n N).toHilbertComplex.mixedForm i j k x =
        (whitneyMin n N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  -- `obtain` on the existential times out here in `isDefEq`; eliminate it explicitly
  refine (smoothingEstimatesMin_exists (n := n)).elim fun p hp => hp.elim fun C hE => ?_
  refine ⟨16 * (2 * C * 1) ^ 2, ?_⟩
  intro i j k hij hjk N f
  constructor
  · exact hE.existsUnique_mixed' hij hjk N f
  · intro x hx
    exact hE.norm_le_of_mixed' hij hjk N hx

/-- **`O(h)` convergence of the Whitney finite element method with vanishing traces** on the
cube ([AFW2010], Thm 3.9; [Arnold2018], Ch. 7), unconditionally: for a solution of the mixed
problem on `H̊Λ(Q)` whose components are `C²` forms vanishing outside `Q` with bound `L`, the
error of the discrete mixed solution is `≤ K L h_N`. -/
theorem mixed_rate_smooth_min {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) : ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)}
    {σ : (complexMin n).domainSpace i} {u : (complexMin n).domainSpace j}
    {q : (complexMin n).harmonic j},
    (complexMin n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsC2FormMin i L ((complexMin n).domainIncl i σ) →
    IsC2FormMin j L ((complexMin n).domainIncl j u) →
    IsC2FormMin j L ((complexMin n).domainIncl j
      ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))) →
    IsC2FormMin j L (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (whitneyMin n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).fst‖ +
        ‖u - (whitneyMin n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin n N) hij hjk f).snd.snd :
            (whitneyMin n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N := by
  obtain ⟨p, C, hE⟩ := smoothingEstimatesMin_exists (n := n)
  refine ⟨(1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
    (2 * ((1 + 2 * C) * (interpBound n i + interpBound n j))),
    fun hs L hL0 hσ hu hB hq N => ?_⟩
  refine (hE.norm_sub_le_meshSize_smooth' hij hjk hs hL0 hσ hu hB hq N).trans_eq ?_
  ring

/-- **Uniformly bounded smoothed cochain projections onto the Whitney complexes with vanishing
boundary DOFs, with vanishing harmonic gap** ([AFW2010], §5.4), unconditionally: as
`smoothedProjection_uniform`, for `H̊Λ(Q)` and the projections `π̊_N = J_N⁻¹ Q̊_N`. -/
theorem smoothedProjection_uniform_min : ∃ (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ)
    (hE : SmoothingEstimatesMin n p C),
    (∀ N i x, ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖) ∧ (∀ N i j, (hE.proj N).IsGraphBounded i j (2 * C)) ∧
    ∀ j, Tendsto (fun N => (hE.proj N).harmonicGap j) atTop (𝓝 0) := by
  obtain ⟨p, C, hE⟩ := smoothingEstimatesMin_exists (n := n)
  exact ⟨p, C, hE, hE.norm_proj_le, hE.isGraphBounded_proj,
    fun _ => hE.tendsto_harmonicGap_whitney⟩

/-- **Quasi-optimality of the Whitney method with vanishing traces** ([AFW2010], Thm 3.9),
unconditionally: as `mixed_quasiOptimal`, for the mixed problem on `H̊Λ(Q)` and the spaces
`V̊ₕ`. -/
theorem mixed_quasiOptimal_min : ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j},
    (complexMin n).IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (whitneyMin n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).fst‖ +
        ‖u - (whitneyMin n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin n N) hij hjk f).snd.snd :
            (whitneyMin n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((whitneyMin n N).domainSub i) +
        Metric.infDist u ((whitneyMin n N).domainSub j) +
        Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitneyMin n N).harmonicW j) +
        μ j N * Metric.infDist ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))
          ((whitneyMin n N).domainSub j)) := by
  refine (smoothingEstimatesMin_exists (n := n)).elim fun p hp => hp.elim fun C hE => ?_
  exact ⟨(1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C),
    fun j N => (hE.proj N).harmonicGap j, fun _ => hE.tendsto_harmonicGap_whitney,
    fun hij hjk _ _ _ _ hs N => (hE.proj N).norm_sub_le_infDist_harmonicGap hij hjk
      hE.one_le_two_mul (norm_le_of_mem_orthogonal_cycles_min hij)
      (norm_le_of_mem_orthogonal_cycles_min hjk) (hE.isGraphBounded_proj N _ _)
      (hE.isGraphBounded_proj N _ _) hs⟩

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
