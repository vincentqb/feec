module

public import Feec.Models.Cube.WhitneyApprox

/-!
# `O(h)` convergence of the Whitney finite element method for smooth solutions

On the Freudenthal meshes of `Q = (0, ½)ⁿ`, the rate theorems of
`Feec.Models.Cube.FiniteElementMethod` take the approximation rates of the exact solution as
hypotheses (`hσ`, `hu`, `hq`, `hB` of `FEM.SmoothingEstimates.norm_sub_le_meshSize`, `happ` of
`FEM.norm_sub_le_meshSize_window`). This module proves them for smooth solutions, from the
interpolation error of the Whitney interpolant (`FEM.exists_mem_whitney_le`, [Arnold2018], Ch. 7).

* `FEM.IsC2Form j L x`: `x ∈ L²(Q; Λʲ)` is (the restriction of) a `C²` `j`-form `w` with
  `‖Dw‖ ≤ L` and `‖D dw‖ ≤ L` on `cl Q`; trivially true in negative degrees, where
  `L²(Q; Λʲ) = 0` (so the scalar Neumann problem `(i, j, k) = (-1, 0, 1)` and windows with `a < 0`
  are covered).
* **Degreewise rate**: such an `x` has `v ∈ Vₕʲ` with `‖x - v‖ ≤ B_j L h_N` and
  `‖d (x - v)‖ ≤ B_j L h_N` (`IsC2Form.exists_mem_whitney_le`), and
  `dist_V(σ, Vₕʲ) ≤ B_j L h_N` in the graph norm (`IsC2Form.infDist_domainSub_whitney_le`),
  `B_j = interpBound n j = A_j + A_{j+1}` independent of `N`.
* **Hodge–Laplace, mixed form** ([AFW2010], Thm 3.9): under the smoothing estimates, if `σ`, `u`,
  `P_𝔅 u` and the harmonic part `p` are `C²` forms, the discrete mixed solutions converge at rate
  `h_N` (`SmoothingEstimates.norm_sub_le_meshSize_smooth`). The harmonic term needs no separate
  estimate: `dist(p, ℌₕ) ≤ (1 + 2C) dist_V(p, Vₕ)` (`CochainProjection.infDist_harmonicW_le`), and
  `p` is a `C²` cycle.
* **Hodge wave equation** ([QuennevilleBelair2015], Thm 4.14): if every component of `ξ(s)` and
  `ξ'(s)` is a `C²` form with bound `L` on `[t₀, t₁]`, the semi-discrete Whitney solutions converge
  at rate `h_N` (`norm_sub_le_meshSize_window_smooth`), through the degreewise-to-total lemma
  `Feec.HilbertComplex.Subcomplex.exists_mem_graphSub_le`.
* **Vanishing traces** (`H̊Λ(Q)`, Whitney spaces `V̊ₕ` with vanishing boundary DOFs): the same
  three statements for `C²` forms vanishing outside `Q` (`FEM.IsC2FormMin`):
  `SmoothingEstimatesMin.norm_sub_le_meshSize` (generic, as for `HΛ(Q)`),
  `SmoothingEstimatesMin.norm_sub_le_meshSize_smooth` and
  `norm_sub_le_meshSize_windowMin_smooth`. The `d_min` of such a form is computed by
  `complexMin_d_formL2` (`d_min ≤ d_max`). In the top degree `j = n` the harmonic forms of
  `H̊Λⁿ(Q)` are the constants, which do not vanish outside `Q`; there `hq` of the smooth mixed
  statement holds only for `p = 0`, and the generic statement with an explicit `dist(p, ℌ̊ₕ)` bound is
  the one to use.

## Main definitions

* `Feec.Models.Cube.FEM.IsC2Form`, `Feec.Models.Cube.FEM.IsC2FormMin`,
  `Feec.Models.Cube.FEM.interpBound`

## Main results

* `Feec.Models.Cube.FEM.SmoothingEstimates.norm_sub_le_meshSize_smooth`
* `Feec.Models.Cube.FEM.norm_sub_le_meshSize_window_smooth`
* `Feec.Models.Cube.FEM.SmoothingEstimatesMin.norm_sub_le_meshSize_smooth`
* `Feec.Models.Cube.FEM.norm_sub_le_meshSize_windowMin_smooth`

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (approximation
  estimates, rates for smooth solutions)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.9 (quasi-optimality of the mixed method)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.14 (convergence of the semi-discrete Hodge wave equation)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.ExteriorFibre

variable {n : ℕ}

/-- `x ∈ L²(Q; Λʲ)` is a `C²` form of degree `j` whose derivative and the derivative of its
exterior derivative are bounded by `L` on `cl Q`. In a negative degree `L²(Q; Λʲ) = 0` and the
condition holds trivially, so that the rate theorems cover the windows and Hodge Laplacians that
reach below degree `0` (e.g. the scalar Neumann problem `(i, j, k) = (-1, 0, 1)`). -/
def IsC2Form (j : ℤ) (L : ℝ) (x : L2F ℝ (cubeDomain n) (formIdx n j)) : Prop :=
  j < 0 ∨ ∃ k : ℕ, (k : ℤ) = j ∧ ∃ w : FormField n, ∃ hw : ContDiff ℝ 2 w, (∀ y, IsDeg k (w y)) ∧
    (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L) ∧
    (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ (extDeriv w) y‖ ≤ L) ∧
    x = formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j ⟨w, hw.continuous⟩

variable (n) in
/-- The constant `B_j = A_j + A_{j+1}` of the graph-norm interpolation error in degree `j`. -/
def interpBound (j : ℤ) : ℝ := interpConst n j.toNat + interpConst n (j.toNat + 1)

variable (n) in
theorem interpBound_nonneg (j : ℤ) : 0 ≤ interpBound n j :=
  add_nonneg (interpConst_nonneg n _) (interpConst_nonneg n _)

/-- `IsC2Form` is monotone in the bound. -/
theorem IsC2Form.mono {j : ℤ} {L L' : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)}
    (hx : IsC2Form j L x) (hLL' : L ≤ L') : IsC2Form j L' x := by
  rcases hx with hj | ⟨k, hk, w, hw, hdeg, hL, hL', he⟩
  · exact Or.inl hj
  · exact Or.inr ⟨k, hk, w, hw, hdeg, fun y hy => (hL y hy).trans hLL',
      fun y hy => (hL' y hy).trans hLL', he⟩

variable [NeZero n]

/-- **Degreewise interpolation error for `C²` forms**: `‖x - v‖ ≤ B_j L h_N` and
`‖d (x - v)‖ ≤ B_j L h_N` for the Whitney interpolant `v ∈ Vₕʲ`. -/
theorem IsC2Form.exists_mem_whitney_le {j : ℤ} {L : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)}
    (hx : IsC2Form j L x) (hL0 : 0 ≤ L) (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (whitney n N).V j, ‖x - v‖ ≤ interpBound n j * L * meshSize N ∧
      ∀ j' (hxj : x ∈ ((complex n).d j j').domain),
        ‖(complex n).d j j' ⟨x - v, Submodule.sub_mem _ hxj ((whitney n N).le_domain j j' hv)⟩‖ ≤
          interpBound n j * L * meshSize N := by
  have hB0 := mul_nonneg (mul_nonneg (interpBound_nonneg n j) hL0) (meshSize_pos N).le
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, hL, hL', rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    refine ⟨0, Submodule.zero_mem _, ?_, fun j' hxj => ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hB0
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := FEM.exists_mem_whitney_le N k hw hL0 hL0 hL hL'
  obtain ⟨hdom, hval⟩ := formL2_mem_domain k (hw.of_le (by norm_num)) hdeg
  have hh := (meshSize_pos N).le
  have hA0 := mul_nonneg (interpConst_nonneg n k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (interpConst_nonneg n (k + 1)) (mul_nonneg hh hL0)
  have e : interpBound n k * L * meshSize N =
      interpConst n k * (meshSize N * L) + interpConst n (k + 1) * (meshSize N * L) := by
    simp only [interpBound, Int.toNat_natCast]; ring
  refine ⟨v, hv, ?_, fun j' hxj => ?_⟩
  · rw [e]; linarith
  by_cases hj : (k : ℤ) + 1 = j'
  · subst hj
    have e' : (complex n).d k (k + 1)
        ⟨_ - v, Submodule.sub_mem _ hxj ((whitney n N).le_domain k (k + 1) hv)⟩ =
        (complex n).d k (k + 1) ⟨_, hdom⟩ - (complex n).d k (k + 1) ⟨v, hdv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e', hval, e]
    linarith
  · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]
    exact mul_nonneg (mul_nonneg (interpBound_nonneg n _) hL0) hh

/-- **Graph-norm distance of a `C²` form to the Whitney space**: `dist_V(σ, Vₕʲ) ≤ B_j L h_N`. -/
theorem IsC2Form.infDist_domainSub_whitney_le {j : ℤ} {L : ℝ} {σ : (complex n).domainSpace j}
    (hσ : IsC2Form j L ((complex n).domainIncl j σ)) (hL0 : 0 ≤ L) (N : ℕ) :
    Metric.infDist σ ((whitney n N).domainSub j) ≤ interpBound n j * L * meshSize N := by
  rcases hσ with hj | ⟨k, rfl, w, hw, hdeg, hL, hL', he⟩
  · have hB0 := mul_nonneg (mul_nonneg (interpBound_nonneg n j) hL0) (meshSize_pos N).le
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    refine (Subcomplex.infDist_domainSub_le (S := whitney n N)
      (rfl : (ComplexShape.up ℤ).Rel (Int.negSucc k) (Int.negSucc k + 1)) σ
      (Submodule.zero_mem _)).trans ?_
    rw [Subsingleton.elim (_ - 0) 0, norm_zero, ← LinearPMap.map_sub,
      Subsingleton.elim (_ - _ : ((complex n).d _ _).domain) 0, LinearPMap.map_zero, norm_zero,
      add_zero]
    exact hB0
  refine (FEM.infDist_domainSub_whitney_le N k hw hdeg hL0 hL0 hL hL' σ he).trans (le_of_eq ?_)
  simp only [interpBound, Int.toNat_natCast]; ring

/-- **`O(h)` convergence of the mixed method for smooth solutions** ([AFW2010], Thm 3.9;
[Arnold2018], Ch. 7): under the smoothing estimates and the Poincaré inequalities, if `σ`, `u`,
`P_𝔅 u` and the harmonic part `p` of the solution of the mixed Hodge–Laplace problem are `C²`
forms with bound `L`, then the discrete Whitney solutions satisfy
`‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖ ≤ C' K h_N`, with `C'` the constant of `norm_sub_le_meshSize`
and `K = (1 + 2C)(B_i + B_j) L`, both independent of `N`. All four approximation hypotheses of
`norm_sub_le_meshSize` are discharged; the harmonic one by
`CochainProjection.infDist_harmonicW_le`. -/
theorem SmoothingEstimates.norm_sub_le_meshSize_smooth {p : ℕ → SmoothingParam (Fin n → ℝ)}
    {C : ℝ} (hE : SmoothingEstimates n p C) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ}
    (hPi : ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖)
    (hPj : ∀ z : ((complex n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complex n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complex n).d j k z‖)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) {L : ℝ} (hL0 : 0 ≤ L)
    (hσ : IsC2Form i L ((complex n).domainIncl i σ))
    (hu : IsC2Form j L ((complex n).domainIncl j u))
    (hB : IsC2Form j L ((complex n).domainIncl j
      ((complex n).boundaryPart j ((complex n).domainIncl j u))))
    (hq : IsC2Form j L (q : L2F ℝ (cubeDomain n) (formIdx n j))) (N : ℕ) :
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
        ((1 + 2 * C) * (interpBound n i + interpBound n j) * L) * meshSize N := by
  have hC := hE.two_mul_nonneg
  have hh := (meshSize_pos N).le
  have hBi := interpBound_nonneg n i
  have hBj := interpBound_nonneg n j
  have hiL := mul_nonneg (mul_nonneg hBi hL0) hh
  have hjL := mul_nonneg (mul_nonneg hBj hL0) hh
  have hK : (1 + 2 * C) * (interpBound n i + interpBound n j) * L * meshSize N =
      (1 + 2 * C) * (interpBound n i * L * meshSize N) +
        (1 + 2 * C) * (interpBound n j * L * meshSize N) := by ring
  have hi : interpBound n i * L * meshSize N ≤
      (1 + 2 * C) * (interpBound n i + interpBound n j) * L * meshSize N := by
    rw [hK]; nlinarith
  have hj : interpBound n j * L * meshSize N ≤
      (1 + 2 * C) * (interpBound n i + interpBound n j) * L * meshSize N := by
    rw [hK]; nlinarith
  have hq' : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j))
      ((whitney n N).harmonicW j) ≤
      (1 + 2 * C) * (interpBound n i + interpBound n j) * L * meshSize N := by
    refine ((hE.proj N).infDist_harmonicW_le hjk hC (hE.isGraphBounded_proj N j k) q.2).trans ?_
    have h := IsC2Form.infDist_domainSub_whitney_le
      (σ := cyclesToDomainSpace ((complex n).harmonic_le_cycles j q.2)) hq hL0 N
    rw [hK]
    have : 0 ≤ 1 + 2 * C := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h this]
  exact hE.norm_sub_le_meshSize hij hjk hPi hPj hs N
    ((hσ.infDist_domainSub_whitney_le hL0 N).trans hi)
    ((hu.infDist_domainSub_whitney_le hL0 N).trans hj) hq'
    ((hB.infDist_domainSub_whitney_le hL0 N).trans hj)

/-- **Graph-norm rate in the total space of a window**: if every component of `ζ ∈ Γ(𝐝)` (the
window `HΛᵃ(Q) → ⋯ → HΛ^{a+m-1}(Q)`) is a `C²` form with bound `L`, some point of the Whitney
window is within `(m + m²) (Σᵢ B_{a+i}) L h_N` of `ζ`. -/
theorem exists_mem_window_le (a : ℤ) (m : ℕ) (ζ : ((complex n).window a m).totalD.GraphSpace)
    {L : ℝ} (hL0 : 0 ≤ L)
    (hζ : ∀ i : Fin m, IsC2Form (a + i) L (((complex n).window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((whitney n N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N := by
  obtain ⟨x, rfl, -, -⟩ := ((complex n).window a m).totalD.exists_toGraphSpace_eq ζ
  simp only [LinearPMap.graphFst_toGraphSpace] at hζ
  have hh := (meshSize_pos N).le
  have hle : ∀ i : Fin m, interpBound n (a + i) * L * meshSize N ≤
      (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N := fun i =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun i : Fin m => interpBound n (a + i))
        (fun _ _ => interpBound_nonneg n _) (Finset.mem_univ i)) hL0) hh
  obtain ⟨w, hw, hlt⟩ := Subcomplex.exists_mem_graphSub_le ((whitney n N).window a m) x
    (ε := (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N) fun i => by
      obtain ⟨v, hv, h1, h2⟩ := (hζ i).exists_mem_whitney_le hL0 N
      exact ⟨v, hv, h1.trans (hle i), fun j hx => (h2 (a + j) hx).trans (hle i)⟩
  refine ⟨w, hw, hlt.trans (le_of_eq ?_)⟩
  rw [Fintype.card_fin]; ring

/-- **`O(h)` convergence of the semi-discrete Hodge wave equation for smooth solutions**
([QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7): if every component of `ξ(s)` and
`ξ'(s)` is a `C²` form with bound `L` for `s ∈ [t₀, t₁]`, then
`‖ξ(t) - ξₕ(t)‖ ≤ A (1 + (t - t₀))² K h_N` with `K = (m + m²) (Σᵢ B_{a+i}) L`, discharging the
hypothesis `happ` of `norm_sub_le_meshSize_window`. -/
theorem norm_sub_le_meshSize_window_smooth (a : ℤ) (m : ℕ) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((whitney n N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitney n N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ s ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      IsC2Form (a + i) L (((complex n).window a m).totalD.graphFst (ξ s) i) ∧
        IsC2Form (a + i) L (((complex n).window a m).totalD.graphFst (ξ' s) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complex n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complex n).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((m : ℝ) + m * m) * (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N) := by
  have e : ((m : ℝ) + m * m) * (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N =
      (((m : ℝ) + m * m) * (∑ i : Fin m, interpBound n (a + i)) * L) * meshSize N := rfl
  rw [e]
  exact norm_sub_le_meshSize_window n a m hξ hξh h0 (fun N s hs =>
    ⟨exists_mem_window_le a m (ξ s) hL0 (fun i => (hreg s hs i).1) N,
      exists_mem_window_le a m (ξ' s) hL0 (fun i => (hreg s hs i).2) N⟩) N ht

/-! ## The vanishing-trace family `H̊Λ(Q)` -/

/-- `x ∈ L²(Q; Λʲ)` is a `C²` form of degree `j` **vanishing outside `Q`** (so with vanishing
traces on `∂Q`), whose derivative and the derivative of its exterior derivative are bounded by `L`
on `cl Q`; trivially true in negative degrees. -/
def IsC2FormMin (j : ℤ) (L : ℝ) (x : L2F ℝ (cubeDomain n) (formIdx n j)) : Prop :=
  j < 0 ∨ ∃ k : ℕ, (k : ℤ) = j ∧ ∃ w : FormField n, ∃ hw : ContDiff ℝ 2 w, (∀ y, IsDeg k (w y)) ∧
    (∀ y ∉ cubeDomain n, w y = 0) ∧
    (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L) ∧
    (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ (extDeriv w) y‖ ≤ L) ∧
    x = formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j ⟨w, hw.continuous⟩

omit [NeZero n] in
/-- **`d_min` of a smooth form**: if `x ∈ H̊Λᵏ(Q)` is the class of a `C¹` `k`-form `w`, then
`d x = (dw)|_Q` (`d_min ≤ d_max`, and `d_max (w|_Q) = (dw)|_Q`). -/
theorem complexMin_d_formL2 [NeZero n] (k : ℕ) {w : FormField n} (hw : ContDiff ℝ 1 w)
    (hdeg : ∀ y, IsDeg k (w y)) (x : ((complexMin n).d k (k + 1)).domain)
    (hx : (x : L2F ℝ (cubeDomain n) (formIdx n k)) =
      formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k ⟨w, hw.continuous⟩) :
    (complexMin n).d k (k + 1) x =
      formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
        ⟨extDeriv w, continuous_extDeriv hw⟩ := by
  have hd := deRham_minimalComplex_d (𝕜 := ℝ) (n := n) (isOpen_cubeDomain n) (k : ℤ)
  have hD := deRham_maximalComplex_d (𝕜 := ℝ) (n := n) (isOpen_cubeDomain n) (k : ℤ)
  obtain ⟨h, hval⟩ := formL2_mem_domain k hw hdeg
  refine (LinearPMap.apply_eq_of_eq' hd x).trans
    (((extDerivOp_minimal_le_maximal (𝕜 := ℝ) (n := n) (isOpen_cubeDomain n) (k : ℤ)).2
      (y := ⟨_, hD ▸ h⟩) hx).trans ?_)
  rw [← hval]
  exact (LinearPMap.apply_eq_of_eq' hD ⟨_, h⟩).symm

/-- **Degreewise interpolation error for `C²` forms vanishing outside `Q`**, in `H̊Λ(Q)`:
`‖x - v‖ ≤ B_j L h_N` and `‖d (x - v)‖ ≤ B_j L h_N` for some `v ∈ V̊ₕʲ`. -/
theorem IsC2FormMin.exists_mem_whitneyMin_le {j : ℤ} {L : ℝ}
    {x : L2F ℝ (cubeDomain n) (formIdx n j)} (hx : IsC2FormMin j L x) (hL0 : 0 ≤ L) (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (whitneyMin n N).V j, ‖x - v‖ ≤ interpBound n j * L * meshSize N ∧
      ∀ j' (hxj : x ∈ ((complexMin n).d j j').domain),
        ‖(complexMin n).d j j'
            ⟨x - v, Submodule.sub_mem _ hxj ((whitneyMin n N).le_domain j j' hv)⟩‖ ≤
          interpBound n j * L * meshSize N := by
  have hB0 := mul_nonneg (mul_nonneg (interpBound_nonneg n j) hL0) (meshSize_pos N).le
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, hsupp, hL, hL', rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    refine ⟨0, Submodule.zero_mem _, ?_, fun j' hxj => ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hB0
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := FEM.exists_mem_whitneyMin_le N k hw hsupp hL0 hL0 hL hL'
  have hh := (meshSize_pos N).le
  have hA0 := mul_nonneg (interpConst_nonneg n k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (interpConst_nonneg n (k + 1)) (mul_nonneg hh hL0)
  have e : interpBound n k * L * meshSize N =
      interpConst n k * (meshSize N * L) + interpConst n (k + 1) * (meshSize N * L) := by
    simp only [interpBound, Int.toNat_natCast]; ring
  refine ⟨v, hv, ?_, fun j' hxj => ?_⟩
  · rw [e]; linarith
  by_cases hj : (k : ℤ) + 1 = j'
  · subst hj
    have e' : (complexMin n).d k (k + 1)
        ⟨_ - v, Submodule.sub_mem _ hxj ((whitneyMin n N).le_domain k (k + 1) hv)⟩ =
        (complexMin n).d k (k + 1) ⟨_, hxj⟩ - (complexMin n).d k (k + 1) ⟨v, hdv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e', complexMin_d_formL2 k (hw.of_le (by norm_num)) hdeg ⟨_, hxj⟩ rfl, e]
    linarith
  · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]
    exact hB0

/-- **Graph-norm distance of a `C²` form vanishing outside `Q` to `V̊ₕʲ`**:
`dist_V(σ, V̊ₕʲ) ≤ 2 B_j L h_N`. -/
theorem IsC2FormMin.infDist_domainSub_whitneyMin_le {j : ℤ} {L : ℝ}
    {σ : (complexMin n).domainSpace j} (hσ : IsC2FormMin j L ((complexMin n).domainIncl j σ))
    (hL0 : 0 ≤ L) (N : ℕ) :
    Metric.infDist σ ((whitneyMin n N).domainSub j) ≤ 2 * (interpBound n j * L * meshSize N) := by
  obtain ⟨v, hv, h1, h2⟩ := hσ.exists_mem_whitneyMin_le hL0 N
  refine (Subcomplex.infDist_domainSub_le (S := whitneyMin n N)
    (rfl : (ComplexShape.up ℤ).Rel j (j + 1)) σ hv).trans ?_
  have e : (complexMin n).d j (j + 1) ((complexMin n).domainCoord j (j + 1) σ) -
      (complexMin n).d j (j + 1) ⟨v, (whitneyMin n N).le_domain j (j + 1) hv⟩ =
      (complexMin n).d j (j + 1) ⟨(complexMin n).domainIncl j σ - v,
        Submodule.sub_mem _ ((complexMin n).domainCoord j (j + 1) σ).2
          ((whitneyMin n N).le_domain j (j + 1) hv)⟩ := by
    rw [← LinearPMap.map_sub]; rfl
  rw [e, two_mul]
  exact add_le_add h1 (h2 (j + 1) ((complexMin n).domainCoord j (j + 1) σ).2)

/-- **Generic rate on the vanishing-trace family**: as `SmoothingEstimates.norm_sub_le_meshSize`,
for `H̊Λ(Q)`, the Whitney spaces with vanishing boundary DOFs and the projections `π̊_N`. -/
theorem SmoothingEstimatesMin.norm_sub_le_meshSize {p : ℕ → SmoothingParam (Fin n → ℝ)}
    {C : ℝ} (hE : SmoothingEstimatesMin n p C) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ}
    (hPi : ∀ z : ((complexMin n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complexMin n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complexMin n).d i j z‖)
    (hPj : ∀ z : ((complexMin n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complexMin n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complexMin n).d j k z‖)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j}
    (hs : (complexMin n).IsMixedSolution i j k f σ u q) {K : ℝ} (N : ℕ)
    (hσ : Metric.infDist σ ((whitneyMin n N).domainSub i) ≤ K * meshSize N)
    (hu : Metric.infDist u ((whitneyMin n N).domainSub j) ≤ K * meshSize N)
    (hq : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitneyMin n N).harmonicW j) ≤
      K * meshSize N)
    (hB : Metric.infDist ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))
      ((whitneyMin n N).domainSub j) ≤ K * meshSize N) :
    ‖σ - (whitneyMin n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).fst‖ +
        ‖u - (whitneyMin n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin n N) hij hjk f).snd.snd :
            (whitneyMin n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K * meshSize N := by
  have hμ0 : 0 ≤ 1 + 2 * C := by linarith [hE.two_mul_nonneg]
  have h := (hE.proj N).norm_sub_le_infDist hij hjk hE.one_le_two_mul hμ0 hPi hPj
    (hE.isGraphBounded_proj N i j) (hE.isGraphBounded_proj N j k)
    (fun _ hq' => (hE.proj N).norm_sub_π_harmonic_le hjk hE.two_mul_nonneg
      (hE.isGraphBounded_proj N j k) hq') hs
  refine h.trans ?_
  have hK0 : 0 ≤ (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) := by
    have := hE.two_mul_nonneg; positivity
  have e : (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K *
      meshSize N = (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) *
        ((4 + 2 * C) * (K * meshSize N)) := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  have hB' := mul_le_mul_of_nonneg_left hB hμ0
  have e' : (4 + 2 * C) * (K * meshSize N) =
      3 * (K * meshSize N) + (1 + 2 * C) * (K * meshSize N) := by ring
  rw [e']
  linarith

/-- **`O(h)` convergence of the mixed method with vanishing traces for smooth solutions**
([AFW2010], Thm 3.9; [Arnold2018], Ch. 7): as `SmoothingEstimates.norm_sub_le_meshSize_smooth`,
for `H̊Λ(Q)`, when `σ`, `u`, `P_𝔅 u` and `p` are `C²` forms vanishing outside `Q`, with
`K = 2 (1 + 2C)(B_i + B_j) L`. -/
theorem SmoothingEstimatesMin.norm_sub_le_meshSize_smooth {p : ℕ → SmoothingParam (Fin n → ℝ)}
    {C : ℝ} (hE : SmoothingEstimatesMin n p C) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ}
    (hPi : ∀ z : ((complexMin n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complexMin n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complexMin n).d i j z‖)
    (hPj : ∀ z : ((complexMin n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complexMin n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complexMin n).d j k z‖)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j}
    (hs : (complexMin n).IsMixedSolution i j k f σ u q) {L : ℝ} (hL0 : 0 ≤ L)
    (hσ : IsC2FormMin i L ((complexMin n).domainIncl i σ))
    (hu : IsC2FormMin j L ((complexMin n).domainIncl j u))
    (hB : IsC2FormMin j L ((complexMin n).domainIncl j
      ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))))
    (hq : IsC2FormMin j L (q : L2F ℝ (cubeDomain n) (formIdx n j))) (N : ℕ) :
    ‖σ - (whitneyMin n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).fst‖ +
        ‖u - (whitneyMin n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin n N) hij hjk f).snd.snd :
            (whitneyMin n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
        (2 * ((1 + 2 * C) * (interpBound n i + interpBound n j) * L)) * meshSize N := by
  have hC := hE.two_mul_nonneg
  have hh := (meshSize_pos N).le
  have hBi := interpBound_nonneg n i
  have hBj := interpBound_nonneg n j
  have hiL := mul_nonneg (mul_nonneg hBi hL0) hh
  have hjL := mul_nonneg (mul_nonneg hBj hL0) hh
  have hK : 2 * ((1 + 2 * C) * (interpBound n i + interpBound n j) * L) * meshSize N =
      2 * ((1 + 2 * C) * (interpBound n i * L * meshSize N)) +
        2 * ((1 + 2 * C) * (interpBound n j * L * meshSize N)) := by ring
  have hi : 2 * (interpBound n i * L * meshSize N) ≤
      2 * ((1 + 2 * C) * (interpBound n i + interpBound n j) * L) * meshSize N := by
    rw [hK]; nlinarith
  have hj : 2 * (interpBound n j * L * meshSize N) ≤
      2 * ((1 + 2 * C) * (interpBound n i + interpBound n j) * L) * meshSize N := by
    rw [hK]; nlinarith
  have hq' : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j))
      ((whitneyMin n N).harmonicW j) ≤
      2 * ((1 + 2 * C) * (interpBound n i + interpBound n j) * L) * meshSize N := by
    refine ((hE.proj N).infDist_harmonicW_le hjk hC (hE.isGraphBounded_proj N j k) q.2).trans ?_
    have h := IsC2FormMin.infDist_domainSub_whitneyMin_le
      (σ := cyclesToDomainSpace ((complexMin n).harmonic_le_cycles j q.2)) hq hL0 N
    rw [hK]
    have : 0 ≤ 1 + 2 * C := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h this]
  exact hE.norm_sub_le_meshSize hij hjk hPi hPj hs N
    ((hσ.infDist_domainSub_whitneyMin_le hL0 N).trans hi)
    ((hu.infDist_domainSub_whitneyMin_le hL0 N).trans hj) hq'
    ((hB.infDist_domainSub_whitneyMin_le hL0 N).trans hj)

instance (N : ℕ) (a : ℤ) (m : ℕ) (i : Fin m) :
    FiniteDimensional ℝ (((whitneyMin n N).window a m).V i) :=
  inferInstanceAs (FiniteDimensional ℝ ((whitneyMin n N).V (a + i)))

instance (N : ℕ) (a : ℤ) (m : ℕ) :
    FiniteDimensional ℝ ((whitneyMin n N).window a m).graphSub :=
  inferInstance

/-- **Graph-norm rate in the total space of a window of `H̊Λ(Q)`**: if every component of `ζ` is
a `C²` form vanishing outside `Q` with bound `L`, some point of the window of `V̊ₕ` is within
`(m + m²) (Σᵢ B_{a+i}) L h_N` of `ζ`. -/
theorem exists_mem_windowMin_le (a : ℤ) (m : ℕ)
    (ζ : ((complexMin n).window a m).totalD.GraphSpace) {L : ℝ} (hL0 : 0 ≤ L)
    (hζ : ∀ i : Fin m, IsC2FormMin (a + i) L (((complexMin n).window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((whitneyMin n N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N := by
  obtain ⟨x, rfl, -, -⟩ := ((complexMin n).window a m).totalD.exists_toGraphSpace_eq ζ
  simp only [LinearPMap.graphFst_toGraphSpace] at hζ
  have hh := (meshSize_pos N).le
  have hle : ∀ i : Fin m, interpBound n (a + i) * L * meshSize N ≤
      (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N := fun i =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun i : Fin m => interpBound n (a + i))
        (fun _ _ => interpBound_nonneg n _) (Finset.mem_univ i)) hL0) hh
  obtain ⟨w, hw, hlt⟩ := Subcomplex.exists_mem_graphSub_le ((whitneyMin n N).window a m) x
    (ε := (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N) fun i => by
      obtain ⟨v, hv, h1, h2⟩ := (hζ i).exists_mem_whitneyMin_le hL0 N
      exact ⟨v, hv, h1.trans (hle i), fun j hx => (h2 (a + j) hx).trans (hle i)⟩
  refine ⟨w, hw, hlt.trans (le_of_eq ?_)⟩
  rw [Fintype.card_fin]; ring

/-- **`O(h)` convergence of the semi-discrete Hodge wave equation with vanishing traces for
smooth solutions** ([QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7): as
`norm_sub_le_meshSize_window_smooth`, for the windows of `H̊Λ(Q)` and of `V̊ₕ`, when every component
of `ξ(s)` and `ξ'(s)` is a `C²` form vanishing outside `Q` with bound `L` on `[t₀, t₁]`. -/
theorem norm_sub_le_meshSize_windowMin_smooth (a : ℤ) (m : ℕ) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complexMin n).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complexMin n).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((whitneyMin n N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ =
      HodgeWave.ellipticProjection (((whitneyMin n N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ s ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      IsC2FormMin (a + i) L (((complexMin n).window a m).totalD.graphFst (ξ s) i) ∧
        IsC2FormMin (a + i) L (((complexMin n).window a m).totalD.graphFst (ξ' s) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complexMin n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complexMin n).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((m : ℝ) + m * m) * (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N) :=
  ((whitneyMin n N).window a m).norm_sub_le_of_approx hξ (hξh N) (h0 N) (fun s hs =>
    ⟨exists_mem_windowMin_le a m (ξ s) hL0 (fun i => (hreg s hs i).1) N,
      exists_mem_windowMin_le a m (ξ' s) hL0 (fun i => (hreg s hs i).2) N⟩) ht

end Feec.Models.Cube.FEM
