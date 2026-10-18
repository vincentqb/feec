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
  `‖Dw‖ ≤ L` and `‖D dw‖ ≤ L` on `cl Q`.
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

## Main definitions

* `Feec.Models.Cube.FEM.IsC2Form`, `Feec.Models.Cube.FEM.interpBound`

## Main results

* `Feec.Models.Cube.FEM.SmoothingEstimates.norm_sub_le_meshSize_smooth`
* `Feec.Models.Cube.FEM.norm_sub_le_meshSize_window_smooth`

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (approximation
  estimates, rates for smooth solutions)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.9 (quasi-optimality of the mixed method)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.14 (convergence of the semi-discrete Hodge wave equation)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.ExteriorFibre

variable {n : ℕ}

/-- `x ∈ L²(Q; Λʲ)` is a `C²` form of degree `j ≥ 0` whose derivative and the derivative of its
exterior derivative are bounded by `L` on `cl Q`. -/
def IsC2Form (j : ℤ) (L : ℝ) (x : L2F ℝ (cubeDomain n) (formIdx n j)) : Prop :=
  ∃ k : ℕ, (k : ℤ) = j ∧ ∃ w : FormField n, ∃ hw : ContDiff ℝ 2 w, (∀ y, IsDeg k (w y)) ∧
    (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L) ∧
    (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ (extDeriv w) y‖ ≤ L) ∧
    x = formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j ⟨w, hw.continuous⟩

variable (n) in
/-- The constant `B_j = A_j + A_{j+1}` of the graph-norm interpolation error in degree `j`. -/
def interpBound (j : ℤ) : ℝ := interpConst n j.toNat + interpConst n (j.toNat + 1)

variable (n) in
theorem interpBound_nonneg (j : ℤ) : 0 ≤ interpBound n j :=
  add_nonneg (interpConst_nonneg n _) (interpConst_nonneg n _)

variable [NeZero n]

/-- **Degreewise interpolation error for `C²` forms**: `‖x - v‖ ≤ B_j L h_N` and
`‖d (x - v)‖ ≤ B_j L h_N` for the Whitney interpolant `v ∈ Vₕʲ`. -/
theorem IsC2Form.exists_mem_whitney_le {j : ℤ} {L : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)}
    (hx : IsC2Form j L x) (hL0 : 0 ≤ L) (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (whitney n N).V j, ‖x - v‖ ≤ interpBound n j * L * meshSize N ∧
      ∀ j' (hxj : x ∈ ((complex n).d j j').domain),
        ‖(complex n).d j j' ⟨x - v, Submodule.sub_mem _ hxj ((whitney n N).le_domain j j' hv)⟩‖ ≤
          interpBound n j * L * meshSize N := by
  obtain ⟨k, rfl, w, hw, hdeg, hL, hL', rfl⟩ := hx
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
  obtain ⟨k, rfl, w, hw, hdeg, hL, hL', he⟩ := hσ
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

end Feec.Models.Cube.FEM
