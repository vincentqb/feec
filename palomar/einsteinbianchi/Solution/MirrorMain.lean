module

public import Solution.MirrorSpaces
public import Solution.MirrorRate
public import Feec.Instances.EinsteinBianchiGauss
public import Solution.Instance

/-!
# The mirror scheme (6.5) on the cube

`mirror_fem_main`: on the Freudenthal meshes of the cube, the mirror scheme `mirrorQ` (one
parity smoother for both rows, `exists_mirror_estimates`) has the spaces of Table 6.1 with the
mirror boundary conditions (`mirrorQ_spaces`), uniformly bounded projections satisfying (5.4)
and consistent at the order `h` (`mirrorQ_isBounded`, `mirrorQ_compatible`,
`mirrorQ_isConsistent`), the mirror data are BGG data (`isBGG_𝒟m`), for all large `N` a
non-stationary solution of (6.5) from `(0, u₀, 0, 0)`, `u₀ ≠ 0`, satisfies the discrete Gauss law
at `t = 0` (`exists_gauss_solution`: `u₀` from `exists_isGauss_ne_zero` and
`eventually_exists_π2_S1_ne`, existence from Prop 6.2 in the form proved in `Feec`, the source of
(6.5) being `0`, `Feec.BGG.exists_discreteSolution_iff_compatible_u`), (6.5) converges to the real
part of every solution from the constraint (`mirrorQ_converges`), and the `O(h)` rate for TSD data
of `D(L³)` holds (`mirrorQ_rate`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2, §6.3, (6.5), Prop 6.2, Table 6.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)

section Gauss

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- **`S¹ ≠ 0`**: the counterexample field of `cube_bestApprox` has `S¹ v ≠ 0`. -/
theorem exists_wsL2_one_ne : ∃ x : Wv W1, wsL2 (Ω := cubeDomain 3) 1 x ≠ 0 := by
  obtain ⟨p, C₀, hT', hB', -⟩ := cube_hyps
  obtain ⟨c, hc, h⟩ := cube_bestApprox hT' hB'
  obtain ⟨v, -, hv0, hle⟩ := h 2 le_rfl
  refine ⟨v, fun h0 => ?_⟩
  have hl := hle 0 (Submodule.zero_mem _)
  change _ ≤ ‖wsL2 (Ω := cubeDomain 3) 1 (v : Wv W1) - 0‖ at hl
  rw [h0, sub_zero, norm_zero] at hl
  have hp : 0 < c * √(‖(v : Wv W1)‖ ^ 2 + ‖𝒟.dt1 v‖ ^ 2) := mul_pos hc (Real.sqrt_pos.2
    (add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.2 hv0) 2) (sq_nonneg _)))
  linarith

/-- **Eventually `π²S¹v ≠ 0` for some `v ∈ Ṽₕ¹`**: for `S¹x ≠ 0`, `π²S¹π̃¹x → S¹x` (the
projections converge strongly and are uniformly bounded). -/
theorem eventually_exists_π2_S1_ne : ∀ᶠ N in atTop, ∃ v : 𝒟m.dt1.domain,
    (v : Wv W1) ∈ (mirrorQ hT hB N).Vt1 ∧ (mirrorQ hT hB N).π2 (𝒟m.S1 v) ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_wsL2_one_ne
  set S : Wv W1 →L[ℝ] W2 := wsL2 (Ω := cubeDomain 3) (n := 3) 1
  have hπt : Tendsto (fun N => ‖x - (mirrorQ hT hB N).πt1 x‖) atTop (𝓝 0) := by
    have h : ∀ a ∈ Finset.univ, Tendsto (fun N => ‖x a - ((hB a).proj N).π 1 (x a)‖ ^ 2)
        atTop (𝓝 0) := fun a _ => by
      simpa using ((hB a).tendsto_norm_sub_proj 1 (x a)).pow 2
    have hs := tendsto_finsetSum Finset.univ h
    rw [Finset.sum_const_zero] at hs
    have e : ∀ N, ‖x - (mirrorQ hT hB N).πt1 x‖ =
        √(∑ a, ‖x a - ((hB a).proj N).π 1 (x a)‖ ^ 2) := fun N => by
      rw [← Real.sqrt_sq (norm_nonneg (x - _)), PiLp.norm_sq_eq_of_L2]
      rfl
    simp_rw [e]
    have hl := (Real.continuous_sqrt.tendsto 0).comp hs
    rw [Real.sqrt_zero] at hl
    exact hl
  have hπ2 : Tendsto (fun N => ‖S x - (mirrorQ hT hB N).π2 (S x)‖) atTop (𝓝 0) :=
    hT.tendsto_norm_sub_proj 2 (S x)
  have hbound : ∀ N, ‖(mirrorQ hT hB N).π2 (S ((mirrorQ hT hB N).πt1 x)) - S x‖ ≤
      2 * C * ‖S‖ * ‖x - (mirrorQ hT hB N).πt1 x‖ + ‖S x - (mirrorQ hT hB N).π2 (S x)‖ :=
    fun N => by
      have hb := (mirrorQ_isBounded hT hB N).2.2.1
      have e : (mirrorQ hT hB N).π2 (S ((mirrorQ hT hB N).πt1 x)) - S x =
          (mirrorQ hT hB N).π2 (S ((mirrorQ hT hB N).πt1 x - x)) +
            ((mirrorQ hT hB N).π2 (S x) - S x) := by
        rw [map_sub, map_sub]; abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sub_rev _ _).le)
      calc ‖(mirrorQ hT hB N).π2 (S ((mirrorQ hT hB N).πt1 x - x))‖
          ≤ ‖(mirrorQ hT hB N).π2‖ * ‖S ((mirrorQ hT hB N).πt1 x - x)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 2 * C * (‖S‖ * ‖(mirrorQ hT hB N).πt1 x - x‖) :=
            mul_le_mul hb (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
              hT.two_mul_nonneg
        _ = 2 * C * ‖S‖ * ‖x - (mirrorQ hT hB N).πt1 x‖ := by rw [norm_sub_rev]; ring
  have ht : Tendsto (fun N => ‖(mirrorQ hT hB N).π2 (S ((mirrorQ hT hB N).πt1 x)) - S x‖)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hbound (by
      simpa using (hπt.const_mul (2 * C * ‖S‖)).add hπ2)
  filter_upwards [ht.eventually (gt_mem_nhds (norm_pos_iff.2 hx))] with N hN
  refine ⟨⟨_, (mirrorQ hT hB N).let1 ((mirrorQ hT hB N).πt1_mem x)⟩,
    (mirrorQ hT hB N).πt1_mem x, fun h0 => ?_⟩
  change (mirrorQ hT hB N).π2 (S ((mirrorQ hT hB N).πt1 x)) = 0 at h0
  rw [h0, zero_sub, norm_neg] at hN
  exact lt_irrefl _ hN

set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
/-- **For all large `N`, a non-stationary solution of (6.5) from a nonzero `uₕ(0)` in the
discrete Gauss law**: `uₕ(0) = u₀` of `exists_isGauss_ne_zero` (from
`eventually_exists_π2_S1_ne`), with `σₕ(0) = 0`, `Mₕ(0) = 0`, `ρₕ(0) = 0`; it exists by
`Feec.BGG.exists_discreteSolution_iff_compatible_u` (`u₀ ⊥ d̃ψ` when `π¹S⁰ψ = 0`, the source of
(6.5) being `0`), and `π²S¹u₀ ≠ 0` makes `Mₕ` non-constant (`IsDiscreteWave.exists_M_ne`). -/
theorem exists_gauss_solution {T : ℝ} (hT0 : 0 < T) : ∀ᶠ N in atTop, ∃ σ φ u M ρ' lam,
    (mirrorQ hT hB N).IsDiscreteWave T 0 σ φ u M ρ' lam ∧
      (mirrorQ hT hB N).IsGauss (σ 0) (u 0) ∧ ((u 0 : 𝒟m.dt1.domain) : Wv W1) ≠ 0 ∧
      ∃ t ∈ Ioc 0 T, M t ≠ M 0 := by
  filter_upwards [eventually_exists_π2_S1_ne hT hB] with N ⟨v₁, hv₁, hne⟩
  obtain ⟨u₀, hu₀, hu₀0, hG, hS⟩ :=
    WeakSymmetryData.Discretization.exists_isGauss_ne_zero isBGG_𝒟m hv₁ hne
  have key := @Feec.BGG.exists_discreteSolution_iff_compatible_u
    (mirrorFEM hT hB N).V0h (mirrorFEM hT hB N).V1h (mirrorFEM hT hB N).W2h
    (mirrorFEM hT hB N).Vt0h (mirrorFEM hT hB N).Vt1h (mirrorFEM hT hB N).Wt2h
    _ _ _ _ _ _ _ _ _ _ _ _ (mirrorWave hT hB N) _ _ _ _ _ _ T hT0
    (mirrorWave_dt0_injective hT hB N) (mirrorWave_S0_surjective hT hB N) (mirrorSource hT hB N 0)
    (continuousOn_const (c := mirrorSource hT hB N 0 0))
  obtain ⟨s, hσ, hu, -, -⟩ := (key 0 ⟨e1m u₀, e1m_mem hT hB N hu₀⟩ 0 0).2 fun ψ hψ => by
    have h1 := congrArg (fun x : (mirrorFEM hT hB N).V1h => ((x : TU1) : W1)) hψ
    exact hG.2 0 (e0m.symm (ψ : BU0)) (Submodule.zero_mem _) (fun a => ψ.2 a)
      ((map_zero _).trans h1.symm)
  have hw := isDiscreteWave_of_mirror hT hB N s
  have hu' : e1m.symm (s.u 0 : BU1) = u₀ := by rw [hu]; exact e1m.symm_apply_apply u₀
  have hσ' : (((s.σ 0 : TU0) : 𝒟m.d0.domain) : W0) = 0 := by simp only [hσ]; rfl
  refine ⟨_, _, _, _, _, _, hw, ?_, ?_, hw.exists_M_ne hT0 ?_⟩
  · change (mirrorQ hT hB N).IsGauss (((s.σ 0 : TU0) : 𝒟m.d0.domain) : W0)
      ((e1m.symm (s.u 0 : BU1) : 𝒟m.dt1.domain) : Wv W1)
    rw [hσ', hu']
    exact hG
  · change ((e1m.symm (s.u 0 : BU1) : 𝒟m.dt1.domain) : Wv W1) ≠ 0
    rw [hu']
    exact hu₀0
  · change (mirrorQ hT hB N).π2 (𝒟m.S1 ((e1m.symm (s.u 0 : BU1) : 𝒟m.dt1.domain) : Wv W1)) ≠ 0
    rw [hu']
    exact hS

end Gauss

/-- **The mirror scheme (6.5) on the cube**: the elements of Table 5.1 with the mirror
conditions, BGG data, the discrete Gauss law for nonzero solutions, the convergence to the real
part of every solution from the constraint (no regularity) and the `O(h)` rate for TSD data of
`D(L³)`. -/
theorem mirror_fem_main : ∃ (𝒯 : ℕ → SimplicialMesh 3) (Q : ℕ → mirrorData.Discretization)
    (C K : ℝ), IsTable51 𝒯 Q C ∅ (fun a => {a}) ∧ mirrorData.IsBGG ∧
    (∀ T, 0 < T → ∀ᶠ N in atTop, ∃ σ φ u M ρ lam, (Q N).IsDiscreteWave T 0 σ φ u M ρ lam ∧
      (Q N).IsGauss (σ 0) (u 0) ∧ (u 0 : L2Vec (cube 3) 1) ≠ 0 ∧ ∃ t ∈ Ioc 0 T, M t ≠ M 0) ∧
    (∀ x ∈ Feec.HilbertComplex.totalSub Feec.Models.Cube.MirrorBGG.tsdQ, ∀ T, 0 < T → ∀ ε > 0,
      ∀ᶠ N in atTop, ∃ σh φh uh Mh ρh lamh, (Q N).IsDiscreteWave T 0 σh φh uh Mh ρh lamh ∧
        ∀ t ∈ Icc 0 T, √(‖(σh t : L2Form (cube 3) 0)‖ ^ 2 +
          ‖(show L2Vec (cube 3) 1 from Feec.Models.Cube.MirrorWeakSymmetry.rowsW1L
            (Feec.Models.Cube.MirrorWeakSymmetry.stEL
              (Feec.Models.Cube.MirrorBGG.complexQ.waveGroup.S t x))) - uh t‖ ^ 2 +
          ‖Mh t‖ ^ 2 + ‖(show L2Vec (cube 3) 2 from Feec.Models.Cube.MirrorWeakSymmetry.rowsW2L
            (Feec.Models.Cube.MirrorWeakSymmetry.stBL
              (Feec.Models.Cube.MirrorBGG.complexQ.waveGroup.S t x))) - ρh t‖ ^ 2) ≤ ε) ∧
    0 ≤ K ∧ ∀ N (D : Feec.Models.Cube.MirrorWeakSymmetry.TSDDatum)
      (h3 : D.LLU₀ ∈ Feec.Models.Cube.MirrorBGG.complexQ.wave.domain) (T : ℝ), 0 < T →
      ∀ U : ℝ → PiLp 2 Feec.Models.Cube.MirrorBGG.SpaceQ, U 0 = D.U₀ →
        Feec.Evolution.IsStrongSolution Feec.Models.Cube.MirrorBGG.complexQ.wave (Icc 0 T) 0 U →
      ∃ σh φh uh Mh ρh lamh, (Q N).IsDiscreteWave T 0 σh φh uh Mh ρh lamh ∧ ∀ t ∈ Icc 0 T,
        √(‖(σh t : L2Form (cube 3) 0)‖ ^ 2 +
          ‖(show L2Vec (cube 3) 1 from Feec.Models.Cube.MirrorWeakSymmetry.rowsW1L
            (Feec.Models.Cube.MirrorWeakSymmetry.stEL (U t))) - uh t‖ ^ 2 +
          ‖Mh t‖ ^ 2 + ‖(show L2Vec (cube 3) 2 from Feec.Models.Cube.MirrorWeakSymmetry.rowsW2L
            (Feec.Models.Cube.MirrorWeakSymmetry.stBL (U t))) - ρh t‖ ^ 2) ≤
        K * (‖D.U₀‖ + ‖D.LU₀‖ + ‖D.LLU₀‖ +
          ‖Feec.Models.Cube.MirrorBGG.complexQ.wave ⟨D.LLU₀, h3⟩‖) * (1 + t) *
            meshSize (𝒯 N) := by
  rw [mirrorData_eq]
  obtain ⟨ρ, C₀, hT, hB⟩ := exists_mirror_estimates
  obtain ⟨A, hA0, hA⟩ := mirrorQ_isConsistent hT hB
  obtain ⟨K, hK0, hK⟩ := mirrorQ_rate hT hB
  have h2C := hT.two_mul_nonneg
  refine ⟨cubeMesh, mirrorQ hT hB, 2 * C₀ + A, K, ⟨isMeshFamily_cube, points_cube, fun N => ?_⟩,
    isBGG_𝒟m, fun T hT0 => exists_gauss_solution hT hB hT0,
    fun x hx T hT0 ε hε => mirrorQ_converges hT hB hx hT0 hε, hK0,
    fun N D h3 T hT0 U hU0 hU => ?_⟩
  · obtain ⟨s0, s1, s2, s3, s4, s5⟩ := mirrorQ_spaces hT hB N
    refine ⟨s0, s1, s2, s3, s4, s5, (mirrorQ_isBounded hT hB N).mono (by linarith),
      mirrorQ_compatible hT hB N, ?_⟩
    rw [meshSize_cubeMesh]; exact hA _ (by linarith) N
  · rw [meshSize_cubeMesh]; exact hK N D h3 T hT0 U hU0 hU

end FEEC
