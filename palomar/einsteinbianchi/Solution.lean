module

public import Solution.CubeMain
public import Solution.CubeSobolev
public import Solution.CubeNonvac
public import Solution.CubeUnique
public import Solution.Converge
public import Solution.MirrorTheorems
public import Solution.Instance

/-!
# What the weak-symmetry method computes for the linearized Einstein–Bianchi equations (solution)

`FEEC.bggWeakSymmetry`: `WeakSymmetryData.weakSymmetry_of` (Prop 5.4, Thm 5.5,
`Solution.Abstract`), `IsDiscreteWave.eq_of_eq` and `IsDiscreteWave.isGauss`
(`Solution.DiscreteWave`).

`FEEC.weakSymmetry_electric`: the cube data are `Feec`'s (`bggData_cube_eq`); `cube_hyps`,
`cubeQ_spaces`, `femSpace_univ_eq`, `cube_S0h_ne`, `cube_bestApprox` (`Solution.Instance`), the
convergence from every datum of `D(L)` and the limit of the TSD datum `(0, 0, 0, ⋆β)`
(`cube_converges`, `cube_beta`, `Solution.Converge`), and the `H¹` rates `cube_static_rate_sob`,
`cube_wave_rate_sob` (`Solution.CubeSobolev`, `Solution.CubeWave`). The `C²` rates of the thesis
follow from its statement (`weakSymmetry_electric_c2`, `Solution.Smooth`).

`FEEC.weakSymmetry_mirror` (`Solution.MirrorTheorems`): the challenge's TSD states are the real
parts of constrained states of `Feec`'s mirror complex, and the mirror scheme is `Feec`'s
(`mirror_fem_main`).

`FEEC.weakSymmetry_electric_nonvacuous`: `cube_static_nonvacuous`, `cube_wave_nonvacuous` and
their `H¹` classes `cube_static_h1`, `cube_wave_h1` (`Solution.CubeNonvac`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 5, Ch. 6

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Set Filter

@[expose] public noncomputable section

universe u

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

theorem bggWeakSymmetry (C : ℝ) : ∃ K : ℝ, ∀ {W0 W1 W2 Wt0 Wt1 Wt2 : Type u}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [NormedAddCommGroup W1]
    [InnerProductSpace ℝ W1] [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
    [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0] [NormedAddCommGroup Wt1]
    [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
    (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2) (Q : D.Discretization),
    (∀ T f σ φ u M ρ lam σ' φ' u' M' ρ' lam', Q.IsDiscreteWave T f σ φ u M ρ lam →
      Q.IsDiscreteWave T f σ' φ' u' M' ρ' lam' → σ 0 = σ' 0 → u 0 = u' 0 → M 0 = M' 0 →
      ρ 0 = ρ' 0 → ∀ t ∈ Icc 0 T, σ t = σ' t ∧ u t = u' t ∧ M t = M' t ∧ ρ t = ρ' t) ∧
    (D.IsBGG → ∀ T σ φ u M ρ lam, Q.IsDiscreteWave T 0 σ φ u M ρ lam →
      Q.IsGauss (σ 0) (u 0) → ∀ t ∈ Icc 0 T, Q.IsGauss (σ t) (u t)) ∧
    (D.IsBGG → D.IsStable C → Q.IsBounded C → Q.Compatible →
    (∀ F, ∃! x : D.d0.domain × D.dt0.domain × D.dt1.domain × W1,
      Q.IsDiscreteSolution F x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
    ∀ (h Λ : ℝ), 0 ≤ h → Q.IsConsistent C h → ∀ F σ φ u lam σh φh uh lamh,
      D.IsSolution F σ φ u lam → ‖lam‖ ≤ Λ →
      (∀ w : D.d1.domain, |⟪D.S1 u, D.d1 w⟫_ℝ| ≤ Λ * ‖(w : W1)‖) →
      Q.IsDiscreteSolution F σh φh uh lamh →
      Q.errorSq σ σh φ φh u uh ≤ K * (Q.projErrorSq σ φ u + h ^ 2 * (Λ ^ 2 + ‖D.S1 u‖ ^ 2) +
        ‖D.S1 u - Q.π2 (D.S1 u)‖ ^ 2)) := by
  obtain ⟨K, hK⟩ := WeakSymmetryData.weakSymmetry_of.{u} C
  exact ⟨K, fun D Q => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 e0 e1 e2 e3 =>
    WeakSymmetryData.Discretization.IsDiscreteWave.eq_of_eq Q h1 h2 e0 e1 e2 e3,
    fun hD _ _ _ _ _ _ _ h h0 => WeakSymmetryData.Discretization.IsDiscreteWave.isGauss Q hD h h0,
    fun hD hS hB hc => hK D Q hD hS hB hc⟩⟩

set_option maxHeartbeats 4000000 in
theorem weakSymmetry_electric : ∃ (𝒯 : ℕ → SimplicialMesh 3)
    (Q : ℕ → (bggData (cube 3)).Discretization) (C K : ℝ),
    IsTable51 𝒯 Q C Finset.univ (fun _ => Finset.univ) ∧ (bggData (cube 3)).IsBGG ∧
    (bggData (cube 3)).IsStable C ∧
    (∀ N, 2 ≤ N → ∃ ψ : (bggData (cube 3)).dt0.domain, (ψ : L2Vec (cube 3) 0) ∈ (Q N).Vt0 ∧
      (Q N).π1 ((bggData (cube 3)).S0 ψ) ≠ (bggData (cube 3)).S0 ψ) ∧
    (∀ N T f σ φ u M ρ lam σ' φ' u' M' ρ' lam', 0 < T → ContinuousOn f (Icc 0 T) →
      (Q N).IsDiscreteWave T f σ φ u M ρ lam → (Q N).IsDiscreteWave T f σ' φ' u' M' ρ' lam' →
      σ 0 = σ' 0 → u 0 = u' 0 → M 0 = M' 0 → ρ 0 = ρ' 0 →
      (∀ t ∈ Icc 0 T, σ t = σ' t ∧ u t = u' t ∧ M t = M' t ∧ ρ t = ρ' t) ∧
        ∀ t ∈ Ico 0 T, φ t = φ' t ∧ lam t = lam' t) ∧
    (∀ U₀ V T, (bggData (cube 3)).IsWave U₀ V → 0 < T →
      (∃ U, U 0 = U₀ ∧ IsStrongSolution {p | (bggData (cube 3)).IsWave p.1 p.2} (Icc 0 T) U) ∧
      (∃ Uh : ℕ → ℝ → _, (∀ N, Uh N ∈ (Q N).trajectories T 0) ∧
        Tendsto (fun N => stateNorm (U₀ - Uh N 0)) atTop (𝓝 0)) ∧
      ∀ U (Uh : ℕ → ℝ → _), U 0 = U₀ →
        IsStrongSolution {p | (bggData (cube 3)).IsWave p.1 p.2} (Icc 0 T) U →
        (∀ N, Uh N ∈ (Q N).trajectories T 0) →
        Tendsto (fun N => stateNorm (U₀ - Uh N 0)) atTop (𝓝 0) →
        ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T, stateNorm (U t - Uh N t) < ε) ∧
    (∃ U₀ V, (bggData (cube 3)).IsWave U₀ V ∧ IsTSDState U₀ ∧ ∀ T > 0,
      ∀ U, U 0 = U₀ → IsStrongSolution {p | (bggData (cube 3)).IsWave p.1 p.2} (Icc 0 T) U →
        (∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (U t).2.1) ∧ ∀ Uh : ℕ → ℝ → _,
          (∀ N, Uh N ∈ (Q N).trajectories T 0) →
          Tendsto (fun N => stateNorm (U₀ - Uh N 0)) atTop (𝓝 0) →
          ∀ᶠ N in atTop, ¬IsTSD (mat1 (Uh N t).2.1)) ∧
        ∃ t ∈ Icc 0 T, (∃ a i, mat2 (U t).2.2.2 a i ≠ mat2 (U t).2.2.2 i a) ∧
          ∀ Uh : ℕ → ℝ → _, (∀ N, Uh N ∈ (Q N).trajectories T 0) →
          Tendsto (fun N => stateNorm (U₀ - Uh N 0)) atTop (𝓝 0) →
          ∀ᶠ N in atTop, ∃ a i, mat2 (Uh N t).2.2.2 a i ≠ mat2 (Uh N t).2.2.2 i a) ∧
    (∀ N F σ φ u lam σh φh uh lamh L, (bggData (cube 3)).IsSolution F σ φ u lam →
      IsSobolevForm (cube 3) 1 0 L (σ : L2Form (cube 3) 0) →
      (∀ a, IsSobolevForm (cube 3) 1 0 L ((φ : L2Vec (cube 3) 0) a)) →
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((bggData (cube 3)).dt0 φ a)) →
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((u : L2Vec (cube 3) 1) a)) →
      (∀ a, IsSobolevForm (cube 3) 1 2 L ((bggData (cube 3)).dt1 u a)) → ‖lam‖ ≤ L →
      (Q N).IsDiscreteSolution F σh φh uh lamh →
      (Q N).errorSq σ σh φ φh u uh ≤ (K * L * meshSize (𝒯 N)) ^ 2) ∧
    (∀ N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, 0 < T → ContinuousOn f (Icc 0 T) →
      (bggData (cube 3)).IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' →
      (∀ t ∈ Icc 0 T, IsH1State L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsH1State L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) →
      ∃ Uh ∈ (Q N).trajectories T f, ∀ t ∈ Icc 0 T,
        stateNorm (((σ t : L2Form (cube 3) 0), (u t : L2Vec (cube 3) 1), M t, ρ t) - Uh t) ≤
          K * L * (1 + t) * meshSize (𝒯 N)) ∧
    ∃ c > 0, ∀ N, 2 ≤ N → ∃ v : (bggData (cube 3)).dt1.domain,
      (v : L2Vec (cube 3) 1) ∈ (Q N).Vt1 ∧ (v : L2Vec (cube 3) 1) ≠ 0 ∧ ∀ w ∈ (Q N).V2,
        c * √(‖(v : L2Vec (cube 3) 1)‖ ^ 2 + ‖(bggData (cube 3)).dt1 v‖ ^ 2) ≤
          ‖(bggData (cube 3)).S1 v - w‖ := by
  rw [bggData_cube_eq]
  obtain ⟨p, C₀, hT, hB, C, hS, hQ⟩ := cube_hyps
  obtain ⟨Ks, hKs⟩ := cube_static_rate_sob hT hB hS (fun N => (hQ N).1) (fun N => (hQ N).2.2)
  obtain ⟨cs, hcs, hcsH⟩ := isSobolevStaticTr_of
  obtain ⟨Kw, hKw⟩ := cube_wave_rate_sob hT hB
  obtain ⟨cw, hcw, hcwH⟩ := isSobolevStateTr_of
  set K := max |Ks * cs| |Kw * cw| with hKdef
  refine ⟨cubeMesh, cubeQ hT hB, C, K, ⟨isMeshFamily_cube, points_cube, fun N => ?_⟩, isBGG_𝒟,
    hS, cube_S0h_ne hT hB,
    fun N T f σ φ u M ρ lam σ' φ' u' M' ρ' lam' hT0 _ h1 h2 e0' e1' e2' e3' =>
      cube_wave_unique hT hB N hT0 h1 h2 e0' e1' e2' e3',
    fun U₀ V T hW hT0 => cube_converges hT hB hW hT0, cube_beta hT hB,
    fun N F σ φ u lam σh φh uh lamh L hs hσ hφ hdφ hu hdu hl hd => ?_,
    fun N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L hT0 hf hw hreg => ?_, cube_bestApprox hT hB⟩
  · obtain ⟨s0, s1, s2, s3, s4, s5⟩ := cubeQ_spaces hT hB N
    simp only [femSpace_univ_eq]
    refine ⟨s0, s1, s2, s3, s4, s5, (hQ N).1, (hQ N).2.1, ?_⟩
    rw [meshSize_cubeMesh]; exact (hQ N).2.2
  · rw [meshSize_cubeMesh]
    have hL0 : 0 ≤ L := (norm_nonneg _).trans hl
    have h := hKs N F σ φ u lam σh φh uh lamh (cs * L) hs
      (hcsH hL0 hs.2.2 hσ hφ hdφ hu hdu) (hl.trans (le_mul_of_one_le_left hL0 hcs)) hd
    have hLh : 0 ≤ L * Feec.Models.Cube.FEM.meshSize N := mul_nonneg hL0 (meshSize_pos N).le
    have hab : |Ks * (cs * L) * Feec.Models.Cube.FEM.meshSize N| ≤
        K * L * Feec.Models.Cube.FEM.meshSize N := by
      rw [show Ks * (cs * L) * Feec.Models.Cube.FEM.meshSize N =
        (Ks * cs) * (L * Feec.Models.Cube.FEM.meshSize N) by ring, abs_mul, abs_of_nonneg hLh,
        mul_assoc K]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hLh
    calc _ ≤ (Ks * (cs * L) * Feec.Models.Cube.FEM.meshSize N) ^ 2 := h
      _ = |Ks * (cs * L) * Feec.Models.Cube.FEM.meshSize N| ^ 2 := (sq_abs _).symm
      _ ≤ (K * L * Feec.Models.Cube.FEM.meshSize N) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hab 2
  · have hL0 : 0 ≤ L := (norm_nonneg _).trans (hreg 0 ⟨le_rfl, hT0.le⟩).2.2.1
    obtain ⟨σh, φh, uh, Mh, ρh, lamh, hd, hr⟩ :=
      hKw N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' (cw * L) hT0 hf hw fun t ht =>
        ⟨hcwH (φ := e0 (φ t)) (u := e1 (u t)) hL0 (hreg t ht).1,
          hcwH (φ := e0 (φ' t)) (u := e1 (u' t)) hL0 (hreg t ht).2.1,
          (hreg t ht).2.2.1.trans (le_mul_of_one_le_left hL0 hcw),
          (hreg t ht).2.2.2.trans (le_mul_of_one_le_left hL0 hcw)⟩
    refine ⟨_, mem_trajectories hd, fun t ht => ?_⟩
    rw [meshSize_cubeMesh]
    have ht0 : 0 ≤ (1 + t) * Feec.Models.Cube.FEM.meshSize N :=
      mul_nonneg (by linarith [ht.1]) (meshSize_pos N).le
    calc _ ≤ Kw * (cw * L) * (1 + t) * Feec.Models.Cube.FEM.meshSize N := hr t ht
      _ = (Kw * cw) * (L * ((1 + t) * Feec.Models.Cube.FEM.meshSize N)) := by ring
      _ ≤ K * (L * ((1 + t) * Feec.Models.Cube.FEM.meshSize N)) :=
        mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_max_right _ _))
          (mul_nonneg hL0 ht0)
      _ = K * L * (1 + t) * Feec.Models.Cube.FEM.meshSize N := by ring

theorem weakSymmetry_electric_nonvacuous :
    (∃ F σ φ u lam L, (bggData (cube 3)).IsSolution F σ φ u lam ∧
      (σ : L2Form (cube 3) 0) ≠ 0 ∧ (φ : L2Vec (cube 3) 0) ≠ 0 ∧ (u : L2Vec (cube 3) 1) ≠ 0 ∧
      lam ≠ 0 ∧ ‖lam‖ ≤ L ∧ IsSobolevForm (cube 3) 1 0 L (σ : L2Form (cube 3) 0) ∧
      (∀ a, IsSobolevForm (cube 3) 1 0 L ((φ : L2Vec (cube 3) 0) a)) ∧
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((bggData (cube 3)).dt0 φ a)) ∧
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((u : L2Vec (cube 3) 1) a)) ∧
      ∀ a, IsSobolevForm (cube 3) 1 2 L ((bggData (cube 3)).dt1 u a)) ∧
    ∀ T, 0 < T → ∃ f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, ContinuousOn f (Icc 0 T) ∧
      (bggData (cube 3)).IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' ∧
      (∀ t ∈ Icc 0 T, IsH1State L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsH1State L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) ∧
      (∀ t, (u t : L2Vec (cube 3) 1) ≠ 0) ∧
      ∀ t ∈ Ioc 0 T, (σ t : L2Form (cube 3) 0) ≠ 0 ∧ (φ t : L2Vec (cube 3) 0) ≠ 0 := by
  rw [bggData_cube_eq]
  obtain ⟨L, hs, h1, h2, h3, h4, -, -, -, c4⟩ := cube_static_nonvacuous
  obtain ⟨L₁, hL₁, s1, s2, s3, s4, s5⟩ := cube_static_h1
  have m := fun {j : ℤ} {x : L2Form (cube 3) j} (h : IsSobolevForm (cube 3) 1 j L₁ x) =>
    isSobolevForm_mono hL₁ (le_max_right L L₁) h
  refine ⟨⟨_, _, _, _, _, max L L₁, hs, h1, h2, h3, h4, c4.trans (le_max_left _ _), m s1,
    fun a => m (s2 a), fun a => m (s3 a), fun a => m (s4 a), fun a => m (s5 a)⟩, fun T hT => ?_⟩
  obtain ⟨L', hf, hw, hreg, hu, hne⟩ := cube_wave_nonvacuous hT
  obtain ⟨L₂, hL₂, hH⟩ := cube_wave_h1 T
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, max L' L₂, hf, hw, fun t ht =>
    ⟨(hH t ht).1.mono hL₂ (le_max_right _ _), (hH t ht).2.mono hL₂ (le_max_right _ _),
      (hreg t ht).2.2.1.trans (le_max_left _ _), (hreg t ht).2.2.2.trans (le_max_left _ _)⟩,
    hu, hne⟩

end FEEC
