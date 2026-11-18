module

public import Solution.CubeMain
public import Solution.CubeSobolev
public import Solution.CubeNonvac
public import Solution.CubeUnique
public import Solution.Bounded
public import Solution.MirrorTheorems
public import Solution.Instance
public import Solution.Box

/-!
# Constraint preservation for the linearized Einstein–Bianchi equations (solution)

`FEEC.bggWeakSymmetry`: `WeakSymmetryData.weakSymmetry_of` (Prop 5.4, Thm 5.5,
`Solution.Abstract`), `IsDiscreteWave.eq_of_eq` and `IsDiscreteWave.isGauss`
(`Solution.DiscreteWave`). `FEEC.tsd_not_propagates`: the datum `(0, 0, 0, ⋆β)` of
`Solution.Bounded` (`tsd_not_propagates_of`). `FEEC.box_stationary`: `Solution.Box`
(`box_stationary_of`).
`FEEC.mirror_tsd_propagates` and `FEEC.mirror_weakSymmetry_cube`: the challenge's TSD states are
the real parts of constrained states of `Feec`'s mirror complex (`Solution.MirrorState`,
`Solution.MirrorChain`), and the mirror scheme is `Feec`'s (`mirror_fem_main`); see
`Solution.MirrorTheorems`. `FEEC.weakSymmetry_cube` and `FEEC.weakSymmetry_cube_nonvacuous`: the
cube data are `Feec`'s (`cubeData_eq`); `cube_hyps`, `cubeQ_spaces`, `femSpace_univ_eq`,
`cube_S0h_ne`, `cube_bestApprox`, `cube_static_rate`, `cube_wave_rate`, `cube_wave_unique`,
`cube_static_nonvacuous`, `cube_wave_nonvacuous`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 5, Ch. 6

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter

@[expose] public noncomputable section

universe u

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

theorem toSmooth {L : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2} {ρ : Wv W2}
    (h : IsRegularState L (σ : W0) (incl0 φ) (incl1 u) M ρ) : IsSmoothStateTr L σ φ u M ρ :=
  ⟨(isTangentialC2_iff le_rfl L _).1 h.1, fun a => (isTangentialC2_iff le_rfl L _).1 (h.2.1 a),
    fun a => (isTangentialC2_iff zero_le_one L _).1 (h.2.2.1 a),
    (isTangentialC2_iff zero_le_two L _).1 h.2.2.2.1,
    fun a => (isTangentialC2_iff zero_le_two L _).1 (h.2.2.2.2 a)⟩

theorem ofSmooth {L : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2} {ρ : Wv W2}
    (h : IsSmoothStateTr L σ φ u M ρ) : IsRegularState L (σ : W0) (incl0 φ) (incl1 u) M ρ :=
  ⟨(isTangentialC2_iff le_rfl L _).2 h.1, fun a => (isTangentialC2_iff le_rfl L _).2 (h.2.1 a),
    fun a => (isTangentialC2_iff zero_le_one L _).2 (h.2.2.1 a),
    (isTangentialC2_iff zero_le_two L _).2 h.2.2.2.1,
    fun a => (isTangentialC2_iff zero_le_two L _).2 (h.2.2.2.2 a)⟩

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

theorem tsd_not_propagates {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : ∃ U₀, (∃ V, (bggData Ω).IsWave U₀ V) ∧ IsTSDState U₀ ∧ ∀ T > 0,
      (∃ U, U 0 = U₀ ∧ IsStrongSolution {p | (bggData Ω).IsWave p.1 p.2} (Icc 0 T) U) ∧
      ∀ U, U 0 = U₀ → IsStrongSolution {p | (bggData Ω).IsWave p.1 p.2} (Icc 0 T) U →
        (∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (U t).2.1)) ∧
        ∃ t ∈ Icc 0 T, ∃ a i, mat2 (U t).2.2.2 a i ≠ mat2 (U t).2.2.2 i a :=
  tsd_not_propagates_of hΩ hb hne

theorem box_stationary {a ℓ : Fin 3 → ℝ} (hℓ : ∀ i, 0 < ℓ i) :
    let L := IsHodgeWave (vecOp fun _ => dMin (box a ℓ) 0) (vecOp fun _ => dMin (box a ℓ) 1)
    (∀ U₀ V, L U₀ V → ∃ U, U 0 = U₀ ∧ IsStrongSolution {p | L p.1 p.2} (Ici 0) U) ∧
    ∀ (S₁ : Submodule ℝ (L2Vec (box a ℓ) 1)) (S₂ : Submodule ℝ (L2Vec (box a ℓ) 2)),
      (∀ u ∈ S₁, IsTSD (mat1 u)) → (∀ ρ ∈ S₂, IsTSD (mat2 ρ)) → ∀ U,
        IsStrongSolution {p | L p.1 p.2} (Ici 0) U →
        ((∀ t ≥ 0, (U t).1 = 0 ∧ (U t).2.1 ∈ S₁ ∧ (U t).2.2 ∈ S₂) ↔
          ((U 0).1 = 0 ∧ (U 0).2.1 ∈ S₁ ∧ (U 0).2.2 ∈ S₂) ∧ L (U 0) 0) :=
  box_stationary_of hℓ

theorem mirror_tsd_propagates :
    (∀ T U U', IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T) U →
      IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T) U' → U 0 = U' 0 →
        EqOn U U' (Icc 0 T)) ∧
    (∀ U₀ V, mirrorData.IsWave U₀ V → IsTSDState U₀ → ∀ T,
      ∃ U, U 0 = U₀ ∧ IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T) U) ∧
    (∀ T U, IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T) U → IsTSDState (U 0) →
      ∀ t ∈ Icc 0 T, IsTSDState (U t)) ∧
    ∃ U₀ V₁ V₂ V₃, mirrorData.IsWave U₀ V₁ ∧ mirrorData.IsWave V₁ V₂ ∧
      mirrorData.IsWave V₂ V₃ ∧ IsTSDState U₀ ∧ V₁ ≠ 0 :=
  mirror_tsd_propagates_of

theorem mirror_weakSymmetry_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3)
    (Q : ℕ → mirrorData.Discretization) (C K : ℝ), IsTable51 𝒯 Q C ∅ (fun a => {a}) ∧
    mirrorData.IsBGG ∧
    (∀ T, 0 < T → ∀ᶠ N in atTop, ∃ σ φ u M ρ lam, (Q N).IsDiscreteWave T 0 σ φ u M ρ lam ∧
      (Q N).IsGauss (σ 0) (u 0) ∧ (u 0 : L2Vec (cube 3) 1) ≠ 0 ∧ ∃ t ∈ Ioc 0 T, M t ≠ M 0) ∧
    ∀ N T U₀ V₁ V₂ V₃ U, 0 < T → mirrorData.IsWave U₀ V₁ → mirrorData.IsWave V₁ V₂ →
      mirrorData.IsWave V₂ V₃ → IsTSDState U₀ → U 0 = U₀ →
      IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T) U →
      ∃ σh φh uh Mh ρh lamh, (Q N).IsDiscreteWave T 0 σh φh uh Mh ρh lamh ∧ ∀ t ∈ Icc 0 T,
        √(‖(σh t : L2Form (cube 3) 0)‖ ^ 2 + ‖(U t).2.1 - uh t‖ ^ 2 + ‖Mh t‖ ^ 2 +
          ‖(U t).2.2.2 - ρh t‖ ^ 2) ≤
        K * (stateNorm U₀ + stateNorm V₁ + stateNorm V₂ + stateNorm V₃) * (1 + t) *
          meshSize (𝒯 N) :=
  mirror_weakSymmetry_cube_of

set_option maxHeartbeats 2000000 in
theorem weakSymmetry_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3) (Q : ℕ → cubeData.Discretization)
    (C : ℝ), IsTable51 𝒯 Q C Finset.univ (fun _ => Finset.univ) ∧ cubeData.IsBGG ∧
    cubeData.IsStable C ∧ (∀ N, 2 ≤ N → ∃ ψ : cubeData.dt0.domain,
      (ψ : L2Vec (cube 3) 0) ∈ (Q N).Vt0 ∧ (Q N).π1 (cubeData.S0 ψ) ≠ cubeData.S0 ψ) ∧
    (∃ c > 0, ∀ N, 2 ≤ N → ∃ v : cubeData.dt1.domain, (v : L2Vec (cube 3) 1) ∈ (Q N).Vt1 ∧
      (v : L2Vec (cube 3) 1) ≠ 0 ∧ ∀ w ∈ (Q N).V2,
        c * √(‖(v : L2Vec (cube 3) 1)‖ ^ 2 + ‖cubeData.dt1 v‖ ^ 2) ≤ ‖cubeData.S1 v - w‖) ∧
    (∃ K, ∀ N F σ φ u lam σh φh uh lamh L, cubeData.IsSolution F σ φ u lam →
      IsTangentialC2 0 L (σ : L2Form (cube 3) 0) →
      (∀ a, IsTangentialC2 0 L ((φ : L2Vec (cube 3) 0) a)) →
      (∀ a, IsTangentialC2 1 L ((u : L2Vec (cube 3) 1) a)) → ‖lam‖ ≤ L →
      (Q N).IsDiscreteSolution F σh φh uh lamh →
      (Q N).errorSq σ σh φ φh u uh ≤ (K * L * meshSize (𝒯 N)) ^ 2) ∧
    (∃ K, ∀ N F σ φ u lam σh φh uh lamh L, cubeData.IsSolution F σ φ u lam →
      IsSobolevForm (cube 3) 1 0 L (σ : L2Form (cube 3) 0) →
      (∀ a, IsSobolevForm (cube 3) 1 0 L ((φ : L2Vec (cube 3) 0) a)) →
      (∀ a, IsSobolevForm (cube 3) 1 1 L (cubeData.dt0 φ a)) →
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((u : L2Vec (cube 3) 1) a)) →
      (∀ a, IsSobolevForm (cube 3) 1 2 L (cubeData.dt1 u a)) → ‖lam‖ ≤ L →
      (Q N).IsDiscreteSolution F σh φh uh lamh →
      (Q N).errorSq σ σh φ φh u uh ≤ (K * L * meshSize (𝒯 N)) ^ 2) ∧
    (∀ N T f σ φ u M ρ lam σ' φ' u' M' ρ' lam', 0 < T → ContinuousOn f (Icc 0 T) →
      (Q N).IsDiscreteWave T f σ φ u M ρ lam → (Q N).IsDiscreteWave T f σ' φ' u' M' ρ' lam' →
      σ 0 = σ' 0 → u 0 = u' 0 → M 0 = M' 0 → ρ 0 = ρ' 0 →
      (∀ t ∈ Icc 0 T, σ t = σ' t ∧ u t = u' t ∧ M t = M' t ∧ ρ t = ρ' t) ∧
        ∀ t ∈ Ico 0 T, φ t = φ' t ∧ lam t = lam' t) ∧
    (∃ K, ∀ N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, 0 < T → ContinuousOn f (Icc 0 T) →
      cubeData.IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' →
      (∀ t ∈ Icc 0 T, IsRegularState L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsRegularState L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) →
      ∃ σh φh uh Mh ρh lamh, (Q N).IsDiscreteWave T f σh φh uh Mh ρh lamh ∧
        ∀ t ∈ Icc 0 T, √(‖(σ t : L2Form (cube 3) 0) - σh t‖ ^ 2 +
          ‖(u t : L2Vec (cube 3) 1) - uh t‖ ^ 2 + ‖M t - Mh t‖ ^ 2 + ‖ρ t - ρh t‖ ^ 2) ≤
            K * L * (1 + t) * meshSize (𝒯 N)) ∧
    ∃ K, ∀ N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, 0 < T → ContinuousOn f (Icc 0 T) →
      cubeData.IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' →
      (∀ t ∈ Icc 0 T, IsH1State L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsH1State L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) →
      ∃ σh φh uh Mh ρh lamh, (Q N).IsDiscreteWave T f σh φh uh Mh ρh lamh ∧
        ∀ t ∈ Icc 0 T, √(‖(σ t : L2Form (cube 3) 0) - σh t‖ ^ 2 +
          ‖(u t : L2Vec (cube 3) 1) - uh t‖ ^ 2 + ‖M t - Mh t‖ ^ 2 + ‖ρ t - ρh t‖ ^ 2) ≤
            K * L * (1 + t) * meshSize (𝒯 N) := by
  rw [cubeData_eq]
  obtain ⟨p, C₀, hT, hB, C, hS, hQ⟩ := cube_hyps
  obtain ⟨K, hK⟩ := cube_static_rate hT hB hS (fun N => (hQ N).1) (fun N => (hQ N).2.2)
  obtain ⟨Ks, hKs⟩ := cube_static_rate_sob hT hB hS (fun N => (hQ N).1) (fun N => (hQ N).2.2)
  obtain ⟨cs, hcs, hcsH⟩ := isSobolevStaticTr_of
  refine ⟨cubeMesh, cubeQ hT hB, C, ⟨isMeshFamily_cube, points_cube, fun N => ?_⟩, isBGG_𝒟, hS,
    cube_S0h_ne hT hB, cube_bestApprox hT hB,
    ⟨K, fun N F σ φ u lam σh φh uh lamh L hs hσ hφ hu hl hd => ?_⟩,
    ⟨Ks * cs, fun N F σ φ u lam σh φh uh lamh L hs hσ hφ hdφ hu hdu hl hd => ?_⟩,
    fun N T f σ φ u M ρ lam σ' φ' u' M' ρ' lam' hT0 _ h1 h2 e0' e1' e2' e3' =>
      cube_wave_unique hT hB N hT0 h1 h2 e0' e1' e2' e3', ?_, ?_⟩
  · obtain ⟨s0, s1, s2, s3, s4, s5⟩ := cubeQ_spaces hT hB N
    simp only [femSpace_univ_eq]
    refine ⟨s0, s1, s2, s3, s4, s5, (hQ N).1, (hQ N).2.1, ?_⟩
    rw [meshSize_cubeMesh]; exact (hQ N).2.2
  · rw [meshSize_cubeMesh]
    exact hK N F σ φ u lam σh φh uh lamh L hs ((isTangentialC2_iff le_rfl L _).1 hσ)
      (fun a => (isTangentialC2_iff le_rfl L _).1 (hφ a))
      (fun a => (isTangentialC2_iff zero_le_one L _).1 (hu a)) hl hd
  · rw [meshSize_cubeMesh]
    have hL0 : 0 ≤ L := (norm_nonneg _).trans hl
    have h := hKs N F σ φ u lam σh φh uh lamh (cs * L) hs
      (hcsH hL0 hs.2.2 hσ hφ hdφ hu hdu) (hl.trans (le_mul_of_one_le_left hL0 hcs)) hd
    exact h.trans_eq (by ring)
  · obtain ⟨K', hK'⟩ := cube_wave_rate hT hB
    refine ⟨K', fun N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L hT0 hf hw hreg => ?_⟩
    rw [meshSize_cubeMesh]
    exact hK' N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L hT0 hf hw fun t ht =>
      ⟨toSmooth (hreg t ht).1, toSmooth (hreg t ht).2.1, (hreg t ht).2.2.1, (hreg t ht).2.2.2⟩
  · obtain ⟨K', hK'⟩ := cube_wave_rate_sob hT hB
    obtain ⟨cw, hcw, hcwH⟩ := isSobolevStateTr_of
    refine ⟨K' * cw, fun N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L hT0 hf hw hreg => ?_⟩
    rw [meshSize_cubeMesh]
    have hL0 : 0 ≤ L := (norm_nonneg _).trans (hreg 0 ⟨le_rfl, hT0.le⟩).2.2.1
    obtain ⟨σh, φh, uh, Mh, ρh, lamh, hd, hr⟩ :=
      hK' N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' (cw * L) hT0 hf hw fun t ht =>
        ⟨hcwH (φ := e0 (φ t)) (u := e1 (u t)) hL0 (hreg t ht).1,
          hcwH (φ := e0 (φ' t)) (u := e1 (u' t)) hL0 (hreg t ht).2.1,
          (hreg t ht).2.2.1.trans (le_mul_of_one_le_left hL0 hcw),
          (hreg t ht).2.2.2.trans (le_mul_of_one_le_left hL0 hcw)⟩
    exact ⟨σh, φh, uh, Mh, ρh, lamh, hd, fun t ht => (hr t ht).trans_eq (by ring)⟩

theorem weakSymmetry_cube_nonvacuous :
    (∃ F σ φ u lam L, cubeData.IsSolution F σ φ u lam ∧ (σ : L2Form (cube 3) 0) ≠ 0 ∧
      (φ : L2Vec (cube 3) 0) ≠ 0 ∧ (u : L2Vec (cube 3) 1) ≠ 0 ∧ lam ≠ 0 ∧
      IsTangentialC2 0 L (σ : L2Form (cube 3) 0) ∧
      (∀ a, IsTangentialC2 0 L ((φ : L2Vec (cube 3) 0) a)) ∧
      (∀ a, IsTangentialC2 1 L ((u : L2Vec (cube 3) 1) a)) ∧ ‖lam‖ ≤ L ∧
      IsSobolevForm (cube 3) 1 0 L (σ : L2Form (cube 3) 0) ∧
      (∀ a, IsSobolevForm (cube 3) 1 0 L ((φ : L2Vec (cube 3) 0) a)) ∧
      (∀ a, IsSobolevForm (cube 3) 1 1 L (cubeData.dt0 φ a)) ∧
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((u : L2Vec (cube 3) 1) a)) ∧
      ∀ a, IsSobolevForm (cube 3) 1 2 L (cubeData.dt1 u a)) ∧
    ∀ T, 0 < T → ∃ f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, ContinuousOn f (Icc 0 T) ∧
      cubeData.IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' ∧
      (∀ t ∈ Icc 0 T, IsRegularState L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsRegularState L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧
        IsH1State L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsH1State L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) ∧
      (∀ t, (u t : L2Vec (cube 3) 1) ≠ 0) ∧
      ∀ t ∈ Ioc 0 T, (σ t : L2Form (cube 3) 0) ≠ 0 ∧ (φ t : L2Vec (cube 3) 0) ≠ 0 := by
  rw [cubeData_eq]
  obtain ⟨L, hs, h1, h2, h3, h4, c1, c2, c3, c4⟩ := cube_static_nonvacuous
  obtain ⟨L₁, hL₁, s1, s2, s3, s4, s5⟩ := cube_static_h1
  have m := fun {j : ℤ} {x : L2Form (cube 3) j} (h : IsSobolevForm (cube 3) 1 j L₁ x) =>
    isSobolevForm_mono hL₁ (le_max_right L L₁) h
  refine ⟨⟨_, _, _, _, _, max L L₁, hs, h1, h2, h3, h4,
    (isTangentialC2_iff le_rfl _ _).2 (c1.mono (le_max_left _ _)),
    fun a => (isTangentialC2_iff le_rfl _ _).2 ((c2 a).mono (le_max_left _ _)),
    fun a => (isTangentialC2_iff zero_le_one _ _).2 ((c3 a).mono (le_max_left _ _)),
    c4.trans (le_max_left _ _), m s1, fun a => m (s2 a), fun a => m (s3 a), fun a => m (s4 a),
    fun a => m (s5 a)⟩, fun T hT => ?_⟩
  obtain ⟨L', hf, hw, hreg, hu, hne⟩ := cube_wave_nonvacuous hT
  obtain ⟨L₂, hL₂, hH⟩ := cube_wave_h1 T
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, max L' L₂, hf, hw, fun t ht =>
    ⟨ofSmooth ((hreg t ht).1.mono (le_max_left _ _)),
      ofSmooth ((hreg t ht).2.1.mono (le_max_left _ _)),
      (hH t ht).1.mono hL₂ (le_max_right _ _), (hH t ht).2.mono hL₂ (le_max_right _ _),
      (hreg t ht).2.2.1.trans (le_max_left _ _), (hreg t ht).2.2.2.trans (le_max_left _ _)⟩,
    hu, hne⟩

end FEEC
