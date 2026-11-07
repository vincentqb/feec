module

public import Solution.CubeMain
public import Solution.CubeSobolev
public import Solution.CubeNonvac
public import Solution.CubeUnique

/-!
# Finite element exterior calculus for the complex with weak symmetry (solution)

`FEEC.weakSymmetry` is `FEEC.WeakSymmetryData.weakSymmetry_of` (`Solution.Abstract`: the BGG data
and discretizations of the challenge as `Feec.BGG.Segment` and `Feec.BGG.Discrete`, then
`Feec.BGG.Discrete.existsUnique_mixed_h` and `Feec.BGG.Discrete.error_estimate_of_weakConsistency`
with the pointwise regular potentials of
`Feec.BGG.Discrete.weakConsistency_of_potential_of_bound`). `FEEC.weakSymmetry_cube`: the cube
data are `Feec`'s (`cubeData_eq`), the discretizations `cubeQ` of the smoothed projections of one
smoother satisfy the hypotheses of `FEEC.weakSymmetry` with one constant (`cube_hyps`), their
spaces are the elements of Table 5.1 (`cubeQ_spaces`) on the Freudenthal meshes (`cubeMesh`), the
static rate is the abstract theorem with the interpolation estimates (`cube_static_rate`), and the
wave clauses are `Feec.Models.Cube.WeakSymmetry.cubeWave_rate_tr'` and `cubeWave_exists_unique`
(`Solution.CubeWave`). The `H¹` rates (`Solution.CubeSobolev`) put the `H¹` classes in `Feec`'s
relative class `H¹_univ` (`Feec.Models.Cube.WeakSymmetry.sobRel_of_h1_zero` and its siblings) and
apply `cube_static_rate_sob` and `cube_wave_rate_sob`. `FEEC.weakSymmetry_cube_nonvacuous` from
`Feec.Models.Cube.WeakSymmetry.exists_coupled_manufactured_solution` and `waveManufactured_hyps`,
with `cube_static_h1` and `cube_wave_h1` for the `H¹` classes.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 5, 6

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter

@[expose] public noncomputable section

universe u

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

theorem weakSymmetry (C : ℝ) : ∃ K : ℝ, ∀ {W0 W1 W2 Wt0 Wt1 Wt2 : Type u}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [NormedAddCommGroup W1]
    [InnerProductSpace ℝ W1] [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
    [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0] [NormedAddCommGroup Wt1]
    [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
    (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2) (Q : D.Discretization), D.IsBGG →
    D.IsStable C → Q.IsBounded C → Q.Compatible →
    (∀ F, ∃! x : D.d0.domain × D.dt0.domain × D.dt1.domain × W1,
      Q.IsDiscreteSolution F x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
    ∀ (h Λ : ℝ), 0 ≤ h → Q.IsConsistent C h → ∀ F σ φ u lam σh φh uh lamh,
      D.IsSolution F σ φ u lam → ‖lam‖ ≤ Λ →
      (∀ w : D.d1.domain, |⟪D.S1 u, D.d1 w⟫_ℝ| ≤ Λ * ‖(w : W1)‖) →
      Q.IsDiscreteSolution F σh φh uh lamh →
      Q.errorSq σ σh φ φh u uh ≤ K * (Q.projErrorSq σ φ u + h ^ 2 * (Λ ^ 2 + ‖D.S1 u‖ ^ 2) +
        ‖D.S1 u - Q.π2 (D.S1 u)‖ ^ 2) :=
  WeakSymmetryData.weakSymmetry_of C

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

set_option maxHeartbeats 2000000 in
theorem weakSymmetry_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3) (Q : ℕ → cubeData.Discretization)
    (C : ℝ), IsMeshFamily (cube 3) 𝒯 ∧
    (∀ N, ∀ T ∈ (𝒯 N).simplices, ∃ (z : Fin 3 → Fin (N + 1)) (σ : Equiv.Perm (Fin 3)), ∀ j i,
      T.points j i = ((z i : ℝ) + if (σ.symm i : ℕ) < (j : ℕ) then 1 else 0) / (2 * (N + 1))) ∧
    (∀ N, ((Q N).V0 : Set (L2Form (cube 3) 0)) = femSpaceMin (cube 3) (𝒯 N) topSeq 0 ∧
      ((Q N).V1 : Set (L2Form (cube 3) 1)) = femSpaceMin (cube 3) (𝒯 N) topSeq 1 ∧
      ((Q N).V2 : Set (L2Form (cube 3) 2)) = femSpaceMin (cube 3) (𝒯 N) topSeq 2 ∧
      ((Q N).Vt0 : Set (L2Vec (cube 3) 0)) =
        {v | ∀ a, v a ∈ femSpaceMin (cube 3) (𝒯 N) bottomSeq 0} ∧
      ((Q N).Vt1 : Set (L2Vec (cube 3) 1)) =
        {v | ∀ a, v a ∈ femSpaceMin (cube 3) (𝒯 N) bottomSeq 1} ∧
      ((Q N).Vt2 : Set (L2Vec (cube 3) 2)) =
        {v | ∀ a, v a ∈ femSpaceMin (cube 3) (𝒯 N) bottomSeq 2}) ∧
    cubeData.IsBGG ∧ cubeData.IsStable C ∧
    (∀ N, (Q N).IsBounded C ∧ (Q N).Compatible ∧ (Q N).IsConsistent C (meshSize (𝒯 N))) ∧
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
  refine ⟨cubeMesh, cubeQ hT hB, C, isMeshFamily_cube, points_cube, cubeQ_spaces hT hB,
    isBGG_𝒟, hS, fun N => ?_, ⟨K, fun N F σ φ u lam σh φh uh lamh L hs hσ hφ hu hl hd => ?_⟩,
    ⟨Ks * cs, fun N F σ φ u lam σh φh uh lamh L hs hσ hφ hdφ hu hdu hl hd => ?_⟩,
    fun N T f σ φ u M ρ lam σ' φ' u' M' ρ' lam' hT0 _ h1 h2 e0' e1' e2' e3' =>
      cube_wave_unique hT hB N hT0 h1 h2 e0' e1' e2' e3', ?_, ?_⟩
  · rw [meshSize_cubeMesh]; exact hQ N
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
