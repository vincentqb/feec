module

public import Solution.CubeMain
public import Solution.CubeSobolev
public import Solution.CubeNonvac
public import Solution.CubeUnique
public import Solution.CrankNicolson

/-!
# Error guarantees for fully discrete finite element schemes on simplicial meshes (solution)

`FEEC.crankNicolson_cube`: the Freudenthal meshes are `Feec`'s (`cubeMesh`), the challenge's
Whitney spaces, interpolant and Crank–Nicolson step are `Feec`'s (`Solution.WhitneySpaces`,
`Solution.WhitneyInterp`, `Solution.WhitneyScheme`), and the error is
`Feec.Models.Cube.Inhomogeneous.RowSolution.whitney_cn_error_le_row` (`Solution.CrankNicolson`).
`FEEC.weakSymmetry_cube`: the cube data are `Feec`'s (`cubeData_eq`), the discretizations `cubeQ`
of the smoothed projections of one smoother satisfy the hypotheses of the abstract theorem
`FEEC.WeakSymmetryData.weakSymmetry_of` (`Solution.Abstract`, not compared here) with one
constant (`cube_hyps`), which gives unique solvability; their spaces are the elements of
Table 5.1 (`cubeQ_spaces`), the static rate is the abstract theorem with the interpolation
estimates (`cube_static_rate`), and the wave clauses are
`Feec.Models.Cube.WeakSymmetry.cubeWave_rate_tr'` and `cubeWave_exists_unique`
(`Solution.CubeWave`). The `H¹` rates (`Solution.CubeSobolev`) put the `H¹` classes in `Feec`'s
relative class `H¹_univ` (`Feec.Models.Cube.WeakSymmetry.sobRel_of_h1_zero` and its siblings).
`FEEC.weakSymmetry_cube_nonvacuous` from
`Feec.Models.Cube.WeakSymmetry.exists_coupled_manufactured_solution` and `waveManufactured_hyps`,
with `cube_static_h1` and `cube_wave_h1` for the `H¹` classes.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 5–7

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter

@[expose] public noncomputable section

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

open Feec.Models.Cube.Inhomogeneous hiding RowSolution in
theorem crankNicolson_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3) (C : ℝ), IsMeshFamily (cube 3) 𝒯 ∧
    IsFreudenthal 𝒯 ∧
    (∀ N k (w : FormField 3), Continuous w → ∃! x, IsWhitneyInterp (cube 3) (𝒯 N) k w x) ∧
    (∀ N Δt g u, RowMem (𝒯 N) false g → RowMem (𝒯 N) false u → ∃! u', IsCNStep (𝒯 N) Δt g u u') ∧
    (∀ N, ∃ v ∈ femSpaceMin (cube 3) (𝒯 N) topSeq 1, v ≠ 0) ∧
    ∀ N T L (X : RowSolution T L) (Δt : ℝ) (M : ℕ) (u g : ℕ → Row), 0 < Δt → M * Δt ≤ T →
      (∀ m < M, IsCNStep (𝒯 N) Δt (g (m + 1)) (u m) (u (m + 1))) →
      (∀ m < M, ∃ w, IsRowInterp (𝒯 N) (X.u ((m + 1 : ℕ) * Δt)) w ∧
        RowMem (𝒯 N) true (g (m + 1) - w)) →
      IsRowInterp (𝒯 N) (X.u 0) (u 0) → ∀ U : Row, IsRepr (cube 3) 0 (X.u (M * Δt) 0) U.1 →
        IsRepr (cube 3) 1 (X.u (M * Δt) 1) U.2.1 → IsRepr (cube 3) 2 (X.u (M * Δt) 2) U.2.2 →
        √(‖(u M - U).1‖ ^ 2 + ‖(u M - U).2.1‖ ^ 2 + ‖(u M - U).2.2‖ ^ 2) ≤
          C * L * (1 + T) * (meshSize (𝒯 N) + Δt ^ 2) := by
  refine ⟨cubeMesh, cnConst, isMeshFamily_cube, points_cube, ?_, ?_, ?_, ?_⟩
  · intro N k w hw
    exact ⟨FEMInterp.canonicalInterp N k ⟨w, hw⟩, (isWhitneyInterp_cube_iff N k ⟨w, hw⟩ _).2 rfl,
      fun x hx => (isWhitneyInterp_cube_iff N k ⟨w, hw⟩ _).1 hx⟩
  · intro N Δt g u hg hu
    obtain ⟨g', rfl⟩ := (rowMem_false_iff N g).1 hg
    obtain ⟨u', rfl⟩ := (rowMem_false_iff N u).1 hu
    obtain ⟨a, ha, hau⟩ := whitney_existsUnique_cnStep N (Δt / 2) 0 g' u'
    refine ⟨ofD N a, (isCNStep_ofD_iff N Δt g' u' _).2 ⟨a, rfl, ha⟩, fun x hx => ?_⟩
    obtain ⟨b, rfl, hb⟩ := (isCNStep_ofD_iff N Δt g' u' x).1 hx
    rw [hau b hb]
  · intro N
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (whitneyMin_one_ne_bot N)
    exact ⟨v, (mem_whitneyMin N 1).1 hv, hv0⟩
  · intro N T L X Δt M u g hΔt hM hstep hg hu0 U hU0 hU1 hU2
    have hL0 := zero_le_L X hΔt hM
    have hu : ∀ m ≤ M, RowMem (cubeMesh N) false (u m) := by
      intro m hm
      rcases m with _ | m
      · rw [ofD_interp X hu0]; exact (rowMem_false_iff N _).2 ⟨_, rfl⟩
      · exact (hstep m hm).1
    have hgm : ∀ m < M, ∃ c ∈ whitneyInterior N,
        g (m + 1) = ofD N (c + X.toFeec.interp N ((m + 1 : ℕ) * Δt)) := by
      intro m hm
      obtain ⟨w, hw, hgw⟩ := hg m hm
      obtain ⟨c, hc, hce⟩ := (rowMem_true_iff N _).1 hgw
      refine ⟨c, hc, ?_⟩
      rw [ofD_add, ← hce, ← ofD_interp X hw, sub_add_cancel]
    classical
    set a : ℕ → DState (whitneyRow N) := fun m =>
      if h : RowMem (cubeMesh N) false (u m) then ((rowMem_false_iff N _).1 h).choose else 0
      with hadef
    have ha : ∀ m ≤ M, u m = ofD N (a m) := fun m hm => by
      rw [hadef]; dsimp only; rw [dite_eq_left (hu m hm)]
      exact ((rowMem_false_iff N _).1 (hu m hm)).choose_spec
    set b : ℕ → DState (whitneyRow N) := fun m =>
      if h : RowMem (cubeMesh N) false (g m) then ((rowMem_false_iff N _).1 h).choose else 0
      with hbdef
    have hgM : ∀ m < M, RowMem (cubeMesh N) false (g (m + 1)) := fun m hm => by
      obtain ⟨c, -, hc⟩ := hgm m hm
      exact (rowMem_false_iff N _).2 ⟨_, hc⟩
    have hb : ∀ m < M, g (m + 1) = ofD N (b (m + 1)) := fun m hm => by
      rw [hbdef]; dsimp only; rw [dite_eq_left (hgM m hm)]
      exact ((rowMem_false_iff N _).1 (hgM m hm)).choose_spec
    have hstep' : ∀ m < M, Feec.TimeStepping.IsDirichletCNStep (whitneyInterior N)
        (discreteWave (whitneyRow N)) (Δt / 2) 0 (b (m + 1)) (a m) (a (m + 1)) := by
      intro m hm
      have h := hstep m hm
      rw [hb m hm, ha m hm.le, ha (m + 1) hm] at h
      obtain ⟨u', hu', h'⟩ := (isCNStep_ofD_iff N Δt _ _ _).1 h
      rwa [← ofD_injective N hu'] at h'
    have hg' : ∀ m < M, b (m + 1) - X.toFeec.interp N ((m + 1 : ℕ) * Δt) ∈ whitneyInterior N := by
      intro m hm
      obtain ⟨c, hc, hce⟩ := hgm m hm
      rw [hb m hm] at hce
      rw [ofD_injective N hce, add_sub_cancel_right]
      exact hc
    have hu0' : a 0 = X.toFeec.interp N 0 :=
      ofD_injective N ((ha 0 (Nat.zero_le M)).symm.trans (ofD_interp X hu0))
    have key := X.toFeec.whitney_cn_error_le_row N hΔt hL0 hM hstep' hg' hu0'
    rw [toRow_field X hU0 hU1 hU2, ha M le_rfl, ofD, ← toRow_sub, norm_toRow, meshSize_cubeMesh]
    exact key

set_option maxHeartbeats 2000000 in
theorem weakSymmetry_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3) (Q : ℕ → cubeData.Discretization)
    (C : ℝ), IsMeshFamily (cube 3) 𝒯 ∧ IsFreudenthal 𝒯 ∧
    (∀ N, ((Q N).V0 : Set (L2Form (cube 3) 0)) = femSpaceMin (cube 3) (𝒯 N) topSeq 0 ∧
      ((Q N).V1 : Set (L2Form (cube 3) 1)) = femSpaceMin (cube 3) (𝒯 N) topSeq 1 ∧
      ((Q N).V2 : Set (L2Form (cube 3) 2)) = femSpaceMin (cube 3) (𝒯 N) topSeq 2 ∧
      ((Q N).Vt0 : Set (L2Vec (cube 3) 0)) =
        {v | ∀ a, v a ∈ femSpaceMin (cube 3) (𝒯 N) bottomSeq 0} ∧
      ((Q N).Vt1 : Set (L2Vec (cube 3) 1)) =
        {v | ∀ a, v a ∈ femSpaceMin (cube 3) (𝒯 N) bottomSeq 1} ∧
      ((Q N).Vt2 : Set (L2Vec (cube 3) 2)) =
        {v | ∀ a, v a ∈ femSpaceMin (cube 3) (𝒯 N) bottomSeq 2}) ∧
    (∀ N, (Q N).IsBounded C ∧ (Q N).Compatible ∧ (Q N).IsConsistent C (meshSize (𝒯 N))) ∧
    (∀ N F, ∃! x : cubeData.d0.domain × cubeData.dt0.domain × cubeData.dt1.domain ×
      L2Form (cube 3) 1, (Q N).IsDiscreteSolution F x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
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
    fun N => ?_, fun N F => ?_, ⟨K, fun N F σ φ u lam σh φh uh lamh L hs hσ hφ hu hl hd => ?_⟩,
    ⟨Ks * cs, fun N F σ φ u lam σh φh uh lamh L hs hσ hφ hdφ hu hdu hl hd => ?_⟩,
    fun N T f σ φ u M ρ lam σ' φ' u' M' ρ' lam' hT0 _ h1 h2 e0' e1' e2' e3' =>
      cube_wave_unique hT hB N hT0 h1 h2 e0' e1' e2' e3', ?_, ?_⟩
  · rw [meshSize_cubeMesh]; exact hQ N
  · obtain ⟨K₀, hK₀⟩ := WeakSymmetryData.weakSymmetry_of C
    exact (hK₀ _ (cubeQ hT hB N) isBGG_𝒟 hS (hQ N).1 (hQ N).2.1).1 F
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
