module

public import Solution.GradCurl

/-!
# The verdicts of the natural boundary conditions

The clauses of `FEEC.tsd_boundary_conditions` for the system (4.14) with the boundary conditions
natural for its complex, read off `Feec` through `Solution.GradCurl`:

* `natural_of`: on every nonempty bounded open `Ω`, the invariant core
  (`Feec.Counterexamples.BoundedDomainTSD.invariantCore_tsd`), the datum `(0, E₀, β)`
  (`betaL2_not_propagates`), the projection hypothesis (`exists_projTSD_not_mem_domain`), the
  density (`not_dense_tsd_inter`), and the system (6.1) (`tsd_not_propagates_of` of
  `Solution.Bounded`);
* `starShaped_of`: on domains star-shaped with respect to a ball, `density_dichotomy` and
  `Feec.Models.BoundedDomain.not_coreSub_le_stationary_iff` with the complete set of eigenvectors
  `Feec.Models.StarShaped.StarDomain.eigenDense_gradCurl`;
* `ball_of`: `Feec.Counterexamples.BallEigenfields.eq_zero_of_isEigenfield_of_contDiff_ball`;
* `box_of`: `Feec.Counterexamples.BoxStationary.mem_invariantCore_tsd_iff_box` and
  `box_stationary_of` of `Solution.Box`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 ((4.14), Prop 4.17)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set MeasureTheory Filter Topology

@[expose] public noncomputable section

namespace FEEC

open Feec Feec.Domain Feec.Models.BoundedDomain Feec.Counterexamples.BoundedDomainTSD
open Feec.HilbertComplex (totalSub)
open Feec.ShortHilbertComplex (W3 family3 mk3 mem_totalSub_family3 inj₁ inj₂)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {Ω : Set (Fin 3 → ℝ)}

/-- The sets of TSD fields of `H̊(curl)`, and of TSD fields, through the electric field. -/
theorem tsd_inter_eq (hΩ : IsOpen Ω) :
    {u : L2Vec Ω 1 | IsTSD (mat1 u) ∧ u ∈ (vecOp fun _ => dMin Ω 1 :
        L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain} =
      fieldE ⁻¹' ((tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain :
        Submodule ℝ (L2F ℝ Ω Ix)) : Set (L2F ℝ Ω Ix)) := by
  ext u
  simp only [mem_ofPred_eq, mem_preimage, SetLike.mem_coe, Submodule.mem_inf, isTSD_iff,
    toIx_mat1, mem_dom_iff hΩ]
  rfl

theorem tsd_eq : {u : L2Vec Ω 1 | IsTSD (mat1 u)} = fieldE ⁻¹' (tsd Ω : Set (L2F ℝ Ω Ix)) := by
  ext u
  simp only [mem_ofPred_eq, mem_preimage, SetLike.mem_coe, isTSD_iff, toIx_mat1]

theorem closure_preimage_fieldE (s : Set (L2F ℝ Ω Ix)) :
    closure (fieldE ⁻¹' s : Set (L2Vec Ω 1)) = fieldE ⁻¹' closure s :=
  ((fieldE (Ω := Ω)).toHomeomorph.preimage_closure s).symm

/-- **The invariant core on a nonempty bounded open `Ω`.** -/
theorem natural_core (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {S : ℝ → (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) →L[ℝ] (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2)}
    (hS : IsEvolution (gradCurlWave Ω) univ S) :
    ∃ (S₁ : Submodule ℝ (L2Vec Ω 1)) (S₂ : Submodule ℝ (L2Vec Ω 2)),
      IsClosed (S₁ : Set (L2Vec Ω 1)) ∧ IsClosed (S₂ : Set (L2Vec Ω 2)) ∧
      invariantCore S (tsdConstraint Ω) = {U | U.1 = 0 ∧ U.2.1 ∈ S₁ ∧ U.2.2 ∈ S₂} ∧
      (∀ u ∈ S₁, IsTSD₀ (mat1 u)) ∧ (∀ ρ ∈ S₂, IsTSD (mat2 ρ)) ∧
      (∃ u, IsTSD (mat1 u) ∧ u ∉ S₁) ∧ (∃ ρ, IsTSD (mat2 ρ) ∧ ρ ∉ S₂) ∧
      ∃ ρ ∈ S₂, ρ ≠ 0 ∧ ((0, 0, ρ), 0) ∈ gradCurlWave Ω := by
  obtain ⟨hcore, h1, h2, -, -, hd1, hd1', hd2, hne', hβ, hβ', -⟩ := invariantCore_tsd hΩ hb hne
  refine ⟨((gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω)).comap
      (fieldE (Ω := Ω)).toLinearEquiv.toLinearMap,
    ((gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω)).comap
      (fieldB (Ω := Ω)).toLinearEquiv.toLinearMap,
    (ShortHilbertComplex.isClosed_invariantCore₁ (S := gradCurl ℝ hΩ)).preimage
      fieldE.continuous,
    (ShortHilbertComplex.isClosed_invariantCore₂ (S := gradCurl ℝ hΩ)).preimage
      fieldB.continuous, ?_, fun u hu => (isTSD₀_iff hΩ hb u).2 (h1 hu),
    fun ρ hρ => (isTSD_iff _).2 (h2 hρ), ⟨fieldE.symm (constField hΩ hb diagA), ?_, ?_⟩,
    ⟨fieldB.symm (betaL2 hΩ hb), ?_, ?_⟩, fieldB.symm (constField hΩ hb diagA), ?_, ?_, ?_⟩
  · refine Set.ext fun U => ?_
    rw [gc_mem_invariantCore_iff hΩ hS, hcore, mem_totalSub_family3]
    change -field0 U.1 ∈ (⊥ : Submodule ℝ (L2F ℝ Ω (Fin 3))) ∧
      fieldE U.2.1 ∈ (gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω) ∧
      fieldB U.2.2 ∈ (gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω) ↔ _
    rw [Submodule.mem_bot, neg_eq_zero, LinearIsometryEquiv.map_eq_zero_iff]
    rfl
  · rw [isTSD_iff, toIx_mat1, LinearIsometryEquiv.apply_symm_apply]; exact hd1
  · show fieldE (fieldE.symm (constField hΩ hb diagA)) ∉
      (gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω)
    rw [LinearIsometryEquiv.apply_symm_apply]; exact hd1'
  · rw [isTSD_iff, toIx_mat2, LinearIsometryEquiv.apply_symm_apply]; exact hβ
  · show fieldB (fieldB.symm (betaL2 hΩ hb)) ∉ (gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω)
    rw [LinearIsometryEquiv.apply_symm_apply]; exact hβ'
  · show fieldB (fieldB.symm (constField hΩ hb diagA)) ∈
      (gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω)
    rw [LinearIsometryEquiv.apply_symm_apply]; exact hd2
  · rw [Ne, LinearIsometryEquiv.map_eq_zero_iff]; exact hne'
  · obtain ⟨hmem, e⟩ := smoothField_mem_adjoint hΩ hb (gradCurl ℝ hΩ) le_rfl
      (Ψ := fun ij _ => diagA ij.1 ij.2) (fun ij => contDiff_const)
    have e0 : (gradCurl ℝ hΩ).d₁† ⟨_, hmem⟩ = 0 := by
      rw [e]; exact smoothField_eq_zero hΩ hb _ fun ij x _ => by simp [curlM]
    refine (gc_mem_stationary_iff hΩ _).2 ?_
    rw [gcState_magnetic, LinearIsometryEquiv.apply_symm_apply]
    exact inj₂_mem_stationary hΩ hmem e0

/-- **The magnetic datum `β` on a nonempty bounded open `Ω`.** -/
theorem natural_beta (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ∃ ρ : L2Vec Ω 2, (∀ a b, ⇑(mat2 ρ a b) =ᵐ[volume.restrict Ω]
        fun x => if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then x 2 else 0) ∧
      (0, 0, ρ) ∈ tsdConstraint Ω ∧ (∃ V, ((0, 0, ρ), V) ∈ gradCurlWave Ω) ∧
      ∀ u T U, 0 < T → U 0 = (0, u, ρ) → IsStrongSolution (gradCurlWave Ω) (Icc 0 T) U →
        ∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (U t).2.1) := by
  obtain ⟨hβd, -⟩ := betaL2_mem_adjoint hΩ hb (gradCurl ℝ hΩ) le_rfl
  refine ⟨fieldB.symm (betaL2 hΩ hb), fun a b => ?_, ⟨rfl, ?_, ?_⟩, ?_,
    fun u T U hT hU0 hU => ?_⟩
  · change ⇑(fieldB (fieldB.symm (betaL2 hΩ hb)) (a, b)) =ᵐ[volume.restrict Ω] _
    rw [LinearIsometryEquiv.apply_symm_apply]
    refine (MemLp.coeFn_toLp (memLp_of_continuous hΩ.measurableSet hb
      (contDiff_betaField (a, b)).continuous)).trans (Eventually.of_forall fun x => ?_)
    simp only [betaField, Prod.mk.injEq]
    split_ifs <;> rfl
  · rw [isTSD_iff, toIx_mat1, map_zero]; exact Submodule.zero_mem _
  · rw [isTSD_iff, toIx_mat2, LinearIsometryEquiv.apply_symm_apply]; exact betaL2_mem_tsd hΩ hb
  · have hd := ShortHilbertComplex.inj₂_mem_wave_domain (S := gradCurl ℝ hΩ) hβd
    refine ⟨gcInv ((gradCurl ℝ hΩ).wave ⟨_, hd⟩), (gc_graph_iff hΩ _ _).2 ?_⟩
    rw [gcState_gcInv, gcState_magnetic, LinearIsometryEquiv.apply_symm_apply,
      HilbertComplex.generator_waveGroup]
    exact LinearPMap.mem_graph _ ⟨_, hd⟩
  · have hU' := isStrongSolution_toFeec field0 fieldE fieldB (gradCurl ℝ hΩ)
      (mem_graph_grad_iff hΩ) (mem_graph_curl_iff hΩ) hU
    obtain ⟨t, ht, hnot⟩ := betaL2_not_propagates hΩ hb hne (gradCurl ℝ hΩ) le_rfl hT hU'
      (by rw [hU0]; change -field0 (0 : L2Vec Ω 0) = 0; simp)
      (by rw [hU0]; change fieldB (fieldB.symm (betaL2 hΩ hb)) = _;
          rw [LinearIsometryEquiv.apply_symm_apply])
    exact ⟨t, ht, fun h => hnot (by rw [isTSD_iff, toIx_mat1] at h; exact h)⟩

/-- **The projection hypothesis fails on a nonempty bounded open `Ω`.** -/
theorem natural_proj (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ∃ u : L2Vec Ω 1, (∀ a b, ∃ φ, IsTestFn Ω φ ∧ ⇑(mat1 u a b) =ᵐ[volume.restrict Ω] φ) ∧
      ∀ v, IsTSD (mat1 v) → (∀ w, IsTSD (mat1 w) → ⟪u - v, w⟫_ℝ = 0) →
        v ∉ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain := by
  obtain ⟨Φ, hΦ, hnot⟩ := exists_projTSD_not_mem_domain hΩ hb hne
  refine ⟨fieldE.symm (testField hΦ), fun a b => ⟨Φ (a, b), isTestFn_of (hΦ (a, b)), ?_⟩,
    fun v hv hvo hvd => hnot ?_⟩
  · change ⇑(fieldE (fieldE.symm (testField hΦ)) (a, b)) =ᵐ[volume.restrict Ω] _
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact coeFn_testField hΦ (a, b)
  · have hv' : fieldE v ∈ tsd Ω := by rw [← toIx_mat1, ← isTSD_iff]; exact hv
    have e : (tsd Ω).starProjection (testField hΦ) = fieldE v :=
      Submodule.eq_starProjection_of_mem_of_inner_eq_zero hv' fun w hw => by
        have h := hvo (fieldE.symm w)
          (by rw [isTSD_iff, toIx_mat1, LinearIsometryEquiv.apply_symm_apply]; exact hw)
        rw [← LinearIsometryEquiv.inner_map_map fieldE, map_sub,
          LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply] at h
        exact h
    rw [e]; exact (mem_dom_iff hΩ v).1 hvd

/-- **`L²(TSD) ∩ H̊(curl)` is not dense in `L²(TSD)` on a nonempty bounded open `Ω`.** -/
theorem natural_dense (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    closure {u : L2Vec Ω 1 | IsTSD (mat1 u) ∧ u ∈ (vecOp fun _ => dMin Ω 1 :
      L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain} ≠ {u | IsTSD (mat1 u)} := by
  intro h
  refine not_dense_tsd_inter hΩ hb hne (SetLike.coe_injective ?_)
  rw [tsd_inter_eq hΩ, tsd_eq, closure_preimage_fieldE] at h
  rw [Submodule.topologicalClosure_coe]
  exact (fieldE (Ω := Ω)).surjective.preimage_injective h

/-- **The boundary conditions natural for the complex, on a nonempty bounded open `Ω`.** -/
theorem natural_of (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    (∃ S, IsEvolution (gradCurlWave Ω) univ S) ∧
      (∀ S, IsEvolution (gradCurlWave Ω) univ S →
        ∃ (S₁ : Submodule ℝ (L2Vec Ω 1)) (S₂ : Submodule ℝ (L2Vec Ω 2)),
          IsClosed (S₁ : Set (L2Vec Ω 1)) ∧ IsClosed (S₂ : Set (L2Vec Ω 2)) ∧
          invariantCore S (tsdConstraint Ω) = {U | U.1 = 0 ∧ U.2.1 ∈ S₁ ∧ U.2.2 ∈ S₂} ∧
          (∀ u ∈ S₁, IsTSD₀ (mat1 u)) ∧ (∀ ρ ∈ S₂, IsTSD (mat2 ρ)) ∧
          (∃ u, IsTSD (mat1 u) ∧ u ∉ S₁) ∧ (∃ ρ, IsTSD (mat2 ρ) ∧ ρ ∉ S₂) ∧
          ∃ ρ ∈ S₂, ρ ≠ 0 ∧ ((0, 0, ρ), 0) ∈ gradCurlWave Ω) ∧
      (∃ ρ : L2Vec Ω 2, (∀ a b, ⇑(mat2 ρ a b) =ᵐ[volume.restrict Ω]
          fun x => if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then x 2 else 0) ∧
        (0, 0, ρ) ∈ tsdConstraint Ω ∧ (∃ V, ((0, 0, ρ), V) ∈ gradCurlWave Ω) ∧
        ∀ u T U, 0 < T → U 0 = (0, u, ρ) → IsStrongSolution (gradCurlWave Ω) (Icc 0 T) U →
          ∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (U t).2.1)) ∧
      (∃ u : L2Vec Ω 1, (∀ a b, ∃ φ, IsTestFn Ω φ ∧ ⇑(mat1 u a b) =ᵐ[volume.restrict Ω] φ) ∧
        ∀ v, IsTSD (mat1 v) → (∀ w, IsTSD (mat1 w) → ⟪u - v, w⟫_ℝ = 0) →
          v ∉ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain) ∧
      closure {u : L2Vec Ω 1 | IsTSD (mat1 u) ∧ u ∈ (vecOp fun _ => dMin Ω 1 :
        L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain} ≠ {u | IsTSD (mat1 u)} ∧
      ∃ U₀, (∃ V, (bggData Ω).IsWave U₀ V) ∧ IsTSDState U₀ ∧ ∀ T > 0,
        (∃ U, U 0 = U₀ ∧ IsStrongSolution {p | (bggData Ω).IsWave p.1 p.2} (Icc 0 T) U) ∧
        ∀ U, U 0 = U₀ → IsStrongSolution {p | (bggData Ω).IsWave p.1 p.2} (Icc 0 T) U →
          (∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (U t).2.1)) ∧
          ∃ t ∈ Icc 0 T, ∃ a i, mat2 (U t).2.2.2 a i ≠ mat2 (U t).2.2.2 i a :=
  ⟨⟨_, gc_isEvolution hΩ⟩, fun _ hS => natural_core hΩ hb hne hS, natural_beta hΩ hb hne,
    natural_proj hΩ hb hne, natural_dense hΩ hb hne, tsd_not_propagates_of hΩ hb hne⟩

/-- **Domains star-shaped with respect to a ball.** -/
theorem starShaped_of (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (hstar : ∃ x₀ s, 0 < s ∧ ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    closure {u : L2Vec Ω 1 | IsTSD (mat1 u) ∧ u ∈ (vecOp fun _ => dMin Ω 1 :
        L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain} = {u | IsTSD₀ (mat1 u)} ∧
      ∀ S, IsEvolution (gradCurlWave Ω) univ S →
        (invariantCore S (tsdConstraint Ω) ⊆ {U | (U, 0) ∈ gradCurlWave Ω} ↔
          ¬∃ ξ > 0, ∃ v : L2Vec Ω 1, v ≠ 0 ∧ IsTSD (mat1 v) ∧ IsEigenfield Ω ξ v ∧
            ∀ h, ¬∃ w ∈ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain,
              mat1 w = mat2 ((vecOp fun _ => dMin Ω 1) ⟨v, h⟩)) := by
  obtain ⟨x₀, s, hs, hst⟩ := hstar
  refine ⟨?_, fun S hS => ?_⟩
  · have e := (density_dichotomy hΩ hb hne hs hst).2.1
    rw [tsd_inter_eq hΩ, closure_preimage_fieldE, ← Submodule.topologicalClosure_coe, e]
    ext u
    simp only [mem_preimage, SetLike.mem_coe, mem_ofPred_eq, isTSD₀_iff hΩ hb]
  · obtain ⟨r, hr⟩ := hb.subset_closedBall x₀
    let D : Feec.Models.StarShaped.StarDomain 3 :=
      { Ω := Ω, isOpen := hΩ, x₀ := x₀, s₀ := s, R := max r 1, s₀_pos := hs,
        R_pos := lt_max_of_lt_right one_pos, starBall := hst,
        norm_sub_le := fun y hy => by
          rw [← dist_eq_norm]
          exact (Metric.mem_closedBall.1
            ((Metric.isClosed_closedBall.closure_subset_iff.2 hr) hy)).trans (le_max_left _ _) }
    have hD : (gradCurl ℝ hΩ).EigenDense := D.eigenDense_gradCurl
    have hle : invariantCore S (tsdConstraint Ω) ⊆ {U | (U, 0) ∈ gradCurlWave Ω} ↔
        (gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω) ≤ (gradCurl ℝ hΩ).stationary := by
      constructor
      · intro h y hy
        have hx : gcInv y ∈ invariantCore S (tsdConstraint Ω) := by
          rw [gc_mem_invariantCore_iff hΩ hS, gcState_gcInv]; exact hy
        have := (gc_mem_stationary_iff hΩ _).1 (h hx)
        rwa [gcState_gcInv] at this
      · intro h x hx
        exact (gc_mem_stationary_iff hΩ x).2 (h ((gc_mem_invariantCore_iff hΩ hS x).1 hx))
    rw [hle, ← not_iff_not, not_not, not_coreSub_le_stationary_iff hΩ hb hD]
    constructor
    · rintro ⟨ξ, hξ, v', hv'0, hv', hE, hc⟩
      refine ⟨ξ, hξ, fieldE.symm v', ?_, ?_, ?_, ?_⟩
      · rw [Ne, LinearIsometryEquiv.map_eq_zero_iff]; exact hv'0
      · rw [isTSD_iff, toIx_mat1, LinearIsometryEquiv.apply_symm_apply]; exact hv'
      · rw [isEigenfield_iff hΩ, LinearIsometryEquiv.apply_symm_apply]; exact hE
      · rw [curl_not_mem_iff hΩ]
        simpa only [LinearIsometryEquiv.apply_symm_apply] using hc
    · rintro ⟨ξ, hξ, v, hv0, hv, hE, hc⟩
      refine ⟨ξ, hξ, fieldE v, ?_, ?_, (isEigenfield_iff hΩ ξ v).1 hE,
        (curl_not_mem_iff hΩ v).1 hc⟩
      · rw [Ne, LinearIsometryEquiv.map_eq_zero_iff]; exact hv0
      · rw [← toIx_mat1, ← isTSD_iff]; exact hv

theorem unitBall_eq : unitBall = Feec.Counterexamples.BallSymTSD.ball3 := by
  ext x
  simp [unitBall, Feec.Counterexamples.BallSymTSD.ball3, Feec.Counterexamples.BallSymTSD.rho,
    Fin.sum_univ_three, sq]

theorem ball_of_eq (hΩ : Ω = Feec.Counterexamples.BallSymTSD.ball3) {ξ : ℝ} (hξ : ξ ≠ 0)
    (v : L2Vec Ω 1) (hv : IsTSD (mat1 v)) (hE : IsEigenfield Ω ξ v) {O : Set (Fin 3 → ℝ)}
    (hO : IsOpen O) (hBO : {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 1} ⊆ O)
    {Φ : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ} (hΦ : ∀ a b, ContDiffOn ℝ 2 (Φ a b) O)
    (hvΦ : ∀ a b, ⇑(mat1 v a b) =ᵐ[volume.restrict Ω] Φ a b) : v = 0 := by
  subst hΩ
  have h := Feec.Counterexamples.BallEigenfields.eq_zero_of_isEigenfield_of_contDiff_ball hξ
    (v := fieldE v) (by rw [← toIx_mat1, ← isTSD_iff]; exact hv)
    ((isEigenfield_iff Feec.Counterexamples.BallSymTSD.isOpen_ball3 ξ v).1 hE) hO
    (fun x hx => hBO (by
      simpa [Feec.Counterexamples.BallSymTSD.rho, Fin.sum_univ_three, sq] using hx))
    (U := fun ij => Φ ij.1 ij.2) (fun ij => hΦ _ _) (fun ij => hvΦ _ _)
  exact (LinearIsometryEquiv.map_eq_zero_iff fieldE).1 h

/-- **The unit ball.** -/
theorem ball_of : ∀ ξ ≠ 0, ∀ v : L2Vec unitBall 1, IsTSD (mat1 v) → IsEigenfield unitBall ξ v →
    (∃ O : Set (Fin 3 → ℝ), IsOpen O ∧ {x | ∑ i, x i ^ 2 ≤ 1} ⊆ O ∧
      ∃ Φ : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ, (∀ a b, ContDiffOn ℝ 2 (Φ a b) O) ∧
        ∀ a b, ⇑(mat1 v a b) =ᵐ[volume.restrict unitBall] Φ a b) → v = 0 :=
  fun _ hξ v hv hE ⟨_, hO, hBO, _, hΦ, hvΦ⟩ => ball_of_eq unitBall_eq hξ v hv hE hO hBO hΦ hvΦ

/-- **Boxes.** -/
theorem box_of {a ℓ : Fin 3 → ℝ} (hℓ : ∀ i, 0 < ℓ i) :
    (∀ S, IsEvolution (gradCurlWave (box a ℓ)) univ S →
        invariantCore S (tsdConstraint (box a ℓ)) =
          tsdConstraint (box a ℓ) ∩ {U | (U, 0) ∈ gradCurlWave (box a ℓ)} ∧
        ∀ U ∈ invariantCore S (tsdConstraint (box a ℓ)), U.2.1 = 0) ∧
      ∀ (S₁ : Submodule ℝ (L2Vec (box a ℓ) 1)) (S₂ : Submodule ℝ (L2Vec (box a ℓ) 2)),
        (∀ u ∈ S₁, IsTSD (mat1 u)) → (∀ ρ ∈ S₂, IsTSD (mat2 ρ)) → ∀ U,
          IsStrongSolution (gradCurlWave (box a ℓ)) (Ici 0) U →
          ((∀ t ≥ 0, (U t).1 = 0 ∧ (U t).2.1 ∈ S₁ ∧ (U t).2.2 ∈ S₂) ↔
            ((U 0).1 = 0 ∧ (U 0).2.1 ∈ S₁ ∧ (U 0).2.2 ∈ S₂) ∧
              (U 0, 0) ∈ gradCurlWave (box a ℓ)) := by
  have hΩ : IsOpen (box a ℓ) := Feec.Models.Box.isOpen_openBox a ℓ
  refine ⟨fun S hS => ?_, (box_stationary_of hℓ).2⟩
  have key : ∀ U, U ∈ invariantCore S (tsdConstraint (box a ℓ)) ↔
      ∃ B ∈ tsd (box a ℓ), ∃ h : B ∈ ((gradCurl ℝ hΩ).d₁†).domain,
        (gradCurl ℝ hΩ).d₁† ⟨B, h⟩ = 0 ∧
          gcState U = inj₂ (𝕜 := ℝ) (L2F ℝ (box a ℓ) (Fin 3)) (L2F ℝ (box a ℓ) Ix)
            (L2F ℝ (box a ℓ) Ix) B := fun U => by
    rw [gc_mem_invariantCore_iff hΩ hS]
    exact Feec.Counterexamples.BoxStationary.mem_invariantCore_tsd_iff_box hℓ (gcState U)
  refine ⟨Set.ext fun U => ⟨fun hU => ⟨?_, ?_⟩, fun ⟨hK, h0⟩ => ?_⟩, fun U hU => ?_⟩
  · have := hU 0; rwa [hS.1] at this
  · obtain ⟨B, -, h, e0, e⟩ := (key U).1 hU
    refine (gc_mem_stationary_iff hΩ U).2 ?_
    rw [e]; exact inj₂_mem_stationary hΩ h e0
  · intro t
    have hst := C0Group.mem_stationary.1 ((gc_mem_stationary_iff hΩ U).1 h0) t
    rw [gc_eq_of_isEvolution hΩ hS, hst, gcInv_gcState]
    exact hK
  · obtain ⟨B, -, -, -, e⟩ := (key U).1 hU
    have e1 := congrArg (fun y : PiLp 2 (W3 (L2F ℝ (box a ℓ) (Fin 3)) (L2F ℝ (box a ℓ) Ix)
      (L2F ℝ (box a ℓ) Ix)) => (y 1 : L2F ℝ (box a ℓ) Ix)) e
    change fieldE U.2.1 = (0 : L2F ℝ (box a ℓ) Ix) at e1
    exact (LinearIsometryEquiv.map_eq_zero_iff fieldE).1 e1

end FEEC
