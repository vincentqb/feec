module

public import Solution.GradCurl
public import Feec.HilbertComplex.Reweight

/-!
# The verdicts of the electric boundary conditions

The verdicts `FEEC.ElectricVerdict`, `FEEC.StarShapedVerdict`, `FEEC.TSDVerdict.ball` and
`FEEC.BoxVerdict` for the system (4.14) with the electric boundary conditions, read off `Feec`
through `Solution.GradCurl`:

* `electric_of`: on every nonempty bounded open `Ω`, the invariant core
  (`Feec.Counterexamples.BoundedDomainTSD.invariantCore_tsd`); for every short complex whose `d¹`
  restricts the minimal curl, read through the fields (`exists_fieldComplex`), the datum
  `(0, E₀, β)` (`betaL2_mem_adjoint`, `beta_mem_domain`; `betaL2_not_propagates`,
  `beta_not_propagates`) and the projection hypothesis
  (`exists_projTSD_not_mem_domain_of_dense` on the dense `D(d₁) ∩ D(d₀†)`, and
  `exists_projTSD_not_mem_domain` for a test field; `electric_proj`); the density
  (`not_dense_tsd_inter`, monotone in `D(d¹)`); and the system (6.1) (`tsd_not_propagates_of`
  of `Solution.Bounded`);
* `starShaped_of`: on domains star-shaped with respect to a ball, `density_dichotomy` (both
  halves, `H(curl)` through `mem_domMax_iff`) and
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

/-- The TSD fields with rows in `H(curl)`, through the electric field. -/
theorem tsd_inter_max_eq (hΩ : IsOpen Ω) :
    {u : L2Vec Ω 1 | IsTSD (mat1 u) ∧ u ∈ (vecOp fun _ => dMax Ω 1 :
        L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain} =
      fieldE ⁻¹' ((tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain :
        Submodule ℝ (L2F ℝ Ω Ix)) : Set (L2F ℝ Ω Ix)) := by
  ext u
  simp only [mem_ofPred_eq, mem_preimage, SetLike.mem_coe, Submodule.mem_inf, isTSD_iff,
    toIx_mat1, mem_domMax_iff hΩ]

theorem tsd_eq : {u : L2Vec Ω 1 | IsTSD (mat1 u)} = fieldE ⁻¹' (tsd Ω : Set (L2F ℝ Ω Ix)) := by
  ext u
  simp only [mem_ofPred_eq, mem_preimage, SetLike.mem_coe, isTSD_iff, toIx_mat1]

theorem closure_preimage_fieldE (s : Set (L2F ℝ Ω Ix)) :
    closure (fieldE ⁻¹' s : Set (L2Vec Ω 1)) = fieldE ⁻¹' closure s :=
  ((fieldE (Ω := Ω)).toHomeomorph.preimage_closure s).symm

/-- Orthogonal projections onto the pull-back of a closed subspace by a unitary map. -/
theorem starProjection_comap_apply {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] (f : E ≃ₗᵢ[ℝ] E') (p : Submodule ℝ E')
    [p.HasOrthogonalProjection] [(p.comap f.toLinearEquiv.toLinearMap).HasOrthogonalProjection]
    (x : E) : f ((p.comap f.toLinearEquiv.toLinearMap).starProjection x) = p.starProjection (f x) := by
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.starProjection_apply_mem (p.comap f.toLinearEquiv.toLinearMap) x) fun w hw => ?_
  rw [← LinearIsometryEquiv.apply_symm_apply f w, ← map_sub, LinearIsometryEquiv.inner_map_map]
  refine Submodule.starProjection_inner_eq_zero x _ ?_
  change f (f.symm w) ∈ p
  rwa [LinearIsometryEquiv.apply_symm_apply]

theorem starProjection_bot_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) : (⊥ : Submodule ℝ E).starProjection x = 0 := by
  rw [Submodule.starProjection_bot]; rfl

/-- **The complex of (4.14) is a short Hilbert complex** on every open `Ω`. -/
theorem electric_complex (hΩ : IsOpen Ω) :
    Dense ((vecOp fun _ => dMin Ω 0 : L2Vec Ω 0 →ₗ.[ℝ] L2Vec Ω 1).domain : Set (L2Vec Ω 0)) ∧
      Dense ((vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain : Set (L2Vec Ω 1)) ∧
      (vecOp fun _ => dMin Ω 0 : L2Vec Ω 0 →ₗ.[ℝ] L2Vec Ω 1).IsClosed ∧
      (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).IsClosed ∧
      ∀ x : (vecOp fun _ => dMin Ω 0 : L2Vec Ω 0 →ₗ.[ℝ] L2Vec Ω 1).domain,
        ∃ h : (vecOp fun _ => dMin Ω 0) x ∈ (vecOp fun _ => dMin Ω 1 :
          L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain, (vecOp fun _ => dMin Ω 1) ⟨_, h⟩ = 0 :=
  ⟨dense_vecOp (by rw [dMin_eq]; exact (extDerivOp ℝ 3 0).dense_minimal_domain hΩ),
    dense_bgg_dt1 hΩ,
    isClosed_vecOp (by rw [dMin_eq]; exact (extDerivOp ℝ 3 0).isClosed_minimal hΩ),
    isClosed_bgg_dt1 hΩ, (isBGG_bggData hΩ).2.1⟩

/-- The electric slot `S₁*` of the invariant core, read through the electric field. -/
abbrev coreE (hΩ : IsOpen Ω) : Submodule ℝ (L2Vec Ω 1) :=
  ((gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω)).comap (fieldE (Ω := Ω)).toLinearEquiv.toLinearMap

/-- The magnetic slot `S₂*` of the invariant core, read through the magnetic field. -/
abbrev coreB (hΩ : IsOpen Ω) : Submodule ℝ (L2Vec Ω 2) :=
  ((gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω)).comap (fieldB (Ω := Ω)).toLinearEquiv.toLinearMap

theorem isClosed_coreE (hΩ : IsOpen Ω) : IsClosed (coreE hΩ : Set (L2Vec Ω 1)) :=
  (ShortHilbertComplex.isClosed_invariantCore₁ (S := gradCurl ℝ hΩ)).preimage fieldE.continuous

theorem isClosed_coreB (hΩ : IsOpen Ω) : IsClosed (coreB hΩ : Set (L2Vec Ω 2)) :=
  (ShortHilbertComplex.isClosed_invariantCore₂ (S := gradCurl ℝ hΩ)).preimage fieldB.continuous

instance hasOrthogonalProjection_coreE (hΩ : IsOpen Ω) : (coreE hΩ).HasOrthogonalProjection :=
  have : CompleteSpace (coreE hΩ) := (isClosed_coreE hΩ).completeSpace_coe
  inferInstance

instance hasOrthogonalProjection_coreB (hΩ : IsOpen Ω) : (coreB hΩ).HasOrthogonalProjection :=
  have : CompleteSpace (coreB hΩ) := (isClosed_coreB hΩ).completeSpace_coe
  inferInstance

/-- **The invariant core is a reducing subcomplex.** -/
theorem coreE_reducing (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    IsReducingSubcomplex (vecOp fun _ => dMin Ω 0) (vecOp fun _ => dMin Ω 1) ⊥ (coreE hΩ)
      (coreB hΩ) := by
  obtain ⟨-, -, -, hred, -⟩ := invariantCore_tsd hΩ hb hne
  have hr01 := hred.reduces 0 1
  have hr12 := hred.reduces 1 2
  change (gradCurl ℝ hΩ).d₀.IsReducingPair (⊥ : Submodule ℝ (L2F ℝ Ω (Fin 3)))
    ((gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω)) at hr01
  change (gradCurl ℝ hΩ).d₁.IsReducingPair ((gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω))
    ((gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω)) at hr12
  constructor
  · intro x
    refine ⟨by rw [starProjection_bot_apply]; exact Submodule.zero_mem _, ?_⟩
    rw [LinearPMap.apply_eq_zero_of_coe_eq_zero _ (starProjection_bot_apply _)]
    obtain ⟨h, e⟩ := apply_of_mem_graph ((mem_graph_grad_iff hΩ x _).1 (LinearPMap.mem_graph _ x))
    have hc := hr01.comm ⟨_, h⟩
    rw [LinearPMap.apply_eq_zero_of_coe_eq_zero _ (starProjection_bot_apply _), e] at hc
    apply fieldE.injective
    rw [starProjection_comap_apply, ← hc, map_zero]
  · intro x
    have hy := (mem_dom_iff hΩ x.1).1 x.2
    have hP := hr12.proj_mem ⟨_, hy⟩
    have eP : fieldE ((coreE hΩ).starProjection x.1) =
        ((gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω)).starProjection (fieldE x.1) :=
      starProjection_comap_apply _ _ _
    have hx' : (coreE hΩ).starProjection x.1 ∈
        (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain :=
      (mem_dom_iff hΩ _).2 (by rw [eP]; exact hP)
    refine ⟨hx', fieldB.injective ?_⟩
    calc fieldB ((vecOp fun _ => dMin Ω 1) ⟨_, hx'⟩)
        = (gradCurl ℝ hΩ).d₁ ⟨_, (mem_dom_iff hΩ _).1 hx'⟩ :=
          (curl_fieldE hΩ ⟨_, hx'⟩ ((mem_dom_iff hΩ _).1 hx')).symm
      _ = (gradCurl ℝ hΩ).d₁ ⟨_, hP⟩ := LinearPMap.apply_congr' _ _ _ eP
      _ = ((gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω)).starProjection
            ((gradCurl ℝ hΩ).d₁ ⟨_, hy⟩) := hr12.comm ⟨_, hy⟩
      _ = ((gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω)).starProjection
            (fieldB ((vecOp fun _ => dMin Ω 1) ⟨x.1, x.2⟩)) := by
          rw [curl_fieldE hΩ ⟨x.1, x.2⟩ hy]
      _ = fieldB ((coreB hΩ).starProjection ((vecOp fun _ => dMin Ω 1) ⟨x.1, x.2⟩)) :=
          (starProjection_comap_apply _ _ _).symm

set_option maxHeartbeats 1000000 in
/-- **The invariant core is the largest reducing subcomplex in the constraint.** -/
theorem coreE_maximal (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (S₁' : Submodule ℝ (L2Vec Ω 1)) (S₂' : Submodule ℝ (L2Vec Ω 2)) [S₁'.HasOrthogonalProjection]
    [S₂'.HasOrthogonalProjection] (hT₁ : ∀ u ∈ S₁', IsTSD (mat1 u))
    (hT₂ : ∀ ρ ∈ S₂', IsTSD (mat2 ρ))
    (hR : IsReducingSubcomplex (vecOp fun _ => dMin Ω 0) (vecOp fun _ => dMin Ω 1) ⊥ S₁' S₂') :
    S₁' ≤ coreE hΩ ∧ S₂' ≤ coreB hΩ := by
  obtain ⟨-, -, -, -, hmax, -⟩ := invariantCore_tsd hΩ hb hne
  set T₁ := S₁'.map (fieldE (Ω := Ω)).toLinearEquiv.toLinearMap
  set T₂ := S₂'.map (fieldB (Ω := Ω)).toLinearEquiv.toLinearMap
  have hT₁' : T₁ ≤ tsd Ω := by
    rintro _ ⟨u, hu, rfl⟩; exact (isTSD_iff _).1 (hT₁ u hu)
  have hT₂' : T₂ ≤ tsd Ω := by
    rintro _ ⟨ρ, hρ, rfl⟩; exact (isTSD_iff _).1 (hT₂ ρ hρ)
  have eT₁ : ∀ y, T₁.starProjection y = fieldE (S₁'.starProjection (fieldE.symm y)) :=
    fun y => Submodule.starProjection_map_apply fieldE S₁' y
  have eT₂ : ∀ y, T₂.starProjection y = fieldB (S₂'.starProjection (fieldB.symm y)) :=
    fun y => Submodule.starProjection_map_apply fieldB S₂' y
  have r01 : (gradCurl ℝ hΩ).d₀.IsReducingPair (⊥ : Submodule ℝ (L2F ℝ Ω (Fin 3))) T₁ := by
    refine ⟨fun y => by rw [starProjection_bot_apply]; exact Submodule.zero_mem _, fun y => ?_⟩
    rw [LinearPMap.apply_eq_zero_of_coe_eq_zero _ (starProjection_bot_apply _)]
    obtain ⟨hx, ex⟩ := apply_of_mem_graph ((mem_graph_grad_iff hΩ (field0.symm y)
      (fieldE.symm ((gradCurl ℝ hΩ).d₀ y))).2 (by simpa using LinearPMap.mem_graph _ y))
    obtain ⟨h0, e0⟩ := hR.1 ⟨_, hx⟩
    rw [LinearPMap.apply_eq_zero_of_coe_eq_zero _ (starProjection_bot_apply _), ex] at e0
    rw [eT₁, ← e0, map_zero]
  have key : ∀ y : (gradCurl ℝ hΩ).d₁.domain, ∃ hx : fieldE.symm (y : L2F ℝ Ω Ix) ∈
      (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain,
      fieldB ((vecOp fun _ => dMin Ω 1) ⟨_, hx⟩) = (gradCurl ℝ hΩ).d₁ y := fun y => by
    obtain ⟨hx, ex⟩ := apply_of_mem_graph ((mem_graph_curl_iff hΩ (fieldE.symm y)
      (fieldB.symm ((gradCurl ℝ hΩ).d₁ y))).2 (by simpa using LinearPMap.mem_graph _ y))
    exact ⟨hx, by rw [ex, LinearIsometryEquiv.apply_symm_apply]⟩
  have hpm : ∀ y : (gradCurl ℝ hΩ).d₁.domain,
      T₁.starProjection (y : L2F ℝ Ω Ix) ∈ (gradCurl ℝ hΩ).d₁.domain := fun y => by
    obtain ⟨hx, -⟩ := key y
    obtain ⟨hP, -⟩ := hR.2 ⟨_, hx⟩
    rw [eT₁]; exact (mem_dom_iff hΩ _).1 hP
  have r12 : (gradCurl ℝ hΩ).d₁.IsReducingPair T₁ T₂ := by
    refine ⟨hpm, fun y => ?_⟩
    obtain ⟨hx, ex⟩ := key y
    obtain ⟨hP, eP⟩ := hR.2 ⟨_, hx⟩
    rw [eT₂, ← ex, LinearIsometryEquiv.symm_apply_apply, ← eP,
      ← curl_fieldE hΩ ⟨_, hP⟩ ((mem_dom_iff hΩ _).1 hP)]
    exact LinearPMap.apply_congr' _ _ _ (eT₁ y)
  have hredT : (gradCurl ℝ hΩ).toHilbertComplex.ReducingSubcomplex
      (family3 (⊥ : Submodule ℝ (L2F ℝ Ω (Fin 3))) T₁ T₂) :=
    HilbertComplex.ReducingSubcomplex.of_rel fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp at hij
      · exact r01
      · exact r12
  obtain ⟨m1, m2⟩ := hmax T₁ T₂ hT₁' hT₂' hredT.isReducing_wave
  exact ⟨fun u hu => m1 ⟨u, hu, rfl⟩, fun ρ hρ => m2 ⟨ρ, hρ, rfl⟩⟩

/-- **The invariant core on a nonempty bounded open `Ω`.** -/
theorem electric_core (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {S : ℝ → (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) →L[ℝ] (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2)}
    (hS : IsEvolution ℝ (gradCurlWave Ω) univ S) :
    ∃ (S₁ : Submodule ℝ (L2Vec Ω 1)) (S₂ : Submodule ℝ (L2Vec Ω 2))
      (_ : S₁.HasOrthogonalProjection) (_ : S₂.HasOrthogonalProjection),
      invariantCore S (tsdConstraint Ω) = {U | U.1 = 0 ∧ U.2.1 ∈ S₁ ∧ U.2.2 ∈ S₂} ∧
      IsReducingSubcomplex (vecOp fun _ => dMin Ω 0) (vecOp fun _ => dMin Ω 1) ⊥ S₁ S₂ ∧
      (∀ (S₁' : Submodule ℝ (L2Vec Ω 1)) (S₂' : Submodule ℝ (L2Vec Ω 2))
        [S₁'.HasOrthogonalProjection] [S₂'.HasOrthogonalProjection],
        (∀ u ∈ S₁', IsTSD (mat1 u)) → (∀ ρ ∈ S₂', IsTSD (mat2 ρ)) →
        IsReducingSubcomplex (vecOp fun _ => dMin Ω 0) (vecOp fun _ => dMin Ω 1) ⊥ S₁' S₂' →
        S₁' ≤ S₁ ∧ S₂' ≤ S₂) ∧
      (∀ u ∈ S₁, IsTSD₀ (mat1 u)) ∧ (∀ ρ ∈ S₂, IsTSD (mat2 ρ)) ∧
      (∃ u, IsTSD (mat1 u) ∧ u ∉ S₁) ∧ (∃ ρ, IsTSD (mat2 ρ) ∧ ρ ∉ S₂) ∧
      ∃ ρ ∈ S₂, ρ ≠ 0 ∧ ((0, 0, ρ), 0) ∈ gradCurlWave Ω := by
  obtain ⟨hcore, h1, h2, -, -, hd1, hd1', hd2, hne', hβ, hβ', -⟩ := invariantCore_tsd hΩ hb hne
  refine ⟨coreE hΩ, coreB hΩ, inferInstance, inferInstance, ?_, coreE_reducing hΩ hb hne,
    fun S₁' S₂' _ _ hT₁ hT₂ hR => coreE_maximal hΩ hb hne S₁' S₂' hT₁ hT₂ hR,
    fun u hu => (isTSD₀_iff hΩ hb u).2 (h1 hu), fun ρ hρ => (isTSD_iff _).2 (h2 hρ),
    ⟨fieldE.symm (constField hΩ hb diagA), ?_, ?_⟩, ⟨fieldB.symm (betaL2 hΩ hb), ?_, ?_⟩,
    fieldB.symm (constField hΩ hb diagA), ?_, ?_, ?_⟩
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

/-- A restriction of the minimal row-wise curl, read through the fields, is a restriction of
`Feec`'s minimal curl. -/
theorem conj_le_curl (hΩ : IsOpen Ω) {d1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2}
    (hle : d1 ≤ vecOp fun _ => dMin Ω 1) :
    d1.conj (fieldE (Ω := Ω)).toContinuousLinearEquiv (fieldB (Ω := Ω)).toContinuousLinearEquiv ≤
      (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω := by
  have hdom : ∀ y : L2F ℝ Ω Ix, y ∈ (d1.conj (fieldE (Ω := Ω)).toContinuousLinearEquiv
      (fieldB (Ω := Ω)).toContinuousLinearEquiv).domain →
      fieldE.symm y ∈ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain :=
    fun y hy => hle.1 hy
  have hmem : ∀ y : L2F ℝ Ω Ix, y ∈ (d1.conj (fieldE (Ω := Ω)).toContinuousLinearEquiv
      (fieldB (Ω := Ω)).toContinuousLinearEquiv).domain →
      y ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain := fun y hy => by
    have h := (mem_dom_iff hΩ _).1 (hdom y hy)
    rwa [LinearIsometryEquiv.apply_symm_apply] at h
  refine ⟨fun y hy => hmem y hy, fun x y hxy => ?_⟩
  rw [LinearPMap.conj_apply]
  have hx := hdom x x.2
  have e1 : d1 ⟨(fieldE (Ω := Ω)).toContinuousLinearEquiv.symm x, x.2⟩ =
      (vecOp fun _ => dMin Ω 1) ⟨fieldE.symm x, hx⟩ := hle.2 rfl
  have h' : fieldE ((⟨fieldE.symm x, hx⟩ : (vecOp fun _ => dMin Ω 1 :
      L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain) : L2Vec Ω 1) ∈ (gradCurl ℝ hΩ).d₁.domain := by
    rw [LinearIsometryEquiv.apply_symm_apply]; exact hmem x x.2
  have e2 := curl_fieldE hΩ ⟨fieldE.symm x, hx⟩ h'
  change fieldB (d1 _) = _
  rw [e1, ← e2]
  exact LinearPMap.apply_congr' _ _ _ (by
    change fieldE (fieldE.symm (x : L2F ℝ Ω Ix)) = (y : L2F ℝ Ω Ix)
    rw [LinearIsometryEquiv.apply_symm_apply, hxy])

/-- **A short complex `W⁰ → L²Λ¹(Ω)³ → L²Λ²(Ω)³` of the challenge, read through the fields**:
a `Feec` short complex `W⁰ → L²(Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)` (the conjugate by `1`, `fieldE`,
`fieldB`) with the graphs of `d⁰` and `d¹`, whose `d₁` restricts `Feec`'s minimal curl when `d¹`
restricts the minimal row-wise curl. -/
theorem exists_fieldComplex (hΩ : IsOpen Ω) (W0 : Type) [NormedAddCommGroup W0]
    [InnerProductSpace ℝ W0] [CompleteSpace W0] (d0 : W0 →ₗ.[ℝ] L2Vec Ω 1)
    (d1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2) (hd0 : Dense (d0.domain : Set W0))
    (hd1 : Dense (d1.domain : Set (L2Vec Ω 1))) (hc0 : d0.IsClosed) (hc1 : d1.IsClosed)
    (hcomp : ∀ x : d0.domain, ∃ h : d0 x ∈ d1.domain, d1 ⟨_, h⟩ = 0) :
    ∃ S : ShortHilbertComplex ℝ W0 (L2F ℝ Ω Ix) (L2F ℝ Ω Ix),
      (∀ x y, (x, y) ∈ d0.graph ↔ (LinearIsometryEquiv.refl ℝ W0 x, fieldE y) ∈ S.d₀.graph) ∧
      (∀ x y, (x, y) ∈ d1.graph ↔ (fieldE x, fieldB y) ∈ S.d₁.graph) ∧
      (d1 ≤ vecOp (fun _ => dMin Ω 1) →
        S.d₁ ≤ (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) := by
  let S₀ : ShortHilbertComplex ℝ W0 (L2Vec Ω 1) (L2Vec Ω 2) :=
    ⟨d0, d1, hd0, hd1, hc0, hc1, fun x => (hcomp x).1, fun x => (hcomp x).2⟩
  refine ⟨S₀.conj (LinearIsometryEquiv.refl ℝ W0).toContinuousLinearEquiv
    (fieldE (Ω := Ω)).toContinuousLinearEquiv (fieldB (Ω := Ω)).toContinuousLinearEquiv,
    fun x y => ?_, fun x y => ?_, fun hle => conj_le_curl hΩ hle⟩
  · change _ ↔ _ ∈ (d0.conj _ _).graph
    rw [LinearPMap.mem_conj_graph_iff]
    change _ ↔ (x, fieldE.symm (fieldE y)) ∈ d0.graph
    rw [LinearIsometryEquiv.symm_apply_apply]
  · change _ ↔ _ ∈ (d1.conj _ _).graph
    rw [LinearPMap.mem_conj_graph_iff]
    change _ ↔ (fieldE.symm (fieldE x), fieldB.symm (fieldB y)) ∈ d1.graph
    rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]

/-- **The datum `(0, E₀, β)` leaves TSD for every boundary condition containing `n × E = 0`.** -/
theorem beta_not_propagates (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (W0 : Type) [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    (d0 : W0 →ₗ.[ℝ] L2Vec Ω 1) (d1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2)
    (hd0 : Dense (d0.domain : Set W0)) (hd1 : Dense (d1.domain : Set (L2Vec Ω 1)))
    (hc0 : d0.IsClosed) (hc1 : d1.IsClosed)
    (hcomp : ∀ x : d0.domain, ∃ h : d0 x ∈ d1.domain, d1 ⟨_, h⟩ = 0)
    (hle : d1 ≤ vecOp (fun _ => dMin Ω 1)) (u : L2Vec Ω 1) (T : ℝ)
    (U : ℝ → W0 × L2Vec Ω 1 × L2Vec Ω 2) (hT : 0 < T)
    (hU0 : U 0 = (0, u, fieldB.symm (betaL2 hΩ hb)))
    (hU : IsStrongSolution {p | IsHodgeWave d0 d1 p.1 p.2} (Icc 0 T) U) :
    ∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (U t).2.1) := by
  obtain ⟨S, h0, h1, hS⟩ := exists_fieldComplex hΩ W0 d0 d1 hd0 hd1 hc0 hc1 hcomp
  have hU' := isStrongSolution_toFeec (LinearIsometryEquiv.refl ℝ W0) fieldE fieldB S h0 h1 hU
  obtain ⟨t, ht, hnot⟩ := betaL2_not_propagates hΩ hb hne S (hS hle) hT hU'
    (by rw [hU0]; change -(LinearIsometryEquiv.refl ℝ W0) (0 : W0) = 0; simp)
    (by rw [hU0]; change fieldB (fieldB.symm (betaL2 hΩ hb)) = _;
        rw [LinearIsometryEquiv.apply_symm_apply])
  exact ⟨t, ht, fun h => hnot (by rw [isTSD_iff, toIx_mat1] at h; exact h)⟩

/-- **The datum `(0, 0, β)` lies in `D(L)` for every boundary condition containing `n × E = 0`**:
`β ∈ D(d₁†)`, as `d₁† ⊇ curl_max` (`betaL2_mem_adjoint`). -/
theorem beta_mem_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (W0 : Type)
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    (d0 : W0 →ₗ.[ℝ] L2Vec Ω 1) (d1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2)
    (hd0 : Dense (d0.domain : Set W0)) (hd1 : Dense (d1.domain : Set (L2Vec Ω 1)))
    (hc0 : d0.IsClosed) (hc1 : d1.IsClosed)
    (hcomp : ∀ x : d0.domain, ∃ h : d0 x ∈ d1.domain, d1 ⟨_, h⟩ = 0)
    (hle : d1 ≤ vecOp (fun _ => dMin Ω 1)) :
    ∃ V, IsHodgeWave d0 d1 (0, 0, fieldB.symm (betaL2 hΩ hb)) V := by
  obtain ⟨S, h0, h1, hS⟩ := exists_fieldComplex hΩ W0 d0 d1 hd0 hd1 hc0 hc1 hcomp
  obtain ⟨hβ, -⟩ := betaL2_mem_adjoint hΩ hb S (hS hle)
  refine (exists_isHodgeWave_iff (LinearIsometryEquiv.refl ℝ W0) fieldE fieldB S h0 h1 _).2 ?_
  rw [stateL_apply]
  simp only [map_zero, neg_zero, LinearIsometryEquiv.apply_symm_apply]
  exact S.mem_wave_domain.2 ⟨S.d₀.domain.zero_mem, S.d₁.domain.zero_mem,
    (S.d₀†).domain.zero_mem, hβ⟩

/-- **The magnetic datum `β` on a nonempty bounded open `Ω`.** -/
theorem electric_beta (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ∃ ρ : L2Vec Ω 2, (∀ a b, ⇑(mat2 ρ a b) =ᵐ[volume.restrict Ω]
        fun x => if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then x 2 else 0) ∧
      (0, 0, ρ) ∈ tsdConstraint Ω ∧
      ∀ (W0 : Type) [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
        (d0 : W0 →ₗ.[ℝ] L2Vec Ω 1) (d1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2),
        Dense (d0.domain : Set W0) → Dense (d1.domain : Set (L2Vec Ω 1)) → d0.IsClosed →
        d1.IsClosed → (∀ x : d0.domain, ∃ h : d0 x ∈ d1.domain, d1 ⟨_, h⟩ = 0) →
        d1 ≤ vecOp (fun _ => dMin Ω 1) → (∃ V, IsHodgeWave d0 d1 (0, 0, ρ) V) ∧
          ∀ u T (U : ℝ → W0 × L2Vec Ω 1 × L2Vec Ω 2), 0 < T → U 0 = (0, u, ρ) →
            IsStrongSolution {p | IsHodgeWave d0 d1 p.1 p.2} (Icc 0 T) U →
            ∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (U t).2.1) := by
  refine ⟨fieldB.symm (betaL2 hΩ hb), fun a b => ?_, ⟨rfl, ?_, ?_⟩,
    fun W0 _ _ _ d0 d1 hd0 hd1 hc0 hc1 hcomp hle =>
      ⟨beta_mem_domain hΩ hb W0 d0 d1 hd0 hd1 hc0 hc1 hcomp hle, fun u T U hT hU0 hU =>
        beta_not_propagates hΩ hb hne W0 d0 d1 hd0 hd1 hc0 hc1 hcomp hle u T U hT hU0 hU⟩⟩
  · change ⇑(fieldB (fieldB.symm (betaL2 hΩ hb)) (a, b)) =ᵐ[volume.restrict Ω] _
    rw [LinearIsometryEquiv.apply_symm_apply]
    refine (MemLp.coeFn_toLp (memLp_of_continuous hΩ.measurableSet hb
      (contDiff_betaField (a, b)).continuous)).trans (Eventually.of_forall fun x => ?_)
    simp only [betaField, Prod.mk.injEq]
    split_ifs <;> rfl
  · rw [isTSD_iff, toIx_mat1, map_zero]; exact Submodule.zero_mem _
  · rw [isTSD_iff, toIx_mat2, LinearIsometryEquiv.apply_symm_apply]; exact betaL2_mem_tsd hΩ hb

/-- A field whose projection onto `Feec`'s `L²(TSD)` leaves `Feec`'s `H̊(curl)` has its orthogonal
projection onto the TSD fields of the challenge outside `H̊(curl)`. -/
theorem proj_not_mem_of (hΩ : IsOpen Ω) {u : L2Vec Ω 1}
    (hu : (tsd Ω).starProjection (fieldE u) ∉
      ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain) :
    ∀ v, IsTSD (mat1 v) → (∀ w, IsTSD (mat1 w) → ⟪u - v, w⟫_ℝ = 0) →
      v ∉ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain := by
  intro v hv hvo hvd
  have hv' : fieldE v ∈ tsd Ω := by rw [← toIx_mat1, ← isTSD_iff]; exact hv
  have e : (tsd Ω).starProjection (fieldE u) = fieldE v :=
    Submodule.eq_starProjection_of_mem_of_inner_eq_zero hv' fun w hw => by
      have h := hvo (fieldE.symm w)
        (by rw [isTSD_iff, toIx_mat1, LinearIsometryEquiv.apply_symm_apply]; exact hw)
      rwa [← LinearIsometryEquiv.inner_map_map fieldE, map_sub,
        LinearIsometryEquiv.apply_symm_apply] at h
  exact hu (by rw [e]; exact (mem_dom_iff hΩ v).1 hvd)

/-- **`P_K D(L) ⊄ D(L)` on a nonempty bounded open `Ω`**: for a test field, and for every boundary
condition containing `n × E = 0` from a field of the dense `D(d₁) ∩ D(d₀†)` of the complex read
through the fields (`Feec.Counterexamples.BoundedDomainTSD.exists_projTSD_not_mem_domain_of_dense`;
the restriction `d¹ ≤ d̊¹` turns `P u ∉ H̊(curl)` into `P_K (0, u, 0) ∉ D(L)`). -/
theorem electric_proj (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    (∃ u : L2Vec Ω 1, (∀ a b, ∃ φ, IsTestFn Ω φ ∧ ⇑(mat1 u a b) =ᵐ[volume.restrict Ω] φ) ∧
      ∀ v, IsTSD (mat1 v) → (∀ w, IsTSD (mat1 w) → ⟪u - v, w⟫_ℝ = 0) →
        v ∉ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain) ∧
    ∀ (W0 : Type) [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
      (d0 : W0 →ₗ.[ℝ] L2Vec Ω 1) (d1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2),
      Dense (d0.domain : Set W0) → Dense (d1.domain : Set (L2Vec Ω 1)) → d0.IsClosed →
      d1.IsClosed → (∀ x : d0.domain, ∃ h : d0 x ∈ d1.domain, d1 ⟨_, h⟩ = 0) →
      d1 ≤ vecOp (fun _ => dMin Ω 1) → ∃ u : L2Vec Ω 1, (∃ V, IsHodgeWave d0 d1 (0, u, 0) V) ∧
        ∀ v, IsTSD (mat1 v) → (∀ w, IsTSD (mat1 w) → ⟪u - v, w⟫_ℝ = 0) →
          v ∉ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain := by
  refine ⟨?_, fun W0 _ _ _ d0 d1 hd0 hd1 hc0 hc1 hcomp _ => ?_⟩
  · obtain ⟨Φ, hΦ, hnot⟩ := exists_projTSD_not_mem_domain hΩ hb hne
    refine ⟨fieldE.symm (testField hΦ), fun a b => ⟨Φ (a, b), isTestFn_of (hΦ (a, b)), ?_⟩,
      proj_not_mem_of hΩ (by rwa [LinearIsometryEquiv.apply_symm_apply])⟩
    change ⇑(fieldE (fieldE.symm (testField hΦ)) (a, b)) =ᵐ[volume.restrict Ω] _
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact coeFn_testField hΦ (a, b)
  · obtain ⟨S, h0, h1, -⟩ := exists_fieldComplex hΩ W0 d0 d1 hd0 hd1 hc0 hc1 hcomp
    obtain ⟨y, ⟨hy1, hy0⟩, hnot⟩ :=
      exists_projTSD_not_mem_domain_of_dense hΩ hb hne S.dense_domain_inf_adjoint
    refine ⟨fieldE.symm y, (exists_isHodgeWave_iff (LinearIsometryEquiv.refl ℝ W0) fieldE fieldB
      S h0 h1 _).2 ?_, proj_not_mem_of hΩ (by rwa [LinearIsometryEquiv.apply_symm_apply])⟩
    rw [stateL_apply]
    simp only [map_zero, neg_zero, LinearIsometryEquiv.apply_symm_apply]
    exact S.mem_wave_domain.2 ⟨S.d₀.domain.zero_mem, hy1, hy0, (S.d₁†).domain.zero_mem⟩

/-- **`L²(TSD) ∩ H̊(curl)` is not dense in `L²(TSD)` on a nonempty bounded open `Ω`.** -/
theorem not_dense_min (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    closure {u : L2Vec Ω 1 | IsTSD (mat1 u) ∧ u ∈ (vecOp fun _ => dMin Ω 1 :
      L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain} ≠ {u | IsTSD (mat1 u)} := by
  intro h
  refine not_dense_tsd_inter hΩ hb hne (SetLike.coe_injective ?_)
  rw [tsd_inter_eq hΩ, tsd_eq, closure_preimage_fieldE] at h
  rw [Submodule.topologicalClosure_coe]
  exact (fieldE (Ω := Ω)).surjective.preimage_injective h

/-- **`L²(TSD) ∩ D(d¹)` is not dense in `L²(TSD)` on a nonempty bounded open `Ω`**, for every
restriction `d¹` of the minimal row-wise curl: it lies in `L²(TSD) ∩ H̊(curl)`. -/
theorem electric_dense (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (d1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2) (hle : d1 ≤ vecOp (fun _ => dMin Ω 1)) :
    closure {u : L2Vec Ω 1 | IsTSD (mat1 u) ∧ u ∈ d1.domain} ≠ {u | IsTSD (mat1 u)} := by
  intro h
  have hT : IsClosed {u : L2Vec Ω 1 | IsTSD (mat1 u)} := by
    rw [tsd_eq]; exact isClosed_tsd.preimage fieldE.continuous
  refine not_dense_min hΩ hb hne
    (Set.Subset.antisymm (closure_minimal (fun u hu => hu.1) hT) ?_)
  rw [← h]
  exact closure_mono fun u hu => ⟨hu.1, hle.1 hu.2⟩

/-- **The electric boundary conditions, on a nonempty bounded open `Ω`.** -/
theorem electric_of (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ElectricVerdict Ω :=
  ⟨electric_complex hΩ, ⟨_, gc_isEvolution hΩ⟩, fun _ hS => electric_core hΩ hb hne hS,
    electric_beta hΩ hb hne, electric_proj hΩ hb hne, electric_dense hΩ hb hne,
    tsd_not_propagates_of hΩ hb hne⟩

/-- **Domains star-shaped with respect to a ball.** -/
theorem starShaped_of (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (hstar : ∃ x₀ s, 0 < s ∧ ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    StarShapedVerdict Ω := by
  obtain ⟨x₀, s, hs, hst⟩ := hstar
  refine ⟨⟨?_, ?_⟩, fun S hS => ?_⟩
  · have e := (density_dichotomy hΩ hb hne hs hst).1
    rw [tsd_inter_max_eq hΩ, closure_preimage_fieldE, ← Submodule.topologicalClosure_coe, e]
    exact tsd_eq.symm
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
    Fin.sum_univ_three, _root_.sq]

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
      simpa [Feec.Counterexamples.BallSymTSD.rho, Fin.sum_univ_three, _root_.sq] using hx))
    (U := fun ij => Φ ij.1 ij.2) (fun ij => hΦ _ _) (fun ij => hvΦ _ _)
  exact (LinearIsometryEquiv.map_eq_zero_iff fieldE).1 h

/-- **The unit ball.** -/
theorem ball_of : ∀ ξ ≠ 0, ∀ v : L2Vec unitBall 1, IsTSD (mat1 v) → IsEigenfield unitBall ξ v →
    (∃ O : Set (Fin 3 → ℝ), IsOpen O ∧ {x | ∑ i, x i ^ 2 ≤ 1} ⊆ O ∧
      ∃ Φ : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ, (∀ a b, ContDiffOn ℝ 2 (Φ a b) O) ∧
        ∀ a b, ⇑(mat1 v a b) =ᵐ[volume.restrict unitBall] Φ a b) → v = 0 :=
  fun _ hξ v hv hE ⟨_, hO, hBO, _, hΦ, hvΦ⟩ => ball_of_eq unitBall_eq hξ v hv hE hO hBO hΦ hvΦ

/-- **Boxes.** -/
theorem box_of {a ℓ : Fin 3 → ℝ} (hℓ : ∀ i, 0 < ℓ i) : BoxVerdict a ℓ := by
  have hΩ : IsOpen (box a ℓ) := Feec.Models.Box.isOpen_openBox a ℓ
  refine ⟨fun S hS => ?_, fun S₁ S₂ h₁ h₂ U hU => (box_stationary_of hℓ).2 S₁ S₂ h₁ h₂ U hU⟩
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
