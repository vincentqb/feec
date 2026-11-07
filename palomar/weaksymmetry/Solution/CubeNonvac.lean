module

public import Solution.CubeWave

/-!
# Non-vacuity of the rates on the cube

The manufactured solutions of `Feec`: the coupled static solution
(`Feec.Models.Cube.WeakSymmetry.exists_coupled_manufactured_solution`: `λ = dg`, `σ = dᵗλ`,
`φₐ = ∂ₐσ`, `uₐ = −g dxₐ` for a bump `g`) and the wave solution `waveManufactured`
(`waveManufactured_hyps`), as solutions of the challenge.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 5.5, §6.3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter

@[expose] public noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 8000000

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

/-- The static datum `v ↦ F(e₁ v)`. -/
def coupledF : 𝒟.dt1.domain →ₗ[ℝ] ℝ := coupledDatum ∘ₗ e1.toLinearEquiv.toLinearMap

/-- **A coupled nontrivial smooth solution of (5.3) on the cube.** -/
theorem cube_static_nonvacuous : ∃ L, 𝒟.IsSolution coupledF coupledσ (e0.symm coupledφ)
    (ofWv1 coupledu) coupledMult ∧ (coupledσ : W0) ≠ 0 ∧ ((e0.symm coupledφ : 𝒟.dt0.domain) : Wv W0) ≠ 0 ∧
    ((ofWv1 coupledu : 𝒟.dt1.domain) : Wv W1) ≠ 0 ∧ coupledMult ≠ 0 ∧
    IsCsFormTr 0 0 L (coupledσ : W0) ∧ (∀ a, IsCsFormTr 0 0 L ((coupledφ a : U0) : W0)) ∧
    (∀ a, IsCsFormTr 0 1 L ((coupledu a : U1) : W1)) ∧ ‖coupledMult‖ ≤ L := by
  obtain ⟨L, -, hσ0, hφ0, hu0, hl0, c1, c2, c3, hσ, hφ, hu, hl, -⟩ :=
    exists_coupled_manufactured_solution
  refine ⟨L, ⟨fun τ ψ => ?_, fun v => ?_, congrArg Subtype.val c3⟩, fun h => hσ0 (Subtype.ext h),
    fun h => hφ0 ?_, fun h => hu0 ?_, hl0, hσ.isCsFormTr, fun a => (hφ a).isCsFormTr,
    fun a => (hu a).isCsFormTr, hl⟩
  · have := c1 τ (e0 ψ)
    rw [inner_wv_U1] at this
    exact this
  · have := c2 (e1 v)
    rw [inner_wv_U1] at this
    exact this
  · have : e0 (e0.symm coupledφ) = 0 := by
      rw [show (e0.symm coupledφ : 𝒟.dt0.domain) = 0 from Subtype.ext h, map_zero]
    rwa [LinearIsometryEquiv.apply_symm_apply] at this
  · have h' : incl1 coupledu = 0 := h
    have : ‖coupledu‖ = 0 := by rw [← norm_incl1, h', norm_zero]
    exact norm_eq_zero.1 this

theorem e0_symm_ne_zero {x : Wv U0} (hx : x ≠ 0) : ((e0.symm x : 𝒟.dt0.domain) : Wv W0) ≠ 0 :=
  fun h => hx (by
    have : e0 (e0.symm x) = 0 := by
      rw [show (e0.symm x : 𝒟.dt0.domain) = 0 from Subtype.ext h, map_zero]
    rwa [LinearIsometryEquiv.apply_symm_apply] at this)

theorem ofWv1_ne_zero {x : Wv U1} (hx : x ≠ 0) : ((ofWv1 x : 𝒟.dt1.domain) : Wv W1) ≠ 0 :=
  fun h => hx (by
    have h' : incl1 x = 0 := h
    have : ‖x‖ = 0 := by rw [← norm_incl1, h', norm_zero]
    exact norm_eq_zero.1 this)

theorem eq_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {x y : E}
    (h : ∀ z, ⟪x, z⟫_ℝ - ⟪y, z⟫_ℝ = 0) : x = y := by
  have := h (x - y)
  rw [← inner_sub_left, real_inner_self_eq_norm_sq] at this
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))

/-- The source of the manufactured wave solution. -/
def waveF (t : ℝ) : Wv W1 := incl1 (t • (bggSegment.dt0 coupledφ + waveCurlCurlU))

/-- **A nontrivial classical solution of (6.2) on the cube** satisfying the hypotheses of the
wave rate. -/
theorem cube_wave_nonvacuous {T : ℝ} (hT : 0 < T) : ∃ L, ContinuousOn waveF (Icc 0 T) ∧
    𝒟.IsWaveSolution T waveF (fun t => (waveManufactured T).σ t) (fun t => (waveManufactured T).σ' t)
      (fun t => e0.symm ((waveManufactured T).φ t)) (fun t => e0.symm ((waveManufactured T).φ' t))
      (fun t => ofWv1 ((waveManufactured T).u t)) (fun t => ofWv1 ((waveManufactured T).u' t))
      (waveManufactured T).M (waveManufactured T).M' (waveManufactured T).ρ
      (waveManufactured T).ρ' (fun _ => coupledMult) (fun _ => 0) ∧
    (∀ t ∈ Icc 0 T, IsSmoothStateTr L ((waveManufactured T).σ t) ((waveManufactured T).φ t)
        ((waveManufactured T).u t) ((waveManufactured T).M t) ((waveManufactured T).ρ t) ∧
      IsSmoothStateTr L ((waveManufactured T).σ' t) ((waveManufactured T).φ' t)
        ((waveManufactured T).u' t) ((waveManufactured T).M' t) ((waveManufactured T).ρ' t) ∧
      ‖coupledMult‖ ≤ L ∧ ‖(0 : W1)‖ ≤ L) ∧
    (∀ t, ((ofWv1 ((waveManufactured T).u t) : 𝒟.dt1.domain) : Wv W1) ≠ 0) ∧
    ∀ t ∈ Ioc 0 T, (((waveManufactured T).σ t : U0) : W0) ≠ 0 ∧
      ((e0.symm ((waveManufactured T).φ t) : 𝒟.dt0.domain) : Wv W0) ≠ 0 := by
  obtain ⟨L, hL0, hreg, -, hne, hune, -⟩ := waveManufactured_hyps hT
  set s := waveManufactured T
  refine ⟨L + ‖coupledMult‖, ?_, ?_, fun t ht => ⟨((hreg t ht).1.isSmoothStateTr).mono
      (le_add_of_nonneg_right (norm_nonneg _)), ((hreg t ht).2.isSmoothStateTr).mono
      (le_add_of_nonneg_right (norm_nonneg _)), le_add_of_nonneg_left hL0,
      by rw [norm_zero]; positivity⟩, fun t => ofWv1_ne_zero (hune t), fun t ht =>
      ⟨fun h => (hne t ht).1 (Subtype.ext h), e0_symm_ne_zero (hne t ht).2⟩⟩
  · exact incl1CLM.continuous.comp_continuousOn ((continuous_id.smul continuous_const).continuousOn)
  · refine ⟨⟨s.cσ, s.cσ', s.dσ⟩, ⟨?_, ?_, fun t ht => ?_⟩, ⟨?_, ?_, fun t ht => ?_⟩,
      ⟨s.cdu, s.cdu', s.ddu⟩, ⟨s.cM, s.cM', s.dM⟩, ⟨s.cρ, s.cρ', s.dρ⟩,
      ⟨continuousOn_const, continuousOn_const, fun t _ => hasDerivWithinAt_const _ _ _⟩,
      fun t ht => ⟨fun τ ψ => ?_, fun v => ?_, ?_, ?_⟩, fun t ht => ⟨?_, ?_⟩⟩
    · exact continuousOn_subtype _ (incl1CLM.continuous.comp_continuousOn s.cu)
    · exact continuousOn_subtype _ (incl1CLM.continuous.comp_continuousOn s.cu')
    · exact hasDerivWithinAt_subtype _ (hasDerivWithinAt_piCoe D1.domain (s.du t ht))
    · exact incl1CLM.continuous.comp_continuousOn s.cdφ
    · exact incl1CLM.continuous.comp_continuousOn s.cdφ'
    · exact hasDerivWithinAt_piCoe D1.domain (s.ddφ t ht)
    · have := s.ea t ht τ (e0 ψ)
      rw [inner_wv_U1] at this
      exact this
    · have := s.eb t ht (e1 v)
      rw [srcFun_apply, inner_wv_U1, inner_wv_U1] at this
      exact this
    · exact eq_of_inner fun z => s.ec t ht z
    · exact eq_of_inner fun z => s.ed t ht z
    · exact congrArg Subtype.val (s.ee t ht)
    · exact congrArg Subtype.val (s.ee' t ht)

end FEEC
