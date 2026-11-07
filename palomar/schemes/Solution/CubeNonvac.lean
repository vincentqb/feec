module

public import Solution.CubeWave
public import Solution.Sobolev
public import Feec.Physics.EinsteinBianchi.WaveFEMRegularity

/-!
# Non-vacuity of the rates on the cube

The manufactured solutions of `Feec`: the coupled static solution
(`Feec.Models.Cube.WeakSymmetry.exists_coupled_manufactured_solution`: `λ = dg`, `σ = dᵗλ`,
`φₐ = ∂ₐσ`, `uₐ = −g dxₐ` for a bump `g`) and the wave solution `waveManufactured`
(`waveManufactured_hyps`), as solutions of the challenge. Their fields are test fields (times
functions of `t`), so they also lie in the `H¹` classes (`cube_static_h1`, `cube_wave_h1`, from
`Feec.Domain.exists_h1Data_testField`).

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
    (ofWv1 coupledu) coupledMult ∧ (coupledσ : W0) ≠ 0 ∧
    ((e0.symm coupledφ : 𝒟.dt0.domain) : Wv W0) ≠ 0 ∧
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
    𝒟.IsWaveSolution T waveF (fun t => (waveManufactured T).σ t)
      (fun t => (waveManufactured T).σ' t)
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

/-! ### The `H¹` classes -/

theorem IsH1State.mono {L L' : ℝ} (hL : 0 ≤ L) (h : L ≤ L') {σ : L2Form (cube 3) 0}
    {φ : L2Vec (cube 3) 0} {u : L2Vec (cube 3) 1} {M : L2Form (cube 3) 2} {ρ : L2Vec (cube 3) 2}
    (hs : IsH1State L σ φ u M ρ) : IsH1State L' σ φ u M ρ :=
  ⟨isSobolevForm_mono hL h hs.1, fun a ha => isSobolevForm_mono hL h (hs.2.1 a ha),
    fun a => isSobolevForm_mono hL h (hs.2.2.1 a),
    fun a ha => isSobolevForm_mono hL h (hs.2.2.2.1 a ha), isSobolevForm_mono hL h hs.2.2.2.2.1,
    fun a => isSobolevForm_mono hL h (hs.2.2.2.2.2.1 a), hs.2.2.2.2.2.2⟩

/-- **A state with `H¹(ℝ³)` data is of class `H¹`.** -/
theorem isH1State_of {B : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2} {ρ : Wv W2}
    (hσ : H1Data (cubeDomain 3) (σ : W0) B) (hφ : ∀ a, H1Data (cubeDomain 3) (D0 (φ a)) B)
    (hu : ∀ a, H1Data (cubeDomain 3) ((u a : U1) : W1) B)
    (hdu : ∀ a, H1Data (cubeDomain 3) (D1 (u a)) B) (hM : H1Data (cubeDomain 3) M B)
    (hρ : ∀ a, H1Data (cubeDomain 3) (ρ a) B) (hMd : M ∈ D2min.domain)
    (hρd : ∀ a, ρ a ∈ D2min.domain) :
    IsH1State (16 * B) (σ : W0) (incl0 φ) (incl1 u) M ρ := by
  refine ⟨isSobolevForm_of_h1Data hσ, fun a h => ?_, fun a => isSobolevForm_of_h1Data (hu a),
    fun a h => ?_, isSobolevForm_of_h1Data hM, fun a => isSobolevForm_of_h1Data (hρ a),
    by rw [dMin_eq]; exact hMd, fun a => by rw [dMin_eq]; exact hρd a⟩
  · rw [LinearPMap.apply_of_eq' (dMin_eq (cube 3) 0)]
    exact isSobolevForm_of_h1Data (hφ a)
  · rw [LinearPMap.apply_of_eq' (dMin_eq (cube 3) 1)]
    exact isSobolevForm_of_h1Data (hdu a)

/-- `H¹(ℝ³)` data of the fields of the manufactured solutions, with one bound. -/
theorem exists_coupled_h1Data : ∃ B, 0 ≤ B ∧ Nonempty (H1Data (cubeDomain 3) (coupledσ : W0) B) ∧
    (∀ a, Nonempty (H1Data (cubeDomain 3) ((coupledφ a : U0) : W0) B)) ∧
    (∀ a, Nonempty (H1Data (cubeDomain 3) (D0 (coupledφ a)) B)) ∧
    (∀ a, Nonempty (H1Data (cubeDomain 3) ((coupledu a : U1) : W1) B)) ∧
    ∀ a, Nonempty (H1Data (cubeDomain 3) (D1 (coupledu a)) B) := by
  obtain ⟨Bσ, ⟨hσ⟩⟩ := exists_h1Data_testField isTestField_coupledSigFn
  choose Bφ hφ using fun a => exists_h1Data_testField (isTestField_coupledPhiFn a)
  choose Bdφ hdφ using fun a => exists_h1Data_testField
    ((extDerivOp ℝ 3 0).isTestField_apply (isTestField_coupledPhiFn a))
  choose Bu hu using fun a => exists_h1Data_testField (isTestField_coupledU a)
  choose Bdu hdu using fun a => exists_h1Data_testField (isTestField_waveCurlU a)
  set B := |Bσ| + ∑ a, (|Bφ a| + |Bdφ a| + |Bu a| + |Bdu a|)
  have hle : ∀ a, |Bφ a| + |Bdφ a| + |Bu a| + |Bdu a| ≤ B - |Bσ| := fun a => by
    have := Finset.single_le_sum (f := fun a => |Bφ a| + |Bdφ a| + |Bu a| + |Bdu a|)
      (fun a _ => by positivity) (Finset.mem_univ a)
    simp only [B]; linarith
  have hσB : |Bσ| ≤ B := by
    have : 0 ≤ ∑ a, (|Bφ a| + |Bdφ a| + |Bu a| + |Bdu a|) := by positivity
    simp only [B]; linarith
  have hb : ∀ a, |Bφ a| ≤ B ∧ |Bdφ a| ≤ B ∧ |Bu a| ≤ B ∧ |Bdu a| ≤ B := fun a => by
    have := hle a
    have := abs_nonneg Bσ
    have := abs_nonneg (Bφ a); have := abs_nonneg (Bdφ a)
    have := abs_nonneg (Bu a); have := abs_nonneg (Bdu a)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  refine ⟨B, (abs_nonneg _).trans hσB, ⟨hσ.mono ((le_abs_self _).trans hσB)⟩, fun a => ⟨?_⟩,
    fun a => ⟨?_⟩, fun a => ⟨?_⟩, fun a => ⟨?_⟩⟩
  · exact (hφ a).some.mono ((le_abs_self _).trans (hb a).1)
  · have e : D0 (coupledφ a) = testField
        ((extDerivOp ℝ 3 0).isTestField_apply (isTestField_coupledPhiFn a)) :=
      (extDerivOp ℝ 3 0).minimal_testField (isOpen_cubeDomain 3) (isTestField_coupledPhiFn a)
    rw [e]
    exact (hdφ a).some.mono ((le_abs_self _).trans (hb a).2.1)
  · exact (hu a).some.mono ((le_abs_self _).trans (hb a).2.2.1)
  · rw [D1_coupledu]
    exact (hdu a).some.mono ((le_abs_self _).trans (hb a).2.2.2)

/-- **The static manufactured solution is of class `H¹`.** -/
theorem cube_static_h1 : ∃ L, 0 ≤ L ∧ IsSobolevForm (cube 3) 1 0 L (coupledσ : W0) ∧
    (∀ a, IsSobolevForm (cube 3) 1 0 L ((coupledφ a : U0) : W0)) ∧
    (∀ a, IsSobolevForm (cube 3) 1 1 L (D0 (coupledφ a))) ∧
    (∀ a, IsSobolevForm (cube 3) 1 1 L ((coupledu a : U1) : W1)) ∧
    ∀ a, IsSobolevForm (cube 3) 1 2 L (D1 (coupledu a)) := by
  obtain ⟨B, hB, ⟨hσ⟩, hφ, hdφ, hu, hdu⟩ := exists_coupled_h1Data
  exact ⟨16 * B, by positivity, isSobolevForm_of_h1Data hσ,
    fun a => isSobolevForm_of_h1Data (hφ a).some, fun a => isSobolevForm_of_h1Data (hdφ a).some,
    fun a => isSobolevForm_of_h1Data (hu a).some, fun a => isSobolevForm_of_h1Data (hdu a).some⟩

/-- **The manufactured wave solution is of class `H¹`** on `[0, T]`. -/
theorem cube_wave_h1 (T : ℝ) : ∃ L, 0 ≤ L ∧ ∀ t ∈ Icc 0 T,
    IsH1State L ((waveManufactured T).σ t : W0) (incl0 ((waveManufactured T).φ t))
      (incl1 ((waveManufactured T).u t)) ((waveManufactured T).M t) ((waveManufactured T).ρ t) ∧
    IsH1State L ((waveManufactured T).σ' t : W0) (incl0 ((waveManufactured T).φ' t))
      (incl1 ((waveManufactured T).u' t)) ((waveManufactured T).M' t)
      ((waveManufactured T).ρ' t) := by
  obtain ⟨B, hB, ⟨hσ⟩, -, hdφ', hu', hdu'⟩ := exists_coupled_h1Data
  have hdφ := fun a => (hdφ' a).some
  have hu := fun a => (hu' a).some
  have hdu := fun a => (hdu' a).some
  set B' := (|T| + 1) * B
  have hB' : 0 ≤ B' := by positivity
  have hBB' : B ≤ B' := le_mul_of_one_le_left hB (by linarith [abs_nonneg T])
  have sc : ∀ {k : ℕ} {x : L2F ℝ (cubeDomain 3) (formIdx 3 k)} {t : ℝ}, t ∈ Icc 0 T →
      H1Data (cubeDomain 3) x B → H1Data (cubeDomain 3) (t • x) B' := fun {k x t} ht h =>
    (h.smul t).mono (mul_le_mul_of_nonneg_right (by
      rw [abs_of_nonneg ht.1]; linarith [ht.2, le_abs_self T]) hB)
  have z : ∀ {k : ℕ}, H1Data (cubeDomain 3) (0 : L2F ℝ (cubeDomain 3) (formIdx 3 k)) B' :=
    H1Data.zero.mono hB'
  refine ⟨16 * B', by positivity, fun t ht => ⟨?_, ?_⟩⟩
  · refine isH1State_of (sc ht hσ) (fun a => ?_) (fun a => (hu a).mono hBB')
      (fun a => (hdu a).mono hBB') z (fun a => sc ht (hdu a)) (Submodule.zero_mem _)
      (fun a => ?_)
    · change H1Data _ (D0 (t • coupledφ a)) B'
      rw [LinearPMap.map_smul]
      exact sc ht (hdφ a)
    · change t • D1 (coupledu a) ∈ D2min.domain
      exact Submodule.smul_mem _ _ (Feec.EinsteinBianchi.WaveFEM.D1_mem_D2min _)
  · refine isH1State_of (hσ.mono hBB') (fun a => (hdφ a).mono hBB') (fun a => ?_)
      (fun a => ?_) z (fun a => (hdu a).mono hBB') (Submodule.zero_mem _)
      (fun a => Feec.EinsteinBianchi.WaveFEM.D1_mem_D2min _)
    · change H1Data _ (0 : W1) B'
      exact z
    · change H1Data _ (D1 0) B'
      rw [LinearPMap.map_zero]
      exact z

end FEEC
