module

public import Feec.Counterexamples.BallSymTSD
public import Feec.Models.BoundedDomain.SymDualGeneral

/-!
# The Hessian–curl complex on balls: TSD data leave the constraint

On every Euclidean ball of `ℝ³`, for the complex `hessCurlMax` of [QuennevilleBelair2015], §4.11,
the strong solution from the TSD datum `(0, E₀((x - c)/R), 0)` leaves `{0} × L²(TSD) × L²(TSD)`.
The obstruction, a `Witness`, pulls back along affine maps.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §3.4, §4.11

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace LinearPMap
open MeasureTheory Set Feec.Domain Feec.Models.BoundedDomain

namespace Feec.Counterexamples.EveryBallSymTSD

open Feec.Counterexamples.BallSymTSD Feec.Counterexamples.BoundedSymTSD
open ShortHilbertComplex (mk3)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-! ### Witnesses of non-propagation -/

/-- TSD `E` with `(0, E, 0) ∈ D(L)` and `C ⊥ H̊(sym curl, T) ∩ L²(TSD)` with `⟪curl E, C⟫ ≠ 0`. -/
structure Witness {Ω : Set R3} (hΩ : IsOpen Ω) (E : symSub ℝ Ω) (C : trSub ℝ Ω) : Prop where
  mem_tsd : E ∈ tsdS Ω
  mem_d₁ : E ∈ (hessCurlMax ℝ hΩ).d₁.domain
  mem_adjoint_d₀ : E ∈ (hessCurlMax ℝ hΩ).d₀†.domain
  orth : ∀ B : (hessCurlMax ℝ hΩ).d₁†.domain, (B : trSub ℝ Ω) ∈ tsdT Ω →
    ⟪(B : trSub ℝ Ω), C⟫_ℝ = 0
  pair : ⟪(hessCurlMax ℝ hΩ).d₁ ⟨E, mem_d₁⟩, C⟫_ℝ ≠ 0

variable {Ω : Set R3} {hΩ : IsOpen Ω} {E : symSub ℝ Ω} {C : trSub ℝ Ω}

theorem Witness.mem_domain (h : Witness hΩ E C) :
    mk3 (0 : L2 ℝ Ω) E (0 : trSub ℝ Ω) ∈ (hessCurlMax ℝ hΩ).wave.domain :=
  (hessCurlMax ℝ hΩ).mem_wave_domain.2
    ⟨Submodule.zero_mem _, h.mem_d₁, h.mem_adjoint_d₀, Submodule.zero_mem _⟩

theorem Witness.mem_K (h : Witness hΩ E C) :
    mk3 (0 : L2 ℝ Ω) E (0 : trSub ℝ Ω) ∈ HilbertComplex.totalSub
      (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω)) (tsdS Ω) (tsdT Ω)) :=
  ShortHilbertComplex.mem_totalSub_family3.2 ⟨Submodule.zero_mem _, h.mem_tsd, Submodule.zero_mem _⟩

theorem Witness.inner_eq_zero (h : Witness hΩ E C)
    (y : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ Ω) (symSub ℝ Ω) (trSub ℝ Ω)))
    (hy : y ∈ (hessCurlMax ℝ hΩ).wave.domain)
    (hyK : y ∈ HilbertComplex.totalSub
      (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω)) (tsdS Ω) (tsdT Ω))) :
    ⟪y, mk3 (0 : L2 ℝ Ω) (0 : symSub ℝ Ω) C⟫_ℝ = 0 := by
  have hD := (hessCurlMax ℝ hΩ).mem_wave_domain.1 hy
  have hK := ShortHilbertComplex.mem_totalSub_family3.1 hyK
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [ShortHilbertComplex.mk3_apply_zero, ShortHilbertComplex.mk3_apply_one,
    ShortHilbertComplex.mk3_apply_two]
  erw [inner_zero_right, inner_zero_right, zero_add, zero_add]
  exact h.orth ⟨_, hD.2.2.2⟩ hK.2.2

/-- From `(0, E, 0)`, the Hodge wave equation of `hessCurlMax` has a unique strong solution on
every `[0, T]`, `T > 0`, and it leaves `K = {0} × L²(TSD) × L²(TSD)`. -/
theorem Witness.not_propagates (h : Witness hΩ E C) :
    ∀ T > 0, Evolution.IsStrongSolution (hessCurlMax ℝ hΩ).wave (Icc 0 T) 0
        (fun t => (hessCurlMax ℝ hΩ).toHilbertComplex.waveGroup.S t
          (mk3 (0 : L2 ℝ Ω) E (0 : trSub ℝ Ω))) ∧
      (∀ U, U 0 = mk3 (0 : L2 ℝ Ω) E (0 : trSub ℝ Ω) →
        Evolution.IsStrongSolution (hessCurlMax ℝ hΩ).wave (Icc 0 T) 0 U →
          (EqOn U (fun t => (hessCurlMax ℝ hΩ).toHilbertComplex.waveGroup.S t
            (mk3 (0 : L2 ℝ Ω) E (0 : trSub ℝ Ω))) (Icc 0 T) ∧
          ∃ t ∈ Icc 0 T, U t ∉ HilbertComplex.totalSub
            (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω)) (tsdS Ω) (tsdT Ω)))) := by
  intro T hT
  have hx := h.mem_domain
  have hU := (hessCurlMax ℝ hΩ).toHilbertComplex.isStrongSolution_waveGroup hx T
  have h0 : (hessCurlMax ℝ hΩ).toHilbertComplex.waveGroup.S 0
      (mk3 (0 : L2 ℝ Ω) E (0 : trSub ℝ Ω)) = mk3 (0 : L2 ℝ Ω) E (0 : trSub ℝ Ω) := by
    rw [(hessCurlMax ℝ hΩ).toHilbertComplex.waveGroup.map_zero]; rfl
  refine ⟨hU, fun U hU0 hU' => ⟨hU'.unique (hessCurlMax ℝ hΩ).isSkewAdjoint_wave.isDissipative
    hU (by rw [hU0, h0]), ?_⟩⟩
  refine not_propagate_of_inner _ (mk3 (0 : L2 ℝ Ω) (0 : symSub ℝ Ω) C)
    (fun y hy hK => h.inner_eq_zero y hy hK) hx ?_ T hT U hU0 hU'
  rw [inner_negL_ini _ hx h.mem_d₁]
  exact h.pair

theorem Witness.curl_not_mem_closure (h : Witness hΩ E C) :
    (hessCurlMax ℝ hΩ).d₁ ⟨E, h.mem_d₁⟩ ∈ tsdT Ω ∧
      (hessCurlMax ℝ hΩ).d₁ ⟨E, h.mem_d₁⟩ ∉
        closure ((tsdT Ω : Set (trSub ℝ Ω)) ∩ (hessCurlMax ℝ hΩ).d₁†.domain) := by
  refine ⟨hessCurlMax_d₁_mem_tsdT hΩ _ h.mem_tsd, fun hmem => h.pair ?_⟩
  have hsub : (tsdT Ω : Set (trSub ℝ Ω)) ∩ (hessCurlMax ℝ hΩ).d₁†.domain ⊆
      (fun B => ⟪B, C⟫_ℝ) ⁻¹' {0} := by
    rintro B ⟨hB, hD⟩
    exact h.orth ⟨B, hD⟩ hB
  exact closure_minimal hsub (isClosed_singleton.preimage (continuous_id.inner continuous_const))
    hmem

/-! ### Witnesses pull back along affine maps -/

section Pull

variable {a : ℝ} (ha : a ≠ 0) (b : R3) {Ω' : Set R3} (hΩ' : IsOpen Ω')
  (hT : aff a b ⁻¹' Ω' = Ω)

/-- A witness `(E, C)` on `Ω'` gives the witness `(E ∘ T, C ∘ T)` on `T⁻¹ Ω'`, `T x = a x + b`. -/
theorem Witness.pull {E : symSub ℝ Ω'} {C : trSub ℝ Ω'} (h : Witness hΩ' E C) :
    Witness (isOpen_of_aff b hΩ' hT) (pullSym ha b hΩ' hT E) (pullTr ha b hΩ' hT C) := by
  have hd₁ := hessCurlMax_d₁_pull (𝕜 := ℝ) ha b hΩ' hT
  have had₀ := adjoint_hessCurlMax_d₀_pull (𝕜 := ℝ) ha b hΩ' hT
  have had₁ := adjoint_hessCurlMax_d₁_pull (𝕜 := ℝ) ha b hΩ' hT
  have hs : ∀ u : symSub ℝ Ω', (pullSym (𝕜 := ℝ) ha b hΩ' hT).symm (pullSym ha b hΩ' hT u) = u :=
    fun u => (pullSym (𝕜 := ℝ) ha b hΩ' hT).symm_apply_apply u
  have hE1 : pullSym ha b hΩ' hT E ∈ (hessCurlMax ℝ (isOpen_of_aff b hΩ' hT)).d₁.domain := by
    rw [hd₁]; exact LinearPMap.mem_conjScaled_domain.2 (by rw [hs]; exact h.mem_d₁)
  refine ⟨(pullSym_mem_tsdS_iff ha b hΩ' hT).2 h.mem_tsd, hE1, ?_, fun B hB => ?_, ?_⟩
  · rw [had₀]; exact LinearPMap.mem_conjScaled_domain.2 (by rw [hs]; exact h.mem_adjoint_d₀)
  · have key : ∀ y : trSub ℝ Ω, y ∈ (hessCurlMax ℝ (isOpen_of_aff b hΩ' hT)).d₁†.domain →
        (pullTr ha b hΩ' hT).symm y ∈ (hessCurlMax ℝ hΩ').d₁†.domain := by
      intro y hy
      rw [had₁] at hy
      exact hy
    have hB' := key _ B.2
    have hBt : (pullTr ha b hΩ' hT).symm (B : trSub ℝ Ω) ∈ tsdT Ω' := by
      rw [← pullTr_mem_tsdT_iff ha b hΩ' hT, ContinuousLinearEquiv.apply_symm_apply]; exact hB
    have e := h.orth ⟨_, hB'⟩ hBt
    rw [← (pullTr ha b hΩ' hT).apply_symm_apply (B : trSub ℝ Ω), inner_pullTr]
    change (((jac (E := R3) a)⁻¹ : ℝ) : ℝ) * ⟪(pullTr ha b hΩ' hT).symm (B : trSub ℝ Ω), C⟫_ℝ = 0
    rw [e, mul_zero]
  · have e : (hessCurlMax ℝ (isOpen_of_aff b hΩ' hT)).d₁ ⟨_, hE1⟩ =
        ((a ^ 1 : ℝ) : ℝ) • pullTr ha b hΩ' hT ((hessCurlMax ℝ hΩ').d₁ ⟨E, h.mem_d₁⟩) := by
      rw [LinearPMap.apply_eq_of_eq hd₁ ⟨_, hE1⟩ ⟨_, by rw [← hd₁]; exact hE1⟩ rfl,
        LinearPMap.conjScaled_apply]
      congr 3
      exact Subtype.ext (hs E)
    rw [e, real_inner_smul_left, inner_pullTr]
    have hj := (jac_pos (E := R3) ha).ne'
    have := h.pair
    change a ^ 1 * ((((jac (E := R3) a)⁻¹ : ℝ) : ℝ) * _) ≠ 0
    exact mul_ne_zero (pow_ne_zero 1 ha) (mul_ne_zero (inv_ne_zero hj) this)

end Pull

/-! ### Every ball -/

/-- The unit ball carries the witness `(E₀, curl Q)` of `Feec.Counterexamples.BallSymTSD`. -/
theorem witness_ball3 : Witness isOpen_ball3 E0 ((hessCurlMax ℝ isOpen_ball3).d₁ ⟨Qs, Qs_mem_d1.1⟩) where
  mem_tsd := E0_mem_TSDS
  mem_d₁ := E0_mem_d1.1
  mem_adjoint_d₀ := E0_mem_adjoint_d0
  orth B hB := by
    have e := LinearPMap.adjoint_isFormalAdjoint (hessCurlMax ℝ isOpen_ball3).dense₁ B
      ⟨Qs, Qs_mem_d1.1⟩
    have h := inner_Qs_eq_zero (adjoint_hessCurlMax_d₁_mem_tsdS isOpen_ball3 B hB)
    rw [e] at h
    exact h
  pair := by
    have h := inner_negL_x0_ne_zero
    rwa [inner_negL_x0] at h

theorem preimage_ball3 (c : R3) {R : ℝ} (hR : 0 < R) :
    aff R⁻¹ (-(R⁻¹ • c)) ⁻¹' ball3 = euclBall c R := by
  ext x
  have e : rho (aff R⁻¹ (-(R⁻¹ • c)) x) = (∑ i, (x i - c i) ^ 2) / R ^ 2 := by
    simp only [rho, aff, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      Fin.sum_univ_three]
    field_simp
    ring
  simp only [mem_preimage, euclBall, ball3]
  change rho _ < 1 ↔ _
  rw [e, div_lt_one (by positivity)]
  rfl

theorem witness_ballE (c : R3) {R : ℝ} (hR : 0 < R) :
    Witness (isOpen_euclBall c R)
      (pullSym (inv_ne_zero hR.ne') (-(R⁻¹ • c)) isOpen_ball3 (preimage_ball3 c hR) E0)
      (pullTr (inv_ne_zero hR.ne') (-(R⁻¹ • c)) isOpen_ball3 (preimage_ball3 c hR)
        ((hessCurlMax ℝ isOpen_ball3).d₁ ⟨Qs, Qs_mem_d1.1⟩)) :=
  witness_ball3.pull (inv_ne_zero hR.ne') (-(R⁻¹ • c)) isOpen_ball3 (preimage_ball3 c hR)

/-- The TSD datum `E₀((x - c)/R)` on `{|x - c| < R}`, `E₀ = e₃ uᵀ + u e₃ᵀ`, `u = e₃ × x`. -/
def E0R (c : R3) {R : ℝ} (hR : 0 < R) : symSub ℝ (euclBall c R) :=
  pullSym (inv_ne_zero hR.ne') (-(R⁻¹ • c)) isOpen_ball3 (preimage_ball3 c hR) E0

/-- On every ball of `ℝ³`, the TSD datum `(0, E₀((x - c)/R), 0) ∈ D(L) ∩ K` of `hessCurlMax` has a
unique strong solution on every `[0, T]`, `T > 0`, and it leaves `K`. -/
theorem tsd_not_propagates (c : R3) {R : ℝ} (hR : 0 < R) :
    E0R c hR ∈ tsdS (euclBall c R) ∧
      mk3 (0 : L2 ℝ (euclBall c R)) (E0R c hR) (0 : trSub ℝ (euclBall c R)) ∈
        (hessCurlMax ℝ (isOpen_euclBall c R)).wave.domain ∧
      mk3 (0 : L2 ℝ (euclBall c R)) (E0R c hR) (0 : trSub ℝ (euclBall c R)) ∈
        HilbertComplex.totalSub (ShortHilbertComplex.family3
          (⊥ : Submodule ℝ (L2 ℝ (euclBall c R))) (tsdS (euclBall c R)) (tsdT (euclBall c R))) ∧
      ∀ T > 0, Evolution.IsStrongSolution (hessCurlMax ℝ (isOpen_euclBall c R)).wave (Icc 0 T) 0
          (fun t => (hessCurlMax ℝ (isOpen_euclBall c R)).toHilbertComplex.waveGroup.S t
            (mk3 (0 : L2 ℝ (euclBall c R)) (E0R c hR) (0 : trSub ℝ (euclBall c R)))) ∧
        (∀ U, U 0 = mk3 (0 : L2 ℝ (euclBall c R)) (E0R c hR) (0 : trSub ℝ (euclBall c R)) →
          Evolution.IsStrongSolution (hessCurlMax ℝ (isOpen_euclBall c R)).wave (Icc 0 T) 0 U →
            (EqOn U (fun t => (hessCurlMax ℝ (isOpen_euclBall c R)).toHilbertComplex.waveGroup.S t
              (mk3 (0 : L2 ℝ (euclBall c R)) (E0R c hR) (0 : trSub ℝ (euclBall c R)))) (Icc 0 T) ∧
            ∃ t ∈ Icc 0 T, U t ∉ HilbertComplex.totalSub (ShortHilbertComplex.family3
              (⊥ : Submodule ℝ (L2 ℝ (euclBall c R))) (tsdS (euclBall c R)) (tsdT (euclBall c R))))) :=
  ⟨(witness_ballE c hR).mem_tsd, (witness_ballE c hR).mem_domain, (witness_ballE c hR).mem_K,
    (witness_ballE c hR).not_propagates⟩

/-- On every ball, `L²(TSD) ∩ H̊(sym curl, T)` is not dense in `L²(TSD)`. -/
theorem not_dense_tsdT (c : R3) {R : ℝ} (hR : 0 < R) :
    closure ((tsdT (euclBall c R) : Set (trSub ℝ (euclBall c R))) ∩
      (hessCurlMax ℝ (isOpen_euclBall c R)).d₁†.domain) ≠ (tsdT (euclBall c R) : Set _) := by
  intro he
  obtain ⟨h1, h2⟩ := (witness_ballE c hR).curl_not_mem_closure
  exact h2 (by rw [he]; exact h1)

end Feec.Counterexamples.EveryBallSymTSD
