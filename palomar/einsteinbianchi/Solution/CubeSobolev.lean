module

public import Solution.Sobolev
public import Solution.CubeWave
public import Solution.CubeStatic
public import Feec.Physics.EinsteinBianchi.WaveFEMRegularity

/-!
# The `H¹` rates on the cube

The `H¹` hypotheses of `FEEC.weakSymmetry_electric` put the exact solution in `Feec`'s relative
parity class `H¹_univ` (`isSobolevStaticTr_of`, `isSobolevStateTr_of`: Gaffney's identity, the
`H¹(ℝⁿ)` data giving `d*`; `dσ = S⁰φ` and `S¹u` from the `φₐ`, `uₐ`). The static rate is then the
abstract Thm 5.5 with the quasi-optimality of the smoothed projections for `H¹_univ` data
(`norm_sub_proj_le_sobStateConst`), and the wave rate is
`Feec.Models.Cube.WeakSymmetry.cubeWave_rate_sobolev_of_one_le`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 5.5, §6.3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter

@[expose] public noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

/-- `H¹(Q)` data with bound `L ≥ 0`. -/
theorem h1Data_of_isSobolevForm' {k : ℕ} {L : ℝ} (hL : 0 ≤ L) {x : L2Form (cube 3) k}
    (hx : IsSobolevForm (cube 3) 1 k L x) :
    Nonempty (H1Data (cubeDomain 3) (x : L2F ℝ (cubeDomain 3) (formIdx 3 k)) L) := by
  have h := h1Data_of_isSobolevForm hx
  rwa [abs_of_nonneg hL] at h

/-- The constant of the `H¹` classes. -/
theorem exists_h1Const : ∃ c : ℝ, 1 ≤ c ∧
    (∀ {B : ℝ} {x : W0}, 0 ≤ B → x ∈ D0.domain → H1Data (cubeDomain 3) x B →
      SobRel 1 (c * B) 0 x) ∧
    (∀ {B : ℝ} {x : W1}, 0 ≤ B → x ∈ D1.domain → H1Data (cubeDomain 3) x B →
      SobRel 1 (c * B) 1 x) ∧
    (∀ {B : ℝ} {x : W2}, 0 ≤ B → x ∈ D2min.domain → H1Data (cubeDomain 3) x B →
      SobRel 1 (c * B) 2 x) ∧
    (∀ {B : ℝ} {v : Wv W0} {x : W1}, 0 ≤ B → (∀ a, H1Data (cubeDomain 3) (v a) B) →
      x = wsL2 (Ω := cubeDomain 3) 0 v → ∀ hx : x ∈ D1.domain, D1 ⟨x, hx⟩ = 0 →
        SobRel 1 (c * B) 1 x) ∧
    (∀ {B : ℝ} {v : Wv W1}, 0 ≤ B → (∀ a, v a ∈ D1.domain) →
      (∀ a, H1Data (cubeDomain 3) (v a) B) →
        SobRel 1 (c * B) 2 (wsL2 (Ω := cubeDomain 3) 1 v)) := by
  obtain ⟨c0, h0, H0⟩ := sobRel_of_h1_zero
  obtain ⟨c1, h1, H1⟩ := sobRel_of_h1_one
  obtain ⟨c2, h2, H2⟩ := sobRel_of_h1_two
  obtain ⟨c3, h3, H3⟩ := sobRel_wsL2_zero
  obtain ⟨c4, h4, H4⟩ := sobRel_wsL2_one
  set c := c0 + c1 + c2 + c3 + c4 + 1
  have m : ∀ {c' B : ℝ} {k : ℕ} {x : L2F ℝ (cubeDomain 3) (formIdx 3 k)}, c' ≤ c → 0 ≤ B →
      SobRel 1 (c' * B) k x → SobRel 1 (c * B) k x := fun hc hB h =>
    h.mono (mul_le_mul_of_nonneg_right hc hB)
  refine ⟨c, by linarith, fun hB hx h => m (by linarith) hB (H0 hB hx h),
    fun hB hx h => m (by linarith) hB (H1 hB hx h), fun hB hx h => m (by linarith) hB (H2 hB hx h),
    fun hB hv hxv hx hd => m (by linarith) hB (H3 hB hv hxv hx hd),
    fun hB hvD hv => m (by linarith) hB (H4 hB hvD hv)⟩

/-- **The static `H¹` hypotheses of the challenge give `Feec`'s class `IsSobolevStaticTr 1`.** -/
theorem isSobolevStaticTr_of : ∃ c : ℝ, 1 ≤ c ∧ ∀ {L : ℝ} {σ : 𝒟.d0.domain}
    {φ : 𝒟.dt0.domain} {u : 𝒟.dt1.domain}, 0 ≤ L → 𝒟.d0 σ = 𝒟.S0 φ →
    IsSobolevForm (cube 3) 1 0 L (σ : W0) →
    (∀ a, IsSobolevForm (cube 3) 1 0 L ((φ : Wv W0) a)) →
    (∀ a, IsSobolevForm (cube 3) 1 1 L (𝒟.dt0 φ a)) →
    (∀ a, IsSobolevForm (cube 3) 1 1 L ((u : Wv W1) a)) →
    (∀ a, IsSobolevForm (cube 3) 1 2 L (𝒟.dt1 u a)) →
    IsSobolevStaticTr 1 (c * L) σ (e0 φ) (e1 u) := by
  obtain ⟨c, hc, H0, H1, H2, H3, H4⟩ := exists_h1Const
  refine ⟨c, hc, fun {L σ φ u} hL hcon hσ hφ hdφ hu hdu => ?_⟩
  have hv : ∀ a, H1Data (cubeDomain 3) ((φ : Wv W0) a) L := fun a =>
    (h1Data_of_isSobolevForm' hL (hφ a)).some
  have hw : ∀ a, H1Data (cubeDomain 3) ((u : Wv W1) a) L := fun a =>
    (h1Data_of_isSobolevForm' hL (hu a)).some
  obtain ⟨hσ'⟩ := h1Data_of_isSobolevForm' hL hσ
  refine ⟨H0 hL σ.2 hσ', H3 hL hv hcon (D0_mem_D1 σ) (D1_D0 σ), fun a => H0 hL (φ.2 a) (hv a),
    fun a => ?_, fun a => H1 hL (u.2 a) (hw a), fun a => ?_, H4 hL (fun a => u.2 a) hw⟩
  · obtain ⟨h⟩ := h1Data_of_isSobolevForm' hL (hdφ a)
    exact H1 hL (D0_mem_D1 _) h
  · obtain ⟨h⟩ := h1Data_of_isSobolevForm' hL (hdu a)
    exact H2 hL (Feec.EinsteinBianchi.WaveFEM.D1_mem_D2min _) h

/-- **The `H¹` states of the challenge are in `Feec`'s class `IsSobolevStateTr 1`.** -/
theorem isSobolevStateTr_of : ∃ c : ℝ, 1 ≤ c ∧ ∀ {L : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1}
    {M : W2} {ρ : Wv W2}, 0 ≤ L → IsH1State L (σ : W0) (incl0 φ) (incl1 u) M ρ →
    IsSobolevStateTr 1 (c * L) σ φ u M ρ := by
  obtain ⟨c, hc, H0, H1, H2, H3, H4⟩ := exists_h1Const
  refine ⟨c, hc, fun {L σ φ u M ρ} hL h => ?_⟩
  obtain ⟨hσ, hdφ, hu, hdu, hM, hρ, hMd, hρd⟩ := h
  rw [dMin_eq] at hMd hρd
  have hw : ∀ a, H1Data (cubeDomain 3) ((u a : U1) : W1) L := fun a =>
    (h1Data_of_isSobolevForm' hL (hu a)).some
  obtain ⟨hσ'⟩ := h1Data_of_isSobolevForm' hL hσ
  obtain ⟨hM'⟩ := h1Data_of_isSobolevForm' hL hM
  refine ⟨H0 hL σ.2 hσ', fun a => ?_, fun a => H1 hL (u a).2 (hw a), fun a => ?_,
    H2 hL hMd hM', fun a => ?_, H4 hL (fun a => (u a).2) hw⟩
  · have h := hdφ a (by rw [dMin_eq]; exact (φ a).2)
    rw [LinearPMap.apply_of_eq' (dMin_eq (cube 3) 0)] at h
    obtain ⟨h'⟩ := h1Data_of_isSobolevForm' hL h
    exact H1 hL (D0_mem_D1 _) h'
  · have h := hdu a (by rw [dMin_eq]; exact (u a).2)
    rw [LinearPMap.apply_of_eq' (dMin_eq (cube 3) 1)] at h
    obtain ⟨h'⟩ := h1Data_of_isSobolevForm' hL h
    exact H2 hL (Feec.EinsteinBianchi.WaveFEM.D1_mem_D2min _) h'
  · obtain ⟨h'⟩ := h1Data_of_isSobolevForm' hL (hρ a)
    exact H2 hL (hρd a) h'

section FEM

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

set_option maxHeartbeats 2000000 in
/-- **The static rate on the cube for `H¹_univ` data** from the abstract theorem. -/
theorem cube_static_rate_sob {C' : ℝ} (hS : 𝒟.IsStable C')
    (hb : ∀ N, (cubeQ hT hB N).IsBounded C')
    (hc : ∀ N, (cubeQ hT hB N).IsConsistent C' (Feec.Models.Cube.FEM.meshSize N)) :
    ∃ K, ∀ N F σ φ u lam σh φh uh lamh L, 𝒟.IsSolution F σ φ u lam →
      IsSobolevStaticTr 1 L σ (e0 φ) (e1 u) → ‖lam‖ ≤ L →
      (cubeQ hT hB N).IsDiscreteSolution F σh φh uh lamh →
      (cubeQ hT hB N).errorSq σ σh φ φh u uh ≤
        (K * L * Feec.Models.Cube.FEM.meshSize N) ^ 2 := by
  obtain ⟨K₀, hK₀⟩ := WeakSymmetryData.weakSymmetry_of.{0} C'
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = sobStateConst C := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := hs ▸ sobStateConst_nonneg hT
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧
      2 * s ^ 2 + 2 * (3 * s ^ 2) + (1 + 8 * C ^ 2) * (2 * (3 * s ^ 2)) + s ^ 2 ≤ A :=
    ⟨_, by positivity, le_rfl⟩
  refine ⟨√(max K₀ 0 * (A + 2)), fun N F σ φ u lam σh φh uh lamh L hsol hsob hlam hdisc => ?_⟩
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hlam
  obtain ⟨h, hh0, rfl⟩ : ∃ h, 0 ≤ h ∧ h = Feec.Models.Cube.FEM.meshSize N :=
    ⟨_, (meshSize_pos N).le, rfl⟩
  have hm : Feec.Models.Cube.FEM.meshSize N ^ min (1 : ℝ) 1 = Feec.Models.Cube.FEM.meshSize N := by
    rw [min_self, Real.rpow_one]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = s * Feec.Models.Cube.FEM.meshSize N * L := ⟨_, rfl⟩
  have lT : Feec.FiniteElement.PolySeq.lowestOrder = Feec.FiniteElement.PolySeq.lowestOrder ∨
      Feec.FiniteElement.PolySeq.lowestOrder = Feec.FiniteElement.PolySeq.lagrangeP2 :=
    Or.inl rfl
  have lB : Feec.FiniteElement.PolySeq.lagrangeP2 = Feec.FiniteElement.PolySeq.lowestOrder ∨
      Feec.FiniteElement.PolySeq.lagrangeP2 = Feec.FiniteElement.PolySeq.lagrangeP2 :=
    Or.inr rfl
  have close : ∀ {S : Feec.FiniteElement.PolySeq} (hE : PolySmoothingEstimatesMin 3 S p C),
      (S = Feec.FiniteElement.PolySeq.lowestOrder ∨ S = Feec.FiniteElement.PolySeq.lagrangeP2) →
      ∀ {k : ℕ}, k < 3 →
      ∀ {x : L2F ℝ (cubeDomain 3) (formIdx 3 k)}, SobRel 1 L k x →
        ‖x - (hE.proj N).π k x‖ ≤ δ := fun {S} hE hS' {k} hk {x} hx => by
    have := norm_sub_proj_le_sobStateConst hT hE hS' N hk zero_le_one hx
    rwa [hm, ← hs, ← hδ] at this
  obtain ⟨hσ, hdσ, hφ, hdφ, hu, hdu, hSu⟩ := hsob
  have hz : ∀ w : 𝒟.d1.domain, |⟪𝒟.S1 u, 𝒟.d1 w⟫_ℝ| ≤ L * ‖(w : W1)‖ := fun w =>
    abs_inner_D1_le_of_sobRel_one hSu w
  have hn : ‖𝒟.S1 u‖ ≤ L := hSu.norm_le zero_le_one
  obtain ⟨-, hrate⟩ := hK₀ 𝒟 (cubeQ hT hB N) isBGG_𝒟 hS (hb N) (cubeQ_compatible hT hB N)
  have key := hrate _ L hh0 (hc N) F σ φ u lam σh φh uh lamh hsol hlam hz hdisc
  set P := (cubeQ hT hB N).projErrorSq σ φ u with hPdef
  set R := ‖𝒟.S1 u - (cubeQ hT hB N).π2 (𝒟.S1 u)‖ ^ 2 with hRdef
  have hδ2 : δ ^ 2 = s ^ 2 * (L * Feec.Models.Cube.FEM.meshSize N) ^ 2 := by rw [hδ]; ring
  have hPR : P + R ≤ A * (L * Feec.Models.Cube.FEM.meshSize N) ^ 2 := by
    have e : P =
        (‖(cubeQ hT hB N).π0 σ - σ‖ ^ 2 + ‖(cubeQ hT hB N).π1 (𝒟.d0 σ) - 𝒟.d0 σ‖ ^ 2) +
        (‖(cubeQ hT hB N).πt0 φ - φ‖ ^ 2 + ‖(cubeQ hT hB N).πt1 (𝒟.dt0 φ) - 𝒟.dt0 φ‖ ^ 2) +
        (‖(cubeQ hT hB N).πt1 u - u‖ ^ 2 +
          ‖(cubeQ hT hB N).π2 (𝒟.S1 ((cubeQ hT hB N).πt1 u - u))‖ ^ 2 +
          ‖(cubeQ hT hB N).πt2 (𝒟.dt1 u) - 𝒟.dt1 u‖ ^ 2) := by
      rw [hPdef]; unfold WeakSymmetryData.Discretization.projErrorSq; ring
    obtain ⟨e00, e01⟩ := projErr0_eq hT hB N σ
    obtain ⟨e10, e11⟩ := projErr1_eq hT hB N φ
    obtain ⟨e20, e21, e22⟩ := projErr2_eq hT hB N u
    rw [e]
    have h0 := graphSq_P0_sub_le_of_close hT hB N σ (close hT lT (by norm_num) hσ)
      (close hT lT (by norm_num) hdσ)
    have h1 := graphSq_Pt0_sub_le_of_close hT hB N (e0 φ)
      (fun a => close hB lB (by norm_num) (hφ a)) (fun a => close hB lB (by norm_num) (hdφ a))
    have h2 := gnSq_Pt1_sub_le_of_close hT hB N (e1 u)
      (fun a => close hB lB (by norm_num) (hu a)) (fun a => close hB lB (by norm_num) (hdu a))
    unfold Feec.BGG.graphSq at h0 h1
    unfold Feec.BGG.Discrete.gnSq at h2
    rw [← e00, ← e01] at h0
    rw [← e10, ← e11] at h1
    rw [← e20, ← e21, ← e22] at h2
    have h3 : ‖𝒟.S1 u - (cubeQ hT hB N).π2 (𝒟.S1 u)‖ ≤ δ := close hT lT (by norm_num) hSu
    have h3' := pow_le_pow_left₀ (norm_nonneg _) h3 2
    rw [hδ2] at h0 h1 h2 h3'
    have hA' := mul_le_mul_of_nonneg_right hA (sq_nonneg (L * Feec.Models.Cube.FEM.meshSize N))
    nlinarith
  have hS2 : ‖𝒟.S1 u‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hX : P + Feec.Models.Cube.FEM.meshSize N ^ 2 * (L ^ 2 + ‖𝒟.S1 u‖ ^ 2) + R ≤
      (A + 2) * (L * Feec.Models.Cube.FEM.meshSize N) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hS2 (sq_nonneg (Feec.Models.Cube.FEM.meshSize N))
    nlinarith [sq_nonneg (L * Feec.Models.Cube.FEM.meshSize N)]
  have hX0 : 0 ≤ P + Feec.Models.Cube.FEM.meshSize N ^ 2 * (L ^ 2 + ‖𝒟.S1 u‖ ^ 2) + R := by
    have : 0 ≤ P := by rw [hPdef]; unfold WeakSymmetryData.Discretization.projErrorSq; positivity
    positivity
  calc _ ≤ _ := key
    _ ≤ max K₀ 0 * ((A + 2) * (L * Feec.Models.Cube.FEM.meshSize N) ^ 2) :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0).trans
          (mul_le_mul_of_nonneg_left hX (le_max_right _ _))
    _ = (√(max K₀ 0 * (A + 2)) * L * Feec.Models.Cube.FEM.meshSize N) ^ 2 := by
        have hs' : √(max K₀ 0 * (A + 2)) ^ 2 = max K₀ 0 * (A + 2) :=
          Real.sq_sqrt (mul_nonneg (le_max_right _ _) (by linarith))
        rw [show (√(max K₀ 0 * (A + 2)) * L * Feec.Models.Cube.FEM.meshSize N) ^ 2 =
          √(max K₀ 0 * (A + 2)) ^ 2 * (L * Feec.Models.Cube.FEM.meshSize N) ^ 2 by ring, hs']
        ring

end FEM

end FEEC
