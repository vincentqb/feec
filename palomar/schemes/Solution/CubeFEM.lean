module

public import Solution.Cube
public import Solution.Spaces
public import Feec.Models.Cube.RegularDecomposition

/-!
# The elements of Table 5.1 on the cube satisfy the hypotheses of `FEEC.weakSymmetry`

For smoothed projections `hT`, `hB` of the two rows from one smoother, `cubeQ hT hB N` is the
discretization of `𝒟 = cubeDataOf D0 D1` by the spaces of `Feec.Models.Cube.FEM.polyMin` with the
projections of `hT.proj N`, `hB.proj N` (the challenge's form of
`Feec.Models.Cube.WeakSymmetry.cubeFEM`). Its spaces are the challenge's `femSpaceMin`
(`cubeQ_V0`, …), and with one constant `C` the continuous hypotheses
(`Feec.Models.Cube.WeakSymmetry.bggStability_of`), the uniform bounds
(`PolySmoothingEstimatesMin.norm_proj_le`), (5.4) (`proj_wsL2_piMap_proj`) and the consistency
(`cubeFEM_happ0`, `cubeFEMReg`) hold (`cube_hyps`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, Table 5.1, Props 5.7, 5.9
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.5

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set MeasureTheory Filter

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

/-! ### Stability -/

/-- **The continuous hypotheses on the cube** with any `C ≥ (2π)⁻¹, C_R, √2`. -/
theorem isStable_𝒟 {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) {C : ℝ}
    (h1 : (2 * Real.pi)⁻¹ ≤ C) (h2 : CR ≤ C) (h3 : √2 ≤ C) : 𝒟.IsStable C := by
  have H := bggStability_of hCR0 hCR
  have hC0 : 0 ≤ C := (Real.sqrt_nonneg _).trans h3
  refine ⟨fun σ => (H.poinc0 σ).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)),
    fun φ => ?_, fun μ hμ => ?_, fun v => ?_, fun x => ?_,
    (norm_wsL2_le 0 zero_le_one).trans h3, (norm_wsL2_le 1 le_rfl).trans h3⟩
  · have := H.poinct0 (e0 φ)
    rw [LinearIsometryEquiv.norm_map, norm_dt0_e0] at this
    exact this.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  · obtain ⟨ρ, hρ⟩ := H.exact1 μ hμ
    exact ⟨ρ, congrArg Subtype.val hρ⟩
  · obtain ⟨ψ, w, hv, hw⟩ := H.hodget1 (e1 v)
    refine ⟨e0.symm ψ, e1.symm w, ?_, ?_⟩
    · have := congrArg incl1 hv
      rw [map_add] at this
      exact this
    · have hn : ‖((e1.symm w : 𝒟.dt1.domain) : Wv W1)‖ = ‖w‖ := e1.symm.norm_map w
      rw [hn]
      exact hw.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  · obtain ⟨φ, e, hφ⟩ := H.reg x
    have hS : 𝒟.S0 (e0.symm φ) = ((bggSegment.S0 φ : U1) : W1) := S0_e0_symm φ
    have hx : (⟨𝒟.S0 (e0.symm φ), (isBGG_𝒟.2.2 (e0.symm φ)).1⟩ : D1.domain) =
        bggSegment.S0 φ := Subtype.ext hS
    refine ⟨e0.symm φ, (isBGG_𝒟.2.2 (e0.symm φ)).1, (congrArg D1 hx).trans e, ?_⟩
    rw [norm_dt0_e0_symm]
    exact hφ.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

/-! ### The discretization -/

section FEM

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

theorem norm_piMap_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →ₗ[ℝ] V) {B : ℝ} (hB0 : 0 ≤ B) (h : ∀ x, ‖P x‖ ≤ B * ‖x‖) (x : Wv V) :
    ‖piMap P x‖ ≤ B * ‖x‖ := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [piMap_apply, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h (x a)) 2

variable (N : ℕ)

/-- The top-row projection in degree `i` as a bounded map. -/
def πT (i : ℤ) : L2F ℝ (cubeDomain 3) (formIdx 3 i) →L[ℝ] L2F ℝ (cubeDomain 3) (formIdx 3 i) :=
  ((hT.proj N).π i).mkContinuous (2 * C) (hT.norm_proj_le N i)

/-- The bottom-row projection in degree `i`, componentwise, as a bounded map. -/
def πB (i : ℤ) : Wv (L2F ℝ (cubeDomain 3) (formIdx 3 i)) →L[ℝ]
    Wv (L2F ℝ (cubeDomain 3) (formIdx 3 i)) :=
  (piMap ((hB.proj N).π i)).mkContinuous (2 * C)
    (norm_piMap_le _ hB.two_mul_nonneg (hB.norm_proj_le N i))

@[simp] theorem πT_apply (i : ℤ) (x) : πT hT N i x = (hT.proj N).π i x := rfl
@[simp] theorem πB_apply (i : ℤ) (x) (a : Fin 3) : πB hB N i x a = (hB.proj N).π i (x a) := rfl

/-- **The discretization of Table 5.1** of `𝒟`. -/
def cubeQ : 𝒟.Discretization where
  V0 := (polyMin 3 PolySeq.lowestOrder N).V 0
  V1 := (polyMin 3 PolySeq.lowestOrder N).V 1
  V2 := (polyMin 3 PolySeq.lowestOrder N).V 2
  Vt0 := tsub ((polyMin 3 PolySeq.lagrangeP2 N).V 0)
  Vt1 := tsub ((polyMin 3 PolySeq.lagrangeP2 N).V 1)
  Vt2 := tsub ((polyMin 3 PolySeq.lagrangeP2 N).V 2)
  fd0 := inferInstanceAs (FiniteDimensional ℝ ((polyMin 3 PolySeq.lowestOrder N).V 0))
  fd1 := inferInstanceAs (FiniteDimensional ℝ ((polyMin 3 PolySeq.lowestOrder N).V 1))
  fd2 := inferInstanceAs (FiniteDimensional ℝ ((polyMin 3 PolySeq.lowestOrder N).V 2))
  fdt0 := finiteDimensional_tsub ((polyMin 3 PolySeq.lagrangeP2 N).V 0)
  fdt1 := finiteDimensional_tsub ((polyMin 3 PolySeq.lagrangeP2 N).V 1)
  fdt2 := finiteDimensional_tsub ((polyMin 3 PolySeq.lagrangeP2 N).V 2)
  le0 _ hx := mem_D0_of_mem_V hx
  le1 _ hx := mem_D1_of_mem_V hx
  let0 _ hx a := mem_D0_of_mem_V (hx a)
  let1 _ hx a := mem_D1_of_mem_V (hx a)
  d0_mem x hx := D0_mem_V x hx
  d1_mem x hx := D1_mem_V x hx
  dt0_mem x hx a := D0_mem_V ⟨_, x.2 a⟩ (hx a)
  dt1_mem x hx a := D1_mem_V ⟨_, x.2 a⟩ (hx a)
  π0 := πT hT N 0
  π1 := πT hT N 1
  π2 := πT hT N 2
  πt0 := πB hB N 0
  πt1 := πB hB N 1
  πt2 := πB hB N 2
  π0_mem x := (hT.proj N).mem 0 x
  π1_mem x := (hT.proj N).mem 1 x
  π2_mem x := (hT.proj N).mem 2 x
  πt0_mem x a := (hB.proj N).mem 0 (x a)
  πt1_mem x a := (hB.proj N).mem 1 (x a)
  πt2_mem x a := (hB.proj N).mem 2 (x a)
  π0_id x hx := (hT.proj N).proj 0 x hx
  π1_id x hx := (hT.proj N).proj 1 x hx
  π2_id x hx := (hT.proj N).proj 2 x hx
  πt0_id x hx := PiLp.ext fun a => (hB.proj N).proj 0 (x a) (hx a)
  πt1_id x hx := PiLp.ext fun a => (hB.proj N).proj 1 (x a) (hx a)
  πt2_id x hx := PiLp.ext fun a => (hB.proj N).proj 2 (x a) (hx a)
  comm0 x := D0_π (hT.proj N) x
  comm1 x := D1_π (hT.proj N) x
  commt0 x := PiLp.ext fun a => D0_π (hB.proj N) ⟨_, x.2 a⟩
  commt1 x := PiLp.ext fun a => D1_π (hB.proj N) ⟨_, x.2 a⟩

theorem cubeQ_isBounded : (cubeQ hT hB N).IsBounded (2 * C) := by
  have h := hT.two_mul_nonneg
  have hB0 := hB.two_mul_nonneg
  exact ⟨LinearMap.mkContinuous_norm_le _ h (hT.norm_proj_le N 0),
    LinearMap.mkContinuous_norm_le _ h (hT.norm_proj_le N 1),
    LinearMap.mkContinuous_norm_le _ h (hT.norm_proj_le N 2),
    LinearMap.mkContinuous_norm_le _ h (norm_piMap_le _ hB0 (hB.norm_proj_le N 0)),
    LinearMap.mkContinuous_norm_le _ h (norm_piMap_le _ hB0 (hB.norm_proj_le N 1)),
    LinearMap.mkContinuous_norm_le _ h (norm_piMap_le _ hB0 (hB.norm_proj_le N 2))⟩

theorem cubeQ_compatible : (cubeQ hT hB N).Compatible := fun ψ => by
  exact proj_wsL2_piMap_proj hT hB N ψ

/-- `e0` maps the discrete space of `cubeQ` onto that of `cubeFEM`. -/
theorem e0_mem {ψ : 𝒟.dt0.domain} (hψ : (ψ : Wv W0) ∈ (cubeQ hT hB N).Vt0) :
    e0 ψ ∈ (cubeFEM hT hB N).Vt0h := fun a => hψ a

theorem e1_mem {v : 𝒟.dt1.domain} (hv : (v : Wv W1) ∈ (cubeQ hT hB N).Vt1) :
    e1 v ∈ (cubeFEM hT hB N).Vt1h := fun a => hv a

theorem coe_S0h_e0 (ψ : 𝒟.dt0.domain) :
    (((cubeFEM hT hB N).S0h (e0 ψ) : U1) : W1) = (cubeQ hT hB N).π1 (𝒟.S0 ψ) := by
  rfl

theorem S1h_e1 (v : 𝒟.dt1.domain) :
    (cubeFEM hT hB N).S1h (e1 v) = (cubeQ hT hB N).π2 (𝒟.S1 v) := by
  rfl

theorem incl1_Pt1 (w : Wv U1) :
    incl1 ((cubeFEM hT hB N).Pt1 w) = (cubeQ hT hB N).πt1 (incl1 w) := rfl

theorem norm_le_dt0 (φ : 𝒟.dt0.domain) : ‖(φ : Wv W0)‖ ≤ ‖𝒟.dt0 φ‖ := by
  have hp := seg_poinct0 (e0 φ)
  have hn : ‖e0 φ‖ = ‖φ‖ := e0.norm_map φ
  have hd : ‖piMap segD0 (e0 φ)‖ = ‖𝒟.dt0 φ‖ := norm_dt0_e0 φ
  rw [hn, hd] at hp
  have h0 : (2 * Real.pi)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]; nlinarith [Real.two_le_pi]
  exact hp.trans (by
    nlinarith [norm_nonneg (𝒟.dt0 φ), inv_nonneg.2 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)])

set_option maxHeartbeats 2000000 in
/-- **Consistency of the elements of Table 5.1** at the order `h_N`, for every constant
`C' ≥ A`. -/
theorem cubeQ_isConsistent {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    ∃ A, 0 ≤ A ∧ ∀ C', A ≤ C' → ∀ N,
      (cubeQ hT hB N).IsConsistent C' (Feec.Models.Cube.FEM.meshSize N) := by
  obtain ⟨Capp, hCapp0, hCapp⟩ := cubeFEM_happ0 hT hB
  have hR := regConst_nonneg hT
  refine ⟨√2 * Capp + CR + regConst C * CR, by positivity, fun C' hC' N => ⟨fun ψ hψ => ?_,
    fun v hv => ?_⟩⟩
  · have hh := (meshSize_pos N).le
    have h := hCapp N (e0 ψ) (e0_mem hT hB N hψ)
    unfold Feec.BGG.graphSq at h
    have e : ‖bggSegment.S0 (e0 ψ) - (cubeFEM hT hB N).S0h (e0 ψ)‖ =
        ‖𝒟.S0 ψ - (cubeQ hT hB N).π1 (𝒟.S0 ψ)‖ := by
      rw [← Submodule.norm_coe, Submodule.coe_sub, S0_e0, coe_S0h_e0]
    have hn : ‖e0 ψ‖ = ‖ψ‖ := e0.norm_map ψ
    rw [e, hn, norm_dt0_e0] at h
    have hg : ‖ψ‖ ^ 2 + ‖𝒟.dt0 ψ‖ ^ 2 ≤ 2 * ‖𝒟.dt0 ψ‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (norm_le_dt0 ψ) 2
      have e' : ‖(ψ : Wv W0)‖ = ‖ψ‖ := rfl
      rw [e'] at this; linarith
    have h2 : ‖𝒟.S0 ψ - (cubeQ hT hB N).π1 (𝒟.S0 ψ)‖ ^ 2 ≤
        (√2 * Capp * Feec.Models.Cube.FEM.meshSize N * ‖𝒟.dt0 ψ‖) ^ 2 := by
      calc _ ≤ _ := h
        _ ≤ (Capp * Feec.Models.Cube.FEM.meshSize N) ^ 2 * (2 * ‖𝒟.dt0 ψ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hg (sq_nonneg _)
        _ = _ := by
          have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          linear_combination (-(Capp * Feec.Models.Cube.FEM.meshSize N * ‖𝒟.dt0 ψ‖) ^ 2) * h2
    have h3 := le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h2
    refine h3.trans ?_
    have : √2 * Capp ≤ C' := le_trans (by linarith [mul_nonneg hR hCR0]) hC'
    gcongr
  · have hh := (meshSize_pos N).le
    have Rg := cubeFEMReg hT hB N hCR0 hCR (le_refl (regConst C))
    obtain ⟨y, hy1, hy2⟩ := Rg.exists_potential (e1 v) (e1_mem hT hB N hv)
    have hy : ‖y‖ ≤ CR * ‖𝒟.dt1 v‖ := hy2
    have hC1 : regConst C * CR ≤ C' :=
      le_trans (by linarith [mul_nonneg (Real.sqrt_nonneg 2) hCapp0]) hC'
    refine ⟨ofWv1 (Rg.R y), (dt1_ofWv1 _).trans (hy1.trans (dt1_e1 v)), ?_, ?_, ?_⟩
    · rw [norm_ofWv1]
      refine (Rg.norm_R_le y).trans ?_
      rw [one_mul]
      refine hy.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      linarith [mul_nonneg hR hCR0, mul_nonneg (Real.sqrt_nonneg 2) hCapp0]
    · have e : ((ofWv1 (Rg.R y) : 𝒟.dt1.domain) : Wv W1) -
          (cubeQ hT hB N).πt1 (ofWv1 (Rg.R y)) =
          incl1 (Rg.R y - (cubeFEM hT hB N).Pt1 (Rg.R y)) := by
        rw [map_sub, coe_ofWv1, incl1_Pt1]
      have hn : ‖((ofWv1 (Rg.R y) : 𝒟.dt1.domain) : Wv W1) -
          (cubeQ hT hB N).πt1 (ofWv1 (Rg.R y))‖ = ‖Rg.R y - (cubeFEM hT hB N).Pt1 (Rg.R y)‖ := by
        rw [e]; exact norm_incl1 _
      rw [hn]
      refine (Rg.approx_Pt1 y).trans ?_
      calc regConst C * Feec.Models.Cube.FEM.meshSize N * ‖y‖
          ≤ regConst C * Feec.Models.Cube.FEM.meshSize N * (CR * ‖𝒟.dt1 v‖) := by gcongr
        _ = regConst C * CR * Feec.Models.Cube.FEM.meshSize N * ‖𝒟.dt1 v‖ := by ring
        _ ≤ _ := by gcongr
    · have e : 𝒟.S1 (ofWv1 (Rg.R y)) - (cubeQ hT hB N).π2 (𝒟.S1 (ofWv1 (Rg.R y))) =
          (bggSegment.S1 - (cubeFEM hT hB N).S1h) (Rg.R y) := by
        rw [S1_ofWv1]; rfl
      rw [e]
      refine (Rg.approx_S1 y).trans ?_
      calc regConst C * Feec.Models.Cube.FEM.meshSize N * ‖y‖
          ≤ regConst C * Feec.Models.Cube.FEM.meshSize N * (CR * ‖𝒟.dt1 v‖) := by gcongr
        _ = regConst C * CR * Feec.Models.Cube.FEM.meshSize N * ‖𝒟.dt1 v‖ := by ring
        _ ≤ _ := by gcongr

end FEM

end FEEC
