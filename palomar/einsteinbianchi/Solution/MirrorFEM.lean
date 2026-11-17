module

public import Solution.MirrorData
public import Solution.Cube
public import Solution.DiscreteWave
public import Feec.Models.Cube.MirrorWeakSymmetryConvergence

/-!
# The mirror data of the challenge and their discretization by the mirror scheme

`mirrorData` is `𝒟m`, the data of `Feec.Models.Cube.MirrorWeakSymmetry.mirrorBGGSegment` in
`Feec`'s types (`mirrorData_eq`: `dMax = d_∅`, `dPart_eq`, `wedge_eq`); they are BGG data
(`isBGG_𝒟m`), the domain of the bottom row being `Feec`'s `∏ₐ H_{a}Λᵏ(Q)` (`vecFamEquiv`).

For one smoother of both rows (`exists_mirror_estimates`), `mirrorQ hT hB N` is the challenge's
form of `Feec.Models.Cube.MirrorWeakSymmetry.mirrorFEM`: the spaces of
`Feec.Models.Cube.FEM.polyPartial` with the parity-smoothed projections. Its projections are
bounded by `2C` (`mirrorQ_isBounded`), it satisfies (5.4) (`mirrorQ_compatible`, from
`proj_wsL2_compatible`) and it is consistent at the order `h_N` (`mirrorQ_isConsistent`, from
`mirrorFEM_happ0` with the Poincaré inequality of the bottom row, and the regular potentials
`mirrorFEMReg`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.2, §6.3, Table 6.1, Prop 5.9

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM
  Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)
open Feec.Models.Cube.DeRhamIdent (dPart_empty dPart_comp)

/-! ### `∏ₐ D(Tₐ)` and `Feec`'s vectors of domain elements -/

section VecFam

variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] (T : Fin n → E →ₗ.[ℝ] F)

/-- `∏ₐ D(Tₐ)` (the domain of `vecOp T`) as `Feec`'s vectors of elements of the `D(Tₐ)`. -/
def vecFamEquiv : (vecOp T).domain ≃ₗᵢ[ℝ] PiLp 2 (fun a => (T a).domain) where
  toFun v := WithLp.toLp 2 fun a => ⟨(v : PiLp 2 fun _ : Fin n => E) a, v.2 a⟩
  invFun w := ⟨WithLp.toLp 2 fun a => (w a : E), fun a => (w a).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' v := by
    change ‖(WithLp.toLp 2 fun a => (⟨(v : PiLp 2 fun _ : Fin n => E) a, v.2 a⟩ : (T a).domain) :
      PiLp 2 (fun a => (T a).domain))‖ = ‖(v : PiLp 2 fun _ : Fin n => E)‖
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    rfl

end VecFam

/-! ### The mirror data -/

/-- **The mirror data in `Feec`'s types and operators**: `d_∅`, `∏ₐ d_{a}`, `wsL2`
(`mirrorData_eq`). -/
abbrev 𝒟m : WeakSymmetryData W0 W1 W2 (Wv W0) (Wv W1) (Wv W2) :=
  ⟨TD0, TD1, vecOp BD0, vecOp BD1, wsL2 (Ω := cubeDomain 3) 0, wsL2 (Ω := cubeDomain 3) 1⟩

/-- **`mirrorData` is the data of `Feec`'s mirror scheme.** -/
theorem mirrorData_eq : mirrorData = (𝒟m : WeakSymmetryData (L2Form (cube 3) 0)
    (L2Form (cube 3) 1) (L2Form (cube 3) 2) (L2Vec (cube 3) 0) (L2Vec (cube 3) 1)
    (L2Vec (cube 3) 2)) := by
  have h0 : dMax (cube 3) 0 = TD0 := (dMax_eq _ _).trans (dPart_empty isOpen_cube 0).symm
  have h1 : dMax (cube 3) 1 = TD1 := (dMax_eq _ _).trans (dPart_empty isOpen_cube 1).symm
  change (⟨dMax (cube 3) 0, dMax (cube 3) 1, vecOp fun a => dPart {a} 0,
    vecOp fun a => dPart {a} 1, wedge (cube 3) 0, wedge (cube 3) 1⟩ : WeakSymmetryData
      (L2Form (cube 3) 0) (L2Form (cube 3) 1) (L2Form (cube 3) 2) (L2Vec (cube 3) 0)
      (L2Vec (cube 3) 1) (L2Vec (cube 3) 2)) = _
  rw [h0, h1, wedge_eq, wedge_eq]
  simp only [dPart_eq]
  rfl

/-- `∏ₐ H_{a}Λ⁰(Q)` as `Feec`'s `BU0`. -/
abbrev e0m : 𝒟m.dt0.domain ≃ₗᵢ[ℝ] BU0 := vecFamEquiv BD0
/-- `∏ₐ H_{a}Λ¹(Q)` as `Feec`'s `BU1`. -/
abbrev e1m : 𝒟m.dt1.domain ≃ₗᵢ[ℝ] BU1 := vecFamEquiv BD1

theorem norm_dt0_e0m (ψ : 𝒟m.dt0.domain) : ‖bD0 (e0m ψ)‖ = ‖𝒟m.dt0 ψ‖ :=
  (norm_bIncl1 (bD0 (e0m ψ))).symm

/-- **The mirror data are BGG data.** -/
theorem isBGG_𝒟m : 𝒟m.IsBGG :=
  ⟨fun x => ⟨TD0_mem x, mirrorBGGSegment.d1_d0 x⟩, fun x => ⟨fun a => BD0_mem a ⟨_, x.2 a⟩,
    PiLp.ext fun a => dPart_comp isOpen_cube {a} 0 ⟨_, x.2 a⟩⟩,
    fun ψ => wsL2_bIncl0_mem (e0m ψ)⟩

/-! ### The discretization -/

/-- The vectors with component `a` in `P a`. -/
def famSub {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : Fin 3 → Submodule ℝ V) : Submodule ℝ (Wv V) where
  carrier := {x | ∀ a, x a ∈ P a}
  add_mem' hx hy a := (P a).add_mem (hx a) (hy a)
  zero_mem' _ := (P _).zero_mem
  smul_mem' c _ hx a := (P a).smul_mem c (hx a)

theorem finiteDimensional_famSub {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : Fin 3 → Submodule ℝ V) [∀ a, FiniteDimensional ℝ (P a)] :
    FiniteDimensional ℝ (famSub P) := by
  let f : famSub P →ₗ[ℝ] (∀ a, P a) :=
    { toFun := fun x a => ⟨(x : Wv V) a, x.2 a⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun x y h => Subtype.ext (PiLp.ext fun a => ?_)
  exact congrArg Subtype.val (congrFun h a)

theorem norm_piFam_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : Fin 3 → V →ₗ[ℝ] V) {B : ℝ} (hB0 : 0 ≤ B) (h : ∀ a x, ‖P a x‖ ≤ B * ‖x‖) (x : Wv V) :
    ‖(WithLp.toLp 2 fun a => P a (x a) : Wv V)‖ ≤ B * ‖x‖ := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h a (x a)) 2

section FEM

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) (N : ℕ)

/-- The top-row projection in degree `i` as a bounded map. -/
def πTm (i : ℤ) : L2F ℝ (cubeDomain 3) (formIdx 3 i) →L[ℝ] L2F ℝ (cubeDomain 3) (formIdx 3 i) :=
  ((hT.proj N).π i).mkContinuous (2 * C) (hT.norm_proj_le N i)

/-- The bottom-row projection in degree `i`, componentwise, as a bounded map. -/
def πBm (i : ℤ) : Wv (L2F ℝ (cubeDomain 3) (formIdx 3 i)) →L[ℝ]
    Wv (L2F ℝ (cubeDomain 3) (formIdx 3 i)) :=
  LinearMap.mkContinuous
    { toFun := fun x => WithLp.toLp 2 fun a => ((hB a).proj N).π i (x a)
      map_add' := fun x y => PiLp.ext fun a => map_add (((hB a).proj N).π i) (x a) (y a)
      map_smul' := fun c x => PiLp.ext fun a => map_smul (((hB a).proj N).π i) c (x a) }
    (2 * C) (norm_piFam_le (fun a => ((hB a).proj N).π i) (hB 0).two_mul_nonneg
      fun a x => (hB a).norm_proj_le N i x)

/-- **The mirror scheme (6.5) as a discretization of `𝒟m`.** -/
def mirrorQ : 𝒟m.Discretization where
  V0 := (polyPartial 3 PolySeq.lowestOrder N ∅).V 0
  V1 := (polyPartial 3 PolySeq.lowestOrder N ∅).V 1
  V2 := (polyPartial 3 PolySeq.lowestOrder N ∅).V 2
  Vt0 := famSub fun a => (polyPartial 3 PolySeq.lagrangeP2 N {a}).V 0
  Vt1 := famSub fun a => (polyPartial 3 PolySeq.lagrangeP2 N {a}).V 1
  Vt2 := famSub fun a => (polyPartial 3 PolySeq.lagrangeP2 N {a}).V 2
  fdt0 := finiteDimensional_famSub _
  fdt1 := finiteDimensional_famSub _
  fdt2 := finiteDimensional_famSub _
  le0 _ hx := mem_dPart0_of_mem_V hx
  le1 _ hx := mem_dPart1_of_mem_V hx
  let0 _ hx a := mem_dPart0_of_mem_V (hx a)
  let1 _ hx a := mem_dPart1_of_mem_V (hx a)
  d0_mem x hx := dPart0_mem_V x hx
  d1_mem x hx := dPart1_mem_V x hx
  dt0_mem x hx a := dPart0_mem_V ⟨_, x.2 a⟩ (hx a)
  dt1_mem x hx a := dPart1_mem_V ⟨_, x.2 a⟩ (hx a)
  π0 := πTm hT N 0
  π1 := πTm hT N 1
  π2 := πTm hT N 2
  πt0 := πBm hB N 0
  πt1 := πBm hB N 1
  πt2 := πBm hB N 2
  π0_mem x := (hT.proj N).mem 0 x
  π1_mem x := (hT.proj N).mem 1 x
  π2_mem x := (hT.proj N).mem 2 x
  πt0_mem x a := ((hB a).proj N).mem 0 (x a)
  πt1_mem x a := ((hB a).proj N).mem 1 (x a)
  πt2_mem x a := ((hB a).proj N).mem 2 (x a)
  π0_id x hx := (hT.proj N).proj 0 x hx
  π1_id x hx := (hT.proj N).proj 1 x hx
  π2_id x hx := (hT.proj N).proj 2 x hx
  πt0_id x hx := PiLp.ext fun a => ((hB a).proj N).proj 0 (x a) (hx a)
  πt1_id x hx := PiLp.ext fun a => ((hB a).proj N).proj 1 (x a) (hx a)
  πt2_id x hx := PiLp.ext fun a => ((hB a).proj N).proj 2 (x a) (hx a)
  comm0 x := dPart0_π (hT.proj N) x
  comm1 x := dPart1_π (hT.proj N) x
  commt0 x := PiLp.ext fun a => dPart0_π ((hB a).proj N) ⟨_, x.2 a⟩
  commt1 x := PiLp.ext fun a => dPart1_π ((hB a).proj N) ⟨_, x.2 a⟩

theorem mirrorQ_isBounded : (mirrorQ hT hB N).IsBounded (2 * C) := by
  have h := hT.two_mul_nonneg
  have hb := fun i => norm_piFam_le (fun a => ((hB a).proj N).π i) (hB 0).two_mul_nonneg
    fun a x => (hB a).norm_proj_le N i x
  exact ⟨LinearMap.mkContinuous_norm_le _ h (hT.norm_proj_le N 0),
    LinearMap.mkContinuous_norm_le _ h (hT.norm_proj_le N 1),
    LinearMap.mkContinuous_norm_le _ h (hT.norm_proj_le N 2),
    LinearMap.mkContinuous_norm_le _ h (hb 0), LinearMap.mkContinuous_norm_le _ h (hb 1),
    LinearMap.mkContinuous_norm_le _ h (hb 2)⟩

/-- **(5.4) for the mirror scheme.** -/
theorem mirrorQ_compatible : (mirrorQ hT hB N).Compatible := fun ψ =>
  proj_wsL2_compatible hT hB N ψ

theorem e0m_mem {ψ : 𝒟m.dt0.domain} (hψ : (ψ : Wv W0) ∈ (mirrorQ hT hB N).Vt0) :
    e0m ψ ∈ (mirrorFEM hT hB N).Vt0h := fun a => hψ a

theorem e1m_mem {v : 𝒟m.dt1.domain} (hv : (v : Wv W1) ∈ (mirrorQ hT hB N).Vt1) :
    e1m v ∈ (mirrorFEM hT hB N).Vt1h := fun a => hv a

theorem norm_le_dt0m (ψ : 𝒟m.dt0.domain) : ‖(ψ : Wv W0)‖ ≤ ‖𝒟m.dt0 ψ‖ := by
  have hp := mirror_poinct0 (e0m ψ)
  have hn : ‖e0m ψ‖ = ‖ψ‖ := e0m.norm_map ψ
  rw [hn, norm_dt0_e0m] at hp
  have h0 : (2 * Real.pi)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]; nlinarith [Real.two_le_pi]
  exact hp.trans (by
    nlinarith [norm_nonneg (𝒟m.dt0 ψ), inv_nonneg.2 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)])

set_option maxHeartbeats 2000000 in
/-- **Consistency of the mirror scheme** at the order `h_N`, for every constant `C' ≥ A`. -/
theorem mirrorQ_isConsistent : ∃ A, 0 ≤ A ∧ ∀ C', A ≤ C' → ∀ N,
    (mirrorQ hT hB N).IsConsistent C' (Feec.Models.Cube.FEM.meshSize N) := by
  obtain ⟨Capp, hCapp0, hCapp⟩ := mirrorFEM_happ0 hT hB
  have hR := mirrorRegConst_nonneg (C := C) hT.two_mul_nonneg
  set CR := √(1 + (2 * Real.pi)⁻¹ ^ 2)
  have hCR0 : 0 ≤ CR := Real.sqrt_nonneg _
  refine ⟨√2 * Capp + CR + mirrorRegConst C * CR, by positivity, fun C' hC' N =>
    ⟨fun ψ hψ => ?_, fun v hv => ?_⟩⟩
  · have hh := (meshSize_pos N).le
    have h := hCapp N (e0m ψ) (e0m_mem hT hB N hψ)
    unfold Feec.BGG.graphSq at h
    have e : ‖mirrorBGGSegment.S0 (e0m ψ) - (mirrorFEM hT hB N).S0h (e0m ψ)‖ =
        ‖𝒟m.S0 ψ - (mirrorQ hT hB N).π1 (𝒟m.S0 ψ)‖ := rfl
    have hn : ‖e0m ψ‖ = ‖ψ‖ := e0m.norm_map ψ
    have hd : ‖mirrorBGGSegment.dt0 (e0m ψ)‖ = ‖𝒟m.dt0 ψ‖ := norm_dt0_e0m ψ
    rw [e, hn, hd] at h
    have hg : ‖ψ‖ ^ 2 + ‖𝒟m.dt0 ψ‖ ^ 2 ≤ 2 * ‖𝒟m.dt0 ψ‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (norm_le_dt0m ψ) 2
      have e' : ‖(ψ : Wv W0)‖ = ‖ψ‖ := rfl
      rw [e'] at this; linarith
    have h2 : ‖𝒟m.S0 ψ - (mirrorQ hT hB N).π1 (𝒟m.S0 ψ)‖ ^ 2 ≤
        (√2 * Capp * Feec.Models.Cube.FEM.meshSize N * ‖𝒟m.dt0 ψ‖) ^ 2 := by
      calc _ ≤ _ := h
        _ ≤ (Capp * Feec.Models.Cube.FEM.meshSize N) ^ 2 * (2 * ‖𝒟m.dt0 ψ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hg (sq_nonneg _)
        _ = _ := by
          have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          linear_combination (-(Capp * Feec.Models.Cube.FEM.meshSize N * ‖𝒟m.dt0 ψ‖) ^ 2) * h2
    have h3 := le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h2
    refine h3.trans ?_
    have : √2 * Capp ≤ C' := le_trans (by linarith [mul_nonneg hR hCR0]) hC'
    gcongr
  · have hh := (meshSize_pos N).le
    have Rg := mirrorFEMReg hT hB N (le_refl (mirrorRegConst C))
    obtain ⟨y, hy1, hy2⟩ := Rg.exists_potential (e1m v) (e1m_mem hT hB N hv)
    have hy : ‖y‖ ≤ CR * ‖𝒟m.dt1 v‖ := hy2
    have hC1 : mirrorRegConst C * CR ≤ C' :=
      le_trans (by linarith [mul_nonneg (Real.sqrt_nonneg 2) hCapp0]) hC'
    refine ⟨e1m.symm (Rg.R y), hy1, ?_, ?_, ?_⟩
    · have hn : ‖((e1m.symm (Rg.R y) : 𝒟m.dt1.domain) : Wv W1)‖ = ‖Rg.R y‖ :=
        e1m.symm.norm_map _
      rw [hn]
      refine (Rg.norm_R_le y).trans ?_
      rw [one_mul]
      refine hy.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      linarith [mul_nonneg hR hCR0, mul_nonneg (Real.sqrt_nonneg 2) hCapp0]
    · have hn : ‖((e1m.symm (Rg.R y) : 𝒟m.dt1.domain) : Wv W1) -
          (mirrorQ hT hB N).πt1 (e1m.symm (Rg.R y))‖ =
          ‖Rg.R y - (mirrorFEM hT hB N).Pt1 (Rg.R y)‖ := by
        rw [← norm_bIncl1, map_sub]; rfl
      rw [hn]
      refine (Rg.approx_Pt1 y).trans ?_
      calc mirrorRegConst C * Feec.Models.Cube.FEM.meshSize N * ‖y‖
          ≤ mirrorRegConst C * Feec.Models.Cube.FEM.meshSize N * (CR * ‖𝒟m.dt1 v‖) := by
            gcongr
        _ = mirrorRegConst C * CR * Feec.Models.Cube.FEM.meshSize N * ‖𝒟m.dt1 v‖ := by ring
        _ ≤ _ := by gcongr
    · have e : 𝒟m.S1 (e1m.symm (Rg.R y)) - (mirrorQ hT hB N).π2 (𝒟m.S1 (e1m.symm (Rg.R y))) =
          (mirrorBGGSegment.S1 - (mirrorFEM hT hB N).S1h) (Rg.R y) := rfl
      rw [e]
      refine (Rg.approx_S1 y).trans ?_
      calc mirrorRegConst C * Feec.Models.Cube.FEM.meshSize N * ‖y‖
          ≤ mirrorRegConst C * Feec.Models.Cube.FEM.meshSize N * (CR * ‖𝒟m.dt1 v‖) := by
            gcongr
        _ = mirrorRegConst C * CR * Feec.Models.Cube.FEM.meshSize N * ‖𝒟m.dt1 v‖ := by ring
        _ ≤ _ := by gcongr

end FEM

namespace WeakSymmetryData.Discretization

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] {D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2} {Q : D.Discretization}

theorem IsBounded.mono {C C' : ℝ} (h : Q.IsBounded C) (hC : C ≤ C') : Q.IsBounded C' :=
  ⟨h.1.trans hC, h.2.1.trans hC, h.2.2.1.trans hC, h.2.2.2.1.trans hC, h.2.2.2.2.1.trans hC,
    h.2.2.2.2.2.trans hC⟩

end WeakSymmetryData.Discretization

end FEEC
