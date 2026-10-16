module

public import Feec.Repair.C419Cube
public import Feec.Repair.C417Pi

/-!
# Prop 4.19 with mirror boundary conditions on every open cube

`Feec.Repair.C419Cube` proves the repaired Prop 4.19 on the box `Q = (0, ½)³`. This file carries
it along `T x = 2s x + b`, which maps `Q` onto `openCube b s = ∏ᵢ (bᵢ, bᵢ + s)`
(`Feec.BoxIdent.mem_Qr_iff_openCube`), as `Feec.Repair.C417Pi` does for Prop 4.17.

The complex (4.16) has a second-order `d0` (the Hessian) and a first-order `d1` (the curl), so the
chain rule factors differ: `Hess (u ∘ T) = (2s)² (Hess u) ∘ T` and `curl (E ∘ T) = 2s (curl E) ∘ T`.
The complex on the cube is therefore the compression, by the pull-back `E ↦ E ∘ T` (`P = id`), of
`mirrorSymCxQ` with `d0` multiplied by `(2s)⁻²` and `d1` by `(2s)⁻¹` (`scaleComplex2`). Its
operators are, in the coordinates of the cube, the Hessian and the curl with the mirror boundary
conditions `∂_n u = 0`, `S_{nτ} = 0`. They are defined by conjugation; their identification with
the weak Hessian and the weak curl on the cube (proved on `Q`: `mirrorSymCxQ_d0_weakHess`,
`mirrorSymCxQ_d1_eq`) is not carried over here.

* `scaleComplex2`: `d0 ↦ λ d0`, `d1 ↦ μ d1` (`λ, μ ≠ 0`). `D(L)` and `ker d0*` are unchanged, and
  the hypotheses of the abstract Prop 4.17 are invariant (`prop_4_17_hyps_scale2`).
* `comprPullR`, `comprPullS`, `comprPullT`: the pull-back of `L²`, `L²(S)`, `L²(T)` as
  compression data.
* **`mirrorSymCxCube_prop_4_19_exists`**, `mirrorSymCxCube_projection_hyp`,
  `mirrorSymCxCube_Kmax_eq`, `mirrorSymCxCube_exists_nonstationary`; the constraint spaces are
  TSD on the cube (`TSDSmCube_le_TSDS`, `TSDTmCube_le_TSDT`).

## References

* [QuennevilleBelair2015], §4.11 (Prop 4.19)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open Set LinearPMap

namespace Feec.Repair.C417

open Feec.Torus Feec.Constraints Feec.HilbertComplex2 Feec.BoxIdent Feec.Box

/-! ## Scaling the two differentials independently -/

section Scale2

variable {W0 W1 W2 : Type*}
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]

/-- **A Hilbert complex with `d0` multiplied by `λ ≠ 0` and `d1` by `μ ≠ 0`.** -/
def scaleComplex2 (H : HilbertComplex2 W0 W1 W2) (l m : ℝ) (hl : l ≠ 0) (hm : m ≠ 0) :
    HilbertComplex2 W0 W1 W2 where
  d0 := l • H.d0
  d1 := m • H.d1
  dense0 := H.dense0
  dense1 := H.dense1
  closed0 := isClosed_smul H.closed0 hl
  closed1 := isClosed_smul H.closed1 hm
  map_mem x := by
    change l • H.d0 ⟨x, x.2⟩ ∈ H.d1.domain
    exact H.d1.domain.smul_mem _ (H.map_mem _)
  comp_zero x := by
    rw [LinearPMap.smul_apply]
    have e : ((⟨(l • H.d0) x, by
        change l • H.d0 ⟨x, x.2⟩ ∈ H.d1.domain
        exact H.d1.domain.smul_mem _ (H.map_mem _)⟩ : H.d1.domain)) =
        l • (⟨H.d0 ⟨x, x.2⟩, H.map_mem _⟩ : H.d1.domain) := rfl
    rw [e, LinearPMap.map_smul, H.comp_zero, smul_zero, smul_zero]

variable {H : HilbertComplex2 W0 W1 W2} {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0)

theorem mem_domL_scale2_iff (x : Tot W0 W1 W2) :
    x ∈ (scaleComplex2 H l m hl hm).domL ↔ x ∈ H.domL := by
  rw [Constraints.mem_domL, Constraints.mem_domL]
  change (tot W0 W1 W2 x).1 ∈ H.d0.domain ∧ ((tot W0 W1 W2 x).2.1 ∈ H.d1.domain ∧
      (tot W0 W1 W2 x).2.1 ∈ (l • H.d0)†.domain) ∧ (tot W0 W1 W2 x).2.2 ∈ (m • H.d1)†.domain ↔
    (tot W0 W1 W2 x).1 ∈ H.d0.domain ∧ ((tot W0 W1 W2 x).2.1 ∈ H.d1.domain ∧
      (tot W0 W1 W2 x).2.1 ∈ H.d0†.domain) ∧ (tot W0 W1 W2 x).2.2 ∈ H.d1†.domain
  rw [mem_adjoint_smul_iff H.dense0 hl, mem_adjoint_smul_iff H.dense1 hm]

theorem ker_adj0_scale2 : (scaleComplex2 H l m hl hm).d0†.ker = H.d0†.ker := by
  ext u
  constructor
  · intro hu
    obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hu
    have hy' : (y : W1) ∈ H.d0†.domain := (mem_adjoint_smul_iff H.dense0 hl).1 y.2
    refine LinearPMap.mem_ker_iff.2 ⟨⟨y, hy'⟩, hy, ?_⟩
    have e := adjoint_smul_apply H.dense0 hl y
    change (l • H.d0)† y = 0 at hy0
    rw [hy0] at e
    exact (smul_eq_zero.1 e.symm).resolve_left hl
  · intro hu
    obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hu
    have hy' : (y : W1) ∈ (l • H.d0)†.domain := (mem_adjoint_smul_iff H.dense0 hl).2 y.2
    refine LinearPMap.mem_ker_iff.2 ⟨⟨y, hy'⟩, hy, ?_⟩
    change (l • H.d0)† ⟨y, hy'⟩ = 0
    rw [adjoint_smul_apply H.dense0 hl]
    rw [show (⟨(y : W1), (mem_adjoint_smul_iff H.dense0 hl).1 hy'⟩ : H.d0†.domain) = y from rfl,
      hy0, smul_zero]

/-- The magnetic component of the scaled Hodge wave operator: `(L_{λ,μ} x)_B = μ (L x)_B`. -/
theorem tot_waveOp_scale2_B (x : Tot W0 W1 W2) (hx : x ∈ (scaleComplex2 H l m hl hm).domL) :
    (tot W0 W1 W2 ((scaleComplex2 H l m hl hm).waveOp ⟨x, hx⟩)).2.2 =
      m • (tot W0 W1 W2 (H.waveOp ⟨x, (mem_domL_scale2_iff hl hm x).1 hx⟩)).2.2 := by
  rw [Constraints.tot_waveOp, Constraints.tot_waveOp]
  change -((m • H.d1) ((scaleComplex2 H l m hl hm).prV1 ⟨x, hx⟩)) =
    m • -(H.d1 (H.prV1 ⟨x, (mem_domL_scale2_iff hl hm x).1 hx⟩))
  rw [smul_neg]
  rfl

/-- **The hypotheses of the abstract Prop 4.17 are invariant under scaling the differentials.** -/
theorem prop_4_17_hyps_scale2 (S1 : Submodule ℝ W1) (S2 : Submodule ℝ W2)
    [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection] (hS1 : S1 ≤ H.d0†.ker)
    (hPD : ∀ x ∈ H.domL, projKc W0 S1 S2 x ∈ H.domL)
    (hd1 : ∀ u : H.d1.domain, (u : W1) ∈ S1 → H.d1 u ∈ S2)
    (hd1s : ∀ ρ : H.d1†.domain, (ρ : W2) ∈ S2 → H.d1† ρ ∈ S1) :
    S1 ≤ (scaleComplex2 H l m hl hm).d0†.ker ∧
    (∀ x ∈ (scaleComplex2 H l m hl hm).domL,
      projKc W0 S1 S2 x ∈ (scaleComplex2 H l m hl hm).domL) ∧
    (∀ u : (scaleComplex2 H l m hl hm).d1.domain, (u : W1) ∈ S1 →
      (scaleComplex2 H l m hl hm).d1 u ∈ S2) ∧
    (∀ ρ : (scaleComplex2 H l m hl hm).d1†.domain, (ρ : W2) ∈ S2 →
      (scaleComplex2 H l m hl hm).d1† ρ ∈ S1) := by
  refine ⟨fun u hu => by rw [ker_adj0_scale2 (H := H) hl hm]; exact hS1 hu, fun x hx => ?_,
    fun u hu => ?_, fun ρ hρ => ?_⟩
  · rw [mem_domL_scale2_iff] at hx ⊢; exact hPD x hx
  · change m • H.d1 ⟨u, u.2⟩ ∈ S2
    exact S2.smul_mem _ (hd1 ⟨u, u.2⟩ hu)
  · have e : (scaleComplex2 H l m hl hm).d1† ρ =
        m • H.d1† ⟨ρ, (mem_adjoint_smul_iff H.dense1 hm).1 ρ.2⟩ :=
      adjoint_smul_apply H.dense1 hm ρ
    rw [e]
    exact S1.smul_mem _ (hd1s _ hρ)

end Scale2

/-! ## Pull-back of `L²`, `L²(S)`, `L²(T)` as compression data -/

section PullSym

open BoundedDomain (R3)

variable {a : ℝ} {b : R3} {Ω Ω' : Set R3} (ha : a ≠ 0) (hT : ∀ x, x ∈ Ω ↔ a • x + b ∈ Ω')

/-- Pull-back of scalar fields along `x ↦ a x + b` as compression data (`P = id`). -/
def comprPullR : Compr (|a ^ 3|⁻¹) (BoundedDomain.L2 Ω') (BoundedDomain.L2 Ω) where
  J := pullL ha hT
  R := pullL (inv_ne_zero ha) (hT_inv ha hT)
  P := ContinuousLinearMap.id ℝ _
  inner_J := inner_pullFun ha hT
  RJ := inv_pull ha hT
  JRP z := pull_inv ha hT z
  PJ _ := rfl
  P_sa _ _ := rfl

theorem pullM_mem_symL2 {A : BoundedDomain.L2M Ω'} (hA : A ∈ BoundedSym.symL2 Ω') :
    pullM ha hT A ∈ BoundedSym.symL2 Ω := fun i j => by
  simp only [pullM_apply]; rw [hA i j]

theorem pullM_mem_trL2 {A : BoundedDomain.L2M Ω'} (hA : A ∈ BoundedSym.trL2 Ω') :
    pullM ha hT A ∈ BoundedSym.trL2 Ω := by
  change ∑ i, pullM ha hT A (i, i) = 0
  simp only [pullM_apply]
  have := map_sum (pullL ha hT) (fun i => A (i, i)) Finset.univ
  simp only [pullL_apply] at this
  rw [← this]
  change pullL ha hT (∑ i, A (i, i)) = 0
  rw [show ∑ i, A (i, i) = 0 from hA]; exact map_zero (pullL ha hT)

/-- The pull-back on symmetric fields. -/
def pullS : BoundedSym.L2S Ω' →L[ℝ] BoundedSym.L2S Ω :=
  (pullM ha hT ∘L (BoundedSym.symL2 Ω').subtypeL).codRestrict (BoundedSym.symL2 Ω)
    fun A => pullM_mem_symL2 ha hT A.2

/-- The pull-back on trace-free fields. -/
def pullT : BoundedSym.L2T Ω' →L[ℝ] BoundedSym.L2T Ω :=
  (pullM ha hT ∘L (BoundedSym.trL2 Ω').subtypeL).codRestrict (BoundedSym.trL2 Ω)
    fun A => pullM_mem_trL2 ha hT A.2

@[simp] theorem coe_pullS (A : BoundedSym.L2S Ω') :
    ((pullS ha hT A : BoundedSym.L2S Ω) : BoundedDomain.L2M Ω) = pullM ha hT A := rfl

@[simp] theorem coe_pullT (A : BoundedSym.L2T Ω') :
    ((pullT ha hT A : BoundedSym.L2T Ω) : BoundedDomain.L2M Ω) = pullM ha hT A := rfl

/-- Pull-back of symmetric fields as compression data. -/
def comprPullS : Compr (|a ^ 3|⁻¹) (BoundedSym.L2S Ω') (BoundedSym.L2S Ω) where
  J := pullS ha hT
  R := pullS (inv_ne_zero ha) (hT_inv ha hT)
  P := ContinuousLinearMap.id ℝ _
  inner_J x y := by
    rw [Submodule.coe_inner, Submodule.coe_inner, coe_pullS, coe_pullS, inner_pullM]
  RJ x := Subtype.ext (inv_pullM ha hT (x : BoundedDomain.L2M Ω'))
  JRP z := Subtype.ext (pullM_inv ha hT (z : BoundedDomain.L2M Ω))
  PJ _ := rfl
  P_sa _ _ := rfl

/-- Pull-back of trace-free fields as compression data. -/
def comprPullT : Compr (|a ^ 3|⁻¹) (BoundedSym.L2T Ω') (BoundedSym.L2T Ω) where
  J := pullT ha hT
  R := pullT (inv_ne_zero ha) (hT_inv ha hT)
  P := ContinuousLinearMap.id ℝ _
  inner_J x y := by
    rw [Submodule.coe_inner, Submodule.coe_inner, coe_pullT, coe_pullT, inner_pullM]
  RJ x := Subtype.ext (inv_pullM ha hT (x : BoundedDomain.L2M Ω'))
  JRP z := Subtype.ext (pullM_inv ha hT (z : BoundedDomain.L2M Ω))
  PJ _ := rfl
  P_sa _ _ := rfl

end PullSym

/-! ## The mirror complex (4.16) on every open cube -/

section MirrorSymCube

open BoundedDomain (R3)
open TorusSym (embL2 symSub trSub)

variable {b : R3} {s : ℝ} (hs : 0 < s)

theorem two_s_sq_inv_ne (hs : 0 < s) : ((2 * s) ^ 2)⁻¹ ≠ 0 := by positivity

/-- The hypotheses of the abstract Prop 4.17 for `mirrorSymCxQ` and `TSDSm`, `TSDTm`. -/
theorem mirrorSymCxQ_hyps :
    TSDSm ≤ mirrorSymCxQ.d0†.ker ∧
    (∀ x ∈ mirrorSymCxQ.domL, projKc RQ TSDSm TSDTm x ∈ mirrorSymCxQ.domL) ∧
    (∀ u : mirrorSymCxQ.d1.domain, (u : SQ) ∈ TSDSm → mirrorSymCxQ.d1 u ∈ TSDTm) ∧
    (∀ ρ : mirrorSymCxQ.d1†.domain, (ρ : TQ) ∈ TSDTm → mirrorSymCxQ.d1† ρ ∈ TSDSm) :=
  prop_4_17_hyps_compr (h0 := comprComm_hess) (h1 := comprComm_curlS) TorusSym.L2TSDS
    TorusSym.L2TSDT eight_pos TorusSym.L2TSDS_le_ker TorusSym.projKc_mem_domL
    TorusSym.curlST_mem_L2TSDT TorusSym.adjoint_curlST_mem_L2TSDS starProjection_comprS
    starProjection_comprT

/-- `mirrorSymCxQ` with `d0` scaled by `(2s)⁻²` and `d1` by `(2s)⁻¹`. -/
abbrev symScaled (s : ℝ) (hs : 0 < s) : HilbertComplex2 RQ SQ TQ :=
  scaleComplex2 mirrorSymCxQ ((2 * s) ^ 2)⁻¹ (2 * s)⁻¹ (two_s_sq_inv_ne hs)
    (inv_ne_zero (two_s_ne hs))

/-- **The complex (4.16) `H²_N → H_{nτ}(curl; S) → L²(T)` with tensorial mirror boundary
conditions on the open cube `∏ᵢ (bᵢ, bᵢ + s)`**: the compression of `mirrorSymCxQ`, with the
chain-rule factors `(2s)⁻²` on the Hessian and `(2s)⁻¹` on the curl, by `E ↦ E ∘ T`,
`T x = 2s x + b`. -/
def mirrorSymCxCube (b : R3) (s : ℝ) (hs : 0 < s) :
    HilbertComplex2 (BoundedDomain.L2 (openCube b s)) (BoundedSym.L2S (openCube b s))
      (BoundedSym.L2T (openCube b s)) :=
  comprComplex (symScaled s hs)
    (comprPullR (two_s_ne hs) (mem_Qr_iff_openCube hs b))
    (comprPullS (two_s_ne hs) (mem_Qr_iff_openCube hs b))
    (comprPullT (two_s_ne hs) (mem_Qr_iff_openCube hs b))
    (comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl))
    (comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl))

/-- The constraint space in `L²(cube; S)`: `E ∘ T ∈ TSDSm`. -/
abbrev TSDSmCube (b : R3) (s : ℝ) (hs : 0 < s) :
    Submodule ℝ (BoundedSym.L2S (openCube b s)) :=
  TSDSm.comap ((comprPullS (two_s_ne hs) (mem_Qr_iff_openCube hs b)).J :
    BoundedSym.L2S (openCube b s) →ₗ[ℝ] SQ)

/-- The constraint space in `L²(cube; T)`: `B ∘ T ∈ TSDTm`. -/
abbrev TSDTmCube (b : R3) (s : ℝ) (hs : 0 < s) :
    Submodule ℝ (BoundedSym.L2T (openCube b s)) :=
  TSDTm.comap ((comprPullT (two_s_ne hs) (mem_Qr_iff_openCube hs b)).J :
    BoundedSym.L2T (openCube b s) →ₗ[ℝ] TQ)

theorem symScaled_hyps :
    TSDSm ≤ (symScaled s hs).d0†.ker ∧
    (∀ x ∈ (symScaled s hs).domL, projKc RQ TSDSm TSDTm x ∈ (symScaled s hs).domL) ∧
    (∀ u : (symScaled s hs).d1.domain, (u : SQ) ∈ TSDSm → (symScaled s hs).d1 u ∈ TSDTm) ∧
    (∀ ρ : (symScaled s hs).d1†.domain, (ρ : TQ) ∈ TSDTm → (symScaled s hs).d1† ρ ∈ TSDSm) :=
  prop_4_17_hyps_scale2 (two_s_sq_inv_ne hs) (inv_ne_zero (two_s_ne hs)) TSDSm TSDTm
    mirrorSymCxQ_hyps.1 mirrorSymCxQ_hyps.2.1 mirrorSymCxQ_hyps.2.2.1 mirrorSymCxQ_hyps.2.2.2

/-- **The projection hypothesis of Prop 4.19 holds on every open cube with mirror conditions.** -/
theorem mirrorSymCxCube_projection_hyp : ∀ x ∈ (mirrorSymCxCube b s hs).domL,
    projKc (BoundedDomain.L2 (openCube b s)) (TSDSmCube b s hs) (TSDTmCube b s hs) x ∈
      (mirrorSymCxCube b s hs).domL :=
  (prop_4_17_hyps_compr (h0 := comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl))
    (h1 := comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl)) TSDSm TSDTm
    (pos_c (two_s_ne hs)) (symScaled_hyps hs).1 (symScaled_hyps hs).2.1
    (symScaled_hyps hs).2.2.1 (symScaled_hyps hs).2.2.2 (fun _ => rfl) (fun _ => rfl)).2.1

/-- **Thesis Prop 4.19, repaired on every open cube `∏ᵢ (bᵢ, bᵢ + s)` with tensorial mirror
boundary conditions** (`∂_n u = 0`, `S_{nτ} = 0`). For data `(0, E₀, B₀) ∈ D(L)` with
`E₀ ∈ TSDSmCube`, `B₀ ∈ TSDTmCube` (TSD on the cube, with the wall conditions in the reflection
sense), the Hodge wave (4.18) has a strong solution on `[0, T]`, unique among strong solutions,
staying in `{0} × TSDSmCube × TSDTmCube` and solving the reduced system.

See [QuennevilleBelair2015, §4.11, Prop 4.19]. -/
theorem mirrorSymCxCube_prop_4_19_exists (T : ℝ) {E₀ : BoundedSym.L2S (openCube b s)}
    {B₀ : BoundedSym.L2T (openCube b s)}
    (hE₀ : E₀ ∈ TSDSmCube b s hs) (hB₀ : B₀ ∈ TSDTmCube b s hs)
    (hD : ini (BoundedDomain.L2 (openCube b s)) E₀ B₀ ∈ (mirrorSymCxCube b s hs).domL) :
    ∃ U : ℝ → Tot (BoundedDomain.L2 (openCube b s)) (BoundedSym.L2S (openCube b s))
        (BoundedSym.L2T (openCube b s)),
      IsStrongSolution (-(mirrorSymCxCube b s hs).waveOp) T
        (ini (BoundedDomain.L2 (openCube b s)) E₀ B₀) 0 U ∧
      (∀ U', IsStrongSolution (-(mirrorSymCxCube b s hs).waveOp) T
        (ini (BoundedDomain.L2 (openCube b s)) E₀ B₀) 0 U' → EqOn U' U (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, U t ∈ Kc (BoundedDomain.L2 (openCube b s)) (TSDSmCube b s hs)
        (TSDTmCube b s hs)) ∧
      IsReducedSolution (mirrorSymCxCube b s hs) T E₀ B₀ (fun t => (tot _ _ _ (U t)).2.1)
        (fun t => (tot _ _ _ (U t)).2.2) :=
  prop_4_17_compr_exists (h0 := comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl))
    (h1 := comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl)) TSDSm TSDTm
    (pos_c (two_s_ne hs)) (symScaled_hyps hs).1 (symScaled_hyps hs).2.1
    (symScaled_hyps hs).2.2.1 (symScaled_hyps hs).2.2.2 (fun _ => rfl) (fun _ => rfl)
    T hE₀ hB₀ hD

/-- **`K* = K` on every open cube for (4.16) with mirror conditions.** -/
theorem mirrorSymCxCube_Kmax_eq (G : UnitaryGroupGenerator (-(mirrorSymCxCube b s hs).waveOp)) :
    Kmax G (Kc (BoundedDomain.L2 (openCube b s)) (TSDSmCube b s hs) (TSDTmCube b s hs)) =
      Kc (BoundedDomain.L2 (openCube b s)) (TSDSmCube b s hs) (TSDTmCube b s hs) :=
  Kmax_compr_eq (h0 := comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl))
    (h1 := comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl)) TSDSm TSDTm
    (pos_c (two_s_ne hs)) (symScaled_hyps hs).1 (symScaled_hyps hs).2.1
    (symScaled_hyps hs).2.2.1 (symScaled_hyps hs).2.2.2 (fun _ => rfl) (fun _ => rfl) G

/-- The constraint spaces on the cube consist of TSD fields. -/
theorem TSDSmCube_le_TSDS {E : BoundedSym.L2S (openCube b s)} (hE : E ∈ TSDSmCube b s hs) :
    E ∈ BoundedSym.TSDS (openCube b s) := by
  have ha : 2 * s ≠ 0 := two_s_ne hs
  have hE' := TSDSm_le_TSDS hE
  rw [BoundedSym.mem_TSDS] at hE' ⊢
  have h := pullM_mem_TSD (inv_ne_zero ha) (hT_inv ha (mem_Qr_iff_openCube hs b))
    (isOpen_openCube b s) (isBounded_openCube b s) isOpen_Qr isBounded_Qr hE'
  change pullM _ _ (pullM _ _ (E : BoundedDomain.L2M (openCube b s))) ∈ _ at h
  rwa [inv_pullM] at h

theorem TSDTmCube_le_TSDT {B : BoundedSym.L2T (openCube b s)} (hB : B ∈ TSDTmCube b s hs) :
    B ∈ BoundedSym.TSDT (openCube b s) := by
  have ha : 2 * s ≠ 0 := two_s_ne hs
  have hB' := TSDTm_le_TSDT hB
  rw [BoundedSym.mem_TSDT] at hB' ⊢
  have h := pullM_mem_TSD (inv_ne_zero ha) (hT_inv ha (mem_Qr_iff_openCube hs b))
    (isOpen_openCube b s) (isBounded_openCube b s) isOpen_Qr isBounded_Qr hB'
  change pullM _ _ (pullM _ _ (B : BoundedDomain.L2M (openCube b s))) ∈ _ at h
  rwa [inv_pullM] at h

/-! ### A non-stationary datum on the cube -/

/-- The magnetic component of `L (0, E₀, 0)` on `Q` is non-zero (`curl E₀ ≠ 0`). -/
theorem cosStateS_waveOp_B_ne :
    (tot RQ SQ TQ (mirrorSymCxQ.waveOp ⟨cosStateS, cosStateS_mem_domL⟩)).2.2 ≠ 0 := by
  intro h0
  have hi := totJ_waveOp (h0 := comprComm_hess) (h1 := comprComm_curlS) eight_pos cosStateS
    cosStateS_mem_domL
  change totJ _ _ _ (mirrorSymCxQ.waveOp ⟨cosStateS, cosStateS_mem_domL⟩) = _ at hi
  have hB := congrArg (fun y => (tot TorusSym.L2R TorusSym.L2S TorusSym.L2T y).2.2) hi
  simp only [tot_totJ, h0, _root_.map_zero] at hB
  have h3 := congrArg (fun y => embL2 trSub y k0) hB
  simp only [Constraints.tot_waveOp, _root_.map_zero, lp.coeFn_zero, Pi.zero_apply] at h3
  rw [LinearIsometry.map_neg, lp.coeFn_neg, Pi.neg_apply, eq_comm, neg_eq_zero] at h3
  apply curlSym_cosE_ne
  rw [← h3]
  have e : TorusSym.symComplex.d1 (TorusSym.symComplex.prV1 ⟨totJ comprR comprS comprT cosStateS,
      (mem_domL_compr_iff (h0 := comprComm_hess) (h1 := comprComm_curlS) eight_pos _).1
        cosStateS_mem_domL⟩) = TorusSym.curlST ⟨comprS.J cosSQ, comprS_cosSQ_mem_HcurlS⟩ :=
    lpmap_congr' _ _ _ (by simp [tot_totJ_cosStateS])
  rw [e, ← TorusSym.curlT_embL2]
  change curlSym (freq k0) (cosE k0) = curlSym (freq k0) (embL2 symSub (comprS.J cosSQ) k0)
  rw [embL2_comprS_cosSQ]

/-- The datum `(0, E₀ ∘ T⁻¹, 0)` on the cube, `E₀ = (2 cos(2π x₃) diag(1, -1, 0))|_Q`. -/
def cosStateSCube (b : R3) (s : ℝ) (hs : 0 < s) :
    Tot (BoundedDomain.L2 (openCube b s)) (BoundedSym.L2S (openCube b s))
      (BoundedSym.L2T (openCube b s)) :=
  ini _ ((comprPullS (two_s_ne hs) (mem_Qr_iff_openCube hs b)).R cosSQ) 0

theorem totJ_cosStateSCube :
    totJ (comprPullR (two_s_ne hs) (mem_Qr_iff_openCube hs b))
      (comprPullS (two_s_ne hs) (mem_Qr_iff_openCube hs b))
      (comprPullT (two_s_ne hs) (mem_Qr_iff_openCube hs b)) (cosStateSCube b s hs) =
      cosStateS := by
  apply (tot RQ SQ TQ).injective
  rw [tot_totJ, cosStateSCube, tot_ini, cosStateS, tot_ini]
  simp only [_root_.map_zero]
  exact Prod.ext rfl (Prod.ext ((comprPullS (two_s_ne hs) (mem_Qr_iff_openCube hs b)).JRP cosSQ)
    rfl)

theorem cosStateSCube_mem_domL : cosStateSCube b s hs ∈ (mirrorSymCxCube b s hs).domL := by
  rw [mirrorSymCxCube, mem_domL_compr_iff (pos_c (two_s_ne hs)), totJ_cosStateSCube,
    mem_domL_scale2_iff]
  exact cosStateS_mem_domL

theorem cosStateSCube_mem_Kc : cosStateSCube b s hs ∈ Kc (BoundedDomain.L2 (openCube b s))
    (TSDSmCube b s hs) (TSDTmCube b s hs) := by
  rw [mem_Kc, cosStateSCube, tot_ini]
  refine ⟨rfl, ?_, Submodule.zero_mem _⟩
  change (comprPullS (two_s_ne hs) (mem_Qr_iff_openCube hs b)).J
    ((comprPullS (two_s_ne hs) (mem_Qr_iff_openCube hs b)).R cosSQ) ∈ TSDSm
  have e : (comprPullS (two_s_ne hs) (mem_Qr_iff_openCube hs b)).J
      ((comprPullS (two_s_ne hs) (mem_Qr_iff_openCube hs b)).R cosSQ) = cosSQ :=
    (comprPullS (two_s_ne hs) (mem_Qr_iff_openCube hs b)).JRP cosSQ
  rw [e]
  exact cosSQ_mem_TSDSm

/-- **Non-stationary TSD data propagate for (4.18) on every open cube with mirror conditions.** -/
theorem mirrorSymCxCube_exists_nonstationary
    (G : UnitaryGroupGenerator (-(mirrorSymCxCube b s hs).waveOp)) :
    cosStateSCube b s hs ∈ (mirrorSymCxCube b s hs).domL ∧
      cosStateSCube b s hs ∈ Kmax G (Kc (BoundedDomain.L2 (openCube b s)) (TSDSmCube b s hs)
        (TSDTmCube b s hs)) ∧ ∃ t, G.S t (cosStateSCube b s hs) ≠ cosStateSCube b s hs := by
  refine ⟨cosStateSCube_mem_domL hs,
    by rw [mirrorSymCxCube_Kmax_eq]; exact cosStateSCube_mem_Kc hs, ?_⟩
  by_contra hst
  push Not at hst
  have hdom : cosStateSCube b s hs ∈ (-(mirrorSymCxCube b s hs).waveOp).domain :=
    cosStateSCube_mem_domL hs
  have hd := G.hasDerivAt_zero ⟨_, hdom⟩
  have hd2 : HasDerivAt (fun t => G.S t (cosStateSCube b s hs)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (cosStateSCube b s hs)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => hst t)
  have h0 := hd.unique hd2
  rw [LinearPMap.neg_apply, neg_eq_zero] at h0
  have hi := totJ_waveOp (h0 := comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl))
    (h1 := comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl)) (pos_c (two_s_ne hs))
    (cosStateSCube b s hs) (cosStateSCube_mem_domL hs)
  change totJ _ _ _ ((mirrorSymCxCube b s hs).waveOp ⟨_, cosStateSCube_mem_domL hs⟩) = _ at hi
  rw [h0, _root_.map_zero] at hi
  have hB := congrArg (fun y => (tot RQ SQ TQ y).2.2) hi
  simp only [_root_.map_zero, Prod.snd_zero] at hB
  rw [tot_waveOp_scale2_B] at hB
  have h1 := (smul_eq_zero.1 hB.symm).resolve_left (inv_ne_zero (two_s_ne hs))
  apply cosStateS_waveOp_B_ne
  rw [← h1]
  exact congrArg (fun y => (tot RQ SQ TQ y).2.2)
    (lpmap_congr' _ _ _ (totJ_cosStateSCube hs).symm)

end MirrorSymCube

end Feec.Repair.C417
