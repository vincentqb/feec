module

public import Feec.Models.Cube.Mirror
public import Feec.Legacy.MirrorCube.SymPi

/-!
# The strong-symmetry complex (4.16) on the cube with mirror boundary conditions

The complex `H²(R) --grad grad--> H(curl, S) --curl--> L²(T)` of Thesis (4.16) on the torus
(`Feec.Models.Cube.torusSym`) carries the mirror action of `(ℤ/2)³` (`u` even, `S` even, `T` odd:
`S(R_i x) = D_i S(x) D_i`, `T(R_i x) = -D_i T(x) D_i`), the TSD constraint
`{0} × L²(TSD) × L²(TSD)` reduces it (`reducingSubcomplex_tsd_torusSym`) and is invariant under
the action, so it descends to the fixed complex, to the complex of genuine fields on
`Q = (0, ½)³` (`∂_n u = 0`, `S_{nτ} = 0`; `MirrorSym.complexQ`, embedded by the mirror
extensions) and to every open cube (`MirrorSym.complexCube`, with the chain-rule factors `(2s)⁻²`
on the Hessian and `(2s)⁻¹` on the curl). This is Thesis Prop 4.19 with mirror boundary
conditions, by the same general mechanism as `Feec.Models.Cube.Mirror`.

## Main results

* `reducingSubcomplex_tsd_torusSym`.
* **`MirrorSym.reducingSubcomplex`**, `MirrorSym.propagates`, `MirrorSym.existsUnique_mem`,
  `MirrorSym.invariantCore_eq`.
* **`MirrorSym.reducingSubcomplexQ`**, `MirrorSym.propagatesQ`, `MirrorSym.existsUnique_memQ`,
  `MirrorSym.invariantCore_eqQ`, `MirrorSym.exists_nonstationaryQ`.
* **`MirrorSym.reducingSubcomplexCube`**, `MirrorSym.propagatesCube`,
  `MirrorSym.existsUnique_memCube`, `MirrorSym.invariantCore_eqCube`,
  `MirrorSym.exists_nonstationaryCube`.

## References

* [QuennevilleBelair2015], §4.11 (Prop 4.19, (4.16))
* [ArnoldHu2021] (the complex (4.16))
-/

open Feec.Legacy

open scoped RealInnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

universe u

namespace Feec.Models.Cube

open Feec.Legacy.HilbertComplex2 Feec.ShortHilbertComplex Feec.Legacy.Constraints Feec.Legacy.Torus Feec.Legacy.Box
open Feec.HilbertComplex (ScaledEmbedding totalSub ReducingSubcomplex)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

/-! ### Rescaling the two differentials independently -/

section Scale2

open Feec.Legacy.MirrorCube

variable {W0 W1 W2 : Type u}
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
  (H : HilbertComplex2 W0 W1 W2) (l m : ℝ) (hl : l ≠ 0) (hm : m ≠ 0)

/-- **A two-factor rescaling is a scaled embedding**: the identity maps `(l • d₀, m • d₁)` to
`(d₀, d₁)` with chain-rule factors `l⁻¹`, `m⁻¹`. -/
def scaleEmbedding2 :
    ScaledEmbedding (scaleComplex2 H l m hl hm).toShort.toHilbertComplex
      H.toShort.toHilbertComplex where
  J i := ContinuousLinearMap.id ℝ _
  scale _ := 1
  scale_pos _ := one_pos
  inner_J i x y := by simp
  dScale i _ := if i = 0 then l⁻¹ else m⁻¹
  dScale_ne_zero i _ := by split_ifs; exacts [inv_ne_zero hl, inv_ne_zero hm]
  mapsTo i j x := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact Submodule.mem_top
      | exact x.2
  comm i j x := by
    fin_cases i <;> fin_cases j
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
    · change H.d0 ⟨x.1, x.2⟩ = l⁻¹ • (l • H.d0 ⟨x.1, x.2⟩)
      rw [smul_smul, inv_mul_cancel₀ hl, one_smul]
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
    · change H.d1 ⟨x.1, x.2⟩ = m⁻¹ • (m • H.d1 ⟨x.1, x.2⟩)
      rw [smul_smul, inv_mul_cancel₀ hm, one_smul]
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
  mem_domain_of_map i j x h := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact Submodule.mem_top
      | exact h

end Scale2

/-! ### The torus constraint -/

open Feec.Legacy.TorusSym in
theorem isReducingPair_hess_tsd :
    symComplex.d0.IsReducingPair (⊥ : Submodule ℝ L2R) L2TSDS := by
  refine isReducingPair_of_le_ker bot_le fun x => ?_
  rw [Submodule.mem_orthogonal]
  intro y hy
  obtain ⟨z, hz, hz0⟩ := mem_ker_iff.1 (L2TSDS_le_ker hy)
  have h := adjoint_isFormalAdjoint symComplex.dense0 z x
  rw [hz0, inner_zero_left] at h
  rw [hz]; exact h.symm

open Feec.Legacy.TorusSym in
theorem isReducingPair_curlS_tsd : symComplex.d1.IsReducingPair L2TSDS L2TSDT :=
  ⟨fun x => projS_mem_HcurlS x.2, fun x => lp.ext (funext fun k => by
    change curlS (freq k) (L2TSDS.starProjection x k) = L2TSDT.starProjection (curlST x) k
    rw [projS_apply, projT_apply, curlS_projS]
    rfl)⟩

/-- **`{0} × L²(TSD) × L²(TSD)` reduces the torus complex (4.16)**.
Thesis: Prop 4.19 -/
theorem reducingSubcomplex_tsd_torusSym :
    torusSym.ReducingSubcomplex
      (sub3 (⊥ : Submodule ℝ Feec.Legacy.TorusSym.L2R) Feec.Legacy.TorusSym.L2TSDS Feec.Legacy.TorusSym.L2TSDT) :=
  reducingSubcomplex_sub3 _ isReducingPair_hess_tsd isReducingPair_curlS_tsd

namespace MirrorSym

/-! ### The parity model -/

/-- **The mirror action on the complex (4.16)**: `u` even, `S` even (`D_i S D_i`), `T` odd
(`-D_i T D_i`). -/
def action : torusSym.Action ReflGroup :=
  reflAction Feec.Legacy.TorusSym.symComplex.toShort Feec.Legacy.Box.intertwines_hess Feec.Legacy.Box.intertwines_curlS

/-- **The complex (4.16) on the cube with mirror boundary conditions** (`∂_n u = 0`,
`S_{nτ} = 0`), as the fixed subcomplex.
Thesis: §4.11 -/
abbrev complex := action.fixedComplex

/-- The torus constraint `{0} × L²(TSD) × L²(TSD)` of (4.16). -/
abbrev tsd :
    ∀ i : Fin 3, Submodule ℝ (W3 Feec.Legacy.TorusSym.L2R Feec.Legacy.TorusSym.L2S Feec.Legacy.TorusSym.L2T i) :=
  sub3 (⊥ : Submodule ℝ Feec.Legacy.TorusSym.L2R) Feec.Legacy.TorusSym.L2TSDS Feec.Legacy.TorusSym.L2TSDT

theorem act_mem_tsd (g : ReflGroup) (i : Fin 3)
    (x : W3 Feec.Legacy.TorusSym.L2R Feec.Legacy.TorusSym.L2S Feec.Legacy.TorusSym.L2T i)
    (hx : x ∈ tsd i) : action.act g i x ∈ tsd i := by
  fin_cases i
  · have hx' : x = (0 : Feec.Legacy.TorusSym.L2R) := (Submodule.mem_bot ℝ).1 hx
    change reflAct mirrorR g x ∈ (⊥ : Submodule ℝ Feec.Legacy.TorusSym.L2R)
    rw [hx', _root_.map_zero]; exact Submodule.zero_mem _
  · exact reflAct_mem mirrorS (fun k A hA => mirrorS_mem_L2TSDS k hA) g hx
  · exact reflAct_mem mirrorT (fun k A hA => mirrorT_mem_L2TSDT k hA) g hx

/-- **TSD with mirror parities reduces the cube complex (4.16).**
Thesis: Prop 4.19 (corrected) -/
theorem reducingSubcomplex : complex.ReducingSubcomplex (compSub action.fixed tsd) :=
  reducingSubcomplex_compSub_fixed action reducingSubcomplex_tsd_torusSym act_mem_tsd

/-- **Prop 4.19 on the cube with mirror boundary conditions** (parity model).
Thesis: Prop 4.19 (corrected) -/
theorem propagates {a b : ℝ} {F U : ℝ → PiLp 2 fun i => action.fixed i}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ totalSub (compSub action.fixed tsd))
    (hF : ∀ t ∈ Icc a b, F t ∈ totalSub (compSub action.fixed tsd)) :
    ∀ t ∈ Icc a b, U t ∈ totalSub (compSub action.fixed tsd) :=
  reducingSubcomplex.propagates hU h0 hF

/-- Prop 4.19 on the mirror cube (parity model) with existence and uniqueness.
Thesis: Prop 4.19 (corrected) -/
theorem existsUnique_mem {U₀ : PiLp 2 fun i => action.fixed i} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀S : U₀ ∈ totalSub (compSub action.fixed tsd)) {F : ℝ → PiLp 2 fun i => action.fixed i}
    {a b : ℝ} (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFS : ∀ t ∈ Icc a b, F t ∈ totalSub (compSub action.fixed tsd)) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ totalSub (compSub action.fixed tsd)) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V → EqOn V U (Icc a b) :=
  reducingSubcomplex.existsUnique_mem hU₀ hU₀S hF hFS

/-- `K* = K` for (4.16) on the mirror cube.
Thesis: Prop 4.19 (corrected) -/
theorem invariantCore_eq :
    complex.waveGroup.invariantCore (totalSub (compSub action.fixed tsd)) =
      totalSub (compSub action.fixed tsd) :=
  reducingSubcomplex.invariantCore_eq

/-! ### The cube `Q = (0, ½)³` -/

open Feec.Legacy.MirrorCube

/-- **The complex (4.16) of genuine fields on `Q` with mirror boundary conditions**
(`Feec.Legacy.MirrorCube.mirrorSymCxQ`). -/
abbrev complexQ := mirrorSymCxQ.toShort.toHilbertComplex

/-- The mirror extensions embed the complex on `Q` in the torus complex (4.16). -/
def embeddingQ : ScaledEmbedding complexQ torusSym :=
  comprEmbedding Feec.Legacy.TorusSym.symComplex comprR comprS comprT comprComm_hess comprComm_curlS
    eight_pos

/-- The constraint on `Q`: `{0} × TSDSm × TSDTm`. -/
abbrev tsdQ : ∀ i : Fin 3, Submodule ℝ (W3 RQ SQ TQ i) := sub3 (⊥ : Submodule ℝ RQ) TSDSm TSDTm

/-- **TSD reduces the complex (4.16) on `Q`.**
Thesis: Prop 4.19 (corrected) -/
theorem reducingSubcomplexQ : complexQ.ReducingSubcomplex tsdQ :=
  reducingSubcomplex_compr Feec.Legacy.TorusSym.symComplex comprR comprS comprT comprComm_hess
    comprComm_curlS
    eight_pos reducingSubcomplex_tsd_torusSym starProjection_comprS starProjection_comprT

/-- **Prop 4.19 on `Q` with mirror boundary conditions.**
Thesis: Prop 4.19 (corrected) -/
theorem propagatesQ {a b : ℝ} {F U : ℝ → PiLp 2 (W3 RQ SQ TQ)}
    (hU : Evolution.IsStrongSolution complexQ.wave (Icc a b) F U) (h0 : U a ∈ totalSub tsdQ)
    (hF : ∀ t ∈ Icc a b, F t ∈ totalSub tsdQ) : ∀ t ∈ Icc a b, U t ∈ totalSub tsdQ :=
  reducingSubcomplexQ.propagates hU h0 hF

/-- Prop 4.19 on `Q` with existence and uniqueness.
Thesis: Prop 4.19 (corrected) -/
theorem existsUnique_memQ {U₀ : PiLp 2 (W3 RQ SQ TQ)} (hU₀ : U₀ ∈ complexQ.wave.domain)
    (hU₀S : U₀ ∈ totalSub tsdQ) {F : ℝ → PiLp 2 (W3 RQ SQ TQ)} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complexQ.wave a b F)
    (hFS : ∀ t ∈ Icc a b, F t ∈ totalSub tsdQ) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complexQ.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ totalSub tsdQ) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complexQ.wave (Icc a b) F V → EqOn V U (Icc a b) :=
  reducingSubcomplexQ.existsUnique_mem hU₀ hU₀S hF hFS

/-- `K* = K` for (4.16) on `Q`.
Thesis: Prop 4.19 (corrected) -/
theorem invariantCore_eqQ : complexQ.waveGroup.invariantCore (totalSub tsdQ) = totalSub tsdQ :=
  reducingSubcomplexQ.invariantCore_eq

/-- A non-stationary TSD datum for (4.16) on `Q`.
Thesis: Prop 4.19 (corrected) -/
theorem exists_nonstationaryQ :
    ∃ y ∈ complexQ.wave.domain, y ∈ totalSub tsdQ ∧ y ∉ complexQ.waveGroup.stationary :=
  ⟨totEquiv cosStateS, (mem_domL_iff mirrorSymCxQ).1 cosStateS_mem_domL,
    (mem_Kc_iff TSDSm TSDTm cosStateS).1 cosStateS_mem_Kc,
    totEquiv_not_mem_stationary mirrorSymCxQ cosStateS_mem_domL cosStateS_waveOp_ne⟩

/-! ### Every open cube -/

open Feec.Legacy.BoundedDomain (R3)
open Feec.Legacy.BoxIdent (openCube mem_Qr_iff_openCube)

variable {b : R3} {s : ℝ} (hs : 0 < s)

/-- **The complex (4.16) with mirror boundary conditions on the open cube** `∏ (bᵢ, bᵢ + s)`
(`Feec.Legacy.MirrorCube.mirrorSymCxCube`). -/
abbrev complexCube (b : R3) (s : ℝ) (hs : 0 < s) :=
  (mirrorSymCxCube b s hs).toShort.toHilbertComplex

/-- The pull-back along `x ↦ 2 s x + b` embeds the cube complex in the complex on `Q`, with
chain-rule factors `(2s)⁻²` on the Hessian and `(2s)⁻¹` on the curl. -/
def embeddingCube : ScaledEmbedding (complexCube b s hs) complexQ :=
  (scaleEmbedding2 mirrorSymCxQ ((2 * s) ^ 2)⁻¹ (2 * s)⁻¹ (two_s_sq_inv_ne hs)
    (inv_ne_zero (two_s_ne hs))).comp
    (comprEmbedding (symScaled s hs)
      (comprPullR (two_s_ne hs) (mem_Qr_iff_openCube hs b))
      (comprPullS (two_s_ne hs) (mem_Qr_iff_openCube hs b))
      (comprPullT (two_s_ne hs) (mem_Qr_iff_openCube hs b))
      (comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl))
      (comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl)) (pos_c (two_s_ne hs)))

/-- The constraint on the cube: the pull-back of `{0} × TSDSm × TSDTm`
(`{0} × TSDSmCube × TSDTmCube`). -/
abbrev tsdCube (b : R3) (s : ℝ) (hs : 0 < s) :
    ∀ i : Fin 3, Submodule ℝ (W3 (Feec.Legacy.BoundedDomain.L2 (openCube b s))
      (Feec.Legacy.BoundedSym.L2S (openCube b s)) (Feec.Legacy.BoundedSym.L2T (openCube b s)) i) :=
  fun i => (tsdQ i).comap ((embeddingCube (b := b) hs).J i : _ →ₗ[ℝ] _)

/-- **TSD reduces the complex (4.16) on every open cube.**
Thesis: Prop 4.19 (corrected) -/
theorem reducingSubcomplexCube : (complexCube b s hs).ReducingSubcomplex (tsdCube b s hs) :=
  (embeddingCube hs).reducingSubcomplex_comap reducingSubcomplexQ fun i x => by
    fin_cases i
    · exact ⟨_, (comprPullR (two_s_ne hs) (mem_Qr_iff_openCube hs b)).JRP _⟩
    · exact ⟨_, (comprPullS (two_s_ne hs) (mem_Qr_iff_openCube hs b)).JRP _⟩
    · exact ⟨_, (comprPullT (two_s_ne hs) (mem_Qr_iff_openCube hs b)).JRP _⟩

/-- **Prop 4.19 on every open cube with mirror boundary conditions.**
Thesis: Prop 4.19 (corrected) -/
theorem propagatesCube {a c : ℝ} {F U : ℝ → PiLp 2 (W3 (Feec.Legacy.BoundedDomain.L2 (openCube b s))
      (Feec.Legacy.BoundedSym.L2S (openCube b s)) (Feec.Legacy.BoundedSym.L2T (openCube b s)))}
    (hU : Evolution.IsStrongSolution (complexCube b s hs).wave (Icc a c) F U)
    (h0 : U a ∈ totalSub (tsdCube b s hs)) (hF : ∀ t ∈ Icc a c, F t ∈ totalSub (tsdCube b s hs)) :
    ∀ t ∈ Icc a c, U t ∈ totalSub (tsdCube b s hs) :=
  (reducingSubcomplexCube hs).propagates hU h0 hF

/-- Prop 4.19 on every open cube, with existence and uniqueness.
Thesis: Prop 4.19 (corrected) -/
theorem existsUnique_memCube {U₀ : PiLp 2 (W3 (Feec.Legacy.BoundedDomain.L2 (openCube b s))
      (Feec.Legacy.BoundedSym.L2S (openCube b s)) (Feec.Legacy.BoundedSym.L2T (openCube b s)))}
    (hU₀ : U₀ ∈ (complexCube b s hs).wave.domain) (hU₀S : U₀ ∈ totalSub (tsdCube b s hs))
    {F : ℝ → PiLp 2 (W3 (Feec.Legacy.BoundedDomain.L2 (openCube b s)) (Feec.Legacy.BoundedSym.L2S (openCube b s))
      (Feec.Legacy.BoundedSym.L2T (openCube b s)))} {a c : ℝ}
    (hF : Evolution.ForcingClass.admissible (complexCube b s hs).wave a c F)
    (hFS : ∀ t ∈ Icc a c, F t ∈ totalSub (tsdCube b s hs)) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (complexCube b s hs).wave (Icc a c) F U ∧
      (∀ t ∈ Icc a c, U t ∈ totalSub (tsdCube b s hs)) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (complexCube b s hs).wave (Icc a c) F V →
        EqOn V U (Icc a c) :=
  (reducingSubcomplexCube hs).existsUnique_mem hU₀ hU₀S hF hFS

/-- `K* = K` for (4.16) on every open cube.
Thesis: Prop 4.19 (corrected) -/
theorem invariantCore_eqCube :
    (complexCube b s hs).waveGroup.invariantCore (totalSub (tsdCube b s hs)) =
      totalSub (tsdCube b s hs) :=
  (reducingSubcomplexCube hs).invariantCore_eq

theorem waveOp_cosStateSCube_ne :
    (mirrorSymCxCube b s hs).waveOp ⟨_, cosStateSCube_mem_domL hs⟩ ≠ 0 := by
  intro h0
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

theorem cosStateSCube_mem_tsdCube :
    totEquiv (cosStateSCube b s hs) ∈ totalSub (tsdCube b s hs) := by
  have hK := (mem_Kc.1 (cosStateSCube_mem_Kc (b := b) hs))
  intro i
  fin_cases i
  · change (embeddingCube (b := b) hs).J 0 (-(tot _ _ _ (cosStateSCube b s hs)).1) ∈
      (⊥ : Submodule ℝ RQ)
    rw [hK.1, neg_zero]
    exact (Submodule.mem_bot ℝ (M := RQ)).2 (_root_.map_zero ((embeddingCube (b := b) hs).J 0))
  · exact hK.2.1
  · exact hK.2.2

/-- A non-stationary TSD datum for (4.16) on every open cube.
Thesis: Prop 4.19 (corrected) -/
theorem exists_nonstationaryCube :
    ∃ y ∈ (complexCube b s hs).wave.domain, y ∈ totalSub (tsdCube b s hs) ∧
      y ∉ (complexCube b s hs).waveGroup.stationary :=
  ⟨totEquiv (cosStateSCube b s hs),
    (mem_domL_iff (mirrorSymCxCube b s hs)).1 (cosStateSCube_mem_domL hs),
    cosStateSCube_mem_tsdCube hs,
    totEquiv_not_mem_stationary (mirrorSymCxCube b s hs) (cosStateSCube_mem_domL hs)
      (waveOp_cosStateSCube_ne hs)⟩

end MirrorSym

end Feec.Models.Cube
