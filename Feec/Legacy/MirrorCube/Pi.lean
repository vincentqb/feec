module

public import Feec.Legacy.MirrorCube.Cube

/-!
# Prop 4.17 with mirror boundary conditions on every open cube

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

`Feec.Legacy.MirrorCube.Cube` proves the repaired Prop 4.17 on `Q = (0, ½)³`. This file carries it
along `T x = 2s x + b`, which maps `Q` onto `openCube b s = ∏ᵢ (bᵢ, bᵢ + s)`
(`Feec.Legacy.BoxIdent.mem_Qr_iff_openCube`):

* `scaleComplex`: a Hilbert complex with both differentials multiplied by `λ ≠ 0` (adjoints
  scale by `λ`, `D(L)` is unchanged, `L` scales by `λ`), and the hypotheses of the abstract
  Prop 4.17 are invariant (`reducing_hyps_scale`).
* `mirrorCxCube b s`: the compression of `(2s)⁻¹ · mirrorCxQ` by the pull-back `E ↦ E ∘ T`
  (`comprPullM`, `comprPullV`, with `P = id`), so `d1 E = curl E` (the chain rule factor `2s`
  cancels): `mirrorCxCube_d1_eq` (`d1` is the weak curl on the cube).
* **`Feec.Models.Cube.Mirror.existsUnique_memCube`**, `Feec.Models.Cube.Mirror.reducingSubcomplexCube`, `Feec.Models.Cube.Mirror.invariantCore_eqCube`,
  `Feec.Models.Cube.Mirror.exists_nonstationaryCube`, and the constraint spaces lie in `L²(TSD)` of the cube
  (`TSDmECube_le_TSD`, `TSDmBCube_le_TSD`); `Feec.Models.Cube.Mirror.existsUnique_memCube` for `(0, π)³`,
  `Feec.Models.Cube.Mirror.existsUnique_memCube` for the unit cube `(0, 1)³` (the domain meshed in Ch. 7;
  the Ch. 7 test solution, with time-dependent boundary values, is not covered).

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17), Ch. 7 (the unit cube mesh)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open Set LinearPMap

namespace Feec.Legacy.MirrorCube

open Feec.Legacy.Torus Feec.Legacy.Constraints Feec.Legacy.HilbertComplex2 Feec.Legacy.BoxIdent Feec.Legacy.Box

/-! ## Scaling a Hilbert complex -/

section Scale

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem isClosed_smul {T : E →ₗ.[ℝ] F} (hT : T.IsClosed) {s : ℝ} (hs : s ≠ 0) :
    (s • T).IsClosed := by
  change IsClosed ((s • T).graph : Set (E × F))
  have e : ((s • T).graph : Set (E × F)) =
      (Prod.map id (fun y : F => s⁻¹ • y)) ⁻¹' (T.graph : Set (E × F)) := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearPMap.mem_graph_iff, mem_preimage, Prod.map_apply, id]
    constructor
    · rintro ⟨z, rfl, rfl⟩
      exact ⟨z, rfl, by rw [LinearPMap.smul_apply, smul_smul, inv_mul_cancel₀ hs, one_smul]⟩
    · rintro ⟨z, rfl, hz⟩
      refine ⟨z, rfl, ?_⟩
      rw [LinearPMap.smul_apply]
      change s • T z = y
      rw [hz, smul_smul, mul_inv_cancel₀ hs, one_smul]
  rw [e]
  exact hT.preimage (continuous_id.prodMap (continuous_const_smul _))

omit [CompleteSpace F] in
theorem mem_adjoint_smul_iff {T : E →ₗ.[ℝ] F} (hd : Dense (T.domain : Set E)) {s : ℝ}
    (hs : s ≠ 0) {y : F} : y ∈ (s • T)†.domain ↔ y ∈ T†.domain := by
  have hd' : Dense ((s • T).domain : Set E) := hd
  constructor
  · intro hy
    refine mem_adjoint_domain_of_exists _ ⟨s⁻¹ • (s • T)† ⟨y, hy⟩, fun x => ?_⟩
    have h := adjoint_isFormalAdjoint hd' ⟨y, hy⟩ (⟨x, x.2⟩ : (s • T).domain)
    rw [real_inner_smul_left, h]
    change s⁻¹ * ⟪(y : F), s • T x⟫ = _
    rw [real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  · intro hy
    refine mem_adjoint_domain_of_exists _ ⟨s • T† ⟨y, hy⟩, fun x => ?_⟩
    have h := adjoint_isFormalAdjoint hd ⟨y, hy⟩ (⟨x, x.2⟩ : T.domain)
    rw [real_inner_smul_left, h]
    change _ = ⟪(y : F), s • T ⟨x, x.2⟩⟫
    rw [real_inner_smul_right]

omit [CompleteSpace F] in
theorem adjoint_smul_apply {T : E →ₗ.[ℝ] F} (hd : Dense (T.domain : Set E)) {s : ℝ}
    (hs : s ≠ 0) (y : (s • T)†.domain) :
    (s • T)† y = s • T† ⟨y, (mem_adjoint_smul_iff hd hs).1 y.2⟩ := by
  have hd' : Dense ((s • T).domain : Set E) := hd
  refine adjoint_apply_eq hd' y fun x => ?_
  have h := adjoint_isFormalAdjoint hd ⟨y, (mem_adjoint_smul_iff hd hs).1 y.2⟩
    (⟨x, x.2⟩ : T.domain)
  rw [real_inner_smul_left, h]
  change _ = ⟪((y : F)), s • T ⟨x, x.2⟩⟫
  rw [real_inner_smul_right]

variable {W0 W1 W2 : Type*}
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]

/-- **A Hilbert complex with both differentials multiplied by `λ ≠ 0`.** -/
def scaleComplex (H : HilbertComplex2 W0 W1 W2) (s : ℝ) (hs : s ≠ 0) : HilbertComplex2 W0 W1 W2 where
  d0 := s • H.d0
  d1 := s • H.d1
  dense0 := H.dense0
  dense1 := H.dense1
  closed0 := isClosed_smul H.closed0 hs
  closed1 := isClosed_smul H.closed1 hs
  map_mem x := by
    change s • H.d0 ⟨x, x.2⟩ ∈ H.d1.domain
    exact H.d1.domain.smul_mem _ (H.map_mem _)
  comp_zero x := by
    rw [LinearPMap.smul_apply]
    have e : ((⟨(s • H.d0) x, by
        change s • H.d0 ⟨x, x.2⟩ ∈ H.d1.domain
        exact H.d1.domain.smul_mem _ (H.map_mem _)⟩ : H.d1.domain)) =
        s • (⟨H.d0 ⟨x, x.2⟩, H.map_mem _⟩ : H.d1.domain) := rfl
    rw [e, LinearPMap.map_smul, H.comp_zero, smul_zero, smul_zero]

variable {H : HilbertComplex2 W0 W1 W2} {s : ℝ} (hs : s ≠ 0)

theorem mem_domL_scale_iff (x : Tot W0 W1 W2) :
    x ∈ (scaleComplex H s hs).domL ↔ x ∈ H.domL := by
  rw [Constraints.mem_domL, Constraints.mem_domL]
  change (tot W0 W1 W2 x).1 ∈ H.d0.domain ∧ ((tot W0 W1 W2 x).2.1 ∈ H.d1.domain ∧
      (tot W0 W1 W2 x).2.1 ∈ (s • H.d0)†.domain) ∧ (tot W0 W1 W2 x).2.2 ∈ (s • H.d1)†.domain ↔
    (tot W0 W1 W2 x).1 ∈ H.d0.domain ∧ ((tot W0 W1 W2 x).2.1 ∈ H.d1.domain ∧
      (tot W0 W1 W2 x).2.1 ∈ H.d0†.domain) ∧ (tot W0 W1 W2 x).2.2 ∈ H.d1†.domain
  rw [mem_adjoint_smul_iff H.dense0 hs, mem_adjoint_smul_iff H.dense1 hs]

theorem ker_adj0_scale : (scaleComplex H s hs).d0†.ker = H.d0†.ker := by
  ext u
  constructor
  · intro hu
    obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hu
    have hy' : (y : W1) ∈ H.d0†.domain := (mem_adjoint_smul_iff H.dense0 hs).1 y.2
    refine LinearPMap.mem_ker_iff.2 ⟨⟨y, hy'⟩, hy, ?_⟩
    have e := adjoint_smul_apply H.dense0 hs y
    change (s • H.d0)† y = 0 at hy0
    rw [hy0] at e
    exact (smul_eq_zero.1 e.symm).resolve_left hs
  · intro hu
    obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hu
    have hy' : (y : W1) ∈ (s • H.d0)†.domain := (mem_adjoint_smul_iff H.dense0 hs).2 y.2
    refine LinearPMap.mem_ker_iff.2 ⟨⟨y, hy'⟩, hy, ?_⟩
    change (s • H.d0)† ⟨y, hy'⟩ = 0
    rw [adjoint_smul_apply H.dense0 hs]
    rw [show (⟨(y : W1), (mem_adjoint_smul_iff H.dense0 hs).1 hy'⟩ : H.d0†.domain) = y from rfl,
      hy0, smul_zero]

/-- **The Hodge wave operator scales**: `L_λ = λ L`. -/
theorem waveOp_scale (x : Tot W0 W1 W2) (hx : x ∈ (scaleComplex H s hs).domL) :
    (scaleComplex H s hs).waveOp ⟨x, hx⟩ = s • H.waveOp ⟨x, (mem_domL_scale_iff hs x).1 hx⟩ := by
  apply (tot W0 W1 W2).injective
  rw [Constraints.tot_waveOp, _root_.map_smul, Constraints.tot_waveOp]
  have e1 : (s • H.d0)† ((scaleComplex H s hs).prV1s ⟨x, hx⟩) =
      s • H.d0† (H.prV1s ⟨x, (mem_domL_scale_iff hs x).1 hx⟩) :=
    adjoint_smul_apply H.dense0 hs _
  have e2 : (s • H.d1)† ((scaleComplex H s hs).prV2s ⟨x, hx⟩) =
      s • H.d1† (H.prV2s ⟨x, (mem_domL_scale_iff hs x).1 hx⟩) :=
    adjoint_smul_apply H.dense1 hs _
  have e3 : (s • H.d0) ((scaleComplex H s hs).pr0 ⟨x, hx⟩) =
      s • H.d0 (H.pr0 ⟨x, (mem_domL_scale_iff hs x).1 hx⟩) := rfl
  have e4 : (s • H.d1) ((scaleComplex H s hs).prV1 ⟨x, hx⟩) =
      s • H.d1 (H.prV1 ⟨x, (mem_domL_scale_iff hs x).1 hx⟩) := rfl
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change -((s • H.d0)† ((scaleComplex H s hs).prV1s ⟨x, hx⟩)) = _
    rw [e1]
    simp only [Prod.smul_fst, smul_neg]
  · change (s • H.d0) ((scaleComplex H s hs).pr0 ⟨x, hx⟩) +
      (s • H.d1)† ((scaleComplex H s hs).prV2s ⟨x, hx⟩) = _
    rw [e2, e3]
    simp only [Prod.smul_snd, Prod.smul_fst, smul_add]
  · change -((s • H.d1) ((scaleComplex H s hs).prV1 ⟨x, hx⟩)) = _
    rw [e4]
    simp only [Prod.smul_snd, smul_neg]

/-- **The hypotheses of the abstract Prop 4.17 are invariant under scaling.** -/
theorem reducing_hyps_scale (S1 : Submodule ℝ W1) (S2 : Submodule ℝ W2)
    [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection] (hS1 : S1 ≤ H.d0†.ker)
    (hPD : ∀ x ∈ H.domL, projKc W0 S1 S2 x ∈ H.domL)
    (hd1 : ∀ u : H.d1.domain, (u : W1) ∈ S1 → H.d1 u ∈ S2)
    (hd1s : ∀ ρ : H.d1†.domain, (ρ : W2) ∈ S2 → H.d1† ρ ∈ S1) :
    S1 ≤ (scaleComplex H s hs).d0†.ker ∧
    (∀ x ∈ (scaleComplex H s hs).domL, projKc W0 S1 S2 x ∈ (scaleComplex H s hs).domL) ∧
    (∀ u : (scaleComplex H s hs).d1.domain, (u : W1) ∈ S1 →
      (scaleComplex H s hs).d1 u ∈ S2) ∧
    (∀ ρ : (scaleComplex H s hs).d1†.domain, (ρ : W2) ∈ S2 →
      (scaleComplex H s hs).d1† ρ ∈ S1) := by
  refine ⟨fun u hu => by rw [ker_adj0_scale (H := H) hs]; exact hS1 hu, fun x hx => ?_,
    fun u hu => ?_, fun ρ hρ => ?_⟩
  · rw [mem_domL_scale_iff] at hx ⊢; exact hPD x hx
  · change s • H.d1 ⟨u, u.2⟩ ∈ S2
    exact S2.smul_mem _ (hd1 ⟨u, u.2⟩ hu)
  · have e : (scaleComplex H s hs).d1† ρ = s • H.d1† ⟨ρ, (mem_adjoint_smul_iff H.dense1 hs).1 ρ.2⟩ :=
      adjoint_smul_apply H.dense1 hs ρ
    rw [e]
    exact S1.smul_mem _ (hd1s _ hρ)

end Scale

/-! ## Pull-back compression data -/

section Pull

open BoundedDomain (R3)

variable {a : ℝ} {b : R3} {Ω Ω' : Set R3} (ha : a ≠ 0) (hT : ∀ x, x ∈ Ω ↔ a • x + b ∈ Ω')

theorem inv_pullV (u : BoundedDomain.L2V Ω') :
    pullV (inv_ne_zero ha) (hT_inv ha hT) (pullV ha hT u) = u :=
  (WithLp.ext_iff 2).2 (funext fun i => inv_pull ha hT (u i))

theorem pos_c {a : ℝ} (ha : a ≠ 0) : 0 < |a ^ 3|⁻¹ := inv_pos.2 (abs_pos.2 (pow_ne_zero 3 ha))

/-- Pull-back along `x ↦ a x + b` as compression data (`P = id`). -/
def comprPullM : Compr (|a ^ 3|⁻¹) (BoundedDomain.L2M Ω') (BoundedDomain.L2M Ω) where
  J := pullM ha hT
  R := pullM (inv_ne_zero ha) (hT_inv ha hT)
  P := ContinuousLinearMap.id ℝ _
  inner_J := inner_pullM ha hT
  RJ := inv_pullM ha hT
  JRP z := pullM_inv ha hT z
  PJ _ := rfl
  P_sa _ _ := rfl

/-- Pull-back of vector fields as compression data. -/
def comprPullV : Compr (|a ^ 3|⁻¹) (BoundedDomain.L2V Ω') (BoundedDomain.L2V Ω) where
  J := pullV ha hT
  R := pullV (inv_ne_zero ha) (hT_inv ha hT)
  P := ContinuousLinearMap.id ℝ _
  inner_J := inner_pullV ha hT
  RJ := inv_pullV ha hT
  JRP z := pullV_inv ha hT z
  PJ _ := rfl
  P_sa _ _ := rfl

theorem comprComm_id {X Y X' Y' : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [NormedAddCommGroup X']
    [InnerProductSpace ℝ X'] [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] {c : ℝ}
    (T : X →ₗ.[ℝ] Y) (A : Compr c X' X) (B : Compr c Y' Y)
    (hA : ∀ z, A.P z = z) (hB : ∀ z, B.P z = z) : ComprComm T A B := fun z =>
  ⟨by rw [hA]; exact z.2, by rw [hB]; exact lpmap_congr' T _ _ (hA z)⟩

end Pull

/-! ## The mirror complex on every open cube -/

section MirrorCube

open BoundedDomain (R3)

variable {b : R3} {s : ℝ} (hs : 0 < s)

theorem two_s_ne (hs : 0 < s) : (2 * s) ≠ 0 := by positivity

/-- **The complex `H¹_n → H_{nτ}(curl) → L²` with tensorial mirror boundary conditions on the
open cube `∏ᵢ (bᵢ, bᵢ + s)`**: the compression of `(2s)⁻¹ · mirrorCxQ` by `E ↦ E ∘ T`,
`T x = 2s x + b`. -/
def mirrorCxCube (b : R3) (s : ℝ) (hs : 0 < s) :
    HilbertComplex2 (BoundedDomain.L2V (openCube b s)) (BoundedDomain.L2M (openCube b s))
      (BoundedDomain.L2M (openCube b s)) :=
  comprComplex (scaleComplex mirrorCxQ (2 * s)⁻¹ (inv_ne_zero (two_s_ne hs)))
    (comprPullV (two_s_ne hs) (mem_Qr_iff_openCube hs b))
    (comprPullM (two_s_ne hs) (mem_Qr_iff_openCube hs b))
    (comprPullM (two_s_ne hs) (mem_Qr_iff_openCube hs b))
    (comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl))
    (comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl))

/-- The electric constraint space on the cube: `E ∘ T ∈ TSDmE`. -/
abbrev TSDmECube (b : R3) (s : ℝ) (hs : 0 < s) : Submodule ℝ (BoundedDomain.L2M (openCube b s)) :=
  TSDmE.comap ((comprPullM (two_s_ne hs) (mem_Qr_iff_openCube hs b)).J :
    BoundedDomain.L2M (openCube b s) →ₗ[ℝ] MQ)

/-- The magnetic constraint space on the cube: `B ∘ T ∈ TSDmB`. -/
abbrev TSDmBCube (b : R3) (s : ℝ) (hs : 0 < s) : Submodule ℝ (BoundedDomain.L2M (openCube b s)) :=
  TSDmB.comap ((comprPullM (two_s_ne hs) (mem_Qr_iff_openCube hs b)).J :
    BoundedDomain.L2M (openCube b s) →ₗ[ℝ] MQ)

theorem mirrorCxQ_hyps :
    TSDmE ≤ mirrorCxQ.d0†.ker ∧
    (∀ x ∈ mirrorCxQ.domL, projKc VQ TSDmE TSDmB x ∈ mirrorCxQ.domL) ∧
    (∀ u : mirrorCxQ.d1.domain, (u : MQ) ∈ TSDmE → mirrorCxQ.d1 u ∈ TSDmB) ∧
    (∀ ρ : mirrorCxQ.d1†.domain, (ρ : MQ) ∈ TSDmB → mirrorCxQ.d1† ρ ∈ TSDmE) :=
  reducing_hyps_compr (h0 := comprComm_grad) (h1 := comprComm_curl) L2TSD L2TSD eight_pos
    L2TSD_le_ker projKc_mem_domL curlT_mem_L2TSD adjoint_curlT_mem_L2TSD
    (starProjection_Pm 1 one_mul_one) (starProjection_Pm (-1) neg_one_mul_neg_one)

theorem scaled_hyps :
    TSDmE ≤ (scaleComplex mirrorCxQ (2 * s)⁻¹ (inv_ne_zero (two_s_ne hs))).d0†.ker ∧
    (∀ x ∈ (scaleComplex mirrorCxQ (2 * s)⁻¹ (inv_ne_zero (two_s_ne hs))).domL,
      projKc VQ TSDmE TSDmB x ∈ (scaleComplex mirrorCxQ (2 * s)⁻¹ (inv_ne_zero (two_s_ne hs))).domL) ∧
    (∀ u : (scaleComplex mirrorCxQ (2 * s)⁻¹ (inv_ne_zero (two_s_ne hs))).d1.domain,
      (u : MQ) ∈ TSDmE → (scaleComplex mirrorCxQ (2 * s)⁻¹ (inv_ne_zero (two_s_ne hs))).d1 u ∈ TSDmB) ∧
    (∀ ρ : (scaleComplex mirrorCxQ (2 * s)⁻¹ (inv_ne_zero (two_s_ne hs))).d1†.domain,
      (ρ : MQ) ∈ TSDmB →
        (scaleComplex mirrorCxQ (2 * s)⁻¹ (inv_ne_zero (two_s_ne hs))).d1† ρ ∈ TSDmE) :=
  reducing_hyps_scale (inv_ne_zero (two_s_ne hs)) TSDmE TSDmB mirrorCxQ_hyps.1
    mirrorCxQ_hyps.2.1 mirrorCxQ_hyps.2.2.1 mirrorCxQ_hyps.2.2.2

/-! ### Faithfulness on the cube -/

/-- **`d1` on the cube is the weak curl**: `D(d1) ⊆ H(curl, cube)` and `d1 E` is the weak curl
of `E` (the maximal curl `d1*` of the thesis' complex on the cube). -/
theorem mirrorCxCube_d1_eq (E : (mirrorCxCube b s hs).d1.domain) :
    ∃ h : (E : BoundedDomain.L2M (openCube b s)) ∈ (cxCube b s).d1†.domain,
      (cxCube b s).d1† ⟨E, h⟩ = (mirrorCxCube b s hs).d1 E := by
  set a := 2 * s
  have ha : a ≠ 0 := two_s_ne hs
  have hT := mem_Qr_iff_openCube hs b
  have hE : pullM ha hT E ∈ mirrorCxQ.d1.domain := E.2
  obtain ⟨h1, e1⟩ := mirrorCxQ_d1_eq ⟨_, hE⟩
  obtain ⟨h2, e2⟩ := adj1_pull (inv_ne_zero ha) (hT_inv ha hT) (isOpen_openCube b s)
    (isBounded_openCube b s) isOpen_Qr isBounded_Qr ⟨_, h1⟩
  have hinv : pullM (inv_ne_zero ha) (hT_inv ha hT) (pullM ha hT E) = E := inv_pullM ha hT _
  have h3 : (E : BoundedDomain.L2M (openCube b s)) ∈ (cxCube b s).d1†.domain := by
    have := h2; rwa [hinv] at this
  refine ⟨h3, ?_⟩
  have e3 : (cxCube b s).d1† ⟨E, h3⟩ =
      (BoundedDomain.curlClosure (Ω := openCube b s))† ⟨_, h2⟩ := lpmap_congr' _ _ _ hinv.symm
  rw [e3, e2]
  change _ = pullM (inv_ne_zero ha) (hT_inv ha hT) ((2 * s)⁻¹ • mirrorCxQ.d1 ⟨_, hE⟩)
  rw [_root_.map_smul, ← e1]
  rfl

/-- The constraint spaces on the cube consist of TSD fields. -/
theorem TSDmECube_le_TSD : TSDmECube b s hs ≤ BoundedDomain.TSD (openCube b s) := fun E hE => by
  have ha : 2 * s ≠ 0 := two_s_ne hs
  have hE' : pullM ha (mem_Qr_iff_openCube hs b) E ∈ TSDmE := hE
  have h := pullM_mem_TSD (inv_ne_zero ha) (hT_inv ha (mem_Qr_iff_openCube hs b))
    (isOpen_openCube b s) (isBounded_openCube b s) isOpen_Qr isBounded_Qr (TSDmE_le_TSD hE')
  rwa [inv_pullM] at h

theorem TSDmBCube_le_TSD : TSDmBCube b s hs ≤ BoundedDomain.TSD (openCube b s) := fun B hB => by
  have ha : 2 * s ≠ 0 := two_s_ne hs
  have hB' : pullM ha (mem_Qr_iff_openCube hs b) B ∈ TSDmB := hB
  have h := pullM_mem_TSD (inv_ne_zero ha) (hT_inv ha (mem_Qr_iff_openCube hs b))
    (isOpen_openCube b s) (isBounded_openCube b s) isOpen_Qr isBounded_Qr (TSDmB_le_TSD hB')
  rwa [inv_pullM] at h

/-! ### A non-stationary datum on the cube -/

/-- The datum `(0, E₀ ∘ T⁻¹, 0)` on the cube, `E₀ = (2 cos(2π x₃) diag(1, -1, 0))|_Q`. -/
def cosStateCube (b : R3) (s : ℝ) (hs : 0 < s) :
    Tot (BoundedDomain.L2V (openCube b s)) (BoundedDomain.L2M (openCube b s))
      (BoundedDomain.L2M (openCube b s)) :=
  ini _ (pullM (inv_ne_zero (two_s_ne hs)) (hT_inv (two_s_ne hs) (mem_Qr_iff_openCube hs b))
    cosEQ) 0

theorem totJ_cosStateCube :
    totJ (comprPullV (two_s_ne hs) (mem_Qr_iff_openCube hs b))
      (comprPullM (two_s_ne hs) (mem_Qr_iff_openCube hs b))
      (comprPullM (two_s_ne hs) (mem_Qr_iff_openCube hs b)) (cosStateCube b s hs) =
      cosStateQ := by
  apply (tot VQ MQ MQ).injective
  rw [tot_totJ, cosStateCube, tot_ini, cosStateQ, tot_ini]
  simp only [_root_.map_zero]
  exact Prod.ext rfl (Prod.ext (pullM_inv _ _ _) rfl)

theorem cosStateCube_mem_domL : cosStateCube b s hs ∈ (mirrorCxCube b s hs).domL := by
  rw [mirrorCxCube, mem_domL_compr_iff (pos_c (two_s_ne hs)), totJ_cosStateCube,
    mem_domL_scale_iff]
  exact cosStateQ_mem_domL

theorem cosStateCube_mem_Kc : cosStateCube b s hs ∈ Kc (BoundedDomain.L2V (openCube b s))
    (TSDmECube b s hs) (TSDmBCube b s hs) := by
  rw [mem_Kc, cosStateCube, tot_ini]
  refine ⟨rfl, ?_, Submodule.zero_mem _⟩
  change pullM _ _ (pullM _ _ cosEQ) ∈ TSDmE
  rw [pullM_inv]; exact cosEQ_mem_TSDmE

end MirrorCube

end Feec.Legacy.MirrorCube
