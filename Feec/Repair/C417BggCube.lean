module

public import Feec.Repair.C419Cube
public import Feec.Repair.C417BggTorus
public import Feec.Ch6.Bounded

/-!
# Chapter 6 on the box `Q = (0, ½)³` with tensorial mirror boundary conditions

**Thesis claim** ([QuennevilleBelair2015, §6.1, §6.3, Table 6.1]). The Ch. 6 method (Hodge wave
of the BGG complex (5.1), symmetry of `E` imposed weakly through `M`) with the §6.3 boundary
conditions solves the linearized EB system, i.e. TSD data propagate as for Props 4.17/4.19.

**Defect.** On every bounded domain with the §6.3 boundary conditions the datum `(0, 0, (0, β))`
loses TSD and `B` loses symmetry (`Feec.Ch6.Bounded.bggComplex_verdict`); the mechanism only
uses that the second operator is `(S₁, curl)` on `H̊(curl, M)`.

**Repair (this file).** On the box with tensorial mirror boundary conditions the Ch. 6 system
propagates TSD: `bggCxQ : L²(Q) → L²(Q; ℝ³ˣ³) → L²(Q; ℝ³) × L²(Q; ℝ³ˣ³)` is the compression of
the periodic BGG complex `Feec.Repair.C417.bggTorus` by the mirror extensions (`u` even;
`E` with the tensor parities, `E_{nτ} = 0`; the multiplier `M` with the pseudo-vector parities
`M(R_i x) = -D_i M(x)`, forced by `S₁ (D M D) = -D S₁ M`; `B` with the pseudo-tensor parities).
Its second operator is `u ↦ (S₁ u, curl u)` with `S₁ = 2 vskw` pointwise and `curl` the mirror
curl of Prop 4.17 (`bggCxQ_d1_eq`).

## Main results

* **`bggCxQ_verdict`**: for `E₀ ∈ TSDmE`, `B₀ ∈ TSDmB` with `(0, E₀, (0, B₀)) ∈ D(L)` the Hodge
  wave equation of (5.1) on `Q` has a strong solution, unique among strong solutions, with
  `σ ≡ 0`, `u(t) ∈ TSDmE ⊆ L²(TSD)(Q)`, `M(t) = 0` and `B(t) ∈ TSDmB ⊆ L²(TSD)(Q)` (in particular
  `B` stays symmetric), solving (4.15). Contrast `Feec.Ch6.Bounded.bggComplex_verdict`.
* `bggCxQ_projection_hyp`, `bggCxQ_Kmax_eq` (`K* = K`), `bggCxQ_exists_nonstationary`.

## References

* [QuennevilleBelair2015], Ch. 5 (§5.1), Ch. 6 (§6.1, §6.3)
* [ArnoldHu2021] (BGG), [AFW2007] (weak symmetry), [AFW2010] (Hilbert complexes)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace InnerProductSpace ComplexConjugate
open MeasureTheory Set Filter Topology LinearPMap

namespace Feec.Repair.C417

open Feec.Torus Feec.TorusWeak UnitAddTorus Feec.Box Feec.BoxIdent Feec.Constraints
open Feec.HilbertComplex2
open Feec.BoundedDomain (R3 Ix IsTest curlM)

attribute [local instance] Feec.Torus.instMeasureSpaceUnitAddCircle_feec

/-! ## The pseudo-vector mirror class -/

section PV

/-- The pseudo-vector mirror action on vectors, `v ↦ -D_i v`. -/
def mirrorPVf : Refl3 Vec3 where
  R i := -vecSgn i
  invol i u := by
    simp only [_root_.neg_apply, _root_.map_neg, neg_neg]
    exact mirrorVf.invol i u
  inner_map i u v := by
    simp only [_root_.neg_apply, inner_neg_left, inner_neg_right, neg_neg]
    exact mirrorVf.inner_map i u v
  comm i j u := by
    simp only [_root_.neg_apply, _root_.map_neg, neg_neg]
    exact mirrorVf.comm i j u

/-- The pseudo-vector mirror action on `L2V`. -/
def mirrorPV : Refl3 L2V := mirrorPVf.lift

/-- The parity of the component `a` of a pseudo-vector in `x_i`: `-s_i(a)`. -/
def cPV (a : Fin 3) : Fin 3 → ℝ := fun i => -sgn i a

theorem cPV_sq (a i : Fin 3) : cPV a i * cPV a i = 1 := by
  simp only [cPV, neg_mul_neg]; exact sgn_mul_self i a

/-- The entrywise pseudo-vector extension, before the Fourier transform. -/
def extPVpi (u : BoundedDomain.L2V Qr) : VField :=
  WithLp.toLp 2 fun a => extS (cPV_sq a) (u a)

theorem norm_sq_extPVpi (u : BoundedDomain.L2V Qr) : ‖extPVpi u‖ ^ 2 = 8 * ‖u‖ ^ 2 := by
  rw [extPVpi, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact norm_sq_extS (cPV_sq a) (u a)

/-- **The pseudo-vector mirror extension** `L²(Q; ℝ³) → L2V`. -/
def Jpv : BoundedDomain.L2V Qr →L[ℝ] L2V :=
  LinearMap.mkContinuous
    { toFun := fun u => vectorFourier (extPVpi u)
      map_add' := fun u u' => by
        rw [← _root_.map_add]; congr 1
        ext a; simp [extPVpi]
      map_smul' := fun r u => by
        rw [RingHom.id_apply, show r • vectorFourier (extPVpi u) =
          vectorFourier ((r : ℂ) • extPVpi u) by rw [_root_.map_smul]; rfl]
        congr 1
        ext a; simp [extPVpi]; rfl }
    (Real.sqrt 8) fun u => by
      refine le_of_eq ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearIsometryEquiv.norm_map]
      rw [← Real.sqrt_sq (norm_nonneg (extPVpi u)), norm_sq_extPVpi,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]

theorem Jpv_apply' (u : BoundedDomain.L2V Qr) : Jpv u = vectorFourier (extPVpi u) := rfl

theorem vectorFourier_symm_Jpv (u : BoundedDomain.L2V Qr) (a : Fin 3) :
    vectorFourier.symm (Jpv u) a = extS (cPV_sq a) (u a) := by
  rw [Jpv_apply', LinearIsometryEquiv.symm_apply_apply]; rfl

theorem Jpv_coeff (u : BoundedDomain.L2V Qr) (k : Z3) (a : Fin 3) :
    Jpv u k a = mFourierCoeff (extS (cPV_sq a) (u a) : T3 → ℂ) k := by
  rw [← vectorFourier_symm_Jpv, vectorFourier_symm_apply, mFourierCoeff_ofCoeff]; rfl

theorem resBV_Jpv (u : BoundedDomain.L2V Qr) : resBV (Jpv u) = u := by
  ext1 a
  rw [resBV_apply, vectorFourier_symm_Jpv, resQ_extS]

theorem Jpv_mem_fix (u : BoundedDomain.L2V Qr) : Jpv u ∈ mirrorPV.fix := fun i => by
  ext k a
  change (-vecSgn i) (Jpv u (Box.refl i k)) a = Jpv u k a
  rw [_root_.neg_apply, PiLp.neg_apply, vecSgn_apply, Jpv_coeff, Jpv_coeff,
    hasPar_extS (cPV_sq a) _ i k, ← mul_assoc, ← Complex.ofReal_mul]
  have := cPV_sq a i
  simp only [cPV] at this ⊢
  rw [neg_mul_neg] at this
  rw [mul_neg, this, Complex.ofReal_neg, Complex.ofReal_one]
  ring

theorem isRealV_Jpv (u : BoundedDomain.L2V Qr) : IsRealV (Jpv u) :=
  fun k a => by rw [Jpv_coeff, Jpv_coeff, isRealT_extS]

theorem norm_sq_Jpv (u : BoundedDomain.L2V Qr) : ‖Jpv u‖ ^ 2 = 8 * ‖u‖ ^ 2 := by
  rw [Jpv_apply', LinearIsometryEquiv.norm_map, norm_sq_extPVpi]

theorem inner_Jpv (u u' : BoundedDomain.L2V Qr) : ⟪Jpv u, Jpv u'⟫_ℝ = 8 * ⟪u, u'⟫_ℝ := by
  have e1 := norm_sq_Jpv (u + u')
  rw [_root_.map_add, norm_add_sq_real, norm_add_sq_real, norm_sq_Jpv, norm_sq_Jpv] at e1
  linarith

theorem coeffPV_refl_of_mem_fix {σ : L2V} (hσ : σ ∈ mirrorPV.fix) (i : Fin 3) (k : Z3)
    (a : Fin 3) : σ (Box.refl i k) a = (cPV a i : ℂ) * σ k a := by
  have h := congrArg (fun ρ : L2V => ρ k a) (hσ i)
  change (-vecSgn i) (σ (Box.refl i k)) a = σ k a at h
  rw [_root_.neg_apply, PiLp.neg_apply, vecSgn_apply] at h
  rw [← h]
  have := cV_sq a i
  simp only [cPV, cV] at this ⊢
  rw [Complex.ofReal_neg, neg_mul, mul_neg, neg_neg, ← mul_assoc, ← Complex.ofReal_mul, this,
    Complex.ofReal_one, one_mul]

theorem Jpv_resBV {σ : L2V} (hσ : σ ∈ mirrorPV.fix) (hr : IsRealV σ) : Jpv (resBV σ) = σ := by
  have hp : ∀ a, extS (cPV_sq a) (resBV σ a) = vectorFourier.symm σ a := fun a => by
    rw [resBV_apply]
    refine extS_resQ (cPV_sq a) (fun i k => ?_) (fun k => ?_)
    · rw [vectorFourier_symm_apply, mFourierCoeff_ofCoeff, mFourierCoeff_ofCoeff]
      exact coeffPV_refl_of_mem_fix hσ i k a
    · rw [vectorFourier_symm_apply, mFourierCoeff_ofCoeff, mFourierCoeff_ofCoeff]
      exact hr k a
  rw [Jpv_apply']
  have e : extPVpi (resBV σ) = vectorFourier.symm σ := by
    ext1 a
    exact hp a
  rw [e, LinearIsometryEquiv.apply_symm_apply]

theorem cjV_RPV (i : Fin 3) (σ : L2V) : cjV (mirrorPV.R i σ) = mirrorPV.R i (cjV σ) := by
  ext k a
  change conjVec ((-vecSgn i) (σ (Box.refl i (-k)))) a = (-vecSgn i) (cjV σ (Box.refl i k)) a
  simp only [_root_.neg_apply, conjVec_apply, PiLp.neg_apply, vecSgn_apply,
    cjV_apply, refl_neg', _root_.map_neg, _root_.map_mul, Complex.conj_ofReal]

theorem cjV_avgPV (σ : L2V) : cjV (mirrorPV.avg σ) = mirrorPV.avg (cjV σ) := by
  simp only [Refl3.avg_apply, Refl3.half_apply, _root_.map_smul, _root_.map_add, cjV_RPV]

theorem reV_avgPV (σ : L2V) : reV (mirrorPV.avg σ) = mirrorPV.avg (reV σ) := by
  rw [reV_apply, reV_apply, _root_.map_smul, _root_.map_add, cjV_avgPV]

/-- The projection onto the real pseudo-vector mirror fields. -/
def Ppv : L2V →L[ℝ] L2V := reV ∘L mirrorPV.avg

theorem Ppv_apply (σ : L2V) : Ppv σ = reV (mirrorPV.avg σ) := rfl

theorem inner_Ppv (σ ρ : L2V) : ⟪Ppv σ, ρ⟫_ℝ = ⟪σ, Ppv ρ⟫_ℝ := by
  rw [Ppv_apply, Ppv_apply, inner_reV, mirrorPV.inner_avg, reV_avgPV]

theorem Ppv_mem_fix (σ : L2V) : Ppv σ ∈ mirrorPV.fix := by
  have h := mirrorPV.avg_mem σ
  have : cjV (mirrorPV.avg σ) ∈ mirrorPV.fix := fun i => by rw [← cjV_RPV, h i]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ h this)

/-- **The compression data of the pseudo-vector mirror class.** -/
def comprPV : Compr 8 (BoundedDomain.L2V Qr) L2V where
  J := Jpv
  R := resBV
  P := Ppv
  inner_J := inner_Jpv
  RJ := resBV_Jpv
  JRP z := Jpv_resBV (Ppv_mem_fix z) (isRealV_reV _)
  PJ u := by rw [Ppv_apply, mirrorPV.avg_of_mem (Jpv_mem_fix u), reV_of_real (isRealV_Jpv u)]
  P_sa := inner_Ppv

end PV

/-! ## Products and transport of compression data -/

section ProdTransport

variable {c : ℝ} {V' V M' M W2 : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup M'] [InnerProductSpace ℝ M']
  [NormedAddCommGroup M] [InnerProductSpace ℝ M] [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]

/-- A map of `L²` products, componentwise. -/
def prodL {X Y X' Y' : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [NormedAddCommGroup X']
    [InnerProductSpace ℝ X'] [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y']
    (f : X →L[ℝ] X') (g : Y →L[ℝ] Y') : WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X' × Y') :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ X' Y').symm.toContinuousLinearMap ∘L (f.prodMap g) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ X Y).toContinuousLinearMap

theorem prodL_apply {X Y X' Y' : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [NormedAddCommGroup X']
    [InnerProductSpace ℝ X'] [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y']
    (f : X →L[ℝ] X') (g : Y →L[ℝ] Y') (x : WithLp 2 (X × Y)) :
    prodL f g x = WithLp.toLp 2 (f (WithLp.ofLp x).1, g (WithLp.ofLp x).2) := rfl

/-- **Product of compression data.** -/
def Compr.prod (A : Compr c V' V) (B : Compr c M' M) :
    Compr c (WithLp 2 (V' × M')) (WithLp 2 (V × M)) where
  J := prodL A.J B.J
  R := prodL A.R B.R
  P := prodL A.P B.P
  inner_J x y := by
    simp only [prodL_apply, WithLp.prod_inner_apply, A.inner_J, B.inner_J]
    ring
  RJ x := by simp only [prodL_apply, A.RJ, B.RJ]
  JRP z := by simp only [prodL_apply, A.JRP, B.JRP]
  PJ x := by simp only [prodL_apply, A.PJ, B.PJ]
  P_sa z w := by
    simp only [prodL_apply, WithLp.prod_inner_apply, A.P_sa, B.P_sa]

/-- **Transport of compression data along an isometric equivalence of the target.** -/
def Compr.mapEquiv {W' W : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℝ W']
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (A : Compr c W' W) (e : W ≃ₗᵢ[ℝ] W2) :
    Compr c W' W2 where
  J := e.toContinuousLinearEquiv.toContinuousLinearMap ∘L A.J
  R := A.R ∘L e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  P := e.toContinuousLinearEquiv.toContinuousLinearMap ∘L A.P ∘L
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  inner_J x y := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.inner_map_map, A.inner_J]
  RJ x := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply, A.RJ]
  JRP z := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
      A.JRP]
  PJ x := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply, A.PJ]
  P_sa z w := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [← e.symm.inner_map_map, LinearIsometryEquiv.symm_apply_apply, A.P_sa,
      ← e.inner_map_map, LinearIsometryEquiv.apply_symm_apply]

end ProdTransport

/-! ## The fibre identification `L2V × L2M ≃ ℓ²(ℤ³; ℂ³ × ℂ³ˣ³)` -/

section Pair

open Feec.Ch6.Whole (VM fstV sndM fstV_apply sndM_apply norm_sq_VM)

/-- A bounded fibre map acting on `ℓ²(ℤ³)`. -/
def clmL2 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (B : E →L[ℝ] F) : L2 Z3 E →L[ℝ] L2 Z3 F :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun k => B (u k), memℓp_clm B u⟩
      map_add' := fun u v => lp.ext (funext fun k => by
        change B ((u + v : L2 Z3 E) k) = B (u k) + B (v k)
        rw [lp.coeFn_add, Pi.add_apply, _root_.map_add])
      map_smul' := fun r u => lp.ext (funext fun k => by
        change B ((r • u : L2 Z3 E) k) = r • B (u k)
        rw [lp.coeFn_smul, Pi.smul_apply, _root_.map_smul]) }
    ‖B‖ fun u => by
      refine lp.norm_le_of_forall_sum_le (by norm_num) (by positivity) fun s => ?_
      have h2 : (2 : ENNReal).toReal = 2 := by norm_num
      simp only [h2, Real.rpow_two]
      have hs := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) u s
      simp only [h2, Real.rpow_two] at hs
      calc ∑ k ∈ s, ‖B (u k)‖ ^ 2 ≤ ∑ k ∈ s, ‖B‖ ^ 2 * ‖u k‖ ^ 2 :=
            Finset.sum_le_sum fun k _ => by
              rw [← mul_pow]
              exact pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm _) 2
        _ = ‖B‖ ^ 2 * ∑ k ∈ s, ‖u k‖ ^ 2 := by rw [Finset.mul_sum]
        _ ≤ ‖B‖ ^ 2 * ‖u‖ ^ 2 := by gcongr
        _ = (‖B‖ * ‖u‖) ^ 2 := by ring

theorem clmL2_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (B : E →L[ℝ] F) (u : L2 Z3 E) (k : Z3) : clmL2 B u k = B (u k) := rfl

theorem memℓp_pair (x : WithLp 2 (L2V × L2M)) :
    Memℓp (fun k => (WithLp.toLp 2 (((WithLp.ofLp x).1 : L2V) k, ((WithLp.ofLp x).2 : L2M) k) :
      VM)) 2 := by
  rw [memℓp_two_iff]
  simp only [norm_sq_VM]
  exact (memℓp_two_iff.1 (lp.memℓp (WithLp.ofLp x).1)).add
    (memℓp_two_iff.1 (lp.memℓp (WithLp.ofLp x).2))

/-- **The pairing `L2V × L2M ≃ₗᵢ ℓ²(ℤ³; ℂ³ × ℂ³ˣ³)`**, `(v, B) ↦ (k ↦ (v_k, B_k))`. -/
def eW : WithLp 2 (L2V × L2M) ≃ₗᵢ[ℝ] Feec.Repair.C417.L2WT where
  toFun x := ⟨_, memℓp_pair x⟩
  invFun ρ := WithLp.toLp 2 (clmL2 fstV ρ, clmL2 sndM ρ)
  map_add' x y := lp.ext (funext fun k => by
    change WithLp.toLp 2 (((WithLp.ofLp (x + y)).1 : L2V) k, ((WithLp.ofLp (x + y)).2 : L2M) k) =
      WithLp.toLp 2 (((WithLp.ofLp x).1 : L2V) k, ((WithLp.ofLp x).2 : L2M) k) +
      WithLp.toLp 2 (((WithLp.ofLp y).1 : L2V) k, ((WithLp.ofLp y).2 : L2M) k)
    simp only [WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, lp.coeFn_add, Pi.add_apply]
    rfl)
  map_smul' r x := lp.ext (funext fun k => by
    change WithLp.toLp 2 (((WithLp.ofLp (r • x)).1 : L2V) k, ((WithLp.ofLp (r • x)).2 : L2M) k) =
      r • WithLp.toLp 2 (((WithLp.ofLp x).1 : L2V) k, ((WithLp.ofLp x).2 : L2M) k)
    simp only [WithLp.ofLp_smul, Prod.smul_fst, Prod.smul_snd, lp.coeFn_smul, Pi.smul_apply]
    rfl)
  left_inv x := by
    apply WithLp.ofLp_injective
    ext k <;> rfl
  right_inv ρ := lp.ext (funext fun k => by
    change WithLp.toLp 2 (fstV (ρ k), sndM (ρ k)) = ρ k
    rfl)
  norm_map' x := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    have h1 := memℓp_two_iff.1 (lp.memℓp x.fst)
    have h2 := memℓp_two_iff.1 (lp.memℓp x.snd)
    rw [norm_sq_L2, WithLp.prod_norm_sq_eq_of_L2, norm_sq_L2, norm_sq_L2, ← h1.tsum_add h2]
    refine tsum_congr fun k => ?_
    exact norm_sq_VM _

theorem eW_apply (x : WithLp 2 (L2V × L2M)) (k : Z3) :
    eW x k = WithLp.toLp 2 (((WithLp.ofLp x).1 : L2V) k, ((WithLp.ofLp x).2 : L2M) k) := rfl

theorem eW_symm_apply (ρ : Feec.Repair.C417.L2WT) :
    eW.symm ρ = WithLp.toLp 2 (clmL2 fstV ρ, clmL2 sndM ρ) := rfl

/-- `eW (0, B) = (0, B)` in the sense of `embBT`. -/
theorem eW_zero_left (B : L2M) : eW (WithLp.toLp 2 (0, B)) = embBT B :=
  lp.ext (funext fun k => by rw [eW_apply, embBT_apply, Feec.Ch6.Whole.inrM_apply]; rfl)

end Pair

/-! ## The compression data of the Ch. 6 target `L²(V) × L²(M)` -/

section BggData

open Feec.Ch6.Whole (VM hessSym bggSym skwSym bggSym_apply hessSym_apply skwSym_apply fstV sndM
  norm_snd_le)

/-- **The compression data of `L²(Q; ℝ³) × L²(Q; ℝ³ˣ³)`**: pseudo-vectors `M` and
pseudo-tensors `B`, identified with `ℓ²(ℤ³; ℂ³ × ℂ³ˣ³)`. -/
def comprW : Compr 8 (WithLp 2 (BoundedDomain.L2V Qr × BoundedDomain.L2M Qr)) L2WT :=
  (comprPV.prod (comprM (-1) neg_one_mul_neg_one)).mapEquiv eW

theorem comprW_J (w : WithLp 2 (BoundedDomain.L2V Qr × BoundedDomain.L2M Qr)) :
    comprW.J w = eW (WithLp.toLp 2 (Jpv (WithLp.ofLp w).1,
      Jm (-1) neg_one_mul_neg_one (WithLp.ofLp w).2)) := rfl

theorem comprW_P_eW (v : L2V) (B : L2M) :
    comprW.P (eW (WithLp.toLp 2 (v, B))) = eW (WithLp.toLp 2 (Ppv v, Pm (-1) neg_one_mul_neg_one B)) := by
  change eW (prodL Ppv (Pm (-1) neg_one_mul_neg_one) (eW.symm (eW (WithLp.toLp 2 (v, B))))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, prodL_apply]

theorem comprW_R_eW (v : L2V) (B : L2M) :
    comprW.R (eW (WithLp.toLp 2 (v, B))) = WithLp.toLp 2 (resBV v, resB B) := by
  change prodL resBV resB (eW.symm (eW (WithLp.toLp 2 (v, B)))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, prodL_apply]

/-- The pointwise skew part `S₁ = 2 vskw` on `𝕋³`. -/
def skwT : L2M →L[ℝ] L2V := clmL2 skwSym

theorem skwSym_matSgn (i : Fin 3) (M : Mat3) : skwSym (matSgn 1 i M) = -vecSgn i (skwSym M) := by
  ext c
  simp only [skwSym_apply, matSgn_apply, PiLp.neg_apply, vecSgn_apply]
  fin_cases i <;> fin_cases c <;> simp [sgn] <;> ring

theorem skwSym_conjM (M : Mat3) : skwSym (conjM M) = conjVec (skwSym M) := by
  ext c; simp [skwSym_apply, conjM_apply]

theorem skwT_R (i : Fin 3) (A : L2M) :
    skwT ((mirrorM 1 one_mul_one).R i A) = mirrorPV.R i (skwT A) :=
  lp.ext (funext fun _ => skwSym_matSgn i _)

theorem skwT_cjM (A : L2M) : skwT (cjM A) = cjV (skwT A) :=
  lp.ext (funext fun _ => skwSym_conjM _)

theorem skwT_Pm (A : L2M) : skwT (Pm 1 one_mul_one A) = Ppv (skwT A) := by
  have hav : skwT ((mirrorM 1 one_mul_one).avg A) = mirrorPV.avg (skwT A) := by
    simp only [Refl3.avg_apply, Refl3.half_apply, _root_.map_smul, _root_.map_add, skwT_R]
  rw [Pm_apply, Ppv_apply, reM_apply, reV_apply, _root_.map_smul, _root_.map_add, skwT_cjM, hav,
    cjV_avgPV]

/-- `D((S₁, curl)) = H(curl)` on `𝕋³`, and `(S₁, curl) z = (S₁ z, curl z)`. -/
theorem bggT_domain_iff {z : L2M} : z ∈ bggT.domain ↔ z ∈ Hcurl := by
  constructor
  · intro h
    change Memℓp (fun k => curlSym (freq k) (z k)) 2
    refine Memℓp.mono' (h : Memℓp (fun k => bggSym (freq k) (z k)) 2) fun k => ?_
    have := norm_snd_le (bggSym (freq k) ((z : L2M) k))
    rw [bggSym_apply, WithLp.ofLp_toLp] at this
    dsimp only at this ⊢
    rw [bggSym_apply]
    exact this
  · intro h
    change Memℓp (fun k => bggSym (freq k) (z k)) 2
    have e : (fun k => bggSym (freq k) (z k)) =
        ⇑(eW (WithLp.toLp 2 (skwT z, curlT ⟨z, h⟩))) := funext fun k => by
      rw [eW_apply, bggSym_apply, WithLp.ofLp_toLp, skwT, clmL2_apply]
      rfl
    rw [e]; exact lp.memℓp _

theorem bggT_eq (z : bggT.domain) :
    bggT z = eW (WithLp.toLp 2 (skwT z, curlT ⟨z, bggT_domain_iff.1 z.2⟩)) :=
  lp.ext (funext fun k => by
    change bggSym (freq k) ((z : L2M) k) = _
    rw [eW_apply, bggSym_apply, WithLp.ofLp_toLp, skwT, clmL2_apply]
    rfl)

theorem hessSym_mirror (i : Fin 3) (k : Z3) (c : ℂ) :
    hessSym (freq (Box.refl i k)) (mirrorRf.R i c) = (mirrorMf 1 one_mul_one).R i
      (hessSym (freq k) c) := by
  ext ⟨a, b⟩
  change hessSym _ c (a, b) = matSgn 1 i (hessSym (freq k) c) (a, b)
  simp only [hessSym_apply, matSgn_apply, freq_refl_eq_sgn]
  push_cast; ring

theorem intertwines_hessTT : Intertwines mirrorR (mirrorM 1 one_mul_one) hessTT :=
  intertwines_mulOp mirrorRf (mirrorMf 1 one_mul_one) (fun k => hessSym (freq k))
    fun i k c => hessSym_mirror i k c

theorem hessSym_conj (k : Z3) (c : ℂ) :
    hessSym (freq k) (conj c) = conjM (hessSym (freq (-k)) c) := by
  ext ⟨a, b⟩
  simp only [hessSym_apply, conjM_apply, freq_neg, PiLp.neg_apply, _root_.map_neg,
    _root_.map_mul, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

/-- `P` commutes with `grad grad` on `𝕋³` (even scalars to tensors). -/
theorem comprComm_hessTT : ComprComm bggTorus.d0 comprR (comprM 1 one_mul_one) := by
  have hav : CommOp bggTorus.d0 (mirrorR.avg : L2RT →ₗ[ℝ] L2RT)
      ((mirrorM 1 one_mul_one).avg : L2M →ₗ[ℝ] L2M) := fun z => intertwines_hessTT.avg z
  have hcj : CommOp bggTorus.d0 (reflRc : L2RT →ₗ[ℝ] L2RT) (cjM : L2M →ₗ[ℝ] L2M) := fun z => by
    have e : (fun k => hessSym (freq k) (reflRc (z : L2RT) k)) = ⇑(cjM (hessTT z)) := by
      funext k
      rw [reflRc_apply, hessSym_conj, cjM_apply]
      rfl
    have h : reflRc (z : L2RT) ∈ hessTT.domain := by
      change Memℓp _ 2; rw [e]; exact lp.memℓp _
    exact ⟨h, lp.ext e⟩
  exact hcj.half.comp hav

/-- `P` commutes with `(S₁, curl)` on `𝕋³`. -/
theorem comprComm_bggT : ComprComm bggTorus.d1 (comprM 1 one_mul_one) comprW := by
  intro z
  have hz : (z : L2M) ∈ Hcurl := bggT_domain_iff.1 z.2
  obtain ⟨h, e⟩ := comprComm_curl ⟨z, hz⟩
  have hP : (comprM 1 one_mul_one).P z ∈ bggT.domain := bggT_domain_iff.2 h
  refine ⟨hP, ?_⟩
  change bggT ⟨_, hP⟩ = comprW.P (bggT z)
  rw [bggT_eq, bggT_eq z, comprW_P_eW]
  refine congrArg (fun p => eW (WithLp.toLp 2 p)) (Prod.ext ?_ ?_)
  · exact skwT_Pm z
  · exact (lpmap_congr' curlT _ h rfl).trans e

/-- `P_{TSDB}` commutes with `P`. -/
theorem starProjection_comprW (ρ : L2WT) :
    L2TSDBT.starProjection (comprW.P ρ) = comprW.P (L2TSDBT.starProjection ρ) :=
  starProjection_comm_of_selfAdj L2TSDBT comprW.P comprW.P_sa (fun ρ hρ => by
    obtain ⟨B, hB, rfl⟩ := mem_L2TSDBT_iff.1 hρ
    rw [← eW_zero_left, comprW_P_eW, _root_.map_zero, eW_zero_left]
    exact mem_L2TSDBT_iff.2 ⟨_, Pm_mem_L2TSD (-1) neg_one_mul_neg_one hB, rfl⟩) ρ

end BggData


/-! ## The Ch. 6 complex on `Q` and its verdict -/

section BggQ

open Feec.Ch6.Whole (VM bggSym skwSym bggSym_apply skwSym_apply)

/-- `L²(Q; ℝ³) × L²(Q; ℝ³ˣ³)`, the target of `(S₁, curl)` (as in `Feec.Ch6.Bounded`). -/
abbrev W2Q := Feec.Ch6.Bounded.W2B Qr

/-- **The BGG complex (5.1) on the box with tensorial mirror boundary conditions**,
`H²_N(Q) --grad grad--> H_{nτ}(curl, Q; ℝ³ˣ³) --(S₁, curl)--> L²(Q; ℝ³) × L²(Q; ℝ³ˣ³)`, the
compression of `bggTorus`. -/
def bggCxQ : HilbertComplex2 RQ MQ W2Q :=
  comprComplex bggTorus comprR (comprM 1 one_mul_one) comprW comprComm_hessTT comprComm_bggT

/-- The magnetic constraint space `{0} × TSDmB` (multiplier `M = 0`, `B` TSD with
`B_{nn} = 0`). -/
abbrev TSDBm : Submodule ℝ W2Q := L2TSDBT.comap (comprW.J : W2Q →ₗ[ℝ] L2WT)

theorem mem_TSDBm {w : W2Q} : w ∈ TSDBm ↔ (WithLp.ofLp w).1 = 0 ∧ (WithLp.ofLp w).2 ∈ TSDmB := by
  change comprW.J w ∈ L2TSDBT ↔ _
  rw [comprW_J]
  constructor
  · intro h
    have h' : ∀ k, (Jpv (WithLp.ofLp w).1 k = 0 ∧ Jm (-1) neg_one_mul_neg_one (WithLp.ofLp w).2 k ∈
        tsd (freq k)) := fun k => by
      have := Feec.Ch6.Whole.mem_tsdB.1 (h k)
      rwa [eW_apply, WithLp.ofLp_toLp] at this
    refine ⟨comprPV.J_injective ?_, fun k => (h' k).2⟩
    change Jpv (WithLp.ofLp w).1 = Jpv 0
    rw [_root_.map_zero]
    exact lp.ext (funext fun k => (h' k).1)
  · rintro ⟨h1, h2⟩ k
    rw [eW_apply, Feec.Ch6.Whole.mem_tsdB, WithLp.ofLp_toLp, h1, _root_.map_zero]
    exact ⟨rfl, h2 k⟩

/-- `(0, B)` with `B ∈ TSDmB` lies in `TSDBm`. -/
theorem zero_pair_mem_TSDBm {B : MQ} (hB : B ∈ TSDmB) : (WithLp.toLp 2 (0, B) : W2Q) ∈ TSDBm :=
  mem_TSDBm.2 ⟨rfl, hB⟩

/-- **`d1 u = (S₁ u, curl u)`**: the pointwise skew part `S₁ = 2 vskw` (`Feec.Ch6.Bounded.skwL`)
and the mirror curl of Prop 4.17 (the weak curl on `Q`). -/
theorem bggCxQ_d1_eq (u : bggCxQ.d1.domain) :
    ∃ h : (u : MQ) ∈ mirrorCxQ.d1.domain,
      bggCxQ.d1 u = WithLp.toLp 2 (Feec.Ch6.Bounded.skwL (u : MQ), mirrorCxQ.d1 ⟨u, h⟩) := by
  have hb : Jm 1 one_mul_one u ∈ bggT.domain := u.2
  have hc : Jm 1 one_mul_one u ∈ Hcurl := bggT_domain_iff.1 hb
  refine ⟨hc, ?_⟩
  change comprW.R (bggT ⟨_, hb⟩) = _
  rw [bggT_eq, comprW_R_eW]
  congr 2
  · ext1 i
    rw [Feec.Ch6.Bounded.skwL_apply, resBV_apply]
    have e : vectorFourier.symm (skwT (Jm 1 one_mul_one u)) i =
        ofCoeff (entry (i + 1, i + 2) (Jm 1 one_mul_one u)) -
          ofCoeff (entry (i + 2, i + 1) (Jm 1 one_mul_one u)) := by
      rw [vectorFourier_symm_apply, ← ofCoeff_sub]
      congr 1
    rw [e, _root_.map_sub]
    rw [← resB_apply, ← resB_apply, resB_Jm]

theorem eight_pos' : (0 : ℝ) < 8 := by norm_num

/-- **The projection hypothesis of the Ch. 6 system on `Q` with mirror conditions.** -/
theorem bggCxQ_projection_hyp :
    ∀ x ∈ bggCxQ.domL, projKc RQ TSDmE TSDBm x ∈ bggCxQ.domL :=
  (prop_4_17_hyps_compr (h0 := comprComm_hessTT) (h1 := comprComm_bggT) L2TSD L2TSDBT eight_pos'
    L2TSD_le_ker_bggT projKc_mem_domL_bggT bggT_mem_L2TSDBT adjoint_bggT_mem_L2TSD
    (starProjection_Pm 1 one_mul_one) starProjection_comprW).2.1

/-- **Ch. 6 on the box `Q` with tensorial mirror boundary conditions: TSD propagates.** For
`E₀ ∈ TSDmE`, `B₀ ∈ TSDmB` with `(σ, u, (M, B))(0) = (0, E₀, (0, B₀)) ∈ D(L)`, the Hodge wave
equation of the BGG complex (5.1) on `Q` has a strong solution on `[0, T]`, unique among strong
solutions, and for all `t ∈ [0, T]`: `σ(t) = 0`, `u(t) ∈ TSDmE ⊆ L²(TSD)(Q)` (the weakly imposed
symmetry holds strongly), `M(t) = 0` and `B(t) ∈ TSDmB ⊆ L²(TSD)(Q)` (in particular `B(t)` is
symmetric); `(u, (M, B))` solves (4.15).

Original claim: the Ch. 6 method with the §6.3 boundary conditions keeps TSD data TSD. Defect:
false on every bounded domain (`Feec.Ch6.Bounded.bggComplex_verdict`). Repair: mirror boundary
conditions (and the wall conditions on the constraint).

See [QuennevilleBelair2015, §6.1, §6.3]. -/
theorem bggCxQ_verdict (T : ℝ) {E₀ B₀ : MQ} (hE₀ : E₀ ∈ TSDmE) (hB₀ : B₀ ∈ TSDmB)
    (hD : ini RQ E₀ (WithLp.toLp 2 (0, B₀) : W2Q) ∈ bggCxQ.domL) :
    ∃ U : ℝ → Tot RQ MQ W2Q,
      IsStrongSolution (-bggCxQ.waveOp) T (ini RQ E₀ (WithLp.toLp 2 (0, B₀) : W2Q)) 0 U ∧
      (∀ U', IsStrongSolution (-bggCxQ.waveOp) T (ini RQ E₀ (WithLp.toLp 2 (0, B₀) : W2Q)) 0 U' →
        EqOn U' U (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, (tot RQ MQ W2Q (U t)).1 = 0 ∧ (tot RQ MQ W2Q (U t)).2.1 ∈ TSDmE ∧
        (WithLp.ofLp (tot RQ MQ W2Q (U t)).2.2).1 = 0 ∧
        (WithLp.ofLp (tot RQ MQ W2Q (U t)).2.2).2 ∈ TSDmB) ∧
      IsReducedSolution bggCxQ T E₀ (WithLp.toLp 2 (0, B₀) : W2Q)
        (fun t => (tot RQ MQ W2Q (U t)).2.1) (fun t => (tot RQ MQ W2Q (U t)).2.2) := by
  obtain ⟨U, hU, huniq, hK, hR⟩ := prop_4_17_compr_exists (h0 := comprComm_hessTT)
    (h1 := comprComm_bggT) L2TSD L2TSDBT eight_pos' L2TSD_le_ker_bggT projKc_mem_domL_bggT
    bggT_mem_L2TSDBT adjoint_bggT_mem_L2TSD (starProjection_Pm 1 one_mul_one)
    starProjection_comprW T hE₀ (zero_pair_mem_TSDBm hB₀) hD
  refine ⟨U, hU, huniq, fun t ht => ?_, hR⟩
  have hk := (mem_Kc (W0 := RQ) (S1 := TSDmE) (S2 := TSDBm)).1 (hK t ht)
  exact ⟨hk.1, hk.2.1, (mem_TSDBm.1 hk.2.2).1, (mem_TSDBm.1 hk.2.2).2⟩

/-- In the verdict, `u(t)` and `B(t)` are TSD on `Q` (symmetric, trace-free, divergence-free). -/
theorem bggCxQ_verdict_TSD {u B : MQ} (hu : u ∈ TSDmE) (hB : B ∈ TSDmB) :
    u ∈ BoundedDomain.TSD Qr ∧ B ∈ BoundedDomain.TSD Qr ∧ B ∈ BoundedSym.symL2 Qr :=
  ⟨TSDmE_le_TSD hu, TSDmB_le_TSD hB, (TSDmB_le_TSD hB).1⟩

/-- **`K* = K` for the Ch. 6 system on `Q` with mirror conditions.** -/
theorem bggCxQ_Kmax_eq (G : UnitaryGroupGenerator (-bggCxQ.waveOp)) :
    Kmax G (Kc RQ TSDmE TSDBm) = Kc RQ TSDmE TSDBm :=
  Kmax_compr_eq (h0 := comprComm_hessTT) (h1 := comprComm_bggT) L2TSD L2TSDBT eight_pos'
    L2TSD_le_ker_bggT projKc_mem_domL_bggT bggT_mem_L2TSDBT adjoint_bggT_mem_L2TSD
    (starProjection_Pm 1 one_mul_one) starProjection_comprW G

/-- The datum `(0, E₀, (0, 0))`, `E₀ = (2 cos(2π x₃) diag(1, -1, 0))|_Q`. -/
def cosStateB : Tot RQ MQ W2Q := ini RQ cosEQ 0

theorem cosStateB_mem_Kc : cosStateB ∈ Kc RQ TSDmE TSDBm := by
  rw [mem_Kc, cosStateB, tot_ini]
  exact ⟨rfl, cosEQ_mem_TSDmE, TSDBm.zero_mem⟩

theorem tot_totJ_cosStateB :
    tot L2RT L2M L2WT (totJ comprR (comprM 1 one_mul_one) comprW cosStateB) = (0, cosE, 0) := by
  rw [tot_totJ, cosStateB, tot_ini]
  simp only [_root_.map_zero]
  exact Prod.ext rfl (Prod.ext Jm_cosEQ rfl)

theorem cosE_mem_bggT_domain : cosE ∈ bggT.domain := bggT_domain_iff.2 cosE_mem_Hcurl

theorem cosStateB_mem_domL : cosStateB ∈ bggCxQ.domL := by
  rw [bggCxQ, mem_domL_compr_iff eight_pos', Constraints.mem_domL, tot_totJ_cosStateB]
  refine ⟨bggTorus.d0.domain.zero_mem, ⟨cosE_mem_bggT_domain, ?_⟩, bggTorus.d1†.domain.zero_mem⟩
  exact (LinearPMap.mem_ker_iff.1 (L2TSD_le_ker_bggT cosE_mem_L2TSD)).elim fun y hy => hy.1 ▸ y.2

theorem cosStateB_waveOp_ne : bggCxQ.waveOp ⟨cosStateB, cosStateB_mem_domL⟩ ≠ 0 := by
  intro h0
  have hi := totJ_waveOp (h0 := comprComm_hessTT) (h1 := comprComm_bggT) eight_pos' cosStateB
    cosStateB_mem_domL
  change totJ _ _ _ (bggCxQ.waveOp ⟨cosStateB, cosStateB_mem_domL⟩) = _ at hi
  rw [h0, _root_.map_zero] at hi
  have h3 := congrArg (fun y => (WithLp.ofLp ((tot L2RT L2M L2WT y).2.2 k0)).2) hi
  simp only [Constraints.tot_waveOp, _root_.map_zero, Prod.snd_zero, lp.coeFn_zero,
    Pi.zero_apply] at h3
  apply curlSym_cosE_ne
  have e : bggTorus.d1 (bggTorus.prV1 ⟨totJ comprR (comprM 1 one_mul_one) comprW cosStateB,
      (mem_domL_compr_iff (h0 := comprComm_hessTT) (h1 := comprComm_bggT) eight_pos' _).1
        cosStateB_mem_domL⟩) = bggT ⟨cosE, cosE_mem_bggT_domain⟩ :=
    lpmap_congr' _ _ _ (by simp [tot_totJ_cosStateB])
  rw [e, lp.coeFn_neg, Pi.neg_apply] at h3
  have h4 : -(curlSym (freq k0) (cosE k0)) = 0 := by
    have h5 : (WithLp.ofLp (-(bggSym (freq k0) (cosE k0)))).2 = (WithLp.ofLp (0 : VM)).2 :=
      h3.symm
    rw [bggSym_apply] at h5
    exact h5
  exact neg_eq_zero.1 h4

/-- **Non-stationary TSD data propagate for the Ch. 6 system on `Q` with mirror conditions**:
for every orthogonal group generated by `-L` of `bggCxQ`, the datum `(0, E₀, (0, 0))`,
`E₀ = (2 cos(2π x₃) diag(1, -1, 0))|_Q`, lies in `D(L) ∩ K*` and is not stationary. -/
theorem bggCxQ_exists_nonstationary (G : UnitaryGroupGenerator (-bggCxQ.waveOp)) :
    cosStateB ∈ bggCxQ.domL ∧ cosStateB ∈ Kmax G (Kc RQ TSDmE TSDBm) ∧
      ∃ t, G.S t cosStateB ≠ cosStateB := by
  refine ⟨cosStateB_mem_domL, by rw [bggCxQ_Kmax_eq]; exact cosStateB_mem_Kc, ?_⟩
  by_contra hs
  push Not at hs
  have hdom : cosStateB ∈ (-bggCxQ.waveOp).domain := cosStateB_mem_domL
  have hd := G.hasDerivAt_zero ⟨cosStateB, hdom⟩
  have hd2 : HasDerivAt (fun t => G.S t cosStateB) 0 0 :=
    (hasDerivAt_const (0 : ℝ) cosStateB).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => hs t)
  have h0 := hd.unique hd2
  rw [LinearPMap.neg_apply, neg_eq_zero] at h0
  exact cosStateB_waveOp_ne h0

end BggQ

end Feec.Repair.C417

