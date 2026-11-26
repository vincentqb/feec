module

public import Feec.Models.Cube.MirrorExt
public import Feec.Models.Cube.RowWiseIdent

/-!
# Real parity extensions on `Q = (0, ½)ᵈ` and their Fourier coefficients

The folding formula `∫_{𝕋ᵈ} (ext_c f) g = ∫_Q f · fold_c g` for continuous `g`
(`integral_extL2_mul`) and the real parity extension `JR` on the Fourier side, with
`⟪JR u, JR v⟫ = 2ᵈ ⟪u, v⟫` (`inner_JR`).
-/

open scoped InnerProductSpace ComplexConjugate ENNReal Topology
open Set MeasureTheory Filter UnitAddTorus Feec.Fourier.TorusWeak

@[expose] public noncomputable section

namespace Feec.Models.Cube.DeRhamIdent

open Geometry MirrorExt
open Feec.Fourier.Torus (flipAt flipAt_neg)
open RowWise (ofRealL reL coeFn_ofRealL coeFn_reL reL_ofRealL ofRealL_reL star_ofRealL
  inner_ofRealL)

/-- The normalised Haar measure on `ℝ/ℤ`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {d : Type*} [Fintype d]

theorem resQ_star (f : T2 d) : star (resQ f) = resQ (star f) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (resQ f), coeFn_resQ f, coeFn_resQ (star f),
    ae_Q_of_ae_boxSet (ae_restrict_of_ae (Lp.coeFn_star f))] with y h1 h2 h3 h4
  rw [h1, Pi.star_apply, h2, h3, h4]
  rfl

section Fold

variable [DecidableEq d]

/-! ### Signs -/

theorem sign_update (c : d → ℂ) (j : d) (ε : d → Bool) :
    sign (Function.update c j (-c j)) ε = (if ε j then -1 else 1) * sign c ε := by
  rw [sign, sign, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ (fun i => if ε i then c i else 1) (Finset.mem_univ j)]
  rw [show (∏ i ∈ Finset.univ.erase j,
      if ε i then Function.update c j (-c j) i else 1) =
      ∏ i ∈ Finset.univ.erase j, if ε i then c i else 1 from
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]]
  by_cases h : ε j <;> simp [h]

/-! ### Folding -/

/-- **The fold** `fold_c g (y) = Σ_ε sign_c(ε) g(R_ε (proj y))` of a function on `𝕋ᵈ`. -/
def fold (c : d → ℂ) (g : UnitAddTorus d → ℂ) (y : d → ℝ) : ℂ :=
  ∑ ε : d → Bool, sign c ε * g (reflB ε (proj y))

theorem fold_eq_zero_of_face {c : d → ℂ} (hc : ∀ j, c j * c j = 1) {j : d} (hcj : c j = -1)
    (g : UnitAddTorus d → ℂ) {y : d → ℝ} (hy : y j = 0 ∨ y j = 1 / 2) : fold c g y = 0 := by
  let e : (d → Bool) ≃ (d → Bool) :=
    { toFun := fun ε i => xor (ε i) (single j i)
      invFun := fun ε i => xor (ε i) (single j i)
      left_inv := fun ε => funext fun i => by simp
      right_inv := fun ε => funext fun i => by simp }
  have hS : fold c g y = ∑ ε : d → Bool, sign c (e ε) * g (reflB (e ε) (proj y)) :=
    (Equiv.sum_comp e fun ε => sign c ε * g (reflB ε (proj y))).symm
  have hterm : ∀ ε : d → Bool, sign c (e ε) * g (reflB (e ε) (proj y)) =
      -(sign c ε * g (reflB ε (proj y))) := fun ε => by
    change sign c (fun i => xor (ε i) (single j i)) *
      g (reflB (fun i => xor (ε i) (single j i)) (proj y)) = _
    rw [sign_xor hc, sign_single, hcj, ← reflB_comp, reflB_single_proj_of_face hy]
    ring
  simp only [hterm, Finset.sum_neg_distrib] at hS
  rw [fold] at hS ⊢
  linear_combination hS / 2

theorem fold_eq (c : d → ℂ) (g : UnitAddTorus d → ℂ) :
    fold c g = fun y => ∑ ε : d → Bool, sign c ε * ((fun x => g (reflB ε x)) ∘ proj) y := rfl

theorem contDiff_fold (c : d → ℂ) {g : UnitAddTorus d → ℂ} (hg : IsSmooth g) :
    ContDiff ℝ (⊤ : ℕ∞) (fold c g) := by
  rw [fold_eq]
  exact ContDiff.sum fun ε _ => contDiff_const.mul (isSmooth_comp_reflB hg ε)

theorem continuous_fold (c : d → ℂ) {g : UnitAddTorus d → ℂ} (hg : Continuous g) :
    Continuous (fold c g) :=
  continuous_finsetSum _ fun ε _ => continuous_const.mul
    (hg.comp ((continuous_reflB ε).comp isOpenQuotientMap_proj.continuous))
where
  continuous_reflB (ε : d → Bool) : Continuous (reflB ε : UnitAddTorus d → UnitAddTorus d) :=
    continuous_pi fun i => by
      by_cases h : ε i
      · simp only [reflB, h, ↓reduceIte]; exact (continuous_apply i).neg
      · simp only [reflB, h, Bool.false_eq_true, ↓reduceIte]; exact continuous_apply i

theorem fderiv_fold (c : d → ℂ) {g : UnitAddTorus d → ℂ} (hg : IsSmooth g) (j : d)
    (y : d → ℝ) :
    fderiv ℝ (fold c g) y (Pi.single j 1) =
      fold (Function.update c j (-c j)) (partialT j g) y := by
  have hs : ∀ ε : d → Bool, ContDiff ℝ (⊤ : ℕ∞) ((fun x => g (reflB ε x)) ∘ proj) := fun ε =>
    isSmooth_comp_reflB hg ε
  have hd : ∀ ε : d → Bool, DifferentiableAt ℝ (fun y => sign c ε *
      ((fun x => g (reflB ε x)) ∘ proj) y) y := fun ε =>
    ((hs ε).differentiable (by simp) y).const_mul _
  rw [fold_eq, fderiv_fun_sum fun ε _ => hd ε]
  simp only [FunLike.coe_sum, Finset.sum_apply, fold]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [fderiv_const_mul ((hs ε).differentiable (by simp) y)]
  simp only [smul_apply, smul_eq_mul]
  rw [← partialT_proj ((hs ε).differentiable (by simp)),
    partialT_comp_reflB (hg.contDiff_one.differentiable one_ne_zero), sign_update]
  ring

theorem norm_fold_le {c : d → ℂ} (hc : ∀ j, c j * c j = 1) (g : C(UnitAddTorus d, ℂ))
    (y : d → ℝ) : ‖fold c g y‖ ≤ 2 ^ Fintype.card d * ‖g‖ := by
  calc ‖fold c g y‖ ≤ ∑ ε : d → Bool, ‖sign c ε * g (reflB ε (proj y))‖ := norm_sum_le _ _
    _ ≤ ∑ _ε : d → Bool, ‖g‖ := Finset.sum_le_sum fun ε _ => by
        rw [norm_mul, norm_sign hc, one_mul]; exact g.norm_coe_le_norm _
    _ = 2 ^ Fintype.card d * ‖g‖ := by
        simp [Finset.card_univ, Fintype.card_bool]

/-! ### The folding formula -/

theorem comp_reflB_ae_of_mem {c : d → ℂ} {f : T2 d} (hf : f ∈ paritySub c) (ε : d → Bool) :
    (fun x => (f : UnitAddTorus d → ℂ) (reflB ε x)) =ᵐ[volume]
      fun x => sign c ε * (f : UnitAddTorus d → ℂ) x := by
  set g : T2 d := Lp.compMeasurePreserving (reflB ε) (measurePreserving_reflB ε) f
  have hg : (g : UnitAddTorus d → ℂ) =ᵐ[volume] fun x => (f : UnitAddTorus d → ℂ) (reflB ε x) :=
    Lp.coeFn_compMeasurePreserving _ _
  have hsf : ((sign c ε • f : T2 d) : UnitAddTorus d → ℂ) =ᵐ[volume]
      fun x => sign c ε * (f : UnitAddTorus d → ℂ) x :=
    (Lp.coeFn_smul (sign c ε) f).mono fun x hx => by rw [hx]; rfl
  have hcf : ∀ {u v : UnitAddTorus d → ℂ}, u =ᵐ[volume] v → ∀ n,
      mFourierCoeff u n = mFourierCoeff v n := fun h n =>
    integral_congr_ae (h.mono fun x hx => by simp [hx])
  have e : g = sign c ε • f := eq_of_mFourierCoeff_eq fun n => by
    rw [hcf hg, mFourierCoeff_comp_reflB, mFourierCoeff_flipB hf, hcf hsf]
    simp only [mFourierCoeff, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1; funext x; ring
  have e' : (g : UnitAddTorus d → ℂ) = ((sign c ε • f : T2 d) : UnitAddTorus d → ℂ) := by rw [e]
  filter_upwards [hg, hsf] with x h1 h2
  rw [← h1, congrFun e' x, h2]

omit [DecidableEq d] in
theorem isFiniteMeasure_Q : IsFiniteMeasure (volume.restrict (Q d)) :=
  isFiniteMeasure_restrict.2 (isBounded_openCube _ _).measure_lt_top.ne

omit [DecidableEq d] in
theorem integrable_mul_bdd_Q (f : Domain.L2 ℂ (Q d)) {h : (d → ℝ) → ℂ} (hh : Continuous h)
    {C : ℝ} (hC : ∀ y, ‖h y‖ ≤ C) :
    Integrable (fun y => (f : (d → ℝ) → ℂ) y * h y) (volume.restrict (Q d)) := by
  have := isFiniteMeasure_Q (d := d)
  exact ((Lp.memLp f).integrable one_le_two).mul_bdd hh.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

/-- **The folding formula**: `∫_{𝕋ᵈ} (ext_c f) g = ∫_Q f · fold_c g` for continuous `g`. -/
theorem integral_extL2_mul {c : d → ℂ} (hc : ∀ j, c j * c j = 1) (f : Domain.L2 ℂ (Q d))
    {g : UnitAddTorus d → ℂ} (hg : Continuous g) :
    ∫ x, (extL2 hc f : UnitAddTorus d → ℂ) x * g x =
      ∫ y in Q d, (f : (d → ℝ) → ℂ) y * fold c g y := by
  set F := extL2 hc f
  have hF : F ∈ paritySub c := extL2_mem hc f
  have hint : Integrable fun x => (F : UnitAddTorus d → ℂ) x * g x := integrable_mul_continuous F hg
  rw [integral_eq_sum_box hint]
  set G : C(UnitAddTorus d, ℂ) := ⟨g, hg⟩
  have hrefl : ∀ ε : d → Bool, Continuous fun x => g (reflB ε x) := fun ε =>
    hg.comp (continuous_fold.continuous_reflB ε)
  have hbox : ∀ ε : d → Bool, ∫ x in boxSet d, (F : UnitAddTorus d → ℂ) (reflB ε x) *
      g (reflB ε x) = sign c ε * ∫ y in Q d, (f : (d → ℝ) → ℂ) y * g (reflB ε (proj y)) := by
    intro ε
    have h1 : ∫ x in boxSet d, (F : UnitAddTorus d → ℂ) (reflB ε x) * g (reflB ε x) =
        ∫ x in boxSet d, sign c ε * ((F : UnitAddTorus d → ℂ) x * g (reflB ε x)) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (comp_reflB_ae_of_mem hF ε)] with x hx
      rw [hx]; ring
    have hm : AEStronglyMeasurable (fun x => sign c ε * ((F : UnitAddTorus d → ℂ) x *
        g (reflB ε x))) (volume.restrict (boxSet d)) :=
      (aestronglyMeasurable_const.mul ((Lp.aestronglyMeasurable F).mul
        (hrefl ε).aestronglyMeasurable)).restrict
    rw [h1, setIntegral_boxSet _ hm, integral_const_mul]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [coeFn_resQ F] with y hy
    rw [← hy, show resQ F = f from resQ_extL2 hc f]
  simp only [hbox]
  have hi : ∀ ε : d → Bool, Integrable (fun y => sign c ε * ((f : (d → ℝ) → ℂ) y *
      g (reflB ε (proj y)))) (volume.restrict (Q d)) := fun ε =>
    (integrable_mul_bdd_Q f ((hrefl ε).comp isOpenQuotientMap_proj.continuous)
      (C := ‖G‖) fun y => G.norm_coe_le_norm _).const_mul _
  calc ∑ ε : d → Bool, sign c ε * ∫ y in Q d, (f : (d → ℝ) → ℂ) y * g (reflB ε (proj y))
      = ∑ ε : d → Bool, ∫ y in Q d, sign c ε * ((f : (d → ℝ) → ℂ) y * g (reflB ε (proj y))) :=
        Finset.sum_congr rfl fun ε _ => (integral_const_mul _ _).symm
    _ = ∫ y in Q d, ∑ ε : d → Bool, sign c ε * ((f : (d → ℝ) → ℂ) y *
        g (reflB ε (proj y))) := (integral_finsetSum _ fun ε _ => hi ε).symm
    _ = _ := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [fold, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ε _ => by ring

/-- **Fourier coefficients of an extension**: `(ext_c f)^(n) = ∫_Q f · fold_c e_{-n}`. -/
theorem mFourierCoeff_extL2 {c : d → ℂ} (hc : ∀ j, c j * c j = 1) (f : Domain.L2 ℂ (Q d))
    (n : d → ℤ) :
    mFourierCoeff (extL2 hc f : UnitAddTorus d → ℂ) n =
      ∫ y in Q d, (f : (d → ℝ) → ℂ) y * fold c (mFourier (-n)) y := by
  rw [← integral_extL2_mul hc f (mFourier (-n)).continuous]
  simp only [mFourierCoeff, smul_eq_mul]
  congr 1; funext x; ring

/-! ### Conjugation -/

theorem star_extL2 {c : d → ℂ} (hc : ∀ j, c j * c j = 1) (hcr : ∀ j, conj (c j) = c j)
    (f : Domain.L2 ℂ (Q d)) : star (extL2 hc f) = extL2 hc (star f) := by
  refine (eq_extL2_iff hc).2 ⟨mem_paritySub.2 fun k n => ?_, ?_⟩
  · have e : flipAt k (-n) = -flipAt k n := flipAt_neg k n
    rw [mFourierCoeff_star, mFourierCoeff_star, ← e,
      mem_paritySub.1 (extL2_mem hc f), map_mul, hcr]
  · rw [← resQ_star, resQ_extL2]

end Fold

/-! ### Real fields -/

section RealFields

variable {Ω : Set (d → ℝ)} {P : Type*} [Fintype P]

variable (Ω P) in
/-- Real fields as complex fields. -/
def ofRealF : Domain.L2F ℝ Ω P →L[ℝ] Domain.L2F ℂ Ω P where
  toFun f := WithLp.toLp 2 fun p => ofRealL _ (f p)
  map_add' f g := by ext p; simp
  map_smul' a f := by ext p; simp
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p =>
    (ofRealL _).continuous.comp (PiLp.continuous_apply 2 _ p))

omit [Fintype P] in
@[simp] theorem ofRealF_apply (f : Domain.L2F ℝ Ω P) (p : P) :
    ofRealF Ω P f p = ofRealL _ (f p) := rfl

variable (Ω P) in
/-- The real part of complex fields. -/
def reF : Domain.L2F ℂ Ω P →L[ℝ] Domain.L2F ℝ Ω P where
  toFun f := WithLp.toLp 2 fun p => reL _ (f p)
  map_add' f g := by ext p; simp
  map_smul' a f := PiLp.ext fun p => (reL _).map_smul_of_tower a (f p)
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p =>
    (reL _).continuous.comp (PiLp.continuous_apply 2 _ p))

omit [Fintype P] in
@[simp] theorem reF_apply (f : Domain.L2F ℂ Ω P) (p : P) : reF Ω P f p = reL _ (f p) := rfl

theorem inner_ofRealF (u v : Domain.L2F ℝ Ω P) :
    ⟪ofRealF Ω P u, ofRealF Ω P v⟫_ℂ = (⟪u, v⟫_ℝ : ℂ) := by
  rw [Domain.L2F.inner_def, Domain.L2F.inner_def]
  simp only [ofRealF_apply, inner_ofRealL]
  push_cast; rfl

variable (d P) in
/-- The restriction to `Q` of Fourier-side fields, real part. -/
def Jinv : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ)) →L[ℝ]
    Domain.L2F ℝ (Q d) P :=
  (reF (Q d) P).comp ((resQF.restrictScalars ℝ).comp
    ((ContinuousLinearEquiv.toContinuousLinearMap
      (Fourier.Torus.fieldFourier d P).symm.toContinuousLinearEquiv).restrictScalars ℝ))

theorem Jinv_apply (w : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ))) :
    Jinv d P w = reF (Q d) P (resQF ((Fourier.Torus.fieldFourier d P).symm w)) := rfl

/-- Coefficient sequences of real fields: `w(-n) = conj w(n)`. -/
def IsReal (w : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ))) : Prop :=
  ∀ n p, (w : (d → ℤ) → EuclideanSpace ℂ P) (-n) p = conj ((w : (d → ℤ) → EuclideanSpace ℂ P) n p)

theorem isReal_iff_star {w : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ))} :
    IsReal w ↔ ∀ p, star ((Fourier.Torus.fieldFourier d P).symm w p) =
      (Fourier.Torus.fieldFourier d P).symm w p := by
  simp only [star_eq_self_iff, coeff_fieldFourier_symm]
  exact ⟨fun h p n => h n p, fun h n p => h p n⟩

section Ext

variable [DecidableEq d] {c : P → d → ℂ} (hc : ∀ p j, c p j * c p j = 1)

/-- **The real parity extension on the Fourier side**, `(JR u)_p = (ext_{c p} u_p)^`. -/
def JR : Domain.L2F ℝ (Q d) P →L[ℝ]
    Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ)) :=
  ((extF hc).restrictScalars ℝ).comp (ofRealF (Q d) P)

theorem JR_apply (u : Domain.L2F ℝ (Q d) P) : JR hc u = extF hc (ofRealF (Q d) P u) := rfl

theorem Jinv_JR (u : Domain.L2F ℝ (Q d) P) : Jinv d P (JR hc u) = u := by
  rw [Jinv_apply, JR_apply, resQF_symm_extF]
  refine PiLp.ext fun p => ?_
  rw [reF_apply, ofRealF_apply, reL_ofRealL]

/-- **`JR` scales inner products by `2ᵈ`.** -/
theorem inner_JR (u v : Domain.L2F ℝ (Q d) P) :
    ⟪JR hc u, JR hc v⟫_ℝ = 2 ^ Fintype.card d * ⟪u, v⟫_ℝ := by
  rw [MeasureTheory.L2.real_inner_eq_re_inner EuclideanSpace.real_inner_eq_re_inner, JR_apply,
    JR_apply, inner_extF, inner_ofRealF, ← Complex.ofReal_mul]
  exact Complex.ofReal_re _

theorem coeff_JR (u : Domain.L2F ℝ (Q d) P) (n : d → ℤ) (p : P) :
    (JR hc u : (d → ℤ) → EuclideanSpace ℂ P) n p =
      ∫ y in Q d, (((u p : (d → ℝ) → ℝ) y : ℝ) : ℂ) * fold (c p) (mFourier (-n)) y := by
  rw [JR_apply, extF_coeff, ofRealF_apply, mFourierCoeff_extL2]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_ofRealL (u p)] with y hy
  rw [hy]

theorem JR_mem_fieldParity (u : Domain.L2F ℝ (Q d) P) : JR hc u ∈ fieldParity c :=
  extF_mem hc _

theorem JR_isReal (hcr : ∀ p j, conj (c p j) = c p j) (u : Domain.L2F ℝ (Q d) P) :
    IsReal (JR hc u) := by
  rw [isReal_iff_star]
  intro p
  rw [JR_apply, fieldFourier_symm_extF, extPi_apply, star_extL2 (hc p) (hcr p), ofRealF_apply,
    ← RowWise.cjL_eq_star]
  congr 1
  refine Lp.ext ?_
  filter_upwards [RowWise.coeFn_cjL (ofRealL (volume.restrict (Q d)) (u p)),
    coeFn_ofRealL (u p)] with y h1 h2
  rw [h1, h2, Complex.conj_ofReal]

/-- **Real parity sequences are extensions**: `JR (Jinv w) = w`. -/
theorem JR_Jinv {w : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ))}
    (hw : w ∈ fieldParity c) (hr : IsReal w) : JR hc (Jinv d P w) = w := by
  rw [Jinv_apply, JR_apply]
  have hs := isReal_iff_star.1 hr
  have e : ofRealF (Q d) P (reF (Q d) P (resQF ((Fourier.Torus.fieldFourier d P).symm w))) =
      resQF ((Fourier.Torus.fieldFourier d P).symm w) := by
    refine PiLp.ext fun p => ?_
    rw [ofRealF_apply, reF_apply, resQF_apply]
    exact ofRealL_reL (by rw [resQ_star, hs p])
  rw [e, extF_resQF hc hw]

end Ext

end RealFields

end Feec.Models.Cube.DeRhamIdent
