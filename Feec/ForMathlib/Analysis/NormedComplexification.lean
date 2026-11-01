module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# The complexification of a normed space

For a normed space `E` over `𝕜 = ℝ` or `ℂ`, the **complexification** `E_ℂ = E × E`
(`NormedComplexification 𝕜 E`, the pair `(x, y)` read as `x + i y`) is a complex normed space for
`(a + i b) (x, y) = (a x - b y, b x + a y)` and the norm

  `‖x + i y‖ = sup_{|w| = 1} ‖re (w (x + i y))‖ = sup_θ ‖cos θ x - sin θ y‖`,

the Taylor complexification norm ([MunozSarantopoulosTonge1999]). It is complete when `E` is,
and `‖x‖, ‖y‖ ≤ ‖x + i y‖ ≤ ‖x‖ + ‖y‖`. Only the real scalars of `𝕜` enter, so for `𝕜 = ℂ` this
is the complexification of the underlying real space. On inner product spaces, `Complexification`
(`Feec.ForMathlib.InnerProductSpace.Complexification`) carries instead the Hilbert norm
`(‖x‖² + ‖y‖²)^{1/2}`.

A bounded operator `T` of `E` acts componentwise, `T_ℂ (x, y) = (T x, T y)`
(`NormedComplexification.map`, a ring homomorphism `NormedComplexification.mapHom`), with
`‖T_ℂ‖ = ‖T‖` (`NormedComplexification.norm_map`); `T` is invertible when `T_ℂ` is
(`NormedComplexification.isUnit_of_isUnit_map`), and then `(T⁻¹)_ℂ = T_ℂ⁻¹`
(`NormedComplexification.map_ringInverse`). This is how statements about complex Banach spaces
(complex points of the spectrum) reach real ones.

## References

* [G. Muñoz, Y. Sarantopoulos, A. Tonge, *Complexifications of real Banach spaces, polynomials and multilinear maps*][MunozSarantopoulosTonge1999]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

/-- The **complexification** `E × E` of a vector space `E` over `𝕜 = ℝ` or `ℂ`, with the Taylor
norm: the pair `(x, y)` is `x + i y`, and `ℂ` acts through the real scalars of `𝕜`. -/
def NormedComplexification (_𝕜 E : Type*) : Type _ := E × E

namespace NormedComplexification

variable {𝕜 E : Type*}

/-- The vector `x + i y` of the complexification. -/
def mk (x y : E) : NormedComplexification 𝕜 E := (x, y)

/-- The real part `x` of `x + i y`. -/
def re (p : NormedComplexification 𝕜 E) : E := Prod.fst p

/-- The imaginary part `y` of `x + i y`. -/
def im (p : NormedComplexification 𝕜 E) : E := Prod.snd p

@[simp] theorem re_mk (x y : E) : (mk x y : NormedComplexification 𝕜 E).re = x := rfl

@[simp] theorem im_mk (x y : E) : (mk x y : NormedComplexification 𝕜 E).im = y := rfl

@[ext] theorem ext {p q : NormedComplexification 𝕜 E} (h₁ : p.re = q.re) (h₂ : p.im = q.im) :
    p = q :=
  Prod.ext h₁ h₂

section Module

variable [AddCommGroup E]

instance : AddCommGroup (NormedComplexification 𝕜 E) := inferInstanceAs (AddCommGroup (E × E))

@[simp] theorem re_add (p q : NormedComplexification 𝕜 E) : (p + q).re = p.re + q.re := rfl
@[simp] theorem im_add (p q : NormedComplexification 𝕜 E) : (p + q).im = p.im + q.im := rfl
@[simp] theorem re_zero : (0 : NormedComplexification 𝕜 E).re = 0 := rfl
@[simp] theorem im_zero : (0 : NormedComplexification 𝕜 E).im = 0 := rfl
@[simp] theorem re_neg (p : NormedComplexification 𝕜 E) : (-p).re = -p.re := rfl
@[simp] theorem im_neg (p : NormedComplexification 𝕜 E) : (-p).im = -p.im := rfl
@[simp] theorem re_sub (p q : NormedComplexification 𝕜 E) : (p - q).re = p.re - q.re := rfl
@[simp] theorem im_sub (p q : NormedComplexification 𝕜 E) : (p - q).im = p.im - q.im := rfl

variable [RCLike 𝕜] [Module 𝕜 E]

instance : SMul ℂ (NormedComplexification 𝕜 E) :=
  ⟨fun z p => mk ((z.re : 𝕜) • p.re - (z.im : 𝕜) • p.im) ((z.im : 𝕜) • p.re + (z.re : 𝕜) • p.im)⟩

@[simp] theorem re_smul (z : ℂ) (p : NormedComplexification 𝕜 E) :
    (z • p).re = (z.re : 𝕜) • p.re - (z.im : 𝕜) • p.im := rfl

@[simp] theorem im_smul (z : ℂ) (p : NormedComplexification 𝕜 E) :
    (z • p).im = (z.im : 𝕜) • p.re + (z.re : 𝕜) • p.im := rfl

instance : Module ℂ (NormedComplexification 𝕜 E) where
  one_smul p := by ext <;> simp
  mul_smul z w p := by
    ext <;> simp only [re_smul, im_smul, Complex.mul_re, Complex.mul_im, smul_sub, smul_add,
      smul_smul] <;> push_cast <;> module
  smul_zero z := by ext <;> simp
  smul_add z p q := by ext <;> simp only [re_smul, im_smul, re_add, im_add, smul_add] <;> abel
  add_smul z w p := by
    ext <;> simp only [re_smul, im_smul, re_add, im_add, Complex.add_re, Complex.add_im] <;>
      push_cast <;> module
  zero_smul p := by ext <;> simp

theorem re_ofReal_smul (a : ℝ) (p : NormedComplexification 𝕜 E) :
    ((a : ℂ) • p).re = (a : 𝕜) • p.re := by
  rw [re_smul, Complex.ofReal_re, Complex.ofReal_im, RCLike.ofReal_zero, zero_smul, sub_zero]

theorem im_ofReal_smul (a : ℝ) (p : NormedComplexification 𝕜 E) :
    ((a : ℂ) • p).im = (a : 𝕜) • p.im := by
  rw [im_smul, Complex.ofReal_re, Complex.ofReal_im, RCLike.ofReal_zero, zero_smul, zero_add]

end Module

/-! ### The Taylor norm -/

section Norm

variable [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The Taylor norm `‖x + i y‖ = sup_{|w| = 1} ‖re (w (x + i y))‖`. -/
instance : Norm (NormedComplexification 𝕜 E) := ⟨fun p => ⨆ w : Circle, ‖((w : ℂ) • p).re‖⟩

theorem norm_def (p : NormedComplexification 𝕜 E) : ‖p‖ = ⨆ w : Circle, ‖((w : ℂ) • p).re‖ :=
  rfl

theorem norm_re_smul_le_add (w : Circle) (p : NormedComplexification 𝕜 E) :
    ‖((w : ℂ) • p).re‖ ≤ ‖p.re‖ + ‖p.im‖ := by
  have h1 : |(w : ℂ).re| ≤ 1 := (Complex.abs_re_le_norm _).trans_eq w.norm_coe
  have h2 : |(w : ℂ).im| ≤ 1 := (Complex.abs_im_le_norm _).trans_eq w.norm_coe
  rw [re_smul]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, RCLike.norm_ofReal]
  exacts [mul_le_of_le_one_left (norm_nonneg _) h1, mul_le_of_le_one_left (norm_nonneg _) h2]

theorem bddAbove_norm_re_smul (p : NormedComplexification 𝕜 E) :
    BddAbove (Set.range fun w : Circle => ‖((w : ℂ) • p).re‖) :=
  ⟨_, Set.forall_mem_range.2 fun w => norm_re_smul_le_add w p⟩

theorem norm_re_smul_le (w : Circle) (p : NormedComplexification 𝕜 E) :
    ‖((w : ℂ) • p).re‖ ≤ ‖p‖ :=
  le_ciSup (bddAbove_norm_re_smul p) w

theorem norm_le_of_forall {p : NormedComplexification 𝕜 E} {C : ℝ}
    (h : ∀ w : Circle, ‖((w : ℂ) • p).re‖ ≤ C) : ‖p‖ ≤ C :=
  ciSup_le h

theorem norm_le_add (p : NormedComplexification 𝕜 E) : ‖p‖ ≤ ‖p.re‖ + ‖p.im‖ :=
  norm_le_of_forall fun w => norm_re_smul_le_add w p

theorem norm_re_le (p : NormedComplexification 𝕜 E) : ‖p.re‖ ≤ ‖p‖ := by
  simpa using norm_re_smul_le 1 p

/-- `-i` on the unit circle. -/
private def negI : Circle := ⟨-Complex.I, by simp [Submonoid.unitSphere]⟩

theorem norm_im_le (p : NormedComplexification 𝕜 E) : ‖p.im‖ ≤ ‖p‖ := by
  simpa [negI] using norm_re_smul_le negI p

@[simp] theorem norm_mk_zero (x : E) : ‖(mk x 0 : NormedComplexification 𝕜 E)‖ = ‖x‖ :=
  le_antisymm ((norm_le_add _).trans (by simp)) (norm_re_le (mk x 0))

private theorem norm_smul_le' (z : ℂ) (p : NormedComplexification 𝕜 E) :
    ‖z • p‖ ≤ ‖z‖ * ‖p‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · refine norm_le_of_forall fun w => ?_
    simp
  refine norm_le_of_forall fun w => ?_
  set u : Circle := ⟨(w : ℂ) * (z / ‖z‖), by
    simp [Submonoid.unitSphere, norm_ne_zero_iff.2 hz]⟩
  have hwz : (w : ℂ) * z = ((‖z‖ : ℝ) : ℂ) * (u : ℂ) := by
    change _ = _ * ((w : ℂ) * (z / ‖z‖))
    field_simp [norm_ne_zero_iff.2 hz]
  rw [smul_smul, hwz, mul_smul, re_ofReal_smul, norm_smul, RCLike.norm_ofReal, abs_norm]
  exact mul_le_mul_of_nonneg_left (norm_re_smul_le u p) (norm_nonneg _)

theorem normedSpaceCore : NormedSpace.Core ℂ (NormedComplexification 𝕜 E) where
  norm_nonneg p := (norm_nonneg p.re).trans (norm_re_le p)
  norm_smul z p := by
    refine le_antisymm (norm_smul_le' z p) ?_
    rcases eq_or_ne z 0 with rfl | hz
    · simp only [norm_zero, zero_mul]; exact (norm_nonneg ((0 : ℂ) • p).re).trans (norm_re_le _)
    calc ‖z‖ * ‖p‖ = ‖z‖ * ‖z⁻¹ • z • p‖ := by rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ ≤ ‖z‖ * (‖z⁻¹‖ * ‖z • p‖) := mul_le_mul_of_nonneg_left (norm_smul_le' _ _) (norm_nonneg _)
      _ = ‖z • p‖ := by rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hz), one_mul]
  norm_triangle p q := norm_le_of_forall fun w => by
    rw [smul_add, re_add]
    exact (norm_add_le _ _).trans (add_le_add (norm_re_smul_le w p) (norm_re_smul_le w q))
  norm_eq_zero_iff p := by
    constructor
    · intro h
      ext
      · exact norm_le_zero_iff.1 (h ▸ norm_re_le p)
      · exact norm_le_zero_iff.1 (h ▸ norm_im_le p)
    · rintro rfl
      exact le_antisymm ((norm_le_add _).trans (by simp)) (by simpa using norm_re_le (0 : NormedComplexification 𝕜 E))

instance : NormedAddCommGroup (NormedComplexification 𝕜 E) :=
  NormedAddCommGroup.ofCore normedSpaceCore

instance : NormedSpace ℂ (NormedComplexification 𝕜 E) := NormedSpace.ofCore normedSpaceCore

instance [CompleteSpace E] : CompleteSpace (NormedComplexification 𝕜 E) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hre : LipschitzWith 1 (re : NormedComplexification 𝕜 E → E) :=
    LipschitzWith.of_dist_le_mul fun p q => by
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← re_sub]; exact norm_re_le _
  have him : LipschitzWith 1 (im : NormedComplexification 𝕜 E → E) :=
    LipschitzWith.of_dist_le_mul fun p q => by
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← im_sub]; exact norm_im_le _
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (hre.uniformContinuous.comp_cauchySeq hu)
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (him.uniformContinuous.comp_cauchySeq hu)
  refine ⟨mk x y, tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_le_add _) ?_)⟩
  simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hx).add (tendsto_iff_norm_sub_tendsto_zero.1 hy)

/-- `x + i y` is jointly continuous in `x` and `y`. -/
theorem continuous_mk : Continuous fun q : E × E => (mk q.1 q.2 : NormedComplexification 𝕜 E) :=
  (LipschitzWith.of_dist_le_mul (K := 2) fun q q' => by
    rw [dist_eq_norm, dist_eq_norm]
    refine (norm_le_add _).trans ?_
    simp only [re_sub, im_sub, re_mk, im_mk, NNReal.coe_ofNat]
    have h1 : ‖q.1 - q'.1‖ ≤ ‖q - q'‖ := norm_fst_le (q - q')
    have h2 : ‖q.2 - q'.2‖ ≤ ‖q - q'‖ := norm_snd_le (q - q')
    linarith).continuous

/-- The real part as a real continuous linear map. -/
def reCLM [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] : NormedComplexification 𝕜 E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := re
      map_add' := re_add
      map_smul' := fun a p => by
        change ((a : ℂ) • p).re = a • p.re
        rw [re_ofReal_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜)] }
    1 fun p => by rw [one_mul]; exact norm_re_le p

/-- The imaginary part as a real continuous linear map. -/
def imCLM [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] : NormedComplexification 𝕜 E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := im
      map_add' := im_add
      map_smul' := fun a p => by
        change ((a : ℂ) • p).im = a • p.im
        rw [im_ofReal_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜)] }
    1 fun p => by rw [one_mul]; exact norm_im_le p

@[simp] theorem reCLM_apply [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    (p : NormedComplexification 𝕜 E) : reCLM p = p.re := rfl

@[simp] theorem imCLM_apply [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    (p : NormedComplexification 𝕜 E) : imCLM p = p.im := rfl

end Norm

/-! ### Complexification of operators -/

section Map

variable [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The **complexification** `T_ℂ (x + i y) = T x + i T y` of a bounded operator. -/
def map (T : E →L[𝕜] E) : NormedComplexification 𝕜 E →L[ℂ] NormedComplexification 𝕜 E :=
  LinearMap.mkContinuous
    { toFun := fun p => mk (T p.re) (T p.im)
      map_add' := fun p q => by ext <;> simp
      map_smul' := fun z p => by
        ext <;> simp only [re_mk, im_mk, re_smul, im_smul, map_sub, map_add, map_smul,
          RingHom.id_apply] }
    ‖T‖ fun p => norm_le_of_forall fun w => by
      have e : ((w : ℂ) • mk (T p.re) (T p.im) : NormedComplexification 𝕜 E).re =
          T (((w : ℂ) • p).re) := by simp
      change ‖((w : ℂ) • mk (T p.re) (T p.im) : NormedComplexification 𝕜 E).re‖ ≤ _
      rw [e]
      exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_re_smul_le w p) (norm_nonneg _))

@[simp] theorem re_map (T : E →L[𝕜] E) (p : NormedComplexification 𝕜 E) :
    (map T p).re = T p.re := rfl

@[simp] theorem im_map (T : E →L[𝕜] E) (p : NormedComplexification 𝕜 E) :
    (map T p).im = T p.im := rfl

theorem map_mk (T : E →L[𝕜] E) (x y : E) :
    map T (mk x y : NormedComplexification 𝕜 E) = mk (T x) (T y) := rfl

/-- The complexification of operators is a ring homomorphism. -/
def mapHom : (E →L[𝕜] E) →+* (NormedComplexification 𝕜 E →L[ℂ] NormedComplexification 𝕜 E) where
  toFun := map
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl
  map_zero' := by ext <;> rfl
  map_add' _ _ := by ext <;> rfl

@[simp] theorem mapHom_apply (T : E →L[𝕜] E) : mapHom T = map T := rfl

/-- Real scalars commute with complexification: `(a T)_ℂ = a T_ℂ`. -/
theorem map_ofReal_smul (a : ℝ) (T : E →L[𝕜] E) : map ((a : 𝕜) • T) = (a : ℂ) • map T := by
  ext p
  · change (a : 𝕜) • T p.re = ((a : ℂ) • map T p).re
    rw [re_ofReal_smul, re_map]
  · change (a : 𝕜) • T p.im = ((a : ℂ) • map T p).im
    rw [im_ofReal_smul, im_map]

/-- `‖T_ℂ‖ = ‖T‖`. -/
theorem norm_map (T : E →L[𝕜] E) : ‖map T‖ = ‖T‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _)
    (T.opNorm_le_bound (norm_nonneg _) fun x => ?_)
  rw [← norm_mk_zero (𝕜 := 𝕜) x]
  calc ‖T x‖ = ‖(map T (mk x 0)).re‖ := rfl
    _ ≤ ‖map T (mk x 0)‖ := norm_re_le _
    _ ≤ ‖map T‖ * ‖(mk x 0 : NormedComplexification 𝕜 E)‖ := (map T).le_opNorm _

/-- **An operator is invertible when its complexification is**: the inverse is
`x ↦ re (T_ℂ⁻¹ (x + i 0))`. -/
theorem isUnit_of_isUnit_map {T : E →L[𝕜] E} (h : IsUnit (map T)) : IsUnit T := by
  obtain ⟨u, hu⟩ := h
  have hl : ∀ p, u.inv (map T p) = p := fun p => by
    rw [← hu]; exact congrArg (fun C : NormedComplexification 𝕜 E →L[ℂ] _ => C p) u.inv_val
  have hr : ∀ p, map T (u.inv p) = p := fun p => by
    rw [← hu]; exact congrArg (fun C : NormedComplexification 𝕜 E →L[ℂ] _ => C p) u.val_inv
  let s : E → E := fun x => (u.inv (mk x 0)).re
  have hTs : ∀ x, T (s x) = x := fun x => by
    have := congrArg re (hr (mk x 0))
    rwa [re_map, re_mk] at this
  have hsT : ∀ x, s (T x) = x := fun x => by
    have e : map T (mk x 0) = (mk (T x) 0 : NormedComplexification 𝕜 E) := by
      ext <;> simp
    simp only [s, ← e, hl, re_mk]
  let S : E →L[𝕜] E := LinearMap.mkContinuous
    { toFun := s
      map_add' := fun x y => by conv_lhs => rw [← hTs x, ← hTs y, ← map_add, hsT]
      map_smul' := fun c x => by
        rw [RingHom.id_apply]; conv_lhs => rw [← hTs x, ← T.map_smul, hsT] }
    ‖u.inv‖ fun x => (norm_re_le _).trans ((u.inv.le_opNorm _).trans_eq (by rw [norm_mk_zero]))
  exact ⟨⟨T, S, ContinuousLinearMap.ext hTs, ContinuousLinearMap.ext hsT⟩, rfl⟩

/-- The complexification of the inverse is the inverse of the complexification. -/
theorem map_ringInverse {T : E →L[𝕜] E} (h : IsUnit T) :
    map (Ring.inverse T) = Ring.inverse (map T) := by
  obtain ⟨u, rfl⟩ := h
  rw [Ring.inverse_unit]
  exact (Ring.inverse_unit (Units.map (mapHom (𝕜 := 𝕜) (E := E)).toMonoidHom u)).symm

end Map

end NormedComplexification
