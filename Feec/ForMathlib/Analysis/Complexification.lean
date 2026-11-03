module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The complexification of a normed space

For a vector space `V` over `𝕜 = ℝ` or `ℂ`, the **complexification** `V_ℂ = V × V`
(`Complexification n 𝕜 V`, the pair `(x, y)` read as `x + i y`) is a complex vector space for
`(a + i b) (x, y) = (a x - b y, b x + a y)`. Only the real scalars of `𝕜` enter, so for `𝕜 = ℂ`
this is the complexification of the underlying real space.

The tag `n : ComplexificationNorm` selects the norm: the Taylor norm on normed spaces
(`NormedComplexification`, `Feec.ForMathlib.Analysis.NormedComplexification`) or the Hilbert norm
on inner product spaces (`Feec.ForMathlib.InnerProductSpace.Complexification`). Both are
`Complexification.NormCore`s: complex norms with `‖x + i 0‖ = ‖x‖`, `‖x‖ ≤ ‖x + i y‖` and
`‖T x + i T y‖ ≤ ‖T‖ ‖x + i y‖` for bounded operators `T`. Everything else is proved here once:
`‖y‖ ≤ ‖x + i y‖ ≤ ‖x‖ + ‖y‖`, completeness when `V` is complete, and for the complexification
`T_ℂ (x + i y) = T x + i T y` of a bounded operator (`Complexification.map`, a ring homomorphism
`Complexification.mapHom`):

* `Complexification.norm_map`: `‖T_ℂ‖ = ‖T‖`;
* `Complexification.map_aeval_map`: `p(T)_ℂ = p(T_ℂ)` for every real polynomial `p`;
* `Complexification.isUnit_of_isUnit_map`: `T` is invertible when `T_ℂ` is, and
  `Complexification.map_ringInverse`: then `(T⁻¹)_ℂ = T_ℂ⁻¹`.

This is how statements about complex spaces (complex points of the spectrum, von Neumann's
inequality) reach real ones.
-/

@[expose] public noncomputable section

open Polynomial

/-- The norm of a `Complexification`. -/
inductive ComplexificationNorm where
  /-- The Taylor norm `sup_θ ‖cos θ x - sin θ y‖`, on normed spaces. -/
  | taylor
  /-- The Hilbert norm `(‖x‖² + ‖y‖²)^{1/2}`, on inner product spaces. -/
  | hilbert

/-- The **complexification** `V × V` of a vector space `V` over `𝕜 = ℝ` or `ℂ`: the pair `(x, y)`
is `x + i y`, and `ℂ` acts through the real scalars of `𝕜`; `n` selects the norm. -/
def Complexification (_n : ComplexificationNorm) (_𝕜 V : Type*) : Type _ := V × V

namespace Complexification

variable {n : ComplexificationNorm} {𝕜 V : Type*}

/-- The vector `x + i y` of the complexification. -/
def mk (x y : V) : Complexification n 𝕜 V := (x, y)

/-- The real part `x` of `x + i y`. -/
def re (p : Complexification n 𝕜 V) : V := Prod.fst p

/-- The imaginary part `y` of `x + i y`. -/
def im (p : Complexification n 𝕜 V) : V := Prod.snd p

@[simp] theorem re_mk (x y : V) : (mk x y : Complexification n 𝕜 V).re = x := rfl

@[simp] theorem im_mk (x y : V) : (mk x y : Complexification n 𝕜 V).im = y := rfl

@[ext] theorem ext {p q : Complexification n 𝕜 V} (h₁ : p.re = q.re) (h₂ : p.im = q.im) :
    p = q :=
  Prod.ext h₁ h₂

section Module

variable [AddCommGroup V]

instance : AddCommGroup (Complexification n 𝕜 V) := inferInstanceAs (AddCommGroup (V × V))

@[simp] theorem re_add (p q : Complexification n 𝕜 V) : (p + q).re = p.re + q.re := rfl
@[simp] theorem im_add (p q : Complexification n 𝕜 V) : (p + q).im = p.im + q.im := rfl
@[simp] theorem re_zero : (0 : Complexification n 𝕜 V).re = 0 := rfl
@[simp] theorem im_zero : (0 : Complexification n 𝕜 V).im = 0 := rfl
@[simp] theorem re_neg (p : Complexification n 𝕜 V) : (-p).re = -p.re := rfl
@[simp] theorem im_neg (p : Complexification n 𝕜 V) : (-p).im = -p.im := rfl
@[simp] theorem re_sub (p q : Complexification n 𝕜 V) : (p - q).re = p.re - q.re := rfl
@[simp] theorem im_sub (p q : Complexification n 𝕜 V) : (p - q).im = p.im - q.im := rfl

variable [RCLike 𝕜] [Module 𝕜 V]

instance : SMul ℂ (Complexification n 𝕜 V) :=
  ⟨fun z p => mk ((z.re : 𝕜) • p.re - (z.im : 𝕜) • p.im) ((z.im : 𝕜) • p.re + (z.re : 𝕜) • p.im)⟩

@[simp] theorem re_smul (z : ℂ) (p : Complexification n 𝕜 V) :
    (z • p).re = (z.re : 𝕜) • p.re - (z.im : 𝕜) • p.im := rfl

@[simp] theorem im_smul (z : ℂ) (p : Complexification n 𝕜 V) :
    (z • p).im = (z.im : 𝕜) • p.re + (z.re : 𝕜) • p.im := rfl

instance : Module ℂ (Complexification n 𝕜 V) where
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

theorem re_ofReal_smul (a : ℝ) (p : Complexification n 𝕜 V) :
    ((a : ℂ) • p).re = (a : 𝕜) • p.re := by
  rw [re_smul, Complex.ofReal_re, Complex.ofReal_im, RCLike.ofReal_zero, zero_smul, sub_zero]

theorem im_ofReal_smul (a : ℝ) (p : Complexification n 𝕜 V) :
    ((a : ℂ) • p).im = (a : 𝕜) • p.im := by
  rw [im_smul, Complex.ofReal_re, Complex.ofReal_im, RCLike.ofReal_zero, zero_smul, zero_add]

end Module

/-! ### Complexification norms -/

/-- A **complexification norm**: a norm on `V_ℂ` with `‖z p‖ ≤ |z| ‖p‖`, `‖x + i 0‖ = ‖x‖`,
`‖x‖ ≤ ‖x + i y‖` and `‖T x + i T y‖ ≤ ‖T‖ ‖x + i y‖` for bounded operators `T`. -/
class NormCore (n : ComplexificationNorm) (𝕜 V : Type*) [RCLike 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] extends Norm (Complexification n 𝕜 V) where
  norm_add_le (p q : Complexification n 𝕜 V) : ‖p + q‖ ≤ ‖p‖ + ‖q‖
  norm_smul_le (z : ℂ) (p : Complexification n 𝕜 V) : ‖z • p‖ ≤ ‖z‖ * ‖p‖
  norm_re_le (p : Complexification n 𝕜 V) : ‖p.re‖ ≤ ‖p‖
  norm_mk_zero (x : V) : ‖(mk x 0 : Complexification n 𝕜 V)‖ = ‖x‖
  norm_mk_map_le (T : V →L[𝕜] V) (p : Complexification n 𝕜 V) :
    ‖(mk (T p.re) (T p.im) : Complexification n 𝕜 V)‖ ≤ ‖T‖ * ‖p‖

section Norm

variable [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormCore n 𝕜 V]

theorem norm_re_le (p : Complexification n 𝕜 V) : ‖p.re‖ ≤ ‖p‖ := NormCore.norm_re_le p

@[simp] theorem norm_mk_zero (x : V) : ‖(mk x 0 : Complexification n 𝕜 V)‖ = ‖x‖ :=
  NormCore.norm_mk_zero x

theorem norm_im_le (p : Complexification n 𝕜 V) : ‖p.im‖ ≤ ‖p‖ := by
  have h : (-Complex.I • p).re = p.im := by simp
  calc ‖p.im‖ = ‖(-Complex.I • p).re‖ := by rw [h]
    _ ≤ ‖-Complex.I • p‖ := norm_re_le _
    _ ≤ ‖p‖ := (NormCore.norm_smul_le _ p).trans_eq (by simp)

theorem norm_le_add (p : Complexification n 𝕜 V) : ‖p‖ ≤ ‖p.re‖ + ‖p.im‖ := by
  have h : p = mk p.re 0 + Complex.I • mk p.im 0 := by ext <;> simp
  calc ‖p‖ = ‖mk p.re 0 + Complex.I • (mk p.im 0 : Complexification n 𝕜 V)‖ := congrArg _ h
    _ ≤ ‖p.re‖ + ‖p.im‖ := (NormCore.norm_add_le _ _).trans (add_le_add (norm_mk_zero _).le
        ((NormCore.norm_smul_le _ _).trans_eq (by simp)))

theorem normedSpaceCore : NormedSpace.Core ℂ (Complexification n 𝕜 V) where
  norm_nonneg p := (norm_nonneg p.re).trans (norm_re_le p)
  norm_smul z p := by
    refine le_antisymm (NormCore.norm_smul_le z p) ?_
    rcases eq_or_ne z 0 with rfl | hz
    · rw [norm_zero, zero_mul]; exact (norm_nonneg ((0 : ℂ) • p).re).trans (norm_re_le _)
    calc ‖z‖ * ‖p‖ = ‖z‖ * ‖z⁻¹ • z • p‖ := by rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ ≤ ‖z‖ * (‖z⁻¹‖ * ‖z • p‖) :=
        mul_le_mul_of_nonneg_left (NormCore.norm_smul_le _ _) (norm_nonneg _)
      _ = ‖z • p‖ := by rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hz), one_mul]
  norm_triangle := NormCore.norm_add_le
  norm_eq_zero_iff p := by
    refine ⟨fun h => ext (norm_le_zero_iff.1 (h ▸ norm_re_le p))
      (norm_le_zero_iff.1 (h ▸ norm_im_le p)), ?_⟩
    rintro rfl
    exact le_antisymm ((norm_le_add _).trans (by simp))
      ((norm_nonneg (0 : Complexification n 𝕜 V).re).trans (norm_re_le _))

instance : NormedAddCommGroup (Complexification n 𝕜 V) :=
  NormedAddCommGroup.ofCore normedSpaceCore

instance : NormedSpace ℂ (Complexification n 𝕜 V) := NormedSpace.ofCore normedSpaceCore

instance [CompleteSpace V] : CompleteSpace (Complexification n 𝕜 V) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hre : LipschitzWith 1 (re : Complexification n 𝕜 V → V) :=
    LipschitzWith.of_dist_le_mul fun p q => by
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← re_sub]; exact norm_re_le _
  have him : LipschitzWith 1 (im : Complexification n 𝕜 V → V) :=
    LipschitzWith.of_dist_le_mul fun p q => by
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← im_sub]; exact norm_im_le _
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (hre.uniformContinuous.comp_cauchySeq hu)
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (him.uniformContinuous.comp_cauchySeq hu)
  refine ⟨mk x y, tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_le_add _) ?_)⟩
  simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hx).add (tendsto_iff_norm_sub_tendsto_zero.1 hy)

/-- `x + i y` is jointly continuous in `x` and `y`. -/
theorem continuous_mk : Continuous fun q : V × V => (mk q.1 q.2 : Complexification n 𝕜 V) :=
  (LipschitzWith.of_dist_le_mul (K := 2) fun q q' => by
    rw [dist_eq_norm, dist_eq_norm]
    refine (norm_le_add _).trans ?_
    simp only [re_sub, im_sub, re_mk, im_mk, NNReal.coe_ofNat]
    have h1 : ‖q.1 - q'.1‖ ≤ ‖q - q'‖ := norm_fst_le (q - q')
    have h2 : ‖q.2 - q'.2‖ ≤ ‖q - q'‖ := norm_snd_le (q - q')
    linarith).continuous

variable [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]

/-- The real part as a real continuous linear map. -/
def reCLM : Complexification n 𝕜 V →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := re
      map_add' := re_add
      map_smul' := fun a p => by
        change ((a : ℂ) • p).re = a • p.re
        rw [re_ofReal_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜)] }
    1 fun p => by rw [one_mul]; exact norm_re_le p

/-- The imaginary part as a real continuous linear map. -/
def imCLM : Complexification n 𝕜 V →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := im
      map_add' := im_add
      map_smul' := fun a p => by
        change ((a : ℂ) • p).im = a • p.im
        rw [im_ofReal_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜)] }
    1 fun p => by rw [one_mul]; exact norm_im_le p

/-- The embedding `x ↦ x + i 0` as a real continuous linear map. -/
def ofRealCLM : V →L[ℝ] Complexification n 𝕜 V :=
  LinearMap.mkContinuous
    { toFun := fun x => mk x 0
      map_add' := fun x y => by ext <;> simp
      map_smul' := fun a x => by
        change mk (a • x) 0 = ((a : ℂ) • mk x 0 : Complexification n 𝕜 V)
        ext
        · rw [re_ofReal_smul, re_mk, re_mk, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
        · rw [im_ofReal_smul, im_mk, im_mk, smul_zero] }
    1 fun x => by rw [one_mul]; exact (norm_mk_zero x).le

@[simp] theorem ofRealCLM_apply (x : V) : (ofRealCLM x : Complexification n 𝕜 V) = mk x 0 := rfl

@[simp] theorem reCLM_apply (p : Complexification n 𝕜 V) : reCLM p = p.re := rfl

@[simp] theorem imCLM_apply (p : Complexification n 𝕜 V) : imCLM p = p.im := rfl

end Norm

/-! ### Complexification of operators -/

section Map

variable [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormCore n 𝕜 V]

/-- The **complexification** `T_ℂ (x + i y) = T x + i T y` of a bounded operator. -/
def map (T : V →L[𝕜] V) : Complexification n 𝕜 V →L[ℂ] Complexification n 𝕜 V :=
  LinearMap.mkContinuous
    { toFun := fun p => mk (T p.re) (T p.im)
      map_add' := fun p q => by ext <;> simp
      map_smul' := fun z p => by
        ext <;> simp only [re_mk, im_mk, re_smul, im_smul, map_sub, map_add, map_smul,
          RingHom.id_apply] }
    ‖T‖ (NormCore.norm_mk_map_le T)

@[simp] theorem re_map (T : V →L[𝕜] V) (p : Complexification n 𝕜 V) :
    (map T p).re = T p.re := rfl

@[simp] theorem im_map (T : V →L[𝕜] V) (p : Complexification n 𝕜 V) :
    (map T p).im = T p.im := rfl

theorem map_mk (T : V →L[𝕜] V) (x y : V) :
    map T (mk x y : Complexification n 𝕜 V) = mk (T x) (T y) := rfl

/-- The complexification of operators is a ring homomorphism. -/
def mapHom : (V →L[𝕜] V) →+* (Complexification n 𝕜 V →L[ℂ] Complexification n 𝕜 V) where
  toFun := map
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl
  map_zero' := by ext <;> rfl
  map_add' _ _ := by ext <;> rfl

@[simp] theorem mapHom_apply (T : V →L[𝕜] V) : mapHom T = map (n := n) T := rfl

/-- Real scalars commute with complexification: `(a T)_ℂ = a T_ℂ`. -/
theorem map_ofReal_smul (a : ℝ) (T : V →L[𝕜] V) :
    map (n := n) ((a : 𝕜) • T) = (a : ℂ) • map T := by
  ext p
  · change (a : 𝕜) • T p.re = ((a : ℂ) • map T p).re
    rw [re_ofReal_smul, re_map]
  · change (a : 𝕜) • T p.im = ((a : ℂ) • map T p).im
    rw [im_ofReal_smul, im_map]

/-- **Real polynomials commute with complexification**: `p(T)_ℂ = p(T_ℂ)`. -/
theorem map_aeval_map (T : V →L[𝕜] V) (p : ℝ[X]) :
    map (n := n) (aeval T (p.map (algebraMap ℝ 𝕜))) = aeval (map T) (p.map (algebraMap ℝ ℂ)) := by
  rw [← mapHom_apply, aeval_def, eval₂_map, hom_eval₂, aeval_def, eval₂_map]
  congr 1
  refine RingHom.ext fun r => ContinuousLinearMap.ext fun q => ext ?_ ?_
  · change (r : 𝕜) • q.re = ((r : ℂ).re : 𝕜) • q.re - ((r : ℂ).im : 𝕜) • q.im
    simp
  · change (r : 𝕜) • q.im = ((r : ℂ).im : 𝕜) • q.re + ((r : ℂ).re : 𝕜) • q.im
    simp

/-- `‖T_ℂ‖ = ‖T‖`. -/
theorem norm_map (T : V →L[𝕜] V) : ‖map (n := n) T‖ = ‖T‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _)
    (T.opNorm_le_bound (norm_nonneg _) fun x => ?_)
  rw [← norm_mk_zero (n := n) (𝕜 := 𝕜) x]
  calc ‖T x‖ = ‖(map T (mk x 0 : Complexification n 𝕜 V)).re‖ := rfl
    _ ≤ ‖map T (mk x 0 : Complexification n 𝕜 V)‖ := norm_re_le _
    _ ≤ ‖map (n := n) T‖ * ‖(mk x 0 : Complexification n 𝕜 V)‖ := (map T).le_opNorm _

/-- **An operator is invertible when its complexification is**: the inverse is
`x ↦ re (T_ℂ⁻¹ (x + i 0))`. -/
theorem isUnit_of_isUnit_map {T : V →L[𝕜] V} (h : IsUnit (map (n := n) T)) : IsUnit T := by
  obtain ⟨u, hu⟩ := h
  have hl : ∀ p, u.inv (map T p) = p := fun p => by
    rw [← hu]; exact congrArg (fun C : Complexification n 𝕜 V →L[ℂ] _ => C p) u.inv_val
  have hr : ∀ p, map T (u.inv p) = p := fun p => by
    rw [← hu]; exact congrArg (fun C : Complexification n 𝕜 V →L[ℂ] _ => C p) u.val_inv
  let s : V → V := fun x => (u.inv (mk x 0)).re
  have hTs : ∀ x, T (s x) = x := fun x => by
    have := congrArg re (hr (mk x 0))
    rwa [re_map, re_mk] at this
  have hsT : ∀ x, s (T x) = x := fun x => by
    have e : map T (mk x 0) = (mk (T x) 0 : Complexification n 𝕜 V) := by
      ext <;> simp
    simp only [s, ← e, hl, re_mk]
  let S : V →L[𝕜] V := LinearMap.mkContinuous
    { toFun := s
      map_add' := fun x y => by conv_lhs => rw [← hTs x, ← hTs y, ← map_add, hsT]
      map_smul' := fun c x => by
        rw [RingHom.id_apply]; conv_lhs => rw [← hTs x, ← T.map_smul, hsT] }
    ‖u.inv‖ fun x => (norm_re_le _).trans ((u.inv.le_opNorm _).trans_eq (by rw [norm_mk_zero]))
  exact ⟨⟨T, S, ContinuousLinearMap.ext hTs, ContinuousLinearMap.ext hsT⟩, rfl⟩

/-- The complexification of the inverse is the inverse of the complexification. -/
theorem map_ringInverse {T : V →L[𝕜] V} (h : IsUnit T) :
    map (n := n) (Ring.inverse T) = Ring.inverse (map T) := by
  obtain ⟨u, rfl⟩ := h
  rw [Ring.inverse_unit]
  exact (Ring.inverse_unit (Units.map (mapHom (n := n) (𝕜 := 𝕜) (V := V)).toMonoidHom u)).symm

end Map

end Complexification
