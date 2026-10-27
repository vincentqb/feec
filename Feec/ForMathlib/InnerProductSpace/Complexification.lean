module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The complexification of an inner product space

For an inner product space `V` over `𝕜 = ℝ` or `ℂ`, the **complexification** `V_ℂ = V × V`
(`Complexification 𝕜 V`, the pair `(x, y)` read as `x + i y`) is a complex inner product space for
`(a + i b) (x, y) = (a x - b y, b x + a y)` and
`⟪(x, y), (x', y')⟫ = re ⟪x, x'⟫ + re ⟪y, y'⟫ + i (re ⟪x, y'⟫ - re ⟪y, x'⟫)`, so that
`‖(x, y)‖² = ‖x‖² + ‖y‖²` (`Complexification.norm_sq`); it is complete when `V` is. Only the real
scalars of `𝕜` enter, so for `𝕜 = ℂ` this is the complexification of the underlying real space.

A bounded operator `T` of `V` acts componentwise, `T_ℂ (x, y) = (T x, T y)`
(`ContinuousLinearMap.complexification`, a ring homomorphism `complexificationHom`), with:

* `norm_complexification`: `‖T_ℂ‖ = ‖T‖`;
* `re_inner_complexification`: `re ⟪T_ℂ (x, y), (x, y)⟫ = re ⟪T x, x⟫ + re ⟪T y, y⟫`, so `T_ℂ` is
  dissipative when `T` is;
* `complexification_aeval`: `p(T)_ℂ = p(T_ℂ)` for every real polynomial `p`;
* `isUnit_of_isUnit_complexification`: `T` is invertible when `T_ℂ` is, and
  `complexification_ringInverse`: then `(T⁻¹)_ℂ = T_ℂ⁻¹`.

This is how statements about complex Hilbert spaces (von Neumann's inequality,
`ContinuousLinearMap.norm_aeval_le_of_norm_le_one`) reach real ones.

## References

* [P. R. Halmos, *Finite-Dimensional Vector Spaces*][Halmos1974], §77 (complexification)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Polynomial

/-- The **complexification** `V × V` of a vector space `V` over `𝕜 = ℝ` or `ℂ`: the pair `(x, y)`
is `x + i y`, and `ℂ` acts through the real scalars of `𝕜`. -/
def Complexification (_𝕜 V : Type*) : Type _ := V × V

namespace Complexification

variable {𝕜 V : Type*}

/-- The vector `x + i y` of the complexification. -/
def mk (x y : V) : Complexification 𝕜 V := (x, y)

/-- The real part `x` of `x + i y`. -/
def re (p : Complexification 𝕜 V) : V := Prod.fst p

/-- The imaginary part `y` of `x + i y`. -/
def im (p : Complexification 𝕜 V) : V := Prod.snd p

@[simp] theorem re_mk (x y : V) : (mk x y : Complexification 𝕜 V).re = x := rfl

@[simp] theorem im_mk (x y : V) : (mk x y : Complexification 𝕜 V).im = y := rfl

@[ext] theorem ext {p q : Complexification 𝕜 V} (h₁ : p.re = q.re) (h₂ : p.im = q.im) : p = q :=
  Prod.ext h₁ h₂

section AddCommGroup

variable [AddCommGroup V]

instance : AddCommGroup (Complexification 𝕜 V) := inferInstanceAs (AddCommGroup (V × V))

@[simp] theorem re_add (p q : Complexification 𝕜 V) : (p + q).re = p.re + q.re := rfl
@[simp] theorem im_add (p q : Complexification 𝕜 V) : (p + q).im = p.im + q.im := rfl
@[simp] theorem re_zero : (0 : Complexification 𝕜 V).re = 0 := rfl
@[simp] theorem im_zero : (0 : Complexification 𝕜 V).im = 0 := rfl
@[simp] theorem re_neg (p : Complexification 𝕜 V) : (-p).re = -p.re := rfl
@[simp] theorem im_neg (p : Complexification 𝕜 V) : (-p).im = -p.im := rfl
@[simp] theorem re_sub (p q : Complexification 𝕜 V) : (p - q).re = p.re - q.re := rfl
@[simp] theorem im_sub (p q : Complexification 𝕜 V) : (p - q).im = p.im - q.im := rfl

end AddCommGroup

section Module

variable [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]

instance : SMul ℂ (Complexification 𝕜 V) :=
  ⟨fun z p => mk ((z.re : 𝕜) • p.re - (z.im : 𝕜) • p.im) ((z.im : 𝕜) • p.re + (z.re : 𝕜) • p.im)⟩

@[simp] theorem re_smul (z : ℂ) (p : Complexification 𝕜 V) :
    (z • p).re = (z.re : 𝕜) • p.re - (z.im : 𝕜) • p.im := rfl

@[simp] theorem im_smul (z : ℂ) (p : Complexification 𝕜 V) :
    (z • p).im = (z.im : 𝕜) • p.re + (z.re : 𝕜) • p.im := rfl

instance : Module ℂ (Complexification 𝕜 V) where
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

end Module

section Inner

variable [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

instance : InnerProductSpace.Core ℂ (Complexification 𝕜 V) where
  inner p q := ⟨RCLike.re ⟪p.re, q.re⟫_𝕜 + RCLike.re ⟪p.im, q.im⟫_𝕜,
    RCLike.re ⟪p.re, q.im⟫_𝕜 - RCLike.re ⟪p.im, q.re⟫_𝕜⟩
  conj_inner_symm p q := by
    apply Complex.ext
    · simp only [Complex.conj_re]
      rw [inner_re_symm (𝕜 := 𝕜) q.re, inner_re_symm (𝕜 := 𝕜) q.im]
    · simp only [Complex.conj_im]
      rw [inner_re_symm (𝕜 := 𝕜) q.re, inner_re_symm (𝕜 := 𝕜) q.im]
      ring
  re_inner_nonneg p := add_nonneg inner_self_nonneg inner_self_nonneg
  add_left p q r := by
    apply Complex.ext <;> simp only [re_add, im_add, inner_add_left, map_add, Complex.add_re,
      Complex.add_im] <;> ring
  smul_left p q z := by
    apply Complex.ext <;>
      simp only [re_smul, im_smul, inner_sub_left, inner_add_left, inner_smul_real_left, map_sub,
        map_add, RCLike.smul_re, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im] <;> ring
  definite p h := by
    have h1 := congrArg Complex.re h
    simp only [Complex.zero_re] at h1
    rw [inner_self_eq_norm_sq (𝕜 := 𝕜), inner_self_eq_norm_sq (𝕜 := 𝕜)] at h1
    have h2 : ‖p.re‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖p.re‖, sq_nonneg ‖p.im‖]
    have h3 : ‖p.im‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖p.re‖, sq_nonneg ‖p.im‖]
    ext
    · simpa using h2
    · simpa using h3

instance : NormedAddCommGroup (Complexification 𝕜 V) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (Complexification 𝕜 V) := InnerProductSpace.ofCore _

theorem re_inner (p q : Complexification 𝕜 V) :
    RCLike.re ⟪p, q⟫_ℂ = RCLike.re ⟪p.re, q.re⟫_𝕜 + RCLike.re ⟪p.im, q.im⟫_𝕜 := rfl

/-- `‖x + i y‖² = ‖x‖² + ‖y‖²`. -/
theorem norm_sq (p : Complexification 𝕜 V) : ‖p‖ ^ 2 = ‖p.re‖ ^ 2 + ‖p.im‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, re_inner, ← @norm_sq_eq_re_inner 𝕜, ← @norm_sq_eq_re_inner 𝕜]

theorem norm_re_le (p : Complexification 𝕜 V) : ‖p.re‖ ≤ ‖p‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by rw [norm_sq]; nlinarith [sq_nonneg ‖p.im‖])

theorem norm_im_le (p : Complexification 𝕜 V) : ‖p.im‖ ≤ ‖p‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by rw [norm_sq]; nlinarith [sq_nonneg ‖p.re‖])

theorem norm_le_add (p : Complexification 𝕜 V) : ‖p‖ ≤ ‖p.re‖ + ‖p.im‖ :=
  (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 (by
    rw [norm_sq]; nlinarith [norm_nonneg p.re, norm_nonneg p.im])

@[simp] theorem norm_mk_zero (x : V) : ‖(mk x 0 : Complexification 𝕜 V)‖ = ‖x‖ := by
  have := norm_sq (mk x 0 : Complexification 𝕜 V)
  simp only [re_mk, im_mk, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

instance [CompleteSpace V] : CompleteSpace (Complexification 𝕜 V) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hre : LipschitzWith 1 (re : Complexification 𝕜 V → V) :=
    LipschitzWith.of_dist_le_mul fun p q => by
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← re_sub]; exact norm_re_le _
  have him : LipschitzWith 1 (im : Complexification 𝕜 V → V) :=
    LipschitzWith.of_dist_le_mul fun p q => by
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← im_sub]; exact norm_im_le _
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (hre.uniformContinuous.comp_cauchySeq hu)
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (him.uniformContinuous.comp_cauchySeq hu)
  refine ⟨mk x y, tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_le_add _) ?_)⟩
  simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hx).add (tendsto_iff_norm_sub_tendsto_zero.1 hy)

end Inner

end Complexification

open Complexification

namespace ContinuousLinearMap

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The **complexification** `T_ℂ (x + i y) = T x + i T y` of a bounded operator. -/
def complexification (T : V →L[𝕜] V) : Complexification 𝕜 V →L[ℂ] Complexification 𝕜 V :=
  LinearMap.mkContinuous
    { toFun := fun p => Complexification.mk (T p.re) (T p.im)
      map_add' := fun p q => by ext <;> simp
      map_smul' := fun z p => by
        ext <;> simp only [re_mk, im_mk, re_smul, im_smul, map_sub, map_add, map_smul,
          RingHom.id_apply] }
    ‖T‖ fun p => (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 (by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [norm_sq, mul_pow, norm_sq, re_mk, im_mk]
      nlinarith [T.le_opNorm p.re, T.le_opNorm p.im, norm_nonneg (T p.re),
        norm_nonneg (T p.im), mul_nonneg (norm_nonneg T) (norm_nonneg p.re),
        mul_nonneg (norm_nonneg T) (norm_nonneg p.im)])

@[simp] theorem complexification_re (T : V →L[𝕜] V) (p : Complexification 𝕜 V) :
    (T.complexification p).re = T p.re := rfl

@[simp] theorem complexification_im (T : V →L[𝕜] V) (p : Complexification 𝕜 V) :
    (T.complexification p).im = T p.im := rfl

@[simp] theorem complexification_mul (S T : V →L[𝕜] V) :
    (S * T).complexification = S.complexification * T.complexification := rfl

/-- The complexification of operators is a ring homomorphism. -/
def complexificationHom :
    (V →L[𝕜] V) →+* (Complexification 𝕜 V →L[ℂ] Complexification 𝕜 V) where
  toFun := complexification
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl
  map_zero' := by ext <;> rfl
  map_add' _ _ := by ext <;> rfl

@[simp] theorem complexificationHom_apply (T : V →L[𝕜] V) :
    complexificationHom T = T.complexification := rfl

/-- `re ⟪T_ℂ (x + i y), x + i y⟫ = re ⟪T x, x⟫ + re ⟪T y, y⟫`. -/
theorem re_inner_complexification (T : V →L[𝕜] V) (p : Complexification 𝕜 V) :
    (⟪T.complexification p, p⟫_ℂ).re = RCLike.re ⟪T p.re, p.re⟫_𝕜 + RCLike.re ⟪T p.im, p.im⟫_𝕜 :=
  rfl

/-- `‖T_ℂ‖ = ‖T‖`. -/
theorem norm_complexification (T : V →L[𝕜] V) : ‖T.complexification‖ = ‖T‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _)
    (opNorm_le_bound _ (norm_nonneg _) fun x => ?_)
  rw [← norm_mk_zero (𝕜 := 𝕜) (T x), ← norm_mk_zero (𝕜 := 𝕜) x]
  convert (T.complexification).le_opNorm (Complexification.mk x 0) using 2
  ext <;> simp

/-- **Real polynomials commute with complexification**: `p(T)_ℂ = p(T_ℂ)`. -/
theorem complexification_aeval (T : V →L[𝕜] V) (p : ℝ[X]) :
    (aeval T (p.map (algebraMap ℝ 𝕜))).complexification =
      aeval T.complexification (p.map (algebraMap ℝ ℂ)) := by
  rw [← complexificationHom_apply, aeval_def, eval₂_map, hom_eval₂, aeval_def, eval₂_map]
  congr 1
  refine RingHom.ext fun r => ContinuousLinearMap.ext fun q => Complexification.ext ?_ ?_
  · change (r : 𝕜) • q.re = ((r : ℂ).re : 𝕜) • q.re - ((r : ℂ).im : 𝕜) • q.im
    simp
  · change (r : 𝕜) • q.im = ((r : ℂ).im : 𝕜) • q.re + ((r : ℂ).re : 𝕜) • q.im
    simp

/-- **An operator is invertible when its complexification is**: the inverse is
`x ↦ re (T_ℂ⁻¹ (x, 0))`. -/
theorem isUnit_of_isUnit_complexification {T : V →L[𝕜] V} (h : IsUnit T.complexification) :
    IsUnit T := by
  obtain ⟨u, hu⟩ := h
  have hl : ∀ p, u.inv (T.complexification p) = p := fun p => by
    rw [← hu]; exact congrArg (fun C : Complexification 𝕜 V →L[ℂ] _ => C p) u.inv_val
  have hr : ∀ p, T.complexification (u.inv p) = p := fun p => by
    rw [← hu]; exact congrArg (fun C : Complexification 𝕜 V →L[ℂ] _ => C p) u.val_inv
  let s : V → V := fun x => (u.inv (Complexification.mk x 0)).re
  have hTs : ∀ x, T (s x) = x := fun x => by
    have := congrArg Complexification.re (hr (Complexification.mk x 0))
    rwa [complexification_re, re_mk] at this
  have hsT : ∀ x, s (T x) = x := fun x => by
    have e : T.complexification (Complexification.mk x 0) = Complexification.mk (T x) 0 := by
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
theorem complexification_ringInverse {T : V →L[𝕜] V} (h : IsUnit T) :
    (Ring.inverse T).complexification = Ring.inverse T.complexification := by
  obtain ⟨u, rfl⟩ := h
  rw [Ring.inverse_unit]
  exact (Ring.inverse_unit (Units.map (complexificationHom (𝕜 := 𝕜) (V := V)).toMonoidHom u)).symm

/-- `‖T‖ ≤ C` when `‖T_ℂ‖ ≤ C`. -/
theorem norm_le_of_norm_complexification_le {T : V →L[𝕜] V} {C : ℝ}
    (h : ‖T.complexification‖ ≤ C) : ‖T‖ ≤ C :=
  T.norm_complexification ▸ h

end ContinuousLinearMap
