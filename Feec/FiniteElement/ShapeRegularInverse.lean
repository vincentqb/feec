module

public import Feec.FiniteElement.PolyInverseEstimate
public import Feec.FiniteElement.InterpolationError
public import Feec.FiniteElement.WhitneyInterpolation

/-!
# Inverse and DOF estimates on shape-regular simplices

Every `n`-simplex is `T = F_T(T̂)`, `F_T x̂ = B_T x̂ + p₀` (`Affine.Simplex.refMap`). The
estimates of `Feec.FiniteElement.InverseEstimate` and `Feec.FiniteElement.PolyInverseEstimate` are
proved on homothetic copies `t + h K` of finitely many reference simplices (Freudenthal–Kuhn
meshes); here they are transferred through the general affine map `F_T`, so that they hold with
one constant on every family that is **shape regular** in the sense of `Feec.Mesh.IsShapeRegular`
(`‖B_T‖ ≤ C h_T`, `‖B_T⁻¹‖ ≤ C / h_T`, `c h_Tⁿ ≤ |det B_T|`; [Ciarlet2002], §3.1–3.2).

* **The reference pullback** `F_T^* u` (`refPull`) of a form field and its inverse:
  `u(x) = (B_T⁻¹)^* (F_T^* u)(F_T⁻¹ x)` (`apply_eq_pullback_refPull`). Pullbacks of `k`-forms by a
  matrix with entries `≤ a` are bounded by `2ⁿ (n a)ᵏ` (`norm_pullback_le`); the entries of `B_T`
  and `B_T⁻¹` are bounded by `‖B_T‖`, `‖B_T⁻¹‖` (`abs_simplexMatrix_le`,
  `Feec.FiniteElement.abs_inv_edgeMatrix_le`).
  Pointwise and Lipschitz bounds (`norm_apply_le_refPull`, `norm_sub_le_refPull`,
  `norm_refMapInv_sub_le`) and the change of variables `∫_T f = |det B_T| ∫_{T̂} f ∘ F_T`
  (`integral_closedInterior_eq`, `abs_det_mul_formL2Sq_refPull_le`) follow.
* **Transfer of reference inverse estimates** (`inverse_bound_of_ref`): if a space `V` of
  continuous `k`-form fields stable under the reference pullbacks satisfies
  `sup_{T̂} ‖u‖, Lip_{T̂}(u) ≤ A₀ ‖u‖_{L²(T̂)}`, then on every shape-regular `T`
  `h_T^{n/2} sup_T ‖u‖ ≤ A ‖u‖_{L²(T)}` and `h_T^{n/2} h_T Lip_T(u) ≤ A ‖u‖_{L²(T)}`, with
  `A = invConst n k A₀ C c`. Instances: every affine-invariant `V ≤ P_rΛᵏ`
  (`exists_inverse_bound_of_le_polySpace`), in particular `P_rΛᵏ`
  (`exists_inverse_bound_polySpace`) and `P_r⁻Λᵏ`, and the Whitney forms `P₁⁻Λᵏ`, coefficientwise (`exists_inverse_bound_p1MinusForms`).
* **DOF estimates** (`dof_bound_of_ref`): `h_Tᵏ sup_T ‖u‖ ≤ 2ⁿ (n C)ᵏ B Σⱼ |ℓⱼ(F_T^* u)|` for any
  family `ℓ` of functionals with `sup_{T̂} ‖v‖ ≤ B Σⱼ |ℓⱼ(v)|`; for unisolvent DOFs on polynomial
  spaces `exists_dof_bound_of_le_polySpace` (for moment DOFs `ℓⱼ(F_T^* u)` are the moments of `u`
  on the faces of `T`, `faceMoment_affine`), and for the Whitney forms in terms of the face
  integrals of `T` itself, `exists_dof_bound_p1MinusForms` (`∫_{ĝ} F_T^* u = ± ∫_{F_T(ĝ)} u`,
  `abs_simplexIntegral_refPull`).

These are the local tools of the smoothed-projection estimates on general quasi-uniform
shape-regular meshes (`Feec.FiniteElement.ShapeRegularSmoothing`,
`Feec.Models.StarShaped.FiniteElement`).

## References

* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1 (affine
  families, shape regularity), §3.2 (inverse inequalities)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.5 (inverse estimates for the smoothed projection)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset

namespace Feec.FiniteElement

open Feec.Mesh ExteriorFibre

variable {n : ℕ}

/-! ### The affine map `F_T` and its inverse as `affine` maps -/

theorem affine_simplexMatrix_eq_refMap (T : Affine.Simplex ℝ (Fin n → ℝ) n) (x : Fin n → ℝ) :
    affine (simplexMatrix T.points) (T.points 0) x = T.refMap x := by
  rw [Affine.Simplex.refMap_apply, ← edgeMatrix_mulVec]
  funext i
  simp [affine_apply, Matrix.mulVec, dotProduct]

/-- The reference pullback `F_T^* u` of a form field. -/
def refPull (T : Affine.Simplex ℝ (Fin n → ℝ) n) (u : FormField n) : FormField n :=
  affinePullback (simplexMatrix T.points) (T.points 0) u

theorem refPull_apply (T : Affine.Simplex ℝ (Fin n → ℝ) n) (u : FormField n) (y : Fin n → ℝ) :
    refPull T u y = pullback (simplexMatrix T.points) (u (T.refMap y)) := by
  rw [refPull, affinePullback_apply, affine_simplexMatrix_eq_refMap]

/-- The inverse edge matrix as a function. -/
def invEdge (T : Affine.Simplex ℝ (Fin n → ℝ) n) : Fin n → Fin n → ℝ :=
  fun i j => (edgeMatrix T.points)⁻¹ i j

/-- **Inverting the reference pullback**: `u(x) = (B_T⁻¹)^* (F_T^* u)(F_T⁻¹ x)`. -/
theorem apply_eq_pullback_refPull (T : Affine.Simplex ℝ (Fin n → ℝ) n) (u : FormField n)
    (x : Fin n → ℝ) : u x = pullback (invEdge T) (refPull T u (refMapInv T x)) := by
  rw [refPull_apply, refMap_refMapInv, pullback_pullback]
  have hM : (fun j l => ∑ i, simplexMatrix T.points j i * invEdge T i l) =
      fun j l => if j = l then (1 : ℝ) else 0 := by
    funext j l
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv _ (isUnit_det_edgeMatrix T)) j) l
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  rw [hM, pullback_id]

theorem abs_simplexMatrix_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i j : Fin n) :
    |simplexMatrix T.points i j| ≤ ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ := by
  have h : simplexMatrix T.points i j = Matrix.mulVec (edgeMatrix T.points) (Pi.single j 1) i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h, edgeMatrix_mulVec, ← Affine.Simplex.linearEquiv_apply, ← Real.norm_eq_abs]
  refine (norm_le_pi_norm _ i).trans ?_
  refine ((T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ).le_opNorm _).trans ?_
  refine le_of_le_of_eq (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (mul_one _)
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => ?_
  by_cases hl : l = j
  · subst hl; simp
  · simp [hl]

/-- **Pointwise bound of a pullback**: `‖M^* α‖ ≤ 2ⁿ (n a)ᵏ ‖α‖` for a `k`-form `α` and a
matrix with entries bounded by `a`. -/
theorem norm_pullback_le {m : ℕ} {M : Fin n → Fin m → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ i j, |M i j| ≤ a) {k : ℕ} {α : Finset (Fin n) → ℝ} (hα : IsDeg k α) :
    ‖pullback M α‖ ≤ 2 ^ n * (m * a) ^ k * ‖α‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun t => ?_
  rw [pullback_apply, Real.norm_eq_abs]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ s : Finset (Fin n), |α s * wedgeProd M s t| ≤ (m * a) ^ k * ‖α‖ := by
    intro s
    by_cases hs : #s = k
    · rw [abs_mul, mul_comm]
      refine mul_le_mul ?_ (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm α s)
        (abs_nonneg _) (by positivity)
      have h := abs_wedgeProd_le ha hM s t
      rwa [Fintype.card_fin, hs] at h
    · rw [hα s hs, zero_mul, abs_zero]; positivity
  calc ∑ s, |α s * wedgeProd M s t| ≤ ∑ _s : Finset (Fin n), (m * a) ^ k * ‖α‖ :=
        Finset.sum_le_sum fun s _ => hterm s
    _ = 2 ^ n * (m * a) ^ k * ‖α‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast; ring

theorem isDeg_refPull {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) n) {u : FormField n}
    (hu : ∀ x, IsDeg k (u x)) (y : Fin n → ℝ) : IsDeg k (refPull T u y) := by
  rw [refPull_apply]; exact (hu _).pullback _

/-- `‖u(x)‖ ≤ 2ⁿ (n ‖B_T⁻¹‖)ᵏ ‖(F_T^* u)(F_T⁻¹ x)‖`. -/
theorem norm_apply_le_refPull {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) n) {u : FormField n}
    (hu : ∀ x, IsDeg k (u x)) (x : Fin n → ℝ) :
    ‖u x‖ ≤ 2 ^ n * (n * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) ^ k *
      ‖refPull T u (refMapInv T x)‖ := by
  rw [apply_eq_pullback_refPull T u x]
  exact norm_pullback_le (norm_nonneg _) (abs_inv_edgeMatrix_le T) (isDeg_refPull T hu _)

/-- `‖u(x) - u(x')‖ ≤ 2ⁿ (n ‖B_T⁻¹‖)ᵏ ‖(F_T^* u)(F_T⁻¹ x) - (F_T^* u)(F_T⁻¹ x')‖`. -/
theorem norm_sub_le_refPull {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) n) {u : FormField n}
    (hu : ∀ x, IsDeg k (u x)) (x x' : Fin n → ℝ) :
    ‖u x - u x'‖ ≤ 2 ^ n * (n * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) ^ k *
      ‖refPull T u (refMapInv T x) - refPull T u (refMapInv T x')‖ := by
  rw [apply_eq_pullback_refPull T u x, apply_eq_pullback_refPull T u x', ← pullback_sub]
  refine norm_pullback_le (norm_nonneg _) (abs_inv_edgeMatrix_le T) ?_
  intro s hs
  rw [Pi.sub_apply, isDeg_refPull T hu _ s hs, isDeg_refPull T hu _ s hs, sub_zero]

theorem norm_refMapInv_sub_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) (x x' : Fin n → ℝ) :
    ‖refMapInv T x - refMapInv T x'‖ ≤
      ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ * ‖x - x'‖ := by
  have e : refMapInv T x - refMapInv T x' = T.linearEquiv.symm (x - x') := by
    simp only [refMapInv, ← map_sub]; congr 1; abel
  rw [e]
  exact (T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ).le_opNorm _

/-! ### Change of variables -/

/-- **Change of variables** on a simplex: `∫_T f = |det B_T| ∫_{T̂} f ∘ F_T`. -/
theorem integral_closedInterior_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (f : (Fin n → ℝ) → ℝ) :
    ∫ x in T.closedInterior, f x =
      |LinearMap.det T.linearPart| * ∫ y in (Mesh.refSimplex n).closedInterior, f (T.refMap y) := by
  rw [T.closedInterior_eq_image_refMap,
    integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_closedInterior _)
      (fun x _ => (hasFDerivAt_refMap T x).hasFDerivWithinAt) (T.refMap_injective.injOn)]
  simp_rw [smul_eq_mul]
  rw [integral_const_mul]
  rfl

theorem continuous_pullback {ι κ : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder κ]
    (M : ι → κ → ℝ) : Continuous fun α : Finset ι → ℝ => pullback M α := by
  refine continuous_pi fun t => ?_
  simp_rw [pullback_apply]
  exact continuous_finsetSum _ fun s _ => (continuous_apply s).mul continuous_const

theorem continuous_refPull (T : Affine.Simplex ℝ (Fin n → ℝ) n) {u : FormField n}
    (hu : Continuous u) : Continuous (refPull T u) := by
  have : refPull T u = (fun α => pullback (simplexMatrix T.points) α) ∘ u ∘ T.refMap := by
    funext y; rw [refPull_apply]; rfl
  rw [this]
  exact (continuous_pullback _).comp (hu.comp (contDiff_refMap T (N := 0)).continuous)

theorem sum_sq_le_card_mul_sq_norm {J : Type*} [Fintype J] (α : J → ℝ) :
    ∑ j, α j ^ 2 ≤ Fintype.card J * ‖α‖ ^ 2 := by
  calc ∑ j, α j ^ 2 ≤ ∑ _j : J, ‖α‖ ^ 2 := Finset.sum_le_sum fun j _ => by
        rw [← sq_abs, ← Real.norm_eq_abs]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm α j) 2
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem formL2Sq_eq_integral_sum {S : Set (Fin n → ℝ)} (hS : IsCompact S) {u : FormField n}
    (hu : Continuous u) : formL2Sq S u = ∫ x in S, ∑ s, (u x s) ^ 2 := by
  rw [formL2Sq, integral_finsetSum]
  intro s _
  exact (((continuous_apply s).comp hu).pow 2).continuousOn.integrableOn_compact hS

/-- **`L²` norms under the reference pullback**:
`|det B_T| ‖F_T^* u‖²_{L²(T̂)} ≤ 8ⁿ (n ‖B_T‖)^{2k} ‖u‖²_{L²(T)}` for a continuous `k`-form. -/
theorem abs_det_mul_formL2Sq_refPull_le {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    {u : FormField n} (hu : ∀ x, IsDeg k (u x)) (hc : Continuous u) :
    |LinearMap.det T.linearPart| * formL2Sq (Mesh.refSimplex n).closedInterior (refPull T u) ≤
      8 ^ n * ((n * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) ^ k) ^ 2 *
        formL2Sq T.closedInterior u := by
  set a := ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖
  set K := (Mesh.refSimplex n).closedInterior
  have hK : IsCompact K := (Mesh.refSimplex n).isCompact_closedInterior
  have hKm : MeasurableSet K := (Mesh.refSimplex n).isClosed_closedInterior.measurableSet
  have hpt : ∀ y, ∑ t, (refPull T u y t) ^ 2 ≤
      8 ^ n * ((n * a) ^ k) ^ 2 * ∑ s, (u (T.refMap y) s) ^ 2 := by
    intro y
    have h1 := sum_sq_le_card_mul_sq_norm (refPull T u y)
    rw [Fintype.card_finset, Fintype.card_fin] at h1
    have h2 : ‖refPull T u y‖ ≤ 2 ^ n * (n * a) ^ k * ‖u (T.refMap y)‖ := by
      rw [refPull_apply]
      exact norm_pullback_le (norm_nonneg _) (abs_simplexMatrix_le T) (hu _)
    have h3 := sq_norm_pi_le_sum_sq (u (T.refMap y))
    calc ∑ t, (refPull T u y t) ^ 2 ≤ (2 ^ n : ℕ) * ‖refPull T u y‖ ^ 2 := h1
      _ ≤ (2 ^ n : ℕ) * (2 ^ n * (n * a) ^ k * ‖u (T.refMap y)‖) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by positivity)
      _ = 8 ^ n * ((n * a) ^ k) ^ 2 * ‖u (T.refMap y)‖ ^ 2 := by
          push_cast
          rw [show (8 : ℝ) ^ n = 2 ^ n * (2 ^ n) ^ 2 by
            rw [← pow_mul, ← pow_add]; rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]; ring_nf]
          ring
      _ ≤ 8 ^ n * ((n * a) ^ k) ^ 2 * ∑ s, (u (T.refMap y) s) ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hcF : Continuous fun y => ∑ s, (u (T.refMap y) s) ^ 2 :=
    continuous_finsetSum _ fun s _ =>
      (((continuous_apply s).comp (hc.comp (contDiff_refMap T (N := 0)).continuous)).pow 2)
  rw [formL2Sq_eq_integral_sum hK (continuous_refPull T hc),
    formL2Sq_eq_integral_sum T.isCompact_closedInterior hc, integral_closedInterior_eq T]
  rw [← mul_assoc, mul_comm (8 ^ n * ((n * a) ^ k) ^ 2) |LinearMap.det T.linearPart|, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ hKm fun y _ => hpt y
  · exact (continuous_finsetSum _ fun t _ => ((continuous_apply t).comp
      (continuous_refPull T hc)).pow 2).continuousOn.integrableOn_compact hK
  · exact ((continuous_const.mul hcF).continuousOn.integrableOn_compact hK :
      IntegrableOn (fun y => 8 ^ n * ((n * a) ^ k) ^ 2 * ∑ s, (u (T.refMap y) s) ^ 2) K)

theorem sqrt_abs_det_mul_le {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    {u : FormField n} (hu : ∀ x, IsDeg k (u x)) (hc : Continuous u) :
    √|LinearMap.det T.linearPart| *
        √(formL2Sq (Mesh.refSimplex n).closedInterior (refPull T u)) ≤
      √(8 ^ n) * (n * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) ^ k *
        √(formL2Sq T.closedInterior u) := by
  have h := abs_det_mul_formL2Sq_refPull_le T hu hc
  rw [← Real.sqrt_mul (abs_nonneg _)]
  refine (Real.sqrt_le_sqrt h).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-! ### Transfer of reference estimates to shape-regular simplices -/

/-- The constant of the transferred inverse estimates. -/
def invConst (n k : ℕ) (A₀ C c : ℝ) : ℝ :=
  2 ^ n * A₀ * √(8 ^ n) * ((n : ℝ) ^ 2 * C ^ 2) ^ k / √c * (1 + C)

theorem invConst_nonneg (n k : ℕ) {A₀ C c : ℝ} (hA₀ : 0 ≤ A₀) (hC : 0 ≤ C) :
    0 ≤ invConst n k A₀ C c := by
  unfold invConst; positivity

/-- The scaling identity behind the transfer: `√h_Tⁿ ‖F_T^* u‖_{L²(T̂)} ≤ c^{-1/2} 8^{n/2}
(n ‖B_T‖)ᵏ ‖u‖_{L²(T)}` when `c h_Tⁿ ≤ |det B_T|`. -/
theorem sqrt_pow_mul_sqrt_formL2Sq_refPull_le {k : ℕ} {c : ℝ} (hc : 0 < c)
    (T : Affine.Simplex ℝ (Fin n → ℝ) n) (hh : 0 < diam T)
    (hdet : c * diam T ^ n ≤ |LinearMap.det T.linearPart|)
    {u : FormField n} (hu : ∀ x, IsDeg k (u x)) (hcu : Continuous u) :
    √(diam T) ^ n * √(formL2Sq (Mesh.refSimplex n).closedInterior (refPull T u)) ≤
      √(8 ^ n) * (n * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) ^ k / √c *
        √(formL2Sq T.closedInterior u) := by
  set d := |LinearMap.det T.linearPart|
  set LK := formL2Sq (Mesh.refSimplex n).closedInterior (refPull T u)
  have hLK : 0 ≤ √LK := Real.sqrt_nonneg _
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  have h1 := sqrt_abs_det_mul_le T hu hcu
  have h2 : √(diam T) ^ n * √c ≤ √d := by
    rw [← sqrt_pow_eq hh.le, ← Real.sqrt_mul (pow_nonneg hh.le n), mul_comm]
    exact Real.sqrt_le_sqrt hdet
  rw [div_mul_eq_mul_div, le_div_iff₀ hsc]
  calc √(diam T) ^ n * √LK * √c = (√(diam T) ^ n * √c) * √LK := by ring
    _ ≤ √d * √LK := mul_le_mul_of_nonneg_right h2 hLK
    _ ≤ _ := h1

/-- **Transfer of reference inverse estimates** to a shape-regular simplex: if a space `V` of
continuous `k`-form fields, stable under the reference pullbacks `F_T^*`, satisfies
`sup_{T̂} ‖u‖ ≤ A₀ ‖u‖_{L²(T̂)}` and `Lip_{T̂}(u) ≤ A₀ ‖u‖_{L²(T̂)}`, then on every simplex `T` with
`‖B_T‖ ≤ C h_T`, `‖B_T⁻¹‖ ≤ C / h_T`, `c h_Tⁿ ≤ |det B_T|`,
`h_T^{n/2} sup_T ‖u‖ ≤ A ‖u‖_{L²(T)}` and `h_T^{n/2} h_T Lip_T(u) ≤ A ‖u‖_{L²(T)}`, with
`A = invConst n k A₀ C c` depending only on `n, k, A₀, C, c`. -/
theorem inverse_bound_of_ref {k : ℕ} {V : Submodule ℝ (FormField n)}
    (hVdeg : ∀ u ∈ V, ∀ x, IsDeg k (u x)) (hVc : ∀ u ∈ V, Continuous u)
    (hVA : ∀ (T : Affine.Simplex ℝ (Fin n → ℝ) n), ∀ u ∈ V, refPull T u ∈ V)
    {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (href : ∀ u ∈ V,
      (∀ y ∈ (Mesh.refSimplex n).closedInterior,
        ‖u y‖ ≤ A₀ * √(formL2Sq (Mesh.refSimplex n).closedInterior u)) ∧
      (∀ y ∈ (Mesh.refSimplex n).closedInterior, ∀ y' ∈ (Mesh.refSimplex n).closedInterior,
        ‖u y - u y'‖ ≤ A₀ * ‖y - y'‖ * √(formL2Sq (Mesh.refSimplex n).closedInterior u)))
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hh : 0 < diam T)
    (hB : ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ≤ C * diam T)
    (hBs : ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ≤ C / diam T)
    (hdet : c * diam T ^ n ≤ |LinearMap.det T.linearPart|) {u : FormField n} (hu : u ∈ V) :
    (∀ x ∈ T.closedInterior, √(diam T) ^ n * ‖u x‖ ≤
      invConst n k A₀ C c * √(formL2Sq T.closedInterior u)) ∧
    (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior, √(diam T) ^ n * diam T * ‖u x - u x'‖ ≤
      invConst n k A₀ C c * ‖x - x'‖ * √(formL2Sq T.closedInterior u)) := by
  set h := diam T
  set a := ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖
  set S := ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖
  set v := refPull T u
  set LK := formL2Sq (Mesh.refSimplex n).closedInterior v
  set LT := formL2Sq T.closedInterior u
  have hdeg := hVdeg u hu
  have hv := hVA T u hu
  obtain ⟨hr1, hr2⟩ := href v hv
  have hLT : 0 ≤ √LT := Real.sqrt_nonneg _
  have hLK : 0 ≤ √LK := Real.sqrt_nonneg _
  have ha : 0 ≤ a := norm_nonneg _
  have hS : 0 ≤ S := norm_nonneg _
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  have hsq : 0 ≤ √h ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  have hkey := sqrt_pow_mul_sqrt_formL2Sq_refPull_le (k := k) hc T hh hdet hdeg (hVc u hu)
  have hSa : (n * S) ^ k * (n * a) ^ k ≤ ((n : ℝ) ^ 2 * C ^ 2) ^ k := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ k
    have : S * a ≤ C / h * (C * h) := mul_le_mul hBs hB ha (by positivity)
    rw [show C / h * (C * h) = C ^ 2 by field_simp] at this
    nlinarith [sq_nonneg (n : ℝ)]
  -- the common bound `2ⁿ (n S)ᵏ A₀ √hⁿ √LK ≤ K₀ √LT`, `K₀ = 2ⁿ A₀ √8ⁿ (n² C²)ᵏ / √c`
  set K₀ := 2 ^ n * A₀ * √(8 ^ n) * ((n : ℝ) ^ 2 * C ^ 2) ^ k / √c
  have hK₀ : invConst n k A₀ C c = K₀ * (1 + C) := rfl
  have hinv : 0 ≤ K₀ := by positivity
  have hcore : 2 ^ n * (n * S) ^ k * A₀ * (√h ^ n * √LK) ≤ K₀ * √LT := by
    calc 2 ^ n * (n * S) ^ k * A₀ * (√h ^ n * √LK)
        ≤ 2 ^ n * (n * S) ^ k * A₀ * (√(8 ^ n) * (n * a) ^ k / √c * √LT) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 2 ^ n * A₀ * √(8 ^ n) * ((n * S) ^ k * (n * a) ^ k) / √c * √LT := by ring
      _ ≤ (2 ^ n * A₀ * √(8 ^ n) * ((n : ℝ) ^ 2 * C ^ 2) ^ k / √c) * √LT := by gcongr
  constructor
  · intro x hx
    have hy := (mem_closedInterior_iff_refMapInv _).1 hx
    calc √h ^ n * ‖u x‖ ≤ √h ^ n * (2 ^ n * (n * S) ^ k * ‖v (refMapInv T x)‖) :=
          mul_le_mul_of_nonneg_left (norm_apply_le_refPull T hdeg x) hsq
      _ ≤ √h ^ n * (2 ^ n * (n * S) ^ k * (A₀ * √LK)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hr1 _ hy) (by positivity)) hsq
      _ = 2 ^ n * (n * S) ^ k * A₀ * (√h ^ n * √LK) := by ring
      _ ≤ K₀ * √LT := hcore
      _ ≤ invConst n k A₀ C c * √LT := by
          rw [hK₀]; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hinv (by linarith)) hLT
  · intro x hx x' hx'
    have hy := (mem_closedInterior_iff_refMapInv _).1 hx
    have hy' := (mem_closedInterior_iff_refMapInv _).1 hx'
    have hyy := norm_refMapInv_sub_le T x x'
    have hhS : h * S ≤ C := by
      have := mul_le_mul_of_nonneg_left hBs hh.le
      rwa [show h * (C / h) = C by field_simp] at this
    calc √h ^ n * h * ‖u x - u x'‖
        ≤ √h ^ n * h * (2 ^ n * (n * S) ^ k *
            ‖v (refMapInv T x) - v (refMapInv T x')‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le_refPull T hdeg x x') (by positivity)
      _ ≤ √h ^ n * h * (2 ^ n * (n * S) ^ k *
            (A₀ * (S * ‖x - x'‖) * √LK)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((hr2 _ hy _ hy').trans ?_)
            (by positivity)) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyy hA₀) hLK
      _ = (h * S) * ‖x - x'‖ * (2 ^ n * (n * S) ^ k * A₀ * (√h ^ n * √LK)) := by ring
      _ ≤ C * ‖x - x'‖ * (K₀ * √LT) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hhS (norm_nonneg _)) hcore (by positivity)
            (by positivity)
      _ ≤ invConst n k A₀ C c * ‖x - x'‖ * √LT := by
          rw [hK₀]
          have h0 : 0 ≤ ‖x - x'‖ * √LT := by positivity
          nlinarith [mul_le_mul_of_nonneg_right (show C * K₀ ≤ K₀ * (1 + C) by nlinarith) h0]

/-! ### Instances: polynomial forms and trimmed linear forms -/

theorem norm_le_one_of_mem_refSimplex {y : Fin n → ℝ}
    (hy : y ∈ (Mesh.refSimplex n).closedInterior) : ‖y‖ ≤ 1 := by
  obtain ⟨h0, h1⟩ := mem_closedInterior_refSimplex.1 hy
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 i)]
  exact (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)).trans h1

/-- **Inverse estimates on shape-regular simplices** for spaces of polynomial forms
(`V ≤ P_rΛᵏ`, stable under affine pullbacks, e.g. `P_rΛᵏ`, `P_r⁻Λᵏ`): with one constant `A`
depending only on `n, k, V, C, c`, every simplex `T` of a family that is shape regular with
constants `C, c` satisfies `h_T^{n/2} sup_T ‖u‖ ≤ A ‖u‖_{L²(T)}` and
`h_T^{n/2} h_T Lip_T(u) ≤ A ‖u‖_{L²(T)}` ([Ciarlet2002], §3.2). -/
theorem exists_inverse_bound_of_le_polySpace {r k : ℕ} {V : Submodule ℝ (FormField n)}
    (hV : V ≤ polySpace n r k)
    (hVA : ∀ (B : Fin n → Fin n → ℝ) (b : Fin n → ℝ), ∀ u ∈ V, affinePullback B b u ∈ V)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ A, 0 ≤ A ∧ ∀ {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular S C c →
      ∀ T ∈ S, 0 < diam T → ∀ u ∈ V,
        (∀ x ∈ T.closedInterior, √(diam T) ^ n * ‖u x‖ ≤
          A * √(formL2Sq T.closedInterior u)) ∧
        (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior,
          √(diam T) ^ n * diam T * ‖u x - u x'‖ ≤
            A * ‖x - x'‖ * √(formL2Sq T.closedInterior u)) := by
  obtain ⟨A₀, hA₀, href⟩ := exists_norm_le_sqrt_formL2Sq hV
    (Mesh.refSimplex n).isCompact_closedInterior (interior_closedInterior_nonempty _)
    (convex_closedInterior _)
  refine ⟨invConst n k A₀ C c, invConst_nonneg n k hA₀ hC, fun {S} hS T hT hh u hu => ?_⟩
  obtain ⟨hB, hBs, hdet⟩ := hS T hT
  exact inverse_bound_of_ref (fun u hu x => isDeg_of_mem_polySpace (hV hu) x)
    (fun u hu => (polySpace_le_c1 (hV hu)).continuous) (fun T u hu => hVA _ _ u hu) hA₀ href hC
    hc hh hB hBs hdet hu

/-- **Inverse estimates on shape-regular simplices for `P_rΛᵏ`.** -/
theorem exists_inverse_bound_polySpace (r k : ℕ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ A, 0 ≤ A ∧ ∀ {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular S C c →
      ∀ T ∈ S, 0 < diam T → ∀ u ∈ polySpace n r k,
        (∀ x ∈ T.closedInterior, √(diam T) ^ n * ‖u x‖ ≤
          A * √(formL2Sq T.closedInterior u)) ∧
        (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior,
          √(diam T) ^ n * diam T * ‖u x - u x'‖ ≤
            A * ‖x - x'‖ * √(formL2Sq T.closedInterior u)) :=
  exists_inverse_bound_of_le_polySpace le_rfl (fun B b _ hu => affinePullback_mem_polySpace B b hu)
    hC hc

/-- **Inverse estimates on shape-regular simplices for the Whitney forms `P₁⁻Λᵏ`**, coefficient-
wise: `h_T^{n/2} |u(x)ₛ| ≤ A ‖u‖_{L²(T)}` and `h_T^{n/2} h_T |u(x)ₛ - u(x')ₛ| ≤
A |x - x'| ‖u‖_{L²(T)}` on `T`. -/
theorem exists_inverse_bound_p1MinusForms (k : ℕ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ A, 0 ≤ A ∧ ∀ {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular S C c →
      ∀ T ∈ S, 0 < diam T → ∀ u ∈ p1MinusForms n k,
        (∀ x ∈ T.closedInterior, ∀ s, √(diam T) ^ n * |u x s| ≤
          A * √(formL2Sq T.closedInterior u)) ∧
        (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior, ∀ s,
          √(diam T) ^ n * diam T * |u x s - u x' s| ≤
            A * ‖x - x'‖ * √(formL2Sq T.closedInterior u)) := by
  obtain ⟨A₁, hA₁, hA⟩ := exists_affSize_le_sqrt_integral (Mesh.refSimplex n).isCompact_closedInterior
    (interior_closedInterior_nonempty _) k
  have href : ∀ u ∈ p1MinusForms n k,
      (∀ y ∈ (Mesh.refSimplex n).closedInterior,
        ‖u y‖ ≤ (2 * A₁) * √(formL2Sq (Mesh.refSimplex n).closedInterior u)) ∧
      (∀ y ∈ (Mesh.refSimplex n).closedInterior, ∀ y' ∈ (Mesh.refSimplex n).closedInterior,
        ‖u y - u y'‖ ≤ (2 * A₁) * ‖y - y'‖ *
          √(formL2Sq (Mesh.refSimplex n).closedInterior u)) := by
    intro u hu
    have haff := isAffineField_of_mem_p1MinusForms hu
    have h1 : affSize u ≤ A₁ * √(formL2Sq (Mesh.refSimplex n).closedInterior u) := hA u hu
    have h0 : 0 ≤ A₁ * √(formL2Sq (Mesh.refSimplex n).closedInterior u) :=
      (affSize_nonneg u).trans h1
    refine ⟨fun y hy => ?_, fun y _ y' _ => ?_⟩
    · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s => ?_
      rw [Real.norm_eq_abs]
      refine (haff.abs_le y s).trans ?_
      have := norm_le_one_of_mem_refSimplex hy
      calc (‖y‖ + 1) * affSize u ≤ 2 * (A₁ * √(formL2Sq (Mesh.refSimplex n).closedInterior u)) :=
            mul_le_mul (by linarith) h1 (affSize_nonneg _) (by norm_num)
        _ = _ := by ring
    · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s => ?_
      rw [Pi.sub_apply, Real.norm_eq_abs]
      refine (haff.abs_sub_le y y' s).trans ?_
      calc ‖y - y'‖ * affSize u ≤ ‖y - y'‖ * (A₁ * √(formL2Sq (Mesh.refSimplex n).closedInterior u)) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ _ := by nlinarith [norm_nonneg (y - y')]
  refine ⟨invConst n k (2 * A₁) C c, invConst_nonneg n k (by positivity) hC,
    fun {S} hS T hT hh u hu => ?_⟩
  obtain ⟨hB, hBs, hdet⟩ := hS T hT
  obtain ⟨h1, h2⟩ := inverse_bound_of_ref (V := p1MinusForms n k)
    (fun u hu x => isDeg_of_mem_p1MinusForms hu x)
    (fun u hu => (isAffineField_of_mem_p1MinusForms hu).continuous)
    (fun T u hu => affinePullback_mem_p1MinusForms _ _ hu) (by positivity) href hC hc hh hB hBs
    hdet hu
  refine ⟨fun x hx s => ?_, fun x hx x' hx' s => ?_⟩
  · refine le_trans ?_ (h1 x hx)
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Real.sqrt_nonneg _) n)
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (u x) s
  · refine le_trans ?_ (h2 x hx x' hx')
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Real.norm_eq_abs, ← Pi.sub_apply]; exact norm_le_pi_norm (u x - u x') s

/-! ### DOF estimates -/

/-- **Transfer of reference DOF estimates**: if `sup_{T̂} ‖v‖ ≤ B Σⱼ |ℓⱼ(v)|` on `V`, then on a
simplex with `h_T ‖B_T⁻¹‖ ≤ C`, `h_Tᵏ sup_T ‖u‖ ≤ 2ⁿ (n C)ᵏ B Σⱼ |ℓⱼ(F_T^* u)|`. -/
theorem dof_bound_of_ref {k : ℕ} {V : Submodule ℝ (FormField n)}
    (hVdeg : ∀ u ∈ V, ∀ x, IsDeg k (u x))
    (hVA : ∀ (T : Affine.Simplex ℝ (Fin n → ℝ) n), ∀ u ∈ V, refPull T u ∈ V)
    {J : Type*} [Fintype J] (ℓ : J → V →ₗ[ℝ] ℝ) {B : ℝ}
    (href : ∀ v : V, ∀ y ∈ (Mesh.refSimplex n).closedInterior,
      ‖(v : FormField n) y‖ ≤ B * ∑ j, |ℓ j v|)
    {C : ℝ} (hC : 0 ≤ C) {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hh : 0 < diam T)
    (hBs : ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ≤ C / diam T)
    {u : FormField n} (hu : u ∈ V) {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) :
    diam T ^ k * ‖u x‖ ≤ 2 ^ n * (n * C) ^ k * B * ∑ j, |ℓ j ⟨refPull T u, hVA T u hu⟩| := by
  set S := ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖
  have hS : 0 ≤ S := norm_nonneg _
  have hhS : diam T * S ≤ C := by
    have := mul_le_mul_of_nonneg_left hBs hh.le
    rwa [show diam T * (C / diam T) = C by field_simp] at this
  have h1 := norm_apply_le_refPull T (hVdeg u hu) x
  have h2 := href ⟨refPull T u, hVA T u hu⟩ _ ((mem_closedInterior_iff_refMapInv _).1 hx)
  have hsum : 0 ≤ ∑ j, |ℓ j ⟨refPull T u, hVA T u hu⟩| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc diam T ^ k * ‖u x‖ ≤ diam T ^ k * (2 ^ n * (n * S) ^ k * ‖refPull T u (refMapInv T x)‖) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg hh.le k)
    _ = 2 ^ n * (n * (diam T * S)) ^ k * ‖refPull T u (refMapInv T x)‖ := by ring
    _ ≤ 2 ^ n * (n * C) ^ k * (B * ∑ j, |ℓ j ⟨refPull T u, hVA T u hu⟩|) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left hhS (Nat.cast_nonneg _)) k) (by positivity)) h2
          (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- **DOF estimates on shape-regular simplices** for spaces of polynomial forms: for a family `ℓ`
of linear functionals unisolvent on `V` (the DOFs on the reference simplex), with one constant
`B` depending only on `V`, `ℓ`, `n`, `k`, `C`, every `T` of a shape-regular family satisfies
`h_Tᵏ sup_T ‖u‖ ≤ B Σⱼ |ℓⱼ(F_T^* u)|`. For moment DOFs `ℓⱼ(F_T^* u)` are the moments of `u` on the
faces of `T` (`faceMoment_affine`). -/
theorem exists_dof_bound_of_le_polySpace {r k : ℕ} {V : Submodule ℝ (FormField n)}
    (hV : V ≤ polySpace n r k)
    (hVA : ∀ (B : Fin n → Fin n → ℝ) (b : Fin n → ℝ), ∀ u ∈ V, affinePullback B b u ∈ V)
    {J : Type*} [Fintype J] (ℓ : J → V →ₗ[ℝ] ℝ) (hℓ : Function.Injective (LinearMap.pi ℓ))
    {C c : ℝ} :
    ∃ B, 0 ≤ B ∧ ∀ {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular S C c →
      ∀ T ∈ S, 0 < diam T → ∀ (u : FormField n) (hu : u ∈ V), ∀ x ∈ T.closedInterior,
        diam T ^ k * ‖u x‖ ≤
          B * ∑ j, |ℓ j ⟨refPull T u, hVA _ _ u hu⟩| := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_sum_abs_dof hV (Mesh.refSimplex n).isCompact_closedInterior
    ℓ hℓ
  refine ⟨2 ^ n * (n * |C|) ^ k * B, by positivity, fun {S} hS T hT hh u hu x hx => ?_⟩
  obtain ⟨-, hBs, -⟩ := hS T hT
  have hBs' : ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ≤ |C| / diam T :=
    hBs.trans (div_le_div_of_nonneg_right (le_abs_self C) hh.le)
  exact dof_bound_of_ref (fun u hu x => isDeg_of_mem_polySpace (hV hu) x)
    (fun T u hu => hVA _ _ u hu) ℓ hB (abs_nonneg C) hh hBs' hu hx

/-- **Face integrals under the reference map**: up to orientation,
`∫_{ĝ} F_T^* u = ∫_{F_T(ĝ)} u` for a `k`-face `ĝ` of the reference simplex. -/
theorem abs_simplexIntegral_refPull {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    {g : Finset (Fin n → ℝ)} (hgc : g.card = k + 1) (u : FormField n) :
    |simplexIntegral (faceEnum g (k + 1)) (refPull T u)| =
      |simplexIntegral (faceEnum (g.image T.refMap) (k + 1)) u| := by
  classical
  have hinj : Function.Injective (T.refMap : (Fin n → ℝ) → Fin n → ℝ) := T.refMap_injective
  have hcard : (g.image T.refMap).card = k + 1 := by
    rw [Finset.card_image_of_injective _ hinj, hgc]
  have hq := injective_faceEnum hgc
  have hrange : Set.range ((T.refMap : (Fin n → ℝ) → Fin n → ℝ) ∘ faceEnum g (k + 1)) =
      Set.range (faceEnum (g.image T.refMap) (k + 1)) := by
    rw [Set.range_comp, range_faceEnum hgc, range_faceEnum hcard, Finset.coe_image]
  obtain ⟨ε, hε, hεw⟩ := exists_sign_simplexIntegral_eq (hinj.comp hq)
    (injective_faceEnum hcard) hrange
  have h2 : simplexIntegral ((T.refMap : (Fin n → ℝ) → Fin n → ℝ) ∘ faceEnum g (k + 1)) u =
      simplexIntegral (faceEnum g (k + 1)) (refPull T u) := by
    rw [refPull, ← simplexIntegral_comp_affine]
    congr 1
    funext i
    rw [affine_simplexMatrix_eq_refMap]; rfl
  rw [← h2, hεw u, abs_mul]
  rcases hε with rfl | rfl <;> simp

theorem image_refMap_subset_vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    {g : Finset (Fin n → ℝ)} (hg : g ⊆ vertexSet (Mesh.refSimplex n)) :
    g.image T.refMap ⊆ vertexSet T := by
  classical
  intro v hv
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
  obtain ⟨i, rfl⟩ := mem_vertexSet.1 (hg hy)
  rw [Mesh.refSimplex_points, Affine.Simplex.refMap_refPoints]
  exact points_mem_vertexSet T i

/-- **DOF estimate on shape-regular simplices for the Whitney forms**: with one constant `B`
(depending only on `n, k, C`), if the face integrals of `z ∈ P₁⁻Λᵏ` over the `k`-faces of `T` are
bounded by `D`, then `h_Tᵏ |z(x)ₛ| ≤ B D` on `T`. -/
theorem exists_dof_bound_p1MinusForms (k : ℕ) {C c : ℝ} :
    ∃ B, 0 ≤ B ∧ ∀ {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular S C c →
      ∀ T ∈ S, 0 < diam T → ∀ {z : FormField n}, z ∈ p1MinusForms n k → ∀ {D : ℝ}, 0 ≤ D →
        (∀ g ⊆ vertexSet T, g.card = k + 1 →
          |simplexIntegral (faceEnum g (k + 1)) z| ≤ D) →
        ∀ x ∈ T.closedInterior, ∀ s, diam T ^ k * |z x s| ≤ B * D := by
  classical
  obtain ⟨B₀, hB₀, hB⟩ := exists_affSize_le_sum_dof (Mesh.refSimplex n) k
  set N := Fintype.card (Σ g : (vertexSet (Mesh.refSimplex n)).powerset,
    WhitneyDofIdx (g : Finset (Fin n → ℝ)) k)
  refine ⟨2 ^ n * (n * |C|) ^ k * (2 * (B₀ * N)), by positivity,
    fun {S} hS T hT hh z hz D hD0 hD x hx s => ?_⟩
  obtain ⟨-, hBs, -⟩ := hS T hT
  have hBs' : ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ≤ |C| / diam T :=
    hBs.trans (div_le_div_of_nonneg_right (le_abs_self C) hh.le)
  set V := p1MinusForms n k
  have hVA : ∀ (T : Affine.Simplex ℝ (Fin n → ℝ) n), ∀ u ∈ V, refPull T u ∈ V :=
    fun T u hu => affinePullback_mem_p1MinusForms _ _ hu
  have hv := hVA T z hz
  set v := refPull T z
  have hsum : ∑ p : Σ g : (vertexSet (Mesh.refSimplex n)).powerset,
      WhitneyDofIdx (g : Finset (Fin n → ℝ)) k,
      |simplexIntegral (faceEnum (p.1 : Finset (Fin n → ℝ)) (k + 1)) v| ≤ N * D := by
    calc _ ≤ ∑ _p : Σ g : (vertexSet (Mesh.refSimplex n)).powerset,
          WhitneyDofIdx (g : Finset (Fin n → ℝ)) k, D := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [abs_simplexIntegral_refPull T p.2.2 z]
          refine hD _ (image_refMap_subset_vertexSet T (Finset.mem_powerset.1 p.1.2)) ?_
          rw [Finset.card_image_of_injective _ T.refMap_injective, p.2.2]
      _ = N * D := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hvb : ‖v (refMapInv T x)‖ ≤ 2 * (B₀ * N) * D := by
    have haff := isAffineField_of_mem_p1MinusForms hv
    have h1 := hB v hv
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun t => ?_
    rw [Real.norm_eq_abs]
    refine (haff.abs_le _ t).trans ?_
    have hy := norm_le_one_of_mem_refSimplex ((mem_closedInterior_iff_refMapInv _).1 hx)
    calc (‖refMapInv T x‖ + 1) * affSize v ≤ 2 * (B₀ * (N * D)) :=
          mul_le_mul (by linarith) (h1.trans (mul_le_mul_of_nonneg_left hsum hB₀))
            (affSize_nonneg _) (by norm_num)
      _ = _ := by ring
  have hS0 : 0 ≤ ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ := norm_nonneg _
  have hhS : diam T * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ≤ |C| := by
    have := mul_le_mul_of_nonneg_left hBs' hh.le
    rwa [show diam T * (|C| / diam T) = |C| by field_simp] at this
  have h1 := norm_apply_le_refPull T (fun x => isDeg_of_mem_p1MinusForms hz x) x
  calc diam T ^ k * |z x s| ≤ diam T ^ k * ‖z x‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hh.le k)
        rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (z x) s
    _ ≤ diam T ^ k * (2 ^ n * (n * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) ^ k *
          ‖v (refMapInv T x)‖) := mul_le_mul_of_nonneg_left h1 (pow_nonneg hh.le k)
    _ = 2 ^ n * (n * (diam T * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖)) ^ k *
          ‖v (refMapInv T x)‖ := by ring
    _ ≤ 2 ^ n * (n * |C|) ^ k * (2 * (B₀ * N) * D) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left hhS (Nat.cast_nonneg _)) k) (by positivity)) hvb
          (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Feec.FiniteElement
