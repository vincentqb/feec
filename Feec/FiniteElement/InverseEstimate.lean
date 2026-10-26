module

public import Feec.FiniteElement.WhitneyComplex
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Inverse estimates for Whitney forms on homothetic simplices

The lowest-order Whitney forms of every nondegenerate `n`-simplex are the **trimmed linear forms**
`P₁⁻Λᵏ = {x ↦ α + ι_x β}` (`whitneySpace_eq_p1MinusForms_of_isUnit`), a fixed
finite-dimensional space of **affine** form fields, `u(y) = u(0) + Σⱼ yⱼ (u(eⱼ) - u(0))`
(`isAffineField_of_mem_p1MinusForms`), whose traces on `k`-faces are constant (`affinePullback_univ_eq_of_mem_p1MinusForms`: the
pulled-back integrand of `∫_g u` is `k! ∫_g u`). The size of such a field is measured by its
**affine size** `affSize u = Σₛ (|u(0)ₛ| + Σⱼ |u(eⱼ)ₛ - u(0)ₛ|)`, which bounds it pointwise and
its Lipschitz constant (`IsAffineField.abs_le`, `IsAffineField.abs_sub_le`).

On a fixed reference simplex `K`, finite dimensionality makes the affine size comparable to
the `L²(K)` norm and to the face integrals (`exists_affSize_le_sqrt_integral`,
`exists_affSize_le_sum_dof`, from the norm comparison `exists_abs_le_mul_norm`). Transporting by
the homothety `y ↦ t + h y` (`affinePullback_scalarMat`: the pullback of a `k`-form is
`hᵏ u(t + h y)`; `abs_simplexIntegral_faceEnum_image`: face integrals are preserved up to
orientation; `integral_closedInterior_mapEquiv_boxMap`: `∫_T f = hⁿ ∫_K f(t + h ·)`) gives, for
`T = t + h K`, with constants depending only on `K` and `k`:

* **the local DOF estimate** `hᵏ sup_T |u| ≲ Σ_g |∫_g u|` over the faces of `T`
  (`exists_local_dof_bound`);
* **the local inverse estimates** `h^{n/2} sup_T |u| ≲ ‖u‖_{L²(T)}` and
  `h^{n/2} h Lip(u) ≲ ‖u‖_{L²(T)}` (`exists_local_inverse_bound`).

These are the inverse estimates behind the smoothed projections of [AFW2010], §5.5 and
[ChristiansenWinther2008]; on meshes whose simplices are homothetic to finitely many reference
simplices (Freudenthal meshes) they hold uniformly without a shape-regularity argument. The
module also records the minor bound `Σₛ |minorₛ| ≤ 2ⁿ k! aᵏ` for faces with edges bounded by `a`
(`sum_abs_wedgeProd_simplexMatrix_le`), the vertex criterion for faces of face-to-face meshes
(`SimplicialMesh.subset_vertexSet_of_mem`) and the bound of a glued field by its local `L²`
norms (`norm_sq_pieceL2_le`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.5 (inverse estimates for the smoothed projection)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3–5 (trimmed linear forms, Whitney forms and their degrees of freedom)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.2 (inverse
  inequalities)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh

variable {n : ℕ}

/-! ### Trimmed linear forms are affine -/

/-- A form field is **affine** if `u(y) = u(0) + Σⱼ yⱼ (u(eⱼ) - u(0))`. -/
def IsAffineField (u : FormField n) : Prop :=
  ∀ y, u y = u 0 + ∑ j, y j • (u (Pi.single j 1) - u 0)

theorem interior_eq_sum_single_smul (y : Fin n → ℝ) (β : Finset (Fin n) → ℝ) :
    interior y β = ∑ j, y j • interior (Pi.single j 1) β := by
  funext s
  simp only [interior_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l]
  · simp; ring
  · intro j _ hj; simp [Ne.symm hj]
  · simp

theorem isAffineField_of_mem_p1MinusForms {k : ℕ} {u : FormField n}
    (hu : u ∈ p1MinusForms n k) : IsAffineField u := by
  induction hu using Submodule.span_induction with
  | mem w hw =>
    rcases hw with ⟨α, -, rfl⟩ | ⟨β, -, rfl⟩
    · intro y; simp
    · intro y
      have h0 : interior (0 : Fin n → ℝ) β = 0 := by
        funext s; simp [interior_apply]
      simp only [h0, sub_zero, zero_add]
      exact interior_eq_sum_single_smul y β
  | zero => intro y; simp
  | add w w' _ _ hw hw' =>
    intro y
    simp only [Pi.add_apply]
    rw [hw y, hw' y]
    simp only [add_sub_add_comm, smul_add, Finset.sum_add_distrib]
    abel
  | smul c w _ hw =>
    intro y
    simp only [Pi.smul_apply]
    rw [hw y]
    simp only [smul_add, ← smul_sub, Finset.smul_sum, smul_comm c]

theorem IsAffineField.sub_eq {u : FormField n} (hu : IsAffineField u) (y y' : Fin n → ℝ) :
    u y - u y' = ∑ j, (y j - y' j) • (u (Pi.single j 1) - u 0) := by
  rw [hu y, hu y']
  simp only [sub_smul, Finset.sum_sub_distrib]
  abel

/-- The **affine size** `Σₛ (|u(0)ₛ| + Σⱼ |u(eⱼ)ₛ - u(0)ₛ|)` of a form field. -/
def affSize (u : FormField n) : ℝ :=
  ∑ s, (|u 0 s| + ∑ j, |u (Pi.single j 1) s - u 0 s|)

theorem affSize_nonneg (u : FormField n) : 0 ≤ affSize u :=
  Finset.sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem le_affSize (u : FormField n) (s : Finset (Fin n)) :
    |u 0 s| + ∑ j, |u (Pi.single j 1) s - u 0 s| ≤ affSize u :=
  Finset.single_le_sum (f := fun s => |u 0 s| + ∑ j, |u (Pi.single j 1) s - u 0 s|)
    (fun _ _ => add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    (Finset.mem_univ s)

/-- Lipschitz bound of an affine field in the sup norm. -/
theorem IsAffineField.abs_sub_le {u : FormField n} (hu : IsAffineField u) (y y' : Fin n → ℝ)
    (s : Finset (Fin n)) : |u y s - u y' s| ≤ ‖y - y'‖ * affSize u := by
  have h := congrFun (hu.sub_eq y y') s
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |(y j - y' j) * (u (Pi.single j 1) s - u 0 s)|
      ≤ ∑ j, ‖y - y'‖ * |u (Pi.single j 1) s - u 0 s| := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have := norm_le_pi_norm (y - y') j
        rwa [Real.norm_eq_abs, Pi.sub_apply] at this
    _ = ‖y - y'‖ * ∑ j, |u (Pi.single j 1) s - u 0 s| := by rw [Finset.mul_sum]
    _ ≤ ‖y - y'‖ * affSize u := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact (le_add_of_nonneg_left (abs_nonneg _)).trans (le_affSize u s)

/-- Sup bound of an affine field. -/
theorem IsAffineField.abs_le {u : FormField n} (hu : IsAffineField u) (y : Fin n → ℝ)
    (s : Finset (Fin n)) : |u y s| ≤ (‖y‖ + 1) * affSize u := by
  have h := hu.abs_sub_le y 0 s
  rw [sub_zero] at h
  have h0 : |u 0 s| ≤ affSize u :=
    (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)).trans (le_affSize u s)
  calc |u y s| ≤ |u y s - u 0 s| + |u 0 s| := by
        have := abs_sub_abs_le_abs_sub (u y s) (u 0 s); linarith
    _ ≤ ‖y‖ * affSize u + affSize u := add_le_add h h0
    _ = (‖y‖ + 1) * affSize u := by ring

/-- **Trimmed linear top forms are constant**: `P₁⁻Λᵏ(ℝᵏ) = P₀Λᵏ(ℝᵏ)`. -/
theorem eq_const_of_mem_p1MinusForms_self {k : ℕ} {w : FormField k}
    (hw : w ∈ p1MinusForms k k) (x : Fin k → ℝ) : w x = w 0 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    rcases hw with ⟨α, -, rfl⟩ | ⟨β, hβ, rfl⟩
    · rfl
    · have hβ0 : β = 0 := by
        funext t
        exact hβ t (by have := Finset.card_le_univ t; simp at this; omega)
      subst hβ0
      funext s; simp [interior_apply]
  | zero => rfl
  | add w w' _ _ hw hw' => simp [hw, hw']
  | smul c w _ hw => simp [hw]


/-- **The Whitney forms of a nondegenerate simplex are the trimmed linear forms**:
`P₁⁻Λᵏ(T) = P₀Λᵏ + κ H₀Λ^{k+1}`, independently of `T`. Stated for vertex families `p` with
invertible edge matrix; for an `Affine.Simplex` see
`Feec.FiniteElement.whitneySpace_eq_p1MinusForms`. -/
theorem whitneySpace_eq_p1MinusForms_of_isUnit {p : Fin (n + 1) → Fin n → ℝ}
    (hp : IsUnit (edgeMatrix p).det) (k : ℕ) : whitneySpace p k = p1MinusForms n k := by
  have hle := whitneySpace_le_p1MinusForms p k
  have hle' := p1MinusForms_le_whitneySpace_refVertex (n := n) k
  have hfd : FiniteDimensional ℝ (p1MinusForms n k) :=
    Submodule.finiteDimensional_of_le hle'
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [finrank_whitneySpace hp]
  calc Module.finrank ℝ (p1MinusForms n k)
      ≤ Module.finrank ℝ (whitneySpace (refVertex n) k) := Submodule.finrank_mono hle'
    _ = _ := by
        rw [finrank_whitneySpace (by rw [edgeMatrix_refVertex, Matrix.det_one]; exact isUnit_one)]

/-! ### Finite-dimensional norm comparison -/

/-- **Norm comparison in finite dimension**: a linear functional on a finite-dimensional space
is bounded by any injective linear map into a normed space. -/
theorem exists_abs_le_mul_norm {V E : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : V →ₗ[ℝ] E) (hι : Function.Injective ι)
    (ℓ : V →ₗ[ℝ] ℝ) : ∃ A, 0 ≤ A ∧ ∀ v, |ℓ v| ≤ A * ‖ι v‖ := by
  set e := LinearEquiv.ofInjective ι hι
  set ℓ' : LinearMap.range ι →ₗ[ℝ] ℝ := ℓ ∘ₗ e.symm.toLinearMap
  have hc : Continuous ℓ' := LinearMap.continuous_of_finiteDimensional ℓ'
  set L : LinearMap.range ι →L[ℝ] ℝ := ⟨ℓ', hc⟩
  refine ⟨‖L‖, ContinuousLinearMap.opNorm_nonneg L, fun v => ?_⟩
  have h1 : ℓ v = L (e v) := by
    change ℓ v = ℓ (e.symm (e v)); rw [LinearEquiv.symm_apply_apply]
  have h2 : ‖(e v : LinearMap.range ι)‖ = ‖ι v‖ := by
    rw [← Submodule.norm_coe]; rfl
  rw [h1, ← Real.norm_eq_abs, ← h2]
  exact L.le_opNorm _

/-- Finitely many functionals at once. -/
theorem exists_abs_le_mul_norm_of_finite {V E ι' : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι']
    (ι : V →ₗ[ℝ] E) (hι : Function.Injective ι) (ℓ : ι' → V →ₗ[ℝ] ℝ) :
    ∃ A, 0 ≤ A ∧ ∀ v j, |ℓ j v| ≤ A * ‖ι v‖ := by
  choose A hA0 hA using fun j => exists_abs_le_mul_norm ι hι (ℓ j)
  refine ⟨∑ j, A j, Finset.sum_nonneg fun j _ => hA0 j, fun v j => (hA j v).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hA0 j) (Finset.mem_univ j))
    (norm_nonneg _)

/-! ### Pullback by a homothety -/

theorem wedgeProd_smul {ι d : Type*} [LinearOrder ι] [LinearOrder d] (c : ℝ) (θ : ι → d → ℝ)
    (s : Finset ι) : wedgeProd (c • θ) s = c ^ #s • wedgeProd θ s := by
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h' => lt_irrefl a (ha a h')
    rw [wedgeProd_insert_of_lt _ ha, wedgeProd_insert_of_lt _ ha, ih, Pi.smul_apply,
      wedge_smul_left, wedge_smul, smul_smul, card_insert_of_notMem has, pow_succ, mul_comm]

/-- The diagonal matrix `h I`. -/
def scalarMat (n : ℕ) (h : ℝ) : Fin n → Fin n → ℝ := fun i j => if i = j then h else 0

theorem affine_scalarMat (h : ℝ) (t y : Fin n → ℝ) : affine (scalarMat n h) t y = h • y + t := by
  funext i
  rw [affine_apply]
  simp [scalarMat]

theorem pullback_scalarMat {k : ℕ} (h : ℝ) {α : Finset (Fin n) → ℝ} (hα : IsDeg k α) :
    pullback (scalarMat n h) α = h ^ k • α := by
  have e : scalarMat n h = h • fun i j : Fin n => if i = j then (1 : ℝ) else 0 := by
    funext i j; simp [scalarMat]
  rw [e]
  conv_rhs => rw [← pullback_id α]
  simp only [pullback, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [wedgeProd_smul, smul_smul]
  by_cases hs : #s = k
  · rw [hs, mul_comm]
  · rw [hα s hs]; simp

/-- **Pullback of a `k`-form by the homothety `y ↦ h y + t`**: `(F^* ω)(y) = hᵏ ω(h y + t)`. -/
theorem affinePullback_scalarMat {k : ℕ} (h : ℝ) (t : Fin n → ℝ) {ω : FormField n}
    (hω : ∀ x, IsDeg k (ω x)) (y : Fin n → ℝ) :
    affinePullback (scalarMat n h) t ω y = h ^ k • ω (h • y + t) := by
  rw [affinePullback_apply, affine_scalarMat, pullback_scalarMat h (hω _)]


/-! ### Face integrals under homotheties; traces on faces -/

/-- **Face integrals under a homothety** `H y = h y + t`, `h ≠ 0`: up to the orientation sign,
`∫_{H g} ω = ∫_g H^* ω`. -/
theorem abs_simplexIntegral_faceEnum_image {k : ℕ} {h : ℝ} (hh : h ≠ 0) (t : Fin n → ℝ)
    {g : Finset (Fin n → ℝ)} (hg : g.card = k + 1) (ω : FormField n) :
    |simplexIntegral (faceEnum (g.image fun y => t + h • y) (k + 1)) ω| =
      |simplexIntegral (faceEnum g (k + 1)) (affinePullback (scalarMat n h) t ω)| := by
  classical
  set H : (Fin n → ℝ) → Fin n → ℝ := fun y => t + h • y
  have hH : Function.Injective H := fun y y' e => by
    have : h • y = h • y' := by simpa [H] using e
    exact smul_right_injective _ hh this
  have hcard : (g.image H).card = k + 1 := by rw [Finset.card_image_of_injective _ hH, hg]
  have hq := injective_faceEnum hg
  have hrange : Set.range (H ∘ faceEnum g (k + 1)) = Set.range (faceEnum (g.image H) (k + 1)) := by
    rw [Set.range_comp, range_faceEnum hg, range_faceEnum hcard, Finset.coe_image]
  obtain ⟨ε, hε, hεw⟩ := exists_sign_simplexIntegral_eq (hH.comp hq) (injective_faceEnum hcard)
    hrange
  have h1 := hεw ω
  have h2 : simplexIntegral (H ∘ faceEnum g (k + 1)) ω =
      simplexIntegral (faceEnum g (k + 1)) (affinePullback (scalarMat n h) t ω) := by
    rw [← simplexIntegral_comp_affine]
    congr 1
    funext i
    rw [affine_scalarMat]
    exact add_comm _ _
  rw [← h2, h1, abs_mul]
  rcases hε with rfl | rfl <;> simp

/-- **The trace of a trimmed linear `k`-form on a `k`-simplex is constant**: the pulled-back
integrand of `∫_q u` is `k! ∫_q u` everywhere. -/
theorem affinePullback_univ_eq_of_mem_p1MinusForms {k : ℕ} {u : FormField n}
    (hu : u ∈ p1MinusForms n k) (q : Fin (k + 1) → Fin n → ℝ) (x : Fin k → ℝ) :
    affinePullback (simplexMatrix q) (q 0) u x univ = k.factorial * simplexIntegral q u := by
  have hw := affinePullback_mem_p1MinusForms (simplexMatrix q) (q 0) hu
  have hc := eq_const_of_mem_p1MinusForms_self hw
  rw [simplexIntegral]
  simp_rw [hc]
  rw [setIntegral_const, volume_real_refSimplex, smul_eq_mul]
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp


/-! ### Comparison of the affine size with other norms -/

/-- Evaluation `u ↦ u(y)ₛ` as a linear functional on a space of form fields. -/
def evalL (V : Submodule ℝ (FormField n)) (y : Fin n → ℝ) (s : Finset (Fin n)) : V →ₗ[ℝ] ℝ :=
  (LinearMap.proj s) ∘ₗ (LinearMap.proj y) ∘ₗ V.subtype

@[simp] theorem evalL_apply (V : Submodule ℝ (FormField n)) (y : Fin n → ℝ) (s : Finset (Fin n))
    (v : V) : evalL V y s v = (v : FormField n) y s := rfl

/-- The functionals entering `affSize`. -/
def affFun (V : Submodule ℝ (FormField n)) : Finset (Fin n) × Option (Fin n) → V →ₗ[ℝ] ℝ
  | (s, none) => evalL V 0 s
  | (s, some j) => evalL V (Pi.single j 1) s - evalL V 0 s

theorem affSize_eq_sum_affFun (V : Submodule ℝ (FormField n)) (v : V) :
    affSize (v : FormField n) = ∑ p, |affFun V p v| := by
  rw [affSize, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_option]
  rfl

/-- **The affine size is dominated by any injective linear map** on a finite-dimensional space
of form fields. -/
theorem exists_affSize_le {V : Submodule ℝ (FormField n)} [FiniteDimensional ℝ V] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : V →ₗ[ℝ] E) (hι : Function.Injective ι) :
    ∃ A, 0 ≤ A ∧ ∀ v : V, affSize (v : FormField n) ≤ A * ‖ι v‖ := by
  obtain ⟨A, hA0, hA⟩ := exists_abs_le_mul_norm_of_finite ι hι (affFun V)
  refine ⟨Fintype.card (Finset (Fin n) × Option (Fin n)) * A, by positivity, fun v => ?_⟩
  rw [affSize_eq_sum_affFun]
  calc ∑ p, |affFun V p v| ≤ ∑ _p : Finset (Fin n) × Option (Fin n), A * ‖ι v‖ :=
        Finset.sum_le_sum fun p _ => hA v p
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_assoc]

/-- An affine field vanishing on a nonempty open set vanishes. -/
theorem IsAffineField.eq_zero_of_eqOn {u : FormField n} (hu : IsAffineField u)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) {y₀ : Fin n → ℝ} (hy₀ : y₀ ∈ U)
    (h0 : ∀ y ∈ U, u y = 0) : u = 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU y₀ hy₀
  have hj : ∀ j, u (Pi.single j 1) - u 0 = 0 := by
    intro j
    have hmem : y₀ + (δ / 2) • (Pi.single j 1 : Fin n → ℝ) ∈ U := by
      refine hball ?_
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg
        (by positivity)]
      have : ‖(Pi.single j 1 : Fin n → ℝ)‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
      nlinarith
    have h := hu.sub_eq (y₀ + (δ / 2) • (Pi.single j 1 : Fin n → ℝ)) y₀
    rw [h0 _ hmem, h0 _ hy₀, sub_zero] at h
    have e : ∑ i, ((y₀ + (δ / 2) • (Pi.single j 1 : Fin n → ℝ)) i - y₀ i) •
        (u (Pi.single i 1) - u 0) = (δ / 2) • (u (Pi.single j 1) - u 0) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [hij]
      · simp
    rw [e] at h
    exact (smul_eq_zero.1 h.symm).resolve_left (by positivity)
  have hu0 : u 0 = 0 := by
    have := hu y₀
    simp only [hj, smul_zero, Finset.sum_const_zero, add_zero] at this
    rw [← this, h0 _ hy₀]
  have hj' : ∀ j, u (Pi.single j 1) = 0 := fun j => by
    have := hj j; rwa [hu0, sub_zero] at this
  funext y
  rw [hu y]
  simp [hj', hu0]

theorem IsAffineField.continuous {u : FormField n} (hu : IsAffineField u) : Continuous u := by
  have : u = fun y => u 0 + ∑ j, y j • (u (Pi.single j 1) - u 0) := funext hu
  rw [this]
  exact continuous_const.add (continuous_finsetSum _ fun j _ =>
    (continuous_apply j).smul continuous_const)


theorem continuous_apply_of_mem_p1MinusForms {k : ℕ} {u : FormField n}
    (hu : u ∈ p1MinusForms n k) (s : Finset (Fin n)) : Continuous fun y => u y s :=
  (continuous_apply s).comp (isAffineField_of_mem_p1MinusForms hu).continuous

theorem memLp_apply_of_mem_p1MinusForms {S : Set (Fin n → ℝ)} (hS : IsCompact S) {k : ℕ}
    (v : p1MinusForms n k) (s : Finset (Fin n)) :
    MemLp (fun y => (v : FormField n) y s) 2 (volume.restrict S) :=
  Domain.memLp_of_continuous hS.measurableSet hS.isBounded
    (continuous_apply_of_mem_p1MinusForms v.2 s)

/-- The `L²(S)` embedding of the trimmed linear forms (`S` compact). -/
def l2Embed {S : Set (Fin n → ℝ)} (hS : IsCompact S) (k : ℕ) :
    p1MinusForms n k →ₗ[ℝ] Domain.L2F ℝ S (Finset (Fin n)) where
  toFun v := Domain.toL2F fun s => memLp_apply_of_mem_p1MinusForms hS v s
  map_add' v w := by
    refine PiLp.ext fun s => ?_
    rw [PiLp.add_apply]
    exact MemLp.toLp_add (memLp_apply_of_mem_p1MinusForms hS v s)
      (memLp_apply_of_mem_p1MinusForms hS w s)
  map_smul' c v := by
    refine PiLp.ext fun s => ?_
    rw [PiLp.smul_apply]
    exact MemLp.toLp_const_smul c (memLp_apply_of_mem_p1MinusForms hS v s)

theorem norm_sq_l2Embed {S : Set (Fin n → ℝ)} (hS : IsCompact S) {k : ℕ} (v : p1MinusForms n k) :
    ‖l2Embed hS k v‖ ^ 2 = ∑ s, ∫ y in S, ((v : FormField n) y s) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (l2Embed hS k v) (Domain.toL2F _) = _
  rw [Domain.inner_toL2F]
  refine Finset.sum_congr rfl fun s _ => integral_congr_ae ?_
  have h := (memLp_apply_of_mem_p1MinusForms hS v s).coeFn_toLp
  filter_upwards [h] with y hy
  change (starRingEnd ℝ) ((memLp_apply_of_mem_p1MinusForms hS v s).toLp _ y) * _ = _
  rw [RCLike.conj_to_real, hy, sq]

theorem l2Embed_injective {S : Set (Fin n → ℝ)} (hS : IsCompact S) (hSi : (interior S).Nonempty)
    (k : ℕ) : Function.Injective (l2Embed hS k) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨y₀, hy₀⟩ := hSi
  have hs : ∀ s, ∀ y ∈ interior S, (v : FormField n) y s = 0 := by
    intro s
    have h0 : (l2Embed hS k v) s = 0 := by rw [hv]; rfl
    have h := (memLp_apply_of_mem_p1MinusForms hS v s).coeFn_toLp
    change (memLp_apply_of_mem_p1MinusForms hS v s).toLp _ = 0 at h0
    rw [h0] at h
    have hz := Lp.coeFn_zero ℝ 2 (volume.restrict S)
    have hae : (fun y => (v : FormField n) y s) =ᵐ[volume.restrict (interior S)] 0 :=
      ae_restrict_of_ae_restrict_of_subset interior_subset ((h.symm.trans hz))
    exact fun y hy => Measure.eqOn_open_of_ae_eq hae isOpen_interior
      (continuous_apply_of_mem_p1MinusForms v.2 s).continuousOn continuousOn_const hy
  have hu := isAffineField_of_mem_p1MinusForms v.2
  have := hu.eq_zero_of_eqOn isOpen_interior hy₀ fun y hy => funext fun s => hs s y hy
  exact Subtype.ext this


instance finiteDimensional_p1MinusForms (k : ℕ) : FiniteDimensional ℝ (p1MinusForms n k) :=
  Submodule.finiteDimensional_of_le (p1MinusForms_le_whitneySpace_refVertex k)

/-- **Reference inverse estimate**: on a compact `S` with nonempty interior, the affine size of a
trimmed linear form is bounded by its `L²(S)` norm. -/
theorem exists_affSize_le_sqrt_integral {S : Set (Fin n → ℝ)} (hS : IsCompact S)
    (hSi : (interior S).Nonempty) (k : ℕ) :
    ∃ A, 0 ≤ A ∧ ∀ v ∈ p1MinusForms n k,
      affSize v ≤ A * √(∑ s, ∫ y in S, (v y s) ^ 2) := by
  obtain ⟨A, hA0, hA⟩ := exists_affSize_le (l2Embed hS k) (l2Embed_injective hS hSi k)
  refine ⟨A, hA0, fun v hv => ?_⟩
  have h := hA ⟨v, hv⟩
  rwa [← norm_sq_l2Embed hS ⟨v, hv⟩, Real.sqrt_sq (norm_nonneg _)]

/-- **Reference DOF estimate**: on a simplex `K`, the affine size of a trimmed linear form is
bounded by its face integrals. -/
theorem exists_affSize_le_sum_dof (K : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ v ∈ p1MinusForms n k, affSize v ≤ B *
      ∑ p : Σ g : (vertexSet K).powerset, WhitneyDofIdx (g : Finset (Fin n → ℝ)) k,
        |simplexIntegral (faceEnum (p.1 : Finset (Fin n → ℝ)) (k + 1)) v| := by
  set ι := LinearMap.pi fun p : Σ g : (vertexSet K).powerset,
      WhitneyDofIdx (g : Finset (Fin n → ℝ)) k =>
    whitneyFaceDof (p.1 : Finset (Fin n → ℝ)) k ∘ₗ
      Submodule.inclusion (whitneySpace_le_contForms K.points k)
  have hι : Function.Injective ι := (isUnisolvent_whitneyFaceDof K k).injective
  obtain ⟨B, hB0, hB⟩ := exists_affSize_le ι hι
  refine ⟨B, hB0, fun v hv => ?_⟩
  have hv' : v ∈ whitneySpace K.points k := by
    rwa [whitneySpace_eq_p1MinusForms_of_isUnit (isUnit_det_edgeMatrix _)]
  refine (hB ⟨v, hv'⟩).trans (mul_le_mul_of_nonneg_left ?_ hB0)
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun p => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun p : Σ g : (vertexSet K).powerset,
      WhitneyDofIdx (g : Finset (Fin n → ℝ)) k =>
    |simplexIntegral (faceEnum (p.1 : Finset (Fin n → ℝ)) (k + 1)) v|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ p)


/-! ### Homothetic images of a reference simplex -/

theorem isDeg_of_mem_p1MinusForms {k : ℕ} {u : FormField n} (hu : u ∈ p1MinusForms n k)
    (x : Fin n → ℝ) : IsDeg k (u x) :=
  isDeg_of_mem_whitneySpace (p1MinusForms_le_whitneySpace_refVertex k hu) x

theorem coe_boxMap (t : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) :
    (boxMap t h hh : (Fin n → ℝ) → Fin n → ℝ) = fun y => t + h • y :=
  funext fun y => boxMap_apply t h hh y

theorem closedInterior_mapEquiv_boxMap (K : Affine.Simplex ℝ (Fin n → ℝ) n) (t : Fin n → ℝ)
    {h : ℝ} (hh : h ≠ 0) :
    (mapEquiv (boxMap t h hh) K).closedInterior = (fun y => t + h • y) '' K.closedInterior := by
  rw [closedInterior_mapEquiv, coe_boxMap]

/-- **Change of variables** for the homothety `y ↦ t + h y`, `h > 0`. -/
theorem integral_closedInterior_mapEquiv_boxMap (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    (t : Fin n → ℝ) {h : ℝ} (hh : 0 < h) (f : (Fin n → ℝ) → ℝ) :
    ∫ x in (mapEquiv (boxMap t h hh.ne') K).closedInterior, f x =
      h ^ n * ∫ y in K.closedInterior, f (t + h • y) := by
  rw [closedInterior_mapEquiv_boxMap]
  have hinj : Set.InjOn (fun y : Fin n → ℝ => t + h • y) K.closedInterior := fun y _ y' _ e => by
    have : h • y = h • y' := by simpa using e
    exact smul_right_injective _ hh.ne' this
  have hd : ∀ y ∈ K.closedInterior, HasFDerivWithinAt (fun y : Fin n → ℝ => t + h • y)
      (h • ContinuousLinearMap.id ℝ (Fin n → ℝ)) K.closedInterior y := fun y _ =>
    (((hasFDerivAt_id y).const_smul h).const_add t).hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume
    K.isClosed_closedInterior.measurableSet hd hinj]
  have hdet : |(h • ContinuousLinearMap.id ℝ (Fin n → ℝ)).det| = h ^ n := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul,
      ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one, Module.finrank_fin_fun,
      abs_of_pos (pow_pos hh n)]
  simp_rw [hdet, smul_eq_mul]
  rw [integral_const_mul]


theorem exists_norm_le_of_mem_closedInterior (K : Affine.Simplex ℝ (Fin n → ℝ) n) :
    ∃ R, 0 ≤ R ∧ ∀ y ∈ K.closedInterior, ‖y‖ ≤ R := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 K.isCompact_closedInterior.isBounded
  exact ⟨max R 0, le_max_right _ _, fun y hy => (hR y hy).trans (le_max_left _ _)⟩

theorem affinePullback_scalarMat_apply_add {k : ℕ} {h : ℝ} {t : Fin n → ℝ} {z : FormField n}
    (hz : z ∈ p1MinusForms n k) (y : Fin n → ℝ) (s : Finset (Fin n)) :
    affinePullback (scalarMat n h) t z y s = h ^ k * z (t + h • y) s := by
  rw [affinePullback_scalarMat h t (isDeg_of_mem_p1MinusForms hz) y, add_comm]; rfl

/-- **Local DOF estimate on homothetic simplices**: for `T = t + h K`, a trimmed linear form is
bounded on `T` by `h⁻ᵏ` times its face integrals over the faces of `T`, with a constant
depending only on `K` and `k`. -/
theorem exists_local_dof_bound (K : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {z : FormField n},
      z ∈ p1MinusForms n k → ∀ x ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior, ∀ s,
        h ^ k * |z x s| ≤ B * ∑ p : Σ g : (vertexSet K).powerset,
          WhitneyDofIdx (g : Finset (Fin n → ℝ)) k,
          |simplexIntegral (faceEnum ((p.1 : Finset (Fin n → ℝ)).image fun y => t + h • y)
            (k + 1)) z| := by
  obtain ⟨R, hR0, hR⟩ := exists_norm_le_of_mem_closedInterior K
  obtain ⟨B₀, hB₀, hB⟩ := exists_affSize_le_sum_dof K k
  refine ⟨(R + 1) * B₀, by positivity, fun {h} hh t z hz x hx s => ?_⟩
  rw [closedInterior_mapEquiv_boxMap] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hu := affinePullback_mem_p1MinusForms (scalarMat n h) t hz
  have hval := affinePullback_scalarMat_apply_add (h := h) (t := t) hz y s
  have hdof : ∀ p : Σ g : (vertexSet K).powerset, WhitneyDofIdx (g : Finset (Fin n → ℝ)) k,
      |simplexIntegral (faceEnum (p.1 : Finset (Fin n → ℝ)) (k + 1))
        (affinePullback (scalarMat n h) t z)| =
      |simplexIntegral (faceEnum ((p.1 : Finset (Fin n → ℝ)).image fun y => t + h • y) (k + 1))
        z| := fun p => (abs_simplexIntegral_faceEnum_image hh.ne' t p.2.2 z).symm
  have h1 := (isAffineField_of_mem_p1MinusForms hu).abs_le y s
  have h2 := hB _ hu
  simp_rw [hdof] at h2
  calc h ^ k * |z (t + h • y) s| = |affinePullback (scalarMat n h) t z y s| := by
        rw [hval, abs_mul, abs_of_nonneg (pow_nonneg hh.le k)]
    _ ≤ (‖y‖ + 1) * affSize (affinePullback (scalarMat n h) t z) := h1
    _ ≤ (R + 1) * (B₀ * _) := mul_le_mul (by linarith [hR y hy]) h2 (affSize_nonneg _)
        (by linarith)
    _ = _ := by ring


theorem sqrt_pow_eq {h : ℝ} (hh : 0 ≤ h) (m : ℕ) : √(h ^ m) = √h ^ m := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg h) m), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt hh]

/-- **Local inverse estimates on homothetic simplices**: for `T = t + h K` and a trimmed linear
form `z`, `h^{n/2} sup_T |z| ≲ ‖z‖_{L²(T)}` and `h^{n/2} h Lip(z) ≲ ‖z‖_{L²(T)}`, with a constant
depending only on `K` and `k`. -/
theorem exists_local_inverse_bound (K : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    ∃ A, 0 ≤ A ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {z : FormField n},
      z ∈ p1MinusForms n k →
        (∀ x ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior, ∀ s,
          √h ^ n * |z x s| ≤ A * √(∑ s, ∫ x in (mapEquiv (boxMap t h hh.ne') K).closedInterior,
            (z x s) ^ 2)) ∧
        (∀ x x' s, √h ^ n * h * |z x s - z x' s| ≤ A * ‖x - x'‖ *
          √(∑ s, ∫ x in (mapEquiv (boxMap t h hh.ne') K).closedInterior, (z x s) ^ 2)) := by
  obtain ⟨R, hR0, hR⟩ := exists_norm_le_of_mem_closedInterior K
  obtain ⟨A₀, hA₀, hA⟩ := exists_affSize_le_sqrt_integral K.isCompact_closedInterior
    (interior_closedInterior_nonempty K) k
  refine ⟨(R + 1) * A₀, by positivity, fun {h} hh t z hz => ?_⟩
  set T := mapEquiv (boxMap t h hh.ne') K
  set u := affinePullback (scalarMat n h) t z
  have hu : u ∈ p1MinusForms n k := affinePullback_mem_p1MinusForms (scalarMat n h) t hz
  have hval : ∀ y s, u y s = h ^ k * z (t + h • y) s := fun y s =>
    affinePullback_scalarMat_apply_add hz y s
  set L := ∑ s, ∫ x in T.closedInterior, (z x s) ^ 2
  set LK := ∑ s, ∫ y in K.closedInterior, (u y s) ^ 2
  have hT : ∀ s, ∫ x in T.closedInterior, (z x s) ^ 2 =
      h ^ n * ∫ y in K.closedInterior, (z (t + h • y) s) ^ 2 := fun s =>
    integral_closedInterior_mapEquiv_boxMap K t hh _
  have hrel : h ^ n * LK = (h ^ k) ^ 2 * L := by
    simp only [LK, L, hval, hT, mul_pow, integral_const_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => by ring
  have hLK : 0 ≤ LK := Finset.sum_nonneg fun s _ => setIntegral_nonneg
    K.isClosed_closedInterior.measurableSet fun y _ => sq_nonneg _
  have hL : 0 ≤ L := Finset.sum_nonneg fun s _ => setIntegral_nonneg
    T.isClosed_closedInterior.measurableSet fun y _ => sq_nonneg _
  have hkey : √h ^ n * √LK = h ^ k * √L := by
    rw [← sqrt_pow_eq hh.le, ← Real.sqrt_mul (pow_nonneg hh.le n), hrel,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hh.le k)]
  have hafs : affSize u ≤ A₀ * √LK := hA u hu
  have hsq : 0 ≤ √h ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  have hhk : 0 < h ^ k := pow_pos hh k
  constructor
  · intro x hx s
    have hx' := hx
    rw [closedInterior_mapEquiv_boxMap] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    have h1 := (isAffineField_of_mem_p1MinusForms hu).abs_le y s
    rw [hval, abs_mul, abs_of_pos hhk] at h1
    have h2 : h ^ k * (√h ^ n * |z (t + h • y) s|) ≤ h ^ k * ((R + 1) * A₀ * √L) := by
      calc h ^ k * (√h ^ n * |z (t + h • y) s|) = √h ^ n * (h ^ k * |z (t + h • y) s|) := by ring
        _ ≤ √h ^ n * ((‖y‖ + 1) * affSize u) := mul_le_mul_of_nonneg_left h1 hsq
        _ ≤ √h ^ n * ((R + 1) * (A₀ * √LK)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul (by linarith [hR y hy]) hafs
              (affSize_nonneg _) (by linarith)) hsq
        _ = (R + 1) * A₀ * (√h ^ n * √LK) := by ring
        _ = h ^ k * ((R + 1) * A₀ * √L) := by rw [hkey]; ring
    exact le_of_mul_le_mul_left h2 hhk
  · intro x x' s
    set y := h⁻¹ • (x - t)
    set y' := h⁻¹ • (x' - t)
    have hy : t + h • y = x := by simp [y, smul_smul, hh.ne']
    have hy' : t + h • y' = x' := by simp [y', smul_smul, hh.ne']
    have hyy : h * ‖y - y'‖ = ‖x - x'‖ := by
      have e : y - y' = h⁻¹ • (x - x') := by
        simp only [y, y', ← smul_sub]; congr 1; abel
      rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hh.le), ← mul_assoc,
        mul_inv_cancel₀ hh.ne', one_mul]
    have h1 := (isAffineField_of_mem_p1MinusForms hu).abs_sub_le y y' s
    rw [hval, hval, hy, hy', ← mul_sub, abs_mul, abs_of_pos hhk] at h1
    have h2 : h ^ k * (√h ^ n * h * |z x s - z x' s|) ≤ h ^ k * ((R + 1) * A₀ * ‖x - x'‖ * √L) := by
      calc h ^ k * (√h ^ n * h * |z x s - z x' s|) = √h ^ n * h * (h ^ k * |z x s - z x' s|) := by
            ring
        _ ≤ √h ^ n * h * (‖y - y'‖ * affSize u) :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg hsq hh.le)
        _ = ‖x - x'‖ * (√h ^ n * affSize u) := by rw [← hyy]; ring
        _ ≤ ‖x - x'‖ * (√h ^ n * (A₀ * √LK)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hafs hsq) (norm_nonneg _)
        _ = ‖x - x'‖ * A₀ * (√h ^ n * √LK) := by ring
        _ = ‖x - x'‖ * A₀ * (h ^ k * √L) := by rw [hkey]
        _ ≤ h ^ k * ((R + 1) * A₀ * ‖x - x'‖ * √L) := by
            have : 0 ≤ ‖x - x'‖ * A₀ * (h ^ k * √L) := by positivity
            nlinarith
    exact le_of_mul_le_mul_left h2 hhk


/-! ### Minors of the edge matrix of a face -/

/-- If the edge vectors of `q` have entries bounded by `a`, the `k × k` minors of its edge
matrix are bounded by `k! aᵏ`, so `Σₛ |minorₛ| ≤ 2ⁿ k! aᵏ`. -/
theorem sum_abs_wedgeProd_simplexMatrix_le {k : ℕ} {q : Fin (k + 1) → Fin n → ℝ} {a : ℝ}
    (ha0 : 0 ≤ a) (ha : ∀ i l, |simplexMatrix q i l| ≤ a) :
    ∑ s, |wedgeProd (simplexMatrix q) s univ| ≤ 2 ^ n * (k.factorial * a ^ k) := by
  have h1 : ∀ s : Finset (Fin n), |wedgeProd (simplexMatrix q) s univ| ≤ k.factorial * a ^ k := by
    intro s
    by_cases hs : #s = k
    · have hu : #(univ : Finset (Fin k)) = k := by simp
      rw [wedgeProd_apply_eq_det_submatrix (simplexMatrix q) hs hu]
      have := Matrix.det_le (abv := AbsoluteValue.abs) (x := a)
        (A := Matrix.of fun i j : Fin k => simplexMatrix q (s.orderEmbOfFin hs i)
          ((univ : Finset (Fin k)).orderEmbOfFin hu j)) fun i j => ha _ _
      simpa [Fintype.card_fin, nsmul_eq_mul] using this
    · rw [isDeg_wedgeProd (simplexMatrix q) s univ (by simpa using fun h => hs h.symm)]
      simp only [abs_zero]
      positivity
  calc ∑ s, |wedgeProd (simplexMatrix q) s univ| ≤ ∑ _s : Finset (Fin n), k.factorial * a ^ k :=
        Finset.sum_le_sum fun s _ => h1 s
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
        nsmul_eq_mul]; push_cast; ring

/-! ### Face-to-face meshes: faces through a point of a common simplex -/

/-- If a point `x = Σₐ λₐ qₐ` of a simplex `T` of a mesh, with positive weights on the distinct
vertices `qₐ` of `T`, lies in another simplex `T'`, then all `qₐ` are vertices of `T'`. -/
theorem SimplicialMesh.subset_vertexSet_of_mem {M : SimplicialMesh n} {T T' : Affine.Simplex ℝ
    (Fin n → ℝ) n} (hT : T ∈ M.simplices) (hT' : T' ∈ M.simplices) {k : ℕ}
    {q : Fin (k + 1) → Fin n → ℝ} (hq : Function.Injective q) (hqT : ∀ a, q a ∈ vertexSet T)
    {μ : Fin (k + 1) → ℝ} (hμ : ∀ a, 0 < μ a) (hμ1 : ∑ a, μ a = 1)
    (hx' : ∑ a, μ a • q a ∈ T'.closedInterior) (a : Fin (k + 1)) : q a ∈ vertexSet T' := by
  classical
  by_contra hqa
  set x := ∑ a, μ a • q a
  have hxT : x ∈ T.closedInterior := by
    rw [← convexHull_vertexSet]
    exact (convex_convexHull ℝ _).sum_mem (fun b _ => (hμ b).le) hμ1
      fun b _ => subset_convexHull ℝ _ (hqT b)
  have hmem : x ∈ convexHull ℝ ((vertexSet T : Set (Fin n → ℝ)) ∩ vertexSet T') := by
    rw [← M.inter_closedInterior T hT T' hT']; exact ⟨hxT, hx'⟩
  obtain ⟨i, hi⟩ := mem_vertexSet.1 (hqT a)
  have h0 := coord_eq_zero_of_mem_convexHull T (i := i)
    (Set.inter_subset_left.trans (coe_vertexSet T).subset) (fun h => hqa (hi ▸ h.2)) hmem
  have hcomb : x = Finset.univ.affineCombination ℝ q μ :=
    (Finset.univ.affineCombination_eq_linear_combination q μ hμ1).symm
  have hmap := Finset.map_affineCombination (s := Finset.univ) q μ hμ1 (T.affineBasis.coord i)
  rw [hcomb, hmap, Finset.affineCombination_eq_linear_combination _ _ _ hμ1] at h0
  have hc : ∀ b, T.affineBasis.coord i (q b) = if b = a then 1 else 0 := by
    intro b
    obtain ⟨j, hj⟩ := mem_vertexSet.1 (hqT b)
    split_ifs with hba
    · subst hba; rw [← hi]; exact T.coord_points_self i
    · have hij : i ≠ j := fun e => hba (hq (by rw [← hj, ← hi, e]))
      rw [← hj, ← Affine.Simplex.coe_affineBasis]
      exact T.affineBasis.coord_apply_ne hij
  simp only [Function.comp_apply, hc, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h0
  exact (hμ a).ne' h0


/-! ### The `L²` norm of a glued piecewise field -/

theorem norm_sq_eq_integral_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, ((f : α → ℝ) x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

theorem pieceFun_sq (M : SimplicialMesh n) (v : Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) :
    (pieceFun M v x) ^ 2 = ∑ T ∈ M.simplices,
      (interior T.closedInterior).indicator (fun x => (v T x) ^ 2) x := by
  by_cases hx : ∃ T ∈ M.simplices, x ∈ interior T.closedInterior
  · obtain ⟨T, hT, hxT⟩ := hx
    rw [pieceFun_of_mem_interior M v hT hxT, Finset.sum_eq_single T, indicator_of_mem hxT]
    · intro T' hT' hne
      exact indicator_of_notMem (Set.disjoint_left.1
        (M.pairwise_disjoint_interior hT hT' hne.symm) hxT) _
    · exact fun h => absurd hT h
  · push Not at hx
    rw [pieceFun, Finset.sum_eq_zero fun T hT => indicator_of_notMem (hx T hT) _,
      Finset.sum_eq_zero fun T hT => indicator_of_notMem (hx T hT) _]
    simp

/-- **The squared norm of a glued field is at most the sum of the local squared norms.** -/
theorem norm_sq_pieceL2_le (M : SimplicialMesh n) (S : Set (Fin n → ℝ)) {ι : Type*} [Fintype ι]
    (v : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → ℝ)
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i)) :
    ‖pieceL2 M S v hv‖ ^ 2 ≤
      ∑ T ∈ M.simplices, ∑ i, ∫ x in T.closedInterior, (v T i x) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_sq_eq_integral_sq]
  have hint : ∀ T ∈ M.simplices, Integrable
      ((interior T.closedInterior).indicator fun x => (v T i x) ^ 2) := fun T hT =>
    (integrable_indicator_iff isOpen_interior.measurableSet).2
      ((((hv T hT i).pow 2).continuousOn.integrableOn_compact T.isCompact_closedInterior).mono_set
        interior_subset)
  have hsum : Integrable fun x => ∑ T ∈ M.simplices,
      (interior T.closedInterior).indicator (fun x => (v T i x) ^ 2) x :=
    integrable_finsetSum _ hint
  calc ∫ x, ((pieceL2 M S v hv i : (Fin n → ℝ) → ℝ) x) ^ 2 ∂volume.restrict S
      = ∫ x in S, (pieceFun M (fun T => v T i) x) ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_pieceL2 M S v hv i] with x hx
        rw [hx]
    _ = ∫ x in S, ∑ T ∈ M.simplices,
          (interior T.closedInterior).indicator (fun x => (v T i x) ^ 2) x := by
        simp_rw [pieceFun_sq]
    _ ≤ ∫ x, ∑ T ∈ M.simplices,
          (interior T.closedInterior).indicator (fun x => (v T i x) ^ 2) x :=
        setIntegral_le_integral hsum (Filter.Eventually.of_forall fun x =>
          Finset.sum_nonneg fun T _ => indicator_nonneg (fun x _ => sq_nonneg _) x)
    _ = ∑ T ∈ M.simplices, ∫ x in interior T.closedInterior, (v T i x) ^ 2 := by
        rw [integral_finsetSum _ hint]
        refine Finset.sum_congr rfl fun T _ => integral_indicator isOpen_interior.measurableSet
    _ ≤ _ := by
        refine Finset.sum_le_sum fun T hT => setIntegral_mono_set
          (((hv T hT i).pow 2).continuousOn.integrableOn_compact T.isCompact_closedInterior)
          (Filter.Eventually.of_forall fun x => sq_nonneg _)
          (Filter.Eventually.of_forall interior_subset)

end Feec.FiniteElement
