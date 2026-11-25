module

public import Feec.FiniteElement.PolyComplex
public import Feec.FiniteElement.PolyInterpolation
public import Feec.FiniteElement.TensorElement

/-!
# The weak-symmetry maps `S⁰ = I` and `S¹ = 2 vskw` in the language of forms

The connecting maps of the BGG complex (4.16) of [QuennevilleBelair2015], §5.3, between the de
Rham complex and its vector-valued copy `ℝⁿ ⊗ Λ`, are the restrictions to degrees `0` and `1` of

`S v = Σᵢ dxᵢ ∧ vᵢ` (`coordWedgeField`), for `v = (v₁, …, vₙ)` a vector of `k`-forms,

that is `S⁰ψ = Σᵢ ψᵢ dxᵢ` on vector `0`-forms (the identity `S₀ = I` on vector proxies,
`coordWedgeSum_singleton`) and `S¹v = Σᵢ dxᵢ ∧ vᵢ` on vector `1`-forms. With rows `vᵢ = Σⱼ uᵢⱼ dxⱼ`,
`(S¹v)_{ab} = u_{ab} − u_{ba}` (`coordWedgeSum_pair`): on vector proxies `S¹ = 2 vskw`,
`(S₁u)ᵢ = u_{i+1,i+2} − u_{i+2,i+1}`, the operator of `Feec.Domain.skwCurlOp`
and of `Feec.Models.BoundedDomain.skwL`. This choice of signs gives the thesis' anticommutation

`d S = −S d` (`extDeriv_coordWedgeField`),

since `d(dxᵢ ∧ vᵢ) = −dxᵢ ∧ dvᵢ`; in degree `0` it is `curl S₀ = −S₁ grad`.

## Main results

* **Algebra.** `isDeg_coordWedgeSum` (degree `k ↦ k + 1`), `coordWedgeSum_singleton` (`S₀ = I`),
  `coordWedgeSum_pair` (`(S¹v)_{ab} = v_{a,b} − v_{b,a}`, so `S₁ = 2 vskw`);
  `pullback_coordWedgeSum`: `B^*(S v) = Σᵢ (Bᵀeᵢ) ∧ B^*vᵢ`, so `S` commutes with the pullback by a
  dilation `x ↦ c x + t` up to the factor `c` (`affinePullback_scalarMat_coordWedgeField`).
* **Analysis.** `extDeriv_coordWedgeField` (`d S = −S d` pointwise), `contDiff_coordWedgeField`.
* **`L²` realization.** `wsL2 k : L²(Ω; Λᵏ)ⁿ → L²(Ω; Λᵏ⁺¹)` (bounded, `norm_wsL2_sq_le`:
  `‖S v‖² ≤ (k + 1) ‖v‖²`, adjoint `wsL2Adj`) maps `D(d_min)ⁿ` into `D(d_min)` and `D(d_max)ⁿ`
  into `D(d_max)` with `d S = −S d` (`wsL2_mem_minimal`, `wsL2_mem_maximal`); since `S` is a
  constant-coefficient map, it commutes with mollification (the smoothing form
  `Feec.Models.Cube.WeakSymmetry.smoothForm_wsL2` lives in `Models`).
* **Finite element level.** For a polynomial family `S` whose degree-`k` test spaces on
  `(k + 1)`-faces contain the constant `1`-forms (`PolySeq.ConstOneTest`), the DOFs of the lowest-order family of `S v`
  are combinations of the DOFs of `v` (`PolySeq.dof_comp_coordWedgeC_mem_span`); this gives
  `S_h = Π' S` on `Vₕ ⊗ ℝⁿ` (`PolySeq.wsPiecewise`, `PolySeq.wsGlobal`, `PolySeq.wsGlobal₀`:
  vanishing boundary DOFs are preserved), **Prop 5.7, adapted** `Π' S Π̃ = Π' S`
  (`PolySeq.wsGlobal_tensorInterp`), the
  **discrete anticommutation** `d S_h = −S_h d` (`PolySeq.dPiecewise_wsPiecewise`), and
  **`S₀,ₕ` onto `P₁⁻Λ̊¹`** (`PolySeq.wsGlobal₀_surjective`). The interpolants coincide with the
  `Feec.FiniteElement.LocalDof` interpolants (`PolySeq.localInterp_eq_polyMinusInterp`).
* **Table 5.1.** `PolySeq.bggS0h`, `PolySeq.bggS1h` (`P₂Λ⁰ ⊗ ℝⁿ → P₁⁻Λ¹`, `P₂⁻Λ¹ ⊗ ℝⁿ → P₁⁻Λ²`),
  `PolySeq.bggS0h₀_surjective`, `PolySeq.bggS0h_tensorInterp` (`Π¹S⁰Π̃⁰ = Π¹S⁰`; the case `k = 1`,
  `Π²S¹Π̃¹ = Π²S¹`, is `PolySeq.wsGlobal_tensorInterp`).
* **Smoothed pairs.** `Feec.HilbertComplex.Subcomplex.CommutingMap.toCochainProjection_comp_toCochainProjection`:
  if `Q 𝒮 = c A Q̃` (from `R 𝒮 = c 𝒮 R̃` and Prop 5.7), the smoothed projections satisfy
  `π 𝒮 π̃ = π 𝒮`, the compatibility `Feec.BGG.Discrete.Compatible`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3 (the maps `S₀ = I`, `S₁ = vskw` of the complex (4.16), here `S₁ = 2 vskw`; Prop 5.7)
* [D. N. Arnold, R. S. Falk, R. Winther, *Mixed finite element methods for linear elasticity with weakly imposed symmetry*][AFW2007]
  (the maps `S` of weakly imposed symmetry)
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021] (BGG connecting maps)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (exterior algebra, pullbacks, traces)

Bibliography: [references.bib](../../docs/references.bib)
-/

open MeasureTheory Set Finset
open scoped ContDiff

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh Feec.Domain

variable {n : ℕ}

/-! ### The fibre map `v ↦ Σᵢ dxᵢ ∧ vᵢ` -/

section Fibre

/-- **The weak-symmetry map on fibres**: `(vᵢ)ᵢ ↦ Σᵢ dxᵢ ∧ vᵢ`. -/
def coordWedgeSum (v : Fin n → Finset (Fin n) → ℝ) : Finset (Fin n) → ℝ :=
  ∑ i, wedge (Pi.single i 1) (v i)

theorem coordWedgeSum_apply (v : Fin n → Finset (Fin n) → ℝ) (s : Finset (Fin n)) :
    coordWedgeSum v s = ∑ i, ∑ j ∈ s, sgn j s * (Pi.single i (1 : ℝ) : Fin n → ℝ) j *
      v i (s.erase j) := by
  simp [coordWedgeSum, Finset.sum_apply, wedge_apply]

theorem coordWedgeSum_add (v w : Fin n → Finset (Fin n) → ℝ) :
    coordWedgeSum (v + w) = coordWedgeSum v + coordWedgeSum w := by
  simp [coordWedgeSum, wedge_add, Finset.sum_add_distrib]

theorem coordWedgeSum_smul (c : ℝ) (v : Fin n → Finset (Fin n) → ℝ) :
    coordWedgeSum (c • v) = c • coordWedgeSum v := by
  simp [coordWedgeSum, wedge_smul, Finset.smul_sum]

theorem coordWedgeSum_zero : coordWedgeSum (0 : Fin n → Finset (Fin n) → ℝ) = 0 := by
  simp [coordWedgeSum]

theorem coordWedgeSum_sum {β : Type*} (u : Finset β) (v : β → Fin n → Finset (Fin n) → ℝ) :
    coordWedgeSum (∑ b ∈ u, v b) = ∑ b ∈ u, coordWedgeSum (v b) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [coordWedgeSum_zero]
  | insert a u ha ih => rw [sum_insert ha, sum_insert ha, coordWedgeSum_add, ih]

/-- The fibre map as a linear map. -/
def coordWedgeSumₗ : (Fin n → Finset (Fin n) → ℝ) →ₗ[ℝ] (Finset (Fin n) → ℝ) where
  toFun := coordWedgeSum
  map_add' := coordWedgeSum_add
  map_smul' := coordWedgeSum_smul

/-- `S` raises the form degree by one. -/
theorem isDeg_coordWedgeSum {k : ℕ} {v : Fin n → Finset (Fin n) → ℝ} (hv : ∀ i, IsDeg k (v i)) :
    IsDeg (k + 1) (coordWedgeSum v) := fun s hs => by
  rw [coordWedgeSum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i _ => (hv i).wedge _ s hs

/-- **`S₀ = I`**: on vector `0`-forms, `(S⁰ψ)_{{j}} = ψⱼ`. -/
theorem coordWedgeSum_singleton {v : Fin n → Finset (Fin n) → ℝ} (j : Fin n) :
    coordWedgeSum v {j} = v j ∅ := by
  rw [coordWedgeSum_apply]
  simp only [Finset.sum_singleton, Finset.erase_singleton]
  have : sgn j ({j} : Finset (Fin n)) = (1 : ℝ) := by simp [sgn, Finset.filter_singleton]
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [Ne.symm hij]) (by simp)]
  simp [this]

/-- **`(S¹v)_{ab} = v_{a,b} − v_{b,a}`** for `a < b`: the coefficient of `dx_a ∧ dx_b` of
`Σᵢ dxᵢ ∧ vᵢ` (with `(vᵢ)_{{j}} = uᵢⱼ`). -/
theorem coordWedgeSum_pair {v : Fin n → Finset (Fin n) → ℝ} {a b : Fin n} (hab : a < b) :
    coordWedgeSum v {a, b} = v a {b} - v b {a} := by
  have hne : a ≠ b := hab.ne
  rw [coordWedgeSum_apply, Finset.sum_comm, Finset.sum_pair hne]
  have h1 : sgn a ({a, b} : Finset (Fin n)) = (1 : ℝ) := by
    simp [sgn, Finset.filter_insert, Finset.filter_singleton, not_lt_of_gt hab]
  have h2 : sgn b ({a, b} : Finset (Fin n)) = (-1 : ℝ) := by
    simp [sgn, Finset.filter_insert, Finset.filter_singleton, hab]
  have e1 : ({a, b} : Finset (Fin n)).erase a = {b} := by
    rw [Finset.erase_insert (by simp [hne])]
  have e2 : ({a, b} : Finset (Fin n)).erase b = {a} := by
    rw [Finset.pair_comm, Finset.erase_insert (by simp [hne.symm])]
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [Ne.symm hi]) (by simp),
    Finset.sum_eq_single b (fun i _ hi => by simp [Ne.symm hi]) (by simp),
    h1, h2, e1, e2]
  simp
  ring

/-- **The pullback of `S v`**: `B^*(Σᵢ dxᵢ ∧ vᵢ) = Σᵢ (Bᵀeᵢ) ∧ B^*vᵢ`. -/
theorem pullback_coordWedgeSum {m : ℕ} (B : Fin n → Fin m → ℝ) (v : Fin n → Finset (Fin n) → ℝ) :
    pullback B (coordWedgeSum v) = ∑ i, wedge (B i) (pullback B (v i)) := by
  rw [coordWedgeSum, pullback_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pullback_wedge]
  congr 1
  funext l
  simp [covPullback, Pi.single_apply]

end Fibre

/-! ### The map on form fields -/

section Field

/-- **The weak-symmetry map on form fields** `S v = Σᵢ dxᵢ ∧ vᵢ`: `S⁰` on vector `0`-forms, `S¹`
on vector `1`-forms ([QuennevilleBelair2015], §5.3, with `S₁ = 2 vskw`). -/
def coordWedgeField (v : Fin n → FormField n) : FormField n := fun x => coordWedgeSum fun i => v i x

theorem coordWedgeField_apply (v : Fin n → FormField n) (x : Fin n → ℝ) :
    coordWedgeField v x = coordWedgeSum fun i => v i x := rfl

theorem coordWedgeField_add (v w : Fin n → FormField n) :
    coordWedgeField (v + w) = coordWedgeField v + coordWedgeField w := by
  funext x
  exact coordWedgeSum_add (fun i => v i x) (fun i => w i x)

theorem coordWedgeField_smul (c : ℝ) (v : Fin n → FormField n) :
    coordWedgeField (c • v) = c • coordWedgeField v := by
  funext x
  exact coordWedgeSum_smul c (fun i => v i x)

theorem isDeg_coordWedgeField {k : ℕ} {v : Fin n → FormField n} (hv : ∀ i x, IsDeg k (v i x))
    (x : Fin n → ℝ) : IsDeg (k + 1) (coordWedgeField v x) :=
  isDeg_coordWedgeSum fun i => hv i x

theorem coordWedgeField_eq_comp (v : Fin n → FormField n) :
    coordWedgeField v = fun x => (LinearMap.toContinuousLinearMap
      (coordWedgeSumₗ : (Fin n → Finset (Fin n) → ℝ) →ₗ[ℝ] _)) fun i => v i x := rfl

theorem contDiff_coordWedgeField {r : WithTop ℕ∞} {v : Fin n → FormField n}
    (hv : ∀ i, ContDiff ℝ r (v i)) : ContDiff ℝ r (coordWedgeField v) := by
  rw [coordWedgeField_eq_comp]
  exact (ContinuousLinearMap.contDiff _).comp (contDiff_pi.2 hv)

theorem continuous_coordWedgeField {v : Fin n → FormField n} (hv : ∀ i, Continuous (v i)) :
    Continuous (coordWedgeField v) := by
  rw [coordWedgeField_eq_comp]
  exact (ContinuousLinearMap.continuous _).comp (continuous_pi hv)

theorem partialDeriv_const_mul_apply {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) (j : Fin n) :
    partialDeriv j (fun y => c * f y) x = c * partialDeriv j f x :=
  partialDeriv_const_smul hf c j

/-- The partial derivatives of `S v` are `S` of the partial derivatives. -/
theorem partialDerivForm_coordWedgeField {v : Fin n → FormField n} {x : Fin n → ℝ}
    (hv : ∀ i, DifferentiableAt ℝ (v i) x) (j : Fin n) :
    partialDerivForm j (coordWedgeField v) x =
      coordWedgeSum fun i => partialDerivForm j (v i) x := by
  have hc : ∀ i t, DifferentiableAt ℝ (fun y => v i y t) x := fun i t =>
    differentiableAt_pi.1 (hv i) t
  funext s
  simp only [partialDerivForm, coordWedgeField_apply, coordWedgeSum_apply]
  rw [partialDeriv_sum _ (fun i _ => DifferentiableAt.fun_sum fun l _ =>
    (hc i _).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [partialDeriv_sum _ (fun l _ => (hc i _).const_mul _)]
  exact Finset.sum_congr rfl fun l _ => partialDeriv_const_mul_apply (hc i _) _ j

/-- **The anticommutation `d S = −S d`**: `d(Σᵢ dxᵢ ∧ vᵢ) = −Σᵢ dxᵢ ∧ dvᵢ`, at every point where
the `vᵢ` are differentiable ([QuennevilleBelair2015], §5.3: `curl S₀ = −S₁ grad`). -/
theorem extDeriv_coordWedgeField {v : Fin n → FormField n} {x : Fin n → ℝ}
    (hv : ∀ i, DifferentiableAt ℝ (v i) x) :
    extDeriv (coordWedgeField v) x = -coordWedgeField (fun i => extDeriv (v i)) x := by
  rw [extDeriv_eq_sum_wedge, coordWedgeField_apply]
  simp_rw [partialDerivForm_coordWedgeField hv, extDeriv_eq_sum_wedge, coordWedgeSum, wedge_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => eq_neg_of_add_eq_zero_left (wedge_wedge_add_wedge_wedge _ _ _)

/-- `d S = −S d` for `C¹` fields. -/
theorem extDeriv_coordWedgeField_eq {v : Fin n → FormField n} (hv : ∀ i, ContDiff ℝ 1 (v i)) :
    extDeriv (coordWedgeField v) = -coordWedgeField (fun i => extDeriv (v i)) :=
  funext fun x => extDeriv_coordWedgeField fun i => (hv i).differentiable one_ne_zero x

/-- **The pullback of `S v` by an affine map**: `F^*(S v) = Σᵢ (Bᵀeᵢ) ∧ F^*vᵢ`. -/
theorem affinePullback_coordWedgeField {m : ℕ} (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ)
    (v : Fin n → FormField n) (x : Fin m → ℝ) :
    affinePullback B b (coordWedgeField v) x =
      ∑ i, wedge (B i) (affinePullback B b (v i) x) := by
  rw [affinePullback_apply, coordWedgeField_apply, pullback_coordWedgeSum]
  rfl

/-- **`S` commutes with the pullback by a dilation up to the factor `c`**:
`(x ↦ c x + t)^*(S v) = c S((x ↦ c x + t)^* v)`. -/
theorem affinePullback_scalarMat_coordWedgeField (c : ℝ) (t : Fin n → ℝ) (v : Fin n → FormField n) :
    affinePullback (scalarMat n c) t (coordWedgeField v) =
      c • coordWedgeField fun i => affinePullback (scalarMat n c) t (v i) := by
  funext x
  rw [affinePullback_coordWedgeField, Pi.smul_apply, coordWedgeField_apply, coordWedgeSum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← wedge_smul_left]
  congr 1
  funext l
  simp [scalarMat, Pi.single_apply, eq_comm]

/-- `S` on continuous forms. -/
def coordWedgeC : (Fin n → contForms n) →ₗ[ℝ] contForms n where
  toFun v := ⟨coordWedgeField fun i => v i, continuous_coordWedgeField fun i => (v i).2⟩
  map_add' v w := Subtype.ext (coordWedgeField_add (fun i => v i) fun i => w i)
  map_smul' c v := Subtype.ext (coordWedgeField_smul c fun i => v i)

@[simp] theorem coe_coordWedgeC (v : Fin n → contForms n) :
    (coordWedgeC v : FormField n) = coordWedgeField fun i => v i := rfl

/-- `S` on `C¹` forms. -/
def coordWedgeC1 : (Fin n → c1Forms n) →ₗ[ℝ] c1Forms n where
  toFun v := ⟨coordWedgeField fun i => v i,
    contDiff_coordWedgeField fun i => mem_c1Forms.1 (v i).2⟩
  map_add' v w := Subtype.ext (coordWedgeField_add (fun i => v i) fun i => w i)
  map_smul' c v := Subtype.ext (coordWedgeField_smul c fun i => v i)

@[simp] theorem coe_coordWedgeC1 (v : Fin n → c1Forms n) :
    (coordWedgeC1 v : FormField n) = coordWedgeField fun i => v i := rfl

/-- `d S = −S d` on `C¹` forms. -/
theorem extDerivC1_coordWedgeC1 (v : Fin n → c1Forms n) :
    extDerivC1 (coordWedgeC1 v) = -coordWedgeC fun i => extDerivC1 (v i) :=
  Subtype.ext (extDeriv_coordWedgeField_eq fun i => mem_c1Forms.1 (v i).2)

/-- The degree-`(k+1)` part of `S v` is `S` of the degree-`k` parts. -/
theorem degField_coordWedgeField (k : ℕ) (v : Fin n → FormField n) :
    degField (k + 1) (coordWedgeField v) = coordWedgeField fun i => degField k (v i) := by
  funext x s
  by_cases hs : #s = k + 1
  · simp only [degField, hs, ↓reduceIte, coordWedgeField_apply, coordWedgeSum_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have : #(s.erase j) = k := by rw [card_erase_of_mem hj, hs]; rfl
    simp only [this, ↓reduceIte]
  · rw [show degField (k + 1) (coordWedgeField v) x s = 0 by simp [degField, hs]]
    exact (isDeg_coordWedgeField (fun i x => isDeg_degField k (v i) x) x s hs).symm

end Field

/-! ### Moments of `S v` -/

section Moment

/-- **Moments of `S v`**: `∫_{T̂} F_q^*(S v)_{k+1} ∧ η = (−1)ᵏ Σᵢ ∫_{T̂} F_q^*(vᵢ)_k ∧ (B_q eᵢ ∧ η)`,
`B_q = simplexMatrix q` (the pulled-back `dxᵢ` are the constant covectors `B_q eᵢ`). -/
theorem vertexMoment_degField_coordWedgeField {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ)
    {η : FormField m} (hη : Continuous η) (k : ℕ) {v : Fin n → FormField n}
    (hv : ∀ i, Continuous (v i)) :
    vertexMoment q η (degField (k + 1) (coordWedgeField v)) =
      (-1 : ℝ) ^ k * ∑ i, vertexMoment q (fun y => wedge (simplexMatrix q i) (η y))
        (degField k (v i)) := by
  rw [degField_coordWedgeField]
  simp only [vertexMoment_eq_integral, Finset.mul_sum, ← integral_const_mul]
  have hint : ∀ i, IntegrableOn (fun x => wedgeField (affinePullback (simplexMatrix q) (q 0)
      (degField k (v i))) (fun y => wedge (simplexMatrix q i) (η y)) x univ) (refSimplex m) :=
    fun i => integrableOn_wedgeField (continuous_affinePullback _ _ (continuous_degField k (hv i)))
      (continuous_pi fun s => continuous_finsetSum _ fun j _ =>
        continuous_const.mul ((continuous_apply _).comp hη))
  rw [← integral_finsetSum _ fun i _ => (hint i).const_mul _]
  refine setIntegral_congr_fun (measurableSet_refSimplex m) fun x _ => ?_
  simp only [wedgeField, affinePullback_coordWedgeField, wedgeForm_sum_left, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← wedge_wedgeForm,
    wedge_wedgeForm_right _ (IsDeg.affinePullback (isDeg_degField k (v i)) _ _ x)]
  simp

end Moment

/-! ### DOF compatibility of `S` for the polynomial families -/

namespace PolySeq

/-- The source sequence `S` admits constant `1`-forms as test forms of its degree-`k` DOFs on
`(k+1)`-faces (true for `P_rΛᵏ` and `P_r⁻Λᵏ` with `r ≥ 2`, `constOneTest_of_two_le_deg`). -/
def ConstOneTest (S : PolySeq) (k : ℕ) : Prop :=
  ∀ m, m = k + 1 → ∀ ξ : Fin m → ℝ, (fun _ : Fin m → ℝ => oneForm ξ) ∈ S.test k m

/-- **The test forms of `P₁⁻Λᵏ⁺¹`** on `m`-faces are the constant `0`-forms for `m = k + 1` and
`0` otherwise. -/
theorem lowestOrder_test_succ {k m : ℕ} {η : FormField m}
    (hη : η ∈ lowestOrder.test (k + 1) m) :
    η = 0 ∨ ∃ _ : m = k + 1, ∃ c : ℝ, ∀ y, η y = c • Pi.single ∅ 1 := by
  have hkind : lowestOrder.kind (k + 1) = .trimmed := by simp [lowestOrder]
  have hdeg : lowestOrder.deg (k + 1) = 1 := rfl
  simp only [PolySeq.test, hkind, hdeg, PolyKind.test_trimmed, testSpaceMinus] at hη
  split_ifs at hη with h
  · obtain rfl : m = k + 1 := by omega
    refine Or.inr ⟨rfl, ?_⟩
    obtain ⟨Ω, hΩ, rfl⟩ := hη
    simp only [show 1 + (k + 1) - (k + 1) - 1 = 0 by omega,
      show k + 1 - (k + 1) = 0 by omega] at hΩ
    refine ⟨MvPolynomial.eval 0 (Ω ∅), fun y => funext fun s => ?_⟩
    by_cases hs : s = ∅
    · subst hs
      have hC := (MvPolynomial.totalDegree_eq_zero_iff_eq_C).1 (Nat.le_zero.1 (hΩ.2 ∅))
      rw [evalForm_apply, hC]
      simp
    · rw [evalForm_apply, hΩ.1 s (by rwa [Ne, Finset.card_eq_zero]), map_zero]
      simp [hs]
  · exact Or.inl ((Submodule.mem_bot ℝ).1 hη)

/-- **Constant `1`-forms are test forms** of `P_rΛᵏ` and `P_r⁻Λᵏ` on `(k+1)`-faces for `r ≥ 2`. -/
theorem constOneTest_of_two_le_deg (S : PolySeq) {k : ℕ} (hk : 2 ≤ S.deg k) :
    S.ConstOneTest k := by
  rintro m rfl ξ
  have hc : ∀ x, (fun _ : Fin (k + 1) → ℝ => oneForm ξ) x =
      (fun _ : Fin (k + 1) → ℝ => oneForm ξ) 0 := fun _ => rfl
  have hd : ∀ x, IsDeg 1 ((fun _ : Fin (k + 1) → ℝ => oneForm ξ) x) := fun _ => isDeg_oneForm ξ
  simp only [PolySeq.test]
  cases hkind : S.kind k
  · simp only [PolyKind.test_full]
    rw [testSpace_eq ⟨by omega, by omega⟩]
    refine polySpace_le_polyMinusSpace (by omega) _ ?_
    rw [show k + 1 - k = 1 by omega]
    exact mem_polySpace_of_eq_const hc hd
  · simp only [PolyKind.test_trimmed]
    rw [testSpaceMinus_eq ⟨by omega, by omega⟩]
    rw [show k + 1 - k = 1 by omega]
    exact mem_polySpace_of_eq_const hc hd

/-- **DOF compatibility of `S` with the target `P₁⁻Λᵏ⁺¹`** (the moment form of
[QuennevilleBelair2015], Prop 5.7): for a source family whose test forms on `(k+1)`-faces contain
the constant `1`-forms, each DOF `ℓ'_{g,i}` of `P₁⁻Λᵏ⁺¹` composed with `S v = Σ dxₐ ∧ vₐ` is a
combination of the degree-`k` DOFs of the components `vₐ` **on the same face** `g`:
`ℓ'_{g,i}(S v) = (−1)ᵏ Σₐ ∫_{T̂} F^*(vₐ) ∧ (B eₐ ∧ η)`, and `B eₐ ∧ η` is a source test form. -/
theorem dof_comp_coordWedgeC_mem_span (S : PolySeq) {k : ℕ} (hS : S.ConstOneTest k)
    (g : Finset (Fin n → ℝ)) (i : lowestOrder.DofIdx g (k + 1)) :
    lowestOrder.dof g (k + 1) i ∘ₗ coordWedgeC ∈
      Submodule.span ℝ (Set.range fun p : Fin n × S.DofIdx g k =>
        S.dof g k p.2 ∘ₗ LinearMap.proj p.1) := by
  classical
  have hg : #g = #g - 1 + 1 := by have := card_pos.2 i.2; omega
  set q := lexEnum g (#g - 1)
  set η := (lowestOrder.testBasis (k + 1) (#g - 1) i.1 : FormField (#g - 1))
  have hη : η ∈ lowestOrder.test (k + 1) (#g - 1) := (lowestOrder.testBasis (k + 1) (#g - 1) i.1).2
  have hηc : Continuous η := lowestOrder.continuous_testBasis (k + 1) (#g - 1) i.1
  have key : ∀ v : Fin n → contForms n, lowestOrder.dof g (k + 1) i (coordWedgeC v) =
      (-1 : ℝ) ^ k * ∑ a, vertexMoment q (fun y => wedge (simplexMatrix q a) (η y))
        (degField k (v a)) := fun v => by
    rw [dof_apply, coe_coordWedgeC]
    exact vertexMoment_degField_coordWedgeField q hηc k fun a => (v a).2
  rcases lowestOrder_test_succ hη with h0 | ⟨hm, c, hc⟩
  · have : lowestOrder.dof g (k + 1) i ∘ₗ coordWedgeC = 0 := by
      refine LinearMap.ext fun v => ?_
      rw [LinearMap.comp_apply, key, LinearMap.zero_apply]
      simp [h0, vertexMoment_eq_integral, wedgeField]
    rw [this]
    exact Submodule.zero_mem _
  · have hζ : ∀ a, (fun y => wedge (simplexMatrix q a) (η y)) ∈ S.test k (#g - 1) := by
      intro a
      have : (fun y => wedge (simplexMatrix q a) (η y)) =
          c • fun _ : Fin (#g - 1) → ℝ => oneForm (simplexMatrix q a) := by
        funext y
        rw [hc y, wedge_smul, Pi.smul_apply, oneForm]
      rw [this]
      exact Submodule.smul_mem _ c (hS _ hm _)
    choose d hd using fun a => S.exists_degMoment_eq_sum hg (hζ a)
    have hfun : lowestOrder.dof g (k + 1) i ∘ₗ coordWedgeC =
        ∑ a, ∑ j, ((-1 : ℝ) ^ k * d a j) • (S.dof g k j ∘ₗ LinearMap.proj a) := by
      refine LinearMap.ext fun v => ?_
      rw [LinearMap.comp_apply, key, Finset.mul_sum]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      have := congrArg (fun L : contForms n →ₗ[ℝ] ℝ => L (v a)) (hd a)
      simp only [degMoment_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul] at this
      rw [this, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfun]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, j), rfl⟩)

/-- **The target DOFs of `S v` only see the source DOFs of the components on the same face.** -/
theorem dof_coordWedgeC_eq (S : PolySeq) {k : ℕ} (hS : S.ConstOneTest k)
    {g : Finset (Fin n → ℝ)} (i : lowestOrder.DofIdx g (k + 1)) {v w : Fin n → contForms n}
    (h : ∀ a j, S.dof g k j (v a) = S.dof g k j (w a)) :
    lowestOrder.dof g (k + 1) i (coordWedgeC v) = lowestOrder.dof g (k + 1) i (coordWedgeC w) :=
  eq_of_mem_span_range (L := lowestOrder.dof g (k + 1) i ∘ₗ coordWedgeC)
    (S.dof_comp_coordWedgeC_mem_span hS g i) fun p => h p.1 p.2

end PolySeq

/-! ### The weak-symmetry interpolant on the finite element spaces -/

namespace PolySeq

variable (S : PolySeq) (M : SimplicialMesh n) (k : ℕ)

/-- A local field of `S` as a continuous form. -/
abbrev toCont {T : Affine.Simplex ℝ (Fin n → ℝ) n} (u : (polyElement n S).space T k) :
    contForms n :=
  ⟨u, (polyElement n S).le_contForms T k u.2⟩

/-- **The weak-symmetry interpolant on piecewise fields**
`(Π'_h S u)_T = Π'_T (Σₐ dxₐ ∧ (uₐ)_T)` into the piecewise `P₁⁻Λᵏ⁺¹` fields: the global
canonical interpolant `Π¹(S⁰ ·)`, `Π²(S¹ ·)` of [QuennevilleBelair2015], §5.3, on the discrete
spaces (where the canonical interpolant of a continuous form is not available). -/
def wsPiecewise :
    (Fin n → (polyElement n S).Piecewise M k) →ₗ[ℝ] (polyElement n lowestOrder).Piecewise M (k + 1)
    where
  toFun u T := (polyElement n lowestOrder).localInterp T (k + 1)
    (coordWedgeC fun a => S.toCont k (u a T))
  map_add' u v := funext fun T => by
    change (polyElement n lowestOrder).localInterp T (k + 1)
        (coordWedgeC fun a => S.toCont k ((u a + v a) T)) =
      (polyElement n lowestOrder).localInterp T (k + 1)
          (coordWedgeC fun a => S.toCont k (u a T)) +
        (polyElement n lowestOrder).localInterp T (k + 1)
          (coordWedgeC fun a => S.toCont k (v a T))
    rw [← map_add, ← map_add]
    rfl
  map_smul' c u := funext fun T => by
    change (polyElement n lowestOrder).localInterp T (k + 1)
        (coordWedgeC fun a => S.toCont k ((c • u a) T)) =
      c • (polyElement n lowestOrder).localInterp T (k + 1)
          (coordWedgeC fun a => S.toCont k (u a T))
    rw [← map_smul, ← map_smul]
    rfl

theorem localDof_wsPiecewise (u : Fin n → (polyElement n S).Piecewise M k) (T : M.simplices)
    {g : Finset (Fin n → ℝ)} (hg : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (i : (polyElement n lowestOrder).DofIdx g (k + 1)) :
    (polyElement n lowestOrder).localDof T (k + 1) g i (S.wsPiecewise M k u T) =
      (polyElement n lowestOrder).dof g (k + 1) i (coordWedgeC fun a => S.toCont k (u a T)) :=
  (polyElement n lowestOrder).localDof_localInterp T (k + 1) _ g hg i

variable {S M k}

/-- `Π'_h S` maps `(Λ_hᵏ)ⁿ` into `P₁⁻Λ_hᵏ⁺¹`: the target DOFs on a shared face are combinations of
the source DOFs on that face (`dof_coordWedgeC_eq`). -/
theorem wsPiecewise_mem_globalSpace (hS : S.ConstOneTest k)
    {u : Fin n → (polyElement n S).Piecewise M k} (hu : ∀ a, u a ∈ (polyElement n S).globalSpace M k) :
    S.wsPiecewise M k u ∈ (polyElement n lowestOrder).globalSpace M (k + 1) := by
  intro T T' g hg hg' i
  rw [localDof_wsPiecewise _ _ _ _ _ hg, localDof_wsPiecewise _ _ _ _ _ hg']
  exact S.dof_coordWedgeC_eq hS i fun a j => hu a T T' g hg hg' j

/-- `Π'_h S` maps `(Λ̊_hᵏ)ⁿ` (vanishing boundary DOFs) into `P₁⁻Λ̊_hᵏ⁺¹`. -/
theorem wsPiecewise_mem_globalSpace₀ (hS : S.ConstOneTest k)
    {u : Fin n → (polyElement n S).Piecewise M k}
    (hu : ∀ a, u a ∈ (polyElement n S).globalSpace₀ M k) :
    S.wsPiecewise M k u ∈ (polyElement n lowestOrder).globalSpace₀ M (k + 1) := by
  refine ⟨wsPiecewise_mem_globalSpace hS fun a => (hu a).1, fun T F hF hFT g hg i => ?_⟩
  rw [localDof_wsPiecewise _ _ _ _ _ (hg.trans hFT)]
  have h0 := S.dof_coordWedgeC_eq hS i (v := fun a => S.toCont k (u a T)) (w := 0)
    fun a j => by
      rw [Pi.zero_apply, map_zero]
      exact (hu a).2 T F hF hFT g hg j
  exact h0.trans (by rw [map_zero, map_zero])

/-- **`S_h = Π'_h S` on the global spaces**: `(Λ_hᵏ)ⁿ → P₁⁻Λ_hᵏ⁺¹` (`S₀,ₕ = Π¹S⁰` for `k = 0`,
`S₁,ₕ = Π²S¹` for `k = 1`). -/
def wsGlobal (hS : S.ConstOneTest k) :
    (Fin n → (polyElement n S).globalSpace M k) →ₗ[ℝ]
      (polyElement n lowestOrder).globalSpace M (k + 1) where
  toFun u := ⟨S.wsPiecewise M k fun a => (u a : (polyElement n S).Piecewise M k),
    wsPiecewise_mem_globalSpace hS fun a => (u a).2⟩
  map_add' u v := Subtype.ext (map_add (S.wsPiecewise M k)
    (fun a => (u a : (polyElement n S).Piecewise M k)) fun a => (v a : (polyElement n S).Piecewise M k))
  map_smul' c u := Subtype.ext (map_smul (S.wsPiecewise M k) c
    fun a => (u a : (polyElement n S).Piecewise M k))

@[simp] theorem coe_wsGlobal (hS : S.ConstOneTest k) (u : Fin n → (polyElement n S).globalSpace M k) :
    (S.wsGlobal hS u : (polyElement n lowestOrder).Piecewise M (k + 1)) =
      S.wsPiecewise M k fun a => (u a : (polyElement n S).Piecewise M k) := rfl

/-- `S_h` on the spaces with vanishing boundary DOFs. -/
def wsGlobal₀ (hS : S.ConstOneTest k) :
    (Fin n → (polyElement n S).globalSpace₀ M k) →ₗ[ℝ]
      (polyElement n lowestOrder).globalSpace₀ M (k + 1) where
  toFun u := ⟨S.wsPiecewise M k fun a => (u a : (polyElement n S).Piecewise M k),
    wsPiecewise_mem_globalSpace₀ hS fun a => (u a).2⟩
  map_add' u v := Subtype.ext (map_add (S.wsPiecewise M k)
    (fun a => (u a : (polyElement n S).Piecewise M k)) fun a => (v a : (polyElement n S).Piecewise M k))
  map_smul' c u := Subtype.ext (map_smul (S.wsPiecewise M k) c
    fun a => (u a : (polyElement n S).Piecewise M k))

@[simp] theorem coe_wsGlobal₀ (hS : S.ConstOneTest k)
    (u : Fin n → (polyElement n S).globalSpace₀ M k) :
    (S.wsGlobal₀ hS u : (polyElement n lowestOrder).Piecewise M (k + 1)) =
      S.wsPiecewise M k fun a => (u a : (polyElement n S).Piecewise M k) := rfl

/-! ### The surjectivity hypothesis (5.4): `Π' S Π̃ = Π' S` -/

/-- **Thesis Prop 5.7, adapted (global form)**: `Π'_h S Π̃_h ψ = Π'_h S ψ` for continuous `ψ`
(`Π̃_h` the componentwise canonical interpolant, `Π'_h` the canonical interpolant of
`P₁⁻Λᵏ⁺¹`): the surjectivity hypothesis (5.4) for the canonical projections, i.e.
`Π¹S⁰Π̃⁰ = Π¹S⁰` (`k = 0`) and `Π²S¹Π̃¹ = Π²S¹` (`k = 1`). -/
theorem wsGlobal_tensorInterp (hS : S.ConstOneTest k) (ψ : Fin n → contForms n) :
    S.wsGlobal hS ((polyElement n S).tensorInterp M n k ψ) =
      (polyElement n lowestOrder).globalInterp M (k + 1) (coordWedgeC ψ) := by
  refine ((polyElement n lowestOrder).globalInterp_piecewise M (k + 1) _ _ fun T g hg i => ?_).symm
  rw [coe_wsGlobal, localDof_wsPiecewise _ _ _ _ _ hg]
  exact S.dof_coordWedgeC_eq hS i fun a j =>
    ((polyElement n S).localDof_globalInterp M k (ψ a) T g hg j).symm

/-! ### The discrete anticommutation -/

/-- **Canonical discrete anticommutation** `d S_h = −S_h d` on the global spaces: with
`dΠ' = Π'd` and `d S = −S d` on polynomial fields. -/
theorem dPiecewise_wsPiecewise (u : Fin n → (polyElement n S).Piecewise M k) :
    (polyElement n lowestOrder).dPiecewise M (k + 1) (S.wsPiecewise M k u) =
      -S.wsPiecewise M (k + 1) fun a => (polyElement n S).dPiecewise M k (u a) := by
  funext T
  rw [Pi.neg_apply, LocalElement.dPiecewise_apply]
  have hc1 : ∀ a, ContDiff ℝ 1 ((u a T : (polyElement n S).space T k) : FormField n) := fun a =>
    (polyElement n S).contDiff_of_mem (u a T).2
  have hw : S.wsPiecewise M k u T = (polyElement n lowestOrder).localInterp T (k + 1)
      (Submodule.inclusion c1Forms_le_contForms
        (coordWedgeC1 fun a => ⟨(u a T : FormField n), hc1 a⟩)) := rfl
  rw [hw, ← (polyElement n lowestOrder).localInterp_extDeriv T (k + 1), extDerivC1_coordWedgeC1,
    map_neg]
  rfl

/-! ### `S₀,ₕ` is onto -/

/-- `P₁⁻Λᵏ⁺¹` has at most one DOF per face. -/
theorem lowestOrder_finrank_test_le_one (k m : ℕ) :
    Module.finrank ℝ (lowestOrder.test (k + 1) m) ≤ 1 := by
  have hkind : lowestOrder.kind (k + 1) = .trimmed := by simp [lowestOrder]
  rw [PolySeq.test, PolyKind.finrank_test _ (lowestOrder.one_le_deg _)]
  simp only [hkind, PolyKind.testDim, show lowestOrder.deg (k + 1) = 1 from rfl]
  split_ifs
  · simp only [Nat.sub_self, Nat.choose_zero_right, one_mul]
    rcases Nat.eq_zero_or_pos (m - (k + 1)) with h | h
    · simp [h]
    · simp [Nat.choose_eq_zero_of_lt h]
  · simp

instance lowestOrder_dofIdx_subsingleton (g : Finset (Fin n → ℝ)) (k : ℕ) :
    Subsingleton (lowestOrder.DofIdx g (k + 1)) :=
  ⟨fun x y => Subtype.ext (Fin.ext (by
    have := x.1.isLt; have := y.1.isLt
    have := lowestOrder_finrank_test_le_one k (#g - 1)
    omega))⟩

/-- **A target DOF of `S v` is reached from one source DOF**: for every DOF `ℓ'_{g,i}` of
`P₁⁻Λᵏ⁺¹` there are a component `a` and a source DOF `ℓ_{g,j}` on the same face such that
`ℓ'_{g,i}(S v) ≠ 0` whenever the source DOFs of `v` on `g` are the Kronecker delta at `(a, j)`.
(The pulled-back `dxₐ` is a nonzero constant `1`-form for some `a`, hence a nonzero source test
form.) -/
theorem exists_dof_coordWedgeC_ne_zero (S : PolySeq) {k : ℕ} (hS : S.ConstOneTest k)
    {g : Finset (Fin n → ℝ)} (i : lowestOrder.DofIdx g (k + 1)) :
    ∃ (a : Fin n) (j : S.DofIdx g k), ∀ v : Fin n → contForms n,
      (∀ a' j', S.dof g k j' (v a') = if a' = a ∧ j' = j then 1 else 0) →
        lowestOrder.dof g (k + 1) i (coordWedgeC v) ≠ 0 := by
  classical
  have hne : g.Nonempty := i.2
  have hg : #g = #g - 1 + 1 := by have := card_pos.2 hne; omega
  set q := lexEnum g (#g - 1)
  set b' := lowestOrder.testBasis (k + 1) (#g - 1)
  set η := (b' i.1 : FormField (#g - 1))
  have hη : η ∈ lowestOrder.test (k + 1) (#g - 1) := (b' i.1).2
  have hηc : Continuous η := lowestOrder.continuous_testBasis (k + 1) (#g - 1) i.1
  have hη0 : η ≠ 0 := fun h => b'.ne_zero i.1 (Subtype.ext h)
  obtain h0 | ⟨hm, c, hc⟩ := lowestOrder_test_succ hη
  · exact absurd h0 hη0
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hη0 (funext fun y => by rw [hc y, zero_smul]; rfl)
  -- a nonzero row of the edge matrix
  have h01 : q ⟨1, by omega⟩ ≠ q 0 := fun h =>
    absurd ((strictMono_lexEnum hg).injective h) (by simp [Fin.ext_iff])
  obtain ⟨a, ha⟩ : ∃ a, simplexMatrix q a ⟨0, by omega⟩ ≠ 0 := by
    by_contra! hcon
    exact h01 (funext fun a => by
      have := hcon a
      simp only [simplexMatrix, Fin.succ_mk, sub_eq_zero] at this
      exact this)
  set ζ : Fin n → FormField (#g - 1) := fun a' y => wedge (simplexMatrix q a') (η y)
  have hζeq : ∀ a', ζ a' = c • fun _ => oneForm (simplexMatrix q a') := fun a' => by
    funext y; simp only [ζ]; rw [hc y, wedge_smul, Pi.smul_apply, oneForm]
  have hζ : ∀ a', ζ a' ∈ S.test k (#g - 1) := fun a' => by
    rw [hζeq]; exact Submodule.smul_mem _ c (hS _ hm _)
  set b := S.testBasis k (#g - 1)
  have hζ0 : (⟨ζ a, hζ a⟩ : S.test k (#g - 1)) ≠ 0 := by
    intro h
    have h1 : ζ a 0 {⟨0, by omega⟩} = 0 := by
      have := congrArg (fun z : S.test k (#g - 1) => (z : FormField (#g - 1)) 0 {⟨0, by omega⟩}) h
      simpa using this
    rw [hζeq] at h1
    simp only [Pi.smul_apply, oneForm_singleton, smul_eq_mul] at h1
    exact mul_ne_zero hc0 ha h1
  obtain ⟨j, hj⟩ : ∃ j, b.repr ⟨ζ a, hζ a⟩ j ≠ 0 := by
    by_contra! hcon
    exact hζ0 (b.repr.injective (Finsupp.ext fun j => by simp [hcon j]))
  refine ⟨a, ⟨j, hne⟩, fun v hv => ?_⟩
  have key : lowestOrder.dof g (k + 1) i (coordWedgeC v) =
      (-1 : ℝ) ^ k * ∑ a', vertexMoment q (ζ a') (degField k (v a')) := by
    rw [dof_apply, coe_coordWedgeC]
    exact vertexMoment_degField_coordWedgeField q hηc k fun a' => (v a').2
  have hexp : ∀ a', vertexMoment q (ζ a') (degField k (v a')) =
      ∑ l, b.repr ⟨ζ a', hζ a'⟩ l * S.dof g k ⟨l, hne⟩ (v a') := fun a' => by
    have e : ζ a' = ∑ l, b.repr ⟨ζ a', hζ a'⟩ l • (b l : FormField (#g - 1)) := by
      have := congrArg (Subtype.val : S.test k (#g - 1) → FormField (#g - 1))
        (b.sum_repr ⟨ζ a', hζ a'⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    conv_lhs => rw [e]
    rw [vertexMoment_sum_smul_right q _ _ (fun l => S.continuous_testBasis k _ l)
      (continuous_degField k (v a').2)]
    rfl
  rw [key]
  simp only [hexp, hv, Subtype.mk.injEq, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a (fun a' _ ha' => by simp [ha']) (by simp)]
  simp only [true_and, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hj

/-- **`S_h = Π' S` maps `(Λ̊_hᵏ)ⁿ` onto `P₁⁻Λ̊_hᵏ⁺¹`** for a source family whose test forms on
`(k+1)`-faces contain the constant `1`-forms (`P_rΛᵏ`, `P_r⁻Λᵏ`, `r ≥ 2`): in particular
`S₀,ₕ = Π¹S⁰ : P₂Λ̊⁰ ⊗ ℝ³ → P₁⁻Λ̊¹` is onto ([QuennevilleBelair2015], §5.3: the edge moments of
`ψ · τ_e` are free). Each interior target DOF is hit by a single source DOF on the same face, and
the target DOFs of `S v` on a face only see the source DOFs on that face. -/
theorem wsGlobal₀_surjective (hS : S.ConstOneTest k) :
    Function.Surjective (S.wsGlobal₀ (M := M) hS) := by
  classical
  set Φ := ((polyElement n lowestOrder).interiorDofEquiv M (k + 1)).toLinearMap ∘ₗ S.wsGlobal₀ (M := M) hS
  suffices hΦ : Function.Surjective Φ by
    intro u
    obtain ⟨x, hx⟩ := hΦ ((polyElement n lowestOrder).interiorDofEquiv M (k + 1) u)
    exact ⟨x, ((polyElement n lowestOrder).interiorDofEquiv M (k + 1)).injective hx⟩
  -- each interior target DOF is hit
  have hit : ∀ p : (polyElement n lowestOrder).InteriorDofIdx M (k + 1), ∃ x, Φ x = (Φ x p) • Pi.single p 1 ∧ Φ x p ≠ 0 := by
    intro p
    obtain ⟨⟨g, i⟩, hpint⟩ := p
    obtain ⟨a, j, hval⟩ := S.exists_dof_coordWedgeC_ne_zero hS i
    -- the source field with one global DOF
    set p' : (polyElement n S).GlobalDofIdx M k := ⟨g, j⟩
    set c : (polyElement n S).GlobalDofIdx M k → ℝ := Pi.single p' 1
    have hc0 : ∀ q : (polyElement n S).GlobalDofIdx M k, (polyElement n S).IsBoundaryDof M q → c q = 0 := by
      intro q hq
      have : q ≠ p' := by
        rintro rfl
        exact hpint (by obtain ⟨F, hF, hgF⟩ := hq; exact ⟨F, hF, hgF⟩)
      simp [c, this]
    have hmem : (polyElement n S).ofGlobalDof M k c ∈ (polyElement n S).globalSpace₀ M k :=
      ((polyElement n S).mem_globalSpace₀_iff M ⟨_, (polyElement n S).ofGlobalDof_mem M k c⟩).2 fun q hq => by
        have : (polyElement n S).globalDof M k ⟨_, (polyElement n S).ofGlobalDof_mem M k c⟩ q = c q := by
          rw [(polyElement n S).globalDof_apply M k _ q (LocalElement.faceSimplex M q.1) (LocalElement.subset_faceSimplex M q.1)]
          exact (polyElement n S).localDof_ofGlobalDof M k c _ _ (LocalElement.subset_faceSimplex M q.1) _
        rw [this, hc0 q hq]
    set x : Fin n → (polyElement n S).globalSpace₀ M k := Pi.single a ⟨_, hmem⟩
    -- the source DOFs of `x`
    have hxdof : ∀ (T : M.simplices) (g' : Finset (Fin n → ℝ))
        (hg' : g' ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)) (a' : Fin n)
        (j' : S.DofIdx g' k),
        S.dof g' k j' (S.toCont k (((x a' : (polyElement n S).globalSpace₀ M k) : (polyElement n S).Piecewise M k) T)) =
          if a' = a then c ⟨⟨g', (LocalElement.mem_meshFaces M).2 ⟨T, T.2, hg'⟩⟩, j'⟩ else 0 := by
      intro T g' hg' a' j'
      by_cases ha' : a' = a
      · subst ha'
        simp only [x, Pi.single_eq_same, ↓reduceIte]
        exact (polyElement n S).localDof_ofGlobalDof M k c T g' hg' j'
      · simp only [x, Pi.single_eq_of_ne ha', ha', ↓reduceIte, ZeroMemClass.coe_zero,
          Pi.zero_apply]
        exact map_zero _
    refine ⟨x, funext fun p'' => ?_, ?_⟩
    · obtain ⟨⟨g'', i''⟩, hp''⟩ := p''
      by_cases hgg : g'' = g
      · subst hgg
        obtain rfl : i'' = i := (lowestOrder_dofIdx_subsingleton _ k).elim _ _
        simp
      · rw [Pi.smul_apply, Pi.single_eq_of_ne (by
          intro h; apply hgg; have := congrArg (fun q => q.1.1) h; exact this), smul_zero]
        change (polyElement n lowestOrder).localDof (LocalElement.faceSimplex M g'') (k + 1) g'' i''
          (S.wsPiecewise M k (fun a => ((x a : (polyElement n S).globalSpace₀ M k) : (polyElement n S).Piecewise M k))
            (LocalElement.faceSimplex M g'')) = 0
        rw [localDof_wsPiecewise _ _ _ _ _ (LocalElement.subset_faceSimplex M g'')]
        refine (S.dof_coordWedgeC_eq hS i'' (w := 0) fun a' j' => ?_).trans (by
          rw [map_zero, map_zero])
        rw [hxdof _ _ (LocalElement.subset_faceSimplex M g''), Pi.zero_apply, map_zero]
        split_ifs
        · simp only [c, Pi.single_apply]
          split_ifs with h
          · exact absurd (Subtype.ext (congrArg Subtype.val (congrArg Sigma.fst h))) hgg
          · rfl
        · rfl
    · change (polyElement n lowestOrder).localDof (LocalElement.faceSimplex M g) (k + 1) g i
          (S.wsPiecewise M k (fun a => ((x a : (polyElement n S).globalSpace₀ M k) : (polyElement n S).Piecewise M k))
            (LocalElement.faceSimplex M g)) ≠ 0
      rw [localDof_wsPiecewise _ _ _ _ _ (LocalElement.subset_faceSimplex M g)]
      refine hval _ fun a' j' => ?_
      rw [hxdof _ _ (LocalElement.subset_faceSimplex M g)]
      by_cases ha' : a' = a
      · simp only [ha', ↓reduceIte, true_and, c, Pi.single_apply]
        congr 1
        exact propext ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.1 h).2, fun h => by subst h; rfl⟩
      · simp [ha']
  intro y
  have hy : y = ∑ p, y p • Pi.single p (1 : ℝ) := by
    funext p; simp [Finset.sum_apply, Pi.single_apply]
  choose x hx hx0 using hit
  refine ⟨∑ p, (y p / Φ (x p) p) • x p, ?_⟩
  rw [map_sum]
  conv_rhs => rw [hy]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e := hx p
  rw [map_smul, e, smul_smul]
  congr 1
  rw [← e]
  exact div_mul_cancel₀ _ (hx0 p)

end PolySeq

/-! ### The `L²` realization of `S` and the domains of `d` -/

section L2

open scoped InnerProductSpace

variable {Ω : Set (Fin n → ℝ)}

/-- The coefficient of `dx_t` in `S(eₐ ⊗ dx_r) = dxₐ ∧ dx_r`. -/
def wsCoeff (k : ℤ) (t : formIdx n (k + 1)) (p : Fin n × formIdx n k) : ℝ :=
  coordWedgeSum (Pi.single p.1 (Pi.single p.2.1 1)) t.1

theorem formExt_eq_sum {k : ℤ} (w : formIdx n k → ℝ) :
    formExt w = ∑ r, w r • (Pi.single r.1 1 : Finset (Fin n) → ℝ) := by
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases hs : (#s : ℤ) = k
  · rw [formExt_of_card _ hs, Finset.sum_eq_single ⟨s, hs⟩]
    · simp
    · intro r _ hr
      simp only [ite_eq_right_iff]
      intro h
      exact absurd (Subtype.ext h.symm) hr
    · simp
  · have hne : ∀ r : formIdx n k, s ≠ r.1 := fun r h => hs (h ▸ r.2)
    simp [formExt, hs, hne]

/-- **`S` in coordinates**: `(S v)_t = Σ_{a,r} c(t; a, r) (vₐ)_r`. -/
theorem coordWedgeSum_formExt {k : ℤ} (w : Fin n → formIdx n k → ℝ) (t : formIdx n (k + 1)) :
    coordWedgeSum (fun a => formExt (w a)) t.1 = ∑ p, wsCoeff k t p * w p.1 p.2 := by
  have : (fun a => formExt (w a)) =
      ∑ p : Fin n × formIdx n k, w p.1 p.2 • Pi.single p.1 (Pi.single p.2.1 1) := by
    funext a
    rw [formExt_eq_sum, Finset.sum_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a (fun b _ hb => by
      simp [Ne.symm hb]) (by simp)]
    simp
  rw [this, coordWedgeSum_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coordWedgeSum_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl

/-- `S` on fields of coefficients. -/
def wsFields {F : Type*} [AddCommMonoid F] [Module ℝ F] (k : ℤ) (φ : Fin n → formIdx n k → F) :
    formIdx n (k + 1) → F :=
  fun t => ∑ p, wsCoeff k t p • φ p.1 p.2

theorem isTestField_wsFields {k : ℤ} {φ : Fin n → formIdx n k → (Fin n → ℝ) → ℝ}
    (hφ : ∀ a, IsTestField Ω (φ a)) : IsTestField Ω (wsFields k φ) := fun t => by
  have : wsFields k φ t = fun x => ∑ p : Fin n × formIdx n k, wsCoeff k t p * φ p.1 p.2 x := by
    funext x; simp [wsFields, Finset.sum_apply]
  rw [this]
  exact IsTest.sum _ fun p _ => (hφ p.1 p.2).const_mul _

/-- The vector of `k`-form coefficient fields as form fields. -/
def toFormField {k : ℤ} (w : formIdx n k → (Fin n → ℝ) → ℝ) : FormField n :=
  fun x s => formExt (fun r => w r x) s

theorem wsFields_eq_formComp {k : ℤ} (φ : Fin n → formIdx n k → (Fin n → ℝ) → ℝ) :
    wsFields k φ = formComp (k := k + 1) (coordWedgeField fun a => toFormField (φ a)) := by
  funext t x
  change _ = coordWedgeSum (fun a => formExt fun r => φ a r x) t.1
  rw [coordWedgeSum_formExt (fun a r => φ a r x)]
  simp [wsFields, Finset.sum_apply]

theorem isDeg_toFormField {k : ℕ} (w : formIdx n k → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    IsDeg k (toFormField w x) := fun s hs => by
  have : ¬ ((#s : ℤ) = k) := by exact_mod_cast hs
  simp [toFormField, formExt, this]

theorem contDiff_toFormField {k : ℤ} {w : formIdx n k → (Fin n → ℝ) → ℝ}
    (hw : ∀ r, ContDiff ℝ ∞ (w r)) : ContDiff ℝ ∞ (toFormField w) := by
  refine contDiff_pi.2 fun s => ?_
  simp only [toFormField, formExt]
  split_ifs
  · exact hw _
  · exact contDiff_const

theorem formComp_toFormField {k : ℤ} (w : formIdx n k → (Fin n → ℝ) → ℝ) :
    formComp (k := k) (toFormField w) = w := by
  funext r x
  simp [formComp, toFormField, formExt_val]

/-- `d` on coefficient fields is the classical exterior derivative of the form field. -/
theorem toFormField_extDerivOp {k : ℕ} (w : formIdx n k → (Fin n → ℝ) → ℝ) :
    toFormField ((extDerivOp ℝ n k).apply w) = extDeriv (toFormField w) := by
  funext x s
  by_cases hs : (#s : ℤ) = k + 1
  · simp only [toFormField, formExt_of_card _ hs]
    have := extDerivOp_apply_formComp (isDeg_toFormField w) ⟨s, hs⟩ x
    rw [formComp_toFormField] at this
    exact this
  · rw [show toFormField ((extDerivOp ℝ n k).apply w) x s = 0 by simp [toFormField, formExt, hs]]
    refine (IsDeg.extDeriv (isDeg_toFormField w) x s fun h => hs ?_).symm
    rw [h]; push_cast; ring

/-- **`d S = −S d` on smooth coefficient fields.** -/
theorem extDerivOp_wsFields {k : ℕ} {φ : Fin n → formIdx n k → (Fin n → ℝ) → ℝ}
    (hφ : ∀ a r, ContDiff ℝ ∞ (φ a r)) :
    (extDerivOp ℝ n ((k : ℤ) + 1)).apply (wsFields k φ) =
      -wsFields ((k : ℤ) + 1) (fun a => (extDerivOp ℝ n k).apply (φ a)) := by
  have hdeg : ∀ x, IsDeg (k + 1)
      ((coordWedgeField fun a => toFormField (φ a)) x) :=
    isDeg_coordWedgeField fun a x => isDeg_toFormField (φ a) x
  have hsm : ∀ a, ContDiff ℝ ∞ (toFormField (φ a)) := fun a => contDiff_toFormField (hφ a)
  funext t x
  rw [wsFields_eq_formComp]
  have h1 := extDerivOp_apply_formComp (k := k + 1) hdeg t x
  refine h1.trans ?_
  rw [extDeriv_coordWedgeField fun a => ((hsm a).differentiable (by simp)) x, Pi.neg_apply,
    Pi.neg_apply, wsFields_eq_formComp]
  simp only [formComp, Pi.neg_apply]
  congr 2
  funext a
  exact (toFormField_extDerivOp (φ a)).symm

/-- **The `L²` realization of `S`**: `L²(Ω; Λᵏ)ⁿ → L²(Ω; Λᵏ⁺¹)`,
`(S v)_t = Σ_{a,r} c(t; a, r) (vₐ)_r`. -/
def wsL2 (k : ℤ) :
    PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k)) →L[ℝ] L2F ℝ Ω (formIdx n (k + 1)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : formIdx n (k + 1) => L2 ℝ Ω)).symm.toContinuousLinearMap
    ∘L ContinuousLinearMap.pi fun t => ∑ p : Fin n × formIdx n k, wsCoeff k t p •
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : formIdx n k => L2 ℝ Ω) p.2) ∘L
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k)) p.1))

theorem wsL2_apply {k : ℤ} (v : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k)))
    (t : formIdx n (k + 1)) : wsL2 k v t = ∑ p, wsCoeff k t p • v p.1 p.2 := by
  simp [wsL2]

/-- The adjoint of `S`: `(Sᵀ w)ₐ,ᵣ = Σ_t c(t; a, r) w_t`. -/
def wsL2Adj (k : ℤ) :
    L2F ℝ Ω (formIdx n (k + 1)) →L[ℝ] PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => L2F ℝ Ω (formIdx n k))).symm.toContinuousLinearMap
    ∘L ContinuousLinearMap.pi fun a =>
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : formIdx n k => L2 ℝ Ω)).symm.toContinuousLinearMap
        ∘L ContinuousLinearMap.pi fun r => ∑ t : formIdx n (k + 1), wsCoeff k t (a, r) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : formIdx n (k + 1) => L2 ℝ Ω) t

theorem wsL2Adj_apply {k : ℤ} (w : L2F ℝ Ω (formIdx n (k + 1))) (a : Fin n) (r : formIdx n k) :
    wsL2Adj k w a r = ∑ t, wsCoeff k t (a, r) • w t := by
  simp [wsL2Adj]

theorem inner_wsL2 {k : ℤ} (v : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k)))
    (w : L2F ℝ Ω (formIdx n (k + 1))) : ⟪wsL2 k v, w⟫_ℝ = ⟪v, wsL2Adj k w⟫_ℝ := by
  rw [L2F.inner_def, PiLp.inner_apply]
  simp only [L2F.inner_def, wsL2_apply, wsL2Adj_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  rw [Finset.sum_comm, Fintype.sum_prod_type]

theorem toL2_sum {ι' : Type*} (u : Finset ι') (c : ι' → ℝ) {f : ι' → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, IsTest Ω (f i)) :
    ∑ i ∈ u, c i • toL2 (hf i) =
      toL2 (IsTest.sum u fun i _ => (hf i).const_mul (c i) : IsTest Ω fun x => ∑ i ∈ u, c i * f i x) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, ← toL2_zero (Ω := Ω) (𝕜 := ℝ)]
    exact toL2_congr _ _ (by funext x; simp)
  | insert a u ha ih =>
    rw [Finset.sum_insert ha, ih, ← toL2_smul, ← toL2_add]
    exact toL2_congr _ _ (by funext x; simp [Finset.sum_insert ha])

/-- `S` maps test fields to test fields. -/
theorem wsL2_testField {k : ℤ} {φ : Fin n → formIdx n k → (Fin n → ℝ) → ℝ}
    (hφ : ∀ a, IsTestField Ω (φ a)) :
    wsL2 k (WithLp.toLp 2 fun a => testField (hφ a)) = testField (isTestField_wsFields hφ) := by
  refine PiLp.ext fun t => ?_
  rw [wsL2_apply, testField_apply]
  simp only [testField_apply]
  rw [toL2_sum Finset.univ (wsCoeff k t) (fun p : Fin n × formIdx n k => hφ p.1 p.2)]
  exact toL2_congr _ _ (by funext x; simp [wsFields, Finset.sum_apply])

/-- `Sᵀ` on fields of coefficients. -/
def wsFieldsAdj {F : Type*} [AddCommMonoid F] [Module ℝ F] (k : ℤ) (ψ : formIdx n (k + 1) → F) :
    Fin n → formIdx n k → F :=
  fun a r => ∑ t, wsCoeff k t (a, r) • ψ t

theorem isTestField_wsFieldsAdj {k : ℤ} {ψ : formIdx n (k + 1) → (Fin n → ℝ) → ℝ}
    (hψ : IsTestField Ω ψ) (a : Fin n) : IsTestField Ω (wsFieldsAdj k ψ a) := fun r => by
  have : wsFieldsAdj k ψ a r = fun x => ∑ t, wsCoeff k t (a, r) * ψ t x := by
    funext x; simp [wsFieldsAdj, Finset.sum_apply]
  rw [this]
  exact IsTest.sum _ fun t _ => (hψ t).const_mul _

/-- `Sᵀ` maps test fields to test fields. -/
theorem wsL2Adj_testField {k : ℤ} {ψ : formIdx n (k + 1) → (Fin n → ℝ) → ℝ}
    (hψ : IsTestField Ω ψ) :
    wsL2Adj k (testField hψ) =
      WithLp.toLp 2 fun a => testField (isTestField_wsFieldsAdj hψ a) := by
  refine PiLp.ext fun a => PiLp.ext fun r => ?_
  rw [wsL2Adj_apply]
  simp only [testField_apply]
  rw [toL2_sum Finset.univ (fun t => wsCoeff k t (a, r)) hψ]
  exact toL2_congr _ _ (by funext x; simp [wsFieldsAdj, Finset.sum_apply])

/-- **`S` maps `D(d_min)ⁿ` into `D(d_min)`** (`H̊Λᵏ(Ω)ⁿ → H̊Λᵏ⁺¹(Ω)`), with `d S = −S d`: the
pairs `(S φ, −S dφ)` of test fields lie in the graph of `d`, and `S` is bounded. -/
theorem wsL2_mem_minimal (hΩ : IsOpen Ω) (k : ℕ)
    {v : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))}
    (hv : ∀ a, v a ∈ ((extDerivOp ℝ n k).minimal Ω).domain) :
    ∃ h : wsL2 k v ∈ ((extDerivOp ℝ n ((k : ℤ) + 1)).minimal Ω).domain,
      (extDerivOp ℝ n ((k : ℤ) + 1)).minimal Ω ⟨_, h⟩ =
        -wsL2 ((k : ℤ) + 1) (WithLp.toLp 2 fun a => (extDerivOp ℝ n k).minimal Ω ⟨v a, hv a⟩) := by
  set A := extDerivOp ℝ n k
  set A' := extDerivOp ℝ n ((k : ℤ) + 1)
  let Ψ : (Fin n → L2F ℝ Ω (formIdx n k) × L2F ℝ Ω (formIdx n ((k : ℤ) + 1))) →
      L2F ℝ Ω (formIdx n ((k : ℤ) + 1)) × L2F ℝ Ω (formIdx n ((k : ℤ) + 1 + 1)) :=
    fun p => (wsL2 k (WithLp.toLp 2 fun a => (p a).1),
      -wsL2 ((k : ℤ) + 1) (WithLp.toLp 2 fun a => (p a).2))
  have hΨc : Continuous Ψ := by
    refine Continuous.prodMk ((wsL2 k).continuous.comp ?_) ((wsL2 _).continuous.comp ?_).neg
    · exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun a =>
        continuous_fst.comp (continuous_apply a))
    · exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun a =>
        continuous_snd.comp (continuous_apply a))
  have hsub : Ψ '' Set.univ.pi (fun _ => (A.testGraph Ω : Set _)) ⊆ (A'.testGraph Ω : Set _) := by
    rintro _ ⟨p, hp, rfl⟩
    choose φ hφ hpφ using fun a => hp a (Set.mem_univ a)
    refine ⟨wsFields k φ, isTestField_wsFields hφ, ?_⟩
    have hsm : ∀ a r, ContDiff ℝ ∞ (φ a r) := fun a r => (hφ a r).contDiff
    have e1 : (WithLp.toLp 2 fun a => (p a).1) = WithLp.toLp 2 fun a => testField (hφ a) := by
      congr 1; funext a; rw [hpφ a]
    have e2 : (WithLp.toLp 2 fun a => (p a).2) =
        WithLp.toLp 2 fun a => testField (A.isTestField_apply (hφ a)) := by
      congr 1; funext a; rw [hpφ a]
    simp only [Ψ, e1, e2, wsL2_testField]
    refine Prod.ext rfl ?_
    change -testField _ = testField _
    rw [testField_congr (A'.isTestField_apply (isTestField_wsFields hφ))
      ((isTestField_wsFields fun a => A.isTestField_apply (hφ a)).smul (-1 : ℝ))
      (by rw [extDerivOp_wsFields hsm, neg_one_smul]), testField_smul, neg_one_smul]
  have hmem : (fun a => (v a, A.minimal Ω ⟨v a, hv a⟩)) ∈
      closure (Set.univ.pi fun _ => (A.testGraph Ω : Set _)) := by
    rw [closure_pi_set]
    intro a _
    have := A.mem_closure_minimal hΩ ⟨v a, hv a⟩
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at this
  have hcl : Ψ (fun a => (v a, A.minimal Ω ⟨v a, hv a⟩)) ∈ (A'.minimal Ω).graph := by
    rw [A'.minimal_graph hΩ, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact closure_mono hsub (mem_closure_image hΨc.continuousAt hmem)
  have hv' : (WithLp.toLp 2 fun a => v a) = v := rfl
  simp only [Ψ, hv'] at hcl
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hcl
  have hy : (y : L2F ℝ Ω (formIdx n ((k : ℤ) + 1))) = wsL2 k v := hy1
  refine ⟨hy ▸ y.2, ?_⟩
  refine Eq.trans ?_ hy2
  exact congrArg (A'.minimal Ω) (Subtype.ext hy.symm)

theorem inner_toLp_single {k : ℤ} (w : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) (a : Fin n)
    (x : L2F ℝ Ω (formIdx n k)) :
    ⟪w, WithLp.toLp 2 (Pi.single a x)⟫_ℝ = ⟪w a, x⟫_ℝ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single a (fun b _ hb => by
    simp [hb]) (by simp)]
  simp

theorem isTestField_single {k : ℤ} {χ : formIdx n k → (Fin n → ℝ) → ℝ} (hχ : IsTestField Ω χ)
    (a : Fin n) : ∀ b, IsTestField Ω ((Pi.single a χ : Fin n → formIdx n k → (Fin n → ℝ) → ℝ) b) :=
  fun b => by
    by_cases h : b = a
    · subst h; simpa using hχ
    · simpa [h] using (IsTestField.zero : IsTestField Ω (0 : formIdx n k → (Fin n → ℝ) → ℝ))

theorem toLp_testField_single {k : ℤ} {χ : formIdx n k → (Fin n → ℝ) → ℝ} (hχ : IsTestField Ω χ)
    (a : Fin n) :
    (WithLp.toLp 2 fun b => testField (isTestField_single hχ a b) :
        PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) =
      WithLp.toLp 2 (Pi.single a (testField hχ)) := by
  congr 1
  funext b
  by_cases h : b = a
  · subst h
    simp only [Pi.single_eq_same]
  · conv_rhs => rw [Pi.single_eq_of_ne h]
    exact (testField_congr _ IsTestField.zero (by simp [h])).trans testField_zero

/-- **The dual anticommutation on test fields**: `Sᵀ dᵗ = −dᵗ Sᵀ` (from `d S = −S d` and Green's
formula). -/
theorem testField_wsFieldsAdj_formalAdj (hΩ : IsOpen Ω) (k : ℕ)
    {ψ : formIdx n ((k : ℤ) + 1 + 1) → (Fin n → ℝ) → ℝ} (hψ : IsTestField Ω ψ) (a : Fin n) :
    testField (isTestField_wsFieldsAdj
        ((extDerivOp ℝ n ((k : ℤ) + 1)).formalAdj.isTestField_apply hψ) a) =
      -testField ((extDerivOp ℝ n k).formalAdj.isTestField_apply
        (isTestField_wsFieldsAdj hψ a)) := by
  set A := extDerivOp ℝ n k
  set A' := extDerivOp ℝ n ((k : ℤ) + 1)
  refine L2F.ext_of_forall_inner_testField hΩ fun χ hχ => ?_
  have hφ := isTestField_single hχ a
  have hsm : ∀ b r, ContDiff ℝ ∞ ((Pi.single a χ : Fin n → formIdx n k → (Fin n → ℝ) → ℝ) b r) :=
    fun b r => (hφ b r).contDiff
  have hAφ : (fun b => A.apply ((Pi.single a χ : Fin n → formIdx n k → (Fin n → ℝ) → ℝ) b)) =
      Pi.single a (A.apply χ) := by
    funext b
    by_cases h : b = a
    · subst h; simp
    · simp only [Pi.single_eq_of_ne h]; exact A.apply_zero
  -- `⟪(Sᵀ w)ₐ, χ⟫ = ⟪w, S (eₐ χ)⟫`
  have hadj : ∀ {j : ℤ} {w : formIdx n (j + 1) → (Fin n → ℝ) → ℝ} (hw : IsTestField Ω w)
      (X : L2F ℝ Ω (formIdx n j)),
      ⟪testField (isTestField_wsFieldsAdj hw a), X⟫_ℝ =
        ⟪testField hw, wsL2 j (WithLp.toLp 2 (Pi.single a X))⟫_ℝ := by
    intro j w hw X
    rw [real_inner_comm (wsL2 j (WithLp.toLp 2 (Pi.single a X))) (testField hw), inner_wsL2,
      wsL2Adj_testField, real_inner_comm (WithLp.toLp 2 fun b =>
        testField (isTestField_wsFieldsAdj hw b)) (WithLp.toLp 2 (Pi.single a X)),
      inner_toLp_single]
  have e1 : ⟪testField (isTestField_wsFieldsAdj (A'.formalAdj.isTestField_apply hψ) a),
      testField hχ⟫_ℝ =
        ⟪testField hψ, testField (A'.isTestField_apply (isTestField_wsFields hφ))⟫_ℝ := by
    rw [hadj, ← toLp_testField_single hχ a, wsL2_testField]
    have := A'.formalAdj.inner_testField_apply_testField hψ (isTestField_wsFields hφ)
    rw [ConstCoeffOp.formalAdj_formalAdj] at this
    exact this
  have e2 : testField (A'.isTestField_apply (isTestField_wsFields hφ)) =
      -wsL2 ((k : ℤ) + 1) (WithLp.toLp 2 (Pi.single a (testField (A.isTestField_apply hχ)))) := by
    have hdχ := A.isTestField_apply hχ
    rw [← toLp_testField_single hdχ a, wsL2_testField,
      testField_congr (A'.isTestField_apply (isTestField_wsFields hφ))
        ((isTestField_wsFields (isTestField_single hdχ a)).smul (-1 : ℝ))
        (by rw [extDerivOp_wsFields hsm, hAφ, neg_one_smul]), testField_smul, neg_one_smul]
  rw [e1, e2, inner_neg_right, ← hadj, inner_neg_left, neg_inj]
  have := A.inner_testField_apply_testField hχ (isTestField_wsFieldsAdj hψ a)
  rw [real_inner_comm, this, real_inner_comm]

/-- Below degree `0` the vectors of forms are zero. -/
theorem subsingleton_vec_formIdx {k : ℤ} (hk : k < 0) :
    Subsingleton (PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) :=
  have := LocalElement.subsingleton_L2F_of_neg Ω (n := n) hk
  ⟨fun _ _ => PiLp.ext fun _ => Subsingleton.elim _ _⟩

/-- **`S` maps `D(d_max)ⁿ` into `D(d_max)`** (`HΛᵏ(Ω)ⁿ → HΛᵏ⁺¹(Ω)`), with `d S = −S d`, in every
degree (below degree `0` the spaces are zero). -/
theorem wsL2_mem_maximal (hΩ : IsOpen Ω) (k : ℤ)
    {v : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))}
    (hv : ∀ a, v a ∈ ((extDerivOp ℝ n k).maximal Ω).domain) :
    ∃ h : wsL2 k v ∈ ((extDerivOp ℝ n (k + 1)).maximal Ω).domain,
      (extDerivOp ℝ n (k + 1)).maximal Ω ⟨_, h⟩ =
        -wsL2 (k + 1) (WithLp.toLp 2 fun a => (extDerivOp ℝ n k).maximal Ω ⟨v a, hv a⟩) := by
  rcases lt_or_ge k 0 with hk | hk
  · have := subsingleton_vec_formIdx (Ω := Ω) (n := n) hk
    obtain rfl : v = 0 := Subsingleton.elim _ _
    have h0 : wsL2 k (0 : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) = 0 := map_zero _
    have hmem : wsL2 k (0 : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) ∈
        ((extDerivOp ℝ n (k + 1)).maximal Ω).domain := h0 ▸ Submodule.zero_mem _
    refine ⟨hmem, ?_⟩
    have e1 : (⟨_, hmem⟩ : ((extDerivOp ℝ n (k + 1)).maximal Ω).domain) = 0 := Subtype.ext h0
    have e2 : (WithLp.toLp 2 fun a => (extDerivOp ℝ n k).maximal Ω
        ⟨(0 : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) a, hv a⟩ :
          PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n (k + 1)))) = 0 :=
      PiLp.ext fun a => (LinearPMap.apply_eq_of_eq rfl _ 0 (by simp)).trans (LinearPMap.map_zero _)
    rw [e1, LinearPMap.map_zero, e2, map_zero, neg_zero]
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  set A := extDerivOp ℝ n k
  set A' := extDerivOp ℝ n ((k : ℤ) + 1)
  set dv : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n ((k : ℤ) + 1))) :=
    WithLp.toLp 2 fun a => A.maximal Ω ⟨v a, hv a⟩
  have key : ∀ φ : formIdx n ((k : ℤ) + 1 + 1) → (Fin n → ℝ) → ℝ, ∀ hφ : IsTestField Ω φ,
      ⟪-wsL2 ((k : ℤ) + 1) dv, testField hφ⟫_ℝ =
        ⟪wsL2 k v, testField (A'.formalAdj.isTestField_apply hφ)⟫_ℝ := by
    intro φ hφ
    rw [inner_neg_left, inner_wsL2, inner_wsL2, wsL2Adj_testField, wsL2Adj_testField,
      PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    change -⟪dv a, testField (isTestField_wsFieldsAdj hφ a)⟫_ℝ =
      ⟪v a, testField (isTestField_wsFieldsAdj (A'.formalAdj.isTestField_apply hφ) a)⟫_ℝ
    rw [testField_wsFieldsAdj_formalAdj hΩ k hφ a, inner_neg_right, neg_inj]
    exact A.maximal_inner_testField hΩ ⟨v a, hv a⟩ (isTestField_wsFieldsAdj hφ a)
  have hmem : wsL2 k v ∈ (A'.maximal Ω).domain := (A'.mem_maximal_domain_iff hΩ).2 ⟨_, key⟩
  exact ⟨hmem, A'.maximal_apply_eq hΩ ⟨_, hmem⟩ key⟩

/-- The coefficients of `S`: `c(t; a, r) = ε(a, t)` if `a ∈ t` and `r = t ∖ a`, else `0`. -/
theorem wsCoeff_eq {k : ℤ} (t : formIdx n (k + 1)) (p : Fin n × formIdx n k) :
    wsCoeff k t p = if p.1 ∈ t.1 ∧ t.1.erase p.1 = p.2.1 then sgn p.1 t.1 else 0 := by
  rw [wsCoeff, coordWedgeSum_apply, Finset.sum_eq_single p.1 (fun i _ hi => by
    simp [Pi.single_apply, hi]) (by simp)]
  simp only [Pi.single_eq_same]
  by_cases h1 : p.1 ∈ t.1
  · rw [Finset.sum_eq_single p.1 (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp [h1])]
    simp only [Pi.single_eq_same, mul_one, Pi.single_apply]
    by_cases h2 : t.1.erase p.1 = p.2.1 <;> simp [h1, h2]
  · rw [Finset.sum_eq_zero fun j hj => by
      have : j ≠ p.1 := fun h => h1 (h ▸ hj)
      simp [Pi.single_apply, this]]
    simp [h1]

theorem abs_wsCoeff {k : ℤ} (t : formIdx n (k + 1)) (p : Fin n × formIdx n k) :
    |wsCoeff k t p| = if p.1 ∈ t.1 ∧ t.1.erase p.1 = p.2.1 then 1 else 0 := by
  rw [wsCoeff_eq]
  split_ifs
  · simp [sgn]
  · simp

/-- Each `t` sees `#t = k + 1` coefficients of absolute value one. -/
theorem sum_abs_wsCoeff_left (k : ℤ) (t : formIdx n (k + 1)) :
    ∑ p : Fin n × formIdx n k, |wsCoeff k t p| = (k : ℝ) + 1 := by
  simp only [abs_wsCoeff]
  rw [Fintype.sum_prod_type]
  have : ∀ a : Fin n, (∑ r : formIdx n k,
      (if a ∈ t.1 ∧ t.1.erase a = r.1 then (1 : ℝ) else 0)) = if a ∈ t.1 then 1 else 0 := by
    intro a
    by_cases ha : a ∈ t.1
    · rw [Finset.sum_eq_single ⟨t.1.erase a, card_erase_of_formIdx t ha⟩]
      · simp [ha]
      · intro r _ hr
        simp only [ite_eq_right_iff]
        rintro ⟨-, h⟩
        exact absurd (Subtype.ext h.symm) hr
      · simp
    · simp [ha]
  simp only [this, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h := t.2
  have : ((#t.1 : ℕ) : ℝ) = (k : ℝ) + 1 := by exact_mod_cast h
  exact this

/-- Each `(a, r)` occurs for at most one `t` (namely `r ∪ {a}`). -/
theorem sum_abs_wsCoeff_right {k : ℤ} (p : Fin n × formIdx n k) :
    ∑ t : formIdx n (k + 1), |wsCoeff k t p| ≤ 1 := by
  simp only [abs_wsCoeff, Finset.sum_boole]
  have : #({t : formIdx n (k + 1) | p.1 ∈ t.1 ∧ t.1.erase p.1 = p.2.1} : Finset _) ≤ 1 := by
    refine Finset.card_le_one.2 fun t ht t' ht' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    refine Subtype.ext ?_
    rw [← Finset.insert_erase ht.1, ← Finset.insert_erase ht'.1, ht.2, ht'.2]
  exact_mod_cast this

/-- **The bound of `S`**: `‖S v‖² ≤ (k + 1) ‖v‖²` (each `(a, r)` occurs in at most one
`t = r ∪ {a}`, and `#t = k + 1`). For `k = 0` (`S⁰`) the constant is `1`, for `k = 1` (`S¹`)
it is `2`. -/
theorem norm_wsL2_sq_le (k : ℤ) (v : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) :
    ‖wsL2 k v‖ ^ 2 ≤ ((k : ℝ) + 1) * ‖v‖ ^ 2 := by
  set c := wsCoeff (n := n) k
  set x : Fin n × formIdx n k → ℝ := fun p => ‖v p.1 p.2‖
  have hpt : ∀ t, ‖wsL2 k v t‖ ^ 2 ≤ ((k : ℝ) + 1) * ∑ p, |c t p| * x p ^ 2 := by
    intro t
    have h1 : ‖wsL2 k v t‖ ≤ ∑ p, |c t p| * x p := by
      rw [wsL2_apply]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
    have h2 : (∑ p, |c t p| * x p) ^ 2 ≤ (∑ p, |c t p|) * ∑ p, |c t p| * x p ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ => abs_nonneg _)
        (fun p _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) fun p _ => by
          rw [mul_pow, sq_abs, ← mul_assoc, ← sq, sq_abs]
    rw [sum_abs_wsCoeff_left] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  calc ‖wsL2 k v‖ ^ 2 = ∑ t, ‖wsL2 k v t‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
    _ ≤ ∑ t, ((k : ℝ) + 1) * ∑ p, |c t p| * x p ^ 2 := Finset.sum_le_sum fun t _ => hpt t
    _ = ((k : ℝ) + 1) * ∑ p, (∑ t, |c t p|) * x p ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ ((k : ℝ) + 1) * ∑ p, x p ^ 2 := by
        by_cases hk : (0 : ℝ) ≤ (k : ℝ) + 1
        · gcongr with p
          exact mul_le_of_le_one_left (sq_nonneg _) (sum_abs_wsCoeff_right p)
        · have : IsEmpty (formIdx n k) := ⟨fun r => by
            have h1 := r.2
            have h2 : (0 : ℤ) ≤ #r.1 := Int.natCast_nonneg _
            have : (k : ℝ) + 1 < 0 := lt_of_not_ge hk
            have : k + 1 < 0 := by exact_mod_cast this
            omega⟩
          simp
    _ = ((k : ℝ) + 1) * ‖v‖ ^ 2 := by
        congr 1
        rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [PiLp.norm_sq_eq_of_L2]

end L2

/-! ### Comparison with the interpolants of `Feec.FiniteElement.LocalDof` -/

namespace PolySeq

/-- The local interpolant of a polynomial family only depends on the vertex set of `T`. -/
theorem localInterp_congr (S : PolySeq) (k : ℕ) {T T' : Affine.Simplex ℝ (Fin n → ℝ) n}
    (h : vertexSet T = vertexSet T') (w : contForms n) :
    (((polyElement n S).localInterp T k w : (polyElement n S).space T k) : FormField n) =
      (((polyElement n S).localInterp T' k w : (polyElement n S).space T' k) : FormField n) := by
  have e := (polyElement n S).localSpace_ext T k (u := (polyElement n S).localInterp T k w)
    (v := ⟨((polyElement n S).localInterp T' k w : FormField n),
      ((polyElement n S).localInterp T' k w).2⟩) fun g hg i => by
      rw [LocalElement.localDof_localInterp _ _ _ _ _ hg]
      have hg' : g ⊆ vertexSet T' := h ▸ hg
      have := (polyElement n S).localDof_localInterp T' k w g hg' i
      rw [LocalElement.localDof_apply] at this ⊢
      exact this.symm
  exact congrArg Subtype.val e

/-- **The global trimmed families have the interpolants of `LocalDof`**: on an `n`-simplex `T`
whose vertices, in lexicographic order, are `q`, the canonical interpolant of a trimmed degree
`k` of an admissible sequence is `polyMinusInterp` for the vertex order `q` (the face moments of
`q ∘ e` are the DOFs of the faces `q(e(·))`, `lexEnum_image_comp`). -/
theorem localInterp_eq_polyMinusInterp (S : PolySeq) {k : ℕ} (hκ : S.kind k = .trimmed)
    (hk : k ≤ n) (T : Affine.Simplex ℝ (Fin n → ℝ) n) {q : Fin (n + 1) → Fin n → ℝ}
    (hq : StrictMono fun i => toLex (q i)) (hqT : ∀ x ∈ vertexSet T, ∃ i, q i = x)
    (hp : IsUnit (edgeMatrix q).det) (w : contDegForms n k) :
    (((polyElement n S).localInterp T k ⟨w, w.2.1⟩ : (polyElement n S).space T k) :
        FormField n) =
      (polyMinusInterp hp (S.one_le_deg k) hk w : FormField n) := by
  set PI := polyMinusInterp hp (S.one_le_deg k) hk
  have hmem : (PI w : FormField n) ∈ S.space n k := by
    have h := (localPolyMinusSpace_eq hp (S.deg k) k).le (PI w).2
    change _ ∈ (S.kind k).space n (S.deg k) k
    rw [hκ]
    exact h
  have hdegP : ∀ x, IsDeg k ((PI w : FormField n) x) := PolyKind.isDeg_of_mem_space hmem
  have hdegw : ∀ x, IsDeg k ((w : FormField n) x) := w.2.2
  have hPc : Continuous (PI w : FormField n) := (PolyKind.contDiff_of_mem_space hmem).continuous
  -- the moments of `PI w` and `w` against all test forms agree on the faces `q ∘ e`
  have key : ∀ {m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) {η : FormField m},
      η ∈ testSpaceMinus (S.deg k) k m →
        faceMoment q e η (PI w : FormField n) = faceMoment q e η (w : FormField n) := by
    intro m e η hη
    set B := testBasisMinus (S.deg k) k m
    have hηe : η = ∑ j, B.repr ⟨η, hη⟩ j • (B j : FormField m) := by
      have := congrArg (Subtype.val : testSpaceMinus (S.deg k) k m → FormField m)
        (B.sum_repr ⟨η, hη⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have hB : ∀ j, Continuous (B j : FormField m) := fun j =>
      (contDiff_of_mem_testSpaceMinus (B j).2).continuous
    rw [faceMoment_eq_vertexMoment, faceMoment_eq_vertexMoment, hηe,
      vertexMoment_sum_smul_right _ _ _ hB hPc,
      vertexMoment_sum_smul_right _ _ _ hB w.2.1]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have h := dof_interp (isUnisolvent_localDofMinus hp (S.one_le_deg k) hk)
      (fun i => polyMinusDof q (S.deg k) k i.1 i.2 ∘ₗ
        Submodule.inclusion (contDegForms_le_contForms k)) w ⟨Face.ofEmb e, j⟩
    simp only [localDofMinus, polyMinusDof, LinearMap.comp_apply, Face.emb_ofEmb] at h
    exact h
  have e := (polyElement n S).localSpace_ext T k (u := (polyElement n S).localInterp T k ⟨w, w.2.1⟩)
    (v := ⟨(PI w : FormField n), hmem⟩) fun g hg i => by
      rw [LocalElement.localDof_localInterp _ _ _ _ _ hg, LocalElement.localDof_apply]
      have hne : g.Nonempty := i.2
      have hgc : #g = #g - 1 + 1 := by have := card_pos.2 hne; omega
      obtain ⟨e, he⟩ := exists_orderEmb_comp_eq_lexEnum hq hgc fun x hx => hqT x (hg hx)
      change vertexMoment (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 : FormField (#g - 1))
          (degField k (w : FormField n)) =
        vertexMoment (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 : FormField (#g - 1))
          (degField k (PI w : FormField n))
      rw [degField_eq_self hdegw, degField_eq_self hdegP, ← he]
      have hb : (S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) ∈
          testSpaceMinus (S.deg k) k (#g - 1) := by
        have := (S.testBasis k (#g - 1) i.1).2
        change _ ∈ (S.kind k).test (S.deg k) k (#g - 1) at this
        rwa [hκ] at this
      exact (key e hb).symm
  exact congrArg Subtype.val e

end PolySeq

/-! ### The thesis' elements (Table 5.1) -/

namespace PolySeq

/-- The constant `1`-forms are test forms of `P₂Λ⁰` on edges. -/
theorem lagrangeP2_constOneTest_zero : lagrangeP2.ConstOneTest 0 :=
  constOneTest_of_two_le_deg _ (by simp)

/-- The constant `1`-forms are test forms of `P₂⁻Λ¹` on triangles. -/
theorem lagrangeP2_constOneTest_one : lagrangeP2.ConstOneTest 1 :=
  constOneTest_of_two_le_deg _ (by simp)

variable (M : SimplicialMesh n)

/-- **`S₀,ₕ = Π¹S⁰ : P₂Λ⁰ ⊗ ℝⁿ → P₁⁻Λ¹`** ([QuennevilleBelair2015], §5.3, (5.7)), with `Π¹` the
canonical interpolant. In a `Feec.BGG.Discrete` instance built from smoothed projections,
`Discrete.S0h = π¹ ∘ S⁰` is a different map; results about `bggS0h` (surjectivity, Props 5.8,
5.9(1)) do not transfer to it automatically. -/
def bggS0h : (Fin n → (polyElement n lagrangeP2).globalSpace M 0) →ₗ[ℝ]
    (polyElement n lowestOrder).globalSpace M 1 :=
  lagrangeP2.wsGlobal (M := M) lagrangeP2_constOneTest_zero

/-- **`S₁,ₕ = Π²S¹ : P₂⁻Λ¹ ⊗ ℝⁿ → P₁⁻Λ²`** ([QuennevilleBelair2015], §5.3, (5.7), with
`S₁ = 2 vskw`). -/
def bggS1h : (Fin n → (polyElement n lagrangeP2).globalSpace M 1) →ₗ[ℝ]
    (polyElement n lowestOrder).globalSpace M 2 :=
  lagrangeP2.wsGlobal (M := M) lagrangeP2_constOneTest_one

/-- **`S₀,ₕ` is onto `P₁⁻Λ̊¹`** from `P₂Λ̊⁰ ⊗ ℝⁿ` (vanishing boundary DOFs). -/
theorem bggS0h₀_surjective :
    Function.Surjective (lagrangeP2.wsGlobal₀ (M := M) lagrangeP2_constOneTest_zero) :=
  wsGlobal₀_surjective _

/-- **Thesis Prop 5.7, adapted**, for the elements of Table 5.1: `Π¹S⁰Π̃⁰ = Π¹S⁰` on continuous
fields (`Π²S¹Π̃¹ = Π²S¹` is `wsGlobal_tensorInterp` with `lagrangeP2_constOneTest_one`). -/
theorem bggS0h_tensorInterp (ψ : Fin n → contForms n) :
    bggS0h M ((polyElement n lagrangeP2).tensorInterp M n 0 ψ) =
      (polyElement n lowestOrder).globalInterp M 1 (coordWedgeC ψ) :=
  wsGlobal_tensorInterp _ ψ

end PolySeq

end Feec.FiniteElement

/-! ### Compatibility of a pair of smoothed projections -/

namespace Feec.HilbertComplex.Subcomplex.CommutingMap

variable {𝕜 : Type*} [RCLike 𝕜] {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)] {W' : ι' → Type*} [∀ i, NormedAddCommGroup (W' i)]
  [∀ i, InnerProductSpace 𝕜 (W' i)] [∀ i, CompleteSpace (W' i)]
  {H : HilbertComplex 𝕜 c W} {H' : HilbertComplex 𝕜 c' W'} {S : H.Subcomplex} {S' : H'.Subcomplex}
  [∀ i, FiniteDimensional 𝕜 (S.V i)] [∀ i, FiniteDimensional 𝕜 (S'.V i)]

/-- **Smoothed projections satisfy the surjectivity hypothesis (5.4)**: let `Q = Π R`,
`Q̃ = Π̃ R̃` be commuting maps into the two finite element rows and `𝒮 : W̃ⁱ → Wʲ` a connecting map
with `Q 𝒮 y = c Π' 𝒮 (Q̃ y)` (from `R 𝒮 = c 𝒮 R̃`, the dilation factor `c`, and
`Π 𝒮 Π̃ = Π 𝒮` on smooth fields, the adapted Prop 5.7; `A` is `Π 𝒮` on the discrete fields).
Then the smoothed projections `π = J⁻¹ Q`, `π̃ = J̃⁻¹ Q̃` satisfy `π 𝒮 π̃ = π 𝒮`: since
`Q̃ π̃ = Q̃`, `Q 𝒮 π̃ x = c A (Q̃ π̃ x) = c A (Q̃ x) = Q 𝒮 x`. This is `Feec.BGG.Discrete.Compatible`
(`P1 = π`, `Pt0 = π̃`, `S0 = 𝒮`) for smoothed projections. The hypothesis `hA` is not discharged
here for the cube smoothing (it combines `Feec.Models.Cube.WeakSymmetry.smoothForm_wsL2` with
`PolySeq.wsGlobal_tensorInterp`); this lemma is the abstract step only. -/
theorem toCochainProjection_comp_toCochainProjection (Q : S.CommutingMap) (Q' : S'.CommutingMap)
    {θ θ' : ℝ} (hθ : θ < 1) (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) (hθ' : θ' < 1)
    (hQ' : ∀ i, ∀ v ∈ S'.V i, ‖v - Q'.Q i v‖ ≤ θ' * ‖v‖) {i : ι'} {j : ι}
    (𝒮 : W' i →ₗ[𝕜] W j) (A : S'.V i →ₗ[𝕜] W j) (cst : 𝕜)
    (hA : ∀ y, Q.Q j (𝒮 y) = cst • A ⟨Q'.Q i y, Q'.mem i y⟩) (x : W' i) :
    (Q.toCochainProjection hθ hQ).π j (𝒮 ((Q'.toCochainProjection hθ' hQ').π i x)) =
      (Q.toCochainProjection hθ hQ).π j (𝒮 x) := by
  have h' : Q'.Q i ((Q'.toCochainProjection hθ' hQ').π i x) = Q'.Q i x := by
    rw [toCochainProjection_π]
    exact Q'.Q_restrictVEquiv_symm hθ' hQ' i _
  have key : Q.Q j (𝒮 ((Q'.toCochainProjection hθ' hQ').π i x)) = Q.Q j (𝒮 x) := by
    rw [hA, hA]
    congr 2
    exact Subtype.ext h'
  rw [toCochainProjection_π, toCochainProjection_π]
  exact congrArg (fun z : S.V j => (((Q.restrictVEquiv hθ hQ j).symm z : S.V j) : W j))
    (Subtype.ext key)

end Feec.HilbertComplex.Subcomplex.CommutingMap
