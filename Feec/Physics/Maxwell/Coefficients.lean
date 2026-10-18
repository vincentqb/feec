module

public import Feec.Physics.Maxwell.Media
public import Feec.Domain.L2Field
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Concrete media: multiplication by scalar and matrix fields

Concrete `Maxwell.Medium`s on the `L²` fields `ℓ²(ι; L²(μ))` (e.g. `L²(Ω; 𝕜^ι)`, `L2F`):

* **isotropic** media: the permittivity and permeability are multiplication by measurable scalar
  fields `ε(x)`, `μ(x)` with `a ≤ ε(x), μ(x) ≤ b` (`0 < a`) a.e., acting componentwise. The
  factors are built pointwise, `e = √ε`, `m = √μ`, so this works over `ℝ` as well as over `ℂ`
  (no functional calculus is needed), and the medium's `ε`, `μ` are exactly the multiplication
  operators (`Maxwell.Medium.isotropic_ε_apply`, `Maxwell.Medium.isotropic_μ_apply`);
* **anisotropic** media (over `ℂ`): multiplication by Hermitian `L^∞` matrix fields that are
  uniformly positive a.e. is bounded, self-adjoint and uniformly positive
  (`MeasureTheory.Lp.isSelfAdjoint_matMul`, `MeasureTheory.Lp.le_re_inner_matMul`), hence a
  medium by `Maxwell.Medium.exists_eq` (`Maxwell.Medium.exists_anisotropic`).

All results of `Feec.Physics.Maxwell.Media` and `Feec.Physics.Maxwell.Ohmic` (well-posedness,
energy conservation and decay, propagation of the weighted Gauss laws `div (ε E) = 0`,
`div (μ H) = 0`) then hold for such media, e.g. on every open `Ω ⊆ ℝ³` with PEC or PMC
(`Maxwell.pec_isotropic_gauss_propagates`); a pointwise nonnegative matrix conductivity satisfies
the Ohmic hypothesis `0 ≤ re ⟪σ E, E⟫` (`MeasureTheory.Lp.re_inner_matMul_nonneg`).

## Main definitions

* `MeasureTheory.Lp.mulL2 G`: multiplication by `G ∈ L^∞` on `L²`, with `‖mulL2 G‖ ≤ ‖G‖`.
* `MeasureTheory.Lp.diagL T`: the componentwise action of `T` on `ℓ²`-sums of copies.
* `MeasureTheory.Lp.matMul A`: multiplication by a matrix field, `(A u)_j = Σ_i A_{ji} u_i`.
* `Maxwell.isotropicFactor`: multiplication by `√s` for a measurable field `a ≤ s ≤ b`, an
  isomorphism with inverse multiplication by `1/√s`.
* `Maxwell.Medium.isotropic`: the isotropic medium with factors `√ε`, `√μ`.

## Main results

* `MeasureTheory.Lp.inner_mulL2`: `⟪G u, v⟫ = ⟪u, Ḡ v⟫`.
* `MeasureTheory.Lp.isSelfAdjoint_matMul`, `MeasureTheory.Lp.le_re_inner_matMul`.
* `Maxwell.Medium.isotropic_ε_apply`, `Maxwell.Medium.isotropic_μ_apply`:
  `(ε E)_j = ε(x) E_j(x)` and `(μ H)_j = μ(x) H_j(x)` a.e.
* `Maxwell.Medium.exists_anisotropic`.

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 8 (evolution problems)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4 (weighted `L²` inner products)
-/

open scoped InnerProductSpace ENNReal ComplexConjugate
open MeasureTheory Filter

@[expose] public noncomputable section

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {𝕜 : Type*} [RCLike 𝕜]

/-! ### Multiplication by an `L^∞` function on `L²` -/

/-- **Multiplication by `G ∈ L^∞(μ)`** on `L²(μ; 𝕜)`, `u ↦ G u`, bounded by `‖G‖`. -/
def mulL2 (G : Lp 𝕜 ∞ μ) : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun u => G • u
      map_add' := Lp.add_smul G
      map_smul' := fun c u => (Lp.smul_comm c G u).symm }
    ‖G‖ fun u => Lp.norm_smul_le G u

theorem mulL2_apply (G : Lp 𝕜 ∞ μ) (u : Lp 𝕜 2 μ) : mulL2 G u = G • u := rfl

theorem coeFn_mulL2 (G : Lp 𝕜 ∞ μ) (u : Lp 𝕜 2 μ) :
    mulL2 G u =ᵐ[μ] fun x => G x * u x :=
  Lp.coeFn_lpSMul (r := 2) G u

/-- Composition of multiplications: `G (H u) = K u` if `K = G H` a.e. -/
theorem mulL2_mulL2 {G H K : Lp 𝕜 ∞ μ} (h : ∀ᵐ x ∂μ, K x = G x * H x) (u : Lp 𝕜 2 μ) :
    mulL2 G (mulL2 H u) = mulL2 K u := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL2 G (mulL2 H u), coeFn_mulL2 H u, coeFn_mulL2 K u, h] with
    x h1 h2 h3 h4
  rw [h1, h2, h3, h4, mul_assoc]

/-- Multiplication by `1` is the identity. -/
theorem mulL2_of_eq_one {G : Lp 𝕜 ∞ μ} (h : ∀ᵐ x ∂μ, G x = 1) (u : Lp 𝕜 2 μ) :
    mulL2 G u = u := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL2 G u, h] with x h1 h2
  rw [h1, h2, one_mul]

/-- **The adjoint of a multiplication** is multiplication by the conjugate:
`⟪G u, v⟫ = ⟪u, G' v⟫` for `G' = Ḡ` a.e. -/
theorem inner_mulL2 {G G' : Lp 𝕜 ∞ μ} (h : ∀ᵐ x ∂μ, G' x = conj (G x)) (u v : Lp 𝕜 2 μ) :
    ⟪mulL2 G u, v⟫_𝕜 = ⟪u, mulL2 G' v⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulL2 G u, coeFn_mulL2 G' v, h] with x h1 h2 h3
  simp only [h1, h2, h3, RCLike.inner_apply, map_mul]
  ring

/-- A bounded a.e.-strongly measurable function as an element of `L^∞`. -/
def ofBound (g : α → 𝕜) (hg : AEStronglyMeasurable g μ) (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    Lp 𝕜 ∞ μ :=
  (memLp_top_of_bound hg C hC).toLp g

theorem coeFn_ofBound (g : α → 𝕜) (hg : AEStronglyMeasurable g μ) (C : ℝ)
    (hC : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) : ofBound g hg C hC =ᵐ[μ] g :=
  MemLp.coeFn_toLp _

/-! ### Componentwise action on `ℓ²`-sums -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {ι : Type*} [Fintype ι]

/-- The **componentwise action** of `T` on `ℓ²(ι; E)`: `(T u)_j = T (u_j)`. -/
def diagL (T : E →L[𝕜] E) : PiLp 2 (fun _ : ι => E) →L[𝕜] PiLp 2 (fun _ : ι => E) :=
  ((PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => E)).symm :
      (ι → E) →L[𝕜] PiLp 2 (fun _ : ι => E)).comp
    ((ContinuousLinearMap.pi fun j => T.comp (ContinuousLinearMap.proj j)).comp
      (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => E) : PiLp 2 (fun _ : ι => E) →L[𝕜] ι → E))

omit [Fintype ι] in
theorem diagL_apply (T : E →L[𝕜] E) (u : PiLp 2 (fun _ : ι => E)) (j : ι) :
    diagL T u j = T (u j) := rfl

omit [Fintype ι] in
theorem diagL_diagL (T T' : E →L[𝕜] E) (u : PiLp 2 (fun _ : ι => E)) :
    diagL T (diagL T' u) = diagL (T.comp T') u := rfl

theorem inner_diagL {T T' : E →L[𝕜] E} (h : ∀ x y, ⟪T x, y⟫_𝕜 = ⟪x, T' y⟫_𝕜)
    (u v : PiLp 2 (fun _ : ι => E)) :
    ⟪diagL T u, v⟫_𝕜 = ⟪u, diagL T' v⟫_𝕜 := by
  simp only [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => h (u j) (v j)

/-! ### Multiplication by a matrix field -/

section Matrix

variable {ι : Type*} [Fintype ι]

/-- **Multiplication by a matrix field** `A = (A_{ji}) ∈ L^∞(μ)^{ι×ι}` on `ℓ²(ι; L²(μ))`:
`(A u)_j = Σ_i A_{ji} u_i`. -/
def matMul (A : ι → ι → Lp 𝕜 ∞ μ) :
    PiLp 2 (fun _ : ι => Lp 𝕜 2 μ) →L[𝕜] PiLp 2 (fun _ : ι => Lp 𝕜 2 μ) :=
  ((PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => Lp 𝕜 2 μ)).symm :
      (ι → Lp 𝕜 2 μ) →L[𝕜] PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)).comp
    ((ContinuousLinearMap.pi fun j => ∑ i, (mulL2 (A j i)).comp (ContinuousLinearMap.proj i)).comp
      (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => Lp 𝕜 2 μ) :
        PiLp 2 (fun _ : ι => Lp 𝕜 2 μ) →L[𝕜] ι → Lp 𝕜 2 μ))

theorem matMul_apply (A : ι → ι → Lp 𝕜 ∞ μ) (u : PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)) (j : ι) :
    matMul A u j = ∑ i, mulL2 (A j i) (u i) := by
  simp [matMul]

theorem inner_matMul (A : ι → ι → Lp 𝕜 ∞ μ) (u v : PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)) :
    ⟪matMul A u, v⟫_𝕜 = ∑ j, ∑ i, ⟪mulL2 (A j i) (u i), v j⟫_𝕜 := by
  rw [PiLp.inner_apply]
  simp_rw [matMul_apply, sum_inner]

/-- A **Hermitian** matrix field (`A_{ij} = conj A_{ji}` a.e.) gives a symmetric multiplication. -/
theorem inner_matMul_eq_inner {A : ι → ι → Lp 𝕜 ∞ μ}
    (hA : ∀ i j, ∀ᵐ x ∂μ, A i j x = conj (A j i x)) (u v : PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)) :
    ⟪matMul A u, v⟫_𝕜 = ⟪u, matMul A v⟫_𝕜 := by
  rw [inner_matMul, PiLp.inner_apply]
  simp_rw [matMul_apply, inner_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => inner_mulL2 (hA i j) _ _

/-- Multiplication by a Hermitian matrix field is **self-adjoint**. -/
theorem isSelfAdjoint_matMul {A : ι → ι → Lp 𝕜 ∞ μ}
    (hA : ∀ i j, ∀ᵐ x ∂μ, A i j x = conj (A j i x)) : IsSelfAdjoint (matMul A) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun u v => inner_matMul_eq_inner hA u v

/-- **Pointwise coercivity gives coercivity**: if `c |v|² ≤ re ⟪A(x) v, v⟫` for all `v ∈ 𝕜^ι`
and a.e. `x`, then `c ‖u‖² ≤ re ⟪A u, u⟫` on `ℓ²(ι; L²)` (for `c = 0`: a nonnegative field
gives a nonnegative operator). -/
theorem le_re_inner_matMul {A : ι → ι → Lp 𝕜 ∞ μ} {c : ℝ}
    (hc : ∀ᵐ x ∂μ, ∀ v : ι → 𝕜,
      c * ∑ j, ‖v j‖ ^ 2 ≤ RCLike.re (∑ j, conj (∑ i, A j i x * v i) * v j))
    (u : PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)) :
    c * ‖u‖ ^ 2 ≤ RCLike.re ⟪matMul A u, u⟫_𝕜 := by
  have hint : ∀ j i, Integrable (fun x => conj (A j i x * u i x) * u j x) μ := fun j i =>
    (L2.integrable_inner (𝕜 := 𝕜) (mulL2 (A j i) (u i)) (u j)).congr (by
      filter_upwards [coeFn_mulL2 (A j i) (u i)] with x hx
      rw [RCLike.inner_apply, hx, mul_comm])
  have hintj : ∀ j, Integrable (fun x => conj (∑ i, A j i x * u i x) * u j x) μ := fun j => by
    simp_rw [map_sum, Finset.sum_mul]
    exact integrable_finsetSum _ fun i _ => hint j i
  have hsq : ∀ j, Integrable (fun x => ‖u j x‖ ^ 2) μ := fun j =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (u j))).1 (Lp.memLp (u j))
  have hn : ∀ j, ‖u j‖ ^ 2 = ∫ x, ‖u j x‖ ^ 2 ∂μ := fun j => by
    rw [@norm_sq_eq_re_inner 𝕜, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
    simp_rw [inner_self_eq_norm_sq]
  have hi : ⟪matMul A u, u⟫_𝕜 = ∫ x, ∑ j, conj (∑ i, A j i x * u i x) * u j x ∂μ := by
    rw [inner_matMul, integral_finsetSum _ fun j _ => hintj j]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [map_sum, Finset.sum_mul]
    rw [integral_finsetSum _ fun i _ => hint j i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_mulL2 (A j i) (u i)] with x hx
    rw [RCLike.inner_apply, hx, mul_comm]
  rw [hi, ← integral_re (integrable_finsetSum _ fun j _ => hintj j), PiLp.norm_sq_eq_of_L2]
  simp_rw [hn]
  rw [← integral_finsetSum _ fun j _ => hsq j, ← integral_const_mul]
  refine integral_mono_ae ((integrable_finsetSum _ fun j _ => hsq j).const_mul c)
    (integrable_finsetSum _ fun j _ => hintj j).re ?_
  filter_upwards [hc] with x hx
  exact hx fun i => u i x

/-- A pointwise **nonnegative** matrix field (e.g. a conductivity `σ(x) ≥ 0`) gives
`0 ≤ re ⟪σ u, u⟫`, the hypothesis of the Ohmic-loss results (`Maxwell.Medium.ohmic`). -/
theorem re_inner_matMul_nonneg {A : ι → ι → Lp 𝕜 ∞ μ}
    (hc : ∀ᵐ x ∂μ, ∀ v : ι → 𝕜, 0 ≤ RCLike.re (∑ j, conj (∑ i, A j i x * v i) * v j))
    (u : PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)) : 0 ≤ RCLike.re ⟪matMul A u, u⟫_𝕜 := by
  have := le_re_inner_matMul (c := 0) (by filter_upwards [hc] with x hx v; simpa using hx v) u
  simpa using this

end Matrix

end MeasureTheory.Lp

namespace Feec.Maxwell

open MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {𝕜 : Type*} [RCLike 𝕜]
  {ι : Type*} [Fintype ι]

/-! ### The factor `√s` of a scalar field -/

section Factor

variable {s : α → ℝ} {a b : ℝ}

theorem aestronglyMeasurable_sqrt (hs : AEStronglyMeasurable s μ) :
    AEStronglyMeasurable (fun x => ((√(s x) : ℝ) : 𝕜)) μ :=
  RCLike.continuous_ofReal.comp_aestronglyMeasurable
    (Real.continuous_sqrt.comp_aestronglyMeasurable hs)

theorem aestronglyMeasurable_inv_sqrt (hs : AEStronglyMeasurable s μ) :
    AEStronglyMeasurable (fun x => (((√(s x))⁻¹ : ℝ) : 𝕜)) μ :=
  RCLike.continuous_ofReal.comp_aestronglyMeasurable
    ((Real.continuous_sqrt.comp_aestronglyMeasurable hs).aemeasurable.inv.aestronglyMeasurable)

theorem norm_sqrt_le (hab : ∀ᵐ x ∂μ, a ≤ s x ∧ s x ≤ b) :
    ∀ᵐ x ∂μ, ‖((√(s x) : ℝ) : 𝕜)‖ ≤ √b := by
  filter_upwards [hab] with x hx
  rw [RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hx.2

theorem norm_inv_sqrt_le (ha : 0 < a) (hab : ∀ᵐ x ∂μ, a ≤ s x ∧ s x ≤ b) :
    ∀ᵐ x ∂μ, ‖(((√(s x))⁻¹ : ℝ) : 𝕜)‖ ≤ (√a)⁻¹ := by
  filter_upwards [hab] with x hx
  rw [RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  exact inv_anti₀ (Real.sqrt_pos.2 ha) (Real.sqrt_le_sqrt hx.1)

variable (hs : AEStronglyMeasurable s μ) (ha : 0 < a) (hab : ∀ᵐ x ∂μ, a ≤ s x ∧ s x ≤ b)

variable (𝕜) in
/-- `√s ∈ L^∞`. -/
def sqrtField : Lp 𝕜 ∞ μ :=
  ofBound _ (aestronglyMeasurable_sqrt (𝕜 := 𝕜) hs) _ (norm_sqrt_le hab)

variable (𝕜) in
/-- `1/√s ∈ L^∞`. -/
def invSqrtField : Lp 𝕜 ∞ μ :=
  ofBound _ (aestronglyMeasurable_inv_sqrt (𝕜 := 𝕜) hs) _ (norm_inv_sqrt_le ha hab)

theorem coeFn_sqrtField : sqrtField 𝕜 hs hab =ᵐ[μ] fun x => ((√(s x) : ℝ) : 𝕜) :=
  coeFn_ofBound _ _ _ _

theorem coeFn_invSqrtField :
    invSqrtField 𝕜 hs ha hab =ᵐ[μ] fun x => (((√(s x))⁻¹ : ℝ) : 𝕜) :=
  coeFn_ofBound _ _ _ _

theorem invSqrtField_mul_sqrtField :
    ∀ᵐ x ∂μ, invSqrtField 𝕜 hs ha hab x * sqrtField 𝕜 hs hab x = 1 := by
  filter_upwards [coeFn_sqrtField (𝕜 := 𝕜) hs hab, coeFn_invSqrtField (𝕜 := 𝕜) hs ha hab, hab] with x h1 h2 h3
  rw [h1, h2, ← RCLike.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.2 (ha.trans_le h3.1)).ne',
    RCLike.ofReal_one]

theorem sqrtField_mul_invSqrtField :
    ∀ᵐ x ∂μ, sqrtField 𝕜 hs hab x * invSqrtField 𝕜 hs ha hab x = 1 := by
  filter_upwards [invSqrtField_mul_sqrtField (𝕜 := 𝕜) hs ha hab] with x h
  rw [mul_comm, h]

variable (𝕜 ι) in
/-- The **factor** `e = √s` of the multiplication by a scalar field `a ≤ s ≤ b` (`0 < a`), acting
componentwise on `ℓ²(ι; L²(μ))`: an isomorphism with inverse `1/√s`. -/
def isotropicFactor : PiLp 2 (fun _ : ι => Lp 𝕜 2 μ) ≃L[𝕜] PiLp 2 (fun _ : ι => Lp 𝕜 2 μ) :=
  ContinuousLinearEquiv.equivOfInverse (diagL (mulL2 (sqrtField 𝕜 hs hab)))
    (diagL (mulL2 (invSqrtField 𝕜 hs ha hab)))
    (fun u => PiLp.ext fun j => by
      change mulL2 _ (mulL2 _ (u j)) = u j
      refine Lp.ext ?_
      filter_upwards [coeFn_mulL2 (invSqrtField 𝕜 hs ha hab) (mulL2 (sqrtField 𝕜 hs hab) (u j)),
        coeFn_mulL2 (sqrtField 𝕜 hs hab) (u j), invSqrtField_mul_sqrtField (𝕜 := 𝕜) hs ha hab] with
        x h1 h2 h3
      rw [h1, h2, ← mul_assoc, h3, one_mul])
    (fun u => PiLp.ext fun j => by
      change mulL2 _ (mulL2 _ (u j)) = u j
      refine Lp.ext ?_
      filter_upwards [coeFn_mulL2 (sqrtField 𝕜 hs hab) (mulL2 (invSqrtField 𝕜 hs ha hab) (u j)),
        coeFn_mulL2 (invSqrtField 𝕜 hs ha hab) (u j), sqrtField_mul_invSqrtField (𝕜 := 𝕜) hs ha hab] with
        x h1 h2 h3
      rw [h1, h2, ← mul_assoc, h3, one_mul])

omit [Fintype ι] in
theorem isotropicFactor_apply (u : PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)) (j : ι) :
    isotropicFactor 𝕜 ι hs ha hab u j = mulL2 (sqrtField 𝕜 hs hab) (u j) := rfl

/-- The factor `√s` is **self-adjoint**. -/
theorem adjoint_isotropicFactor :
    ContinuousLinearMap.adjoint (isotropicFactor 𝕜 ι hs ha hab :
      PiLp 2 (fun _ : ι => Lp 𝕜 2 μ) →L[𝕜] PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)) =
      (isotropicFactor 𝕜 ι hs ha hab :
      PiLp 2 (fun _ : ι => Lp 𝕜 2 μ) →L[𝕜] PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun u v => ?_).symm
  refine inner_diagL (fun x y => inner_mulL2 ?_ x y) u v
  filter_upwards [coeFn_sqrtField (𝕜 := 𝕜) hs hab] with x h
  rw [h, RCLike.conj_ofReal]

/-- `(√s)† √s` is **multiplication by `s`**: `((√s)† √s u)_j = s u_j` a.e. -/
theorem adjoint_isotropicFactor_comp_apply (u : PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)) (j : ι) :
    (ContinuousLinearMap.adjoint (isotropicFactor 𝕜 ι hs ha hab :
      PiLp 2 (fun _ : ι => Lp 𝕜 2 μ) →L[𝕜] PiLp 2 (fun _ : ι => Lp 𝕜 2 μ))
      (isotropicFactor 𝕜 ι hs ha hab u)) j =ᵐ[μ] fun x => (s x : 𝕜) * u j x := by
  rw [adjoint_isotropicFactor]
  change (mulL2 _ (mulL2 _ (u j)) : Lp 𝕜 2 μ) =ᵐ[μ] _
  filter_upwards [coeFn_mulL2 (sqrtField 𝕜 hs hab) (mulL2 (sqrtField 𝕜 hs hab) (u j)),
    coeFn_mulL2 (sqrtField 𝕜 hs hab) (u j), coeFn_sqrtField (𝕜 := 𝕜) hs hab, hab] with x h1 h2 h3 h4
  rw [h1, h2, h3, ← mul_assoc, ← RCLike.ofReal_mul,
    Real.mul_self_sqrt (ha.le.trans h4.1)]

end Factor

/-! ### The isotropic medium -/

variable {κ : Type*} [Fintype κ]
  {ε μ' : α → ℝ} (hε : AEStronglyMeasurable ε μ) (hμ : AEStronglyMeasurable μ' μ) {a b : ℝ}
  (ha : 0 < a) (hεb : ∀ᵐ x ∂μ, a ≤ ε x ∧ ε x ≤ b) (hμb : ∀ᵐ x ∂μ, a ≤ μ' x ∧ μ' x ≤ b)

variable (𝕜 ι κ) in
/-- The **isotropic inhomogeneous medium** with permittivity `ε(x)` and permeability `μ(x)`,
measurable scalar fields with `a ≤ ε(x), μ(x) ≤ b`, `0 < a`, acting componentwise on the
electric fields `ℓ²(ι; L²)` and the magnetic fields `ℓ²(κ; L²)`: factors `e = √ε`, `m = √μ`. -/
def Medium.isotropic :
    Medium 𝕜 (PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)) (PiLp 2 (fun _ : κ => Lp 𝕜 2 μ)) where
  e := isotropicFactor 𝕜 ι hε ha hεb
  m := isotropicFactor 𝕜 κ hμ ha hμb

/-- The permittivity of the isotropic medium is **multiplication by `ε(x)`**. -/
theorem Medium.isotropic_ε_apply (u : PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)) (j : ι) :
    ((Medium.isotropic 𝕜 ι κ hε hμ ha hεb hμb).ε u) j =ᵐ[μ] fun x => (ε x : 𝕜) * u j x :=
  adjoint_isotropicFactor_comp_apply hε ha hεb u j

/-- The permeability of the isotropic medium is **multiplication by `μ(x)`**. -/
theorem Medium.isotropic_μ_apply (u : PiLp 2 (fun _ : κ => Lp 𝕜 2 μ)) (j : κ) :
    ((Medium.isotropic 𝕜 ι κ hε hμ ha hεb hμb).μ u) j =ᵐ[μ] fun x => (μ' x : 𝕜) * u j x :=
  adjoint_isotropicFactor_comp_apply hμ ha hμb u j

/-! ### Anisotropic media (over `ℂ`) -/

/-- **Anisotropic inhomogeneous media are media** (over `ℂ`): for Hermitian matrix fields
`A = ε(x)`, `B = μ(x)` in `L^∞` with `c |v|² ≤ re ⟪A(x) v, v⟫`, `c |v|² ≤ re ⟪B(x) v, v⟫`
(`c > 0`) a.e., there is a `Maxwell.Medium` whose permittivity and permeability are the
multiplication operators (factors `e = ε^{1/2}`, `m = μ^{1/2}`, `Maxwell.Medium.exists_eq`). -/
theorem Medium.exists_anisotropic {κ : Type*} [Fintype κ] {A : ι → ι → Lp ℂ ∞ μ}
    {B : κ → κ → Lp ℂ ∞ μ} (hA : ∀ i j, ∀ᵐ x ∂μ, A i j x = conj (A j i x))
    (hB : ∀ i j, ∀ᵐ x ∂μ, B i j x = conj (B j i x)) {c : ℝ} (hc : 0 < c)
    (hcA : ∀ᵐ x ∂μ, ∀ v : ι → ℂ,
      c * ∑ j, ‖v j‖ ^ 2 ≤ RCLike.re (∑ j, conj (∑ i, A j i x * v i) * v j))
    (hcB : ∀ᵐ x ∂μ, ∀ v : κ → ℂ,
      c * ∑ j, ‖v j‖ ^ 2 ≤ RCLike.re (∑ j, conj (∑ i, B j i x * v i) * v j)) :
    ∃ M : Medium ℂ (PiLp 2 (fun _ : ι => Lp ℂ 2 μ)) (PiLp 2 (fun _ : κ => Lp ℂ 2 μ)),
      M.ε = matMul A ∧ M.μ = matMul B :=
  Medium.exists_eq (isSelfAdjoint_matMul hA) (isSelfAdjoint_matMul hB) hc (le_re_inner_matMul hcA)
    (le_re_inner_matMul hcB)

/-! ### Isotropic media on domains of `ℝ³` -/

section Domain

open Feec.Domain Set ShortHilbertComplex

variable {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) [Fact (IsOpen Ω)] {ε μ' : (Fin 3 → ℝ) → ℝ}
  (hε : AEStronglyMeasurable ε (volume.restrict Ω)) (hμ : AEStronglyMeasurable μ' (volume.restrict Ω))
  {a b : ℝ} (ha : 0 < a) (hεb : ∀ᵐ x ∂(volume.restrict Ω), a ≤ ε x ∧ ε x ≤ b)
  (hμb : ∀ᵐ x ∂(volume.restrict Ω), a ≤ μ' x ∧ μ' x ≤ b)

/-- **Maxwell in an isotropic inhomogeneous medium with a perfect electric conductor** on any
open `Ω ⊆ ℝ³`: for measurable `a ≤ ε(x), μ(x) ≤ b` (`0 < a`), the weighted Gauss laws `σ = 0`,
`div (ε E) = 0`, `div (μ H) = 0` with `μ H · n = 0` propagate. -/
theorem pec_isotropic_gauss_propagates {t₀ t₁ : ℝ}
    {F U : ℝ → PiLp 2 (W3 (L2F 𝕜 Ω (Fin 1)) (L2F 𝕜 Ω (Fin 1 × Fin 3)) (L2F 𝕜 Ω (Fin 1 × Fin 3)))}
    (hU : Evolution.IsStrongSolution
      ((Medium.isotropic 𝕜 (Fin 1 × Fin 3) (Fin 1 × Fin 3) hε hμ ha hεb hμb).maxwell (pec 𝕜 hΩ))
      (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ (Medium.isotropic 𝕜 (Fin 1 × Fin 3) (Fin 1 × Fin 3) hε hμ ha hεb hμb).gauss
      (pec 𝕜 hΩ) (magneticPEC 𝕜 Ω))
    (hF : ∀ t ∈ Icc t₀ t₁, F t ∈
      (Medium.isotropic 𝕜 (Fin 1 × Fin 3) (Fin 1 × Fin 3) hε hμ ha hεb hμb).gauss (pec 𝕜 hΩ)
        (magneticPEC 𝕜 Ω)) :
    ∀ t ∈ Icc t₀ t₁, U t ∈
      (Medium.isotropic 𝕜 (Fin 1 × Fin 3) (Fin 1 × Fin 3) hε hμ ha hεb hμb).gauss (pec 𝕜 hΩ)
        (magneticPEC 𝕜 Ω) :=
  pec_gauss_propagates_medium hΩ _ hU h0 hF

end Domain

end Feec.Maxwell
