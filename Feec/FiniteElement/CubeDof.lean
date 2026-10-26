module

public import Feec.Algebra.CubicalForm
public import Feec.Algebra.Wedge
public import Feec.FiniteElement.Dof
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Degrees of freedom of `Q_r⁻Λᵏ`: unisolvence, traces and the commuting interpolant

The degrees of freedom of the tensor-product family `Q_r⁻Λᵏ` on the cube `[0, 1]ⁿ`
([ArnoldBoffiBonizzoni2015], §3; [ArnoldAwanou2014], §2) are the moments

  `ω ↦ ∫_g tr_g ω ∧ η`, `η ∈ Q_{r-1}⁻Λ^{m-k}(g)`,

over the faces `g` of dimension `m ≥ k`. We index them like the monomial basis `x^α dx_s` of
`Q_b⁻Λᵏ` (`Feec.Koszul.cubeFormMinus`, degrees `b_j` in each direction): the degree of freedom
`(s, α)` lives on the face `dofFace f s α`, where a direction `j ∉ s` with `α_j ∈ {0, 1}` is
fixed at the endpoint `x_j = α_j`, against the test monomial `x^β dx_{G ∖ s}` (`dofTest`). On
monomials it is a tensor product of one-dimensional degrees of freedom (`cubeDof_apply`): in each
direction, the endpoint values and the moments against `P_{r-2}` on `P_rΛ⁰(I)`, the moments
against `P_{r-1}` on `P_{r-1}Λ¹(I)`. Unisolvence thus reduces to the one-dimensional case and the
invertibility of Kronecker products.

Everything is stated on a face `f : d → Option ℝ` of the cube (`f j = some c`: the direction `j`
is fixed at `x_j = c`; `f = fun _ => none`: the cube itself) and a degree `b` on it
(`IsFaceDeg f b`: `b_j ≥ 1` free, `b_j = 0` fixed), the space being `cubeFormMinus ℝ b k`; for
`b ≥ 1` the face space is `faceDeg b f` (`isFaceDeg_faceDeg`). This gives the trace
determination for free.

## Main definitions

* `Feec.FiniteElement.Cube.unitIntegral`: `∫_{[0,1]^d}` on polynomials (`unitIntegral_eq_integral`);
* `Feec.FiniteElement.Cube.cubeMoment g η ω = ∫_g tr_g ω ∧ η`;
* `Feec.FiniteElement.Cube.edgeDof`, `tensorDof`: the one-dimensional degrees of
  freedom and their tensor products;
* `Feec.FiniteElement.Cube.momentDof f s α`, `Feec.FiniteElement.Cube.CubeDofIdx b k`,
  `Feec.FiniteElement.Cube.cubeDof f i`: the degrees of freedom of `Q_b⁻Λᵏ(f)`, indexed like the
  monomial basis;
* `Feec.FiniteElement.Cube.IsFaceDeg f b`: `b` is a degree on the face `f`;
* `Feec.FiniteElement.Cube.cubeInterp f b k hfb`: the canonical interpolant onto `Q_b⁻Λᵏ(f)`.

## Main results

* `eq_zero_of_moments_eq_zero`, `eq_zero_of_endpoints_moments_eq_zero`, `edgeDof_injective`:
  one-dimensional unisolvence; `eq_zero_of_kronecker`: Kronecker products of invertible matrices
  are invertible;
* `momentDof_apply`: the degrees of freedom are tensor products of one-dimensional ones;
  `dofTest_mem_cubeFormMinus`: the test forms lie in `Q_{b-1}⁻Λ^{m-k}` of their face;
* `card_cubeDofIdx`, `isUnisolvent_cubeDof`: **unisolvence of the degrees of freedom of
  `Q_b⁻Λᵏ(f)`**, for all `n`, `k` and degrees `b`, on the cube and on each of its faces
  ([ArnoldBoffiBonizzoni2015], §3);
* `cubeTrace_eq_zero_of_cubeDof_eq_zero`: **the degrees of freedom of the faces of `f` determine
  the trace on `f`**;
* `cubeDof_extDeriv_mem_span`: **Stokes compatibility**, `ℓ ∘ d` is a combination of
  degrees of freedom (one-dimensional integration by parts, `edgeDof_pderiv`), hence
  `cubeInterp_extDeriv`: **the canonical interpolant commutes with `d`**.

## References

* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §3 (degrees of freedom, unisolvence and the commuting projection of `Q_r⁻Λᵏ`)
* [D. N. Arnold, G. Awanou, *Finite element differential forms on cubical meshes*][ArnoldAwanou2014],
  §2 (the tensor-product construction)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset

@[expose] public noncomputable section

namespace Feec.FiniteElement.Cube

/-! ### One-dimensional moments -/

section OneDim

open Polynomial

/-- The moments of `P = Σ_γ v_γ x^γ`: `∫₀¹ xⁱ P = Σ_γ v_γ / (γ + i + 1)`. -/
theorem integral_pow_mul_sum {n : ℕ} (v : Fin n → ℝ) (i : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ i * (∑ γ : Fin n, C (v γ) * X ^ (γ : ℕ)).eval x =
      ∑ γ : Fin n, v γ * ((γ + i + 1 : ℕ) : ℝ)⁻¹ := by
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, mul_sum]
  rw [intervalIntegral.integral_finsetSum fun γ _ =>
    (by fun_prop : Continuous fun x : ℝ => x ^ i * (v γ * x ^ (γ : ℕ))).intervalIntegrable _ _]
  refine sum_congr rfl fun γ _ => ?_
  rw [show (fun x : ℝ => x ^ i * (v γ * x ^ (γ : ℕ))) = fun x => v γ * x ^ ((γ : ℕ) + i) by
    funext x; ring, intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  ring

/-- `∫₀¹ w p² = 0` with `w > 0` on `(0, 1)`, `w ≥ 0` on `[0, 1]`, forces `p = 0`. -/
theorem eq_zero_of_integral_mul_sq_eq_zero {w p : ℝ[X]}
    (hw0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ w.eval x) (hw : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < w.eval x)
    (h : ∫ x in (0 : ℝ)..1, w.eval x * p.eval x ^ 2 = 0) : p = 0 := by
  by_contra hp
  have hcont : Continuous fun x => w.eval x * p.eval x ^ 2 := w.continuous.mul (p.continuous.pow 2)
  have hpos : 0 < ∫ x in (0 : ℝ)..1, w.eval x * p.eval x ^ 2 := by
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae']
    · refine ⟨zero_lt_one, ?_⟩
      have hfin : {x | p.eval x = 0}.Finite := p.finite_setOfPred_isRoot hp
      calc (0 : ENNReal) < MeasureTheory.volume (Set.Ioo (0 : ℝ) 1 \ {x | p.eval x = 0}) := by
            rw [MeasureTheory.measure_sdiff_null (hfin.measure_zero _)]; simp
        _ ≤ _ := MeasureTheory.measure_mono fun x hx =>
            Set.mem_inter
              (Function.mem_support.2 (mul_ne_zero (hw x hx.1).ne' (pow_ne_zero 2 hx.2)))
              (Set.Ioo_subset_Ioc_self hx.1)
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).2
        (MeasureTheory.ae_of_all _ fun x hx => mul_nonneg (hw0 x ?_) (sq_nonneg _))
      rw [Set.uIoc_of_le zero_le_one] at hx
      exact Set.Ioc_subset_Icc_self hx
    · exact hcont.intervalIntegrable _ _
  exact hpos.ne' h

theorem coeff_sum_C_mul_X_pow {n : ℕ} (v : Fin n → ℝ) (γ : Fin n) :
    (∑ γ' : Fin n, C (v γ') * X ^ (γ' : ℕ)).coeff γ = v γ := by
  rw [finsetSum_coeff, sum_eq_single γ (fun γ' _ h => by
    rw [coeff_C_mul_X_pow, ite_eq_right (fun h' => h (Fin.ext h'.symm))]) (by simp)]
  simp

/-- **Unisolvence of the moments on `P_{n-1}(I)`**: `∫₀¹ xⁱ P = 0` for `i < n` forces `P = 0`
(the Hilbert matrix `1/(γ + i + 1)` is invertible). -/
theorem eq_zero_of_moments_eq_zero {n : ℕ} {v : Fin n → ℝ}
    (h : ∀ i : Fin n, ∑ γ : Fin n, v γ * ((γ + i + 1 : ℕ) : ℝ)⁻¹ = 0) : v = 0 := by
  set P := ∑ γ : Fin n, C (v γ) * X ^ (γ : ℕ)
  have hP : P = 0 := by
    refine eq_zero_of_integral_mul_sq_eq_zero (w := 1) (by simp) (by simp) ?_
    have : ∀ x : ℝ, (1 : ℝ[X]).eval x * P.eval x ^ 2 =
        ∑ i : Fin n, v i * (x ^ (i : ℕ) * P.eval x) := fun x => by
      have hPe : P.eval x = ∑ i : Fin n, v i * x ^ (i : ℕ) := by
        simp only [P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      rw [eval_one, one_mul, sq]
      conv_lhs => arg 1; rw [hPe]
      rw [sum_mul]; exact sum_congr rfl fun i _ => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_finsetSum fun i _ =>
      (by have := P.continuous; fun_prop :
        Continuous fun x : ℝ => v i * (x ^ (i : ℕ) * P.eval x)).intervalIntegrable _ _]
    refine sum_eq_zero fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_pow_mul_sum, h i, mul_zero]
  funext γ
  rw [← coeff_sum_C_mul_X_pow v γ]
  exact (congrArg (coeff · γ) hP).trans (coeff_zero _)

/-- **Unisolvence of the endpoint values and moments on `P_r(I)`**: `P(0) = P(1) = 0` and
`∫₀¹ xⁱ P = 0` for `i < r - 1` force `P = 0` (`P = x (x - 1) g` with `∫₀¹ x (1 - x) g² = 0`). -/
theorem eq_zero_of_endpoints_moments_eq_zero {r : ℕ} {v : Fin (r + 1) → ℝ}
    (h0 : ∑ γ : Fin (r + 1), v γ * 0 ^ (γ : ℕ) = 0) (h1 : ∑ γ : Fin (r + 1), v γ = 0)
    (h : ∀ i < r - 1, ∑ γ : Fin (r + 1), v γ * ((γ + i + 1 : ℕ) : ℝ)⁻¹ = 0) : v = 0 := by
  set P := ∑ γ : Fin (r + 1), C (v γ) * X ^ (γ : ℕ)
  have hev : ∀ x, P.eval x = ∑ γ : Fin (r + 1), v γ * x ^ (γ : ℕ) := fun x => by
    simp only [P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  have hdeg : P.natDegree ≤ r := natDegree_sum_le_of_forall_le _ _ fun γ _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  have hP0 : P.IsRoot 0 := by rw [IsRoot, hev]; exact h0
  have hP1 : P.IsRoot 1 := by rw [IsRoot, hev]; simpa using h1
  have e0 := mul_divByMonic_eq_iff_isRoot.2 hP0
  have hP1' : (P /ₘ (X - C 0)).IsRoot 1 := by
    have := hP1
    rw [← e0, IsRoot, eval_mul] at this
    simpa using this
  have e1 := mul_divByMonic_eq_iff_isRoot.2 hP1'
  set g := (P /ₘ (X - C 0)) /ₘ (X - C 1)
  have hfac : P = X * (X - C 1) * g := by
    rw [mul_assoc, e1]; simpa using e0.symm
  have hg : g = 0 := by
    by_contra hg
    have hdg : g.natDegree + 2 ≤ r := by
      have : P.natDegree = g.natDegree + 2 := by
        rw [hfac, natDegree_mul (mul_ne_zero X_ne_zero (X_sub_C_ne_zero 1)) hg,
          natDegree_mul X_ne_zero (X_sub_C_ne_zero 1), natDegree_X, natDegree_X_sub_C]
        ring
      omega
    have hgP : ∫ x in (0 : ℝ)..1, g.eval x * P.eval x = 0 := by
      have : (fun x => g.eval x * P.eval x) =
          fun x => ∑ i ∈ range (g.natDegree + 1), g.coeff i * (x ^ i * P.eval x) :=
        funext fun x => by rw [eval_eq_sum_range, sum_mul]; exact sum_congr rfl fun i _ => by ring
      rw [this, intervalIntegral.integral_finsetSum fun i _ =>
        (by have := P.continuous; fun_prop :
          Continuous fun x : ℝ => g.coeff i * (x ^ i * P.eval x)).intervalIntegrable _ _]
      refine sum_eq_zero fun i hi => ?_
      rw [intervalIntegral.integral_const_mul, integral_pow_mul_sum,
        h i (by simp only [mem_range] at hi; omega), mul_zero]
    refine hg (eq_zero_of_integral_mul_sq_eq_zero (w := X * (1 - X)) (fun x hx => ?_)
      (fun x hx => ?_) ?_)
    · simp only [eval_mul, eval_X, eval_sub, eval_one]
      exact mul_nonneg hx.1 (by linarith [hx.2])
    · simp only [eval_mul, eval_X, eval_sub, eval_one]
      exact mul_pos hx.1 (by linarith [hx.2])
    · have : (fun x => (X * (1 - X) : ℝ[X]).eval x * g.eval x ^ 2) =
          fun x => -(g.eval x * P.eval x) := funext fun x => by
        rw [hfac]; simp only [eval_mul, eval_X, eval_sub, eval_one, eval_C]; ring
      rw [this, intervalIntegral.integral_neg, hgP, neg_zero]
  funext γ
  rw [← coeff_sum_C_mul_X_pow v γ]
  change P.coeff γ = 0
  rw [hfac, hg, mul_zero, coeff_zero]

/-- The one-dimensional degrees of freedom of `Q_r⁻Λ` evaluated on `x^γ`, in a direction where
the face is `c` (`none`: the interval `[0, 1]`; `some a`: the point `x = a`) and the form does
(`e = true`) or does not (`e = false`) contain `dx`:
* on a point `a`: the value `a^γ`;
* on the interval, with `dx` (`P_{r-1}Λ¹(I)`): the moments `∫₀¹ x^{γ + i} = 1/(γ + i + 1)`;
* on the interval, without `dx` (`P_rΛ⁰(I)`): the endpoint values `0^γ`, `1` (`i = 0, 1`) and
  the moments `1/(γ + i - 1)` against `x^{i-2}` (`i ≥ 2`). -/
def edgeDof : Option ℝ → Bool → ℕ → ℕ → ℝ
  | some a, _, _, γ => a ^ γ
  | none, true, i, γ => ((γ + i + 1 : ℕ) : ℝ)⁻¹
  | none, false, 0, γ => 0 ^ γ
  | none, false, 1, _ => 1
  | none, false, i + 2, γ => ((γ + i + 1 : ℕ) : ℝ)⁻¹

/-- **One-dimensional unisolvence**: the `n = b + 1 - [e]` degrees of freedom `edgeDof c e`
are unisolvent on the polynomials of degree `< n` (`b ≥ 1` on the interval, `b = 0` on a
point). -/
theorem edgeDof_injective (c : Option ℝ) (e : Bool) {b n : ℕ} (hb : c = none → 1 ≤ b)
    (hc : c ≠ none → b = 0) (hn : n = b + 1 - if e then 1 else 0) :
    Function.Injective (Matrix.of fun i γ : Fin n => edgeDof c e i γ).mulVec := by
  intro v w hvw
  rw [← sub_eq_zero]
  have h0 : (Matrix.of fun i γ : Fin n => edgeDof c e i γ).mulVec (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  generalize v - w = u at h0
  have hrow : ∀ i : Fin n, ∑ γ : Fin n, u γ * edgeDof c e i γ = 0 := fun i => by
    have := congrFun h0 i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [← this]; exact sum_congr rfl fun γ _ => mul_comm _ _
  cases c with
  | some a =>
    rw [hc (Option.some_ne_none a)] at hn
    cases e
    · simp only [Bool.false_eq_true, ↓reduceIte, zero_add, tsub_zero] at hn
      subst hn
      funext γ
      have := hrow 0
      simp only [edgeDof, Fin.sum_univ_one] at this
      rw [Fin.fin_one_eq_zero γ, Pi.zero_apply]
      simpa using this
    · simp only [↓reduceIte, zero_add, tsub_self] at hn
      subst hn
      exact funext fun γ => γ.elim0
  | none =>
    have hr := hb rfl
    cases e
    · simp only [Bool.false_eq_true, ↓reduceIte, tsub_zero] at hn
      subst hn
      refine eq_zero_of_endpoints_moments_eq_zero ?_ ?_ fun i hi => ?_
      · simpa [edgeDof] using hrow ⟨0, by omega⟩
      · simpa [edgeDof] using hrow ⟨1, by omega⟩
      · simpa [edgeDof] using hrow ⟨i + 2, by omega⟩
    · simp only [↓reduceIte, add_tsub_cancel_right] at hn
      subst hn
      exact eq_zero_of_moments_eq_zero fun i => by simpa [edgeDof] using hrow i

end OneDim

/-! ### Tensor products of unisolvent families -/

/-- **Unisolvence of tensor products**: if the square matrices `Mⱼ` are invertible, so is their
Kronecker product `(∏ⱼ Mⱼ(aⱼ, γⱼ))_{a, γ}` (its inverse is the Kronecker product of the
inverses). -/
theorem eq_zero_of_kronecker {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] {n : ι → ℕ}
    (M : ∀ j, Fin (n j) → Fin (n j) → K) (hM : ∀ j, Function.Injective (Matrix.of (M j)).mulVec)
    {q : (∀ j, Fin (n j)) → K} (h : ∀ a : ∀ j, Fin (n j), ∑ γ, (∏ j, M j (a j) (γ j)) * q γ = 0) :
    q = 0 := by
  let L : ∀ j, Fin (n j) → Fin (n j) → K := fun j x a => (Matrix.of (M j))⁻¹ x a
  have hδ : ∀ j (x y : Fin (n j)), (if x = y then (1 : K) else 0) = ∑ a, L j x a * M j a y :=
    fun j x y => by
      have := congrFun (congrFun (Matrix.nonsing_inv_mul (Matrix.of (M j))
        ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_injective_iff_isUnit.1 (hM j))))
          x) y
      simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply] at this
      exact this.symm
  funext c
  calc q c = ∑ γ, (∏ j, if c j = γ j then (1 : K) else 0) * q γ := by
        simp only [Fintype.prod_boole, ← funext_iff, ite_mul, one_mul, zero_mul, sum_ite_eq,
          mem_univ, ↓reduceIte]
    _ = ∑ γ, ∑ a : ∀ j, Fin (n j),
          (∏ j, L j (c j) (a j)) * ((∏ j, M j (a j) (γ j)) * q γ) := by
        refine sum_congr rfl fun γ _ => ?_
        rw [prod_congr rfl fun j _ => hδ j (c j) (γ j), Fintype.prod_sum, sum_mul]
        exact sum_congr rfl fun a _ => by rw [prod_mul_distrib, mul_assoc]
    _ = 0 := by
        rw [sum_comm]
        exact sum_eq_zero fun a _ => by rw [← mul_sum, h a, mul_zero]

/-! ### Moments on the faces of the cube -/

section Moments

open MvPolynomial Koszul ExteriorFibre

variable {d : Type*} [Fintype d]

/-- The integral `∫_{[0,1]^d}` of polynomials: `x^γ ↦ ∏ⱼ 1/(γⱼ + 1)`. -/
def unitIntegral : MvPolynomial d ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials d ℝ).constr ℝ fun γ => ∏ j, ((γ j + 1 : ℕ) : ℝ)⁻¹

theorem unitIntegral_monomial (γ : d →₀ ℕ) (c : ℝ) :
    unitIntegral (monomial γ c) = c * ∏ j, ((γ j + 1 : ℕ) : ℝ)⁻¹ := by
  rw [show monomial γ c = c • (basisMonomials d ℝ) γ by simp [smul_monomial], map_smul,
    unitIntegral, Module.Basis.constr_basis, smul_eq_mul]

/-- **`unitIntegral` is the integral over the unit cube** `[0, 1]^d`. -/
theorem unitIntegral_eq_integral (p : MvPolynomial d ℝ) :
    unitIntegral p = ∫ x in Set.univ.pi fun _ : d => Set.Icc (0 : ℝ) 1, eval x p := by
  induction p using MvPolynomial.induction_on' with
  | monomial γ c =>
    rw [unitIntegral_monomial]
    simp only [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.volume_pi,
      MeasureTheory.Measure.restrict_pi_pi,
      MeasureTheory.integral_fintype_prod_eq_prod (fun j (y : ℝ) => y ^ γ j)]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_pow]
    push_cast
    simp
  | add p q hp hq =>
    have hint : ∀ r : MvPolynomial d ℝ,
        MeasureTheory.IntegrableOn (fun x => eval x r)
          (Set.univ.pi fun _ : d => Set.Icc (0 : ℝ) 1) :=
      fun r => (MvPolynomial.continuous_eval (p := r)).continuousOn.integrableOn_compact
        (isCompact_univ_pi fun _ => isCompact_Icc)
    rw [map_add, hp, hq, ← MeasureTheory.integral_add (hint p) (hint q)]
    simp

variable [LinearOrder d]

/-- The free directions `{j : g j = none}` of a coordinate plane `g`. -/
def freeSet (g : d → Option ℝ) : Finset d := {j | (g j).isNone}

omit [LinearOrder d] in
@[simp] theorem mem_freeSet {g : d → Option ℝ} {j : d} : j ∈ freeSet g ↔ (g j).isNone := by
  simp [freeSet]

/-- The moment `ω ↦ ∫_g tr_g ω ∧ η` on the plane `g`: the integral over `[0, 1]^d` of the top
coefficient `(tr_g ω ∧ η)_G` along the free directions `G` (for `η` a form on `g`, this is the
integral over the face `g ∩ [0, 1]^d`). -/
def cubeMoment (g : d → Option ℝ) (η : PolyForm ℝ d) : PolyForm ℝ d →ₗ[ℝ] ℝ where
  toFun ω := unitIntegral (wedgeForm (cubeTrace g ω) η (freeSet g))
  map_add' ω ω' := by rw [cubeTrace_add, wedgeForm_add_left, Pi.add_apply, map_add]
  map_smul' c ω := by
    rw [cubeTrace_smul, show c • cubeTrace g ω = (C c : MvPolynomial d ℝ) • cubeTrace g ω by
      funext s; simp [smul_eq_C_mul], wedgeForm_smul_left, Pi.smul_apply, smul_eq_mul,
      ← smul_eq_C_mul, map_smul, RingHom.id_apply]

/-- The face of the degree of freedom `(s, α)` on the face `f`: in a free direction `j ∉ s` of `f`
with `α_j ∈ {0, 1}`, the endpoint `x_j = α_j`; otherwise as `f`. -/
def dofFace (f : d → Option ℝ) (s : Finset d) (α : d →₀ ℕ) : d → Option ℝ := fun j =>
  (f j).or (if j ∈ s ∨ 2 ≤ α j then none else some (α j : ℝ))

/-- The exponent `β` of the test form `x^β dx_{G ∖ s}` of the degree of freedom `(s, α)`:
`β_j = α_j` for `j ∈ s`, `α_j - 2` otherwise. -/
def dofTest (s : Finset d) (α : d →₀ ℕ) : d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => if j ∈ s then α j else α j - 2

/-- The moment of index `(s, α)` on the face `f`: `ω ↦ ∫_g tr_g ω ∧ x^β dx_{G ∖ s}` on the face
`g = dofFace f s α ⊆ f` (free directions `G`, `β = dofTest s α`). -/
def momentDof (f : d → Option ℝ) (s : Finset d) (α : d →₀ ℕ) : PolyForm ℝ d →ₗ[ℝ] ℝ :=
  cubeMoment (dofFace f s α)
    (Pi.single (freeSet (dofFace f s α) \ s) (monomial (dofTest s α) 1))

/-- The indices `(s, α)` of the monomial basis `x^α dx_s` of `Q_b⁻Λᵏ`. -/
abbrev CubeDofIdx (b : d → ℕ) (k : ℕ) := Σ s : {s : Finset d // #s = k}, cubeSupport b s.1

/-- **The degrees of freedom of `Q_b⁻Λᵏ(f)`** ([ArnoldBoffiBonizzoni2015], §3), indexed like
the monomial basis: the moments `ω ↦ ∫_g tr_g ω ∧ x^β dx_{G ∖ s}` on the faces
`g = dofFace f s α ⊆ f`. On each face `g` of dimension `m ≥ k` the test forms are monomials of
`Q_{b-1}⁻Λ^{m-k}(g)` (`dofTest_mem_cubeFormMinus`). -/
abbrev cubeDof (f : d → Option ℝ) {b : d → ℕ} {k : ℕ} (i : CubeDofIdx b k) :
    PolyForm ℝ d →ₗ[ℝ] ℝ :=
  momentDof f i.1.1 i.2.1

/-- `b` is a degree on the face `f`: `b_j ≥ 1` in the free directions and `b_j = 0` in the fixed
ones (`Q_b⁻Λᵏ` is then the space of the face). -/
structure IsFaceDeg (f : d → Option ℝ) (b : d → ℕ) : Prop where
  one_le : ∀ j, f j = none → 1 ≤ b j
  eq_zero : ∀ j, f j ≠ none → b j = 0

omit [LinearOrder d] [Fintype d] in
theorem isFaceDeg_none {b : d → ℕ} (hb : ∀ j, 1 ≤ b j) : IsFaceDeg (fun _ => none) b :=
  ⟨fun j _ => hb j, fun _ h => absurd rfl h⟩

omit [LinearOrder d] [Fintype d] in
theorem isFaceDeg_faceDeg {b : d → ℕ} (hb : ∀ j, 1 ≤ b j) (f : d → Option ℝ) :
    IsFaceDeg f (faceDeg b f) :=
  ⟨fun j h => by simp [faceDeg, h, hb j],
    fun j h => by simp [faceDeg, Option.isNone_iff_eq_none, h]⟩

/-- The tensor product `⊗ⱼ edgeDof` of the one-dimensional degrees of freedom. -/
def tensorDof (f : d → Option ℝ) (s : Finset d) (α : d →₀ ℕ) : MvPolynomial d ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials d ℝ).constr ℝ fun γ => ∏ j, edgeDof (f j) (decide (j ∈ s)) (α j) (γ j)

theorem tensorDof_monomial (f : d → Option ℝ) (s : Finset d) (α γ : d →₀ ℕ) (c : ℝ) :
    tensorDof f s α (monomial γ c) = c * ∏ j, edgeDof (f j) (decide (j ∈ s)) (α j) (γ j) := by
  rw [show monomial γ c = c • (basisMonomials d ℝ) γ by simp [smul_monomial], map_smul,
    tensorDof, Module.Basis.constr_basis, smul_eq_mul]

variable {b : d → ℕ} {f : d → Option ℝ} {k : ℕ} {s : Finset d} {α : d →₀ ℕ}

omit [Fintype d] in
/-- The directions of `dx_s` are free directions of the face of `(s, α)`. -/
theorem dofFace_eq_none (hf : ∀ j, f j ≠ none → b j = 0) (hα : α ∈ cubeSupport b s) {j : d}
    (hj : j ∈ s) : dofFace f s α j = none := by
  have := hα j
  simp only [hj, ↓reduceIte] at this
  have hfj : f j = none := by
    by_contra h
    rw [hf j h] at this
    omega
  simp [dofFace, hfj, hj]

theorem subset_freeSet (hf : ∀ j, f j ≠ none → b j = 0) (hα : α ∈ cubeSupport b s) :
    s ⊆ freeSet (dofFace f s α) :=
  fun j hj => by simp [dofFace_eq_none hf hα hj]

/-- The test form `x^β dx_{G ∖ s}` of the degree of freedom `(s, α)` of `Q_b⁻Λᵏ(f)` is a
monomial of `Q_{b-1}⁻Λ^{m-k}(g)` on its face `g` (`m = #G` the dimension of `g`). -/
theorem dofTest_mem_cubeFormMinus (hf : ∀ j, f j ≠ none → b j = 0) (hα : α ∈ cubeSupport b s)
    (hs : #s = k) :
    (Pi.single (freeSet (dofFace f s α) \ s) (monomial (dofTest s α) 1) : PolyForm ℝ d) ∈
      cubeFormMinus ℝ (faceDeg (fun j => b j - 1) (dofFace f s α))
        (#(freeSet (dofFace f s α)) - k) := by
  refine ⟨fun t ht => Pi.single_eq_of_ne (fun h => ht ?_) _, fun t => ?_⟩
  · rw [h, card_sdiff_of_subset (subset_freeSet hf hα), hs]
  · by_cases ht : t = freeSet (dofFace f s α) \ s
    · subst ht
      rw [Pi.single_eq_same]
      refine (monomial_mem_restrictSupport ℝ).2 (Or.inl fun j => ?_)
      have := hα j
      simp only [dofTest, Finsupp.coe_equivFunOnFinite_symm, faceDeg, mem_sdiff,
        mem_freeSet] at this ⊢
      simp only [dofFace] at this ⊢
      by_cases hfj : f j = none
      · by_cases hjs : j ∈ s
        · simp only [hfj, hjs, ↓reduceIte, Option.isNone_none, Option.none_or, true_or,
            not_true_eq_false, and_false, add_zero] at this ⊢
          omega
        · simp only [hfj, hjs, ↓reduceIte, add_zero, false_or,
            Option.none_or, not_false_eq_true, and_true] at this ⊢
          by_cases h2 : 2 ≤ α j <;> simp [h2] <;> omega
      · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hfj
        have h0 := hf j hfj
        have hjs : j ∉ s := fun h => by simp [h, h0] at this
        simp_all
    · rw [Pi.single_eq_of_ne ht]; exact Submodule.zero_mem _

/-- On the face of `(s, α)` against `x^β`, the moment of a coefficient is the tensor product
of the one-dimensional degrees of freedom. -/
theorem unitIntegral_faceSubst_mul (hf : ∀ j, f j ≠ none → b j = 0) (hα : α ∈ cubeSupport b s)
    (p : MvPolynomial d ℝ) :
    unitIntegral (faceSubst (dofFace f s α) p * monomial (dofTest s α) 1) = tensorDof f s α p := by
  have : unitIntegral ∘ₗ LinearMap.mulRight ℝ (monomial (dofTest s α) (1 : ℝ)) ∘ₗ
      faceSubst (dofFace f s α) = tensorDof f s α :=
    (basisMonomials d ℝ).ext fun γ => by
      simp only [coe_basisMonomials, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.mulRight_apply, faceSubst_monomial, one_mul, monomial_mul_monomial, mul_one,
        unitIntegral_monomial, tensorDof_monomial, faceWeight, ← prod_mul_distrib]
      refine prod_congr rfl fun j _ => ?_
      have hαj := hα j
      simp only [dofFace, dofTest, Finsupp.coe_add, Pi.add_apply,
        Finsupp.coe_equivFunOnFinite_symm] at hαj ⊢
      cases hfj : f j with
      | some c =>
        rw [hf j (by simp [hfj])] at hαj
        have hjs : j ∉ s := fun h => by simp [h] at hαj
        simp [hjs, show α j = 0 by simp only [hjs, ↓reduceIte] at hαj; omega, edgeDof]
      | none =>
        by_cases hjs : j ∈ s
        · simp [hjs, hfj, edgeDof]
        · rcases h : α j with _ | _ | i
          · simp [hjs, h, edgeDof]
          · simp [hjs, h, edgeDof]
          · simp [hjs, h, hfj, edgeDof]
  exact LinearMap.congr_fun this p

/-- **The degrees of freedom are tensor products of one-dimensional ones**:
`ℓ_{s,α}(ω) = ±(⊗ⱼ edgeDof)(ω_s)`. -/
theorem momentDof_apply (hf : ∀ j, f j ≠ none → b j = 0) (hα : α ∈ cubeSupport b s)
    (ω : PolyForm ℝ d) :
    momentDof f s α ω =
      shuffleSgn s (freeSet (dofFace f s α) \ s) * tensorDof f s α (ω s) := by
  have hsub := subset_freeSet hf hα
  simp only [momentDof, cubeMoment, LinearMap.coe_mk, AddHom.coe_mk]
  rw [wedgeForm_apply, sum_eq_single s (fun u hu hus => by
      rw [Pi.single_eq_of_ne (fun h => hus ?_), mul_zero]
      rw [← Finset.sdiff_sdiff_eq_self (mem_powerset.1 hu), h, Finset.sdiff_sdiff_eq_self hsub])
    (fun h => absurd (mem_powerset.2 hsub) h), Pi.single_eq_same, cubeTrace,
    ite_eq_left fun j hj => by simpa using hsub hj, shuffleSgn_eq_C, mul_assoc,
    ← smul_eq_C_mul, map_smul, unitIntegral_faceSubst_mul hf hα, smul_eq_mul]

end Moments

/-! ### Unisolvence -/

section Unisolvence

open MvPolynomial Koszul ExteriorFibre

variable {d : Type*} [LinearOrder d] [Fintype d] {b : d → ℕ} {f : d → Option ℝ} {k : ℕ}
  {s : Finset d}

/-- A polynomial supported on `cubeSupport b s` is the sum of its monomials. -/
theorem sum_monomial_coeff {R : Type*} [CommRing R] {b : d → ℕ} {p : MvPolynomial d R}
    (hp : p ∈ restrictSupport R (cubeSupport b s)) :
    ∑ γ : cubeSupport b s, monomial γ.1 (p.coeff γ.1) = p := by
  classical
  ext m
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases hm : m ∈ cubeSupport b s
  · rw [Fintype.sum_eq_single ⟨m, hm⟩ fun γ hγ => ite_eq_right fun h => hγ (Subtype.ext h)]
    simp
  · rw [sum_eq_zero fun γ _ => ?_]
    · exact (notMem_support_iff.1 fun h => hm (hp h)).symm
    · refine ite_eq_right fun h => hm ?_
      rw [← h]; exact γ.2

/-- **Unisolvence on a coefficient**: a polynomial supported on `cubeSupport b s` on which all
the tensor-product degrees of freedom of the face `f` vanish is zero. -/
theorem eq_zero_of_tensorDof_eq_zero (hfb : IsFaceDeg f b) {p : MvPolynomial d ℝ}
    (hp : p ∈ restrictSupport ℝ (cubeSupport b s))
    (h : ∀ α ∈ cubeSupport b s, tensorDof f s α p = 0) : p = 0 := by
  set e := cubeSupportEquiv b s
  have hq : (fun c => p.coeff (e.symm c).1) = 0 := by
    refine eq_zero_of_kronecker (fun j a c => edgeDof (f j) (decide (j ∈ s)) a c)
      (fun j => edgeDof_injective (f j) _ (hfb.one_le j) (hfb.eq_zero j) (by simp))
      fun a => ?_
    have := h _ (e.symm a).2
    rw [← sum_monomial_coeff hp, map_sum] at this
    rw [← this, ← e.symm.sum_comp]
    refine sum_congr rfl fun c _ => ?_
    rw [tensorDof_monomial, mul_comm]
    rfl
  rw [← sum_monomial_coeff hp]
  refine sum_eq_zero fun γ _ => ?_
  have := congrFun hq (e γ)
  simp only [Equiv.symm_apply_apply, Pi.zero_apply] at this
  rw [this, monomial_zero]

/-- **The degrees of freedom of `Q_b⁻Λᵏ(f)` vanish only on `0`**. [ArnoldBoffiBonizzoni2015], §3 -/
theorem eq_zero_of_cubeDof_eq_zero (hfb : IsFaceDeg f b) {ω : PolyForm ℝ d}
    (hω : ω ∈ cubeFormMinus ℝ b k) (h : ∀ i : CubeDofIdx b k, cubeDof f i ω = 0) : ω = 0 := by
  funext s
  by_cases hs : #s = k
  · refine eq_zero_of_tensorDof_eq_zero hfb (hω.2 s) fun α hα => ?_
    have := h ⟨⟨s, hs⟩, ⟨α, hα⟩⟩
    rw [cubeDof, momentDof_apply hfb.eq_zero hα] at this
    exact (mul_eq_zero.1 this).resolve_left fun h0 => by
      simpa [h0] using shuffleSgn_mul_self (R := ℝ) s (freeSet (dofFace f s α) \ s)
  · exact hω.1 s hs

theorem card_cubeDofIdx (b : d → ℕ) (k : ℕ) :
    Fintype.card (CubeDofIdx b k) = Module.finrank ℝ (cubeFormMinus ℝ b k) := by
  rw [finrank_cubeFormMinus, Fintype.card_sigma]
  simp_rw [Fintype.card_congr (cubeSupportEquiv _ _), Fintype.card_pi, Fintype.card_fin]
  exact (Finset.sum_subtype (powersetCard k univ) (p := fun s => #s = k)
    (fun s => by simp [mem_powersetCard])
    (fun s => ∏ j, (b j + 1 - if j ∈ s then 1 else 0))).symm

/-- **Unisolvence of the degrees of freedom of `Q_b⁻Λᵏ(f)`**, for every face `f` of the cube and
every degree `b` on `f` (`b_j ≥ 1` free, `b_j = 0` fixed), in any dimension and form degree: in
particular `Q_r⁻Λᵏ` (`r ≥ 1`) on the cube (`isFaceDeg_none`) and on each of its faces
(`isFaceDeg_faceDeg`). [ArnoldBoffiBonizzoni2015], §3 -/
theorem isUnisolvent_cubeDof (hfb : IsFaceDeg f b) (k : ℕ) :
    IsUnisolvent fun i : CubeDofIdx b k => cubeDof f i ∘ₗ (cubeFormMinus ℝ b k).subtype := by
  rw [isUnisolvent_iff_forall_eq_zero _ (card_cubeDofIdx b k).symm]
  exact fun ω h => Subtype.ext (eq_zero_of_cubeDof_eq_zero hfb ω.2 h)

/-- The moments on the faces of `f` only see the trace on `f`. -/
theorem momentDof_cubeTrace (f : d → Option ℝ) (s : Finset d) (α : d →₀ ℕ) (ω : PolyForm ℝ d) :
    momentDof f s α (cubeTrace f ω) = momentDof f s α ω := by
  simp only [momentDof, cubeMoment, LinearMap.coe_mk, AddHom.coe_mk, cubeTrace_cubeTrace]
  congr 3
  funext j
  simp only [dofFace]
  cases f j <;> rfl

/-- **Trace determination**: the degrees of freedom of the faces of `f` determine the trace of
`ω ∈ Q_b⁻Λᵏ` on `f` (`b ≥ 1`). [ArnoldBoffiBonizzoni2015], §3 -/
theorem cubeTrace_eq_zero_of_cubeDof_eq_zero (hb : ∀ j, 1 ≤ b j) {ω : PolyForm ℝ d}
    (hω : ω ∈ cubeFormMinus ℝ b k) (h : ∀ i : CubeDofIdx (faceDeg b f) k, cubeDof f i ω = 0) :
    cubeTrace f ω = 0 :=
  eq_zero_of_cubeDof_eq_zero (isFaceDeg_faceDeg hb f) (cubeTrace_mem hω f) fun i => by
    rw [cubeDof, momentDof_cubeTrace, h]

end Unisolvence

/-! ### The commuting property -/

section Commuting

open MvPolynomial Koszul ExteriorFibre

/-- **One-dimensional integration by parts**: `∫₀¹ xⁱ p' = p(1) - 0ⁱ p(0) - i ∫₀¹ x^{i-1} p`, on
`p = x^γ`, in terms of the degrees of freedom. -/
theorem edgeDof_pderiv (i γ : ℕ) :
    (γ : ℝ) * edgeDof none true i (γ - 1) = edgeDof none false 1 γ -
      0 ^ i * edgeDof none false 0 γ - i * edgeDof none false (i + 1) γ := by
  rcases γ with _ | g <;> rcases i with _ | i
  · simp [edgeDof]
  · simp only [edgeDof]
    push_cast
    field_simp
    ring
  · simp [edgeDof]
    field_simp
  · simp only [edgeDof, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

variable {d : Type*} [LinearOrder d] [Fintype d] {f : d → Option ℝ} {b : d → ℕ} {k : ℕ}

/-- The degrees of freedom composed with `∂ⱼ` (`j ∈ s` free): the tensor product of the
integration by parts in the direction `j` with the identity in the others. -/
theorem tensorDof_pderiv {s : Finset d} {α : d →₀ ℕ} {j : d} (hj : j ∈ s) (hf : f j = none)
    (p : MvPolynomial d ℝ) :
    tensorDof f s α (pderiv j p) = tensorDof f (s.erase j) (α.update j 1) p -
      0 ^ α j * tensorDof f (s.erase j) (α.update j 0) p -
        (α j : ℝ) * tensorDof f (s.erase j) (α.update j (α j + 1)) p := by
  have : tensorDof f s α ∘ₗ (pderiv j).toLinearMap = tensorDof f (s.erase j) (α.update j 1) -
      (0 : ℝ) ^ α j • tensorDof f (s.erase j) (α.update j 0) -
        (α j : ℝ) • tensorDof f (s.erase j) (α.update j (α j + 1)) :=
    (basisMonomials d ℝ).ext fun γ => by
      simp only [coe_basisMonomials, LinearMap.coe_comp, Function.comp_apply,
        Derivation.coeFn_coe, pderiv_monomial, one_mul, tensorDof_monomial, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j,
        Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j]
      set P := ∏ l ∈ {j}ᶜ, edgeDof (f l) (decide (l ∈ s)) (α l) (γ l)
      have hlhs : ∏ l ∈ {j}ᶜ, edgeDof (f l) (decide (l ∈ s)) (α l)
          ((γ - Finsupp.single j 1 : d →₀ ℕ) l) = P :=
        prod_congr rfl fun l hl => by
          have hlj : l ≠ j := by simpa using hl
          simp [Ne.symm hlj]
      have hrest : ∀ v, ∏ l ∈ {j}ᶜ, edgeDof (f l) (decide (l ∈ s.erase j)) ((α.update j v) l)
          (γ l) = P := fun v =>
        prod_congr rfl fun l hl => by
          have hlj : l ≠ j := by simpa using hl
          simp [Finsupp.update_apply, hlj]
      rw [hlhs, hrest, hrest, hrest]
      simp only [Finsupp.update_apply, ite_true, hf, hj, decide_true, mem_erase, ne_eq,
        not_true_eq_false, false_and, decide_false, Finsupp.coe_tsub, Pi.sub_apply,
        Finsupp.single_eq_same]
      have := edgeDof_pderiv (α j) (γ j)
      linear_combination P * this
  exact LinearMap.congr_fun this p

/-- **Stokes compatibility**: each degree of freedom of `Q_b⁻Λ^{k+1}(f)` composed with `d` is a
linear combination of degrees of freedom of `Q_b⁻Λᵏ(f)`. -/
theorem cubeDof_extDeriv_mem_span (hf : ∀ j, f j ≠ none → b j = 0)
    (i : CubeDofIdx b (k + 1)) :
    cubeDof f i ∘ₗ extDerivₗ ℝ d ∈
      Submodule.span ℝ (Set.range fun i' : CubeDofIdx b k => cubeDof f i') := by
  obtain ⟨⟨s, hs⟩, ⟨α, hα⟩⟩ := i
  set ε := (shuffleSgn s (freeSet (dofFace f s α) \ s) : ℝ)
  -- the degrees of freedom of the faces of `(s, α)` that appear
  have hmem : ∀ j ∈ s, ∀ v ≤ α j + 1, α.update j v ∈ cubeSupport b (s.erase j) :=
    fun _ hj _ hv => update_mem_cubeSupport_erase hα hj hv
  have hcard : ∀ j ∈ s, #(s.erase j) = k := fun j hj => by rw [card_erase_of_mem hj, hs]; rfl
  let D : ∀ j ∈ s, ∀ v ≤ α j + 1, PolyForm ℝ d →ₗ[ℝ] ℝ := fun j hj v hv =>
    (shuffleSgn (s.erase j) (freeSet (dofFace f (s.erase j) (α.update j v)) \ s.erase j) : ℝ) •
      cubeDof f (⟨⟨s.erase j, hcard j hj⟩, ⟨α.update j v, hmem j hj v hv⟩⟩ : CubeDofIdx b k)
  have hD : ∀ j hj v hv (ω : PolyForm ℝ d),
      D j hj v hv ω = tensorDof f (s.erase j) (α.update j v) (ω (s.erase j)) :=
    fun j hj v hv ω => by
      simp only [D, LinearMap.smul_apply, cubeDof, momentDof_apply hf (hmem j hj v hv),
        smul_eq_mul, ← mul_assoc, shuffleSgn_mul_self, one_mul]
  have hfs : ∀ j ∈ s, f j = none := fun j hj => by
    have := hα j
    simp only [hj, ↓reduceIte] at this
    by_contra h
    rw [hf j h] at this
    omega
  have key : cubeDof f (⟨⟨s, hs⟩, ⟨α, hα⟩⟩ : CubeDofIdx b (k + 1)) ∘ₗ extDerivₗ ℝ d =
      ∑ j ∈ s.attach, (ε * sgn j.1 s) • (D j.1 j.2 1 (by omega) -
        (0 : ℝ) ^ α j.1 • D j.1 j.2 0 (by omega) - (α j.1 : ℝ) • D j.1 j.2 (α j.1 + 1) le_rfl) := by
    refine LinearMap.ext fun ω => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, extDerivₗ_apply, cubeDof,
      momentDof_apply hf hα, extDeriv_apply, map_sum, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.sub_apply, hD, smul_eq_mul, mul_sum]
    rw [← sum_attach s]
    refine sum_congr rfl fun j _ => ?_
    rw [map_sgn_mul, tensorDof_pderiv j.2 (hfs j.1 j.2)]
    ring
  rw [key]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.sub_mem _
    (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_)) <;>
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

variable (f b k) in
/-- **The canonical interpolant** `Π : PolyForm → Q_b⁻Λᵏ(f)`, `ℓ_i(Π ω) = ℓ_i(ω)`. -/
def cubeInterp (hfb : IsFaceDeg f b) : PolyForm ℝ d →ₗ[ℝ] cubeFormMinus ℝ b k :=
  interp (isUnisolvent_cubeDof hfb k) fun i => cubeDof f i

theorem cubeDof_cubeInterp (hfb : IsFaceDeg f b) (ω : PolyForm ℝ d) (i : CubeDofIdx b k) :
    cubeDof f i (cubeInterp f b k hfb ω) = cubeDof f i ω :=
  dof_interp (isUnisolvent_cubeDof hfb k) (fun i => cubeDof f i) ω i

/-- `Π` is a projection onto `Q_b⁻Λᵏ(f)`. -/
theorem cubeInterp_of_mem (hfb : IsFaceDeg f b) {ω : PolyForm ℝ d}
    (hω : ω ∈ cubeFormMinus ℝ b k) : (cubeInterp f b k hfb ω : PolyForm ℝ d) = ω :=
  congrArg Subtype.val (interp_incl (isUnisolvent_cubeDof hfb k) (fun i => cubeDof f i)
    (cubeFormMinus ℝ b k).subtype (fun _ => rfl) ⟨ω, hω⟩)

/-- **The commuting property** `Π d = d Π` of the canonical interpolants of `Q_b⁻Λ(f)`.
[ArnoldBoffiBonizzoni2015], §3 -/
theorem cubeInterp_extDeriv (hfb : IsFaceDeg f b) (ω : PolyForm ℝ d) :
    (cubeInterp f b (k + 1) hfb (extDeriv ω) : PolyForm ℝ d) =
      extDeriv (cubeInterp f b k hfb ω : PolyForm ℝ d) :=
  congrArg Subtype.val (interp_comp_eq (isUnisolvent_cubeDof hfb k) (fun i => cubeDof f i)
    (isUnisolvent_cubeDof hfb (k + 1)) (fun i => cubeDof f i)
    (cubeFormMinus ℝ b k).subtype (cubeFormMinus ℝ b (k + 1)).subtype
    (fun _ => rfl) (fun _ => rfl) (extDerivₗ ℝ d)
    ((extDerivₗ ℝ d).restrict fun _ h => extDeriv_mem_cubeFormMinus h) rfl
    (cubeDof_extDeriv_mem_span hfb.eq_zero) ω)

end Commuting

end Feec.FiniteElement.Cube
