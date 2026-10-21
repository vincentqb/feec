module

public import Feec.FiniteElement.Whitney
public import Feec.Algebra.PolynomialFormDim
public import Feec.Algebra.Wedge
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# The local spaces `P_rΛᵏ(T)` and `P_r⁻Λᵏ(T)`

Let `T` be an `n`-simplex in `ℝⁿ` with vertices `p₀, …, pₙ` (affinely independent, e.g. the
points of a Mathlib `Affine.Simplex ℝ (Fin n → ℝ) n`) and `F_T(x̂) = p₀ + B x̂` its affine
parametrization by the reference simplex `T̂ₙ`. The shape functions of the two FEEC families
are the polynomial form fields

  `P_rΛᵏ(T) = (F_T⁻¹)^* P_rΛᵏ(ℝⁿ)`, `P_r⁻Λᵏ(T) = (F_T⁻¹)^* P_r⁻Λᵏ(ℝⁿ)`,

pullbacks of the algebraic spaces `Feec.Koszul.polyForm`, `Feec.Koszul.polyFormMinus`
(evaluated as form fields by `Feec.FiniteElement.evalForm`). The trace on a face `f = p ∘ e`
(`e : Fin (m + 1) → Fin (n + 1)` listing its vertices) is the pullback along its
parametrization `F_f : ℝᵐ → ℝⁿ`, and a form has vanishing trace on `∂T` (it is a *bubble*) when
its traces on all proper faces vanish ([AFW2006], §3–4; [AFW2010], §5.1–5.2; [Arnold2018], Ch. 7).

## Main definitions

* `Feec.FiniteElement.polySubst B b`, `polyPullback B b`: affine substitution in polynomials and
  the pullback of polynomial forms along `x̂ ↦ B x̂ + b`;
* `Feec.FiniteElement.polySpace n r k`, `polyMinusSpace n r k`: `P_rΛᵏ(ℝⁿ)`, `P_r⁻Λᵏ(ℝⁿ)` as
  spaces of form fields;
* `Feec.FiniteElement.localPolySpace p r k`, `localPolyMinusSpace p r k`: `P_rΛᵏ(T)`,
  `P_r⁻Λᵏ(T)`;
* `Feec.FiniteElement.faceTrace p e`: the trace on the face `p ∘ e`;
* `Feec.FiniteElement.IsBubble p ω`, `bubbleSpace p V`: vanishing trace on `∂T`, `V̊`;
* `Feec.FiniteElement.wedgeField ω η`: the pointwise exterior product.

## Main results

* fibre identities: `Feec.ExteriorFibre.pullback_interior` (`B^*(ι_{Bx} α) = ι_x B^* α`),
  `Feec.ExteriorFibre.pullback_wedgeForm` (`B^*(α ∧ β) = B^*α ∧ B^*β`),
  `Feec.ExteriorFibre.interior_wedgeProd` (contraction is an antiderivation);
* polynomial calculus: `partialDeriv_eval`, `extDeriv_evalForm` (`d` of an evaluated polynomial
  form), `evalForm_injective`, `evalForm_wedgeForm`;
* **affine invariance**: `polyPullback_mem_polyForm`, `polyPullback_mem_polyFormMinus`
  (`F^* P_rΛᵏ(ℝⁿ) ⊆ P_rΛᵏ(ℝᵐ)`, `F^* P_r⁻Λᵏ(ℝⁿ) ⊆ P_r⁻Λᵏ(ℝᵐ)` for every affine `F : ℝᵐ → ℝⁿ`,
  via `F^*(κω) = κ(F^*ω) + F^*(ι_b ω)`), hence `localPolySpace_eq`, `localPolyMinusSpace_eq`:
  `P_rΛᵏ(T) = P_rΛᵏ(ℝⁿ)` and `P_r⁻Λᵏ(T) = P_r⁻Λᵏ(ℝⁿ)` for every simplex;
* **traces**: `map_faceTrace_polySpace`, `map_faceTrace_polyMinusSpace`:
  `tr_f P_rΛᵏ(T) = P_rΛᵏ(f)`, `tr_f P_r⁻Λᵏ(T) = P_r⁻Λᵏ(f)` (the inclusion by affine invariance,
  the equality by the barycentric retraction of `T` onto `f`); traces are multiplicative
  (`faceTrace_wedgeField`) and commute with `d` (`faceTrace_extDeriv`);
* **bubbles** ([AFW2006], Lemmas 4.5–4.7, 4.11): `eq_zero_of_coordTrace_of_integral` (a form whose
  traces vanish on the faces through `0` and which is orthogonal to `P_{r+k-n}Λ^{n-k}` vanishes),
  `eq_zero_of_isBubble_of_mem_polyForm` (a bubble of `P_rΛᵏ` orthogonal to
  `P⁻_{r+k-n}Λ^{n-k}` vanishes), `eq_zero_of_isBubble_of_mem_polyFormMinus` (a bubble of
  `P_r⁻Λᵏ` orthogonal to `P_{r+k-n-1}Λ^{n-k}` vanishes), and `bubbleSpace_polySpace_eq_bot`,
  `bubbleSpace_polyMinusSpace_eq_bot` (no bubbles if `r + k ≤ n`); the dimensions of the bubble
  spaces are in `Feec.FiniteElement.LocalDof`;
* `integral_extDeriv_wedge_of_isBubble`: Stokes' theorem for a bubble,
  `∫_{T̂} dω ∧ μ = -(-1)^k ∫_{T̂} ω ∧ dμ`.

## Implementation notes

Form fields are defined on all of `ℝⁿ`, so the traces of polynomial forms are polynomial form
fields on all of `ℝᵐ`, and "vanishing trace" means that this polynomial form vanishes (for
polynomials, equivalently on the face). The orthogonality hypotheses use the integral
`∫_{T̂} (ω ∧ η)_{univ}` of the reference simplex (`Feec.FiniteElement.simplexIntegral`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3 (affine invariance), §4.5–4.6 (Lemmas 4.5–4.7, 4.11)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.1–5.2 (the spaces on simplices and their traces)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MeasureTheory

@[expose] public noncomputable section

namespace Feec.ExteriorFibre

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d] {ι : Type*} [LinearOrder ι]

/-! ### Fibre identities: ring homomorphisms, contractions and products -/

theorem map_wedge {S : Type*} [CommRing S] (φ : R →+* S) (ξ : d → R) (ω : Finset d → R)
    (s : Finset d) : φ (wedge ξ ω s) = wedge (φ ∘ ξ) (φ ∘ ω) s := by
  simp [wedge_apply, map_sum, sgn]

theorem map_wedgeProd {S : Type*} [CommRing S] (φ : R →+* S) (θ : ι → d → R) (s : Finset ι)
    (t : Finset d) : φ (wedgeProd θ s t) = wedgeProd (fun i => φ ∘ θ i) s t := by
  induction s using Finset.induction_on_min generalizing t with
  | empty => simp [Pi.single_apply, apply_ite φ]
  | insert a s ha ih =>
    rw [wedgeProd_insert_of_lt _ ha, wedgeProd_insert_of_lt _ ha, map_wedge]
    congr 1
    funext t'
    exact ih t'

theorem map_pullback {S : Type*} [CommRing S] [Fintype ι] {κ : Type*} [LinearOrder κ]
    (φ : R →+* S) (B : ι → κ → R) (α : Finset ι → R) (t : Finset κ) :
    φ (pullback B α t) = pullback (fun i => φ ∘ B i) (φ ∘ α) t := by
  simp only [pullback_apply, map_sum, map_mul, map_wedgeProd, Function.comp_apply]

theorem interior_sum [Fintype d] {β : Type*} (x : d → R) (u : Finset β) (ω : β → Finset d → R) :
    interior x (∑ b ∈ u, ω b) = ∑ b ∈ u, interior x (ω b) := by
  funext s; simp only [interior_apply, Finset.sum_apply, mul_sum]; exact sum_comm

/-- **Contraction is an antiderivation**: `ι_x (θ_{g₁} ∧ ⋯ ∧ θ_{g_k}) = W_g` with the scalars
`⟨θᵢ, x⟩`. -/
theorem interior_wedgeProd [Fintype d] (θ : ι → d → R) (x : d → R) (g : Finset ι) :
    interior x (wedgeProd θ g) = whitneyFibre (fun i => ∑ l, θ i l * x l) θ g := by
  induction g using Finset.induction_on_min with
  | empty =>
    funext s
    simp only [wedgeProd_empty, interior_apply, whitneyFibre, sum_empty, Pi.zero_apply]
    refine sum_eq_zero fun j hj => ?_
    have : insert j s ≠ ∅ := insert_ne_empty j s
    simp [this]
  | insert a g ha ih =>
    rw [wedgeProd_insert_of_lt _ ha, whitneyFibre_insert_of_lt _ _ ha, ← ih]
    have h := wedge_interior_add_interior_wedge (θ a) x (wedgeProd θ g)
    rw [eq_sub_of_add_eq' h]

/-- **Pullback commutes with contraction**: `B^*(ι_{Bx} α) = ι_x (B^* α)`. -/
theorem pullback_interior [Fintype ι] {κ : Type*} [LinearOrder κ] [Fintype κ]
    (B : ι → κ → R) (x : κ → R) (α : Finset ι → R) :
    pullback B (interior (fun i => ∑ l, B i l * x l) α) = interior x (pullback B α) := by
  rw [interior_eq_sum_single, pullback_sum, pullback]
  rw [interior_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [pullback_smul, interior_smul, ← whitneyFibre_single_eq_interior, pullback_whitneyFibre,
    interior_wedgeProd]
  congr 2
  funext a l
  simp [covPullback, Pi.single_apply]

/-- `B^*(θ_s^∧ ∧ β) = (Bᵀθ)_s^∧ ∧ B^* β`. -/
theorem pullback_wedgeForm_wedgeProd [Fintype ι] {κ : Type*} [LinearOrder κ] {μ : Type*}
    [LinearOrder μ] (B : ι → κ → R) (θ : μ → ι → R) (s : Finset μ) (β : Finset ι → R) :
    pullback B (wedgeForm (wedgeProd θ s) β) =
      wedgeForm (wedgeProd (fun j => covPullback B (θ j)) s) (pullback B β) := by
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a s ha ih =>
    rw [wedgeProd_insert_of_lt _ ha, wedgeProd_insert_of_lt _ ha, ← wedge_wedgeForm,
      pullback_wedge, ih, wedge_wedgeForm]

theorem eq_sum_smul_single [Fintype d] (α : Finset d → R) : α = ∑ s, α s • Pi.single s 1 := by
  funext t; simp [Finset.sum_apply, Pi.single_apply]

/-- **Pullback is multiplicative**: `B^*(α ∧ β) = B^*α ∧ B^*β`. -/
theorem pullback_wedgeForm [Fintype ι] {κ : Type*} [LinearOrder κ] (B : ι → κ → R)
    (α β : Finset ι → R) :
    pullback B (wedgeForm α β) = wedgeForm (pullback B α) (pullback B β) := by
  conv_lhs => rw [eq_sum_smul_single α]
  rw [wedgeForm_sum_left, pullback_sum, pullback, wedgeForm_sum_left]
  refine sum_congr rfl fun s _ => ?_
  rw [wedgeForm_smul_left, pullback_smul, wedgeForm_smul_left, ← wedgeProd_single s,
    pullback_wedgeForm_wedgeProd]
  congr 3
  funext j l
  simp [covPullback, Pi.single_apply]

end Feec.ExteriorFibre

namespace Feec.Koszul

open ExteriorFibre MvPolynomial

variable {K : Type*} [Field K] {d : Type*} [LinearOrder d] [Fintype d]

/-- `κ P_{r-1}Λ^{k+1} ⊆ P_r⁻Λᵏ` (the second form of the definition of `P_r⁻Λᵏ`, [AFW2010],
§5.1.3). -/
theorem koszul_mem_polyFormMinus {r k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ polyForm K d (r - 1) (k + 1)) :
    koszul ω ∈ polyFormMinus K d r k := by
  rw [← sum_homComp h, ← koszulₗ_apply, map_sum]
  refine Submodule.sum_mem _ fun j hj => ?_
  have hj' : j ≤ r - 1 := by simp at hj; omega
  have hm := homComp_mem_homForm h.1 j
  rcases Nat.lt_or_ge j (r - 1) with hlt | hge
  · refine Submodule.mem_sup_left (polyForm_mono (show j + 1 ≤ r - 1 by omega) k ?_)
    exact homForm_le_polyForm (j + 1) k (by simpa using koszul_mem_homForm hm)
  · have : j = r - 1 := le_antisymm hj' hge
    subst this
    exact Submodule.mem_sup_right ⟨_, hm, rfl⟩

omit [Fintype d] in
/-- Contraction with a constant vector: `ι_b : P_rΛ^{k+1} → P_rΛᵏ`. -/
theorem interior_C_mem_polyForm [Fintype d] (b : d → K) {r k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ polyForm K d r (k + 1)) : interior (fun j => C (b j)) ω ∈ polyForm K d r k := by
  refine ⟨(h.1).interior _, fun s => (totalDegree_finsetSum _ _).trans
    (Finset.sup_le fun j _ => (totalDegree_mul _ _).trans ?_)⟩
  have h0 : (sgn j s * C (b j) : MvPolynomial d K).totalDegree = 0 := by
    rw [show (sgn j s : MvPolynomial d K) = C (sgn j s) by simp [sgn], ← C_mul, totalDegree_C]
  rw [h0, zero_add]
  exact h.2 _

end Feec.Koszul

namespace Feec.FiniteElement

open ExteriorFibre MvPolynomial

variable {n m : ℕ}

/-! ### Polynomials as smooth functions -/

theorem contDiff_eval (p : MvPolynomial (Fin n) ℝ) {r : WithTop ℕ∞} :
    ContDiff ℝ r (fun x : Fin n → ℝ => eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (by fun_prop)

theorem differentiable_eval (p : MvPolynomial (Fin n) ℝ) :
    Differentiable ℝ (fun x : Fin n → ℝ => eval x p) :=
  (contDiff_eval p (r := 1)).differentiable one_ne_zero

/-- Partial derivatives of polynomial functions are the formal partial derivatives. -/
theorem partialDeriv_eval (p : MvPolynomial (Fin n) ℝ) (j : Fin n) (x : Fin n → ℝ) :
    partialDeriv j (fun y => eval y p) x = eval x (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add]
    rw [partialDeriv_add (differentiable_eval p x) (differentiable_eval q x), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    rw [partialDeriv_mul (differentiable_eval p x) (differentiable_apply i x), hp,
      partialDeriv_apply_coord, pderiv_mul, pderiv_X]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]

theorem contDiff_evalForm (ω : Koszul.PolyForm ℝ (Fin n)) {r : WithTop ℕ∞} :
    ContDiff ℝ r (evalForm n ω) :=
  contDiff_pi.2 fun s => contDiff_eval (ω s)

/-- `d` of an evaluated polynomial form is the evaluated formal exterior derivative. -/
theorem extDeriv_evalForm (ω : Koszul.PolyForm ℝ (Fin n)) :
    extDeriv (evalForm n ω) = evalForm n (Koszul.extDeriv ω) := by
  funext x s
  simp only [extDeriv_apply, evalForm_apply, Koszul.extDeriv_apply, map_sum, map_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [partialDeriv_eval]
  simp [sgn]

/-- Evaluation is injective on polynomial forms. -/
theorem evalForm_injective : Function.Injective (evalForm n) := by
  intro ω η h
  funext s
  exact MvPolynomial.funext fun x => congrFun (congrFun h x) s

/-- Evaluation commutes with the exterior product. -/
theorem evalForm_wedgeForm (ω η : Koszul.PolyForm ℝ (Fin n)) (x : Fin n → ℝ) :
    evalForm n (wedgeForm ω η) x = wedgeForm (evalForm n ω x) (evalForm n η x) := by
  funext u
  simp only [evalForm_apply, wedgeForm_apply, map_sum, map_mul]
  refine sum_congr rfl fun s _ => ?_
  simp [shuffleSgn, sgn, map_prod]

/-! ### Affine substitution in polynomials -/

/-- The affine substitution `p ↦ p ∘ F`, `F(x̂) = B x̂ + b`. -/
def polySubst (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) :
    MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin m) ℝ :=
  aeval fun i => ∑ l, C (B i l) * X l + C (b i)

theorem eval_polySubst (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ)
    (x : Fin m → ℝ) : eval x (polySubst B b p) = eval (affine B b x) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [polySubst]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, polySubst, aeval_X]
    simp [affine_apply]

theorem totalDegree_affineCoord_le (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n) :
    (∑ l, C (B i l) * X l + C (b i) : MvPolynomial (Fin m) ℝ).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_finsetSum _ _).trans
    (Finset.sup_le fun l _ => ?_)) (by simp))
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])

/-- Affine substitution does not raise the total degree. -/
theorem totalDegree_polySubst_le (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ)
    (p : MvPolynomial (Fin n) ℝ) : (polySubst B b p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun v hv => ?_)
  rw [polySubst, aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (totalDegree_affineCoord_le B b i))) ?_
  simp only [mul_one]
  exact le_totalDegree hv

/-! ### Affine pullback of polynomial forms -/

/-- The pullback of a polynomial form along `F(x̂) = B x̂ + b`, as a polynomial form. -/
def polyPullback (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (ω : Koszul.PolyForm ℝ (Fin n)) :
    Koszul.PolyForm ℝ (Fin m) :=
  ExteriorFibre.pullback (fun i l => C (B i l)) (fun s => polySubst B b (ω s))

theorem polyPullback_apply (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ)
    (ω : Koszul.PolyForm ℝ (Fin n)) (t : Finset (Fin m)) :
    polyPullback B b ω t = ∑ s, polySubst B b (ω s) * C (wedgeProd B s t) := by
  rw [polyPullback, pullback_apply]
  refine sum_congr rfl fun s _ => ?_
  rw [map_wedgeProd C B s t]
  rfl

/-- `F^*` of an evaluated polynomial form is the evaluated polynomial pullback. -/
theorem evalForm_polyPullback (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ)
    (ω : Koszul.PolyForm ℝ (Fin n)) :
    evalForm m (polyPullback B b ω) = affinePullback B b (evalForm n ω) := by
  funext x t
  rw [evalForm_apply, polyPullback_apply, affinePullback_apply, pullback_apply]
  simp only [map_sum, map_mul, eval_C, eval_polySubst, evalForm_apply]

theorem polyPullback_add (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ)
    (ω η : Koszul.PolyForm ℝ (Fin n)) :
    polyPullback B b (ω + η) = polyPullback B b ω + polyPullback B b η := by
  rw [polyPullback, polyPullback, polyPullback, ← pullback_add]
  congr 1; funext s; simp

/-- **`F^* P_rΛᵏ(ℝⁿ) ⊆ P_rΛᵏ(ℝᵐ)`** for every affine `F : ℝᵐ → ℝⁿ`. -/
theorem polyPullback_mem_polyForm (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) {r k : ℕ}
    {ω : Koszul.PolyForm ℝ (Fin n)} (h : ω ∈ Koszul.polyForm ℝ (Fin n) r k) :
    polyPullback B b ω ∈ Koszul.polyForm ℝ (Fin m) r k := by
  refine ⟨IsDeg.pullback (fun s hs => by simp [h.1 s hs]) _, fun t => ?_⟩
  rw [polyPullback_apply]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s _ => (totalDegree_mul _ _).trans ?_)
  rw [totalDegree_C, add_zero]
  exact (totalDegree_polySubst_le B b _).trans (h.2 s)

/-- The pullback of `κ ω` along `F(x̂) = B x̂ + b`: `F^*(κ ω) = κ (F^* ω) + F^*(ι_b ω)`. -/
theorem polyPullback_koszul (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ)
    (ω : Koszul.PolyForm ℝ (Fin n)) :
    polyPullback B b (Koszul.koszul ω) = Koszul.koszul (polyPullback B b ω) +
      polyPullback B b (interior (fun j => C (b j)) ω) := by
  have hsub : (fun s => polySubst B b (Koszul.koszul ω s)) =
      interior (fun j => ∑ l, C (B j l) * X l) (fun s => polySubst B b (ω s)) +
        interior (fun j => C (b j)) (fun s => polySubst B b (ω s)) := by
    rw [← interior_add_left]
    funext s
    simp only [Koszul.koszul_apply, interior_apply, map_sum, map_mul, Pi.add_apply]
    refine sum_congr rfl fun j _ => ?_
    simp [polySubst, sgn]
  have hsub2 : (fun s => polySubst B b (interior (fun j => C (b j)) ω s)) =
      interior (fun j => C (b j)) (fun s => polySubst B b (ω s)) := by
    funext s
    simp only [interior_apply, map_sum, map_mul]
    refine sum_congr rfl fun j _ => ?_
    simp [polySubst, sgn]
  rw [polyPullback, hsub, pullback_add, pullback_interior, polyPullback, polyPullback, hsub2]
  rfl

/-- **`F^* P_r⁻Λᵏ(ℝⁿ) ⊆ P_r⁻Λᵏ(ℝᵐ)`** for every affine `F : ℝᵐ → ℝⁿ` ([AFW2010], §5.1.3: the
trimmed spaces do not depend on the base point of `κ`). -/
theorem polyPullback_mem_polyFormMinus (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) {r k : ℕ}
    {ω : Koszul.PolyForm ℝ (Fin n)} (h : ω ∈ Koszul.polyFormMinus ℝ (Fin n) r k) :
    polyPullback B b ω ∈ Koszul.polyFormMinus ℝ (Fin m) r k := by
  obtain ⟨a, ha, c, ⟨c, hc, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
  rw [polyPullback_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left (polyPullback_mem_polyForm B b ha)) ?_
  change polyPullback B b (Koszul.koszul c) ∈ _
  rw [polyPullback_koszul]
  refine Submodule.add_mem _ (Koszul.koszul_mem_polyFormMinus
    (polyPullback_mem_polyForm B b (Koszul.homForm_le_polyForm _ _ hc))) ?_
  exact Submodule.mem_sup_left (polyPullback_mem_polyForm B b
    (Koszul.interior_C_mem_polyForm b (Koszul.homForm_le_polyForm _ _ hc)))

/-! ### The spaces `P_rΛᵏ(ℝⁿ)`, `P_r⁻Λᵏ(ℝⁿ)` of form fields -/

variable (n) in
/-- `P_rΛᵏ(ℝⁿ)` as a space of (smooth) form fields: the evaluated polynomial forms of
`Feec.Koszul.polyForm`. -/
def polySpace (r k : ℕ) : Submodule ℝ (FormField n) :=
  (Koszul.polyForm ℝ (Fin n) r k).map (evalForm n)

variable (n) in
/-- `P_r⁻Λᵏ(ℝⁿ)` as a space of form fields.

Warning: this is meaningful only for `1 ≤ r`. At `r = 0` the underlying
`Feec.Koszul.polyFormMinus` uses the truncated `r - 1 = 0`, so it is `P_0Λᵏ + κH_0Λ^{k+1}` rather
than the classical `P_0⁻Λᵏ = 0`; every result here about the trimmed family assumes `1 ≤ r`. -/
def polyMinusSpace (r k : ℕ) : Submodule ℝ (FormField n) :=
  (Koszul.polyFormMinus ℝ (Fin n) r k).map (evalForm n)

/-- The affine pullback as a linear map. -/
def affinePullbackₗ (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) : FormField n →ₗ[ℝ] FormField m where
  toFun := affinePullback B b
  map_add' := affinePullback_add B b
  map_smul' := affinePullback_smul B b

@[simp] theorem affinePullbackₗ_apply (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (ω : FormField n) :
    affinePullbackₗ B b ω = affinePullback B b ω := rfl

theorem affinePullback_mem_polySpace (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) {r k : ℕ}
    {ω : FormField n} (h : ω ∈ polySpace n r k) : affinePullback B b ω ∈ polySpace m r k := by
  obtain ⟨Ω, hΩ, rfl⟩ := h
  exact ⟨_, polyPullback_mem_polyForm B b hΩ, evalForm_polyPullback B b Ω⟩

theorem affinePullback_mem_polyMinusSpace (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) {r k : ℕ}
    {ω : FormField n} (h : ω ∈ polyMinusSpace n r k) :
    affinePullback B b ω ∈ polyMinusSpace m r k := by
  obtain ⟨Ω, hΩ, rfl⟩ := h
  exact ⟨_, polyPullback_mem_polyFormMinus B b hΩ, evalForm_polyPullback B b Ω⟩

theorem affinePullback_id (ω : FormField n) :
    affinePullback (fun i j => if i = j then (1 : ℝ) else 0) 0 ω = ω := by
  funext x
  have : affine (fun i j : Fin n => if i = j then (1 : ℝ) else 0) 0 x = x := by
    funext i; simp [affine_apply]
  rw [affinePullback_apply, this, pullback_id]

/-- If `G ∘ F = id` for affine maps, then `F^* ∘ G^* = id`. -/
theorem affinePullback_affinePullback_of_comp_eq_id (C : Fin m → Fin n → ℝ)
    (c : Fin m → ℝ) (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ)
    (h : ∀ x, affine C c (affine B b x) = x) (ω : FormField m) :
    affinePullback B b (affinePullback C c ω) = ω := by
  have h' : ∀ x, affine (fun j l => ∑ i, C j i * B i l) (affine C c b) x = x := fun x => by
    rw [← affine_comp]; exact h x
  have hv : affine C c b = 0 := by
    have := h' 0
    funext j
    have hj := congrFun this j
    simpa [affine_apply] using hj
  have hM : (fun j l => ∑ i, C j i * B i l) = fun j l => if j = l then (1 : ℝ) else 0 := by
    funext j l
    have := congrFun (h' (Pi.single l 1)) j
    simp only [affine_apply, hv, Pi.zero_apply, add_zero, Pi.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at this
    rw [this]
  rw [affinePullback_affinePullback, hM, hv, affinePullback_id]

theorem polySpace_le_c1 {r k : ℕ} {ω : FormField n} (h : ω ∈ polySpace n r k) :
    ContDiff ℝ ⊤ ω := by
  obtain ⟨Ω, -, rfl⟩ := h
  exact contDiff_evalForm Ω

theorem polyMinusSpace_le_polySpace {r k : ℕ} (hr : 1 ≤ r) :
    polyMinusSpace n r k ≤ polySpace n r k :=
  Submodule.map_mono (Koszul.polyFormMinus_le_polyForm hr k)

theorem polySpace_le_polyMinusSpace (r k : ℕ) :
    polySpace n (r - 1) k ≤ polyMinusSpace n r k :=
  Submodule.map_mono (Koszul.polyForm_le_polyFormMinus r k)

/-! ### Local spaces on a simplex -/

variable {p : Fin (n + 1) → Fin n → ℝ}

/-- The matrix of `F_T⁻¹`. -/
def invMatrix (p : Fin (n + 1) → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => (edgeMatrix p)⁻¹ i j

/-- The offset of `F_T⁻¹(x) = B⁻¹ (x - p₀)`. -/
def invOffset (p : Fin (n + 1) → Fin n → ℝ) : Fin n → ℝ :=
  -Matrix.mulVec (edgeMatrix p)⁻¹ (p 0)

theorem affine_inv_simplexMap (hp : IsUnit (edgeMatrix p).det) (x : Fin n → ℝ) :
    affine (invMatrix p) (invOffset p) (simplexMap p x) = x := by
  have : simplexMap p x = Matrix.mulVec (edgeMatrix p) x + p 0 := by
    funext i; simp [simplexMap, affine_apply, Matrix.mulVec, dotProduct]
  have ha : ∀ y, affine (invMatrix p) (invOffset p) y = Matrix.mulVec (edgeMatrix p)⁻¹ y +
      invOffset p := fun y => by
    funext i; simp [affine_apply, invMatrix, Matrix.mulVec, dotProduct]
  rw [ha, this, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hp,
    Matrix.one_mulVec, invOffset, add_neg_cancel_right]

theorem simplexMap_affine_inv (hp : IsUnit (edgeMatrix p).det) (x : Fin n → ℝ) :
    simplexMap p (affine (invMatrix p) (invOffset p) x) = x := by
  have h1 : ∀ y, simplexMap p y = Matrix.mulVec (edgeMatrix p) y + p 0 := fun y => by
    funext i; simp [simplexMap, affine_apply, Matrix.mulVec, dotProduct]
  have ha : ∀ y, affine (invMatrix p) (invOffset p) y = Matrix.mulVec (edgeMatrix p)⁻¹ y +
      invOffset p := fun y => by
    funext i; simp [affine_apply, invMatrix, Matrix.mulVec, dotProduct]
  rw [h1, ha, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hp,
    Matrix.one_mulVec, invOffset, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hp, Matrix.one_mulVec]
  abel

/-- **The local space** `P_rΛᵏ(T)`: the pullback of the reference space `P_rΛᵏ(ℝⁿ)` (on `T̂`)
along `F_T⁻¹`. -/
def localPolySpace (p : Fin (n + 1) → Fin n → ℝ) (r k : ℕ) : Submodule ℝ (FormField n) :=
  (polySpace n r k).map (affinePullbackₗ (invMatrix p) (invOffset p))

/-- **The local space** `P_r⁻Λᵏ(T)`: the pullback of `P_r⁻Λᵏ(ℝⁿ)` along `F_T⁻¹`
(meaningful for `1 ≤ r`; see `polyMinusSpace`). -/
def localPolyMinusSpace (p : Fin (n + 1) → Fin n → ℝ) (r k : ℕ) : Submodule ℝ (FormField n) :=
  (polyMinusSpace n r k).map (affinePullbackₗ (invMatrix p) (invOffset p))

/-- **Affine invariance**: `P_rΛᵏ(T)` is the space of polynomial `k`-forms of degree `≤ r`,
independently of `T`. [AFW2010], §5.1.3 (remark on affine invariance) -/
theorem localPolySpace_eq (hp : IsUnit (edgeMatrix p).det) (r k : ℕ) :
    localPolySpace p r k = polySpace n r k := by
  refine le_antisymm ?_ fun ω h => ⟨affinePullback (simplexMatrix p) (p 0) ω,
    affinePullback_mem_polySpace _ _ h, ?_⟩
  · rintro _ ⟨ω, h, rfl⟩
    exact affinePullback_mem_polySpace _ _ h
  · exact affinePullback_affinePullback_of_comp_eq_id _ _ _ _ (simplexMap_affine_inv hp) ω

/-- **Affine invariance** of the trimmed spaces: `P_r⁻Λᵏ(T) = P_r⁻Λᵏ(ℝⁿ)`. -/
theorem localPolyMinusSpace_eq (hp : IsUnit (edgeMatrix p).det) (r k : ℕ) :
    localPolyMinusSpace p r k = polyMinusSpace n r k := by
  refine le_antisymm ?_ fun ω h => ⟨affinePullback (simplexMatrix p) (p 0) ω,
    affinePullback_mem_polyMinusSpace _ _ h, ?_⟩
  · rintro _ ⟨ω, h, rfl⟩
    exact affinePullback_mem_polyMinusSpace _ _ h
  · exact affinePullback_affinePullback_of_comp_eq_id _ _ _ _ (simplexMap_affine_inv hp) ω

/-- `F_T^*` maps `P_rΛᵏ(T)` onto the reference space. -/
theorem map_affinePullback_localPolySpace (hp : IsUnit (edgeMatrix p).det) (r k : ℕ) :
    (localPolySpace p r k).map (affinePullbackₗ (simplexMatrix p) (p 0)) = polySpace n r k := by
  rw [localPolySpace_eq hp]
  refine le_antisymm ?_ fun ω h => ⟨affinePullback (invMatrix p) (invOffset p) ω,
    affinePullback_mem_polySpace _ _ h, ?_⟩
  · rintro _ ⟨ω, h, rfl⟩
    exact affinePullback_mem_polySpace _ _ h
  · exact affinePullback_affinePullback_of_comp_eq_id _ _ _ _ (affine_inv_simplexMap hp) ω

/-! ### Traces on faces -/

/-- The **trace** on the face `p ∘ e` (`e : Fin (m + 1) → Fin (n + 1)` listing its vertices):
the pullback along the parametrization `F_{p ∘ e} : ℝᵐ → ℝⁿ`. -/
def faceTrace (p : Fin (n + 1) → Fin n → ℝ) (e : Fin (m + 1) → Fin (n + 1)) :
    FormField n →ₗ[ℝ] FormField m :=
  affinePullbackₗ (simplexMatrix (p ∘ e)) (p (e 0))

theorem faceTrace_apply (p : Fin (n + 1) → Fin n → ℝ) (e : Fin (m + 1) → Fin (n + 1))
    (ω : FormField n) :
    faceTrace p e ω = affinePullback (simplexMatrix (p ∘ e)) (p (e 0)) ω := rfl

/-- The barycentric left inverse `x ↦ (λ_{e(l+1)}(x))ₗ` of the face parametrization. -/
def faceRetractMatrix (p : Fin (n + 1) → Fin n → ℝ) (e : Fin (m + 1) → Fin (n + 1)) :
    Fin m → Fin n → ℝ :=
  fun l i => baryGrad p (e l.succ) i

def faceRetractOffset (p : Fin (n + 1) → Fin n → ℝ) (e : Fin (m + 1) → Fin (n + 1)) :
    Fin m → ℝ :=
  fun l => baryCoord p 0 (e l.succ)

theorem affine_faceRetract_simplexMap (hp : IsUnit (edgeMatrix p).det)
    {e : Fin (m + 1) → Fin (n + 1)} (he : Function.Injective e) (y : Fin m → ℝ) :
    affine (faceRetractMatrix p e) (faceRetractOffset p e) (simplexMap (p ∘ e) y) = y := by
  funext l
  have h := baryCoord_simplexMap_comp hp e y (e l.succ)
  rw [baryCoord_apply] at h
  rw [affine_apply]
  simp only [faceRetractMatrix, faceRetractOffset]
  rw [h, sum_eq_single l.succ (fun j _ hj => by simp [he.ne hj]) (by simp)]
  simp

/-- **Traces of `P_rΛᵏ`**: `tr_f P_rΛᵏ(T) = P_rΛᵏ(f)` for every face `f` of `T`. [AFW2010], §5.2 -/
theorem map_faceTrace_polySpace (hp : IsUnit (edgeMatrix p).det)
    {e : Fin (m + 1) → Fin (n + 1)} (he : Function.Injective e) (r k : ℕ) :
    (polySpace n r k).map (faceTrace p e) = polySpace m r k := by
  refine le_antisymm ?_ fun η h => ⟨_, affinePullback_mem_polySpace (faceRetractMatrix p e)
    (faceRetractOffset p e) h, ?_⟩
  · rintro _ ⟨ω, h, rfl⟩
    exact affinePullback_mem_polySpace _ _ h
  · exact affinePullback_affinePullback_of_comp_eq_id _ _ _ _
      (affine_faceRetract_simplexMap hp he) η

/-- **Traces of `P_r⁻Λᵏ`**: `tr_f P_r⁻Λᵏ(T) = P_r⁻Λᵏ(f)`. [AFW2010], §5.2 -/
theorem map_faceTrace_polyMinusSpace (hp : IsUnit (edgeMatrix p).det)
    {e : Fin (m + 1) → Fin (n + 1)} (he : Function.Injective e) (r k : ℕ) :
    (polyMinusSpace n r k).map (faceTrace p e) = polyMinusSpace m r k := by
  refine le_antisymm ?_ fun η h => ⟨_, affinePullback_mem_polyMinusSpace (faceRetractMatrix p e)
    (faceRetractOffset p e) h, ?_⟩
  · rintro _ ⟨ω, h, rfl⟩
    exact affinePullback_mem_polyMinusSpace _ _ h
  · exact affinePullback_affinePullback_of_comp_eq_id _ _ _ _
      (affine_faceRetract_simplexMap hp he) η

/-! ### Polynomials vanishing on coordinate hyperplanes -/

/-- A real polynomial vanishing on the hyperplane `xᵢ = 0` is divisible by `xᵢ`. -/
theorem X_dvd_of_eval_eq_zero {q : MvPolynomial (Fin n) ℝ} {i : Fin n}
    (h : ∀ x : Fin n → ℝ, x i = 0 → eval x q = 0) : X i ∣ q := by
  classical
  rw [X_dvd_iff_modMonomial_eq_zero]
  set r := q.modMonomial (Finsupp.single i 1)
  have hsupp : ∀ v ∈ r.support, v i = 0 := by
    intro v hv
    by_contra hvi
    have hle : Finsupp.single i 1 ≤ v := by
      rw [Finsupp.single_le_iff]; omega
    exact (mem_support_iff.1 hv) (coeff_modMonomial_of_le q hle)
  have hind : ∀ x : Fin n → ℝ, eval x r = eval (Function.update x i 0) r := by
    intro x
    rw [eval_eq', eval_eq']
    refine sum_congr rfl fun v hv => ?_
    congr 1
    refine prod_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj; rw [hsupp v hv, pow_zero, pow_zero]
    · rw [Function.update_of_ne hj]
  have hq := divMonomial_add_modMonomial_single q i
  refine MvPolynomial.funext fun x => ?_
  rw [hind, map_zero]
  have h0 := h (Function.update x i 0) (by simp)
  rw [← hq, map_add, map_mul, eval_X, Function.update_self, zero_mul, zero_add] at h0
  exact h0

/-- Divisibility by distinct variables gives divisibility by their product. -/
theorem prod_X_dvd {q : MvPolynomial (Fin n) ℝ} (S : Finset (Fin n)) (h : ∀ j ∈ S, X j ∣ q) :
    (∏ j ∈ S, X j) ∣ q := by
  classical
  induction S using Finset.induction_on generalizing q with
  | empty => simp
  | insert a S ha ih =>
    obtain ⟨q', rfl⟩ := h a (mem_insert_self a S)
    rw [prod_insert ha]
    refine mul_dvd_mul_left _ (ih fun j hj => ?_)
    have := h j (mem_insert_of_mem hj)
    rcases (X_dvd_mul_iff.1 this) with h1 | h1
    · exact absurd (X_dvd_X.1 h1) fun e => ha (e ▸ hj)
    · exact h1

theorem totalDegree_prod_X (S : Finset (Fin n)) :
    (∏ j ∈ S, (X j : MvPolynomial (Fin n) ℝ)).totalDegree = #S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [prod_insert ha, totalDegree_mul_of_isDomain (X_ne_zero a)
      (Finset.prod_ne_zero_iff.2 fun j _ => X_ne_zero j), totalDegree_X, ih,
      card_insert_of_notMem ha, add_comm]

theorem eval_prod_X_pos {S : Finset (Fin n)} {x : Fin n → ℝ} (hx : ∀ j, 0 < x j) :
    0 < eval x (∏ j ∈ S, (X j : MvPolynomial (Fin n) ℝ)) := by
  rw [map_prod]
  exact prod_pos fun j _ => by simpa using hx j

theorem eval_prod_X_nonneg {S : Finset (Fin n)} {x : Fin n → ℝ} (hx : ∀ j, 0 ≤ x j) :
    0 ≤ eval x (∏ j ∈ S, (X j : MvPolynomial (Fin n) ℝ)) := by
  rw [map_prod]
  exact prod_nonneg fun j _ => by simpa using hx j

/-! ### A positivity argument on the reference simplex -/

/-- A box in the interior of `T̂ₙ`. -/
theorem pi_Ioo_subset_refSimplex :
    Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) (1 / (n + 1))) ⊆ refSimplex n := by
  intro x hx
  rw [mem_refSimplex_iff]
  refine ⟨fun i => (hx i (Set.mem_univ i)).1.le, ?_⟩
  calc ∑ i, x i ≤ ∑ _i : Fin n, (1 / (n + 1) : ℝ) :=
        sum_le_sum fun i _ => (hx i (Set.mem_univ i)).2.le
    _ = n / (n + 1) := by simp [div_eq_mul_inv]
    _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith

/-- A continuous function, nonnegative on `T̂ₙ` with zero integral, vanishes on an interior
box. -/
theorem eq_zero_of_setIntegral_refSimplex_eq_zero {g : (Fin n → ℝ) → ℝ} (hg : Continuous g)
    (h0 : ∀ x ∈ refSimplex n, 0 ≤ g x) (hint : ∫ x in refSimplex n, g x = 0) :
    ∀ x ∈ Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) (1 / (n + 1))), g x = 0 := by
  intro x₀ hx₀
  by_contra hne
  have hpos : 0 < g x₀ := lt_of_le_of_ne (h0 x₀ (pi_Ioo_subset_refSimplex hx₀)) (Ne.symm hne)
  have hint' : IntegrableOn g (refSimplex n) :=
    hg.continuousOn.integrableOn_compact (isCompact_refSimplex n)
  have hae : 0 ≤ᵐ[volume.restrict (refSimplex n)] g :=
    (ae_restrict_iff' (measurableSet_refSimplex n)).2 (Filter.Eventually.of_forall h0)
  have := (setIntegral_pos_iff_support_of_nonneg_ae hae hint').2 ?_
  · linarith
  set U := Function.support g ∩ Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) (1 / (n + 1)))
  have hU : IsOpen U := (isOpen_ne_fun hg continuous_const).inter
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo)
  have hUne : U.Nonempty := ⟨x₀, ne_of_gt hpos, hx₀⟩
  exact lt_of_lt_of_le (hU.measure_pos volume hUne) (measure_mono
    (Set.inter_subset_inter_right _ pi_Ioo_subset_refSimplex))

/-- A polynomial vanishing on an interior box of `T̂ₙ` vanishes. -/
theorem eq_zero_of_eval_eq_zero_on_box {q : MvPolynomial (Fin n) ℝ}
    (h : ∀ x ∈ Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) (1 / (n + 1))), eval x q = 0) :
    q = 0 := by
  refine MvPolynomial.funext_set (fun _ => Set.Ioo (0 : ℝ) (1 / (n + 1)))
    (fun _ => Set.Ioo_infinite (by positivity)) fun x hx => ?_
  rw [h x hx, map_zero]

/-! ### Forms with vanishing traces on the coordinate faces ([AFW2006], Lemmas 4.5–4.6) -/

/-- **[AFW2006], Lemmas 4.5–4.6**: a polynomial `k`-form `ω ∈ P_rΛᵏ(ℝⁿ)` whose coefficients
`ω_σ` vanish on the coordinate hyperplanes `xᵢ = 0`, `i ∉ σ` (i.e. whose traces on the faces of
`T̂` through the origin vanish), and which is orthogonal on `T̂` to `P_{r+k-n}Λ^{n-k}` under
`(ω, η) ↦ ∫_{T̂} ω ∧ η`, vanishes. (If `r + k < n` the test space is `0` and no orthogonality is
needed.) By Lemma 4.5, `ω_σ = x_{σᶜ} b_σ` with `b_σ ∈ P_{r+k-n}`, and the test form
`η = Σ_σ ε(σ, σᶜ) b_σ dx_{σᶜ}` gives `∫_{T̂} Σ_σ x_{σᶜ} b_σ² = 0`. -/
theorem eq_zero_of_coordTrace_of_integral {r k : ℕ} {Ω : Koszul.PolyForm ℝ (Fin n)}
    (hΩ : Ω ∈ Koszul.polyForm ℝ (Fin n) r k)
    (htr : ∀ σ : Finset (Fin n), ∀ i ∉ σ, ∀ x : Fin n → ℝ, x i = 0 → eval x (Ω σ) = 0)
    (hint : n ≤ r + k → ∀ H ∈ Koszul.polyForm ℝ (Fin n) (r + k - n) (n - k),
      ∫ x in refSimplex n, eval x (wedgeForm Ω H univ) = 0) : Ω = 0 := by
  classical
  have hdvd : ∀ σ : Finset (Fin n), ∃ c, Ω σ = (∏ j ∈ σᶜ, X j) * c := fun σ =>
    prod_X_dvd _ fun j hj => X_dvd_of_eval_eq_zero (htr σ j (mem_compl.1 hj))
  choose b hb using hdvd
  have hXne : ∀ σ : Finset (Fin n), (∏ j ∈ σᶜ, (X j : MvPolynomial (Fin n) ℝ)) ≠ 0 := fun σ =>
    Finset.prod_ne_zero_iff.2 fun j _ => X_ne_zero j
  have hb0 : ∀ σ, Ω σ = 0 ↔ b σ = 0 := fun σ => by
    rw [hb σ, mul_eq_zero, or_iff_right (hXne σ)]
  -- degrees
  have hdeg : ∀ σ : Finset (Fin n), #σ = k → b σ ≠ 0 →
      n - k ≤ r ∧ (b σ).totalDegree ≤ r + k - n := by
    intro σ hσ hne
    have h1 := hΩ.2 σ
    rw [hb σ, totalDegree_mul_of_isDomain (hXne σ) hne, totalDegree_prod_X, card_compl, hσ,
      Fintype.card_fin] at h1
    constructor <;> omega
  have hk : ∀ σ : Finset (Fin n), #σ ≠ k → b σ = 0 := fun σ hσ => (hb0 σ).1 (hΩ.1 σ hσ)
  suffices hall : ∀ σ, b σ = 0 from funext fun σ => (hb0 σ).2 (hall σ)
  by_cases hkn : k ≤ n
  swap
  · intro σ
    refine hk σ fun h => hkn ?_
    rw [← h]; simpa using card_le_univ σ
  by_cases hnr : n ≤ r + k
  swap
  · intro σ
    by_contra hne
    by_cases hσ : #σ = k
    · have := (hdeg σ hσ hne).1; omega
    · exact hne (hk σ hσ)
  -- the test form
  set H : Koszul.PolyForm ℝ (Fin n) := fun t =>
    if #t = n - k then C (shuffleSgn tᶜ t) * b tᶜ else 0 with hH
  have hHmem : H ∈ Koszul.polyForm ℝ (Fin n) (r + k - n) (n - k) := by
    refine ⟨fun t ht => by simp [H, ht], fun t => ?_⟩
    simp only [H]
    split_ifs with ht
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      by_cases hne : b tᶜ = 0
      · rw [hne]; simp
      · have hc : #tᶜ = k := by
          rw [card_compl, ht, Fintype.card_fin]
          omega
        exact (hdeg _ hc hne).2
    · simp
  have hwedge : ∀ x, eval x (wedgeForm Ω H univ) =
      ∑ σ, if #σ = k then eval x (∏ j ∈ σᶜ, X j) * eval x (b σ) ^ 2 else 0 := by
    intro x
    rw [wedgeForm_apply, map_sum, powerset_univ]
    refine sum_congr rfl fun σ _ => ?_
    rw [← compl_eq_univ_sdiff]
    by_cases hσ : #σ = k
    · have hc : #σᶜ = n - k := by rw [card_compl, hσ, Fintype.card_fin]
      simp only [H, hc, ↓reduceIte, compl_compl, hσ]
      rw [hb σ, Koszul.shuffleSgn_eq_C]
      have h2 := shuffleSgn_mul_self (R := ℝ) σ σᶜ
      simp only [map_mul, eval_C]
      linear_combination (eval x (∏ j ∈ σᶜ, X j) * eval x (b σ) ^ 2) * h2
    · rw [hΩ.1 σ hσ]; simp [hσ]
  have hcont : Continuous fun x : Fin n → ℝ => eval x (wedgeForm Ω H univ) :=
    (contDiff_eval _ (r := 0)).continuous
  have hnonneg : ∀ x ∈ refSimplex n, 0 ≤ eval x (wedgeForm Ω H univ) := by
    intro x hx
    rw [hwedge]
    refine sum_nonneg fun σ _ => ?_
    split_ifs
    · exact mul_nonneg (eval_prod_X_nonneg (mem_refSimplex_iff.1 hx).1) (sq_nonneg _)
    · exact le_rfl
  have hzero := eq_zero_of_setIntegral_refSimplex_eq_zero hcont hnonneg (hint hnr H hHmem)
  intro σ
  by_cases hσ : #σ = k
  swap
  · exact hk σ hσ
  refine eq_zero_of_eval_eq_zero_on_box fun x hx => ?_
  have hxpos : ∀ j, 0 < x j := fun j => (hx j (Set.mem_univ j)).1
  have hsum := hzero x hx
  rw [hwedge] at hsum
  have hterm := (sum_eq_zero_iff_of_nonneg fun σ' _ => by
    split_ifs
    · exact mul_nonneg (eval_prod_X_nonneg fun j => (hxpos j).le) (sq_nonneg _)
    · exact le_rfl).1 hsum σ (mem_univ σ)
  simp only [hσ, ↓reduceIte] at hterm
  have hX := eval_prod_X_pos (S := σᶜ) hxpos
  have : eval x (b σ) ^ 2 = 0 := by
    rcases mul_eq_zero.1 hterm with h | h
    · exact absurd h hX.ne'
    · exact h
  exact pow_eq_zero_iff (two_ne_zero) |>.1 this

/-! ### Bubbles: forms with vanishing trace on `∂T` -/

/-- `ω` has **vanishing trace on `∂T`**: its traces on all proper faces `p ∘ e`
(`e : Fin (m + 1) ↪o Fin (n + 1)`, `m < n`) vanish. -/
def IsBubble (p : Fin (n + 1) → Fin n → ℝ) (ω : FormField n) : Prop :=
  ∀ (m : ℕ) (e : Fin (m + 1) ↪o Fin (n + 1)), m < n → faceTrace p e ω = 0

/-- The **bubble space** `V̊ = {ω ∈ V | tr_{∂T} ω = 0}` of a space `V` of form fields on `T`. -/
def bubbleSpace (p : Fin (n + 1) → Fin n → ℝ) (V : Submodule ℝ (FormField n)) :
    Submodule ℝ (FormField n) where
  carrier := {ω | ω ∈ V ∧ IsBubble p ω}
  zero_mem' := ⟨V.zero_mem, fun m e _ => map_zero _⟩
  add_mem' ha hb := ⟨V.add_mem ha.1 hb.1, fun m e hm => by rw [map_add, ha.2 m e hm,
    hb.2 m e hm, add_zero]⟩
  smul_mem' c ω h := ⟨V.smul_mem c h.1, fun m e hm => by rw [map_smul, h.2 m e hm, smul_zero]⟩

/-- The pointwise exterior product of form fields. -/
def wedgeField (ω η : FormField n) : FormField n := fun x => wedgeForm (ω x) (η x)

theorem evalForm_wedgeForm' (ω η : Koszul.PolyForm ℝ (Fin n)) :
    evalForm n (wedgeForm ω η) = wedgeField (evalForm n ω) (evalForm n η) :=
  funext fun x => evalForm_wedgeForm ω η x

/-- **Traces are multiplicative**: `tr_f (ω ∧ η) = tr_f ω ∧ tr_f η`. -/
theorem faceTrace_wedgeField (p : Fin (n + 1) → Fin n → ℝ) (e : Fin (m + 1) → Fin (n + 1))
    (ω η : FormField n) :
    faceTrace p e (wedgeField ω η) = wedgeField (faceTrace p e ω) (faceTrace p e η) := by
  funext x
  simp only [faceTrace_apply, affinePullback_apply, wedgeField, pullback_wedgeForm]

/-- **Traces commute with `d`** (for differentiable forms). -/
theorem faceTrace_extDeriv (p : Fin (n + 1) → Fin n → ℝ) (e : Fin (m + 1) → Fin (n + 1))
    {ω : FormField n} (hω : Differentiable ℝ ω) :
    faceTrace p e (extDeriv ω) = extDeriv (faceTrace p e ω) := by
  funext x
  rw [faceTrace_apply, faceTrace_apply, extDeriv_affinePullback_apply _ _ (hω _)]

theorem IsBubble.extDeriv {p : Fin (n + 1) → Fin n → ℝ} {ω : FormField n} (h : IsBubble p ω)
    (hω : Differentiable ℝ ω) : IsBubble p (extDeriv ω) := fun m e hm => by
  rw [faceTrace_extDeriv p e hω, h m e hm]
  funext x s; simp [FiniteElement.extDeriv_apply]

/-- The trace on the coordinate face `{xᵢ = 0}` of `T̂_{N+1}` (opposite the vertex `v̂_{i+1}`)
restricts to the coordinates other than `i`. -/
theorem faceTrace_refVertex_succAbove_succ {N : ℕ} (i : Fin (N + 1)) (ω : FormField (N + 1))
    (y : Fin N → ℝ) :
    faceTrace (refVertex (N + 1)) (Fin.succAbove i.succ) ω y =
      restrict (Fin.succAboveOrderEmb i)
        (ω (affine (fun j l => if j = i.succAbove l then 1 else 0) 0 y)) := by
  have hB : simplexMatrix (refVertex (N + 1) ∘ Fin.succAbove i.succ) =
      fun j l => if j = i.succAbove l then 1 else 0 := by
    funext j l
    simp only [simplexMatrix, Function.comp_apply, Fin.succ_succAbove_succ,
      Fin.succ_succAbove_zero, refVertex_succ, refVertex_zero, Pi.zero_apply, sub_zero,
      Pi.single_apply]
  rw [faceTrace_apply, affinePullback_apply, hB]
  simp only [Fin.succ_succAbove_zero, refVertex_zero]
  refine pullback_eq_restrict (Fin.succAboveOrderEmb i) (fun j l => ?_) _
  simp only [Fin.coe_succAboveOrderEmb]
  exact ⟨fun h => by simp [h], fun h => by simp [h]⟩

/-- Vanishing traces on the coordinate faces mean that the coefficients `ω_σ` vanish on the
hyperplanes `xᵢ = 0`, `i ∉ σ`. -/
theorem apply_eq_zero_of_faceTrace_eq_zero {N : ℕ} {i : Fin (N + 1)} {ω : FormField (N + 1)}
    (h : faceTrace (refVertex (N + 1)) (Fin.succAbove i.succ) ω = 0) {σ : Finset (Fin (N + 1))}
    (hσ : i ∉ σ) {x : Fin (N + 1) → ℝ} (hx : x i = 0) : ω x σ = 0 := by
  have hpt : affine (fun j l => if j = i.succAbove l then (1 : ℝ) else 0) 0
      (fun l => x (i.succAbove l)) = x := by
    funext j
    simp only [affine_apply, Pi.zero_apply, add_zero, ite_mul, one_mul, zero_mul]
    by_cases hj : j = i
    · subst hj
      rw [hx]
      exact sum_eq_zero fun l _ => by simp [Ne.symm (Fin.succAbove_ne j l)]
    · obtain ⟨l₀, rfl⟩ := Fin.exists_succAbove_eq hj
      rw [sum_eq_single l₀ (fun l _ hl => by simp [(Fin.succAbove_right_injective).ne hl.symm])
        (by simp)]
      simp
  have hσ' : σ = (σ.preimage i.succAbove Fin.succAbove_right_injective.injOn).map
      (Fin.succAboveOrderEmb i).toEmbedding := by
    ext j
    simp only [mem_map, mem_preimage, RelEmbedding.coe_toEmbedding, Fin.coe_succAboveOrderEmb]
    constructor
    · intro hj
      have hji : j ≠ i := fun e => hσ (e ▸ hj)
      obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hji
      exact ⟨l, hj, rfl⟩
    · rintro ⟨l, hl, rfl⟩; exact hl
  have := congrFun (congrFun h (fun l => x (i.succAbove l)))
    (σ.preimage i.succAbove Fin.succAbove_right_injective.injOn)
  rw [faceTrace_refVertex_succAbove_succ, hpt, ExteriorFibre.restrict, ← hσ'] at this
  exact this

theorem IsBubble.faceTrace_succAbove {N : ℕ} {p : Fin (N + 2) → Fin (N + 1) → ℝ}
    {ω : FormField (N + 1)} (h : IsBubble p ω) (i : Fin (N + 2)) :
    faceTrace p (Fin.succAbove i) ω = 0 := by
  have := h N (Fin.succAboveOrderEmb i) (Nat.lt_succ_self N)
  rwa [Fin.coe_succAboveOrderEmb] at this

/-- A bubble's coefficients vanish on the coordinate hyperplanes `xᵢ = 0`, `i ∉ σ`. -/
theorem IsBubble.eval_eq_zero {Ω : Koszul.PolyForm ℝ (Fin n)}
    (h : IsBubble (refVertex n) (evalForm n Ω)) (σ : Finset (Fin n)) (i : Fin n) (hi : i ∉ σ)
    (x : Fin n → ℝ) (hx : x i = 0) : eval x (Ω σ) = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ N =>
    have := apply_eq_zero_of_faceTrace_eq_zero (h.faceTrace_succAbove i.succ) hi hx
    rwa [evalForm_apply] at this

/-- `d` of a polynomial form with constant coefficients vanishes. -/
theorem extDeriv_eq_zero_of_mem_polyForm_zero {k : ℕ} {Ω : Koszul.PolyForm ℝ (Fin n)}
    (h : Ω ∈ Koszul.polyForm ℝ (Fin n) 0 k) : Koszul.extDeriv Ω = 0 := by
  rw [← Koszul.sum_homComp h, Finset.sum_range_one]
  exact Koszul.extDeriv_homComp_zero Ω

/-- **Stokes' theorem for a bubble**: if `ω` has vanishing trace on `∂T̂`, then
`∫_{T̂} dω ∧ μ = -(-1)^k ∫_{T̂} ω ∧ dμ` for polynomial forms `ω` (of degree `k`) and `μ`. -/
theorem integral_extDeriv_wedge_of_isBubble {N k : ℕ} {Ω M : Koszul.PolyForm ℝ (Fin (N + 1))}
    (hΩ : IsDeg k Ω) (hbub : IsBubble (refVertex (N + 1)) (evalForm (N + 1) Ω)) :
    ∫ x in refSimplex (N + 1), eval x (wedgeForm (Koszul.extDeriv Ω) M univ) =
      -((-1) ^ k * ∫ x in refSimplex (N + 1), eval x (wedgeForm Ω (Koszul.extDeriv M) univ)) := by
  set η := evalForm (N + 1) (wedgeForm Ω M)
  have hS := setIntegral_refSimplex_extDeriv (m := N) (η := η) isOpen_univ (Set.subset_univ _)
    (contDiff_evalForm _).contDiffOn
  have hface : ∀ i : Fin (N + 2), simplexIntegral (refVertex (N + 1) ∘ i.succAbove) η = 0 := by
    intro i
    have h0 : faceTrace (refVertex (N + 1)) (Fin.succAbove i) η = 0 := by
      change faceTrace _ _ (evalForm (N + 1) (wedgeForm Ω M)) = 0
      rw [evalForm_wedgeForm', faceTrace_wedgeField, hbub.faceTrace_succAbove i]
      funext x; simp [wedgeField]
    have : simplexIntegral (refVertex (N + 1) ∘ i.succAbove) η =
        ∫ x in refSimplex N, faceTrace (refVertex (N + 1)) (Fin.succAbove i) η x univ := rfl
    rw [this, h0]; simp
  simp only [hface, mul_zero, sum_const_zero] at hS
  rw [extDeriv_evalForm, Koszul.extDeriv_wedgeForm hΩ] at hS
  have hc : ∀ Ψ : Koszul.PolyForm ℝ (Fin (N + 1)),
      IntegrableOn (fun x => eval x (Ψ univ)) (refSimplex (N + 1)) := fun Ψ =>
    (contDiff_eval _ (r := 0)).continuous.continuousOn.integrableOn_compact
      (isCompact_refSimplex _)
  have hsplit : (fun x => evalForm (N + 1) (wedgeForm (Koszul.extDeriv Ω) M +
      (-1 : MvPolynomial (Fin (N + 1)) ℝ) ^ k • wedgeForm Ω (Koszul.extDeriv M)) x univ) =
      fun x => eval x (wedgeForm (Koszul.extDeriv Ω) M univ) +
        (-1) ^ k * eval x (wedgeForm Ω (Koszul.extDeriv M) univ) := by
    funext x
    simp [evalForm_apply]
  rw [hsplit, integral_add (hc _) ((hc _).const_mul _), integral_const_mul] at hS
  linarith

/-- If `ω` is a closed bubble, `∫_{T̂} ω ∧ dμ = 0`. -/
theorem integral_wedge_extDeriv_eq_zero_of_isBubble {N k : ℕ}
    {Ω M : Koszul.PolyForm ℝ (Fin (N + 1))} (hΩ : IsDeg k Ω)
    (hbub : IsBubble (refVertex (N + 1)) (evalForm (N + 1) Ω)) (hd : Koszul.extDeriv Ω = 0) :
    ∫ x in refSimplex (N + 1), eval x (wedgeForm Ω (Koszul.extDeriv M) univ) = 0 := by
  have h := integral_extDeriv_wedge_of_isBubble (M := M) hΩ hbub
  rw [hd] at h
  simp only [wedgeForm_zero_left, Pi.zero_apply, map_zero, integral_zero] at h
  have h1 : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have : (-1 : ℝ) ^ k * ∫ x in refSimplex (N + 1),
      eval x (wedgeForm Ω (Koszul.extDeriv M) univ) = 0 := by linarith
  exact (mul_eq_zero.1 this).resolve_left h1

theorem integral_wedge_add {Ω H H' : Koszul.PolyForm ℝ (Fin n)} :
    ∫ x in refSimplex n, eval x (wedgeForm Ω (H + H') univ) =
      (∫ x in refSimplex n, eval x (wedgeForm Ω H univ)) +
        ∫ x in refSimplex n, eval x (wedgeForm Ω H' univ) := by
  have hc : ∀ Ψ : Koszul.PolyForm ℝ (Fin n),
      IntegrableOn (fun x => eval x (Ψ univ)) (refSimplex n) := fun Ψ =>
    (contDiff_eval _ (r := 0)).continuous.continuousOn.integrableOn_compact
      (isCompact_refSimplex _)
  rw [← integral_add (hc (wedgeForm Ω H)) (hc (wedgeForm Ω H'))]
  congr 1
  funext x
  rw [wedgeForm_add_right, Pi.add_apply, map_add]

/-- `P_r⁻Λⁿ(ℝⁿ) = P_{r-1}Λⁿ(ℝⁿ)` (`κ` of an `(n+1)`-form vanishes). -/
theorem polyFormMinus_top_le (r : ℕ) :
    Koszul.polyFormMinus ℝ (Fin n) r n ≤ Koszul.polyForm ℝ (Fin n) (r - 1) n := by
  refine sup_le le_rfl ?_
  rintro _ ⟨c, hc, rfl⟩
  have : c = 0 := funext fun s => hc.1 s fun h => by
    have := card_le_univ s; simp at this; omega
  rw [this, map_zero]
  exact Submodule.zero_mem _

/-- **[AFW2006], Lemma 4.7** (bubbles of `P_rΛᵏ`): if `ω ∈ P_rΛᵏ(T̂)` (`r ≥ 1`) has vanishing
trace on `∂T̂` and `∫_{T̂} ω ∧ η = 0` for all `η ∈ P⁻_{r+k-n}Λ^{n-k}` (a condition only when
`r + k > n`; otherwise this test space is `0`), then `ω = 0`. -/
theorem eq_zero_of_isBubble_of_mem_polyForm {r k : ℕ} (hr : 1 ≤ r)
    {Ω : Koszul.PolyForm ℝ (Fin n)} (hΩ : Ω ∈ Koszul.polyForm ℝ (Fin n) r k)
    (hbub : IsBubble (refVertex n) (evalForm n Ω))
    (hint : n < r + k → ∀ H ∈ Koszul.polyFormMinus ℝ (Fin n) (r + k - n) (n - k),
      ∫ x in refSimplex n, eval x (wedgeForm Ω H univ) = 0) : Ω = 0 := by
  by_cases hkn : n ≤ k
  · refine eq_zero_of_coordTrace_of_integral hΩ hbub.eval_eq_zero fun hnr H hH => ?_
    refine hint (by omega) H ?_
    rw [show n - k = 0 by omega, Koszul.polyFormMinus_zero (by omega)]
    rwa [show n - k = 0 by omega] at hH
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hdmem := Koszul.extDeriv_mem_polyForm hΩ
  have hdbub : IsBubble (refVertex (N + 1)) (evalForm (N + 1) (Koszul.extDeriv Ω)) := by
    rw [← extDeriv_evalForm]
    exact hbub.extDeriv ((contDiff_evalForm Ω (r := 1)).differentiable one_ne_zero)
  -- `dω = 0`
  have hd : Koszul.extDeriv Ω = 0 := by
    refine eq_zero_of_coordTrace_of_integral hdmem hdbub.eval_eq_zero fun hnr M hM => ?_
    rw [integral_extDeriv_wedge_of_isBubble hΩ.1 hbub]
    have hdM : Koszul.extDeriv M ∈ Koszul.polyForm ℝ (Fin (N + 1)) (r + k - (N + 1) - 1)
        (N + 1 - k) := by
      have := Koszul.extDeriv_mem_polyForm hM
      rwa [show r - 1 + (k + 1) - (N + 1) = r + k - (N + 1) by omega,
        show N + 1 - (k + 1) + 1 = N + 1 - k by omega] at this
    rcases Nat.lt_or_ge (N + 1) (r + k) with hlt | hge
    · rw [hint hlt _ (Koszul.polyForm_le_polyFormMinus _ _ hdM)]; ring
    · have hM0 : Koszul.extDeriv M = 0 := extDeriv_eq_zero_of_mem_polyForm_zero
        (by rwa [show r - 1 + (k + 1) - (N + 1) = 0 by omega] at hM)
      rw [hM0]; simp
  -- `ω ⊥ P_{r+k-n}Λ^{n-k}`
  refine eq_zero_of_coordTrace_of_integral hΩ hbub.eval_eq_zero fun hnr H hH => ?_
  obtain ⟨j, hj⟩ : ∃ j, N + 1 - k = j + 1 := ⟨N - k, by omega⟩
  rw [hj] at hH
  rcases Nat.eq_zero_or_pos (r + k - (N + 1)) with hs | hs
  · rw [hs] at hH
    obtain ⟨c, -, rfl⟩ := Koszul.exists_extDeriv_eq_of_mem_polyForm hH
      (extDeriv_eq_zero_of_mem_polyForm_zero hH)
    exact integral_wedge_extDeriv_eq_zero_of_isBubble hΩ.1 hbub hd
  · rw [← Koszul.polyFormMinus_sup_map_extDeriv hs] at hH
    obtain ⟨a, ha, b, ⟨c, -, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hH
    rw [integral_wedge_add, hint (by omega) a (by rwa [hj]),
      show (Koszul.extDerivₗ ℝ (Fin (N + 1))) c = Koszul.extDeriv c from rfl,
      integral_wedge_extDeriv_eq_zero_of_isBubble hΩ.1 hbub hd, add_zero]

/-- **[AFW2006], Lemma 4.11** (bubbles of `P_r⁻Λᵏ`): if `ω ∈ P_r⁻Λᵏ(T̂)` (`r ≥ 1`) has vanishing
trace on `∂T̂` and `∫_{T̂} ω ∧ η = 0` for all `η ∈ P_{r+k-n-1}Λ^{n-k}` (a condition only when
`r + k > n`), then `ω = 0`. -/
theorem eq_zero_of_isBubble_of_mem_polyFormMinus {r k : ℕ} (hr : 1 ≤ r)
    {Ω : Koszul.PolyForm ℝ (Fin n)} (hΩ : Ω ∈ Koszul.polyFormMinus ℝ (Fin n) r k)
    (hbub : IsBubble (refVertex n) (evalForm n Ω))
    (hint : n < r + k → ∀ H ∈ Koszul.polyForm ℝ (Fin n) (r + k - n - 1) (n - k),
      ∫ x in refSimplex n, eval x (wedgeForm Ω H univ) = 0) : Ω = 0 := by
  by_cases hkn : n ≤ k
  · by_cases hkn' : k = n
    · subst hkn'
      have hΩ' := polyFormMinus_top_le r hΩ
      refine eq_zero_of_coordTrace_of_integral hΩ' hbub.eval_eq_zero fun hnr H hH => ?_
      refine hint (by omega) H ?_
      rwa [show r - 1 + k - k = r + k - k - 1 by omega] at hH
    · have hdeg : IsDeg k Ω := (Koszul.polyFormMinus_le_polyForm_succ r k hΩ).1
      exact funext fun s => hdeg s fun h => by have := card_le_univ s; simp at this; omega
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hdmem := Koszul.extDeriv_mem_polyForm_sub_one_of_mem_polyFormMinus hΩ
  have hdeg : IsDeg k Ω := (Koszul.polyFormMinus_le_polyForm_succ r k hΩ).1
  have hdbub : IsBubble (refVertex (N + 1)) (evalForm (N + 1) (Koszul.extDeriv Ω)) := by
    rw [← extDeriv_evalForm]
    exact hbub.extDeriv ((contDiff_evalForm Ω (r := 1)).differentiable one_ne_zero)
  have hd : Koszul.extDeriv Ω = 0 := by
    refine eq_zero_of_coordTrace_of_integral hdmem hdbub.eval_eq_zero fun hnr M hM => ?_
    rw [integral_extDeriv_wedge_of_isBubble hdeg hbub]
    have hdM : Koszul.extDeriv M ∈ Koszul.polyForm ℝ (Fin (N + 1)) (r + k - (N + 1) - 1)
        (N + 1 - k) := by
      have := Koszul.extDeriv_mem_polyForm hM
      rwa [show r - 1 + (k + 1) - (N + 1) = r + k - (N + 1) by omega,
        show N + 1 - (k + 1) + 1 = N + 1 - k by omega] at this
    rcases Nat.lt_or_ge (N + 1) (r + k) with hlt | hge
    · rw [hint hlt _ hdM]; ring
    · have hM0 : Koszul.extDeriv M = 0 := extDeriv_eq_zero_of_mem_polyForm_zero
        (by rwa [show r - 1 + (k + 1) - (N + 1) = 0 by omega] at hM)
      rw [hM0]; simp
  have hΩ' := Koszul.mem_polyForm_of_mem_polyFormMinus_of_extDeriv_eq_zero hr hΩ hd
  refine eq_zero_of_coordTrace_of_integral hΩ' hbub.eval_eq_zero fun hnr H hH => ?_
  exact hint (by omega) H (by rwa [show r - 1 + k - (N + 1) = r + k - (N + 1) - 1 by omega] at hH)

/-! ### Bubble spaces in terms of form fields -/

theorem simplexIntegral_wedgeField_evalForm (Ω H : Koszul.PolyForm ℝ (Fin n)) :
    simplexIntegral (refVertex n) (wedgeField (evalForm n Ω) (evalForm n H)) =
      ∫ x in refSimplex n, eval x (wedgeForm Ω H univ) := by
  rw [simplexIntegral_refVertex, ← evalForm_wedgeForm']
  rfl

/-- **The bubbles of `P_rΛᵏ(T̂)` are detected by `P⁻_{r+k-n}Λ^{n-k}(T̂)`** ([AFW2006], Lemma 4.7):
a form in `P̊_rΛᵏ(T̂)` with `∫_{T̂} ω ∧ η = 0` for all `η ∈ P⁻_{r+k-n}Λ^{n-k}` vanishes; and
`P̊_rΛᵏ(T̂) = 0` when `r + k ≤ n`. -/
theorem eq_zero_of_mem_bubbleSpace_polySpace {r k : ℕ} (hr : 1 ≤ r) {ω : FormField n}
    (hω : ω ∈ bubbleSpace (refVertex n) (polySpace n r k))
    (hint : n < r + k → ∀ η ∈ polyMinusSpace n (r + k - n) (n - k),
      simplexIntegral (refVertex n) (wedgeField ω η) = 0) : ω = 0 := by
  obtain ⟨⟨Ω, hΩ, rfl⟩, hbub⟩ := hω
  rw [eq_zero_of_isBubble_of_mem_polyForm hr hΩ hbub fun h H hH => by
    rw [← simplexIntegral_wedgeField_evalForm]; exact hint h _ ⟨H, hH, rfl⟩, map_zero]

/-- **The bubbles of `P_r⁻Λᵏ(T̂)` are detected by `P_{r+k-n-1}Λ^{n-k}(T̂)`** ([AFW2006],
Lemma 4.11); `P̊_r⁻Λᵏ(T̂) = 0` when `r + k ≤ n`. -/
theorem eq_zero_of_mem_bubbleSpace_polyMinusSpace {r k : ℕ} (hr : 1 ≤ r) {ω : FormField n}
    (hω : ω ∈ bubbleSpace (refVertex n) (polyMinusSpace n r k))
    (hint : n < r + k → ∀ η ∈ polySpace n (r + k - n - 1) (n - k),
      simplexIntegral (refVertex n) (wedgeField ω η) = 0) : ω = 0 := by
  obtain ⟨⟨Ω, hΩ, rfl⟩, hbub⟩ := hω
  rw [eq_zero_of_isBubble_of_mem_polyFormMinus hr hΩ hbub fun h H hH => by
    rw [← simplexIntegral_wedgeField_evalForm]; exact hint h _ ⟨H, hH, rfl⟩, map_zero]

/-- `P̊_rΛᵏ(T̂) = 0` if `r + k ≤ n`. -/
theorem bubbleSpace_polySpace_eq_bot {r k : ℕ} (hr : 1 ≤ r) (h : r + k ≤ n) :
    bubbleSpace (refVertex n) (polySpace n r k) = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun ω hω =>
    eq_zero_of_mem_bubbleSpace_polySpace hr hω fun h' => absurd h' (by omega)

/-- `P̊_r⁻Λᵏ(T̂) = 0` if `r + k ≤ n`. -/
theorem bubbleSpace_polyMinusSpace_eq_bot {r k : ℕ} (hr : 1 ≤ r) (h : r + k ≤ n) :
    bubbleSpace (refVertex n) (polyMinusSpace n r k) = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun ω hω =>
    eq_zero_of_mem_bubbleSpace_polyMinusSpace hr hω fun h' => absurd h' (by omega)

/-! ### Mathlib simplices -/

/-- For a Mathlib `n`-simplex `T` in `ℝⁿ`: `P_rΛᵏ(T) = P_rΛᵏ(ℝⁿ)`. -/
theorem localPolySpace_simplex (T : Affine.Simplex ℝ (Fin n → ℝ) n) (r k : ℕ) :
    localPolySpace T.points r k = polySpace n r k :=
  localPolySpace_eq (isUnit_det_edgeMatrix T) r k

/-- For a Mathlib `n`-simplex `T` in `ℝⁿ`: `P_r⁻Λᵏ(T) = P_r⁻Λᵏ(ℝⁿ)`. -/
theorem localPolyMinusSpace_simplex (T : Affine.Simplex ℝ (Fin n → ℝ) n) (r k : ℕ) :
    localPolyMinusSpace T.points r k = polyMinusSpace n r k :=
  localPolyMinusSpace_eq (isUnit_det_edgeMatrix T) r k

/-- For a Mathlib `n`-simplex `T`: `tr_f P_rΛᵏ(T) = P_rΛᵏ(f)` on every face `f = T ∘ e`. -/
theorem map_faceTrace_localPolySpace_simplex (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    {e : Fin (m + 1) → Fin (n + 1)} (he : Function.Injective e) (r k : ℕ) :
    (localPolySpace T.points r k).map (faceTrace T.points e) = polySpace m r k := by
  rw [localPolySpace_simplex, map_faceTrace_polySpace (isUnit_det_edgeMatrix T) he]

/-- For a Mathlib `n`-simplex `T`: `tr_f P_r⁻Λᵏ(T) = P_r⁻Λᵏ(f)`. -/
theorem map_faceTrace_localPolyMinusSpace_simplex (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    {e : Fin (m + 1) → Fin (n + 1)} (he : Function.Injective e) (r k : ℕ) :
    (localPolyMinusSpace T.points r k).map (faceTrace T.points e) = polyMinusSpace m r k := by
  rw [localPolyMinusSpace_simplex, map_faceTrace_polyMinusSpace (isUnit_det_edgeMatrix T) he]

end Feec.FiniteElement
