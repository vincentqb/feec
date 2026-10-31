module

public import Feec.Algebra.SerendipityForm
public import Feec.Algebra.PolynomialFormDim
public import Mathlib.Algebra.MvPolynomial.Division

/-!
# The dimension of the serendipity forms

The shape functions `S_rΛᵏ = P_rΛᵏ + κ M_{r-1}Λ^{k+1} + d κ M_rΛᵏ` of [ArnoldAwanou2014]
(`Feec.Koszul.serendipityForm`) have the dimension of `M_rΛᵏ`, the span of the monomial `k`-forms
of superlinear degree `≤ r` ([ArnoldAwanou2014], Thm 3.6 (1) and (24)): the dimension is the
number of these monomials.

With `H_rΛᵏ` the part of `M_rΛᵏ` of polynomial degree `> r` (`Feec.Koszul.highForm`),
`M_rΛᵏ = P_rΛᵏ ⊕ H_rΛᵏ` and `S_rΛᵏ = P_rΛᵏ ⊕ κ H_{r-1}Λ^{k+1} ⊕ d κ H_rΛᵏ`. The key is the
**exactness of the Koszul complex at bounded superlinear degree**, `ker κ ∩ H_rΛᵏ = κ H_{r-1}Λ^{k+1}`
([ArnoldAwanou2014], Thm 2.3, due to Adams and Reiner), so that, `d` being injective on the range
of `κ`, `dim S_rΛᵏ = dim P_rΛᵏ + dim κ H_{r-1}Λ^{k+1} + dim κ H_rΛᵏ = dim P_rΛᵏ + dim H_rΛᵏ`.

## Main definitions

* `Feec.Koszul.monomialFilter P`, `Feec.Koszul.formFilter P`: the parts of a polynomial and of a
  polynomial form supported on the monomials satisfying `P`;
* `Feec.Koszul.formWeight s α`: the weight `α + 1_s` of `x^α dx_s`, preserved by `κ` and `d`;
* `Feec.Koszul.highForm R d r k`: `H_rΛᵏ`, the monomial `k`-forms of superlinear degree `≤ r` and
  degree `> r`.

## Main results

* `koszul_wedge_divMonomial`: a `κ`-closed form all of whose monomials contain `x_j` or `dx_j` is
  `κ (dx_j ∧ ω / x_j)` (Cartan's identity twice);
* `mem_map_koszul_highForm`: **`ker κ ∩ H_rΛᵏ = κ H_{r-1}Λ^{k+1}`** (`r ≥ 1`), over any commutative
  ring ([ArnoldAwanou2014], Thm 2.3): splitting along the weights, the superlinear variables first;
* `finrank_serendipityForm`: **`dim S_rΛᵏ = dim M_rΛᵏ`** (`r ≥ 1`) ([ArnoldAwanou2014], Thm 3.6).

## Implementation notes

The proof of exactness differs from [ArnoldAwanou2014], Lemma 2.4 (a canonical form of the forms
of linear degree `l - 1`): `κ` preserves the weight `α + 1_s`, so the part of a `κ`-closed form
whose weights are `≥ 2` (respectively `≥ 1`) in a direction `j` is again `κ`-closed, and is
`κ (dx_j ∧ ω / x_j)`, which lowers the superlinear degree (respectively keeps it `0`).

## References

* [D. N. Arnold, G. Awanou, *Finite element differential forms on cubical meshes*][ArnoldAwanou2014],
  §2 (Thm 2.3), §3 (Thm 3.6, (24))

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.Koszul

open ExteriorFibre

local infixl:70 " /ᵐ " => divMonomial
local infixl:70 " %ᵐ " => modMonomial

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d] [Fintype d]

/-! ### Monomial filters -/

section Filter

omit [LinearOrder d] [Fintype d]

open Classical in
/-- The part of a polynomial supported on the exponents satisfying `P`. -/
def monomialFilter (P : (d →₀ ℕ) → Prop) : MvPolynomial d R →ₗ[R] MvPolynomial d R :=
  (basisMonomials d R).constr R fun α => if P α then monomial α 1 else 0

open Classical in
theorem monomialFilter_monomial (P : (d →₀ ℕ) → Prop) (β : d →₀ ℕ) :
    monomialFilter P (monomial β (1 : R)) = if P β then monomial β 1 else 0 := by
  rw [monomialFilter, show monomial β (1 : R) = basisMonomials d R β from rfl,
    Module.Basis.constr_basis]
  rfl

theorem coeff_monomialFilter_of_pos {P : (d →₀ ℕ) → Prop} {α : d →₀ ℕ} (hα : P α)
    (p : MvPolynomial d R) : (monomialFilter P p).coeff α = p.coeff α := by
  classical
  have : lcoeff R α ∘ₗ monomialFilter P = lcoeff R α := (basisMonomials d R).ext fun β => by
    simp only [coe_basisMonomials, LinearMap.coe_comp, Function.comp_apply, monomialFilter_monomial,
      lcoeff_apply]
    split_ifs with hβ
    · rfl
    · simp [coeff_monomial, show β ≠ α from fun h => hβ (h ▸ hα)]
  exact LinearMap.congr_fun this p

theorem coeff_monomialFilter_of_neg {P : (d →₀ ℕ) → Prop} {α : d →₀ ℕ} (hα : ¬P α)
    (p : MvPolynomial d R) : (monomialFilter P p).coeff α = 0 := by
  classical
  have : lcoeff R α ∘ₗ monomialFilter P = 0 := (basisMonomials d R).ext fun β => by
    simp only [coe_basisMonomials, LinearMap.coe_comp, Function.comp_apply, monomialFilter_monomial,
      lcoeff_apply, LinearMap.zero_apply]
    split_ifs with hβ
    · simp [coeff_monomial, show β ≠ α from fun h => hα (h ▸ hβ)]
    · simp
  exact LinearMap.congr_fun this p

theorem monomialFilter_mem_restrictSupport {P : (d →₀ ℕ) → Prop} {S : Set (d →₀ ℕ)}
    {p : MvPolynomial d R} (hp : p ∈ restrictSupport R S) :
    monomialFilter P p ∈ restrictSupport R {α | α ∈ S ∧ P α} := by
  rw [mem_restrictSupport_iff] at hp ⊢
  intro α hα
  rw [Finset.mem_coe, mem_support_iff] at hα
  by_cases h : P α
  · rw [coeff_monomialFilter_of_pos h] at hα; exact ⟨hp (Finset.mem_coe.2 (mem_support_iff.2 hα)), h⟩
  · exact absurd (coeff_monomialFilter_of_neg h p) hα

theorem monomialFilter_add_monomialFilter_not (P : (d →₀ ℕ) → Prop) (p : MvPolynomial d R) :
    monomialFilter P p + monomialFilter (fun α => ¬P α) p = p := by
  classical
  have : monomialFilter P + monomialFilter (fun α => ¬P α) =
      (LinearMap.id : MvPolynomial d R →ₗ[R] _) :=
    (basisMonomials d R).ext fun β => by
      simp only [coe_basisMonomials, LinearMap.add_apply, monomialFilter_monomial, LinearMap.id_apply]
      by_cases h : P β <;> simp [h]
  exact LinearMap.congr_fun this p

theorem monomialFilter_X_mul [DecidableEq d] (P : (d →₀ ℕ) → Prop) (j : d) (p : MvPolynomial d R) :
    monomialFilter P (X j * p) = X j * monomialFilter (fun α => P (α + Finsupp.single j 1)) p := by
  ext α
  rw [coeff_X_mul']
  by_cases hj : j ∈ α.support
  · have : α - Finsupp.single j 1 + Finsupp.single j 1 = α := tsub_add_cancel_of_le
      (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hj)))
    rw [ite_eq_left hj]
    by_cases hP : P α
    · rw [coeff_monomialFilter_of_pos hP, coeff_monomialFilter_of_pos (P := fun α => P (α + _))
        (by rwa [this]), coeff_X_mul', ite_eq_left hj]
    · rw [coeff_monomialFilter_of_neg hP, coeff_monomialFilter_of_neg (P := fun α => P (α + _))
        (by rwa [this])]
  · rw [ite_eq_right hj]
    by_cases hP : P α
    · rw [coeff_monomialFilter_of_pos hP, coeff_X_mul', ite_eq_right hj]
    · rw [coeff_monomialFilter_of_neg hP]

end Filter

/-! ### Weights and filters of forms -/

/-- The part of a polynomial form whose monomial forms `x^α dx_s` satisfy `P s α`. -/
def formFilter (P : Finset d → (d →₀ ℕ) → Prop) (ω : PolyForm R d) : PolyForm R d :=
  fun s => monomialFilter (P s) (ω s)

omit [LinearOrder d] [Fintype d] in
theorem formFilter_add_formFilter_not (P : Finset d → (d →₀ ℕ) → Prop) (ω : PolyForm R d) :
    formFilter P ω + formFilter (fun s α => ¬P s α) ω = ω :=
  funext fun s => monomialFilter_add_monomialFilter_not (P s) (ω s)

omit [LinearOrder d] [Fintype d] in
theorem formFilter_mem_supportForm [DecidableEq d] (P : Finset d → (d →₀ ℕ) → Prop) {k : ℕ}
    {S : Finset d → Set (d →₀ ℕ)} {ω : PolyForm R d} (h : ω ∈ supportForm R d k S) :
    formFilter P ω ∈ supportForm R d k (fun s => {α | α ∈ S s ∧ P s α}) :=
  ⟨fun s hs => by simp [formFilter, h.1 s hs], fun s => monomialFilter_mem_restrictSupport (h.2 s)⟩

/-- The weight `α + 1_s` of the monomial form `x^α dx_s`: `κ` and `d` move a unit between `α` and
`1_s`. -/
def formWeight (s : Finset d) (α : d →₀ ℕ) (i : d) : ℕ := α i + if i ∈ s then 1 else 0

omit [Fintype d] in
theorem formWeight_add_single {s : Finset d} {j : d} (hj : j ∉ s) (α : d →₀ ℕ) :
    formWeight s (α + Finsupp.single j 1) = formWeight (insert j s) α := funext fun i => by
  by_cases hi : i = j
  · subst hi; simp [formWeight, hj]
  · simp [formWeight, hi]

omit [Fintype d] in
theorem formWeight_sub_single {s : Finset d} {j : d} (hj : j ∈ s) {α : d →₀ ℕ} (hα : 1 ≤ α j) :
    formWeight s (α - Finsupp.single j 1) = formWeight (s.erase j) α := funext fun i => by
  by_cases hi : i = j
  · subst hi; simp [formWeight, hj]; omega
  · simp [formWeight, hi]

/-- **The filters by weight commute with `κ`**. -/
theorem koszul_formFilter_formWeight (Q : (d → ℕ) → Prop) (ω : PolyForm R d) :
    koszul (formFilter (fun s α => Q (formWeight s α)) ω) =
      formFilter (fun s α => Q (formWeight s α)) (koszul ω) := by
  funext s
  simp only [koszul_apply, formFilter, map_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [mul_assoc, mul_assoc, map_sgn_mul, monomialFilter_X_mul]
  simp_rw [formWeight_add_single (mem_compl.1 hj)]

theorem koszul_formFilter_formWeight_eq_zero (Q : (d → ℕ) → Prop) {ω : PolyForm R d}
    (h : koszul ω = 0) : koszul (formFilter (fun s α => Q (formWeight s α)) ω) = 0 := by
  rw [koszul_formFilter_formWeight, h]
  funext s
  simp [formFilter]

/-! ### Contraction along a direction -/

omit [LinearOrder d] [Fintype d] in
theorem divMonomial_X_mul_of_ne [DecidableEq d] {u j : d} (h : j ≠ u) (p : MvPolynomial d R) :
    X j * p /ᵐ Finsupp.single u 1 = X j * (p /ᵐ Finsupp.single u 1) := by
  ext α
  rw [coeff_divMonomial, coeff_X_mul', coeff_X_mul', coeff_divMonomial]
  have hs : j ∈ (Finsupp.single u 1 + α).support ↔ j ∈ α.support := by
    simp [Ne.symm h]
  by_cases hj : j ∈ α.support
  · rw [ite_eq_left (hs.2 hj), ite_eq_left hj]
    congr 1
    ext i
    by_cases hi : i = j
    · subst hi; simp [h]
    · by_cases hiu : i = u
      · subst hiu; simp [hi]
      · simp [hi, hiu]
  · rw [ite_eq_right (fun h' => hj (hs.1 h')), ite_eq_right hj]

omit [LinearOrder d] [Fintype d] in
theorem divMonomial_C_mul (a : R) (p : MvPolynomial d R) (s : d →₀ ℕ) :
    C a * p /ᵐ s = C a * (p /ᵐ s) := by
  ext α; simp [coeff_C_mul]

omit [LinearOrder d] [Fintype d] in
theorem sum_divMonomial {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial d R) (s : d →₀ ℕ) :
    (∑ i ∈ t, f i) /ᵐ s = ∑ i ∈ t, f i /ᵐ s := by
  ext α; simp

/-- Dividing `κω` by `x_u`: `(κω) / x_u = κ (ω / x_u) + ι_{e_u} (ω mod x_u)`. -/
theorem divMonomial_koszul (u : d) (ω : PolyForm R d) :
    (fun s => koszul ω s /ᵐ Finsupp.single u 1) =
      koszul (fun s => ω s /ᵐ Finsupp.single u 1) +
        interior (Pi.single u 1) (fun s => ω s %ᵐ Finsupp.single u 1) := by
  funext s
  simp only [Pi.add_apply, koszul_apply, interior_apply, sum_divMonomial, ← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  have hsgn : (sgn j s : MvPolynomial d R) = C (sgn j s) := by simp [sgn]
  by_cases hju : j = u
  · subst hju
    rw [mul_assoc, hsgn, divMonomial_C_mul, X_mul_divMonomial, Pi.single_eq_same, mul_one,
      mul_assoc, ← mul_add, divMonomial_add_modMonomial_single]
  · rw [mul_assoc, hsgn, divMonomial_C_mul, divMonomial_X_mul_of_ne hju, Pi.single_eq_of_ne hju,
      mul_zero, zero_mul, add_zero, mul_assoc]

/-- **Contraction along `x_u`**: a `κ`-closed form `θ` whose coefficients `θ_t`, `u ∉ t`, are
divisible by `x_u` (every monomial form contains `x_u` or `dx_u`) is `κ (dx_u ∧ θ / x_u)`:
Cartan's identity `κ (dx_u ∧ η) + dx_u ∧ κη = x_u η` for `η = θ / x_u`, and
`dx_u ∧ ι_{e_u} ρ = ρ` for the remainder `ρ = θ mod x_u`, `κ η = -ι_{e_u} ρ` by
`divMonomial_koszul`. -/
theorem koszul_wedge_divMonomial (u : d) {θ : PolyForm R d} (hκ : koszul θ = 0)
    (hθ : ∀ t, u ∉ t → θ t %ᵐ Finsupp.single u 1 = 0) :
    koszul (wedge (Pi.single u 1) (fun s => θ s /ᵐ Finsupp.single u 1)) = θ := by
  set η : PolyForm R d := fun s => θ s /ᵐ Finsupp.single u 1
  set ρ : PolyForm R d := fun s => θ s %ᵐ Finsupp.single u 1
  have hθηρ : θ = (X u : MvPolynomial d R) • η + ρ := funext fun s => by
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (divMonomial_add_modMonomial_single (θ s) u).symm
  -- `κ η = - ι_{e_u} ρ`
  have h1 : koszul η + interior (Pi.single u 1) ρ = 0 := by
    rw [← divMonomial_koszul, hκ]
    funext s; simp [divMonomial]
  -- `dx_u ∧ ρ = 0`
  have h2 : wedge (Pi.single u 1 : d → MvPolynomial d R) ρ = 0 := by
    funext t
    rw [wedge_apply, Pi.zero_apply]
    refine sum_eq_zero fun j hj => ?_
    by_cases hju : j = u
    · subst hju; rw [show ρ (t.erase j) = 0 from hθ _ (notMem_erase j t), mul_zero]
    · rw [Pi.single_eq_of_ne hju, mul_zero, zero_mul]
  have hC1 := wedge_interior_add_interior_wedge (Pi.single u 1) (fun j => (X j : MvPolynomial d R)) η
  have hC2 := wedge_interior_add_interior_wedge (Pi.single u 1) (Pi.single u 1) ρ
  rw [h2, show interior (Pi.single u 1 : d → MvPolynomial d R) 0 = 0 by
    funext s; simp [interior_apply], add_zero] at hC2
  have hs1 : (∑ j, (Pi.single u 1 : d → MvPolynomial d R) j * X j) = (X u : MvPolynomial d R) := by
    simp [Pi.single_apply]
  have hs2 : (∑ j, (Pi.single u 1 : d → MvPolynomial d R) j * (Pi.single u 1 : d → MvPolynomial d R) j) = 1 := by
    simp [Pi.single_apply]
  rw [hs1] at hC1
  rw [hs2, one_smul] at hC2
  have hκη : koszul η = -interior (Pi.single u 1) ρ := eq_neg_of_add_eq_zero_left h1
  change wedge _ (koszul η) + koszul _ = _ at hC1
  rw [hκη, show wedge (Pi.single u 1 : d → MvPolynomial d R) (-interior (Pi.single u 1) ρ) =
    -wedge (Pi.single u 1) (interior (Pi.single u 1) ρ) by
      funext t; simp [wedge_apply, mul_neg, sum_neg_distrib], hC2] at hC1
  rw [hθηρ, ← hC1]
  abel

/-! ### Exactness of `κ` at bounded superlinear degree -/

/-- The exponents of `x^α dx_s` of superlinear degree `≤ r` and degree `> r`. -/
def highSupport (r : ℕ) (s : Finset d) : Set (d →₀ ℕ) :=
  {α | superlinDeg s α ≤ r ∧ r < α.degree}

variable (R d) in
/-- `H_rΛᵏ`: the span of the monomial `k`-forms of superlinear degree `≤ r` and degree `> r`, the
part of `M_rΛᵏ` beyond `P_rΛᵏ` ([ArnoldAwanou2014], Prop 3.1: `Σ_{l ≥ 1} H_{r+l,l}Λᵏ`). -/
def highForm (r k : ℕ) : Submodule R (PolyForm R d) := supportForm R d k (highSupport r)

theorem highForm_le_superlinForm (r k : ℕ) : highForm R d r k ≤ superlinForm R d r k :=
  supportForm_mono (S := highSupport r) (T := superlinSupport r) (fun _ _ hα => hα.1) k

omit [LinearOrder d] [Fintype d] in
theorem degree_sub_single_add_one {α : d →₀ ℕ} {j : d} (hj : 1 ≤ α j) :
    (α - Finsupp.single j 1).degree + 1 = α.degree := by
  conv_rhs => rw [← tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hj)]
  rw [map_add, Finsupp.degree_single]

/-- `κ H_{r-1}Λ^{k+1} ⊆ H_rΛᵏ` (`r ≥ 1`). -/
theorem koszul_mem_highForm {r k : ℕ} (hr : 1 ≤ r) {ω : PolyForm R d}
    (h : ω ∈ highForm R d (r - 1) (k + 1)) : koszul ω ∈ highForm R d r k := by
  refine ⟨IsDeg.koszul h.1, fun s => Submodule.sum_mem _ fun j hj => ?_⟩
  rw [mul_assoc]
  refine sgn_mul_mem j s (X_mul_mem_restrictSupport (S := highSupport (r - 1) (insert j s))
    (T := highSupport r s) j (fun α hα => ⟨?_, ?_⟩) (h.2 _))
  · exact (superlinDeg_add_single_le (mem_compl.1 hj) α).trans (by have := hα.1; omega)
  · rw [map_add, Finsupp.degree_single]; have := hα.2; omega

omit [LinearOrder d] [Fintype d] in
/-- A polynomial all of whose monomials contain `x_u` is divisible by `x_u`. -/
theorem modMonomial_eq_zero {p : MvPolynomial d R} {u : d} {S : Set (d →₀ ℕ)}
    (hp : p ∈ restrictSupport R S) (hS : ∀ α ∈ S, 1 ≤ α u) : p %ᵐ Finsupp.single u 1 = 0 := by
  ext α
  rw [show (0 : MvPolynomial d R).coeff α = 0 from rfl]
  by_cases h : Finsupp.single u 1 ≤ α
  · exact coeff_modMonomial_of_le _ h
  · rw [coeff_modMonomial_of_not_le _ h]
    by_contra h0
    exact h (Finsupp.single_le_iff.2 (hS α ((mem_restrictSupport_iff R).1 hp (mem_support_iff.2 h0))))

omit [Fintype d] in
/-- The support of `dx_u ∧ θ / x_u`. -/
theorem wedge_divMonomial_mem_supportForm (u : d) {k : ℕ} {S T : Finset d → Set (d →₀ ℕ)}
    {θ : PolyForm R d} (h : θ ∈ supportForm R d k S)
    (hST : ∀ t, u ∈ t → ∀ α ∈ S (t.erase u), 1 ≤ α u → α - Finsupp.single u 1 ∈ T t) :
    wedge (Pi.single u 1) (fun s => θ s /ᵐ Finsupp.single u 1) ∈ supportForm R d (k + 1) T := by
  refine ⟨IsDeg.wedge (fun s hs => by rw [h.1 s hs]; ext; simp) _, fun t => ?_⟩
  rw [wedge_apply]
  refine Submodule.sum_mem _ fun j hj => ?_
  by_cases hju : j = u
  · subst hju
    rw [Pi.single_eq_same, mul_one]
    refine sgn_mul_mem j t ((mem_restrictSupport_iff R).2 fun β hβ => ?_)
    rw [Finset.mem_coe, mem_support_iff, coeff_divMonomial] at hβ
    have hα := (mem_restrictSupport_iff R).1 (h.2 (t.erase j)) (mem_support_iff.2 hβ)
    have h1 : 1 ≤ (Finsupp.single j 1 + β : d →₀ ℕ) j := by simp
    simpa using hST t hj _ hα h1
  · rw [Pi.single_eq_of_ne hju, mul_zero, zero_mul]; exact Submodule.zero_mem _

/-- The second phase of the exactness proof: weights `≤ 1`, vanishing outside `T`. -/
theorem mem_map_koszul_highForm_of_formWeight_le_one {r : ℕ} (hr : 1 ≤ r) {k : ℕ} (T : Finset d) :
    ∀ θ ∈ supportForm R d k (fun s => {α | α ∈ highSupport r s ∧ (∀ i, formWeight s α i ≤ 1) ∧
        ∀ i ∉ T, formWeight s α i = 0}), koszul θ = 0 →
      θ ∈ (highForm R d (r - 1) (k + 1)).map (koszulₗ R d) := by
  induction T using Finset.induction_on with
  | empty =>
    intro θ hθ _
    -- every weight vanishes: `θ` would be a constant `0`-form of degree `> r`
    suffices θ = 0 by rw [this]; exact Submodule.zero_mem _
    funext s
    have hS : {α | α ∈ highSupport r s ∧ (∀ i, formWeight s α i ≤ 1) ∧
        ∀ i ∉ (∅ : Finset d), formWeight s α i = 0} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun α hα => ?_
      obtain ⟨⟨-, hdeg⟩, -, h0⟩ := hα
      have : α = 0 := Finsupp.ext fun i => by
        have := h0 i (notMem_empty i); simp only [formWeight] at this; simp; omega
      subst this; simp at hdeg
    have h0 : θ s ∈ restrictSupport R (∅ : Set (d →₀ ℕ)) := hS ▸ hθ.2 s
    show θ s = 0
    exact support_eq_empty.1 (Finset.coe_eq_empty.1
      (Set.subset_empty_iff.1 ((mem_restrictSupport_iff R).1 h0)))
  | insert u T hu ih =>
    intro θ hθ hκ
    rw [← formFilter_add_formFilter_not (fun s α => 1 ≤ formWeight s α u) θ]
    refine Submodule.add_mem _ ?_ (ih _ ?_ ?_)
    · -- the part with `x_u` or `dx_u`
      have hθ₁ := formFilter_mem_supportForm (fun s α => 1 ≤ formWeight s α u) hθ
      refine ⟨_, wedge_divMonomial_mem_supportForm u hθ₁ fun t ht α hα hαu => ⟨?_, ?_⟩,
        koszul_wedge_divMonomial u (koszul_formFilter_formWeight_eq_zero (fun w => 1 ≤ w u) hκ)
          fun t hut => modMonomial_eq_zero (hθ₁.2 t) fun α hα => by
            simpa [formWeight, hut] using hα.2⟩
      · rw [superlinDeg_eq_zero fun i => by
          change formWeight t (α - Finsupp.single u 1) i ≤ 1
          rw [formWeight_sub_single ht hαu]
          exact hα.1.2.1 i]
        exact Nat.zero_le _
      · have := degree_sub_single_add_one hαu; have := hα.1.1.2; omega
    · refine supportForm_mono ?_ k (formFilter_mem_supportForm _ hθ)
      intro s α hα
      refine ⟨hα.1.1, hα.1.2.1, fun i hi => ?_⟩
      by_cases hiu : i = u
      · subst hiu; have := hα.2; omega
      · exact hα.1.2.2 i (by simp [hiu, hi])
    · exact koszul_formFilter_formWeight_eq_zero (fun w => ¬1 ≤ w u) hκ

/-- The first phase of the exactness proof: weights `≤ 1` outside `T`. -/
theorem mem_map_koszul_highForm_of_formWeight {r : ℕ} (hr : 1 ≤ r) {k : ℕ} (T : Finset d) :
    ∀ θ ∈ supportForm R d k (fun s => {α | α ∈ highSupport r s ∧ ∀ i ∉ T, formWeight s α i ≤ 1}),
      koszul θ = 0 → θ ∈ (highForm R d (r - 1) (k + 1)).map (koszulₗ R d) := by
  induction T using Finset.induction_on with
  | empty =>
    intro θ hθ hκ
    refine mem_map_koszul_highForm_of_formWeight_le_one hr univ θ (supportForm_mono ?_ k hθ) hκ
    intro s α hα
    exact ⟨hα.1, fun i => hα.2 i (notMem_empty i), fun i hi => absurd (mem_univ i) hi⟩
  | insert u T hu ih =>
    intro θ hθ hκ
    rw [← formFilter_add_formFilter_not (fun s α => 2 ≤ formWeight s α u) θ]
    refine Submodule.add_mem _ ?_ (ih _ ?_ ?_)
    · -- the part superlinear in `u`: `dx_u ∧ θ / x_u` has a lower superlinear degree
      have hθ₁ := formFilter_mem_supportForm (fun s α => 2 ≤ formWeight s α u) hθ
      refine ⟨_, wedge_divMonomial_mem_supportForm u hθ₁ fun t ht α hα hαu => ⟨?_, ?_⟩,
        koszul_wedge_divMonomial u (koszul_formFilter_formWeight_eq_zero (fun w => 2 ≤ w u) hκ)
          fun t hut => modMonomial_eq_zero (hθ₁.2 t) fun α hα => by
            have := hα.2; simp [formWeight, hut] at this; omega⟩
      · have h2 : 2 ≤ α u := by have := hα.2; simpa [formWeight] using this
        have := superlinDeg_sub_single_add_one ht h2
        have := hα.1.1.1
        omega
      · have := degree_sub_single_add_one hαu; have := hα.1.1.2; omega
    · refine supportForm_mono ?_ k (formFilter_mem_supportForm _ hθ)
      intro s α hα
      refine ⟨hα.1.1, fun i hi => ?_⟩
      by_cases hiu : i = u
      · subst hiu; have := hα.2; omega
      · exact hα.1.2 i (by simp [hiu, hi])
    · exact koszul_formFilter_formWeight_eq_zero (fun w => ¬2 ≤ w u) hκ

/-- **Exactness of the Koszul complex at bounded superlinear degree**: for `r ≥ 1`, a `κ`-closed
form of `H_rΛᵏ` is `κ` of a form of `H_{r-1}Λ^{k+1}`, over any commutative ring.
[ArnoldAwanou2014], Thm 2.3 -/
theorem mem_map_koszul_highForm {r k : ℕ} (hr : 1 ≤ r) {θ : PolyForm R d}
    (h : θ ∈ highForm R d r k) (hκ : koszul θ = 0) :
    θ ∈ (highForm R d (r - 1) (k + 1)).map (koszulₗ R d) :=
  mem_map_koszul_highForm_of_formWeight hr univ θ
    (supportForm_mono (S := highSupport r)
      (T := fun s => {α | α ∈ highSupport r s ∧ ∀ i ∉ (univ : Finset d), formWeight s α i ≤ 1})
      (fun _ _ hα => ⟨hα, fun i hi => absurd (mem_univ i) hi⟩) k h) hκ

/-! ### Sums of monomial spaces -/

section Sums

omit [LinearOrder d] [Fintype d]
variable [DecidableEq d]

omit [DecidableEq d] in
theorem supportForm_inf (k : ℕ) (S T : Finset d → Set (d →₀ ℕ)) :
    supportForm R d k S ⊓ supportForm R d k T = supportForm R d k (fun s => S s ∩ T s) := by
  ext ω
  refine ⟨fun ⟨h, h'⟩ => ⟨h.1, fun s => ?_⟩, fun h => ⟨⟨h.1, fun s => ?_⟩, ⟨h.1, fun s => ?_⟩⟩⟩
  · exact (mem_restrictSupport_iff R).2 (Set.subset_inter ((mem_restrictSupport_iff R).1 (h.2 s))
      ((mem_restrictSupport_iff R).1 (h'.2 s)))
  · exact restrictSupport_mono R Set.inter_subset_left (h.2 s)
  · exact restrictSupport_mono R Set.inter_subset_right (h.2 s)

omit [DecidableEq d] in
/-- Monomial spaces on disjoint supports are independent. -/
theorem disjoint_supportForm {k : ℕ} {S T : Finset d → Set (d →₀ ℕ)}
    (h : ∀ s, Disjoint (S s) (T s)) : Disjoint (supportForm R d k S) (supportForm R d k T) := by
  rw [disjoint_iff, supportForm_inf, eq_bot_iff]
  intro ω hω
  refine (Submodule.mem_bot R).2 (funext fun s => ?_)
  have : ↑(ω s).support ⊆ S s ∩ T s := (mem_restrictSupport_iff R).1 (hω.2 s)
  rw [(h s).inter_eq] at this
  exact support_eq_empty.1 (Finset.coe_eq_empty.1 (Set.subset_empty_iff.1 this))

/-- The monomial space on a union is the sum. -/
theorem supportForm_union (k : ℕ) (S T : Finset d → Set (d →₀ ℕ)) :
    supportForm R d k (fun s => S s ∪ T s) = supportForm R d k S ⊔ supportForm R d k T := by
  refine le_antisymm (fun ω hω => ?_) (sup_le (supportForm_mono (fun _ => Set.subset_union_left) k)
    (supportForm_mono (fun _ => Set.subset_union_right) k))
  rw [← formFilter_add_formFilter_not (fun s α => α ∈ S s) ω]
  refine Submodule.add_mem_sup (supportForm_mono
    (S := fun s => {α | α ∈ S s ∪ T s ∧ α ∈ S s}) (T := S) (fun _ _ hα => hα.2) k
    (formFilter_mem_supportForm _ hω)) (supportForm_mono
      (S := fun s => {α | α ∈ S s ∪ T s ∧ ¬α ∈ S s}) (T := T) (fun s α hα => ?_) k
      (formFilter_mem_supportForm _ hω))
  exact hα.1.resolve_left hα.2

end Sums

omit [LinearOrder d] [Fintype d] in
/-- `P_rΛᵏ` is the monomial space of the exponents of degree `≤ r`. -/
theorem polyForm_eq_supportForm (r k : ℕ) :
    polyForm R d r k = supportForm R d k (fun _ => {α | α.degree ≤ r}) := by
  ext ω
  exact and_congr_right fun _ => forall_congr' fun s =>
    (mem_restrictTotalDegree d (m := r) (ω s)).symm


/-! ### The decompositions of `M_rΛᵏ` and `S_rΛᵏ` -/

/-- **`M_rΛᵏ = P_rΛᵏ ⊕ H_rΛᵏ`** (with `disjoint_polyForm_highForm`). -/
theorem polyForm_sup_highForm (r k : ℕ) :
    polyForm R d r k ⊔ highForm R d r k = superlinForm R d r k := by
  rw [polyForm_eq_supportForm, highForm, ← supportForm_union, superlinForm]
  congr 1
  funext s
  ext α
  simp only [highSupport, superlinSupport, Set.mem_union, Set.mem_ofPred_eq]
  have := superlinDeg_le s α
  have : (α.sum fun _ e => e) = α.degree := rfl
  constructor
  · rintro (h | h) <;> [omega; exact h.1]
  · intro h; by_cases h' : α.degree ≤ r
    · exact Or.inl h'
    · exact Or.inr ⟨h, by omega⟩

theorem disjoint_polyForm_highForm (r k : ℕ) :
    Disjoint (polyForm R d r k) (highForm R d r k) := by
  rw [polyForm_eq_supportForm, highForm]
  exact disjoint_supportForm fun s => Set.disjoint_left.2 fun α h h' => by
    have := h'.2; simp only [Set.mem_ofPred_eq] at h; omega

/-- The forms all of whose monomials have degree `> m`. -/
theorem koszul_mem_supportForm_degree {m k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ supportForm R d (k + 1) (fun _ => {α | m < α.degree})) :
    koszul ω ∈ supportForm R d k (fun _ => {α | m + 1 < α.degree}) := by
  refine ⟨IsDeg.koszul h.1, fun s => Submodule.sum_mem _ fun j _ => ?_⟩
  rw [mul_assoc]
  refine sgn_mul_mem j s (X_mul_mem_restrictSupport (S := {α | m < α.degree})
    (T := {α | m + 1 < α.degree}) j (fun α hα => ?_) (h.2 _))
  simp only [Set.mem_ofPred_eq, map_add, Finsupp.degree_single] at hα ⊢
  omega

omit [Fintype d] in
theorem extDeriv_mem_supportForm_degree {m k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ supportForm R d k (fun _ => {α | m + 1 < α.degree})) :
    extDeriv ω ∈ supportForm R d (k + 1) (fun _ => {α | m < α.degree}) :=
  ⟨IsDeg.extDeriv h.1, fun s => Submodule.sum_mem _ fun j _ => sgn_mul_mem j s
    (pderiv_mem_restrictSupport j (fun α (hα : m + 1 < α.degree) hj => show m < _ by
      have := degree_sub_single_add_one (Nat.one_le_iff_ne_zero.2 hj); omega) (h.2 _))⟩

/-- **`S_rΛᵏ = P_rΛᵏ + κ H_{r-1}Λ^{k+1} + d κ H_rΛᵏ`** (`r ≥ 1`): the parts of degree `≤ r` of
`κ M_{r-1}Λ^{k+1}` and `d κ M_rΛᵏ` lie in `P_rΛᵏ`. -/
theorem serendipityForm_eq_sup {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    serendipityForm R d r k = polyForm R d r k ⊔
      ((highForm R d (r - 1) (k + 1)).map (koszulₗ R d) ⊔
        ((highForm R d r k).map (koszulₗ R d)).map (extDerivₗ R d)) := by
  refine le_antisymm (fun ω h => serendipityForm_induction ?_ ?_ ?_ (fun _ _ => add_mem) h) ?_
  · exact fun ω hω => Submodule.mem_sup_left hω
  · rintro r' rfl a ha
    rw [Nat.add_sub_cancel]
    rw [← polyForm_sup_highForm] at ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.1 ha
    rw [koszul_add]
    refine add_mem (Submodule.mem_sup_left ?_)
      (Submodule.mem_sup_right (Submodule.mem_sup_left (Submodule.mem_map_of_mem ha₂)))
    simpa using koszul_mem_polyForm ha₁
  · intro b hb
    rw [← polyForm_sup_highForm] at hb
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.1 hb
    rw [koszul_add, extDeriv_add]
    refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right
      (Submodule.mem_sup_right (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hb₂))))
    cases k with
    | zero => rw [IsDeg.koszul_eq_zero hb₁.1, extDeriv_zero]; exact Submodule.zero_mem _
    | succ k => simpa using extDeriv_mem_polyForm (koszul_mem_polyForm hb₁)
  · refine sup_le (polyForm_le_serendipityForm r k) (sup_le ?_ ?_)
    · rintro _ ⟨a, ha, rfl⟩
      simpa [Nat.sub_add_cancel hr] using koszul_mem_serendipityForm (highForm_le_superlinForm _ _ ha)
    · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact extDeriv_koszul_mem_serendipityForm (highForm_le_superlinForm _ _ hb)

/-- The forms of `κ H_{r-1}Λ^{k+1} + d κ H_rΛᵏ` have only monomials of degree `> r`. -/
theorem sup_le_supportForm_degree {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    (highForm R d (r - 1) (k + 1)).map (koszulₗ R d) ⊔
        ((highForm R d r k).map (koszulₗ R d)).map (extDerivₗ R d) ≤
      supportForm R d k (fun _ => {α | r < α.degree}) := by
  refine sup_le ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact supportForm_mono (S := highSupport r) (fun _ _ hα => hα.2) k (koszul_mem_highForm hr ha)
  · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    cases k with
    | zero =>
      change extDeriv (koszul b) ∈ _
      rw [IsDeg.koszul_eq_zero hb.1, extDeriv_zero]; exact Submodule.zero_mem _
    | succ k =>
      exact extDeriv_mem_supportForm_degree (koszul_mem_supportForm_degree
        (supportForm_mono (S := highSupport r) (fun _ _ hα => hα.2) _ hb))

/-! ### Homogeneous components of `κ` -/

theorem homComp_koszul (j : ℕ) (ω : PolyForm R d) :
    homComp (j + 1) (koszul ω) = koszul (homComp j ω) := by
  funext s
  simp only [homComp_apply, koszul_apply, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show (sgn i s : MvPolynomial d R) = C (sgn i s) by simp [sgn], mul_assoc, mul_assoc,
    homogeneousComponent_C_mul]
  congr 1
  ext α
  rw [coeff_homogeneousComponent, coeff_X_mul', coeff_X_mul', coeff_homogeneousComponent]
  by_cases hi : i ∈ α.support
  · rw [ite_eq_left hi, ite_eq_left hi]
    have := degree_sub_single_add_one (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi))
    by_cases hd : α.degree = j + 1
    · rw [ite_eq_left hd, ite_eq_left (by omega)]
    · rw [ite_eq_right hd, ite_eq_right (by omega)]
  · rw [ite_eq_right hi]; split_ifs <;> rfl

theorem homComp_zero_koszul (ω : PolyForm R d) : homComp 0 (koszul ω) = 0 := by
  funext s
  ext α
  rw [homComp_apply, coeff_homogeneousComponent, Pi.zero_apply]
  split_ifs with hα
  · obtain rfl : α = 0 := (Finsupp.degree_eq_zero_iff α).1 hα
    rw [koszul_apply, coeff_sum]
    refine sum_eq_zero fun j _ => ?_
    rw [show (sgn j s : MvPolynomial d R) = C (sgn j s) by simp [sgn], mul_assoc, coeff_C_mul,
      coeff_X_mul']
    simp
  · rfl

/-! ### Dimension (characteristic zero) -/

section Dim

variable {K : Type*} [Field K] [CharZero K]

instance (r k : ℕ) : FiniteDimensional K (highForm K d r k) :=
  Submodule.finiteDimensional_of_le (highForm_le_superlinForm r k)

omit [CharZero K] in
/-- Rank–nullity for `κ` on `H_rΛᵏ`, with the kernel given by exactness:
`dim H_rΛᵏ = dim κ H_rΛᵏ + dim κ H_{r-1}Λ^{k+1}`. -/
theorem finrank_highForm {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    Module.finrank K (highForm K d r k) =
      Module.finrank K ((highForm K d r k).map (koszulₗ K d)) +
        Module.finrank K ((highForm K d (r - 1) (k + 1)).map (koszulₗ K d)) := by
  set f := koszulₗ K d ∘ₗ (highForm K d r k).subtype
  have hrange : LinearMap.range f = (highForm K d r k).map (koszulₗ K d) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : (LinearMap.ker f).map (highForm K d r k).subtype =
      (highForm K d (r - 1) (k + 1)).map (koszulₗ K d) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_map_koszul_highForm hr x.2 hx
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨⟨_, koszul_mem_highForm hr ha⟩, by
        simp [f, LinearMap.mem_ker, koszulₗ, koszul_koszul], rfl⟩
  rw [← LinearMap.finrank_range_add_finrank_ker f, hrange, ← hker,
    Submodule.finrank_map_subtype_eq]

/-- **The dimension of the serendipity forms** ([ArnoldAwanou2014], Thm 3.6 (1)): for `r ≥ 1`,
`dim S_rΛᵏ = dim M_rΛᵏ`, the number of monomial `k`-forms of superlinear degree `≤ r`
(`finrank_superlinForm`). -/
theorem finrank_serendipityForm {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    Module.finrank K (serendipityForm K d r k) = Module.finrank K (superlinForm K d r k) := by
  set A := (highForm K d (r - 1) (k + 1)).map (koszulₗ K d)
  set B := ((highForm K d r k).map (koszulₗ K d)).map (extDerivₗ K d)
  have hAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨a, -, rfl⟩, ⟨_, ⟨b, -, rfl⟩, hb⟩⟩
    refine (Submodule.mem_bot K).2 (koszul_eq_zero_of_extDeriv_koszul_eq_zero ?_)
    change extDeriv (koszul b) = koszul a at hb
    rw [← hb, extDeriv_extDeriv]
  have hPAB : polyForm K d r k ⊓ (A ⊔ B) = ⊥ := by
    refine eq_bot_iff.2 ((inf_le_inf_left _ (sup_le_supportForm_degree hr k)).trans ?_)
    rw [polyForm_eq_supportForm, ← disjoint_iff.1 (disjoint_supportForm (R := K) (k := k)
      (S := fun _ => {α : d →₀ ℕ | α.degree ≤ r}) (T := fun _ => {α | r < α.degree})
      fun _ => Set.disjoint_left.2 fun α h h' => by simp only [Set.mem_ofPred_eq] at h h'; omega)]
  have hB : Module.finrank K B = Module.finrank K ((highForm K d r k).map (koszulₗ K d)) :=
    finrank_map_of_injOn _ _ fun x ⟨b, _, hb⟩ hd => by
      subst hb; exact koszul_eq_zero_of_extDeriv_koszul_eq_zero hd
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (polyForm K d r k) (A ⊔ B)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq A B
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (polyForm K d r k) (highForm K d r k)
  rw [hPAB, finrank_bot, add_zero] at h1
  rw [hAB, finrank_bot, add_zero] at h2
  rw [(disjoint_polyForm_highForm r k).eq_bot, finrank_bot, add_zero, polyForm_sup_highForm] at h3
  rw [serendipityForm_eq_sup hr, h1, h2, hB, h3, finrank_highForm hr k]
  ring

end Dim

end Feec.Koszul
