module

public import Feec.Algebra.PolynomialForm
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Fintype.Powerset

/-!
# Dimensions, direct sums and exact sequences of polynomial form spaces

For polynomial differential forms on `K^d` (`Feec.Koszul.PolyForm`, `d` a finite linearly ordered
index type with `n = #d`) over a field `K`, this file completes the algebra of the spaces
`H_rΛᵏ = homForm r k`, `P_rΛᵏ = polyForm r k` and `P_r⁻Λᵏ = polyFormMinus r k` of
`Feec.Algebra.PolynomialForm`: finite-dimensionality, the direct sum decompositions, their
dimensions and the exactness of the two polynomial de Rham complexes ([AFW2006], §3;
[AFW2010], §5.1; [Arnold2018], Ch. 7).

The homogeneous components `homComp j ω` of a polynomial form (coefficientwise
`MvPolynomial.homogeneousComponent`) commute with `d` and `κ` up to the degree shift
(`homComp_extDeriv`, `homComp_koszul`), which reduces everything to the homogeneous homotopy
formula `(dκ + κd) ω = (r + k) ω` on `H_rΛᵏ`.

## Main results

Over any field:

* `finrank_homForm`: `dim H_rΛᵏ = (n choose k) (n + r - 1 choose r)`;
* `polyForm_sup_homForm`, `disjoint_polyForm_homForm`: `P_{r+1}Λᵏ = P_rΛᵏ ⊕ H_{r+1}Λᵏ`
  (and `P_0Λᵏ = H_0Λᵏ`, `polyForm_zero_eq_homForm`);
* `finrank_polyForm`: `dim P_rΛᵏ = (r + n choose r + k) (r + k choose k)`;
* `polyFormMinus_succ`, `disjoint_polyForm_map_koszul`:
  `P_{r+1}⁻Λᵏ = P_rΛᵏ ⊕ κ H_rΛ^{k+1}`;
* finite-dimensionality instances for `homForm`, `polyForm`, `polyFormMinus`.

In characteristic zero:

* `map_koszul_sup_map_extDeriv`, `disjoint_map_koszul_map_extDeriv`: the Koszul decomposition
  `H_{r+1}Λ^{k+1} = κ H_rΛ^{k+2} ⊕ d H_{r+2}Λᵏ`, and `map_koszul_homForm_one`:
  `H_{r+1}Λ⁰ = κ H_rΛ¹`;
* `finrank_map_koszul_homForm`, `finrank_map_extDeriv_homForm'`:
  `dim κ H_rΛ^{k+1} = dim d H_{r+1}Λᵏ = (n + r choose r + k + 1) (r + k choose k)`
  ([AFW2010], Thm 5.3);
* `polyFormMinus_sup_map_extDeriv`, `disjoint_polyFormMinus_map_extDeriv`:
  `P_rΛ^{k+1} = P_r⁻Λ^{k+1} ⊕ d H_{r+1}Λᵏ` (`r ≥ 1`), and `polyFormMinus_zero`:
  `P_r⁻Λ⁰ = P_rΛ⁰`;
* `finrank_polyFormMinus`: `dim P_r⁻Λᵏ = (r + n choose r + k) (r + k - 1 choose k)` (`r ≥ 1`);
* **exactness**: `exists_extDeriv_eq_of_mem_polyForm`, `map_extDeriv_polyForm` for
  `P_{r+1}Λᵏ → P_rΛ^{k+1} → P_{r-1}Λ^{k+2}`, `exists_extDeriv_eq_of_mem_polyFormMinus`,
  `map_extDeriv_polyFormMinus` for `P_r⁻Λᵏ → P_r⁻Λ^{k+1} → P_r⁻Λ^{k+2}` (`r ≥ 1`), and the
  cohomology in degree `0`: `polyForm_inf_ker_extDeriv_zero`,
  `polyFormMinus_inf_ker_extDeriv_zero` (the closed `0`-forms are the constants `P_0Λ⁰`, of
  dimension one by `finrank_polyForm_zero_zero`);
* `mem_polyForm_of_mem_polyFormMinus_of_extDeriv_eq_zero`: a closed form of `P_r⁻Λᵏ` lies in
  `P_{r-1}Λᵏ` ([AFW2010], Thm 5.4).

The edge case `r + k = 0` is excluded exactly where it fails: `H_0Λ⁰` (the constants) is not
`κ(·) + d(·)`, and the closed `0`-forms are the constants rather than `0`.

## Implementation notes

Statements are written with `r + 1`, `k + 1` where the textbook writes `r ≥ 1`, `k - 1`, to
avoid truncated subtraction: e.g. `H_{r+1}Λ^{k+1} = κ H_rΛ^{k+2} ⊕ d H_{r+2}Λᵏ` is
`H_rΛᵏ = κ H_{r-1}Λ^{k+1} ⊕ d H_{r+1}Λ^{k-1}` for `r, k ≥ 1`; the cases `k = 0` and `r = 0` are
`map_koszul_homForm_one` and `Feec.Koszul.homForm_le_sup`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3 (the Koszul complex, `P_rΛᵏ`, `P_r⁻Λᵏ`, their dimensions)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.1 (Thms 5.1–5.4, the resolutions (71), (72))
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.Koszul

open ExteriorFibre

variable {R : Type*} [CommRing R] {d : Type*}

/-! ### Homogeneous components of polynomial forms -/

variable (j : ℕ) in
/-- The homogeneous component of polynomial degree `j` of a polynomial form, coefficientwise. -/
def homComp (ω : PolyForm R d) : PolyForm R d := fun s => homogeneousComponent j (ω s)

theorem homComp_apply (j : ℕ) (ω : PolyForm R d) (s : Finset d) :
    homComp j ω s = homogeneousComponent j (ω s) := rfl

@[simp] theorem homComp_zero (j : ℕ) : homComp j (0 : PolyForm R d) = 0 := by
  funext s; simp [homComp_apply]

theorem homComp_add (j : ℕ) (ω η : PolyForm R d) :
    homComp j (ω + η) = homComp j ω + homComp j η := by
  funext s; simp [homComp_apply]

theorem homComp_smul (j : ℕ) (c : R) (ω : PolyForm R d) :
    homComp j (c • ω) = c • homComp j ω := by
  funext s; simp [homComp_apply]

theorem homComp_sum {ι : Type*} (j : ℕ) (u : Finset ι) (ω : ι → PolyForm R d) :
    homComp j (∑ i ∈ u, ω i) = ∑ i ∈ u, homComp j (ω i) := by
  funext s; simp [homComp_apply, Finset.sum_apply, map_sum]

theorem isDeg_homComp {k : ℕ} {ω : PolyForm R d} (h : IsDeg k ω) (j : ℕ) :
    IsDeg k (homComp j ω) := fun s hs => by simp [homComp_apply, h s hs]

theorem homComp_mem_homForm {k : ℕ} {ω : PolyForm R d} (h : IsDeg k ω) (j : ℕ) :
    homComp j ω ∈ homForm R d j k :=
  ⟨isDeg_homComp h j, fun s => homogeneousComponent_isHomogeneous j (ω s)⟩

theorem homComp_of_mem_homForm {m k : ℕ} {ω : PolyForm R d} (h : ω ∈ homForm R d m k) (j : ℕ) :
    homComp j ω = if j = m then ω else 0 := by
  funext s
  rw [homComp_apply, homogeneousComponent_of_mem (h.2 s)]
  split_ifs <;> rfl

theorem homComp_eq_zero_of_mem_polyForm {r k : ℕ} {ω : PolyForm R d} (h : ω ∈ polyForm R d r k)
    {j : ℕ} (hj : r < j) : homComp j ω = 0 := by
  funext s
  exact homogeneousComponent_eq_zero _ _ (lt_of_le_of_lt (h.2 s) hj)

/-- A polynomial form of degree `≤ r` is the sum of its homogeneous components of degree `≤ r`. -/
theorem sum_homComp {r k : ℕ} {ω : PolyForm R d} (h : ω ∈ polyForm R d r k) :
    ∑ j ∈ range (r + 1), homComp j ω = ω := by
  funext s
  rw [Finset.sum_apply]
  simp only [homComp_apply]
  conv_rhs => rw [← sum_homogeneousComponent (ω s)]
  have hle : (ω s).totalDegree + 1 ≤ r + 1 := by have := h.2 s; omega
  rw [← Finset.sum_range_add_sum_Ico _ hle]
  rw [Finset.sum_eq_zero (s := Ico _ _) fun j hj => homogeneousComponent_eq_zero _ _
    (by simp at hj; omega), add_zero]

theorem homComp_mem_polyForm_iff {r k : ℕ} {ω : PolyForm R d} (hk : IsDeg k ω) :
    ω ∈ polyForm R d r k ↔ ∀ j, r < j → homComp j ω = 0 := by
  refine ⟨fun h j hj => homComp_eq_zero_of_mem_polyForm h hj, fun h => ⟨hk, fun s => ?_⟩⟩
  rw [totalDegree, Finset.sup_le_iff]
  intro m hm
  by_contra hlt
  push Not at hlt
  have h0 := congrFun (h _ hlt) s
  rw [homComp_apply, Pi.zero_apply] at h0
  have := congrArg (fun p : MvPolynomial d R => p.coeff m) h0
  simp only [coeff_homogeneousComponent, AddMonoidAlgebra.coeff_zero] at this
  rw [ite_eq_left_iff.2 (fun h => absurd (by rw [Finsupp.degree]; rfl) h)] at this
  exact (mem_support_iff.1 hm) this

section Order

variable [LinearOrder d]

/-- Homogeneous components of a constant times a polynomial. -/
theorem homogeneousComponent_sgn_mul (j : ℕ) (i : d) (s : Finset d) (p : MvPolynomial d R) :
    homogeneousComponent j ((sgn i s : MvPolynomial d R) * p) =
      sgn i s * homogeneousComponent j p := by
  rw [show (sgn i s : MvPolynomial d R) = C (sgn i s) by simp [sgn], homogeneousComponent_C_mul]

omit [LinearOrder d] in
theorem homogeneousComponent_pderiv (j : ℕ) (i : d) (p : MvPolynomial d R) :
    homogeneousComponent j (pderiv i p) = pderiv i (homogeneousComponent (j + 1) p) := by
  conv_lhs => rw [← sum_homogeneousComponent p, map_sum, map_sum]
  rw [Finset.sum_eq_single (j + 1)]
  · have := ((homogeneousComponent_isHomogeneous (j + 1) p).pderiv (i := i))
    rw [Nat.add_sub_cancel] at this
    exact homogeneousComponent_eq_self this
  · intro m _ hm
    have hh := (homogeneousComponent_isHomogeneous m p).pderiv (i := i)
    rw [homogeneousComponent_of_mem hh]
    split_ifs with h
    · rcases m with _ | m
      · rw [homogeneousComponent_zero, pderiv_C]
      · simp at h; omega
    · rfl
  · intro hj
    rw [homogeneousComponent_eq_zero _ p (by simp at hj; omega), map_zero, map_zero]

omit [LinearOrder d] in
theorem homogeneousComponent_X_mul (j : ℕ) (i : d) (p : MvPolynomial d R) :
    homogeneousComponent (j + 1) (X i * p) = X i * homogeneousComponent j p := by
  conv_lhs => rw [← sum_homogeneousComponent p, mul_sum, map_sum]
  rw [Finset.sum_eq_single j]
  · have := (isHomogeneous_X R i).mul (homogeneousComponent_isHomogeneous j p)
    rw [add_comm] at this
    exact homogeneousComponent_eq_self this
  · intro m _ hm
    have hh := (isHomogeneous_X R i).mul (homogeneousComponent_isHomogeneous m p)
    rw [homogeneousComponent_of_mem hh]
    simp only [ite_eq_right_iff]
    omega
  · intro hj
    rw [homogeneousComponent_eq_zero _ p (by simp at hj; omega), mul_zero, map_zero]

omit [LinearOrder d] in
theorem homogeneousComponent_zero_X_mul (i : d) (p : MvPolynomial d R) :
    homogeneousComponent 0 (X i * p) = 0 := by
  classical
  rw [homogeneousComponent_zero, coeff_X_mul']
  simp

/-- `d` lowers the polynomial degree by one: `(dω)_j = d(ω_{j+1})`. -/
theorem homComp_extDeriv (j : ℕ) (ω : PolyForm R d) :
    homComp j (extDeriv ω) = extDeriv (homComp (j + 1) ω) := by
  funext s
  simp only [homComp_apply, extDeriv_apply, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show (sgn i s : MvPolynomial d R) = C (sgn i s) by simp [sgn], homogeneousComponent_C_mul,
    homogeneousComponent_pderiv]

variable [Fintype d]

/-- `κ` raises the polynomial degree by one: `(κω)_{j+1} = κ(ω_j)`. -/
theorem homComp_koszul (j : ℕ) (ω : PolyForm R d) :
    homComp (j + 1) (koszul ω) = koszul (homComp j ω) := by
  funext s
  simp only [homComp_apply, koszul_apply, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show (sgn i s : MvPolynomial d R) = C (sgn i s) by simp [sgn], mul_assoc,
    homogeneousComponent_C_mul, homogeneousComponent_X_mul, mul_assoc]

theorem homComp_zero_koszul (ω : PolyForm R d) : homComp 0 (koszul ω) = 0 := by
  funext s
  simp only [homComp_apply, koszul_apply, map_sum, Pi.zero_apply]
  refine sum_eq_zero fun i _ => ?_
  rw [show (sgn i s : MvPolynomial d R) = C (sgn i s) by simp [sgn], mul_assoc,
    homogeneousComponent_C_mul, homogeneousComponent_zero_X_mul, mul_zero]

end Order

/-! ### Forms with coefficients in a submodule -/

variable (R) in
/-- The `k`-forms all of whose coefficients lie in the submodule `S`. -/
def coeffForm (k : ℕ) (S : Submodule R (MvPolynomial d R)) : Submodule R (PolyForm R d) where
  carrier := {ω | IsDeg k ω ∧ ∀ s, ω s ∈ S}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => S.zero_mem⟩
  add_mem' {ω η} hω hη := ⟨fun s hs => by simp [hω.1 s hs, hη.1 s hs],
    fun s => S.add_mem (hω.2 s) (hη.2 s)⟩
  smul_mem' c ω hω := ⟨fun s hs => by simp [hω.1 s hs], fun s => S.smul_mem c (hω.2 s)⟩

/-- `k`-forms with coefficients in `S` are the families of elements of `S` indexed by the
`k`-subsets. -/
def coeffFormEquiv (k : ℕ) (S : Submodule R (MvPolynomial d R)) :
    coeffForm R k S ≃ₗ[R] ({s : Finset d // #s = k} → S) where
  toFun ω := fun s => ⟨ω.1 s.1, ω.2.2 s.1⟩
  invFun c := ⟨fun s => if h : #s = k then (c ⟨s, h⟩ : MvPolynomial d R) else 0,
    fun s hs => by simp [hs], fun s => by by_cases h : #s = k <;> simp [h]⟩
  left_inv ω := by
    refine Subtype.ext (funext fun s => ?_)
    simp only
    split_ifs with h
    · rfl
    · exact (ω.2.1 s h).symm
  right_inv c := funext fun s => Subtype.ext (by simp [s.2])
  map_add' ω η := rfl
  map_smul' c ω := rfl

theorem homForm_eq_coeffForm (r k : ℕ) :
    homForm R d r k = coeffForm R k (homogeneousSubmodule d R r) := rfl

theorem polyForm_eq_coeffForm (r k : ℕ) :
    polyForm R d r k = coeffForm R k (restrictTotalDegree d R r) := by
  ext ω
  exact and_congr_right fun _ => forall_congr' fun s => (mem_restrictTotalDegree d (m := r) (ω s)).symm

/-! ### Direct sums -/

/-- A form that is homogeneous of degree `r + 1` and of degree `≤ r` vanishes. -/
theorem eq_zero_of_mem_homForm_of_mem_polyForm {r k k' : ℕ} {ω : PolyForm R d}
    (h : ω ∈ homForm R d (r + 1) k) (h' : ω ∈ polyForm R d r k') : ω = 0 := by
  have h1 := homComp_of_mem_homForm h (r + 1)
  rw [homComp_eq_zero_of_mem_polyForm h' (Nat.lt_succ_self r)] at h1
  simpa using h1.symm

/-- `P_rΛᵏ ∩ H_{r+1}Λᵏ = 0`. -/
theorem disjoint_polyForm_homForm (r k : ℕ) :
    Disjoint (polyForm R d r k) (homForm R d (r + 1) k) := by
  rw [Submodule.disjoint_def]
  exact fun ω h h' => eq_zero_of_mem_homForm_of_mem_polyForm h' h

/-- **`P_{r+1}Λᵏ = P_rΛᵏ ⊕ H_{r+1}Λᵏ`** (with `disjoint_polyForm_homForm`). [AFW2010], §5.1 -/
theorem polyForm_sup_homForm (r k : ℕ) :
    polyForm R d r k ⊔ homForm R d (r + 1) k = polyForm R d (r + 1) k := by
  refine le_antisymm (sup_le (polyForm_mono (Nat.le_succ r) k) (homForm_le_polyForm _ _))
    fun ω h => ?_
  rw [← sum_homComp h, Finset.sum_range_succ]
  refine Submodule.add_mem_sup (Submodule.sum_mem _ fun j hj => ?_)
    (homComp_mem_homForm h.1 (r + 1))
  exact polyForm_mono (by simp at hj; omega) k
    (homForm_le_polyForm _ _ (homComp_mem_homForm h.1 j))

/-- `P_0Λᵏ = H_0Λᵏ` (constant coefficients). -/
theorem polyForm_zero_eq_homForm (k : ℕ) : polyForm R d 0 k = homForm R d 0 k := by
  refine le_antisymm (fun ω h => ?_) (homForm_le_polyForm _ _)
  rw [← sum_homComp h, Finset.sum_range_one]
  exact homComp_mem_homForm h.1 0

section Order

variable [LinearOrder d] [Fintype d]

/-- `κ H_rΛ^{k+1} ⊆ H_{r+1}Λᵏ`. -/
theorem map_koszul_homForm_le_succ (r k : ℕ) :
    (homForm R d r (k + 1)).map (koszulₗ R d) ≤ homForm R d (r + 1) k :=
  map_koszul_homForm_le (r := r + 1) (Nat.le_add_left 1 r) k

/-- `P_{r+1}⁻Λᵏ = P_rΛᵏ + κ H_rΛ^{k+1}`. -/
theorem polyFormMinus_succ (r k : ℕ) :
    polyFormMinus R d (r + 1) k =
      polyForm R d r k ⊔ (homForm R d r (k + 1)).map (koszulₗ R d) := rfl

/-- `P_rΛᵏ ∩ κ H_rΛ^{k+1} = 0`: the sum `P_{r+1}⁻Λᵏ = P_rΛᵏ ⊕ κ H_rΛ^{k+1}` is direct.
[AFW2010], §5.1.3 -/
theorem disjoint_polyForm_map_koszul (r k : ℕ) :
    Disjoint (polyForm R d r k) ((homForm R d r (k + 1)).map (koszulₗ R d)) :=
  (disjoint_polyForm_homForm r k).mono_right (map_koszul_homForm_le_succ r k)

end Order

/-! ### Binomial identities -/

/-- `C(n, k) C(n + r, r) = C(r + n, r + k) C(r + k, k)`. -/
theorem choose_mul_add_choose (n r k : ℕ) :
    n.choose k * (n + r).choose r = (r + n).choose (r + k) * (r + k).choose k := by
  have h := Nat.choose_mul (n := r + n) (k := r + k) (s := r) (Nat.le_add_right r k)
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h
  rw [← @Nat.choose_symm_add r k, h, add_comm n r, mul_comm]

/-! ### Dimensions (over a field) -/

section Field

variable {K : Type*} [Field K] [LinearOrder d] [Fintype d]

instance (k : ℕ) (S : Submodule K (MvPolynomial d K)) [FiniteDimensional K S] :
    FiniteDimensional K (coeffForm K k S) :=
  LinearEquiv.finiteDimensional (coeffFormEquiv k S).symm

omit [LinearOrder d] in
theorem finrank_coeffForm (k : ℕ) (S : Submodule K (MvPolynomial d K)) [FiniteDimensional K S] :
    Module.finrank K (coeffForm K k S) = (Fintype.card d).choose k * Module.finrank K S := by
  rw [(coeffFormEquiv k S).finrank_eq, Module.finrank_pi_fintype, sum_const, card_univ,
    Fintype.card_finset_len, smul_eq_mul]

instance (r k : ℕ) : FiniteDimensional K (polyForm K d r k) := by
  rw [polyForm_eq_coeffForm]; infer_instance

instance (r k : ℕ) : FiniteDimensional K (homForm K d r k) :=
  Submodule.finiteDimensional_of_le (homForm_le_polyForm r k)

theorem polyFormMinus_le_polyForm_succ (r k : ℕ) :
    polyFormMinus K d r k ≤ polyForm K d (r + 1) k := by
  refine sup_le (polyForm_mono (by omega) k) ?_
  rintro _ ⟨ω, hω, rfl⟩
  exact polyForm_mono (by omega) k (homForm_le_polyForm _ _ (koszul_mem_homForm hω))

instance (r k : ℕ) : FiniteDimensional K (polyFormMinus K d r k) :=
  Submodule.finiteDimensional_of_le (polyFormMinus_le_polyForm_succ r k)

/-- `dim H_r(ℝⁿ) = (n + r - 1 choose r)`: the monomials of degree `r`. -/
theorem finrank_homogeneousSubmodule (r : ℕ) :
    Module.finrank K (homogeneousSubmodule d K r) = (Fintype.card d + r - 1).choose r := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank K (restrictSupport K {f : d →₀ ℕ | f.degree = r}) = _
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K {f : d →₀ ℕ | f.degree = r})]
  have hset : {f : d →₀ ℕ | f.degree = r} = ↑((univ : Finset d).finsuppAntidiag r) := by
    ext f
    simp [Finsupp.degree_eq_sum]
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    card_finsuppAntidiag_nat_eq_choose, card_univ]

/-- **`dim H_rΛᵏ(ℝⁿ) = (n choose k) (n + r - 1 choose r)`**. -/
theorem finrank_homForm (r k : ℕ) :
    Module.finrank K (homForm K d r k) =
      (Fintype.card d).choose k * (Fintype.card d + r - 1).choose r := by
  rw [homForm_eq_coeffForm]
  have : FiniteDimensional K (homogeneousSubmodule d K r) :=
    Module.Finite.iff_fg.2 (homogeneousSubmodule_fg d K r)
  rw [finrank_coeffForm, finrank_homogeneousSubmodule]

theorem finrank_polyForm_eq_mul (r k : ℕ) :
    Module.finrank K (polyForm K d r k) =
      (Fintype.card d).choose k * (Fintype.card d + r).choose r := by
  induction r with
  | zero => rw [polyForm_zero_eq_homForm, finrank_homForm]; simp
  | succ r ih =>
    have h := Submodule.finrank_sup_add_finrank_inf_eq (polyForm K d r k) (homForm K d (r + 1) k)
    rw [polyForm_sup_homForm, (disjoint_polyForm_homForm r k).eq_bot, finrank_bot, add_zero,
      ih, finrank_homForm, show Fintype.card d + (r + 1) - 1 = Fintype.card d + r by omega] at h
    rw [h, ← mul_add, ← Nat.choose_succ_succ']
    rfl

/-- **`dim P_rΛᵏ(ℝⁿ) = (r + n choose r + k) (r + k choose k)`**. [AFW2006], §3; [AFW2010], §5.1 -/
theorem finrank_polyForm (r k : ℕ) :
    Module.finrank K (polyForm K d r k) =
      (r + Fintype.card d).choose (r + k) * (r + k).choose k := by
  rw [finrank_polyForm_eq_mul, choose_mul_add_choose]

end Field

/-! ### The Koszul decompositions and their dimensions (characteristic zero) -/

/-- A linear map injective on `V` preserves its dimension. -/
theorem finrank_map_of_injOn {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (V : Submodule K M)
    (hf : ∀ x ∈ V, f x = 0 → x = 0) : Module.finrank K (V.map f) = Module.finrank K V := by
  have hinj : Function.Injective (f ∘ₗ V.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hf x x.2 hx)
  have hr : LinearMap.range (f ∘ₗ V.subtype) = V.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hr, ← (LinearEquiv.ofInjective _ hinj).finrank_eq]

/-- `d` of a form with constant coefficients vanishes. -/
theorem extDeriv_homComp_zero [LinearOrder d] (ω : PolyForm R d) :
    extDeriv (homComp 0 ω) = 0 := by
  funext s
  simp [extDeriv_apply, homComp_apply]

/-- The homogeneous components of a closed form are closed. -/
theorem extDeriv_homComp_eq_zero [LinearOrder d] {ω : PolyForm R d} (hω : extDeriv ω = 0)
    (j : ℕ) : extDeriv (homComp j ω) = 0 := by
  rcases j with _ | j
  · exact extDeriv_homComp_zero ω
  · rw [← homComp_extDeriv, hω]
    funext s; simp [homComp_apply]

section CharZero

variable {K : Type*} [Field K] [CharZero K] [LinearOrder d] [Fintype d]

/-- A closed form in `H_rΛᵏ`, `r + k > 0`, is `d` of `(r + k)⁻¹ κ ω`. -/
theorem extDeriv_smul_koszul_of_mem {r k : ℕ} (hrk : 0 < r + k) {ω : PolyForm K d}
    (h : ω ∈ homForm K d r k) (hd : extDeriv ω = 0) :
    extDeriv (((r + k : ℕ) : K)⁻¹ • koszul ω) = ω := by
  conv_rhs => rw [eq_koszul_add_extDeriv hrk h]
  rw [hd, smul_zero, koszul_zero, zero_add]

/-- **`P_r⁻Λᵏ` with `d ω = 0` lies in `P_{r-1}Λᵏ`** (`r ≥ 1`). [AFW2010], §5.1.3, Thm 5.4 -/
theorem mem_polyForm_of_mem_polyFormMinus_of_extDeriv_eq_zero {r k : ℕ} (hr : 1 ≤ r)
    {ω : PolyForm K d} (h : ω ∈ polyFormMinus K d r k) (hd : extDeriv ω = 0) :
    ω ∈ polyForm K d (r - 1) k := by
  obtain ⟨a, ha, b, ⟨c, hc, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
  change a + koszul c ∈ _
  change extDeriv (a + koszul c) = 0 at hd
  -- the degree-`r` part `κ c` of `ω` is closed
  have hκc : koszul c ∈ homForm K d r k := map_koszul_homForm_le hr k ⟨c, hc, rfl⟩
  have hdκ : extDeriv (koszul c) = 0 := by
    have h1 := congrArg (homComp (r - 1)) hd
    rw [extDeriv_add, homComp_add, homComp_extDeriv, homComp_extDeriv, Nat.sub_add_cancel hr,
      homComp_eq_zero_of_mem_polyForm ha (Nat.sub_lt hr Nat.one_pos), homComp_of_mem_homForm hκc] at h1
    simpa using h1
  have hzero : koszul c = 0 := by
    have := extDeriv_koszul_add_koszul_extDeriv_of_mem hκc
    rw [hdκ, koszul_koszul, extDeriv_zero, koszul_zero, add_zero] at this
    exact (smul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 (by omega))
  rw [hzero, add_zero]
  exact ha

/-! #### Exactness of the polynomial complexes -/

/-- **Exactness of the polynomial de Rham complex** `P_{r+1}Λᵏ → P_rΛ^{k+1} → P_{r-1}Λ^{k+2}`:
a closed `ω ∈ P_rΛ^{k+1}` is `d η` with `η = Σⱼ (j + k + 1)⁻¹ κ ωⱼ ∈ P_{r+1}Λᵏ` (`ωⱼ` the
homogeneous components of `ω`). [AFW2010], §5.1.4, (71) -/
theorem exists_extDeriv_eq_of_mem_polyForm {r k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ polyForm K d r (k + 1)) (hd : extDeriv ω = 0) :
    ∃ η ∈ polyForm K d (r + 1) k, extDeriv η = ω := by
  refine ⟨∑ j ∈ range (r + 1), ((j + (k + 1) : ℕ) : K)⁻¹ • koszul (homComp j ω),
    Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_, ?_⟩
  · have := koszul_mem_homForm (homComp_mem_homForm h.1 j)
    exact polyForm_mono (by simp at hj; omega) k (homForm_le_polyForm _ _ this)
  · rw [← extDerivₗ_apply, map_sum]
    conv_rhs => rw [← sum_homComp h]
    refine sum_congr rfl fun j _ => ?_
    exact extDeriv_smul_koszul_of_mem (by omega) (homComp_mem_homForm h.1 j)
      (extDeriv_homComp_eq_zero hd j)

/-- **The cohomology in degree `0` is the constants**: a closed polynomial `0`-form has constant
coefficients. [AFW2010], §5.1.4, (71) -/
theorem mem_polyForm_zero_of_extDeriv_eq_zero {ω : PolyForm K d} (h0 : IsDeg 0 ω)
    (hd : extDeriv ω = 0) : ω ∈ polyForm K d 0 0 := by
  refine (homComp_mem_polyForm_iff h0).2 fun j hj => ?_
  have hm := homComp_mem_homForm h0 j
  have := extDeriv_koszul_add_koszul_extDeriv_of_mem hm
  rw [IsDeg.koszul_eq_zero hm.1, extDeriv_zero, extDeriv_homComp_eq_zero hd j, koszul_zero,
    add_zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 (by omega))

/-- The range of `d : P_{r+1}Λᵏ → P_rΛ^{k+1}` is the kernel of `d` on `P_rΛ^{k+1}`. -/
theorem map_extDeriv_polyForm (r k : ℕ) :
    (polyForm K d (r + 1) k).map (extDerivₗ K d) =
      polyForm K d r (k + 1) ⊓ LinearMap.ker (extDerivₗ K d) := by
  refine le_antisymm ?_ fun ω ⟨h, hd⟩ => ?_
  · rintro _ ⟨η, hη, rfl⟩
    exact ⟨by simpa using extDeriv_mem_polyForm hη, extDeriv_extDeriv η⟩
  · obtain ⟨η, hη, rfl⟩ := exists_extDeriv_eq_of_mem_polyForm h hd
    exact ⟨η, hη, rfl⟩

/-- The kernel of `d` on `P_rΛ⁰` is the constants `P_0Λ⁰`. -/
theorem polyForm_inf_ker_extDeriv_zero (r : ℕ) :
    polyForm K d r 0 ⊓ LinearMap.ker (extDerivₗ K d) = polyForm K d 0 0 := by
  refine le_antisymm (fun ω ⟨h, hd⟩ => mem_polyForm_zero_of_extDeriv_eq_zero h.1 hd)
    fun ω h => ⟨polyForm_mono (Nat.zero_le r) 0 h, ?_⟩
  rw [polyForm_zero_eq_homForm] at h
  change extDeriv ω = 0
  rw [← sum_homComp (homForm_le_polyForm _ _ h), Finset.sum_range_one]
  exact extDeriv_homComp_zero ω

omit [CharZero K] in
/-- `dim P_0Λ⁰ = 1`: the cohomology of the polynomial complexes in degree `0` is `K`. -/
theorem finrank_polyForm_zero_zero : Module.finrank K (polyForm K d 0 0) = 1 := by
  rw [finrank_polyForm]; simp

/-- **`P_r⁻Λ⁰ = P_rΛ⁰`** (`r ≥ 1`). [AFW2010], §5.1.3 -/
theorem polyFormMinus_zero {r : ℕ} (hr : 1 ≤ r) : polyFormMinus K d r 0 = polyForm K d r 0 := by
  refine le_antisymm (polyFormMinus_le_polyForm hr 0) fun ω h => ?_
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [← sum_homComp h, Finset.sum_range_succ]
  refine Submodule.add_mem_sup (Submodule.sum_mem _ fun j hj => ?_) ?_
  · exact polyForm_mono (by simp at hj; omega) 0
      (homForm_le_polyForm _ _ (homComp_mem_homForm h.1 j))
  · have hm := homComp_mem_homForm h.1 (r + 1)
    rw [eq_koszul_add_extDeriv (by omega) hm, IsDeg.koszul_eq_zero hm.1, smul_zero, extDeriv_zero,
      add_zero]
    exact ⟨_, Submodule.smul_mem _ _ (extDeriv_mem_homForm hm), rfl⟩

/-- **Exactness of the trimmed complex** `P_r⁻Λᵏ → P_r⁻Λ^{k+1} → P_r⁻Λ^{k+2}` (`r ≥ 1`): a closed
`ω ∈ P_r⁻Λ^{k+1}` is `d η` with `η ∈ P_r⁻Λᵏ`. [AFW2010], §5.1.4, (72) -/
theorem exists_extDeriv_eq_of_mem_polyFormMinus {r k : ℕ} (hr : 1 ≤ r) {ω : PolyForm K d}
    (h : ω ∈ polyFormMinus K d r (k + 1)) (hd : extDeriv ω = 0) :
    ∃ η ∈ polyFormMinus K d r k, extDeriv η = ω := by
  have h' := mem_polyForm_of_mem_polyFormMinus_of_extDeriv_eq_zero hr h hd
  refine ⟨∑ j ∈ range (r - 1 + 1), ((j + (k + 1) : ℕ) : K)⁻¹ • koszul (homComp j ω),
    Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_, ?_⟩
  · have hj' : j ≤ r - 1 := by simp at hj; omega
    have hm := homComp_mem_homForm h'.1 j
    rcases Nat.lt_or_ge j (r - 1) with hlt | hge
    · refine Submodule.mem_sup_left (polyForm_mono (show j + 1 ≤ r - 1 by omega) k ?_)
      exact homForm_le_polyForm (j + 1) k (by simpa using koszul_mem_homForm hm)
    · have : j = r - 1 := le_antisymm hj' hge
      subst this
      exact Submodule.mem_sup_right ⟨_, hm, rfl⟩
  · rw [← extDerivₗ_apply, map_sum]
    conv_rhs => rw [← sum_homComp h']
    refine sum_congr rfl fun j _ => ?_
    exact extDeriv_smul_koszul_of_mem (by omega) (homComp_mem_homForm h'.1 j)
      (extDeriv_homComp_eq_zero hd j)

/-- The range of `d : P_r⁻Λᵏ → P_r⁻Λ^{k+1}` is the kernel of `d` on `P_r⁻Λ^{k+1}` (`r ≥ 1`). -/
theorem map_extDeriv_polyFormMinus {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    (polyFormMinus K d r k).map (extDerivₗ K d) =
      polyFormMinus K d r (k + 1) ⊓ LinearMap.ker (extDerivₗ K d) := by
  refine le_antisymm ?_ fun ω ⟨h, hd⟩ => ?_
  · rintro _ ⟨η, hη, rfl⟩
    exact ⟨extDeriv_mem_polyFormMinus hr hη, extDeriv_extDeriv η⟩
  · obtain ⟨η, hη, rfl⟩ := exists_extDeriv_eq_of_mem_polyFormMinus hr h hd
    exact ⟨η, hη, rfl⟩

/-- The kernel of `d` on `P_r⁻Λ⁰` is the constants (`r ≥ 1`). -/
theorem polyFormMinus_inf_ker_extDeriv_zero {r : ℕ} (hr : 1 ≤ r) :
    polyFormMinus K d r 0 ⊓ LinearMap.ker (extDerivₗ K d) = polyForm K d 0 0 := by
  rw [polyFormMinus_zero hr, polyForm_inf_ker_extDeriv_zero]

/-! #### `P_rΛᵏ = P_r⁻Λᵏ ⊕ d H_{r+1}Λ^{k-1}` -/

/-- **`P_rΛ^{k+1} = P_r⁻Λ^{k+1} + d H_{r+1}Λᵏ`** (`r ≥ 1`); the sum is direct
(`disjoint_polyFormMinus_map_extDeriv`), and `P_r⁻Λ⁰ = P_rΛ⁰` (`polyFormMinus_zero`).
[AFW2010], §5.1.3 -/
theorem polyFormMinus_sup_map_extDeriv {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    polyFormMinus K d r (k + 1) ⊔ (homForm K d (r + 1) k).map (extDerivₗ K d) =
      polyForm K d r (k + 1) := by
  refine le_antisymm (sup_le (polyFormMinus_le_polyForm hr _) ?_) fun ω h => ?_
  · rintro _ ⟨η, hη, rfl⟩
    exact homForm_le_polyForm _ _ (by simpa using extDeriv_mem_homForm hη)
  · obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [← sum_homComp h, Finset.sum_range_succ]
    have hm := homComp_mem_homForm h.1 (r + 1)
    rw [eq_koszul_add_extDeriv (by omega) hm, ← add_assoc]
    refine Submodule.add_mem_sup (Submodule.add_mem _ (Submodule.mem_sup_left
      (Submodule.sum_mem _ fun j hj => ?_)) (Submodule.mem_sup_right ⟨_,
        Submodule.smul_mem _ _ (extDeriv_mem_homForm hm), rfl⟩))
      ⟨_, Submodule.smul_mem _ _ (by simpa using koszul_mem_homForm hm), rfl⟩
    exact polyForm_mono (by simp at hj; omega) _
      (homForm_le_polyForm _ _ (homComp_mem_homForm h.1 j))

/-- `P_r⁻Λ^{k+1} ∩ d H_{r+1}Λᵏ = 0` (`r ≥ 1`). [AFW2010], §5.1.3 -/
theorem disjoint_polyFormMinus_map_extDeriv {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    Disjoint (polyFormMinus K d r (k + 1)) ((homForm K d (r + 1) k).map (extDerivₗ K d)) := by
  rw [Submodule.disjoint_def]
  rintro x hx ⟨β, hβ, rfl⟩
  have hxh : extDeriv β ∈ homForm K d r (k + 1) := by simpa using extDeriv_mem_homForm hβ
  obtain ⟨a, ha, b, ⟨c, hc, rfl⟩, hab⟩ := Submodule.mem_sup.1 hx
  have hκc : koszul c ∈ homForm K d r (k + 1) := map_koszul_homForm_le hr _ ⟨c, hc, rfl⟩
  have h1 := congrArg (homComp r) hab
  change homComp r (a + koszul c) = homComp r (extDeriv β) at h1
  rw [homComp_add, homComp_eq_zero_of_mem_polyForm ha (Nat.sub_lt hr Nat.one_pos),
    homComp_of_mem_homForm hκc, homComp_of_mem_homForm hxh] at h1
  simp only [↓reduceIte, zero_add] at h1
  exact eq_zero_of_eq_koszul_of_eq_extDeriv (by omega) hxh h1.symm rfl

/-! #### Dimensions of `κ H_rΛ^{k+1}`, `d H_{r+1}Λᵏ` and `P_r⁻Λᵏ` -/

/-- `κ H_sΛ¹ = H_{s+1}Λ⁰`. -/
theorem map_koszul_homForm_one (s : ℕ) :
    (homForm K d s 1).map (koszulₗ K d) = homForm K d (s + 1) 0 := by
  refine le_antisymm (map_koszul_homForm_le_succ s 0) fun ω hm => ?_
  rw [eq_koszul_add_extDeriv (by omega) hm, IsDeg.koszul_eq_zero hm.1, smul_zero, extDeriv_zero,
    add_zero]
  exact ⟨_, Submodule.smul_mem _ _ (by simpa using extDeriv_mem_homForm hm), rfl⟩

/-- `d H_{r+1}Λᵏ = d κ H_rΛ^{k+1}`. -/
theorem map_extDeriv_homForm_eq (r k : ℕ) :
    (homForm K d (r + 1) k).map (extDerivₗ K d) =
      ((homForm K d r (k + 1)).map (koszulₗ K d)).map (extDerivₗ K d) := by
  refine le_antisymm ?_ (Submodule.map_mono (map_koszul_homForm_le_succ r k))
  rintro _ ⟨ω, hm, rfl⟩
  refine ⟨_, ⟨_, Submodule.smul_mem _ (((r + 1 + k : ℕ) : K)⁻¹)
    (by simpa using extDeriv_mem_homForm hm), rfl⟩, ?_⟩
  conv_rhs => rw [extDerivₗ_apply, eq_koszul_add_extDeriv (by omega) hm, extDeriv_add,
    extDeriv_extDeriv, add_zero]
  rfl

/-- `d` is injective on `κ H_rΛ^{k+1}`. -/
theorem eq_zero_of_extDeriv_eq_zero_of_mem_map_koszul {r k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ (homForm K d r (k + 1)).map (koszulₗ K d)) (hd : extDeriv ω = 0) : ω = 0 := by
  have hm := map_koszul_homForm_le_succ r k h
  obtain ⟨c, -, rfl⟩ := h
  change koszul c ∈ _ at hm
  change extDeriv (koszul c) = 0 at hd
  change koszul c = 0
  have := extDeriv_koszul_add_koszul_extDeriv_of_mem hm
  rw [koszul_koszul, extDeriv_zero, zero_add, hd, koszul_zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 (by omega))

/-- `dim d H_{r+1}Λᵏ = dim κ H_rΛ^{k+1}`. -/
theorem finrank_map_extDeriv_homForm (r k : ℕ) :
    Module.finrank K ((homForm K d (r + 1) k).map (extDerivₗ K d)) =
      Module.finrank K ((homForm K d r (k + 1)).map (koszulₗ K d)) := by
  rw [map_extDeriv_homForm_eq]
  exact finrank_map_of_injOn _ _ fun x hx hd => eq_zero_of_extDeriv_eq_zero_of_mem_map_koszul hx hd

/-- **The Koszul decomposition** `H_{r+1}Λ^{k+1} = κ H_rΛ^{k+2} ⊕ d H_{r+2}Λᵏ`, as an equality of
submodules (the sum is direct by `eq_zero_of_eq_koszul_of_eq_extDeriv`). [AFW2010], §5.1, (69) -/
theorem map_koszul_sup_map_extDeriv (r k : ℕ) :
    (homForm K d r (k + 2)).map (koszulₗ K d) ⊔ (homForm K d (r + 2) k).map (extDerivₗ K d) =
      homForm K d (r + 1) (k + 1) := by
  refine le_antisymm (sup_le (map_koszul_homForm_le_succ r (k + 1)) ?_) ?_
  · rintro _ ⟨η, hη, rfl⟩
    simpa using extDeriv_mem_homForm hη
  · have := homForm_le_sup (K := K) (d := d) (r := r + 1) (k := k + 1) (by omega)
    simpa using this

theorem disjoint_map_koszul_map_extDeriv (r k : ℕ) :
    Disjoint ((homForm K d r (k + 2)).map (koszulₗ K d))
      ((homForm K d (r + 2) k).map (extDerivₗ K d)) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨a, ha, rfl⟩ ⟨b, -, hb⟩
  exact eq_zero_of_eq_koszul_of_eq_extDeriv (r := r + 1) (k := k + 1) (by omega)
    (map_koszul_homForm_le_succ r (k + 1) ⟨a, ha, rfl⟩) rfl hb.symm

/-- `dim H_{r+1}Λ^{k+1} = dim κ H_rΛ^{k+2} + dim κ H_{r+1}Λ^{k+1}`. -/
theorem finrank_homForm_eq_add (r k : ℕ) :
    Module.finrank K (homForm K d (r + 1) (k + 1)) =
      Module.finrank K ((homForm K d r (k + 2)).map (koszulₗ K d)) +
        Module.finrank K ((homForm K d (r + 1) (k + 1)).map (koszulₗ K d)) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    ((homForm K d r (k + 2)).map (koszulₗ K d)) ((homForm K d (r + 2) k).map (extDerivₗ K d))
  rw [map_koszul_sup_map_extDeriv, (disjoint_map_koszul_map_extDeriv r k).eq_bot, finrank_bot,
    add_zero, finrank_map_extDeriv_homForm] at h
  exact h

/-- The binomial identity behind `dim κ H_rΛ^{k+1}`. -/
theorem choose_identity_koszul (n s j : ℕ) :
    n.choose (j + 1) * (n + s).choose (s + 1) =
      (n + s).choose (s + j + 2) * (s + j + 1).choose (j + 1) +
        (n + s + 1).choose (s + j + 2) * (s + j + 1).choose j := by
  have hP := choose_mul_add_choose n s (j + 1)
  have hP' := choose_mul_add_choose n (s + 1) (j + 1)
  have h1 : (n + (s + 1)).choose (s + 1) = (n + s).choose s + (n + s).choose (s + 1) :=
    Nat.choose_succ_succ' (n + s) s
  have h2 : (s + 1 + (j + 1)).choose (j + 1) = (s + j + 1).choose j + (s + j + 1).choose (j + 1) := by
    rw [show s + 1 + (j + 1) = s + j + 1 + 1 by omega]; exact Nat.choose_succ_succ' _ _
  have h3 : (s + 1 + n).choose (s + 1 + (j + 1)) =
      (n + s).choose (s + j + 1) + (n + s).choose (s + j + 2) := by
    rw [show s + 1 + n = n + s + 1 by omega, show s + 1 + (j + 1) = s + j + 1 + 1 by omega]
    exact Nat.choose_succ_succ' _ _
  rw [h1, h2, h3] at hP'
  rw [show s + n = n + s by omega, show s + (j + 1) = s + j + 1 by omega] at hP
  have h4 : (n + s + 1).choose (s + j + 2) =
      (n + s).choose (s + j + 1) + (n + s).choose (s + j + 2) := Nat.choose_succ_succ' _ _
  rw [h4]
  zify at hP hP' ⊢
  linear_combination hP' - hP

/-- **`dim κ H_rΛ^{k+1}(ℝⁿ) = (n + r choose r + k + 1) (r + k choose k)`** (equivalently
`(n + r choose n - k - 1) (r + k choose k)`). [AFW2010], §5.1, Thm 5.3 -/
theorem finrank_map_koszul_homForm (r k : ℕ) :
    Module.finrank K ((homForm K d r (k + 1)).map (koszulₗ K d)) =
      (Fintype.card d + r).choose (r + k + 1) * (r + k).choose k := by
  induction k generalizing r with
  | zero =>
    rw [map_koszul_homForm_one, finrank_homForm]
    simp [show Fintype.card d + (r + 1) - 1 = Fintype.card d + r by omega]
  | succ k ih =>
    have h := finrank_homForm_eq_add (K := K) (d := d) r k
    rw [ih (r + 1), finrank_homForm, show Fintype.card d + (r + 1) - 1 = Fintype.card d + r by omega,
      choose_identity_koszul] at h
    rw [show r + (k + 1) + 1 = r + k + 2 by omega, show r + (k + 1) = r + k + 1 by omega,
      show k + 1 + 1 = k + 2 from rfl]
    rw [show r + 1 + k + 1 = r + k + 2 by omega, show r + 1 + k = r + k + 1 by omega,
      show Fintype.card d + (r + 1) = Fintype.card d + r + 1 by omega] at h
    omega

/-- **`dim d H_{r+1}Λᵏ(ℝⁿ) = (n + r choose r + k + 1) (r + k choose k)`**. [AFW2010], §5.1, Thm 5.3 -/
theorem finrank_map_extDeriv_homForm' (r k : ℕ) :
    Module.finrank K ((homForm K d (r + 1) k).map (extDerivₗ K d)) =
      (Fintype.card d + r).choose (r + k + 1) * (r + k).choose k := by
  rw [finrank_map_extDeriv_homForm, finrank_map_koszul_homForm]

/-- **`dim P_r⁻Λᵏ(ℝⁿ) = (r + n choose r + k) (r + k - 1 choose k)`** (`r ≥ 1`).
[AFW2006], §3; [AFW2010], §5.1.3 -/
theorem finrank_polyFormMinus {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    Module.finrank K (polyFormMinus K d r k) =
      (r + Fintype.card d).choose (r + k) * (r + k - 1).choose k := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq (polyForm K d r k)
    ((homForm K d r (k + 1)).map (koszulₗ K d))
  rw [← polyFormMinus_succ, (disjoint_polyForm_map_koszul r k).eq_bot, finrank_bot, add_zero,
    finrank_polyForm, finrank_map_koszul_homForm] at h
  rw [h, show r + 1 + k - 1 = r + k by omega, show r + 1 + Fintype.card d =
    r + Fintype.card d + 1 by omega, show r + 1 + k = r + k + 1 by omega,
    Nat.choose_succ_succ', add_mul, show Fintype.card d + r = r + Fintype.card d by omega]

end CharZero

end Feec.Koszul
