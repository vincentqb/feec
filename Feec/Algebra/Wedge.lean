module

public import Feec.Algebra.Koszul
public import Mathlib.Data.Finset.Powerset

/-!
# The exterior product of coefficient forms

Forms on `R^d` (`d` a finite linearly ordered index type, `R` a commutative ring) in the basis
`dx_s` are coefficient functions `ω : Finset d → R` (`Feec.ExteriorFibre`). Their exterior product
is

  `(ω ∧ η)_u = Σ_{s ⊆ u} ε(s, u ∖ s) ω_s η_{u ∖ s}`,

with the shuffle sign `ε(s, t) = ∏_{a ∈ s} ε(a, t) = (-1)^{#{(a, b) ∈ s × t | b < a}}`, so that
`dx_s ∧ dx_t = ε(s, t) dx_{s ∪ t}` for disjoint `s`, `t`. Taking `R = R'[x_d]` gives the exterior
product of polynomial forms (`Feec.Koszul.PolyForm`), for which the exterior derivative is a
graded derivation.

## Main definitions

* `Feec.ExteriorFibre.shuffleSgn s t`, `Feec.ExteriorFibre.wedgeForm ω η`;
* `Feec.ExteriorFibre.oneForm ξ`: a covector as a `1`-form;
* `Feec.Koszul.pderivForm j ω`: coefficientwise partial derivatives.

## Main results

* bilinearity, units (`wedgeForm_one_left`, `wedgeForm_one_right`) and degrees
  (`IsDeg.wedgeForm`);
* `wedgeForm_assoc`: **associativity** `(ω ∧ η) ∧ ζ = ω ∧ (η ∧ ζ)`;
* `wedgeForm_comm`: **graded commutativity** `η ∧ ω = (-1)^{kl} ω ∧ η`;
* `wedge_wedgeForm`, `wedge_wedgeForm_right`: associativity with a covector,
  `ξ ∧ (ω ∧ η) = (ξ ∧ ω) ∧ η = (-1)^k ω ∧ (ξ ∧ η)`;
* `wedgeForm_oneForm_left`, `wedgeForm_oneForm_right`: **compatibility with
  `Feec.ExteriorFibre.wedge`** for `1`-forms, `ξ^♭ ∧ ω = ξ ∧ ω = (-1)^k ω ∧ ξ^♭`;
* `Feec.Koszul.extDeriv_wedgeForm`: **the Leibniz rule** `d (ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη`
  for polynomial forms.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (the exterior algebra and the exterior derivative)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset

@[expose] public noncomputable section

namespace Feec.ExteriorFibre

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d]

/-! ### Shuffle signs -/

/-- The sign `ε(s, t) = ∏_{a ∈ s} ε(a, t) = (-1)^{#{(a, b) ∈ s × t | b < a}}` of the shuffle
`dx_s ∧ dx_t = ε(s, t) dx_{s ∪ t}` (`s`, `t` disjoint). -/
def shuffleSgn (s t : Finset d) : R := ∏ a ∈ s, sgn a t

@[simp] theorem shuffleSgn_empty_left (t : Finset d) : (shuffleSgn ∅ t : R) = 1 := by
  simp [shuffleSgn]

@[simp] theorem shuffleSgn_empty_right (s : Finset d) : (shuffleSgn s ∅ : R) = 1 := by
  simp [shuffleSgn, sgn]

theorem shuffleSgn_singleton_left (j : d) (t : Finset d) :
    (shuffleSgn {j} t : R) = sgn j t := by
  simp [shuffleSgn]

theorem shuffleSgn_insert_left {j : d} {s : Finset d} (hj : j ∉ s) (t : Finset d) :
    (shuffleSgn (insert j s) t : R) = sgn j t * shuffleSgn s t := by
  rw [shuffleSgn, prod_insert hj]; rfl

theorem sgn_sq (j : d) (s : Finset d) : (sgn j s : R) ^ 2 = 1 := by
  rw [sq, sgn_mul_self]

theorem shuffleSgn_mul_self (s t : Finset d) : (shuffleSgn s t : R) * shuffleSgn s t = 1 := by
  rw [shuffleSgn, ← prod_mul_distrib]
  exact prod_eq_one fun a _ => sgn_mul_self a t

/-- `∏_{b ∈ t} (if a < b then -1 else 1) = (-1)^{#{b ∈ t | a < b}}`. -/
theorem prod_ite_lt (a : d) (t : Finset d) :
    (∏ b ∈ t, (if a < b then -1 else 1 : R)) = (-1) ^ #({b ∈ t | a < b}) := by
  rw [prod_ite, prod_const_one, mul_one, prod_const]

/-- For `a ∉ t`: `ε(a, t) ∏_{b ∈ t} (if a < b then -1 else 1) = (-1)^{#t}`. -/
theorem sgn_mul_prod_ite_lt {a : d} {t : Finset d} (ha : a ∉ t) :
    (sgn a t : R) * ∏ b ∈ t, (if a < b then -1 else 1 : R) = (-1) ^ #t := by
  rw [prod_ite_lt, sgn, ← pow_add]
  congr 1
  rw [← card_filter_add_card_filter_not (s := t) (p := fun b => b < a)]
  congr 1
  congr 1
  ext b
  simp only [mem_filter, not_lt]
  constructor
  · rintro ⟨hb, h⟩; exact ⟨hb, h.le⟩
  · rintro ⟨hb, h⟩
    exact ⟨hb, lt_of_le_of_ne h fun e => ha (e ▸ hb)⟩

theorem shuffleSgn_insert_right {j : d} {t : Finset d} (hj : j ∉ t) (s : Finset d) :
    (shuffleSgn s (insert j t) : R) =
      (∏ a ∈ s, (if j < a then -1 else 1 : R)) * shuffleSgn s t := by
  rw [shuffleSgn, shuffleSgn, ← prod_mul_distrib]
  exact prod_congr rfl fun a _ => sgn_insert hj

/-- **Graded commutativity of shuffles**: `ε(s, t) ε(t, s) = (-1)^{#s #t}` for disjoint `s`, `t`. -/
theorem shuffleSgn_mul_shuffleSgn {s t : Finset d} (h : Disjoint s t) :
    (shuffleSgn s t : R) * shuffleSgn t s = (-1) ^ (#s * #t) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hat : a ∉ t := fun hm => disjoint_left.1 h (mem_insert_self a s) hm
    have hst : Disjoint s t := disjoint_of_subset_left (subset_insert a s) h
    rw [shuffleSgn_insert_left ha, shuffleSgn_insert_right ha, card_insert_of_notMem ha,
      add_mul, one_mul, pow_add, ← ih hst, ← sgn_mul_prod_ite_lt hat]
    ring

theorem sgn_union {j : d} {s t : Finset d} (h : Disjoint s t) :
    (sgn j (s ∪ t) : R) = sgn j s * sgn j t := by
  rw [sgn, sgn, sgn, filter_union, card_union_of_disjoint (disjoint_filter_filter h), pow_add]

/-- For `j ∉ s`: `(-1)^{#{i ∈ s | j < i}} = (-1)^{#s} ε(j, s)`. -/
theorem prod_ite_lt_eq {j : d} {s : Finset d} (hj : j ∉ s) :
    (∏ i ∈ s, (if j < i then -1 else 1 : R)) = (-1) ^ #s * sgn j s := by
  have h := sgn_mul_prod_ite_lt (R := R) hj
  rw [← h, mul_comm (sgn j s : R), mul_assoc, sgn_mul_self, mul_one]

/-! ### The exterior product -/

/-- The **exterior product** of coefficient forms,
`(ω ∧ η)_u = Σ_{s ⊆ u} ε(s, u ∖ s) ω_s η_{u ∖ s}`. -/
def wedgeForm (ω η : Finset d → R) : Finset d → R :=
  fun u => ∑ s ∈ u.powerset, shuffleSgn s (u \ s) * ω s * η (u \ s)

theorem wedgeForm_apply (ω η : Finset d → R) (u : Finset d) :
    wedgeForm ω η u = ∑ s ∈ u.powerset, shuffleSgn s (u \ s) * ω s * η (u \ s) := rfl

@[simp] theorem wedgeForm_zero_left (η : Finset d → R) : wedgeForm 0 η = 0 := by
  funext u; simp [wedgeForm_apply]

@[simp] theorem wedgeForm_zero_right (ω : Finset d → R) : wedgeForm ω 0 = 0 := by
  funext u; simp [wedgeForm_apply]

theorem wedgeForm_add_left (ω ω' η : Finset d → R) :
    wedgeForm (ω + ω') η = wedgeForm ω η + wedgeForm ω' η := by
  funext u; simp [wedgeForm_apply, mul_add, add_mul, sum_add_distrib]

theorem wedgeForm_add_right (ω η η' : Finset d → R) :
    wedgeForm ω (η + η') = wedgeForm ω η + wedgeForm ω η' := by
  funext u; simp [wedgeForm_apply, mul_add, sum_add_distrib]

theorem wedgeForm_smul_left (c : R) (ω η : Finset d → R) :
    wedgeForm (c • ω) η = c • wedgeForm ω η := by
  funext u; simp only [wedgeForm_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

theorem wedgeForm_smul_right (c : R) (ω η : Finset d → R) :
    wedgeForm ω (c • η) = c • wedgeForm ω η := by
  funext u; simp only [wedgeForm_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

theorem wedgeForm_neg_left (ω η : Finset d → R) : wedgeForm (-ω) η = -wedgeForm ω η := by
  rw [show -ω = (-1 : R) • ω by simp, wedgeForm_smul_left]; simp

theorem wedgeForm_sum_left {ι : Type*} (u : Finset ι) (ω : ι → Finset d → R) (η : Finset d → R) :
    wedgeForm (∑ i ∈ u, ω i) η = ∑ i ∈ u, wedgeForm (ω i) η := by
  funext v; simp only [wedgeForm_apply, Finset.sum_apply, mul_sum, sum_mul]
  exact sum_comm

theorem wedgeForm_sum_right {ι : Type*} (u : Finset ι) (ω : Finset d → R) (η : ι → Finset d → R) :
    wedgeForm ω (∑ i ∈ u, η i) = ∑ i ∈ u, wedgeForm ω (η i) := by
  funext v; simp only [wedgeForm_apply, Finset.sum_apply, mul_sum]
  exact sum_comm

/-- The unit `dx_∅ = 1` is a left identity. -/
@[simp] theorem wedgeForm_one_left (ω : Finset d → R) : wedgeForm (Pi.single ∅ 1) ω = ω := by
  funext u
  rw [wedgeForm_apply, sum_eq_single ∅ (fun s _ hs => by simp [hs]) (by simp)]
  simp

/-- The unit `dx_∅ = 1` is a right identity. -/
@[simp] theorem wedgeForm_one_right (ω : Finset d → R) : wedgeForm ω (Pi.single ∅ 1) = ω := by
  funext u
  rw [wedgeForm_apply, sum_eq_single u (fun s hs hsu => ?_) (by simp)]
  · simp
  · have : u \ s ≠ ∅ := fun h =>
      hsu (le_antisymm (mem_powerset.1 hs) (sdiff_eq_empty_iff_subset.1 h))
    simp [this]

/-- Degrees add: the exterior product of a `k`-form and an `l`-form is a `(k + l)`-form. -/
theorem IsDeg.wedgeForm {k l : ℕ} {ω η : Finset d → R} (hω : IsDeg k ω) (hη : IsDeg l η) :
    IsDeg (k + l) (wedgeForm ω η) := by
  intro u hu
  refine sum_eq_zero fun s hs => ?_
  by_cases hk : #s = k
  · have hsu := card_le_card (mem_powerset.1 hs)
    have : #(u \ s) ≠ l := by
      rw [card_sdiff_of_subset (mem_powerset.1 hs)]; omega
    rw [hη _ this, mul_zero]
  · rw [hω s hk, mul_zero, zero_mul]

/-- **Graded commutativity** `η ∧ ω = (-1)^{kl} ω ∧ η` for a `k`-form `ω` and an `l`-form `η`.
[AFW2006], §2 -/
theorem wedgeForm_comm {k l : ℕ} {ω η : Finset d → R} (hω : IsDeg k ω) (hη : IsDeg l η) :
    wedgeForm η ω = (-1 : R) ^ (k * l) • wedgeForm ω η := by
  funext u
  rw [Pi.smul_apply, smul_eq_mul, wedgeForm_apply, wedgeForm_apply, mul_sum]
  refine sum_nbij' (fun s => u \ s) (fun s => u \ s) (fun s hs => by simp)
    (fun s hs => by simp) (fun s hs => Finset.sdiff_sdiff_eq_self (mem_powerset.1 hs))
    (fun s hs => Finset.sdiff_sdiff_eq_self (mem_powerset.1 hs)) fun s hs => ?_
  have hsu := mem_powerset.1 hs
  rw [Finset.sdiff_sdiff_eq_self hsu]
  by_cases hl : #s = l
  · by_cases hk : #(u \ s) = k
    · have h := shuffleSgn_mul_shuffleSgn (R := R) (disjoint_sdiff : Disjoint s (u \ s))
      rw [hk, hl, mul_comm l k] at h
      have h2 := shuffleSgn_mul_self (R := R) (u \ s) s
      linear_combination (-(shuffleSgn s (u \ s) * η s * ω (u \ s))) * h2 +
        (shuffleSgn (u \ s) s * ω (u \ s) * η s) * h
    · rw [hω _ hk]; ring
  · rw [hη _ hl]; ring

/-- The product of two basis forms: `(a dx_s ∧ b dx_t)_u = ε(s, t) a b` if `u = s ⊔ t`, else `0`. -/
theorem wedgeForm_single_single_apply (s t u : Finset d) (a b : R) :
    wedgeForm (Pi.single s a) (Pi.single t b) u =
      if s ⊆ u ∧ u \ s = t then shuffleSgn s t * a * b else 0 := by
  rw [wedgeForm_apply]
  split_ifs with h
  · rw [sum_eq_single s (fun s' _ hs' => by simp [hs']) (fun hs => absurd (mem_powerset.2 h.1) hs),
      h.2]
    simp
  · refine sum_eq_zero fun s' hs' => ?_
    by_cases hs : s' = s
    · subst hs
      have : u \ s' ≠ t := fun e => h ⟨mem_powerset.1 hs', e⟩
      simp [this]
    · simp [hs]

/-! ### Exterior multiplication by a covector -/

/-- Reindexing pairs `j ∈ s' ⊆ u` as `(j, s' ∖ j)`. -/
theorem sum_powerset_sum_mem {M : Type*} [AddCommMonoid M] (u : Finset d)
    (F : Finset d → d → M) :
    ∑ s' ∈ u.powerset, ∑ j ∈ s', F s' j =
      ∑ j ∈ u, ∑ s ∈ (u.erase j).powerset, F (insert j s) j := by
  rw [sum_comm' (t' := u) (s' := fun j => u.powerset.filter (j ∈ ·))]
  · refine sum_congr rfl fun j hj => ?_
    refine sum_nbij' (fun s' => s'.erase j) (fun s => insert j s) ?_ ?_ ?_ ?_ ?_
    · intro s' hs'
      simp only [mem_filter, mem_powerset] at hs'
      simpa using erase_subset_erase j hs'.1
    · intro s hs
      simp only [mem_powerset, subset_erase] at hs
      simp only [mem_filter, mem_powerset]
      exact ⟨insert_subset hj hs.1, mem_insert_self j s⟩
    · intro s' hs'
      exact insert_erase (mem_filter.1 hs').2
    · intro s hs
      exact erase_insert (fun h => notMem_erase j u (mem_powerset.1 hs h))
    · intro s' hs'
      rw [insert_erase (mem_filter.1 hs').2]
  · intro s' j
    simp only [mem_powerset, mem_filter]
    exact ⟨fun h => ⟨h, h.1 h.2⟩, fun h => h.1⟩

theorem sdiff_insert_eq_erase_sdiff (u s : Finset d) (j : d) :
    u \ insert j s = u.erase j \ s := by
  ext x; simp only [mem_sdiff, mem_insert, mem_erase, not_or]; tauto

/-- **Associativity** `ξ ∧ (ω ∧ η) = (ξ ∧ ω) ∧ η` for a covector `ξ`. -/
theorem wedge_wedgeForm (ξ : d → R) (ω η : Finset d → R) :
    wedge ξ (wedgeForm ω η) = wedgeForm (wedge ξ ω) η := by
  funext u
  simp only [wedge_apply, wedgeForm_apply, mul_sum, sum_mul]
  rw [sum_powerset_sum_mem u (fun s' j => shuffleSgn s' (u \ s') * (sgn j s' * ξ j *
    ω (s'.erase j)) * η (u \ s'))]
  refine sum_congr rfl fun j hj => sum_congr rfl fun s hs => ?_
  have hjs : j ∉ s := fun h => notMem_erase j u (mem_powerset.1 hs h)
  have hsu : s ⊆ u.erase j := mem_powerset.1 hs
  rw [sdiff_insert_eq_erase_sdiff, erase_insert hjs, sgn_insert_self,
    shuffleSgn_insert_left hjs, ← sgn_erase_self j u,
    ← union_sdiff_of_subset hsu, sgn_union disjoint_sdiff, union_sdiff_of_subset hsu]
  ring

/-- Reindexing pairs `s ⊆ u`, `j ∈ u ∖ s` as `j ∈ u`, `s ⊆ u ∖ j`. -/
theorem sum_powerset_sum_sdiff {M : Type*} [AddCommMonoid M] (u : Finset d)
    (F : Finset d → d → M) :
    ∑ s ∈ u.powerset, ∑ j ∈ u \ s, F s j = ∑ j ∈ u, ∑ s ∈ (u.erase j).powerset, F s j := by
  refine sum_comm' fun s j => ?_
  simp only [mem_powerset, mem_sdiff, subset_erase]
  constructor
  · rintro ⟨hs, hj, hjs⟩; exact ⟨⟨hs, hjs⟩, hj⟩
  · rintro ⟨⟨hs, hjs⟩, hj⟩; exact ⟨hs, hj, hjs⟩

/-- **Associativity, graded**: `ξ ∧ (ω ∧ η) = (-1)^k ω ∧ (ξ ∧ η)` for a covector `ξ` and a
`k`-form `ω`. -/
theorem wedge_wedgeForm_right (ξ : d → R) {k : ℕ} {ω : Finset d → R} (hω : IsDeg k ω)
    (η : Finset d → R) :
    wedge ξ (wedgeForm ω η) = (-1 : R) ^ k • wedgeForm ω (wedge ξ η) := by
  funext u
  simp only [Pi.smul_apply, smul_eq_mul, wedge_apply, wedgeForm_apply, mul_sum]
  rw [sum_powerset_sum_sdiff u (fun s j => (-1) ^ k * (shuffleSgn s (u \ s) * ω s *
    (sgn j (u \ s) * ξ j * η ((u \ s).erase j))))]
  refine sum_congr rfl fun j hj => sum_congr rfl fun s hs => ?_
  have hjs : j ∉ s := fun h => notMem_erase j u (mem_powerset.1 hs h)
  have hsu : s ⊆ u.erase j := mem_powerset.1 hs
  have ht : j ∉ u.erase j \ s := fun h => notMem_erase j u (mem_sdiff.1 h).1
  have hus : u \ s = insert j (u.erase j \ s) := by
    rw [← sdiff_insert_eq_erase_sdiff]
    ext x
    simp only [mem_sdiff, mem_insert]
    constructor
    · rintro ⟨hx, hxs⟩
      by_cases hxj : x = j
      · exact Or.inl hxj
      · exact Or.inr ⟨hx, fun h => h.elim hxj hxs⟩
    · rintro (rfl | ⟨hx, hxs⟩)
      · exact ⟨hj, hjs⟩
      · exact ⟨hx, fun h => hxs (Or.inr h)⟩
  by_cases hk : #s = k
  · rw [hus, erase_insert ht, sgn_insert_self, shuffleSgn_insert_right ht,
      prod_ite_lt_eq hjs, hk, ← sgn_erase_self j u, ← union_sdiff_of_subset hsu,
      sgn_union disjoint_sdiff, union_sdiff_of_subset hsu]
    have h1 : ((-1 : R) ^ k) * (-1) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    linear_combination (-(sgn j s * sgn j (u.erase j \ s) * ξ j *
      (shuffleSgn s (u.erase j \ s) * ω s * η (u.erase j \ s)))) * h1
  · rw [hω s hk]; ring

/-! ### Associativity -/

theorem shuffleSgn_union_left {s t : Finset d} (h : Disjoint s t) (v : Finset d) :
    (shuffleSgn (s ∪ t) v : R) = shuffleSgn s v * shuffleSgn t v := by
  rw [shuffleSgn, prod_union h]; rfl

theorem shuffleSgn_union_right (s : Finset d) {t v : Finset d} (h : Disjoint t v) :
    (shuffleSgn s (t ∪ v) : R) = shuffleSgn s t * shuffleSgn s v := by
  rw [shuffleSgn, shuffleSgn, shuffleSgn, ← prod_mul_distrib]
  exact prod_congr rfl fun a _ => sgn_union h

/-- Reindexing pairs `s ⊆ a ⊆ u` as `s ⊆ u`, `t ⊆ u ∖ s` (with `a = s ∪ t`). -/
theorem sum_powerset_sum_powerset {M : Type*} [AddCommMonoid M] (u : Finset d)
    (F : Finset d → Finset d → M) :
    ∑ a ∈ u.powerset, ∑ s ∈ a.powerset, F a s =
      ∑ s ∈ u.powerset, ∑ t ∈ (u \ s).powerset, F (s ∪ t) s := by
  rw [sum_comm' (t' := u.powerset) (s' := fun s => u.powerset.filter (s ⊆ ·))]
  · refine sum_congr rfl fun s hs => ?_
    refine sum_nbij' (fun a => a \ s) (fun t => s ∪ t) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_powerset] at ha
      simpa using sdiff_subset_sdiff ha.1 (subset_refl s)
    · intro t ht
      simp only [mem_powerset, subset_sdiff] at ht
      simp only [mem_filter, mem_powerset]
      exact ⟨union_subset (mem_powerset.1 hs) ht.1, subset_union_left⟩
    · intro a ha
      exact union_sdiff_of_subset (mem_filter.1 ha).2
    · intro t ht
      exact union_sdiff_cancel_left (subset_sdiff.1 (mem_powerset.1 ht)).2.symm
    · intro a ha
      rw [union_sdiff_of_subset (mem_filter.1 ha).2]
  · intro a s
    simp only [mem_powerset, mem_filter]
    exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2.trans h.1⟩, fun h => ⟨h.1.1, h.1.2⟩⟩

/-- **Associativity** of the exterior product, `(ω ∧ η) ∧ ζ = ω ∧ (η ∧ ζ)`. -/
theorem wedgeForm_assoc (ω η ζ : Finset d → R) :
    wedgeForm (wedgeForm ω η) ζ = wedgeForm ω (wedgeForm η ζ) := by
  funext u
  simp only [wedgeForm_apply, mul_sum, sum_mul]
  rw [sum_powerset_sum_powerset u (fun a s => shuffleSgn a (u \ a) *
    (shuffleSgn s (a \ s) * ω s * η (a \ s)) * ζ (u \ a))]
  refine sum_congr rfl fun s hs => sum_congr rfl fun t ht => ?_
  have hsu : s ⊆ u := mem_powerset.1 hs
  have hts : Disjoint s t := (subset_sdiff.1 (mem_powerset.1 ht)).2.symm
  have htu : t ⊆ u \ s := mem_powerset.1 ht
  have h1 : (s ∪ t) \ s = t := union_sdiff_cancel_left hts
  have h2 : u \ (s ∪ t) = (u \ s) \ t := by
    ext x; simp only [mem_sdiff, mem_union, not_or]; tauto
  have hv : Disjoint t ((u \ s) \ t) := disjoint_sdiff
  have h3 : u \ s = t ∪ ((u \ s) \ t) := (union_sdiff_of_subset htu).symm
  rw [h1, h2, shuffleSgn_union_left hts, h3, shuffleSgn_union_right s hv, ← h3]
  ring

/-- A covector `ξ` as the `1`-form `Σⱼ ξⱼ dxⱼ = ξ ∧ 1`. -/
def oneForm (ξ : d → R) : Finset d → R := wedge ξ (Pi.single ∅ 1)

theorem oneForm_singleton (ξ : d → R) (j : d) : oneForm ξ {j} = ξ j := by
  simp [oneForm, wedge_apply, sgn, filter_singleton]

theorem isDeg_oneForm (ξ : d → R) : IsDeg 1 (oneForm ξ) := by
  have h : IsDeg 0 (Pi.single ∅ (1 : R) : Finset d → R) := fun s hs => by
    rw [Pi.single_apply]
    simp only [ite_eq_right_iff]
    intro h; exact absurd (by rw [h, card_empty]) hs
  exact h.wedge ξ

/-- **Compatibility with exterior multiplication by a covector**: `ξ^♭ ∧ ω = ξ ∧ ω`. -/
theorem wedgeForm_oneForm_left (ξ : d → R) (ω : Finset d → R) :
    wedgeForm (oneForm ξ) ω = wedge ξ ω := by
  rw [oneForm, ← wedge_wedgeForm, wedgeForm_one_left]

/-- `ω ∧ ξ^♭ = (-1)^k ξ ∧ ω` for a `k`-form `ω`. -/
theorem wedgeForm_oneForm_right (ξ : d → R) {k : ℕ} {ω : Finset d → R} (hω : IsDeg k ω) :
    wedgeForm ω (oneForm ξ) = (-1 : R) ^ k • wedge ξ ω := by
  have h := wedge_wedgeForm_right ξ hω (Pi.single ∅ 1)
  rw [wedgeForm_one_right] at h
  rw [h, smul_smul, ← pow_add, ← two_mul, pow_mul]
  simp [oneForm]

end Feec.ExteriorFibre

namespace Feec.Koszul

open ExteriorFibre MvPolynomial

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d]

/-! ### The Leibniz rule for polynomial forms -/

/-- The coefficientwise partial derivative `∂ⱼ ω` of a polynomial form. -/
def pderivForm (j : d) (ω : PolyForm R d) : PolyForm R d := fun s => pderiv j (ω s)

omit [LinearOrder d] in
theorem isDeg_pderivForm {k : ℕ} {ω : PolyForm R d} (h : IsDeg k ω) (j : d) :
    IsDeg k (pderivForm j ω) := fun s hs => by simp [Koszul.pderivForm, h s hs]

/-- `d = Σⱼ dxⱼ ∧ ∂ⱼ` on polynomial forms. -/
theorem extDeriv_eq_sum_wedge [Fintype d] (ω : PolyForm R d) :
    extDeriv ω = ∑ j, wedge (Pi.single j 1) (pderivForm j ω) := by
  funext s
  simp only [extDeriv_apply, Finset.sum_apply, wedge_apply, pderivForm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

theorem shuffleSgn_eq_C (s t : Finset d) :
    (shuffleSgn s t : MvPolynomial d R) = C (shuffleSgn s t) := by
  simp [shuffleSgn, sgn, map_prod]

/-- `∂ⱼ` is a derivation of the exterior product. -/
theorem pderivForm_wedgeForm (j : d) (ω η : PolyForm R d) :
    pderivForm j (wedgeForm ω η) = wedgeForm (pderivForm j ω) η + wedgeForm ω (pderivForm j η) := by
  funext u
  simp only [pderivForm, wedgeForm_apply, Pi.add_apply, map_sum, ← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  rw [shuffleSgn_eq_C, mul_assoc, pderiv_C_mul, pderiv_mul]
  ring

/-- **The Leibniz rule** `d (ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη` for a polynomial `k`-form `ω`.
[AFW2006], §2 -/
theorem extDeriv_wedgeForm [Fintype d] {k : ℕ} {ω : PolyForm R d} (hω : IsDeg k ω)
    (η : PolyForm R d) :
    extDeriv (wedgeForm ω η) =
      wedgeForm (extDeriv ω) η + (-1 : MvPolynomial d R) ^ k • wedgeForm ω (extDeriv η) := by
  rw [extDeriv_eq_sum_wedge, extDeriv_eq_sum_wedge, extDeriv_eq_sum_wedge, wedgeForm_sum_left,
    wedgeForm_sum_right, Finset.smul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [pderivForm_wedgeForm, wedge_add, wedge_wedgeForm,
    wedge_wedgeForm_right _ hω]

end Feec.Koszul
