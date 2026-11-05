module

public import Feec.FiniteElement.PolyComplex
public import Feec.FiniteElement.LocalSpace
public import Feec.Counterexamples.PolynomialForms

/-!
# Regression test: the trimmed spaces `P_r⁻Λᵏ` with `P_0⁻Λᵏ = 0`

`Feec.Koszul.polyFormMinus r k` was `P_{r-1}Λᵏ + κ H_{r-1}Λ^{k+1}` for every `r`, so that at
`r = 0` the truncation `0 - 1 = 0` gave `P_1⁻Λᵏ`; `Feec.FiniteElement.PolyKind.form₀` kept the
convention `P_0⁻Λᵏ = 0` of [AFW2006], §3.3 for the admissible sequences. `polyFormMinus` now has
that convention (`polyFormMinus_zero_left`), the old space `polyFormMinus r k` is the new
`polyFormMinus (r - 1 + 1) k` (`polyFormMinus_old`), and `form₀` is `PolyKind.form`.

The theorems below state the old results and derive them from the new ones: verbatim where the
statement does not mention `P_0⁻Λ`, and otherwise with `polyFormMinus (r - 1 + 1)` for the old
`polyFormMinus r` (the old `form₀` is restated here as `form₀_old`). Every other statement of
`Feec` about `polyFormMinus r` for all `r` reads at `r = 0` with `P_0⁻Λ = 0`; its old content is
its instance at `r - 1 + 1`.

With `P_0⁻Λ = 0` the hypothesis `r ≥ 1` of several results became unnecessary and was dropped
(`Koszul.polyFormMinus_le_polyForm`, `Koszul.exists_extDeriv_eq_of_mem_polyFormMinus`,
`PolyKind.form_le_polyForm`, …); their earlier statements are restated below with the unused
hypothesis `_hr`. `Koszul.polyFormMinus_zero` (`k = 0`) is now `Koszul.polyFormMinus_zero_right`,
beside `Koszul.polyFormMinus_zero_left` (`r = 0`), and the duplicate
`Counterexamples.PolynomialForms.koszul_mem_polyForm_of_mem_polyFormMinus` was removed in favour
of `Koszul.koszul_mem_polyForm_of_mem_polyFormMinus_succ`.

This file is part of the `FeecCheck` library, not of `Feec`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.3, §3.5, (5.13)

Bibliography: [references.bib](../../docs/references.bib)
-/

public section

namespace FeecCheck.TrimmedForms

open Feec Feec.FiniteElement
open Koszul (PolyForm homForm polyForm polyFormMinus koszulₗ)

section Koszul

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d] [Fintype d]

/-- The earlier definition of `polyFormMinus r k` is `polyFormMinus (r - 1 + 1) k`. -/
theorem polyFormMinus_old (r k : ℕ) :
    polyForm R d (r - 1) k ⊔ (homForm R d (r - 1) (k + 1)).map (koszulₗ R d) =
      polyFormMinus R d (r - 1 + 1) k :=
  rfl

/-- The earlier `Koszul.polyForm_le_polyFormMinus` (every `r`). -/
theorem polyForm_le_polyFormMinus_old (r k : ℕ) :
    polyForm R d (r - 1) k ≤ polyFormMinus R d (r - 1 + 1) k :=
  le_sup_left

/-- The earlier `Koszul.extDeriv_mem_polyForm_of_mem_polyFormMinus` (`r ≥ 1`), verbatim. -/
theorem extDeriv_mem_polyForm_of_mem_polyFormMinus_old {r k : ℕ} (_hr : 1 ≤ r)
    {ω : PolyForm R d} (h : ω ∈ polyFormMinus R d r k) :
    Koszul.extDeriv ω ∈ polyForm R d (r - 1) (k + 1) :=
  Koszul.extDeriv_mem_polyForm_of_mem_polyFormMinus h

/-- The earlier `Koszul.extDeriv_mem_polyFormMinus` (`r ≥ 1`), verbatim. -/
theorem extDeriv_mem_polyFormMinus_old {r k : ℕ} (_hr : 1 ≤ r) {ω : PolyForm R d}
    (h : ω ∈ polyFormMinus R d r k) : Koszul.extDeriv ω ∈ polyFormMinus R d r (k + 1) :=
  Koszul.extDeriv_mem_polyFormMinus h

/-- The earlier `Koszul.extDeriv_mem_polyForm_sub_one_of_mem_polyFormMinus` (every `r`). -/
theorem extDeriv_mem_polyForm_sub_one_of_mem_polyFormMinus_old {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ polyFormMinus R d (r - 1 + 1) k) :
    Koszul.extDeriv ω ∈ polyForm R d (r - 1) (k + 1) :=
  Koszul.extDeriv_mem_polyForm_of_mem_polyFormMinus (r := r - 1 + 1) h

/-- The earlier `Koszul.extDeriv_mem_polyFormMinus_of_mem_polyFormMinus` (every `r`). -/
theorem extDeriv_mem_polyFormMinus_of_mem_polyFormMinus_old {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ polyFormMinus R d (r - 1 + 1) k) :
    Koszul.extDeriv ω ∈ polyFormMinus R d (r - 1 + 1) (k + 1) :=
  Koszul.extDeriv_mem_polyFormMinus h

/-- The earlier `Koszul.extDeriv_mem_polyFormMinus_of_mem_polyForm` (every `r`). -/
theorem extDeriv_mem_polyFormMinus_of_mem_polyForm_old {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ polyForm R d r k) : Koszul.extDeriv ω ∈ polyFormMinus R d (r - 1 + 1) (k + 1) :=
  polyForm_le_polyFormMinus_old r (k + 1) (Koszul.extDeriv_mem_polyForm h)

/-- The earlier `Koszul.isSubcomplex_polyForm` (every `r`). -/
theorem isSubcomplex_polyForm_old (r k : ℕ) :
    Koszul.IsSubcomplex (polyForm R d (r + 1) k) (polyForm R d r (k + 1))
        (polyForm R d (r - 1) (k + 2)) ∧
      Koszul.IsSubcomplex (polyForm R d (r + 1) k) (polyForm R d r (k + 1))
        (polyFormMinus R d (r - 1 + 1) (k + 2)) ∧
      Koszul.IsSubcomplex (polyForm R d r k) (polyFormMinus R d (r - 1 + 1) (k + 1))
        (polyForm R d (r - 1) (k + 2)) ∧
      Koszul.IsSubcomplex (polyForm R d r k) (polyFormMinus R d (r - 1 + 1) (k + 1))
        (polyFormMinus R d (r - 1 + 1) (k + 2)) := by
  have h0 := (Koszul.isSubcomplex_polyForm (R := R) (d := d) r k).1
  refine ⟨h0, ⟨h0.1, fun _ hω => extDeriv_mem_polyFormMinus_of_mem_polyForm_old hω⟩,
    ⟨fun _ hω => extDeriv_mem_polyFormMinus_of_mem_polyForm_old hω,
      fun _ hω => extDeriv_mem_polyForm_sub_one_of_mem_polyFormMinus_old hω⟩,
    ⟨fun _ hω => extDeriv_mem_polyFormMinus_of_mem_polyForm_old hω,
      fun _ hω => extDeriv_mem_polyFormMinus_of_mem_polyFormMinus_old hω⟩⟩

/-- The earlier helper `Koszul.extDeriv_koszul_mem_homForm` (of the removed
`extDeriv_mem_polyForm_sub_one_of_mem_polyFormMinus`), verbatim. -/
theorem extDeriv_koszul_mem_homForm_old {r k : ℕ} {η : PolyForm R d}
    (h : η ∈ homForm R d (r - 1) (k + 1)) :
    Koszul.extDeriv (Koszul.koszul η) ∈ homForm R d (r - 1) (k + 1) := by
  have h1 := Koszul.koszul_mem_homForm h
  rw [Nat.add_sub_cancel] at h1
  have := Koszul.extDeriv_mem_homForm h1
  rwa [Nat.add_sub_cancel] at this

omit [Fintype d] in
/-- The earlier `Koszul.extDeriv_eq_zero_of_mem_polyForm_zero` over a field, verbatim. -/
theorem extDeriv_eq_zero_of_mem_polyForm_zero_old {K : Type*} [Field K] {k : ℕ}
    {ω : PolyForm K d} (h : ω ∈ polyForm K d 0 k) : Koszul.extDeriv ω = 0 :=
  Koszul.extDeriv_eq_zero_of_mem_polyForm_zero h

end Koszul

/-- The earlier `Koszul.koszul_mem_polyFormMinus` (every `r`). -/
theorem koszul_mem_polyFormMinus_old {K : Type*} [Field K] {d : Type*} [LinearOrder d]
    [Fintype d] {r k : ℕ} {ω : PolyForm K d} (h : ω ∈ polyForm K d (r - 1) (k + 1)) :
    Koszul.koszul ω ∈ polyFormMinus K d (r - 1 + 1) k :=
  Koszul.koszul_mem_polyFormMinus (by omega) (by simpa using h)

/-- The earlier `polySpace_le_polyMinusSpace` (every `r`). -/
theorem polySpace_le_polyMinusSpace_old {n : ℕ} (r k : ℕ) :
    polySpace n (r - 1) k ≤ polyMinusSpace n (r - 1 + 1) k := by
  simpa using polySpace_le_polyMinusSpace (n := n) (r := r - 1 + 1) (by omega) k

section PolyKind

variable {n : ℕ}

/-- The earlier `PolyKind.exists_extDeriv_eq` (`r ≥ 1`), verbatim. -/
theorem exists_extDeriv_eq_old {K : Type*} [Field K] [CharZero K] (κ : PolyKind) {r : ℕ}
    (_hr : 1 ≤ r) {κ' : PolyKind} {r' : ℕ} (ht : PolyKind.Transition r κ' r') {k : ℕ}
    {ω : PolyForm K (Fin n)} (hω : ω ∈ κ'.form K r' (k + 1)) (hd : Koszul.extDeriv ω = 0) :
    ∃ η ∈ κ.form K r k, Koszul.extDeriv η = ω :=
  κ.exists_extDeriv_eq ht hω hd

variable (K : Type*) [CommRing K]

/-- The earlier `PolyKind.form₀`, verbatim: the families with `P_0⁻Λᵏ = 0`. -/
noncomputable def form₀_old : PolyKind → ℕ → ℕ → Submodule K (PolyForm K (Fin n))
  | .full, r, k => polyForm K (Fin n) r k
  | .trimmed, 0, _ => ⊥
  | .trimmed, r + 1, k => polyFormMinus K (Fin n) (r + 1) k

variable {K}

/-- `form₀` is now `PolyKind.form`. -/
theorem form₀_old_eq (κ : PolyKind) (r k : ℕ) : form₀_old K (n := n) κ r k = κ.form K r k := by
  cases κ <;> cases r <;> rfl

/-- The earlier `PolyKind.form₀_of_one_le`. -/
theorem form₀_of_one_le_old (κ : PolyKind) {r : ℕ} (_hr : 1 ≤ r) (k : ℕ) :
    form₀_old K (n := n) κ r k = κ.form K r k :=
  form₀_old_eq κ r k

/-- The earlier `PolyKind.extDeriv_mem_form₀`. -/
theorem extDeriv_mem_form₀_old (κ : PolyKind) {r : ℕ} {κ' : PolyKind} {r' : ℕ}
    (ht : PolyKind.Transition r κ' r') {k : ℕ} {ω : PolyForm K (Fin n)}
    (hω : ω ∈ form₀_old K κ r k) : Koszul.extDeriv ω ∈ form₀_old K κ' r' (k + 1) := by
  rw [form₀_old_eq] at hω ⊢
  exact κ.extDeriv_mem_form ht hω

/-- The earlier `PolyKind.exists_extDeriv_eq_of_mem_form₀`. -/
theorem exists_extDeriv_eq_of_mem_form₀_old {K : Type*} [Field K] [CharZero K] (κ : PolyKind)
    {r : ℕ} {κ' : PolyKind} {r' : ℕ} (ht : PolyKind.Transition r κ' r') {k : ℕ}
    {ω : PolyForm K (Fin n)} (hω : ω ∈ form₀_old K κ' r' (k + 1)) (hd : Koszul.extDeriv ω = 0) :
    ∃ η ∈ form₀_old K κ r k, Koszul.extDeriv η = ω := by
  rw [form₀_old_eq] at hω ⊢
  exact κ.exists_extDeriv_eq ht hω hd

/-- The earlier `PolyKind.IsAdmissible.extDeriv_mem` (over a field, with `form₀`). -/
theorem isAdmissible_extDeriv_mem_old {K : Type*} [Field K] {κ : ℕ → PolyKind} {r : ℕ → ℕ}
    (h : PolyKind.IsAdmissible κ r) {k : ℕ} {ω : PolyForm K (Fin n)}
    (hω : ω ∈ form₀_old K (κ k) (r k) k) :
    Koszul.extDeriv ω ∈ form₀_old K (κ (k + 1)) (r (k + 1)) (k + 1) :=
  extDeriv_mem_form₀_old (κ k) (h.transition k) hω

/-- The earlier `PolyKind.IsAdmissible.exists_extDeriv_eq` (with `form₀`). -/
theorem isAdmissible_exists_extDeriv_eq_old {K : Type*} [Field K] [CharZero K]
    {κ : ℕ → PolyKind} {r : ℕ → ℕ} (h : PolyKind.IsAdmissible κ r) {k : ℕ}
    {ω : PolyForm K (Fin n)} (hω : ω ∈ form₀_old K (κ (k + 1)) (r (k + 1)) (k + 1))
    (hd : Koszul.extDeriv ω = 0) : ∃ η ∈ form₀_old K (κ k) (r k) k, Koszul.extDeriv η = ω :=
  exists_extDeriv_eq_of_mem_form₀_old (κ k) (h.transition k) hω hd

/-- The earlier `PolyKind.IsAdmissible.mem_polyForm_zero_of_extDeriv_eq_zero` (with `form₀`),
removed: it is `PolyKind.mem_polyForm_zero_of_extDeriv_eq_zero` of `κ 0`, for every degree. -/
theorem isAdmissible_mem_polyForm_zero_of_extDeriv_eq_zero_old {K : Type*} [Field K] [CharZero K]
    {κ : ℕ → PolyKind} {r : ℕ → ℕ} (_h : PolyKind.IsAdmissible κ r) {ω : PolyForm K (Fin n)}
    (hω : ω ∈ form₀_old K (κ 0) (r 0) 0) (hd : Koszul.extDeriv ω = 0) :
    ω ∈ polyForm K (Fin n) 0 0 :=
  (κ 0).mem_polyForm_zero_of_extDeriv_eq_zero (by rwa [form₀_old_eq] at hω) hd

/-- The earlier `PolySeq.form_eq_form₀`. -/
theorem polySeq_form_eq_form₀_old (S : PolySeq) (k : ℕ) :
    S.form K (n := n) k = form₀_old K (S.kind k) (S.deg k) k :=
  (form₀_old_eq _ _ _).symm

end PolyKind

section DroppedHypotheses

/-! ### Results whose hypothesis `r ≥ 1` was dropped -/

section CommRing

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d] [Fintype d]

/-- The earlier `Koszul.polyFormMinus_le_polyForm` (`r ≥ 1`), verbatim. -/
theorem polyFormMinus_le_polyForm_old {r : ℕ} (_hr : 1 ≤ r) (k : ℕ) :
    polyFormMinus R d r k ≤ polyForm R d r k :=
  Koszul.polyFormMinus_le_polyForm r k

/-- The earlier `Koszul.koszul_mem_polyForm_of_mem_polyFormMinus_succ` (`r ≥ 1`), verbatim. -/
theorem koszul_mem_polyForm_of_mem_polyFormMinus_succ_old {r k : ℕ} (_hr : 1 ≤ r)
    {ω : PolyForm R d}
    (h : ω ∈ polyFormMinus R d r (k + 1)) : Koszul.koszul ω ∈ polyForm R d r k :=
  Koszul.koszul_mem_polyForm_of_mem_polyFormMinus_succ h

/-- The earlier `PolyKind.form_le_polyForm` (`r ≥ 1`), verbatim. -/
theorem form_le_polyForm_old {n : ℕ} (κ : PolyKind) {r : ℕ} (_hr : 1 ≤ r) (k : ℕ) :
    κ.form R r k ≤ Koszul.polyForm R (Fin n) r k :=
  κ.form_le_polyForm r k

/-- The earlier `PolyKind.polyFormMinus_le_form` (`r ≥ 1`), verbatim. -/
theorem polyFormMinus_le_form_old {n : ℕ} (κ : PolyKind) {r : ℕ} (_hr : 1 ≤ r) (k : ℕ) :
    Koszul.polyFormMinus R (Fin n) r k ≤ κ.form R r k :=
  κ.polyFormMinus_le_form r k

end CommRing

section Field

variable {K : Type*} [Field K] [CharZero K] {d : Type*} [LinearOrder d] [Fintype d]

/-- The earlier `Koszul.extDeriv_not_mem_polyFormMinus_of_koszul_eq_zero` (`r ≥ 1`), verbatim. -/
theorem extDeriv_not_mem_polyFormMinus_of_koszul_eq_zero_old {r s k : ℕ} (_hr : 1 ≤ r)
    (hs : r + 1 ≤ s) {ω : PolyForm K d} (hω : ω ∈ homForm K d s k) (hκ : Koszul.koszul ω = 0)
    (hne : ω ≠ 0) : Koszul.extDeriv ω ∉ polyFormMinus K d r (k + 1) :=
  Koszul.extDeriv_not_mem_polyFormMinus_of_koszul_eq_zero hs hω hκ hne

/-- The earlier `Koszul.map_extDeriv_polyForm_le_polyFormMinus_iff` (`r ≥ 1`), verbatim. -/
theorem map_extDeriv_polyForm_le_polyFormMinus_iff_old [Nonempty d] {r s : ℕ} (_hr : 1 ≤ r) :
    (polyForm K d s 0).map (Koszul.extDerivₗ K d) ≤ polyFormMinus K d r 1 ↔ s ≤ r :=
  Koszul.map_extDeriv_polyForm_le_polyFormMinus_iff

/-- The earlier `Koszul.tensorForm_reduced_iff` (`r ≥ 1`), verbatim. -/
theorem tensorForm_reduced_iff_old (ι : Type*) [Nonempty ι] [Nonempty d] {r : ℕ} (_hr : 1 ≤ r)
    (s : ℕ) :
    ((∀ A ∈ Koszul.tensorForm K d ι (polyForm K d s 0),
      (fun a => Koszul.extDeriv (A a)) ∈ Koszul.tensorForm K d ι (polyForm K d r 1)) ↔
        s ≤ r + 1) ∧
    ((∀ A ∈ Koszul.tensorForm K d ι (polyForm K d s 0),
      (fun a => Koszul.extDeriv (A a)) ∈ Koszul.tensorForm K d ι (polyFormMinus K d r 1)) ↔
        s ≤ r) :=
  Koszul.tensorForm_reduced_iff ι r s

/-- The earlier `Koszul.polyFormMinus_lt_polyForm_one` (`r ≥ 1`), verbatim. -/
theorem polyFormMinus_lt_polyForm_one_old [Nonempty d] {r : ℕ} (_hr : 1 ≤ r) :
    polyFormMinus K d r 1 < polyForm K d r 1 :=
  Koszul.polyFormMinus_lt_polyForm_one r

/-- The earlier `Koszul.mem_polyForm_of_mem_polyFormMinus_of_extDeriv_eq_zero` (`r ≥ 1`),
verbatim. -/
theorem mem_polyForm_of_mem_polyFormMinus_of_extDeriv_eq_zero_old {r k : ℕ} (_hr : 1 ≤ r)
    {ω : PolyForm K d} (h : ω ∈ polyFormMinus K d r k) (hd : Koszul.extDeriv ω = 0) :
    ω ∈ polyForm K d (r - 1) k :=
  Koszul.mem_polyForm_of_mem_polyFormMinus_of_extDeriv_eq_zero h hd

/-- The earlier `Koszul.exists_extDeriv_eq_of_mem_polyFormMinus` (`r ≥ 1`), verbatim. -/
theorem exists_extDeriv_eq_of_mem_polyFormMinus_old {r k : ℕ} (_hr : 1 ≤ r) {ω : PolyForm K d}
    (h : ω ∈ polyFormMinus K d r (k + 1)) (hd : Koszul.extDeriv ω = 0) :
    ∃ η ∈ polyFormMinus K d r k, Koszul.extDeriv η = ω :=
  Koszul.exists_extDeriv_eq_of_mem_polyFormMinus h hd

/-- The earlier `Koszul.polyFormMinus_sup_map_extDeriv` (`r ≥ 1`), verbatim. -/
theorem polyFormMinus_sup_map_extDeriv_old {r : ℕ} (_hr : 1 ≤ r) (k : ℕ) :
    polyFormMinus K d r (k + 1) ⊔ (homForm K d (r + 1) k).map (Koszul.extDerivₗ K d) =
      polyForm K d r (k + 1) :=
  Koszul.polyFormMinus_sup_map_extDeriv r k

/-- The earlier `Koszul.disjoint_polyFormMinus_map_extDeriv` (`r ≥ 1`), verbatim. -/
theorem disjoint_polyFormMinus_map_extDeriv_old {r : ℕ} (_hr : 1 ≤ r) (k : ℕ) :
    Disjoint (polyFormMinus K d r (k + 1))
      ((homForm K d (r + 1) k).map (Koszul.extDerivₗ K d)) :=
  Koszul.disjoint_polyFormMinus_map_extDeriv r k

/-- The earlier `Koszul.polyFormMinus_lt_polyForm` (`r ≥ 1`), verbatim. -/
theorem polyFormMinus_lt_polyForm_old {r k : ℕ} (_hr : 1 ≤ r) (hk : k + 1 ≤ Fintype.card d) :
    polyFormMinus K d r (k + 1) < polyForm K d r (k + 1) :=
  Koszul.polyFormMinus_lt_polyForm r hk

/-- The earlier name `Koszul.polyFormMinus_zero` of `Koszul.polyFormMinus_zero_right`. -/
theorem polyFormMinus_zero_old {r : ℕ} (hr : 1 ≤ r) : polyFormMinus K d r 0 = polyForm K d r 0 :=
  Koszul.polyFormMinus_zero_right hr

/-- The earlier `PolyKind.mem_polyForm_zero_of_extDeriv_eq_zero` (`r ≥ 1`), verbatim. -/
theorem mem_polyForm_zero_of_extDeriv_eq_zero_old {n : ℕ} (κ : PolyKind) {r : ℕ} (_hr : 1 ≤ r)
    {ω : Koszul.PolyForm K (Fin n)} (hω : ω ∈ κ.form K r 0) (hd : Koszul.extDeriv ω = 0) :
    ω ∈ Koszul.polyForm K (Fin n) 0 0 :=
  κ.mem_polyForm_zero_of_extDeriv_eq_zero hω hd

end Field

section Counterexamples

open Counterexamples.PolynomialForms

variable {K : Type*} [Field K] {d : Type*} [LinearOrder d] [Fintype d]

/-- The removed `Counterexamples.PolynomialForms.koszul_mem_polyForm_of_mem_polyFormMinus`
(`r ≥ 1`), verbatim; it is `Koszul.koszul_mem_polyForm_of_mem_polyFormMinus_succ` at `k = 0`. -/
theorem koszul_mem_polyForm_of_mem_polyFormMinus_old {r : ℕ} (_hr : 1 ≤ r) {v : PolyForm K d}
    (hv : v ∈ polyFormMinus K d r 1) : Koszul.koszul v ∈ polyForm K d r 0 :=
  Koszul.koszul_mem_polyForm_of_mem_polyFormMinus_succ hv

/-- The earlier `Counterexamples.PolynomialForms.extDeriv_not_mem_polyFormMinus` (`r ≥ 1`),
verbatim. -/
theorem extDeriv_not_mem_polyFormMinus_old [CharZero K] {r s : ℕ} (_hr : 1 ≤ r) (hs : r + 1 ≤ s)
    {ω : PolyForm K d} (hω : ω ∈ homForm K d s 0) (hne : ω ≠ 0) :
    Koszul.extDeriv ω ∉ polyFormMinus K d r 1 :=
  extDeriv_not_mem_polyFormMinus hs hω hne

/-- The earlier `Counterexamples.PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus`
(`r ≥ 1`), verbatim. -/
theorem not_map_extDeriv_polyForm_le_polyFormMinus_old [CharZero K] [Nonempty d] {r : ℕ}
    (_hr : 1 ≤ r) :
    ¬ (polyForm K d (r + 1) 0).map (Koszul.extDerivₗ K d) ≤ polyFormMinus K d r 1 :=
  not_map_extDeriv_polyForm_le_polyFormMinus r

/-- The earlier `Counterexamples.PolynomialForms.not_isTensorSubcomplex_printed` (`r ≥ 1`),
verbatim. -/
theorem not_isTensorSubcomplex_printed_old [CharZero K] [Nonempty d] (ι : Type*) [Nonempty ι]
    {r : ℕ} (_hr : 1 ≤ r) (V₂ : Submodule K (PolyForm K d)) :
    ¬ Koszul.IsTensorSubcomplex ι (polyForm K d (r + 1) 0) (polyFormMinus K d r 1) V₂ :=
  not_isTensorSubcomplex_printed ι r V₂

end Counterexamples

section FormFields

open MeasureTheory ExteriorFibre MvPolynomial Finset

variable {n : ℕ}

/-- The earlier `polyMinusSpace_le_polySpace` (`r ≥ 1`), verbatim. -/
theorem polyMinusSpace_le_polySpace_old {r k : ℕ} (_hr : 1 ≤ r) :
    polyMinusSpace n r k ≤ polySpace n r k :=
  polyMinusSpace_le_polySpace

/-- The earlier `polyMinusSpace_mono` (`s ≥ 1`), verbatim. -/
theorem polyMinusSpace_mono_old {m s : ℕ} (_hs : 1 ≤ s) (j : ℕ) :
    polyMinusSpace m s j ≤ polyMinusSpace m (s + 1) j :=
  polyMinusSpace_mono s j

/-- The earlier `eq_zero_of_isBubble_of_mem_polyFormMinus` (`r ≥ 1`), verbatim. -/
theorem eq_zero_of_isBubble_of_mem_polyFormMinus_old {r k : ℕ} (_hr : 1 ≤ r)
    {Ω : Koszul.PolyForm ℝ (Fin n)} (hΩ : Ω ∈ Koszul.polyFormMinus ℝ (Fin n) r k)
    (hbub : IsBubble (refVertex n) (evalForm n Ω))
    (hint : n < r + k → ∀ H ∈ Koszul.polyForm ℝ (Fin n) (r + k - n - 1) (n - k),
      ∫ x in refSimplex n, eval x (wedgeForm Ω H univ) = 0) : Ω = 0 :=
  eq_zero_of_isBubble_of_mem_polyFormMinus hΩ hbub hint

/-- The earlier `eq_zero_of_mem_bubbleSpace_polyMinusSpace` (`r ≥ 1`), verbatim. -/
theorem eq_zero_of_mem_bubbleSpace_polyMinusSpace_old {r k : ℕ} (_hr : 1 ≤ r) {ω : FormField n}
    (hω : ω ∈ bubbleSpace (refVertex n) (polyMinusSpace n r k))
    (hint : n < r + k → ∀ η ∈ polySpace n (r + k - n - 1) (n - k),
      simplexIntegral (refVertex n) (wedgeField ω η) = 0) : ω = 0 :=
  eq_zero_of_mem_bubbleSpace_polyMinusSpace hω hint

/-- The earlier `eq_zero_of_faceMoment_eq_zero_minus` (`r ≥ 1`), verbatim. -/
theorem eq_zero_of_faceMoment_eq_zero_minus_old {r : ℕ} (_hr : 1 ≤ r) (k n : ℕ) {ω : FormField n}
    (hω : ω ∈ polyMinusSpace n r k)
    (hdof : ∀ (m : ℕ) (e : Fin (m + 1) ↪o Fin (n + 1)), ∀ η ∈ testSpaceMinus r k m,
      faceMoment (refVertex n) e η ω = 0) : ω = 0 :=
  eq_zero_of_faceMoment_eq_zero_minus k n hω hdof

/-- The earlier `eq_zero_of_faceMoment_eq_zero_minus_simplex` (`r ≥ 1`), verbatim. -/
theorem eq_zero_of_faceMoment_eq_zero_minus_simplex_old {p : Fin (n + 1) → Fin n → ℝ}
    (hp : IsUnit (edgeMatrix p).det) {r : ℕ}
    (_hr : 1 ≤ r) (k : ℕ) {ω : FormField n} (hω : ω ∈ polyMinusSpace n r k)
    (hdof : ∀ (m : ℕ) (e : Fin (m + 1) ↪o Fin (n + 1)), ∀ η ∈ testSpaceMinus r k m,
      faceMoment p e η ω = 0) : ω = 0 :=
  eq_zero_of_faceMoment_eq_zero_minus_simplex hp k hω hdof

/-- The earlier `faceTrace_eq_of_localDofMinus_eq` (`r ≥ 1`), verbatim. -/
theorem faceTrace_eq_of_localDofMinus_eq_old {p : Fin (n + 1) → Fin n → ℝ}
    (hp : IsUnit (edgeMatrix p).det) {r k : ℕ}
    (_hr : 1 ≤ r) (f : Face n) {ω ω' : localPolyMinusSpace p r k}
    (h : ∀ g : Face n, g.2.1 ⊆ f.2.1 → ∀ i,
      localDofMinus p r k ⟨g, i⟩ ω = localDofMinus p r k ⟨g, i⟩ ω') :
    faceTrace p f.emb ω = faceTrace p f.emb ω' :=
  faceTrace_eq_of_localDofMinus_eq hp f h

/-- The earlier `PolyKind.extDeriv_mem_space` (`r ≥ 1`), verbatim. -/
theorem extDeriv_mem_space_old (κ : PolyKind) {r : ℕ} (_hr : 1 ≤ r) {κ' : PolyKind} {r' : ℕ}
    (ht : PolyKind.Transition r κ' r') {k : ℕ} {ω : FormField n} (hω : ω ∈ κ.space n r k) :
    extDeriv ω ∈ κ'.space n r' (k + 1) :=
  κ.extDeriv_mem_space ht hω

end FormFields

end DroppedHypotheses

end FeecCheck.TrimmedForms
