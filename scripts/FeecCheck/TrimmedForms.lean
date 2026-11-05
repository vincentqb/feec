module

public import Feec.FiniteElement.PolyComplex
public import Feec.FiniteElement.LocalSpace

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

/-- The earlier `PolyKind.IsAdmissible.mem_polyForm_zero_of_extDeriv_eq_zero` (with `form₀`). -/
theorem isAdmissible_mem_polyForm_zero_of_extDeriv_eq_zero_old {K : Type*} [Field K] [CharZero K]
    {κ : ℕ → PolyKind} {r : ℕ → ℕ} (h : PolyKind.IsAdmissible κ r) {ω : PolyForm K (Fin n)}
    (hω : ω ∈ form₀_old K (κ 0) (r 0) 0) (hd : Koszul.extDeriv ω = 0) :
    ω ∈ polyForm K (Fin n) 0 0 :=
  h.mem_polyForm_zero_of_extDeriv_eq_zero (by rwa [form₀_old_eq] at hω) hd

/-- The earlier `PolySeq.form_eq_form₀`. -/
theorem polySeq_form_eq_form₀_old (S : PolySeq) (k : ℕ) :
    S.form K (n := n) k = form₀_old K (S.kind k) (S.deg k) k :=
  (form₀_old_eq _ _ _).symm

end PolyKind

end FeecCheck.TrimmedForms
