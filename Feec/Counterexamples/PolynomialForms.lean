module

public import Feec.Algebra.PolynomialForm
public import Mathlib.Basic.Real.Basic

/-!
# `P_{r+1}Λ⁰ → P_r⁻Λ¹` is not a pair of a subcomplex

Thesis §4.10 lists `P_{r+1}Λ⁰ ⊗ V × P_r⁻Λ¹ ⊗ V × …` among the discretizations of the matrix wave
equation (4.14). These are not subcomplexes: in every dimension, over every field of
characteristic zero, the exterior derivative of a nonzero homogeneous `0`-form of degree
`s ≥ r + 1` is not in `P_r⁻Λ¹` (`extDeriv_not_mem_polyFormMinus`), so
`d (P_{r+1}Λ⁰) ⊄ P_r⁻Λ¹` (`not_map_extDeriv_polyForm_le_polyFormMinus`). The admissible pairing
is `P_rΛ⁰` with `P_r⁻Λ¹` (`Feec.Koszul.extDeriv_mem_polyFormMinus_of_mem_polyForm`).

Proof: `κ (P_r⁻Λ¹) ⊆ P_rΛ⁰` (`Feec.Koszul.koszul_mem_polyForm_of_mem_polyFormMinus_succ`), while
the homotopy formula gives `κ d ω = s ω`, of degree `s > r`, for `ω ∈ H_sΛ⁰`.

The three-dimensional function form for `r = 1` (lowest-order Nédélec fields `a + b × x`) is
`grad_sq_not_whitney`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.Counterexamples.PolynomialForms

open Feec.Koszul ExteriorFibre

variable {K : Type*} [Field K] {d : Type*} [LinearOrder d] [Fintype d]

/-- **`d ω ∉ P_r⁻Λ¹`** for every nonzero homogeneous `0`-form `ω` of degree `s ≥ r + 1`, in every
dimension. [QuennevilleBelair2015], §4.10 (refuted) -/
theorem extDeriv_not_mem_polyFormMinus [CharZero K] {r s : ℕ} (hs : r + 1 ≤ s)
    {ω : PolyForm K d} (hω : ω ∈ homForm K d s 0) (hne : ω ≠ 0) :
    extDeriv ω ∉ polyFormMinus K d r 1 := by
  intro hv
  have h1 := koszul_mem_polyForm_of_mem_polyFormMinus_succ hv
  have h2 := extDeriv_koszul_add_koszul_extDeriv_of_mem hω
  rw [IsDeg.koszul_eq_zero hω.1] at h2
  have h0 : extDeriv (0 : PolyForm K d) = 0 := by
    funext t; simp [extDeriv_apply]
  rw [h0, zero_add, add_zero] at h2
  rw [h2] at h1
  obtain ⟨t, ht⟩ : ∃ t, ω t ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    exact hne (funext h)
  have hc : ((s : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hhom : ((((s : ℕ) : K) • ω) t).IsHomogeneous s := by
    rw [Pi.smul_apply, smul_eq_C_mul]
    have := (isHomogeneous_C d ((s : ℕ) : K)).mul (hω.2 t)
    rwa [zero_add] at this
  have hne' : (((s : ℕ) : K) • ω) t ≠ 0 := by
    rw [Pi.smul_apply]
    exact smul_ne_zero hc ht
  have := h1.2 t
  rw [hhom.totalDegree hne'] at this
  omega

/-- The `0`-form `x_j^s`. -/
def monomialForm (j : d) (s : ℕ) : PolyForm K d := fun t => if t = ∅ then X j ^ s else 0

omit [Fintype d] in
theorem monomialForm_mem (j : d) (s : ℕ) : monomialForm (K := K) j s ∈ homForm K d s 0 := by
  refine ⟨fun t ht => ?_, fun t => ?_⟩
  · simp only [monomialForm]
    rw [ite_eq_right_iff]
    intro h
    exact absurd (by simp [h]) ht
  · simp only [monomialForm]
    split_ifs
    · exact isHomogeneous_X_pow j s
    · exact isHomogeneous_zero _ _ _

omit [Fintype d] in
theorem monomialForm_ne_zero (j : d) (s : ℕ) : monomialForm (K := K) j s ≠ 0 := fun h => by
  have := congrFun h ∅
  simp [monomialForm] at this

/-- **`d (P_{r+1}Λ⁰) ⊄ P_r⁻Λ¹`** in every dimension `≥ 1`: the pairs `P_{r+1}Λ⁰ × P_r⁻Λ¹` listed in
thesis §4.10 (`r ≥ 1`) are not subcomplexes. [QuennevilleBelair2015], §4.10 (refuted) -/
theorem not_map_extDeriv_polyForm_le_polyFormMinus [CharZero K] [Nonempty d] (r : ℕ) :
    ¬ (polyForm K d (r + 1) 0).map (extDerivₗ K d) ≤ polyFormMinus K d r 1 := fun h => by
  obtain ⟨j⟩ := ‹Nonempty d›
  exact extDeriv_not_mem_polyFormMinus le_rfl (monomialForm_mem j (r + 1))
    (monomialForm_ne_zero j (r + 1))
    (h ⟨_, homForm_le_polyForm _ _ (monomialForm_mem j (r + 1)), rfl⟩)

/-- The `r = 1` instance in function form (lowest-order Nédélec fields `a + b × x` on `ℝ³`):
`grad x₀² = (2x₀, 0, 0)` is not of this form. [QuennevilleBelair2015], §4.10 (refuted) -/
theorem grad_sq_not_whitney :
    ¬ ∃ a b : Fin 3 → ℝ, ∀ x : Fin 3 → ℝ, 2 * x 0 = a 0 + (b 1 * x 2 - b 2 * x 1) := by
  rintro ⟨a, b, h⟩
  have h0 := h 0
  have h1 := h (Pi.single 0 1)
  simp at h0 h1
  linarith

/-- **The printed (4.14) discretizations with `P_r⁻Λ¹` are not subcomplexes** (thesis §4.10,
p. 66), in every dimension `≥ 1` and for every number of rows: for every `r` and `V₂`,
`P_{r+1}Λ⁰ ⊗ V × P_r⁻Λ¹ ⊗ V × V₂ ⊗ V` is not a subcomplex. The corrected list is
`Feec.Koszul.isTensorSubcomplex_polyForm`. [QuennevilleBelair2015], §4.10 (refuted) -/
theorem not_isTensorSubcomplex_printed [CharZero K] [Nonempty d] (ι : Type*) [Nonempty ι]
    (r : ℕ) (V₂ : Submodule K (PolyForm K d)) :
    ¬ IsTensorSubcomplex ι (polyForm K d (r + 1) 0) (polyFormMinus K d r 1) V₂ := fun h =>
  not_map_extDeriv_polyForm_le_polyFormMinus (K := K) (d := d) r fun _ ⟨_, hω, he⟩ =>
    he ▸ ((isTensorSubcomplex_iff.1 h).extDeriv_mem₀ _ hω)

end Feec.Counterexamples.PolynomialForms
