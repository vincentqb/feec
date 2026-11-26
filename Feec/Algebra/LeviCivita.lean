module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# The Levi-Civita symbol

The Levi-Civita symbol `ε_{v 0 ⋯ v (n-1)} ∈ R` of `v : Fin n → Fin n`, the determinant of the
matrix with rows `e_{v 0}, …, e_{v (n-1)}` ([QuennevilleBelair2015], §3.1), and its cases
`n = 3, 4` as casts of integer closed forms.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Matrix Equiv

@[expose] public noncomputable section

namespace Feec

variable (R : Type*) [CommRing R]

/-- The Levi-Civita symbol: the determinant of the matrix with rows `e_{v 0}, …, e_{v (n-1)}`. -/
def leviCivita {n : ℕ} (v : Fin n → Fin n) : R :=
  ((1 : Matrix (Fin n) (Fin n) R).submatrix v id).det

variable {R}

@[simp] theorem leviCivita_perm {n : ℕ} (σ : Perm (Fin n)) :
    leviCivita R σ = ((Perm.sign σ : ℤˣ) : ℤ) := by
  rw [leviCivita, det_permute, det_one, mul_one]

theorem leviCivita_of_not_injective {n : ℕ} {v : Fin n → Fin n} (hv : ¬ Function.Injective v) :
    leviCivita R v = 0 := by
  simp only [Function.Injective, not_forall] at hv
  obtain ⟨i, j, hij, hne⟩ := hv
  exact det_zero_of_row_eq hne (by funext k; simp only [submatrix_apply]; rw [hij])

theorem leviCivita_of_injective {n : ℕ} {v : Fin n → Fin n} (hv : Function.Injective v) :
    leviCivita R v =
      ((Perm.sign (Equiv.ofBijective v (Finite.injective_iff_bijective.1 hv)) : ℤˣ) : ℤ) :=
  leviCivita_perm (Equiv.ofBijective v _)

theorem leviCivita_eq_intCast {n : ℕ} (v : Fin n → Fin n) :
    leviCivita R v = ((leviCivita ℤ v : ℤ) : R) := by
  by_cases hv : Function.Injective v
  · rw [leviCivita_of_injective hv, leviCivita_of_injective hv]; simp
  · rw [leviCivita_of_not_injective hv, leviCivita_of_not_injective hv, Int.cast_zero]

theorem map_leviCivita {S : Type*} [CommRing S] (f : R →+* S) {n : ℕ} (v : Fin n → Fin n) :
    f (leviCivita R v) = leviCivita S v := by
  rw [leviCivita_eq_intCast (R := R), leviCivita_eq_intCast (R := S), map_intCast]

variable (R)

/-- `ε_{ijk}` in three dimensions. [QuennevilleBelair2015], §3.1 -/
def leviCivita3 (i j k : Fin 3) : R := leviCivita R ![i, j, k]

/-- `ε_{abcd}` in four dimensions. [QuennevilleBelair2015], §3.1 -/
def leviCivita4 (a b c d : Fin 4) : R := leviCivita R ![a, b, c, d]

variable {R}

/-- Integer closed form `∏_{p<q} (x_q - x_p) / 2` of the three-dimensional symbol. -/
def leviCivita3Int (i j k : Fin 3) : ℤ :=
  ((j : ℤ) - i) * ((k : ℤ) - i) * ((k : ℤ) - j) / 2

/-- Integer closed form `∏_{p<q} (x_q - x_p) / 12` of the four-dimensional symbol. -/
def leviCivita4Int (a b c d : Fin 4) : ℤ :=
  ((b : ℤ) - a) * ((c : ℤ) - a) * ((d : ℤ) - a) * ((c : ℤ) - b) * ((d : ℤ) - b) *
    ((d : ℤ) - c) / 12

theorem leviCivita3Int_perm : ∀ σ : Perm (Fin 3),
    ((Perm.sign σ : ℤˣ) : ℤ) = leviCivita3Int (σ 0) (σ 1) (σ 2) := by decide

theorem leviCivita3Int_not_inj : ∀ i j k : Fin 3,
    ¬ Function.Injective ![i, j, k] → leviCivita3Int i j k = 0 := by decide

theorem leviCivita4Int_perm : ∀ σ : Perm (Fin 4),
    ((Perm.sign σ : ℤˣ) : ℤ) = leviCivita4Int (σ 0) (σ 1) (σ 2) (σ 3) := by decide

theorem leviCivita4Int_not_inj : ∀ a b c d : Fin 4,
    ¬ Function.Injective ![a, b, c, d] → leviCivita4Int a b c d = 0 := by decide

theorem leviCivita3_eq_int (i j k : Fin 3) :
    leviCivita3 R i j k = (leviCivita3Int i j k : R) := by
  unfold leviCivita3
  by_cases hv : Function.Injective ![i, j, k]
  · rw [leviCivita_of_injective hv, leviCivita3Int_perm]
    simp
  · rw [leviCivita_of_not_injective hv, leviCivita3Int_not_inj i j k hv, Int.cast_zero]

theorem leviCivita4_eq_int (a b c d : Fin 4) :
    leviCivita4 R a b c d = (leviCivita4Int a b c d : R) := by
  unfold leviCivita4
  by_cases hv : Function.Injective ![a, b, c, d]
  · rw [leviCivita_of_injective hv, leviCivita4Int_perm]
    simp
  · rw [leviCivita_of_not_injective hv, leviCivita4Int_not_inj a b c d hv, Int.cast_zero]

theorem leviCivita3_apply (i j k : Fin 3) : leviCivita3 R i j k =
    ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]], ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
      ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]] i j k := by
  rw [leviCivita3_eq_int]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [leviCivita3Int]

theorem leviCivita4_swap_pairs (a b c d : Fin 4) :
    leviCivita4 R a b c d = leviCivita4 R c d a b := by
  simp only [leviCivita4_eq_int]; congr 1; revert a b c d; decide

theorem leviCivita4_swap34 (a b c d : Fin 4) :
    leviCivita4 R a b d c = -leviCivita4 R a b c d := by
  simp only [leviCivita4_eq_int, ← Int.cast_neg]; congr 1; revert a b c d; decide

end Feec
