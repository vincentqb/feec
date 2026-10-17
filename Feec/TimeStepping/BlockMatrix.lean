module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Signed symmetrization of Crank–Nicolson block systems (MINRES)

A Crank–Nicolson step of `M ẋ = -K x` solves `(M + s K) x' = (M - s K) x` (`s = Δt/2`), with `M`
symmetric (the mass matrix) and `K` skew (the stiffness of `d - d*`). The matrix `M + s K` is
not symmetric, so MINRES does not apply directly. If the unknowns carry signs `ε i = ±1` such
that `M` couples only equal signs and `K` only opposite signs, as for a Hilbert complex graded by
the parity of the form degree, then `diag(ε) (M + s K)` is symmetric and has the same solutions.

## Main results

* `TimeStepping.isSymm_diagonal_mul_add_smul`: `diag(ε) (M + s K)` is symmetric.
* `TimeStepping.mulVec_diagonal_mul_iff`: the signed system has the same solutions.

This holds for any number of blocks (any length of the complex) and any commutative ring.

## References

* [QuennevilleBelair2015], Ch. 7 (MINRES for the Crank–Nicolson systems)
* [PaigeSaunders1975] (MINRES for symmetric indefinite systems)
-/

open Matrix

@[expose] public noncomputable section

namespace Feec.TimeStepping

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- **Signed symmetrization**: if `M` is symmetric and couples only unknowns with equal signs,
and `K` is skew and couples only unknowns with opposite signs, then `diag(ε) (M + s K)` is
symmetric. Thesis: Ch. 7 -/
theorem isSymm_diagonal_mul_add_smul (ε : n → R) {M K : Matrix n n R} (hM : M.IsSymm)
    (hK : Kᵀ = -K) (hMε : ∀ i j, M i j ≠ 0 → ε i = ε j) (hKε : ∀ i j, K i j ≠ 0 → ε i = -ε j)
    (s : R) : (diagonal ε * (M + s • K)).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [diagonal_mul, add_apply, smul_apply, smul_eq_mul]
  have hMji : M j i = M i j := by simpa using congrFun (congrFun hM.eq i) j
  have hKji : K j i = -K i j := by simpa using congrFun (congrFun hK i) j
  rw [hMji, hKji]
  have e1 : ε j * M i j = ε i * M i j := by
    by_cases h : M i j = 0
    · rw [h, mul_zero, mul_zero]
    · rw [hMε i j h]
  have e2 : ε j * (s * -K i j) = ε i * (s * K i j) := by
    by_cases h : K i j = 0
    · simp [h]
    · rw [hKε i j h]; ring
  linear_combination e1 + e2

/-- The signed system `diag(ε) A x = diag(ε) b` has the solutions of `A x = b` when
`ε i² = 1`. Thesis: Ch. 7 -/
theorem mulVec_diagonal_mul_iff (ε : n → R) (hε : ∀ i, ε i * ε i = 1) (A : Matrix n n R)
    (x b : n → R) : (diagonal ε * A) *ᵥ x = diagonal ε *ᵥ b ↔ A *ᵥ x = b := by
  have hεε : diagonal ε * diagonal ε = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; exact congrArg diagonal (funext hε)
  constructor
  · intro h
    have := congrArg (diagonal ε *ᵥ ·) h
    simpa [mulVec_mulVec, ← Matrix.mul_assoc, hεε] using this
  · intro h; rw [← mulVec_mulVec, h]

end Feec.TimeStepping
