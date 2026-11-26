module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.NoncommRing

/-!
# A noncommutative telescoping identity for `aⁿ - bⁿ`

In any ring, `aⁿ - bⁿ = Σ_{j<n} aʲ (a - b) b^{n-1-j}`, with no commutativity assumption.
-/

open Finset

@[expose] public section

theorem pow_sub_pow_eq_sum_pow_mul_sub_mul_pow {R : Type*} [Ring R] (a b : R) (n : ℕ) :
    a ^ n - b ^ n = ∑ j ∈ range n, a ^ j * (a - b) * b ^ (n - 1 - j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    have : ∑ j ∈ range n, a ^ j * (a - b) * b ^ (n - j) =
        (∑ j ∈ range n, a ^ j * (a - b) * b ^ (n - 1 - j)) * b := by
      rw [sum_mul]
      refine sum_congr rfl fun j hj => ?_
      rw [show n - j = n - 1 - j + 1 by have := mem_range.1 hj; omega, pow_succ]
      simp only [mul_assoc]
    rw [this, ← ih, pow_succ, pow_succ]
    noncomm_ring
