module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

/-!
# Transverse–traceless matrices at a frequency

The transverse–traceless (TT) matrices at `ξ`, symmetric, trace-free and `A ξ = 0`
([QuennevilleBelair2015], (2.12), §3.4), and the TT projection, which maps symmetric matrices to
TT matrices when `ξ·ξ ≠ 0` and `n - 1 ≠ 0`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Matrix

@[expose] public noncomputable section

namespace Feec.TT

variable {ι : Type*} [Fintype ι]

section CommRing

variable {R : Type*} [CommRing R]

/-- The transverse–traceless matrices at `ξ`: symmetric, trace-free and `A ξ = 0`. -/
def ttSub (ξ : ι → R) : Submodule R (Matrix ι ι R) where
  carrier := {A | Aᵀ = A ∧ A.trace = 0 ∧ A *ᵥ ξ = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro A B ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    exact ⟨by rw [transpose_add, h1, k1], by rw [trace_add, h2, k2, add_zero],
      by rw [add_mulVec, h3, k3, add_zero]⟩
  smul_mem' := by
    rintro c A ⟨h1, h2, h3⟩
    exact ⟨by rw [transpose_smul, h1], by rw [trace_smul, h2, smul_zero],
      by rw [smul_mulVec, h3, smul_zero]⟩

end CommRing

section Field

variable [DecidableEq ι] {K : Type*} [Field K]

/-- The projector `P = 1 - (ξ·ξ)⁻¹ ξ ξᵀ` onto the hyperplane `ξ^⊥`. -/
def transverseProj (ξ : ι → K) : Matrix ι ι K := 1 - (ξ ⬝ᵥ ξ)⁻¹ • vecMulVec ξ ξ

theorem transverseProj_transpose (ξ : ι → K) : (transverseProj ξ)ᵀ = transverseProj ξ := by
  simp [transverseProj, transpose_sub, transpose_smul, transpose_vecMulVec]

variable {ξ : ι → K}

theorem transverseProj_mulVec_self (hq : ξ ⬝ᵥ ξ ≠ 0) : transverseProj ξ *ᵥ ξ = 0 := by
  funext i
  simp only [transverseProj, sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply]
  have : (vecMulVec ξ ξ *ᵥ ξ) i = ξ i * (ξ ⬝ᵥ ξ) := by
    simp [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]
  rw [this]
  field_simp
  ring

theorem trace_transverseProj (hq : ξ ⬝ᵥ ξ ≠ 0) :
    (transverseProj ξ).trace = (Fintype.card ι : K) - 1 := by
  rw [transverseProj, trace_sub, trace_one, trace_smul, trace_vecMulVec, smul_eq_mul,
    inv_mul_cancel₀ hq]

/-- The TT projection `ttProj ξ A = P A P - (n - 1)⁻¹ tr(P A P) P`, `n = card ι`. -/
def ttProj (ξ : ι → K) (A : Matrix ι ι K) : Matrix ι ι K :=
  transverseProj ξ * A * transverseProj ξ -
    (((Fintype.card ι : K) - 1)⁻¹ * (transverseProj ξ * A * transverseProj ξ).trace) •
      transverseProj ξ

theorem ttProj_mem (hq : ξ ⬝ᵥ ξ ≠ 0) (hn : (Fintype.card ι : K) - 1 ≠ 0) {A : Matrix ι ι K}
    (hA : Aᵀ = A) : ttProj ξ A ∈ ttSub ξ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ttProj, transpose_sub, transpose_smul, transverseProj_transpose, transpose_mul,
      transpose_mul, transverseProj_transpose, hA, Matrix.mul_assoc]
  · rw [ttProj, trace_sub, trace_smul, trace_transverseProj hq, smul_eq_mul]
    field_simp
    ring
  · rw [ttProj, sub_mulVec, smul_mulVec, ← mulVec_mulVec, transverseProj_mulVec_self hq,
      mulVec_zero, smul_zero, sub_zero]

end Field

end Feec.TT
