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

For a vector `ξ` (a frequency, or a wave covector) in any dimension, a matrix `A` is
**transverse–traceless** (TT) at `ξ` if it is symmetric, trace-free and transverse,
`A ξ = 0`. In the Fourier picture these are the symbols of the symmetric, trace-free,
divergence-free (TSD) matrix fields, and in linearized gravity the TT gauge amplitudes.

## Main definitions

* `Feec.TT.ttSub ξ`: the TT matrices at `ξ`, a submodule over any commutative ring.
* `Feec.TT.transverseProj ξ = 1 - (ξ·ξ)⁻¹ ξ ξᵀ`: the projector onto `ξ^⊥`.
* `Feec.TT.ttProj ξ A = P A P - (n-1)⁻¹ tr(P A P) P`: the TT projection (any field, any
  dimension `n = card ι`), and its linear version `ttProjₗ`.

## Main results

* `transverseProj_mulVec_self`, `transverseProj_transpose`, `transverseProj_mul_self`,
  `trace_transverseProj` (`tr P = n - 1`).
* `ttProj_mem`: `ttProj ξ A` is TT for symmetric `A` (when `ξ·ξ ≠ 0`, `n - 1 ≠ 0`);
  `ttProj_eq_self`: TT matrices are fixed; `ttProj_ttProj`: idempotence.
* `sum_sub_ttProj_mul_eq_zero`: `A - ttProj ξ A` is Frobenius-orthogonal to every TT
  matrix (bilinear form, so it applies to real and, via conjugation, complex symbols).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §2.8 ((2.12)–(2.13), the TT gauge), §3.4 (TSD fields)
* [R. M. Wald, *General Relativity*][Wald1984], §4.4

Bibliography: [references.bib](../../docs/references.bib)
-/

open Matrix

@[expose] public noncomputable section

namespace Feec.TT

variable {ι : Type*} [Fintype ι]

section CommRing

variable {R : Type*} [CommRing R]

/-- The transverse–traceless matrices at `ξ`: symmetric, trace-free and `A ξ = 0`.
[QuennevilleBelair2015], (2.12), §3.4 -/
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

theorem mem_ttSub {ξ : ι → R} {A : Matrix ι ι R} :
    A ∈ ttSub ξ ↔ Aᵀ = A ∧ A.trace = 0 ∧ A *ᵥ ξ = 0 := Iff.rfl

/-- TT matrices are also annihilated by `ξ` from the left. -/
theorem vecMul_eq_zero_of_mem {ξ : ι → R} {A : Matrix ι ι R} (hA : A ∈ ttSub ξ) :
    ξ ᵥ* A = 0 := by
  rw [← mulVec_transpose, hA.1, hA.2.2]

/-- The TT condition is preserved by ring homomorphisms (e.g. complex conjugation of a
symbol at a real frequency). -/
theorem map_mem_ttSub {S : Type*} [CommRing S] (f : R →+* S) {ξ : ι → R} {A : Matrix ι ι R}
    (hA : A ∈ ttSub ξ) : A.map f ∈ ttSub (f ∘ ξ) := by
  refine ⟨by rw [← transpose_map, hA.1], by rw [show (A.map f).trace = f A.trace by simp [trace, map_sum], hA.2.1, map_zero], ?_⟩
  funext i
  have := congrArg f (congrFun hA.2.2 i)
  simpa [mulVec, dotProduct, map_sum] using this

/-- Scaling the frequency does not change the TT space. -/
theorem ttSub_smul_le (c : R) (ξ : ι → R) : ttSub ξ ≤ ttSub (c • ξ) := by
  rintro A ⟨h1, h2, h3⟩
  exact ⟨h1, h2, by rw [mulVec_smul, h3, smul_zero]⟩

end CommRing

section Field

variable [DecidableEq ι] {K : Type*} [Field K]

/-- The projector `P = 1 - (ξ·ξ)⁻¹ ξ ξᵀ` onto the hyperplane `ξ^⊥`. -/
def transverseProj (ξ : ι → K) : Matrix ι ι K := 1 - (ξ ⬝ᵥ ξ)⁻¹ • vecMulVec ξ ξ

theorem transverseProj_apply (ξ : ι → K) (i j : ι) :
    transverseProj ξ i j = (if i = j then 1 else 0) - (ξ ⬝ᵥ ξ)⁻¹ * (ξ i * ξ j) := by
  simp [transverseProj, one_apply, vecMulVec_apply]

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

theorem vecMul_transverseProj_self (hq : ξ ⬝ᵥ ξ ≠ 0) : ξ ᵥ* transverseProj ξ = 0 := by
  rw [← mulVec_transpose, transverseProj_transpose, transverseProj_mulVec_self hq]

theorem transverseProj_mul_vecMulVec (hq : ξ ⬝ᵥ ξ ≠ 0) (w : ι → K) :
    transverseProj ξ * vecMulVec ξ w = 0 := by
  ext i j
  have h := congrFun (transverseProj_mulVec_self hq) i
  simp only [mulVec, dotProduct, Pi.zero_apply] at h
  simp only [mul_apply, vecMulVec_apply, zero_apply]
  simp_rw [← mul_assoc, ← Finset.sum_mul, h, zero_mul]

theorem transverseProj_mul_self (hq : ξ ⬝ᵥ ξ ≠ 0) :
    transverseProj ξ * transverseProj ξ = transverseProj ξ := by
  conv_lhs => arg 2; rw [transverseProj]
  rw [mul_sub, mul_one, mul_smul_comm, transverseProj_mul_vecMulVec hq, smul_zero, sub_zero]

theorem trace_transverseProj (hq : ξ ⬝ᵥ ξ ≠ 0) :
    (transverseProj ξ).trace = (Fintype.card ι : K) - 1 := by
  rw [transverseProj, trace_sub, trace_one, trace_smul, trace_vecMulVec, smul_eq_mul,
    inv_mul_cancel₀ hq]

/-- A TT matrix is fixed by `P` on either side. -/
theorem transverseProj_mul_of_mem {A : Matrix ι ι K} (hA : A ∈ ttSub ξ) :
    transverseProj ξ * A = A := by
  rw [transverseProj, sub_mul, one_mul, smul_mul_assoc]
  have : vecMulVec ξ ξ * A = vecMulVec ξ (ξ ᵥ* A) := by
    ext i j; simp [mul_apply, vecMulVec_apply, vecMul, dotProduct, Finset.mul_sum, mul_assoc]
  rw [this, vecMul_eq_zero_of_mem hA]
  ext i j
  simp

theorem mul_transverseProj_of_mem {A : Matrix ι ι K} (hA : A ∈ ttSub ξ) :
    A * transverseProj ξ = A := by
  have h := congrArg transpose (transverseProj_mul_of_mem hA)
  rwa [transpose_mul, transverseProj_transpose, hA.1] at h

/-- The TT projection `ttProj ξ A = P A P - (n - 1)⁻¹ tr(P A P) P`, `n = card ι`.
[QuennevilleBelair2015], §2.8, §3.4 -/
def ttProj (ξ : ι → K) (A : Matrix ι ι K) : Matrix ι ι K :=
  transverseProj ξ * A * transverseProj ξ -
    (((Fintype.card ι : K) - 1)⁻¹ * (transverseProj ξ * A * transverseProj ξ).trace) •
      transverseProj ξ

/-- `ttProj ξ` as a linear map. -/
def ttProjₗ (ξ : ι → K) : Matrix ι ι K →ₗ[K] Matrix ι ι K where
  toFun := ttProj ξ
  map_add' A B := by
    simp only [ttProj, mul_add, add_mul, trace_add, mul_add, add_smul]; abel
  map_smul' c A := by
    simp only [ttProj, mul_smul_comm, smul_mul_assoc, trace_smul, smul_eq_mul, RingHom.id_apply,
      smul_sub, smul_smul]
    ring_nf

@[simp] theorem ttProjₗ_apply (A : Matrix ι ι K) : ttProjₗ ξ A = ttProj ξ A := rfl

/-- **TT projection**: for symmetric `A`, `ttProj ξ A` is TT at `ξ` (if `ξ·ξ ≠ 0` and
`n - 1 ≠ 0`). [QuennevilleBelair2015], §2.8, §3.4 -/
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

/-- TT matrices are fixed by the TT projection. -/
theorem ttProj_eq_self {A : Matrix ι ι K} (hA : A ∈ ttSub ξ) :
    ttProj ξ A = A := by
  rw [ttProj, transverseProj_mul_of_mem hA, mul_transverseProj_of_mem hA, hA.2.1,
    mul_zero, zero_smul, sub_zero]

theorem ttProj_ttProj (hq : ξ ⬝ᵥ ξ ≠ 0) (hn : (Fintype.card ι : K) - 1 ≠ 0) {A : Matrix ι ι K}
    (hA : Aᵀ = A) : ttProj ξ (ttProj ξ A) = ttProj ξ A :=
  ttProj_eq_self (ttProj_mem hq hn hA)

/-- `A - ttProj ξ A` is orthogonal to the TT matrices for the Frobenius pairing
`⟨X, Y⟩ = ∑ X_ij Y_ij` (no symmetry of `A` needed). -/
theorem sum_sub_ttProj_mul_eq_zero (A : Matrix ι ι K) {B : Matrix ι ι K}
    (hB : B ∈ ttSub ξ) : ∑ i, ∑ j, (A - ttProj ξ A) i j * B i j = 0 := by
  have hF : ∀ X : Matrix ι ι K, ∑ i, ∑ j, X i j * B i j = (Xᵀ * B).trace := by
    intro X
    simp only [trace, diag, mul_apply, transpose_apply]
    rw [Finset.sum_comm]
  have hPB : transverseProj ξ * B = B := transverseProj_mul_of_mem hB
  have hBP : B * transverseProj ξ = B := mul_transverseProj_of_mem hB
  have e : (A - ttProj ξ A)ᵀ * B = Aᵀ * B - transverseProj ξ * (Aᵀ * B) +
      (((Fintype.card ι : K) - 1)⁻¹ *
        (transverseProj ξ * A * transverseProj ξ).trace) • B := by
    rw [ttProj, transpose_sub, transpose_sub, transpose_smul, transverseProj_transpose,
      transpose_mul, transpose_mul, transverseProj_transpose]
    simp only [sub_mul, smul_mul_assoc, Matrix.mul_assoc, hPB]
    abel
  rw [hF, e, trace_add, trace_sub, trace_smul, hB.2.1, smul_zero, add_zero,
    trace_mul_comm (transverseProj ξ), Matrix.mul_assoc, hBP, sub_self]

end Field

end Feec.TT
