module

public import Feec.Legacy.CrankNicolson
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Algebra.Order.Star.Real

/-!
# Repair of the thesis Ch. 7 solver claim: MINRES on the symmetrized Crank–Nicolson system

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

[QuennevilleBelair2015, Ch. 7, l. 4284–4285]: the mass matrices are inverted by
Jacobi-preconditioned CG and "other matrices are inverted with MINRES preconditioned with AMG".
The thesis never assembles the system, so which "other matrices" are meant is a matter of
reading. Two readings are treated here, and neither is asserted to be the thesis' intent.

Monolithic reading: MINRES is applied to the Crank–Nicolson (CN) matrix `M + sK` of (4.14) /
(4.15) (`M = diag(M0, M1, M2)` SPD, `K` skew, `s = Δt/2`). Then the claim needs a repair: MINRES
needs a symmetric nonsingular matrix, and `M + sK` is nonsingular but not symmetric whenever
`s ≠ 0` and the coupling is nonzero (`cn_matrix_not_isSymm`). Its `J`-symmetrization is the
right system.
* `cn_matrix_transpose`: `(M + sK)ᵀ = M − sK`; `cn_matrix_not_isSymm`.
* `minres_matrix_indefinite` (packaged), from `minres_symm`, `minres_matrix_isUnit`,
  `minres_matrix_not_posDef`, `minres_matrix_not_negDef`: `J(M + sK)` (`J = diag(−I, I, −I)`)
  is symmetric, nonsingular and indefinite once the `E` block and the `σ` or `B` block are
  nonempty. So under this reading MINRES, not CG, is the Krylov method.
* `minres_cn_existsUnique`, `minres_cn_iff`: the symmetrized CN system
  `J(M + sK) x' = J(M − sK) x` has exactly one solution, the CN update.

Block-elimination (Schur complement) reading: the separate mass solves suggest eliminating
`σ' = M0⁻¹(r₀ + s Gᵀ E')`, `B' = M2⁻¹(r₂ + s C E')` and solving
`S E' = r₁ − s G M0⁻¹ r₀ − s Cᵀ M2⁻¹ r₂` with `S = M1 + s²(G M0⁻¹ Gᵀ + Cᵀ M2⁻¹ C)`. Under this
reading the thesis claim holds as stated. `cn_schur_iff`: the elimination is equivalent to the
CN system. `schurE_posDef`: `S` is SPD, so MINRES (and CG) apply. `cn_step_schur`: the `E` block
of the CN step is `S⁻¹(…)`.

Bridge to the scheme. Take bases `b0, b1, b2` of abstract finite-dimensional inner-product spaces
`V0, V1, V2` and abstract linear maps `d0 : V0 → V1`, `d1 : V1 → V2`. In the thesis these are the
FE spaces with their `L²` products and `d0 = grad`, `d1 = curl`, but no concrete FE space is
instantiated here. `Mᵢ` are the Gram matrices (`Matrix.gram`), `G = gradMat`
(`Gᵢⱼ = (b1ᵢ, d0 b0ⱼ)`), `C = curlMat` (`Cᵢⱼ = (b2ᵢ, d1 b1ⱼ)`), and `coordVec` is the coefficient
vector. `fullStep_iff_matrix`: a full CN step of (4.14) (`Feec.Legacy.CrankNicolson.FullStep`) is
exactly `(M + sK) c(x') = (M − sK) c(x)`. `minres_solution_iff_cnStep`: a vector solves the
symmetrized system iff it is the coefficient vector of the CN iterate `cnStep x`.
`cnSystem_not_isSymm_of_ne`: for `s ≠ 0` and `d0 ≠ 0 ∨ d1 ≠ 0` the assembled `M + sK` is not
symmetric. The reduced system (4.15) is the case of an empty `σ` block (`redStep_iff_matrix`,
`minres_solution_iff_redStep`), where `J` is `diag(I, −I)`.

Not formalized: AMG preconditioning and MINRES convergence (numerical).
-/

open Matrix LinearMap InnerProductSpace
open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace Feec.Legacy.Minres

open Feec.Legacy.CrankNicolson

/-! ## Matrix level -/

section MatrixLevel

variable {n0 n1 n2 : Type*} [Fintype n0] [Fintype n1] [Fintype n2]
  [DecidableEq n0] [DecidableEq n1] [DecidableEq n2]

omit [Fintype n0] [Fintype n1] [Fintype n2] [DecidableEq n0] [DecidableEq n1]
  [DecidableEq n2] in
/-- `(M + sK)ᵀ = M − sK` for symmetric mass blocks (`K` skew). -/
theorem cn_matrix_transpose {M0 : Matrix n0 n0 ℝ} {M1 : Matrix n1 n1 ℝ} {M2 : Matrix n2 n2 ℝ}
    (h0 : M0.IsSymm) (h1 : M1.IsSymm) (h2 : M2.IsSymm) (G : Matrix n1 n0 ℝ)
    (C : Matrix n2 n1 ℝ) (s : ℝ) :
    (massM M0 M1 M2 + s • stiffK G C)ᵀ = massM M0 M1 M2 - s • stiffK G C := by
  rw [transpose_add, transpose_smul, stiffK_transpose, (massM_isSymm h0 h1 h2).eq, smul_neg,
    sub_eq_add_neg]

omit [Fintype n0] [Fintype n1] [Fintype n2] [DecidableEq n0] [DecidableEq n1]
  [DecidableEq n2] in
/-- `K = 0` iff `G = 0` and `C = 0`. -/
theorem stiffK_eq_zero_iff (G : Matrix n1 n0 ℝ) (C : Matrix n2 n1 ℝ) :
    stiffK G C = 0 ↔ G = 0 ∧ C = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext i j; simpa [stiffK] using congrFun (congrFun h (.inr (.inl i))) (.inl j)
    · ext i j; simpa [stiffK] using congrFun (congrFun h (.inr (.inr i))) (.inr (.inl j))
  · rintro ⟨rfl, rfl⟩
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;> simp [stiffK]

omit [Fintype n0] [Fintype n1] [Fintype n2] [DecidableEq n0] [DecidableEq n1]
  [DecidableEq n2] in
/-- **The CN matrix is not symmetric** (Thesis Ch. 7, l. 4284–4285). For symmetric mass blocks,
`s ≠ 0` and nonzero coupling (`G ≠ 0` or `C ≠ 0`), `M + sK` is not symmetric, so MINRES does not
apply to the unsymmetrized CN system. Refutes the monolithic reading of
[QuennevilleBelair2015, Ch. 7] (MINRES on the CN matrix as it stands); under the
block-elimination reading the claim holds (`schurE_posDef`). -/
theorem cn_matrix_not_isSymm {M0 : Matrix n0 n0 ℝ} {M1 : Matrix n1 n1 ℝ} {M2 : Matrix n2 n2 ℝ}
    (h0 : M0.IsSymm) (h1 : M1.IsSymm) (h2 : M2.IsSymm) {G : Matrix n1 n0 ℝ}
    {C : Matrix n2 n1 ℝ} {s : ℝ} (hs : s ≠ 0) (hGC : G ≠ 0 ∨ C ≠ 0) :
    ¬ (massM M0 M1 M2 + s • stiffK G C).IsSymm := by
  intro h
  have he : massM M0 M1 M2 + s • stiffK G C = massM M0 M1 M2 - s • stiffK G C := by
    rw [← cn_matrix_transpose h0 h1 h2 G C s, h.eq]
  have hn : s • stiffK G C = -(s • stiffK G C) := by
    rw [sub_eq_add_neg] at he; exact add_left_cancel he
  have h2 : (2 : ℝ) • (s • stiffK G C) = 0 := by
    rw [two_smul]; nth_rewrite 2 [hn]; exact add_neg_cancel _
  have hK0 : stiffK G C = 0 :=
    (smul_eq_zero.mp ((smul_eq_zero.mp h2).resolve_left two_ne_zero)).resolve_left hs
  obtain ⟨rfl, rfl⟩ := (stiffK_eq_zero_iff G C).mp hK0
  simp at hGC

/-- `J` is invertible (`J² = I`). -/
theorem signJ_isUnit : IsUnit (signJ : Matrix (Idx n0 n1 n2) (Idx n0 n1 n2) ℝ) :=
  ⟨⟨signJ, signJ, signJ_mul_self, signJ_mul_self⟩, rfl⟩

/-- **The symmetrized CN matrix is nonsingular.** For SPD mass blocks and every `s`,
`J(M + sK)` is invertible. Together with `minres_symm` (symmetry) this is what MINRES needs.
Repair of [QuennevilleBelair2015, Ch. 7, l. 4284–4285]. -/
theorem minres_matrix_isUnit {M0 : Matrix n0 n0 ℝ} {M1 : Matrix n1 n1 ℝ} {M2 : Matrix n2 n2 ℝ}
    (h0 : M0.PosDef) (h1 : M1.PosDef) (h2 : M2.PosDef) (G : Matrix n1 n0 ℝ)
    (C : Matrix n2 n1 ℝ) (s : ℝ) : IsUnit (signJ * (massM M0 M1 M2 + s • stiffK G C)) :=
  signJ_isUnit.mul (cn_invertible h0 h1 h2 G C s)

/-- Diagonal of `J(M + sK)`: `−M0`, `M1`, `−M2`. -/
theorem minres_matrix_diag (M0 : Matrix n0 n0 ℝ) (M1 : Matrix n1 n1 ℝ) (M2 : Matrix n2 n2 ℝ)
    (G : Matrix n1 n0 ℝ) (C : Matrix n2 n1 ℝ) (s : ℝ) :
    (∀ i, (signJ * (massM M0 M1 M2 + s • stiffK G C) : Matrix (Idx n0 n1 n2) (Idx n0 n1 n2) ℝ)
      (.inl i) (.inl i) = -M0 i i) ∧
    (∀ i, (signJ * (massM M0 M1 M2 + s • stiffK G C) : Matrix (Idx n0 n1 n2) (Idx n0 n1 n2) ℝ)
      (.inr (.inl i)) (.inr (.inl i)) = M1 i i) ∧
    (∀ i, (signJ * (massM M0 M1 M2 + s • stiffK G C) : Matrix (Idx n0 n1 n2) (Idx n0 n1 n2) ℝ)
      (.inr (.inr i)) (.inr (.inr i)) = -M2 i i) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
    simp [signJ, massM, stiffK, diagonal_mul]

/-- **The symmetrized CN matrix is not positive definite** when the `σ` block or the `B` block
is nonempty (its diagonal has the entries `−M0 i i < 0`, `−M2 i i < 0`). So CG does not apply;
under the monolithic reading MINRES (symmetric indefinite) is the appropriate Krylov method.
Repair of
[QuennevilleBelair2015, Ch. 7, l. 4284–4285]. -/
theorem minres_matrix_not_posDef {M0 : Matrix n0 n0 ℝ} {M1 : Matrix n1 n1 ℝ}
    {M2 : Matrix n2 n2 ℝ} (h0 : M0.PosDef) (h2 : M2.PosDef) (G : Matrix n1 n0 ℝ)
    (C : Matrix n2 n1 ℝ) (s : ℝ) (hn : Nonempty n0 ∨ Nonempty n2) :
    ¬ (signJ * (massM M0 M1 M2 + s • stiffK G C)).PosDef := by
  intro h
  obtain ⟨d0, -, d2⟩ := minres_matrix_diag M0 M1 M2 G C s
  rcases hn with hn | hn
  · obtain ⟨i⟩ := hn
    have := h.diag_pos (i := .inl i); rw [d0] at this; linarith [h0.diag_pos (i := i)]
  · obtain ⟨i⟩ := hn
    have := h.diag_pos (i := .inr (.inr i)); rw [d2] at this; linarith [h2.diag_pos (i := i)]

/-- **Nor is it negative definite** when the `E` block is nonempty (diagonal entries
`M1 i i > 0`). With `minres_matrix_not_posDef`, `J(M + sK)` is indefinite for the full system
(4.14) with nonempty blocks. -/
theorem minres_matrix_not_negDef {M0 : Matrix n0 n0 ℝ} {M1 : Matrix n1 n1 ℝ}
    {M2 : Matrix n2 n2 ℝ} (h1 : M1.PosDef) (G : Matrix n1 n0 ℝ) (C : Matrix n2 n1 ℝ) (s : ℝ)
    [Nonempty n1] : ¬ (-(signJ * (massM M0 M1 M2 + s • stiffK G C))).PosDef := by
  intro h
  obtain ⟨-, d1, -⟩ := minres_matrix_diag M0 M1 M2 G C s
  obtain ⟨i⟩ := ‹Nonempty n1›
  have := h.diag_pos (i := .inr (.inl i))
  rw [neg_apply, d1] at this
  linarith [h1.diag_pos (i := i)]

/-- **The symmetrized CN system is equivalent to the CN system.**
`J(M + sK) x' = J(M − sK) x ⇔ (M + sK) x' = (M − sK) x`. -/
theorem minres_cn_iff (M0 : Matrix n0 n0 ℝ) (M1 : Matrix n1 n1 ℝ) (M2 : Matrix n2 n2 ℝ)
    (G : Matrix n1 n0 ℝ) (C : Matrix n2 n1 ℝ) (s : ℝ) (x x' : Idx n0 n1 n2 → ℝ) :
    (signJ * (massM M0 M1 M2 + s • stiffK G C)) *ᵥ x' =
        (signJ * (massM M0 M1 M2 - s • stiffK G C)) *ᵥ x ↔
      (massM M0 M1 M2 + s • stiffK G C) *ᵥ x' = (massM M0 M1 M2 - s • stiffK G C) *ᵥ x := by
  rw [← mulVec_mulVec x signJ (massM M0 M1 M2 - s • stiffK G C)]
  exact minres_system_iff _ _ _

/-- **Unique solvability of the symmetrized CN system** (SPD mass blocks, every `s`): for every
`x` there is exactly one `x'` with `J(M + sK) x' = J(M − sK) x`, namely the CN update
`(M + sK)⁻¹ (M − sK) x`. Repair of [QuennevilleBelair2015, Ch. 7, l. 4284–4285]. -/
theorem minres_cn_existsUnique {M0 : Matrix n0 n0 ℝ} {M1 : Matrix n1 n1 ℝ}
    {M2 : Matrix n2 n2 ℝ} (h0 : M0.PosDef) (h1 : M1.PosDef) (h2 : M2.PosDef)
    (G : Matrix n1 n0 ℝ) (C : Matrix n2 n1 ℝ) (s : ℝ) (x : Idx n0 n1 n2 → ℝ) :
    ∃! x', (signJ * (massM M0 M1 M2 + s • stiffK G C)) *ᵥ x' =
      (signJ * (massM M0 M1 M2 - s • stiffK G C)) *ᵥ x := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (cn_invertible h0 h1 h2 G C s)
  refine ⟨(massM M0 M1 M2 + s • stiffK G C)⁻¹ *ᵥ ((massM M0 M1 M2 - s • stiffK G C) *ᵥ x),
    ?_, fun y hy => ?_⟩
  · beta_reduce
    rw [minres_cn_iff, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  · beta_reduce at hy
    rw [minres_cn_iff] at hy
    rw [← hy, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]

/-- **Packaged: the symmetrized CN matrix is symmetric, nonsingular and indefinite.** For SPD
mass blocks, every `s`, a nonempty `E` block and a nonempty `σ` or `B` block, `A = J(M + sK)`
is symmetric, invertible, and has vectors `v`, `w` with `vᵀAv < 0 < wᵀAw` (basis vectors of the
`σ`/`B` block and of the `E` block). These are exactly the matrix properties for which MINRES
(and not CG) is the Krylov method. Repair of [QuennevilleBelair2015, Ch. 7, l. 4284–4285] under
the monolithic reading. -/
theorem minres_matrix_indefinite {M0 : Matrix n0 n0 ℝ} {M1 : Matrix n1 n1 ℝ}
    {M2 : Matrix n2 n2 ℝ} (h0 : M0.PosDef) (h1 : M1.PosDef) (h2 : M2.PosDef)
    (G : Matrix n1 n0 ℝ) (C : Matrix n2 n1 ℝ) (s : ℝ) [Nonempty n1]
    (hn : Nonempty n0 ∨ Nonempty n2) :
    (signJ * (massM M0 M1 M2 + s • stiffK G C)).IsSymm ∧
      IsUnit (signJ * (massM M0 M1 M2 + s • stiffK G C)) ∧
      (∃ v, v ⬝ᵥ ((signJ * (massM M0 M1 M2 + s • stiffK G C)) *ᵥ v) < 0) ∧
      ∃ w, 0 < w ⬝ᵥ ((signJ * (massM M0 M1 M2 + s • stiffK G C)) *ᵥ w) := by
  have hd : ∀ (A : Matrix (Idx n0 n1 n2) (Idx n0 n1 n2) ℝ) k,
      Pi.single k 1 ⬝ᵥ (A *ᵥ Pi.single k 1) = A k k := fun A k => by
    simp
  obtain ⟨d0, d1, d2⟩ := minres_matrix_diag M0 M1 M2 G C s
  refine ⟨minres_symm h0.isHermitian.eq h1.isHermitian.eq h2.isHermitian.eq G C s,
    minres_matrix_isUnit h0 h1 h2 G C s, ?_, ?_⟩
  · rcases hn with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
    · exact ⟨Pi.single (.inl i) 1, by rw [hd, d0]; linarith [h0.diag_pos (i := i)]⟩
    · exact ⟨Pi.single (.inr (.inr i)) 1, by rw [hd, d2]; linarith [h2.diag_pos (i := i)]⟩
  · obtain ⟨i⟩ := ‹Nonempty n1›
    exact ⟨Pi.single (.inr (.inl i)) 1, by rw [hd, d1]; exact h1.diag_pos⟩

end MatrixLevel

/-! ## Block elimination (Schur complement) reading of Ch. 7

Thesis l. 4284–4285 inverts the mass matrices separately (CG + Jacobi). This fits a block
elimination: eliminate `σ'` and `B'` with `M0⁻¹`, `M2⁻¹` and solve the `E` Schur complement
system `S E' = rhs`, `S = M1 + s²(G M0⁻¹ Gᵀ + Cᵀ M2⁻¹ C)`. Under this reading the "other
matrix" is `S`, which is SPD (`schurE_posDef`), so MINRES applies to it directly (as would CG),
and the thesis claim is true as stated. `cn_schur_iff` proves that the elimination is
equivalent to the monolithic CN system. -/

section Schur

variable {n0 n1 n2 : Type*} [Fintype n0] [Fintype n1] [Fintype n2]
  [DecidableEq n0] [DecidableEq n1] [DecidableEq n2]

/-- `σ` block of a vector on `Idx n0 n1 n2`. -/
def blk0 (x : Idx n0 n1 n2 → ℝ) : n0 → ℝ := fun i => x (.inl i)
/-- `E` block. -/
def blk1 (x : Idx n0 n1 n2 → ℝ) : n1 → ℝ := fun i => x (.inr (.inl i))
/-- `B` block. -/
def blk2 (x : Idx n0 n1 n2 → ℝ) : n2 → ℝ := fun i => x (.inr (.inr i))

/-- The `E` Schur complement `S = M1 + s²(G M0⁻¹ Gᵀ + Cᵀ M2⁻¹ C)` of the CN matrix. -/
def schurE (M0 : Matrix n0 n0 ℝ) (M1 : Matrix n1 n1 ℝ) (M2 : Matrix n2 n2 ℝ)
    (G : Matrix n1 n0 ℝ) (C : Matrix n2 n1 ℝ) (s : ℝ) : Matrix n1 n1 ℝ :=
  M1 + s ^ 2 • (G * M0⁻¹ * Gᵀ + Cᵀ * M2⁻¹ * C)

omit [DecidableEq n0] [DecidableEq n1] [DecidableEq n2] in
/-- Block rows of `(M + sK) x`: `M0 σ − s Gᵀ E`, `M1 E + s G σ + s Cᵀ B`, `M2 B − s C E`. -/
theorem cn_mulVec_eq_iff (M0 : Matrix n0 n0 ℝ) (M1 : Matrix n1 n1 ℝ) (M2 : Matrix n2 n2 ℝ)
    (G : Matrix n1 n0 ℝ) (C : Matrix n2 n1 ℝ) (s : ℝ) (x r : Idx n0 n1 n2 → ℝ) :
    (massM M0 M1 M2 + s • stiffK G C) *ᵥ x = r ↔
      M0 *ᵥ blk0 x - s • (Gᵀ *ᵥ blk1 x) = blk0 r ∧
      M1 *ᵥ blk1 x + s • (G *ᵥ blk0 x) + s • (Cᵀ *ᵥ blk2 x) = blk1 r ∧
      M2 *ᵥ blk2 x - s • (C *ᵥ blk1 x) = blk2 r := by
  have e0 : ∀ i, ((massM M0 M1 M2 + s • stiffK G C) *ᵥ x) (.inl i) =
      (M0 *ᵥ blk0 x - s • (Gᵀ *ᵥ blk1 x)) i := fun i => by
    simp [mulVec, dotProduct, Fintype.sum_sum_type, massM, stiffK, blk0, blk1,
      Finset.mul_sum, sub_eq_add_neg, mul_assoc, mul_comm]
  have e1 : ∀ i, ((massM M0 M1 M2 + s • stiffK G C) *ᵥ x) (.inr (.inl i)) =
      (M1 *ᵥ blk1 x + s • (G *ᵥ blk0 x) + s • (Cᵀ *ᵥ blk2 x)) i := fun i => by
    simp [mulVec, dotProduct, Fintype.sum_sum_type, massM, stiffK, blk0, blk1, blk2,
      Finset.mul_sum, mul_assoc, mul_comm]
    ring
  have e2 : ∀ i, ((massM M0 M1 M2 + s • stiffK G C) *ᵥ x) (.inr (.inr i)) =
      (M2 *ᵥ blk2 x - s • (C *ᵥ blk1 x)) i := fun i => by
    simp [mulVec, dotProduct, Fintype.sum_sum_type, massM, stiffK, blk1, blk2,
      Finset.mul_sum, sub_eq_add_neg, mul_assoc, mul_comm]
    ring
  constructor
  · rintro rfl
    exact ⟨funext fun i => (e0 i).symm, funext fun i => (e1 i).symm,
      funext fun i => (e2 i).symm⟩
  · rintro ⟨h0, h1, h2⟩
    funext k
    rcases k with i | i | i
    · rw [e0, h0]; rfl
    · rw [e1, h1]; rfl
    · rw [e2, h2]; rfl

omit [Fintype n0] [Fintype n1] [Fintype n2] [DecidableEq n0] [DecidableEq n1]
  [DecidableEq n2] in
lemma mulVec_eq_iff_inv {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}
    (hM : IsUnit M) (y v : n → ℝ) : M *ᵥ y = v ↔ y = M⁻¹ *ᵥ v := by
  have hdet := (isUnit_iff_isUnit_det M).mp hM
  constructor
  · rintro rfl; rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  · rintro rfl; rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]

omit [DecidableEq n1] in
/-- **Block elimination of the CN system.** For SPD `M0`, `M2` (any `M1`, `s`), the CN system
`(M + sK) x = r` holds iff
`σ = M0⁻¹(r₀ + s Gᵀ E)`, `B = M2⁻¹(r₂ + s C E)` and
`S E = r₁ − s G M0⁻¹ r₀ − s Cᵀ M2⁻¹ r₂` with `S = schurE`. So a CN step can be computed by two
mass-matrix solves (CG + Jacobi in the thesis) around one solve with `S`. Supports the
block-elimination reading of [QuennevilleBelair2015, Ch. 7, l. 4284–4285]. -/
theorem cn_schur_iff {M0 : Matrix n0 n0 ℝ} (M1 : Matrix n1 n1 ℝ) {M2 : Matrix n2 n2 ℝ}
    (h0 : M0.PosDef) (h2 : M2.PosDef) (G : Matrix n1 n0 ℝ) (C : Matrix n2 n1 ℝ) (s : ℝ)
    (x r : Idx n0 n1 n2 → ℝ) :
    (massM M0 M1 M2 + s • stiffK G C) *ᵥ x = r ↔
      blk0 x = M0⁻¹ *ᵥ (blk0 r + s • (Gᵀ *ᵥ blk1 x)) ∧
      blk2 x = M2⁻¹ *ᵥ (blk2 r + s • (C *ᵥ blk1 x)) ∧
      schurE M0 M1 M2 G C s *ᵥ blk1 x =
        blk1 r - s • (G *ᵥ (M0⁻¹ *ᵥ blk0 r)) - s • (Cᵀ *ᵥ (M2⁻¹ *ᵥ blk2 r)) := by
  rw [cn_mulVec_eq_iff]
  have r0 : M0 *ᵥ blk0 x - s • (Gᵀ *ᵥ blk1 x) = blk0 r ↔
      blk0 x = M0⁻¹ *ᵥ (blk0 r + s • (Gᵀ *ᵥ blk1 x)) := by
    rw [sub_eq_iff_eq_add]; exact mulVec_eq_iff_inv h0.isUnit _ _
  have r2 : M2 *ᵥ blk2 x - s • (C *ᵥ blk1 x) = blk2 r ↔
      blk2 x = M2⁻¹ *ᵥ (blk2 r + s • (C *ᵥ blk1 x)) := by
    rw [sub_eq_iff_eq_add]; exact mulVec_eq_iff_inv h2.isUnit _ _
  rw [r0, r2]
  constructor
  · rintro ⟨hσ, h1, hB⟩
    refine ⟨hσ, hB, ?_⟩
    rw [hσ, hB] at h1
    rw [← h1]
    simp only [schurE, add_mulVec, smul_mulVec, mulVec_add, mulVec_smul, ← mulVec_mulVec]
    module
  · rintro ⟨hσ, hB, hS⟩
    refine ⟨hσ, ?_, hB⟩
    rw [hσ, hB]
    rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq] at hS
    rw [← hS]
    simp only [schurE, add_mulVec, smul_mulVec, mulVec_add, mulVec_smul, ← mulVec_mulVec]
    module

omit [DecidableEq n1] in
/-- **The Schur complement is SPD.** For SPD `M0, M1, M2` and every `s`,
`S = M1 + s²(G M0⁻¹ Gᵀ + Cᵀ M2⁻¹ C)` is positive definite, so MINRES (and CG) apply to the
`E` system of the block elimination. Under this reading the thesis claim
[QuennevilleBelair2015, Ch. 7, l. 4284–4285] holds as stated. -/
theorem schurE_posDef {M0 : Matrix n0 n0 ℝ} {M1 : Matrix n1 n1 ℝ} {M2 : Matrix n2 n2 ℝ}
    (h0 : M0.PosDef) (h1 : M1.PosDef) (h2 : M2.PosDef) (G : Matrix n1 n0 ℝ)
    (C : Matrix n2 n1 ℝ) (s : ℝ) : (schurE M0 M1 M2 G C s).PosDef := by
  have hG : (G * M0⁻¹ * Gᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      h0.inv.posSemidef.mul_mul_conjTranspose_same G
  have hC : (Cᵀ * M2⁻¹ * C).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      h2.inv.posSemidef.conjTranspose_mul_mul_same C
  exact h1.add_posSemidef ((hG.add hC).smul (sq_nonneg s))

/-- **The CN step via block elimination.** For SPD blocks and every `s`, if
`(M + sK) x' = r` (for the CN step, `r = (M − sK) x`), then the `E` block of `x'` is
`S⁻¹(r₁ − s G M0⁻¹ r₀ − s Cᵀ M2⁻¹ r₂)`; its `σ`, `B` blocks are then given by the two mass
solves of `cn_schur_iff`. -/
theorem cn_step_schur {M0 : Matrix n0 n0 ℝ} {M1 : Matrix n1 n1 ℝ} {M2 : Matrix n2 n2 ℝ}
    (h0 : M0.PosDef) (h1 : M1.PosDef) (h2 : M2.PosDef) (G : Matrix n1 n0 ℝ)
    (C : Matrix n2 n1 ℝ) (s : ℝ) {x' r : Idx n0 n1 n2 → ℝ}
    (hx' : (massM M0 M1 M2 + s • stiffK G C) *ᵥ x' = r) :
    blk1 x' = (schurE M0 M1 M2 G C s)⁻¹ *ᵥ
      (blk1 r - s • (G *ᵥ (M0⁻¹ *ᵥ blk0 r)) - s • (Cᵀ *ᵥ (M2⁻¹ *ᵥ blk2 r))) :=
  (mulVec_eq_iff_inv (schurE_posDef h0 h1 h2 G C s).isUnit _ _).1
    ((cn_schur_iff M1 h0 h2 G C s x' r).1 hx').2.2

end Schur

/-! ## Bridge: the assembled CN system of (4.14) / (4.15) -/

section Bridge

variable {V0 V1 V2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0] [FiniteDimensional ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1] [FiniteDimensional ℝ V1]
  [NormedAddCommGroup V2] [InnerProductSpace ℝ V2] [FiniteDimensional ℝ V2]
  {n0 n1 n2 : Type*} [Fintype n0] [Fintype n1] [Fintype n2]
  [DecidableEq n0] [DecidableEq n1] [DecidableEq n2]

/-- Assembled discrete gradient `Gᵢⱼ = (b1ᵢ, d0 b0ⱼ)`. -/
def gradMat (b0 : Module.Basis n0 ℝ V0) (b1 : Module.Basis n1 ℝ V1) (d0 : V0 →ₗ[ℝ] V1) :
    Matrix n1 n0 ℝ :=
  Matrix.of fun i j => ⟪b1 i, d0 (b0 j)⟫

/-- Assembled discrete curl `Cᵢⱼ = (b2ᵢ, d1 b1ⱼ)`. -/
def curlMat (b1 : Module.Basis n1 ℝ V1) (b2 : Module.Basis n2 ℝ V2) (d1 : V1 →ₗ[ℝ] V2) :
    Matrix n2 n1 ℝ :=
  Matrix.of fun i j => ⟪b2 i, d1 (b1 j)⟫

/-- Coefficient vector of a state `(σ, E, B)` in the bases `b0, b1, b2`. -/
def coordVec (b0 : Module.Basis n0 ℝ V0) (b1 : Module.Basis n1 ℝ V1)
    (b2 : Module.Basis n2 ℝ V2) (x : V0 × V1 × V2) : Idx n0 n1 n2 → ℝ :=
  Sum.elim (fun i => b0.repr x.1 i) (Sum.elim (fun i => b1.repr x.2.1 i) fun i => b2.repr x.2.2 i)

/-- Load vector: the inner products of a state with the basis functions (testing). -/
def rowVec (b0 : Module.Basis n0 ℝ V0) (b1 : Module.Basis n1 ℝ V1)
    (b2 : Module.Basis n2 ℝ V2) (y : V0 × V1 × V2) : Idx n0 n1 n2 → ℝ :=
  Sum.elim (fun i => ⟪b0 i, y.1⟫) (Sum.elim (fun i => ⟪b1 i, y.2.1⟫) fun i => ⟪b2 i, y.2.2⟫)

omit [FiniteDimensional ℝ V0] [DecidableEq n0] in
/-- Expansion of `⟪w, y⟫` in the coefficients of `y`. -/
lemma inner_eq_sum_repr (b : Module.Basis n0 ℝ V0) (w y : V0) :
    ⟪w, y⟫ = ∑ j, b.repr y j * ⟪w, b j⟫ := by
  conv_lhs => rw [← b.sum_repr y]
  rw [inner_sum]
  simp [inner_smul_right]

omit [FiniteDimensional ℝ V0] [DecidableEq n0] in
/-- Testing against a basis determines a vector. -/
lemma eq_of_inner_basis (b : Module.Basis n0 ℝ V0) {y y' : V0}
    (h : ∀ i, ⟪b i, y⟫ = ⟪b i, y'⟫) : y = y' := by
  refine ext_inner_left ℝ fun w => ?_
  rw [← b.sum_repr w, sum_inner, sum_inner]
  simp [inner_smul_left, h]

omit [FiniteDimensional ℝ V0] [FiniteDimensional ℝ V1] [FiniteDimensional ℝ V2]
  [DecidableEq n0] [DecidableEq n1] [DecidableEq n2] in
/-- `rowVec` is injective. -/
lemma rowVec_injective (b0 : Module.Basis n0 ℝ V0) (b1 : Module.Basis n1 ℝ V1)
    (b2 : Module.Basis n2 ℝ V2) : Function.Injective (rowVec b0 b1 b2) := by
  intro y y' h
  have h0 : y.1 = y'.1 := eq_of_inner_basis b0 fun i => congrFun h (.inl i)
  have h1 : y.2.1 = y'.2.1 := eq_of_inner_basis b1 fun i => congrFun h (.inr (.inl i))
  have h2 : y.2.2 = y'.2.2 := eq_of_inner_basis b2 fun i => congrFun h (.inr (.inr i))
  exact Prod.ext h0 (Prod.ext h1 h2)

omit [DecidableEq n0] [DecidableEq n1] [DecidableEq n2] in
/-- **Assembly.** Testing the operator CN left side `fullLHS d0 d1 s x` against the basis gives
`(M + sK) c(x)` with the Gram mass matrices, `G = gradMat`, `C = curlMat`. -/
theorem rowVec_fullLHS (b0 : Module.Basis n0 ℝ V0) (b1 : Module.Basis n1 ℝ V1)
    (b2 : Module.Basis n2 ℝ V2) (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (s : ℝ)
    (x : V0 × V1 × V2) :
    rowVec b0 b1 b2 (fullLHS d0 d1 s x) =
      (massM (gram ℝ b0) (gram ℝ b1) (gram ℝ b2) +
        s • stiffK (gradMat b0 b1 d0) (curlMat b1 b2 d1)) *ᵥ coordVec b0 b1 b2 x := by
  obtain ⟨σ, E, B⟩ := x
  funext i
  rcases i with i | i | i
  · simp only [rowVec, fullLHS, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, inner_sub_right,
      inner_smul_right, adjoint_inner_right]
    rw [inner_eq_sum_repr b0 (b0 i) σ, inner_eq_sum_repr b1 (d0 (b0 i)) E]
    simp [mulVec, dotProduct, Fintype.sum_sum_type, massM, stiffK, gradMat, coordVec,
      Finset.mul_sum, real_inner_comm, mul_comm, sub_eq_add_neg, mul_assoc]
  · simp only [rowVec, fullLHS, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr, Sum.elim_inl,
      inner_add_right, inner_smul_right, adjoint_inner_right]
    rw [show ⟪b1 i, d0 σ⟫ = ⟪adjoint d0 (b1 i), σ⟫ from (adjoint_inner_left _ _ _).symm,
      inner_eq_sum_repr b1 (b1 i) E, inner_eq_sum_repr b0 (adjoint d0 (b1 i)) σ,
      inner_eq_sum_repr b2 (d1 (b1 i)) B]
    simp [mulVec, dotProduct, Fintype.sum_sum_type, massM, stiffK, gradMat, curlMat, coordVec,
      Finset.mul_sum, adjoint_inner_left, real_inner_comm, mul_comm, mul_add]
    ring_nf
  · simp only [rowVec, fullLHS, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr,
      inner_sub_right, inner_smul_right]
    rw [show ⟪b2 i, d1 E⟫ = ⟪adjoint d1 (b2 i), E⟫ from (adjoint_inner_left _ _ _).symm,
      inner_eq_sum_repr b2 (b2 i) B, inner_eq_sum_repr b1 (adjoint d1 (b2 i)) E]
    simp [mulVec, dotProduct, Fintype.sum_sum_type, massM, stiffK, curlMat, coordVec,
      Finset.mul_sum, adjoint_inner_left, real_inner_comm, mul_comm, sub_eq_add_neg]
    ring_nf

omit [DecidableEq n0] [DecidableEq n1] [DecidableEq n2] in
/-- **A CN step of (4.14) is the assembled linear system.** For bases `b0, b1, b2`,
`FullStep d0 d1 s x x'` holds iff `(M + sK) c(x') = (M − sK) c(x)` with Gram mass matrices,
`G = gradMat b0 b1 d0` and `C = curlMat b1 b2 d1`. Links the matrix section of
`Feec.Legacy.CrankNicolson` to the scheme (Thesis Ch. 7, (4.14) with CN). -/
theorem fullStep_iff_matrix (b0 : Module.Basis n0 ℝ V0) (b1 : Module.Basis n1 ℝ V1)
    (b2 : Module.Basis n2 ℝ V2) (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (s : ℝ)
    (x x' : V0 × V1 × V2) :
    FullStep d0 d1 s x.1 x'.1 x.2.1 x'.2.1 x.2.2 x'.2.2 ↔
      (massM (gram ℝ b0) (gram ℝ b1) (gram ℝ b2) +
          s • stiffK (gradMat b0 b1 d0) (curlMat b1 b2 d1)) *ᵥ coordVec b0 b1 b2 x' =
        (massM (gram ℝ b0) (gram ℝ b1) (gram ℝ b2) -
          s • stiffK (gradMat b0 b1 d0) (curlMat b1 b2 d1)) *ᵥ coordVec b0 b1 b2 x := by
  rw [fullStep_iff, sub_eq_add_neg, ← neg_smul, ← rowVec_fullLHS, ← rowVec_fullLHS]
  exact (rowVec_injective b0 b1 b2).eq_iff.symm

omit [FiniteDimensional ℝ V0] [DecidableEq n0] in
/-- Gram matrices of bases are SPD (the FE mass matrices). -/
lemma gram_posDef (b : Module.Basis n0 ℝ V0) : (gram ℝ b).PosDef :=
  posDef_gram_of_linearIndependent b.linearIndependent

/-- **The MINRES system has the CN iterate as its unique solution.** With the assembled
matrices of `fullStep_iff_matrix`, a vector `v` solves the symmetrized system
`J(M + sK) v = J(M − sK) c(x)` iff `v = c(cnStep d0 d1 s x)`, the coefficient vector of the
CN iterate. So the system MINRES is applied to (symmetric by `minres_symm`, nonsingular by
`minres_matrix_isUnit`, indefinite by `minres_matrix_not_posDef`) computes exactly the CN step
of (4.14). Repair of [QuennevilleBelair2015, Ch. 7, l. 4284–4285]. -/
theorem minres_solution_iff_cnStep (b0 : Module.Basis n0 ℝ V0) (b1 : Module.Basis n1 ℝ V1)
    (b2 : Module.Basis n2 ℝ V2) (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (s : ℝ)
    (x : V0 × V1 × V2) (v : Idx n0 n1 n2 → ℝ) :
    (signJ * (massM (gram ℝ b0) (gram ℝ b1) (gram ℝ b2) +
          s • stiffK (gradMat b0 b1 d0) (curlMat b1 b2 d1))) *ᵥ v =
        (signJ * (massM (gram ℝ b0) (gram ℝ b1) (gram ℝ b2) -
          s • stiffK (gradMat b0 b1 d0) (curlMat b1 b2 d1))) *ᵥ coordVec b0 b1 b2 x ↔
      v = coordVec b0 b1 b2 (cnStep d0 d1 s x) := by
  have hc : (signJ * (massM (gram ℝ b0) (gram ℝ b1) (gram ℝ b2) +
          s • stiffK (gradMat b0 b1 d0) (curlMat b1 b2 d1))) *ᵥ
        coordVec b0 b1 b2 (cnStep d0 d1 s x) =
      (signJ * (massM (gram ℝ b0) (gram ℝ b1) (gram ℝ b2) -
          s • stiffK (gradMat b0 b1 d0) (curlMat b1 b2 d1))) *ᵥ coordVec b0 b1 b2 x :=
    (minres_cn_iff _ _ _ _ _ _ _ _).2
      ((fullStep_iff_matrix b0 b1 b2 d0 d1 s x _).1 (fullStep_cnStep d0 d1 s x))
  obtain ⟨_, -, huniq⟩ := minres_cn_existsUnique (gram_posDef b0) (gram_posDef b1)
    (gram_posDef b2) (gradMat b0 b1 d0) (curlMat b1 b2 d1) s (coordVec b0 b1 b2 x)
  constructor
  · intro hv; exact (huniq v hv).trans (huniq _ hc).symm
  · rintro rfl; exact hc

omit [FiniteDimensional ℝ V0] [FiniteDimensional ℝ V1] [FiniteDimensional ℝ V2]
  [Fintype n0] [DecidableEq n0] [DecidableEq n1] [DecidableEq n2] in
/-- `gradMat = 0` iff `d0 = 0`. -/
lemma gradMat_eq_zero_iff (b0 : Module.Basis n0 ℝ V0) (b1 : Module.Basis n1 ℝ V1)
    (d0 : V0 →ₗ[ℝ] V1) : gradMat b0 b1 d0 = 0 ↔ d0 = 0 := by
  constructor
  · intro h
    refine b0.ext fun j => eq_of_inner_basis b1 fun i => ?_
    simpa [gradMat] using congrFun (congrFun h i) j
  · rintro rfl; ext i j; simp [gradMat]

omit [FiniteDimensional ℝ V0] [FiniteDimensional ℝ V1] [FiniteDimensional ℝ V2]
  [Fintype n1] [DecidableEq n0] [DecidableEq n1] [DecidableEq n2] in
/-- `curlMat = 0` iff `d1 = 0`. -/
lemma curlMat_eq_zero_iff (b1 : Module.Basis n1 ℝ V1) (b2 : Module.Basis n2 ℝ V2)
    (d1 : V1 →ₗ[ℝ] V2) : curlMat b1 b2 d1 = 0 ↔ d1 = 0 := by
  constructor
  · intro h
    refine b1.ext fun j => eq_of_inner_basis b2 fun i => ?_
    simpa [curlMat] using congrFun (congrFun h i) j
  · rintro rfl; ext i j; simp [curlMat]

omit [FiniteDimensional ℝ V0] [FiniteDimensional ℝ V1] [FiniteDimensional ℝ V2]
  [Fintype n0] [DecidableEq n0] [DecidableEq n1] [DecidableEq n2] in
/-- **The assembled CN matrix of (4.14) is not symmetric** for `s ≠ 0` as soon as `grad` or
`curl` is nonzero on the FE spaces. So MINRES does not apply to the CN matrix itself, only to
its `J`-symmetrization. Refutes the monolithic reading of [QuennevilleBelair2015, Ch. 7]
(see the module docstring for the block-elimination reading, under which the claim holds). -/
theorem cnSystem_not_isSymm_of_ne (b0 : Module.Basis n0 ℝ V0) (b1 : Module.Basis n1 ℝ V1)
    (b2 : Module.Basis n2 ℝ V2) {d0 : V0 →ₗ[ℝ] V1} {d1 : V1 →ₗ[ℝ] V2} {s : ℝ} (hs : s ≠ 0)
    (hd : d0 ≠ 0 ∨ d1 ≠ 0) :
    ¬ (massM (gram ℝ b0) (gram ℝ b1) (gram ℝ b2) +
        s • stiffK (gradMat b0 b1 d0) (curlMat b1 b2 d1)).IsSymm :=
  cn_matrix_not_isSymm (isHermitian_gram ℝ b0).eq (isHermitian_gram ℝ b1).eq
    (isHermitian_gram ℝ b2).eq hs
    (hd.imp (mt (gradMat_eq_zero_iff b0 b1 d0).1) (mt (curlMat_eq_zero_iff b1 b2 d1).1))

omit [DecidableEq n0] [DecidableEq n1] [DecidableEq n2] in
/-- **The reduced system (4.15).** With an empty `σ` block (`n0` empty, so `V0 = 0` and `J`
is `diag(I, −I)` on the `E`, `B` blocks), a reduced CN step `RedStep d1 s E E' B B'` holds iff
the assembled system `(M + sK) c(0, E', B') = (M − sK) c(0, E, B)` holds. -/
theorem redStep_iff_matrix [IsEmpty n0] (b0 : Module.Basis n0 ℝ V0)
    (b1 : Module.Basis n1 ℝ V1) (b2 : Module.Basis n2 ℝ V2) (d0 : V0 →ₗ[ℝ] V1)
    (d1 : V1 →ₗ[ℝ] V2) (s : ℝ) (E E' : V1) (B B' : V2) :
    RedStep d1 s E E' B B' ↔
      (massM (gram ℝ b0) (gram ℝ b1) (gram ℝ b2) +
          s • stiffK (gradMat b0 b1 d0) (curlMat b1 b2 d1)) *ᵥ coordVec b0 b1 b2 (0, E', B') =
        (massM (gram ℝ b0) (gram ℝ b1) (gram ℝ b2) -
          s • stiffK (gradMat b0 b1 d0) (curlMat b1 b2 d1)) *ᵥ coordVec b0 b1 b2 (0, E, B) := by
  have hV0 : ∀ v : V0, v = 0 := fun v => b0.ext_elem fun i => isEmptyElim i
  rw [← fullStep_iff_matrix b0 b1 b2 d0 d1 s (0, E, B) (0, E', B')]
  simp only [FullStep, RedStep, add_zero, map_zero, zero_add]
  exact ⟨fun h => ⟨(hV0 _).trans (hV0 _).symm, h⟩, fun h => h.2⟩

/-- **MINRES for the reduced system (4.15).** With an empty `σ` block, `v` solves the
symmetrized system `J(M + sK) v = J(M − sK) c(0, E, B)` iff `v = c(0, E', B')` for the unique
reduced CN step `(E, B) ↦ (E', B')`. Repair of [QuennevilleBelair2015, Ch. 7, l. 4284–4285]
for (4.15). -/
theorem minres_solution_iff_redStep [IsEmpty n0] (b0 : Module.Basis n0 ℝ V0)
    (b1 : Module.Basis n1 ℝ V1) (b2 : Module.Basis n2 ℝ V2) (d0 : V0 →ₗ[ℝ] V1)
    (d1 : V1 →ₗ[ℝ] V2) (s : ℝ) (E : V1) (B : V2) (v : Idx n0 n1 n2 → ℝ) :
    (signJ * (massM (gram ℝ b0) (gram ℝ b1) (gram ℝ b2) +
          s • stiffK (gradMat b0 b1 d0) (curlMat b1 b2 d1))) *ᵥ v =
        (signJ * (massM (gram ℝ b0) (gram ℝ b1) (gram ℝ b2) -
          s • stiffK (gradMat b0 b1 d0) (curlMat b1 b2 d1))) *ᵥ coordVec b0 b1 b2 (0, E, B) ↔
      ∃ E' B', RedStep d1 s E E' B B' ∧ v = coordVec b0 b1 b2 (0, E', B') := by
  obtain ⟨⟨E', B'⟩, hr, -⟩ := red_step_existsUnique d1 s E B
  have hc := (minres_cn_iff _ _ _ _ _ _ _ _).2
    ((redStep_iff_matrix b0 b1 b2 d0 d1 s E E' B B').1 hr)
  obtain ⟨_, -, huniq⟩ := minres_cn_existsUnique (gram_posDef b0) (gram_posDef b1)
    (gram_posDef b2) (gradMat b0 b1 d0) (curlMat b1 b2 d1) s (coordVec b0 b1 b2 (0, E, B))
  constructor
  · intro hv; exact ⟨E', B', hr, (huniq v hv).trans (huniq _ hc).symm⟩
  · rintro ⟨E'', B'', hr', rfl⟩
    exact (minres_cn_iff _ _ _ _ _ _ _ _).2
      ((redStep_iff_matrix b0 b1 b2 d0 d1 s E E'' B B'').1 hr')

end Bridge

end Feec.Legacy.Minres
