module

public import Feec.Ch7.CrankNicolson
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Repair of the thesis Ch. 7 solver claim: MINRES on the symmetrized Crank–Nicolson system

[QuennevilleBelair2015, Ch. 7, l. 4284–4285]: the mass matrices are inverted by
Jacobi-preconditioned CG and "other matrices are inverted with MINRES preconditioned with AMG".
Implicitly these are the Crank–Nicolson (CN) matrices of the full system (4.14) and the reduced
system (4.15), and MINRES applies to them.

Defect. MINRES needs a symmetric nonsingular matrix. In the natural block form the CN matrix
`M + sK` (`M = diag(M0, M1, M2)` SPD, `K` skew, `s = Δt/2`) is nonsingular but not symmetric
whenever `s ≠ 0` and the coupling is nonzero (`cn_matrix_not_isSymm`), so MINRES does not apply
to it as written. The thesis never assembles the system.

Repair (this file), building on `Feec.CrankNicolson` (§2 there: `minres_symm`,
`minres_system_iff`, `cn_invertible`).
* Matrix level. `cn_matrix_transpose`: `(M + sK)ᵀ = M − sK`; `cn_matrix_not_isSymm`;
  `minres_matrix_isUnit`: `J(M + sK)` is nonsingular (`J = diag(−I, I, −I)`);
  `minres_matrix_not_posDef`, `minres_matrix_not_negDef`: it is indefinite as soon as the
  `σ`/`B` blocks and the `E` block are nonempty, so CG does not apply and MINRES is the right
  Krylov method; `minres_cn_existsUnique`, `minres_cn_iff`: the symmetrized CN system
  `J(M + sK) x' = J(M − sK) x` has exactly one solution, the CN update.
* Bridge to the scheme. For bases `b0, b1, b2` of the FE spaces `V0, V1, V2` (with their `L²`
  inner products) and `d0 = grad`, `d1 = curl`: `Mᵢ` are the Gram (mass) matrices
  (`Matrix.gram`), `G = gradMat` (`Gᵢⱼ = (b1ᵢ, d0 b0ⱼ)`), `C = curlMat`
  (`Cᵢⱼ = (b2ᵢ, d1 b1ⱼ)`), and `coordVec` the coefficient vector. `fullStep_iff_matrix`: a full
  CN step of (4.14) (`Feec.CrankNicolson.FullStep`) is exactly `(M + sK) c(x') = (M − sK) c(x)`;
  `minres_solution_iff_cnStep`: a vector solves the symmetrized system iff it is the coefficient
  vector of the CN iterate `cnStep x`; `cnSystem_not_isSymm_of_ne`: for `s ≠ 0` and
  `d0 ≠ 0 ∨ d1 ≠ 0` the assembled `M + sK` is not symmetric. The reduced system (4.15) is the
  case of an empty `σ` block (`redStep_iff_matrix`, `minres_solution_iff_redStep`), where `J`
  is `diag(I, −I)`.

Not formalized: AMG preconditioning and MINRES convergence (numerical).
-/

open Matrix LinearMap InnerProductSpace
open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace Feec.Repair.C67

open Feec.CrankNicolson

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
apply to the unsymmetrized CN system. Refutes the implicit claim of
[QuennevilleBelair2015, Ch. 7] that MINRES applies to the CN matrices as they stand. -/
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
MINRES (symmetric indefinite) is the appropriate Krylov method. Repair of
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

end MatrixLevel

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
`Feec.CrankNicolson` to the scheme (Thesis Ch. 7, (4.14) with CN). -/
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
its `J`-symmetrization. Refutes the implicit claim of [QuennevilleBelair2015, Ch. 7]. -/
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

end Feec.Repair.C67
