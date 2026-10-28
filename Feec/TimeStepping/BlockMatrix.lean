module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Algebra.Order.Star.Real
public import Feec.TimeStepping.Cayley

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

This holds for any number of blocks (any length of the complex) and any commutative ring;
`TimeStepping.isHermitian_diagonal_mul_add_smul` is the Hermitian form over a star ring.

## Crank–Nicolson for a bounded generator in a basis

For a basis `b` of an inner product space over `ℝ` or `ℂ`, with Gram (mass) matrix `M` and
stiffness `K i j = -⟪bᵢ, T bⱼ⟫` (`stiffness`) of a linear map `T`:

* `isCNStep_iff_mulVec`: `u'` is a CN step from `u` for `u' = T u` iff
  `(M + sK) c(u') = (M - sK) c(u)`;
* `diagonal_mul_mulVec_iff_isCNStep`: the signed system `diag(ε) (M + sK) w = diag(ε) (M - sK) c(u)`
  has the CN steps as solutions;
* `isHermitian_signed_cn`: for a skew `T` and signs adapted to `b`, `diag(ε) (M + sK)` is
  Hermitian. The crown's fully discrete Crank–Nicolson scheme reads through these
  (`Feec.HilbertComplex.SkewFEEC.crankNicolson_signed`).

## Three-block systems of the Einstein–Bianchi scheme (thesis Ch. 7)

With block mass matrix `M = diag(M₀, M₁, M₂)` (`blockMass`) and stiffness
`K = [[0, -Gᵀ, 0], [G, 0, Cᵀ], [0, -C, 0]]` (`blockStiffness`) on `n₀ ⊕ n₁ ⊕ n₂`:

* `isUnit_blockMass_add_smul`: `M + sK` is invertible for SPD blocks and every `s`;
  `dotProduct_mulVec_eq_of_cn`: the CN map conserves the `M`-energy.
* **`not_isSymm_blockMass_add_smul`**: `M + sK` is not symmetric for `s ≠ 0` and nonzero
  coupling, so MINRES does not apply to it directly.
* **`isSymm_isUnit_indefinite_blockSign_mul`**: `J (M + sK)`, `J = diag(-I, I, -I)`, is
  symmetric, nonsingular and indefinite; **`existsUnique_blockSign_mul_mulVec`**: its system has
  the CN update as unique solution.
* Block elimination: **`blockMass_add_smul_mulVec_eq_iff_schur`** and
  **`posDef_schurComplement`**: the `E` Schur complement `M₁ + s²(G M₀⁻¹ Gᵀ + Cᵀ M₂⁻¹ C)` is SPD.
* Assembly in bases (`testMatrix`, `blockCoord`): `isFullCNStep_iff_mulVec`, and
  **`blockSign_mul_mulVec_iff_fullCNStep`**: the symmetrized system computes exactly the CN
  iterate of `Feec.TimeStepping.fullCNStep`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7 (MINRES for the Crank–Nicolson systems)
* [C. C. Paige, M. A. Saunders, *Solution of sparse indefinite systems of linear equations*][PaigeSaunders1975]
  (MINRES for symmetric indefinite systems)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Matrix

@[expose] public noncomputable section

namespace Feec.TimeStepping

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- **Signed symmetrization**: if `M` is symmetric and couples only unknowns with equal signs,
and `K` is skew and couples only unknowns with opposite signs, then `diag(ε) (M + s K)` is
symmetric. [QuennevilleBelair2015], Ch. 7 -/
theorem isSymm_diagonal_mul_add_smul (ε : n → R) {M K : Matrix n n R} (hM : M.IsSymm)
    (hK : Kᵀ = -K) (hMε : ∀ i j, M i j ≠ 0 → ε i = ε j) (hKε : ∀ i j, K i j ≠ 0 → ε i = -ε j)
    (s : R) : (diagonal ε * (M + s • K)).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [diagonal_mul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
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
`ε i² = 1`. [QuennevilleBelair2015], Ch. 7 -/
theorem mulVec_diagonal_mul_iff (ε : n → R) (hε : ∀ i, ε i * ε i = 1) (A : Matrix n n R)
    (x b : n → R) : (diagonal ε * A) *ᵥ x = diagonal ε *ᵥ b ↔ A *ᵥ x = b := by
  have hεε : diagonal ε * diagonal ε = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; exact congrArg diagonal (funext hε)
  constructor
  · intro h
    have := congrArg (diagonal ε *ᵥ ·) h
    simpa [mulVec_mulVec, ← Matrix.mul_assoc, hεε] using this
  · intro h; rw [← mulVec_mulVec, h]

/-- **Signed Hermitian symmetrization**: if `M` is Hermitian and couples only unknowns with equal
signs, `K` is skew-Hermitian and couples only unknowns with opposite signs, and the signs and `s`
are self-adjoint, then `diag(ε) (M + s K)` is Hermitian (the complex form of
`isSymm_diagonal_mul_add_smul`). [QuennevilleBelair2015], Ch. 7 -/
theorem isHermitian_diagonal_mul_add_smul [StarRing R] (ε : n → R) {M K : Matrix n n R}
    (hM : M.IsHermitian) (hK : Kᴴ = -K) (hε : ∀ i, star (ε i) = ε i)
    (hMε : ∀ i j, M i j ≠ 0 → ε i = ε j) (hKε : ∀ i j, K i j ≠ 0 → ε i = -ε j) {s : R}
    (hs : star s = s) : (diagonal ε * (M + s • K)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [diagonal_mul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul',
    star_add, hε, hs, hM.apply]
  have hKji : star (K j i) = -K i j := by simpa using congrFun (congrFun hK i) j
  rw [hKji]
  have e1 : ε j * M i j = ε i * M i j := by
    by_cases h : M i j = 0
    · rw [h, mul_zero, mul_zero]
    · rw [hMε i j h]
  have e2 : ε j * (s * -K i j) = ε i * (s * K i j) := by
    by_cases h : K i j = 0
    · simp [h]
    · rw [hKε i j h]; ring
  linear_combination e1 + e2

/-! ### Crank–Nicolson for a bounded generator in a basis -/

section Generator

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

omit [DecidableEq n] in
/-- Expansion of `⟪w, y⟫` in the coordinates of `y`. -/
theorem inner_eq_sum_repr (b : Module.Basis n 𝕜 E) (w y : E) :
    ⟪w, y⟫_𝕜 = ∑ j, b.repr y j * ⟪w, b j⟫_𝕜 := by
  conv_lhs => rw [← b.sum_repr y]
  rw [inner_sum]
  simp [inner_smul_right]

omit [DecidableEq n] in
/-- Testing against a basis determines a vector. -/
theorem eq_of_inner_basis (b : Module.Basis n 𝕜 E) {y y' : E}
    (h : ∀ i, ⟪b i, y⟫_𝕜 = ⟪b i, y'⟫_𝕜) : y = y' := by
  refine ext_inner_left 𝕜 fun w => ?_
  rw [← b.sum_repr w, sum_inner, sum_inner]
  simp [inner_smul_left, h]

/-- The **stiffness matrix** `K i j = -⟪bᵢ, T bⱼ⟫` of `T` in the basis `b`: tested against `b`,
`u' = T u` reads `M c' = -K c` with the Gram (mass) matrix `M` and the coefficients `c` of `u`. -/
def stiffness (b : Module.Basis n 𝕜 E) (T : E →ₗ[𝕜] E) : Matrix n n 𝕜 :=
  Matrix.of fun i j => -⟪b i, T (b j)⟫_𝕜

omit [DecidableEq n] in
/-- Testing in coordinates: `(⟪bᵢ, y⟫)ᵢ = M c(y)`. -/
theorem inner_basis_eq_gram_mulVec (b : Module.Basis n 𝕜 E) (y : E) :
    (fun i => ⟪b i, y⟫_𝕜) = Matrix.gram 𝕜 b *ᵥ b.equivFun y := by
  funext i
  rw [inner_eq_sum_repr b]
  simp [mulVec, dotProduct, Matrix.gram_apply, mul_comm]

omit [DecidableEq n] in
/-- Testing `T y` in coordinates: `(⟪bᵢ, T y⟫)ᵢ = -K c(y)`. -/
theorem inner_basis_apply_eq_neg_stiffness_mulVec (b : Module.Basis n 𝕜 E) (T : E →ₗ[𝕜] E)
    (y : E) : (fun i => ⟪b i, T y⟫_𝕜) = -(stiffness b T *ᵥ b.equivFun y) := by
  funext i
  have e : ⟪b i, T y⟫_𝕜 = ∑ j, b.repr y j * ⟪b i, T (b j)⟫_𝕜 := by
    conv_lhs => rw [← b.sum_repr y, map_sum, inner_sum]
    simp only [map_smul, inner_smul_right]
  simp [e, mulVec, dotProduct, stiffness, mul_comm]

omit [DecidableEq n] in
/-- **A Crank–Nicolson step is the assembled system**: `u'` is a CN step from `u` with half step
`s` for `u' = T u` iff `(M + sK) c(u') = (M - sK) c(u)` (Gram matrix `M`, stiffness `K`).
[QuennevilleBelair2015], Ch. 7 -/
theorem isCNStep_iff_mulVec (b : Module.Basis n 𝕜 E) (T : E →ₗ[𝕜] E) (s : ℝ) (u u' : E) :
    IsCNStep (T.toPMap ⊤) s u u' ↔
      (Matrix.gram 𝕜 b + (s : 𝕜) • stiffness b T) *ᵥ b.equivFun u' =
        (Matrix.gram 𝕜 b - (s : 𝕜) • stiffness b T) *ᵥ b.equivFun u := by
  have hC : IsCNStep (T.toPMap ⊤) s u u' ↔ u' - (s : 𝕜) • T u' = u + (s : 𝕜) • T u := by
    refine ⟨fun ⟨_, e⟩ => ?_, fun e => ⟨Submodule.mem_top, ?_⟩⟩
    · change u' - u = (s : 𝕜) • T (u' + u) at e
      rw [map_add] at e
      linear_combination (norm := module) e
    · change u' - u = (s : 𝕜) • T (u' + u)
      rw [map_add]
      linear_combination (norm := module) e
  have hK : ∀ y, stiffness b T *ᵥ b.equivFun y = -fun i => ⟪b i, T y⟫_𝕜 := fun y => by
    rw [inner_basis_apply_eq_neg_stiffness_mulVec, neg_neg]
  rw [hC, add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, ← inner_basis_eq_gram_mulVec,
    ← inner_basis_eq_gram_mulVec, hK, hK]
  refine ⟨fun e => funext fun i => ?_, fun e => eq_of_inner_basis b fun i => ?_⟩
  · have := congrArg (⟪b i, ·⟫_𝕜) e
    simp only [inner_sub_right, inner_add_right, inner_smul_right] at this
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination this
  · have := congrFun e i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at this
    simp only [inner_sub_right, inner_add_right, inner_smul_right]
    linear_combination this

omit [Fintype n] [DecidableEq n] in
/-- `K` is skew-Hermitian for a skew `T`. -/
theorem conjTranspose_stiffness (b : Module.Basis n 𝕜 E) {T : E →ₗ[𝕜] E}
    (hT : ∀ x y, ⟪T x, y⟫_𝕜 = -⟪x, T y⟫_𝕜) : (stiffness b T)ᴴ = -stiffness b T := by
  ext i j
  simp only [conjTranspose_apply, stiffness, Matrix.of_apply, Matrix.neg_apply, star_neg,
    neg_neg, ← inner_conj_symm (b j), RCLike.star_def, RingHomCompTriple.comp_apply,
    RingHom.id_apply, hT]

/-- **The signed Crank–Nicolson system is Hermitian** for a skew `T` and real signs `ε i = ±1`
such that the basis functions with different signs are orthogonal and `T` couples only basis
functions with opposite signs (a basis adapted to a grading by the parity of the degree):
`diag(ε) (M + sK)` is Hermitian, so MINRES applies to it. [QuennevilleBelair2015], Ch. 7;
[PaigeSaunders1975] -/
theorem isHermitian_signed_cn (b : Module.Basis n 𝕜 E) {T : E →ₗ[𝕜] E}
    (hT : ∀ x y, ⟪T x, y⟫_𝕜 = -⟪x, T y⟫_𝕜) (ε : n → ℝ)
    (hMε : ∀ i j, ⟪b i, b j⟫_𝕜 ≠ 0 → ε i = ε j) (hKε : ∀ i j, ⟪b i, T (b j)⟫_𝕜 ≠ 0 → ε i = -ε j)
    (s : ℝ) :
    (diagonal (fun i => (ε i : 𝕜)) * (Matrix.gram 𝕜 b + (s : 𝕜) • stiffness b T)).IsHermitian :=
  isHermitian_diagonal_mul_add_smul _ (Matrix.isHermitian_gram 𝕜 b) (conjTranspose_stiffness b hT)
    (fun _ => RCLike.conj_ofReal _) (fun i j hij => by rw [hMε i j hij])
    (fun i j hij => by rw [hKε i j (by simpa [stiffness] using hij), RCLike.ofReal_neg])
    (RCLike.conj_ofReal s)

/-- **The signed system has the CN steps as solutions**: for signs with `ε i² = 1`, `w` solves
`diag(ε) (M + sK) w = diag(ε) (M - sK) c(u)` iff `b.equivFun.symm w` is a CN step from `u`.
[QuennevilleBelair2015], Ch. 7 -/
theorem diagonal_mul_mulVec_iff_isCNStep (b : Module.Basis n 𝕜 E)
    (T : E →ₗ[𝕜] E) (s : ℝ) (ε : n → 𝕜) (hε : ∀ i, ε i * ε i = 1) (u : E) (w : n → 𝕜) :
    (diagonal ε * (Matrix.gram 𝕜 b + (s : 𝕜) • stiffness b T)) *ᵥ w =
        (diagonal ε * (Matrix.gram 𝕜 b - (s : 𝕜) • stiffness b T)) *ᵥ b.equivFun u ↔
      IsCNStep (T.toPMap ⊤) s u (b.equivFun.symm w) := by
  rw [← mulVec_mulVec (b.equivFun u) (diagonal ε), mulVec_diagonal_mul_iff ε hε,
    isCNStep_iff_mulVec b, LinearEquiv.apply_symm_apply]

end Generator

/-! ### Three-block Crank–Nicolson matrices (thesis Ch. 7) -/

section ThreeBlock

variable {n₀ n₁ n₂ : Type*} [Fintype n₀] [Fintype n₁] [Fintype n₂]
  [DecidableEq n₀] [DecidableEq n₁] [DecidableEq n₂]

/-- Index type of the coefficient vector `(σ, E, B)`. -/
abbrev BlockIdx (n₀ n₁ n₂ : Type*) := n₀ ⊕ (n₁ ⊕ n₂)

/-- Block-diagonal mass matrix `M = diag(M₀, M₁, M₂)`. -/
def blockMass (M₀ : Matrix n₀ n₀ ℝ) (M₁ : Matrix n₁ n₁ ℝ) (M₂ : Matrix n₂ n₂ ℝ) :
    Matrix (BlockIdx n₀ n₁ n₂) (BlockIdx n₀ n₁ n₂) ℝ :=
  Matrix.of fun i j =>
    match i, j with
    | .inl i, .inl j => M₀ i j
    | .inr (.inl i), .inr (.inl j) => M₁ i j
    | .inr (.inr i), .inr (.inr j) => M₂ i j
    | _, _ => 0

/-- Stiffness matrix `K = [[0, -Gᵀ, 0], [G, 0, Cᵀ], [0, -C, 0]]` of `M ẋ = -K x` (`G` the
discrete gradient, `C` the discrete curl; (4.14) in coordinates). -/
def blockStiffness (G : Matrix n₁ n₀ ℝ) (C : Matrix n₂ n₁ ℝ) :
    Matrix (BlockIdx n₀ n₁ n₂) (BlockIdx n₀ n₁ n₂) ℝ :=
  Matrix.of fun i j =>
    match i, j with
    | .inl i, .inr (.inl j) => -G j i
    | .inr (.inl i), .inl j => G i j
    | .inr (.inl i), .inr (.inr j) => C j i
    | .inr (.inr i), .inr (.inl j) => -C i j
    | _, _ => 0

/-- The signs `-1, 1, -1` of the three blocks. -/
def blockSigns : BlockIdx n₀ n₁ n₂ → ℝ
  | .inl _ => -1
  | .inr (.inl _) => 1
  | .inr (.inr _) => -1

/-- Sign matrix `J = diag(-I, I, -I)`. -/
def blockSign : Matrix (BlockIdx n₀ n₁ n₂) (BlockIdx n₀ n₁ n₂) ℝ := diagonal blockSigns

omit [Fintype n₀] [Fintype n₁] [Fintype n₂] [DecidableEq n₀] [DecidableEq n₁]
  [DecidableEq n₂] in
/-- `K` is skew-symmetric. -/
theorem transpose_blockStiffness (G : Matrix n₁ n₀ ℝ) (C : Matrix n₂ n₁ ℝ) :
    (blockStiffness (n₀ := n₀) G C)ᵀ = -blockStiffness G C := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;> simp [blockStiffness]

omit [Fintype n₀] [Fintype n₁] [Fintype n₂] [DecidableEq n₀] [DecidableEq n₁]
  [DecidableEq n₂] in
/-- The block mass matrix is symmetric. -/
theorem isSymm_blockMass {M₀ : Matrix n₀ n₀ ℝ} {M₁ : Matrix n₁ n₁ ℝ} {M₂ : Matrix n₂ n₂ ℝ}
    (h₀ : M₀.IsSymm) (h₁ : M₁.IsSymm) (h₂ : M₂.IsSymm) : (blockMass M₀ M₁ M₂).IsSymm := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [blockMass, h₀.apply, h₁.apply, h₂.apply]

omit [Fintype n₀] [Fintype n₁] [Fintype n₂] [DecidableEq n₀] [DecidableEq n₁]
  [DecidableEq n₂] in
theorem blockSigns_mul_self (i : BlockIdx n₀ n₁ n₂) : blockSigns i * blockSigns i = 1 := by
  rcases i with i | i | i <;> norm_num [blockSigns]

/-- `J² = I`. -/
theorem blockSign_mul_self :
    (blockSign : Matrix (BlockIdx n₀ n₁ n₂) (BlockIdx n₀ n₁ n₂) ℝ) * blockSign = 1 := by
  rw [blockSign, diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext blockSigns_mul_self)

/-- **`J (M + sK)` is symmetric** (an instance of `isSymm_diagonal_mul_add_smul`: `M` couples
equal signs, `K` opposite signs). See [QuennevilleBelair2015], Ch. 7. -/
theorem isSymm_blockSign_mul {M₀ : Matrix n₀ n₀ ℝ} {M₁ : Matrix n₁ n₁ ℝ} {M₂ : Matrix n₂ n₂ ℝ}
    (h₀ : M₀.IsSymm) (h₁ : M₁.IsSymm) (h₂ : M₂.IsSymm) (G : Matrix n₁ n₀ ℝ)
    (C : Matrix n₂ n₁ ℝ) (s : ℝ) :
    (blockSign * (blockMass M₀ M₁ M₂ + s • blockStiffness G C)).IsSymm :=
  isSymm_diagonal_mul_add_smul _ (isSymm_blockMass h₀ h₁ h₂) (transpose_blockStiffness G C)
    (fun i j hij => by
      rcases i with i | i | i <;> rcases j with j | j | j <;> simp_all [blockMass, blockSigns])
    (fun i j hij => by
      rcases i with i | i | i <;> rcases j with j | j | j <;>
        simp_all [blockStiffness, blockSigns]) s

/-- The `J`-signed system has the solutions of the unsigned one (`J² = I`). -/
theorem blockSign_mulVec_iff (A : Matrix (BlockIdx n₀ n₁ n₂) (BlockIdx n₀ n₁ n₂) ℝ)
    (x b : BlockIdx n₀ n₁ n₂ → ℝ) : (blockSign * A) *ᵥ x = blockSign *ᵥ b ↔ A *ᵥ x = b :=
  mulVec_diagonal_mul_iff _ blockSigns_mul_self A x b

omit [DecidableEq n₀] [DecidableEq n₁] [DecidableEq n₂] in
/-- `xᵀ K x = 0` for skew `K`. -/
theorem dotProduct_mulVec_self_eq_zero {ι : Type*} [Fintype ι] {K : Matrix ι ι ℝ}
    (hK : Kᵀ = -K) (x : ι → ℝ) : x ⬝ᵥ (K *ᵥ x) = 0 := by
  have h : x ⬝ᵥ (K *ᵥ x) = -(x ⬝ᵥ (K *ᵥ x)) := by
    calc x ⬝ᵥ (K *ᵥ x) = (Kᵀ *ᵥ x) ⬝ᵥ x := by rw [dotProduct_mulVec, mulVec_transpose]
      _ = -(x ⬝ᵥ (K *ᵥ x)) := by rw [hK, neg_mulVec, neg_dotProduct, dotProduct_comm]
  linarith

omit [DecidableEq n₀] [DecidableEq n₁] [DecidableEq n₂] in
/-- **The CN matrix `M + sK` is invertible** for SPD `M`, skew `K` and every real `s`: if
`(M + sK) x = 0` then `xᵀ M x = 0`. See [QuennevilleBelair2015], Ch. 7. -/
theorem det_add_smul_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {M K : Matrix ι ι ℝ}
    (hM : M.PosDef) (hK : Kᵀ = -K) (s : ℝ) : (M + s • K).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := (exists_mulVec_eq_zero_iff (M := M + s • K)).2 hdet
  have hpos := hM.dotProduct_mulVec_pos hv
  rw [star_trivial] at hpos
  have : v ⬝ᵥ ((M + s • K) *ᵥ v) = v ⬝ᵥ (M *ᵥ v) := by
    rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul,
      dotProduct_mulVec_self_eq_zero hK, smul_zero, add_zero]
  rw [hMv, dotProduct_zero] at this
  linarith

omit [DecidableEq n₀] [DecidableEq n₁] [DecidableEq n₂] in
/-- **Energy conservation of the matrix CN step**: `(M + sK) x' = (M - sK) x` with `M`
symmetric and `K` skew gives `x'ᵀ M x' = xᵀ M x`. See [QuennevilleBelair2015], Ch. 7. -/
theorem dotProduct_mulVec_eq_of_cn {ι : Type*} [Fintype ι] {M K : Matrix ι ι ℝ} (hM : M.IsSymm)
    (hK : Kᵀ = -K) (s : ℝ) (x x' : ι → ℝ) (h : (M + s • K) *ᵥ x' = (M - s • K) *ᵥ x) :
    x' ⬝ᵥ (M *ᵥ x') = x ⬝ᵥ (M *ᵥ x) := by
  have h' : M *ᵥ (x' - x) = -(s • (K *ᵥ (x' + x))) := by
    rw [add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec] at h
    rw [mulVec_sub, mulVec_add, smul_add]
    linear_combination (exp := 1) h
  have hsymm : ∀ u w : ι → ℝ, u ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (M *ᵥ u) := fun u w => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hM.eq, dotProduct_comm]
  have key : (x' + x) ⬝ᵥ (M *ᵥ (x' - x)) = 0 := by
    rw [h', dotProduct_neg, dotProduct_smul, dotProduct_mulVec_self_eq_zero hK, smul_zero,
      neg_zero]
  rw [mulVec_sub, dotProduct_sub, add_dotProduct, add_dotProduct, hsymm x x'] at key
  linarith

omit [DecidableEq n₀] [DecidableEq n₁] [DecidableEq n₂] in
/-- The block mass matrix is SPD when its blocks are. -/
theorem posDef_blockMass {M₀ : Matrix n₀ n₀ ℝ} {M₁ : Matrix n₁ n₁ ℝ} {M₂ : Matrix n₂ n₂ ℝ}
    (h₀ : M₀.PosDef) (h₁ : M₁.PosDef) (h₂ : M₂.PosDef) : (blockMass M₀ M₁ M₂).PosDef := by
  have hq : ∀ x : BlockIdx n₀ n₁ n₂ → ℝ, x ⬝ᵥ (blockMass M₀ M₁ M₂ *ᵥ x) =
      (fun i => x (.inl i)) ⬝ᵥ (M₀ *ᵥ fun i => x (.inl i)) +
      ((fun i => x (.inr (.inl i))) ⬝ᵥ (M₁ *ᵥ fun i => x (.inr (.inl i))) +
      (fun i => x (.inr (.inr i))) ⬝ᵥ (M₂ *ᵥ fun i => x (.inr (.inr i)))) := by
    intro x
    simp [dotProduct, mulVec, Fintype.sum_sum_type, blockMass]
  have hsymm : (blockMass M₀ M₁ M₂).IsHermitian :=
    isSymm_blockMass h₀.isHermitian.eq h₁.isHermitian.eq h₂.isHermitian.eq
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hsymm fun x hx => ?_
  rw [star_trivial, hq]
  have p0 := h₀.posSemidef.dotProduct_mulVec_nonneg (fun i => x (.inl i))
  have p1 := h₁.posSemidef.dotProduct_mulVec_nonneg (fun i => x (.inr (.inl i)))
  have p2 := h₂.posSemidef.dotProduct_mulVec_nonneg (fun i => x (.inr (.inr i)))
  simp only [star_trivial] at p0 p1 p2
  by_cases e0 : (fun i => x (.inl i)) = 0
  · by_cases e1 : (fun i => x (.inr (.inl i))) = 0
    · have e2 : (fun i => x (.inr (.inr i))) ≠ 0 := by
        intro e2; apply hx; ext i
        rcases i with i | i | i
        · exact congrFun e0 i
        · exact congrFun e1 i
        · exact congrFun e2 i
      have := h₂.dotProduct_mulVec_pos e2
      rw [star_trivial] at this
      linarith
    · have := h₁.dotProduct_mulVec_pos e1
      rw [star_trivial] at this
      linarith
  · have := h₀.dotProduct_mulVec_pos e0
    rw [star_trivial] at this
    linarith

/-- **The CN matrix of the full system is invertible** for SPD mass blocks and every `s`.
See [QuennevilleBelair2015], (4.14), Ch. 7. -/
theorem isUnit_blockMass_add_smul {M₀ : Matrix n₀ n₀ ℝ} {M₁ : Matrix n₁ n₁ ℝ}
    {M₂ : Matrix n₂ n₂ ℝ} (h₀ : M₀.PosDef) (h₁ : M₁.PosDef) (h₂ : M₂.PosDef)
    (G : Matrix n₁ n₀ ℝ) (C : Matrix n₂ n₁ ℝ) (s : ℝ) :
    IsUnit (blockMass M₀ M₁ M₂ + s • blockStiffness G C) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact det_add_smul_ne_zero (posDef_blockMass h₀ h₁ h₂) (transpose_blockStiffness G C) s

omit [Fintype n₀] [Fintype n₁] [Fintype n₂] [DecidableEq n₀] [DecidableEq n₁]
  [DecidableEq n₂] in
/-- `(M + sK)ᵀ = M - sK` for symmetric mass blocks. -/
theorem transpose_blockMass_add_smul {M₀ : Matrix n₀ n₀ ℝ} {M₁ : Matrix n₁ n₁ ℝ}
    {M₂ : Matrix n₂ n₂ ℝ} (h₀ : M₀.IsSymm) (h₁ : M₁.IsSymm) (h₂ : M₂.IsSymm)
    (G : Matrix n₁ n₀ ℝ) (C : Matrix n₂ n₁ ℝ) (s : ℝ) :
    (blockMass M₀ M₁ M₂ + s • blockStiffness G C)ᵀ =
      blockMass M₀ M₁ M₂ - s • blockStiffness G C := by
  rw [transpose_add, transpose_smul, transpose_blockStiffness, (isSymm_blockMass h₀ h₁ h₂).eq,
    smul_neg, sub_eq_add_neg]

omit [Fintype n₀] [Fintype n₁] [Fintype n₂] [DecidableEq n₀] [DecidableEq n₁]
  [DecidableEq n₂] in
theorem blockStiffness_eq_zero_iff (G : Matrix n₁ n₀ ℝ) (C : Matrix n₂ n₁ ℝ) :
    blockStiffness G C = 0 ↔ G = 0 ∧ C = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext i j; simpa [blockStiffness] using congrFun (congrFun h (.inr (.inl i))) (.inl j)
    · ext i j; simpa [blockStiffness] using congrFun (congrFun h (.inr (.inr i))) (.inr (.inl j))
  · rintro ⟨rfl, rfl⟩
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;> simp [blockStiffness]

omit [Fintype n₀] [Fintype n₁] [Fintype n₂] [DecidableEq n₀] [DecidableEq n₁]
  [DecidableEq n₂] in
/-- **The CN matrix is not symmetric** for `s ≠ 0` and nonzero coupling, so MINRES does not apply
to the unsymmetrized CN system (the monolithic reading of the thesis' solver claim).
See [QuennevilleBelair2015], Ch. 7 (l. 4284–4285). -/
theorem not_isSymm_blockMass_add_smul {M₀ : Matrix n₀ n₀ ℝ} {M₁ : Matrix n₁ n₁ ℝ}
    {M₂ : Matrix n₂ n₂ ℝ} (h₀ : M₀.IsSymm) (h₁ : M₁.IsSymm) (h₂ : M₂.IsSymm)
    {G : Matrix n₁ n₀ ℝ} {C : Matrix n₂ n₁ ℝ} {s : ℝ} (hs : s ≠ 0) (hGC : G ≠ 0 ∨ C ≠ 0) :
    ¬ (blockMass M₀ M₁ M₂ + s • blockStiffness G C).IsSymm := by
  intro h
  have he : blockMass M₀ M₁ M₂ + s • blockStiffness G C =
      blockMass M₀ M₁ M₂ - s • blockStiffness G C := by
    rw [← transpose_blockMass_add_smul h₀ h₁ h₂ G C s, h.eq]
  have hn : s • blockStiffness G C = -(s • blockStiffness G C) := by
    rw [sub_eq_add_neg] at he; exact add_left_cancel he
  have h2 : (2 : ℝ) • (s • blockStiffness G C) = 0 := by
    rw [two_smul]; nth_rewrite 2 [hn]; exact add_neg_cancel _
  have hK0 : blockStiffness G C = 0 :=
    (smul_eq_zero.mp ((smul_eq_zero.mp h2).resolve_left two_ne_zero)).resolve_left hs
  obtain ⟨rfl, rfl⟩ := (blockStiffness_eq_zero_iff G C).mp hK0
  simp at hGC

theorem isUnit_blockSign :
    IsUnit (blockSign : Matrix (BlockIdx n₀ n₁ n₂) (BlockIdx n₀ n₁ n₂) ℝ) :=
  ⟨⟨blockSign, blockSign, blockSign_mul_self, blockSign_mul_self⟩, rfl⟩

/-- `J (M + sK)` is nonsingular for SPD mass blocks and every `s`. -/
theorem isUnit_blockSign_mul {M₀ : Matrix n₀ n₀ ℝ} {M₁ : Matrix n₁ n₁ ℝ} {M₂ : Matrix n₂ n₂ ℝ}
    (h₀ : M₀.PosDef) (h₁ : M₁.PosDef) (h₂ : M₂.PosDef) (G : Matrix n₁ n₀ ℝ)
    (C : Matrix n₂ n₁ ℝ) (s : ℝ) :
    IsUnit (blockSign * (blockMass M₀ M₁ M₂ + s • blockStiffness G C)) :=
  isUnit_blockSign.mul (isUnit_blockMass_add_smul h₀ h₁ h₂ G C s)

/-- The diagonal of `J (M + sK)`: `-M₀`, `M₁`, `-M₂`. -/
theorem blockSign_mul_diag (M₀ : Matrix n₀ n₀ ℝ) (M₁ : Matrix n₁ n₁ ℝ) (M₂ : Matrix n₂ n₂ ℝ)
    (G : Matrix n₁ n₀ ℝ) (C : Matrix n₂ n₁ ℝ) (s : ℝ) :
    (∀ i, (blockSign * (blockMass M₀ M₁ M₂ + s • blockStiffness G C) :
      Matrix (BlockIdx n₀ n₁ n₂) (BlockIdx n₀ n₁ n₂) ℝ) (.inl i) (.inl i) = -M₀ i i) ∧
    (∀ i, (blockSign * (blockMass M₀ M₁ M₂ + s • blockStiffness G C) :
      Matrix (BlockIdx n₀ n₁ n₂) (BlockIdx n₀ n₁ n₂) ℝ) (.inr (.inl i)) (.inr (.inl i)) =
        M₁ i i) ∧
    (∀ i, (blockSign * (blockMass M₀ M₁ M₂ + s • blockStiffness G C) :
      Matrix (BlockIdx n₀ n₁ n₂) (BlockIdx n₀ n₁ n₂) ℝ) (.inr (.inr i)) (.inr (.inr i)) =
        -M₂ i i) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
    simp [blockSign, blockSigns, blockMass, blockStiffness, diagonal_mul]

/-- The symmetrized CN system is equivalent to the CN system. -/
theorem blockSign_mul_mulVec_iff (M₀ : Matrix n₀ n₀ ℝ) (M₁ : Matrix n₁ n₁ ℝ)
    (M₂ : Matrix n₂ n₂ ℝ) (G : Matrix n₁ n₀ ℝ) (C : Matrix n₂ n₁ ℝ) (s : ℝ)
    (x x' : BlockIdx n₀ n₁ n₂ → ℝ) :
    (blockSign * (blockMass M₀ M₁ M₂ + s • blockStiffness G C)) *ᵥ x' =
        (blockSign * (blockMass M₀ M₁ M₂ - s • blockStiffness G C)) *ᵥ x ↔
      (blockMass M₀ M₁ M₂ + s • blockStiffness G C) *ᵥ x' =
        (blockMass M₀ M₁ M₂ - s • blockStiffness G C) *ᵥ x := by
  rw [← mulVec_mulVec x blockSign (blockMass M₀ M₁ M₂ - s • blockStiffness G C)]
  exact blockSign_mulVec_iff _ _ _

/-- **Unique solvability of the symmetrized CN system** (SPD mass blocks, every `s`): its unique
solution is the CN update `(M + sK)⁻¹ (M - sK) x`. See [QuennevilleBelair2015], Ch. 7. -/
theorem existsUnique_blockSign_mul_mulVec {M₀ : Matrix n₀ n₀ ℝ} {M₁ : Matrix n₁ n₁ ℝ}
    {M₂ : Matrix n₂ n₂ ℝ} (h₀ : M₀.PosDef) (h₁ : M₁.PosDef) (h₂ : M₂.PosDef)
    (G : Matrix n₁ n₀ ℝ) (C : Matrix n₂ n₁ ℝ) (s : ℝ) (x : BlockIdx n₀ n₁ n₂ → ℝ) :
    ∃! x', (blockSign * (blockMass M₀ M₁ M₂ + s • blockStiffness G C)) *ᵥ x' =
      (blockSign * (blockMass M₀ M₁ M₂ - s • blockStiffness G C)) *ᵥ x := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_blockMass_add_smul h₀ h₁ h₂ G C s)
  refine ⟨(blockMass M₀ M₁ M₂ + s • blockStiffness G C)⁻¹ *ᵥ
    ((blockMass M₀ M₁ M₂ - s • blockStiffness G C) *ᵥ x), ?_, fun y hy => ?_⟩
  · beta_reduce
    rw [blockSign_mul_mulVec_iff, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  · beta_reduce at hy
    rw [blockSign_mul_mulVec_iff] at hy
    rw [← hy, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]

/-- **The symmetrized CN matrix is symmetric, nonsingular and indefinite** (SPD blocks, every
`s`, nonempty `E` block and nonempty `σ` or `B` block): the matrix properties for which MINRES,
and not CG, is the Krylov method. Repair of the thesis' solver claim under the monolithic
reading. See [QuennevilleBelair2015], Ch. 7 (l. 4284–4285). -/
theorem isSymm_isUnit_indefinite_blockSign_mul {M₀ : Matrix n₀ n₀ ℝ} {M₁ : Matrix n₁ n₁ ℝ}
    {M₂ : Matrix n₂ n₂ ℝ} (h₀ : M₀.PosDef) (h₁ : M₁.PosDef) (h₂ : M₂.PosDef)
    (G : Matrix n₁ n₀ ℝ) (C : Matrix n₂ n₁ ℝ) (s : ℝ) [Nonempty n₁]
    (hn : Nonempty n₀ ∨ Nonempty n₂) :
    (blockSign * (blockMass M₀ M₁ M₂ + s • blockStiffness G C)).IsSymm ∧
      IsUnit (blockSign * (blockMass M₀ M₁ M₂ + s • blockStiffness G C)) ∧
      (∃ v, v ⬝ᵥ ((blockSign * (blockMass M₀ M₁ M₂ + s • blockStiffness G C)) *ᵥ v) < 0) ∧
      ∃ w, 0 < w ⬝ᵥ ((blockSign * (blockMass M₀ M₁ M₂ + s • blockStiffness G C)) *ᵥ w) := by
  have hd : ∀ (A : Matrix (BlockIdx n₀ n₁ n₂) (BlockIdx n₀ n₁ n₂) ℝ) k,
      Pi.single k 1 ⬝ᵥ (A *ᵥ Pi.single k 1) = A k k := fun A k => by
    simp
  obtain ⟨d0, d1, d2⟩ := blockSign_mul_diag M₀ M₁ M₂ G C s
  refine ⟨isSymm_blockSign_mul h₀.isHermitian.eq h₁.isHermitian.eq h₂.isHermitian.eq G C s,
    isUnit_blockSign_mul h₀ h₁ h₂ G C s, ?_, ?_⟩
  · rcases hn with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
    · exact ⟨Pi.single (.inl i) 1, by rw [hd, d0]; linarith [h₀.diag_pos (i := i)]⟩
    · exact ⟨Pi.single (.inr (.inr i)) 1, by rw [hd, d2]; linarith [h₂.diag_pos (i := i)]⟩
  · obtain ⟨i⟩ := ‹Nonempty n₁›
    exact ⟨Pi.single (.inr (.inl i)) 1, by rw [hd, d1]; exact h₁.diag_pos⟩

/-! #### Block elimination (Schur complement) -/

/-- The `σ` block of a vector on `BlockIdx n₀ n₁ n₂`. -/
def block₀ (x : BlockIdx n₀ n₁ n₂ → ℝ) : n₀ → ℝ := fun i => x (.inl i)

/-- The `E` block. -/
def block₁ (x : BlockIdx n₀ n₁ n₂ → ℝ) : n₁ → ℝ := fun i => x (.inr (.inl i))

/-- The `B` block. -/
def block₂ (x : BlockIdx n₀ n₁ n₂ → ℝ) : n₂ → ℝ := fun i => x (.inr (.inr i))

/-- The `E` Schur complement `S = M₁ + s²(G M₀⁻¹ Gᵀ + Cᵀ M₂⁻¹ C)` of the CN matrix. -/
def schurComplement (M₀ : Matrix n₀ n₀ ℝ) (M₁ : Matrix n₁ n₁ ℝ) (M₂ : Matrix n₂ n₂ ℝ)
    (G : Matrix n₁ n₀ ℝ) (C : Matrix n₂ n₁ ℝ) (s : ℝ) : Matrix n₁ n₁ ℝ :=
  M₁ + s ^ 2 • (G * M₀⁻¹ * Gᵀ + Cᵀ * M₂⁻¹ * C)

omit [DecidableEq n₀] [DecidableEq n₁] [DecidableEq n₂] in
/-- Block rows of `(M + sK) x`: `M₀ σ - s Gᵀ E`, `M₁ E + s G σ + s Cᵀ B`, `M₂ B - s C E`. -/
theorem blockMass_add_smul_mulVec_eq_iff (M₀ : Matrix n₀ n₀ ℝ) (M₁ : Matrix n₁ n₁ ℝ)
    (M₂ : Matrix n₂ n₂ ℝ) (G : Matrix n₁ n₀ ℝ) (C : Matrix n₂ n₁ ℝ) (s : ℝ)
    (x r : BlockIdx n₀ n₁ n₂ → ℝ) :
    (blockMass M₀ M₁ M₂ + s • blockStiffness G C) *ᵥ x = r ↔
      M₀ *ᵥ block₀ x - s • (Gᵀ *ᵥ block₁ x) = block₀ r ∧
      M₁ *ᵥ block₁ x + s • (G *ᵥ block₀ x) + s • (Cᵀ *ᵥ block₂ x) = block₁ r ∧
      M₂ *ᵥ block₂ x - s • (C *ᵥ block₁ x) = block₂ r := by
  have e0 : ∀ i, ((blockMass M₀ M₁ M₂ + s • blockStiffness G C) *ᵥ x) (.inl i) =
      (M₀ *ᵥ block₀ x - s • (Gᵀ *ᵥ block₁ x)) i := fun i => by
    simp [mulVec, dotProduct, Fintype.sum_sum_type, blockMass, blockStiffness, block₀, block₁,
      Finset.mul_sum, sub_eq_add_neg, mul_assoc, mul_comm]
  have e1 : ∀ i, ((blockMass M₀ M₁ M₂ + s • blockStiffness G C) *ᵥ x) (.inr (.inl i)) =
      (M₁ *ᵥ block₁ x + s • (G *ᵥ block₀ x) + s • (Cᵀ *ᵥ block₂ x)) i := fun i => by
    simp [mulVec, dotProduct, Fintype.sum_sum_type, blockMass, blockStiffness, block₀, block₁,
      block₂, Finset.mul_sum, mul_assoc, mul_comm]
    ring
  have e2 : ∀ i, ((blockMass M₀ M₁ M₂ + s • blockStiffness G C) *ᵥ x) (.inr (.inr i)) =
      (M₂ *ᵥ block₂ x - s • (C *ᵥ block₁ x)) i := fun i => by
    simp [mulVec, dotProduct, Fintype.sum_sum_type, blockMass, blockStiffness, block₁, block₂,
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

omit [Fintype n₀] [Fintype n₁] [Fintype n₂] [DecidableEq n₀] [DecidableEq n₁]
  [DecidableEq n₂] in
theorem mulVec_eq_iff_eq_inv_mulVec {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}
    (hM : IsUnit M) (y v : n → ℝ) : M *ᵥ y = v ↔ y = M⁻¹ *ᵥ v := by
  have hdet := (isUnit_iff_isUnit_det M).mp hM
  constructor
  · rintro rfl; rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  · rintro rfl; rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]

omit [DecidableEq n₁] in
/-- **Block elimination of the CN system**: for SPD `M₀`, `M₂`, `(M + sK) x = r` iff
`σ = M₀⁻¹(r₀ + s Gᵀ E)`, `B = M₂⁻¹(r₂ + s C E)` and `S E = r₁ - s G M₀⁻¹ r₀ - s Cᵀ M₂⁻¹ r₂`, so
a CN step is two mass solves around one solve with `S`. Supports the block-elimination reading
of the thesis' solver claim. See [QuennevilleBelair2015], Ch. 7 (l. 4284–4285). -/
theorem blockMass_add_smul_mulVec_eq_iff_schur {M₀ : Matrix n₀ n₀ ℝ} (M₁ : Matrix n₁ n₁ ℝ)
    {M₂ : Matrix n₂ n₂ ℝ} (h₀ : M₀.PosDef) (h₂ : M₂.PosDef) (G : Matrix n₁ n₀ ℝ)
    (C : Matrix n₂ n₁ ℝ) (s : ℝ) (x r : BlockIdx n₀ n₁ n₂ → ℝ) :
    (blockMass M₀ M₁ M₂ + s • blockStiffness G C) *ᵥ x = r ↔
      block₀ x = M₀⁻¹ *ᵥ (block₀ r + s • (Gᵀ *ᵥ block₁ x)) ∧
      block₂ x = M₂⁻¹ *ᵥ (block₂ r + s • (C *ᵥ block₁ x)) ∧
      schurComplement M₀ M₁ M₂ G C s *ᵥ block₁ x =
        block₁ r - s • (G *ᵥ (M₀⁻¹ *ᵥ block₀ r)) - s • (Cᵀ *ᵥ (M₂⁻¹ *ᵥ block₂ r)) := by
  rw [blockMass_add_smul_mulVec_eq_iff]
  have r0 : M₀ *ᵥ block₀ x - s • (Gᵀ *ᵥ block₁ x) = block₀ r ↔
      block₀ x = M₀⁻¹ *ᵥ (block₀ r + s • (Gᵀ *ᵥ block₁ x)) := by
    rw [sub_eq_iff_eq_add]; exact mulVec_eq_iff_eq_inv_mulVec h₀.isUnit _ _
  have r2 : M₂ *ᵥ block₂ x - s • (C *ᵥ block₁ x) = block₂ r ↔
      block₂ x = M₂⁻¹ *ᵥ (block₂ r + s • (C *ᵥ block₁ x)) := by
    rw [sub_eq_iff_eq_add]; exact mulVec_eq_iff_eq_inv_mulVec h₂.isUnit _ _
  rw [r0, r2]
  constructor
  · rintro ⟨hσ, h1, hB⟩
    refine ⟨hσ, hB, ?_⟩
    rw [hσ, hB] at h1
    rw [← h1]
    simp only [schurComplement, add_mulVec, smul_mulVec, mulVec_add, mulVec_smul,
      ← mulVec_mulVec]
    module
  · rintro ⟨hσ, hB, hS⟩
    refine ⟨hσ, ?_, hB⟩
    rw [hσ, hB]
    rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq] at hS
    rw [← hS]
    simp only [schurComplement, add_mulVec, smul_mulVec, mulVec_add, mulVec_smul,
      ← mulVec_mulVec]
    module

omit [DecidableEq n₁] in
/-- **The Schur complement is SPD** for SPD blocks and every `s`, so MINRES (and CG) apply to the
`E` system of the block elimination; under this reading the thesis' solver claim holds as stated.
See [QuennevilleBelair2015], Ch. 7 (l. 4284–4285). -/
theorem posDef_schurComplement {M₀ : Matrix n₀ n₀ ℝ} {M₁ : Matrix n₁ n₁ ℝ}
    {M₂ : Matrix n₂ n₂ ℝ} (h₀ : M₀.PosDef) (h₁ : M₁.PosDef) (h₂ : M₂.PosDef)
    (G : Matrix n₁ n₀ ℝ) (C : Matrix n₂ n₁ ℝ) (s : ℝ) :
    (schurComplement M₀ M₁ M₂ G C s).PosDef := by
  have hG : (G * M₀⁻¹ * Gᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      h₀.inv.posSemidef.mul_mul_conjTranspose_same G
  have hC : (Cᵀ * M₂⁻¹ * C).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      h₂.inv.posSemidef.conjTranspose_mul_mul_same C
  exact h₁.add_posSemidef ((hG.add hC).smul (sq_nonneg s))

end ThreeBlock

/-! ### Assembly: the CN system of (4.14) / (4.15) in bases -/

section Assembly

open LinearMap InnerProductSpace
open scoped RealInnerProductSpace

variable {V₀ V₁ V₂ : Type*}
  [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀] [FiniteDimensional ℝ V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [FiniteDimensional ℝ V₂]
  {n₀ n₁ n₂ : Type*} [Fintype n₀] [Fintype n₁] [Fintype n₂]
  [DecidableEq n₀] [DecidableEq n₁] [DecidableEq n₂]

/-- The matrix `(b' i, d (b j))` of a linear map tested against bases (the assembled discrete
gradient `G` for `d = d₀`, the discrete curl `C` for `d = d₁`). -/
def testMatrix {W W' : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℝ W'] {m m' : Type*} (b : Module.Basis m ℝ W)
    (b' : Module.Basis m' ℝ W') (d : W →ₗ[ℝ] W') : Matrix m' m ℝ :=
  Matrix.of fun i j => ⟪b' i, d (b j)⟫

/-- Coefficient vector of a state `(σ, E, B)` in the bases `b₀, b₁, b₂`. -/
def blockCoord (b₀ : Module.Basis n₀ ℝ V₀) (b₁ : Module.Basis n₁ ℝ V₁)
    (b₂ : Module.Basis n₂ ℝ V₂) (x : V₀ × V₁ × V₂) : BlockIdx n₀ n₁ n₂ → ℝ :=
  Sum.elim (fun i => b₀.repr x.1 i) (Sum.elim (fun i => b₁.repr x.2.1 i) fun i => b₂.repr x.2.2 i)

/-- Load vector: the inner products of a state with the basis functions (testing). -/
def blockLoad (b₀ : Module.Basis n₀ ℝ V₀) (b₁ : Module.Basis n₁ ℝ V₁)
    (b₂ : Module.Basis n₂ ℝ V₂) (y : V₀ × V₁ × V₂) : BlockIdx n₀ n₁ n₂ → ℝ :=
  Sum.elim (fun i => ⟪b₀ i, y.1⟫) (Sum.elim (fun i => ⟪b₁ i, y.2.1⟫) fun i => ⟪b₂ i, y.2.2⟫)

omit [FiniteDimensional ℝ V₀] [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
  [DecidableEq n₀] [DecidableEq n₁] [DecidableEq n₂] in
theorem blockLoad_injective (b₀ : Module.Basis n₀ ℝ V₀) (b₁ : Module.Basis n₁ ℝ V₁)
    (b₂ : Module.Basis n₂ ℝ V₂) : Function.Injective (blockLoad b₀ b₁ b₂) := by
  intro y y' h
  have h0 : y.1 = y'.1 := eq_of_inner_basis b₀ fun i => congrFun h (.inl i)
  have h1 : y.2.1 = y'.2.1 := eq_of_inner_basis b₁ fun i => congrFun h (.inr (.inl i))
  have h2 : y.2.2 = y'.2.2 := eq_of_inner_basis b₂ fun i => congrFun h (.inr (.inr i))
  exact Prod.ext h0 (Prod.ext h1 h2)

omit [DecidableEq n₀] [DecidableEq n₁] [DecidableEq n₂] in
/-- **Assembly**: testing `cnLHS d₀ d₁ s x` against the bases gives `(M + sK) c(x)` with the Gram
mass matrices and `G = testMatrix b₀ b₁ d₀`, `C = testMatrix b₁ b₂ d₁`. -/
theorem blockLoad_cnLHS (b₀ : Module.Basis n₀ ℝ V₀) (b₁ : Module.Basis n₁ ℝ V₁)
    (b₂ : Module.Basis n₂ ℝ V₂) (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ)
    (x : V₀ × V₁ × V₂) :
    blockLoad b₀ b₁ b₂ (cnLHS d₀ d₁ s x) =
      (blockMass (gram ℝ b₀) (gram ℝ b₁) (gram ℝ b₂) +
        s • blockStiffness (testMatrix b₀ b₁ d₀) (testMatrix b₁ b₂ d₁)) *ᵥ
          blockCoord b₀ b₁ b₂ x := by
  obtain ⟨σ, E, B⟩ := x
  funext i
  rcases i with i | i | i
  · simp only [blockLoad, cnLHS, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, inner_sub_right,
      inner_smul_right, adjoint_inner_right]
    rw [inner_eq_sum_repr b₀ (b₀ i) σ, inner_eq_sum_repr b₁ (d₀ (b₀ i)) E]
    simp [mulVec, dotProduct, Fintype.sum_sum_type, blockMass, blockStiffness, testMatrix,
      blockCoord, Finset.mul_sum, real_inner_comm, mul_comm, sub_eq_add_neg, mul_assoc]
  · simp only [blockLoad, cnLHS, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr, Sum.elim_inl,
      inner_add_right, inner_smul_right, adjoint_inner_right]
    rw [show ⟪b₁ i, d₀ σ⟫ = ⟪adjoint d₀ (b₁ i), σ⟫ from (adjoint_inner_left _ _ _).symm,
      inner_eq_sum_repr b₁ (b₁ i) E, inner_eq_sum_repr b₀ (adjoint d₀ (b₁ i)) σ,
      inner_eq_sum_repr b₂ (d₁ (b₁ i)) B]
    simp [mulVec, dotProduct, Fintype.sum_sum_type, blockMass, blockStiffness, testMatrix,
      blockCoord, Finset.mul_sum, adjoint_inner_left, real_inner_comm, mul_comm, mul_add]
    ring_nf
  · simp only [blockLoad, cnLHS, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr,
      inner_sub_right, inner_smul_right]
    rw [show ⟪b₂ i, d₁ E⟫ = ⟪adjoint d₁ (b₂ i), E⟫ from (adjoint_inner_left _ _ _).symm,
      inner_eq_sum_repr b₂ (b₂ i) B, inner_eq_sum_repr b₁ (adjoint d₁ (b₂ i)) E]
    simp [mulVec, dotProduct, Fintype.sum_sum_type, blockMass, blockStiffness, testMatrix,
      blockCoord, Finset.mul_sum, adjoint_inner_left, real_inner_comm, mul_comm, sub_eq_add_neg]
    ring_nf

omit [DecidableEq n₀] [DecidableEq n₁] [DecidableEq n₂] in
/-- **A CN step of (4.14) is the assembled linear system**
`(M + sK) c(x') = (M - sK) c(x)` (Gram mass matrices, `G`, `C` the tested `d₀`, `d₁`).
See [QuennevilleBelair2015], (4.14), Ch. 7. -/
theorem isFullCNStep_iff_mulVec (b₀ : Module.Basis n₀ ℝ V₀) (b₁ : Module.Basis n₁ ℝ V₁)
    (b₂ : Module.Basis n₂ ℝ V₂) (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ)
    (x x' : V₀ × V₁ × V₂) :
    IsFullCNStep d₀ d₁ s x.1 x'.1 x.2.1 x'.2.1 x.2.2 x'.2.2 ↔
      (blockMass (gram ℝ b₀) (gram ℝ b₁) (gram ℝ b₂) +
          s • blockStiffness (testMatrix b₀ b₁ d₀) (testMatrix b₁ b₂ d₁)) *ᵥ
            blockCoord b₀ b₁ b₂ x' =
        (blockMass (gram ℝ b₀) (gram ℝ b₁) (gram ℝ b₂) -
          s • blockStiffness (testMatrix b₀ b₁ d₀) (testMatrix b₁ b₂ d₁)) *ᵥ
            blockCoord b₀ b₁ b₂ x := by
  rw [isFullCNStep_iff_cnLHS, sub_eq_add_neg, ← neg_smul, ← blockLoad_cnLHS, ← blockLoad_cnLHS]
  exact (blockLoad_injective b₀ b₁ b₂).eq_iff.symm

/-- **The MINRES system computes the CN iterate**: with the assembled matrices, `v` solves the
symmetrized system `J(M + sK) v = J(M - sK) c(x)` iff `v = c(fullCNStep d₀ d₁ s x)`. Repair of
the thesis' solver claim. See [QuennevilleBelair2015], Ch. 7 (l. 4284–4285). -/
theorem blockSign_mul_mulVec_iff_fullCNStep (b₀ : Module.Basis n₀ ℝ V₀)
    (b₁ : Module.Basis n₁ ℝ V₁) (b₂ : Module.Basis n₂ ℝ V₂) (d₀ : V₀ →ₗ[ℝ] V₁)
    (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ) (x : V₀ × V₁ × V₂) (v : BlockIdx n₀ n₁ n₂ → ℝ) :
    (blockSign * (blockMass (gram ℝ b₀) (gram ℝ b₁) (gram ℝ b₂) +
          s • blockStiffness (testMatrix b₀ b₁ d₀) (testMatrix b₁ b₂ d₁))) *ᵥ v =
        (blockSign * (blockMass (gram ℝ b₀) (gram ℝ b₁) (gram ℝ b₂) -
          s • blockStiffness (testMatrix b₀ b₁ d₀) (testMatrix b₁ b₂ d₁))) *ᵥ
            blockCoord b₀ b₁ b₂ x ↔
      v = blockCoord b₀ b₁ b₂ (fullCNStep d₀ d₁ s x) := by
  have hc := (blockSign_mul_mulVec_iff _ _ _ _ _ _ _ _).2
    ((isFullCNStep_iff_mulVec b₀ b₁ b₂ d₀ d₁ s x _).1 (isFullCNStep_fullCNStep d₀ d₁ s x))
  obtain ⟨_, -, huniq⟩ := existsUnique_blockSign_mul_mulVec
    (posDef_gram_of_linearIndependent b₀.linearIndependent)
    (posDef_gram_of_linearIndependent b₁.linearIndependent)
    (posDef_gram_of_linearIndependent b₂.linearIndependent) (testMatrix b₀ b₁ d₀)
    (testMatrix b₁ b₂ d₁) s (blockCoord b₀ b₁ b₂ x)
  constructor
  · intro hv; exact (huniq v hv).trans (huniq _ hc).symm
  · rintro rfl; exact hc

omit [FiniteDimensional ℝ V₀] [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
  [Fintype n₀] [Fintype n₁] [Fintype n₂] [DecidableEq n₀] [DecidableEq n₁] [DecidableEq n₂] in
/-- `testMatrix b b' d = 0` iff `d = 0`. -/
theorem testMatrix_eq_zero_iff {W W' : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℝ W'] {m m' : Type*} [Fintype m']
    (b : Module.Basis m ℝ W) (b' : Module.Basis m' ℝ W') (d : W →ₗ[ℝ] W') :
    testMatrix b b' d = 0 ↔ d = 0 := by
  constructor
  · intro h
    refine b.ext fun j => eq_of_inner_basis b' fun i => ?_
    simpa [testMatrix] using congrFun (congrFun h i) j
  · rintro rfl; ext i j; simp [testMatrix]

omit [FiniteDimensional ℝ V₀] [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂] [Fintype n₀]
  [DecidableEq n₀] [DecidableEq n₁] [DecidableEq n₂] in
/-- **The assembled CN matrix of (4.14) is not symmetric** for `s ≠ 0` once `d₀ ≠ 0` or
`d₁ ≠ 0`. See [QuennevilleBelair2015], Ch. 7 (l. 4284–4285). -/
theorem not_isSymm_assembled (b₀ : Module.Basis n₀ ℝ V₀) (b₁ : Module.Basis n₁ ℝ V₁)
    (b₂ : Module.Basis n₂ ℝ V₂) {d₀ : V₀ →ₗ[ℝ] V₁} {d₁ : V₁ →ₗ[ℝ] V₂} {s : ℝ} (hs : s ≠ 0)
    (hd : d₀ ≠ 0 ∨ d₁ ≠ 0) :
    ¬ (blockMass (gram ℝ b₀) (gram ℝ b₁) (gram ℝ b₂) +
        s • blockStiffness (testMatrix b₀ b₁ d₀) (testMatrix b₁ b₂ d₁)).IsSymm :=
  not_isSymm_blockMass_add_smul (isHermitian_gram ℝ b₀).eq (isHermitian_gram ℝ b₁).eq
    (isHermitian_gram ℝ b₂).eq hs
    (hd.imp (mt (testMatrix_eq_zero_iff b₀ b₁ d₀).1) (mt (testMatrix_eq_zero_iff b₁ b₂ d₁).1))

omit [DecidableEq n₀] [DecidableEq n₁] [DecidableEq n₂] in
/-- **The reduced system (4.15)**: with an empty `σ` block, a reduced CN step is the assembled
system for the states `(0, E, B)`. See [QuennevilleBelair2015], (4.15), Ch. 7. -/
theorem isReducedCNStep_iff_mulVec [IsEmpty n₀] (b₀ : Module.Basis n₀ ℝ V₀)
    (b₁ : Module.Basis n₁ ℝ V₁) (b₂ : Module.Basis n₂ ℝ V₂) (d₀ : V₀ →ₗ[ℝ] V₁)
    (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ) (E E' : V₁) (B B' : V₂) :
    IsReducedCNStep d₁ s E E' B B' ↔
      (blockMass (gram ℝ b₀) (gram ℝ b₁) (gram ℝ b₂) +
          s • blockStiffness (testMatrix b₀ b₁ d₀) (testMatrix b₁ b₂ d₁)) *ᵥ
            blockCoord b₀ b₁ b₂ (0, E', B') =
        (blockMass (gram ℝ b₀) (gram ℝ b₁) (gram ℝ b₂) -
          s • blockStiffness (testMatrix b₀ b₁ d₀) (testMatrix b₁ b₂ d₁)) *ᵥ
            blockCoord b₀ b₁ b₂ (0, E, B) := by
  have hV0 : ∀ v : V₀, v = 0 := fun v => b₀.ext_elem fun i => isEmptyElim i
  rw [← isFullCNStep_iff_mulVec b₀ b₁ b₂ d₀ d₁ s (0, E, B) (0, E', B')]
  simp only [IsFullCNStep, IsReducedCNStep, add_zero, map_zero, zero_add]
  exact ⟨fun h => ⟨(hV0 _).trans (hV0 _).symm, h⟩, fun h => h.2⟩

/-- **MINRES for the reduced system (4.15)**: with an empty `σ` block, `v` solves the
symmetrized system iff `v = c(0, E', B')` for the reduced CN step `(E, B) ↦ (E', B')`.
See [QuennevilleBelair2015], Ch. 7 (l. 4284–4285). -/
theorem blockSign_mul_mulVec_iff_reducedCNStep [IsEmpty n₀] (b₀ : Module.Basis n₀ ℝ V₀)
    (b₁ : Module.Basis n₁ ℝ V₁) (b₂ : Module.Basis n₂ ℝ V₂) (d₀ : V₀ →ₗ[ℝ] V₁)
    (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ) (E : V₁) (B : V₂) (v : BlockIdx n₀ n₁ n₂ → ℝ) :
    (blockSign * (blockMass (gram ℝ b₀) (gram ℝ b₁) (gram ℝ b₂) +
          s • blockStiffness (testMatrix b₀ b₁ d₀) (testMatrix b₁ b₂ d₁))) *ᵥ v =
        (blockSign * (blockMass (gram ℝ b₀) (gram ℝ b₁) (gram ℝ b₂) -
          s • blockStiffness (testMatrix b₀ b₁ d₀) (testMatrix b₁ b₂ d₁))) *ᵥ
            blockCoord b₀ b₁ b₂ (0, E, B) ↔
      ∃ E' B', IsReducedCNStep d₁ s E E' B B' ∧ v = blockCoord b₀ b₁ b₂ (0, E', B') := by
  obtain ⟨⟨E', B'⟩, hr, -⟩ := existsUnique_isReducedCNStep d₁ s E B
  have hc := (blockSign_mul_mulVec_iff _ _ _ _ _ _ _ _).2
    ((isReducedCNStep_iff_mulVec b₀ b₁ b₂ d₀ d₁ s E E' B B').1 hr)
  obtain ⟨_, -, huniq⟩ := existsUnique_blockSign_mul_mulVec
    (posDef_gram_of_linearIndependent b₀.linearIndependent)
    (posDef_gram_of_linearIndependent b₁.linearIndependent)
    (posDef_gram_of_linearIndependent b₂.linearIndependent) (testMatrix b₀ b₁ d₀)
    (testMatrix b₁ b₂ d₁) s (blockCoord b₀ b₁ b₂ (0, E, B))
  constructor
  · intro hv; exact ⟨E', B', hr, (huniq v hv).trans (huniq _ hc).symm⟩
  · rintro ⟨E'', B'', hr', rfl⟩
    exact (blockSign_mul_mulVec_iff _ _ _ _ _ _ _ _).2
      ((isReducedCNStep_iff_mulVec b₀ b₁ b₂ d₀ d₁ s E E'' B B'').1 hr')

end Assembly

end Feec.TimeStepping
