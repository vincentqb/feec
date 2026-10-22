module

public import Feec.Mesh.Freudenthal

/-!
# Shape regularity

Every `n`-simplex `T` of `ℝⁿ` is the image `T = F_T(T̂)` of the reference simplex
`T̂ = conv {0, e₀, …, e_{n-1}}` under `F_T x̂ = B_T x̂ + p₀` (`Affine.Simplex.refMap`,
`Affine.Simplex.map_refSimplex`), where `B_T` has columns `pᵢ₊₁ - p₀`. A family of simplices is
*shape regular* with constants `C, c > 0` if
`‖B_T‖ ≤ C h_T`, `‖B_T⁻¹‖ ≤ C / h_T` and `|det B_T| ≥ c h_Tⁿ` for all its members
([Ciarlet2002], §3.1; [Arnold2018], Ch. 7). Here `ℝⁿ` carries Mathlib's
sup norm, `h_T` is the sup-norm diameter and `‖·‖` the induced operator norm; changing the norm
changes only the constants. The classical equivalent formulation by a bound on `h_T / ρ_T`
(`ρ_T` the inradius) is not formalized.

The level-`N` Freudenthal simplex `T = b + (s/N)(m + K_σ)` has `B_T = (s/N) B_σ`, where `B_σ` is
the triangular `0/1` matrix of `Feec.Mesh.kuhnMap`; `‖B_σ‖ ≤ n`, `‖B_σ⁻¹‖ ≤ 2` (the rows of
`B_σ⁻¹` are differences `y_{σ i} - y_{σ(i+1)}`) and `|det B_σ| = 1`. Since `h_T = s/N`, the
Freudenthal meshes of a box are shape regular with constants `C = max n 2`, `c = 1`, uniformly in
the level `N`.

## Main definitions

* `Feec.Mesh.IsShapeRegular S C c`: the set of simplices `S` is shape regular with constants
  `C, c`.

## Main results

* `abs_det_kuhnMap`: `|det B_σ| = 1`;
  `norm_kuhnMap_apply_le`, `norm_le_two_mul_norm_kuhnMap`.
* `linearPart_freudenthalMesh_simplex`: `B_T = (s/N) B_σ` for the Freudenthal simplices.
* `norm_linearEquiv_le_freudenthal`, `norm_linearEquiv_symm_le_freudenthal`,
  `abs_det_linearPart_freudenthal`: `‖B_T‖ ≤ n h`, `‖B_T⁻¹‖ ≤ 2 / h`, `|det B_T| = hⁿ`, `h = s/N`.
* `isShapeRegular_freudenthalMesh`: the Freudenthal meshes of a box are shape regular with
  constants `max n 2` and `1`, for every level `N ≥ 1`.

## References

* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
  (affine families, regular families of triangulations)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (shape regular meshes)
* [J. Bey, *Simplicial grid refinement: on Freudenthal's algorithm and the optimal number of congruence classes*][Bey2000]
  (Freudenthal refinement produces finitely many congruence classes)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public section

noncomputable section

open Set

namespace Feec.Mesh

variable {n : ℕ}

/-! ### Shape regularity -/

/-- A set `S` of `n`-simplices of `ℝⁿ` is shape regular with constants `C, c`:
`‖B_T‖ ≤ C h_T`, `‖B_T⁻¹‖ ≤ C / h_T` and `c h_Tⁿ ≤ |det B_T|` for every `T ∈ S`. -/
def IsShapeRegular (S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)) (C c : ℝ) : Prop :=
  ∀ T ∈ S, ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ C * diam T ∧
    ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ C / diam T ∧
    c * diam T ^ n ≤ |LinearMap.det T.linearPart|

/-! ### The matrix `B_σ` -/

theorem norm_kuhnMap_apply_le (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    ‖kuhnMap σ x‖ ≤ n * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  rw [kuhnMap_apply, tailSum, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin n, |if (σ.symm k : ℕ) ≤ (i : ℕ) then x i else 0| ≤ ∑ _i : Fin n, ‖x‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · exact (Real.norm_eq_abs (x i)).symm.le.trans (norm_le_pi_norm x i)
        · simp
    _ = n * ‖x‖ := by simp

theorem abs_tailSum_le_norm_kuhnMap (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (t : ℕ) :
    |tailSum x t| ≤ ‖kuhnMap σ x‖ := by
  rw [tailSum_eq_of_kuhnMap σ rfl t]
  split_ifs with h
  · exact (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm _ _)
  · simp

theorem norm_le_two_mul_norm_kuhnMap (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    ‖x‖ ≤ 2 * ‖kuhnMap σ x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, ← tailSum_sub_succ x i]
  refine (abs_sub _ _).trans ?_
  linarith [abs_tailSum_le_norm_kuhnMap σ x i, abs_tailSum_le_norm_kuhnMap σ x (i + 1)]

/-- The upper triangular all-ones matrix. -/
def upperOnes (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a i => if a ≤ i then 1 else 0

theorem det_upperOnes (n : ℕ) : (upperOnes n).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [upperOnes]
  · intro i j hij
    simp only [id] at hij
    simp only [upperOnes, Matrix.of_apply]
    exact ite_eq_right (not_le.2 hij)

theorem kuhnMatrix_eq_submatrix (σ : Equiv.Perm (Fin n)) :
    kuhnMatrix σ = (upperOnes n).submatrix σ.symm id := by
  ext k i
  simp only [kuhnMatrix, upperOnes, Matrix.of_apply, Matrix.submatrix_apply, id]
  exact if_congr Fin.le_def.symm rfl rfl

/-- `|det B_σ| = 1`. -/
theorem abs_det_kuhnMap (σ : Equiv.Perm (Fin n)) : |LinearMap.det (kuhnMap σ)| = 1 := by
  rw [kuhnMap, LinearMap.det_toLin', kuhnMatrix_eq_submatrix, Matrix.det_permute, det_upperOnes,
    mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]

/-! ### The Freudenthal simplices -/

theorem linearPart_freudenthalMesh_simplex (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0)
    (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    (mapEquiv (boxMap b h hh) (freudenthalSimplex m σ)).linearPart = h • kuhnMap σ := by
  refine (Pi.basisFun ℝ (Fin n)).ext fun i => ?_
  rw [Pi.basisFun_apply, Affine.Simplex.linearPart_single]
  simp only [mapEquiv_points, freudenthalSimplex_points, boxMap_apply, kuhnVertex_zero, add_zero,
    LinearMap.smul_apply, ← refPoints_succ, kuhnMap_refPoints]
  simp only [smul_add]
  abel

section Bounds

variable (b : Fin n → ℝ) {h : ℝ} (hh : 0 < h) (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n))

/-- `‖B_T‖ ≤ n h` for `T = b + h (m + K_σ)`. -/
theorem norm_linearEquiv_le_freudenthal :
    ‖((mapEquiv (boxMap b h hh.ne') (freudenthalSimplex m σ)).linearEquiv :
      (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ n * h := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [ContinuousLinearEquiv.coe_coe, Affine.Simplex.linearEquiv_apply,
    linearPart_freudenthalMesh_simplex, LinearMap.smul_apply, norm_smul, Real.norm_of_nonneg hh.le]
  calc h * ‖kuhnMap σ x‖ ≤ h * (n * ‖x‖) := by gcongr; exact norm_kuhnMap_apply_le σ x
    _ = n * h * ‖x‖ := by ring

/-- `‖B_T⁻¹‖ ≤ 2 / h` for `T = b + h (m + K_σ)`. -/
theorem norm_linearEquiv_symm_le_freudenthal :
    ‖((mapEquiv (boxMap b h hh.ne') (freudenthalSimplex m σ)).linearEquiv.symm :
      (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ 2 / h := by
  set T := mapEquiv (boxMap b h hh.ne') (freudenthalSimplex m σ)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  rw [ContinuousLinearEquiv.coe_coe]
  set x := T.linearEquiv.symm y
  have hy : y = h • kuhnMap σ x := by
    rw [← LinearMap.smul_apply, ← linearPart_freudenthalMesh_simplex b hh.ne' m σ, ← Affine.Simplex.linearEquiv_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [hy, norm_smul, Real.norm_of_nonneg hh.le]
  calc ‖x‖ ≤ 2 * ‖kuhnMap σ x‖ := norm_le_two_mul_norm_kuhnMap σ x
    _ = 2 / h * (h * ‖kuhnMap σ x‖) := by field_simp

/-- `|det B_T| = hⁿ` for `T = b + h (m + K_σ)`. -/
theorem abs_det_linearPart_freudenthal :
    |LinearMap.det (mapEquiv (boxMap b h hh.ne') (freudenthalSimplex m σ)).linearPart| = h ^ n := by
  rw [linearPart_freudenthalMesh_simplex, LinearMap.det_smul, Module.finrank_fin_fun, abs_mul,
    abs_det_kuhnMap, mul_one, abs_pow, abs_of_pos hh]

end Bounds

theorem diam_freudenthalMesh_simplex_of_isEmpty (hn : n = 0) (b : Fin n → ℝ) {h : ℝ}
    (hh : h ≠ 0) (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    diam (mapEquiv (boxMap b h hh) (freudenthalSimplex m σ)) = 0 := by
  subst hn
  exact Metric.diam_subsingleton (Set.subsingleton_of_subsingleton)

/-- **The Freudenthal meshes of a box are shape regular**, with the constants `C = max n 2`,
`c = 1`, uniformly in the level `N ≥ 1`. -/
theorem isShapeRegular_freudenthalMesh (b : Fin n → ℝ) (s : ℝ) (hs : 0 < s) :
    IsShapeRegular {T | ∃ N : ℕ, T ∈ (freudenthalMesh b s hs (N + 1)).simplices}
      (max n 2) 1 := by
  rintro T ⟨N, hT⟩
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hh : 0 < s / ((N + 1 : ℕ) : ℝ) := div_pos hs hN
  have h1 := norm_linearEquiv_le_freudenthal b hh (finLattice m) σ
  have h2 := norm_linearEquiv_symm_le_freudenthal b hh (finLattice m) σ
  have h3 := abs_det_linearPart_freudenthal b hh (finLattice m) σ
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- the zero-dimensional case: `h_T = 0` and all operators vanish
    subst hn
    rw [diam_freudenthalMesh_simplex_of_isEmpty rfl]
    refine ⟨by simp [ContinuousLinearMap.opNorm_subsingleton], by
      simp [ContinuousLinearMap.opNorm_subsingleton], ?_⟩
    rw [h3]; simp
  · have : NeZero n := ⟨hn.ne'⟩
    rw [diam_freudenthalMesh_simplex b hh]
    refine ⟨h1.trans (by gcongr; exact le_max_left _ _), h2.trans ?_, by rw [h3, one_mul]⟩
    exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_right n 2) hh.le

end Feec.Mesh
