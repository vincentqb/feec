module

public import Feec.Mesh.Freudenthal
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Shape regularity

A family of `n`-simplices `T = F_T(T̂)`, `F_T x̂ = B_T x̂ + p₀`, is shape regular with constants
`C, c` if `‖B_T‖ ≤ C h_T`, `‖B_T⁻¹‖ ≤ C / h_T` and `|det B_T| ≥ c h_Tⁿ` ([Ciarlet2002], §3.1;
[Arnold2018], Ch. 7); the Freudenthal meshes of a box are shape regular uniformly in the level.

## References

* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018]

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public section

noncomputable section

open Set

namespace Feec.Mesh

variable {n : ℕ}

/-- Shape regularity: `‖B_T‖ ≤ C h_T`, `‖B_T⁻¹‖ ≤ C / h_T` and `c h_Tⁿ ≤ |det B_T|` on `S`. -/
def IsShapeRegular (S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)) (C c : ℝ) : Prop :=
  ∀ T ∈ S, ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ C * diam T ∧
    ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ C / diam T ∧
    c * diam T ^ n ≤ |LinearMap.det T.linearPart|

theorem diam_pos [NeZero n] (T : Affine.Simplex ℝ (Fin n → ℝ) n) : 0 < diam T := by
  have h01 : (0 : Fin (n + 1)) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_one', Nat.one_mod_eq_one.2 (by have := NeZero.ne n; omega)] at this
    exact zero_ne_one this
  have hne : T.points 0 ≠ T.points 1 := fun h => h01 (T.independent.injective h)
  calc 0 < dist (T.points 0) (T.points 1) := dist_pos.2 hne
    _ ≤ diam T := Metric.dist_le_diam_of_mem T.isCompact_closedInterior.isBounded
        (T.point_mem_closedInterior 0) (T.point_mem_closedInterior 1)

theorem norm_linearEquiv_le_mul_diam (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ n * diam T := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg n.cast_nonneg (diam_nonneg T))
    fun x => ?_
  rw [ContinuousLinearEquiv.coe_coe, Affine.Simplex.linearEquiv_apply,
    Affine.Simplex.linearPart_apply]
  calc ‖∑ i, x i • (T.points i.succ - T.points 0)‖
        ≤ ∑ i, ‖x i • (T.points i.succ - T.points 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖x‖ * diam T := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, ← dist_eq_norm]
        exact mul_le_mul (norm_le_pi_norm x i)
          (Metric.dist_le_diam_of_mem T.isCompact_closedInterior.isBounded
            (T.point_mem_closedInterior _) (T.point_mem_closedInterior _))
          dist_nonneg (norm_nonneg _)
    _ = n * diam T * ‖x‖ := by simp; ring

theorem norm_linearEquiv_symm_le_of_ball_subset {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {x : Fin n → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hB : Metric.ball x ρ ⊆ T.closedInterior) :
    ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ 1 / ρ := by
  have hcB : Metric.closedBall x ρ ⊆ T.closedInterior := by
    rw [← closure_ball x hρ.ne']
    exact closure_minimal hB T.isCompact_closedInterior.isClosed
  have hunit : ∀ a ∈ (refSimplex n).closedInterior, ∀ i, 0 ≤ a i ∧ a i ≤ 1 := fun a ha i => by
    rw [mem_closedInterior_refSimplex] at ha
    exact ⟨ha.1 i, (Finset.single_le_sum (fun j _ => ha.1 j) (Finset.mem_univ i)).trans ha.2⟩
  have key : ∀ y, ‖y‖ ≤ ρ → ‖T.linearEquiv.symm y‖ ≤ 1 := by
    intro y hy
    have h1 : x + y ∈ T.closedInterior :=
      hcB (by rwa [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left])
    have h0 : x ∈ T.closedInterior := hcB (Metric.mem_closedBall_self hρ.le)
    rw [T.closedInterior_eq_image_refMap] at h1 h0
    obtain ⟨a, ha, hax⟩ := h1
    obtain ⟨b, hb, hbx⟩ := h0
    have hy' : T.linearEquiv.symm y = a - b := by
      rw [ContinuousLinearEquiv.symm_apply_eq, Affine.Simplex.linearEquiv_apply, map_sub]
      rw [Affine.Simplex.refMap_apply] at hax hbx
      calc y = (x + y) - x := by abel
        _ = _ := by rw [← hax, ← hbx]; abel
    rw [hy']
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hunit a ha i, hunit b hb i]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have hy : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have h := key ((ρ / ‖y‖) • y) (by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hy.ne'])
  rw [map_smul, norm_smul, Real.norm_of_nonneg (by positivity)] at h
  rw [ContinuousLinearEquiv.coe_coe]
  calc ‖T.linearEquiv.symm y‖ = (ρ / ‖y‖ * ‖T.linearEquiv.symm y‖) * (‖y‖ / ρ) := by
        field_simp
    _ ≤ 1 * (‖y‖ / ρ) := by gcongr
    _ = 1 / ρ * ‖y‖ := by ring

theorem one_div_le_abs_det_of_norm_symm_le {T : Affine.Simplex ℝ (Fin n → ℝ) n} {C : ℝ}
    (h : ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ C) :
    1 / ((n.factorial : ℝ) * C ^ n) ≤ |LinearMap.det T.linearPart| := by
  set f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := T.linearEquiv.symm.toLinearEquiv.toLinearMap
  have hentry : ∀ i j, |LinearMap.toMatrix' f i j| ≤ C := fun i j => by
    rw [LinearMap.toMatrix'_apply]
    have hv : ‖(Pi.single j 1 : Fin n → ℝ)‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j' => by
        by_cases hj : j' = j <;> simp [hj]
    calc |f (Pi.single j 1) i|
          ≤ ‖f (Pi.single j 1)‖ := by
            rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i
      _ ≤ ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ * 1 := by
          change ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (Pi.single j 1)‖ ≤ _
          exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
      _ ≤ C := by rw [mul_one]; exact h
  have hdet := Matrix.det_le (abv := AbsoluteValue.abs) hentry
  rw [LinearMap.det_toMatrix', Fintype.card_fin, nsmul_eq_mul] at hdet
  have hf : LinearMap.det f = (LinearMap.det T.linearPart)⁻¹ :=
    LinearEquiv.det_coe_symm T.linearEquiv.toLinearEquiv
  change |LinearMap.det f| ≤ _ at hdet
  rw [hf, abs_inv] at hdet
  have hne : LinearMap.det T.linearPart ≠ 0 :=
    (LinearEquiv.isUnit_det' T.linearEquiv.toLinearEquiv).ne_zero
  have hpos : 0 < |LinearMap.det T.linearPart| := abs_pos.2 hne
  rcases le_or_gt ((n.factorial : ℝ) * C ^ n) 0 with h0 | h0
  · exact (one_div_nonpos.2 h0).trans hpos.le
  · rw [div_le_iff₀ h0]
    calc 1 = |LinearMap.det T.linearPart| * |LinearMap.det T.linearPart|⁻¹ :=
          (mul_inv_cancel₀ hpos.ne').symm
      _ ≤ |LinearMap.det T.linearPart| * (n.factorial * C ^ n) := by gcongr

/-- Shape regularity from inscribed balls of radius `ρ ≥ h_T / σ` ([Ciarlet2002], §3.1). -/
theorem isShapeRegular_of_ball [NeZero n] {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)} {σ : ℝ}
    (hS : ∀ T ∈ S, ∃ x ρ, 0 < ρ ∧ Metric.ball x ρ ⊆ T.closedInterior ∧ diam T ≤ σ * ρ) :
    IsShapeRegular S (max n σ) (1 / ((n.factorial : ℝ) * σ ^ n)) := by
  intro T hT
  obtain ⟨x, ρ, hρ, hB, hd⟩ := hS T hT
  have hh := diam_pos T
  have hσ : 0 < σ := pos_of_mul_pos_left (hh.trans_le hd) hρ.le
  have hinv := norm_linearEquiv_symm_le_of_ball_subset hρ hB
  have hinv' : 1 / ρ ≤ σ / diam T := by
    rw [div_le_div_iff₀ hρ hh]; linarith
  refine ⟨(norm_linearEquiv_le_mul_diam T).trans (by gcongr; exact le_max_left _ _),
    hinv.trans (hinv'.trans (by gcongr; exact le_max_right _ _)), ?_⟩
  have hdet := one_div_le_abs_det_of_norm_symm_le (hinv.trans hinv')
  calc 1 / ((n.factorial : ℝ) * σ ^ n) * diam T ^ n
        = 1 / ((n.factorial : ℝ) * (σ / diam T) ^ n) := by rw [div_pow]; field_simp
    _ ≤ _ := hdet

theorem exists_ball_of_isShapeRegular [NeZero n] {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}
    {C c : ℝ} (hS : IsShapeRegular S C c) :
    ∀ T ∈ S, ∃ x ρ, 0 < ρ ∧ Metric.ball x ρ ⊆ T.closedInterior ∧ diam T ≤ 2 * n * C * ρ := by
  intro T hT
  obtain ⟨-, h2, -⟩ := hS T hT
  have hh := diam_pos T
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hC : 0 < C := by
    have hne : (T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ≠ 0 := fun h0 => by
      have := congrArg (fun f : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => f (T.linearEquiv 1)) h0
      simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
        zero_apply] at this
      exact one_ne_zero (congrFun this ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩)
    have := (norm_pos_iff.2 hne).trans_le h2
    exact (div_pos_iff.1 this).elim (fun h => h.1) fun h => absurd h.2 (not_lt.2 hh.le)
  set c₀ : Fin n → ℝ := fun _ => 1 / (2 * n)
  refine ⟨T.refMap c₀, diam T / (2 * n * C), by positivity, fun z hz => ?_,
    le_of_eq (by field_simp)⟩
  rw [T.closedInterior_eq_image_refMap]
  set w := T.linearEquiv.symm (z - T.refMap c₀)
  have hw : ‖w‖ < 1 / (2 * n) := by
    have hle := ContinuousLinearMap.le_opNorm
      (T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (z - T.refMap c₀)
    rw [ContinuousLinearEquiv.coe_coe] at hle
    rw [Metric.mem_ball, dist_eq_norm] at hz
    calc ‖w‖ ≤ C / diam T * ‖z - T.refMap c₀‖ := hle.trans (by gcongr)
      _ < C / diam T * (diam T / (2 * n * C)) := by gcongr
      _ = 1 / (2 * n) := by field_simp
  have hwi : ∀ i, |w i| < 1 / (2 * n) := fun i =>
    (Real.norm_eq_abs (w i) ▸ norm_le_pi_norm w i).trans_lt hw
  refine ⟨c₀ + w, ?_, ?_⟩
  · rw [mem_closedInterior_refSimplex]
    refine ⟨fun i => ?_, ?_⟩
    · have := (abs_lt.1 (hwi i)).1
      simp only [Pi.add_apply, c₀]; linarith
    · calc ∑ i, (c₀ + w) i ≤ ∑ _i : Fin n, 1 / (n : ℝ) := Finset.sum_le_sum fun i _ => by
            have := (abs_lt.1 (hwi i)).2
            have e : 1 / (2 * (n : ℝ)) + 1 / (2 * n) = 1 / n := by field_simp; ring
            simp only [Pi.add_apply, c₀]; linarith
        _ = 1 := by simp [hn.ne']
  · have hBw : T.linearPart w = z - T.refMap c₀ := by
      rw [← Affine.Simplex.linearEquiv_apply]; exact T.linearEquiv.apply_symm_apply _
    rw [Affine.Simplex.refMap_apply, map_add, hBw, Affine.Simplex.refMap_apply]
    abel

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

theorem abs_det_kuhnMap (σ : Equiv.Perm (Fin n)) : |LinearMap.det (kuhnMap σ)| = 1 := by
  rw [kuhnMap, LinearMap.det_toLin', kuhnMatrix_eq_submatrix, Matrix.det_permute, det_upperOnes,
    mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]

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

theorem norm_linearEquiv_le_freudenthal :
    ‖((mapEquiv (boxMap b h hh.ne') (freudenthalSimplex m σ)).linearEquiv :
      (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ n * h := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [ContinuousLinearEquiv.coe_coe, Affine.Simplex.linearEquiv_apply,
    linearPart_freudenthalMesh_simplex, LinearMap.smul_apply, norm_smul, Real.norm_of_nonneg hh.le]
  calc h * ‖kuhnMap σ x‖ ≤ h * (n * ‖x‖) := by gcongr; exact norm_kuhnMap_apply_le σ x
    _ = n * h * ‖x‖ := by ring

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

/-- The Freudenthal meshes of a box are shape regular with the constants `max n 2` and `1`. -/
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
