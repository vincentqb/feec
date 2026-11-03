module

public import Feec.FiniteElement.WhitneyComplex
public import Feec.FiniteElement.InterpolationError

/-!
# Interpolation error of the Whitney elements `P₁⁻Λᵏ`

The canonical interpolant `Π_T ω = Σ_g (∫_g ω) φ_g` of the lowest-order Whitney forms
(`Feec.FiniteElement.whitneyInterp`) is estimated in the classical `C¹` form of [Arnold2018],
Ch. 7 ([Ciarlet2002], Thm 3.1.4), with explicit constants:

* **stability**: if the degree-`k` coefficients of `ω` are bounded by `M` on an `n`-simplex `T`,
  then `|Σ_g (∫_g ω) φ_g(x)_s| ≤ C_{n,k} (h_T ‖B_T⁻¹‖)^k M` on `T`
  (`abs_sum_simplexIntegral_mul_whitneyForm_le`; `C_{n,k} = whitneyConst n k`), from the bounds
  `Σ_s |minor_s(B_g)| ≤ 2ⁿ (k h_T)^k` of the face edge matrices and
  `|φ_g| ≤ k! (k + 1) (n (n + 1) ‖B_T⁻¹‖)^k` of the Whitney forms
  (`sum_abs_wedgeProd_faceVertices_le`, `abs_baryGrad_le`, `abs_whitneyForm_le`);
* **reproduction of constants**: `P₁⁻Λᵏ(T)` is the space of trimmed linear forms
  `x ↦ α + ι_x β` for every simplex (`whitneySpace_eq_p1MinusForms`, by a dimension count), so
  constant `k`-forms are Whitney forms (`const_mem_whitneySpace_simplex`);
* **local error**: `|(w - Π_T w)(x)_s| ≤ C_{n,k} (h_T ‖B_T⁻¹‖)^k h_T sup_T ‖Dw‖` for `C¹` forms
  `w` and `#s = k` (`abs_sub_whitneyInterp_le`).

**The reference interpolant.** On the reference simplex `T̂`, the interpolant in all degrees at
once, `whitneyRefInterp g = Σ_k Σ_{k-faces f} (∫_f g) φ_f` (equal to `Π_T̂` on `k`-forms,
`whitneyRefInterp_apply_eq_whitneyInterp`), satisfies `Feec.FiniteElement.IsRefInterpolant` with
`r = 0`, `m = 0` (`isRefInterpolant_whitney`): it reproduces the constant forms
(`whitneyRefInterp_const`) and is stable in `C⁰(T̂)`; hence
`sup_{T̂} ‖f - I f‖ ≤ (1 + C) sup_{T̂} ‖Df‖` (`IsRefInterpolant.norm_sub_le`). This instance is a
side result, stated for coefficient fields `T̂ → (Finset (Fin n) → ℝ)`; the mesh estimates below
do not use it.

**On a mesh.** The global canonical interpolant of the Whitney element family is `Π_T` on every
simplex (`whitney_globalInterp_apply`). With `formL2` the degree-`k` coefficients of a continuous
form as an element of `L²(Ω; Λᵏ)`, on a mesh with `h_T ‖B_T⁻¹‖ ≤ C₀` and `h_T ≤ h`:
`‖w - Π_h w‖_{L²(Ω; Λᵏ)} ≤ #Λᵏ |Ω|^{1/2} C_{n,k} C₀^k h sup_{cl Ω} ‖Dw‖`
(`norm_formL2_sub_glue_le`). Since `Π_h` commutes with `d`
(`LocalElement.glue_globalInterp_mem_maximal` in `Feec.FiniteElement.GlobalInterpolation`), the
same bound for `dw` (with `sup ‖D dw‖`, so `w ∈ C²`) gives the graph-norm error. Smooth
`k`-forms are in `D(d_max)` with the classical `d` (`formL2_mem_maximal`). The estimate takes
the raw shape bound `h_T ‖B_T⁻¹‖ ≤ C₀`, which follows from the second condition of
`Feec.Mesh.IsShapeRegular` (`diam_mul_norm_symm_le_of_isShapeRegular`,
`norm_formL2_sub_glue_le_of_isShapeRegular`). It is proved directly on each simplex, not by
transport from `T̂` (`Feec.FiniteElement.norm_sub_transportInterp_le` would need the naturality
of `Π_T` under affine maps).

## Main definitions

* `Feec.FiniteElement.whitneyConst n k`: the constant of the local estimates.
* `Feec.FiniteElement.formL2`: a continuous form as an `L²` field of `k`-forms on a bounded `Ω`.
* `Feec.FiniteElement.whitneyRefInterp`, `whitneyRefConst`: the reference interpolant and its
  stability constant.

## Main results

* `abs_sub_whitneyInterp_le`: the local interpolation error.
* `isRefInterpolant_whitney`: the Whitney interpolant as a reference interpolant.
* `whitney_globalInterp_apply`, `norm_formL2_sub_glue_le`,
  `norm_formL2_sub_glue_le_of_isShapeRegular`: the global `L²` error.
* `formL2_mem_maximal`, `contDiff_extDeriv`: `d` on smooth forms.

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (approximation
  estimates on shape regular meshes)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], Thm 3.1.4
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5 (canonical interpolants, Whitney forms)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter

namespace Feec.ExteriorFibre

variable {d : Type*} [LinearOrder d] [Fintype d]

omit [Fintype d] in
theorem abs_sgn (j : d) (s : Finset d) : |(sgn j s : ℝ)| = 1 := by
  simp [sgn, abs_pow]

/-- `|(ξ ∧ ω)_s| ≤ #d · A · B` if `|ξ_j| ≤ A` and `|ω_t| ≤ B`. -/
theorem abs_wedge_le {ξ : d → ℝ} {ω : Finset d → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hξ : ∀ j, |ξ j| ≤ A) (hω : ∀ t, |ω t| ≤ B) (s : Finset d) :
    |wedge ξ ω s| ≤ Fintype.card d * (A * B) := by
  rw [wedge_apply]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ s, |sgn j s * ξ j * ω (s.erase j)| ≤ ∑ _j ∈ s, A * B := by
        refine sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul, abs_sgn, one_mul]
        exact mul_le_mul (hξ j) (hω _) (abs_nonneg _) hA
    _ = #s * (A * B) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        gcongr
        exact_mod_cast card_le_univ s

/-- `|(θ_{s₁} ∧ ⋯ ∧ θ_{s_k})_t| ≤ (#d · A)^k` if all `|θ_{ij}| ≤ A`. -/
theorem abs_wedgeProd_le {ι : Type*} [LinearOrder ι] {θ : ι → d → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hθ : ∀ i j, |θ i j| ≤ A) (s : Finset ι) (t : Finset d) :
    |wedgeProd θ s t| ≤ (Fintype.card d * A) ^ #s := by
  induction s using Finset.induction_on_min generalizing t with
  | empty =>
    rw [wedgeProd_empty, Finset.card_empty, pow_zero]
    by_cases ht : t = ∅
    · subst ht; simp
    · simp [ht]
  | insert a s ha ih =>
    have has : a ∉ s := fun h' => lt_irrefl a (ha a h')
    rw [wedgeProd_insert_of_lt _ ha, card_insert_of_notMem has, pow_succ]
    refine (abs_wedge_le hA (by positivity) (hθ a) ih t).trans (le_of_eq ?_)
    ring

end Feec.ExteriorFibre

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh Feec.Domain

variable {n : ℕ}

/-! ### The degree-`k` part of a fibre form -/

/-- The degree-`k` part `Σ_{#s = k} α_s dx_s` of a fibre form. -/
def degPart (k : ℕ) (α : Finset (Fin n) → ℝ) : Finset (Fin n) → ℝ :=
  fun t => if #t = k then α t else 0

theorem isDeg_degPart (k : ℕ) (α : Finset (Fin n) → ℝ) : IsDeg k (degPart k α) :=
  fun _ ht => ite_eq_right_iff.2 fun h => absurd h ht

theorem degPart_of_card {k : ℕ} (α : Finset (Fin n) → ℝ) {t : Finset (Fin n)} (ht : #t = k) :
    degPart k α t = α t := by simp [degPart, ht]

/-! ### Bounds for face integrals -/

/-- **The face integral only sees the degree-`k` coefficients**: if `|ω_s| ≤ M` on the face for
`#s = k`, then `|∫_p ω| ≤ (Σ_s |minor_s(B_p)|) M / k!` (the minors vanish for `#s ≠ k`). -/
theorem abs_simplexIntegral_le_of_card {k : ℕ} {p : Fin (k + 1) → Fin n → ℝ} {ω : FormField n}
    {M : ℝ} (hM : ∀ x ∈ refSimplex k, ∀ s : Finset (Fin n), #s = k → |ω (simplexMap p x) s| ≤ M) :
    |simplexIntegral p ω| ≤
      (∑ s, |wedgeProd (simplexMatrix p) s univ|) * M / k.factorial := by
  rw [simplexIntegral_def, ← Real.norm_eq_abs, div_eq_mul_one_div, ← volume_real_refSimplex]
  refine norm_setIntegral_le_of_norm_le_const (volume_refSimplex_lt_top k) fun x hx => ?_
  rw [Real.norm_eq_abs, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ => ?_)
  by_cases hs : #s = k
  · rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hM x hx s hs) (abs_nonneg _)
  · have h0 : wedgeProd (simplexMatrix p) s univ = 0 :=
      isDeg_wedgeProd _ s univ (by rw [card_univ, Fintype.card_fin]; exact Ne.symm hs)
    simp [h0]

/-! ### Geometry of a simplex: vertices, barycentric coordinates and their gradients -/

theorem simplexMatrix_faceVertices_abs_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) {k : ℕ}
    (g : Finset (Fin (n + 1))) (hg : #g = k + 1) (i : Fin n) (l : Fin k) :
    |simplexMatrix (faceVertices T.points g hg) i l| ≤ diam T := by
  have hb := T.isCompact_closedInterior.isBounded
  have h := Metric.dist_le_diam_of_mem hb (T.point_mem_closedInterior _)
    (T.point_mem_closedInterior (g.orderEmbOfFin hg 0)) (x := T.points (g.orderEmbOfFin hg l.succ))
  rw [dist_eq_norm] at h
  refine le_trans ?_ h
  simp only [simplexMatrix, faceVertices, Function.comp_apply]
  rw [← Pi.sub_apply, ← Real.norm_eq_abs]
  exact norm_le_pi_norm _ i

/-- The minors of the edge matrix of a face: `Σ_s |minor_s| ≤ 2ⁿ (k h_T)^k`. -/
theorem sum_abs_wedgeProd_faceVertices_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) {k : ℕ}
    (g : Finset (Fin (n + 1))) (hg : #g = k + 1) :
    ∑ s, |wedgeProd (simplexMatrix (faceVertices T.points g hg)) s univ| ≤
      2 ^ n * (k * diam T) ^ k := by
  have hterm : ∀ s : Finset (Fin n),
      |wedgeProd (simplexMatrix (faceVertices T.points g hg)) s univ| ≤ (k * diam T) ^ k := by
    intro s
    by_cases hs : #s = k
    · have h := abs_wedgeProd_le (diam_nonneg T) (simplexMatrix_faceVertices_abs_le T g hg) s univ
      rwa [Fintype.card_fin, hs] at h
    · rw [isDeg_wedgeProd _ s univ (by rw [card_univ, Fintype.card_fin]; exact Ne.symm hs),
        abs_zero]
      exact pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (diam_nonneg T)) _
  calc _ ≤ ∑ _s : Finset (Fin n), (k * diam T) ^ k := sum_le_sum fun s _ => hterm s
    _ = _ := by rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]; simp

/-- `B_T x̂ = (edge matrix) x̂`. -/
theorem edgeMatrix_mulVec (T : Affine.Simplex ℝ (Fin n → ℝ) n) (v : Fin n → ℝ) :
    Matrix.mulVec (edgeMatrix T.points) v = T.linearPart v := by
  funext i
  rw [Affine.Simplex.linearPart_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, simplexMatrix, Finset.sum_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  exact sum_congr rfl fun l _ => by ring

theorem inv_edgeMatrix_mulVec (T : Affine.Simplex ℝ (Fin n → ℝ) n) (y : Fin n → ℝ) :
    Matrix.mulVec (edgeMatrix T.points)⁻¹ y = T.linearEquiv.symm y := by
  apply T.linearPart_injective
  rw [← edgeMatrix_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_det_edgeMatrix T), Matrix.one_mulVec,
    ← Affine.Simplex.linearEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem abs_inv_edgeMatrix_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) (m l : Fin n) :
    |(edgeMatrix T.points)⁻¹ m l| ≤
      ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ := by
  have h : (edgeMatrix T.points)⁻¹ m l =
      Matrix.mulVec (edgeMatrix T.points)⁻¹ (Pi.single l 1) m := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h, inv_edgeMatrix_mulVec, ← Real.norm_eq_abs]
  refine (norm_le_pi_norm _ m).trans ?_
  refine ((T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ).le_opNorm _).trans ?_
  refine le_of_le_of_eq (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (mul_one _)
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases hj : j = l
  · subst hj; simp
  · simp [hj]

/-- **The gradients of the barycentric coordinates**: `|dλᵢ| ≤ (n + 1) ‖B_T⁻¹‖`. -/
theorem abs_baryGrad_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i : Fin (n + 1)) (l : Fin n) :
    |baryGrad T.points i l| ≤
      (n + 1) * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ := by
  set S := ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖
  have hS : 0 ≤ S := norm_nonneg _
  refine Fin.cases ?_ (fun m => ?_) i
  · simp only [baryGrad, Fin.cons_zero, abs_neg]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m, |(edgeMatrix T.points)⁻¹ m l| ≤ ∑ _m : Fin n, S :=
          sum_le_sum fun m _ => abs_inv_edgeMatrix_le T m l
      _ = n * S := by simp
      _ ≤ (n + 1) * S := by nlinarith
  · simp only [baryGrad, Fin.cons_succ]
    calc |(edgeMatrix T.points)⁻¹ m l| ≤ S := abs_inv_edgeMatrix_le T m l
      _ ≤ (n + 1) * S := le_mul_of_one_le_left hS (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-- On `T`, the barycentric coordinates lie in `[0, 1]`. -/
theorem baryCoord_mem_Icc (T : Affine.Simplex ℝ (Fin n → ℝ) n) {x : Fin n → ℝ}
    (hx : x ∈ T.closedInterior) (i : Fin (n + 1)) : baryCoord T.points x i ∈ Set.Icc (0 : ℝ) 1 := by
  rw [← Affine.Simplex.convexHull_eq_closedInterior] at hx
  obtain ⟨y, hy, rfl⟩ := exists_simplexMap_eq_of_mem_convexHull T.points hx
  rw [baryCoord_simplexMap (isUnit_det_edgeMatrix T)]
  refine ⟨hy i, ?_⟩
  have h := sum_refBary y
  rw [← Finset.add_sum_erase _ _ (mem_univ i)] at h
  have : 0 ≤ ∑ j ∈ univ.erase i, refBary y j := sum_nonneg fun j _ => hy j
  linarith

/-- **Bound of the Whitney forms on `T`**: `|φ_g(x)_s| ≤ k! (k + 1) (n (n + 1) ‖B_T⁻¹‖)^k`. -/
theorem abs_whitneyForm_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) {k : ℕ} {g : Finset (Fin (n + 1))}
    (hg : #g = k + 1) {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) (s : Finset (Fin n)) :
    |whitneyForm T.points g x s| ≤ k.factorial * ((k + 1) * (n * ((n + 1) *
      ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖)) ^ k) := by
  set G := (n + 1) * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖
  have hG : 0 ≤ G := by positivity
  simp only [whitneyForm, Pi.smul_apply, smul_eq_mul, hg, Nat.add_sub_cancel, abs_mul,
    Nat.abs_cast]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  simp only [whitneyFibre, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ g, |sgn i g * baryCoord T.points x i * wedgeProd (baryGrad T.points) (g.erase i) s|
      ≤ ∑ _i ∈ g, (n * G) ^ k := by
        refine sum_le_sum fun i hi => ?_
        rw [abs_mul, abs_mul, abs_sgn, one_mul]
        have h1 : |baryCoord T.points x i| ≤ 1 := by
          have := baryCoord_mem_Icc T hx i
          rw [abs_of_nonneg this.1]; exact this.2
        have h2 := abs_wedgeProd_le hG (abs_baryGrad_le T) (g.erase i) s
        rw [Fintype.card_fin, card_erase_of_mem hi, hg, Nat.add_sub_cancel] at h2
        calc |baryCoord T.points x i| * |wedgeProd (baryGrad T.points) (g.erase i) s|
            ≤ 1 * (n * G) ^ k := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ = (k + 1) * (n * G) ^ k := by rw [sum_const, hg, nsmul_eq_mul]; push_cast; ring

/-! ### Constant forms are Whitney forms -/

theorem const_mem_whitneySpace_simplex (T : Affine.Simplex ℝ (Fin n → ℝ) n) {k : ℕ}
    {α : Finset (Fin n) → ℝ} (hα : IsDeg k α) : (fun _ => α) ∈ whitneySpace T.points k := by
  rw [whitneySpace_eq_p1MinusForms]; exact const_mem_p1MinusForms hα

/-! ### The local interpolation error -/

/-- The constant of the local estimate: `#{k-faces} · 2ⁿ k^k (k + 1) (n (n + 1))^k`. -/
def whitneyConst (n k : ℕ) : ℝ :=
  (n + 1).choose (k + 1) * (2 ^ n * k ^ k * ((k + 1) * (n * (n + 1)) ^ k))

theorem whitneyConst_nonneg (n k : ℕ) : 0 ≤ whitneyConst n k := by
  unfold whitneyConst; positivity

/-- **Stability of the Whitney interpolation formula**: if the degree-`k` coefficients of `ω` are
bounded by `M` on `T`, then at every point of `T`,
`|Σ_g (∫_g ω) φ_g(x)_s| ≤ C_{n,k} (h_T ‖B_T⁻¹‖)^k M`: the face integrals are `O(h_T^k M)` and the
Whitney forms `O(‖B_T⁻¹‖^k)`. No continuity of `ω` is needed. -/
theorem abs_sum_simplexIntegral_mul_whitneyForm_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ)
    {ω : FormField n} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ T.closedInterior, ∀ t : Finset (Fin n), #t = k → |ω y t| ≤ M)
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) (s : Finset (Fin n)) :
    |∑ g : Faces n k, simplexIntegral (faceVertices T.points g.1 g.2) ω *
        whitneyForm T.points g.1 x s| ≤
      whitneyConst n k * (diam T * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) ^ k *
        M := by
  set S := ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖
  set D := diam T
  have hS : 0 ≤ S := norm_nonneg _
  have hD : 0 ≤ D := diam_nonneg T
  have hface : ∀ g : Faces n k,
      |simplexIntegral (faceVertices T.points g.1 g.2) ω * whitneyForm T.points g.1 x s| ≤
        2 ^ n * k ^ k * ((k + 1) * (n * (n + 1)) ^ k) * (D * S) ^ k * M := by
    intro g
    have hint : |simplexIntegral (faceVertices T.points g.1 g.2) ω| ≤
        2 ^ n * (k * D) ^ k * M / k.factorial := by
      refine (abs_simplexIntegral_le_of_card (M := M) fun y hy t ht => ?_).trans ?_
      · refine hM _ ?_ t ht
        rw [← Affine.Simplex.convexHull_eq_closedInterior]
        exact convexHull_mono (Set.range_comp_subset_range _ _) (simplexMap_mem_convexHull _ hy)
      · have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
        have hsum := sum_abs_wedgeProd_faceVertices_le T g.1 g.2
        rw [div_le_div_iff_of_pos_right hfac]
        exact mul_le_mul_of_nonneg_right hsum hM0
    have hφ := abs_whitneyForm_le T g.2 hx s
    have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    rw [abs_mul]
    calc |simplexIntegral (faceVertices T.points g.1 g.2) ω| * |whitneyForm T.points g.1 x s|
        ≤ (2 ^ n * (k * D) ^ k * M / k.factorial) *
            (k.factorial * ((k + 1) * (n * ((n + 1) * S)) ^ k)) :=
          mul_le_mul hint hφ (abs_nonneg _) (by positivity)
      _ = _ := by
          field_simp
          rw [mul_pow, mul_pow, mul_pow]
          ring
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ g : Faces n k,
        |simplexIntegral (faceVertices T.points g.1 g.2) ω * whitneyForm T.points g.1 x s|
      ≤ ∑ _g : Faces n k, 2 ^ n * k ^ k * ((k + 1) * (n * (n + 1)) ^ k) * (D * S) ^ k * M :=
        sum_le_sum fun g _ => hface g
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_finset_len, Fintype.card_fin, nsmul_eq_mul,
          whitneyConst]
        ring

/-- **Local interpolation error of the Whitney interpolant** ([Arnold2018], Ch. 7, the classical
`C¹` form): for a `C¹` form `w` with `‖Dw‖ ≤ L` on `T`, at every point of `T` the degree-`k`
coefficients satisfy `|(w - Π_T w)(x)_s| ≤ C_{n,k} (h_T ‖B_T⁻¹‖)^k h_T L`. Proof: with the
constant form `c = w(x)` (degree-`k` part), `Π_T c = c`, so `(w - Π_T w)(x)_s = -Π_T(w - c)(x)_s`,
and `|w - c| ≤ h_T L` on `T` (mean value theorem). -/
theorem abs_sub_whitneyInterp_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) {w : FormField n}
    (hw : ContDiff ℝ 1 w) {L : ℝ}
    (hL : ∀ y ∈ T.closedInterior, ‖fderiv ℝ w y‖ ≤ L) {x : Fin n → ℝ}
    (hx : x ∈ T.closedInterior) {s : Finset (Fin n)} (hs : #s = k) :
    |w x s - (whitneyInterp (isUnit_det_edgeMatrix T) k ⟨w, hw.continuous⟩ : FormField n) x s| ≤
      whitneyConst n k * (diam T * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) ^ k *
        (diam T * L) := by
  set hp := isUnit_det_edgeMatrix T
  set D := diam T
  have hD : 0 ≤ D := diam_nonneg T
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL x hx)
  -- the constant form `c = w(x)` (degree-`k` part) is reproduced
  set c : FormField n := fun _ => degPart k (w x)
  have hc : c ∈ whitneySpace T.points k := const_mem_whitneySpace_simplex T (isDeg_degPart k _)
  have hcc : Continuous c := continuous_const
  have hwc : Continuous (w - c) := hw.continuous.sub hcc
  have hsplit : (⟨w, hw.continuous⟩ : contForms n) =
      ⟨w - c, hwc⟩ + Submodule.inclusion (whitneySpace_le_contForms T.points k) ⟨c, hc⟩ := by
    ext1; simp
  have hPi : (whitneyInterp hp k ⟨w, hw.continuous⟩ : FormField n) =
      (whitneyInterp hp k ⟨w - c, hwc⟩ : FormField n) + c := by
    rw [hsplit, map_add, whitneyInterp_inclusion]; rfl
  have hcx : c x s = w x s := degPart_of_card _ hs
  rw [hPi, Pi.add_apply, Pi.add_apply, hcx, sub_add_cancel_right, abs_neg,
    whitneyInterp_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine abs_sum_simplexIntegral_mul_whitneyForm_le T k (mul_nonneg hD hL0) (fun z hz t ht => ?_)
    hx s
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => (hw.differentiable one_ne_zero) y) hL (convex_closedInterior T) hx hz
  have hdist : ‖z - x‖ ≤ D := by
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem T.isCompact_closedInterior.isBounded hz hx
  change |w z t - degPart k (w x) t| ≤ D * L
  rw [degPart_of_card _ ht, ← Pi.sub_apply, ← Real.norm_eq_abs]
  calc ‖(w z - w x) t‖ ≤ ‖w z - w x‖ := norm_le_pi_norm _ t
    _ ≤ L * ‖z - x‖ := hmv
    _ ≤ L * D := mul_le_mul_of_nonneg_left hdist hL0
    _ = D * L := mul_comm _ _

/-! ### The Whitney interpolant as a reference interpolant (`IsRefInterpolant`) -/

/-- The face integral only depends on the degree-`k` coefficients on the face. -/
theorem simplexIntegral_congr_card {k : ℕ} (p : Fin (k + 1) → Fin n → ℝ) {ω η : FormField n}
    (h : ∀ x ∈ refSimplex k, ∀ s : Finset (Fin n), #s = k →
      ω (simplexMap p x) s = η (simplexMap p x) s) :
    simplexIntegral p ω = simplexIntegral p η := by
  rw [simplexIntegral_def, simplexIntegral_def]
  refine setIntegral_congr_fun (measurableSet_refSimplex k) fun x hx => ?_
  refine sum_congr rfl fun s _ => ?_
  by_cases hs : #s = k
  · rw [h x hx s hs]
  · rw [isDeg_wedgeProd _ s univ (by rw [card_univ, Fintype.card_fin]; exact Ne.symm hs),
      mul_zero, mul_zero]

/-- **The canonical interpolant of the lowest-order Whitney forms on the reference simplex**, in all
degrees at once: `I g = Σ_k Σ_{k-faces f} (∫_f g) φ_f` (on `k`-forms, `Π_T̂` of `P₁⁻Λᵏ(T̂)`,
`whitneyRefInterp_apply_of_card`). -/
def whitneyRefInterp (g : (Fin n → ℝ) → Finset (Fin n) → ℝ) (x : Fin n → ℝ) :
    Finset (Fin n) → ℝ :=
  ∑ k ∈ range (n + 1), ∑ f : Faces n k,
    simplexIntegral (faceVertices (refPoints n) f.1 f.2) g • whitneyForm (refPoints n) f.1 x

/-- The stability constant of `whitneyRefInterp`: `Σ_{k ≤ n} C_{n,k} (h_T̂ ‖B_T̂⁻¹‖)^k`. -/
def whitneyRefConst (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), whitneyConst n k *
    (diam (Feec.Mesh.refSimplex n) *
      ‖((Feec.Mesh.refSimplex n).linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) ^ k

theorem whitneyRefConst_nonneg (n : ℕ) : 0 ≤ whitneyRefConst n :=
  sum_nonneg fun k _ => mul_nonneg (whitneyConst_nonneg n k)
    (pow_nonneg (mul_nonneg (diam_nonneg _) (norm_nonneg _)) k)

/-- The degree-`k` coefficient of `whitneyRefInterp g` is the face-integral formula of degree
`k` (the Whitney forms of the other degrees vanish there). -/
theorem whitneyRefInterp_apply_of_card (g : (Fin n → ℝ) → Finset (Fin n) → ℝ)
    (x : Fin n → ℝ) {s : Finset (Fin n)} {k : ℕ} (hs : #s = k) :
    whitneyRefInterp g x s = ∑ f : Faces n k,
      simplexIntegral (faceVertices (refPoints n) f.1 f.2) g * whitneyForm (refPoints n) f.1 x s := by
  have hk : k ∈ range (n + 1) := by
    rw [Finset.mem_range, ← hs]; have := card_le_univ s; rw [Fintype.card_fin] at this; omega
  simp only [whitneyRefInterp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single_of_mem k hk fun k' _ hk' => sum_eq_zero fun f _ => by
    rw [isDeg_whitneyForm _ f.2 x s (by rw [hs]; exact Ne.symm hk'), mul_zero]]

/-- On continuous `k`-forms the reference interpolant is `Π_T̂`. -/
theorem whitneyRefInterp_apply_eq_whitneyInterp (g : contForms n) (x : Fin n → ℝ)
    {s : Finset (Fin n)} {k : ℕ} (hs : #s = k) :
    whitneyRefInterp g x s =
      (whitneyInterp (isUnit_det_edgeMatrix (Feec.Mesh.refSimplex n)) k g : FormField n) x s := by
  rw [whitneyRefInterp_apply_of_card _ x hs, whitneyInterp_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

/-- **`I` reproduces the constant forms** (all degrees). -/
theorem whitneyRefInterp_const (c : Finset (Fin n) → ℝ) (x : Fin n → ℝ) :
    whitneyRefInterp (fun _ => c) x = c := by
  funext t
  set k := #t
  set hp := isUnit_det_edgeMatrix (Feec.Mesh.refSimplex n)
  have hc : (fun _ => degPart k c) ∈ whitneySpace (Feec.Mesh.refSimplex n).points k :=
    const_mem_whitneySpace_simplex _ (isDeg_degPart k c)
  rw [whitneyRefInterp_apply_eq_whitneyInterp ⟨fun _ => c, continuous_const⟩ x rfl]
  have e : (whitneyInterp hp k ⟨fun _ => c, continuous_const⟩ : FormField n) =
      (whitneyInterp hp k (Submodule.inclusion (whitneySpace_le_contForms _ k) ⟨_, hc⟩) :
        FormField n) := by
    rw [whitneyInterp_eq_sum, whitneyInterp_eq_sum]
    refine sum_congr rfl fun f _ => ?_
    congr 1
    exact simplexIntegral_congr_card _ fun y _ s hs => (degPart_of_card c hs).symm
  rw [e, whitneyInterp_inclusion]
  exact degPart_of_card c rfl

/-- **The Whitney interpolant is a reference interpolant** in the sense of
`Feec.FiniteElement.IsRefInterpolant` ([Ciarlet2002], Thm 3.1.4; [Arnold2018], Ch. 7): it is
additive on `C¹` fields, reproduces `P₀` (the constant forms of all degrees,
`whitneyRefInterp_const`), and is stable in the `C⁰(T̂)` norm,
`sup_{T̂} ‖I g‖ ≤ C sup_{T̂} ‖g‖` (`r = 0`, `m = 0`, `C = whitneyRefConst n`). -/
theorem isRefInterpolant_whitney (n : ℕ) :
    IsRefInterpolant n 0 0 (Finset (Fin n) → ℝ) whitneyRefInterp (whitneyRefConst n) where
  le_succ := Nat.zero_le _
  map_sub V hV hTV f g hf hg x _ := by
    have hsub : ∀ k (q : Faces n k), simplexMap (faceVertices (refPoints n) q.1 q.2) ''
        refSimplex k ⊆ V := by
      rintro k q _ ⟨y, hy, rfl⟩
      refine hTV ?_
      rw [← Affine.Simplex.convexHull_eq_closedInterior]
      exact convexHull_mono (Set.range_comp_subset_range _ _) (simplexMap_mem_convexHull _ hy)
    simp only [whitneyRefInterp, ← Finset.sum_sub_distrib, ← sub_smul]
    refine sum_congr rfl fun k _ => sum_congr rfl fun q _ => ?_
    rw [simplexIntegral_sub (hf.continuousOn.mono (hsub k q)) (hg.continuousOn.mono (hsub k q))]
  apply_eq p hp x _ := by
    have hc : ∀ y, p y = p 0 := fun y => by
      have hd : Differentiable ℝ p :=
        (contDiff_of_mem_polyFunctions hp (N := 1)).differentiable one_ne_zero
      exact is_const_of_fderiv_eq_zero hd (fun z => by rw [fderiv_eq_zero_of_mem_polyFunctions_zero hp]; rfl) y 0
    have e : p = fun _ => p 0 := funext hc
    rw [e, whitneyRefInterp_const]
  norm_le V hV hTV g hg B hB x hx := by
    have hB0 : ∀ y ∈ (Feec.Mesh.refSimplex n).closedInterior, ‖g y‖ ≤ B 0 := fun y hy => by
      simpa using hB 0 le_rfl y hy
    have hB00 : 0 ≤ B 0 := (norm_nonneg _).trans (hB0 x hx)
    rw [sum_range_one]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (whitneyRefConst_nonneg n) hB00)).2 fun t => ?_
    rw [Real.norm_eq_abs, whitneyRefInterp_apply_of_card g x (rfl : #t = #t)]
    have hk : #t ∈ range (n + 1) := by
      rw [Finset.mem_range]; have := card_le_univ t; rw [Fintype.card_fin] at this; omega
    refine (abs_sum_simplexIntegral_mul_whitneyForm_le (Feec.Mesh.refSimplex n) #t hB00
      (fun y hy s _ => (norm_le_pi_norm (g y) s).trans (hB0 y hy)) hx t).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hB00
    exact single_le_sum (f := fun k => whitneyConst n k *
      (diam (Feec.Mesh.refSimplex n) *
        ‖((Feec.Mesh.refSimplex n).linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) ^ k)
      (fun k _ => mul_nonneg (whitneyConst_nonneg n k)
        (pow_nonneg (mul_nonneg (diam_nonneg _) (norm_nonneg _)) k)) hk

/-! ### The canonical interpolant of the Whitney element family -/

/-- On each simplex, the global canonical interpolant of the Whitney element family is the
canonical interpolant `Π_T` of `P₁⁻Λᵏ(T)` (the face integrals agree up to the orientation sign
of the enumeration of each face). -/
theorem whitney_globalInterp_apply (M : SimplicialMesh n) (k : ℕ) (w : contForms n)
    (T : M.simplices) :
    ((((whitneyElement n).globalInterp M k w : (whitneyElement n).Piecewise M k) T :
        (whitneyElement n).space T k) : FormField n) =
      (whitneyInterp (isUnit_det_edgeMatrix (T : Affine.Simplex ℝ (Fin n → ℝ) n)) k w :
        FormField n) := by
  classical
  obtain ⟨T', hT'⟩ := T
  set hp := isUnit_det_edgeMatrix T'
  have h := (whitneyElement n).localSpace_ext T' k
    (u := (((whitneyElement n).globalInterp M k w : (whitneyElement n).Piecewise M k) ⟨T', hT'⟩))
    (v := whitneyInterp hp k w) fun g hg i => by
      refine (LocalElement.localDof_globalInterp (whitneyElement n) M k w ⟨T', hT'⟩ g hg i).trans ?_
      change whitneyFaceDof g k w = whitneyFaceDof g k ⟨_, _⟩
      have hgc : g.card = k + 1 := i.2
      set f : Finset (Fin (n + 1)) := univ.filter fun j => T'.points j ∈ g
      have hfg : f.image T'.points = g := by
        ext x
        simp only [f, Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨j, hj, rfl⟩; exact hj.2
        · intro hx
          obtain ⟨j, rfl⟩ := mem_vertexSet.1 (hg hx)
          exact ⟨j, ⟨mem_univ _, hx⟩, rfl⟩
      have hf : #f = k + 1 := by
        rw [← hgc, ← hfg, Finset.card_image_of_injective _ T'.independent.injective]
      have hinj : Function.Injective (faceVertices T'.points f hf) :=
        T'.independent.injective.comp (f.orderEmbOfFin hf).injective
      have hrange : Set.range (faceEnum g (k + 1)) = Set.range (faceVertices T'.points f hf) := by
        rw [range_faceEnum hgc, faceVertices, Set.range_comp, Finset.range_orderEmbOfFin, ← hfg,
          Finset.coe_image]
      obtain ⟨ε, -, hε⟩ := exists_sign_simplexIntegral_eq (injective_faceEnum hgc) hinj hrange
      rw [whitneyFaceDof_apply, whitneyFaceDof_apply, hε, hε]
      congr 1
      exact (simplexIntegral_whitneyInterp hp w ⟨f, hf⟩).symm
  exact congrArg Subtype.val h

/-! ### Continuous forms as `L²` fields -/

/-- The degree-`k` coefficients of a continuous form, as an element of `L²(Ω; Λᵏ)` (`Ω`
bounded). -/
def formL2 {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) (k : ℤ) :
    contForms n →ₗ[ℝ] L2F ℝ Ω (formIdx n k) where
  toFun w := Feec.Domain.toL2F fun s => memLp_of_continuous hΩ hb (continuous_formComp (k := k) w.2 s)
  map_add' w w' := by
    refine PiLp.ext fun s => ?_
    change (memLp_of_continuous hΩ hb (continuous_formComp (k := k) (w + w').2 s)).toLp _ =
      (memLp_of_continuous hΩ hb (continuous_formComp (k := k) w.2 s)).toLp _ +
        (memLp_of_continuous hΩ hb (continuous_formComp (k := k) w'.2 s)).toLp _
    rw [← MemLp.toLp_add]
    rfl
  map_smul' a w := by
    refine PiLp.ext fun s => ?_
    change (memLp_of_continuous hΩ hb (continuous_formComp (k := k) (a • w).2 s)).toLp _ =
      a • (memLp_of_continuous hΩ hb (continuous_formComp (k := k) w.2 s)).toLp _
    rw [← MemLp.toLp_const_smul]
    rfl

theorem coeFn_formL2 {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    (k : ℤ) (w : contForms n) (s : formIdx n k) :
    (formL2 hΩ hb k w s : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω]
      fun x => (w : FormField n) x s.1 :=
  (memLp_of_continuous hΩ hb (continuous_formComp (k := k) w.2 s)).coeFn_toLp

/-- `formL2` only sees the values on `Ω`. -/
theorem formL2_congr {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    (k : ℤ) {w w' : contForms n} (h : ∀ x ∈ Ω, (w : FormField n) x = (w' : FormField n) x) :
    formL2 hΩ hb k w = formL2 hΩ hb k w' := by
  refine PiLp.ext fun s => Lp.ext ?_
  filter_upwards [coeFn_formL2 hΩ hb k w s, coeFn_formL2 hΩ hb k w' s,
    ae_restrict_mem hΩ] with x h1 h2 hx
  rw [h1, h2, h x hx]

theorem _root_.Feec.Mesh.SimplicialMesh.isBounded_domain (M : SimplicialMesh n) :
    Bornology.IsBounded M.domain := by
  refine Bornology.IsBounded.subset ?_ subset_closure
  rw [← M.biUnion_closedInterior]
  exact (Bornology.isBounded_biUnion_finset M.simplices).2 fun T _ => T.isCompact_closedInterior.isBounded

/-- The constant piecewise field of a continuous form is the form. -/
theorem pieceL2_formComp_eq_formL2 (M : SimplicialMesh n) (hΩ : MeasurableSet M.domain) (k : ℤ)
    (w : contForms n) :
    pieceL2 M M.domain (fun _ => formComp (k := k) (w : FormField n))
        (fun _ _ s => continuous_formComp w.2 s) =
      formL2 hΩ M.isBounded_domain k w := by
  refine PiLp.ext fun s => Lp.ext ?_
  filter_upwards [coeFn_pieceL2 M M.domain (fun _ => formComp (k := k) (w : FormField n))
    (fun _ _ s => continuous_formComp w.2 s) s, coeFn_formL2 hΩ M.isBounded_domain k w s,
    Feec.FiniteElement.ae_mem_interior M hΩ] with x h1 h2 hx
  obtain ⟨T, hT, hxT⟩ := hx
  rw [h1, h2, pieceFun_of_mem_interior M _ hT hxT]
  rfl

/-- `‖v‖ ≤ #ι · B` in `L²(Ω; ℝ^ι)` if every component has norm `≤ B`. -/
theorem L2F.norm_le_card_mul {Ω : Set (Fin n → ℝ)} {ι : Type*} [Fintype ι] (v : L2F ℝ Ω ι)
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ i, ‖v i‖ ≤ B) : ‖v‖ ≤ Fintype.card ι * B := by
  have hsq : ‖v‖ ^ 2 ≤ (Fintype.card ι * B) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : ι, B ^ 2 :=
          sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
      _ = Fintype.card ι * B ^ 2 := by simp
      _ ≤ (Fintype.card ι * B) ^ 2 := by
          rw [mul_pow]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
          · simp [h0]
          · have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast h0
            nlinarith
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

/-! ### The global interpolation error -/

theorem _root_.Feec.FiniteElement.LocalElement.glue_apply (E : LocalElement n)
    (M : SimplicialMesh n) (k : ℤ) (u : E.Piecewise M k.toNat) :
    E.glue M k u = pieceL2 M M.domain (fun T => formComp (k := k) (E.extendPW M u T))
      (fun _ hT s => continuous_formComp (E.contDiff_extendPW M u hT).continuous s) := rfl

section Global

variable (M : SimplicialMesh n) (hΩ : MeasurableSet M.domain)

/-- **Global `L²` interpolation error of the Whitney complex** ([Arnold2018], Ch. 7, classical
`C¹` form): on a mesh with `h_T ‖B_T⁻¹‖ ≤ C₀` and `h_T ≤ h` for every simplex, for a `C¹` form
`w` with `‖Dw‖ ≤ L` on `cl Ω`,
`‖w - Π_h w‖_{L²(Ω; Λᵏ)} ≤ #Λᵏ |Ω|^{1/2} C_{n,k} C₀^k h L`. -/
theorem norm_formL2_sub_glue_le (k : ℕ) {w : FormField n} (hw : ContDiff ℝ 1 w) {L C₀ h : ℝ}
    (hC₀ : 0 ≤ C₀) (hh0 : 0 ≤ h) (hL0 : 0 ≤ L) (hL : ∀ y ∈ closure M.domain, ‖fderiv ℝ w y‖ ≤ L)
    (hC : ∀ T ∈ M.simplices,
      diam T * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ≤ C₀)
    (hh : ∀ T ∈ M.simplices, diam T ≤ h) :
    ‖formL2 hΩ M.isBounded_domain k ⟨w, hw.continuous⟩ -
        (whitneyElement n).glue M k ((whitneyElement n).globalInterp M k ⟨w, hw.continuous⟩ :
          (whitneyElement n).Piecewise M k)‖ ≤
      Fintype.card (formIdx n k) * (volume.real M.domain ^ (1 / 2 : ℝ) *
        (whitneyConst n k * C₀ ^ k * (h * L))) := by
  have : IsFiniteMeasure (volume.restrict M.domain) :=
    isFiniteMeasure_restrict.2 M.isBounded_domain.measure_lt_top.ne
  set B := whitneyConst n k * C₀ ^ k * (h * L)
  -- the pointwise bound
  have hpt : ∀ T ∈ M.simplices, ∀ x ∈ interior T.closedInterior, ∀ s : Finset (Fin n), #s = k →
      |w x s - (whitneyInterp (isUnit_det_edgeMatrix T) k ⟨w, hw.continuous⟩ : FormField n) x s|
        ≤ B := by
    intro T hT x hx s hs
    have hxT := interior_subset hx
    have hTcl : T.closedInterior ⊆ closure M.domain := by
      rw [← M.biUnion_closedInterior]; exact Set.subset_biUnion_of_mem (u := fun T => T.closedInterior) hT
    refine (abs_sub_whitneyInterp_le T k hw (fun y hy => hL y (hTcl hy)) hxT hs).trans ?_
    have hD := diam_nonneg T
    have hS : 0 ≤ diam T * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ :=
      mul_nonneg hD (norm_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS (hC T hT) k)
      (whitneyConst_nonneg n k)) (mul_le_mul_of_nonneg_right (hh T hT) hL0) (by positivity)
      (by have := whitneyConst_nonneg n k; positivity)
  have hB : 0 ≤ B := by have := whitneyConst_nonneg n k; positivity
  rw [LocalElement.glue_apply]
  refine L2F.norm_le_card_mul _ (by positivity) fun s => ?_
  refine (Lp.norm_le_of_ae_bound hB ?_).trans (le_of_eq ?_)
  · set u : (whitneyElement n).Piecewise M k :=
      ((whitneyElement n).globalInterp M k ⟨w, hw.continuous⟩ : (whitneyElement n).Piecewise M k)
    have hcont : ∀ T ∈ M.simplices, ∀ s : formIdx n k,
        Continuous (formComp (k := (k : ℤ)) ((whitneyElement n).extendPW M u T) s) :=
      fun T hT s => continuous_formComp ((whitneyElement n).contDiff_extendPW M u hT).continuous s
    filter_upwards [Lp.coeFn_sub (formL2 hΩ M.isBounded_domain k ⟨w, hw.continuous⟩ s)
      (pieceL2 M M.domain (fun T => formComp (k := (k : ℤ)) ((whitneyElement n).extendPW M u T))
        hcont s), coeFn_formL2 hΩ M.isBounded_domain k ⟨w, hw.continuous⟩ s,
      coeFn_pieceL2 (𝕜 := ℝ) M M.domain _ hcont s, Feec.FiniteElement.ae_mem_interior M hΩ]
      with x h1 h2 h3 hx
    obtain ⟨T, hT, hxT⟩ := hx
    rw [PiLp.sub_apply, h1, Pi.sub_apply, h2, h3, pieceFun_of_mem_interior M _ hT hxT]
    change ‖w x s.1 - (whitneyElement n).extendPW M _ T x s.1‖ ≤ B
    rw [LocalElement.extendPW_of_mem _ _ _ hT, whitney_globalInterp_apply M k _ ⟨T, hT⟩,
      Real.norm_eq_abs]
    have hs : #s.1 = k := by exact_mod_cast s.2
    exact hpt T hT x hxT s.1 hs
  · rw [measureUnivNNReal, Measure.restrict_apply_univ, ENNReal.toReal_ofNat, one_div]
    rfl

/-- On a shape regular mesh (`Feec.Mesh.IsShapeRegular` with constants `C₀, c`), the shape bound
`h_T ‖B_T⁻¹‖ ≤ C₀` holds for every simplex. -/
theorem diam_mul_norm_symm_le_of_isShapeRegular {C₀ c : ℝ} (hC₀ : 0 ≤ C₀)
    (hreg : IsShapeRegular (↑M.simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)) C₀ c)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ M.simplices) :
    diam T * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ≤ C₀ := by
  have h := (hreg T hT).2.1
  rcases (diam_nonneg T).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]; exact hC₀
  · calc _ ≤ diam T * (C₀ / diam T) := mul_le_mul_of_nonneg_left h h0.le
      _ = C₀ := by field_simp

/-- **Global `L²` interpolation error on a shape regular mesh** ([Arnold2018], Ch. 7): with the
constants `C₀, c` of `Feec.Mesh.IsShapeRegular` and `h_T ≤ h`,
`‖w - Π_h w‖_{L²(Ω; Λᵏ)} ≤ #Λᵏ |Ω|^{1/2} C_{n,k} C₀^k h sup_{cl Ω} ‖Dw‖`. -/
theorem norm_formL2_sub_glue_le_of_isShapeRegular (k : ℕ) {w : FormField n}
    (hw : ContDiff ℝ 1 w) {L C₀ c h : ℝ} (hC₀ : 0 ≤ C₀) (hh0 : 0 ≤ h) (hL0 : 0 ≤ L)
    (hL : ∀ y ∈ closure M.domain, ‖fderiv ℝ w y‖ ≤ L)
    (hreg : IsShapeRegular (↑M.simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)) C₀ c)
    (hh : ∀ T ∈ M.simplices, diam T ≤ h) :
    ‖formL2 hΩ M.isBounded_domain k ⟨w, hw.continuous⟩ -
        (whitneyElement n).glue M k ((whitneyElement n).globalInterp M k ⟨w, hw.continuous⟩ :
          (whitneyElement n).Piecewise M k)‖ ≤
      Fintype.card (formIdx n k) * (volume.real M.domain ^ (1 / 2 : ℝ) *
        (whitneyConst n k * C₀ ^ k * (h * L))) :=
  norm_formL2_sub_glue_le M hΩ k hw hC₀ hh0 hL0 hL
    (fun _ hT => diam_mul_norm_symm_le_of_isShapeRegular M hC₀ hreg hT) hh

/-- `d` of a `C^{m+1}` form is `C^m`. -/
theorem contDiff_extDeriv {m : WithTop ℕ∞} {ω : FormField n} (hω : ContDiff ℝ (m + 1) ω) :
    ContDiff ℝ m (extDeriv ω) :=
  contDiff_pi.2 fun s => ContDiff.sum fun j _ =>
    contDiff_const.mul ((contDiff_pi.1 hω (s.erase j)).partialDeriv le_rfl j)

/-- **Smooth `k`-forms are in `D(d_max)`**: for a `C¹` form `w` of degree `k`, `w|_Ω ∈ HΛᵏ(Ω)`
with `d_max (w|_Ω) = (dw)|_Ω`. -/
theorem formL2_mem_maximal [NeZero n] (hΩo : IsOpen M.domain) (k : ℕ) {w : FormField n}
    (hw : ContDiff ℝ 1 w) (hdeg : ∀ x, IsDeg k (w x)) :
    ∃ h : formL2 hΩo.measurableSet M.isBounded_domain k ⟨w, hw.continuous⟩ ∈
        ((extDerivOp ℝ n k).maximal M.domain).domain,
      (extDerivOp ℝ n k).maximal M.domain ⟨_, h⟩ =
        formL2 hΩo.measurableSet M.isBounded_domain ((k : ℤ) + 1)
          ⟨extDeriv w, continuous_extDeriv hw⟩ := by
  obtain ⟨h, hval⟩ := extDeriv_pieceL2_mem_maximal_domain k M hΩo (η := fun _ => w)
    (fun _ _ => hw) (fun _ _ => hdeg) fun _ _ _ _ _ _ _ _ => fun _ _ => rfl
  have e1 := pieceL2_formComp_eq_formL2 M hΩo.measurableSet (k : ℤ) ⟨w, hw.continuous⟩
  have e2 := pieceL2_formComp_eq_formL2 M hΩo.measurableSet ((k : ℤ) + 1)
    ⟨extDeriv w, continuous_extDeriv hw⟩
  refine ⟨e1 ▸ h, ?_⟩
  rw [← e2, ← hval]
  congr 1
  exact Subtype.ext e1.symm

end Global

end Feec.FiniteElement
