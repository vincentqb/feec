module

public import Feec.FiniteElement.LumpedLaplacian
public import Feec.FiniteElement.P1Global
public import Feec.ForMathlib.Calculus.DirectionalSecondDifference

/-!
# Second-order nodal consistency of the lumped-mass `P₁` Laplacian

At a vertex `y` of a simplicial mesh `M` the lumped-mass `P₁` Laplacian is a difference operator
on the edges `[y, v]` of the simplices `T` at `y` (`neg_p1Stiffness_nodalIndicator`):
`m(y) (Lₕ U)(y) = Σ_T Σ_v ω_T(y, v) (U(v) - U(y))`, with the weights
`ω_T(y, v) = -|T| ∇φ_y · ∇φ_v` of the stiffness form (`vertexWeight`, `hatGrad`), which depend on
the vertices of `T` and not on their numbering (`p1Grad_congr_vertexSet`) and are nonnegative on
non-obtuse meshes.

It is consistent with the Laplacian, to second order, where the mesh is **translation invariant**
(`IsTranslationInvariantAt`): with every simplex `T` at `y`, the translates `T + (y - v)` that move
a vertex `v` of `T` to `y` are simplices of `M`, as at the vertices where `M` agrees with a lattice
triangulation, e.g. at the interior nodes of the Freudenthal meshes
(`isTranslationInvariantAt_freudenthalMesh`). Then

* the edges come in opposite pairs of equal weight (`sum_vertexWeight_mul_neg`): the translate
  of `T` moving the end `v` of the edge `[y, v]` to `y` has the edge `[y, y - (v - y)]`; so the
  odd terms of Taylor's formula cancel;
* the second moments of the edges are those of the Laplacian, `Σ ω (v - y)(v - y)ᵀ = 2 m(y) I`
  (`sum_vertexWeight_mul_mul`): by the energy identity of a simplex
  (`sum_sum_baryGrad_dotProduct_mul`, the element stiffness matrix applied to `zₐ z_b`), the
  edges of a simplex `T` at `y`, all of them, carry `2 |T| I`, and the translates of `T` moving
  each of its `n + 1` vertices to `y` count every edge at `y` once from each vertex.

Without translation invariance the lumped-mass Laplacian need not be consistent at all: on the
cross-polytope `{z | Σᵢ |zᵢ| < h}` meshed by its `2ⁿ` orthant simplices
`conv(0, ±h e₁, …, ±h eₙ)` (`crossMesh`, non-obtuse), with the single node `0`,
`(Lₕ U)(0) = -n (n + 1) U(0) / h²` (`lumpedLaplacianOn_crossMesh`).

## Main results

* **`abs_lumpedLaplacianOn_sub_laplacian_le`**: on a non-obtuse mesh translation invariant at a
  node `y = x i` (a vertex), for `u ∈ C⁴` vanishing at the vertices of the simplices at `y` that
  are not nodes, with `|D⁴u(z)(d, d, d, d)| ≤ B |d|⁴` on these simplices (`|d|` Euclidean),
  `|(Lₕ Iₕ u)(y) - Δu(y)| ≤ n B h² / 12` for every `h` bounding the Euclidean lengths of the
  edges at `y`.
* `isTranslationInvariantAt_freudenthalMesh`, `dotProduct_sub_le_freudenthalMesh`: the
  Freudenthal meshes are translation invariant at their interior nodes, with edges of length at
  most `√n` times the mesh size.
* **`abs_lumpedLaplacianOn_crossMesh_sub_laplacian`**: on the cross-polytope mesh, the quadratic
  `(|z|² - h²)/2`, which vanishes at the vertices other than `0` and has Laplacian `n`, has nodal
  consistency error `n (n - 1)/2` at `0`, for every `h`.

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
  (the lumped mass method)
* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MeasureTheory

@[expose] public noncomputable section

namespace Feec.FiniteElement

open Feec.Mesh

variable {n : ℕ}

/-! ### The energy identity of a simplex -/

/-- **Affine reproduction of the gradients**: `Σⱼ (pⱼ)ₐ ∇λⱼ = eₐ`, the gradient of the coordinate
`z ↦ zₐ`. -/
theorem sum_smul_baryGrad {p : Fin (n + 1) → Fin n → ℝ} (hp : IsUnit (edgeMatrix p).det)
    (a : Fin n) : ∑ j, p j a • baryGrad p j = Pi.single a 1 := by
  classical
  funext l
  have h1 := congrFun (sum_baryCoord_smul hp (Pi.single l 1)) a
  have h0 := congrFun (sum_baryCoord_smul hp 0) a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h0 ⊢
  have e : ∀ j, baryGrad p j l = baryCoord p (Pi.single l 1) j - baryCoord p 0 j := fun j => by
    rw [baryCoord_sub]
    simp [Pi.single_apply]
  have e1 : ∑ j, p j a * baryGrad p j l =
      ∑ j, baryCoord p (Pi.single l 1) j * p j a - ∑ j, baryCoord p 0 j * p j a := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [e]; ring
  rw [e1, h1, h0, sub_zero]
  simp [Pi.single_apply, eq_comm]

/-- `Σⱼ Σₖ (gⱼ · gₖ) cⱼ dₖ = (Σⱼ cⱼ gⱼ) · (Σₖ dₖ gₖ)`. -/
theorem sum_sum_dotProduct_mul_mul (g : Fin (n + 1) → Fin n → ℝ) (c d : Fin (n + 1) → ℝ) :
    ∑ j, ∑ k, (g j ⬝ᵥ g k) * (c j * d k) = (∑ j, c j • g j) ⬝ᵥ ∑ k, d k • g k := by
  rw [sum_dotProduct]
  refine sum_congr rfl fun j _ => ?_
  rw [dotProduct_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The energy identity of a simplex**:
`Σⱼ Σₖ (∇λⱼ · ∇λₖ) (pₖ - pⱼ)ₐ (pₖ - pⱼ)_b = -2 δₐ_b`, the element stiffness matrix applied to the
quadratic `zₐ z_b` (its rows sum to `0`, and `Σⱼ (pⱼ)ₐ ∇λⱼ = eₐ`). -/
theorem sum_sum_baryGrad_dotProduct_mul {p : Fin (n + 1) → Fin n → ℝ}
    (hp : IsUnit (edgeMatrix p).det) (a b : Fin n) :
    ∑ j, ∑ k, (baryGrad p j ⬝ᵥ baryGrad p k) * ((p k a - p j a) * (p k b - p j b)) =
      -2 * if a = b then 1 else 0 := by
  have hrow : ∀ j, ∑ k, baryGrad p j ⬝ᵥ baryGrad p k = 0 := fun j => by
    rw [← dotProduct_sum, sum_baryGrad, dotProduct_zero]
  have hcol : ∀ k, ∑ j, baryGrad p j ⬝ᵥ baryGrad p k = 0 := fun k => by
    rw [← sum_dotProduct, sum_baryGrad, zero_dotProduct]
  have e1 : ∑ j, ∑ k, (baryGrad p j ⬝ᵥ baryGrad p k) * (p k a * p k b) = 0 := by
    rw [sum_comm]
    exact sum_eq_zero fun k _ => by rw [← sum_mul, hcol, zero_mul]
  have e2 : ∑ j, ∑ k, (baryGrad p j ⬝ᵥ baryGrad p k) * (p j a * p j b) = 0 :=
    sum_eq_zero fun j _ => by rw [← sum_mul, hrow, zero_mul]
  have e3 : ∑ j, ∑ k, (baryGrad p j ⬝ᵥ baryGrad p k) * (p j b * p k a) =
      if a = b then 1 else 0 := by
    rw [sum_sum_dotProduct_mul_mul, sum_smul_baryGrad hp, sum_smul_baryGrad hp,
      dotProduct_single, Pi.single_apply, mul_one]
  have e4 : ∑ j, ∑ k, (baryGrad p j ⬝ᵥ baryGrad p k) * (p j a * p k b) =
      if a = b then 1 else 0 := by
    rw [sum_sum_dotProduct_mul_mul, sum_smul_baryGrad hp, sum_smul_baryGrad hp,
      dotProduct_single, Pi.single_apply, mul_one]
    simp only [eq_comm]
  have e : ∀ j k, (baryGrad p j ⬝ᵥ baryGrad p k) * ((p k a - p j a) * (p k b - p j b)) =
      (baryGrad p j ⬝ᵥ baryGrad p k) * (p k a * p k b) +
        (baryGrad p j ⬝ᵥ baryGrad p k) * (p j a * p j b) -
        (baryGrad p j ⬝ᵥ baryGrad p k) * (p j b * p k a) -
        (baryGrad p j ⬝ᵥ baryGrad p k) * (p j a * p k b) := fun j k => by ring
  simp_rw [e, sum_sub_distrib, sum_add_distrib]
  rw [e1, e2, e3, e4]
  ring

/-! ### Translates of simplices -/

/-- The translate `T + c` of the simplex `T`. -/
def translate (c : Fin n → ℝ) (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    Affine.Simplex ℝ (Fin n → ℝ) n :=
  mapEquiv (AffineEquiv.constVAdd ℝ (Fin n → ℝ) c) T

@[simp] theorem translate_points (c : Fin n → ℝ) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (k : Fin (n + 1)) : (translate c T).points k = c + T.points k := by
  simp [translate]

theorem translate_translate (c c' : Fin n → ℝ) (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    translate c (translate c' T) = translate (c + c') T :=
  Affine.Simplex.ext fun k => by simp [add_assoc]

@[simp] theorem translate_zero (T : Affine.Simplex ℝ (Fin n → ℝ) n) : translate 0 T = T :=
  Affine.Simplex.ext fun k => by simp

theorem baryGrad_translate (c : Fin n → ℝ) (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    baryGrad (translate c T).points = baryGrad T.points := by
  have : edgeMatrix (translate c T).points = edgeMatrix T.points := by
    ext i l
    simp [edgeMatrix, simplexMatrix]
  simp only [baryGrad, this]

theorem measureReal_closedInterior_translate (c : Fin n → ℝ)
    (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    volume.real (translate c T).closedInterior = volume.real T.closedInterior := by
  have e : ⇑(AffineEquiv.constVAdd ℝ (Fin n → ℝ) c) = (c + ·) := funext fun z => by simp
  rw [translate, closedInterior_mapEquiv, e, Set.image_add_left, measureReal_def, measureReal_def,
    measure_preimage_add]

/-- An `n`-simplex of `ℝⁿ` has positive volume. -/
theorem measureReal_closedInterior_pos (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    0 < volume.real T.closedInterior := by
  rw [measureReal_def]
  refine ENNReal.toReal_pos ?_ T.isCompact_closedInterior.measure_lt_top.ne
  exact ((isOpen_interior.measure_pos volume (interior_closedInterior_nonempty T)).trans_le
    (measure_mono interior_subset)).ne'

/-! ### Hat-function gradients, and their invariance under renumbering and translation -/

/-- **Barycentric gradients under a renumbering of the vertices**: `∇λ^{p ∘ π}ᵢ = ∇λ^p_{π i}`. -/
theorem baryGrad_comp_perm {p : Fin (n + 1) → Fin n → ℝ} (hp : IsUnit (edgeMatrix p).det)
    (π : Equiv.Perm (Fin (n + 1))) (hpπ : IsUnit (edgeMatrix (p ∘ π)).det) (i : Fin (n + 1)) :
    baryGrad (p ∘ π) i = baryGrad p (π i) := by
  classical
  funext l
  have h := baryCoord_sub (p ∘ π) (Pi.single l 1) 0 i
  rw [baryCoord_comp_perm hp π hpπ, baryCoord_comp_perm hp π hpπ, baryCoord_sub] at h
  simpa [Pi.single_apply] using h.symm

/-- Two simplices with the same vertices are renumberings of each other. -/
theorem exists_perm_of_vertexSet_eq {S S' : Affine.Simplex ℝ (Fin n → ℝ) n}
    (h : (vertexSet S : Set (Fin n → ℝ)) = vertexSet S') :
    ∃ π : Equiv.Perm (Fin (n + 1)), S'.points = S.points ∘ π := by
  have hr : Set.range S.points = Set.range S'.points := by
    rw [← coe_vertexSet, ← coe_vertexSet, h]
  have hmem : ∀ i, ∃ j, S.points j = S'.points i := fun i => by
    have : S'.points i ∈ Set.range S.points := by rw [hr]; exact Set.mem_range_self i
    exact this
  choose f hf using hmem
  have hinj : Function.Injective f := fun i i' e =>
    S'.independent.injective (by rw [← hf i, ← hf i', e])
  exact ⟨Equiv.ofBijective f hinj.bijective_of_finite, funext fun i => (hf i).symm⟩

/-- **The `P₁` gradient depends on the vertices only**, not on their numbering. -/
theorem p1Grad_congr_vertexSet {S S' : Affine.Simplex ℝ (Fin n → ℝ) n}
    (h : (vertexSet S : Set (Fin n → ℝ)) = vertexSet S') (u : (Fin n → ℝ) → ℝ) :
    p1Grad S.points u = p1Grad S'.points u := by
  obtain ⟨π, hπ⟩ := exists_perm_of_vertexSet_eq h
  have hS' := isUnit_det_edgeMatrix S'
  rw [hπ] at hS' ⊢
  rw [p1Grad_apply, p1Grad_apply]
  simp only [Function.comp_apply, baryGrad_comp_perm (isUnit_det_edgeMatrix S) π hS']
  exact (Equiv.sum_comp π fun i => u (S.points i) • baryGrad S.points i).symm

theorem p1Grad_translate (c : Fin n → ℝ) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (u : (Fin n → ℝ) → ℝ) :
    p1Grad (translate c T).points u = p1Grad T.points fun z => u (c + z) := by
  rw [p1Grad_apply, p1Grad_apply, baryGrad_translate]
  simp only [translate_points]

theorem coe_vertexSet_translate (c : Fin n → ℝ) (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    (vertexSet (translate c T) : Set (Fin n → ℝ)) = (· + c) '' vertexSet T := by
  rw [coe_vertexSet, coe_vertexSet]
  ext z
  simp only [Set.mem_range, Set.mem_image, translate_points]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, add_comm _ _⟩
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, add_comm _ _⟩

/-- The gradient `∇φᵥ` on the simplex `T` of the hat function of the point `v`: `∇λⱼ` if `v` is
the vertex `pⱼ` of `T` (`hatGrad_points`), `0` if `v` is no vertex of `T`. -/
def hatGrad (T : Affine.Simplex ℝ (Fin n → ℝ) n) (v : Fin n → ℝ) : Fin n → ℝ :=
  p1Grad T.points (nodalIndicator v)

theorem hatGrad_points (T : Affine.Simplex ℝ (Fin n → ℝ) n) (j : Fin (n + 1)) :
    hatGrad T (T.points j) = baryGrad T.points j :=
  p1Grad_nodalIndicator T.independent.injective j

theorem hatGrad_of_notMem {T : Affine.Simplex ℝ (Fin n → ℝ) n} {v : Fin n → ℝ}
    (hv : v ∉ vertexSet T) : hatGrad T v = 0 := by
  rw [hatGrad, p1Grad_apply]
  refine sum_eq_zero fun j _ => ?_
  rw [nodalIndicator, ite_eq_right_iff.2 fun e => absurd (mem_vertexSet.2 ⟨j, e⟩) hv, zero_smul]

/-- `∇Πₜw = Σᵥ w(v) ∇φᵥ` over the vertices `v` of `T`. -/
theorem p1Grad_eq_sum_hatGrad (T : Affine.Simplex ℝ (Fin n → ℝ) n) (w : (Fin n → ℝ) → ℝ) :
    p1Grad T.points w = ∑ v ∈ vertexSet T, w v • hatGrad T v := by
  classical
  have e : ∑ v ∈ vertexSet T, w v • hatGrad T v =
      p1Grad T.points (∑ v ∈ vertexSet T, w v • nodalIndicator v) := by
    simp only [hatGrad, map_sum, map_smul]
  rw [e, p1Grad_apply, p1Grad_apply]
  refine sum_congr rfl fun j _ => ?_
  congr 1
  rw [Finset.sum_apply, Finset.sum_eq_single (T.points j)]
  · simp [nodalIndicator]
  · intro v _ hv
    simp [nodalIndicator, Ne.symm hv]
  · exact fun h => absurd (points_mem_vertexSet T j) h

theorem sum_hatGrad (T : Affine.Simplex ℝ (Fin n → ℝ) n) : ∑ v ∈ vertexSet T, hatGrad T v = 0 := by
  have := p1Grad_eq_sum_hatGrad T fun _ => 1
  simp only [one_smul] at this
  rw [← this, p1Grad_apply]
  simp [sum_baryGrad]

variable {S T : Affine.Simplex ℝ (Fin n → ℝ) n} {c : Fin n → ℝ}

/-- **Hat-function gradients are invariant under translation**: if the vertices of `S` are those
of `T` translated by `c`, then `∇φ^S_{v + c} = ∇φ^T_v`. -/
theorem hatGrad_of_vertexSet_eq (h : (vertexSet S : Set (Fin n → ℝ)) = (· + c) '' vertexSet T)
    (v : Fin n → ℝ) : hatGrad S (v + c) = hatGrad T v := by
  rw [hatGrad, p1Grad_congr_vertexSet (h.trans (coe_vertexSet_translate c T).symm),
    p1Grad_translate, hatGrad]
  congr 1
  funext z
  simp only [nodalIndicator, add_comm c z, add_left_inj]

theorem measureReal_closedInterior_of_vertexSet_eq
    (h : (vertexSet S : Set (Fin n → ℝ)) = (· + c) '' vertexSet T) :
    volume.real S.closedInterior = volume.real T.closedInterior := by
  rw [← convexHull_vertexSet S, h, ← coe_vertexSet_translate, convexHull_vertexSet,
    measureReal_closedInterior_translate]

/-- The weight `-|T| ∇φᵥ · ∇φ_w` of the edge `[v, w]` of `T` in the stiffness form, nonnegative for
distinct vertices of a non-obtuse simplex (`vertexWeight_nonneg`). -/
def vertexWeight (T : Affine.Simplex ℝ (Fin n → ℝ) n) (v w : Fin n → ℝ) : ℝ :=
  -(volume.real T.closedInterior * (hatGrad T v ⬝ᵥ hatGrad T w))

theorem vertexWeight_of_vertexSet_eq
    (h : (vertexSet S : Set (Fin n → ℝ)) = (· + c) '' vertexSet T) (v w : Fin n → ℝ) :
    vertexWeight S (v + c) (w + c) = vertexWeight T v w := by
  simp only [vertexWeight, hatGrad_of_vertexSet_eq h, measureReal_closedInterior_of_vertexSet_eq h]

theorem vertexWeight_comm (T : Affine.Simplex ℝ (Fin n → ℝ) n) (v w : Fin n → ℝ) :
    vertexWeight T v w = vertexWeight T w v := by
  simp only [vertexWeight, dotProduct_comm]

theorem vertexWeight_of_notMem {v : Fin n → ℝ} (hv : v ∉ vertexSet T) (w : Fin n → ℝ) :
    vertexWeight T v w = 0 := by
  simp [vertexWeight, hatGrad_of_notMem hv]

theorem vertexWeight_nonneg {M : SimplicialMesh n} (hM : IsNonobtuse M) (hT : T ∈ M.simplices)
    {v w : Fin n → ℝ} (hv : v ∈ vertexSet T) (hw : w ∈ vertexSet T) (hvw : v ≠ w) :
    0 ≤ vertexWeight T v w := by
  obtain ⟨j, rfl⟩ := mem_vertexSet.1 hv
  obtain ⟨k, rfl⟩ := mem_vertexSet.1 hw
  rw [vertexWeight, hatGrad_points, hatGrad_points]
  exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos measureReal_nonneg
    (hM T hT j k fun e => hvw (by rw [e])))

theorem sum_vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) (f : (Fin n → ℝ) → ℝ) :
    ∑ v ∈ vertexSet T, f v = ∑ j, f (T.points j) := by
  rw [vertexSet]
  exact sum_image fun i _ j _ e => T.independent.injective e

/-- **The energy identity over the vertices**:
`Σᵥ Σ_w ω(v, w) (w - v)ₐ (w - v)_b = 2 |T| δₐ_b` (`sum_sum_baryGrad_dotProduct_mul`). -/
theorem sum_sum_vertexWeight_mul (T : Affine.Simplex ℝ (Fin n → ℝ) n) (a b : Fin n) :
    ∑ v ∈ vertexSet T, ∑ w ∈ vertexSet T, vertexWeight T v w * ((w - v) a * (w - v) b) =
      2 * volume.real T.closedInterior * if a = b then 1 else 0 := by
  rw [sum_vertexSet]
  simp_rw [sum_vertexSet]
  have e : ∀ j k, vertexWeight T (T.points j) (T.points k) *
      ((T.points k - T.points j) a * (T.points k - T.points j) b) =
      -volume.real T.closedInterior * ((baryGrad T.points j ⬝ᵥ baryGrad T.points k) *
        ((T.points k a - T.points j a) * (T.points k b - T.points j b))) := fun j k => by
    rw [vertexWeight, hatGrad_points, hatGrad_points, Pi.sub_apply, Pi.sub_apply]
    ring
  simp only [e, ← mul_sum, sum_sum_baryGrad_dotProduct_mul (isUnit_det_edgeMatrix T) a b]
  ring

/-! ### The lumped-mass Laplacian at a vertex as a difference operator -/

variable (M : SimplicialMesh n) (y : Fin n → ℝ)

open Classical in
/-- The **star** of `y`: the simplices of `M` with vertex `y`. -/
def star : Finset (Affine.Simplex ℝ (Fin n → ℝ) n) :=
  M.simplices.filter fun T => y ∈ vertexSet T

variable {M y}

theorem mem_star : T ∈ star M y ↔ T ∈ M.simplices ∧ y ∈ vertexSet T := by
  classical
  simp [star]

variable (M y)

/-- The lumped mass over the star: `m(y) = Σ_{T ∋ y} |T| / (n + 1)`. -/
theorem lumpedMass_eq_sum_star :
    lumpedMass M y = ∑ T ∈ star M y, volume.real T.closedInterior / (n + 1) := by
  classical
  rw [lumpedMass, star, sum_filter]
  refine sum_congr rfl fun T _ => ?_
  split_ifs with hy
  · obtain ⟨j, hj⟩ := mem_vertexSet.1 hy
    have : (univ.filter fun i => T.points i = y) = {j} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun hi => T.independent.injective (hi.trans hj.symm), fun hi => hi ▸ hj⟩
    rw [this, card_singleton, Nat.cast_one, mul_one]
  · have : (univ.filter fun i => T.points i = y) = ∅ :=
      filter_eq_empty_iff.2 fun i _ hi => hy (mem_vertexSet.2 ⟨i, hi⟩)
    rw [this, card_empty, Nat.cast_zero, mul_zero]

/-- **The lumped-mass Laplacian at a vertex is a difference operator**:
`-a(φ_y, w) = Σ_{T ∋ y} Σᵥ ω_T(y, v) (w(v) - w(y))` over the vertices `v` of the simplices `T` at
`y`, `ω_T = vertexWeight T`; so `m(y) (Lₕ U)(y) = Σ ω (U(v) - U(y))`. -/
theorem neg_p1Stiffness_nodalIndicator (w : (Fin n → ℝ) → ℝ) :
    -p1Stiffness M (nodalIndicator y) w =
      ∑ T ∈ star M y, ∑ v ∈ vertexSet T, vertexWeight T y v * (w v - w y) := by
  classical
  have h1 : ∀ T : Affine.Simplex ℝ (Fin n → ℝ) n,
      -(volume.real T.closedInterior *
        (p1Grad T.points (nodalIndicator y) ⬝ᵥ p1Grad T.points w)) =
      ∑ v ∈ vertexSet T, vertexWeight T y v * (w v - w y) := fun T => by
    have hs : ∑ v ∈ vertexSet T, vertexWeight T y v = 0 := by
      simp only [vertexWeight]
      rw [sum_neg_distrib, ← mul_sum, ← dotProduct_sum, sum_hatGrad, dotProduct_zero, mul_zero,
        neg_zero]
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hs, zero_mul, sub_zero]
    rw [p1Grad_eq_sum_hatGrad T w, dotProduct_sum, mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun v _ => ?_
    rw [dotProduct_smul, smul_eq_mul]
    simp only [vertexWeight, hatGrad]
    ring
  rw [p1Stiffness_eq, ← sum_neg_distrib, star, sum_filter_of_ne]
  · exact sum_congr rfl fun T _ => h1 T
  · intro T _ hne
    by_contra hy
    exact hne (sum_eq_zero fun v _ => by rw [vertexWeight_of_notMem hy, zero_mul])

/-! ### Translation invariance -/

/-- The mesh `M` is **translation invariant at** `y`: for every simplex `T` of `M` with vertex
`y` and every vertex `v` of `T`, the translate `T + (y - v)`, which moves `v` to `y`, is a simplex
of `M` (`M` has a simplex with these vertices, in any numbering). It holds at a vertex where `M`
agrees with a lattice triangulation (a triangulation invariant under the translations by the
differences of its vertices), e.g. at the interior nodes of the Freudenthal meshes
(`isTranslationInvariantAt_freudenthalMesh`). -/
def IsTranslationInvariantAt (M : SimplicialMesh n) (y : Fin n → ℝ) : Prop :=
  ∀ T ∈ M.simplices, y ∈ vertexSet T → ∀ v ∈ vertexSet T, ∃ S ∈ M.simplices,
    (vertexSet S : Set (Fin n → ℝ)) = (· + (y - v)) '' vertexSet T

open Classical in
/-- The simplex of `M` with the vertices of `T + c`, if there is one (`T` otherwise). -/
def reroot (M : SimplicialMesh n) (T : Affine.Simplex ℝ (Fin n → ℝ) n) (c : Fin n → ℝ) :
    Affine.Simplex ℝ (Fin n → ℝ) n :=
  if h : ∃ S ∈ M.simplices, (vertexSet S : Set (Fin n → ℝ)) = (· + c) '' vertexSet T then
    h.choose else T

variable {M y}

theorem reroot_spec
    (h : ∃ S ∈ M.simplices, (vertexSet S : Set (Fin n → ℝ)) = (· + c) '' vertexSet T) :
    reroot M T c ∈ M.simplices ∧
      (vertexSet (reroot M T c) : Set (Fin n → ℝ)) = (· + c) '' vertexSet T := by
  rw [reroot]
  split_ifs
  exact h.choose_spec

/-- The simplex of `M` with given vertices is unique. -/
theorem reroot_eq (hS : S ∈ M.simplices)
    (hV : (vertexSet S : Set (Fin n → ℝ)) = (· + c) '' vertexSet T) : reroot M T c = S := by
  obtain ⟨h1, h2⟩ := reroot_spec ⟨S, hS, hV⟩
  exact M.vertexSet_injOn h1 hS (Finset.coe_injective (h2.trans hV.symm))

/-- The vertices of `T + c` translate back to those of `T`. -/
theorem image_add_neg_image_add (V : Set (Fin n → ℝ)) (c : Fin n → ℝ) :
    (· + -c) '' ((· + c) '' V) = V := by
  rw [Set.image_image]
  simp

theorem mem_vertexSet_reroot (hT : IsTranslationInvariantAt M y) (hTM : T ∈ M.simplices)
    (hyT : y ∈ vertexSet T) {v : Fin n → ℝ} (hv : v ∈ vertexSet T) {z : Fin n → ℝ} :
    z ∈ vertexSet (reroot M T (y - v)) ↔ z - (y - v) ∈ vertexSet T := by
  rw [← Finset.mem_coe, (reroot_spec (hT T hTM hyT v hv)).2, Set.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [add_sub_cancel_right]
    exact hw
  · exact fun hz => ⟨_, hz, by abel⟩

/-- `reroot` undone: the simplex with the vertices of `reroot M T (y - v)` translated back is
`T`. -/
theorem reroot_reroot (hT : IsTranslationInvariantAt M y) (hTM : T ∈ M.simplices)
    (hyT : y ∈ vertexSet T) {v : Fin n → ℝ} (hv : v ∈ vertexSet T) :
    reroot M (reroot M T (y - v)) (-(y - v)) = T := by
  refine reroot_eq hTM ?_
  rw [(reroot_spec (hT T hTM hyT v hv)).2, image_add_neg_image_add]

/-- **Opposite edges** (translation invariance at `y`): the simplex with the vertices of `T`
translated by `y - v` has the edge `[y, y - (v - y)]`, with the weight of `[y, v]` in `T`; so
`Σ ω f(v - y) = Σ ω f(y - v)` over the edges `[y, v]` of the star. -/
theorem sum_vertexWeight_mul_neg (hT : IsTranslationInvariantAt M y) (f : (Fin n → ℝ) → ℝ) :
    ∑ T ∈ star M y, ∑ v ∈ vertexSet T, vertexWeight T y v * f (v - y) =
      ∑ T ∈ star M y, ∑ v ∈ vertexSet T, vertexWeight T y v * f (-(v - y)) := by
  classical
  rw [sum_sigma', sum_sigma']
  have hmem : ∀ p ∈ (star M y).sigma vertexSet,
      (⟨reroot M p.1 (y - p.2), y + (y - p.2)⟩ :
        (_ : Affine.Simplex ℝ (Fin n → ℝ) n) × (Fin n → ℝ)) ∈ (star M y).sigma vertexSet := by
    rintro ⟨T, v⟩ hp
    rw [mem_sigma, mem_star] at hp
    obtain ⟨⟨hTM, hyT⟩, hv⟩ := hp
    rw [mem_sigma, mem_star]
    refine ⟨⟨(reroot_spec (hT T hTM hyT v hv)).1, ?_⟩, ?_⟩
    · rw [mem_vertexSet_reroot hT hTM hyT hv]
      simpa using hv
    · rw [mem_vertexSet_reroot hT hTM hyT hv]
      simpa using hyT
  have hinv : ∀ p ∈ (star M y).sigma vertexSet,
      (⟨reroot M (reroot M p.1 (y - p.2)) (y - (y + (y - p.2))), y + (y - (y + (y - p.2)))⟩ :
        (_ : Affine.Simplex ℝ (Fin n → ℝ) n) × (Fin n → ℝ)) = p := by
    rintro ⟨T, v⟩ hp
    rw [mem_sigma, mem_star] at hp
    obtain ⟨⟨hTM, hyT⟩, hv⟩ := hp
    have e1 : y - (y + (y - v)) = -(y - v) := by abel
    have e2 : y + -(y - v) = v := by abel
    simp only [e1, e2, reroot_reroot hT hTM hyT hv]
  refine sum_nbij' (fun p => ⟨reroot M p.1 (y - p.2), y + (y - p.2)⟩)
    (fun p => ⟨reroot M p.1 (y - p.2), y + (y - p.2)⟩) hmem hmem hinv hinv ?_
  rintro ⟨T, v⟩ hp
  rw [mem_sigma, mem_star] at hp
  obtain ⟨⟨hTM, hyT⟩, hv⟩ := hp
  have hw := vertexWeight_of_vertexSet_eq (reroot_spec (hT T hTM hyT v hv)).2 v y
  rw [add_sub_cancel] at hw
  simp only [hw, vertexWeight_comm T v y]
  congr 2
  abel

/-- **The second moments of the edges at `y`** (translation invariance at `y`):
`Σ ω (v - y)ₐ (v - y)_b = 2 m(y) δₐ_b` over the edges `[y, v]` of the star. By the energy identity
(`sum_sum_vertexWeight_mul`) all the edges of a simplex `T` together give `2 |T| δₐ_b`; the
translates of `T` moving each of its `n + 1` vertices to `y` count every edge at `y` once from
each vertex. -/
theorem sum_vertexWeight_mul_mul (hT : IsTranslationInvariantAt M y) (a b : Fin n) :
    ∑ T ∈ star M y, ∑ v ∈ vertexSet T, vertexWeight T y v * ((v - y) a * (v - y) b) =
      2 * lumpedMass M y * if a = b then 1 else 0 := by
  classical
  set Q := (star M y).sigma fun T => vertexSet T ×ˢ vertexSet T with hQ
  have hQmem : ∀ {q : (_ : Affine.Simplex ℝ (Fin n → ℝ) n) × ((Fin n → ℝ) × (Fin n → ℝ))},
      q ∈ Q ↔ (q.1 ∈ M.simplices ∧ y ∈ vertexSet q.1) ∧ q.2.1 ∈ vertexSet q.1 ∧
        q.2.2 ∈ vertexSet q.1 := by
    intro q
    rw [hQ, mem_sigma, mem_star, mem_product]
  have h1 : ∑ q ∈ Q, vertexWeight q.1 q.2.1 q.2.2 * ((q.2.2 - q.2.1) a * (q.2.2 - q.2.1) b) =
      ∑ T ∈ star M y, 2 * volume.real T.closedInterior * if a = b then 1 else 0 := by
    rw [sum_sigma]
    refine sum_congr rfl fun T _ => ?_
    rw [sum_product]
    exact sum_sum_vertexWeight_mul T a b
  have h2 : ∑ q ∈ Q, vertexWeight q.1 q.2.1 q.2.2 * ((q.2.2 - q.2.1) a * (q.2.2 - q.2.1) b) =
      ∑ q ∈ Q, vertexWeight q.1 y q.2.1 * ((q.2.1 - y) a * (q.2.1 - y) b) := by
    refine sum_nbij'
      (fun q => ⟨reroot M q.1 (y - q.2.1), (q.2.2 + (y - q.2.1), y + (y - q.2.1))⟩)
      (fun q => ⟨reroot M q.1 (y - q.2.2), (y + (y - q.2.2), q.2.1 + (y - q.2.2))⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨T, v, w⟩ hq
      obtain ⟨⟨hTM, hyT⟩, hv, hw⟩ := hQmem.1 hq
      refine hQmem.2 ⟨⟨(reroot_spec (hT T hTM hyT v hv)).1, ?_⟩, ?_, ?_⟩ <;>
        simp only [mem_vertexSet_reroot hT hTM hyT hv]
      · simpa using hv
      · simpa using hw
      · simpa using hyT
    · rintro ⟨T, v, w⟩ hq
      obtain ⟨⟨hTM, hyT⟩, hv, hw⟩ := hQmem.1 hq
      refine hQmem.2 ⟨⟨(reroot_spec (hT T hTM hyT w hw)).1, ?_⟩, ?_, ?_⟩ <;>
        simp only [mem_vertexSet_reroot hT hTM hyT hw]
      · simpa using hw
      · simpa using hyT
      · simpa using hv
    · rintro ⟨T, v, w⟩ hq
      obtain ⟨⟨hTM, hyT⟩, hv, hw⟩ := hQmem.1 hq
      have e1 : y - (y + (y - v)) = -(y - v) := by abel
      have e2 : y + -(y - v) = v := by abel
      have e3 : w + (y - v) + -(y - v) = w := by abel
      simp only [e1, e2, e3, reroot_reroot hT hTM hyT hv]
    · rintro ⟨T, v, w⟩ hq
      obtain ⟨⟨hTM, hyT⟩, hv, hw⟩ := hQmem.1 hq
      have e1 : y - (y + (y - w)) = -(y - w) := by abel
      have e2 : v + (y - w) + -(y - w) = v := by abel
      have e3 : y + -(y - w) = w := by abel
      simp only [e1, e2, e3, reroot_reroot hT hTM hyT hw]
    · rintro ⟨T, v, w⟩ hq
      obtain ⟨⟨hTM, hyT⟩, hv, hw⟩ := hQmem.1 hq
      have hwt := vertexWeight_of_vertexSet_eq (reroot_spec (hT T hTM hyT v hv)).2 v w
      rw [add_sub_cancel] at hwt
      have e : w + (y - v) - y = w - v := by abel
      simp only [hwt, e]
  have h3 : ∑ q ∈ Q, vertexWeight q.1 y q.2.1 * ((q.2.1 - y) a * (q.2.1 - y) b) =
      (n + 1) * ∑ T ∈ star M y, ∑ v ∈ vertexSet T,
        vertexWeight T y v * ((v - y) a * (v - y) b) := by
    rw [sum_sigma, mul_sum]
    refine sum_congr rfl fun T _ => ?_
    rw [sum_product, mul_sum]
    refine sum_congr rfl fun v _ => ?_
    simp only [sum_const, card_vertexSet, nsmul_eq_mul]
    push_cast
    ring
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [← mul_right_inj' hn.ne', ← h3, ← h2, h1, lumpedMass_eq_sum_star, mul_sum, sum_mul, mul_sum]
  refine sum_congr rfl fun T _ => ?_
  field_simp

/-! ### Second-order consistency -/

/-- **Second-order nodal consistency of the lumped-mass `P₁` Laplacian where the mesh is
translation invariant**: let `M` be non-obtuse, `x : ι → ℝⁿ` injective nodes and `y = x i` a
vertex of `M` at which `M` is translation invariant. For `u ∈ C⁴` vanishing at the vertices of
the simplices at `y` that are not nodes, with `|D⁴u(z)(d, d, d, d)| ≤ B |d|⁴` on these simplices
(`|d|² = d · d`), and `h` bounding the Euclidean lengths of the edges at `y`,
`|(Lₕ Iₕ u)(y) - Δu(y)| ≤ n B h² / 12`: the odd Taylor terms cancel on opposite edges
(`sum_vertexWeight_mul_neg`), the second moments are those of the Laplacian
(`sum_vertexWeight_mul_mul`), and the second difference along each edge is
`D²u(y)(d, d) + O(|d|⁴)` (`abs_secondDiff_sub_iteratedFDeriv_le`), with nonnegative weights.
[Thomee2006], Ch. 15 -/
theorem abs_lumpedLaplacianOn_sub_laplacian_le {ι : Type*} [Fintype ι] {x : ι → Fin n → ℝ}
    (hM : IsNonobtuse M) (hx : Function.Injective x) {i : ι}
    (hv : ∃ T ∈ M.simplices, x i ∈ vertexSet T) (hT : IsTranslationInvariantAt M (x i))
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 4 u) {B h : ℝ}
    (hbd : ∀ T ∈ M.simplices, x i ∈ vertexSet T → ∀ v ∈ vertexSet T, v ∉ Set.range x → u v = 0)
    (hh : ∀ T ∈ M.simplices, x i ∈ vertexSet T → ∀ v ∈ vertexSet T,
      (v - x i) ⬝ᵥ (v - x i) ≤ h ^ 2)
    (hB : ∀ T ∈ M.simplices, x i ∈ vertexSet T → ∀ z ∈ T.closedInterior, ∀ d,
      |iteratedFDeriv ℝ 4 u z (fun _ => d)| ≤ B * (d ⬝ᵥ d) ^ 2) :
    |lumpedLaplacianOn M x (fun q => u (x q)) i - laplacian u (x i)| ≤ n * B * h ^ 2 / 12 := by
  classical
  have hm : 0 < lumpedMass M (x i) := by
    obtain ⟨T, hTM, hyT⟩ := hv
    rw [lumpedMass_eq_sum_star]
    exact sum_pos' (fun T _ => div_nonneg measureReal_nonneg (by positivity))
      ⟨T, mem_star.2 ⟨hTM, hyT⟩, div_pos (measureReal_closedInterior_pos T) (by positivity)⟩
  -- the stencil: `m (Lₕ Iₕ u)(y) = Σ ω (u(y + d) - u(y))`
  have h1 : lumpedMass M (x i) * lumpedLaplacianOn M x (fun q => u (x q)) i =
      ∑ T ∈ star M (x i), ∑ v ∈ vertexSet T,
        vertexWeight T (x i) v * (u (x i + (v - x i)) - u (x i)) := by
    rw [lumpedLaplacianOn_apply, mul_div_assoc', mul_div_cancel_left₀ _ hm.ne',
      neg_p1Stiffness_nodalIndicator, nodalFun_apply hx]
    refine sum_congr rfl fun T hT' => sum_congr rfl fun v hvT => ?_
    obtain ⟨hTM, hyT⟩ := mem_star.1 hT'
    rw [add_sub_cancel]
    congr 2
    by_cases hr : v ∈ Set.range x
    · obtain ⟨q, rfl⟩ := hr
      rw [nodalFun_apply hx]
    · rw [hbd T hTM hyT v hvT hr]
      exact sum_eq_zero fun q _ => ite_eq_right_iff.2 fun e => absurd ⟨q, e⟩ hr
  -- opposite edges
  have h2 : ∑ T ∈ star M (x i), ∑ v ∈ vertexSet T,
        vertexWeight T (x i) v * (u (x i + (v - x i)) - u (x i)) =
      ∑ T ∈ star M (x i), ∑ v ∈ vertexSet T,
        vertexWeight T (x i) v * (u (x i - (v - x i)) - u (x i)) := by
    simpa [sub_eq_add_neg] using sum_vertexWeight_mul_neg hT fun d => u (x i + d) - u (x i)
  -- the second moments
  set H : Fin n → Fin n → ℝ := fun a b =>
    fderiv ℝ (fderiv ℝ u) (x i) (Pi.single a 1) (Pi.single b 1) with hH
  have hQ : ∀ w : Fin n → ℝ,
      iteratedFDeriv ℝ 2 u (x i) (fun _ => w) = ∑ a, ∑ b, H a b * (w a * w b) := by
    intro w
    rw [iteratedFDeriv_two_apply]
    have hw : w = ∑ a, w a • Pi.single a (1 : ℝ) := by
      funext l
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hw]
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, mul_sum, H]
    rw [sum_comm]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have hΔ : laplacian u (x i) = ∑ a, H a a := by
    have hd : DifferentiableAt ℝ (fderiv ℝ u) (x i) :=
      (hu.fderiv_right (m := 3) (by norm_num)).differentiable (by norm_num) _
    rw [laplacian_apply]
    exact sum_congr rfl fun a _ => partialDeriv_partialDeriv hd a a
  have h3 : ∑ T ∈ star M (x i), ∑ v ∈ vertexSet T, vertexWeight T (x i) v *
        iteratedFDeriv ℝ 2 u (x i) (fun _ => v - x i) =
      2 * lumpedMass M (x i) * laplacian u (x i) := by
    have e : ∀ T ∈ star M (x i), ∑ v ∈ vertexSet T, vertexWeight T (x i) v *
        iteratedFDeriv ℝ 2 u (x i) (fun _ => v - x i) = ∑ a, ∑ b, H a b *
          ∑ v ∈ vertexSet T, vertexWeight T (x i) v * ((v - x i) a * (v - x i) b) := fun T _ => by
      simp only [hQ, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun a _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun b _ => sum_congr rfl fun v _ => by ring
    calc ∑ T ∈ star M (x i), ∑ v ∈ vertexSet T, vertexWeight T (x i) v *
          iteratedFDeriv ℝ 2 u (x i) (fun _ => v - x i)
        = ∑ a, ∑ b, H a b * ∑ T ∈ star M (x i), ∑ v ∈ vertexSet T, vertexWeight T (x i) v *
            ((v - x i) a * (v - x i) b) := by
          rw [sum_congr rfl e, sum_comm]
          refine sum_congr rfl fun a _ => ?_
          rw [sum_comm]
          exact sum_congr rfl fun b _ => (mul_sum _ _ _).symm
      _ = ∑ a, ∑ b, H a b * (2 * lumpedMass M (x i) * if a = b then 1 else 0) := by
          simp_rw [sum_vertexWeight_mul_mul hT]
      _ = 2 * lumpedMass M (x i) * laplacian u (x i) := by
          rw [hΔ, mul_sum]
          refine sum_congr rfl fun a _ => ?_
          simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
          ring
  -- the second difference along each edge
  have h4 : ∀ T ∈ star M (x i), ∀ v ∈ vertexSet T,
      |vertexWeight T (x i) v * (u (x i + (v - x i)) - 2 * u (x i) + u (x i - (v - x i)) -
          iteratedFDeriv ℝ 2 u (x i) (fun _ => v - x i))| ≤
        B * h ^ 2 / 12 * (vertexWeight T (x i) v * ((v - x i) ⬝ᵥ (v - x i))) := by
    intro T hT' v hvT
    obtain ⟨hTM, hyT⟩ := mem_star.1 hT'
    have hyc : x i ∈ T.closedInterior := by
      rw [← convexHull_vertexSet]
      exact subset_convexHull ℝ _ (Finset.mem_coe.2 hyT)
    have hvc : v ∈ T.closedInterior := by
      rw [← convexHull_vertexSet]
      exact subset_convexHull ℝ _ (Finset.mem_coe.2 hvT)
    by_cases hvy : v = x i
    · rw [hvy, sub_self]
      have h0 : iteratedFDeriv ℝ 2 u (x i) (fun _ => (0 : Fin n → ℝ)) = 0 :=
        (iteratedFDeriv ℝ 2 u (x i)).map_coord_zero 0 rfl
      have hz : u (x i) - 2 * u (x i) + u (x i) = 0 := by ring
      simp [h0, hz]
    · have hω := vertexWeight_nonneg hM hTM hyT hvT (Ne.symm hvy)
      set d := v - x i with hd
      have hdd := hh T hTM hyT v hvT
      have hdd0 : 0 ≤ d ⬝ᵥ d := by
        simp only [dotProduct]
        exact sum_nonneg fun _ _ => mul_self_nonneg _
      have hseg : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
          |iteratedFDeriv ℝ 4 u (x i + t • d) (fun _ => d)| ≤ B * (d ⬝ᵥ d) ^ 2 := by
        intro t ht
        rcases le_total 0 t with h0 | h0
        · exact hB T hTM hyT _ ((convex_closedInterior T).add_smul_sub_mem hyc hvc ⟨h0, ht.2⟩) d
        · set R := reroot M T (x i - v) with hR
          have hRM := (reroot_spec (hT T hTM hyT v hvT)).1
          have hyR : x i ∈ vertexSet R := by
            rw [hR, mem_vertexSet_reroot hT hTM hyT hvT]
            simpa using hvT
          have hy'R : x i - d ∈ vertexSet R := by
            rw [hR, mem_vertexSet_reroot hT hTM hyT hvT, hd]
            simpa [sub_sub] using hyT
          have hyRc : x i ∈ R.closedInterior := by
            rw [← convexHull_vertexSet]
            exact subset_convexHull ℝ _ (Finset.mem_coe.2 hyR)
          have hy'Rc : x i - d ∈ R.closedInterior := by
            rw [← convexHull_vertexSet]
            exact subset_convexHull ℝ _ (Finset.mem_coe.2 hy'R)
          have hmem := (convex_closedInterior R).add_smul_sub_mem hyRc hy'Rc
            (show -t ∈ Set.Icc (0 : ℝ) 1 from ⟨by linarith, by linarith [ht.1]⟩)
          rw [sub_sub_cancel_left, smul_neg, neg_smul, neg_neg] at hmem
          exact hB R hRM hyR _ hmem d
      have hR := abs_secondDiff_sub_iteratedFDeriv_le hu (x i) d hseg
      have hB0 : B * (d ⬝ᵥ d) ^ 2 ≤ B * h ^ 2 * (d ⬝ᵥ d) := by
        have h0 : 0 ≤ B * (d ⬝ᵥ d) ^ 2 := (abs_nonneg _).trans (hB T hTM hyT _ hyc d)
        rcases hdd0.eq_or_lt with he | hlt
        · rw [← he]; simp
        · have hB' : 0 ≤ B := by
            by_contra hneg
            have : B * (d ⬝ᵥ d) ^ 2 < 0 :=
              mul_neg_of_neg_of_pos (lt_of_not_ge hneg) (by positivity)
            linarith
          have := mul_le_mul_of_nonneg_left hdd (mul_nonneg hB' hdd0)
          nlinarith
      rw [abs_mul, abs_of_nonneg hω]
      calc vertexWeight T (x i) v * |u (x i + d) - 2 * u (x i) + u (x i - d) -
            iteratedFDeriv ℝ 2 u (x i) (fun _ => d)|
          ≤ vertexWeight T (x i) v * (B * (d ⬝ᵥ d) ^ 2 / 12) := mul_le_mul_of_nonneg_left hR hω
        _ ≤ B * h ^ 2 / 12 * (vertexWeight T (x i) v * (d ⬝ᵥ d)) := by nlinarith
  -- combine
  have h5 : 2 * lumpedMass M (x i) *
        (lumpedLaplacianOn M x (fun q => u (x q)) i - laplacian u (x i)) =
      ∑ T ∈ star M (x i), ∑ v ∈ vertexSet T, vertexWeight T (x i) v *
        (u (x i + (v - x i)) - 2 * u (x i) + u (x i - (v - x i)) -
          iteratedFDeriv ℝ 2 u (x i) (fun _ => v - x i)) := by
    have e : 2 * (lumpedMass M (x i) * lumpedLaplacianOn M x (fun q => u (x q)) i) =
        (∑ T ∈ star M (x i), ∑ v ∈ vertexSet T,
          vertexWeight T (x i) v * (u (x i + (v - x i)) - u (x i))) +
        ∑ T ∈ star M (x i), ∑ v ∈ vertexSet T,
          vertexWeight T (x i) v * (u (x i - (v - x i)) - u (x i)) := by
      rw [h1, two_mul, h2]
    calc 2 * lumpedMass M (x i) *
          (lumpedLaplacianOn M x (fun q => u (x q)) i - laplacian u (x i))
        = 2 * (lumpedMass M (x i) * lumpedLaplacianOn M x (fun q => u (x q)) i) -
            2 * lumpedMass M (x i) * laplacian u (x i) := by ring
      _ = _ := by
          rw [e, ← h3, ← sum_add_distrib, ← sum_sub_distrib]
          refine sum_congr rfl fun T _ => ?_
          rw [← sum_add_distrib, ← sum_sub_distrib]
          exact sum_congr rfl fun v _ => by ring
  have h6 : ∑ T ∈ star M (x i), ∑ v ∈ vertexSet T, vertexWeight T (x i) v *
        ((v - x i) ⬝ᵥ (v - x i)) = 2 * lumpedMass M (x i) * n := by
    have e : ∀ T ∈ star M (x i), ∑ v ∈ vertexSet T, vertexWeight T (x i) v *
        ((v - x i) ⬝ᵥ (v - x i)) = ∑ a, ∑ v ∈ vertexSet T, vertexWeight T (x i) v *
          ((v - x i) a * (v - x i) a) := fun T _ => by
      simp only [dotProduct, mul_sum]
      exact sum_comm
    rw [sum_congr rfl e, sum_comm]
    simp only [sum_vertexWeight_mul_mul hT, ↓reduceIte, mul_one, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hpos : (0 : ℝ) < 2 * lumpedMass M (x i) := by positivity
  refine le_of_mul_le_mul_left ?_ hpos
  rw [← abs_of_pos hpos, ← abs_mul, h5]
  calc _ ≤ ∑ T ∈ star M (x i), ∑ v ∈ vertexSet T, B * h ^ 2 / 12 * (vertexWeight T (x i) v *
          ((v - x i) ⬝ᵥ (v - x i))) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun T hT' =>
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v hv => h4 T hT' v hv))
    _ = |2 * lumpedMass M (x i)| * (n * B * h ^ 2 / 12) := by
        simp_rw [← mul_sum]
        rw [h6, abs_of_pos hpos]
        ring

/-! ### The Freudenthal meshes -/

/-- **The Freudenthal meshes are translation invariant at their interior nodes**: the translate of
a simplex `b + h (m + K_σ)` moving its vertex `b + h (m + vⱼ)` to an interior node `b + h q` is
the simplex `b + h (q - vⱼ + K_σ)` of the mesh. -/
theorem isTranslationInvariantAt_freudenthalMesh (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ)
    {q : Fin n → ℤ} (hq : q ∈ interiorNodes n (N + 1)) :
    IsTranslationInvariantAt (freudenthalMesh b s hs (N + 1)) (node b (s / (N + 1 : ℕ)) q) := by
  intro T hT _ v hv
  obtain ⟨j, rfl⟩ := mem_vertexSet.1 hv
  refine ⟨_, ?_, (coe_vertexSet_translate _ T).trans (by rfl)⟩
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  have hq' := mem_interiorNodes.1 hq
  have hm : ∀ r, 0 ≤ q r - kuhnLattice σ j r ∧ q r - kuhnLattice σ j r < (N + 1 : ℕ) := fun r => by
    have := hq' r
    rcases kuhnLattice_mem σ j r with h | h <;> rw [h] <;> push_cast at this ⊢ <;> omega
  set m' : Fin n → Fin (N + 1) := fun r =>
    ⟨(q r - kuhnLattice σ j r).toNat, by have := hm r; omega⟩ with hm'_def
  have hm' : finLattice m' = q - kuhnLattice σ j := by
    funext r
    simp only [finLattice, m', Pi.sub_apply]
    exact Int.toNat_of_nonneg (hm r).1
  refine mem_freudenthalMesh_simplices.2 ⟨m', σ, Affine.Simplex.ext fun k => ?_⟩
  rw [translate_points, mapEquiv_boxMap_freudenthalSimplex_points,
    mapEquiv_boxMap_freudenthalSimplex_points, freudenthalPoints_eq_node, freudenthalPoints_eq_node,
    freudenthalPoints_eq_node, hm']
  funext r
  simp only [node_coord, Pi.add_apply, Pi.sub_apply]
  push_cast
  ring

/-- **The edges of the Freudenthal meshes** have Euclidean length at most `√n h`: the vertices of
`b + h (m + K_σ)` differ by `h` times vectors with entries in `{-1, 0, 1}`. -/
theorem dotProduct_sub_le_freudenthalMesh (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (freudenthalMesh b s hs (N + 1)).simplices)
    (j k : Fin (n + 1)) :
    (T.points k - T.points j) ⬝ᵥ (T.points k - T.points j) ≤ n * (s / (N + 1 : ℕ)) ^ 2 := by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  rw [mapEquiv_boxMap_freudenthalSimplex_points]
  have hle : ∀ r, (freudenthalPoints b (s / (N + 1 : ℕ)) (finLattice m) σ k -
      freudenthalPoints b (s / (N + 1 : ℕ)) (finLattice m) σ j) r *
      (freudenthalPoints b (s / (N + 1 : ℕ)) (finLattice m) σ k -
      freudenthalPoints b (s / (N + 1 : ℕ)) (finLattice m) σ j) r ≤ (s / (N + 1 : ℕ)) ^ 2 := by
    intro r
    have e : (freudenthalPoints b (s / (N + 1 : ℕ)) (finLattice m) σ k -
        freudenthalPoints b (s / (N + 1 : ℕ)) (finLattice m) σ j) r =
        s / (N + 1 : ℕ) * (kuhnVertex σ k r - kuhnVertex σ j r) := by
      simp only [freudenthalPoints, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h01 : ∀ l, kuhnVertex σ l r = 0 ∨ kuhnVertex σ l r = 1 := fun l => by
      simp only [kuhnVertex]
      split_ifs <;> simp
    rw [e]
    rcases h01 k with hk | hk <;> rcases h01 j with hj | hj <;> rw [hk, hj] <;>
      nlinarith [sq_nonneg (s / (N + 1 : ℕ))]
  calc _ = ∑ r, (freudenthalPoints b (s / (N + 1 : ℕ)) (finLattice m) σ k -
        freudenthalPoints b (s / (N + 1 : ℕ)) (finLattice m) σ j) r *
        (freudenthalPoints b (s / (N + 1 : ℕ)) (finLattice m) σ k -
        freudenthalPoints b (s / (N + 1 : ℕ)) (finLattice m) σ j) r := rfl
    _ ≤ ∑ _r : Fin n, (s / (N + 1 : ℕ)) ^ 2 := sum_le_sum fun r _ => hle r
    _ = n * (s / (N + 1 : ℕ)) ^ 2 := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The cross-polytope: no consistency without translation invariance -/

section CrossPolytope

variable {h : ℝ}

/-- The sign `1` or `-1` of `b : Bool`. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

theorem boolSign_mul_self (b : Bool) : boolSign b * boolSign b = 1 := by
  cases b <;> norm_num [boolSign]

theorem boolSign_ne_zero (b : Bool) : boolSign b ≠ 0 := by
  cases b <;> norm_num [boolSign]

theorem boolSign_injective : Function.Injective boolSign := by
  intro a b e
  cases a <;> cases b <;> first | rfl | (norm_num [boolSign] at e)

/-- The diagonal map `z ↦ (h sᵢ zᵢ)ᵢ` onto the orthant of the signs `s`. -/
def orthantEquiv (hh : h ≠ 0) (s : Fin n → Bool) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  LinearEquiv.piCongrRight fun i =>
    LinearEquiv.smulOfNeZero ℝ ℝ (h * boolSign (s i)) (mul_ne_zero hh (boolSign_ne_zero _))

@[simp] theorem orthantEquiv_apply (hh : h ≠ 0) (s : Fin n → Bool) (z : Fin n → ℝ) (i : Fin n) :
    orthantEquiv hh s z i = h * boolSign (s i) * z i := by
  simp [orthantEquiv]

/-- **The orthant simplex** `conv(0, h s₀ e₀, …, h s_{n-1} e_{n-1})` of the signs `s`, `sᵢ = ±1`. -/
def orthantSimplex (hh : h ≠ 0) (s : Fin n → Bool) : Affine.Simplex ℝ (Fin n → ℝ) n :=
  mapEquiv (orthantEquiv hh s).toAffineEquiv (Feec.Mesh.refSimplex n)

@[simp] theorem orthantSimplex_points_zero (hh : h ≠ 0) (s : Fin n → Bool) :
    (orthantSimplex hh s).points 0 = 0 := by
  simp [orthantSimplex]

@[simp] theorem orthantSimplex_points_succ (hh : h ≠ 0) (s : Fin n → Bool) (l : Fin n) :
    (orthantSimplex hh s).points l.succ = Pi.single l (h * boolSign (s l)) := by
  funext i
  simp only [orthantSimplex, mapEquiv_points, LinearEquiv.coe_toAffineEquiv,
    Feec.Mesh.refSimplex_points, Feec.Mesh.refPoints_succ, orthantEquiv_apply]
  by_cases hi : i = l
  · subst hi; simp
  · simp [hi]

theorem orthantSimplex_points_ne_zero (hh : h ≠ 0) (s : Fin n → Bool) (l : Fin n) :
    (orthantSimplex hh s).points l.succ ≠ 0 := by
  rw [orthantSimplex_points_succ]
  intro e
  have := congrFun e l
  simp only [Pi.single_eq_same, Pi.zero_apply] at this
  exact mul_ne_zero hh (boolSign_ne_zero _) this

theorem mem_closedInterior_orthantSimplex (hh : 0 < h) (s : Fin n → Bool) {z : Fin n → ℝ} :
    z ∈ (orthantSimplex hh.ne' s).closedInterior ↔
      (∀ i, 0 ≤ boolSign (s i) * z i) ∧ ∑ i, boolSign (s i) * z i ≤ h := by
  rw [orthantSimplex, closedInterior_mapEquiv, LinearEquiv.coe_toAffineEquiv]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Feec.Mesh.mem_closedInterior_refSimplex] at hw
    have e : ∀ i, boolSign (s i) * orthantEquiv hh.ne' s w i = h * w i := fun i => by
      rw [orthantEquiv_apply]
      linear_combination (h * w i) * boolSign_mul_self (s i)
    simp only [e]
    refine ⟨fun i => mul_nonneg hh.le (hw.1 i), ?_⟩
    rw [← mul_sum]
    nlinarith [hw.2]
  · rintro ⟨h0, h1⟩
    refine ⟨fun i => boolSign (s i) * z i / h, ?_, ?_⟩
    · rw [Feec.Mesh.mem_closedInterior_refSimplex]
      refine ⟨fun i => div_nonneg (h0 i) hh.le, ?_⟩
      rw [← sum_div, div_le_one hh]
      exact h1
    · funext i
      rw [orthantEquiv_apply]
      field_simp
      linear_combination z i * boolSign_mul_self (s i)

theorem closure_sum_abs_lt (hh : 0 < h) :
    closure {z : Fin n → ℝ | ∑ i, |z i| < h} = {z | ∑ i, |z i| ≤ h} := by
  have hc : Continuous fun z : Fin n → ℝ => ∑ i, |z i| := by fun_prop
  refine subset_antisymm (closure_lt_subset_le hc continuous_const) fun z hz => ?_
  have hcont : Continuous fun t : ℝ => t • z := continuous_id.smul continuous_const
  have ht : Filter.Tendsto (fun t : ℝ => t • z) (nhdsWithin 1 (Set.Iio 1)) (nhds z) := by
    have := hcont.tendsto 1
    simp only [one_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos ht.1, ← mul_sum]
  have hz' : ∑ i, |z i| ≤ h := hz
  nlinarith [ht.1, ht.2]

theorem iUnion_closedInterior_orthantSimplex (hh : 0 < h) :
    ⋃ s : Fin n → Bool, (orthantSimplex hh.ne' s).closedInterior = {z | ∑ i, |z i| ≤ h} := by
  ext z
  simp only [Set.mem_iUnion, mem_closedInterior_orthantSimplex hh, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, h0, h1⟩
    have e : ∀ i, |z i| = boolSign (s i) * z i := fun i => by
      rw [← abs_of_nonneg (h0 i), abs_mul]
      cases s i <;> simp [boolSign]
    simpa only [e] using h1
  · intro hz
    refine ⟨fun i => decide (0 ≤ z i), fun i => ?_, ?_⟩
    · by_cases hi : 0 ≤ z i
      · simp [boolSign, hi]
      · simp only [boolSign, hi, decide_false, Bool.false_eq_true, ↓reduceIte]
        linarith
    · have e : ∀ i, boolSign (decide (0 ≤ z i)) * z i = |z i| := fun i => by
        by_cases hi : 0 ≤ z i
        · simp [boolSign, hi, abs_of_nonneg hi]
        · simp [boolSign, hi, abs_of_neg (lt_of_not_ge hi)]
      simpa only [e] using hz

theorem inter_closedInterior_orthantSimplex (hh : 0 < h) (s s' : Fin n → Bool) :
    (orthantSimplex hh.ne' s).closedInterior ∩ (orthantSimplex hh.ne' s').closedInterior =
      convexHull ℝ ((vertexSet (orthantSimplex hh.ne' s) : Set (Fin n → ℝ)) ∩
        vertexSet (orthantSimplex hh.ne' s')) := by
  classical
  refine subset_antisymm (fun z hz => ?_) (Set.subset_inter
    (fun z hz => convexHull_vertexSet (orthantSimplex hh.ne' s) ▸
      convexHull_mono Set.inter_subset_left hz)
    (fun z hz => convexHull_vertexSet (orthantSimplex hh.ne' s') ▸
      convexHull_mono Set.inter_subset_right hz))
  obtain ⟨hz, hz'⟩ := hz
  rw [mem_closedInterior_orthantSimplex hh] at hz hz'
  have h0 : ∀ i, s i ≠ s' i → z i = 0 := fun i hi => by
    have hs : boolSign (s' i) = -boolSign (s i) := by
      cases hsi : s i <;> cases hs'i : s' i <;> simp_all [boolSign]
    have a := hz.1 i
    have b := hz'.1 i
    rw [hs, neg_mul] at b
    exact (mul_eq_zero.1 (le_antisymm (by linarith) a)).resolve_left (boolSign_ne_zero _)
  -- the common vertices `0` and `h sᵢ eᵢ` for `sᵢ = s'ᵢ`
  set V : Set (Fin n → ℝ) := (vertexSet (orthantSimplex hh.ne' s) : Set (Fin n → ℝ)) ∩
    vertexSet (orthantSimplex hh.ne' s')
  have hV0 : (0 : Fin n → ℝ) ∈ V :=
    ⟨mem_vertexSet.2 ⟨0, by simp⟩, mem_vertexSet.2 ⟨0, by simp⟩⟩
  set v : Fin n → Fin n → ℝ := fun i => if s i = s' i then Pi.single i (h * boolSign (s i)) else 0
  have hv : ∀ i, v i ∈ convexHull ℝ V := fun i => by
    by_cases hi : s i = s' i
    · refine subset_convexHull ℝ V ⟨mem_vertexSet.2 ⟨i.succ, ?_⟩, mem_vertexSet.2 ⟨i.succ, ?_⟩⟩
      · simp [v, hi]
      · simp [v, hi]
    · simpa [v, hi] using subset_convexHull ℝ V hV0
  set w : Fin n → ℝ := fun i => boolSign (s i) * z i / h
  have hz_eq : z = ∑ i, w i • v i := by
    funext l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v, w]
    rw [Finset.sum_eq_single l (fun i _ hil => by split_ifs <;> simp [Ne.symm hil]) (by simp)]
    by_cases hl : s l = s' l
    · simp only [hl, ↓reduceIte, Pi.single_eq_same]
      field_simp
      linear_combination -(z l) * boolSign_mul_self (s' l)
    · simp [hl, h0 l hl]
  have hw0 : ∀ i, 0 ≤ w i := fun i => div_nonneg (hz.1 i) hh.le
  have hw1 : ∑ i, w i ≤ 1 := by
    simp only [w]
    rw [← sum_div, div_le_one hh]
    exact hz.2
  -- a convex combination with the vertex `0`
  have key := (convex_convexHull ℝ V).sum_mem (t := univ)
    (w := (Fin.cons (1 - ∑ i, w i) w : Fin (n + 1) → ℝ))
    (z := (Fin.cons 0 v : Fin (n + 1) → Fin n → ℝ))
    (fun j _ => Fin.cases (by simpa using hw1) (fun i => by simpa using hw0 i) j)
    (by simp [Fin.sum_univ_succ])
    (fun j _ => Fin.cases (by simpa using subset_convexHull ℝ V hV0)
      (fun i => by simpa using hv i) j)
  rw [Fin.sum_univ_succ] at key
  simpa [← hz_eq] using key

theorem injective_orthantSimplex (hh : h ≠ 0) :
    Function.Injective (orthantSimplex (n := n) hh) := by
  intro s s' e
  funext l
  have := congrFun (congrArg Affine.Simplex.points e) l.succ
  simp only [orthantSimplex_points_succ] at this
  have hl := congrFun this l
  simp only [Pi.single_eq_same] at hl
  exact boolSign_injective (mul_left_cancel₀ hh hl)

theorem injOn_vertexSet_orthantSimplex (hh : 0 < h) :
    Set.InjOn vertexSet (Set.range (orthantSimplex (n := n) hh.ne')) := by
  rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩ hV
  congr 1
  funext l
  have hl : Pi.single l (h * boolSign (s l)) ∈ vertexSet (orthantSimplex hh.ne' s') :=
    hV ▸ mem_vertexSet.2 ⟨l.succ, by simp⟩
  obtain ⟨j, hj⟩ := mem_vertexSet.1 hl
  induction j using Fin.cases with
  | zero =>
    have := congrFun hj l
    simp only [orthantSimplex_points_zero, Pi.zero_apply, Pi.single_eq_same] at this
    exact absurd this.symm (mul_ne_zero hh.ne' (boolSign_ne_zero _))
  | succ k =>
    rw [orthantSimplex_points_succ] at hj
    have hkl : k = l := by
      by_contra hkl
      have := congrFun hj l
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne' hkl] at this
      exact mul_ne_zero hh.ne' (boolSign_ne_zero _) this.symm
    subst hkl
    have := congrFun hj k
    simp only [Pi.single_eq_same] at this
    exact (boolSign_injective (mul_left_cancel₀ hh.ne' this)).symm

open Classical in
/-- **The cross-polytope mesh** of `{z | Σᵢ |zᵢ| < h}`: the `2ⁿ` orthant simplices
`conv(0, h s₀ e₀, …, h s_{n-1} e_{n-1})`, which meet at the centre `0`. -/
def crossMesh (hh : 0 < h) : SimplicialMesh n :=
  SimplicialMesh.ofConforming (univ.image (orthantSimplex hh.ne')) {z | ∑ i, |z i| < h}
    (by
      rw [closure_sum_abs_lt hh, ← iUnion_closedInterior_orthantSimplex hh,
        Finset.set_biUnion_finset_image]
      simp)
    (by
      simp only [mem_image, mem_univ, true_and]
      rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩
      exact inter_closedInterior_orthantSimplex hh s s')
    (by
      rw [coe_image, coe_univ, Set.image_univ]
      exact injOn_vertexSet_orthantSimplex hh)

theorem mem_crossMesh_simplices (hh : 0 < h) {T : Affine.Simplex ℝ (Fin n → ℝ) n} :
    T ∈ (crossMesh hh).simplices ↔ ∃ s, orthantSimplex hh.ne' s = T := by
  classical
  simp [crossMesh, SimplicialMesh.ofConforming]

theorem sum_crossMesh (hh : 0 < h) (f : Affine.Simplex ℝ (Fin n → ℝ) n → ℝ) :
    ∑ T ∈ (crossMesh hh).simplices, f T = ∑ s, f (orthantSimplex hh.ne' s) := by
  classical
  show ∑ T ∈ univ.image (orthantSimplex hh.ne'), f T = _
  rw [sum_image fun s _ s' _ e => injective_orthantSimplex hh.ne' e]

theorem edgeMatrix_orthantSimplex (hh : h ≠ 0) (s : Fin n → Bool) :
    edgeMatrix (orthantSimplex hh s).points = Matrix.diagonal fun l => h * boolSign (s l) := by
  ext i l
  simp only [edgeMatrix, simplexMatrix, Matrix.of_apply, orthantSimplex_points_succ,
    orthantSimplex_points_zero, Pi.zero_apply, sub_zero, Matrix.diagonal_apply, Pi.single_apply]
  split_ifs with hil
  · rw [hil]
  · rfl

theorem inv_edgeMatrix_orthantSimplex (hh : h ≠ 0) (s : Fin n → Bool) :
    (edgeMatrix (orthantSimplex hh s).points)⁻¹ =
      Matrix.diagonal fun l => (h * boolSign (s l))⁻¹ := by
  rw [edgeMatrix_orthantSimplex]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext l
  exact inv_mul_cancel₀ (mul_ne_zero hh (boolSign_ne_zero _))

/-- `∇λ₀ = -(h sₗ)⁻¹`, the gradient of the barycentric coordinate of the centre. -/
theorem baryGrad_orthantSimplex_zero (hh : h ≠ 0) (s : Fin n → Bool) :
    baryGrad (orthantSimplex hh s).points 0 = fun l => -(h * boolSign (s l))⁻¹ := by
  funext l
  simp [baryGrad, inv_edgeMatrix_orthantSimplex, Matrix.diagonal_apply]

/-- `∇λₘ₊₁ = (h sₘ)⁻¹ eₘ`. -/
theorem baryGrad_orthantSimplex_succ (hh : h ≠ 0) (s : Fin n → Bool) (m : Fin n) :
    baryGrad (orthantSimplex hh s).points m.succ = Pi.single m (h * boolSign (s m))⁻¹ := by
  funext l
  simp [baryGrad, inv_edgeMatrix_orthantSimplex, Matrix.diagonal_apply, Pi.single_apply, eq_comm]

/-- **The cross-polytope mesh is non-obtuse**: its simplices have right angles at the centre. -/
theorem isNonobtuse_crossMesh (hh : 0 < h) : IsNonobtuse (crossMesh (n := n) hh) := by
  intro T hT j k hjk
  obtain ⟨s, rfl⟩ := (mem_crossMesh_simplices hh).1 hT
  have hsq : ∀ m, 0 ≤ (h * boolSign (s m))⁻¹ * (h * boolSign (s m))⁻¹ := fun m =>
    mul_self_nonneg _
  induction j using Fin.cases with
  | zero =>
    induction k using Fin.cases with
    | zero => exact absurd rfl hjk
    | succ k =>
      rw [baryGrad_orthantSimplex_zero, baryGrad_orthantSimplex_succ, dotProduct_single]
      linarith [hsq k]
  | succ j =>
    induction k using Fin.cases with
    | zero =>
      rw [baryGrad_orthantSimplex_succ, baryGrad_orthantSimplex_zero, single_dotProduct]
      linarith [hsq j]
    | succ k =>
      have hjk' : j ≠ k := fun e => hjk (by rw [e])
      rw [baryGrad_orthantSimplex_succ, baryGrad_orthantSimplex_succ, dotProduct_single,
        Pi.single_eq_of_ne' hjk', zero_mul]

/-- **The lumped-mass Laplacian of the cross-polytope mesh at its centre**, the single node:
`(Lₕ U)(0) = -n (n + 1) U(0) / h²` (Dirichlet data at the other vertices): `a(φ₀, φ₀) = Σ |T| n/h²`
and `m(0) = Σ |T| / (n + 1)`. -/
theorem lumpedLaplacianOn_crossMesh (hh : 0 < h) (U : Unit → ℝ) :
    lumpedLaplacianOn (crossMesh (n := n) hh) (fun _ : Unit => (0 : Fin n → ℝ)) U () =
      -(n * (n + 1) / h ^ 2) * U () := by
  classical
  have hgrad : ∀ s : Fin n → Bool, p1Grad (orthantSimplex hh.ne' s).points (nodalIndicator 0) =
      baryGrad (orthantSimplex hh.ne' s).points 0 := fun s => by
    have := p1Grad_nodalIndicator (orthantSimplex hh.ne' s).independent.injective 0
    rwa [orthantSimplex_points_zero] at this
  have hnorm : ∀ s : Fin n → Bool, baryGrad (orthantSimplex hh.ne' s).points 0 ⬝ᵥ
      baryGrad (orthantSimplex hh.ne' s).points 0 = n / h ^ 2 := fun s => by
    have e : ∀ l, -(h * boolSign (s l))⁻¹ * -(h * boolSign (s l))⁻¹ = 1 / h ^ 2 := fun l => by
      rw [neg_mul_neg, ← mul_inv, mul_mul_mul_comm, boolSign_mul_self, mul_one, one_div, sq]
    rw [baryGrad_orthantSimplex_zero]
    simp only [dotProduct, e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hcard : ∀ s : Fin n → Bool, (#{j | (orthantSimplex hh.ne' s).points j = 0} : ℝ) = 1 :=
      fun s => by
    have : (univ.filter fun j => (orthantSimplex hh.ne' s).points j = 0) = {0} := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      refine ⟨fun hj => ?_, fun hj => by rw [hj, orthantSimplex_points_zero]⟩
      by_contra hj0
      obtain ⟨l, rfl⟩ := Fin.exists_succ_eq.2 hj0
      exact orthantSimplex_points_ne_zero hh.ne' s l hj
    rw [this, card_singleton, Nat.cast_one]
  have ha : p1Stiffness (crossMesh (n := n) hh) (nodalIndicator 0) (nodalIndicator 0) =
      (∑ s : Fin n → Bool, volume.real (orthantSimplex hh.ne' s).closedInterior) * (n / h ^ 2) := by
    rw [p1Stiffness_eq, sum_crossMesh, sum_mul]
    simp only [hgrad, hnorm]
  have hm : lumpedMass (crossMesh (n := n) hh) 0 =
      (∑ s : Fin n → Bool, volume.real (orthantSimplex hh.ne' s).closedInterior) / (n + 1) := by
    rw [lumpedMass, sum_crossMesh, sum_div]
    simp only [hcard, mul_one]
  have hV : 0 < ∑ s : Fin n → Bool, volume.real (orthantSimplex hh.ne' s).closedInterior :=
    sum_pos (fun s _ => measureReal_closedInterior_pos _) univ_nonempty
  rw [lumpedLaplacianOn_apply_eq_sum, Fintype.sum_unique]
  simp only [lumpedEntry, ha, hm]
  field_simp

/-- `∂ₗ (|z|² - c)/2 = zₗ`. -/
theorem partialDeriv_half_dotProduct_sub (c : ℝ) (l : Fin n) :
    partialDeriv l (fun z : Fin n → ℝ => (z ⬝ᵥ z - c) / 2) = fun z => z l := by
  funext y
  have e : (fun z : Fin n → ℝ => (z ⬝ᵥ z - c) / 2) = fun z => 2⁻¹ * (∑ i, z i * z i - c) := by
    funext z
    simp only [dotProduct]
    ring
  have hd : ∀ i, DifferentiableAt ℝ (fun z : Fin n → ℝ => z i) y := fun i => by fun_prop
  rw [e, partialDeriv_const_mul (by fun_prop) _ l, partialDeriv_sub (by fun_prop) (by fun_prop) l,
    partialDeriv_sum univ (fun i _ => by fun_prop) l, partialDeriv_const]
  simp only [partialDeriv_mul (hd _) (hd _), partialDeriv_apply_coord, ite_mul, one_mul,
    zero_mul, mul_ite, mul_one, mul_zero, sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte,
    sub_zero]
  ring

/-- `Δ (|z|² - c)/2 = n`. -/
theorem laplacian_half_dotProduct_sub (c : ℝ) (y : Fin n → ℝ) :
    laplacian (fun z : Fin n → ℝ => (z ⬝ᵥ z - c) / 2) y = n := by
  rw [laplacian_apply]
  have e : ∀ l : Fin n,
      partialDeriv l (partialDeriv l fun z : Fin n → ℝ => (z ⬝ᵥ z - c) / 2) y = 1 := fun l => by
    simp [partialDeriv_half_dotProduct_sub, partialDeriv_apply_coord]
  rw [sum_congr rfl fun l _ => e l, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]

/-- **No consistency without translation invariance**: on the cross-polytope mesh (non-obtuse),
with the single node `0` and Dirichlet data at the other vertices `±h eᵢ`, the lumped-mass
Laplacian of `u(z) = (|z|² - h²)/2`, which vanishes at the other vertices and has `Δu = n`, is
`n (n + 1)/2` at `0`: the nodal consistency error is `n (n - 1)/2` at every `h`, though
`D³u = D⁴u = 0`. The star of `0` is centrally symmetric; for `n ≥ 2` the mesh is not translation
invariant at `0` (`abs_lumpedLaplacianOn_sub_laplacian_le`). -/
theorem abs_lumpedLaplacianOn_crossMesh_sub_laplacian (hh : 0 < h) :
    |lumpedLaplacianOn (crossMesh (n := n) hh) (fun _ : Unit => (0 : Fin n → ℝ))
        (fun _ => ((0 : Fin n → ℝ) ⬝ᵥ 0 - h ^ 2) / 2) () -
      laplacian (fun z : Fin n → ℝ => (z ⬝ᵥ z - h ^ 2) / 2) 0| = n * (n - 1) / 2 := by
  rw [lumpedLaplacianOn_crossMesh, laplacian_half_dotProduct_sub, zero_dotProduct]
  have e : -(n * (n + 1) / h ^ 2) * ((0 - h ^ 2) / 2) - n = (n : ℝ) * (n - 1) / 2 := by
    field_simp
    ring
  rw [e]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact abs_of_nonneg (by positivity)

end CrossPolytope

end Feec.FiniteElement
