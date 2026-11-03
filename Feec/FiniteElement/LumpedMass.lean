module

public import Feec.FiniteElement.InverseEstimate

/-!
# Lumped-mass `P₁` finite elements on Freudenthal meshes: the difference stencil

The **`P₁` stiffness form** of a simplicial mesh `M` (`p1Stiffness M u w`) is
`a(u, w) = Σ_T ∫_T ∇Πₜu · ∇Πₜw`, with `Πₜu = Σⱼ u(pⱼ) λⱼ` the `P₁` interpolant of the nodal
values on `T` (`p1Interp`, gradient `p1Grad = Σⱼ u(pⱼ) ∇λⱼ`, `p1Interp_sub`), and the **lumped
mass** (`lumpedMass M x`) is the vertex quadrature `m(x) = Σ_{T ∋ x} |T| / (n + 1)` of `∫ φₓ`
([Thomee2006], Ch. 15). The **lumped-mass `P₁` Laplacian** is `-m⁻¹ a`.

`p1Stiffness` is defined by elementwise assembly; `Feec.FiniteElement.P1Global` identifies it with
`∫_Ω ∇u_h · ∇w_h` for the global conforming `P₁` (Whitney `0`-form) functions, and the lumped
mass with `∫_Ω φₓ`. With `neg_p1Stiffness_div_lumpedMass` the lumped-mass scheme on the
Freudenthal meshes is exactly the classical `(2n + 1)`-point finite difference scheme.

## Main results

* `p1Stiffness_indicator_nonpos` (Ciarlet–Raviart): if every simplex is **non-obtuse**,
  `∇λⱼ · ∇λₖ ≤ 0` for `j ≠ k`, the stiffness matrix has nonpositive off-diagonal entries;
* `baryGrad_freudenthal`: on a Freudenthal simplex `b + h (m + K_σ)` with vertices
  `vⱼ = Σ_{i<j} e_{σ i}`, `∇λⱼ = h⁻¹ (e_{σ(j-1)} - e_{σ j})`, so (`p1Grad_freudenthal`)
  `∂ₗ Πₜu = (u(v_{k+1}) - u(v_k)) / h` along the edge `v_k → v_{k+1} = v_k + h eₗ`,
  `k = σ⁻¹ l`; the element stiffness matrix is `hⁿ⁻² / n!` times the Laplacian of the path
  `v₀ - v₁ - ⋯ - vₙ` (`baryGrad_dotProduct_freudenthal_nonpos`: **Freudenthal simplices are
  non-obtuse**);
* **`p1Stiffness_freudenthalMesh`**: on the level-`N` Freudenthal mesh of a box, for nodal values
  vanishing on the boundary, `a(u, w) = hⁿ Σₗ Σ_{edges q → q + eₗ} Dₗu(q) Dₗw(q)` with the
  difference quotients `Dₗu(q) = (u(q + eₗ) - u(q)) / h`: every axis edge with an interior
  endpoint lies in exactly `n!` simplices as a path edge (one for each `σ`), each of volume
  `hⁿ / n!`, and the diagonal edges carry no coupling;
* `lumpedMass_freudenthalMesh`: `m(x) = hⁿ` at every interior node (`(n + 1)!` simplices of
  volume `hⁿ / n!` meet there);
* **`neg_p1Stiffness_div_lumpedMass`**: the lumped-mass `P₁` Laplacian at an interior node `p`
  is the `(2n + 1)`-point difference Laplacian
  `-a(φₚ, w) / m(p) = Σₗ (w(p + h eₗ) - 2 w(p) + w(p - h eₗ)) / h²`.

## References

* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
  (the lumped mass method)
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MeasureTheory

@[expose] public noncomputable section

namespace Feec.FiniteElement

open Feec.Mesh

variable {n : ℕ}

/-! ### `P₁` interpolation, stiffness and lumped mass on a mesh -/

/-- The gradient `∇Πₜu = Σⱼ u(pⱼ) ∇λⱼ` of the `P₁` interpolant of the nodal values `u` on the
simplex with vertices `p`. -/
def p1Grad (p : Fin (n + 1) → Fin n → ℝ) (u : (Fin n → ℝ) → ℝ) : Fin n → ℝ :=
  ∑ j, u (p j) • baryGrad p j

/-- The `P₁` interpolant `Πₜu = Σⱼ u(pⱼ) λⱼ` of the nodal values `u` on the simplex `p`. -/
def p1Interp (p : Fin (n + 1) → Fin n → ℝ) (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j, u (p j) * baryCoord p x j

/-- `Πₜu` is affine with gradient `p1Grad p u`. -/
theorem p1Interp_sub (p : Fin (n + 1) → Fin n → ℝ) (u : (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    p1Interp p u x - p1Interp p u y = p1Grad p u ⬝ᵥ (x - y) := by
  simp only [p1Interp, p1Grad, ← sum_sub_distrib, ← mul_sub, baryCoord_sub, dotProduct,
    Pi.sub_apply, mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- `Πₜu` interpolates `u` at the vertices. -/
theorem p1Interp_vertex {p : Fin (n + 1) → Fin n → ℝ} (hp : IsUnit (edgeMatrix p).det)
    (u : (Fin n → ℝ) → ℝ) (j : Fin (n + 1)) : p1Interp p u (p j) = u (p j) := by
  simp [p1Interp, baryCoord_vertex hp]

theorem p1Grad_add (p : Fin (n + 1) → Fin n → ℝ) (u w : (Fin n → ℝ) → ℝ) :
    p1Grad p (u + w) = p1Grad p u + p1Grad p w := by
  simp [p1Grad, add_smul, sum_add_distrib]

theorem p1Grad_smul (p : Fin (n + 1) → Fin n → ℝ) (c : ℝ) (u : (Fin n → ℝ) → ℝ) :
    p1Grad p (c • u) = c • p1Grad p u := by
  simp [p1Grad, smul_sum, smul_smul]

/-- **The `P₁` stiffness form** `a(u, w) = Σ_T ∫_T ∇Πₜu · ∇Πₜw` of the mesh `M`, on nodal
values `u, w : ℝⁿ → ℝ` (only the values at the vertices enter), assembled elementwise; it is
`⟪d u_h, d w_h⟫_{L²Λ¹(Ω)}` for the global `P₁` functions
(`Feec.FiniteElement.inner_glue_dPiecewise_p1Global`). -/
def p1Stiffness (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑ T ∈ M.simplices, ∫ _ in T.closedInterior, p1Grad T.points u ⬝ᵥ p1Grad T.points w

/-- The integrands are constant: `a(u, w) = Σ_T |T| ∇Πₜu · ∇Πₜw`. -/
theorem p1Stiffness_eq (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) :
    p1Stiffness M u w =
      ∑ T ∈ M.simplices, volume.real T.closedInterior * (p1Grad T.points u ⬝ᵥ p1Grad T.points w) := by
  simp [p1Stiffness, smul_eq_mul]

theorem p1Stiffness_comm (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) :
    p1Stiffness M u w = p1Stiffness M w u := by
  simp only [p1Stiffness, dotProduct_comm]

/-- `a(Σᵢ cᵢ uᵢ, w) = Σᵢ cᵢ a(uᵢ, w)`. -/
theorem p1Stiffness_sum_smul (M : SimplicialMesh n) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (u : ι → (Fin n → ℝ) → ℝ) (w : (Fin n → ℝ) → ℝ) :
    p1Stiffness M (∑ i ∈ s, c i • u i) w = ∑ i ∈ s, c i * p1Stiffness M (u i) w := by
  classical
  have hg : ∀ p : Fin (n + 1) → Fin n → ℝ,
      p1Grad p (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i • p1Grad p (u i) := fun p => by
    induction s using Finset.induction_on with
    | empty => simp [p1Grad]
    | insert a s ha ih => rw [sum_insert ha, sum_insert ha, p1Grad_add, p1Grad_smul, ih]
  simp only [p1Stiffness_eq, hg, sum_dotProduct, smul_dotProduct, smul_eq_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun T _ => by ring

theorem p1Stiffness_sum_smul_right (M : SimplicialMesh n) {κ : Type*} (s : Finset κ) (c : κ → ℝ)
    (u : (Fin n → ℝ) → ℝ) (w : κ → (Fin n → ℝ) → ℝ) :
    p1Stiffness M u (∑ i ∈ s, c i • w i) = ∑ i ∈ s, c i * p1Stiffness M u (w i) := by
  rw [p1Stiffness_comm, p1Stiffness_sum_smul]
  simp_rw [p1Stiffness_comm M u]

theorem p1Stiffness_add_right (M : SimplicialMesh n) (u w w' : (Fin n → ℝ) → ℝ) :
    p1Stiffness M u (w + w') = p1Stiffness M u w + p1Stiffness M u w' := by
  simp only [p1Stiffness_eq, p1Grad_add, dotProduct_add, mul_add, sum_add_distrib]

theorem p1Stiffness_congr_right (M : SimplicialMesh n) (u : (Fin n → ℝ) → ℝ)
    {w w' : (Fin n → ℝ) → ℝ} (h : ∀ T ∈ M.simplices, ∀ j, w (T.points j) = w' (T.points j)) :
    p1Stiffness M u w = p1Stiffness M u w' := by
  rw [p1Stiffness_eq, p1Stiffness_eq]
  refine sum_congr rfl fun T hT => ?_
  congr 2
  simp only [p1Grad, h T hT]

theorem p1Stiffness_const_right (M : SimplicialMesh n) (u : (Fin n → ℝ) → ℝ) (c : ℝ) :
    p1Stiffness M u (fun _ => c) = 0 := by
  rw [p1Stiffness_eq]
  refine sum_eq_zero fun T _ => ?_
  have : p1Grad T.points (fun _ => c) = 0 := by
    rw [p1Grad, ← smul_sum, sum_baryGrad, smul_zero]
  rw [this, dotProduct_zero, mul_zero]

/-- **The lumped mass** at `x`: the vertex quadrature `Σ_T |T| / (n + 1) · #{j | pⱼ = x}` of
`∫ φₓ`. -/
def lumpedMass (M : SimplicialMesh n) (x : Fin n → ℝ) : ℝ :=
  ∑ T ∈ M.simplices, volume.real T.closedInterior / (n + 1) *
    (#{j | T.points j = x} : ℝ)

theorem lumpedMass_nonneg (M : SimplicialMesh n) (x : Fin n → ℝ) : 0 ≤ lumpedMass M x :=
  sum_nonneg fun _ _ => mul_nonneg (div_nonneg measureReal_nonneg (by positivity))
    (Nat.cast_nonneg _)

/-- A point of positive lumped mass is a vertex of the mesh. -/
theorem exists_mem_vertexSet_of_lumpedMass_pos (M : SimplicialMesh n) {x : Fin n → ℝ}
    (h : 0 < lumpedMass M x) : ∃ T ∈ M.simplices, x ∈ vertexSet T := by
  by_contra! hc
  refine h.ne' (sum_eq_zero fun T hT => ?_)
  rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun j _ hj => hc T hT (mem_vertexSet.2 ⟨j, hj⟩)),
    Nat.cast_zero, mul_zero]

/-- The nodal values of the hat function `φₓ`: `1` at `x`, `0` elsewhere. -/
def nodalIndicator (x : Fin n → ℝ) : (Fin n → ℝ) → ℝ := fun y => if y = x then 1 else 0

/-- The non-obtuseness of a mesh: `∇λⱼ · ∇λₖ ≤ 0` for `j ≠ k` on every simplex. -/
def IsNonobtuse (M : SimplicialMesh n) : Prop :=
  ∀ T ∈ M.simplices, ∀ j k, j ≠ k → baryGrad T.points j ⬝ᵥ baryGrad T.points k ≤ 0

/-- **Non-obtuse meshes have nonpositive off-diagonal stiffness** (Ciarlet–Raviart): if
`∇λⱼ · ∇λₖ ≤ 0` for `j ≠ k` on every simplex, then `a(φₓ, φ_y) ≤ 0` for `x ≠ y`.
[CiarletRaviart1973] -/
theorem p1Stiffness_indicator_nonpos (M : SimplicialMesh n) (hM : IsNonobtuse M)
    {x y : Fin n → ℝ} (hxy : x ≠ y) :
    p1Stiffness M (nodalIndicator x) (nodalIndicator y) ≤ 0 := by
  rw [p1Stiffness_eq]
  refine sum_nonpos fun T hT => mul_nonpos_of_nonneg_of_nonpos measureReal_nonneg ?_
  simp only [p1Grad, nodalIndicator, ite_smul, one_smul, zero_smul, sum_dotProduct,
    dotProduct_sum]
  refine sum_nonpos fun j _ => sum_nonpos fun k _ => ?_
  split_ifs
  · exact hM T hT _ _ fun e => hxy (by subst e; simp_all)
  all_goals simp

/-! ### The Kuhn simplex and its barycentric gradients -/

/-- `s_k = e_{σ(k-1)}` for `1 ≤ k ≤ n`, `0` for `k = 0` and `k > n`: the step `v_k - v_{k-1}` of
the Kuhn path. -/
def kuhnStep (σ : Equiv.Perm (Fin n)) (k : ℕ) : Fin n → ℝ :=
  fun l => if (σ.symm l : ℕ) + 1 = k then 1 else 0

/-- The inverse of the Kuhn matrix: row `m` is `e_{σ m} - e_{σ(m+1)}`. -/
def kuhnMatrixInv (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun m l => kuhnStep σ (m + 1) l - kuhnStep σ (m + 2) l

/-- `Σₗ (s_k)ₗ fₗ = f_{σ(k-1)}` for `1 ≤ k ≤ n`, and `0` otherwise. -/
theorem sum_kuhnStep_mul (σ : Equiv.Perm (Fin n)) (k : ℕ) (f : Fin n → ℝ) :
    ∑ l, kuhnStep σ k l * f l = if h : 1 ≤ k ∧ k ≤ n then f (σ ⟨k - 1, by omega⟩) else 0 := by
  rw [← Equiv.sum_comp σ]
  simp only [kuhnStep, Equiv.symm_apply_apply, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
    · rw [ite_eq_left (by simp; omega)]
    · intro b _ hb
      rw [ite_eq_right]
      intro hc
      exact hb (Fin.ext (by simp; omega))
    · simp
  · exact sum_eq_zero fun a _ => by rw [ite_eq_right]; omega

theorem kuhnMatrixInv_mul (σ : Equiv.Perm (Fin n)) : kuhnMatrixInv σ * kuhnMatrix σ = 1 := by
  ext m i
  have e : ∀ k : ℕ, ∑ l, kuhnStep σ k l * kuhnMatrix σ l i =
      if 1 ≤ k ∧ k ≤ n ∧ k - 1 ≤ i then 1 else 0 := fun k => by
    rw [sum_kuhnStep_mul]
    simp only [kuhnMatrix, Matrix.of_apply, Equiv.symm_apply_apply, Fin.val_mk]
    split_ifs <;> first | rfl | omega
  simp only [Matrix.mul_apply, kuhnMatrixInv, Matrix.of_apply, sub_mul, sum_sub_distrib, e,
    Matrix.one_apply, Fin.ext_iff]
  have := m.2
  have := i.2
  split_ifs <;> (try simp) <;> omega

/-- The vertices `b + h (m + vⱼ)` of the Freudenthal simplex `b + h (m + K_σ)`. -/
def freudenthalPoints (b : Fin n → ℝ) (h : ℝ) (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    Fin (n + 1) → Fin n → ℝ :=
  fun j => b + h • (latticePoint m + kuhnVertex σ j)

theorem mapEquiv_boxMap_freudenthalSimplex_points (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0)
    (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    (mapEquiv (boxMap b h hh) (freudenthalSimplex m σ)).points = freudenthalPoints b h m σ := by
  funext j; simp [freudenthalPoints]

theorem edgeMatrix_freudenthalPoints (b : Fin n → ℝ) (h : ℝ) (m : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) : edgeMatrix (freudenthalPoints b h m σ) = h • kuhnMatrix σ := by
  ext i l
  simp [edgeMatrix, simplexMatrix, freudenthalPoints, kuhnMatrix, kuhnVertex]

theorem inv_edgeMatrix_freudenthalPoints (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) (m : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) :
    (edgeMatrix (freudenthalPoints b h m σ))⁻¹ = h⁻¹ • kuhnMatrixInv σ := by
  rw [edgeMatrix_freudenthalPoints]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hh, one_smul,
    kuhnMatrixInv_mul]

theorem isUnit_det_edgeMatrix_freudenthalPoints (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0)
    (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    IsUnit (edgeMatrix (freudenthalPoints b h m σ)).det := by
  refine Matrix.isUnit_det_of_left_inverse (B := h⁻¹ • kuhnMatrixInv σ) ?_
  rw [edgeMatrix_freudenthalPoints, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hh, one_smul, kuhnMatrixInv_mul]

/-- **The barycentric gradients of a Freudenthal simplex**: `∇λⱼ = h⁻¹ (s_j - s_{j+1})`, i.e.
`∇λ₀ = -h⁻¹ e_{σ 0}`, `∇λⱼ = h⁻¹ (e_{σ(j-1)} - e_{σ j})`, `∇λₙ = h⁻¹ e_{σ(n-1)}`. -/
theorem baryGrad_freudenthalPoints (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) (m : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    baryGrad (freudenthalPoints b h m σ) j = h⁻¹ • (kuhnStep σ j - kuhnStep σ (j + 1)) := by
  rw [baryGrad, inv_edgeMatrix_freudenthalPoints b hh]
  refine Fin.cases ?_ (fun k => ?_) j
  · funext l
    simp only [Fin.cons_zero, Matrix.smul_apply, kuhnMatrixInv, Matrix.of_apply, smul_eq_mul,
      ← mul_sum, Pi.smul_apply, Pi.sub_apply, Fin.val_zero, zero_add]
    rw [Fin.sum_univ_eq_sum_range (fun m => kuhnStep σ (m + 1) l - kuhnStep σ (m + 2) l),
      sum_range_sub' (fun m => kuhnStep σ (m + 1) l)]
    have h0 : kuhnStep σ 0 l = 0 := by simp [kuhnStep]
    have hn : kuhnStep σ (n + 1) l = 0 := by
      simp only [kuhnStep]; rw [ite_eq_right]; have := (σ.symm l).2; omega
    simp only [h0, hn]
    ring
  · funext l
    simp [kuhnMatrixInv, Fin.val_succ]

/-- `∑ⱼ fⱼ [j = a] = f a` over the vertices, with the condition on the values. -/
theorem sum_ite_val_eq (a : ℕ) (ha : a < n + 1) (f : Fin (n + 1) → ℝ) :
    ∑ j : Fin (n + 1), (if (j : ℕ) = a then f j else 0) = f ⟨a, ha⟩ := by
  rw [Finset.sum_eq_single ⟨a, ha⟩]
  · simp
  · intro c _ hc; rw [ite_eq_right]; intro e; exact hc (Fin.ext e)
  · simp

/-- **The gradient of the `P₁` interpolant on a Freudenthal simplex**:
`∂ₗ Πₜu = (u(v_{k+1}) - u(v_k)) / h`, `k = σ⁻¹ l`, the difference quotient along the path edge
`v_k → v_{k+1} = v_k + h eₗ`. -/
theorem p1Grad_freudenthalPoints (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) (m : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) (u : (Fin n → ℝ) → ℝ) (l : Fin n) :
    p1Grad (freudenthalPoints b h m σ) u l =
      (u (freudenthalPoints b h m σ (σ.symm l).succ) -
        u (freudenthalPoints b h m σ (σ.symm l).castSucc)) / h := by
  have hterm : ∀ j : Fin (n + 1), u (freudenthalPoints b h m σ j) *
      (h⁻¹ * (kuhnStep σ j l - kuhnStep σ (j + 1) l)) =
      h⁻¹ * ((if (j : ℕ) = σ.symm l + 1 then u (freudenthalPoints b h m σ j) else 0) -
        (if (j : ℕ) = σ.symm l then u (freudenthalPoints b h m σ j) else 0)) := by
    intro j; simp only [kuhnStep]; split_ifs <;> first | (exfalso; omega) | ring
  have hl := (σ.symm l).2
  simp only [p1Grad, baryGrad_freudenthalPoints b hh, Finset.sum_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← mul_sum, sum_sub_distrib,
    sum_ite_val_eq _ (by omega), sum_ite_val_eq _ (by omega), div_eq_inv_mul]
  rfl

/-- **Freudenthal simplices are non-obtuse**: `∇λⱼ · ∇λₖ ≤ 0` for `j ≠ k` (the element stiffness
matrix is `hⁿ⁻² / n!` times the Laplacian of the path `v₀ - v₁ - ⋯ - vₙ`). -/
theorem baryGrad_dotProduct_freudenthalPoints_nonpos (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0)
    (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) {j k : Fin (n + 1)} (hjk : j ≠ k) :
    baryGrad (freudenthalPoints b h m σ) j ⬝ᵥ baryGrad (freudenthalPoints b h m σ) k ≤ 0 := by
  rw [baryGrad_freudenthalPoints b hh, baryGrad_freudenthalPoints b hh, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
  refine mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) (sum_nonpos fun l _ => ?_)
  have : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
  simp only [Pi.sub_apply, kuhnStep]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- **The Freudenthal meshes are non-obtuse** (`baryGrad_dotProduct_freudenthalPoints_nonpos`). -/
theorem isNonobtuse_freudenthalMesh (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N] :
    IsNonobtuse (freudenthalMesh b s hs N) := fun T hT j k hjk => by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  rw [mapEquiv_boxMap_freudenthalSimplex_points]
  exact baryGrad_dotProduct_freudenthalPoints_nonpos b (freudenthalScale_ne_zero hs N) _ _ hjk

/-- **The Freudenthal meshes are non-obtuse**, so their stiffness matrices have nonpositive
off-diagonal entries (Ciarlet–Raviart). [CiarletRaviart1973] -/
theorem p1Stiffness_freudenthalMesh_indicator_nonpos (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s)
    (N : ℕ) [NeZero N] {x y : Fin n → ℝ} (hxy : x ≠ y) :
    p1Stiffness (freudenthalMesh b s hs N) (nodalIndicator x) (nodalIndicator y) ≤ 0 :=
  p1Stiffness_indicator_nonpos _ (isNonobtuse_freudenthalMesh b hs N) hxy

/-! ### Lattice nodes, edges and the boundary -/

/-- The lattice node `b + h q`. -/
def node (b : Fin n → ℝ) (h : ℝ) (q : Fin n → ℤ) : Fin n → ℝ := b + h • latticePoint q

theorem node_injective (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) : Function.Injective (node b h) := by
  intro q q' e
  funext i
  have := congrFun e i
  simp only [node, Pi.add_apply, Pi.smul_apply, latticePoint_apply, smul_eq_mul, add_right_inj,
    mul_eq_mul_left_iff, hh, or_false, Int.cast_inj] at this
  exact this

/-- The nodes of a finite set of lattice points are distinct. -/
theorem node_injective_subtype (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) (S : Finset (Fin n → ℤ)) :
    Function.Injective fun q : S => node b h q :=
  fun _ _ e => Subtype.ext (node_injective b hh e)

theorem node_add_single (b : Fin n → ℝ) (h : ℝ) (q : Fin n → ℤ) (l : Fin n) (c : ℤ) :
    node b h (q + Pi.single l c) = node b h q + (h * c) • Pi.single l 1 := by
  funext i
  simp only [node, Pi.add_apply, Pi.smul_apply, latticePoint_apply, smul_eq_mul, Int.cast_add]
  by_cases hi : i = l
  · subst hi; simp; ring
  · simp [hi]

/-- The interior nodes `q ∈ {1, …, N - 1}ⁿ` of the level-`N` lattice. -/
def interiorNodes (n N : ℕ) : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Ioo 0 (N : ℤ)

/-- The base points `q` of the axis edges `q → q + eₗ` with an interior endpoint:
`qₗ ∈ {0, …, N - 1}`, `qⱼ ∈ {1, …, N - 1}` for `j ≠ l`. -/
def edgeBases (n N : ℕ) (l : Fin n) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun j => if j = l then Ico 0 (N : ℤ) else Ioo 0 (N : ℤ)

/-- The nodal values `u` vanish at the boundary nodes of the level-`N` lattice of `b + h ℤⁿ`. -/
def VanishesOnBoundary (b : Fin n → ℝ) (h : ℝ) (N : ℕ) (u : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ q : Fin n → ℤ, (∀ j, 0 ≤ q j ∧ q j ≤ (N : ℤ)) → (∃ j, q j = 0 ∨ q j = (N : ℤ)) →
    u (node b h q) = 0

/-- **Shift invariance of the edge sums**: for a `0/1` vector `a` with `aₗ = 0` and `G` vanishing
on the edges `q → q + eₗ` of the boundary faces (`qⱼ ∈ {0, N}` for some `j ≠ l`), the sum of `G`
over the cells shifted by `a` is its sum over the edges with an interior endpoint. -/
theorem sum_finLattice_add {N : ℕ} (l : Fin n) {a : Fin n → ℤ} (ha : ∀ j, a j = 0 ∨ a j = 1)
    (hal : a l = 0) (G : (Fin n → ℤ) → ℝ)
    (hG : ∀ q : Fin n → ℤ, (∀ j, 0 ≤ q j ∧ q j ≤ (N : ℤ)) → q l < N →
      (∃ j, j ≠ l ∧ (q j = 0 ∨ q j = (N : ℤ))) → G q = 0) :
    ∑ m : Fin n → Fin N, G (finLattice m + a) = ∑ q ∈ edgeBases n N l, G q := by
  have hinj : Function.Injective fun m : Fin n → Fin N => finLattice m + a := by
    intro m m' e
    funext j
    have := congrFun e j
    simp only [Pi.add_apply, finLattice, add_left_inj, Nat.cast_inj] at this
    exact Fin.ext this
  rw [← sum_image (f := G) fun m _ m' _ e => hinj e]
  symm
  refine sum_subset (fun q hq => ?_) fun q hq hq' => ?_
  · rw [edgeBases, Fintype.mem_piFinset] at hq
    rw [mem_image]
    have hb : ∀ j, 0 ≤ q j - a j ∧ q j - a j < N := fun j => by
      have h1 := hq j
      by_cases hj : j = l
      · subst hj
        rw [ite_eq_left rfl, mem_Ico] at h1
        rw [hal]; omega
      · rw [ite_eq_right hj, mem_Ioo] at h1
        rcases ha j with h | h <;> rw [h] <;> omega
    refine ⟨fun j => ⟨(q j - a j).toNat, by have := hb j; omega⟩, mem_univ _, ?_⟩
    funext j
    simp only [finLattice, Pi.add_apply]
    have := hb j
    omega
  · obtain ⟨m, -, rfl⟩ := mem_image.1 hq
    have hm : ∀ j, 0 ≤ (finLattice m j : ℤ) ∧ (finLattice m j : ℤ) < N := fun j => by
      have := (m j).2
      simp only [finLattice]; omega
    apply hG
    · intro j
      have := hm j
      rcases ha j with h | h <;> simp only [Pi.add_apply, h] <;> omega
    · have := hm l
      simp only [Pi.add_apply, hal, add_zero]; omega
    · rw [edgeBases, Fintype.mem_piFinset] at hq'
      simp only [not_forall] at hq'
      obtain ⟨j, hj⟩ := hq'
      have := hm j
      by_cases hjl : j = l
      · subst hjl
        rw [ite_eq_left rfl, mem_Ico] at hj
        simp only [Pi.add_apply, hal, add_zero] at hj
        omega
      · refine ⟨j, hjl, ?_⟩
        rw [ite_eq_right hjl, mem_Ioo] at hj
        simp only [Pi.add_apply] at hj ⊢
        rcases ha j with h | h <;> rw [h] at hj ⊢ <;> omega

/-! ### Assembly on the Freudenthal mesh of a box -/

/-- The Kuhn vertices as lattice vectors: coordinate `k` of `vⱼ` is `1` iff `σ⁻¹ k < j`. -/
def kuhnLattice (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) : Fin n → ℤ :=
  fun k => if (σ.symm k : ℕ) < j then 1 else 0

theorem latticePoint_kuhnLattice (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    latticePoint (kuhnLattice σ j) = kuhnVertex σ j := by
  funext k; simp only [latticePoint_apply, kuhnLattice, kuhnVertex]; split_ifs <;> simp

theorem kuhnLattice_mem (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) (k : Fin n) :
    kuhnLattice σ j k = 0 ∨ kuhnLattice σ j k = 1 := by
  simp only [kuhnLattice]; split_ifs <;> simp

/-- `v_{k+1} = v_k + e_{σ k}`. -/
theorem kuhnLattice_succ (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    kuhnLattice σ k.succ = kuhnLattice σ k.castSucc + Pi.single (σ k) 1 := by
  funext i
  simp only [kuhnLattice, Fin.val_succ, Fin.val_castSucc, Pi.add_apply]
  by_cases hi : i = σ k
  · subst hi; simp
  · have : (σ.symm i : ℕ) ≠ k := fun e => hi (by rw [← Fin.ext e]; simp)
    rw [Pi.single_eq_of_ne hi]
    split_ifs <;> first | rfl | omega

theorem kuhnLattice_symm_self (σ : Equiv.Perm (Fin n)) (l : Fin n) :
    kuhnLattice σ (σ.symm l).castSucc l = 0 := by
  simp [kuhnLattice]

theorem freudenthalPoints_eq_node (b : Fin n → ℝ) (h : ℝ) (m : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    freudenthalPoints b h m σ j = node b h (m + kuhnLattice σ j) := by
  funext i
  simp [freudenthalPoints, node, ← latticePoint_kuhnLattice, mul_add]

/-- The edge term `Dₗu(q) Dₗw(q)` of the difference quotients along `q → q + eₗ`. -/
def edgeTerm (b : Fin n → ℝ) (h : ℝ) (u w : (Fin n → ℝ) → ℝ) (l : Fin n) (q : Fin n → ℤ) : ℝ :=
  (u (node b h (q + Pi.single l 1)) - u (node b h q)) / h *
    ((w (node b h (q + Pi.single l 1)) - w (node b h q)) / h)

/-- **The element stiffness of a Freudenthal simplex**: `∇Πₜu · ∇Πₜw = Σₗ Dₗu Dₗw` over the `n`
path edges `v_k → v_k + eₗ` (`k = σ⁻¹ l`); the other edges carry no coupling. -/
theorem p1Grad_dotProduct_freudenthalPoints (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0)
    (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) (u w : (Fin n → ℝ) → ℝ) :
    p1Grad (freudenthalPoints b h m σ) u ⬝ᵥ p1Grad (freudenthalPoints b h m σ) w =
      ∑ l, edgeTerm b h u w l (m + kuhnLattice σ (σ.symm l).castSucc) := by
  refine sum_congr rfl fun l _ => ?_
  have e : freudenthalPoints b h m σ (σ.symm l).succ =
      node b h (m + kuhnLattice σ (σ.symm l).castSucc + Pi.single l 1) := by
    rw [freudenthalPoints_eq_node, kuhnLattice_succ, Equiv.apply_symm_apply, add_assoc]
  rw [p1Grad_freudenthalPoints b hh, p1Grad_freudenthalPoints b hh, e, freudenthalPoints_eq_node]
  rfl

open Classical in
theorem freudenthalMesh_simplices (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N] :
    (freudenthalMesh b s hs N).simplices = univ.image fun p : (Fin n → Fin N) ×
      Equiv.Perm (Fin n) => mapEquiv (boxMap b (s / N) (freudenthalScale_ne_zero hs N))
        (freudenthalSimplex (finLattice p.1) p.2) := by
  ext T
  rw [mem_freudenthalMesh_simplices, mem_image]
  simp

/-- The vertices of the Freudenthal mesh are lattice nodes. -/
theorem exists_eq_node_of_mem_vertexSet (b : Fin n → ℝ) {s : ℝ} {hs : 0 < s} {N : ℕ} [NeZero N]
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (freudenthalMesh b s hs N).simplices)
    {y : Fin n → ℝ} (hy : y ∈ vertexSet T) : ∃ q, y = node b (s / N) q := by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  obtain ⟨j, rfl⟩ := mem_vertexSet.1 hy
  exact ⟨_, by rw [mapEquiv_boxMap_freudenthalSimplex_points, freudenthalPoints_eq_node]⟩

theorem injective_freudenthalMesh_simplex (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) (N : ℕ) :
    Function.Injective fun p : (Fin n → Fin N) × Equiv.Perm (Fin n) =>
      mapEquiv (boxMap b h hh) (freudenthalSimplex (finLattice p.1) p.2) := by
  rintro ⟨m, σ⟩ ⟨m', σ'⟩ e
  have hc := congrArg Affine.Simplex.closedInterior e
  simp only [closedInterior_mapEquiv] at hc
  obtain ⟨h1, h2⟩ := freudenthalSimplex_eq_of_closedInterior_eq
    ((boxMap b h hh).injective.image_injective hc)
  have : m = m' := funext fun j => Fin.ext (by
    have := congrFun h1 j; simp only [finLattice, Nat.cast_inj] at this; exact this)
  rw [this, h2]

/-- `|b + h (m + K_σ)| = hⁿ / n!`. -/
theorem volume_real_freudenthalMesh_simplex (b : Fin n → ℝ) {h : ℝ} (hh : 0 < h)
    (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    volume.real (mapEquiv (boxMap b h hh.ne') (freudenthalSimplex m σ)).closedInterior =
      h ^ n / n.factorial := by
  have e : mapEquiv (boxMap b h hh.ne') (freudenthalSimplex m σ) =
      mapEquiv (boxMap (b + h • latticePoint m) h hh.ne') (kuhnSimplex σ) := by
    refine Affine.Simplex.ext fun j => ?_
    simp [smul_add, add_assoc]
  have h1 := integral_closedInterior_mapEquiv_boxMap (kuhnSimplex σ) (b + h • latticePoint m) hh
    (fun _ => (1 : ℝ))
  rw [setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h1
  rw [e, h1, Measure.real, volume_closedInterior_kuhnSimplex]
  simp [div_eq_mul_inv]

open Classical in
theorem sum_freudenthalMesh_simplices (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N]
    (f : Affine.Simplex ℝ (Fin n → ℝ) n → ℝ) :
    ∑ T ∈ (freudenthalMesh b s hs N).simplices, f T = ∑ m : Fin n → Fin N, ∑ σ,
      f (mapEquiv (boxMap b (s / N) (freudenthalScale_ne_zero hs N))
        (freudenthalSimplex (finLattice m) σ)) := by
  rw [freudenthalMesh_simplices, sum_image fun p _ p' _ e =>
    injective_freudenthalMesh_simplex b _ N e, ← Finset.univ_product_univ, sum_product]

theorem freudenthalScale_pos {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N] : 0 < s / N :=
  div_pos hs (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))

/-- **The `P₁` stiffness form on the Freudenthal mesh** of the box `b + (0, s)ⁿ` at level `N`
(`h = s / N`): for nodal values `u` vanishing on the boundary,
`a(u, w) = hⁿ Σₗ Σ_{q → q + eₗ} Dₗu(q) Dₗw(q)` over the axis edges with an interior endpoint.
Every such edge is the path edge `v_{σ⁻¹ l} → v_{σ⁻¹ l + 1}` of exactly one simplex
`b + h (m + K_σ)` for each `σ` (`sum_finLattice_add`), and `|T| = hⁿ / n!`. -/
theorem p1Stiffness_freudenthalMesh (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N]
    {u : (Fin n → ℝ) → ℝ} (hu : VanishesOnBoundary b (s / N) N u) (w : (Fin n → ℝ) → ℝ) :
    p1Stiffness (freudenthalMesh b s hs N) u w =
      (s / N) ^ n * ∑ l, ∑ q ∈ edgeBases n N l, edgeTerm b (s / N) u w l q := by
  have hh := freudenthalScale_pos hs N
  rw [p1Stiffness_eq, sum_freudenthalMesh_simplices]
  simp_rw [volume_real_freudenthalMesh_simplex b hh, mapEquiv_boxMap_freudenthalSimplex_points,
    p1Grad_dotProduct_freudenthalPoints b hh.ne', mul_sum]
  rw [sum_comm]
  simp_rw [sum_comm (s := (univ : Finset (Fin n → Fin N))) (t := (univ : Finset (Fin n))),
    ← mul_sum]
  have hshift : ∀ σ : Equiv.Perm (Fin n), ∀ l, ∑ m : Fin n → Fin N,
      edgeTerm b (s / N) u w l (finLattice m + kuhnLattice σ (σ.symm l).castSucc) =
        ∑ q ∈ edgeBases n N l, edgeTerm b (s / N) u w l q := fun σ l =>
    sum_finLattice_add l (kuhnLattice_mem σ _) (kuhnLattice_symm_self σ l) _
      fun q hq hql ⟨j, hjl, hj⟩ => by
        have h0 : u (node b (s / N) q) = 0 := hu q hq ⟨j, hj⟩
        have h1 : u (node b (s / N) (q + Pi.single l 1)) = 0 := hu _ (fun i => by
          by_cases hi : i = l
          · subst hi; simp; have := hq i; omega
          · simp [Pi.single_eq_of_ne hi, hq i]) ⟨j, by simpa [Pi.single_eq_of_ne hjl] using hj⟩
        simp [edgeTerm, h0, h1]
  simp_rw [hshift, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, div_mul_cancel₀ _ (by exact_mod_cast n.factorial_ne_zero :
    (n.factorial : ℝ) ≠ 0)]

/-- An interior node `p` is reached from exactly one cell `m` by every `0/1` shift `a`. -/
theorem sum_finLattice_add_ite {N : ℕ} {a : Fin n → ℤ} (ha : ∀ j, a j = 0 ∨ a j = 1)
    {p : Fin n → ℤ} (hp : p ∈ interiorNodes n N) :
    ∑ m : Fin n → Fin N, (if finLattice m + a = p then 1 else 0 : ℝ) = 1 := by
  rw [interiorNodes, Fintype.mem_piFinset] at hp
  have hb : ∀ j, 0 ≤ p j - a j ∧ p j - a j < N := fun j => by
    have := mem_Ioo.1 (hp j); rcases ha j with h | h <;> rw [h] <;> omega
  set m₀ : Fin n → Fin N := fun j => ⟨(p j - a j).toNat, by have := hb j; omega⟩
  have key : ∀ m, finLattice m + a = p ↔ m = m₀ := fun m => by
    constructor
    · intro e; funext j; apply Fin.ext
      have := congrFun e j; have := hb j
      simp only [Pi.add_apply, finLattice, m₀] at *; omega
    · rintro rfl; funext j; have := hb j; simp only [Pi.add_apply, finLattice, m₀]; omega
  simp_rw [key]
  simp

theorem interiorNodes_subset_edgeBases (N : ℕ) (l : Fin n) :
    interiorNodes n N ⊆ edgeBases n N l := fun p hp => by
  rw [interiorNodes, Fintype.mem_piFinset] at hp
  rw [edgeBases, Fintype.mem_piFinset]
  intro j
  have := mem_Ioo.1 (hp j)
  split_ifs
  · exact mem_Ico.2 ⟨this.1.le, this.2⟩
  · exact hp j

/-- **The lumped mass of the Freudenthal mesh**: `m(x) = hⁿ` at every interior node, `(n + 1)!`
simplices of volume `hⁿ / n!` meeting there (`n + 1` vertex positions for each `σ`). -/
theorem lumpedMass_freudenthalMesh (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N]
    {p : Fin n → ℤ} (hp : p ∈ interiorNodes n N) :
    lumpedMass (freudenthalMesh b s hs N) (node b (s / N) p) = (s / N) ^ n := by
  have hh := freudenthalScale_pos hs N
  rw [lumpedMass, sum_freudenthalMesh_simplices]
  simp_rw [volume_real_freudenthalMesh_simplex b hh, mapEquiv_boxMap_freudenthalSimplex_points,
    freudenthalPoints_eq_node, (node_injective b hh.ne').eq_iff, card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ← mul_sum]
  rw [sum_comm]
  have hσ : ∀ σ : Equiv.Perm (Fin n), ∑ m : Fin n → Fin N,
      ∑ j, (if finLattice m + kuhnLattice σ j = p then 1 else 0 : ℝ) = n + 1 := fun σ => by
    rw [sum_comm, sum_congr rfl fun j _ => sum_finLattice_add_ite (kuhnLattice_mem σ j) hp]
    simp
  rw [sum_congr rfl fun σ _ => hσ σ]
  simp only [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem nodalIndicator_node (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) (p q : Fin n → ℤ) :
    nodalIndicator (node b h p) (node b h q) = if q = p then 1 else 0 := by
  simp [nodalIndicator, (node_injective b hh).eq_iff]

/-- The hat function of an interior node vanishes on the boundary. -/
theorem vanishesOnBoundary_nodalIndicator (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) {N : ℕ}
    {p : Fin n → ℤ} (hp : p ∈ interiorNodes n N) :
    VanishesOnBoundary b h N (nodalIndicator (node b h p)) := by
  rintro q - ⟨j, hj⟩
  rw [nodalIndicator_node b hh, ite_eq_right]
  rintro rfl
  rw [interiorNodes, Fintype.mem_piFinset] at hp
  have := mem_Ioo.1 (hp j)
  omega

theorem sub_single_mem_edgeBases {N : ℕ} {p : Fin n → ℤ} (hp : p ∈ interiorNodes n N)
    (l : Fin n) : p - Pi.single l 1 ∈ edgeBases n N l := by
  rw [interiorNodes, Fintype.mem_piFinset] at hp
  rw [edgeBases, Fintype.mem_piFinset]
  intro j
  have := mem_Ioo.1 (hp j)
  by_cases hj : j = l
  · subst hj; simp only [ite_true, Pi.sub_apply, Pi.single_eq_same, mem_Ico]; omega
  · simpa [hj, Pi.single_eq_of_ne hj] using hp j

/-- **The stiffness row of an interior node**: `a(φₚ, w) = hⁿ Σₗ (2 w(p) - w(p + eₗ) - w(p - eₗ)) / h²`
on the Freudenthal mesh. -/
theorem p1Stiffness_nodalIndicator_freudenthalMesh (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ)
    [NeZero N] {p : Fin n → ℤ} (hp : p ∈ interiorNodes n N) (w : (Fin n → ℝ) → ℝ) :
    p1Stiffness (freudenthalMesh b s hs N) (nodalIndicator (node b (s / N) p)) w =
      (s / N) ^ n * ∑ l, (2 * w (node b (s / N) p) - w (node b (s / N) (p + Pi.single l 1)) -
        w (node b (s / N) (p - Pi.single l 1))) / (s / N) ^ 2 := by
  have hh := (freudenthalScale_pos hs N).ne'
  rw [p1Stiffness_freudenthalMesh b hs N (vanishesOnBoundary_nodalIndicator b hh hp) w]
  congr 1
  refine sum_congr rfl fun l _ => ?_
  set X : (Fin n → ℤ) → ℝ := fun q =>
    (w (node b (s / N) (q + Pi.single l 1)) - w (node b (s / N) q)) / (s / N) / (s / N)
  have e : ∀ q, edgeTerm b (s / N) (nodalIndicator (node b (s / N) p)) w l q =
      (if q = p - Pi.single l 1 then X q else 0) - (if q = p then X q else 0) := fun q => by
    simp only [edgeTerm, nodalIndicator_node b hh, ← eq_sub_iff_add_eq, X]
    split_ifs <;> ring
  simp_rw [e, sum_sub_distrib, sum_ite_eq', ite_eq_left (sub_single_mem_edgeBases hp l),
    ite_eq_left (interiorNodes_subset_edgeBases N l hp), X, sub_add_cancel]
  field_simp
  ring

/-- **The lumped-mass `P₁` Laplacian on the Freudenthal mesh is the `(2n + 1)`-point difference
Laplacian**: at every interior node `p`,
`-a(φₚ, w) / m(p) = Σₗ (w(p + h eₗ) - 2 w(p) + w(p - h eₗ)) / h²`. [Thomee2006], Ch. 15 -/
theorem neg_p1Stiffness_div_lumpedMass (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N]
    {p : Fin n → ℤ} (hp : p ∈ interiorNodes n N) (w : (Fin n → ℝ) → ℝ) :
    -p1Stiffness (freudenthalMesh b s hs N) (nodalIndicator (node b (s / N) p)) w /
        lumpedMass (freudenthalMesh b s hs N) (node b (s / N) p) =
      ∑ l, (w (node b (s / N) (p + Pi.single l 1)) - 2 * w (node b (s / N) p) +
        w (node b (s / N) (p - Pi.single l 1))) / (s / N) ^ 2 := by
  have hh := (freudenthalScale_pos hs N).ne'
  rw [p1Stiffness_nodalIndicator_freudenthalMesh b hs N hp, lumpedMass_freudenthalMesh b hs N hp,
    neg_div, mul_div_cancel_left₀ _ (pow_ne_zero n hh), ← sum_neg_distrib]
  refine sum_congr rfl fun l _ => ?_
  ring

end Feec.FiniteElement
