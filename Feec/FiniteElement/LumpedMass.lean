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
* `baryGrad_freudenthalPoints`: on a Freudenthal simplex `b + h (m + K_σ)` with vertices
  `vⱼ = Σ_{i<j} e_{σ i}`, `∇λⱼ = h⁻¹ (e_{σ(j-1)} - e_{σ j})`, so (`p1Grad_freudenthalPoints`)
  `∂ₗ Πₜu = (u(v_{k+1}) - u(v_k)) / h` along the edge `v_k → v_{k+1} = v_k + h eₗ`,
  `k = σ⁻¹ l`; the element stiffness matrix is `hⁿ⁻² / n!` times the Laplacian of the path
  `v₀ - v₁ - ⋯ - vₙ` (`baryGrad_dotProduct_freudenthalPoints_nonpos`: **Freudenthal simplices are
  non-obtuse**);
* **`p1Stiffness_nodalIndicator_eq`**, `lumpedMass_node_eq`: on the level-`N` Freudenthal mesh
  of a box (`h = s / N`), at every lattice node `p`, boundary nodes included,
  `a(φₚ, w) = hⁿ / n! Σ_σ Σₗ (α⁻ Dₗw(p - eₗ) - α⁺ Dₗw(p)) / h` with the difference quotients
  `Dₗw(q) = (w(q + eₗ) - w(q)) / h` and `α±_{σ,l}(p) ∈ {0, 1}` recording whether the path edge
  `p → p ± eₗ` of the Kuhn simplex `σ` lies in the mesh (`upCount`, `downCount`), and
  `m(p) = hⁿ C(p) / (n + 1)!`, `C(p)` the number of simplices at `p` (`vertexCount`): each
  simplex has volume `hⁿ / n!` and couples only the vertices of its path edges;
* `lumpedMass_freudenthalMesh`: `m(x) = hⁿ` at every interior node (`α± = 1`,
  `C = (n + 1)!`);
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

section nodalFun

variable {ι : Type*} [Fintype ι]

/-- The nodal function on `ℝⁿ` with values `U` at the nodes `x` and `0` elsewhere. -/
def nodalFun (x : ι → Fin n → ℝ) (U : ι → ℝ) : (Fin n → ℝ) → ℝ :=
  fun y => ∑ q, if x q = y then U q else 0

theorem nodalFun_apply {x : ι → Fin n → ℝ} (hx : Function.Injective x) (U : ι → ℝ) (q : ι) :
    nodalFun x U (x q) = U q := by
  classical
  simp only [nodalFun, hx.eq_iff]
  rw [Finset.sum_eq_single q (fun c _ hc => by simp [hc]) (by simp)]
  simp

theorem nodalFun_eq_sum (x : ι → Fin n → ℝ) (U : ι → ℝ) :
    nodalFun x U = ∑ q, U q • nodalIndicator (x q) := by
  funext y
  simp [nodalFun, nodalIndicator, Finset.sum_apply, eq_comm]

end nodalFun

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

/-! ### Lattice nodes -/

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

theorem nodalIndicator_node (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) (p q : Fin n → ℤ) :
    nodalIndicator (node b h p) (node b h q) = if q = p then 1 else 0 := by
  simp [nodalIndicator, (node_injective b hh).eq_iff]

/-! ### Counting the simplices at a node -/

/-- The cell `m` with `m + a = q` is unique, and exists iff `0 ≤ q - a < N`. -/
theorem sum_finLattice_add_ite {N : ℕ} (a q : Fin n → ℤ) :
    ∑ m : Fin n → Fin N, (if finLattice m + a = q then 1 else 0 : ℝ) =
      if ∀ i, 0 ≤ q i - a i ∧ q i - a i < N then 1 else 0 := by
  split_ifs with h
  · set m₀ : Fin n → Fin N := fun j => ⟨(q j - a j).toNat, by have := h j; omega⟩
    have key : ∀ m, finLattice m + a = q ↔ m = m₀ := fun m => by
      constructor
      · intro e; funext j; apply Fin.ext
        have := congrFun e j; have := h j
        simp only [Pi.add_apply, finLattice, m₀] at *; omega
      · rintro rfl; funext j; have := h j; simp only [Pi.add_apply, finLattice, m₀]; omega
    simp_rw [key]
    simp
  · refine sum_eq_zero fun m _ => ?_
    rw [ite_eq_right]
    intro e
    refine absurd (fun i => ?_) h
    have := congrFun e i
    have := (m i).2
    simp only [Pi.add_apply, finLattice] at *
    omega

/-- The edge shift `κ_{σ,l} = v_{σ⁻¹ l}`: the path edge of the Kuhn simplex `σ` along `eₗ` is
`v_{σ⁻¹ l} → v_{σ⁻¹ l} + eₗ`. -/
def edgeShift (σ : Equiv.Perm (Fin n)) (l : Fin n) : Fin n → ℤ :=
  kuhnLattice σ (σ.symm l).castSucc

theorem edgeShift_self (σ : Equiv.Perm (Fin n)) (l : Fin n) : edgeShift σ l l = 0 :=
  kuhnLattice_symm_self σ l

/-- `α⁺_{σ,l}(p)`: the simplex `σ` of the level-`N` lattice with path edge `p → p + eₗ` exists. -/
def upCount (N : ℕ) (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) : ℝ :=
  ∑ m : Fin n → Fin N, if finLattice m + edgeShift σ l = p then 1 else 0

/-- `α⁻_{σ,l}(p)`: the simplex `σ` with path edge `p - eₗ → p` exists. -/
def downCount (N : ℕ) (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) : ℝ :=
  upCount N σ l (p - Pi.single l 1)

/-- `C(p)`: the number of pairs (simplex `m + K_σ` of the level-`N` lattice, vertex index `j`)
with `m + v_j = p`, i.e. the simplices with vertex `p` (each once, the `vⱼ` being distinct); the
lumped mass is `m(p) = hⁿ C(p) / (n + 1)!` (`lumpedMass_node_eq`). -/
def vertexCount (N : ℕ) (p : Fin n → ℤ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∑ j, ∑ m : Fin n → Fin N,
    if finLattice m + kuhnLattice σ j = p then 1 else 0

section counting

variable {N : ℕ}

theorem upCount_eq (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) :
    upCount N σ l p =
      if ∀ i, 0 ≤ p i - edgeShift σ l i ∧ p i - edgeShift σ l i < N then 1 else 0 :=
  sum_finLattice_add_ite _ _

theorem upCount_nonneg (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) :
    0 ≤ upCount N σ l p := by
  rw [upCount_eq]; split_ifs <;> norm_num

theorem upCount_le_one (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) :
    upCount N σ l p ≤ 1 := by
  rw [upCount_eq]; split_ifs <;> norm_num

/-- **Interior directions are symmetric**: for `1 ≤ pₗ < N`, `α⁺_{σ,l}(p) = α⁻_{σ,l}(p)`. -/
theorem upCount_eq_downCount (σ : Equiv.Perm (Fin n)) {l : Fin n} {p : Fin n → ℤ}
    (h1 : 1 ≤ p l) (h2 : p l < N) : upCount N σ l p = downCount N σ l p := by
  rw [downCount, upCount_eq, upCount_eq]
  congr 1
  refine propext (forall_congr' fun i => ?_)
  by_cases hi : i = l
  · subst hi; simp [edgeShift_self]; omega
  · simp [hi]

theorem downCount_eq_zero (σ : Equiv.Perm (Fin n)) {l : Fin n} {p : Fin n → ℤ}
    (h : p l = 0) : downCount N σ l p = 0 := by
  rw [downCount, upCount_eq, ite_eq_right]
  intro H
  have := (H l).1
  simp [edgeShift_self, h] at this

theorem upCount_eq_zero (σ : Equiv.Perm (Fin n)) {l : Fin n} {p : Fin n → ℤ}
    (h : p l = N) : upCount N σ l p = 0 := by
  rw [upCount_eq, ite_eq_right]
  intro H
  have := (H l).2
  simp [edgeShift_self, h] at this

/-- At an interior node, every path edge `p → p + eₗ` lies in the mesh. -/
theorem upCount_of_mem_interiorNodes (σ : Equiv.Perm (Fin n)) (l : Fin n) {p : Fin n → ℤ}
    (hp : p ∈ interiorNodes n N) : upCount N σ l p = 1 := by
  rw [upCount_eq, ite_eq_left]
  intro i
  have := mem_Ioo.1 (Fintype.mem_piFinset.1 hp i)
  rcases kuhnLattice_mem σ (σ.symm l).castSucc i with h | h <;> rw [edgeShift, h] <;> omega

/-- At an interior node, every path edge `p - eₗ → p` lies in the mesh. -/
theorem downCount_of_mem_interiorNodes (σ : Equiv.Perm (Fin n)) (l : Fin n) {p : Fin n → ℤ}
    (hp : p ∈ interiorNodes n N) : downCount N σ l p = 1 := by
  have := mem_Ioo.1 (Fintype.mem_piFinset.1 hp l)
  rw [← upCount_eq_downCount σ (by omega) this.2, upCount_of_mem_interiorNodes σ l hp]

theorem vertexCount_le (p : Fin n → ℤ) : vertexCount N p ≤ (n + 1) * n.factorial := by
  calc vertexCount N p ≤ ∑ _σ : Equiv.Perm (Fin n), ∑ _j : Fin (n + 1), (1 : ℝ) :=
        sum_le_sum fun σ _ => sum_le_sum fun j _ => by
          rw [sum_finLattice_add_ite]; split_ifs <;> norm_num
    _ = _ := by simp [Fintype.card_perm]; ring

/-- `C(p) = (n + 1)!` at an interior node. -/
theorem vertexCount_of_mem_interiorNodes {p : Fin n → ℤ} (hp : p ∈ interiorNodes n N) :
    vertexCount N p = (n + 1) * n.factorial := by
  have h1 : ∀ σ : Equiv.Perm (Fin n), ∀ j, ∑ m : Fin n → Fin N,
      (if finLattice m + kuhnLattice σ j = p then 1 else 0 : ℝ) = 1 := fun σ j => by
    rw [sum_finLattice_add_ite, ite_eq_left]
    intro i
    have := mem_Ioo.1 (Fintype.mem_piFinset.1 hp i)
    rcases kuhnLattice_mem σ j i with h | h <;> rw [h] <;> omega
  simp [vertexCount, h1, Fintype.card_perm]; ring

/-- Every term `#{m | m + v_j = p}` of `C(p)` is at most `C(p)`. -/
theorem le_vertexCount (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) (p : Fin n → ℤ) :
    ∑ m : Fin n → Fin N, (if finLattice m + kuhnLattice σ j = p then 1 else 0 : ℝ) ≤
      vertexCount N p := by
  have h0 : ∀ σ' : Equiv.Perm (Fin n), ∀ j', 0 ≤ ∑ m : Fin n → Fin N,
      (if finLattice m + kuhnLattice σ' j' = p then 1 else 0 : ℝ) := fun _ _ =>
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  exact (single_le_sum (fun j' _ => h0 σ j') (mem_univ j)).trans
    (single_le_sum (f := fun σ' => ∑ j', ∑ m : Fin n → Fin N,
      (if finLattice m + kuhnLattice σ' j' = p then 1 else 0 : ℝ))
      (fun σ' _ => sum_nonneg fun j' _ => h0 σ' j') (mem_univ σ))

theorem upCount_le_vertexCount (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) :
    upCount N σ l p ≤ vertexCount N p :=
  le_vertexCount σ _ p

theorem downCount_le_vertexCount (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) :
    downCount N σ l p ≤ vertexCount N p := by
  have e : downCount N σ l p = ∑ m : Fin n → Fin N,
      (if finLattice m + kuhnLattice σ (σ.symm l).succ = p then 1 else 0 : ℝ) := by
    refine sum_congr rfl fun m _ => ?_
    rw [kuhnLattice_succ, Equiv.apply_symm_apply, edgeShift]
    congr 1
    exact propext ⟨fun h => by rw [← add_assoc, h, sub_add_cancel],
      fun h => by rw [eq_sub_iff_add_eq, add_assoc, h]⟩
  rw [e]
  exact le_vertexCount σ _ p

end counting

/-! ### The stiffness rows and the lumped masses -/

/-- The difference quotient `(w(q + eₗ) - w(q)) / h²` along the edge `q → q + eₗ`. -/
def edgeQuot (b : Fin n → ℝ) (h : ℝ) (w : (Fin n → ℝ) → ℝ) (l : Fin n) (q : Fin n → ℤ) : ℝ :=
  (w (node b h (q + Pi.single l 1)) - w (node b h q)) / h / h

/-- **The stiffness row of any node** `p` (boundary nodes included) of the level-`N` Freudenthal
mesh: `a(φₚ, w) = hⁿ / n! Σ_σ Σₗ (α⁻_{σ,l}(p) Dₗw(p - eₗ) - α⁺_{σ,l}(p) Dₗw(p)) / h`. Every
simplex `b + h (m + K_σ)` couples only the `n` vertices of its path edges
(`p1Grad_dotProduct_freudenthalPoints`), and `|T| = hⁿ / n!`. -/
theorem p1Stiffness_nodalIndicator_eq (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N]
    (p : Fin n → ℤ) (w : (Fin n → ℝ) → ℝ) :
    p1Stiffness (freudenthalMesh b s hs N) (nodalIndicator (node b (s / N) p)) w =
      (s / N) ^ n / n.factorial * ∑ σ : Equiv.Perm (Fin n), ∑ l,
        (downCount N σ l p * edgeQuot b (s / N) w l (p - Pi.single l 1) -
          upCount N σ l p * edgeQuot b (s / N) w l p) := by
  have hh := freudenthalScale_pos hs N
  have hh' := hh.ne'
  rw [p1Stiffness_eq, sum_freudenthalMesh_simplices]
  simp_rw [volume_real_freudenthalMesh_simplex b hh, mapEquiv_boxMap_freudenthalSimplex_points,
    p1Grad_dotProduct_freudenthalPoints b hh', mul_sum]
  rw [sum_comm]
  simp_rw [sum_comm (s := (univ : Finset (Fin n → Fin N))) (t := (univ : Finset (Fin n)))]
  refine sum_congr rfl fun σ _ => sum_congr rfl fun l _ => ?_
  have e : ∀ q, edgeTerm b (s / N) (nodalIndicator (node b (s / N) p)) w l q =
      (if q = p - Pi.single l 1 then 1 else 0) * edgeQuot b (s / N) w l (p - Pi.single l 1) -
        (if q = p then 1 else 0) * edgeQuot b (s / N) w l p := fun q => by
    have hne : p - Pi.single l 1 ≠ p := fun h => by have := congrFun h l; simp at this
    simp only [edgeTerm, edgeQuot, nodalIndicator_node b hh', ← eq_sub_iff_add_eq]
    by_cases h1 : q = p - Pi.single l 1
    · subst h1; simp [hne]; field_simp
    · by_cases h2 : q = p
      · subst h2; simp [h1]; field_simp
      · simp [h1, h2]
  rw [← mul_sum]
  congr 1
  simp_rw [e, sum_sub_distrib, ← sum_mul]
  rfl

/-- **The lumped mass of any node** of the level-`N` Freudenthal mesh: `m(p) = hⁿ C(p) / (n + 1)!`.
-/
theorem lumpedMass_node_eq (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N]
    (p : Fin n → ℤ) :
    lumpedMass (freudenthalMesh b s hs N) (node b (s / N) p) =
      (s / N) ^ n / n.factorial / (n + 1) * vertexCount N p := by
  have hh := freudenthalScale_pos hs N
  rw [lumpedMass, sum_freudenthalMesh_simplices]
  simp_rw [volume_real_freudenthalMesh_simplex b hh, mapEquiv_boxMap_freudenthalSimplex_points,
    freudenthalPoints_eq_node, (node_injective b hh.ne').eq_iff, card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ← mul_sum]
  rw [vertexCount]
  congr 1
  rw [sum_comm]
  exact sum_congr rfl fun σ _ => sum_comm

/-- **The lumped mass of the Freudenthal mesh**: `m(x) = hⁿ` at every interior node, `(n + 1)!`
simplices of volume `hⁿ / n!` meeting there (`vertexCount_of_mem_interiorNodes`). -/
theorem lumpedMass_freudenthalMesh (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N]
    {p : Fin n → ℤ} (hp : p ∈ interiorNodes n N) :
    lumpedMass (freudenthalMesh b s hs N) (node b (s / N) p) = (s / N) ^ n := by
  rw [lumpedMass_node_eq, vertexCount_of_mem_interiorNodes hp]
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The lumped-mass `P₁` Laplacian on the Freudenthal mesh is the `(2n + 1)`-point difference
Laplacian**: at every interior node `p` (where `α± = 1`, `upCount_of_mem_interiorNodes`),
`-a(φₚ, w) / m(p) = Σₗ (w(p + h eₗ) - 2 w(p) + w(p - h eₗ)) / h²`. [Thomee2006], Ch. 15 -/
theorem neg_p1Stiffness_div_lumpedMass (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N]
    {p : Fin n → ℤ} (hp : p ∈ interiorNodes n N) (w : (Fin n → ℝ) → ℝ) :
    -p1Stiffness (freudenthalMesh b s hs N) (nodalIndicator (node b (s / N) p)) w /
        lumpedMass (freudenthalMesh b s hs N) (node b (s / N) p) =
      ∑ l, (w (node b (s / N) (p + Pi.single l 1)) - 2 * w (node b (s / N) p) +
        w (node b (s / N) (p - Pi.single l 1))) / (s / N) ^ 2 := by
  have hh := (freudenthalScale_pos hs N).ne'
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [p1Stiffness_nodalIndicator_eq, lumpedMass_freudenthalMesh b hs N hp]
  simp_rw [upCount_of_mem_interiorNodes _ _ hp, downCount_of_mem_interiorNodes _ _ hp, one_mul,
    sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, div_mul_cancel₀ _ hf, neg_div, mul_div_cancel_left₀ _ (pow_ne_zero n hh),
    ← sum_neg_distrib]
  refine sum_congr rfl fun l _ => ?_
  simp only [edgeQuot, sub_add_cancel]
  field_simp
  ring

end Feec.FiniteElement
