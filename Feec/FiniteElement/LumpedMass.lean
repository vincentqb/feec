module

public import Feec.FiniteElement.InverseEstimate

/-!
# Lumped-mass `P₁` finite elements on Freudenthal meshes: the difference stencil

The `P₁` stiffness form and the lumped mass define the lumped-mass `P₁` Laplacian ([Thomee2006],
Ch. 15); on the non-obtuse Freudenthal meshes it is the `(2n + 1)`-point difference Laplacian.

## Main results

* `p1Stiffness_indicator_nonpos`: nonpositive off-diagonal stiffness on non-obtuse meshes.
* `isNonobtuse_freudenthalMesh`: the Freudenthal meshes are non-obtuse.
* `neg_p1Stiffness_div_lumpedMass`: the `(2n + 1)`-point difference Laplacian at interior nodes.

## References

* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MeasureTheory

@[expose] public noncomputable section

namespace Feec.FiniteElement

open Feec.Mesh

variable {n : ℕ}

/-! ### `P₁` interpolation, stiffness and lumped mass on a mesh -/

/-- The gradient `∇Πₜu = Σⱼ u(pⱼ) ∇λⱼ` of the `P₁` interpolant of `u` on the simplex `p`. -/
def p1Grad (p : Fin (n + 1) → Fin n → ℝ) : ((Fin n → ℝ) → ℝ) →ₗ[ℝ] Fin n → ℝ :=
  ∑ j, (LinearMap.proj (p j)).smulRight (baryGrad p j)

theorem p1Grad_apply (p : Fin (n + 1) → Fin n → ℝ) (u : (Fin n → ℝ) → ℝ) :
    p1Grad p u = ∑ j, u (p j) • baryGrad p j := by
  simp [p1Grad]

/-- The `P₁` interpolant `Πₜu = Σⱼ u(pⱼ) λⱼ` of the nodal values `u` on the simplex `p`. -/
def p1Interp (p : Fin (n + 1) → Fin n → ℝ) : ((Fin n → ℝ) → ℝ) →ₗ[ℝ] (Fin n → ℝ) → ℝ :=
  ∑ j, (LinearMap.proj (p j)).smulRight fun x => baryCoord p x j

theorem p1Interp_apply (p : Fin (n + 1) → Fin n → ℝ) (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    p1Interp p u x = ∑ j, u (p j) * baryCoord p x j := by
  simp [p1Interp]

theorem p1Interp_sub (p : Fin (n + 1) → Fin n → ℝ) (u : (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    p1Interp p u x - p1Interp p u y = p1Grad p u ⬝ᵥ (x - y) := by
  simp only [p1Interp_apply, p1Grad_apply, ← sum_sub_distrib, ← mul_sub, baryCoord_sub, dotProduct,
    Pi.sub_apply, mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem p1Interp_vertex {p : Fin (n + 1) → Fin n → ℝ} (hp : IsUnit (edgeMatrix p).det)
    (u : (Fin n → ℝ) → ℝ) (j : Fin (n + 1)) : p1Interp p u (p j) = u (p j) := by
  simp [p1Interp_apply, baryCoord_vertex hp]

/-- The `P₁` stiffness form `a(u, w) = Σ_T ∫_T ∇Πₜu · ∇Πₜw` of the mesh `M` on nodal values. -/
def p1Stiffness (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑ T ∈ M.simplices, ∫ _ in T.closedInterior, p1Grad T.points u ⬝ᵥ p1Grad T.points w

theorem p1Stiffness_eq (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) :
    p1Stiffness M u w =
      ∑ T ∈ M.simplices,
        volume.real T.closedInterior * (p1Grad T.points u ⬝ᵥ p1Grad T.points w) := by
  simp [p1Stiffness, smul_eq_mul]

theorem p1Stiffness_comm (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) :
    p1Stiffness M u w = p1Stiffness M w u := by
  simp only [p1Stiffness, dotProduct_comm]

theorem p1Stiffness_sum_smul (M : SimplicialMesh n) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (u : ι → (Fin n → ℝ) → ℝ) (w : (Fin n → ℝ) → ℝ) :
    p1Stiffness M (∑ i ∈ s, c i • u i) w = ∑ i ∈ s, c i * p1Stiffness M (u i) w := by
  simp only [p1Stiffness_eq, map_sum, map_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul,
    mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun T _ => by ring

theorem p1Stiffness_sum_smul_right (M : SimplicialMesh n) {κ : Type*} (s : Finset κ) (c : κ → ℝ)
    (u : (Fin n → ℝ) → ℝ) (w : κ → (Fin n → ℝ) → ℝ) :
    p1Stiffness M u (∑ i ∈ s, c i • w i) = ∑ i ∈ s, c i * p1Stiffness M u (w i) := by
  rw [p1Stiffness_comm, p1Stiffness_sum_smul]
  simp_rw [p1Stiffness_comm M u]

theorem p1Stiffness_add_right (M : SimplicialMesh n) (u w w' : (Fin n → ℝ) → ℝ) :
    p1Stiffness M u (w + w') = p1Stiffness M u w + p1Stiffness M u w' := by
  simp only [p1Stiffness_eq, map_add, dotProduct_add, mul_add, sum_add_distrib]

theorem p1Stiffness_congr_right (M : SimplicialMesh n) (u : (Fin n → ℝ) → ℝ)
    {w w' : (Fin n → ℝ) → ℝ} (h : ∀ T ∈ M.simplices, ∀ j, w (T.points j) = w' (T.points j)) :
    p1Stiffness M u w = p1Stiffness M u w' := by
  rw [p1Stiffness_eq, p1Stiffness_eq]
  refine sum_congr rfl fun T hT => ?_
  congr 2
  simp only [p1Grad_apply, h T hT]

theorem p1Stiffness_const_right (M : SimplicialMesh n) (u : (Fin n → ℝ) → ℝ) (c : ℝ) :
    p1Stiffness M u (fun _ => c) = 0 := by
  rw [p1Stiffness_eq]
  refine sum_eq_zero fun T _ => ?_
  have : p1Grad T.points (fun _ => c) = 0 := by
    rw [p1Grad_apply, ← smul_sum, sum_baryGrad, smul_zero]
  rw [this, dotProduct_zero, mul_zero]

/-- The lumped mass at `x`: the vertex quadrature `Σ_T |T| / (n + 1) · #{j | pⱼ = x}` of `∫ φₓ`. -/
def lumpedMass (M : SimplicialMesh n) (x : Fin n → ℝ) : ℝ :=
  ∑ T ∈ M.simplices, volume.real T.closedInterior / (n + 1) *
    (#{j | T.points j = x} : ℝ)

theorem lumpedMass_nonneg (M : SimplicialMesh n) (x : Fin n → ℝ) : 0 ≤ lumpedMass M x :=
  sum_nonneg fun _ _ => mul_nonneg (div_nonneg measureReal_nonneg (by positivity))
    (Nat.cast_nonneg _)

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

/-- Non-obtuse meshes have nonpositive off-diagonal stiffness: `a(φₓ, φ_y) ≤ 0` for `x ≠ y`
([CiarletRaviart1973]). -/
theorem p1Stiffness_indicator_nonpos (M : SimplicialMesh n) (hM : IsNonobtuse M)
    {x y : Fin n → ℝ} (hxy : x ≠ y) :
    p1Stiffness M (nodalIndicator x) (nodalIndicator y) ≤ 0 := by
  rw [p1Stiffness_eq]
  refine sum_nonpos fun T hT => mul_nonpos_of_nonneg_of_nonpos measureReal_nonneg ?_
  simp only [p1Grad_apply, nodalIndicator, ite_smul, one_smul, zero_smul, sum_dotProduct,
    dotProduct_sum]
  refine sum_nonpos fun j _ => sum_nonpos fun k _ => ?_
  split_ifs
  · exact hM T hT _ _ fun e => hxy (by subst e; simp_all)
  all_goals simp

/-! ### The Kuhn simplex and its barycentric gradients -/

/-- `s_k = e_{σ(k-1)}` for `1 ≤ k ≤ n`, `0` otherwise: the step `v_k - v_{k-1}` of the Kuhn path. -/
def kuhnStep (σ : Equiv.Perm (Fin n)) (k : ℕ) : Fin n → ℝ :=
  fun l => if (σ.symm l : ℕ) + 1 = k then 1 else 0

/-- The inverse of the Kuhn matrix: row `m` is `e_{σ m} - e_{σ(m+1)}`. -/
def kuhnMatrixInv (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun m l => kuhnStep σ (m + 1) l - kuhnStep σ (m + 2) l

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

theorem sum_ite_val_eq (a : ℕ) (ha : a < n + 1) (f : Fin (n + 1) → ℝ) :
    ∑ j : Fin (n + 1), (if (j : ℕ) = a then f j else 0) = f ⟨a, ha⟩ := by
  rw [Finset.sum_eq_single ⟨a, ha⟩]
  · simp
  · intro c _ hc; rw [ite_eq_right]; intro e; exact hc (Fin.ext e)
  · simp

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
  simp only [p1Grad_apply, baryGrad_freudenthalPoints b hh, Finset.sum_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← mul_sum, sum_sub_distrib,
    sum_ite_val_eq _ (by omega), sum_ite_val_eq _ (by omega), div_eq_inv_mul]
  rfl

theorem baryGrad_dotProduct_freudenthalPoints_nonpos (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0)
    (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) {j k : Fin (n + 1)} (hjk : j ≠ k) :
    baryGrad (freudenthalPoints b h m σ) j ⬝ᵥ baryGrad (freudenthalPoints b h m σ) k ≤ 0 := by
  rw [baryGrad_freudenthalPoints b hh, baryGrad_freudenthalPoints b hh, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
  refine mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) (sum_nonpos fun l _ => ?_)
  have : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
  simp only [Pi.sub_apply, kuhnStep]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- The Freudenthal meshes are non-obtuse. -/
theorem isNonobtuse_freudenthalMesh (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N] :
    IsNonobtuse (freudenthalMesh b s hs N) := fun T hT j k hjk => by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  rw [mapEquiv_boxMap_freudenthalSimplex_points]
  exact baryGrad_dotProduct_freudenthalPoints_nonpos b (freudenthalScale_ne_zero hs N) _ _ hjk

/-! ### Lattice nodes -/

/-- The lattice node `b + h q`. -/
def node (b : Fin n → ℝ) (h : ℝ) (q : Fin n → ℤ) : Fin n → ℝ := b + h • latticePoint q

@[simp] theorem node_coord (b : Fin n → ℝ) (h : ℝ) (q : Fin n → ℤ) (l : Fin n) :
    node b h q l = b l + h * q l := by
  simp [node, latticePoint_apply]

theorem node_injective (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) : Function.Injective (node b h) := by
  intro q q' e
  funext i
  have := congrFun e i
  simp only [node, Pi.add_apply, Pi.smul_apply, latticePoint_apply, smul_eq_mul, add_right_inj,
    mul_eq_mul_left_iff, hh, or_false, Int.cast_inj] at this
  exact this

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

theorem node_add_single_one (b : Fin n → ℝ) (h : ℝ) (q : Fin n → ℤ) (l : Fin n) :
    node b h (q + Pi.single l 1) = node b h q + h • Pi.single l 1 := by
  rw [node_add_single]; simp

theorem node_sub_single_one (b : Fin n → ℝ) (h : ℝ) (q : Fin n → ℤ) (l : Fin n) :
    node b h (q - Pi.single l 1) = node b h q + (-h) • Pi.single l 1 := by
  rw [sub_eq_add_neg, ← Pi.single_neg, node_add_single]; simp

/-- The interior nodes `q ∈ {1, …, N - 1}ⁿ` of the level-`N` lattice. -/
def interiorNodes (n N : ℕ) : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Ioo 0 (N : ℤ)

theorem mem_interiorNodes {N : ℕ} {q : Fin n → ℤ} :
    q ∈ interiorNodes n N ↔ ∀ j, 0 < q j ∧ q j < N := by
  simp [interiorNodes]

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

/-- The edge shift `κ_{σ,l} = v_{σ⁻¹ l}`, the base of the path edge of `K_σ` along `eₗ`. -/
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

/-- `C(p)`: the number of simplices of the level-`N` lattice with vertex `p`. -/
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

theorem upCount_of_mem_interiorNodes (σ : Equiv.Perm (Fin n)) (l : Fin n) {p : Fin n → ℤ}
    (hp : p ∈ interiorNodes n N) : upCount N σ l p = 1 := by
  rw [upCount_eq, ite_eq_left]
  intro i
  have := mem_interiorNodes.1 hp i
  rcases kuhnLattice_mem σ (σ.symm l).castSucc i with h | h <;> rw [edgeShift, h] <;> omega

theorem downCount_of_mem_interiorNodes (σ : Equiv.Perm (Fin n)) (l : Fin n) {p : Fin n → ℤ}
    (hp : p ∈ interiorNodes n N) : downCount N σ l p = 1 := by
  have := mem_interiorNodes.1 hp l
  rw [← upCount_eq_downCount σ (by omega) this.2, upCount_of_mem_interiorNodes σ l hp]

theorem vertexCount_le (p : Fin n → ℤ) : vertexCount N p ≤ (n + 1) * n.factorial := by
  calc vertexCount N p ≤ ∑ _σ : Equiv.Perm (Fin n), ∑ _j : Fin (n + 1), (1 : ℝ) :=
        sum_le_sum fun σ _ => sum_le_sum fun j _ => by
          rw [sum_finLattice_add_ite]; split_ifs <;> norm_num
    _ = _ := by simp [Fintype.card_perm]; ring

theorem vertexCount_of_mem_interiorNodes {p : Fin n → ℤ} (hp : p ∈ interiorNodes n N) :
    vertexCount N p = (n + 1) * n.factorial := by
  have h1 : ∀ σ : Equiv.Perm (Fin n), ∀ j, ∑ m : Fin n → Fin N,
      (if finLattice m + kuhnLattice σ j = p then 1 else 0 : ℝ) = 1 := fun σ j => by
    rw [sum_finLattice_add_ite, ite_eq_left]
    intro i
    have := mem_interiorNodes.1 hp i
    rcases kuhnLattice_mem σ j i with h | h <;> rw [h] <;> omega
  simp [vertexCount, h1, Fintype.card_perm]; ring

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

/-! ### The stiffness form as a sum over the axis edges -/

theorem p1Stiffness_freudenthalMesh_eq (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N]
    (u w : (Fin n → ℝ) → ℝ) :
    p1Stiffness (freudenthalMesh b s hs N) u w =
      (s / N) ^ n / n.factorial * ∑ σ : Equiv.Perm (Fin n), ∑ l, ∑ m : Fin n → Fin N,
        edgeTerm b (s / N) u w l (finLattice m + edgeShift σ l) := by
  have hh := freudenthalScale_pos hs N
  rw [p1Stiffness_eq, sum_freudenthalMesh_simplices]
  simp_rw [volume_real_freudenthalMesh_simplex b hh, mapEquiv_boxMap_freudenthalSimplex_points,
    p1Grad_dotProduct_freudenthalPoints b hh.ne', mul_sum]
  rw [sum_comm]
  simp_rw [sum_comm (s := (univ : Finset (Fin n → Fin N))) (t := (univ : Finset (Fin n)))]
  rfl

/-- The base points `q` of the axis edges `q → q + eₗ` through the open box `(0, N)ⁿ`. -/
def edgeBases (n N : ℕ) (l : Fin n) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun j => if j = l then Ico 0 (N : ℤ) else Ioo 0 (N : ℤ)

/-- The nodal values `u` vanish at the boundary nodes of the level-`N` lattice of `b + h ℤⁿ`. -/
def VanishesOnBoundary (b : Fin n → ℝ) (h : ℝ) (N : ℕ) (u : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ q : Fin n → ℤ, (∀ j, 0 ≤ q j ∧ q j ≤ (N : ℤ)) → (∃ j, q j = 0 ∨ q j = (N : ℤ)) →
    u (node b h q) = 0

theorem sum_edgeTerm_edgeShift (b : Fin n → ℝ) (h : ℝ) {N : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : VanishesOnBoundary b h N u) (w : (Fin n → ℝ) → ℝ) (σ : Equiv.Perm (Fin n))
    (l : Fin n) :
    ∑ m : Fin n → Fin N, edgeTerm b h u w l (finLattice m + edgeShift σ l) =
      ∑ q ∈ edgeBases n N l, edgeTerm b h u w l q := by
  set a := edgeShift σ l
  have ha : ∀ i, a i = 0 ∨ a i = 1 := kuhnLattice_mem σ _
  have hal : a l = 0 := edgeShift_self σ l
  have hE : ∀ q ∈ edgeBases n N l,
      ∑ m : Fin n → Fin N, (if finLattice m + a = q then 1 else 0 : ℝ) = 1 := fun q hq => by
    rw [sum_finLattice_add_ite, ite_eq_left]
    intro i
    have := Fintype.mem_piFinset.1 hq i
    by_cases hi : i = l
    · subst hi; rw [ite_eq_left rfl, mem_Ico] at this; omega
    · rw [ite_eq_right hi, mem_Ioo] at this; rcases ha i with e | e <;> rw [e] <;> omega
  have hG : ∀ m : Fin n → Fin N, finLattice m + a ∉ edgeBases n N l →
      edgeTerm b h u w l (finLattice m + a) = 0 := fun m hm => by
    set q := finLattice m + a
    have hb : ∀ i, 0 ≤ q i ∧ q i ≤ N := fun i => by
      have := (m i).2; simp only [q, Pi.add_apply, finLattice]; rcases ha i with e | e <;> omega
    have hql : q l < N := by
      have := (m l).2; simp only [q, Pi.add_apply, finLattice, hal]; omega
    obtain ⟨j, hj⟩ := not_forall.1 (mt Fintype.mem_piFinset.2 hm)
    have hjl : j ≠ l := fun e => by
      subst e; rw [ite_eq_left rfl, mem_Ico] at hj; exact hj ⟨(hb j).1, hql⟩
    rw [ite_eq_right hjl, mem_Ioo] at hj
    have h0 := hu q hb ⟨j, by have := hb j; omega⟩
    have h1 := hu (q + Pi.single l 1) (fun i => by
      by_cases hi : i = l
      · subst hi; simp; have := hb i; omega
      · simp [Pi.single_eq_of_ne hi, hb i])
      ⟨j, by simp [Pi.single_eq_of_ne hjl]; have := hb j; omega⟩
    simp [edgeTerm, h0, h1]
  calc ∑ m : Fin n → Fin N, edgeTerm b h u w l (finLattice m + a)
      = ∑ m : Fin n → Fin N, ∑ q ∈ edgeBases n N l,
          (if finLattice m + a = q then 1 else 0 : ℝ) * edgeTerm b h u w l q :=
        sum_congr rfl fun m _ => by
          simp_rw [boole_mul, sum_ite_eq]
          split_ifs with hm
          · rfl
          · exact hG m hm
    _ = _ := by
        rw [sum_comm]
        exact sum_congr rfl fun q hq => by rw [← sum_mul, hE q hq, one_mul]

theorem p1Stiffness_freudenthalMesh (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N]
    {u : (Fin n → ℝ) → ℝ} (hu : VanishesOnBoundary b (s / N) N u) (w : (Fin n → ℝ) → ℝ) :
    p1Stiffness (freudenthalMesh b s hs N) u w =
      (s / N) ^ n * ∑ l, ∑ q ∈ edgeBases n N l, edgeTerm b (s / N) u w l q := by
  simp_rw [p1Stiffness_freudenthalMesh_eq, sum_edgeTerm_edgeShift b _ hu, sum_const, card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, div_mul_cancel₀ _ (by positivity)]

/-! ### The stiffness rows and the lumped masses -/

/-- The difference quotient `(w(q + eₗ) - w(q)) / h²` along the edge `q → q + eₗ`. -/
def edgeQuot (b : Fin n → ℝ) (h : ℝ) (w : (Fin n → ℝ) → ℝ) (l : Fin n) (q : Fin n → ℤ) : ℝ :=
  (w (node b h (q + Pi.single l 1)) - w (node b h q)) / h / h

theorem p1Stiffness_nodalIndicator_eq (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N]
    (p : Fin n → ℤ) (w : (Fin n → ℝ) → ℝ) :
    p1Stiffness (freudenthalMesh b s hs N) (nodalIndicator (node b (s / N) p)) w =
      (s / N) ^ n / n.factorial * ∑ σ : Equiv.Perm (Fin n), ∑ l,
        (downCount N σ l p * edgeQuot b (s / N) w l (p - Pi.single l 1) -
          upCount N σ l p * edgeQuot b (s / N) w l p) := by
  have hh' := (freudenthalScale_pos hs N).ne'
  rw [p1Stiffness_freudenthalMesh_eq]
  congr 1
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
  simp_rw [e, sum_sub_distrib, ← sum_mul]
  rfl

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

theorem lumpedMass_freudenthalMesh (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N]
    {p : Fin n → ℤ} (hp : p ∈ interiorNodes n N) :
    lumpedMass (freudenthalMesh b s hs N) (node b (s / N) p) = (s / N) ^ n := by
  rw [lumpedMass_node_eq, vertexCount_of_mem_interiorNodes hp]
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- At every interior node `p` of the Freudenthal mesh, `-a(φₚ, w) / m(p)` is the `(2n + 1)`-point
difference Laplacian `Σₗ (w(p + h eₗ) - 2 w(p) + w(p - h eₗ)) / h²` ([Thomee2006], Ch. 15). -/
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
