module

public import Feec.Models.Cube.MaxNormHeat

open Set Finset NormedSpace Feec.Mesh Feec.FiniteElement Feec.TimeStepping MeasureTheory
open Feec.Models.Cube.Geometry (openCube)

/-!
# The heat equation with natural boundary conditions in the maximum norm

The heat equation `uₜ = Δu` on the cube `Q = b + (0, s)ⁿ` with the natural (Neumann) boundary
condition `∂_ν u = 0`, discretized by lumped-mass `P₁` elements on the Freudenthal mesh of level
`N + 1` (`h = s / (N + 1)`) with **all** nodes `{0, …, N + 1}ⁿ` as unknowns
(`MaxNormNeumann.Space N`): `(Lₕ U)(p) = -a(φₚ, U_h) / m(p)` (`neumannLaplacian`), the stiffness
form and lumped mass of `Feec.FiniteElement.LumpedMass`.

## Main results

**`MaxNormNeumann.maxNormNeumann`** (statement `MaxNormNeumann.Verdict`):

1. (**the discrete maximum principle**, `isSubMarkovGenerator`) only the non-obtuseness of the
   Freudenthal simplices enters: `Lₕ` has nonnegative off-diagonal entries and `Lₕ 𝟙 = 0`
   (`neumannLaplacian_apply_one`, the constants lie in the `P₁` space), so `e^{tLₕ}` is positive and
   contractive in the maximum norm;
2. (**the stencil at every node**, `neumannLaplacian_interp`) `(Lₕ Iₕ u)(p) = (n + 1) S_u(p) / C(p)`
   with `C(p)` the number of (simplex, vertex position) pairs at `p` and
   `S_u(p) = Σ_σ Σₗ (α⁺ D⁺ₗu - α⁻ D⁻ₗu)`, `α±_{σ,l}(p) ∈ {0, 1}` recording whether the path edge
   `p → p ± eₗ` of the Kuhn simplex `σ` lies in the mesh; along a coordinate interior to the cube
   `α⁺ = α⁻` (`upCount_eq_downCount`);
3. (**consistency**) `O(h²)` at the interior nodes (`abs_laplacian_sub_interior_le`, the
   `(2n + 1)`-point stencil), and `O(1)` at the boundary nodes for `∂_ν u = 0`:
   `|Δu(p) - (Lₕ Iₕ u)(p)| ≤ n B₂ (1 + (n + 1)!)` (`abs_laplacian_sub_boundary_le`);
4. (**the barrier**, `neumannLaplacian_interp_chi_boundary`) for `χ = |x - c|²` and
   `s / h ≥ K_n = 2 (1 + 2n · n!)`, `Lₕ χ ≤ -s / (2 h n!)` at every boundary node, and
   `Lₕ χ = 2n` at the interior nodes;
5. (**the semidiscrete error**, `norm_interp_sub_exp_le`) for every classical solution
   (`NeumannSolution`: `C⁴` on `ℝⁿ`, `uₜ = Δu` on `Q̄`, `∂_ν u = 0`, `|∂ᵢ²u| ≤ B₂`,
   `|∂ᵢ⁴u| ≤ B₄` on `Q̄`),
   `‖Iₕ u(t) - e^{tLₕ} v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + t n B₄ h² / 12 + K_n G h (t / s + s)`,
   `G = n B₂ (1 + (n + 1)!)`: **first order** in the maximum norm at the nodes, by the comparison
   principle `abs_apply_le_of_barrier` (positivity of `e^{tLₕ}` and the barrier `κ χ`,
   `κ = 2 n! h G / s`);
6. the verdict of the Banach layer for the family (`StableFamily.Verdict`, `M = 1`).

The proved order is `O(h)`; `O(h²)` is not proved. The boundary consistency is only bounded,
and this is not an artefact of the proof at the nodes with two or more coordinates on the
boundary: there the edge weights `Σ_σ α±` are not those of the reflected interior stencil (the
Freudenthal mesh is not reflection symmetric); for instance in the plane, at the corner `b`,
`(Lₕ Iₕ u)(b) → (3/4) Δu(b)` for smooth `u` with `∂_ν u = 0` (a hand computation, not formalized),
so no argument through nodal consistency gives more there. `cosSolution`
(`e^{-λt} ∏ᵢ cos(π(xᵢ - bᵢ)/s)`) is a nonzero classical solution (`maxNormNeumann_nonvacuous`).

## References

* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
  (the lumped mass method)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Cube.MaxNormNeumann

open Feec.Models.Cube.MaxNormHeat

variable {n : ℕ} {b : Fin n → ℝ} {s : ℝ} {N : ℕ}

/-! ### Counting the simplices at a node -/

/-- The cell `m` with `m + a = q` is unique, and exists iff `0 ≤ q - a ≤ N`. -/
theorem sum_finLattice_add_ite_eq (a q : Fin n → ℤ) :
    ∑ m : Fin n → Fin (N + 1), (if finLattice m + a = q then 1 else 0 : ℝ) =
      if ∀ i, 0 ≤ q i - a i ∧ q i - a i ≤ N then 1 else 0 := by
  split_ifs with h
  · set m₀ : Fin n → Fin (N + 1) := fun j => ⟨(q j - a j).toNat, by have := h j; omega⟩
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

/-- `α⁺_{σ,l}(p)`: the simplex `σ` with path edge `p → p + eₗ` lies in the mesh. -/
def upCount (N : ℕ) (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) : ℝ :=
  ∑ m : Fin n → Fin (N + 1), if finLattice m + edgeShift σ l = p then 1 else 0

/-- `α⁻_{σ,l}(p)`: the simplex `σ` with path edge `p - eₗ → p` lies in the mesh. -/
def downCount (N : ℕ) (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) : ℝ :=
  upCount N σ l (p - Pi.single l 1)

/-- `C(p)`: the number of simplices of the mesh with vertex `p`, counted with the vertex
position. -/
def vertexCount (N : ℕ) (p : Fin n → ℤ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∑ j, ∑ m : Fin n → Fin (N + 1),
    if finLattice m + kuhnLattice σ j = p then 1 else 0

theorem upCount_eq (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) :
    upCount N σ l p =
      if ∀ i, 0 ≤ p i - edgeShift σ l i ∧ p i - edgeShift σ l i ≤ N then 1 else 0 :=
  sum_finLattice_add_ite_eq _ _

theorem upCount_nonneg (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) :
    0 ≤ upCount N σ l p := by
  rw [upCount_eq]; split_ifs <;> norm_num

theorem upCount_le_one (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) :
    upCount N σ l p ≤ 1 := by
  rw [upCount_eq]; split_ifs <;> norm_num

theorem edgeShift_self (σ : Equiv.Perm (Fin n)) (l : Fin n) : edgeShift σ l l = 0 :=
  kuhnLattice_symm_self σ l

/-- **Interior directions are symmetric**: for `1 ≤ pₗ ≤ N`, `α⁺_{σ,l}(p) = α⁻_{σ,l}(p)`. -/
theorem upCount_eq_downCount (σ : Equiv.Perm (Fin n)) {l : Fin n} {p : Fin n → ℤ}
    (h1 : 1 ≤ p l) (h2 : p l ≤ N) : upCount N σ l p = downCount N σ l p := by
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
    (h : p l = N + 1) : upCount N σ l p = 0 := by
  rw [upCount_eq, ite_eq_right]
  intro H
  have := (H l).2
  simp [edgeShift_self, h] at this

theorem vertexCount_le (p : Fin n → ℤ) : vertexCount N p ≤ (n + 1) * n.factorial := by
  calc vertexCount N p ≤ ∑ _σ : Equiv.Perm (Fin n), ∑ _j : Fin (n + 1), (1 : ℝ) :=
        sum_le_sum fun σ _ => sum_le_sum fun j _ => by
          rw [sum_finLattice_add_ite_eq]; split_ifs <;> norm_num
    _ = _ := by simp [Fintype.card_perm]; ring

theorem upCount_le_vertexCount (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) :
    upCount N σ l p ≤ vertexCount N p := by
  have hnn : ∀ σ' : Equiv.Perm (Fin n), ∀ j : Fin (n + 1), 0 ≤ ∑ m : Fin n → Fin (N + 1),
      (if finLattice m + kuhnLattice σ' j = p then 1 else 0 : ℝ) := fun _ _ =>
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  calc upCount N σ l p = ∑ m : Fin n → Fin (N + 1),
        (if finLattice m + kuhnLattice σ (σ.symm l).castSucc = p then 1 else 0 : ℝ) := rfl
    _ ≤ ∑ j, ∑ m : Fin n → Fin (N + 1),
        (if finLattice m + kuhnLattice σ j = p then 1 else 0 : ℝ) :=
      single_le_sum (f := fun j => ∑ m : Fin n → Fin (N + 1),
        (if finLattice m + kuhnLattice σ j = p then 1 else 0 : ℝ)) (fun j _ => hnn σ j)
        (mem_univ _)
    _ ≤ vertexCount N p :=
      single_le_sum (f := fun σ' => ∑ j, ∑ m : Fin n → Fin (N + 1),
        (if finLattice m + kuhnLattice σ' j = p then 1 else 0 : ℝ))
        (fun σ' _ => sum_nonneg fun j _ => hnn σ' j) (mem_univ σ)

theorem downCount_le_vertexCount (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) :
    downCount N σ l p ≤ vertexCount N p := by
  have hnn : ∀ σ' : Equiv.Perm (Fin n), ∀ j : Fin (n + 1), 0 ≤ ∑ m : Fin n → Fin (N + 1),
      (if finLattice m + kuhnLattice σ' j = p then 1 else 0 : ℝ) := fun _ _ =>
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have e : downCount N σ l p = ∑ m : Fin n → Fin (N + 1),
      (if finLattice m + kuhnLattice σ (σ.symm l).succ = p then 1 else 0 : ℝ) := by
    refine sum_congr rfl fun m _ => ?_
    rw [kuhnLattice_succ, Equiv.apply_symm_apply, edgeShift]
    congr 1
    exact propext ⟨fun h => by rw [← add_assoc, h, sub_add_cancel],
      fun h => by rw [eq_sub_iff_add_eq, add_assoc, h]⟩
  rw [e]
  refine (single_le_sum (f := fun j => ∑ m : Fin n → Fin (N + 1),
        (if finLattice m + kuhnLattice σ j = p then 1 else 0 : ℝ)) (fun j _ => hnn σ j)
        (mem_univ _)).trans ?_
  exact single_le_sum (f := fun σ' => ∑ j, ∑ m : Fin n → Fin (N + 1),
        (if finLattice m + kuhnLattice σ' j = p then 1 else 0 : ℝ))
        (fun σ' _ => sum_nonneg fun j _ => hnn σ' j) (mem_univ σ)

/-- The Kuhn order putting the coordinates at the upper face first, then `l`, then the others. -/
def boundaryPerm (N : ℕ) (p : Fin n → ℤ) (l : Fin n) : Equiv.Perm (Fin n) :=
  Tuple.sort fun i : Fin n => if i = l then 1 else if p i = N + 1 then 0 else 2

theorem edgeShift_boundaryPerm {p : Fin n → ℤ} {l i : Fin n} (hi : i ≠ l) :
    (p i = N + 1 → edgeShift (boundaryPerm N p l) l i = 1) ∧
      (p i ≠ N + 1 → edgeShift (boundaryPerm N p l) l i = 0) := by
  set f : Fin n → ℕ := fun i : Fin n => if i = l then 1 else if p i = N + 1 then 0 else 2
  set σ := boundaryPerm N p l
  have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
  have lt_of : ∀ a c : Fin n, f a < f c → σ.symm a < σ.symm c := fun a c h => by
    by_contra h'
    have := hmono (not_lt.1 h')
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
    omega
  simp only [edgeShift, kuhnLattice, Fin.val_castSucc]
  constructor
  · intro hp
    have : f i < f l := by simp [f, hi, hp]
    simp [Fin.lt_def.1 (lt_of _ _ this)]
  · intro hp
    have : f l < f i := by simp [f, hi, hp]
    simp [not_lt.2 (Fin.le_def.1 (lt_of _ _ this).le)]

/-- At a node of the lower face `pₗ = 0`, the edge `p → p + eₗ` lies in a simplex. -/
theorem upCount_boundaryPerm {p : Fin n → ℤ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ N + 1) {l : Fin n}
    (hl : p l = 0) : upCount N (boundaryPerm N p l) l p = 1 := by
  rw [upCount_eq, ite_eq_left_iff]
  intro H
  refine absurd (fun i => ?_) H
  by_cases hi : i = l
  · subst hi; simp [edgeShift_self, hl]
  · have := hp i
    by_cases hN : p i = N + 1
    · rw [(edgeShift_boundaryPerm hi).1 hN]; omega
    · rw [(edgeShift_boundaryPerm hi).2 hN]; omega

/-- At a node of the upper face `pₗ = N + 1`, the edge `p - eₗ → p` lies in a simplex. -/
theorem downCount_boundaryPerm {p : Fin n → ℤ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ N + 1) {l : Fin n}
    (hl : p l = N + 1) : downCount N (boundaryPerm N p l) l p = 1 := by
  rw [downCount, upCount_eq, ite_eq_left_iff]
  intro H
  refine absurd (fun i => ?_) H
  by_cases hi : i = l
  · subst hi; simp [edgeShift_self, hl]
  · have := hp i
    simp only [Pi.sub_apply, Pi.single_apply, hi, ite_false, sub_zero]
    by_cases hN : p i = N + 1
    · rw [(edgeShift_boundaryPerm hi).1 hN]; omega
    · rw [(edgeShift_boundaryPerm hi).2 hN]; omega

/-! ### The stiffness rows and the lumped masses at every node -/

/-- The difference quotient `(w(q + eₗ) - w(q)) / h²` along the edge `q → q + eₗ`. -/
def edgeQuot (b : Fin n → ℝ) (h : ℝ) (w : (Fin n → ℝ) → ℝ) (l : Fin n) (q : Fin n → ℤ) : ℝ :=
  (w (node b h (q + Pi.single l 1)) - w (node b h q)) / h / h

/-- **The stiffness row of any node** `p` (boundary nodes included):
`a(φₚ, w) = hⁿ / n! Σ_σ Σₗ (α⁻_{σ,l}(p) Dₗw(p - eₗ) - α⁺_{σ,l}(p) Dₗw(p)) / h`. -/
theorem p1Stiffness_nodalIndicator_eq (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) (p : Fin n → ℤ)
    (w : (Fin n → ℝ) → ℝ) :
    p1Stiffness (freudenthalMesh b s hs (N + 1)) (nodalIndicator (node b (meshSize s N) p)) w =
      meshSize s N ^ n / n.factorial * ∑ σ : Equiv.Perm (Fin n), ∑ l,
        (downCount N σ l p * edgeQuot b (meshSize s N) w l (p - Pi.single l 1) -
          upCount N σ l p * edgeQuot b (meshSize s N) w l p) := by
  have hh := freudenthalScale_pos hs (N + 1)
  have hh' := hh.ne'
  rw [p1Stiffness_eq, sum_freudenthalMesh_simplices, meshSize]
  simp_rw [volume_real_freudenthalMesh_simplex b hh, mapEquiv_boxMap_freudenthalSimplex_points,
    p1Grad_dotProduct_freudenthalPoints b hh', mul_sum]
  rw [sum_comm]
  simp_rw [sum_comm (s := (univ : Finset (Fin n → Fin (N + 1)))) (t := (univ : Finset (Fin n)))]
  refine sum_congr rfl fun σ _ => sum_congr rfl fun l _ => ?_
  have e : ∀ q, edgeTerm b (s / ↑(N + 1)) (nodalIndicator (node b (s / ↑(N + 1)) p)) w l q =
      (if q = p - Pi.single l 1 then 1 else 0) * edgeQuot b (s / ↑(N + 1)) w l (p - Pi.single l 1) -
        (if q = p then 1 else 0) * edgeQuot b (s / ↑(N + 1)) w l p := fun q => by
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

/-- **The lumped mass of any node**: `m(p) = hⁿ C(p) / (n + 1)!`. -/
theorem lumpedMass_node_eq (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) (p : Fin n → ℤ) :
    lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p) =
      meshSize s N ^ n / n.factorial / (n + 1) * vertexCount N p := by
  have hh := freudenthalScale_pos hs (N + 1)
  rw [lumpedMass, sum_freudenthalMesh_simplices, meshSize]
  simp_rw [volume_real_freudenthalMesh_simplex b hh, mapEquiv_boxMap_freudenthalSimplex_points,
    freudenthalPoints_eq_node, (node_injective b hh.ne').eq_iff, card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ← mul_sum]
  rw [vertexCount]
  congr 1
  rw [sum_comm]
  exact sum_congr rfl fun σ _ => sum_comm

/-! ### The Neumann problem: all nodes -/

/-- All nodes `q ∈ {0, …, N + 1}ⁿ` of the level-`(N + 1)` lattice. -/
def closedNodes (n N : ℕ) : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Icc 0 (N + 1 : ℤ)

theorem mem_closedNodes {p : Fin n → ℤ} : p ∈ closedNodes n N ↔ ∀ i, 0 ≤ p i ∧ p i ≤ N + 1 := by
  simp [closedNodes]

/-- The nodes of the Neumann problem. -/
abbrev Nodes (n N : ℕ) := ↥(closedNodes n N)

/-- The discrete space of the Neumann problem: values at all nodes, with the maximum norm. -/
abbrev Space (n N : ℕ) := Nodes n N → ℝ

/-- The nodal function on `ℝⁿ` with values `U` at the nodes and `0` elsewhere. -/
def nodal (b : Fin n → ℝ) (s : ℝ) (U : Space n N) : (Fin n → ℝ) → ℝ :=
  fun x => ∑ q : Nodes n N, if node b (meshSize s N) q = x then U q else 0

theorem nodal_node (hs : 0 < s) (U : Space n N) (q : Nodes n N) :
    nodal b s U (node b (meshSize s N) q) = U q := by
  have hinj := node_injective b (meshSize_pos hs N).ne'
  simp only [nodal, hinj.eq_iff]
  rw [Finset.sum_eq_single q]
  · simp
  · intro c _ hc; rw [ite_eq_right]; intro e; exact hc (Subtype.ext e)
  · simp

theorem nodal_eq_sum (U : Space n N) :
    nodal b s U = ∑ q : Nodes n N, U q • nodalIndicator (node b (meshSize s N) q) := by
  funext x
  simp [nodal, nodalIndicator, Finset.sum_apply, eq_comm]

/-- The lumped-mass Neumann Laplacian `-M_L⁻¹ K` on all nodes, before linearity. -/
def neumannLaplacianFun (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) : Space n N := fun p =>
  -p1Stiffness (freudenthalMesh b s hs (N + 1)) (nodalIndicator (node b (meshSize s N) p))
    (nodal b s U) / lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p)

/-- The matrix form: `(Lₕ U)(p) = Σ_q (-a(φₚ, φ_q) / m(p)) U(q)`. -/
theorem neumannLaplacianFun_apply (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) (p : Nodes n N) :
    neumannLaplacianFun b hs U p = ∑ q : Nodes n N,
      -p1Stiffness (freudenthalMesh b s hs (N + 1)) (nodalIndicator (node b (meshSize s N) p))
        (nodalIndicator (node b (meshSize s N) q)) /
        lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p) * U q := by
  rw [neumannLaplacianFun, nodal_eq_sum, p1Stiffness_comm, p1Stiffness_sum_smul, ← sum_neg_distrib,
    sum_div]
  refine sum_congr rfl fun q _ => ?_
  rw [p1Stiffness_comm]
  ring

/-- **The lumped-mass `P₁` Laplacian with natural (Neumann) boundary conditions** on the
level-`(N + 1)` Freudenthal mesh of `b + (0, s)ⁿ`: `(Lₕ U)(p) = -a(φₚ, U_h) / m(p)` at every node,
boundary nodes included. -/
def neumannLaplacian (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) : Space n N →L[ℝ] Space n N :=
  LinearMap.toContinuousLinearMap
    { toFun := neumannLaplacianFun b hs
      map_add' := fun U V => by
        funext p
        simp only [neumannLaplacianFun_apply, Pi.add_apply, mul_add, sum_add_distrib]
      map_smul' := fun c U => by
        funext p
        simp only [neumannLaplacianFun_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        exact sum_congr rfl fun q _ => by ring }

theorem neumannLaplacian_apply (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) (p : Nodes n N) :
    neumannLaplacian b hs N U p =
      -p1Stiffness (freudenthalMesh b s hs (N + 1)) (nodalIndicator (node b (meshSize s N) p))
        (nodal b s U) / lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p) :=
  rfl

theorem lumpedMass_nonneg (M : SimplicialMesh n) (x : Fin n → ℝ) : 0 ≤ lumpedMass M x :=
  sum_nonneg fun _ _ => mul_nonneg (div_nonneg measureReal_nonneg (by positivity))
    (Nat.cast_nonneg _)

/-- **Conservation**: `Lₕ 𝟙 = 0` (the constants are in the `P₁` space and `a(φₚ, 1) = 0`). -/
theorem neumannLaplacian_apply_one (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    neumannLaplacian b hs N (fun _ => 1) = 0 := by
  funext p
  rw [neumannLaplacian_apply, p1Stiffness_congr_right _ _ (w' := fun _ => 1) fun T hT j => ?_,
    p1Stiffness_const_right, neg_zero, zero_div, Pi.zero_apply]
  obtain ⟨q, hq, e⟩ := exists_node_eq_points hs hT j
  rw [e, nodal_node hs (q := ⟨q, mem_closedNodes.2 hq⟩)]

/-- **The discrete maximum principle for the Neumann problem**: `Lₕ` is a sub-Markov (indeed
Markov, `Lₕ 𝟙 = 0`) generator, so `e^{tLₕ}` is positive and contractive in the maximum norm.
Only the non-obtuseness of the mesh enters (Ciarlet–Raviart). [CiarletRaviart1973] -/
theorem isSubMarkovGenerator (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    IsSubMarkovGenerator (neumannLaplacian b hs N) where
  exists_shift := by
    set a : Nodes n N → Nodes n N → ℝ := fun p q =>
      -p1Stiffness (freudenthalMesh b s hs (N + 1)) (nodalIndicator (node b (meshSize s N) p))
        (nodalIndicator (node b (meshSize s N) q)) /
        lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p)
    have hoff : ∀ p q, p ≠ q → 0 ≤ a p q := fun p q hpq =>
      div_nonneg (neg_nonneg.2 (p1Stiffness_freudenthalMesh_indicator_nonpos b hs (N + 1)
        fun h => hpq (Subtype.ext (node_injective b (meshSize_pos hs N).ne' h))))
        (lumpedMass_nonneg _ _)
    refine ⟨∑ p, |a p p|, sum_nonneg fun _ _ => abs_nonneg _, fun U hU p => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [show neumannLaplacian b hs N U p = ∑ q, a p q * U q from neumannLaplacianFun_apply b hs U p,
      ← Finset.add_sum_erase _ _ (mem_univ p)]
    have h1 : 0 ≤ ∑ q ∈ univ.erase p, a p q * U q :=
      sum_nonneg fun q hq => mul_nonneg (hoff p q (Finset.ne_of_mem_erase hq).symm) (hU q)
    have h2 : 0 ≤ a p p + ∑ p, |a p p| := by
      have := single_le_sum (f := fun p => |a p p|) (fun _ _ => abs_nonneg _) (mem_univ p)
      linarith [neg_abs_le (a p p)]
    nlinarith [mul_nonneg h2 (hU p)]
  apply_one_nonpos p := by rw [neumannLaplacian_apply_one]; exact le_rfl

/-! ### A comparison principle -/

section Comparison

variable {ι : Type*} [Fintype ι]

/-- **Positivity along the flow**: for a sub-Markov generator `L`, a curve with `Z(0) ≥ 0` and
`Z' - L Z ≥ 0` on `[0, t]` has `Z(t) ≥ 0` (`Z(t) = e^{tL} Z(0) + ∫ e^{(t-r)L} (Z' - L Z)`). -/
theorem nonneg_of_hasDerivAt {L : (ι → ℝ) →L[ℝ] (ι → ℝ)} (hL : IsSubMarkovGenerator L)
    {Z Z' : ℝ → ι → ℝ} {t : ℝ} (ht : 0 ≤ t) (hZ : ∀ r ∈ Icc 0 t, HasDerivAt Z (Z' r) r)
    (hZ' : ∀ r ∈ Icc 0 t, 0 ≤ Z' r - L (Z r)) (h0 : 0 ≤ Z 0) : 0 ≤ Z t := by
  set f : ℝ → ι → ℝ := fun r => exp (((t - r : ℝ) : ℝ) • L) (Z r)
  have hf : ∀ r ∈ Icc 0 t, HasDerivAt f (exp (((t - r : ℝ) : ℝ) • L) (Z' r - L (Z r))) r :=
    fun r hr => hasDerivAt_exp_sub_smul_apply L t (hZ r hr)
  intro i
  have hmono : MonotoneOn (fun r => f r i) (Icc 0 t) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
      (fun r hr => ((hasDerivAt_pi.1 (hf r hr) i).continuousAt).continuousWithinAt)
      (fun r hr => (hasDerivAt_pi.1 (hf r (interior_subset hr)) i).hasDerivWithinAt)
      fun r hr => ?_
    have hr' := interior_subset hr
    exact hL.exp_smul_apply_nonneg (sub_nonneg.2 hr'.2) (hZ' r hr') i
  have h := hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simp only [f, sub_self, zero_smul, exp_zero, one_apply_eq_self, sub_zero] at h
  exact (hL.exp_smul_apply_nonneg ht h0 i).trans h

/-- **The barrier estimate**: for a Markov generator `L` (`L 𝟙 = 0`) and a curve `E` whose defect
`E' - L E` is bounded by `A - L ψ` for a barrier `ψ ≥ 0`, `|E(t)| ≤ ‖E(0)‖ + ψ + t A`. -/
theorem abs_apply_le_of_barrier {L : (ι → ℝ) →L[ℝ] (ι → ℝ)} (hL : IsSubMarkovGenerator L)
    (h1 : L (fun _ => 1) = 0) {E E' : ℝ → ι → ℝ} {t A : ℝ} (ht : 0 ≤ t)
    (hE : ∀ r ∈ Icc 0 t, HasDerivAt E (E' r) r) {ψ : ι → ℝ} (hψ : 0 ≤ ψ)
    (hτ : ∀ r ∈ Icc 0 t, ∀ i, |(E' r - L (E r)) i| ≤ A - L ψ i) (i : ι) :
    |E t i| ≤ ‖E 0‖ + ψ i + t * A := by
  have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ε * E t i ≤ ‖E 0‖ + ψ i + t * A := fun ε hε => by
    set Z : ℝ → ι → ℝ := fun r => (‖E 0‖ + r * A) • (fun _ => (1 : ℝ)) + ψ - ε • E r
    have hZ : ∀ r ∈ Icc 0 t, HasDerivAt Z (A • (fun _ => (1 : ℝ)) - ε • E' r) r := fun r hr => by
      refine hasDerivAt_pi.2 fun j => ?_
      have := ((((hasDerivAt_id r).mul_const A).const_add ‖E 0‖).add_const (ψ j)).sub
        ((hasDerivAt_pi.1 (hE r hr) j).const_mul ε)
      convert this using 1 <;> first | (funext x; simp [Z]) | simp
    have hL1 : ∀ c : ℝ, L (c • fun _ => (1 : ℝ)) = 0 := fun c => by rw [map_smul, h1, smul_zero]
    have h := nonneg_of_hasDerivAt hL ht hZ (fun r hr j => by
      have hb := hτ r hr j
      simp only [Z, map_sub, map_add, hL1, zero_add, map_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply, mul_one]
      rcases hε with rfl | rfl
      · have := (abs_le.1 hb).2; simp only [Pi.sub_apply] at this; linarith
      · have := (abs_le.1 hb).1; simp only [Pi.sub_apply] at this; linarith) (fun j => by
      simp only [Z, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero,
        mul_one, Pi.zero_apply]
      have := norm_le_pi_norm (E 0) j
      rw [Real.norm_eq_abs] at this
      have hψj : 0 ≤ ψ j := hψ j
      rcases hε with rfl | rfl
      · linarith [le_abs_self (E 0 j)]
      · linarith [neg_abs_le (E 0 j)]) i
    simp only [Z, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one,
      Pi.zero_apply] at h
    linarith
  rcases abs_cases (E t i) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; simpa using key 1 (Or.inl rfl)
  · rw [h]; simpa using key (-1) (Or.inr rfl)

end Comparison

/-! ### The stencil at every node -/

/-- The nodal interpolant `(Iₕ u)(p) = u(b + h p)` at all nodes. -/
def interp (b : Fin n → ℝ) (s : ℝ) (N : ℕ) (u : (Fin n → ℝ) → ℝ) : Space n N :=
  fun p => u (node b (meshSize s N) p)

/-- The stencil sum `Σ_σ Σₗ (α⁺_{σ,l}(p) D⁺ₗw(p) - α⁻_{σ,l}(p) D⁻ₗw(p))`, `D±` the one-sided
second-order difference quotients. -/
def stencilSum (b : Fin n → ℝ) (s : ℝ) (N : ℕ) (w : (Fin n → ℝ) → ℝ) (p : Fin n → ℤ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∑ l, (upCount N σ l p * edgeQuot b (meshSize s N) w l p -
    downCount N σ l p * edgeQuot b (meshSize s N) w l (p - Pi.single l 1))

/-- **The Neumann stencil at any node**: `(Lₕ Iₕ u)(p) = (n + 1) S_u(p) / C(p)`. -/
theorem neumannLaplacian_interp (hs : 0 < s) (u : (Fin n → ℝ) → ℝ) (p : Nodes n N) :
    neumannLaplacian b hs N (interp b s N u) p =
      (n + 1) * stencilSum b s N u p / vertexCount N (p : Fin n → ℤ) := by
  rw [neumannLaplacian_apply, p1Stiffness_congr_right _ _ (w' := u) fun T hT j => ?_,
    p1Stiffness_nodalIndicator_eq, lumpedMass_node_eq]
  · have ha : meshSize s N ^ n / n.factorial ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (meshSize_pos hs N).ne') (by positivity)
    have e : stencilSum b s N u p = -∑ σ : Equiv.Perm (Fin n), ∑ l,
        (downCount N σ l p * edgeQuot b (meshSize s N) u l ((p : Fin n → ℤ) - Pi.single l 1) -
          upCount N σ l p * edgeQuot b (meshSize s N) u l p) := by
      rw [stencilSum, ← sum_neg_distrib]
      exact sum_congr rfl fun σ _ => by rw [← sum_neg_distrib]; exact sum_congr rfl fun l _ => by ring
    rw [e]
    have hh := (meshSize_pos hs N).ne'
    rcases eq_or_ne (vertexCount N (p : Fin n → ℤ)) 0 with hC | hC
    · simp [hC]
    · field_simp
  · obtain ⟨q, hq, e⟩ := exists_node_eq_points hs hT j
    rw [e, nodal_node hs (q := ⟨q, mem_closedNodes.2 hq⟩)]
    rfl

/-! ### The barrier `χ(x) = |x - c|²` -/

/-- The barrier `χ(x) = Σᵢ (xᵢ - cᵢ)²`, `c` the centre of the cube. -/
def chi (b : Fin n → ℝ) (s : ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, (x i - b i - s / 2) ^ 2

theorem chi_add_single (b : Fin n → ℝ) (s : ℝ) (x : Fin n → ℝ) (l : Fin n) (t : ℝ) :
    chi b s (x + t • Pi.single l 1) = chi b s x + 2 * t * (x l - b l - s / 2) + t ^ 2 := by
  have : chi b s (x + t • Pi.single l 1) - chi b s x = 2 * t * (x l - b l - s / 2) + t ^ 2 := by
    rw [chi, chi, ← sum_sub_distrib, Finset.sum_eq_single l]
    · simp; ring
    · intro i _ hi; simp [hi]
    · simp
  linarith

theorem chi_nonneg (b : Fin n → ℝ) (s : ℝ) (x : Fin n → ℝ) : 0 ≤ chi b s x :=
  sum_nonneg fun _ _ => sq_nonneg _

theorem chi_le (b : Fin n → ℝ) {s : ℝ} {x : Fin n → ℝ} (hx : x ∈ closedCube b s) :
    chi b s x ≤ n * s ^ 2 / 4 := by
  calc chi b s x ≤ ∑ _i : Fin n, s ^ 2 / 4 := sum_le_sum fun i _ => by
        have := hx i (mem_univ i)
        nlinarith [this.1, this.2]
    _ = _ := by simp; ring

theorem node_coord (b : Fin n → ℝ) (h : ℝ) (p : Fin n → ℤ) (l : Fin n) :
    node b h p l = b l + h * p l := by
  simp [node, latticePoint_apply]

theorem node_add_single_one (b : Fin n → ℝ) (h : ℝ) (p : Fin n → ℤ) (l : Fin n) :
    node b h (p + Pi.single l 1) = node b h p + h • Pi.single l 1 := by
  rw [node_add_single]; simp

theorem node_eq_sub_single_add (b : Fin n → ℝ) (h : ℝ) (p : Fin n → ℤ) (l : Fin n) :
    node b h p = node b h (p - Pi.single l 1) + h • Pi.single l 1 := by
  rw [← node_add_single_one, sub_add_cancel]

/-- The stencil terms of the barrier: `α⁺ (2yₗ/h + 1) - α⁻ (2yₗ/h - 1)`, `yₗ = xₗ - cₗ`. -/
theorem stencilTerm_chi (hs : 0 < s) (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) :
    upCount N σ l p * edgeQuot b (meshSize s N) (chi b s) l p -
        downCount N σ l p * edgeQuot b (meshSize s N) (chi b s) l (p - Pi.single l 1) =
      upCount N σ l p * (2 * (meshSize s N * p l - s / 2) / meshSize s N + 1) -
        downCount N σ l p * (2 * (meshSize s N * p l - s / 2) / meshSize s N - 1) := by
  have hh := (meshSize_pos hs N).ne'
  have d1 : chi b s (node b (meshSize s N) (p + Pi.single l 1)) - chi b s (node b (meshSize s N) p) =
      2 * meshSize s N * (meshSize s N * p l - s / 2) + meshSize s N ^ 2 := by
    rw [node_add_single_one, chi_add_single, node_coord]; ring
  have d2 : chi b s (node b (meshSize s N) (p - Pi.single l 1 + Pi.single l 1)) -
      chi b s (node b (meshSize s N) (p - Pi.single l 1)) =
      2 * meshSize s N * (meshSize s N * p l - s / 2) - meshSize s N ^ 2 := by
    rw [node_add_single_one, chi_add_single, node_coord]
    simp only [Pi.sub_apply, Pi.single_eq_same, Int.cast_sub, Int.cast_one]
    ring
  simp only [edgeQuot]
  rw [d1, d2]
  field_simp

theorem meshSize_le (hs : 0 < s) (N : ℕ) : meshSize s N ≤ s := by
  rw [meshSize, div_le_iff₀ (by positivity)]
  have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
  nlinarith

/-- Every stencil term of the barrier is at most `2`; at a boundary coordinate it is
`α± (1 - s/h) ≤ 0`. -/
theorem stencilTerm_chi_le (hs : 0 < s) (σ : Equiv.Perm (Fin n)) (l : Fin n) {p : Fin n → ℤ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ N + 1) :
    upCount N σ l p * edgeQuot b (meshSize s N) (chi b s) l p -
        downCount N σ l p * edgeQuot b (meshSize s N) (chi b s) l (p - Pi.single l 1) ≤
      2 - (if σ = boundaryPerm N p l ∧ (p l = 0 ∨ p l = N + 1) then 1 + s / meshSize s N
        else 0) := by
  have hh := meshSize_pos hs N
  have hm := meshSize_mul s N
  push_cast at hm
  have hsh : 1 ≤ s / meshSize s N := by rw [le_div_iff₀ hh, one_mul]; exact meshSize_le hs N
  rw [stencilTerm_chi hs]
  have hu0 := upCount_nonneg (N := N) σ l p
  have hu1 := upCount_le_one (N := N) σ l p
  have hd0 := upCount_nonneg (N := N) σ l (p - Pi.single l 1)
  have hd1 := upCount_le_one (N := N) σ l (p - Pi.single l 1)
  rw [← downCount] at hd0 hd1
  rcases (hp l).1.eq_or_lt with h0 | h0
  · -- the lower face
    have hl : p l = 0 := h0.symm
    rw [downCount_eq_zero σ hl, hl]
    have e : 2 * (meshSize s N * ((0 : ℤ) : ℝ) - s / 2) / meshSize s N + 1 =
        1 - s / meshSize s N := by field_simp; ring
    rw [e]
    split_ifs with hσ
    · rw [hσ.1, upCount_boundaryPerm hp hl]; ring_nf; linarith
    · nlinarith
  rcases (hp l).2.eq_or_lt with hN | hN
  · -- the upper face
    rw [upCount_eq_zero σ hN, hN]
    have e : 2 * (meshSize s N * (((N : ℤ) + 1 : ℤ) : ℝ) - s / 2) / meshSize s N - 1 =
        s / meshSize s N - 1 := by push_cast; field_simp; linarith
    rw [e]
    split_ifs with hσ
    · rw [hσ.1, downCount_boundaryPerm hp hN]; ring_nf; linarith
    · nlinarith
  · -- an interior coordinate
    rw [← upCount_eq_downCount σ (by omega) (by omega)]
    rw [ite_eq_right_iff.2 (by rintro ⟨-, h | h⟩ <;> omega)]
    nlinarith

/-- `L χ = 2n` at the interior nodes (the difference Laplacian is exact on quadratics). -/
theorem neumannLaplacian_interp_chi_interior (hs : 0 < s) {p : Nodes n N}
    (hp : (p : Fin n → ℤ) ∈ interiorNodes n (N + 1)) :
    neumannLaplacian b hs N (interp b s N (chi b s)) p = 2 * n := by
  have hh := (meshSize_pos hs N).ne'
  rw [neumannLaplacian_apply, p1Stiffness_congr_right _ _ (w' := chi b s) fun T hT j => ?_]
  · have := neg_p1Stiffness_div_lumpedMass b hs (N + 1) hp (chi b s)
    rw [meshSize, this]
    have e : ∀ l, (chi b s (node b (s / ↑(N + 1)) ((p : Fin n → ℤ) + Pi.single l 1)) -
        2 * chi b s (node b (s / ↑(N + 1)) p) +
        chi b s (node b (s / ↑(N + 1)) ((p : Fin n → ℤ) - Pi.single l 1))) / (s / ↑(N + 1)) ^ 2
        = 2 := fun l => by
      rw [node_add_single_one, chi_add_single, node_eq_sub_single_add b _ (p : Fin n → ℤ) l,
        chi_add_single, node_coord, ← node_eq_sub_single_add, node_coord]
      simp only [Pi.sub_apply, Pi.single_eq_same, Int.cast_sub, Int.cast_one]
      have : s / ↑(N + 1) ≠ 0 := hh
      field_simp
      ring
    simp only [e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · obtain ⟨q, hq, e⟩ := exists_node_eq_points hs hT j
    rw [e, nodal_node hs (q := ⟨q, mem_closedNodes.2 hq⟩)]
    rfl

/-- The constant `K_n = 2 (1 + 2n · n!)` of the boundary layer. -/
def layerConst (n : ℕ) : ℝ := 2 * (1 + 2 * n * n.factorial)

theorem one_le_vertexCount_of_boundary {p : Fin n → ℤ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ N + 1)
    {l : Fin n} (hl : p l = 0 ∨ p l = N + 1) : 1 ≤ vertexCount N p := by
  rcases hl with hl | hl
  · rw [← upCount_boundaryPerm hp hl]; exact upCount_le_vertexCount _ _ _
  · rw [← downCount_boundaryPerm hp hl]; exact downCount_le_vertexCount _ _ _

/-- **The barrier at the boundary nodes**: for `s / h ≥ K_n`, `L χ ≤ -s / (2 h n!)` at every node
with a coordinate on the boundary. -/
theorem neumannLaplacian_interp_chi_boundary (hs : 0 < s) (p : Nodes n N) {l₀ : Fin n}
    (hl₀ : (p : Fin n → ℤ) l₀ = 0 ∨ (p : Fin n → ℤ) l₀ = N + 1)
    (hK : layerConst n ≤ s / meshSize s N) :
    neumannLaplacian b hs N (interp b s N (chi b s)) p ≤
      -(s / meshSize s N) / (2 * n.factorial) := by
  have hp := mem_closedNodes.1 p.2
  have hh := meshSize_pos hs N
  set r := s / meshSize s N
  have hr : 0 ≤ r := by positivity
  set f : Equiv.Perm (Fin n) → Fin n → ℝ := fun σ l =>
    if σ = boundaryPerm N p l ∧ ((p : Fin n → ℤ) l = 0 ∨ (p : Fin n → ℤ) l = N + 1) then 1 + r
    else 0
  have hf : ∀ σ l, 0 ≤ f σ l := fun σ l => by simp only [f]; split_ifs <;> linarith
  have hS : stencilSum b s N (chi b s) p ≤ 2 * n * n.factorial - (1 + r) := by
    calc stencilSum b s N (chi b s) p ≤ ∑ σ : Equiv.Perm (Fin n), ∑ l, (2 - f σ l) :=
          sum_le_sum fun σ _ => sum_le_sum fun l _ => stencilTerm_chi_le hs σ l hp
      _ = 2 * n * n.factorial - ∑ σ, ∑ l, f σ l := by
          simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, Fintype.card_perm,
            nsmul_eq_mul]
          ring
      _ ≤ 2 * n * n.factorial - (1 + r) := by
          have h1 : f (boundaryPerm N p l₀) l₀ = 1 + r := by simp [f, hl₀]
          have h2 : f (boundaryPerm N p l₀) l₀ ≤ ∑ l, f (boundaryPerm N p l₀) l :=
            single_le_sum (f := fun l => f (boundaryPerm N p l₀) l) (fun l _ => hf _ l)
              (mem_univ l₀)
          have h3 : ∑ l, f (boundaryPerm N p l₀) l ≤ ∑ σ, ∑ l, f σ l :=
            single_le_sum (f := fun σ => ∑ l, f σ l) (fun σ _ => sum_nonneg fun l _ => hf σ l)
              (mem_univ _)
          linarith
  have hC1 := one_le_vertexCount_of_boundary hp hl₀
  have hC2 := vertexCount_le (N := N) (p : Fin n → ℤ)
  have hfac : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
  have hK' : 2 * (1 + 2 * n * n.factorial) ≤ r := hK
  rw [neumannLaplacian_interp, div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hC2 (by linarith : (0 : ℝ) ≤ r / 2)]

/-! ### Taylor's formula along the axes -/

theorem sum_smul_single_mul (l : Fin n) (t : ℝ) (F : Fin n → ℝ) :
    ∑ i, (t • Pi.single l 1 : Fin n → ℝ) i * F i = t * F l := by
  rw [Finset.sum_eq_single l]
  · simp
  · intro i _ hi; simp [hi]
  · simp

/-- **Taylor along an axis**: `|f(x + t eₗ) - f(x) - t ∂ₗf(x)| ≤ B t² / 2` for `|∂ₗ²f| ≤ B` on
the segment. -/
theorem abs_axis_taylor_le {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (x : Fin n → ℝ)
    (l : Fin n) (t : ℝ) {B : ℝ}
    (hB : ∀ τ ∈ uIcc 0 t, |partialDeriv l (partialDeriv l f) (x + τ • Pi.single l 1)| ≤ B) :
    |f (x + t • Pi.single l 1) - f x - t * partialDeriv l f x| ≤ B * t ^ 2 / 2 := by
  have hd1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (partialDeriv l f) :=
    (hf.partialDeriv (m := 1) (by norm_num) l).differentiable (by norm_num)
  set v : Fin n → ℝ := t • Pi.single l 1
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • v = x + (τ * t) • Pi.single l 1 := fun τ _ => by
    simp [v, smul_smul]
  have hmem : ∀ τ ∈ Icc (0 : ℝ) 1, τ * t ∈ uIcc 0 t := fun τ hτ => by
    rw [Set.mem_uIcc]
    rcases le_total 0 t with ht | ht
    · left; exact ⟨mul_nonneg hτ.1 ht, by nlinarith [hτ.2]⟩
    · right; exact ⟨by nlinarith [hτ.2], mul_nonpos_of_nonneg_of_nonpos hτ.1 ht⟩
  have := abs_taylor_one_le (g := fun τ => f (x + τ • v))
    (g₁ := fun τ => t * partialDeriv l f (x + τ • v))
    (g₂ := fun τ => t * (t * partialDeriv l (partialDeriv l f) (x + τ • v))) (M := B * t ^ 2)
    (fun τ _ => by
      have := hasDerivAt_comp_line (v := v) (hd1 (x + τ • v))
      rwa [sum_smul_single_mul] at this)
    (fun τ _ => by
      have := hasDerivAt_comp_line (v := v) (hd2 (x + τ • v))
      rw [sum_smul_single_mul] at this
      exact this.const_mul t)
    (fun τ hτ => by
      have h := hB _ (hmem τ hτ)
      rw [← hseg τ hτ] at h
      rw [abs_mul, abs_mul, ← mul_assoc, abs_mul_abs_self]
      nlinarith [sq_nonneg t])
  simpa [v] using this

/-- **The second difference**: `|f(x + h eₗ) - 2 f(x) + f(x - h eₗ)| ≤ B h²`. -/
theorem abs_axis_secondDiff_le {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (x : Fin n → ℝ)
    (l : Fin n) {h B : ℝ}
    (hB : ∀ τ ∈ Icc (-|h|) |h|, |partialDeriv l (partialDeriv l f) (x + τ • Pi.single l 1)| ≤ B) :
    |f (x + h • Pi.single l 1) - 2 * f x + f (x + (-h) • Pi.single l 1)| ≤ B * h ^ 2 := by
  have sub : ∀ t, |t| = |h| → uIcc 0 t ⊆ Icc (-|h|) |h| := fun t ht τ hτ => by
    rw [← ht]
    rcases Set.mem_uIcc.1 hτ with h1 | h1 <;> constructor <;>
      cases abs_cases t <;> linarith [h1.1, h1.2]
  have h1 := abs_axis_taylor_le hf x l h fun τ hτ => hB τ (sub h rfl hτ)
  have h2 := abs_axis_taylor_le hf x l (-h) fun τ hτ => hB τ (sub (-h) (abs_neg h) hτ)
  calc |f (x + h • Pi.single l 1) - 2 * f x + f (x + (-h) • Pi.single l 1)|
      = |(f (x + h • Pi.single l 1) - f x - h * partialDeriv l f x) +
          (f (x + (-h) • Pi.single l 1) - f x - -h * partialDeriv l f x)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by nlinarith [neg_sq h])

/-- **The truncation error of the second difference**: for `u ∈ C⁴` with `|∂ₗ⁴u| ≤ B` on
`x + [-h, h] eₗ`, `|∂ₗ²u(x) - (u(x + h eₗ) - 2 u(x) + u(x - h eₗ)) / h²| ≤ B h² / 12`. -/
theorem abs_partialDeriv_sub_secondDiff_le {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 4 u) {h B : ℝ}
    (hh : 0 < h) (x : Fin n → ℝ) (l : Fin n)
    (hB : ∀ t ∈ Icc (-h) h, |(partialDeriv l)^[4] u (x + t • Pi.single l 1)| ≤ B) :
    |partialDeriv l (partialDeriv l u) x -
        (u (x + h • Pi.single l 1) - 2 * u x + u (x + (-h) • Pi.single l 1)) / h ^ 2| ≤
      B * h ^ 2 / 12 := by
  have hd : ∀ k : ℕ, k ≤ 3 → Differentiable ℝ ((partialDeriv l)^[k] u) := by
    intro k hk
    have : ∀ k ≤ 4, ContDiff ℝ (4 - k : ℕ) ((partialDeriv l)^[k] u) := by
      intro k hk
      induction k with
      | zero => simpa using hu
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (ih (by omega)).partialDeriv (by norm_cast; omega) l
    exact (this k (by omega)).differentiable (by norm_cast; omega)
  set g : ℕ → ℝ → ℝ := fun k t => (partialDeriv l)^[k] u (x + t • Pi.single l 1)
  have hg : ∀ k ≤ 3, ∀ t, HasDerivAt (g k) (g (k + 1) t) t := fun k hk t => by
    have := hasDerivAt_line (hd k hk) x l t
    simpa [g, Function.iterate_succ_apply'] using this
  have key := abs_secondDiff_sub_le (g := g 0) (g₁ := g 1) (g₂ := g 2) (g₃ := g 3)
    (g₄ := g 4) (B := B) hh.le (fun t _ => hg 0 (by omega) t) (fun t _ => hg 1 (by omega) t)
    (fun t _ => hg 2 (by omega) t) (fun t _ => hg 3 le_rfl t) hB
  simp only [g, Function.iterate_zero, id, zero_smul, add_zero, Function.iterate_succ,
    Function.comp] at key
  have hh2 : 0 < h ^ 2 := by positivity
  rw [show partialDeriv l (partialDeriv l u) x -
      (u (x + h • Pi.single l 1) - 2 * u x + u (x + (-h) • Pi.single l 1)) / h ^ 2 =
      -(u (x + h • Pi.single l 1) - 2 * u x + u (x + (-h) • Pi.single l 1) -
        h ^ 2 * partialDeriv l (partialDeriv l u) x) / h ^ 2 by field_simp; ring,
    abs_div, abs_neg, abs_of_pos hh2, div_le_iff₀ hh2]
  calc _ ≤ B * h ^ 4 / 12 := key
    _ = B * h ^ 2 / 12 * h ^ 2 := by ring

/-! ### Classical solutions of the Neumann problem -/

/-- A **classical solution of the heat equation with natural boundary conditions**
`uₜ = Δu` on `[0, T] × Q̄`, `∂_ν u = 0` on `∂Q`: `C⁴` on `ℝⁿ` at each time, with the bounds
`|∂ᵢ²u| ≤ B₂` and `|∂ᵢ⁴u| ≤ B₄` on `Q̄`. -/
structure NeumannSolution (b : Fin n → ℝ) (s T : ℝ) where
  /-- the solution -/
  u : ℝ → (Fin n → ℝ) → ℝ
  /-- its time derivative -/
  u₁ : ℝ → (Fin n → ℝ) → ℝ
  contDiff : ∀ t ∈ Icc 0 T, ContDiff ℝ 4 (u t)
  hasDerivAt : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, HasDerivAt (fun t => u t x) (u₁ t x) t
  heat : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, u₁ t x = MaxNormHeat.laplacian (u t) x
  /-- the natural boundary condition `∂_ν u = 0` on the faces -/
  neumann : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, ∀ i, x i = b i ∨ x i = b i + s →
    partialDeriv i (u t) x = 0
  /-- the bound of the second derivatives -/
  B₂ : ℝ
  bound₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, ∀ i,
    |partialDeriv i (partialDeriv i (u t)) x| ≤ B₂
  /-- the bound of the fourth derivatives -/
  B₄ : ℝ
  bound₄ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, ∀ i, |(partialDeriv i)^[4] (u t) x| ≤ B₄

theorem node_add_mem_closedCube (hs : 0 < s) {p : Fin n → ℤ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ N + 1)
    (l : Fin n) {τ : ℝ} (h1 : 0 ≤ meshSize s N * p l + τ)
    (h2 : meshSize s N * p l + τ ≤ s) :
    node b (meshSize s N) p + τ • Pi.single l 1 ∈ closedCube b s := by
  have hh := meshSize_pos hs N
  have hm := meshSize_mul s N
  push_cast at hm
  intro i _
  have a1 : (0 : ℝ) ≤ p i := by exact_mod_cast (hp i).1
  have a2 : (p i : ℝ) ≤ N + 1 := by exact_mod_cast (hp i).2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, node_coord, Set.mem_Icc]
  by_cases hi : i = l
  · subst hi; simp only [Pi.single_eq_same, mul_one]; constructor <;> linarith
  · simp only [Pi.single_eq_of_ne hi, mul_zero, add_zero]; constructor <;> nlinarith

theorem node_sub_single_one (b : Fin n → ℝ) (h : ℝ) (p : Fin n → ℤ) (l : Fin n) :
    node b h (p - Pi.single l 1) = node b h p + (-h) • Pi.single l 1 := by
  rw [node_eq_sub_single_add b h p l]
  simp [add_assoc]

/-- The stencil terms of a function with `∂_ν u = 0` are bounded by `max |∂ₗ²u|`. -/
theorem abs_stencilTerm_le (hs : 0 < s) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) {B : ℝ}
    (hB : ∀ x ∈ closedCube b s, ∀ i, |partialDeriv i (partialDeriv i u) x| ≤ B)
    (hneu : ∀ x ∈ closedCube b s, ∀ i, x i = b i ∨ x i = b i + s → partialDeriv i u x = 0)
    (σ : Equiv.Perm (Fin n)) (l : Fin n) {p : Fin n → ℤ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ N + 1) :
    |upCount N σ l p * edgeQuot b (meshSize s N) u l p -
        downCount N σ l p * edgeQuot b (meshSize s N) u l (p - Pi.single l 1)| ≤ B := by
  set h := meshSize s N
  have hh := meshSize_pos hs N
  have hm := meshSize_mul s N
  push_cast at hm
  have hhs := meshSize_le hs N
  set x := node b h p
  have hx : x ∈ closedCube b s := by
    simpa using node_add_mem_closedCube (b := b) hs hp l (τ := 0)
      (by have : (0 : ℝ) ≤ p l := by exact_mod_cast (hp l).1
          positivity)
      (by have : (p l : ℝ) ≤ N + 1 := by exact_mod_cast (hp l).2
          nlinarith)
  have hu0 := upCount_nonneg (N := N) σ l p
  have hu1 := upCount_le_one (N := N) σ l p
  have hd0 := upCount_nonneg (N := N) σ l (p - Pi.single l 1)
  have hd1 := upCount_le_one (N := N) σ l (p - Pi.single l 1)
  rw [← downCount] at hd0 hd1
  have hh2 : 0 < h ^ 2 := by positivity
  have hh' : h ≠ 0 := hh.ne'
  simp only [edgeQuot]
  rw [node_add_single_one, node_sub_single_one, sub_add_cancel]
  rcases (hp l).1.eq_or_lt with h0 | h0
  · -- the lower face
    have hl : p l = 0 := h0.symm
    rw [downCount_eq_zero σ hl, zero_mul, sub_zero]
    have hT := abs_axis_taylor_le hu x l h (B := B) fun τ hτ => hB _ (node_add_mem_closedCube hs hp l
      (by rw [Set.uIcc_of_le hh.le] at hτ; simp [hl]; exact hτ.1)
      (by rw [Set.uIcc_of_le hh.le] at hτ; simp [hl]; linarith [hτ.2])) l
    rw [hneu x hx l (Or.inl (by simp [x, node_coord, hl])), mul_zero, sub_zero] at hT
    rw [abs_mul, abs_of_nonneg hu0, div_div, ← sq, abs_div, abs_of_pos hh2]
    calc upCount N σ l p * (|u (x + h • Pi.single l 1) - u x| / h ^ 2)
        ≤ 1 * (B * h ^ 2 / 2 / h ^ 2) := mul_le_mul hu1 (div_le_div_of_nonneg_right hT hh2.le)
          (by positivity) zero_le_one
      _ = B / 2 := by field_simp
      _ ≤ B := by
          have : 0 ≤ B := (abs_nonneg _).trans (hB x hx l)
          linarith
  rcases (hp l).2.eq_or_lt with hN | hN
  · -- the upper face
    rw [upCount_eq_zero σ hN, zero_mul, zero_sub, abs_neg]
    have hT := abs_axis_taylor_le hu x l (-h) (B := B) fun τ hτ => hB _ (node_add_mem_closedCube hs hp l
      (by rw [Set.uIcc_of_ge (by linarith)] at hτ; rw [hN]; push_cast; nlinarith [hτ.1])
      (by rw [Set.uIcc_of_ge (by linarith)] at hτ; rw [hN]; push_cast; nlinarith [hτ.2])) l
    rw [hneu x hx l (Or.inr (by simp [x, node_coord, hN]; linarith)), mul_zero, sub_zero] at hT
    rw [abs_mul, abs_of_nonneg hd0, div_div, ← sq, abs_div, abs_of_pos hh2, abs_sub_comm]
    rw [neg_sq] at hT
    calc downCount N σ l p * (|u (x + (-h) • Pi.single l 1) - u x| / h ^ 2)
        ≤ 1 * (B * h ^ 2 / 2 / h ^ 2) := mul_le_mul hd1 (div_le_div_of_nonneg_right hT hh2.le)
          (by positivity) zero_le_one
      _ = B / 2 := by field_simp
      _ ≤ B := by
          have : 0 ≤ B := (abs_nonneg _).trans (hB x hx l)
          linarith
  · -- an interior coordinate
    rw [← upCount_eq_downCount σ (by omega) (by omega)]
    have h1 : (1 : ℝ) ≤ p l := by exact_mod_cast h0
    have h2 : (p l : ℝ) ≤ N := by exact_mod_cast (show p l ≤ N by omega)
    have hD := abs_axis_secondDiff_le hu x l (h := h) (B := B) fun τ hτ => hB _
      (node_add_mem_closedCube hs hp l (by rw [abs_of_pos hh] at hτ; nlinarith [hτ.1])
        (by rw [abs_of_pos hh] at hτ; nlinarith [hτ.2])) l
    rw [← mul_sub, abs_mul, abs_of_nonneg hu0]
    have e : (u (x + h • Pi.single l 1) - u x) / h / h - (u x - u (x + (-h) • Pi.single l 1)) / h / h =
        (u (x + h • Pi.single l 1) - 2 * u x + u (x + (-h) • Pi.single l 1)) / h ^ 2 := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos hh2]
    calc upCount N σ l p * (|u (x + h • Pi.single l 1) - 2 * u x + u (x + (-h) • Pi.single l 1)| /
          h ^ 2) ≤ 1 * (B * h ^ 2 / h ^ 2) :=
          mul_le_mul hu1 (div_le_div_of_nonneg_right hD hh2.le) (by positivity) zero_le_one
      _ = B := by rw [one_mul, mul_div_assoc, div_self hh2.ne', mul_one]

/-- A node is interior or has a coordinate on a face. -/
theorem interior_or_boundary (p : Nodes n N) :
    (p : Fin n → ℤ) ∈ interiorNodes n (N + 1) ∨
      ∃ l, (p : Fin n → ℤ) l = 0 ∨ (p : Fin n → ℤ) l = N + 1 := by
  have hp := mem_closedNodes.1 p.2
  by_cases h : ∀ j, 1 ≤ (p : Fin n → ℤ) j ∧ (p : Fin n → ℤ) j ≤ N
  · exact Or.inl (mem_interiorNodes.2 h)
  · push Not at h
    obtain ⟨l, hl⟩ := h
    refine Or.inr ⟨l, ?_⟩
    have := hp l
    by_cases h1 : 1 ≤ (p : Fin n → ℤ) l
    · have := hl h1; omega
    · omega

/-- **Consistency at the boundary nodes is `O(1)`**: for `u ∈ C²` with `∂_ν u = 0` and
`|∂ᵢ²u| ≤ B` on `Q̄`, `|Δu(p) - (Lₕ Iₕ u)(p)| ≤ n B (1 + (n + 1)!)` at every node with a
coordinate on a face. -/
theorem abs_laplacian_sub_boundary_le (hs : 0 < s) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u)
    {B : ℝ} (hB : ∀ x ∈ closedCube b s, ∀ i, |partialDeriv i (partialDeriv i u) x| ≤ B)
    (hneu : ∀ x ∈ closedCube b s, ∀ i, x i = b i ∨ x i = b i + s → partialDeriv i u x = 0)
    (p : Nodes n N) {l₀ : Fin n}
    (hl₀ : (p : Fin n → ℤ) l₀ = 0 ∨ (p : Fin n → ℤ) l₀ = N + 1) :
    |MaxNormHeat.laplacian u (node b (meshSize s N) p) -
        neumannLaplacian b hs N (interp b s N u) p| ≤ n * B * (1 + (n + 1).factorial) := by
  have hp := mem_closedNodes.1 p.2
  have hx : node b (meshSize s N) p ∈ closedCube b s := by
    simpa using node_add_mem_closedCube (b := b) hs hp l₀ (τ := 0)
      (by have : (0 : ℝ) ≤ (p : Fin n → ℤ) l₀ := by exact_mod_cast (hp l₀).1
          have := meshSize_pos hs N
          positivity)
      (by have : ((p : Fin n → ℤ) l₀ : ℝ) ≤ N + 1 := by exact_mod_cast (hp l₀).2
          have := meshSize_pos hs N
          have hm := meshSize_mul s N
          push_cast at hm
          nlinarith)
  have hΔ : |MaxNormHeat.laplacian u (node b (meshSize s N) p)| ≤ n * B := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |partialDeriv i (partialDeriv i u) (node b (meshSize s N) p)|
        ≤ ∑ _i : Fin n, B := sum_le_sum fun i _ => hB _ hx i
      _ = n * B := by simp
  have hS : |stencilSum b s N u p| ≤ n.factorial * n * B := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ σ : Equiv.Perm (Fin n), |∑ l, (upCount N σ l p * edgeQuot b (meshSize s N) u l p -
          downCount N σ l p * edgeQuot b (meshSize s N) u l ((p : Fin n → ℤ) - Pi.single l 1))|
        ≤ ∑ _σ : Equiv.Perm (Fin n), ∑ _l : Fin n, B := sum_le_sum fun σ _ =>
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ =>
            abs_stencilTerm_le hs hu hB hneu σ l hp)
      _ = _ := by simp [Fintype.card_perm]; ring
  have hC := one_le_vertexCount_of_boundary hp hl₀
  have hL : |neumannLaplacian b hs N (interp b s N u) p| ≤ (n + 1).factorial * n * B := by
    rw [neumannLaplacian_interp, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n + 1),
      abs_of_pos (by linarith : (0 : ℝ) < vertexCount N (p : Fin n → ℤ))]
    calc (n + 1) * |stencilSum b s N u p| / vertexCount N (p : Fin n → ℤ)
        ≤ (n + 1) * |stencilSum b s N u p| := div_le_self (by positivity) hC
      _ ≤ (n + 1) * (n.factorial * n * B) := mul_le_mul_of_nonneg_left hS (by positivity)
      _ = _ := by rw [Nat.factorial_succ]; push_cast; ring
  calc _ ≤ |MaxNormHeat.laplacian u (node b (meshSize s N) p)| +
        |neumannLaplacian b hs N (interp b s N u) p| := abs_sub _ _
    _ ≤ n * B + (n + 1).factorial * n * B := add_le_add hΔ hL
    _ = _ := by ring

/-- `Lₕ Iₕ u` at an interior node is the `(2n + 1)`-point difference Laplacian. -/
theorem neumannLaplacian_interp_interior (hs : 0 < s) (u : (Fin n → ℝ) → ℝ) {p : Nodes n N}
    (hp : (p : Fin n → ℤ) ∈ interiorNodes n (N + 1)) :
    neumannLaplacian b hs N (interp b s N u) p = ∑ l,
      (u (node b (meshSize s N) p + meshSize s N • Pi.single l 1) -
        2 * u (node b (meshSize s N) p) +
        u (node b (meshSize s N) p + (-meshSize s N) • Pi.single l 1)) / meshSize s N ^ 2 := by
  rw [neumannLaplacian_apply, p1Stiffness_congr_right _ _ (w' := u) fun T hT j => ?_]
  · have := neg_p1Stiffness_div_lumpedMass b hs (N + 1) hp u
    rw [meshSize] at *
    rw [this]
    refine sum_congr rfl fun l _ => ?_
    rw [node_add_single_one, node_sub_single_one]
  · obtain ⟨q, hq, e⟩ := exists_node_eq_points hs hT j
    rw [e, nodal_node hs (q := ⟨q, mem_closedNodes.2 hq⟩)]
    rfl

/-- **Consistency at the interior nodes is `O(h²)`**: `|Δu(p) - (Lₕ Iₕ u)(p)| ≤ n B h² / 12`
for `u ∈ C⁴` with `|∂ᵢ⁴u| ≤ B` on `Q̄`. -/
theorem abs_laplacian_sub_interior_le (hs : 0 < s) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 4 u)
    {B : ℝ} (hB : ∀ x ∈ closedCube b s, ∀ i, |(partialDeriv i)^[4] u x| ≤ B) {p : Nodes n N}
    (hp : (p : Fin n → ℤ) ∈ interiorNodes n (N + 1)) :
    |MaxNormHeat.laplacian u (node b (meshSize s N) p) -
        neumannLaplacian b hs N (interp b s N u) p| ≤ n * B * meshSize s N ^ 2 / 12 := by
  have hh := meshSize_pos hs N
  have hm := meshSize_mul s N
  push_cast at hm
  have hpc := mem_closedNodes.1 p.2
  have hpi := mem_interiorNodes.1 hp
  rw [neumannLaplacian_interp_interior hs u hp, MaxNormHeat.laplacian, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _l : Fin n, B * meshSize s N ^ 2 / 12 := sum_le_sum fun l _ =>
        abs_partialDeriv_sub_secondDiff_le hu hh _ l fun t ht => hB _
          (node_add_mem_closedCube hs hpc l
            (by have : (1 : ℝ) ≤ (p : Fin n → ℤ) l := by exact_mod_cast (hpi l).1
                nlinarith [ht.1])
            (by have : ((p : Fin n → ℤ) l : ℝ) ≤ N := by exact_mod_cast (hpi l).2
                nlinarith [ht.2])) l
    _ = _ := by simp; ring

/-! ### The semidiscrete error in the maximum norm -/

/-- The interior truncation error `n B₄ h² / 12`. -/
def NeumannSolution.defect {T : ℝ} (S : NeumannSolution b s T) (N : ℕ) : ℝ :=
  n * S.B₄ * meshSize s N ^ 2 / 12

/-- The boundary truncation bound `G = n B₂ (1 + (n + 1)!)`. -/
def NeumannSolution.boundaryDefect {T : ℝ} (S : NeumannSolution b s T) : ℝ :=
  n * S.B₂ * (1 + (n + 1).factorial)

/-- **The semidiscrete error of the Neumann problem in the maximum norm at the nodes**: for every
classical solution and `t ∈ [0, T]`,
`‖Iₕ u(t) - e^{tLₕ} v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + t n B₄ h² / 12 + K_n G h (t / s + s)`:
`O(h)` uniformly in the mesh, from `O(h²)` consistency at the interior nodes and `O(1)`
consistency at the boundary nodes, through the barrier `χ = |x - c|²` (`Lₕ χ ≤ -s / (2 h n!)` at
the boundary nodes) and the maximum principle. -/
theorem norm_interp_sub_exp_le (hs : 0 < s) {T : ℝ} (S : NeumannSolution b s T) (N : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 T) (v : Space n N) :
    ‖interp b s N (S.u t) - exp (t • neumannLaplacian b hs N) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + t * S.defect N +
        layerConst n * S.boundaryDefect * meshSize s N * (t / s + s) := by
  set L := neumannLaplacian b hs N
  set h := meshSize s N
  have hh := meshSize_pos hs N
  have hL := isSubMarkovGenerator b hs N
  have hL1 := neumannLaplacian_apply_one b hs N
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hh' : h ≠ 0 := hh.ne'
  set E : ℝ → Space n N := fun r => interp b s N (S.u r) - exp (r • L) v
  set E' : ℝ → Space n N := fun r => interp b s N (S.u₁ r) - L (exp (r • L) v)
  have hnode : ∀ p : Nodes n N, node b h p ∈ closedCube b s := fun p => by
    have hp := mem_closedNodes.1 p.2
    have hm := meshSize_mul s N
    push_cast at hm
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨l⟩⟩
    · intro i; exact (hn.false i).elim
    · simpa using node_add_mem_closedCube (b := b) hs hp l (τ := 0)
        (by have : (0 : ℝ) ≤ (p : Fin n → ℤ) l := by exact_mod_cast (hp l).1
            positivity)
        (by have : ((p : Fin n → ℤ) l : ℝ) ≤ N + 1 := by exact_mod_cast (hp l).2
            nlinarith)
  have hE : ∀ r ∈ Icc 0 t, HasDerivAt E (E' r) r := fun r hr =>
    (hasDerivAt_pi.2 fun p => S.hasDerivAt r (hsub hr) _ (hnode p)).sub
      (C0Group.hasDerivAt_exp_ofReal_smul_apply L v r)
  have hτ : ∀ r ∈ Icc 0 t, ∀ p, (E' r - L (E r)) p =
      MaxNormHeat.laplacian (S.u r) (node b h p) - L (interp b s N (S.u r)) p := fun r hr p => by
    simp only [E, E', map_sub, Pi.sub_apply]
    rw [show interp b s N (S.u₁ r) p = S.u₁ r (node b h p) from rfl,
      S.heat r (hsub hr) _ (hnode p)]
    ring
  set D := S.defect N
  set G := S.boundaryDefect
  have hb : b ∈ closedCube b s := fun i _ => ⟨le_rfl, by linarith⟩
  have hD0 : 0 ≤ D := by
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨l⟩⟩
    · obtain rfl : n = 0 := by rw [← Fintype.card_fin n]; exact Fintype.card_eq_zero_iff.2 hn
      simp [D, NeumannSolution.defect]
    · have := (abs_nonneg _).trans (S.bound₄ 0 ⟨le_rfl, ht.1.trans ht.2⟩ b hb l)
      simp only [D, NeumannSolution.defect]; positivity
  have hG0 : 0 ≤ G := by
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨l⟩⟩
    · obtain rfl : n = 0 := by rw [← Fintype.card_fin n]; exact Fintype.card_eq_zero_iff.2 hn
      simp [G, NeumannSolution.boundaryDefect]
    · have := (abs_nonneg _).trans (S.bound₂ 0 ⟨le_rfl, ht.1.trans ht.2⟩ b hb l)
      simp only [G, NeumannSolution.boundaryDefect]; positivity
  have hdef : ∀ r ∈ Icc 0 t, ∀ p : Nodes n N,
      ((p : Fin n → ℤ) ∈ interiorNodes n (N + 1) → |(E' r - L (E r)) p| ≤ D) ∧
      (∀ l, (p : Fin n → ℤ) l = 0 ∨ (p : Fin n → ℤ) l = N + 1 → |(E' r - L (E r)) p| ≤ G) :=
    fun r hr p => by
      rw [hτ r hr p]
      exact ⟨fun hp => abs_laplacian_sub_interior_le hs (S.contDiff r (hsub hr))
          (S.bound₄ r (hsub hr)) hp,
        fun l hl => abs_laplacian_sub_boundary_le hs ((S.contDiff r (hsub hr)).of_le (by norm_num))
          (S.bound₂ r (hsub hr)) (S.neumann r (hsub hr)) p hl⟩
  have hK0 : 0 < layerConst n := by unfold layerConst; positivity
  have hbd0 : 0 ≤ ‖interp b s N (S.u 0) - v‖ + t * D + layerConst n * G * h * (t / s + s) := by
    have h1 := norm_nonneg (interp b s N (S.u 0) - v)
    have h2 : 0 ≤ t * D := mul_nonneg ht.1 hD0
    have h3 : 0 ≤ layerConst n * G * h * (t / s + s) :=
      mul_nonneg (mul_nonneg (mul_nonneg hK0.le hG0) hh.le) (add_nonneg (div_nonneg ht.1 hs.le) hs.le)
    linarith
  refine (pi_norm_le_iff_of_nonneg hbd0).2 fun p => ?_
  rw [Real.norm_eq_abs]
  by_cases hK : layerConst n ≤ s / h
  · -- the barrier `κ χ`
    set κ := 2 * n.factorial * h * G / s
    have hκ : 0 ≤ κ := by positivity
    set ψ : Space n N := κ • interp b s N (chi b s)
    have hψ : 0 ≤ ψ := fun q => mul_nonneg hκ (chi_nonneg b s _)
    have hbar := abs_apply_le_of_barrier hL hL1 ht.1 hE (A := D + 2 * n * κ) hψ (fun r hr q => by
      have hLψ : L ψ q = κ * L (interp b s N (chi b s)) q := by
        show L (κ • interp b s N (chi b s)) q = _
        rw [map_smul]; rfl
      rcases interior_or_boundary q with hq | ⟨l, hl⟩
      · rw [hLψ, neumannLaplacian_interp_chi_interior hs hq]
        linarith [(hdef r hr q).1 hq]
      · have hb' := neumannLaplacian_interp_chi_boundary (b := b) hs q hl hK
        have : κ * L (interp b s N (chi b s)) q ≤ -G := by
          calc κ * L (interp b s N (chi b s)) q ≤ κ * (-(s / h) / (2 * n.factorial)) :=
                mul_le_mul_of_nonneg_left hb' hκ
            _ = -G := by simp only [κ]; field_simp
        rw [hLψ]
        have h2n : 0 ≤ 2 * (n : ℝ) * κ := mul_nonneg (by positivity) hκ
        linarith [(hdef r hr q).2 l hl]) p
    have hχ : ψ p ≤ κ * (n * s ^ 2 / 4) := mul_le_mul_of_nonneg_left (chi_le b (hnode p)) hκ
    have hfac : (0 : ℝ) ≤ n.factorial := by positivity
    calc |E t p| ≤ ‖E 0‖ + ψ p + t * (D + 2 * n * κ) := hbar
      _ ≤ ‖E 0‖ + κ * (n * s ^ 2 / 4) + t * (D + 2 * n * κ) := by linarith
      _ ≤ _ := by
          have e0 : E 0 = interp b s N (S.u 0) - v := by simp [E]
          rw [e0]
          have hGh : 0 ≤ G * h := mul_nonneg hG0 hh.le
          have hn1 : (n : ℝ) * n.factorial / 2 ≤ layerConst n := by
            unfold layerConst; nlinarith [mul_nonneg (Nat.cast_nonneg n) hfac]
          have hn2 : 4 * (n : ℝ) * n.factorial ≤ layerConst n := by
            unfold layerConst; nlinarith [mul_nonneg (Nat.cast_nonneg n) hfac]
          have h1 : κ * (n * s ^ 2 / 4) ≤ layerConst n * G * h * s := by
            have e : κ * (n * s ^ 2 / 4) = (n * n.factorial / 2) * (G * h * s) := by
              simp only [κ]; field_simp; ring
            rw [e, show layerConst n * G * h * s = layerConst n * (G * h * s) by ring]
            exact mul_le_mul_of_nonneg_right hn1 (mul_nonneg hGh hs.le)
          have h2 : t * (2 * n * κ) ≤ layerConst n * G * h * (t / s) := by
            have e : t * (2 * n * κ) = (4 * n * n.factorial) * (G * h * (t / s)) := by
              simp only [κ]; field_simp; ring
            rw [e, show layerConst n * G * h * (t / s) = layerConst n * (G * h * (t / s)) by ring]
            exact mul_le_mul_of_nonneg_right hn2 (mul_nonneg hGh (div_nonneg ht.1 hs.le))
          nlinarith
  · -- large mesh sizes: no barrier
    have hbar := abs_apply_le_of_barrier hL hL1 ht.1 hE (A := D + G) le_rfl (fun r hr q => by
      simp only [map_zero, Pi.zero_apply, sub_zero]
      rcases interior_or_boundary q with hq | ⟨l, hl⟩
      · linarith [(hdef r hr q).1 hq]
      · linarith [(hdef r hr q).2 l hl]) p
    have e0 : E 0 = interp b s N (S.u 0) - v := by simp [E]
    rw [e0] at hbar
    have hKh : s ≤ layerConst n * h := by
      rw [not_le, div_lt_iff₀ hh] at hK; linarith
    have : t * G ≤ layerConst n * G * h * (t / s) := by
      rw [mul_div_assoc', le_div_iff₀ hs]
      nlinarith [mul_nonneg ht.1 hG0]
    have : 0 ≤ layerConst n * G * h * s := by positivity
    simp only [Pi.zero_apply, add_zero] at hbar
    nlinarith

/-! ### A classical solution: the first Neumann eigenmode -/

/-- The shifted centre `b - s/2`: `sin(a(y - (bᵢ - s/2))) = cos(a(y - bᵢ))`, `a = π/s`. -/
def cosCentre (b : Fin n → ℝ) (s : ℝ) : Fin n → ℝ := b - (s / 2) • fun _ => 1

/-- **The first Neumann eigenmode** `u(t, x) = e^{-λt} ∏ᵢ cos(π(xᵢ - bᵢ)/s)`, `λ = n π²/s²`
(written `∏ᵢ sin(π(xᵢ - bᵢ + s/2)/s)`): a classical solution of the Neumann problem on every
`[0, T] × Q̄` with `B₂ = (π/s)²`, `B₄ = (π/s)⁴`. -/
def cosSolution (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) : NeumannSolution b s T where
  u t x := Real.exp (-(n * sineFreq s ^ 2) * t) *
    ∏ j, sineDeriv (sineFreq s) (cosCentre b s j) 0 (x j)
  u₁ t x := -(n * sineFreq s ^ 2) * (Real.exp (-(n * sineFreq s ^ 2) * t) *
    ∏ j, sineDeriv (sineFreq s) (cosCentre b s j) 0 (x j))
  contDiff t _ := by simp only [sineDeriv]; fun_prop
  hasDerivAt t _ x _ := by
    have := ((Real.hasDerivAt_exp _).comp t
      ((hasDerivAt_id t).const_mul (-(n * sineFreq s ^ 2)))).mul_const
      (∏ j, sineDeriv (sineFreq s) (cosCentre b s j) 0 (x j))
    exact this.congr_deriv (by simp; ring)
  heat t _ x _ := by
    have e : ∀ i, partialDeriv i (partialDeriv i (fun x : Fin n → ℝ =>
        Real.exp (-(n * sineFreq s ^ 2) * t) *
          ∏ j, sineDeriv (sineFreq s) (cosCentre b s j) 0 (x j))) x =
        -sineFreq s ^ 2 * (Real.exp (-(n * sineFreq s ^ 2) * t) *
          ∏ j, sineDeriv (sineFreq s) (cosCentre b s j) 0 (x j)) := fun i => by
      have := congrFun (iterate_partialDeriv_sine (cosCentre b s) (sineFreq s)
        (Real.exp (-(n * sineFreq s ^ 2) * t)) i 2 (by omega)) x
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id] at this
      rw [this, sineFactors, show sineDeriv (sineFreq s) (cosCentre b s i) 2 =
        fun y => -sineFreq s ^ 2 * sineDeriv (sineFreq s) (cosCentre b s i) 0 y from rfl,
        prod_update_const_mul (fun j => sineDeriv (sineFreq s) (cosCentre b s j) 0)]
      ring
    simp only [MaxNormHeat.laplacian, e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  neumann t _ x _ i hi := by
    have := congrFun (iterate_partialDeriv_sine (cosCentre b s) (sineFreq s)
      (Real.exp (-(n * sineFreq s ^ 2) * t)) i 1 (by omega)) x
    simp only [Function.iterate_one] at this
    rw [this]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
    simp only [sineFactors, Function.update_self, sineDeriv, cosCentre, sineFreq, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, mul_one]
    refine mul_eq_zero_of_right _ ?_
    rcases hi with h | h <;> rw [h]
    · rw [show Real.pi / s * (b i - (b i - s / 2)) = Real.pi / 2 by field_simp; ring,
        Real.cos_pi_div_two]
    · rw [show Real.pi / s * (b i + s - (b i - s / 2)) = Real.pi / 2 + Real.pi by
        field_simp; ring, Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
  B₂ := sineFreq s ^ 2
  bound₂ t ht x _ i := by
    have := congrFun (iterate_partialDeriv_sine (cosCentre b s) (sineFreq s)
      (Real.exp (-(n * sineFreq s ^ 2) * t)) i 2 (by omega)) x
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id] at this
    rw [this, sineFactors, show sineDeriv (sineFreq s) (cosCentre b s i) 2 =
      fun y => -sineFreq s ^ 2 * sineDeriv (sineFreq s) (cosCentre b s i) 0 y from rfl,
      prod_update_const_mul (fun j => sineDeriv (sineFreq s) (cosCentre b s j) 0), abs_mul,
      abs_mul, abs_of_pos (Real.exp_pos _), Finset.abs_prod, abs_neg]
    have h1 : Real.exp (-(n * sineFreq s ^ 2) * t) ≤ 1 :=
      Real.exp_le_one_iff.2 (by rw [neg_mul]; exact neg_nonpos.2 (mul_nonneg (by positivity) ht.1))
    have h2 : ∏ j, |sineDeriv (sineFreq s) (cosCentre b s j) 0 (x j)| ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => Real.abs_sin_le_one _
    rw [abs_of_nonneg (by positivity)]
    calc Real.exp (-(n * sineFreq s ^ 2) * t) *
          (sineFreq s ^ 2 * ∏ j, |sineDeriv (sineFreq s) (cosCentre b s j) 0 (x j)|)
        ≤ 1 * (sineFreq s ^ 2 * 1) := by gcongr
      _ = sineFreq s ^ 2 := by ring
  B₄ := sineFreq s ^ 4
  bound₄ t ht x _ i := by
    have := congrFun (iterate_partialDeriv_sine (cosCentre b s) (sineFreq s)
      (Real.exp (-(n * sineFreq s ^ 2) * t)) i 4 le_rfl) x
    rw [this, sineFactors, show sineDeriv (sineFreq s) (cosCentre b s i) 4 =
      fun y => sineFreq s ^ 4 * sineDeriv (sineFreq s) (cosCentre b s i) 0 y from rfl,
      prod_update_const_mul (fun j => sineDeriv (sineFreq s) (cosCentre b s j) 0), abs_mul,
      abs_mul, abs_of_pos (Real.exp_pos _), Finset.abs_prod]
    have h1 : Real.exp (-(n * sineFreq s ^ 2) * t) ≤ 1 :=
      Real.exp_le_one_iff.2 (by rw [neg_mul]; exact neg_nonpos.2 (mul_nonneg (by positivity) ht.1))
    have h2 : ∏ j, |sineDeriv (sineFreq s) (cosCentre b s j) 0 (x j)| ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => Real.abs_sin_le_one _
    rw [abs_of_nonneg (by positivity)]
    calc Real.exp (-(n * sineFreq s ^ 2) * t) *
          (sineFreq s ^ 4 * ∏ j, |sineDeriv (sineFreq s) (cosCentre b s j) 0 (x j)|)
        ≤ 1 * (sineFreq s ^ 4 * 1) := by gcongr
      _ = sineFreq s ^ 4 := by ring

/-- The first Neumann eigenmode is `1` at the corner `b` at `t = 0`. -/
theorem cosSolution_u_zero_corner (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) :
    (cosSolution b hs T).u 0 b = 1 := by
  simp only [cosSolution, sineDeriv, sineFreq, cosCentre, mul_zero, Real.exp_zero, one_mul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [show Real.pi / s * (b j - (b j - s / 2)) = Real.pi / 2 by field_simp; ring,
    Real.sin_pi_div_two]

/-! ### The verdict -/

/-- **The maximum-norm Neumann family**: the lumped-mass Neumann Laplacians of the levels
`N + 1`, a uniformly stable family with `M = 1` (`isSubMarkovGenerator`). -/
abbrev family (b : Fin n → ℝ) (hs : 0 < s) : StableFamily ℝ ℕ where
  X N := Space n N
  L N := neumannLaplacian b hs N
  M := 1
  M_nonneg := zero_le_one
  norm_exp_le N t ht := by simpa using (isSubMarkovGenerator b hs N).norm_exp_smul_le_one ht

/-- The conclusions of `maxNormNeumann` for the cube `b + (0, s)ⁿ`. -/
structure Verdict (b : Fin n → ℝ) (hs : 0 < s) : Prop where
  /-- the discrete maximum principle: `e^{tLₕ}` is positive and contractive in the maximum norm -/
  maximumPrinciple (N : ℕ) : IsSubMarkovGenerator (neumannLaplacian b hs N)
  /-- conservation: `Lₕ 𝟙 = 0` -/
  conservation (N : ℕ) : neumannLaplacian b hs N (fun _ => 1) = 0
  /-- the stencil at every node, `(Lₕ Iₕ u)(p) = (n + 1) S_u(p) / C(p)` -/
  stencil (N : ℕ) (u : (Fin n → ℝ) → ℝ) (p : Nodes n N) :
    neumannLaplacian b hs N (interp b s N u) p =
      (n + 1) * stencilSum b s N u p / vertexCount N (p : Fin n → ℤ)
  /-- consistency `O(h²)` at the interior nodes -/
  consistency_interior (N : ℕ) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 4 u) {B : ℝ}
    (hB : ∀ x ∈ closedCube b s, ∀ i, |(partialDeriv i)^[4] u x| ≤ B) {p : Nodes n N}
    (hp : (p : Fin n → ℤ) ∈ interiorNodes n (N + 1)) :
    |MaxNormHeat.laplacian u (node b (meshSize s N) p) -
        neumannLaplacian b hs N (interp b s N u) p| ≤ n * B * meshSize s N ^ 2 / 12
  /-- consistency `O(1)` at the boundary nodes, for `∂_ν u = 0` -/
  consistency_boundary (N : ℕ) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) {B : ℝ}
    (hB : ∀ x ∈ closedCube b s, ∀ i, |partialDeriv i (partialDeriv i u) x| ≤ B)
    (hneu : ∀ x ∈ closedCube b s, ∀ i, x i = b i ∨ x i = b i + s → partialDeriv i u x = 0)
    (p : Nodes n N) {l : Fin n} (hl : (p : Fin n → ℤ) l = 0 ∨ (p : Fin n → ℤ) l = N + 1) :
    |MaxNormHeat.laplacian u (node b (meshSize s N) p) -
        neumannLaplacian b hs N (interp b s N u) p| ≤ n * B * (1 + (n + 1).factorial)
  /-- the barrier: `Lₕ χ ≤ -s / (2 h n!)` at the boundary nodes, `s / h ≥ K_n` -/
  barrier (N : ℕ) (p : Nodes n N) {l : Fin n}
    (hl : (p : Fin n → ℤ) l = 0 ∨ (p : Fin n → ℤ) l = N + 1)
    (hK : layerConst n ≤ s / meshSize s N) :
    neumannLaplacian b hs N (interp b s N (chi b s)) p ≤
      -(s / meshSize s N) / (2 * n.factorial)
  /-- the semidiscrete error `O(h)` in the maximum norm at the nodes -/
  semidiscrete {T : ℝ} (S : NeumannSolution b s T) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (v : Space n N) :
    ‖interp b s N (S.u t) - exp (t • neumannLaplacian b hs N) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + t * S.defect N +
        layerConst n * S.boundaryDefect * meshSize s N * (t / s + s)
  /-- the verdict of the Banach layer for the Neumann family (`M = 1`) -/
  banach : (family b hs).Verdict

/-- **The heat equation with natural boundary conditions in the maximum norm** (lumped-mass `P₁`
elements on the Freudenthal meshes of the cube `b + (0, s)ⁿ`, all nodes): see `Verdict`.
[CiarletRaviart1973]; [Thomee2006], Ch. 15 -/
theorem maxNormNeumann (b : Fin n → ℝ) (hs : 0 < s) : Verdict b hs where
  maximumPrinciple := isSubMarkovGenerator b hs
  conservation := neumannLaplacian_apply_one b hs
  stencil _ u p := neumannLaplacian_interp hs u p
  consistency_interior _ _ hu _ hB _ hp := abs_laplacian_sub_interior_le hs hu hB hp
  consistency_boundary _ _ hu _ hB hneu p _ hl := abs_laplacian_sub_boundary_le hs hu hB hneu p hl
  barrier _ p _ hl hK := neumannLaplacian_interp_chi_boundary hs p hl hK
  semidiscrete S N _ ht v := norm_interp_sub_exp_le hs S N ht v
  banach := stableFamily _

/-- **The Neumann verdict is not vacuous**: the first Neumann eigenmode `cosSolution` is a
classical solution on every `[0, T] × Q̄`, nonzero at `t = 0`. -/
theorem maxNormNeumann_nonvacuous (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) :
    Verdict b hs ∧ ∃ S : NeumannSolution b s T, S.u 0 ≠ 0 :=
  ⟨maxNormNeumann b hs, cosSolution b hs T, fun h => by
    have := congrFun h b
    rw [cosSolution_u_zero_corner] at this
    exact one_ne_zero this⟩

end Feec.Models.Cube.MaxNormNeumann
