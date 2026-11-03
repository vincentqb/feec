module

public import Feec.Models.Cube.MaxNormHeat

open Set Finset NormedSpace Feec.Mesh Feec.FiniteElement Feec.TimeStepping MeasureTheory
open Feec.Models.Cube.Geometry (openCube closedCube)

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
   `α⁺ = α⁻` (`Feec.FiniteElement.upCount_eq_downCount`);
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
   principle `IsSubMarkovGenerator.abs_apply_le_of_barrier` (positivity of `e^{tLₕ}` and the
   barrier `κ χ`, `κ = 2 n! h G / s`, `NeumannSolution.exists_barrier`);
6. the verdict of the Banach layer for the family (`StableFamily.Verdict`, `M = 1`);
7. (**backward Euler**, `norm_interp_sub_res_pow_le`) with `|uₜₜ| ≤ Bₜ` on `Q̄`,
   `‖Iₕ u(kτ) - (1 - τLₕ)⁻ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ (3/2 τ Bₜ + n B₄ h² / 12)`
   `+ K_n G h (kτ / s + s)`: `O(τ + h)`, by the same barrier and the discrete comparison
   principle `IsSubMarkovGenerator.abs_apply_le_of_barrier_step` (positivity of `(1 - τLₕ)⁻¹`);
8. (**every A-stable rational scheme**, `norm_interp_sub_step_pow_le`) Brenner–Thomée's stability
   bound `1 + C'_r √k` and, for `r` of order `p`, the semidiscrete error plus
   `C_r kτ τᵖ ‖Lₕ^{p+1} v‖_∞` (`StableFamily.norm_sub_step_pow_le_norm_sub_exp_add`);
9. (**the finite element function on `Q̄`**, `abs_sub_p1Interp_nodal_le`, from
   `MaxNormHeat.abs_sub_p1Interp_le_of_nodes`) `|u(x) - U_h(x)| ≤ ‖Iₕ u - U‖_∞ + n² D₂ h² / 2`
   on every simplex, so 5, 7 and 8 bound the errors in `L^∞(Q)` (the simplices cover `Q̄`,
   `MaxNormHeat.exists_simplex_mem`).

The proved order in `h` is `O(h)`; `O(h²)` is not proved. The boundary consistency is only bounded:
at nodes with two or more coordinates on the boundary the edge weights `Σ_σ α±` are not those of
the reflected interior stencil (the Freudenthal mesh is not reflection symmetric), and the nodal
consistency error does not tend to `0` there (in the plane, at the corner `b`,
`(Lₕ Iₕ u)(b) → (3/4) Δu(b)` for smooth `u` with `∂_ν u = 0`: a hand computation, not
formalized). `cosSolution`
(`e^{-λt} ∏ᵢ cos(π(xᵢ - bᵢ)/s)`) is a nonzero classical solution with `|uₜₜ| ≤ λ²` and
`|∂ᵢ∂ₖ u| ≤ (π/s)²` (`maxNormNeumann_nonvacuous`).

## References

* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
  (the lumped mass method)
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Cube.MaxNormNeumann

open Feec.Models.Cube.MaxNormHeat (meshSize meshSize_pos meshSize_mul meshSize_le
  node_mem_closedCube_iff node_add_mem_closedCube node_add_smul_mem_closedCube
  exists_node_eq_points sineDeriv sineFreq iterate_partialDeriv_sine sineFactors
  sineSolution hasDerivAt_sineMode laplacian_sineMode abs_iterate_partialDeriv_sineMode_le
  abs_partialDeriv_partialDeriv_sineSolution_le sineSolution_hasDerivAt₁ abs_sineSolution_u₂_le
  feDefect abs_sub_p1Interp_le_of_nodes)

variable {n : ℕ} {b : Fin n → ℝ} {s : ℝ} {N : ℕ}

/-! ### The boundary edges: a Kuhn order through each boundary node -/

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
    (hl : p l = 0) : upCount (N + 1) (boundaryPerm N p l) l p = 1 := by
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
    (hl : p l = N + 1) : downCount (N + 1) (boundaryPerm N p l) l p = 1 := by
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
  nodalFun (fun q : Nodes n N => node b (meshSize s N) q) U

theorem nodal_node (hs : 0 < s) (U : Space n N) (q : Nodes n N) :
    nodal b s U (node b (meshSize s N) q) = U q :=
  nodalFun_apply (node_injective_subtype b (meshSize_pos hs N).ne' _) U q

/-- **The lumped-mass `P₁` Laplacian with natural (Neumann) boundary conditions** on the
level-`(N + 1)` Freudenthal mesh of `b + (0, s)ⁿ`: `(Lₕ U)(p) = -a(φₚ, U_h) / m(p)` at every node,
boundary nodes included (`Feec.FiniteElement.lumpedLaplacianOn` on all nodes). -/
def neumannLaplacian (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) : Space n N →L[ℝ] Space n N :=
  lumpedLaplacianOn (freudenthalMesh b s hs (N + 1)) fun q : Nodes n N => node b (meshSize s N) q

theorem neumannLaplacian_apply (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) (p : Nodes n N) :
    neumannLaplacian b hs N U p =
      -p1Stiffness (freudenthalMesh b s hs (N + 1)) (nodalIndicator (node b (meshSize s N) p))
        (nodal b s U) / lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p) :=
  lumpedLaplacianOn_apply _ _ U p

/-- **Conservation**: `Lₕ 𝟙 = 0`, every vertex of the mesh being a node
(`Feec.FiniteElement.lumpedLaplacianOn_apply_one`). -/
theorem neumannLaplacian_apply_one (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    neumannLaplacian b hs N (fun _ => 1) = 0 :=
  lumpedLaplacianOn_apply_one (node_injective_subtype b (meshSize_pos hs N).ne' _) fun T hT j => by
    obtain ⟨q, hq, e⟩ := exists_node_eq_points hs hT j
    exact ⟨⟨q, mem_closedNodes.2 hq⟩, e.symm⟩

/-- **The discrete maximum principle for the Neumann problem**: the Freudenthal meshes are
non-obtuse, so `Lₕ` is a sub-Markov (indeed Markov, `Lₕ 𝟙 = 0`) generator and `e^{tLₕ}` is
positive and contractive in the maximum norm. [CiarletRaviart1973] -/
theorem isSubMarkovGenerator (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    IsSubMarkovGenerator (neumannLaplacian b hs N) :=
  isSubMarkovGenerator_lumpedLaplacianOn (isNonobtuse_freudenthalMesh b hs (N + 1))
    (node_injective_subtype b (meshSize_pos hs N).ne' _)

/-- **The maximum-norm Neumann family**: the lumped-mass Neumann Laplacians of the levels
`N + 1`, a uniformly stable family with `M = 1` (`isSubMarkovGenerator`). -/
abbrev family (b : Fin n → ℝ) (hs : 0 < s) : StableFamily ℝ ℕ :=
  StableFamily.ofSubMarkov (fun N => Nodes n N) (neumannLaplacian b hs) (isSubMarkovGenerator b hs)

@[simp] theorem family_M (b : Fin n → ℝ) (hs : 0 < s) : (family b hs).M = 1 := rfl

@[simp] theorem family_L (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    (family b hs).L N = neumannLaplacian b hs N := rfl

/-! ### The stencil at every node -/

/-- The nodal interpolant `(Iₕ u)(p) = u(b + h p)` at all nodes. -/
def interp (b : Fin n → ℝ) (s : ℝ) (N : ℕ) (u : (Fin n → ℝ) → ℝ) : Space n N :=
  fun p => u (node b (meshSize s N) p)

/-- The stencil sum `Σ_σ Σₗ (α⁺_{σ,l}(p) D⁺ₗw(p) - α⁻_{σ,l}(p) D⁻ₗw(p))`, `D±` the one-sided
second-order difference quotients. -/
def stencilSum (b : Fin n → ℝ) (s : ℝ) (N : ℕ) (w : (Fin n → ℝ) → ℝ) (p : Fin n → ℤ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∑ l, (upCount (N + 1) σ l p * edgeQuot b (meshSize s N) w l p -
    downCount (N + 1) σ l p * edgeQuot b (meshSize s N) w l (p - Pi.single l 1))

/-- **The Neumann stencil at any node**: `(Lₕ Iₕ u)(p) = (n + 1) S_u(p) / C(p)`. -/
theorem neumannLaplacian_interp (hs : 0 < s) (u : (Fin n → ℝ) → ℝ) (p : Nodes n N) :
    neumannLaplacian b hs N (interp b s N u) p =
      (n + 1) * stencilSum b s N u p / vertexCount (N + 1) (p : Fin n → ℤ) := by
  rw [neumannLaplacian_apply, p1Stiffness_congr_right _ _ (w' := u) fun T hT j => ?_]
  · have e : stencilSum b s N u p = -∑ σ : Equiv.Perm (Fin n), ∑ l,
        (downCount (N + 1) σ l p * edgeQuot b (meshSize s N) u l ((p : Fin n → ℤ) - Pi.single l 1) -
          upCount (N + 1) σ l p * edgeQuot b (meshSize s N) u l p) := by
      rw [stencilSum, ← sum_neg_distrib]
      exact sum_congr rfl fun σ _ => by
        rw [← sum_neg_distrib]; exact sum_congr rfl fun l _ => by ring
    rw [e, meshSize, p1Stiffness_nodalIndicator_eq, lumpedMass_node_eq]
    have hh := (freudenthalScale_pos hs (N + 1)).ne'
    rcases eq_or_ne (vertexCount (N + 1) (p : Fin n → ℤ)) 0 with hC | hC
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

/-- The stencil terms of the barrier: `α⁺ (2yₗ/h + 1) - α⁻ (2yₗ/h - 1)`, `yₗ = xₗ - cₗ`. -/
theorem stencilTerm_chi (hs : 0 < s) (σ : Equiv.Perm (Fin n)) (l : Fin n) (p : Fin n → ℤ) :
    upCount (N + 1) σ l p * edgeQuot b (meshSize s N) (chi b s) l p -
        downCount (N + 1) σ l p * edgeQuot b (meshSize s N) (chi b s) l (p - Pi.single l 1) =
      upCount (N + 1) σ l p * (2 * (meshSize s N * p l - s / 2) / meshSize s N + 1) -
        downCount (N + 1) σ l p * (2 * (meshSize s N * p l - s / 2) / meshSize s N - 1) := by
  have hh := (meshSize_pos hs N).ne'
  have d1 : chi b s (node b (meshSize s N) (p + Pi.single l 1)) -
      chi b s (node b (meshSize s N) p) =
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

/-- Every stencil term of the barrier is at most `2`; at a boundary coordinate it is
`α± (1 - s/h) ≤ 0`. -/
theorem stencilTerm_chi_le (hs : 0 < s) (σ : Equiv.Perm (Fin n)) (l : Fin n) {p : Fin n → ℤ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ N + 1) :
    upCount (N + 1) σ l p * edgeQuot b (meshSize s N) (chi b s) l p -
        downCount (N + 1) σ l p * edgeQuot b (meshSize s N) (chi b s) l (p - Pi.single l 1) ≤
      2 - (if σ = boundaryPerm N p l ∧ (p l = 0 ∨ p l = N + 1) then 1 + s / meshSize s N
        else 0) := by
  have hh := meshSize_pos hs N
  have hm := meshSize_mul s N
  push_cast at hm
  have hsh : 1 ≤ s / meshSize s N := by rw [le_div_iff₀ hh, one_mul]; exact meshSize_le hs N
  rw [stencilTerm_chi hs]
  have hu0 := upCount_nonneg (N := N + 1) σ l p
  have hu1 := upCount_le_one (N := N + 1) σ l p
  have hd0 := upCount_nonneg (N := N + 1) σ l (p - Pi.single l 1)
  have hd1 := upCount_le_one (N := N + 1) σ l (p - Pi.single l 1)
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

/-- `L χ = 2n` at the interior nodes (the difference Laplacian is exact on quadratics). -/
theorem neumannLaplacian_interp_chi_interior (hs : 0 < s) {p : Nodes n N}
    (hp : (p : Fin n → ℤ) ∈ interiorNodes n (N + 1)) :
    neumannLaplacian b hs N (interp b s N (chi b s)) p = 2 * n := by
  have hh := (meshSize_pos hs N).ne'
  rw [neumannLaplacian_interp_interior hs _ hp]
  have e : ∀ l, (chi b s (node b (meshSize s N) p + meshSize s N • Pi.single l 1) -
      2 * chi b s (node b (meshSize s N) p) +
      chi b s (node b (meshSize s N) p + (-meshSize s N) • Pi.single l 1)) / meshSize s N ^ 2
      = 2 := fun l => by
    rw [chi_add_single, chi_add_single]
    field_simp
    ring
  simp only [e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The constant `K_n = 2 (1 + 2n · n!)` of the boundary layer. -/
def layerConst (n : ℕ) : ℝ := 2 * (1 + 2 * n * n.factorial)

theorem one_le_vertexCount_of_boundary {p : Fin n → ℤ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ N + 1)
    {l : Fin n} (hl : p l = 0 ∨ p l = N + 1) : 1 ≤ vertexCount (N + 1) p := by
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
  have hC2 := vertexCount_le (N := N + 1) (p : Fin n → ℤ)
  have hfac : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
  have hK' : 2 * (1 + 2 * n * n.factorial) ≤ r := hK
  rw [neumannLaplacian_interp, div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hC2 (by linarith : (0 : ℝ) ≤ r / 2)]

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

/-- Every node lies in the closed cube. -/
theorem node_mem_closedCube (hs : 0 < s) (p : Nodes n N) :
    node b (meshSize s N) p ∈ closedCube b s :=
  (node_mem_closedCube_iff hs).2 (mem_closedNodes.1 p.2)

/-- The stencil terms of a function with `∂_ν u = 0` are bounded by `max |∂ₗ²u|`. -/
theorem abs_stencilTerm_le (hs : 0 < s) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) {B : ℝ}
    (hB : ∀ x ∈ closedCube b s, ∀ i, |partialDeriv i (partialDeriv i u) x| ≤ B)
    (hneu : ∀ x ∈ closedCube b s, ∀ i, x i = b i ∨ x i = b i + s → partialDeriv i u x = 0)
    (σ : Equiv.Perm (Fin n)) (l : Fin n) {p : Fin n → ℤ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ N + 1) :
    |upCount (N + 1) σ l p * edgeQuot b (meshSize s N) u l p -
        downCount (N + 1) σ l p * edgeQuot b (meshSize s N) u l (p - Pi.single l 1)| ≤ B := by
  set h := meshSize s N
  have hh := meshSize_pos hs N
  have hm := meshSize_mul s N
  push_cast at hm
  have hhs := meshSize_le hs N
  set x := node b h p
  have hx : x ∈ closedCube b s := (node_mem_closedCube_iff hs).2 hp
  have hu0 := upCount_nonneg (N := N + 1) σ l p
  have hu1 := upCount_le_one (N := N + 1) σ l p
  have hd0 := upCount_nonneg (N := N + 1) σ l (p - Pi.single l 1)
  have hd1 := upCount_le_one (N := N + 1) σ l (p - Pi.single l 1)
  rw [← downCount] at hd0 hd1
  have hh2 : 0 < h ^ 2 := by positivity
  have hh' : h ≠ 0 := hh.ne'
  simp only [edgeQuot]
  rw [node_add_single_one, node_sub_single_one, sub_add_cancel]
  rcases (hp l).1.eq_or_lt with h0 | h0
  · -- the lower face
    have hl : p l = 0 := h0.symm
    rw [downCount_eq_zero σ hl, zero_mul, sub_zero]
    have hT := abs_axis_taylor_le hu x l h (B := B) fun τ hτ =>
      hB _ (node_add_mem_closedCube hs hp l
      (by rw [Set.uIcc_of_le hh.le] at hτ; simp [hl]; exact hτ.1)
      (by rw [Set.uIcc_of_le hh.le] at hτ; simp [hl]; linarith [hτ.2])) l
    rw [hneu x hx l (Or.inl (by simp [x, node_coord, hl])), mul_zero, sub_zero] at hT
    rw [abs_mul, abs_of_nonneg hu0, div_div, ← sq, abs_div, abs_of_pos hh2]
    calc upCount (N + 1) σ l p * (|u (x + h • Pi.single l 1) - u x| / h ^ 2)
        ≤ 1 * (B * h ^ 2 / 2 / h ^ 2) := mul_le_mul hu1 (div_le_div_of_nonneg_right hT hh2.le)
          (by positivity) zero_le_one
      _ = B / 2 := by field_simp
      _ ≤ B := by
          have : 0 ≤ B := (abs_nonneg _).trans (hB x hx l)
          linarith
  rcases (hp l).2.eq_or_lt with hN | hN
  · -- the upper face
    rw [upCount_eq_zero σ hN, zero_mul, zero_sub, abs_neg]
    have hT := abs_axis_taylor_le hu x l (-h) (B := B) fun τ hτ =>
      hB _ (node_add_mem_closedCube hs hp l
      (by rw [Set.uIcc_of_ge (by linarith)] at hτ; rw [hN]; push_cast; nlinarith [hτ.1])
      (by rw [Set.uIcc_of_ge (by linarith)] at hτ; rw [hN]; push_cast; nlinarith [hτ.2])) l
    rw [hneu x hx l (Or.inr (by simp [x, node_coord, hN]; linarith)), mul_zero, sub_zero] at hT
    rw [abs_mul, abs_of_nonneg hd0, div_div, ← sq, abs_div, abs_of_pos hh2, abs_sub_comm]
    rw [neg_sq] at hT
    calc downCount (N + 1) σ l p * (|u (x + (-h) • Pi.single l 1) - u x| / h ^ 2)
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
    have e : (u (x + h • Pi.single l 1) - u x) / h / h -
        (u x - u (x + (-h) • Pi.single l 1)) / h / h =
        (u (x + h • Pi.single l 1) - 2 * u x + u (x + (-h) • Pi.single l 1)) / h ^ 2 := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos hh2]
    calc _ ≤ 1 * (B * h ^ 2 / h ^ 2) :=
          mul_le_mul hu1 (div_le_div_of_nonneg_right hD hh2.le) (by positivity) zero_le_one
      _ = B := by rw [one_mul, mul_div_assoc, div_self hh2.ne', mul_one]

/-- A node is interior or has a coordinate on a face. -/
theorem interior_or_boundary (p : Nodes n N) :
    (p : Fin n → ℤ) ∈ interiorNodes n (N + 1) ∨
      ∃ l, (p : Fin n → ℤ) l = 0 ∨ (p : Fin n → ℤ) l = N + 1 := by
  have hp := mem_closedNodes.1 p.2
  by_cases h : ∀ j, 0 < (p : Fin n → ℤ) j ∧ (p : Fin n → ℤ) j < (N + 1 : ℕ)
  · exact Or.inl (mem_interiorNodes.2 h)
  · push Not at h
    obtain ⟨l, hl⟩ := h
    refine Or.inr ⟨l, ?_⟩
    have := hp l
    by_cases h1 : 0 < (p : Fin n → ℤ) l
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
  have hx := node_mem_closedCube (b := b) hs p
  have hΔ : |MaxNormHeat.laplacian u (node b (meshSize s N) p)| ≤ n * B := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |partialDeriv i (partialDeriv i u) (node b (meshSize s N) p)|
        ≤ ∑ _i : Fin n, B := sum_le_sum fun i _ => hB _ hx i
      _ = n * B := by simp
  have hS : |stencilSum b s N u p| ≤ n.factorial * n * B := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∑ _l : Fin n, B := sum_le_sum fun σ _ =>
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ =>
            abs_stencilTerm_le hs hu hB hneu σ l hp)
      _ = _ := by simp [Fintype.card_perm]; ring
  have hC := one_le_vertexCount_of_boundary hp hl₀
  have hL : |neumannLaplacian b hs N (interp b s N u) p| ≤ (n + 1).factorial * n * B := by
    rw [neumannLaplacian_interp, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n + 1),
      abs_of_pos (by linarith : (0 : ℝ) < vertexCount (N + 1) (p : Fin n → ℤ))]
    calc (n + 1) * |stencilSum b s N u p| / vertexCount (N + 1) (p : Fin n → ℤ)
        ≤ (n + 1) * |stencilSum b s N u p| := div_le_self (by positivity) hC
      _ ≤ (n + 1) * (n.factorial * n * B) := mul_le_mul_of_nonneg_left hS (by positivity)
      _ = _ := by rw [Nat.factorial_succ]; push_cast; ring
  calc _ ≤ |MaxNormHeat.laplacian u (node b (meshSize s N) p)| +
        |neumannLaplacian b hs N (interp b s N u) p| := abs_sub _ _
    _ ≤ n * B + (n + 1).factorial * n * B := add_le_add hΔ hL
    _ = _ := by ring

/-- **Consistency at the interior nodes is `O(h²)`**: `|Δu(p) - (Lₕ Iₕ u)(p)| ≤ n B h² / 12`
for `u ∈ C⁴` with `|∂ᵢ⁴u| ≤ B` on `Q̄`. -/
theorem abs_laplacian_sub_interior_le (hs : 0 < s) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 4 u)
    {B : ℝ} (hB : ∀ x ∈ closedCube b s, ∀ i, |(partialDeriv i)^[4] u x| ≤ B) {p : Nodes n N}
    (hp : (p : Fin n → ℤ) ∈ interiorNodes n (N + 1)) :
    |MaxNormHeat.laplacian u (node b (meshSize s N) p) -
        neumannLaplacian b hs N (interp b s N u) p| ≤ n * B * meshSize s N ^ 2 / 12 := by
  rw [neumannLaplacian_interp_interior hs u hp, MaxNormHeat.laplacian, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _l : Fin n, B * meshSize s N ^ 2 / 12 := sum_le_sum fun l _ =>
        abs_partialDeriv_sub_secondDiff_le hu (meshSize_pos hs N) _ l fun t ht =>
          hB _ (node_add_smul_mem_closedCube hs hp l ht) l
    _ = _ := by simp; ring

/-! ### The barrier and the errors in the maximum norm at the nodes -/

/-- The interior truncation error `n B₄ h² / 12`. -/
def NeumannSolution.defect {T : ℝ} (S : NeumannSolution b s T) (N : ℕ) : ℝ :=
  n * S.B₄ * meshSize s N ^ 2 / 12

/-- The boundary truncation bound `G = n B₂ (1 + (n + 1)!)`. -/
def NeumannSolution.boundaryDefect {T : ℝ} (S : NeumannSolution b s T) : ℝ :=
  n * S.B₂ * (1 + (n + 1).factorial)

instance (n N : ℕ) : Nonempty (Nodes n N) :=
  ⟨⟨0, mem_closedNodes.2 fun _ => by simp only [Pi.zero_apply]; omega⟩⟩

/-- **The barrier of the boundary layer**: there are `ψ ≥ 0` and `A` with
`|Iₕ uₜ - Lₕ Iₕ u| ≤ A - Lₕ ψ` at every node on `[0, T]` (`O(h²)` in the interior, `O(1)` at the
boundary nodes) and `ψ + t A ≤ t n B₄ h² / 12 + K_n G h (t / s + s)` for `t ≥ 0`: `ψ = κ χ`,
`κ = 2 n! h G / s`, for `s / h ≥ K_n` (`Lₕ χ ≤ -s / (2 h n!)` at the boundary nodes), `ψ = 0`
otherwise. -/
theorem NeumannSolution.exists_barrier {T : ℝ} (S : NeumannSolution b s T) (hs : 0 < s)
    (hT : 0 ≤ T) (N : ℕ) :
    ∃ ψ : Space n N, ∃ A : ℝ, 0 ≤ ψ ∧
      (∀ r ∈ Icc 0 T, ∀ p, |(interp b s N (S.u₁ r) -
        neumannLaplacian b hs N (interp b s N (S.u r))) p| ≤ A - neumannLaplacian b hs N ψ p) ∧
      ∀ t, 0 ≤ t → ∀ p, ψ p + t * A ≤
        t * S.defect N + layerConst n * S.boundaryDefect * meshSize s N * (t / s + s) := by
  set L := neumannLaplacian b hs N
  set h := meshSize s N
  have hh : 0 < h := meshSize_pos hs N
  have hh' : h ≠ 0 := hh.ne'
  set D := S.defect N
  set G := S.boundaryDefect
  have hb : b ∈ closedCube b s := fun i _ => ⟨le_rfl, by linarith⟩
  obtain ⟨hD0, hG0⟩ : 0 ≤ D ∧ 0 ≤ G := by
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨l⟩⟩
    · obtain rfl : n = 0 := by rw [← Fintype.card_fin n]; exact Fintype.card_eq_zero_iff.2 hn
      simp [D, G, NeumannSolution.defect, NeumannSolution.boundaryDefect]
    · have := (abs_nonneg _).trans (S.bound₄ 0 ⟨le_rfl, hT⟩ b hb l)
      have := (abs_nonneg _).trans (S.bound₂ 0 ⟨le_rfl, hT⟩ b hb l)
      simp only [D, G, NeumannSolution.defect, NeumannSolution.boundaryDefect]
      constructor <;> positivity
  have hdef : ∀ r ∈ Icc 0 T, ∀ p : Nodes n N,
      ((p : Fin n → ℤ) ∈ interiorNodes n (N + 1) →
        |(interp b s N (S.u₁ r) - L (interp b s N (S.u r))) p| ≤ D) ∧
      (∀ l, (p : Fin n → ℤ) l = 0 ∨ (p : Fin n → ℤ) l = N + 1 →
        |(interp b s N (S.u₁ r) - L (interp b s N (S.u r))) p| ≤ G) := fun r hr p => by
    rw [Pi.sub_apply, show interp b s N (S.u₁ r) p = S.u₁ r (node b h p) from rfl,
      S.heat r hr _ (node_mem_closedCube hs p)]
    exact ⟨fun hp => abs_laplacian_sub_interior_le hs (S.contDiff r hr) (S.bound₄ r hr) hp,
      fun l hl => abs_laplacian_sub_boundary_le hs ((S.contDiff r hr).of_le (by norm_num))
        (S.bound₂ r hr) (S.neumann r hr) p hl⟩
  have hK0 : 0 < layerConst n := by unfold layerConst; positivity
  by_cases hK : layerConst n ≤ s / h
  · set κ := 2 * n.factorial * h * G / s
    have hκ : 0 ≤ κ := by positivity
    refine ⟨κ • interp b s N (chi b s), D + 2 * n * κ, fun q => mul_nonneg hκ (chi_nonneg b s _),
      fun r hr q => ?_, fun t ht p => ?_⟩
    · have hLψ : L (κ • interp b s N (chi b s)) q = κ * L (interp b s N (chi b s)) q := by
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
        linarith [(hdef r hr q).2 l hl]
    · have hχ : (κ • interp b s N (chi b s)) p ≤ κ * (n * s ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left (chi_le b (node_mem_closedCube hs p)) hκ
      have hfac : (0 : ℝ) ≤ n.factorial := by positivity
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
        exact mul_le_mul_of_nonneg_right hn2 (mul_nonneg hGh (div_nonneg ht hs.le))
      nlinarith
  · -- large mesh sizes: no barrier
    refine ⟨0, D + G, le_rfl, fun r hr q => ?_, fun t ht p => ?_⟩
    · simp only [map_zero, Pi.zero_apply, sub_zero]
      rcases interior_or_boundary q with hq | ⟨l, hl⟩
      · linarith [(hdef r hr q).1 hq]
      · linarith [(hdef r hr q).2 l hl]
    · have hKh : s ≤ layerConst n * h := by
        rw [not_le, div_lt_iff₀ hh] at hK; linarith
      have : t * G ≤ layerConst n * G * h * (t / s) := by
        rw [mul_div_assoc', le_div_iff₀ hs]
        nlinarith [mul_nonneg ht hG0]
      have : 0 ≤ layerConst n * G * h * s := by positivity
      simp only [Pi.zero_apply, zero_add]
      nlinarith

/-- **The semidiscrete error of the Neumann problem in the maximum norm at the nodes**: for every
classical solution and `t ∈ [0, T]`,
`‖Iₕ u(t) - e^{tLₕ} v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + t n B₄ h² / 12 + K_n G h (t / s + s)`:
`O(h)` uniformly in the mesh, from `O(h²)` consistency at the interior nodes and `O(1)`
consistency at the boundary nodes, through the barrier `χ = |x - c|²` (`Lₕ χ ≤ -s / (2 h n!)` at
the boundary nodes, `NeumannSolution.exists_barrier`) and the maximum principle. -/
theorem norm_interp_sub_exp_le (hs : 0 < s) {T : ℝ} (S : NeumannSolution b s T) (N : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 T) (v : Space n N) :
    ‖interp b s N (S.u t) - exp (t • neumannLaplacian b hs N) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + t * S.defect N +
        layerConst n * S.boundaryDefect * meshSize s N * (t / s + s) := by
  set L := neumannLaplacian b hs N
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  obtain ⟨ψ, A, hψ, hd, hb⟩ := S.exists_barrier hs (ht.1.trans ht.2) N
  set E : ℝ → Space n N := fun r => interp b s N (S.u r) - exp (r • L) v
  have hE : ∀ r ∈ Icc 0 t, HasDerivAt E (interp b s N (S.u₁ r) - L (exp (r • L) v)) r :=
    fun r hr => (hasDerivAt_pi.2 fun p => S.hasDerivAt r (hsub hr) _ (node_mem_closedCube hs p)).sub
      (ContinuousLinearMap.hasDerivAt_exp_ofReal_smul_apply L v r)
  refine (pi_norm_le_iff_of_nonempty _).2 fun p => ?_
  have hbar := (isSubMarkovGenerator b hs N).abs_apply_le_of_barrier
    (neumannLaplacian_apply_one b hs N) ht.1 hE hψ (fun r hr q => by
      have e : interp b s N (S.u₁ r) - L (exp (r • L) v) - L (E r) =
          interp b s N (S.u₁ r) - L (interp b s N (S.u r)) := by simp only [E, map_sub]; abel
      rw [e]; exact hd r (hsub hr) q) p
  have e0 : E 0 = interp b s N (S.u 0) - v := by simp [E]
  rw [e0] at hbar
  rw [Real.norm_eq_abs]
  linarith [hb t ht.1 p]

/-- **Backward Euler for the Neumann problem in the maximum norm at the nodes**: if moreover
`uₜ` has time derivative `u₂` with `|u₂| ≤ Bₜ` on `Q̄`, then for `kτ ≤ T`
`‖Iₕ u(kτ) - (1 - τLₕ)⁻ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ (3/2 τ Bₜ + n B₄ h² / 12)`
`+ K_n G h (kτ / s + s)`: `O(τ + h)`, unconditionally, by the same barrier and the discrete
comparison principle (`IsSubMarkovGenerator.abs_apply_le_of_barrier_step`). -/
theorem norm_interp_sub_res_pow_le (hs : 0 < s) {T : ℝ} (S : NeumannSolution b s T)
    {u₂ : ℝ → (Fin n → ℝ) → ℝ} {Bₜ : ℝ}
    (hu₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, HasDerivAt (fun t => S.u₁ t x) (u₂ t x) t)
    (hBₜ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, |u₂ t x| ≤ Bₜ) (N : ℕ) {τ : ℝ} (hτ : 0 < τ)
    {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) :
    ‖interp b s N (S.u (k * τ)) - ((family b hs).res τ N ^ k) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * (3 / 2 * τ * Bₜ + S.defect N) +
        layerConst n * S.boundaryDefect * meshSize s N * (k * τ / s + s) := by
  set L := neumannLaplacian b hs N
  set R := (family b hs).res τ N
  set W : ℝ → Space n N := fun r => interp b s N (S.u r)
  set W₁ : ℝ → Space n N := fun r => interp b s N (S.u₁ r)
  obtain ⟨ψ, A, hψ, hd, hb⟩ := S.exists_barrier hs ((by positivity : (0 : ℝ) ≤ k * τ).trans hk) N
  set E : ℕ → Space n N := fun j => W (j * τ) - (R ^ j) v
  set δ : ℕ → Space n N := fun j =>
    τ⁻¹ • (W ((j + 1 : ℕ) * τ) - W (j * τ) - τ • W₁ ((j + 1 : ℕ) * τ)) +
      (W₁ ((j + 1 : ℕ) * τ) - L (W ((j + 1 : ℕ) * τ)))
  have hE : ∀ j < k, E (j + 1) - τ • L (E (j + 1)) = E j + τ • δ j := fun j _ => by
    have hR : R ((R ^ j) v) - τ • L (R ((R ^ j) v)) = (R ^ j) v := by
      simpa using (family b hs).res_sub_smul_apply_res hτ N ((R ^ j) v)
    have e : E (j + 1) - τ • L (E (j + 1)) = (W ((j + 1 : ℕ) * τ) -
        τ • L (W ((j + 1 : ℕ) * τ))) - (R ((R ^ j) v) - τ • L (R ((R ^ j) v))) := by
      have hp : (R ^ (j + 1)) v = R ((R ^ j) v) := by rw [pow_succ']; rfl
      simp only [E, hp, map_sub, smul_sub]; abel
    rw [e, hR]
    simp only [E, δ, smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul,
      mul_inv_cancel_left₀ hτ.ne']
    abel
  have hδ : ∀ j < k, ∀ p, |δ j p| ≤ A + 3 / 2 * τ * Bₜ - L ψ p := fun j hj p => by
    have hj' : ((j + 1 : ℕ) : ℝ) * τ ≤ k * τ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hτ.le
    have e : ((j + 1 : ℕ) : ℝ) * τ = j * τ + τ := by push_cast; ring
    have hI : Icc ((j : ℝ) * τ) (j * τ + τ) ⊆ Icc 0 T :=
      Icc_subset_Icc (by positivity) (by linarith)
    have hq := norm_sub_sub_smul_le hτ.le (f := W) (f₁ := W₁)
      (f₂ := fun r => interp b s N (u₂ r)) (a := j * τ) (B := Bₜ)
      (fun r hr => hasDerivAt_pi.2 fun q => S.hasDerivAt r (hI hr) _ (node_mem_closedCube hs q))
      (fun r hr => hasDerivAt_pi.2 fun q => hu₂ r (hI hr) _ (node_mem_closedCube hs q))
      (fun r hr => (pi_norm_le_iff_of_nonempty _).2 fun q => by
        rw [Real.norm_eq_abs]; exact hBₜ r (hI hr) _ (node_mem_closedCube hs q))
    rw [← e] at hq
    have h1 : |(τ⁻¹ • (W ((j + 1 : ℕ) * τ) - W (j * τ) - τ • W₁ ((j + 1 : ℕ) * τ))) p| ≤
        3 / 2 * τ * Bₜ := by
      rw [← Real.norm_eq_abs]
      refine (norm_le_pi_norm _ p).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hτ.le)]
      calc τ⁻¹ * ‖W ((j + 1 : ℕ) * τ) - W (j * τ) - τ • W₁ ((j + 1 : ℕ) * τ)‖
          ≤ τ⁻¹ * (3 / 2 * τ ^ 2 * Bₜ) := by gcongr
        _ = 3 / 2 * τ * Bₜ := by field_simp
    have h2 := hd _ ⟨by positivity, hj'.trans hk⟩ p
    exact (abs_add_le _ _).trans (by linarith)
  refine (pi_norm_le_iff_of_nonempty _).2 fun p => ?_
  have hbar := (isSubMarkovGenerator b hs N).abs_apply_le_of_barrier_step
    (neumannLaplacian_apply_one b hs N) hτ.le hE hψ hδ p
  have e0 : E 0 = W 0 - v := by simp [E]
  rw [e0] at hbar
  rw [Real.norm_eq_abs]
  have := hb (k * τ) (by positivity) p
  show |E k p| ≤ _
  linarith

/-- **Every A-stable rational scheme for the Neumann problem in the maximum norm at the nodes**:
for `r` of order `p` (Crank–Nicolson, the Gauss and Radau methods), the semidiscrete error plus
Brenner–Thomée's smooth-data term `C_r kτ τᵖ ‖Lₕ^{p+1} v‖_∞`. -/
theorem norm_interp_sub_step_pow_le (hs : 0 < s) {T : ℝ} (S : NeumannSolution b s T)
    {r : RationalScheme} (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) (N : ℕ) {τ : ℝ}
    (hτ : 0 < τ) {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) :
    ‖interp b s N (S.u (k * τ)) - ((family b hs).step r τ N ^ k) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * S.defect N +
        layerConst n * S.boundaryDefect * meshSize s N * (k * τ / s + s) +
        r.sharpConst p * (k * τ) * τ ^ p * ‖(neumannLaplacian b hs N ^ (p + 1)) v‖ := by
  have := (family b hs).norm_sub_step_pow_le_norm_sub_exp_add hr hp hτ N
    (interp b s N (S.u (k * τ))) k v
  simp only [mul_one, RCLike.ofReal_real_eq_id, id_eq] at this
  linarith [norm_interp_sub_exp_le hs S N ⟨by positivity, hk⟩ v]

/-- **The finite element function in the maximum norm on `Q̄`** (Neumann): for `u ∈ C²` with
`|∂ᵢ∂ₖ u| ≤ D` on `Q̄` and nodal values `U`, at every point `x` of every simplex `K` of the mesh,
`|u(x) - U_h(x)| ≤ ‖Iₕ u - U‖_∞ + n² D h² / 2` (`MaxNormHeat.abs_sub_p1Interp_le_of_nodes`). -/
theorem abs_sub_p1Interp_nodal_le (hs : 0 < s) (N : ℕ) {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 2 u) {D : ℝ}
    (hD : ∀ x ∈ closedCube b s, ∀ i k, |partialDeriv k (partialDeriv i u) x| ≤ D) (U : Space n N)
    {K : Affine.Simplex ℝ (Fin n → ℝ) n} (hK : K ∈ (freudenthalMesh b s hs (N + 1)).simplices)
    {x : Fin n → ℝ} (hx : x ∈ K.closedInterior) :
    |u x - p1Interp K.points (nodal b s U) x| ≤
      ‖interp b s N u - U‖ + feDefect (s := s) (n := n) D N :=
  abs_sub_p1Interp_le_of_nodes hs N hu hD (fun q hq => by
    rw [show nodal b s U (node b (meshSize s N) q) = U ⟨q, mem_closedNodes.2 hq⟩ from
      nodal_node hs U ⟨q, mem_closedNodes.2 hq⟩, ← Real.norm_eq_abs]
    exact norm_le_pi_norm (interp b s N u - U) ⟨q, mem_closedNodes.2 hq⟩) hK hx

/-! ### A classical solution: the first Neumann eigenmode -/

/-- The shifted centre `b - s/2`: `sin(a(y - (bᵢ - s/2))) = cos(a(y - bᵢ))`, `a = π/s`. -/
def cosCentre (b : Fin n → ℝ) (s : ℝ) : Fin n → ℝ := b - (s / 2) • fun _ => 1

/-- **The first Neumann eigenmode** `u(t, x) = e^{-λt} ∏ᵢ cos(π(xᵢ - bᵢ)/s)`, `λ = n π²/s²`
(written `∏ᵢ sin(π(xᵢ - bᵢ + s/2)/s)`): a classical solution of the Neumann problem on every
`[0, T] × Q̄` with `B₂ = (π/s)²`, `B₄ = (π/s)⁴`. -/
def cosSolution (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) : NeumannSolution b s T where
  u := (sineSolution (cosCentre b s) hs T).u
  u₁ := (sineSolution (cosCentre b s) hs T).u₁
  contDiff := (sineSolution (cosCentre b s) hs T).contDiff
  hasDerivAt t _ x _ := hasDerivAt_sineMode (cosCentre b s) t x
  heat t _ x _ := (laplacian_sineMode (cosCentre b s) t x).symm
  neumann t _ x _ i hi := by
    show partialDeriv i (fun x : Fin n → ℝ => Real.exp (-(n * sineFreq s ^ 2) * t) *
      ∏ j, sineDeriv (sineFreq s) (cosCentre b s j) 0 (x j)) x = 0
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
  bound₂ t ht x _ i := abs_partialDeriv_partialDeriv_sineSolution_le (cosCentre b s) hs T ht.1 x i i
  B₄ := sineFreq s ^ 4
  bound₄ t ht x _ i := abs_iterate_partialDeriv_sineMode_le (cosCentre b s) ht.1 x i

/-- The first Neumann eigenmode is `1` at the corner `b` at `t = 0`. -/
theorem cosSolution_u_zero_corner (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) :
    (cosSolution b hs T).u 0 b = 1 := by
  simp only [cosSolution, sineSolution, sineDeriv, sineFreq, cosCentre, mul_zero, Real.exp_zero,
    one_mul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [show Real.pi / s * (b j - (b j - s / 2)) = Real.pi / 2 by field_simp; ring,
    Real.sin_pi_div_two]

/-! ### The verdict -/

/-- The conclusions of `maxNormNeumann` for the cube `b + (0, s)ⁿ`. -/
structure Verdict (b : Fin n → ℝ) (hs : 0 < s) : Prop where
  /-- the discrete maximum principle: `e^{tLₕ}` is positive and contractive in the maximum norm -/
  maximumPrinciple (N : ℕ) : IsSubMarkovGenerator (neumannLaplacian b hs N)
  /-- conservation: `Lₕ 𝟙 = 0` -/
  conservation (N : ℕ) : neumannLaplacian b hs N (fun _ => 1) = 0
  /-- the stencil at every node, `(Lₕ Iₕ u)(p) = (n + 1) S_u(p) / C(p)` -/
  stencil (N : ℕ) (u : (Fin n → ℝ) → ℝ) (p : Nodes n N) :
    neumannLaplacian b hs N (interp b s N u) p =
      (n + 1) * stencilSum b s N u p / vertexCount (N + 1) (p : Fin n → ℤ)
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
  /-- backward Euler, `O(τ + h)` in the maximum norm at the nodes -/
  backwardEuler {T : ℝ} (S : NeumannSolution b s T) {u₂ : ℝ → (Fin n → ℝ) → ℝ} {Bₜ : ℝ}
    (hu₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, HasDerivAt (fun t => S.u₁ t x) (u₂ t x) t)
    (hBₜ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, |u₂ t x| ≤ Bₜ) (N : ℕ) {τ : ℝ} (hτ : 0 < τ)
    {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) :
    ‖interp b s N (S.u (k * τ)) - ((family b hs).res τ N ^ k) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * (3 / 2 * τ * Bₜ + S.defect N) +
        layerConst n * S.boundaryDefect * meshSize s N * (k * τ / s + s)
  /-- Brenner–Thomée's stability bound for every A-stable rational scheme -/
  stable_rational {r : RationalScheme} (hr : r.IsAStable) (N : ℕ) {τ : ℝ} (hτ : 0 < τ) (k : ℕ) :
    ‖(family b hs).step r τ N ^ k‖ ≤ 1 + r.sqrtConst * √k
  /-- every A-stable rational scheme of order `p` against every classical solution -/
  rational {T : ℝ} (S : NeumannSolution b s T) {r : RationalScheme} (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) (N : ℕ) {τ : ℝ} (hτ : 0 < τ) {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) :
    ‖interp b s N (S.u (k * τ)) - ((family b hs).step r τ N ^ k) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * S.defect N +
        layerConst n * S.boundaryDefect * meshSize s N * (k * τ / s + s) +
        r.sharpConst p * (k * τ) * τ ^ p * ‖(neumannLaplacian b hs N ^ (p + 1)) v‖
  /-- the semidiscrete error of the finite element function at every point of `Q̄` -/
  semidiscrete_fe {T : ℝ} (S : NeumannSolution b s T) {D₂ : ℝ}
    (hD₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, ∀ i k,
      |partialDeriv k (partialDeriv i (S.u t)) x| ≤ D₂) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (v : Space n N) {K : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hK : K ∈ (freudenthalMesh b s hs (N + 1)).simplices) {x : Fin n → ℝ}
    (hx : x ∈ K.closedInterior) :
    |S.u t x - p1Interp K.points (nodal b s (exp (t • neumannLaplacian b hs N) v)) x| ≤
      ‖interp b s N (S.u 0) - v‖ + t * S.defect N +
        layerConst n * S.boundaryDefect * meshSize s N * (t / s + s) +
        feDefect (s := s) (n := n) D₂ N
  /-- backward Euler: the error of the finite element function at every point of `Q̄` -/
  backwardEuler_fe {T : ℝ} (S : NeumannSolution b s T) {D₂ : ℝ}
    (hD₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, ∀ i k,
      |partialDeriv k (partialDeriv i (S.u t)) x| ≤ D₂)
    {u₂ : ℝ → (Fin n → ℝ) → ℝ} {Bₜ : ℝ}
    (hu₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, HasDerivAt (fun t => S.u₁ t x) (u₂ t x) t)
    (hBₜ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, |u₂ t x| ≤ Bₜ) (N : ℕ) {τ : ℝ} (hτ : 0 < τ)
    {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) {K : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hK : K ∈ (freudenthalMesh b s hs (N + 1)).simplices) {x : Fin n → ℝ}
    (hx : x ∈ K.closedInterior) :
    |S.u (k * τ) x - p1Interp K.points (nodal b s (((family b hs).res τ N ^ k) v)) x| ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * (3 / 2 * τ * Bₜ + S.defect N) +
        layerConst n * S.boundaryDefect * meshSize s N * (k * τ / s + s) +
        feDefect (s := s) (n := n) D₂ N
  /-- every A-stable rational scheme: the error of the finite element function on `Q̄` -/
  rational_fe {T : ℝ} (S : NeumannSolution b s T) {D₂ : ℝ}
    (hD₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, ∀ i k,
      |partialDeriv k (partialDeriv i (S.u t)) x| ≤ D₂)
    {r : RationalScheme} (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) (N : ℕ) {τ : ℝ}
    (hτ : 0 < τ) {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) {K : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hK : K ∈ (freudenthalMesh b s hs (N + 1)).simplices) {x : Fin n → ℝ}
    (hx : x ∈ K.closedInterior) :
    |S.u (k * τ) x - p1Interp K.points (nodal b s (((family b hs).step r τ N ^ k) v)) x| ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * S.defect N +
        layerConst n * S.boundaryDefect * meshSize s N * (k * τ / s + s) +
        r.sharpConst p * (k * τ) * τ ^ p * ‖(neumannLaplacian b hs N ^ (p + 1)) v‖ +
        feDefect (s := s) (n := n) D₂ N

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
  backwardEuler S _ _ hu₂ hBₜ N _ hτ _ hk v := norm_interp_sub_res_pow_le hs S hu₂ hBₜ N hτ hk v
  stable_rational hr N _ hτ k := by simpa using (family b hs).norm_step_pow_le hr hτ N k
  rational S _ hr _ hp N _ hτ _ hk v := norm_interp_sub_step_pow_le hs S hr hp N hτ hk v
  semidiscrete_fe S _ hD₂ N _ ht v _ hK _ hx :=
    (abs_sub_p1Interp_nodal_le hs N ((S.contDiff _ ht).of_le (by norm_num)) (hD₂ _ ht) _ hK
      hx).trans (add_le_add (norm_interp_sub_exp_le hs S N ht v) le_rfl)
  backwardEuler_fe S _ hD₂ _ _ hu₂ hBₜ N τ hτ k hk v _ hK _ hx :=
    have hkt : (k : ℝ) * τ ∈ Set.Icc 0 _ := ⟨by positivity, hk⟩
    (abs_sub_p1Interp_nodal_le hs N ((S.contDiff _ hkt).of_le (by norm_num)) (hD₂ _ hkt) _ hK
      hx).trans (add_le_add (norm_interp_sub_res_pow_le hs S hu₂ hBₜ N hτ hk v) le_rfl)
  rational_fe S _ hD₂ _ hr _ hp N τ hτ k hk v _ hK _ hx :=
    have hkt : (k : ℝ) * τ ∈ Set.Icc 0 _ := ⟨by positivity, hk⟩
    (abs_sub_p1Interp_nodal_le hs N ((S.contDiff _ hkt).of_le (by norm_num)) (hD₂ _ hkt) _ hK
      hx).trans (add_le_add (norm_interp_sub_step_pow_le hs S hr hp N hτ hk v) le_rfl)

/-- **The Neumann verdict is not vacuous**: the first Neumann eigenmode `cosSolution` is a
classical solution on every `[0, T] × Q̄`, nonzero at `t = 0`, with `uₜₜ = λ² u`, `|uₜₜ| ≤ λ²`
and `|∂ᵢ∂ₖ u| ≤ (π/s)²`; so the backward Euler and finite element clauses apply to it. -/
theorem maxNormNeumann_nonvacuous (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) :
    Verdict b hs ∧ ∃ S : NeumannSolution b s T, S.u 0 ≠ 0 ∧
      (∃ (u₂ : ℝ → (Fin n → ℝ) → ℝ) (Bₜ : ℝ),
        (∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, HasDerivAt (fun t => S.u₁ t x) (u₂ t x) t) ∧
        ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, |u₂ t x| ≤ Bₜ) ∧
      ∃ D₂ : ℝ, ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, ∀ i k,
        |partialDeriv k (partialDeriv i (S.u t)) x| ≤ D₂ :=
  ⟨maxNormNeumann b hs, cosSolution b hs T, fun h => by
    have := congrFun h b
    rw [cosSolution_u_zero_corner] at this
    exact one_ne_zero this,
    ⟨fun t x => (n * sineFreq s ^ 2) ^ 2 * (cosSolution b hs T).u t x, (n * sineFreq s ^ 2) ^ 2,
      fun t _ x _ => sineSolution_hasDerivAt₁ (cosCentre b s) hs T t x,
      fun t ht x _ => abs_sineSolution_u₂_le (cosCentre b s) hs T ht.1 x⟩,
    sineFreq s ^ 2, fun t ht x _ i k =>
      abs_partialDeriv_partialDeriv_sineSolution_le (cosCentre b s) hs T ht.1 x i k⟩

end Feec.Models.Cube.MaxNormNeumann
