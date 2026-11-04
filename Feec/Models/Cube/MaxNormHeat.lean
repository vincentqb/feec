module

public import Feec.FiniteElement.MaxNormHeat
public import Feec.ForMathlib.Analysis.FiniteDifference
public import Feec.ForMathlib.Calculus.Partial
public import Feec.ForMathlib.Calculus.SecondDifference
public import Feec.Models.Cube.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The heat equation in the maximum norm: lumped-mass `P₁` elements on Freudenthal meshes

The heat equation `uₜ = Δu` on the cube `Q = b + (0, s)ⁿ` with homogeneous Dirichlet data,
discretized in space by lumped-mass `P₁` finite elements on the Freudenthal meshes of level
`N + 1` (mesh size `h = s / (N + 1)`, `Feec.Mesh.freudenthalMesh`), is a **uniformly stable
family in the maximum norm at the nodes** (`MaxNormHeat.family`, `M = 1`). `Lₕ` is the
symmetric negative definite difference Laplacian, so `e^{tLₕ}` is also a contraction in `ℓ²`;
the direct Hilbert route reaches the maximum norm through the norm equivalence, with a factor
`h^{-n/2}`. The Banach layer (`Feec.TimeStepping.stableFamily`, the discrete half of
`Feec.TimeStepping.banachFEEC`) gives the maximum-norm theory with constants independent of `h`.

The scheme is the lumped-mass Galerkin method on the space `P̊₁⁻Λ⁰` of conforming `P₁` (Whitney
`0`-form) functions of `Feec.FiniteElement.WhitneyComplex` with vanishing boundary DOFs: the
global `P₁` functions `U_h` with values `U` at the interior nodes (`feFun`) are exactly
`P̊₁⁻Λ⁰` (`feEquiv`, a linear isomorphism, since the interior nodes are the mesh vertices off
`∂Q`), and `W = Lₕ U` iff `(W, V)_h = -⟪d U_h, d V_h⟫_{L²Λ¹(Q)}` for all `V`
(`lumpedLaplacian_eq_iff`; for all test functions `V_h ∈ P̊₁⁻Λ⁰`,
`lumpedLaplacian_eq_iff_globalSpace₀`), with the vertex quadrature `(U, V)_h = Σ m(p) U(p) V(p)`,
`m(p) = ∫_Q φₚ` (`Feec.FiniteElement.P1Global`). With the stencil theorem it is exactly the
classical finite difference scheme for the heat equation: `Feec.Models.Cube.FiniteDifferenceHeat`
states the finite difference Laplacian `FiniteDifference.laplacian` on its own, proves it equal to
`Lₕ` (`FiniteDifferenceHeat.fdLaplacian_eq`), and reads the results below for it.

The discrete space is `ℝ^{interior nodes}` with the maximum norm (`MaxNormHeat.Space N`). The
discrete Laplacian `Lₕ = -M_L⁻¹ K` (`MaxNormHeat.lumpedLaplacian`) is defined from the `P₁`
stiffness form and the lumped mass of the mesh (`Feec.FiniteElement.p1Stiffness`,
`Feec.FiniteElement.lumpedMass`), the nodal values extended by `0` to the boundary nodes. The
meshes with their interior nodes are a family of non-obtuse meshes (`MaxNormHeat.meshes`), and the
error estimates 4–6 below are the general ones of `Feec.FiniteElement.NonobtuseMeshes.maxNormHeat`
with the nodal consistency error `n B₄ h² / 12` of 3: what is specific to the cube is the uniform
stencil, hence the `O(h²)` consistency.

## Main results

**`MaxNormHeat.maxNormHeat`** (statement `MaxNormHeat.Verdict`):

1. (**the stencil**, `lumpedLaplacian_apply`) the Freudenthal simplices are non-obtuse
   (`Feec.FiniteElement.isNonobtuse_freudenthalMesh`), so the stiffness matrix has nonpositive
   off-diagonal entries (Ciarlet–Raviart), and `Lₕ` is the
   `(2n + 1)`-point difference Laplacian
   `(Lₕ U)(p) = Σₗ (U(p + eₗ) - 2 U(p) + U(p - eₗ)) / h²` (`U = 0` at the boundary nodes);
2. (**the discrete maximum principle**, `isSubMarkovGenerator`) `Lₕ` is a sub-Markov generator:
   `e^{tLₕ}` is positive and contractive in the maximum norm, `-a ≤ v ≤ a ⇒ -a ≤ e^{tLₕ} v ≤ a`;
3. (**consistency**, `norm_interp_laplacian_sub_le`) for `u ∈ C⁴` vanishing on `∂Q` with
   `|∂ᵢ⁴ u| ≤ B` on `Q̄`, `‖Iₕ Δu - Lₕ Iₕ u‖_∞ ≤ n B h² / 12` (`Iₕ` the nodal interpolant);
4. (**semidiscrete error**) for every classical solution `u` on `[0, T]` (`HeatSolution`:
   `C⁴` on all of `ℝⁿ` at each time with `|∂ᵢ⁴ u| ≤ B₄` on `Q̄`, `uₜ = Δu`, `u = 0` on `∂Q`),
   `‖Iₕ u(t) - e^{tLₕ} v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + t n B₄ h² / 12`;
5. (**backward Euler**) with `|uₜₜ| ≤ B₂`,
   `‖Iₕ u(kτ) - (1 - τLₕ)⁻ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ (3/2 τ B₂ + n B₄ h² / 12)`:
   `O(τ + h²)` in the maximum norm, unconditionally;
6. (**every A-stable rational scheme**, Crank–Nicolson and the Gauss and Radau methods among
   them) Brenner–Thomée's stability bound `‖r(τLₕ)ᵏ‖_∞ ≤ 1 + C'_r √k`, and for `r` of order `p`
   `‖Iₕ u(kτ) - r(τLₕ)ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ n B₄ h² / 12 + C_r kτ τᵖ ‖Lₕ^{p+1} v‖_∞`
   (the sharp smooth-data estimate; the factor `‖Lₕ^{p+1} v‖_∞` is that of the discrete datum);
7. the full verdict of the Banach layer for the family (`StableFamily.Verdict`);
8. (**the Galerkin form**) `m(x) = ⟪φₓ, 1⟫_{L²(Q)}` and `W = Lₕ U ⟺ (W, V)_h = -⟪d U_h, d V_h⟫`,
   with `U ↦ U_h` a bijection onto `P̊₁⁻Λ⁰` (`feFun_bijective`), so the test functions `V_h`
   range over all of `P̊₁⁻Λ⁰`;
9. (**the finite element function on `Q̄`**, `abs_sub_p1Interp_nodal_le`) a `P₁` function attains
   its extreme values at the vertices (`Feec.FiniteElement.abs_p1Interp_le`) and the `P₁`
   interpolation error is `≤ n² D₂ h² / 2` for `|∂ᵢ∂ₖ u| ≤ D₂`
   (`Feec.FiniteElement.abs_sub_p1Interp_le`), so at every point `x` of every simplex `K`
   (the simplices cover `Q̄`, `exists_simplex_mem`),
   `|u(x) - U_h(x)| ≤ ‖Iₕ u - U‖_∞ + n² D₂ h² / 2`; with 4–6 this bounds the semidiscrete,
   backward Euler and rational errors in `L^∞(Q)` (`semidiscrete_fe`, `backwardEuler_fe`,
   `rational_fe`).

Among the fully discrete results only 5 is uniform in `h` with the constants of `u` alone; in 6
the factor `‖Lₕ^{p+1} v‖_∞` is not bounded uniformly in `h`, and the uniform route through the
stability bound loses `√k` (no `‖r(τLₕ)ᵏ‖_∞ ≤ C` uniform in `k` and `h` is proved). The
estimates 4–6 are in the maximum norm at the nodes, 9 in `L^∞(Q)` of the finite element function.
`sineSolution` is a nonzero classical solution (`exp(-λt) ∏ᵢ sin(π(xᵢ - bᵢ)/s)`, with
`|∂ᵢ∂ₖ u| ≤ (π/s)²`), so the hypotheses of 4–6 and 9 are satisfied (`maxNormHeat_nonvacuous`).

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
  (the lumped mass method, the maximum principle and maximum-norm estimates)
* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set Finset NormedSpace Feec.Mesh Feec.FiniteElement Feec.TimeStepping
open scoped InnerProductSpace
open Feec.Models.Cube.Geometry (openCube closedCube)
open FiniteDifference (zeroExt zeroExt_sub abs_zeroExt_le)

@[expose] public noncomputable section

namespace Feec.Models.Cube.MaxNormHeat

variable {n : ℕ} {b : Fin n → ℝ} {s : ℝ}

/-! ### The discrete Laplacian -/

/-- The mesh size `h = s / (N + 1)` of the level-`(N + 1)` Freudenthal mesh. -/
def meshSize (s : ℝ) (N : ℕ) : ℝ := s / (N + 1 : ℕ)

theorem meshSize_pos (hs : 0 < s) (N : ℕ) : 0 < meshSize s N := freudenthalScale_pos hs (N + 1)

theorem meshSize_mul (s : ℝ) (N : ℕ) : meshSize s N * (N + 1 : ℕ) = s := by
  rw [meshSize, div_mul_cancel₀]; positivity

theorem meshSize_le (hs : 0 < s) (N : ℕ) : meshSize s N ≤ s := by
  rw [meshSize, div_le_iff₀ (by positivity)]
  have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
  nlinarith

/-- The interior nodes of the level-`(N + 1)` lattice. -/
abbrev Nodes (n N : ℕ) := ↥(interiorNodes n (N + 1))

/-- The discrete space: nodal values at the interior nodes, with the maximum norm. -/
abbrev Space (n N : ℕ) := Nodes n N → ℝ

variable {N : ℕ}

/-- The nodal function on `ℝⁿ` with values `U` at the interior nodes and `0` elsewhere. -/
def nodal (b : Fin n → ℝ) (s : ℝ) (U : Space n N) : (Fin n → ℝ) → ℝ :=
  nodalFun (fun q : Nodes n N => node b (meshSize s N) q) U

theorem nodal_node (hs : 0 < s) (U : Space n N) (q : Fin n → ℤ) :
    nodal b s U (node b (meshSize s N) q) = zeroExt U q := by
  by_cases hq : q ∈ interiorNodes n (N + 1)
  · simp only [zeroExt, hq, ↓reduceDIte]
    exact nodalFun_apply (node_injective_subtype b (meshSize_pos hs N).ne' _) U ⟨q, hq⟩
  · simp only [zeroExt, hq, ↓reduceDIte]
    refine sum_eq_zero fun c _ => ?_
    rw [ite_eq_right_iff]
    intro e
    exact absurd (node_injective b (meshSize_pos hs N).ne' e ▸ c.2) hq

/-- **The Freudenthal meshes with their interior nodes**: the level-`(N + 1)` meshes of
`b + (0, s)ⁿ` are non-obtuse (`Feec.FiniteElement.isNonobtuse_freudenthalMesh`), a family of
non-obtuse meshes (`Feec.FiniteElement.NonobtuseMeshes`) with Dirichlet data at the boundary
nodes. -/
abbrev meshes (b : Fin n → ℝ) (hs : 0 < s) : NonobtuseMeshes n ℕ where
  mesh N := freudenthalMesh b s hs (N + 1)
  Node N := Nodes n N
  x N q := node b (meshSize s N) q
  injective N := node_injective_subtype b (meshSize_pos hs N).ne' _
  isNonobtuse N := isNonobtuse_freudenthalMesh b hs (N + 1)

/-- **The lumped-mass `P₁` Laplacian** `Lₕ = -M_L⁻¹ K` on the level-`(N + 1)` Freudenthal mesh of
`b + (0, s)ⁿ`, with homogeneous Dirichlet data: `(Lₕ U)(p) = -a(φₚ, U) / m(p)` at the interior
nodes (`Feec.FiniteElement.lumpedLaplacianOn`). -/
def lumpedLaplacian (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) : Space n N →L[ℝ] Space n N :=
  (meshes b hs).L N

theorem lumpedLaplacian_apply_eq (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) (p : Nodes n N) :
    lumpedLaplacian b hs N U p =
      -p1Stiffness (freudenthalMesh b s hs (N + 1)) (nodalIndicator (node b (meshSize s N) p))
        (nodal b s U) / lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p) :=
  lumpedLaplacianOn_apply _ _ U p

/-- **The stencil** (`Lₕ` is the difference Laplacian). [Thomee2006], Ch. 15 -/
theorem lumpedLaplacian_apply (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) (p : Nodes n N) :
    lumpedLaplacian b hs N U p = ∑ l, (zeroExt U ((p : Fin n → ℤ) + Pi.single l 1) - 2 * U p +
      zeroExt U ((p : Fin n → ℤ) - Pi.single l 1)) / meshSize s N ^ 2 := by
  rw [lumpedLaplacian_apply_eq, meshSize, neg_p1Stiffness_div_lumpedMass b hs (N + 1) p.2]
  refine sum_congr rfl fun l _ => ?_
  have e := nodal_node (b := b) hs U
  simp only [meshSize] at e
  rw [e, e, e]
  congr 2
  simp [zeroExt, p.2]

/-- **The discrete maximum principle**: the Freudenthal meshes are non-obtuse, so `Lₕ` is a
sub-Markov generator (`Feec.FiniteElement.isSubMarkovGenerator_lumpedLaplacianOn`) and `e^{tLₕ}`
is positive and contractive in the maximum norm. [CiarletRaviart1973]; [Thomee2006], Ch. 15 -/
theorem isSubMarkovGenerator (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    IsSubMarkovGenerator (lumpedLaplacian b hs N) :=
  (meshes b hs).isSubMarkovGenerator N

/-! ### Consistency -/

/-- The nodal interpolant `(Iₕ u)(p) = u(b + h p)` at the interior nodes. -/
def interp (b : Fin n → ℝ) (s : ℝ) (N : ℕ) (u : (Fin n → ℝ) → ℝ) : Space n N :=
  fun p => u (node b (meshSize s N) p)

/-- A lattice node lies in the closed cube iff it is a node of the level-`(N + 1)` lattice. -/
theorem node_mem_closedCube_iff (hs : 0 < s) {q : Fin n → ℤ} :
    node b (meshSize s N) q ∈ closedCube b s ↔ ∀ j, 0 ≤ q j ∧ q j ≤ N + 1 := by
  have hm := meshSize_mul s N
  have hh := meshSize_pos hs N
  set h := meshSize s N
  simp only [closedCube, mem_univ_pi]
  refine forall_congr' fun j => ?_
  rw [node_coord, Set.mem_Icc, le_add_iff_nonneg_right, add_le_add_iff_left, ← hm,
    mul_nonneg_iff_of_pos_left hh, mul_le_mul_iff_of_pos_left hh]
  push_cast
  norm_cast

/-- A lattice node lies in the open cube iff it is an interior node. -/
theorem node_mem_openCube_iff (hs : 0 < s) {q : Fin n → ℤ} :
    node b (meshSize s N) q ∈ openCube b s ↔ q ∈ interiorNodes n (N + 1) := by
  have hm := meshSize_mul s N
  have hh := meshSize_pos hs N
  set h := meshSize s N
  simp only [openCube, mem_univ_pi, mem_interiorNodes]
  refine forall_congr' fun j => ?_
  rw [node_coord, Set.mem_Ioo, lt_add_iff_pos_right, add_lt_add_iff_left, ← hm,
    mul_pos_iff_of_pos_left hh, mul_lt_mul_iff_of_pos_left hh]
  norm_cast

/-- The axis segment `x + τ eₗ` through a node `x` of the closed lattice lies in the closed cube
while its `l`-th coordinate does. -/
theorem node_add_mem_closedCube (hs : 0 < s) {p : Fin n → ℤ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ N + 1)
    (l : Fin n) {τ : ℝ} (h1 : 0 ≤ meshSize s N * p l + τ) (h2 : meshSize s N * p l + τ ≤ s) :
    node b (meshSize s N) p + τ • Pi.single l 1 ∈ closedCube b s := by
  intro i _
  have := (node_mem_closedCube_iff (b := b) hs).2 hp i (mem_univ i)
  by_cases hi : i = l
  · subst hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, node_coord,
      Set.mem_Icc]
    constructor <;> linarith
  · simpa [Pi.single_eq_of_ne hi] using this

/-- The segments `x ± t eₗ`, `|t| ≤ h`, through an interior node lie in the closed cube. -/
theorem node_add_smul_mem_closedCube (hs : 0 < s) {p : Fin n → ℤ} (hp : p ∈ interiorNodes n (N + 1))
    (l : Fin n) {t : ℝ} (ht : t ∈ Icc (-meshSize s N) (meshSize s N)) :
    node b (meshSize s N) p + t • Pi.single l 1 ∈ closedCube b s := by
  have hp' := mem_interiorNodes.1 hp
  have hm := meshSize_mul s N
  push_cast at hm
  have := hp' l
  have h1 : (1 : ℝ) ≤ p l := by exact_mod_cast (by omega : (1 : ℤ) ≤ p l)
  have h2 : (p l : ℝ) ≤ N := by exact_mod_cast (by omega : p l ≤ N)
  exact node_add_mem_closedCube hs (fun i => by have := hp' i; omega) l
    (by nlinarith [ht.1, meshSize_pos hs N]) (by nlinarith [ht.2, meshSize_pos hs N])

/-- Interior nodes lie in the open cube. -/
theorem node_mem_openCube (hs : 0 < s) (p : Nodes n N) :
    node b (meshSize s N) p ∈ openCube b s :=
  (node_mem_openCube_iff hs).2 p.2

/-- The extension by `0` of the interpolant of `u`, `u = 0` on `∂Q`, is `u` at every node of the
closed lattice. -/
theorem zeroExt_interp (hs : 0 < s) {u : (Fin n → ℝ) → ℝ}
    (hbd : ∀ x ∈ closedCube b s, x ∉ openCube b s → u x = 0) {q : Fin n → ℤ}
    (hq : ∀ j, 0 ≤ q j ∧ q j ≤ N + 1) :
    zeroExt (interp b s N u) q = u (node b (meshSize s N) q) := by
  simp only [zeroExt, interp]
  split_ifs with hq'
  · rfl
  · exact (hbd _ ((node_mem_closedCube_iff hs).2 hq) fun ho =>
      hq' ((node_mem_openCube_iff hs).1 ho)).symm

/-- **Consistency in the maximum norm**: for `u ∈ C⁴` vanishing on `∂Q` with `|∂ᵢ⁴ u| ≤ B` on
`Q̄`, `|(Iₕ Δu)(p) - (Lₕ Iₕ u)(p)| ≤ n B h² / 12` at every interior node (the truncation error of
the difference Laplacian, by Taylor's formula along the axes, `abs_secondDiff_sub_le`). -/
theorem abs_interp_laplacian_sub_le (hs : 0 < s) (N : ℕ) {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 4 u) {B : ℝ}
    (hB : ∀ x ∈ closedCube b s, ∀ i, |(partialDeriv i)^[4] u x| ≤ B)
    (hbd : ∀ x ∈ closedCube b s, x ∉ openCube b s → u x = 0) (p : Nodes n N) :
    |interp b s N (laplacian u) p - lumpedLaplacian b hs N (interp b s N u) p| ≤
      n * B * meshSize s N ^ 2 / 12 := by
  set h := meshSize s N
  have hh := meshSize_pos hs N
  set x := node b h p
  have hp := mem_interiorNodes.1 p.2
  have hterm : ∀ l, |partialDeriv l (partialDeriv l u) x -
      (u (node b h ((p : Fin n → ℤ) + Pi.single l 1)) - 2 * u x +
        u (node b h ((p : Fin n → ℤ) - Pi.single l 1))) / h ^ 2| ≤ B * h ^ 2 / 12 := by
    intro l
    rw [node_add_single_one, node_sub_single_one]
    exact abs_partialDeriv_sub_secondDiff_le hu hh x l fun t ht =>
      hB _ (node_add_smul_mem_closedCube hs p.2 l ht) l
  have hplus : ∀ l, zeroExt (interp b s N u) ((p : Fin n → ℤ) + Pi.single l 1) =
      u (node b h ((p : Fin n → ℤ) + Pi.single l 1)) := fun l =>
    zeroExt_interp hs hbd fun j => by
      have := hp j
      by_cases hj : j = l
      · subst hj; simp only [Pi.add_apply, Pi.single_eq_same]; omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]; omega
  have hminus : ∀ l, zeroExt (interp b s N u) ((p : Fin n → ℤ) - Pi.single l 1) =
      u (node b h ((p : Fin n → ℤ) - Pi.single l 1)) := fun l =>
    zeroExt_interp hs hbd fun j => by
      have := hp j
      by_cases hj : j = l
      · subst hj; simp only [Pi.sub_apply, Pi.single_eq_same]; omega
      · simp only [Pi.sub_apply, Pi.single_eq_of_ne hj, sub_zero]; omega
  rw [lumpedLaplacian_apply, show interp b s N (laplacian u) p =
    ∑ l, partialDeriv l (partialDeriv l u) x from rfl, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l, |partialDeriv l (partialDeriv l u) x - (zeroExt (interp b s N u)
          ((p : Fin n → ℤ) + Pi.single l 1) - 2 * interp b s N u p +
          zeroExt (interp b s N u) ((p : Fin n → ℤ) - Pi.single l 1)) / h ^ 2|
      ≤ ∑ _l : Fin n, B * h ^ 2 / 12 := sum_le_sum fun l _ => by
        rw [hplus, hminus]; exact hterm l
    _ = n * B * h ^ 2 / 12 := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Consistency in the maximum norm**: `‖Iₕ Δu - Lₕ Iₕ u‖_∞ ≤ n B h² / 12`. -/
theorem norm_interp_laplacian_sub_le (hs : 0 < s) (N : ℕ) {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 4 u) {B : ℝ}
    (hB : ∀ x ∈ closedCube b s, ∀ i, |(partialDeriv i)^[4] u x| ≤ B)
    (hbd : ∀ x ∈ closedCube b s, x ∉ openCube b s → u x = 0) :
    ‖interp b s N (laplacian u) - lumpedLaplacian b hs N (interp b s N u)‖ ≤
      n * B * meshSize s N ^ 2 / 12 := by
  have h0 : 0 ≤ n * B * meshSize s N ^ 2 / 12 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hb : b ∈ closedCube b s := fun i _ => ⟨le_rfl, by linarith⟩
      have := (abs_nonneg _).trans (hB b hb ⟨0, hn⟩)
      positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun p => ?_
  rw [Real.norm_eq_abs]
  exact abs_interp_laplacian_sub_le hs N hu hB hbd p

/-! ### The lumped-mass Galerkin method on `P̊₁⁻Λ⁰` -/

/-- The **global `P₁` function** `U_h` of the discrete values `U` (`0` at the boundary nodes) on
the level-`(N + 1)` Freudenthal mesh: an element of the global Whitney `0`-form (Lagrange `P₁`)
space. -/
def feFun (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) :
    (whitneyElement n).globalSpace (freudenthalMesh b s hs (N + 1)) 0 :=
  p1Global _ (nodal b s U)

/-- `d U_h ∈ L²Λ¹(Q)` (elementwise `d`, the `L²` exterior derivative by
`Feec.FiniteElement.inner_maximal_p1Global`). -/
def dFeFun (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) :
    Feec.Domain.L2F ℝ (freudenthalMesh b s hs (N + 1)).domain
      (Feec.Domain.formIdx n (((0 : ℕ) : ℤ) + 1)) :=
  (whitneyElement n).glue _ (((0 : ℕ) : ℤ) + 1) ((whitneyElement n).dPiecewise _ 0
    (feFun b hs U : (whitneyElement n).Piecewise (freudenthalMesh b s hs (N + 1)) 0))

/-- The **lumped-mass inner product** `(U, V)_h = Σ_p m(p) U(p) V(p)`, the vertex quadrature of
`∫ U_h V_h`. -/
def lumpedInner (b : Fin n → ℝ) (hs : 0 < s) (U V : Space n N) : ℝ :=
  ∑ p : Nodes n N, lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p) *
    U p * V p

theorem lumpedMass_node_pos (b : Fin n → ℝ) (hs : 0 < s) (p : Nodes n N) :
    0 < lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p) := by
  have := lumpedMass_freudenthalMesh b hs (N + 1) p.2
  rw [meshSize, this]
  exact pow_pos (meshSize_pos hs N) n

/-- **The lumped-mass `P₁` Laplacian in weak form**: `(Lₕ U, V)_h = -a(U_h, V_h)`. -/
theorem lumpedInner_lumpedLaplacian (b : Fin n → ℝ) (hs : 0 < s) (U V : Space n N) :
    lumpedInner b hs (lumpedLaplacian b hs N U) V =
      -p1Stiffness (freudenthalMesh b s hs (N + 1)) (nodal b s U) (nodal b s V) := by
  rw [p1Stiffness_comm, nodal, nodalFun_eq_sum _ V, p1Stiffness_sum_smul, lumpedInner,
    ← sum_neg_distrib]
  refine sum_congr rfl fun p _ => ?_
  rw [lumpedLaplacian_apply_eq]
  have := (lumpedMass_node_pos b hs p).ne'
  field_simp

/-- **The scheme is the lumped-mass Galerkin method on `P̊₁⁻Λ⁰`** (`feEquiv`):
`(Lₕ U, V)_h = -⟪d U_h, d V_h⟫_{L²Λ¹(Q)} = -∫_Q ∇U_h · ∇V_h` for all discrete values `U, V`. -/
theorem lumpedInner_lumpedLaplacian_eq_neg_inner (b : Fin n → ℝ) (hs : 0 < s) (U V : Space n N) :
    lumpedInner b hs (lumpedLaplacian b hs N U) V = -⟪dFeFun b hs U, dFeFun b hs V⟫_ℝ := by
  rw [lumpedInner_lumpedLaplacian, dFeFun, dFeFun, feFun, feFun,
    inner_glue_dPiecewise_p1Global _ (fun T hT =>
      interior_subset_freudenthalMesh_domain b hs (N + 1) hT)]

/-- **`Lₕ` is determined by the Galerkin equations**: `W = Lₕ U` iff
`(W, V)_h = -⟪d U_h, d V_h⟫` for every `V`; so `U' = Lₕ U` is the semidiscrete lumped-mass
Galerkin equation `(U', V)_h + ⟪d U_h, d V_h⟫ = 0`. [Thomee2006], Ch. 15 -/
theorem lumpedLaplacian_eq_iff (b : Fin n → ℝ) (hs : 0 < s) (U W : Space n N) :
    lumpedLaplacian b hs N U = W ↔
      ∀ V : Space n N, lumpedInner b hs W V = -⟪dFeFun b hs U, dFeFun b hs V⟫_ℝ := by
  constructor
  · rintro rfl V; exact lumpedInner_lumpedLaplacian_eq_neg_inner b hs U V
  · intro h
    classical
    funext p
    have key : ∀ W' : Space n N, lumpedInner b hs W' (Pi.single p 1) =
        lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p) * W' p := fun W' => by
      rw [lumpedInner, Finset.sum_eq_single p]
      · simp
      · intro q _ hq; simp [hq]
      · simp
    have h1 := key (lumpedLaplacian b hs N U)
    rw [lumpedInner_lumpedLaplacian_eq_neg_inner, ← h (Pi.single p 1), key] at h1
    exact (mul_left_cancel₀ (lumpedMass_node_pos b hs p).ne' h1).symm

theorem interior_closure_freudenthalMesh_domain (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    interior (closure (freudenthalMesh b s hs (N + 1)).domain) = openCube b s := by
  rw [freudenthalMesh_domain, closure_pi_set, interior_pi_set Set.finite_univ]
  refine Set.pi_congr rfl fun i _ => ?_
  rw [closure_Ioo (by linarith : b i ≠ b i + s), interior_Icc]

/-- **The interior nodes are the free vertices** of the mesh: the vertices off `∂Q`. -/
theorem isFreeVertexEnum (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    IsFreeVertexEnum (freudenthalMesh b s hs (N + 1))
      fun p : Nodes n N => node b (meshSize s N) p := by
  refine ⟨node_injective_subtype b (meshSize_pos hs N).ne' _, fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨p, rfl⟩
    refine ⟨exists_mem_vertexSet_of_lumpedMass_pos _ (lumpedMass_node_pos b hs p), fun h => ?_⟩
    rw [frontier, interior_closure_freudenthalMesh_domain] at h
    exact h.2 (node_mem_openCube hs p)
  · rintro ⟨⟨T, hT, hy⟩, hyf⟩
    obtain ⟨q, rfl⟩ : ∃ q, y = node b (meshSize s N) q := exists_eq_node_of_mem_vertexSet b hT hy
    have hq : node b (meshSize s N) q ∈ openCube b s := by
      rw [← interior_closure_freudenthalMesh_domain b hs N]
      by_contra h
      exact hyf ⟨subset_closure ((freudenthalMesh b s hs (N + 1)).closedInterior_subset_closure hT
        (vertexSet_subset_closedInterior T hy)), h⟩
    exact ⟨⟨q, (node_mem_openCube_iff hs).1 hq⟩, rfl⟩

/-- **The nodal values are a linear isomorphism `ℝ^{interior nodes} ≃ P̊₁⁻Λ⁰`**, `U ↦ U_h`: every
`P₁` function with vanishing boundary DOFs is `U_h` for its values `U` at the interior nodes
(`Feec.FiniteElement.p1GlobalEquiv₀`). -/
def feEquiv (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    Space n N ≃ₗ[ℝ] (whitneyElement n).globalSpace₀ (freudenthalMesh b s hs (N + 1)) 0 :=
  p1GlobalEquiv₀ _ (isFreeVertexEnum b hs N)

theorem feEquiv_apply (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) :
    (feEquiv b hs N U : (whitneyElement n).Piecewise (freudenthalMesh b s hs (N + 1)) 0) =
      feFun b hs U := rfl

/-- `U_h` has vanishing boundary DOFs: it lies in the space `P̊₁⁻Λ⁰` of the minimal (`H̊¹`)
complex. -/
theorem feFun_mem_globalSpace₀ (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) :
    (feFun b hs U : (whitneyElement n).Piecewise (freudenthalMesh b s hs (N + 1)) 0) ∈
      (whitneyElement n).globalSpace₀ (freudenthalMesh b s hs (N + 1)) 0 :=
  (feEquiv b hs N U).2

/-- **The scheme is the lumped-mass Galerkin method on `P̊₁⁻Λ⁰`**: `W = Lₕ U` iff
`(W, v)_h = -⟪d U_h, d v⟫_{L²Λ¹(Q)}` for every test function `v ∈ P̊₁⁻Λ⁰`, `(W, v)_h` the
vertex quadrature with the nodal values of `v` (`feEquiv`). [Thomee2006], Ch. 15 -/
theorem lumpedLaplacian_eq_iff_globalSpace₀ (b : Fin n → ℝ) (hs : 0 < s) (U W : Space n N) :
    lumpedLaplacian b hs N U = W ↔
      ∀ v : (whitneyElement n).globalSpace₀ (freudenthalMesh b s hs (N + 1)) 0,
        lumpedInner b hs W ((feEquiv b hs N).symm v) = -⟪dFeFun b hs U, (whitneyElement n).glue _
          (((0 : ℕ) : ℤ) + 1) ((whitneyElement n).dPiecewise _ 0 v)⟫_ℝ := by
  refine (lumpedLaplacian_eq_iff b hs U W).trans ⟨fun h v => ?_, fun h V => ?_⟩
  · simpa only [dFeFun, ← feEquiv_apply, LinearEquiv.apply_symm_apply] using
      h ((feEquiv b hs N).symm v)
  · simpa only [dFeFun, ← feEquiv_apply, LinearEquiv.symm_apply_apply] using h (feEquiv b hs N V)

/-! ### The stable family and the heat equation -/

/-- **The maximum-norm family**: the lumped-mass `P₁` Laplacians `Lₕ` of the levels `N + 1` on
`ℝ^{interior nodes}` with the maximum norm, a uniformly stable family with `M = 1`
(`isSubMarkovGenerator`), the family of `meshes` (`Feec.FiniteElement.NonobtuseMeshes.family`). -/
abbrev family (b : Fin n → ℝ) (hs : 0 < s) : StableFamily ℝ ℕ :=
  (meshes b hs).family

@[simp] theorem family_M (b : Fin n → ℝ) (hs : 0 < s) : (family b hs).M = 1 := rfl

@[simp] theorem family_L (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    (family b hs).L N = lumpedLaplacian b hs N := rfl

/-- A **classical solution of the heat equation** `uₜ = Δu` on `[0, T] × Q`, `u = 0` on `∂Q`:
`C⁴` on all of `ℝⁿ` at each time with `|∂ᵢ⁴ u| ≤ B₄` on `Q̄`, with time derivative
`u₁ = uₜ = Δu` in `Q`. -/
structure HeatSolution (b : Fin n → ℝ) (s T : ℝ) where
  /-- the solution -/
  u : ℝ → (Fin n → ℝ) → ℝ
  /-- its time derivative -/
  u₁ : ℝ → (Fin n → ℝ) → ℝ
  contDiff : ∀ t ∈ Icc 0 T, ContDiff ℝ 4 (u t)
  hasDerivAt : ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, HasDerivAt (fun t => u t x) (u₁ t x) t
  heat : ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, u₁ t x = laplacian (u t) x
  boundary : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, x ∉ openCube b s → u t x = 0
  /-- the bound of the fourth derivatives -/
  B₄ : ℝ
  bound₄ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, ∀ i, |(partialDeriv i)^[4] (u t) x| ≤ B₄

namespace HeatSolution

variable {T : ℝ} (S : HeatSolution b s T)

/-- The truncation error `n B₄ h² / 12` of the space discretization. -/
def defect (N : ℕ) : ℝ := n * S.B₄ * meshSize s N ^ 2 / 12

/-- **The defect of the interpolated solution**: `‖Iₕ uₜ - Lₕ Iₕ u‖_∞ ≤ n B₄ h² / 12`. -/
theorem norm_defect_le (hs : 0 < s) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖interp b s N (S.u₁ t) - lumpedLaplacian b hs N (interp b s N (S.u t))‖ ≤ S.defect N := by
  have e : interp b s N (S.u₁ t) = interp b s N (laplacian (S.u t)) :=
    funext fun p => S.heat t ht _ (node_mem_openCube hs p)
  rw [e]
  exact norm_interp_laplacian_sub_le hs N (S.contDiff t ht) (S.bound₄ t ht) (S.boundary t ht)

end HeatSolution

/-- **The semidiscrete error in the maximum norm**: `‖Iₕ u(t) - e^{tLₕ} v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞`
`+ t n B₄ h² / 12` for `t ∈ [0, T]`, every discrete datum `v`
(`Feec.FiniteElement.NonobtuseMeshes.norm_interp_sub_exp_le` with the consistency error
`n B₄ h² / 12`). -/
theorem norm_interp_sub_exp_le (hs : 0 < s) {T : ℝ} (S : HeatSolution b s T) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) (v : Space n N) :
    ‖interp b s N (S.u t) - exp (t • lumpedLaplacian b hs N) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + t * S.defect N := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  exact (meshes b hs).norm_interp_sub_exp_le N ht.1
    (fun r hr q => S.hasDerivAt r (hsub hr) _ (node_mem_openCube hs q))
    (fun r hr => S.norm_defect_le hs N (hsub hr)) v

/-- **Backward Euler in the maximum norm**: if moreover `uₜ` has time derivative `u₂` with
`|u₂| ≤ B₂` in `Q`, then for `kτ ≤ T`
`‖Iₕ u(kτ) - (1 - τLₕ)⁻ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ (3/2 τ B₂ + n B₄ h² / 12)`:
`O(τ + h²)`, unconditionally stable (Hille–Yosida, `M = 1`). -/
theorem norm_interp_sub_res_pow_le (hs : 0 < s) {T : ℝ} (S : HeatSolution b s T)
    {u₂ : ℝ → (Fin n → ℝ) → ℝ} {B₂ : ℝ}
    (hu₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, HasDerivAt (fun t => S.u₁ t x) (u₂ t x) t)
    (hB₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, |u₂ t x| ≤ B₂) (N : ℕ) {τ : ℝ} (hτ : 0 < τ)
    {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) :
    ‖interp b s N (S.u (k * τ)) - ((family b hs).res τ N ^ k) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * (3 / 2 * τ * B₂ + S.defect N) := by
  have hsub : Icc 0 (k * τ) ⊆ Icc 0 T := Icc_subset_Icc le_rfl hk
  have hB : ∀ r ∈ Icc 0 (k * τ), ‖interp b s N (u₂ r)‖ ≤ B₂ := fun r hr => by
    have hc : b + (s / 2) • (fun _ => (1 : ℝ)) ∈ openCube b s := fun i _ => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, Set.mem_Ioo]
      constructor <;> linarith
    have h0 : 0 ≤ B₂ := (abs_nonneg _).trans (hB₂ r (hsub hr) _ hc)
    refine (pi_norm_le_iff_of_nonneg h0).2 fun p => ?_
    rw [Real.norm_eq_abs]
    exact hB₂ r (hsub hr) _ (node_mem_openCube hs p)
  exact (meshes b hs).norm_interp_sub_res_pow_le hτ N
    (fun r hr q => S.hasDerivAt r (hsub hr) _ (node_mem_openCube hs q))
    (fun r hr q => hu₂ r (hsub hr) _ (node_mem_openCube hs q)) hB
    (fun r hr => S.norm_defect_le hs N (hsub hr)) v

/-- **Every A-stable rational scheme in the maximum norm**: for `r` of order `p` (Crank–Nicolson,
the Gauss and Radau methods),
`‖Iₕ u(kτ) - r(τLₕ)ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ n B₄ h² / 12 + C_r kτ τᵖ ‖Lₕ^{p+1} v‖_∞`,
`C_r = sharpConst r p` (Brenner–Thomée's smooth-data estimate, `M = 1`). -/
theorem norm_interp_sub_step_pow_le (hs : 0 < s) {T : ℝ} (S : HeatSolution b s T)
    {r : RationalScheme} (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) (N : ℕ) {τ : ℝ}
    (hτ : 0 < τ) {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) :
    ‖interp b s N (S.u (k * τ)) - ((family b hs).step r τ N ^ k) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * S.defect N +
        r.sharpConst p * (k * τ) * τ ^ p * ‖(lumpedLaplacian b hs N ^ (p + 1)) v‖ :=
  have hsub : Icc 0 (k * τ) ⊆ Icc 0 T := Icc_subset_Icc le_rfl hk
  (meshes b hs).norm_interp_sub_step_pow_le hr hp hτ N
    (fun t ht q => S.hasDerivAt t (hsub ht) _ (node_mem_openCube hs q))
    (fun _ ht => S.norm_defect_le hs N (hsub ht)) v

/-- **Brenner–Thomée's stability bound in the maximum norm**: `‖r(τLₕ)ᵏ‖_∞ ≤ 1 + C'_r √k` for
every A-stable `r` (Crank–Nicolson included), uniformly in `h`. [BrennerThomee1979] -/
theorem norm_step_pow_le (hs : 0 < s) {r : RationalScheme} (hr : r.IsAStable) (N : ℕ) {τ : ℝ}
    (hτ : 0 < τ) (k : ℕ) : ‖(family b hs).step r τ N ^ k‖ ≤ 1 + r.sqrtConst * √k :=
  (meshes b hs).norm_step_pow_le hr hτ N k

/-! ### A classical solution: the first eigenmode -/

/-- The frequency `a = π / s` of the first Dirichlet eigenmode of the cube. -/
def sineFreq (s : ℝ) : ℝ := Real.pi / s

/-- The factor `y ↦ sin(a (y - c))` and its derivatives `aᵏ sin⁽ᵏ⁾(a (y - c))`. -/
def sineDeriv (a c : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun y => Real.sin (a * (y - c))
  | 1 => fun y => a * Real.cos (a * (y - c))
  | 2 => fun y => -a ^ 2 * Real.sin (a * (y - c))
  | 3 => fun y => -a ^ 3 * Real.cos (a * (y - c))
  | _ => fun y => a ^ 4 * Real.sin (a * (y - c))

theorem hasDerivAt_sineDeriv (a c : ℝ) (k : ℕ) (hk : k ≤ 3) (y : ℝ) :
    HasDerivAt (sineDeriv a c k) (sineDeriv a c (k + 1) y) y := by
  have hl : HasDerivAt (fun y => a * (y - c)) a y := by
    simpa using ((hasDerivAt_id y).sub_const c).const_mul a
  have hs := (Real.hasDerivAt_sin _).comp y hl
  have hc := (Real.hasDerivAt_cos _).comp y hl
  interval_cases k
  · exact hs.congr_deriv (by simp [sineDeriv]; ring)
  · exact (hc.const_mul a).congr_deriv (by simp [sineDeriv]; ring)
  · exact (hs.const_mul (-a ^ 2)).congr_deriv (by simp [sineDeriv]; ring)
  · exact (hc.const_mul (-a ^ 3)).congr_deriv (by simp [sineDeriv]; ring)

theorem differentiable_sineDeriv (a c : ℝ) (k : ℕ) : Differentiable ℝ (sineDeriv a c k) := by
  rcases k with _ | _ | _ | _ | k <;> simp only [sineDeriv] <;> fun_prop

/-- The factors of the eigenmode, the `i`-th differentiated `k` times. -/
def sineFactors (b : Fin n → ℝ) (a : ℝ) (i : Fin n) (k : ℕ) : Fin n → ℝ → ℝ :=
  Function.update (fun j => sineDeriv a (b j) 0) i (sineDeriv a (b i) k)

theorem sineFactors_zero (b : Fin n → ℝ) (a : ℝ) (i : Fin n) :
    sineFactors b a i 0 = fun j => sineDeriv a (b j) 0 := by
  funext j; by_cases hj : j = i
  · subst hj; simp [sineFactors]
  · simp [sineFactors, Function.update_of_ne hj]

/-- `∂ᵢᵏ (c ∏ⱼ sin(a (xⱼ - bⱼ))) = c ∏ⱼ (factor `i` differentiated `k` times)`, `k ≤ 4`. -/
theorem iterate_partialDeriv_sine (b : Fin n → ℝ) (a c : ℝ) (i : Fin n) (k : ℕ) (hk : k ≤ 4) :
    (partialDeriv i)^[k] (fun x : Fin n → ℝ => c * ∏ j, sineDeriv a (b j) 0 (x j)) =
      fun x => c * ∏ j, sineFactors b a i k j (x j) := by
  induction k with
  | zero => rw [sineFactors_zero]; rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hG : ∀ j, Differentiable ℝ (sineFactors b a i k j) := fun j => by
      rw [sineFactors, Function.update_apply]; split_ifs <;> exact differentiable_sineDeriv _ _ _
    rw [partialDeriv_const_mul_prod c hG (g := sineDeriv a (b i) (k + 1)) (fun y => by
      simpa [sineFactors] using hasDerivAt_sineDeriv a (b i) k (by omega) y)]
    simp only [sineFactors, Function.update_idem]

/-- `∏ⱼ G̃ⱼ(xⱼ) = κ ∏ⱼ Gⱼ(xⱼ)` when the `i`-th factor is replaced by `κ Gᵢ`. -/
theorem prod_update_const_mul (G : Fin n → ℝ → ℝ) (i : Fin n) (κ : ℝ) (x : Fin n → ℝ) :
    ∏ j, Function.update G i (fun y => κ * G i y) j (x j) = κ * ∏ j, G j (x j) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The eigenmode `e^{-λt} ∏ᵢ sin(π(xᵢ - cᵢ)/s)` has time derivative `-λ` times itself (any
centre `c`, any `x`). -/
theorem hasDerivAt_sineMode (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) :
    HasDerivAt (fun t => Real.exp (-(n * sineFreq s ^ 2) * t) *
        ∏ j, sineDeriv (sineFreq s) (c j) 0 (x j))
      (-(n * sineFreq s ^ 2) * (Real.exp (-(n * sineFreq s ^ 2) * t) *
        ∏ j, sineDeriv (sineFreq s) (c j) 0 (x j))) t := by
  have := ((Real.hasDerivAt_exp _).comp t
    ((hasDerivAt_id t).const_mul (-(n * sineFreq s ^ 2)))).mul_const
    (∏ j, sineDeriv (sineFreq s) (c j) 0 (x j))
  exact this.congr_deriv (by simp; ring)

/-- `Δ` of the eigenmode is `-λ` times itself, `λ = n (π/s)²` (any centre, any `x`). -/
theorem laplacian_sineMode (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) :
    laplacian (fun x : Fin n → ℝ => Real.exp (-(n * sineFreq s ^ 2) * t) *
        ∏ j, sineDeriv (sineFreq s) (c j) 0 (x j)) x =
      -(n * sineFreq s ^ 2) * (Real.exp (-(n * sineFreq s ^ 2) * t) *
        ∏ j, sineDeriv (sineFreq s) (c j) 0 (x j)) := by
  have e : ∀ i, partialDeriv i (partialDeriv i (fun x : Fin n → ℝ =>
      Real.exp (-(n * sineFreq s ^ 2) * t) * ∏ j, sineDeriv (sineFreq s) (c j) 0 (x j))) x =
      -sineFreq s ^ 2 * (Real.exp (-(n * sineFreq s ^ 2) * t) *
        ∏ j, sineDeriv (sineFreq s) (c j) 0 (x j)) :=
    fun i => by
      have := congrFun (iterate_partialDeriv_sine c (sineFreq s)
        (Real.exp (-(n * sineFreq s ^ 2) * t)) i 2 (by omega)) x
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id] at this
      rw [this, sineFactors, show sineDeriv (sineFreq s) (c i) 2 =
        fun y => -sineFreq s ^ 2 * sineDeriv (sineFreq s) (c i) 0 y from rfl,
        prod_update_const_mul (fun j => sineDeriv (sineFreq s) (c j) 0)]
      ring
  simp only [laplacian, e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `|∂ᵢ⁴|` of the eigenmode is at most `(π/s)⁴` for `t ≥ 0` (any centre, any `x`). -/
theorem abs_iterate_partialDeriv_sineMode_le (c : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (x : Fin n → ℝ) (i : Fin n) :
    |(partialDeriv i)^[4] (fun x : Fin n → ℝ => Real.exp (-(n * sineFreq s ^ 2) * t) *
        ∏ j, sineDeriv (sineFreq s) (c j) 0 (x j)) x| ≤
      sineFreq s ^ 4 := by
  have := congrFun (iterate_partialDeriv_sine c (sineFreq s)
    (Real.exp (-(n * sineFreq s ^ 2) * t)) i 4 le_rfl) x
  rw [this, sineFactors, show sineDeriv (sineFreq s) (c i) 4 =
    fun y => sineFreq s ^ 4 * sineDeriv (sineFreq s) (c i) 0 y from rfl,
    prod_update_const_mul (fun j => sineDeriv (sineFreq s) (c j) 0), abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos _), Finset.abs_prod]
  have h1 : Real.exp (-(n * sineFreq s ^ 2) * t) ≤ 1 :=
    Real.exp_le_one_iff.2 (by rw [neg_mul]; exact neg_nonpos.2 (mul_nonneg (by positivity) ht))
  have h2 : ∏ j, |sineDeriv (sineFreq s) (c j) 0 (x j)| ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => Real.abs_sin_le_one _
  rw [abs_of_nonneg (by positivity)]
  calc Real.exp (-(n * sineFreq s ^ 2) * t) *
        (sineFreq s ^ 4 * ∏ j, |sineDeriv (sineFreq s) (c j) 0 (x j)|)
      ≤ 1 * (sineFreq s ^ 4 * 1) := by gcongr
    _ = sineFreq s ^ 4 := by ring

/-- **The first eigenmode** `u(t, x) = e^{-λt} ∏ᵢ sin(π (xᵢ - bᵢ)/s)`, `λ = n π² / s²`: a
classical solution of the heat equation on every `[0, T] × Q` with `B₄ = (π/s)⁴`. -/
def sineSolution (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) : HeatSolution b s T where
  u t x := Real.exp (-(n * sineFreq s ^ 2) * t) * ∏ j, sineDeriv (sineFreq s) (b j) 0 (x j)
  u₁ t x := -(n * sineFreq s ^ 2) *
    (Real.exp (-(n * sineFreq s ^ 2) * t) * ∏ j, sineDeriv (sineFreq s) (b j) 0 (x j))
  contDiff t _ := by simp only [sineDeriv]; fun_prop
  hasDerivAt t _ x _ := hasDerivAt_sineMode b t x
  heat t _ x _ := (laplacian_sineMode b t x).symm
  boundary t _ x hx hno := by
    obtain ⟨i, hi⟩ : ∃ i, x i = b i ∨ x i = b i + s := by
      by_contra! h
      exact hno fun i _ => ⟨lt_of_le_of_ne (hx i (mem_univ i)).1 (Ne.symm (h i).1),
        lt_of_le_of_ne (hx i (mem_univ i)).2 (h i).2⟩
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
    simp only [sineDeriv, sineFreq]
    rcases hi with h | h <;> rw [h]
    · simp
    · rw [add_sub_cancel_left, div_mul_cancel₀ _ hs.ne', Real.sin_pi]
  B₄ := sineFreq s ^ 4
  bound₄ t ht x _ i := abs_iterate_partialDeriv_sineMode_le b ht.1 x i

/-- The first eigenmode is nonzero at the centre of the cube at `t = 0`. -/
theorem sineSolution_u_zero_center (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) :
    (sineSolution b hs T).u 0 (b + (s / 2) • fun _ => (1 : ℝ)) = 1 := by
  simp only [sineSolution, sineDeriv, sineFreq, mul_zero, Real.exp_zero, one_mul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, mul_one, add_sub_cancel_left]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [show Real.pi / s * (s / 2) = Real.pi / 2 by field_simp, Real.sin_pi_div_two]

/-! ### The maximum norm of the finite element function -/

theorem closedInterior_subset_closedCube (hs : 0 < s) {K : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hK : K ∈ (freudenthalMesh b s hs (N + 1)).simplices) : K.closedInterior ⊆ closedCube b s := by
  refine ((freudenthalMesh b s hs (N + 1)).closedInterior_subset_closure hK).trans ?_
  rw [freudenthalMesh_domain, closure_pi_set]
  intro x hx i hi
  have := hx i hi
  simp only at this ⊢
  rwa [closure_Ioo (by linarith : b i ≠ b i + s)] at this

/-- The simplices of the level-`(N + 1)` mesh have diameter at most `h` (maximum norm). -/
theorem dist_le_meshSize (hs : 0 < s) {K : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hK : K ∈ (freudenthalMesh b s hs (N + 1)).simplices) {y z : Fin n → ℝ}
    (hy : y ∈ K.closedInterior) (hz : z ∈ K.closedInterior) : dist y z ≤ meshSize s N := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [Subsingleton.elim y z, dist_self]; exact (meshSize_pos hs N).le
  · have : NeZero n := ⟨(Fin.pos hn.some).ne'⟩
    obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hK
    refine (Metric.dist_le_diam_of_mem (Affine.Simplex.isCompact_closedInterior _).isBounded hy
      hz).trans (le_of_eq ?_)
    exact diam_freudenthalMesh_simplex b (freudenthalScale_pos hs (N + 1)) (finLattice m) σ

/-- The vertices of the level-`(N + 1)` mesh are lattice nodes `b + h q`, `q ∈ {0, …, N + 1}ⁿ`. -/
theorem exists_node_eq_points (hs : 0 < s) {K : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hK : K ∈ (freudenthalMesh b s hs (N + 1)).simplices) (j : Fin (n + 1)) :
    ∃ q : Fin n → ℤ, (∀ i, 0 ≤ q i ∧ q i ≤ N + 1) ∧ K.points j = node b (meshSize s N) q := by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hK
  rw [mapEquiv_boxMap_freudenthalSimplex_points, freudenthalPoints_eq_node]
  refine ⟨_, fun i => ?_, rfl⟩
  have h1 := (m i).2
  rcases kuhnLattice_mem σ j i with h | h <;>
    simp only [Pi.add_apply, h, finLattice] <;> omega


/-- **The simplices of the mesh cover `Q̄`** (`Feec.Mesh.SimplicialMesh.biUnion_closedInterior`,
from `Feec.Mesh.iUnion_freudenthalSet`): the bounds below on every simplex hold on all of `Q̄`. -/
theorem exists_simplex_mem (hs : 0 < s) {x : Fin n → ℝ} (hx : x ∈ closedCube b s) :
    ∃ K ∈ (freudenthalMesh b s hs (N + 1)).simplices, x ∈ K.closedInterior := by
  have h : x ∈ closure (freudenthalMesh b s hs (N + 1)).domain := by
    rw [freudenthalMesh_domain, closure_pi_set]
    intro i hi
    have := hx i hi
    simp only at this ⊢
    rwa [closure_Ioo (by linarith : b i ≠ b i + s)]
  rw [← (freudenthalMesh b s hs (N + 1)).biUnion_closedInterior] at h
  simpa using h

/-- The interpolation term `n² D₂ h² / 2`. -/
def feDefect (D₂ : ℝ) (N : ℕ) : ℝ := n ^ 2 * D₂ * meshSize s N ^ 2 / 2

/-- **A finite element function on `Q̄` from its values at the nodes**: for `u ∈ C²` with
`|∂ᵢ∂ₖ u| ≤ D` on `Q̄` and `g` with `|u - g| ≤ ε` at the nodes `{0, …, N + 1}ⁿ`, at every point `x`
of every simplex `K` of the mesh, `|u(x) - Π_K g(x)| ≤ ε + n² D h² / 2`
(`Feec.FiniteElement.abs_sub_p1Interp_le_of_vertices`); any boundary condition and node set. -/
theorem abs_sub_p1Interp_le_of_nodes (hs : 0 < s) (N : ℕ) {u g : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 2 u) {D ε : ℝ}
    (hD : ∀ x ∈ closedCube b s, ∀ i k, |partialDeriv k (partialDeriv i u) x| ≤ D)
    (hε : ∀ q : Fin n → ℤ, (∀ i, 0 ≤ q i ∧ q i ≤ N + 1) →
      |u (node b (meshSize s N) q) - g (node b (meshSize s N) q)| ≤ ε)
    {K : Affine.Simplex ℝ (Fin n → ℝ) n} (hK : K ∈ (freudenthalMesh b s hs (N + 1)).simplices)
    {x : Fin n → ℝ} (hx : x ∈ K.closedInterior) :
    |u x - p1Interp K.points g x| ≤ ε + feDefect (s := s) (n := n) D N :=
  abs_sub_p1Interp_le_of_vertices K hu
    (fun y hy => hD y (closedInterior_subset_closedCube hs hK hy))
    (fun y hy z hz => dist_le_meshSize hs hK hy hz) (fun j => by
      obtain ⟨q, hq, e⟩ := exists_node_eq_points hs hK j
      rw [e]; exact hε q hq) hx

/-- **The finite element function in the maximum norm on `Q̄`**: for `u ∈ C²` vanishing on `∂Q`
with `|∂ᵢ∂ₖ u| ≤ D` on `Q̄` and discrete values `U`, at every point `x` of every simplex `K` of the
mesh, `|u(x) - U_h(x)| ≤ ‖Iₕ u - U‖_∞ + n² D h² / 2`, `U_h = Π_K U` the global `P₁` function
(a `P₁` function attains its extrema at the vertices, plus the `P₁` interpolation error). -/
theorem abs_sub_p1Interp_nodal_le (hs : 0 < s) (N : ℕ) {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 2 u) {D : ℝ}
    (hD : ∀ x ∈ closedCube b s, ∀ i k, |partialDeriv k (partialDeriv i u) x| ≤ D)
    (hbd : ∀ x ∈ closedCube b s, x ∉ openCube b s → u x = 0) (U : Space n N)
    {K : Affine.Simplex ℝ (Fin n → ℝ) n} (hK : K ∈ (freudenthalMesh b s hs (N + 1)).simplices)
    {x : Fin n → ℝ} (hx : x ∈ K.closedInterior) :
    |u x - p1Interp K.points (nodal b s U) x| ≤
      ‖interp b s N u - U‖ + feDefect (s := s) (n := n) D N :=
  abs_sub_p1Interp_le_of_nodes hs N hu hD (fun q hq => by
    rw [nodal_node hs, ← zeroExt_interp hs hbd hq, ← zeroExt_sub]
    exact abs_zeroExt_le _ q) hK hx

theorem abs_sineDeriv_le {a : ℝ} (ha : 0 ≤ a) (c : ℝ) {k : ℕ} (hk : k ≤ 4) (y : ℝ) :
    |sineDeriv a c k y| ≤ a ^ k := by
  have hs := Real.abs_sin_le_one (a * (y - c))
  have hc := Real.abs_cos_le_one (a * (y - c))
  interval_cases k <;> simp only [sineDeriv, abs_mul, abs_neg, abs_pow, abs_of_nonneg ha] <;>
    first | simpa using hs | nlinarith [pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4]

/-- `∂ₖ (c ∏ⱼ sin⁽ᵐʲ⁾(a(xⱼ - bⱼ))) = c ∏ⱼ sin⁽ᵐ'ʲ⁾`, `m' = m + eₖ` (for `mₖ ≤ 3`). -/
theorem partialDeriv_sineProd (b : Fin n → ℝ) (a c : ℝ) (m : Fin n → ℕ) (k : Fin n)
    (hk : m k ≤ 3) :
    partialDeriv k (fun x : Fin n → ℝ => c * ∏ j, sineDeriv a (b j) (m j) (x j)) =
      fun x => c * ∏ j, sineDeriv a (b j) ((m + Pi.single k 1 : Fin n → ℕ) j) (x j) := by
  rw [partialDeriv_const_mul_prod c (G := fun j => sineDeriv a (b j) (m j))
    (fun j => differentiable_sineDeriv a _ _) (g := sineDeriv a (b k) (m k + 1))
    (fun y => hasDerivAt_sineDeriv a (b k) (m k) hk y)]
  funext x
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = k
  · subst hj; simp
  · simp [hj]

theorem abs_const_mul_sineProd_le {a : ℝ} (ha : 0 ≤ a) (b : Fin n → ℝ) (c : ℝ) (m : Fin n → ℕ)
    (hm : ∀ j, m j ≤ 4) (x : Fin n → ℝ) :
    |c * ∏ j, sineDeriv a (b j) (m j) (x j)| ≤ |c| * a ^ ∑ j, m j := by
  rw [abs_mul, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
    fun j _ => abs_sineDeriv_le ha _ (hm j) _) (abs_nonneg _)

/-- The second derivatives of the first eigenmode: `|∂ᵢ∂ₖ u| ≤ (π/s)²` for `t ≥ 0`. -/
theorem abs_partialDeriv_partialDeriv_sineSolution_le (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : Fin n → ℝ) (i k : Fin n) :
    |partialDeriv k (partialDeriv i ((sineSolution b hs T).u t)) x| ≤ sineFreq s ^ 2 := by
  have ha : 0 ≤ sineFreq s := div_nonneg Real.pi_pos.le hs.le
  set c := Real.exp (-(n * sineFreq s ^ 2) * t)
  have e0 : (sineSolution b hs T).u t =
      fun x => c * ∏ j, sineDeriv (sineFreq s) (b j) ((0 : Fin n → ℕ) j) (x j) := rfl
  have hsingle : ∀ (l : Fin n) (j : Fin n), (Pi.single l 1 : Fin n → ℕ) j ≤ 1 := fun l j => by
    by_cases h : j = l
    · subst h; simp
    · simp [h]
  rw [e0, partialDeriv_sineProd b _ c 0 i (by simp),
    partialDeriv_sineProd b _ c _ k (by have := hsingle i k; simp; omega)]
  refine (abs_const_mul_sineProd_le ha b c _ (fun j => by
    have := hsingle i j; have := hsingle k j; simp; omega) x).trans ?_
  have hc : |c| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2
      (by rw [neg_mul]; exact neg_nonpos.2 (mul_nonneg (by positivity) ht))
  have hsum : ∑ j, ((0 : Fin n → ℕ) + Pi.single i 1 + Pi.single k 1 : Fin n → ℕ) j = 2 := by
    simp [Finset.sum_add_distrib]
  rw [hsum]
  calc |c| * sineFreq s ^ 2 ≤ 1 * sineFreq s ^ 2 := by gcongr
    _ = _ := one_mul _

/-! ### The verdict -/

/-- The conclusions of `maxNormHeat` for the cube `b + (0, s)ⁿ`: non-obtuse Freudenthal meshes,
the difference stencil of the lumped-mass `P₁` Laplacian, the discrete maximum principle,
maximum-norm consistency, the semidiscrete, backward Euler and rational-scheme errors against
every classical solution, Brenner–Thomée's stability bound, and the verdict of the Banach layer
for the family. -/
structure Verdict (b : Fin n → ℝ) (hs : 0 < s) : Prop where
  /-- the Freudenthal meshes are non-obtuse (so the off-diagonal stiffness is nonpositive,
  `Feec.FiniteElement.p1Stiffness_indicator_nonpos`) -/
  nonobtuse (N : ℕ) [NeZero N] : IsNonobtuse (freudenthalMesh b s hs N)
  /-- the lumped-mass `P₁` Laplacian is the `(2n + 1)`-point difference Laplacian -/
  stencil (N : ℕ) (U : Space n N) (p : Nodes n N) :
    lumpedLaplacian b hs N U p = ∑ l, (zeroExt U ((p : Fin n → ℤ) + Pi.single l 1) - 2 * U p +
      zeroExt U ((p : Fin n → ℤ) - Pi.single l 1)) / meshSize s N ^ 2
  /-- the discrete maximum principle: `e^{tLₕ}` is positive and contractive in the maximum norm -/
  maximumPrinciple (N : ℕ) : IsSubMarkovGenerator (lumpedLaplacian b hs N)
  /-- consistency in the maximum norm, `‖Iₕ Δu - Lₕ Iₕ u‖_∞ ≤ n B h² / 12` -/
  consistency (N : ℕ) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 4 u) {B : ℝ}
    (hB : ∀ x ∈ closedCube b s, ∀ i, |(partialDeriv i)^[4] u x| ≤ B)
    (hbd : ∀ x ∈ closedCube b s, x ∉ openCube b s → u x = 0) :
    ‖interp b s N (laplacian u) - lumpedLaplacian b hs N (interp b s N u)‖ ≤
      n * B * meshSize s N ^ 2 / 12
  /-- the semidiscrete error against every classical solution -/
  semidiscrete {T : ℝ} (S : HeatSolution b s T) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (v : Space n N) : ‖interp b s N (S.u t) - exp (t • lumpedLaplacian b hs N) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + t * S.defect N
  /-- backward Euler, `O(τ + h²)` in the maximum norm -/
  backwardEuler {T : ℝ} (S : HeatSolution b s T) {u₂ : ℝ → (Fin n → ℝ) → ℝ} {B₂ : ℝ}
    (hu₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, HasDerivAt (fun t => S.u₁ t x) (u₂ t x) t)
    (hB₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, |u₂ t x| ≤ B₂) (N : ℕ) {τ : ℝ} (hτ : 0 < τ)
    {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) :
    ‖interp b s N (S.u (k * τ)) - ((family b hs).res τ N ^ k) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * (3 / 2 * τ * B₂ + S.defect N)
  /-- Brenner–Thomée's stability bound for every A-stable rational scheme -/
  stable_rational {r : RationalScheme} (hr : r.IsAStable) (N : ℕ) {τ : ℝ} (hτ : 0 < τ) (k : ℕ) :
    ‖(family b hs).step r τ N ^ k‖ ≤ 1 + r.sqrtConst * √k
  /-- every A-stable rational scheme of order `p` against every classical solution -/
  rational {T : ℝ} (S : HeatSolution b s T) {r : RationalScheme} (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) (N : ℕ) {τ : ℝ} (hτ : 0 < τ) {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) :
    ‖interp b s N (S.u (k * τ)) - ((family b hs).step r τ N ^ k) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * S.defect N +
        r.sharpConst p * (k * τ) * τ ^ p * ‖(lumpedLaplacian b hs N ^ (p + 1)) v‖
  /-- the verdict of the Banach layer for the maximum-norm family (`M = 1`) -/
  banach : (family b hs).Verdict
  /-- the lumped mass is the integral of the hat function, `m(x) = ⟪φₓ, 1⟫_{L²(Q)}` -/
  lumpedMass_eq_inner (N : ℕ) (x : Fin n → ℝ) :
    ⟪(whitneyElement n).glue (freudenthalMesh b s hs (N + 1)) (0 : ℕ)
        (p1Global (freudenthalMesh b s hs (N + 1)) (nodalIndicator x) :
          (whitneyElement n).Piecewise (freudenthalMesh b s hs (N + 1)) 0),
      (whitneyElement n).glue (freudenthalMesh b s hs (N + 1)) (0 : ℕ)
        (p1Global (freudenthalMesh b s hs (N + 1)) (fun _ => 1) :
          (whitneyElement n).Piecewise (freudenthalMesh b s hs (N + 1)) 0)⟫_ℝ =
      lumpedMass (freudenthalMesh b s hs (N + 1)) x
  /-- the scheme is the lumped-mass Galerkin method on `P̊₁⁻Λ⁰` (`feFun_bijective`):
  `W = Lₕ U ⟺ (W, V)_h = -⟪d U_h, d V_h⟫_{L²Λ¹(Q)}` for all `V` -/
  galerkin (N : ℕ) (U W : Space n N) : lumpedLaplacian b hs N U = W ↔
    ∀ V : Space n N, lumpedInner b hs W V = -⟪dFeFun b hs U, dFeFun b hs V⟫_ℝ
  /-- the semidiscrete error of the finite element function at every point of `Q̄` -/
  semidiscrete_fe {T : ℝ} (S : HeatSolution b s T) {D₂ : ℝ}
    (hD₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, ∀ i k,
      |partialDeriv k (partialDeriv i (S.u t)) x| ≤ D₂) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (v : Space n N) {K : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hK : K ∈ (freudenthalMesh b s hs (N + 1)).simplices) {x : Fin n → ℝ}
    (hx : x ∈ K.closedInterior) :
    |S.u t x - p1Interp K.points (nodal b s (exp (t • lumpedLaplacian b hs N) v)) x| ≤
      ‖interp b s N (S.u 0) - v‖ + t * S.defect N + feDefect (s := s) (n := n) D₂ N
  /-- backward Euler: the error of the finite element function at every point of `Q̄` -/
  backwardEuler_fe {T : ℝ} (S : HeatSolution b s T) {D₂ : ℝ}
    (hD₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, ∀ i k,
      |partialDeriv k (partialDeriv i (S.u t)) x| ≤ D₂)
    {u₂ : ℝ → (Fin n → ℝ) → ℝ} {B₂ : ℝ}
    (hu₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, HasDerivAt (fun t => S.u₁ t x) (u₂ t x) t)
    (hB₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, |u₂ t x| ≤ B₂) (N : ℕ) {τ : ℝ} (hτ : 0 < τ)
    {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) {K : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hK : K ∈ (freudenthalMesh b s hs (N + 1)).simplices) {x : Fin n → ℝ}
    (hx : x ∈ K.closedInterior) :
    |S.u (k * τ) x - p1Interp K.points (nodal b s (((family b hs).res τ N ^ k) v)) x| ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * (3 / 2 * τ * B₂ + S.defect N) +
        feDefect (s := s) (n := n) D₂ N
  /-- every A-stable rational scheme: the error of the finite element function on `Q̄` -/
  rational_fe {T : ℝ} (S : HeatSolution b s T) {D₂ : ℝ}
    (hD₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, ∀ i k,
      |partialDeriv k (partialDeriv i (S.u t)) x| ≤ D₂)
    {r : RationalScheme} (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) (N : ℕ) {τ : ℝ}
    (hτ : 0 < τ) {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) {K : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hK : K ∈ (freudenthalMesh b s hs (N + 1)).simplices) {x : Fin n → ℝ}
    (hx : x ∈ K.closedInterior) :
    |S.u (k * τ) x - p1Interp K.points (nodal b s (((family b hs).step r τ N ^ k) v)) x| ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * S.defect N +
        r.sharpConst p * (k * τ) * τ ^ p * ‖(lumpedLaplacian b hs N ^ (p + 1)) v‖ +
        feDefect (s := s) (n := n) D₂ N
  /-- the simplices of the mesh cover `Q̄`, so the bounds of the finite element function on every
  simplex hold on all of `Q̄` -/
  covers (N : ℕ) {x : Fin n → ℝ} (hx : x ∈ closedCube b s) :
    ∃ K ∈ (freudenthalMesh b s hs (N + 1)).simplices, x ∈ K.closedInterior
  /-- `U ↦ U_h` is a bijection of `ℝ^{interior nodes}` onto `P̊₁⁻Λ⁰` -/
  feFun_bijective (N : ℕ) : Function.Bijective fun U : Space n N =>
    (⟨feFun b hs U, feFun_mem_globalSpace₀ b hs U⟩ :
      (whitneyElement n).globalSpace₀ (freudenthalMesh b s hs (N + 1)) 0)

/-- **The heat equation in the maximum norm** (lumped-mass `P₁` elements on the Freudenthal
meshes of the cube `b + (0, s)ⁿ`, Dirichlet data): see `Verdict`. [Thomee2006], Ch. 15;
[CiarletRaviart1973]; [BrennerThomee1979] -/
theorem maxNormHeat (b : Fin n → ℝ) (hs : 0 < s) : Verdict b hs where
  nonobtuse N _ := isNonobtuse_freudenthalMesh b hs N
  stencil := fun _ U p => lumpedLaplacian_apply b hs U p
  maximumPrinciple := isSubMarkovGenerator b hs
  consistency := @fun N _ hu _ hB hbd => norm_interp_laplacian_sub_le hs N hu hB hbd
  semidiscrete := @fun _ S N _ ht v => norm_interp_sub_exp_le hs S N ht v
  backwardEuler := @fun _ S _ _ hu₂ hB₂ N _ hτ _ hk v =>
    norm_interp_sub_res_pow_le hs S hu₂ hB₂ N hτ hk v
  stable_rational := @fun _ hr N _ hτ k => norm_step_pow_le hs hr N hτ k
  rational := @fun _ S _ hr _ hp N _ hτ _ hk v => norm_interp_sub_step_pow_le hs S hr hp N hτ hk v
  banach := stableFamily _
  lumpedMass_eq_inner N x := inner_glue_p1Global_nodalIndicator_one _
    (fun _ hT => interior_subset_freudenthalMesh_domain b hs (N + 1) hT) x
  galerkin _ U W := lumpedLaplacian_eq_iff b hs U W
  semidiscrete_fe S _ hD₂ N _ ht v _ hK _ hx :=
    (abs_sub_p1Interp_nodal_le hs N ((S.contDiff _ ht).of_le (by norm_num)) (hD₂ _ ht)
      (S.boundary _ ht) _ hK hx).trans (add_le_add (norm_interp_sub_exp_le hs S N ht v) le_rfl)
  backwardEuler_fe S _ hD₂ _ _ hu₂ hB₂ N τ hτ k hk v _ hK _ hx :=
    have hkt : (k : ℝ) * τ ∈ Set.Icc 0 _ := ⟨by positivity, hk⟩
    (abs_sub_p1Interp_nodal_le hs N ((S.contDiff _ hkt).of_le (by norm_num)) (hD₂ _ hkt)
      (S.boundary _ hkt) _ hK hx).trans
      (add_le_add (norm_interp_sub_res_pow_le hs S hu₂ hB₂ N hτ hk v) le_rfl)
  rational_fe S _ hD₂ _ hr _ hp N τ hτ k hk v _ hK _ hx :=
    have hkt : (k : ℝ) * τ ∈ Set.Icc 0 _ := ⟨by positivity, hk⟩
    (abs_sub_p1Interp_nodal_le hs N ((S.contDiff _ hkt).of_le (by norm_num)) (hD₂ _ hkt)
      (S.boundary _ hkt) _ hK hx).trans
      (add_le_add (norm_interp_sub_step_pow_le hs S hr hp N hτ hk v) le_rfl)
  covers _ _ hx := exists_simplex_mem hs hx
  feFun_bijective N := (feEquiv b hs N).bijective

/-- The second time derivative of the first eigenmode: `uₜₜ = λ² u`, `λ = n (π/s)²`. -/
theorem sineSolution_hasDerivAt₁ (b : Fin n → ℝ) (hs : 0 < s) (T t : ℝ) (x : Fin n → ℝ) :
    HasDerivAt (fun t => (sineSolution b hs T).u₁ t x)
      ((n * sineFreq s ^ 2) ^ 2 * (sineSolution b hs T).u t x) t := by
  have := (((Real.hasDerivAt_exp _).comp t
    ((hasDerivAt_id t).const_mul (-(n * sineFreq s ^ 2)))).mul_const
    (∏ j, sineDeriv (sineFreq s) (b j) 0 (x j))).const_mul (-(n * sineFreq s ^ 2))
  exact this.congr_deriv (by simp [sineSolution]; ring)

/-- `|uₜₜ| ≤ λ²` for the first eigenmode, `t ≥ 0`. -/
theorem abs_sineSolution_u₂_le (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (x : Fin n → ℝ) :
    |(n * sineFreq s ^ 2) ^ 2 * (sineSolution b hs T).u t x| ≤ (n * sineFreq s ^ 2) ^ 2 := by
  have h1 : Real.exp (-(n * sineFreq s ^ 2) * t) ≤ 1 :=
    Real.exp_le_one_iff.2 (by rw [neg_mul]; exact neg_nonpos.2 (mul_nonneg (by positivity) ht))
  have h2 : ∏ j, |sineDeriv (sineFreq s) (b j) 0 (x j)| ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => Real.abs_sin_le_one _
  simp only [sineSolution, abs_mul, abs_of_pos (Real.exp_pos _), Finset.abs_prod,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n * sineFreq s ^ 2) ^ 2)]
  calc (n * sineFreq s ^ 2) ^ 2 *
        (Real.exp (-(n * sineFreq s ^ 2) * t) * ∏ j, |sineDeriv (sineFreq s) (b j) 0 (x j)|)
      ≤ (n * sineFreq s ^ 2) ^ 2 * (1 * 1) := by gcongr
    _ = _ := by ring

/-- **The verdict is not vacuous**: the first eigenmode `sineSolution` is a classical solution
on every `[0, T] × Q`, nonzero at `t = 0`, with `uₜₜ = λ² u`, `|uₜₜ| ≤ λ²`; so the semidiscrete,
backward Euler (its extra hypotheses on `uₜₜ` hold) and rational clauses all apply to it. -/
theorem maxNormHeat_nonvacuous (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) :
    Verdict b hs ∧ ∃ S : HeatSolution b s T, S.u 0 ≠ 0 ∧
      (∃ (u₂ : ℝ → (Fin n → ℝ) → ℝ) (B₂ : ℝ),
        (∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, HasDerivAt (fun t => S.u₁ t x) (u₂ t x) t) ∧
        ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, |u₂ t x| ≤ B₂) ∧
      ∃ D₂ : ℝ, ∀ t ∈ Icc 0 T, ∀ x ∈ closedCube b s, ∀ i k,
        |partialDeriv k (partialDeriv i (S.u t)) x| ≤ D₂ :=
  ⟨maxNormHeat b hs, sineSolution b hs T, fun h => by
    have := congrFun h (b + (s / 2) • fun _ => (1 : ℝ))
    rw [sineSolution_u_zero_center] at this
    exact one_ne_zero this,
    ⟨fun t x => (n * sineFreq s ^ 2) ^ 2 * (sineSolution b hs T).u t x, (n * sineFreq s ^ 2) ^ 2,
      fun t _ x _ => sineSolution_hasDerivAt₁ b hs T t x,
      fun t ht x _ => abs_sineSolution_u₂_le b hs T ht.1 x⟩,
    sineFreq s ^ 2, fun t ht x _ i k =>
      abs_partialDeriv_partialDeriv_sineSolution_le b hs T ht.1 x i k⟩

end Feec.Models.Cube.MaxNormHeat
