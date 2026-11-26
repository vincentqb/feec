module

public import Feec.FiniteElement.NonobtuseHeat
public import Feec.ForMathlib.Analysis.FiniteDifference
public import Feec.ForMathlib.Calculus.Partial
public import Feec.ForMathlib.Calculus.SecondDifference
public import Feec.Models.Cube.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The heat equation in the maximum norm: lumped-mass `P₁` elements on Freudenthal meshes

Lumped-mass `P₁` elements on the Freudenthal meshes of `Q = b + (0, s)ⁿ` for the heat equation with
Dirichlet data: a discrete maximum principle and maximum-norm error estimates.

## Main results

* `MaxNormHeat.maxNormHeat`: the stencil, the maximum principle, consistency and the errors.
* `MaxNormHeat.maxNormHeat_nonvacuous`: some nonzero classical solution meets the hypotheses.

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006]
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

/-- **The Freudenthal meshes with their interior nodes**, a family of non-obtuse meshes. -/
abbrev meshes (b : Fin n → ℝ) (hs : 0 < s) : NonobtuseMeshes n ℕ where
  mesh N := freudenthalMesh b s hs (N + 1)
  Node N := Nodes n N
  x N q := node b (meshSize s N) q
  injective N := node_injective_subtype b (meshSize_pos hs N).ne' _
  isNonobtuse N := isNonobtuse_freudenthalMesh b hs (N + 1)

/-- **The lumped-mass `P₁` Laplacian** `Lₕ = -M_L⁻¹ K`, homogeneous Dirichlet data. -/
def lumpedLaplacian (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) : Space n N →L[ℝ] Space n N :=
  (meshes b hs).L N

theorem lumpedLaplacian_apply_eq (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) (p : Nodes n N) :
    lumpedLaplacian b hs N U p =
      -p1Stiffness (freudenthalMesh b s hs (N + 1)) (nodalIndicator (node b (meshSize s N) p))
        (nodal b s U) / lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p) :=
  lumpedLaplacianOn_apply _ _ U p

/-- **The stencil**: `Lₕ` is the difference Laplacian ([Thomee2006], Ch. 15). -/
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

/-- **The discrete maximum principle**: `Lₕ` is a sub-Markov generator ([CiarletRaviart1973]). -/
theorem isSubMarkovGenerator (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    IsSubMarkovGenerator (lumpedLaplacian b hs N) :=
  (meshes b hs).isSubMarkovGenerator N

/-! ### Consistency -/

/-- The nodal interpolant `(Iₕ u)(p) = u(b + h p)` at the interior nodes. -/
def interp (b : Fin n → ℝ) (s : ℝ) (N : ℕ) (u : (Fin n → ℝ) → ℝ) : Space n N :=
  fun p => u (node b (meshSize s N) p)

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

theorem node_mem_openCube (hs : 0 < s) (p : Nodes n N) :
    node b (meshSize s N) p ∈ openCube b s :=
  (node_mem_openCube_iff hs).2 p.2

theorem zeroExt_interp (hs : 0 < s) {u : (Fin n → ℝ) → ℝ}
    (hbd : ∀ x ∈ closedCube b s, x ∉ openCube b s → u x = 0) {q : Fin n → ℤ}
    (hq : ∀ j, 0 ≤ q j ∧ q j ≤ N + 1) :
    zeroExt (interp b s N u) q = u (node b (meshSize s N) q) := by
  simp only [zeroExt, interp]
  split_ifs with hq'
  · rfl
  · exact (hbd _ ((node_mem_closedCube_iff hs).2 hq) fun ho =>
      hq' ((node_mem_openCube_iff hs).1 ho)).symm

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

/-- The **global `P₁` function** `U_h` of the discrete values `U`, `0` at the boundary nodes. -/
def feFun (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) :
    (whitneyElement n).globalSpace (freudenthalMesh b s hs (N + 1)) 0 :=
  p1Global _ (nodal b s U)

/-- `d U_h ∈ L²Λ¹(Q)`, the elementwise exterior derivative. -/
def dFeFun (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) :
    Feec.Domain.L2F ℝ (freudenthalMesh b s hs (N + 1)).domain
      (Feec.Domain.formIdx n (((0 : ℕ) : ℤ) + 1)) :=
  (whitneyElement n).glue _ (((0 : ℕ) : ℤ) + 1) ((whitneyElement n).dPiecewise _ 0
    (feFun b hs U : (whitneyElement n).Piecewise (freudenthalMesh b s hs (N + 1)) 0))

/-- The **lumped-mass inner product** `(U, V)_h = Σ_p m(p) U(p) V(p)`. -/
def lumpedInner (b : Fin n → ℝ) (hs : 0 < s) (U V : Space n N) : ℝ :=
  ∑ p : Nodes n N, lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p) *
    U p * V p

theorem lumpedMass_node_pos (b : Fin n → ℝ) (hs : 0 < s) (p : Nodes n N) :
    0 < lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p) := by
  have := lumpedMass_freudenthalMesh b hs (N + 1) p.2
  rw [meshSize, this]
  exact pow_pos (meshSize_pos hs N) n

theorem lumpedInner_lumpedLaplacian (b : Fin n → ℝ) (hs : 0 < s) (U V : Space n N) :
    lumpedInner b hs (lumpedLaplacian b hs N U) V =
      -p1Stiffness (freudenthalMesh b s hs (N + 1)) (nodal b s U) (nodal b s V) := by
  rw [p1Stiffness_comm, nodal, nodalFun_eq_sum _ V, p1Stiffness_sum_smul, lumpedInner,
    ← sum_neg_distrib]
  refine sum_congr rfl fun p _ => ?_
  rw [lumpedLaplacian_apply_eq]
  have := (lumpedMass_node_pos b hs p).ne'
  field_simp

theorem lumpedInner_lumpedLaplacian_eq_neg_inner (b : Fin n → ℝ) (hs : 0 < s) (U V : Space n N) :
    lumpedInner b hs (lumpedLaplacian b hs N U) V = -⟪dFeFun b hs U, dFeFun b hs V⟫_ℝ := by
  rw [lumpedInner_lumpedLaplacian, dFeFun, dFeFun, feFun, feFun,
    inner_glue_dPiecewise_p1Global _ (fun T hT =>
      interior_subset_freudenthalMesh_domain b hs (N + 1) hT)]

/-- **`Lₕ` is determined by the Galerkin equations**: `W = Lₕ U` iff
`(W, V)_h = -⟪d U_h, d V_h⟫` for every `V` ([Thomee2006], Ch. 15). -/
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

/-- **The nodal values are a linear isomorphism `ℝ^{interior nodes} ≃ P̊₁⁻Λ⁰`**, `U ↦ U_h`. -/
def feEquiv (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    Space n N ≃ₗ[ℝ] (whitneyElement n).globalSpace₀ (freudenthalMesh b s hs (N + 1)) 0 :=
  p1GlobalEquiv₀ _ (isFreeVertexEnum b hs N)

theorem feEquiv_apply (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) :
    (feEquiv b hs N U : (whitneyElement n).Piecewise (freudenthalMesh b s hs (N + 1)) 0) =
      feFun b hs U := rfl

theorem feFun_mem_globalSpace₀ (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) :
    (feFun b hs U : (whitneyElement n).Piecewise (freudenthalMesh b s hs (N + 1)) 0) ∈
      (whitneyElement n).globalSpace₀ (freudenthalMesh b s hs (N + 1)) 0 :=
  (feEquiv b hs N U).2

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

/-- **The maximum-norm family** of the `Lₕ`, uniformly stable with `M = 1`. -/
abbrev family (b : Fin n → ℝ) (hs : 0 < s) : StableFamily ℝ ℕ :=
  (meshes b hs).family

@[simp] theorem family_M (b : Fin n → ℝ) (hs : 0 < s) : (family b hs).M = 1 := rfl

@[simp] theorem family_L (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    (family b hs).L N = lumpedLaplacian b hs N := rfl

/-- A **classical solution of the heat equation** `uₜ = Δu` on `[0, T] × Q`, `u = 0` on `∂Q`,
`C⁴` in space. -/
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

theorem norm_defect_le (hs : 0 < s) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖interp b s N (S.u₁ t) - lumpedLaplacian b hs N (interp b s N (S.u t))‖ ≤ S.defect N := by
  have e : interp b s N (S.u₁ t) = interp b s N (laplacian (S.u t)) :=
    funext fun p => S.heat t ht _ (node_mem_openCube hs p)
  rw [e]
  exact norm_interp_laplacian_sub_le hs N (S.contDiff t ht) (S.bound₄ t ht) (S.boundary t ht)

end HeatSolution

theorem norm_interp_sub_exp_le (hs : 0 < s) {T : ℝ} (S : HeatSolution b s T) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) (v : Space n N) :
    ‖interp b s N (S.u t) - exp (t • lumpedLaplacian b hs N) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + t * S.defect N := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  exact (meshes b hs).norm_interp_sub_exp_le N ht.1
    (fun r hr q => S.hasDerivAt r (hsub hr) _ (node_mem_openCube hs q))
    (fun r hr => S.norm_defect_le hs N (hsub hr)) v

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

theorem norm_step_pow_le (hs : 0 < s) {r : RationalScheme} (hr : r.IsAStable) (N : ℕ) {τ : ℝ}
    (hτ : 0 < τ) (k : ℕ) : ‖(family b hs).step r τ N ^ k‖ ≤ 1 + r.sqrtConst * √k :=
  (meshes b hs).norm_step_pow_le hr hτ N k

/-! ### A classical solution: the first eigenmode -/

/-- The frequency `a = π / s` of the first Dirichlet eigenmode of the cube. -/
def sineFreq (s : ℝ) : ℝ := Real.pi / s

/-- The factor `y ↦ sin(a (y - c))` and its derivatives `aᵏ sin⁽ᵏ⁾(a (y - c))`, `k ≤ 4`. -/
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

theorem prod_update_const_mul (G : Fin n → ℝ → ℝ) (i : Fin n) (κ : ℝ) (x : Fin n → ℝ) :
    ∏ j, Function.update G i (fun y => κ * G i y) j (x j) = κ * ∏ j, G j (x j) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem partialDeriv_partialDeriv_sineProd (b : Fin n → ℝ) (a c : ℝ) (i : Fin n) :
    partialDeriv i (partialDeriv i fun x : Fin n → ℝ => c * ∏ j, sineDeriv a (b j) 0 (x j)) =
      fun x => -a ^ 2 * c * ∏ j, sineDeriv a (b j) 0 (x j) := by
  funext x
  have := congrFun (iterate_partialDeriv_sine b a c i 2 (by omega)) x
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id] at this
  rw [this, sineFactors, show sineDeriv a (b i) 2 =
    fun y => -a ^ 2 * sineDeriv a (b i) 0 y from rfl,
    prod_update_const_mul (fun j => sineDeriv a (b j) 0)]
  ring

theorem sineDeriv_zero_two_mul_sub (a c y : ℝ) :
    sineDeriv a c 0 (2 * c - y) = -sineDeriv a c 0 y := by
  simp only [sineDeriv]
  rw [show a * (2 * c - y - c) = -(a * (y - c)) by ring, Real.sin_neg]

theorem hasDerivAt_sineMode (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) :
    HasDerivAt (fun t => Real.exp (-(n * sineFreq s ^ 2) * t) *
        ∏ j, sineDeriv (sineFreq s) (c j) 0 (x j))
      (-(n * sineFreq s ^ 2) * (Real.exp (-(n * sineFreq s ^ 2) * t) *
        ∏ j, sineDeriv (sineFreq s) (c j) 0 (x j))) t := by
  have := ((Real.hasDerivAt_exp _).comp t
    ((hasDerivAt_id t).const_mul (-(n * sineFreq s ^ 2)))).mul_const
    (∏ j, sineDeriv (sineFreq s) (c j) 0 (x j))
  exact this.congr_deriv (by simp; ring)

theorem laplacian_sineMode (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) :
    laplacian (fun x : Fin n → ℝ => Real.exp (-(n * sineFreq s ^ 2) * t) *
        ∏ j, sineDeriv (sineFreq s) (c j) 0 (x j)) x =
      -(n * sineFreq s ^ 2) * (Real.exp (-(n * sineFreq s ^ 2) * t) *
        ∏ j, sineDeriv (sineFreq s) (c j) 0 (x j)) := by
  have e : ∀ i, partialDeriv i (partialDeriv i (fun x : Fin n → ℝ =>
      Real.exp (-(n * sineFreq s ^ 2) * t) * ∏ j, sineDeriv (sineFreq s) (c j) 0 (x j))) x =
      -sineFreq s ^ 2 * (Real.exp (-(n * sineFreq s ^ 2) * t) *
        ∏ j, sineDeriv (sineFreq s) (c j) 0 (x j)) := fun i =>
    (congrFun (partialDeriv_partialDeriv_sineProd c _ _ i) x).trans (by ring)
  simp only [laplacian, e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

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

/-- **The first eigenmode** `u(t, x) = e^{-λt} ∏ᵢ sin(π (xᵢ - bᵢ)/s)`, `λ = n π² / s²`. -/
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

theorem exists_node_eq_points (hs : 0 < s) {K : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hK : K ∈ (freudenthalMesh b s hs (N + 1)).simplices) (j : Fin (n + 1)) :
    ∃ q : Fin n → ℤ, (∀ i, 0 ≤ q i ∧ q i ≤ N + 1) ∧ K.points j = node b (meshSize s N) q := by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hK
  rw [mapEquiv_boxMap_freudenthalSimplex_points, freudenthalPoints_eq_node]
  refine ⟨_, fun i => ?_, rfl⟩
  have h1 := (m i).2
  rcases kuhnLattice_mem σ j i with h | h <;>
    simp only [Pi.add_apply, h, finLattice] <;> omega


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

/-- The conclusions of `maxNormHeat` for the cube `b + (0, s)ⁿ`. -/
structure Verdict (b : Fin n → ℝ) (hs : 0 < s) : Prop where
  /-- the Freudenthal meshes are non-obtuse -/
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
  /-- the scheme is the lumped-mass Galerkin method on `P̊₁⁻Λ⁰` -/
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
  /-- the simplices of the mesh cover `Q̄` -/
  covers (N : ℕ) {x : Fin n → ℝ} (hx : x ∈ closedCube b s) :
    ∃ K ∈ (freudenthalMesh b s hs (N + 1)).simplices, x ∈ K.closedInterior
  /-- `U ↦ U_h` is a bijection of `ℝ^{interior nodes}` onto `P̊₁⁻Λ⁰` -/
  feFun_bijective (N : ℕ) : Function.Bijective fun U : Space n N =>
    (⟨feFun b hs U, feFun_mem_globalSpace₀ b hs U⟩ :
      (whitneyElement n).globalSpace₀ (freudenthalMesh b s hs (N + 1)) 0)

/-- **The heat equation in the maximum norm**: `Verdict` on the cube `b + (0, s)ⁿ` ([Thomee2006],
Ch. 15; [CiarletRaviart1973]; [BrennerThomee1979]). -/
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

theorem sineSolution_hasDerivAt₁ (b : Fin n → ℝ) (hs : 0 < s) (T t : ℝ) (x : Fin n → ℝ) :
    HasDerivAt (fun t => (sineSolution b hs T).u₁ t x)
      ((n * sineFreq s ^ 2) ^ 2 * (sineSolution b hs T).u t x) t := by
  have := (((Real.hasDerivAt_exp _).comp t
    ((hasDerivAt_id t).const_mul (-(n * sineFreq s ^ 2)))).mul_const
    (∏ j, sineDeriv (sineFreq s) (b j) 0 (x j))).const_mul (-(n * sineFreq s ^ 2))
  exact this.congr_deriv (by simp [sineSolution]; ring)

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

/-- **The verdict is not vacuous**: a nonzero classical solution has bounded `uₜₜ` and `∂ᵢ∂ₖ u`. -/
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
