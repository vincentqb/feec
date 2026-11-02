module

public import Feec.FiniteElement.LumpedMass
public import Feec.TimeStepping.StableFamily
public import Feec.ForMathlib.Analysis.SubMarkov
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
symmetric negative definite difference Laplacian, so `e^{tLₕ}` is also a contraction in `ℓ²`; the
Hilbert route reaches the maximum norm only through the norm equivalence, with a factor
`h^{-n/2}`. The Banach layer (`Feec.TimeStepping.stableFamily`, the discrete half of
`Feec.TimeStepping.banachFEEC`) gives the maximum-norm theory with constants independent of `h`.

With the stencil theorem the scheme is exactly the classical finite difference scheme for the
heat equation; the stiffness form `Feec.FiniteElement.p1Stiffness` is the elementwise assembly
of `∫_T ∇Πₜu · ∇Πₜw`, and is not proved equal to `∫_Q ∇u_h · ∇w_h` for the global conforming
`P₁` (Whitney `0`-form) functions of `Feec.FiniteElement.WhitneyComplex`.

The discrete space is `ℝ^{interior nodes}` with the maximum norm (`MaxNormHeat.Space N`). The
discrete Laplacian `Lₕ = -M_L⁻¹ K` (`MaxNormHeat.lumpedLaplacian`) is defined from the `P₁`
stiffness form and the lumped mass of the mesh (`Feec.FiniteElement.p1Stiffness`,
`Feec.FiniteElement.lumpedMass`), the nodal values extended by `0` to the boundary nodes.

## Main results

**`MaxNormHeat.maxNormHeat`** (statement `MaxNormHeat.Verdict`):

1. (**the stencil**, `lumpedLaplacian_apply`) the Freudenthal simplices are non-obtuse, so the
   stiffness matrix has nonpositive off-diagonal entries (Ciarlet–Raviart), and `Lₕ` is the
   `(2n + 1)`-point difference Laplacian
   `(Lₕ U)(p) = Σₗ (U(p + eₗ) - 2 U(p) + U(p - eₗ)) / h²` (`U = 0` at the boundary nodes);
2. (**the discrete maximum principle**, `isSubMarkovGenerator`) `Lₕ` is a sub-Markov generator:
   `e^{tLₕ}` is positive and contractive in the maximum norm, `-a ≤ v ≤ a ⇒ -a ≤ e^{tLₕ} v ≤ a`;
3. (**consistency**, `norm_interp_laplacian_sub_le`) for `u ∈ C⁴` vanishing on `∂Q` with
   `|∂ᵢ⁴ u| ≤ B` on `Q̄`, `‖Iₕ Δu - Lₕ Iₕ u‖_∞ ≤ n B h² / 12` (`Iₕ` the nodal interpolant);
4. (**semidiscrete error**) for every classical solution `u` on `[0, T]` (`HeatSolution`:
   `C⁴` in space with `|∂ᵢ⁴ u| ≤ B₄`, `uₜ = Δu`, `u = 0` on `∂Q`),
   `‖Iₕ u(t) - e^{tLₕ} v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + t n B₄ h² / 12`;
5. (**backward Euler**) with `|uₜₜ| ≤ B₂`,
   `‖Iₕ u(kτ) - (1 - τLₕ)⁻ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ (3/2 τ B₂ + n B₄ h² / 12)`:
   `O(τ + h²)` in the maximum norm, unconditionally;
6. (**every A-stable rational scheme**, Crank–Nicolson and the Gauss and Radau methods among
   them) Brenner–Thomée's stability bound `‖r(τLₕ)ᵏ‖_∞ ≤ 1 + C'_r √k`, and for `r` of order `p`
   `‖Iₕ u(kτ) - r(τLₕ)ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ n B₄ h² / 12 + C_r kτ τᵖ ‖Lₕ^{p+1} v‖_∞`
   (the sharp smooth-data estimate; the factor `‖Lₕ^{p+1} v‖_∞` is that of the discrete datum);
7. the full verdict of the Banach layer for the family (`StableFamily.Verdict`).

Among the fully discrete results only 5 is uniform in `h` with the constants of `u` alone; in 6
the factor `‖Lₕ^{p+1} v‖_∞` is not bounded uniformly in `h`, and the uniform route through the
stability bound loses `√k` (no `‖r(τLₕ)ᵏ‖_∞ ≤ C` uniform in `k` and `h` is proved). The
estimates are in the maximum norm at the nodes. `sineSolution` is a nonzero classical solution
(`exp(-λt) ∏ᵢ sin(π(xᵢ - bᵢ)/s)`), so the hypotheses of 4–6 are satisfied
(`maxNormHeat_nonvacuous`).

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
  (the lumped mass method, the maximum principle and maximum-norm estimates)
* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set Finset NormedSpace Feec.Mesh Feec.FiniteElement Feec.TimeStepping
open Feec.Models.Cube.Geometry (openCube)

@[expose] public noncomputable section

namespace Feec.Models.Cube.MaxNormHeat

variable {n : ℕ} {b : Fin n → ℝ} {s : ℝ}

/-! ### The discrete Laplacian -/

/-- The mesh size `h = s / (N + 1)` of the level-`(N + 1)` Freudenthal mesh. -/
def meshSize (s : ℝ) (N : ℕ) : ℝ := s / (N + 1 : ℕ)

theorem meshSize_pos (hs : 0 < s) (N : ℕ) : 0 < meshSize s N := freudenthalScale_pos hs (N + 1)

/-- The interior nodes of the level-`(N + 1)` lattice. -/
abbrev Nodes (n N : ℕ) := ↥(interiorNodes n (N + 1))

/-- The discrete space: nodal values at the interior nodes, with the maximum norm. -/
abbrev Space (n N : ℕ) := Nodes n N → ℝ

variable {N : ℕ}

/-- The extension of discrete values by `0` to the lattice. -/
def ext (U : Space n N) (q : Fin n → ℤ) : ℝ :=
  if h : q ∈ interiorNodes n (N + 1) then U ⟨q, h⟩ else 0

/-- The nodal function on `ℝⁿ` with values `U` at the interior nodes and `0` elsewhere. -/
def nodal (b : Fin n → ℝ) (s : ℝ) (U : Space n N) : (Fin n → ℝ) → ℝ :=
  fun x => ∑ q : Nodes n N, if node b (meshSize s N) q = x then U q else 0

theorem nodal_node (hs : 0 < s) (U : Space n N) (q : Fin n → ℤ) :
    nodal b s U (node b (meshSize s N) q) = ext U q := by
  have hinj := node_injective b (meshSize_pos hs N).ne'
  simp only [nodal, hinj.eq_iff, ext]
  split_ifs with hq
  · rw [Finset.sum_eq_single ⟨q, hq⟩]
    · simp
    · intro c _ hc; rw [ite_eq_right]; intro e; exact hc (Subtype.ext e)
    · simp
  · exact sum_eq_zero fun c _ => by
      rw [ite_eq_right]; rintro rfl; exact hq c.2

/-- The **lumped-mass `P₁` Laplacian** `-M_L⁻¹ K` before linearity is proved. -/
def lumpedLaplacianFun (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) : Space n N := fun p =>
  -p1Stiffness (freudenthalMesh b s hs (N + 1)) (nodalIndicator (node b (meshSize s N) p))
    (nodal b s U) / lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p)

/-- **The stencil**: the lumped-mass `P₁` Laplacian is the `(2n + 1)`-point difference
Laplacian. -/
theorem lumpedLaplacianFun_apply (hs : 0 < s) (U : Space n N) (p : Nodes n N) :
    lumpedLaplacianFun b hs U p = ∑ l, (ext U ((p : Fin n → ℤ) + Pi.single l 1) - 2 * U p +
      ext U ((p : Fin n → ℤ) - Pi.single l 1)) / meshSize s N ^ 2 := by
  rw [lumpedLaplacianFun, meshSize]
  rw [neg_p1Stiffness_div_lumpedMass b hs (N + 1) p.2]
  refine sum_congr rfl fun l _ => ?_
  have e := nodal_node (b := b) hs U
  simp only [meshSize] at e
  rw [e, e, e]
  congr 2
  simp [ext, p.2]

/-- **The lumped-mass `P₁` Laplacian** `Lₕ = -M_L⁻¹ K` on the level-`(N + 1)` Freudenthal mesh of
`b + (0, s)ⁿ`, with homogeneous Dirichlet data: `(Lₕ U)(p) = -a(φₚ, U) / m(p)`. -/
def lumpedLaplacian (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) : Space n N →L[ℝ] Space n N :=
  LinearMap.toContinuousLinearMap
    { toFun := lumpedLaplacianFun b hs
      map_add' := fun U V => by
        funext p
        simp only [lumpedLaplacianFun_apply, Pi.add_apply, ← sum_add_distrib]
        refine sum_congr rfl fun l _ => ?_
        simp only [ext, Pi.add_apply]; split_ifs <;> ring
      map_smul' := fun c U => by
        funext p
        simp only [lumpedLaplacianFun_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          mul_sum]
        refine sum_congr rfl fun l _ => ?_
        simp only [ext, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring }

/-- **The stencil** (`Lₕ` is the difference Laplacian). [Thomee2006], Ch. 15 -/
theorem lumpedLaplacian_apply (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) (p : Nodes n N) :
    lumpedLaplacian b hs N U p = ∑ l, (ext U ((p : Fin n → ℤ) + Pi.single l 1) - 2 * U p +
      ext U ((p : Fin n → ℤ) - Pi.single l 1)) / meshSize s N ^ 2 :=
  lumpedLaplacianFun_apply hs U p

theorem lumpedLaplacian_apply_eq (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) (p : Nodes n N) :
    lumpedLaplacian b hs N U p =
      -p1Stiffness (freudenthalMesh b s hs (N + 1)) (nodalIndicator (node b (meshSize s N) p))
        (nodal b s U) / lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p) :=
  rfl

/-- **The discrete maximum principle**: `Lₕ` is a sub-Markov generator (`Lₕ + 2n/h²` is positive
and `Lₕ 𝟙 ≤ 0`), so `e^{tLₕ}` is positive and contractive in the maximum norm.
[CiarletRaviart1973]; [Thomee2006], Ch. 15 -/
theorem isSubMarkovGenerator (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    IsSubMarkovGenerator (lumpedLaplacian b hs N) where
  exists_shift := by
    refine ⟨2 * n / meshSize s N ^ 2, by positivity, fun U hU p => ?_⟩
    have hext : ∀ q, 0 ≤ ext U q := fun q => by
      simp only [ext]; split_ifs; exacts [hU _, le_rfl]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lumpedLaplacian_apply, Pi.zero_apply]
    have e : ∑ l, (ext U ((p : Fin n → ℤ) + Pi.single l 1) - 2 * U p +
          ext U ((p : Fin n → ℤ) - Pi.single l 1)) / meshSize s N ^ 2 +
          2 * n / meshSize s N ^ 2 * U p =
        ∑ l, (ext U ((p : Fin n → ℤ) + Pi.single l 1) + ext U ((p : Fin n → ℤ) - Pi.single l 1)) /
          meshSize s N ^ 2 := by
      have : 2 * n / meshSize s N ^ 2 * U p = ∑ _l : Fin n, 2 * U p / meshSize s N ^ 2 := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      rw [this, ← sum_add_distrib]
      refine sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact sum_nonneg fun l _ => div_nonneg (add_nonneg (hext _) (hext _)) (sq_nonneg _)
  apply_one_nonpos p := by
    rw [lumpedLaplacian_apply]
    refine sum_nonpos fun l _ => div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    have h1 : ∀ q : Fin n → ℤ, ext (fun _ => (1 : ℝ)) (N := N) q ≤ 1 := fun q => by
      simp only [ext]; split_ifs <;> norm_num
    linarith [h1 ((p : Fin n → ℤ) + Pi.single l 1), h1 ((p : Fin n → ℤ) - Pi.single l 1)]

/-! ### Consistency -/

/-- The Laplacian `Δu = Σᵢ ∂ᵢ∂ᵢ u`. -/
def laplacian (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, partialDeriv i (partialDeriv i u) x

/-- The closed cube `b + [0, s]ⁿ`. -/
def closedCube (b : Fin n → ℝ) (s : ℝ) : Set (Fin n → ℝ) := univ.pi fun i => Icc (b i) (b i + s)


/-- The nodal interpolant `(Iₕ u)(p) = u(b + h p)` at the interior nodes. -/
def interp (b : Fin n → ℝ) (s : ℝ) (N : ℕ) (u : (Fin n → ℝ) → ℝ) : Space n N :=
  fun p => u (node b (meshSize s N) p)

theorem meshSize_mul (s : ℝ) (N : ℕ) : meshSize s N * (N + 1 : ℕ) = s := by
  rw [meshSize, div_mul_cancel₀]; positivity

theorem mem_interiorNodes {N : ℕ} {p : Fin n → ℤ} :
    p ∈ interiorNodes n (N + 1) ↔ ∀ j, 1 ≤ p j ∧ p j ≤ N := by
  rw [interiorNodes, Fintype.mem_piFinset]
  refine forall_congr' fun j => ?_
  rw [Finset.mem_Ioo]; push_cast; omega

/-- The segments `x ± t eₗ`, `|t| ≤ h`, through an interior node lie in the closed cube. -/
theorem node_add_smul_mem_closedCube (hs : 0 < s) (p : Nodes n N) (l : Fin n) {t : ℝ}
    (ht : t ∈ Icc (-meshSize s N) (meshSize s N)) :
    node b (meshSize s N) p + t • Pi.single l 1 ∈ closedCube b s := by
  have hp := mem_interiorNodes.1 p.2
  have hh := (meshSize_pos hs N).le
  have hm := meshSize_mul s N
  intro j _
  have h1 : (1 : ℝ) ≤ (p : Fin n → ℤ) j := by exact_mod_cast (hp j).1
  have h2 : ((p : Fin n → ℤ) j : ℝ) ≤ N := by exact_mod_cast (hp j).2
  push_cast at hm
  simp only [node, Pi.add_apply, Pi.smul_apply, latticePoint_apply, smul_eq_mul, Set.mem_Icc]
  by_cases hj : j = l
  · subst hj
    simp only [Pi.single_eq_same, mul_one]
    constructor <;> nlinarith [ht.1, ht.2]
  · simp only [Pi.single_eq_of_ne hj, mul_zero, add_zero]
    constructor <;> nlinarith

/-- Interior nodes lie in the open cube. -/
theorem node_mem_openCube (hs : 0 < s) (p : Nodes n N) :
    node b (meshSize s N) p ∈ openCube b s := by
  have hp := mem_interiorNodes.1 p.2
  have hh := meshSize_pos hs N
  have hm := meshSize_mul s N
  push_cast at hm
  intro j _
  have h1 : (1 : ℝ) ≤ (p : Fin n → ℤ) j := by exact_mod_cast (hp j).1
  have h2 : ((p : Fin n → ℤ) j : ℝ) ≤ N := by exact_mod_cast (hp j).2
  simp only [node, Pi.add_apply, Pi.smul_apply, latticePoint_apply, smul_eq_mul, Set.mem_Ioo]
  constructor <;> nlinarith

/-- The extension by `0` of the interpolant of `u`, `u = 0` on `∂Q`, is `u` at every node of the
closed lattice. -/
theorem ext_interp (hs : 0 < s) {u : (Fin n → ℝ) → ℝ}
    (hbd : ∀ x ∈ closedCube b s, x ∉ openCube b s → u x = 0) {q : Fin n → ℤ}
    (hq : ∀ j, 0 ≤ q j ∧ q j ≤ N + 1) : ext (interp b s N u) q = u (node b (meshSize s N) q) := by
  have hh := meshSize_pos hs N
  have hm := meshSize_mul s N
  push_cast at hm
  simp only [ext, interp]
  split_ifs with hq'
  · rfl
  · symm
    have hc : node b (meshSize s N) q ∈ closedCube b s := fun j _ => by
      have h1 : (0 : ℝ) ≤ q j := by exact_mod_cast (hq j).1
      have h2 : (q j : ℝ) ≤ N + 1 := by exact_mod_cast (hq j).2
      simp only [node, Pi.add_apply, Pi.smul_apply, latticePoint_apply, smul_eq_mul, Set.mem_Icc]
      constructor <;> nlinarith
    refine hbd _ hc fun ho => hq' (mem_interiorNodes.2 fun j => ?_)
    have := ho j (mem_univ j)
    simp only [node, Pi.add_apply, Pi.smul_apply, latticePoint_apply, smul_eq_mul, Set.mem_Ioo] at this
    have h1 : (0 : ℝ) < q j := by nlinarith
    have h2 : (q j : ℝ) < N + 1 := by nlinarith
    have h1' : (0 : ℤ) < q j := by exact_mod_cast h1
    have h2' : q j < (N : ℤ) + 1 := by exact_mod_cast h2
    omega

/-- `s ↦ f(x + s eₗ)` has derivative `∂ₗ f(x + t eₗ)` at `t`. -/
theorem hasDerivAt_line {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f) (x : Fin n → ℝ)
    (l : Fin n) (t : ℝ) :
    HasDerivAt (fun r : ℝ => f (x + r • Pi.single l 1))
      (partialDeriv l f (x + t • Pi.single l 1)) t := by
  have hl : HasDerivAt (fun r : ℝ => x + r • (Pi.single l 1 : Fin n → ℝ)) (Pi.single l 1) t := by
    simpa using ((hasDerivAt_id t).smul_const (Pi.single l (1 : ℝ) : Fin n → ℝ)).const_add x
  exact (hf _).hasFDerivAt.comp_hasDerivAt t hl

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
  have hd : ∀ (l : Fin n) (k : ℕ), k ≤ 3 → Differentiable ℝ ((partialDeriv l)^[k] u) := by
    intro l k hk
    have : ∀ k ≤ 4, ContDiff ℝ (4 - k : ℕ) ((partialDeriv l)^[k] u) := by
      intro k hk
      induction k with
      | zero => simpa using hu
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (ih (by omega)).partialDeriv (by norm_cast; omega) l
    exact (this k (by omega)).differentiable (by norm_cast; omega)
  have hterm : ∀ l, |partialDeriv l (partialDeriv l u) x -
      (u (node b h ((p : Fin n → ℤ) + Pi.single l 1)) - 2 * u x +
        u (node b h ((p : Fin n → ℤ) - Pi.single l 1))) / h ^ 2| ≤ B * h ^ 2 / 12 := by
    intro l
    set g : ℕ → ℝ → ℝ := fun k t => (partialDeriv l)^[k] u (x + t • Pi.single l 1)
    have hg : ∀ k ≤ 3, ∀ t, HasDerivAt (g k) (g (k + 1) t) t := fun k hk t => by
      have := hasDerivAt_line (hd l k hk) x l t
      simpa [g, Function.iterate_succ_apply'] using this
    have key := abs_secondDiff_sub_le (g := g 0) (g₁ := g 1) (g₂ := g 2) (g₃ := g 3)
      (g₄ := g 4) (B := B) hh.le (fun t _ => hg 0 (by omega) t) (fun t _ => hg 1 (by omega) t)
      (fun t _ => hg 2 (by omega) t) (fun t _ => hg 3 le_rfl t)
      (fun t ht => hB _ (node_add_smul_mem_closedCube hs p l ht) l)
    have e1 : node b h ((p : Fin n → ℤ) + Pi.single l 1) = x + h • Pi.single l 1 := by
      rw [node_add_single, Int.cast_one, mul_one]
    have e2 : node b h ((p : Fin n → ℤ) - Pi.single l 1) = x + (-h) • Pi.single l 1 := by
      rw [sub_eq_add_neg, ← Pi.single_neg, node_add_single, Int.cast_neg, Int.cast_one, mul_neg,
        mul_one]
    simp only [g, Function.iterate_zero, id, zero_smul, add_zero, Function.iterate_succ,
      Function.comp] at key
    rw [e1, e2]
    have hh2 : 0 < h ^ 2 := by positivity
    have hh' : h ≠ 0 := hh.ne'
    rw [show partialDeriv l (partialDeriv l u) x -
        (u (x + h • Pi.single l 1) - 2 * u x + u (x + (-h) • Pi.single l 1)) / h ^ 2 =
        -(u (x + h • Pi.single l 1) - 2 * u x + u (x + (-h) • Pi.single l 1) -
          h ^ 2 * partialDeriv l (partialDeriv l u) x) / h ^ 2 by field_simp; ring,
      abs_div, abs_neg, abs_of_pos hh2, div_le_iff₀ hh2]
    calc _ ≤ B * h ^ 4 / 12 := key
      _ = B * h ^ 2 / 12 * h ^ 2 := by ring
  have hplus : ∀ l, ext (interp b s N u) ((p : Fin n → ℤ) + Pi.single l 1) =
      u (node b h ((p : Fin n → ℤ) + Pi.single l 1)) := fun l =>
    ext_interp hs hbd fun j => by
      have := hp j
      by_cases hj : j = l
      · subst hj; simp only [Pi.add_apply, Pi.single_eq_same]; omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]; omega
  have hminus : ∀ l, ext (interp b s N u) ((p : Fin n → ℤ) - Pi.single l 1) =
      u (node b h ((p : Fin n → ℤ) - Pi.single l 1)) := fun l =>
    ext_interp hs hbd fun j => by
      have := hp j
      by_cases hj : j = l
      · subst hj; simp only [Pi.sub_apply, Pi.single_eq_same]; omega
      · simp only [Pi.sub_apply, Pi.single_eq_of_ne hj, sub_zero]; omega
  rw [lumpedLaplacian_apply, show interp b s N (laplacian u) p =
    ∑ l, partialDeriv l (partialDeriv l u) x from rfl, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l, |partialDeriv l (partialDeriv l u) x - (ext (interp b s N u)
          ((p : Fin n → ℤ) + Pi.single l 1) - 2 * interp b s N u p +
          ext (interp b s N u) ((p : Fin n → ℤ) - Pi.single l 1)) / h ^ 2|
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

/-! ### The stable family and the heat equation -/

/-- **The maximum-norm family**: the lumped-mass `P₁` Laplacians `Lₕ` of the levels `N + 1` on
`ℝ^{interior nodes}` with the maximum norm, a uniformly stable family with `M = 1`
(`isSubMarkovGenerator`). -/
abbrev family (b : Fin n → ℝ) (hs : 0 < s) : StableFamily ℝ ℕ where
  X N := Space n N
  L N := lumpedLaplacian b hs N
  M := 1
  M_nonneg := zero_le_one
  norm_exp_le N t ht := by simpa using (isSubMarkovGenerator b hs N).norm_exp_smul_le_one ht

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

theorem hasDerivAt_interp (hs : 0 < s) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivAt (fun t => interp b s N (S.u t)) (interp b s N (S.u₁ t)) t :=
  hasDerivAt_pi.2 fun p => S.hasDerivAt t ht _ (node_mem_openCube hs p)

/-- **The defect of the interpolated solution**: `‖Iₕ uₜ - Lₕ Iₕ u‖_∞ ≤ n B₄ h² / 12`. -/
theorem norm_defect_le (hs : 0 < s) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖interp b s N (S.u₁ t) - lumpedLaplacian b hs N (interp b s N (S.u t))‖ ≤ S.defect N := by
  have e : interp b s N (S.u₁ t) = interp b s N (laplacian (S.u t)) :=
    funext fun p => S.heat t ht _ (node_mem_openCube hs p)
  rw [e]
  exact norm_interp_laplacian_sub_le hs N (S.contDiff t ht) (S.bound₄ t ht) (S.boundary t ht)

end HeatSolution

/-- **The semidiscrete error in the maximum norm**: `‖Iₕ u(t) - e^{tLₕ} v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞`
`+ t n B₄ h² / 12` for `t ∈ [0, T]`, every discrete datum `v`. -/
theorem norm_interp_sub_exp_le (hs : 0 < s) {T : ℝ} (S : HeatSolution b s T) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) (v : Space n N) :
    ‖interp b s N (S.u t) - exp (t • lumpedLaplacian b hs N) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + t * S.defect N := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have H := (family b hs).norm_sub_exp_le_of_defect N ht.1
    (U := fun t => interp b s N (S.u t)) (fun r hr => S.hasDerivAt_interp hs N (hsub hr))
    (fun r hr => S.norm_defect_le hs N (hsub hr)) v
  simpa using H

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
  have H := (family b hs).norm_sub_res_pow_le_of_traj hτ N
    (U := fun t => interp b s N (S.u t)) (U₁ := fun t => interp b s N (S.u₁ t))
    (U₂ := fun t => interp b s N (u₂ t)) (fun r hr => S.hasDerivAt_interp hs N (hsub hr))
    (fun r hr => hasDerivAt_pi.2 fun p => hu₂ r (hsub hr) _ (node_mem_openCube hs p)) hB
    (fun r hr => S.norm_defect_le hs N (hsub hr)) v
  simpa using H

/-- **Every A-stable rational scheme in the maximum norm**: for `r` of order `p` (Crank–Nicolson,
the Gauss and Radau methods),
`‖Iₕ u(kτ) - r(τLₕ)ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ n B₄ h² / 12 + C_r kτ τᵖ ‖Lₕ^{p+1} v‖_∞`,
`C_r = sharpConst r p` (Brenner–Thomée's smooth-data estimate, `M = 1`). -/
theorem norm_interp_sub_step_pow_le (hs : 0 < s) {T : ℝ} (S : HeatSolution b s T)
    {r : RationalScheme} (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) (N : ℕ) {τ : ℝ}
    (hτ : 0 < τ) {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) :
    ‖interp b s N (S.u (k * τ)) - ((family b hs).step r τ N ^ k) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * S.defect N +
        r.sharpConst p * (k * τ) * τ ^ p * ‖(lumpedLaplacian b hs N ^ (p + 1)) v‖ := by
  have hsub : Icc 0 (k * τ) ⊆ Icc 0 T := Icc_subset_Icc le_rfl hk
  have H := (family b hs).norm_sub_step_pow_le_of_traj hr hp hτ N
    (U := fun t => interp b s N (S.u t)) (fun r hr => S.hasDerivAt_interp hs N (hsub hr))
    (fun r hr => S.norm_defect_le hs N (hsub hr)) v
  simpa using H

/-- **Brenner–Thomée's stability bound in the maximum norm**: `‖r(τLₕ)ᵏ‖_∞ ≤ 1 + C'_r √k` for
every A-stable `r` (Crank–Nicolson included), uniformly in `h`. [BrennerThomee1979] -/
theorem norm_step_pow_le (hs : 0 < s) {r : RationalScheme} (hr : r.IsAStable) (N : ℕ) {τ : ℝ}
    (hτ : 0 < τ) (k : ℕ) : ‖(family b hs).step r τ N ^ k‖ ≤ 1 + r.sqrtConst * √k := by
  simpa using (family b hs).norm_step_pow_le hr hτ N k

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

theorem differentiable_sineDeriv (a c : ℝ) (k : ℕ) (hk : k ≤ 3) :
    Differentiable ℝ (sineDeriv a c k) := fun y => (hasDerivAt_sineDeriv a c k hk y).differentiableAt

theorem differentiable_sineDeriv_four (a c : ℝ) : Differentiable ℝ (sineDeriv a c 4) := by
  simp only [sineDeriv]; fun_prop

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
      by_cases hj : j = i
      · subst hj; simp only [sineFactors, Function.update_self]
        exact differentiable_sineDeriv a _ k (by omega)
      · simp only [sineFactors, Function.update_of_ne hj]
        exact differentiable_sineDeriv a _ 0 (by omega)
    rw [partialDeriv_const_mul_prod c hG (g := sineDeriv a (b i) (k + 1)) (fun y => by
      simpa [sineFactors] using hasDerivAt_sineDeriv a (b i) k (by omega) y)]
    simp only [sineFactors, Function.update_idem]

/-- `∏ⱼ G̃ⱼ(xⱼ) = κ ∏ⱼ Gⱼ(xⱼ)` when the `i`-th factor is replaced by `κ Gᵢ`. -/
theorem prod_update_const_mul (G : Fin n → ℝ → ℝ) (i : Fin n) (κ : ℝ) (x : Fin n → ℝ) :
    ∏ j, Function.update G i (fun y => κ * G i y) j (x j) = κ * ∏ j, G j (x j) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    Function.update_self, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **The first eigenmode** `u(t, x) = e^{-λt} ∏ᵢ sin(π (xᵢ - bᵢ)/s)`, `λ = n π² / s²`: a
classical solution of the heat equation on every `[0, T] × Q` with `B₄ = (π/s)⁴`. -/
def sineSolution (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) : HeatSolution b s T where
  u t x := Real.exp (-(n * sineFreq s ^ 2) * t) * ∏ j, sineDeriv (sineFreq s) (b j) 0 (x j)
  u₁ t x := -(n * sineFreq s ^ 2) *
    (Real.exp (-(n * sineFreq s ^ 2) * t) * ∏ j, sineDeriv (sineFreq s) (b j) 0 (x j))
  contDiff t _ := by simp only [sineDeriv]; fun_prop
  hasDerivAt t _ x _ := by
    have := ((Real.hasDerivAt_exp _).comp t
      ((hasDerivAt_id t).const_mul (-(n * sineFreq s ^ 2)))).mul_const
      (∏ j, sineDeriv (sineFreq s) (b j) 0 (x j))
    exact this.congr_deriv (by simp; ring)
  heat t _ x _ := by
    have e : ∀ i, partialDeriv i (partialDeriv i (fun x : Fin n → ℝ =>
        Real.exp (-(n * sineFreq s ^ 2) * t) * ∏ j, sineDeriv (sineFreq s) (b j) 0 (x j))) x =
        -sineFreq s ^ 2 *
          (Real.exp (-(n * sineFreq s ^ 2) * t) * ∏ j, sineDeriv (sineFreq s) (b j) 0 (x j)) :=
      fun i => by
        have := congrFun (iterate_partialDeriv_sine b (sineFreq s)
          (Real.exp (-(n * sineFreq s ^ 2) * t)) i 2 (by omega)) x
        simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id] at this
        rw [this, sineFactors, show sineDeriv (sineFreq s) (b i) 2 =
          fun y => -sineFreq s ^ 2 * sineDeriv (sineFreq s) (b i) 0 y from rfl,
          prod_update_const_mul (fun j => sineDeriv (sineFreq s) (b j) 0)]
        ring
    simp only [laplacian, e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
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
  bound₄ t ht x _ i := by
    have := congrFun (iterate_partialDeriv_sine b (sineFreq s)
      (Real.exp (-(n * sineFreq s ^ 2) * t)) i 4 le_rfl) x
    rw [this, sineFactors, show sineDeriv (sineFreq s) (b i) 4 =
      fun y => sineFreq s ^ 4 * sineDeriv (sineFreq s) (b i) 0 y from rfl,
      prod_update_const_mul (fun j => sineDeriv (sineFreq s) (b j) 0), abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), Finset.abs_prod]
    have h1 : Real.exp (-(n * sineFreq s ^ 2) * t) ≤ 1 :=
      Real.exp_le_one_iff.2 (by rw [neg_mul]; exact neg_nonpos.2 (mul_nonneg (by positivity) ht.1))
    have h2 : ∏ j, |sineDeriv (sineFreq s) (b j) 0 (x j)| ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => Real.abs_sin_le_one _
    rw [abs_of_nonneg (by positivity)]
    calc Real.exp (-(n * sineFreq s ^ 2) * t) *
          (sineFreq s ^ 4 * ∏ j, |sineDeriv (sineFreq s) (b j) 0 (x j)|)
        ≤ 1 * (sineFreq s ^ 4 * 1) := by gcongr
      _ = sineFreq s ^ 4 := by ring

/-- The first eigenmode is nonzero at the centre of the cube at `t = 0`. -/
theorem sineSolution_u_zero_center (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) :
    (sineSolution b hs T).u 0 (b + (s / 2) • fun _ => (1 : ℝ)) = 1 := by
  simp only [sineSolution, sineDeriv, sineFreq, mul_zero, Real.exp_zero, one_mul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, mul_one, add_sub_cancel_left]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [show Real.pi / s * (s / 2) = Real.pi / 2 by field_simp, Real.sin_pi_div_two]

/-! ### The verdict -/

/-- The conclusions of `maxNormHeat` for the cube `b + (0, s)ⁿ`: non-obtuse Freudenthal meshes,
the difference stencil of the lumped-mass `P₁` Laplacian, the discrete maximum principle,
maximum-norm consistency, the semidiscrete, backward Euler and rational-scheme errors against
every classical solution, Brenner–Thomée's stability bound, and the verdict of the Banach layer
for the family. -/
structure Verdict (b : Fin n → ℝ) (hs : 0 < s) : Prop where
  /-- the Freudenthal meshes are non-obtuse: nonpositive off-diagonal stiffness -/
  nonobtuse (N : ℕ) [NeZero N] {x y : Fin n → ℝ} (hxy : x ≠ y) :
    p1Stiffness (freudenthalMesh b s hs N) (nodalIndicator x) (nodalIndicator y) ≤ 0
  /-- the lumped-mass `P₁` Laplacian is the `(2n + 1)`-point difference Laplacian -/
  stencil (N : ℕ) (U : Space n N) (p : Nodes n N) :
    lumpedLaplacian b hs N U p = ∑ l, (ext U ((p : Fin n → ℤ) + Pi.single l 1) - 2 * U p +
      ext U ((p : Fin n → ℤ) - Pi.single l 1)) / meshSize s N ^ 2
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

/-- **The heat equation in the maximum norm** (lumped-mass `P₁` elements on the Freudenthal
meshes of the cube `b + (0, s)ⁿ`, Dirichlet data): see `Verdict`. [Thomee2006], Ch. 15;
[CiarletRaviart1973]; [BrennerThomee1979] -/
theorem maxNormHeat (b : Fin n → ℝ) (hs : 0 < s) : Verdict b hs where
  nonobtuse := fun N _ _ _ hxy => p1Stiffness_freudenthalMesh_indicator_nonpos b hs N hxy
  stencil := fun _ U p => lumpedLaplacian_apply b hs U p
  maximumPrinciple := isSubMarkovGenerator b hs
  consistency := @fun N _ hu _ hB hbd => norm_interp_laplacian_sub_le hs N hu hB hbd
  semidiscrete := @fun _ S N _ ht v => norm_interp_sub_exp_le hs S N ht v
  backwardEuler := @fun _ S _ _ hu₂ hB₂ N _ hτ _ hk v =>
    norm_interp_sub_res_pow_le hs S hu₂ hB₂ N hτ hk v
  stable_rational := @fun _ hr N _ hτ k => norm_step_pow_le hs hr N hτ k
  rational := @fun _ S _ hr _ hp N _ hτ _ hk v => norm_interp_sub_step_pow_le hs S hr hp N hτ hk v
  banach := stableFamily _

/-- **The verdict is not vacuous**: the first eigenmode `sineSolution` is a classical solution
on every `[0, T] × Q`, nonzero at `t = 0`, so the semidiscrete, backward Euler and rational
clauses apply to it. -/
theorem maxNormHeat_nonvacuous (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) :
    Verdict b hs ∧ ∃ S : HeatSolution b s T, S.u 0 ≠ 0 :=
  ⟨maxNormHeat b hs, sineSolution b hs T, fun h => by
    have := congrFun h (b + (s / 2) • fun _ => (1 : ℝ))
    rw [sineSolution_u_zero_center] at this
    exact one_ne_zero this⟩

end Feec.Models.Cube.MaxNormHeat
