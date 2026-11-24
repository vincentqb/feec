module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but its thirteen theorems),
compiled against Mathlib alone so that their elaborated values are those of the challenge: its
imports, opens and definitions, the rational schemes of semigroups (`TimeStepping.IsC0Semigroup`,
`TimeStepping.generatorGraph`, `TimeStepping.rationalOfResolvent`, `TimeStepping.IsAStable`,
`TimeStepping.HasOrder` and their companions), sub-Markov generators
(`TimeStepping.IsSubMarkovGenerator`), the lumped-mass `P₁` method on simplicial meshes
(`TimeStepping.SimplicialMesh`, `TimeStepping.p1Grad`, `TimeStepping.p1Stiffness`,
`TimeStepping.lumpedMass`, `TimeStepping.lumpedLaplacian`, `TimeStepping.IsNonobtuse`,
`TimeStepping.IsTranslationInvariantAt`) and finite differences (`TimeStepping.fdLaplacian`,
`TimeStepping.gridNodes`, `TimeStepping.gridPoint`, `TimeStepping.gridInterp`). The solution
imports this module and the bridges to `Feec`, and proves the theorems (`Solution.lean`).

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [A. Gomilko, Y. Tomilov, *Rational Approximation of Operator Semigroups via the B-Calculus*][GomilkoTomilov2024],
  Thm 1.1
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.4, §1.5, §3.4
* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.3,
  §IV.11
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7, 9, 15
* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Polynomial Asymptotics Filter Set LinearPMap MeasureTheory

@[expose] public noncomputable section

namespace TimeStepping

section Operators

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `S` is a **strongly continuous semigroup** of bounded operators: `S 0 = 1`,
`S (s + t) = S s S t` for `s, t ≥ 0`, and every orbit `t ↦ S t x` is continuous on `[0, ∞)`. -/
def IsC0Semigroup (S : ℝ → E →L[𝕜] E) : Prop :=
  S 0 = 1 ∧ (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t) ∧
    ∀ x : E, ContinuousOn (fun t => S t x) (Ici 0)

/-- The **graph of the generator** `A` of `S`: `(x, y)` with `x ∈ D(A)` and `A x = y`, i.e. the
orbit `t ↦ S t x` has right derivative `y` at `0`. -/
def generatorGraph [NormedSpace ℝ E] (S : ℝ → E →L[𝕜] E) : Set (E × E) :=
  {xy | HasDerivWithinAt (fun t => S t xy.1) xy.2 (Ici 0) 0}

/-- The polynomial `p` evaluated through the resolvent `R = (1 - τA)⁻¹` at degree `N`:
`P(R) = Σ_{k ≤ N} pₖ (R - 1)ᵏ R^{N-k}`, i.e. the bounded operator `p(τA) Rᴺ` (`= Rᴺ p(τA)` on
`D(Aᴺ)`) since `R - 1 = τA R`, when `deg p ≤ N` (coefficients of `p` above `N` are dropped). -/
def resolventPoly (N : ℕ) (p : ℝ[X]) (R : E →L[𝕜] E) : E →L[𝕜] E :=
  ∑ k ∈ Finset.range (N + 1), (p.coeff k : 𝕜) • ((R - 1) ^ k * R ^ (N - k))

/-- **The rational scheme through the resolvent**: `r(τA) = P(R) Q(R)⁻¹` for `r = p/q`,
`N = deg q`, at the resolvent `R = (1 - τA)⁻¹` (`Q(R)⁻¹` the inverse in the algebra of bounded
operators, `Ring.inverse`). -/
def rationalOfResolvent (p q : ℝ[X]) (R : E →L[𝕜] E) : E →L[𝕜] E :=
  resolventPoly q.natDegree p R * Ring.inverse (resolventPoly q.natDegree q R)

end Operators

-- palomar-shared: rationalScheme
/-- `r = p/q` is **A-stable** ([HairerWanner1996], §IV.3): on the closed left half-plane `q` has
no zero and `|r| ≤ 1` (a property of the pair `p`, `q`; for coprime `p`, `q`, of `r`). -/
def IsAStable (p q : Polynomial ℝ) : Prop :=
  ∀ z : ℂ, z.re ≤ 0 → Polynomial.aeval z q ≠ 0 ∧
    ‖Polynomial.aeval z p / Polynomial.aeval z q‖ ≤ 1
/-- `r = p/q` has **order `m`**: `r(z) - e^z = O(z^{m+1})` as `z → 0` (with `q(0) ≠ 0`, as for
A-stable `p/q`, the quotient is the rational function near `0`). -/
def HasOrder (p q : Polynomial ℝ) (m : ℕ) : Prop :=
  (fun z : ℂ => Polynomial.aeval z p / Polynomial.aeval z q - Complex.exp z) =O[𝓝 0]
    fun z => z ^ (m + 1)
/-- **The rational scheme of a bounded operator**: `r(L) = p(L) q(L)⁻¹` for `r = p/q` (`0` if
`q(L)` is not invertible; for A-stable `p/q` and dissipative `L` on a Hilbert space it is). -/
def rationalApply {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (p q : Polynomial ℝ) (L : E →L[𝕜] E) : E →L[𝕜] E :=
  Polynomial.aeval L (p.map (algebraMap ℝ 𝕜)) *
    Ring.inverse (Polynomial.aeval L (q.map (algebraMap ℝ 𝕜)))
-- palomar-shared-end: rationalScheme

/-! ### Banach spaces: Brenner–Thomée -/

/-! ### Hilbert spaces: von Neumann -/

/-! ### Convergence for every datum: Lax -/

/-! ### Where the Banach theory is needed: the heat equation in the maximum norm -/

/-- `L` is a **sub-Markov generator** on `ℝ^ι` (`ι` finite, maximum norm): `L + c` is positive
for some `c ≥ 0` and `L 𝟙 ≤ 0`. For a matrix: nonnegative off-diagonal entries and nonpositive
row sums. -/
def IsSubMarkovGenerator {ι : Type*} [Fintype ι] (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) : Prop :=
  (∃ c : ℝ, 0 ≤ c ∧ ∀ v : ι → ℝ, 0 ≤ v → 0 ≤ L v + c • v) ∧ ∀ i, L (fun _ => 1) i ≤ 0

-- palomar-shared: SimplicialMesh
/-- The vertex set `{v₀, …, v_k}` of a simplex. -/
def vertexSet {n k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) : Finset (Fin n → ℝ) :=
  Finset.univ.image T.points
/-- A **conforming simplicial mesh** of `closure domain ⊆ ℝⁿ`: a finite set of `n`-simplices
whose closed simplices cover `closure domain`, have pairwise disjoint interiors, and meet face to
face (the intersection of two closed simplices is the convex hull of their common vertices). -/
structure SimplicialMesh (n : ℕ) where
  /-- the `n`-simplices -/
  simplices : Finset (Affine.Simplex ℝ (Fin n → ℝ) n)
  /-- the meshed set `Ω`; the mesh covers its closure -/
  domain : Set (Fin n → ℝ)
  biUnion_closedInterior : ⋃ T ∈ simplices, T.closedInterior = closure domain
  pairwise_disjoint_interior :
    (simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)).Pairwise fun T T' =>
      Disjoint (interior T.closedInterior) (interior T'.closedInterior)
  inter_closedInterior : ∀ T ∈ simplices, ∀ T' ∈ simplices,
    T.closedInterior ∩ T'.closedInterior =
      convexHull ℝ ((vertexSet T : Set (Fin n → ℝ)) ∩ vertexSet T')
-- palomar-shared-end: SimplicialMesh

-- palomar-shared: p1
/-- **The gradient `∇Π_T u` of the `P₁` interpolant** of `u` on the `n`-simplex `T` of `ℝⁿ` with
vertices `v₀, …, vₙ`: the gradient of the affine function with the values `u(vⱼ)` at the
vertices, the vector `g` with `g · (vₗ - v₀) = u(vₗ) - u(v₀)` for `l = 1, …, n`, that is
`g = (Eᵀ)⁻¹ δ` for the edge matrix `E` with columns `vₗ - v₀` and `δₗ = u(vₗ) - u(v₀)`. For `u`
equal to `1` at `vⱼ` and `0` at the other vertices it is the gradient `∇λⱼ` of the barycentric
coordinate `λⱼ`. -/
def p1Grad {n : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) n) (u : (Fin n → ℝ) → ℝ) : Fin n → ℝ :=
  Matrix.vecMul (fun l : Fin n => u (T.points l.succ) - u (T.points 0))
    (Matrix.of fun i l : Fin n => T.points l.succ i - T.points 0 i)⁻¹
/-- **The `P₁` stiffness form** of the mesh `M` on nodal values (only the values of `u`, `w` at
the vertices enter), `a(u, w) = Σ_T ∫_T ∇Π_T u · ∇Π_T w`: the Dirichlet form `∫ ∇u_h · ∇w_h` of
the continuous piecewise affine functions `u_h`, `w_h` with these vertex values. -/
def p1Stiffness {n : ℕ} (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑ T ∈ M.simplices, ∫ _ in T.closedInterior, p1Grad T u ⬝ᵥ p1Grad T w
-- palomar-shared-end: p1

/-- **The lumped mass** of the mesh `M` at `y`, the vertex quadrature of `∫ φ_y` (`φ_y` the
continuous piecewise affine hat function at `y`): `m(y) = Σ_T |T| / (n + 1)` over the simplices
`T` with vertex `y`. -/
def lumpedMass {n : ℕ} (M : SimplicialMesh n) (y : Fin n → ℝ) : ℝ :=
  ∑ T ∈ M.simplices, volume.real T.closedInterior / (n + 1) *
    ((Finset.univ.filter fun j => T.points j = y).card : ℝ)

/-- **The lumped-mass `P₁` Laplacian** `Lₕ = -M_L⁻¹ K` of the mesh `M` on the nodes
`x : ι → ℝⁿ` (`ι` finite; [Thomee2006], Ch. 15): on the nodal values `U : ι → ℝ`, with the
maximum norm, `(Lₕ U)(p) = -a(φ_{x p}, U_h) / m(x p)`, `U_h = Σ_q U(q) φ_{x q}` the continuous
piecewise affine function with the values `U` at the nodes and `0` at the other vertices
(homogeneous Dirichlet data there; if every vertex is a node, the natural boundary condition), in
matrix form. `U' = Lₕ U` is the semidiscrete heat equation of the lumped-mass method: the Galerkin
method in the `P₁` functions vanishing at the vertices that are not nodes, with the vertex
quadrature `Σ_y m(y) U_h(y) V_h(y)` as inner product. (A node that is no vertex has `m = 0`
and a zero row.) -/
def lumpedLaplacian {n : ℕ} (M : SimplicialMesh n) {ι : Type*} [Fintype ι]
    (x : ι → Fin n → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (Matrix.of fun p q => -p1Stiffness M (fun z => if z = x p then 1 else 0)
    (fun z => if z = x q then 1 else 0) / lumpedMass M (x p)).mulVecLin.toContinuousLinearMap

/-- The mesh `M` is **non-obtuse**: all dihedral angles of its simplices are at most `π / 2`,
that is `∇λⱼ · ∇λₖ ≤ 0` for `j ≠ k`, `λⱼ` the barycentric coordinates of the simplex. -/
def IsNonobtuse {n : ℕ} (M : SimplicialMesh n) : Prop :=
  ∀ T ∈ M.simplices, ∀ j k, j ≠ k →
    p1Grad T (fun z => if z = T.points j then 1 else 0) ⬝ᵥ
      p1Grad T (fun z => if z = T.points k then 1 else 0) ≤ 0

/-- The mesh `M` is **translation invariant at** `y`: for every simplex `T` of `M` with vertex
`y` and every vertex `v` of `T`, the translate `T + (y - v)`, which moves `v` to `y`, is a simplex
of `M`: `M` has a simplex whose vertices are those of `T` translated by `y - v` (in any
numbering). It holds at a vertex `y` where `M` agrees with a lattice triangulation of `ℝⁿ` (a
triangulation invariant under the translations by the differences of its vertices, such as the
Freudenthal triangulation): the simplices of `M` with vertex `y` are those of the
triangulation. -/
def IsTranslationInvariantAt {n : ℕ} (M : SimplicialMesh n) (y : Fin n → ℝ) : Prop :=
  ∀ T ∈ M.simplices, y ∈ vertexSet T → ∀ j, ∃ T' ∈ M.simplices,
    (vertexSet T' : Set (Fin n → ℝ)) = (· + (y - T.points j)) '' (vertexSet T : Set (Fin n → ℝ))

/-- **The finite difference Laplacian** on a finite grid `G ⊆ ℤ^ι` with mesh size `h` and
homogeneous Dirichlet data: `(Δₕ U)(p) = Σᵢ (U(p + eᵢ) - 2 U(p) + U(p - eᵢ)) / h²`, the values
off `G` taken to be `0`. -/
def fdLaplacian {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Finset (ι → ℤ)) (h : ℝ) :
    (G → ℝ) →L[ℝ] (G → ℝ) :=
  LinearMap.toContinuousLinearMap <| LinearMap.pi fun p : G => ∑ i, (h ^ 2)⁻¹ •
    ((if hq : (p : ι → ℤ) + Pi.single i 1 ∈ G then LinearMap.proj (R := ℝ) (φ := fun _ : G => ℝ)
        ⟨_, hq⟩ else 0) - (2 : ℝ) • LinearMap.proj (R := ℝ) (φ := fun _ : G => ℝ) p +
      (if hq : (p : ι → ℤ) - Pi.single i 1 ∈ G then LinearMap.proj (R := ℝ) (φ := fun _ : G => ℝ)
        ⟨_, hq⟩ else 0))

/-- The `Nⁿ` interior nodes `q ∈ {1, …, N}ⁿ` of the uniform grid of a cube. -/
def gridNodes (n N : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Finset.Ioo 0 ((N + 1 : ℕ) : ℤ)

/-- The grid point `b + h q` of mesh size `h` at `q ∈ ℤⁿ`. -/
def gridPoint {n : ℕ} (b : Fin n → ℝ) (h : ℝ) (q : Fin n → ℤ) : Fin n → ℝ :=
  b + h • fun j => (q j : ℝ)

/-- The nodal interpolant `(Iₕ f)(q) = f(b + h q)` at the interior grid nodes. -/
def gridInterp {n : ℕ} (b : Fin n → ℝ) (h : ℝ) (N : ℕ) (f : (Fin n → ℝ) → ℝ) :
    gridNodes n N → ℝ :=
  fun g => f (gridPoint b h g)

/-! ### The hypotheses on `r` are met -/

/-- The numerator `p(z) = det(1 - z A + z 𝟙 bᵀ)` of the **stability function** `r = p/q` of the
`s`-stage Runge–Kutta method with Butcher tableau `(A, b)` (`A ∈ ℝ^{s×s}` the coefficients,
`b ∈ ℝˢ` the weights, `𝟙 = (1, …, 1)`; the nodes do not enter linear autonomous problems), a
real polynomial in `z` ([HairerWanner1996], §IV.3, Prop 3.2): applied to `u' = λ u` with time
step `τ`, the method gives `u₁ = r(τλ) u₀` where `q(τλ) ≠ 0` (`rungeKutta`), and
`r(z) = 1 + z bᵀ (1 - z A)⁻¹ 𝟙` where `q(z) ≠ 0` (the case `L = z` of `rungeKutta`). -/
def stabilityNum {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) : ℝ[X] :=
  ((1 : Matrix (Fin s) (Fin s) ℝ[X]) -
    (X : ℝ[X]) • (A - Matrix.vecMulVec (fun _ => 1) b).map C).det

/-- The denominator `q(z) = det(1 - z A)` of the stability function of the Runge–Kutta method
with coefficients `A`. -/
def stabilityDen {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) : ℝ[X] :=
  ((1 : Matrix (Fin s) (Fin s) ℝ[X]) - (X : ℝ[X]) • A.map C).det

/-! ### The classical inputs -/

end TimeStepping
