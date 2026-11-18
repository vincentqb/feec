module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
`TimeStepping.HasOrder` and their companions), finite differences (`TimeStepping.fdLaplacian`,
`TimeStepping.gridNodes`, `TimeStepping.gridInterp`) and the Whitney schemes of the cube
(`TimeStepping.femSpace`, `TimeStepping.IsCNStep`, `TimeStepping.IsLeapfrogStep`,
`TimeStepping.RowSolution` and their companions). The solution imports this module and the
bridges to `Feec`, and proves the theorems (`Solution.lean`).

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [A. Gomilko, Y. Tomilov, *Rational Approximation of Operator Semigroups via the B-Calculus*][GomilkoTomilov2024],
  Thm 1.1
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.4, §1.5, §3.4
* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.3,
  §IV.11
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 1, 7, 15
* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7
* [P. Joly, *Variational Methods for Time-Dependent Wave Propagation Problems*][Joly2003]
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3–5
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4, §5.2
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6, 7
* [H. Whitney, *Geometric Integration Theory*][Whitney1957], Ch. IV
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1, §3.2
* [S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*][BrennerScott2008],
  §4.5

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
/-- **The rational scheme of a bounded operator**: `r(L) = p(L) q(L)⁻¹` for `r = p/q`. -/
def rationalApply {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (p q : Polynomial ℝ) (L : E →L[𝕜] E) : E →L[𝕜] E :=
  Polynomial.aeval L (p.map (algebraMap ℝ 𝕜)) *
    Ring.inverse (Polynomial.aeval L (q.map (algebraMap ℝ 𝕜)))
-- palomar-shared-end: rationalScheme

/-! ### Banach spaces -/

/-! ### Hilbert spaces -/

/-! ### Differential forms on `ℝⁿ` (the text of `palomar/fem`) -/

-- palomar-shared: forms
/-- The coefficients of a `k`-form on `ℝⁿ`: the `k`-subsets `s = {s₁ < ⋯ < s_k}` of `Fin n`,
`s` indexing `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}` (none unless `0 ≤ k ≤ n`). -/
abbrev FormIdx (n : ℕ) (k : ℤ) : Type := {s : Finset (Fin n) // (s.card : ℤ) = k}
/-- `L²(Ω; Λᵏ)`: an `L²(Ω)` coefficient (Lebesgue measure) for each `dx_s`, an `ℓ²` sum. -/
abbrev L2Form {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : Type :=
  PiLp 2 fun _ : FormIdx n k => Lp ℝ 2 (volume.restrict Ω)
/-- A **form field** on `ℝⁿ`: at each point a coefficient of `dx_s` for every subset `s` of
`Fin n` (a `k`-form when those off the `k`-subsets vanish). -/
abbrev FormField (n : ℕ) : Type := (Fin n → ℝ) → Finset (Fin n) → ℝ
/-- The sign `ε(j, s) = (-1)^{#{l ∈ s | l < j}}` of moving `dx_j` to its place in `dx_s`. -/
def sgn {n : ℕ} {R : Type*} [Ring R] (j : Fin n) (s : Finset (Fin n)) : R :=
  (-1) ^ (s.filter fun l => l < j).card
/-- The partial derivative `∂_j f(x) = Df(x) e_j` (`0` where `f` is not differentiable). -/
def partialDeriv {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single j 1)
/-- The **exterior derivative** of a form field, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`. -/
def extDeriv {n : ℕ} (w : FormField n) : FormField n :=
  fun x s => ∑ j ∈ s, sgn j s * partialDeriv j (fun y => w y (s.erase j)) x
/-- The **codifferential** `(dᵗψ)_s = -Σ_{j ∉ s} ε(j, s) ∂_j ψ_{s ∪ j}`, formal adjoint of `d`. -/
def codiff {n : ℕ} (ψ : FormField n) : FormField n :=
  fun x s => -∑ j ∈ sᶜ, sgn j s * partialDeriv j (fun y => ψ y (insert j s)) x
open scoped ContDiff in
/-- `f` is a **test function** on `Ω`: smooth, with compact support contained in `Ω`. -/
def IsTestFn {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω
/-- The **weak exterior derivative** `d : L²(Ω; Λᵏ) → L²(Ω; Λᵏ⁺¹)`: the adjoint of the closure of
the codifferential on test forms (the span of the pairs `(ψ, dᵗψ)`), so `du = w` iff
`⟪w, ψ⟫ = ⟪u, dᵗψ⟫` for every test form `ψ`; its domain is `HΛᵏ(Ω)` ([AFW2010], §4). -/
def dMax {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Form Ω k →ₗ.[ℝ] L2Form Ω (k + 1) :=
  (Submodule.span ℝ {p : L2Form Ω (k + 1) × L2Form Ω k | ∃ ψ : FormField n,
    (∀ s, IsTestFn Ω fun x => ψ x s) ∧
    (∀ t : FormIdx n (k + 1), ⇑(p.1 t) =ᵐ[volume.restrict Ω] fun x => ψ x t.1) ∧
    ∀ s : FormIdx n k, ⇑(p.2 s) =ᵐ[volume.restrict Ω] fun x => codiff ψ x s.1}
    ).topologicalClosure.toLinearPMap†
/-- The cube `(0, ½)ⁿ`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := univ.pi fun _ => Ioo 0 (1 / 2)
-- palomar-shared-end: forms

/-! ### The maximum norm -/

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

/-- The nodal interpolant `(Iₕ f)(q) = f(b + h q)` at the interior grid nodes. -/
def gridInterp {n : ℕ} (b : Fin n → ℝ) (h : ℝ) (N : ℕ) (f : (Fin n → ℝ) → ℝ) :
    gridNodes n N → ℝ :=
  fun g => f (b + h • fun j => ((g : Fin n → ℤ) j : ℝ))

/-! ### The hypotheses on `r` are met -/

section FiniteElements

variable {n : ℕ}

/-! ### Polynomial differential forms ([AFW2006], §3) -/

-- palomar-shared: PolyForm
/-- **Polynomial differential forms** on `Kⁿ` in coordinates: a polynomial coefficient `ω_s` for
every subset `s` of `Fin n`, the form `Σ_s ω_s dx_s`. -/
abbrev PolyForm (K : Type*) [Field K] (n : ℕ) : Type _ := Finset (Fin n) → MvPolynomial (Fin n) K
/-- `P_rΛᵏ`: the polynomial `k`-forms (`ω_s = 0` unless `#s = k`) with coefficients of degree at
most `r`. -/
def polyForm (K : Type*) [Field K] (n r k : ℕ) : Submodule K (PolyForm K n) :=
  Submodule.pi Set.univ fun s =>
    if s.card = k then MvPolynomial.restrictTotalDegree (Fin n) K r else ⊥
/-- `H_rΛᵏ`: the polynomial `k`-forms with coefficients homogeneous of degree `r`. -/
def homForm (K : Type*) [Field K] (n r k : ℕ) : Submodule K (PolyForm K n) :=
  Submodule.pi Set.univ fun s =>
    if s.card = k then MvPolynomial.homogeneousSubmodule (Fin n) K r else ⊥
/-- The **Koszul differential** `κ`, the contraction with the position vector field `x`:
`(κω)_s = Σ_{j ∉ s} ε(j, s) x_j ω_{s ∪ j}`. -/
def koszul (K : Type*) [Field K] (n : ℕ) : PolyForm K n →ₗ[K] PolyForm K n :=
  LinearMap.pi fun s => ∑ j ∈ sᶜ,
    (sgn j s : K) • (LinearMap.mulLeft K (MvPolynomial.X j) ∘ₗ LinearMap.proj (insert j s))
/-- `P_r⁻Λᵏ = P_{r-1}Λᵏ + κ H_{r-1}Λ^{k+1}`, the trimmed polynomial `k`-forms (`r ≥ 1`), and
`P_0⁻Λᵏ = 0` ([AFW2006], §3.3). -/
def polyFormMinus (K : Type*) [Field K] (n : ℕ) : ℕ → ℕ → Submodule K (PolyForm K n)
  | 0, _ => ⊥
  | r + 1, k => polyForm K n r k ⊔ (homForm K n r (k + 1)).map (koszul K n)
/-- The **evaluation** of a real polynomial form: the form field `x ↦ (ω_s(x))_s`. -/
def evalForm {n : ℕ} : PolyForm ℝ n →ₗ[ℝ] FormField n :=
  LinearMap.pi fun x => LinearMap.pi fun s =>
    (MvPolynomial.aeval x).toLinearMap ∘ₗ LinearMap.proj s
-- palomar-shared-end: PolyForm
-- palomar-shared: PolySeq
/-- **An admissible sequence** of polynomial families ([AFW2006], §5; [AFW2010], §5.2): in every
form degree `k` the full space `P_{r_k}Λᵏ` (`full k = true`) or the trimmed space `P_{r_k}⁻Λᵏ`,
`r_k ≥ 1`, followed in degree `k + 1` by `P_{r_k}⁻Λᵏ⁺¹` or by `P_{r_k - 1}Λᵏ⁺¹`. (The piecewise
constants `P_0Λⁿ` are represented by the equal space `P_1⁻Λⁿ`; the spaces of degree `k > n`
are `0`. A full space `P_0Λᵏ` with `k < n` is excluded: it is followed by `P_0⁻Λᵏ⁺¹ = 0`, and
such a family could not approximate `HΛᵏ⁺¹(Ω)`.) -/
structure PolySeq where
  /-- `P_{r_k}Λᵏ` (`true`) or `P_{r_k}⁻Λᵏ` (`false`) in degree `k` -/
  full : ℕ → Bool
  /-- the polynomial degree `r_k` -/
  deg : ℕ → ℕ
  one_le_deg : ∀ k, 1 ≤ deg k
  transition : ∀ k, (full (k + 1) = false ∧ deg (k + 1) = deg k) ∨
    (full (k + 1) = true ∧ deg (k + 1) + 1 = deg k)
/-- The space `P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` of form fields on `ℝⁿ` of the sequence in degree `k`. -/
def PolySeq.space (S : PolySeq) (n k : ℕ) : Submodule ℝ (FormField n) :=
  (if S.full k then polyForm ℝ n (S.deg k) k else polyFormMinus ℝ n (S.deg k) k).map evalForm
-- palomar-shared-end: PolySeq
-- palomar-shared: topSeq
/-- **The Whitney sequence** `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ² → P₁⁻Λ³ → ⋯` (in `ℝ³` the Lagrange, Nédélec
edge and Raviart–Thomas face elements and the piecewise constants; [Whitney1957], [AFW2006],
§3–4). -/
def topSeq : PolySeq where
  full k := k == 0
  deg _ := 1
  one_le_deg _ := le_rfl
  transition _ := Or.inl ⟨rfl, rfl⟩
-- palomar-shared-end: topSeq

/-! ### Simplicial meshes -/

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
/-- The **boundary facets** of the mesh: the facets (sets of `n` vertices of a simplex) of exactly
one of its simplices. -/
def SimplicialMesh.boundaryFacets {n : ℕ} (M : SimplicialMesh n) : Set (Finset (Fin n → ℝ)) :=
  {F | F.card = n ∧ ∃! T, T ∈ M.simplices ∧ F ⊆ vertexSet T}
/-- `h_T`: the diameter of the closed simplex `T`. -/
def diam {n k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) : ℝ := Metric.diam T.closedInterior
/-- The **mesh size** `h = max_T h_T`. -/
def meshSize {n : ℕ} (M : SimplicialMesh n) : ℝ :=
  ⨆ T : M.simplices, diam (T : Affine.Simplex ℝ (Fin n → ℝ) n)
/-- The mesh is **shape regular** with constant `σ` ([Ciarlet2002], §3.1): every simplex `T`
contains a ball `B(x, ρ)` with `h_T ≤ σ ρ`, that is `h_T / ρ_T ≤ σ` for the inradius `ρ_T` (the
largest radius of a ball in `T`). Balls and `h_T` are those of the sup norm (Conventions). -/
def IsShapeRegular {n : ℕ} (M : SimplicialMesh n) (σ : ℝ) : Prop :=
  ∀ T ∈ M.simplices, ∃ x ρ, 0 < ρ ∧ Metric.ball x ρ ⊆ T.closedInterior ∧ diam T ≤ σ * ρ
/-- The mesh is **quasi-uniform** with constant `q`: `q h ≤ h_T` for every simplex. -/
def IsQuasiUniform {n : ℕ} (M : SimplicialMesh n) (q : ℝ) : Prop :=
  ∀ T ∈ M.simplices, q * meshSize M ≤ diam T
/-- `M_N` is a **shape-regular, quasi-uniform family of meshes of `Ω`** with mesh size `h_N → 0`:
meshes of `Ω`, shape regular and quasi-uniform with constants independent of `N`. -/
def IsMeshFamily {n : ℕ} (Ω : Set (Fin n → ℝ)) (M : ℕ → SimplicialMesh n) : Prop :=
  (∀ N, (M N).domain = Ω) ∧
    (∃ σ q : ℝ, 0 < q ∧ ∀ N, IsShapeRegular (M N) σ ∧ IsQuasiUniform (M N) q) ∧
    (∀ N, 0 < meshSize (M N)) ∧ Tendsto (fun N => meshSize (M N)) atTop (𝓝 0)
/-- `𝒯` are **Freudenthal meshes** of the cube `(0, ½)ⁿ` ([Freudenthal1942]): every simplex of
`𝒯 N` is a Kuhn simplex `h (z + K_σ)`, `h = 1 / (2 (N + 1))`, `z ∈ {0, …, N}ⁿ`, `σ ∈ 𝔖ₙ`, with
vertices `v_j = h (z + e_{σ 0} + ⋯ + e_{σ (j - 1)})`, `j = 0, …, n` (a mesh of `(0, ½)ⁿ` of such
simplices consists of all of them). -/
def IsFreudenthal {n : ℕ} (𝒯 : ℕ → SimplicialMesh n) : Prop :=
  ∀ N, ∀ T ∈ (𝒯 N).simplices, ∃ (z : Fin n → Fin (N + 1)) (σ : Equiv.Perm (Fin n)), ∀ j i,
    T.points j i = ((z i : ℝ) + if (σ.symm i : ℕ) < (j : ℕ) then 1 else 0) / (2 * (N + 1))
-- palomar-shared-end: SimplicialMesh

/-! ### The finite element spaces -/

-- palomar-shared: femSpace
/-- The value `α(v₁, …, v_k) = Σ_{#s = k} α_s det (v_l(s_i))_{i,l}` of the `k`-covector `α` on
the vectors `v₁, …, v_k`. -/
def covEval {n k : ℕ} (α : Finset (Fin n) → ℝ) (v : Fin k → Fin n → ℝ) : ℝ :=
  ∑ s : Finset (Fin n), if h : s.card = k then
    α s * (Matrix.of fun i l => v l (s.orderEmbOfFin h i)).det else 0
/-- The `k`-covectors `α`, `β` have the **same tangential trace** on the face spanned by the
points `g`: they agree on all `k`-tuples of vectors tangent to the face. -/
def TraceEq {n : ℕ} (g : Finset (Fin n → ℝ)) (k : ℕ) (α β : Finset (Fin n) → ℝ) : Prop :=
  ∀ v : Fin k → Fin n → ℝ, (∀ l, v l ∈ vectorSpan ℝ (g : Set (Fin n → ℝ))) →
    covEval α v = covEval β v
/-- `p = (p_T)_T` are **finite element pieces** of `u ∈ L²(Ω; Λᵏ)` on the mesh `M` for the
sequence `S`: on every simplex `T`, `u` is (almost everywhere) the polynomial form `p_T ∈ S_k`,
and the tangential traces of `p_T` and `p_{T'}` agree on the common face of any two simplices. -/
def IsFemPieces {n : ℕ} (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (S : PolySeq) (k : ℤ)
    (u : L2Form Ω k) (p : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n) : Prop :=
  (∀ T ∈ M.simplices, p T ∈ S.space n k.toNat) ∧
    (∀ T ∈ M.simplices, ∀ s : FormIdx n k,
      ⇑(u s) =ᵐ[volume.restrict (Ω ∩ T.closedInterior)] fun x => p T x s.1) ∧
    ∀ T ∈ M.simplices, ∀ T' ∈ M.simplices,
      ∀ x ∈ convexHull ℝ ((vertexSet T ∩ vertexSet T' : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)),
        TraceEq (vertexSet T ∩ vertexSet T') k.toNat (p T x) (p T' x)
/-- **The finite element space** `S_k(M) ⊆ L²(Ω; Λᵏ)` of the admissible sequence `S` on the mesh
`M` **with vanishing traces on the facets `Γ`** ([AFW2006], §5; [Arnold2018], Ch. 7): the forms
that are on every simplex a polynomial form of `S_k`, with single-valued tangential traces on the
faces of the mesh, vanishing on the facets of the mesh in `Γ` (`Γ = ∅`: no boundary condition,
the spaces of `HΛ(Ω)`; `Γ = M.boundaryFacets`: vanishing traces on `∂Ω`, those of `H̊Λ(Ω)`). -/
def femSpace {n : ℕ} (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (S : PolySeq)
    (Γ : Set (Finset (Fin n → ℝ))) (k : ℤ) : Set (L2Form Ω k) :=
  {u | ∃ p, IsFemPieces Ω M S k u p ∧ ∀ T ∈ M.simplices, ∀ F ⊆ vertexSet T, F.card = n →
    F ∈ Γ → ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), TraceEq F k.toNat (p T x) 0}
-- palomar-shared-end: femSpace

/-! ### The Crank–Nicolson Whitney scheme ([QuennevilleBelair2015], Ch. 7) -/

/-- **The integral of a `k`-form over the oriented `k`-simplex** `p = (p₀, …, p_k)` in `ℝⁿ`:
`∫_p w = ∫_{T̂_k} w(F(x))(p₁ - p₀, …, p_k - p₀) dx` over the reference simplex
`T̂_k = {x ∈ ℝᵏ | xᵢ ≥ 0, Σ xᵢ ≤ 1}`, `F(x) = p₀ + Σᵢ xᵢ (pᵢ₊₁ - p₀)`. -/
def simplexIntegral {k : ℕ} (p : Fin (k + 1) → Fin n → ℝ) (w : FormField n) : ℝ :=
  ∫ x in {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1},
    covEval (w (p 0 + ∑ i, x i • (p i.succ - p 0))) fun i => p i.succ - p 0

/-- `x ∈ L²(Ω; Λᵏ)` is **the Whitney interpolant** `Π_h w` of the form field `w` on the mesh `M`
([Whitney1957], Ch. IV; [Arnold2018], Ch. 7): `x` lies in the Whitney space `P₁⁻Λᵏ(M)` with
pieces `p_T` having the degrees of freedom of `w`, `∫_f p_T = ∫_f w` on every oriented
`k`-face `f` of every simplex `T`. -/
def IsWhitneyInterp (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (k : ℕ) (w : FormField n)
    (x : L2Form Ω k) : Prop :=
  ∃ p, IsFemPieces Ω M topSeq k x p ∧ ∀ T ∈ M.simplices, ∀ q : Fin (k + 1) → Fin (n + 1),
    Function.Injective q → simplexIntegral (T.points ∘ q) (p T) = simplexIntegral (T.points ∘ q) w

/-- `x ∈ L²(Ω; Λᵏ)` is (almost everywhere) the form field `w` on `Ω`. -/
def IsRepr (Ω : Set (Fin n → ℝ)) (k : ℤ) (w : FormField n) (x : L2Form Ω k) : Prop :=
  ∀ s : FormIdx n k, ⇑(x s) =ᵐ[volume.restrict Ω] fun y => w y s.1

/-- A **row** `(σ, E, B)`: a `0`-form, a `1`-form and a `2`-form of `L²(Q)`, `Q = (0, ½)³`. -/
abbrev Row : Type := L2Form (cube 3) 0 × L2Form (cube 3) 1 × L2Form (cube 3) 2

/-- The `L²` inner product of rows. -/
def rowInner (x y : Row) : ℝ := ⟪x.1, y.1⟫_ℝ + ⟪x.2.1, y.2.1⟫_ℝ + ⟪x.2.2, y.2.2⟫_ℝ

open Classical in
/-- The weak exterior derivative `dx`, for `x` in its domain `HΛᵏ(Q)` (and `0` elsewhere; it is
only applied to finite element forms, which lie in `HΛᵏ(Q)`). -/
def wd (k : ℤ) (x : L2Form (cube 3) k) : L2Form (cube 3) (k + 1) :=
  if h : x ∈ (dMax (cube 3) k).domain then dMax (cube 3) k ⟨x, h⟩ else 0

/-- **The form of the Hodge wave operator** `A = 𝐝 - 𝐝*` on rows, `⟪A x, y⟫ = ⟪𝐝x, y⟫ - ⟪x, 𝐝y⟫`
for `𝐝(σ, E, B) = (0, dσ, dE)`: in vector proxies
`(grad σ, C) - (E, grad τ) + (curl E, D) - (B, curl C)`. -/
def waveForm (x y : Row) : ℝ :=
  ⟪wd 0 x.1, y.2.1⟫_ℝ + ⟪wd 1 x.2.1, y.2.2⟫_ℝ - ⟪x.2.1, wd 0 y.1⟫_ℝ - ⟪x.2.2, wd 1 y.2.1⟫_ℝ

/-- The row `x` lies in the Whitney spaces `Vₕ = P₁Λ⁰(M) × P₁⁻Λ¹(M) × P₁⁻Λ²(M)` (`b = false`),
or in the spaces `V̊ₕ` with vanishing boundary traces (`b = true`). -/
def RowMem (M : SimplicialMesh 3) (b : Bool) (x : Row) : Prop :=
  let V := femSpace (cube 3) M topSeq (if b then M.boundaryFacets else ∅)
  x.1 ∈ V 0 ∧ x.2.1 ∈ V 1 ∧ x.2.2 ∈ V 2

/-- **One Crank–Nicolson step with prescribed boundary degrees of freedom** on the mesh `M`
([QuennevilleBelair2015], Ch. 7): from `u` to `u' ∈ Vₕ` with the boundary degrees of freedom of
`g` (`u' - g ∈ V̊ₕ`), `⟪u' - u, v⟫ = (Δt / 2) ⟪A (u' + u), v⟫` for all `v ∈ V̊ₕ`. -/
def IsCNStep (M : SimplicialMesh 3) (Δt : ℝ) (g u u' : Row) : Prop :=
  RowMem M false u' ∧ RowMem M true (u' - g) ∧
    ∀ v, RowMem M true v → rowInner (u' - u) v = Δt / 2 * waveForm (u' + u) v

/-- A **smooth solution of the Hodge wave equation** `U' = (d - dᵗ) U` on the window
`Λ⁰ → Λ¹ → Λ²` of `ℝ³` (no boundary condition): forms `u t i` of degree `i` (`σ`, `E`, `B`), `C²`
in space and `C³` in time with jointly continuous time derivatives `u₁, u₂, u₃`, solving
`σ' = -dᵗE`, `E' = dσ - dᵗB`, `B' = dE` pointwise, with `‖Du‖, ‖D du‖ ≤ L` on `cl Q`, these
`L`-Lipschitz in `t ∈ [0, T]`, and `|∂ₜ³u| ≤ L` on `[0, T] × Q`. -/
structure RowSolution (T L : ℝ) where
  /-- the fields and their first three time derivatives -/
  u : ℝ → Fin 3 → FormField 3
  u₁ : ℝ → Fin 3 → FormField 3
  u₂ : ℝ → Fin 3 → FormField 3
  u₃ : ℝ → Fin 3 → FormField 3
  isDeg : ∀ t (i : Fin 3) y (s : Finset (Fin 3)), s.card ≠ i → u t i y s = 0
  contDiff : ∀ t i, ContDiff ℝ 2 (u t i)
  continuous₁ : ∀ i s, Continuous fun p : ℝ × (Fin 3 → ℝ) => u₁ p.1 i p.2 s
  continuous₂ : ∀ i s, Continuous fun p : ℝ × (Fin 3 → ℝ) => u₂ p.1 i p.2 s
  continuous₃ : ∀ i s, Continuous fun p : ℝ × (Fin 3 → ℝ) => u₃ p.1 i p.2 s
  hasDerivAt₁ : ∀ t i y s, HasDerivAt (fun τ => u τ i y s) (u₁ t i y s) t
  hasDerivAt₂ : ∀ t i y s, HasDerivAt (fun τ => u₁ τ i y s) (u₂ t i y s) t
  hasDerivAt₃ : ∀ t i y s, HasDerivAt (fun τ => u₂ τ i y s) (u₃ t i y s) t
  pde₀ : ∀ t, u₁ t 0 = -codiff (u t 1)
  pde₁ : ∀ t, u₁ t 1 = extDeriv (u t 0) - codiff (u t 2)
  pde₂ : ∀ t, u₁ t 2 = extDeriv (u t 1)
  bound : ∀ t ∈ Icc 0 T, ∀ i, ∀ y ∈ closure (cube 3),
    ‖fderiv ℝ (u t i) y‖ ≤ L ∧ ‖fderiv ℝ (extDeriv (u t i)) y‖ ≤ L
  lipschitz : ∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T, ∀ i, ∀ y ∈ closure (cube 3),
    ‖fderiv ℝ (u t' i) y - fderiv ℝ (u t i) y‖ ≤ L * |t' - t| ∧
      ‖fderiv ℝ (extDeriv (u t' i)) y - fderiv ℝ (extDeriv (u t i)) y‖ ≤ L * |t' - t|
  bound₃ : ∀ t ∈ Icc 0 T, ∀ i, ∀ y ∈ cube 3, ∀ s, |u₃ t i y s| ≤ L

/-- `x` is the Whitney interpolant of the row of form fields `w`. -/
def IsRowInterp (M : SimplicialMesh 3) (w : Fin 3 → FormField 3) (x : Row) : Prop :=
  IsWhitneyInterp (cube 3) M 0 (w 0) x.1 ∧ IsWhitneyInterp (cube 3) M 1 (w 1) x.2.1 ∧
    IsWhitneyInterp (cube 3) M 2 (w 2) x.2.2

/-- The `L²` norm `‖x‖ = (‖σ‖² + ‖E‖² + ‖B‖²)^{1/2}` of a row `x = (σ, E, B)`. -/
def rowNorm (x : Row) : ℝ := √(‖x.1‖ ^ 2 + ‖x.2.1‖ ^ 2 + ‖x.2.2‖ ^ 2)

/-- **One leapfrog step with prescribed boundary degrees of freedom** on the mesh `M`
([Joly2003]): from `u`, `u'` to `u'' ∈ Vₕ` with the boundary degrees of freedom of `g`
(`u'' - g ∈ V̊ₕ`), `⟪u'' - u, v⟫ = 2 Δt ⟪A u', v⟫` for all `v ∈ V̊ₕ`: the explicit three-level
scheme `uₙ₊₂ = uₙ + 2 Δt Aₕ uₙ₊₁` on the interior degrees of freedom (one solve with the mass
matrix). -/
def IsLeapfrogStep (M : SimplicialMesh 3) (Δt : ℝ) (g u u' u'' : Row) : Prop :=
  RowMem M false u'' ∧ RowMem M true (u'' - g) ∧
    ∀ v, RowMem M true v → rowInner (u'' - u) v = 2 * Δt * waveForm u' v

/-! ### The Whitney schemes on the cube -/

end FiniteElements

end TimeStepping
