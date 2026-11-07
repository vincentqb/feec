module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
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

/-!
# Error guarantees for fully discrete finite element schemes on simplicial meshes

Two finite element schemes on the cube `Q = (0, ½)³` with its **Freudenthal meshes** `𝒯_N`
(every simplex a Kuhn simplex `h (z + K_σ)`, `h = 1 / (2 (N + 1))`), with explicit spaces, an
explicit scheme and error bounds with constants independent of the mesh, the time step and the
solution: the numerical-analysis counterpart of the structure theory of `palomar/fem` and of the
time stepping of `palomar/timestepping`.

* `FEEC.crankNicolson_cube` (**the Crank–Nicolson Whitney scheme with Dirichlet degrees of
  freedom**, [QuennevilleBelair2015], Ch. 7): the Hodge wave equation of the de Rham window
  `HΛ⁰ → HΛ¹ → L²Λ²`, `σ' = -dᵗE`, `E' = dσ - dᵗB`, `B' = dE` (in vector proxies `σ' = div E`,
  `E' = grad σ - curl B`, `B' = curl E`), discretized by the Whitney elements
  `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ²` (Lagrange, Nédélec, Raviart–Thomas) and the Crank–Nicolson rule, the
  boundary degrees of freedom of every step taken from the exact solution (`IsCNStep`). The face
  integrals are unisolvent on the Whitney spaces, every step is uniquely solvable, and from the
  interpolant of the initial value the error after `M` steps of size `Δt ≤ T / M` is at most
  `C L (1 + T) (h_N + Δt²)` for smooth solutions (`RowSolution`, no boundary condition imposed).
* `FEEC.weakSymmetry_cube` (**the elements of Table 5.1 for the complex with weak symmetry**,
  [QuennevilleBelair2015], §5.3, §6.3): the mixed method (5.6) with `Sₕ = πS` for the complex
  `Γ → Ṽ¹ → W² × W̃²`, `Γ = {(σ, φ) | dσ = S⁰φ}`, of the linearized Einstein–Bianchi equations,
  the constraint imposed by a Lagrange multiplier (below). Its discrete problem is uniquely
  solvable, `Sₕ` is consistent at the order `h`, and the error is `O(h_N)` for `C²` and for `H¹`
  solutions; the semi-discrete wave problem (6.5) is uniquely solvable from its initial data and
  its error is `O((1 + t) h_N)`. `FEEC.weakSymmetry_cube_nonvacuous`: the hypotheses of the
  rates are met by nontrivial solutions.

**The complex with weak symmetry.** The BGG construction ([ArnoldHu2021]) couples two de Rham
complexes by connecting maps `S : Ṽⁱ → Vⁱ⁺¹` with `d S = -S d̃`; eliminating `Ṽ⁰` against `V¹`
weakly gives the saddle point problem (5.3) of [QuennevilleBelair2015]: find `σ ∈ V⁰`, `φ ∈ Ṽ⁰`,
`u ∈ Ṽ¹` and a multiplier `λ` with `⟪σ, τ⟫ - ⟪u, d̃ψ⟫ - ⟪λ, dτ - S⁰ψ⟫ = 0` for all `τ ∈ V⁰`,
`ψ ∈ Ṽ⁰`, `⟪d̃φ, v⟫ + ⟪S¹u, S¹v⟫ + ⟪d̃u, d̃v⟫ = F(v)` for all `v ∈ Ṽ¹`, and `dσ = S⁰φ`. On the
cube the rows are `H̊¹ → H̊(curl) → L²` and, in vector proxies, `S⁰ = I`, `S¹ = 2 vskw`, so
`Γ = {(σ, grad σ) | σ ∈ H̊²}`: a conforming discretization of `Γ` needs `C¹` elements, which the
multiplier avoids. The method replaces `S` by `Sₕ = πS` for cochain projections `π` (a
variational crime), and the compatibility condition (5.4) `π¹S⁰π̃⁰ = π¹S⁰` replaces the
surjectivity of `S⁰ₕ`. [AFW2007] derived the mixed methods for linear elasticity with weakly
imposed symmetry from the same two-row diagram at its other end; they are not formalized here.

## Conventions

Points of `ℝⁿ` are `Fin n → ℝ` (Lebesgue measure, sup norm). A `k`-form is given by its
coefficients `ω_s` on `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}`, `s = {s₁ < ⋯ < s_k} ⊆ Fin n`
(`FormIdx n k`); `L²(Ω; Λᵏ)` is the `ℓ²` sum of a copy of `L²(Ω)` per coefficient (`L2Form`) and
`L²(Ω; Λᵏ ⊗ ℝⁿ)` the `ℓ²` sum of `n` copies of it (`L2Vec`). With the sign
`ε(j, s) = (-1)^{#{l ∈ s | l < j}}`, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}` and
`(Σₐ dxₐ ∧ vₐ)_s = Σ_{a ∈ s} ε(a, s) (vₐ)_{s ∖ a}`. The definitions of differential forms,
polynomial forms, simplicial meshes, finite element spaces and Sobolev spaces are those of the
Palomar entry `palomar/fem`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 5 ((5.1)–(5.6), Thm 5.5, Table 5.1), Ch. 6 ((6.2)–(6.5), Prop 6.2), Ch. 7
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3–5
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3, §4, §5.5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6, 7
* [D. N. Arnold, R. S. Falk, R. Winther, *Mixed finite element methods for linear elasticity with weakly imposed symmetry*][AFW2007]
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021]
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [H. Whitney, *Geometric Integration Theory*][Whitney1957], Ch. IV
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
* [S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*][BrennerScott2008],
  Ch. 3, 4
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 1
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Filter Topology Set LinearPMap MeasureTheory

@[expose] public noncomputable section

namespace FEEC

/-! ### Differential forms on `ℝⁿ` and the `L²` de Rham complexes (from `palomar/fem`) -/

variable {n : ℕ}

/-- The index set of the coefficients of a `k`-form on `ℝⁿ`: the `k`-subsets
`s = {s₁ < ⋯ < s_k}` of `Fin n`, `s` indexing `dx_{s₁} ∧ ⋯ ∧ dx_{s_k}` (empty unless
`0 ≤ k ≤ n`). -/
abbrev FormIdx (n : ℕ) (k : ℤ) : Type := {s : Finset (Fin n) // (s.card : ℤ) = k}

/-- `L²(Ω; Λᵏ)`: the square-integrable `k`-forms on `Ω ⊆ ℝⁿ` (Lebesgue measure), the `ℓ²` sum
of a copy of `L²(Ω)` for each coefficient. -/
abbrev L2Form (Ω : Set (Fin n → ℝ)) (k : ℤ) : Type :=
  PiLp 2 fun _ : FormIdx n k => Lp ℝ 2 (volume.restrict Ω)

/-- A **form field** on `ℝⁿ`: at each point, a coefficient for every subset `s` of `Fin n` (the
coefficient of `dx_s`); it is a `k`-form when the coefficients off the `k`-subsets vanish. -/
abbrev FormField (n : ℕ) : Type := (Fin n → ℝ) → Finset (Fin n) → ℝ

/-- The sign `ε(j, s) = (-1)^{#{l ∈ s | l < j}}` of moving `dx_j` to its place in `dx_s`. -/
def sgn (j : Fin n) (s : Finset (Fin n)) : ℝ := (-1) ^ (s.filter fun l => l < j).card

/-- The partial derivative `∂_j f(x)`. -/
def partialDeriv (j : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single j 1)

/-- The **exterior derivative** of a form field, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`. -/
def extDeriv (w : FormField n) : FormField n :=
  fun x s => ∑ j ∈ s, sgn j s * partialDeriv j (fun y => w y (s.erase j)) x

/-- The **formal adjoint** of `d`, the codifferential `δ`,
`(dᵗψ)_s = -Σ_{j ∉ s} ε(j, s) ∂_j ψ_{s ∪ j}`: `∫ ⟨dφ, ψ⟩ = ∫ ⟨φ, dᵗψ⟩` for test forms. -/
def codiff (ψ : FormField n) : FormField n :=
  fun x s => -∑ j ∈ sᶜ, sgn j s * partialDeriv j (fun y => ψ y (insert j s)) x

/-- `f` is a **test function** on `Ω`: smooth, with compact support contained in `Ω`. -/
def IsTestFn (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω

/-- The graph `{(φ, dφ)}` of the exterior derivative on the test `k`-forms `φ ∈ C_c^∞(Ω; Λᵏ)`
(every coefficient a test function), as a subspace of `L²(Ω; Λᵏ) × L²(Ω; Λᵏ⁺¹)`. -/
def testGraph (Ω : Set (Fin n → ℝ)) (k : ℤ) : Submodule ℝ (L2Form Ω k × L2Form Ω (k + 1)) :=
  Submodule.span ℝ {p | ∃ φ : FormField n, (∀ s, IsTestFn Ω fun x => φ x s) ∧
    (∀ s : FormIdx n k, ⇑(p.1 s) =ᵐ[volume.restrict Ω] fun x => φ x s.1) ∧
    ∀ t : FormIdx n (k + 1), ⇑(p.2 t) =ᵐ[volume.restrict Ω] fun x => extDeriv φ x t.1}

/-- The graph `{(ψ, dᵗψ)}` of the formal adjoint on the test `(k + 1)`-forms, as a subspace of
`L²(Ω; Λᵏ⁺¹) × L²(Ω; Λᵏ)`. -/
def codiffGraph (Ω : Set (Fin n → ℝ)) (k : ℤ) : Submodule ℝ (L2Form Ω (k + 1) × L2Form Ω k) :=
  Submodule.span ℝ {p | ∃ ψ : FormField n, (∀ s, IsTestFn Ω fun x => ψ x s) ∧
    (∀ t : FormIdx n (k + 1), ⇑(p.1 t) =ᵐ[volume.restrict Ω] fun x => ψ x t.1) ∧
    ∀ s : FormIdx n k, ⇑(p.2 s) =ᵐ[volume.restrict Ω] fun x => codiff ψ x s.1}

/-- The **minimal exterior derivative** `d̊ : L²(Ω; Λᵏ) → L²(Ω; Λᵏ⁺¹)`, the closure of `d` on
test forms (the closure of the graph is a graph: `d` is closable, its formal adjoint being
densely defined): its domain is `H̊Λᵏ(Ω)` (for Lipschitz `Ω`, the forms of `HΛᵏ(Ω)` with vanishing
tangential trace) ([AFW2010], §4; [Arnold2018], Ch. 6). -/
def dMin (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Form Ω k →ₗ.[ℝ] L2Form Ω (k + 1) :=
  (testGraph Ω k).topologicalClosure.toLinearPMap

/-- The closure of the formal adjoint `dᵗ` on test `(k + 1)`-forms. -/
def codiffMin (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Form Ω (k + 1) →ₗ.[ℝ] L2Form Ω k :=
  (codiffGraph Ω k).topologicalClosure.toLinearPMap

/-- The **weak exterior derivative** `d : L²(Ω; Λᵏ) → L²(Ω; Λᵏ⁺¹)`, the adjoint of the formal
adjoint on test forms: `u ∈ D(d)` iff some `w ∈ L²(Ω; Λᵏ⁺¹)` has `⟪w, ψ⟫ = ⟪u, dᵗψ⟫` for every
test `(k + 1)`-form `ψ`, and then `du = w`. Its domain is `HΛᵏ(Ω)` ([AFW2010], §4;
[Arnold2018], Ch. 6). -/
def dMax (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Form Ω k →ₗ.[ℝ] L2Form Ω (k + 1) :=
  (codiffMin Ω k)†

/-! ### Polynomial differential forms ([AFW2006], §3) -/

/-- **Polynomial differential forms** on `ℝⁿ` in coordinates: a polynomial coefficient `ω_s` for
every subset `s` of `Fin n`, the form `Σ_s ω_s dx_s`. -/
abbrev PolyForm (n : ℕ) : Type := Finset (Fin n) → MvPolynomial (Fin n) ℝ

/-- `P_rΛᵏ`: the polynomial `k`-forms (`ω_s = 0` unless `#s = k`) with coefficients of degree at
most `r`. -/
def polyForm (r k : ℕ) : Submodule ℝ (PolyForm n) :=
  Submodule.pi Set.univ fun s =>
    if s.card = k then MvPolynomial.restrictTotalDegree (Fin n) ℝ r else ⊥

/-- `H_rΛᵏ`: the polynomial `k`-forms with coefficients homogeneous of degree `r`. -/
def homForm (r k : ℕ) : Submodule ℝ (PolyForm n) :=
  Submodule.pi Set.univ fun s =>
    if s.card = k then MvPolynomial.homogeneousSubmodule (Fin n) ℝ r else ⊥

/-- The **Koszul differential** `κ`, the contraction with the position vector field `x`:
`(κω)_s = Σ_{j ∉ s} ε(j, s) x_j ω_{s ∪ j}`. -/
def koszul : PolyForm n →ₗ[ℝ] PolyForm n :=
  LinearMap.pi fun s => ∑ j ∈ sᶜ,
    sgn j s • (LinearMap.mulLeft ℝ (MvPolynomial.X j) ∘ₗ LinearMap.proj (insert j s))

/-- `P_r⁻Λᵏ = P_{r-1}Λᵏ + κ H_{r-1}Λ^{k+1}`, the trimmed polynomial `k`-forms (`r ≥ 1`), and
`P_0⁻Λᵏ = 0` ([AFW2006], §3.3). -/
def polyFormMinus : ℕ → ℕ → Submodule ℝ (PolyForm n)
  | 0, _ => ⊥
  | r + 1, k => polyForm r k ⊔ (homForm r (k + 1)).map koszul

/-- The **evaluation** of a polynomial form: the form field `x ↦ (ω_s(x))_s`. -/
def evalForm : PolyForm n →ₗ[ℝ] FormField n :=
  LinearMap.pi fun x => LinearMap.pi fun s =>
    (MvPolynomial.aeval x).toLinearMap ∘ₗ LinearMap.proj s

/-- **An admissible sequence** of polynomial families ([AFW2006], §5; [AFW2010], §5.2): in every
form degree `k` the full space `P_{r_k}Λᵏ` (`full k = true`) or the trimmed space `P_{r_k}⁻Λᵏ`,
`r_k ≥ 1`, followed in degree `k + 1` by `P_{r_k}⁻Λᵏ⁺¹` or by `P_{r_k - 1}Λᵏ⁺¹`. (The piecewise
constants `P_0Λⁿ` are represented by the equal space `P_1⁻Λⁿ`; the spaces of degree `k > n`
are `0`.) -/
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
  (if S.full k then polyForm (n := n) (S.deg k) k else polyFormMinus (S.deg k) k).map evalForm

/-! ### Simplicial meshes -/

/-- The vertex set `{v₀, …, v_k}` of a simplex. -/
def vertexSet {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) : Finset (Fin n → ℝ) :=
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

/-- `h_T`: the diameter of the closed simplex `T`. -/
def diam {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) : ℝ := Metric.diam T.closedInterior

/-- The **mesh size** `h = max_T h_T`. -/
def meshSize (M : SimplicialMesh n) : ℝ :=
  ⨆ T : M.simplices, diam (T : Affine.Simplex ℝ (Fin n → ℝ) n)

/-- The mesh is **shape regular** with constant `σ` ([Ciarlet2002], §3.1): every simplex `T`
contains a ball `B(x, ρ)` with `h_T ≤ σ ρ`, that is `h_T / ρ_T ≤ σ` for the inradius `ρ_T` (the
largest radius of a ball in `T`). Balls and `h_T` are those of the sup norm (Conventions). -/
def IsShapeRegular (M : SimplicialMesh n) (σ : ℝ) : Prop :=
  ∀ T ∈ M.simplices, ∃ x ρ, 0 < ρ ∧ Metric.ball x ρ ⊆ T.closedInterior ∧ diam T ≤ σ * ρ

/-- The mesh is **quasi-uniform** with constant `q`: `q h ≤ h_T` for every simplex. -/
def IsQuasiUniform (M : SimplicialMesh n) (q : ℝ) : Prop :=
  ∀ T ∈ M.simplices, q * meshSize M ≤ diam T

/-- `M_N` is a **shape-regular, quasi-uniform family of meshes of `Ω`** with mesh size `h_N → 0`:
meshes of `Ω`, shape regular and quasi-uniform with constants independent of `N`. -/
def IsMeshFamily (Ω : Set (Fin n → ℝ)) (M : ℕ → SimplicialMesh n) : Prop :=
  (∀ N, (M N).domain = Ω) ∧
    (∃ σ q : ℝ, 0 < q ∧ ∀ N, IsShapeRegular (M N) σ ∧ IsQuasiUniform (M N) q) ∧
    (∀ N, 0 < meshSize (M N)) ∧ Tendsto (fun N => meshSize (M N)) atTop (𝓝 0)

/-- The cube `(0, ½)ⁿ`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := univ.pi fun _ => Ioo 0 (1 / 2)

/-- `𝒯` are **Freudenthal meshes** of the cube ([Freudenthal1942]): every simplex of `𝒯 N` is a
Kuhn simplex `h (z + K_σ)`, `h = 1 / (2 (N + 1))`, `z ∈ {0, …, N}ⁿ`, `σ ∈ 𝔖ₙ`, with vertices
`v_j = h (z + e_{σ 0} + ⋯ + e_{σ (j - 1)})`, `j = 0, …, n` (a mesh of `(0, ½)ⁿ` of such
simplices consists of all of them). -/
def IsFreudenthal (𝒯 : ℕ → SimplicialMesh n) : Prop :=
  ∀ N, ∀ T ∈ (𝒯 N).simplices, ∃ (z : Fin n → Fin (N + 1)) (σ : Equiv.Perm (Fin n)), ∀ j i,
    T.points j i = ((z i : ℝ) + if (σ.symm i : ℕ) < (j : ℕ) then 1 else 0) / (2 * (N + 1))

/-! ### The finite element spaces -/

/-- The value `α(v₁, …, v_k) = Σ_{#s = k} α_s det (v_l(s_i))_{i,l}` of the `k`-covector `α` on
the vectors `v₁, …, v_k`. -/
def covEval {k : ℕ} (α : Finset (Fin n) → ℝ) (v : Fin k → Fin n → ℝ) : ℝ :=
  ∑ s : Finset (Fin n), if h : s.card = k then
    α s * (Matrix.of fun i l => v l (s.orderEmbOfFin h i)).det else 0

/-- The `k`-covectors `α`, `β` have the **same tangential trace** on the face spanned by the
points `g`: they agree on all `k`-tuples of vectors tangent to the face. -/
def TraceEq (g : Finset (Fin n → ℝ)) (k : ℕ) (α β : Finset (Fin n) → ℝ) : Prop :=
  ∀ v : Fin k → Fin n → ℝ, (∀ l, v l ∈ vectorSpan ℝ (g : Set (Fin n → ℝ))) →
    covEval α v = covEval β v

/-- `p = (p_T)_T` are **finite element pieces** of `u ∈ L²(Ω; Λᵏ)` on the mesh `M` for the
sequence `S`: on every simplex `T`, `u` is (almost everywhere) the polynomial form `p_T ∈ S_k`,
and the tangential traces of `p_T` and `p_{T'}` agree on the common face of any two simplices. -/
def IsFemPieces (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (S : PolySeq) (k : ℤ)
    (u : L2Form Ω k) (p : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n) : Prop :=
  (∀ T ∈ M.simplices, p T ∈ S.space n k.toNat) ∧
    (∀ T ∈ M.simplices, ∀ s : FormIdx n k,
      ⇑(u s) =ᵐ[volume.restrict (Ω ∩ T.closedInterior)] fun x => p T x s.1) ∧
    ∀ T ∈ M.simplices, ∀ T' ∈ M.simplices,
      ∀ x ∈ convexHull ℝ ((vertexSet T ∩ vertexSet T' : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)),
        TraceEq (vertexSet T ∩ vertexSet T') k.toNat (p T x) (p T' x)

/-- **The finite element space** `S_k(M) ⊆ L²(Ω; Λᵏ)` of the admissible sequence `S` on the mesh
`M` ([AFW2006], §5; [Arnold2018], Ch. 7): the forms that are on every simplex a polynomial form
of `S_k`, with single-valued tangential traces on the faces of the mesh. -/
def femSpace (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (S : PolySeq) (k : ℤ) :
    Set (L2Form Ω k) :=
  {u | ∃ p, IsFemPieces Ω M S k u p}

/-- **The finite element space with vanishing boundary traces** `S̊_k(M)`: the forms of
`S_k(M)` whose tangential traces vanish on the boundary facets (the facets of a single simplex of
the mesh). -/
def femSpaceMin (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (S : PolySeq) (k : ℤ) :
    Set (L2Form Ω k) :=
  {u | ∃ p, IsFemPieces Ω M S k u p ∧ ∀ T ∈ M.simplices, ∀ F ⊆ vertexSet T, F.card = n →
    (∀ T' ∈ M.simplices, F ⊆ vertexSet T' → T' = T) →
      ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), TraceEq F k.toNat (p T x) 0}

/-- **The Whitney sequence** `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ² → P₁⁻Λ³` (Lagrange, Nédélec edge,
Raviart–Thomas face elements and piecewise constants; [Whitney1957], [AFW2006], §3–4). -/
def topSeq : PolySeq where
  full k := k == 0
  deg _ := 1
  one_le_deg _ := le_rfl
  transition _ := Or.inl ⟨rfl, rfl⟩

/-- `x ∈ L²(Ω; Λʲ)` **lies in `Hᵐ(Ω; Λʲ)` with norm at most `L`**, for `Hᵐ(Ω) = Hᵐ(ℝⁿ)|_Ω` (the
restriction definition, weak derivatives as in [Evans2010], §5.2; on Lipschitz domains, by
Stein's extension theorem, the space of weak derivatives in `L²(Ω)` with an equivalent norm): each
coefficient is the restriction of a function `D t []` on `ℝⁿ` with weak derivatives `D t l` in
`L²(ℝⁿ)` along the words `l` of length at most `m` (`∫ D t [] ∂_{l₁} ⋯ ∂_{l_p} φ =
(-1)^p ∫ D t l φ` for test functions `φ`), with `Σ_t Σ_{|l| ≤ m} ‖D t l‖² ≤ L²` (norm at most
`|L|`; a sum over words: a derivative of multi-index `α` is counted `|α|!/α!` times). -/
def IsSobolevForm (Ω : Set (Fin n → ℝ)) (m : ℕ) (j : ℤ) (L : ℝ) (x : L2Form Ω j) : Prop :=
  ∃ D : FormIdx n j → List (Fin n) → (Fin n → ℝ) → ℝ,
    (∀ t l, l.length ≤ m → MemLp (D t l) 2 volume ∧ ∀ φ, IsTestFn univ φ →
      ∫ y, D t [] y * l.foldr partialDeriv φ y = (-1) ^ l.length * ∫ y, D t l y * φ y) ∧
    ∑ t, ∑ p ∈ Finset.range (m + 1), ∑ l : Fin p → Fin n, ∫ y, D t (List.ofFn l) y ^ 2 ≤ L ^ 2 ∧
    ∀ t, ⇑(x t) =ᵐ[volume.restrict Ω] D t []

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
  let V := if b then femSpaceMin (cube 3) M topSeq else femSpace (cube 3) M topSeq
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

/-! ### Vector-valued forms and the connecting maps -/

/-- `L²(Ω; Λᵏ ⊗ ℝⁿ)`: the vectors `v = (v₀, …, v_{n-1})` of `k`-forms of `L²(Ω; Λᵏ)`, an `ℓ²`
sum. -/
abbrev L2Vec (Ω : Set (Fin n → ℝ)) (k : ℤ) : Type := PiLp 2 fun _ : Fin n => L2Form Ω k

/-- The operator `T` acting componentwise on vectors, with domain `D(T)ⁿ`. -/
def vecOp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (T : E →ₗ.[ℝ] F) :
    PiLp 2 (fun _ : Fin n => E) →ₗ.[ℝ] PiLp 2 (fun _ : Fin n => F) where
  domain :=
    { carrier := {v | ∀ a, v a ∈ T.domain}
      add_mem' := fun hv hw a => T.domain.add_mem (hv a) (hw a)
      zero_mem' := fun _ => T.domain.zero_mem
      smul_mem' := fun c _ hv a => T.domain.smul_mem c (hv a) }
  toFun :=
    { toFun := fun v => WithLp.toLp 2 fun a => T ⟨(v : PiLp 2 fun _ : Fin n => E) a, v.2 a⟩
      map_add' := fun v w => PiLp.ext fun a => T.map_add ⟨_, v.2 a⟩ ⟨_, w.2 a⟩
      map_smul' := fun c v => PiLp.ext fun a => T.map_smul c ⟨_, v.2 a⟩ }

/-- **The connecting map** `S v = Σₐ dxₐ ∧ vₐ : L²(Ω; Λᵏ ⊗ ℝⁿ) → L²(Ω; Λᵏ⁺¹)`,
`(S v)_s = Σ_{a ∈ s} ε(a, s) (vₐ)_{s ∖ a}`. On vector proxies, `S` is the identity `S⁰ = I` on
vector `0`-forms (`(S v)_{a} = vₐ`), and on vector `1`-forms `vₐ = Σ_b u_{ab} dx_b`,
`(S v)_{ab} = u_{ab} - u_{ba}`, i.e. `S¹ = 2 vskw` ([QuennevilleBelair2015], §5.3; [AFW2007]). -/
def wedge (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Vec Ω k →L[ℝ] L2Form Ω (k + 1) :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : FormIdx n (k + 1) =>
      Lp ℝ 2 (volume.restrict Ω)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun s => ∑ a : Fin n, if h : a ∈ s.1 then sgn a s.1 •
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : FormIdx n k => Lp ℝ 2 (volume.restrict Ω))
          ⟨s.1.erase a, by
            rw [Finset.card_erase_of_mem h, Nat.cast_sub (Finset.card_pos.2 ⟨a, h⟩), s.2]
            ring⟩) ∘L PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => L2Form Ω k) a) else 0

/-! ### BGG data with weak symmetry and their discretization -/

/-- **BGG data**: two segments `W⁰ → W¹ → W²` and `W̃⁰ → W̃¹ → W̃²` of densely defined operators
`d`, `d̃` between Hilbert spaces (`LinearPMap`s; their domains `V = D(d)` carry the inner product
of `W`), with bounded connecting maps `S⁰ : W̃⁰ → W¹`, `S¹ : W̃¹ → W²`. -/
structure WeakSymmetryData (W0 W1 W2 Wt0 Wt1 Wt2 : Type*) [NormedAddCommGroup W0]
    [InnerProductSpace ℝ W0] [NormedAddCommGroup W1] [InnerProductSpace ℝ W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0]
    [InnerProductSpace ℝ Wt0] [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1]
    [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2] where
  /-- the top row -/
  d0 : W0 →ₗ.[ℝ] W1
  d1 : W1 →ₗ.[ℝ] W2
  /-- the bottom row -/
  dt0 : Wt0 →ₗ.[ℝ] Wt1
  dt1 : Wt1 →ₗ.[ℝ] Wt2
  /-- the connecting maps -/
  S0 : Wt0 →L[ℝ] W1
  S1 : Wt1 →L[ℝ] W2

namespace WeakSymmetryData

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2)

/-- `(σ, φ, u)` with the multiplier `λ ∈ W¹` solves **the mixed problem (5.3)** with datum `F`
([QuennevilleBelair2015], (5.3), with an `L²` multiplier): `⟪σ, τ⟫ - ⟪u, d̃ψ⟫ - ⟪λ, dτ - S⁰ψ⟫ = 0`,
`⟪d̃φ, v⟫ + ⟪S¹u, S¹v⟫ + ⟪d̃u, d̃v⟫ = F v` for all `τ ∈ V⁰`, `ψ ∈ Ṽ⁰`, `v ∈ Ṽ¹`, and `dσ = S⁰φ`. -/
def IsSolution (F : D.dt1.domain →ₗ[ℝ] ℝ) (σ : D.d0.domain) (φ : D.dt0.domain)
    (u : D.dt1.domain) (lam : W1) : Prop :=
  (∀ (τ : D.d0.domain) (ψ : D.dt0.domain),
      ⟪(σ : W0), τ⟫_ℝ - ⟪(u : Wt1), D.dt0 ψ⟫_ℝ - ⟪lam, D.d0 τ - D.S0 ψ⟫_ℝ = 0) ∧
    (∀ v : D.dt1.domain,
      ⟪D.dt0 φ, v⟫_ℝ + ⟪D.S1 u, D.S1 v⟫_ℝ + ⟪D.dt1 u, D.dt1 v⟫_ℝ = F v) ∧
    D.d0 σ = D.S0 φ

/-- **A discretization** of `D` ([QuennevilleBelair2015], §5.2): finite-dimensional subspaces of
the domains forming subcomplexes of both rows, with bounded cochain projections `π : W → W` onto
them (identity on the subspaces, `d π = π d` on the domains). The method (5.6) couples the rows by
`S⁰ₕ = π¹S⁰`, `S¹ₕ = π²S¹`. -/
structure Discretization where
  /-- the finite element spaces -/
  V0 : Submodule ℝ W0
  V1 : Submodule ℝ W1
  V2 : Submodule ℝ W2
  Vt0 : Submodule ℝ Wt0
  Vt1 : Submodule ℝ Wt1
  Vt2 : Submodule ℝ Wt2
  [fd0 : FiniteDimensional ℝ V0]
  [fd1 : FiniteDimensional ℝ V1]
  [fd2 : FiniteDimensional ℝ V2]
  [fdt0 : FiniteDimensional ℝ Vt0]
  [fdt1 : FiniteDimensional ℝ Vt1]
  [fdt2 : FiniteDimensional ℝ Vt2]
  le0 : V0 ≤ D.d0.domain
  le1 : V1 ≤ D.d1.domain
  let0 : Vt0 ≤ D.dt0.domain
  let1 : Vt1 ≤ D.dt1.domain
  d0_mem : ∀ x : D.d0.domain, (x : W0) ∈ V0 → D.d0 x ∈ V1
  d1_mem : ∀ x : D.d1.domain, (x : W1) ∈ V1 → D.d1 x ∈ V2
  dt0_mem : ∀ x : D.dt0.domain, (x : Wt0) ∈ Vt0 → D.dt0 x ∈ Vt1
  dt1_mem : ∀ x : D.dt1.domain, (x : Wt1) ∈ Vt1 → D.dt1 x ∈ Vt2
  /-- the cochain projections -/
  π0 : W0 →L[ℝ] W0
  π1 : W1 →L[ℝ] W1
  π2 : W2 →L[ℝ] W2
  πt0 : Wt0 →L[ℝ] Wt0
  πt1 : Wt1 →L[ℝ] Wt1
  πt2 : Wt2 →L[ℝ] Wt2
  π0_mem : ∀ x, π0 x ∈ V0
  π1_mem : ∀ x, π1 x ∈ V1
  π2_mem : ∀ x, π2 x ∈ V2
  πt0_mem : ∀ x, πt0 x ∈ Vt0
  πt1_mem : ∀ x, πt1 x ∈ Vt1
  πt2_mem : ∀ x, πt2 x ∈ Vt2
  π0_id : ∀ x ∈ V0, π0 x = x
  π1_id : ∀ x ∈ V1, π1 x = x
  π2_id : ∀ x ∈ V2, π2 x = x
  πt0_id : ∀ x ∈ Vt0, πt0 x = x
  πt1_id : ∀ x ∈ Vt1, πt1 x = x
  πt2_id : ∀ x ∈ Vt2, πt2 x = x
  comm0 : ∀ x : D.d0.domain, D.d0 ⟨π0 x, le0 (π0_mem x)⟩ = π1 (D.d0 x)
  comm1 : ∀ x : D.d1.domain, D.d1 ⟨π1 x, le1 (π1_mem x)⟩ = π2 (D.d1 x)
  commt0 : ∀ x : D.dt0.domain, D.dt0 ⟨πt0 x, let0 (πt0_mem x)⟩ = πt1 (D.dt0 x)
  commt1 : ∀ x : D.dt1.domain, D.dt1 ⟨πt1 x, let1 (πt1_mem x)⟩ = πt2 (D.dt1 x)

namespace Discretization

variable {D} (Q : D.Discretization)

/-- The projections are **bounded by `C`**: `‖π‖ ≤ C`, `‖π̃‖ ≤ C` in every degree. -/
def IsBounded (C : ℝ) : Prop :=
  ‖Q.π0‖ ≤ C ∧ ‖Q.π1‖ ≤ C ∧ ‖Q.π2‖ ≤ C ∧ ‖Q.πt0‖ ≤ C ∧ ‖Q.πt1‖ ≤ C ∧ ‖Q.πt2‖ ≤ C

/-- **The compatibility condition (5.4)** `π¹S⁰π̃⁰ = π¹S⁰` ([QuennevilleBelair2015], (5.4)). -/
def Compatible : Prop := ∀ ψ, Q.π1 (D.S0 (Q.πt0 ψ)) = Q.π1 (D.S0 ψ)

/-- **Consistency of `Sₕ` at the order `h`** with constant `C` (cf. [QuennevilleBelair2015],
Prop 5.9): `‖(S⁰ - S⁰ₕ)ψ‖ ≤ C h ‖d̃ψ‖` on `Ṽₕ⁰`, and every `d̃v`, `v ∈ Ṽₕ¹`, has a **regular
potential** `w`, `d̃w = d̃v`, `‖w‖ ≤ C ‖d̃v‖`, on which `π̃¹` and `S¹ₕ` are accurate,
`‖(1 - π̃¹)w‖, ‖(S¹ - S¹ₕ)w‖ ≤ C h ‖d̃v‖`. -/
def IsConsistent (C h : ℝ) : Prop :=
  (∀ ψ : D.dt0.domain, (ψ : Wt0) ∈ Q.Vt0 → ‖D.S0 ψ - Q.π1 (D.S0 ψ)‖ ≤ C * h * ‖D.dt0 ψ‖) ∧
    ∀ v : D.dt1.domain, (v : Wt1) ∈ Q.Vt1 → ∃ w : D.dt1.domain, D.dt1 w = D.dt1 v ∧
      ‖(w : Wt1)‖ ≤ C * ‖D.dt1 v‖ ∧ ‖(w : Wt1) - Q.πt1 w‖ ≤ C * h * ‖D.dt1 v‖ ∧
      ‖D.S1 w - Q.π2 (D.S1 w)‖ ≤ C * h * ‖D.dt1 v‖

/-- `(σₕ, φₕ, uₕ, λₕ) ∈ Vₕ⁰ × Ṽₕ⁰ × Ṽₕ¹ × Vₕ¹` solves **the discrete problem (5.6)** with datum
`F`: (5.3) on the discrete spaces with `S⁰ₕ = π¹S⁰`, `S¹ₕ = π²S¹` in place of `S⁰`, `S¹`. -/
def IsDiscreteSolution (F : D.dt1.domain →ₗ[ℝ] ℝ) (σ : D.d0.domain) (φ : D.dt0.domain)
    (u : D.dt1.domain) (lam : W1) : Prop :=
  (σ : W0) ∈ Q.V0 ∧ (φ : Wt0) ∈ Q.Vt0 ∧ (u : Wt1) ∈ Q.Vt1 ∧ lam ∈ Q.V1 ∧
    (∀ (τ : D.d0.domain) (ψ : D.dt0.domain), (τ : W0) ∈ Q.V0 → (ψ : Wt0) ∈ Q.Vt0 →
      ⟪(σ : W0), τ⟫_ℝ - ⟪(u : Wt1), D.dt0 ψ⟫_ℝ - ⟪lam, D.d0 τ - Q.π1 (D.S0 ψ)⟫_ℝ = 0) ∧
    (∀ v : D.dt1.domain, (v : Wt1) ∈ Q.Vt1 → ⟪D.dt0 φ, v⟫_ℝ +
      ⟪Q.π2 (D.S1 u), Q.π2 (D.S1 v)⟫_ℝ + ⟪D.dt1 u, D.dt1 v⟫_ℝ = F v) ∧
    D.d0 σ = Q.π1 (D.S0 φ)

/-- The squared **error** in the graph norms of `V⁰`, `Ṽ⁰` and in `‖w‖² + ‖S¹ₕw‖² + ‖d̃w‖²` on
`Ṽ¹`. -/
def errorSq (σ σh : D.d0.domain) (φ φh : D.dt0.domain) (u uh : D.dt1.domain) : ℝ :=
  ‖((σ - σh : D.d0.domain) : W0)‖ ^ 2 + ‖D.d0 (σ - σh)‖ ^ 2 +
    ‖((φ - φh : D.dt0.domain) : Wt0)‖ ^ 2 + ‖D.dt0 (φ - φh)‖ ^ 2 +
    ‖((u - uh : D.dt1.domain) : Wt1)‖ ^ 2 + ‖Q.π2 (D.S1 (u - uh))‖ ^ 2 + ‖D.dt1 (u - uh)‖ ^ 2

end Discretization

/-- `x` is **continuous on `[0, T]` with right derivative `x'` on `[0, T)`**, `x'` continuous on
`[0, T]`. -/
def IsC1On {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ) (x x' : ℝ → E) : Prop :=
  ContinuousOn x (Icc 0 T) ∧ ContinuousOn x' (Icc 0 T) ∧
    ∀ t ∈ Ico 0 T, HasDerivWithinAt x (x' t) (Ici t) t

/-- A **classical solution of the wave problem (6.2)** on `[0, T]` with source `f` and an `L²`
multiplier `λ` ([QuennevilleBelair2015], (6.2)): paths `σ` in `D(d⁰)`, `φ` in `D(d̃⁰)`, `u` in
`D(d̃¹)`, `M` in `W²`, `ρ` in `W̃²`, `λ` in `W¹`, with `L²`-continuous right derivatives
`σ', u', M', ρ', λ'` and `(d̃φ)' = d̃φ'`, `(d̃u)' = d̃u'` (the energy class of the thesis), such
that on `[0, T)`, for all `τ ∈ D(d⁰)`, `ψ ∈ D(d̃⁰)`, `v ∈ D(d̃¹)`:
`⟪σ', τ⟫ - ⟪u, d̃ψ⟫ - ⟪λ, dτ - S⁰ψ⟫ = 0`, `⟪u', v⟫ + ⟪d̃φ, v⟫ + ⟪M, S¹v⟫ + ⟪ρ, d̃v⟫ = ⟪f, v⟫`,
`M' = S¹u`, `ρ' = d̃u`; and on `[0, T]` the constraint `dσ = S⁰φ`, also for `σ'`, `φ'`. -/
def IsWaveSolution (T : ℝ) (f : ℝ → Wt1) (σ σ' : ℝ → D.d0.domain) (φ φ' : ℝ → D.dt0.domain)
    (u u' : ℝ → D.dt1.domain) (M M' : ℝ → W2) (ρ ρ' : ℝ → Wt2) (lam lam' : ℝ → W1) : Prop :=
  IsC1On T σ σ' ∧ IsC1On T u u' ∧
    IsC1On T (fun t => D.dt0 (φ t)) (fun t => D.dt0 (φ' t)) ∧
    IsC1On T (fun t => D.dt1 (u t)) (fun t => D.dt1 (u' t)) ∧ IsC1On T M M' ∧ IsC1On T ρ ρ' ∧
    IsC1On T lam lam' ∧
    (∀ t ∈ Ico 0 T, (∀ (τ : D.d0.domain) (ψ : D.dt0.domain), ⟪(σ' t : W0), τ⟫_ℝ -
        ⟪(u t : Wt1), D.dt0 ψ⟫_ℝ - ⟪lam t, D.d0 τ - D.S0 ψ⟫_ℝ = 0) ∧
      (∀ v : D.dt1.domain, ⟪(u' t : Wt1), v⟫_ℝ + ⟪D.dt0 (φ t), v⟫_ℝ + ⟪M t, D.S1 v⟫_ℝ +
        ⟪ρ t, D.dt1 v⟫_ℝ = ⟪f t, v⟫_ℝ) ∧ M' t = D.S1 (u t) ∧ ρ' t = D.dt1 (u t)) ∧
    ∀ t ∈ Icc 0 T, D.d0 (σ t) = D.S0 (φ t) ∧ D.d0 (σ' t) = D.S0 (φ' t)

variable {D} in
/-- `(σₕ, φₕ, uₕ, Mₕ, ρₕ, λₕ)` solves **the semi-discrete problem (6.5)** of `Q` on `[0, T]`
([QuennevilleBelair2015], (6.3), (6.5)): values in `Vₕ⁰ × Ṽₕ⁰ × Ṽₕ¹ × Vₕ² × Ṽₕ² × Vₕ¹`, `σₕ, uₕ,
Mₕ, ρₕ` continuous on `[0, T]` and right-differentiable on `[0, T)`, where (6.2) holds on the
discrete spaces with `S⁰ₕ = π¹S⁰`, `S¹ₕ = π²S¹` (`φₕ` and `λₕ` are algebraic unknowns). -/
def Discretization.IsDiscreteWave (Q : D.Discretization) (T : ℝ) (f : ℝ → Wt1)
    (σ : ℝ → D.d0.domain) (φ : ℝ → D.dt0.domain) (u : ℝ → D.dt1.domain) (M : ℝ → W2)
    (ρ : ℝ → Wt2) (lam : ℝ → W1) : Prop :=
  ContinuousOn (fun t => (σ t : W0)) (Icc 0 T) ∧ ContinuousOn (fun t => (u t : Wt1)) (Icc 0 T) ∧
    ContinuousOn M (Icc 0 T) ∧ ContinuousOn ρ (Icc 0 T) ∧
    (∀ t ∈ Icc 0 T, (σ t : W0) ∈ Q.V0 ∧ (φ t : Wt0) ∈ Q.Vt0 ∧ (u t : Wt1) ∈ Q.Vt1 ∧
      M t ∈ Q.V2 ∧ ρ t ∈ Q.Vt2 ∧ lam t ∈ Q.V1 ∧ D.d0 (σ t) = Q.π1 (D.S0 (φ t))) ∧
    ∃ (σ' : ℝ → W0) (u' : ℝ → Wt1) (M' : ℝ → W2) (ρ' : ℝ → Wt2), ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => (σ s : W0)) (σ' t) (Ici t) t ∧
      HasDerivWithinAt (fun s => (u s : Wt1)) (u' t) (Ici t) t ∧
      HasDerivWithinAt M (M' t) (Ici t) t ∧ HasDerivWithinAt ρ (ρ' t) (Ici t) t ∧
      (∀ (τ : D.d0.domain) (ψ : D.dt0.domain), (τ : W0) ∈ Q.V0 → (ψ : Wt0) ∈ Q.Vt0 →
        ⟪σ' t, τ⟫_ℝ - ⟪(u t : Wt1), D.dt0 ψ⟫_ℝ - ⟪lam t, D.d0 τ - Q.π1 (D.S0 ψ)⟫_ℝ = 0) ∧
      (∀ v : D.dt1.domain, (v : Wt1) ∈ Q.Vt1 → ⟪u' t, v⟫_ℝ + ⟪D.dt0 (φ t), v⟫_ℝ +
        ⟪M t, Q.π2 (D.S1 v)⟫_ℝ + ⟪ρ t, D.dt1 v⟫_ℝ = ⟪f t, v⟫_ℝ) ∧
      (∀ z ∈ Q.V2, ⟪M' t, z⟫_ℝ = ⟪Q.π2 (D.S1 (u t)), z⟫_ℝ) ∧
      ∀ z ∈ Q.Vt2, ⟪ρ' t, z⟫_ℝ = ⟪D.dt1 (u t), z⟫_ℝ

end WeakSymmetryData

/-! ### The cube: the BGG data (4.16) and the elements of Table 5.1 -/

/-- **The bottom row of Table 5.1**, `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₁⁻Λ³` (Lagrange `P₂`, second-order
Nédélec edge elements of the first kind, `BDM₁` and piecewise constants). -/
def bottomSeq : PolySeq where
  full k := k == 0 || k == 2
  deg k := if k ≤ 1 then 2 else 1
  one_le_deg
    | 0 => Nat.le_succ 1
    | 1 => Nat.le_succ 1
    | _ + 2 => le_rfl
  transition
    | 0 => Or.inl ⟨rfl, rfl⟩
    | 1 => Or.inr ⟨rfl, rfl⟩
    | 2 => Or.inl ⟨rfl, rfl⟩
    | _ + 3 => Or.inl ⟨rfl, rfl⟩

/-- **The BGG data (4.16) on the cube** `Q = (0, ½)³` with the thesis' boundary conditions
([QuennevilleBelair2015], §5.3): the top row `H̊Λ⁰(Q) → H̊Λ¹(Q) → L²Λ²(Q)` and, componentwise, the
bottom row `H̊Λ⁰(Q) ⊗ ℝ³ → H̊Λ¹(Q) ⊗ ℝ³ → L²Λ²(Q) ⊗ ℝ³` of the minimal exterior derivative, with
`S⁰ = S¹ = Σₐ dxₐ ∧ ·` (`wedge`). In vector proxies the rows are `H̊¹ → H̊(curl) → L²(ℝ³)` and
`S⁰ = I`, `S¹ = 2 vskw`. -/
def cubeData : WeakSymmetryData (L2Form (cube 3) 0) (L2Form (cube 3) 1) (L2Form (cube 3) 2)
    (L2Vec (cube 3) 0) (L2Vec (cube 3) 1) (L2Vec (cube 3) 2) :=
  ⟨dMin (cube 3) 0, dMin (cube 3) 1, vecOp (dMin (cube 3) 0), vecOp (dMin (cube 3) 1),
    wedge (cube 3) 0, wedge (cube 3) 1⟩

/-- `x ∈ L²(Q; Λʲ)` on the cube `Q = (0, ½)ⁿ` is (almost everywhere) a `C²` form `w` on `ℝⁿ` of
degree `j` whose **tangential components vanish on `∂Q`** (`(w y)_t = 0` for `y ∈ cl Q` on a face
`y_i ∈ {0, ½}` with `i ∉ t`; no condition on the normal components), the values and first
derivatives of `w` and `dw` being bounded by `L` on `cl Q`. -/
def IsTangentialC2 (j : ℤ) (L : ℝ) (x : L2Form (cube n) j) : Prop :=
  ∃ w : FormField n, ContDiff ℝ 2 w ∧ (∀ y (t : Finset (Fin n)), (t.card : ℤ) ≠ j → w y t = 0) ∧
    (∀ y ∈ closure (cube n), ∀ (i : Fin n) (t : Finset (Fin n)), i ∉ t →
      (y i = 0 ∨ y i = 1 / 2) → w y t = 0) ∧
    (∀ m ≤ 1, ∀ y ∈ closure (cube n),
      ‖iteratedFDeriv ℝ m w y‖ ≤ L ∧ ‖iteratedFDeriv ℝ m (extDeriv w) y‖ ≤ L) ∧
    ∀ t : FormIdx n j, ⇑(x t) =ᵐ[volume.restrict (cube n)] fun y => w y t.1

/-- A state `(σ, φ, u, M, ρ)` of the cube is **regular with bound `L`**: all components are
`IsTangentialC2` with bound `L`. -/
def IsRegularState (L : ℝ) (σ : L2Form (cube 3) 0) (φ : L2Vec (cube 3) 0) (u : L2Vec (cube 3) 1)
    (M : L2Form (cube 3) 2) (ρ : L2Vec (cube 3) 2) : Prop :=
  IsTangentialC2 0 L σ ∧ (∀ a, IsTangentialC2 0 L (φ a)) ∧ (∀ a, IsTangentialC2 1 L (u a)) ∧
    IsTangentialC2 2 L M ∧ ∀ a, IsTangentialC2 2 L (ρ a)

/-- A state `(σ, φ, u, M, ρ)` of the cube is **of class `H¹` with bound `L`**: `σ`, the `uₐ`, `M`
and the `ρₐ` lie in `H¹(Q)` with norms at most `L` (`IsSobolevForm`), so do the `d̊φₐ` and `d̊uₐ`
(when `φₐ`, `uₐ` lie in the domain of `dMin`), and `M` and the `ρₐ` have vanishing tangential
traces: they lie in `H̊Λ²(Q)`, the domain of `dMin`. -/
def IsH1State (L : ℝ) (σ : L2Form (cube 3) 0) (φ : L2Vec (cube 3) 0) (u : L2Vec (cube 3) 1)
    (M : L2Form (cube 3) 2) (ρ : L2Vec (cube 3) 2) : Prop :=
  IsSobolevForm (cube 3) 1 0 L σ ∧
    (∀ a (h : φ a ∈ (dMin (cube 3) 0).domain),
      IsSobolevForm (cube 3) 1 1 L (dMin (cube 3) 0 ⟨φ a, h⟩)) ∧
    (∀ a, IsSobolevForm (cube 3) 1 1 L (u a)) ∧
    (∀ a (h : u a ∈ (dMin (cube 3) 1).domain),
      IsSobolevForm (cube 3) 1 2 L (dMin (cube 3) 1 ⟨u a, h⟩)) ∧
    IsSobolevForm (cube 3) 1 2 L M ∧ (∀ a, IsSobolevForm (cube 3) 1 2 L (ρ a)) ∧
    M ∈ (dMin (cube 3) 2).domain ∧ ∀ a, ρ a ∈ (dMin (cube 3) 2).domain

/-! ### The theorems -/

/-- **`O(h + Δt²)` convergence of the Crank–Nicolson Whitney scheme with Dirichlet degrees of
freedom** ([QuennevilleBelair2015], Ch. 7; [Arnold2018], Ch. 7; [Monk2003]; [Thomee2006], Ch. 1). The cube
`Q = (0, ½)³` carries a shape-regular, quasi-uniform family of Freudenthal meshes `𝒯_N`,
`h_N → 0`, on which:

* (**unisolvence**) every continuous form field `w` has exactly one Whitney interpolant `Π_h w`
  in each degree `k` (the form of `P₁⁻Λᵏ(𝒯_N)` with the face integrals of `w`);
* (**well-posedness**) for every time step `Δt` and all rows `g`, `u` of the Whitney spaces `Vₕ`
  the Crank–Nicolson step from `u` with the boundary degrees of freedom of `g` has exactly one
  solution, and `V̊ₕ¹ ≠ 0`;
* (**the error**) there is `C` such that, for every smooth solution `U` of the Hodge wave equation
  on `[0, T] × cl Q` with bound `L` (`RowSolution`), every `Δt > 0` and `M Δt ≤ T`, the iterates
  `uₙ` of the scheme started from `u₀ = Π_h U(0)` with the boundary degrees of freedom of
  `Π_h U(tₙ)` (`gₙ - Π_h U(tₙ) ∈ V̊ₕ`, `tₙ = n Δt`) satisfy
  `‖u_M - U(t_M)‖_{L²} ≤ C L (1 + T) (h_N + Δt²)`, `C` independent of `N`, `Δt`, `T`, `L`, `U`. -/
theorem crankNicolson_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3) (C : ℝ), IsMeshFamily (cube 3) 𝒯 ∧
    IsFreudenthal 𝒯 ∧
    (∀ N k (w : FormField 3), Continuous w → ∃! x, IsWhitneyInterp (cube 3) (𝒯 N) k w x) ∧
    (∀ N Δt g u, RowMem (𝒯 N) false g → RowMem (𝒯 N) false u → ∃! u', IsCNStep (𝒯 N) Δt g u u') ∧
    (∀ N, ∃ v ∈ femSpaceMin (cube 3) (𝒯 N) topSeq 1, v ≠ 0) ∧
    ∀ N T L (X : RowSolution T L) (Δt : ℝ) (M : ℕ) (u g : ℕ → Row), 0 < Δt → M * Δt ≤ T →
      (∀ m < M, IsCNStep (𝒯 N) Δt (g (m + 1)) (u m) (u (m + 1))) →
      (∀ m < M, ∃ w, IsRowInterp (𝒯 N) (X.u ((m + 1 : ℕ) * Δt)) w ∧
        RowMem (𝒯 N) true (g (m + 1) - w)) →
      IsRowInterp (𝒯 N) (X.u 0) (u 0) → ∀ U : Row, IsRepr (cube 3) 0 (X.u (M * Δt) 0) U.1 →
        IsRepr (cube 3) 1 (X.u (M * Δt) 1) U.2.1 → IsRepr (cube 3) 2 (X.u (M * Δt) 2) U.2.2 →
        √(‖(u M - U).1‖ ^ 2 + ‖(u M - U).2.1‖ ^ 2 + ‖(u M - U).2.2‖ ^ 2) ≤
          C * L * (1 + T) * (meshSize (𝒯 N) + Δt ^ 2) := by
  sorry

/-- **The finite element method of Table 5.1 for the complex with weak symmetry on the cube**
([QuennevilleBelair2015], §5.3, Table 5.1, Thm 5.5, §6.3, Prop 6.2; [AFW2010], §5.5;
[ChristiansenWinther2008]). The cube `Q = (0, ½)³` carries a shape-regular, quasi-uniform family
of Freudenthal meshes `𝒯_N`, `h_N → 0`, and discretizations `Q_N` of `cubeData` whose spaces
are the elements of Table 5.1 with vanishing boundary traces (`femSpaceMin` of `topSeq`, and of
`bottomSeq` in each component), with projections bounded by one constant `C`, satisfying (5.4),
such that:

* (**consistency**) `Sₕ = πS` is consistent at the order `h_N` with constant `C`;
* (**well-posedness**) the discrete problem (5.6) has exactly one solution for every datum `F`;
* (**static rates**) for every solution of (5.3) with `‖λ‖ ≤ L` whose components `σ`, `φₐ`, `uₐ`
  are `C²` up to `∂Q` with vanishing tangential traces and bound `L`, or whose components `σ`,
  `φₐ`, `d̃φₐ`, `uₐ`, `d̃uₐ` lie in `H¹(Q)` with norms at most `L`, the solution of (5.6) has
  `errorSq ≤ (K L h_N)²`;
* (**wave**) solutions of the semi-discrete problem (6.5) are determined on `[0, T]` by
  `(σₕ, uₕ, Mₕ, ρₕ)(0)` (and `φₕ`, `λₕ` on `[0, T)`), and for every classical solution of
  (6.2) whose states and their time derivatives are regular (`IsRegularState`) or of class `H¹`
  (`IsH1State`) with bound `L` and whose multipliers are bounded by `L`, some solution of (6.5)
  (the one starting from the elliptic projection of the exact data, [QuennevilleBelair2015],
  (6.4)) has `(‖σ - σₕ‖² + ‖u - uₕ‖² + ‖M - Mₕ‖² + ‖ρ - ρₕ‖²)^{1/2} ≤ K L (1 + t) h_N` on
  `[0, T]`.

The projections are asserted, not named (in the proof, the smoothed projections of one smoother
for both rows); the method (5.6) depends on them through `Sₕ = πS`. -/
theorem weakSymmetry_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3) (Q : ℕ → cubeData.Discretization)
    (C : ℝ), IsMeshFamily (cube 3) 𝒯 ∧ IsFreudenthal 𝒯 ∧
    (∀ N, ((Q N).V0 : Set (L2Form (cube 3) 0)) = femSpaceMin (cube 3) (𝒯 N) topSeq 0 ∧
      ((Q N).V1 : Set (L2Form (cube 3) 1)) = femSpaceMin (cube 3) (𝒯 N) topSeq 1 ∧
      ((Q N).V2 : Set (L2Form (cube 3) 2)) = femSpaceMin (cube 3) (𝒯 N) topSeq 2 ∧
      ((Q N).Vt0 : Set (L2Vec (cube 3) 0)) =
        {v | ∀ a, v a ∈ femSpaceMin (cube 3) (𝒯 N) bottomSeq 0} ∧
      ((Q N).Vt1 : Set (L2Vec (cube 3) 1)) =
        {v | ∀ a, v a ∈ femSpaceMin (cube 3) (𝒯 N) bottomSeq 1} ∧
      ((Q N).Vt2 : Set (L2Vec (cube 3) 2)) =
        {v | ∀ a, v a ∈ femSpaceMin (cube 3) (𝒯 N) bottomSeq 2}) ∧
    (∀ N, (Q N).IsBounded C ∧ (Q N).Compatible ∧ (Q N).IsConsistent C (meshSize (𝒯 N))) ∧
    (∀ N F, ∃! x : cubeData.d0.domain × cubeData.dt0.domain × cubeData.dt1.domain ×
      L2Form (cube 3) 1, (Q N).IsDiscreteSolution F x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
    (∃ K, ∀ N F σ φ u lam σh φh uh lamh L, cubeData.IsSolution F σ φ u lam →
      IsTangentialC2 0 L (σ : L2Form (cube 3) 0) →
      (∀ a, IsTangentialC2 0 L ((φ : L2Vec (cube 3) 0) a)) →
      (∀ a, IsTangentialC2 1 L ((u : L2Vec (cube 3) 1) a)) → ‖lam‖ ≤ L →
      (Q N).IsDiscreteSolution F σh φh uh lamh →
      (Q N).errorSq σ σh φ φh u uh ≤ (K * L * meshSize (𝒯 N)) ^ 2) ∧
    (∃ K, ∀ N F σ φ u lam σh φh uh lamh L, cubeData.IsSolution F σ φ u lam →
      IsSobolevForm (cube 3) 1 0 L (σ : L2Form (cube 3) 0) →
      (∀ a, IsSobolevForm (cube 3) 1 0 L ((φ : L2Vec (cube 3) 0) a)) →
      (∀ a, IsSobolevForm (cube 3) 1 1 L (cubeData.dt0 φ a)) →
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((u : L2Vec (cube 3) 1) a)) →
      (∀ a, IsSobolevForm (cube 3) 1 2 L (cubeData.dt1 u a)) → ‖lam‖ ≤ L →
      (Q N).IsDiscreteSolution F σh φh uh lamh →
      (Q N).errorSq σ σh φ φh u uh ≤ (K * L * meshSize (𝒯 N)) ^ 2) ∧
    (∀ N T f σ φ u M ρ lam σ' φ' u' M' ρ' lam', 0 < T → ContinuousOn f (Icc 0 T) →
      (Q N).IsDiscreteWave T f σ φ u M ρ lam → (Q N).IsDiscreteWave T f σ' φ' u' M' ρ' lam' →
      σ 0 = σ' 0 → u 0 = u' 0 → M 0 = M' 0 → ρ 0 = ρ' 0 →
      (∀ t ∈ Icc 0 T, σ t = σ' t ∧ u t = u' t ∧ M t = M' t ∧ ρ t = ρ' t) ∧
        ∀ t ∈ Ico 0 T, φ t = φ' t ∧ lam t = lam' t) ∧
    (∃ K, ∀ N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, 0 < T → ContinuousOn f (Icc 0 T) →
      cubeData.IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' →
      (∀ t ∈ Icc 0 T, IsRegularState L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsRegularState L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) →
      ∃ σh φh uh Mh ρh lamh, (Q N).IsDiscreteWave T f σh φh uh Mh ρh lamh ∧
        ∀ t ∈ Icc 0 T, √(‖(σ t : L2Form (cube 3) 0) - σh t‖ ^ 2 +
          ‖(u t : L2Vec (cube 3) 1) - uh t‖ ^ 2 + ‖M t - Mh t‖ ^ 2 + ‖ρ t - ρh t‖ ^ 2) ≤
            K * L * (1 + t) * meshSize (𝒯 N)) ∧
    ∃ K, ∀ N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, 0 < T → ContinuousOn f (Icc 0 T) →
      cubeData.IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' →
      (∀ t ∈ Icc 0 T, IsH1State L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsH1State L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) →
      ∃ σh φh uh Mh ρh lamh, (Q N).IsDiscreteWave T f σh φh uh Mh ρh lamh ∧
        ∀ t ∈ Icc 0 T, √(‖(σ t : L2Form (cube 3) 0) - σh t‖ ^ 2 +
          ‖(u t : L2Vec (cube 3) 1) - uh t‖ ^ 2 + ‖M t - Mh t‖ ^ 2 + ‖ρ t - ρh t‖ ^ 2) ≤
            K * L * (1 + t) * meshSize (𝒯 N) := by
  sorry

/-- **Non-vacuity of the rates of `FEEC.weakSymmetry_cube`**: (5.3) on the cube has a smooth
solution with `σ`, `φ`, `u` and `λ` all nonzero satisfying the hypotheses of both static rates
(`C²` and `H¹`) for some `L`; and for every `T > 0`, (6.2) has a classical solution on `[0, T]`,
with `u(t) ≠ 0` for all `t` and `σ(t), φ(t) ≠ 0` for `t ∈ (0, T]`, satisfying the hypotheses of
both wave rates (`IsRegularState` and `IsH1State`) for some `L`. -/
theorem weakSymmetry_cube_nonvacuous :
    (∃ F σ φ u lam L, cubeData.IsSolution F σ φ u lam ∧ (σ : L2Form (cube 3) 0) ≠ 0 ∧
      (φ : L2Vec (cube 3) 0) ≠ 0 ∧ (u : L2Vec (cube 3) 1) ≠ 0 ∧ lam ≠ 0 ∧
      IsTangentialC2 0 L (σ : L2Form (cube 3) 0) ∧
      (∀ a, IsTangentialC2 0 L ((φ : L2Vec (cube 3) 0) a)) ∧
      (∀ a, IsTangentialC2 1 L ((u : L2Vec (cube 3) 1) a)) ∧ ‖lam‖ ≤ L ∧
      IsSobolevForm (cube 3) 1 0 L (σ : L2Form (cube 3) 0) ∧
      (∀ a, IsSobolevForm (cube 3) 1 0 L ((φ : L2Vec (cube 3) 0) a)) ∧
      (∀ a, IsSobolevForm (cube 3) 1 1 L (cubeData.dt0 φ a)) ∧
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((u : L2Vec (cube 3) 1) a)) ∧
      ∀ a, IsSobolevForm (cube 3) 1 2 L (cubeData.dt1 u a)) ∧
    ∀ T, 0 < T → ∃ f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, ContinuousOn f (Icc 0 T) ∧
      cubeData.IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' ∧
      (∀ t ∈ Icc 0 T, IsRegularState L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsRegularState L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧
        IsH1State L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsH1State L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) ∧
      (∀ t, (u t : L2Vec (cube 3) 1) ≠ 0) ∧
      ∀ t ∈ Ioc 0 T, (σ t : L2Form (cube 3) 0) ≠ 0 ∧ (φ t : L2Vec (cube 3) 0) ≠ 0 := by
  sorry

end FEEC
