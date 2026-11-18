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
# What the weak-symmetry finite element method computes for the linearized Einstein–Bianchi equations

The linearized Einstein–Bianchi system of [QuennevilleBelair2015] evolves the electric and
magnetic parts `E`, `B` of the linearized Weyl tensor; its solutions describe gravitational waves
only while `E` and `B` are **TSD** (symmetric, trace-free, divergence-free). The method of
[QuennevilleBelair2015], Ch. 5–6, solves it as the Hodge wave equation (6.1) of the complex with
weak symmetry `Γ → Ṽ¹ → W² × W̃²` (below) on states `(σ, u, M, ρ)`: `u` the rows of `E` (vector
`1`-forms), `ρ` the rows of `⋆B` (vector `2`-forms), `M` the multiplier of the symmetry of `E`,
`σ` the potential of `Γ`. The constraint is `σ = 0`, `M = 0`, `E` and `B` TSD (`IsTSDState`).
Whether boundary conditions keep the constraints is the central difficulty of the initial
boundary value problem of general relativity ([FriedrichNagy1999], [KreissWinicour2006]); the
entry `palomar/constraints` answers it for the exact evolution. This entry answers it for the
method: which solution does it compute?

* `FEEC.bggWeakSymmetry`, the abstract method (Prop 5.4, Thm 5.5): for BGG data with weak
  symmetry and finite-dimensional subcomplexes with bounded cochain projections `π`, the method
  that replaces `S` by `Sₕ = πS` is uniquely solvable and converges up to the consistency of
  `Sₕ` at the order `h`; its semi-discrete form (6.5) is determined by the initial values and
  keeps a discrete Gauss law.
* `FEEC.weakSymmetry_cube`: the method with the elements of Table 5.1 on Freudenthal meshes of the
  cube `Q = (0, ½)³`, for both boundary conditions of `CubeBC`. With the **electric** boundary
  conditions of the thesis (`σ = 0`, `n × E = 0` on `∂Q`, §6.3) it is an instance of
  `FEEC.bggWeakSymmetry` with `Sₕ ≠ S`, converges at the rates `h` (static) and `(1 + t) h` (wave)
  for solutions of class `H¹`, and converges with no regularity from every datum of `D(L)`; from
  the TSD datum `(0, 0, 0, ⋆β)` its limit leaves TSD, and so do its discrete fields: it computes a
  solution that is not a gravitational wave. With the **mirror** boundary conditions it converges
  at the rate `(1 + t) h` from the TSD data of `D(L³)` to the exact solution, which stays TSD,
  and it has non-stationary discrete solutions in the discrete Gauss law.
* `FEEC.weakSymmetry_cube_nonvacuous`: nontrivial solutions meet the hypotheses of the electric
  rates.

**The complex with weak symmetry.** The BGG construction ([ArnoldHu2021]) couples two de Rham
complexes by connecting maps `S : Ṽⁱ → Vⁱ⁺¹` with `d S = -S d̃`; eliminating `Ṽ⁰` against `V¹`
weakly by a multiplier `λ` gives the saddle point problem (5.3): find `σ ∈ V⁰`, `φ ∈ Ṽ⁰`,
`u ∈ Ṽ¹`, `λ` with `⟪σ, τ⟫ - ⟪u, d̃ψ⟫ - ⟪λ, dτ - S⁰ψ⟫ = 0` for all `τ ∈ V⁰`, `ψ ∈ Ṽ⁰`,
`⟪d̃φ, v⟫ + ⟪S¹u, S¹v⟫ + ⟪d̃u, d̃v⟫ = F(v)` for all `v ∈ Ṽ¹`, and `dσ = S⁰φ`. With the electric
boundary conditions the rows are `H̊¹ → H̊(curl) → L²`, `S⁰ = I`, `S¹ = 2 vskw` in vector proxies,
and `Γ = {(σ, grad σ) | σ ∈ H̊²}` needs `C¹` elements, which the multiplier avoids. The method
replaces `S` by `Sₕ = πS` for cochain projections `π` (a variational crime); the compatibility
condition (5.4) `π¹S⁰π̃⁰ = π¹S⁰` replaces the surjectivity of `S⁰ₕ`. The Hodge wave equation of
the complex is (6.1), written with the multiplier as (6.2) and discretized as (6.5).

## Conventions

Points of `ℝⁿ` are `Fin n → ℝ` (Lebesgue measure, sup norm). A `k`-form is given by its
coefficients `ω_s` on `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}`, `s = {s₁ < ⋯ < s_k} ⊆ Fin n`
(`FormIdx n k`); `L²(Ω; Λᵏ)` is the `ℓ²` sum of a copy of `L²(Ω)` per coefficient (`L2Form`) and
`L²(Ω; Λᵏ ⊗ ℝⁿ)` the `ℓ²` sum of `n` copies of it (`L2Vec`). With `ε(j, s) =
(-1)^{#{l ∈ s | l < j}}`, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}` and `(Σₐ dxₐ ∧ vₐ)_s =
Σ_{a ∈ s} ε(a, s) (vₐ)_{s ∖ a}`. Forms, polynomial forms, meshes, finite element and Sobolev
spaces are stated in the words of the Palomar entry `palomar/fem`. In `ℝ³` the electric field of
a state is `E_{ab} = (uₐ)_{dx_b}` and the magnetic field `B_{ai} = (-1)ⁱ (ρₐ)_{{i}ᶜ}`
(`⋆dxᵢ = (-1)ⁱ dx_{{i}ᶜ}`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 5 ((5.1)–(5.6), Props 5.3, 5.4, 5.9, Thm 5.5, Table 5.1), Ch. 6 ((6.1)–(6.5), §6.3,
  Prop 6.2)
* [H. Friedrich, G. Nagy, *The Initial Boundary Value Problem for Einstein's Vacuum Field Equation*][FriedrichNagy1999]
* [H.-O. Kreiss, J. Winicour, *Problems which are well posed in a generalized sense with applications to the Einstein equations*][KreissWinicour2006]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3–5
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3, §4, §5.5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6, 7
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021]
* [D. N. Arnold, R. S. Falk, R. Winther, *Mixed finite element methods for linear elasticity with weakly imposed symmetry*][AFW2007]
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], Lemma 2.4
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [H. Whitney, *Geometric Integration Theory*][Whitney1957], Ch. IV
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Filter Topology Set LinearPMap MeasureTheory

@[expose] public noncomputable section

universe u

namespace FEEC
/-! ### Differential forms on `ℝⁿ` and the `L²` de Rham complexes (from `palomar/fem`) -/

variable {n : ℕ}

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
-- palomar-shared: dMin
/-- The **minimal exterior derivative** `d̊ : L²(Ω; Λᵏ) → L²(Ω; Λᵏ⁺¹)`, the closure of `d` on test
forms, that is of the span of the pairs `(φ, dφ)`, `φ` a test `k`-form (the closure is a graph:
`d` is closable, its formal adjoint being densely defined); its domain is `H̊Λᵏ(Ω)` (for Lipschitz
`Ω`, the forms of `HΛᵏ(Ω)` with vanishing tangential trace) ([AFW2010], §4). -/
def dMin {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Form Ω k →ₗ.[ℝ] L2Form Ω (k + 1) :=
  (Submodule.span ℝ {p : L2Form Ω k × L2Form Ω (k + 1) | ∃ φ : FormField n,
    (∀ s, IsTestFn Ω fun x => φ x s) ∧
    (∀ s : FormIdx n k, ⇑(p.1 s) =ᵐ[volume.restrict Ω] fun x => φ x s.1) ∧
    ∀ t : FormIdx n (k + 1), ⇑(p.2 t) =ᵐ[volume.restrict Ω] fun x => extDeriv φ x t.1}
    ).topologicalClosure.toLinearPMap
-- palomar-shared-end: dMin

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
/-- `𝒯` are **Freudenthal meshes** ([Freudenthal1942]): every simplex of `𝒯 N` is a Kuhn simplex
`h (z + K_σ)` of `[0, ½]ⁿ`, `h = 1 / (2 (N + 1))`, `z ∈ {0, …, N}ⁿ`, `σ ∈ 𝔖ₙ`, with vertices
`v_j = h (z + e_{σ 0} + ⋯ + e_{σ (j - 1)})`, `j = 0, …, n` (a mesh of the cube `(0, ½)ⁿ` of such
simplices consists of all of them, the Freudenthal triangulation of the cube). -/
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

/-- The vertex sets lying in a face `{y_j = 0}` or `{y_j = ½}`, `j ∈ J`, of the cube `(0, ½)ⁿ`: in
`femSpace`, vanishing traces on the faces normal to `eⱼ`, `j ∈ J` (`J = ∅`: no boundary condition;
`J = univ`: vanishing traces on `∂Q`). -/
def cubeFacets (J : Finset (Fin n)) : Set (Finset (Fin n → ℝ)) :=
  {F | ∃ j ∈ J, (∀ v ∈ F, v j = 0) ∨ ∀ v ∈ F, v j = 1 / 2}

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

-- palomar-shared: IsSobolevForm
/-- `x ∈ L²(Ω; Λʲ)` **lies in `Hᵐ(Ω; Λʲ)` with norm at most `L`**, for `Hᵐ(Ω) = Hᵐ(ℝⁿ)|_Ω` (the
restriction definition, weak derivatives as in [Evans2010], §5.2; on Lipschitz domains, by
Stein's extension theorem, the space of weak derivatives in `L²(Ω)` with an equivalent norm): each
coefficient is the restriction of a function `D t []` on `ℝⁿ` with weak derivatives `D t l` in
`L²(ℝⁿ)` along the words `l` of length at most `m` (`∫ D t [] ∂_{l₁} ⋯ ∂_{l_p} φ =
(-1)^p ∫ D t l φ` for test functions `φ`), with `Σ_t Σ_{|l| ≤ m} ‖D t l‖² ≤ L²` (norm at most
`|L|`; a sum over words: a derivative of multi-index `α` is counted `|α|!/α!` times). -/
def IsSobolevForm {n : ℕ} (Ω : Set (Fin n → ℝ)) (m : ℕ) (j : ℤ) (L : ℝ) (x : L2Form Ω j) :
    Prop :=
  ∃ D : FormIdx n j → List (Fin n) → (Fin n → ℝ) → ℝ,
    (∀ t l, l.length ≤ m → MemLp (D t l) 2 volume ∧ ∀ φ, IsTestFn univ φ →
      ∫ y, D t [] y * l.foldr partialDeriv φ y = (-1) ^ l.length * ∫ y, D t l y * φ y) ∧
    ∑ t, ∑ p ∈ Finset.range (m + 1), ∑ l : Fin p → Fin n, ∫ y, D t (List.ofFn l) y ^ 2 ≤ L ^ 2 ∧
    ∀ t, ⇑(x t) =ᵐ[volume.restrict Ω] D t []
-- palomar-shared-end: IsSobolevForm

/-! ### Vector-valued forms and the connecting maps -/

-- palomar-shared: L2Vec
/-- `L²(Ω; Λᵏ ⊗ ℝⁿ)`: the vectors `v = (v₀, …, v_{n-1})` of `k`-forms of `L²(Ω; Λᵏ)`, an `ℓ²`
sum. -/
abbrev L2Vec {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : Type := PiLp 2 fun _ : Fin n => L2Form Ω k
/-- The operators `Tₐ` acting componentwise on vectors, `(vₐ) ↦ (Tₐ vₐ)`, with domain
`∏ₐ D(Tₐ)`. -/
def vecOp {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (T : Fin n → E →ₗ.[ℝ] F) :
    PiLp 2 (fun _ : Fin n => E) →ₗ.[ℝ] PiLp 2 (fun _ : Fin n => F) where
  domain :=
    { carrier := {v | ∀ a, v a ∈ (T a).domain}
      add_mem' := fun hv hw a => (T a).domain.add_mem (hv a) (hw a)
      zero_mem' := fun a => (T a).domain.zero_mem
      smul_mem' := fun c _ hv a => (T a).domain.smul_mem c (hv a) }
  toFun :=
    { toFun := fun v => WithLp.toLp 2 fun a => T a ⟨(v : PiLp 2 fun _ : Fin n => E) a, v.2 a⟩
      map_add' := fun v w => PiLp.ext fun a => (T a).map_add ⟨_, v.2 a⟩ ⟨_, w.2 a⟩
      map_smul' := fun c v => PiLp.ext fun a => (T a).map_smul c ⟨_, v.2 a⟩ }
-- palomar-shared-end: L2Vec
-- palomar-shared: wedge
/-- **The connecting map** `S v = Σₐ dxₐ ∧ vₐ : L²(Ω; Λᵏ ⊗ ℝⁿ) → L²(Ω; Λᵏ⁺¹)`,
`(S v)_s = Σ_{a ∈ s} ε(a, s) (vₐ)_{s ∖ a}`. On vector proxies, `S` is the identity `S⁰ = I` on
vector `0`-forms (`(S v)_{a} = vₐ`), and on vector `1`-forms `vₐ = Σ_b u_{ab} dx_b`,
`(S v)_{ab} = u_{ab} - u_{ba}`, i.e. `S¹ = 2 vskw` ([QuennevilleBelair2015], §5.3; [AFW2007]). -/
def wedge {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Vec Ω k →L[ℝ] L2Form Ω (k + 1) :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : FormIdx n (k + 1) =>
      Lp ℝ 2 (volume.restrict Ω)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun s => ∑ a : Fin n, if h : a ∈ s.1 then (sgn a s.1 : ℝ) •
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : FormIdx n k => Lp ℝ 2 (volume.restrict Ω))
          ⟨s.1.erase a, by
            rw [Finset.card_erase_of_mem h, Nat.cast_sub (Finset.card_pos.2 ⟨a, h⟩), s.2]
            ring⟩) ∘L PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => L2Form Ω k) a) else 0
-- palomar-shared-end: wedge

/-! ### BGG data with weak symmetry and their discretization ([QuennevilleBelair2015], Ch. 5) -/

-- palomar-shared: WeakSymmetryData
/-- **BGG data with weak symmetry**: two segments `W⁰ → W¹ → W²` and `W̃⁰ → W̃¹ → W̃²` of
operators `d`, `d̃` between real inner product spaces (unbounded, `LinearPMap`s; densely defined
and closed in the applications, which is not required), with bounded connecting maps
`S⁰ : W̃⁰ → W¹`, `S¹ : W̃¹ → W²`. No law is imposed: the complex and anticommutation laws are
hypotheses where they are used. -/
structure WeakSymmetryData (W0 W1 W2 Wt0 Wt1 Wt2 : Type*) [NormedAddCommGroup W0]
    [InnerProductSpace ℝ W0] [NormedAddCommGroup W1] [InnerProductSpace ℝ W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0]
    [InnerProductSpace ℝ Wt0] [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1]
    [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2] where
  /-- the top row -/
  (d0 : W0 →ₗ.[ℝ] W1) (d1 : W1 →ₗ.[ℝ] W2)
  /-- the bottom row -/
  (dt0 : Wt0 →ₗ.[ℝ] Wt1) (dt1 : Wt1 →ₗ.[ℝ] Wt2)
  /-- the connecting maps -/
  (S0 : Wt0 →L[ℝ] W1) (S1 : Wt1 →L[ℝ] W2)
namespace WeakSymmetryData
variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2)
/-- **The Hodge wave operator `L` of the complex with weak symmetry** `Γ → Ṽ¹ → W² × W̃²`,
`Γ = {(σ, φ) ∈ D(d⁰) × D(d̃⁰) | d⁰σ = S⁰φ}`, with the operators `(σ, φ) ↦ d̃φ` and
`u ↦ (S¹u, d̃u)` ([QuennevilleBelair2015], (6.1), (6.2)), given by its graph in the sign
convention of (6.2): `L U = V` for `U = (σ, u, M, ρ)` iff `σ` lies in `Γ` with some `φ`,
`u ∈ D(d̃¹)`, `⟪V_σ, τ⟫ = ⟪u, d̃ψ⟫` for all `(τ, ψ) ∈ Γ`,
`⟪V_u, v⟫ = -⟪d̃φ, v⟫ - ⟪M, S¹v⟫ - ⟪ρ, d̃v⟫` for all `v ∈ D(d̃¹)`, `V_M = S¹u` and `V_ρ = d̃u`. -/
def IsWave (U V : W0 × Wt1 × W2 × Wt2) : Prop :=
  ∃ (σ : D.d0.domain) (φ : D.dt0.domain) (u : D.dt1.domain), (σ : W0) = U.1 ∧
    (u : Wt1) = U.2.1 ∧ D.d0 σ = D.S0 φ ∧
    (∀ (τ : D.d0.domain) (ψ : D.dt0.domain), D.d0 τ = D.S0 ψ →
      ⟪V.1, τ⟫_ℝ = ⟪(u : Wt1), D.dt0 ψ⟫_ℝ) ∧
    (∀ v : D.dt1.domain, ⟪V.2.1, v⟫_ℝ =
      -⟪D.dt0 φ, v⟫_ℝ - ⟪U.2.2.1, D.S1 v⟫_ℝ - ⟪U.2.2.2, D.dt1 v⟫_ℝ) ∧
    V.2.2.1 = D.S1 u ∧ V.2.2.2 = D.dt1 u
end WeakSymmetryData
-- palomar-shared-end: WeakSymmetryData

namespace WeakSymmetryData

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2)

/-- The rows are complexes, `R(d⁰) ⊆ D(d¹)`, `d¹d⁰ = 0` and `R(d̃⁰) ⊆ D(d̃¹)`, `d̃¹d̃⁰ = 0`, and
`S` anticommutes with them: `S⁰D(d̃⁰) ⊆ D(d¹)` and `d¹S⁰ = -S¹d̃⁰` (a morphism `Ṽ → V[1]`). -/
def IsBGG : Prop :=
  (∀ x : D.d0.domain, ∃ h : D.d0 x ∈ D.d1.domain, D.d1 ⟨_, h⟩ = 0) ∧
    (∀ x : D.dt0.domain, ∃ h : D.dt0 x ∈ D.dt1.domain, D.dt1 ⟨_, h⟩ = 0) ∧
    ∀ ψ : D.dt0.domain, ∃ h : D.S0 ψ ∈ D.d1.domain, D.d1 ⟨_, h⟩ = -D.S1 (D.dt0 ψ)

/-- **The continuous hypotheses with constant `C`** ([QuennevilleBelair2015], §5.1, Prop 5.3):
Poincaré inequalities on `V⁰` and `Ṽ⁰` (so `d⁰`, `d̃⁰` are injective, with closed range when
closed), exactness of the top row at `V¹`, the Hodge decomposition `v = d̃ψ + w`,
`‖w‖ ≤ C ‖d̃v‖`, on `Ṽ¹` (exactness of the bottom row at `Ṽ¹` and the Poincaré inequality), the
**regular decomposition** `d¹V¹ = d¹S⁰Ṽ⁰` with the bound `‖d̃φ‖ ≤ C ‖d¹x‖` ([Hiptmair2002],
Lemma 2.4, in the application), and `‖S⁰‖, ‖S¹‖ ≤ C`. -/
structure IsStable (C : ℝ) : Prop where
  poincare : ∀ σ : D.d0.domain, ‖(σ : W0)‖ ≤ C * ‖D.d0 σ‖
  poincare_t : ∀ φ : D.dt0.domain, ‖(φ : Wt0)‖ ≤ C * ‖D.dt0 φ‖
  exact : ∀ μ : D.d1.domain, D.d1 μ = 0 → ∃ ρ : D.d0.domain, D.d0 ρ = μ
  hodge_t : ∀ v : D.dt1.domain, ∃ (ψ : D.dt0.domain) (w : D.dt1.domain),
    (v : Wt1) = D.dt0 ψ + w ∧ ‖(w : Wt1)‖ ≤ C * ‖D.dt1 v‖
  regular : ∀ x : D.d1.domain, ∃ (φ : D.dt0.domain) (h : D.S0 φ ∈ D.d1.domain),
    D.d1 ⟨_, h⟩ = D.d1 x ∧ ‖D.dt0 φ‖ ≤ C * ‖D.d1 x‖
  norm_S0 : ‖D.S0‖ ≤ C
  norm_S1 : ‖D.S1‖ ≤ C

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
  (V0 : Submodule ℝ W0) (V1 : Submodule ℝ W1) (V2 : Submodule ℝ W2)
  (Vt0 : Submodule ℝ Wt0) (Vt1 : Submodule ℝ Wt1) (Vt2 : Submodule ℝ Wt2)
  [fd0 : FiniteDimensional ℝ V0] [fd1 : FiniteDimensional ℝ V1] [fd2 : FiniteDimensional ℝ V2]
  [fdt0 : FiniteDimensional ℝ Vt0] [fdt1 : FiniteDimensional ℝ Vt1]
  [fdt2 : FiniteDimensional ℝ Vt2]
  (le0 : V0 ≤ D.d0.domain) (le1 : V1 ≤ D.d1.domain)
  (let0 : Vt0 ≤ D.dt0.domain) (let1 : Vt1 ≤ D.dt1.domain)
  (d0_mem : ∀ x : D.d0.domain, (x : W0) ∈ V0 → D.d0 x ∈ V1)
  (d1_mem : ∀ x : D.d1.domain, (x : W1) ∈ V1 → D.d1 x ∈ V2)
  (dt0_mem : ∀ x : D.dt0.domain, (x : Wt0) ∈ Vt0 → D.dt0 x ∈ Vt1)
  (dt1_mem : ∀ x : D.dt1.domain, (x : Wt1) ∈ Vt1 → D.dt1 x ∈ Vt2)
  /-- the cochain projections -/
  (π0 : W0 →L[ℝ] W0) (π1 : W1 →L[ℝ] W1) (π2 : W2 →L[ℝ] W2)
  (πt0 : Wt0 →L[ℝ] Wt0) (πt1 : Wt1 →L[ℝ] Wt1) (πt2 : Wt2 →L[ℝ] Wt2)
  (π0_mem : ∀ x, π0 x ∈ V0) (π1_mem : ∀ x, π1 x ∈ V1) (π2_mem : ∀ x, π2 x ∈ V2)
  (πt0_mem : ∀ x, πt0 x ∈ Vt0) (πt1_mem : ∀ x, πt1 x ∈ Vt1) (πt2_mem : ∀ x, πt2 x ∈ Vt2)
  (π0_id : ∀ x ∈ V0, π0 x = x) (π1_id : ∀ x ∈ V1, π1 x = x) (π2_id : ∀ x ∈ V2, π2 x = x)
  (πt0_id : ∀ x ∈ Vt0, πt0 x = x) (πt1_id : ∀ x ∈ Vt1, πt1 x = x)
  (πt2_id : ∀ x ∈ Vt2, πt2 x = x)
  (comm0 : ∀ x : D.d0.domain, D.d0 ⟨π0 x, le0 (π0_mem x)⟩ = π1 (D.d0 x))
  (comm1 : ∀ x : D.d1.domain, D.d1 ⟨π1 x, le1 (π1_mem x)⟩ = π2 (D.d1 x))
  (commt0 : ∀ x : D.dt0.domain, D.dt0 ⟨πt0 x, let0 (πt0_mem x)⟩ = πt1 (D.dt0 x))
  (commt1 : ∀ x : D.dt1.domain, D.dt1 ⟨πt1 x, let1 (πt1_mem x)⟩ = πt2 (D.dt1 x))

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

/-- The squared **projection error** of `(σ, φ, u)` in the norms of `errorSq` (with `d π = π d`). -/
def projErrorSq (σ : D.d0.domain) (φ : D.dt0.domain) (u : D.dt1.domain) : ℝ :=
  ‖Q.π0 σ - σ‖ ^ 2 + ‖Q.π1 (D.d0 σ) - D.d0 σ‖ ^ 2 + ‖Q.πt0 φ - φ‖ ^ 2 +
    ‖Q.πt1 (D.dt0 φ) - D.dt0 φ‖ ^ 2 + ‖Q.πt1 u - u‖ ^ 2 + ‖Q.π2 (D.S1 (Q.πt1 u - u))‖ ^ 2 +
    ‖Q.πt2 (D.dt1 u) - D.dt1 u‖ ^ 2

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

variable {D} in
/-- `(σₕ, uₕ)` satisfies **the discrete Gauss law** of `Q`: `σₕ = 0` and `uₕ ⊥ d̃ψ` for every
discrete pair `(τ, ψ) ∈ Vₕ⁰ × Ṽₕ⁰` with `dτ = π¹S⁰ψ` (the discrete form of `div E = 0`, the
part of the constraint seen by the first operator of the complex). -/
def Discretization.IsGauss (Q : D.Discretization) (σ : W0) (u : Wt1) : Prop :=
  σ = 0 ∧ ∀ (τ : D.d0.domain) (ψ : D.dt0.domain), (τ : W0) ∈ Q.V0 → (ψ : Wt0) ∈ Q.Vt0 →
    D.d0 τ = Q.π1 (D.S0 ψ) → ⟪u, D.dt0 ψ⟫_ℝ = 0

variable {D} in
/-- The **trajectories** of the semi-discrete problem (6.5) of `Q` on `[0, T]` with source `f`:
the paths `t ↦ (σₕ, uₕ, Mₕ, ρₕ)(t)` of its solutions (`IsDiscreteWave`). -/
def Discretization.trajectories (Q : D.Discretization) (T : ℝ) (f : ℝ → Wt1) :
    Set (ℝ → W0 × Wt1 × W2 × Wt2) :=
  {U | ∃ σ φ u M ρ lam, Q.IsDiscreteWave T f σ φ u M ρ lam ∧
    ∀ t, U t = ((σ t : W0), (u t : Wt1), M t, ρ t)}

end WeakSymmetryData

/-- The `L²` norm `(‖σ‖² + ‖u‖² + ‖M‖² + ‖ρ‖²)^{1/2}` of a state `U = (σ, u, M, ρ)`. -/
def stateNorm {E F G H : Type*} [Norm E] [Norm F] [Norm G] [Norm H] (U : E × F × G × H) : ℝ :=
  √(‖U.1‖ ^ 2 + ‖U.2.1‖ ^ 2 + ‖U.2.2.1‖ ^ 2 + ‖U.2.2.2‖ ^ 2)

-- palomar-shared: IsStrongSolution
/-- `u` is a **strong solution** of `u' = A u` on `I ⊆ ℝ` for an operator given by its graph, a
relation `A ⊆ X × X` (a `LinearPMap` through its `graph`): `u` is continuous on `I` and at every
`t ∈ I` has, within `I`, a derivative `v` with `(u(t), v) ∈ A` (so `u(t)` lies in `D(A)`). -/
def IsStrongSolution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : SetRel X X)
    (I : Set ℝ) (u : ℝ → X) : Prop :=
  ContinuousOn u I ∧ ∀ t ∈ I, ∃ v, (u t, v) ∈ A ∧ HasDerivWithinAt u v I t
-- palomar-shared-end: IsStrongSolution

/-! ### The Einstein–Bianchi fields, the constraint and the boundary conditions -/

-- palomar-shared: bggData
/-- BGG data on the forms of `Ω ⊆ ℝ³`: the rows `L²Λ⁰ → L²Λ¹ → L²Λ²` and
`L²Λ⁰ ⊗ ℝ³ → L²Λ¹ ⊗ ℝ³ → L²Λ² ⊗ ℝ³`. -/
abbrev FormData (Ω : Set (Fin 3 → ℝ)) : Type :=
  WeakSymmetryData (L2Form Ω 0) (L2Form Ω 1) (L2Form Ω 2) (L2Vec Ω 0) (L2Vec Ω 1) (L2Vec Ω 2)
/-- **The BGG data (4.16) on `Ω ⊆ ℝ³` with the electric boundary conditions**
([QuennevilleBelair2015], §5.3, §6.3), vanishing tangential traces on `∂Ω` in both rows (on the
states, `σ = 0` and `n × E = 0`): the top row `H̊Λ⁰(Ω) → H̊Λ¹(Ω) → L²Λ²(Ω)` and, componentwise,
the bottom row `H̊Λ⁰(Ω) ⊗ ℝ³ → H̊Λ¹(Ω) ⊗ ℝ³ → L²Λ²(Ω) ⊗ ℝ³` of the minimal exterior derivative,
with `S⁰ = S¹ = Σₐ dxₐ ∧ ·` (`wedge`). In vector proxies the rows are `H̊¹ → H̊(curl) → L²(ℝ³)`
and `S⁰ = I`, `S¹ = 2 vskw`. -/
def bggData (Ω : Set (Fin 3 → ℝ)) : FormData Ω :=
  ⟨dMin Ω 0, dMin Ω 1, vecOp fun _ => dMin Ω 0, vecOp fun _ => dMin Ω 1, wedge Ω 0, wedge Ω 1⟩
-- palomar-shared-end: bggData
-- palomar-shared: IsTSD
/-- **The electric field** `E_{ab} = (uₐ)_{dx_b}` of a vector `1`-form `u` (its rows are the
`uₐ`). -/
def mat1 {Ω : Set (Fin 3 → ℝ)} (u : L2Vec Ω 1) (a b : Fin 3) : Lp ℝ 2 (volume.restrict Ω) :=
  u a ⟨{b}, by simp⟩
/-- **The magnetic field** `B_{ai} = (-1)ⁱ (ρₐ)_{{i}ᶜ}` of a vector `2`-form `ρ` (its rows are
the `⋆ρₐ`, `⋆dxᵢ = (-1)ⁱ dx_{{i}ᶜ}`). -/
def mat2 {Ω : Set (Fin 3 → ℝ)} (ρ : L2Vec Ω 2) (a i : Fin 3) : Lp ℝ 2 (volume.restrict Ω) :=
  (-1 : ℝ) ^ (i : ℕ) • ρ a ⟨Finset.univ.erase i, by simp⟩
/-- A matrix field `E` on `Ω` is **TSD**: symmetric, trace-free and weakly divergence-free in
`Ω`, `Σ_c ∫_Ω E_{ac} ∂_c ψ = 0` for every row `a` and every test function `ψ` (no boundary
condition). -/
def IsTSD {Ω : Set (Fin 3 → ℝ)} (E : Fin 3 → Fin 3 → Lp ℝ 2 (volume.restrict Ω)) : Prop :=
  (∀ a b, E a b = E b a) ∧ ∑ a, E a a = 0 ∧
    ∀ a ψ, IsTestFn Ω ψ → ∑ c, ∫ x in Ω, E a c x * partialDeriv c ψ x = 0
-- palomar-shared-end: IsTSD
-- palomar-shared: IsTSDState
/-- A state `(σ, u, M, ρ)` of the system (6.1) satisfies **the constraint**: `σ = 0`, `M = 0`,
and the electric and magnetic fields are TSD. -/
def IsTSDState {Ω : Set (Fin 3 → ℝ)} (U : L2Form Ω 0 × L2Vec Ω 1 × L2Form Ω 2 × L2Vec Ω 2) :
    Prop :=
  U.1 = 0 ∧ U.2.2.1 = 0 ∧ IsTSD (mat1 U.2.1) ∧ IsTSD (mat2 U.2.2.2)
-- palomar-shared-end: IsTSDState
-- palomar-shared: mirrorData
/-- **The exterior derivative with vanishing tangential traces on the faces normal to `eⱼ`,
`j ∈ J`**, of the cube `(0, ½)ⁿ`: the closure of `dMax` on the forms of its domain vanishing
almost everywhere near the faces `{y_j = 0}`, `{y_j = ½}`, `j ∈ J` (its domain is `H_JΛᵏ`;
`J = ∅` gives `dMax`). -/
def dPart {n : ℕ} (J : Finset (Fin n)) (k : ℤ) :
    L2Form (cube n) k →ₗ.[ℝ] L2Form (cube n) (k + 1) :=
  (Submodule.span ℝ {p : L2Form (cube n) k × L2Form (cube n) (k + 1) |
    ∃ h : p.1 ∈ (dMax (cube n) k).domain, dMax (cube n) k ⟨p.1, h⟩ = p.2 ∧
      ∃ δ > 0, ∀ s, ∀ᵐ y ∂volume.restrict (cube n),
        (∃ j ∈ J, y j < δ ∨ 1 / 2 - δ < y j) → p.1 s y = 0}).topologicalClosure.toLinearPMap
/-- **The BGG data on the cube `Q = (0, ½)³` with mirror boundary conditions**: the top row
`HΛ⁰(Q) → HΛ¹(Q) → L²Λ²(Q)` (no boundary condition) and the bottom row with component `a` in
`H_{a}Λ⁰(Q) → H_{a}Λ¹(Q) → L²Λ²(Q)` (vanishing tangential traces on the faces normal to `eₐ`),
`S = Σₐ dxₐ ∧ ·`. These are the conditions satisfied by fields invariant under the reflections in
the faces with `E` a tensor, `B` a pseudotensor and `M` a pseudovector. -/
def mirrorData : FormData (cube 3) :=
  ⟨dMax (cube 3) 0, dMax (cube 3) 1, vecOp fun a => dPart {a} 0, vecOp fun a => dPart {a} 1,
    wedge (cube 3) 0, wedge (cube 3) 1⟩
-- palomar-shared-end: mirrorData

/-- **The two boundary conditions of the system (6.1) on the cube `Q = (0, ½)³`**, and of its
discretization: `electric`, vanishing tangential traces on `∂Q` in both rows (`σ = 0`,
`n × E = 0`; the thesis' §6.3), and `mirror`, the conditions of the fields invariant under the
reflections in the faces (none in the top row, in component `a` of the bottom row vanishing
tangential traces on the faces normal to `eₐ`). -/
inductive CubeBC where
  /-- the electric boundary conditions (`bggData`) -/
  | electric
  /-- the mirror boundary conditions (`mirrorData`) -/
  | mirror

namespace CubeBC

/-- The BGG data on `Q` with the boundary conditions `bc`: `bggData (cube 3)` (electric),
`mirrorData` (mirror). -/
def data : CubeBC → FormData (cube 3)
  | electric => bggData (cube 3)
  | mirror => mirrorData

/-- The faces normal to `eⱼ`, `j ∈ bc.top`, on which the finite element spaces of the top row
have vanishing traces: all (electric), none (mirror). -/
def top : CubeBC → Finset (Fin 3)
  | electric => Finset.univ
  | mirror => ∅

/-- The faces normal to `eⱼ`, `j ∈ bc.bottom a`, on which component `a` of the bottom row has
vanishing traces: all (electric), those normal to `eₐ` (mirror). -/
def bottom : CubeBC → Fin 3 → Finset (Fin 3)
  | electric => fun _ => Finset.univ
  | mirror => fun a => {a}

end CubeBC

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

/-- `Q_N` are **discretizations of `D` by the elements of Table 5.1 on Freudenthal meshes `𝒯_N`
of `Q = (0, ½)³`** ([QuennevilleBelair2015], §5.3; [AFW2010], §5.5): `𝒯` a shape-regular,
quasi-uniform family with `h_N → 0`, the spaces of `topSeq` (top row) and, in each component,
`bottomSeq` (bottom row) with vanishing traces on the faces normal to `eⱼ`, `j ∈ J` (top row),
`j ∈ J̃ a` (component `a` of the bottom row), and projections bounded by `C`, satisfying (5.4)
and consistent at the order `h_N`. -/
def IsTable51 {D : FormData (cube 3)} (𝒯 : ℕ → SimplicialMesh 3) (Q : ℕ → D.Discretization)
    (C : ℝ) (J : Finset (Fin 3)) (Jt : Fin 3 → Finset (Fin 3)) : Prop :=
  IsMeshFamily (cube 3) 𝒯 ∧ IsFreudenthal 𝒯 ∧ ∀ N,
    ((Q N).V0 : Set (L2Form (cube 3) 0)) = femSpace (cube 3) (𝒯 N) topSeq (cubeFacets J) 0 ∧
    ((Q N).V1 : Set (L2Form (cube 3) 1)) = femSpace (cube 3) (𝒯 N) topSeq (cubeFacets J) 1 ∧
    ((Q N).V2 : Set (L2Form (cube 3) 2)) = femSpace (cube 3) (𝒯 N) topSeq (cubeFacets J) 2 ∧
    ((Q N).Vt0 : Set (L2Vec (cube 3) 0)) =
      {v | ∀ a, v a ∈ femSpace (cube 3) (𝒯 N) bottomSeq (cubeFacets (Jt a)) 0} ∧
    ((Q N).Vt1 : Set (L2Vec (cube 3) 1)) =
      {v | ∀ a, v a ∈ femSpace (cube 3) (𝒯 N) bottomSeq (cubeFacets (Jt a)) 1} ∧
    ((Q N).Vt2 : Set (L2Vec (cube 3) 2)) =
      {v | ∀ a, v a ∈ femSpace (cube 3) (𝒯 N) bottomSeq (cubeFacets (Jt a)) 2} ∧
    (Q N).IsBounded C ∧ (Q N).Compatible ∧ (Q N).IsConsistent C (meshSize (𝒯 N))

/-! ### The theorems -/

/-- **Stability and convergence of the method with weak symmetry**
([QuennevilleBelair2015], Prop 5.4, Thm 5.5, Prop 6.2, (6.5); [AFW2007]; [AFW2010], §3). For
every BGG data `D` and every discretization `Q`, solutions of (6.5) with the same source are
determined on `[0, T]` by `(σₕ, uₕ, Mₕ, ρₕ)(0)`, and if `D` satisfies `IsBGG`, solutions of (6.5)
without source satisfying the discrete Gauss law at `t = 0` satisfy it at every `t`. For every
constant `C` there is `K` such that, if `D` satisfies the continuous hypotheses with constant `C`
and `Q` has projections bounded by `C` satisfying (5.4): the discrete problem (5.6) has exactly
one solution for every datum `F` (Prop 5.4); and if `Sₕ` is consistent at the order `h` with
constant `C`, then for every solution `(σ, φ, u, λ)` of (5.3) with `‖λ‖ ≤ Λ` and
`|⟪S¹u, d¹w⟫| ≤ Λ ‖w‖` on `V¹` (for densely defined `d¹`: `S¹u ∈ D(d¹*)`, `‖d¹*S¹u‖ ≤ Λ`), and the
solution of (5.6) with the same datum, the squared error is at most `K` times the squared
projection error of `(σ, φ, u)` plus `h² (Λ² + ‖S¹u‖²)` plus `‖(S¹ - S¹ₕ)u‖²` (Thm 5.5). -/
theorem bggWeakSymmetry (C : ℝ) : ∃ K : ℝ, ∀ {W0 W1 W2 Wt0 Wt1 Wt2 : Type u}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [NormedAddCommGroup W1]
    [InnerProductSpace ℝ W1] [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
    [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0] [NormedAddCommGroup Wt1]
    [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
    (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2) (Q : D.Discretization),
    (∀ T f σ φ u M ρ lam σ' φ' u' M' ρ' lam', Q.IsDiscreteWave T f σ φ u M ρ lam →
      Q.IsDiscreteWave T f σ' φ' u' M' ρ' lam' → σ 0 = σ' 0 → u 0 = u' 0 → M 0 = M' 0 →
      ρ 0 = ρ' 0 → ∀ t ∈ Icc 0 T, σ t = σ' t ∧ u t = u' t ∧ M t = M' t ∧ ρ t = ρ' t) ∧
    (D.IsBGG → ∀ T σ φ u M ρ lam, Q.IsDiscreteWave T 0 σ φ u M ρ lam →
      Q.IsGauss (σ 0) (u 0) → ∀ t ∈ Icc 0 T, Q.IsGauss (σ t) (u t)) ∧
    (D.IsBGG → D.IsStable C → Q.IsBounded C → Q.Compatible →
    (∀ F, ∃! x : D.d0.domain × D.dt0.domain × D.dt1.domain × W1,
      Q.IsDiscreteSolution F x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
    ∀ (h Λ : ℝ), 0 ≤ h → Q.IsConsistent C h → ∀ F σ φ u lam σh φh uh lamh,
      D.IsSolution F σ φ u lam → ‖lam‖ ≤ Λ →
      (∀ w : D.d1.domain, |⟪D.S1 u, D.d1 w⟫_ℝ| ≤ Λ * ‖(w : W1)‖) →
      Q.IsDiscreteSolution F σh φh uh lamh →
      Q.errorSq σ σh φ φh u uh ≤ K * (Q.projErrorSq σ φ u + h ^ 2 * (Λ ^ 2 + ‖D.S1 u‖ ^ 2) +
        ‖D.S1 u - Q.π2 (D.S1 u)‖ ^ 2)) := by
  sorry

/-- **What the method computes on the cube** ([QuennevilleBelair2015], §5.3, Table 5.1, Thm 5.5,
Prop 5.9, §6.2–6.3, (6.4), (6.5), Prop 6.2; [AFW2010], §5.5; [ChristiansenWinther2008]). For both
boundary conditions `bc`, there are discretizations `Q_N` of `bc.data` by the elements of
Table 5.1 with the boundary conditions `bc` on Freudenthal meshes of `Q = (0, ½)³` (`IsTable51`
with the faces `bc.top`, `bc.bottom`), `bc.data` satisfying `IsBGG` (so by
`FEEC.bggWeakSymmetry` solutions of (6.5) are determined by their initial values and keep the
discrete Gauss law), such that, with `L = bc.data.IsWave`:

* with the **electric** boundary conditions:
  - (*an instance of `FEEC.bggWeakSymmetry`*) the continuous hypotheses hold with constant `C`
    (so (5.6) is uniquely solvable), and for `N ≥ 2` the method changes `S⁰` on the discrete
    space: `S⁰ₕψ = π¹S⁰ψ ≠ S⁰ψ` for some `ψ ∈ Ṽₕ⁰`;
  - (*no best approximation of `S¹` at the order `h`*) for some `c > 0` and every `N ≥ 2`, some
    `v ∈ Ṽₕ¹`, `v ≠ 0`, has `‖S¹v - w‖ ≥ c (‖v‖² + ‖d̃v‖²)^{1/2}` for all `w ∈ Vₕ²`
    (Raviart–Thomas): no projection has `‖(S¹ - S¹ₕ)v‖ ≤ C h_N ‖v‖_{HΛ}` on `Ṽₕ¹`
    (`IsConsistent` asks less);
  - (*the static rate*) for every solution of (5.3) with `‖λ‖ ≤ L` whose components `σ`, `φₐ`,
    `d̃φₐ`, `uₐ`, `d̃uₐ` lie in `H¹(Q)` with norms at most `L`, the solution of (5.6) has
    `errorSq ≤ (K L h_N)²`;
  - (*the wave rate*) solutions of (6.5) are determined by `(σₕ, uₕ, Mₕ, ρₕ)(0)` (so are `φₕ`,
    `λₕ` on `[0, T)`), and for every classical solution of (6.2) whose states and their time
    derivatives are of class `H¹` with bound `L` (`IsH1State`) and whose multipliers are bounded
    by `L`, some trajectory of (6.5) (from the elliptic projection (6.4)) is within
    `K L (1 + t) h_N` on `[0, T]`;
  - (*convergence from every datum of `D(L)`, no regularity*) for every `U₀ ∈ D(L)` and `T > 0`,
    `U' = L U` has a strong solution on `[0, T]` from `U₀`, and for every such solution `U`, every
    family of trajectories of (6.5) without source whose initial states converge to `U₀`
    converges to `U` uniformly on `[0, T]`;
  - (*the limit leaves the constraint*) some TSD datum `U₀ ∈ D(L)` (in the proof
    `(0, 0, 0, ⋆β)`, `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)`) is, for every `T > 0`, the limit of initial
    states of families of trajectories of (6.5), and every strong solution `U` from `U₀` has, at
    some `t ∈ [0, T]`, an electric field `E(t)` that is not TSD, and at some `t' ∈ [0, T]` a
    magnetic field `B(t')` that is not symmetric; at these times, for all large `N`, so have the
    discrete fields of every such family;
* with the **mirror** boundary conditions:
  - (*a non-stationary solution in the discrete Gauss law*) for every `T > 0` and all large `N`,
    some trajectory of (6.5) without source has `uₕ(0) ≠ 0`, satisfies the law at `t = 0` (so at
    every `t`) and has a non-constant `Mₕ`;
  - (*the rate, to the TSD solution*) for every TSD datum `U₀` with `U₀`, `L U₀`, `L² U₀` in
    `D(L)` and every strong solution `U` of `U' = L U` from `U₀`, `U` stays TSD and some trajectory
    of (6.5) without source (from the elliptic projection (6.4) of `U₀`) is within
    `K (Σ_{k ≤ 3} ‖Lᵏ U₀‖) (1 + t) h_N` of `U` on `[0, T]`; and some such datum is not stationary
    (`L U₀ ≠ 0`; in the proof `E₀ = 2 cos(2π x₃) diag(1, -1, 0)`, `σ₀ = 0`, `M₀ = 0`, `B₀ = 0`).

The rates of [QuennevilleBelair2015] for states `C²` up to `∂Q` with vanishing tangential traces
are corollaries: such states are of class `H¹`. The projections are asserted, not named (in the
proof, the smoothed projections of one smoother for both rows, commuting with the reflections in
the faces for the mirror conditions); the method depends on them through `Sₕ = πS`. -/
theorem weakSymmetry_cube (bc : CubeBC) : ∃ (𝒯 : ℕ → SimplicialMesh 3)
    (Q : ℕ → bc.data.Discretization) (C K : ℝ), IsTable51 𝒯 Q C bc.top bc.bottom ∧
    bc.data.IsBGG ∧
    (bc = .electric →
      bc.data.IsStable C ∧
      (∀ N, 2 ≤ N → ∃ ψ : bc.data.dt0.domain, (ψ : L2Vec (cube 3) 0) ∈ (Q N).Vt0 ∧
        (Q N).π1 (bc.data.S0 ψ) ≠ bc.data.S0 ψ) ∧
      (∃ c > 0, ∀ N, 2 ≤ N → ∃ v : bc.data.dt1.domain, (v : L2Vec (cube 3) 1) ∈ (Q N).Vt1 ∧
        (v : L2Vec (cube 3) 1) ≠ 0 ∧ ∀ w ∈ (Q N).V2,
          c * √(‖(v : L2Vec (cube 3) 1)‖ ^ 2 + ‖bc.data.dt1 v‖ ^ 2) ≤ ‖bc.data.S1 v - w‖) ∧
      (∀ N F σ φ u lam σh φh uh lamh L, bc.data.IsSolution F σ φ u lam →
        IsSobolevForm (cube 3) 1 0 L (σ : L2Form (cube 3) 0) →
        (∀ a, IsSobolevForm (cube 3) 1 0 L ((φ : L2Vec (cube 3) 0) a)) →
        (∀ a, IsSobolevForm (cube 3) 1 1 L (bc.data.dt0 φ a)) →
        (∀ a, IsSobolevForm (cube 3) 1 1 L ((u : L2Vec (cube 3) 1) a)) →
        (∀ a, IsSobolevForm (cube 3) 1 2 L (bc.data.dt1 u a)) → ‖lam‖ ≤ L →
        (Q N).IsDiscreteSolution F σh φh uh lamh →
        (Q N).errorSq σ σh φ φh u uh ≤ (K * L * meshSize (𝒯 N)) ^ 2) ∧
      (∀ N T f σ φ u M ρ lam σ' φ' u' M' ρ' lam', 0 < T → ContinuousOn f (Icc 0 T) →
        (Q N).IsDiscreteWave T f σ φ u M ρ lam → (Q N).IsDiscreteWave T f σ' φ' u' M' ρ' lam' →
        σ 0 = σ' 0 → u 0 = u' 0 → M 0 = M' 0 → ρ 0 = ρ' 0 →
        (∀ t ∈ Icc 0 T, σ t = σ' t ∧ u t = u' t ∧ M t = M' t ∧ ρ t = ρ' t) ∧
          ∀ t ∈ Ico 0 T, φ t = φ' t ∧ lam t = lam' t) ∧
      (∀ N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, 0 < T → ContinuousOn f (Icc 0 T) →
        bc.data.IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' →
        (∀ t ∈ Icc 0 T, IsH1State L (σ t) (φ t) (u t) (M t) (ρ t) ∧
          IsH1State L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) →
        ∃ Uh ∈ (Q N).trajectories T f, ∀ t ∈ Icc 0 T,
          stateNorm (((σ t : L2Form (cube 3) 0), (u t : L2Vec (cube 3) 1), M t, ρ t) - Uh t) ≤
            K * L * (1 + t) * meshSize (𝒯 N)) ∧
      (∀ U₀ V T, bc.data.IsWave U₀ V → 0 < T →
        (∃ U, U 0 = U₀ ∧ IsStrongSolution {p | bc.data.IsWave p.1 p.2} (Icc 0 T) U) ∧
        ∀ U (Uh : ℕ → ℝ → _), U 0 = U₀ →
          IsStrongSolution {p | bc.data.IsWave p.1 p.2} (Icc 0 T) U →
          (∀ N, Uh N ∈ (Q N).trajectories T 0) →
          Tendsto (fun N => stateNorm (U₀ - Uh N 0)) atTop (𝓝 0) →
          ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T, stateNorm (U t - Uh N t) < ε) ∧
      ∃ U₀ V, bc.data.IsWave U₀ V ∧ IsTSDState U₀ ∧ ∀ T > 0,
        (∃ Uh : ℕ → ℝ → _, (∀ N, Uh N ∈ (Q N).trajectories T 0) ∧
          Tendsto (fun N => stateNorm (U₀ - Uh N 0)) atTop (𝓝 0)) ∧
        ∀ U, U 0 = U₀ → IsStrongSolution {p | bc.data.IsWave p.1 p.2} (Icc 0 T) U →
          (∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (U t).2.1) ∧ ∀ Uh : ℕ → ℝ → _,
            (∀ N, Uh N ∈ (Q N).trajectories T 0) →
            Tendsto (fun N => stateNorm (U₀ - Uh N 0)) atTop (𝓝 0) →
            ∀ᶠ N in atTop, ¬IsTSD (mat1 (Uh N t).2.1)) ∧
          ∃ t ∈ Icc 0 T, (∃ a i, mat2 (U t).2.2.2 a i ≠ mat2 (U t).2.2.2 i a) ∧
            ∀ Uh : ℕ → ℝ → _, (∀ N, Uh N ∈ (Q N).trajectories T 0) →
            Tendsto (fun N => stateNorm (U₀ - Uh N 0)) atTop (𝓝 0) →
            ∀ᶠ N in atTop, ∃ a i, mat2 (Uh N t).2.2.2 a i ≠ mat2 (Uh N t).2.2.2 i a) ∧
    (bc = .mirror →
      (∀ T, 0 < T → ∀ᶠ N in atTop, ∃ Uh ∈ (Q N).trajectories T 0,
        (Q N).IsGauss (Uh 0).1 (Uh 0).2.1 ∧ (Uh 0).2.1 ≠ 0 ∧
          ∃ t ∈ Ioc 0 T, (Uh t).2.2.1 ≠ (Uh 0).2.2.1) ∧
      (∀ N T U₀ V₁ V₂ V₃ U, 0 < T → bc.data.IsWave U₀ V₁ → bc.data.IsWave V₁ V₂ →
        bc.data.IsWave V₂ V₃ → IsTSDState U₀ → U 0 = U₀ →
        IsStrongSolution {p | bc.data.IsWave p.1 p.2} (Icc 0 T) U →
        (∀ t ∈ Icc 0 T, IsTSDState (U t)) ∧ ∃ Uh ∈ (Q N).trajectories T 0, ∀ t ∈ Icc 0 T,
          stateNorm (U t - Uh t) ≤
            K * (stateNorm U₀ + stateNorm V₁ + stateNorm V₂ + stateNorm V₃) * (1 + t) *
              meshSize (𝒯 N)) ∧
      ∃ U₀ V₁ V₂ V₃, bc.data.IsWave U₀ V₁ ∧ bc.data.IsWave V₁ V₂ ∧ bc.data.IsWave V₂ V₃ ∧
        IsTSDState U₀ ∧ V₁ ≠ 0) := by
  sorry

/-- **Non-vacuity of the electric rates of `FEEC.weakSymmetry_cube`**: (5.3) on the cube with
the electric boundary conditions has a smooth solution with `σ`, `φ`, `u` and `λ` all nonzero
satisfying the hypotheses of the static rate for some `L`; and for every `T > 0`, (6.2) has a
classical solution on `[0, T]`, with `u(t) ≠ 0` for all `t` and `σ(t), φ(t) ≠ 0` for
`t ∈ (0, T]`, satisfying the hypotheses of the wave rate (`IsH1State`) for some `L`. -/
theorem weakSymmetry_cube_nonvacuous :
    (∃ F σ φ u lam L, (bggData (cube 3)).IsSolution F σ φ u lam ∧
      (σ : L2Form (cube 3) 0) ≠ 0 ∧ (φ : L2Vec (cube 3) 0) ≠ 0 ∧ (u : L2Vec (cube 3) 1) ≠ 0 ∧
      lam ≠ 0 ∧ ‖lam‖ ≤ L ∧ IsSobolevForm (cube 3) 1 0 L (σ : L2Form (cube 3) 0) ∧
      (∀ a, IsSobolevForm (cube 3) 1 0 L ((φ : L2Vec (cube 3) 0) a)) ∧
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((bggData (cube 3)).dt0 φ a)) ∧
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((u : L2Vec (cube 3) 1) a)) ∧
      ∀ a, IsSobolevForm (cube 3) 1 2 L ((bggData (cube 3)).dt1 u a)) ∧
    ∀ T, 0 < T → ∃ f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, ContinuousOn f (Icc 0 T) ∧
      (bggData (cube 3)).IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' ∧
      (∀ t ∈ Icc 0 T, IsH1State L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsH1State L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) ∧
      (∀ t, (u t : L2Vec (cube 3) 1) ≠ 0) ∧
      ∀ t ∈ Ioc 0 T, (σ t : L2Form (cube 3) 0) ≠ 0 ∧ (φ t : L2Vec (cube 3) 0) ≠ 0 := by
  sorry

end FEEC
