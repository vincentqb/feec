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

/-!
# Finite element exterior calculus on polyhedral domains: the `P_r⁻Λ` and `P_rΛ` families

Let `Ω ⊆ ℝⁿ` be a bounded open domain star-shaped with respect to a ball (the sources allow
Lipschitz polyhedral domains; star-shapedness is assumed here), and `M_N` a family of
conforming simplicial meshes of `Ω`, uniformly shape regular and quasi-uniform, with mesh size
`h_N → 0`. Let `S` be an admissible sequence of polynomial families ([AFW2006], §5;
[AFW2010], §5.2): in each form degree `k` the full space `P_{r_k}Λᵏ` or the trimmed space
`P_{r_k}⁻Λᵏ`, consecutive degrees being `P_rΛᵏ` or `P_r⁻Λᵏ` followed by `P_r⁻Λᵏ⁺¹` or
`P_{r-1}Λᵏ⁺¹`. The finite element space `Vₕᵏ = S_k(M_N)` (`femSpace`) consists of the
`L²` forms that are, on every simplex `T`, a polynomial form of `S_k`, with single-valued
tangential traces on the common faces of the mesh; `V̊ₕᵏ` (`femSpaceMin`) has in addition
vanishing traces on the boundary facets.

The `L²` de Rham complexes are `HΛ(Ω)`, with the weak exterior derivative `d` (`dMax`, the
adjoint of the codifferential on test forms), and `H̊Λ(Ω)`, with the closure of `d` on test forms
(`dMin`). The abstract notions — Hilbert complexes, subcomplexes, cochain projections, families
of subcomplexes, graph-norm bounds, approximation and Jackson estimates — are the definitions of
the Palomar entry `palomar/feec` (finite element exterior calculus for Hilbert complexes),
verbatim, so that the families of this file are families in the sense of its theorem `FEEC.feec`.

The theorems, with no hypothesis beyond the data:

* `FEEC.fem` (`HΛ(Ω)`, [AFW2010], §5; [ChristiansenWinther2008]; [Arnold2018], Ch. 7): the spaces
  `S_k(M_N)` are the spaces of a family of finite-dimensional subcomplexes of `HΛ(Ω)` with
  cochain projections `π_N` bounded in `L²` uniformly in `N` (the smoothed projections), hence in
  every graph norm, approximating in the graph norm in every degree, with a Jackson estimate of
  order `h_N^{s+1}` for `C^{s+2}` forms in the degrees `j` with `P_sΛʲ ⊆ S_j` and
  `P_sΛʲ⁺¹ ⊆ S_{j+1}`.
* `FEEC.femMin`: the same for `V̊ₕ ⊆ H̊Λ(Ω)`, for forms vanishing outside `Ω`.
* `FEEC.fem_parallelepiped`: every parallelepiped `A (0, 1)ⁿ + b`, `A` invertible (every open
  box), is such a domain,
  carries such a mesh family, and `d` has closed range in every degree on `HΛ(Ω)` and on `H̊Λ(Ω)`,
  so the static FEEC theorem of `palomar/feec` applies to the families of `FEEC.fem` and
  `FEEC.femMin` on it with no remaining hypothesis.
* `FEEC.maxwell` ([QuennevilleBelair2015], Ch. 4; [AFW2010], §4; [Monk2003]): for `n = 3`, the
  vector proxies `V_N⁰ ⊆ H¹(Ω)`, `V_N¹ ⊆ H(curl, Ω)`, `V_N² ⊆ H(div, Ω)` of `S_0(M_N)`,
  `S_1(M_N)`, `S_2(M_N)` (`proxy0`, `proxy1`, `proxy2`) discretize Maxwell's equations
  `σ' = -grad* E`, `E' = grad σ - curl* B`, `B' = curl E` (`IsMaxwellSolution`; the weak `grad`,
  `curl`, `div` of `weakOp`): for data in the domain of the Maxwell operator there is a unique
  strong solution, it conserves the energy and the Gauss laws `σ = 0`, `grad* E = 0`,
  `div B = 0`, and every family of Galerkin solutions (`IsMaxwellGalerkin`) with converging
  initial data converges to it uniformly on `[0, T]`.

## Conventions

Points of `ℝⁿ` are `Fin n → ℝ` (Lebesgue measure, sup norm). A `k`-form is given by its
coefficients `ω_s` on `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}`, `s = {s₁ < ⋯ < s_k} ⊆ Fin n`
(`FormIdx n k`; a form field `ω : FormField n` has a coefficient for every subset);
`L²(Ω; Λᵏ)` is the `ℓ²` sum of a copy of `L²(Ω)` per coefficient (`L2Form`). With the sign
`ε(j, s) = (-1)^{#{l ∈ s | l < j}}`, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}` and
`(dᵗψ)_s = -Σ_{j ∉ s} ε(j, s) ∂_j ψ_{s ∪ j}` is its formal adjoint. Diameters and balls are
those of the sup norm; for the Euclidean norm the shape-regularity constant `h_T / ρ_T` changes by
a factor depending only on `n`. In `ℝ³` a scalar field has one component (`Fin 1`) and a vector
field three (`Fin 3`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3 (the spaces `P_rΛᵏ`, `P_r⁻Λᵏ`), §5 (assembly, admissible sequences)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–§3.5 (subcomplexes, bounded cochain projections, Jackson estimates), §4 (the `L²` de Rham
  complex), §5.2 (the complexes of `P_rΛ` and `P_r⁻Λ`), §5.5 (smoothed projections)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6, 7
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1–§3.2
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 4 (§4.4, §4.6, Prop. 4.16), Ch. 5

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Filter Topology Set LinearPMap MeasureTheory

@[expose] public noncomputable section

namespace FEEC

/-! ### Hilbert complexes and families of subcomplexes (verbatim from `palomar/feec`) -/

/-- A **Hilbert complex** over `𝕜` on `ℤ`: closed densely defined operators `d i j : Wⁱ → Wʲ`,
zero unless `j = i + 1`, with `R(d i j) ⊆ D(d j k)` and `d j k ∘ d i j = 0`. -/
structure HilbertComplex (𝕜 : Type*) [RCLike 𝕜] (W : ℤ → Type*) [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] where
  /-- the differentials -/
  d : ∀ i j, W i →ₗ.[𝕜] W j
  shape : ∀ i j, ¬ i + 1 = j → d i j = 0
  dense : ∀ i j, Dense ((d i j).domain : Set (W i))
  closed : ∀ i j, (d i j).IsClosed
  mapsTo : ∀ i j k (x : (d i j).domain), (d i j x : W j) ∈ (d j k).domain
  d_comp_d : ∀ i j k (x : (d i j).domain), d j k ⟨_, mapsTo i j k x⟩ = 0

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W)

/-- The **graph norm** `‖x‖_V = (‖x‖² + ‖d x‖²)^½` on `D(d i j)`. -/
def graphNorm (i j : ℤ) (x : (H.d i j).domain) : ℝ := √(‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2)

/-- A **subcomplex**: subspaces `Vⁱ ⊆ D(d i j)` with `d Vⁱ ⊆ Vʲ`. -/
structure Subcomplex where
  /-- the subspaces -/
  V : ∀ i, Submodule 𝕜 (W i)
  le_domain : ∀ i j, V i ≤ (H.d i j).domain
  mapsTo : ∀ i j (x : W i) (hx : x ∈ V i), (H.d i j ⟨x, le_domain i j hx⟩ : W j) ∈ V j

/-- A **cochain projection** onto `S`: projections `πⁱ : D(dⁱ) → Sⁱ` of the domain complex
commuting with `d`. -/
structure Subcomplex.CochainProjection {H : HilbertComplex 𝕜 W} (S : H.Subcomplex) where
  /-- the projections -/
  π : ∀ i, (H.d i (i + 1)).domain →ₗ[𝕜] S.V i
  proj : ∀ i (x : (H.d i (i + 1)).domain), (x : W i) ∈ S.V i → (π i x : W i) = x
  comm : ∀ i (x : (H.d i (i + 1)).domain),
    H.d i (i + 1) ⟨π i x, S.le_domain i (i + 1) (π i x).2⟩ =
      π (i + 1) ⟨H.d i (i + 1) x, H.mapsTo i (i + 1) (i + 1 + 1) x⟩

/-- A **family of subcomplexes** of `H` along the filter `l` (the refinement `h → 0`):
finite-dimensional subcomplexes `Vₕ` with cochain projections `πₕ`. It carries no bound and no
approximation property: these are hypotheses of the theorem. -/
structure SubcomplexFamily (κ : Type*) where
  /-- the filter of the refinement `h → 0` -/
  l : Filter κ
  /-- the subcomplexes -/
  V : κ → H.Subcomplex
  [finiteDimensional : ∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
  /-- the cochain projections -/
  π : ∀ h, (V h).CochainProjection

attribute [instance] SubcomplexFamily.finiteDimensional

/-- The distance `E(x) = inf_{v ∈ Vⁱ} ‖x - v‖_V` from `x ∈ D(d i j)` to `Vⁱ` in the graph norm. -/
def Subcomplex.graphDist {H : HilbertComplex 𝕜 W} (S : H.Subcomplex) (i j : ℤ)
    (x : (H.d i j).domain) : ℝ :=
  ⨅ v : S.V i, H.graphNorm i j (x - ⟨v, S.le_domain i j v.2⟩)

variable {H} {κ : Type*}

/-- The cochain projections of `F` are **bounded in the graph norm by `C`** in degree `i`,
uniformly in `h`: `‖πₕ x‖_V ≤ C ‖x‖_V` on `D(d i (i + 1))`. -/
def SubcomplexFamily.IsGraphBoundedBy (F : H.SubcomplexFamily κ) (i : ℤ) (C : ℝ) : Prop :=
  ∀ (h : κ) (x : (H.d i (i + 1)).domain),
    H.graphNorm i (i + 1) ⟨(F.π h).π i x, (F.V h).le_domain i (i + 1) ((F.π h).π i x).2⟩ ≤
      C * H.graphNorm i (i + 1) x

/-- The cochain projections of `F` are **bounded in the graph norm** in degree `i`, uniformly in
`h`. -/
def SubcomplexFamily.IsGraphBounded (F : H.SubcomplexFamily κ) (i : ℤ) : Prop :=
  ∃ C : ℝ, F.IsGraphBoundedBy i C

/-- `F` **approximates** in degree `i` in the graph norm: the distance from every `x ∈ D(d)` to
`Vₕⁱ` in the graph norm tends to `0`. -/
def SubcomplexFamily.Approximates (F : H.SubcomplexFamily κ) (i : ℤ) : Prop :=
  ∀ x : (H.d i (i + 1)).domain, Tendsto (fun h => (F.V h).graphDist i (i + 1) x) F.l (𝓝 0)

/-- **A Jackson estimate** for `F` ([AFW2010], §3.5): a mesh size `hₕ → 0` and, for every
regularity index `s : ρ`, classes `Reg s i L` of `s`-regular forms in `Wⁱ` with bound `L`,
approximated in `Vₕⁱ` at the order `hₕ^{ord s}`: some `v ∈ Vₕⁱ` has `‖x - v‖ ≤ B L hₕ^{ord s}`
and `‖d (x - v)‖ ≤ B L hₕ^{ord s}`. -/
structure SubcomplexFamily.Jackson (F : H.SubcomplexFamily κ) (ρ : Type*) where
  /-- the mesh size -/
  meshSize : κ → ℝ
  meshSize_nonneg : ∀ h, 0 ≤ meshSize h
  tendsto_meshSize : Tendsto meshSize F.l (𝓝 0)
  /-- `Reg s i L x`: `x ∈ Wⁱ` is `s`-regular with bound `L` -/
  Reg : ρ → ∀ i, ℝ → W i → Prop
  /-- the order of the class `s` -/
  ord : ρ → ℝ
  /-- the constants -/
  B : ρ → ℤ → ℝ
  jackson : ∀ s h i {L : ℝ} (x : W i), 0 ≤ L → Reg s i L x → ∃ v, ∃ hv : v ∈ (F.V h).V i,
    ‖x - v‖ ≤ B s i * (L * meshSize h ^ ord s) ∧ ∀ j (hx : x ∈ (H.d i j).domain),
      ‖H.d i j ⟨x - v, Submodule.sub_mem _ hx ((F.V h).le_domain i j hv)⟩‖ ≤
        B s i * (L * meshSize h ^ ord s)

end HilbertComplex

/-! ### Differential forms on `ℝⁿ` and the `L²` de Rham complexes -/

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

namespace PolySeq

variable (S : PolySeq)

/-- The space `P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` of form fields on `ℝⁿ` of the sequence in degree `k`. -/
def space (n k : ℕ) : Submodule ℝ (FormField n) :=
  (if S.full k then polyForm (n := n) (S.deg k) k else polyFormMinus (S.deg k) k).map evalForm

/-- `S` **reproduces polynomial forms of degree `s`** in the form degrees `j` and `j + 1`:
`P_sΛʲ ⊆ S_j` and `P_sΛʲ⁺¹ ⊆ S_{j+1}` (vacuous for `j < 0`). -/
def PolyOrderAt (n s : ℕ) (j : ℤ) : Prop :=
  ∀ k : ℕ, (k : ℤ) = j → (polyForm (n := n) s k).map evalForm ≤ S.space n k ∧
    (polyForm (n := n) s (k + 1)).map evalForm ≤ S.space n (k + 1)

end PolySeq

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
contains a ball `B(x, ρ)` with `h_T ≤ σ ρ`, that is `h_T / ρ_T ≤ σ` for the inradius `ρ_T`. -/
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

/-- `Ω` is a **bounded open domain star-shaped with respect to a ball** `B(x₀, s₀)`: the segment
from every point of the ball to every point of `Ω` lies in `Ω`. -/
def IsStarShapedBall (Ω : Set (Fin n → ℝ)) : Prop :=
  IsOpen Ω ∧ Bornology.IsBounded Ω ∧ ∃ x₀ : Fin n → ℝ, ∃ s₀ : ℝ, 0 < s₀ ∧
    ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ Ω

/-- The **parallelepiped** `A (0, 1)ⁿ + b` (an open box when `A` is diagonal). -/
def parallelepiped (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Set (Fin n → ℝ) :=
  (fun x => A.mulVec x + b) '' Set.univ.pi fun _ => Set.Ioo 0 1

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

/-! ### Smooth forms -/

/-- `x ∈ L²(Ω; Λʲ)` is (almost everywhere) a `C^{s+2}` form `w` of degree `j` whose
`(s+1)`-st derivative and that of `dw` are bounded by `L` on `cl Ω` (true in negative degrees):
the regularity class of the order `h^{s+1}`. -/
def IsCsForm (Ω : Set (Fin n → ℝ)) (s : ℕ) (j : ℤ) (L : ℝ) (x : L2Form Ω j) : Prop :=
  j < 0 ∨ ∃ w : FormField n, ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w ∧
    (∀ y (t : Finset (Fin n)), (t.card : ℤ) ≠ j → w y t = 0) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L) ∧
    ∀ t : FormIdx n j, ⇑(x t) =ᵐ[volume.restrict Ω] fun y => w y t.1

/-- `IsCsForm` for a form `w` vanishing outside `Ω` (the regularity class of `H̊Λ(Ω)`): `w` is
`C^{s+2}` on `ℝⁿ`, so all its derivatives of order at most `s + 2` vanish on `∂Ω`, a class
smaller than the forms of `H̊Λ(Ω)` of Sobolev regularity `s + 1`. -/
def IsCsFormMin (Ω : Set (Fin n → ℝ)) (s : ℕ) (j : ℤ) (L : ℝ) (x : L2Form Ω j) : Prop :=
  j < 0 ∨ ∃ w : FormField n, ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w ∧
    (∀ y (t : Finset (Fin n)), (t.card : ℤ) ≠ j → w y t = 0) ∧ (∀ y ∉ Ω, w y = 0) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L) ∧
    ∀ t : FormIdx n j, ⇑(x t) =ᵐ[volume.restrict Ω] fun y => w y t.1

/-! ### Maxwell's equations in vector proxies (`n = 3`) -/

/-- `L²(Ω; ℝ^ι)`: the square-integrable fields on `Ω ⊆ ℝ³` with components indexed by `ι`
(`Fin 1`: scalar fields, `Fin 3`: vector fields), an `ℓ²` sum of copies of `L²(Ω)`. -/
abbrev L2Field (Ω : Set (Fin 3 → ℝ)) (ι : Type) [Fintype ι] : Type :=
  PiLp 2 fun _ : ι => Lp ℝ 2 (volume.restrict Ω)

/-- The **weak realization** `A : L²(Ω; ℝ^ι) → L²(Ω; ℝ^κ)` of the first-order operator with
formal adjoint `Aᵗ` (as `dMax`): the adjoint of the closure of `Aᵗ` on test fields, so that
`u ∈ D(A)` iff some `w` has `⟪w, ψ⟫ = ⟪u, Aᵗψ⟫` for every test field `ψ`, and then `A u = w`. -/
def weakOp (Ω : Set (Fin 3 → ℝ)) {ι κ : Type} [Fintype ι] [Fintype κ]
    (At : ((Fin 3 → ℝ) → κ → ℝ) → (Fin 3 → ℝ) → ι → ℝ) : L2Field Ω ι →ₗ.[ℝ] L2Field Ω κ :=
  (Submodule.span ℝ {p : L2Field Ω κ × L2Field Ω ι | ∃ ψ : (Fin 3 → ℝ) → κ → ℝ,
    (∀ j, IsTestFn Ω fun x => ψ x j) ∧ (∀ j, ⇑(p.1 j) =ᵐ[volume.restrict Ω] fun x => ψ x j) ∧
    ∀ i, ⇑(p.2 i) =ᵐ[volume.restrict Ω] fun x => At ψ x i}).topologicalClosure.toLinearPMap†

/-- The **weak gradient** `grad : H¹(Ω) ⊆ L²(Ω) → L²(Ω; ℝ³)` (formal adjoint `-div`). -/
def grad (Ω : Set (Fin 3 → ℝ)) : L2Field Ω (Fin 1) →ₗ.[ℝ] L2Field Ω (Fin 3) :=
  weakOp Ω fun ψ x _ => -∑ j, partialDeriv j (fun y => ψ y j) x

/-- The **weak curl** `curl : H(curl, Ω) ⊆ L²(Ω; ℝ³) → L²(Ω; ℝ³)`,
`(curl v)ᵢ = ∂_{i+1} v_{i+2} - ∂_{i+2} v_{i+1}` (indices mod 3; formally self-adjoint). -/
def curl (Ω : Set (Fin 3 → ℝ)) : L2Field Ω (Fin 3) →ₗ.[ℝ] L2Field Ω (Fin 3) :=
  weakOp Ω fun ψ x i =>
    partialDeriv (i + 1) (fun y => ψ y (i + 2)) x - partialDeriv (i + 2) (fun y => ψ y (i + 1)) x

/-- The **weak divergence** `div : H(div, Ω) ⊆ L²(Ω; ℝ³) → L²(Ω)` (formal adjoint `-grad`). -/
def div (Ω : Set (Fin 3 → ℝ)) : L2Field Ω (Fin 3) →ₗ.[ℝ] L2Field Ω (Fin 1) :=
  weakOp Ω fun ψ x j => -partialDeriv j (fun y => ψ y 0) x

/-- The **vector proxy** of a `0`-form: the scalar `f_∅`. -/
def proxy0 {Ω : Set (Fin 3 → ℝ)} (u : L2Form Ω 0) : L2Field Ω (Fin 1) :=
  WithLp.toLp 2 fun _ => u ⟨∅, rfl⟩

/-- The **vector proxy** of a `1`-form `Σⱼ vⱼ dxⱼ`: the vector `v`. -/
def proxy1 {Ω : Set (Fin 3 → ℝ)} (u : L2Form Ω 1) : L2Field Ω (Fin 3) :=
  WithLp.toLp 2 fun j => u ⟨{j}, by simp⟩

/-- The **vector proxy** of a `2`-form `ω`: the vector `(ω₁₂, -ω₀₂, ω₀₁)`. -/
def proxy2 {Ω : Set (Fin 3 → ℝ)} (u : L2Form Ω 2) : L2Field Ω (Fin 3) :=
  WithLp.toLp 2 fun i => (-1 : ℝ) ^ (i : ℕ) • u ⟨Finset.univ.erase i, by simp⟩

/-- `(σ, E, B)` is a **strong solution of Maxwell's equations** on `[0, T]`: `σ' = -grad* E`,
`E' = grad σ - curl* B`, `B' = curl E` for the weak `grad`, `curl` and their adjoints
(`grad* = -div` with `E · n = 0`, `curl* = curl` with `B × n = 0`), the derivatives in `L²`;
`B ∈ L²(Ω; ℝ³)` is the last space of the window `H¹ → H(curl) → L²(Ω; ℝ³)`. -/
def IsMaxwellSolution (Ω : Set (Fin 3 → ℝ)) (T : ℝ) (σ : ℝ → L2Field Ω (Fin 1))
    (E B : ℝ → L2Field Ω (Fin 3)) : Prop :=
  ∀ t ∈ Icc 0 T, ∃ σ' E' B' g c, HasDerivWithinAt σ σ' (Icc 0 T) t ∧
    HasDerivWithinAt E E' (Icc 0 T) t ∧ HasDerivWithinAt B B' (Icc 0 T) t ∧
    (E t, -σ') ∈ (grad Ω)†.graph ∧ (σ t, g) ∈ (grad Ω).graph ∧ (B t, c) ∈ (curl Ω)†.graph ∧
    E' = g - c ∧ (E t, B') ∈ (curl Ω).graph

/-- `(σ, E, B)` is a **semi-discrete (Galerkin) solution of Maxwell's equations** on `[0, T]` in
`V⁰ × V¹ × V²`: `⟪σ', τ⟫ + ⟪E', F⟫ + ⟪B', G⟫ = ⟪grad σ, F⟫ + ⟪curl E, G⟫ - ⟪E, grad τ⟫ -
⟪B, curl F⟫` for all `τ ∈ V⁰`, `F ∈ V¹`, `G ∈ V²`. -/
def IsMaxwellGalerkin (Ω : Set (Fin 3 → ℝ)) (V₀ : Set (L2Field Ω (Fin 1)))
    (V₁ V₂ : Set (L2Field Ω (Fin 3))) (T : ℝ) (σ : ℝ → L2Field Ω (Fin 1))
    (E B : ℝ → L2Field Ω (Fin 3)) : Prop :=
  ∀ t ∈ Icc 0 T, σ t ∈ V₀ ∧ E t ∈ V₁ ∧ B t ∈ V₂ ∧ ∃ σ' E' B', HasDerivWithinAt σ σ' (Icc 0 T) t ∧
    HasDerivWithinAt E E' (Icc 0 T) t ∧ HasDerivWithinAt B B' (Icc 0 T) t ∧
    ∀ τ ∈ V₀, ∀ F ∈ V₁, ∀ G ∈ V₂, ∀ gσ gτ cE cF, (σ t, gσ) ∈ (grad Ω).graph →
      (τ, gτ) ∈ (grad Ω).graph → (E t, cE) ∈ (curl Ω).graph → (F, cF) ∈ (curl Ω).graph →
        ⟪σ', τ⟫_ℝ + ⟪E', F⟫_ℝ + ⟪B', G⟫_ℝ =
          ⟪gσ, F⟫_ℝ + ⟪cE, G⟫_ℝ - ⟪E t, gτ⟫_ℝ - ⟪B t, cF⟫_ℝ

/-! ### The theorems -/

/-- **The finite element de Rham complexes of `HΛ(Ω)`** ([AFW2006], §5; [AFW2010], §5.2, §5.5;
[ChristiansenWinther2008]; [Arnold2018], Ch. 7). Let `Ω` be star-shaped with respect to a ball,
`M_N` a shape-regular, quasi-uniform family of meshes of `Ω` with `h_N → 0`, and `S` an
admissible sequence. Then `HΛ(Ω)` (the weak exterior derivative `dMax`) is a Hilbert complex,
the finite element spaces `S_k(M_N)` are the spaces of a family of finite-dimensional
subcomplexes of it, along `N → ∞`, whose cochain projections are bounded in `L²(Ω; Λ)`
uniformly in `N` and hence in every graph norm, which approximates every element of `HΛᵏ(Ω)` in
the graph norm, and which has a Jackson estimate of order `h_N^{s+1}` for the `C^{s+2}` forms
(`IsCsForm`) of the degrees where `S` reproduces `P_sΛ` (`PolySeq.PolyOrderAt`). -/
theorem fem [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (S : PolySeq) :
    ∃ (H : HilbertComplex ℝ (L2Form Ω)) (F : H.SubcomplexFamily ℕ) (J : F.Jackson ℕ),
      (∀ k, H.d k (k + 1) = dMax Ω k) ∧ F.l = atTop ∧
      (∀ N k, ((F.V N).V k : Set (L2Form Ω k)) = femSpace Ω (M N) S k) ∧
      (∃ C : ℝ, ∀ N i (x : (H.d i (i + 1)).domain),
        ‖((F.π N).π i x : L2Form Ω i)‖ ≤ C * ‖(x : L2Form Ω i)‖) ∧
      (∀ i, F.IsGraphBounded i) ∧ (∀ i, F.Approximates i) ∧
      (∀ N, J.meshSize N = meshSize (M N)) ∧ (∀ s, J.ord s = s + 1) ∧
      ∀ s j L x, J.Reg s j L x ↔ S.PolyOrderAt n s j ∧ IsCsForm Ω s j L x := by
  sorry

/-- **The finite element de Rham complexes of `H̊Λ(Ω)`**: under the hypotheses of `fem`,
`H̊Λ(Ω)` (the closure `dMin` of `d` on test forms) is a Hilbert complex and the spaces
`S̊_k(M_N)` with vanishing boundary traces form a family of finite-dimensional subcomplexes of it
with cochain projections bounded in `L²(Ω; Λ)` uniformly in `N`, approximating in the graph norm,
with a Jackson estimate of order `h_N^{s+1}` for the `C^{s+2}` forms vanishing outside `Ω`
(`IsCsFormMin`). -/
theorem femMin [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (S : PolySeq) :
    ∃ (H : HilbertComplex ℝ (L2Form Ω)) (F : H.SubcomplexFamily ℕ) (J : F.Jackson ℕ),
      (∀ k, H.d k (k + 1) = dMin Ω k) ∧ F.l = atTop ∧
      (∀ N k, ((F.V N).V k : Set (L2Form Ω k)) = femSpaceMin Ω (M N) S k) ∧
      (∃ C : ℝ, ∀ N i (x : (H.d i (i + 1)).domain),
        ‖((F.π N).π i x : L2Form Ω i)‖ ≤ C * ‖(x : L2Form Ω i)‖) ∧
      (∀ i, F.IsGraphBounded i) ∧ (∀ i, F.Approximates i) ∧
      (∀ N, J.meshSize N = meshSize (M N)) ∧ (∀ s, J.ord s = s + 1) ∧
      ∀ s j L x, J.Reg s j L x ↔ S.PolyOrderAt n s j ∧ IsCsFormMin Ω s j L x := by
  sorry

/-- **Parallelepipeds** ([Freudenthal1942]; [AFW2010], §4): every parallelepiped
`Ω = A (0, 1)ⁿ + b`, `A` invertible, is star-shaped with respect to a ball, carries a
shape-regular, quasi-uniform family of meshes with `h_N → 0` (the images of the Freudenthal
meshes of the cube), and the weak and the minimal exterior derivatives have closed range in
every degree. With the graph-norm bounds of `fem` and `femMin`, these are the hypotheses of the
static FEEC theorem of `palomar/feec` (`FEEC.feec`, field `static`) for their families on `Ω`. -/
theorem fem_parallelepiped [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (b : Fin n → ℝ) :
    IsStarShapedBall (parallelepiped A b) ∧ (∃ M, IsMeshFamily (parallelepiped A b) M) ∧
      ∀ k, IsClosed (LinearMap.range (dMax (parallelepiped A b) k).toFun :
          Set (L2Form (parallelepiped A b) (k + 1))) ∧
        IsClosed (LinearMap.range (dMin (parallelepiped A b) k).toFun :
          Set (L2Form (parallelepiped A b) (k + 1))) := by
  sorry

/-- **Maxwell's equations** ([QuennevilleBelair2015], Ch. 4; [AFW2010], §4; [Monk2003]): on
`Ω ⊆ ℝ³` star-shaped with respect to a ball, with a shape-regular, quasi-uniform family of meshes
`M_N` and an admissible sequence `S`, the vector proxies `V_N⁰`, `V_N¹`, `V_N²` of `S_k(M_N)`
(for `S = P₁⁻`: the Lagrange, Nédélec edge and Raviart–Thomas face elements) lie in `H¹(Ω)`,
`H(curl, Ω)` and `H(div, Ω)`. Maxwell's equations are in Hodge-wave form: with `H = -B` they are
`E' = curl H`, `H' = -curl E` with perfect-magnetic-conductor walls. For data `(σ₀, E₀, B₀)` in the domain of the Maxwell operator and every `T`:
there is a unique strong solution on `[0, T]`, it conserves the energy, it satisfies the Gauss
laws `σ = 0`, `grad* E = 0`, `div B = 0` if the data do, and it is the uniform limit on `[0, T]`
of every family of Galerkin solutions in `V_N⁰ × V_N¹ × V_N²` whose initial data converge to the
data, `N → ∞`; such families exist. -/
theorem maxwell {Ω : Set (Fin 3 → ℝ)} (hΩ : IsStarShapedBall Ω) {M : ℕ → SimplicialMesh 3}
    (hM : IsMeshFamily Ω M) (S : PolySeq) :
    (∀ N, proxy0 '' femSpace Ω (M N) S 0 ⊆ (grad Ω).domain ∧
      proxy1 '' femSpace Ω (M N) S 1 ⊆ (curl Ω).domain ∧
      proxy2 '' femSpace Ω (M N) S 2 ⊆ (div Ω).domain) ∧
    ∀ σ₀ E₀ B₀, σ₀ ∈ (grad Ω).domain → E₀ ∈ (curl Ω).domain → E₀ ∈ (grad Ω)†.domain →
      B₀ ∈ (curl Ω)†.domain → ∀ T, ∃ σ E B, σ 0 = σ₀ ∧ E 0 = E₀ ∧ B 0 = B₀ ∧
        IsMaxwellSolution Ω T σ E B ∧
        (∀ σ₁ E₁ B₁, σ₁ 0 = σ₀ → E₁ 0 = E₀ → B₁ 0 = B₀ → IsMaxwellSolution Ω T σ₁ E₁ B₁ →
          ∀ t ∈ Icc 0 T, σ₁ t = σ t ∧ E₁ t = E t ∧ B₁ t = B t) ∧
        (∀ t ∈ Icc 0 T, ‖σ t‖ ^ 2 + ‖E t‖ ^ 2 + ‖B t‖ ^ 2 = ‖σ₀‖ ^ 2 + ‖E₀‖ ^ 2 + ‖B₀‖ ^ 2) ∧
        (σ₀ = 0 → (E₀, 0) ∈ (grad Ω)†.graph → (B₀, 0) ∈ (div Ω).graph → ∀ t ∈ Icc 0 T,
          σ t = 0 ∧ (E t, 0) ∈ (grad Ω)†.graph ∧ (B t, 0) ∈ (div Ω).graph) ∧
        (∀ (σh : ℕ → ℝ → L2Field Ω (Fin 1)) (Eh Bh : ℕ → ℝ → L2Field Ω (Fin 3)),
          (∀ N, IsMaxwellGalerkin Ω (proxy0 '' femSpace Ω (M N) S 0)
            (proxy1 '' femSpace Ω (M N) S 1) (proxy2 '' femSpace Ω (M N) S 2) T
            (σh N) (Eh N) (Bh N)) →
          Tendsto (fun N => σh N 0) atTop (𝓝 σ₀) → Tendsto (fun N => Eh N 0) atTop (𝓝 E₀) →
          Tendsto (fun N => Bh N 0) atTop (𝓝 B₀) →
          TendstoUniformlyOn σh σ atTop (Icc 0 T) ∧ TendstoUniformlyOn Eh E atTop (Icc 0 T) ∧
            TendstoUniformlyOn Bh B atTop (Icc 0 T)) ∧
        ∃ (σh : ℕ → ℝ → L2Field Ω (Fin 1)) (Eh Bh : ℕ → ℝ → L2Field Ω (Fin 3)),
          (∀ N, IsMaxwellGalerkin Ω (proxy0 '' femSpace Ω (M N) S 0)
            (proxy1 '' femSpace Ω (M N) S 1) (proxy2 '' femSpace Ω (M N) S 2) T
            (σh N) (Eh N) (Bh N)) ∧
          Tendsto (fun N => σh N 0) atTop (𝓝 σ₀) ∧ Tendsto (fun N => Eh N 0) atTop (𝓝 E₀) ∧
          Tendsto (fun N => Bh N 0) atTop (𝓝 B₀) := by
  sorry

end FEEC
