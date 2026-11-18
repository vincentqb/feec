module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Finite element methods for the Hodge wave and Maxwell equations

Do finite element methods for the Hodge wave equation `U' = (𝐝 - 𝐝*) U` converge, fully discrete
(under what time-step condition?) and, for Maxwell's equations, semi-discrete? Take the finite
element de Rham complexes of `palomar/fem`: `Ω ⊆ ℝⁿ` bounded, open and star-shaped with respect to
a ball, shape-regular, quasi-uniform simplicial meshes `M_N` of `Ω` with `h_N → 0`, an admissible
sequence `S` of `P_rΛ` and `P_r⁻Λ` spaces, in `HΛ(Ω)` or `H̊Λ(Ω)`, and the finite element forms
`Xₕ` of a window `[a, a + m)` of degrees.

* **The inverse estimate** `h_N ‖dv‖ ≤ C ‖v‖` holds on the finite element forms
  (`inverse_estimate`); on the window, `h_N ‖𝐝 x‖ ≤ C₀ ‖x‖` on `Xₕ`, so the discrete wave
  operator has `‖Lₕ‖ ≤ 2 C₀ / h_N`.
* **Fully discrete: Crank–Nicolson converges for every time step, leapfrog under the CFL
  condition** `2 C₀ Δt ≤ c h_N`, `c < 1` (`fem_wave`; [QuennevilleBelair2015], Ch. 4, 7;
  [Joly2003]): from any starting values in `Xₕ`, the error at `t_K = K Δt` (for leapfrog, `1 - c`
  times the error) is at most the starting errors plus `C (1 + T) L (h_N^{s+1} + Δt²)`, uniformly
  in `N`, for every solution with the homogeneous boundary conditions of the complex, `C³` in time
  with `‖∂ₜ³U‖ ≤ L`, whose values and time increments are `C^{s+2}` forms (vanishing outside `Ω`
  in `H̊Λ(Ω)`) with the bounds `L` and `L |t' - t|`, where `S` reproduces `P_sΛ` in the degrees
  `a, …, a + m`. With the natural boundary conditions a standing wave of the cube meets these
  hypotheses at all times and is neither zero nor stationary (`fem_wave_nonvacuous`).
* **Fully discrete, inhomogeneous Dirichlet data**: with the boundary degrees of freedom of the
  exact solution (the runs of [QuennevilleBelair2015], Ch. 7: the Whitney forms on the Freudenthal
  meshes of the cube, in `HΛ`), both schemes converge at `O(h + Δt²)` for every smooth solution
  with bound `L` (`RowSolution`): Crank–Nicolson for every time step from `u₀ = Π_h U(0)`, leapfrog
  under the CFL condition, with the factor `1 / (1 - c)`, from `u₀ = Π_h U(0)` and
  `u₁ = Π_h U(Δt)` (`crankNicolson_cube`, `leapfrog_cube`); some of these solutions are neither
  zero nor stationary (`rowSolution_nonvacuous`).
* **Semi-discrete: Maxwell's equations.** In vector proxies they are the Hodge wave equation of the
  window `[0, 3)` of `HΛ(Ω)` in `ℝ³`, the electric field in degree `1` (`maxwell`): well-posedness,
  conservation of the energy and of the Gauss laws, and the semi-discrete Galerkin solutions in
  the finite element spaces, which are unique, converge uniformly on `[0, T]` when their initial
  data converge (no rate; the fully discrete schemes of this window are those of `fem_wave`, in
  forms, and semi-discrete convergence on every window is the wave clause of
  `FEEC.evolutionFEEC` of `palomar/feec`).

## Conventions

Points of `ℝⁿ` are `Fin n → ℝ` (Lebesgue measure; diameters and balls of the sup norm, which
change the shape-regularity constant `h_T / ρ_T` by a factor depending only on `n`). A `k`-form
has coefficients `ω_s` on `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}`, `s₁ < ⋯ < s_k` (`FormIdx n k`);
`L²(Ω; Λᵏ)` is the `ℓ²` sum of copies of `L²(Ω)` (`L2Form`), and `Total (L2Form Ω) a m` the
window `L²(Ω; Λᵃ) ⊕ ⋯ ⊕ L²(Ω; Λ^{a+m-1})`. In `ℝ³` a scalar field has one component (`Fin 1`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3, §5
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4, §5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7, 8
* [S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*][BrennerScott2008],
  §4.5
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1–§3.2
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [P. Joly, *Variational Methods for Time-Dependent Wave Propagation Problems*][Joly2003]
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 1, 7
* [H. Whitney, *Geometric Integration Theory*][Whitney1957], Ch. IV
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 4, 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Filter Topology Set LinearPMap MeasureTheory

@[expose] public noncomputable section

namespace FEEC

/-! ### Hilbert complexes and their windows (the notions of `palomar/feec`) -/

-- palomar-shared: HilbertComplex
/-- A **Hilbert complex** over `𝕜` on `ℤ`: closed densely defined operators `d i j : Wⁱ → Wʲ`,
zero unless `j = i + 1`, with `R(d i j) ⊆ D(d j k)` and `d j k ∘ d i j = 0`. -/
structure HilbertComplex (𝕜 : Type*) [RCLike 𝕜] (W : ℤ → Type*) [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] where
  d : ∀ i j, W i →ₗ.[𝕜] W j
  shape : ∀ i j, ¬ i + 1 = j → d i j = 0
  dense : ∀ i j, Dense ((d i j).domain : Set (W i))
  closed : ∀ i j, (d i j).IsClosed
  mapsTo : ∀ i j k (x : (d i j).domain), (d i j x : W j) ∈ (d j k).domain
  d_comp_d : ∀ i j k (x : (d i j).domain), d j k ⟨_, mapsTo i j k x⟩ = 0
-- palomar-shared-end: HilbertComplex
-- palomar-shared: window
/-- The total space `Wᵃ ⊕ ⋯ ⊕ W^{a+m-1}` of the **window** `[a, a + m)` (an `ℓ²` sum). -/
abbrev Total (W : ℤ → Type*) (a : ℤ) (m : ℕ) : Type _ := PiLp 2 fun i : Fin m => W (a + (i : ℕ))
namespace HilbertComplex
variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] (H : HilbertComplex 𝕜 W) (a : ℤ)
  (m : ℕ)
/-- The domain `{x | ∀ i j, xᵢ ∈ D(d (a + i) (a + j))}` of the total differential. -/
def totalDomain : Submodule 𝕜 (Total W a m) where
  carrier := {x | ∀ i j : Fin m, x i ∈ (H.d (a + (i : ℕ)) (a + (j : ℕ))).domain}
  add_mem' hx hy i j := (H.d _ _).domain.add_mem (hx i j) (hy i j)
  zero_mem' _ _ := (H.d _ _).domain.zero_mem
  smul_mem' c _ hx i j := (H.d _ _).domain.smul_mem c (hx i j)
/-- The **total differential** `(𝐝 x)ⱼ = ∑ᵢ d (a + i) (a + j) xᵢ` of the window. -/
def totalD : Total W a m →ₗ.[𝕜] Total W a m where
  domain := H.totalDomain a m
  toFun :=
    { toFun := fun x => WithLp.toLp 2 fun j : Fin m =>
        ∑ i : Fin m, H.d (a + (i : ℕ)) (a + (j : ℕ)) ⟨(x : Total W a m) i, x.2 i j⟩
      map_add' := fun x y => PiLp.ext fun j => by
        rw [PiLp.add_apply, PiLp.toLp_apply, PiLp.toLp_apply, PiLp.toLp_apply,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => (H.d _ _).map_add ⟨_, x.2 i j⟩ ⟨_, y.2 i j⟩
      map_smul' := fun c x => PiLp.ext fun j => by
        rw [PiLp.smul_apply, PiLp.toLp_apply, PiLp.toLp_apply, RingHom.id_apply,
          Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => (H.d _ _).map_smul c ⟨_, x.2 i j⟩ }
/-- The **Hodge–Dirac (wave) operator** `L = 𝐝 - 𝐝*` of the window; `L² = -Δ`. -/
def wave : Total W a m →ₗ.[𝕜] Total W a m := H.totalD a m - (H.totalD a m)†
end HilbertComplex
-- palomar-shared-end: window

/-! ### The fully discrete Hodge wave equation on a window -/

namespace HilbertComplex
variable {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)]
  [∀ i, CompleteSpace (W i)] (H : HilbertComplex ℝ W) (a : ℤ) (m : ℕ)

open Classical in
/-- The total differential `𝐝 x` of `x ∈ D(𝐝)`, read as `0` off `D(𝐝)` (it is only applied to
finite element forms, which lie in `D(𝐝)`). -/
def dApply (x : Total W a m) : Total W a m :=
  if h : x ∈ (H.totalD a m).domain then H.totalD a m ⟨x, h⟩ else 0
/-- The **form of the Hodge wave operator** `L = 𝐝 - 𝐝*` of the window,
`a(x, y) = ⟪𝐝 x, y⟫ - ⟪x, 𝐝 y⟫` on `D(𝐝)`, so that `a(x, y) = ⟪L x, y⟫` for `x ∈ D(L)`. -/
def waveForm (x y : Total W a m) : ℝ := ⟪H.dApply a m x, y⟫_ℝ - ⟪x, H.dApply a m y⟫_ℝ
/-- One **Crank–Nicolson step** of the Hodge wave equation in the trial space `V`, with test space
`V₀ ⊆ V` and boundary values `g`: `u' ∈ V`, `u' - g ∈ V₀` (the boundary degrees of freedom of `g`),
`⟪u' - u, v⟫ = (Δt / 2) a(u' + u, v)` on `V₀`. For `V₀ = V`, `g = 0` (homogeneous boundary
conditions) `u' = r(Δt Lₕ) u`, `r(z) = (2 + z) / (2 - z)`, `Lₕ` the discrete wave operator. -/
def IsCNStep (V V₀ : Set (Total W a m)) (Δt : ℝ) (g u u' : Total W a m) : Prop :=
  u' ∈ V ∧ u' - g ∈ V₀ ∧ ∀ v ∈ V₀, ⟪u' - u, v⟫_ℝ = Δt / 2 * H.waveForm a m (u' + u) v
/-- One **leapfrog step** ([Joly2003]), trial space `V`, test space `V₀ ⊆ V`, boundary values `g`:
`u'' ∈ V`, `u'' - g ∈ V₀`, `⟪u'' - u, v⟫ = 2 Δt a(u', v)` on `V₀`; the explicit three-level
scheme `uₙ₊₂ = uₙ + 2 Δt Lₕ uₙ₊₁` (one solve with the mass matrix). -/
def IsLeapfrogStep (V V₀ : Set (Total W a m)) (Δt : ℝ) (g u u' u'' : Total W a m) : Prop :=
  u'' ∈ V ∧ u'' - g ∈ V₀ ∧ ∀ v ∈ V₀, ⟪u'' - u, v⟫_ℝ = 2 * Δt * H.waveForm a m u' v
end HilbertComplex

/-! ### Differential forms on `ℝⁿ` and the `L²` de Rham complexes -/

variable {n : ℕ}

-- palomar-shared: FormField
/-- A **form field** on `ℝⁿ`: at each point a coefficient of `dx_s` for every subset `s` of
`Fin n` (a `k`-form when those off the `k`-subsets vanish). -/
abbrev FormField (n : ℕ) : Type := (Fin n → ℝ) → Finset (Fin n) → ℝ
/-- The sign `ε(j, s) = (-1)^{#{l ∈ s | l < j}}` of moving `dx_j` to its place in `dx_s`. -/
def sgn {n : ℕ} {R : Type*} [Ring R] (j : Fin n) (s : Finset (Fin n)) : R :=
  (-1) ^ (s.filter fun l => l < j).card
-- palomar-shared-end: FormField
-- palomar-shared: forms
/-- The coefficients of a `k`-form on `ℝⁿ`: the `k`-subsets `s = {s₁ < ⋯ < s_k}` of `Fin n`,
`s` indexing `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}` (none unless `0 ≤ k ≤ n`). -/
abbrev FormIdx (n : ℕ) (k : ℤ) : Type := {s : Finset (Fin n) // (s.card : ℤ) = k}
/-- `L²(Ω; Λᵏ)`: an `L²(Ω)` coefficient (Lebesgue measure) for each `dx_s`, an `ℓ²` sum. -/
abbrev L2Form {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : Type :=
  PiLp 2 fun _ : FormIdx n k => Lp ℝ 2 (volume.restrict Ω)
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

/-! ### Polynomial differential forms and admissible sequences ([AFW2006], §3, §5) -/

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
-- palomar-shared: PolyOrderAt
/-- The admissible sequence `S` **reproduces polynomial forms of degree `s`** in the form degrees
`j` and `j + 1`: `P_sΛʲ ⊆ S_j` and `P_sΛʲ⁺¹ ⊆ S_{j+1}` (vacuous for `j < 0`). -/
def PolySeq.PolyOrderAt (S : PolySeq) (n s : ℕ) (j : ℤ) : Prop :=
  ∀ k : ℕ, (k : ℤ) = j → (polyForm ℝ n s k).map evalForm ≤ S.space n k ∧
    (polyForm ℝ n s (k + 1)).map evalForm ≤ S.space n (k + 1)
-- palomar-shared-end: PolyOrderAt
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

/-! ### Domains, meshes and the finite element spaces (the notions of `palomar/fem`) -/

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
-- palomar-shared: meshFamily
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
-- palomar-shared-end: meshFamily
-- palomar-shared: IsStarShapedBall
/-- `Ω` is a **bounded open domain star-shaped with respect to a ball** `B(x₀, s₀)`: the segment
from every point of the ball to every point of `Ω` lies in `Ω`. -/
def IsStarShapedBall {n : ℕ} (Ω : Set (Fin n → ℝ)) : Prop :=
  IsOpen Ω ∧ Bornology.IsBounded Ω ∧ ∃ x₀ : Fin n → ℝ, ∃ s₀ : ℝ, 0 < s₀ ∧
    ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ Ω
-- palomar-shared-end: IsStarShapedBall
-- palomar-shared: covEval
/-- The value `α(v₁, …, v_k) = Σ_{#s = k} α_s det (v_l(s_i))_{i,l}` of the `k`-covector `α` on
the vectors `v₁, …, v_k`. -/
def covEval {n k : ℕ} (α : Finset (Fin n) → ℝ) (v : Fin k → Fin n → ℝ) : ℝ :=
  ∑ s : Finset (Fin n), if h : s.card = k then
    α s * (Matrix.of fun i l => v l (s.orderEmbOfFin h i)).det else 0
-- palomar-shared-end: covEval
-- palomar-shared: femSpace
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

/-! ### Finite element forms of a window and the Whitney interpolant -/

/-- The finite element space `Xₕ = S_a(M) ⊕ ⋯ ⊕ S_{a+m-1}(M)` of the window `[a, a + m)`, with
vanishing traces on the facets `Γ`: the forms of the window whose components lie in `femSpace`. -/
def femTotal (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (S : PolySeq)
    (Γ : Set (Finset (Fin n → ℝ))) (a : ℤ) (m : ℕ) : Set (Total (L2Form Ω) a m) :=
  {x | ∀ i : Fin m, x i ∈ femSpace Ω M S Γ (a + (i : ℕ))}
/-- The **integral of a `k`-form over the oriented `k`-simplex** `p` in `ℝⁿ`: `∫_p w =
∫_{T̂_k} w(F(x))(p₁ - p₀, …, p_k - p₀) dx`, `F(x) = p₀ + Σᵢ xᵢ (pᵢ₊₁ - p₀)`, on the reference
simplex `T̂_k = {x ≥ 0, Σᵢ xᵢ ≤ 1}`. -/
def simplexIntegral {k : ℕ} (p : Fin (k + 1) → Fin n → ℝ) (w : FormField n) : ℝ :=
  ∫ x in {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1},
    covEval (w (p 0 + ∑ i, x i • (p i.succ - p 0))) fun i => p i.succ - p 0
/-- `x` is **the Whitney interpolant** `Π_h w` of the form fields `w = (w_a, …, w_{a+m-1})` on the
mesh `M` ([Whitney1957], Ch. IV; [Arnold2018], Ch. 7): in every degree `k = a + i ≥ 0` of the
window, `xᵢ` lies in the Whitney space `P₁⁻Λᵏ(M)` with pieces `p_T` having the degrees of freedom of
`wᵢ`, `∫_f p_T = ∫_f wᵢ` on every oriented `k`-face `f` of every simplex `T`. -/
def IsWhitneyInterp (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (a : ℤ) (m : ℕ)
    (w : Fin m → FormField n) (x : Total (L2Form Ω) a m) : Prop :=
  ∀ i : Fin m, ∃ p, IsFemPieces Ω M topSeq (a + (i : ℕ)) (x i) p ∧ ∀ T ∈ M.simplices,
    ∀ q : Fin ((a + (i : ℕ)).toNat + 1) → Fin (n + 1), Function.Injective q →
      simplexIntegral (T.points ∘ q) (p T) = simplexIntegral (T.points ∘ q) (w i)
/-- `x` is (almost everywhere on `Ω`) the form fields `w = (w_a, …, w_{a+m-1})` of the window. -/
def IsRepr (Ω : Set (Fin n → ℝ)) (a : ℤ) (m : ℕ) (w : Fin m → FormField n)
    (x : Total (L2Form Ω) a m) : Prop :=
  ∀ i : Fin m, ∀ s : FormIdx n (a + (i : ℕ)), ⇑(x i s) =ᵐ[volume.restrict Ω] fun y => w i y s.1

/-! ### Smooth forms and smooth waves -/

-- palomar-shared: IsCsForm
/-- `x ∈ L²(Ω; Λʲ)` is a.e. a `C^{s+2}` form `w` of degree `j` with `‖D^{s+1} w‖, ‖D^{s+1} dw‖ ≤ L`
on `cl Ω` (true in negative degrees): the regularity class of the order `h^{s+1}`. -/
def IsCsForm {n : ℕ} (Ω : Set (Fin n → ℝ)) (s : ℕ) (j : ℤ) (L : ℝ) (x : L2Form Ω j) : Prop :=
  j < 0 ∨ ∃ w : FormField n, ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w ∧
    (∀ y (t : Finset (Fin n)), (t.card : ℤ) ≠ j → w y t = 0) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L) ∧
    ∀ t : FormIdx n j, ⇑(x t) =ᵐ[volume.restrict Ω] fun y => w y t.1
-- palomar-shared-end: IsCsForm
-- palomar-shared: IsCsFormMin
/-- `x ∈ L²(Ω; Λʲ)` is a.e. a `C^{s+2}` form `w` of degree `j` **vanishing outside `Ω`** with
`‖D^{s+1} w‖, ‖D^{s+1} dw‖ ≤ L` on `cl Ω` (true in negative degrees): the regularity class of the
order `h^{s+1}` with vanishing traces (for Lipschitz `Ω` the derivatives of `w` of order at most
`s + 2` vanish on `∂Ω`, a class smaller than `H̊Λ(Ω) ∩ H^{s+1}`). -/
def IsCsFormMin {n : ℕ} (Ω : Set (Fin n → ℝ)) (s : ℕ) (j : ℤ) (L : ℝ) (x : L2Form Ω j) : Prop :=
  j < 0 ∨ ∃ w : FormField n, ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w ∧
    (∀ y (t : Finset (Fin n)), (t.card : ℤ) ≠ j → w y t = 0) ∧ (∀ y ∉ Ω, w y = 0) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L) ∧
    ∀ t : FormIdx n j, ⇑(x t) =ᵐ[volume.restrict Ω] fun y => w y t.1
-- palomar-shared-end: IsCsFormMin

/-- A **smooth solution of the Hodge wave equation** `U' = (d - dᵗ) U` on the window
`Λ⁰ → Λ¹ → Λ²` of `ℝ³` (no boundary condition; one row of [QuennevilleBelair2015], (4.14)): forms
`u t i` of degree `i` (`σ`, `E`, `B`), `C²` in space and `C³` in time with jointly continuous time
derivatives `u₁, u₂, u₃`, solving `σ' = -dᵗE`, `E' = dσ - dᵗB`, `B' = dE` pointwise, with
`‖Du‖, ‖D du‖ ≤ L` on `cl Q`, `Q = (0, ½)³`, these `L`-Lipschitz in `t ∈ [0, T]`, and
`|∂ₜ³u| ≤ L` on `[0, T] × Q`. -/
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

/-! ### The fully discrete Hodge wave equation -/

/-- **The global inverse estimate** ([Ciarlet2002], §3.2; [BrennerScott2008], §4.5): for a
shape-regular, quasi-uniform family of meshes `M_N` of an open `Ω` whose open simplices lie in `Ω`
(true when `Ω` is the interior of its closure, e.g. Lipschitz or star-shaped), every admissible
sequence and every degree `k`, the forms `v` of `S_k(M_N)` lie in `HΛᵏ(Ω)` and
`h_N ‖dv‖ ≤ C ‖v‖`, `C` independent of `N`. It bounds the discrete wave operator,
`‖Lₕ‖ ≤ 2 C / h_N`: the CFL condition of `fem_wave` and `leapfrog_cube`. -/
theorem inverse_estimate [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M)
    (hint : ∀ N, ∀ T ∈ (M N).simplices, interior T.closedInterior ⊆ Ω) (S : PolySeq) (k : ℕ) :
    ∃ C, ∀ N, ∀ v ∈ femSpace Ω (M N) S ∅ k, ∃ hv : v ∈ (dMax Ω k).domain,
      meshSize (M N) * ‖dMax Ω k ⟨v, hv⟩‖ ≤ C * ‖v‖ := by
  sorry

/-- **The fully discrete Hodge wave equation** ([QuennevilleBelair2015], Ch. 4, 7; [Joly2003];
[Arnold2018], Ch. 8). For `Ω` star-shaped with respect to a ball, shape-regular, quasi-uniform
meshes `M_N` of `Ω` with `h_N → 0` and an admissible sequence `S` (the setting of `palomar/fem`),
`HΛ(Ω)` (`b = false`, natural boundary conditions) or `H̊Λ(Ω)` (`b = true`, vanishing traces) is a
Hilbert complex `H`, and on every window `[a, a + m)`, with its finite element forms `Xₕ`
(`femTotal`): some `C₀` has `h_N ‖𝐝 x‖ ≤ C₀ ‖x‖` on `Xₕ` (inverse estimate); and for every `s`
such that `S` reproduces `P_sΛ` in the degrees `a, …, a + m` (`PolySeq.PolyOrderAt` in the
degrees of the window), some `C` (independent of `N`, `Δt`, `T`, `L`, `U`, `c`, `C₀`) bounds the
errors of the iterates `uₖ ∈ Xₕ`, from any starting values in `Xₕ`, for every solution `U` of
`U' = (𝐝 - 𝐝*) U` on `[0, T]` (in the domain of the wave operator of `H`: its boundary
conditions), `C³` in time on `ℝ` with `‖∂ₜ³U‖ ≤ L` on `[0, T]`, whose values and time increments
are `C^{s+2}` forms (`IsCsForm`, resp. `IsCsFormMin`) with the bounds `L`, `L |t' - t|`,
`Δt > 0`, `K Δt ≤ T`: `‖u_K - U(K Δt)‖ ≤ ‖u₀ - U(0)‖ + C (1 + T) L (h_N^{s+1} + Δt²)` for
**Crank–Nicolson** (every time step), and `(1 - c) ‖u_K - U(K Δt)‖ ≤ ‖u₀ - U(0)‖ + ‖u₁ - U(Δt)‖ +
C (1 + T) L (h_N^{s+1} + Δt²)` for **leapfrog** under the CFL condition `2 C₀ Δt ≤ c h_N`,
`c < 1`, for every constant `C₀ ≥ 0` of the inverse estimate. For `U = 0` these are the stability
bounds `‖u_K‖ ≤ ‖u₀‖` and `(1 - c) ‖u_K‖ ≤ ‖u₀‖ + ‖u₁‖`. (For `H̊Λ(Ω)`, `IsCsFormMin` asks the
derivatives of order at most `s + 2` to vanish on `∂Ω` at every `t ∈ [0, T]`: a wave that reaches
the boundary before `T` is in general not in the class.) -/
theorem fem_wave [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (S : PolySeq) (b : Bool) :
    ∃ H : HilbertComplex ℝ (L2Form Ω), (∀ k, H.d k (k + 1) = if b then dMin Ω k else dMax Ω k) ∧
    ∀ (a : ℤ) (m : ℕ),
    let X : ℕ → Set (Total (L2Form Ω) a m) := fun N =>
      femTotal Ω (M N) S (if b then (M N).boundaryFacets else ∅) a m
    let Reg := if b then IsCsFormMin Ω else IsCsForm Ω
    let IsInv C₀ := ∀ N, ∀ x ∈ X N, meshSize (M N) * ‖H.dApply a m x‖ ≤ C₀ * ‖x‖
    (∃ C₀, IsInv C₀) ∧
    ∀ s : ℕ, (∀ i : Fin m, S.PolyOrderAt n s (a + (i : ℕ))) → ∃ C : ℝ,
      ∀ (T L : ℝ) (U U₁ U₂ U₃ : ℝ → Total (L2Form Ω) a m),
      (∀ t, HasDerivAt U (U₁ t) t ∧ HasDerivAt U₁ (U₂ t) t ∧ HasDerivAt U₂ (U₃ t) t) →
      (∀ t ∈ Icc 0 T, ‖U₃ t‖ ≤ L ∧ (U t, U₁ t) ∈ (H.wave a m).graph) →
      (∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T, ∀ i : Fin m, Reg s (a + (i : ℕ)) L (U t i) ∧
        Reg s (a + (i : ℕ)) (L * |t' - t|) (U t' i - U t i)) →
      ∀ N (Δt : ℝ) (K : ℕ) (u : ℕ → Total (L2Form Ω) a m), 0 < Δt → K * Δt ≤ T →
        ((∀ k < K, H.IsCNStep a m (X N) (X N) Δt 0 (u k) (u (k + 1))) → u 0 ∈ X N →
          ‖u K - U (K * Δt)‖ ≤
            ‖u 0 - U 0‖ + C * (1 + T) * L * (meshSize (M N) ^ (s + 1) + Δt ^ 2)) ∧
        ∀ C₀ c : ℝ, 0 ≤ C₀ → IsInv C₀ → c < 1 → 2 * C₀ * Δt ≤ c * meshSize (M N) →
          (∀ k, k + 2 ≤ K → H.IsLeapfrogStep a m (X N) (X N) Δt 0 (u k) (u (k + 1)) (u (k + 2))) →
          u 0 ∈ X N → u 1 ∈ X N → (1 - c) * ‖u K - U (K * Δt)‖ ≤
            ‖u 0 - U 0‖ + ‖u 1 - U Δt‖ + C * (1 + T) * L * (meshSize (M N) ^ (s + 1) + Δt ^ 2) := by
  sorry

/-- **Non-vacuity of `fem_wave`: a standing wave with the natural boundary conditions.** The cube
`Q = (0, ½)ⁿ` is star-shaped with respect to a ball and has a shape-regular, quasi-uniform family
of meshes with `h_N → 0`, and on the window `[0, 2)` of `HΛ(Q)` (`b = false`) the standing wave
`U(t) = (cos 2πt cos 2πx₀, -sin 2πt sin 2πx₀ dx₀)` (in the proof), a solution of `σ' = -d*E`,
`E' = dσ` with `E · n = 0` on `∂Q`, meets the hypotheses of `fem_wave` on the exact solution at
all times, for every `s`, with some bound `L`, and is neither zero nor stationary at any time. -/
theorem fem_wave_nonvacuous [NeZero n] (s : ℕ) :
    IsStarShapedBall (cube n) ∧ (∃ M, IsMeshFamily (cube n) M) ∧
    ∀ H : HilbertComplex ℝ (L2Form (cube n)), (∀ k, H.d k (k + 1) = dMax (cube n) k) →
    ∃ (L : ℝ) (U U₁ U₂ U₃ : ℝ → Total (L2Form (cube n)) 0 2),
      (∀ t, HasDerivAt U (U₁ t) t ∧ HasDerivAt U₁ (U₂ t) t ∧ HasDerivAt U₂ (U₃ t) t) ∧
      (∀ t, ‖U₃ t‖ ≤ L ∧ (U t, U₁ t) ∈ (H.wave 0 2).graph) ∧
      (∀ t t' (i : Fin 2), IsCsForm (cube n) s ((0 : ℤ) + (i : ℕ)) L (U t i) ∧
        IsCsForm (cube n) s ((0 : ℤ) + (i : ℕ)) (L * |t' - t|) (U t' i - U t i)) ∧
      ∀ t, U t ≠ 0 ∧ U₁ t ≠ 0 := by
  sorry

/-! ### The Whitney schemes of the cube with the boundary data of the exact solution -/

/-- **The Crank–Nicolson Whitney scheme with the boundary degrees of freedom of the exact solution
converges at `O(h + Δt²)`** ([QuennevilleBelair2015], Ch. 7; [Arnold2018], Ch. 7; [Monk2003];
[Thomee2006]). The cube `Q = (0, ½)³` has shape-regular, quasi-uniform Freudenthal meshes `𝒯_N`,
`h_N → 0`, and `HΛ(Q)` is a Hilbert complex `H`, on whose window `[0, 3)`, with the Whitney spaces
`Vₕ` (`topSeq`) and their fields `V̊ₕ` with vanishing boundary traces: continuous `w` have exactly
one Whitney interpolant `Π_h w` (the forms of `P₁⁻Λ` with the face integrals of `w`) on every
window `[0, m)`; the step from `u` with the boundary degrees of freedom of `g` (test space `V̊ₕ`)
is uniquely solvable for all `g, u ∈ Vₕ`, `Δt`; `V̊ₕ¹ ≠ 0`; and some `C` has, for every smooth
solution `U` with bound `L` (`RowSolution`), `Δt > 0`, `M Δt ≤ T`, for the iterates from
`u₀ = Π_h U(0)` with the boundary degrees of freedom of `Π_h U(tₙ)`,
`‖u_M - U(t_M)‖ ≤ C L (1 + T) (h_N + Δt²)`. With vanishing boundary data (`gₙ = 0`) the scheme on
`V̊ₕ` is that of `fem_wave` (`b = true`, `S = topSeq`); the hypotheses on the solution differ
(there `IsCsFormMin`, flat on `∂Q`; here `RowSolution`, no boundary condition), so neither
statement contains the other. -/
theorem crankNicolson_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3) (C : ℝ), IsMeshFamily (cube 3) 𝒯 ∧
    IsFreudenthal 𝒯 ∧ ∃ H : HilbertComplex ℝ (L2Form (cube 3)),
      (∀ k, H.d k (k + 1) = dMax (cube 3) k) ∧
    let V : ℕ → Set (Total (L2Form (cube 3)) 0 3) := fun N => femTotal (cube 3) (𝒯 N) topSeq ∅ 0 3
    let V₀ : ℕ → Set (Total (L2Form (cube 3)) 0 3) := fun N =>
      femTotal (cube 3) (𝒯 N) topSeq (𝒯 N).boundaryFacets 0 3
    (∀ N m (w : Fin m → FormField 3), (∀ i, Continuous (w i)) →
      ∃! x, IsWhitneyInterp (cube 3) (𝒯 N) 0 m w x) ∧
    (∀ N Δt g u, g ∈ V N → u ∈ V N → ∃! u', H.IsCNStep 0 3 (V N) (V₀ N) Δt g u u') ∧
    (∀ N, ∃ v ∈ femSpace (cube 3) (𝒯 N) topSeq (𝒯 N).boundaryFacets 1, v ≠ 0) ∧
    ∀ N T L (X : RowSolution T L) (Δt : ℝ) (M : ℕ) (u g : ℕ → Total (L2Form (cube 3)) 0 3),
      0 < Δt → M * Δt ≤ T →
      (∀ k < M, H.IsCNStep 0 3 (V N) (V₀ N) Δt (g (k + 1)) (u k) (u (k + 1))) →
      (∀ k < M, ∃ w, IsWhitneyInterp (cube 3) (𝒯 N) 0 3 (X.u ((k + 1 : ℕ) * Δt)) w ∧
        g (k + 1) - w ∈ V₀ N) →
      IsWhitneyInterp (cube 3) (𝒯 N) 0 3 (X.u 0) (u 0) → ∀ U, IsRepr (cube 3) 0 3 (X.u (M * Δt)) U →
        ‖u M - U‖ ≤ C * L * (1 + T) * (meshSize (𝒯 N) + Δt ^ 2) := by
  sorry

/-- **The explicit leapfrog Whitney scheme under a CFL condition, with the boundary degrees of
freedom of the exact solution** ([Joly2003]; [QuennevilleBelair2015], Ch. 7). With `𝒯_N`, the
Hilbert complex `HΛ(Q)`, `Vₕ` and `V̊ₕ` as in `crankNicolson_cube`: some `C₀` has
`h_N ‖𝐝 v‖ ≤ C₀ ‖v‖` on `Vₕ` (`inverse_estimate`), so `2 C₀ Δt ≤ c h_N` is a CFL condition
`Δt ‖Lₕ‖ ≤ c`; the step is uniquely solvable for all `g, u, u' ∈ Vₕ`, `Δt`; and some `C` serves
**every** constant `C₀ ≥ 0` of the inverse estimate (none is explicit) under the CFL condition
with `c < 1`: iterates with vanishing boundary degrees of freedom from `u₀, u₁ ∈ V̊ₕ` have
`√(1 - c) ‖u_{m+1}‖ ≤ √((1 + c)(‖u₀‖² + ‖u₁‖²))`, and for `U`, `L`, `Δt`, `M` as there the
iterates from `u₀ = Π_h U(0)`, `u₁ = Π_h U(Δt)` (no starting procedure is analysed) with the
boundary degrees of freedom of `Π_h U(tₙ)` have
`‖u_M - U(t_M)‖ ≤ C L (1 + T) (h_N + Δt²) / (1 - c)`. -/
theorem leapfrog_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3) (C : ℝ), IsMeshFamily (cube 3) 𝒯 ∧
    IsFreudenthal 𝒯 ∧ ∃ H : HilbertComplex ℝ (L2Form (cube 3)),
      (∀ k, H.d k (k + 1) = dMax (cube 3) k) ∧
    let V : ℕ → Set (Total (L2Form (cube 3)) 0 3) := fun N => femTotal (cube 3) (𝒯 N) topSeq ∅ 0 3
    let V₀ : ℕ → Set (Total (L2Form (cube 3)) 0 3) := fun N =>
      femTotal (cube 3) (𝒯 N) topSeq (𝒯 N).boundaryFacets 0 3
    let IsInv C₀ := ∀ N, ∀ v ∈ V N, meshSize (𝒯 N) * ‖H.dApply 0 3 v‖ ≤ C₀ * ‖v‖
    (∃ C₀, IsInv C₀) ∧ (∀ N Δt g u u', g ∈ V N → u ∈ V N → u' ∈ V N →
      ∃! u'', H.IsLeapfrogStep 0 3 (V N) (V₀ N) Δt g u u' u'') ∧ ∀ C₀, 0 ≤ C₀ → IsInv C₀ →
    (∀ N Δt c (u : ℕ → Total (L2Form (cube 3)) 0 3) m, 0 ≤ Δt → c < 1 →
      2 * C₀ * Δt ≤ c * meshSize (𝒯 N) →
      (∀ k < m, H.IsLeapfrogStep 0 3 (V N) (V₀ N) Δt 0 (u k) (u (k + 1)) (u (k + 2))) →
      u 0 ∈ V₀ N → u 1 ∈ V₀ N → √(1 - c) * ‖u (m + 1)‖ ≤ √((1 + c) * (‖u 0‖ ^ 2 + ‖u 1‖ ^ 2))) ∧
    ∀ N T L (X : RowSolution T L) (Δt c : ℝ) (M : ℕ) (u g : ℕ → Total (L2Form (cube 3)) 0 3),
      0 < Δt → c < 1 → 2 * C₀ * Δt ≤ c * meshSize (𝒯 N) → M * Δt ≤ T →
      (∀ k, k + 2 ≤ M → H.IsLeapfrogStep 0 3 (V N) (V₀ N) Δt (g (k + 2)) (u k) (u (k + 1))
        (u (k + 2))) →
      (∀ k, k + 2 ≤ M → ∃ w, IsWhitneyInterp (cube 3) (𝒯 N) 0 3 (X.u ((k + 2 : ℕ) * Δt)) w ∧
        g (k + 2) - w ∈ V₀ N) →
      IsWhitneyInterp (cube 3) (𝒯 N) 0 3 (X.u 0) (u 0) →
      IsWhitneyInterp (cube 3) (𝒯 N) 0 3 (X.u Δt) (u 1) →
      ∀ U, IsRepr (cube 3) 0 3 (X.u (M * Δt)) U →
        ‖u M - U‖ ≤ C * L * (1 + T) * (meshSize (𝒯 N) + Δt ^ 2) / (1 - c) := by
  sorry

/-- **Non-vacuity of the error bounds of `crankNicolson_cube` and `leapfrog_cube`**: for every
`T` some `RowSolution T L` (row `0` of the plane wave of [QuennevilleBelair2015], Ch. 7, in the
proof) has at every time a point of `Q` where `E(t)` and `∂ₜE(t)` are nonzero: neither zero nor
stationary. -/
theorem rowSolution_nonvacuous (T : ℝ) :
    ∃ L, ∃ X : RowSolution T L, ∀ t, ∃ y ∈ cube 3, X.u t 1 y ≠ 0 ∧ X.u₁ t 1 y ≠ 0 := by
  sorry

/-! ### Maxwell's equations, semi-discrete -/

/-- **Maxwell's equations** ([QuennevilleBelair2015], Ch. 4; [AFW2010], §4; [Monk2003]): for the
domains, meshes and admissible sequences of `fem_wave` in `ℝ³`, the vector proxies `V_N⁰`, `V_N¹`,
`V_N²` of `S_k(M_N)` (for `S = topSeq` the Lagrange, Nédélec and Raviart–Thomas elements) lie in
`H¹(Ω)`, `H(curl, Ω)`, `H(div, Ω)`, and data in `V_N⁰ × V_N¹ × V_N²` have unique semi-discrete
Galerkin solutions on `[0, T]` (continuous in time). In Hodge-wave form (the window `[0, 3)` of
`HΛ(Ω)` in vector proxies), with `H = -B`, `σ = 0`: `E' = curl H`, `H' = -curl E` with
perfect-magnetic-conductor walls `H × n = 0`, `E · n = 0`. For data in the domain of the Maxwell
operator and every `T` there is a unique strong solution on `[0, T]`; it conserves the energy,
keeps the Gauss laws `σ = 0`, `grad* E = 0`, `div B = 0`, and is the uniform limit on `[0, T]` of
every family of Galerkin solutions whose initial data converge to the data; such families
exist. -/
theorem maxwell {Ω : Set (Fin 3 → ℝ)} (hΩ : IsStarShapedBall Ω) {M : ℕ → SimplicialMesh 3}
    (hM : IsMeshFamily Ω M) (S : PolySeq) :
    let V₀ := fun N => proxy0 '' femSpace Ω (M N) S ∅ 0
    let V₁ := fun N => proxy1 '' femSpace Ω (M N) S ∅ 1
    let V₂ := fun N => proxy2 '' femSpace Ω (M N) S ∅ 2
    (∀ N, V₀ N ⊆ (grad Ω).domain ∧ V₁ N ⊆ (curl Ω).domain ∧ V₂ N ⊆ (div Ω).domain) ∧
    (∀ N T σh₀ Eh₀ Bh₀, σh₀ ∈ V₀ N → Eh₀ ∈ V₁ N → Bh₀ ∈ V₂ N →
      ∃ σh Eh Bh, σh 0 = σh₀ ∧ Eh 0 = Eh₀ ∧ Bh 0 = Bh₀ ∧
        IsMaxwellGalerkin Ω (V₀ N) (V₁ N) (V₂ N) T σh Eh Bh ∧
        ∀ σ₁ E₁ B₁, σ₁ 0 = σh₀ → E₁ 0 = Eh₀ → B₁ 0 = Bh₀ →
          IsMaxwellGalerkin Ω (V₀ N) (V₁ N) (V₂ N) T σ₁ E₁ B₁ →
          ∀ t ∈ Icc 0 T, σ₁ t = σh t ∧ E₁ t = Eh t ∧ B₁ t = Bh t) ∧
    ∀ σ₀ E₀ B₀, σ₀ ∈ (grad Ω).domain → E₀ ∈ (curl Ω).domain → E₀ ∈ (grad Ω)†.domain →
      B₀ ∈ (curl Ω)†.domain → ∀ T, ∃ σ E B, σ 0 = σ₀ ∧ E 0 = E₀ ∧ B 0 = B₀ ∧
        IsMaxwellSolution Ω T σ E B ∧
        (∀ σ₁ E₁ B₁, σ₁ 0 = σ₀ → E₁ 0 = E₀ → B₁ 0 = B₀ → IsMaxwellSolution Ω T σ₁ E₁ B₁ →
          ∀ t ∈ Icc 0 T, σ₁ t = σ t ∧ E₁ t = E t ∧ B₁ t = B t) ∧
        (∀ t ∈ Icc 0 T, ‖σ t‖ ^ 2 + ‖E t‖ ^ 2 + ‖B t‖ ^ 2 = ‖σ₀‖ ^ 2 + ‖E₀‖ ^ 2 + ‖B₀‖ ^ 2) ∧
        (σ₀ = 0 → (E₀, 0) ∈ (grad Ω)†.graph → (B₀, 0) ∈ (div Ω).graph → ∀ t ∈ Icc 0 T,
          σ t = 0 ∧ (E t, 0) ∈ (grad Ω)†.graph ∧ (B t, 0) ∈ (div Ω).graph) ∧
        (∀ (σh : ℕ → ℝ → L2Field Ω (Fin 1)) (Eh Bh : ℕ → ℝ → L2Field Ω (Fin 3)),
          (∀ N, IsMaxwellGalerkin Ω (V₀ N) (V₁ N) (V₂ N) T (σh N) (Eh N) (Bh N)) →
          Tendsto (fun N => σh N 0) atTop (𝓝 σ₀) → Tendsto (fun N => Eh N 0) atTop (𝓝 E₀) →
          Tendsto (fun N => Bh N 0) atTop (𝓝 B₀) →
          TendstoUniformlyOn σh σ atTop (Icc 0 T) ∧ TendstoUniformlyOn Eh E atTop (Icc 0 T) ∧
            TendstoUniformlyOn Bh B atTop (Icc 0 T)) ∧
        ∃ (σh : ℕ → ℝ → L2Field Ω (Fin 1)) (Eh Bh : ℕ → ℝ → L2Field Ω (Fin 3)),
          (∀ N, IsMaxwellGalerkin Ω (V₀ N) (V₁ N) (V₂ N) T (σh N) (Eh N) (Bh N)) ∧
          Tendsto (fun N => σh N 0) atTop (𝓝 σ₀) ∧ Tendsto (fun N => Eh N 0) atTop (𝓝 E₀) ∧
          Tendsto (fun N => Bh N 0) atTop (𝓝 B₀) := by
  sorry

end FEEC
