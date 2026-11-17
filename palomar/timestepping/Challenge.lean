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
# Rational time stepping on Banach spaces, with finite difference and finite element instances

A one-step method for `u' = A u` replaces the exact evolution `e^{τA}` by `r(τA)`, `r = p/q` a
rational function with real coefficients; it is **A-stable** (`IsAStable`) if `q` has no zero
and `|r| ≤ 1` on the closed left half-plane, and of **order `m`** (`HasOrder`) if
`r(z) - e^z = O(z^{m+1})` at `0`. On a Hilbert space von Neumann's inequality makes A-stable
schemes contractive; on a Banach space, e.g. for the heat equation in the maximum norm, they need
not be power bounded. Brenner and Thomée showed that they are nevertheless nearly stable and
converge at their order for smooth data, with constants depending on `r` only, hence uniformly
over every family of space discretizations with uniformly bounded semigroups. Two such families
are the instances here: finite differences for the heat equation in the maximum norm, and
Whitney finite elements for the Hodge wave equation on the Freudenthal meshes of a cube.

Mathlib has no `C₀`-semigroups: `IsC0Semigroup` is the definition and `generatorGraph` the graph
of the generator (right derivatives at `0`). For a bounded `L`, `r(τL) = p(τL) q(τL)⁻¹`
(`rationalApply`); for a generator `A` with resolvent `R = (1 - τA)⁻¹`, `r(τA) = P(R) Q(R)⁻¹`
(`rationalOfResolvent`, `resolventPoly`), `P(R) = p(τA) Rᴺ`, `N = deg q`.

**Banach spaces** ([BrennerThomee1979], Thms 1, 4, as stated in [GomilkoTomilov2024], Thm 1.1).
For every A-stable `r`, `|r(∞)| = 1` included, and every bounded strongly continuous semigroup
(`‖S(t)‖ ≤ M`) of a real or complex Banach space, `‖r(τA)ⁿ‖ ≤ M (1 + C √n)` (`stable`), and for
`r` of order `m`, `‖r(τA)ⁿ x - S(nτ) x‖ ≤ K M nτ τᵐ ‖A^{m+1} x‖` (`error`), `C`, `K` depending
on `r`, `m` only. The Hille–Yosida estimates (`hilleYosida`, [Pazy1983], §1.5) make backward
Euler power bounded also under growth `‖S(t)‖ ≤ M e^{ωt}`. For space discretizations `Lₕ` with
uniformly bounded semigroups, stability and consistency give convergence for every datum
(`converges`, [Thomee2006], Ch. 7).

**Hilbert spaces** ([VonNeumann1951]; [HairerWanner1996], §IV.11). Von Neumann's inequality
(`vonNeumann`); for m-dissipative `A`, `‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` (`contractive`).

**Finite differences in the maximum norm** ([Thomee2006], Ch. 15). The finite difference
Laplacian `fdLaplacian` satisfies the discrete maximum principle, `‖e^{tΔₕ}‖_∞ ≤ 1`, so `error`
applies with `M = 1` uniformly in `h`: on a cube every A-stable scheme of order `m`, started from
the nodal interpolant, approximates every classical solution of the heat equation whose initial
value satisfies the compatibility conditions to `O(h² + τᵐ)` in the maximum norm (`fdHeat`).

**Whitney elements for the Hodge wave equation** ([QuennevilleBelair2015], Ch. 7; [Joly2003]).
On the Freudenthal meshes of `Q = (0, ½)³` the Whitney spaces `P₁Λ⁰ × P₁⁻Λ¹ × P₁⁻Λ²` discretize
`σ' = -dᵗE`, `E' = dσ - dᵗB`, `B' = dE`; on the fields `V̊ₕ` with vanishing boundary degrees of
freedom the discrete operator `Aₕ` is skew-adjoint for the `L²` product. The implicit
Crank–Nicolson rule is `r(ΔtAₕ)` for the A-stable `r(z) = (2 + z)/(2 - z)`
(`crankNicolson_isAStable`, `|r(iy)| = 1`), the Hilbert case of `contractive`: stable for every
time step, of error `O(h + Δt²)` (`crankNicolson_cube`). The explicit leapfrog rule is a two-step
method outside the one-step class; it is stable under the CFL condition `Δt ≲ h` that the
global inverse estimate (`inverse_estimate`) makes concrete, with the same error
(`leapfrog_cube`). A plane wave meets the hypotheses of both error bounds
(`rowSolution_nonvacuous`), as backward Euler and Crank–Nicolson meet those on `r`
(`backwardEuler_isAStable`, `crankNicolson_isAStable`).

## Conventions

Points of `ℝⁿ` are `Fin n → ℝ` (Lebesgue measure, sup norm). A `k`-form is given by its
coefficients `ω_s` on `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}`, `s = {s₁ < ⋯ < s_k} ⊆ Fin n`
(`FormIdx n k`); `L²(Ω; Λᵏ)` is the `ℓ²` sum of a copy of `L²(Ω)` per coefficient (`L2Form`).
With `ε(j, s) = (-1)^{#{l ∈ s | l < j}}`, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`. The
definitions of differential forms, polynomial forms, simplicial meshes and finite element spaces
are those of the Palomar entry `palomar/fem`.

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

Bibliography: [references.bib](../../docs/references.bib)
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

/-- **The rational scheme of a bounded operator**: `r(L) = p(L) q(L)⁻¹` for `r = p/q`. -/
def rationalApply (p q : ℝ[X]) (L : E →L[𝕜] E) : E →L[𝕜] E :=
  aeval L (p.map (algebraMap ℝ 𝕜)) * Ring.inverse (aeval L (q.map (algebraMap ℝ 𝕜)))

end Operators

/-- `r = p/q` is **A-stable**: on the closed left half-plane `q` has no zero and `|r| ≤ 1`. This
is a property of the representation `p/q`; for coprime `p`, `q` it is the A-stability of `r`. -/
def IsAStable (p q : ℝ[X]) : Prop :=
  ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0 ∧ ‖aeval z p / aeval z q‖ ≤ 1

/-- `r = p/q` has **order `m`**: `r(z) - e^z = O(z^{m+1})` as `z → 0` (with `q(0) ≠ 0`, as for
A-stable `p/q`, the quotient is the rational function near `0`). -/
def HasOrder (p q : ℝ[X]) (m : ℕ) : Prop :=
  (fun z : ℂ => aeval z p / aeval z q - Complex.exp z) =O[𝓝 0] fun z => z ^ (m + 1)

/-! ### Banach spaces -/

/-- **The Hille–Yosida estimates** ([Pazy1983], §1.5). Let `S` be a strongly continuous
semigroup of a complex Banach space (real ones are covered by complexification in `Feec`, not
here) with `‖S t‖ ≤ M e^{ωt}`, generator `A`. Every `z` with
`re z > ω` is in the resolvent set of `A`: there is a bounded `R` with `R (z x - A x) = x` on
`D(A)`, `R y ∈ D(A)` with `A R y = z R y - y`, and `‖Rᵐ‖ ≤ M/(re z - ω)ᵐ` for every `m`. At
`z = 1/τ`, `ωτ < 1`, backward Euler `(1 - τA)⁻¹ = z R` is power bounded, `‖(1 - τA)⁻ᵏ‖ ≤
M/(1 - ωτ)ᵏ`, for every step: the stability hypothesis of `converges`. -/
theorem hilleYosida {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (S : ℝ → E →L[ℂ] E) (hS : IsC0Semigroup S) {M ω : ℝ}
    (hSb : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M * Real.exp (ω * t)) (z : ℂ) (hz : ω < z.re) :
    ∃ R : E →L[ℂ] E, (∀ x y : E, (x, y) ∈ generatorGraph S → R (z • x - y) = x) ∧
      (∀ y : E, (R y, z • R y - y) ∈ generatorGraph S) ∧
      ∀ m : ℕ, ‖R ^ m‖ ≤ M / (z.re - ω) ^ m := by
  sorry

/-- **Brenner–Thomée's stability bound** ([BrennerThomee1979]). For every A-stable `r = p/q`
(`|r(∞)| = 1` allowed) there is `C ≥ 0`, depending on `r` only, such that for every strongly
continuous semigroup `S` of a real or complex Banach space with `‖S t‖ ≤ M` (`t ≥ 0`), generator
`A`, and every `τ > 0`: exactly one bounded `R` satisfies `R (x - τAx) = x` on `D(A)` (the
resolvent `(1 - τA)⁻¹`), `Q(R)` is invertible, and `‖r(τA)ⁿ‖ ≤ M (1 + C √n)` for every `n`. -/
theorem stable (p q : ℝ[X]) (hr : IsAStable p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
      [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E) (M : ℝ),
      IsC0Semigroup S → (∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) → ∀ τ : ℝ, 0 < τ → ∃ R : E →L[𝕜] E,
        (∀ T : E →L[𝕜] E,
          (∀ x y : E, (x, y) ∈ generatorGraph S → T (x - (τ : 𝕜) • y) = x) ↔ T = R) ∧
        IsUnit (resolventPoly q.natDegree q R) ∧
        ∀ n : ℕ, ‖rationalOfResolvent p q R ^ n‖ ≤ M * (1 + C * √n) := by
  sorry

/-- **Brenner–Thomée's smooth-data error estimate** ([BrennerThomee1979]; [GomilkoTomilov2024],
Thm 1.1(ii), `s = m + 1`, optimal in general). For every A-stable `r = p/q` of order `m`
(`|r(∞)| = 1` allowed) there is `K`, depending on `r` and `m` only, such that for every strongly
continuous semigroup `S` of a real or complex Banach space with `‖S t‖ ≤ M` (`t ≥ 0`), generator
`A`, every `τ > 0` and the resolvent `R` (as in `stable`),
`‖r(τA)ⁿ x - S(nτ) x‖ ≤ K M nτ τᵐ ‖A^{m+1} x‖` for every `n` and `x ∈ D(A^{m+1})` (a chain
`u 0 = x, …, u (m + 1) = A^{m+1} x` in the graph of `A`): order `m` at fixed `T = nτ`, without
the `√n` of the stability bound. -/
theorem error (p q : ℝ[X]) (hr : IsAStable p q) {m : ℕ} (hm : HasOrder p q m) :
    ∃ K : ℝ, ∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
      [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E) (M : ℝ),
      IsC0Semigroup S → (∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) → ∀ τ : ℝ, 0 < τ → ∀ R : E →L[𝕜] E,
        (∀ x y : E, (x, y) ∈ generatorGraph S → R (x - (τ : 𝕜) • y) = x) →
        ∀ (n : ℕ) (u : ℕ → E), (∀ j < m + 1, (u j, u (j + 1)) ∈ generatorGraph S) →
          ‖(rationalOfResolvent p q R ^ n) (u 0) - S (n * τ) (u 0)‖ ≤
            K * M * (n * τ) * τ ^ m * ‖u (m + 1)‖ := by
  sorry

/-- **Stability and consistency give convergence** (the sufficiency half of the Lax equivalence
theorem, for the time discretization; [Thomee2006], Ch. 7, 9; [Pazy1983], §3.4). Let `S` be a
strongly continuous semigroup of a Banach space `E` over `𝕜 = ℝ` or `ℂ` with `‖S t‖ ≤ M`, and
let Banach spaces `Xₕ` (`h : κ`, refined along a filter `l`) carry bounded generators `Lₕ` with
`‖e^{tLₕ}‖ ≤ M` for `t ≥ 0`, uniformly in `h`, read in `E` by `ιₕ` with left inverses `πₕ`
(`πₕ ιₕ = 1`), `‖ιₕ‖, ‖πₕ‖ ≤ C`. Let `Pₕ` be a time scheme with steps `τₕ > 0`, `τₕ → 0`,
power bounded (`‖Pₕⁿ‖ ≤ Mₛ(T)` for `nτₕ ≤ T`) and consistent of order `p ≥ 1`
(`‖Pₕ y - e^{τₕLₕ} y‖ ≤ K τₕ^{p+1} ‖Lₕ^{p+1} y‖`). If the semidiscrete solutions
`ιₕ e^{tLₕ} vₕ` converge to `S(t) x` uniformly on every `[0, T]`, then the fully discrete
solutions `ιₕ Pₕⁿ vₕ` converge to `S(nτₕ) x` uniformly over the time levels `nτₕ ∈ [0, T]`: no
smoothness of `x` or `vₕ` is assumed. (`S` enters the conclusion only through
`S(nτₕ) x`, the limit of the semidiscrete solutions.) -/
theorem converges {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E)
    (hS : IsC0Semigroup S) {κ : Type*} (l : Filter κ) (X : κ → Type*)
    [∀ h, NormedAddCommGroup (X h)] [∀ h, NormedSpace 𝕜 (X h)] [∀ h, CompleteSpace (X h)]
    [∀ h, NormedSpace ℝ (X h)] [∀ h, IsScalarTower ℝ 𝕜 (X h)] (L : ∀ h, X h →L[𝕜] X h) (M : ℝ)
    (hL : ∀ h (t : ℝ), 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L h)‖ ≤ M)
    (hSM : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) (ι : ∀ h, X h →L[𝕜] E) (π : ∀ h, E →L[𝕜] X h)
    (hπι : ∀ h x, π h (ι h x) = x) (hC : ∃ C, ∀ h, ‖ι h‖ ≤ C ∧ ‖π h‖ ≤ C) (τ : κ → ℝ)
    (hτ : ∀ h, 0 < τ h) (hτ0 : Tendsto τ l (𝓝 0)) (P : ∀ h, X h →L[𝕜] X h) (Ms : ℝ → ℝ)
    (hP : ∀ (T : ℝ) (h : κ) (n : ℕ), n * τ h ≤ T → ‖P h ^ n‖ ≤ Ms T) {p : ℕ} (hp : 0 < p)
    {K : ℝ} (hK : 0 ≤ K) (hcons : ∀ h (y : X h), ‖P h y - NormedSpace.exp ((τ h : 𝕜) • L h) y‖ ≤
      K * τ h ^ (p + 1) * ‖(L h ^ (p + 1)) y‖) (x : E) (v : ∀ h, X h)
    (hsd : ∀ T : ℝ, TendstoUniformlyOn
      (fun h (t : ℝ) => ι h (NormedSpace.exp ((t : 𝕜) • L h) (v h))) (fun t => S t x) l (Icc 0 T))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in l, ∀ n : ℕ, n * τ h ∈ Icc 0 T → ‖S (n * τ h) x - ι h ((P h ^ n) (v h))‖ < ε := by
  sorry

/-! ### Hilbert spaces -/

/-- **Von Neumann's inequality** ([VonNeumann1951]), for rational functions. For a contraction
`T` of a complex Hilbert space and complex polynomials `p`, `q` with `q` free of zeros in the
closed unit disc, `q(T)` is invertible and `‖p(T) q(T)⁻¹‖ ≤ sup_{|ζ| = 1} |p(ζ)/q(ζ)|` (for
`q = 1`, `‖p(T)‖ ≤ sup_{|ζ| = 1} |p(ζ)|`). -/
theorem vonNeumann {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {T : E →L[ℂ] E} (hT : ‖T‖ ≤ 1) (p q : ℂ[X])
    (hq : ∀ z : ℂ, ‖z‖ ≤ 1 → q.eval z ≠ 0) :
    IsUnit (aeval T q) ∧
      ‖aeval T p * Ring.inverse (aeval T q)‖ₑ ≤
        ⨆ ζ ∈ Metric.sphere (0 : ℂ) 1, ‖p.eval ζ / q.eval ζ‖ₑ := by
  sorry

/-- **Rational schemes for m-dissipative operators: von Neumann's theorem** ([HairerWanner1996],
§IV.11; [Pazy1983], §1.4). Let `A` be a possibly unbounded operator of a real or complex Hilbert
space, dissipative (`re ⟪A x, x⟫ ≤ 0` on its domain) with `μ - A` onto for some `μ > 0`
(m-dissipative), `r = p/q` a real rational function with `q` free of zeros in the closed left
half-plane, and `τ > 0`. Exactly one bounded `R` satisfies `R (x - τAx) = x` on `D(A)` (the
resolvent `(1 - τA)⁻¹`), `Q(R)` is invertible, and `‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` for every `n`
(suprema in `[0, ∞]`; infinite when `deg p > deg q`). For A-stable `r` this is `≤ 1`:
A-stable schemes are contractive. -/
theorem contractive {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] {A : E →ₗ.[𝕜] E} (hA : ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ 0)
    (hA' : ∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : 𝕜) • (x : E) - A x = y)
    (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0) {τ : ℝ} (hτ : 0 < τ) :
    ∃ R : E →L[𝕜] E,
      (∀ T : E →L[𝕜] E, (∀ x : A.domain, T ((x : E) - (τ : 𝕜) • A x) = x) ↔ T = R) ∧
      IsUnit (resolventPoly q.natDegree q R) ∧ ∀ n : ℕ, ‖rationalOfResolvent p q R ^ n‖ₑ ≤
        (⨆ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ₑ) ^ n := by
  sorry

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

/-- The partial derivative `∂ᵢ f (x)` of `f : ℝⁿ → ℝ`: the Fréchet derivative in the direction
`eᵢ` (`0` where `f` is not differentiable). -/
def partialDeriv {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- **The heat equation in the maximum norm by finite differences** ([Thomee2006], Ch. 15;
[BrennerThomee1979]). For every A-stable `r = p/q` of order `m` there is `K`, depending on `r`
and `m` only, such that: let `u` be a classical solution of `uₜ = Δu` on the cube
`Q = b + (0, s)ⁿ` for `t ∈ [0, T]` (`u(t)` of class `C⁴` on `ℝⁿ`, with two-sided time
derivative `u₁ = Δu` at the points of `Q` and of `[0, T]`), vanishing on `∂Q`, with pure fourth
derivatives `|∂ᵢ⁴ u(t)| ≤ B` on `Q̄`, whose initial value satisfies the **compatibility
conditions of order `m`**: `u(0)` is on `Q̄` a function `ũ` of class `C^{2m+2}` on `ℝⁿ` that is
odd under the reflections in the faces of `Q` (`xᵢ ↦ 2bᵢ - xᵢ`, `xᵢ ↦ 2(bᵢ + s) - xᵢ`: `ũ` is
the odd `2s`-periodic extension of `u(0)`; for `n = 1`, `u(0) ∈ C^{2m+2}(Q̄)` with
`∂^{2j} u(0) = 0` at both ends for `j ≤ m + 1`), with
`|∂²_{i₁} ⋯ ∂²_{i_{m+1}} ũ| ≤ B'` for all `i₁, …, i_{m+1}`. On the grid of the `Nⁿ` interior
nodes `b + h q`, `q ∈ {1, …, N}ⁿ` (`gridNodes`), `h = s/(N + 1)`, with the nodal interpolant
`Iₕ` (`gridInterp`) and the finite difference Laplacian `Δₕ`, the scheme started from
`Iₕ u(0)` satisfies, for every `τ > 0` and `kτ ≤ T`,
`‖Iₕ u(kτ) - r(τΔₕ)ᵏ Iₕ u(0)‖_∞ ≤ kτ (n B h²/12 + K nᵐ⁺¹ B' τᵐ)`: `O(h² + τᵐ)` with `K`
independent of `h`, `τ`, the dimension and `u`. -/
theorem fdHeat (p q : ℝ[X]) (hr : IsAStable p q) {m : ℕ} (hm : HasOrder p q m) :
    ∃ K : ℝ, ∀ (n : ℕ) (b : Fin n → ℝ) (s T B B' : ℝ) (u u₁ : ℝ → (Fin n → ℝ) → ℝ)
      (ũ : (Fin n → ℝ) → ℝ), 0 < s →
      (∀ t ∈ Icc 0 T, ContDiff ℝ 4 (u t)) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Ioo (b i) (b i + s),
        HasDerivAt (fun t => u t x) (u₁ t x) t ∧
          u₁ t x = ∑ i, partialDeriv i (partialDeriv i (u t)) x) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Icc (b i) (b i + s),
        x ∉ univ.pi (fun i => Ioo (b i) (b i + s)) → u t x = 0) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Icc (b i) (b i + s), ∀ i,
        |(partialDeriv i)^[4] (u t) x| ≤ B) →
      ContDiff ℝ (2 * m + 2) ũ → (∀ x ∈ univ.pi fun i => Icc (b i) (b i + s), ũ x = u 0 x) →
      (∀ i x, ũ (Function.update x i (2 * b i - x i)) = -ũ x ∧
        ũ (Function.update x i (2 * (b i + s) - x i)) = -ũ x) →
      (∀ (l : Fin (m + 1) → Fin n) x,
        |(List.ofFn l).foldr (fun i f => partialDeriv i (partialDeriv i f)) ũ x| ≤ B') →
      ∀ (N : ℕ) (τ : ℝ), 0 < τ → ∀ k : ℕ, k * τ ≤ T →
        ‖gridInterp b (s / (N + 1 : ℕ)) N (u (k * τ)) -
            (rationalApply p q (τ • fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ))) ^ k)
              (gridInterp b (s / (N + 1 : ℕ)) N (u 0))‖ ≤
          k * τ * (n * B * (s / (N + 1 : ℕ)) ^ 2 / 12 + K * n ^ (m + 1) * B' * τ ^ m) := by
  sorry

/-! ### The hypotheses on `r` are met -/

/-- **Backward Euler** `r(z) = 1/(1 - z)` is A-stable of order `1`. -/
theorem backwardEuler_isAStable : IsAStable 1 (1 - X) ∧ HasOrder 1 (1 - X) 1 := by
  sorry

/-- **Crank–Nicolson** `r(z) = (2 + z)/(2 - z)` is A-stable (with `|r(∞)| = 1`) of order `2`. -/
theorem crankNicolson_isAStable : IsAStable (2 + X) (2 - X) ∧ HasOrder (2 + X) (2 - X) 2 := by
  sorry

section FiniteElements

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

/-- The **exterior derivative** of a form field, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`. -/
def extDeriv (w : FormField n) : FormField n :=
  fun x s => ∑ j ∈ s, sgn j s * partialDeriv j (fun y => w y (s.erase j)) x

/-- The **formal adjoint** of `d`, the codifferential `δ`,
`(dᵗψ)_s = -Σ_{j ∉ s} ε(j, s) ∂_j ψ_{s ∪ j}`: `∫ ⟨dφ, ψ⟩ = ∫ ⟨φ, dᵗψ⟩` for test forms. -/
def codiff (ψ : FormField n) : FormField n :=
  fun x s => -∑ j ∈ sᶜ, sgn j s * partialDeriv j (fun y => ψ y (insert j s)) x

open scoped ContDiff in
/-- `f` is a **test function** on `Ω`: smooth, with compact support contained in `Ω`. -/
def IsTestFn (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω

/-- The graph `{(ψ, dᵗψ)}` of the formal adjoint on the test `(k + 1)`-forms, as a subspace of
`L²(Ω; Λᵏ⁺¹) × L²(Ω; Λᵏ)`. -/
def codiffGraph (Ω : Set (Fin n → ℝ)) (k : ℤ) : Submodule ℝ (L2Form Ω (k + 1) × L2Form Ω k) :=
  Submodule.span ℝ {p | ∃ ψ : FormField n, (∀ s, IsTestFn Ω fun x => ψ x s) ∧
    (∀ t : FormIdx n (k + 1), ⇑(p.1 t) =ᵐ[volume.restrict Ω] fun x => ψ x t.1) ∧
    ∀ s : FormIdx n k, ⇑(p.2 s) =ᵐ[volume.restrict Ω] fun x => codiff ψ x s.1}

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

/-- **The global inverse estimate** ([Ciarlet2002], §3.2; [BrennerScott2008], §4.5): for a
shape-regular, quasi-uniform family of meshes `M_N` of an open `Ω` whose open simplices lie in `Ω`,
every admissible sequence `S` and every form degree `k`, there is `C` such that every `v` of the
finite element space `S_k(M_N)` lies in `HΛᵏ(Ω)` and `h_N ‖dv‖_{L²} ≤ C ‖v‖_{L²}`, `C`
independent of `N`. (A mesh of `Ω` covers `cl Ω`; that its open simplices lie in `Ω`, true when
`Ω` is the interior of its closure, e.g. for convex or Lipschitz `Ω`, makes `‖v‖²_{L²(Ω)}` the sum
of the norms of `v` on the whole simplices.) On the Whitney spaces it bounds the discrete wave
operator, `‖Aₕ‖ ≤ 2C/h_N`, the CFL constant of `leapfrog_cube`. -/
theorem inverse_estimate [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M)
    (hint : ∀ N, ∀ T ∈ (M N).simplices, interior T.closedInterior ⊆ Ω) (S : PolySeq) (k : ℕ) :
    ∃ C, ∀ N, ∀ v ∈ femSpace Ω (M N) S k, ∃ hv : v ∈ (dMax Ω k).domain,
      meshSize (M N) * ‖dMax Ω k ⟨v, hv⟩‖ ≤ C * ‖v‖ := by
  sorry

/-- **`O(h + Δt²)` convergence of the Crank–Nicolson Whitney scheme with Dirichlet degrees of
freedom** ([QuennevilleBelair2015], Ch. 7; [Arnold2018], Ch. 7; [Monk2003]; [Thomee2006]). The
cube `Q = (0, ½)³` carries a shape-regular, quasi-uniform family of Freudenthal meshes `𝒯_N`,
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
  `‖u_M - U(t_M)‖_{L²} ≤ C L (1 + T) (h_N + Δt²)`, `C` independent of `N`, `Δt`, `T`, `L`, `U`.

With vanishing boundary data a step is `u' = r(ΔtAₕ) u` on `V̊ₕ`, `r(z) = (2 + z)/(2 - z)`, `Aₕ`
skew-adjoint: the setting of `contractive`, `‖r(ΔtAₕ)ⁿ‖ ≤ 1`, which is the stability behind the
error bound. -/
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
        rowNorm (u M - U) ≤ C * L * (1 + T) * (meshSize (𝒯 N) + Δt ^ 2) := by
  sorry

/-- **The explicit leapfrog Whitney scheme under a CFL condition** ([Joly2003];
[QuennevilleBelair2015], Ch. 7). On the shape-regular, quasi-uniform Freudenthal meshes `𝒯_N` of
the cube `Q = (0, ½)³`, `h_N → 0`, with the Whitney row `Vₕ = P₁Λ⁰ × P₁⁻Λ¹ × P₁⁻Λ²` of
`crankNicolson_cube`:

* (**the inverse estimate**) some `C₀` has `h_N ‖𝐝ₕ v‖ ≤ C₀ ‖v‖` for every `v ∈ Vₕ` and every `N`,
  `𝐝(σ, E, B) = (0, dσ, dE)` (`inverse_estimate`), so `‖Aₕ‖ ≤ 2 C₀ / h_N` and
  `2 C₀ Δt ≤ c h_N` is a CFL condition `Δt ‖Aₕ‖ ≤ c`;
* (**explicit**) for every time step `Δt` and all rows `g, u, u'` of `Vₕ` the leapfrog step has
  exactly one solution;

and there is `C` such that for **every** constant `C₀ ≥ 0` of the inverse estimate (so the CFL
condition is that of any computed `C₀`, the existence of one having no explicit value):

* (**stability**) under the CFL condition with `c < 1`, leapfrog iterates with vanishing boundary
  degrees of freedom from `u₀, u₁ ∈ V̊ₕ` satisfy `√(1 - c) ‖u_{m+1}‖ ≤ √((1 + c)(‖u₀‖² + ‖u₁‖²))`
  for every `m`;
* (**the error**) under the CFL condition with `c < 1`, for every smooth solution `U` of the Hodge
  wave equation on `[0, T] × cl Q` with bound `L` (`RowSolution`), `Δt > 0` and `M Δt ≤ T`, the
  iterates started from `u₀ = Π_h U(0)`, `u₁ = Π_h U(Δt)` (the second starting value from the
  exact solution; no one-step starting procedure is analysed) with the boundary degrees of
  freedom of `Π_h U(tₙ)` satisfy `‖u_M - U(t_M)‖_{L²} ≤ C L (1 + T) (h_N + Δt²) / (1 - c)`, `C`
  independent of `C₀`, `N`, `Δt`, `c`, `T`, `L`, `U`. -/
theorem leapfrog_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3) (C : ℝ), IsMeshFamily (cube 3) 𝒯 ∧
    IsFreudenthal 𝒯 ∧
    (∃ C₀, ∀ N v, RowMem (𝒯 N) false v →
      meshSize (𝒯 N) * √(‖wd 0 v.1‖ ^ 2 + ‖wd 1 v.2.1‖ ^ 2) ≤ C₀ * rowNorm v) ∧
    (∀ N Δt g u u', RowMem (𝒯 N) false g → RowMem (𝒯 N) false u → RowMem (𝒯 N) false u' →
      ∃! u'', IsLeapfrogStep (𝒯 N) Δt g u u' u'') ∧
    ∀ C₀, 0 ≤ C₀ → (∀ N v, RowMem (𝒯 N) false v →
      meshSize (𝒯 N) * √(‖wd 0 v.1‖ ^ 2 + ‖wd 1 v.2.1‖ ^ 2) ≤ C₀ * rowNorm v) →
    (∀ N Δt c (u : ℕ → Row) m, 0 ≤ Δt → c < 1 → 2 * C₀ * Δt ≤ c * meshSize (𝒯 N) →
      (∀ k < m, IsLeapfrogStep (𝒯 N) Δt 0 (u k) (u (k + 1)) (u (k + 2))) →
      RowMem (𝒯 N) true (u 0) → RowMem (𝒯 N) true (u 1) →
      √(1 - c) * rowNorm (u (m + 1)) ≤ √((1 + c) * (rowNorm (u 0) ^ 2 + rowNorm (u 1) ^ 2))) ∧
    ∀ N T L (X : RowSolution T L) (Δt c : ℝ) (M : ℕ) (u g : ℕ → Row), 0 < Δt → c < 1 →
      2 * C₀ * Δt ≤ c * meshSize (𝒯 N) → M * Δt ≤ T →
      (∀ m, m + 2 ≤ M → IsLeapfrogStep (𝒯 N) Δt (g (m + 2)) (u m) (u (m + 1)) (u (m + 2))) →
      (∀ m, m + 2 ≤ M → ∃ w, IsRowInterp (𝒯 N) (X.u ((m + 2 : ℕ) * Δt)) w ∧
        RowMem (𝒯 N) true (g (m + 2) - w)) →
      IsRowInterp (𝒯 N) (X.u 0) (u 0) → IsRowInterp (𝒯 N) (X.u Δt) (u 1) →
      ∀ U : Row, IsRepr (cube 3) 0 (X.u (M * Δt) 0) U.1 →
        IsRepr (cube 3) 1 (X.u (M * Δt) 1) U.2.1 → IsRepr (cube 3) 2 (X.u (M * Δt) 2) U.2.2 →
        rowNorm (u M - U) ≤ C * L * (1 + T) * (meshSize (𝒯 N) + Δt ^ 2) / (1 - c) := by
  sorry

/-- **Non-vacuity of the error bounds of `crankNicolson_cube` and `leapfrog_cube`**: for every
`T` the smooth solutions they quantify over include genuine waves: some `RowSolution T L` (in the
proof, row `0` of the plane wave of [QuennevilleBelair2015], Ch. 7) has at every time `t` a point
of `Q` where the electric field `E(t)` and its time derivative `∂ₜE(t)` are nonzero (so `U` is
neither zero nor stationary). -/
theorem rowSolution_nonvacuous (T : ℝ) :
    ∃ L, ∃ X : RowSolution T L, ∀ t, ∃ y ∈ cube 3, X.u t 1 y ≠ 0 ∧ X.u₁ t 1 y ≠ 0 := by
  sorry

end FiniteElements

end TimeStepping
