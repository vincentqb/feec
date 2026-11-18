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
# A-stable rational time stepping for `C₀`-semigroups

A one-step method for `u' = A u`, `A` the generator of a strongly continuous semigroup `S`,
replaces the evolution `S(τ) = e^{τA}` over a time step `τ` by `r(τA)`, `r = p/q` a rational
function with real coefficients: **A-stable** (`IsAStable`) if `q` has no zero and `|r| ≤ 1` on
the closed left half-plane, of **order `m`** (`HasOrder`) if `r(z) - e^z = O(z^{m+1})` at `0`.
Backward Euler `1/(1 - z)` (order `1`) and Crank–Nicolson `(2 + z)/(2 - z)` (order `2`,
`|r(∞)| = 1`) are such schemes (`backwardEuler_isAStable`, `crankNicolson_isAStable`).

**The question.** How do the powers `r(τA)ⁿ` of an A-stable scheme behave, with constants that
depend on `r` alone (hence uniformly over every family of space discretizations with uniformly
bounded semigroups), and when is the Banach-space theory needed?

**The answer.**

* **Banach spaces: Brenner–Thomée** ([BrennerThomee1979], Thms 1, 4, as stated in
  [GomilkoTomilov2024], Thm 1.1). For every A-stable `r` (`|r(∞)| = 1` included) and every
  bounded strongly continuous semigroup (`‖S(t)‖ ≤ M`) of a real or complex Banach space,
  `‖r(τA)ⁿ‖ ≤ M (1 + C √n)` (`stable`), and for `r` of order `m` the error for smooth data has
  the order of the scheme, without the `√n`: `‖r(τA)ⁿ x - S(nτ) x‖ ≤ K M nτ τᵐ ‖A^{m+1} x‖`
  (`error`); both bounds are optimal in general ([GomilkoTomilov2024]). `C` and `K` depend on `r`
  and `m` only: the second clauses state both bounds for bounded generators `L` with
  `‖e^{tL}‖ ≤ M`, uniformly in `L`, the error also along trajectories with a consistency defect.
  Backward Euler is power bounded for bounded semigroups of every Banach space (`backwardEuler`).
* **Hilbert spaces: von Neumann** ([HairerWanner1996], §IV.11). For an m-dissipative `A` (the
  generator of a contraction semigroup) every A-stable scheme is a contraction (`contractive`):
  no `√n`.
* **Convergence for every datum: Lax** ([Thomee2006], Ch. 7). For a family of space
  discretizations whose semidiscrete solutions converge, power-bounded consistent schemes converge
  for every datum, without smoothness: backward Euler on Banach spaces, and every A-stable scheme
  of order `m ≥ 1` of contraction semigroups on Hilbert spaces (`converges`). The schemes that are
  only `√n`-stable converge at their order for smooth data (`error`).
* **Where the Banach theory is needed: the heat equation in the maximum norm**
  ([CiarletRaviart1973]; [Thomee2006], Ch. 15). The maximum norm is not a Hilbert norm. A
  sub-Markov generator generates positive contractions of it (`subMarkov`), so `M = 1`; the
  lumped-mass `P₁` Laplacian of every non-obtuse simplicial mesh, in every dimension, is one (the
  discrete maximum principle), and every A-stable scheme for it is `(1 + C √k)`-stable in the
  maximum norm, with error bounds whose constants do not depend on the mesh (`maxNormHeat`). The
  witness (`fdHeat`): finite differences on a cube are the lumped-mass method of a non-obtuse
  mesh, and from initial data satisfying the compatibility conditions every A-stable scheme of
  order `m` has maximum-norm error `O(h² + τᵐ)`, uniformly in `h`.

Two classical inputs are stated as well: the Hille–Yosida estimates (`hilleYosida`,
[Pazy1983], §1.5), whose resolvent `(1 - τA)⁻¹` defines `r(τA)` and is backward Euler, and von
Neumann's inequality (`vonNeumann`, [VonNeumann1951]), behind `contractive`.

Mathlib has no `C₀`-semigroups: `IsC0Semigroup` is the definition and `generatorGraph` the graph
of the generator (right derivatives at `0`). For a bounded `L`, `r(τL) = p(τL) q(τL)⁻¹`
(`rationalApply`); for a generator `A` with resolvent `R = (1 - τA)⁻¹`, `r(τA) = P(R) Q(R)⁻¹`
(`rationalOfResolvent`, `resolventPoly`), `P(R) = p(τA) Rᴺ`, `N = deg q`.

## Conventions

Points of `ℝⁿ` are `Fin n → ℝ` (Lebesgue measure, sup norm), `eᵢ = Pi.single i 1`, and
`D^k f(x)(v₁, …, v_k)` is the `k`-th derivative `iteratedFDeriv ℝ k f x`; functions `ι → ℝ` on a
finite set of nodes carry the maximum norm. The simplicial meshes are stated in the words of the
Palomar entry `palomar/fem`; only `SimplicialMesh` is used here (no shape regularity or mesh
family).

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
* [M. Crouzeix, S. Larsson, S. Piskarev, V. Thomée, *The stability of rational approximations of analytic semigroups*][CrouzeixLarssonPiskarevThomee1993]
* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]

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

/-- **Brenner–Thomée's stability bound** ([BrennerThomee1979]), the headline on Banach spaces.
For every A-stable `r = p/q` (`|r(∞)| = 1` allowed) there is `C ≥ 0`, depending on `r` only,
such that:

* for every strongly continuous semigroup `S` of a real or complex Banach space with
  `‖S t‖ ≤ M` (`t ≥ 0`), generator `A`, and every `τ > 0`: exactly one bounded `R` satisfies
  `R (x - τAx) = x` on `D(A)` (the resolvent `(1 - τA)⁻¹`), `Q(R)` is invertible, and
  `‖r(τA)ⁿ‖ ≤ M (1 + C √n)` for every `n`;
* (**bounded generators**, the case `S(t) = e^{tL}`, with `r(τL) = p(τL) q(τL)⁻¹`) for every
  bounded operator `L` of a real or complex Banach space with `‖e^{tL}‖ ≤ M` (`t ≥ 0`) and every
  `τ > 0`, `q(τL)` is invertible and `‖r(τL)ⁿ‖ ≤ M (1 + C √n)` for every `n`: for a family of
  space discretizations `Lₕ` with `‖e^{tLₕ}‖ ≤ M` the bound is uniform in `h`. -/
theorem stable (p q : ℝ[X]) (hr : IsAStable p q) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
        [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E) (M : ℝ),
        IsC0Semigroup S → (∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) → ∀ τ : ℝ, 0 < τ → ∃ R : E →L[𝕜] E,
          (∀ T : E →L[𝕜] E,
            (∀ x y : E, (x, y) ∈ generatorGraph S → T (x - (τ : 𝕜) • y) = x) ↔ T = R) ∧
          IsUnit (resolventPoly q.natDegree q R) ∧
          ∀ n : ℕ, ‖rationalOfResolvent p q R ^ n‖ ≤ M * (1 + C * √n)) ∧
      ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
        (L : X →L[𝕜] X) (M : ℝ), (∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L)‖ ≤ M) →
        ∀ τ : ℝ, 0 < τ → IsUnit (aeval ((τ : 𝕜) • L) (q.map (algebraMap ℝ 𝕜))) ∧
          ∀ n : ℕ, ‖rationalApply p q ((τ : 𝕜) • L) ^ n‖ ≤ M * (1 + C * √n) := by
  sorry

/-- **Brenner–Thomée's smooth-data error estimate** ([BrennerThomee1979]; [GomilkoTomilov2024],
Thm 1.1(ii), `s = m + 1`, optimal in general). For every A-stable `r = p/q` of order `m`
(`|r(∞)| = 1` allowed) there is `K`, depending on `r` and `m` only, such that:

* for every strongly continuous semigroup `S` of a real or complex Banach space with `‖S t‖ ≤ M`
  (`t ≥ 0`), generator `A`, every `τ > 0` and the resolvent `R` (as in `stable`),
  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ K M nτ τᵐ ‖A^{m+1} x‖` for every `n` and `x ∈ D(A^{m+1})` (a chain
  `u 0 = x, …, u (m + 1) = A^{m+1} x` in the graph of `A`): order `m` at fixed `T = nτ`, without
  the `√n` of the stability bound;
* (**bounded generators**, the case `S(t) = e^{tL}`, and along trajectories) for every bounded
  operator `L` of a real or complex Banach space with `‖e^{tL}‖ ≤ M` (`t ≥ 0`), every `τ > 0`,
  `n` and `v`: `‖r(τL)ⁿ v - e^{nτL} v‖ ≤ K M nτ τᵐ ‖L^{m+1} v‖`, and for every curve `U` (a
  trajectory, e.g. the interpolant of an exact solution) with derivative `U'` at every point of
  `[0, nτ]` (two-sided, so `U` is defined around the endpoints) and defect `‖U' - L U‖ ≤ D`
  there, `‖U(nτ) - r(τL)ⁿ v‖ ≤ M ‖U(0) - v‖ + M nτ D + K M nτ τᵐ ‖L^{m+1} v‖`. For a family
  `Lₕ` the constants are uniform in `h`; the temporal term is that of the discrete datum `v`,
  bounded uniformly in `h` only when `‖Lₕ^{m+1} v‖` is (as for the compatible data of
  `fdHeat`). -/
theorem error (p q : ℝ[X]) (hr : IsAStable p q) {m : ℕ} (hm : HasOrder p q m) :
    ∃ K : ℝ,
      (∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
        [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E) (M : ℝ),
        IsC0Semigroup S → (∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) → ∀ τ : ℝ, 0 < τ → ∀ R : E →L[𝕜] E,
          (∀ x y : E, (x, y) ∈ generatorGraph S → R (x - (τ : 𝕜) • y) = x) →
          ∀ (n : ℕ) (u : ℕ → E), (∀ j < m + 1, (u j, u (j + 1)) ∈ generatorGraph S) →
            ‖(rationalOfResolvent p q R ^ n) (u 0) - S (n * τ) (u 0)‖ ≤
              K * M * (n * τ) * τ ^ m * ‖u (m + 1)‖) ∧
      ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
        [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] (L : X →L[𝕜] X) (M : ℝ),
        (∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L)‖ ≤ M) → ∀ τ : ℝ, 0 < τ →
        ∀ (n : ℕ) (v : X),
          ‖(rationalApply p q ((τ : 𝕜) • L) ^ n) v -
              NormedSpace.exp (((n * τ : ℝ) : 𝕜) • L) v‖ ≤
            K * M * (n * τ) * τ ^ m * ‖(L ^ (m + 1)) v‖ ∧
          ∀ (U U' : ℝ → X) (D : ℝ), (∀ s ∈ Icc 0 (n * τ), HasDerivAt U (U' s) s) →
            (∀ s ∈ Icc 0 (n * τ), ‖U' s - L (U s)‖ ≤ D) →
            ‖U (n * τ) - (rationalApply p q ((τ : 𝕜) • L) ^ n) v‖ ≤
              M * ‖U 0 - v‖ + M * (n * τ) * D + K * M * (n * τ) * τ ^ m * ‖(L ^ (m + 1)) v‖ := by
  sorry

/-- **Backward Euler is stable on every Banach space, power bounded for bounded semigroups**
([Pazy1983], §1.5; [BrennerThomee1979]): the A-stable scheme `r(z) = 1/(1 - z)` without the `√n`
of `stable`, under growth. Let `S` be a strongly continuous semigroup of a real or complex Banach
space with `‖S t‖ ≤ M e^{ωt}` (`ω ≥ 0`), generator `A`, and `τ > 0` with `ωτ < 1`. Exactly one
bounded `R` satisfies `R (x - τAx) = x` on `D(A)` (the resolvent `(1 - τA)⁻¹`, so `r(τA) = R`);
`‖Rᵏ‖ ≤ M/(1 - ωτ)ᵏ` (Hille–Yosida: power bounded for `ω = 0`, stable on bounded time intervals
for `ω > 0`), and for every `n` and `x ∈ D(A²)` (a chain `u 0 = x, u 1 = A x, u 2 = A² x` in the
graph of `A`), the first-order error
`‖Rⁿ x - S(nτ) x‖ ≤ (M/(1 - ωτ)ⁿ) (M/(1 - ωτ) + M e^{ωnτ}/2) M e^{ωnτ} nτ τ ‖A² x‖`. -/
theorem backwardEuler {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E)
    (hS : IsC0Semigroup S) {M ω : ℝ} (hω : 0 ≤ ω)
    (hSb : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M * Real.exp (ω * t)) {τ : ℝ} (hτ : 0 < τ)
    (hωτ : ω * τ < 1) :
    ∃ R : E →L[𝕜] E,
      (∀ T : E →L[𝕜] E,
        (∀ x y : E, (x, y) ∈ generatorGraph S → T (x - (τ : 𝕜) • y) = x) ↔ T = R) ∧
      (∀ k : ℕ, ‖R ^ k‖ ≤ M / (1 - ω * τ) ^ k) ∧
      ∀ (n : ℕ) (u : ℕ → E), (∀ j < 2, (u j, u (j + 1)) ∈ generatorGraph S) →
        ‖(R ^ n) (u 0) - S (n * τ) (u 0)‖ ≤ M / (1 - ω * τ) ^ n *
          (M / (1 - ω * τ) + M * Real.exp (ω * (n * τ)) / 2) * (M * Real.exp (ω * (n * τ))) *
            (n * τ) * τ * ‖u 2‖ := by
  sorry

/-! ### Hilbert spaces: von Neumann -/

/-- **Rational schemes for m-dissipative operators: von Neumann's theorem** ([HairerWanner1996],
§IV.11; [Pazy1983], §1.4), the Hilbert-space counterpart of `stable` for contraction semigroups
(`M = 1`). Let `A` be a possibly unbounded operator of a real or complex Hilbert space,
dissipative (`re ⟪A x, x⟫ ≤ 0` on its domain) with `μ - A` onto for some `μ > 0`
(m-dissipative), `r = p/q` a real rational function with `q` free of zeros in the closed left
half-plane, and `τ > 0`. Exactly one bounded `R` satisfies `R (x - τAx) = x` on `D(A)` (the
resolvent `(1 - τA)⁻¹`), `Q(R)` is invertible, and `‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` for every `n`
(suprema in `[0, ∞]`; infinite when `deg p > deg q`). For A-stable `r` this is `≤ 1`: A-stable
schemes are contractive. -/
theorem contractive {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] {A : E →ₗ.[𝕜] E} (hA : ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ 0)
    (hA' : ∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : 𝕜) • (x : E) - A x = y)
    (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0) {τ : ℝ} (hτ : 0 < τ) :
    ∃ R : E →L[𝕜] E,
      (∀ T : E →L[𝕜] E, (∀ x : A.domain, T ((x : E) - (τ : 𝕜) • A x) = x) ↔ T = R) ∧
      IsUnit (resolventPoly q.natDegree q R) ∧ ∀ n : ℕ, ‖rationalOfResolvent p q R ^ n‖ₑ ≤
        (⨆ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ₑ) ^ n := by
  sorry

/-! ### Convergence for every datum: Lax -/

/-- **Stability and consistency give convergence for every datum** (the sufficiency half of the
Lax equivalence theorem, for the time discretization; [Thomee2006], Ch. 7, 9; [Pazy1983], §3.4).
Let `S` be a strongly continuous semigroup of a Banach space `E` over `𝕜 = ℝ` or `ℂ` with
`‖S t‖ ≤ M`, and let Banach spaces `Xₕ` (`h : κ`, refined along a filter `l`) carry bounded
generators `Lₕ` with `‖e^{tLₕ}‖ ≤ M` for `t ≥ 0`, uniformly in `h`, read in `E` by `ιₕ` with left
inverses `πₕ` (`πₕ ιₕ = 1`), `‖ιₕ‖, ‖πₕ‖ ≤ C`, time steps `τₕ > 0` with `τₕ → 0`, and data `vₕ`
whose semidiscrete solutions `ιₕ e^{tLₕ} vₕ` converge to `S(t) x` uniformly on every `[0, T]`.
Then the fully discrete solutions `ιₕ Pₕⁿ vₕ` converge to `S(nτₕ) x` uniformly over the time
levels `nτₕ ∈ [0, T]`, for every `x`, no smoothness of `x` or `vₕ` assumed (`S` enters the
conclusion only through `S(nτₕ) x`, the limit of the semidiscrete solutions), for:

* every time scheme `Pₕ` that is power bounded (`‖Pₕⁿ‖ ≤ Mₛ(t)` for `nτₕ ≤ t`) and consistent
  of order `m ≥ 1` (`‖Pₕ y - e^{τₕLₕ} y‖ ≤ K τₕ^{m+1} ‖Lₕ^{m+1} y‖`);
* backward Euler `Pₕ = (1 - τₕLₕ)⁻¹`, with no assumption on the scheme (power bounded by
  Hille–Yosida, `backwardEuler`, of order `1`);
* every A-stable `r = p/q` of order `m ≥ 1`, `Pₕ = r(τₕLₕ)`, when the `Xₕ` are Hilbert spaces
  (their norms satisfy the parallelogram law) and the semigroups contractions (`M ≤ 1`): then
  `r(τₕLₕ)` is a contraction (`contractive`; for bounded `Lₕ` on a Hilbert space, `‖e^{tLₕ}‖ ≤ 1`
  iff `Lₕ` is dissipative), consistent of order `m` (`error`).

On a Banach space the A-stable schemes that are only `√n`-stable (`stable`) are not covered:
convergence for every datum is not claimed for them. -/
theorem converges {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E)
    (hS : IsC0Semigroup S) {κ : Type*} (l : Filter κ) (X : κ → Type*)
    [∀ h, NormedAddCommGroup (X h)] [∀ h, NormedSpace 𝕜 (X h)] [∀ h, CompleteSpace (X h)]
    [∀ h, NormedSpace ℝ (X h)] [∀ h, IsScalarTower ℝ 𝕜 (X h)] (L : ∀ h, X h →L[𝕜] X h) (M : ℝ)
    (hL : ∀ h (t : ℝ), 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L h)‖ ≤ M)
    (hSM : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) (ι : ∀ h, X h →L[𝕜] E) (π : ∀ h, E →L[𝕜] X h)
    (hπι : ∀ h x, π h (ι h x) = x) (hC : ∃ C, ∀ h, ‖ι h‖ ≤ C ∧ ‖π h‖ ≤ C) (τ : κ → ℝ)
    (hτ : ∀ h, 0 < τ h) (hτ0 : Tendsto τ l (𝓝 0)) (x : E) (v : ∀ h, X h)
    (hsd : ∀ T : ℝ, TendstoUniformlyOn
      (fun h (t : ℝ) => ι h (NormedSpace.exp ((t : 𝕜) • L h) (v h))) (fun t => S t x) l (Icc 0 T))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∀ (P : ∀ h, X h →L[𝕜] X h) (Ms : ℝ → ℝ),
      (∀ (t : ℝ) (h : κ) (n : ℕ), n * τ h ≤ t → ‖P h ^ n‖ ≤ Ms t) → ∀ {m : ℕ}, 0 < m →
      ∀ {K : ℝ}, 0 ≤ K → (∀ h (y : X h), ‖P h y - NormedSpace.exp ((τ h : 𝕜) • L h) y‖ ≤
        K * τ h ^ (m + 1) * ‖(L h ^ (m + 1)) y‖) →
      ∀ᶠ h in l, ∀ n : ℕ, n * τ h ∈ Icc 0 T → ‖S (n * τ h) x - ι h ((P h ^ n) (v h))‖ < ε) ∧
    (∀ᶠ h in l, ∀ n : ℕ, n * τ h ∈ Icc 0 T →
      ‖S (n * τ h) x - ι h ((Ring.inverse (1 - (τ h : 𝕜) • L h) ^ n) (v h))‖ < ε) ∧
    ((∀ h, InnerProductSpaceable (X h)) → M ≤ 1 → ∀ p q : ℝ[X], IsAStable p q →
      ∀ m : ℕ, HasOrder p q m → 0 < m →
      ∀ᶠ h in l, ∀ n : ℕ, n * τ h ∈ Icc 0 T →
        ‖S (n * τ h) x - ι h ((rationalApply p q ((τ h : 𝕜) • L h) ^ n) (v h))‖ < ε) := by
  sorry

/-! ### Where the Banach theory is needed: the heat equation in the maximum norm -/

/-- `L` is a **sub-Markov generator** on `ℝ^ι` (`ι` finite, maximum norm): `L + c` is positive
for some `c ≥ 0` and `L 𝟙 ≤ 0`. For a matrix: nonnegative off-diagonal entries and nonpositive
row sums. -/
def IsSubMarkovGenerator {ι : Type*} [Fintype ι] (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) : Prop :=
  (∃ c : ℝ, 0 ≤ c ∧ ∀ v : ι → ℝ, 0 ≤ v → 0 ≤ L v + c • v) ∧ ∀ i, L (fun _ => 1) i ≤ 0

/-- **Sub-Markov generators are contractive in the maximum norm** ([CiarletRaviart1973];
[Thomee2006], Ch. 15), so the Banach-space bounds hold for them with `M = 1`. For a sub-Markov
generator `L` on `ℝ^ι` with the maximum norm, `e^{tL}` (`t ≥ 0`) is positive and
`‖e^{tL}‖ ≤ 1`, and for `τ > 0` backward Euler `(1 - τL)⁻¹` exists, is positive and
`‖(1 - τL)⁻¹‖ ≤ 1`. -/
theorem subMarkov {ι : Type*} [Fintype ι] {L : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hL : IsSubMarkovGenerator L) :
    (∀ t : ℝ, 0 ≤ t → (∀ v, 0 ≤ v → 0 ≤ NormedSpace.exp (t • L) v) ∧
      ‖NormedSpace.exp (t • L)‖ ≤ 1) ∧
    ∀ τ : ℝ, 0 < τ → IsUnit (1 - τ • L) ∧ (∀ v, 0 ≤ v → 0 ≤ Ring.inverse (1 - τ • L) v) ∧
      ‖Ring.inverse (1 - τ • L)‖ ≤ 1 := by
  sorry

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

/-- **The lumped-mass heat equation in the maximum norm on non-obtuse meshes: the discrete
maximum principle, and the stability and error bounds of every A-stable scheme with constants
independent of the mesh** ([CiarletRaviart1973]; [Thomee2006], Ch. 15; [BrennerThomee1979]).
For every A-stable `r = p/q` there are `C ≥ 0`, depending on `r` only, and `K m`, depending on
`r` and `m` only, such that for every non-obtuse simplicial mesh `M` of a domain `Ω` of `ℝⁿ`
(every `n`; no shape regularity, quasi-uniformity or condition on the domain) and injective
nodes `x : ι → ℝⁿ`, the lumped-mass Laplacian `Lₕ` on `ℝ^ι` with the maximum norm:

* (**the discrete maximum principle**) is a sub-Markov generator, so (`subMarkov`) `e^{tLₕ}` and
  backward Euler are positive contractions of the maximum norm;
* (**stability**, the bounded-generator clause of `stable` with `M = 1`) for `τ > 0`, `q(τLₕ)` is
  invertible and `‖r(τLₕ)ᵏ‖_∞ ≤ 1 + C √k`;
* (**backward Euler**, power bounded) for every `u : ℝ → ℝⁿ → ℝ` with time derivatives `u₁`, `u₂`
  at the nodes on `[0, kτ]`, `‖Iₕ u₂(s)‖_∞ ≤ B` and nodal consistency error
  `‖Iₕ u₁(s) - Lₕ Iₕ u(s)‖_∞ ≤ ε` there (`Iₕ f = f ∘ x` the nodal values; for a solution of
  `uₜ = Δu`, `u₁ = Δu`) and every discrete datum `v`,
  `‖Iₕ u(kτ) - (1 - τLₕ)⁻ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ (3/2 τ B + ε)`: first order, with a
  temporal term of the solution `u` alone (bounded uniformly in the mesh when `uₜₜ` is bounded
  on `[0, kτ] × Ω̄` and the nodes lie in `Ω̄`; for a solution of the heat equation this asks a
  compatibility condition of order `1` of its initial value);
* (**every A-stable scheme**, the bounded-generator clause of `error`) if `r` has order `m`: for
  `u`, `u₁` and `ε` as above,
  `‖Iₕ u(kτ) - r(τLₕ)ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ ε + K m kτ τᵐ ‖Lₕ^{m+1} v‖_∞`.

The constants are independent of the mesh; the bounds are not convergence statements uniform in
the mesh. The errors are at the nodes. The consistency error `ε` depends on the mesh (`O(h²)` on
the Freudenthal meshes of a cube, where `Lₕ` is the finite difference Laplacian of `fdHeat`; on a
general non-obtuse mesh it need not be small). The temporal term of the last bound is that of the
discrete datum `v`: it is bounded uniformly in the mesh for compatible data on a cube (`fdHeat`),
not in general. `√k` is what the contractivity of `e^{tLₕ}` alone gives. For bounded analytic
semigroups of Banach spaces the A-stable rational approximations, Crank–Nicolson included, are
power bounded ([CrouzeixLarssonPiskarevThomee1993]); here that would need the analyticity of
`e^{tLₕ}` in the maximum norm uniformly in the mesh, and neither is stated. -/
theorem maxNormHeat (p q : ℝ[X]) (hr : IsAStable p q) :
    ∃ (C : ℝ) (K : ℕ → ℝ), 0 ≤ C ∧ ∀ (n : ℕ) (M : SimplicialMesh n), IsNonobtuse M →
      ∀ {ι : Type*} [Fintype ι] (x : ι → Fin n → ℝ), Function.Injective x →
        IsSubMarkovGenerator (lumpedLaplacian M x) ∧
        (∀ τ : ℝ, 0 < τ → IsUnit (aeval (τ • lumpedLaplacian M x) q) ∧ ∀ k : ℕ,
          ‖rationalApply p q (τ • lumpedLaplacian M x) ^ k‖ ≤ 1 + C * √k) ∧
        (∀ τ : ℝ, 0 < τ → ∀ (k : ℕ) (u u₁ u₂ : ℝ → (Fin n → ℝ) → ℝ) (B ε : ℝ) (v : ι → ℝ),
          (∀ s ∈ Icc 0 (k * τ), ∀ i, HasDerivAt (fun s => u s (x i)) (u₁ s (x i)) s) →
          (∀ s ∈ Icc 0 (k * τ), ∀ i, HasDerivAt (fun s => u₁ s (x i)) (u₂ s (x i)) s) →
          (∀ s ∈ Icc 0 (k * τ), ‖u₂ s ∘ x‖ ≤ B) →
          (∀ s ∈ Icc 0 (k * τ), ‖u₁ s ∘ x - lumpedLaplacian M x (u s ∘ x)‖ ≤ ε) →
          ‖u (k * τ) ∘ x - (Ring.inverse (1 - τ • lumpedLaplacian M x) ^ k) v‖ ≤
            ‖u 0 ∘ x - v‖ + k * τ * (3 / 2 * τ * B + ε)) ∧
        ∀ m : ℕ, HasOrder p q m → ∀ τ : ℝ, 0 < τ → ∀ (k : ℕ) (u u₁ : ℝ → (Fin n → ℝ) → ℝ)
          (ε : ℝ) (v : ι → ℝ),
          (∀ s ∈ Icc 0 (k * τ), ∀ i, HasDerivAt (fun s => u s (x i)) (u₁ s (x i)) s) →
          (∀ s ∈ Icc 0 (k * τ), ‖u₁ s ∘ x - lumpedLaplacian M x (u s ∘ x)‖ ≤ ε) →
          ‖u (k * τ) ∘ x - (rationalApply p q (τ • lumpedLaplacian M x) ^ k) v‖ ≤
            ‖u 0 ∘ x - v‖ + k * τ * ε +
              K m * (k * τ) * τ ^ m * ‖(lumpedLaplacian M x ^ (m + 1)) v‖ := by
  sorry

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

/-- **The heat equation in the maximum norm by finite differences**, the witness of
`maxNormHeat` ([Thomee2006], Ch. 15; [BrennerThomee1979]):

* (**the discrete maximum principle**) on every finite grid, for every mesh size, the finite
  difference Laplacian is a sub-Markov generator, so the bounded-generator clauses of `stable`
  and `error` hold for it with `M = 1` (`subMarkov`);

and on the cube `Q = b + (0, s)ⁿ` with the grid of the `Nⁿ` interior nodes `b + h q`,
`q ∈ {1, …, N}ⁿ` (`gridNodes`), `h = s/(N + 1)`, the nodal interpolant `Iₕ` (`gridInterp`) and
the finite difference Laplacian `Δₕ`:

* (**finite differences are lumped-mass `P₁` elements**) `Δₕ` is the lumped-mass Laplacian of a
  non-obtuse mesh of `Q` on the interior nodes (in the proof, the Freudenthal mesh of the Kuhn
  simplices `b + h (z + K_σ)`), so `maxNormHeat` applies to it;
* (**`O(h² + τᵐ)` from compatible data**) for every A-stable `r = p/q` of order `m` there is `K`,
  depending on `r` and `m` only, such that: let `u` be a classical solution of
  `uₜ = Δu = Σᵢ D²u(eᵢ, eᵢ)` on `Q` for `t ∈ [0, T]` (`u(t)` of class `C⁴` on `ℝⁿ`, with
  two-sided time derivative `u₁` at the points of `Q` and of `[0, T]`), vanishing on `∂Q`, with
  pure fourth derivatives `|∂ᵢ⁴ u(t)| = |D⁴u(t)(eᵢ, eᵢ, eᵢ, eᵢ)| ≤ B` on `Q̄`, whose initial
  value satisfies the **compatibility conditions of order `m`**: `u(0)` is on `Q̄` a function `ũ`
  of class `C^{2m+2}` on `ℝⁿ` that is odd under the reflections in the faces of `Q`
  (`xᵢ ↦ 2bᵢ - xᵢ`, `xᵢ ↦ 2(bᵢ + s) - xᵢ`: `ũ` is the odd `2s`-periodic extension of `u(0)`;
  for `n = 1`, `u(0) ∈ C^{2m+2}(Q̄)` with `∂^{2j} u(0) = 0` at both ends for `j ≤ m + 1`), with
  `|∂²_{l 0} ⋯ ∂²_{l m} ũ| = |D^{2m+2}ũ(e_{l 0}, e_{l 0}, …, e_{l m}, e_{l m})| ≤ B'` for all
  directions `l` (only `l 0, …, l m` enter). The scheme started from `Iₕ u(0)` satisfies, for
  every `τ > 0` and `kτ ≤ T`,
  `‖Iₕ u(kτ) - r(τΔₕ)ᵏ Iₕ u(0)‖_∞ ≤ kτ (n B h²/12 + K nᵐ⁺¹ B' τᵐ)`: `O(h² + τᵐ)` with `K`
  independent of `h`, `τ`, the dimension and `u`. -/
theorem fdHeat :
    (∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Finset (ι → ℤ)) (h : ℝ),
      IsSubMarkovGenerator (fdLaplacian G h)) ∧
    (∀ (n N : ℕ) (b : Fin n → ℝ) (s : ℝ), 0 < s → ∃ M : SimplicialMesh n,
      M.domain = univ.pi (fun i => Ioo (b i) (b i + s)) ∧ IsNonobtuse M ∧
      lumpedLaplacian M (fun g : gridNodes n N => gridPoint b (s / (N + 1 : ℕ)) g) =
        fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ))) ∧
    ∀ p q : ℝ[X], IsAStable p q → ∀ m : ℕ, HasOrder p q m →
    ∃ K : ℝ, ∀ (n : ℕ) (b : Fin n → ℝ) (s T B B' : ℝ) (u u₁ : ℝ → (Fin n → ℝ) → ℝ)
      (ũ : (Fin n → ℝ) → ℝ), 0 < s →
      (∀ t ∈ Icc 0 T, ContDiff ℝ 4 (u t)) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Ioo (b i) (b i + s),
        HasDerivAt (fun t => u t x) (u₁ t x) t ∧
          u₁ t x = ∑ i, iteratedFDeriv ℝ 2 (u t) x fun _ => Pi.single i 1) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Icc (b i) (b i + s),
        x ∉ univ.pi (fun i => Ioo (b i) (b i + s)) → u t x = 0) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Icc (b i) (b i + s), ∀ i,
        |iteratedFDeriv ℝ 4 (u t) x fun _ => Pi.single i 1| ≤ B) →
      ContDiff ℝ (2 * m + 2) ũ → (∀ x ∈ univ.pi fun i => Icc (b i) (b i + s), ũ x = u 0 x) →
      (∀ i x, ũ (Function.update x i (2 * b i - x i)) = -ũ x ∧
        ũ (Function.update x i (2 * (b i + s) - x i)) = -ũ x) →
      (∀ (l : ℕ → Fin n) x,
        |iteratedFDeriv ℝ (2 * m + 2) ũ x fun j => Pi.single (l ((j : ℕ) / 2)) 1| ≤ B') →
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

/-! ### The classical inputs -/

/-- **The Hille–Yosida estimates** ([Pazy1983], §1.5), the input of `backwardEuler` and of the
resolvent form of `r(τA)`. Let `S` be a strongly continuous semigroup of a complex Banach space
(real ones are covered by complexification in `Feec`, not here) with `‖S t‖ ≤ M e^{ωt}`,
generator `A`. Every `z` with `re z > ω` is in the resolvent set of `A`: there is a bounded `R`
with `R (z x - A x) = x` on `D(A)`, `R y ∈ D(A)` with `A R y = z R y - y`, and
`‖Rᵐ‖ ≤ M/(re z - ω)ᵐ` for every `m`. At `z = 1/τ`, `ωτ < 1`, the resolvent `(1 - τA)⁻¹ = z R`
defines the rational schemes `r(τA)` (`rationalOfResolvent`) and is backward Euler. -/
theorem hilleYosida {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (S : ℝ → E →L[ℂ] E) (hS : IsC0Semigroup S) {M ω : ℝ}
    (hSb : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M * Real.exp (ω * t)) (z : ℂ) (hz : ω < z.re) :
    ∃ R : E →L[ℂ] E, (∀ x y : E, (x, y) ∈ generatorGraph S → R (z • x - y) = x) ∧
      (∀ y : E, (R y, z • R y - y) ∈ generatorGraph S) ∧
      ∀ m : ℕ, ‖R ^ m‖ ≤ M / (z.re - ω) ^ m := by
  sorry

/-- **Von Neumann's inequality** ([VonNeumann1951]), for rational functions, the input of
`contractive`. For a contraction `T` of a complex Hilbert space and complex polynomials `p`, `q`
with `q` free of zeros in the closed unit disc, `q(T)` is invertible and
`‖p(T) q(T)⁻¹‖ ≤ sup_{|ζ| = 1} |p(ζ)/q(ζ)|` (for `q = 1`, `‖p(T)‖ ≤ sup_{|ζ| = 1} |p(ζ)|`).
Through the Cayley transform it gives `contractive`. -/
theorem vonNeumann {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {T : E →L[ℂ] E} (hT : ‖T‖ ≤ 1) (p q : ℂ[X])
    (hq : ∀ z : ℂ, ‖z‖ ≤ 1 → q.eval z ≠ 0) :
    IsUnit (aeval T q) ∧
      ‖aeval T p * Ring.inverse (aeval T q)‖ₑ ≤
        ⨆ ζ ∈ Metric.sphere (0 : ℂ) 1, ‖p.eval ζ / q.eval ζ‖ₑ := by
  sorry

end TimeStepping
