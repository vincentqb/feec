module

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

/-!
# Time stepping for uniformly stable semigroup families on Banach spaces

A one-step method for `u' = A u` replaces the exact evolution `e^{τA}` by `r(τA)`, `r = p/q` a
rational function with real coefficients; it is **A-stable** (`IsAStable`) if `q` has no zero
and `|r| ≤ 1` on the closed left half-plane, and of **order `m`** (`HasOrder`) if
`r(z) - e^z = O(z^{m+1})` at `0`. On a Hilbert space von Neumann's inequality makes A-stable
schemes contractive; on a Banach space, e.g. for the heat equation in the maximum norm, they need
not be power bounded. Brenner and Thomée showed that they are nevertheless nearly stable and
converge at their order for smooth data, with constants depending on `r` only. The estimates
therefore hold uniformly over families of space discretizations, and stability with consistency
gives convergence for every datum; finite differences for the heat equation are the example.

Mathlib has no `C₀`-semigroups: `IsC0Semigroup` is the definition and `generatorGraph` the graph
of the generator (right derivatives at `0`). For a bounded `L`, `r(τL) = p(τL) q(τL)⁻¹`
(`rationalApply`); for a generator `A` with resolvent `R = (1 - τA)⁻¹`, `r(τA) = P(R) Q(R)⁻¹`
(`rationalOfResolvent`, `resolventPoly`), `P(R) = p(τA) Rᴺ`, `N = deg q`.

**Banach spaces** ([BrennerThomee1979], Thms 1, 4, as stated in [GomilkoTomilov2024], Thm 1.1).
For every A-stable `r`, `|r(∞)| = 1` included, and every bounded strongly continuous semigroup
(`‖S(t)‖ ≤ M`) of a real or complex Banach space, `‖r(τA)ⁿ‖ ≤ M (1 + C √n)` (`stable`), and for
`r` of order `m`, `‖r(τA)ⁿ x - S(nτ) x‖ ≤ K M nτ τᵐ ‖A^{m+1} x‖` (`error`), `C`, `K` depending
on `r`, `m` only. The Hille–Yosida estimates (`hilleYosida`, [Pazy1983], §1.5) make backward
Euler power bounded also under growth `‖S(t)‖ ≤ M e^{ωt}` (`backwardEuler`).

**Uniformly stable families** ([Thomee2006], Ch. 7, 9). The same bounds for every bounded `L`
with `‖e^{tL}‖ ≤ M` (`stable_of_bounded`, `error_of_bounded`, the latter also along a
trajectory with a defect). For bounded generators `Lₕ` on Banach spaces `Xₕ`, uniformly stable
and read in `E` by uniformly bounded `ιₕ` with uniformly bounded left inverses: if the
semidiscrete solutions converge to `S(t) x`, so do the fully discrete solutions of every
power-bounded scheme consistent of order `p ≥ 1`, for every datum (`converges`); backward Euler
is always one (`converges_backwardEuler`).

**Hilbert spaces** ([VonNeumann1951]; [HairerWanner1996], §IV.11). Von Neumann's inequality
(`vonNeumann`, `vonNeumann_rational`); for m-dissipative `A`,
`‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` (`contractive`).

**The maximum norm** ([CiarletRaviart1973]; [Thomee2006], Ch. 15). A sub-Markov generator
(`IsSubMarkovGenerator`) generates positive contractions and has positive contractive backward
Euler steps (`subMarkov`); the finite difference Laplacian `fdLaplacian` on every finite grid of
`ℤ^ι` is one (`isSubMarkovGenerator_fdLaplacian`). On a cube, every A-stable scheme of order `m`
approximates every classical solution of the heat equation with bounded fourth derivatives to
`O(h²) + O(τᵐ)` in the maximum norm (`fdHeat`). Backward Euler and Crank–Nicolson satisfy the
hypotheses on `r` (`backwardEuler_isAStable`, `crankNicolson_isAStable`).

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

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Polynomial Asymptotics Filter Set

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
`D(A)`, `R y ∈ D(A)` with `A R y = z R y - y`, and `‖Rᵐ‖ ≤ M/(re z - ω)ᵐ` for every `m`. -/
theorem hilleYosida {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (S : ℝ → E →L[ℂ] E) (hS : IsC0Semigroup S) {M ω : ℝ}
    (hSb : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M * Real.exp (ω * t)) (z : ℂ) (hz : ω < z.re) :
    ∃ R : E →L[ℂ] E, (∀ x y : E, (x, y) ∈ generatorGraph S → R (z • x - y) = x) ∧
      (∀ y : E, (R y, z • R y - y) ∈ generatorGraph S) ∧
      ∀ m : ℕ, ‖R ^ m‖ ≤ M / (z.re - ω) ^ m := by
  sorry

/-- **Backward Euler on Banach spaces** ([BrennerThomee1979]; [Pazy1983], §1.5). Let `S` be a
strongly continuous semigroup of a real or complex Banach space with `‖S t‖ ≤ M e^{ωt}`
(`ω ≥ 0`), generator `A`, `τ > 0` with `ωτ < 1`, and `R` with `R (x - τAx) = x` on `D(A)`, so
that `r(τA) = R` for `r(z) = 1/(1 - z)`. Then `‖Rᵏ‖ ≤ M/(1 - ωτ)ᵏ` (Hille–Yosida), and for every
`n` and `x ∈ D(A²)` (a chain `u 0 = x, u 1 = A x, u 2 = A² x` in the graph of `A`)
`‖Rⁿ x - S(nτ) x‖ ≤ (M/(1 - ωτ)ⁿ) (M/(1 - ωτ) + M e^{ωnτ}/2) M e^{ωnτ} nτ τ ‖A² x‖`. -/
theorem backwardEuler {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E)
    (hS : IsC0Semigroup S) {M ω : ℝ} (hω : 0 ≤ ω)
    (hSb : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M * Real.exp (ω * t)) {τ : ℝ} (hτ : 0 < τ)
    (hωτ : ω * τ < 1) (R : E →L[𝕜] E)
    (hR : ∀ x y : E, (x, y) ∈ generatorGraph S → R (x - (τ : 𝕜) • y) = x) :
    (∀ k : ℕ, ‖R ^ k‖ ≤ M / (1 - ω * τ) ^ k) ∧
      ∀ (n : ℕ) (u : ℕ → E), (∀ j < 2, (u j, u (j + 1)) ∈ generatorGraph S) →
        ‖(R ^ n) (u 0) - S (n * τ) (u 0)‖ ≤ M / (1 - ω * τ) ^ n *
          (M / (1 - ω * τ) + M * Real.exp (ω * (n * τ)) / 2) * (M * Real.exp (ω * (n * τ))) *
            (n * τ) * τ * ‖u 2‖ := by
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

/-! ### Uniformly stable families of bounded generators -/

/-- **Brenner–Thomée's stability bound for bounded generators**, uniformly in the generator.
For every A-stable `r = p/q` there is `C ≥ 0`, depending on `r` only, such that for every
bounded operator `L` of a real or complex Banach space with `‖e^{tL}‖ ≤ M` (`t ≥ 0`) and every
`τ > 0`, `q(τL)` is invertible and `‖r(τL)ⁿ‖ ≤ M (1 + C √n)` for every `n`. -/
theorem stable_of_bounded (p q : ℝ[X]) (hr : IsAStable p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [CompleteSpace X] (L : X →L[𝕜] X) (M : ℝ),
      (∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L)‖ ≤ M) → ∀ τ : ℝ, 0 < τ →
        IsUnit (aeval ((τ : 𝕜) • L) (q.map (algebraMap ℝ 𝕜))) ∧
        ∀ n : ℕ, ‖rationalApply p q ((τ : 𝕜) • L) ^ n‖ ≤ M * (1 + C * √n) := by
  sorry

/-- **The error of A-stable schemes for bounded generators**, uniformly in the generator. For
every A-stable `r = p/q` of order `m` there is `K`, depending on `r` and `m` only, such that for
every bounded operator `L` of a real or complex Banach space with `‖e^{tL}‖ ≤ M` (`t ≥ 0`), every
`τ > 0`, `n` and `v`: `‖r(τL)ⁿ v - e^{nτL} v‖ ≤ K M nτ τᵐ ‖L^{m+1} v‖`, and for every curve `U`
(a trajectory, e.g. the interpolant of an exact solution) with derivative `U'` at every point
of `[0, nτ]` (two-sided, so `U` is defined around the endpoints) and defect `‖U' - L U‖ ≤ D`
there,
`‖U(nτ) - r(τL)ⁿ v‖ ≤ M ‖U(0) - v‖ + M nτ D + K M nτ τᵐ ‖L^{m+1} v‖`. -/
theorem error_of_bounded (p q : ℝ[X]) (hr : IsAStable p q) {m : ℕ} (hm : HasOrder p q m) :
    ∃ K : ℝ, ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [CompleteSpace X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] (L : X →L[𝕜] X) (M : ℝ),
      (∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L)‖ ≤ M) → ∀ τ : ℝ, 0 < τ →
      ∀ (n : ℕ) (v : X),
        ‖(rationalApply p q ((τ : 𝕜) • L) ^ n) v - NormedSpace.exp (((n * τ : ℝ) : 𝕜) • L) v‖ ≤
          K * M * (n * τ) * τ ^ m * ‖(L ^ (m + 1)) v‖ ∧
        ∀ (U U' : ℝ → X) (D : ℝ), (∀ s ∈ Icc 0 (n * τ), HasDerivAt U (U' s) s) →
          (∀ s ∈ Icc 0 (n * τ), ‖U' s - L (U s)‖ ≤ D) →
          ‖U (n * τ) - (rationalApply p q ((τ : 𝕜) • L) ^ n) v‖ ≤
            M * ‖U 0 - v‖ + M * (n * τ) * D + K * M * (n * τ) * τ ^ m * ‖(L ^ (m + 1)) v‖ := by
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

/-- **Backward Euler converges for every datum**: in the setting of `converges`, with no
assumption on the scheme, `Pₕ = (1 - τₕLₕ)⁻¹` (stable by Hille–Yosida, of order `1`). -/
theorem converges_backwardEuler {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    (S : ℝ → E →L[𝕜] E) (hS : IsC0Semigroup S) {κ : Type*} (l : Filter κ) (X : κ → Type*)
    [∀ h, NormedAddCommGroup (X h)] [∀ h, NormedSpace 𝕜 (X h)] [∀ h, CompleteSpace (X h)]
    [∀ h, NormedSpace ℝ (X h)] [∀ h, IsScalarTower ℝ 𝕜 (X h)] (L : ∀ h, X h →L[𝕜] X h) (M : ℝ)
    (hL : ∀ h (t : ℝ), 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L h)‖ ≤ M)
    (hSM : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) (ι : ∀ h, X h →L[𝕜] E) (π : ∀ h, E →L[𝕜] X h)
    (hπι : ∀ h x, π h (ι h x) = x) (hC : ∃ C, ∀ h, ‖ι h‖ ≤ C ∧ ‖π h‖ ≤ C) (τ : κ → ℝ)
    (hτ : ∀ h, 0 < τ h) (hτ0 : Tendsto τ l (𝓝 0)) (x : E) (v : ∀ h, X h)
    (hsd : ∀ T : ℝ, TendstoUniformlyOn
      (fun h (t : ℝ) => ι h (NormedSpace.exp ((t : 𝕜) • L h) (v h))) (fun t => S t x) l (Icc 0 T))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in l, ∀ n : ℕ, n * τ h ∈ Icc 0 T →
      ‖S (n * τ h) x - ι h ((Ring.inverse (1 - (τ h : 𝕜) • L h) ^ n) (v h))‖ < ε := by
  sorry

/-! ### Hilbert spaces -/

/-- **Von Neumann's inequality** ([VonNeumann1951]). For a contraction `T` of a complex inner
product space, not necessarily complete, and a complex polynomial `p`,
`‖p(T)‖ ≤ sup_{|ζ| = 1} |p(ζ)|` (suprema in `[0, ∞]`). -/
theorem vonNeumann {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {T : E →L[ℂ] E}
    (hT : ‖T‖ ≤ 1) (p : ℂ[X]) :
    ‖aeval T p‖ₑ ≤ ⨆ ζ ∈ Metric.sphere (0 : ℂ) 1, ‖p.eval ζ‖ₑ := by
  sorry

/-- **Von Neumann's inequality for rational functions** ([VonNeumann1951]). For a contraction
`T` of a complex Hilbert space and complex polynomials `p`, `q` with `q` free of zeros in the
closed unit disc, `q(T)` is invertible and `‖p(T) q(T)⁻¹‖ ≤ sup_{|ζ| = 1} |p(ζ)/q(ζ)|`. -/
theorem vonNeumann_rational {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
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

/-- `L` is a **sub-Markov generator** on `ℝ^ι` (`ι` finite, maximum norm): `L + c` is positive
for some `c ≥ 0` and `L 𝟙 ≤ 0`. For a matrix: nonnegative off-diagonal entries and nonpositive
row sums. -/
def IsSubMarkovGenerator {ι : Type*} [Fintype ι] (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) : Prop :=
  (∃ c : ℝ, 0 ≤ c ∧ ∀ v : ι → ℝ, 0 ≤ v → 0 ≤ L v + c • v) ∧ ∀ i, L (fun _ => 1) i ≤ 0

/-- **The discrete maximum principle gives contractions in the maximum norm**
([CiarletRaviart1973]; [Thomee2006], Ch. 15). For a sub-Markov generator `L` on `ℝ^ι` with the
maximum norm, `e^{tL}` (`t ≥ 0`) is positive and `‖e^{tL}‖ ≤ 1`, and for `τ > 0` backward Euler
`(1 - τL)⁻¹` exists, is positive and `‖(1 - τL)⁻¹‖ ≤ 1`. -/
theorem subMarkov {ι : Type*} [Fintype ι] {L : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hL : IsSubMarkovGenerator L) :
    (∀ t : ℝ, 0 ≤ t → (∀ v, 0 ≤ v → 0 ≤ NormedSpace.exp (t • L) v) ∧
      ‖NormedSpace.exp (t • L)‖ ≤ 1) ∧
    ∀ τ : ℝ, 0 < τ → IsUnit (1 - τ • L) ∧ (∀ v, 0 ≤ v → 0 ≤ Ring.inverse (1 - τ • L) v) ∧
      ‖Ring.inverse (1 - τ • L)‖ ≤ 1 := by
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

/-- **The discrete maximum principle for finite differences** ([Thomee2006], Ch. 15): the finite
difference Laplacian on every finite grid, for every mesh size, is a sub-Markov generator. -/
theorem isSubMarkovGenerator_fdLaplacian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Finset (ι → ℤ)) (h : ℝ) : IsSubMarkovGenerator (fdLaplacian G h) := by
  sorry

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
derivatives `|∂ᵢ⁴ u(t)| ≤ B` on `Q̄`. On the grid of the `Nⁿ` interior nodes `b + h q`,
`q ∈ {1, …, N}ⁿ` (`gridNodes`), `h = s/(N + 1)`, with the nodal interpolant `Iₕ` (`gridInterp`),
the finite difference Laplacian `Δₕ` and every `τ > 0`, `kτ ≤ T` and discrete datum `v`,
`‖Iₕ u(kτ) - r(τΔₕ)ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ n B h²/12 + K kτ τᵐ ‖Δₕ^{m+1} v‖_∞`. The
last term is of the discrete datum (for `v = Iₕ u(0)` it is bounded in `h` only under the usual
compatibility conditions at `∂Q`). -/
theorem fdHeat (p q : ℝ[X]) (hr : IsAStable p q) {m : ℕ} (hm : HasOrder p q m) :
    ∃ K : ℝ, ∀ (n : ℕ) (b : Fin n → ℝ) (s T B : ℝ) (u u₁ : ℝ → (Fin n → ℝ) → ℝ), 0 < s →
      (∀ t ∈ Icc 0 T, ContDiff ℝ 4 (u t)) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Ioo (b i) (b i + s),
        HasDerivAt (fun t => u t x) (u₁ t x) t ∧
          u₁ t x = ∑ i, partialDeriv i (partialDeriv i (u t)) x) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Icc (b i) (b i + s),
        x ∉ univ.pi (fun i => Ioo (b i) (b i + s)) → u t x = 0) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Icc (b i) (b i + s), ∀ i,
        |(partialDeriv i)^[4] (u t) x| ≤ B) →
      ∀ (N : ℕ) (τ : ℝ), 0 < τ → ∀ k : ℕ, k * τ ≤ T → ∀ v : gridNodes n N → ℝ,
        ‖gridInterp b (s / (N + 1 : ℕ)) N (u (k * τ)) -
            (rationalApply p q (τ • fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ))) ^ k) v‖ ≤
          ‖gridInterp b (s / (N + 1 : ℕ)) N (u 0) - v‖ +
            k * τ * (n * B * (s / (N + 1 : ℕ)) ^ 2 / 12) +
            K * (k * τ) * τ ^ m *
              ‖(fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ)) ^ (m + 1)) v‖ := by
  sorry

/-! ### The hypotheses on `r` are met -/

/-- **Backward Euler** `r(z) = 1/(1 - z)` is A-stable of order `1`. -/
theorem backwardEuler_isAStable : IsAStable 1 (1 - X) ∧ HasOrder 1 (1 - X) 1 := by
  sorry

/-- **Crank–Nicolson** `r(z) = (2 + z)/(2 - z)` is A-stable (with `|r(∞)| = 1`) of order `2`. -/
theorem crankNicolson_isAStable : IsAStable (2 + X) (2 - X) ∧ HasOrder (2 + X) (2 - X) 2 := by
  sorry

end TimeStepping
