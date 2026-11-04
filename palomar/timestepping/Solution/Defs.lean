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
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but its sixteen theorems),
compiled against Mathlib alone so that their elaborated values are those of the challenge: its
imports, opens and the definitions `TimeStepping.IsC0Semigroup`, `TimeStepping.generatorGraph`,
`TimeStepping.resolventPoly`, `TimeStepping.rationalOfResolvent`, `TimeStepping.rationalApply`,
`TimeStepping.IsAStable`, `TimeStepping.HasOrder`, `TimeStepping.IsSubMarkovGenerator`,
`TimeStepping.fdLaplacian`, `TimeStepping.gridNodes`, `TimeStepping.gridInterp` and
`TimeStepping.partialDeriv`. The solution imports this module and
the bridge to `Feec` and proves the theorems (`Solution.lean`).

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../../docs/references.bib)
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

/-! ### Uniformly stable families of bounded generators -/

/-! ### Hilbert spaces -/

/-! ### The maximum norm -/

/-- `L` is a **sub-Markov generator** on `ℝ^ι` (`ι` finite, maximum norm): `L + c` is positive
for some `c ≥ 0` and `L 𝟙 ≤ 0`. For a matrix: nonnegative off-diagonal entries and nonpositive
row sums. -/
def IsSubMarkovGenerator {ι : Type*} [Fintype ι] (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) : Prop :=
  (∃ c : ℝ, 0 ≤ c ∧ ∀ v : ι → ℝ, 0 ≤ v → 0 ≤ L v + c • v) ∧ ∀ i, L (fun _ => 1) i ≤ 0

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

/-! ### The hypotheses on `r` are met -/

end TimeStepping
