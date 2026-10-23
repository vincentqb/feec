module

public import Feec.Evolution.Solution
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Semi-discrete schemes: the vocabulary of the verdicts

The master theorems `Feec.HilbertComplex.approxFEEC` (a skew-adjoint generator, a unitary group)
and `Feec.HilbertComplex.dissipFEEC` (an m-dissipative generator, a contraction semigroup) state
their conclusions about the same objects: an exact flow `S(t)` on a space `E`, a constraint
`K ⊆ E`, a filter of refinements, discrete states `Xₕ` read in `E` through maps `ιₕ`, the
discrete states `πₕ x` of a datum, and the discrete solutions `ιₕ e^{tLₕ} v`. A **scheme**
(`Feec.Evolution.Scheme`) records exactly these, and this file states the predicates both
verdicts are made of, so that each verdict is a short conjunction of named predicates and the
skew-adjoint verdict contains the dissipative one of its forward-time reading.

## Main definitions

* `Evolution.IsUniqueSolution A T x u`: `u` is a classical solution of `u' = A u` on `[0, T]`
  and the only strong one from `x`.
* `Scheme.Converges σ v x`: the family `vₕ` converges to `x` through the reading maps, `ιₕ vₕ → x`.
* `Scheme.ConvergesFrom σ x`: the discrete states `πₕ x` converge to `x`, and from every family
  converging to `x` the discrete solutions converge to `S(t) x` uniformly on every `[0, T]`.
* `Scheme.residual σ y`: the distance `dist(y, K)` of `y` to the constraint.
* `Scheme.Keeps σ Q I`: `S(t) Q ⊆ Q` for every `t ∈ I` (forward invariance for `I = [0, ∞)`,
  invariance in both time directions for `I = ℝ`).
* `Scheme.Exits σ D Q I`: some datum of `D` leaves `Q` at some time of `I` (so `¬ σ.Keeps Q I`
  is `σ.Exits Q Q I`).
* `Scheme.ResidualBounded σ x`, `Scheme.ResidualVanishes σ x`: the residuals of the discrete
  solutions are at most their errors from `x`, and tend to `0` uniformly on every `[0, T]`.
* `Scheme.Detects σ Q x t`: if `S(t) x ∉ Q`, its distance to `Q` is positive and the distances
  of the discrete solutions at `t` tend to it.
* `Scheme.SmoothDense σ D`: the constraint lies in the closure of its part in `D`.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.4 (Trotter–Kato approximation theorems), §4.1 (classical and strong solutions)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4 (Thms 4.6, 4.7), §4.10 (Prop. 4.17)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter Topology Metric

@[expose] public noncomputable section

universe u

namespace Feec.Evolution

section Unique

variable {𝕜 E : Type*} [Ring 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [NormedSpace ℝ E]

/-- `u` is the unique solution of `A` from `x` up to time `T`: `u 0 = x`, `u` is a classical
solution of `u' = A u` on `[0, T]`, and every strong solution `U` there with `U 0 = x` is `u`.
See [Pazy1983], §4.1. -/
abbrev IsUniqueSolution (A : E →ₗ.[𝕜] E) (T : ℝ) (x : E) (u : ℝ → E) : Prop :=
  u 0 = x ∧ IsClassicalSolution A (Icc 0 T) 0 u ∧
    ∀ U : ℝ → E, U 0 = x → IsStrongSolution A (Icc 0 T) 0 U → EqOn U u (Icc 0 T)

end Unique

/-- A **semi-discrete scheme** on `E`: an exact flow `S(t)`, a constraint `K`, a filter of
refinements, discrete states `Xₕ` with reading maps `ιₕ : Xₕ → E`, the discrete states `πₕ x` of
the data, and the discrete solutions `ιₕ e^{tLₕ} v`. It carries only what the verdicts of
`approxFEEC` and `dissipFEEC` speak about. [Pazy1983], §3.4 -/
structure Scheme (E : Type*) (κ : Type*) where
  /-- the exact flow -/
  S : ℝ → E → E
  /-- the constraint -/
  K : Set E
  /-- the filter along which the scheme is refined -/
  l : Filter κ
  /-- the discrete states -/
  X : κ → Type u
  /-- the maps reading discrete states in `E` -/
  incl : ∀ h, X h → E
  /-- the discrete states of the data -/
  proj : ∀ h, E → X h
  /-- the discrete solutions -/
  sol : ∀ h, X h → ℝ → E

namespace Scheme

variable {E κ : Type*}

section General

variable (σ : Scheme.{u} E κ)

/-- `σ` keeps `Q` at the times of `I`, `S(t) Q ⊆ Q` for every `t ∈ I`. -/
abbrev Keeps (Q : Set E) (I : Set ℝ) : Prop := ∀ t ∈ I, ∀ x ∈ Q, σ.S t x ∈ Q

/-- `σ` takes some datum of `D` out of `Q` at a time of `I`: `S(t) x ∉ Q` for some `x ∈ D` and
`t ∈ I`. -/
abbrev Exits (D Q : Set E) (I : Set ℝ) : Prop := ∃ x ∈ D, ∃ t ∈ I, σ.S t x ∉ Q

theorem not_keeps_iff (Q : Set E) (I : Set ℝ) : ¬ σ.Keeps Q I ↔ σ.Exits Q Q I := by
  simp only [Keeps, Exits, not_forall, exists_prop]
  exact ⟨fun ⟨t, ht, x, hx, h⟩ => ⟨x, hx, t, ht, h⟩, fun ⟨x, hx, t, ht, h⟩ => ⟨t, ht, x, hx, h⟩⟩

end General

section Topology

variable [TopologicalSpace E] (σ : Scheme.{u} E κ)

/-- `v` converges to `x` through the reading maps of `σ`, `ιₕ vₕ → x`. -/
abbrev Converges (v : ∀ h, σ.X h) (x : E) : Prop :=
  Tendsto (fun h => σ.incl h (v h)) σ.l (𝓝 x)

/-- `σ` has its constraint in the closure of its part in `D`, `K ⊆ closure (D ∩ K)`. -/
abbrev SmoothDense (D : Set E) : Prop := ∀ k ∈ σ.K, k ∈ closure (D ∩ σ.K)

end Topology

section Uniform

variable [UniformSpace E] (σ : Scheme.{u} E κ)

/-- `σ` converges from `x`: the discrete states of `x` converge to `x`, and from every family
converging to `x` the discrete solutions converge to the exact one uniformly on every `[0, T]`.
[Pazy1983], §3.4 -/
abbrev ConvergesFrom (x : E) : Prop :=
  σ.Converges (fun h => σ.proj h x) x ∧ ∀ v : ∀ h, σ.X h, σ.Converges v x → ∀ T : ℝ,
    TendstoUniformlyOn (fun h t => σ.sol h (v h) t) (fun t => σ.S t x) σ.l (Icc 0 T)

end Uniform

section Metric

variable [PseudoMetricSpace E] (σ : Scheme.{u} E κ)

/-- The residual of `y` in `σ`, its distance `dist(y, K)` to the constraint. -/
abbrev residual (y : E) : ℝ := infDist y σ.K

/-- `σ` has residuals tending to zero from `x`: from every family converging to `x`, the
residuals of the discrete solutions tend to `0` uniformly on every `[0, T]`. -/
abbrev ResidualVanishes (x : E) : Prop :=
  ∀ v : ∀ h, σ.X h, σ.Converges v x → ∀ T : ℝ,
    TendstoUniformlyOn (fun h t => σ.residual (σ.sol h (v h) t)) (fun _ => 0) σ.l (Icc 0 T)

/-- `σ` detects the departure of `x` from `Q` at time `t`: if `S(t) x ∉ Q`, its distance to `Q`
is positive and, from every family converging to `x`, the distances to `Q` of the discrete
solutions at time `t` tend to it. -/
abbrev Detects (Q : Set E) (x : E) (t : ℝ) : Prop :=
  σ.S t x ∉ Q → 0 < infDist (σ.S t x) Q ∧ ∀ v : ∀ h, σ.X h, σ.Converges v x →
    Tendsto (fun h => infDist (σ.sol h (v h) t) Q) σ.l (𝓝 (infDist (σ.S t x) Q))

end Metric

section Normed

variable [SeminormedAddCommGroup E] (σ : Scheme.{u} E κ)

/-- `σ` has residuals at most its errors from `x`: `dist(ιₕ e^{tLₕ} v, K) ≤ ‖S(t) x - ιₕ e^{tLₕ} v‖`
for every discrete state `v` and `t ≥ 0`. -/
abbrev ResidualBounded (x : E) : Prop :=
  ∀ h, ∀ v : σ.X h, ∀ t : ℝ, 0 ≤ t → σ.residual (σ.sol h v t) ≤ ‖σ.S t x - σ.sol h v t‖

end Normed

end Scheme

end Feec.Evolution
