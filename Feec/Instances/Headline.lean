-- leantex: show = prose, glossary = where, decls = headline_dissip, headline, phrase.Feec.HilbertComplex.Headline.Converges = "#2 converges to #3 through the reading maps of #1", phrase.Feec.HilbertComplex.Headline.ConvergesFrom = "#1 converges from #2", phrase.Feec.HilbertComplex.Headline.Keeps = "#1 keeps #2 at the times in #3", phrase.Feec.HilbertComplex.Headline.Exits = "#1 takes some datum of #2 out of #3 at a time in #4", phrase.Feec.HilbertComplex.Headline.SmoothDense = "#1 has its constraint in the closure of its part in #2", phrase.Feec.HilbertComplex.Headline.ResidualBounded = "#1 has residuals at most its errors from #2", phrase.Feec.HilbertComplex.Headline.ResidualVanishes = "#1 has residuals tending to zero from #2", phrase.Feec.HilbertComplex.Headline.Detects = "#1 detects the departure of #3 from #2 at time #4", phrase.Feec.HilbertComplex.Headline.IsUniqueSolution = "#4 is the unique solution of #1 from #3 up to time #2", phrase.Feec.HilbertComplex.Headline.Bounds = "#1 bounds the error by best approximation plus consistency plus initial mismatch", phrase.Feec.HilbertComplex.Headline.Alternates = "#2 alternates along #1", phrase.Feec.HilbertComplex.Headline.ReversalInvariant = "#1 has its constraint invariant under the reversal by #2", phrase.Feec.HilbertComplex.DissipFEEC.Verdict = "#1 satisfies the dissipative FEEC theorem with the core #2", phrase.Feec.HilbertComplex.ApproxFEEC.toScheme = "the wave scheme of #1", phrase.Feec.HilbertComplex.DissipFEEC.toScheme = "the scheme of #1", phrase.Feec.HilbertComplex.ApproxFEEC.toDissipFEEC = "the forward reading of #1", phrase.Feec.HilbertComplex.ApproxFEEC.Core.toDissip = "the forward core of #1", phrase.Feec.Evolution.Scheme.K = "the constraint of #1", phrase.SetLike.coe = "the set #1", phrase.Inter.inter = "the part of #2 in #1", phrase.Set.Icc = "the interval from #1 to #2", phrase.Set.Ici = "the half-line from #1", phrase.Set.univ = "the whole line", phrase.AntitoneOn = "#1 is antitone on #2"
module

public import Feec.HilbertComplex.Approximation.ApproxFEEC

/-!
# The crowning theorem, stated in full

`approxFEEC` ([HolstStern2012], Thm 3.9, Thm 3.10 for the elliptic analogues;
[QuennevilleBelair2015], Thms 4.6, 4.14, Prop. 4.17) states its conclusion as the abbreviation
`ApproxFEEC.Verdict`: the verdict `DissipFEEC.Verdict` of the dissipative FEEC theorem
`dissipFEEC` for the forward-time reading `ApproxFEEC.toDissipFEEC`, and the conclusions that use
both time directions. Both are conjunctions of the predicates of `Feec.Evolution.Scheme`. This
module states them as two theorems, `headline_dissip` (the dissipative verdict, over an arbitrary
Hilbert space) and `headline` (the approximating verdict, citing the dissipative one for its
forward-time reading, which keeps each statement within the size `leantex` typesets), so that
the full statement can be read and typeset (by `leantex` with `show = prose`, each predicate
explained after it); the proofs are `dissipFEEC` and `approxFEEC` themselves.

`leantex` takes a constant's words from the `phrase.` entries of the directive on the first line,
and explains a predicate only where the typeset file declares it, so the module restates, in the
namespace `Feec.HilbertComplex.Headline`, the predicates of `Feec.Evolution.Scheme`, the rate
clause `DissipFEEC.RateClass.Bounds` and the grading predicates `Alternates`,
`ApproxFEEC.ReversalInvariant`, with the same definitions. These restatements are checked: the
two theorems are proved by `dissipFEEC` and `approxFEEC` through their definitions, so each is
definitionally the library's.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

/-- The propositional assumptions on the spaces, as data: every `W i` is complete and its real
scalars are those of `𝕜`. A binder of this class hides in a typeset statement, as one of
`RCLike 𝕜` does, where a propositional binder the rest refers to cannot be said. -/
class Spaces (𝕜 : Type*) [RCLike 𝕜] {ι : Type*} (W : ι → Type*) [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, NormedSpace ℝ (W i)] : Type where
  complete : ∀ i, CompleteSpace (W i)
  isScalarTower : ∀ i, IsScalarTower ℝ 𝕜 (W i)

attribute [local instance] Spaces.complete Spaces.isScalarTower

namespace Headline

open Evolution (Scheme)

/-! ### The vocabulary, restated for the glossary

The type-class assumptions of these definitions are implicit binders, not instance ones, so that
`leantex` can say their definitions; each use passes them as `inferInstance`. -/

section Vocabulary

variable {E κ : Type*}

/-- `v` converges to `x` through the reading maps of `σ`, `ιₕ vₕ → x`. -/
abbrev Converges {iE : TopologicalSpace E} (σ : Scheme.{u} E κ) (v : ∀ h, σ.X h) (x : E) :
    Prop :=
  Tendsto (fun h => σ.incl h (v h)) σ.l (𝓝 x)

/-- `σ` converges from `x`: the discrete states of `x` converge to `x`, and from every family
converging to `x` the discrete solutions converge to the exact one uniformly on every `[0, T]`. -/
abbrev ConvergesFrom {iE : UniformSpace E} (σ : Scheme.{u} E κ) (x : E) : Prop :=
  Converges (iE := inferInstance) σ (fun h => σ.proj h x) x ∧
    ∀ v : ∀ h, σ.X h, Converges (iE := inferInstance) σ v x → ∀ T : ℝ,
      TendstoUniformlyOn (fun h t => σ.sol h (v h) t) (fun t => σ.S t x) σ.l (Icc 0 T)

/-- `σ` keeps `Q` at the times of `I`, `S(t) Q ⊆ Q` for every `t ∈ I`. -/
abbrev Keeps (σ : Scheme.{u} E κ) (Q : Set E) (I : Set ℝ) : Prop := ∀ t ∈ I, ∀ x ∈ Q, σ.S t x ∈ Q

/-- `σ` takes some datum of `D` out of `Q` at a time of `I`: `S(t) x ∉ Q` for some `x ∈ D` and
`t ∈ I`. -/
abbrev Exits (σ : Scheme.{u} E κ) (D Q : Set E) (I : Set ℝ) : Prop := ∃ x ∈ D, ∃ t ∈ I, σ.S t x ∉ Q

/-- `σ` has its constraint in the closure of its part in `D`, `K ⊆ closure (D ∩ K)`. -/
abbrev SmoothDense {iE : TopologicalSpace E} (σ : Scheme.{u} E κ) (D : Set E) : Prop :=
  ∀ k ∈ σ.K, k ∈ closure (D ∩ σ.K)

/-- `σ` has residuals at most its errors from `x`: `dist(ιₕ e^{tLₕ} v, K) ≤ ‖S(t) x - ιₕ e^{tLₕ} v‖`
for every discrete state `v` and `t ≥ 0`. -/
abbrev ResidualBounded {iE : SeminormedAddCommGroup E} (σ : Scheme.{u} E κ) (x : E) : Prop :=
  ∀ h, ∀ v : σ.X h, ∀ t : ℝ, 0 ≤ t → infDist (σ.sol h v t) σ.K ≤ ‖σ.S t x - σ.sol h v t‖

/-- `σ` has residuals tending to zero from `x`: from every family converging to `x`, the
residuals of the discrete solutions tend to `0` uniformly on every `[0, T]`. -/
abbrev ResidualVanishes {iE : PseudoMetricSpace E} (σ : Scheme.{u} E κ) (x : E) : Prop :=
  ∀ v : ∀ h, σ.X h, Converges (iE := inferInstance) σ v x → ∀ T : ℝ,
    TendstoUniformlyOn (fun h t => infDist (σ.sol h (v h) t) σ.K) (fun _ => 0) σ.l (Icc 0 T)

/-- `σ` detects the departure of `x` from `Q` at time `t`: if `S(t) x ∉ Q`, its distance to `Q`
is positive and, from every family converging to `x`, the distances to `Q` of the discrete
solutions at time `t` tend to it. -/
abbrev Detects {iE : PseudoMetricSpace E} (σ : Scheme.{u} E κ) (Q : Set E) (x : E) (t : ℝ) :
    Prop :=
  σ.S t x ∉ Q → 0 < infDist (σ.S t x) Q ∧ ∀ v : ∀ h, σ.X h, Converges (iE := inferInstance) σ v x →
    Tendsto (fun h => infDist (σ.sol h (v h) t) Q) σ.l (𝓝 (infDist (σ.S t x) Q))

end Vocabulary

/-- The propositional assumptions on a space, as data: `E` is complete and its real scalars are
those of `𝕜` (a binder of this class hides in a typeset statement). -/
class Space (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedSpace ℝ E] : Type where
  complete : CompleteSpace E
  isScalarTower : IsScalarTower ℝ 𝕜 E

/-- An m-dissipative operator, as data (a binder of this class hides in a typeset statement). -/
class MDissipative {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Type where
  isMDissipative : A.IsMDissipative

attribute [local instance] Space.complete Space.isScalarTower

section Dissip

variable {𝕜 : Type*} {i𝕜 : RCLike 𝕜} {E : Type*} {iE : NormedAddCommGroup E}
  {iI : InnerProductSpace 𝕜 E} {iR : NormedSpace ℝ E} {sp : Space 𝕜 E} {A : E →ₗ.[𝕜] E}
  {m : MDissipative A} {κ : Type*}

/-- `u` is a classical solution of `A` up to time `T` and the only strong one from `x`:
`u` is a classical solution of `u' = A u` on `[0, T]`, and every strong solution `U` there with
`U 0 = x` is `u`. -/
abbrev IsUniqueSolution (A : E →ₗ.[𝕜] E) (T : ℝ) (x : E) (u : ℝ → E) : Prop :=
  Evolution.IsClassicalSolution A (Icc 0 T) 0 u ∧
    ∀ U : ℝ → E, U 0 = x → Evolution.IsStrongSolution A (Icc 0 T) 0 U → EqOn U u (Icc 0 T)

/-- `R` bounds the error by best approximation plus consistency plus initial mismatch:
`‖S(t) x - ιₕ e^{tLₕ} v‖ ≤ (C + ‖ιₕ‖ C' t) hᵅ ‖x‖_c + ‖ιₕ‖ ‖pₕ(0) - v‖` for every datum `x` of
`R`, discrete state `v` and `t ∈ [0, T]`. -/
abbrev Bounds {F : DissipFEEC.{u} m.isMDissipative κ} {T : ℝ} (R : F.RateClass T) : Prop :=
  ∀ x ∈ R.Data, ∀ h, ∀ v : F.X h, ∀ t ∈ Icc 0 T,
    ‖F.toScheme.S t x - F.sol h v t‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * ‖R.p x h 0 - v‖

end Dissip

section Grading

variable {𝕜 : Type*} {i𝕜 : RCLike 𝕜} {ι : Type*} {iι : Fintype ι} {W : ι → Type*}
  {iW : ∀ i, NormedAddCommGroup (W i)} {iI : ∀ i, InnerProductSpace 𝕜 (W i)}
  {iN : ∀ i, NormedSpace ℝ (W i)} {iS : Spaces 𝕜 W} {c : ComplexShape ι}
  {H : HilbertComplex 𝕜 c W} {κ : Type*}

/-- `p` alternates along `c`, `p j ≠ p i` whenever `c.Rel i j`. -/
abbrev Alternates (c : ComplexShape ι) (p : ι → Bool) : Prop := ∀ i j, c.Rel i j → p j ≠ p i

/-- `F` has its constraint invariant under the reversal by `p`, `R_p K ⊆ K`. -/
abbrev ReversalInvariant (F : ApproxFEEC.{u} H κ) (p : ι → Bool) : Prop :=
  ∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K

end Grading

end Headline

section Dissip

open Headline

variable {𝕜 : Type*} {i𝕜 : RCLike 𝕜} {E : Type*} {iE : NormedAddCommGroup E}
  {iI : InnerProductSpace 𝕜 E} {iR : NormedSpace ℝ E} {sp : Space 𝕜 E} {A : E →ₗ.[𝕜] E}
  {m : MDissipative A} {κ : Type*}

attribute [local instance] Space.complete Space.isScalarTower

/-- **The dissipative FEEC theorem.** For a dissipative FEEC discretization `F` of `ξ' = A ξ`
with `A` m-dissipative and an orbit-consistent core `Z`: well-posedness and energy, the
propagation criteria, convergence from every datum of the closure of the core, rates, the
residual of an invariant constraint, detection of departures from closed sets, and departures
from a non-invariant constraint. This is `DissipFEEC.Verdict`. [Pazy1983], §1.4 (Thm 4.3), §3.4 -/
theorem headline_dissip (F : DissipFEEC.{u} m.isMDissipative κ) (Z : F.Core) :
    (∀ x : A.domain, ∀ T : ℝ,
      IsUniqueSolution (iR := iR) A T x (fun t => F.toScheme.S t x) ∧
      AntitoneOn (fun t => ‖F.toScheme.S t x‖) (Ici 0) ∧
      ∀ t, 0 ≤ t → ‖F.toScheme.S t x‖ ^ 2 = ‖(x : E)‖ ^ 2 +
        ∫ s in (0 : ℝ)..t, 2 * RCLike.re ⟪F.toScheme.S s (A x), F.toScheme.S s x⟫_𝕜) ∧
    ((Keeps F.toScheme F.toScheme.K (Ici 0) ↔
      ∀ μ : ℝ, 0 < μ → ∀ y ∈ F.K, Operator.resolvent A (μ : 𝕜) y ∈ F.K) ∧
    (Keeps F.toScheme F.toScheme.K (Ici 0) ↔
      ∃ μ : ℝ, 0 < μ ∧ ∀ y ∈ F.K, ∃ u : A.domain, (u : E) ∈ F.K ∧ (μ : 𝕜) • (u : E) - A u = y) ∧
    (A.IsReducing F.K ↔
      Keeps F.toScheme F.toScheme.K (Ici 0) ∧ Keeps F.toScheme F.Kᗮ (Ici 0))) ∧
    (∀ x ∈ Z.Data.topologicalClosure, ConvergesFrom (iE := inferInstance) F.toScheme x) ∧
    (∀ (T : ℝ) (R : F.RateClass T), Bounds (iR := iR) (sp := sp) (m := m) R) ∧
    (Keeps F.toScheme F.toScheme.K (Ici 0) → ∀ x ∈ F.toScheme.K,
      ResidualBounded (iE := inferInstance) F.toScheme x ∧
      (x ∈ Z.Data.topologicalClosure → ResidualVanishes (iE := inferInstance) F.toScheme x)) ∧
    (∀ Q : Set E, IsClosed Q → Q.Nonempty → ∀ x ∈ Z.Data.topologicalClosure, ∀ t, 0 ≤ t →
      Detects (iE := inferInstance) F.toScheme Q x t) ∧
    (¬ Keeps F.toScheme F.toScheme.K (Ici 0) → ∀ T : ℝ, 0 < T →
      Exits F.toScheme F.toScheme.K F.toScheme.K (Icc 0 T) ∧
      (SmoothDense (iE := inferInstance) F.toScheme A.domain →
        Exits F.toScheme ((A.domain : Set E) ∩ F.toScheme.K) F.toScheme.K (Icc 0 T))) :=
  dissipFEEC F Z

end Dissip

open ApproxFEEC Headline

/- The type-class assumptions are implicit binders here, not instance ones, so a typeset
statement hides them as it hides `𝕜`, `W` and `H`; they are still local instances in the
statement and the proof. -/
variable {𝕜 : Type*} {_ : RCLike 𝕜} {ι : Type*} {_ : Fintype ι} {c : ComplexShape ι}
  {W : ι → Type*} {_ : ∀ i, NormedAddCommGroup (W i)} {_ : ∀ i, InnerProductSpace 𝕜 (W i)}
  {_ : ∀ i, NormedSpace ℝ (W i)} {iS : Spaces 𝕜 W}
  {H : HilbertComplex 𝕜 c W} {κ : Type*}

/-- **The approximating FEEC theorem.** For an approximating FEEC discretization `F` of the Hodge
wave equation of `H` and an orbit-consistent core `Z`: the forward-time reading `F.toDissipFEEC`
satisfies the dissipative FEEC theorem with the core `Z.toDissip`, and the conclusions that use
both time directions hold for the wave group: unique weak solutions and conservation of the norm,
propagation iff reducing, departures from a non-reducing constraint or its orthogonal complement,
from `D(L) ∩ K` in one of the two time directions, and forward in time on a graded complex. This
is `ApproxFEEC.Verdict`. [QuennevilleBelair2015], Thms 4.6, 4.7, Prop. 4.17; [HolstStern2012],
Thm 3.9, Thm 3.10 (elliptic analogues) -/
theorem headline (F : ApproxFEEC.{u} H κ) (Z : F.Core) :
    F.toDissipFEEC.Verdict Z.toDissip ∧
    (∀ x ∈ H.wave.domain, ∀ T : ℝ,
      (∀ U, U 0 = x → HodgeWave.IsWeakSolution H (Icc 0 T) 0 U →
        EqOn U (fun t => F.toScheme.S t x) (Icc 0 T)) ∧
      ∀ t, ‖F.toScheme.S t x‖ = ‖x‖) ∧
    (H.wave.IsReducing F.K ↔ Keeps F.toScheme F.toScheme.K univ) ∧
    (¬ H.wave.IsReducing F.K → ∀ T : ℝ, 0 < T →
      Exits F.toScheme F.toScheme.K F.toScheme.K (Icc 0 T) ∨
        Exits F.toScheme F.Kᗮ F.Kᗮ (Icc 0 T)) ∧
    (¬ H.wave.IsReducing F.K → SmoothDense (iE := inferInstance) F.toScheme H.wave.domain →
      ∀ T : ℝ, 0 < T →
      Exits F.toScheme ((H.wave.domain : Set (PiLp 2 W)) ∩ F.toScheme.K) F.toScheme.K
        (Icc (-T) T)) ∧
    (∀ p : ι → Bool, Headline.Alternates c p →
      Headline.ReversalInvariant (iN := inferInstance) (iS := iS) F p →
      SmoothDense (iE := inferInstance) F.toScheme H.wave.domain → ¬ H.wave.IsReducing F.K →
      ∀ T : ℝ, 0 < T →
      Exits F.toScheme ((H.wave.domain : Set (PiLp 2 W)) ∩ F.toScheme.K) F.toScheme.K
        (Icc 0 T)) :=
  approxFEEC F Z

end Feec.HilbertComplex
