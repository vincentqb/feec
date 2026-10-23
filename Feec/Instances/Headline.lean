-- leantex: show = prose, glossary = where, decls = headline_wellPosed, headline_propagates_iff, headline_converges_core, headline_converges, headline_rate, headline_residual_reducing, headline_residual_leaves, headline_residual_not_reducing, headline_residual_not_reducing_symm, headline_residual_not_reducing_graded
module

public import Feec.HilbertComplex.Approximation.ApproxFEEC

/-!
# The crowning theorem, stated in full

`approxFEEC` ([HolstStern2012], Thm 3.9, Thm 3.10 for the elliptic analogues;
[QuennevilleBelair2015], Thms 4.6, 4.14, Prop. 4.17) states its conclusion as the abbreviation
`ApproxFEEC.Verdict`. This module restates it with the abbreviation unfolded, so that its full
statement can be read and typeset (e.g. by `leantex` with `show = prose`); the proof is
`approxFEEC` itself.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

section Helpers

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxFEEC.{u} H κ)

/-- The state at time `t` of the solution of `H` from `x`, `e^{tL} x`. -/
def exact (H : HilbertComplex 𝕜 c W) (x : PiLp 2 W) (t : ℝ) : PiLp 2 W :=
  H.waveGroup.S t x

/-- The distance of `y` to the constraint of `F`, `dist(y, K)`. -/
def ApproxFEEC.residual (y : PiLp 2 W) : ℝ := infDist y (F.K : Set (PiLp 2 W))

/-- `v` converges to `x` through the reading maps of `F`, `ιₕ vₕ → x`. -/
def ApproxFEEC.Converges (v : ∀ h, F.X h) (x : PiLp 2 W) : Prop :=
  Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x)

/-- `F` has its constraint in the closure of its smooth part, `K ⊆ closure (D(L) ∩ K)`. -/
def ApproxFEEC.SmoothDense : Prop :=
  ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)

/-- `F` has its constraint invariant under the reversal by `p`, `R_p K ⊆ K`. -/
def ApproxFEEC.ReversalInvariant (p : ι → Bool) : Prop := ∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K

variable {F} in
/-- `Z` detects the departure of `x` at time `t`: from initial data converging to `x`, the
residuals at `t` tend to that of the exact solution and eventually exceed half of it. -/
def ApproxFEEC.Core.Detects (Z : F.Core) (x : PiLp 2 W) (t : ℝ) : Prop :=
  x ∈ Z.Data.topologicalClosure → ∀ v : ∀ h, F.X h, F.Converges v x →
    Tendsto (fun h => F.residual (F.sol h (v h) t)) F.l (𝓝 (F.residual (H.exact x t))) ∧
    ∀ᶠ h in F.l, F.residual (H.exact x t) / 2 < F.residual (F.sol h (v h) t)

/-- `p` alternates along `c`, `p j ≠ p i` whenever `c.Rel i j`. -/
def Alternates (c : ComplexShape ι) (p : ι → Bool) : Prop := ∀ i j, c.Rel i j → p j ≠ p i

end Helpers

open ApproxFEEC

/-- The propositional assumptions on the spaces, as data: every `W i` is complete and its real
scalars are those of `𝕜`. A binder of this class hides in a typeset statement, as one of
`RCLike 𝕜` does, where a propositional binder the rest refers to cannot be said. -/
class Spaces (𝕜 : Type*) [RCLike 𝕜] {ι : Type*} (W : ι → Type*) [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, NormedSpace ℝ (W i)] : Type where
  complete : ∀ i, CompleteSpace (W i)
  isScalarTower : ∀ i, IsScalarTower ℝ 𝕜 (W i)

attribute [local instance] Spaces.complete Spaces.isScalarTower

/- The type-class assumptions are implicit binders here, not instance ones, so a typeset
statement hides them as it hides `𝕜`, `W` and `H`; they are still local instances in each
statement and proof. -/
variable {𝕜 : Type*} {_ : RCLike 𝕜} {ι : Type*} {_ : Fintype ι} {c : ComplexShape ι}
  {W : ι → Type*} {_ : ∀ i, NormedAddCommGroup (W i)} {_ : ∀ i, InnerProductSpace 𝕜 (W i)}
  {_ : ∀ i, NormedSpace ℝ (W i)} {_ : Spaces 𝕜 W}
  {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxFEEC.{u} H κ)

/-- **Well-posedness.** Every datum of `D(L)` has a unique classical, strong and weak solution, which conserves the norm (conclusion 1 of `approxFEEC`). -/
theorem headline_wellPosed (Z : F.Core) :
    (∀ x ∈ H.wave.domain, ∀ T : ℝ,
      Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 (H.exact x) ∧
      (∀ U, U 0 = x → Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U →
        EqOn U (H.exact x) (Icc 0 T)) ∧
      (∀ U, U 0 = x → HodgeWave.IsWeakSolution H (Icc 0 T) 0 U →
        EqOn U (H.exact x) (Icc 0 T)) ∧
      ∀ t, ‖H.exact x t‖ = ‖x‖) :=
  (approxFEEC F Z).1

/-- **Propagation.** The flow preserves the constraint if and only if `K` reduces `L` (conclusion 2 of `approxFEEC`). -/
theorem headline_propagates_iff (Z : F.Core) :
    (H.wave.IsReducing F.K ↔ ∀ t, ∀ x ∈ F.K, H.exact x t ∈ F.K) :=
  (approxFEEC F Z).2.1

/-- **Convergence on the core**, uniformly on `[0, T]` (conclusion 3 of `approxFEEC`). -/
theorem headline_converges_core (Z : F.Core) :
    (∀ T : ℝ, ∀ x ∈ Z.Data, TendstoUniformlyOn
      (fun h t => F.sol h ((Z.cmp T).p x h 0) t) (H.exact x) F.l (Icc 0 T)) :=
  (approxFEEC F Z).2.2.1

/-- **Convergence on the closure of the core**, from every initial family converging to the datum; one exists (conclusion 4 of `approxFEEC`). -/
theorem headline_converges (Z : F.Core) :
    (∀ T : ℝ, ∀ x ∈ Z.Data.topologicalClosure,
      Tendsto (fun h => F.incl h (F.proj h x)) F.l (𝓝 x) ∧
      ∀ v : ∀ h, F.X h, F.Converges v x →
        TendstoUniformlyOn (fun h t => F.sol h (v h) t) (H.exact x) F.l
          (Icc 0 T)) :=
  (approxFEEC F Z).2.2.2.1

/-- **Rate.** The error is bounded by best approximation, consistency and initial mismatch (conclusion 5 of `approxFEEC`). -/
theorem headline_rate (Z : F.Core) :
    (∀ (T : ℝ) (R : F.RateClass T), ∀ x ∈ R.Data, ∀ h, ∀ v : F.X h, ∀ t ∈ Icc 0 T,
      ‖H.exact x t - F.sol h v t‖ ≤
        (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) +
          ‖F.incl h‖ * ‖R.p x h 0 - v‖) :=
  (approxFEEC F Z).2.2.2.2.1

/-- **Reducing constraint.** The residual is bounded by the error and tends to `0` (conclusion 6 of `approxFEEC`). -/
theorem headline_residual_reducing (Z : F.Core) :
    (H.wave.IsReducing F.K → ∀ x ∈ F.K,
      (∀ h (v : F.X h) t, F.residual (F.sol h v t) ≤
        ‖H.exact x t - F.sol h v t‖) ∧
      (x ∈ Z.Data.topologicalClosure → ∀ T : ℝ, ∀ v : ∀ h, F.X h,
        F.Converges v x →
        TendstoUniformlyOn (fun h t => F.residual (F.sol h (v h) t))
          (fun _ => 0) F.l (Icc 0 T))) :=
  (approxFEEC F Z).2.2.2.2.2.1

/-- **A solution leaving a closed set.** The residuals tend to its positive distance (conclusion 7 of `approxFEEC`). -/
theorem headline_residual_leaves (Z : F.Core) :
    (∀ Q : Set (PiLp 2 W), IsClosed Q → Q.Nonempty → ∀ x ∈ Z.Data.topologicalClosure,
      ∀ v : ∀ h, F.X h, F.Converges v x → ∀ t, 0 ≤ t →
      H.exact x t ∉ Q → 0 < infDist (H.exact x t) Q ∧
        Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l
          (𝓝 (infDist (H.exact x t) Q))) :=
  (approxFEEC F Z).2.2.2.2.2.2.1

/-- **Non-reducing constraint.** A datum of `K` or `Kᗮ` leaves it, with residuals of positive limit when the core is dense (conclusion 8 of `approxFEEC`). -/
theorem headline_residual_not_reducing (Z : F.Core) :
    (¬ H.wave.IsReducing F.K → ∀ T : ℝ, 0 < T →
      ∃ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
        H.exact x t ∉ Q ∧ 0 < infDist (H.exact x t) Q ∧
        (Dense (Z.Data : Set (PiLp 2 W)) → ∀ v : ∀ h, F.X h,
          F.Converges v x →
          Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l
            (𝓝 (infDist (H.exact x t) Q)))) :=
  (approxFEEC F Z).2.2.2.2.2.2.2.1

/-- **Non-reducing constraint, smooth data.** A datum of `D(L) ∩ K` leaves `K` for some `t ∈ [-T, T]` (conclusion 9 of `approxFEEC`). -/
theorem headline_residual_not_reducing_symm (Z : F.Core) :
    (¬ H.wave.IsReducing F.K →
      F.SmoothDense → ∀ T : ℝ, 0 < T →
      ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc (-T) T,
        H.exact x t ∉ F.K ∧ 0 < F.residual (H.exact x t)) :=
  (approxFEEC F Z).2.2.2.2.2.2.2.2.1

/-- **Non-reducing constraint, graded complex.** A datum of `D(L) ∩ K` leaves `K` forward in time, with residuals of positive limit (conclusion 10 of `approxFEEC`). -/
theorem headline_residual_not_reducing_graded (Z : F.Core) :
    (∀ p : ι → Bool, Alternates c p → F.ReversalInvariant p → F.SmoothDense →
      ¬ H.wave.IsReducing F.K → ∀ T : ℝ, 0 < T →
      ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc 0 T,
        H.exact x t ∉ F.K ∧ 0 < F.residual (H.exact x t) ∧ Z.Detects x t) :=
  (approxFEEC F Z).2.2.2.2.2.2.2.2.2

end Feec.HilbertComplex
