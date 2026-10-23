-- leantex: show = prose
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

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxFEEC.{u} H κ)

open ApproxFEEC


/-- **1. 1. well-posedness (constrainedFEEC_wellPosed)** (conclusion 1 of `approxFEEC`). -/
theorem approxFEEC_wellPosed (Z : F.Core) :
    (∀ x ∈ H.wave.domain, ∀ T : ℝ,
      Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 (fun t => H.waveGroup.S t x) ∧
      (∀ U, U 0 = x → Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      (∀ U, U 0 = x → HodgeWave.IsWeakSolution H (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      ∀ t, ‖H.waveGroup.S t x‖ = ‖x‖) :=
  (approxFEEC F Z).1

/-- **2. 2. propagation iff reducing** (conclusion 2 of `approxFEEC`). -/
theorem headline_propagates_iff (Z : F.Core) :
    (H.wave.IsReducing F.K ↔ ∀ t, ∀ x ∈ F.K, H.waveGroup.S t x ∈ F.K) :=
  (approxFEEC F Z).2.1

/-- **3. 3a. convergence on the core** (conclusion 3 of `approxFEEC`). -/
theorem headline_converges_core (Z : F.Core) :
    (∀ T : ℝ, ∀ x ∈ Z.Data, TendstoUniformlyOn
      (fun h t => F.sol h ((Z.cmp T).p x h 0) t) (fun t => H.waveGroup.S t x) F.l (Icc 0 T)) :=
  (approxFEEC F Z).2.2.1

/-- **4. 3b. convergence on the closure of the core, every convergent initial family; one exists** (conclusion 4 of `approxFEEC`). -/
theorem headline_converges (Z : F.Core) :
    (∀ T : ℝ, ∀ x ∈ Z.Data.topologicalClosure,
      Tendsto (fun h => F.incl h (F.proj h x)) F.l (𝓝 x) ∧
      ∀ v : ∀ h, F.X h, Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => F.sol h (v h) t) (fun t => H.waveGroup.S t x) F.l
          (Icc 0 T)) :=
  (approxFEEC F Z).2.2.2.1

/-- **5. 3c. rates: best approximation + consistency (+ initial mismatch)** (conclusion 5 of `approxFEEC`). -/
theorem headline_rate (Z : F.Core) :
    (∀ (T : ℝ) (R : F.RateClass T), ∀ x ∈ R.Data, ∀ h, ∀ v : F.X h, ∀ t ∈ Icc 0 T,
      ‖H.waveGroup.S t x - F.sol h v t‖ ≤
        (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) +
          ‖F.incl h‖ * ‖R.p x h 0 - v‖) :=
  (approxFEEC F Z).2.2.2.2.1

/-- **6. 4a. reducing constraint: residual through ιₕ bounded by the error, tends to 0** (conclusion 6 of `approxFEEC`). -/
theorem headline_residual_reducing (Z : F.Core) :
    (H.wave.IsReducing F.K → ∀ x ∈ F.K,
      (∀ h (v : F.X h) t, infDist (F.sol h v t) (F.K : Set (PiLp 2 W)) ≤
        ‖H.waveGroup.S t x - F.sol h v t‖) ∧
      (x ∈ Z.Data.topologicalClosure → ∀ T : ℝ, ∀ v : ∀ h, F.X h,
        Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => infDist (F.sol h (v h) t) (F.K : Set (PiLp 2 W)))
          (fun _ => 0) F.l (Icc 0 T))) :=
  (approxFEEC F Z).2.2.2.2.2.1

/-- **7. 4b. per datum: a solution leaving Q has residual tending to dist(e^{tL}x, Q) > 0** (conclusion 7 of `approxFEEC`). -/
theorem headline_residual_leaves (Z : F.Core) :
    (∀ Q : Set (PiLp 2 W), IsClosed Q → Q.Nonempty → ∀ x ∈ Z.Data.topologicalClosure,
      ∀ v : ∀ h, F.X h, Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) → ∀ t, 0 ≤ t →
      H.waveGroup.S t x ∉ Q → 0 < infDist (H.waveGroup.S t x) Q ∧
        Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l
          (𝓝 (infDist (H.waveGroup.S t x) Q))) :=
  (approxFEEC F Z).2.2.2.2.2.2.1

/-- **8. 4b. a non-reducing constraint is left by data of K or Kᗮ; with a dense core, the residuals of every convergent discretization of that datum have a positive limit** (conclusion 8 of `approxFEEC`). -/
theorem headline_residual_not_reducing (Z : F.Core) :
    (¬ H.wave.IsReducing F.K → ∀ T : ℝ, 0 < T →
      ∃ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
        H.waveGroup.S t x ∉ Q ∧ 0 < infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)) ∧
        (Dense (Z.Data : Set (PiLp 2 W)) → ∀ v : ∀ h, F.X h,
          Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
          Tendsto (fun h => infDist (F.sol h (v h) t) (Q : Set (PiLp 2 W))) F.l
            (𝓝 (infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)))))) :=
  (approxFEEC F Z).2.2.2.2.2.2.2.1

/-- **9. 4c. with D(L) ∩ K dense in K: a datum of D(L) ∩ K leaves K for some t ∈ [-T, T]** (conclusion 9 of `approxFEEC`). -/
theorem headline_residual_not_reducing_symm (Z : F.Core) :
    (¬ H.wave.IsReducing F.K →
      (∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) → ∀ T : ℝ, 0 < T →
      ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc (-T) T,
        H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W))) :=
  (approxFEEC F Z).2.2.2.2.2.2.2.2.1

/-- **10. 4c. graded complex, R-invariant K, D(L) ∩ K dense in K: a datum of D(L) ∩ K leaves K forward in time, with residuals tending to a positive limit** (conclusion 10 of `approxFEEC`). -/
theorem headline_residual_not_reducing_graded (Z : F.Core) :
    (∀ p : ι → Bool, (∀ i j, c.Rel i j → p j ≠ p i) → (∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K) →
      (∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) →
      ¬ H.wave.IsReducing F.K → ∀ T : ℝ, 0 < T →
      ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc 0 T,
        H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) ∧
        ((x : PiLp 2 W) ∈ Z.Data.topologicalClosure → ∀ v : ∀ h, F.X h,
          Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
          Tendsto (fun h => infDist (F.sol h (v h) t) (F.K : Set (PiLp 2 W))) F.l
            (𝓝 (infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)))) ∧
          ∀ᶠ h in F.l, infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) / 2 <
            infDist (F.sol h (v h) t) (F.K : Set (PiLp 2 W)))) :=
  (approxFEEC F Z).2.2.2.2.2.2.2.2.2

end Feec.HilbertComplex
