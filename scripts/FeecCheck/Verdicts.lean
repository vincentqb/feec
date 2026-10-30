module

public import Feec.HilbertComplex.Approximation.ApproxFEEC
public import Feec.HilbertComplex.Approximation.ApproxConforming

/-!
# Regression tests: nothing is lost from the verdicts

The verdicts `DissipFEEC.Verdict`, `SkewFEEC.Verdict` and `ApproxFEEC.Verdict` are structures
whose fields are the conclusions of `dissipFEEC`, `skewFEEC` and `approxFEEC`, each extending the
one below and stated at the most general layer where it is provable; `ConstrainedFEEC.Verdict` is
the structure of the conclusions of `constrainedFEEC` (and `constrainedFEEC_of_approxFEEC`).
Their earlier shape was one conjunction per theorem, with the flow of each theorem written out
(the Lumer–Phillips semigroup `hA.semigroup.S` and the wave group `H.waveGroup.S`), convergence on
the core from the comparison initial values, the residual bound for all `t` and the departures
with their positive residual limits. The theorems below derive those conjunctions, verbatim, from
the new verdicts (`constrained_old`: the eight-part conjunction that `constrainedFEEC` stated before
`ConstrainedFEEC.Verdict`).

Two things did change besides the shape. The m-dissipativity of `A` is now a field
`F.isMDissipative` of `F` rather than a parameter of its type: `hA` below is any proof of it, and
`hA.semigroup.S` is `F.S` by proof irrelevance. And the binder types `F.Core` and `F.RateClass T`
of an approximating discretization are now those of `DissipFEEC`, whose approximation clauses are
stated for the semigroup `F.S` rather than for the wave group; the two agree on `[0, T]`
(`ApproxFEEC.S_eq_waveGroup`), the only times these clauses mention.

This file is part of the `FeecCheck` library, not of `Feec`: it is compiled by
`lake build FeecCheck` (and so by `lake exe feec-gate`), not by a plain `lake build`, and fails
that build if a conclusion is dropped.
-/

public section

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

universe u

namespace FeecCheck.Verdicts

open Feec Feec.HilbertComplex

section Dissip

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  {A : E →ₗ.[𝕜] E} {hA : A.IsMDissipative} {κ : Type*} {F : DissipFEEC.{u} A κ}

/-- The conclusion of `dissipFEEC` in its earlier shape, from `DissipFEEC.Verdict`. -/
theorem dissip_old {Z : F.Core} (V : F.Verdict Z) :
    -- 1. well-posedness and energy (Lumer–Phillips)
    (∀ x : A.domain, ∀ T : ℝ,
      Evolution.IsClassicalSolution A (Icc 0 T) 0 (fun t => hA.semigroup.S t x) ∧
      (∀ U, U 0 = (x : E) → Evolution.IsStrongSolution A (Icc 0 T) 0 U →
        EqOn U (fun t => hA.semigroup.S t x) (Icc 0 T)) ∧
      (∀ s t, 0 ≤ s → s ≤ t → ‖hA.semigroup.S t x‖ ≤ ‖hA.semigroup.S s x‖) ∧
      ∀ t, 0 ≤ t → ‖hA.semigroup.S t x‖ ^ 2 = ‖(x : E)‖ ^ 2 +
        ∫ s in (0 : ℝ)..t, 2 * RCLike.re ⟪hA.semigroup.S s (A x), hA.semigroup.S s x⟫_𝕜) ∧
    -- 2. propagation
    (((∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) ↔
      ∀ μ : ℝ, 0 < μ → ∀ y ∈ F.K, Operator.resolvent A (μ : 𝕜) y ∈ F.K) ∧
    ((∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) ↔
      ∃ μ : ℝ, 0 < μ ∧ ∀ y ∈ F.K, ∃ u : A.domain, (u : E) ∈ F.K ∧ (μ : 𝕜) • (u : E) - A u = y) ∧
    (A.IsReducing F.K ↔ (∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) ∧
      ∀ t, 0 ≤ t → ∀ x ∈ F.Kᗮ, hA.semigroup.S t x ∈ F.Kᗮ)) ∧
    -- 3a. convergence on the core
    (∀ T : ℝ, ∀ x ∈ Z.Data, TendstoUniformlyOn
      (fun h t => F.sol h ((Z.cmp T).p x h 0) t) (fun t => hA.semigroup.S t x) F.l (Icc 0 T)) ∧
    -- 3b. convergence on the closure of the core
    (∀ T : ℝ, ∀ x ∈ Z.Data.topologicalClosure,
      Tendsto (fun h => F.incl h (F.proj h x)) F.l (𝓝 x) ∧
      ∀ v : ∀ h, F.X h, Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => F.sol h (v h) t) (fun t => hA.semigroup.S t x) F.l
          (Icc 0 T)) ∧
    -- 3c. rates
    (∀ (T : ℝ) (R : F.RateClass T), ∀ x ∈ R.Data, ∀ h, ∀ v : F.X h, ∀ t ∈ Icc 0 T,
      ‖hA.semigroup.S t x - F.sol h v t‖ ≤
        (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) +
          ‖F.incl h‖ * ‖R.p x h 0 - v‖) ∧
    -- 4a. invariant constraint
    ((∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) → ∀ x ∈ F.K,
      (∀ h (v : F.X h) t, 0 ≤ t → infDist (F.sol h v t) (F.K : Set E) ≤
        ‖hA.semigroup.S t x - F.sol h v t‖) ∧
      (x ∈ Z.Data.topologicalClosure → ∀ T : ℝ, ∀ v : ∀ h, F.X h,
        Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => infDist (F.sol h (v h) t) (F.K : Set E))
          (fun _ => 0) F.l (Icc 0 T))) ∧
    -- 4b. per datum
    (∀ Q : Set E, IsClosed Q → Q.Nonempty → ∀ x ∈ Z.Data.topologicalClosure,
      ∀ v : ∀ h, F.X h, Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) → ∀ t, 0 ≤ t →
      hA.semigroup.S t x ∉ Q → 0 < infDist (hA.semigroup.S t x) Q ∧
        Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l
          (𝓝 (infDist (hA.semigroup.S t x) Q))) ∧
    -- 4c. non-invariant constraint
    ((¬ ∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) → ∀ T : ℝ, 0 < T →
      ((∀ k ∈ F.K, k ∈ closure ((A.domain : Set E) ∩ F.K)) →
        ∃ x : A.domain, (x : E) ∈ F.K ∧ ∃ t ∈ Icc 0 T, hA.semigroup.S t x ∉ F.K) ∧
      ∃ x ∈ F.K, ∃ t ∈ Icc 0 T, hA.semigroup.S t x ∉ F.K ∧
        0 < infDist (hA.semigroup.S t x) (F.K : Set E) ∧
        (x ∈ Z.Data.topologicalClosure → ∀ v : ∀ h, F.X h,
          Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
          Tendsto (fun h => infDist (F.sol h (v h) t) (F.K : Set E)) F.l
            (𝓝 (infDist (hA.semigroup.S t x) (F.K : Set E))) ∧
          ∀ᶠ h in F.l, infDist (hA.semigroup.S t x) (F.K : Set E) / 2 <
            infDist (F.sol h (v h) t) (F.K : Set E))) := by
  refine ⟨fun x T => ⟨V.isClassicalSolution x T, V.unique x T,
      fun s t hs hst => V.antitone x hs (hs.trans hst) hst, fun t ht => V.energy x ht⟩,
    ⟨V.keeps_iff_resolvent, V.keeps_iff_solvable, V.isReducing_iff⟩, fun T x hx => ?_,
    fun T x hx => ⟨V.tendsto_incl_proj hx, fun v hv => V.converges hx hv T⟩,
    fun T R x hx h v t ht => V.rate R hx h v ht,
    fun hK x hxK => ⟨fun h v t ht => V.residual_le hK hxK h v ht,
      fun hx T v hv => V.residual_tendsto hK hxK hx hv T⟩,
    fun Q hQ hQne x hx v hv t ht hout =>
      ⟨(V.detects hQ hQne ht hout).1, V.tendsto_infDist Q hx hv ht⟩,
    fun hK T hT => ⟨fun hd => ?_, ?_⟩⟩
  · rcases lt_or_ge T 0 with hT | hT
    · rw [Icc_eq_empty (by linarith)]; exact tendstoUniformlyOn_empty
    exact V.converges (Submodule.le_topologicalClosure _ hx) (Z.tendsto_incl_p hT hx) T
  · obtain ⟨x, ⟨hxD, hxK⟩, t, ht, hout⟩ := V.leaves_smooth F.isClosed_K hK hd hT
    exact ⟨⟨x, hxD⟩, hxK, t, ht, hout⟩
  · obtain ⟨x, hxK, t, ht, hout⟩ := V.leaves hK hT
    exact ⟨x, hxK, t, ht, hout, V.detects F.isClosed_K ⟨0, F.K.zero_mem⟩ ht.1 hout⟩

end Dissip

section Approx

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} {F : ApproxFEEC.{u} H κ}

/-- The conclusion of `approxFEEC` in its earlier shape (the wave group throughout), from
`ApproxFEEC.Verdict`. -/
theorem approx_old {Z : F.Core} (V : F.Verdict Z) :
    -- 1. well-posedness
    (∀ x ∈ H.wave.domain, ∀ T : ℝ,
      Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 (fun t => H.waveGroup.S t x) ∧
      (∀ U, U 0 = x → Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      (∀ U, U 0 = x → HodgeWave.IsWeakSolution H (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      ∀ t, ‖H.waveGroup.S t x‖ = ‖x‖) ∧
    -- 2. propagation iff reducing
    (H.wave.IsReducing F.K ↔ ∀ t, ∀ x ∈ F.K, H.waveGroup.S t x ∈ F.K) ∧
    -- 3a. convergence on the core
    (∀ T : ℝ, ∀ x ∈ Z.Data, TendstoUniformlyOn
      (fun h t => F.sol h ((Z.cmp T).p x h 0) t) (fun t => H.waveGroup.S t x) F.l (Icc 0 T)) ∧
    -- 3b. convergence on the closure of the core
    (∀ T : ℝ, ∀ x ∈ Z.Data.topologicalClosure,
      Tendsto (fun h => F.incl h (F.proj h x)) F.l (𝓝 x) ∧
      ∀ v : ∀ h, F.X h, Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => F.sol h (v h) t) (fun t => H.waveGroup.S t x) F.l
          (Icc 0 T)) ∧
    -- 3c. rates
    (∀ (T : ℝ) (R : F.RateClass T), ∀ x ∈ R.Data, ∀ h, ∀ v : F.X h, ∀ t ∈ Icc 0 T,
      ‖H.waveGroup.S t x - F.sol h v t‖ ≤
        (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) +
          ‖F.incl h‖ * ‖R.p x h 0 - v‖) ∧
    -- 4a. reducing constraint
    (H.wave.IsReducing F.K → ∀ x ∈ F.K,
      (∀ h (v : F.X h) t, infDist (F.sol h v t) (F.K : Set (PiLp 2 W)) ≤
        ‖H.waveGroup.S t x - F.sol h v t‖) ∧
      (x ∈ Z.Data.topologicalClosure → ∀ T : ℝ, ∀ v : ∀ h, F.X h,
        Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => infDist (F.sol h (v h) t) (F.K : Set (PiLp 2 W)))
          (fun _ => 0) F.l (Icc 0 T))) ∧
    -- 4b. per datum
    (∀ Q : Set (PiLp 2 W), IsClosed Q → Q.Nonempty → ∀ x ∈ Z.Data.topologicalClosure,
      ∀ v : ∀ h, F.X h, Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) → ∀ t, 0 ≤ t →
      H.waveGroup.S t x ∉ Q → 0 < infDist (H.waveGroup.S t x) Q ∧
        Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l
          (𝓝 (infDist (H.waveGroup.S t x) Q))) ∧
    -- 4b. a non-reducing constraint is left by data of `K` or `Kᗮ`
    (¬ H.wave.IsReducing F.K → ∀ T : ℝ, 0 < T →
      ∃ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
        H.waveGroup.S t x ∉ Q ∧ 0 < infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)) ∧
        (Dense (Z.Data : Set (PiLp 2 W)) → ∀ v : ∀ h, F.X h,
          Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
          Tendsto (fun h => infDist (F.sol h (v h) t) (Q : Set (PiLp 2 W))) F.l
            (𝓝 (infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)))))) ∧
    -- 4c. with `D(L) ∩ K` dense in `K`: departure for some `t ∈ [-T, T]`
    (¬ H.wave.IsReducing F.K →
      (∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) → ∀ T : ℝ, 0 < T →
      ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc (-T) T,
        H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W))) ∧
    -- 4c. graded complex: departure forward in time, with residuals of positive limit
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
            infDist (F.sol h (v h) t) (F.K : Set (PiLp 2 W)))) := by
  have hS : ∀ t, 0 ≤ t → ∀ x, F.S t x = H.waveGroup.S t x := fun t ht x => by
    rw [F.S_eq_waveGroup ht]
  have hcl : Dense (Z.Data : Set (PiLp 2 W)) → ∀ x, x ∈ Z.Data.topologicalClosure := fun hd x => by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, hd.closure_eq]; trivial
  have hlim : ∀ (Q : Set (PiLp 2 W)) {x}, x ∈ Z.Data.topologicalClosure → ∀ {v : ∀ h, F.X h},
      Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) → ∀ {t}, 0 ≤ t →
      Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l
        (𝓝 (infDist (H.waveGroup.S t x) Q)) := fun Q x hx v hv t ht => by
    rw [← hS t ht x]; exact V.tendsto_infDist Q hx hv ht
  have hKr : H.wave.IsReducing F.K → F.Keeps F.K := fun hK => (V.isReducing_iff.1 hK).1
  refine ⟨fun x hx T => ?_, V.isReducing_iff_invariant,
    fun T x hx => ?_, ?_, fun T R x hx h v t ht => ?_,
    fun hK x hxK => ⟨fun h v t => ?_, fun hx T v hv => V.residual_tendsto (hKr hK) hxK hx hv T⟩,
    fun Q hQ hQne x hx v hv t ht hout =>
      ⟨(hQ.notMem_iff_infDist_pos hQne).1 hout, hlim Q hx hv ht⟩,
    fun hK T hT => ?_, fun hK hd T hT => ?_, fun p hp hRK hd hK T hT => ?_⟩
  · have e : EqOn (fun t => F.S t x) (fun t => H.waveGroup.S t x) (Icc 0 T) :=
      fun t ht => hS t ht.1 x
    exact ⟨(V.isClassicalSolution ⟨x, hx⟩ T).congr e fun _ _ => rfl,
      fun U hU0 hU => (V.unique ⟨x, hx⟩ T U hU0 hU).trans e,
      fun U hU0 hU => (V.unique_weak ⟨x, hx⟩ T U hU0 hU).trans e, fun t => V.norm_U t x⟩
  · rcases lt_or_ge T 0 with hT | hT
    · rw [Icc_eq_empty (by linarith)]; exact tendstoUniformlyOn_empty
    exact (V.converges (Submodule.le_topologicalClosure _ hx) (Z.tendsto_incl_p hT hx)
      T).congr_right fun t ht => hS t ht.1 x
  · intro T x hx
    exact ⟨V.tendsto_incl_proj hx, fun v hv =>
      (V.converges hx hv T).congr_right fun t ht => hS t ht.1 x⟩
  · rw [← hS t ht.1 x]; exact V.rate R hx h v ht
  · rw [norm_sub_rev, ← dist_eq_norm]
    exact infDist_le_dist_of_mem (V.isReducing_iff_invariant.1 hK t x hxK)
  · have hnot : ¬ (F.Keeps F.K ∧ F.Keeps F.Kᗮ) := fun h => hK (V.isReducing_iff.2 h)
    have hc : IsClosed (F.Kᗮ : Set (PiLp 2 W)) := Submodule.isClosed_orthogonal _
    have key : ∀ Q : Submodule 𝕜 (PiLp 2 W), IsClosed (Q : Set (PiLp 2 W)) →
        ¬ F.Keeps Q → ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
          H.waveGroup.S t x ∉ Q ∧ 0 < infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)) ∧
          (Dense (Z.Data : Set (PiLp 2 W)) → ∀ v : ∀ h, F.X h,
            Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
            Tendsto (fun h => infDist (F.sol h (v h) t) (Q : Set (PiLp 2 W))) F.l
              (𝓝 (infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W))))) := fun Q hQ hnk => by
      obtain ⟨x, hx, t, ht, hout⟩ := V.leaves hnk hT
      obtain ⟨hp, hd⟩ := V.detects hQ ⟨0, Q.zero_mem⟩ ht.1 hout
      rw [F.S_eq_waveGroup ht.1] at hout hp hd
      exact ⟨x, hx, t, ht, hout, hp, fun hdn v hv => (hd (hcl hdn x) v hv).1⟩
    by_cases hk : F.Keeps F.K
    · obtain ⟨x, hx, t, ht, h⟩ := key F.Kᗮ hc fun h => hnot ⟨hk, h⟩
      exact ⟨F.Kᗮ, Or.inr rfl, x, hx, t, ht, h⟩
    · obtain ⟨x, hx, t, ht, h⟩ := key F.K F.isClosed_K hk
      exact ⟨F.K, Or.inl rfl, x, hx, t, ht, h⟩
  · obtain ⟨x, ⟨hxD, hxK⟩, t, ht, hout⟩ := V.leaves_smooth_symm F.isClosed_K
      (fun h => hK (V.isReducing_iff_invariant.2 h)) hd hT
    exact ⟨⟨x, hxD⟩, hxK, t, ht, hout,
      (F.isClosed_K.notMem_iff_infDist_pos ⟨0, F.K.zero_mem⟩).1 hout⟩
  · obtain ⟨x, ⟨hxD, hxK⟩, t, ht, hout⟩ := V.leaves_smooth F.isClosed_K
      (fun h => hK ((V.isReducing_iff_keeps hp hRK hd).2 h)) hd hT
    have hdet := V.detects F.isClosed_K ⟨0, F.K.zero_mem⟩ ht.1 hout
    rw [F.S_eq_waveGroup ht.1] at hout hdet
    exact ⟨⟨x, hxD⟩, hxK, t, ht, hout, hdet⟩

end Approx

section Constrained

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} {F : ConstrainedFEEC H κ}

/-- The conclusion of `constrainedFEEC` in its earlier shape (an eight-part conjunction), from
`ConstrainedFEEC.Verdict`. -/
theorem constrained_old (V : F.Verdict) :
    -- 1. well-posedness
    (∀ x ∈ H.wave.domain, ∀ T : ℝ,
      Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 (fun t => H.waveGroup.S t x) ∧
      (∀ U, U 0 = x → Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      (∀ U, U 0 = x → HodgeWave.IsWeakSolution H (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      ∀ t, ‖H.waveGroup.S t x‖ = ‖x‖) ∧
    -- 2. constraint propagation
    (H.wave.IsReducing F.K ↔ ∀ t, ∀ x ∈ F.K, H.waveGroup.S t x ∈ F.K) ∧
    -- 3. convergence, with rates
    (∀ T : ℝ, (∀ x : H.wave.domain, TendstoUniformlyOn
        (fun h t => H.totalD.graphFst (F.discrete h (waveLift H x) t))
        (fun t => H.waveGroup.S t x) F.l (Icc 0 T)) ∧
      ∀ x : PiLp 2 W,
        (∀ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
          (∀ h, HodgeWave.IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
          Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
          TendstoUniformlyOn (fun h t => H.totalD.graphFst (ξh h t))
            (fun t => H.waveGroup.S t x) F.l (Icc 0 T)) ∧
        ∃ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
          (∀ h, HodgeWave.IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) ∧
          Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x)) ∧
    (∀ (T : ℝ) (R : F.RateClass T) (x : PiLp 2 W) (hxR : x ∈ R.Data) (h : κ), ∀ t ∈ Icc 0 T,
      ‖H.waveGroup.S t x -
          H.totalD.graphFst (F.discrete h (waveLift H ⟨x, R.mem_domain x hxR⟩) t)‖ ≤
        (1 + ellipticConst H) * (1 + t) ^ 2 * (R.C * R.meshSize h ^ R.α * R.classNorm x)) ∧
    -- 4. the constraint residual
    (H.wave.IsReducing F.K → ∀ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K → ∀ T : ℝ,
      (∀ h t, infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
          (F.K : Set (PiLp 2 W)) ≤
        ‖H.waveGroup.S t x - H.totalD.graphFst (F.discrete h (waveLift H x) t)‖) ∧
      TendstoUniformlyOn
        (fun h t => infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
          (F.K : Set (PiLp 2 W))) (fun _ => 0) F.l (Icc 0 T)) ∧
    (¬ H.wave.IsReducing F.K → ∀ T : ℝ, 0 < T →
      ∃ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
        H.waveGroup.S t x ∉ Q ∧ 0 < infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)) ∧
        ∀ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
          (∀ h, HodgeWave.IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
          Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
          Tendsto (fun h => infDist (H.totalD.graphFst (ξh h t)) (Q : Set (PiLp 2 W))) F.l
            (𝓝 (infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W))))) ∧
    (¬ H.wave.IsReducing F.K →
      (∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) → ∀ T : ℝ, 0 < T →
      ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc (-T) T,
        H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W))) ∧
    (∀ p : ι → Bool, (∀ i j, c.Rel i j → p j ≠ p i) → (∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K) →
      (∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) →
      ¬ H.wave.IsReducing F.K → ∀ T : ℝ, 0 < T →
      ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc 0 T,
        H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) ∧
        Tendsto (fun h => infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
          (F.K : Set (PiLp 2 W))) F.l (𝓝 (infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)))) ∧
        ∀ᶠ h in F.l, infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) / 2 <
          infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t)) (F.K : Set (PiLp 2 W))) :=
  ⟨fun _ hx T => V.wellPosed hx T, V.propagates_iff,
    fun T => ⟨fun x => V.converges x T,
      fun x => ⟨fun ξh ξh' hξh h0 => V.converges_of_tendsto x ξh ξh' hξh h0, V.exists_tendsto x T⟩⟩,
    fun _ R _ hxR h _ ht => V.rate R hxR h ht,
    fun hK x hxK _ => ⟨fun h t => V.residual_le hK x hxK h t, V.residual_tendsto hK x hxK _⟩,
    fun hK _ hT => V.leaves hK hT, fun hK hD _ hT => V.leaves_symm hK hD hT,
    fun _ hp hRK hD hK _ hT => V.leaves_graded hp hRK hD hK hT⟩

/-- Both proofs of the constrained FEEC theorem give the verdict. -/
example (F : ConstrainedFEEC H κ) : F.Verdict := constrainedFEEC F

example (F : ConstrainedFEEC H κ) : F.Verdict := F.constrainedFEEC_of_approxFEEC

end Constrained

end FeecCheck.Verdicts
