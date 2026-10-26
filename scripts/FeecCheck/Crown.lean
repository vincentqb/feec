import Feec.HilbertComplex.Approximation.StaticFEEC
import Feec.HilbertComplex.Approximation.Ritz
import Feec.HilbertComplex.Approximation.RitzResolvent
import Feec.HilbertComplex.Approximation.ApproxConforming

/-!
# Regression tests: nothing is lost on the way to the crown

The crown layers restate or re-derive the constructions they replace; each section below states
an old result verbatim and proves it from the new API.

## The static layer

The finite element theorems for families of subcomplexes with uniformly bounded projections were
stated on `HΛ`-type complexes over `ℝ`, on `ComplexShape.up ℤ`, for sequences `N → ∞`, in
`Feec.Models.Parallelepiped` (`HasUniformProj`, `discretePoincare_of`, `mixed_wellPosed_of`,
`mixed_quasiOptimal_of`, `mixed_rate_of`, `infDist_domainSub_le_two_mul`). They are now the
theorems of `Feec.HilbertComplex.Approximation.StaticFEEC`, over any `RCLike` field, any complex
shape and any filter (`Subcomplex.HasUniformProj`, `HasUniformProj.discretePoincare`,
`HasUniformProj.mixed_wellPosed`, `HasUniformProj.mixed_quasiOptimal`,
`Subcomplex.CochainProjection.norm_sub_le_rate`, `Subcomplex.infDist_domainSub_le_two_mul`), and,
for conforming families, the fields of `ConformingFamily.StaticVerdict`. The theorems `static_old_*`
below state the old results verbatim (the old `HasUniformProj H S` is
`Subcomplex.HasUniformProj atTop S`, `static_old_hasUniformProj`) and derive them from the new
ones at `ℝ`, `ComplexShape.up ℤ` and `atTop`.

## Ritz projections

The Trotter–Kato bridge of `Feec.HilbertComplex.DissipFEEC` (`DissipFEEC.Comparison.ofOperator`,
`DissipFEEC.Core.ofOperator`) is the Ritz projection of the identity lift
(`DissipFEEC.Ritz.ofOperator`): its comparison is `Ritz.cmp` and its core is `Ritz.toCore`, both
by definition (`rfl`). The resolvent core (`DissipFEEC.Core.ofResolvent`) is, by definition, the
core of the resolvent Ritz projection (`DissipFEEC.Ritz.ofResolvent`), whose hypotheses its own
imply; likewise the graph-space bridge `ApproxFEEC.Core.ofOperator` is the core of the graph Ritz
projection `ApproxFEEC.graphRitz`.

## The dynamic duplicates, collapsed onto Ritz projections

The conforming wave discretizations (`ConstrainedFEEC`) had a direct proof of the constrained FEEC
theorem next to its re-derivation from `approxFEEC`; `constrainedFEEC` is now the re-derivation
(the core and the rate classes of the wave Ritz projection `ConstrainedFEEC.waveRitz`, the
elliptic projection), and the lemmas of the direct proof are gone. The theorems
`constrained_old_*` below state them verbatim and derive them from the verdict
`constrainedFEEC F` (and, for the propagation facts, from the verdict of `approxFEEC` on
`F.toApprox`); `constrained_old_rate_le` is the old `ConstrainedFEEC.rate_le_constrainedFEEC`, the
`(1 + C_P)(1 + t)²` bound, now `constrainedFEEC_rate`. The direct Trotter–Kato proof of the
resolvent core is gone too: `DissipFEEC.Core.ofResolvent` is the core of the resolvent Ritz
projection, and the trajectories of the deleted `DissipFEEC.Comparison.ofResolvent` are those of
`Ritz.ofResolvent` (`resolvent_old_p`).

This file is part of the `FeecCheck` library, not of `Feec`: it is compiled by
`lake build FeecCheck` (and so by `lake exe feec-gate`) and fails that build if a conclusion is
dropped or a re-derivation breaks.
-/

open Set Filter Topology

universe u

namespace FeecCheck.Crown

open Feec Feec.HilbertComplex

section StaticOld

variable {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)]
  [∀ i, CompleteSpace (W i)] {H : HilbertComplex ℝ (ComplexShape.up ℤ) W}

/-- The old `Parallelepiped.HasUniformProj H S` is `Subcomplex.HasUniformProj atTop S`. -/
theorem static_old_hasUniformProj (S : ℕ → H.Subcomplex) :
    Subcomplex.HasUniformProj atTop S ↔
      ∃ (C : ℝ) (π : ∀ N, (S N).CochainProjection), 1 ≤ C ∧
        (∀ N i x, ‖(π N).π i x‖ ≤ C * ‖x‖) ∧ (∀ N i j, (π N).IsGraphBounded i j C) ∧
        ∀ j, Tendsto (fun N => (π N).harmonicGap j) atTop (𝓝 0) :=
  Iff.rfl

/-- The old `Parallelepiped.infDist_domainSub_le_two_mul`. -/
theorem static_old_infDist_domainSub_le_two_mul (S : H.Subcomplex)
    [∀ i, FiniteDimensional ℝ (S.V i)] {j : ℤ} (σ : H.domainSpace j) {v : W j} (hv : v ∈ S.V j)
    {ε : ℝ} (h1 : ‖H.domainIncl j σ - v‖ ≤ ε)
    (h2 : ∀ j' (hx : H.domainIncl j σ ∈ (H.d j j').domain),
      ‖H.d j j' ⟨H.domainIncl j σ - v, Submodule.sub_mem _ hx (S.le_domain j j' hv)⟩‖ ≤ ε) :
    Metric.infDist σ (S.domainSub j) ≤ 2 * ε :=
  S.infDist_domainSub_le_two_mul (rfl : (ComplexShape.up ℤ).Rel j (j + 1)) σ hv h1 (h2 _)

variable {S : ℕ → H.Subcomplex} [∀ N k, FiniteDimensional ℝ ((S N).V k)] {cP : ℝ}
  (hcP : 1 ≤ cP)
  (hP : ∀ i j, (ComplexShape.up ℤ).Rel i j → ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ →
    ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
include hP

omit [∀ N k, FiniteDimensional ℝ ((S N).V k)] in
/-- The old `Parallelepiped.discretePoincare_of`. -/
theorem static_old_discretePoincare (h : Subcomplex.HasUniformProj atTop S) : ∃ c : ℝ,
    ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ) {x : W i} (hx : x ∈ (S N).V i),
    (∀ y ∈ (S N).cyclesW i, inner ℝ y x = 0) →
      ‖x‖ ≤ c * ‖H.d i j ⟨x, (S N).le_domain i j hx⟩‖ :=
  Subcomplex.HasUniformProj.discretePoincare hP h

include hcP in
/-- The old `Parallelepiped.mixed_wellPosed_of`. -/
theorem static_old_wellPosed (h : Subcomplex.HasUniformProj atTop S) : ∃ C : ℝ, ∀ {i j k : ℤ},
    (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k → ∀ (N : ℕ) (f : (S N).V j),
    (∃! x, (S N).toHilbertComplex.mixedForm i j k x = (S N).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (S N).toHilbertComplex.MixedSpace i j,
      (S N).toHilbertComplex.mixedForm i j k x = (S N).toHilbertComplex.mixedRHS i j f →
        ‖x‖ ≤ C * ‖f‖ :=
  Subcomplex.HasUniformProj.mixed_wellPosed hP hcP h

/-- The old `Parallelepiped.mixed_quasiOptimal_of`. -/
theorem static_old_quasiOptimal (h : Subcomplex.HasUniformProj atTop S) :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {q : H.harmonic j},
    H.IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution (S N) hij hjk f).fst‖ +
        ‖u - (S N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (S N) hij hjk f).snd.fst‖ +
        ‖(q : W j) - (((Subcomplex.CochainProjection.discreteMixedSolution (S N) hij hjk
          f).snd.snd : (S N).V j) : W j)‖ ≤
      K * (Metric.infDist σ ((S N).domainSub i) + Metric.infDist u ((S N).domainSub j) +
        Metric.infDist (q : W j) ((S N).harmonicW j) +
        μ j N * Metric.infDist (H.boundaryPart j (H.domainIncl j u)) ((S N).domainSub j)) :=
  Subcomplex.HasUniformProj.mixed_quasiOptimal hP h

/-- The old `Parallelepiped.mixed_rate_of`. -/
theorem static_old_rate {C : ℝ} (π : ∀ N, (S N).CochainProjection) (hC1 : 1 ≤ C)
    (hg : ∀ N i j, (π N).IsGraphBounded i j C) {Reg : ∀ l, W l → Prop} {B : ℤ → ℝ}
    (hB : ∀ l, 0 ≤ B l) {r : ℕ → ℝ} (hr : ∀ N, 0 ≤ r N)
    (happ : ∀ N l (x : W l), Reg l x → ∃ v, ∃ hv : v ∈ (S N).V l, ‖x - v‖ ≤ B l * r N ∧
      ∀ j' (hx : x ∈ (H.d l j').domain),
        ‖H.d l j' ⟨x - v, Submodule.sub_mem _ hx ((S N).le_domain l j' hv)⟩‖ ≤ B l * r N)
    {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {q : H.harmonic j}
    (hs : H.IsMixedSolution i j k f σ u q) (hσ : Reg i (H.domainIncl i σ))
    (hu : Reg j (H.domainIncl j u))
    (hb : Reg j (H.domainIncl j (H.boundaryPart j (H.domainIncl j u))))
    (hq : Reg j (q : W j)) (N : ℕ) :
    ‖σ - (S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution (S N) hij hjk f).fst‖ +
        ‖u - (S N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (S N) hij hjk f).snd.fst‖ +
        ‖(q : W j) - (((Subcomplex.CochainProjection.discreteMixedSolution (S N) hij hjk
          f).snd.snd : (S N).V j) : W j)‖ ≤
      (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) * (2 * (B i + B j) * (3 + 2 * C)) * r N :=
  (π N).norm_sub_le_rate hij hjk hC1 (hP i j hij) (hP j k hjk) (hg N i j) (hg N j k) hB (hr N)
    (happ N) hs hσ hu hb hq

end StaticOld

section Ritz

open DissipFEEC

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  {A : E →ₗ.[𝕜] E} {κ : Type*} (F : DissipFEEC.{u} A κ)

/-- `Comparison.ofOperator` is the comparison of the Ritz projection `Ritz.ofOperator`. -/
example (R Δ Δ' : ∀ h, E →L[𝕜] F.X h) (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hdef : ∀ h (y : A.domain), R h (A y) - F.L h (R h y) = Δ h (A y) + Δ' h y) (T : ℝ) :
    (Ritz.ofOperator F R Δ Δ' hR hΔ hdef).cmp T = Comparison.ofOperator F R T :=
  rfl

/-- `Core.ofOperator` (the Trotter–Kato bridge) is the core of the Ritz projection
`Ritz.ofOperator`. -/
example (R : ∀ h, E →L[𝕜] F.X h) (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (happrox : ∀ y, Tendsto (fun h => F.incl h (R h y)) F.l (𝓝 y))
    (Δ Δ' : ∀ h, E →L[𝕜] F.X h) (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hdef : ∀ h (y : A.domain), R h (A y) - F.L h (R h y) = Δ h (A y) + Δ' h y)
    (hΔ0 : ∀ y, Tendsto (fun h => ‖Δ h y‖) F.l (𝓝 0))
    (hΔ'0 : ∀ y, Tendsto (fun h => ‖Δ' h y‖) F.l (𝓝 0)) :
    (Ritz.ofOperator F R Δ Δ' hR hΔ hdef).toCore happrox hΔ0 hΔ'0 =
      Core.ofOperator F R hR happrox Δ Δ' hΔ hdef hΔ0 hΔ'0 :=
  rfl

/-- The hypotheses of `Core.ofResolvent` give the core of the resolvent Ritz projection, which
is `Core.ofResolvent`, with data `D(A²)`. -/
example (hres : ∀ z, Tendsto (fun h => F.incl h (F.discreteRes h (F.proj h z))) F.l
      (𝓝 (Operator.resolvent A 1 z)))
    (happ : ∀ z, Tendsto (fun h => F.incl h (F.proj h z)) F.l (𝓝 z)) :
    (Ritz.ofResolvent F).toCore hres (Ritz.tendsto_ofResolvent F hres happ).1
      (Ritz.tendsto_ofResolvent F hres happ).2 = Core.ofResolvent F hres happ :=
  rfl

end Ritz


section ConstrainedOld

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ)

open HodgeWave Metric

/-- The old `forall_nonneg_of_forall_Icc` (on the wave group). -/
theorem constrained_old_forall_nonneg_of_forall_Icc {P : Set (PiLp 2 W)} {T : ℝ} (hT : 0 < T)
    (hP : ∀ x ∈ P, ∀ s ∈ Icc 0 T, H.waveGroup.S s x ∈ P) :
    ∀ x ∈ P, ∀ t, 0 ≤ t → H.waveGroup.S t x ∈ P :=
  H.waveGroup.toC0Semigroup.forall_nonneg_of_forall_Icc hT hP

/-- The old `forall_of_forall_Icc_neg` (on the wave group). -/
theorem constrained_old_forall_of_forall_Icc_neg {P : Set (PiLp 2 W)} {T : ℝ} (hT : 0 < T)
    (hP : ∀ x ∈ P, ∀ s ∈ Icc (-T) T, H.waveGroup.S s x ∈ P) :
    ∀ x ∈ P, ∀ t, H.waveGroup.S t x ∈ P :=
  H.waveGroup.forall_of_forall_Icc_neg hT hP

/-- The old `constrainedFEEC_converges`. -/
theorem constrained_old_converges (T : ℝ) :
    (∀ x : H.wave.domain, TendstoUniformlyOn
      (fun h t => H.totalD.graphFst (F.discrete h (waveLift H x) t))
      (fun t => H.waveGroup.S t x) F.l (Icc 0 T)) ∧
    ∀ x : PiLp 2 W,
      (∀ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
        Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => H.totalD.graphFst (ξh h t))
          (fun t => H.waveGroup.S t x) F.l (Icc 0 T)) ∧
      ∃ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) ∧
        Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) :=
  ⟨fun x => (constrainedFEEC F).converges x T, fun x =>
    ⟨fun ξh ξh' hξh h0 => (constrainedFEEC F).converges_of_tendsto x ξh ξh' hξh h0,
      (constrainedFEEC F).exists_tendsto x T⟩⟩

/-- The old `ConstrainedFEEC.rate_le_constrainedFEEC`, now `constrainedFEEC_rate`. -/
theorem constrained_old_rate_le {T : ℝ} (R : F.RateClass T) {x : PiLp 2 W} (hxR : x ∈ R.Data)
    (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖H.waveGroup.S t x -
        H.totalD.graphFst (F.discrete h (waveLift H ⟨x, R.mem_domain x hxR⟩) t)‖ ≤
      (1 + ellipticConst H) * (1 + t) ^ 2 * (R.C * R.meshSize h ^ R.α * R.classNorm x) :=
  (constrainedFEEC F).rate R hxR h ht

/-- The old `constrainedFEEC_residual`. -/
theorem constrained_old_residual (hK : H.wave.IsReducing F.K) (x : H.wave.domain)
    (hxK : (x : PiLp 2 W) ∈ F.K) (T : ℝ) :
    (∀ h t, infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t)) (F.K : Set (PiLp 2 W)) ≤
      ‖H.waveGroup.S t x - H.totalD.graphFst (F.discrete h (waveLift H x) t)‖) ∧
    TendstoUniformlyOn
      (fun h t => infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
        (F.K : Set (PiLp 2 W))) (fun _ => 0) F.l (Icc 0 T) :=
  ⟨(constrainedFEEC F).residual_le hK x hxK, (constrainedFEEC F).residual_tendsto hK x hxK T⟩

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- The old `ConstrainedFEEC.tendsto_infDist`. -/
theorem constrained_old_tendsto_infDist {Q : Set (PiLp 2 W)} {y : PiLp 2 W} {f : κ → PiLp 2 W}
    (hf : Tendsto f F.l (𝓝 y)) : Tendsto (fun h => infDist (f h) Q) F.l (𝓝 (infDist y Q)) :=
  ((continuous_infDist_pt Q).tendsto y).comp hf

/-- The old `ConstrainedFEEC.isReducing_of_forall_nonneg`, from `DissipFEEC.Verdict.isReducing_iff`
for `F.toApprox`. -/
theorem constrained_old_isReducing_of_forall_nonneg
    (h1 : ∀ x ∈ F.K, ∀ t, 0 ≤ t → H.waveGroup.S t x ∈ F.K)
    (h2 : ∀ x ∈ F.Kᗮ, ∀ t, 0 ≤ t → H.waveGroup.S t x ∈ F.Kᗮ) : H.wave.IsReducing F.K :=
  (approxFEEC F.toApprox F.toCore).isReducing_iff.2
    ⟨fun t ht x hx => by rw [F.toApprox.S_eq_waveGroup ht]; exact h1 x hx t ht,
      fun t ht x hx => by rw [F.toApprox.S_eq_waveGroup ht]; exact h2 x hx t ht⟩

/-- The old `ConstrainedFEEC.exists_not_mem_of_not_isReducing`. -/
theorem constrained_old_exists_not_mem_of_not_isReducing (hK : ¬ H.wave.IsReducing F.K) {T : ℝ}
    (hT : 0 < T) :
    (∃ x ∈ F.K, ∃ t ∈ Icc 0 T, H.waveGroup.S t x ∉ F.K) ∨
      ∃ x ∈ F.Kᗮ, ∃ t ∈ Icc 0 T, H.waveGroup.S t x ∉ F.Kᗮ := by
  by_contra hc
  simp only [not_or, not_exists, not_and, not_not] at hc
  exact hK (constrained_old_isReducing_of_forall_nonneg F
    (H.waveGroup.toC0Semigroup.forall_nonneg_of_forall_Icc hT (P := F.K) hc.1)
    (H.waveGroup.toC0Semigroup.forall_nonneg_of_forall_Icc hT (P := F.Kᗮ) hc.2))

/-- The old `constrainedFEEC_residual_not_isReducing`. -/
theorem constrained_old_residual_not_isReducing (hK : ¬ H.wave.IsReducing F.K) {T : ℝ}
    (hT : 0 < T) :
    ∃ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ Q ∧ 0 < infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)) ∧
      ∀ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
        Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
        Tendsto (fun h => infDist (H.totalD.graphFst (ξh h t)) (Q : Set (PiLp 2 W))) F.l
          (𝓝 (infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)))) :=
  (constrainedFEEC F).leaves hK hT

/-- The old `constrainedFEEC_residual_not_isReducing_of_grading`. -/
theorem constrained_old_residual_not_isReducing_of_grading {p : ι → Bool}
    (hp : ∀ i j, c.Rel i j → p j ≠ p i) (hRK : ∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K)
    (hdense : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K))
    (hK : ¬ H.wave.IsReducing F.K) {T : ℝ} (hT : 0 < T) :
    ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) ∧
      Tendsto (fun h => infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
        (F.K : Set (PiLp 2 W))) F.l (𝓝 (infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)))) ∧
      ∀ᶠ h in F.l, infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) / 2 <
        infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t)) (F.K : Set (PiLp 2 W)) :=
  (constrainedFEEC F).leaves_graded hp hRK hdense hK hT

/-- The old `constrainedFEEC_residual_not_isReducing_symm`. -/
theorem constrained_old_residual_not_isReducing_symm (hK : ¬ H.wave.IsReducing F.K)
    (hdense : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) {T : ℝ}
    (hT : 0 < T) :
    ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc (-T) T,
      H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) :=
  (constrainedFEEC F).leaves_symm hK hdense hT

/-- The core of the constrained FEEC discretization is the core of its wave Ritz projection, and
its rate classes are rate classes of that projection (`Ritz.orbitRateClass`). -/
example : F.toCore.cmp = F.waveRitz.cmp := rfl

example {T : ℝ} (R : F.RateClass T) : R.toApprox.toComparison =
    (F.waveRitz.cmp T).restrict R.Data
      (fun x hx => LinearPMap.mem_domainSq.2 ⟨R.mem_domain x hx, R.mem_domain_sq x _ hx⟩) :=
  rfl

end ConstrainedOld

section ResolventOld

open DissipFEEC

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  {A : E →ₗ.[𝕜] E} {κ : Type*} (F : DissipFEEC.{u} A κ)

/-- The comparison of the deleted `DissipFEEC.Comparison.ofResolvent` (data `R(1) D(A)`,
trajectories `pₕ(t) = (1 - Lₕ)⁻¹ πₕ S(t) (1 - A) x`) is that of the resolvent Ritz projection
(the old `Ritz.ofResolvent_cmp_p`). -/
theorem resolvent_old_p (T : ℝ) {x : E} (hx : x ∈ resData (A := A)) (h : κ) {t : ℝ}
    (ht : 0 ≤ t) : ((Ritz.ofResolvent F).cmp T).Data = resData (A := A) ∧
      ((Ritz.ofResolvent F).cmp T).p x h t =
        F.discreteRes h (F.proj h (F.S t (x - genExt A x))) :=
  ⟨rfl, congrArg (fun z => F.discreteRes h (F.proj h z))
    (F.S_sub_genExt (mem_domain_of_mem_resData F.isMDissipative hx) ht)⟩

end ResolventOld

end FeecCheck.Crown
