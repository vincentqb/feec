import Feec.HilbertComplex.Approximation.StaticFEEC
import Feec.HilbertComplex.Approximation.Ritz
import Feec.HilbertComplex.Approximation.RitzResolvent
import Feec.HilbertComplex.Approximation.FullyDiscrete
import Feec.Models.Cube.InhomogeneousError

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
by definition (`rfl`). The resolvent core of `Feec.HilbertComplex.DissipGalerkin`
(`DissipFEEC.Core.ofResolvent`) has the data of the resolvent Ritz projection
(`DissipFEEC.Ritz.ofResolvent`), whose hypotheses its own imply.

## The fully discrete layer

The temporal error of `DissipFEEC.TimeScheme.Verdict.rate_iterates` is `‖Lₕ^{p+1} v‖`, not
uniform in `h`; `rate_smooth_iterates` replaces it by the `(p + 1)`-st time derivative of a smooth
comparison (`DissipFEEC.Comparison.Smooth`), which for a Ritz projection (`DissipFEEC.Ritz.smooth`)
is `Rₕ S(t) A^{p+1} x`. The example `ritz_crankNicolson` composes the Ritz rate class on
`D(A³)` (`Ritz.toRateClass`, `RegScale.domainPow`) with Crank–Nicolson: the temporal error is
`1/12 tₙ τₕ² C ‖A³ x‖`, from static estimates only. The trapezoidal remainder of the Dirichlet
Crank–Nicolson estimate of `Feec.Models.Cube.InhomogeneousError` is now
`Feec.TimeStepping.norm_trapezoid_le` (right derivatives, sharp constant `1/12`); `trapezoid_old`
states the old remainder verbatim and derives it. The Dirichlet scheme itself (inhomogeneous
boundary degrees of freedom, a weak solution against `V̊ₕ`) is not the orbit of a `DissipFEEC`, so
its estimate is not a corollary of the fully discrete verdict: `cn_old` states the conclusion of
`norm_cn_error_le` verbatim and derives it from the model theorem, which shares the trapezoidal
engine.

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

/-- The hypotheses of `Core.ofResolvent` give the core of the resolvent Ritz projection, with
the same data `D(A²)`. -/
example (hres : ∀ z, Tendsto (fun h => F.incl h (F.discreteRes h (F.proj h z))) F.l
      (𝓝 (Operator.resolvent A 1 z)))
    (happ : ∀ z, Tendsto (fun h => F.incl h (F.proj h z)) F.l (𝓝 z)) :
    ((Ritz.ofResolvent F).toCore hres (Ritz.tendsto_ofResolvent F hres happ).1
      (Ritz.tendsto_ofResolvent F hres happ).2).Data =
      (Core.ofResolvent F hres happ).Data :=
  rfl

end Ritz

section FullyDiscrete

open DissipFEEC

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E} {κ : Type*}
  {F : DissipFEEC.{u} A κ}

/-- **Ritz projection plus Crank–Nicolson**: for a Ritz projection of the identity lift with
`‖Rₕ‖ ≤ C` and static estimates on `D(A³)`, at `tₙ = n τₕ ∈ [0, T]`, the error is the spatial
rate plus `‖ιₕ‖ (‖Rₕ x - v‖ + tₙ (τₕ²/12 · C ‖A³ x‖ + C_d hᵅ ‖x‖_{D(A³)}))`. -/
example (𝓡 : F.Ritz (Lift.ofDomain F)) {C : ℝ} (hC : ∀ h, ‖𝓡.R h‖ ≤ C) {T : ℝ} (D : Set E)
    (meshSize : κ → ℝ) (hmesh : ∀ h, 0 ≤ meshSize h) (α Cs Cd : ℝ) (hCs : 0 ≤ Cs) (hCd : 0 ≤ Cd)
    (happrox : ∀ y ∈ iterDomain A 3, ∀ h,
      ‖y - F.incl h (𝓡.R h y)‖ ≤ Cs * meshSize h ^ α * iterDomainNorm A 3 y)
    (hdefect : ∀ y ∈ iterDomain A 3, ∀ h, ‖𝓡.Δ h (genExt A y)‖ + ‖𝓡.Δ' h y‖ ≤
      Cd * meshSize h ^ α * iterDomainNorm A 3 y)
    {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) {x : E} (hx : x ∈ D ∩ iterDomain A 3) (h : κ) (v : F.X h)
    {n : ℕ} (hn : (n : ℝ) * τ h ∈ Icc 0 T) :
    ‖F.S (n * τ h) x - (F.crankNicolson τ hτ).sol h v n‖ ≤
      Cs * 1 * meshSize h ^ α * iterDomainNorm A 3 x + ‖F.incl h‖ * 1 *
        (‖𝓡.R h (F.S 0 x) - v‖ + n * τ h * (1 / 12 * τ h ^ 2 * (C * ‖(genExt A)^[3] x‖) +
          Cd * 1 * meshSize h ^ α * iterDomainNorm A 3 x)) :=
  (F.crankNicolson τ hτ).norm_S_sub_sol_le_of_smooth (F.crankNicolson_isTrajConsistent hτ)
    (𝓡.toRateClass (RegScale.domainPow F T D 3) (fun _ hy => hy.2 0 (by norm_num)) meshSize
      hmesh α Cs Cd hCs hCd happrox hdefect)
    ((𝓡.smooth T 3 (iterDomain A 3) (fun _ hy => hy) hC (fun y => ‖(genExt A)^[3] y‖)
      fun _ _ t ht => F.norm_S_apply_le ht.1 _).restrict (RegScale.domainPow F T D 3).Data
      fun _ hy => hy.2 0 (by norm_num))
    hx hx.2 h v hn

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The old trapezoidal remainder of `Feec.Models.Cube.InhomogeneousError` (`norm_trapezoid_le`,
derivatives within `[a, b]`, constant `1/2`), from `Feec.TimeStepping.norm_trapezoid_le`. -/
theorem trapezoid_old {f f₁ f₂ f₃ : ℝ → X} {a b L : ℝ} (hab : a ≤ b)
    (h1 : ∀ t ∈ Icc a b, HasDerivWithinAt f (f₁ t) (Icc a b) t)
    (h2 : ∀ t ∈ Icc a b, HasDerivWithinAt f₁ (f₂ t) (Icc a b) t)
    (h3 : ∀ t ∈ Icc a b, HasDerivWithinAt f₂ (f₃ t) (Icc a b) t)
    (hL : ∀ t ∈ Icc a b, ‖f₃ t‖ ≤ L) :
    ‖f b - f a - ((b - a) / 2) • (f₁ b + f₁ a)‖ ≤ L * (b - a) ^ 3 / 2 := by
  have hc : ∀ {g g' : ℝ → X}, (∀ t ∈ Icc a b, HasDerivWithinAt g (g' t) (Icc a b) t) →
      ContinuousOn g (Icc a b) := fun hg t ht => (hg t ht).continuousWithinAt
  have hr : ∀ {g g' : ℝ → X}, (∀ t ∈ Icc a b, HasDerivWithinAt g (g' t) (Icc a b) t) →
      ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t := fun hg t ht =>
    (hg t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
  refine (TimeStepping.norm_trapezoid_le hab (hc h1) (hc h2) (hc h3) (hr h1) (hr h2) (hr h3)
    fun t ht => hL t (Ico_subset_Icc_self ht)).trans ?_
  have := pow_nonneg (sub_nonneg.2 hab) 3
  nlinarith [(norm_nonneg _).trans (hL a ⟨le_rfl, hab⟩)]

open scoped RealInnerProductSpace in
open Feec.Models.Cube.Inhomogeneous in
/-- The conclusion of the Dirichlet Crank–Nicolson estimate `norm_cn_error_le`, verbatim. -/
theorem cn_old {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {emb : V →ₗ[ℝ] X} {D : V →ₗ[ℝ] V} {V₀ : Submodule ℝ V}
    (hemb : ∀ x y, ⟪emb x, emb y⟫ = ⟪x, y⟫)
    (hD₀ : ∀ v ∈ V₀, D v ∈ V₀) (hDD : ∀ v ∈ V₀, D (D v) = 0) {A : V →ₗ[ℝ] V}
    (hA : ∀ x y, ⟪A x, y⟫ = ⟪D x, y⟫ - ⟪x, D y⟫) {Δt T L₃ a : ℝ} (hΔt : 0 < Δt)
    {U U₁ U₂ U₃ DU : ℝ → X}
    (hU₁ : ∀ t ∈ Icc 0 T, HasDerivWithinAt U (U₁ t) (Icc 0 T) t)
    (hU₂ : ∀ t ∈ Icc 0 T, HasDerivWithinAt U₁ (U₂ t) (Icc 0 T) t)
    (hU₃ : ∀ t ∈ Icc 0 T, HasDerivWithinAt U₂ (U₃ t) (Icc 0 T) t)
    (hL₃ : ∀ t ∈ Icc 0 T, ‖U₃ t‖ ≤ L₃)
    (hweak : ∀ t ∈ Icc 0 T, ∀ v ∈ V₀, ⟪U₁ t, emb v⟫ = ⟪DU t, emb v⟫ - ⟪U t, emb (D v)⟫)
    {w : ℕ → V}
    (hA1 : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (w n) - U (n * Δt)‖ ≤ a)
    (hA2 : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (D (w n)) - DU (n * Δt)‖ ≤ a)
    (hA3 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * Δt ≤ T →
      ‖(emb (w (n + 1)) - U ((n + 1 : ℕ) * Δt)) - (emb (w n) - U (n * Δt))‖ ≤ a * Δt)
    {M : ℕ} (hM : (M : ℝ) * Δt ≤ T) {u g : ℕ → V}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep V₀ A (Δt / 2) 0 (g (n + 1)) (u n)
      (u (n + 1)))
    (hg : ∀ n < M, g (n + 1) - w (n + 1) ∈ V₀) (hu0 : u 0 - w 0 ∈ V₀) :
    ∃ ũ : ℕ → V, (∀ n, ũ n - w n ∈ V₀) ∧
      (∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (ũ n) - U (n * Δt)‖ ≤ a) ∧
      ‖u M - ũ M‖ ≤ ‖u 0 - w 0‖ + a + T * (L₃ * Δt ^ 2 / 2 + 2 * a) ∧
      ‖emb (u M) - U (M * Δt)‖ ≤ ‖u 0 - w 0‖ + 2 * a + T * (L₃ * Δt ^ 2 / 2 + 2 * a) :=
  norm_cn_error_le hemb hD₀ hDD hA hΔt hU₁ hU₂ hU₃ hL₃ hweak hA1 hA2 hA3 hM hstep hg hu0

end FullyDiscrete

end FeecCheck.Crown
