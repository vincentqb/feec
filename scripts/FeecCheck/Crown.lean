module

public import Feec.HilbertComplex.Approximation.StaticFEEC
public import Feec.HilbertComplex.Approximation.Ritz
public import Feec.HilbertComplex.Approximation.RitzResolvent
public import Feec.HilbertComplex.Approximation.ApproxConforming
public import Feec.HilbertComplex.Approximation.FullyDiscrete
public import Feec.HilbertComplex.Approximation.Crown
public import Feec.Models.Cube.HeatFEM
public import Feec.Models.Cube.InhomogeneousError
public import Feec.Models.Cube.SobolevRateHigh
public import Feec.Models.Cube.TangentialRate
public import Feec.Models.Parallelepiped.FiniteElement
public import Feec.Models.StarShaped.PolyFiniteElement
public import Feec.Instances.EinsteinBianchiFEM
public import Feec.Instances.EinsteinBianchiFEMDefect
public import Feec.Instances.EuclideanBand

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

## The static models

The finite element theorems of the models (the Freudenthal meshes of the cube,
`Feec.Models.Cube.FEM`; parallelepipeds, `Feec.Models.Parallelepiped`; domains star-shaped with
respect to a ball, `Feec.Models.StarShaped`) were stated family by family: the discrete Poincaré
inequality, well-posedness, quasi-optimality, the uniformly bounded projections with vanishing
harmonic gap, and the rates, once with no hypothesis and once more under the smoothing estimates
with explicit constants. They are now the static FEEC theorem
(`ConformingFamily.staticFEEC`, `ConformingFamily.StaticVerdict.rate`, `ConformingFamily.rate`)
for the conforming families of the models (`ConformingFamily.ofSmoothing` on the cube,
`IsChainIso.comapFamily` on parallelepipeds, `ConformingFamily.ofExists` on star-shaped domains;
`whitneyFamily`, `polyFamily` and their `Min` versions) with their Jackson estimates
(`whitneyJackson`, `polyJackson`, `polyJacksonTr`, `sobolevJackson`, `sobolevHighJackson`). The
theorems `cube_old_*`, `whitney_old_*`, `whitneyMin_old_*`, `poly_old_*`, `polyMin_old_*`,
`parity_old_*`, `para_old_*` and `star_old_*` state the deleted results verbatim (the transported
projections `Parallelepiped.proj` and their constant `projConst` with their definitions unfolded)
and derive them from the new API.

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

## The fully discrete layer

The temporal error of `DissipFEEC.TimeScheme.Verdict.rate_iterates` is `‖Lₕ^{p+1} v‖`, not
uniform in `h`; `rate_smooth_iterates` replaces it by the `(p + 1)`-st time derivative of a smooth
comparison (`DissipFEEC.Comparison.Smooth`), which for a Ritz projection (`DissipFEEC.Ritz.smooth`)
is `Rₕ S(t) A^{p+1} x`. The example `ritz_crankNicolson` composes the Ritz rate class on
`D(A³)` (`Ritz.toRateClass`, `RegScale.domainPow`) with Crank–Nicolson: the temporal error is
`1/12 tₙ τₕ² C ‖A³ x‖`, from static estimates only. `rate_uniform_iterates` needs no smooth
comparison: for every datum of a rate class in `D(A)` the error from `pₕ(0)` is the spatial rate
plus `O(τₕ^{p/(p+2)})` uniformly in `h` (the Crank–Nicolson example below: `τₕ^{1/2}`). The
trapezoidal remainder of the Dirichlet
Crank–Nicolson estimate of `Feec.Models.Cube.InhomogeneousError` is now
`Feec.TimeStepping.norm_trapezoid_le` (right derivatives, sharp constant `1/12`); `trapezoid_old`
states the old remainder verbatim and derives it. The Dirichlet scheme itself (inhomogeneous
boundary degrees of freedom, a weak solution against `V̊ₕ`) is not the orbit of a `DissipFEEC`, so
its estimate is not a corollary of the fully discrete verdict: `cn_old` states the conclusion of
`norm_cn_error_le` verbatim and derives it from the model theorem, which shares the trapezoidal
engine.

## The Einstein–Bianchi scheme (6.5)

The scheme (6.5) of [QuennevilleBelair2015] is one crime front: `ofComplexCrime` of the Galerkin
family of its elliptic core (`Feec.Instances.EinsteinBianchi.FEM.mirrorComplex`,
`Feec.Instances.EinsteinBianchi.FEM.standardCubeComplex`), with the verdicts
`Feec.Instances.EinsteinBianchi.MirrorFEMApprox.Verdict` and
`Feec.Instances.EinsteinBianchi.StandardCubeApprox.Verdict` (structures extending the verdict of
the approximating FEEC theorem by the instance-only fields). Gone are:

* the orbit cores `mirrorFEMCore`, `standardCubeCore` (the model convergence theorems read on the
  discretization, `mirrorFEM_hconv`, `standardCube_hconv`) and the orbit rate classes
  `mirrorFEMRate`, `mirrorFEMRateSobolev` (constants of the model rate theorems);
* the second route to the mirror verdict, through `ApproxComplexCrime.ofCochainDefect` with the
  hidden interpolants (`mirrorSplitComplex`): its discretization and core were, by definition,
  those of `mirrorComplex` (the same family `mirrorFamily`, constraint, filter and core data;
  checked by `rfl` before the deletion);
* the direct verdicts on the elliptic cores and the per-instance restatements of the verdict
  (`einsteinBianchi_mirrorFEM_converges`, `einsteinBianchi_standardCube_converges`, the crime
  front conjunctions and their rates), and the `Prop` abbreviations `MirrorFEMApproxVerdict`,
  `StandardCubeApproxVerdict` (with the `maxHeartbeats 2000000` of their proof).

The theorems `eb_old_*` state them verbatim, with the deleted definitions restated here with their
definitions unfolded (`mirrorFEMCore`, `standardCubeCore`: the orbit cores of
`ApproxFEEC.orbitCore`, whose model convergence hypothesis is now derived from the verdict,
`eb_old_mirrorFEM_hconv`, `eb_old_standardCube_hconv`; the orbit rate classes with the constants of
`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain` and
`mirror_waveFEM_rate_sobolev_of_add_two`, private), and `mirrorSplitComplex` unfolded to
`mirrorComplex` in `eb_old_mirrorFEM_ofCochainDefect`.

## The crown

The fields of the FEEC theorem (`ConformingFamily.feec`, `ConformingFamily.Verdict`) and of its
rated form (`ConformingFamily.feec_rated`) are the verdicts of the layer theorems: the examples of
the section on the crown fields check, by `type_of%`, that the type of each field is,
definitionally, the statement of the layer theorem it is read from (`staticFEEC`, `approxFEEC`,
`constrainedFEEC`, `heatFEEC`, `dissipFEEC_fullyDiscrete` for the θ-schemes, Crank–Nicolson and
every time scheme, `SkewFEEC.norm_S_sub_leapfrog_le`, `constrainedFEEC_perturbed`;
`ConformingFamily.rate`,
`ConstrainedFEEC.rate_le`, `ConstrainedFEEC.rate_heat`, `rate_smooth_iterates`). On the cube, the
heat verdict of `Feec.Models.Cube.FEM.crown_heat_nonvacuous` is a field of the crown of
`FEM.polyFamily`.

The crown gained a last field, `crime`: the FEEC theorem for approximating families with
variational crimes (`ApproxComplexCrime.feec`, whose fields are, by `type_of%`, the verdicts of
`approxFEEC_ofComplexCrime`, `dissipFEEC_fullyDiscrete` and `perturbFEEC`) on every conforming
window, read as the family with zero inner-product and cochain defects
(`ConformingFamily.windowCrime`, `ConstrainedFEEC.toCrime`). `OldVerdict` states the verdict
before it verbatim, and `crown_old_verdict` derives it from the new one.

## Spectral methods

The time-uniform truncation rates of reducing families and of spectral families, the
frequency-truncation theorems of `ℝᵈ` and the propagation-only `ℝ³` verdict `EuclideanVerdict` of
the Einstein–Bianchi system are the fields of the FEEC theorem for reducing families
(`ReducingFamily.feec`, `ReducingFamily.Verdict`: exactness on the bands, error = truncation error
of the datum, exact preservation of reducing constraints) and of the instance verdicts
`EuclideanBand.EuclideanEBVerdict`, `EuclideanBand.EuclideanMaxwellVerdict` that extend it; the
theorems `spectral_old_*` and `band_old_*` state the deleted results verbatim and derive them.

This file is part of the `FeecCheck` library, not of `Feec`: it is compiled by
`lake build FeecCheck` (and so by `lake exe feec-gate`) and fails that build if a conclusion is
dropped or a re-derivation breaks.
-/

public section

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


section GraphBoundOld

section Smoothed

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W} {S : H.Subcomplex} (Q : S.CommutingMap)
  [∀ i, FiniteDimensional 𝕜 (S.V i)]

/-- The old `Feec.HilbertComplex.Subcomplex.CommutingMap.norm_d_toCochainProjection_le`. -/
theorem graph_old_norm_d_toCochainProjection_le {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) {i j : ι} (x : (H.d i j).domain) :
    ‖H.d i j ⟨(Q.toCochainProjection hθ hQ).π i x,
        S.le_domain i j ((Q.toCochainProjection hθ hQ).mem i x)⟩‖ ≤
      (1 - θ)⁻¹ * ‖Q.Q j (H.d i j x)‖ := by
  rw [(Q.toCochainProjection hθ hQ).comm]
  exact Q.norm_toCochainProjection_le_norm_Q hθ hQ j _

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- The old `Feec.HilbertComplex.Subcomplex.CommutingMap.graph_le_of_norm_le`. -/
theorem graph_old_graph_le_of_norm_le {i j : ι} {C : ℝ} (hi : ∀ x, ‖Q.Q i x‖ ≤ C * ‖x‖)
    (hj : ∀ x, ‖Q.Q j x‖ ≤ C * ‖x‖) (x : (H.d i j).domain) :
    ‖Q.Q i x‖ ^ 2 + ‖H.d i j ⟨Q.Q i x, S.le_domain i j (Q.mem i x)⟩‖ ^ 2 ≤
      C ^ 2 * (‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2) := by
  rw [Q.comm]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hi x) 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (hj (H.d i j x)) 2
  nlinarith

/-- The old `Feec.HilbertComplex.Subcomplex.CommutingMap.isGraphBounded_toCochainProjection`. -/
theorem graph_old_isGraphBounded_toCochainProjection {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) {i j : ι} {C : ℝ}
    (hC : ∀ x : (H.d i j).domain, ‖Q.Q i x‖ ^ 2 +
      ‖H.d i j ⟨Q.Q i x, S.le_domain i j (Q.mem i x)⟩‖ ^ 2 ≤
        C ^ 2 * (‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2)) :
    (Q.toCochainProjection hθ hQ).IsGraphBounded i j ((1 - θ)⁻¹ * C) := by
  intro x
  have ha := Q.norm_toCochainProjection_le_norm_Q hθ hQ i x
  have hb := graph_old_norm_d_toCochainProjection_le Q hθ hQ x
  rw [← Q.comm i j x] at hb
  have hk : 0 ≤ (1 - θ)⁻¹ := inv_nonneg.2 (by linarith)
  have ha2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have := hC x
  calc _ ≤ ((1 - θ)⁻¹ * ‖Q.Q i x‖) ^ 2 +
        ((1 - θ)⁻¹ * ‖H.d i j ⟨Q.Q i x, S.le_domain i j (Q.mem i x)⟩‖) ^ 2 := add_le_add ha2 hb2
    _ = (1 - θ)⁻¹ ^ 2 * (‖Q.Q i x‖ ^ 2 +
        ‖H.d i j ⟨Q.Q i x, S.le_domain i j (Q.mem i x)⟩‖ ^ 2) := by ring
    _ ≤ (1 - θ)⁻¹ ^ 2 * (C ^ 2 * (‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

/-- The old
`Feec.HilbertComplex.Subcomplex.CommutingMap.isGraphBounded_toCochainProjection_of_norm_le`. -/
theorem graph_old_isGraphBounded_toCochainProjection_of_norm_le {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) {i j : ι} {C : ℝ}
    (hi : ∀ x, ‖Q.Q i x‖ ≤ C * ‖x‖) (hj : ∀ x, ‖Q.Q j x‖ ≤ C * ‖x‖) :
    (Q.toCochainProjection hθ hQ).IsGraphBounded i j ((1 - θ)⁻¹ * C) :=
  graph_old_isGraphBounded_toCochainProjection Q hθ hQ (graph_old_graph_le_of_norm_le Q hi hj)

end Smoothed

section ChainIso

variable {ι : Type*} {c : ComplexShape ι} {W W' : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace ℝ (W' i)] [∀ i, CompleteSpace (W' i)]
  {H : HilbertComplex ℝ c W} {H' : HilbertComplex ℝ c W'} {e : ∀ i, W i ≃L[ℝ] W' i}
  (hI : IsChainIso H H' e)
include hI

/-- The old `Feec.HilbertComplex.IsChainIso.isGraphBounded_comapProj`. -/
theorem graph_old_isGraphBounded_comapProj {S' : H'.Subcomplex} (S : H.Subcomplex) (hS)
    (P : S'.CochainProjection) {i j : ι}
    {C M M' : ℝ} (h : P.IsGraphBounded i j C)
    (hM : ∀ k, ‖(e k : W k →L[ℝ] W' k)‖ ≤ M)
    (hM' : ∀ k, ‖((e k).symm : W' k →L[ℝ] W k)‖ ≤ M') :
    (hI.comapProj S hS P).IsGraphBounded i j (M' * C * M) := by
  intro x
  have hx' : e i x ∈ (H'.d i j).domain := (hI.mem_domain_iff _ _ _).2 x.2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM i)
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' i)
  have hb := h ⟨_, hx'⟩
  set y : (H'.d i j).domain := ⟨P.π i (e i x), S'.le_domain i j (P.mem i _)⟩
  have hd : H.d i j ⟨(hI.comapProj S hS P).π i x,
      S.le_domain i j ((hI.comapProj S hS P).mem i x)⟩ = (e j).symm (H'.d i j y) :=
    hI.comm_symm i j y _
  have hdx : H'.d i j ⟨e i x, hx'⟩ = e j (H.d i j x) := hI.comm i j x hx'
  rw [hd, IsChainIso.comapProj_π]
  have n1 := ((e i).symm : W' i →L[ℝ] W i).le_of_opNorm_le (hM' i) (P.π i (e i x))
  have n2 := ((e j).symm : W' j →L[ℝ] W j).le_of_opNorm_le (hM' j) (H'.d i j y)
  have n3 := (e i : W i →L[ℝ] W' i).le_of_opNorm_le (hM i) x
  have n4 := (e j : W j →L[ℝ] W' j).le_of_opNorm_le (hM j) (H.d i j x)
  change ‖P.π i (e i x)‖ ^ 2 + ‖H'.d i j y‖ ^ 2 ≤
    C ^ 2 * (‖e i x‖ ^ 2 + ‖H'.d i j ⟨e i x, hx'⟩‖ ^ 2) at hb
  rw [hdx] at hb
  have s1 : ‖(e i).symm (P.π i (e i x))‖ ^ 2 ≤ M' ^ 2 * ‖P.π i (e i x)‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) n1 2
  have s2 : ‖(e j).symm (H'.d i j y)‖ ^ 2 ≤ M' ^ 2 * ‖H'.d i j y‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) n2 2
  have s3 : ‖e i x‖ ^ 2 ≤ M ^ 2 * ‖(x : W i)‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) n3 2
  have s4 : ‖e j (H.d i j x)‖ ^ 2 ≤ M ^ 2 * ‖H.d i j x‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) n4 2
  calc ‖(e i).symm (P.π i (e i x))‖ ^ 2 + ‖(e j).symm (H'.d i j y)‖ ^ 2
      ≤ M' ^ 2 * (‖P.π i (e i x)‖ ^ 2 + ‖H'.d i j y‖ ^ 2) := by nlinarith
    _ ≤ M' ^ 2 * (C ^ 2 * (‖e i x‖ ^ 2 + ‖e j (H.d i j x)‖ ^ 2)) := by gcongr
    _ ≤ M' ^ 2 * (C ^ 2 * (M ^ 2 * ‖(x : W i)‖ ^ 2 + M ^ 2 * ‖H.d i j x‖ ^ 2)) := by gcongr
    _ = (M' * C * M) ^ 2 * (‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2) := by ring

end ChainIso

end GraphBoundOld

section CubeOld

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM

variable {n : ℕ} [NeZero n]

/-- The old `Models.Cube.FEM.inv_two_pi_le_one`. -/
theorem cube_old_inv_two_pi_le_one : (2 * Real.pi)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by nlinarith [Real.two_le_pi])

omit [NeZero n] in
/-- The old `Models.Cube.FEM.poincare`. -/
theorem cube_old_poincare {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) {cP : ℝ}
    (hcP : (2 * Real.pi)⁻¹ ≤ cP) :
    ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖ := fun z hz =>
  (norm_le_of_mem_orthogonal_cycles hij z hz).trans
    (mul_le_mul_of_nonneg_right hcP (norm_nonneg _))

omit [NeZero n] in
/-- The old `Models.Cube.FEM.poincare_min`. -/
theorem cube_old_poincare_min {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) {cP : ℝ}
    (hcP : (2 * Real.pi)⁻¹ ≤ cP) :
    ∀ z : ((complexMin n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complexMin n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complexMin n).d i j z‖ := fun z hz =>
  (norm_le_of_mem_orthogonal_cycles_min hij z hz).trans
    (mul_le_mul_of_nonneg_right hcP (norm_nonneg _))

variable {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} in
/-- The old `Models.Cube.FEM.SmoothingEstimates.one_le_two_mul`. -/
theorem whitney_old_one_le_two_mul (hE : SmoothingEstimates n p C) : 1 ≤ 2 * C := by
  linarith [hE.half_le]

variable {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} in
/-- The old `Models.Cube.FEM.SmoothingEstimatesMin.one_le_two_mul`. -/
theorem whitneyMin_old_one_le_two_mul (hE : SmoothingEstimatesMin n p C) : 1 ≤ 2 * C := by
  linarith [hE.half_le]

variable {S : PolySeq} {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} in
/-- The old `Models.Cube.FEM.PolySmoothingEstimates.one_le_two_mul`. -/
theorem poly_old_one_le_two_mul (hE : PolySmoothingEstimates n S p C) : 1 ≤ 2 * C := by
  linarith [hE.half_le]

variable {S : PolySeq} {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} in
/-- The old `Models.Cube.FEM.PolySmoothingEstimatesMin.one_le_two_mul`. -/
theorem polyMin_old_one_le_two_mul (hE : PolySmoothingEstimatesMin n S p C) : 1 ≤ 2 * C := by
  linarith [hE.half_le]

/-- The old `Models.Cube.FEM.discretePoincare`. -/
theorem cube_old_discretePoincare : ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
    {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (whitney n N).V i),
    (∀ y ∈ (whitney n N).cyclesW i, inner ℝ y x = 0) →
      ‖x‖ ≤ c * ‖(complex n).d i j ⟨x, (whitney n N).le_domain i j hx⟩‖ :=
  (Feec.Models.Cube.FEM.whitneyFamily n).hasUniformProj.discretePoincare fun _ _ hij => norm_le_of_mem_orthogonal_cycles hij

/-- The old `Models.Cube.FEM.mixed_wellPosed`. -/
theorem cube_old_mixed_wellPosed : ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j →
    (ComplexShape.up ℤ).Rel j k → ∀ (N : ℕ) (f : (whitney n N).V j),
    (∃! x, (whitney n N).toHilbertComplex.mixedForm i j k x =
      (whitney n N).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (whitney n N).toHilbertComplex.MixedSpace i j,
      (whitney n N).toHilbertComplex.mixedForm i j k x =
        (whitney n N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  have := (Feec.Models.Cube.FEM.whitneyFamily n).finiteDimensional
  exact (Feec.Models.Cube.FEM.whitneyFamily n).hasUniformProj.mixed_wellPosed
    (fun _ _ hij => cube_old_poincare hij cube_old_inv_two_pi_le_one) le_rfl

/-- The old `Models.Cube.FEM.mixed_rate_smooth`. -/
theorem cube_old_mixed_rate_smooth {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) : ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)}
    {σ : (complex n).domainSpace i} {u : (complex n).domainSpace j} {q : (complex n).harmonic j},
    (complex n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsC2Form i L ((complex n).domainIncl i σ) →
    IsC2Form j L ((complex n).domainIncl j u) →
    IsC2Form j L ((complex n).domainIncl j
      ((complex n).boundaryPart j ((complex n).domainIncl j u))) →
    IsC2Form j L (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N :=
  by
  obtain ⟨K, hK⟩ := ((Feec.Models.Cube.FEM.whitneyFamily n).staticFEEC closedRangeAt j).rate (whitneyJackson n) () hij hjk
  refine ⟨K, fun hs _ hL hσ hu hb hq N => ?_⟩
  have h := hK hs hL hσ hu hb hq N
  simp only [whitneyFamily_V, whitneyJackson, Real.rpow_one] at h
  exact h

/-- The old `Models.Cube.FEM.smoothedProjection_uniform`. -/
theorem cube_old_smoothedProjection_uniform : ∃ (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ)
    (hE : SmoothingEstimates n p C),
    (∀ N i x, ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖) ∧ (∀ N i j, (hE.proj N).IsGraphBounded i j (2 * C)) ∧
    ∀ j, Tendsto (fun N => (hE.proj N).harmonicGap j) atTop (𝓝 0) :=
  let ⟨p, C, hE⟩ := smoothingEstimates_exists (n := n)
  ⟨p, C, hE, hE.norm_proj_le, fun N i j =>
    (hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j),
    fun _ => hE.family.tendsto_harmonicGap⟩

/-- The old `Models.Cube.FEM.mixed_quasiOptimal`. -/
theorem cube_old_mixed_quasiOptimal : ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j},
    (complex n).IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((whitney n N).domainSub i) +
        Metric.infDist u ((whitney n N).domainSub j) +
        Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitney n N).harmonicW j) +
        μ j N * Metric.infDist ((complex n).boundaryPart j ((complex n).domainIncl j u))
          ((whitney n N).domainSub j)) := by
  have := (Feec.Models.Cube.FEM.whitneyFamily n).finiteDimensional
  exact (Feec.Models.Cube.FEM.whitneyFamily n).hasUniformProj.mixed_quasiOptimal fun _ _ hij => norm_le_of_mem_orthogonal_cycles hij

/-- The old `Models.Cube.FEM.discretePoincare_min`. -/
theorem cube_old_discretePoincare_min : ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
    {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (whitneyMin n N).V i),
    (∀ y ∈ (whitneyMin n N).cyclesW i, inner ℝ y x = 0) →
      ‖x‖ ≤ c * ‖(complexMin n).d i j ⟨x, (whitneyMin n N).le_domain i j hx⟩‖ :=
  (Feec.Models.Cube.FEM.whitneyFamilyMin n).hasUniformProj.discretePoincare fun _ _ hij => norm_le_of_mem_orthogonal_cycles_min hij

/-- The old `Models.Cube.FEM.mixed_wellPosed_min`. -/
theorem cube_old_mixed_wellPosed_min : ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j →
    (ComplexShape.up ℤ).Rel j k → ∀ (N : ℕ) (f : (whitneyMin n N).V j),
    (∃! x, (whitneyMin n N).toHilbertComplex.mixedForm i j k x =
      (whitneyMin n N).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (whitneyMin n N).toHilbertComplex.MixedSpace i j,
      (whitneyMin n N).toHilbertComplex.mixedForm i j k x =
        (whitneyMin n N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  have := (Feec.Models.Cube.FEM.whitneyFamilyMin n).finiteDimensional
  exact (Feec.Models.Cube.FEM.whitneyFamilyMin n).hasUniformProj.mixed_wellPosed
    (fun _ _ hij => cube_old_poincare_min hij cube_old_inv_two_pi_le_one) le_rfl

/-- The old `Models.Cube.FEM.mixed_rate_smooth_min`. -/
theorem cube_old_mixed_rate_smooth_min {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) : ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)}
    {σ : (complexMin n).domainSpace i} {u : (complexMin n).domainSpace j}
    {q : (complexMin n).harmonic j},
    (complexMin n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsC2FormMin i L ((complexMin n).domainIncl i σ) →
    IsC2FormMin j L ((complexMin n).domainIncl j u) →
    IsC2FormMin j L ((complexMin n).domainIncl j
      ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))) →
    IsC2FormMin j L (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (whitneyMin n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).fst‖ +
        ‖u - (whitneyMin n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin n N) hij hjk f).snd.snd :
            (whitneyMin n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N :=
  by
  obtain ⟨K, hK⟩ := ((Feec.Models.Cube.FEM.whitneyFamilyMin n).staticFEEC closedRangeAt_min j).rate (whitneyJacksonMin n) () hij hjk
  refine ⟨K, fun hs _ hL hσ hu hb hq N => ?_⟩
  have h := hK hs hL hσ hu hb hq N
  simp only [whitneyFamilyMin_V, whitneyJacksonMin, Real.rpow_one] at h
  exact h

/-- The old `Models.Cube.FEM.smoothedProjection_uniform_min`. -/
theorem cube_old_smoothedProjection_uniform_min : ∃ (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ)
    (hE : SmoothingEstimatesMin n p C),
    (∀ N i x, ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖) ∧ (∀ N i j, (hE.proj N).IsGraphBounded i j (2 * C)) ∧
    ∀ j, Tendsto (fun N => (hE.proj N).harmonicGap j) atTop (𝓝 0) :=
  let ⟨p, C, hE⟩ := smoothingEstimatesMin_exists (n := n)
  ⟨p, C, hE, hE.norm_proj_le, fun N i j =>
    (hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j),
    fun _ => hE.family.tendsto_harmonicGap⟩

/-- The old `Models.Cube.FEM.mixed_quasiOptimal_min`. -/
theorem cube_old_mixed_quasiOptimal_min : ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j},
    (complexMin n).IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (whitneyMin n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).fst‖ +
        ‖u - (whitneyMin n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin n N) hij hjk f).snd.snd :
            (whitneyMin n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((whitneyMin n N).domainSub i) +
        Metric.infDist u ((whitneyMin n N).domainSub j) +
        Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitneyMin n N).harmonicW j) +
        μ j N * Metric.infDist ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))
          ((whitneyMin n N).domainSub j)) := by
  have := (Feec.Models.Cube.FEM.whitneyFamilyMin n).finiteDimensional
  exact (Feec.Models.Cube.FEM.whitneyFamilyMin n).hasUniformProj.mixed_quasiOptimal fun _ _ hij => norm_le_of_mem_orthogonal_cycles_min hij

/-- The old `Models.Cube.FEM.polySmoothedProjection_uniform`. -/
theorem cube_old_polySmoothedProjection_uniform (S : PolySeq) :
    ∃ (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ) (hE : PolySmoothingEstimates n S p C),
      (∀ N i x, ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖) ∧
      (∀ N i j, (hE.proj N).IsGraphBounded i j (2 * C)) ∧
      ∀ j, Tendsto (fun N => (hE.proj N).harmonicGap j) atTop (𝓝 0) :=
  let ⟨p, C, hE⟩ := polySmoothingEstimates_exists (n := n) S
  ⟨p, C, hE, hE.norm_proj_le, fun N i j =>
    (hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j),
    fun _ => hE.family.tendsto_harmonicGap⟩

/-- The old `Models.Cube.FEM.polySmoothedProjection_uniform_min`. -/
theorem cube_old_polySmoothedProjection_uniform_min (S : PolySeq) :
    ∃ (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ) (hE : PolySmoothingEstimatesMin n S p C),
      (∀ N i x, ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖) ∧
      (∀ N i j, (hE.proj N).IsGraphBounded i j (2 * C)) ∧
      ∀ j, Tendsto (fun N => (hE.proj N).harmonicGap j) atTop (𝓝 0) :=
  let ⟨p, C, hE⟩ := polySmoothingEstimatesMin_exists (n := n) S
  ⟨p, C, hE, hE.norm_proj_le, fun N i j =>
    (hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j),
    fun _ => hE.family.tendsto_harmonicGap⟩

/-- The old `Models.Cube.FEM.discretePoincare_poly`. -/
theorem cube_old_discretePoincare_poly (S : PolySeq) : ∃ c : ℝ, ∀ {i j : ℤ},
    (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ) {x : L2F ℝ (cubeDomain n) (formIdx n i)}
    (hx : x ∈ (poly n S N).V i), (∀ y ∈ (poly n S N).cyclesW i, inner ℝ y x = 0) →
      ‖x‖ ≤ c * ‖(complex n).d i j ⟨x, (poly n S N).le_domain i j hx⟩‖ :=
  (polyFamily n S).hasUniformProj.discretePoincare fun _ _ hij => norm_le_of_mem_orthogonal_cycles hij

/-- The old `Models.Cube.FEM.discretePoincare_polyMin`. -/
theorem cube_old_discretePoincare_polyMin (S : PolySeq) : ∃ c : ℝ, ∀ {i j : ℤ},
    (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ) {x : L2F ℝ (cubeDomain n) (formIdx n i)}
    (hx : x ∈ (polyMin n S N).V i), (∀ y ∈ (polyMin n S N).cyclesW i, inner ℝ y x = 0) →
      ‖x‖ ≤ c * ‖(complexMin n).d i j ⟨x, (polyMin n S N).le_domain i j hx⟩‖ :=
  (polyFamilyMin n S).hasUniformProj.discretePoincare fun _ _ hij => norm_le_of_mem_orthogonal_cycles_min hij

/-- The old `Models.Cube.FEM.mixed_wellPosed_poly`. -/
theorem cube_old_mixed_wellPosed_poly (S : PolySeq) : ∃ C : ℝ, ∀ {i j k : ℤ},
    (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k → ∀ (N : ℕ) (f : (poly n S N).V j),
    (∃! x, (poly n S N).toHilbertComplex.mixedForm i j k x =
      (poly n S N).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (poly n S N).toHilbertComplex.MixedSpace i j,
      (poly n S N).toHilbertComplex.mixedForm i j k x =
        (poly n S N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  have := (polyFamily n S).finiteDimensional
  exact (polyFamily n S).hasUniformProj.mixed_wellPosed
    (fun _ _ hij => cube_old_poincare hij cube_old_inv_two_pi_le_one) le_rfl

/-- The old `Models.Cube.FEM.mixed_wellPosed_polyMin`. -/
theorem cube_old_mixed_wellPosed_polyMin (S : PolySeq) : ∃ C : ℝ, ∀ {i j k : ℤ},
    (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k → ∀ (N : ℕ)
    (f : (polyMin n S N).V j),
    (∃! x, (polyMin n S N).toHilbertComplex.mixedForm i j k x =
      (polyMin n S N).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (polyMin n S N).toHilbertComplex.MixedSpace i j,
      (polyMin n S N).toHilbertComplex.mixedForm i j k x =
        (polyMin n S N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  have := (polyFamilyMin n S).finiteDimensional
  exact (polyFamilyMin n S).hasUniformProj.mixed_wellPosed
    (fun _ _ hij => cube_old_poincare_min hij cube_old_inv_two_pi_le_one) le_rfl

/-- The old `Models.Cube.FEM.mixed_quasiOptimal_poly`. -/
theorem cube_old_mixed_quasiOptimal_poly (S : PolySeq) :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j},
    (complex n).IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (poly n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).fst‖ +
        ‖u - (poly n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n S N) hij hjk f).snd.snd :
            (poly n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((poly n S N).domainSub i) +
        Metric.infDist u ((poly n S N).domainSub j) +
        Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((poly n S N).harmonicW j) +
        μ j N * Metric.infDist ((complex n).boundaryPart j ((complex n).domainIncl j u))
          ((poly n S N).domainSub j)) := by
  have := (polyFamily n S).finiteDimensional
  exact (polyFamily n S).hasUniformProj.mixed_quasiOptimal fun _ _ hij => norm_le_of_mem_orthogonal_cycles hij

/-- The old `Models.Cube.FEM.mixed_quasiOptimal_polyMin`. -/
theorem cube_old_mixed_quasiOptimal_polyMin (S : PolySeq) :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j},
    (complexMin n).IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (polyMin n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).fst‖ +
        ‖u - (polyMin n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyMin n S N) hij hjk f).snd.snd :
            (polyMin n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((polyMin n S N).domainSub i) +
        Metric.infDist u ((polyMin n S N).domainSub j) +
        Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((polyMin n S N).harmonicW j) +
        μ j N * Metric.infDist ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))
          ((polyMin n S N).domainSub j)) := by
  have := (polyFamilyMin n S).finiteDimensional
  exact (polyFamilyMin n S).hasUniformProj.mixed_quasiOptimal fun _ _ hij => norm_le_of_mem_orthogonal_cycles_min hij


end CubeOld

section CubeTowerOld

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM

variable {n : ℕ} [NeZero n]

section Whitney

variable {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ}

section Max

variable (hE : SmoothingEstimates n p C)
include hE

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.isGraphBounded_proj`. -/
theorem whitney_old_isGraphBounded_proj (N : ℕ) (i j : ℤ) : (hE.proj N).IsGraphBounded i j (2 * C) :=
  (hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j)

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.norm_le_of_forall_inner_eq_zero`. -/
theorem whitney_old_norm_le_of_forall_inner_eq_zero {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) {cP : ℝ}
    (hP : ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖)
    (N : ℕ) {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (whitney n N).V i)
    (hxo : ∀ y ∈ (whitney n N).cyclesW i, inner ℝ y x = 0) :
    ‖x‖ ≤ 2 * C * cP * ‖(complex n).d i j ⟨x, (whitney n N).le_domain i j hx⟩‖ :=
  (hE.proj N).norm_le_of_forall_inner_eq_zero hij hP hE.two_mul_nonneg (hE.norm_proj_le N i) hx
    hxo

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.existsUnique_mixed`. -/
theorem whitney_old_existsUnique_mixed {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ} (hcP : 1 ≤ cP)
    (hPi : ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖)
    (hPj : ∀ z : ((complex n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complex n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complex n).d j k z‖)
    (N : ℕ) (f : (whitney n N).V j) :
    ∃! x, (whitney n N).toHilbertComplex.mixedForm i j k x =
      (whitney n N).toHilbertComplex.mixedRHS i j f :=
  (hE.proj N).existsUnique_mixed hij hjk hcP (by linarith [hE.half_le]) hPi hPj (hE.norm_proj_le N i)
    (hE.norm_proj_le N j) f

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.norm_le_of_mixed`. -/
theorem whitney_old_norm_le_of_mixed {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ} (hcP : 1 ≤ cP)
    (hPi : ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖)
    (hPj : ∀ z : ((complex n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complex n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complex n).d j k z‖)
    (N : ℕ) {f : (whitney n N).V j} {x : (whitney n N).toHilbertComplex.MixedSpace i j}
    (hx : (whitney n N).toHilbertComplex.mixedForm i j k x =
      (whitney n N).toHilbertComplex.mixedRHS i j f) :
    ‖x‖ ≤ 16 * (2 * C * cP) ^ 2 * ‖f‖ :=
  (hE.proj N).norm_le_of_mixed hij hjk hcP (by linarith [hE.half_le]) hPi hPj (hE.norm_proj_le N i)
    (hE.norm_proj_le N j) hx

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.norm_sub_le_infDist`. -/
theorem whitney_old_norm_sub_le_infDist {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ}
    (hPi : ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖)
    (hPj : ∀ z : ((complex n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complex n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complex n).d j k z‖)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) (N : ℕ) :
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) *
        (Metric.infDist σ ((whitney n N).domainSub i) + Metric.infDist u ((whitney n N).domainSub j) +
          Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitney n N).harmonicW j) +
          (hE.proj N).harmonicGap j *
            Metric.infDist ((complex n).boundaryPart j ((complex n).domainIncl j u))
              ((whitney n N).domainSub j)) :=
  (hE.proj N).norm_sub_le_infDist_harmonicGap hij hjk (by linarith [hE.half_le]) hPi hPj
    (whitney_old_isGraphBounded_proj hE N i j) (whitney_old_isGraphBounded_proj hE N j k) hs

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.norm_sub_le_meshSize`. -/
theorem whitney_old_norm_sub_le_meshSize {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ}
    (hPi : ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖)
    (hPj : ∀ z : ((complex n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complex n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complex n).d j k z‖)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) {K : ℝ} (N : ℕ)
    (hσ : Metric.infDist σ ((whitney n N).domainSub i) ≤ K * meshSize N)
    (hu : Metric.infDist u ((whitney n N).domainSub j) ≤ K * meshSize N)
    (hq : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitney n N).harmonicW j) ≤
      K * meshSize N)
    (hB : Metric.infDist ((complex n).boundaryPart j ((complex n).domainIncl j u))
      ((whitney n N).domainSub j) ≤ K * meshSize N) :
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K * meshSize N := by
  have hμ0 : 0 ≤ 1 + 2 * C := by linarith [hE.two_mul_nonneg]
  have h := (hE.proj N).norm_sub_le_infDist hij hjk (by linarith [hE.half_le]) hμ0 hPi hPj
    (whitney_old_isGraphBounded_proj hE N i j) (whitney_old_isGraphBounded_proj hE N j k)
    (fun _ hq' => (hE.proj N).norm_sub_π_harmonic_le hjk hE.two_mul_nonneg
      (whitney_old_isGraphBounded_proj hE N j k) hq') hs
  refine h.trans ?_
  have hK0 : 0 ≤ (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) := by
    have := hE.two_mul_nonneg; positivity
  have e : (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K *
      meshSize N = (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) *
        ((4 + 2 * C) * (K * meshSize N)) := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  have hB' := mul_le_mul_of_nonneg_left hB hμ0
  have e' : (4 + 2 * C) * (K * meshSize N) =
      3 * (K * meshSize N) + (1 + 2 * C) * (K * meshSize N) := by ring
  rw [e']
  linarith

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.tendsto_harmonicGap`. -/
theorem whitney_old_tendsto_harmonicGap {j : ℤ} [FiniteDimensional ℝ ((complex n).harmonic j)]
    (happrox : ∀ q ∈ (complex n).harmonic j,
      Tendsto (fun N => Metric.infDist q ((whitney n N).V j :
        Set (L2F ℝ (cubeDomain n) (formIdx n j)))) atTop (𝓝 0)) :
    Tendsto (fun N => (hE.proj N).harmonicGap j) atTop (𝓝 0) :=
  Subcomplex.CochainProjection.tendsto_harmonicGap hE.proj hE.two_mul_nonneg
    (fun N x => hE.norm_proj_le N j x) happrox

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.norm_le_of_forall_inner_eq_zero'`. -/
theorem whitney_old_norm_le_of_forall_inner_eq_zero' {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (N : ℕ)
    {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (whitney n N).V i)
    (hxo : ∀ y ∈ (whitney n N).cyclesW i, inner ℝ y x = 0) :
    ‖x‖ ≤ 2 * C * (2 * Real.pi)⁻¹ *
      ‖(complex n).d i j ⟨x, (whitney n N).le_domain i j hx⟩‖ :=
  whitney_old_norm_le_of_forall_inner_eq_zero hE hij (norm_le_of_mem_orthogonal_cycles hij) N hx hxo

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.existsUnique_mixed'`. -/
theorem whitney_old_existsUnique_mixed' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) (N : ℕ) (f : (whitney n N).V j) :
    ∃! x, (whitney n N).toHilbertComplex.mixedForm i j k x =
      (whitney n N).toHilbertComplex.mixedRHS i j f :=
  whitney_old_existsUnique_mixed hE hij hjk le_rfl (cube_old_poincare hij cube_old_inv_two_pi_le_one)
    (cube_old_poincare hjk cube_old_inv_two_pi_le_one) N f

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.norm_le_of_mixed'`. -/
theorem whitney_old_norm_le_of_mixed' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) (N : ℕ) {f : (whitney n N).V j}
    {x : (whitney n N).toHilbertComplex.MixedSpace i j}
    (hx : (whitney n N).toHilbertComplex.mixedForm i j k x =
      (whitney n N).toHilbertComplex.mixedRHS i j f) :
    ‖x‖ ≤ 16 * (2 * C * 1) ^ 2 * ‖f‖ :=
  whitney_old_norm_le_of_mixed hE hij hjk le_rfl (cube_old_poincare hij cube_old_inv_two_pi_le_one)
    (cube_old_poincare hjk cube_old_inv_two_pi_le_one) N hx

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.norm_sub_le_infDist'`. -/
theorem whitney_old_norm_sub_le_infDist' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {f : L2F ℝ (cubeDomain n) (formIdx n j)}
    {σ : (complex n).domainSpace i} {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) (N : ℕ) :
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) *
        (Metric.infDist σ ((whitney n N).domainSub i) + Metric.infDist u ((whitney n N).domainSub j) +
          Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitney n N).harmonicW j) +
          (hE.proj N).harmonicGap j *
            Metric.infDist ((complex n).boundaryPart j ((complex n).domainIncl j u))
              ((whitney n N).domainSub j)) :=
  whitney_old_norm_sub_le_infDist hE hij hjk (norm_le_of_mem_orthogonal_cycles hij)
    (norm_le_of_mem_orthogonal_cycles hjk) hs N

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.norm_sub_le_meshSize'`. -/
theorem whitney_old_norm_sub_le_meshSize' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {f : L2F ℝ (cubeDomain n) (formIdx n j)}
    {σ : (complex n).domainSpace i} {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) {K : ℝ} (N : ℕ)
    (hσ : Metric.infDist σ ((whitney n N).domainSub i) ≤ K * meshSize N)
    (hu : Metric.infDist u ((whitney n N).domainSub j) ≤ K * meshSize N)
    (hq : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitney n N).harmonicW j) ≤
      K * meshSize N)
    (hB : Metric.infDist ((complex n).boundaryPart j ((complex n).domainIncl j u))
      ((whitney n N).domainSub j) ≤ K * meshSize N) :
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K *
        meshSize N :=
  whitney_old_norm_sub_le_meshSize hE hij hjk (norm_le_of_mem_orthogonal_cycles hij)
    (norm_le_of_mem_orthogonal_cycles hjk) hs N hσ hu hq hB

end Max

section Min

variable (hE : SmoothingEstimatesMin n p C)
include hE

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimatesMin.isGraphBounded_proj`. -/
theorem whitneyMin_old_isGraphBounded_proj (N : ℕ) (i j : ℤ) : (hE.proj N).IsGraphBounded i j (2 * C) :=
  (hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j)

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimatesMin.norm_le_of_forall_inner_eq_zero`. -/
theorem whitneyMin_old_norm_le_of_forall_inner_eq_zero {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) {cP : ℝ}
    (hP : ∀ z : ((complexMin n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complexMin n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complexMin n).d i j z‖)
    (N : ℕ) {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (whitneyMin n N).V i)
    (hxo : ∀ y ∈ (whitneyMin n N).cyclesW i, inner ℝ y x = 0) :
    ‖x‖ ≤ 2 * C * cP * ‖(complexMin n).d i j ⟨x, (whitneyMin n N).le_domain i j hx⟩‖ :=
  (hE.proj N).norm_le_of_forall_inner_eq_zero hij hP hE.two_mul_nonneg (hE.norm_proj_le N i) hx
    hxo

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimatesMin.existsUnique_mixed`. -/
theorem whitneyMin_old_existsUnique_mixed {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ} (hcP : 1 ≤ cP)
    (hPi : ∀ z : ((complexMin n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complexMin n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complexMin n).d i j z‖)
    (hPj : ∀ z : ((complexMin n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complexMin n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complexMin n).d j k z‖)
    (N : ℕ) (f : (whitneyMin n N).V j) :
    ∃! x, (whitneyMin n N).toHilbertComplex.mixedForm i j k x =
      (whitneyMin n N).toHilbertComplex.mixedRHS i j f :=
  (hE.proj N).existsUnique_mixed hij hjk hcP (by linarith [hE.half_le]) hPi hPj (hE.norm_proj_le N i)
    (hE.norm_proj_le N j) f

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimatesMin.norm_le_of_mixed`. -/
theorem whitneyMin_old_norm_le_of_mixed {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ} (hcP : 1 ≤ cP)
    (hPi : ∀ z : ((complexMin n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complexMin n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complexMin n).d i j z‖)
    (hPj : ∀ z : ((complexMin n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complexMin n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complexMin n).d j k z‖)
    (N : ℕ) {f : (whitneyMin n N).V j} {x : (whitneyMin n N).toHilbertComplex.MixedSpace i j}
    (hx : (whitneyMin n N).toHilbertComplex.mixedForm i j k x =
      (whitneyMin n N).toHilbertComplex.mixedRHS i j f) :
    ‖x‖ ≤ 16 * (2 * C * cP) ^ 2 * ‖f‖ :=
  (hE.proj N).norm_le_of_mixed hij hjk hcP (by linarith [hE.half_le]) hPi hPj (hE.norm_proj_le N i)
    (hE.norm_proj_le N j) hx

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimatesMin.tendsto_harmonicGap`. -/
theorem whitneyMin_old_tendsto_harmonicGap {j : ℤ} [FiniteDimensional ℝ ((complexMin n).harmonic j)]
    (happrox : ∀ q ∈ (complexMin n).harmonic j,
      Tendsto (fun N => Metric.infDist q ((whitneyMin n N).V j :
        Set (L2F ℝ (cubeDomain n) (formIdx n j)))) atTop (𝓝 0)) :
    Tendsto (fun N => (hE.proj N).harmonicGap j) atTop (𝓝 0) :=
  Subcomplex.CochainProjection.tendsto_harmonicGap hE.proj hE.two_mul_nonneg
    (fun N x => hE.norm_proj_le N j x) happrox

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimatesMin.norm_le_of_forall_inner_eq_zero'`. -/
theorem whitneyMin_old_norm_le_of_forall_inner_eq_zero' {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (N : ℕ)
    {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (whitneyMin n N).V i)
    (hxo : ∀ y ∈ (whitneyMin n N).cyclesW i, inner ℝ y x = 0) :
    ‖x‖ ≤ 2 * C * (2 * Real.pi)⁻¹ *
      ‖(complexMin n).d i j ⟨x, (whitneyMin n N).le_domain i j hx⟩‖ :=
  whitneyMin_old_norm_le_of_forall_inner_eq_zero hE hij (norm_le_of_mem_orthogonal_cycles_min hij) N hx hxo

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimatesMin.existsUnique_mixed'`. -/
theorem whitneyMin_old_existsUnique_mixed' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) (N : ℕ) (f : (whitneyMin n N).V j) :
    ∃! x, (whitneyMin n N).toHilbertComplex.mixedForm i j k x =
      (whitneyMin n N).toHilbertComplex.mixedRHS i j f :=
  whitneyMin_old_existsUnique_mixed hE hij hjk le_rfl (cube_old_poincare_min hij cube_old_inv_two_pi_le_one)
    (cube_old_poincare_min hjk cube_old_inv_two_pi_le_one) N f

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimatesMin.norm_le_of_mixed'`. -/
theorem whitneyMin_old_norm_le_of_mixed' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) (N : ℕ) {f : (whitneyMin n N).V j}
    {x : (whitneyMin n N).toHilbertComplex.MixedSpace i j}
    (hx : (whitneyMin n N).toHilbertComplex.mixedForm i j k x =
      (whitneyMin n N).toHilbertComplex.mixedRHS i j f) :
    ‖x‖ ≤ 16 * (2 * C * 1) ^ 2 * ‖f‖ :=
  whitneyMin_old_norm_le_of_mixed hE hij hjk le_rfl (cube_old_poincare_min hij cube_old_inv_two_pi_le_one)
    (cube_old_poincare_min hjk cube_old_inv_two_pi_le_one) N hx

end Min

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.norm_sub_le_meshSize_smooth`. -/
theorem whitney_old_norm_sub_le_meshSize_smooth {p : ℕ → SmoothingParam (Fin n → ℝ)}
    {C : ℝ} (hE : SmoothingEstimates n p C) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ}
    (hPi : ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖)
    (hPj : ∀ z : ((complex n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complex n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complex n).d j k z‖)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) {L : ℝ} (hL0 : 0 ≤ L)
    (hσ : IsC2Form i L ((complex n).domainIncl i σ))
    (hu : IsC2Form j L ((complex n).domainIncl j u))
    (hB : IsC2Form j L ((complex n).domainIncl j
      ((complex n).boundaryPart j ((complex n).domainIncl j u))))
    (hq : IsC2Form j L (q : L2F ℝ (cubeDomain n) (formIdx n j))) (N : ℕ) :
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
        ((1 + 2 * C) * (interpBound n i + interpBound n j) * L) * meshSize N := by
  have hC := hE.two_mul_nonneg
  have hh := (meshSize_pos N).le
  have hBi := interpBound_nonneg n i
  have hBj := interpBound_nonneg n j
  have hiL := mul_nonneg (mul_nonneg hBi hL0) hh
  have hjL := mul_nonneg (mul_nonneg hBj hL0) hh
  have hK : (1 + 2 * C) * (interpBound n i + interpBound n j) * L * meshSize N =
      (1 + 2 * C) * (interpBound n i * L * meshSize N) +
        (1 + 2 * C) * (interpBound n j * L * meshSize N) := by ring
  have hi : interpBound n i * L * meshSize N ≤
      (1 + 2 * C) * (interpBound n i + interpBound n j) * L * meshSize N := by
    rw [hK]; nlinarith
  have hj : interpBound n j * L * meshSize N ≤
      (1 + 2 * C) * (interpBound n i + interpBound n j) * L * meshSize N := by
    rw [hK]; nlinarith
  have hq' : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j))
      ((whitney n N).harmonicW j) ≤
      (1 + 2 * C) * (interpBound n i + interpBound n j) * L * meshSize N := by
    refine ((hE.proj N).infDist_harmonicW_le hjk hC (whitney_old_isGraphBounded_proj hE N j k) q.2).trans ?_
    have h := IsC2Form.infDist_domainSub_whitney_le
      (σ := cyclesToDomainSpace ((complex n).harmonic_le_cycles j q.2)) hq hL0 N
    rw [hK]
    have : 0 ≤ 1 + 2 * C := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h this]
  exact whitney_old_norm_sub_le_meshSize hE hij hjk hPi hPj hs N
    ((hσ.infDist_domainSub_whitney_le hL0 N).trans hi)
    ((hu.infDist_domainSub_whitney_le hL0 N).trans hj) hq'
    ((hB.infDist_domainSub_whitney_le hL0 N).trans hj)

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.tendsto_harmonicGap_whitney`. -/
theorem whitney_old_tendsto_harmonicGap_whitney {p : ℕ → SmoothingParam (Fin n → ℝ)}
    {C : ℝ} (hE : SmoothingEstimates n p C) {j : ℤ}
    [FiniteDimensional ℝ ((complex n).harmonic j)] :
    Tendsto (fun N => (hE.proj N).harmonicGap j) atTop (𝓝 0) :=
  whitney_old_tendsto_harmonicGap hE fun q _ => tendsto_infDist_whitney j q

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimatesMin.norm_sub_le_meshSize`. -/
theorem whitneyMin_old_norm_sub_le_meshSize {p : ℕ → SmoothingParam (Fin n → ℝ)}
    {C : ℝ} (hE : SmoothingEstimatesMin n p C) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ}
    (hPi : ∀ z : ((complexMin n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complexMin n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complexMin n).d i j z‖)
    (hPj : ∀ z : ((complexMin n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complexMin n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complexMin n).d j k z‖)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j}
    (hs : (complexMin n).IsMixedSolution i j k f σ u q) {K : ℝ} (N : ℕ)
    (hσ : Metric.infDist σ ((whitneyMin n N).domainSub i) ≤ K * meshSize N)
    (hu : Metric.infDist u ((whitneyMin n N).domainSub j) ≤ K * meshSize N)
    (hq : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitneyMin n N).harmonicW j) ≤
      K * meshSize N)
    (hB : Metric.infDist ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))
      ((whitneyMin n N).domainSub j) ≤ K * meshSize N) :
    ‖σ - (whitneyMin n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).fst‖ +
        ‖u - (whitneyMin n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin n N) hij hjk f).snd.snd :
            (whitneyMin n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K * meshSize N := by
  have hμ0 : 0 ≤ 1 + 2 * C := by linarith [hE.two_mul_nonneg]
  have h := (hE.proj N).norm_sub_le_infDist hij hjk (by linarith [hE.half_le]) hμ0 hPi hPj
    (whitneyMin_old_isGraphBounded_proj hE N i j) (whitneyMin_old_isGraphBounded_proj hE N j k)
    (fun _ hq' => (hE.proj N).norm_sub_π_harmonic_le hjk hE.two_mul_nonneg
      (whitneyMin_old_isGraphBounded_proj hE N j k) hq') hs
  refine h.trans ?_
  have hK0 : 0 ≤ (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) := by
    have := hE.two_mul_nonneg; positivity
  have e : (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K *
      meshSize N = (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) *
        ((4 + 2 * C) * (K * meshSize N)) := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  have hB' := mul_le_mul_of_nonneg_left hB hμ0
  have e' : (4 + 2 * C) * (K * meshSize N) =
      3 * (K * meshSize N) + (1 + 2 * C) * (K * meshSize N) := by ring
  rw [e']
  linarith

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimatesMin.norm_sub_le_meshSize_smooth`. -/
theorem whitneyMin_old_norm_sub_le_meshSize_smooth {p : ℕ → SmoothingParam (Fin n → ℝ)}
    {C : ℝ} (hE : SmoothingEstimatesMin n p C) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ}
    (hPi : ∀ z : ((complexMin n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complexMin n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complexMin n).d i j z‖)
    (hPj : ∀ z : ((complexMin n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complexMin n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complexMin n).d j k z‖)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j}
    (hs : (complexMin n).IsMixedSolution i j k f σ u q) {L : ℝ} (hL0 : 0 ≤ L)
    (hσ : IsC2FormMin i L ((complexMin n).domainIncl i σ))
    (hu : IsC2FormMin j L ((complexMin n).domainIncl j u))
    (hB : IsC2FormMin j L ((complexMin n).domainIncl j
      ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))))
    (hq : IsC2FormMin j L (q : L2F ℝ (cubeDomain n) (formIdx n j))) (N : ℕ) :
    ‖σ - (whitneyMin n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).fst‖ +
        ‖u - (whitneyMin n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin n N) hij hjk f).snd.snd :
            (whitneyMin n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
        (2 * ((1 + 2 * C) * (interpBound n i + interpBound n j) * L)) * meshSize N := by
  have hC := hE.two_mul_nonneg
  have hh := (meshSize_pos N).le
  have hBi := interpBound_nonneg n i
  have hBj := interpBound_nonneg n j
  have hiL := mul_nonneg (mul_nonneg hBi hL0) hh
  have hjL := mul_nonneg (mul_nonneg hBj hL0) hh
  have hK : 2 * ((1 + 2 * C) * (interpBound n i + interpBound n j) * L) * meshSize N =
      2 * ((1 + 2 * C) * (interpBound n i * L * meshSize N)) +
        2 * ((1 + 2 * C) * (interpBound n j * L * meshSize N)) := by ring
  have hi : 2 * (interpBound n i * L * meshSize N) ≤
      2 * ((1 + 2 * C) * (interpBound n i + interpBound n j) * L) * meshSize N := by
    rw [hK]; nlinarith
  have hj : 2 * (interpBound n j * L * meshSize N) ≤
      2 * ((1 + 2 * C) * (interpBound n i + interpBound n j) * L) * meshSize N := by
    rw [hK]; nlinarith
  have hq' : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j))
      ((whitneyMin n N).harmonicW j) ≤
      2 * ((1 + 2 * C) * (interpBound n i + interpBound n j) * L) * meshSize N := by
    refine ((hE.proj N).infDist_harmonicW_le hjk hC (whitneyMin_old_isGraphBounded_proj hE N j k) q.2).trans ?_
    have h := IsC2FormMin.infDist_domainSub_whitneyMin_le
      (σ := cyclesToDomainSpace ((complexMin n).harmonic_le_cycles j q.2)) hq hL0 N
    rw [hK]
    have : 0 ≤ 1 + 2 * C := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h this]
  exact whitneyMin_old_norm_sub_le_meshSize hE hij hjk hPi hPj hs N
    ((hσ.infDist_domainSub_whitneyMin_le hL0 N).trans hi)
    ((hu.infDist_domainSub_whitneyMin_le hL0 N).trans hj) hq'
    ((hB.infDist_domainSub_whitneyMin_le hL0 N).trans hj)

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimatesMin.tendsto_harmonicGap_whitney`. -/
theorem whitneyMin_old_tendsto_harmonicGap_whitney {p : ℕ → SmoothingParam (Fin n → ℝ)}
    {C : ℝ} (hE : SmoothingEstimatesMin n p C) {j : ℤ}
    [FiniteDimensional ℝ ((complexMin n).harmonic j)] :
    Tendsto (fun N => (hE.proj N).harmonicGap j) atTop (𝓝 0) :=
  whitneyMin_old_tendsto_harmonicGap hE fun q _ => tendsto_infDist_whitneyMin j q

section Max

variable (hE : SmoothingEstimates n p C)
include hE

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimates.norm_sub_le_meshSize_smooth'`. -/
theorem whitney_old_norm_sub_le_meshSize_smooth' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) {L : ℝ} (hL0 : 0 ≤ L)
    (hσ : IsC2Form i L ((complex n).domainIncl i σ))
    (hu : IsC2Form j L ((complex n).domainIncl j u))
    (hB : IsC2Form j L ((complex n).domainIncl j
      ((complex n).boundaryPart j ((complex n).domainIncl j u))))
    (hq : IsC2Form j L (q : L2F ℝ (cubeDomain n) (formIdx n j))) (N : ℕ) :
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
        ((1 + 2 * C) * (interpBound n i + interpBound n j) * L) * meshSize N :=
  whitney_old_norm_sub_le_meshSize_smooth hE hij hjk (norm_le_of_mem_orthogonal_cycles hij)
    (norm_le_of_mem_orthogonal_cycles hjk) hs hL0 hσ hu hB hq N

end Max

section Min

variable (hE : SmoothingEstimatesMin n p C)
include hE

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimatesMin.norm_sub_le_meshSize'`. -/
theorem whitneyMin_old_norm_sub_le_meshSize' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j}
    (hs : (complexMin n).IsMixedSolution i j k f σ u q) {K : ℝ} (N : ℕ)
    (hσ : Metric.infDist σ ((whitneyMin n N).domainSub i) ≤ K * meshSize N)
    (hu : Metric.infDist u ((whitneyMin n N).domainSub j) ≤ K * meshSize N)
    (hq : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitneyMin n N).harmonicW j) ≤
      K * meshSize N)
    (hB : Metric.infDist ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))
      ((whitneyMin n N).domainSub j) ≤ K * meshSize N) :
    ‖σ - (whitneyMin n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).fst‖ +
        ‖u - (whitneyMin n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin n N) hij hjk f).snd.snd :
            (whitneyMin n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K *
        meshSize N :=
  whitneyMin_old_norm_sub_le_meshSize hE hij hjk (norm_le_of_mem_orthogonal_cycles_min hij)
    (norm_le_of_mem_orthogonal_cycles_min hjk) hs N hσ hu hq hB

/-- The old `Feec.Models.Cube.FEM.SmoothingEstimatesMin.norm_sub_le_meshSize_smooth'`. -/
theorem whitneyMin_old_norm_sub_le_meshSize_smooth' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j}
    (hs : (complexMin n).IsMixedSolution i j k f σ u q) {L : ℝ} (hL0 : 0 ≤ L)
    (hσ : IsC2FormMin i L ((complexMin n).domainIncl i σ))
    (hu : IsC2FormMin j L ((complexMin n).domainIncl j u))
    (hB : IsC2FormMin j L ((complexMin n).domainIncl j
      ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))))
    (hq : IsC2FormMin j L (q : L2F ℝ (cubeDomain n) (formIdx n j))) (N : ℕ) :
    ‖σ - (whitneyMin n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).fst‖ +
        ‖u - (whitneyMin n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin n N) hij hjk f).snd.snd :
            (whitneyMin n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
        (2 * ((1 + 2 * C) * (interpBound n i + interpBound n j) * L)) * meshSize N :=
  whitneyMin_old_norm_sub_le_meshSize_smooth hE hij hjk (norm_le_of_mem_orthogonal_cycles_min hij)
    (norm_le_of_mem_orthogonal_cycles_min hjk) hs hL0 hσ hu hB hq N

end Min

end Whitney

section Poly

variable {S : PolySeq} {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ}

section Max

variable (hE : PolySmoothingEstimates n S p C)
include hE

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimates.isGraphBounded_proj`. -/
theorem poly_old_isGraphBounded_proj (N : ℕ) (i j : ℤ) : (hE.proj N).IsGraphBounded i j (2 * C) :=
  (hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j)

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimates.norm_le_of_forall_inner_eq_zero`. -/
theorem poly_old_norm_le_of_forall_inner_eq_zero {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (N : ℕ)
    {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (poly n S N).V i)
    (hxo : ∀ y ∈ (poly n S N).cyclesW i, inner ℝ y x = 0) :
    ‖x‖ ≤ 2 * C * (2 * Real.pi)⁻¹ * ‖(complex n).d i j ⟨x, (poly n S N).le_domain i j hx⟩‖ :=
  (hE.proj N).norm_le_of_forall_inner_eq_zero hij (norm_le_of_mem_orthogonal_cycles hij)
    hE.two_mul_nonneg (hE.norm_proj_le N i) hx hxo

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimates.existsUnique_mixed`. -/
theorem poly_old_existsUnique_mixed {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) (N : ℕ) (f : (poly n S N).V j) :
    ∃! x, (poly n S N).toHilbertComplex.mixedForm i j k x =
      (poly n S N).toHilbertComplex.mixedRHS i j f :=
  (hE.proj N).existsUnique_mixed hij hjk le_rfl (by linarith [hE.half_le])
    (cube_old_poincare hij cube_old_inv_two_pi_le_one) (cube_old_poincare hjk cube_old_inv_two_pi_le_one) (hE.norm_proj_le N i)
    (hE.norm_proj_le N j) f

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimates.norm_le_of_mixed`. -/
theorem poly_old_norm_le_of_mixed {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) (N : ℕ) {f : (poly n S N).V j}
    {x : (poly n S N).toHilbertComplex.MixedSpace i j}
    (hx : (poly n S N).toHilbertComplex.mixedForm i j k x =
      (poly n S N).toHilbertComplex.mixedRHS i j f) :
    ‖x‖ ≤ 16 * (2 * C * 1) ^ 2 * ‖f‖ :=
  (hE.proj N).norm_le_of_mixed hij hjk le_rfl (by linarith [hE.half_le])
    (cube_old_poincare hij cube_old_inv_two_pi_le_one) (cube_old_poincare hjk cube_old_inv_two_pi_le_one) (hE.norm_proj_le N i)
    (hE.norm_proj_le N j) hx

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimates.norm_sub_le_infDist`. -/
theorem poly_old_norm_sub_le_infDist {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {f : L2F ℝ (cubeDomain n) (formIdx n j)}
    {σ : (complex n).domainSpace i} {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) (N : ℕ) :
    ‖σ - (poly n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).fst‖ +
        ‖u - (poly n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n S N) hij hjk f).snd.snd :
            (poly n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) *
        (Metric.infDist σ ((poly n S N).domainSub i) + Metric.infDist u ((poly n S N).domainSub j) +
          Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((poly n S N).harmonicW j) +
          (hE.proj N).harmonicGap j *
            Metric.infDist ((complex n).boundaryPart j ((complex n).domainIncl j u))
              ((poly n S N).domainSub j)) :=
  (hE.proj N).norm_sub_le_infDist_harmonicGap hij hjk (by linarith [hE.half_le])
    (norm_le_of_mem_orthogonal_cycles hij) (norm_le_of_mem_orthogonal_cycles hjk)
    (poly_old_isGraphBounded_proj hE N i j) (poly_old_isGraphBounded_proj hE N j k) hs

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimates.norm_sub_le_of_infDist_le`. -/
theorem poly_old_norm_sub_le_of_infDist_le {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {f : L2F ℝ (cubeDomain n) (formIdx n j)}
    {σ : (complex n).domainSpace i} {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) {K δ : ℝ} (N : ℕ)
    (hσ : Metric.infDist σ ((poly n S N).domainSub i) ≤ K * δ)
    (hu : Metric.infDist u ((poly n S N).domainSub j) ≤ K * δ)
    (hq : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((poly n S N).harmonicW j) ≤
      K * δ)
    (hB : Metric.infDist ((complex n).boundaryPart j ((complex n).domainIncl j u))
      ((poly n S N).domainSub j) ≤ K * δ) :
    ‖σ - (poly n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).fst‖ +
        ‖u - (poly n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n S N) hij hjk f).snd.snd :
            (poly n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K *
        δ := by
  have hμ0 : 0 ≤ 1 + 2 * C := by linarith [hE.two_mul_nonneg]
  have h := (hE.proj N).norm_sub_le_infDist hij hjk (by linarith [hE.half_le]) hμ0
    (norm_le_of_mem_orthogonal_cycles hij) (norm_le_of_mem_orthogonal_cycles hjk)
    (poly_old_isGraphBounded_proj hE N i j) (poly_old_isGraphBounded_proj hE N j k)
    (fun _ hq' => (hE.proj N).norm_sub_π_harmonic_le hjk hE.two_mul_nonneg
      (poly_old_isGraphBounded_proj hE N j k) hq') hs
  refine h.trans ?_
  have hK0 : 0 ≤ (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) := by
    have := hE.two_mul_nonneg; positivity
  have e : (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
      K * δ = (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) *
        ((4 + 2 * C) * (K * δ)) := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  have hB' := mul_le_mul_of_nonneg_left hB hμ0
  have e' : (4 + 2 * C) * (K * δ) = 3 * (K * δ) + (1 + 2 * C) * (K * δ) := by ring
  rw [e']
  linarith

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimates.tendsto_harmonicGap`. -/
theorem poly_old_tendsto_harmonicGap (j : ℤ) : Tendsto (fun N => (hE.proj N).harmonicGap j) atTop (𝓝 0) :=
  Subcomplex.CochainProjection.tendsto_harmonicGap hE.proj hE.two_mul_nonneg
    (fun N x => hE.norm_proj_le N j x) fun q _ => tendsto_infDist_poly S j q

end Max

section Min

variable (hE : PolySmoothingEstimatesMin n S p C)
include hE

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimatesMin.isGraphBounded_proj`. -/
theorem polyMin_old_isGraphBounded_proj (N : ℕ) (i j : ℤ) : (hE.proj N).IsGraphBounded i j (2 * C) :=
  (hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j)

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimatesMin.norm_le_of_forall_inner_eq_zero`. -/
theorem polyMin_old_norm_le_of_forall_inner_eq_zero {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (N : ℕ)
    {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (polyMin n S N).V i)
    (hxo : ∀ y ∈ (polyMin n S N).cyclesW i, inner ℝ y x = 0) :
    ‖x‖ ≤ 2 * C * (2 * Real.pi)⁻¹ *
      ‖(complexMin n).d i j ⟨x, (polyMin n S N).le_domain i j hx⟩‖ :=
  (hE.proj N).norm_le_of_forall_inner_eq_zero hij (norm_le_of_mem_orthogonal_cycles_min hij)
    hE.two_mul_nonneg (hE.norm_proj_le N i) hx hxo

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimatesMin.existsUnique_mixed`. -/
theorem polyMin_old_existsUnique_mixed {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) (N : ℕ) (f : (polyMin n S N).V j) :
    ∃! x, (polyMin n S N).toHilbertComplex.mixedForm i j k x =
      (polyMin n S N).toHilbertComplex.mixedRHS i j f :=
  (hE.proj N).existsUnique_mixed hij hjk le_rfl (by linarith [hE.half_le])
    (cube_old_poincare_min hij cube_old_inv_two_pi_le_one) (cube_old_poincare_min hjk cube_old_inv_two_pi_le_one)
    (hE.norm_proj_le N i) (hE.norm_proj_le N j) f

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimatesMin.norm_le_of_mixed`. -/
theorem polyMin_old_norm_le_of_mixed {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) (N : ℕ) {f : (polyMin n S N).V j}
    {x : (polyMin n S N).toHilbertComplex.MixedSpace i j}
    (hx : (polyMin n S N).toHilbertComplex.mixedForm i j k x =
      (polyMin n S N).toHilbertComplex.mixedRHS i j f) :
    ‖x‖ ≤ 16 * (2 * C * 1) ^ 2 * ‖f‖ :=
  (hE.proj N).norm_le_of_mixed hij hjk le_rfl (by linarith [hE.half_le])
    (cube_old_poincare_min hij cube_old_inv_two_pi_le_one) (cube_old_poincare_min hjk cube_old_inv_two_pi_le_one)
    (hE.norm_proj_le N i) (hE.norm_proj_le N j) hx

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimatesMin.norm_sub_le_infDist`. -/
theorem polyMin_old_norm_sub_le_infDist {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {f : L2F ℝ (cubeDomain n) (formIdx n j)}
    {σ : (complexMin n).domainSpace i} {u : (complexMin n).domainSpace j}
    {q : (complexMin n).harmonic j}
    (hs : (complexMin n).IsMixedSolution i j k f σ u q) (N : ℕ) :
    ‖σ - (polyMin n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).fst‖ +
        ‖u - (polyMin n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyMin n S N) hij hjk f).snd.snd :
            (polyMin n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) *
        (Metric.infDist σ ((polyMin n S N).domainSub i) +
          Metric.infDist u ((polyMin n S N).domainSub j) +
          Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((polyMin n S N).harmonicW j) +
          (hE.proj N).harmonicGap j *
            Metric.infDist ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))
              ((polyMin n S N).domainSub j)) :=
  (hE.proj N).norm_sub_le_infDist_harmonicGap hij hjk (by linarith [hE.half_le])
    (norm_le_of_mem_orthogonal_cycles_min hij) (norm_le_of_mem_orthogonal_cycles_min hjk)
    (polyMin_old_isGraphBounded_proj hE N i j) (polyMin_old_isGraphBounded_proj hE N j k) hs

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimatesMin.norm_sub_le_of_infDist_le`. -/
theorem polyMin_old_norm_sub_le_of_infDist_le {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {f : L2F ℝ (cubeDomain n) (formIdx n j)}
    {σ : (complexMin n).domainSpace i} {u : (complexMin n).domainSpace j}
    {q : (complexMin n).harmonic j}
    (hs : (complexMin n).IsMixedSolution i j k f σ u q) {K δ : ℝ} (N : ℕ)
    (hσ : Metric.infDist σ ((polyMin n S N).domainSub i) ≤ K * δ)
    (hu : Metric.infDist u ((polyMin n S N).domainSub j) ≤ K * δ)
    (hq : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((polyMin n S N).harmonicW j) ≤
      K * δ)
    (hB : Metric.infDist ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))
      ((polyMin n S N).domainSub j) ≤ K * δ) :
    ‖σ - (polyMin n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).fst‖ +
        ‖u - (polyMin n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyMin n S N) hij hjk f).snd.snd :
            (polyMin n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K *
        δ := by
  have hμ0 : 0 ≤ 1 + 2 * C := by linarith [hE.two_mul_nonneg]
  have h := (hE.proj N).norm_sub_le_infDist hij hjk (by linarith [hE.half_le]) hμ0
    (norm_le_of_mem_orthogonal_cycles_min hij) (norm_le_of_mem_orthogonal_cycles_min hjk)
    (polyMin_old_isGraphBounded_proj hE N i j) (polyMin_old_isGraphBounded_proj hE N j k)
    (fun _ hq' => (hE.proj N).norm_sub_π_harmonic_le hjk hE.two_mul_nonneg
      (polyMin_old_isGraphBounded_proj hE N j k) hq') hs
  refine h.trans ?_
  have hK0 : 0 ≤ (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) := by
    have := hE.two_mul_nonneg; positivity
  have e : (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
      K * δ = (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) *
        ((4 + 2 * C) * (K * δ)) := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  have hB' := mul_le_mul_of_nonneg_left hB hμ0
  have e' : (4 + 2 * C) * (K * δ) = 3 * (K * δ) + (1 + 2 * C) * (K * δ) := by ring
  rw [e']
  linarith

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimatesMin.tendsto_harmonicGap`. -/
theorem polyMin_old_tendsto_harmonicGap (j : ℤ) : Tendsto (fun N => (hE.proj N).harmonicGap j) atTop (𝓝 0) :=
  Subcomplex.CochainProjection.tendsto_harmonicGap hE.proj hE.two_mul_nonneg
    (fun N x => hE.norm_proj_le N j x) fun q _ => tendsto_infDist_polyMin S j q

end Min

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimates.norm_sub_le_meshSize_pow`. -/
theorem poly_old_norm_sub_le_meshSize_pow {S : PolySeq}
    {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimates n S p C) {s : ℕ}
    {i j k : ℤ} (hSi : PolyOrderAt n S s i) (hSj : PolyOrderAt n S s j)
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) {L : ℝ} (hL0 : 0 ≤ L)
    (hσ : IsCsForm s i L ((complex n).domainIncl i σ))
    (hu : IsCsForm s j L ((complex n).domainIncl j u))
    (hB : IsCsForm s j L ((complex n).domainIncl j
      ((complex n).boundaryPart j ((complex n).domainIncl j u))))
    (hq : IsCsForm s j L (q : L2F ℝ (cubeDomain n) (formIdx n j))) (N : ℕ) :
    ‖σ - (poly n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).fst‖ +
        ‖u - (poly n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n S N) hij hjk f).snd.snd :
            (poly n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
        (2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L)) *
          meshSize N ^ (s + 1) := by
  have hC := hE.two_mul_nonneg
  have hh := pow_nonneg (meshSize_pos N).le (s + 1)
  have hBi := polyInterpBound_nonneg (n := n) S i
  have hBj := polyInterpBound_nonneg (n := n) S j
  have hiL := mul_nonneg (mul_nonneg hBi hL0) hh
  have hjL := mul_nonneg (mul_nonneg hBj hL0) hh
  have hK : 2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
      meshSize N ^ (s + 1) =
      2 * ((1 + 2 * C) * (polyInterpBound n S i * L * meshSize N ^ (s + 1))) +
        2 * ((1 + 2 * C) * (polyInterpBound n S j * L * meshSize N ^ (s + 1))) := by ring
  have hi : 2 * (polyInterpBound n S i * L * meshSize N ^ (s + 1)) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    rw [hK]; nlinarith
  have hj : 2 * (polyInterpBound n S j * L * meshSize N ^ (s + 1)) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    rw [hK]; nlinarith
  have hq' : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j))
      ((poly n S N).harmonicW j) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    refine ((hE.proj N).infDist_harmonicW_le hjk hC (poly_old_isGraphBounded_proj hE N j k) q.2).trans ?_
    have h := IsCsForm.infDist_domainSub_poly_le hSj
      (σ := cyclesToDomainSpace ((complex n).harmonic_le_cycles j q.2)) hq hL0 N
    rw [hK]
    have : 0 ≤ 1 + 2 * C := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h this]
  exact poly_old_norm_sub_le_of_infDist_le hE hij hjk hs N
    ((hσ.infDist_domainSub_poly_le hSi hL0 N).trans hi)
    ((hu.infDist_domainSub_poly_le hSj hL0 N).trans hj) hq'
    ((hB.infDist_domainSub_poly_le hSj hL0 N).trans hj)

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimates.infDist_domainSub_le_sobGraph`. -/
theorem poly_old_infDist_domainSub_le_sobGraph {S : PolySeq}
    {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimates n S p C) {s L : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (N : ℕ) {j : ℤ} {σ : (complex n).domainSpace j}
    (hσ : SobGraph n s L σ) :
    Metric.infDist σ ((poly n S N).domainSub j) ≤
      (1 + 2 * C) * (sobConstZ n S j + sobConstZ n S (j + 1)) * meshSize N ^ s * L := by
  refine (infDist_domainSub_le_proj (hE.proj N) hE.two_mul_nonneg (hE.norm_proj_le N) j σ).trans ?_
  have h1 := infDist_poly_le_sobAt S hs0 hs1 N hσ.1
  have h2 := infDist_poly_le_sobAt S hs0 hs1 N hσ.2
  have := hE.two_mul_nonneg
  calc (1 + 2 * C) * (Metric.infDist ((complex n).domainIncl j σ) ((poly n S N).V j) +
        Metric.infDist ((complex n).d j (j + 1) ((complex n).domainCoord j (j + 1) σ))
          ((poly n S N).V (j + 1))) ≤
      (1 + 2 * C) * (sobConstZ n S j * meshSize N ^ s * L +
        sobConstZ n S (j + 1) * meshSize N ^ s * L) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by linarith)
    _ = _ := by ring

omit [NeZero n] in
/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimates.infDist_domainSub_le_sobGraph_high`. -/
theorem poly_old_infDist_domainSub_le_sobGraph_high [NeZero n] {S : PolySeq}
    {p' : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimates n S p' C)
    {p : ℕ} (hns : n < 2 * (p + 1)) {s L : ℝ} (hs0 : 0 ≤ s) (N : ℕ) {j : ℤ}
    (hS0 : ∀ k : ℕ, (k : ℤ) = j → polySpace n p k ≤ S.space n k)
    (hS1 : ∀ k : ℕ, (k : ℤ) = j + 1 → polySpace n p k ≤ S.space n k)
    {σ : (complex n).domainSpace j} (hσ : SobGraph n s L σ) :
    Metric.infDist σ ((poly n S N).domainSub j) ≤
      (1 + 2 * C) * (sobConstHighZ n S p j + sobConstHighZ n S p (j + 1)) *
        meshSize N ^ min s (p + 1) * L := by
  refine (infDist_domainSub_le_proj (hE.proj N) hE.two_mul_nonneg (hE.norm_proj_le N) j σ).trans ?_
  have h1 := infDist_poly_le_sobAt_high S hns hs0 N hS0 hσ.1
  have h2 := infDist_poly_le_sobAt_high S hns hs0 N hS1 hσ.2
  have := hE.two_mul_nonneg
  calc (1 + 2 * C) * (Metric.infDist ((complex n).domainIncl j σ) ((poly n S N).V j) +
        Metric.infDist ((complex n).d j (j + 1) ((complex n).domainCoord j (j + 1) σ))
          ((poly n S N).V (j + 1))) ≤
      (1 + 2 * C) * (sobConstHighZ n S p j * meshSize N ^ min s (p + 1) * L +
        sobConstHighZ n S p (j + 1) * meshSize N ^ min s (p + 1) * L) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by linarith)
    _ = _ := by ring

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimatesMin.norm_sub_le_meshSize_pow`. -/
theorem polyMin_old_norm_sub_le_meshSize_pow {S : PolySeq}
    {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimatesMin n S p C)
    {s : ℕ} {i j k : ℤ} (hSi : PolyOrderAt n S s i) (hSj : PolyOrderAt n S s j)
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j}
    (hs : (complexMin n).IsMixedSolution i j k f σ u q) {L : ℝ} (hL0 : 0 ≤ L)
    (hσ : IsCsFormMin s i L ((complexMin n).domainIncl i σ))
    (hu : IsCsFormMin s j L ((complexMin n).domainIncl j u))
    (hB : IsCsFormMin s j L ((complexMin n).domainIncl j
      ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))))
    (hq : IsCsFormMin s j L (q : L2F ℝ (cubeDomain n) (formIdx n j))) (N : ℕ) :
    ‖σ - (polyMin n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).fst‖ +
        ‖u - (polyMin n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyMin n S N) hij hjk f).snd.snd :
            (polyMin n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
        (2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L)) *
          meshSize N ^ (s + 1) := by
  have hC := hE.two_mul_nonneg
  have hh := pow_nonneg (meshSize_pos N).le (s + 1)
  have hBi := polyInterpBound_nonneg (n := n) S i
  have hBj := polyInterpBound_nonneg (n := n) S j
  have hiL := mul_nonneg (mul_nonneg hBi hL0) hh
  have hjL := mul_nonneg (mul_nonneg hBj hL0) hh
  have hK : 2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
      meshSize N ^ (s + 1) =
      2 * ((1 + 2 * C) * (polyInterpBound n S i * L * meshSize N ^ (s + 1))) +
        2 * ((1 + 2 * C) * (polyInterpBound n S j * L * meshSize N ^ (s + 1))) := by ring
  have hi : 2 * (polyInterpBound n S i * L * meshSize N ^ (s + 1)) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    rw [hK]; nlinarith
  have hj : 2 * (polyInterpBound n S j * L * meshSize N ^ (s + 1)) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    rw [hK]; nlinarith
  have hq' : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j))
      ((polyMin n S N).harmonicW j) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    refine ((hE.proj N).infDist_harmonicW_le hjk hC (polyMin_old_isGraphBounded_proj hE N j k) q.2).trans ?_
    have h := IsCsFormMin.infDist_domainSub_polyMin_le hSj
      (σ := cyclesToDomainSpace ((complexMin n).harmonic_le_cycles j q.2)) hq hL0 N
    rw [hK]
    have : 0 ≤ 1 + 2 * C := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h this]
  exact polyMin_old_norm_sub_le_of_infDist_le hE hij hjk hs N
    ((hσ.infDist_domainSub_polyMin_le hSi hL0 N).trans hi)
    ((hu.infDist_domainSub_polyMin_le hSj hL0 N).trans hj) hq'
    ((hB.infDist_domainSub_polyMin_le hSj hL0 N).trans hj)

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimatesMin.norm_sub_le_meshSize_pow_tr`. -/
theorem polyMin_old_norm_sub_le_meshSize_pow_tr {S : PolySeq}
    {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimatesMin n S p C)
    {s : ℕ} {i j k : ℤ} (hSi : PolyOrderAt n S s i) (hSj : PolyOrderAt n S s j)
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j}
    (hs : (complexMin n).IsMixedSolution i j k f σ u q) {L : ℝ} (hL0 : 0 ≤ L)
    (hσ : IsCsFormTr s i L ((complexMin n).domainIncl i σ))
    (hu : IsCsFormTr s j L ((complexMin n).domainIncl j u))
    (hB : IsCsFormTr s j L ((complexMin n).domainIncl j
      ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))))
    (hq : IsCsFormTr s j L (q : L2F ℝ (cubeDomain n) (formIdx n j))) (N : ℕ) :
    ‖σ - (polyMin n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).fst‖ +
        ‖u - (polyMin n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyMin n S N) hij hjk f).snd.snd :
            (polyMin n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
        (2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L)) *
          meshSize N ^ (s + 1) := by
  have hC := hE.two_mul_nonneg
  have hh := pow_nonneg (meshSize_pos N).le (s + 1)
  have hBi := polyInterpBound_nonneg (n := n) S i
  have hBj := polyInterpBound_nonneg (n := n) S j
  have hiL := mul_nonneg (mul_nonneg hBi hL0) hh
  have hjL := mul_nonneg (mul_nonneg hBj hL0) hh
  have hK : 2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
      meshSize N ^ (s + 1) =
      2 * ((1 + 2 * C) * (polyInterpBound n S i * L * meshSize N ^ (s + 1))) +
        2 * ((1 + 2 * C) * (polyInterpBound n S j * L * meshSize N ^ (s + 1))) := by ring
  have hi : 2 * (polyInterpBound n S i * L * meshSize N ^ (s + 1)) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    rw [hK]; nlinarith
  have hj : 2 * (polyInterpBound n S j * L * meshSize N ^ (s + 1)) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    rw [hK]; nlinarith
  have hq' : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j))
      ((polyMin n S N).harmonicW j) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    refine ((hE.proj N).infDist_harmonicW_le hjk hC (polyMin_old_isGraphBounded_proj hE N j k) q.2).trans ?_
    have h := IsCsFormTr.infDist_domainSub_polyMin_le hSj
      (σ := cyclesToDomainSpace ((complexMin n).harmonic_le_cycles j q.2)) hq hL0 N
    rw [hK]
    have : 0 ≤ 1 + 2 * C := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h this]
  exact polyMin_old_norm_sub_le_of_infDist_le hE hij hjk hs N
    ((hσ.infDist_domainSub_polyMin_le hSi hL0 N).trans hi)
    ((hu.infDist_domainSub_polyMin_le hSj hL0 N).trans hj) hq'
    ((hB.infDist_domainSub_polyMin_le hSj hL0 N).trans hj)

end Poly

section Parity

open Feec.Models.Cube.ParitySmoother

variable {J : Finset (Fin n)} {S : PolySeq} {ρ : ℕ → ReflKernel n} {C : ℝ}
  (hE : ParitySmoothingEstimates n J S ρ C)
include hE

/-- The old `Feec.Models.Cube.FEM.ParitySmoothingEstimates.isGraphBounded_proj`. -/
theorem parity_old_isGraphBounded_proj (N : ℕ) (i j : ℤ) : (hE.proj N).IsGraphBounded i j (2 * C) :=
  (hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j)

end Parity

end CubeTowerOld

section ParallelepipedOld

open Feec.Domain Feec.FiniteElement Feec.Models.Cube Feec.Models.Parallelepiped

/-- The old `HilbertComplex.Subcomplex.CochainProjection.IsGraphBounded.mono'`. -/
theorem para_old_isGraphBounded_mono
    {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
    {H : HilbertComplex ℝ c W} {S : H.Subcomplex} {P : S.CochainProjection} {i j : ι} {C C' : ℝ}
    (h : P.IsGraphBounded i j C) (hC : 0 ≤ C) (hCC : C ≤ C') : P.IsGraphBounded i j C' :=
  fun x => (h x).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC hCC 2) (by positivity))

section Generic

variable {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)]
  [∀ i, CompleteSpace (W i)] {H : HilbertComplex ℝ (ComplexShape.up ℤ) W}

/-- The old `Models.Parallelepiped.hasUniformProj_of_chainIso`. -/
theorem para_old_hasUniformProj_of_chainIso {W' : ℤ → Type*} [∀ i, NormedAddCommGroup (W' i)]
    [∀ i, InnerProductSpace ℝ (W' i)] [∀ i, CompleteSpace (W' i)]
    {H' : HilbertComplex ℝ (ComplexShape.up ℤ) W'} {e : ∀ i, W i ≃L[ℝ] W' i}
    (hI : IsChainIso H H' e) {M M' : ℝ} (hM : ∀ k, ‖(e k : W k →L[ℝ] W' k)‖ ≤ M)
    (hM' : ∀ k, ‖((e k).symm : W' k →L[ℝ] W k)‖ ≤ M')
    (hfin : ∀ j, FiniteDimensional ℝ (H'.harmonic j))
    {S' : ℕ → H'.Subcomplex} {S : ℕ → H.Subcomplex} [∀ N k, FiniteDimensional ℝ ((S N).V k)]
    (hS : ∀ N k x, x ∈ (S N).V k ↔ e k x ∈ (S' N).V k) {C : ℝ} (hC : 0 ≤ C)
    (P : ∀ N, (S' N).CochainProjection) (hb : ∀ N i x, ‖(P N).π i x‖ ≤ C * ‖x‖)
    (hg : ∀ N i j, (P N).IsGraphBounded i j C)
    (happ : ∀ j (x' : W' j), Tendsto (fun N => Metric.infDist x' ((S' N).V j : Set (W' j)))
      atTop (𝓝 0)) :
    Subcomplex.HasUniformProj atTop S := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' 0)
  set C₀ := max 1 (M' * C * M)
  set π : ∀ N, (S N).CochainProjection := fun N => hI.comapProj (S N) (hS N) (P N)
  have hbπ : ∀ N i x, ‖(π N).π i x‖ ≤ C₀ * ‖x‖ := fun N i x =>
    (hI.norm_comapProj_le _ _ (P N) hC (hb N i) (hM i) (hM' i) x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  refine ⟨C₀, π, le_max_left _ _, hbπ, fun N i j =>
    para_old_isGraphBounded_mono (graph_old_isGraphBounded_comapProj hI _ _ (P N) (hg N i j) hM hM')
      (mul_nonneg (mul_nonneg hM'0 hC) hM0) (le_max_right _ _), fun j => ?_⟩
  have := hfin j
  have := hI.finiteDimensional_harmonic j
  exact Subcomplex.CochainProjection.tendsto_harmonicGap π (zero_le_one.trans (le_max_left _ _))
    (fun N x => hbπ N j x) fun q _ => IsChainIso.tendsto_infDist_comapSub S hS (happ j) q

end Generic

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

/-- The old `Models.Parallelepiped.one_le_projConst`. -/
theorem para_old_one_le_projConst (C : ℝ) : 1 ≤ max 1 (pullConst A⁻¹ * (2 * C) * pullConst A) :=
  le_max_left _ _

/-- The old `Models.Parallelepiped.one_le_poincareConst`. -/
theorem para_old_one_le_poincareConst : 1 ≤ poincareConst A := le_max_left _ _

variable [NeZero n] {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ}

/-- The old `Models.Parallelepiped.norm_proj_le`. -/
theorem para_old_norm_proj_le (hE : FEM.SmoothingEstimates n p C) (N : ℕ) (i : ℤ)
    (x : L2F ℝ (domain A b) (formIdx n i)) :
    ‖((isChainIso A hA b).comapProj (whitney A hA b N)
      (fun i x => mem_whitney_V_iff A hA b N i x) (hE.proj N)).π i x‖ ≤ max 1 (pullConst A⁻¹ * (2 * C) * pullConst A) * ‖x‖ :=
  ((isChainIso A hA b).norm_comapProj_le _ _ (hE.proj N) hE.two_mul_nonneg (hE.norm_proj_le N i)
    (norm_pullEquiv_le A hA b i) (norm_pullEquiv_symm_le A hA b i) x).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- The old `Models.Parallelepiped.isGraphBounded_proj`. -/
theorem para_old_isGraphBounded_proj (hE : FEM.SmoothingEstimates n p C) (N : ℕ) (i j : ℤ) :
    ((isChainIso A hA b).comapProj (whitney A hA b N)
      (fun i x => mem_whitney_V_iff A hA b N i x) (hE.proj N)).IsGraphBounded i j
      (max 1 (pullConst A⁻¹ * (2 * C) * pullConst A)) :=
  para_old_isGraphBounded_mono (graph_old_isGraphBounded_comapProj (isChainIso A hA b) _ _ (hE.proj N)
    ((hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j))
    (norm_pullEquiv_le A hA b) (norm_pullEquiv_symm_le A hA b))
    (mul_nonneg (mul_nonneg (pullConst_nonneg _) hE.two_mul_nonneg) (pullConst_nonneg _))
    (le_max_right _ _)

/-- The old `Models.Parallelepiped.norm_projMin_le`. -/
theorem para_old_norm_projMin_le (hE : FEM.SmoothingEstimatesMin n p C) (N : ℕ) (i : ℤ)
    (x : L2F ℝ (domain A b) (formIdx n i)) :
    ‖((isChainIsoMin A hA b).comapProj (whitneyMin A hA b N)
      (fun i x => mem_whitneyMin_V_iff A hA b N i x) (hE.proj N)).π i x‖ ≤ max 1 (pullConst A⁻¹ * (2 * C) * pullConst A) * ‖x‖ :=
  ((isChainIsoMin A hA b).norm_comapProj_le _ _ (hE.proj N) hE.two_mul_nonneg
    (hE.norm_proj_le N i) (norm_pullEquiv_le A hA b i) (norm_pullEquiv_symm_le A hA b i) x).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- The old `Models.Parallelepiped.isGraphBounded_projMin`. -/
theorem para_old_isGraphBounded_projMin (hE : FEM.SmoothingEstimatesMin n p C) (N : ℕ) (i j : ℤ) :
    ((isChainIsoMin A hA b).comapProj (whitneyMin A hA b N)
      (fun i x => mem_whitneyMin_V_iff A hA b N i x) (hE.proj N)).IsGraphBounded i j
      (max 1 (pullConst A⁻¹ * (2 * C) * pullConst A)) :=
  para_old_isGraphBounded_mono (graph_old_isGraphBounded_comapProj (isChainIsoMin A hA b) _ _ (hE.proj N)
    ((hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j))
    (norm_pullEquiv_le A hA b) (norm_pullEquiv_symm_le A hA b))
    (mul_nonneg (mul_nonneg (pullConst_nonneg _) hE.two_mul_nonneg) (pullConst_nonneg _))
    (le_max_right _ _)

/-- The old `Models.Parallelepiped.tendsto_harmonicGap_proj`. -/
theorem para_old_tendsto_harmonicGap_proj (hE : FEM.SmoothingEstimates n p C) (j : ℤ) :
    Tendsto (fun N => ((isChainIso A hA b).comapProj (whitney A hA b N)
      (fun i x => mem_whitney_V_iff A hA b N i x) (hE.proj N)).harmonicGap j) atTop (𝓝 0) := by
  have := finiteDimensional_harmonic A hA b j
  exact Subcomplex.CochainProjection.tendsto_harmonicGap (fun N => (isChainIso A hA b).comapProj (whitney A hA b N)
      (fun i x => mem_whitney_V_iff A hA b N i x) (hE.proj N))
    (zero_le_one.trans (para_old_one_le_projConst A C)) (fun N x => para_old_norm_proj_le A hA b hE N j x)
    fun q _ => IsChainIso.tendsto_infDist_comapSub (whitney A hA b)
      (fun N i x => mem_whitney_V_iff A hA b N i x) (fun x' => FEM.tendsto_infDist_whitney j x') q

/-- The old `Models.Parallelepiped.tendsto_harmonicGap_projMin`. -/
theorem para_old_tendsto_harmonicGap_projMin (hE : FEM.SmoothingEstimatesMin n p C) (j : ℤ) :
    Tendsto (fun N => ((isChainIsoMin A hA b).comapProj (whitneyMin A hA b N)
      (fun i x => mem_whitneyMin_V_iff A hA b N i x) (hE.proj N)).harmonicGap j) atTop (𝓝 0) := by
  have := finiteDimensional_harmonic_min A hA b j
  exact Subcomplex.CochainProjection.tendsto_harmonicGap (fun N => (isChainIsoMin A hA b).comapProj (whitneyMin A hA b N)
      (fun i x => mem_whitneyMin_V_iff A hA b N i x) (hE.proj N))
    (zero_le_one.trans (para_old_one_le_projConst A C)) (fun N x => para_old_norm_projMin_le A hA b hE N j x)
    fun q _ => IsChainIso.tendsto_infDist_comapSub (whitneyMin A hA b)
      (fun N i x => mem_whitneyMin_V_iff A hA b N i x)
      (fun x' => FEM.tendsto_infDist_whitneyMin j x') q

/-- The old `Models.Parallelepiped.smoothedProjection_uniform`. -/
theorem para_old_smoothedProjection_uniform : ∃ (C : ℝ) (π : ∀ N, (whitney A hA b N).CochainProjection),
    1 ≤ C ∧ (∀ N i x, ‖(π N).π i x‖ ≤ C * ‖x‖) ∧ (∀ N i j, (π N).IsGraphBounded i j C) ∧
      ∀ j, Tendsto (fun N => (π N).harmonicGap j) atTop (𝓝 0) := by
  have := finiteDimensional_harmonic A hA b
  exact (whitneyFamily A hA b).hasUniformProj

/-- The old `Models.Parallelepiped.smoothedProjection_uniform_min`. -/
theorem para_old_smoothedProjection_uniform_min :
    ∃ (C : ℝ) (π : ∀ N, (whitneyMin A hA b N).CochainProjection),
    1 ≤ C ∧ (∀ N i x, ‖(π N).π i x‖ ≤ C * ‖x‖) ∧ (∀ N i j, (π N).IsGraphBounded i j C) ∧
      ∀ j, Tendsto (fun N => (π N).harmonicGap j) atTop (𝓝 0) := by
  have := finiteDimensional_harmonic_min A hA b
  exact (whitneyFamilyMin A hA b).hasUniformProj

/-- The old `Models.Parallelepiped.discretePoincare`. -/
theorem para_old_discretePoincare : ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
    {x : L2F ℝ (domain A b) (formIdx n i)} (hx : x ∈ (whitney A hA b N).V i),
    (∀ y ∈ (whitney A hA b N).cyclesW i, inner ℝ y x = 0) →
      ‖x‖ ≤ c * ‖(complex A b).d i j ⟨x, (whitney A hA b N).le_domain i j hx⟩‖ := by
  have := finiteDimensional_harmonic A hA b
  exact (whitneyFamily A hA b).hasUniformProj.discretePoincare (poincare A hA b)

/-- The old `Models.Parallelepiped.discretePoincare_min`. -/
theorem para_old_discretePoincare_min : ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
    {x : L2F ℝ (domain A b) (formIdx n i)} (hx : x ∈ (whitneyMin A hA b N).V i),
    (∀ y ∈ (whitneyMin A hA b N).cyclesW i, inner ℝ y x = 0) →
      ‖x‖ ≤ c * ‖(complexMin A b).d i j ⟨x, (whitneyMin A hA b N).le_domain i j hx⟩‖ := by
  have := finiteDimensional_harmonic_min A hA b
  exact (whitneyFamilyMin A hA b).hasUniformProj.discretePoincare (poincare_min A hA b)

/-- The old `Models.Parallelepiped.mixed_wellPosed`. -/
theorem para_old_mixed_wellPosed : ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j →
    (ComplexShape.up ℤ).Rel j k → ∀ (N : ℕ) (f : (whitney A hA b N).V j),
    (∃! x, (whitney A hA b N).toHilbertComplex.mixedForm i j k x =
      (whitney A hA b N).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (whitney A hA b N).toHilbertComplex.MixedSpace i j,
      (whitney A hA b N).toHilbertComplex.mixedForm i j k x =
        (whitney A hA b N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  have := finiteDimensional_harmonic A hA b
  have := (whitneyFamily A hA b).finiteDimensional
  exact (whitneyFamily A hA b).hasUniformProj.mixed_wellPosed (poincare A hA b) (para_old_one_le_poincareConst A)

/-- The old `Models.Parallelepiped.mixed_wellPosed_min`. -/
theorem para_old_mixed_wellPosed_min : ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j →
    (ComplexShape.up ℤ).Rel j k → ∀ (N : ℕ) (f : (whitneyMin A hA b N).V j),
    (∃! x, (whitneyMin A hA b N).toHilbertComplex.mixedForm i j k x =
      (whitneyMin A hA b N).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (whitneyMin A hA b N).toHilbertComplex.MixedSpace i j,
      (whitneyMin A hA b N).toHilbertComplex.mixedForm i j k x =
        (whitneyMin A hA b N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  have := finiteDimensional_harmonic_min A hA b
  have := (whitneyFamilyMin A hA b).finiteDimensional
  exact (whitneyFamilyMin A hA b).hasUniformProj.mixed_wellPosed (poincare_min A hA b) (para_old_one_le_poincareConst A)

/-- The old `Models.Parallelepiped.mixed_quasiOptimal`. -/
theorem para_old_mixed_quasiOptimal : ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (domain A b) (formIdx n j)} {σ : (complex A b).domainSpace i}
    {u : (complex A b).domainSpace j} {q : (complex A b).harmonic j},
    (complex A b).IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (whitney A hA b N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney A hA b N) hij hjk f).fst‖ +
        ‖u - (whitney A hA b N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney A hA b N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (domain A b) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney A hA b N) hij hjk f).snd.snd :
            (whitney A hA b N).V j) : L2F ℝ (domain A b) (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((whitney A hA b N).domainSub i) +
        Metric.infDist u ((whitney A hA b N).domainSub j) +
        Metric.infDist (q : L2F ℝ (domain A b) (formIdx n j)) ((whitney A hA b N).harmonicW j) +
        μ j N * Metric.infDist ((complex A b).boundaryPart j ((complex A b).domainIncl j u))
          ((whitney A hA b N).domainSub j)) := by
  have := finiteDimensional_harmonic A hA b
  have := (whitneyFamily A hA b).finiteDimensional
  exact (whitneyFamily A hA b).hasUniformProj.mixed_quasiOptimal (poincare A hA b)

/-- The old `Models.Parallelepiped.mixed_quasiOptimal_min`. -/
theorem para_old_mixed_quasiOptimal_min : ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (domain A b) (formIdx n j)} {σ : (complexMin A b).domainSpace i}
    {u : (complexMin A b).domainSpace j} {q : (complexMin A b).harmonic j},
    (complexMin A b).IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (whitneyMin A hA b N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin A hA b N) hij hjk f).fst‖ +
        ‖u - (whitneyMin A hA b N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin A hA b N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (domain A b) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin A hA b N) hij hjk
            f).snd.snd : (whitneyMin A hA b N).V j) : L2F ℝ (domain A b) (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((whitneyMin A hA b N).domainSub i) +
        Metric.infDist u ((whitneyMin A hA b N).domainSub j) +
        Metric.infDist (q : L2F ℝ (domain A b) (formIdx n j))
          ((whitneyMin A hA b N).harmonicW j) +
        μ j N * Metric.infDist ((complexMin A b).boundaryPart j ((complexMin A b).domainIncl j u))
          ((whitneyMin A hA b N).domainSub j)) := by
  have := finiteDimensional_harmonic_min A hA b
  have := (whitneyFamilyMin A hA b).finiteDimensional
  exact (whitneyFamilyMin A hA b).hasUniformProj.mixed_quasiOptimal (poincare_min A hA b)

/-- The old `Models.Parallelepiped.mixed_rate_smooth`. -/
theorem para_old_mixed_rate_smooth {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) : ∃ K : ℝ, ∀ {f : L2F ℝ (domain A b) (formIdx n j)}
    {σ : (complex A b).domainSpace i} {u : (complex A b).domainSpace j}
    {q : (complex A b).harmonic j},
    (complex A b).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsC2Form A hA b i L ((complex A b).domainIncl i σ) →
    IsC2Form A hA b j L ((complex A b).domainIncl j u) →
    IsC2Form A hA b j L ((complex A b).domainIncl j
      ((complex A b).boundaryPart j ((complex A b).domainIncl j u))) →
    IsC2Form A hA b j L (q : L2F ℝ (domain A b) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (whitney A hA b N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney A hA b N) hij hjk f).fst‖ +
        ‖u - (whitney A hA b N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney A hA b N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (domain A b) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney A hA b N) hij hjk f).snd.snd :
            (whitney A hA b N).V j) : L2F ℝ (domain A b) (formIdx n j))‖ ≤
      K * L * FEM.meshSize N := by
  have := finiteDimensional_harmonic A hA b
  obtain ⟨K, hK⟩ := ((whitneyFamily A hA b).staticFEEC (closedRangeAt A hA b) j).rate (whitneyJackson A hA b) () hij hjk
  refine ⟨K, fun hs _ hL hσ hu hb hq N => ?_⟩
  have h := hK hs hL hσ hu hb hq N
  simp only [whitneyFamily_V, whitneyJackson, Real.rpow_one] at h
  exact h

/-- The old `Models.Parallelepiped.mixed_rate_smooth_min`. -/
theorem para_old_mixed_rate_smooth_min {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) : ∃ K : ℝ, ∀ {f : L2F ℝ (domain A b) (formIdx n j)}
    {σ : (complexMin A b).domainSpace i} {u : (complexMin A b).domainSpace j}
    {q : (complexMin A b).harmonic j},
    (complexMin A b).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsC2FormMin A hA b i L ((complexMin A b).domainIncl i σ) →
    IsC2FormMin A hA b j L ((complexMin A b).domainIncl j u) →
    IsC2FormMin A hA b j L ((complexMin A b).domainIncl j
      ((complexMin A b).boundaryPart j ((complexMin A b).domainIncl j u))) →
    IsC2FormMin A hA b j L (q : L2F ℝ (domain A b) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (whitneyMin A hA b N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin A hA b N) hij hjk f).fst‖ +
        ‖u - (whitneyMin A hA b N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin A hA b N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (domain A b) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin A hA b N) hij hjk
            f).snd.snd : (whitneyMin A hA b N).V j) : L2F ℝ (domain A b) (formIdx n j))‖ ≤
      K * L * FEM.meshSize N := by
  have := finiteDimensional_harmonic_min A hA b
  obtain ⟨K, hK⟩ := ((whitneyFamilyMin A hA b).staticFEEC (closedRangeAt_min A hA b) j).rate (whitneyJacksonMin A hA b) () hij hjk
  refine ⟨K, fun hs _ hL hσ hu hb hq N => ?_⟩
  have h := hK hs hL hσ hu hb hq N
  simp only [whitneyFamilyMin_V, whitneyJacksonMin, Real.rpow_one] at h
  exact h

/-- The old `Models.Parallelepiped.polySmoothedProjection_uniform`. -/
theorem para_old_polySmoothedProjection_uniform (S : PolySeq) :
    Subcomplex.HasUniformProj atTop (poly A hA b S) := by
  have := finiteDimensional_harmonic A hA b
  exact (polyFamily A hA b S).hasUniformProj

/-- The old `Models.Parallelepiped.polySmoothedProjection_uniform_min`. -/
theorem para_old_polySmoothedProjection_uniform_min (S : PolySeq) :
    Subcomplex.HasUniformProj atTop (polyMin A hA b S) := by
  have := finiteDimensional_harmonic_min A hA b
  exact (polyFamilyMin A hA b S).hasUniformProj

/-- The old `Models.Parallelepiped.discretePoincare_poly`. -/
theorem para_old_discretePoincare_poly (S : PolySeq) : ∃ c : ℝ, ∀ {i j : ℤ},
    (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ) {x : L2F ℝ (domain A b) (formIdx n i)}
    (hx : x ∈ (poly A hA b S N).V i), (∀ y ∈ (poly A hA b S N).cyclesW i, inner ℝ y x = 0) →
      ‖x‖ ≤ c * ‖(complex A b).d i j ⟨x, (poly A hA b S N).le_domain i j hx⟩‖ := by
  have := finiteDimensional_harmonic A hA b
  exact (polyFamily A hA b S).hasUniformProj.discretePoincare (poincare A hA b)

/-- The old `Models.Parallelepiped.discretePoincare_polyMin`. -/
theorem para_old_discretePoincare_polyMin (S : PolySeq) : ∃ c : ℝ, ∀ {i j : ℤ},
    (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ) {x : L2F ℝ (domain A b) (formIdx n i)}
    (hx : x ∈ (polyMin A hA b S N).V i),
    (∀ y ∈ (polyMin A hA b S N).cyclesW i, inner ℝ y x = 0) →
      ‖x‖ ≤ c * ‖(complexMin A b).d i j ⟨x, (polyMin A hA b S N).le_domain i j hx⟩‖ := by
  have := finiteDimensional_harmonic_min A hA b
  exact (polyFamilyMin A hA b S).hasUniformProj.discretePoincare (poincare_min A hA b)

/-- The old `Models.Parallelepiped.mixed_wellPosed_poly`. -/
theorem para_old_mixed_wellPosed_poly (S : PolySeq) : ∃ C : ℝ, ∀ {i j k : ℤ},
    (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k → ∀ (N : ℕ)
    (f : (poly A hA b S N).V j),
    (∃! x, (poly A hA b S N).toHilbertComplex.mixedForm i j k x =
      (poly A hA b S N).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (poly A hA b S N).toHilbertComplex.MixedSpace i j,
      (poly A hA b S N).toHilbertComplex.mixedForm i j k x =
        (poly A hA b S N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  have := finiteDimensional_harmonic A hA b
  have := (polyFamily A hA b S).finiteDimensional
  exact (polyFamily A hA b S).hasUniformProj.mixed_wellPosed (poincare A hA b) (para_old_one_le_poincareConst A)

/-- The old `Models.Parallelepiped.mixed_wellPosed_polyMin`. -/
theorem para_old_mixed_wellPosed_polyMin (S : PolySeq) : ∃ C : ℝ, ∀ {i j k : ℤ},
    (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k → ∀ (N : ℕ)
    (f : (polyMin A hA b S N).V j),
    (∃! x, (polyMin A hA b S N).toHilbertComplex.mixedForm i j k x =
      (polyMin A hA b S N).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (polyMin A hA b S N).toHilbertComplex.MixedSpace i j,
      (polyMin A hA b S N).toHilbertComplex.mixedForm i j k x =
        (polyMin A hA b S N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  have := finiteDimensional_harmonic_min A hA b
  have := (polyFamilyMin A hA b S).finiteDimensional
  exact (polyFamilyMin A hA b S).hasUniformProj.mixed_wellPosed (poincare_min A hA b) (para_old_one_le_poincareConst A)

/-- The old `Models.Parallelepiped.mixed_quasiOptimal_poly`. -/
theorem para_old_mixed_quasiOptimal_poly (S : PolySeq) :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (domain A b) (formIdx n j)} {σ : (complex A b).domainSpace i}
    {u : (complex A b).domainSpace j} {q : (complex A b).harmonic j},
    (complex A b).IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (poly A hA b S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (poly A hA b S N) hij hjk f).fst‖ +
        ‖u - (poly A hA b S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (poly A hA b S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (domain A b) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly A hA b S N) hij hjk
            f).snd.snd : (poly A hA b S N).V j) : L2F ℝ (domain A b) (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((poly A hA b S N).domainSub i) +
        Metric.infDist u ((poly A hA b S N).domainSub j) +
        Metric.infDist (q : L2F ℝ (domain A b) (formIdx n j)) ((poly A hA b S N).harmonicW j) +
        μ j N * Metric.infDist ((complex A b).boundaryPart j ((complex A b).domainIncl j u))
          ((poly A hA b S N).domainSub j)) := by
  have := finiteDimensional_harmonic A hA b
  have := (polyFamily A hA b S).finiteDimensional
  exact (polyFamily A hA b S).hasUniformProj.mixed_quasiOptimal (poincare A hA b)

/-- The old `Models.Parallelepiped.mixed_quasiOptimal_polyMin`. -/
theorem para_old_mixed_quasiOptimal_polyMin (S : PolySeq) :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (domain A b) (formIdx n j)} {σ : (complexMin A b).domainSpace i}
    {u : (complexMin A b).domainSpace j} {q : (complexMin A b).harmonic j},
    (complexMin A b).IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (polyMin A hA b S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin A hA b S N) hij hjk f).fst‖ +
        ‖u - (polyMin A hA b S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin A hA b S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (domain A b) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyMin A hA b S N) hij hjk
            f).snd.snd : (polyMin A hA b S N).V j) : L2F ℝ (domain A b) (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((polyMin A hA b S N).domainSub i) +
        Metric.infDist u ((polyMin A hA b S N).domainSub j) +
        Metric.infDist (q : L2F ℝ (domain A b) (formIdx n j))
          ((polyMin A hA b S N).harmonicW j) +
        μ j N * Metric.infDist ((complexMin A b).boundaryPart j ((complexMin A b).domainIncl j u))
          ((polyMin A hA b S N).domainSub j)) := by
  have := finiteDimensional_harmonic_min A hA b
  have := (polyFamilyMin A hA b S).finiteDimensional
  exact (polyFamilyMin A hA b S).hasUniformProj.mixed_quasiOptimal (poincare_min A hA b)

end ParallelepipedOld

section StarShapedOld

open Feec.Domain Feec.FiniteElement Feec.Models.Cube Feec.Models.StarShaped

variable {n : ℕ} [NeZero n]

section Whitney

variable {D : StarDomain n} (F : MeshFamily D)

/-- The old `Models.StarShaped.MeshFamily.smoothedProjection_uniform`. -/
theorem star_old_smoothedProjection_uniform [∀ j, FiniteDimensional ℝ (D.complex.harmonic j)] :
    Subcomplex.HasUniformProj atTop F.whitney :=
  F.whitneyFamily.hasUniformProj

/-- The old `Models.StarShaped.MeshFamily.discretePoincare`. -/
theorem star_old_discretePoincare {cP : ℝ} (hP : HasPoincare D.complex cP) :
    ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
      {x : L2F ℝ D.Ω (formIdx n i)} (hx : x ∈ (F.whitney N).V i),
      (∀ y ∈ (F.whitney N).cyclesW i, inner ℝ y x = 0) →
        ‖x‖ ≤ c * ‖D.complex.d i j ⟨x, (F.whitney N).le_domain i j hx⟩‖ :=
  ⟨F.whitneyFamily.projBound * cP, fun {_ _} hij N _ hx hxo => (F.whitneyFamily.π N).norm_le_of_forall_inner_eq_zero hij
    (hP _ _ hij) (zero_le_one.trans F.whitneyFamily.one_le_projBound) (F.whitneyFamily.norm_π_le N _) hx hxo⟩

/-- The old `Models.StarShaped.MeshFamily.mixed_wellPosed`. -/
theorem star_old_mixed_wellPosed {cP : ℝ} (hP : HasPoincare D.complex cP) :
    ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      ∀ (N : ℕ) (f : (F.whitney N).V j),
      (∃! x, (F.whitney N).toHilbertComplex.mixedForm i j k x =
        (F.whitney N).toHilbertComplex.mixedRHS i j f) ∧
      ∀ x : (F.whitney N).toHilbertComplex.MixedSpace i j,
        (F.whitney N).toHilbertComplex.mixedForm i j k x =
          (F.whitney N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  refine F.exists_uniform_proj.elim fun K hK => ?_
  have hcP : 1 ≤ max 1 cP := le_max_left _ _
  have hP' := hP.mono (le_max_right 1 cP)
  refine ⟨16 * (K * max 1 cP) ^ 2, fun {i j k} hij hjk N f =>
    (hK.2 N).elim fun π hπ => ⟨?_, fun x hx => ?_⟩⟩
  · exact π.existsUnique_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) f
  · exact π.norm_le_of_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) hx

/-- The old `Models.StarShaped.MeshFamily.mixed_quasiOptimal`. -/
theorem star_old_mixed_quasiOptimal {cP : ℝ} (hP : HasPoincare D.complex cP)
    [∀ j, FiniteDimensional ℝ (D.complex.harmonic j)] :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complex.domainSpace i} {u : D.complex.domainSpace j}
    {q : D.complex.harmonic j},
    D.complex.IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (F.whitney N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.whitney N) hij hjk f).fst‖ +
        ‖u - (F.whitney N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.whitney N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
          (F.whitney N) hij hjk f).snd.snd : (F.whitney N).V j) : L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((F.whitney N).domainSub i) +
        Metric.infDist u ((F.whitney N).domainSub j) +
        Metric.infDist (q : L2F ℝ D.Ω (formIdx n j)) ((F.whitney N).harmonicW j) +
        μ j N * Metric.infDist (D.complex.boundaryPart j (D.complex.domainIncl j u))
          ((F.whitney N).domainSub j)) :=
  Subcomplex.HasUniformProj.mixed_quasiOptimal hP (star_old_smoothedProjection_uniform F)

/-- The old `Models.StarShaped.MeshFamily.mixed_rate_smooth`. -/
theorem star_old_mixed_rate_smooth {cP : ℝ} (hP : HasPoincare D.complex cP) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complex.domainSpace i} {u : D.complex.domainSpace j}
    {q : D.complex.harmonic j} (hs : D.complex.IsMixedSolution i j k f σ u q) {L : ℝ}
    (hL0 : 0 ≤ L) (hσ : D.IsC2Form i L (D.complex.domainIncl i σ))
    (hu : D.IsC2Form j L (D.complex.domainIncl j u))
    (hb : D.IsC2Form j L (D.complex.domainIncl j
      (D.complex.boundaryPart j (D.complex.domainIncl j u))))
    (hq : D.IsC2Form j L (q : L2F ℝ D.Ω (formIdx n j))) :
    ∃ K : ℝ, ∀ N : ℕ,
      ‖σ - (F.whitney N).embD i
          (Subcomplex.CochainProjection.discreteMixedSolution (F.whitney N) hij hjk f).fst‖ +
        ‖u - (F.whitney N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.whitney N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
          (F.whitney N) hij hjk f).snd.snd : (F.whitney N).V j) : L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize := by
  obtain ⟨K, hK⟩ := F.whitneyFamily.rate F.whitneyJackson () hij hjk
    ((D.complex.closedRangeAt_iff_poincare_of_rel hij).2 ⟨cP, hP i j hij⟩)
    ((D.complex.closedRangeAt_iff_poincare_of_rel hjk).2 ⟨cP, hP j k hjk⟩)
  refine ⟨K, fun N => ?_⟩
  have h := hK hs hL0 hσ hu hb hq N
  simp only [MeshFamily.whitneyFamily_V, MeshFamily.whitneyJackson, Real.rpow_one] at h
  exact h

/-- The old `Models.StarShaped.MeshFamily.smoothedProjection_uniformMin`. -/
theorem star_old_smoothedProjection_uniformMin [∀ j, FiniteDimensional ℝ (D.complexMin.harmonic j)] :
    Subcomplex.HasUniformProj atTop F.whitneyMin :=
  F.whitneyFamilyMin.hasUniformProj

/-- The old `Models.StarShaped.MeshFamily.discretePoincareMin`. -/
theorem star_old_discretePoincareMin {cP : ℝ} (hP : HasPoincare D.complexMin cP) :
    ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
      {x : L2F ℝ D.Ω (formIdx n i)} (hx : x ∈ (F.whitneyMin N).V i),
      (∀ y ∈ (F.whitneyMin N).cyclesW i, inner ℝ y x = 0) →
        ‖x‖ ≤ c * ‖D.complexMin.d i j ⟨x, (F.whitneyMin N).le_domain i j hx⟩‖ :=
  ⟨F.whitneyFamilyMin.projBound * cP, fun {_ _} hij N _ hx hxo => (F.whitneyFamilyMin.π N).norm_le_of_forall_inner_eq_zero hij
    (hP _ _ hij) (zero_le_one.trans F.whitneyFamilyMin.one_le_projBound) (F.whitneyFamilyMin.norm_π_le N _) hx hxo⟩

/-- The old `Models.StarShaped.MeshFamily.mixed_wellPosedMin`. -/
theorem star_old_mixed_wellPosedMin {cP : ℝ} (hP : HasPoincare D.complexMin cP) :
    ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      ∀ (N : ℕ) (f : (F.whitneyMin N).V j),
      (∃! x, (F.whitneyMin N).toHilbertComplex.mixedForm i j k x =
        (F.whitneyMin N).toHilbertComplex.mixedRHS i j f) ∧
      ∀ x : (F.whitneyMin N).toHilbertComplex.MixedSpace i j,
        (F.whitneyMin N).toHilbertComplex.mixedForm i j k x =
          (F.whitneyMin N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  refine F.exists_uniform_projMin.elim fun K hK => ?_
  have hcP : 1 ≤ max 1 cP := le_max_left _ _
  have hP' := hP.mono (le_max_right 1 cP)
  refine ⟨16 * (K * max 1 cP) ^ 2, fun {i j k} hij hjk N f =>
    (hK.2 N).elim fun π hπ => ⟨?_, fun x hx => ?_⟩⟩
  · exact π.existsUnique_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) f
  · exact π.norm_le_of_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) hx

/-- The old `Models.StarShaped.MeshFamily.mixed_quasiOptimalMin`. -/
theorem star_old_mixed_quasiOptimalMin {cP : ℝ} (hP : HasPoincare D.complexMin cP)
    [∀ j, FiniteDimensional ℝ (D.complexMin.harmonic j)] :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complexMin.domainSpace i} {u : D.complexMin.domainSpace j}
    {q : D.complexMin.harmonic j},
    D.complexMin.IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (F.whitneyMin N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.whitneyMin N) hij hjk f).fst‖ +
        ‖u - (F.whitneyMin N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.whitneyMin N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
          (F.whitneyMin N) hij hjk f).snd.snd : (F.whitneyMin N).V j) : L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((F.whitneyMin N).domainSub i) +
        Metric.infDist u ((F.whitneyMin N).domainSub j) +
        Metric.infDist (q : L2F ℝ D.Ω (formIdx n j)) ((F.whitneyMin N).harmonicW j) +
        μ j N * Metric.infDist (D.complexMin.boundaryPart j (D.complexMin.domainIncl j u))
          ((F.whitneyMin N).domainSub j)) :=
  Subcomplex.HasUniformProj.mixed_quasiOptimal hP (star_old_smoothedProjection_uniformMin F)

/-- The old `Models.StarShaped.MeshFamily.mixed_rate_smoothMin`. -/
theorem star_old_mixed_rate_smoothMin {cP : ℝ} (hP : HasPoincare D.complexMin cP) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complexMin.domainSpace i} {u : D.complexMin.domainSpace j}
    {q : D.complexMin.harmonic j} (hs : D.complexMin.IsMixedSolution i j k f σ u q) {L : ℝ}
    (hL0 : 0 ≤ L) (hσ : D.IsC2FormMin i L (D.complexMin.domainIncl i σ))
    (hu : D.IsC2FormMin j L (D.complexMin.domainIncl j u))
    (hb : D.IsC2FormMin j L (D.complexMin.domainIncl j
      (D.complexMin.boundaryPart j (D.complexMin.domainIncl j u))))
    (hq : D.IsC2FormMin j L (q : L2F ℝ D.Ω (formIdx n j))) :
    ∃ K : ℝ, ∀ N : ℕ,
      ‖σ - (F.whitneyMin N).embD i
          (Subcomplex.CochainProjection.discreteMixedSolution (F.whitneyMin N) hij hjk f).fst‖ +
        ‖u - (F.whitneyMin N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.whitneyMin N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
          (F.whitneyMin N) hij hjk f).snd.snd : (F.whitneyMin N).V j) : L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize := by
  obtain ⟨K, hK⟩ := F.whitneyFamilyMin.rate F.whitneyJacksonMin () hij hjk
    ((D.complexMin.closedRangeAt_iff_poincare_of_rel hij).2 ⟨cP, hP i j hij⟩)
    ((D.complexMin.closedRangeAt_iff_poincare_of_rel hjk).2 ⟨cP, hP j k hjk⟩)
  refine ⟨K, fun N => ?_⟩
  have h := hK hs hL0 hσ hu hb hq N
  simp only [MeshFamily.whitneyFamilyMin_V, MeshFamily.whitneyJacksonMin, Real.rpow_one] at h
  exact h

end Whitney

section Poly

variable {D : StarDomain n} (F : MeshFamily D) (S : PolySeq)

/-- The old `Models.StarShaped.MeshFamily.polySmoothedProjection_uniform`. -/
theorem star_old_polySmoothedProjection_uniform [∀ j, FiniteDimensional ℝ (D.complex.harmonic j)] :
    Subcomplex.HasUniformProj atTop (F.poly S) :=
  (F.polyFamily S).hasUniformProj

/-- The old `Models.StarShaped.MeshFamily.discretePoincare_poly`. -/
theorem star_old_discretePoincare_poly {cP : ℝ} (hP : HasPoincare D.complex cP) :
    ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
      {x : L2F ℝ D.Ω (formIdx n i)} (hx : x ∈ (F.poly S N).V i),
      (∀ y ∈ (F.poly S N).cyclesW i, inner ℝ y x = 0) →
        ‖x‖ ≤ c * ‖D.complex.d i j ⟨x, (F.poly S N).le_domain i j hx⟩‖ :=
  ⟨(F.polyFamily S).projBound * cP, fun {_ _} hij N _ hx hxo => ((F.polyFamily S).π N).norm_le_of_forall_inner_eq_zero hij
    (hP _ _ hij) (zero_le_one.trans (F.polyFamily S).one_le_projBound) ((F.polyFamily S).norm_π_le N _) hx hxo⟩

/-- The old `Models.StarShaped.MeshFamily.mixed_wellPosed_poly`. -/
theorem star_old_mixed_wellPosed_poly {cP : ℝ} (hP : HasPoincare D.complex cP) :
    ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      ∀ (N : ℕ) (f : (F.poly S N).V j),
      (∃! x, (F.poly S N).toHilbertComplex.mixedForm i j k x =
        (F.poly S N).toHilbertComplex.mixedRHS i j f) ∧
      ∀ x : (F.poly S N).toHilbertComplex.MixedSpace i j,
        (F.poly S N).toHilbertComplex.mixedForm i j k x =
          (F.poly S N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  refine (F.exists_uniform_polyProj S).elim fun K hK => ?_
  have hcP : 1 ≤ max 1 cP := le_max_left _ _
  have hP' := hP.mono (le_max_right 1 cP)
  refine ⟨16 * (K * max 1 cP) ^ 2, fun {i j k} hij hjk N f =>
    (hK.2 N).elim fun π hπ => ⟨?_, fun x hx => ?_⟩⟩
  · exact π.existsUnique_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) f
  · exact π.norm_le_of_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) hx

/-- The old `Models.StarShaped.MeshFamily.mixed_quasiOptimal_poly`. -/
theorem star_old_mixed_quasiOptimal_poly {cP : ℝ} (hP : HasPoincare D.complex cP)
    [∀ j, FiniteDimensional ℝ (D.complex.harmonic j)] :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complex.domainSpace i} {u : D.complex.domainSpace j}
    {q : D.complex.harmonic j},
    D.complex.IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (F.poly S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).fst‖ +
        ‖u - (F.poly S N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
          (F.poly S N) hij hjk f).snd.snd : (F.poly S N).V j) : L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((F.poly S N).domainSub i) +
        Metric.infDist u ((F.poly S N).domainSub j) +
        Metric.infDist (q : L2F ℝ D.Ω (formIdx n j)) ((F.poly S N).harmonicW j) +
        μ j N * Metric.infDist (D.complex.boundaryPart j (D.complex.domainIncl j u))
          ((F.poly S N).domainSub j)) :=
  Subcomplex.HasUniformProj.mixed_quasiOptimal hP (star_old_polySmoothedProjection_uniform F S)

/-- The old `Models.StarShaped.MeshFamily.polySmoothedProjection_uniformMin`. -/
theorem star_old_polySmoothedProjection_uniformMin
    [∀ j, FiniteDimensional ℝ (D.complexMin.harmonic j)] :
    Subcomplex.HasUniformProj atTop (F.polyMin S) :=
  (F.polyFamilyMin S).hasUniformProj

/-- The old `Models.StarShaped.MeshFamily.discretePoincare_polyMin`. -/
theorem star_old_discretePoincare_polyMin {cP : ℝ} (hP : HasPoincare D.complexMin cP) :
    ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
      {x : L2F ℝ D.Ω (formIdx n i)} (hx : x ∈ (F.polyMin S N).V i),
      (∀ y ∈ (F.polyMin S N).cyclesW i, inner ℝ y x = 0) →
        ‖x‖ ≤ c * ‖D.complexMin.d i j ⟨x, (F.polyMin S N).le_domain i j hx⟩‖ :=
  ⟨(F.polyFamilyMin S).projBound * cP, fun {_ _} hij N _ hx hxo => ((F.polyFamilyMin S).π N).norm_le_of_forall_inner_eq_zero hij
    (hP _ _ hij) (zero_le_one.trans (F.polyFamilyMin S).one_le_projBound) ((F.polyFamilyMin S).norm_π_le N _) hx hxo⟩

/-- The old `Models.StarShaped.MeshFamily.mixed_wellPosed_polyMin`. -/
theorem star_old_mixed_wellPosed_polyMin {cP : ℝ} (hP : HasPoincare D.complexMin cP) :
    ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      ∀ (N : ℕ) (f : (F.polyMin S N).V j),
      (∃! x, (F.polyMin S N).toHilbertComplex.mixedForm i j k x =
        (F.polyMin S N).toHilbertComplex.mixedRHS i j f) ∧
      ∀ x : (F.polyMin S N).toHilbertComplex.MixedSpace i j,
        (F.polyMin S N).toHilbertComplex.mixedForm i j k x =
          (F.polyMin S N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  refine (F.exists_uniform_polyProjMin S).elim fun K hK => ?_
  have hcP : 1 ≤ max 1 cP := le_max_left _ _
  have hP' := hP.mono (le_max_right 1 cP)
  refine ⟨16 * (K * max 1 cP) ^ 2, fun {i j k} hij hjk N f =>
    (hK.2 N).elim fun π hπ => ⟨?_, fun x hx => ?_⟩⟩
  · exact π.existsUnique_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) f
  · exact π.norm_le_of_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) hx

/-- The old `Models.StarShaped.MeshFamily.mixed_quasiOptimal_polyMin`. -/
theorem star_old_mixed_quasiOptimal_polyMin {cP : ℝ} (hP : HasPoincare D.complexMin cP)
    [∀ j, FiniteDimensional ℝ (D.complexMin.harmonic j)] :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complexMin.domainSpace i}
    {u : D.complexMin.domainSpace j} {q : D.complexMin.harmonic j},
    D.complexMin.IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (F.polyMin S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.polyMin S N) hij hjk f).fst‖ +
        ‖u - (F.polyMin S N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.polyMin S N) hij hjk
            f).snd.fst‖ +
        ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
          (F.polyMin S N) hij hjk f).snd.snd : (F.polyMin S N).V j) :
            L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((F.polyMin S N).domainSub i) +
        Metric.infDist u ((F.polyMin S N).domainSub j) +
        Metric.infDist (q : L2F ℝ D.Ω (formIdx n j)) ((F.polyMin S N).harmonicW j) +
        μ j N * Metric.infDist (D.complexMin.boundaryPart j (D.complexMin.domainIncl j u))
          ((F.polyMin S N).domainSub j)) :=
  Subcomplex.HasUniformProj.mixed_quasiOptimal hP (star_old_polySmoothedProjection_uniformMin F S)

end Poly

section General

variable (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)
  (F : MeshFamily (ParallelepipedWitness.starDomain A hA b)) (S : PolySeq)

/-- The old `Models.StarShaped.Parallelepiped.discretePoincare_poly_general`. -/
theorem star_old_discretePoincare_poly_general :
    ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
      {x : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n i)}
      (hx : x ∈ (F.poly S N).V i),
      (∀ y ∈ (F.poly S N).cyclesW i, inner ℝ y x = 0) →
        ‖x‖ ≤ c * ‖(ParallelepipedWitness.starDomain A hA b).complex.d i j
          ⟨x, (F.poly S N).le_domain i j hx⟩‖ :=
  star_old_discretePoincare_poly F S (Feec.Models.StarShaped.Parallelepiped.hasPoincare A hA b)

/-- The old `Models.StarShaped.Parallelepiped.mixed_wellPosed_poly_general`. -/
theorem star_old_mixed_wellPosed_poly_general :
    ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      ∀ (N : ℕ) (f : (F.poly S N).V j),
      (∃! x, (F.poly S N).toHilbertComplex.mixedForm i j k x =
        (F.poly S N).toHilbertComplex.mixedRHS i j f) ∧
      ∀ x : (F.poly S N).toHilbertComplex.MixedSpace i j,
        (F.poly S N).toHilbertComplex.mixedForm i j k x =
          (F.poly S N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ :=
  star_old_mixed_wellPosed_poly F S (Feec.Models.StarShaped.Parallelepiped.hasPoincare A hA b)

/-- The old `Models.StarShaped.Parallelepiped.mixed_quasiOptimal_poly_general`. -/
theorem star_old_mixed_quasiOptimal_poly_general :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)}
    {σ : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace i}
    {u : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace j}
    {q : (ParallelepipedWitness.starDomain A hA b).complex.harmonic j},
    (ParallelepipedWitness.starDomain A hA b).complex.IsMixedSolution i j k f σ u q →
    ∀ N : ℕ,
    ‖σ - (F.poly S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).fst‖ +
        ‖u - (F.poly S N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution
            (F.poly S N) hij hjk f).snd.snd : (F.poly S N).V j) :
              L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((F.poly S N).domainSub i) +
        Metric.infDist u ((F.poly S N).domainSub j) +
        Metric.infDist (q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j))
          ((F.poly S N).harmonicW j) +
        μ j N * Metric.infDist ((ParallelepipedWitness.starDomain A hA b).complex.boundaryPart j
          ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j u))
          ((F.poly S N).domainSub j)) :=
  star_old_mixed_quasiOptimal_poly F S (Feec.Models.StarShaped.Parallelepiped.hasPoincare A hA b)

end General

end StarShapedOld

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

/-- **Crank–Nicolson for every datum of a rate class in `D(A)`**: from `v = pₕ(0)` the error is
the spatial rate plus `‖ιₕ‖ (6 C_F (2C + ‖ιₕ‖ C' T) hᵅ ‖x‖_c + τₕ^{1/2} (6 C_F ‖A x‖ +
10/3 tₙ ‖pₕ(0)‖))`: `O(hᵅ + τₕ^{1/2})` uniformly in `h` (`p = 2`, `M = 1`, `K = 5/12`). -/
example {T : ℝ} (R : F.RateClass T) {x : E} (hx : x ∈ R.Data) (hxA : x ∈ A.domain)
    {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ) {n : ℕ} (hn : (n : ℝ) * τ h ∈ Icc 0 T)
    (hτT : τ h ^ (1 / 2 : ℝ) ≤ T) :
    ‖F.S (n * τ h) x - (F.crankNicolson τ hτ).sol h (R.p x h 0) n‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * (n * τ h)) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * (6 * F.boundConst * (2 * R.C + ‖F.incl h‖ * R.C' * T) *
            (R.meshSize h ^ R.α * R.classNorm x) +
          τ h ^ (1 / 2 : ℝ) * (6 * F.boundConst * ‖genExt A x‖ +
            10 / 3 * (n * τ h) * ‖R.p x h 0‖)) := by
  have e : ((2 : ℕ) : ℝ) / ((2 : ℕ) + 2) = 1 / 2 := by norm_num
  have key := (F.crankNicolson τ hτ).norm_S_sub_sol_le_uniform R hx hxA h (R.p x h 0) hn
    (by change τ h ^ (((2 : ℕ) : ℝ) / ((2 : ℕ) + 2)) ≤ T; rwa [e])
  change _ ≤ _ + ‖F.incl h‖ * (1 * _ + (1 + 1) * (((2 : ℕ) : ℝ) + 1) * _ * _ * _ +
    τ h ^ (((2 : ℕ) : ℝ) / ((2 : ℕ) + 2)) * ((1 + 1) * (((2 : ℕ) : ℝ) + 1) * _ * _ +
      1 * (5 / 12) * _ * 2 ^ (2 + 1) * _)) at key
  rw [e, sub_self, norm_zero, mul_zero, zero_add,
    show (F.crankNicolson τ hτ).τ h = τ h from rfl] at key
  refine key.trans_eq ?_
  push_cast
  ring

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

section SpectralOld

/-! ### Spectral methods: the FEEC theorem for reducing families

The truncation rates of reducing families (`norm_sub_sol_le_of_truncation`,
`infDist_sol_le_of_truncation`, `SpectralFamily.norm_sub_sol_le`), the frequency-truncation
theorems of `ℝᵈ` (`bandApprox_*`, `ebApprox_*`, `maxwellApprox_*` and the approximating FEEC
headlines) and the propagation-only `ℝ³` verdict `EuclideanVerdict` are now the fields of
`ReducingFamily.Verdict` (`ReducingFamily.feec`) and of the instance verdicts
`EuclideanEBVerdict`, `EuclideanMaxwellVerdict` that extend it. The theorems `spectral_old_*` and
`band_old_*` state the deleted results verbatim (the deleted abbreviations `bandApprox`,
`bandCore`, `ebCore`, `maxwellCore`, `maxwellPotentialCore` and `EuclideanVerdict` unfolded;
`SpectralFamily.toReducingFamily` is `ReducingFamily.ofSpectral`) and derive them from the new
API. -/

section Reducing

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] {H : HilbertComplex 𝕜 c W}
  {κ : Type*} (S : ReducingFamily H κ) (K : Submodule 𝕜 (PiLp 2 W))
  (hK : IsClosed (K : Set (PiLp 2 W)))

theorem spectral_old_norm_sub_sol_le_of_truncation {Data : Set (PiLp 2 W)}
    {classNorm : PiLp 2 W → ℝ} {meshSize : κ → ℝ} {α C : ℝ}
    (hrate : ∀ x ∈ Data, ∀ N, ‖x - (S.B N).starProjection x‖ ≤ C * meshSize N ^ α * classNorm x)
    {x : PiLp 2 W} (hx : x ∈ Data) (N : κ) {t : ℝ} (_ht : 0 ≤ t) :
    ‖H.waveGroup.S t x - (S.toApprox K hK).sol N ((S.B N).orthogonalProjectionOnto x) t‖ ≤
      C * meshSize N ^ α * classNorm x :=
  ((S.feec K hK).norm_sub_sol N x t).trans_le (hrate x hx N)

theorem spectral_old_infDist_sol_le_of_truncation (hKr : H.wave.IsReducing K)
    {Data : Set (PiLp 2 W)} {classNorm : PiLp 2 W → ℝ} {meshSize : κ → ℝ} {α C : ℝ}
    (hrate : ∀ x ∈ Data, ∀ N, ‖x - (S.B N).starProjection x‖ ≤ C * meshSize N ^ α * classNorm x)
    {x : PiLp 2 W} (hx : x ∈ Data) (hxK : x ∈ K) (N : κ) {t : ℝ} (ht : 0 ≤ t) :
    Metric.infDist ((S.toApprox K hK).sol N ((S.B N).orthogonalProjectionOnto x) t)
        (K : Set (PiLp 2 W)) ≤ C * meshSize N ^ α * classNorm x := by
  have V := S.feec K hK
  refine (V.residual_le (V.isReducing_iff.1 hKr).1 hxK N _ ht).trans ?_
  rw [ApproxFEEC.S_eq_waveGroup _ ht]
  exact (V.norm_sub_sol N x t).trans_le (hrate x hx N)

end Reducing

section Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] {H : HilbertComplex 𝕜 c W}
  (S : SpectralFamily H)

theorem spectral_old_norm_sub_sol_le (K : Submodule 𝕜 (PiLp 2 W))
    (hK : IsClosed (K : Set (PiLp 2 W))) {α : ℝ} {x : PiLp 2 W} (hx : x ∈ S.rateData α) (N : ℕ)
    {t : ℝ} (_ht : 0 ≤ t) :
    ‖H.waveGroup.S t x - ((ReducingFamily.ofSpectral S).toApprox K hK).sol N
        (((ReducingFamily.ofSpectral S).B N).orthogonalProjectionOnto x) t‖ ≤
      (1 / ((N : ℝ) + 1)) ^ α * S.rateNorm α x := by
  have h := S.norm_sub_P_le_rateNorm hx N
  rw [one_mul] at h
  exact (((ReducingFamily.ofSpectral S).feec K hK).norm_sub_sol N x t).trans_le h

end Spectral

theorem spectral_old_le_domain_of_isReducingPair {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {T : E →ₗ.[𝕜] F} {K : Submodule 𝕜 E} {L : Submodule 𝕜 F} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] [FiniteDimensional 𝕜 K] (h : T.IsReducingPair K L)
    (hT : Dense (T.domain : Set E)) : K ≤ T.domain :=
  h.le_domain hT

section EinsteinBianchiSpectral

open Feec.Instances.EinsteinBianchi

theorem spectral_old_einsteinBianchi_torus_approxFEEC : torusApprox.Verdict torusCore :=
  einsteinBianchi_torus_approxFEEC.toApprox

theorem spectral_old_einsteinBianchi_mirror_approxFEEC : mirrorApprox.Verdict mirrorCore :=
  einsteinBianchi_mirror_approxFEEC.toApprox

end EinsteinBianchiSpectral

section Band

open MeasureTheory Feec.Fourier Feec.Instances.EuclideanBand

variable {𝕜 : Type*} [RCLike 𝕜] {d : Type*} [Fintype d] {ι : Type*} [Fintype ι]
  {c : ComplexShape ι} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, CompleteSpace (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, IsScalarTower ℝ 𝕜 (E i)]
  (S : SymbolComplex 𝕜 (volume : Measure (EuclideanSpace ℝ d)) c E)
  (hS : ∀ i j, Continuous (S.m i j))
  (K : Submodule 𝕜 (PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))))
  (hK : IsClosed (K : Set (PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d)))))

theorem band_old_bandCore_data : ((bands S hS).toCore K hK).Data = ⊤ := rfl

theorem band_old_bandApprox_verdict :
    ((bands S hS).toApprox K hK).Verdict ((bands S hS).toCore K hK) :=
  ((bands S hS).feec K hK).toApprox

theorem band_old_bandApprox_sol (N : ℕ) (x : PiLp 2 fun i => Lp (E i) 2 volume) (t : ℝ) :
    ((bands S hS).toApprox K hK).sol N (((bands S hS).toApprox K hK).proj N x) t =
      (totalSub (S.band (freqBall N))).starProjection (S.toHilbertComplex.waveGroup.S t x) :=
  ((bands S hS).feec K hK).sol_eq N x t

theorem band_old_bandApprox_rate {s : ℝ} (hs : 0 ≤ s) {x : PiLp 2 fun i => Lp (E i) 2 volume}
    (hx : x ∈ sobolev 𝕜 E s) (N : ℕ) {t : ℝ} (_ht : 0 ≤ t) :
    ‖S.toHilbertComplex.waveGroup.S t x -
        ((bands S hS).toApprox K hK).sol N (((bands S hS).toApprox K hK).proj N x) t‖ ≤
      (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm 𝕜 s x :=
  (((bands S hS).feec K hK).norm_sub_sol N x t).trans_le
    (norm_sub_starProjection_le_of_mem_sobolev S hs hx N)

theorem band_old_bandApprox_norm_sub_sol (N : ℕ) (x : PiLp 2 fun i => Lp (E i) 2 volume)
    (t : ℝ) :
    ‖S.toHilbertComplex.waveGroup.S t x -
        ((bands S hS).toApprox K hK).sol N (((bands S hS).toApprox K hK).proj N x) t‖ =
      ‖x - (totalSub (S.band (freqBall N))).starProjection x‖ :=
  ((bands S hS).feec K hK).norm_sub_sol N x t

theorem band_old_bandApprox_sol_mem (hKr : S.toHilbertComplex.wave.IsReducing K)
    (hP : ∀ N, ∀ x ∈ K, (totalSub (S.band (freqBall N))).starProjection x ∈ K)
    {x : PiLp 2 fun i => Lp (E i) 2 volume} (hxK : x ∈ K) (N : ℕ) (t : ℝ) :
    ((bands S hS).toApprox K hK).sol N (((bands S hS).toApprox K hK).proj N x) t ∈ K :=
  ((bands S hS).feec K hK).sol_mem hKr hP hxK N t

end Band

section BandEB

open MeasureTheory Feec.Fourier Feec.Instances.EuclideanBand Feec.Models.Euclidean.BGG
  Feec.Fourier.BGG Feec.Fourier.GradCurl Feec.Fourier.SymCurl Feec.ShortHilbertComplex

theorem band_old_einsteinBianchi_euclidean_approxFEEC :
    ebApprox.Verdict (ebBands.toCore (totalSub constraint) isClosed_totalSub) :=
  einsteinBianchi_euclidean_band.toApprox

theorem band_old_ebApprox_norm_sub_sol (x : PiLp 2 Space) (N : ℕ) (t : ℝ) :
    ‖complex.waveGroup.S t x - ebApprox.sol N (ebApprox.proj N x) t‖ =
      ‖x - (totalSub ((Euclidean.symbolComplex bggFamily).band (freqBall N))).starProjection x‖ :=
  einsteinBianchi_euclidean_band.norm_sub_sol N x t

theorem band_old_ebApprox_sol_mem {x : PiLp 2 Space} (hx : x ∈ totalSub constraint) (N : ℕ)
    (t : ℝ) : ebApprox.sol N (ebApprox.proj N x) t ∈ totalSub constraint :=
  have V := einsteinBianchi_euclidean_band
  V.sol_mem V.isReducing (fun N _ hx => V.starProjection_mem N hx) hx N t

/-- The old `EuclideanEBVerdict`, a conjunction. -/
theorem band_old_einsteinBianchi_euclidean_band :
    ebApprox.Verdict (ebBands.toCore (totalSub constraint) isClosed_totalSub) ∧
    complex.wave.IsReducing (totalSub constraint) ∧
    (∀ (x : PiLp 2 Space) (N : ℕ) (t : ℝ),
      ‖complex.waveGroup.S t x - ebApprox.sol N (ebApprox.proj N x) t‖ =
        ‖x - (totalSub ((Euclidean.symbolComplex bggFamily).band (freqBall N))).starProjection
          x‖) ∧
    (∀ s : ℝ, 0 ≤ s → ∀ x ∈ sobolev ℂ (W3 ℂ Mat VM) s, ∀ (N : ℕ) (t : ℝ), 0 ≤ t →
      ‖complex.waveGroup.S t x - ebApprox.sol N (ebApprox.proj N x) t‖ ≤
        (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm ℂ s x) ∧
    (∀ s s' : ℝ, 0 ≤ s → s < s' → ∀ t : ℝ, ¬ ∃ C : ℝ, ∀ (N : ℕ), ∀ x ∈ totalSub constraint,
      x ∈ sobolev ℂ (W3 ℂ Mat VM) s →
      ‖complex.waveGroup.S t x - ebApprox.sol N (ebApprox.proj N x) t‖ ≤
        C * (1 / ((N : ℝ) + 1)) ^ s' * sobolevNorm ℂ s x) ∧
    (∀ x ∈ totalSub constraint, ∀ (N : ℕ) (t : ℝ),
      ebApprox.sol N (ebApprox.proj N x) t ∈ totalSub constraint) :=
  have V := einsteinBianchi_euclidean_band
  ⟨V.toApprox, V.isReducing, fun x N t => V.norm_sub_sol N x t,
    fun _ hs _ hx N t _ => (V.norm_sub_sol N _ t).trans_le (V.norm_sub_starProjection_le hs hx N),
    fun _ _ hs hss t => V.rate_optimal hs hss t, fun _ hx N t => band_old_ebApprox_sol_mem hx N t⟩

/-- The old `EuclideanVerdict` of `Feec.Instances.EinsteinBianchi` (well-posedness and
propagation on `ℝ³`), with `constrainedFEEC_wellPosed` and the reducing constraint of
`EuclideanEBVerdict`. -/
theorem spectral_old_einsteinBianchi_euclidean :
    (∀ x ∈ complex.wave.domain, ∀ T : ℝ,
      Evolution.IsClassicalSolution complex.wave (Icc 0 T) 0 (fun t => complex.waveGroup.S t x) ∧
      (∀ U, U 0 = x → Evolution.IsStrongSolution complex.wave (Icc 0 T) 0 U →
        EqOn U (fun t => complex.waveGroup.S t x) (Icc 0 T)) ∧
      ∀ t, ‖complex.waveGroup.S t x‖ = ‖x‖) ∧
    complex.wave.IsReducing (totalSub constraint) ∧
    ∀ t, ∀ x ∈ totalSub constraint, complex.waveGroup.S t x ∈ totalSub constraint :=
  ⟨fun _ hx T => have h := constrainedFEEC_wellPosed hx T; ⟨h.1, h.2.1, h.2.2.2⟩,
    einsteinBianchi_euclidean_band.isReducing, fun t _ hx => C0Group.map_le_iff_forall.1
      ((complex.isReducing_iff_waveGroup_invariant _).1 einsteinBianchi_euclidean_band.isReducing)
      t _ hx⟩

/-- The old `einsteinBianchi_constrainedFEEC_summary`, with its `ℝ³` row `EuclideanVerdict`. -/
theorem spectral_old_einsteinBianchi_constrainedFEEC_summary :
    (Instances.EinsteinBianchi.TorusVerdict ∧ Instances.EinsteinBianchi.TorusSobolevVerdict ∧
      Instances.EinsteinBianchi.TorusNonvacuous) ∧
    ((∀ x ∈ complex.wave.domain, ∀ T : ℝ,
      Evolution.IsClassicalSolution complex.wave (Icc 0 T) 0 (fun t => complex.waveGroup.S t x) ∧
      (∀ U, U 0 = x → Evolution.IsStrongSolution complex.wave (Icc 0 T) 0 U →
        EqOn U (fun t => complex.waveGroup.S t x) (Icc 0 T)) ∧
      ∀ t, ‖complex.waveGroup.S t x‖ = ‖x‖) ∧
    complex.wave.IsReducing (totalSub constraint) ∧
    ∀ t, ∀ x ∈ totalSub constraint, complex.waveGroup.S t x ∈ totalSub constraint) ∧
    (Instances.EinsteinBianchi.MirrorVerdict ∧ Instances.EinsteinBianchi.MirrorSobolevVerdict ∧
      Instances.EinsteinBianchi.MirrorNonvacuous) ∧
    Instances.EinsteinBianchi.MirrorFEMVerdict ∧ Instances.EinsteinBianchi.StandardCubeVerdict :=
  have h := Instances.EinsteinBianchi.einsteinBianchi_constrainedFEEC_summary
  ⟨⟨h.1.1.toTorusVerdict, h.1⟩, spectral_old_einsteinBianchi_euclidean,
    ⟨h.2.1.1.toMirrorVerdict, h.2.1⟩, h.2.2⟩

end BandEB

section BandMaxwell

open MeasureTheory Feec.Fourier Feec.Instances.EuclideanBand Feec.Models.Euclidean.DeRham
  Feec.Instances.Maxwell Feec.Fourier.Exterior

variable (d : Type*) [Fintype d] [LinearOrder d] (a : ℕ)

theorem band_old_maxwell_euclidean_approxFEEC :
    (maxwellApprox d a).Verdict
      ((maxwellBands d a).toCore (windowGauss (complex d) a) (isClosed_gauss _ _)) :=
  (maxwell_euclidean_band d a).toApprox

theorem band_old_maxwellApprox_sol_mem {x : PiLp 2 fun i : Fin 3 => L2Form d (a + i)}
    (hx : x ∈ windowGauss (complex d) a) (N : ℕ) (t : ℝ) :
    (maxwellApprox d a).sol N ((maxwellApprox d a).proj N x) t ∈ windowGauss (complex d) a :=
  have V := maxwell_euclidean_band d a
  V.sol_mem V.isReducing (fun N _ hx => V.starProjection_mem N hx) hx N t

theorem band_old_maxwellApprox_norm_sub_sol (x : PiLp 2 fun i : Fin 3 => L2Form d (a + i))
    (N : ℕ) (t : ℝ) :
    ‖((complex d).window a 3).waveGroup.S t x -
        (maxwellApprox d a).sol N ((maxwellApprox d a).proj N x) t‖ =
      ‖x - (totalSub ((maxwellSymbol d a).band (freqBall N))).starProjection x‖ :=
  (maxwell_euclidean_band d a).norm_sub_sol N x t

/-- The old `EuclideanMaxwellVerdict`, a conjunction. -/
theorem band_old_maxwell_euclidean_band :
    (maxwellApprox d a).Verdict
      ((maxwellBands d a).toCore (windowGauss (complex d) a) (isClosed_gauss _ _)) ∧
    ((complex d).window a 3).wave.IsReducing (windowGauss (complex d) a) ∧
    (∀ (x : PiLp 2 fun i : Fin 3 => L2Form d (a + i)) (N : ℕ) (t : ℝ),
      ‖((complex d).window a 3).waveGroup.S t x -
          (maxwellApprox d a).sol N ((maxwellApprox d a).proj N x) t‖ =
        ‖x - (totalSub ((maxwellSymbol d a).band (freqBall N))).starProjection x‖) ∧
    (∀ s : ℝ, 0 ≤ s → ∀ x ∈ sobolev ℂ (fun i : Fin 3 => Form ℂ d (a + i)) s,
      ∀ (N : ℕ) (t : ℝ), 0 ≤ t →
      ‖((complex d).window a 3).waveGroup.S t x -
          (maxwellApprox d a).sol N ((maxwellApprox d a).proj N x) t‖ ≤
        (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm ℂ s x) ∧
    (∀ x ∈ windowGauss (complex d) a, ∀ (N : ℕ) (t : ℝ),
      (maxwellApprox d a).sol N ((maxwellApprox d a).proj N x) t ∈ windowGauss (complex d) a) :=
  have V := maxwell_euclidean_band d a
  ⟨V.toApprox, V.isReducing, fun x N t => V.norm_sub_sol N x t,
    fun _ hs _ hx N t _ => (V.norm_sub_sol N _ t).trans_le (V.norm_sub_starProjection_le hs hx N),
    fun _ hx N t => band_old_maxwellApprox_sol_mem d a hx N t⟩

theorem band_old_maxwell_euclidean_potential_approxFEEC :
    (maxwellPotentialApprox d a).Verdict ((maxwellBands d a).toCore
      (potential ℂ fun i : Fin 3 => L2Form d (a + i)) isClosed_potential) :=
  ((maxwellBands d a).feec _ _).toApprox

end BandMaxwell

end SpectralOld

section CrownFields

/-! ### The crown fields: every field of the crown is the layer verdict -/

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α] [CharZero α]
  {V : α → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]
  {H : HilbertComplex 𝕜 (ComplexShape.up α) V} {κ : Type*} (F : ConformingFamily H κ) (a : α)
  (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
  (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))

example (hcr : ∀ i, H.ClosedRangeAt i) (j : α) [FiniteDimensional 𝕜 (H.harmonic j)] :
    type_of% (F.staticFEEC hcr j) :=
  F.feec.static hcr j

example : type_of% (approxFEEC _ (F.windowFEEC a m K hK).toCore) := F.feec.wave a m K hK

example : type_of% (constrainedFEEC (F.windowFEEC a m K hK)) := F.feec.constrained a m K hK

example (hcr : ∀ i, (H.window a m).ClosedRangeAt i)
    [∀ i, FiniteDimensional 𝕜 ((H.window a m).harmonic i)] :
    type_of% ((F.windowFEEC a m K hK).heatFEEC hcr) :=
  F.feec.heat a m K hK hcr

example (Θ : (F.windowFEEC a m K hK).toApprox.TimeScheme) :
    type_of% (dissipFEEC_fullyDiscrete (F.windowFEEC a m K hK).toCore Θ) :=
  (F.feec.full a m K hK).wave Θ

example (hcr : ∀ i, (H.window a m).ClosedRangeAt i)
    [∀ i, FiniteDimensional 𝕜 ((H.window a m).harmonic i)]
    (Θ : (F.windowFEEC a m K hK).toHeat.TimeScheme) :
    type_of% (dissipFEEC_fullyDiscrete ((F.windowFEEC a m K hK).heatCore hcr) Θ) :=
  (F.feec.full a m K hK).heat hcr Θ

/-- The θ-schemes (`θ ≥ 1/2`; implicit Euler at `θ = 1`) and Crank–Nicolson are time schemes of
the wave and heat discretizations, so their fully discrete verdicts are fields of the crown. -/
example (θ : ℝ) (hθ : 1 / 2 ≤ θ) (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h)
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i)
    [∀ i, FiniteDimensional 𝕜 ((H.window a m).harmonic i)] :
    ((F.windowFEEC a m K hK).toApprox.thetaScheme θ hθ τ hτ).Verdict
        (F.windowFEEC a m K hK).toCore ∧
      ((F.windowFEEC a m K hK).toApprox.crankNicolson τ hτ).Verdict
        (F.windowFEEC a m K hK).toCore ∧
      ((F.windowFEEC a m K hK).toHeat.thetaScheme θ hθ τ hτ).Verdict
        ((F.windowFEEC a m K hK).heatCore hcr) ∧
      ((F.windowFEEC a m K hK).toHeat.crankNicolson τ hτ).Verdict
        ((F.windowFEEC a m K hK).heatCore hcr) :=
  ⟨(F.feec.full a m K hK).wave _, (F.feec.full a m K hK).wave _,
    (F.feec.full a m K hK).heat hcr _, (F.feec.full a m K hK).heat hcr _⟩

example {T : ℝ} (R : (F.windowFEEC a m K hK).toApprox.RateClass T)
    {x : PiLp 2 fun i : Fin m => V (a + i)} (hx : x ∈ R.Data) (h : κ)
    (v : (F.windowFEEC a m K hK).toApprox.X h) {τ c : ℝ} (hτ : 0 ≤ τ)
    (hc : τ * ‖(F.windowFEEC a m K hK).toApprox.L h‖ ≤ c) (hc1 : c < 1)
    {w : ℕ → (F.windowFEEC a m K hK).toApprox.X h}
    (hw : TimeStepping.IsLeapfrog ((F.windowFEEC a m K hK).toApprox.L h) τ w) (h0 : w 0 = v)
    {n : ℕ} (hn : (n : ℝ) * τ ∈ Icc 0 T) :
    type_of% ((F.windowFEEC a m K hK).toApprox.norm_S_sub_leapfrog_le R hx h v hτ hc hc1 hw h0
      hn) :=
  (F.feec.full a m K hK).leapfrog R hx h v hτ hc hc1 hw h0 hn

open scoped InnerProductSpace in
example (B : (PiLp 2 fun i : Fin m => V (a + i)) →L[𝕜] PiLp 2 fun i : Fin m => V (a + i))
    (hB : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0) :
    type_of% (constrainedFEEC_perturbed (F.windowFEEC a m K hK) B hB) :=
  F.feec.perturbed a m K hK B hB

variable {ρ : Type*} (J : F.Jackson ρ)

example (s : ρ) {i j k : α} (hij : (ComplexShape.up α).Rel i j)
    (hjk : (ComplexShape.up α).Rel j k) (hj : H.ClosedRangeAt j) (hk : H.ClosedRangeAt k) :
    type_of% (F.rate J s hij hjk hj hk) :=
  (F.feec_rated J).rate_static s hij hjk hj hk

example {T : ℝ} (s : ρ) {L : ℝ} (hL : 0 ≤ L) {x : PiLp 2 fun i : Fin m => V (a + i)}
    (hx : x ∈ (ConstrainedFEEC.RateClass.ofJackson (F.windowFEEC a m K hK) (J.window a m) T s
      hL).Data) (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    type_of% ((F.windowFEEC a m K hK).rate_le
      (ConstrainedFEEC.RateClass.ofJackson _ (J.window a m) T s hL) hx h ht) :=
  (F.feec_rated J).rate_wave a m K hK s hL hx h ht

example (hcr : ∀ i, (H.window a m).ClosedRangeAt i)
    [∀ i, FiniteDimensional 𝕜 ((H.window a m).harmonic i)] (s : ρ) :
    type_of% ((F.windowFEEC a m K hK).rate_heat hcr
      ((F.windowFEEC a m K hK).totalJackson (J.window a m)) s) :=
  (F.feec_rated J).rate_heat a m K hK hcr s

example : type_of% (constrainedFEEC_fullRate (F.windowFEEC a m K hK) (J.window a m)) :=
  (F.feec_rated J).rate_full a m K hK

end CrownFields

section CrownCube

open Feec.Models.Cube.FEM in
/-- On the cube, the heat verdict of `crown_heat_nonvacuous` (a nonzero datum in its core) is the
field `heat` of the crown of the finite element family of every admissible sequence, on the
window `HΛ⁰(Q) → ⋯ → HΛⁿ(Q)` with the trivial constraint. -/
example (n : ℕ) [NeZero n] (S : FiniteElement.PolySeq) :
    (heatFamily n S).toHeat.Verdict ((heatFamily n S).heatCore (closedRangeAt_heatWindow n)) :=
  (polyFamily n S).feec.heat 0 (n + 1) ⊤ _ (closedRangeAt_heatWindow n)

end CrownCube

noncomputable section EinsteinBianchiOld

open Feec.Instances Feec.Instances.EinsteinBianchi Feec.Instances.EinsteinBianchi.FEM Metric

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-! ### Mirror boundary conditions -/

section Mirror

open Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.FEM (ParitySmoothingEstimates meshSize meshSize_pos)
open Feec.FiniteElement (PolySeq)
open Feec.Models.Cube.MirrorBGG (SpaceQ complexQ tsdQ)

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- The old `mirrorFEM_hconv` (model convergence read on `mirrorFEMApprox`), from the verdict: the
discrete solutions from `π' ξ₀` converge. -/
theorem eb_old_mirrorFEM_hconv : ∀ x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq, ∀ T : ℝ, 0 < T →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∃ v : (mirrorFEMApprox hT hB).X N,
      ∀ t ∈ Icc 0 T, ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤ ε := by
  intro x hx T _ ε hε
  have V := mirrorFEMApprox_verdict hT hB
  have hxc := V.closure.ge hx.1
  have hc := V.converges hxc (V.tendsto_incl_proj hxc) T
  rw [Metric.tendstoUniformlyOn_iff] at hc
  filter_upwards [hc ε hε] with N hN
  refine ⟨(mirrorFEMApprox hT hB).proj N x, fun t ht => ?_⟩
  have h := hN t ht
  rw [dist_eq_norm, ApproxFEEC.S_eq_waveGroup _ ht.1] at h
  rw [← V.sol]
  exact h.le

/-- The old orbit core `mirrorFEMCore`, with its definition unfolded. -/
abbrev mirrorFEMCore : (mirrorFEMApprox hT hB).Core :=
  ApproxFEEC.orbitCore (mirrorFEMApprox_isOrthogonal hT hB) (tsdQℝ ⊓ complexQℝ.wave.domainSq)
    (eb_old_mirrorFEM_hconv hT hB)

/-- The old helpers of the orbit rate classes (`mirrorSource_zero`, `toSourceFree`, `pairInit`,
`mirrorFEMApprox_sol_pairInit`, `norm_sub_sol_pairInit_le`), verbatim. -/
private theorem mirrorSource_zero (N : ℕ) (t : ℝ) : mirrorSource hT hB N 0 t = 0 :=
  ext_inner_right ℝ fun v => by
    rw [inner_mirrorSource, Pi.zero_apply, inner_zero_left, inner_zero_left]

/-- A solution of (6.5) with the (vanishing) projected source as a solution without source. -/
private def toSourceFree (N : ℕ) {T : ℝ}
    (s : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0)) :
    Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T 0 :=
  s.ofEqOn fun t _ => (mirrorSource_zero hT hB N t).symm

/-- The discrete initial value of a pair of solutions of (6.5) (real and imaginary parts). -/
private def pairInit (N : ℕ) {T : ℝ} (hT0 : 0 ≤ T)
    (s s' : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0)) :
    (mirrorFEMApprox hT hB).X N :=
  WithLp.toLp 2 (DiscreteSolution.hiddenInit hT0 (toSourceFree hT hB N s),
    DiscreteSolution.hiddenInit hT0 (toSourceFree hT hB N s'))

/-- **The complex discrete solution from a pair of solutions of (6.5)**:
`ι' e^{tL'}(v, v') = Rt(state of s)(t) + i Rt(state of s')(t)`. -/
private theorem mirrorFEMApprox_sol_pairInit (N : ℕ) {T : ℝ} (hT0 : 0 ≤ T)
    (s s' : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0)) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    (mirrorFEMApprox hT hB).sol N (pairInit hT hB N hT0 s s') t =
      mirrorReEmb (dState hT hB N (toSourceFree hT hB N s) t) +
        mulI (mirrorReEmb (dState hT hB N (toSourceFree hT hB N s') t)) :=
  (mirrorFEMApprox_sol hT hB N _ _ t).trans (congrArg₂ (· + ·)
    (mirrorFEMReal_sol_eq hT hB N hT0 _ ht) (congrArg mulI (mirrorFEMReal_sol_eq hT hB N hT0 _ ht)))

/-- **The error of a pair of solutions of (6.5)** against the TSD solution: at most the error of
the real part plus the error of the imaginary part, each being the quantity of
`mirror_waveFEM` for the data `ξ₀` and `-i ξ₀`. -/
private theorem norm_sub_sol_pairInit_le (N : ℕ) {T : ℝ} (hT0 : 0 ≤ T)
    (s s' : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0)) {t : ℝ}
    (ht : t ∈ Icc 0 T) {y : PiLp 2 SpaceQ} (hy : y ∈ totalSub tsdQ) :
    ‖y - (mirrorFEMApprox hT hB).sol N (pairInit hT hB N hT0 s s') t‖ ≤
      tsdErr y (dState hT hB N (toSourceFree hT hB N s) t) +
        tsdErr (-Complex.I • y) (dState hT hB N (toSourceFree hT hB N s') t) := by
  rw [mirrorFEMApprox_sol_pairInit hT hB N hT0 s s' ht, mulI_apply, ← sub_sub]
  exact norm_sub_mirrorReEmb_le hy _ _

/-- The constant of `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain`. -/
def mirrorRateK : ℝ := (mirror_waveFEM_rate_of_mem_domain hT hB).choose

private theorem mirrorRateK_nonneg : 0 ≤ mirrorRateK hT hB :=
  (mirror_waveFEM_rate_of_mem_domain hT hB).choose_spec.1

-- the budget of the deleted `EinsteinBianchiFEMMirrorCore` (main): obtaining the discrete
-- solution of the model rate unfolds the mirror scheme `mirrorWave`
set_option maxHeartbeats 400000 in
/-- The model rate (`mirror_waveFEM_rate_of_mem_domain`) for one TSD datum of `D(L³)`. -/
private theorem mirrorFEM_rate_datum (N : ℕ) {x : PiLp 2 SpaceQ}
    (hx : x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq) (h3 : (tsdDatumOf hx).LLU₀ ∈ complexQ.wave.domain) {T : ℝ} (hT0 : 0 < T) :
    ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0),
      ∀ t ∈ Icc 0 T, tsdErr ((tsdDatumOf hx).U t) (dState hT hB N (toSourceFree hT hB N sh) t) ≤
        mirrorRateK hT hB * l3Norm (tsdDatumOf hx) h3 * (1 + t) * meshSize N := by
  obtain ⟨sh, -, hsh⟩ := (mirror_waveFEM_rate_of_mem_domain hT hB).choose_spec.2 N
    (tsdDatumOf hx) h3 hT0
    (tsdDatumOf hx).U_zero ((tsdDatumOf hx).isStrongSolution T)
  exact ⟨sh, hsh⟩

/-- **The model rate of the mirror scheme for TSD data of `D(L³)`**
(`mirror_waveFEM_rate_of_mem_domain` for `ξ₀` and `-i ξ₀`): for every `N`, some discrete initial
value gives `‖e^{tL} ξ₀ - ι' e^{tL'} v‖ ≤ 2 K (1 + T) h_N ‖ξ₀‖_{L³}` on `[0, T]`. -/
private theorem mirrorFEM_hrate {T : ℝ} (hT0 : 0 < T) :
    ∀ x ∈ mirrorL3Data, ∀ N, ∃ v : (mirrorFEMApprox hT hB).X N, ∀ t ∈ Icc 0 T,
      ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤
        2 * mirrorRateK hT hB * (1 + T) * meshSize N ^ (1 : ℝ) * mirrorL3Norm x := by
  rintro x ⟨hx, h3⟩ N
  obtain ⟨sh, hsh⟩ := mirrorFEM_rate_datum hT hB N hx h3 hT0
  obtain ⟨sh', hsh'⟩ := mirrorFEM_rate_datum hT hB N (neg_I_smul_mem hx) (mem_LLU₀_negI hx h3) hT0
  refine ⟨pairInit hT hB N hT0.le sh sh', fun t ht => ?_⟩
  have hyU : complexQℝ.waveGroup.S t x = (tsdDatumOf hx).U t := complexQℝ_waveGroup ht.1 x
  have hyU' : (tsdDatumOf (neg_I_smul_mem hx)).U t = -Complex.I • (tsdDatumOf hx).U t :=
    (complexQ.waveGroup.S t).map_smul (-Complex.I) x
  have hb := norm_sub_sol_pairInit_le hT hB N hT0.le sh sh' ht ((tsdDatumOf hx).U_tsd t)
  have e1 := hsh t ht
  have e2 := hsh' t ht
  rw [hyU', l3Norm_negI hx h3] at e2
  rw [hyU, mirrorL3Norm_of_mem hx h3, Real.rpow_one]
  have hc := l3Norm_nonneg (tsdDatumOf hx) h3
  have hm := (meshSize_pos N).le
  have hK := mirrorRateK_nonneg hT hB
  have h1t : (1 + t) ≤ (1 + T) := by linarith [ht.2]
  have h4 : mirrorRateK hT hB * l3Norm (tsdDatumOf hx) h3 * (1 + t) * meshSize N ≤
      mirrorRateK hT hB * l3Norm (tsdDatumOf hx) h3 * (1 + T) * meshSize N :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1t (mul_nonneg hK hc)) hm
  have h5 : mirrorRateK hT hB * l3Norm (tsdDatumOf hx) h3 * (1 + T) * meshSize N * 2 =
      2 * mirrorRateK hT hB * (1 + T) * meshSize N * l3Norm (tsdDatumOf hx) h3 := by ring
  linarith

/-- **The rate class of order `1`**: TSD data of `D(L³)` with the norm
`‖ξ₀‖ + ‖Lξ₀‖ + ‖L²ξ₀‖ + ‖L³ξ₀‖`, `C = 6 K (1 + T)` and `C' = 0` (orbit comparison). -/
private def mirrorFEMRate (T : ℝ) (hT0 : 0 < T) : (mirrorFEMApprox hT hB).RateClass T :=
  ApproxFEEC.orbitRate (mirrorFEMApprox_isOrthogonal hT hB) mirrorL3Data mirrorL3Norm meshSize 1
    (2 * mirrorRateK hT hB * (1 + T)) (mirrorFEM_hrate hT hB hT0)

/-- The constant of `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev_of_add_two`. -/
def mirrorSobK : ℝ := (mirror_waveFEM_rate_sobolev_of_add_two hT hB).choose

private theorem mirrorSobK_nonneg : 0 ≤ mirrorSobK hT hB :=
  (mirror_waveFEM_rate_sobolev_of_add_two hT hB).choose_spec.1

-- the budget of the deleted `EinsteinBianchiFEMMirrorCore` (main): obtaining the discrete
-- solution of the model rate unfolds the mirror scheme `mirrorWave`
set_option maxHeartbeats 400000 in
/-- The model Sobolev rate (`mirror_waveFEM_rate_sobolev_of_add_two`) for one TSD datum. -/
private theorem mirrorFEM_sobolev_datum (N : ℕ) {x : PiLp 2 SpaceQ}
    (hx : x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h : MemSobState (2 + s) x) {T : ℝ} (hT0 : 0 < T) :
    ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0),
      ∀ t ∈ Icc 0 T, tsdErr ((tsdDatumOf hx).U t) (dState hT hB N (toSourceFree hT hB N sh) t) ≤
        mirrorSobK hT hB * √(sobState (2 + s) x) * (1 + t) * meshSize N ^ s := by
  obtain ⟨sh, -, hsh⟩ := (mirror_waveFEM_rate_sobolev_of_add_two hT hB).choose_spec.2 N
    (tsdDatumOf hx) hs0 hs1 h hT0 (tsdDatumOf hx).U_zero ((tsdDatumOf hx).isStrongSolution T)
  exact ⟨sh, hsh⟩

/-- **The model Sobolev rate of the mirror scheme** (`mirror_waveFEM_rate_sobolev_of_add_two` for
`ξ₀` and `-i ξ₀`): `‖e^{tL} ξ₀ - ι' e^{tL'} v‖ ≤ 2 K (1 + T) h_Nˢ ‖ξ₀‖_{2+s}` on `[0, T]`. -/
private theorem mirrorFEM_hrate_sobolev {T s : ℝ} (hT0 : 0 < T) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ x ∈ mirrorSobData s, ∀ N, ∃ v : (mirrorFEMApprox hT hB).X N, ∀ t ∈ Icc 0 T,
      ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤
        2 * mirrorSobK hT hB * (1 + T) * meshSize N ^ s * √(sobState (2 + s) x) := by
  rintro x ⟨hx, h⟩ N
  obtain ⟨sh, hsh⟩ := mirrorFEM_sobolev_datum hT hB N hx hs0 hs1 h hT0
  obtain ⟨sh', hsh'⟩ := mirrorFEM_sobolev_datum hT hB N (neg_I_smul_mem hx) hs0 hs1
    (memSobState_negI h) hT0
  refine ⟨pairInit hT hB N hT0.le sh sh', fun t ht => ?_⟩
  have hyU : complexQℝ.waveGroup.S t x = (tsdDatumOf hx).U t := complexQℝ_waveGroup ht.1 x
  have hyU' : (tsdDatumOf (neg_I_smul_mem hx)).U t = -Complex.I • (tsdDatumOf hx).U t :=
    (complexQ.waveGroup.S t).map_smul (-Complex.I) x
  have hb := norm_sub_sol_pairInit_le hT hB N hT0.le sh sh' ht ((tsdDatumOf hx).U_tsd t)
  have e1 := hsh t ht
  have e2 := hsh' t ht
  rw [hyU', sobState_negI] at e2
  rw [hyU]
  have hc := Real.sqrt_nonneg (sobState (2 + s) x)
  have hm : 0 ≤ meshSize N ^ s := Real.rpow_nonneg (meshSize_pos N).le s
  have hK := mirrorSobK_nonneg hT hB
  have h1t : (1 + t) ≤ (1 + T) := by linarith [ht.2]
  have h4 : mirrorSobK hT hB * √(sobState (2 + s) x) * (1 + t) * meshSize N ^ s ≤
      mirrorSobK hT hB * √(sobState (2 + s) x) * (1 + T) * meshSize N ^ s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1t (mul_nonneg hK hc)) hm
  have h5 : mirrorSobK hT hB * √(sobState (2 + s) x) * (1 + T) * meshSize N ^ s * 2 =
      2 * mirrorSobK hT hB * (1 + T) * meshSize N ^ s * √(sobState (2 + s) x) := by ring
  linarith

/-- **The rate class of order `s ∈ [0, 1]`**: TSD data with mirror extension in `H^{2+s}`, norm
`‖ξ₀‖_{2+s}`, `C = 6 K (1 + T)` and `C' = 0`. -/
private def mirrorFEMRateSobolev (T s : ℝ) (hT0 : 0 < T) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (mirrorFEMApprox hT hB).RateClass T :=
  ApproxFEEC.orbitRate (mirrorFEMApprox_isOrthogonal hT hB) (mirrorSobData s)
    (fun x => √(sobState (2 + s) x)) meshSize s (2 * mirrorSobK hT hB * (1 + T))
    (mirrorFEM_hrate_sobolev hT hB hT0 hs0 hs1)

/-- The old `einsteinBianchi_mirrorFEM_approxFEEC` (the orbit core). -/
theorem eb_old_mirrorFEM_approxFEEC :
    (mirrorFEMApprox hT hB).Verdict (mirrorFEMCore hT hB) :=
  approxFEEC _ _

/-- The old `einsteinBianchi_mirrorFEM_converges`, from `MirrorFEMApprox.Verdict`. -/
theorem eb_old_mirrorFEM_converges {x : PiLp 2 SpaceQ} (hx : x ∈ tsdQℝ) (T : ℝ) :
    (∀ t, complexQℝ.waveGroup.S t x ∈ tsdQℝ) ∧
    Tendsto (fun N => (mirrorFEMApprox hT hB).incl N ((mirrorFEMApprox hT hB).proj N x)) atTop
      (𝓝 x) ∧
    ∀ v : ∀ N, (mirrorFEMApprox hT hB).X N,
      Tendsto (fun N => (mirrorFEMApprox hT hB).incl N (v N)) atTop (𝓝 x) →
      TendstoUniformlyOn (fun N t => (mirrorFEMApprox hT hB).sol N (v N) t)
        (fun t => complexQℝ.waveGroup.S t x) atTop (Icc 0 T) ∧
      TendstoUniformlyOn (fun N t => infDist ((mirrorFEMApprox hT hB).sol N (v N) t)
        (tsdQℝ : Set (PiLp 2 SpaceQ))) (fun _ => 0) atTop (Icc 0 T) := by
  have V := mirrorFEMApprox_verdict hT hB
  have hxc := V.closure.ge hx
  have hsol : ∀ (v : ∀ N, (mirrorFEMApprox hT hB).X N), ∀ᶠ N in atTop, EqOn
      (fun t => (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N (v N) t)
      (fun t => (mirrorFEMApprox hT hB).sol N (v N) t) (Icc 0 T) := fun v =>
    Eventually.of_forall fun N t _ => V.sol N (v N) t
  refine ⟨fun t => V.isReducing_iff_invariant.1 V.isReducing t x hx, V.tendsto_incl_proj hxc,
    fun v hv => ⟨((V.converges hxc hv T).congr (hsol v)).congr_right fun t ht =>
      DFunLike.congr_fun (ApproxFEEC.S_eq_waveGroup _ ht.1) x,
      (V.residual_tendsto (V.isReducing_iff.1 V.isReducing).1 hx hxc hv T).congr
        ((hsol v).mono fun N hN t ht => congrArg (infDist · _) (hN ht))⟩⟩

/-- The old `einsteinBianchi_mirrorFEM_rate` (the orbit rate class), verbatim. -/
theorem eb_old_mirrorFEM_rate {T : ℝ} (hT0 : 0 < T) {x : PiLp 2 SpaceQ}
    (hx : x ∈ mirrorL3Data) (N : ℕ) (v : (mirrorFEMApprox hT hB).X N) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤
      3 * (2 * mirrorRateK hT hB * (1 + T)) * (meshSize N * mirrorL3Norm x) +
        ‖(mirrorFEMApprox hT hB).proj N x - v‖ := by
  have h := (eb_old_mirrorFEM_approxFEEC hT hB).rate (mirrorFEMRate hT hB T hT0) hx N v ht
  rw [ApproxFEEC.S_eq_waveGroup _ ht.1] at h
  have hp : (mirrorFEMRate hT hB T hT0).p x N 0 = (mirrorFEMApprox hT hB).proj N x :=
    C0Group.S_zero_apply _ _
  have hι := (mirrorFEMApprox_isOrthogonal hT hB).norm_incl_le_one N
  have hC : (mirrorFEMRate hT hB T hT0).C = 3 * (2 * mirrorRateK hT hB * (1 + T)) := rfl
  have hC' : (mirrorFEMRate hT hB T hT0).C' = 0 := rfl
  have hm : (mirrorFEMRate hT hB T hT0).meshSize N ^ (mirrorFEMRate hT hB T hT0).α *
      (mirrorFEMRate hT hB T hT0).classNorm x = meshSize N * mirrorL3Norm x := by
    change meshSize N ^ (1 : ℝ) * mirrorL3Norm x = _
    rw [Real.rpow_one]
  simp only [hC, hC', hm, hp, mul_zero, zero_mul, add_zero] at h
  have hn := norm_nonneg ((mirrorFEMApprox hT hB).proj N x - v)
  linarith [mul_le_of_le_one_left hn hι]

/-- The old `einsteinBianchi_mirrorFEM_rate_sobolev` (the orbit rate class), verbatim. -/
theorem eb_old_mirrorFEM_rate_sobolev {T s : ℝ} (hT0 : 0 < T) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorSobData s) (N : ℕ)
    (v : (mirrorFEMApprox hT hB).X N) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤
      3 * (2 * mirrorSobK hT hB * (1 + T)) * (meshSize N ^ s * √(sobState (2 + s) x)) +
        ‖(mirrorFEMApprox hT hB).proj N x - v‖ := by
  have h := (eb_old_mirrorFEM_approxFEEC hT hB).rate
    (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1) hx N v ht
  rw [ApproxFEEC.S_eq_waveGroup _ ht.1] at h
  have hp : (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).p x N 0 =
      (mirrorFEMApprox hT hB).proj N x := C0Group.S_zero_apply _ _
  have hι := (mirrorFEMApprox_isOrthogonal hT hB).norm_incl_le_one N
  have hC : (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).C =
      3 * (2 * mirrorSobK hT hB * (1 + T)) := rfl
  have hC' : (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).C' = 0 := rfl
  have hm : (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).meshSize N ^
      (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).α *
      (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).classNorm x =
        meshSize N ^ s * √(sobState (2 + s) x) := rfl
  simp only [hC, hC', hm, hp, mul_zero, zero_mul, add_zero] at h
  have hn := norm_nonneg ((mirrorFEMApprox hT hB).proj N x - v)
  linarith [mul_le_of_le_one_left hn hι]

/-- The old `einsteinBianchi_mirrorFEM_approxFEEC_elliptic` (the direct verdict on the elliptic
core). -/
theorem eb_old_mirrorFEM_approxFEEC_elliptic :
    (mirrorFEMApprox hT hB).Verdict (mirrorEllCore hT hB) :=
  approxFEEC _ _

/-- The old `einsteinBianchi_mirrorFEM_rate_elliptic`, from `MirrorFEMApprox.Verdict` (the
comparison initial value does not depend on the horizon). -/
theorem eb_old_mirrorFEM_rate_elliptic {T : ℝ} {x : PiLp 2 SpaceQ}
    (hx : x ∈ mirrorL3Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖complexQℝ.waveGroup.S t x -
        (mirrorFEMApprox hT hB).sol N ((mirrorEllCmp hT hB T).p x N 0) t‖ ≤
      (4 * mirrorEllK (C := C) + 8 * mirrorEllK (C := C) * t) *
        (meshSize N * mirrorL3Norm x) := by
  rw [mirrorEllCmp_p_zero_eq_init hT hB T]
  exact (mirrorFEMApprox_verdict hT hB).rate_init hx N ht.1

/-- The old `einsteinBianchi_mirrorFEM_rate_sobolev_elliptic`, from `MirrorFEMApprox.Verdict` (the
comparison initial value does not depend on the horizon). -/
theorem eb_old_mirrorFEM_rate_sobolev_elliptic {T s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorSobData s) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖complexQℝ.waveGroup.S t x -
        (mirrorFEMApprox hT hB).sol N ((mirrorEllCmp hT hB T).p x N 0) t‖ ≤
      (6 * mirrorEllK (C := C) + 12 * mirrorEllK (C := C) * t) *
        (meshSize N ^ s * √(sobState (2 + s) x)) := by
  rw [mirrorEllCmp_p_zero_eq_init hT hB T]
  exact (mirrorFEMApprox_verdict hT hB).rate_sobolev_init hs0 hs1 hx N ht.1

/-- The old `einsteinBianchi_mirrorFEM_ofComplexCrime`, from `MirrorFEMApprox.Verdict`. -/
theorem eb_old_mirrorFEM_ofComplexCrime :
    (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).Verdict
      (ApproxFEEC.ofComplexCrimeCore (mirrorComplex hT hB)) ∧
    (∀ N v t, (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N v t =
      (mirrorFEMApprox hT hB).sol N v t) ∧
    (∀ N, (mirrorFEMApprox hT hB).L N = diffWave (mirrorD hT hB N)) ∧
    (ApproxFEEC.ofComplexCrimeCore (mirrorComplex hT hB)).Data.topologicalClosure = tsdQℝ ∧
    (∀ x ∈ tsdQℝ, ∀ T : ℝ, ∀ v : ∀ N, (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).X N,
      Tendsto (fun N => (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).incl N (v N)) atTop
        (𝓝 x) →
      TendstoUniformlyOn
        (fun N t => (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N (v N) t)
        (fun t => complexQℝ.waveGroup.S t x) atTop (Icc 0 T) ∧
      TendstoUniformlyOn (fun N t => infDist
        ((ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N (v N) t) (tsdQℝ : Set _))
        (fun _ => 0) atTop (Icc 0 T)) := by
  have V := mirrorFEMApprox_verdict hT hB
  refine ⟨V.toApprox, V.sol, mirrorFEMApprox_L_eq hT hB, V.closure, fun x hx T v hv => ?_⟩
  have hxc := V.closure.ge hx
  exact ⟨(V.converges hxc hv T).congr_right fun t ht =>
    DFunLike.congr_fun (ApproxFEEC.S_eq_waveGroup _ ht.1) x,
    V.residual_tendsto (V.isReducing_iff.1 V.isReducing).1 hx hxc hv T⟩

/-- The old `einsteinBianchi_mirrorFEM_ofComplexCrime_rate` (the crime rate class), verbatim. -/
theorem eb_old_mirrorFEM_ofComplexCrime_rate {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorL3Data)
    (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N (mirrorEllInit hT hB x N) t‖ ≤
      ((mirrorComplex hT hB).toFamily.rateConstA * (4 * mirrorEllK (C := C)) +
        (mirrorComplex hT hB).toFamily.boundConst *
          (2 * (mirrorComplex hT hB).toFamily.rateConstD * (4 * mirrorEllK (C := C))) * t) *
        (meshSize N * mirrorL3Norm x) := by
  have h := (mirrorComplex hT hB).error_le_of_rateClass (mirrorComplexRate hT hB t) hx N
    ⟨ht, le_rfl⟩
  have hp : (mirrorComplexRate hT hB t).p x N 0 = mirrorEllInit hT hB x N :=
    (galerkinRateClass_p (hfd := mirrorFEMApprox_finiteDimensional hT hB) _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ hx N ⟨le_rfl, by linarith⟩).trans
      (mirrorEllCmp_p_zero_eq_init hT hB (t + 1) x N)
  rw [hp, mirrorComplex_sol] at h
  refine h.trans_eq ?_
  change _ * (meshSize N ^ (1 : ℝ) * mirrorL3Norm x) = _
  rw [Real.rpow_one]
  rfl

/-- The old `einsteinBianchi_mirrorFEM_ofComplexCrime_rate_sobolev` (the crime rate class),
verbatim. -/
theorem eb_old_mirrorFEM_ofComplexCrime_rate_sobolev {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorSobData s) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N (mirrorEllInit hT hB x N) t‖ ≤
      ((mirrorComplex hT hB).toFamily.rateConstA * (6 * mirrorEllK (C := C)) +
        (mirrorComplex hT hB).toFamily.boundConst *
          (2 * (mirrorComplex hT hB).toFamily.rateConstD * (6 * mirrorEllK (C := C))) * t) *
        (meshSize N ^ s * √(sobState (2 + s) x)) := by
  have h := (mirrorComplex hT hB).error_le_of_rateClass
    (mirrorComplexRateSobolev hT hB t s hs0 hs1) hx N ⟨ht, le_rfl⟩
  have hp : (mirrorComplexRateSobolev hT hB t s hs0 hs1).p x N 0 = mirrorEllInit hT hB x N :=
    (galerkinRateClass_p (hfd := mirrorFEMApprox_finiteDimensional hT hB) _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ hx N ⟨le_rfl, by linarith⟩).trans
      (mirrorEllCmp_p_zero_eq_init hT hB (t + 1) x N)
  rw [hp, mirrorComplex_sol] at h
  exact h

/-- The old `MirrorFEMApproxVerdict`, verbatim (the orbit core and rate classes as above). -/
abbrev MirrorFEMApproxVerdict : Prop :=
  (∃ (ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3) (C : ℝ),
      ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C ∧
        ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) ∧
    (cosDatum.U₀ ∈ mirrorL3Data ∧ (∀ s, cosDatum.U₀ ∈ mirrorSobData s) ∧
      cosDatum.U₀ ∉ Feec.Models.Cube.MirrorBGG.complexQ.waveGroup.stationary) ∧
    -- the model verdict, as a corollary of the elliptic instance
    MirrorFEMVerdict ∧
    ∀ {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
      (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
      (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C),
      -- 1. the verdict
      (mirrorFEMApprox hT hB).Verdict (mirrorFEMCore hT hB) ∧
      -- 2. the closure of the core, the reducing constraint
      (mirrorFEMCore hT hB).Data.topologicalClosure = tsdQℝ ∧ complexQℝ.wave.IsReducing tsdQℝ ∧
      -- 3. convergence to the TSD solution, residual → 0
      (∀ x ∈ tsdQℝ, ∀ T : ℝ, (∀ t, complexQℝ.waveGroup.S t x ∈ tsdQℝ) ∧
        Tendsto (fun N => (mirrorFEMApprox hT hB).incl N ((mirrorFEMApprox hT hB).proj N x))
          atTop (𝓝 x) ∧
        ∀ v : ∀ N, (mirrorFEMApprox hT hB).X N,
          Tendsto (fun N => (mirrorFEMApprox hT hB).incl N (v N)) atTop (𝓝 x) →
          TendstoUniformlyOn (fun N t => (mirrorFEMApprox hT hB).sol N (v N) t)
            (fun t => complexQℝ.waveGroup.S t x) atTop (Icc 0 T) ∧
          TendstoUniformlyOn (fun N t => infDist ((mirrorFEMApprox hT hB).sol N (v N) t)
            (tsdQℝ : Set (PiLp 2 SpaceQ))) (fun _ => 0) atTop (Icc 0 T)) ∧
      -- 4. orbit rates
      (∀ {T : ℝ}, 0 < T → ∀ x ∈ mirrorL3Data, ∀ (N : ℕ) (v : (mirrorFEMApprox hT hB).X N),
        ∀ t ∈ Icc 0 T, ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤
          3 * (2 * mirrorRateK hT hB * (1 + T)) * (meshSize N * mirrorL3Norm x) +
            ‖(mirrorFEMApprox hT hB).proj N x - v‖) ∧
      (∀ {T s : ℝ}, 0 < T → 0 ≤ s → s ≤ 1 → ∀ x ∈ mirrorSobData s, ∀ (N : ℕ)
        (v : (mirrorFEMApprox hT hB).X N), ∀ t ∈ Icc 0 T,
        ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤
          3 * (2 * mirrorSobK hT hB * (1 + T)) * (meshSize N ^ s * √(sobState (2 + s) x)) +
            ‖(mirrorFEMApprox hT hB).proj N x - v‖) ∧
      -- 5. the discrete solutions are (6.5)
      (∀ (N : ℕ) {T : ℝ} (hT0 : 0 < T) (a b : mirrorHidden hT hB N),
        ∃ s s' : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T 0,
          DiscreteSolution.hiddenInit hT0.le s = a ∧ DiscreteSolution.hiddenInit hT0.le s' = b ∧
          ∀ t ∈ Icc 0 T, (mirrorFEMApprox hT hB).sol N (WithLp.toLp 2 (a, b)) t =
            mirrorReEmb (dState hT hB N s t) + mulI (mirrorReEmb (dState hT hB N s' t))) ∧
      -- 6. the elliptic core
      (mirrorFEMApprox hT hB).Verdict (mirrorEllCore hT hB) ∧
      (mirrorEllCore hT hB).Data.topologicalClosure = tsdQℝ ∧
      -- 7. the elliptic rates from the horizon-free initialization (6.4)
      (∀ {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData) (N : ℕ),
        (∀ T : ℝ, (mirrorEllCmp hT hB T).p x N 0 = mirrorEllInit hT hB x N) ∧
        mirrorEllInit hT hB x N = WithLp.toLp 2 (mEll hT hB N (tsdDatumOf hx) 0 0,
          mEll hT hB N (tsdDatumOf (neg_I_smul_mem hx)) 0 0)) ∧
      (∀ (N : ℕ) (D : TSDDatum) {T : ℝ}, 0 ≤ T →
        (mEll hT hB N D 0 0).toEState = EState.mkL (Feec.BGG.ellipticProjection
          (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
          (Feec.BGG.exists_sub_eq_of_surjective (mirrorWave_S0_surjective hT hB N))
          (Feec.BGG.ellipticRhs ((mirrorFEM hT hB N).ellipticDataH ((D.exactWave T).σ 0)
            ((D.exactWave T).φ 0) ((D.exactWave T).u 0) ((D.exactWave T).M 0)
            ((D.exactWave T).ρ 0) ((D.exactWave T).ℓ 0)) 0)).1.1) ∧
      (∀ {x : PiLp 2 SpaceQ}, x ∈ mirrorL3Data → ∀ (N : ℕ) {t : ℝ}, 0 ≤ t →
        ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N (mirrorEllInit hT hB x N) t‖ ≤
          (4 * mirrorEllK (C := C) + 8 * mirrorEllK (C := C) * t) *
            (meshSize N * mirrorL3Norm x)) ∧
      (∀ {s : ℝ}, 0 ≤ s → s ≤ 1 → ∀ {x : PiLp 2 SpaceQ}, x ∈ mirrorSobData s → ∀ (N : ℕ)
        {t : ℝ}, 0 ≤ t →
        ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N (mirrorEllInit hT hB x N) t‖ ≤
          (6 * mirrorEllK (C := C) + 12 * mirrorEllK (C := C) * t) *
            (meshSize N ^ s * √(sobState (2 + s) x)))

-- The orbit rate items of the old statement elaborate the arithmetic of their bounds with other
-- instance paths than the theorems they bundle, so the unifier unfolds the scheme; the deleted
-- `mirrorFEMApproxVerdict` carried the same override (`2000000`).
set_option maxHeartbeats 1000000 in
/-- The old `mirrorFEMApproxVerdict`. -/
theorem eb_old_mirrorFEMApproxVerdict : MirrorFEMApproxVerdict := by
  refine ⟨exists_mirror_estimates, ⟨cosDatum_mem_mirrorL3Data, cosDatum_mem_mirrorSobData,
    cosDatum_not_stationary⟩, mirrorFEMVerdict_of_approxFEEC, fun hT hB => ?_⟩
  have V := mirrorFEMApprox_verdict hT hB
  refine ⟨eb_old_mirrorFEM_approxFEEC hT hB, topologicalClosure_tsdQℝ_inf_domainSq, V.isReducing,
    fun _ hx T => eb_old_mirrorFEM_converges hT hB hx T,
    ?_, ?_, V.sol_eq_scheme, eb_old_mirrorFEM_approxFEEC_elliptic hT hB, mirrorEllCore_closure hT hB,
    fun hx N => ⟨fun T => mirrorEllCmp_p_zero_eq_init hT hB T _ N, V.init hx N⟩,
    V.init_toEState, V.rate_init, V.rate_sobolev_init⟩
  · intro T hT0 x hx N v t ht
    exact eb_old_mirrorFEM_rate hT hB hT0 hx N v ht
  · intro T s hT0 hs0 hs1 x hx N v t ht
    exact eb_old_mirrorFEM_rate_sobolev hT hB hT0 hs0 hs1 hx N v ht

/-- The old `einsteinBianchi_mirrorFEM_ofCochainDefect` (the split route), with
`mirrorSplitComplex` unfolded to `mirrorComplex`. -/
theorem eb_old_mirrorFEM_ofCochainDefect :
    (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).Verdict
      (ApproxFEEC.ofComplexCrimeCore (mirrorComplex hT hB)) ∧
    (∀ N v t, (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N v t =
      (mirrorFEMApprox hT hB).sol N v t) ∧
    (ApproxFEEC.ofComplexCrimeCore (mirrorComplex hT hB)).Data.topologicalClosure = tsdQℝ ∧
    (∀ x ∈ tsdQℝ, ∀ T : ℝ, ∀ v : ∀ N, (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).X N,
      Tendsto (fun N => (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).incl N (v N)) atTop
        (𝓝 x) →
      TendstoUniformlyOn
        (fun N t => (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N (v N) t)
        (fun t => complexQℝ.waveGroup.S t x) atTop (Icc 0 T) ∧
      TendstoUniformlyOn (fun N t => infDist
        ((ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N (v N) t) (tsdQℝ : Set _))
        (fun _ => 0) atTop (Icc 0 T)) ∧
    (∀ N (y : complexQℝ.wave.domain), (y : PiLp 2 SpaceQ) ∈ tsdQℝ →
      (mirrorComplex hT hB).toFamily.cochainDefect N y = 0) :=
  have V := eb_old_mirrorFEM_ofComplexCrime hT hB
  ⟨V.1, V.2.1, V.2.2.2.1, V.2.2.2.2, mirrorComplex_cochainDefect_eq_zero hT hB⟩

end Mirror

/-! ### The thesis' boundary conditions -/

section Cube

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry
  Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM Feec.EinsteinBianchi.MatrixModel
  Feec.EinsteinBianchi.BoundedFailure Feec.EinsteinBianchi.BoundedConvergence

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- The old `standardCube_hconv` (model convergence read on `standardCubeApprox`), from the verdict:
the discrete solutions from `π ξ₀` converge. -/
theorem eb_old_standardCube_hconv : ∀ x ∈ matrixComplex.wave.domainSq, ∀ T : ℝ, 0 < T →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∃ v : (standardCubeApprox hT hB).X N,
      ∀ t ∈ Icc 0 T,
        ‖matrixComplex.waveGroup.S t x - (standardCubeApprox hT hB).sol N v t‖ ≤ ε := by
  intro x _ T _ ε hε
  have V := standardCubeApprox_verdict hT hB
  have hxc : x ∈ (ApproxFEEC.ofComplexCrimeCore (standardCubeComplex hT hB)).Data.topologicalClosure :=
    (standardCubeEllCore_closure hT hB).ge Submodule.mem_top
  have hc := V.converges hxc (V.tendsto_incl_proj hxc) T
  rw [Metric.tendstoUniformlyOn_iff] at hc
  filter_upwards [hc ε hε] with N hN
  refine ⟨(standardCubeApprox hT hB).proj N x, fun t ht => ?_⟩
  have h := hN t ht
  rw [dist_eq_norm, ApproxFEEC.S_eq_waveGroup _ ht.1] at h
  rw [← V.sol]
  exact h.le

/-- The old orbit core `standardCubeCore`, with its definition unfolded. -/
abbrev standardCubeCore : (standardCubeApprox hT hB).Core :=
  ApproxFEEC.orbitCore (standardCubeApprox_isOrthogonal hT hB) matrixComplex.wave.domainSq
    (eb_old_standardCube_hconv hT hB)

/-- The old `dense_standardCubeCore`. -/
theorem eb_old_dense_standardCubeCore : Dense ((standardCubeCore hT hB).Data : Set (PiLp 2
    (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
      (W2B ℝ (cubeDomain 3))))) :=
  matrixComplex.isSkewAdjoint_wave.dense_domainSq

/-- The old `einsteinBianchi_standardCube_approxFEEC` (the orbit core). -/
theorem eb_old_standardCube_approxFEEC :
    (standardCubeApprox hT hB).Verdict (standardCubeCore hT hB) :=
  approxFEEC _ _

/-- The old `einsteinBianchi_standardCube_approxFEEC_elliptic` (the direct verdict on the
elliptic core). -/
theorem eb_old_standardCube_approxFEEC_elliptic :
    (standardCubeApprox hT hB).Verdict (standardCubeEllCore hT hB) :=
  approxFEEC _ _

/-- The old `einsteinBianchi_standardCube_converges`, from `StandardCubeApprox.Verdict`. -/
theorem eb_old_standardCube_converges (x : PiLp 2 (ShortHilbertComplex.W3
    (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))) (T : ℝ) :
    Tendsto (fun N => (standardCubeApprox hT hB).incl N ((standardCubeApprox hT hB).proj N x))
      atTop (𝓝 x) ∧
    ∀ v : ∀ N, (standardCubeApprox hT hB).X N,
      Tendsto (fun N => (standardCubeApprox hT hB).incl N (v N)) atTop (𝓝 x) →
      TendstoUniformlyOn (fun N t => (standardCubeApprox hT hB).sol N (v N) t)
        (fun t => matrixComplex.waveGroup.S t x) atTop (Icc 0 T) := by
  have V := standardCubeApprox_verdict hT hB
  have hxc : x ∈ (ApproxFEEC.ofComplexCrimeCore (standardCubeComplex hT hB)).Data.topologicalClosure :=
    (standardCubeEllCore_closure hT hB).ge Submodule.mem_top
  exact ⟨V.tendsto_incl_proj hxc, fun v hv =>
    ((V.converges hxc hv T).congr (Eventually.of_forall fun N t _ => V.sol N (v N) t)).congr_right
      fun t ht => DFunLike.congr_fun (ApproxFEEC.S_eq_waveGroup _ ht.1) x⟩

/-- The old `einsteinBianchi_standardCube_ofComplexCrime`, from `StandardCubeApprox.Verdict`. -/
theorem eb_old_standardCube_ofComplexCrime :
    (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).Verdict
      (ApproxFEEC.ofComplexCrimeCore (standardCubeComplex hT hB)) ∧
    (∀ N v t, (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).sol N v t =
      (standardCubeApprox hT hB).sol N v t) ∧
    (∀ N, (standardCubeApprox hT hB).L N = diffWave (cubeD hT hB N)) ∧
    (ApproxFEEC.ofComplexCrimeCore (standardCubeComplex hT hB)).Data.topologicalClosure = ⊤ ∧
    (∀ x T, ∀ v : ∀ N, (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).X N,
      Tendsto (fun N => (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).incl N (v N))
        atTop (𝓝 x) →
      TendstoUniformlyOn
        (fun N t => (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).sol N (v N) t)
        (fun t => matrixComplex.waveGroup.S t x) atTop (Icc 0 T)) ∧
    betaDatum ∈ thesisTSD ∧
    (∀ T : ℝ, 0 < T → ∃ t ∈ Icc 0 T, matrixComplex.waveGroup.S t betaDatum ∉ thesisTSD ∧
      0 < infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _) ∧
      ∀ v : ∀ N, (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).X N,
        Tendsto (fun N => (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).incl N (v N))
          atTop (𝓝 betaDatum) →
        Tendsto (fun N => infDist
          ((ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).sol N (v N) t)
            (thesisTSD : Set _))
          atTop (𝓝 (infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _)))) := by
  have V := standardCubeApprox_verdict hT hB
  have hcl : (ApproxFEEC.ofComplexCrimeCore (standardCubeComplex hT hB)).Data.topologicalClosure =
      ⊤ := standardCubeEllCore_closure hT hB
  refine ⟨V.toApprox, V.sol, standardCubeApprox_L_eq hT hB, hcl, fun x T v hv => ?_,
    betaDatum_mem_thesisTSD, fun T hT0 => ?_⟩
  · exact (V.converges (hcl.ge Submodule.mem_top) hv T).congr_right fun t ht =>
      DFunLike.congr_fun (ApproxFEEC.S_eq_waveGroup _ ht.1) x
  · obtain ⟨t, ht, hout, hpos, -⟩ := V.residual_not_mem hT0
    refine ⟨t, ht, hout, hpos, fun v hv => ?_⟩
    have h := V.tendsto_infDist (thesisTSD : Set _) (hcl.ge Submodule.mem_top) hv ht.1
    rwa [ApproxFEEC.S_eq_waveGroup _ ht.1] at h

/-- The old `StandardCubeApproxVerdict`, verbatim (the orbit core as above). -/
abbrev StandardCubeApproxVerdict : Prop :=
  (betaDatum ∈ thesisTSD ∧ ¬ matrixComplex.wave.IsReducing thesisTSD) ∧
    -- the model verdict (componentwise discrete failure of TSD, explicit projected data)
    StandardCubeVerdict ∧
    (∃ (p : ℕ → SmoothingParam (Fin 3 → ℝ)) (C : ℝ),
      PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C ∧
        PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) ∧
    ∀ {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
      (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
      (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C),
      -- 1. the verdict, dense core
      (standardCubeApprox hT hB).Verdict (standardCubeCore hT hB) ∧
      Dense ((standardCubeCore hT hB).Data : Set (PiLp 2 (ShortHilbertComplex.W3
        (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) ∧
      -- 2. the discrete solutions are (6.5)
      (∀ (N : ℕ) {T : ℝ} (hT0 : 0 < T) (v : cubeHidden hT hB N),
        ∃ s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T 0,
          DiscreteSolution.hiddenInit hT0.le s = v ∧
          ∀ t ∈ Icc 0 T, (standardCubeApprox hT hB).sol N v t =
            totalE (vecInv (cState hT hB N s t))) ∧
      -- 3. convergence for every datum
      (∀ (x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
          (W2B ℝ (cubeDomain 3)))) (T : ℝ),
        Tendsto (fun N => (standardCubeApprox hT hB).incl N ((standardCubeApprox hT hB).proj N x))
          atTop (𝓝 x) ∧
        ∀ v : ∀ N, (standardCubeApprox hT hB).X N,
          Tendsto (fun N => (standardCubeApprox hT hB).incl N (v N)) atTop (𝓝 x) →
          TendstoUniformlyOn (fun N t => (standardCubeApprox hT hB).sol N (v N) t)
            (fun t => matrixComplex.waveGroup.S t x) atTop (Icc 0 T)) ∧
      -- 4. the residual from `(0, 0, (0, β))` tends to a positive limit
      (∀ {T : ℝ}, 0 < T →
        ∃ t ∈ Icc 0 T, matrixComplex.waveGroup.S t betaDatum ∉ thesisTSD ∧
          0 < infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _) ∧
          ∀ v : ∀ N, (standardCubeApprox hT hB).X N,
            Tendsto (fun N => (standardCubeApprox hT hB).incl N (v N)) atTop (𝓝 betaDatum) →
            Tendsto (fun N => infDist ((standardCubeApprox hT hB).sol N (v N) t)
              (thesisTSD : Set _)) atTop
              (𝓝 (infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _))) ∧
            ∀ᶠ N in atTop, infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _) / 2 <
              infDist ((standardCubeApprox hT hB).sol N (v N) t) (thesisTSD : Set _)) ∧
      -- 5. the elliptic core (dense), and the converse part from `¬ IsReducing` alone
      (standardCubeApprox hT hB).Verdict (standardCubeEllCore hT hB) ∧
      Dense ((standardCubeEllCore hT hB).Data : Set (PiLp 2 (ShortHilbertComplex.W3
        (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) ∧
      (∀ {T : ℝ}, 0 < T →
        ∃ Q : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
            (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))),
          (Q = thesisTSD ∨ Q = thesisTSDᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
            matrixComplex.waveGroup.S t x ∉ Q ∧
            0 < infDist (matrixComplex.waveGroup.S t x) (Q : Set _) ∧
            ∀ v : ∀ N, (standardCubeApprox hT hB).X N,
              Tendsto (fun N => (standardCubeApprox hT hB).incl N (v N)) atTop (𝓝 x) →
              Tendsto (fun N => infDist ((standardCubeApprox hT hB).sol N (v N) t) (Q : Set _))
                atTop (𝓝 (infDist (matrixComplex.waveGroup.S t x) (Q : Set _)))) ∧
      -- 6. the density hypothesis of the `D(L) ∩ K` clauses fails
      ¬ ∀ k ∈ (standardCubeApprox hT hB).K, k ∈ closure ((matrixComplex.wave.domain :
        Set (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
          (W2B ℝ (cubeDomain 3))))) ∩ (standardCubeApprox hT hB).K)

/-- The old `standardCubeApproxVerdict`. -/
theorem eb_old_standardCubeApproxVerdict : StandardCubeApproxVerdict := by
  refine ⟨⟨betaDatum_mem_thesisTSD, not_isReducing_thesisTSD⟩, standardCubeVerdict, ?_,
    fun hT hB =>
    ⟨eb_old_standardCube_approxFEEC hT hB, eb_old_dense_standardCubeCore hT hB,
      fun N _ hT0 v => standardCube_sol_eq_scheme hT hB N hT0 v,
      fun x T => eb_old_standardCube_converges hT hB x T,
      fun hT0 => standardCube_residual_not_mem hT hB hT0,
      eb_old_standardCube_approxFEEC_elliptic hT hB, dense_standardCubeEllCore hT hB,
      fun hT0 => standardCube_residual_not_isReducing hT hB hT0,
      not_forall_mem_closure_domain_inf_thesisTSD⟩⟩
  obtain ⟨p, C, hT, hB, -⟩ := Feec.Models.Cube.FEM.tableRows_H1
  exact ⟨p, C, hT, hB⟩

end Cube

/-- The old `einsteinBianchi_summary`, verbatim; its `ℝ³` row is the old conjunction
`EuclideanEBVerdict` (`band_old_einsteinBianchi_euclidean_band`). -/
theorem eb_old_summary :
    -- the constrained FEEC verdicts, with the approximating `ℝ³` row
    ((TorusVerdict ∧ TorusSobolevVerdict ∧ TorusNonvacuous) ∧
      type_of% band_old_einsteinBianchi_euclidean_band ∧
      (MirrorVerdict ∧ MirrorSobolevVerdict ∧ MirrorNonvacuous) ∧ MirrorFEMVerdict ∧
      StandardCubeVerdict) ∧
    -- the scheme (6.5) as an approximating FEEC discretization
    MirrorFEMApproxVerdict ∧ StandardCubeApproxVerdict :=
  have h := einsteinBianchi_constrainedFEEC_summary
  ⟨⟨⟨h.1.1.toTorusVerdict, h.1⟩, band_old_einsteinBianchi_euclidean_band,
    ⟨h.2.1.1.toMirrorVerdict, h.2.1⟩, mirrorFEMVerdict_of_approxFEEC, h.2.2.2⟩,
    eb_old_mirrorFEMApproxVerdict, eb_old_standardCubeApproxVerdict⟩

end EinsteinBianchiOld

section CrownCrime

/-! ### The crown for approximating families, and the conforming verdict before it -/

open scoped InnerProductSpace

section Crime

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] {H : HilbertComplex 𝕜 c W}
  {κ : Type*} (G : ApproxComplexCrime H κ)

example : type_of% (approxFEEC_ofComplexCrime G).1 := G.feec.wave

example (Θ : (ApproxFEEC.ofComplexCrime G).TimeScheme) :
    type_of% (dissipFEEC_fullyDiscrete (ApproxFEEC.ofComplexCrimeCore G) Θ) :=
  G.feec.full Θ

example (hZ : (ApproxFEEC.ofComplexCrimeCore G).Data.topologicalClosure = ⊤)
    (P : (ApproxFEEC.ofComplexCrime G).Perturbation) :
    type_of% (perturbFEEC _ hZ P) :=
  G.feec.perturbed hZ P

end Crime

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α] [CharZero α]
  {V : α → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]
  {H : HilbertComplex 𝕜 (ComplexShape.up α) V} {κ : Type*}

/-- **The conclusions of the FEEC theorem before the field `crime`** (`ConformingFamily.Verdict`
of main `28e5d3e`), stated verbatim. -/
structure OldVerdict (F : ConformingFamily H κ) : Prop where
  /-- the static FEEC theorem in every degree with finite-dimensional harmonic forms
  ([AFW2010], Thms 3.4–3.9) -/
  static (hcr : ∀ i, H.ClosedRangeAt i) (j : α) [FiniteDimensional 𝕜 (H.harmonic j)] :
    F.StaticVerdict j
  /-- the approximating FEEC theorem for the wave equation on every window with every closed
  constraint, hence the skew-adjoint and dissipative ones -/
  wave (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowFEEC a m K hK).toApprox.Verdict (F.windowFEEC a m K hK).toCore
  /-- the constrained FEEC theorem on every window with every closed constraint
  ([QuennevilleBelair2015], Thms 4.6, 4.7, 4.14, Prop. 4.17) -/
  constrained (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowFEEC a m K hK).Verdict
  /-- the heat FEEC theorem on every window with closed range and finite-dimensional harmonic
  forms, with every closed constraint -/
  heat (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i)
    [∀ i, FiniteDimensional 𝕜 ((H.window a m).harmonic i)] :
    (F.windowFEEC a m K hK).toHeat.Verdict ((F.windowFEEC a m K hK).heatCore hcr)
  /-- the fully discrete wave and heat FEEC theorems on every window with every closed
  constraint, for every time scheme, and leapfrog under the CFL condition -/
  full (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowFEEC a m K hK).FullVerdict
  /-- the perturbed FEEC theorems on every window with every closed constraint and every bounded
  dissipative `B`: the damped wave and perturbed heat equations ([Pazy1983], §3.1, §3.3, §3.4) -/
  perturbed (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (B : (PiLp 2 fun i : Fin m => V (a + i)) →L[𝕜] PiLp 2 fun i : Fin m => V (a + i))
    (hB : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0) : (F.windowFEEC a m K hK).PerturbedVerdict B hB

/-- The old verdict is the new one without its last field. -/
theorem crown_old_verdict (F : ConformingFamily H κ) : OldVerdict F :=
  ⟨F.feec.static, F.feec.wave, F.feec.constrained, F.feec.heat, F.feec.full, F.feec.perturbed⟩

variable (F : ConformingFamily H κ) (a : α) (m : ℕ)
  (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
  (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))

/-- The field `crime` is the crime crown of the conforming window. -/
example : type_of% (F.windowCrime a m K hK).feec := F.feec.crime a m K hK

/-- The conforming window is the approximating family with zero inner-product and cochain
defects, whose discrete solutions are those of the subcomplex scheme. -/
example (h : κ) (y : (H.window a m).wave.domain)
    (v : PiLp 2 ((F.windowFEEC a m K hK).toFamily.V h)) (t : ℝ) :
    (F.windowCrime a m K hK).toFamily.J h = 1 ∧
      (F.windowCrime a m K hK).toFamily.cochainDefect h y = 0 ∧
      (ApproxFEEC.ofComplexCrime (F.windowCrime a m K hK)).sol h v t =
        (F.windowFEEC a m K hK).toApprox.sol h ((F.windowFEEC a m K hK).toXh h v) t :=
  ⟨(F.windowFEEC a m K hK).toCrime_J h, (F.windowFEEC a m K hK).toCrime_cochainDefect h y,
    (F.windowFEEC a m K hK).toCrime_sol h v t⟩

end CrownCrime

end FeecCheck.Crown
