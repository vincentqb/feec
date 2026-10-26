import Feec.HilbertComplex.Approximation.StaticFEEC

/-!
# Regression tests: nothing is lost on the way to the crown

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

This file is part of the `FeecCheck` library, not of `Feec`: it is compiled by
`lake build FeecCheck` (and so by `lake exe feec-gate`) and fails that build if a conclusion is
dropped.
-/

open Filter Topology

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

end FeecCheck.Crown
