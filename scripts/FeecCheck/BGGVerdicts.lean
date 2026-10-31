module

public import Feec.Domain.BGGRealization
public import Feec.Instances.CrownNonVacuity

/-!
# Regression test: the analytic BGG verdict

`Feec.BGG.HilbertData.DerivedVerdict` gained the fields `quotient_surjective`, `quotient_d`
(the Hilbert quotient norm of `Γ / Δ`), `quasiIso_sum` and `represents` (Theorem 7 and
Corollary 1 of [ArnoldHu2021]) after its first three. `derivedVerdict_old` states the earlier
three-field verdict (closed range, finite-dimensional cohomology, the dimension bound) verbatim
and derives it from the new structure. `HilbertData.bggVerdict` and
`Domain.ConstCoeffBGG.maximalData_bggVerdict` now conclude `HilbertData.BGGVerdict`, which extends
`DerivedVerdict` by the explicit map (30); `bggVerdict_old` and `maximalData_bggVerdict_old` state
their earlier conclusions verbatim and derive them from the new ones. `BGGVerdict` then gained
the fields `injective_domainData_S` and `quasiIso_orthSumMap` (the orthogonal form of (30) with the
Moore–Penrose inverses);
`bggVerdict_explicit_old` states its earlier fields verbatim and derives them from the new
structure.
`Instances.CrownNonVacuity` gained a last field `bgg`, the explicit map (30) on the smooth
Hessian, elasticity and div-div complexes; `crownNonVacuity_bgg` checks, by `type_of%`, that it is
the statement of `Domain.smoothBGGVerdict`.

This file is part of the `FeecCheck` library, not of `Feec`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], Theorems 6 and 7, Corollary 1

Bibliography: [references.bib](../../docs/references.bib)
-/

public section

universe v

namespace FeecCheck.BGGVerdicts

open Feec Feec.BGG

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W Wt : ι → Type v}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (Wt i)] [∀ i, InnerProductSpace 𝕜 (Wt i)]
  [∀ i, CompleteSpace (Wt i)] {D : HilbertData 𝕜 c W Wt} {E F : ι → Prop} {i : ι}

/-- The earlier `HilbertData.DerivedVerdict`, from the new one. -/
theorem derivedVerdict_old (v : D.DerivedVerdict E F i) :
    (D.domainData.derivedComplex E F).ClosedRangeAt i ∧
      FiniteDimensional 𝕜 ((D.domainData.derivedComplex E F).cohomology i) ∧
      Module.finrank 𝕜 ((D.domainData.derivedComplex E F).cohomology i) ≤
        Module.finrank 𝕜 (D.H.cohomology i) + Module.finrank 𝕜 (D.Ht.cohomology i) :=
  ⟨v.closedRangeAt, v.finiteDimensional, v.finrank_le⟩

/-- The earlier `HilbertData.bggVerdict`, from the new one. -/
theorem bggVerdict_old {W Wt : ℤ → Type v} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] [∀ i, NormedAddCommGroup (Wt i)]
    [∀ i, InnerProductSpace 𝕜 (Wt i)] [∀ i, CompleteSpace (Wt i)]
    (D : HilbertData 𝕜 (ComplexShape.up ℤ) W Wt) {J : ℤ}
    (hS : ∀ i ≤ J, ∃ K, AntilipschitzWith K (D.S i (i + 1)))
    (htop : D.RegularDecomposition J) (i : ℤ) [FiniteDimensional 𝕜 (D.H.cohomology i)]
    [FiniteDimensional 𝕜 (D.Ht.cohomology i)] : D.DerivedVerdict (J < ·) (· < J) i :=
  (D.bggVerdict hS htop i).toDerivedVerdict

/-- The earlier `HilbertData.BGGVerdict` (before the fields `injective_domainData_S` and
`quasiIso_orthSumMap`, the orthogonal form of (30) with the Moore–Penrose inverses), from the new
one. -/
theorem bggVerdict_explicit_old {W Wt : ℤ → Type v} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] [∀ i, NormedAddCommGroup (Wt i)]
    [∀ i, InnerProductSpace 𝕜 (Wt i)] [∀ i, CompleteSpace (Wt i)]
    {D : HilbertData 𝕜 (ComplexShape.up ℤ) W Wt} {J i : ℤ} (v : D.BGGVerdict J i) :
    D.DerivedVerdict (J < ·) (· < J) i ∧
      (∀ {t : ∀ i j, D.H.domainSpace j →ₗ[𝕜] D.Ht.domainSpace i}
        (ht : D.domainData.InjSurjWith J t) {K : ∀ i, D.Ht.domainSpace i →ₗ[𝕜] D.H.domainSpace i}
        (hK : D.domainData.IsNullHomotopy K), QuasiIso (D.domainData.bggSumMap t hK ht)) ∧
      ∀ {t : ∀ i j, D.H.domainSpace j →ₗ[𝕜] D.Ht.domainSpace i}
        (ht : D.domainData.InjSurjWith J t) {K : ∀ i, D.Ht.domainSpace i →ₗ[𝕜] D.H.domainSpace i}
        (hK : D.domainData.IsNullHomotopy K)
        {H : Submodule 𝕜 (D.H.domainSpace i)} {Ht : Submodule 𝕜 (D.Ht.domainSpace i)},
        D.domainData.rowTop.Represents i H → D.domainData.rowBot.Represents i Ht →
        (D.domainData.bgg J).Represents i
          ((H.prod Ht).map ((D.domainData.bggSumMap t hK ht).f i).hom) :=
  ⟨v.toDerivedVerdict, v.quasiIso_bggSumMap, v.bgg_represents⟩

open MeasureTheory in
/-- The earlier `Domain.ConstCoeffBGG.maximalData_bggVerdict`, from the new one. -/
theorem maximalData_bggVerdict_old {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] {Ω : Set E} (B : Domain.ConstCoeffBGG E 𝕜)
    (M : ∀ k, Matrix (B.top.ι (k + 1)) (B.bot.ι k) 𝕜)
    (hM : ∀ k f, (B.S k).apply f = (Domain.ConstCoeffOp.ofMatrix (M k)).apply f)
    [∀ k, DecidableEq (B.bot.ι k)] (hΩ : IsOpen Ω) {J : ℤ}
    (hN : ∀ k ≤ J, ∃ N : Matrix (B.bot.ι k) (B.top.ι (k + 1)) 𝕜, N * M k = 1)
    (htop : (B.maximalData M hM hΩ).RegularDecomposition J)
    (i : ℤ) [FiniteDimensional 𝕜 ((B.top.maximalComplex hΩ).cohomology i)]
    [FiniteDimensional 𝕜 ((B.bot.maximalComplex hΩ).cohomology i)] :
    (B.maximalData M hM hΩ).DerivedVerdict (J < ·) (· < J) i :=
  (B.maximalData_bggVerdict M hM hΩ hN htop i).toDerivedVerdict

universe u in
/-- The last field of `Instances.CrownNonVacuity` is the statement of `Domain.smoothBGGVerdict`. -/
theorem crownNonVacuity_bgg (h : Instances.CrownNonVacuity.{u}) :
    type_of% @Domain.smoothBGGVerdict.{u} :=
  h.bgg

end FeecCheck.BGGVerdicts
