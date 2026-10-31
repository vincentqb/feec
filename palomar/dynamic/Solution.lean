module

public import Solution.Bridge

/-!
# The FEEC theorem for the Hodge wave and heat equations (solution)

`FEEC.dynamicFEEC` of `Challenge.lean`, proved from `Feec.HilbertComplex.approxFEEC`,
`Feec.HilbertComplex.ConstrainedFEEC.heatFEEC` and `Feec.HilbertComplex.ConstrainedFEEC.rate_le`
through the bridge `Solution.Bridge`: the wave verdict (`SubcomplexFamily.waveVerdict`) and the heat verdict (`SubcomplexFamily.heatVerdict`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015], §4.4–§4.6, §4.10
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Filter Topology

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] [∀ i, NormedSpace ℝ (W i)]
  [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The FEEC theorem for the Hodge wave and heat equations** ([QuennevilleBelair2015], Thms 4.6,
4.7, 4.14, Props 4.13, 4.17; [Thomee2006], Ch. 7; [GilletteHolstZhu2017]). Let `F` be a family of
subcomplexes which approximates in the graph norm in the degrees `a, …, a + m - 1`. On the window
`[a, a + m)`, `F` satisfies the wave and heat verdicts (`SubcomplexFamily.DynamicVerdict`). -/
theorem dynamicFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} (F : H.SubcomplexFamily κ) (a : ℤ)
    (m : ℕ) (happrox : ∀ i : Fin m, F.Approximates (a + (i : ℕ))) : F.DynamicVerdict a m where
  wave := F.waveVerdict a m happrox
  heat hπ hπ' hcr := F.heatVerdict a m happrox hπ hπ' hcr

end FEEC
