module

public import Solution.Bridge

/-!
# The FEEC theorem for the Hodge wave and heat equations (solution)

`FEEC.dynamicFEEC` of `Challenge.lean`, proved from `Feec.HilbertComplex.ConformingFamily.feec`
and `Feec.HilbertComplex.ConstrainedFEEC.rate_le` through the bridge `Solution.Bridge`: the wave
verdict (`ConformingFamily.waveVerdict`) and the heat verdict (`ConformingFamily.heatVerdict`).

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
4.7, 4.14, Props 4.13, 4.17; [Thomee2006], Ch. 7; [GilletteHolstZhu2017]). Let `F` be a conforming
family whose cochain projections are bounded uniformly in `W`, `‖πₕ x‖ ≤ C ‖x‖`, and which
approximates every `w ∈ Wⁱ`. On every window, `F` satisfies the wave and heat verdicts
(`ConformingFamily.DynamicVerdict`). -/
theorem dynamicFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} (F : H.ConformingFamily κ)
    (hπ : ∃ C : ℝ, ∀ (h : κ) (i : ℤ) (x : W i), ‖(F.π h).π i x‖ ≤ C * ‖x‖)
    (happrox : ∀ (i : ℤ) (w : W i),
      Tendsto (fun h => Metric.infDist w ((F.V h).V i : Set (W i))) F.l (𝓝 0))
    (a : ℤ) (m : ℕ) : F.DynamicVerdict a m where
  wave := F.waveVerdict hπ happrox a m
  heat hcr _ := F.heatVerdict hπ happrox a m hcr

end FEEC
