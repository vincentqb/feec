module

public import Solution.Bridge

/-!
# The FEEC theorem (solution)

`FEEC.feec` of `Challenge.lean`, proved from `Feec.HilbertComplex.ConformingFamily.feec` through
the bridge `Solution.Bridge`: the static verdict (`ConformingFamily.staticVerdict`), the wave
verdict (`ConformingFamily.waveVerdict`) and the heat verdict (`ConformingFamily.heatVerdict`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3–§3.4
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015], §4.4–§4.6
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7

Bibliography: [references.bib](../docs/references.bib)
-/

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] [∀ i, NormedSpace ℝ (W i)]
  [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The FEEC theorem.** Every conforming family of every Hilbert complex satisfies the static,
wave and heat FEEC theorems (`ConformingFamily.Verdict`). [AFW2010], Thms 3.4–3.9;
[QuennevilleBelair2015], Thms 4.6, 4.7, 4.14, Prop. 4.17; [Thomee2006], Ch. 7 -/
theorem feec {κ : Type*} {H : HilbertComplex 𝕜 W} (F : H.ConformingFamily κ) : F.Verdict where
  static hcr j _ := F.staticVerdict hcr j
  wave a m := F.waveVerdict a m
  heat a m hcr _ := F.heatVerdict a m hcr

end FEEC
