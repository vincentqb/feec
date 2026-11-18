module

public import Solution.Rates

/-!
# The verdicts of the challenge from their componentwise forms

The static verdict of `Solution.Bridge` and the rates of `Solution.Rates` are proved for the
componentwise forms of `Solution.Legacy`; with the one-equation mixed problem
(`HilbertComplex.isMixedSolution_iff`) they are the verdict and the rates of the challenge
(`SubcomplexFamily.StaticVerdict₀.toStaticVerdict`, `SubcomplexFamily.Rated₀.hasRate`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

variable {H : HilbertComplex 𝕜 W} {κ : Type*}

/-- **The static verdict** from its componentwise form. -/
theorem SubcomplexFamily.StaticVerdict₀.toStaticVerdict {F : H.SubcomplexFamily κ} {j : ℤ}
    {C : ℝ} (V : F.StaticVerdict₀ j C) : F.StaticVerdict j C where
  harmonicDist h q := V.harmonicDist h q q.2
  discreteHarmonicDist h q hq := V.discreteHarmonicDist h q hq
  cohomologyMap_comp_incl h := V.cohomologyMap_comp_incl h
  cohomology_of_lt h hgap := V.cohomology_of_lt h fun q hq hne =>
    hgap ⟨q, hq⟩ fun h0 => hne (congrArg Subtype.val h0)
  cohomology ha _ := ⟨V.harmonicGap ha, V.cohomology ha⟩
  poincare h := V.poincare h
  existsUnique f := ⟨(existsUnique_congr fun _ => isMixedSolution_iff).2 (V.existsUnique f),
    fun h => (existsUnique_congr fun _ => isMixedSolution_iff).2 (V.existsUnique_discrete h f)⟩
  infSup h x hx := by
    obtain ⟨τ, v, q, hτ, hv, hq, h1, h2⟩ := V.infSup h x.1 x.2.1 x.2.2 hx.1 hx.2.1 hx.2.2
    exact ⟨(τ, v, q), ⟨hτ, hv, hq⟩, h1, h2⟩
  stable h f x hx := V.stable h (isMixedSolution_iff.1 hx)
  quasiOptimal hs h xh hsh := V.quasiOptimal (isMixedSolution_iff.1 hs) h (isMixedSolution_iff.1 hsh)
  converges ha ha' f x hs xh hsh := V.converges ha ha' (isMixedSolution_iff.1 hs)
    (σh := fun h => (xh h).1) (uh := fun h => (xh h).2.1) (ph := fun h => (xh h).2.2)
    fun h => isMixedSolution_iff.1 (hsh h)

/-- **The static rate** from its componentwise form. -/
theorem SubcomplexFamily.Rated₀.hasRate {F : H.SubcomplexFamily κ} {ρ : Type*} {J : F.Jackson ρ}
    (R : F.Rated₀ J) (j : ℤ) (hπ : F.IsGraphBounded (j - 1)) (hπ' : F.IsGraphBounded j)
    (hj : IsClosed (H.boundaries j : Set (W j)))
    (hj' : IsClosed (H.boundaries (j + 1) : Set (W (j + 1)))) (s : ρ) :
    F.HasRate j (J.Reg s) fun h => J.meshSize h ^ J.ord s := by
  obtain ⟨C, hC⟩ := R.static j hπ hπ' hj hj' s
  exact ⟨C, fun hs L hL h1 h2 h3 h4 h xh hsh =>
    hC (isMixedSolution_iff.1 hs) hL h1 h2 h3 h4 h (isMixedSolution_iff.1 hsh)⟩

end HilbertComplex

end FEEC
