module

public import Solution.Bridge

/-!
# The BGG construction (solution)

`FEEC.bggCohomology` and `FEEC.bggFinrank` of `Challenge.lean`, proved from
`Feec.BGG.Data.quasiIso_Γ` and `Feec.BGG.Data.quasiIso_derived` through the bridge
`Solution.Bridge` (`FEEC.BGG.verdict`, `FEEC.BGG.finiteDimensional_and_finrank_le`).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], Theorem 6 and §5.2

Bibliography: [references.bib](../../docs/references.bib)
-/

open CategoryTheory

@[expose] public noncomputable section

universe u v

namespace FEEC

/-- **The BGG construction** ([ArnoldHu2021], §5.2). For a stacked diagram `S : Ṽ ⟶ V⟦1⟧` of
cochain complexes of modules over any ring, with `Sⁱ` injective for `i < J` and surjective for
`i ≥ J`, the BGG complex at `J` has the cohomology of the twisted complex
(`BGG.Verdict`). -/
theorem bggCohomology {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i → Function.Surjective (S.f i)) : BGG.Verdict S J :=
  BGG.verdict hinj hsurj

/-- **The dimension bound of the BGG complex** ([ArnoldHu2021], Theorem 6). Over a field, under
the hypotheses of `FEEC.bggCohomology`, if both rows have finite-dimensional cohomology in
degree `i`, so does the BGG complex, and `dim Hⁱ(Γ / Δ) ≤ dim Hⁱ(V) + dim Hⁱ(Ṽ)`. -/
theorem bggFinrank {K : Type u} [Field K] {V Vt : CochainComplex (ModuleCat.{v} K) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i → Function.Surjective (S.f i)) (i : ℤ)
    [FiniteDimensional K (V.homology i)] [FiniteDimensional K (Vt.homology i)] :
    FiniteDimensional K ((BGG.bgg S J).homology i) ∧
      Module.finrank K ((BGG.bgg S J).homology i) ≤
        Module.finrank K (V.homology i) + Module.finrank K (Vt.homology i) :=
  BGG.finiteDimensional_and_finrank_le hinj hsurj i

end FEEC
