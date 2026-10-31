module

public import Feec.HilbertComplex.BGG.DomainData

/-!
# Regression test: the analytic BGG verdict

`Feec.BGG.HilbertData.DerivedVerdict` gained the fields `quotient_surjective`, `quotient_d`
(the Hilbert quotient norm of `Γ / Δ`), `quasiIso_sum` and `represents` (Theorem 7 and
Corollary 1 of [ArnoldHu2021]) after its first three. `derivedVerdict_old` states the earlier
three-field verdict (closed range, finite-dimensional cohomology, the dimension bound) verbatim
and derives it from the new structure.

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

end FeecCheck.BGGVerdicts
