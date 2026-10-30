module

public import Solution.Bridge

/-!
# The algebra of the periodic table (solution)

`FEEC.periodicTable` of `Challenge.lean`, proved from `Feec.Algebra.PolynomialFormDim` and
`Feec.Algebra.CubicalForm` through the bridge `Solution.Bridge` (`periodicTable_of_feec`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3
* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §3

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

universe u

namespace FEEC

/-- **The algebra of the periodic table of the finite elements** ([AFW2006], §3;
[ArnoldBoffiBonizzoni2015], §3). Over every field of characteristic `0`, in every dimension `n`,
the spaces `P_rΛᵏ`, `P_r⁻Λᵏ` and `Q_r⁻Λᵏ` have the dimensions of the periodic table, their
polynomial de Rham complexes are exact with the constants as cohomology in degree `0`, and the
Koszul decompositions hold (`PeriodicTable`). -/
theorem periodicTable (K : Type u) [Field K] [CharZero K] (n : ℕ) : PeriodicTable K n :=
  periodicTable_of_feec K n

end FEEC
