module

public import Solution.Affine
public import Solution.Bridge

/-!
# The algebra of the periodic table (solution)

`FEEC.periodicTable` of `Challenge.lean`, proved from `Feec.Algebra.PolynomialFormDim` and
`Feec.Algebra.CubicalForm` through the bridge `Solution.Bridge` (`periodicTable_of_feec`), which
identifies the forms `MvPolynomial ⊗ ExteriorAlgebra` of the challenge with the coefficient forms of
`Feec` (`Feec.Algebra.ExteriorAlgebraForm`), and `FEEC.affineInvariantForms` from
`Feec.FiniteElement.InvariantForm` and `Feec.FiniteElement.AffineInvariantForm` through
`Solution.Affine` (`affineInvariantForms_of_feec`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3
* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §5

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

universe u

namespace FEEC

/-- **The algebra of the periodic table of the finite elements** ([AFW2006], §3;
[ArnoldBoffiBonizzoni2015], §5). In every dimension `n`, the spaces `P_rΛᵏ`, `P_r⁻Λᵏ` and
`Q_b⁻Λᵏ` have the dimensions of the periodic table and, in characteristic `0`, their polynomial de
Rham complexes are resolutions of the constants; the homotopy formula and the Koszul
decompositions hold (`PeriodicTable`). -/
theorem periodicTable (K : Type u) [Field K] (n : ℕ) : PeriodicTable K n :=
  periodicTable_of_feec K n

/-- **The affinely invariant spaces of polynomial differential forms** on `ℝⁿ` ([AFW2006],
Theorems 3.5–3.6): for `0 < k < n` they are the spaces `dP_{r+1}Λ^{k-1} + κP_sΛ^{k+1}`,
`-1 ≤ s ≤ r`, among them `P_rΛᵏ` and `P_{r+1}⁻Λᵏ`; the summands `dH_{r+1}Λ^{k-1}` and
`κH_{r-1}Λ^{k+1}` of `H_rΛᵏ` are irreducible under the linear maps
(`AffineInvariantForms`). -/
theorem affineInvariantForms (n : ℕ) : AffineInvariantForms n :=
  affineInvariantForms_of_feec n

end FEEC
