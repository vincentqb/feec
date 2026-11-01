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
`Solution.Affine` (`affineInvariantForms_of_feec`), and `FEEC.charZero_iff_classification` from
`Feec.Counterexamples.PositiveCharacteristic` (`charZero_iff_classification_of_feec`).

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

/-- **The affinely invariant spaces of polynomial differential forms** on `Kⁿ`, `K` of
characteristic `0` ([AFW2006], Theorems 3.5–3.6): for `0 < k < n` they are the spaces
`dP_{r+1}Λ^{k-1} + κP_sΛ^{k+1}`, `-1 ≤ s ≤ r`, among them `P_rΛᵏ` and `P_{r+1}⁻Λᵏ`; the summands
`dH_{r+1}Λ^{k-1}` and `κH_{r-1}Λ^{k+1}` of `H_rΛᵏ` are irreducible under `GL(n)`
(`AffineInvariantForms`). -/
theorem affineInvariantForms (K : Type u) [Field K] [CharZero K] (n : ℕ) :
    AffineInvariantForms K n :=
  affineInvariantForms_of_feec K n

/-- **Characteristic `0` is necessary for the classification** ([AFW2006], §3.4): the
`GL(n)`-invariant subspaces of `H_{r+1}Λ^{k+1}` are `0`, `dH_{r+2}Λᵏ`, `κH_rΛ^{k+2}` and
`H_{r+1}Λ^{k+1}` in every dimension `n` and all degrees iff `K` has characteristic `0`. -/
theorem charZero_iff_classification (K : Type u) [Field K] :
    CharZero K ↔ ∀ (n r k : ℕ) (W : Submodule K (Form K n)), IsGLInvariant K n W →
      W ≤ homForm K n (r + 1) (k + 1) →
        W = ⊥ ∨ W = (homForm K n (r + 2) k).map (extDeriv K n) ∨
          W = (homForm K n r (k + 2)).map (koszul K n) ∨ W = homForm K n (r + 1) (k + 1) :=
  charZero_iff_classification_of_feec K

end FEEC
