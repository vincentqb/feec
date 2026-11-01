module

public import Feec.Instances.Corollaries

/-!
# Regression test: the shape spaces of the periodic table over `ℝ`

`Feec.FiniteElement.PolyComplex` stated the shape spaces `PolyKind.form` of the periodic table, their
description as spaces `X(r', r - 1, k)` of [AFW2006], Theorem 3.5, and their affine invariance over
`ℝ`, and the closed-form dimensions of the classical elements for the form fields over `ℝ³`, `ℝ²`.
The spaces are now defined over every commutative ring and the algebra holds over every field (of
characteristic `0` for the trimmed spaces and the invariance); the closed-form dimensions over `ℝ`
are specializations of those over every field (`finrank_polyForm_three_one`, …). The theorems below
state the old real results verbatim (with the field `ℝ` explicit) and derive them from the new ones
at `K = ℝ`.

This file is part of the `FeecCheck` library, not of `Feec`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.4, Theorem 3.5

Bibliography: [references.bib](../../docs/references.bib)
-/

public section

namespace FeecCheck.PolyFields

open Feec Feec.FiniteElement

variable {n : ℕ}

/-- The earlier `PolyKind.space_eq_map_form`, with `PolyKind.form` over `ℝ`. -/
theorem space_eq_map_form_old (κ : PolyKind) (r k : ℕ) :
    κ.space n r k = (κ.form ℝ r k).map (evalForm n) :=
  κ.space_eq_map_form r k

/-- The earlier `PolyKind.form_eq_sup` over `ℝ` ([AFW2006], Theorem 3.5). -/
theorem form_eq_sup_old (κ : PolyKind) {r k : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) :
    κ.form ℝ (n := n) r k =
      (Koszul.polyForm ℝ (Fin n) (κ.dDeg r + 1) (k - 1)).map (Koszul.extDerivₗ ℝ (Fin n)) ⊔
        (Koszul.polyForm ℝ (Fin n) (r - 1) (k + 1)).map (Koszul.koszulₗ ℝ (Fin n)) :=
  κ.form_eq_sup hr hk

/-- The earlier `PolyKind.isAffineInvariant_form` over `ℝ` ([AFW2006], Theorem 3.5). -/
theorem kind_isAffineInvariant_form_old (κ : PolyKind) {r k : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) :
    IsAffineInvariant (κ.form ℝ (n := n) r k) :=
  κ.isAffineInvariant_form hr hk

/-- The earlier `PolySeq.isAffineInvariant_form` over `ℝ` ([AFW2006], Theorem 3.5). -/
theorem seq_isAffineInvariant_form_old (S : PolySeq) {k : ℕ} (hk : 1 ≤ k) :
    IsAffineInvariant ((S.kind k).form ℝ (n := n) (S.deg k) k) :=
  S.isAffineInvariant_form hk

/-- The earlier `Feec.Instances.Corollaries.Cube.FEM.feec_affineInvariant`, verbatim. -/
theorem feec_affineInvariant_old (n : ℕ) [NeZero n] (S : PolySeq) :
    (Models.Cube.FEM.polyFamily n S).Verdict ∧ ∀ k, 1 ≤ k →
      S.space n k = ((S.kind k).form ℝ (S.deg k) k).map (evalForm n) ∧
        IsAffineInvariant ((S.kind k).form ℝ (n := n) (S.deg k) k) :=
  Instances.Corollaries.Cube.FEM.feec_affineInvariant n S

end FeecCheck.PolyFields
