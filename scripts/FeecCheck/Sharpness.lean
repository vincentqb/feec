module

public import Feec.Counterexamples.Sharpness

/-!
# Regression tests: bounded cochain projections and discrete stability

The statements of `Feec.HilbertComplex.Subcomplex.exists_cochainProjection` ([AFW2010], Thm 3.7)
and `Feec.HilbertComplex.Subcomplex.exists_isGraphBounded_iff` (Thms 3.6, 3.7 and (30)), written
out verbatim and proved from the library, and the field `projections` of the crown's sharpness
record `Feec.Counterexamples.CrownSharpness`, read back as the characterization. A change of
either statement fails `lake build FeecCheck`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3, Thms 3.6, 3.7

Bibliography: [references.bib](../../docs/references.bib)
-/

public section

open scoped InnerProductSpace

namespace FeecCheck.Sharpness

open Feec.HilbertComplex

variable {𝕜 : Type} [RCLike 𝕜] {ι : Type} {c : ComplexShape ι} {W : ι → Type}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : Feec.HilbertComplex 𝕜 c W}

/-- [AFW2010], Thm 3.7, with the explicit bound `(1 + c₁ʲ)(1 + c₂ʲ)`. -/
example (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)] {c₁ c₂ : ι → ℝ}
    (hc₁ : ∀ j, 0 ≤ c₁ j) (hc₂ : ∀ j, 0 ≤ c₂ j)
    (hP : ∀ j, ∀ ⦃x : W j⦄ (hx : x ∈ S.V j), (∀ y ∈ S.cyclesW j, ⟪y, x⟫_𝕜 = 0) →
      ‖x‖ ^ 2 + ‖H.d j (c.next j) ⟨x, S.le_domain j _ hx⟩‖ ^ 2 ≤
        c₁ j ^ 2 * ‖H.d j (c.next j) ⟨x, S.le_domain j _ hx⟩‖ ^ 2)
    (hH : ∀ j, ∀ q ∈ S.harmonicW j, ‖q‖ ≤ c₂ j * ‖(H.harmonic j).starProjection q‖) :
    ∃ P : S.CochainProjection, ∀ j (x : (H.d j (c.next j)).domain),
      ‖P.π j x‖ ^ 2 + ‖H.d j (c.next j) ⟨P.π j x, S.le_domain j _ (P.mem j x)⟩‖ ^ 2 ≤
        ((1 + c₁ j) * (1 + c₂ j)) ^ 2 * (‖(x : W j)‖ ^ 2 + ‖H.d j (c.next j) x‖ ^ 2) :=
  S.exists_cochainProjection hc₁ hc₂ hP hH

/-- The crown's sharpness field `projections` is the characterization of bounded projections. -/
example {κ : Type} (V : κ → H.Subcomplex) [∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
    (hcr : ∀ i, H.ClosedRangeAt i) :
    (∃ π : ∀ h, (V h).CochainProjection, ∀ i, ∃ C, ∀ h, (π h).IsGraphBounded i (c.next i) C) ↔
      ∀ i, ∃ c₁ c₂ : ℝ, ∀ h, (V h).DiscretePoincare i c₁ ∧ (V h).HarmonicBound i c₂ :=
  Feec.Counterexamples.crownSharpness.{0, 0}.projections V hcr

end FeecCheck.Sharpness
