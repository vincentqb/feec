module

public import Feec.Counterexamples.Sharpness

/-!
# Regression tests: bounded cochain projections and discrete stability

The statements of `Feec.HilbertComplex.Subcomplex.exists_cochainProjection` ([AFW2010], Thm 3.7)
and `Feec.HilbertComplex.Subcomplex.exists_isGraphBounded_iff` (Thms 3.6, 3.7 and (30)), written
out verbatim and proved from the library, and the field `projections` of the crown's sharpness
record `Feec.Counterexamples.CrownSharpness` (`SubcomplexFamily.exists_isGraphBounded_iff`), read
back with `SubcomplexFamily.IsGraphBounded` unfolded, its field `charZero_exact` (characteristic
`0` is necessary for the Poincaré lemma of `H_mΛᵏ`), and the statements that characteristic `0`
is necessary for the classification of the invariant subspaces of `H_mΛᵏ`, with the
counterexamples behind them. A change of any of these statements fails `lake build FeecCheck`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3, Thms 3.6, 3.7
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.4

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

/-- [AFW2010], Thms 3.6, 3.7, (30), for bare projections. -/
example {κ : Type} (V : κ → H.Subcomplex) [∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
    (hcr : ∀ i, H.ClosedRangeAt i) :
    (∃ π : ∀ h, (V h).CochainProjection, ∀ i, ∃ C, ∀ h, (π h).IsGraphBounded i (c.next i) C) ↔
      ∀ i, ∃ c₁ c₂ : ℝ, ∀ h, (V h).DiscretePoincare i c₁ ∧ (V h).HarmonicBound i c₂ :=
  Subcomplex.exists_isGraphBounded_iff V hcr

/-- The crown's sharpness field `projections`: the hypothesis `SubcomplexFamily.IsGraphBounded`
of the static FEEC theorem is discrete stability. -/
example {κ : Type} (l : Filter κ) (V : κ → H.Subcomplex) [∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
    (hcr : ∀ i, H.ClosedRangeAt i) :
    (∃ G : SubcomplexFamily H κ, G.l = l ∧ G.V = V ∧ ∀ i, ∃ C, ∀ h,
        ∀ x : (H.d i (c.next i)).domain,
          ‖(G.π h).π i x‖ ^ 2 +
              ‖H.d i (c.next i) ⟨(G.π h).π i x, (G.V h).le_domain i _ ((G.π h).mem i x)⟩‖ ^ 2 ≤
            C ^ 2 * (‖(x : W i)‖ ^ 2 + ‖H.d i (c.next i) x‖ ^ 2)) ↔
      ∀ i, ∃ c₁ c₂ : ℝ, ∀ h, (V h).DiscretePoincare i c₁ ∧ (V h).HarmonicBound i c₂ :=
  Feec.Counterexamples.crownSharpness.{0, 0}.projections l V hcr

/-! ### Characteristic `0` and the polynomial shape spaces -/

section PositiveCharacteristic

open Feec Feec.FiniteElement Feec.Counterexamples.PositiveCharacteristic
open Koszul (PolyForm homForm coeffForm koszulₗ extDerivₗ)

variable (K : Type) [Field K]

/-- `charZero_iff_classification_ker`: the summands as kernels. -/
example : CharZero K ↔ ∀ (n : ℕ) (W : Submodule K (PolyForm K (Fin n))), IsGLInvariant W →
    ∀ m k, 0 < m + k → W ≤ homForm K (Fin n) m k →
      W = ⊥ ∨ W = homForm K (Fin n) m k ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ∨
        W = homForm K (Fin n) m k ⊓ LinearMap.ker (koszulₗ K (Fin n)) ∨
          W = homForm K (Fin n) m k :=
  charZero_iff_classification_ker K

/-- `charZero_iff_classification`: the summands as images ([AFW2006], §3.4). -/
example : CharZero K ↔ ∀ (n : ℕ) (W : Submodule K (PolyForm K (Fin n))), IsGLInvariant W →
    ∀ m k, W ≤ homForm K (Fin n) (m + 1) (k + 1) →
      W = ⊥ ∨ W = (homForm K (Fin n) (m + 2) k).map (extDerivₗ K (Fin n)) ∨
        W = (homForm K (Fin n) m (k + 2)).map (koszulₗ K (Fin n)) ∨
          W = homForm K (Fin n) (m + 1) (k + 1) :=
  charZero_iff_classification K

/-- The crown's sharpness field `charZero_exact`. -/
example : CharZero K ↔ ∀ n m k,
    homForm K (Fin n) m (k + 1) ⊓ LinearMap.ker (extDerivₗ K (Fin n)) =
      (homForm K (Fin n) (m + 1) k).map (extDerivₗ K (Fin n)) :=
  Feec.Counterexamples.crownSharpness.{0, 0}.charZero_exact K

variable {K} {n : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The counterexample: `UΛ¹`, `U` spanned by the `x_l^{p²}`, is linearly invariant, in
`H_{p²}Λ¹`, and not one of the four. -/
example {i j : Fin n} (hij : i ≠ j) {m : ℕ} (hm : m + 1 = p ^ 2) :
    IsLinearInvariant (coeffForm K 1 (powSpan K n (m + 1))) ∧
      coeffForm K 1 (powSpan K n (m + 1)) ≤ homForm K (Fin n) (m + 1) 1 ∧
      ¬ (coeffForm K 1 (powSpan K n (m + 1)) = ⊥ ∨
        coeffForm K 1 (powSpan K n (m + 1)) =
          (homForm K (Fin n) (m + 2) 0).map (extDerivₗ K (Fin n)) ∨
        coeffForm K 1 (powSpan K n (m + 1)) = (homForm K (Fin n) m 2).map (koszulₗ K (Fin n)) ∨
        coeffForm K 1 (powSpan K n (m + 1)) = homForm K (Fin n) (m + 1) 1) :=
  ⟨hm ▸ isLinearInvariant_coeffForm_powSpan p 1, coeffForm_powSpan_le_homForm _ 1,
    coeffForm_powSpan_not_classified_succ p hij hm⟩

/-- The counterexample: `x_i^{p-1} dx_i` is closed and not exact. -/
example (i : Fin n) {m : ℕ} (hm : m + 1 = p) :
    (Pi.single {i} (MvPolynomial.X i ^ m) : PolyForm K (Fin n)) ∈
        homForm K (Fin n) m 1 ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ∧
      (Pi.single {i} (MvPolynomial.X i ^ m) : PolyForm K (Fin n)) ∉
        (homForm K (Fin n) (m + 1) 0).map (extDerivₗ K (Fin n)) :=
  closed_not_exact p i hm

end PositiveCharacteristic

end FeecCheck.Sharpness
