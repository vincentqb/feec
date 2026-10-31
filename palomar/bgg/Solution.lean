module

public import Solution.Bridge

/-!
# The BGG construction (solution)

`FEEC.bggCohomology`, `FEEC.bggIdentification`, `FEEC.bggFinrank`, `FEEC.bggSum`,
`FEEC.bggExplicit` and `FEEC.bggClosedRange` of
`Challenge.lean`, proved through the bridge `Solution.Bridge` (`FEEC.BGG.verdict`,
`FEEC.BGG.identification`, `FEEC.BGG.finiteDimensional_and_finrank_le`, `FEEC.BGG.sum`,
`FEEC.BGG.explicit`, `FEEC.BGG.closedRange`)
from `Feec.BGG.Data.quasiIso_Γ`, `Feec.BGG.Data.quasiIso_derived`,
`Feec.BGG.Data.finrank_twistComplex_homology_eq_iff`, `Feec.BGG.Data.bggProj`,
`Feec.BGG.Data.quasiIso_of_Γι_comp`, `HomologicalComplex.Represents.map` and
`Feec.BGG.BoundedData.isClosed_Δ_sup_map_twist`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], (24)–(31), Theorems 6 and 7,
  Corollary 1 and §5

Bibliography: [references.bib](../../docs/references.bib)
-/

open CategoryTheory

@[expose] public noncomputable section

universe u v

namespace FEEC

/-- **The BGG construction** ([ArnoldHu2021], §5.2). For a stacked diagram `S : Ṽ ⟶ V⟦1⟧` of
cochain complexes of modules over any ring, with `Sⁱ` injective for `i < J` and onto modulo `d`
for `i ≥ J` (`R(dⁱ) + R(Sⁱ) = Vⁱ⁺¹`; in particular when `Sⁱ` is surjective, [ArnoldHu2021], (23)),
the BGG complex at `J` has the cohomology of the twisted complex (`BGG.Verdict`). -/
theorem bggCohomology {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i →
      LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (BGG.conn S i (i + 1)) = ⊤) :
    BGG.Verdict S J :=
  BGG.verdict hinj hsurj

/-- **The BGG complex is the output complex of [ArnoldHu2021], (24)–(26)**, for every stacked
diagram and every `J` (`BGG.Identification`). -/
theorem bggIdentification {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) : BGG.Identification S J :=
  BGG.identification S J

/-- **The cohomology of the BGG complex** ([ArnoldHu2021], Theorem 6). Over a field, under the
hypotheses of `FEEC.bggCohomology`, if both rows have finite-dimensional cohomology in degree `i`,
so does the BGG complex, `dim Hⁱ(Γ / Δ) ≤ dim Hⁱ(V) + dim Hⁱ(Ṽ)`, with equality if and only if
`Sⁱ⁻¹` and `Sⁱ` induce the zero maps on cohomology ([ArnoldHu2021], (27)). -/
theorem bggFinrank {K : Type u} [Field K] {V Vt : CochainComplex (ModuleCat.{v} K) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i →
      LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (BGG.conn S i (i + 1)) = ⊤) (i : ℤ)
    [FiniteDimensional K (V.homology i)] [FiniteDimensional K (Vt.homology i)] :
    FiniteDimensional K ((BGG.bgg S J).homology i) ∧
      Module.finrank K ((BGG.bgg S J).homology i) ≤
        Module.finrank K (V.homology i) + Module.finrank K (Vt.homology i) ∧
      (Module.finrank K ((BGG.bgg S J).homology i) =
          Module.finrank K (V.homology i) + Module.finrank K (Vt.homology i) ↔
        BGG.InducesZero S (i - 1) ∧ BGG.InducesZero S i) :=
  BGG.finiteDimensional_and_finrank_le hinj hsurj i

/-- **Cohomology through the sum complex** ([ArnoldHu2021], Theorem 7 and Proposition 1). If
`Sⁱ = dKⁱ - Kⁱ⁺¹d̃` for maps `Kⁱ : Ṽⁱ → Vⁱ` ((28)), then `S` induces the zero maps on cohomology
((27), Proposition 1) and the cochain map `(ω, μ) ↦ (ω + Kμ, μ)` from the sum complex (the
twisted complex of `S = 0`: `Vⁱ × Ṽⁱ` with differential `d × d̃`) to the twisted complex is an
isomorphism; under the hypotheses of `FEEC.bggCohomology` at any `J`, the BGG complex has the
cohomology of the sum complex (Theorem 7). -/
theorem bggSum {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (K : ∀ i, Vt.X i →ₗ[R] V.X i)
    (hK : ∀ i μ, BGG.conn S i (i + 1) μ = V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ)) :
    (∀ i, BGG.InducesZero S i) ∧ IsIso (BGG.sumToTwisted S K hK) ∧
      ∀ J, (∀ i < J, Function.Injective (S.f i)) →
        (∀ i, J ≤ i →
          LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (BGG.conn S i (i + 1)) = ⊤) →
        ∀ i, Nonempty ((BGG.bgg S J).homology i ≅
          (BGG.twisted (0 : Vt ⟶ V⟦(1 : ℤ)⟧)).homology i) :=
  BGG.sum S K hK

/-- **The explicit cochain map of Theorem 7 and the cohomology representatives of Corollary 1**
([ArnoldHu2021], (30), (31)). If `Sⁱ = dKⁱ - Kⁱ⁺¹d̃` ((28)), `Sⁱ` is injective for `i ≤ J` and
`tⁱ⁺¹` is a right inverse of `Sⁱ` for `i ≥ J` ((23), (29)), then `BGG.sumMap` defines a cochain
map `κ` from the sum complex to the BGG complex at `J` (with values in `Γ`), `κ` induces an
isomorphism on cohomology (Theorem 7), and if `H`, `H̃` represent the cohomology of the rows in
degree `i`, then `κ(H × H̃)` represents the cohomology of the BGG complex (Corollary 1). -/
theorem bggExplicit {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (K : ∀ i, Vt.X i →ₗ[R] V.X i)
    (hK : ∀ i μ, BGG.conn S i (i + 1) μ = V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ))
    (J : ℤ) (t : ∀ i j, V.X j →ₗ[R] Vt.X i) (hinj : ∀ i ≤ J, Function.Injective (S.f i))
    (ht : ∀ i, J ≤ i → ∀ v, BGG.conn S i (i + 1) (t i (i + 1) v) = v) :
    ∃ κ : BGG.twisted (0 : Vt ⟶ V⟦(1 : ℤ)⟧) ⟶ BGG.bgg S J,
      (∀ i x, ∃ hx : BGG.sumMap S K t J i x ∈ BGG.Γ S J i,
        (κ.f i).hom x = Submodule.Quotient.mk ⟨_, hx⟩) ∧ QuasiIso κ ∧
      ∀ i (H : Submodule R (V.X i)) (Ht : Submodule R (Vt.X i)), BGG.Represents V i H →
        BGG.Represents Vt i Ht → BGG.Represents (BGG.bgg S J) i ((H.prod Ht).map (κ.f i).hom) :=
  BGG.explicit S K hK J t hinj ht

/-- **The BGG complex of bounded Hilbert complexes is a bounded Hilbert complex with closed
ranges** ([ArnoldHu2021], Theorem 6 and the remark after it). Let `d`, `d̃` be complexes of
bounded operators on Hilbert spaces and `s` bounded connecting maps with `d s = -s d̃`, bounded
below for `i < J` and onto modulo `d` for `i ≥ J`. Then `Γⁱ` and `Δⁱ` are closed in `Hⁱ × H̃ⁱ`, so
`Γⁱ / Δⁱ` is a Hilbert space and the differentials, induced by the bounded twisted differential,
are bounded; and where both rows have finite-dimensional cohomology, the range of the BGG
differential into `Γⁱ / Δⁱ` is closed: its preimage `Δⁱ + T(Γⁱ⁻¹)` in `Hⁱ × H̃ⁱ` is closed. -/
theorem bggClosedRange {𝕜 : Type u} [RCLike 𝕜] {H Ht : ℤ → Type v}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace 𝕜 (H i)] [∀ i, CompleteSpace (H i)]
    [∀ i, NormedAddCommGroup (Ht i)] [∀ i, InnerProductSpace 𝕜 (Ht i)]
    [∀ i, CompleteSpace (Ht i)]
    (d : ∀ i, H i →L[𝕜] H (i + 1)) (hd : ∀ i x, d (i + 1) (d i x) = 0)
    (dt : ∀ i, Ht i →L[𝕜] Ht (i + 1)) (hdt : ∀ i x, dt (i + 1) (dt i x) = 0)
    (s : ∀ i, Ht i →L[𝕜] H (i + 1)) (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x))
    (J : ℤ) (hinj : ∀ i < J, ∃ C, AntilipschitzWith C (s i))
    (hsurj : ∀ i, J ≤ i → LinearMap.range (d i : H i →ₗ[𝕜] H (i + 1)) ⊔
      LinearMap.range (s i : Ht i →ₗ[𝕜] H (i + 1)) = ⊤) (i : ℤ) :
    let S := BGG.ofBoundedHom (hd := hd) (hdt := hdt) s hs
    IsClosed (BGG.Γ S J i : Set (H i × Ht i)) ∧ IsClosed (BGG.Δ S J i : Set (H i × Ht i)) ∧
      ([FiniteDimensional 𝕜 ((BGG.ofBounded d hd).homology i)] →
        [FiniteDimensional 𝕜 ((BGG.ofBounded dt hdt).homology i)] →
        IsClosed ((BGG.Δ S J i ⊔ (BGG.Γ S J (i - 1)).map (BGG.twist S (i - 1) i) :
          Submodule 𝕜 _) : Set (H i × Ht i))) :=
  BGG.closedRange s hs J hinj hsurj i

end FEEC
