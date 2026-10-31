module

public import Solution.Bridge

/-!
# The BGG construction (solution)

`FEEC.bggCohomology`, `FEEC.bggIdentification`, `FEEC.bggFinrank`, `FEEC.bggSum`,
`FEEC.bggExplicit`, `FEEC.bggClosedRange` and `FEEC.bggOrthogonal` of
`Challenge.lean`, proved through the bridge `Solution.Bridge` (`FEEC.BGG.verdict`,
`FEEC.BGG.identification`, `FEEC.BGG.finiteDimensional_and_finrank_le`, `FEEC.BGG.sum`,
`FEEC.BGG.explicit`, `FEEC.BGG.closedRange`, `FEEC.BGG.orthogonal`)
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

/-- **The orthogonal form of Theorem 7: the cochain map (30) with Moore–Penrose inverses**
([ArnoldHu2021], (15)–(16), (23), (28)–(30), Theorem 7). Let `d`, `d̃` be complexes of bounded
operators on Hilbert spaces and `s` bounded connecting maps with `d s = -s d̃`, null-homotopic,
`sⁱ = dKⁱ - Kⁱ⁺¹d̃` ((28)), with `sⁱ` injective for `i ≤ J`, surjective for `i ≥ J` ((23)) and
of closed range for `i < J`; let `tⁱ⁺¹ = (sⁱ)†` (`BGG.moorePenrose`). Then there is a complex `Y`
with isomorphisms `Yⁱ ≅ Υⁱ` onto the output spaces (`BGG.Υ`: `R(sⁱ⁻¹)ᗮ` up to `J`, `N(sⁱ)` after)
carrying its differential to the output differentials (16), `P_{R(sⁱ)ᗮ} d` before `J`,
`d̃ (sᴶ)† d` at `J`, `d̃` after `J`, and a quasi-isomorphism `κ` from the sum complex to `Y` which
is the map (30): `(ω, μ) ↦ P_{R(sⁱ⁻¹)ᗮ}(ω + Kμ)` up to `J`, and in degree `i + 1 > J`,
`(ω, μ) ↦ P_{N(sⁱ⁺¹)}(d̃ tⁱ⁺¹ω + (I + d̃ tⁱ⁺¹ K)μ)`; and `Y` is isomorphic to the BGG complex. -/
theorem bggOrthogonal {𝕜 : Type u} [RCLike 𝕜] {H Ht : ℤ → Type v}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace 𝕜 (H i)] [∀ i, CompleteSpace (H i)]
    [∀ i, NormedAddCommGroup (Ht i)] [∀ i, InnerProductSpace 𝕜 (Ht i)]
    [∀ i, CompleteSpace (Ht i)]
    (d : ∀ i, H i →L[𝕜] H (i + 1)) (hd : ∀ i x, d (i + 1) (d i x) = 0)
    (dt : ∀ i, Ht i →L[𝕜] Ht (i + 1)) (hdt : ∀ i x, dt (i + 1) (dt i x) = 0)
    (s : ∀ i, Ht i →L[𝕜] H (i + 1)) (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x))
    (K : ∀ i, Ht i →ₗ[𝕜] H i) (hK : ∀ i μ, s i μ = d i (K i μ) - K (i + 1) (dt i μ))
    (J : ℤ) (hinj : ∀ i ≤ J, Function.Injective (s i))
    (hsurj : ∀ i, J ≤ i → Function.Surjective (s i))
    (hR : ∀ i < J, IsClosed (Set.range (s i))) :
    let S := BGG.ofBoundedHom (hd := hd) (hdt := hdt) s hs
    let P := fun i => (BGG.rangeS S i : Submodule 𝕜 (H i))ᗮ.starProjection
    ∃ (Y : CochainComplex (ModuleCat.{v} 𝕜) ℤ) (e : ∀ i, Y.X i ≃ₗ[𝕜] BGG.Υ (hd := hd) (hdt := hdt) s hs J i)
      (κ : BGG.twisted (0 : BGG.ofBounded dt hdt ⟶ (BGG.ofBounded d hd)⟦(1 : ℤ)⟧) ⟶ Y),
      (∀ i < J, ∀ y, (e (i + 1) (Y.d i (i + 1) y) : H (i + 1) × Ht (i + 1)) =
        (P (i + 1) (d i (e i y : H i × Ht i).1), 0)) ∧
      (∀ y, (e (J + 1) (Y.d J (J + 1) y) : H (J + 1) × Ht (J + 1)) =
        (0, dt J (BGG.moorePenrose (s J) (d J (e J y : H J × Ht J).1)))) ∧
      (∀ i, J < i → ∀ y, (e (i + 1) (Y.d i (i + 1) y) : H (i + 1) × Ht (i + 1)) =
        (0, dt i (e i y : H i × Ht i).2)) ∧
      (∀ i ≤ J, ∀ x : H i × Ht i, (e i ((κ.f i).hom x) : H i × Ht i) = (P i (x.1 + K i x.2), 0)) ∧
      (∀ i, J ≤ i → ∀ x : H (i + 1) × Ht (i + 1),
        (e (i + 1) ((κ.f (i + 1)).hom x) : H (i + 1) × Ht (i + 1)) =
          (0, (s (i + 1)).ker.starProjection (dt i (BGG.moorePenrose (s i) x.1) +
            (x.2 + dt i (BGG.moorePenrose (s i) (K (i + 1) x.2)))))) ∧
      QuasiIso κ ∧ Nonempty (Y ≅ BGG.bgg S J) :=
  BGG.orthogonal d hd dt hdt s hs K hK J hinj hsurj hR

end FEEC
