module

public import Solution.Bridge

/-!
# The BGG construction (solution)

`FEEC.bggCohomology`, `FEEC.bggIdentification`, `FEEC.bggFinrank`, `FEEC.bggSum`,
`FEEC.bggExplicit`, `FEEC.bggHilbert` and `FEEC.bggOrthogonal` of
`Challenge.lean`, proved through the bridge `Solution.Bridge` (`FEEC.BGG.verdict`,
`FEEC.BGG.identification`, `FEEC.BGG.finiteDimensional_and_finrank_le`, `FEEC.BGG.sum`,
`FEEC.BGG.explicit`, `FEEC.BGG.hilbert`, `FEEC.BGG.orthogonal`)
from `Feec.BGG.Data.quasiIso_Γ`, `Feec.BGG.Data.quasiIso_derived`,
`Feec.BGG.Data.finrank_twistComplex_homology_eq_iff`, `Feec.BGG.Data.bggProj`,
`Feec.BGG.Data.quasiIso_of_Γι_comp`, `HomologicalComplex.Represents.map`,
`Feec.HilbertComplex.Subquotient.toQuotEquiv`, `Feec.HilbertComplex.Subquotient.quotD_toQuot`,
`Feec.HilbertComplex.Subquotient.cohomologyEquiv`, `Feec.BGG.BoundedData.quasiIso_orthSumMap` and
`Feec.BGG.BoundedData.orth_represents`.

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

/-- **The BGG complex of bounded Hilbert complexes is a bounded Hilbert complex, with the
quotient norm, and has closed ranges** ([ArnoldHu2021], Theorem 6 and the remark after it). Let
`d`, `d̃` be complexes of bounded operators on Hilbert spaces and `s` bounded connecting maps with
`d s = -s d̃`, bounded below for `i < J` and onto modulo `d` for `i ≥ J`. Then `Γⁱ` and `Δⁱ` are
closed in `Hⁱ × H̃ⁱ`; for the quotient norm of the `ℓ²` norm, `y ↦ [y]` is an isometry of the
closed subspace `Γⁱ ⊖ Δⁱ = Γⁱ ∩ (Δⁱ)ᗮ` of the Hilbert space `Hⁱ ⊕ H̃ⁱ` onto `Γⁱ / Δⁱ` (so the
quotient norm is a Hilbert norm); the differentials `[(σ, φ)] ↦ [(dσ - sφ, d̃φ)]` of the BGG
complex are bounded for it; and where both rows have finite-dimensional cohomology in degree
`i + 1`, the differential into `Γⁱ⁺¹ / Δⁱ⁺¹` has closed range. -/
theorem bggHilbert {𝕜 : Type u} [RCLike 𝕜] {H Ht : ℤ → Type v}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace 𝕜 (H i)] [∀ i, CompleteSpace (H i)]
    [∀ i, NormedAddCommGroup (Ht i)] [∀ i, InnerProductSpace 𝕜 (Ht i)]
    [∀ i, CompleteSpace (Ht i)]
    (d : ∀ i, H i →L[𝕜] H (i + 1)) (hd : ∀ i x, d (i + 1) (d i x) = 0)
    (dt : ∀ i, Ht i →L[𝕜] Ht (i + 1)) (hdt : ∀ i x, dt (i + 1) (dt i x) = 0)
    (s : ∀ i, Ht i →L[𝕜] H (i + 1)) (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x))
    (J : ℤ) (hinj : ∀ i < J, ∃ C, AntilipschitzWith C (s i))
    (hsurj : ∀ i, J ≤ i → LinearMap.range (d i : H i →ₗ[𝕜] H (i + 1)) ⊔
      LinearMap.range (s i : Ht i →ₗ[𝕜] H (i + 1)) = ⊤) :
    let S := BGG.ofBoundedHom (hd := hd) (hdt := hdt) s hs
    let ΓL := BGG.ΓL (hd := hd) (hdt := hdt) s hs J
    let ΔL := BGG.ΔL (hd := hd) (hdt := hdt) s hs J
    let Q := BGG.QuotL (hd := hd) (hdt := hdt) s hs J
    (∀ i, IsClosed (BGG.Γ S J i : Set (H i × Ht i)) ∧ IsClosed (BGG.Δ S J i : Set (H i × Ht i))) ∧
      (∀ i, ∃ e : ↥(ΓL i ⊓ (ΔL i)ᗮ) ≃ₗᵢ[𝕜] Q i, ∀ y, e y = Submodule.Quotient.mk ⟨y, y.2.1⟩) ∧
      ∃ D : ∀ i, Q i →L[𝕜] Q (i + 1),
        (∀ i (x : ΓL i) (x' : ΓL (i + 1)), (x' : WithLp 2 (H (i + 1) × Ht (i + 1))).ofLp =
          BGG.twist S i (i + 1) (x : WithLp 2 (H i × Ht i)).ofLp →
            D i (Submodule.Quotient.mk x) = Submodule.Quotient.mk x') ∧
        ∀ i, [FiniteDimensional 𝕜 ((BGG.ofBounded d hd).homology (i + 1))] →
          [FiniteDimensional 𝕜 ((BGG.ofBounded dt hdt).homology (i + 1))] →
          IsClosed (Set.range (D i)) :=
  BGG.hilbert s hs J hinj hsurj

/-- **The orthogonal form of Theorem 7: the cochain map (30) with Moore–Penrose inverses**
([ArnoldHu2021], (24)–(26), (23), (28)–(30), Theorem 7). Let `d`, `d̃` be complexes of bounded
operators on Hilbert spaces and `s` bounded connecting maps with `d s = -s d̃`, null-homotopic,
`sⁱ = dKⁱ - Kⁱ⁺¹d̃` ((28)), with `sⁱ` injective for `i ≤ J`, surjective for `i ≥ J` ((23)) and
of closed range for `i < J`; let `tⁱ⁺¹ = (sⁱ)†` (`BGG.moorePenrose`). Then there is a complex `Y`
with isomorphisms `Yⁱ ≅ Υⁱ` onto the output spaces (`BGG.Υ`: `R(sⁱ⁻¹)ᗮ` up to `J`, `N(sⁱ)` after)
carrying its differential to the output differentials (26), `P_{R(sⁱ)ᗮ} d` before `J`,
`d̃ (sᴶ)† d` at `J`, `d̃` after `J`, and a quasi-isomorphism `κ` from the sum complex to `Y` which
is the map (30): `(ω, μ) ↦ P_{R(sⁱ⁻¹)ᗮ}(ω + Kμ)` up to `J`, and in degree `i + 1 > J`,
`(ω, μ) ↦ P_{N(sⁱ⁺¹)}(d̃ tⁱ⁺¹ω + (I + d̃ tⁱ⁺¹ K)μ)`; `Y` is isomorphic to the BGG complex; and
(Corollary 1, (31)) if `A`, `Ã` represent the cohomology of the rows in degree `i`, then `κ(A × Ã)`
represents that of `Y`. -/
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
      QuasiIso κ ∧ Nonempty (Y ≅ BGG.bgg S J) ∧
      ∀ i (A : Submodule 𝕜 (H i)) (At : Submodule 𝕜 (Ht i)),
        BGG.Represents (BGG.ofBounded d hd) i A → BGG.Represents (BGG.ofBounded dt hdt) i At →
          BGG.Represents Y i ((A.prod At).map (κ.f i).hom) :=
  BGG.orthogonal d hd dt hdt s hs K hK J hinj hsurj hR

end FEEC
