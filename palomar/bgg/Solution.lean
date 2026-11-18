module

public import Solution.Bridge

/-!
# Bernstein–Gelfand–Gelfand complexes (solution)

`FEEC.bggCohomology`, `FEEC.bggFinrank` and `FEEC.bggHilbert` of `Challenge.lean`, through the
bridge `Solution.Bridge`: `FEEC.BGG.identification`, `FEEC.BGG.verdict`, `FEEC.BGG.sum` and
`FEEC.BGG.explicit` (from `Feec.BGG.Data.quasiIso_Γ`, `Feec.BGG.Data.quasiIso_derived`,
`Feec.BGG.Data.bggSumMap`, `Feec.BGG.Data.quasiIso_bggSumMap`, `Feec.BGG.Data.bgg_represents`),
`FEEC.BGG.finiteDimensional_and_finrank_le` (`Feec.BGG.Data.finrank_twistComplex_homology_eq_iff`),
`FEEC.BGG.hilbert` (`Feec.HilbertComplex.Subquotient.toQuotEquiv`, `quotD_toQuot`,
`cohomologyEquiv`, `Feec.HilbertComplex.closedRangeAt_of_finiteDimensional_cohomology`) and
`FEEC.BGG.orthogonal` (`Feec.BGG.BoundedData.quasiIso_orthSumMap`, `isIso_toOrth`,
`orth_represents`).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], (24)–(31), Theorems 6 and 7,
  Proposition 1, Corollary 1 and §5

Bibliography: [references.bib](../../docs/references.bib)
-/

open CategoryTheory
open scoped InnerProductSpace

@[expose] public noncomputable section

universe u v

namespace FEEC

/-- **The BGG construction and its cohomology** ([ArnoldHu2021], (24)–(31), Theorem 7,
Proposition 1, Corollary 1, §5.2). For a stacked diagram `S : Ṽ ⟶ V⟦1⟧` of cochain complexes of
modules over any ring and every `J`: the BGG complex is the output complex (24)–(26)
(`BGG.Identification`), and `0 → V → T → Ṽ → 0` is short exact. If `Sⁱ` is injective for `i < J`
and onto modulo `d` for `i ≥ J` (`R(dⁱ) + R(Sⁱ) = Vⁱ⁺¹`, weaker than (23)), the inclusion `Γ → T`
and the projection `Γ → Γ / Δ` are quasi-isomorphisms: the BGG complex has the cohomology of the
twisted complex, is exact when both rows are, and, if `S` is null-homotopic, has the cohomology of
the sum complex (Theorem 7). If `Sⁱ = dKⁱ - Kⁱ⁺¹d̃` ((28)): `S` induces zero on cohomology
(Proposition 1), `(ω, μ) ↦ (ω + Kμ, μ)` is an isomorphism from the sum complex (the twisted complex
of `S = 0`) onto `T`, and if moreover `Sⁱ` is injective for `i ≤ J` with right inverses `tⁱ⁺¹`
for `i ≥ J` ((23), (29)), `BGG.sumMap` defines a quasi-isomorphism `κ` from the sum complex to the
BGG complex (the map (30), Theorem 7) carrying representatives `H × H̃` of the cohomology of the
rows to representatives of that of the BGG complex (Corollary 1, (31)). -/
theorem bggCohomology {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) :
    BGG.Identification S J ∧ (BGG.rows S).ShortExact ∧
    ((∀ i < J, Function.Injective (S.f i)) →
      (∀ i, J ≤ i →
        LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (BGG.conn S i (i + 1)) = ⊤) →
      QuasiIso (BGG.bggΓι S J) ∧ QuasiIso (BGG.bggπ S J) ∧
        (∀ i, Nonempty ((BGG.bgg S J).homology i ≅ (BGG.twisted S).homology i)) ∧
        (V.Acyclic → Vt.Acyclic → (BGG.bgg S J).Acyclic) ∧
        ∀ K : ∀ i, Vt.X i →ₗ[R] V.X i, (∀ i μ, BGG.conn S i (i + 1) μ =
          V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ)) →
          ∀ i, Nonempty ((BGG.bgg S J).homology i ≅
            (BGG.twisted (0 : Vt ⟶ V⟦(1 : ℤ)⟧)).homology i)) ∧
    ∀ (K : ∀ i, Vt.X i →ₗ[R] V.X i)
      (hK : ∀ i μ, BGG.conn S i (i + 1) μ = V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ)),
      (∀ i, BGG.InducesZero S i) ∧ IsIso (BGG.sumToTwisted S K hK) ∧
      ∀ t : ∀ i j, V.X j →ₗ[R] Vt.X i, (∀ i ≤ J, Function.Injective (S.f i)) →
        (∀ i, J ≤ i → ∀ v, BGG.conn S i (i + 1) (t i (i + 1) v) = v) →
        ∃ κ : BGG.twisted (0 : Vt ⟶ V⟦(1 : ℤ)⟧) ⟶ BGG.bgg S J,
          (∀ i x, ∃ hx : BGG.sumMap S K t J i x ∈ BGG.Γ S J i,
            (κ.f i).hom x = Submodule.Quotient.mk ⟨_, hx⟩) ∧ QuasiIso κ ∧
          ∀ i (H : Submodule R (V.X i)) (Ht : Submodule R (Vt.X i)), BGG.Represents V i H →
            BGG.Represents Vt i Ht →
              BGG.Represents (BGG.bgg S J) i ((H.prod Ht).map (κ.f i).hom) := by
  refine ⟨BGG.identification S J, BGG.rows_shortExact, fun hinj hsurj => ?_, fun K hK => ?_⟩
  · have V := BGG.verdict (S := S) hinj hsurj
    exact ⟨V.quasiIso_ι, V.quasiIso_π, V.homology, V.acyclic, fun K hK =>
      (BGG.sum S K hK).2.2 J hinj hsurj⟩
  · obtain ⟨h0, hiso, -⟩ := BGG.sum S K hK
    exact ⟨h0, hiso, fun t hinj ht => BGG.explicit S K hK J t hinj ht⟩

/-- **The dimension of the cohomology of the BGG complex** ([ArnoldHu2021], Theorem 6, (27)).
Over a field, under the hypotheses of `FEEC.bggCohomology`, if both rows have finite-dimensional
cohomology in degree `i`, so does the BGG complex, `dim Hⁱ(Γ / Δ) ≤ dim Hⁱ(V) + dim Hⁱ(Ṽ)`, with
equality if and only if `Sⁱ⁻¹` and `Sⁱ` induce the zero maps on cohomology. -/
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

/-- **The BGG complex of bounded Hilbert complexes** ([ArnoldHu2021], (23)–(31), Theorems 6 and 7,
the remark after Theorem 6, Corollary 1). Let `d`, `d̃` be complexes of bounded operators on
Hilbert spaces and `s` bounded connecting maps with `d s = -s d̃`. If `sⁱ` is bounded below for
`i < J` and onto modulo `d` for `i ≥ J`: `Γⁱ` and `Δⁱ` are closed in `Hⁱ × H̃ⁱ`; for the quotient
norm of the `ℓ²` norm, `y ↦ [y]` is an isometry of the closed subspace `Γⁱ ⊖ Δⁱ = Γⁱ ∩ (Δⁱ)ᗮ` of
the Hilbert space `Hⁱ ⊕ H̃ⁱ` onto `Γⁱ / Δⁱ` (so the quotient norm is a Hilbert norm); the
differentials `[(σ, φ)] ↦ [(dσ - sφ, d̃φ)]` of the BGG complex are bounded for it; and where both
rows have finite-dimensional cohomology in degree `i + 1`, the differential into `Γⁱ⁺¹ / Δⁱ⁺¹` has
closed range. If `sⁱ = dKⁱ - Kⁱ⁺¹d̃` ((28)) with `sⁱ` injective for `i ≤ J`, surjective for
`i ≥ J` ((23)) and of closed range for `i < J`, and `tⁱ⁺¹ = (sⁱ)†` (`BGG.moorePenrose`): there is
a complex `Y` with isomorphisms `Yⁱ ≅ Υⁱ` onto the output spaces (`BGG.Υ`: `R(sⁱ⁻¹)ᗮ` up to `J`,
`N(sⁱ)` after) carrying its differential to the output differentials (26), `P_{R(sⁱ)ᗮ} d` before
`J`, `d̃ (sᴶ)† d` at `J`, `d̃` after `J`; a quasi-isomorphism `κ` from the sum complex to `Y`, the
map (30): `(ω, μ) ↦ P_{R(sⁱ⁻¹)ᗮ}(ω + Kμ)` up to `J`, and in degree `i + 1 > J`,
`(ω, μ) ↦ P_{N(sⁱ⁺¹)}(d̃ tⁱ⁺¹ω + (I + d̃ tⁱ⁺¹ K)μ)`; `Y` is isomorphic to the BGG complex (as a
complex of modules); and if `A`, `Ã` represent the cohomology of the rows in degree `i`, then
`κ(A × Ã)` represents that of `Y` (Corollary 1, (31)). -/
theorem bggHilbert {𝕜 : Type u} [RCLike 𝕜] {H Ht : ℤ → Type v}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace 𝕜 (H i)] [∀ i, CompleteSpace (H i)]
    [∀ i, NormedAddCommGroup (Ht i)] [∀ i, InnerProductSpace 𝕜 (Ht i)]
    [∀ i, CompleteSpace (Ht i)]
    (d : ∀ i, H i →L[𝕜] H (i + 1)) (hd : ∀ i x, d (i + 1) (d i x) = 0)
    (dt : ∀ i, Ht i →L[𝕜] Ht (i + 1)) (hdt : ∀ i x, dt (i + 1) (dt i x) = 0)
    (s : ∀ i, Ht i →L[𝕜] H (i + 1)) (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x))
    (J : ℤ) :
    let S := BGG.ofBoundedHom (hd := hd) (hdt := hdt) s hs
    let ΓL := BGG.ΓL (hd := hd) (hdt := hdt) s hs J
    let ΔL := BGG.ΔL (hd := hd) (hdt := hdt) s hs J
    let Q := BGG.QuotL (hd := hd) (hdt := hdt) s hs J
    let P := fun i => (BGG.rangeS S i : Submodule 𝕜 (H i))ᗮ.starProjection
    ((∀ i < J, ∃ C, AntilipschitzWith C (s i)) →
      (∀ i, J ≤ i → LinearMap.range (d i : H i →ₗ[𝕜] H (i + 1)) ⊔
        LinearMap.range (s i : Ht i →ₗ[𝕜] H (i + 1)) = ⊤) →
      (∀ i, IsClosed (BGG.Γ S J i : Set (H i × Ht i)) ∧
        IsClosed (BGG.Δ S J i : Set (H i × Ht i))) ∧
      (∀ i, ∃ e : ↥(ΓL i ⊓ (ΔL i)ᗮ) ≃ₗᵢ[𝕜] Q i, ∀ y, e y = Submodule.Quotient.mk ⟨y, y.2.1⟩) ∧
      ∃ D : ∀ i, Q i →L[𝕜] Q (i + 1),
        (∀ i (x : ΓL i) (x' : ΓL (i + 1)), (x' : WithLp 2 (H (i + 1) × Ht (i + 1))).ofLp =
          BGG.twist S i (i + 1) (x : WithLp 2 (H i × Ht i)).ofLp →
            D i (Submodule.Quotient.mk x) = Submodule.Quotient.mk x') ∧
        ∀ i, [FiniteDimensional 𝕜 ((BGG.ofBounded d hd).homology (i + 1))] →
          [FiniteDimensional 𝕜 ((BGG.ofBounded dt hdt).homology (i + 1))] →
          IsClosed (Set.range (D i))) ∧
    ∀ K : ∀ i, Ht i →ₗ[𝕜] H i, (∀ i μ, s i μ = d i (K i μ) - K (i + 1) (dt i μ)) →
      (∀ i ≤ J, Function.Injective (s i)) → (∀ i, J ≤ i → Function.Surjective (s i)) →
      (∀ i < J, IsClosed (Set.range (s i))) →
      ∃ (Y : CochainComplex (ModuleCat.{v} 𝕜) ℤ)
        (e : ∀ i, Y.X i ≃ₗ[𝕜] BGG.Υ (hd := hd) (hdt := hdt) s hs J i)
        (κ : BGG.twisted (0 : BGG.ofBounded dt hdt ⟶ (BGG.ofBounded d hd)⟦(1 : ℤ)⟧) ⟶ Y),
        (∀ i < J, ∀ y, (e (i + 1) (Y.d i (i + 1) y) : H (i + 1) × Ht (i + 1)) =
          (P (i + 1) (d i (e i y : H i × Ht i).1), 0)) ∧
        (∀ y, (e (J + 1) (Y.d J (J + 1) y) : H (J + 1) × Ht (J + 1)) =
          (0, dt J (BGG.moorePenrose (s J) (d J (e J y : H J × Ht J).1)))) ∧
        (∀ i, J < i → ∀ y, (e (i + 1) (Y.d i (i + 1) y) : H (i + 1) × Ht (i + 1)) =
          (0, dt i (e i y : H i × Ht i).2)) ∧
        (∀ i ≤ J, ∀ x : H i × Ht i,
          (e i ((κ.f i).hom x) : H i × Ht i) = (P i (x.1 + K i x.2), 0)) ∧
        (∀ i, J ≤ i → ∀ x : H (i + 1) × Ht (i + 1),
          (e (i + 1) ((κ.f (i + 1)).hom x) : H (i + 1) × Ht (i + 1)) =
            (0, (s (i + 1)).ker.starProjection (dt i (BGG.moorePenrose (s i) x.1) +
              (x.2 + dt i (BGG.moorePenrose (s i) (K (i + 1) x.2)))))) ∧
        QuasiIso κ ∧ Nonempty (Y ≅ BGG.bgg S J) ∧
        ∀ i (A : Submodule 𝕜 (H i)) (At : Submodule 𝕜 (Ht i)),
          BGG.Represents (BGG.ofBounded d hd) i A → BGG.Represents (BGG.ofBounded dt hdt) i At →
            BGG.Represents Y i ((A.prod At).map (κ.f i).hom) := by
  intro S ΓL ΔL Q P
  exact ⟨fun hinj hsurj => BGG.hilbert s hs J hinj hsurj, fun K hK hinj hsurj hR =>
    BGG.orthogonal d hd dt hdt s hs K hK J hinj hsurj hR⟩

end FEEC
