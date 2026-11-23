module

public import Solution.Bridge
public import Solution.Cube

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

`FEEC.bggCube` from `FEEC.bggHilbert` and `FEEC.bggFinrank` themselves: the diagrams of the
challenge on the cube are `Feec`'s BGG data of forms (`Solution.Cube`), whose graph spaces form
stacked diagrams of domain complexes (`FEEC.toDomainDiagram`) with the cohomology of the rows
(`FEEC.graphHomologyEquiv`); `S` is bounded below up to `J` and the rows split from `J` on
(`Feec.FiniteElement.hessianFormData_antilipschitz`, `hessianFormData_exists_add_eq` and their
siblings, from the regular decompositions of `HΛ(Q)`), and the rows have the cohomology of a point
(`Feec.Models.Cube.FormBGG.finrank_formRow_cohomology`, `finrank_vecRow_cohomology`), so `S`
induces zero on cohomology (`Feec.BGG.Data.inducesZero_of_isZero_rowBot`,
`inducesZero_of_isZero_rowTop`) and the dimensions add (`FEEC.BGG.DomainDiagram.verdict`). The
cohomology of degree `0`: in the lowest degree of the rows `[(σ, φ)] ↦ σ` embeds `H⁰` with range
`{σ | dσ ∈ S⁰ N(d̃⁰)}` (`Feec.BGG.Data.exists_bgg_homology_lowCycles`, through
`FEEC.BGG.exists_bgg_homology_lowCycles` and `FEEC.cohomologyIs_toDomainDiagram`), the `u` with
`d u = S⁰ v` for a constant `v`: the affine functions, the rigid motions and the fields `a + b x`
(`Feec.Models.Cube.FormBGG.hessian_lowest_iff`, `elasticity_lowest_iff`, `divDiv_lowest_iff`, from
`Feec.Models.Cube.FormBGG.exists_maximal_eq_sum_dxL2_iff`: a constant weak gradient forces an
affine function on the connected cube).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], (24)–(31), Theorems 6 and 7,
  Proposition 1, Corollary 1, §4.1 and §5
* [D. Pauly, W. Zulehner, *The divDiv-complex and applications to biharmonic equations*][PaulyZulehner2020]

Bibliography: [references.bib](../../docs/references.bib)
-/

open CategoryTheory MeasureTheory
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

/-! ### The Hessian, elasticity and div–div complexes on the cube -/

/-- **The verdict of a stacked diagram of domain complexes** from the hypotheses of the main
clause of `FEEC.bggHilbert` and the cohomology of the rows, concentrated in degree `0`: closed
range by `FEEC.bggHilbert`; the dimensions by `FEEC.bggFinrank`, `S` inducing zero on cohomology
since `H⁻¹(Ṽ) = H¹(V) = 0`. -/
theorem BGG.DomainDiagram.verdict {E Et : ℤ → Type} [∀ k, NormedAddCommGroup (E k)]
    [∀ k, InnerProductSpace ℝ (E k)] [∀ k, NormedAddCommGroup (Et k)]
    [∀ k, InnerProductSpace ℝ (Et k)] {T : ∀ k, E k →ₗ.[ℝ] E (k + 1)}
    {Tt : ∀ k, Et k →ₗ.[ℝ] Et (k + 1)} {S : ∀ k, Et k →L[ℝ] E (k + 1)}
    (D : BGG.DomainDiagram T Tt S) [∀ k, CompleteSpace (graph2 (T k))]
    [∀ k, CompleteSpace (graph2 (Tt k))] {J : ℤ} {m₁ m₂ : ℕ}
    (hS : ∀ i < J, ∃ C, AntilipschitzWith C (D.s i))
    (hsurj : ∀ i, J ≤ i → LinearMap.range (D.d i : graph2 (T i) →ₗ[ℝ] graph2 (T (i + 1))) ⊔
      LinearMap.range (D.s i : graph2 (Tt i) →ₗ[ℝ] graph2 (T (i + 1))) = ⊤)
    [∀ i, FiniteDimensional ℝ ((BGG.ofBounded D.d D.d_d).homology i)]
    [∀ i, FiniteDimensional ℝ ((BGG.ofBounded D.dt D.dt_dt).homology i)]
    (hV : ∀ i, Module.finrank ℝ ((BGG.ofBounded D.d D.d_d).homology i) = if i = 0 then m₁ else 0)
    (hVt : ∀ i, Module.finrank ℝ ((BGG.ofBounded D.dt D.dt_dt).homology i) =
      if i = 0 then m₂ else 0) :
    D.Verdict J (m₁ + m₂) := by
  obtain ⟨-, -, D', hD', hcl⟩ := (bggHilbert D.d D.d_d D.dt D.dt_dt D.s D.d_s J).1 hS hsurj
  have hinj : ∀ i < J, Function.Injective (D.toHom.f i) := fun i hi =>
    (hS i hi).choose_spec.injective
  have hsurj' : ∀ i, J ≤ i → LinearMap.range ((BGG.ofBounded D.d D.d_d).d i (i + 1)).hom ⊔
      LinearMap.range (BGG.conn D.toHom i (i + 1)) = ⊤ := fun i hi => by
    rw [BGG.conn_ofBoundedHom, BGG.ofBounded_d_succ]
    exact hsurj i hi
  have hzV : ∀ i ≠ 0, Limits.IsZero ((BGG.ofBounded D.d D.d_d).homology i) := fun i hi =>
    @ModuleCat.isZero_of_subsingleton _ _ _
      (Module.finrank_zero_iff.1 ((hV i).trans (ite_eq_right hi)))
  have hzVt : ∀ i ≠ 0, Limits.IsZero ((BGG.ofBounded D.dt D.dt_dt).homology i) := fun i hi =>
    @ModuleCat.isZero_of_subsingleton _ _ _
      (Module.finrank_zero_iff.1 ((hVt i).trans (ite_eq_right hi)))
  refine ⟨hS, hsurj, ⟨D', hD', fun i => hcl i⟩, fun i => (bggFinrank D.toHom J hinj hsurj' i).1,
    fun i => ?_⟩
  obtain ⟨-, hle, heq⟩ := bggFinrank D.toHom J hinj hsurj' i
  by_cases hi : i = 0
  · subst hi
    rw [ite_eq_left rfl, heq.2 ⟨?_, ?_⟩, hV, hVt, ite_eq_left rfl, ite_eq_left rfl]
    · rw [BGG.inducesZero_iff (sub_add_cancel 0 1)]
      exact (BGG.toData D.toHom).inducesZero_of_isZero_rowBot (sub_add_cancel 0 1)
        (hzVt _ (by norm_num))
    · rw [BGG.inducesZero_iff rfl]
      exact (BGG.toData D.toHom).inducesZero_of_isZero_rowTop rfl (hzV _ (by norm_num))
  · rw [hV, hVt, ite_eq_right hi, ite_eq_right hi] at hle
    rw [ite_eq_right hi]
    omega

/-- The verdict and the cohomology of degree `0` of the diagram of the challenge from those of
`Feec`'s diagram it is. -/
theorem BGG.exists_verdict_of_eq {E Et : ℤ → Type} [∀ k, NormedAddCommGroup (E k)]
    [∀ k, InnerProductSpace ℝ (E k)] [∀ k, CompleteSpace (E k)] [∀ k, NormedAddCommGroup (Et k)]
    [∀ k, InnerProductSpace ℝ (Et k)] [∀ k, CompleteSpace (Et k)]
    (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et) {T : ∀ k, E k →ₗ.[ℝ] E (k + 1)}
    {Tt : ∀ k, Et k →ₗ.[ℝ] Et (k + 1)} {S : ∀ k, Et k →L[ℝ] E (k + 1)}
    (hT : ∀ k, D.H.d k (k + 1) = T k) (hTt : ∀ k, D.Ht.d k (k + 1) = Tt k)
    (hS : ∀ k, D.S k (k + 1) = S k) {J : ℤ} {m : ℕ} {P : Set (E 0)}
    (h : (toDomainDiagram D).Verdict J m) (h0 : (toDomainDiagram D).CohomologyIs J 0 P) :
    ∃ D' : BGG.DomainDiagram T Tt S, D'.Verdict J m ∧ D'.CohomologyIs J 0 P := by
  obtain rfl : T = fun k => D.H.d k (k + 1) := funext fun k => (hT k).symm
  obtain rfl : Tt = fun k => D.Ht.d k (k + 1) := funext fun k => (hTt k).symm
  obtain rfl : S = fun k => D.S k (k + 1) := funext fun k => (hS k).symm
  exact ⟨_, h, h0⟩

/-- **The verdict of the domain complexes of `Feec`'s analytic BGG data** from `S` bounded below
up to `J`, the `L²` splittings from `J` on and rows with the cohomology of a point. -/
theorem BGG.verdict_toDomainDiagram {E Et : ℤ → Type} [∀ k, NormedAddCommGroup (E k)]
    [∀ k, InnerProductSpace ℝ (E k)] [∀ k, CompleteSpace (E k)] [∀ k, NormedAddCommGroup (Et k)]
    [∀ k, InnerProductSpace ℝ (Et k)] [∀ k, CompleteSpace (Et k)]
    (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et) {J : ℤ} {m₁ m₂ : ℕ}
    (hS : ∀ i ≤ J, ∃ K, AntilipschitzWith K (D.S i (i + 1)))
    (hsplit : ∀ i, J ≤ i → ∀ u ∈ (D.H.d (i + 1) (i + 1 + 1)).domain,
      ∃ (p : (D.H.d i (i + 1)).domain) (φ : (D.Ht.d i (i + 1)).domain),
        D.H.d i (i + 1) p + D.S i (i + 1) φ = u)
    [∀ i, FiniteDimensional ℝ (D.H.cohomology i)] [∀ i, FiniteDimensional ℝ (D.Ht.cohomology i)]
    (hV : ∀ i, Module.finrank ℝ (D.H.cohomology i) = if i = 0 then m₁ else 0)
    (hVt : ∀ i, Module.finrank ℝ (D.Ht.cohomology i) = if i = 0 then m₂ else 0) :
    (toDomainDiagram D).Verdict J (m₁ + m₂) := by
  have : ∀ k, CompleteSpace (graph2 (D.H.d k (k + 1))) := fun k =>
    (D.H.closed k (k + 1)).completeSpace_graphSpace
  have : ∀ k, CompleteSpace (graph2 (D.Ht.d k (k + 1))) := fun k =>
    (D.Ht.closed k (k + 1)).completeSpace_graphSpace
  have : ∀ i, FiniteDimensional ℝ ((BGG.ofBounded (toDomainDiagram D).d
      (toDomainDiagram D).d_d).homology i) := fun i =>
    (graphHomologyEquiv D.H i).finiteDimensional
  have : ∀ i, FiniteDimensional ℝ ((BGG.ofBounded (toDomainDiagram D).dt
      (toDomainDiagram D).dt_dt).homology i) := fun i =>
    (graphHomologyEquiv D.Ht i).finiteDimensional
  refine (toDomainDiagram D).verdict (fun i hi => ?_) (fun i hi => sup_range_eq_top_of_exists D
    (hsplit i hi)) (fun i => (graphHomologyEquiv D.H i).symm.finrank_eq.trans (hV i))
    (fun i => (graphHomologyEquiv D.Ht i).symm.finrank_eq.trans (hVt i))
  obtain ⟨K₁, h₁⟩ := hS i hi.le
  obtain ⟨K₂, h₂⟩ := hS (i + 1) (by omega)
  exact ⟨_, antilipschitz_graphS D h₁ h₂⟩

open Feec.FiniteElement Feec.Models.Cube.FormBGG in
/-- **The Hessian complex on the cube.** -/
theorem BGG.hessianCube :
    ∃ D : BGG.DomainDiagram (dMax (cube 3)) (fun k => vecOp fun _ : Fin 3 => dMax (cube 3) k)
      (wedge (cube 3)), D.Verdict 0 4 ∧ D.CohomologyIs 0 0 {u | ∃ (a : ℝ) (b : Fin 3 → ℝ),
        ∀ s, ⇑(u s) =ᵐ[volume.restrict (cube 3)] fun x => a + b ⬝ᵥ x} := by
  have hΩ := Feec.Models.Cube.FEM.isOpen_cubeDomain 3
  have : ∀ k, FiniteDimensional ℝ ((hessianFormData hΩ).H.cohomology k) :=
    finiteDimensional_formRow_cohomology
  have : ∀ k, FiniteDimensional ℝ ((hessianFormData hΩ).Ht.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow 3 hΩ).cohomology k))
  have := LocalElement.subsingleton_L2F_of_neg (Feec.Models.Cube.FEM.cubeDomain 3) (n := 3)
    (j := 0 - 1) (by norm_num)
  have := subsingleton_vec_formIdx (Ω := Feec.Models.Cube.FEM.cubeDomain 3) (n := 3) (k := 0 - 1)
    (by norm_num)
  have h0 := cohomologyIs_toDomainDiagram (hessianFormData hΩ) (i := 0) (J := 0) le_rfl
    (fun _ => ((hessianFormData_antilipschitz hΩ) 0 le_rfl).choose_spec.injective)
    (fun h => absurd h (by norm_num))
  refine BGG.exists_verdict_of_eq (hessianFormData hΩ) dMax_cube_eq vecOp_cube_eq
    (fun k => (hessianFormData_S hΩ k).trans (wedge_eq _ k).symm)
    (BGG.verdict_toDomainDiagram (m₁ := 1) (m₂ := 3) _ (hessianFormData_antilipschitz hΩ)
      (fun i hi u hu => hessianFormData_exists_add_eq hΩ deRham_hasRegularDecomposition_cube hi hu)
      finrank_formRow_cohomology finrank_vecRow_cohomology) ?_
  obtain ⟨f, hf, hr, hc⟩ := h0
  refine ⟨f, hf, hr.trans ?_, hc⟩
  ext u
  simp only [Set.mem_ofPred_eq, hessianFormData_S]
  exact hessian_lowest_iff u

open Feec.FiniteElement Feec.Models.Cube.FormBGG in
/-- **The div–div complex on the cube.** -/
theorem BGG.divDivCube :
    ∃ D : BGG.DomainDiagram (fun k => vecOp fun _ : Fin 3 => dMax (cube 3) k) (dMax (cube 3))
      (dxVec (cube 3)), D.Verdict 2 4 ∧ D.CohomologyIs 2 0 {u | ∃ (a : Fin 3 → ℝ) (b : ℝ),
        ∀ c s, ⇑(u c s) =ᵐ[volume.restrict (cube 3)] fun x => a c + b * x c} := by
  have hΩ := Feec.Models.Cube.FEM.isOpen_cubeDomain 3
  have : ∀ k, FiniteDimensional ℝ ((divDivFormData hΩ).Ht.cohomology k) :=
    finiteDimensional_formRow_cohomology
  have : ∀ k, FiniteDimensional ℝ ((divDivFormData hΩ).H.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow 3 hΩ).cohomology k))
  have := LocalElement.subsingleton_L2F_of_neg (Feec.Models.Cube.FEM.cubeDomain 3) (n := 3)
    (j := 0 - 1) (by norm_num)
  have := subsingleton_vec_formIdx (Ω := Feec.Models.Cube.FEM.cubeDomain 3) (n := 3) (k := 0 - 1)
    (by norm_num)
  have hS := divDivFormData_antilipschitz hΩ
  have h0 := cohomologyIs_toDomainDiagram (divDivFormData hΩ) (i := 0) (J := 2) (by norm_num)
    (fun h => absurd h (by norm_num)) (fun _ => (hS (0 + 1) (by norm_num)).choose_spec.injective)
  refine BGG.exists_verdict_of_eq (divDivFormData hΩ) vecOp_cube_eq dMax_cube_eq
    (fun k => (divDivFormData_S hΩ k).trans (dxVec_eq _ k).symm)
    (BGG.verdict_toDomainDiagram (J := 2) (m₁ := 3) (m₂ := 1) _ (divDivFormData_antilipschitz hΩ)
      (fun i hi u hu => divDivFormData_exists_add_eq hΩ
        (deRham_hasRegularDecomposition_cube.mono (by norm_num)) hi hu)
      finrank_vecRow_cohomology finrank_formRow_cohomology) ?_
  obtain ⟨f, hf, hr, hc⟩ := h0
  refine ⟨f, hf, hr.trans ?_, hc⟩
  ext u
  simp only [Set.mem_ofPred_eq, divDivFormData_S]
  exact divDiv_lowest_iff u

open scoped Matrix in
open Feec.FiniteElement Feec.Models.Cube.FormBGG in
/-- **The elasticity complex on the cube.** -/
theorem BGG.elasticityCube :
    ∃ D : BGG.DomainDiagram (fun k => vecOp fun _ : Fin 3 => dMax (cube 3) k)
      (fun k => vecOp fun _ : Fin 3 => dMax (cube 3) k) (crossWedge (cube 3)),
      D.Verdict 1 6 ∧ D.CohomologyIs 1 0 {u | ∃ a b : Fin 3 → ℝ,
        ∀ c s, ⇑(u c s) =ᵐ[volume.restrict (cube 3)] fun x => a c + (b ⨯₃ x) c} := by
  have hΩ := Feec.Models.Cube.FEM.isOpen_cubeDomain 3
  have : ∀ k, FiniteDimensional ℝ ((elasticityFormData hΩ).H.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow 3 hΩ).cohomology k))
  have : ∀ k, FiniteDimensional ℝ ((elasticityFormData hΩ).Ht.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow 3 hΩ).cohomology k))
  have := subsingleton_vec_formIdx (Ω := Feec.Models.Cube.FEM.cubeDomain 3) (n := 3) (k := 0 - 1)
    (by norm_num)
  have h0 := cohomologyIs_toDomainDiagram (elasticityFormData hΩ) (i := 0) (J := 1) zero_le_one
    (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
  refine BGG.exists_verdict_of_eq (elasticityFormData hΩ) vecOp_cube_eq vecOp_cube_eq
    (fun k => (elasticityFormData_S hΩ k).trans (crossWedge_eq _ k).symm)
    (BGG.verdict_toDomainDiagram (J := 1) (m₁ := 3) (m₂ := 3) _
      (elasticityFormData_antilipschitz hΩ)
      (fun i hi u hu => elasticityFormData_exists_add_eq hΩ
        (deRham_hasRegularDecomposition_cube.mono zero_le_one) hi hu)
      finrank_vecRow_cohomology finrank_vecRow_cohomology) ?_
  obtain ⟨f, hf, hr, hc⟩ := h0
  refine ⟨f, hf, hr.trans ?_, hc⟩
  ext u
  simp only [Set.mem_ofPred_eq, elasticityFormData_S]
  exact elasticity_lowest_iff u

open scoped Matrix in
/-- **The Hessian, elasticity and div–div complexes on the cube** ([ArnoldHu2021], §4.1 and
Theorem 6; [PaulyZulehner2020]). On `Q = (0, ½)³`, with `HΛ(Q)` the `L²` de Rham complex of the
weak exterior derivative `dMax` on `L²(Q; Λ)` and `HΛ(Q) ⊗ ℝ³` its copy `vecOp` on vectors of
forms, the diagrams

* of the **Hessian** complex: `HΛ(Q)` over `HΛ(Q) ⊗ ℝ³` linked by `S v = Σₐ dxₐ ∧ vₐ` (`wedge`),
  at `J = 0`;
* of the **elasticity** complex: `HΛ(Q) ⊗ ℝ³` over itself linked by `crossWedge`, at `J = 1`;
* of the **div–div** complex: `HΛ(Q) ⊗ ℝ³` over `HΛ(Q)` linked by `dxVec`, at `J = 2`,

have stacked diagrams of their domain complexes (`BGG.DomainDiagram`) that satisfy the hypotheses
of the main clause of `FEEC.bggHilbert`: `sⁱ` bounded below before `J`, and onto modulo `d` from
`J` on (the regular decompositions of [ArnoldHu2021], §2, Theorem 3, on `Q`). So their BGG
complexes are bounded Hilbert complexes (by `FEEC.bggHilbert`), with closed range in every degree,
and their cohomology is finite-dimensional, of dimension `4`, `6` and `4` in degree `0` and `0` in
the other degrees (`BGG.DomainDiagram.Verdict`): the rows have the cohomology of a point, so `S`
induces zero on cohomology and the dimensions of the cohomology of the rows add
(`FEEC.bggFinrank`). **The cohomology in degree `0`** is the space of the affine functions
`a + b ⬝ᵥ x`, of the rigid motions `a + b ⨯₃ x`, resp. of the fields `a + b x` on `Q` (`0`-forms,
resp. vectors of `0`-forms, in `L²(Q)`): `[(σ, φ)] ↦ u`, `σ = (u, du)`, is a linear isomorphism of
`H⁰` onto that space (`BGG.DomainDiagram.CohomologyIs`). In vector proxies these BGG complexes are
the `L²` Hessian complex `H²(Q) → H(curl; Q; 𝕊) → H(div; Q; 𝕋) → L²(Q; ℝ³)` and the `L²`
elasticity and div–div complexes of [ArnoldHu2021], §4.1 (away from `J` by `BGG.Identification`;
in degree `J`, `sᴶ` being injective, `Γᴶ / Δᴶ ≅ {σ ∈ Vᴶ | dσ ∈ R(sᴶ)} / R(sᴶ⁻¹)`, e.g. `H²(Q)`);
this identification of the complexes is not part of the statement. -/
theorem bggCube :
    (∃ D : BGG.DomainDiagram (dMax (cube 3)) (fun k => vecOp fun _ : Fin 3 => dMax (cube 3) k)
      (wedge (cube 3)), D.Verdict 0 4 ∧ D.CohomologyIs 0 0 {u | ∃ (a : ℝ) (b : Fin 3 → ℝ),
        ∀ s, ⇑(u s) =ᵐ[volume.restrict (cube 3)] fun x => a + b ⬝ᵥ x}) ∧
    (∃ D : BGG.DomainDiagram (fun k => vecOp fun _ : Fin 3 => dMax (cube 3) k)
      (fun k => vecOp fun _ : Fin 3 => dMax (cube 3) k) (crossWedge (cube 3)),
      D.Verdict 1 6 ∧ D.CohomologyIs 1 0 {u | ∃ a b : Fin 3 → ℝ,
        ∀ c s, ⇑(u c s) =ᵐ[volume.restrict (cube 3)] fun x => a c + (b ⨯₃ x) c}) ∧
    ∃ D : BGG.DomainDiagram (fun k => vecOp fun _ : Fin 3 => dMax (cube 3) k) (dMax (cube 3))
      (dxVec (cube 3)), D.Verdict 2 4 ∧ D.CohomologyIs 2 0 {u | ∃ (a : Fin 3 → ℝ) (b : ℝ),
        ∀ c s, ⇑(u c s) =ᵐ[volume.restrict (cube 3)] fun x => a c + b * x c} :=
  ⟨BGG.hessianCube, BGG.elasticityCube, BGG.divDivCube⟩

end FEEC
