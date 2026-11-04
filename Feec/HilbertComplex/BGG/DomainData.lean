module

public import Feec.HilbertComplex.BGG.Analytic
public import Feec.HilbertComplex.BGG.Orthogonal
public import Feec.HilbertComplex.BGG.SumComplex
public import Feec.HilbertComplex.BGG.Twisted

/-!
# Analytic BGG data restricted to the domains

Analytic BGG data `D : HilbertData 𝕜 c W Wt` (two Hilbert complexes and bounded connecting maps
`S` with `S D(d̃) ⊆ D(d)` and `d S = -S d̃`) restricts to the domain complexes: the domain spaces
`Vⁱ = D(dⁱ)`, `Ṽⁱ = D(d̃ⁱ)` (graph spaces), the bounded differentials and `S` form algebraic BGG
data (`HilbertData.domainData`). This is the bounded setting of [ArnoldHu2021], §3 (bounded
Hilbert complexes, e.g. the domain complexes, linked by bounded maps), so every algebraic result
of `Feec.HilbertComplex.BGG.Derived` applies: the BGG complex of the domain complexes has the
cohomology of their twisted complex (`HilbertData.domainBggHomologyIso`), and is exact when both
domain complexes are.

## Main definitions

* `Feec.BGG.HilbertData.domainS`: `S` between the domain spaces, a bounded operator.
* `Feec.BGG.HilbertData.domainData`: the bounded BGG data of the domain complexes.

## Main results

* `HilbertData.domainIncl_domainS`: `ι (S v) = S (ι v)`.
* `HilbertData.domainBggHomologyIso`, `HilbertData.domainBgg_acyclic`.
* `HilbertData.DerivedVerdict`, **`HilbertData.derivedVerdict`**: the analytic BGG theorem for
  Hilbert complexes (closed exact part, elimination hypotheses): closed range, the dimension
  bound, the Hilbert quotient norm of `Γ / Δ` (`BoundedData.derivedQuotLEquiv`), and Theorem 7
  and Corollary 1 of [ArnoldHu2021] (`Data.quasiIso_sumIso_comp`, `Data.derived_represents`).
* `HilbertData.injective_domainS`, `HilbertData.antilipschitz_domainS`: `S` one-to-one (bounded
  below) is one-to-one (bounded below) between the domains.
* `HilbertData.isClosed_Δ_and_eliminates_bgg`, `HilbertData.BGGVerdict`,
  **`HilbertData.bggVerdict`**: the analytic BGG theorem for the BGG complex `bgg J`, from the
  connecting maps up to `J` bounded below and the regular decompositions after `J`
  (`HilbertData.RegularDecomposition`; from splittings `u = dⁱ p + Sⁱ φ` in the full spaces,
  `HilbertData.regularDecomposition_of_forall_exists`), with the explicit map (30) of Theorem 7
  (`Data.quasiIso_bggSumMap`, `Data.bgg_represents`), also in its orthogonal form with the
  Moore–Penrose inverses into the output complex `R(Sⁱ⁻¹)ᗮ` / `N(Sⁱ)`
  (`BoundedData.quasiIso_orthSumMap`; the closed ranges up to `J` from `S` bounded below).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3 (bounded Hilbert complexes
  and linking maps, Theorems 6 and 7, Corollary 1), §2 (regular decompositions)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1.2 (domain complex)
* [A. Čap, K. Hu, *BGG sequences with weak regularity and applications*][CapHu2024] (BGG
  sequences of Sobolev spaces: closed range and cohomology)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

universe v

open CategoryTheory

namespace Feec.BGG.HilbertData

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W Wt : ι → Type v}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (Wt i)] [∀ i, InnerProductSpace 𝕜 (Wt i)]
  [∀ i, CompleteSpace (Wt i)] (D : HilbertData 𝕜 c W Wt)

theorem toLp_S_mem_graphL2 (i j : ι) (v : D.Ht.domainSpace i) :
    WithLp.toLp 2 (D.S i j (D.Ht.domainIncl i v),
        -D.S j (c.next j) (D.Ht.domainIncl j (D.Ht.domainD i j v))) ∈
      (D.H.d j (c.next j)).graphL2 := by
  rw [LinearPMap.mem_graphL2, WithLp.ofLp_toLp, LinearPMap.mem_graph_iff]
  exact ⟨⟨_, D.S_mapsTo i j (c.next j) (D.Ht.domainCoord i j v)⟩, rfl,
    D.anticomm i j (c.next j) (D.Ht.domainCoord i j v)⟩

/-- The connecting map `S i j` on the domains, `D(d̃ i ·) → D(d j ·)`, bounded in the graph norms
since `d S = -S d̃`. -/
def domainS (i j : ι) : D.Ht.domainSpace i →L[𝕜] D.H.domainSpace j :=
  ContinuousLinearMap.codRestrict
    ((WithLp.prodContinuousLinearEquiv 2 𝕜 (W j) (W (c.next j))).symm.toContinuousLinearMap ∘L
      ((D.S i j ∘L D.Ht.domainIncl i).prod
        (-(D.S j (c.next j) ∘L D.Ht.domainIncl j ∘L D.Ht.domainD i j))))
    _ (D.toLp_S_mem_graphL2 i j)

@[simp] theorem domainIncl_domainS (i j : ι) (v : D.Ht.domainSpace i) :
    D.H.domainIncl j (D.domainS i j v) = D.S i j (D.Ht.domainIncl i v) := rfl

/-- `S` one-to-one is one-to-one between the domains. -/
theorem injective_domainS {i j : ι} (h : Function.Injective (D.S i j)) :
    Function.Injective (D.domainS i j) := fun φ ψ hφψ =>
  D.Ht.domainIncl_injective i (h (by
    rw [← domainIncl_domainS, ← domainIncl_domainS, hφψ]))

/-- **Analytic BGG data on the domains**: the domain complexes of the two rows, with the
connecting maps on the domains. -/
def domainData : BoundedData 𝕜 c D.H.domainSpace D.Ht.domainSpace where
  d i j := D.H.domainD i j
  dt i j := D.Ht.domainD i j
  S i j := D.domainS i j
  shape_d i j h := by rw [D.H.domainD_eq_zero_of_not_rel h]; rfl
  shape_dt i j h := by rw [D.Ht.domainD_eq_zero_of_not_rel h]; rfl
  shape_S i j h := LinearMap.ext fun v => D.H.domainIncl_injective j (by
    change D.S i j _ = D.H.domainIncl j 0
    rw [D.shape_S i j h, map_zero]; rfl)
  d_comp_d := D.H.domainD_comp_domainD
  dt_comp_dt := D.Ht.domainD_comp_domainD
  anticomm i j k φ := D.H.domainIncl_injective k (by
    change D.H.d j k (D.H.domainCoord j k (D.domainS i j φ)) =
      D.H.domainIncl k (-(D.domainS j k (D.Ht.domainD i j φ)))
    rw [map_neg, domainIncl_domainS, D.Ht.domainIncl_domainD]
    exact D.anticomm i j k (D.Ht.domainCoord i j φ))
  continuous_d i j := (D.H.domainD i j).continuous
  continuous_dt i j := (D.Ht.domainD i j).continuous
  continuous_S i j := (D.domainS i j).continuous

/-- **The BGG complex of the domain complexes has the cohomology of their twisted complex**,
for analytic BGG data on `ℤ` satisfying the injectivity/surjectivity condition at `J` between
the domains. [ArnoldHu2021], §5.2 -/
def domainBggHomologyIso {W Wt : ℤ → Type v} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    [∀ i, NormedAddCommGroup (Wt i)] [∀ i, InnerProductSpace 𝕜 (Wt i)]
    [∀ i, CompleteSpace (Wt i)] (D : HilbertData 𝕜 (ComplexShape.up ℤ) W Wt) {J : ℤ}
    (h : D.domainData.InjSurj J) (i : ℤ) :
    (D.domainData.bgg J).homology i ≅ D.domainData.twistComplex.homology i :=
  Data.bggHomologyIso h i

/-- **The BGG complex of the domain complexes is exact when both domain complexes are.**
[ArnoldHu2021], §5.2 -/
theorem domainBgg_acyclic {W Wt : ℤ → Type v} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    [∀ i, NormedAddCommGroup (Wt i)] [∀ i, InnerProductSpace 𝕜 (Wt i)]
    [∀ i, CompleteSpace (Wt i)] (D : HilbertData 𝕜 (ComplexShape.up ℤ) W Wt) {J : ℤ}
    (h : D.domainData.InjSurj J) (hV : D.domainData.rowTop.Acyclic)
    (hVt : D.domainData.rowBot.Acyclic) : (D.domainData.bgg J).Acyclic :=
  Data.bgg_acyclic h hV hVt

/-- The cohomology of the top row of `domainData` is that of the top complex. -/
def domainRowTopCohomologyEquiv (i : ι) :
    D.domainData.rowTopComplex.cohomology i ≃ₗ[𝕜] D.H.cohomology i :=
  D.H.domainComplexCohomologyEquiv i

/-- The cohomology of the bottom row of `domainData` is that of the bottom complex. -/
def domainRowBotCohomologyEquiv (i : ι) :
    D.domainData.rowBotComplex.cohomology i ≃ₗ[𝕜] D.Ht.cohomology i :=
  D.Ht.domainComplexCohomologyEquiv i

variable (E F : ι → Prop) in
/-- **The analytic BGG verdict at `i`**: the derived complex of the domain complexes has closed
range at `i` and finite-dimensional cohomology, of dimension at most `dim Hⁱ(W) + dim Hⁱ(W̃)`;
the quotient norm of `Γⁱ / Δⁱ` is the Hilbert norm of `Υⁱ`, with the bounded differentials of the
quotient; and, for null-homotopic connecting maps `S = dK - Kd̃`, every cochain map from the
twisted complex to `Γ / Δ` extending the projection, composed with `(ω, μ) ↦ (ω + Kμ, μ)`, induces
an isomorphism on cohomology (Theorem 7) and carries cohomology representatives of the rows to
cohomology representatives (Corollary 1). -/
structure DerivedVerdict (i : ι) : Prop where
  closedRangeAt : (D.domainData.derivedComplex E F).ClosedRangeAt i
  finiteDimensional : FiniteDimensional 𝕜 ((D.domainData.derivedComplex E F).cohomology i)
  finrank_le : Module.finrank 𝕜 ((D.domainData.derivedComplex E F).cohomology i) ≤
    Module.finrank 𝕜 (D.H.cohomology i) + Module.finrank 𝕜 (D.Ht.cohomology i)
  /-- `Υⁱ → Γⁱ / Δⁱ`, an isometry for the quotient norm, is onto ([ArnoldHu2021], Theorem 6:
  the output complex is a Hilbert space) -/
  quotient_surjective : Function.Surjective (D.domainData.toDerivedQuotL E F i)
  /-- it carries the differential of `Υ` to the bounded differential of `Γ / Δ` -/
  quotient_d : ∀ y, D.domainData.derivedQuotD E F i (c.next i) (D.domainData.toDerivedQuotL E F i y)
    = D.domainData.toDerivedQuotL E F (c.next i) (D.domainData.derivedD E F i (c.next i) y)
  /-- [ArnoldHu2021], Theorem 7 -/
  quasiIso_sum : ∀ {K : ∀ i, D.Ht.domainSpace i →ₗ[𝕜] D.H.domainSpace i}
    (hK : D.domainData.IsNullHomotopy K)
    {r : D.domainData.twistComplex ⟶ D.domainData.derived E F},
    D.domainData.Γι E ≫ r = D.domainData.derivedπ E F → QuasiIso ((D.domainData.sumIso hK).hom ≫ r)
  /-- [ArnoldHu2021], Corollary 1 -/
  represents : ∀ {K : ∀ i, D.Ht.domainSpace i →ₗ[𝕜] D.H.domainSpace i}
    (hK : D.domainData.IsNullHomotopy K)
    {r : D.domainData.twistComplex ⟶ D.domainData.derived E F},
    D.domainData.Γι E ≫ r = D.domainData.derivedπ E F →
    ∀ {H : Submodule 𝕜 (D.H.domainSpace i)} {Ht : Submodule 𝕜 (D.Ht.domainSpace i)},
      D.domainData.rowTop.Represents i H → D.domainData.rowBot.Represents i Ht →
      (D.domainData.derived E F).Represents i
        ((H.prod Ht).map (((D.domainData.sumIso hK).hom ≫ r).f i).hom)

variable {E F : ι → Prop}
  (hΔ : ∀ i, IsClosed (D.domainData.Δ F i : Set (D.H.domainSpace i × D.Ht.domainSpace i)))
  (h : D.domainData.Eliminates E F) (i : ι) [FiniteDimensional 𝕜 (D.H.cohomology i)]
  [FiniteDimensional 𝕜 (D.Ht.cohomology i)]
include hΔ h

/-- **Analytic BGG for Hilbert complexes**: for two Hilbert complexes linked by bounded
connecting maps, the derived complex of their domain complexes is a closed Hilbert complex with
closed range and finite-dimensional cohomology, of dimension at most
`dim Hⁱ(W) + dim Hⁱ(W̃)`, at every index where the two complexes have finite-dimensional
cohomology, provided the exact part is closed and the elimination hypotheses hold.
[ArnoldHu2021], Theorem 6; [CapHu2024] -/
theorem derivedVerdict : D.DerivedVerdict E F i := by
  have := (D.domainRowTopCohomologyEquiv i).symm.finiteDimensional
  have := (D.domainRowBotCohomologyEquiv i).symm.finiteDimensional
  refine ⟨D.domainData.derivedComplex_closedRangeAt hΔ h i,
    D.domainData.finiteDimensional_derivedComplex_cohomology hΔ h i, ?_,
    D.domainData.toDerivedQuotL_surjective E hΔ i,
    D.domainData.derivedQuotD_toDerivedQuotL E hΔ i (c.next i),
    fun hK _ hr => Data.quasiIso_sumIso_comp hK h hr,
    fun hK _ hr _ _ hH hHt => Data.derived_represents hK h hr hH hHt⟩
  rw [← (D.domainRowTopCohomologyEquiv i).finrank_eq,
    ← (D.domainRowBotCohomologyEquiv i).finrank_eq]
  exact D.domainData.finrank_derivedComplex_cohomology_le hΔ h i

omit hΔ h in
/-- **`S` bounded below is bounded below between the domains**: `‖φ‖ ≤ K₁ ‖Sⁱφ‖` on `W̃ⁱ` and
`‖ψ‖ ≤ K₂ ‖Sʲψ‖` on `W̃ʲ` give `‖φ‖ ≤ max K₁ K₂ ‖Sⁱφ‖` in the graph norms, since
`d Sⁱ φ = -Sʲ d̃ φ`. -/
theorem antilipschitz_domainS {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {K₁ K₂ : NNReal}
    (h₁ : AntilipschitzWith K₁ (D.S i j)) (h₂ : AntilipschitzWith K₂ (D.S j k)) :
    AntilipschitzWith (max K₁ K₂) (D.domainS i j) := by
  obtain rfl := c.next_eq' hij
  obtain rfl := c.next_eq' hjk
  refine (D.domainS i _).antilipschitz_of_bound fun φ => ?_
  have e : D.H.d (c.next i) (c.next (c.next i)) (D.H.domainCoord _ _ (D.domainS i _ φ)) =
      -D.S (c.next i) _ (D.Ht.d i (c.next i) (D.Ht.domainCoord i _ φ)) :=
    D.anticomm i _ _ (D.Ht.domainCoord i _ φ)
  have hSφ := D.H.norm_sq_domainSpace (c.next i) (D.domainS i (c.next i) φ)
  rw [e, norm_neg, domainIncl_domainS] at hSφ
  have b₁ := ((D.S i _).bound_of_antilipschitz h₁ (D.Ht.domainIncl i φ)).trans
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 (le_max_left K₁ K₂)) (norm_nonneg _))
  have b₂ := ((D.S (c.next i) _).bound_of_antilipschitz h₂
    (D.Ht.d i (c.next i) (D.Ht.domainCoord i _ φ))).trans
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 (le_max_right K₁ K₂)) (norm_nonneg _))
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [D.Ht.norm_sq_domainSpace i φ, mul_pow, hSφ, mul_add, ← mul_pow, ← mul_pow]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) b₁ 2) (pow_le_pow_left₀ (norm_nonneg _) b₂ 2)

end Feec.BGG.HilbertData

/-! ### The BGG complex of two Hilbert complexes -/

namespace Feec.BGG.HilbertData

variable {𝕜 : Type*} [RCLike 𝕜] {W Wt : ℤ → Type v} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] [∀ i, NormedAddCommGroup (Wt i)]
  [∀ i, InnerProductSpace 𝕜 (Wt i)] [∀ i, CompleteSpace (Wt i)]
  (D : HilbertData 𝕜 (ComplexShape.up ℤ) W Wt)

/-- **The regular decompositions after `J`**: `R(dʲ⁻¹) + R(Sʲ⁻¹) = D(dʲ)` between the domains for
`j > J`, the onto-modulo-`d` hypotheses of the BGG complex `bgg J` (`Data.eliminates_bgg`). For
the `L²` de Rham complexes these are the regular decompositions of [ArnoldHu2021], §2,
Theorem 3. -/
def RegularDecomposition (J : ℤ) : Prop :=
  ∀ j, J < j → LinearMap.range (D.domainData.d (j - 1) j) ⊔
    LinearMap.range (D.domainData.S (j - 1) j) = ⊤

/-- **The regular decompositions from splittings in `L²`**: if every `u ∈ D(dⁱ⁺¹)`, `i ≥ J`, is
`dⁱ p + Sⁱ φ` with `p ∈ D(dⁱ)`, `φ ∈ D(d̃ⁱ)`, then `R(dʲ⁻¹) + R(Sʲ⁻¹) = D(dʲ)` between the
domains for `j > J`. -/
theorem regularDecomposition_of_forall_exists {J : ℤ}
    (h : ∀ i, J ≤ i → ∀ u ∈ (D.H.d (i + 1) (i + 1 + 1)).domain,
      ∃ (p : (D.H.d i (i + 1)).domain) (φ : (D.Ht.d i (i + 1)).domain),
        D.H.d i (i + 1) p + D.S i (i + 1) φ = u) :
    D.RegularDecomposition J := by
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by ring⟩
  rw [show i + 1 - 1 = i by ring]
  refine eq_top_iff.2 fun u _ => ?_
  have hnext : (ComplexShape.up ℤ).next i = i + 1 := (ComplexShape.up ℤ).next_eq' rfl
  obtain ⟨p, φ, e⟩ := h i (by omega) _
    (D.H.domain_next_le (i + 1) (i + 1 + 1) (D.H.domainIncl_mem (i + 1) u))
  have hp : (p : W i) ∈ (D.H.d i ((ComplexShape.up ℤ).next i)).domain := by
    rw [hnext]; exact p.2
  have hφ : (φ : Wt i) ∈ (D.Ht.d i ((ComplexShape.up ℤ).next i)).domain := by
    rw [hnext]; exact φ.2
  let pv : D.H.domainSpace i := LinearPMap.toGraphSpace _ ⟨_, hp⟩
  let φv : D.Ht.domainSpace i := LinearPMap.toGraphSpace _ ⟨_, hφ⟩
  have hmem := Submodule.add_mem_sup (LinearMap.mem_range_self (D.domainData.d i (i + 1)) pv)
    (LinearMap.mem_range_self (D.domainData.S i (i + 1)) φv)
  convert hmem using 1
  refine D.H.domainIncl_injective (i + 1) ?_
  rw [map_add, ← e]
  rfl

/-- `S` bounded below up to `J` is bounded below between the domains before `J`
(`antilipschitz_domainS`). -/
theorem exists_antilipschitz_domainData_S {J : ℤ}
    (hS : ∀ i ≤ J, ∃ K, AntilipschitzWith K (D.S i (i + 1))) {i : ℤ} (hi : i < J) :
    ∃ K, AntilipschitzWith K (D.domainData.S i (i + 1)) := by
  obtain ⟨K₁, h₁⟩ := hS i hi.le
  obtain ⟨K₂, h₂⟩ := hS (i + 1) (by omega)
  exact ⟨_, D.antilipschitz_domainS rfl rfl h₁ h₂⟩

/-- **The hypotheses of the analytic BGG theorem for `bgg J`**: if the connecting maps `Sⁱ`,
`i ≤ J`, are bounded below and the regular decompositions after `J` hold, the exact part of the
domain complexes is closed (`BoundedData.isClosed_bgg_Δ`, `S` bounded below between the domains
by `antilipschitz_domainS`) and the elimination hypotheses hold (`Data.eliminates_bgg`). -/
theorem isClosed_Δ_and_eliminates_bgg {J : ℤ}
    (hS : ∀ i ≤ J, ∃ K, AntilipschitzWith K (D.S i (i + 1))) (htop : D.RegularDecomposition J) :
    (∀ i, IsClosed (D.domainData.Δ (· < J) i : Set (D.H.domainSpace i × D.Ht.domainSpace i))) ∧
      D.domainData.Eliminates (J < ·) (· < J) := by
  have hS' := fun i (hi : i < J) => D.exists_antilipschitz_domainData_S hS hi
  exact ⟨D.domainData.isClosed_bgg_Δ hS',
    Data.eliminates_bgg (fun i hi => (hS' i hi).choose_spec.injective) htop⟩

/-- **The analytic BGG verdict for `bgg J` at `i`**: the analytic BGG verdict (`DerivedVerdict`)
and, for right inverses `t` of the connecting maps from `J` on (`Data.InjSurjWith`) and
null-homotopic connecting maps `S = dK - Kd̃`, the explicit cochain map (30) from the sum complex
(`Data.bggSumMap`) induces an isomorphism on cohomology (Theorem 7) and carries cohomology
representatives `H × H̃` of the rows to cohomology representatives of `bgg J` (Corollary 1); and
`Sᵏ` is one-to-one between the domains for `k ≤ J` and, where it is onto for `k ≥ J` (so that (23)
holds), the map (30) in its orthogonal form, with the Moore–Penrose inverses, into the output
complex of [ArnoldHu2021], (24)–(26) (`BoundedData.orthSumMap`), is a quasi-isomorphism. -/
structure BGGVerdict (J i : ℤ) : Prop extends D.DerivedVerdict (J < ·) (· < J) i where
  /-- [ArnoldHu2021], Theorem 7 -/
  quasiIso_bggSumMap : ∀ {t : ∀ i j, D.H.domainSpace j →ₗ[𝕜] D.Ht.domainSpace i}
    (ht : D.domainData.InjSurjWith J t) {K : ∀ i, D.Ht.domainSpace i →ₗ[𝕜] D.H.domainSpace i}
    (hK : D.domainData.IsNullHomotopy K), QuasiIso (D.domainData.bggSumMap t hK ht)
  /-- [ArnoldHu2021], Corollary 1, (31) -/
  bgg_represents : ∀ {t : ∀ i j, D.H.domainSpace j →ₗ[𝕜] D.Ht.domainSpace i}
    (ht : D.domainData.InjSurjWith J t) {K : ∀ i, D.Ht.domainSpace i →ₗ[𝕜] D.H.domainSpace i}
    (hK : D.domainData.IsNullHomotopy K)
    {H : Submodule 𝕜 (D.H.domainSpace i)} {Ht : Submodule 𝕜 (D.Ht.domainSpace i)},
    D.domainData.rowTop.Represents i H → D.domainData.rowBot.Represents i Ht →
    (D.domainData.bgg J).Represents i ((H.prod Ht).map ((D.domainData.bggSumMap t hK ht).f i).hom)
  /-- `Sᵏ` is one-to-one between the domains for `k ≤ J`, the first half of [ArnoldHu2021], (23) -/
  injective_domainData_S : ∀ k ≤ J, Function.Injective (D.domainData.S k (k + 1))
  /-- [ArnoldHu2021], Theorem 7 in its orthogonal form: where `Sᵏ` is onto between the domains
  for `k ≥ J` (the second half of (23)), the map (30) with the Moore–Penrose inverses `(Sᵏ)†`,
  into the output complex `R(Sⁱ⁻¹)ᗮ` / `N(Sⁱ)` with the differentials (26)
  (`BoundedData.orthSumMap`), is a quasi-isomorphism -/
  quasiIso_orthSumMap : ∀ (hsurj : ∀ k, J ≤ k → Function.Surjective (D.domainData.S k (k + 1)))
    {K : ∀ i, D.Ht.domainSpace i →ₗ[𝕜] D.H.domainSpace i} (hK : D.domainData.IsNullHomotopy K),
    QuasiIso (D.domainData.orthSumMap J injective_domainData_S hsurj hK)

/-- **Analytic BGG for the BGG complex of two Hilbert complexes**: if the connecting maps `Sⁱ`,
`i ≤ J`, are bounded below and the regular decompositions after `J` hold, then wherever the two
complexes have finite-dimensional cohomology the BGG complex `bgg J` of their domain complexes has
closed range and finite-dimensional cohomology of dimension at most `dim Hⁱ(W) + dim Hⁱ(W̃)`. The
exact part is closed and the other elimination hypotheses hold by `S` bounded below
(`BoundedData.isClosed_bgg_Δ`, `antilipschitz_domainS`). With right inverses of `S` from `J` on
and null-homotopic connecting maps, the explicit map (30) is a quasi-isomorphism carrying
cohomology representatives to cohomology representatives. `S` bounded below makes `Sᵏ`, `k ≤ J`,
one-to-one between the domains with closed range, so where `Sᵏ`, `k ≥ J`, is onto between the
domains, so is the orthogonal form of (30) with the Moore–Penrose inverses, into the output
complex `R(Sⁱ⁻¹)ᗮ` / `N(Sⁱ)`. [ArnoldHu2021], Theorems 6 and 7,
Corollary 1 -/
theorem bggVerdict {J : ℤ} (hS : ∀ i ≤ J, ∃ K, AntilipschitzWith K (D.S i (i + 1)))
    (htop : D.RegularDecomposition J) (i : ℤ) [FiniteDimensional 𝕜 (D.H.cohomology i)]
    [FiniteDimensional 𝕜 (D.Ht.cohomology i)] : D.BGGVerdict J i :=
  have h := D.isClosed_Δ_and_eliminates_bgg hS htop
  { D.derivedVerdict h.1 h.2 i with
    quasiIso_bggSumMap := fun ht _ hK => Data.quasiIso_bggSumMap ht hK
    bgg_represents := fun ht _ hK _ _ hH hHt => Data.bgg_represents ht hK hH hHt
    injective_domainData_S := fun k hk => (D.injective_domainS ((hS k hk).choose_spec.injective))
    quasiIso_orthSumMap := fun hsurj _ hK =>
      BoundedData.quasiIso_orthSumMap hK _ hsurj fun k hk => by
        obtain ⟨K, hK⟩ := D.exists_antilipschitz_domainData_S hS (i := k - 1) (by omega)
        rw [sub_add_cancel] at hK
        rw [LinearMap.coe_range]
        exact hK.isClosed_range (D.domainData.SL (k - 1) k).uniformContinuous }

end Feec.BGG.HilbertData
