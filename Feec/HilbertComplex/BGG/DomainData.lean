module

public import Feec.HilbertComplex.BGG.Analytic
public import Feec.HilbertComplex.BGG.Orthogonal
public import Feec.HilbertComplex.BGG.SumComplex
public import Feec.HilbertComplex.BGG.Twisted

/-!
# Analytic BGG data restricted to the domains

Two Hilbert complexes linked by bounded connecting maps restrict to bounded BGG data on their
domain complexes. Where the two complexes have finite-dimensional cohomology, the derived complex
(closed exact part, elimination hypotheses) and `bgg J` (`Sⁱ`, `i ≤ J`, bounded below, regular
decompositions after `J`) have closed range and finite-dimensional cohomology
([ArnoldHu2021], Theorems 6 and 7; [CapHu2024]).

## Main results

* `HilbertData.derivedVerdict`: the analytic BGG theorem for the derived complex.
* `HilbertData.bggVerdict`: the analytic BGG theorem for `bgg J`.
* `HilbertData.homologyIs_lowest`: the cohomology of `bgg J` in the lowest degree of the rows.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §2, §3
* [A. Čap, K. Hu, *BGG sequences with weak regularity and applications*][CapHu2024]

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

/-- The connecting map `S i j` on the domains, `D(d̃ i ·) → D(d j ·)`. -/
def domainS (i j : ι) : D.Ht.domainSpace i →L[𝕜] D.H.domainSpace j :=
  ContinuousLinearMap.codRestrict
    ((WithLp.prodContinuousLinearEquiv 2 𝕜 (W j) (W (c.next j))).symm.toContinuousLinearMap ∘L
      ((D.S i j ∘L D.Ht.domainIncl i).prod
        (-(D.S j (c.next j) ∘L D.Ht.domainIncl j ∘L D.Ht.domainD i j))))
    _ (D.toLp_S_mem_graphL2 i j)

@[simp] theorem domainIncl_domainS (i j : ι) (v : D.Ht.domainSpace i) :
    D.H.domainIncl j (D.domainS i j v) = D.S i j (D.Ht.domainIncl i v) := rfl

theorem injective_domainS {i j : ι} (h : Function.Injective (D.S i j)) :
    Function.Injective (D.domainS i j) := fun φ ψ hφψ =>
  D.Ht.domainIncl_injective i (h (by
    rw [← domainIncl_domainS, ← domainIncl_domainS, hφψ]))

theorem exists_forall_S_ne {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k)
    (hS : Function.Injective (D.S i j))
    (h : ∀ C : ℝ, ∃ φ : (D.Ht.d i j).domain,
      D.H.d j k ⟨_, D.S_mapsTo i j k φ⟩ = 0 ∧ C * ‖(φ : Wt i)‖ < ‖D.Ht.d i j φ‖) :
    ∃ u ∈ (D.H.d j k).domain, ∀ φ ∈ (D.Ht.d i j).domain, D.S i j φ ≠ u := by
  obtain rfl := c.next_eq' hij
  obtain rfl := c.next_eq' hjk
  by_contra! hsurj
  have hs : Function.Surjective (D.domainS i (c.next i)) := fun w => by
    obtain ⟨φ, hφ, hφu⟩ := hsurj (D.H.domainIncl _ w) (D.H.domainIncl_mem _ w)
    exact ⟨(D.Ht.d i (c.next i)).toGraphSpace ⟨φ, hφ⟩, D.H.domainIncl_injective _ hφu⟩
  obtain ⟨K, hK⟩ := (D.domainS i (c.next i)).antilipschitz_of_injective_of_isClosed_range
    (D.injective_domainS hS) (by rw [hs.range_eq]; exact isClosed_univ)
  obtain ⟨φ, hdφ, hlt⟩ := h (K * ‖D.S i (c.next i)‖)
  set v := (D.Ht.d i (c.next i)).toGraphSpace φ
  have h1 : ‖D.Ht.d i (c.next i) φ‖ ≤ ‖v‖ := D.Ht.norm_d_domainCoord_le i (c.next i) v
  have h2 : ‖v‖ ≤ K * ‖D.domainS i (c.next i) v‖ :=
    ContinuousLinearMap.bound_of_antilipschitz _ hK v
  have h3 : ‖D.domainS i (c.next i) v‖ = ‖D.S i (c.next i) φ‖ := by
    have e := D.H.norm_sq_domainSpace (c.next i) (D.domainS i (c.next i) v)
    have e0 : D.H.d (c.next i) (c.next (c.next i))
        (D.H.domainCoord (c.next i) _ (D.domainS i (c.next i) v)) = 0 := hdφ
    rw [e0, norm_zero, zero_pow two_ne_zero, add_zero, domainIncl_domainS] at e
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e
  have h4 : ‖D.S i (c.next i) φ‖ ≤ ‖D.S i (c.next i)‖ * ‖(φ : Wt i)‖ :=
    (D.S i (c.next i)).le_opNorm _
  have hK0 : (0 : ℝ) ≤ K := K.2
  nlinarith [mul_le_mul_of_nonneg_left h4 hK0]

/-- If `S i j` is one-to-one and `d̃` is unbounded on the `φ` with `d S φ = 0`, then `domainS i j`
is not surjective. -/
theorem not_surjective_domainS {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k)
    (hS : Function.Injective (D.S i j))
    (h : ∀ C : ℝ, ∃ φ : (D.Ht.d i j).domain,
      D.H.d j k ⟨_, D.S_mapsTo i j k φ⟩ = 0 ∧ C * ‖(φ : Wt i)‖ < ‖D.Ht.d i j φ‖) :
    ¬ Function.Surjective (D.domainS i j) := fun hs => by
  obtain ⟨u, hu, hne⟩ := D.exists_forall_S_ne hij hjk hS h
  obtain rfl := c.next_eq' hij
  obtain rfl := c.next_eq' hjk
  obtain ⟨v, hv⟩ := hs ((D.H.d (c.next i) (c.next (c.next i))).toGraphSpace ⟨u, hu⟩)
  exact hne _ (D.Ht.domainIncl_mem i v) (by rw [← domainIncl_domainS, hv]; rfl)

/-- The bounded BGG data of the domain complexes of the two rows. -/
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

/-- Under `InjSurj J` between the domains, `bgg J` has the cohomology of the twisted complex. -/
def domainBggHomologyIso {W Wt : ℤ → Type v} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    [∀ i, NormedAddCommGroup (Wt i)] [∀ i, InnerProductSpace 𝕜 (Wt i)]
    [∀ i, CompleteSpace (Wt i)] (D : HilbertData 𝕜 (ComplexShape.up ℤ) W Wt) {J : ℤ}
    (h : D.domainData.InjSurj J) (i : ℤ) :
    (D.domainData.bgg J).homology i ≅ D.domainData.twistComplex.homology i :=
  Data.bggHomologyIso h i

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

/-- The homology of the top row of `domainData` is the cohomology of the top complex. -/
def domainRowTopHomologyEquiv (i : ι) :
    D.domainData.rowTop.homology i ≃ₗ[𝕜] D.H.cohomology i :=
  (D.domainData.rowTopCohomologyEquiv i).symm.trans (D.domainRowTopCohomologyEquiv i)

/-- The homology of the bottom row of `domainData` is the cohomology of the bottom complex. -/
def domainRowBotHomologyEquiv (i : ι) :
    D.domainData.rowBot.homology i ≃ₗ[𝕜] D.Ht.cohomology i :=
  (D.domainData.rowBotCohomologyEquiv i).symm.trans (D.domainRowBotCohomologyEquiv i)

variable (E F : ι → Prop) in
/-- The conclusions of the analytic BGG theorem for the derived complex at `i`. -/
structure DerivedVerdict (i : ι) : Prop where
  closedRangeAt : (D.domainData.derivedComplex E F).ClosedRangeAt i
  finiteDimensional : FiniteDimensional 𝕜 ((D.domainData.derivedComplex E F).cohomology i)
  finrank_le : Module.finrank 𝕜 ((D.domainData.derivedComplex E F).cohomology i) ≤
    Module.finrank 𝕜 (D.H.cohomology i) + Module.finrank 𝕜 (D.Ht.cohomology i)
  /-- `Υⁱ → Γⁱ / Δⁱ` is onto -/
  quotient_surjective : Function.Surjective (D.domainData.toDerivedQuotL E F i)
  /-- it intertwines the differentials -/
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

/-- With closed exact part and the elimination hypotheses, the derived complex of the domain
complexes satisfies `DerivedVerdict` where both complexes have finite-dimensional cohomology. -/
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

/-- The regular decompositions `R(dʲ⁻¹) + R(Sʲ⁻¹) = D(dʲ)` between the domains for `j > J`. -/
def RegularDecomposition (J : ℤ) : Prop :=
  ∀ j, J < j → LinearMap.range (D.domainData.d (j - 1) j) ⊔
    LinearMap.range (D.domainData.S (j - 1) j) = ⊤

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

theorem exists_antilipschitz_domainData_S {J : ℤ}
    (hS : ∀ i ≤ J, ∃ K, AntilipschitzWith K (D.S i (i + 1))) {i : ℤ} (hi : i < J) :
    ∃ K, AntilipschitzWith K (D.domainData.S i (i + 1)) := by
  obtain ⟨K₁, h₁⟩ := hS i hi.le
  obtain ⟨K₂, h₂⟩ := hS (i + 1) (by omega)
  exact ⟨_, D.antilipschitz_domainS rfl rfl h₁ h₂⟩

theorem isClosed_Δ_and_eliminates_bgg {J : ℤ}
    (hS : ∀ i ≤ J, ∃ K, AntilipschitzWith K (D.S i (i + 1))) (htop : D.RegularDecomposition J) :
    (∀ i, IsClosed (D.domainData.Δ (· < J) i : Set (D.H.domainSpace i × D.Ht.domainSpace i))) ∧
      D.domainData.Eliminates (J < ·) (· < J) := by
  have hS' := fun i (hi : i < J) => D.exists_antilipschitz_domainData_S hS hi
  exact ⟨D.domainData.isClosed_bgg_Δ hS',
    Data.eliminates_bgg (fun i hi => (hS' i hi).choose_spec.injective) htop⟩

/-- The conclusions of the analytic BGG theorem for `bgg J` at `i`. -/
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
  /-- `Sᵏ` is one-to-one between the domains for `k ≤ J` -/
  injective_domainData_S : ∀ k ≤ J, Function.Injective (D.domainData.S k (k + 1))
  /-- [ArnoldHu2021], Theorem 7, with the Moore–Penrose inverses -/
  quasiIso_orthSumMap : ∀ (hsurj : ∀ k, J ≤ k → Function.Surjective (D.domainData.S k (k + 1)))
    {K : ∀ i, D.Ht.domainSpace i →ₗ[𝕜] D.H.domainSpace i} (hK : D.domainData.IsNullHomotopy K),
    QuasiIso (D.domainData.orthSumMap J injective_domainData_S hsurj hK)

/-- If the `Sⁱ`, `i ≤ J`, are bounded below and the regular decompositions after `J` hold, `bgg J`
satisfies `BGGVerdict` where both complexes have finite-dimensional cohomology. -/
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

/-- Under the hypotheses of `bggVerdict` in every degree, if `Hⁱ(W̃) = 0` or `Hⁱ⁺¹(W) = 0` for all
`i`, then `dim Hⁱ(bgg J) = dim Hⁱ(W) + dim Hⁱ(W̃)`. [ArnoldHu2021], Theorem 6, (27) -/
theorem finrank_bgg_homology_eq_add {J : ℤ}
    (hS : ∀ i ≤ J, ∃ K, AntilipschitzWith K (D.S i (i + 1))) (htop : D.RegularDecomposition J)
    [∀ i, FiniteDimensional 𝕜 (D.H.cohomology i)] [∀ i, FiniteDimensional 𝕜 (D.Ht.cohomology i)]
    (hzero : ∀ i, Subsingleton (D.Ht.cohomology i) ∨ Subsingleton (D.H.cohomology (i + 1)))
    (i : ℤ) :
    Module.finrank 𝕜 ((D.domainData.bgg J).homology i) =
      Module.finrank 𝕜 (D.H.cohomology i) + Module.finrank 𝕜 (D.Ht.cohomology i) := by
  have : ∀ i, FiniteDimensional 𝕜 (D.domainData.rowTop.homology i) := fun i =>
    (D.domainRowTopHomologyEquiv i).symm.finiteDimensional
  have : ∀ i, FiniteDimensional 𝕜 (D.domainData.rowBot.homology i) := fun i =>
    (D.domainRowBotHomologyEquiv i).symm.finiteDimensional
  have hz : ∀ k, Limits.IsZero (D.domainData.rowBot.homology k) ∨
      Limits.IsZero (D.domainData.rowTop.homology (k + 1)) := fun k =>
    (hzero k).imp
      (fun h => @ModuleCat.isZero_of_subsingleton _ _ _
        (@Equiv.subsingleton _ _ (D.domainRowBotHomologyEquiv k).toEquiv h))
      fun h => @ModuleCat.isZero_of_subsingleton _ _ _
        (@Equiv.subsingleton _ _ (D.domainRowTopHomologyEquiv (k + 1)).toEquiv h)
  have h₁ := hz (i - 1)
  rw [sub_add_cancel] at h₁
  rw [Data.finrank_derived_homology_eq_add (sub_add_cancel i 1) rfl
      (D.isClosed_Δ_and_eliminates_bgg hS htop).2 h₁ (hz i),
    (D.domainRowTopHomologyEquiv i).finrank_eq, (D.domainRowBotHomologyEquiv i).finrank_eq]

theorem finrank_bgg_homology_eq_ite {J : ℤ}
    (hS : ∀ i ≤ J, ∃ K, AntilipschitzWith K (D.S i (i + 1))) (htop : D.RegularDecomposition J)
    [∀ i, FiniteDimensional 𝕜 (D.H.cohomology i)] [∀ i, FiniteDimensional 𝕜 (D.Ht.cohomology i)]
    {m m' : ℕ} (hV : ∀ i, Module.finrank 𝕜 (D.H.cohomology i) = if i = 0 then m else 0)
    (hVt : ∀ i, Module.finrank 𝕜 (D.Ht.cohomology i) = if i = 0 then m' else 0) (i : ℤ) :
    Module.finrank 𝕜 ((D.domainData.bgg J).homology i) = if i = 0 then m + m' else 0 := by
  have hzero : ∀ k, Subsingleton (D.Ht.cohomology k) ∨ Subsingleton (D.H.cohomology (k + 1)) :=
    fun k => by
      by_cases hk : k = 0
      · exact Or.inr (Module.finrank_zero_iff.1 ((hV (k + 1)).trans (ite_eq_right (by omega))))
      · exact Or.inl (Module.finrank_zero_iff.1 ((hVt k).trans (ite_eq_right hk)))
  rw [D.finrank_bgg_homology_eq_add hS htop hzero i, hV, hVt]
  split_ifs <;> rfl

/-! ### The cohomology in the lowest degree of the rows -/

theorem _root_.Feec.HilbertComplex.exists_domainIncl_eq_of_mem
    (H : Feec.HilbertComplex 𝕜 (ComplexShape.up ℤ) W) {i : ℤ} {u : W i}
    (hu : u ∈ (H.d i (i + 1)).domain) : ∃ σ : H.domainSpace i, H.domainIncl i σ = u :=
  ⟨(H.d i ((ComplexShape.up ℤ).next i)).toGraphSpace ⟨u, by rwa [CochainComplex.next]⟩, rfl⟩

theorem mem_domainData_lowCycles {i : ℤ} {σ : D.H.domainSpace i} :
    σ ∈ D.domainData.lowCycles i ↔ ∃ v ∈ (D.Ht.d i (i + 1)).ker,
      D.S i (i + 1) v = D.H.d i (i + 1) (D.H.domainCoord i (i + 1) σ) := by
  rw [Data.mem_lowCycles]
  constructor
  · rintro ⟨φ, hφ, hS⟩
    refine ⟨D.Ht.domainIncl i φ, LinearPMap.mem_ker_iff.2 ⟨D.Ht.domainCoord i (i + 1) φ, rfl, ?_⟩,
      ?_⟩
    · rw [← D.Ht.domainIncl_domainD]
      change D.Ht.domainIncl (i + 1) (D.domainData.dt i (i + 1) φ) = 0
      rw [hφ, map_zero]
    · rw [← domainIncl_domainS, ← D.H.domainIncl_domainD]
      exact congrArg (D.H.domainIncl (i + 1)) hS
  · rintro ⟨v, hv, hS⟩
    obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hv
    obtain ⟨φ, hφ⟩ := D.Ht.exists_domainIncl_eq_of_mem y.2
    have hc : D.Ht.domainCoord i (i + 1) φ = y := Subtype.ext hφ
    refine ⟨φ, D.Ht.domainIncl_injective (i + 1) ?_, D.H.domainIncl_injective (i + 1) ?_⟩
    · change D.Ht.domainIncl (i + 1) (D.Ht.domainD i (i + 1) φ) = _
      rw [D.Ht.domainIncl_domainD, hc, hy, map_zero]
    · change D.H.domainIncl (i + 1) (D.domainS i (i + 1) φ) =
        D.H.domainIncl (i + 1) (D.H.domainD i (i + 1) σ)
      rw [domainIncl_domainS, D.H.domainIncl_domainD, hφ, hS]

/-- `[(σ, φ)] ↦ ι σ` maps `Hⁱ(bgg J)` linearly and injectively onto `P ⊆ Wⁱ`. -/
def HomologyIs (J i : ℤ) (P : Set (W i)) : Prop :=
  ∃ f : (D.domainData.bgg J).homology i →ₗ[𝕜] W i, Function.Injective f ∧ Set.range f = P ∧
    ∀ (z : (D.domainData.bgg J).cycles i) (y : D.domainData.Γ (J < ·) i),
      (D.domainData.bgg J).iCycles i z = Submodule.Quotient.mk y →
        f ((D.domainData.bgg J).homologyπ i z) =
          D.H.domainIncl i (y : D.H.domainSpace i × D.Ht.domainSpace i).1

/-- If the rows vanish in degree `i - 1`, `i ≤ J`, and `Sⁱ`, `Sⁱ⁺¹` are one-to-one as required,
then `Hⁱ(bgg J)` is the set of `u ∈ D(dⁱ)` with `d u = S v` for some `v ∈ N(d̃ⁱ)`. -/
theorem homologyIs_lowest {i J : ℤ} (hiJ : i ≤ J) [Subsingleton (W (i - 1))]
    [Subsingleton (Wt (i - 1))] (hS : J = i → Function.Injective (D.S i (i + 1)))
    (hS' : i + 2 ≤ J → Function.Injective (D.S (i + 1) (i + 1 + 1))) :
    D.HomologyIs J i {u | ∃ hu : u ∈ (D.H.d i (i + 1)).domain, ∃ v ∈ (D.Ht.d i (i + 1)).ker,
        D.S i (i + 1) v = D.H.d i (i + 1) ⟨u, hu⟩} := by
  have : Subsingleton (D.H.domainSpace (i - 1)) := (D.H.domainIncl_injective _).subsingleton
  have : Subsingleton (D.Ht.domainSpace (i - 1)) := (D.Ht.domainIncl_injective _).subsingleton
  obtain ⟨f, hf, hrange, hfz⟩ := D.domainData.exists_bgg_homology_lowCycles hiJ
    (fun h => D.injective_domainS (hS h)) (fun h => D.injective_domainS (hS' h))
  refine ⟨(D.H.domainIncl i).toLinearMap ∘ₗ f, (D.H.domainIncl_injective i).comp hf, ?_,
    fun z y h => by rw [LinearMap.comp_apply, hfz z y h]; rfl⟩
  rw [LinearMap.coe_comp, Set.range_comp, ← LinearMap.coe_range, hrange]
  ext u
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨v, hv, hSv⟩ := (D.mem_domainData_lowCycles).1 hσ
    exact ⟨_, v, hv, hSv⟩
  · rintro ⟨hu, v, hv, hSv⟩
    obtain ⟨σ, rfl⟩ := D.H.exists_domainIncl_eq_of_mem hu
    exact ⟨σ, (D.mem_domainData_lowCycles).2 ⟨v, hv, hSv⟩, rfl⟩

end Feec.BGG.HilbertData
