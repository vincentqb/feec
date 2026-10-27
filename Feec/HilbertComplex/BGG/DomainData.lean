module

public import Feec.HilbertComplex.BGG.Analytic
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
* **`HilbertData.derivedComplex_closedRangeAt_finrank_le`**: the analytic BGG theorem for Hilbert
  complexes.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3 (bounded Hilbert complexes
  and linking maps)
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

variable {E F : ι → Prop}
  (hΔ : ∀ i, IsClosed (D.domainData.Δ F i : Set (D.H.domainSpace i × D.Ht.domainSpace i)))
  (h : D.domainData.Eliminates E F) (i : ι) [FiniteDimensional 𝕜 (D.H.cohomology i)]
  [FiniteDimensional 𝕜 (D.Ht.cohomology i)]
include hΔ h

/-- **Analytic BGG for Hilbert complexes**: for two Hilbert complexes linked by bounded
connecting maps, the derived complex of their domain complexes is a closed Hilbert complex with
closed range and finite-dimensional cohomology, of dimension at most
`dim Hⁱ(W) + dim Hⁱ(W̃)`, at every index where the two complexes have finite-dimensional
cohomology. [ArnoldHu2021], §5; [CapHu2024] -/
theorem derivedComplex_closedRangeAt_finrank_le :
    (D.domainData.derivedComplex E F).ClosedRangeAt i ∧
      FiniteDimensional 𝕜 ((D.domainData.derivedComplex E F).cohomology i) ∧
      Module.finrank 𝕜 ((D.domainData.derivedComplex E F).cohomology i) ≤
        Module.finrank 𝕜 (D.H.cohomology i) + Module.finrank 𝕜 (D.Ht.cohomology i) := by
  have := (D.domainRowTopCohomologyEquiv i).symm.finiteDimensional
  have := (D.domainRowBotCohomologyEquiv i).symm.finiteDimensional
  refine ⟨D.domainData.derivedComplex_closedRangeAt hΔ h i,
    D.domainData.finiteDimensional_derivedComplex_cohomology hΔ h i, ?_⟩
  rw [← (D.domainRowTopCohomologyEquiv i).finrank_eq,
    ← (D.domainRowBotCohomologyEquiv i).finrank_eq]
  exact D.domainData.finrank_derivedComplex_cohomology_le hΔ h i

end Feec.BGG.HilbertData
