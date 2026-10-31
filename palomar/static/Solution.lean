module

public import Solution.Bridge
public import Solution.Existence

/-!
# The static FEEC theorem (solution)

`FEEC.staticFEEC` and `FEEC.staticFEEC_uniform` of `Challenge.lean`, proved from
`Feec.HilbertComplex.SubcomplexFamily.staticFEEC` and the explicit constants of `Feec` through the
bridge `Solution.Bridge` (`HilbertComplex.SubcomplexFamily.staticVerdict_of`, with the constant
`HilbertComplex.staticConst`); `FEEC.exists_cochainProjection` and
`FEEC.exists_subcomplexFamily_iff` from `Feec.HilbertComplex.Subcomplex.exists_cochainProjection`
and `Feec.HilbertComplex.Subcomplex.exists_isGraphBounded_iff` through `Solution.Existence`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3–§3.4, Thm 3.7

Bibliography: [references.bib](../../docs/references.bib)
-/

open Filter Topology

universe u v w

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-- **The static FEEC theorem** ([AFW2010], Thms 3.4–3.6, 3.8, 3.9). Let `F` be a family of
subcomplexes whose cochain projections are bounded uniformly in the graph norm in degrees `j - 1`
and `j`. If the ranges `𝔅ʲ` of `dʲ⁻¹` and `𝔅ʲ⁺¹` of `dʲ` are closed, `F` satisfies the static
verdict in degree `j` (`SubcomplexFamily.StaticVerdict`) with a constant independent of `h`. -/
theorem staticFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} (F : H.SubcomplexFamily κ) (j : ℤ)
    (hπ : F.IsGraphBounded (j - 1)) (hπ' : F.IsGraphBounded j)
    (hj : IsClosed (H.boundaries j : Set (W j)))
    (hj' : IsClosed (H.boundaries (j + 1) : Set (W (j + 1)))) : ∃ C, F.StaticVerdict j C := by
  obtain ⟨c₁, hc₁, h₁⟩ := hπ.exists_one_le
  obtain ⟨c₂, -, h₂⟩ := hπ'.exists_one_le
  obtain ⟨p₁, hp₁⟩ := H.exists_poincareBy (i := j - 1) (by rwa [sub_add_cancel])
  obtain ⟨p₂, hp₂⟩ := H.exists_poincareBy hj'
  exact ⟨_, F.staticVerdict_of j (hc₁.trans (le_max_left _ c₂)) (h₁.mono (le_max_left _ _))
    (h₂.mono (le_max_right _ _)) (hp₁.mono (le_max_left _ p₂)) (hp₂.mono (le_max_right _ _))⟩

/-- **The constants of the static FEEC theorem** depend only on the bound `c` of the cochain
projections and the Poincaré constant `c_P` ([AFW2010], §3.3–§3.4): one function `Φ` serves every
Hilbert complex, family of subcomplexes and degree. -/
theorem staticFEEC_uniform : ∃ Φ : ℝ → ℝ → ℝ, ∀ {𝕜 : Type u} [RCLike 𝕜] {W : ℤ → Type v}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    {κ : Type w} {H : HilbertComplex 𝕜 W} (F : H.SubcomplexFamily κ) (j : ℤ) {c cP : ℝ},
    F.IsGraphBoundedBy (j - 1) c → F.IsGraphBoundedBy j c →
    H.PoincareBy (j - 1) cP → H.PoincareBy j cP → F.StaticVerdict j (Φ c cP) :=
  ⟨fun c cP => HilbertComplex.staticConst (max c 1) cP, fun F j _ _ hπ hπ' hP hP' =>
    F.staticVerdict_of j (le_max_right _ _) (hπ.mono (le_max_left _ _)) (hπ'.mono (le_max_left _ _))
      hP hP'⟩

/-- **Bounded cochain projections from discrete stability** ([AFW2010], Thm 3.7). -/
theorem exists_cochainProjection {H : HilbertComplex 𝕜 W} (S : H.Subcomplex)
    [∀ i, FiniteDimensional 𝕜 (S.V i)] {c₁ c₂ : ℤ → ℝ} (hc₁ : ∀ i, 0 ≤ c₁ i)
    (hc₂ : ∀ i, 0 ≤ c₂ i) (hP : ∀ i, S.PoincareBy i (c₁ i))
    (hH : ∀ i, S.HarmonicBoundBy i (c₂ i)) :
    ∃ P : S.CochainProjection, ∀ i (x : (H.d i (i + 1)).domain),
      H.graphNorm i (i + 1) ⟨P.π i x, S.le_domain i (i + 1) (P.π i x).2⟩ ≤
        (1 + c₁ i) * (1 + c₂ i) * H.graphNorm i (i + 1) x := by
  obtain ⟨P, hP'⟩ := S.toFeec.exists_cochainProjection hc₁ hc₂ (fun i => (hP i).toFeec)
    fun i => HilbertComplex.Subcomplex.harmonicBound_iff.2 (hH i)
  exact ⟨HilbertComplex.Subcomplex.CochainProjection.ofFeec P, fun i x =>
    HilbertComplex.Subcomplex.CochainProjection.graphNorm_ofFeec_le P
      (mul_nonneg (by linarith [hc₁ i]) (by linarith [hc₂ i])) (hP' i) x⟩

/-- **Uniformly bounded cochain projections exist iff discrete stability holds uniformly**
([AFW2010], Thms 3.6, 3.7 and (30)). -/
theorem exists_subcomplexFamily_iff {κ : Type*} {H : HilbertComplex 𝕜 W} (l : Filter κ)
    (V : κ → H.Subcomplex) [∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
    (hcr : ∀ i, IsClosed (H.boundaries i : Set (W i))) :
    (∃ F : H.SubcomplexFamily κ, F.l = l ∧ F.V = V ∧ ∀ i, F.IsGraphBounded i) ↔
      ∀ i, ∃ c₁ c₂ : ℝ, ∀ h, (V h).PoincareBy i c₁ ∧ (V h).HarmonicBoundBy i c₂ := by
  have key := Feec.HilbertComplex.Subcomplex.exists_isGraphBounded_iff (fun h => (V h).toFeec)
    fun i => (H.closedRangeAt_iff i).2 (hcr i)
  refine ⟨?_, fun hV => ?_⟩
  · rintro ⟨F, rfl, rfl, hF⟩ i
    obtain ⟨c₁, c₂, hc⟩ := key.1 ⟨fun h => (F.π h).toFeec,
      fun i => HilbertComplex.SubcomplexFamily.isGraphBounded_toFeec (hF i)⟩ i
    exact ⟨|c₁|, c₂, fun h => ⟨HilbertComplex.Subcomplex.poincareBy_of_feec (hc h).1,
      HilbertComplex.Subcomplex.harmonicBound_iff.1 (hc h).2⟩⟩
  · obtain ⟨π, hπ⟩ := key.2 fun i => by
      obtain ⟨c₁, c₂, hc⟩ := hV i
      exact ⟨c₁, c₂, fun h =>
        ⟨(hc h).1.toFeec, HilbertComplex.Subcomplex.harmonicBound_iff.2 (hc h).2⟩⟩
    refine ⟨⟨l, V, fun h => HilbertComplex.Subcomplex.CochainProjection.ofFeec (π h)⟩, rfl, rfl,
      fun i => ?_⟩
    obtain ⟨C, hC⟩ := hπ i
    exact ⟨|C|, fun h x => HilbertComplex.Subcomplex.CochainProjection.graphNorm_ofFeec_le (π h)
      (abs_nonneg C) (fun y => (hC h y).trans_eq (by rw [sq_abs])) x⟩

end FEEC
