module

public import Solution.Bridge

/-!
# The static FEEC theorem (solution)

`FEEC.staticFEEC` and `FEEC.staticFEEC_uniform` of `Challenge.lean`, proved from
`Feec.HilbertComplex.SubcomplexFamily.staticFEEC` and the explicit constants of `Feec` through the
bridge `Solution.Bridge` (`HilbertComplex.SubcomplexFamily.staticVerdict_of`, with the constant
`HilbertComplex.staticConst`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3–§3.4

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

end FEEC
