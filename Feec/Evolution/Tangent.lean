module

public import Feec.Evolution.Solution

/-!
# Derivatives of curves staying in a closed subspace

A curve staying in a closed subspace `K` has its derivatives within sets accumulating at the point
in `K`; hence a strong solution of `U' = A U + F` on `[a,b]`, `a < b`, with values in `K` has
`A U + F ∈ K`.
-/

open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {R : Type*} [Ring R] [Module R E] [SMul ℝ R] [IsScalarTower ℝ R E]

/-- **Tangent lemma**: the derivative within `s` at an accumulation point `t` of `s` of a curve
staying in a closed subspace `K` near `t` lies in `K`. -/
theorem deriv_mem_of_eventually_mem_closed {f : ℝ → E} {f' : E} {s : Set ℝ} {t : ℝ}
    {K : Submodule R E} (hK : IsClosed (K : Set E)) (hf : HasDerivWithinAt f f' s t)
    (hs : (𝓝[s \ {t}] t).NeBot) (hev : ∀ᶠ r in 𝓝[s] t, f r ∈ K) (ht : f t ∈ K) : f' ∈ K := by
  refine hK.mem_of_tendsto (hasDerivWithinAt_iff_tendsto_slope.1 hf) ?_
  have hev' : ∀ᶠ r in 𝓝[s \ {t}] t, f r ∈ K := nhdsWithin_mono _ sdiff_subset hev
  filter_upwards [hev'] with r hr
  rw [slope_def_module]
  exact K.smul_of_tower_mem _ (K.sub_mem hr ht)

theorem neBot_nhdsWithin_Icc_diff {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    (𝓝[Icc a b \ {t}] t).NeBot := by
  rcases ht.2.lt_or_eq with htb | rfl
  · refine (left_nhdsWithin_Ioo_neBot htb).mono (nhdsWithin_mono _ ?_)
    intro r hr
    exact ⟨⟨ht.1.trans hr.1.le, hr.2.le⟩, hr.1.ne'⟩
  · refine (right_nhdsWithin_Ioo_neBot hab).mono (nhdsWithin_mono _ ?_)
    intro r hr
    exact ⟨⟨hr.1.le, hr.2.le⟩, hr.2.ne⟩

namespace IsStrongSolution

variable {𝕜 : Type*} [RCLike 𝕜] [InnerProductSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  {A : E →ₗ.[𝕜] E} {F U : ℝ → E} {a b : ℝ}

/-- A strong solution on `[a,b]`, `a < b`, with values in a closed subspace `K` has
`A U + F ∈ K`. -/
theorem deriv_mem_of_mem (hab : a < b) {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E))
    (hU : IsStrongSolution A (Icc a b) F U) (hmem : ∀ t ∈ Icc a b, U t ∈ K) {t : ℝ}
    (ht : t ∈ Icc a b) : A ⟨U t, hU.mem_domain ht⟩ + F t ∈ K :=
  deriv_mem_of_eventually_mem_closed hK (hU.hasDerivWithinAt ht) (neBot_nhdsWithin_Icc_diff hab ht)
    (eventually_nhdsWithin_of_forall hmem) (hmem t ht)

end IsStrongSolution

end Feec.Evolution
