module

public import Feec.Evolution.Solution

/-!
# Derivatives of curves staying in a closed subspace

If a curve `f : ℝ → E` stays in a closed subspace `K` near `t` (within a set `s` accumulating
at `t`), its derivative within `s` at `t` lies in `K`: the difference quotients
`(r - t)⁻¹ • (f r - f t)` lie in `K` and converge to `f'`. This is the tangent argument behind
every "necessity" statement for constraint propagation: a solution of `U' = A U + F` that stays
in `K` has `A U + F ∈ K`.

## Main results

* `deriv_mem_of_eventually_mem_closed`: the general statement, for a derivative within any set
  `s` with `(𝓝[s \ {t}] t).NeBot`;
* `deriv_mem_of_eventually_mem_closed_Ici`: the right-derivative case;
* `IsStrongSolution.deriv_mem_of_mem`: a strong solution on `[a,b]` (`a < b`) with values in a
  closed subspace `K` has `A (U t) + F t ∈ K` for every `t ∈ [a,b]`;
* `IsStrongSolution.apply_mem_of_mem`: in particular `A (U t) ∈ K` when the forcing is
  `K`-valued.

The subspace may be a submodule over any scalar ring `R` acting compatibly with `ℝ`, e.g. `ℝ`,
`ℂ` or `RCLike 𝕜`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
-/

open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {R : Type*} [Ring R] [Module R E] [SMul ℝ R] [IsScalarTower ℝ R E]

/-- **Tangent lemma**: if `f` has derivative `f'` within `s` at `t`, `t` is an accumulation
point of `s`, and `f r ∈ K` for `r ∈ s` near `t` (and `f t ∈ K`), with `K` a closed subspace,
then `f' ∈ K`. -/
theorem deriv_mem_of_eventually_mem_closed {f : ℝ → E} {f' : E} {s : Set ℝ} {t : ℝ}
    {K : Submodule R E} (hK : IsClosed (K : Set E)) (hf : HasDerivWithinAt f f' s t)
    (hs : (𝓝[s \ {t}] t).NeBot) (hev : ∀ᶠ r in 𝓝[s] t, f r ∈ K) (ht : f t ∈ K) : f' ∈ K := by
  refine hK.mem_of_tendsto (hasDerivWithinAt_iff_tendsto_slope.1 hf) ?_
  have hev' : ∀ᶠ r in 𝓝[s \ {t}] t, f r ∈ K := nhdsWithin_mono _ sdiff_subset hev
  filter_upwards [hev'] with r hr
  rw [slope_def_module]
  exact K.smul_of_tower_mem _ (K.sub_mem hr ht)

/-- **Tangent lemma, right derivative**: if `f` has right derivative `f'` at `t` and `f r ∈ K`
for `r ≥ t` near `t`, with `K` a closed subspace, then `f' ∈ K`. -/
theorem deriv_mem_of_eventually_mem_closed_Ici {f : ℝ → E} {f' : E} {t : ℝ}
    {K : Submodule R E} (hK : IsClosed (K : Set E)) (hf : HasDerivWithinAt f f' (Ici t) t)
    (hev : ∀ᶠ r in 𝓝[≥] t, f r ∈ K) : f' ∈ K := by
  refine deriv_mem_of_eventually_mem_closed hK hf ?_ hev
    (hev.self_of_nhdsWithin self_mem_Ici)
  exact (inferInstance : (𝓝[>] t).NeBot).mono
    (nhdsWithin_mono _ fun r (hr : t < r) => ⟨hr.le, hr.ne'⟩)

/-- In `[a,b]` with `a < b`, every point is an accumulation point. -/
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

/-- A strong solution on `[a,b]` (`a < b`) with values in a closed subspace `K` has
`A (U t) + F t ∈ K` for every `t ∈ [a,b]` (tangent lemma). -/
theorem deriv_mem_of_mem (hab : a < b) {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E))
    (hU : IsStrongSolution A (Icc a b) F U) (hmem : ∀ t ∈ Icc a b, U t ∈ K) {t : ℝ}
    (ht : t ∈ Icc a b) : A ⟨U t, hU.mem_domain ht⟩ + F t ∈ K :=
  deriv_mem_of_eventually_mem_closed hK (hU.hasDerivWithinAt ht) (neBot_nhdsWithin_Icc_diff hab ht)
    (eventually_nhdsWithin_of_forall hmem) (hmem t ht)

/-- A strong solution on `[a,b]` (`a < b`) with `K`-valued forcing and values in a closed
subspace `K` has `A (U t) ∈ K` for every `t ∈ [a,b]`. -/
theorem apply_mem_of_mem (hab : a < b) {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E))
    (hU : IsStrongSolution A (Icc a b) F U) (hmem : ∀ t ∈ Icc a b, U t ∈ K)
    (hF : ∀ t ∈ Icc a b, F t ∈ K) {t : ℝ} (ht : t ∈ Icc a b) : A ⟨U t, hU.mem_domain ht⟩ ∈ K := by
  have := K.sub_mem (hU.deriv_mem_of_mem hab hK hmem ht) (hF t ht)
  rwa [add_sub_cancel_right] at this

end IsStrongSolution

end Feec.Evolution
