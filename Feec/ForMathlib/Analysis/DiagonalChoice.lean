module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A diagonal choice of approximants

`exists_tendsto_zero_of_forall_eventually_exists_lt`: let `α N` be nonempty types and
`g N : α N → ℝ` nonnegative. If for every `ε > 0`, for all large `N`, some `a ∈ α N` has
`g N a < ε`, then some choice `a N ∈ α N` has `g N (a N) → 0`: the infima `inf g N` tend to `0`,
and `a N` is taken within `1 / (N + 1)` of `inf g N`.

For a family of approximation schemes, with `α N` the admissible discrete data at level `N` and
`g N` their distance to a datum, it turns "the datum is approximated by admissible data at every
fine enough level" into a sequence of admissible data converging to it, the hypothesis of a
Lax-type convergence theorem (the initial data of the semi-discrete scheme (6.5) of
[QuennevilleBelair2015], which are constrained).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Filter Topology

@[expose] public section

/-- **A diagonal choice**: if, for every `ε > 0`, for all large `N` some `a ∈ α N` has
`g N a < ε` (`g ≥ 0`, every `α N` nonempty), then some choice `a N ∈ α N` has `g N (a N) → 0`. -/
theorem exists_tendsto_zero_of_forall_eventually_exists_lt {α : ℕ → Type*}
    (hne : ∀ N, Nonempty (α N)) {g : ∀ N, α N → ℝ} (hg : ∀ N a, 0 ≤ g N a)
    (h : ∀ ε > 0, ∀ᶠ N in atTop, ∃ a, g N a < ε) :
    ∃ a : ∀ N, α N, Tendsto (fun N => g N (a N)) atTop (𝓝 0) := by
  have hbdd : ∀ N, BddBelow (Set.range (g N)) := fun N => ⟨0, by
    rintro _ ⟨a, rfl⟩
    exact hg N a⟩
  have hm : Tendsto (fun N => ⨅ a, g N a) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun b hb => Eventually.of_forall fun N => ?_, fun b hb => ?_⟩
    · have := hne N
      exact hb.trans_le (le_ciInf (hg N))
    · filter_upwards [h b hb] with N ⟨a, ha⟩
      exact (ciInf_le (hbdd N) a).trans_lt ha
  have hex : ∀ N, ∃ a, g N a < (⨅ a, g N a) + 1 / ((N : ℝ) + 1) := fun N => by
    have := hne N
    exact exists_lt_of_ciInf_lt (lt_add_of_pos_right _ Nat.one_div_pos_of_nat)
  choose a ha using hex
  refine ⟨a, squeeze_zero (fun N => hg N (a N)) (fun N => (ha N).le) ?_⟩
  simpa using hm.add tendsto_one_div_add_atTop_nhds_zero_nat
