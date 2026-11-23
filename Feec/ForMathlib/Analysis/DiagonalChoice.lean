module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# A diagonal choice of approximants, and Lax's principle

`exists_tendsto_zero_of_forall_eventually_exists_lt`: let `α N` be nonempty types and
`g N : α N → ℝ` nonnegative. If for every `ε > 0`, for all large `N`, some `a ∈ α N` has
`g N a < ε`, then some choice `a N ∈ α N` has `g N (a N) → 0`: the infima `inf g N` tend to `0`,
and `a N` is taken within `1 / (N + 1)` of `inf g N`.

For a family of approximation schemes, with `α N` the admissible discrete data at level `N` and
`g N` their distance to a datum, it turns "the datum is approximated by admissible data at every
fine enough level" into a sequence of admissible data converging to it, the hypothesis of a
Lax-type convergence theorem (the initial data of the semi-discrete scheme (6.5) of
[QuennevilleBelair2015], which are constrained).

**Lax's principle** (`tendstoUniformlyOn_iff_tendsto_of_stable`), in the form used for
evolution problems: let `A i` be sets of paths `α → X` in a pseudometric space, *stable* on `s`
from `a ∈ s` (`dist (v t) (w t) ≤ dist (v a) (w a)` on `s` for `v, w ∈ A i`, the energy estimate
of a scheme), and let `u` be uniformly approximated on `s` by paths of `A i` for `i` large (the
convergence of the scheme for regular data, transferred to `u` by density). Then a family
`v i ∈ A i` converges to `u` uniformly on `s` iff it converges at `a`; and when every `A N` is
nonempty some family does (`exists_tendstoUniformlyOn_of_stable`, by the diagonal choice).

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

/-! ### Lax's principle -/

section Stable

variable {α X : Type*} [PseudoMetricSpace X] {s : Set α} {a : α} {u : α → X}

/-- **Lax's principle**: let the paths of `A i` be *stable* on `s` from `a ∈ s`,
`dist (v t) (w t) ≤ dist (v a) (w a)` for `v, w ∈ A i` and `t ∈ s`, and let `u` be uniformly
approximated by them: for every `ε > 0`, for `i` large some `w ∈ A i` is within `ε` of `u` on
`s`. Then a family `v i ∈ A i` converges to `u` uniformly on `s` iff it converges at `a`. -/
theorem tendstoUniformlyOn_iff_tendsto_of_stable {ι : Type*} {l : Filter ι}
    {A : ι → Set (α → X)} (ha : a ∈ s)
    (hA : ∀ i, ∀ v ∈ A i, ∀ w ∈ A i, ∀ t ∈ s, dist (v t) (w t) ≤ dist (v a) (w a))
    (hu : ∀ ε > 0, ∀ᶠ i in l, ∃ w ∈ A i, ∀ t ∈ s, dist (u t) (w t) ≤ ε)
    {v : ι → α → X} (hv : ∀ i, v i ∈ A i) :
    TendstoUniformlyOn v u l s ↔ Tendsto (fun i => v i a) l (𝓝 (u a)) := by
  refine ⟨fun h => h.tendsto_at ha, fun h => Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
  filter_upwards [hu (ε / 3) (by positivity), Metric.tendsto_nhds.1 h (ε / 3) (by positivity)]
    with i ⟨w, hw, hwu⟩ hi t ht
  calc dist (u t) (v i t) ≤ dist (u t) (w t) + dist (w t) (v i t) := dist_triangle _ _ _
    _ ≤ ε / 3 + (dist (u a) (w a) + dist (v i a) (u a)) := by
      rw [dist_comm (u a) (w a), dist_comm (v i a) (u a)]
      exact add_le_add (hwu t ht) ((hA i w hw (v i) (hv i) t ht).trans (dist_triangle _ _ _))
    _ < ε / 3 + (ε / 3 + ε / 3) :=
      add_lt_add_of_le_of_lt le_rfl (add_lt_add_of_le_of_lt (hwu a ha) hi)
    _ = ε := by ring

/-- **A family converging to an approximated path**: with the hypotheses of
`tendstoUniformlyOn_iff_tendsto_of_stable` on `ℕ`, if every `A N` is nonempty, some family
`v N ∈ A N` converges to `u` uniformly on `s` (its initial values are chosen diagonally,
`exists_tendsto_zero_of_forall_eventually_exists_lt`). -/
theorem exists_tendstoUniformlyOn_of_stable {A : ℕ → Set (α → X)} (hne : ∀ N, (A N).Nonempty)
    (ha : a ∈ s) (hA : ∀ N, ∀ v ∈ A N, ∀ w ∈ A N, ∀ t ∈ s, dist (v t) (w t) ≤ dist (v a) (w a))
    (hu : ∀ ε > 0, ∀ᶠ N in atTop, ∃ w ∈ A N, ∀ t ∈ s, dist (u t) (w t) ≤ ε) :
    ∃ v : ℕ → α → X, (∀ N, v N ∈ A N) ∧ TendstoUniformlyOn v u atTop s := by
  obtain ⟨w, hw⟩ := exists_tendsto_zero_of_forall_eventually_exists_lt
    (α := fun N => A N) (fun N => (hne N).to_subtype)
    (g := fun N w => dist (u a) ((w : α → X) a)) (fun _ _ => dist_nonneg) fun ε hε =>
      (hu (ε / 2) (half_pos hε)).mono fun N ⟨w, hw, h⟩ =>
        ⟨⟨w, hw⟩, (h a ha).trans_lt (half_lt_self hε)⟩
  refine ⟨fun N => w N, fun N => (w N).2,
    (tendstoUniformlyOn_iff_tendsto_of_stable ha hA hu fun N => (w N).2).2 ?_⟩
  exact tendsto_iff_dist_tendsto_zero.2 (hw.congr fun N => dist_comm _ _)

end Stable
