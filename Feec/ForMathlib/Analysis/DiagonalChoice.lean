module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# A diagonal choice of approximants, and Lax's principle

A diagonal choice of approximants `a N ∈ α N` with `g N (a N) → 0`, and Lax's principle: for
uniformly stable families of paths approximating `u`, uniform convergence to `u` is convergence at
the initial point.
-/

open Filter Topology

@[expose] public section

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

section Stable

variable {α X : Type*} [PseudoMetricSpace X] {s : Set α} {a : α} {u : α → X}

/-- **Lax's principle**: for families of paths uniformly stable on `s` from `a ∈ s` and
approximating `u` on `s`, a family converges to `u` uniformly on `s` iff it converges at `a`. -/
theorem tendstoUniformlyOn_iff_tendsto_of_stable {ι : Type*} {l : Filter ι}
    {A : ι → Set (α → X)} {C : ℝ} (ha : a ∈ s)
    (hA : ∀ i, ∀ v ∈ A i, ∀ w ∈ A i, ∀ t ∈ s, dist (v t) (w t) ≤ C * dist (v a) (w a))
    (hu : ∀ ε > 0, ∀ᶠ i in l, ∃ w ∈ A i, ∀ t ∈ s, dist (u t) (w t) ≤ ε)
    {v : ι → α → X} (hv : ∀ i, v i ∈ A i) :
    TendstoUniformlyOn v u l s ↔ Tendsto (fun i => v i a) l (𝓝 (u a)) := by
  refine ⟨fun h => h.tendsto_at ha, fun h => Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
  set δ := ε / (2 * (1 + 2 * |C|))
  have hδ : 0 < δ := by positivity
  filter_upwards [hu δ hδ, Metric.tendsto_nhds.1 h δ hδ] with i ⟨w, hw, hwu⟩ hi t ht
  have hwa : dist (w a) (v i a) ≤ δ + δ := (dist_triangle _ (u a) _).trans
    (add_le_add (by rw [dist_comm]; exact hwu a ha) (by rw [dist_comm]; exact hi.le))
  calc dist (u t) (v i t) ≤ dist (u t) (w t) + dist (w t) (v i t) := dist_triangle _ _ _
    _ ≤ δ + |C| * (δ + δ) := add_le_add (hwu t ht) ((hA i w hw (v i) (hv i) t ht).trans
        ((mul_le_mul_of_nonneg_right (le_abs_self C) dist_nonneg).trans
          (mul_le_mul_of_nonneg_left hwa (abs_nonneg C))))
    _ = ε / 2 := by
      simp only [δ]
      field_simp
      ring
    _ < ε := half_lt_self hε

theorem exists_tendstoUniformlyOn_of_stable {A : ℕ → Set (α → X)} {C : ℝ}
    (hne : ∀ N, (A N).Nonempty) (ha : a ∈ s)
    (hA : ∀ N, ∀ v ∈ A N, ∀ w ∈ A N, ∀ t ∈ s, dist (v t) (w t) ≤ C * dist (v a) (w a))
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
