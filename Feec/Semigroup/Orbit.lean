module

public import Feec.Semigroup.Basic
public import Feec.ForMathlib.LinearPMap.Integral
public import Feec.ForMathlib.Calculus.IntervalIntegral
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Orbit calculus for a strongly continuous semigroup

For a strongly continuous semigroup `G` on a Banach space `E` over `𝕜 = ℝ` or `ℂ`, with
generator `A`:

* `C0Semigroup.exists_bound`, `C0Semigroup.continuous_extS_uncurry`: local boundedness and joint
  continuity of `(t, x) ↦ S t x` (`extS t = S (max t 0)` extends `S` to negative times);
* `C0Semigroup.mapsTo_domain`, `C0Semigroup.generator_apply_S`: `S t D(A) ⊆ D(A)`,
  `A S t = S t A`;
* `C0Semigroup.sub_eq_integral`, `C0Semigroup.hasDerivWithinAt_apply`: on `D(A)`,
  `S t x - x = ∫₀ᵗ S s (A x) ds` and `(d/dt) S t x = S t (A x)`;
* `C0Semigroup.mem_graph_iff_sub_eq_integral`: `(x, y) ∈ graph A` iff
  `S τ x - x = ∫₀^τ S s y ds` for all `τ ≥ 0`; hence `C0Semigroup.isClosed_generator`;
* convolutions `∫ₐᵗ S(t - s) g(s) ds`: continuity (`continuousOn_conv`), the graph property
  (`conv_mem_graph`, `integral_mem_graph_S`) and the primitive identity (`conv_primitive`);
* `C0Semigroup.hasDerivWithinAt_extS_comp`: the product rule along the semigroup;
* `C0Semigroup.dense_domain_generator`, `C0Group.dense_domain_generator`: generators are densely
  defined;
* `C0Semigroup.forall_nonneg_of_forall_Icc`, `C0Group.forall_of_forall_Icc_neg`: invariance on
  `[0, T]` (resp. `[-T, T]`), `T > 0`, is invariance for all `t ≥ 0` (resp. all `t`).

Duhamel's formula and mild solutions are in `Feec.Evolution.Duhamel`.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.2 (Thm 2.4: generators)
* [K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*][EngelNagel2000],
  §II.1

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

namespace Feec

/-! ### Orbit calculus for a strongly continuous semigroup -/

namespace C0Semigroup

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] (G : C0Semigroup 𝕜 E)

theorem S_add_apply {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : E) :
    G.S (s + t) x = G.S s (G.S t x) := by
  rw [G.map_add s t hs ht]; rfl

@[simp] theorem S_zero_apply (x : E) : G.S 0 x = x := by rw [G.map_zero]; rfl

theorem S_comm_apply {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : E) :
    G.S s (G.S t x) = G.S t (G.S s x) := by
  rw [← G.S_add_apply hs ht, add_comm, G.S_add_apply ht hs]

/-- **Invariance on `[0, T]` is invariance for all `t ≥ 0`** (`S(t) = S(t - T) S(T)`). -/
theorem forall_nonneg_of_forall_Icc {P : Set E} {T : ℝ} (hT : 0 < T)
    (h : ∀ x ∈ P, ∀ t ∈ Icc 0 T, G.S t x ∈ P) : ∀ x ∈ P, ∀ t, 0 ≤ t → G.S t x ∈ P := by
  have key : ∀ n : ℕ, ∀ x ∈ P, ∀ t ∈ Icc 0 (n * T), G.S t x ∈ P := by
    intro n
    induction n with
    | zero =>
      intro x hx t ht
      have : t = 0 := le_antisymm (by simpa using ht.2) ht.1
      subst this; simpa using hx
    | succ n ih =>
      intro x hx t ht
      rcases le_total t T with htT | htT
      · exact h x hx t ⟨ht.1, htT⟩
      · have e : t = (t - T) + T := by ring
        rw [e, G.S_add_apply (by linarith) hT.le]
        refine ih _ (h x hx T ⟨hT.le, le_rfl⟩) _ ⟨by linarith, ?_⟩
        have := ht.2; push_cast at this; linarith
  intro x hx t ht
  obtain ⟨n, hn⟩ := Archimedean.arch t hT
  exact key n x hx t ⟨ht, by simpa [nsmul_eq_mul] using hn⟩

/-- `S` extended to negative times by `S 0 = 1`: `extS t = S (max t 0)`. -/
def extS (t : ℝ) : E →L[𝕜] E := G.S (max t 0)

theorem extS_of_nonneg {t : ℝ} (ht : 0 ≤ t) : G.extS t = G.S t := by
  simp [extS, max_eq_left ht]

theorem continuous_extS_apply (x : E) : Continuous fun t => G.extS t x :=
  (G.strongCont x).comp_continuous (continuous_id.max continuous_const) fun t => le_max_right t 0

variable [CompleteSpace E]

/-- `‖S t‖` is bounded on `[0,T]` (Banach–Steinhaus). -/
theorem exists_bound (T : ℝ) : ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ‖G.S t‖ ≤ C := by
  have h : ∀ x, ∃ C, ∀ i : Icc (0 : ℝ) T, ‖G.S i x‖ ≤ C := fun x => by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((G.strongCont x).mono Icc_subset_Ici_self)
    exact ⟨C, fun i => hC i i.2⟩
  obtain ⟨C, hC⟩ := banach_steinhaus h
  exact ⟨max C 0, le_max_right _ _, fun t ht => (hC ⟨t, ht⟩).trans (le_max_left _ _)⟩

/-- `‖extS t‖` is bounded on `(-∞, T]`. -/
theorem exists_bound_extS (T : ℝ) : ∃ C, 0 ≤ C ∧ ∀ t ≤ T, ‖G.extS t‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := G.exists_bound (max T 0)
  exact ⟨C, hC0, fun t ht => hC _ ⟨le_max_right _ _, max_le_max_right 0 ht⟩⟩

/-- **Joint continuity** of `(t, x) ↦ extS t x`. -/
theorem continuous_extS_uncurry : Continuous fun p : ℝ × E => G.extS p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, x₀⟩
  obtain ⟨C, -, hC⟩ := G.exists_bound_extS (t₀ + 1)
  have h1 : Tendsto (fun p : ℝ × E => G.extS p.1 x₀) (𝓝 (t₀, x₀)) (𝓝 (G.extS t₀ x₀)) :=
    ((G.continuous_extS_apply x₀).comp continuous_fst).continuousAt
  have hev : ∀ᶠ p : ℝ × E in 𝓝 (t₀, x₀), p.1 ≤ t₀ + 1 :=
    (continuous_fst.tendsto (t₀, x₀)).eventually (eventually_le_nhds (by linarith))
  have h2 : Tendsto (fun p : ℝ × E => G.extS p.1 (p.2 - x₀)) (𝓝 (t₀, x₀)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hv : Tendsto (fun p : ℝ × E => C * ‖p.2 - x₀‖) (𝓝 (t₀, x₀)) (𝓝 0) := by
      have : Tendsto (fun p : ℝ × E => p.2 - x₀) (𝓝 (t₀, x₀)) (𝓝 (x₀ - x₀)) :=
        (continuous_snd.sub continuous_const).continuousAt
      simpa using this.norm.const_mul C
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hv
    filter_upwards [hev] with p hp
    exact ((G.extS p.1).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC _ hp) (norm_nonneg _))
  have := h2.add h1
  rw [zero_add] at this
  exact this.congr fun p => by rw [← _root_.map_add, sub_add_cancel]

/-- `s ↦ extS (φ s) (g s)` is a.e.-strongly measurable for `g` a.e.-strongly measurable and `φ`
continuous. -/
theorem aestronglyMeasurable_extS_comp {μ : Measure ℝ} {g : ℝ → E} {φ : ℝ → ℝ}
    (hg : AEStronglyMeasurable g μ) (hφ : Continuous φ) :
    AEStronglyMeasurable (fun s => G.extS (φ s) (g s)) μ :=
  G.continuous_extS_uncurry.comp_aestronglyMeasurable (hφ.aestronglyMeasurable.prodMk hg)

/-- `s ↦ extS (φ s) (g s)` is interval integrable when `g` is and `φ` is continuous and bounded
above on `[a,b]`. -/
theorem intervalIntegrable_extS_comp {g : ℝ → E} {φ : ℝ → ℝ} {a b T : ℝ}
    (hg : IntervalIntegrable g volume a b) (hφ : Continuous φ) (hT : ∀ s ∈ uIcc a b, φ s ≤ T) :
    IntervalIntegrable (fun s => G.extS (φ s) (g s)) volume a b := by
  obtain ⟨C, -, hC⟩ := G.exists_bound_extS T
  refine (hg.norm.const_mul C).mono_fun' ?_ ?_
  · exact G.aestronglyMeasurable_extS_comp hg.def'.aestronglyMeasurable hφ
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    exact ((G.extS (φ s)).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (hC _ (hT s (uIoc_subset_uIcc hs))) (norm_nonneg _))

/-! ### The generator -/

section Generator

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

omit [CompleteSpace E] in
/-- A continuous `𝕜`-linear map carries `ℝ`-derivatives within a set along. -/
theorem _root_.ContinuousLinearMap.hasDerivWithinAt_apply_of_hasDerivWithinAt (L : E →L[𝕜] E)
    {f : ℝ → E} {f' : E} {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt f f' s t) :
    HasDerivWithinAt (fun r => L (f r)) (L f') s t :=
  (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t h

omit [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] in
theorem integral_extS_eq {τ : ℝ} (hτ : 0 ≤ τ) (y : E) :
    ∫ σ in (0 : ℝ)..τ, G.extS σ y = ∫ σ in (0 : ℝ)..τ, G.S σ y :=
  intervalIntegral.integral_congr fun σ hσ => by
    rw [uIcc_of_le hτ] at hσ
    rw [G.extS_of_nonneg hσ.1]

omit [IsScalarTower ℝ 𝕜 E] in
/-- The orbit `τ ↦ x + ∫₀^τ extS σ y` has derivative `extS t y` everywhere. -/
theorem hasDerivAt_add_integral_extS (x y : E) (t : ℝ) :
    HasDerivAt (fun τ => x + ∫ σ in (0 : ℝ)..τ, G.extS σ y) (G.extS t y) t :=
  ((G.continuous_extS_apply y).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add x

omit [CompleteSpace E] in
/-- On `D(A)`, the orbit has right derivative `S t (A x)` at every `t ≥ 0`. -/
theorem hasDerivWithinAt_Ici_apply (x : G.generator.domain) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => G.S s x) (G.S t (G.generator x)) (Ici t) t := by
  have h1 : HasDerivWithinAt (fun h => G.S t (G.S h x)) (G.S t (G.generator x)) (Ici 0)
      (t - t) := by
    rw [sub_self]
    exact (G.S t).hasDerivWithinAt_apply_of_hasDerivWithinAt (G.hasDerivWithinAt_generator x)
  have hh : HasDerivWithinAt (fun s : ℝ => s - t) 1 (Ici t) t :=
    ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
  have h2 := HasDerivWithinAt.scomp (h := fun s : ℝ => s - t) t h1 hh
    fun s (hs : t ≤ s) => sub_nonneg.2 hs
  rw [one_smul] at h2
  refine h2.congr_of_mem (fun s (hs : t ≤ s) => ?_) self_mem_Ici
  simp only [Function.comp_apply]
  rw [← G.S_add_apply ht (sub_nonneg.2 hs), add_sub_cancel]

omit [CompleteSpace E] in
/-- `S t` maps `D(A)` into `D(A)` (`t ≥ 0`), with right derivative `S t (A x)` at `0`. -/
theorem hasDerivWithinAt_S_apply_zero (x : G.generator.domain) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun h => G.S h (G.S t x)) (G.S t (G.generator x)) (Ici 0) 0 := by
  refine ((G.S t).hasDerivWithinAt_apply_of_hasDerivWithinAt
    (G.hasDerivWithinAt_generator x)).congr_of_mem (fun h (hh : 0 ≤ h) => ?_) self_mem_Ici
  exact G.S_comm_apply hh ht x

omit [CompleteSpace E] in
/-- `S t` maps `D(A)` into `D(A)` for `t ≥ 0`. -/
theorem mapsTo_domain (x : G.generator.domain) {t : ℝ} (ht : 0 ≤ t) :
    G.S t x ∈ G.generator.domain :=
  ⟨_, G.hasDerivWithinAt_S_apply_zero x ht⟩

omit [CompleteSpace E] in
/-- `A (S t x) = S t (A x)` on `D(A)`, `t ≥ 0`. -/
theorem generator_apply_S (x : G.generator.domain) {t : ℝ} (ht : 0 ≤ t) :
    G.generator ⟨G.S t x, G.mapsTo_domain x ht⟩ = G.S t (G.generator x) :=
  G.generator_apply_eq (G.hasDerivWithinAt_S_apply_zero x ht)

omit [CompleteSpace E] in
/-- Graph form of `generator_apply_S`. -/
theorem S_mem_graph {x y : E} (h : (x, y) ∈ G.generator.graph) {t : ℝ} (ht : 0 ≤ t) :
    (G.S t x, G.S t y) ∈ G.generator.graph := by
  obtain ⟨hx, rfl⟩ := LinearPMap.mem_graph_iff_exists.1 h
  exact LinearPMap.mem_graph_iff_exists.2 ⟨G.mapsTo_domain ⟨x, hx⟩ ht,
    G.generator_apply_S ⟨x, hx⟩ ht⟩

/-- **The orbit identity** on `D(A)`: `S t x - x = ∫₀ᵗ S s (A x) ds` for `t ≥ 0`. -/
theorem sub_eq_integral (x : G.generator.domain) {t : ℝ} (ht : 0 ≤ t) :
    G.S t x - x = ∫ s in (0 : ℝ)..t, G.S s (G.generator x) := by
  set y := G.generator x
  have hc : ContinuousOn (fun τ => G.S τ x - x - ∫ σ in (0 : ℝ)..τ, G.extS σ y) (Icc 0 t) :=
    (((G.strongCont x).mono Icc_subset_Ici_self).sub continuousOn_const).sub
      (fun τ _ => ((G.hasDerivAt_add_integral_extS 0 y τ).continuousAt.continuousWithinAt).congr
        (fun s _ => by simp) (by simp))
  have h := constant_of_has_deriv_right_zero hc fun τ hτ => by
    have h1 := (G.hasDerivWithinAt_Ici_apply x hτ.1).sub_const (x : E)
    have h2 := (G.hasDerivAt_add_integral_extS 0 y τ).hasDerivWithinAt (s := Ici τ)
    simp only [zero_add] at h2
    have := h1.sub h2
    rwa [G.extS_of_nonneg hτ.1, sub_self] at this
  have := h t ⟨ht, le_rfl⟩
  simp only [S_zero_apply, sub_self, intervalIntegral.integral_same, sub_eq_zero] at this
  rw [this, G.integral_extS_eq ht]

/-- On `D(A)`, `t ↦ S t x` has derivative `S t (A x)` within `[0, ∞)` at every `t ≥ 0`. -/
theorem hasDerivWithinAt_apply (x : G.generator.domain) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => G.S s x) (G.S t (G.generator x)) (Ici 0) t := by
  refine ((G.hasDerivAt_add_integral_extS x (G.generator x) t).hasDerivWithinAt).congr_of_mem
    (fun s (hs : 0 ≤ s) => ?_) ht |>.congr_deriv (G.extS_of_nonneg ht ▸ rfl)
  rw [G.integral_extS_eq hs, ← G.sub_eq_integral x hs, add_sub_cancel]

/-- **Characterization of the generator graph**: `(x, y) ∈ graph A` iff
`S τ x - x = ∫₀^τ S σ y dσ` for every `τ ≥ 0`. -/
theorem mem_graph_iff_sub_eq_integral {x y : E} :
    (x, y) ∈ G.generator.graph ↔ ∀ τ, 0 ≤ τ → G.S τ x - x = ∫ σ in (0 : ℝ)..τ, G.S σ y := by
  constructor
  · intro h τ hτ
    obtain ⟨hx, rfl⟩ := LinearPMap.mem_graph_iff_exists.1 h
    exact G.sub_eq_integral ⟨x, hx⟩ hτ
  · intro h
    have hd : HasDerivWithinAt (fun τ => G.S τ x) y (Ici 0) 0 := by
      have := (G.hasDerivAt_add_integral_extS x y 0).hasDerivWithinAt (s := Ici 0)
      rw [G.extS_of_nonneg le_rfl, S_zero_apply] at this
      refine this.congr_of_mem (fun τ (hτ : 0 ≤ τ) => ?_) self_mem_Ici
      rw [G.integral_extS_eq hτ, ← h τ hτ, add_sub_cancel]
    exact LinearPMap.mem_graph_iff_exists.2 ⟨⟨y, hd⟩, G.generator_apply_eq hd⟩

/-- **The generator is closed.** -/
theorem isClosed_generator : G.generator.IsClosed := by
  have e : (G.generator.graph : Set (E × E)) =
      ⋂ τ ∈ Ici (0 : ℝ), {p : E × E | G.S τ p.1 - p.1 = ∫ σ in (0 : ℝ)..τ, G.extS σ p.2} := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, mem_iInter, mem_Ici, mem_ofPred_eq]
    rw [G.mem_graph_iff_sub_eq_integral]
    exact forall₂_congr fun τ hτ => by rw [G.integral_extS_eq hτ]
  show IsClosed (G.generator.graph : Set (E × E))
  rw [e]
  refine isClosed_biInter fun τ _ => isClosed_eq ?_ ?_
  · exact ((G.S τ).continuous.comp continuous_fst).sub continuous_fst
  · have hc : Continuous fun q : (E × E) × ℝ => G.extS q.2 q.1.2 :=
      G.continuous_extS_uncurry.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (p : E × E) (σ : ℝ) => G.extS σ p.2) hc 0 τ

/-- `∫₀ᵘ S σ y dσ ∈ D(A)` with `A ∫₀ᵘ S σ y dσ = S u y - y` (`u ≥ 0`). -/
theorem integral_mem_graph_S {u : ℝ} (hu : 0 ≤ u) (y : E) :
    (∫ σ in (0 : ℝ)..u, G.S σ y, G.S u y - y) ∈ G.generator.graph := by
  rw [G.mem_graph_iff_sub_eq_integral]
  intro τ hτ
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun σ => G.extS σ y) volume a b := fun a b =>
    (G.continuous_extS_apply y).intervalIntegrable a b
  have e1 : G.S τ (∫ σ in (0 : ℝ)..u, G.S σ y) = ∫ σ in τ..τ + u, G.extS σ y := by
    rw [← G.integral_extS_eq hu, ← (G.S τ).intervalIntegral_comp_comm (hi 0 u)]
    have := intervalIntegral.integral_comp_add_left (fun σ => G.extS σ y) τ (a := 0) (b := u)
    rw [add_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [uIcc_of_le hu] at hσ
    simp only [G.extS_of_nonneg hσ.1, G.extS_of_nonneg (add_nonneg hτ hσ.1),
      ← G.S_add_apply hτ hσ.1]
  have e2 : (∫ σ in (0 : ℝ)..τ, G.S σ (G.S u y - y)) =
      (∫ σ in u..τ + u, G.extS σ y) - ∫ σ in (0 : ℝ)..τ, G.extS σ y := by
    rw [← G.integral_extS_eq hτ]
    simp only [_root_.map_sub]
    rw [intervalIntegral.integral_sub ((G.continuous_extS_apply _).intervalIntegrable 0 τ)
      (hi 0 τ)]
    congr 1
    have := intervalIntegral.integral_comp_add_right (fun σ => G.extS σ y) u (a := 0) (b := τ)
    rw [zero_add] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [uIcc_of_le hτ] at hσ
    simp only [G.extS_of_nonneg hσ.1, G.extS_of_nonneg (add_nonneg hσ.1 hu),
      ← G.S_add_apply hσ.1 hu]
  rw [e1, e2, ← G.integral_extS_eq hu]
  have h1 : (∫ σ in τ..τ + u, G.extS σ y) =
      (∫ σ in (0 : ℝ)..τ + u, G.extS σ y) - ∫ σ in (0 : ℝ)..τ, G.extS σ y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 τ) (hi τ (τ + u))]; abel
  have h2 : (∫ σ in u..τ + u, G.extS σ y) =
      (∫ σ in (0 : ℝ)..τ + u, G.extS σ y) - ∫ σ in (0 : ℝ)..u, G.extS σ y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 u) (hi u (τ + u))]; abel
  rw [h1, h2]; abel

/-! ### Convolutions `∫ₐᵗ S(t - s) g(s) ds` -/

omit [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] in
theorem integral_S_sub_eq_extS {g : ℝ → E} {a t : ℝ} (hat : a ≤ t) :
    ∫ s in a..t, G.S (t - s) (g s) = ∫ s in a..t, G.extS (t - s) (g s) :=
  intervalIntegral.integral_congr fun s hs => by
    rw [uIcc_of_le hat] at hs
    rw [G.extS_of_nonneg (sub_nonneg.2 hs.2)]

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem integrableOn_S_sub {g : ℝ → E} {a t : ℝ} (hat : a ≤ t) (hg : IntegrableOn g (Ioc a t)) :
    IntegrableOn (fun s => G.S (t - s) (g s)) (Ioc a t) := by
  have h := (G.intervalIntegrable_extS_comp (T := t - a) (φ := fun s => t - s)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2 hg) (continuous_const.sub continuous_id)
    fun s hs => by rw [uIcc_of_le hat] at hs; linarith [hs.1]).1
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioc
  simp only [G.extS_of_nonneg (sub_nonneg.2 hs.2)]

omit [IsScalarTower ℝ 𝕜 E] in
/-- The convolution `t ↦ ∫ₐᵗ S(t - s) g(s) ds` of `g ∈ L¹(a,b)` is continuous on `[a,b]`. -/
theorem continuousOn_conv {g : ℝ → E} {a b : ℝ} (hg : IntegrableOn g (Ioc a b)) :
    ContinuousOn (fun t => ∫ s in a..t, G.S (t - s) (g s)) (Icc a b) := by
  set μ := volume.restrict (Ioc a b)
  set f : ℝ → ℝ → E := fun t s => G.extS (t - s) (g s)
  have e : ∀ t ∈ Icc a b, ∫ s in a..t, G.S (t - s) (g s) = ∫ s, (Iic t).indicator (f t) s ∂μ :=
    fun t ht => by
      rw [G.integral_S_sub_eq_extS ht.1, intervalIntegral.integral_of_le ht.1,
        setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right ht.2]
  refine ContinuousOn.congr (f := fun t => ∫ s, (Iic t).indicator (f t) s ∂μ) ?_ e
  intro t₀ ht₀
  obtain ⟨C, -, hC⟩ := G.exists_bound_extS (b - a)
  refine continuousWithinAt_of_dominated (bound := fun s => C * ‖g s‖) ?_ ?_
    (hg.norm.const_mul C) ?_
  · exact Eventually.of_forall fun t =>
      (G.aestronglyMeasurable_extS_comp hg.aestronglyMeasurable
        (continuous_const.sub continuous_id)).indicator measurableSet_Iic
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    refine (norm_indicator_le_norm_self _ _).trans ?_
    exact ((G.extS _).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (hC _ (by linarith [ht.2, hs.1])) (norm_nonneg _))
  · filter_upwards [Measure.ae_ne μ t₀] with s hs
    refine ContinuousAt.continuousWithinAt ?_
    rcases hs.lt_or_gt with hs | hs
    · have hc : Continuous fun t : ℝ => G.extS (t - s) (g s) :=
        (G.continuous_extS_apply (g s)).comp (continuous_id.sub continuous_const)
      refine hc.continuousAt.congr ?_
      filter_upwards [eventually_gt_nhds hs] with t ht
      simp [f, indicator_of_mem (show s ∈ Iic t from ht.le)]
    · refine (continuousAt_const (y := (0 : E))).congr ?_
      filter_upwards [eventually_lt_nhds hs] with t ht
      simp [indicator_of_notMem (show s ∉ Iic t from not_le.2 ht)]

/-- **Hille's theorem along the semigroup**: if `(f s, H s) ∈ graph A` for a.e. `s ∈ (a,t]`, then
`(∫ₐᵗ S(t - s) f s ds, ∫ₐᵗ S(t - s) H s ds) ∈ graph A`. -/
theorem conv_mem_graph {f H : ℝ → E} {a t : ℝ} (hat : a ≤ t) (hf : IntegrableOn f (Ioc a t))
    (hH : IntegrableOn H (Ioc a t))
    (hfH : ∀ᵐ s ∂(volume.restrict (Ioc a t)), (f s, H s) ∈ G.generator.graph) :
    (∫ s in a..t, G.S (t - s) (f s), ∫ s in a..t, G.S (t - s) (H s)) ∈ G.generator.graph := by
  refine LinearPMap.integral_mem_graph_of_isClosed G.isClosed_generator hat
    (G.integrableOn_S_sub hat hf) (G.integrableOn_S_sub hat hH) ?_
  filter_upwards [hfH, ae_restrict_mem measurableSet_Ioc] with s hs hs'
  exact G.S_mem_graph hs (sub_nonneg.2 hs'.2)

omit [CompleteSpace E] [IsScalarTower ℝ 𝕜 E] in
/-- `t ↦ ∫ₐᵗ S(t - s) x ds = ∫₀^{t-a} S σ x dσ`. -/
theorem integral_S_sub_const {a t : ℝ} (hat : a ≤ t) (x : E) :
    ∫ s in a..t, G.S (t - s) x = ∫ σ in (0 : ℝ)..t - a, G.S σ x := by
  rw [G.integral_S_sub_eq_extS hat,
    intervalIntegral.integral_comp_sub_left (fun σ => G.extS σ x) t, sub_self,
    G.integral_extS_eq (sub_nonneg.2 hat)]

omit [IsScalarTower ℝ 𝕜 E] in
/-- **Fubini for the convolution with a primitive**: for `g ∈ L¹(a,t)`,
`∫ₐᵗ S(t - s) (∫ₐˢ g) ds = ∫ₐᵗ (∫₀^{t-r} S σ (g r) dσ) dr`. -/
theorem conv_primitive {g : ℝ → E} {a t : ℝ} (hat : a ≤ t) (hg : IntegrableOn g (Ioc a t)) :
    ∫ s in a..t, G.S (t - s) (∫ r in a..s, g r) =
      ∫ r in a..t, ∫ σ in (0 : ℝ)..t - r, G.S σ (g r) := by
  obtain ⟨C, hC0, hC⟩ := G.exists_bound_extS (t - a)
  have hgi : ∀ s ∈ Ioc a t, IntervalIntegrable g volume a s := fun s hs =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1.le).2
      (hg.mono_set (Ioc_subset_Ioc_right hs.2))
  have h1 : ∫ s in a..t, G.S (t - s) (∫ r in a..s, g r) =
      ∫ s in a..t, ∫ r in a..s, G.extS (t - s) (g r) := by
    rw [G.integral_S_sub_eq_extS hat, intervalIntegral.integral_of_le hat,
      intervalIntegral.integral_of_le hat]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    exact ((G.extS (t - s)).intervalIntegral_comp_comm (hgi s hs)).symm
  have h2 := integral_integral_triangle_swap (k := fun s r => G.extS (t - s) (g r))
    (g := fun r => C * ‖g r‖) hat
    (G.continuous_extS_uncurry.comp_aestronglyMeasurable
      (((continuous_const.sub continuous_fst).aestronglyMeasurable).prodMk
        hg.aestronglyMeasurable.comp_snd))
    (hg.norm.const_mul C) fun s hs r _ =>
      ((G.extS _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC _ (by linarith [hs.1]))
        (norm_nonneg _))
  rw [h1, h2]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hat] at hr
  rw [intervalIntegral.integral_comp_sub_left (fun σ => G.extS σ (g r)) t, sub_self,
    G.integral_extS_eq (sub_nonneg.2 hr.2)]

/-- **Product rule along the semigroup**: if `y` and `φ` have derivatives `y'`, `φ'` within `s`
at `x` and `u ↦ extS u (y x)` has derivative `D` at `φ x`, then
`τ ↦ extS (φ τ) (y τ)` has derivative `extS (φ x) y' + φ' • D` within `s` at `x`. -/
theorem hasDerivWithinAt_extS_comp {y : ℝ → E} {y' D : E} {φ : ℝ → ℝ} {φ' : ℝ} {s : Set ℝ}
    {x : ℝ} (hy : HasDerivWithinAt y y' s x) (hφ : HasDerivWithinAt φ φ' s x)
    (hD : HasDerivAt (fun u => G.extS u (y x)) D (φ x)) :
    HasDerivWithinAt (fun τ => G.extS (φ τ) (y τ)) (G.extS (φ x) y' + φ' • D) s x := by
  have h1 : HasDerivWithinAt (fun τ => G.extS (φ τ) (y τ - y x)) (G.extS (φ x) y') s x := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hp : Tendsto (fun τ => (φ τ, slope y x τ)) (𝓝[s \ {x}] x) (𝓝 (φ x, y')) :=
      ((hφ.continuousWithinAt.mono sdiff_subset).tendsto).prodMk_nhds
        (hasDerivWithinAt_iff_tendsto_slope.1 hy)
    refine ((G.continuous_extS_uncurry.tendsto (φ x, y')).comp hp).congr fun τ => ?_
    simp only [Function.comp_apply, slope_def_module, sub_self, _root_.map_zero, sub_zero,
      ContinuousLinearMap.map_smul_of_tower]
  have h2 := hD.scomp_hasDerivWithinAt x hφ
  refine (h1.add h2).congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_) ?_
  · simp only [Pi.add_apply, Function.comp_apply]
    rw [← _root_.map_add, sub_add_cancel]
  · simp only [Pi.add_apply, Function.comp_apply]
    rw [sub_self, _root_.map_zero, zero_add]

/-- On `D(A)`, `u ↦ extS u x` has derivative `S u (A x)` at every `u > 0`. -/
theorem hasDerivAt_extS_apply (x : G.generator.domain) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v => G.extS v x) (G.S u (G.generator x)) u := by
  have h := (G.hasDerivWithinAt_apply x hu.le).hasDerivAt (Ici_mem_nhds hu)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hu] with v hv
  exact congrArg (· (x : E)) (G.extS_of_nonneg hv.le)

/-- **The generator of a semigroup is densely defined**: `h⁻¹ ∫₀ʰ S σ x dσ ∈ D(A)` tends to
`x` as `h → 0⁺`. -/
theorem dense_domain_generator : Dense (G.generator.domain : Set E) := by
  intro x
  have hd := ((G.continuous_extS_apply x).integral_hasStrictDerivAt 0 0).hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have hd' := hd.mono_left (nhdsWithin_mono _
    (fun h (hh : h ∈ Ioi (0 : ℝ)) => (ne_of_gt hh : h ≠ 0) : Ioi (0 : ℝ) ⊆ {0}ᶜ))
  rw [G.extS_of_nonneg le_rfl, S_zero_apply] at hd'
  refine mem_closure_of_tendsto hd' ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  rw [slope_def_module, intervalIntegral.integral_same, sub_zero, sub_zero,
    G.integral_extS_eq hh.le]
  exact Submodule.smul_of_tower_mem _ _
    (LinearPMap.mem_domain_of_mem_graph (G.integral_mem_graph_S hh.le x))

end Generator

end C0Semigroup

namespace C0Group

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **The generator of a group is densely defined** (that of `G.toC0Semigroup`). -/
theorem dense_domain_generator (G : C0Group 𝕜 E) [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    [CompleteSpace E] : Dense (G.generator.domain : Set E) :=
  G.toC0Semigroup.dense_domain_generator

/-- **Invariance on `[-T, T]` is invariance for all `t`** (`T > 0`): the forward case for the
group and for its reversal `t ↦ S(-t)`. -/
theorem forall_of_forall_Icc_neg (G : C0Group 𝕜 E) {P : Set E} {T : ℝ} (hT : 0 < T)
    (hP : ∀ x ∈ P, ∀ s ∈ Icc (-T) T, G.S s x ∈ P) : ∀ x ∈ P, ∀ t, G.S t x ∈ P := by
  let R : C0Semigroup 𝕜 E := ⟨fun t => G.S (-t), by rw [neg_zero, G.map_zero],
    fun s t _ _ => by rw [neg_add, G.map_add],
    fun x => ((G.strongCont x).comp continuous_neg).continuousOn⟩
  intro x hx t
  rcases le_total 0 t with ht | ht
  · exact G.toC0Semigroup.forall_nonneg_of_forall_Icc hT
      (fun y hy s hs => hP y hy s ⟨by linarith [hs.1], hs.2⟩) x hx t ht
  · simpa [R] using R.forall_nonneg_of_forall_Icc hT
      (fun y hy s hs => hP y hy (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩) x hx (-t)
      (by linarith)

end C0Group

end Feec
