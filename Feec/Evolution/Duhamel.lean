module

public import Feec.Semigroup.Basic
public import Feec.Evolution.Forcing
public import Feec.Evolution.Solution
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Duhamel's formula for a strongly continuous semigroup

For a strongly continuous semigroup `G` on a Banach space `E` over `𝕜 = ℝ` or `ℂ`, with
generator `A`, the **mild solution** (Duhamel's formula) of `U' = A U + F`, `U a = U₀` is
`Evolution.mild G.S a U₀ F t = S(t - a) U₀ + ∫ₐᵗ S(t - s) F(s) ds`.

## Main results

Orbit calculus (any `C0Semigroup`):

* `C0Semigroup.exists_bound`, `C0Semigroup.continuous_extS_uncurry`: local boundedness and joint
  continuity of `(t, x) ↦ S t x` (`extS t = S (max t 0)` extends `S` to negative times);
* `C0Semigroup.mapsTo_domain`, `C0Semigroup.generator_apply_S`: `S t D(A) ⊆ D(A)`,
  `A S t = S t A`;
* `C0Semigroup.sub_eq_integral`, `C0Semigroup.hasDerivWithinAt_apply`: on `D(A)`,
  `S t x - x = ∫₀ᵗ S s (A x) ds` and `(d/dt) S t x = S t (A x)`;
* `C0Semigroup.mem_graph_iff_sub_eq_integral`: `(x, y) ∈ graph A` iff
  `S τ x - x = ∫₀^τ S s y ds` for all `τ ≥ 0`; hence `C0Semigroup.isClosed_generator`.

Duhamel's formula:

* `Evolution.integral_mem_graph_of_isClosed`: a closed operator commutes with the Bochner
  integral (Hille).
* `C0Semigroup.integral_mem_graph`: **the domain property, once**: for admissible forcing
  (`ForcingClass.admissible`), `∫ₐᵗ S(t - s) F(s) ds ∈ D(A)` with `A`-image continuous in `t`
  (`L¹(a,b; D(A))` branch: Hille; `W^{1,1}` branch: Fubini and `A ∫₀ᵘ S = S u - 1`).
* `C0Semigroup.isClassicalSolution_mild`: the mild solution is a classical solution.
* `Evolution.IsStrongSolution.eq_mild`: every strong solution with continuous forcing is the mild
  solution (`s ↦ S(t - s) U(s)` has derivative `S(t - s) F(s)`).

## References

* [Pazy1983], §1.2 (Thm 2.4: generators), §4.2 (Thm 2.4, Cor 2.5: classical solutions)
* [EngelNagel2000], §II.1, §VI.7
* [QuennevilleBelair2015], §4.3 (Thm 4.3)
-/

open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

namespace Feec

/-! ### Closed operators commute with the Bochner integral -/

namespace Evolution

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]

/-- **Hille's theorem for closed operators**: if `A` is closed, `f` and `H` are integrable on
`(a,b]` and `(f s, H s)` lies in the graph of `A` for a.e. `s`, then
`(∫ₐᵇ f, ∫ₐᵇ H)` lies in the graph of `A`. -/
theorem integral_mem_graph_of_isClosed {A : E →ₗ.[𝕜] E} (hA : A.IsClosed) {f H : ℝ → E}
    {a b : ℝ} (hab : a ≤ b) (hf : IntegrableOn f (Ioc a b)) (hH : IntegrableOn H (Ioc a b))
    (hfH : ∀ᵐ s ∂(volume.restrict (Ioc a b)), (f s, H s) ∈ A.graph) :
    (∫ s in a..b, f s, ∫ s in a..b, H s) ∈ A.graph := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    ← integral_pair hf hH]
  set K : Submodule ℝ (E × E) := A.graph.restrictScalars ℝ
  have hK : IsClosed (K : Set (E × E)) := hA
  rcases hab.lt_or_eq with hab | rfl
  · have h0 : volume (Ioc a b) ≠ 0 := by simp [hab]
    have hfin : volume (Ioc a b) ≠ ⊤ := by simp
    have havg := K.convex.set_average_mem hK h0 hfin hfH (hf.prodMk hH)
    rw [setAverage_eq] at havg
    have := K.smul_mem (volume.real (Ioc a b)) havg
    rwa [smul_inv_smul₀ (by rw [Real.volume_real_Ioc_of_le hab.le]; linarith)] at this
  · simp only [Ioc_self, Measure.restrict_empty, integral_zero_measure]
    exact A.graph.zero_mem

omit [CompleteSpace E] in
/-- **Fubini on a triangle**: for `a ≤ t` and `k` a.e.-measurable on `(a,t]²` with
`‖k s r‖ ≤ g r`, `g` integrable,
`∫ₐᵗ ∫ₐˢ k s r dr ds = ∫ₐᵗ ∫ᵣᵗ k s r ds dr`. -/
theorem integral_integral_triangle_swap {k : ℝ → ℝ → E} {g : ℝ → ℝ} {a t : ℝ} (hat : a ≤ t)
    (hk : AEStronglyMeasurable (Function.uncurry k)
      ((volume.restrict (Ioc a t)).prod (volume.restrict (Ioc a t))))
    (hg : IntegrableOn g (Ioc a t)) (hb : ∀ s ∈ Ioc a t, ∀ r ∈ Ioc a t, ‖k s r‖ ≤ g r) :
    ∫ s in a..t, ∫ r in a..s, k s r = ∫ r in a..t, ∫ s in r..t, k s r := by
  set μ := volume.restrict (Ioc a t)
  set K : ℝ → ℝ → E := fun s r => if r ≤ s then k s r else 0 with hK
  have hKi : Integrable (Function.uncurry K) (μ.prod μ) := by
    refine Integrable.mono' (hg.comp_snd μ) ?_ ?_
    · have : Function.uncurry K = {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (Function.uncurry k) := by
        ext ⟨s, r⟩; simp [hK, Set.indicator, Function.uncurry]
      rw [this]
      exact hk.indicator (measurableSet_le measurable_snd measurable_fst)
    · filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        (ae_restrict_mem (μ := volume) measurableSet_Ioc), Measure.quasiMeasurePreserving_snd.ae
        (ae_restrict_mem (μ := volume) measurableSet_Ioc)] with p hp hp'
      simp only [Function.uncurry, hK]
      split_ifs
      · exact hb _ hp _ hp'
      · simpa using (norm_nonneg _).trans (hb p.1 hp p.2 hp')
  have hL : ∀ s ∈ Ioc a t, ∫ r in a..s, k s r = ∫ r, K s r ∂μ := fun s hs => by
    rw [intervalIntegral.integral_of_le hs.1.le]
    have : (fun r => K s r) = (Iic s).indicator (k s) := by
      ext r; simp [hK, Set.indicator]
    rw [this, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hs.2]
  have hR : ∀ r ∈ Ioc a t, ∫ s in r..t, k s r = ∫ s, K s r ∂μ := fun r hr => by
    rw [intervalIntegral.integral_of_le hr.2, ← integral_Icc_eq_integral_Ioc]
    have : (fun s => K s r) = (Ici r).indicator (fun s => k s r) := by
      ext s; simp [hK, Set.indicator]
    have e : Ioc a t ∩ Ici r = Icc r t := by
      ext s; simp only [mem_Icc, mem_inter_iff, mem_Ioc, mem_Ici]
      constructor
      · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hr.1.trans_le h1, h2⟩, h1⟩
    rw [this, setIntegral_indicator measurableSet_Ici, e]
  rw [intervalIntegral.integral_of_le hat, intervalIntegral.integral_of_le hat,
    setIntegral_congr_fun measurableSet_Ioc hL, setIntegral_congr_fun measurableSet_Ioc hR]
  exact integral_integral_swap hKi

/-- The primitive of a function continuous on `[a,b]` has derivative within `[a,b]`. -/
theorem hasDerivWithinAt_integral_of_continuousOn {W : ℝ → E} {a b t : ℝ}
    (hW : ContinuousOn W (Icc a b)) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun τ => ∫ s in a..τ, W s) (W t) (Icc a b) t := by
  have hab : a ≤ b := ht.1.trans ht.2
  set W' : ℝ → E := fun s => W (projIcc a b hab s)
  have hW' : Continuous W' :=
    hW.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun s => (projIcc a b hab s).2
  have e : ∀ τ ∈ Icc a b, ∫ s in a..τ, W s = ∫ s in a..τ, W' s := fun τ hτ =>
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le hτ.1] at hs
      simp [W', projIcc_of_mem hab ⟨hs.1, hs.2.trans hτ.2⟩]
  have hd := ((hW'.integral_hasStrictDerivAt a t).hasDerivAt).hasDerivWithinAt (s := Icc a b)
  rw [show W' t = W t by simp [W', projIcc_of_mem hab ht]] at hd
  exact hd.congr_of_mem e ht

end Evolution

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
  obtain ⟨hx, rfl⟩ := Evolution.mem_graph_iff_exists.1 h
  exact Evolution.mem_graph_iff_exists.2 ⟨G.mapsTo_domain ⟨x, hx⟩ ht,
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
    obtain ⟨hx, rfl⟩ := Evolution.mem_graph_iff_exists.1 h
    exact G.sub_eq_integral ⟨x, hx⟩ hτ
  · intro h
    have hd : HasDerivWithinAt (fun τ => G.S τ x) y (Ici 0) 0 := by
      have := (G.hasDerivAt_add_integral_extS x y 0).hasDerivWithinAt (s := Ici 0)
      rw [G.extS_of_nonneg le_rfl, S_zero_apply] at this
      refine this.congr_of_mem (fun τ (hτ : 0 ≤ τ) => ?_) self_mem_Ici
      rw [G.integral_extS_eq hτ, ← h τ hτ, add_sub_cancel]
    exact Evolution.mem_graph_iff_exists.2 ⟨⟨y, hd⟩, G.generator_apply_eq hd⟩

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
  refine Evolution.integral_mem_graph_of_isClosed G.isClosed_generator hat
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
  have h2 := Evolution.integral_integral_triangle_swap (k := fun s r => G.extS (t - s) (g r))
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

/-- **The domain property of Duhamel's integral, once**: for admissible forcing
(`F ∈ C([a,b]; E) ∩ (W^{1,1}(a,b; E) ∪ L¹(a,b; D(A)))`), `∫ₐᵗ S(t - s) F(s) ds ∈ D(A)` for
`t ∈ [a,b]`, with an `A`-image continuous on `[a,b]`. Explicitly the image is
`∫ₐᵗ S(t - s) A F(s) ds` in the `L¹(D(A))` case and `S(t - a) F(a) - F(t) + ∫ₐᵗ S(t - s) g(s) ds`
in the `W^{1,1}` case (`g` the weak derivative). Cf. [Pazy1983], Thm 4.2.4, Cor 4.2.5. -/
theorem integral_mem_graph {F : ℝ → E} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible G.generator a b F) :
    ∃ V : ℝ → E, ContinuousOn V (Icc a b) ∧
      ∀ t ∈ Icc a b, (∫ s in a..t, G.S (t - s) (F s), V t) ∈ G.generator.graph := by
  obtain ⟨hFc, hW | ⟨H, hH, hD⟩⟩ := hF
  · -- the `W^{1,1}` branch
    obtain ⟨g, hg, hpt⟩ := (Evolution.ForcingClass.w11_iff hFc).1 hW
    refine ⟨fun t => G.S (t - a) (F a) - F t + ∫ s in a..t, G.S (t - s) (g s), ?_, ?_⟩
    · have h1 : ContinuousOn (fun t => G.S (t - a) (F a)) (Icc a b) :=
        (G.strongCont (F a)).comp (continuousOn_id.sub continuousOn_const)
          fun t (ht : t ∈ Icc a b) => (sub_nonneg.2 ht.1 : (0 : ℝ) ≤ t - a)
      exact (h1.sub hFc).add (G.continuousOn_conv hg)
    intro t ht
    have hat := ht.1
    have hg' : IntegrableOn g (Ioc a t) := hg.mono_set (Ioc_subset_Ioc_right ht.2)
    have hgi : ∀ s ∈ Icc a t, IntervalIntegrable g volume a s := fun s hs =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).2
        (hg'.mono_set (Ioc_subset_Ioc_right hs.2))
    -- split `F = F a + ∫ₐ^· g`
    have hsplit : ∫ s in a..t, G.S (t - s) (F s) =
        (∫ σ in (0 : ℝ)..t - a, G.S σ (F a)) +
          ∫ r in a..t, ∫ σ in (0 : ℝ)..t - r, G.S σ (g r) := by
      rw [← G.integral_S_sub_const hat, ← G.conv_primitive hat hg', ← intervalIntegral.integral_add]
      · refine intervalIntegral.integral_congr fun s hs => ?_
        rw [uIcc_of_le hat] at hs
        rw [hpt s ⟨hs.1, hs.2.trans ht.2⟩, _root_.map_add]
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2 (G.integrableOn_S_sub hat
          ((continuousOn_const (c := F a)).integrableOn_Icc.mono_set Ioc_subset_Icc_self))
      · refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2
          (G.integrableOn_S_sub hat (g := fun s => ∫ r in a..s, g r) ?_)
        exact ((Evolution.ForcingClass.continuousOn_primitive hat hg').integrableOn_Icc).mono_set
          Ioc_subset_Icc_self
    -- the two graph pairs
    have hP1 := G.integral_mem_graph_S (sub_nonneg.2 hat) (F a)
    obtain ⟨C, hC0, hC⟩ := G.exists_bound_extS (t - a)
    have hΦ : Continuous fun p : ℝ × E => ∫ σ in (0 : ℝ)..p.1, G.extS σ p.2 :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : ℝ × E) (σ : ℝ) => G.extS σ p.2)
        (G.continuous_extS_uncurry.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
        continuous_fst
    have hΨi : IntegrableOn (fun r => ∫ σ in (0 : ℝ)..t - r, G.S σ (g r)) (Ioc a t) := by
      refine Integrable.mono' ((hg'.norm.const_mul (C * (t - a)))) ?_ ?_
      · have hc : Continuous fun r : ℝ => t - r := continuous_const.sub continuous_id
        refine (hΦ.comp_aestronglyMeasurable
          ((hc.aestronglyMeasurable).prodMk hg'.aestronglyMeasurable)).congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact G.integral_extS_eq (sub_nonneg.2 hr.2) (g r)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        rw [← G.integral_extS_eq (sub_nonneg.2 hr.2)]
        refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C * ‖g r‖)
          fun σ hσ => ?_).trans ?_
        · exact ((G.extS σ).le_opNorm _).trans (mul_le_mul_of_nonneg_right
            (hC σ (by rw [uIoc_of_le (sub_nonneg.2 hr.2)] at hσ; linarith [hσ.2, hr.1]))
            (norm_nonneg _))
        · rw [sub_zero, abs_of_nonneg (sub_nonneg.2 hr.2)]
          have : t - r ≤ t - a := by linarith [hr.1]
          calc C * ‖g r‖ * (t - r) ≤ C * ‖g r‖ * (t - a) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = C * (t - a) * ‖g r‖ := by ring
    have hP2 := Evolution.integral_mem_graph_of_isClosed G.isClosed_generator hat hΨi
      ((G.integrableOn_S_sub hat hg').sub hg') (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact G.integral_mem_graph_S (sub_nonneg.2 hr.2) (g r))
    have hgt : ∫ r in a..t, g r = F t - F a := by rw [hpt t ht]; abel
    rw [hsplit]
    convert G.generator.graph.add_mem hP1 hP2 using 1
    refine Prod.ext rfl ?_
    simp only [Prod.snd_add, Pi.sub_apply]
    rw [intervalIntegral.integral_sub
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2 (G.integrableOn_S_sub hat hg'))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2 hg'), hgt]
    abel
  · -- the `L¹(a,b; D(A))` branch
    refine ⟨fun t => ∫ s in a..t, G.S (t - s) (H s), G.continuousOn_conv hH, fun t ht => ?_⟩
    have hae : ∀ᵐ s ∂(volume.restrict (Ioc a t)), (F s, H s) ∈ G.generator.graph := by
      rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))] at hD
      refine ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht.2) ?_
      filter_upwards [hD] with s ⟨hs, e⟩
      exact Evolution.mem_graph_iff_exists.2 ⟨hs, e⟩
    exact G.conv_mem_graph ht.1 ((hFc.integrableOn_Icc).mono_set
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))) (hH.mono_set
      (Ioc_subset_Ioc_right ht.2)) hae

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

end Generator

end C0Semigroup

/-! ### Mild solutions -/

namespace Evolution

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]

/-- **Duhamel's formula**: the mild solution of `U' = A U + F`, `U a = U₀`, for the propagator
`S`: `mild S a U₀ F t = S(t - a) U₀ + ∫ₐᵗ S(t - s) F(s) ds`. -/
def mild (S : ℝ → E →L[𝕜] E) (a : ℝ) (U₀ : E) (F : ℝ → E) (t : ℝ) : E :=
  S (t - a) U₀ + ∫ s in a..t, S (t - s) (F s)

theorem mild_self {S : ℝ → E →L[𝕜] E} (hS : S 0 = 1) (a : ℝ) (U₀ : E) (F : ℝ → E) :
    mild S a U₀ F a = U₀ := by
  simp [mild, hS]

end Evolution

namespace C0Semigroup

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E)

omit [CompleteSpace E] [IsScalarTower ℝ 𝕜 E] in
@[simp] theorem mild_self (a : ℝ) (U₀ : E) (F : ℝ → E) : Evolution.mild G.S a U₀ F a = U₀ :=
  Evolution.mild_self G.map_zero a U₀ F

/-- `A ∫ₐᵗ v = v t - ∫ₐᵗ F` for the Duhamel term `v t = ∫ₐᵗ S(t - s) F(s) ds`. -/
theorem integral_conv_mem_graph {F : ℝ → E} {a t : ℝ} (hat : a ≤ t)
    (hF : IntegrableOn F (Ioc a t)) :
    (∫ s in a..t, ∫ r in a..s, G.S (s - r) (F r),
      (∫ r in a..t, G.S (t - r) (F r)) - ∫ r in a..t, F r) ∈ G.generator.graph := by
  obtain ⟨C, hC0, hC⟩ := G.exists_bound_extS (t - a)
  have h1 : ∫ s in a..t, ∫ r in a..s, G.S (s - r) (F r) =
      ∫ s in a..t, ∫ r in a..s, G.extS (s - r) (F r) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hat] at hs
    exact G.integral_S_sub_eq_extS hs.1
  have h2 := Evolution.integral_integral_triangle_swap (k := fun s r => G.extS (s - r) (F r))
    (g := fun r => C * ‖F r‖) hat
    (G.continuous_extS_uncurry.comp_aestronglyMeasurable
      (((continuous_fst.sub continuous_snd).aestronglyMeasurable).prodMk
        hF.aestronglyMeasurable.comp_snd))
    (hF.norm.const_mul C) fun s hs r hr =>
      ((G.extS _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC _ (by linarith [hs.2, hr.1]))
        (norm_nonneg _))
  have h3 : ∫ r in a..t, ∫ s in r..t, G.extS (s - r) (F r) =
      ∫ r in a..t, ∫ σ in (0 : ℝ)..t - r, G.S σ (F r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hat] at hr
    rw [intervalIntegral.integral_comp_sub_right (fun σ => G.extS σ (F r)) r, sub_self,
      G.integral_extS_eq (sub_nonneg.2 hr.2)]
  rw [h1, h2, h3]
  obtain ⟨C', hC'0, hC'⟩ := G.exists_bound_extS (t - a)
  have hΦ : Continuous fun p : ℝ × E => ∫ σ in (0 : ℝ)..p.1, G.extS σ p.2 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × E) (σ : ℝ) => G.extS σ p.2)
      (G.continuous_extS_uncurry.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
      continuous_fst
  have hΨi : IntegrableOn (fun r => ∫ σ in (0 : ℝ)..t - r, G.S σ (F r)) (Ioc a t) := by
    refine Integrable.mono' ((hF.norm.const_mul (C' * (t - a)))) ?_ ?_
    · have hc : Continuous fun r : ℝ => t - r := continuous_const.sub continuous_id
      refine (hΦ.comp_aestronglyMeasurable
        ((hc.aestronglyMeasurable).prodMk hF.aestronglyMeasurable)).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact G.integral_extS_eq (sub_nonneg.2 hr.2) (F r)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [← G.integral_extS_eq (sub_nonneg.2 hr.2)]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C' * ‖F r‖)
        fun σ hσ => ?_).trans ?_
      · exact ((G.extS σ).le_opNorm _).trans (mul_le_mul_of_nonneg_right
          (hC' σ (by rw [uIoc_of_le (sub_nonneg.2 hr.2)] at hσ; linarith [hσ.2, hr.1]))
          (norm_nonneg _))
      · rw [sub_zero, abs_of_nonneg (sub_nonneg.2 hr.2)]
        have : t - r ≤ t - a := by linarith [hr.1]
        calc C' * ‖F r‖ * (t - r) ≤ C' * ‖F r‖ * (t - a) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = C' * (t - a) * ‖F r‖ := by ring
  have := Evolution.integral_mem_graph_of_isClosed G.isClosed_generator hat hΨi
    ((G.integrableOn_S_sub hat hF).sub hF) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact G.integral_mem_graph_S (sub_nonneg.2 hr.2) (F r))
  convert this using 2
  simp only [Pi.sub_apply]
  rw [intervalIntegral.integral_sub
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2 (G.integrableOn_S_sub hat hF))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2 hF)]

/-- **Duhamel's formula gives a classical solution**: for `U₀ ∈ D(A)` and admissible forcing
`F ∈ C([a,b]; E) ∩ (W^{1,1}(a,b; E) ∪ L¹(a,b; D(A)))`, the mild solution
`t ↦ S(t - a) U₀ + ∫ₐᵗ S(t - s) F(s) ds` is a classical solution of `U' = A U + F` on `[a,b]`.
Thesis: Thm 4.3 (existence). Cf. [Pazy1983], Thm 4.2.4, Cor 4.2.5. -/
theorem isClassicalSolution_mild {U₀ : E} (hU₀ : U₀ ∈ G.generator.domain) {F : ℝ → E} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible G.generator a b F) :
    Evolution.IsClassicalSolution G.generator (Icc a b) F (Evolution.mild G.S a U₀ F) := by
  obtain ⟨V, hVc, hV⟩ := G.integral_mem_graph hF
  have hFc := hF.1
  set v : ℝ → E := fun t => ∫ s in a..t, G.S (t - s) (F s) with hv
  -- `v t = ∫ₐᵗ (V + F)` on `[a,b]`
  have key : ∀ t ∈ Icc a b, v t = ∫ s in a..t, (V s + F s) := by
    intro t ht
    have hFt : IntegrableOn F (Ioc a t) := (hFc.integrableOn_Icc).mono_set
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))
    have hvc : ContinuousOn v (Icc a t) :=
      (G.continuousOn_conv (g := F) hFt)
    have hVt : ContinuousOn V (Icc a t) := hVc.mono (Icc_subset_Icc_right ht.2)
    have hA := G.integral_conv_mem_graph ht.1 hFt
    have hB := Evolution.integral_mem_graph_of_isClosed G.isClosed_generator ht.1
      (f := v) (H := V) (hvc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hVt.integrableOn_Icc.mono_set Ioc_subset_Icc_self) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hV s ⟨hs.1.le, hs.2.trans ht.2⟩)
    have e := LinearPMap.mem_graph_snd_inj G.generator hA hB rfl
    rw [intervalIntegral.integral_add
      ((intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2 hVt.integrableOn_Icc)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2
        ((hFc.mono (Icc_subset_Icc_right ht.2)).integrableOn_Icc)), ← e]
    simp [hv]
  have hvd : ∀ t ∈ Icc a b, HasDerivWithinAt v (V t + F t) (Icc a b) t := fun t ht =>
    (Evolution.hasDerivWithinAt_integral_of_continuousOn (hVc.add hFc) ht).congr_of_mem key ht
  -- the homogeneous part
  have hh : ∀ t ∈ Icc a b, HasDerivWithinAt (fun τ => G.S (τ - a) U₀)
      (G.S (t - a) (G.generator ⟨U₀, hU₀⟩)) (Icc a b) t := by
    intro t ht
    have h1 := G.hasDerivWithinAt_apply ⟨U₀, hU₀⟩ (sub_nonneg.2 ht.1)
    have h2 : HasDerivWithinAt (fun τ : ℝ => τ - a) 1 (Icc a b) t :=
      ((hasDerivAt_id t).sub_const a).hasDerivWithinAt
    have := HasDerivWithinAt.scomp (h := fun τ : ℝ => τ - a) t h1 h2
      fun τ (hτ : τ ∈ Icc a b) => (sub_nonneg.2 hτ.1 : (0 : ℝ) ≤ τ - a)
    rwa [one_smul] at this
  have hhc : ContinuousOn (fun t => G.S (t - a) (G.generator ⟨U₀, hU₀⟩)) (Icc a b) :=
    (G.strongCont _).comp (continuousOn_id.sub continuousOn_const)
      fun t (ht : t ∈ Icc a b) => (sub_nonneg.2 ht.1 : (0 : ℝ) ≤ t - a)
  have hgraph : ∀ t ∈ Icc a b, (Evolution.mild G.S a U₀ F t,
      G.S (t - a) (G.generator ⟨U₀, hU₀⟩) + V t) ∈ G.generator.graph := fun t ht => by
    convert G.generator.graph.add_mem (G.S_mem_graph (G.generator.mem_graph ⟨U₀, hU₀⟩)
      (sub_nonneg.2 ht.1)) (hV t ht) using 1
    simp only [Evolution.mild, Prod.mk_add_mk]
  refine ⟨Evolution.IsStrongSolution.of_deriv fun t ht => ⟨_, hgraph t ht, ?_⟩,
    _, hhc.add hVc, hgraph⟩
  have := (hh t ht).add (hvd t ht)
  rw [← add_assoc] at this
  exact this.congr_of_mem (fun τ _ => rfl) ht

/-- **Every strong solution is the mild solution**: if `U` is a strong solution of
`U' = A U + F` on `[a,b]` with `F` continuous, then `U t = S(t - a) U(a) + ∫ₐᵗ S(t - s) F(s) ds`
on `[a,b]`. Proof: `s ↦ S(t - s) U(s)` has derivative `S(t - s) F(s)` on `(a,t)`.
Cf. [Pazy1983], Thm 4.1.3. -/
theorem _root_.Feec.Evolution.IsStrongSolution.eq_mild {G : C0Semigroup 𝕜 E} {F U : ℝ → E}
    {a b : ℝ} (hU : Evolution.IsStrongSolution G.generator (Icc a b) F U)
    (hF : ContinuousOn F (Icc a b)) : ∀ t ∈ Icc a b, U t = Evolution.mild G.S a (U a) F t := by
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  set φ : ℝ → E := fun s => G.extS (t - s) (U s)
  have hφc : ContinuousOn φ (Icc a t) :=
    G.continuous_extS_uncurry.comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).prodMk (hU.continuousOn.mono hsub))
  have hφd : ∀ s ∈ Ioo a t, HasDerivWithinAt φ (G.extS (t - s) (F s)) (Ioi s) s := by
    intro s hs
    have hs' : s ∈ Ico a b := ⟨hs.1.le, hs.2.trans_le ht.2⟩
    have hy := (hU.hasDerivWithinAt_Ici hs').mono Ioi_subset_Ici_self
    have hφ' : HasDerivWithinAt (fun σ : ℝ => t - σ) (-1) (Ioi s) s :=
      ((hasDerivAt_id s).const_sub t).hasDerivWithinAt
    have hD := G.hasDerivAt_extS_apply ⟨U s, hU.mem_domain (Ico_subset_Icc_self hs')⟩
      (sub_pos.2 hs.2)
    have := G.hasDerivWithinAt_extS_comp hy hφ' hD
    refine this.congr_deriv ?_
    rw [G.extS_of_nonneg (sub_pos.2 hs.2).le, _root_.map_add, neg_one_smul]
    abel
  have hint : IntervalIntegrable (fun s => G.extS (t - s) (F s)) volume a t :=
    G.intervalIntegrable_extS_comp (T := t - a) (φ := fun s => t - s)
      ((hF.mono hsub).intervalIntegrable_of_Icc ht.1) (continuous_const.sub continuous_id)
      fun s hs => by rw [uIcc_of_le ht.1] at hs; linarith [hs.1]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 hφc hφd hint
  simp only [φ, sub_self, G.extS_of_nonneg le_rfl, S_zero_apply,
    G.extS_of_nonneg (sub_nonneg.2 ht.1)] at hftc
  rw [Evolution.mild, G.integral_S_sub_eq_extS ht.1, hftc]
  abel

end C0Semigroup

end Feec
