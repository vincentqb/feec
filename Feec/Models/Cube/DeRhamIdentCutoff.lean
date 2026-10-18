module

public import Feec.Models.Cube.DeRhamIdentExt

/-!
# Cut-off approximation on `Q = (0, ½)ᵈ`: traces of smooth forms

A smooth field on `ℝᵈ` (bounded, with bounded first derivatives) restricts to an element of the
minimal domain of a first-order constant-coefficient operator `A` on `Q = (0, ½)ᵈ` as soon as the
cut-offs `χ_m ψ` (`χ_m = ∏ᵢ η_m(yᵢ)`, equal to `1` at distance `≥ 1/m` from the faces) have
uniformly bounded `A (χ_m ψ)` on `Q` (`mem_closure_testGraph_of_cutoff`): `χ_m ψ → ψ` and
`A (χ_m ψ) → A ψ` pointwise on `Q`, dominated. The bound comes from the commutator estimate
`|∂_c χ_m · f| ≤ 4 M₀ L` for `f` vanishing on the faces `{y_c ∈ {0, ½}}` (`abs_fderiv_chi_mul_le`;
a function vanishing on two opposite faces is `O(dist)`, `abs_le_of_faces`). For the exterior
derivative this applies when the **tangential** components vanish on the faces
(`Feec.Models.Cube.DeRhamIdent.mem_closure_extDerivOp_of_tangential`), for its formal adjoint
(minus the codifferential) when the **normal** components vanish
(`Feec.Models.Cube.DeRhamIdent.mem_closure_formalAdj_single1`).

## Main results

* `chi`, `isTest_chi_mul`, `eventually_chi_eq_one`, `abs_fderiv_chi_le`; `abs_le_of_faces`,
  `abs_fderiv_chi_mul_le`, `tendsto_toLp_of_bdd`.
* `apply_congr_of_eventuallyEq`; **`mem_closure_testGraph_of_cutoff`**.

## References

* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.4 (`W₀^{1,p}`, cut-off arguments)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §6.2 (vanishing tangential and
  normal traces)
-/

open scoped InnerProductSpace ContDiff Topology
open Set MeasureTheory Filter

@[expose] public noncomputable section

namespace Feec.Models.Cube.DeRhamIdent

open Geometry
open RowWise (mN mN_pos eta eta_nonneg eta_le_one abs_eta_le_one contDiff_eta eta_eq_zero_of_ne
  eta_eq_one abs_deriv_eta_mul_le exists_bound_deriv_smoothTransition)

variable {d : Type*} [Fintype d]

/-! ### The cut-off on `Q` -/

/-- The cut-off on `Q`: `χ_m(y) = ∏ᵢ η_m(yᵢ)`. -/
def chi (m : ℕ) (y : d → ℝ) : ℝ := ∏ i, eta m (y i)

theorem contDiff_chi (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (chi (d := d) m) :=
  contDiff_prod fun i _ => (contDiff_eta m).comp (contDiff_apply ℝ (fun _ : d => ℝ) i)

theorem abs_chi_le_one (m : ℕ) (y : d → ℝ) : |chi m y| ≤ 1 := by
  rw [chi, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => abs_eta_le_one m _

/-- The closed box `[1/(2m), ½ - 1/(2m)]ᵈ` containing the support of `χ_m`. -/
def chiBox (m : ℕ) : Set (d → ℝ) :=
  univ.pi fun _ => Icc (1 / (2 * mN m)) (1 / 2 - 1 / (2 * mN m))

theorem support_chi_subset (m : ℕ) : Function.support (chi (d := d) m) ⊆ chiBox m := by
  intro y hy i _
  have h : chi m y ≠ 0 := hy
  have hi : eta m (y i) ≠ 0 := fun h0 => h (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  exact ⟨(eta_eq_zero_of_ne hi).1.le, (eta_eq_zero_of_ne hi).2.le⟩

omit [Fintype d] in
theorem isCompact_chiBox (m : ℕ) : IsCompact (chiBox (d := d) m) :=
  isCompact_univ_pi fun _ => isCompact_Icc

omit [Fintype d] in
theorem chiBox_subset_Q (m : ℕ) : chiBox (d := d) m ⊆ Q d := by
  intro y hy
  refine mem_Q.2 fun i => ?_
  have hm := mN_pos m
  have h := hy i (mem_univ i)
  have hp : 0 < 1 / (2 * mN m) := by positivity
  exact ⟨hp.trans_le h.1, h.2.trans_lt (by linarith)⟩

/-- `χ_m f` is a test function on `Q` for every smooth `f`. -/
theorem isTest_chi_mul {f : (d → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : ℕ) :
    Domain.IsTest (Q d) (fun y => chi m y * f y) := by
  have hsub : Function.support (fun y => chi m y * f y) ⊆ chiBox m :=
    (Function.support_mul_subset_left _ _).trans (support_chi_subset m)
  refine ⟨((contDiff_chi m).mul hf).of_le (by exact_mod_cast le_top), ?_, ?_⟩
  · exact HasCompactSupport.intro (isCompact_chiBox m) fun y hy =>
      Function.notMem_support.1 fun h => hy (hsub h)
  · exact (closure_minimal hsub (isCompact_chiBox m).isClosed).trans (chiBox_subset_Q m)

/-- **Near each point of `Q`, `χ_m = 1` for all large `m`.** -/
theorem eventually_chi_eq_one {y : d → ℝ} (hy : y ∈ Q d) :
    ∀ᶠ m in atTop, chi (d := d) m =ᶠ[𝓝 y] fun _ => 1 := by
  have hy' := mem_Q.1 hy
  have hpos : ∀ i, 0 < min (y i) (1 / 2 - y i) := fun i =>
    lt_min (hy' i).1 (by linarith [(hy' i).2])
  obtain ⟨δ, hδ, hδi⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ min (y i) (1 / 2 - y i) := by
    by_cases he : IsEmpty d
    · exact ⟨1, one_pos, fun i => (he.false i).elim⟩
    · have hne : (Finset.univ : Finset d).Nonempty := by
        rw [Finset.univ_nonempty_iff]; exact not_isEmpty_iff.1 he
      refine ⟨Finset.univ.inf' hne fun i => min (y i) (1 / 2 - y i), ?_, fun i =>
        Finset.inf'_le _ (Finset.mem_univ i)⟩
      rw [Finset.lt_inf'_iff]
      exact fun i _ => hpos i
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  filter_upwards [eventually_ge_atTop N] with m hm
  have hmN : 2 / δ < mN m := by
    unfold mN; linarith [show (N : ℝ) ≤ m from Nat.cast_le.2 hm]
  have hmδ : 1 / mN m < δ / 2 := by
    rw [div_lt_iff₀ (mN_pos m)]
    rw [div_lt_iff₀ hδ] at hmN
    linarith
  filter_upwards [Metric.ball_mem_nhds y (by linarith : (0 : ℝ) < δ / 2)] with z hz
  rw [Metric.mem_ball] at hz
  have hzi : ∀ i, 1 / mN m ≤ z i ∧ z i ≤ 1 / 2 - 1 / mN m := by
    intro i
    have hd : |z i - y i| < δ / 2 := by
      have := (dist_le_pi_dist z y i).trans_lt hz
      rwa [Real.dist_eq] at this
    rw [abs_lt] at hd
    have h1 := (hδi i).trans (min_le_left _ _)
    have h2 := (hδi i).trans (min_le_right _ _)
    constructor <;> linarith
  simp only [chi]
  exact Finset.prod_eq_one fun i _ => eta_eq_one (hzi i).1 (hzi i).2

variable [DecidableEq d]

omit [Fintype d] in
theorem single_eq_smul (k : d) (t : ℝ) :
    (Pi.single k t : d → ℝ) = t • (Pi.single k (1 : ℝ) : d → ℝ) := by
  funext j; by_cases h : j = k
  · subst h; simp
  · simp [h]

/-- Line derivative: `d/dt f(x + t e_k) = ∂_k f (x + t e_k)`. -/
theorem hasDerivAt_line {f : (d → ℝ) → ℝ} (hf : Differentiable ℝ f) (x : d → ℝ) (k : d) (t : ℝ) :
    HasDerivAt (fun s => f (x + Pi.single k s))
      (fderiv ℝ f (x + Pi.single k t) (Pi.single k 1)) t := by
  have hl : HasDerivAt (fun s : ℝ => x + Pi.single k s) (Pi.single k 1) t := by
    have : (fun s : ℝ => x + Pi.single k s) = fun s => x + s • (Pi.single k (1 : ℝ) : d → ℝ) := by
      funext s; rw [single_eq_smul k s]
    rw [this]
    simpa using ((hasDerivAt_id t).smul_const (Pi.single k (1 : ℝ) : d → ℝ)).const_add x
  exact (hf _).hasFDerivAt.comp_hasDerivAt t hl

/-- **The derivative of the cut-off**: `|∂_c χ_m(y)| ≤ |η_m'(y_c)|`. -/
theorem abs_fderiv_chi_le (m : ℕ) (c : d) (y : d → ℝ) :
    |fderiv ℝ (chi m) y (Pi.single c 1)| ≤ |deriv (eta m) (y c)| := by
  have hd : ∀ s, HasDerivAt (eta m) (deriv (eta m) s) s := fun s =>
    ((contDiff_eta m).differentiable (by simp) s).hasDerivAt
  have hl := hasDerivAt_line ((contDiff_chi (d := d) m).differentiable (by simp)) y c 0
  rw [Pi.single_zero, add_zero] at hl
  set R : ℝ := ∏ i ∈ Finset.univ.erase c, eta m (y i)
  have e : (fun s => chi m (y + Pi.single c s)) = fun s => eta m (y c + s) * R := by
    funext s
    rw [chi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c)]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun i hi => by
        simp [Finset.ne_of_mem_erase hi]
  have h2 : HasDerivAt (fun s => eta m (y c + s) * R) (deriv (eta m) (y c) * R) 0 := by
    have := (hd (y c + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add (y c))
    simp only [add_zero, mul_one] at this
    exact this.mul_const R
  rw [e] at hl
  rw [hl.unique h2, abs_mul]
  have hR : |R| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => abs_eta_le_one m _
  calc |deriv (eta m) (y c)| * |R| ≤ |deriv (eta m) (y c)| * 1 :=
        mul_le_mul_of_nonneg_left hR (abs_nonneg _)
    _ = _ := mul_one _

/-- **Vanishing on two opposite faces with a bounded normal derivative**: if `f = 0` on
`{y_c = 0}` and `{y_c = ½}` and `|∂_c f| ≤ L`, then `|f(y)| ≤ L min(y_c, ½ - y_c)` on `Q`. -/
theorem abs_le_of_faces {f : (d → ℝ) → ℝ} (hf : Differentiable ℝ f) {c : d} {L : ℝ}
    (hL : ∀ y, |fderiv ℝ f y (Pi.single c 1)| ≤ L) (h0 : ∀ y : d → ℝ, y c = 0 → f y = 0)
    (h1 : ∀ y : d → ℝ, y c = 1 / 2 → f y = 0) {y : d → ℝ} (hy : y ∈ Q d) :
    |f y| ≤ L * min (y c) (1 / 2 - y c) := by
  set g : ℝ → ℝ := fun s => f (y + Pi.single c s)
  have hg : ∀ s, HasDerivAt g (fderiv ℝ f (y + Pi.single c s) (Pi.single c 1)) s :=
    hasDerivAt_line hf y c
  have hb : ∀ s ∈ (univ : Set ℝ), ‖deriv g s‖ ≤ L := fun s _ => by
    rw [(hg s).deriv, Real.norm_eq_abs]; exact hL _
  have hd : ∀ s ∈ (univ : Set ℝ), DifferentiableAt ℝ g s := fun s _ => (hg s).differentiableAt
  have hyc := mem_Q.1 hy c
  have e0 : g 0 = f y := by simp [g]
  have ea : g (-y c) = 0 := h0 _ (by simp)
  have eb : g (1 / 2 - y c) = 0 := h1 _ (by simp)
  have m1 := convex_univ.norm_image_sub_le_of_norm_deriv_le hd hb (mem_univ (-y c)) (mem_univ 0)
  have m2 := convex_univ.norm_image_sub_le_of_norm_deriv_le hd hb (mem_univ 0)
    (mem_univ (1 / 2 - y c))
  rw [e0, ea, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, zero_sub, neg_neg,
    abs_of_pos hyc.1] at m1
  rw [e0, eb, zero_sub, Real.norm_eq_abs, abs_neg, Real.norm_eq_abs, sub_zero,
    abs_of_pos (by linarith [hyc.2] : 0 < 1 / 2 - y c)] at m2
  rcases le_total (y c) (1 / 2 - y c) with h | h
  · rw [min_eq_left h]; exact m1
  · rw [min_eq_right h]; exact m2

/-- **The commutator bound**: `|∂_c χ_m · f| ≤ 4 M₀ L` on `Q` for `f` vanishing on the faces
`y_c ∈ {0, ½}` with `|∂_c f| ≤ L`. -/
theorem abs_fderiv_chi_mul_le {M₀ : ℝ} (hM₀ : ∀ x, |deriv Real.smoothTransition x| ≤ M₀) (m : ℕ)
    {f : (d → ℝ) → ℝ} (hf : Differentiable ℝ f) {c : d} {L : ℝ}
    (hL : ∀ y, |fderiv ℝ f y (Pi.single c 1)| ≤ L)
    (hV : ∀ y : d → ℝ, (y c = 0 ∨ y c = 1 / 2) → f y = 0) {y : d → ℝ} (hy : y ∈ Q d) :
    |fderiv ℝ (chi m) y (Pi.single c 1) * f y| ≤ 4 * M₀ * L := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL y)
  have hface := abs_le_of_faces hf hL (fun z hz => hV z (Or.inl hz)) (fun z hz => hV z (Or.inr hz))
    hy
  rw [abs_mul]
  calc |fderiv ℝ (chi m) y (Pi.single c 1)| * |f y| ≤
        |deriv (eta m) (y c)| * (L * min (y c) (1 / 2 - y c)) :=
        mul_le_mul (abs_fderiv_chi_le m c y) hface (abs_nonneg _) (abs_nonneg _)
    _ = L * (|deriv (eta m) (y c)| * min (y c) (1 / 2 - y c)) := by ring
    _ ≤ L * (4 * M₀) := mul_le_mul_of_nonneg_left (abs_deriv_eta_mul_le hM₀ m (mem_Q.1 hy c)) hL0
    _ = 4 * M₀ * L := by ring

omit [DecidableEq d] in
/-- **`L²(Q)`-convergence of uniformly bounded, pointwise convergent sequences.** -/
theorem tendsto_toLp_of_bdd {g : ℕ → (d → ℝ) → ℝ} {h : (d → ℝ) → ℝ}
    (hg : ∀ m, MemLp (g m) 2 (volume.restrict (Q d))) (hh : MemLp h 2 (volume.restrict (Q d)))
    {K : ℝ} (hK : ∀ m, ∀ y ∈ Q d, |g m y| ≤ K)
    (hlim : ∀ y ∈ Q d, Tendsto (fun m => g m y) atTop (𝓝 (h y))) :
    Tendsto (fun m => (hg m).toLp (g m)) atTop (𝓝 (hh.toLp h)) := by
  have := isFiniteMeasure_Q (d := d)
  rw [tendsto_iff_edist_tendsto_0]
  simp_rw [Lp.edist_toLp_toLp]
  have hui : UnifIntegrable g 2 (volume.restrict (Q d)) := by
    refine (unifIntegrable_const (ι := ℕ) one_le_two (by norm_num)
      (memLp_const (μ := volume.restrict (Q d)) K)).ae_mono
      (fun m => (hg m).aestronglyMeasurable) fun m => ?_
    filter_upwards [ae_restrict_mem measurableSet_Q] with y hy
    rw [enorm_le_iff_norm_le, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hK m y hy).trans (le_abs_self K)
  exact tendsto_Lp_finite_of_tendsto_ae one_le_two (by norm_num)
    (fun m => (hg m).aestronglyMeasurable) hh hui
    (by filter_upwards [ae_restrict_mem measurableSet_Q] with y hy; exact hlim y hy)

omit [DecidableEq d] in
/-- Convergence in `L²(Ω; ℝ^ι)` is componentwise. -/
theorem tendsto_L2F_of_forall {Ω : Set (d → ℝ)} {ι : Type*} {u : ℕ → Domain.L2F ℝ Ω ι}
    {v : Domain.L2F ℝ Ω ι} (h : ∀ p, Tendsto (fun m => u m p) atTop (𝓝 (v p))) :
    Tendsto u atTop (𝓝 v) := by
  have hc := (PiLp.continuous_toLp 2 (fun _ : ι => Domain.L2 ℝ Ω)).tendsto (WithLp.ofLp v)
  exact hc.comp (tendsto_pi_nhds.2 h)

/-! ### The cut-off approximation for constant-coefficient operators -/

omit [DecidableEq d] in
/-- Iterated directional derivatives only see the germ. -/
theorem iterDeriv_eventuallyEq {f g : (d → ℝ) → ℝ} {y : d → ℝ} (h : f =ᶠ[𝓝 y] g)
    (vs : List (d → ℝ)) : Domain.iterDeriv vs f =ᶠ[𝓝 y] Domain.iterDeriv vs g := by
  induction vs with
  | nil => exact h
  | cons v vs ih =>
    filter_upwards [Filter.EventuallyEq.fderiv (𝕜 := ℝ) ih] with z hz
    simp only [Domain.iterDeriv_cons, hz]

omit [DecidableEq d] in
/-- **A constant-coefficient operator only sees the germ.** -/
theorem apply_congr_of_eventuallyEq {ι κ : Type*} [Fintype ι]
    (A : Domain.ConstCoeffOp (d → ℝ) ℝ ι κ) {f g : ι → (d → ℝ) → ℝ} {y : d → ℝ}
    (h : ∀ p, f p =ᶠ[𝓝 y] g p) (q : κ) : A.apply f q y = A.apply g q y := by
  simp only [Domain.ConstCoeffOp.apply, Domain.ConstCoeffOp.applyEntry]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  refine List.map_congr_left fun t _ => ?_
  rw [(iterDeriv_eventuallyEq (h p) t.1).eq_of_nhds]

omit [DecidableEq d] in
/-- **Cut-off approximation**: a smooth field `ψ` on `ℝᵈ`, bounded on `Q`, whose cut-offs
`χ_m ψ` have `A (χ_m ψ)` uniformly bounded on `Q`, restricts to an element of the minimal domain
of `A` on `Q`: `(ψ, A ψ)` lies in the closure of the graph of `A` on `C_c^∞(Q)`. -/
theorem mem_closure_testGraph_of_cutoff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Domain.ConstCoeffOp (d → ℝ) ℝ ι κ) {ψ : ι → (d → ℝ) → ℝ}
    (hψ : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (ψ p)) {M : ℝ} (hM : ∀ p, ∀ y ∈ Q d, |ψ p y| ≤ M)
    (hψL : ∀ p, MemLp (ψ p) 2 (volume.restrict (Q d)))
    (hAψL : ∀ q, MemLp (A.apply ψ q) 2 (volume.restrict (Q d))) {K : ℝ}
    (hK : ∀ m q, ∀ y ∈ Q d, |A.apply (fun p y => chi m y * ψ p y) q y| ≤ K) :
    (Domain.toL2F hψL, Domain.toL2F hAψL) ∈
      closure (A.testGraph (Q d) : Set (Domain.L2F ℝ (Q d) ι × Domain.L2F ℝ (Q d) κ)) := by
  set Φ : ℕ → ι → (d → ℝ) → ℝ := fun m p y => chi m y * ψ p y
  have hΦ : ∀ m, Domain.IsTestField (Q d) (Φ m) := fun m p => isTest_chi_mul (hψ p) m
  have hev : ∀ y ∈ Q d, ∀ᶠ m in atTop, ∀ p, (Φ m p) =ᶠ[𝓝 y] ψ p := fun y hy => by
    filter_upwards [eventually_chi_eq_one hy] with m hm p
    filter_upwards [hm] with z hz
    simp [Φ, hz]
  refine mem_closure_of_tendsto (b := (atTop : Filter ℕ))
    (f := fun m => (Domain.testField (hΦ m), Domain.testField (A.isTestField_apply (hΦ m)))) ?_
    (Filter.Eventually.of_forall fun m => ⟨Φ m, hΦ m, rfl⟩)
  refine Tendsto.prodMk_nhds (tendsto_L2F_of_forall fun p => ?_)
    (tendsto_L2F_of_forall fun q => ?_)
  · refine tendsto_toLp_of_bdd (fun m => (hΦ m p).memLp) (hψL p) (K := M)
      (fun m y hy => ?_) fun y hy => ?_
    · simp only [Φ, abs_mul]
      calc |chi m y| * |ψ p y| ≤ 1 * M :=
            mul_le_mul (abs_chi_le_one m y) (hM p y hy) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev y hy] with m hm
      exact (hm p).eq_of_nhds.symm
  · refine tendsto_toLp_of_bdd (fun m => (A.isTestField_apply (hΦ m) q).memLp) (hAψL q) (K := K)
      (fun m y hy => hK m q y hy) fun y hy => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev y hy] with m hm
    exact (apply_congr_of_eventuallyEq A hm q).symm

end Feec.Models.Cube.DeRhamIdent
