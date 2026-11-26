module

public import Feec.Semigroup.DissipativeInvariance
public import Feec.Evolution.WellPosed
public import Feec.Evolution.Energy
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The dissipative FEEC theorem

The FEEC theorem for `ξ' = A ξ` with `A` m-dissipative, discretized by bounded dissipative
generators on Hilbert spaces read through uniformly bounded maps, with consistency tested along the
exact orbits as in the Trotter–Kato theorem ([Pazy1983], §3.4).

## Main results

* `norm_sub_le_of_defect_of_dissipative`: best approximation plus integrated consistency defect.
* `dissipFEEC`: the dissipative FEEC theorem.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

/-! ### The energy estimate for dissipative bounded generators -/

section Defect

variable {𝕜 : Type*} [RCLike 𝕜] {X E : Type*}
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X] [NormedSpace ℝ X]
  [IsScalarTower ℝ 𝕜 X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **The consistency estimate**: for a bounded dissipative `L` and a comparison trajectory `p`,
`‖u(t) - ι e^{tL} p(0)‖ ≤ ‖u(t) - ι p(t)‖ + ‖ι‖ ∫₀ᵗ ‖p' - L p‖`. -/
theorem norm_sub_le_of_defect_of_dissipative (L : X →L[𝕜] X)
    (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) (ι : X →L[𝕜] E) {u : ℝ → E} {p p' : ℝ → X} {T : ℝ}
    (hpc : ContinuousOn p (Icc 0 T)) (hp'c : ContinuousOn p' (Icc 0 T))
    (hp : ∀ t ∈ Ico 0 T, HasDerivWithinAt p (p' t) (Ici t) t) :
    ∀ t ∈ Icc 0 T, ‖u t - ι ((C0Group.ofBounded L).S t (p 0))‖ ≤
      ‖u t - ι (p t)‖ + ‖ι‖ * ∫ s in (0 : ℝ)..t, ‖p' s - L (p s)‖ := by
  set G := C0Group.ofBounded L
  set e : ℝ → X := fun t => p t - G.S t (p 0)
  have hGd : ∀ t, HasDerivAt (fun s => G.S s (p 0)) (L (G.S t (p 0))) t := fun t =>
    ContinuousLinearMap.hasDerivAt_exp_ofReal_smul_apply L (p 0) t
  have hec : ContinuousOn e (Icc 0 T) :=
    hpc.sub (fun t _ => (hGd t).continuousAt.continuousWithinAt)
  have hed : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (p' t - L (G.S t (p 0))) (Ici t) t :=
    fun t ht => (hp t ht).sub (hGd t).hasDerivWithinAt
  have hgc : ContinuousOn (fun s => ‖p' s - L (p s)‖) (Icc 0 T) :=
    (hp'c.sub (L.continuous.comp_continuousOn hpc)).norm
  have hle : ∀ t ∈ Ico 0 T, RCLike.re ⟪p' t - L (G.S t (p 0)), e t⟫_𝕜 ≤
      ‖p' t - L (p t)‖ * ‖e t‖ := by
    intro t _
    have hsplit : p' t - L (G.S t (p 0)) = (p' t - L (p t)) + L (e t) := by
      simp only [e, _root_.map_sub]; abel
    rw [hsplit, inner_add_left, _root_.map_add]
    have h1 : RCLike.re ⟪p' t - L (p t), e t⟫_𝕜 ≤ ‖p' t - L (p t)‖ * ‖e t‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    linarith [hL (e t)]
  have hE := Evolution.Energy.norm_le_add_integral_of_re_inner_deriv_le (𝕜 := 𝕜) hec hed hgc
    (fun _ _ => norm_nonneg _) hle
  intro t ht
  have h0 : e 0 = 0 := by simp [e, G]
  have he := hE t ht
  rw [h0, norm_zero, zero_add] at he
  calc ‖u t - ι (G.S t (p 0))‖ = ‖(u t - ι (p t)) + ι (e t)‖ := by
        simp only [e, _root_.map_sub]; abel_nf
    _ ≤ ‖u t - ι (p t)‖ + ‖ι‖ * ‖e t‖ := (norm_add_le _ _).trans (by gcongr; exact ι.le_opNorm _)
    _ ≤ _ := by gcongr

theorem norm_ofBounded_apply_le (L : X →L[𝕜] X) (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {t : ℝ}
    (ht : 0 ≤ t) (x : X) : ‖(C0Group.ofBounded L).S t x‖ ≤ ‖x‖ := by
  rw [C0Group.ofBounded_S]; exact LumerPhillips.norm_exp_smul_apply_le hL ht x

end Defect

/-! ### Uniform convergence on compact sets -/

section Compact

theorem eventually_forall_lt_of_tendsto {κ F : Type*} [SeminormedAddCommGroup F] {l : Filter κ}
    {f : κ → F → ℝ} {M : ℝ} (hf : ∀ h ζ ζ', f h ζ ≤ f h ζ' + M * ‖ζ - ζ'‖)
    (hlim : ∀ ζ, Tendsto (fun h => f h ζ) l (𝓝 0)) {S : Set F} (hS : IsCompact S) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ h in l, ∀ ζ ∈ S, f h ζ < ε := by
  set M' := max M 0
  have hM' : 0 ≤ M' := le_max_right _ _
  set δ := ε / (2 * (M' + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨t, -, htf, hcov⟩ := hS.finite_cover_balls hδ
  have hev : ∀ᶠ h in l, ∀ z ∈ t, f h z < ε / 2 :=
    (htf.eventually_all).2 fun z _ => (tendsto_order.1 (hlim z)).2 _ (half_pos hε)
  filter_upwards [hev] with h hh ζ hζ
  obtain ⟨z, hz, hζz⟩ := mem_iUnion₂.1 (hcov hζ)
  rw [Metric.mem_ball, dist_eq_norm] at hζz
  have h1 := hf h ζ z
  have h2 : M * ‖ζ - z‖ ≤ M' * δ :=
    (mul_le_mul_of_nonneg_right (le_max_left M 0) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hζz.le hM')
  have h3 : M' * δ < ε / 2 := by
    have e : M' * δ = ε / 2 * (M' / (M' + 1)) := by
      simp only [δ]; field_simp
    rw [e]
    have : M' / (M' + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    nlinarith
  linarith [hh z hz]

theorem eventually_forall_norm_lt_of_tendsto {𝕜 κ F : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {G : κ → Type*}
    [∀ h, SeminormedAddCommGroup (G h)] [∀ h, NormedSpace 𝕜 (G h)] {l : Filter κ}
    {A : ∀ h, F →L[𝕜] G h} {M : ℝ} (hM : ∀ h ζ, ‖A h ζ‖ ≤ M * ‖ζ‖)
    (hlim : ∀ ζ, Tendsto (fun h => ‖A h ζ‖) l (𝓝 0)) {S : Set F} (hS : IsCompact S) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ h in l, ∀ ζ ∈ S, ‖A h ζ‖ < ε :=
  eventually_forall_lt_of_tendsto (M := M) (fun h ζ ζ' => by
    have e : A h ζ = A h ζ' + A h (ζ - ζ') := by rw [_root_.map_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans (by linarith [hM h (ζ - ζ')])) hlim hS hε

theorem tendstoUniformlyOn_apply_of_tendsto {𝕜 κ F G : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {l : Filter κ} {P : κ → F →L[𝕜] G} {P₀ : F →L[𝕜] G} (hP : ∃ C, ∀ h, ‖P h‖ ≤ C)
    (hlim : ∀ ζ, Tendsto (fun h => P h ζ) l (𝓝 (P₀ ζ))) {f : ℝ → F} {S : Set ℝ}
    (hf : IsCompact (f '' S)) :
    TendstoUniformlyOn (fun h t => P h (f t)) (fun t => P₀ (f t)) l S := by
  obtain ⟨C, hC⟩ := hP
  have hB : ∀ h ζ, ‖(P₀ - P h) ζ‖ ≤ (‖P₀‖ + C) * ‖ζ‖ := fun h ζ =>
    ((P₀ - P h).le_opNorm ζ).trans (mul_le_mul_of_nonneg_right
      ((norm_sub_le _ _).trans (add_le_add_right (hC h) _)) (norm_nonneg _))
  have hB0 : ∀ ζ, Tendsto (fun h => ‖(P₀ - P h) ζ‖) l (𝓝 0) := fun ζ =>
    (tendsto_iff_norm_sub_tendsto_zero.1 (hlim ζ)).congr fun h => norm_sub_rev _ _
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_forall_norm_lt_of_tendsto hB hB0 hf hε] with h hh t ht
  simpa [dist_eq_norm] using hh _ (mem_image_of_mem _ ht)

theorem tendstoUniformlyOn_norm_of_le {𝕜 κ F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] {G D : κ → Type*} [∀ h, SeminormedAddCommGroup (G h)]
    [∀ h, NormedSpace 𝕜 (G h)] [∀ h, SeminormedAddCommGroup (D h)] {l : Filter κ}
    {Δ Δ' : ∀ h, F →L[𝕜] G h} (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hΔ0 : ∀ ζ, Tendsto (fun h => ‖Δ h ζ‖) l (𝓝 0))
    (hΔ'0 : ∀ ζ, Tendsto (fun h => ‖Δ' h ζ‖) l (𝓝 0)) {f g : ℝ → F} {S : Set ℝ}
    (hf : IsCompact (f '' S)) (hg : IsCompact (g '' S)) {d : ∀ h, ℝ → D h}
    (hd : ∀ h, ∀ t ∈ S, ‖d h t‖ ≤ ‖Δ h (f t)‖ + ‖Δ' h (g t)‖) :
    TendstoUniformlyOn (fun h t => ‖d h t‖) (fun _ => 0) l S := by
  obtain ⟨C, hC⟩ := hΔ
  have hb : ∀ B : ∀ h, F →L[𝕜] G h, (∀ h, ‖B h‖ ≤ C) → ∀ h ζ, ‖B h ζ‖ ≤ C * ‖ζ‖ :=
    fun B hB h ζ => ((B h).le_opNorm ζ).trans (mul_le_mul_of_nonneg_right (hB h) (norm_nonneg _))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_forall_norm_lt_of_tendsto (hb Δ fun h => (hC h).1) hΔ0 hf
      (half_pos hε),
    eventually_forall_norm_lt_of_tendsto (hb Δ' fun h => (hC h).2) hΔ'0 hg (half_pos hε)]
    with h h1 h2 t ht
  rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg (norm_nonneg _)]
  linarith [hd h t ht, h1 _ (mem_image_of_mem _ ht), h2 _ (mem_image_of_mem _ ht)]

theorem integral_le_mul_of_norm_le {g : ℝ → ℝ} {t M : ℝ} (ht : 0 ≤ t)
    (hg : ∀ s ∈ Icc 0 t, ‖g s‖ ≤ M) : ∫ s in (0 : ℝ)..t, g s ≤ M * t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (f := g)
    (C := M) fun s hs => hg s (Ioc_subset_Icc_self (by rwa [uIoc_of_le ht] at hs))
  rw [sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

end Compact

/-! ### Dissipative FEEC discretizations -/

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A **dissipative FEEC discretization** of `ξ' = A ξ`, `A` m-dissipative. -/
structure DissipFEEC (A : E →ₗ.[𝕜] E) (κ : Type*) where
  /-- the generator is m-dissipative -/
  isMDissipative : A.IsMDissipative
  /-- the constraint subspace -/
  K : Submodule 𝕜 E
  isClosed_K : IsClosed (K : Set E)
  /-- the filter of refinement -/
  l : Filter κ
  /-- the discrete spaces -/
  X : κ → Type u
  [normedAddCommGroup : ∀ h, NormedAddCommGroup (X h)]
  [innerProductSpace : ∀ h, InnerProductSpace 𝕜 (X h)]
  [completeSpace : ∀ h, CompleteSpace (X h)]
  [normedSpaceReal : ∀ h, NormedSpace ℝ (X h)]
  [isScalarTower : ∀ h, IsScalarTower ℝ 𝕜 (X h)]
  /-- the discrete generators -/
  L : ∀ h, X h →L[𝕜] X h
  dissipative : ∀ h x, RCLike.re ⟪L h x, x⟫_𝕜 ≤ 0
  /-- the reading maps -/
  incl : ∀ h, X h →L[𝕜] E
  /-- their left inverses -/
  proj : ∀ h, E →L[𝕜] X h
  proj_incl : ∀ h x, proj h (incl h x) = x
  bound : ∃ C, ∀ h, ‖incl h‖ ≤ C ∧ ‖proj h‖ ≤ C

attribute [instance] DissipFEEC.normedAddCommGroup DissipFEEC.innerProductSpace
  DissipFEEC.completeSpace DissipFEEC.normedSpaceReal DissipFEEC.isScalarTower

namespace DissipFEEC

variable {A : E →ₗ.[𝕜] E} {κ : Type*} (F : DissipFEEC.{u} A κ)

instance [CompleteSpace E] : CompleteSpace F.K := F.isClosed_K.completeSpace_coe

instance [CompleteSpace E] : F.K.HasOrthogonalProjection := .ofCompleteSpace _

/-- A nonnegative uniform bound of `‖ιₕ‖`, `‖πₕ‖`. -/
def boundConst : ℝ := max F.bound.choose 0

theorem boundConst_nonneg : 0 ≤ F.boundConst := le_max_right _ _

theorem norm_incl_le (h : κ) : ‖F.incl h‖ ≤ F.boundConst :=
  (F.bound.choose_spec h).1.trans (le_max_left _ _)

theorem norm_proj_le (h : κ) : ‖F.proj h‖ ≤ F.boundConst :=
  (F.bound.choose_spec h).2.trans (le_max_left _ _)

theorem norm_le_norm_incl (h : κ) (v : F.X h) : ‖v‖ ≤ F.boundConst * ‖F.incl h v‖ :=
  calc ‖v‖ = ‖F.proj h (F.incl h v)‖ := by rw [F.proj_incl]
    _ ≤ ‖F.proj h‖ * ‖F.incl h v‖ := (F.proj h).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right (F.norm_proj_le h) (norm_nonneg _)

theorem norm_incl_apply_le (h : κ) (v : F.X h) : ‖F.incl h v‖ ≤ F.boundConst * ‖v‖ :=
  ((F.incl h).le_opNorm v).trans (mul_le_mul_of_nonneg_right (F.norm_incl_le h) (norm_nonneg _))

theorem bound_incl_comp {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {R : ∀ h, G →L[𝕜] F.X h} (hR : ∃ C, ∀ h, ‖R h‖ ≤ C) : ∃ C, ∀ h, ‖F.incl h ∘L R h‖ ≤ C :=
  let ⟨C, hC⟩ := hR
  ⟨F.boundConst * C, fun h => (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (F.norm_incl_le h) (hC h) (norm_nonneg _) F.boundConst_nonneg)⟩

theorem norm_incl_proj_le (h : κ) (y : E) :
    ‖F.incl h (F.proj h y)‖ ≤ F.boundConst ^ 2 * ‖y‖ := by
  have h1 := F.norm_incl_apply_le h (F.proj h y)
  have h2 := ((F.proj h).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (F.norm_proj_le h) (norm_nonneg _))
  have h0 := F.boundConst_nonneg
  calc _ ≤ F.boundConst * ‖F.proj h y‖ := h1
    _ ≤ F.boundConst * (F.boundConst * ‖y‖) := mul_le_mul_of_nonneg_left h2 h0
    _ = _ := by ring

/-- The discrete evolution `e^{t Lₕ}`. -/
def group (h : κ) : C0Group 𝕜 (F.X h) := C0Group.ofBounded (F.L h)

theorem norm_group_apply_le (h : κ) {t : ℝ} (ht : 0 ≤ t) (v : F.X h) :
    ‖(F.group h).S t v‖ ≤ ‖v‖ :=
  norm_ofBounded_apply_le (F.L h) (F.dissipative h) ht v

/-- The discrete solution `ιₕ e^{t Lₕ} v`. -/
def sol (h : κ) (v : F.X h) (t : ℝ) : E := F.incl h ((F.group h).S t v)

@[simp] theorem sol_zero (h : κ) (v : F.X h) : F.sol h v 0 = F.incl h v := by
  simp [sol, group]

theorem norm_sol_sub_sol_le (h : κ) (v w : F.X h) {t : ℝ} (ht : 0 ≤ t) :
    ‖F.sol h v t - F.sol h w t‖ ≤ ‖F.incl h‖ * ‖v - w‖ := by
  rw [sol, sol, ← _root_.map_sub, ← _root_.map_sub]
  refine ((F.incl h).le_opNorm _).trans ?_
  gcongr
  exact F.norm_group_apply_le h ht _

/-- `v` converges to `x` through the reading maps, `ιₕ vₕ → x`. -/
abbrev Converges (v : ∀ h, F.X h) (x : E) : Prop := Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x)

/-- **Comparison trajectories** `pₕ(t)` on `[0, T]`, with right derivatives `pₕ'(t)`. -/
structure Comparison (T : ℝ) where
  /-- the data -/
  Data : Set E
  /-- the comparison trajectories -/
  p : E → ∀ h, ℝ → F.X h
  /-- their derivatives -/
  p' : E → ∀ h, ℝ → F.X h
  continuousOn : ∀ x ∈ Data, ∀ h, ContinuousOn (p x h) (Icc 0 T)
  continuousOn' : ∀ x ∈ Data, ∀ h, ContinuousOn (p' x h) (Icc 0 T)
  hasDerivWithinAt : ∀ x ∈ Data, ∀ h, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (p x h) (p' x h t) (Ici t) t

variable {F} in
/-- The **consistency defect** `pₕ' - Lₕ pₕ`. -/
def Comparison.defect {T : ℝ} (P : F.Comparison T) (x : E) (h : κ) (t : ℝ) : F.X h :=
  P.p' x h t - F.L h (P.p x h t)

variable {F} in
/-- Restriction of a comparison to a subset of its data. -/
def Comparison.restrict {T : ℝ} (P : F.Comparison T) (D : Set E) (hD : D ⊆ P.Data) :
    F.Comparison T where
  Data := D
  p := P.p
  p' := P.p'
  continuousOn x hx := P.continuousOn x (hD hx)
  continuousOn' x hx := P.continuousOn' x (hD hx)
  hasDerivWithinAt x hx := P.hasDerivWithinAt x (hD hx)

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

omit [CompleteSpace E] in
theorem hasDerivAt_sol (h : κ) (v : F.X h) (t : ℝ) :
    HasDerivAt (F.sol h v) (F.incl h (F.L h ((F.group h).S t v))) t :=
  ((F.incl h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (ContinuousLinearMap.hasDerivAt_exp_ofReal_smul_apply (F.L h) v t)

/-- The **exact flow** `S(t)`: the contraction semigroup generated by `A`. -/
def S (t : ℝ) : E →L[𝕜] E := F.isMDissipative.semigroup.S t

theorem S_def (t : ℝ) : F.S t = F.isMDissipative.semigroup.S t := rfl

theorem continuousOn_S (x : E) (T : ℝ) : ContinuousOn (fun t => F.S t x) (Icc 0 T) :=
  (F.isMDissipative.semigroup.strongCont x).mono Icc_subset_Ici_self

theorem exists_sol_ne {x : E} (hx : x ∈ A.domain) (h : κ) (v : F.X h)
    (hne : F.incl h (F.L h v) ≠ A ⟨x, hx⟩) : ∃ t, 0 ≤ t ∧ F.sol h v t ≠ F.S t x := by
  by_contra hc
  push Not at hc
  have h1 : HasDerivWithinAt (fun s => F.S s x) (F.incl h (F.L h ((F.group h).S 0 v))) (Ici 0)
      0 := ((F.hasDerivAt_sol h v 0).hasDerivWithinAt).congr (fun s hs => (hc s hs).symm)
    (hc 0 le_rfl).symm
  have h2 := F.isMDissipative.hasDerivWithinAt_semigroup ⟨x, hx⟩ (le_refl 0)
  have e := (uniqueDiffWithinAt_Ici 0).eq_deriv _ h1 h2
  rw [C0Group.S_zero_apply, C0Semigroup.S_zero_apply] at e
  exact hne e

/-- `F` keeps `Q`: `S(t) Q ⊆ Q` for every `t ≥ 0`. -/
abbrev Keeps (Q : Set E) : Prop := ∀ t, 0 ≤ t → ∀ x ∈ Q, F.S t x ∈ Q

/-- `x` leaves `Q` by time `T`: `S(t) x ∉ Q` for some `t ∈ [0, T]`. -/
abbrev Leaves (x : E) (Q : Set E) (T : ℝ) : Prop := ∃ t ∈ Icc 0 T, F.S t x ∉ Q

/-- `Q` has a dense smooth part: `D(A) ∩ Q` is dense in `Q`. -/
abbrev SmoothDense (_ : DissipFEEC.{u} A κ) (Q : Set E) : Prop :=
  ∀ k ∈ Q, k ∈ closure ((A.domain : Set E) ∩ Q)

/-- A **rate class**: comparisons with approximation and consistency defect `O(hᵅ)` on `[0, T]`. -/
structure RateClass (T : ℝ) extends F.Comparison T where
  /-- the norm of the class -/
  classNorm : E → ℝ
  /-- the mesh size -/
  meshSize : κ → ℝ
  /-- the order -/
  α : ℝ
  /-- the approximation constant -/
  C : ℝ
  /-- the consistency constant -/
  C' : ℝ
  approx : ∀ x ∈ Data, ∀ h, ∀ t ∈ Icc 0 T,
    ‖F.S t x - F.incl h (p x h t)‖ ≤ C * meshSize h ^ α * classNorm x
  consistency : ∀ x ∈ Data, ∀ h, ∀ t ∈ Icc 0 T,
    ‖toComparison.defect x h t‖ ≤ C' * meshSize h ^ α * classNorm x

/-- An **orbit-consistent core**: comparisons approximating the orbits, with defects `→ 0`. -/
structure Core where
  /-- the core -/
  Data : Submodule 𝕜 E
  /-- the comparisons -/
  cmp : ∀ T : ℝ, F.Comparison T
  data_eq : ∀ T, (cmp T).Data = Data
  tendsto_approx : ∀ T, ∀ x ∈ Data, TendstoUniformlyOn
    (fun h t => F.incl h ((cmp T).p x h t)) (fun t => F.S t x) F.l (Icc 0 T)
  tendsto_defect : ∀ T, ∀ x ∈ Data, TendstoUniformlyOn
    (fun h t => ‖(cmp T).defect x h t‖) (fun _ => 0) F.l (Icc 0 T)

theorem norm_sub_sol_le {T : ℝ} (P : F.Comparison T) {x : E} (hx : x ∈ P.Data) (h : κ) :
    ∀ t ∈ Icc 0 T, ‖F.S t x - F.sol h (P.p x h 0) t‖ ≤
      ‖F.S t x - F.incl h (P.p x h t)‖ + ‖F.incl h‖ * ∫ s in (0 : ℝ)..t, ‖P.defect x h s‖ :=
  norm_sub_le_of_defect_of_dissipative (F.L h) (F.dissipative h) (F.incl h)
    (P.continuousOn x hx h) (P.continuousOn' x hx h) (P.hasDerivWithinAt x hx h)

variable {F} in
theorem Core.tendsto_incl_p (Z : F.Core) {T : ℝ} (hT : 0 ≤ T) {x : E} (hx : x ∈ Z.Data) :
    F.Converges (fun h => (Z.cmp T).p x h 0) x := by
  have h0 := (Z.tendsto_approx T x hx).tendsto_at (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
  rwa [S_def, C0Semigroup.S_zero_apply] at h0

theorem tendsto_incl_proj (Z : F.Core) {x : E} (hx : x ∈ Z.Data.topologicalClosure) :
    F.Converges (fun h => F.proj h x) x := by
  refine ContinuousLinearMap.tendsto_apply_of_mem_closure (T := fun h => F.incl h ∘L F.proj h)
    (fun h => ContinuousLinearMap.opNorm_le_bound _ (by positivity) (F.norm_incl_proj_le h))
    continuous_id' (s := Z.Data) (fun y hy => ?_) (by rwa [← Submodule.topologicalClosure_coe])
  have hb : Tendsto (fun h => (F.boundConst ^ 2 + 1) * ‖F.incl h ((Z.cmp 0).p y h 0) - y‖) F.l
      (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 (Z.tendsto_incl_p le_rfl hy)).const_mul
      (F.boundConst ^ 2 + 1)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun h => ?_) hb
  set w := F.incl h ((Z.cmp 0).p y h 0)
  have e : (F.incl h ∘L F.proj h) y - y = F.incl h (F.proj h (y - w)) - (y - w) := by
    rw [ContinuousLinearMap.comp_apply, _root_.map_sub, _root_.map_sub, F.proj_incl]; abel
  rw [e, ← norm_sub_rev y w]
  have := F.norm_incl_proj_le h (y - w)
  linarith [norm_sub_le (F.incl h (F.proj h (y - w))) (y - w)]

/-! ### The Trotter–Kato bridge -/

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
variable (A) in
open scoped Classical in
/-- `A` on `D(A)`, extended by `0`. -/
def genExt (x : E) : E :=
  if hx : x ∈ A.domain then A ⟨x, hx⟩ else 0

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem genExt_of_mem {x : E} (hx : x ∈ A.domain) : genExt A x = A ⟨x, hx⟩ := by
  unfold genExt; simp [hx]

/-- Comparison trajectories `pₕ(t) = Rₕ S(t) x` on `D(A)`, with derivatives `Rₕ S(t) A x`. -/
def Comparison.ofOperator (R : ∀ h, E →L[𝕜] F.X h) (T : ℝ) : F.Comparison T where
  Data := A.domain
  p x h t := R h (F.S t x)
  p' x h t := R h (F.S t (genExt A x))
  continuousOn x _ h := (R h).continuous.comp_continuousOn (F.continuousOn_S x T)
  continuousOn' x _ h := (R h).continuous.comp_continuousOn (F.continuousOn_S (genExt A x) T)
  hasDerivWithinAt x hx h t ht := by
    have hd := F.isMDissipative.hasDerivWithinAt_semigroup ⟨x, hx⟩ ht.1
    rw [← genExt_of_mem hx] at hd
    exact ((R h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hd

/-- **The Trotter–Kato bridge**: the core `D(A)` of `Rₕ` ([Pazy1983], §3.4). -/
def Core.ofOperator (R : ∀ h, E →L[𝕜] F.X h) (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (happrox : ∀ y, Tendsto (fun h => F.incl h (R h y)) F.l (𝓝 y))
    (Δ Δ' : ∀ h, E →L[𝕜] F.X h) (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hdef : ∀ h (y : A.domain), R h (A y) - F.L h (R h y) = Δ h (A y) + Δ' h y)
    (hΔ0 : ∀ y, Tendsto (fun h => ‖Δ h y‖) F.l (𝓝 0))
    (hΔ'0 : ∀ y, Tendsto (fun h => ‖Δ' h y‖) F.l (𝓝 0)) : F.Core where
  Data := A.domain
  cmp T := Comparison.ofOperator F R T
  data_eq _ := rfl
  tendsto_approx T x _ := tendstoUniformlyOn_apply_of_tendsto (P₀ := ContinuousLinearMap.id 𝕜 E)
    (F.bound_incl_comp hR) happrox (isCompact_Icc.image_of_continuousOn (F.continuousOn_S x T))
  tendsto_defect T x hx := tendstoUniformlyOn_norm_of_le hΔ hΔ0 hΔ'0
    (isCompact_Icc.image_of_continuousOn (F.continuousOn_S (genExt A x) T))
    (isCompact_Icc.image_of_continuousOn (F.continuousOn_S x T))
    fun h t ht => by
      have e := hdef h ⟨_, F.isMDissipative.semigroup_mem_domain ⟨x, hx⟩ ht.1⟩
      rw [F.isMDissipative.apply_semigroup ⟨x, hx⟩ ht.1] at e
      change ‖R h (F.isMDissipative.semigroup.S t (genExt A x)) -
        F.L h (R h (F.isMDissipative.semigroup.S t x))‖ ≤ _
      rw [genExt_of_mem hx, e]
      exact norm_add_le _ _

theorem Core.ofOperator_data_closure (R : ∀ h, E →L[𝕜] F.X h) (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (happrox : ∀ y, Tendsto (fun h => F.incl h (R h y)) F.l (𝓝 y))
    (Δ Δ' : ∀ h, E →L[𝕜] F.X h) (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hdef : ∀ h (y : A.domain), R h (A y) - F.L h (R h y) = Δ h (A y) + Δ' h y)
    (hΔ0 : ∀ y, Tendsto (fun h => ‖Δ h y‖) F.l (𝓝 0))
    (hΔ'0 : ∀ y, Tendsto (fun h => ‖Δ' h y‖) F.l (𝓝 0)) :
    (Core.ofOperator F R hR happrox Δ Δ' hΔ hdef hΔ0 hΔ'0).Data.topologicalClosure = ⊤ := by
  exact Submodule.dense_iff_topologicalClosure_eq_top.1 F.isMDissipative.dense_domain

end DissipFEEC

/-! ### The dissipative FEEC theorem -/

section Main

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
variable {A : E →ₗ.[𝕜] E} {κ : Type*} (F : DissipFEEC.{u} A κ)

open DissipFEEC

theorem dissipFEEC_wellPosed (x : A.domain) (T : ℝ) :
    Evolution.IsClassicalSolution A (Icc 0 T) 0 (fun t => F.S t x) ∧
    (∀ U, U 0 = (x : E) → Evolution.IsStrongSolution A (Icc 0 T) 0 U →
      EqOn U (fun t => F.S t x) (Icc 0 T)) ∧
    ∀ t, 0 ≤ t → ‖F.S t x‖ ^ 2 = ‖(x : E)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, 2 * RCLike.re ⟪F.S s (A x), F.S s x⟫_𝕜 := by
  have hcl : Evolution.IsClassicalSolution A (Icc 0 T) 0 (fun t => F.S t x) := by
    have h := F.isMDissipative.semigroup.isClassicalSolution_orbit
      (F.isMDissipative.mem_semigroup_generator_domain x) 0 T
    rw [F.isMDissipative.generator_semigroup] at h
    simpa [S_def] using h
  refine ⟨hcl, fun U hU0 hU => ?_, fun t ht => F.isMDissipative.norm_sq_semigroup_apply x ht⟩
  exact hU.unique F.isMDissipative.dissipative hcl.toIsStrongSolution (by rw [hU0, S_def]; simp)

theorem dissipFEEC_antitone (x : E) : AntitoneOn (fun t => ‖F.S t x‖) (Ici 0) := by
  intro s (hs : 0 ≤ s) t _ hst
  have e : F.S t x = F.S (t - s) (F.S s x) := by
    simp only [S_def]
    rw [← C0Semigroup.S_add_apply _ (by linarith) hs, sub_add_cancel]
  change ‖F.S t x‖ ≤ ‖F.S s x‖
  rw [e]
  exact ((F.S (t - s)).le_opNorm _).trans (by
    simpa [S_def] using mul_le_mul_of_nonneg_right
      (F.isMDissipative.isContraction_semigroup _ (by linarith)) (norm_nonneg (F.S s x)))

theorem dissipFEEC_propagates_iff :
    (F.Keeps F.K ↔ ∀ μ : ℝ, 0 < μ → ∀ y ∈ F.K, Operator.resolvent A (μ : 𝕜) y ∈ F.K) ∧
    (F.Keeps F.K ↔
      ∃ μ : ℝ, 0 < μ ∧ ∀ y ∈ F.K, ∃ u : A.domain, (u : E) ∈ F.K ∧ (μ : 𝕜) • (u : E) - A u = y) ∧
    (A.IsReducing F.K ↔ F.Keeps F.K ∧ F.Keeps F.Kᗮ) :=
  ⟨F.isMDissipative.invariant_iff_resolvent F.isClosed_K,
    F.isMDissipative.invariant_iff_exists_solve F.isClosed_K, F.isMDissipative.isReducing_iff⟩

theorem dissipFEEC_converges_core (Z : F.Core) (T : ℝ) {x : E} (hx : x ∈ Z.Data) :
    TendstoUniformlyOn (fun h t => F.sol h ((Z.cmp T).p x h 0) t) (fun t => F.S t x) F.l
      (Icc 0 T) := by
  have hxP : x ∈ (Z.cmp T).Data := by rw [Z.data_eq]; exact hx
  have ha := Metric.tendstoUniformlyOn_iff.1 (Z.tendsto_approx T x hx)
  have hd := Metric.tendstoUniformlyOn_iff.1 (Z.tendsto_defect T x hx)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set T' := max T 0
  set C := F.boundConst
  have hC := F.boundConst_nonneg
  set δ := ε / (2 * (C * T' + 1))
  have hδ : 0 < δ := by positivity
  filter_upwards [ha _ (half_pos hε), hd δ hδ] with h h1 h2 t ht
  rw [dist_eq_norm]
  have hb := F.norm_sub_sol_le (Z.cmp T) hxP h t ht
  have hint : ∫ s in (0 : ℝ)..t, ‖(Z.cmp T).defect x h s‖ ≤ δ * t :=
    integral_le_mul_of_norm_le ht.1 fun s hs => by
      have := h2 s ⟨hs.1, hs.2.trans ht.2⟩
      rw [dist_eq_norm, zero_sub, norm_neg] at this
      exact this.le
  have hT' : t ≤ T' := ht.2.trans (le_max_left _ _)
  have i1 : ‖F.incl h‖ * ∫ s in (0 : ℝ)..t, ‖(Z.cmp T).defect x h s‖ ≤ C * (δ * T') :=
    mul_le_mul (F.norm_incl_le h) (hint.trans (mul_le_mul_of_nonneg_left hT' hδ.le))
      (intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _) hC
  have i2 : C * (δ * T') < ε / 2 := by
    have e : C * (δ * T') = ε / 2 * (C * T' / (C * T' + 1)) := by
      simp only [δ]; field_simp
    rw [e]
    have hCT : 0 ≤ C * T' := mul_nonneg hC (le_max_right _ _)
    have : C * T' / (C * T' + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    nlinarith
  have := h1 t ht
  rw [dist_eq_norm] at this
  linarith

theorem dissipFEEC_converges (Z : F.Core) (T : ℝ) {x : E} (hx : x ∈ Z.Data.topologicalClosure)
    {v : ∀ h, F.X h} (hv : F.Converges v x) :
    TendstoUniformlyOn (fun h t => F.sol h (v h) t) (fun t => F.S t x) F.l (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · rw [Icc_eq_empty (by linarith)]; exact tendstoUniformlyOn_empty
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set C := F.boundConst
  have hC := F.boundConst_nonneg
  set B := C ^ 2 + 1
  have hB : 0 < B := by positivity
  have hε' : 0 < ε / (4 * B) := by positivity
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ hε'
  rw [dist_eq_norm] at hxy
  have hy' : y ∈ Z.Data := SetLike.mem_coe.1 hy
  have hc := Metric.tendstoUniformlyOn_iff.1 (dissipFEEC_converges_core F Z T hy') _
    (show 0 < ε / 4 by positivity)
  filter_upwards [hc, (Metric.tendsto_nhds.1 (Z.tendsto_incl_p hT hy')) _ hε',
    Metric.tendsto_nhds.1 hv _ hε'] with h h1 h2 h3 t ht
  set w := (Z.cmp T).p y h 0
  rw [dist_eq_norm] at h2 h3 ⊢
  have a1 : ‖F.S t x - F.S t y‖ ≤ ‖x - y‖ := by
    rw [← _root_.map_sub]
    exact ((F.S t).le_opNorm _).trans (by
      simpa [S_def] using mul_le_mul_of_nonneg_right
        (F.isMDissipative.isContraction_semigroup t ht.1) (norm_nonneg (x - y)))
  have a2 : ‖F.S t y - F.sol h w t‖ < ε / 4 := by
    have := h1 t ht; rwa [dist_eq_norm] at this
  have a3 : ‖F.sol h w t - F.sol h (v h) t‖ ≤ C * ‖w - v h‖ :=
    (F.norm_sol_sub_sol_le h _ _ ht.1).trans
      (mul_le_mul_of_nonneg_right (F.norm_incl_le h) (norm_nonneg _))
  have a4 : ‖w - v h‖ ≤ C * (‖F.incl h w - y‖ + ‖y - x‖ + ‖x - F.incl h (v h)‖) := by
    refine (F.norm_le_norm_incl h _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [_root_.map_sub]
    calc ‖F.incl h w - F.incl h (v h)‖ =
        ‖(F.incl h w - y) + (y - x) + (x - F.incl h (v h))‖ := by abel_nf
      _ ≤ _ := norm_add₃_le
  have e : F.S t x - F.sol h (v h) t =
      (F.S t x - F.S t y) + (F.S t y - F.sol h w t) + (F.sol h w t - F.sol h (v h) t) := by abel
  rw [e]
  refine norm_add₃_le.trans_lt ?_
  rw [norm_sub_rev] at h3
  have hyx : ‖y - x‖ < ε / (4 * B) := by rw [norm_sub_rev]; exact hxy
  have hsum : ‖F.incl h w - y‖ + ‖y - x‖ + ‖x - F.incl h (v h)‖ < 3 * (ε / (4 * B)) := by
    linarith
  have hCC : C * (C * (‖F.incl h w - y‖ + ‖y - x‖ + ‖x - F.incl h (v h)‖)) ≤
      C ^ 2 * (3 * (ε / (4 * B))) := by
    rw [← mul_assoc, ← pow_two]
    exact mul_le_mul_of_nonneg_left hsum.le (sq_nonneg _)
  have key : ε / (4 * B) + C ^ 2 * (3 * (ε / (4 * B))) ≤ 3 * (ε / 4) := by
    have e1 : ε / (4 * B) + C ^ 2 * (3 * (ε / (4 * B))) = ε / 4 * ((1 + 3 * C ^ 2) / B) := by
      field_simp
    rw [e1]
    have : (1 + 3 * C ^ 2) / B ≤ 3 := (div_le_iff₀ hB).2 (by simp only [B]; linarith)
    nlinarith
  have hxy' : ‖x - y‖ < ε / (4 * B) := hxy
  linarith [a3.trans (mul_le_mul_of_nonneg_left a4 hC)]

theorem dissipFEEC_rate {T : ℝ} (R : F.RateClass T) {x : E} (hx : x ∈ R.Data) (h : κ)
    (v : F.X h) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖F.S t x - F.sol h v t‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * ‖R.p x h 0 - v‖ := by
  have hb := F.norm_sub_sol_le R.toComparison hx h t ht
  have hint : ∫ s in (0 : ℝ)..t, ‖R.toComparison.defect x h s‖ ≤
      R.C' * R.meshSize h ^ R.α * R.classNorm x * t :=
    integral_le_mul_of_norm_le ht.1 fun s hs => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact R.consistency x hx h s ⟨hs.1, hs.2.trans ht.2⟩
  have h1 := R.approx x hx h t ht
  have h2 := mul_le_mul_of_nonneg_left hint (norm_nonneg (F.incl h))
  have h3 := F.norm_sol_sub_sol_le h (R.p x h 0) v ht.1
  have e : F.S t x - F.sol h v t =
      (F.S t x - F.sol h (R.p x h 0) t) + (F.sol h (R.p x h 0) t - F.sol h v t) := by
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have : (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) =
      R.C * R.meshSize h ^ R.α * R.classNorm x +
        ‖F.incl h‖ * (R.C' * R.meshSize h ^ R.α * R.classNorm x * t) := by ring
  rw [this]
  linarith

theorem dissipFEEC_residual_le (hK : F.Keeps F.K) {x : E} (hxK : x ∈ F.K) (h : κ) (v : F.X h)
    {t : ℝ} (ht : 0 ≤ t) : infDist (F.sol h v t) F.K ≤ ‖F.S t x - F.sol h v t‖ := by
  rw [norm_sub_rev, ← dist_eq_norm]
  exact infDist_le_dist_of_mem (hK t ht x hxK)

theorem dissipFEEC_residual (hK : F.Keeps F.K) (Z : F.Core) (T : ℝ) {x : E}
    (hx : x ∈ Z.Data.topologicalClosure) (hxK : x ∈ F.K) {v : ∀ h, F.X h}
    (hv : F.Converges v x) :
    TendstoUniformlyOn (fun h t => infDist (F.sol h (v h) t) F.K) (fun _ => 0) F.l (Icc 0 T) := by
  have hc := Metric.tendstoUniformlyOn_iff.1 (dissipFEEC_converges F Z T hx hv)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hc ε hε] with h hh t ht
  have := hh t ht
  rw [dist_eq_norm] at this
  rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg infDist_nonneg]
  exact (dissipFEEC_residual_le F hK hxK h (v h) ht.1).trans_lt this

theorem dissipFEEC_tendsto_infDist (Z : F.Core) (Q : Set E) {x : E}
    (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h} (hv : F.Converges v x) {t : ℝ}
    (ht : 0 ≤ t) :
    Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l (𝓝 (infDist (F.S t x) Q)) :=
  ((continuous_infDist_pt Q).tendsto _).comp
    ((dissipFEEC_converges F Z t hx hv).tendsto_at ⟨ht, le_rfl⟩)

theorem dissipFEEC_leaves {Q : Set E} (hQ : ¬ F.Keeps Q) {T : ℝ} (hT : 0 < T) :
    ∃ x ∈ Q, F.Leaves x Q T := by
  by_contra hc
  refine hQ fun t ht x hx =>
    F.isMDissipative.semigroup.forall_nonneg_of_forall_Icc hT (fun y hy s hs => ?_) x hx t ht
  by_contra hout
  exact hc ⟨y, hy, s, hs, hout⟩

theorem dissipFEEC_leaves_of_not_isReducing (hK : ¬ A.IsReducing F.K) {T : ℝ} (hT : 0 < T) :
    ∃ Q : Submodule 𝕜 E, (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, F.Leaves x Q T := by
  by_cases hk : F.Keeps F.K
  · exact ⟨F.Kᗮ, Or.inr rfl, dissipFEEC_leaves F
      (fun h => hK ((dissipFEEC_propagates_iff F).2.2.2 ⟨hk, h⟩)) hT⟩
  · exact ⟨F.K, Or.inl rfl, dissipFEEC_leaves F hk hT⟩

theorem dissipFEEC_leaves_smooth {Q : Set E} (hQc : IsClosed Q) (hQ : ¬ F.Keeps Q)
    (hD : F.SmoothDense Q) {T : ℝ} (hT : 0 < T) :
    ∃ x ∈ (A.domain : Set E) ∩ Q, F.Leaves x Q T := by
  by_contra hc
  refine hQ fun t ht => ?_
  have hP : ∀ y ∈ (A.domain : Set E) ∩ Q, ∀ s, 0 ≤ s → F.S s y ∈ (A.domain : Set E) ∩ Q :=
    F.isMDissipative.semigroup.forall_nonneg_of_forall_Icc hT fun y hy s hs =>
      ⟨F.isMDissipative.semigroup_mem_domain ⟨y, hy.1⟩ hs.1,
        by_contra fun hout => hc ⟨y, hy, s, hs, hout⟩⟩
  exact F.isMDissipative.semigroup.mem_of_dense hQc hD fun y hy => (hP y hy t ht).2

/-- The conclusions of the dissipative FEEC theorem for `F` and the core `Z`. -/
structure DissipFEEC.Verdict (Z : F.Core) : Prop where
  /-- the orbits of `D(A)` are classical solutions -/
  isClassicalSolution (x : A.domain) (T : ℝ) :
    Evolution.IsClassicalSolution A (Icc 0 T) 0 (fun t => F.S t x)
  /-- and the only strong ones -/
  unique (x : A.domain) (T : ℝ) (U : ℝ → E) (hU0 : U 0 = (x : E))
    (hU : Evolution.IsStrongSolution A (Icc 0 T) 0 U) : EqOn U (fun t => F.S t x) (Icc 0 T)
  /-- the energy identity on `D(A)` -/
  energy (x : A.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖F.S t x‖ ^ 2 = ‖(x : E)‖ ^ 2 + ∫ s in (0 : ℝ)..t, 2 * RCLike.re ⟪F.S s (A x), F.S s x⟫_𝕜
  /-- the energy is nonincreasing -/
  antitone (x : E) : AntitoneOn (fun t => ‖F.S t x‖) (Ici 0)
  /-- `K` is kept iff the resolvents map `K` into `K` -/
  keeps_iff_resolvent :
    F.Keeps F.K ↔ ∀ μ : ℝ, 0 < μ → ∀ y ∈ F.K, Operator.resolvent A (μ : 𝕜) y ∈ F.K
  /-- `K` is kept iff the stationary problem is solvable in `D(A) ∩ K` -/
  keeps_iff_solvable : F.Keeps F.K ↔
    ∃ μ : ℝ, 0 < μ ∧ ∀ y ∈ F.K, ∃ u : A.domain, (u : E) ∈ F.K ∧ (μ : 𝕜) • (u : E) - A u = y
  /-- `K` reduces `A` iff `K` and `Kᗮ` are kept -/
  isReducing_iff : A.IsReducing F.K ↔ F.Keeps F.K ∧ F.Keeps F.Kᗮ
  /-- `ιₕ πₕ x → x` on the closure of the core -/
  tendsto_incl_proj {x : E} (hx : x ∈ Z.Data.topologicalClosure) :
    F.Converges (fun h => F.proj h x) x
  /-- convergence on the closure of the core, uniformly on `[0, T]` -/
  converges {x : E} (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h} (hv : F.Converges v x)
    (T : ℝ) : TendstoUniformlyOn (fun h t => F.sol h (v h) t) (fun t => F.S t x) F.l (Icc 0 T)
  /-- the rate -/
  rate {T : ℝ} (R : F.RateClass T) {x : E} (hx : x ∈ R.Data) (h : κ) (v : F.X h) {t : ℝ}
    (ht : t ∈ Icc 0 T) : ‖F.S t x - F.sol h v t‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * ‖R.p x h 0 - v‖
  /-- for a kept `K`, the residual is at most the error -/
  residual_le (hK : F.Keeps F.K) {x : E} (hxK : x ∈ F.K) (h : κ) (v : F.X h) {t : ℝ}
    (ht : 0 ≤ t) : infDist (F.sol h v t) F.K ≤ ‖F.S t x - F.sol h v t‖
  /-- and tends to `0` uniformly on `[0, T]` -/
  residual_tendsto (hK : F.Keeps F.K) {x : E} (hxK : x ∈ F.K)
    (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h} (hv : F.Converges v x) (T : ℝ) :
    TendstoUniformlyOn (fun h t => infDist (F.sol h (v h) t) F.K) (fun _ => 0) F.l (Icc 0 T)
  /-- the distances to any set converge to that of the exact solution -/
  tendsto_infDist (Q : Set E) {x : E} (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h}
    (hv : F.Converges v x) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l (𝓝 (infDist (F.S t x) Q))
  /-- a set that is not kept is left before any time `T > 0` -/
  leaves {Q : Set E} (hQ : ¬ F.Keeps Q) {T : ℝ} (hT : 0 < T) : ∃ x ∈ Q, F.Leaves x Q T
  /-- by a datum of its dense smooth part when it is closed -/
  leaves_smooth {Q : Set E} (hQc : IsClosed Q) (hQ : ¬ F.Keeps Q) (hD : F.SmoothDense Q) {T : ℝ}
    (hT : 0 < T) : ∃ x ∈ (A.domain : Set E) ∩ Q, F.Leaves x Q T

/-- **The dissipative FEEC theorem**: a dissipative FEEC discretization with an orbit-consistent
core satisfies `DissipFEEC.Verdict` (cf. [Pazy1983], §1.4, Thm 4.3, §3.4). -/
theorem dissipFEEC (Z : F.Core) : F.Verdict Z where
  isClassicalSolution x T := (dissipFEEC_wellPosed F x T).1
  unique x T U hU0 hU := (dissipFEEC_wellPosed F x T).2.1 U hU0 hU
  energy := fun x {_} ht => (dissipFEEC_wellPosed F x 0).2.2 _ ht
  antitone := dissipFEEC_antitone F
  keeps_iff_resolvent := (dissipFEEC_propagates_iff F).1
  keeps_iff_solvable := (dissipFEEC_propagates_iff F).2.1
  isReducing_iff := (dissipFEEC_propagates_iff F).2.2
  tendsto_incl_proj := fun {_} hx => tendsto_incl_proj F Z hx
  converges := fun {_} hx {_} hv T => dissipFEEC_converges F Z T hx hv
  rate := fun {_} R {_} hx h v {_} ht => dissipFEEC_rate F R hx h v ht
  residual_le := fun hK {_} hxK h v {_} ht => dissipFEEC_residual_le F hK hxK h v ht
  residual_tendsto := fun hK {_} hxK hx {_} hv T => dissipFEEC_residual F hK Z T hx hxK hv
  tendsto_infDist := fun Q {_} hx {_} hv {_} ht => dissipFEEC_tendsto_infDist F Z Q hx hv ht
  leaves := fun {_} hQ {_} hT => dissipFEEC_leaves F hQ hT
  leaves_smooth := fun {_} hQc hQ hD {_} hT => dissipFEEC_leaves_smooth F hQc hQ hD hT

variable {F} in
theorem DissipFEEC.Verdict.detects {Z : F.Core} (V : F.Verdict Z) {Q : Set E} (hQc : IsClosed Q)
    (hQ : Q.Nonempty) {x : E} {t : ℝ} (ht : 0 ≤ t) (hout : F.S t x ∉ Q) :
    0 < infDist (F.S t x) Q ∧ (x ∈ Z.Data.topologicalClosure → ∀ v : ∀ h, F.X h,
      F.Converges v x → Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l
        (𝓝 (infDist (F.S t x) Q)) ∧
      ∀ᶠ h in F.l, infDist (F.S t x) Q / 2 < infDist (F.sol h (v h) t) Q) := by
  have hpos := (hQc.notMem_iff_infDist_pos hQ).1 hout
  refine ⟨hpos, fun hx v hv => ?_⟩
  have hlim := V.tendsto_infDist Q hx hv ht
  exact ⟨hlim, (tendsto_order.1 hlim).1 _ (half_lt_self hpos)⟩

variable {F} in
theorem DissipFEEC.Verdict.tendsto_infDist_zero_iff {Z : F.Core} (V : F.Verdict Z) [F.l.NeBot]
    {Q : Set E} (hQc : IsClosed Q) (hQ : Q.Nonempty) {x : E}
    (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h} (hv : F.Converges v x) :
    (∀ t, 0 ≤ t → Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l (𝓝 0)) ↔
      ∀ t, 0 ≤ t → F.S t x ∈ Q := by
  refine forall₂_congr fun t ht => ?_
  rw [hQc.mem_iff_infDist_zero hQ]
  exact ⟨fun h => tendsto_nhds_unique (V.tendsto_infDist Q hx hv ht) h,
    fun h => h ▸ V.tendsto_infDist Q hx hv ht⟩

end Main

end Feec.HilbertComplex
