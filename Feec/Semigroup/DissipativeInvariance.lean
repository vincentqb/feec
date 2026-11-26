module

public import Feec.Semigroup.LumerPhillips
public import Feec.ForMathlib.LinearPMap.Reducing

/-!
# Invariant subspaces of contraction semigroups

For an m-dissipative `A` on a Hilbert space and a closed `K`, the semigroup of `A` leaves `K`
invariant iff the resolvents do, iff the part of `A` in `K` is m-dissipative.

## References

* [K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*][EngelNagel2000],
  §II.2.3

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology NormedSpace LinearPMap Feec.Operator

@[expose] public noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Feec

/-! ### Exponentials and closed invariant subspaces -/

theorem exp_apply_mem_of_mapsTo [CompleteSpace E] {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E))
    {B : E →L[𝕜] E} (hB : ∀ x ∈ K, B x ∈ K) {x : E} (hx : x ∈ K) : exp B x ∈ K := by
  have hpow : ∀ n : ℕ, (B ^ n) x ∈ K := fun n => by
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', mul_apply_eq_comp]; exact hB _ ih
  have hs := ((ContinuousLinearMap.apply 𝕜 E x).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) B))
  refine hK.mem_of_tendsto hs.tendsto_sum_nat (Eventually.of_forall fun N => ?_)
  refine K.sum_mem fun n _ => ?_
  simp only [ContinuousLinearMap.apply_apply, _root_.smul_apply]
  exact K.smul_mem _ (hpow n)

/-! ### Invariance from a dense subset -/

namespace C0Semigroup

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E)

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem mem_of_dense {P : Set E} (hP : IsClosed P) {D : Set E} (hD : ∀ k ∈ P, k ∈ closure (D ∩ P))
    {t : ℝ} (h : ∀ x ∈ D ∩ P, G.S t x ∈ P) : ∀ x ∈ P, G.S t x ∈ P := by
  intro x hx
  have hc : G.S t x ∈ closure (G.S t '' (D ∩ P)) :=
    map_mem_closure (G.S t).continuous (hD x hx) fun y hy => mem_image_of_mem _ hy
  exact (closure_minimal (image_subset_iff.2 fun y hy => h y hy) hP) hc

end C0Semigroup

/-! ### The energy identity -/

namespace C0Semigroup

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E)

theorem norm_sq_S_apply [CompleteSpace E] (x : G.generator.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖G.S t x‖ ^ 2 = ‖(x : E)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, 2 * RCLike.re ⟪G.S s (G.generator x), G.S s x⟫_𝕜 := by
  set f : ℝ → ℝ := fun s => RCLike.re ⟪G.S s x, G.S s x⟫_𝕜
  have hfe : ∀ s, f s = ‖G.S s x‖ ^ 2 := fun s => by
    simp only [f]; exact inner_self_eq_norm_sq (𝕜 := 𝕜) _
  have hcont : ContinuousOn (fun s => G.S s (x : E)) (Icc 0 t) :=
    (G.strongCont x).mono Icc_subset_Ici_self
  have hcont' : ContinuousOn (fun s => G.S s (G.generator x)) (Icc 0 t) :=
    (G.strongCont _).mono Icc_subset_Ici_self
  have hd : ∀ s ∈ Ioo 0 t, HasDerivWithinAt f
      (2 * RCLike.re ⟪G.S s (G.generator x), G.S s x⟫_𝕜) (Ioi s) s := by
    intro s hs
    have h1 := (G.hasDerivWithinAt_apply x hs.1.le).mono
      (Ioi_subset_Ici_self.trans (Ici_subset_Ici.2 hs.1.le))
    have h2 := h1.inner 𝕜 h1
    have h3 : HasDerivWithinAt f (RCLike.reCLM (⟪G.S s x, G.S s (G.generator x)⟫_𝕜 +
        ⟪G.S s (G.generator x), G.S s x⟫_𝕜)) (Ioi s) s :=
      (RCLike.reCLM (K := 𝕜)).hasFDerivAt.comp_hasDerivWithinAt s h2
    convert h3 using 1
    rw [RCLike.reCLM_apply, _root_.map_add, inner_re_symm (𝕜 := 𝕜) (G.S s x)]; ring
  have hint : IntervalIntegrable (fun s => 2 * RCLike.re ⟪G.S s (G.generator x), G.S s x⟫_𝕜)
      MeasureTheory.volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht]
    exact continuousOn_const.mul (RCLike.continuous_re.comp_continuousOn (hcont'.inner hcont))
  have hfc : ContinuousOn f (Icc 0 t) := RCLike.continuous_re.comp_continuousOn
    (hcont.inner hcont)
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hfc hd hint
  rw [hfe, hfe, S_zero_apply] at h
  linarith

end C0Semigroup

/-! ### The restriction of a semigroup to an invariant closed subspace -/

namespace C0Semigroup

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E) (K : Submodule 𝕜 E)

/-- **The restriction** of a semigroup to an invariant subspace `K`, `S_K(t) = S(max t 0)|_K`. -/
def restrict (hK : ∀ t, 0 ≤ t → ∀ x ∈ K, G.S t x ∈ K) : C0Semigroup 𝕜 K where
  S t := (G.S (max t 0) ∘L K.subtypeL).codRestrict K fun x => hK _ (le_max_right _ _) _ x.2
  map_zero := by
    ext x; simp
  map_add s t hs ht := by
    ext x
    simp [max_eq_left hs, max_eq_left ht, max_eq_left (add_nonneg hs ht), G.S_add_apply hs ht]
  strongCont x := by
    have h : ContinuousOn (fun t => G.S (max t 0) (x : E)) (Ici 0) :=
      ((G.strongCont x).comp (continuous_id.max continuous_const).continuousOn
        fun t _ => le_max_right t 0)
    exact (continuousOn_iff_continuous_domRestrict.2 (continuous_induced_rng.2
      (continuousOn_iff_continuous_domRestrict.1 h)))

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
variable {G K} in
@[simp] theorem coe_restrict_S (hK : ∀ t, 0 ≤ t → ∀ x ∈ K, G.S t x ∈ K) {t : ℝ} (ht : 0 ≤ t)
    (x : K) : ((G.restrict K hK).S t x : E) = G.S t x := by
  simp [restrict, max_eq_left ht]

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
variable {G K} in
theorem IsContraction.restrict (hG : G.IsContraction) (hK : ∀ t, 0 ≤ t → ∀ x ∈ K, G.S t x ∈ K) :
    (G.restrict K hK).IsContraction := fun t ht =>
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, ← Submodule.norm_coe, coe_restrict_S hK ht, ← Submodule.norm_coe]
    calc ‖G.S t (x : E)‖ ≤ ‖G.S t‖ * ‖(x : E)‖ := (G.S t).le_opNorm _
      _ ≤ 1 * ‖(x : E)‖ := mul_le_mul_of_nonneg_right (hG t ht) (norm_nonneg _)
      _ = ‖(x : E)‖ := one_mul _

variable {G K} in
theorem restrict_generator (hK : ∀ t, 0 ≤ t → ∀ x ∈ K, G.S t x ∈ K)
    (u : (G.restrict K hK).generator.domain) :
    ∃ h : ((u : K) : E) ∈ G.generator.domain,
      G.generator ⟨_, h⟩ = ((G.restrict K hK).generator u : E) := by
  have hd := (G.restrict K hK).hasDerivWithinAt_generator u
  have hd' : HasDerivWithinAt (fun t => G.S t ((u : K) : E))
      (((G.restrict K hK).generator u : K) : E) (Ici 0) 0 := by
    have := (K.subtypeL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) hd
    refine this.congr_of_mem (fun t (ht : 0 ≤ t) => ?_) self_mem_Ici
    simp [coe_restrict_S hK ht]
  exact ⟨⟨_, hd'⟩, G.generator_apply_eq hd'⟩

end C0Semigroup

end Feec

/-! ### The part of an operator in a subspace -/

namespace LinearPMap

variable (A : E →ₗ.[𝕜] E) (K : Submodule 𝕜 E)

/-- The domain of the part of `A` in `K`: `{u ∈ K | u ∈ D(A), A u ∈ K}`. -/
def partInDomain : Submodule 𝕜 K where
  carrier := {u | ∃ h : (u : E) ∈ A.domain, A ⟨u, h⟩ ∈ K}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨A.domain.add_mem ha hb, ?_⟩
    have e : (⟨((a + b : K) : E), A.domain.add_mem ha hb⟩ : A.domain) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, LinearPMap.map_add]; exact K.add_mem ha' hb'
  zero_mem' := ⟨A.domain.zero_mem, by
    have e : (⟨((0 : K) : E), A.domain.zero_mem⟩ : A.domain) = 0 := rfl
    rw [e, LinearPMap.map_zero]; exact K.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨A.domain.smul_mem c ha, ?_⟩
    have e : (⟨((c • a : K) : E), A.domain.smul_mem c ha⟩ : A.domain) = c • ⟨a, ha⟩ := rfl
    rw [e, LinearPMap.map_smul]; exact K.smul_mem c ha'

/-- The part of `A` in `K`: `A` on `{u ∈ D(A) ∩ K | A u ∈ K}`. Cf. [EngelNagel2000], §II.2.3 -/
def partIn : K →ₗ.[𝕜] K where
  domain := A.partInDomain K
  toFun :=
    { toFun := fun u => ⟨A ⟨((u : K) : E), u.2.1⟩, u.2.2⟩
      map_add' := fun a b => by
        ext
        change A ⟨((a : K) : E) + ((b : K) : E), _⟩ = A ⟨_, a.2.1⟩ + A ⟨_, b.2.1⟩
        rw [← LinearPMap.map_add]; rfl
      map_smul' := fun c a => by
        ext
        change A ⟨c • ((a : K) : E), _⟩ = c • A ⟨_, a.2.1⟩
        rw [← LinearPMap.map_smul]; rfl }

variable {A K}

theorem coe_partIn_apply (u : (A.partIn K).domain) :
    ((A.partIn K u : K) : E) = A ⟨((u : K) : E), u.2.1⟩ := rfl

theorem IsDissipative.partIn (hA : A.IsDissipative) : (A.partIn K).IsDissipative := fun u => by
  have := hA ⟨((u : K) : E), u.2.1⟩
  rwa [Submodule.coe_inner, coe_partIn_apply]

theorem IsMDissipative.eq_of_le [CompleteSpace E] (hA : A.IsMDissipative) {B : E →ₗ.[𝕜] E}
    (hAB : A ≤ B) (hB : B.IsDissipative) : B = A := by
  refine (LinearPMap.eq_of_le_of_domain_le hAB fun x hx => ?_).symm
  obtain ⟨y, hy⟩ := hA.surjective one_pos ((x : E) - B ⟨x, hx⟩)
  set y' : B.domain := ⟨y, hAB.1 y.2⟩
  have hBy : B y' = A y := (hAB.2 rfl).symm
  have h0 : ((1 : ℝ) : 𝕜) • ((y' - ⟨x, hx⟩ : B.domain) : E) - B (y' - ⟨x, hx⟩) = 0 := by
    calc _ = (((1 : ℝ) : 𝕜) • (y : E) - A y) - ((x : E) - B ⟨x, hx⟩) := by
          rw [LinearPMap.map_sub, hBy, Submodule.coe_sub, RCLike.ofReal_one, one_smul, one_smul]
          abel
      _ = 0 := by rw [hy, sub_self]
  have h1 := congrArg Subtype.val (hB.eq_zero_of_smul_sub_eq_zero one_pos h0)
  have hxy : (y : E) = x := by simpa [sub_eq_zero, y'] using h1
  rw [← hxy]; exact y.2

end LinearPMap

/-! ### Invariance: the resolvent and generator criteria -/

namespace LinearPMap.IsMDissipative

open Feec Feec.LumerPhillips

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E}
  {K : Submodule 𝕜 E}

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
private theorem pmap_congr {T T' : E →ₗ.[𝕜] E} (e : T = T') (x : T.domain) (y : T'.domain)
    (hxy : (x : E) = y) : T x = T' y := by
  subst e; rw [Subtype.ext hxy]

/-! ### The orbits of the Lumer–Phillips semigroup in terms of `A` -/

theorem mem_semigroup_generator_domain (hA : A.IsMDissipative) (x : A.domain) :
    (x : E) ∈ hA.semigroup.generator.domain := by
  rw [hA.generator_semigroup]; exact x.2

theorem semigroup_generator_apply (hA : A.IsMDissipative) (x : A.domain) :
    hA.semigroup.generator ⟨x, hA.mem_semigroup_generator_domain x⟩ = A x :=
  pmap_congr hA.generator_semigroup _ _ rfl

theorem semigroup_mem_domain (hA : A.IsMDissipative) (x : A.domain) {t : ℝ} (ht : 0 ≤ t) :
    hA.semigroup.S t x ∈ A.domain := by
  have := hA.semigroup.mapsTo_domain ⟨x, hA.mem_semigroup_generator_domain x⟩ ht
  simp only at this
  rwa [hA.generator_semigroup] at this

theorem apply_semigroup (hA : A.IsMDissipative) (x : A.domain) {t : ℝ} (ht : 0 ≤ t) :
    A ⟨_, hA.semigroup_mem_domain x ht⟩ = hA.semigroup.S t (A x) := by
  have h := hA.semigroup.generator_apply_S ⟨x, hA.mem_semigroup_generator_domain x⟩ ht
  rw [hA.semigroup_generator_apply] at h
  rw [← h]
  exact (pmap_congr hA.generator_semigroup _ _ rfl).symm

theorem hasDerivWithinAt_semigroup (hA : A.IsMDissipative) (x : A.domain) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => hA.semigroup.S s x) (hA.semigroup.S t (A x)) (Ici t) t := by
  have h := hA.semigroup.hasDerivWithinAt_Ici_apply ⟨x, hA.mem_semigroup_generator_domain x⟩ ht
  rwa [hA.semigroup_generator_apply] at h

theorem norm_sq_semigroup_apply (hA : A.IsMDissipative) (x : A.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖hA.semigroup.S t x‖ ^ 2 = ‖(x : E)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, 2 * RCLike.re ⟪hA.semigroup.S s (A x), hA.semigroup.S s x⟫_𝕜 := by
  have h := hA.semigroup.norm_sq_S_apply ⟨x, hA.mem_semigroup_generator_domain x⟩ ht
  rwa [hA.semigroup_generator_apply] at h

theorem semigroup_mem_of_res_mem (hA : A.IsMDissipative) (hK : _root_.IsClosed (K : Set E))
    (hR : ∀ n : ℕ, ∀ x ∈ K, res A n x ∈ K) (t : ℝ) {x : E} (hx : x ∈ K) :
    hA.semigroup.S t x ∈ K := by
  have hY : ∀ n, ∀ y ∈ K, yosida A n y ∈ K := fun n y hy => by
    simp only [yosida, approxJ, _root_.sub_apply, _root_.smul_apply, one_apply_eq_self]
    exact K.sub_mem (K.smul_mem _ (K.smul_mem _ (hR n y hy))) (K.smul_mem _ hy)
  have hS : ∀ n, approxS A n (max t 0) x ∈ K := fun n =>
    exp_apply_mem_of_mapsTo hK (fun y hy => by
      rw [_root_.smul_apply]; exact K.smul_mem _ (hY n y hy)) hx
  exact hK.mem_of_tendsto (tendsto_approxS_max hA t x) (Eventually.of_forall hS)

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem resolvent_apply_sub (hA : A.IsMDissipative) {μ : ℝ} (hμ : 0 < μ) (u : A.domain) :
    resolvent A (μ : 𝕜) ((μ : 𝕜) • (u : E) - A u) = u :=
  (hA.isResolvent hμ).apply_sub u

theorem exists_solve_of_invariant (hA : A.IsMDissipative) (hK : _root_.IsClosed (K : Set E))
    (hinv : ∀ t, 0 ≤ t → ∀ x ∈ K, hA.semigroup.S t x ∈ K) {μ : ℝ} (hμ : 0 < μ) (y : E)
    (hy : y ∈ K) : ∃ u : A.domain, (u : E) ∈ K ∧ (μ : 𝕜) • (u : E) - A u = y := by
  have : CompleteSpace K := hK.completeSpace_coe
  set G := hA.semigroup.restrict K hinv
  have hG : G.IsContraction := hA.isContraction_semigroup.restrict hinv
  obtain ⟨u, hu⟩ := hG.isMDissipative_generator.surjective hμ ⟨y, hy⟩
  obtain ⟨hdom', hgen⟩ := C0Semigroup.restrict_generator hinv u
  have hdom : ((u : K) : E) ∈ A.domain := by rw [← hA.generator_semigroup]; exact hdom'
  have hgen' : A ⟨_, hdom⟩ = ((G.generator u : K) : E) := by
    rw [← hgen]; exact pmap_congr hA.generator_semigroup.symm _ _ rfl
  refine ⟨⟨_, hdom⟩, ((u : K)).2, ?_⟩
  have := congrArg Subtype.val hu
  simp only [Submodule.coe_sub, Submodule.coe_smul] at this
  rw [hgen']
  exact this

/-- **The resolvent criterion for invariance**: for a closed `K`, `S(t) K ⊆ K` for all `t ≥ 0`
iff `(μ - A)⁻¹ K ⊆ K` for all `μ > 0`. -/
theorem invariant_iff_resolvent (hA : A.IsMDissipative) (hK : _root_.IsClosed (K : Set E)) :
    (∀ t, 0 ≤ t → ∀ x ∈ K, hA.semigroup.S t x ∈ K) ↔
      ∀ μ : ℝ, 0 < μ → ∀ y ∈ K, resolvent A (μ : 𝕜) y ∈ K := by
  constructor
  · intro hinv μ hμ y hy
    obtain ⟨u, huK, hu⟩ := hA.exists_solve_of_invariant hK hinv hμ y hy
    rw [← hu, hA.resolvent_apply_sub hμ]; exact huK
  · intro hR t _ x hx
    exact hA.semigroup_mem_of_res_mem hK (fun n y hy => hR _ (Stone.scale_pos n) y hy) t hx

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem isMDissipative_partIn_of_solve (hA : A.IsMDissipative) {μ : ℝ} (hμ : 0 < μ)
    (hs : ∀ y ∈ K, ∃ u : A.domain, (u : E) ∈ K ∧ (μ : 𝕜) • (u : E) - A u = y) :
    (A.partIn K).IsMDissipative := by
  refine ⟨hA.dissipative.partIn, μ, hμ, fun y => ?_⟩
  obtain ⟨u, huK, hu⟩ := hs y y.2
  have hAu : A u ∈ K := by
    have : A u = (μ : 𝕜) • (u : E) - y := by rw [← hu]; abel
    rw [this]; exact K.sub_mem (K.smul_mem _ huK) y.2
  refine ⟨⟨⟨u, huK⟩, u.2, hAu⟩, Subtype.ext ?_⟩
  simp only [Submodule.coe_sub, Submodule.coe_smul, LinearPMap.coe_partIn_apply]
  exact hu

theorem invariant_iff_exists_solve (hA : A.IsMDissipative) (hK : _root_.IsClosed (K : Set E)) :
    (∀ t, 0 ≤ t → ∀ x ∈ K, hA.semigroup.S t x ∈ K) ↔
      ∃ μ : ℝ, 0 < μ ∧ ∀ y ∈ K, ∃ u : A.domain, (u : E) ∈ K ∧ (μ : 𝕜) • (u : E) - A u = y := by
  refine ⟨fun hinv => ⟨1, one_pos, fun y hy => hA.exists_solve_of_invariant hK hinv one_pos y hy⟩,
    fun ⟨μ, hμ, hs⟩ => ?_⟩
  have : CompleteSpace K := hK.completeSpace_coe
  have hP := hA.isMDissipative_partIn_of_solve hμ hs
  refine (hA.invariant_iff_resolvent hK).2 fun ν hν y hy => ?_
  obtain ⟨u, hu⟩ := hP.surjective hν ⟨y, hy⟩
  have hu' := congrArg Subtype.val hu
  simp only [Submodule.coe_sub, Submodule.coe_smul, LinearPMap.coe_partIn_apply] at hu'
  rw [← hu', hA.resolvent_apply_sub hν ⟨_, u.2.1⟩]
  exact ((u : K)).2

/-- **The part of `A` in a closed invariant `K` is m-dissipative**, and conversely. -/
theorem invariant_iff_isMDissipative_partIn (hA : A.IsMDissipative)
    (hK : _root_.IsClosed (K : Set E)) :
    (∀ t, 0 ≤ t → ∀ x ∈ K, hA.semigroup.S t x ∈ K) ↔ (A.partIn K).IsMDissipative := by
  rw [hA.invariant_iff_exists_solve hK]
  constructor
  · rintro ⟨μ, hμ, hs⟩
    exact hA.isMDissipative_partIn_of_solve hμ hs
  · rintro hP
    refine ⟨1, one_pos, fun y hy => ?_⟩
    obtain ⟨u, hu⟩ := hP.surjective one_pos ⟨y, hy⟩
    have hu' := congrArg Subtype.val hu
    simp only [Submodule.coe_sub, Submodule.coe_smul, LinearPMap.coe_partIn_apply] at hu'
    exact ⟨⟨_, u.2.1⟩, ((u : K)).2, hu'⟩

theorem closure_domain_inter_of_invariant (hA : A.IsMDissipative)
    (hK : _root_.IsClosed (K : Set E)) (hinv : ∀ t, 0 ≤ t → ∀ x ∈ K, hA.semigroup.S t x ∈ K) :
    ∀ k ∈ K, k ∈ _root_.closure ((A.domain : Set E) ∩ K) := by
  have : CompleteSpace K := hK.completeSpace_coe
  set G := hA.semigroup.restrict K hinv
  have hG := (hA.isContraction_semigroup.restrict hinv).isMDissipative_generator
  have hD := hG.dense_domain
  intro k hk
  have hsub : (fun u : K => (u : E)) '' (G.generator.domain : Set K) ⊆ (A.domain : Set E) ∩ K := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hdom, -⟩ := C0Semigroup.restrict_generator hinv ⟨u, hu⟩
    refine ⟨?_, u.2⟩
    rw [← hA.generator_semigroup]; exact hdom
  refine closure_mono hsub ?_
  have hk' : (⟨k, hk⟩ : K) ∈ _root_.closure (G.generator.domain : Set K) :=
    hD.closure_eq ▸ mem_univ _
  exact map_mem_closure continuous_subtype_val hk' fun u hu => mem_image_of_mem _ hu

/-- **Reducing subspaces of an m-dissipative operator**: `K` reduces `A` iff `K` and `Kᗮ` are both
invariant under the contraction semigroup. -/
theorem isReducing_iff (hA : A.IsMDissipative) [K.HasOrthogonalProjection] :
    A.IsReducing K ↔ (∀ t, 0 ≤ t → ∀ x ∈ K, hA.semigroup.S t x ∈ K) ∧
      ∀ t, 0 ≤ t → ∀ x ∈ Kᗮ, hA.semigroup.S t x ∈ Kᗮ := by
  have hKc : _root_.IsClosed (K : Set E) := by
    rw [← Submodule.orthogonal_orthogonal K]; exact Submodule.isClosed_orthogonal _
  have hKc' : _root_.IsClosed (Kᗮ : Set E) := Submodule.isClosed_orthogonal _
  constructor
  · intro hred
    -- the resolvents commute with `P_K`
    have hcomm : ∀ μ : ℝ, 0 < μ → ∀ y, resolvent A (μ : 𝕜) (K.starProjection y) =
        K.starProjection (resolvent A (μ : 𝕜) y) := by
      intro μ hμ y
      set u := (hA.isResolvent hμ).toDomain y
      have hu : (μ : 𝕜) • (u : E) - A u = y := (hA.isResolvent hμ).sub_apply_toDomain y
      have hPu : (μ : 𝕜) • (K.starProjection (u : E)) - A ⟨_, hred.proj_mem u⟩ =
          K.starProjection y := by
        rw [hred.comm u, ← hu, _root_.map_sub, _root_.map_smul]
      rw [← hPu]; exact hA.resolvent_apply_sub hμ ⟨_, hred.proj_mem u⟩
    refine ⟨(hA.invariant_iff_resolvent hKc).2 fun μ hμ y hy => ?_,
      (hA.invariant_iff_resolvent hKc').2 fun μ hμ y hy => ?_⟩
    · rw [← K.starProjection_eq_self_iff.2 hy, hcomm μ hμ]
      exact K.starProjection_apply_mem _
    · have h0 : K.starProjection y = 0 := K.starProjection_apply_eq_zero_iff.2 hy
      have : K.starProjection (resolvent A (μ : 𝕜) y) = 0 := by
        rw [← hcomm μ hμ, h0, _root_.map_zero]
      exact K.starProjection_apply_eq_zero_iff.1 this
  · rintro ⟨h1, h2⟩
    -- `P_K` commutes with `S(t)`, `t ≥ 0`
    have hS : ∀ t, 0 ≤ t → ∀ x, hA.semigroup.S t (K.starProjection x) =
        K.starProjection (hA.semigroup.S t x) := fun t ht x =>
      (K.eq_starProjection_of_mem_orthogonal' (h1 t ht _ (K.starProjection_apply_mem x))
        (z := hA.semigroup.S t (x - K.starProjection x))
        (h2 t ht _ (K.sub_starProjection_mem_orthogonal x))
        (by rw [_root_.map_sub]; abel)).symm
    have hd : ∀ x : A.domain, HasDerivWithinAt (fun t => hA.semigroup.S t (K.starProjection x))
        (K.starProjection (A x)) (Ici 0) 0 := fun x => by
      have hx : (x : E) ∈ hA.semigroup.generator.domain := by
        rw [hA.generator_semigroup]; exact x.2
      have h := (K.starProjection).hasDerivWithinAt_apply_of_hasDerivWithinAt
        (hA.semigroup.hasDerivWithinAt_generator ⟨x, hx⟩)
      have e : hA.semigroup.generator ⟨x, hx⟩ = A x :=
        pmap_congr hA.generator_semigroup _ _ rfl
      rw [e] at h
      exact h.congr_of_mem (fun t ht => hS t ht x) self_mem_Ici
    have hdomeq : hA.semigroup.generator.domain = A.domain := by rw [hA.generator_semigroup]
    have hmem : ∀ x : A.domain, K.starProjection (x : E) ∈ A.domain := fun x =>
      Eq.mp (congrArg (fun D : Submodule 𝕜 E => K.starProjection (x : E) ∈ D) hdomeq) ⟨_, hd x⟩
    refine ⟨hmem, fun x => ?_⟩
    have hx : K.starProjection (x : E) ∈ hA.semigroup.generator.domain :=
      Eq.mpr (congrArg (fun D : Submodule 𝕜 E => K.starProjection (x : E) ∈ D) hdomeq) (hmem x)
    have e := hA.semigroup.generator_apply_eq (x := ⟨_, hx⟩) (hd x)
    rw [← e]
    exact (pmap_congr hA.generator_semigroup _ _ rfl).symm

end LinearPMap.IsMDissipative
