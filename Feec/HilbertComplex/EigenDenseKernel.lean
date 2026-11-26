module

public import Feec.HilbertComplex.Compactness
public import Feec.Semigroup.Spectral

/-!
# A complete set of eigenvectors from compactness below the top degree

A skew-adjoint `A` whose unit box of `D(A) ∩ N(A)ᗮ` lies in a compact set has a dense span of
eigenvectors of `A²`; for the wave operator of a finite Hilbert complex this follows from the same
compactness of `D(dⁱ) ∩ (𝔷ⁱ)ᗮ` in every degree.

## Main results

* `Operator.HasCompactPair.exists_isCompact_coeff`: Weber's lemma, abstract form.
* `IsSkewAdjoint.dense_span_isEigenSq_of_hasCompactPerp`: spectral theorem off the kernel.
* `eigenDense_wave_of_compact_perp`, `eigenDense_wave_fin3`: the wave group is `EigenDense`.

## References

* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology Pointwise
open LinearPMap Set Filter

@[expose] public noncomputable section

namespace Feec.Operator

/-! ### Total boundedness along maps with a modulus -/

theorem totallyBounded_of_modulus {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {s : Set X} {t : Set Y} (ht : TotallyBounded t) (f : X → Y) (hf : MapsTo f s t)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) < δ → dist x y < ε) :
    TotallyBounded s := by
  refine Metric.totallyBounded_iff.2 fun ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := hmod ε hε
  obtain ⟨u, hus, hu, hcov⟩ :=
    Metric.finite_approx_of_totallyBounded (ht.subset (image_subset_iff.2 hf)) δ hδ
  choose g hg using fun y : u => hus y.2
  have : Finite u := hu.to_subtype
  refine ⟨range g, finite_range g, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcov (mem_image_of_mem f hx))
  refine mem_iUnion₂.2 ⟨g ⟨y, hy⟩, mem_range_self _, ?_⟩
  rw [Metric.mem_ball] at hxy ⊢
  exact h x hx _ (hg ⟨y, hy⟩).1 (by rw [(hg ⟨y, hy⟩).2]; exact hxy)

theorem exists_isCompact_of_totallyBounded {X : Type*} [MetricSpace X] [CompleteSpace X]
    {s : Set X} (hs : TotallyBounded s) : ∃ K : Set X, IsCompact K ∧ s ⊆ K :=
  ⟨closure s, hs.closure.isCompact_of_isClosed isClosed_closure, subset_closure⟩

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-! ### Compact boxes of a partial map -/

/-- The unit box of `D(T) ∩ N(T)ᗮ`, in the graph norm, lies in a compact set. -/
def HasCompactPerp (T : E →ₗ.[𝕜] F) : Prop :=
  ∃ K : Set E, IsCompact K ∧ ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ 1 → ‖T x‖ ≤ 1 →
    (x : E) ∈ K

/-- The unit box `‖x‖, ‖T x‖ ≤ 1` of `D(T)` lies in a compact set. -/
def HasCompactBall (T : E →ₗ.[𝕜] F) : Prop :=
  ∃ K : Set E, IsCompact K ∧ ∀ x : T.domain, ‖(x : E)‖ ≤ 1 → ‖T x‖ ≤ 1 → (x : E) ∈ K

variable {T : E →ₗ.[𝕜] F}

theorem HasCompactBall.hasCompactPerp (h : HasCompactBall T) : HasCompactPerp T := by
  obtain ⟨K, hK, hsub⟩ := h
  exact ⟨K, hK, fun x _ h1 h2 => hsub x h1 h2⟩

omit [InnerProductSpace 𝕜 E] in
theorem norm_ofReal_smul [NormedSpace 𝕜 E] {a : ℝ} (ha : 0 < a) (v : E) :
    ‖((a : ℝ) : 𝕜) • v‖ = a * ‖v‖ := by
  rw [norm_smul, RCLike.norm_ofReal, abs_of_pos ha]

theorem mul_le_max_one (C : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1) : C * t ≤ max C 1 := by
  rcases le_total 0 C with hC | hC
  · exact (mul_le_of_le_one_right hC ht).trans (le_max_left _ _)
  · exact (mul_nonpos_of_nonpos_of_nonneg hC ht0).trans (zero_le_one.trans (le_max_right _ _))

theorem HasCompactPerp.exists_isCompact (h : HasCompactPerp T) (r : ℝ) :
    ∃ K : Set E, IsCompact K ∧ ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ r → ‖T x‖ ≤ r →
      (x : E) ∈ K := by
  obtain ⟨K, hK, hsub⟩ := h
  set s : ℝ := max r 1
  have hs : 0 < s := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(fun y => (s : 𝕜) • y) '' K, hK.image (continuous_const_smul _), ?_⟩
  intro x hx h1 h2
  have hle : ∀ a : ℝ, a ≤ r → s⁻¹ * a ≤ 1 := fun a ha => by
    rw [inv_mul_le_iff₀ hs, mul_one]; exact ha.trans (le_max_left _ _)
  refine ⟨_, hsub (((s⁻¹ : ℝ) : 𝕜) • x) (Submodule.smul_mem _ _ hx)
    (by rw [Submodule.coe_smul, norm_ofReal_smul (inv_pos.2 hs)]; exact hle _ h1)
    (by rw [LinearPMap.map_smul, norm_ofReal_smul (inv_pos.2 hs)]; exact hle _ h2), ?_⟩
  simp only [Submodule.coe_smul, smul_smul]
  rw [← RCLike.ofReal_mul, mul_inv_cancel₀ hs.ne', RCLike.ofReal_one, one_smul]

theorem HasCompactBall.exists_isCompact (h : HasCompactBall T) (r : ℝ) :
    ∃ K : Set E, IsCompact K ∧ ∀ x : T.domain, ‖(x : E)‖ ≤ r → ‖T x‖ ≤ r → (x : E) ∈ K := by
  obtain ⟨K, hK, hsub⟩ := h
  set s : ℝ := max r 1
  have hs : 0 < s := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(fun y => (s : 𝕜) • y) '' K, hK.image (continuous_const_smul _), ?_⟩
  intro x h1 h2
  have hle : ∀ a : ℝ, a ≤ r → s⁻¹ * a ≤ 1 := fun a ha => by
    rw [inv_mul_le_iff₀ hs, mul_one]; exact ha.trans (le_max_left _ _)
  refine ⟨_, hsub (((s⁻¹ : ℝ) : 𝕜) • x)
    (by rw [Submodule.coe_smul, norm_ofReal_smul (inv_pos.2 hs)]; exact hle _ h1)
    (by rw [LinearPMap.map_smul, norm_ofReal_smul (inv_pos.2 hs)]; exact hle _ h2), ?_⟩
  simp only [Submodule.coe_smul, smul_smul]
  rw [← RCLike.ofReal_mul, mul_inv_cancel₀ hs.ne', RCLike.ofReal_one, one_smul]

theorem HasCompactBall.isCompact_closure (h : HasCompactBall T) :
    IsCompact (closure {x : E | ∃ hx : x ∈ T.domain, ‖x‖ ≤ 1 ∧ ‖T ⟨x, hx⟩‖ ≤ 1}) := by
  obtain ⟨K, hK, hsub⟩ := h
  exact hK.of_isClosed_subset isClosed_closure
    (closure_minimal (fun x ⟨hx, h1, h2⟩ => hsub ⟨x, hx⟩ h1 h2) hK.isClosed)

theorem hasCompactPerp_of_ker_eq_top (h : T.ker = ⊤) : HasCompactPerp T := by
  refine ⟨{0}, isCompact_singleton, fun x hx _ _ => ?_⟩
  rw [h, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hx
  exact hx

theorem hasCompactPerp_zero : HasCompactPerp (0 : E →ₗ.[𝕜] F) := by
  refine hasCompactPerp_of_ker_eq_top (eq_top_iff.2 fun x _ => ?_)
  exact (LinearPMap.mem_ker_iff).2 ⟨⟨x, Submodule.mem_top⟩, rfl, rfl⟩

theorem HasCompactBall.of_isClosedEmbedding {E' F' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E'] [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']
    {T' : E' →ₗ.[𝕜] F'} (h : HasCompactBall T') (J : E →L[𝕜] E')
    (hJ : Topology.IsClosedEmbedding J) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ x : T.domain, ∃ hx : J x ∈ T'.domain, ‖T' ⟨J x, hx⟩‖ ≤ C * ‖T x‖) :
    HasCompactBall T := by
  obtain ⟨K, hK, hsub⟩ := h.exists_isCompact (max ‖J‖ C)
  refine ⟨J ⁻¹' K, hJ.isCompact_preimage hK, fun x h1 h2 => ?_⟩
  obtain ⟨hy, ey⟩ := hd x
  refine hsub ⟨J x, hy⟩ ?_ (ey.trans ?_)
  · exact (J.le_opNorm x).trans ((mul_le_of_le_one_right (norm_nonneg _) h1).trans
      (le_max_left _ _))
  · exact (mul_le_of_le_one_right hC h2).trans (le_max_right _ _)

theorem HasCompactBall.of_components {E' F' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E'] [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']
    {T' : E' →ₗ.[𝕜] F'} (h : HasCompactBall T') {m : Type*} [Finite m] (P : m → E →L[𝕜] E')
    (Q : m → F →L[𝕜] F') (R : (m → E') → E) (hR : Continuous R)
    (hRP : ∀ x : E, R (fun i => P i x) = x)
    (hd : ∀ (x : T.domain) (i : m), ∃ hx : P i x ∈ T'.domain, T' ⟨P i x, hx⟩ = Q i (T x)) :
    HasCompactBall T := by
  choose K hK hsub using fun i => h.exists_isCompact (max ‖P i‖ ‖Q i‖)
  refine ⟨R '' Set.pi univ K, (isCompact_univ_pi hK).image hR, fun x h1 h2 => ?_⟩
  refine ⟨fun i => P i x, fun i _ => ?_, hRP x⟩
  obtain ⟨hx, ex⟩ := hd x i
  refine hsub i ⟨P i x, hx⟩ ?_ ?_
  · exact ((P i).le_opNorm x).trans ((mul_le_of_le_one_right (norm_nonneg _) h1).trans
      (le_max_left _ _))
  · rw [ex]
    exact ((Q i).le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) h2).trans
      (le_max_right _ _))

variable [CompleteSpace E] [CompleteSpace F]

theorem HasCompactPerp.isClosed_range (h : HasCompactPerp T) (hc : T.IsClosed) :
    _root_.IsClosed (LinearMap.range T.toFun : Set F) := by
  obtain ⟨K, hK, hsub⟩ := h
  exact isClosed_range_of_subset_isCompact hc hK hsub

theorem HasCompactPerp.adjoint (hT : Dense (T.domain : Set E)) (hc : T.IsClosed)
    (h : HasCompactPerp T) : HasCompactPerp T† := by
  classical
  have hR := h.isClosed_range hc
  obtain ⟨C, hC⟩ := (isClosed_range_iff_exists_norm_le hc).1 hR
  obtain ⟨K, hK, hsub⟩ := h.exists_isCompact (max C 1)
  have hfa := adjoint_isFormalAdjoint hT
  set B : Set F := {v | ∃ hv : v ∈ T†.domain, v ∈ T†.kerᗮ ∧ ‖v‖ ≤ 1 ∧ ‖T† ⟨v, hv⟩‖ ≤ 1}
  -- every point of the box is the image of a point of `D(T) ∩ N(T)ᗮ`
  have hpre : ∀ v ∈ B, ∃ u ∈ K, ∃ hu : u ∈ T.domain, u ∈ T.kerᗮ ∧ T ⟨u, hu⟩ = v := by
    rintro v ⟨hv, hvk, hv1, -⟩
    rw [← range_eq_orthogonal_ker_adjoint T hT hR] at hvk
    obtain ⟨x, hx⟩ := hvk
    obtain ⟨z, hz, hTz⟩ := exists_mem_orthogonal_ker_eq hc x
    have hTz' : T z = v := hTz.trans hx
    have hzC : ‖(z : E)‖ ≤ C * ‖T z‖ := hC z hz
    rw [hTz'] at hzC
    exact ⟨z, hsub z hz (hzC.trans (mul_le_max_one C (norm_nonneg _) hv1))
      (by rw [hTz']; exact hv1.trans (le_max_right _ _)), z.2, hz, by rw [hTz']⟩
  choose! f hfK hfd hfk hfv using hpre
  have hB : TotallyBounded B := by
    refine totallyBounded_of_modulus hK.totallyBounded f (fun v hv => hfK v hv) fun ε hε => ?_
    refine ⟨ε ^ 2 / 2, by positivity, fun v hv v' hv' hd => ?_⟩
    obtain ⟨hv0, -, -, hv2⟩ := id hv
    obtain ⟨hv0', -, -, hv2'⟩ := id hv'
    rw [dist_eq_norm] at hd ⊢
    -- `‖v - v'‖² = ⟪T† (v - v'), u - u'⟫`
    set y : T†.domain := ⟨v, hv0⟩ - ⟨v', hv0'⟩
    set x : T.domain := ⟨f v, hfd v hv⟩ - ⟨f v', hfd v' hv'⟩
    have hTx : T x = v - v' := by
      simp only [x, LinearPMap.map_sub, hfv v hv, hfv v' hv']
    have hey : (y : F) = v - v' := rfl
    have hsq : ‖v - v'‖ ^ 2 = RCLike.re ⟪T† y, (x : E)⟫_𝕜 := by
      rw [hfa y x, hTx, hey, ← norm_sq_eq_re_inner]
    have hTy : ‖T† y‖ ≤ 2 := by
      simp only [y, LinearPMap.map_sub]
      exact (norm_sub_le _ _).trans (by linarith)
    have hb : ‖v - v'‖ ^ 2 ≤ 2 * ‖f v - f v'‖ := by
      rw [hsq]
      refine (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
      exact mul_le_mul hTy le_rfl (norm_nonneg _) zero_le_two
    have : ‖v - v'‖ ^ 2 < ε ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  obtain ⟨K', hK', hBK⟩ := exists_isCompact_of_totallyBounded hB
  exact ⟨K', hK', fun v hv h1 h2 => hBK ⟨v.2, hv, h1, h2⟩⟩

/-! ### Weber's lemma, abstract form -/

variable {S : F →ₗ.[𝕜] G}

/-- **Weber's lemma**: if `S T = 0`, `HasCompactPerp T`, `HasCompactPair T S` and `ε` is bounded and
coercive, the box `‖u‖, ‖S u‖, ‖T† (ε u)‖ ≤ 1` lies in a compact set. [Hiptmair2002], §4 -/
theorem HasCompactPair.exists_isCompact_coeff (hT : Dense (T.domain : Set E)) (hc : T.IsClosed)
    (hmaps : ∀ x : T.domain, T x ∈ S.domain) (hcomp : ∀ x : T.domain, S ⟨T x, hmaps x⟩ = 0)
    (hTc : HasCompactPerp T) (hpair : HasCompactPair T S) (ε : F →L[𝕜] F) {lam : ℝ}
    (hlam : 0 < lam) (hcoer : ∀ y : F, lam * ‖y‖ ^ 2 ≤ RCLike.re ⟪ε y, y⟫_𝕜) :
    ∃ K : Set F, IsCompact K ∧ ∀ (u : F) (hu : u ∈ S.domain) (hu' : ε u ∈ T†.domain),
      ‖u‖ ≤ 1 → ‖S ⟨u, hu⟩‖ ≤ 1 → ‖T† ⟨ε u, hu'⟩‖ ≤ 1 → u ∈ K := by
  classical
  have hR := hTc.isClosed_range hc
  obtain ⟨C, hC⟩ := (isClosed_range_iff_exists_norm_le hc).1 hR
  obtain ⟨Kr, hKr, hsubr⟩ := hTc.exists_isCompact (max C 1)
  obtain ⟨Kv, hKv, hsubv⟩ := hpair
  set M : Submodule 𝕜 F := LinearMap.range T.toFun
  have : CompleteSpace M := hR.completeSpace_coe
  have hMker : Mᗮ = T†.ker := orthogonal_range_eq_ker_adjoint T hT
  have hfa := adjoint_isFormalAdjoint hT
  set B : Set F := {u | ∃ (hu : u ∈ S.domain) (hu' : ε u ∈ T†.domain), ‖u‖ ≤ 1 ∧
    ‖S ⟨u, hu⟩‖ ≤ 1 ∧ ‖T† ⟨ε u, hu'⟩‖ ≤ 1}
  -- the decomposition `u = T r + v`
  have hdec : ∀ u ∈ B, ∃ p : E × F, p ∈ Kr ×ˢ Kv ∧ ∃ hr : p.1 ∈ T.domain,
      p.1 ∈ T.kerᗮ ∧ T ⟨p.1, hr⟩ = M.starProjection u ∧ p.2 = u - M.starProjection u ∧
      ‖T ⟨p.1, hr⟩‖ ≤ 1 := by
    rintro u ⟨hu, hu', h1, h2, h3⟩
    obtain ⟨x, hx⟩ := M.starProjection_apply_mem u
    obtain ⟨z, hz, hTz⟩ := exists_mem_orthogonal_ker_eq hc x
    have hTz' : T z = M.starProjection u := hTz.trans hx
    have hPu : ‖M.starProjection u‖ ≤ 1 := (M.norm_starProjection_apply_le u).trans h1
    have hzr : ‖(z : E)‖ ≤ max C 1 :=
      (hC z hz).trans (by rw [hTz']; exact mul_le_max_one C (norm_nonneg _) hPu)
    -- `v = u - P u ∈ D(S) ∩ N(T†)`
    set v : F := u - M.starProjection u
    have hvM : v ∈ Mᗮ := Submodule.sub_starProjection_mem_orthogonal u
    have hvk : v ∈ T†.ker := hMker ▸ hvM
    have hvD : v ∈ T†.domain := LinearPMap.ker_le_domain hvk
    have hv0 : T† ⟨v, hvD⟩ = 0 := (LinearPMap.coe_mem_ker_iff (x := ⟨v, hvD⟩)).1 hvk
    have hTzS : (M.starProjection u : F) ∈ S.domain := hTz' ▸ hmaps z
    have hvS : v ∈ S.domain := S.domain.sub_mem hu hTzS
    have hSv : S ⟨v, hvS⟩ = S ⟨u, hu⟩ := by
      have e : (⟨v, hvS⟩ : S.domain) = ⟨u, hu⟩ - ⟨_, hTzS⟩ := rfl
      rw [e, LinearPMap.map_sub]
      have : S ⟨_, hTzS⟩ = 0 := by
        have e2 : (⟨_, hTzS⟩ : S.domain) = ⟨T z, hmaps z⟩ := Subtype.ext hTz'.symm
        rw [e2, hcomp z]
      rw [this, sub_zero]
    have hv1 : ‖v‖ ≤ 1 := by
      have : v = Mᗮ.starProjection u := (Submodule.starProjection_orthogonal_val (K := M) u).symm
      rw [this]; exact (Mᗮ.norm_starProjection_apply_le u).trans h1
    have hvB : v ∈ Kv := hsubv v hvS hvD hv1 (by rw [hSv]; exact h2)
      (by rw [hv0, norm_zero]; exact zero_le_one)
    refine ⟨((z : E), v), ⟨hsubr z hz hzr (by rw [hTz']; exact hPu.trans (le_max_right _ _)), hvB⟩, z.2, hz, hTz', rfl,
      by rw [hTz']; exact hPu⟩
  choose! p hpK hpd hpk hpT hpv hpT1 using hdec
  have hB : TotallyBounded B := by
    refine totallyBounded_of_modulus ((hKr.prod hKv).totallyBounded) p (fun u hu => hpK u hu)
      fun η hη => ?_
    set c : ℝ := 2 + 2 * ‖ε‖
    have hc0 : 0 < c := by positivity
    refine ⟨min (η / 2) (lam * (η / 2) ^ 2 / c), by positivity, fun u hu u' hu' hd => ?_⟩
    obtain ⟨hu0, hu1, h1, h2, h3⟩ := id hu
    obtain ⟨hu0', hu1', h1', h2', h3'⟩ := id hu'
    rw [Prod.dist_eq, max_lt_iff, lt_min_iff, lt_min_iff] at hd
    obtain ⟨⟨hr1, hr2⟩, hv1, hv2⟩ := hd
    rw [dist_eq_norm] at hr1 hr2 hv1 hv2 ⊢
    -- the differences
    set r : T.domain := ⟨(p u).1, hpd u hu⟩ - ⟨(p u').1, hpd u' hu'⟩
    have hr : ((r : T.domain) : E) = (p u).1 - (p u').1 := rfl
    have hTr : T r = M.starProjection u - M.starProjection u' := by
      simp only [r, LinearPMap.map_sub, hpT u hu, hpT u' hu']
    have hdu : u - u' = T r + ((p u).2 - (p u').2) := by
      rw [hTr, hpv u hu, hpv u' hu']; abel
    have hTr2 : ‖T r‖ ≤ 2 := by
      rw [LinearPMap.map_sub]
      exact (norm_sub_le _ _).trans (by linarith [hpT1 u hu, hpT1 u' hu'])
    -- `⟪ε (u - u'), T r⟫ = ⟪T† (ε u - ε u'), r⟫`
    set y : T†.domain := ⟨ε u, hu1⟩ - ⟨ε u', hu1'⟩
    have hy : (y : F) = ε (u - u') := by simp [y, _root_.map_sub]
    have hTy : ‖T† y‖ ≤ 2 := by
      simp only [y, LinearPMap.map_sub]
      exact (norm_sub_le _ _).trans (by linarith)
    have hkey : lam * ‖T r‖ ^ 2 ≤ 2 * ‖(r : E)‖ + 2 * ‖ε‖ * ‖(p u).2 - (p u').2‖ := by
      have e1 : RCLike.re ⟪ε (T r), T r⟫_𝕜 =
          RCLike.re ⟪T† y, (r : E)⟫_𝕜 - RCLike.re ⟪ε ((p u).2 - (p u').2), T r⟫_𝕜 := by
        rw [hfa y r, hy, hdu, _root_.map_add, inner_add_left, _root_.map_add, add_sub_cancel_right]
      have e2 : RCLike.re ⟪T† y, (r : E)⟫_𝕜 ≤ 2 * ‖(r : E)‖ :=
        (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right hTy (norm_nonneg _)))
      have e3 : -RCLike.re ⟪ε ((p u).2 - (p u').2), T r⟫_𝕜 ≤
          2 * ‖ε‖ * ‖(p u).2 - (p u').2‖ := by
        refine (neg_le_abs _).trans ((RCLike.abs_re_le_norm _).trans
          ((norm_inner_le_norm _ _).trans ?_))
        calc ‖ε ((p u).2 - (p u').2)‖ * ‖T r‖
            ≤ (‖ε‖ * ‖(p u).2 - (p u').2‖) * 2 :=
              mul_le_mul (ε.le_opNorm _) hTr2 (norm_nonneg _) (by positivity)
          _ = 2 * ‖ε‖ * ‖(p u).2 - (p u').2‖ := by ring
      have := hcoer (T r)
      linarith
    have hsmall : ‖T r‖ < η / 2 := by
      have hm : 2 * ‖(r : E)‖ + 2 * ‖ε‖ * ‖(p u).2 - (p u').2‖ <
          c * (lam * (η / 2) ^ 2 / c) := by
        rw [hr]
        nlinarith [mul_le_mul_of_nonneg_left hv2.le (norm_nonneg ε)]
      rw [mul_div_cancel₀ _ hc0.ne'] at hm
      have : lam * ‖T r‖ ^ 2 < lam * (η / 2) ^ 2 := lt_of_le_of_lt hkey hm
      have h2 : ‖T r‖ ^ 2 < (η / 2) ^ 2 := lt_of_mul_lt_mul_left this hlam.le
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
    rw [hdu]
    calc ‖T r + ((p u).2 - (p u').2)‖ ≤ ‖T r‖ + ‖(p u).2 - (p u').2‖ := norm_add_le _ _
      _ < η / 2 + η / 2 := add_lt_add hsmall hv1
      _ = η := by ring
  obtain ⟨K, hK, hBK⟩ := exists_isCompact_of_totallyBounded hB
  exact ⟨K, hK, fun u hu hu' h1 h2 h3 => hBK ⟨hu, hu', h1, h2, h3⟩⟩

end Feec.Operator

/-! ### The spectral theorem off the kernel -/

namespace LinearPMap

open Feec Feec.Operator

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] {A : E →ₗ.[𝕜] E}

theorem IsSkewAdjoint.exists_isEigenSq_of_resolvent (hA : A.IsSkewAdjoint) {μ : 𝕜} (hμ : μ ≠ 0)
    {v : E} (hv : resolvent A 1 (ContinuousLinearMap.adjoint (resolvent A 1) v) = μ • v) :
    ∃ ω, A.IsEigenSq ω v := by
  set R := resolvent A (1 : 𝕜)
  set R' := resolvent A (-1 : 𝕜)
  have hR : IsResolvent A 1 R := isResolvent_resolvent hA (by simp)
  have hR' : IsResolvent A (-1) R' := isResolvent_resolvent hA (by simp)
  have hadj : ContinuousLinearMap.adjoint R = -R' := by
    have := adjoint_resolvent hA (z := (1 : 𝕜)) (by simp)
    simpa using this
  rw [hadj, _root_.neg_apply] at hv
  set u := -R' v
  have hu : u ∈ A.domain := A.domain.neg_mem (hR'.mem_domain v)
  have hAu : A ⟨u, hu⟩ = v - u := by
    have : (⟨u, hu⟩ : A.domain) = -hR'.toDomain v := rfl
    rw [this, LinearPMap.map_neg, hR'.apply_resolvent]
    simp only [u, neg_smul, one_smul]
    abel
  have hvw : v = μ⁻¹ • R u := by rw [hv, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hvD : v ∈ A.domain := hvw ▸ A.domain.smul_mem _ (hR.mem_domain u)
  have hAv : A ⟨v, hvD⟩ = v - μ⁻¹ • u := by
    have : (⟨v, hvD⟩ : A.domain) = μ⁻¹ • hR.toDomain u := Subtype.ext hvw
    rw [this, LinearPMap.map_smul, hR.apply_resolvent, one_smul, smul_sub, ← hvw]
  have hAvD : A ⟨v, hvD⟩ ∈ A.domain := by
    rw [hAv]; exact A.domain.sub_mem hvD (A.domain.smul_mem _ hu)
  have hAAv : A ⟨A ⟨v, hvD⟩, hAvD⟩ = (1 - μ⁻¹) • v := by
    have : (⟨A ⟨v, hvD⟩, hAvD⟩ : A.domain) = ⟨v, hvD⟩ - μ⁻¹ • ⟨u, hu⟩ := Subtype.ext hAv
    rw [this, LinearPMap.map_sub, LinearPMap.map_smul, hAv, hAu]
    module
  exact hA.isSkewSymmetric.exists_isEigenSq hvD hAvD hAAv

omit [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] in
theorem isEigenSq_zero_of_mem_ker {v : E} (hv : v ∈ A.ker) : A.IsEigenSq 0 v := by
  obtain ⟨x, rfl, hx0⟩ := (LinearPMap.mem_ker_iff).1 hv
  have h' : A x ∈ A.domain := by rw [hx0]; exact A.domain.zero_mem
  refine ⟨x.2, h', ?_⟩
  have e : (⟨A x, h'⟩ : A.domain) = 0 := Subtype.ext hx0
  rw [e, LinearPMap.map_zero]
  simp

/-- **The spectral theorem off the kernel.** If `A` is skew-adjoint and compact off its kernel,
the eigenvectors of `A²` span a dense subspace. -/
theorem IsSkewAdjoint.dense_span_isEigenSq_of_hasCompactPerp (hA : A.IsSkewAdjoint)
    (h : HasCompactPerp A) :
    Dense (Submodule.span 𝕜 {v | ∃ ω, A.IsEigenSq ω v} : Set E) := by
  set N := A.ker
  have hNc : _root_.IsClosed (N : Set E) := isClosed_ker hA.isClosed
  have : CompleteSpace N := hNc.completeSpace_coe
  set P := Nᗮ.starProjection
  set R := resolvent A (1 : 𝕜)
  set R' := resolvent A (-1 : 𝕜)
  have hR : IsResolvent A 1 R := isResolvent_resolvent hA (by simp)
  have hR' : IsResolvent A (-1) R' := isResolvent_resolvent hA (by simp)
  have hadj : ContinuousLinearMap.adjoint R = -R' := by
    have := adjoint_resolvent hA (z := (1 : 𝕜)) (by simp)
    simpa using this
  -- `R = R† = 1` on `N`
  have hRN : ∀ n ∈ N, R n = n := by
    intro n hn
    obtain ⟨x, rfl, hx0⟩ := (LinearPMap.mem_ker_iff).1 hn
    have := hR.apply_sub x
    rwa [hx0, sub_zero, one_smul] at this
  have hRadjN : ∀ n ∈ N, ContinuousLinearMap.adjoint R n = n := by
    intro n hn
    obtain ⟨x, rfl, hx0⟩ := (LinearPMap.mem_ker_iff).1 hn
    have := hR'.apply_sub x
    rw [hx0, sub_zero, neg_one_smul, _root_.map_neg] at this
    rw [hadj, _root_.neg_apply]; exact this
  -- `R` and `R†` preserve `Nᗮ`
  have hRperp : ∀ w ∈ Nᗮ, R w ∈ Nᗮ := by
    intro w hw
    rw [Submodule.mem_orthogonal]
    intro n hn
    rw [← ContinuousLinearMap.adjoint_inner_left, hRadjN n hn]
    exact (Submodule.mem_orthogonal _ _).1 hw n hn
  have hRadjperp : ∀ w ∈ Nᗮ, ContinuousLinearMap.adjoint R w ∈ Nᗮ := by
    intro w hw
    rw [Submodule.mem_orthogonal]
    intro n hn
    rw [ContinuousLinearMap.adjoint_inner_right, hRN n hn]
    exact (Submodule.mem_orthogonal _ _).1 hw n hn
  have hRinj := hR.injective
  have hRadjinj : Function.Injective (ContinuousLinearMap.adjoint R) := by
    intro a b hab
    rw [hadj] at hab
    exact hR'.injective (neg_injective hab)
  -- `P R` is compact
  obtain ⟨K, hK, hsub⟩ := h.exists_isCompact 2
  have hPR : IsCompactOperator (P ∘L R) := by
    refine ⟨K, hK, Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) fun y hy => ?_⟩
    rw [mem_ball_zero_iff] at hy
    have hre : RCLike.re (1 : 𝕜) ≠ 0 := by simp
    have hx1 : ‖R y‖ ≤ 1 := by
      have hn1 : ‖R‖ ≤ 1 := (norm_resolvent_le hA hre).trans (by simp)
      exact (R.le_of_opNorm_le hn1 y).trans (by nlinarith [norm_nonneg y])
    have hAx : A ⟨R y, hR.mem_domain y⟩ = R y - y := by
      have := hR.sub_apply y
      rw [one_smul] at this
      rw [eq_sub_iff_add_eq]; exact (sub_eq_iff_eq_add'.1 this).symm
    have hPn : N.starProjection (R y) ∈ A.domain := A.ker_le_domain (N.starProjection_apply_mem _)
    set x : A.domain := ⟨R y, hR.mem_domain y⟩ - ⟨_, hPn⟩
    have hx : (x : E) = P (R y) := by
      change R y - N.starProjection (R y) = _
      rw [Submodule.starProjection_orthogonal_val]
    have hAx' : A x = A ⟨R y, hR.mem_domain y⟩ := by
      rw [LinearPMap.map_sub,
        (LinearPMap.coe_mem_ker_iff (x := ⟨_, hPn⟩)).1 (N.starProjection_apply_mem _), sub_zero]
    change P (R y) ∈ K
    rw [← hx]
    refine hsub x (hx ▸ Nᗮ.starProjection_apply_mem _) ?_ ?_
    · rw [hx]; exact (Nᗮ.norm_starProjection_apply_le _).trans (hx1.trans one_le_two)
    · rw [hAx', hAx]
      exact (norm_sub_le _ _).trans (by linarith)
  -- `T = P R R† P` is compact and self-adjoint
  set T : E →L[𝕜] E := (P ∘L R) ∘L (ContinuousLinearMap.adjoint R ∘L P)
  have hTc : IsCompactOperator T := hPR.comp_clm _
  have hTs : (T : E →ₗ[𝕜] E).IsSymmetric := fun x y => by
    change ⟪P (R (ContinuousLinearMap.adjoint R (P x))), y⟫_𝕜 =
      ⟪x, P (R (ContinuousLinearMap.adjoint R (P y)))⟫_𝕜
    calc ⟪P (R (ContinuousLinearMap.adjoint R (P x))), y⟫_𝕜
        = ⟪R (ContinuousLinearMap.adjoint R (P x)), P y⟫_𝕜 :=
          Submodule.inner_starProjection_left_eq_right _ _ _
      _ = ⟪ContinuousLinearMap.adjoint R (P x), ContinuousLinearMap.adjoint R (P y)⟫_𝕜 :=
          (ContinuousLinearMap.adjoint_inner_right R _ _).symm
      _ = ⟪P x, R (ContinuousLinearMap.adjoint R (P y))⟫_𝕜 :=
          ContinuousLinearMap.adjoint_inner_left R _ _
      _ = ⟪x, P (R (ContinuousLinearMap.adjoint R (P y)))⟫_𝕜 :=
          Submodule.inner_starProjection_left_eq_right _ _ _
  have hspec := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hTs
  have hdense : Dense ((⨆ μ, Module.End.eigenspace (T : Module.End 𝕜 E) μ : Submodule 𝕜 E) :
      Set E) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
    exact hspec
  refine hdense.mono (show (⨆ μ, Module.End.eigenspace (T : Module.End 𝕜 E) μ : Submodule 𝕜 E) ≤
    Submodule.span 𝕜 {v | ∃ ω, A.IsEigenSq ω v} from iSup_le fun μ => ?_)
  intro v hv
  refine Submodule.subset_span ?_
  rw [Module.End.mem_eigenspace_iff] at hv
  change P (R (ContinuousLinearMap.adjoint R (P v))) = μ • v at hv
  have hRRP : R (ContinuousLinearMap.adjoint R (P v)) ∈ Nᗮ :=
    hRperp _ (hRadjperp _ (Nᗮ.starProjection_apply_mem v))
  rw [(Nᗮ.starProjection_eq_self_iff).2 hRRP] at hv
  by_cases hμ : μ = 0
  · rw [hμ, zero_smul] at hv
    have h1 : P v = 0 := hRadjinj (hRinj (by rw [hv, _root_.map_zero, _root_.map_zero]))
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at h1
    exact ⟨0, isEigenSq_zero_of_mem_ker h1⟩
  · -- `v ∈ Nᗮ`, so `R R† v = μ v`
    have hvN : v ∈ Nᗮ := by
      have : v = μ⁻¹ • R (ContinuousLinearMap.adjoint R (P v)) := by
        rw [hv, smul_smul, inv_mul_cancel₀ hμ, one_smul]
      rw [this]; exact Nᗮ.smul_mem _ hRRP
    rw [(Nᗮ.starProjection_eq_self_iff).2 hvN] at hv
    exact hA.exists_isEigenSq_of_resolvent hμ hv

end LinearPMap

namespace Feec.C0Group

open Feec.Operator

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] {A : E →ₗ.[𝕜] E}

theorem eigenDense_of_hasCompactPerp (hA : A.IsSkewAdjoint) (h : HasCompactPerp A) :
    hA.group.EigenDense := by
  unfold EigenDense
  rw [hA.generator_group]
  exact hA.dense_span_isEigenSq_of_hasCompactPerp h

end Feec.C0Group

/-! ### Hilbert complexes -/

namespace Feec.HilbertComplex

open Feec.Operator

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

/-- **Half compactness at `i`**: `HasCompactPerp` for `d i (c.next i)`. -/
def HasCompactCyclePerpAt (i : ι) : Prop := HasCompactPerp (H.d i (c.next i))

variable {H}

theorem HasCompactPropertyAt.hasCompactCyclePerpAt {i : ι} (h : H.HasCompactPropertyAt i) :
    H.HasCompactCyclePerpAt i := by
  obtain ⟨K, hK, hsub⟩ := h
  refine ⟨K, hK, fun x hx h1 h2 => ?_⟩
  have hk := H.orthogonal_ker_le_ker_adjoint (c.prev i) i (c.next i) hx
  obtain ⟨⟨y, hy⟩, hyx, hy0⟩ := (LinearPMap.mem_ker_iff).1 hk
  subst hyx
  exact hsub _ x.2 hy h1 h2 (by rw [hy0, norm_zero]; exact zero_le_one)

theorem hasCompactCyclePerpAt_of_not_rel {i : ι} (hi : ∀ j, ¬ c.Rel i j) :
    H.HasCompactCyclePerpAt i := by
  rw [HasCompactCyclePerpAt, H.shape i (c.next i) (hi _)]
  exact hasCompactPerp_zero

theorem HasCompactCyclePerpAt.adjoint_prev {i : ι} (h : H.HasCompactCyclePerpAt (c.prev i)) :
    HasCompactPerp ((H.d (c.prev i) i)†) := by
  by_cases hrel : c.Rel (c.prev i) i
  · have h' : HasCompactPerp (H.d (c.prev i) i) := by
      have := h; rw [HasCompactCyclePerpAt, c.next_eq' hrel] at this; exact this
    exact h'.adjoint (H.dense _ _) (H.closed _ _)
  · rw [H.shape _ _ hrel, adjoint_zero]
    exact hasCompactPerp_zero

variable [Fintype ι]

theorem single_mem_ker_wave [DecidableEq ι] {i : ι} {h : W i} (hh : h ∈ H.harmonic i) :
    PiLp.single 2 i h ∈ H.wave.ker := by
  have hd : h ∈ (H.d i (c.next i)).domain := H.cycles_le_domain i hh.1
  have hd' : h ∈ (H.dual.d i (c.symm.next i)).domain := LinearPMap.ker_le_domain hh.2
  have h1 := H.single_mem_totalDomain i hd
  have h2 := H.dual.single_mem_totalDomain i hd'
  have hz1 : H.totalD ⟨_, h1⟩ = 0 := by
    have e := H.inner_totalD_single (H.totalD ⟨_, h1⟩) i h h1
    have h0 : H.d i (c.next i) ⟨h, by simpa using h1 i (c.next i)⟩ = 0 :=
      (LinearPMap.coe_mem_ker_iff (x := ⟨h, _⟩)).1 hh.1
    rw [h0, inner_zero_right] at e
    exact inner_self_eq_zero.1 e
  have hz2 : H.dual.totalD ⟨_, h2⟩ = 0 := by
    have e := H.dual.inner_totalD_single (H.dual.totalD ⟨_, h2⟩) i h h2
    have h0 : H.dual.d i (c.symm.next i) ⟨h, by simpa using h2 i (c.symm.next i)⟩ = 0 :=
      (LinearPMap.coe_mem_ker_iff (x := ⟨h, _⟩)).1 hh.2
    rw [h0, inner_zero_right] at e
    exact inner_self_eq_zero.1 e
  refine (LinearPMap.mem_ker_iff).2 ⟨⟨_, h1, h2⟩, rfl, ?_⟩
  change H.totalD ⟨_, h1⟩ - H.dual.totalD ⟨_, h2⟩ = 0
  rw [hz1, hz2, sub_zero]

theorem hasCompactPerp_wave (h : ∀ i, H.HasCompactCyclePerpAt i) : HasCompactPerp H.wave := by
  classical
  choose Kb hKb hsubb using fun i => (h (c.prev i)).adjoint_prev
  choose Ka hKa hsuba using h
  refine ⟨(PiLp.homeomorph 2 W) ⁻¹' Set.pi univ (fun i => Ka i + Kb i),
    (PiLp.homeomorph 2 W).isCompact_preimage.2 (isCompact_univ_pi fun i => (hKa i).add (hKb i)),
    fun z hz h1 h2 => ?_⟩
  intro i _
  change (z : PiLp 2 W) i ∈ Ka i + Kb i
  set x : W i := (z : PiLp 2 W) i
  have hx : x ∈ (H.d i (c.next i)).domain := z.2.1 i (c.next i)
  have hx' : x ∈ ((H.d (c.prev i) i)†).domain := z.2.2 i (c.prev i)
  have hx1 : ‖x‖ ≤ 1 := (PiLp.norm_apply_le _ i).trans h1
  have hsq := H.norm_wave_sq z
  have hT : ‖H.totalD ⟨z, z.2.1⟩‖ ≤ 1 := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).1 ?_
    nlinarith [norm_nonneg (H.dual.totalD ⟨z, z.2.2⟩), norm_nonneg (H.wave z)]
  have hT' : ‖H.dual.totalD ⟨z, z.2.2⟩‖ ≤ 1 := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).1 ?_
    nlinarith [norm_nonneg (H.totalD ⟨z, z.2.1⟩), norm_nonneg (H.wave z)]
  have hdx : ‖H.d i (c.next i) ⟨x, hx⟩‖ ≤ 1 :=
    (H.norm_d_le_norm_totalD ⟨z, z.2.1⟩ i (c.next i)).trans hT
  have hdx' : ‖(H.d (c.prev i) i)† ⟨x, hx'⟩‖ ≤ 1 :=
    (H.dual.norm_d_le_norm_totalD ⟨z, z.2.2⟩ i (c.prev i)).trans hT'
  -- `x ⊥ ℌⁱ`
  have hxh : x ∈ (H.harmonic i)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro g hg
    have e := Submodule.inner_right_of_mem_orthogonal (H.single_mem_ker_wave hg) hz
    rw [PiLp.inner_apply, Finset.sum_eq_single i (fun j _ hj => by
      rw [PiLp.single_eq_of_ne (p := 2) hj, inner_zero_left]) (by simp),
      PiLp.single_eq_same] at e
    exact e
  -- the splitting `x = b + a`
  set Z : Submodule 𝕜 (W i) := H.cycles i
  have : CompleteSpace Z := (H.isClosed_cycles i).completeSpace_coe
  set N' : Submodule 𝕜 (W i) := ((H.d (c.prev i) i)†).ker
  have : CompleteSpace N' :=
    (LinearPMap.isClosed_ker (adjoint_isClosed (H.dense _ _))).completeSpace_coe
  set a : W i := Z.starProjection x
  have haZ : a ∈ Z := Z.starProjection_apply_mem x
  have haD : a ∈ (H.d i (c.next i)).domain := H.cycles_le_domain i haZ
  set b : W i := x - a
  have hbZ : b ∈ Zᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hbN : b ∈ N' := H.orthogonal_ker_le_ker_adjoint (c.prev i) i (c.next i) hbZ
  have hbD : b ∈ (H.d i (c.next i)).domain := (H.d i (c.next i)).domain.sub_mem hx haD
  have hbD' : b ∈ ((H.d (c.prev i) i)†).domain := LinearPMap.ker_le_domain hbN
  have haD' : a ∈ ((H.d (c.prev i) i)†).domain := by
    have : a = x - b := by simp [b]
    rw [this]; exact Submodule.sub_mem _ hx' hbD'
  have hdb : H.d i (c.next i) ⟨b, hbD⟩ = H.d i (c.next i) ⟨x, hx⟩ := by
    have e : (⟨b, hbD⟩ : (H.d i (c.next i)).domain) = ⟨x, hx⟩ - ⟨a, haD⟩ := rfl
    rw [e, LinearPMap.map_sub, (LinearPMap.coe_mem_ker_iff (x := ⟨a, haD⟩)).1 haZ, sub_zero]
  have hda : (H.d (c.prev i) i)† ⟨a, haD'⟩ = (H.d (c.prev i) i)† ⟨x, hx'⟩ := by
    have e : (⟨a, haD'⟩ : ((H.d (c.prev i) i)†).domain) = ⟨x, hx'⟩ - ⟨b, hbD'⟩ :=
      Subtype.ext (by simp [b])
    rw [e, LinearPMap.map_sub, (LinearPMap.coe_mem_ker_iff (x := ⟨b, hbD'⟩)).1 hbN, sub_zero]
  -- `a ∈ N(d†)ᗮ`: its projection onto `N(d†)` is harmonic and orthogonal to `a`
  have haperp : a ∈ N'ᗮ := by
    set a1 : W i := N'.starProjection a
    have ha2 : a - a1 ∈ N'ᗮ := Submodule.sub_starProjection_mem_orthogonal a
    have ha2Z : a - a1 ∈ Z := H.orthogonal_ker_adjoint_le_ker (c.prev i) i (c.next i) ha2
    have ha1Z : a1 ∈ Z := by
      have : a1 = a - (a - a1) := by abel
      rw [this]; exact Z.sub_mem haZ ha2Z
    have ha1H : a1 ∈ H.harmonic i := ⟨ha1Z, N'.starProjection_apply_mem a⟩
    -- `⟪a1, a⟫ = 0` since `a = x - b`, `x ⊥ ℌ`, `b ⊥ 𝔷`
    have e1 : ⟪a1, x⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal ha1H hxh
    have e2 : ⟪a1, b⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal ha1Z hbZ
    have e3 : ⟪a1, a - a1⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal (N'.starProjection_apply_mem a) ha2
    have e4 : ⟪a1, a⟫_𝕜 = 0 := by
      have : a = x - b := by simp [b]
      rw [this, inner_sub_right, e1, e2, sub_zero]
    have h0 : ⟪a1, a1⟫_𝕜 = 0 := by
      rw [inner_sub_right, e4, zero_sub, neg_eq_zero] at e3; exact e3
    have ha10 : a1 = 0 := inner_self_eq_zero.1 h0
    rw [← Submodule.starProjection_apply_eq_zero_iff]
    exact ha10
  have hb1 : ‖b‖ ≤ 1 := by
    have : b = Zᗮ.starProjection x := (Submodule.starProjection_orthogonal_val (K := Z) x).symm
    rw [this]; exact (Zᗮ.norm_starProjection_apply_le x).trans hx1
  have ha1 : ‖a‖ ≤ 1 := (Z.norm_starProjection_apply_le x).trans hx1
  have hbK : b ∈ Ka i := hsuba i ⟨b, hbD⟩ hbZ hb1 (by rw [hdb]; exact hdx)
  have haK : a ∈ Kb i := hsubb i ⟨a, haD'⟩ haperp ha1 (by rw [hda]; exact hdx')
  have hxab : x = b + a := by simp [b]
  rw [hxab]
  exact Set.add_mem_add hbK haK

variable [NormedSpace ℝ (PiLp 2 W)] [IsScalarTower ℝ 𝕜 (PiLp 2 W)]

/-- **`EigenDense` from half compactness in every degree.** -/
theorem eigenDense_wave_of_compact_perp (h : ∀ i, H.HasCompactCyclePerpAt i) :
    H.isSkewAdjoint_wave.group.EigenDense :=
  C0Group.eigenDense_of_hasCompactPerp _ (hasCompactPerp_wave h)

end Feec.HilbertComplex

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {W : Fin 3 → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [NormedSpace ℝ (PiLp 2 W)] [IsScalarTower ℝ 𝕜 (PiLp 2 W)]

/-- **Short complexes: half compactness at `0` and `1` suffices** for `EigenDense`. -/
theorem eigenDense_wave_fin3 (H : HilbertComplex 𝕜 ComplexShape.fin3 W)
    (h0 : H.HasCompactCyclePerpAt 0) (h1 : H.HasCompactCyclePerpAt 1) :
    H.isSkewAdjoint_wave.group.EigenDense := by
  refine eigenDense_wave_of_compact_perp fun i => ?_
  fin_cases i
  · exact h0
  · exact h1
  · exact hasCompactCyclePerpAt_of_not_rel fun j hj => by
      simp only [ComplexShape.window_rel] at hj; omega

end Feec.HilbertComplex
