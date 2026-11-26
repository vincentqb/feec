module

public import Feec.FiniteElement.FormBGGElasticity

/-!
# The Hessian, elasticity and div–div complexes of forms: closed range and cohomology

If `HΛ(Ω)` has `H¹`-regular decompositions and the cohomology of a point, the Hessian, elasticity
and div–div complexes of forms have closed range and cohomology only in degree `0`
([ArnoldHu2021], Thm 6), identified on bounded `Ω`.

## Main results

* `hessianFormData_bggVerdict`, `hessianFormData_homologyIs_zero`: the Hessian complex.
* `elasticityFormData_bggVerdict`, `elasticityFormData_homologyIs_zero`: the elasticity complex.
* `divDivFormData_bggVerdict`, `divDivFormData_homologyIs_zero`: the div–div complex.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §4

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.FiniteElement

open MeasureTheory
open Feec.Domain Feec.HilbertComplex

variable {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)

/-! ### Closed range and the dimension of the cohomology -/

theorem finrank_vecRow_cohomology_of [∀ k, FiniteDimensional ℝ ((formRow n hΩ).cohomology k)]
    (hH : ∀ k, Module.finrank ℝ ((formRow n hΩ).cohomology k) = if k = 0 then 1 else 0) (k : ℤ) :
    Module.finrank ℝ ((vecRow n hΩ).cohomology k) = if k = 0 then n else 0 := by
  rw [finrank_pi_cohomology, hH, Fintype.card_fin]
  split_ifs <;> simp

/-- If `HΛ(Ω)` has `H¹`-regular decompositions from `0` on and the cohomology of a point, the
Hessian complex has closed range and `dim Hⁱ = [i = 0] (n + 1)` ([ArnoldHu2021], Thm 6). -/
theorem hessianFormData_bggVerdict (h : (deRham ℝ n).HasRegularDecomposition Ω 0)
    [∀ k, FiniteDimensional ℝ ((formRow n hΩ).cohomology k)]
    (hH : ∀ k, Module.finrank ℝ ((formRow n hΩ).cohomology k) = if k = 0 then 1 else 0) (i : ℤ) :
    (hessianFormData hΩ).BGGVerdict 0 i ∧
      Module.finrank ℝ (((hessianFormData hΩ).domainData.bgg 0).homology i) =
        if i = 0 then n + 1 else 0 := by
  set D := hessianFormData hΩ
  have : ∀ k, FiniteDimensional ℝ (D.H.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((formRow n hΩ).cohomology k))
  have : ∀ k, FiniteDimensional ℝ (D.Ht.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow n hΩ).cohomology k))
  have hS := hessianFormData_antilipschitz hΩ
  have htop := hessianFormData_regularDecomposition hΩ h
  refine ⟨D.bggVerdict hS htop i, ?_⟩
  rw [D.finrank_bgg_homology_eq_ite hS htop hH (finrank_vecRow_cohomology_of hΩ hH), Nat.add_comm]

/-- If `HΛ(Ω)`, `Ω ⊆ ℝ³`, has `H¹`-regular decompositions from `1` on and the cohomology of a
point, the elasticity complex has closed range and `dim Hⁱ = [i = 0] 6` ([ArnoldHu2021], Thm 6). -/
theorem elasticityFormData_bggVerdict {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω)
    (h : (deRham ℝ 3).HasRegularDecomposition Ω 1)
    [∀ k, FiniteDimensional ℝ ((formRow 3 hΩ).cohomology k)]
    (hH : ∀ k, Module.finrank ℝ ((formRow 3 hΩ).cohomology k) = if k = 0 then 1 else 0) (i : ℤ) :
    (elasticityFormData hΩ).BGGVerdict 1 i ∧
      Module.finrank ℝ (((elasticityFormData hΩ).domainData.bgg 1).homology i) =
        if i = 0 then 6 else 0 := by
  set D := elasticityFormData hΩ
  have : ∀ k, FiniteDimensional ℝ (D.H.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow 3 hΩ).cohomology k))
  have : ∀ k, FiniteDimensional ℝ (D.Ht.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow 3 hΩ).cohomology k))
  have hS := elasticityFormData_antilipschitz hΩ
  have htop := elasticityFormData_regularDecomposition hΩ h
  exact ⟨D.bggVerdict hS htop i, D.finrank_bgg_homology_eq_ite hS htop
    (finrank_vecRow_cohomology_of hΩ hH) (finrank_vecRow_cohomology_of hΩ hH) i⟩

/-- If `HΛ(Ω)`, `n ≥ 1`, has `H¹`-regular decompositions from `n - 1` on and the cohomology of a
point, the div–div complex has closed range, `dim Hⁱ = [i = 0] (n + 1)`; [ArnoldHu2021], Thm 6. -/
theorem divDivFormData_bggVerdict [NeZero n]
    (h : (deRham ℝ n).HasRegularDecomposition Ω ((n : ℤ) - 1))
    [∀ k, FiniteDimensional ℝ ((formRow n hΩ).cohomology k)]
    (hH : ∀ k, Module.finrank ℝ ((formRow n hΩ).cohomology k) = if k = 0 then 1 else 0) (i : ℤ) :
    (divDivFormData hΩ).BGGVerdict ((n : ℤ) - 1) i ∧
      Module.finrank ℝ (((divDivFormData hΩ).domainData.bgg ((n : ℤ) - 1)).homology i) =
        if i = 0 then n + 1 else 0 := by
  set D := divDivFormData hΩ
  have : ∀ k, FiniteDimensional ℝ (D.H.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow n hΩ).cohomology k))
  have : ∀ k, FiniteDimensional ℝ (D.Ht.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((formRow n hΩ).cohomology k))
  have hS := divDivFormData_antilipschitz hΩ
  have htop := divDivFormData_regularDecomposition hΩ h
  exact ⟨D.bggVerdict hS htop i, D.finrank_bgg_homology_eq_ite hS htop
    (finrank_vecRow_cohomology_of hΩ hH) hH i⟩

/-! ### The cohomology in degree `0`: affine functions, rigid motions, the fields `a + b x` -/

section Lowest

variable (hb : Bornology.IsBounded Ω)

/-- The constant `0`-form `1` on a bounded open `Ω`. -/
def constOne : L2F ℝ Ω (formIdx n 0) :=
  toL2F (ψ := fun _ _ => (1 : ℝ)) fun _ => memLp_of_continuous hΩ.measurableSet hb continuous_const

theorem coeFn_constOne (s : formIdx n 0) :
    ⇑(constOne hΩ hb s) =ᵐ[volume.restrict Ω] fun _ => (1 : ℝ) :=
  (memLp_of_continuous hΩ.measurableSet hb continuous_const).coeFn_toLp

theorem dxL2_constOne_apply (a : Fin n) (t : formIdx n (0 + 1)) :
    dxL2 0 a (constOne hΩ hb) t = if a ∈ t.1 then constOne hΩ hb ⟨∅, by simp⟩ else 0 := by
  rw [dxL2_apply, Fintype.sum_eq_single ⟨∅, by simp⟩ fun r hr => absurd (formIdx_zero_eq r _) hr,
    wsCoeff_eq]
  obtain ⟨l, hl⟩ := Finset.card_eq_one.1 (by have := t.2; omega : t.1.card = 1)
  by_cases ha : a ∈ t.1
  · have hal : a = l := by rw [hl, Finset.mem_singleton] at ha; exact ha
    subst hal
    rw [ite_eq_left ⟨ha, by rw [hl, Finset.erase_singleton]⟩, ite_eq_left ha, hl]
    rw [Feec.ExteriorFibre.sgn, Finset.filter_singleton, ite_eq_right (lt_irrefl a)]
    simp
  · rw [ite_eq_right fun h => ha h.1, ite_eq_right ha, zero_smul]

theorem exists_dotProduct_mem_maximal (b : Fin n → ℝ) :
    ∃ (hw : ∀ _ : formIdx n 0, MemLp (fun x : Fin n → ℝ => b ⬝ᵥ x) 2 (volume.restrict Ω))
      (hℓ : toL2F hw ∈ ((extDerivOp ℝ n 0).maximal Ω).domain),
      (extDerivOp ℝ n 0).maximal Ω ⟨_, hℓ⟩ = ∑ c, b c • dxL2 0 c (constOne hΩ hb) := by
  have hm := hΩ.measurableSet
  set w : formIdx n 0 → (Fin n → ℝ) → ℝ := fun _ x => b ⬝ᵥ x
  set L : (Fin n → ℝ) →L[ℝ] ℝ := ∑ c, b c • ContinuousLinearMap.proj c
  have hL : ∀ x, L x = b ⬝ᵥ x := fun x => by simp [L, dotProduct]
  have hws : ∀ s, ContDiff ℝ 1 (w s) := fun s => by
    have : w s = L := funext fun x => (hL x).symm
    rw [this]; exact L.contDiff
  have hw : ∀ s, MemLp (w s) 2 (volume.restrict Ω) := fun s =>
    memLp_of_continuous hm hb (hws s).continuous
  have hdw : ∀ t, MemLp ((extDerivOp ℝ n 0).apply w t) 2 (volume.restrict Ω) :=
    fun t => memLp_of_continuous hm hb
      ((extDerivOp ℝ n 0).continuous_apply (extDerivOp_isOrderLE 0) hws t)
  obtain ⟨hℓ, eℓ⟩ := extDerivOp_smooth_mem_maximal_domain hΩ hws hw hdw
  refine ⟨hw, hℓ, ?_⟩
  rw [eℓ]
  refine PiLp.ext fun t => ?_
  obtain ⟨l, hl⟩ := Finset.card_eq_one.1 (by have := t.2; omega : t.1.card = 1)
  have hsum : (∑ c, b c • dxL2 0 c (constOne hΩ hb)) t = b l • constOne hΩ hb ⟨∅, by simp⟩ := by
    rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single l (fun c _ hc => by
      rw [WithLp.ofLp_smul, Pi.smul_apply, dxL2_constOne_apply, hl,
        ite_eq_right (by simpa using hc), smul_zero]) (by simp)]
    rw [WithLp.ofLp_smul, Pi.smul_apply, dxL2_constOne_apply, hl,
      ite_eq_left (Finset.mem_singleton_self l)]
  rw [hsum]
  have ht : t = ⟨{l}, by simp⟩ := Subtype.ext hl
  refine Lp.ext ?_
  filter_upwards [(hdw t).coeFn_toLp, Lp.coeFn_smul (b l) (constOne hΩ hb ⟨∅, by simp⟩),
    coeFn_constOne hΩ hb ⟨∅, by simp⟩] with x h1 h2 h3
  change ((hdw t).toLp _ : (Fin n → ℝ) → ℝ) x = _
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, mul_one]
  subst ht
  rw [extDerivOp_zero_apply]
  have : w ⟨∅, by simp⟩ = L := funext fun x => (hL x).symm
  rw [this, L.fderiv]
  simp [L, coordDir, Pi.single_apply]

theorem constOne_mem_ker : constOne hΩ hb ∈ ((extDerivOp ℝ n 0).maximal Ω).ker := by
  have hws : ∀ s : formIdx n 0, ContDiff ℝ 1 fun _ : Fin n → ℝ => (1 : ℝ) := fun _ =>
    contDiff_const
  have hw : ∀ s : formIdx n 0, MemLp (fun _ : Fin n → ℝ => (1 : ℝ)) 2 (volume.restrict Ω) :=
    fun _ => memLp_of_continuous hΩ.measurableSet hb continuous_const
  have hdw : ∀ t, MemLp ((extDerivOp ℝ n 0).apply (fun _ _ => (1 : ℝ)) t) 2
      (volume.restrict Ω) := fun t => memLp_of_continuous hΩ.measurableSet hb
    ((extDerivOp ℝ n 0).continuous_apply (extDerivOp_isOrderLE 0) hws t)
  obtain ⟨h, e⟩ := extDerivOp_smooth_mem_maximal_domain hΩ hws hw hdw
  refine LinearPMap.mem_ker_iff.2 ⟨⟨_, h⟩, rfl, e.trans (PiLp.ext fun t => ?_)⟩
  rw [WithLp.ofLp_zero, Pi.zero_apply]
  refine Lp.ext ?_
  obtain ⟨l, hl⟩ := Finset.card_eq_one.1 (by have := t.2; omega : t.1.card = 1)
  obtain rfl : t = ⟨{l}, by simp⟩ := Subtype.ext hl
  filter_upwards [(hdw _).coeFn_toLp, Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x h1 h2
  change ((hdw _).toLp _ : (Fin n → ℝ) → ℝ) x = _
  rw [h1, h2, extDerivOp_zero_apply]
  simp

theorem ker_maximal_zero_eq_span
    (hH0 : Module.finrank ℝ ((formRow n hΩ).cohomology 0) = 1) :
    ((extDerivOp ℝ n 0).maximal Ω).ker = ℝ ∙ constOne hΩ hb := by
  have hb0 : (formRow n hΩ).boundaries 0 = ⊥ := by
    have := LocalElement.subsingleton_L2F_of_neg Ω (n := n)
      (j := (ComplexShape.up ℤ).prev 0) (by rw [CochainComplex.prev]; norm_num)
    refine eq_bot_iff.2 ?_
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y 0, map_zero]
    exact Submodule.zero_mem _
  have hz : (formRow n hΩ).cycles 0 = ((extDerivOp ℝ n 0).maximal Ω).ker := by
    rw [(formRow n hΩ).cycles_eq (show (ComplexShape.up ℤ).Rel (0 : ℤ) (0 + 1) from rfl),
      formRow_d]
  have h1 : Module.finrank ℝ ((extDerivOp ℝ n 0).maximal Ω).ker = 1 := by
    rw [← hz, ← hH0]
    exact ((Submodule.quotEquivOfEqBot _ (by
      rw [hb0, Submodule.comap_bot, Submodule.ker_subtype])).finrank_eq).symm
  have hne : constOne hΩ hb ≠ 0 := by
    refine toL2F_ne_zero _ (fun hΩ0 => ?_) (i := ⟨∅, by simp⟩) fun _ => one_ne_zero
    have hae : ae (volume.restrict Ω) = ⊥ := ae_eq_bot.2 (Measure.restrict_eq_zero.2 hΩ0)
    have : Subsingleton (L2F ℝ Ω (formIdx n 0)) := ⟨fun u v => PiLp.ext fun s => Lp.ext (by
      rw [Filter.EventuallyEq, hae]; exact Filter.eventually_bot)⟩
    have h0 := Module.finrank_zero_of_subsingleton (R := ℝ)
      (M := ((extDerivOp ℝ n 0).maximal Ω).ker)
    omega
  have : FiniteDimensional ℝ ((extDerivOp ℝ n 0).maximal Ω).ker :=
    Module.finite_of_finrank_pos (by rw [h1]; exact one_pos)
  exact (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2
    (constOne_mem_ker hΩ hb)) (by rw [finrank_span_singleton hne, h1])).symm

theorem exists_maximal_eq_sum_dxL2_iff
    (hker : ((extDerivOp ℝ n 0).maximal Ω).ker = ℝ ∙ constOne hΩ hb) (b : Fin n → ℝ)
    (u : L2F ℝ Ω (formIdx n 0)) :
    (∃ hu : u ∈ ((extDerivOp ℝ n 0).maximal Ω).domain,
      (extDerivOp ℝ n 0).maximal Ω ⟨u, hu⟩ = ∑ c, b c • dxL2 0 c (constOne hΩ hb)) ↔
      ∃ a : ℝ, ∀ s, ⇑(u s) =ᵐ[volume.restrict Ω] fun x => a + b ⬝ᵥ x := by
  set A := (extDerivOp ℝ n 0).maximal Ω
  obtain ⟨hw, hℓ, hdℓ⟩ := exists_dotProduct_mem_maximal hΩ hb b
  have h1 : constOne hΩ hb ∈ A.ker := constOne_mem_ker hΩ hb
  obtain ⟨y₁, hy₁, hy₁0⟩ := LinearPMap.mem_ker_iff.1 h1
  constructor
  · rintro ⟨hu, hdu⟩
    have hk : u - toL2F hw ∈ A.ker := LinearPMap.mem_ker_iff.2
      ⟨⟨u, hu⟩ - ⟨_, hℓ⟩, rfl, by rw [A.map_sub, hdu, hdℓ, sub_self]⟩
    rw [hker, Submodule.mem_span_singleton] at hk
    obtain ⟨a, ha⟩ := hk
    refine ⟨a, fun s => ?_⟩
    have hu' : u = a • constOne hΩ hb + toL2F hw := by rw [ha, sub_add_cancel]
    filter_upwards [show ⇑(u s) =ᵐ[volume.restrict Ω] _ from by rw [hu'],
      Lp.coeFn_add (a • constOne hΩ hb s) (toL2F hw s), Lp.coeFn_smul a (constOne hΩ hb s),
      coeFn_constOne hΩ hb s, (hw s).coeFn_toLp] with x h0 h1 h2 h3 h4
    rw [h0]
    change ((a • constOne hΩ hb s + toL2F hw s : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x = _
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, smul_eq_mul, mul_one]
    change a + ((hw s).toLp _ : (Fin n → ℝ) → ℝ) x = _
    rw [h4]
  · rintro ⟨a, ha⟩
    have hu : u = a • constOne hΩ hb + toL2F hw := by
      refine PiLp.ext fun s => Lp.ext ?_
      filter_upwards [ha s, Lp.coeFn_add (a • constOne hΩ hb s) (toL2F hw s),
        Lp.coeFn_smul a (constOne hΩ hb s), coeFn_constOne hΩ hb s, (hw s).coeFn_toLp]
        with x h0 h1 h2 h3 h4
      rw [h0]
      change _ = ((a • constOne hΩ hb s + toL2F hw s : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, smul_eq_mul, mul_one]
      change _ = a + ((hw s).toLp _ : (Fin n → ℝ) → ℝ) x
      rw [h4]
    have hmem : u ∈ A.domain := by
      rw [hu, hy₁]; exact A.domain.add_mem (A.domain.smul_mem a y₁.2) hℓ
    refine ⟨hmem, ?_⟩
    have : (⟨u, hmem⟩ : A.domain) = a • y₁ + ⟨_, hℓ⟩ := Subtype.ext (show u = _ by
      rw [hu, hy₁]; rfl)
    rw [this, A.map_add, A.map_smul, hy₁0, smul_zero]
    exact (zero_add _).trans hdℓ

theorem mem_formRow_ker_zero_iff (hker : ((extDerivOp ℝ n 0).maximal Ω).ker = ℝ ∙ constOne hΩ hb)
    {f : L2F ℝ Ω (formIdx n 0)} :
    f ∈ ((formRow n hΩ).d 0 (0 + 1)).ker ↔ ∃ c : ℝ, c • constOne hΩ hb = f := by
  rw [formRow_d, hker, Submodule.mem_span_singleton]

theorem mem_vecRow_ker_zero_iff (hker : ((extDerivOp ℝ n 0).maximal Ω).ker = ℝ ∙ constOne hΩ hb)
    {v : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n 0))} :
    v ∈ ((vecRow n hΩ).d 0 (0 + 1)).ker ↔
      ∃ c : Fin n → ℝ, WithLp.toLp 2 (fun a => c a • constOne hΩ hb) = v := by
  constructor
  · intro hv
    obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hv
    have h : ∀ a, ∃ c : ℝ, c • constOne hΩ hb =
        (y : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n 0))) a := fun a => by
      refine Submodule.mem_span_singleton.1 ?_
      rw [← hker]
      refine LinearPMap.mem_ker_iff.2 ⟨⟨_, (mem_vecRow_domain hΩ).1 y.2 a⟩, rfl, ?_⟩
      rw [← vecRow_d_apply hΩ y a, hy]; rfl
    choose c hc using h
    exact ⟨c, PiLp.ext hc⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨y₁, hy₁, hy₁0⟩ := LinearPMap.mem_ker_iff.1 (constOne_mem_ker hΩ hb)
    have hmem : (WithLp.toLp 2 (fun a => c a • constOne hΩ hb) :
        PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n 0))) ∈
        ((vecRow n hΩ).d 0 (0 + 1)).domain :=
      (mem_vecRow_domain hΩ).2 fun a => by
        rw [PiLp.toLp_apply, hy₁]; exact Submodule.smul_mem _ _ y₁.2
    refine LinearPMap.mem_ker_iff.2 ⟨⟨_, hmem⟩, rfl, PiLp.ext fun a => ?_⟩
    rw [vecRow_d_apply hΩ]
    have : (⟨_, (mem_vecRow_domain hΩ).1 hmem a⟩ :
        ((extDerivOp ℝ n 0).maximal Ω).domain) = c a • y₁ :=
      Subtype.ext (show (c a • constOne hΩ hb : L2F ℝ Ω (formIdx n 0)) =
        c a • (y₁ : L2F ℝ Ω (formIdx n 0)) by rw [hy₁])
    rw [this, LinearPMap.map_smul, hy₁0, smul_zero]; rfl

theorem wsL2_const (b : Fin n → ℝ) :
    wsL2 (Ω := Ω) 0 (WithLp.toLp 2 fun c => b c • constOne hΩ hb) =
      ∑ c, b c • dxL2 0 c (constOne hΩ hb) := by
  rw [wsL2_eq_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [PiLp.toLp_apply, map_smul]

theorem hessian_lowest_iff (hker : ((extDerivOp ℝ n 0).maximal Ω).ker = ℝ ∙ constOne hΩ hb)
    (u : L2F ℝ Ω (formIdx n 0)) :
    (∃ hu : u ∈ ((formRow n hΩ).d 0 (0 + 1)).domain,
      ∃ v ∈ ((vecRow n hΩ).d 0 (0 + 1)).ker, wsL2 0 v = (formRow n hΩ).d 0 (0 + 1) ⟨u, hu⟩) ↔
      ∃ (a : ℝ) (b : Fin n → ℝ), ∀ s, ⇑(u s) =ᵐ[volume.restrict Ω] fun x => a + b ⬝ᵥ x := by
  simp only [mem_vecRow_ker_zero_iff hΩ hb hker]
  rw [formRow_d]
  constructor
  · rintro ⟨hu, _, ⟨b, rfl⟩, h⟩
    obtain ⟨a, ha⟩ := (exists_maximal_eq_sum_dxL2_iff hΩ hb hker b u).1
      ⟨hu, h.symm.trans (wsL2_const hΩ hb b)⟩
    exact ⟨a, b, ha⟩
  · rintro ⟨a, b, ha⟩
    obtain ⟨hu, h⟩ := (exists_maximal_eq_sum_dxL2_iff hΩ hb hker b u).2 ⟨a, ha⟩
    exact ⟨hu, _, ⟨b, rfl⟩, (wsL2_const hΩ hb b).trans h.symm⟩

theorem sum_single_smul_dxL2 (c : Fin n) (r : ℝ) (φ : L2F ℝ Ω (formIdx n 0)) :
    ∑ i, (r • Pi.single c 1 : Fin n → ℝ) i • dxL2 0 i φ = r • dxL2 0 c φ := by
  rw [Finset.sum_eq_single c (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem exists_vecRow_d_eq_sum_dxL2_iff
    (hker : ((extDerivOp ℝ n 0).maximal Ω).ker = ℝ ∙ constOne hΩ hb) (β : Fin n → Fin n → ℝ)
    (u : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n 0))) :
    (∃ hu : u ∈ ((vecRow n hΩ).d 0 (0 + 1)).domain,
      (vecRow n hΩ).d 0 (0 + 1) ⟨u, hu⟩ =
        WithLp.toLp 2 fun a => ∑ c, β a c • dxL2 0 c (constOne hΩ hb)) ↔
      ∃ α : Fin n → ℝ, ∀ a s, ⇑(u a s) =ᵐ[volume.restrict Ω] fun x => α a + β a ⬝ᵥ x := by
  constructor
  · rintro ⟨hu, h⟩
    have : ∀ a, ∃ α : ℝ, ∀ s, ⇑(u a s) =ᵐ[volume.restrict Ω] fun x => α + β a ⬝ᵥ x := fun a =>
      (exists_maximal_eq_sum_dxL2_iff hΩ hb hker (β a) (u a)).1
        ⟨(mem_vecRow_domain hΩ).1 hu a, by rw [← vecRow_d_apply hΩ ⟨u, hu⟩ a, h]⟩
    choose α hα using this
    exact ⟨α, hα⟩
  · rintro ⟨α, hα⟩
    have h : ∀ a, ∃ hu : u a ∈ ((extDerivOp ℝ n 0).maximal Ω).domain,
        (extDerivOp ℝ n 0).maximal Ω ⟨u a, hu⟩ = ∑ c, β a c • dxL2 0 c (constOne hΩ hb) :=
      fun a => (exists_maximal_eq_sum_dxL2_iff hΩ hb hker (β a) (u a)).2 ⟨α a, hα a⟩
    have hu : u ∈ ((vecRow n hΩ).d 0 (0 + 1)).domain :=
      (mem_vecRow_domain hΩ).2 fun a => (h a).1
    exact ⟨hu, PiLp.ext fun a => by rw [vecRow_d_apply hΩ]; exact (h a).2⟩

open scoped Matrix in
theorem cross_apply_eq_sub (b x : Fin 3 → ℝ) (c : Fin 3) :
    (b ⨯₃ x) c = b (c + 1) * x (c + 2) - b (c + 2) * x (c + 1) := by
  fin_cases c <;> simp [cross_apply]

open scoped Matrix in
theorem elasticity_lowest_iff {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hker : ((extDerivOp ℝ 3 0).maximal Ω).ker = ℝ ∙ constOne hΩ hb)
    (u : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 0))) :
    (∃ hu : u ∈ ((vecRow 3 hΩ).d 0 (0 + 1)).domain,
      ∃ v ∈ ((vecRow 3 hΩ).d 0 (0 + 1)).ker, crossL2 0 v = (vecRow 3 hΩ).d 0 (0 + 1) ⟨u, hu⟩) ↔
      ∃ a b : Fin 3 → ℝ, ∀ c s, ⇑(u c s) =ᵐ[volume.restrict Ω] fun x => a c + (b ⨯₃ x) c := by
  set β : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ := fun b c =>
    b (c + 1) • Pi.single (c + 2) 1 - b (c + 2) • Pi.single (c + 1) 1
  have hβ : ∀ b c x, β b c ⬝ᵥ x = (b ⨯₃ x) c := fun b c x => by
    rw [cross_apply_eq_sub]
    simp [β, dotProduct, Pi.single_apply, Finset.sum_sub_distrib, sub_mul]
  have hS : ∀ b, crossL2 (Ω := Ω) 0 (WithLp.toLp 2 fun c => b c • constOne hΩ hb) =
      WithLp.toLp 2 fun c => ∑ i, β b c i • dxL2 0 i (constOne hΩ hb) := fun b =>
    PiLp.ext fun c => by
      simp only [β, crossL2_apply, map_smul, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      rw [← sum_single_smul_dxL2, ← sum_single_smul_dxL2]
  simp only [mem_vecRow_ker_zero_iff hΩ hb hker]
  constructor
  · rintro ⟨hu, _, ⟨b, rfl⟩, h⟩
    obtain ⟨α, hα⟩ := (exists_vecRow_d_eq_sum_dxL2_iff hΩ hb hker (β b) u).1
      ⟨hu, h.symm.trans (hS b)⟩
    exact ⟨α, b, fun c s => by simpa only [hβ] using hα c s⟩
  · rintro ⟨a, b, ha⟩
    obtain ⟨hu, h⟩ := (exists_vecRow_d_eq_sum_dxL2_iff hΩ hb hker (β b) u).2
      ⟨a, fun c s => by simpa only [hβ] using ha c s⟩
    exact ⟨hu, _, ⟨b, rfl⟩, (hS b).trans h.symm⟩

theorem divDiv_lowest_iff (hker : ((extDerivOp ℝ n 0).maximal Ω).ker = ℝ ∙ constOne hΩ hb)
    (u : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n 0))) :
    (∃ hu : u ∈ ((vecRow n hΩ).d 0 (0 + 1)).domain,
      ∃ f ∈ ((formRow n hΩ).d 0 (0 + 1)).ker,
        dxVecL2 0 f = (vecRow n hΩ).d 0 (0 + 1) ⟨u, hu⟩) ↔
      ∃ (a : Fin n → ℝ) (b : ℝ), ∀ c s, ⇑(u c s) =ᵐ[volume.restrict Ω]
        fun x => a c + b * x c := by
  set β : ℝ → Fin n → Fin n → ℝ := fun b c => b • Pi.single c 1
  have hβ : ∀ b c x, β b c ⬝ᵥ x = b * x c := fun b c x => by
    simp [β, dotProduct, Pi.single_apply]
  have hS : ∀ b, dxVecL2 (Ω := Ω) 0 (b • constOne hΩ hb) =
      WithLp.toLp 2 fun c => ∑ i, β b c i • dxL2 0 i (constOne hΩ hb) := fun b =>
    PiLp.ext fun c => by
      rw [dxVecL2_apply, PiLp.toLp_apply, sum_single_smul_dxL2, map_smul]
  simp only [mem_formRow_ker_zero_iff hΩ hb hker]
  constructor
  · rintro ⟨hu, _, ⟨b, rfl⟩, h⟩
    obtain ⟨α, hα⟩ := (exists_vecRow_d_eq_sum_dxL2_iff hΩ hb hker (β b) u).1
      ⟨hu, h.symm.trans (hS b)⟩
    exact ⟨α, b, fun c s => by simpa only [hβ] using hα c s⟩
  · rintro ⟨a, b, ha⟩
    obtain ⟨hu, h⟩ := (exists_vecRow_d_eq_sum_dxL2_iff hΩ hb hker (β b) u).2
      ⟨a, fun c s => by simpa only [hβ] using ha c s⟩
    exact ⟨hu, _, ⟨b, rfl⟩, (hS b).trans h.symm⟩

include hb in
/-- On a bounded open `Ω` with `dim H⁰(HΛ(Ω)) = 1`, `[(σ, φ)] ↦ σ` is a linear isomorphism of `H⁰`
of the Hessian complex of forms onto the affine functions `a + b ⬝ᵥ x`. -/
theorem hessianFormData_homologyIs_zero
    (hH0 : Module.finrank ℝ ((formRow n hΩ).cohomology 0) = 1) :
    (hessianFormData hΩ).HomologyIs 0 0
      {u | ∃ (a : ℝ) (b : Fin n → ℝ), ∀ s, ⇑(u s) =ᵐ[volume.restrict Ω] fun x => a + b ⬝ᵥ x} := by
  have := LocalElement.subsingleton_L2F_of_neg Ω (n := n) (j := 0 - 1) (by norm_num)
  have := subsingleton_vec_formIdx (Ω := Ω) (n := n) (k := 0 - 1) (by norm_num)
  have h := (hessianFormData hΩ).homologyIs_lowest le_rfl
    (fun _ => ((hessianFormData_antilipschitz hΩ) 0 le_rfl).choose_spec.injective)
    (fun h => absurd h (by norm_num))
  convert h using 1
  ext u
  rw [Set.mem_ofPred_eq, ← hessian_lowest_iff hΩ hb (ker_maximal_zero_eq_span hΩ hb hH0),
    Set.mem_ofPred_eq]
  simp only [hessianFormData_S]
  rfl

open scoped Matrix in
/-- On a bounded open `Ω ⊆ ℝ³` with `dim H⁰(HΛ(Ω)) = 1`, `[(σ, φ)] ↦ σ` is a linear isomorphism
of `H⁰` of the elasticity complex of forms onto the rigid motions `a + b ⨯₃ x`. -/
theorem elasticityFormData_homologyIs_zero {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hH0 : Module.finrank ℝ ((formRow 3 hΩ).cohomology 0) = 1) :
    (elasticityFormData hΩ).HomologyIs 1 0
      {u | ∃ a b : Fin 3 → ℝ, ∀ c s, ⇑(u c s) =ᵐ[volume.restrict Ω] fun x => a c + (b ⨯₃ x) c} := by
  have := subsingleton_vec_formIdx (Ω := Ω) (n := 3) (k := 0 - 1) (by norm_num)
  have h := (elasticityFormData hΩ).homologyIs_lowest (i := 0) (J := 1)
    zero_le_one (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
  convert h using 1
  ext u
  rw [Set.mem_ofPred_eq, ← elasticity_lowest_iff hΩ hb (ker_maximal_zero_eq_span hΩ hb hH0),
    Set.mem_ofPred_eq]
  simp only [elasticityFormData_S]
  rfl

include hb in
/-- On a bounded open `Ω ⊆ ℝⁿ`, `n ≥ 1`, with `dim H⁰(HΛ(Ω)) = 1`, `[(σ, φ)] ↦ σ` is a linear
isomorphism of `H⁰` of the div–div complex of forms onto the fields `a + b x`. -/
theorem divDivFormData_homologyIs_zero [NeZero n]
    (hH0 : Module.finrank ℝ ((formRow n hΩ).cohomology 0) = 1) :
    (divDivFormData hΩ).HomologyIs ((n : ℤ) - 1) 0
      {u | ∃ (a : Fin n → ℝ) (b : ℝ), ∀ c s, ⇑(u c s) =ᵐ[volume.restrict Ω]
        fun x => a c + b * x c} := by
  have := LocalElement.subsingleton_L2F_of_neg Ω (n := n) (j := 0 - 1) (by norm_num)
  have := subsingleton_vec_formIdx (Ω := Ω) (n := n) (k := 0 - 1) (by norm_num)
  have hn := NeZero.pos n
  have hS := divDivFormData_antilipschitz hΩ
  have h := (divDivFormData hΩ).homologyIs_lowest (i := 0) (J := (n : ℤ) - 1) (by omega)
    (fun _ => (hS 0 (by omega)).choose_spec.injective)
    (fun _ => (hS (0 + 1) (by omega)).choose_spec.injective)
  convert h using 1
  ext u
  rw [Set.mem_ofPred_eq, ← divDiv_lowest_iff hΩ hb (ker_maximal_zero_eq_span hΩ hb hH0),
    Set.mem_ofPred_eq]
  simp only [divDivFormData_S]
  rfl

end Lowest

end Feec.FiniteElement
