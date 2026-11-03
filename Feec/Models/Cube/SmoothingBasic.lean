module

public import Feec.FiniteElement.InverseEstimate
public import Feec.FiniteElement.ShapeRegularSmoothing
public import Feec.Models.Cube.FiniteElementMethod

/-!
# Pointwise and local estimates of the smoother on simplicial meshes

The mesh-independent ingredients of the smoothed-projection estimates ([AFW2010], §5.5;
[ChristiansenWinther2008]) for the smoother `smoothForm` of
`Feec.Models.Cube.FiniteElementMethod`, on any conforming simplicial mesh: Jensen's inequality for
the mollifier and the pointwise bound of the smoothed form by the local mass
(`sq_integral_mul_normed_le`, `abs_smoothForm_le`); the Whitney DOFs as face integrals and their
agreement on shared faces (`simplexIntegral_globalInterp`, `simplexIntegral_eq_of_mem_globalSpace`,
`sum_mul_minor_eq`); the boundary layer `nearBdry` of the reference simplex and its measure
(`volume_real_nearBdry_le`, `mul_abs_integral_refSimplex_le`); glued fields almost everywhere
(`ae_glue_eq_local`, `sum_integral_sq_le_of_subset`, `ae_extField_glue_eq`); and the pointwise
estimate of a face integrand of `v - R v` as a mollified average
(`sum_sub_smoothForm_mul_eq`, `sqrt_mul_abs_sum_sub_smoothForm_le`). They are used by the
estimates on shape-regular meshes of star-shaped domains (`Feec.Models.StarShaped.Smoothing`) and
on the cube (`Feec.Models.Cube.SmoothingEstimates`, `Feec.Models.Cube.ParitySmoothingEstimates`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.5 (smoothed projections)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre

variable {n : ℕ}

/-! ### The smoother at a point -/

section Smoother

variable (φ : ContDiffBump (0 : Fin n → ℝ))

theorem isTest_normed_comp_sub (y : Fin n → ℝ) :
    IsTest (univ : Set (Fin n → ℝ)) fun t => φ.normed volume (y - t) :=
  IsTest.comp_sub ⟨φ.contDiff_normed, φ.hasCompactSupport_normed, subset_univ _⟩ y

theorem integral_normed_comp_sub (y : Fin n → ℝ) : ∫ t, φ.normed volume (y - t) = 1 := by
  rw [integral_sub_left_eq_self (fun t => φ.normed volume t) volume y, φ.integral_normed]

/-- **Jensen's inequality for the mollifier**: `(∫ f ρ(y - ·))² ≤ ∫ f² ρ(y - ·)`. -/
theorem sq_integral_mul_normed_le {f : (Fin n → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    (hf2 : LocallyIntegrable (fun t => f t ^ 2) volume) (y : Fin n → ℝ) :
    (∫ t, f t * φ.normed volume (y - t)) ^ 2 ≤ ∫ t, f t ^ 2 * φ.normed volume (y - t) := by
  set g : (Fin n → ℝ) → ℝ := fun t => φ.normed volume (y - t)
  have hg := isTest_normed_comp_sub φ y
  have h1 : Integrable fun t => f t * g t := integrable_mul_isTest hf hg
  have h2 : Integrable fun t => f t ^ 2 * g t := integrable_mul_isTest hf2 hg
  have h0 : Integrable g := hg.continuous.integrable_of_hasCompactSupport hg.hasCompactSupport
  set a := ∫ t, f t * g t
  have hpos : 0 ≤ ∫ t, (f t - a) ^ 2 * g t :=
    integral_nonneg fun t => mul_nonneg (sq_nonneg _) (φ.nonneg_normed _)
  have e : (fun t => (f t - a) ^ 2 * g t) =
      fun t => f t ^ 2 * g t - (2 * a) * (f t * g t) + a ^ 2 * g t := by
    funext t; ring
  have hA : Integrable fun t => f t ^ 2 * g t - (2 * a) * (f t * g t) :=
    h2.sub (h1.const_mul _)
  have hB : Integrable fun t => a ^ 2 * g t := h0.const_mul _
  have e2 : ∫ t, (f t ^ 2 * g t - (2 * a) * (f t * g t) + a ^ 2 * g t) =
      (∫ t, f t ^ 2 * g t) - (2 * a) * a + a ^ 2 * 1 := by
    rw [integral_add hA hB, integral_sub h2 (h1.const_mul _), integral_const_mul,
      integral_const_mul, integral_normed_comp_sub φ y]
  rw [e, e2] at hpos
  change a ^ 2 ≤ ∫ t, f t ^ 2 * g t
  nlinarith

/-- The mollified square is controlled by the mass on the ball of radius `rOut`:
`∫ f² ρ(y - ·) ≤ |B(0, rIn)|⁻¹ ∫_{B̄(y, rOut)} f²`. -/
theorem integral_sq_mul_normed_le {f : (Fin n → ℝ) → ℝ}
    (hf2 : Integrable (fun t => f t ^ 2) volume) (y : Fin n → ℝ) :
    ∫ t, f t ^ 2 * φ.normed volume (y - t) ≤
      1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) φ.rIn) *
        ∫ t in Metric.closedBall y φ.rOut, f t ^ 2 := by
  set Mρ := 1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) φ.rIn)
  have hg := isTest_normed_comp_sub φ y
  rw [← integral_const_mul, ← integral_indicator Metric.isClosed_closedBall.measurableSet]
  refine integral_mono (integrable_mul_isTest hf2.locallyIntegrable hg)
    ((hf2.const_mul Mρ).indicator Metric.isClosed_closedBall.measurableSet) fun t => ?_
  simp only
  by_cases ht : t ∈ Metric.closedBall y φ.rOut
  · rw [Set.indicator_of_mem ht, mul_comm Mρ]
    exact mul_le_mul_of_nonneg_left (φ.normed_le_div_measure_closedBall_rIn volume _)
      (sq_nonneg _)
  · rw [Set.indicator_of_notMem ht]
    have : φ.normed volume (y - t) = 0 := by
      rw [← Function.notMem_support, φ.support_normed_eq, Metric.mem_ball, dist_zero_right,
        ← dist_eq_norm, dist_comm]
      exact fun h => ht (Metric.mem_closedBall.2 h.le)
    rw [this, mul_zero]

theorem normed_eq_zero_of_le {y t : Fin n → ℝ} (h : φ.rOut ≤ dist t y) :
    φ.normed volume (y - t) = 0 := by
  rw [← Function.notMem_support, φ.support_normed_eq, Metric.mem_ball, dist_zero_right,
    ← dist_eq_norm, dist_comm]
  exact not_lt.2 h

end Smoother

/-! ### The smoothed form at a point -/

theorem smoothForm_apply_eq {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) (k : ℕ) (x : L2F ℝ Ω (formIdx n k)) (y : Fin n → ℝ)
    (s : formIdx n k) :
    (smoothForm p hΩ k x : FormField n) y s.1 = p.factor ^ k *
      ∫ t, Ω.indicator ((x s : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t *
        p.bump.normed volume (p.center + p.factor • (y - p.center) - t) := by
  rw [smoothForm_apply, formExt_val, smoothCoeff, smoothExt, dil, molli_apply, zpow_natCast]

/-- **Pointwise bound of the smoothed form**:
`|R x (y)ₛ|² ≤ c^{2k} |B(0, rIn)|⁻¹ Σ_{s'} ∫_{B̄(ŷ, rOut)} |x̄_{s'}|²`, `ŷ` the dilated point. -/
theorem abs_smoothForm_le {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) (k : ℕ) (x : L2F ℝ Ω (formIdx n k))
    (y : Fin n → ℝ) (s : Finset (Fin n)) :
    |(smoothForm p hΩ k x : FormField n) y s| ≤ p.factor ^ k *
      √(1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) p.bump.rIn) *
        ∑ s' : formIdx n k, ∫ t in Metric.closedBall (p.center + p.factor • (y - p.center))
          p.bump.rOut, (Ω.indicator ((x s' : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t) ^ 2) := by
  set Mρ := 1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) p.bump.rIn)
  have hMρ : 0 ≤ Mρ := by positivity
  set ŷ := p.center + p.factor • (y - p.center)
  have hterm : ∀ s' : formIdx n k, 0 ≤ ∫ t in Metric.closedBall ŷ p.bump.rOut,
      (Ω.indicator ((x s' : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t) ^ 2 := fun s' =>
    setIntegral_nonneg Metric.isClosed_closedBall.measurableSet fun t _ => sq_nonneg _
  by_cases hs : #s = k
  · have hs' : ((#s : ℕ) : ℤ) = (k : ℤ) := by rw [hs]
    have e := smoothForm_apply_eq hΩ p k x y ⟨s, hs'⟩
    simp only at e
    rw [e]
    set f := Ω.indicator ((x ⟨s, hs'⟩ : L2 ℝ Ω) : (Fin n → ℝ) → ℝ)
    have hmem : MemLp f 2 volume := memLp_indicator hΩ _
    have hf : LocallyIntegrable f volume := hmem.locallyIntegrable (by norm_num)
    have hf2 : Integrable (fun t => f t ^ 2) volume := hmem.integrable_sq
    rw [abs_mul, abs_of_pos (pow_pos p.factor_pos k)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg p.factor_pos.le k)
    rw [← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    refine (sq_integral_mul_normed_le p.bump hf hf2.locallyIntegrable ŷ).trans
      ((integral_sq_mul_normed_le p.bump hf2 ŷ).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ hMρ
    exact Finset.single_le_sum (f := fun s' : formIdx n k => ∫ t in Metric.closedBall ŷ p.bump.rOut,
      (Ω.indicator ((x s' : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t) ^ 2) (fun s' _ => hterm s')
      (Finset.mem_univ _)
  · rw [isDeg_smoothForm p hΩ k x y s hs, abs_zero]
    exact mul_nonneg (pow_nonneg p.factor_pos.le k) (Real.sqrt_nonneg _)


/-! ### Local estimates on the mesh simplices -/

theorem simplexIntegral_localDof {M : SimplicialMesh n} {k : ℕ} (T : M.simplices)
    {g : Finset (Fin n → ℝ)} (hg : g.card = k + 1) (z : (whitneyElement n).space T k) :
    (whitneyElement n).localDof T k g ⟨(), hg⟩ z =
      simplexIntegral (faceEnum g (k + 1)) (z : FormField n) := rfl

theorem simplexIntegral_globalInterp {M : SimplicialMesh n} (k : ℕ) (w : contForms n)
    (T : M.simplices) {g : Finset (Fin n → ℝ)}
    (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)) (hg : g.card = k + 1) :
    simplexIntegral (faceEnum g (k + 1))
        ((((whitneyElement n).globalInterp M k w : (whitneyElement n).Piecewise M k) T :
          (whitneyElement n).space T k) : FormField n) =
      simplexIntegral (faceEnum g (k + 1)) (w : FormField n) := by
  have h := (whitneyElement n).localDof_globalInterp M k w T g hgT
    (⟨(), hg⟩ : WhitneyDofIdx g k)
  exact (simplexIntegral_localDof T hg _).symm.trans (h.trans rfl)

theorem mem_p1MinusForms_of_space {T : Affine.Simplex ℝ (Fin n → ℝ) n} {k : ℕ}
    (z : (whitneyElement n).space T k) : (z : FormField n) ∈ p1MinusForms n k := by
  have := z.2
  change (z : FormField n) ∈ whitneySpace T.points k at this
  rwa [whitneySpace_eq_p1MinusForms_of_isUnit (isUnit_det_edgeMatrix _)] at this

theorem card_formIdx_le (k : ℤ) : (Fintype.card (formIdx n k) : ℝ) ≤ 2 ^ n := by
  have h := Fintype.card_subtype_le (fun s : Finset (Fin n) => (#s : ℤ) = k)
  rw [Fintype.card_finset, Fintype.card_fin] at h
  exact_mod_cast h

theorem volume_real_closedBall_zero {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.closedBall (0 : Fin n → ℝ) r) = (2 * r) ^ n := by
  rw [Measure.real, Real.volume_pi_closedBall _ hr, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]

/-- **The `L²` norm of a glued field by local integrals** (any element family and mesh):
`‖glue d‖² ≤ Σ_T f(T)` when `Σₛ ‖(d_T)ₛ‖²_{L²(T)} ≤ f(T)` for every simplex. -/
theorem norm_sq_glue_le (E : LocalElement n) (M : SimplicialMesh n) {k : ℕ} (d : E.Piecewise M k)
    (f : Affine.Simplex ℝ (Fin n → ℝ) n → ℝ)
    (hd : ∀ T (hT : T ∈ M.simplices), ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((d ⟨T, hT⟩ : E.space T k) : FormField n) y s.1) ^ 2 ≤ f T) :
    ‖E.glue M k d‖ ^ 2 ≤ ∑ T ∈ M.simplices, f T := by
  refine (norm_sq_pieceL2_le M M.domain (fun T => formComp (k := (k : ℤ)) (E.extendPW M d T))
    (fun T hT s => continuous_formComp (E.contDiff_extendPW M _ hT).continuous s)).trans
    (Finset.sum_le_sum fun T hT => ?_)
  have e : ∀ s : formIdx n k, ∀ y, formComp (k := (k : ℤ)) (E.extendPW M d T) s y =
      ((d ⟨T, hT⟩ : E.space T k) : FormField n) y s.1 := fun s y => by
    change E.extendPW M d T y s.1 = _
    rw [E.extendPW_of_mem M _ hT]
  simp_rw [e]
  exact hd T hT

theorem subsingleton_L2F_of_lt {Ω : Set (Fin n → ℝ)} {k : ℕ} (hk : n < k) :
    Subsingleton (L2F ℝ Ω (formIdx n k)) := by
  constructor
  intro x y
  refine PiLp.ext fun s => ?_
  exfalso
  have h1 := s.2
  have h2 : #s.1 ≤ n := by simpa using Finset.card_le_univ s.1
  omega

/-- A bound `‖y‖² ≤ K_k ‖x‖²` in the degrees `k ≤ n` gives `‖y‖ ≤ (Σ_{k ≤ n} K_k)^{1/2} ‖x‖` in
every degree (`L²(Ω; Λᵏ) = 0` for `k > n`). -/
theorem norm_le_sqrt_sum_of_sq_le {K : ℕ → ℝ} (hK : ∀ k, 0 ≤ K k) {Ω : Set (Fin n → ℝ)} {k : ℕ}
    {x y : L2F ℝ Ω (formIdx n k)} (h : k ≤ n → ‖y‖ ^ 2 ≤ K k * ‖x‖ ^ 2) :
    ‖y‖ ≤ √(∑ k ∈ Finset.range (n + 1), K k) * ‖x‖ := by
  by_cases hk : n < k
  · have := subsingleton_L2F_of_lt (Ω := Ω) hk
    rw [Subsingleton.elim y 0, norm_zero]
    positivity
  push Not at hk
  refine le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) ?_
  rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun k _ => hK k)]
  exact (h hk).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun k _ => hK k)
    (Finset.mem_range.2 (by omega))) (sq_nonneg _))

/-! ### Ingredients of the closeness estimate -/

/-- **The trace of a trimmed linear form on a `k`-face is constant**:
`Σₛ u(F x̂)ₛ minorₛ = k! ∫_q u`. -/
theorem sum_mul_minor_eq {k : ℕ} {u : FormField n} (hu : u ∈ p1MinusForms n k)
    (q : Fin (k + 1) → Fin n → ℝ) (x : Fin k → ℝ) :
    ∑ s, u (simplexMap q x) s * wedgeProd (simplexMatrix q) s univ =
      k.factorial * simplexIntegral q u := by
  rw [← affinePullback_univ_eq_of_mem_p1MinusForms hu q x, affinePullback_apply, pullback_apply]
  rfl

/-- **DOFs of global Whitney fields agree on shared faces.** -/
theorem simplexIntegral_eq_of_mem_globalSpace {M : SimplicialMesh n} {k : ℕ}
    {u : (whitneyElement n).Piecewise M k} (hu : u ∈ (whitneyElement n).globalSpace M k)
    (T T' : M.simplices) {g : Finset (Fin n → ℝ)}
    (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (hgT' : g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n)) (hg : g.card = k + 1) :
    simplexIntegral (faceEnum g (k + 1)) ((u T : (whitneyElement n).space T k) : FormField n) =
      simplexIntegral (faceEnum g (k + 1)) ((u T' : (whitneyElement n).space T' k) :
        FormField n) := by
  have := hu T T' g hgT hgT' (⟨(), hg⟩ : WhitneyDofIdx g k)
  rw [simplexIntegral_localDof T hg, simplexIntegral_localDof T' hg] at this
  exact this

theorem integral_closedInterior_eq_interior (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (f : (Fin n → ℝ) → ℝ) :
    ∫ x in T.closedInterior, f x = ∫ x in interior T.closedInterior, f x :=
  (setIntegral_congr_set (interior_ae_eq_of_null_frontier (μ := volume)
    (s := T.closedInterior) (Convex.addHaar_frontier volume (convex_closedInterior T)))).symm

/-! ### The set of points of a reference simplex near its boundary -/

/-- The points of `ℝᵏ` with a barycentric coordinate `< θ`. -/
def nearBdry (k : ℕ) (θ : ℝ) : Set (Fin k → ℝ) := {x | ∃ a, refBary x a < θ}

theorem isOpen_nearBdry (k : ℕ) (θ : ℝ) : IsOpen (nearBdry k θ) := by
  have : nearBdry k θ = ⋃ a, (fun x => refBary x a) ⁻¹' Set.Iio θ := by
    ext x; simp [nearBdry]
  rw [this]
  exact isOpen_iUnion fun a => isOpen_Iio.preimage (continuous_refBary_apply a)

/-- A coordinate slab of the reference simplex has volume at most its width. -/
theorem volume_slab_le {k : ℕ} (θ : ℝ) (j : Fin k) :
    volume (FiniteElement.refSimplex k ∩ {x | x j < θ}) ≤ ENNReal.ofReal θ := by
  classical
  have hsub : FiniteElement.refSimplex k ∩ {x | x j < θ} ⊆
      Set.Icc (0 : Fin k → ℝ) (Function.update 1 j θ) := by
    rintro x ⟨hx, hxj⟩
    have h := refSimplex_subset_pi k hx
    refine ⟨fun i => (h i (Set.mem_univ i)).1, fun i => ?_⟩
    by_cases hij : i = j
    · subst hij; simp only [Function.update_self]; exact le_of_lt hxj
    · simp only [Function.update_of_ne hij, Pi.one_apply]; exact (h i (Set.mem_univ i)).2
  refine (measure_mono hsub).trans ?_
  rw [Real.volume_Icc_pi]
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij; simp [Function.update_of_ne hij]
  · simp

theorem volume_nearBdry_apply_le {k : ℕ} {θ : ℝ} (hθ1 : θ ≤ 1) (a : Fin (k + 1)) :
    volume (FiniteElement.refSimplex k ∩ {x | refBary x a < θ}) ≤ ENNReal.ofReal θ := by
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨j, rfl⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : FiniteElement.refSimplex 0 ∩ {x | refBary x 0 < θ} = ∅ := by
        ext x; simp only [refBary_zero, Finset.univ_eq_empty, Finset.sum_empty, sub_zero,
          Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
          not_lt]
        exact fun _ => hθ1
      rw [this, measure_empty]; exact bot_le
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      set π : Equiv.Perm (Fin (k' + 2)) := Equiv.swap 0 1
      have hpre : permMap π ⁻¹' (FiniteElement.refSimplex (k' + 1) ∩ {x | x 0 < θ}) =
          FiniteElement.refSimplex (k' + 1) ∩ {x | refBary x 0 < θ} := by
        rw [Set.preimage_inter, permMap_preimage_refSimplex]
        congr 1
        ext x
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        have := congrFun (refBary_permMap π x) 1
        have h1 : refBary (permMap π x) 1 = permMap π x 0 := by
          rw [← Fin.succ_zero_eq_one, refBary_succ]
        rw [← h1, this]
        simp [π, Equiv.swap_apply_right]
      rw [← hpre, (measurePreserving_permMap π).measure_preimage
        (((isClosed_refSimplex _).measurableSet.inter
          (measurableSet_lt (measurable_pi_apply 0) measurable_const))).nullMeasurableSet]
      exact volume_slab_le θ 0
  · simpa using volume_slab_le θ j

/-- **The boundary layer of the reference simplex is small**:
`|{x̂ ∈ T̂_k : some λ̂ₐ(x̂) < θ}| ≤ (k + 1) θ`. -/
theorem volume_real_nearBdry_le {k : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    volume.real (FiniteElement.refSimplex k ∩ nearBdry k θ) ≤ (k + 1) * θ := by
  have e : FiniteElement.refSimplex k ∩ nearBdry k θ =
      ⋃ a, FiniteElement.refSimplex k ∩ {x | refBary x a < θ} := by
    ext x; simp [nearBdry]
  have h : volume (FiniteElement.refSimplex k ∩ nearBdry k θ) ≤ ENNReal.ofReal ((k + 1) * θ) := by
    rw [e]
    refine (measure_iUnion_le _).trans ?_
    calc ∑' a, volume (FiniteElement.refSimplex k ∩ {x | refBary x a < θ})
        = ∑ a, volume (FiniteElement.refSimplex k ∩ {x | refBary x a < θ}) := tsum_fintype _
      _ ≤ ∑ _a : Fin (k + 1), ENNReal.ofReal θ :=
          Finset.sum_le_sum fun a _ => volume_nearBdry_apply_le hθ1 a
      _ = ENNReal.ofReal ((k + 1) * θ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_nsmul,
            nsmul_eq_mul]
          push_cast; rfl
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

theorem volume_real_refSimplex_le_one (m : ℕ) :
    volume.real (FiniteElement.refSimplex m) ≤ 1 := by
  rw [volume_real_refSimplex, div_le_one (by positivity)]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m)

open Classical in
/-- **Integration of a face-integrand bound**: if `H |F(ξ)| ≤ c` near `∂Δ` (barycentric weight
`< θ`) and `≤ c ε` elsewhere, then `H |∫_Δ F| ≤ c (ε + (m + 1) θ)`. -/
theorem mul_abs_integral_refSimplex_le {m : ℕ} {F : (Fin m → ℝ) → ℝ} (hF : Continuous F)
    {H c ε θ : ℝ} (hH : 0 ≤ H) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hpt : ∀ ξ ∈ FiniteElement.refSimplex m,
      H * |F ξ| ≤ c * (if ξ ∈ nearBdry m θ then 1 else ε)) :
    H * |∫ ξ in FiniteElement.refSimplex m, F ξ| ≤ c * (ε + (m + 1) * θ) := by
  have hS : MeasurableSet (FiniteElement.refSimplex m) := measurableSet_refSimplex m
  have hfin : volume (FiniteElement.refSimplex m) ≠ ⊤ := (volume_refSimplex_lt_top m).ne
  have hB := (isOpen_nearBdry m θ).measurableSet
  set β : (Fin m → ℝ) → ℝ := fun ξ => c * ε + c * (nearBdry m θ).indicator 1 ξ
  have hpt' : ∀ ξ ∈ FiniteElement.refSimplex m, H * |F ξ| ≤ β ξ := fun ξ hξ => by
    refine (hpt ξ hξ).trans ?_
    by_cases hb : ξ ∈ nearBdry m θ
    · simp only [hb, ite_true, β, Set.indicator_of_mem hb, Pi.one_apply]
      nlinarith [mul_nonneg hc hε]
    · simp [hb, β]
  have hind : IntegrableOn (fun ξ => (nearBdry m θ).indicator (1 : (Fin m → ℝ) → ℝ) ξ)
      (FiniteElement.refSimplex m) := (integrableOn_const hfin).indicator hB
  have hint : ∫ ξ in FiniteElement.refSimplex m, β ξ =
      c * ε * volume.real (FiniteElement.refSimplex m) +
        c * volume.real (FiniteElement.refSimplex m ∩ nearBdry m θ) := by
    rw [integral_add (integrableOn_const hfin) (hind.const_mul _), setIntegral_const, smul_eq_mul,
      integral_const_mul, integral_indicator_one hB, Measure.real, Measure.real,
      Measure.restrict_apply hB, Set.inter_comm]
    simp only [Measure.real]
    ring
  have hvol := volume_real_refSimplex_le_one m
  have hbad := volume_real_nearBdry_le (k := m) hθ0 hθ1
  calc H * |∫ ξ in FiniteElement.refSimplex m, F ξ|
      ≤ H * ∫ ξ in FiniteElement.refSimplex m, |F ξ| :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hH
    _ = ∫ ξ in FiniteElement.refSimplex m, H * |F ξ| := (integral_const_mul _ _).symm
    _ ≤ ∫ ξ in FiniteElement.refSimplex m, β ξ :=
        setIntegral_mono_on ((hF.abs.continuousOn.integrableOn_compact
          (isCompact_refSimplex m)).const_mul _)
          ((integrableOn_const hfin).add (hind.const_mul _)) hS hpt'
    _ ≤ c * (ε + (m + 1) * θ) := by
        rw [hint]
        have h1 := mul_le_mul_of_nonneg_left hvol (mul_nonneg hc hε)
        have h2 := mul_le_mul_of_nonneg_left hbad hc
        nlinarith


/-! ### Glued fields almost everywhere -/

/-- **A glued field almost everywhere** (any element family): a.e. point of `Ω` lies in the
interior of a simplex `T'`, where the field is the local field of `T'`. -/
theorem ae_glue_eq_local (E : LocalElement n) {M : SimplicialMesh n} {k : ℕ} (u : E.Piecewise M k)
    (hΩ : MeasurableSet M.domain) :
    ∀ᵐ t ∂volume, t ∈ M.domain → ∃ T' : M.simplices,
      t ∈ interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ∧
        ∀ s : formIdx n k, M.domain.indicator
          ((E.glue M k u s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) t =
          ((u T' : E.space T' k) : FormField n) t s.1 := by
  have h1 : ∀ᵐ t ∂volume.restrict M.domain, ∀ s : formIdx n k,
      ((E.glue M k u s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) t =
        pieceFun M (fun T => formComp (k := (k : ℤ)) (E.extendPW M u T) s) t := by
    rw [ae_all_iff]
    intro s
    exact coeFn_pieceL2 M M.domain _ (fun T hT s => continuous_formComp
      (E.contDiff_extendPW M u hT).continuous s) s
  have h2 := ae_mem_interior M hΩ
  rw [← ae_restrict_iff' hΩ]
  filter_upwards [h1, h2, ae_restrict_mem hΩ] with t ht1 ht2 htΩ
  obtain ⟨T', hT', htT'⟩ := ht2
  refine ⟨⟨T', hT'⟩, htT', fun s => ?_⟩
  rw [Set.indicator_of_mem htΩ, ht1 s, pieceFun_of_mem_interior M _ hT' htT']
  change E.extendPW M u T' t s.1 = _
  rw [E.extendPW_of_mem M u hT']

/-- **The local fields are controlled by the glued field** on any set containing their simplex
(any element family and mesh with `interior T ⊆ Ω` for every simplex `T`). -/
theorem sum_integral_sq_le_of_subset (E : LocalElement n) {M : SimplicialMesh n}
    (hΩ : MeasurableSet M.domain) (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain)
    {k : ℕ} (u : E.Piecewise M k) (T' : M.simplices) {K : Set (Fin n → ℝ)}
    (hsub : (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆ K) :
    ∑ s, ∫ y in (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (((u T' : E.space T' k) : FormField n) y s) ^ 2 ≤
      ∑ s : formIdx n k, ∫ t in K,
        (M.domain.indicator ((E.glue M k u s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) t) ^ 2 := by
  set z : FormField n := ((u T' : E.space T' k) : FormField n)
  have hdeg : ∀ y, IsDeg k (z y) := E.isDeg_of_mem (u T').2
  rw [sum_eq_sum_formIdx (fun s hs => by
    have : ∀ y, (z y s) ^ 2 = 0 := fun y => by rw [hdeg y s hs]; ring
    simp_rw [this]; simp)]
  refine Finset.sum_le_sum fun s _ => ?_
  have hae := ae_glue_eq_local E u hΩ
  rw [integral_closedInterior_eq_interior]
  have heq : ∫ y in interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, (z y s.1) ^ 2 =
      ∫ y in interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        (M.domain.indicator ((E.glue M k u s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) y) ^ 2 := by
    refine setIntegral_congr_ae isOpen_interior.measurableSet ?_
    filter_upwards [hae] with y hy hyT
    obtain ⟨T'', hyT'', hval⟩ := hy (hint T' T'.2 hyT)
    have : T'' = T' := by
      by_contra hne
      exact Set.disjoint_left.1 (M.pairwise_disjoint_interior T''.2 T'.2
        (fun e => hne (Subtype.ext e))) hyT'' hyT
    subst this
    rw [hval s]
  rw [heq]
  exact setIntegral_mono_set ((memLp_indicator hΩ _).integrable_sq).integrableOn
    (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall fun y hy => hsub (interior_subset hy))

/-! ### Mollified differences -/

/-- `|∫ g G| ≤ β` for a probability density `g` and `|G| ≤ β` a.e. on `{g ≠ 0}`. -/
theorem abs_integral_mul_le_of_ae {g G : (Fin n → ℝ) → ℝ} (hg0 : ∀ t, 0 ≤ g t)
    (hgi : Integrable g) (hg1 : ∫ t, g t = 1) (hG : Integrable fun t => g t * G t) {β : ℝ}
    (hb : ∀ᵐ t ∂volume, g t ≠ 0 → |G t| ≤ β) : |∫ t, g t * G t| ≤ β := by
  calc |∫ t, g t * G t| ≤ ∫ t, |g t * G t| := abs_integral_le_integral_abs
    _ ≤ ∫ t, g t * β := by
        refine integral_mono_ae hG.abs (hgi.mul_const β) ?_
        filter_upwards [hb] with t ht
        rw [abs_mul, abs_of_nonneg (hg0 t)]
        by_cases h0 : g t = 0
        · rw [h0]; simp
        · exact mul_le_mul_of_nonneg_left (ht h0) (hg0 t)
    _ = β := by rw [integral_mul_const, hg1, one_mul]


/-- The zero extension of an `L²` `k`-form field, as a fibre form at each point. -/
def extField {Ω : Set (Fin n → ℝ)} {k : ℕ} (v : L2F ℝ Ω (formIdx n k)) (t : Fin n → ℝ) :
    Finset (Fin n) → ℝ :=
  formExt (fun s : formIdx n k => Ω.indicator ((v s : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t)

theorem smoothForm_apply_eq_integral {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) (k : ℕ) (v : L2F ℝ Ω (formIdx n k)) (x : Fin n → ℝ)
    (s : Finset (Fin n)) :
    (smoothForm p hΩ k v : FormField n) x s = p.factor ^ k *
      ∫ t, extField v t s * p.bump.normed volume (p.center + p.factor • (x - p.center) - t) := by
  by_cases hs : (#s : ℤ) = (k : ℤ)
  · have e := smoothForm_apply_eq hΩ p k v x ⟨s, hs⟩
    simp only at e
    rw [e]
    congr 2
    funext t
    rw [extField, formExt_of_card _ hs]
  · rw [isDeg_smoothForm p hΩ k v x s (fun h => hs (by rw [h]))]
    have : ∀ t, extField v t s = 0 := fun t => by simp [extField, formExt, hs]
    simp [this]

theorem integrable_extField_mul {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) {k : ℕ}
    (v : L2F ℝ Ω (formIdx n k)) (φ : ContDiffBump (0 : Fin n → ℝ)) (y : Fin n → ℝ)
    (s : Finset (Fin n)) :
    Integrable fun t => extField v t s * φ.normed volume (y - t) := by
  by_cases hs : (#s : ℤ) = (k : ℤ)
  · have e : ∀ t, extField v t s = Ω.indicator ((v ⟨s, hs⟩ : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t :=
      fun t => by rw [extField, formExt_of_card _ hs]
    simp_rw [e]
    exact integrable_mul_isTest ((memLp_indicator hΩ _).locallyIntegrable (by norm_num))
      (isTest_normed_comp_sub φ y)
  · have : ∀ t, extField v t s = 0 := fun t => by simp [extField, formExt, hs]
    simp [this]

/-- **The face integrand of `u - R v` as a mollified average**: for any fibre form `a` and
coefficients `m`, `Σₛ (aₛ - (R v)(x)ₛ) mₛ = ∫ ρ(x̂ - t) Σₛ (aₛ - cᵏ v̄(t)ₛ) mₛ dt`, `x̂` the dilated
point. -/
theorem sum_sub_smoothForm_mul_eq {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) (k : ℕ) (v : L2F ℝ Ω (formIdx n k))
    (a m : Finset (Fin n) → ℝ) (x : Fin n → ℝ) :
    ∑ s, (a s - (smoothForm p hΩ k v : FormField n) x s) * m s =
      ∫ t, p.bump.normed volume (p.center + p.factor • (x - p.center) - t) *
        ∑ s, (a s - p.factor ^ k * extField v t s) * m s := by
  set ŷ := p.center + p.factor • (x - p.center)
  set g : (Fin n → ℝ) → ℝ := fun t => p.bump.normed volume (ŷ - t)
  have hg : Integrable g :=
    (isTest_normed_comp_sub p.bump ŷ).continuous.integrable_of_hasCompactSupport
    (isTest_normed_comp_sub p.bump ŷ).hasCompactSupport
  have hg1 : ∫ t, g t = 1 := integral_normed_comp_sub p.bump ŷ
  have e : ∀ t, g t * ∑ s, (a s - p.factor ^ k * extField v t s) * m s =
      ∑ s, ((a s * m s) * g t - (p.factor ^ k * m s) * (extField v t s * g t)) := fun t => by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
  have hint : ∀ s ∈ (Finset.univ : Finset (Finset (Fin n))), Integrable fun t =>
      (a s * m s) * g t - (p.factor ^ k * m s) * (extField v t s * g t) := fun s _ =>
    (hg.const_mul _).sub ((integrable_extField_mul hΩ v p.bump ŷ s).const_mul _)
  rw [integral_congr_ae (Eventually.of_forall e), integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_sub (hg.const_mul _) ((integrable_extField_mul hΩ v p.bump ŷ s).const_mul _),
    integral_const_mul, integral_const_mul, hg1, smoothForm_apply_eq_integral hΩ p k v x s]
  ring


/-- **The zero extension of a glued field almost everywhere** (any element family): a.e. point
of `Ω` lies in the interior of a simplex `T'` whose local field is the zero extension there. -/
theorem ae_extField_glue_eq (E : LocalElement n) {M : SimplicialMesh n} {k : ℕ}
    (u : E.Piecewise M k) (hΩ : MeasurableSet M.domain) :
    ∀ᵐ t ∂volume, t ∈ M.domain → ∃ T' : M.simplices,
      t ∈ interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ∧
        ∀ s, extField (E.glue M k u) t s = ((u T' : E.space T' k) : FormField n) t s := by
  filter_upwards [ae_glue_eq_local E u hΩ] with t ht htΩ
  obtain ⟨T', htT', hval⟩ := ht htΩ
  refine ⟨T', htT', fun s => ?_⟩
  by_cases hs' : (#s : ℤ) = (k : ℤ)
  · rw [extField, formExt_of_card _ hs']; exact hval ⟨s, hs'⟩
  · have : extField (E.glue M k u) t s = 0 := by simp [extField, formExt, hs']
    rw [this, E.isDeg_of_mem (u T').2 t s (fun h' => hs' (by rw [h']))]

/-- `H |Σₛ fₛ cₛ| ≤ K Σₛ |cₛ|` when `H |fₛ| ≤ K` for every `s`. -/
theorem mul_abs_sum_mul_le {H K : ℝ} (hH : 0 ≤ H) {f c : Finset (Fin n) → ℝ}
    (hf : ∀ s, H * |f s| ≤ K) : H * |∑ s, f s * c s| ≤ K * ∑ s, |c s| := by
  calc H * |∑ s, f s * c s| ≤ H * ∑ s, |f s| * |c s| :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (le_of_eq (Finset.sum_congr rfl fun s _ => abs_mul _ _))) hH
    _ = ∑ s, (H * |f s|) * |c s| := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ∑ s, K * |c s| :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hf s) (abs_nonneg _)
    _ = K * ∑ s, |c s| := by rw [Finset.mul_sum]

open Classical in
/-- **The pointwise estimate of a face integrand of `v - R v`**, for any element family and mesh:
at a point `x` with dilated point `x̂`, if the local field `a` at `x` and, a.e. near `x̂` inside
`Ω`, a local field `w` representing `v` obey the inverse estimates `H |·| ≤ A √L`, then
`H |Σₛ (aₛ - (R v)(x)ₛ) cₛ| ≤ (Σₛ |cₛ|) A √L 2^{k+1} · (1 or (k + 1) ε)`. The factor `(k + 1) ε`
holds when (`¬ b`) the traces agree (`Σₛ aₛ cₛ = Σₛ w(x)ₛ cₛ`), the displacement costs
`H |w(x)ₛ - w(t)ₛ| ≤ ε A √L`, the dilation defect is `|1 - cᵏ| ≤ k 2ᵏ ε`, and samples outside
`Ω` force `Σₛ aₛ cₛ = 0`. -/
theorem sqrt_mul_abs_sum_sub_smoothForm_le {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) {k : ℕ} (v : L2F ℝ Ω (formIdx n k)) (x : Fin n → ℝ)
    (a c : Finset (Fin n) → ℝ) {H A L ε : ℝ} (b : Prop) (hH : 0 < H) (hA0 : 0 ≤ A)
    (hε : 0 ≤ ε) (hκ : p.factor ^ k ≤ 2 ^ k)
    (hdef : |1 - p.factor ^ k| ≤ k * 2 ^ k * ε) (ha : ∀ s, H * |a s| ≤ A * √L)
    (hloc : ∀ᵐ t ∂volume, dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut →
      t ∈ Ω → ∃ w : FormField n, (∀ s, extField v t s = w t s) ∧ (∀ s, H * |w t s| ≤ A * √L) ∧
        (¬ b → ∑ s, a s * c s = ∑ s, w x s * c s ∧ (∀ s, H * |w x s| ≤ A * √L) ∧
          ∀ s, H * |w x s - w t s| ≤ ε * (A * √L)))
    (hout : ¬ b → ∀ t, dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut → t ∉ Ω →
      ∑ s, a s * c s = 0) :
    H * |∑ s, (a s - (smoothForm p hΩ k v : FormField n) x s) * c s| ≤
      (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * (if b then 1 else (k + 1) * ε) := by
  set ŷ := p.center + p.factor • (x - p.center)
  set κ := p.factor ^ k
  set R := (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * (if b then 1 else (k + 1) * ε)
  have hκ0 : 0 ≤ κ := pow_nonneg p.factor_pos.le k
  have hAL : 0 ≤ A * √L := mul_nonneg hA0 (Real.sqrt_nonneg _)
  have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
  -- the four cases of the pointwise bound, as `H |fₛ| ≤ K` with `K Σₛ |cₛ| ≤ R`
  have hnear : b → ∀ f : Finset (Fin n) → ℝ, (∀ s, H * |f s| ≤ 2 ^ (k + 1) * (A * √L)) →
      H * |∑ s, f s * c s| ≤ R := fun hb f hf =>
    (mul_abs_sum_mul_le hH.le hf).trans (le_of_eq (by simp only [R, hb, ite_true]; ring))
  have hfar : ¬ b → ∀ f : Finset (Fin n) → ℝ,
      (∀ s, H * |f s| ≤ (k + 1) * 2 ^ k * ε * (A * √L)) → H * |∑ s, f s * c s| ≤ R :=
    fun hb f hf => (mul_abs_sum_mul_le hH.le hf).trans (by
      simp only [R, hb, ite_false, pow_succ]
      have : 0 ≤ (k + 1) * 2 ^ k * ε * (A * √L) * ∑ s, |c s| := by positivity
      nlinarith)
  have hmono : A * √L ≤ 2 ^ (k + 1) * (A * √L) :=
    le_mul_of_one_le_left hAL (one_le_pow₀ (by norm_num))
  rw [sum_sub_smoothForm_mul_eq hΩ p k v a c x]
  set G : (Fin n → ℝ) → ℝ := fun t => ∑ s, (a s - κ * extField v t s) * c s
  set ρ : (Fin n → ℝ) → ℝ := fun t => p.bump.normed volume (ŷ - t)
  have hρi : Integrable ρ :=
    (isTest_normed_comp_sub p.bump ŷ).continuous.integrable_of_hasCompactSupport
      (isTest_normed_comp_sub p.bump ŷ).hasCompactSupport
  have hρG : Integrable fun t => ρ t * G t := by
    have e : (fun t => ρ t * G t) = fun t => ∑ s, ((a s * c s) * ρ t -
        (κ * c s) * (extField v t s * ρ t)) := by
      funext t; simp only [G, Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
    rw [e]
    exact integrable_finsetSum _ fun s _ =>
      (hρi.const_mul _).sub ((integrable_extField_mul hΩ v p.bump ŷ s).const_mul _)
  have hb : ∀ᵐ t ∂volume, ρ t ≠ 0 → |G t| ≤ R / H := by
    filter_upwards [hloc] with t ht hρt
    have hdist : dist t ŷ < p.bump.rOut := by
      by_contra hcon; push Not at hcon
      exact hρt (normed_eq_zero_of_le p.bump hcon)
    rw [le_div_iff₀ hH, mul_comm]
    by_cases htΩ : t ∈ Ω
    · obtain ⟨w, hext, hwt, hfar'⟩ := ht hdist htΩ
      have hGt : G t = ∑ s, (a s - κ * w t s) * c s := by simp only [G, hext]
      rw [hGt]
      by_cases hbad : b
      · refine hnear hbad _ fun s => ?_
        calc H * |a s - κ * w t s| ≤ H * (|a s| + κ * |w t s|) :=
              mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
                (by rw [abs_mul, abs_of_nonneg hκ0])) hH.le
          _ = H * |a s| + κ * (H * |w t s|) := by ring
          _ ≤ A * √L + 2 ^ k * (A * √L) :=
              add_le_add (ha s) (mul_le_mul hκ (hwt s) (by positivity) h2k)
          _ ≤ 2 ^ (k + 1) * (A * √L) := by
              rw [pow_succ]
              nlinarith [mul_le_mul_of_nonneg_right
                (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)) hAL]
      · obtain ⟨htr, hwx, hlip⟩ := hfar' hbad
        have e : ∑ s, (a s - κ * w t s) * c s =
            ∑ s, ((1 - κ) * w x s + κ * (w x s - w t s)) * c s := by
          have e1 : ∑ s, (a s - κ * w t s) * c s =
              ∑ s, a s * c s - ∑ s, κ * w t s * c s := by
            rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
          have e2 : ∑ s, ((1 - κ) * w x s + κ * (w x s - w t s)) * c s =
              ∑ s, w x s * c s - ∑ s, κ * w t s * c s := by
            rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
          rw [e1, e2, htr]
        rw [e]
        refine hfar hbad _ fun s => ?_
        calc H * |(1 - κ) * w x s + κ * (w x s - w t s)|
            ≤ |1 - κ| * (H * |w x s|) + κ * (H * |w x s - w t s|) := by
              refine (mul_le_mul_of_nonneg_left (abs_add_le _ _) hH.le).trans (le_of_eq ?_)
              rw [abs_mul, abs_mul, abs_of_nonneg hκ0]; ring
          _ ≤ (k * 2 ^ k * ε) * (A * √L) + 2 ^ k * (ε * (A * √L)) :=
              add_le_add (mul_le_mul hdef (hwx s) (by positivity) (by positivity))
                (mul_le_mul hκ (hlip s) (by positivity) h2k)
          _ = (k + 1) * 2 ^ k * ε * (A * √L) := by ring
    · have hext : ∀ s, extField v t s = 0 := fun s => by
        simp [extField, formExt, Set.indicator_of_notMem htΩ]
      have hGt : G t = ∑ s, a s * c s := by simp only [G, hext]; simp
      rw [hGt]
      by_cases hbad : b
      · exact hnear hbad a fun s => (ha s).trans hmono
      · rw [hout hbad t hdist htΩ, abs_zero, mul_zero]
        simp only [R, hbad, ite_false]
        positivity
  have hmain := abs_integral_mul_le_of_ae (fun t => p.bump.nonneg_normed _) hρi
    (integral_normed_comp_sub p.bump ŷ) hρG hb
  rw [le_div_iff₀ hH, mul_comm] at hmain
  exact hmain

theorem self_subset_cthickening (T : Affine.Simplex ℝ (Fin n → ℝ) n) {r : ℝ} (hr : 0 ≤ r) :
    T.closedInterior ⊆ Metric.cthickening r T.closedInterior :=
  Metric.self_subset_cthickening _ |>.trans (Metric.cthickening_mono hr _)

/-- **Choice of the smoothing scale** `γ`: small against the constants of the local
estimates. -/
theorem sq_le_quarter {S K x : ℝ} (hS : 0 ≤ S) (hK : 1 ≤ K) (hx0 : 0 ≤ x) (hx : x ≤ S) :
    K * (x * (1 / (2 * (1 + S * K)))) ^ 2 ≤ 1 / 4 := by
  have hpos : 0 < 1 + S * K := by nlinarith
  rw [mul_pow, div_pow, one_pow, mul_pow]
  rw [show K * (x ^ 2 * (1 / (2 ^ 2 * (1 + S * K) ^ 2))) = K * x ^ 2 / (4 * (1 + S * K) ^ 2) by
    field_simp; ring]
  rw [div_le_iff₀ (by positivity)]
  have h1 : K * x ^ 2 ≤ K * S ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx 2)
    (by linarith)
  have h2 : K * S ^ 2 ≤ (S * K) ^ 2 := by nlinarith
  nlinarith

theorem norm_eq_zero_negSucc {Ω : Set (Fin n → ℝ)} (k : ℕ)
    (y : L2F ℝ Ω (formIdx n (Int.negSucc k))) : ‖y‖ = 0 := by
  have := LocalElement.subsingleton_L2F_negSucc Ω (n := n) k
  rw [Subsingleton.elim y 0, norm_zero]

end Feec.Models.Cube.FEM
