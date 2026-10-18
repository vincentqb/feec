module

public import Feec.FiniteElement.SimplexIntegral

/-!
# The divergence theorem and Stokes' theorem on simplices

On the reference simplex `T̂_{m+1} ⊆ ℝ^{m+1}` the boundary consists of the slanted face
`{Σ x̂ = 1}` (opposite the vertex `v̂₀ = 0`), parametrized by the barycentric map
`λ̂ : T̂_m → ℝ^{m+1}`, and of the coordinate faces `{x̂ⱼ = 0}` (opposite `v̂ⱼ₊₁ = eⱼ`),
parametrized by `ŷ ↦ (ŷ with 0 inserted at j)`. Integrating `∂ⱼ` first along the coordinate `j`
(Fubini on the slices, `Feec.FiniteElement.setIntegral_refSimplex_succ`) and then using the
fundamental theorem of calculus gives the slanted and the `j`-th coordinate face; a vertex
permutation of `T̂_m` (`Feec.FiniteElement.setIntegral_refSimplex_comp_permMap`) brings the
slanted face to the barycentric parametrization. This is the technique of Mathlib's divergence
theorem on boxes (`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`), adapted to
the simplex.

The pullback then transports the result to every affine simplex: for a `C¹` form `ω` on a
neighbourhood of an oriented affine `(k+1)`-simplex `p` in `ℝⁿ`,

  `∫_p dω = Σ_{i=0}^{k+1} (-1)^i ∫_{∂_i p} ω`,   `∂_i p = (p₀, …, p̂ᵢ, …, p_{k+1})`.

## Main results

* `setIntegral_refSimplex_partialDeriv`: `∫_{T̂} ∂ⱼ h = ∫_{T̂_m} h ∘ λ̂ - ∫_{T̂_m} h(· with 0 at j)`;
* `setIntegral_refSimplex_divergence`: **the divergence theorem on the reference simplex**;
* `setIntegral_refSimplex_extDeriv`: Stokes' theorem on the reference simplex;
* `simplexIntegral_extDeriv`: **Stokes' theorem on an affine simplex**, and
  `simplexIntegral_extDeriv_faceOpposite` for Mathlib's `Affine.Simplex`;
* `setIntegral_image_simplexMap_divergence`: the divergence theorem on an affine `n`-simplex
  of `ℝⁿ`, `± ∫_T div F = Σᵢ (-1)ⁱ ∫_{∂ᵢ T} ι_F vol`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (Stokes' theorem)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6
-/

open Finset MeasureTheory

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre

variable {n m k : ℕ}

/-! ### The faces of the reference simplex -/

theorem continuous_refBary : Continuous (refBary : (Fin m → ℝ) → Fin (m + 1) → ℝ) :=
  continuous_pi continuous_refBary_apply

theorem refBary_mem_refSimplex {y : Fin m → ℝ} (hy : y ∈ refSimplex m) :
    refBary y ∈ refSimplex (m + 1) := by
  rw [mem_refSimplex_iff, sum_refBary]
  exact ⟨hy, le_rfl⟩

theorem insertNth_zero_mem_refSimplex (j : Fin (m + 1)) {y : Fin m → ℝ}
    (hy : y ∈ refSimplex m) : Fin.insertNth j 0 y ∈ refSimplex (m + 1) := by
  refine (insertNth_mem_refSimplex_iff j 0 y).2 ⟨hy, le_rfl, ?_⟩
  linarith [(mem_refSimplex_iff.1 hy).2]

theorem continuous_insertNth_const (j : Fin (m + 1)) (c : ℝ) :
    Continuous fun y : Fin m → ℝ => Fin.insertNth (α := fun _ => ℝ) j c y :=
  continuous_const.finInsertNth j continuous_id

/-- The slanted face read along the coordinate `j` is the barycentric map up to a cyclic
permutation of the coordinates. -/
theorem insertNth_one_sub_sum (j : Fin (m + 1)) (y : Fin m → ℝ) :
    Fin.insertNth j (1 - ∑ i, y i) y = refBary y ∘ Fin.cycleRange j := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨l, rfl⟩
  · simp [Fin.cycleRange_self]
  · simp [Fin.cycleRange_succAbove]

/-- The slanted face: `∫_{T̂_m} G(ŷ with 1 - Σŷ inserted at j) dŷ = ∫_{T̂_m} G(λ̂(ŷ)) dŷ`. -/
theorem setIntegral_refSimplex_insertNth_one_sub_sum (j : Fin (m + 1))
    (G : (Fin (m + 1) → ℝ) → ℝ) :
    ∫ y in refSimplex m, G (Fin.insertNth j (1 - ∑ i, y i) y) =
      ∫ y in refSimplex m, G (refBary y) := by
  simp_rw [insertNth_one_sub_sum]
  have := setIntegral_refSimplex_comp_permMap (k := m) (Fin.cycleRange j).symm
    (fun y => G (refBary y))
  simp only [refBary_permMap, Equiv.symm_symm] at this
  exact this

theorem hasDerivAt_insertNth (j : Fin (m + 1)) (y : Fin m → ℝ) (t : ℝ) :
    HasDerivAt (fun t => Fin.insertNth (α := fun _ => ℝ) j t y) (Pi.single j 1) t := by
  have h : (fun t : ℝ => Fin.insertNth (α := fun _ => ℝ) j t y) =
      fun t => Fin.insertNth (α := fun _ => ℝ) j 0 y + t • (Pi.single j 1 : Fin (m + 1) → ℝ) := by
    funext t i
    rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨l, rfl⟩
    · simp
    · simp [Fin.succAbove_ne]
  rw [h]
  simpa using ((hasDerivAt_id t).smul_const (Pi.single j (1 : ℝ))).const_add
    (Fin.insertNth (α := fun _ => ℝ) j 0 y)

theorem continuous_insertNth_left (j : Fin (m + 1)) (y : Fin m → ℝ) :
    Continuous fun t : ℝ => Fin.insertNth (α := fun _ => ℝ) j t y :=
  Continuous.finInsertNth (A := fun _ => ℝ) j continuous_id continuous_const

theorem continuous_insertNth_one_sub_sum (j : Fin (m + 1)) :
    Continuous fun y : Fin m → ℝ => Fin.insertNth (α := fun _ => ℝ) j (1 - ∑ i, y i) y :=
  Continuous.finInsertNth (A := fun _ => ℝ) j
    (continuous_const.sub (continuous_finsetSum _ fun i _ => continuous_apply i)) continuous_id

/-! ### The divergence theorem on the reference simplex -/

/-- **Fundamental theorem of calculus on the reference simplex**: for `h` of class `C¹` on a
neighbourhood of `T̂_{m+1}`,
`∫_{T̂_{m+1}} ∂ⱼ h = ∫_{T̂_m} h(λ̂(ŷ)) dŷ - ∫_{T̂_m} h(ŷ with 0 inserted at j) dŷ`. -/
theorem setIntegral_refSimplex_partialDeriv (j : Fin (m + 1)) {h : (Fin (m + 1) → ℝ) → ℝ}
    {U : Set (Fin (m + 1) → ℝ)} (hU : IsOpen U) (hTU : refSimplex (m + 1) ⊆ U)
    (hh : ContDiffOn ℝ 1 h U) :
    ∫ x in refSimplex (m + 1), partialDeriv j h x =
      (∫ y in refSimplex m, h (refBary y)) - ∫ y in refSimplex m, h (Fin.insertNth j 0 y) := by
  have hcont : ContinuousOn (partialDeriv j h) U := by
    have := hh.continuousOn_fderiv_of_isOpen hU le_rfl
    rw [partialDeriv_fun]
    exact this.clm_apply continuousOn_const
  have hdiff : ∀ x ∈ U, HasFDerivAt h (fderiv ℝ h x) x := fun x hx =>
    (((hh.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hhc : ContinuousOn h U := hh.continuousOn
  have hi1 : IntegrableOn (fun y => h (refBary y)) (refSimplex m) :=
    (hhc.comp continuous_refBary.continuousOn fun y hy => hTU (refBary_mem_refSimplex hy)
      ).integrableOn_compact (isCompact_refSimplex m)
  have hi2 : IntegrableOn (fun y => h (Fin.insertNth j 0 y)) (refSimplex m) :=
    (hhc.comp (continuous_insertNth_const j 0).continuousOn fun y hy =>
      hTU (insertNth_zero_mem_refSimplex j hy)).integrableOn_compact (isCompact_refSimplex m)
  have hi3 : IntegrableOn (fun y => h (Fin.insertNth j (1 - ∑ i, y i) y)) (refSimplex m) := by
    refine (hhc.comp (continuous_insertNth_one_sub_sum j).continuousOn fun y hy => ?_
      ).integrableOn_compact (isCompact_refSimplex m)
    refine hTU ((insertNth_mem_refSimplex_iff j _ y).2 ⟨hy, ?_, le_rfl⟩)
    linarith [(mem_refSimplex_iff.1 hy).2]
  rw [setIntegral_refSimplex_succ j
    ((hcont.mono hTU).integrableOn_compact (isCompact_refSimplex _)),
    ← setIntegral_refSimplex_insertNth_one_sub_sum j h, ← integral_sub hi3 hi2]
  refine setIntegral_congr_fun (measurableSet_refSimplex m) fun y hy => ?_
  have ha : 0 ≤ 1 - ∑ i, y i := by linarith [(mem_refSimplex_iff.1 hy).2]
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) (1 - ∑ i, y i), Fin.insertNth j t y ∈ U := by
    intro t ht
    rw [Set.uIcc_of_le ha] at ht
    exact hTU ((insertNth_mem_refSimplex_iff j t y).2 ⟨hy, ht⟩)
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => h (Fin.insertNth j t y))
    (f' := fun t => partialDeriv j h (Fin.insertNth j t y)) (fun t ht => ?_) ?_
  · exact (hdiff _ (hmem t ht)).comp_hasDerivAt t (hasDerivAt_insertNth j y t)
  · refine ContinuousOn.intervalIntegrable ?_
    exact hcont.comp (continuous_insertNth_left j y).continuousOn hmem

/-- **The divergence theorem on the reference simplex.** For a vector field `F` of class `C¹`
on a neighbourhood of `T̂_{m+1}`,
`∫_{T̂_{m+1}} div F = ∫_{T̂_m} Σⱼ Fⱼ(λ̂(ŷ)) dŷ - Σⱼ ∫_{T̂_m} Fⱼ(ŷ with 0 at j) dŷ`:
the flux through the slanted face (outward normal `(1, …, 1)/√(m+1)`, area element
`√(m+1) dŷ`) and through the coordinate faces `{x̂ⱼ = 0}` (outward normal `-eⱼ`). -/
theorem setIntegral_refSimplex_divergence {F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ}
    {U : Set (Fin (m + 1) → ℝ)} (hU : IsOpen U) (hTU : refSimplex (m + 1) ⊆ U)
    (hF : ∀ j, ContDiffOn ℝ 1 (F j) U) :
    ∫ x in refSimplex (m + 1), ∑ j, partialDeriv j (F j) x =
      (∫ y in refSimplex m, ∑ j, F j (refBary y)) -
        ∑ j, ∫ y in refSimplex m, F j (Fin.insertNth j 0 y) := by
  have hcont : ∀ j, ContinuousOn (partialDeriv j (F j)) U := fun j => by
    have := (hF j).continuousOn_fderiv_of_isOpen hU le_rfl
    rw [partialDeriv_fun]
    exact this.clm_apply continuousOn_const
  have hI1 : ∀ j, IntegrableOn (fun x => partialDeriv j (F j) x) (refSimplex (m + 1)) :=
    fun j => ((hcont j).mono hTU).integrableOn_compact (isCompact_refSimplex _)
  have hI2 : ∀ j, IntegrableOn (fun y => F j (refBary y)) (refSimplex m) := fun j =>
    ((hF j).continuousOn.comp continuous_refBary.continuousOn
      fun y hy => hTU (refBary_mem_refSimplex hy)).integrableOn_compact (isCompact_refSimplex m)
  rw [integral_finsetSum _ fun j _ => hI1 j, integral_finsetSum _ fun j _ => hI2 j,
    ← sum_sub_distrib]
  exact sum_congr rfl fun j _ => setIntegral_refSimplex_partialDeriv j hU hTU (hF j)

/-! ### Pullbacks to the faces of the reference simplex -/

theorem map_succAboveOrderEmb_univ (j : Fin (m + 1)) :
    (univ : Finset (Fin m)).map (Fin.succAboveOrderEmb j).toEmbedding = univ.erase j := by
  ext i
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨l, rfl⟩
  · simp [Fin.succAbove_ne]
  · simp [Fin.succAbove_ne]

/-- The coordinate face `{x̂ⱼ = 0}` (opposite `v̂ⱼ₊₁`): its parametrization inserts `0` at `j`
and the pullback picks the coefficient of `dx̂_{univ ∖ j}`. -/
theorem simplexIntegral_refFace_succ (j : Fin (m + 1)) (η : FormField (m + 1)) :
    simplexIntegral (refVertex (m + 1) ∘ (j.succ).succAbove) η =
      ∫ y in refSimplex m, η (Fin.insertNth j 0 y) (univ.erase j) := by
  have hB : simplexMatrix (refVertex (m + 1) ∘ (j.succ).succAbove) =
      fun a l => if a = j.succAbove l then 1 else 0 := by
    funext a l
    simp [simplexMatrix, Fin.succ_succAbove_succ, Pi.single_apply]
  have hb : (refVertex (m + 1) ∘ (j.succ).succAbove) 0 = 0 := by simp
  have hmap : ∀ y, affine (simplexMatrix (refVertex (m + 1) ∘ (j.succ).succAbove))
      ((refVertex (m + 1) ∘ (j.succ).succAbove) 0) y = Fin.insertNth j 0 y := by
    intro y
    rw [hB, hb]
    funext a
    simp only [affine_apply, Pi.zero_apply, add_zero]
    rcases Fin.eq_self_or_eq_succAbove j a with rfl | ⟨l, rfl⟩
    · simp
    · rw [Finset.sum_eq_single l (fun l' _ hl' => by simp [Ne.symm hl']) (by simp)]
      simp
  have hB' : ∀ a l, (a = Fin.succAboveOrderEmb j l →
      simplexMatrix (refVertex (m + 1) ∘ (j.succ).succAbove) a l = 1) ∧
      (a ≠ Fin.succAboveOrderEmb j l →
        simplexMatrix (refVertex (m + 1) ∘ (j.succ).succAbove) a l = 0) := fun a l => by
    rw [hB]
    exact ⟨fun h => by simp [h], fun h => by
      simp only [ite_eq_right_iff]; exact fun h' => absurd h' h⟩
  simp only [simplexIntegral, affinePullback_apply, hmap,
    pullback_eq_restrict (Fin.succAboveOrderEmb j) hB', ExteriorFibre.restrict,
    map_succAboveOrderEmb_univ]

/-- The coefficients of the pullback to the slanted face: `Σⱼ (-1)ʲ α_{univ ∖ j}`. -/
theorem pullback_refFace_zero_apply_univ (α : Finset (Fin (m + 1)) → ℝ) :
    pullback (fun (a : Fin (m + 1)) (l : Fin m) =>
      (Pi.single l.succ (1 : ℝ) : Fin (m + 1) → ℝ) a - (Pi.single 0 (1 : ℝ) : Fin (m + 1) → ℝ) a)
        α univ = ∑ j : Fin (m + 1), (-1) ^ (j : ℕ) * α (univ.erase j) := by
  set B : Fin (m + 1) → Fin m → ℝ := fun a l =>
    (Pi.single l.succ (1 : ℝ) : Fin (m + 1) → ℝ) a - (Pi.single 0 (1 : ℝ) : Fin (m + 1) → ℝ) a
  have hsucc : (fun a => B (Fin.succAboveOrderEmb 0 a)) = fun a => Pi.single a 1 := by
    funext a l
    simp [B, Pi.single_apply, Fin.succ_ne_zero, eq_comm]
  rw [pullback_apply, sum_eq_sum_erase_of_card (fun s => α s * wedgeProd B s univ) fun s hs => by
    rw [isDeg_wedgeProd B s univ (by rw [card_univ, Fintype.card_fin]; exact Ne.symm hs),
      mul_zero]]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  congr 1
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [← map_succAboveOrderEmb_univ, wedgeProd_map]
    change wedgeProd (fun a => B (Fin.succAboveOrderEmb 0 a)) univ univ = _
    rw [hsucc, wedgeProd_single]; simp
  · have h0 : (0 : Fin (m + 1)) ∈ univ.erase j.succ := by simp [(Fin.succ_ne_zero j).symm]
    have herase : (univ.erase j.succ).erase 0 =
        (univ.erase j).map (Fin.succAboveOrderEmb 0).toEmbedding := by
      ext x
      rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨x, rfl⟩
      · simp [Fin.succ_ne_zero]
      · simp [Fin.succ_ne_zero]
    rw [wedgeProd_eq_sgn_smul_wedge_erase B h0, herase, wedgeProd_map]
    change ((sgn 0 (univ.erase j.succ) : ℝ) • wedge (B 0)
      (wedgeProd (fun a => B (Fin.succAboveOrderEmb 0 a)) (univ.erase j))) univ = _
    rw [hsucc, wedgeProd_single]
    have hs0 : (sgn 0 (univ.erase j.succ) : ℝ) = 1 := by
      rw [sgn, filter_eq_empty_iff.2 fun x _ => not_lt.2 (Fin.zero_le x)]; simp
    have hB0 : B 0 = fun _ => -1 := by
      funext l; simp [B, Fin.succ_ne_zero]
    rw [hs0, one_smul, hB0, wedge_apply]
    rw [sum_eq_single j (fun l _ hl => by
      have : univ.erase l ≠ univ.erase j := by
        intro h
        have h' : l ∈ univ.erase j := mem_erase.2 ⟨hl, mem_univ _⟩
        rw [← h] at h'
        simp at h'
      simp [this]) (by simp)]
    rw [sgn_univ]
    simp [Fin.val_succ, pow_succ]

/-- The slanted face (opposite `v̂₀`): its parametrization is the barycentric map `λ̂` and the
pullback is `Σⱼ (-1)ʲ η_{univ ∖ j}`. -/
theorem simplexIntegral_refFace_zero (η : FormField (m + 1)) :
    simplexIntegral (refVertex (m + 1) ∘ (0 : Fin (m + 2)).succAbove) η =
      ∫ y in refSimplex m, ∑ j : Fin (m + 1), (-1) ^ (j : ℕ) * η (refBary y) (univ.erase j) := by
  have hB : simplexMatrix (refVertex (m + 1) ∘ (0 : Fin (m + 2)).succAbove) =
      fun (a : Fin (m + 1)) (l : Fin m) => (Pi.single l.succ (1 : ℝ) : Fin (m + 1) → ℝ) a -
        (Pi.single 0 (1 : ℝ) : Fin (m + 1) → ℝ) a := by
    funext a l
    have h1 : refVertex (m + 1) 1 = Pi.single 0 1 := by
      rw [← Fin.succ_zero_eq_one, refVertex_succ]
    simp [simplexMatrix, h1]
  have hmap : ∀ y, affine (simplexMatrix (refVertex (m + 1) ∘ (0 : Fin (m + 2)).succAbove))
      ((refVertex (m + 1) ∘ (0 : Fin (m + 2)).succAbove) 0) y = refBary y := by
    intro y
    change simplexMap _ y = _
    rw [simplexMap_eq_sum]
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Fin.succAbove_zero,
      refVertex_succ, smul_eq_mul]
    rw [Finset.sum_eq_single a (fun l _ hl => by simp [hl]) (by simp)]
    simp
  simp only [simplexIntegral, affinePullback_apply, hmap]
  rw [hB]
  simp only [pullback_refFace_zero_apply_univ]

/-! ### Stokes' theorem -/

/-- **Stokes' theorem on the reference simplex**: for a form `η` of class `C¹` on a
neighbourhood of `T̂_{m+1}`, `∫_{T̂_{m+1}} (dη)_{univ} = Σᵢ (-1)ⁱ ∫_{∂ᵢ T̂} η`. -/
theorem setIntegral_refSimplex_extDeriv {η : FormField (m + 1)} {U : Set (Fin (m + 1) → ℝ)}
    (hU : IsOpen U) (hTU : refSimplex (m + 1) ⊆ U) (hη : ContDiffOn ℝ 1 η U) :
    ∫ x in refSimplex (m + 1), extDeriv η x univ =
      ∑ i : Fin (m + 2), (-1) ^ (i : ℕ) *
        simplexIntegral (refVertex (m + 1) ∘ i.succAbove) η := by
  have hc : ∀ s, ContDiffOn ℝ 1 (fun x => η x s) U := fun s => contDiffOn_pi.1 hη s
  have hcont : ∀ j : Fin (m + 1), ContinuousOn
      (partialDeriv j (fun x => η x (univ.erase j))) U := fun j => by
    have := (hc (univ.erase j)).continuousOn_fderiv_of_isOpen hU le_rfl
    rw [partialDeriv_fun]
    exact this.clm_apply continuousOn_const
  simp only [extDeriv_apply, sgn_univ]
  rw [integral_finsetSum _ fun j _ =>
    (((hcont j).mono hTU).integrableOn_compact (isCompact_refSimplex _)).const_mul _]
  simp only [integral_const_mul]
  simp only [fun j : Fin (m + 1) => setIntegral_refSimplex_partialDeriv j hU hTU
    (hc (univ.erase j))]
  conv_rhs => rw [Fin.sum_univ_succ, simplexIntegral_refFace_zero]
  simp only [simplexIntegral_refFace_succ, Fin.val_zero, pow_zero, one_mul, Fin.val_succ]
  have hI : ∀ j : Fin (m + 1), IntegrableOn
      (fun y => (-1 : ℝ) ^ (j : ℕ) * η (refBary y) (univ.erase j)) (refSimplex m) := fun j =>
    (((hc (univ.erase j)).continuousOn.comp continuous_refBary.continuousOn
      fun y hy => hTU (refBary_mem_refSimplex hy)).integrableOn_compact
        (isCompact_refSimplex m)).const_mul _
  rw [integral_finsetSum _ fun j _ => hI j]
  simp only [integral_const_mul]
  have hs : ∀ j : Fin (m + 1), (-1 : ℝ) ^ ((j : ℕ) + 1) = -(-1) ^ (j : ℕ) := fun j => by ring
  simp only [hs, neg_mul, sum_neg_distrib, mul_sub, sum_sub_distrib]
  ring

/-- **Stokes' theorem on an affine simplex**: for an oriented affine `(k+1)`-simplex
`p = (p₀, …, p_{k+1})` in `ℝⁿ` and a form `ω` of class `C¹` on an open neighbourhood `U` of the
simplex, `∫_p dω = Σᵢ (-1)ⁱ ∫_{∂ᵢ p} ω`, where `∂ᵢ p = p ∘ succAbove i` omits the vertex `pᵢ`. -/
theorem simplexIntegral_extDeriv (p : Fin (k + 2) → Fin n → ℝ) {ω : FormField n}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hpU : simplexMap p '' refSimplex (k + 1) ⊆ U)
    (hω : ContDiffOn ℝ 1 ω U) :
    simplexIntegral p (extDeriv ω) =
      ∑ i : Fin (k + 2), (-1) ^ (i : ℕ) * simplexIntegral (p ∘ i.succAbove) ω := by
  set η := affinePullback (simplexMatrix p) (p 0) ω
  have hU' : IsOpen (simplexMap p ⁻¹' U) := hU.preimage (continuous_simplexMap p)
  have hTU : refSimplex (k + 1) ⊆ simplexMap p ⁻¹' U := fun x hx => hpU ⟨x, hx, rfl⟩
  have hη : ContDiffOn ℝ 1 η (simplexMap p ⁻¹' U) :=
    contDiffOn_affinePullback (simplexMatrix p) (p 0) hω
  have h1 : simplexIntegral p (extDeriv ω) = ∫ x in refSimplex (k + 1), extDeriv η x univ := by
    refine setIntegral_congr_fun (measurableSet_refSimplex _) fun x hx => ?_
    have hd : DifferentiableAt ℝ ω (affine (simplexMatrix p) (p 0) x) :=
      ((hω.differentiableOn one_ne_zero) _ (hTU hx)).differentiableAt
        (hU.mem_nhds (hTU hx))
    simp only [η]
    rw [extDeriv_affinePullback_apply _ _ hd]
  rw [h1, setIntegral_refSimplex_extDeriv hU' hTU hη]
  refine sum_congr rfl fun i _ => ?_
  congr 1
  have hq : p ∘ i.succAbove = fun l => affine (simplexMatrix p) (p 0)
      ((refVertex (k + 1) ∘ i.succAbove) l) := by
    funext l; exact (simplexMap_refVertex p _).symm
  rw [hq, simplexIntegral_comp_affine]

/-- **Stokes' theorem for a Mathlib simplex** `σ : Affine.Simplex ℝ (Fin n → ℝ) (k + 1)`, with
the faces `σ.faceOpposite i`. -/
theorem simplexIntegral_extDeriv_faceOpposite (σ : Affine.Simplex ℝ (Fin n → ℝ) (k + 1))
    {ω : FormField n} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hσU : simplexMap σ.points '' refSimplex (k + 1) ⊆ U) (hω : ContDiffOn ℝ 1 ω U) :
    simplexIntegral σ.points (extDeriv ω) =
      ∑ i : Fin (k + 2), (-1) ^ (i : ℕ) * simplexIntegral (σ.faceOpposite i).points ω := by
  rw [simplexIntegral_extDeriv σ.points hU hσU hω]
  refine sum_congr rfl fun i _ => ?_
  congr 1
  have : (σ.faceOpposite i).points = σ.points ∘ i.succAbove := by
    funext j
    rw [Affine.Simplex.faceOpposite_point_eq_point_succAbove]
    rfl
  rw [this]

end Feec.FiniteElement
