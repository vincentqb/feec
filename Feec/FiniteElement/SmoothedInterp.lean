module

public import Feec.FiniteElement.GlobalInterpolation
public import Feec.Domain.StarShapedSmoothing

/-!
# The smoothed canonical interpolant of an element family

For an element family on a simplicial mesh of an open `Ω ⊆ ℝⁿ` star-shaped with respect to a ball,
the glued canonical interpolant `Q = Π_h R` of the smoothed forms `R u` commutes with the exterior
derivative: for maximal-family smoothing parameters it maps into `Vₕ ⊆ HΛ(Ω)`, for minimal-family
parameters into `V̊ₕ ⊆ H̊Λ(Ω)`.

## Main results

* `LocalElement.maximal_smoothedInterp`, `LocalElement.minimal_smoothedInterp`: `d Q u = Q d u`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff

namespace Feec.FiniteElement

open Feec.Domain Feec.Mesh Feec.ExteriorFibre

variable {n : ℕ}

section SmoothForm

variable {Ω : Set (Fin n → ℝ)} (p : SmoothingParam (Fin n → ℝ))

/-- The coefficients `cᵏ R̃ uₛ` of the smoothed `k`-form. -/
def smoothCoeff (p : SmoothingParam (Fin n → ℝ)) (k : ℤ) (u : L2F ℝ Ω (formIdx n k))
    (s : formIdx n k) : (Fin n → ℝ) → ℝ :=
  fun x => p.factor ^ k * smoothExt Ω p ((u s : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) x

theorem contDiff_smoothCoeff (hΩ : MeasurableSet Ω) (k : ℤ) (u : L2F ℝ Ω (formIdx n k))
    (s : formIdx n k) :
    ContDiff ℝ ∞ (smoothCoeff p k u s) :=
  contDiff_const.mul (contDiff_smoothExt ((memLp_indicator hΩ _).locallyIntegrable (by norm_num)))

/-- The smoothed `k`-form `x ↦ Σₛ cᵏ (R̃ uₛ)(x) dxₛ`, as a linear map `L²(Ω; Λᵏ) → C¹Λᵏ`. -/
def smoothForm (p : SmoothingParam (Fin n → ℝ)) (hΩ : MeasurableSet Ω) (k : ℤ) :
    L2F ℝ Ω (formIdx n k) →ₗ[ℝ] c1Forms n where
  toFun u := ⟨fun x t => formExt (smoothCoeff p k u) t x,
    mem_c1Forms.2 (contDiff_pi.2 fun t =>
      (contDiff_formExt (contDiff_smoothCoeff p hΩ k u) t).of_le (by exact_mod_cast le_top))⟩
  map_add' u v := by
    refine Subtype.ext (funext fun x => funext fun t => ?_)
    change formExt (smoothCoeff p k (u + v)) t x =
      formExt (smoothCoeff p k u) t x + formExt (smoothCoeff p k v) t x
    unfold formExt
    split_ifs with h
    · simp only [smoothCoeff, PiLp.add_apply, smoothExt_coe_add hΩ, Pi.add_apply]; ring
    · simp
  map_smul' a u := by
    refine Subtype.ext (funext fun x => funext fun t => ?_)
    change formExt (smoothCoeff p k (a • u)) t x = a * formExt (smoothCoeff p k u) t x
    unfold formExt
    split_ifs with h
    · simp only [smoothCoeff, PiLp.smul_apply, smoothExt_coe_smul hΩ, Pi.smul_apply,
        smul_eq_mul]; ring
    · simp

theorem smoothForm_apply (hΩ : MeasurableSet Ω) (k : ℤ) (u : L2F ℝ Ω (formIdx n k)) (x : Fin n → ℝ)
    (t : Finset (Fin n)) :
    (smoothForm p hΩ k u : FormField n) x t = formExt (smoothCoeff p k u) t x := rfl

theorem isDeg_smoothForm (hΩ : MeasurableSet Ω) (k : ℕ) (u : L2F ℝ Ω (formIdx n k))
    (x : Fin n → ℝ) :
    IsDeg k ((smoothForm p hΩ k u : FormField n) x) := by
  intro t ht
  rw [smoothForm_apply]
  unfold formExt
  split_ifs with h
  · exact absurd (by exact_mod_cast h) ht
  · rfl

theorem formComp_smoothForm (hΩ : MeasurableSet Ω) (k : ℕ) (u : L2F ℝ Ω (formIdx n k)) :
    formComp (k := (k : ℤ)) (smoothForm p hΩ k u : FormField n) =
      fun s => p.factor ^ (k : ℤ) • smoothExt Ω p ((u s : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) := by
  funext s x
  change formExt (smoothCoeff p k u) s.1 x = _
  rw [formExt_val]
  rfl

theorem extDeriv_smoothForm_of_maximal (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω) {x₀ : Fin n → ℝ}
    {s₀ : ℝ}
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ Ω) (hp : p.IsMaximal x₀ s₀)
    (k : ℕ) (u : ((extDerivOp ℝ n k).maximal Ω).domain) {x : Fin n → ℝ} (hx : x ∈ closure Ω) :
    extDeriv (smoothForm p hΩ k u : FormField n) x =
      (smoothForm p hΩ ((k : ℤ) + 1) ((extDerivOp ℝ n k).maximal Ω u) : FormField n) x := by
  funext t
  by_cases ht : (#t : ℤ) = (k : ℤ) + 1
  · have h1 := extDerivOp_apply_formComp (isDeg_smoothForm p hΩ k (u : L2F ℝ Ω (formIdx n k)))
      ⟨t, ht⟩ x
    rw [formComp_smoothForm] at h1
    rw [← h1, apply_smoothExt_of_maximal hΩo hstar hp (extDerivOp_isRowHomogeneous k) u _ _ hx,
      smoothForm_apply, formExt_of_card _ ht]
    change _ = p.factor ^ ((k : ℤ) + 1) * _
    rw [pow_one, zpow_add_one₀ p.factor_pos.ne']
  · have h0 := IsDeg.extDeriv (isDeg_smoothForm p hΩ k (u : L2F ℝ Ω (formIdx n k))) x t
      (fun h => ht (by exact_mod_cast h))
    rw [h0, smoothForm_apply]
    simp [formExt, ht]

theorem extDeriv_smoothForm_of_minimal (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω) (k : ℕ)
    (u : ((extDerivOp ℝ n k).minimal Ω).domain) (x : Fin n → ℝ) :
    extDeriv (smoothForm p hΩ k u : FormField n) x =
      (smoothForm p hΩ ((k : ℤ) + 1) ((extDerivOp ℝ n k).minimal Ω u) : FormField n) x := by
  funext t
  by_cases ht : (#t : ℤ) = (k : ℤ) + 1
  · have h1 := extDerivOp_apply_formComp (isDeg_smoothForm p hΩ k (u : L2F ℝ Ω (formIdx n k)))
      ⟨t, ht⟩ x
    rw [formComp_smoothForm] at h1
    rw [← h1, apply_smoothExt_of_minimal (p := p) hΩo (extDerivOp_isRowHomogeneous k) u _ _ x,
      smoothForm_apply, formExt_of_card _ ht]
    change _ = p.factor ^ ((k : ℤ) + 1) * _
    rw [pow_one, zpow_add_one₀ p.factor_pos.ne']
  · have h0 := IsDeg.extDeriv (isDeg_smoothForm p hΩ k (u : L2F ℝ Ω (formIdx n k))) x t
      (fun h => ht (by exact_mod_cast h))
    rw [h0, smoothForm_apply]
    simp [formExt, ht]

theorem smoothForm_eq_zero_of_minimal (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : Fin n → ℝ} {s₀ : ℝ} (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ Ω)
    (hp : p.IsMinimal x₀ s₀) (k : ℤ) (u : L2F ℝ Ω (formIdx n k)) {x : Fin n → ℝ} (hx : x ∉ Ω) :
    (smoothForm p hΩ.measurableSet k u : FormField n) x = 0 := by
  funext t
  rw [smoothForm_apply]
  unfold formExt
  split_ifs with h
  · change p.factor ^ k * smoothExt Ω p ((u ⟨t, h⟩ : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) x = 0
    rw [image_eq_zero_of_notMem_tsupport fun hx' => hx ((isTest_smoothExt hb hstar hp
      ((memLp_indicator hΩ.measurableSet _).locallyIntegrable (by norm_num))).tsupport_subset hx'),
      mul_zero]
  · rfl

end SmoothForm

namespace LocalElement

variable (E : LocalElement n) (M : SimplicialMesh n)

theorem globalInterp_congr (k : ℕ) {w w' : contForms n}
    (h : ∀ x ∈ closure M.domain, (w : FormField n) x = (w' : FormField n) x) :
    E.globalInterp M k w = E.globalInterp M k w' := by
  refine E.globalInterp_piecewise M k _ w fun T g hg i => ?_
  rw [localDof_globalInterp _ _ _ _ _ _ hg]
  refine E.dof_congr i fun x hx V _ => ?_
  have hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := by
    rw [← Mesh.convexHull_vertexSet]
    exact convexHull_mono (Finset.coe_subset.2 hg) hx
  have hxΩ : x ∈ closure M.domain := by
    rw [← M.biUnion_closedInterior]
    exact Set.mem_biUnion T.2 hxT
  rw [h x hxΩ]

variable (p : SmoothingParam (Fin n → ℝ))

/-- The smoothed canonical interpolant `Q = Π_h R : L²(Ω; Λᵏ) → Vₕᵏ`. [AFW2010], §5.5 -/
def smoothedInterp (p : SmoothingParam (Fin n → ℝ)) (hΩ : MeasurableSet M.domain) :
    ∀ k : ℤ, L2F ℝ M.domain (formIdx n k) →ₗ[ℝ] L2F ℝ M.domain (formIdx n k)
  | Int.ofNat k => E.glue M k ∘ₗ (E.globalSpace M k).subtype ∘ₗ E.globalInterp M k ∘ₗ
      Submodule.inclusion c1Forms_le_contForms ∘ₗ smoothForm p hΩ k
  | Int.negSucc _ => 0

theorem smoothedInterp_natCast (hΩ : MeasurableSet M.domain) (k : ℕ)
    (u : L2F ℝ M.domain (formIdx n k)) :
    E.smoothedInterp M p hΩ k u = E.glue M k (E.globalInterp M k
      (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k u)) : E.Piecewise M k) := rfl

theorem smoothedInterp_mem_V (hΩ : MeasurableSet M.domain) (k : ℤ)
    (u : L2F ℝ M.domain (formIdx n k)) :
    E.smoothedInterp M p hΩ k u ∈ E.V M k := by
  rcases k with k | k
  · exact ⟨_, rfl⟩
  · exact Submodule.zero_mem _

/-- **`d_max Q u = Q d_max u`** (maximal family). -/
theorem maximal_smoothedInterp [NeZero n] (hΩ : MeasurableSet M.domain) (hΩo : IsOpen M.domain)
    {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMaximal x₀ s₀) (k : ℕ) (u : ((extDerivOp ℝ n k).maximal M.domain).domain) :
    ∃ h : E.smoothedInterp M p hΩ k u ∈ ((extDerivOp ℝ n k).maximal M.domain).domain,
      (extDerivOp ℝ n k).maximal M.domain ⟨_, h⟩ =
        E.smoothedInterp M p hΩ ((k : ℤ) + 1) ((extDerivOp ℝ n k).maximal M.domain u) := by
  set w := smoothForm p hΩ k (u : L2F ℝ M.domain (formIdx n k))
  obtain ⟨h, hval⟩ := E.glue_mem_maximal M hΩo k
    (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w))
  refine ⟨h, hval.trans ?_⟩
  have h1 : E.dPiecewise M k
      (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) : E.Piecewise M k) =
      (E.dGlobal M k (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w)) :
        E.Piecewise M (k + 1)) := rfl
  rw [h1, ← globalInterp_extDeriv]
  have h2 : E.globalInterp M (k + 1) (extDerivC1 w) = E.globalInterp M (k + 1)
      (Submodule.inclusion c1Forms_le_contForms
        (smoothForm p hΩ ((k + 1 : ℕ) : ℤ) ((extDerivOp ℝ n k).maximal M.domain u))) :=
    E.globalInterp_congr M (k + 1) fun x hx =>
      extDeriv_smoothForm_of_maximal p hΩ hΩo hstar hp k u hx
  rw [h2]
  rfl

/-- `Q = Π_h R` as a commuting map into `Vₕ ⊆ HΛ(Ω)` (maximal family). -/
def smoothedCommutingMap [NeZero n] (hΩo : IsOpen M.domain) {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMaximal x₀ s₀) : (E.subcomplex M hΩo).CommutingMap where
  Q := E.smoothedInterp M p hΩo.measurableSet
  mem i x := E.smoothedInterp_mem_V M p hΩo.measurableSet i x
  comm i j x := by
    by_cases hij : i + 1 = j
    · subst hij
      have hd := deRham_maximalComplex_d (𝕜 := ℝ) (n := n) hΩo i
      rcases i with k | k
      · rw [LinearPMap.apply_eq_of_eq' hd, LinearPMap.apply_eq_of_eq' hd x]
        obtain ⟨h, hv⟩ := E.maximal_smoothedInterp M p hΩo.measurableSet hΩo hstar hp k
          ⟨x.1, hd ▸ x.2⟩
        exact hv
      · have h0 : ∀ y : (((deRham ℝ n).maximalComplex hΩo).d (Int.negSucc k)
            (Int.negSucc k + 1)).domain, ((deRham ℝ n).maximalComplex hΩo).d _ _ y = 0 := by
          intro y
          have : y = 0 := Subtype.ext ((subsingleton_L2F_negSucc M.domain k).elim _ _)
          rw [this, LinearPMap.map_zero]
        rw [h0, h0]
        exact (E.smoothedInterp M p hΩo.measurableSet _).map_zero.symm
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij),
        HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij)]
      exact (E.smoothedInterp M p hΩo.measurableSet j).map_zero.symm

@[simp] theorem smoothedCommutingMap_Q [NeZero n] (hΩo : IsOpen M.domain) {x₀ : Fin n → ℝ}
    {s₀ : ℝ} (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMaximal x₀ s₀) (i : ℤ) :
    (E.smoothedCommutingMap M p hΩo hstar hp).Q i = E.smoothedInterp M p hΩo.measurableSet i :=
  rfl

theorem smoothedInterp_mem_V₀ (hΩo : IsOpen M.domain) (hb : Bornology.IsBounded M.domain)
    {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMinimal x₀ s₀) (k : ℤ) (u : L2F ℝ M.domain (formIdx n k)) :
    E.smoothedInterp M p hΩo.measurableSet k u ∈ E.V₀ M k := by
  rcases k with k | k
  · exact ⟨⟨_, E.globalInterp_mem_globalSpace₀ M k fun x hx =>
      smoothForm_eq_zero_of_minimal p hΩo hb hstar hp k u (M.notMem_domain_of_mem_frontier hΩo hx)⟩,
      rfl⟩
  · exact Submodule.zero_mem _

/-- **`d_min Q u = Q d_min u`** (minimal family). -/
theorem minimal_smoothedInterp [NeZero n] (hΩo : IsOpen M.domain)
    (hb : Bornology.IsBounded M.domain) {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMinimal x₀ s₀) (y₀ : Fin n → ℝ)
    (hstar' : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → y₀ + t • (x - y₀) ∈ M.domain)
    (k : ℕ) (u : ((extDerivOp ℝ n k).minimal M.domain).domain) :
    ∃ h : E.smoothedInterp M p hΩo.measurableSet k u ∈
        ((extDerivOp ℝ n k).minimal M.domain).domain,
      (extDerivOp ℝ n k).minimal M.domain ⟨_, h⟩ =
        E.smoothedInterp M p hΩo.measurableSet ((k : ℤ) + 1)
          ((extDerivOp ℝ n k).minimal M.domain u) := by
  set w := smoothForm p hΩo.measurableSet k (u : L2F ℝ M.domain (formIdx n k))
  have hw : (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) : E.Piecewise M k) ∈
      E.globalSpace₀ M k := E.globalInterp_mem_globalSpace₀ M k fun x hx =>
    smoothForm_eq_zero_of_minimal p hΩo hb hstar hp k _ (M.notMem_domain_of_mem_frontier hΩo hx)
  obtain ⟨h, hval⟩ := E.glue_mem_minimal M hΩo y₀ hstar' k ⟨_, hw⟩
  refine ⟨h, hval.trans ?_⟩
  have h1 : E.dPiecewise M k
      (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) : E.Piecewise M k) =
      (E.dGlobal M k (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w)) :
        E.Piecewise M (k + 1)) := rfl
  change E.glue M ((k : ℤ) + 1) (E.dPiecewise M k
    (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) : E.Piecewise M k)) = _
  rw [h1, ← globalInterp_extDeriv]
  have h2 : E.globalInterp M (k + 1) (extDerivC1 w) = E.globalInterp M (k + 1)
      (Submodule.inclusion c1Forms_le_contForms
        (smoothForm p hΩo.measurableSet ((k + 1 : ℕ) : ℤ)
          ((extDerivOp ℝ n k).minimal M.domain u))) :=
    E.globalInterp_congr M (k + 1) fun x _ =>
      extDeriv_smoothForm_of_minimal p hΩo.measurableSet hΩo k u x
  rw [h2]
  rfl

/-- `Q = Π_h R` as a commuting map into `V̊ₕ ⊆ H̊Λ(Ω)` (minimal family). -/
def smoothedCommutingMapMin [NeZero n] (hΩo : IsOpen M.domain)
    (hb : Bornology.IsBounded M.domain) {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMinimal x₀ s₀) (y₀ : Fin n → ℝ)
    (hstar' : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → y₀ + t • (x - y₀) ∈ M.domain) :
    (E.subcomplexMin M hΩo y₀ hstar').CommutingMap where
  Q := E.smoothedInterp M p hΩo.measurableSet
  mem i x := E.smoothedInterp_mem_V₀ M p hΩo hb hstar hp i x
  comm i j x := by
    by_cases hij : i + 1 = j
    · subst hij
      have hd := deRham_minimalComplex_d (𝕜 := ℝ) (n := n) hΩo i
      rcases i with k | k
      · rw [LinearPMap.apply_eq_of_eq' hd, LinearPMap.apply_eq_of_eq' hd x]
        obtain ⟨h, hv⟩ := E.minimal_smoothedInterp M p hΩo hb hstar hp y₀ hstar' k
          ⟨x.1, hd ▸ x.2⟩
        exact hv
      · have h0 : ∀ y : (((deRham ℝ n).minimalComplex hΩo).d (Int.negSucc k)
            (Int.negSucc k + 1)).domain, ((deRham ℝ n).minimalComplex hΩo).d _ _ y = 0 := by
          intro y
          have : y = 0 := Subtype.ext ((subsingleton_L2F_negSucc M.domain k).elim _ _)
          rw [this, LinearPMap.map_zero]
        rw [h0, h0]
        exact (E.smoothedInterp M p hΩo.measurableSet _).map_zero.symm
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij),
        HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij)]
      exact (E.smoothedInterp M p hΩo.measurableSet j).map_zero.symm

@[simp] theorem smoothedCommutingMapMin_Q [NeZero n] (hΩo : IsOpen M.domain)
    (hb : Bornology.IsBounded M.domain) {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMinimal x₀ s₀) (y₀ : Fin n → ℝ)
    (hstar' : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → y₀ + t • (x - y₀) ∈ M.domain)
    (i : ℤ) :
    (E.smoothedCommutingMapMin M p hΩo hb hstar hp y₀ hstar').Q i =
      E.smoothedInterp M p hΩo.measurableSet i :=
  rfl

end LocalElement

end Feec.FiniteElement
