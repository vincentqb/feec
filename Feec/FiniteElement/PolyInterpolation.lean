module

public import Feec.FiniteElement.PolyInverseEstimate
public import Feec.FiniteElement.WhitneyInterpolation
public import Feec.FiniteElement.PolyElement

/-!
# Interpolation error of the canonical interpolants of `P_rΛᵏ` and `P_r⁻Λᵏ`

The canonical interpolants `Π_T = polyInterp`, `polyMinusInterp` of `Feec.FiniteElement.LocalDof`
(defined by the moment DOFs `∫_f tr_f ω ∧ η`) are estimated on homothetic simplices
`T = t + h K` in the classical `C^{s+1}` form of [Arnold2018], Ch. 7 and [Ciarlet2002],
Thm 3.1.4, by transport from the reference simplex `T̂` with `Feec.FiniteElement.transportInterp`.
This generalizes `Feec.FiniteElement.WhitneyInterpolation` (`P₁⁻Λᵏ`) to all orders.

* **Naturality** (`affinePullback_polyInterp`, `affinePullback_polyMinusInterp`): for
  nondegenerate simplices `q = G ∘ p`, `G y = A y + a`, `G^* Π_q ω = Π_p G^* ω`: the moments of
  `ω` on the faces of `q` are the moments of `G^* ω` on the faces of `p`
  (`Feec.FiniteElement.faceMoment_affine`), and the DOFs are unisolvent. This is the naturality
  that `Feec.FiniteElement.norm_sub_transportInterp_le` needs.
* **Reference interpolants** in all form degrees at once (`momentRefInterp`, `polyRefInterp`,
  `polyMinusRefInterp`): `I g = Σ_k Π_{T̂}(g)_k`, with the moments computed for any field `g`
  (`(g)_k` its degree-`k` part, `degPartField`). They are additive on fields continuous on `T̂`
  (`momentRefInterp_sub`, via `faceMoment_sub_of_continuousOn`), stable in `C⁰(T̂)` since the
  moments only need values (`exists_abs_faceMoment_le`, `exists_norm_momentRefInterp_le`), agree
  with `Π_{T̂}` on continuous `k`-forms (`polyRefInterp_eq_polyInterp`), and reproduce `P_s(ℝⁿ; Λ)`
  for `s ≤ r` (`P_rΛ`, `polyRefInterp_apply_eq`) and for `s ≤ r - 1` (`P_r⁻Λ`,
  `polyMinusRefInterp_apply_eq`). Hence they satisfy `Feec.FiniteElement.IsRefInterpolant n s 0`
  (`exists_isRefInterpolant_polyRefInterp`, `exists_isRefInterpolant_polyMinusRefInterp`).
* **Transport** (`transportInterp_polyRefInterp_eq`): on `T = t + h K`, with the `h`-independent
  fibre map `Φ_K = B_K^*` (`fibrePullbackEquiv`), `Φ_K⁻¹ ∘ I (Φ_K ∘ w ∘ F_T) ∘ F_T⁻¹ = Π_T w` for
  continuous `k`-forms (`F_T^* w = hᵏ Φ_K ∘ w ∘ F_T`, `affinePullback_points_mapEquiv_boxMap`), and
  `‖B_T‖ = h ‖B_K‖` (`norm_linearEquiv_mapEquiv_boxMap`).
* **Local error estimates**, constants depending only on `K`, `n`, `r`, `s`:
  `sup_T ‖w - Π_T w‖ ≤ C h^{s+1} sup_T ‖D^{s+1} w‖` for `s ≤ r` (`P_rΛᵏ`,
  `exists_norm_sub_polyInterp_le`) and `s ≤ r - 1` (`P_r⁻Λᵏ`,
  `exists_norm_sub_polyMinusInterp_le`), so the full orders `h^{r+1}` and `h^r`, and `O(h)` for
  `C¹` data (`s = 0`). The `L²(T)` and graph-norm versions (through the commuting property
  `d Π_T = Π_T d`, `Feec.FiniteElement.polyInterp_extDeriv`, `polyMinusInterp_extDeriv`) are
  proved on shape-regular simplices in `Feec.Models.StarShaped.PolySmoothing`.
* **Kernel lemma for `Π_T`** (`exists_formL2Sq_sub_polyMinusInterp_le_formGradL2Sq`): for
  `u ∈ P_rΛᵏ` and `Π_T` onto `P_{r'}⁻Λᵏ(T)`, `r' ≤ r`, `‖u - Π_T u‖_{L²(T)} ≤ C h ‖Du‖_{L²(T)}`,
  from `Feec.FiniteElement.exists_local_kernel_bound` and naturality: the first estimate of
  [QuennevilleBelair2015], Prop 5.9 (case `P_2Λ¹ ≅ P_2Λ⁰ ⊗ ℝ³ → P_1⁻Λ¹`), with the scaling in `h`
  made explicit. The second estimate of Prop 5.9, `(I - Π²_T) vskw v` bounded by `h` times the
  `H(curl)` seminorm, cannot hold if the seminorm is `‖curl v‖` (as in its proof): for `v = grad (0, 0, x₁x₂)` (rows
  `∂_jφ_i`), `curl v = 0` row-wise while `vskw v = (x₁/2, -x₂/2, 0)` is linear and not of the
  form `a + b x`, so it is not in `P_1⁻Λ²` and `(I - Π²_T) vskw v ≠ 0`. Only the version with
  the full seminorm `‖Dv‖` follows from the kernel lemma.
* **Degrees of freedom of the global families** (`Feec.FiniteElement.PolySeq`, faces with
  lexicographically ordered vertices): a homothety `H y = t + h y` with `h > 0` preserves the
  lexicographic order (`strictMono_toLex_affine_scalarMat`), so the DOF `ℓ_{H(g),i}` on
  `T = t + h K` is `ℓ_{g,i} ∘ H^*` (`PolySeq.sum_dof_mapEquiv_boxMap`) and the estimates of
  `Feec.FiniteElement.PolyInverseEstimate` apply with the unisolvence `PolySeq.isUnisolvent_dof`
  on `K`: `hᵏ sup_T ‖u‖ ≤ B Σ |ℓ_{g,i}(u)|` (`PolySeq.exists_local_dof_bound`) and
  `‖u‖²_{L²(T)} ≍ h^{n-2k} Σ ℓ_{g,i}(u)²` (`PolySeq.exists_local_formL2Sq_equiv`).
* **Finitely many reference simplices** (`PolySeq.exists_local_dof_bound_uniform`): the
  constants can be taken uniform over a finite family `K_σ` (the Kuhn simplices of a Freudenthal
  mesh).

The estimates are local (one simplex); the mesh-level statements are assembled from them on the
Freudenthal–Kuhn meshes, whose simplices are homothetic copies `t + h K_σ` of finitely many
reference simplices. As in `Feec.FiniteElement.InterpolationError`, all seminorms are suprema of
iterated Fréchet derivatives (no Sobolev spaces).

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (approximation
  estimates)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], Thm 3.1.4
  (interpolation error for affine-equivalent families)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §4.5–4.9 (degrees of freedom, canonical interpolants, commuting property)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 5.9

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh

variable {n : ℕ}

/-! ### Naturality of the canonical interpolants under affine maps -/

section Naturality

variable {r k : ℕ}

theorem affinePullback_mem_contDegForms (A : Fin n → Fin n → ℝ) (a : Fin n → ℝ)
    {ω : FormField n} (hω : ω ∈ contDegForms n k) :
    affinePullback A a ω ∈ contDegForms n k :=
  ⟨continuous_affinePullback A a hω.1, fun x => IsDeg.affinePullback hω.2 A a x⟩

theorem mem_polySpace_of_mem_localPolySpace {p : Fin (n + 1) → Fin n → ℝ}
    (hp : IsUnit (edgeMatrix p).det) {ω : FormField n} (h : ω ∈ localPolySpace p r k) :
    ω ∈ polySpace n r k := by
  rwa [localPolySpace_eq hp] at h

theorem mem_polyMinusSpace_of_mem_localPolyMinusSpace {p : Fin (n + 1) → Fin n → ℝ}
    (hp : IsUnit (edgeMatrix p).det) {ω : FormField n} (h : ω ∈ localPolyMinusSpace p r k) :
    ω ∈ polyMinusSpace n r k := by
  rwa [localPolyMinusSpace_eq hp] at h

/-- **Naturality of the canonical interpolant of `P_rΛᵏ` under affine maps**: if
`q = G ∘ p` (`G y = A y + a`) for two nondegenerate simplices, then
`G^* (Π_q ω) = Π_p (G^* ω)`. The DOFs of `ω` on `q` are those of `G^* ω` on `p`
(`faceMoment_affine`), and unisolvence on `p` concludes. -/
theorem affinePullback_polyInterp {p q : Fin (n + 1) → Fin n → ℝ}
    (hp : IsUnit (edgeMatrix p).det) (hq : IsUnit (edgeMatrix q).det) (A : Fin n → Fin n → ℝ)
    (a : Fin n → ℝ) (hpq : q = fun i => affine A a (p i)) (hr : 1 ≤ r) (hk : k ≤ n)
    (ω : contDegForms n k) :
    affinePullback A a (polyInterp hq hr hk ω : FormField n) =
      (polyInterp hp hr hk ⟨affinePullback A a ω, affinePullback_mem_contDegForms A a ω.2⟩ :
        FormField n) := by
  have hmem : affinePullback A a (polyInterp hq hr hk ω : FormField n) ∈ localPolySpace p r k := by
    rw [localPolySpace_eq hp]
    exact affinePullback_mem_polySpace A a
      (mem_polySpace_of_mem_localPolySpace hq (polyInterp hq hr hk ω).2)
  have h := (isUnisolvent_localDof hp hr hk).ext (p := ⟨_, hmem⟩)
    (q := polyInterp hp hr hk ⟨affinePullback A a ω, affinePullback_mem_contDegForms A a ω.2⟩)
    fun i => by
      rw [localDof_polyInterp, localDof_apply]
      have e1 := localDof_polyInterp hq hr hk ω i
      rw [localDof_apply] at e1
      change faceMoment p i.1.emb _ (affinePullback A a _) =
        faceMoment p i.1.emb _ (affinePullback A a ω)
      rw [← faceMoment_affine, ← faceMoment_affine, ← hpq]
      exact e1
  exact congrArg Subtype.val h

/-- **Naturality of the canonical interpolant of `P_r⁻Λᵏ` under affine maps**. -/
theorem affinePullback_polyMinusInterp {p q : Fin (n + 1) → Fin n → ℝ}
    (hp : IsUnit (edgeMatrix p).det) (hq : IsUnit (edgeMatrix q).det) (A : Fin n → Fin n → ℝ)
    (a : Fin n → ℝ) (hpq : q = fun i => affine A a (p i)) (hr : 1 ≤ r) (hk : k ≤ n)
    (ω : contDegForms n k) :
    affinePullback A a (polyMinusInterp hq hr hk ω : FormField n) =
      (polyMinusInterp hp hr hk
        ⟨affinePullback A a ω, affinePullback_mem_contDegForms A a ω.2⟩ : FormField n) := by
  have hmem : affinePullback A a (polyMinusInterp hq hr hk ω : FormField n) ∈
      localPolyMinusSpace p r k := by
    rw [localPolyMinusSpace_eq hp]
    exact affinePullback_mem_polyMinusSpace A a
      (mem_polyMinusSpace_of_mem_localPolyMinusSpace hq (polyMinusInterp hq hr hk ω).2)
  have h := (isUnisolvent_localDofMinus hp hr hk).ext (p := ⟨_, hmem⟩)
    (q := polyMinusInterp hp hr hk
      ⟨affinePullback A a ω, affinePullback_mem_contDegForms A a ω.2⟩)
    fun i => by
      rw [show localDofMinus p r k i (polyMinusInterp hp hr hk _) = _ from
        dof_interp _ _ _ i, localDofMinus_apply]
      have e1 : localDofMinus q r k i (polyMinusInterp hq hr hk ω) = _ := dof_interp _ _ ω i
      rw [localDofMinus_apply] at e1
      change faceMoment p i.1.emb _ (affinePullback A a _) =
        faceMoment p i.1.emb _ (affinePullback A a ω)
      rw [← faceMoment_affine, ← faceMoment_affine, ← hpq]
      exact e1
  exact congrArg Subtype.val h

end Naturality

/-! ### Moments of fields that are only continuous on the reference simplex -/

section Moments

theorem continuousOn_faceTrace_apply {m : ℕ} (p : Fin (n + 1) → Fin n → ℝ)
    (e : Fin (m + 1) → Fin (n + 1)) {F : FormField n}
    (hF : ContinuousOn F (simplexMap (p ∘ e) '' refSimplex m)) (s : Finset (Fin m)) :
    ContinuousOn (fun x => faceTrace p e F x s) (refSimplex m) := by
  simp only [faceTrace_apply, affinePullback_apply, pullback_apply]
  refine continuousOn_finsetSum _ fun t _ => ContinuousOn.mul ?_ continuousOn_const
  exact (continuous_apply t).comp_continuousOn
    (hF.comp (continuous_simplexMap (p ∘ e)).continuousOn (Set.mapsTo_image _ _))

theorem continuousOn_wedgeField_faceTrace {m : ℕ} (p : Fin (n + 1) → Fin n → ℝ)
    (e : Fin (m + 1) → Fin (n + 1)) {F : FormField n}
    (hF : ContinuousOn F (simplexMap (p ∘ e) '' refSimplex m)) {η : FormField m}
    (hη : Continuous η) (u : Finset (Fin m)) :
    ContinuousOn (fun x => wedgeField (faceTrace p e F) η x u) (refSimplex m) := by
  simp only [wedgeField, wedgeForm_apply]
  exact continuousOn_finsetSum _ fun s _ =>
    (continuousOn_const.mul (continuousOn_faceTrace_apply p e hF s)).mul
      ((continuous_apply _).comp hη).continuousOn

/-- Additivity of a moment on fields continuous on the face. -/
theorem faceMoment_sub_of_continuousOn {m : ℕ} (p : Fin (n + 1) → Fin n → ℝ)
    (e : Fin (m + 1) → Fin (n + 1)) {η : FormField m} (hη : Continuous η) {F G : FormField n}
    (hF : ContinuousOn F (simplexMap (p ∘ e) '' refSimplex m))
    (hG : ContinuousOn G (simplexMap (p ∘ e) '' refSimplex m)) :
    faceMoment p e η (F - G) = faceMoment p e η F - faceMoment p e η G := by
  simp only [faceMoment_eq_integral]
  rw [← integral_sub ((continuousOn_wedgeField_faceTrace p e hF hη univ).integrableOn_compact
    (isCompact_refSimplex m))
    ((continuousOn_wedgeField_faceTrace p e hG hη univ).integrableOn_compact
    (isCompact_refSimplex m))]
  congr 1
  funext x
  simp only [wedgeField, wedgeForm_apply, map_sub, Pi.sub_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib]

theorem wedgeForm_pullback_apply {m : ℕ} (B : Fin n → Fin m → ℝ) (α : Finset (Fin n) → ℝ)
    (β : Finset (Fin m) → ℝ) (u : Finset (Fin m)) :
    wedgeForm (pullback B α) β u = ∑ t, α t * wedgeForm (wedgeProd B t) β u := by
  simp only [wedgeForm_apply, pullback_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring

/-- **Stability of a moment in the sup norm**: `|∫_f tr F ∧ η| ≤ c sup_f ‖F‖`, with `c`
depending only on the face and on `η`; `F` need not be continuous. -/
theorem exists_abs_faceMoment_le {m : ℕ} (p : Fin (n + 1) → Fin n → ℝ)
    (e : Fin (m + 1) → Fin (n + 1)) {η : FormField m} (hη : Continuous η) :
    ∃ c, 0 ≤ c ∧ ∀ (F : FormField n) (B₀ : ℝ),
      (∀ x ∈ refSimplex m, ‖F (simplexMap (p ∘ e) x)‖ ≤ B₀) →
        |faceMoment p e η F| ≤ c * B₀ := by
  set W := simplexMatrix (p ∘ e)
  have hc : Continuous fun x => ∑ t, |wedgeForm (wedgeProd W t) (η x) univ| := by
    refine continuous_finsetSum _ fun t _ => continuous_abs.comp ?_
    simp only [wedgeForm_apply]
    exact continuous_finsetSum _ fun s _ => continuous_const.mul ((continuous_apply _).comp hη)
  obtain ⟨M, hM⟩ := (isCompact_refSimplex m).exists_bound_of_continuousOn hc.continuousOn
  set M' := max M 0
  refine ⟨M' * volume.real (refSimplex m), mul_nonneg (le_max_right _ _) measureReal_nonneg,
    fun F B₀ hF => ?_⟩
  rw [faceMoment_eq_integral, ← Real.norm_eq_abs]
  have hB : ∀ x ∈ refSimplex m, ‖wedgeField (faceTrace p e F) η x univ‖ ≤ M' * B₀ := by
    intro x hx
    have hB₀ : 0 ≤ B₀ := (norm_nonneg _).trans (hF x hx)
    simp only [wedgeField, faceTrace_apply, affinePullback_apply]
    rw [wedgeForm_pullback_apply, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ t, |F (affine W ((p ∘ e) 0) x) t * wedgeForm (wedgeProd W t) (η x) univ|
        ≤ ∑ t, B₀ * |wedgeForm (wedgeProd W t) (η x) univ| := by
          refine Finset.sum_le_sum fun t _ => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          have := (norm_le_pi_norm (F (simplexMap (p ∘ e) x)) t).trans (hF x hx)
          rwa [Real.norm_eq_abs] at this
      _ = B₀ * ∑ t, |wedgeForm (wedgeProd W t) (η x) univ| := by rw [Finset.mul_sum]
      _ ≤ B₀ * M' := by
          refine mul_le_mul_of_nonneg_left ?_ hB₀
          have := hM x hx
          rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at this
          exact this.trans (le_max_left _ _)
      _ = M' * B₀ := mul_comm _ _
  refine (norm_setIntegral_le_of_norm_le_const (volume_refSimplex_lt_top m) hB).trans ?_
  rw [mul_right_comm]

end Moments

/-! ### Reference interpolants in all form degrees -/

section RefInterp

/-- The **degree-`k` part** of a field, `x ↦ Σ_{#s = k} g(x)_s dx_s`. -/
def degPartField (k : ℕ) (g : (Fin n → ℝ) → Finset (Fin n) → ℝ) : FormField n :=
  fun y => degPart k (g y)

theorem norm_degPart_le (k : ℕ) (α : Finset (Fin n) → ℝ) : ‖degPart k α‖ ≤ ‖α‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun t => ?_
  by_cases ht : #t = k
  · rw [degPart_of_card _ ht]; exact norm_le_pi_norm α t
  · simp [degPart, ht]

theorem degPartField_sub (k : ℕ) (f g : (Fin n → ℝ) → Finset (Fin n) → ℝ) :
    degPartField k (f - g) = degPartField k f - degPartField k g := by
  funext y t; simp only [degPartField, degPart, Pi.sub_apply]; split_ifs <;> simp

theorem degPartField_smul (k : ℕ) (c : ℝ) (g : (Fin n → ℝ) → Finset (Fin n) → ℝ) :
    degPartField k (c • g) = c • degPartField k g := by
  funext y t; simp only [degPartField, degPart, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

theorem degPartField_of_isDeg {k : ℕ} {g : FormField n} (hg : ∀ x, IsDeg k (g x)) :
    degPartField k g = g := by
  funext y t
  by_cases ht : #t = k
  · exact degPart_of_card _ ht
  · simp [degPartField, degPart, ht, hg y t ht]

theorem degPartField_of_isDeg_ne {j k : ℕ} (hjk : j ≠ k) {g : FormField n}
    (hg : ∀ x, IsDeg k (g x)) : degPartField j g = 0 := by
  funext y t
  by_cases ht : #t = j
  · simp [degPartField, degPart, ht, hg y t (by omega)]
  · simp [degPartField, degPart, ht]

theorem sum_degPart (α : Finset (Fin n) → ℝ) :
    ∑ k : Fin (n + 1), degPart k α = α := by
  funext t
  rw [Finset.sum_apply]
  have ht : #t < n + 1 := by have := Finset.card_le_univ t; rw [Fintype.card_fin] at this; omega
  rw [Finset.sum_eq_single ⟨#t, ht⟩ (fun k _ hk => by
      have : #t ≠ (k : ℕ) := fun h => hk (Fin.ext h.symm)
      simp [degPart, this]) (by simp)]
  exact degPart_of_card _ rfl

/-- The **reference interpolant assembled from moment DOFs** in all form degrees on `T̂`: for
each degree `k`, DOFs `g ↦ ∫_{f_{k,i}} tr (g)_k ∧ η_{k,i}` on faces `f_{k,i}` of `T̂` with test
forms `η_{k,i}`, and shape functions `φ_{k,i}`:
`I g = Σ_k Σ_i (∫_{f_{k,i}} tr (g)_k ∧ η_{k,i}) φ_{k,i}`. -/
def momentRefInterp {ι : Fin (n + 1) → Type*} [∀ k, Fintype (ι k)] (face : ∀ k, ι k → Face n)
    (η : ∀ k (i : ι k), FormField (face k i).dim) (φ : ∀ k, ι k → FormField n)
    (g : (Fin n → ℝ) → Finset (Fin n) → ℝ) (x : Fin n → ℝ) : Finset (Fin n) → ℝ :=
  ∑ k, ∑ i, faceMoment (refVertex n) (face k i).emb (η k i) (degPartField k g) • φ k i x

variable {ι : Fin (n + 1) → Type*} [∀ k, Fintype (ι k)] {face : ∀ k, ι k → Face n}
  {η : ∀ k (i : ι k), FormField (face k i).dim} {φ : ∀ k, ι k → FormField n}

theorem simplexMap_mem_closedInterior_refSimplex {m : ℕ} (e : Fin (m + 1) → Fin (n + 1))
    {x : Fin m → ℝ} (hx : x ∈ refSimplex m) :
    simplexMap (refVertex n ∘ e) x ∈ (Feec.Mesh.refSimplex n).closedInterior := by
  rw [← Affine.Simplex.convexHull_eq_closedInterior]
  exact convexHull_mono (Set.range_comp_subset_range _ _) (simplexMap_mem_convexHull _ hx)

theorem momentRefInterp_smul (c : ℝ) (g : (Fin n → ℝ) → Finset (Fin n) → ℝ) :
    momentRefInterp face η φ (c • g) = c • momentRefInterp face η φ g := by
  funext x
  simp only [momentRefInterp, degPartField_smul, faceMoment_smul_left, Finset.smul_sum,
    smul_smul, smul_eq_mul, Pi.smul_apply]

theorem momentRefInterp_sub (hη : ∀ k i, Continuous (η k i))
    {f g : (Fin n → ℝ) → Finset (Fin n) → ℝ}
    (hf : ContinuousOn f (Feec.Mesh.refSimplex n).closedInterior)
    (hg : ContinuousOn g (Feec.Mesh.refSimplex n).closedInterior) (x : Fin n → ℝ) :
    momentRefInterp face η φ (f - g) x =
      momentRefInterp face η φ f x - momentRefInterp face η φ g x := by
  simp only [momentRefInterp, ← Finset.sum_sub_distrib, ← sub_smul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  have hsub : simplexMap (refVertex n ∘ (face k i).emb) '' refSimplex (face k i).dim ⊆
      (Feec.Mesh.refSimplex n).closedInterior := by
    rintro _ ⟨y, hy, rfl⟩; exact simplexMap_mem_closedInterior_refSimplex _ hy
  have hcont : ∀ {F : (Fin n → ℝ) → Finset (Fin n) → ℝ},
      ContinuousOn F (Feec.Mesh.refSimplex n).closedInterior →
      ContinuousOn (degPartField k F) (simplexMap (refVertex n ∘ (face k i).emb) ''
        refSimplex (face k i).dim) := fun {F} hF => by
    refine continuousOn_pi.2 fun t => ?_
    simp only [degPartField, degPart]
    split_ifs
    · exact ((continuous_apply t).comp_continuousOn hF).mono hsub
    · exact continuousOn_const
  rw [degPartField_sub, faceMoment_sub_of_continuousOn _ _ (hη k i) (hcont hf) (hcont hg)]

/-- **Stability of a moment reference interpolant in `C⁰(T̂)`**: `sup_{T̂} ‖I g‖ ≤ C sup_{T̂} ‖g‖`
for continuous test forms and shape functions. -/
theorem exists_norm_momentRefInterp_le (hη : ∀ k i, Continuous (η k i))
    (hφ : ∀ k i, Continuous (φ k i)) :
    ∃ C, 0 ≤ C ∧ ∀ (g : (Fin n → ℝ) → Finset (Fin n) → ℝ) (B₀ : ℝ),
      (∀ y ∈ (Feec.Mesh.refSimplex n).closedInterior, ‖g y‖ ≤ B₀) →
      ∀ x ∈ (Feec.Mesh.refSimplex n).closedInterior, ‖momentRefInterp face η φ g x‖ ≤ C * B₀ := by
  choose c hc0 hc using fun k (i : ι k) =>
    exists_abs_faceMoment_le (refVertex n) (face k i).emb (hη k i)
  choose S hS using fun k (i : ι k) =>
    (Feec.Mesh.refSimplex n).isCompact_closedInterior.exists_bound_of_continuousOn
      (hφ k i).continuousOn
  refine ⟨∑ k, ∑ i, c k i * max (S k i) 0, Finset.sum_nonneg fun k _ => Finset.sum_nonneg
    fun i _ => mul_nonneg (hc0 k i) (le_max_right _ _), fun g B₀ hg x hx => ?_⟩
  have hB₀ : 0 ≤ B₀ := (norm_nonneg _).trans (hg x hx)
  rw [momentRefInterp, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  have h1 : |faceMoment (refVertex n) (face k i).emb (η k i) (degPartField k g)| ≤ c k i * B₀ :=
    hc k i _ B₀ fun y hy => (norm_degPart_le _ _).trans
      (hg _ (simplexMap_mem_closedInterior_refSimplex _ hy))
  calc |faceMoment (refVertex n) (face k i).emb (η k i) (degPartField k g)| * ‖φ k i x‖
      ≤ (c k i * B₀) * max (S k i) 0 :=
        mul_le_mul h1 ((hS k i x hx).trans (le_max_left _ _)) (norm_nonneg _)
          (mul_nonneg (hc0 k i) hB₀)
    _ = c k i * max (S k i) 0 * B₀ := by ring

/-- A moment reference interpolant with continuous test forms and shape functions that reproduces
`P_s(ℝⁿ; Λ)` (all form degrees) is a reference interpolant of order `s` with stability order
`m = 0` (`Feec.FiniteElement.IsRefInterpolant`). -/
theorem exists_isRefInterpolant_momentRefInterp {s : ℕ} (hη : ∀ k i, Continuous (η k i))
    (hφ : ∀ k i, Continuous (φ k i))
    (hrep : ∀ p ∈ polyFunctions n s (Finset (Fin n) → ℝ), ∀ x,
      momentRefInterp face η φ p x = p x) :
    ∃ C, 0 ≤ C ∧
      IsRefInterpolant n s 0 (Finset (Fin n) → ℝ) (momentRefInterp face η φ) C := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_momentRefInterp_le hη hφ
  refine ⟨C, hC0, ⟨Nat.zero_le _, fun V _ hTV f g hf hg x _ =>
    momentRefInterp_sub hη (hf.continuousOn.mono hTV) (hg.continuousOn.mono hTV) x,
    fun p hp x _ => hrep p hp x, fun V _ _ g _ B hB x hx => ?_⟩⟩
  rw [Finset.sum_range_one]
  exact hC g (B 0) (fun y hy => by simpa using hB 0 le_rfl y hy) x hx

end RefInterp

/-! ### The reference interpolants of `P_rΛ` and `P_r⁻Λ` -/

section PolyRef

variable {r : ℕ}

theorem val_le_of_fin_succ (k : Fin (n + 1)) : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2

/-- The canonical interpolant as a combination of a dual basis: `Π y = Σᵢ mᵢ(y) φᵢ`,
`φᵢ = (ℓ-coordinates)⁻¹(eᵢ)`. -/
theorem interp_eq_sum_smul {P Y ι : Type*} [AddCommGroup P] [Module ℝ P] [AddCommGroup Y]
    [Module ℝ Y] [Fintype ι] [DecidableEq ι] {ℓ : ι → P →ₗ[ℝ] ℝ} (hℓ : IsUnisolvent ℓ)
    (m : ι → Y →ₗ[ℝ] ℝ) (y : Y) :
    interp hℓ m y = ∑ i, m i y • hℓ.equiv.symm (Pi.single i 1) := by
  have h : LinearMap.pi m y = ∑ i, m i y • (Pi.single i 1 : ι → ℝ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [interp, LinearMap.comp_apply, h, map_sum]
  simp only [map_smul, LinearEquiv.coe_coe]

/-- The dual basis of the DOFs of `P_rΛᵏ(T̂)`. -/
def polyDualBasis (hr : 1 ≤ r) {k : ℕ} (hk : k ≤ n) (i : Σ f : Face n, DofIndex r k f) :
    FormField n :=
  ((isUnisolvent_localDof (isUnit_det_edgeMatrix_refVertex (n := n)) hr hk).equiv.symm
    (Pi.single i 1) : FormField n)

/-- The dual basis of the DOFs of `P_r⁻Λᵏ(T̂)`. -/
def polyMinusDualBasis (hr : 1 ≤ r) {k : ℕ} (hk : k ≤ n)
    (i : Σ f : Face n, DofIndexMinus r k f) : FormField n :=
  ((isUnisolvent_localDofMinus (isUnit_det_edgeMatrix_refVertex (n := n)) hr hk).equiv.symm
    (Pi.single i 1) : FormField n)

theorem continuous_polyDualBasis (hr : 1 ≤ r) {k : ℕ} (hk : k ≤ n)
    (i : Σ f : Face n, DofIndex r k f) : Continuous (polyDualBasis hr hk i) :=
  localPolySpace_le_contForms _ r k
    ((isUnisolvent_localDof (isUnit_det_edgeMatrix_refVertex (n := n)) hr hk).equiv.symm
      (Pi.single i 1)).2

theorem continuous_polyMinusDualBasis (hr : 1 ≤ r) {k : ℕ} (hk : k ≤ n)
    (i : Σ f : Face n, DofIndexMinus r k f) : Continuous (polyMinusDualBasis hr hk i) :=
  localPolyMinusSpace_le_contForms _ r k
    ((isUnisolvent_localDofMinus (isUnit_det_edgeMatrix_refVertex (n := n)) hr hk).equiv.symm
      (Pi.single i 1)).2

theorem polyInterp_refVertex_eq_sum (hr : 1 ≤ r) {k : ℕ} (hk : k ≤ n) (ω : contDegForms n k) :
    (polyInterp (isUnit_det_edgeMatrix_refVertex (n := n)) hr hk ω : FormField n) =
      ∑ i, faceMoment (refVertex n) i.1.emb (testBasis r k i.1.dim i.2 : FormField i.1.dim) ω •
        polyDualBasis hr hk i := by
  rw [polyInterp, interp_eq_sum_smul, Submodule.coe_sum]
  rfl

theorem polyMinusInterp_refVertex_eq_sum (hr : 1 ≤ r) {k : ℕ} (hk : k ≤ n)
    (ω : contDegForms n k) :
    (polyMinusInterp (isUnit_det_edgeMatrix_refVertex (n := n)) hr hk ω : FormField n) =
      ∑ i, faceMoment (refVertex n) i.1.emb
        (testBasisMinus r k i.1.dim i.2 : FormField i.1.dim) ω • polyMinusDualBasis hr hk i := by
  rw [polyMinusInterp, interp_eq_sum_smul, Submodule.coe_sum]
  rfl

/-- **The reference interpolant of the `P_rΛ` family on `T̂`**, in all form degrees:
`I g = Σ_k Π_{T̂}^{P_rΛᵏ} (g)_k`, with the moment DOFs of `Feec.FiniteElement.localDof`. -/
def polyRefInterp (hr : 1 ≤ r) :
    ((Fin n → ℝ) → Finset (Fin n) → ℝ) → (Fin n → ℝ) → Finset (Fin n) → ℝ :=
  momentRefInterp (ι := fun k => Σ f : Face n, DofIndex r k f) (fun _ i => i.1)
    (fun k i => (testBasis r k i.1.dim i.2 : FormField i.1.dim))
    (fun k i => polyDualBasis hr (val_le_of_fin_succ k) i)

/-- **The reference interpolant of the `P_r⁻Λ` family on `T̂`**, in all form degrees. -/
def polyMinusRefInterp (hr : 1 ≤ r) :
    ((Fin n → ℝ) → Finset (Fin n) → ℝ) → (Fin n → ℝ) → Finset (Fin n) → ℝ :=
  momentRefInterp (ι := fun k => Σ f : Face n, DofIndexMinus r k f) (fun _ i => i.1)
    (fun k i => (testBasisMinus r k i.1.dim i.2 : FormField i.1.dim))
    (fun k i => polyMinusDualBasis hr (val_le_of_fin_succ k) i)

theorem faceMoment_zero {m : ℕ} (p : Fin (n + 1) → Fin n → ℝ) (e : Fin (m + 1) → Fin (n + 1))
    (η : FormField m) : faceMoment p e η 0 = 0 := by
  have h := faceMoment_smul_left p e η 0 0
  simpa using h

/-- On continuous `k`-forms the reference interpolant is the canonical interpolant `Π_{T̂}` of
`P_rΛᵏ(T̂)`. -/
theorem polyRefInterp_eq_polyInterp (hr : 1 ≤ r) {k : ℕ} (hk : k ≤ n) (ω : contDegForms n k) :
    polyRefInterp hr ω =
      (polyInterp (isUnit_det_edgeMatrix_refVertex (n := n)) hr hk ω : FormField n) := by
  funext x
  rw [polyInterp_refVertex_eq_sum, polyRefInterp, momentRefInterp,
    Finset.sum_eq_single (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n + 1))]
  · rw [degPartField_of_isDeg ω.2.2, Finset.sum_apply]
    rfl
  · intro j _ hj
    have hjk : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
    rw [degPartField_of_isDeg_ne hjk ω.2.2]
    simp [faceMoment_zero]
  · simp

theorem polyMinusRefInterp_eq_polyMinusInterp (hr : 1 ≤ r) {k : ℕ} (hk : k ≤ n)
    (ω : contDegForms n k) :
    polyMinusRefInterp hr ω =
      (polyMinusInterp (isUnit_det_edgeMatrix_refVertex (n := n)) hr hk ω : FormField n) := by
  funext x
  rw [polyMinusInterp_refVertex_eq_sum, polyMinusRefInterp, momentRefInterp,
    Finset.sum_eq_single (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n + 1))]
  · rw [degPartField_of_isDeg ω.2.2, Finset.sum_apply]
    rfl
  · intro j _ hj
    have hjk : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
    rw [degPartField_of_isDeg_ne hjk ω.2.2]
    simp [faceMoment_zero]
  · simp

theorem degPartField_add (k : ℕ) (f g : (Fin n → ℝ) → Finset (Fin n) → ℝ) :
    degPartField k (f + g) = degPartField k f + degPartField k g := by
  funext y t; simp only [degPartField, degPart, Pi.add_apply]; split_ifs <;> simp

theorem polySpace_mono {s r k : ℕ} (h : s ≤ r) : polySpace n s k ≤ polySpace n r k := by
  rintro _ ⟨Ω, hΩ, rfl⟩
  exact ⟨Ω, ⟨hΩ.1, fun t => (hΩ.2 t).trans h⟩, rfl⟩

/-- The degree-`k` part of a polynomial of degree `≤ s` with values in `Λ(ℝⁿ)` is in
`P_sΛᵏ`. -/
theorem degPartField_mem_polySpace {s : ℕ} {p : (Fin n → ℝ) → Finset (Fin n) → ℝ}
    (hp : p ∈ polyFunctions n s (Finset (Fin n) → ℝ)) (k : ℕ) :
    degPartField k p ∈ polySpace n s k := by
  induction hp using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨q, hq, c, rfl⟩ := hg
    refine ⟨fun t => if #t = k then MvPolynomial.C (c t) * q else 0, ⟨fun t ht => by simp [ht],
      fun t => ?_⟩, ?_⟩
    · dsimp only
      split_ifs
      · exact (MvPolynomial.totalDegree_mul _ _).trans (by
          rw [MvPolynomial.totalDegree_C, zero_add]; exact hq)
      · simp
    · funext y t
      simp only [evalForm_apply, degPartField, degPart, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp [mul_comm]
  | zero =>
    have : degPartField k (0 : (Fin n → ℝ) → Finset (Fin n) → ℝ) = 0 := by
      funext y t; simp [degPartField, degPart]
    rw [this]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [degPartField_add]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf => rw [degPartField_smul]; exact Submodule.smul_mem _ c hf

/-- **`I` reproduces `P_s(ℝⁿ; Λ)` for `s ≤ r`** (the `P_rΛ` family). -/
theorem polyRefInterp_apply_eq (hr : 1 ≤ r) {s : ℕ} (hs : s ≤ r)
    {p : (Fin n → ℝ) → Finset (Fin n) → ℝ} (hp : p ∈ polyFunctions n s (Finset (Fin n) → ℝ))
    (x : Fin n → ℝ) : polyRefInterp hr p x = p x := by
  have hk : ∀ k : Fin (n + 1), degPartField k p ∈ localPolySpace (refVertex n) r k := fun k => by
    rw [localPolySpace_eq isUnit_det_edgeMatrix_refVertex]
    exact polySpace_mono hs (degPartField_mem_polySpace hp k)
  have h : ∀ k : Fin (n + 1), ∑ i : Σ f : Face n, DofIndex r k f,
      faceMoment (refVertex n) i.1.emb (testBasis r k i.1.dim i.2 : FormField i.1.dim)
        (degPartField k p) • polyDualBasis hr (val_le_of_fin_succ k) i x =
      degPart k (p x) := fun k => by
    have e := polyInterp_inclusion (isUnit_det_edgeMatrix_refVertex (n := n)) hr
      (val_le_of_fin_succ k) ⟨_, hk k⟩
    have e2 := congrArg (fun ω : localPolySpace (refVertex n) r k => (ω : FormField n) x) e
    simp only at e2
    rw [polyInterp_refVertex_eq_sum, Finset.sum_apply] at e2
    exact e2
  rw [polyRefInterp, momentRefInterp, Finset.sum_congr rfl fun k _ => h k]
  exact sum_degPart (p x)

/-- **`I` reproduces `P_s(ℝⁿ; Λ)` for `s + 1 ≤ r`** (the `P_r⁻Λ` family). -/
theorem polyMinusRefInterp_apply_eq (hr : 1 ≤ r) {s : ℕ} (hs : s + 1 ≤ r)
    {p : (Fin n → ℝ) → Finset (Fin n) → ℝ} (hp : p ∈ polyFunctions n s (Finset (Fin n) → ℝ))
    (x : Fin n → ℝ) : polyMinusRefInterp hr p x = p x := by
  have hk : ∀ k : Fin (n + 1), degPartField k p ∈ localPolyMinusSpace (refVertex n) r k :=
    fun k => by
      rw [localPolyMinusSpace_eq isUnit_det_edgeMatrix_refVertex]
      exact polySpace_le_polyMinusSpace hr k
        (polySpace_mono (by omega) (degPartField_mem_polySpace hp k))
  have h : ∀ k : Fin (n + 1), ∑ i : Σ f : Face n, DofIndexMinus r k f,
      faceMoment (refVertex n) i.1.emb (testBasisMinus r k i.1.dim i.2 : FormField i.1.dim)
        (degPartField k p) • polyMinusDualBasis hr (val_le_of_fin_succ k) i x =
      degPart k (p x) := fun k => by
    have e := polyMinusInterp_inclusion (isUnit_det_edgeMatrix_refVertex (n := n)) hr
      (val_le_of_fin_succ k) ⟨_, hk k⟩
    have e2 := congrArg (fun ω : localPolyMinusSpace (refVertex n) r k => (ω : FormField n) x) e
    simp only at e2
    rw [polyMinusInterp_refVertex_eq_sum, Finset.sum_apply] at e2
    exact e2
  rw [polyMinusRefInterp, momentRefInterp, Finset.sum_congr rfl fun k _ => h k]
  exact sum_degPart (p x)

/-- **The canonical interpolant of `P_rΛ` is a reference interpolant** of every order `s ≤ r`
(`IsRefInterpolant n s 0`): it reproduces `P_s`, and it is stable in `C⁰(T̂)` since its moment
DOFs only need values ([Ciarlet2002], Thm 3.1.4; [AFW2010], §5.2). -/
theorem exists_isRefInterpolant_polyRefInterp (hr : 1 ≤ r) {s : ℕ} (hs : s ≤ r) :
    ∃ C, 0 ≤ C ∧ IsRefInterpolant n s 0 (Finset (Fin n) → ℝ) (polyRefInterp hr) C :=
  exists_isRefInterpolant_momentRefInterp
    (fun k i => (contDiff_of_mem_testSpace (testBasis r k _ i.2).2).continuous)
    (fun _ i => continuous_polyDualBasis hr _ i)
    fun _ hp x => polyRefInterp_apply_eq hr hs hp x

/-- **The canonical interpolant of `P_r⁻Λ` is a reference interpolant** of every order
`s ≤ r - 1`. -/
theorem exists_isRefInterpolant_polyMinusRefInterp (hr : 1 ≤ r) {s : ℕ} (hs : s + 1 ≤ r) :
    ∃ C, 0 ≤ C ∧ IsRefInterpolant n s 0 (Finset (Fin n) → ℝ) (polyMinusRefInterp hr) C :=
  exists_isRefInterpolant_momentRefInterp
    (fun k i => (contDiff_of_mem_testSpaceMinus (testBasisMinus r k _ i.2).2).continuous)
    (fun _ i => continuous_polyMinusDualBasis hr _ i)
    fun _ hp x => polyMinusRefInterp_apply_eq hr hs hp x

theorem polyRefInterp_smul (hr : 1 ≤ r) (c : ℝ) (g : (Fin n → ℝ) → Finset (Fin n) → ℝ) :
    polyRefInterp hr (c • g) = c • polyRefInterp hr g :=
  momentRefInterp_smul c g

theorem polyMinusRefInterp_smul (hr : 1 ≤ r) (c : ℝ) (g : (Fin n → ℝ) → Finset (Fin n) → ℝ) :
    polyMinusRefInterp hr (c • g) = c • polyMinusRefInterp hr g :=
  momentRefInterp_smul c g

end PolyRef

/-! ### Transport to homothetic simplices -/

section Transport

variable {r k : ℕ}

/-- The fibre pullback `α ↦ B_p^* α` by the edge matrix of a nondegenerate simplex, as a
continuous linear equivalence of `Λ(ℝⁿ)` (all degrees). -/
def fibrePullbackEquiv (p : Fin (n + 1) → Fin n → ℝ) (hp : IsUnit (edgeMatrix p).det) :
    (Finset (Fin n) → ℝ) ≃L[ℝ] (Finset (Fin n) → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := pullback (simplexMatrix p)
      invFun := pullback (invMatrix p)
      map_add' := pullback_add _
      map_smul' := pullback_smul _
      left_inv := fun α => by
        have h := affinePullback_affinePullback_of_comp_eq_id (simplexMatrix p) (p 0)
          (invMatrix p) (invOffset p) (simplexMap_affine_inv hp) (fun _ => α)
        exact congrFun h 0
      right_inv := fun β => by
        have h := affinePullback_affinePullback_of_comp_eq_id (invMatrix p) (invOffset p)
          (simplexMatrix p) (p 0) (affine_inv_simplexMap hp) (fun _ => β)
        exact congrFun h 0 }

theorem fibrePullbackEquiv_apply (p : Fin (n + 1) → Fin n → ℝ)
    (hp : IsUnit (edgeMatrix p).det) (α : Finset (Fin n) → ℝ) :
    fibrePullbackEquiv p hp α = pullback (simplexMatrix p) α := rfl

theorem simplexMatrix_points_mapEquiv_boxMap (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    (t : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) :
    simplexMatrix (mapEquiv (boxMap t h hh) K).points = h • simplexMatrix K.points := by
  rw [points_mapEquiv_boxMap, simplexMatrix_comp_affine]
  funext i l
  simp [scalarMat]

theorem pullback_smul_matrix_of_isDeg {B : Fin n → Fin n → ℝ} (h : ℝ)
    {α : Finset (Fin n) → ℝ} (hα : IsDeg k α) :
    pullback (h • B) α = h ^ k • pullback B α := by
  simp only [pullback, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [wedgeProd_smul, smul_smul]
  by_cases hs : #s = k
  · rw [hs, mul_comm]
  · rw [hα s hs]; simp

/-- For `T = t + h K` and a `k`-form `w`, `F_T^* w = hᵏ (Φ_K ∘ w ∘ F_T)` with the fixed fibre map
`Φ_K = B_K^*` (`Feec.FiniteElement.refPullback`). -/
theorem affinePullback_points_mapEquiv_boxMap (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    (t : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) {w : FormField n} (hw : ∀ x, IsDeg k (w x)) :
    affinePullback (simplexMatrix (mapEquiv (boxMap t h hh) K).points)
        ((mapEquiv (boxMap t h hh) K).points 0) w =
      h ^ k • refPullback (mapEquiv (boxMap t h hh) K)
        (fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K)) w := by
  funext x
  rw [affinePullback_apply, simplexMatrix_points_mapEquiv_boxMap, pullback_smul_matrix_of_isDeg h
    (hw _), Pi.smul_apply, refPullback, fibrePullbackEquiv_apply]
  congr 2
  have := congrFun (simplexMap_eq_refMap (mapEquiv (boxMap t h hh) K)) x
  rw [← this, simplexMap, simplexMatrix_points_mapEquiv_boxMap]

theorem linearEquiv_mapEquiv_boxMap (K : Affine.Simplex ℝ (Fin n → ℝ) n) (t : Fin n → ℝ)
    {h : ℝ} (hh : h ≠ 0) :
    ((mapEquiv (boxMap t h hh) K).linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ) =
      h • (K.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ) := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearEquiv.coe_coe, Affine.Simplex.linearEquiv_apply,
    Affine.Simplex.linearPart_apply, smul_apply, mapEquiv_points,
    boxMap_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_sub_add_left_eq_sub, ← smul_sub, smul_comm]

theorem norm_linearEquiv_mapEquiv_boxMap (K : Affine.Simplex ℝ (Fin n → ℝ) n) (t : Fin n → ℝ)
    {h : ℝ} (hh : 0 < h) :
    ‖((mapEquiv (boxMap t h hh.ne') K).linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ =
      h * ‖(K.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ := by
  rw [linearEquiv_mapEquiv_boxMap, norm_smul, Real.norm_of_nonneg hh.le]

theorem mem_contDegForms {w : FormField n} (hwc : Continuous w) (hwk : ∀ x, IsDeg k (w x)) :
    w ∈ contDegForms n k := ⟨hwc, hwk⟩

/-- **The transported reference interpolant is the canonical interpolant** of `P_rΛᵏ(T)` on
`T = t + h K`: `Π_T w = Φ_K⁻¹ ∘ I (Φ_K ∘ w ∘ F_T) ∘ F_T⁻¹` (`Feec.FiniteElement.transportInterp`)
with the `h`-independent fibre map `Φ_K = B_K^*`. This is the naturality needed by
`Feec.FiniteElement.norm_sub_transportInterp_le`. -/
theorem transportInterp_polyRefInterp_eq (K : Affine.Simplex ℝ (Fin n → ℝ) n) (hr : 1 ≤ r)
    (hk : k ≤ n) {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {w : FormField n} (hwc : Continuous w)
    (hwk : ∀ x, IsDeg k (w x)) (x : Fin n → ℝ) :
    transportInterp (mapEquiv (boxMap t h hh.ne') K)
        (fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K)) (polyRefInterp hr) w x =
      (polyInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr hk
        ⟨w, mem_contDegForms hwc hwk⟩ : FormField n) x := by
  set T := mapEquiv (boxMap t h hh.ne') K
  set Φ := fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K)
  set P := (polyInterp (isUnit_det_edgeMatrix T) hr hk ⟨w, mem_contDegForms hwc hwk⟩ :
    FormField n)
  have hhk : h ^ k ≠ 0 := pow_ne_zero k hh.ne'
  have hPdeg : ∀ x, IsDeg k (P x) := isDeg_of_mem_polySpace
    (mem_polySpace_of_mem_localPolySpace (isUnit_det_edgeMatrix T)
      (polyInterp (isUnit_det_edgeMatrix T) hr hk ⟨w, mem_contDegForms hwc hwk⟩).2)
  have hrefw : refPullback T Φ w = (h ^ k)⁻¹ •
      affinePullback (simplexMatrix T.points) (T.points 0) w := by
    rw [affinePullback_points_mapEquiv_boxMap K t hh.ne' hwk, smul_smul, inv_mul_cancel₀ hhk,
      one_smul]
  have hrefP : refPullback T Φ P = (h ^ k)⁻¹ •
      affinePullback (simplexMatrix T.points) (T.points 0) P := by
    rw [affinePullback_points_mapEquiv_boxMap K t hh.ne' hPdeg, smul_smul, inv_mul_cancel₀ hhk,
      one_smul]
  have hnat := affinePullback_polyInterp (isUnit_det_edgeMatrix_refVertex (n := n))
    (isUnit_det_edgeMatrix T) (simplexMatrix T.points) (T.points 0)
    (funext fun i => (simplexMap_refVertex T.points i).symm) hr hk ⟨w, mem_contDegForms hwc hwk⟩
  have hid : polyRefInterp hr (affinePullback (simplexMatrix T.points) (T.points 0) w) =
      (polyInterp (isUnit_det_edgeMatrix_refVertex (n := n)) hr hk
        ⟨affinePullback (simplexMatrix T.points) (T.points 0) w,
          affinePullback_mem_contDegForms _ _ (mem_contDegForms hwc hwk)⟩ : FormField n) :=
    polyRefInterp_eq_polyInterp hr hk ⟨affinePullback (simplexMatrix T.points) (T.points 0) w,
      affinePullback_mem_contDegForms _ _ (mem_contDegForms hwc hwk)⟩
  have hI : polyRefInterp hr (refPullback T Φ w) = refPullback T Φ P := by
    rw [hrefw, polyRefInterp_smul, hid, ← hnat, hrefP]
  rw [transportInterp, hI, refPullback, refMap_refMapInv, ContinuousLinearEquiv.symm_apply_apply]

/-- The analogue of `transportInterp_polyRefInterp_eq` for `P_r⁻Λᵏ`. -/
theorem transportInterp_polyMinusRefInterp_eq (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    (hr : 1 ≤ r) (hk : k ≤ n) {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {w : FormField n}
    (hwc : Continuous w) (hwk : ∀ x, IsDeg k (w x)) (x : Fin n → ℝ) :
    transportInterp (mapEquiv (boxMap t h hh.ne') K)
        (fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K)) (polyMinusRefInterp hr) w x =
      (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr hk
        ⟨w, mem_contDegForms hwc hwk⟩ : FormField n) x := by
  set T := mapEquiv (boxMap t h hh.ne') K
  set Φ := fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K)
  set P := (polyMinusInterp (isUnit_det_edgeMatrix T) hr hk ⟨w, mem_contDegForms hwc hwk⟩ :
    FormField n)
  have hhk : h ^ k ≠ 0 := pow_ne_zero k hh.ne'
  have hPdeg : ∀ x, IsDeg k (P x) := isDeg_of_mem_polySpace (polyMinusSpace_le_polySpace hr
    (mem_polyMinusSpace_of_mem_localPolyMinusSpace (isUnit_det_edgeMatrix T)
      (polyMinusInterp (isUnit_det_edgeMatrix T) hr hk ⟨w, mem_contDegForms hwc hwk⟩).2))
  have hrefw : refPullback T Φ w = (h ^ k)⁻¹ •
      affinePullback (simplexMatrix T.points) (T.points 0) w := by
    rw [affinePullback_points_mapEquiv_boxMap K t hh.ne' hwk, smul_smul, inv_mul_cancel₀ hhk,
      one_smul]
  have hrefP : refPullback T Φ P = (h ^ k)⁻¹ •
      affinePullback (simplexMatrix T.points) (T.points 0) P := by
    rw [affinePullback_points_mapEquiv_boxMap K t hh.ne' hPdeg, smul_smul, inv_mul_cancel₀ hhk,
      one_smul]
  have hnat := affinePullback_polyMinusInterp (isUnit_det_edgeMatrix_refVertex (n := n))
    (isUnit_det_edgeMatrix T) (simplexMatrix T.points) (T.points 0)
    (funext fun i => (simplexMap_refVertex T.points i).symm) hr hk ⟨w, mem_contDegForms hwc hwk⟩
  have hid : polyMinusRefInterp hr (affinePullback (simplexMatrix T.points) (T.points 0) w) =
      (polyMinusInterp (isUnit_det_edgeMatrix_refVertex (n := n)) hr hk
        ⟨affinePullback (simplexMatrix T.points) (T.points 0) w,
          affinePullback_mem_contDegForms _ _ (mem_contDegForms hwc hwk)⟩ : FormField n) :=
    polyMinusRefInterp_eq_polyMinusInterp hr hk
      ⟨affinePullback (simplexMatrix T.points) (T.points 0) w,
      affinePullback_mem_contDegForms _ _ (mem_contDegForms hwc hwk)⟩
  have hI : polyMinusRefInterp hr (refPullback T Φ w) = refPullback T Φ P := by
    rw [hrefw, polyMinusRefInterp_smul, hid, ← hnat, hrefP]
  rw [transportInterp, hI, refPullback, refMap_refMapInv, ContinuousLinearEquiv.symm_apply_apply]

end Transport

/-! ### Interpolation error on homothetic simplices -/

section Error

variable {r k : ℕ}

/-- **Local interpolation error of the canonical interpolant of `P_rΛᵏ`** on `T = t + h K`
([Ciarlet2002], Thm 3.1.4; [Arnold2018], Ch. 7; the classical `C^{s+1}` form): for every
admissible order `s ≤ r` and every continuous `k`-form `w` of class `C^{s+1}` near `T`,
`sup_T ‖w - Π_T w‖ ≤ C h^{s+1} sup_T ‖D^{s+1} w‖`, with `C` depending only on `K`, `n`, `r`, `s`.
For `s = r` this is the full order `h^{r+1}`; `s = 0` is the `O(h)` estimate for `C¹` data. -/
theorem exists_norm_sub_polyInterp_le (K : Affine.Simplex ℝ (Fin n → ℝ) n) (hr : 1 ≤ r)
    (hk : k ≤ n) {s : ℕ} (hs : s ≤ r) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {w : FormField n} (hwc : Continuous w)
      (hwk : ∀ x, IsDeg k (w x)) {U : Set (Fin n → ℝ)}, IsOpen U →
      (mapEquiv (boxMap t h hh.ne') K).closedInterior ⊆ U → ContDiffOn ℝ (s + 1) w U →
      ∀ {M : ℝ}, (∀ y ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior,
        ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ M) →
      ∀ x ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior,
        ‖w x - (polyInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr hk
          ⟨w, mem_contDegForms hwc hwk⟩ : FormField n) x‖ ≤ C * h ^ (s + 1) * M := by
  obtain ⟨CI, hCI0, hI⟩ := exists_isRefInterpolant_polyRefInterp (n := n) hr hs
  set Φ := fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K)
  have hc : 0 ≤ 1 + CI * (((0 : ℕ) : ℝ) + 1) := by push_cast; linarith
  refine ⟨‖(Φ.symm : (Finset (Fin n) → ℝ) →L[ℝ] (Finset (Fin n) → ℝ))‖ *
      ((1 + CI * (((0 : ℕ) : ℝ) + 1)) *
      (‖(Φ : (Finset (Fin n) → ℝ) →L[ℝ] (Finset (Fin n) → ℝ))‖ *
        ‖(K.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (s + 1))),
    mul_nonneg (norm_nonneg _) (mul_nonneg hc (mul_nonneg (norm_nonneg _)
      (pow_nonneg (norm_nonneg _) _))),
    fun {h} hh t w hwc hwk U hU hTU hw M hM x hx => ?_⟩
  have h1 := norm_sub_transportInterp_le hI (mapEquiv (boxMap t h hh.ne') K) Φ hU hTU hw hM hx
  rw [transportInterp_polyRefInterp_eq K hr hk hh t hwc hwk,
    norm_linearEquiv_mapEquiv_boxMap K t hh] at h1
  refine h1.trans_eq ?_
  rw [mul_pow]
  ring

/-- **Local interpolation error of the canonical interpolant of `P_r⁻Λᵏ`** on `T = t + h K`:
for every admissible order `s ≤ r - 1`,
`sup_T ‖w - Π_T w‖ ≤ C h^{s+1} sup_T ‖D^{s+1} w‖`; the full order is `h^r` (`s = r - 1`), and
`s = 0` gives the `O(h)` estimate of the Whitney forms (`r = 1`). -/
theorem exists_norm_sub_polyMinusInterp_le (K : Affine.Simplex ℝ (Fin n → ℝ) n) (hr : 1 ≤ r)
    (hk : k ≤ n) {s : ℕ} (hs : s + 1 ≤ r) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {w : FormField n} (hwc : Continuous w)
      (hwk : ∀ x, IsDeg k (w x)) {U : Set (Fin n → ℝ)}, IsOpen U →
      (mapEquiv (boxMap t h hh.ne') K).closedInterior ⊆ U → ContDiffOn ℝ (s + 1) w U →
      ∀ {M : ℝ}, (∀ y ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior,
        ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ M) →
      ∀ x ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior,
        ‖w x - (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr hk
          ⟨w, mem_contDegForms hwc hwk⟩ : FormField n) x‖ ≤ C * h ^ (s + 1) * M := by
  obtain ⟨CI, hCI0, hI⟩ := exists_isRefInterpolant_polyMinusRefInterp (n := n) hr hs
  set Φ := fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K)
  have hc : 0 ≤ 1 + CI * (((0 : ℕ) : ℝ) + 1) := by push_cast; linarith
  refine ⟨‖(Φ.symm : (Finset (Fin n) → ℝ) →L[ℝ] (Finset (Fin n) → ℝ))‖ *
      ((1 + CI * (((0 : ℕ) : ℝ) + 1)) *
      (‖(Φ : (Finset (Fin n) → ℝ) →L[ℝ] (Finset (Fin n) → ℝ))‖ *
        ‖(K.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (s + 1))),
    mul_nonneg (norm_nonneg _) (mul_nonneg hc (mul_nonneg (norm_nonneg _)
      (pow_nonneg (norm_nonneg _) _))),
    fun {h} hh t w hwc hwk U hU hTU hw M hM x hx => ?_⟩
  have h1 := norm_sub_transportInterp_le hI (mapEquiv (boxMap t h hh.ne') K) Φ hU hTU hw hM hx
  rw [transportInterp_polyMinusRefInterp_eq K hr hk hh t hwc hwk,
    norm_linearEquiv_mapEquiv_boxMap K t hh] at h1
  refine h1.trans_eq ?_
  rw [mul_pow]
  ring

/-- `‖u‖²_{L²(S)} ≤ #Λ |S| B²` if `‖u‖ ≤ B` on `S` (no measurability needed). -/
theorem formL2Sq_le_of_norm_le {S : Set (Fin n → ℝ)} (hS : volume S < ⊤) {u : FormField n}
    {B : ℝ} (hu : ∀ x ∈ S, ‖u x‖ ≤ B) :
    formL2Sq S u ≤ Fintype.card (Finset (Fin n)) * volume.real S * B ^ 2 := by
  have h1 : ∀ t : Finset (Fin n), ∫ x in S, (u x t) ^ 2 ≤ B ^ 2 * volume.real S := fun t => by
    refine (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const hS fun x hx => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    have hle : |u x t| ≤ ‖u x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (u x) t
    exact pow_le_pow_left₀ (abs_nonneg _) (hle.trans (hu x hx)) 2
  calc formL2Sq S u ≤ ∑ _t : Finset (Fin n), B ^ 2 * volume.real S :=
        Finset.sum_le_sum fun t _ => h1 t
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem measureReal_closedInterior_mapEquiv_boxMap (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    (t : Fin n → ℝ) {h : ℝ} (hh : 0 < h) :
    volume.real (mapEquiv (boxMap t h hh.ne') K).closedInterior =
      h ^ n * volume.real K.closedInterior := by
  have := integral_closedInterior_mapEquiv_boxMap K t hh fun _ => (1 : ℝ)
  simpa [setIntegral_const] using this

end Error

/-! ### The kernel lemma for the canonical interpolants -/

section KernelInterp

variable {r k : ℕ}

theorem polySpace_le_contDegForms (r k : ℕ) : polySpace n r k ≤ contDegForms n k :=
  fun _ hu => ⟨polySpace_le_contForms r k hu, isDeg_of_mem_polySpace hu⟩

/-- A constant `k`-form field lies in `P_sΛᵏ` for every `s`. -/
theorem mem_polySpace_of_eq_const {s : ℕ} {v : FormField n} (hv : ∀ x, v x = v 0)
    (hvk : ∀ x, IsDeg k (v x)) : v ∈ polySpace n s k := by
  refine ⟨fun t => MvPolynomial.C (v 0 t), ⟨fun t ht => by simp [hvk 0 t ht], fun t => by
    simp⟩, ?_⟩
  rw [evalForm_C]
  exact (funext hv).symm

/-- `Π_K` of `P_{r'}⁻Λᵏ(K)` as a linear map `P_rΛᵏ → P_rΛᵏ` (`r' ≤ r`). -/
def polyMinusInterpOn (K : Affine.Simplex ℝ (Fin n → ℝ) n) {r' : ℕ} (hr' : 1 ≤ r') (hk : k ≤ n)
    (hrr : r' ≤ r) : polySpace n r k →ₗ[ℝ] polySpace n r k :=
  Submodule.inclusion (fun _ hω => polySpace_mono hrr (polyMinusSpace_le_polySpace hr'
      (mem_polyMinusSpace_of_mem_localPolyMinusSpace (isUnit_det_edgeMatrix K) hω))) ∘ₗ
    polyMinusInterp (isUnit_det_edgeMatrix K) hr' hk ∘ₗ
      Submodule.inclusion (polySpace_le_contDegForms r k)

/-- **The scaling argument of [QuennevilleBelair2015], Prop 5.9(1)**, for the canonical
interpolant of `P_{r'}⁻Λᵏ` on `T = t + h K` acting on `P_rΛᵏ` (`r' ≤ r`; the thesis case is
`P_2Λ¹ ≅ P_2Λ⁰ ⊗ ℝ³ → P_1⁻Λ¹`): `‖u - Π_T u‖_{L²(T)} ≤ C h ‖Du‖_{L²(T)}` with `C` depending only
on `K`, `n`, `r`, `r'`, `k`. -/
theorem exists_formL2Sq_sub_polyMinusInterp_le_formGradL2Sq (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    {r' : ℕ} (hr' : 1 ≤ r') (hk : k ≤ n) (hrr : r' ≤ r) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {u : FormField n}
      (hu : u ∈ polySpace n r k),
      √(formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior
        (u - (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr' hk
          ⟨u, polySpace_le_contDegForms r k hu⟩ : FormField n))) ≤
        C * h * √(formGradL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u) := by
  set P := polyMinusInterpOn K hr' hk hrr (r := r)
  have hP : ∀ v : polySpace n r k, (∀ x, (v : FormField n) x = (v : FormField n) 0) →
      (LinearMap.id - P : polySpace n r k →ₗ[ℝ] polySpace n r k) v = 0 := by
    intro v hv
    have hc : (v : FormField n) ∈ localPolyMinusSpace K.points r' k := by
      rw [localPolyMinusSpace_eq (isUnit_det_edgeMatrix K)]
      exact polySpace_le_polyMinusSpace hr' k
        (mem_polySpace_of_eq_const hv (isDeg_of_mem_polySpace v.2))
    have e := polyMinusInterp_inclusion (isUnit_det_edgeMatrix K) hr' hk ⟨_, hc⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    refine Subtype.ext ?_
    have e2 := congrArg Subtype.val e
    exact e2.symm
  obtain ⟨C, hC0, hC⟩ := exists_local_kernel_bound le_rfl
    (fun h t _ hu => affinePullback_mem_polySpace_scalarMat h t hu) le_rfl
    (LinearMap.id - P : polySpace n r k →ₗ[ℝ] polySpace n r k) hP K
  refine ⟨C, hC0, fun {h} hh t u hu => hC hh t u hu _ (fun x => ?_) ?_⟩
  · have hPi := isDeg_of_mem_polySpace (polyMinusSpace_le_polySpace hr'
      (mem_polyMinusSpace_of_mem_localPolyMinusSpace (isUnit_det_edgeMatrix _)
        (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr' hk
          ⟨u, polySpace_le_contDegForms r k hu⟩).2))
    intro s hs
    simp [isDeg_of_mem_polySpace hu x s hs, hPi x s hs]
  · have hnat := affinePullback_polyMinusInterp (isUnit_det_edgeMatrix K)
      (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) (scalarMat n h) t
      (points_mapEquiv_boxMap K t hh.ne') hr' hk ⟨u, polySpace_le_contDegForms r k hu⟩
    rw [show affinePullback (scalarMat n h) t (u - (polyMinusInterp _ hr' hk ⟨u, _⟩ :
        FormField n)) = affinePullback (scalarMat n h) t u -
          affinePullback (scalarMat n h) t (polyMinusInterp
            (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr' hk
            ⟨u, polySpace_le_contDegForms r k hu⟩ : FormField n) from
        map_sub (affinePullbackₗ (scalarMat n h) t) _ _, hnat]
    rfl

end KernelInterp

/-! ### Degrees of freedom of the global families on homothetic simplices -/

section GlobalDof

/-- Moments along vertex families under affine maps. -/
theorem vertexMoment_affine {m : ℕ} (A : Fin n → Fin n → ℝ) (a : Fin n → ℝ)
    (q : Fin (m + 1) → Fin n → ℝ) (η : FormField m) (ω : FormField n) :
    vertexMoment (fun i => affine A a (q i)) η ω = vertexMoment q η (affinePullback A a ω) := by
  rw [vertexMoment, vertexMoment, affinePullback_affinePullback, simplexMatrix_comp_affine]

/-- A homothety with positive ratio preserves the lexicographic order. -/
theorem strictMono_toLex_affine_scalarMat {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) :
    StrictMono fun x : Lex (Fin n → ℝ) => toLex (affine (scalarMat n h) t (ofLex x)) := by
  intro x y hxy
  obtain ⟨i, hj, hi⟩ := hxy
  have hj' : ∀ j, j < i → ofLex x j = ofLex y j := hj
  have hi' : ofLex x i < ofLex y i := hi
  refine ⟨i, fun j hji => ?_, ?_⟩
  · show affine (scalarMat n h) t (ofLex x) j = affine (scalarMat n h) t (ofLex y) j
    simp only [affine_scalarMat, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hj' j hji]
  · show affine (scalarMat n h) t (ofLex x) i < affine (scalarMat n h) t (ofLex y) i
    simp only [affine_scalarMat, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith

theorem lexEnum_image_affine_scalarMat {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ)
    {g : Finset (Fin n → ℝ)} {m : ℕ} (hg : #g = m + 1) :
    lexEnum (g.image (affine (scalarMat n h) t)) m =
      fun i => affine (scalarMat n h) t (lexEnum g m i) := by
  have hinj : Function.Injective (affine (scalarMat n h) t) := fun x y hxy => by
    rw [affine_scalarMat, affine_scalarMat] at hxy
    exact smul_right_injective _ hh.ne' (add_right_cancel hxy)
  refine lexEnum_eq (by rw [card_image_of_injective _ hinj, hg])
    (fun i => mem_image_of_mem _ (lexEnum_mem hg i)) fun i j hij => ?_
  exact strictMono_toLex_affine_scalarMat hh t (strictMono_lexEnum hg hij)

theorem injective_affine_scalarMat {h : ℝ} (hh : h ≠ 0) (t : Fin n → ℝ) :
    Function.Injective (affine (scalarMat n h) t) := fun x y hxy => by
  rw [affine_scalarMat, affine_scalarMat] at hxy
  exact smul_right_injective _ hh (add_right_cancel hxy)

theorem vertexSet_mapEquiv_boxMap (K : Affine.Simplex ℝ (Fin n → ℝ) n) (t : Fin n → ℝ)
    {h : ℝ} (hh : h ≠ 0) :
    vertexSet (mapEquiv (boxMap t h hh) K) = (vertexSet K).image (affine (scalarMat n h) t) := by
  classical
  simp only [vertexSet, points_mapEquiv_boxMap K t hh, Finset.image_image]
  rfl

namespace PolySeq

variable (S : PolySeq)

theorem space_le_polySpace (k : ℕ) : S.space n k ≤ polySpace n (S.deg k) k := by
  change (S.kind k).space n (S.deg k) k ≤ _
  cases S.kind k
  · exact le_rfl
  · exact polyMinusSpace_le_polySpace (S.one_le_deg k)

theorem affinePullback_mem_space_scalarMat (k : ℕ) (h : ℝ) (t : Fin n → ℝ) {u : FormField n}
    (hu : u ∈ S.space n k) : affinePullback (scalarMat n h) t u ∈ S.space n k := by
  change u ∈ (S.kind k).space n (S.deg k) k at hu
  change _ ∈ (S.kind k).space n (S.deg k) k
  generalize S.kind k = κ at hu ⊢
  cases κ
  · exact affinePullback_mem_polySpace_scalarMat h t hu
  · exact affinePullback_mem_polyMinusSpace_scalarMat h t hu

/-- The degrees of freedom of a face `g` of `K` and of its homothetic image `t + h g`
(`h > 0`) correspond: `ℓ_{t + h g, i}(u) = ℓ_{g, i}(H^* u)`. -/
theorem sum_dofIdx_image_affine_scalarMat {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) (k : ℕ)
    (g : Finset (Fin n → ℝ)) (f : ℝ → ℝ) {u : FormField n} (hu : u ∈ S.space n k) :
    ∑ i : S.DofIdx (g.image (affine (scalarMat n h) t)) k,
        f (S.dof _ k i ⟨u, S.space_le_contForms n k hu⟩) =
      ∑ i : S.DofIdx g k, f (S.dof g k i ⟨affinePullback (scalarMat n h) t u,
        S.space_le_contForms n k (S.affinePullback_mem_space_scalarMat k h t hu)⟩) := by
  classical
  set G := affine (scalarMat n h) t
  set g' := g.image G
  have hc : #g' = #g := card_image_of_injective _ (injective_affine_scalarMat hh.ne' t)
  have hN : Module.finrank ℝ (S.test k (#g' - 1)) = Module.finrank ℝ (S.test k (#g - 1)) := by
    rw [hc]
  have hne : ∀ _i : Fin (Module.finrank ℝ (S.test k (#g' - 1))), g'.Nonempty ↔ g.Nonempty :=
    fun _ => Finset.image_nonempty
  refine Fintype.sum_equiv (Equiv.subtypeEquiv (finCongr hN) hne) _ _ fun i => ?_
  have key : ∀ (a b : ℕ) (hab : a = b) (j : Fin (Module.finrank ℝ (S.test k a))),
      vertexMoment (lexEnum g' a) (S.testBasis k a j : FormField a) u =
        vertexMoment (lexEnum g' b) (S.testBasis k b (Fin.cast (by rw [hab]) j) : FormField b)
          u := by
    intro a b hab j
    subst hab
    rfl
  rcases g.eq_empty_or_nonempty with h0 | hg0
  · exact absurd ((hne i.1).1 i.2) (by rw [h0]; exact Finset.not_nonempty_empty)
  have hg : #g = (#g - 1) + 1 := (Nat.succ_pred_eq_of_pos (card_pos.2 hg0)).symm
  rw [dof_apply, dof_apply]
  rw [degField_eq_self (PolyKind.isDeg_of_mem_space hu),
    degField_eq_self (PolyKind.isDeg_of_mem_space (S.affinePullback_mem_space_scalarMat k h t hu)),
    key _ _ (by rw [hc]) i.1, lexEnum_image_affine_scalarMat hh t hg, vertexMoment_affine]
  rfl

/-- The homothety `g ↦ t + h g` of faces of `K` onto faces of `T = t + h K`. -/
def powersetHomothety (K : Affine.Simplex ℝ (Fin n → ℝ) n) {h : ℝ} (hh : 0 < h)
    (t : Fin n → ℝ) :
    (vertexSet K).powerset ≃ (vertexSet (mapEquiv (boxMap t h hh.ne') K)).powerset := by
  classical
  refine Equiv.ofBijective (fun g => ⟨(g : Finset (Fin n → ℝ)).image (affine (scalarMat n h) t),
    ?_⟩) ⟨fun g g' hgg' => ?_, fun g' => ?_⟩
  · rw [Finset.mem_powerset, vertexSet_mapEquiv_boxMap K t hh.ne']
    exact image_subset_image (Finset.mem_powerset.1 g.2)
  · exact Subtype.ext (Finset.image_injective (injective_affine_scalarMat hh.ne' t)
      (congrArg Subtype.val hgg'))
  · have h1 : (g' : Finset (Fin n → ℝ)) ⊆ (vertexSet K).image (affine (scalarMat n h) t) :=
      (Finset.mem_powerset.1 g'.2).trans (vertexSet_mapEquiv_boxMap K t hh.ne').le
    obtain ⟨s, hs, hse⟩ := Finset.subset_image_iff.1 h1
    exact ⟨⟨s, Finset.mem_powerset.2 hs⟩, Subtype.ext hse⟩

/-- **The degrees of freedom of the global families on `T = t + h K`** are those of `K` applied to
`H^* u`: for every `f`, `Σ_{g ⊆ T, i} f(ℓ_{g,i}(u)) = Σ_{g ⊆ K, i} f(ℓ_{g,i}(H^* u))`. The
lexicographic vertex order is preserved by `H` (`h > 0`). -/
theorem sum_dof_mapEquiv_boxMap (K : Affine.Simplex ℝ (Fin n → ℝ) n) {h : ℝ} (hh : 0 < h)
    (t : Fin n → ℝ) (k : ℕ) (f : ℝ → ℝ) {u : FormField n} (hu : u ∈ S.space n k) :
    ∑ p : Σ g : (vertexSet (mapEquiv (boxMap t h hh.ne') K)).powerset,
        S.DofIdx (g : Finset (Fin n → ℝ)) k,
        f (S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ⟨u, S.space_le_contForms n k hu⟩) =
      ∑ p : Σ g : (vertexSet K).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k,
        f (S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ⟨affinePullback (scalarMat n h) t u,
          S.space_le_contForms n k (S.affinePullback_mem_space_scalarMat k h t hu)⟩) := by
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  refine (Fintype.sum_equiv (powersetHomothety K hh t) _ _ fun g => ?_).symm
  exact (S.sum_dofIdx_image_affine_scalarMat hh t k g f hu).symm

/-- The degrees of freedom of the faces of `K` as functionals on `S.space n k`. -/
def dofOn (K : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ)
    (p : Σ g : (vertexSet K).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k) :
    S.space n k →ₗ[ℝ] ℝ :=
  S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ∘ₗ Submodule.inclusion (S.space_le_contForms n k)

theorem injective_pi_dofOn (K : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    Function.Injective (LinearMap.pi (S.dofOn K k)) := fun _ _ huv =>
  (S.isUnisolvent_dof K k).ext fun p => congrFun huv p

/-- **DOF estimate for the global families on `T = t + h K`**: for `u ∈ P_{r_k}Λᵏ` (resp.
`P_{r_k}⁻Λᵏ`), `hᵏ sup_T ‖u‖ ≤ B Σ_{g ⊆ T, i} |ℓ_{g,i}(u)|` with the degrees of freedom
`ℓ_{g,i}` of `Feec.FiniteElement.PolySeq.dof` (lexicographically ordered faces of `T`) and `B`
depending only on `K`, `S` and `k`. -/
theorem exists_local_dof_bound (K : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {u : FormField n}
      (hu : u ∈ S.space n k), ∀ x ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior,
        h ^ k * ‖u x‖ ≤ B * ∑ p : Σ g : (vertexSet (mapEquiv (boxMap t h hh.ne') K)).powerset,
          S.DofIdx (g : Finset (Fin n → ℝ)) k,
          |S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ⟨u, S.space_le_contForms n k hu⟩| := by
  obtain ⟨B, hB0, hB⟩ := exists_local_dof_bound_of_le_polySpace (S.space_le_polySpace k)
    (fun h t _ hu => S.affinePullback_mem_space_scalarMat k h t hu) K (S.dofOn K k)
    (S.injective_pi_dofOn K k)
  refine ⟨B, hB0, fun {h} hh t u hu x hx => (hB hh t u hu x hx).trans_eq ?_⟩
  rw [S.sum_dof_mapEquiv_boxMap K hh t k (fun a => |a|) hu]
  rfl

/-- **`ℓ²`-scaling of the DOFs of the global families on `T = t + h K`** (the corrected form of
[QuennevilleBelair2015], Prop 5.8): `‖u‖²_{L²(T)} ≍ h^{n - 2k} Σ_{g ⊆ T, i} ℓ_{g,i}(u)²`. -/
theorem exists_local_formL2Sq_equiv (K : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {u : FormField n}
      (hu : u ∈ S.space n k),
      (h ^ k) ^ 2 * formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u ≤
          C * (h ^ n * ∑ p : Σ g : (vertexSet (mapEquiv (boxMap t h hh.ne') K)).powerset,
            S.DofIdx (g : Finset (Fin n → ℝ)) k,
            (S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ⟨u, S.space_le_contForms n k hu⟩) ^ 2) ∧
        h ^ n * ∑ p : Σ g : (vertexSet (mapEquiv (boxMap t h hh.ne') K)).powerset,
            S.DofIdx (g : Finset (Fin n → ℝ)) k,
            (S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ⟨u, S.space_le_contForms n k hu⟩) ^ 2 ≤
          C * ((h ^ k) ^ 2 * formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u) := by
  obtain ⟨C, hC0, hC⟩ := exists_local_formL2Sq_equiv_of_le_polySpace (S.space_le_polySpace k)
    (fun h t _ hu => S.affinePullback_mem_space_scalarMat k h t hu) K (S.dofOn K k)
    (S.injective_pi_dofOn K k)
  refine ⟨C, hC0, fun {h} hh t u hu => ?_⟩
  rw [S.sum_dof_mapEquiv_boxMap K hh t k (fun a => a ^ 2) hu]
  exact hC hh t u hu

end PolySeq

end GlobalDof

/-! ### Uniform constants for finitely many reference simplices -/

section Uniform

variable {r k : ℕ}

namespace PolySeq

variable (S : PolySeq)

/-- `PolySeq.exists_local_dof_bound` with one constant for a finite family of reference
simplices. -/
theorem exists_local_dof_bound_uniform {ι : Type*} [Finite ι]
    (K : ι → Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ i, ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {u : FormField n}
      (hu : u ∈ S.space n k), ∀ x ∈ (mapEquiv (boxMap t h hh.ne') (K i)).closedInterior,
        h ^ k * ‖u x‖ ≤ B * ∑ p : Σ g : (vertexSet (mapEquiv (boxMap t h hh.ne') (K i))).powerset,
          S.DofIdx (g : Finset (Fin n → ℝ)) k,
          |S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ⟨u, S.space_le_contForms n k hu⟩| := by
  classical
  have := Fintype.ofFinite ι
  choose B hB0 hB using fun i => S.exists_local_dof_bound (K i) k
  refine ⟨∑ i, B i, Finset.sum_nonneg fun i _ => hB0 i,
    fun i {h} hh t u hu x hx => (hB i hh t hu x hx).trans ?_⟩
  have hBi : B i ≤ ∑ j, B j :=
    Finset.single_le_sum (f := B) (fun j _ => hB0 j) (Finset.mem_univ i)
  exact mul_le_mul_of_nonneg_right hBi (Finset.sum_nonneg fun _ _ => abs_nonneg _)

end PolySeq

end Uniform

end Feec.FiniteElement
