module

public import Feec.FiniteElement.SmoothingBasic
public import Feec.FiniteElement.PolyInterpolation
public import Feec.FiniteElement.PolyComplex

/-!
# Degrees of freedom of the higher-order families on simplicial meshes

The mesh-independent ingredients of the smoothed-projection estimates for an admissible sequence
`S` (`Feec.FiniteElement.PolySeq`), used on shape-regular meshes of star-shaped domains
(`Feec.Models.StarShaped.PolySmoothing`) and on the cube
(`Feec.Models.Cube.PolySmoothingEstimates`):

* **Trace determination on every face** (`PolySeq.affinePullback_lexEnum_eq_of_dof_eq`, the
  facet case being `PolySeq.tangentialTraceEq_of_dof_eq`): fields of the global space have the
  same trace on every common face of two simplices (`PolySeq.pullback_eq_of_mem_globalSpace`).
* **Degrees of freedom as integrals of the values** (`PolySeq.dof_eq_integral`): the moment DOF
  `ℓ_{g,i}(ω) = ∫_{T̂_m} F_q^* ω_k ∧ ηᵢ` (`q` the lexicographic parametrization of the face `g`) is
  `∫_{T̂_m} Σₛ ω(F_q ξ)ₛ cₛ(ξ) dξ` with a coefficient vector `c = dofCoeff` bounded by the `k × k`
  minors of the edge matrix and the test forms (`sum_abs_dofCoeff_le`,
  `PolySeq.exists_coeffBound_of_le`), which only sees the trace on `g`
  (`sum_mul_dofCoeff_eq_of_pullback_eq`); hence `|ℓ_{g,i}(ω)| ≲ |edges|ᵏ sup_T |ω|`
  (`PolySeq.abs_dof_le_of_coeff_le`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §4.5–4.6 (the moment degrees of freedom)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter

/-! ### Traces on the faces of a simplex -/

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh

variable {n : ℕ}

namespace PolySeq

variable (S : PolySeq)

/-- **Trace determination on any face**: two fields of `P_{r_k}Λᵏ` (resp. `P_{r_k}⁻Λᵏ`) with the
same degrees of freedom on the subfaces of a face `g` of an `n`-simplex `T` have the same pullback
along the lexicographic parametrization of `g` (the facet case is
`PolySeq.tangentialTraceEq_of_dof_eq`). -/
theorem affinePullback_lexEnum_eq_of_dof_eq {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {g : Finset (Fin n → ℝ)} {k m : ℕ} (hT : g ⊆ vertexSet T) (hc : #g = m + 1)
    {w η : FormField n} (hw : w ∈ S.space n k) (hη : η ∈ S.space n k)
    (hdof : ∀ g' ⊆ g, ∀ i : S.DofIdx g' k, S.dof g' k i ⟨w, S.space_le_contForms n k hw⟩ =
      S.dof g' k i ⟨η, S.space_le_contForms n k hη⟩) :
    affinePullback (simplexMatrix (lexEnum g m)) (lexEnum g m 0) w =
      affinePullback (simplexMatrix (lexEnum g m)) (lexEnum g m 0) η := by
  set p' := lexEnum (vertexSet T) n
  have hp' := isUnit_det_edgeMatrix_lexEnum T
  have hmono := strictMono_lexEnum (card_vertexSet T)
  obtain ⟨eF, heF⟩ := exists_orderEmb_comp_eq_lexEnum hmono hc fun x hx =>
    exists_lexEnum_eq_of_mem_vertexSet T (hT hx)
  have htr := PolyKind.faceTrace_eq (S.kind k) hp' (S.one_le_deg k) (Face.ofEmb eF) hw hη
    fun g'' hg ζ hζ => by
      obtain ⟨hcard, hG⟩ := lexEnum_image_comp hmono g''.emb.strictMono
      have hGF : Finset.univ.image (p' ∘ g''.emb) ⊆ g := fun x hx => by
        obtain ⟨j, -, rfl⟩ := mem_image.1 hx
        have hj := hg (orderEmbOfFin_mem g''.2.1 g''.2.2 j)
        obtain ⟨a, -, ha⟩ := mem_map.1 hj
        change p' (g''.2.1.orderEmbOfFin g''.2.2 j) ∈ g
        rw [← ha]
        change (p' ∘ eF) a ∈ g
        rw [heF]
        exact lexEnum_mem hc a
      have h := S.degMoment_eq_of_dof_eq hcard (fun i => hdof _ hGF i) hζ
      rw [hG, degField_eq_self (PolyKind.isDeg_of_mem_space hw),
        degField_eq_self (PolyKind.isDeg_of_mem_space hη)] at h
      exact h
  rw [Face.emb_ofEmb, faceTrace_apply, faceTrace_apply] at htr
  rw [heF, show lexEnum (vertexSet T) n (eF 0) = lexEnum g m 0 from congrFun heF 0] at htr
  exact htr

/-- The pointwise form of `affinePullback_lexEnum_eq_of_dof_eq`: at every point of the
parametrized face, the pullbacks of the values agree. -/
theorem pullback_eq_of_dof_eq {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {g : Finset (Fin n → ℝ)} {k m : ℕ} (hT : g ⊆ vertexSet T) (hc : #g = m + 1)
    {w η : FormField n} (hw : w ∈ S.space n k) (hη : η ∈ S.space n k)
    (hdof : ∀ g' ⊆ g, ∀ i : S.DofIdx g' k, S.dof g' k i ⟨w, S.space_le_contForms n k hw⟩ =
      S.dof g' k i ⟨η, S.space_le_contForms n k hη⟩) (ξ : Fin m → ℝ) :
    pullback (simplexMatrix (lexEnum g m)) (w (simplexMap (lexEnum g m) ξ)) =
      pullback (simplexMatrix (lexEnum g m)) (η (simplexMap (lexEnum g m) ξ)) :=
  congrFun (S.affinePullback_lexEnum_eq_of_dof_eq hT hc hw hη hdof) ξ

end PolySeq

/-! ### The degrees of freedom as integrals of the values against coefficient fields -/

/-- The coefficient vector of the moment `∫_{T̂_m} F_q^* ω ∧ η` at `ξ ∈ T̂_m`, on degree-`k`
fields: `ω ↦ Σₛ ω(F_q ξ)ₛ cₛ(ξ)`. -/
def dofCoeff {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ) (η : FormField m) (k : ℕ) (ξ : Fin m → ℝ) :
    Finset (Fin n) → ℝ := fun s =>
  if #s = k then wedgeForm (wedgeProd (simplexMatrix q) s) (η ξ) univ else 0

theorem wedgeField_affinePullback_degField_eq {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ)
    (η : FormField m) (k : ℕ) (ω : FormField n) (ξ : Fin m → ℝ) :
    wedgeField (affinePullback (simplexMatrix q) (q 0) (degField k ω)) η ξ univ =
      ∑ s, ω (simplexMap q ξ) s * dofCoeff q η k ξ s := by
  simp only [wedgeField, affinePullback_apply, wedgeForm_pullback_apply, degField, dofCoeff]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [simplexMap]

/-- **The moment as an integral of the values**: `∫_{T̂_m} F_q^* ω_k ∧ η = ∫_{T̂_m} Σₛ ω(F_q ξ)ₛ
cₛ(ξ) dξ`. -/
theorem vertexMoment_degField_eq {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ) (η : FormField m)
    (k : ℕ) (ω : FormField n) :
    vertexMoment q η (degField k ω) =
      ∫ ξ in refSimplex m, ∑ s, ω (simplexMap q ξ) s * dofCoeff q η k ξ s := by
  rw [vertexMoment_eq_integral]
  exact setIntegral_congr_fun (measurableSet_refSimplex m) fun ξ _ =>
    wedgeField_affinePullback_degField_eq q η k ω ξ

/-- **The coefficient vector only sees the trace**: for degree-`k` vectors with the same pullback
along the edge matrix, the pairings with `c(ξ)` agree. -/
theorem sum_mul_dofCoeff_eq_of_pullback_eq {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ)
    (η : FormField m) {k : ℕ} (ξ : Fin m → ℝ) {α β : Finset (Fin n) → ℝ} (hα : IsDeg k α)
    (hβ : IsDeg k β) (h : pullback (simplexMatrix q) α = pullback (simplexMatrix q) β) :
    ∑ s, α s * dofCoeff q η k ξ s = ∑ s, β s * dofCoeff q η k ξ s := by
  have key : ∀ γ : Finset (Fin n) → ℝ, IsDeg k γ →
      ∑ s, γ s * dofCoeff q η k ξ s = wedgeForm (pullback (simplexMatrix q) γ) (η ξ) univ := by
    intro γ hγ
    rw [wedgeForm_pullback_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [dofCoeff]
    split_ifs with hs
    · rfl
    · rw [hγ s hs]; ring
  rw [key α hα, key β hβ, h]

theorem abs_shuffleSgn {d : Type*} [LinearOrder d] (s t : Finset d) :
    |(shuffleSgn s t : ℝ)| = 1 := by
  have h := shuffleSgn_mul_self (R := ℝ) s t
  have h2 : |(shuffleSgn s t : ℝ)| * |(shuffleSgn s t : ℝ)| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith [abs_nonneg (shuffleSgn s t : ℝ)]

/-- `|(α ∧ β)_{univ}| ≤ Σ_a |α_a| ‖β‖`. -/
theorem abs_wedgeForm_univ_le {m : ℕ} (α β : Finset (Fin m) → ℝ) :
    |wedgeForm α β univ| ≤ (∑ a, |α a|) * ‖β‖ := by
  rw [wedgeForm_apply, Finset.powerset_univ, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul, abs_mul, abs_shuffleSgn, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := norm_le_pi_norm β (univ \ a)
  rwa [Real.norm_eq_abs] at this

/-- **Size of the coefficient vector**: if the edge vectors of `q` have entries `≤ a`, then
`Σₛ |cₛ(ξ)| ≤ 2ⁿ 2ᵐ k! aᵏ ‖η(ξ)‖`. -/
theorem sum_abs_dofCoeff_le {m : ℕ} {q : Fin (m + 1) → Fin n → ℝ} {a : ℝ} (ha0 : 0 ≤ a)
    (ha : ∀ i l, |simplexMatrix q i l| ≤ a) (η : FormField m) (k : ℕ) (ξ : Fin m → ℝ) :
    ∑ s, |dofCoeff q η k ξ s| ≤ 2 ^ n * (2 ^ m * (k.factorial * a ^ k)) * ‖η ξ‖ := by
  have hminor : ∀ s : Finset (Fin n), #s = k → ∀ t : Finset (Fin m),
      |wedgeProd (simplexMatrix q) s t| ≤ k.factorial * a ^ k := by
    intro s hs t
    by_cases ht : #t = k
    · rw [wedgeProd_apply_eq_det_submatrix (simplexMatrix q) hs ht]
      have := Matrix.det_le (abv := AbsoluteValue.abs) (x := a)
        (A := Matrix.of fun i j : Fin k => simplexMatrix q (s.orderEmbOfFin hs i)
          (t.orderEmbOfFin ht j)) fun i j => ha _ _
      simpa [Fintype.card_fin, nsmul_eq_mul] using this
    · rw [isDeg_wedgeProd (simplexMatrix q) s t (by rw [hs]; exact ht)]
      simp only [abs_zero]
      positivity
  have h1 : ∀ s : Finset (Fin n), |dofCoeff q η k ξ s| ≤ 2 ^ m * (k.factorial * a ^ k) * ‖η ξ‖ := by
    intro s
    simp only [dofCoeff]
    split_ifs with hs
    · refine (abs_wedgeForm_univ_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      calc ∑ t, |wedgeProd (simplexMatrix q) s t| ≤ ∑ _t : Finset (Fin m), k.factorial * a ^ k :=
            Finset.sum_le_sum fun t _ => hminor s hs t
        _ = 2 ^ m * (k.factorial * a ^ k) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
              nsmul_eq_mul]; push_cast; ring
    · rw [abs_zero]; positivity
  calc ∑ s, |dofCoeff q η k ξ s| ≤ ∑ _s : Finset (Fin n), 2 ^ m * (k.factorial * a ^ k) * ‖η ξ‖ :=
        Finset.sum_le_sum fun s _ => h1 s
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
          nsmul_eq_mul]; push_cast; ring

/-- The lexicographic parametrization of a face of `T` maps the reference simplex into `T`. -/
theorem simplexMap_lexEnum_mem {T : Affine.Simplex ℝ (Fin n → ℝ) n} {g : Finset (Fin n → ℝ)}
    (hgT : g ⊆ vertexSet T) {m : ℕ} (hg : #g = m + 1) {ξ : Fin m → ℝ}
    (hξ : ξ ∈ refSimplex m) :
    simplexMap (lexEnum g m) ξ ∈ T.closedInterior := by
  rw [← convexHull_vertexSet]
  refine convexHull_mono ?_ (simplexMap_mem_convexHull _ hξ)
  rw [range_lexEnum hg]; exact Finset.coe_subset.2 hgT

namespace PolySeq

variable (S : PolySeq)

/-- **The degrees of freedom as integrals of the values**: `ℓ_{g,i}(ω) = ∫_{T̂_m} Σₛ ω(F_q ξ)ₛ
cₛ(ξ) dξ`, `q = lexEnum g m`, `m = #g - 1`, `cₛ = dofCoeff q ηᵢ k`. -/
theorem dof_eq_integral (g : Finset (Fin n → ℝ)) (k : ℕ) (i : S.DofIdx g k) (ω : contForms n) :
    S.dof g k i ω = ∫ ξ in refSimplex (#g - 1),
      ∑ s, (ω : FormField n) (simplexMap (lexEnum g (#g - 1)) ξ) s *
        dofCoeff (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) k ξ s := by
  rw [dof_apply, vertexMoment_degField_eq]

/-- A uniform bound of the test forms on the reference simplices. -/
theorem exists_testBound (k : ℕ) : ∃ M, 0 ≤ M ∧ ∀ m ≤ n,
    ∀ (i : Fin (Module.finrank ℝ (S.test k m))), ∀ ξ ∈ refSimplex m,
      ‖(S.testBasis k m i : FormField m) ξ‖ ≤ M := by
  have hb : ∀ m (i : Fin (Module.finrank ℝ (S.test k m))), ∃ M, 0 ≤ M ∧
      ∀ ξ ∈ refSimplex m, ‖(S.testBasis k m i : FormField m) ξ‖ ≤ M := by
    intro m i
    obtain ⟨M, hM⟩ := (isCompact_refSimplex m).exists_bound_of_continuousOn
      (S.continuous_testBasis k m i).continuousOn
    exact ⟨max M 0, le_max_right _ _, fun ξ hξ => (hM ξ hξ).trans (le_max_left _ _)⟩
  choose M hM0 hM using hb
  refine ⟨∑ m ∈ Finset.range (n + 1), ∑ i, M m i, Finset.sum_nonneg fun m _ =>
    Finset.sum_nonneg fun i _ => hM0 m i, fun m hm i ξ hξ => (hM m i ξ hξ).trans ?_⟩
  calc M m i ≤ ∑ i, M m i := Finset.single_le_sum (f := M m) (fun i _ => hM0 m i)
        (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun m => ∑ i, M m i)
        (fun m _ => Finset.sum_nonneg fun i _ => hM0 m i) (Finset.mem_range.2 (by omega))

/-- **The coefficient fields of the degrees of freedom are `O(hᵏ)`** on every simplex whose edge
vectors are bounded by `h`, with one constant. -/
theorem exists_coeffBound_of_le (k : ℕ) : ∃ D, 0 ≤ D ∧
    ∀ {T : Affine.Simplex ℝ (Fin n → ℝ) n} {g : Finset (Fin n → ℝ)}, g ⊆ vertexSet T →
      ∀ (i : S.DofIdx g k) {h : ℝ}, 0 ≤ h →
        (∀ j l, |simplexMatrix (lexEnum g (#g - 1)) j l| ≤ h) →
        ∀ ξ ∈ refSimplex (#g - 1),
          ∑ s, |dofCoeff (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 :
            FormField (#g - 1)) k ξ s| ≤ D * h ^ k := by
  obtain ⟨M, hM0, hM⟩ := exists_testBound S k
  refine ⟨2 ^ n * (2 ^ n * k.factorial) * M, by positivity,
    fun {T g} hgT i h hh hle ξ hξ => ?_⟩
  have hgn : #g - 1 ≤ n := by
    have := Finset.card_le_card hgT
    rw [card_vertexSet] at this; omega
  refine (sum_abs_dofCoeff_le hh hle _ k ξ).trans ?_
  have h2 : (2 : ℝ) ^ (#g - 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hgn
  have hη := hM (#g - 1) hgn i.1 ξ hξ
  have hhk := pow_nonneg hh k
  calc 2 ^ n * (2 ^ (#g - 1) * (k.factorial * h ^ k)) *
        ‖(S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) ξ‖
      ≤ 2 ^ n * (2 ^ n * (k.factorial * h ^ k)) * M := by
        gcongr
    _ = _ := by ring

/-- **Stability of the degrees of freedom in the sup norm**: if the coefficient fields of the
moment `ℓ_{g,i}` of a face `g` of `T` satisfy `Σₛ |cₛ| ≤ K` on the reference simplex, then
`|ℓ_{g,i}(ω)| ≤ K sup_T |ω|` for every continuous form `ω`. -/
theorem abs_dof_le_of_coeff_le {k : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (i : S.DofIdx g k) (ω : contForms n)
    {K B : ℝ} (hK : ∀ ξ ∈ refSimplex (#g - 1),
      ∑ s, |dofCoeff (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) k
        ξ s| ≤ K) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ T.closedInterior, ∀ s, |(ω : FormField n) x s| ≤ B) :
    |S.dof g k i ω| ≤ K * B := by
  have hne := i.2
  have hg : #g = (#g - 1) + 1 := (Nat.succ_pred_eq_of_pos (card_pos.2 hne)).symm
  set q := lexEnum g (#g - 1)
  set η := (S.testBasis k (#g - 1) i.1 : FormField (#g - 1))
  rw [S.dof_eq_integral]
  have h0 : (0 : Fin (#g - 1) → ℝ) ∈ refSimplex (#g - 1) := fun a => by
    refine Fin.cases ?_ (fun l => ?_) a
    · simp
    · simp [refBary]
  have hK0 : 0 ≤ K := (Finset.sum_nonneg fun s _ => abs_nonneg _).trans (hK 0 h0)
  have hpt : ∀ ξ ∈ refSimplex (#g - 1),
      ‖∑ s, (ω : FormField n) (simplexMap q ξ) s * dofCoeff q η k ξ s‖ ≤ K * B := by
    intro ξ hξ
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s, |(ω : FormField n) (simplexMap q ξ) s * dofCoeff q η k ξ s|
        ≤ ∑ s, B * |dofCoeff q η k ξ s| := Finset.sum_le_sum fun s _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hB _ (simplexMap_lexEnum_mem hgT hg hξ) s)
            (abs_nonneg _)
      _ = B * ∑ s, |dofCoeff q η k ξ s| := by rw [Finset.mul_sum]
      _ ≤ B * K := mul_le_mul_of_nonneg_left (hK ξ hξ) hB0
      _ = K * B := by ring
  rw [← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le_const (volume_refSimplex_lt_top _) hpt).trans ?_
  calc K * B * volume.real (refSimplex (#g - 1)) ≤ K * B * 1 :=
        mul_le_mul_of_nonneg_left (volume_real_refSimplex_le_one _) (mul_nonneg hK0 hB0)
    _ = _ := mul_one _

variable {S} in
/-- Global fields have the same pullback along a common face (`pullback_eq_of_dof_eq`). -/
theorem pullback_eq_of_mem_globalSpace {M : SimplicialMesh n} {k : ℕ}
    {u : (polyElement n S).Piecewise M k} (hu : u ∈ (polyElement n S).globalSpace M k)
    (T T' : M.simplices) {g : Finset (Fin n → ℝ)} {m : ℕ}
    (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (hgT' : g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n)) (hg : #g = m + 1)
    (ξ : Fin m → ℝ) :
    pullback (simplexMatrix (lexEnum g m))
        (((u T : (polyElement n S).space T k) : FormField n) (simplexMap (lexEnum g m) ξ)) =
      pullback (simplexMatrix (lexEnum g m))
        (((u T' : (polyElement n S).space T' k) : FormField n) (simplexMap (lexEnum g m) ξ)) :=
  S.pullback_eq_of_dof_eq hgT hg (u T).2 (u T').2
    (fun g' hg' i => hu T T' g' (hg'.trans hgT) (hg'.trans hgT') i) ξ

theorem card_le_of_dofIdx {g : Finset (Fin n → ℝ)} {k : ℕ} (i : S.DofIdx g k) : k + 1 ≤ #g := by
  by_contra h
  exact (S.isEmpty_dofIdx_of_card_lt (by omega)).false i

end PolySeq

end Feec.FiniteElement
