module

public import Feec.Models.Cube.SmoothingEstimates
public import Feec.FiniteElement.PolyInterpolation
public import Feec.FiniteElement.PolyComplex

/-!
# Smoothed-projection estimates for the higher-order families on the cube

DOCSTRING
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
      ∫ ξ in FiniteElement.refSimplex m, ∑ s, ω (simplexMap q ξ) s * dofCoeff q η k ξ s := by
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

namespace PolySeq

variable (S : PolySeq)

/-- **The degrees of freedom as integrals of the values**: `ℓ_{g,i}(ω) = ∫_{T̂_m} Σₛ ω(F_q ξ)ₛ
cₛ(ξ) dξ`, `q = lexEnum g m`, `m = #g - 1`, `cₛ = dofCoeff q ηᵢ k`. -/
theorem dof_eq_integral (g : Finset (Fin n → ℝ)) (k : ℕ) (i : S.DofIdx g k) (ω : contForms n) :
    S.dof g k i ω = ∫ ξ in FiniteElement.refSimplex (#g - 1),
      ∑ s, (ω : FormField n) (simplexMap (lexEnum g (#g - 1)) ξ) s *
        dofCoeff (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) k ξ s := by
  rw [dof_apply, vertexMoment_degField_eq]

end PolySeq

end Feec.FiniteElement

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre

variable {n : ℕ}

namespace Poly

variable (S : PolySeq)

/-! ### Uniform local estimates on the mesh simplices -/

theorem abs_simplexMatrix_lexEnum_le {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) {m : ℕ}
    (hg : #g = m + 1) (i : Fin n) (l : Fin m) :
    |simplexMatrix (lexEnum g m) i l| ≤ hN N := by
  obtain ⟨m', σ, rfl⟩ := mem_mesh_simplices.1 hT
  have hmem : ∀ a, lexEnum g m a ∈ (cubeSimplex N m' σ).closedInterior := fun a =>
    vertexSet_subset_closedInterior _ (hgT (lexEnum_mem hg a))
  have := norm_sub_le_of_mem_cubeSimplex (hmem l.succ) (hmem 0)
  refine le_trans ?_ this
  have h := norm_le_pi_norm (lexEnum g m l.succ - lexEnum g m 0) i
  rwa [Real.norm_eq_abs, Pi.sub_apply] at h

theorem simplexMap_lexEnum_mem {T : Affine.Simplex ℝ (Fin n → ℝ) n} {g : Finset (Fin n → ℝ)}
    (hgT : g ⊆ vertexSet T) {m : ℕ} (hg : #g = m + 1) {ξ : Fin m → ℝ}
    (hξ : ξ ∈ FiniteElement.refSimplex m) :
    simplexMap (lexEnum g m) ξ ∈ T.closedInterior := by
  rw [← convexHull_vertexSet]
  refine convexHull_mono ?_ (simplexMap_mem_convexHull _ hξ)
  rw [range_lexEnum hg]; exact Finset.coe_subset.2 hgT

/-- A uniform bound of the test forms on the reference simplices. -/
theorem exists_testBound (k : ℕ) : ∃ M, 0 ≤ M ∧ ∀ m ≤ n,
    ∀ (i : Fin (Module.finrank ℝ (S.test k m))), ∀ ξ ∈ FiniteElement.refSimplex m,
      ‖(S.testBasis k m i : FormField m) ξ‖ ≤ M := by
  have hb : ∀ m (i : Fin (Module.finrank ℝ (S.test k m))), ∃ M, 0 ≤ M ∧
      ∀ ξ ∈ FiniteElement.refSimplex m, ‖(S.testBasis k m i : FormField m) ξ‖ ≤ M := by
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

/-- **The coefficient fields of the degrees of freedom are `O(h_Nᵏ)`** on the mesh simplices,
with one constant. -/
def CoeffBound (n k : ℕ) (D : ℝ) : Prop :=
  ∀ (N : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}, T ∈ (mesh n N).simplices →
    ∀ {g : Finset (Fin n → ℝ)}, g ⊆ vertexSet T → ∀ (i : S.DofIdx g k),
      ∀ ξ ∈ FiniteElement.refSimplex (#g - 1),
        ∑ s, |dofCoeff (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) k
          ξ s| ≤ D * hN N ^ k

theorem exists_coeffBound (k : ℕ) : ∃ D, 0 ≤ D ∧ CoeffBound S n k D := by
  obtain ⟨M, hM0, hM⟩ := exists_testBound S k
  refine ⟨2 ^ n * (2 ^ n * k.factorial) * M, by positivity,
    fun N T hT g hgT i ξ hξ => ?_⟩
  have hne := i.2
  have hg : #g = (#g - 1) + 1 := (Nat.succ_pred_eq_of_pos (card_pos.2 hne)).symm
  have hgn : #g - 1 ≤ n := by
    have := Finset.card_le_card hgT
    rw [card_vertexSet] at this; omega
  refine (sum_abs_dofCoeff_le (hN_pos N).le (abs_simplexMatrix_lexEnum_le hT hgT hg) _ k ξ).trans ?_
  have h2 : (2 : ℝ) ^ (#g - 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hgn
  have hη := hM (#g - 1) hgn i.1 ξ hξ
  have hh := pow_nonneg (hN_pos N).le k
  calc 2 ^ n * (2 ^ (#g - 1) * (k.factorial * hN N ^ k)) *
        ‖(S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) ξ‖
      ≤ 2 ^ n * (2 ^ n * (k.factorial * hN N ^ k)) * M := by
        gcongr
    _ = _ := by ring

theorem volume_real_refSimplex_le_one (m : ℕ) :
    volume.real (FiniteElement.refSimplex m) ≤ 1 := by
  rw [volume_real_refSimplex, div_le_one (by positivity)]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m)

/-- **Stability of the degrees of freedom in the sup norm**: `|ℓ_{g,i}(ω)| ≤ D h_Nᵏ sup_T |ω|`
for a face `g` of a mesh simplex `T` and a continuous form `ω`. -/
theorem abs_dof_le {k : ℕ} {D : ℝ} (hD : CoeffBound S n k D) {N : ℕ}
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (i : S.DofIdx g k) (ω : contForms n)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ T.closedInterior, ∀ s, |(ω : FormField n) x s| ≤ B) :
    |S.dof g k i ω| ≤ D * hN N ^ k * B := by
  have hne := i.2
  have hg : #g = (#g - 1) + 1 := (Nat.succ_pred_eq_of_pos (card_pos.2 hne)).symm
  set q := lexEnum g (#g - 1)
  set η := (S.testBasis k (#g - 1) i.1 : FormField (#g - 1))
  rw [S.dof_eq_integral]
  have hD0 : 0 ≤ D * hN N ^ k := by
    obtain ⟨ξ, hξ⟩ : (FiniteElement.refSimplex (#g - 1)).Nonempty :=
      ⟨0, fun a => by
        refine Fin.cases ?_ (fun l => ?_) a
        · simp
        · simp [refBary]⟩
    exact (Finset.sum_nonneg fun s _ => abs_nonneg _).trans (hD N hT hgT i ξ hξ)
  have hpt : ∀ ξ ∈ FiniteElement.refSimplex (#g - 1),
      ‖∑ s, (ω : FormField n) (simplexMap q ξ) s * dofCoeff q η k ξ s‖ ≤ D * hN N ^ k * B := by
    intro ξ hξ
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s, |(ω : FormField n) (simplexMap q ξ) s * dofCoeff q η k ξ s|
        ≤ ∑ s, B * |dofCoeff q η k ξ s| := Finset.sum_le_sum fun s _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hB _ (simplexMap_lexEnum_mem hgT hg hξ) s)
            (abs_nonneg _)
      _ = B * ∑ s, |dofCoeff q η k ξ s| := by rw [Finset.mul_sum]
      _ ≤ B * (D * hN N ^ k) := mul_le_mul_of_nonneg_left (hD N hT hgT i ξ hξ) hB0
      _ = D * hN N ^ k * B := by ring
  rw [← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le_const (volume_refSimplex_lt_top _) hpt).trans ?_
  calc D * hN N ^ k * B * volume.real (FiniteElement.refSimplex (#g - 1))
      ≤ D * hN N ^ k * B * 1 :=
        mul_le_mul_of_nonneg_left (volume_real_refSimplex_le_one _) (mul_nonneg hD0 hB0)
    _ = _ := mul_one _

/-- **The local DOF estimate on the mesh simplices**, with one constant:
`h_Nᵏ ‖z(x)‖ ≤ B Σ_{g ⊆ T, i} |ℓ_{g,i}(z)|` for `z ∈ P_{r_k}Λᵏ` (resp. `P_{r_k}⁻Λᵏ`). -/
def DofBound (n k : ℕ) (B : ℝ) : Prop :=
  ∀ (N : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}, T ∈ (mesh n N).simplices →
    ∀ {z : FormField n} (hz : z ∈ S.space n k), ∀ x ∈ T.closedInterior,
      hN N ^ k * ‖z x‖ ≤ B * ∑ p : Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k,
        |S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ⟨z, S.space_le_contForms n k hz⟩|

theorem exists_dofBound (k : ℕ) : ∃ B, 0 ≤ B ∧ DofBound S n k B := by
  obtain ⟨B, hB0, hB⟩ := S.exists_local_dof_bound_uniform (n := n) kuhnSimplex k
  refine ⟨B, hB0, fun N T hT z hz x hx => ?_⟩
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  rw [cubeSimplex_eq] at hx ⊢
  exact hB σ (hN_pos N) _ hz x hx

/-- **The local inverse estimates on the mesh simplices**, with one constant:
`h_N^{n/2} ‖z(x)‖ ≤ A ‖z‖_{L²(T)}` and `h_N^{n/2} h_N ‖z(x) - z(x')‖ ≤ A ‖x - x'‖ ‖z‖_{L²(T)}`. -/
def InvBound (n k : ℕ) (A : ℝ) : Prop :=
  ∀ (N : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}, T ∈ (mesh n N).simplices →
    ∀ z ∈ S.space n k,
      (∀ x ∈ T.closedInterior, √(hN N) ^ n * ‖z x‖ ≤ A * √(formL2Sq T.closedInterior z)) ∧
      (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior,
        √(hN N) ^ n * hN N * ‖z x - z x'‖ ≤ A * ‖x - x'‖ * √(formL2Sq T.closedInterior z))

theorem exists_invBound (k : ℕ) : ∃ A, 0 ≤ A ∧ InvBound S n k A := by
  choose A hA0 hA using fun σ : Equiv.Perm (Fin n) =>
    exists_local_inverse_bound_of_le_polySpace (S.space_le_polySpace k)
      (fun h t _ hu => S.affinePullback_mem_space_scalarMat k h t hu) (kuhnSimplex σ)
  have hle : ∀ σ, A σ ≤ ∑ σ, A σ := fun σ =>
    Finset.single_le_sum (fun σ _ => hA0 σ) (Finset.mem_univ σ)
  refine ⟨∑ σ, A σ, Finset.sum_nonneg fun σ _ => hA0 σ, fun N T hT z hz => ?_⟩
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  rw [cubeSimplex_eq]
  obtain ⟨h1, h2⟩ := hA σ (hN_pos N) _ z hz
  exact ⟨fun x hx => (h1 x hx).trans (mul_le_mul_of_nonneg_right (hle σ) (Real.sqrt_nonneg _)),
    fun x hx x' hx' => (h2 x hx x' hx').trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hle σ) (norm_nonneg _)) (Real.sqrt_nonneg _))⟩

/-! ### Glued fields of an element family -/

section Glue

variable (E : LocalElement n)

/-- **A glued field almost everywhere** (any element family): a.e. point of `Ω` lies in the
interior of a simplex `T'`, where the field is the local field of `T'`. -/
theorem ae_glue_eq_local {M : SimplicialMesh n} {k : ℕ} (u : E.Piecewise M k)
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

/-- **The local mass controls the local fields** of the simplices inside the neighbourhood (any
element family). -/
theorem sum_integral_sq_le_locMass {N k : ℕ} (u : E.Piecewise (mesh n N) k)
    (T' : (mesh n N).simplices) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hsub : (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆
      Metric.cthickening (2 * hN N) T.closedInterior) :
    ∑ s, ∫ y in (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (((u T' : E.space T' k) : FormField n) y s) ^ 2 ≤ locMass (E.glue (mesh n N) k u) T := by
  set z : FormField n := ((u T' : E.space T' k) : FormField n)
  have hdeg : ∀ y, IsDeg k (z y) := E.isDeg_of_mem (u T').2
  rw [sum_eq_sum_formIdx (fun s hs => by
    have : ∀ y, (z y s) ^ 2 = 0 := fun y => by rw [hdeg y s hs]; ring
    simp_rw [this]; simp)]
  refine Finset.sum_le_sum fun s _ => ?_
  have hΩ := (isOpen_mesh_domain n N).measurableSet
  have hae := ae_glue_eq_local E u hΩ
  have hint : interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆ (mesh n N).domain := by
    rw [mesh_domain]; exact interior_closedInterior_subset_cubeDomain T'.2
  rw [integral_closedInterior_eq_interior]
  have heq : ∫ y in interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, (z y s.1) ^ 2 =
      ∫ y in interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        ((mesh n N).domain.indicator ((E.glue (mesh n N) k u s :
          L2 ℝ (mesh n N).domain) : (Fin n → ℝ) → ℝ) y) ^ 2 := by
    refine setIntegral_congr_ae isOpen_interior.measurableSet ?_
    filter_upwards [hae] with y hy hyT
    obtain ⟨T'', hyT'', hval⟩ := hy (hint hyT)
    have : T'' = T' := by
      by_contra hne
      exact Set.disjoint_left.1 ((mesh n N).pairwise_disjoint_interior T''.2 T'.2
        (fun e => hne (Subtype.ext e))) hyT'' hyT
    subst this
    rw [hval s]
  rw [heq]
  refine setIntegral_mono_set (integrable_sq_indicator _).integrableOn
    (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall fun y hy => hsub (interior_subset hy))

end Glue

/-! ### The uniform `L²` bound -/

theorem card_dofs_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    (Fintype.card (Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k) : ℝ) =
      Module.finrank ℝ (S.space n k) := by
  exact_mod_cast S.card_sigma_dofIdx T k

/-- A bound on all the degrees of freedom bounds the local field:
`|z(x)ₛ| ≤ B dim(P) D'` if `h_Nᵏ`-scaled DOFs are `≤ h_Nᵏ D'`. -/
theorem abs_le_of_abs_dof_le {k : ℕ} {B : ℝ} (hB : DofBound S n k B) (hB0 : 0 ≤ B) {N : ℕ}
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices) {z : FormField n}
    (hz : z ∈ S.space n k) {D' : ℝ}
    (hD : ∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ hN N ^ k * D')
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) (s : Finset (Fin n)) :
    |z x s| ≤ B * Module.finrank ℝ (S.space n k) * D' := by
  have hhk : 0 < hN N ^ k := pow_pos (hN_pos N) k
  have h1 := hB N hT hz x hx
  have h2 : ∑ p : Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k,
      |S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ⟨z, S.space_le_contForms n k hz⟩| ≤
      Module.finrank ℝ (S.space n k) * (hN N ^ k * D') := by
    calc _ ≤ ∑ _p : Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k,
          hN N ^ k * D' := Finset.sum_le_sum fun p _ => hD _ (Finset.mem_powerset.1 p.1.2) p.2
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_dofs_eq]
  have h3 : |z x s| ≤ ‖z x‖ := by
    have := norm_le_pi_norm (z x) s; rwa [Real.norm_eq_abs] at this
  refine le_of_mul_le_mul_left ?_ hhk
  calc hN N ^ k * |z x s| ≤ hN N ^ k * ‖z x‖ := mul_le_mul_of_nonneg_left h3 hhk.le
    _ ≤ B * (Module.finrank ℝ (S.space n k) * (hN N ^ k * D')) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hB0)
    _ = hN N ^ k * (B * Module.finrank ℝ (S.space n k) * D') := by ring

/-- **The local `L²` bound of `Q_N = Π_h R`** for the higher-order families:
`‖Q_N x‖²_{L²(T)} ≲ m_T(x)`. -/
theorem sum_integral_sq_interp_le {N k : ℕ} {B D : ℝ} (hB : DofBound S n k B) (hB0 : 0 ≤ B)
    (hD : CoeffBound S n k D) {γ : ℝ}
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p) (hγ1 : γ ≤ 1)
    (x : L2F ℝ (mesh n N).domain (formIdx n k)) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((((polyElement n S).globalInterp (mesh n N) k
        (Submodule.inclusion c1Forms_le_contForms
          (smoothForm p (isOpen_mesh_domain n N).measurableSet k x)) :
          (polyElement n S).Piecewise (mesh n N) k) ⟨T, hT⟩ : (polyElement n S).space T k) :
          FormField n) y s.1) ^ 2 ≤
      2 ^ n * (B * Module.finrank ℝ (S.space n k) * D * 2 ^ k) ^ 2 * (32 / γ) ^ n *
        locMass x T := by
  set h := hN N
  have hh : 0 < h := hN_pos N
  have hγ0 : 0 < γ := hp.gamma_pos
  set hΩ := (isOpen_mesh_domain n N).measurableSet
  set w := smoothForm p hΩ k x
  set z : FormField n := ((((polyElement n S).globalInterp (mesh n N) k
    (Submodule.inclusion c1Forms_le_contForms w) :
      (polyElement n S).Piecewise (mesh n N) k) ⟨T, hT⟩ : (polyElement n S).space T k) :
        FormField n)
  have hz : z ∈ S.space n k := (((polyElement n S).globalInterp (mesh n N) k
    (Submodule.inclusion c1Forms_le_contForms w) :
      (polyElement n S).Piecewise (mesh n N) k) ⟨T, hT⟩).2
  set L := locMass x T
  have hL := locMass_nonneg x T
  set Mρ := 1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) p.bump.rIn)
  have hMρ : Mρ = (32 / (γ * h)) ^ n := by
    simp only [Mρ]
    rw [hp.rIn_eq, volume_real_closedBall_zero (by positivity)]
    rw [one_div, ← inv_pow]
    congr 1
    simp only [h]
    field_simp
    ring
  set A := 2 ^ k * √(Mρ * L)
  have hA0 : 0 ≤ A := by positivity
  -- the smoothed field is bounded by `A` on `T`
  have hw : ∀ y ∈ T.closedInterior, ∀ s, |(w : FormField n) y s| ≤ A := by
    intro y hy s
    refine (abs_smoothForm_le hΩ p k x y s).trans (mul_le_mul (hp.pow_factor_le hγ1 k) ?_
      (Real.sqrt_nonneg _) (by positivity))
    refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s' _ => ?_)
      (by positivity))
    refine setIntegral_mono_set (integrable_sq_indicator _).integrableOn
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun t ht => ?_)
    have hyc : y ∈ closure (cubeDomain n) := by
      rw [← mesh_domain n N]; exact (mesh n N).closedInterior_subset_closure hT hy
    have h1 := hp.norm_dil_sub_le hyc
    have h2 : dist t (p.center + p.factor • (y - p.center)) ≤ γ * h / 32 := by
      have := Metric.mem_closedBall.1 ht; rwa [hp.rOut_eq] at this
    refine Metric.mem_cthickening_of_dist_le t y _ _ hy ?_
    calc dist t y ≤ dist t (p.center + p.factor • (y - p.center)) +
          dist (p.center + p.factor • (y - p.center)) y := dist_triangle _ _ _
      _ ≤ γ * h / 32 + γ * h / 4 := add_le_add h2 (by rw [dist_eq_norm]; exact h1)
      _ ≤ 2 * h := by nlinarith
  -- its degrees of freedom are `O(hᵏ A)`
  have hdof : ∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ h ^ k * (D * A) := by
    intro g hgT i
    have e : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ =
        S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) :=
      (polyElement n S).localDof_globalInterp (mesh n N) k
        (Submodule.inclusion c1Forms_le_contForms w) ⟨T, hT⟩ g hgT i
    rw [e]
    refine (abs_dof_le S hD hT hgT i _ hA0 hw).trans (le_of_eq ?_)
    ring
  -- hence `|z| ≤ B dim D A` on `T`
  have hzb : ∀ y ∈ T.closedInterior, ∀ s, |z y s| ≤ B * Module.finrank ℝ (S.space n k) * (D * A) :=
    fun y hy s => abs_le_of_abs_dof_le S hB hB0 hT hz hdof hy s
  have hzc : Continuous z := (PolyKind.contDiff_of_mem_space hz).continuous
  obtain ⟨m, σ, hmσ⟩ := mem_mesh_simplices.1 hT
  set P := (Module.finrank ℝ (S.space n k) : ℝ)
  have hloc : ∀ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2 ≤
      h ^ n * (B * P * (D * A)) ^ 2 := by
    intro s
    rw [← hmσ]
    refine integral_cubeSimplex_le m σ (f := fun y => (z y s.1) ^ 2)
      (((continuous_apply s.1).comp hzc).pow 2) (fun y hy => ?_) (fun y => sq_nonneg _)
    rw [hmσ] at hy
    have := hzb y hy s.1
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc ∑ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2
      ≤ ∑ _s : formIdx n k, h ^ n * (B * P * (D * A)) ^ 2 := Finset.sum_le_sum fun s _ => hloc s
    _ = Fintype.card (formIdx n k) * (h ^ n * (B * P * (D * A)) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * (h ^ n * (B * P * (D * A)) ^ 2) :=
        mul_le_mul_of_nonneg_right (card_formIdx_le _) (by positivity)
    _ = 2 ^ n * (B * P * D * 2 ^ k) ^ 2 * (h ^ n * Mρ) * L := by
        have hA2 : A ^ 2 = (2 ^ k) ^ 2 * (Mρ * L) := by
          simp only [A]; rw [mul_pow, Real.sq_sqrt (by positivity)]
        rw [show B * P * (D * A) = (B * P * D) * A by ring, mul_pow (B * P * D) A, hA2]; ring
    _ = 2 ^ n * (B * P * D * 2 ^ k) ^ 2 * (32 / γ) ^ n * L := by
        rw [hMρ, ← mul_pow, show h * (32 / (γ * h)) = 32 / γ by field_simp]

/-- **The uniform `L²` bound of the smoothed interpolants** `Q_N = Π_h R_N` of the higher-order
families, for any admissible parameters (`IsAdm`, either family): `‖Q_N x‖ ≤ C ‖x‖` for all `N`,
all degrees and all `x`, with `C` depending only on `n`, `S` and `γ`. -/
theorem exists_norm_smoothedInterp_le {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ (N k : ℕ) (p : SmoothingParam (Fin n → ℝ)), IsAdm γ N p →
      ∀ x : L2F ℝ (mesh n N).domain (formIdx n k),
        ‖(polyElement n S).smoothedInterp (mesh n N) p
          (isOpen_mesh_domain n N).measurableSet k x‖ ≤ C * ‖x‖ := by
  classical
  choose B hB0 hB using fun k : ℕ => exists_dofBound (n := n) S k
  choose D hD0 hD using fun k : ℕ => exists_coeffBound (n := n) S k
  set Cov : ℝ := ((6 ^ n * n.factorial : ℕ) : ℝ)
  set K : ℕ → ℝ := fun k => 2 ^ n * (B k * Module.finrank ℝ (S.space n k) * D k * 2 ^ k) ^ 2 *
    (32 / γ) ^ n * Cov
  have hK : ∀ k, 0 ≤ K k := fun k => by have := hB0 k; have := hD0 k; positivity
  refine ⟨√(∑ k ∈ Finset.range (n + 1), K k), Real.sqrt_nonneg _, fun N k p hp x => ?_⟩
  by_cases hk : n < k
  · have := subsingleton_L2F_of_lt (Ω := (mesh n N).domain) hk
    rw [Subsingleton.elim x 0]
    simp
  push Not at hk
  have hQ := (polyElement n S).smoothedInterp_natCast (mesh n N) p
    (isOpen_mesh_domain n N).measurableSet k x
  set u := (polyElement n S).globalInterp (mesh n N) k (Submodule.inclusion c1Forms_le_contForms
    (smoothForm p (isOpen_mesh_domain n N).measurableSet k x))
  have h1 := norm_sq_pieceL2_le (mesh n N) (mesh n N).domain (fun T => formComp (k := (k : ℤ))
    ((polyElement n S).extendPW (mesh n N) (u : (polyElement n S).Piecewise (mesh n N) k) T))
    (fun T hT s => continuous_formComp ((polyElement n S).contDiff_extendPW (mesh n N) _
      hT).continuous s)
  have h2 : ∑ T ∈ (mesh n N).simplices, ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (formComp (k := (k : ℤ)) ((polyElement n S).extendPW (mesh n N)
        (u : (polyElement n S).Piecewise (mesh n N) k) T) s y) ^ 2 ≤
      ∑ T ∈ (mesh n N).simplices,
        2 ^ n * (B k * Module.finrank ℝ (S.space n k) * D k * 2 ^ k) ^ 2 * (32 / γ) ^ n *
          locMass x T := by
    refine Finset.sum_le_sum fun T hT => ?_
    have e : ∀ s : formIdx n k, ∀ y, formComp (k := (k : ℤ))
        ((polyElement n S).extendPW (mesh n N) (u : (polyElement n S).Piecewise (mesh n N) k) T)
          s y = (((u : (polyElement n S).Piecewise (mesh n N) k) ⟨T, hT⟩ :
            (polyElement n S).space T k) : FormField n) y s.1 := fun s y => by
      change (polyElement n S).extendPW (mesh n N) _ T y s.1 = _
      rw [(polyElement n S).extendPW_of_mem (mesh n N) _ hT]
    simp_rw [e]
    exact sum_integral_sq_interp_le S (hB k) (hB0 k) (hD k) hp hγ1 x hT
  have h3 := sum_locMass_le N x
  have hsq : ‖(polyElement n S).smoothedInterp (mesh n N) p
      (isOpen_mesh_domain n N).measurableSet k x‖ ^ 2 ≤
      (√(∑ k ∈ Finset.range (n + 1), K k) * ‖x‖) ^ 2 := by
    rw [hQ, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun k _ => hK k)]
    refine h1.trans (h2.trans ?_)
    rw [← Finset.mul_sum]
    calc 2 ^ n * (B k * Module.finrank ℝ (S.space n k) * D k * 2 ^ k) ^ 2 * (32 / γ) ^ n *
          ∑ T ∈ (mesh n N).simplices, locMass x T
        ≤ 2 ^ n * (B k * Module.finrank ℝ (S.space n k) * D k * 2 ^ k) ^ 2 * (32 / γ) ^ n *
            (Cov * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = K k * ‖x‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun k _ => hK k)
          (Finset.mem_range.2 (by omega))) (sq_nonneg _)
  exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hsq

/-! ### The closeness estimate on `Vₕ` -/

/-- **Faces through nearby points** (`subset_vertexSet_of_near`, for the lexicographic
parametrization of the face). -/
theorem subset_vertexSet_of_near_lex {N : ℕ} {T T' : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) (hT' : T' ∈ (mesh n N).simplices) {m : ℕ}
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (hg : #g = m + 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) {μ : Fin (m + 1) → ℝ} (hμ : ∀ a, θ ≤ μ a)
    (hμ1 : ∑ a, μ a = 1) {t : Fin n → ℝ} (ht : t ∈ T'.closedInterior)
    (hxt : ‖∑ a, μ a • lexEnum g m a - t‖ < θ * hN N / 2) : g ⊆ vertexSet T' := by
  classical
  set q := lexEnum g m
  have hq := lexEnum_injective hg
  have hqT : ∀ a, q a ∈ vertexSet T := fun a => hgT (lexEnum_mem hg a)
  obtain ⟨m₀, σ, rfl⟩ := mem_mesh_simplices.1 hT
  obtain ⟨m', σ', rfl⟩ := mem_mesh_simplices.1 hT'
  have hj : ∀ a, ∃ j, q a = hN N • (latticePoint (finLattice m₀) + kuhnVertex σ j) := fun a => by
    obtain ⟨j, hj⟩ := mem_vertexSet.1 (hqT a)
    exact ⟨j, by rw [← hj, cubeSimplex_points]⟩
  choose j hj using hj
  set x := ∑ a, μ a • q a
  have hxs : (hN N)⁻¹ • x = latticePoint (finLattice m₀) + ∑ a, μ a • kuhnVertex σ (j a) := by
    have hh := hN_ne_zero N
    simp only [x, hj, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib,
      ← Finset.sum_smul]
    have e1 : (hN N)⁻¹ * ∑ i, μ i * hN N = 1 := by
      rw [← Finset.sum_mul, hμ1]; field_simp
    have e2 : ∀ a, (hN N)⁻¹ * (μ a * hN N) = μ a := fun a => by field_simp
    simp only [e1, e2, one_smul]
  have hsep := isSep_latticePoint_add_sum hθ0.le hθ (finLattice m₀) σ j hμ hμ1
  rw [← hxs] at hsep
  have hx' : x ∈ (cubeSimplex N m' σ').closedInterior := by
    rw [mem_closedInterior_cubeSimplex] at ht ⊢
    refine mem_freudenthalSet_of_isSep hsep ht fun l => ?_
    have h := hN_pos N
    have : ‖(hN N)⁻¹ • x - (hN N)⁻¹ • t‖ < θ / 2 := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 h.le), inv_mul_lt_iff₀ h]
      linarith
    exact lt_of_le_of_lt (by
      have := norm_le_pi_norm ((hN N)⁻¹ • x - (hN N)⁻¹ • t) l
      rwa [Real.norm_eq_abs, Pi.sub_apply] at this) this
  intro v hv
  have : v ∈ Set.range q := by rw [range_lexEnum hg]; exact hv
  obtain ⟨a, rfl⟩ := this
  exact SimplicialMesh.subset_vertexSet_of_mem hT hT' hq hqT
    (fun a => hθ0.trans_le (hμ a)) hμ1 hx' a

/-- **The sampling condition** for the higher-order families: every sample of the smoother outside
`Ω`, near a point of a face `g` with barycentric weights `≥ γ`, forces the degrees of freedom of
the subfaces of `g` to vanish (vacuous for the maximal family; for the minimal family the
vanishing of the boundary DOFs). -/
def SampleOK {N k : ℕ} (γ : ℝ) (p : SmoothingParam (Fin n → ℝ))
    (u : (polyElement n S).Piecewise (mesh n N) k) : Prop :=
  ∀ (T : (mesh n N).simplices) (g : Finset (Fin n → ℝ)),
    g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) → ∀ {m : ℕ}, #g = m + 1 →
    ∀ ξ ∈ FiniteElement.refSimplex m, ξ ∉ nearBdry m γ →
      ∀ t, dist t (p.center + p.factor • (simplexMap (lexEnum g m) ξ - p.center)) <
        p.bump.rOut → t ∉ (mesh n N).domain →
        ∀ g' ⊆ g, ∀ i : S.DofIdx g' k,
          (polyElement n S).localDof T k g' i (u T) = 0

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

variable {γ : ℝ}

open Classical in
/-- **The pointwise estimate of the DOF integrand of `v - Q_N v`** (`v ∈ Vₕ`) for the
higher-order families: at a point `x = F_q(ξ)` of a face `g` of `T` (`q` its lexicographic
parametrization) and for any coefficient vector `c` that only sees the trace on `g`,
`h^{n/2} |Σₛ (v_T - R v)(x)ₛ cₛ| ≤ (Σₛ |cₛ|) A m_T(v)^{1/2} 2^{k+1} · (1 or (k + 1) γ)`,
with the factor `(k + 1) γ` when all barycentric coordinates of `ξ` are `≥ γ`: then every
simplex sampled by the smoother inside `Ω` contains `g`, where the traces of the local fields
agree (`pullback_eq_of_mem_globalSpace`). -/
theorem sqrt_mul_abs_integrand_le {N k : ℕ} {A : ℝ} (hA0 : 0 ≤ A) (hA : InvBound S n k A)
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ2 : γ ≤ 1 / 2) {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpace (mesh n N) k) (hs : SampleOK S γ p u)
    (T : (mesh n N).simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)) {m : ℕ}
    (hg : #g = m + 1) {ξ : Fin m → ℝ} (hξ : ξ ∈ FiniteElement.refSimplex m)
    (c : Finset (Fin n) → ℝ)
    (hc : ∀ α β : Finset (Fin n) → ℝ, IsDeg k α → IsDeg k β →
      pullback (simplexMatrix (lexEnum g m)) α = pullback (simplexMatrix (lexEnum g m)) β →
        ∑ s, α s * c s = ∑ s, β s * c s) :
    √(hN N) ^ n * |∑ s, (((u T : (polyElement n S).space T k) : FormField n)
        (simplexMap (lexEnum g m) ξ) s -
      (smoothForm p (isOpen_mesh_domain n N).measurableSet k
        ((polyElement n S).glue (mesh n N) k u) : FormField n)
        (simplexMap (lexEnum g m) ξ) s) * c s| ≤
      (∑ s, |c s|) * A *
        √(locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)) *
        2 ^ (k + 1) * (if ξ ∈ nearBdry m γ then 1 else (k + 1) * γ) := by
  classical
  have hγ := hp.gamma_pos
  have hγ1 : γ ≤ 1 := by linarith
  set h := hN N
  have hh : 0 < h := hN_pos N
  have hh2 : h ≤ 1 / 2 := hN_le N
  set hΩ := (isOpen_mesh_domain n N).measurableSet
  set v := (polyElement n S).glue (mesh n N) k u
  set q := lexEnum g m
  set x := simplexMap q ξ
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  set L := locMass v (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hL0 : 0 ≤ L := locMass_nonneg _ _
  set R := (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * (if ξ ∈ nearBdry m γ then 1 else (k + 1) * γ)
  have hsq : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  have hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
    simplexMap_lexEnum_mem hgT hg hξ
  have hxc : x ∈ closure (cubeDomain n) := by
    rw [← mesh_domain n N]; exact (mesh n N).closedInterior_subset_closure T.2 hxT
  set ŷ := p.center + p.factor • (x - p.center)
  have hŷ : ‖ŷ - x‖ ≤ γ * h / 4 := hp.norm_dil_sub_le hxc
  have hc0 : 0 < p.factor := p.factor_pos
  have hck : p.factor ^ k ≤ 2 ^ k := hp.pow_factor_le hγ1 k
  have hck0 : 0 ≤ p.factor ^ k := pow_nonneg hc0.le k
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hdef : |1 - p.factor ^ k| ≤ k * 2 ^ k * γ := by
    refine (hp.abs_one_sub_pow_le hγ1 k).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    nlinarith
  have hTinv := hA N T.2 uT huT
  have hLT : formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior uT ≤ L :=
    sum_integral_sq_le_locMass (polyElement n S) u T (self_subset_cthickening _ (by positivity))
  have hsqLT : √(formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior uT) ≤ √L :=
    Real.sqrt_le_sqrt hLT
  have hTs : ∀ y ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
      √h ^ n * |uT y s| ≤ A * √L := fun y hy s => by
    have h1 : |uT y s| ≤ ‖uT y‖ := by
      have := norm_le_pi_norm (uT y) s; rwa [Real.norm_eq_abs] at this
    exact (mul_le_mul_of_nonneg_left h1 hsq.le).trans ((hTinv.1 y hy).trans
      (mul_le_mul_of_nonneg_left hsqLT hA0))
  have hR0 : 0 ≤ (∑ s, |c s|) * A * √L * 2 ^ (k + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Finset.sum_nonneg fun s _ => abs_nonneg _) hA0)
      (Real.sqrt_nonneg _)) (by positivity)
  -- the integrand as a mollified average
  rw [sum_sub_smoothForm_mul_eq hΩ p k v (uT x) c x]
  set G : (Fin n → ℝ) → ℝ := fun t => ∑ s, (uT x s - p.factor ^ k * extField v t s) * c s
  set ρ : (Fin n → ℝ) → ℝ := fun t => p.bump.normed volume (ŷ - t)
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => p.bump.nonneg_normed _
  have hρi : Integrable ρ := (isTest_normed_comp_sub p.bump ŷ).continuous.integrable_of_hasCompactSupport
    (isTest_normed_comp_sub p.bump ŷ).hasCompactSupport
  have hρ1 : ∫ t, ρ t = 1 := integral_normed_comp_sub p.bump ŷ
  have hρG : Integrable fun t => ρ t * G t := by
    have e : (fun t => ρ t * G t) = fun t => ∑ s, ((uT x s * c s) * ρ t -
        (p.factor ^ k * c s) * (extField v t s * ρ t)) := by
      funext t; simp only [G, Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
    rw [e]
    exact integrable_finsetSum _ fun s _ =>
      (hρi.const_mul _).sub ((integrable_extField_mul hΩ v p.bump ŷ s).const_mul _)
  -- the bound of the `T`-term
  have hbT : √h ^ n * ∑ s, |uT x s| * |c s| ≤ (∑ s, |c s|) * A * √L := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun s _ => ?_
    calc √h ^ n * (|uT x s| * |c s|) = (√h ^ n * |uT x s|) * |c s| := by ring
      _ ≤ (A * √L) * |c s| := mul_le_mul_of_nonneg_right (hTs x hxT s) (abs_nonneg _)
      _ = |c s| * A * √L := by ring
  -- the pointwise bound on the support of the mollifier
  have hae := ae_glue_eq_local (polyElement n S) u hΩ
  have hb : ∀ᵐ t ∂volume, ρ t ≠ 0 → |G t| ≤ R / √h ^ n := by
    filter_upwards [hae] with t ht hρt
    have hdist : dist t ŷ < p.bump.rOut := by
      by_contra hcon; push Not at hcon
      exact hρt (normed_eq_zero_of_le p.bump hcon)
    rw [le_div_iff₀ hsq, mul_comm]
    by_cases htΩ : t ∈ (mesh n N).domain
    · obtain ⟨T', htT', hval⟩ := ht htΩ
      set u' : FormField n := ((u T' : (polyElement n S).space T' k) : FormField n)
      have hu' : u' ∈ S.space n k := (u T').2
      have hext : ∀ s, extField v t s = u' t s := by
        intro s
        by_cases hs' : (#s : ℤ) = (k : ℤ)
        · rw [extField, formExt_of_card _ hs']; exact hval ⟨s, hs'⟩
        · have : extField v t s = 0 := by simp [extField, formExt, hs']
          rw [this, PolyKind.isDeg_of_mem_space hu' t s (fun h' => hs' (by rw [h']))]
      have hGt : G t = ∑ s, (uT x s - p.factor ^ k * u' t s) * c s := by
        simp only [G, hext]
      have htT'c : t ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := interior_subset htT'
      have hxt : ‖x - t‖ < γ * h / 2 := by
        have h1 : ‖ŷ - t‖ < γ * h / 32 := by
          rw [← dist_eq_norm, dist_comm, ← hp.rOut_eq]; exact hdist
        calc ‖x - t‖ = ‖(x - ŷ) + (ŷ - t)‖ := by congr 1; abel
          _ ≤ ‖x - ŷ‖ + ‖ŷ - t‖ := norm_add_le _ _
          _ < γ * h / 4 + γ * h / 32 := by
              rw [norm_sub_rev] at hŷ
              exact add_lt_add_of_le_of_lt hŷ h1
          _ ≤ γ * h / 2 := by nlinarith
      have hT'sub : (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆
          Metric.cthickening (2 * h) (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := by
        intro y hy
        obtain ⟨m', σ', hmσ'⟩ := mem_mesh_simplices.1 T'.2
        have hdy : ‖y - t‖ ≤ h := by
          rw [← hmσ'] at hy htT'c; exact norm_sub_le_of_mem_cubeSimplex hy htT'c
        refine Metric.mem_cthickening_of_dist_le y x _ _ hxT ?_
        rw [dist_eq_norm]
        calc ‖y - x‖ = ‖(y - t) + (t - x)‖ := by congr 1; abel
          _ ≤ ‖y - t‖ + ‖t - x‖ := norm_add_le _ _
          _ ≤ h + γ * h / 2 := by rw [norm_sub_rev t x]; exact add_le_add hdy hxt.le
          _ ≤ 2 * h := by nlinarith
      have hL' : formL2Sq (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior u' ≤ L :=
        sum_integral_sq_le_locMass (polyElement n S) u T' hT'sub
      have hT'inv := hA N T'.2 u' hu'
      have hsqL' : √(formL2Sq (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior u') ≤ √L :=
        Real.sqrt_le_sqrt hL'
      have hT's : ∀ y ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
          √h ^ n * |u' y s| ≤ A * √L := fun y hy s => by
        have h1 : |u' y s| ≤ ‖u' y‖ := by
          have := norm_le_pi_norm (u' y) s; rwa [Real.norm_eq_abs] at this
        exact (mul_le_mul_of_nonneg_left h1 hsq.le).trans ((hT'inv.1 y hy).trans
          (mul_le_mul_of_nonneg_left hsqL' hA0))
      rw [hGt]
      by_cases hbad : ξ ∈ nearBdry m γ
      · -- near the boundary of the face: inverse estimates only
        have hR : R = (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * 1 := by
          simp only [R, hbad, ite_true]
        rw [hR]
        calc √h ^ n * |∑ s, (uT x s - p.factor ^ k * u' t s) * c s|
            ≤ √h ^ n * ∑ s, (2 ^ k * (|uT x s| + |u' t s|)) * |c s| := by
              refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun s _ => ?_)) hsq.le
              rw [abs_mul]
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              calc |uT x s - p.factor ^ k * u' t s| ≤ |uT x s| + |p.factor ^ k * u' t s| :=
                    abs_sub _ _
                _ ≤ 2 ^ k * |uT x s| + 2 ^ k * |u' t s| := by
                    rw [abs_mul, abs_of_nonneg hck0]
                    exact add_le_add (le_mul_of_one_le_left (abs_nonneg _) h2k)
                      (mul_le_mul_of_nonneg_right hck (abs_nonneg _))
                _ = 2 ^ k * (|uT x s| + |u' t s|) := by ring
          _ = 2 ^ k * ∑ s, (√h ^ n * |uT x s| + √h ^ n * |u' t s|) * |c s| := by
              rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
          _ ≤ 2 ^ k * ∑ s, (A * √L + A * √L) * |c s| := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ =>
                mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) (by positivity)
              exact add_le_add (hTs x hxT s) (hT's t htT'c s)
          _ = (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * 1 := by
              rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_congr rfl fun s _ => by ring
      · -- away from the boundary of the face: the sampled simplex contains the face
        have hR : R = (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * ((k + 1) * γ) := by
          simp only [R, hbad, ite_false]
        rw [hR]
        have hμ : ∀ a, γ ≤ refBary ξ a := by
          intro a; by_contra hlt; push Not at hlt; exact hbad ⟨a, hlt⟩
        have hx : x = ∑ a, refBary ξ a • q a := simplexMap_eq_sum q ξ
        have hgT' : g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) :=
          subset_vertexSet_of_near_lex T.2 T'.2 hgT hg hγ hγ2 hμ (sum_refBary ξ) htT'c
            (by rw [← hx]; exact hxt)
        have htr : ∑ s, uT x s * c s = ∑ s, u' x s * c s :=
          hc _ _ (PolyKind.isDeg_of_mem_space huT x) (PolyKind.isDeg_of_mem_space hu' x)
            (pullback_eq_of_mem_globalSpace hu T T' hgT hgT' hg ξ)
        have e : ∑ s, (uT x s - p.factor ^ k * u' t s) * c s =
            ∑ s, ((1 - p.factor ^ k) * u' x s + p.factor ^ k * (u' x s - u' t s)) * c s := by
          have e1 : ∑ s, (uT x s - p.factor ^ k * u' t s) * c s =
              ∑ s, uT x s * c s - ∑ s, p.factor ^ k * u' t s * c s := by
            rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
          have e2 : ∑ s, ((1 - p.factor ^ k) * u' x s + p.factor ^ k * (u' x s - u' t s)) * c s =
              ∑ s, u' x s * c s - ∑ s, p.factor ^ k * u' t s * c s := by
            rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
          rw [e1, e2, htr]
        rw [e]
        have hxT' : x ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
          simplexMap_lexEnum_mem hgT' hg hξ
        have hLip : ∀ s, √h ^ n * h * |u' x s - u' t s| ≤ A * ‖x - t‖ * √L := fun s => by
          have h1 : |u' x s - u' t s| ≤ ‖u' x - u' t‖ := by
            have := norm_le_pi_norm (u' x - u' t) s; rwa [Real.norm_eq_abs, Pi.sub_apply] at this
          refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ((hT'inv.2 x hxT' t htT'c).trans
            (mul_le_mul_of_nonneg_left hsqL' (by positivity)))
        calc √h ^ n * |∑ s, ((1 - p.factor ^ k) * u' x s + p.factor ^ k * (u' x s - u' t s)) * c s|
            ≤ √h ^ n * ∑ s, ((k * 2 ^ k * γ) * |u' x s| + 2 ^ k * |u' x s - u' t s|) * |c s| := by
              refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun s _ => ?_)) hsq.le
              rw [abs_mul]
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hdef (abs_nonneg _)
              · rw [abs_mul, abs_of_nonneg hck0]
                exact mul_le_mul_of_nonneg_right hck (abs_nonneg _)
          _ = ∑ s, ((k * 2 ^ k * γ) * (√h ^ n * |u' x s|) +
                2 ^ k * ((√h ^ n * h * |u' x s - u' t s|) / h)) * |c s| := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by field_simp
          _ ≤ ∑ s, ((k * 2 ^ k * γ) * (A * √L) + 2 ^ k * ((A * (γ * h / 2) * √L) / h)) *
                |c s| := by
              refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right
                (add_le_add ?_ (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hh.le)
                  (by positivity))) (abs_nonneg _)
              · exact mul_le_mul_of_nonneg_left (hT's x hxT' s) (by positivity)
              · refine (hLip s).trans ?_
                exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxt.le hA0)
                  (Real.sqrt_nonneg _)
          _ = ∑ s, (2 ^ k * ((k + 1 / 2) * γ) * (A * √L)) * |c s| := by
              refine Finset.sum_congr rfl fun s _ => by field_simp
          _ ≤ ∑ s, (2 ^ (k + 1) * ((k + 1) * γ) * (A * √L)) * |c s| := by
              refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              rw [pow_succ]
              have : 0 ≤ (2 : ℝ) ^ k * γ := by positivity
              nlinarith
          _ = (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * ((k + 1) * γ) := by
              rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_congr rfl fun s _ => by ring
    · -- a sample outside `Ω`: the zero extension vanishes there
      have hext : ∀ s, extField v t s = 0 := fun s => by
        simp [extField, formExt, Set.indicator_of_notMem htΩ]
      have hGt : G t = ∑ s, uT x s * c s := by simp only [G, hext]; simp
      rw [hGt]
      by_cases hbad : ξ ∈ nearBdry m γ
      · have hR : R = (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * 1 := by
          simp only [R, hbad, ite_true]
        rw [hR]
        calc √h ^ n * |∑ s, uT x s * c s| ≤ √h ^ n * ∑ s, |uT x s| * |c s| := by
              refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
                (le_of_eq (Finset.sum_congr rfl fun s _ => abs_mul _ _))) hsq.le
          _ ≤ (∑ s, |c s|) * A * √L := hbT
          _ ≤ (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * 1 := by
              rw [mul_one]
              exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
      · have h0 := hs T g hgT hg ξ hξ hbad t hdist htΩ
        have hpb : pullback (simplexMatrix q) (uT x) = pullback (simplexMatrix q) ((0 : FormField n) x) :=
          S.pullback_eq_of_dof_eq hgT hg huT (Submodule.zero_mem _) (fun g' hg' i => by
            rw [show (⟨(0 : FormField n), S.space_le_contForms n k (Submodule.zero_mem _)⟩ :
              contForms n) = 0 from rfl, map_zero]
            exact h0 g' hg' i) ξ
        have h00 := hc _ _ (PolyKind.isDeg_of_mem_space huT x) (fun s _ => rfl) hpb
        have hz : ∑ s, uT x s * c s = 0 := by rw [h00]; simp
        rw [hz, abs_zero, mul_zero]
        have hR : R = (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * ((k + 1) * γ) := by
          simp only [R, hbad, ite_false]
        rw [hR]
        exact mul_nonneg hR0 (by positivity)
  have hmain := abs_integral_mul_le_of_ae hρ0 hρi hρ1 hρG hb
  rw [le_div_iff₀ hsq, mul_comm] at hmain
  exact hmain

theorem card_le_of_dofIdx {g : Finset (Fin n → ℝ)} {k : ℕ} (i : S.DofIdx g k) : k + 1 ≤ #g := by
  by_contra h
  exact (S.isEmpty_dofIdx_of_card_lt (by omega)).false i

/-- **The DOF error of `Q_N` on `Vₕ`** for the higher-order families: for `v ∈ Vₕ`, a face `g`
of `T` and a degree of freedom `i` of `g`,
`h^{n/2} |ℓ_{g,i}(v_T - R v)| ≤ 3 (n + 1) D 2^{k+1} A γ hᵏ m_T(v)^{1/2}`. -/
theorem sqrt_mul_abs_dof_err_le {N k : ℕ} {A D : ℝ} (hA0 : 0 ≤ A) (hA : InvBound S n k A)
    (hD : CoeffBound S n k D) {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ2 : γ ≤ 1 / 2) {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpace (mesh n N) k) (hs : SampleOK S γ p u)
    (T : (mesh n N).simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (i : S.DofIdx g k) :
    √(hN N) ^ n * |S.dof g k i ⟨((u T : (polyElement n S).space T k) : FormField n),
        S.space_le_contForms n k (u T).2⟩ -
      S.dof g k i (Submodule.inclusion c1Forms_le_contForms
        (smoothForm p (isOpen_mesh_domain n N).measurableSet k
          ((polyElement n S).glue (mesh n N) k u)))| ≤
      3 * (n + 1) * D * 2 ^ (k + 1) * A * γ * hN N ^ k *
        √(locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)) := by
  classical
  have hγ := hp.gamma_pos
  have hne := i.2
  set m := #g - 1
  have hg : #g = m + 1 := (Nat.succ_pred_eq_of_pos (card_pos.2 hne)).symm
  have hkm : k ≤ m := by have := card_le_of_dofIdx S i; omega
  have hmn : m ≤ n := by
    have := Finset.card_le_card hgT
    rw [card_vertexSet] at this; omega
  set q := lexEnum g m
  set η := (S.testBasis k m i.1 : FormField m)
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  set w : c1Forms n := smoothForm p (isOpen_mesh_domain n N).measurableSet k
    ((polyElement n S).glue (mesh n N) k u)
  set L := locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have huc : Continuous uT := (PolyKind.contDiff_of_mem_space huT).continuous
  have hwc : Continuous (w : FormField n) := (mem_c1Forms.1 w.2).continuous
  set F : (Fin m → ℝ) → ℝ := fun ξ =>
    ∑ s, (uT (simplexMap q ξ) s - (w : FormField n) (simplexMap q ξ) s) * dofCoeff q η k ξ s
  have hdc : Continuous fun ξ : Fin m → ℝ => η ξ := S.continuous_testBasis k m i.1
  have hcoef : ∀ s, Continuous fun ξ => dofCoeff q η k ξ s := fun s => by
    simp only [dofCoeff]
    split_ifs
    · simp only [wedgeForm_apply]
      exact continuous_finsetSum _ fun a _ => continuous_const.mul
        ((continuous_apply _).comp hdc)
    · exact continuous_const
  have hFc : Continuous F := continuous_finsetSum _ fun s _ =>
    ((((continuous_apply s).comp (huc.comp (continuous_simplexMap q))).sub
      ((continuous_apply s).comp (hwc.comp (continuous_simplexMap q)))).mul (hcoef s))
  have herr : S.dof g k i ⟨uT, S.space_le_contForms n k huT⟩ -
      S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) =
        ∫ ξ in FiniteElement.refSimplex m, F ξ := by
    rw [← map_sub, S.dof_eq_integral]
    refine setIntegral_congr_fun (measurableSet_refSimplex _) fun ξ _ => ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    rfl
  have hsq : 0 ≤ √(hN N) ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  set Mc := D * hN N ^ k
  have hMc : ∀ ξ ∈ FiniteElement.refSimplex m, ∑ s, |dofCoeff q η k ξ s| ≤ Mc :=
    fun ξ hξ => hD N T.2 hgT i ξ hξ
  have hMc0 : 0 ≤ Mc := by
    have h0 : (0 : Fin m → ℝ) ∈ FiniteElement.refSimplex m := fun a => by
      refine Fin.cases ?_ (fun l => ?_) a
      · simp
      · simp [refBary]
    exact (Finset.sum_nonneg fun s _ => abs_nonneg _).trans (hMc 0 h0)
  set β : (Fin m → ℝ) → ℝ := fun ξ =>
    Mc * A * √L * 2 ^ (k + 1) * ((k + 1) * γ + 2 * (nearBdry m γ).indicator 1 ξ)
  have hpt : ∀ ξ ∈ FiniteElement.refSimplex m, √(hN N) ^ n * |F ξ| ≤ β ξ := by
    intro ξ hξ
    refine (sqrt_mul_abs_integrand_le S hA0 hA hp hγ2 hu hs T hgT hg hξ (dofCoeff q η k ξ)
      (fun α β hα hβ hαβ => sum_mul_dofCoeff_eq_of_pullback_eq q η ξ hα hβ hαβ)).trans ?_
    have h0 : 0 ≤ A * √L * 2 ^ (k + 1) := by positivity
    have h1 : (∑ s, |dofCoeff q η k ξ s|) * A * √L * 2 ^ (k + 1) ≤ Mc * A * √L * 2 ^ (k + 1) := by
      have := mul_le_mul_of_nonneg_right (hMc ξ hξ) h0
      linarith [show (∑ s, |dofCoeff q η k ξ s|) * A * √L * 2 ^ (k + 1) =
        (∑ s, |dofCoeff q η k ξ s|) * (A * √L * 2 ^ (k + 1)) by ring,
        show Mc * A * √L * 2 ^ (k + 1) = Mc * (A * √L * 2 ^ (k + 1)) by ring]
    have hfac : 0 ≤ (if ξ ∈ nearBdry m γ then 1 else (k + 1) * γ : ℝ) := by
      split_ifs <;> positivity
    refine (mul_le_mul_of_nonneg_right h1 hfac).trans ?_
    have h0' : 0 ≤ Mc * A * √L * 2 ^ (k + 1) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ h0'
    by_cases hb : ξ ∈ nearBdry m γ
    · rw [Set.indicator_of_mem hb, Pi.one_apply]; simp only [hb, ↓reduceIte]; nlinarith
    · rw [Set.indicator_of_notMem hb]; simp [hb]
  have hS : MeasurableSet (FiniteElement.refSimplex m) := measurableSet_refSimplex m
  have hfin : volume (FiniteElement.refSimplex m) ≠ ⊤ := (volume_refSimplex_lt_top m).ne
  set c := Mc * A * √L * 2 ^ (k + 1)
  have hβ' : ∀ ξ, β ξ = c * ((k + 1) * γ) + (c * 2) * (nearBdry m γ).indicator 1 ξ := fun ξ => by
    simp only [β, c]; ring
  have hind : IntegrableOn (fun ξ => (nearBdry m γ).indicator (1 : (Fin m → ℝ) → ℝ) ξ)
      (FiniteElement.refSimplex m) :=
    (integrableOn_const hfin).indicator (isOpen_nearBdry m γ).measurableSet
  have hβi : IntegrableOn β (FiniteElement.refSimplex m) := by
    have : IntegrableOn (fun ξ => c * ((k + 1) * γ) + (c * 2) * (nearBdry m γ).indicator 1 ξ)
        (FiniteElement.refSimplex m) := (integrableOn_const hfin).add (hind.const_mul _)
    exact this.congr_fun (fun ξ _ => (hβ' ξ).symm) hS
  have hint : ∫ ξ in FiniteElement.refSimplex m, β ξ =
      c * ((k + 1) * γ * volume.real (FiniteElement.refSimplex m) +
        2 * volume.real (FiniteElement.refSimplex m ∩ nearBdry m γ)) := by
    simp_rw [hβ']
    rw [integral_add (integrableOn_const hfin) (hind.const_mul _), setIntegral_const, smul_eq_mul,
      integral_const_mul (c * 2), integral_indicator_one (isOpen_nearBdry m γ).measurableSet,
      Measure.real, Measure.real, Measure.restrict_apply (isOpen_nearBdry m γ).measurableSet,
      Set.inter_comm]
    simp only [Measure.real]
    ring
  have hvol := volume_real_refSimplex_le_one m
  have hbad := volume_real_nearBdry_le (k := m) hγ.le (by linarith : γ ≤ 1)
  rw [herr]
  have hc0 : 0 ≤ c := by positivity
  calc √(hN N) ^ n * |∫ ξ in FiniteElement.refSimplex m, F ξ|
      ≤ √(hN N) ^ n * ∫ ξ in FiniteElement.refSimplex m, |F ξ| :=
        mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) hsq
    _ = ∫ ξ in FiniteElement.refSimplex m, √(hN N) ^ n * |F ξ| := (integral_const_mul _ _).symm
    _ ≤ ∫ ξ in FiniteElement.refSimplex m, β ξ :=
        setIntegral_mono_on ((hFc.abs.continuousOn.integrableOn_compact
          (isCompact_refSimplex m)).const_mul _) hβi hS hpt
    _ = c * ((k + 1) * γ * volume.real (FiniteElement.refSimplex m) +
        2 * volume.real (FiniteElement.refSimplex m ∩ nearBdry m γ)) := hint
    _ ≤ c * ((k + 1) * γ * 1 + 2 * ((m + 1) * γ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        have : 0 ≤ (k + 1 : ℝ) * γ := by positivity
        nlinarith
    _ ≤ c * (3 * (n + 1) * γ) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        have hk' : (k : ℝ) ≤ n := by exact_mod_cast hkm.trans hmn
        have hm' : (m : ℝ) ≤ n := by exact_mod_cast hmn
        nlinarith
    _ = 3 * (n + 1) * D * 2 ^ (k + 1) * A * γ * hN N ^ k * √L := by simp only [c, Mc]; ring

/-- **The local `L²` error of `Q_N` on `Vₕ`** for the higher-order families:
`‖v - Q_N v‖²_{L²(T)} ≲ γ² m_T(v)`. -/
theorem sum_integral_sq_sub_interp_le {N k : ℕ} {A B D : ℝ} (hA0 : 0 ≤ A) (hA : InvBound S n k A)
    (hB0 : 0 ≤ B) (hB : DofBound S n k B) (hD0 : 0 ≤ D) (hD : CoeffBound S n k D)
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ2 : γ ≤ 1 / 2) {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpace (mesh n N) k) (hs : SampleOK S γ p u)
    (T : (mesh n N).simplices) :
    ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      ((((u T : (polyElement n S).space T k) : FormField n) -
        ((((polyElement n S).globalInterp (mesh n N) k
          (Submodule.inclusion c1Forms_le_contForms
            (smoothForm p (isOpen_mesh_domain n N).measurableSet k
              ((polyElement n S).glue (mesh n N) k u))) :
            (polyElement n S).Piecewise (mesh n N) k) T : (polyElement n S).space T k) :
              FormField n)) y s.1) ^ 2 ≤
      2 ^ n * (B * Module.finrank ℝ (S.space n k) *
        (3 * (n + 1) * D * 2 ^ (k + 1) * A) * γ) ^ 2 *
        locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n) := by
  set h := hN N
  have hh : 0 < h := hN_pos N
  set w := smoothForm p (isOpen_mesh_domain n N).measurableSet k
    ((polyElement n S).glue (mesh n N) k u)
  set Pw : (polyElement n S).space T k := (((polyElement n S).globalInterp (mesh n N) k
    (Submodule.inclusion c1Forms_le_contForms w) : (polyElement n S).Piecewise (mesh n N) k) T)
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  have hPw : (Pw : FormField n) ∈ S.space n k := Pw.2
  set z : FormField n := uT - (Pw : FormField n)
  have hz : z ∈ S.space n k := Submodule.sub_mem _ huT hPw
  set L := locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hL0 : 0 ≤ L := locMass_nonneg _ _
  have hγ := hp.gamma_pos
  set C₁ := 3 * (n + 1) * D * 2 ^ (k + 1) * A
  have hC₁ : 0 ≤ C₁ := by positivity
  have hsq : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  set D' := C₁ * γ * √L / √h ^ n
  have hD'0 : 0 ≤ D' := by positivity
  have hdof : ∀ g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n), ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ h ^ k * D' := by
    intro g hgT i
    have e1 : S.dof g k i ⟨(Pw : FormField n), S.space_le_contForms n k hPw⟩ =
        S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) :=
      (polyElement n S).localDof_globalInterp (mesh n N) k
        (Submodule.inclusion c1Forms_le_contForms w) T g hgT i
    have e : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ =
        S.dof g k i ⟨uT, S.space_le_contForms n k huT⟩ -
          S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) := by
      rw [← e1, ← map_sub]; rfl
    rw [e]
    have h1 := sqrt_mul_abs_dof_err_le S hA0 hA hD hp hγ2 hu hs T hgT i
    have e2 : h ^ k * D' = C₁ * γ * h ^ k * √L / √h ^ n := by
      simp only [D']; ring
    rw [e2, le_div_iff₀ hsq, mul_comm]
    exact h1
  have hzb : ∀ y ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
      |z y s| ≤ B * Module.finrank ℝ (S.space n k) * D' :=
    fun y hy s => abs_le_of_abs_dof_le S hB hB0 T.2 hz hdof hy s
  have hzc : Continuous z := (PolyKind.contDiff_of_mem_space hz).continuous
  obtain ⟨m, σ, hmσ⟩ := mem_mesh_simplices.1 T.2
  set P := (Module.finrank ℝ (S.space n k) : ℝ)
  have hloc : ∀ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (z y s.1) ^ 2 ≤ h ^ n * (B * P * D') ^ 2 := by
    intro s
    rw [← hmσ]
    refine integral_cubeSimplex_le m σ (f := fun y => (z y s.1) ^ 2)
      (((continuous_apply s.1).comp hzc).pow 2) (fun y hy => ?_) (fun y => sq_nonneg _)
    rw [hmσ] at hy
    have := hzb y hy s.1
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hhn : h ^ n = (√h ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hh.le]
  calc ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        (z y s.1) ^ 2
      ≤ ∑ _s : formIdx n k, h ^ n * (B * P * D') ^ 2 :=
        Finset.sum_le_sum fun s _ => hloc s
    _ = Fintype.card (formIdx n k) * (h ^ n * (B * P * D') ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * (h ^ n * (B * P * D') ^ 2) :=
        mul_le_mul_of_nonneg_right (card_formIdx_le _) (by positivity)
    _ = 2 ^ n * (B * P * C₁ * γ) ^ 2 * (√L) ^ 2 := by
        rw [hhn]; simp only [D']; field_simp
    _ = 2 ^ n * (B * P * C₁ * γ) ^ 2 * L := by rw [Real.sq_sqrt hL0]

/-- **`Q_N` is close to the identity on `Vₕ`** for the higher-order families:
`‖v - Q_N v‖² ≤ 2ⁿ (B dim(P) C₁ γ)² 6ⁿ n! ‖v‖²`, `C₁ = 3 (n + 1) D 2^{k+1} A`. -/
theorem norm_sq_sub_smoothedInterp_le {N k : ℕ} {A B D : ℝ} (hA0 : 0 ≤ A) (hA : InvBound S n k A)
    (hB0 : 0 ≤ B) (hB : DofBound S n k B) (hD0 : 0 ≤ D) (hD : CoeffBound S n k D)
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ2 : γ ≤ 1 / 2) {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpace (mesh n N) k) (hs : SampleOK S γ p u) :
    ‖(polyElement n S).glue (mesh n N) k u - (polyElement n S).smoothedInterp (mesh n N)
        p (isOpen_mesh_domain n N).measurableSet k
        ((polyElement n S).glue (mesh n N) k u)‖ ^ 2 ≤
      2 ^ n * (B * Module.finrank ℝ (S.space n k) *
        (3 * (n + 1) * D * 2 ^ (k + 1) * A) * γ) ^ 2 *
        ((6 ^ n * n.factorial : ℕ) * ‖(polyElement n S).glue (mesh n N) k u‖ ^ 2) := by
  set v := (polyElement n S).glue (mesh n N) k u
  have hQ := (polyElement n S).smoothedInterp_natCast (mesh n N) p
    (isOpen_mesh_domain n N).measurableSet k v
  set Pw := (polyElement n S).globalInterp (mesh n N) k (Submodule.inclusion c1Forms_le_contForms
    (smoothForm p (isOpen_mesh_domain n N).measurableSet k v))
  set d : (polyElement n S).Piecewise (mesh n N) k :=
    u - (Pw : (polyElement n S).Piecewise (mesh n N) k)
  have hsub : v - (polyElement n S).smoothedInterp (mesh n N) p
      (isOpen_mesh_domain n N).measurableSet k v = (polyElement n S).glue (mesh n N) k d := by
    rw [hQ, map_sub]
  have hglue : (polyElement n S).glue (mesh n N) k d = pieceL2 (mesh n N) (mesh n N).domain
      (fun T => formComp (k := (k : ℤ)) ((polyElement n S).extendPW (mesh n N) d T))
      (fun T hT s => continuous_formComp ((polyElement n S).contDiff_extendPW (mesh n N) _
        hT).continuous s) := rfl
  have h1 := norm_sq_pieceL2_le (mesh n N) (mesh n N).domain (fun T => formComp (k := (k : ℤ))
    ((polyElement n S).extendPW (mesh n N) d T))
    (fun T hT s => continuous_formComp ((polyElement n S).contDiff_extendPW (mesh n N) _
      hT).continuous s)
  set C := 2 ^ n * (B * Module.finrank ℝ (S.space n k) *
    (3 * (n + 1) * D * 2 ^ (k + 1) * A) * γ) ^ 2
  have h2 : ∑ T ∈ (mesh n N).simplices, ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (formComp (k := (k : ℤ)) ((polyElement n S).extendPW (mesh n N) d T) s y) ^ 2 ≤
      ∑ T ∈ (mesh n N).simplices, C * locMass v T := by
    refine Finset.sum_le_sum fun T hT => ?_
    have e : ∀ s : formIdx n k, ∀ y, formComp (k := (k : ℤ))
        ((polyElement n S).extendPW (mesh n N) d T) s y =
        ((((u ⟨T, hT⟩ : (polyElement n S).space T k) : FormField n) -
          (((Pw : (polyElement n S).Piecewise (mesh n N) k) ⟨T, hT⟩ :
            (polyElement n S).space T k) : FormField n)) y s.1) := fun s y => by
      change (polyElement n S).extendPW (mesh n N) d T y s.1 = _
      rw [(polyElement n S).extendPW_of_mem (mesh n N) _ hT]
      rfl
    simp_rw [e]
    exact sum_integral_sq_sub_interp_le S hA0 hA hB0 hB hD0 hD hp hγ2 hu hs ⟨T, hT⟩
  have h3 := sum_locMass_le N v
  rw [hsub, hglue]
  refine h1.trans (h2.trans ?_)
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

/-! ### The smoothing scale, uniformly for all small `γ` -/

/-- `K (x γ)² ≤ ¼` for every `0 ≤ γ ≤ 1 / (2 (1 + S K))` and `0 ≤ x ≤ S`. -/
theorem sq_le_quarter_of_le {S K x γ : ℝ} (hS : 0 ≤ S) (hK : 1 ≤ K) (hx0 : 0 ≤ x) (hx : x ≤ S)
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / (2 * (1 + S * K))) : K * (x * γ) ^ 2 ≤ 1 / 4 := by
  refine le_trans ?_ (sq_le_quarter hS hK hx0 hx)
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  exact pow_le_pow_left₀ (mul_nonneg hx0 hγ0) (mul_le_mul_of_nonneg_left hγ hx0) 2

variable (n) in
/-- **The smoothing scale for the higher-order families, for all small `γ`**: there is
`γ₀ ∈ (0, ½]`, depending only on `n` and the sequence `S`, such that for **every** `γ ∈ (0, γ₀]`,
every admissible parameter at scale `γ` (either family) and every global field satisfying the
sampling condition, `‖v - Q_N v‖ ≤ ½ ‖v‖`. -/
theorem exists_gamma₀ :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ γ : ℝ, γ ≤ γ₀ → ∀ (N k : ℕ)
      (p : SmoothingParam (Fin n → ℝ)), IsAdm γ N p →
      ∀ u ∈ (polyElement n S).globalSpace (mesh n N) k, SampleOK S γ p u →
        ‖(polyElement n S).glue (mesh n N) k u - (polyElement n S).smoothedInterp (mesh n N) p
          (isOpen_mesh_domain n N).measurableSet k ((polyElement n S).glue (mesh n N) k u)‖ ≤
          1 / 2 * ‖(polyElement n S).glue (mesh n N) k u‖ := by
  classical
  choose A hA0 hA using fun k : ℕ => exists_invBound (n := n) S k
  choose B hB0 hB using fun k : ℕ => exists_dofBound (n := n) S k
  choose D hD0 hD using fun k : ℕ => exists_coeffBound (n := n) S k
  set x : ℕ → ℝ := fun k => B k * Module.finrank ℝ (S.space n k) *
    (3 * (n + 1) * D k * 2 ^ (k + 1) * A k)
  have hx0 : ∀ k, 0 ≤ x k := fun k => by
    have := hA0 k; have := hB0 k; have := hD0 k; positivity
  set S' := ∑ k ∈ Finset.range (n + 1), x k
  have hS : 0 ≤ S' := Finset.sum_nonneg fun k _ => hx0 k
  set K : ℝ := 2 ^ n * ((6 ^ n * n.factorial : ℕ) : ℝ)
  have hK : 1 ≤ K := one_le_cov
  set γ₀ := 1 / (2 * (1 + S' * K)) with hγe
  have hpos : 0 < 1 + S' * K := by nlinarith
  have hγ₀ : 0 < γ₀ := by positivity
  have hγ₀2 : γ₀ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ N k p hp u hu hs => ?_⟩
  have hγ0 := hp.gamma_pos
  by_cases hk : n < k
  · have := subsingleton_L2F_of_lt (Ω := (mesh n N).domain) hk
    rw [Subsingleton.elim ((polyElement n S).glue (mesh n N) k u) 0]; simp
  push Not at hk
  have hxk : x k ≤ S' := Finset.single_le_sum (fun k _ => hx0 k) (Finset.mem_range.2 (by omega))
  have h := norm_sq_sub_smoothedInterp_le S (hA0 k) (hA k) (hB0 k) (hB k) (hD0 k) (hD k) hp
    (hγ.trans hγ₀2) hu hs
  have hq := sq_le_quarter_of_le hS hK (hx0 k) hxk hγ0.le hγ
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (h.trans ?_)
  calc 2 ^ n * (x k * γ) ^ 2 *
        (((6 ^ n * n.factorial : ℕ) : ℝ) * ‖(polyElement n S).glue (mesh n N) k u‖ ^ 2)
      = K * (x k * γ) ^ 2 * ‖(polyElement n S).glue (mesh n N) k u‖ ^ 2 := by ring
    _ ≤ 1 / 4 * ‖(polyElement n S).glue (mesh n N) k u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hq (sq_nonneg _)
    _ = (1 / 2 * ‖(polyElement n S).glue (mesh n N) k u‖) ^ 2 := by ring

variable (n) in
/-- **The smoothing scale of the Whitney family, for all small `γ`** (the form of
`FEM.exists_gamma` with every `γ ∈ (0, γ₀]`), so that one smoother serves the Whitney and the
higher-order families at once. -/
theorem exists_gamma₀_whitney :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ γ : ℝ, γ ≤ γ₀ → ∀ (N k : ℕ)
      (p : SmoothingParam (Fin n → ℝ)), IsAdm γ N p →
      ∀ u ∈ (whitneyElement n).globalSpace (mesh n N) k, FEM.SampleOK γ p u →
        ‖(whitneyElement n).glue (mesh n N) k u - (whitneyElement n).smoothedInterp (mesh n N) p
          (isOpen_mesh_domain n N).measurableSet k ((whitneyElement n).glue (mesh n N) k u)‖ ≤
          1 / 2 * ‖(whitneyElement n).glue (mesh n N) k u‖ := by
  classical
  choose A hA0 hA using fun k : ℕ => FEM.exists_invBound (n := n) k
  choose B hB0 hB using fun k : ℕ => FEM.exists_dofBound (n := n) k
  set x : ℕ → ℝ := fun k => B k * (3 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A k)
  have hx0 : ∀ k, 0 ≤ x k := fun k => mul_nonneg (hB0 k) (by have := hA0 k; positivity)
  set S' := ∑ k ∈ Finset.range (n + 1), x k
  have hS : 0 ≤ S' := Finset.sum_nonneg fun k _ => hx0 k
  set K : ℝ := 2 ^ n * ((6 ^ n * n.factorial : ℕ) : ℝ)
  have hK : 1 ≤ K := one_le_cov
  set γ₀ := 1 / (2 * (1 + S' * K)) with hγe
  have hpos : 0 < 1 + S' * K := by nlinarith
  have hγ₀ : 0 < γ₀ := by positivity
  have hγ₀2 : γ₀ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ N k p hp u hu hs => ?_⟩
  have hγ0 := hp.gamma_pos
  by_cases hk : n < k
  · have := subsingleton_L2F_of_lt (Ω := (mesh n N).domain) hk
    rw [Subsingleton.elim ((whitneyElement n).glue (mesh n N) k u) 0]; simp
  push Not at hk
  have hxk : x k ≤ S' := Finset.single_le_sum (fun k _ => hx0 k) (Finset.mem_range.2 (by omega))
  have h := FEM.norm_sq_sub_smoothedInterp_le (hA0 k) (hA k) (hB k) hp (hγ.trans hγ₀2) hu hs
  have hq := sq_le_quarter_of_le hS hK (hx0 k) hxk hγ0.le hγ
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (h.trans ?_)
  calc 2 ^ n * (x k * γ) ^ 2 *
        (((6 ^ n * n.factorial : ℕ) : ℝ) * ‖(whitneyElement n).glue (mesh n N) k u‖ ^ 2)
      = K * (x k * γ) ^ 2 * ‖(whitneyElement n).glue (mesh n N) k u‖ ^ 2 := by ring
    _ ≤ 1 / 4 * ‖(whitneyElement n).glue (mesh n N) k u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hq (sq_nonneg _)
    _ = (1 / 2 * ‖(whitneyElement n).glue (mesh n N) k u‖) ^ 2 := by ring

/-! ### The sampling condition for both families -/

/-- **The maximal family samples only inside `Ω`**, so the sampling condition holds for every
field. -/
theorem sampleOK_pMax {γ : ℝ} {hγ : 0 < γ} {hγ1 : γ ≤ 1} {N k : ℕ}
    (u : (polyElement n S).Piecewise (mesh n N) k) :
    SampleOK S γ (pMax (n := n) γ hγ hγ1 N) u := by
  intro T g hgT m hg ξ hξ _ t ht htΩ
  exfalso
  have hxT := simplexMap_lexEnum_mem hgT hg hξ
  have hxc : simplexMap (lexEnum g m) ξ ∈ closure (mesh n N).domain :=
    (mesh n N).closedInterior_subset_closure T.2 hxT
  have hp := pMax_isMaximal (n := n) (γ := γ) (hγ := hγ) (hγ1 := hγ1) N
  have := closedBall_dil_subset_of_starBall (starBall_mesh n N)
    (pMax (n := n) γ hγ hγ1 N).half_le_factor hp.factor_lt_one hp.rOut_lt hxc
  rw [← hp.center_eq] at this
  exact htΩ (this (Metric.mem_closedBall.2 ht.le))

/-- Points of a face of a mesh simplex with weights `≥ θ` are `θ`-separated in lattice
coordinates (lexicographic parametrization). -/
theorem isSep_inv_smul_of_face_lex {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {m : ℕ} {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T)
    (hg : #g = m + 1) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) {μ : Fin (m + 1) → ℝ}
    (hμ : ∀ a, θ ≤ μ a) (hμ1 : ∑ a, μ a = 1) :
    IsSep θ ((hN N)⁻¹ • ∑ a, μ a • lexEnum g m a) := by
  classical
  set q := lexEnum g m
  have hqT : ∀ a, q a ∈ vertexSet T := fun a => hgT (lexEnum_mem hg a)
  obtain ⟨m₀, σ, rfl⟩ := mem_mesh_simplices.1 hT
  have hj : ∀ a, ∃ j, q a = hN N • (latticePoint (finLattice m₀) + kuhnVertex σ j) := fun a => by
    obtain ⟨j, hj⟩ := mem_vertexSet.1 (hqT a)
    exact ⟨j, by rw [← hj, cubeSimplex_points]⟩
  choose j hj using hj
  have hxs : (hN N)⁻¹ • ∑ a, μ a • q a =
      latticePoint (finLattice m₀) + ∑ a, μ a • kuhnVertex σ (j a) := by
    have hh := hN_ne_zero N
    simp only [hj, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib,
      ← Finset.sum_smul]
    have e1 : (hN N)⁻¹ * ∑ i, μ i * hN N = 1 := by
      rw [← Finset.sum_mul, hμ1]; field_simp
    have e2 : ∀ a, (hN N)⁻¹ * (μ a * hN N) = μ a := fun a => by field_simp
    simp only [e1, e2, one_smul]
  rw [hxs]
  exact isSep_latticePoint_add_sum hθ0.le hθ (finLattice m₀) σ j hμ hμ1

/-- **The minimal family satisfies the sampling condition on `V̊ₕ`** (higher-order families): a
sample outside `Ω` near a point of a face with weights `≥ γ` forces the face to lie in a boundary
facet, where the DOFs of fields with vanishing boundary DOFs vanish. -/
theorem sampleOK_pMin {γ : ℝ} {hγ : 0 < γ} (hγ2 : γ ≤ 1 / 2) {N k : ℕ}
    {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpace₀ (mesh n N) k) :
    SampleOK S γ (pMin (n := n) γ hγ N) u := by
  classical
  intro T g hgT m hg ξ hξ hgood t ht htΩ
  have hp := pMin_isAdm (n := n) (γ := γ) (hγ := hγ) N
  have hh := hN_pos N
  set h := hN N
  set q := lexEnum g m
  set x := simplexMap q ξ
  have hμ : ∀ a, γ ≤ refBary ξ a := by
    intro a; by_contra hlt; push Not at hlt; exact hgood ⟨a, hlt⟩
  have hx : x = ∑ a, refBary ξ a • q a := simplexMap_eq_sum q ξ
  have hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
    simplexMap_lexEnum_mem hgT hg hξ
  have hxc : x ∈ closure (cubeDomain n) := by
    rw [← mesh_domain n N]; exact (mesh n N).closedInterior_subset_closure T.2 hxT
  have hxt : ‖x - t‖ < γ * h / 2 := by
    have hŷ := hp.norm_dil_sub_le hxc
    have h1 : ‖(pMin (n := n) γ hγ N).center + (pMin (n := n) γ hγ N).factor •
        (x - (pMin (n := n) γ hγ N).center) - t‖ < γ * h / 32 := by
      rw [← dist_eq_norm, dist_comm, ← hp.rOut_eq]; exact ht
    calc ‖x - t‖ = ‖(x - ((pMin (n := n) γ hγ N).center + (pMin (n := n) γ hγ N).factor •
          (x - (pMin (n := n) γ hγ N).center))) + (((pMin (n := n) γ hγ N).center +
            (pMin (n := n) γ hγ N).factor • (x - (pMin (n := n) γ hγ N).center)) - t)‖ := by
          congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ < γ * h / 4 + γ * h / 32 := by
          rw [norm_sub_rev] at hŷ; exact add_lt_add_of_le_of_lt hŷ h1
      _ ≤ γ * h / 2 := by nlinarith
  have hsep := isSep_inv_smul_of_face_lex T.2 hgT hg hγ hγ2 hμ (sum_refBary ξ)
  rw [← hx] at hsep
  have hqT : ∀ a, q a ∈ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) := fun a =>
    hgT (lexEnum_mem hg a)
  have hgq : ∀ v ∈ g, ∃ a, q a = v := fun v hv => by
    have : v ∈ Set.range q := by rw [range_lexEnum hg]; exact hv
    exact this
  have hμp : ∀ a, 0 < refBary ξ a := fun a => hγ.trans_le (hμ a)
  -- `t ∉ Ω`: some coordinate leaves `(0, ½)`
  obtain ⟨i, hi⟩ : ∃ i, ¬ (0 < t i ∧ t i < 1 / 2) := by
    by_contra hcon; push Not at hcon
    exact htΩ (by rw [mesh_domain]; exact fun i _ => hcon i)
  have hxi : |x i - t i| < γ * h / 2 := by
    have := norm_le_pi_norm (x - t) i
    rw [Real.norm_eq_abs, Pi.sub_apply] at this
    exact this.trans_lt hxt
  rw [abs_lt] at hxi
  have hxbox := hxc
  rw [closure_cubeDomain] at hxbox
  have hx01 := hxbox i (Set.mem_univ i)
  have hXi : ((hN N)⁻¹ • x) i = x i / h := by
    simp [div_eq_inv_mul, h]
  obtain ⟨m₀, σ, hmσ⟩ := mem_mesh_simplices.1 T.2
  have hgT' : g ⊆ vertexSet (cubeSimplex N m₀ σ) := by rw [hmσ]; exact hgT
  have hgne : g.Nonempty := Finset.card_pos.1 (by rw [hg]; omega)
  obtain ⟨T'', hT'', F, hF, hFT'', hgF⟩ : ∃ T'' ∈ (mesh n N).simplices, ∃ F,
      (mesh n N).IsBoundaryFacet F ∧ F ⊆ vertexSet T'' ∧ g ⊆ F := by
    by_cases hlow : t i ≤ 0
    · -- the lower face
      have hx0 : x i = 0 := by
        rcases hsep.1 i 0 with e | e
        · rw [hXi] at e; push_cast at e
          rcases (div_eq_zero_iff.1 e) with e' | e'
          · exact e'
          · exact absurd e' hh.ne'
        · exfalso
          rw [hXi] at e; push_cast at e
          rw [sub_zero, abs_of_nonneg (div_nonneg hx01.1 hh.le), le_div_iff₀ hh] at e
          nlinarith
      refine exists_boundaryFacet_of_lower m₀ σ i hgT' (fun v hv => ?_) hgne
      obtain ⟨a, rfl⟩ := hgq v hv
      refine eq_of_sum_smul_apply_eq hμp (sum_refBary ξ) (fun b => ?_) (by rw [← hx]; exact hx0) a
      have := (apply_mem_Icc_of_mem_vertexSet T.2 (hqT b) i).1; linarith
    · -- the upper face
      have hup : 1 / 2 ≤ t i := by
        by_contra h'; push Not at h'; exact hi ⟨by push Not at hlow; exact hlow, h'⟩
      have hhN : h * ((N : ℝ) + 1) = 1 / 2 := by
        simp only [h]; unfold hN; push_cast; field_simp
      have hx1 : x i = 1 / 2 := by
        rcases hsep.1 i (N + 1) with e | e
        · rw [hXi] at e; push_cast at e
          rw [div_eq_iff hh.ne'] at e; rw [e, mul_comm]; exact hhN
        · exfalso
          rw [hXi] at e; push_cast at e
          have hx2 := hx01.2
          have hle : x i / h ≤ N + 1 := by
            rw [div_le_iff₀ hh]; linarith [hhN, mul_comm h ((N : ℝ) + 1)]
          have hgt : (N : ℝ) + 1 - γ / 2 < x i / h := by
            rw [lt_div_iff₀ hh]
            have : (N : ℝ) + 1 - γ / 2 = ((N : ℝ) + 1) - γ / 2 := rfl
            nlinarith [hhN, mul_comm h ((N : ℝ) + 1)]
          rw [abs_of_nonpos (by linarith)] at e
          linarith
      refine exists_boundaryFacet_of_upper m₀ σ i hgT' (fun v hv => ?_) hgne
      obtain ⟨a, rfl⟩ := hgq v hv
      have h1 := eq_of_sum_smul_apply_eq (q := fun a => -q a) (i := i) (c := -(1 / 2)) hμp
        (sum_refBary ξ)
        (fun b => by have := (apply_mem_Icc_of_mem_vertexSet T.2 (hqT b) i).2; simp; linarith)
        (by
          have : (∑ a, refBary ξ a • -q a) = -(∑ a, refBary ξ a • q a) := by
            simp [Finset.sum_neg_distrib]
          rw [this, ← hx, Pi.neg_apply, hx1]) a
      simp only [Pi.neg_apply, neg_inj] at h1
      exact h1
  -- the boundary DOFs vanish
  intro g' hg' j
  have h0 := hu.2 ⟨T'', hT''⟩ F hF hFT'' g' (hg'.trans hgF) j
  rw [hu.1 T ⟨T'', hT''⟩ g' (hg'.trans hgT) ((hg'.trans hgF).trans hFT'') j]
  exact h0

end Poly

/-! ### The higher-order complexes of the cube and their smoothed interpolants -/

variable [NeZero n]

instance (S : PolySeq) (M : SimplicialMesh n) (hΩ : IsOpen M.domain) (k : ℤ) :
    FiniteDimensional ℝ ((S.subcomplex M hΩ).V k) :=
  inferInstanceAs (FiniteDimensional ℝ ((polyElement n S).V M k))

instance (S : PolySeq) (M : SimplicialMesh n) (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain)
    (k : ℤ) : FiniteDimensional ℝ ((S.subcomplexMin M hΩ x₀ hstar).V k) :=
  inferInstanceAs (FiniteDimensional ℝ ((polyElement n S).V₀ M k))

variable (n) in
/-- **The finite element complex of the admissible sequence `S`** on the level-`(N + 1)`
Freudenthal mesh of the cube (`P_{r_k}Λᵏ` / `P_{r_k}⁻Λᵏ` in degree `k`), as a subcomplex of
`HΛ(Q)`. -/
def poly (S : PolySeq) (N : ℕ) : (complex n).Subcomplex :=
  (deRham ℝ n).maximalSubcomplexOfEq (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n) (S.subcomplex (mesh n N) (isOpen_mesh_domain n N))

instance (S : PolySeq) (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((poly n S N).V k) :=
  (deRham ℝ n).finiteDimensional_maximalSubcomplexOfEq _ _ _ _ k

variable (n) in
/-- **The finite element complex of `S` with vanishing boundary DOFs** on the level-`(N + 1)`
Freudenthal mesh of the cube, as a subcomplex of `H̊Λ(Q)`. -/
def polyMin (S : PolySeq) (N : ℕ) : (complexMin n).Subcomplex :=
  (deRham ℝ n).minimalSubcomplexOfEq (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    (S.subcomplexMin (mesh n N) (isOpen_mesh_domain n N) (center n) (strictStar_mesh n N))

instance (S : PolySeq) (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((polyMin n S N).V k) :=
  (deRham ℝ n).finiteDimensional_minimalSubcomplexOfEq _ _ _ _ k

variable (n) in
/-- **The smoothed canonical interpolant** `Q_N = Π_h R` of the complex of `S` on the cube, for
maximal-family smoothing parameters centred at the centre of the cube. -/
def polySmoothed (S : PolySeq) (N : ℕ) (p : SmoothingParam (Fin n → ℝ))
    (hp : p.IsMaximal (center n) (1 / 4)) : (poly n S N).CommutingMap :=
  (deRham ℝ n).commutingMapOfEq (mesh_domain n N) (isOpen_mesh_domain n N) (isOpen_cubeDomain n)
    ((polyElement n S).smoothedCommutingMap (mesh n N) p (isOpen_mesh_domain n N)
      (starBall_mesh n N) hp)

variable (n) in
/-- **The smoothed canonical interpolant with vanishing boundary DOFs** `Q̊_N = Π_h R` of the
complex of `S` on the cube, for minimal-family smoothing parameters. -/
def polySmoothedMin (S : PolySeq) (N : ℕ) (p : SmoothingParam (Fin n → ℝ))
    (hp : p.IsMinimal (center n) (1 / 4)) : (polyMin n S N).CommutingMap :=
  (deRham ℝ n).commutingMapOfEqMin (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    ((polyElement n S).smoothedCommutingMapMin (mesh n N) p (isOpen_mesh_domain n N)
      (mesh_domain n N ▸ isBounded_cubeDomain n) (starBall_mesh n N) hp (center n)
      (strictStar_mesh n N))

variable (n) in
/-- **The estimates of the smoothed interpolants of the complex of `S`** ([AFW2010], §5.4;
[ChristiansenWinther2008]): for maximal-family parameters `p N`, uniform `L²` bounds of `Q_N`
and `‖v - Q_N v‖ ≤ ½ ‖v‖` on `Vₕ`, normalized by `½ ≤ C` (the analogue of
`FEM.SmoothingEstimates` for the Whitney complex). -/
structure PolySmoothingEstimates (S : PolySeq) (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ) :
    Prop where
  isMaximal : ∀ N, (p N).IsMaximal (center n) (1 / 4)
  half_le : 1 / 2 ≤ C
  bound : ∀ N i x, ‖(polySmoothed n S N (p N) (isMaximal N)).Q i x‖ ≤ C * ‖x‖
  close : ∀ N i, ∀ v ∈ (poly n S N).V i,
    ‖v - (polySmoothed n S N (p N) (isMaximal N)).Q i v‖ ≤ 1 / 2 * ‖v‖

variable (n) in
/-- **The estimates of the smoothed interpolants with vanishing boundary DOFs** of the complex of
`S` (the analogue of `FEM.SmoothingEstimatesMin`). -/
structure PolySmoothingEstimatesMin (S : PolySeq) (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ) :
    Prop where
  isMinimal : ∀ N, (p N).IsMinimal (center n) (1 / 4)
  half_le : 1 / 2 ≤ C
  bound : ∀ N i x, ‖(polySmoothedMin n S N (p N) (isMinimal N)).Q i x‖ ≤ C * ‖x‖
  close : ∀ N i, ∀ v ∈ (polyMin n S N).V i,
    ‖v - (polySmoothedMin n S N (p N) (isMinimal N)).Q i v‖ ≤ 1 / 2 * ‖v‖

omit [NeZero n] in
theorem norm_eq_zero_negSucc {Ω : Set (Fin n → ℝ)} (k : ℕ)
    (y : L2F ℝ Ω (formIdx n (Int.negSucc k))) : ‖y‖ = 0 := by
  have := LocalElement.subsingleton_L2F_negSucc Ω (n := n) k
  rw [Subsingleton.elim y 0, norm_zero]

theorem smoothedCommutingMapMin_Q_eq (E : LocalElement n) {M : SimplicialMesh n}
    (p : SmoothingParam (Fin n → ℝ))
    (hΩo : IsOpen M.domain) (hb : Bornology.IsBounded M.domain) {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMinimal x₀ s₀) (y₀ : Fin n → ℝ)
    (hstar' : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → y₀ + t • (x - y₀) ∈ M.domain)
    (i : ℤ) :
    (E.smoothedCommutingMapMin M p hΩo hb hstar hp y₀ hstar').Q i =
      E.smoothedInterp M p hΩo.measurableSet i := rfl

/-- **The smoothed-projection estimates hold for every admissible sequence, for all small `γ`**
([AFW2010], §5.4; [ChristiansenWinther2008]): there is `γ₀ ∈ (0, ½]` depending only on `n` and
`S` such that for **every** `γ ∈ (0, γ₀]` the parameters `pMax γ` (dilation factor
`1 - γ h_N` about the centre, bump radii `γ h_N / 64 < γ h_N / 32`) satisfy the estimates, with
a constant `C` depending on `γ`. -/
theorem polySmoothingEstimates_pMax (S : PolySeq) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1), γ ≤ γ₀ →
      ∃ C, PolySmoothingEstimates n S (pMax γ hγ hγ1) C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, hclose⟩ := Poly.exists_gamma₀ n S
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ hγ1 hγγ₀ => ?_⟩
  obtain ⟨C, hC0, hbound⟩ := Poly.exists_norm_smoothedInterp_le (n := n) S hγ hγ1
  refine ⟨max C (1 / 2), ?_⟩
  have hest : ∀ N, (∀ i x, ‖(polySmoothed n S N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i x‖ ≤
      max C (1 / 2) * ‖x‖) ∧ (∀ i, ∀ v ∈ (poly n S N).V i,
        ‖v - (polySmoothed n S N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i v‖ ≤
          1 / 2 * ‖v‖) := by
    intro N
    refine commutingMapOfEq_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · exact (hbound N k _ (pMax_isAdm N) x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · obtain ⟨u, rfl⟩ := hv
        exact hclose γ hγγ₀ N k _ (pMax_isAdm N) u.1 u.2 (Poly.sampleOK_pMax S _)
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  exact ⟨fun N => pMax_isMaximal N, le_max_right _ _, fun N => (hest N).1,
    fun N => (hest N).2⟩

/-- **The smoothed-projection estimates with vanishing boundary DOFs hold for every admissible
sequence, for all small `γ`**: as `polySmoothingEstimates_pMax`, for the parameters `pMin γ`
(dilation factor `1 + γ h_N` towards the centre). -/
theorem polySmoothingEstimatesMin_pMin (S : PolySeq) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ), γ ≤ γ₀ →
      ∃ C, PolySmoothingEstimatesMin n S (pMin γ hγ) C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, hclose⟩ := Poly.exists_gamma₀ n S
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ hγγ₀ => ?_⟩
  have hγ2 : γ ≤ 1 / 2 := hγγ₀.trans hγ₀2
  have hγ1 : γ ≤ 1 := by linarith
  obtain ⟨C, hC0, hbound⟩ := Poly.exists_norm_smoothedInterp_le (n := n) S hγ hγ1
  refine ⟨max C (1 / 2), ?_⟩
  have hest : ∀ N, (∀ i x, ‖(polySmoothedMin n S N (pMin γ hγ N) (pMin_isMinimal N)).Q i x‖ ≤
      max C (1 / 2) * ‖x‖) ∧ (∀ i, ∀ v ∈ (polyMin n S N).V i,
        ‖v - (polySmoothedMin n S N (pMin γ hγ N) (pMin_isMinimal N)).Q i v‖ ≤
          1 / 2 * ‖v‖) := by
    intro N
    refine commutingMapOfEqMin_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rw [smoothedCommutingMapMin_Q_eq]
      rcases i with k | k
      · exact (hbound N k _ (pMin_isAdm N) x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
    · rw [smoothedCommutingMapMin_Q_eq]
      rcases i with k | k
      · obtain ⟨u, rfl⟩ := hv
        exact hclose γ hγγ₀ N k _ (pMin_isAdm N) u.1
          ((polyElement n S).globalSpace₀_le (mesh n N) k u.2) (Poly.sampleOK_pMin S hγ2 u.2)
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  exact ⟨fun N => pMin_isMinimal N, le_max_right _ _, fun N => (hest N).1,
    fun N => (hest N).2⟩

/-- **The Whitney smoothing estimates for all small `γ`** (`FEM.smoothingEstimates_pMax` fixes
one `γ`): for every `γ ∈ (0, γ₀]` the parameters `pMax γ` satisfy `FEM.SmoothingEstimates`. -/
theorem smoothingEstimates_pMax_forall :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1), γ ≤ γ₀ →
      ∃ C, SmoothingEstimates n (pMax γ hγ hγ1) C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, hclose⟩ := Poly.exists_gamma₀_whitney n
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ hγ1 hγγ₀ => ?_⟩
  obtain ⟨C, hC0, hbound⟩ := exists_norm_smoothedInterp_le (n := n) hγ hγ1
  refine ⟨max C (1 / 2), ?_⟩
  have hest : ∀ N, (∀ i x, ‖(smoothed n N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i x‖ ≤
      max C (1 / 2) * ‖x‖) ∧ (∀ i, ∀ v ∈ (whitney n N).V i,
        ‖v - (smoothed n N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i v‖ ≤ 1 / 2 * ‖v‖) := by
    intro N
    refine commutingMapOfEq_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · exact (hbound N k _ (pMax_isAdm N) x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · obtain ⟨u, rfl⟩ := hv
        exact hclose γ hγγ₀ N k _ (pMax_isAdm N) u.1 u.2 (sampleOK_pMax _)
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  exact ⟨fun N => pMax_isMaximal N, le_max_right _ _, fun N => (hest N).1,
    fun N => (hest N).2⟩

/-- **The Whitney smoothing estimates with vanishing boundary DOFs for all small `γ`**. -/
theorem smoothingEstimatesMin_pMin_forall :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ), γ ≤ γ₀ →
      ∃ C, SmoothingEstimatesMin n (pMin γ hγ) C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, hclose⟩ := Poly.exists_gamma₀_whitney n
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ hγγ₀ => ?_⟩
  have hγ2 : γ ≤ 1 / 2 := hγγ₀.trans hγ₀2
  have hγ1 : γ ≤ 1 := by linarith
  obtain ⟨C, hC0, hbound⟩ := exists_norm_smoothedInterp_le (n := n) hγ hγ1
  refine ⟨max C (1 / 2), ?_⟩
  have hest : ∀ N, (∀ i x, ‖(smoothedMin n N (pMin γ hγ N) (pMin_isMinimal N)).Q i x‖ ≤
      max C (1 / 2) * ‖x‖) ∧ (∀ i, ∀ v ∈ (whitneyMin n N).V i,
        ‖v - (smoothedMin n N (pMin γ hγ N) (pMin_isMinimal N)).Q i v‖ ≤ 1 / 2 * ‖v‖) := by
    intro N
    refine commutingMapOfEqMin_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rw [smoothedCommutingMapMin_Q]
      rcases i with k | k
      · exact (hbound N k _ (pMin_isAdm N) x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
    · rw [smoothedCommutingMapMin_Q]
      rcases i with k | k
      · obtain ⟨u, rfl⟩ := hv
        exact hclose γ hγγ₀ N k _ (pMin_isAdm N) u.1
          ((whitneyElement n).globalSpace₀_le (mesh n N) k u.2) (sampleOK_pMin hγ2 u.2)
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  exact ⟨fun N => pMin_isMinimal N, le_max_right _ _, fun N => (hest N).1,
    fun N => (hest N).2⟩

/-- **One smoother for finitely many families at once**: for a finite family of admissible
sequences `S i` there is `γ₀ > 0` such that for every `γ ∈ (0, γ₀]` the same parameters `pMax γ`
(resp. `pMin γ`) satisfy the smoothing estimates of the Whitney complex and of every complex
`S i`, in both boundary-condition families. -/
theorem exists_common_gamma {ι : Type*} [Finite ι] (S : ι → PolySeq) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1), γ ≤ γ₀ →
      (∃ C, SmoothingEstimates n (pMax γ hγ hγ1) C) ∧
      (∃ C, SmoothingEstimatesMin n (pMin γ hγ) C) ∧
      ∀ i, (∃ C, PolySmoothingEstimates n (S i) (pMax γ hγ hγ1) C) ∧
        ∃ C, PolySmoothingEstimatesMin n (S i) (pMin γ hγ) C := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨γw, hγw, hγw2, hw⟩ := smoothingEstimates_pMax_forall (n := n)
  obtain ⟨γw', hγw', hγw'2, hw'⟩ := smoothingEstimatesMin_pMin_forall (n := n)
  choose γp hγp hγp2 hp using fun i => polySmoothingEstimates_pMax (n := n) (S i)
  choose γq hγq hγq2 hq using fun i => polySmoothingEstimatesMin_pMin (n := n) (S i)
  set G : Finset ℝ := insert γw (insert γw' (Finset.univ.image γp ∪ Finset.univ.image γq))
  have hGne : G.Nonempty := Finset.insert_nonempty _ _
  set γ₀ := G.min' hGne
  have hmem : γ₀ ∈ G := Finset.min'_mem G hGne
  have hle : ∀ x ∈ G, γ₀ ≤ x := fun x hx => Finset.min'_le G x hx
  have hpos : ∀ x ∈ G, 0 < x ∧ x ≤ 1 / 2 := by
    intro x hx
    simp only [G, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hx
    rcases hx with rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨hγw, hγw2⟩
    · exact ⟨hγw', hγw'2⟩
    · exact ⟨hγp i, hγp2 i⟩
    · exact ⟨hγq i, hγq2 i⟩
  refine ⟨γ₀, (hpos _ hmem).1, (hpos _ hmem).2, fun γ hγ hγ1 hγγ₀ => ⟨hw γ hγ hγ1
    (hγγ₀.trans (hle _ (by simp [G]))), hw' γ hγ (hγγ₀.trans (hle _ (by simp [G]))),
    fun i => ⟨hp i γ hγ hγ1 (hγγ₀.trans (hle _ (by simp [G]))),
      hq i γ hγ (hγγ₀.trans (hle _ (by simp [G])))⟩⟩⟩

end Feec.Models.Cube.FEM
