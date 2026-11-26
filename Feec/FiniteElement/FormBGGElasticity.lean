module

public import Feec.FiniteElement.FormBGG

/-!
# The elasticity diagram of differential forms on `ℝ³`

The elasticity diagram of [ArnoldHu2021], §4.1 stacks `HΛ(Ω) ⊗ ℝ³` over itself, `Ω ⊆ ℝ³` open; its
regular decompositions follow from those of `HΛ(Ω)`, and `S¹` is not onto between the `L²` domains.

## Main results

* `elasticityFormData_regularDecomposition`: the regular decompositions of the diagram.
* `elasticityFormData_exists_forall_S_ne`: `S¹` is not onto between the `L²` domains.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Finset
open MeasureTheory

@[expose] public noncomputable section

namespace Feec.FiniteElement

open Feec.Domain

variable {Ω : Set (Fin 3 → ℝ)}

/-! ### Indices mod `3` -/

theorem fin3_add_add (i : Fin 3) :
    i + 1 + 1 = i + 2 ∧ i + 1 + 2 = i ∧ i + 2 + 1 = i ∧ i + 2 + 2 = i + 1 := by
  fin_cases i <;> decide

theorem fin3_ne (i : Fin 3) : i + 1 ≠ i ∧ i + 2 ≠ i ∧ i + 2 ≠ i + 1 := by
  fin_cases i <;> decide

theorem sum_fin3 {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) (i : Fin 3) :
    ∑ c, f c = f i + f (i + 1) + f (i + 2) := by
  fin_cases i <;> simp [Fin.sum_univ_three] <;> abel

/-! ### The elasticity map and its adjoint -/

/-- The elasticity connecting map `(S μ)_b = dx_{b+2} ∧ μ_{b+1} − dx_{b+1} ∧ μ_{b+2}`. -/
def crossL2 (k : ℤ) : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 k)) →L[ℝ]
    PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (k + 1))) :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin 3 =>
      L2F ℝ Ω (formIdx 3 (k + 1))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun b =>
      dxL2 k (b + 2) ∘L PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 k)) (b + 1) -
        dxL2 k (b + 1) ∘L PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 k)) (b + 2)

@[simp] theorem crossL2_apply (k : ℤ) (μ : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 k)))
    (b : Fin 3) : crossL2 k μ b = dxL2 k (b + 2) (μ (b + 1)) - dxL2 k (b + 1) (μ (b + 2)) :=
  rfl

/-- The adjoint of `crossL2`, `(Sᵀ w)_i = ι_{i+1} w_{i+2} − ι_{i+2} w_{i+1}`. -/
def crossAdj (k : ℤ) : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (k + 1))) →L[ℝ]
    PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 k)) :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin 3 =>
      L2F ℝ Ω (formIdx 3 k)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i =>
      ιL2 k (i + 1) ∘L
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (k + 1))) (i + 2) -
        ιL2 k (i + 2) ∘L
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (k + 1))) (i + 1)

@[simp] theorem crossAdj_apply (k : ℤ) (w : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (k + 1))))
    (i : Fin 3) : crossAdj k w i = ιL2 k (i + 1) (w (i + 2)) - ιL2 k (i + 2) (w (i + 1)) :=
  rfl

theorem inner_crossL2 (k : ℤ) (μ : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 k)))
    (w : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (k + 1)))) :
    ⟪crossL2 k μ, w⟫_ℝ = ⟪μ, crossAdj k w⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_three, crossL2_apply, crossAdj_apply, Fin.isValue, Fin.reduceAdd,
    inner_sub_left, inner_sub_right, inner_dxL2]
  ring

theorem inner_dxVecL2 {n : ℕ} {Ω : Set (Fin n → ℝ)} (k : ℤ) (φ : L2F ℝ Ω (formIdx n k))
    (w : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n (k + 1)))) :
    ⟪dxVecL2 k φ, w⟫_ℝ = ⟪φ, dxVecAdj k w⟫_ℝ := by
  rw [PiLp.inner_apply, dxVecAdj_eq_sum, inner_sum]
  exact Finset.sum_congr rfl fun c _ => inner_dxL2 k c φ (w c)

/-! ### The Gram identities -/

theorem crossAdj_crossL2 (k : ℤ) (μ : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (k + 1)))) :
    crossAdj (k + 1) (crossL2 (k + 1) μ) = ((1 : ℝ) - k) • μ + dxVecL2 k (dxVecAdj k μ) := by
  refine PiLp.ext fun i => ?_
  obtain ⟨e1, e2, e3, e4⟩ := fin3_add_add i
  obtain ⟨n1, n2, n3⟩ := fin3_ne i
  have hE := sum_dxL2_ιL2 k (μ i)
  rw [sum_fin3 _ i] at hE
  simp only [crossAdj_apply, crossL2_apply, map_sub, e1, e2, e3, e4, PiLp.add_apply,
    PiLp.smul_apply, dxVecL2_apply, dxVecAdj_eq_sum, ιL2_dxL2, n1, n2, ite_true, ite_false]
  rw [sum_fin3 _ i, map_add, map_add]
  linear_combination (norm := module) -hE

theorem crossAdj_crossL2_zero (μ : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 0))) :
    crossAdj 0 (crossL2 0 μ) = (2 : ℝ) • μ := by
  refine PiLp.ext fun i => ?_
  obtain ⟨e1, e2, e3, e4⟩ := fin3_add_add i
  obtain ⟨n1, n2, n3⟩ := fin3_ne i
  simp only [crossAdj_apply, crossL2_apply, map_sub, e1, e2, e3, e4, PiLp.smul_apply,
    ιL2_dxL2_zero, n1, n2, ite_true, ite_false]
  module

theorem crossL2_crossAdj (k : ℤ) (w : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (k + 1)))) :
    crossL2 k (crossAdj k w) = (k : ℝ) • w + wsL2Adj (k + 1) (wsL2 (k + 1) w) := by
  refine PiLp.ext fun b => ?_
  obtain ⟨e1, e2, e3, e4⟩ := fin3_add_add b
  obtain ⟨n1, n2, n3⟩ := fin3_ne b
  have hD := sum_ιL2_dxL2 (k + 1) (w b)
  rw [sum_fin3 _ b] at hD
  have c1 := ιL2_dxL2_add_dxL2_ιL2 k (b + 2) (b + 2) (w b)
  have c2 := ιL2_dxL2_add_dxL2_ιL2 k b (b + 2) (w (b + 2))
  have c3 := ιL2_dxL2_add_dxL2_ιL2 k b (b + 1) (w (b + 1))
  have c4 := ιL2_dxL2_add_dxL2_ιL2 k (b + 1) (b + 1) (w b)
  simp only [ite_true, n2.symm, n1.symm, ite_false] at c1 c2 c3 c4
  simp only [crossL2_apply, crossAdj_apply, map_sub, e1, e2, e3, e4, PiLp.add_apply,
    PiLp.smul_apply, ← ιL2_eq, wsL2_eq_sum]
  rw [sum_fin3 _ b, map_add, map_add]
  linear_combination (norm := module) c1 - c2 - c3 + c4 - hD

/-! ### The elasticity diagram -/

theorem crossL2_crossL2 (k : ℤ) (v : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 k))) :
    crossL2 (k + 1) (crossL2 k v) = -dxVecL2 (k + 1) (wsL2 k v) := by
  refine PiLp.ext fun b => ?_
  obtain ⟨h1, h2, h3, h4⟩ := fin3_add_add b
  rw [crossL2_apply, crossL2_apply, crossL2_apply, PiLp.neg_apply, dxVecL2_apply, wsL2_eq_sum,
    map_sum, sum_fin3 _ b, h1, h2, h3, h4, map_sub, map_sub, dxL2_dxL2_self, dxL2_dxL2_self,
    dxL2_dxL2_self, eq_neg_of_add_eq_zero_left (dxL2_dxL2_add_dxL2_dxL2 k (b + 2) b (v (b + 2))),
    eq_neg_of_add_eq_zero_left (dxL2_dxL2_add_dxL2_dxL2 k (b + 1) b (v (b + 1)))]
  abel

variable (hΩ : IsOpen Ω)
include hΩ

/-- The elasticity diagram of forms, `HΛ(Ω) ⊗ ℝ³` over itself ([ArnoldHu2021], §4.1). -/
def elasticityFormData : BGG.HilbertData ℝ (ComplexShape.up ℤ)
    (fun k => PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 k)))
    (fun k => PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 k))) :=
  BGG.HilbertData.ofSucc (vecRow 3 hΩ) (vecRow 3 hΩ) (fun k => crossL2 k)
    (fun k φ => (mem_vecRow_domain hΩ).2 fun b => by
      rw [crossL2_apply]
      exact Submodule.sub_mem _
        (dxL2_mem_maximal hΩ k _ ((mem_vecRow_domain hΩ).1 φ.2 _)).1
        (dxL2_mem_maximal hΩ k _ ((mem_vecRow_domain hΩ).1 φ.2 _)).1)
    (fun k φ => PiLp.ext fun b => by
      have hφ := (mem_vecRow_domain hΩ).1 φ.2
      obtain ⟨h1, e1⟩ := dxL2_mem_maximal hΩ k (b + 2) (hφ (b + 1))
      obtain ⟨h2, e2⟩ := dxL2_mem_maximal hΩ k (b + 1) (hφ (b + 2))
      refine (vecRow_d_apply hΩ _ b).trans ?_
      refine (LinearPMap.apply_eq_of_eq rfl _
        ((⟨_, h1⟩ : ((extDerivOp ℝ 3 (k + 1)).maximal Ω).domain) - ⟨_, h2⟩) rfl).trans ?_
      rw [LinearPMap.map_sub, e1, e2, PiLp.neg_apply, crossL2_apply, vecRow_d_apply,
        vecRow_d_apply]
      abel)

@[simp] theorem elasticityFormData_S (k : ℤ) : (elasticityFormData hΩ).S k (k + 1) = crossL2 k :=
  BGG.HilbertData.succCLM_succ (X := fun k => PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 k)))
    (Y := fun k => PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 k))) (fun k => crossL2 k) k

omit hΩ in
theorem norm_le_norm_crossL2_one (μ : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (0 + 1)))) :
    ‖μ‖ ≤ ‖crossL2 (0 + 1) μ‖ := by
  have h := crossAdj_crossL2 0 μ
  have hsq : ‖crossL2 (0 + 1) μ‖ ^ 2 = ‖μ‖ ^ 2 + ‖dxVecAdj 0 μ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_crossL2, h, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm, inner_dxVecL2, real_inner_self_eq_norm_sq]
    push_cast
    ring
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [hsq]
  nlinarith [sq_nonneg ‖dxVecAdj 0 μ‖]

theorem elasticityFormData_antilipschitz :
    ∀ i ≤ 1, ∃ K, AntilipschitzWith K ((elasticityFormData hΩ).S i (i + 1)) := by
  intro i hi
  rw [elasticityFormData_S]
  rcases lt_trichotomy i 0 with hi0 | rfl | hi0
  · have := subsingleton_vec_formIdx (Ω := Ω) (n := 3) hi0
    exact ⟨0, AntilipschitzWith.of_subsingleton⟩
  · refine ⟨_, ((2 : ℝ)⁻¹ • crossAdj 0).lipschitzWith.to_rightInverse fun μ => ?_⟩
    rw [_root_.smul_apply, crossAdj_crossL2_zero, smul_smul,
      inv_mul_cancel₀ two_ne_zero, one_smul]
  · obtain rfl : i = 0 + 1 := by omega
    exact ⟨1, (crossL2 (0 + 1)).antilipschitz_of_bound fun μ => by
      rw [NNReal.coe_one, one_mul]
      exact norm_le_norm_crossL2_one μ⟩

theorem crossAdj_mem_fieldH1 (k : ℤ) {w : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (k + 1)))}
    (hw : ∀ b, w b ∈ fieldH1 ℝ Ω (formIdx 3 (k + 1))) (i : Fin 3) :
    crossAdj k w i ∈ fieldH1 ℝ Ω (formIdx 3 k) := by
  rw [crossAdj_apply, ιL2_eq, ιL2_eq]
  exact Submodule.sub_mem _ (wsL2Adj_mem_fieldH1 hΩ k (hw _) _) (wsL2Adj_mem_fieldH1 hΩ k (hw _) _)

omit hΩ in
theorem crossL2_crossAdj_one (w : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (1 + 1)))) :
    crossL2 1 (crossAdj 1 (w - (4 : ℝ)⁻¹ • wsL2Adj (1 + 1) (wsL2 (1 + 1) w))) = w := by
  have h := crossL2_crossAdj (Ω := Ω) 1 (w - (4 : ℝ)⁻¹ • wsL2Adj (1 + 1) (wsL2 (1 + 1) w))
  have h3 : wsL2 (1 + 1) (wsL2Adj (1 + 1) (wsL2 (1 + 1) w)) =
      ((1 + 1 : ℤ) + 1 : ℝ) • wsL2 (1 + 1) w :=
    wsL2_wsL2Adj (1 + 1) _
  rw [h, map_sub, map_sub, map_smul, map_smul, h3, map_smul]
  push_cast
  module

omit hΩ in
theorem crossL2_crossAdj_two (w : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (2 + 1)))) :
    crossL2 2 ((2 : ℝ)⁻¹ • crossAdj 2 w) = w := by
  have h := crossL2_crossAdj (Ω := Ω) 2 w
  have : Subsingleton (L2F ℝ Ω (formIdx 3 (2 + 1 + 1))) :=
    have : IsEmpty (formIdx 3 (2 + 1 + 1)) := ⟨fun s => by
      have h1 := s.2
      have h2 : #s.1 ≤ 3 := by simpa using Finset.card_le_univ s.1
      omega⟩
    ⟨fun _ _ => PiLp.ext fun s => isEmptyElim s⟩
  rw [Subsingleton.elim (wsL2 (2 + 1) w) 0, map_zero, add_zero] at h
  rw [map_smul, h, smul_smul]
  norm_num

theorem elasticityFormData_exists_add_eq (h : (deRham ℝ 3).HasRegularDecomposition Ω 1) {i : ℤ}
    (hi : 1 ≤ i) {u : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (i + 1)))}
    (hu : u ∈ ((vecRow 3 hΩ).d (i + 1) (i + 1 + 1)).domain) :
    ∃ (p : ((vecRow 3 hΩ).d i (i + 1)).domain) (φ : ((vecRow 3 hΩ).d i (i + 1)).domain),
      (vecRow 3 hΩ).d i (i + 1) p + (elasticityFormData hΩ).S i (i + 1) φ = u := by
  rcases lt_trichotomy i 2 with hi2 | rfl | hi2
  · obtain rfl : i = 1 := by omega
    obtain ⟨p, hp, hw⟩ := vecRow_exists_sub_mem_fieldH1 h le_rfl ((mem_vecRow_domain hΩ).1 hu)
    have hpm : p ∈ ((vecRow 3 hΩ).d 1 (1 + 1)).domain := (mem_vecRow_domain hΩ).2 hp
    set w := u - (vecRow 3 hΩ).d 1 (1 + 1) ⟨p, hpm⟩
    have hwa : ∀ a, w a ∈ fieldH1 ℝ Ω (formIdx 3 (1 + 1)) := fun a => by
      simp only [w, PiLp.sub_apply, vecRow_d_apply]
      exact hw a
    set v := w - (4 : ℝ)⁻¹ • wsL2Adj (1 + 1) (wsL2 (1 + 1) w)
    have hva : ∀ a, v a ∈ fieldH1 ℝ Ω (formIdx 3 (1 + 1)) := fun a =>
      Submodule.sub_mem _ (hwa a)
        (Submodule.smul_mem _ _ (wsL2Adj_mem_fieldH1 hΩ _ (wsL2_mem_fieldH1 hΩ _ hwa) a))
    have hφ : crossAdj 1 v ∈ ((vecRow 3 hΩ).d 1 (1 + 1)).domain :=
      (mem_vecRow_domain hΩ).2 fun a =>
        fieldH1_le_extDerivOp_maximal hΩ _ (crossAdj_mem_fieldH1 hΩ 1 hva a)
    refine ⟨⟨p, hpm⟩, ⟨_, hφ⟩, ?_⟩
    rw [elasticityFormData_S]
    change (vecRow 3 hΩ).d 1 (1 + 1) ⟨p, hpm⟩ +
      crossL2 1 (crossAdj 1 (w - (4 : ℝ)⁻¹ • wsL2Adj (1 + 1) (wsL2 (1 + 1) w))) = u
    rw [crossL2_crossAdj_one]
    simp only [w]
    abel
  · obtain ⟨p, hp, hw⟩ := vecRow_exists_sub_mem_fieldH1 h hi ((mem_vecRow_domain hΩ).1 hu)
    have hpm : p ∈ ((vecRow 3 hΩ).d 2 (2 + 1)).domain := (mem_vecRow_domain hΩ).2 hp
    set w := u - (vecRow 3 hΩ).d 2 (2 + 1) ⟨p, hpm⟩
    have hwa : ∀ a, w a ∈ fieldH1 ℝ Ω (formIdx 3 (2 + 1)) := fun a => by
      simp only [w, PiLp.sub_apply, vecRow_d_apply]
      exact hw a
    have hφ : (2 : ℝ)⁻¹ • crossAdj 2 w ∈ ((vecRow 3 hΩ).d 2 (2 + 1)).domain :=
      (mem_vecRow_domain hΩ).2 fun a => fieldH1_le_extDerivOp_maximal hΩ _
        (Submodule.smul_mem _ _ (crossAdj_mem_fieldH1 hΩ 2 hwa a))
    refine ⟨⟨p, hpm⟩, ⟨_, hφ⟩, ?_⟩
    rw [elasticityFormData_S]
    change (vecRow 3 hΩ).d 2 (2 + 1) ⟨p, hpm⟩ + crossL2 2 ((2 : ℝ)⁻¹ • crossAdj 2 w) = u
    rw [crossL2_crossAdj_two]
    simp only [w]
    abel
  · -- above degree `2` the target spaces are zero
    have : IsEmpty (formIdx 3 (i + 1)) := ⟨fun s => by
      have h1 := s.2
      have h2 : #s.1 ≤ 3 := by simpa using Finset.card_le_univ s.1
      omega⟩
    have hu0 : u = 0 := PiLp.ext fun a => PiLp.ext fun s => isEmptyElim s
    refine ⟨0, 0, ?_⟩
    rw [hu0, LinearPMap.map_zero, ZeroMemClass.coe_zero, map_zero, add_zero]

/-- The regular decompositions of the elasticity diagram, from those of `HΛ(Ω)` from `1` on. -/
theorem elasticityFormData_regularDecomposition
    (h : (deRham ℝ 3).HasRegularDecomposition Ω 1) :
    (elasticityFormData hΩ).RegularDecomposition 1 :=
  (elasticityFormData hΩ).regularDecomposition_of_forall_exists fun _ hi _ hu =>
    elasticityFormData_exists_add_eq hΩ h hi hu

/-! ### `S¹` is not onto between the `L²` domains -/

theorem elasticityFormData_exists_lt_norm (hne : Ω.Nonempty) (C : ℝ) :
    ∃ φ : ((elasticityFormData hΩ).Ht.d (0 + 1) (0 + 1 + 1)).domain,
      (elasticityFormData hΩ).H.d (0 + 1 + 1) (0 + 1 + 1 + 1)
          ⟨_, (elasticityFormData hΩ).S_mapsTo (0 + 1) (0 + 1 + 1) (0 + 1 + 1 + 1) φ⟩ = 0 ∧
        C * ‖(φ : PiLp 2 fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 (0 + 1)))‖ <
          ‖(elasticityFormData hΩ).Ht.d (0 + 1) (0 + 1 + 1) φ‖ := by
  obtain ⟨K₁, hK₁⟩ := elasticityFormData_antilipschitz hΩ (0 + 1) (by norm_num)
  rw [elasticityFormData_S] at hK₁
  set S₀ : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 0)) →L[ℝ] _ := crossL2 0
  obtain ⟨ψ, hdψ, hlt⟩ := hessianFormData_exists_lt_norm hΩ hne (by norm_num : 0 < 3)
    (max C 0 * ‖S₀‖ * K₁)
  set D := elasticityFormData hΩ
  have hmem := D.S_mapsTo 0 (0 + 1) (0 + 1 + 1) ψ
  have hd : D.H.d (0 + 1) (0 + 1 + 1) ⟨_, hmem⟩ = -crossL2 (0 + 1) (D.Ht.d 0 (0 + 1) ψ) := by
    rw [D.anticomm 0 (0 + 1) (0 + 1 + 1) ψ, elasticityFormData_S]
  have hW := (hessianFormData hΩ).anticomm 0 (0 + 1) (0 + 1 + 1) ψ
  rw [hdψ, hessianFormData_S, eq_comm, neg_eq_zero] at hW
  have hW' : wsL2 (0 + 1) (D.Ht.d 0 (0 + 1) ψ) = 0 := hW
  have e : D.Ht.d (0 + 1) (0 + 1 + 1) ⟨_, hmem⟩ = -crossL2 (0 + 1) (D.Ht.d 0 (0 + 1) ψ) := hd
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · rw [D.anticomm (0 + 1) (0 + 1 + 1) (0 + 1 + 1 + 1) ⟨_, hmem⟩, elasticityFormData_S, e,
      map_neg, neg_neg, crossL2_crossL2, hW', map_zero, neg_zero]
  · rw [e, norm_neg]
    have h1 := (crossL2 (0 + 1)).bound_of_antilipschitz hK₁ (D.Ht.d 0 (0 + 1) ψ)
    have h2 : ‖S₀ (ψ : PiLp 2 fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 0))‖ ≤ ‖S₀‖ * ‖(ψ : _)‖ :=
      S₀.le_opNorm _
    have hlt' : max C 0 * ‖S₀‖ * K₁ * ‖(ψ : PiLp 2 fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 0))‖ <
        ‖D.Ht.d 0 (0 + 1) ψ‖ := hlt
    have hK0 : (0 : ℝ) ≤ K₁ := K₁.2
    have hC : C * ‖S₀ (ψ : PiLp 2 fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 0))‖ ≤
        max C 0 * ‖S₀‖ * ‖(ψ : _)‖ := by
      calc C * ‖S₀ (ψ : PiLp 2 fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 0))‖
          ≤ max C 0 * ‖S₀ (ψ : PiLp 2 fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 0))‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ max C 0 * (‖S₀‖ * ‖(ψ : _)‖) :=
            mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
        _ = _ := by ring
    have key : K₁ * (max C 0 * ‖S₀‖ * ‖(ψ : _)‖) <
        K₁ * ‖crossL2 (0 + 1) (D.Ht.d 0 (0 + 1) ψ)‖ := by
      calc K₁ * (max C 0 * ‖S₀‖ * ‖(ψ : _)‖) = max C 0 * ‖S₀‖ * K₁ * ‖(ψ : _)‖ := by ring
        _ < ‖D.Ht.d 0 (0 + 1) ψ‖ := hlt'
        _ ≤ _ := h1
    exact hC.trans_lt (lt_of_mul_lt_mul_left key hK0)

/-- `S¹` is not onto between the `L²` domains of the elasticity diagram: on every nonempty open
`Ω ⊆ ℝ³`, some `u ∈ HΛ²(Ω) ⊗ ℝ³` is `S¹ φ` for no `φ ∈ HΛ¹(Ω) ⊗ ℝ³`. -/
theorem elasticityFormData_exists_forall_S_ne (hne : Ω.Nonempty) :
    ∃ u ∈ ((vecRow 3 hΩ).d (1 + 1) (1 + 1 + 1)).domain,
      ∀ φ ∈ ((vecRow 3 hΩ).d 1 (1 + 1)).domain, crossL2 1 φ ≠ u := by
  have h := (elasticityFormData hΩ).exists_forall_S_ne (i := 0 + 1) (j := 0 + 1 + 1)
    (k := 0 + 1 + 1 + 1) rfl rfl
    ((elasticityFormData_antilipschitz hΩ (0 + 1) (by norm_num)).choose_spec.injective)
    (elasticityFormData_exists_lt_norm hΩ hne)
  rw [elasticityFormData_S] at h
  exact h

end Feec.FiniteElement
