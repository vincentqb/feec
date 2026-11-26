module

public import Feec.Algebra.ExteriorFibre
public import Feec.ForMathlib.Calculus.Partial
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Smooth differential forms on `ℝⁿ`: exterior derivative and affine pullback

Form fields on `ℝⁿ` in the basis `dx_s`, with the exterior derivative and the affine pullback.

## Main results

* `ExteriorFibre.wedgeProd_apply_eq_det_submatrix`: the coefficients of wedge products are minors.
* `extDeriv_extDeriv`: `d ∘ d = 0` for `C²` forms.
* `extDeriv_smul_apply`: the Leibniz rule.
* `extDeriv_affinePullback_apply`: `d (F^* ω) = F^* (d ω)` for affine `F`.
-/

open Finset

@[expose] public noncomputable section

namespace Feec.ExteriorFibre

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d]

@[simp] theorem wedge_zero (ξ : d → R) : wedge ξ (0 : Finset d → R) = 0 := by
  funext s; simp [wedge_apply]

@[simp] theorem wedge_zero_left (ω : Finset d → R) : wedge (0 : d → R) ω = 0 := by
  funext s; simp [wedge_apply]

theorem wedge_sum {β : Type*} (ξ : d → R) (u : Finset β) (f : β → Finset d → R) :
    wedge ξ (∑ b ∈ u, f b) = ∑ b ∈ u, wedge ξ (f b) := by
  funext s; simp only [wedge_apply, Finset.sum_apply, mul_sum]
  exact sum_comm

theorem wedge_sum_left {β : Type*} (u : Finset β) (ξ : β → d → R) (ω : Finset d → R) :
    wedge (∑ b ∈ u, ξ b) ω = ∑ b ∈ u, wedge (ξ b) ω := by
  funext s; simp only [wedge_apply, Finset.sum_apply, sum_mul, mul_sum]
  exact sum_comm

theorem wedge_neg_left (ξ : d → R) (ω : Finset d → R) : wedge (-ξ) ω = -wedge ξ ω := by
  rw [show -ξ = (-1 : R) • ξ by simp, wedge_smul_left]; simp

variable {ι : Type*} [LinearOrder ι]

/-- The iterated exterior product `θ_{s₁} ∧ ⋯ ∧ θ_{s_k}` (`s₁ < ⋯ < s_k`) of covectors `θ`. -/
def wedgeProd (θ : ι → d → R) (s : Finset ι) : Finset d → R :=
  (s.sort (· ≤ ·)).foldr (fun j ω => wedge (θ j) ω) (Pi.single ∅ 1)

@[simp] theorem wedgeProd_empty (θ : ι → d → R) : wedgeProd θ ∅ = Pi.single ∅ 1 := by
  simp [wedgeProd]

theorem wedgeProd_insert_of_lt (θ : ι → d → R) {a : ι} {s : Finset ι} (h : ∀ x ∈ s, a < x) :
    wedgeProd θ (insert a s) = wedge (θ a) (wedgeProd θ s) := by
  have ha : a ∉ s := fun h' => lt_irrefl a (h a h')
  rw [wedgeProd, Finset.sort_insert _ (fun b hb => (h b hb).le) ha, List.foldr_cons]
  rfl

theorem wedgeProd_congr {θ θ' : ι → d → R} {s : Finset ι} (h : ∀ j ∈ s, θ j = θ' j) :
    wedgeProd θ s = wedgeProd θ' s := by
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a s ha ih =>
    rw [wedgeProd_insert_of_lt _ ha, wedgeProd_insert_of_lt _ ha, h a (mem_insert_self a s),
      ih fun j hj => h j (mem_insert_of_mem hj)]

theorem wedgeProd_singleton (θ : ι → d → R) (j : ι) :
    wedgeProd θ {j} = wedge (θ j) (Pi.single ∅ 1) := by
  rw [← insert_empty, wedgeProd_insert_of_lt _ (by simp), wedgeProd_empty]

theorem wedgeProd_insert (θ : ι → d → R) {j : ι} {s : Finset ι} (hj : j ∉ s) :
    wedgeProd θ (insert j s) = (sgn j s : R) • wedge (θ j) (wedgeProd θ s) := by
  induction s using Finset.induction_on_min generalizing j with
  | empty => simp [wedgeProd_singleton, sgn]
  | insert a s ha ih =>
    have hja : j ≠ a := fun h => hj (h ▸ mem_insert_self a s)
    have hjs : j ∉ s := fun h => hj (mem_insert_of_mem h)
    have has : a ∉ s := fun h' => lt_irrefl a (ha a h')
    rcases lt_or_gt_of_ne hja with hlt | hlt
    · have hall : ∀ x ∈ insert a s, j < x := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact hlt
        · exact hlt.trans (ha x hx)
      rw [wedgeProd_insert_of_lt _ hall]
      have : sgn j (insert a s) = (1 : R) := by
        rw [sgn, filter_eq_empty_iff.2 fun x hx => not_lt.2 (hall x hx).le]; simp
      rw [this, one_smul]
    · have hall : ∀ x ∈ insert j s, a < x := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact hlt
        · exact ha x hx
      rw [insert_comm, wedgeProd_insert_of_lt _ hall, ih hjs, wedge_smul,
        wedgeProd_insert_of_lt _ ha, sgn_insert has, ite_eq_left_of_eq_true _ _ (eq_true hlt)]
      have := wedge_wedge_add_wedge_wedge (θ a) (θ j) (wedgeProd θ s)
      rw [eq_neg_of_add_eq_zero_left this]
      simp [smul_neg, neg_smul]

theorem wedge_wedgeProd_of_notMem (θ : ι → d → R) {j : ι} {s : Finset ι} (hj : j ∉ s) :
    wedge (θ j) (wedgeProd θ s) = (sgn j s : R) • wedgeProd θ (insert j s) := by
  rw [wedgeProd_insert θ hj, smul_smul, sgn_mul_self, one_smul]

theorem wedge_wedgeProd_of_mem (θ : ι → d → R) {j : ι} {s : Finset ι} (hj : j ∈ s) :
    wedge (θ j) (wedgeProd θ s) = 0 := by
  rw [← insert_erase hj, wedgeProd_insert θ (notMem_erase j s), wedge_smul, wedge_wedge_self,
    smul_zero]

theorem wedgeProd_eq_sgn_smul_wedge_erase (θ : ι → d → R) {j : ι} {s : Finset ι} (hj : j ∈ s) :
    wedgeProd θ s = (sgn j s : R) • wedge (θ j) (wedgeProd θ (s.erase j)) := by
  conv_lhs => rw [← insert_erase hj]
  rw [wedgeProd_insert θ (notMem_erase j s), sgn_erase_self]

theorem wedgeProd_eq_zero_of_mem {θ : ι → d → R} {j : ι} {s : Finset ι} (hj : j ∈ s)
    (h : θ j = 0) : wedgeProd θ s = 0 := by
  rw [wedgeProd_eq_sgn_smul_wedge_erase θ hj, h, wedge_zero_left, smul_zero]

theorem isDeg_wedgeProd (θ : ι → d → R) (s : Finset ι) : IsDeg #s (wedgeProd θ s) := by
  induction s using Finset.induction_on_min with
  | empty =>
    intro t ht
    have : t ≠ ∅ := fun h => ht (by simp [h])
    simp [this]
  | insert a s ha ih =>
    have has : a ∉ s := fun h' => lt_irrefl a (ha a h')
    rw [wedgeProd_insert_of_lt _ ha, card_insert_of_notMem has]
    exact ih.wedge _

theorem wedgeProd_single (s : Finset d) :
    wedgeProd (fun j => (Pi.single j 1 : d → R)) s = Pi.single s 1 := by
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h' => lt_irrefl a (ha a h')
    rw [wedgeProd_insert_of_lt _ ha, ih, wedge_single_single has]
    have : sgn a s = (1 : R) := by
      rw [sgn, filter_eq_empty_iff.2 fun x hx => not_lt.2 (ha x hx).le]; simp
    rw [this, one_smul]

theorem wedgeProd_map {ι' : Type*} [LinearOrder ι'] (θ : ι' → d → R) (e : ι ↪o ι')
    (s : Finset ι) : wedgeProd θ (s.map e.toEmbedding) = wedgeProd (θ ∘ e) s := by
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a s ha ih =>
    rw [map_insert, wedgeProd_insert_of_lt _ ha, wedgeProd_insert_of_lt, ih]
    · rfl
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
      exact e.lt_iff_lt.2 (ha y hy)

/-- The components of `ω` on the coordinates `e(·)`: `(res_e ω)_r = ω_{e(r)}`. -/
def restrict {d' : Type*} [LinearOrder d'] (e : d' ↪o d) (ω : Finset d → R) : Finset d' → R :=
  fun r => ω (r.map e.toEmbedding)

theorem sgn_map {d' : Type*} [LinearOrder d'] (e : d' ↪o d) (j : d') (r : Finset d') :
    (sgn (e j) (r.map e.toEmbedding) : R) = sgn j r := by
  rw [sgn, sgn, filter_map, card_map]
  congr 3
  ext x
  simp [e.lt_iff_lt]

theorem restrict_wedge {d' : Type*} [LinearOrder d'] (e : d' ↪o d) (ξ : d → R)
    (ω : Finset d → R) : restrict e (wedge ξ ω) = wedge (ξ ∘ e) (restrict e ω) := by
  funext r
  simp only [restrict, wedge_apply, sum_map, Function.comp_apply, RelEmbedding.coe_toEmbedding]
  refine sum_congr rfl fun j _ => ?_
  rw [sgn_map]
  congr 2
  rw [Finset.map_erase]
  rfl

theorem restrict_wedgeProd {d' : Type*} [LinearOrder d'] (e : d' ↪o d) (θ : ι → d → R)
    (s : Finset ι) :
    restrict e (wedgeProd θ s) = wedgeProd (fun j => θ j ∘ e) s := by
  induction s using Finset.induction_on_min with
  | empty =>
    funext r
    simp only [restrict, wedgeProd_empty, Pi.single_apply, map_eq_empty]
  | insert a s ha ih =>
    rw [wedgeProd_insert_of_lt _ ha, wedgeProd_insert_of_lt _ ha, restrict_wedge, ih]

section Det

variable [Fintype ι]

omit [Fintype ι] in
theorem wedgeProd_update [DecidableEq ι] (θ : ι → d → R) {i : ι} {s : Finset ι} (hi : i ∈ s)
    (z : d → R) :
    wedgeProd (Function.update θ i z) s = (sgn i s : R) • wedge z (wedgeProd θ (s.erase i)) := by
  rw [wedgeProd_eq_sgn_smul_wedge_erase _ hi, Function.update_self]
  congr 2
  convert wedgeProd_congr (θ := Function.update θ i z) (θ' := θ) (s := s.erase i)
    (fun j hj => Function.update_of_ne (ne_of_mem_erase hj) _ _)

/-- `θ ↦ (θ₁ ∧ ⋯ ∧ θ_m)_{univ}` as an alternating map of the rows. -/
def wedgeProdAlternating : (ι → R) [⋀^ι]→ₗ[R] R where
  toFun θ := wedgeProd θ univ univ
  map_update_add' θ i x y := by
    simp only [wedgeProd_update θ (mem_univ i), wedge_add_left, smul_add, Pi.add_apply]
  map_update_smul' θ i c x := by
    simp only [wedgeProd_update θ (mem_univ i), wedge_smul_left, Pi.smul_apply, smul_eq_mul]
    ring
  map_eq_zero_of_eq' θ i j h hij := by
    change wedgeProd θ univ univ = 0
    rw [wedgeProd_eq_sgn_smul_wedge_erase _ (mem_univ i), h,
      wedge_wedgeProd_of_mem θ (mem_erase.2 ⟨hij.symm, mem_univ j⟩)]
    simp

theorem wedgeProd_univ_apply_univ (θ : ι → ι → R) :
    wedgeProd θ univ univ = (Matrix.of θ).det := by
  have h := (wedgeProdAlternating (R := R) (ι := ι)).eq_smul_basis_det (Pi.basisFun R ι)
  have h1 : wedgeProdAlternating (R := R) (ι := ι) (Pi.basisFun R ι) = 1 := by
    change wedgeProd (fun j => Pi.basisFun R ι j) univ univ = 1
    simp only [Pi.basisFun_apply]
    rw [wedgeProd_single]; simp
  rw [h1, one_smul] at h
  have := congrArg (fun f => f θ) h
  change wedgeProd θ univ univ = _ at this
  rw [this, Pi.basisFun_det_apply]

end Det

/-- **Coefficients are minors**: for `#s = #t = k`, the `dx_t`-coefficient of
`θ_{s₁} ∧ ⋯ ∧ θ_{s_k}` is the `k × k` minor of `θ` on the rows `s` and the columns `t`. -/
theorem wedgeProd_apply_eq_det_submatrix (θ : ι → d → R) {k : ℕ} {s : Finset ι}
    {t : Finset d} (hs : #s = k) (ht : #t = k) :
    wedgeProd θ s t =
      (Matrix.of fun i j : Fin k => θ (s.orderEmbOfFin hs i) (t.orderEmbOfFin ht j)).det := by
  have h1 : wedgeProd θ s = wedgeProd (θ ∘ s.orderEmbOfFin hs) univ := by
    rw [← wedgeProd_map θ (s.orderEmbOfFin hs) univ, map_orderEmbOfFin_univ]
  have h2 : wedgeProd θ s t = restrict (t.orderEmbOfFin ht) (wedgeProd θ s) univ := by
    rw [restrict, map_orderEmbOfFin_univ]
  rw [h2, h1, restrict_wedgeProd]
  exact wedgeProd_univ_apply_univ _

section Pullback

variable [Fintype ι] {κ : Type*} [LinearOrder κ]

/-- The pulled-back covector `(Bᵀ ξ)_l = Σ_i ξ_i B_{il}`. -/
def covPullback (B : ι → κ → R) (ξ : ι → R) : κ → R := fun l => ∑ i, ξ i * B i l

omit [LinearOrder ι] [LinearOrder κ] in
theorem covPullback_eq_sum (B : ι → κ → R) (ξ : ι → R) : covPullback B ξ = ∑ i, ξ i • B i := by
  funext l; simp [covPullback, Finset.sum_apply]

/-- The pullback `B^* α = Σ_s α_s B_{s₁·} ∧ ⋯ ∧ B_{s_k·}` of a fibre form by the matrix `B`. -/
def pullback (B : ι → κ → R) (α : Finset ι → R) : Finset κ → R :=
  ∑ s, α s • wedgeProd B s

theorem pullback_apply (B : ι → κ → R) (α : Finset ι → R) (t : Finset κ) :
    pullback B α t = ∑ s, α s * wedgeProd B s t := by
  simp [pullback, Finset.sum_apply]

@[simp] theorem pullback_zero (B : ι → κ → R) : pullback B (0 : Finset ι → R) = 0 := by
  simp [pullback]

theorem pullback_add (B : ι → κ → R) (α β : Finset ι → R) :
    pullback B (α + β) = pullback B α + pullback B β := by
  simp [pullback, add_smul, sum_add_distrib]

theorem pullback_smul (B : ι → κ → R) (c : R) (α : Finset ι → R) :
    pullback B (c • α) = c • pullback B α := by
  simp [pullback, smul_sum, smul_smul]

theorem pullback_sum {β : Type*} (B : ι → κ → R) (u : Finset β) (α : β → Finset ι → R) :
    pullback B (∑ b ∈ u, α b) = ∑ b ∈ u, pullback B (α b) := by
  simp only [pullback, Finset.sum_apply, sum_smul]
  exact sum_comm

theorem pullback_sub (B : ι → κ → R) (α β : Finset ι → R) :
    pullback B (α - β) = pullback B α - pullback B β := by
  simp [pullback, sub_smul, sum_sub_distrib]

theorem pullback_single_empty (B : ι → κ → R) :
    pullback B (Pi.single ∅ 1) = Pi.single ∅ 1 := by
  rw [pullback, sum_eq_single ∅ (fun s _ hs => by simp [hs]) (by simp)]
  simp

theorem pullback_wedge (B : ι → κ → R) (ξ : ι → R) (α : Finset ι → R) :
    pullback B (wedge ξ α) = wedge (covPullback B ξ) (pullback B α) := by
  rw [covPullback_eq_sum, wedge_sum_left]
  simp only [wedge_smul_left, pullback, wedge_sum, wedge_smul]
  -- right side: `Σ_j Σ_r ξ_j α_r (B_j ∧ W_r)`
  have hR : ∀ j, ∑ r, α r • ξ j • wedge (B j) (wedgeProd B r) =
      ∑ r with j ∉ r, (ξ j * α r * sgn j r) • wedgeProd B (insert j r) := by
    intro j
    rw [← sum_filter_add_sum_filter_not univ (fun r => j ∉ r)]
    rw [sum_eq_zero (s := filter (fun r => ¬j ∉ r) univ) fun r hr => by
      rw [wedge_wedgeProd_of_mem B (not_not.1 (mem_filter.1 hr).2), smul_zero, smul_zero],
      add_zero]
    refine sum_congr rfl fun r hr => ?_
    rw [wedge_wedgeProd_of_notMem B (mem_filter.1 hr).2, smul_smul, smul_smul]
    congr 1; ring
  simp only [hR]
  -- left side: `Σ_s Σ_{j ∈ s} ε(j,s) ξ_j α_{s∖j} W_s`
  have hL : ∑ s, wedge ξ α s • wedgeProd B s =
      ∑ j, ∑ s with j ∈ s, (sgn j s * ξ j * α (s.erase j)) • wedgeProd B s := by
    simp only [wedge_apply, sum_smul]
    rw [sum_comm' (t' := univ) (s' := fun j => filter (fun s => j ∈ s) univ)]
    intro s j; simp
  rw [hL]
  refine sum_congr rfl fun j _ => ?_
  refine sum_nbij' (fun s => s.erase j) (fun r => insert j r) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp
  · intro r hr; simp
  · intro s hs; exact insert_erase (mem_filter.1 hs).2
  · intro r hr; exact erase_insert (mem_filter.1 hr).2
  · intro s hs
    have hjs := (mem_filter.1 hs).2
    rw [insert_erase hjs, sgn_erase_self]
    congr 1
    ring

theorem pullback_wedgeProd {μ : Type*} [LinearOrder μ] (B : ι → κ → R) (θ : μ → ι → R)
    (s : Finset μ) : pullback B (wedgeProd θ s) = wedgeProd (fun j => covPullback B (θ j)) s := by
  induction s using Finset.induction_on_min with
  | empty => simp [pullback_single_empty]
  | insert a s ha ih =>
    rw [wedgeProd_insert_of_lt _ ha, wedgeProd_insert_of_lt _ ha, pullback_wedge, ih]

theorem pullback_pullback [Fintype κ] {μ : Type*} [LinearOrder μ] (B : ι → κ → R)
    (C : κ → μ → R) (α : Finset ι → R) :
    pullback C (pullback B α) = pullback (fun j l => ∑ i, B j i * C i l) α := by
  have : pullback B α = ∑ s, α s • wedgeProd B s := rfl
  rw [this, pullback_sum]
  simp only [pullback_smul, pullback_wedgeProd]
  rfl

theorem pullback_id (α : Finset ι → R) :
    pullback (fun i j => if i = j then (1 : R) else 0) α = α := by
  have h1 : ∀ s, wedgeProd (fun i j => if i = j then (1 : R) else 0) s =
      (Pi.single s (1 : R) : Finset ι → R) := by
    intro s
    rw [← wedgeProd_single s]
    refine wedgeProd_congr fun j _ => ?_
    funext l
    simp [Pi.single_apply, eq_comm]
  funext t
  simp only [pullback_apply, h1]
  rw [sum_eq_single t (fun s _ hs => by simp [Ne.symm hs]) (by simp)]
  simp

theorem IsDeg.pullback {k : ℕ} {α : Finset ι → R} (hα : IsDeg k α) (B : ι → κ → R) :
    IsDeg k (pullback B α) := by
  intro t ht
  rw [pullback_apply]
  refine sum_eq_zero fun s _ => ?_
  by_cases hs : #s = k
  · rw [isDeg_wedgeProd B s t (by rw [hs]; exact ht), mul_zero]
  · rw [hα s hs, zero_mul]

theorem pullback_apply_univ (B : ι → ι → R) (α : Finset ι → R) :
    pullback B α univ = (Matrix.of B).det * α univ := by
  rw [pullback_apply, sum_eq_single univ (fun s _ hs => ?_) (by simp),
    wedgeProd_univ_apply_univ, mul_comm]
  rw [isDeg_wedgeProd B s univ, mul_zero]
  intro h
  exact hs (eq_univ_of_card s (by rw [← h, card_univ]))

theorem pullback_eq_restrict [Fintype κ] (e : κ ↪o ι) {B : ι → κ → R}
    (hB : ∀ i l, (i = e l → B i l = 1) ∧ (i ≠ e l → B i l = 0)) (α : Finset ι → R) :
    pullback B α = restrict e α := by
  classical
  have hmap : ∀ t : Finset κ, wedgeProd B (t.map e.toEmbedding) = Pi.single t 1 := by
    intro t
    rw [wedgeProd_map, ← wedgeProd_single t]
    refine wedgeProd_congr fun l _ => ?_
    funext l'
    by_cases h : l = l'
    · subst h; simp [(hB _ _).1 rfl]
    · rw [Function.comp_apply, (hB _ _).2 (fun h' => h (e.injective h'))]
      simp [Ne.symm h]
  funext t
  rw [pullback_apply, sum_eq_single (t.map e.toEmbedding), hmap, restrict]
  · simp
  · intro s _ hs
    by_cases hall : ∀ i ∈ s, ∃ l, e l = i
    · have hs' : s = (univ.filter fun l => e l ∈ s).map e.toEmbedding := by
        ext i
        simp only [mem_map, mem_filter, mem_univ, true_and, RelEmbedding.coe_toEmbedding]
        constructor
        · intro hi
          obtain ⟨l, rfl⟩ := hall i hi
          exact ⟨l, hi, rfl⟩
        · rintro ⟨l, hl, rfl⟩; exact hl
      have hne : t ≠ univ.filter fun l => e l ∈ s := fun h => hs (by rw [hs', ← h])
      rw [hs', hmap]
      simp [hne]
    · simp only [not_forall, not_exists] at hall
      obtain ⟨i, hi, hne⟩ := hall
      have hB0 : B i = 0 := by
        funext l
        exact (hB i l).2 fun h => hne l h.symm
      rw [wedgeProd_eq_zero_of_mem hi hB0, Pi.zero_apply, mul_zero]
  · simp

end Pullback

theorem sum_eq_sum_erase_of_card {M : Type*} [AddCommMonoid M] {m : ℕ}
    (F : Finset (Fin (m + 1)) → M) (hF : ∀ s, #s ≠ m → F s = 0) :
    ∑ s, F s = ∑ j, F (univ.erase j) := by
  have hinj : Set.InjOn (fun j : Fin (m + 1) => univ.erase j) ↑(univ : Finset (Fin (m + 1))) := by
    intro i _ j _ h
    by_contra hij
    have : i ∈ univ.erase j := mem_erase.2 ⟨hij, mem_univ i⟩
    simp only at h
    rw [← h] at this
    simp at this
  rw [← sum_image hinj]
  refine (sum_subset (subset_univ _) fun s _ hs => hF s fun hcard => hs ?_).symm
  have : sᶜ.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    have := congrArg card (compl_eq_empty_iff s |>.1 h)
    simp [hcard] at this
  obtain ⟨j, hj⟩ := this
  refine mem_image.2 ⟨j, mem_univ j, ?_⟩
  refine (eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
  · exact mem_erase.2 ⟨fun h => (mem_compl.1 hj) (h ▸ hx), mem_univ x⟩
  · rw [hcard, card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]; simp

theorem sgn_univ {m : ℕ} (j : Fin m) : (sgn j (univ : Finset (Fin m)) : R) = (-1) ^ (j : ℕ) := by
  rw [sgn]
  congr 1
  rw [show (univ.filter fun l => l < j) = Iio j by ext; simp, Fin.card_Iio]

end Feec.ExteriorFibre

namespace Feec.FiniteElement

open ExteriorFibre

/-- Differential form fields on `ℝⁿ`: coefficient functions `ω x s` in the basis `dx_s`. -/
abbrev FormField (n : ℕ) := (Fin n → ℝ) → Finset (Fin n) → ℝ

variable {n m p : ℕ}

theorem partialDeriv_comm_of_contDiffAt {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (a b : Fin n) :
    partialDeriv a (partialDeriv b f) x = partialDeriv b (partialDeriv a f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [partialDeriv_partialDeriv hd, partialDeriv_partialDeriv hd]
  exact (ContDiffAt.isSymmSndFDerivAt hf (by simp)) _ _

theorem differentiableAt_partialDeriv_of_contDiffAt {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (j : Fin n) : DifferentiableAt ℝ (partialDeriv j f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [partialDeriv_fun]
  exact hd.clm_apply (differentiableAt_const _)

/-- The gradient covector `df = Σⱼ ∂ⱼ f dxⱼ` of a function at a point. -/
def grad (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ := fun j => partialDeriv j f x

theorem grad_affine (ξ : Fin n → ℝ) (c : ℝ) (x : Fin n → ℝ) :
    grad (fun y => ∑ i, ξ i * y i + c) x = ξ := by
  funext j
  have h : HasFDerivAt (fun y : Fin n → ℝ => ∑ i, ξ i * y i + c)
      (∑ i, ξ i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) x := by
    refine HasFDerivAt.add_const c ?_
    refine HasFDerivAt.fun_sum fun i _ => ?_
    exact (hasFDerivAt_apply i x).const_mul (ξ i)
  rw [grad, h.partialDeriv_eq]
  simp [Pi.single_apply]

/-- The **exterior derivative** `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`. -/
def extDeriv (ω : FormField n) : FormField n :=
  fun x s => ∑ j ∈ s, sgn j s * partialDeriv j (fun y => ω y (s.erase j)) x

theorem extDeriv_apply (ω : FormField n) (x : Fin n → ℝ) (s : Finset (Fin n)) :
    extDeriv ω x s = ∑ j ∈ s, sgn j s * partialDeriv j (fun y => ω y (s.erase j)) x := rfl

/-- The fibre form `(∂_j ω)(x)` of coefficientwise partial derivatives. -/
def partialDerivForm (j : Fin n) (ω : FormField n) (x : Fin n → ℝ) : Finset (Fin n) → ℝ :=
  fun s => partialDeriv j (fun y => ω y s) x

theorem extDeriv_eq_sum_wedge (ω : FormField n) (x : Fin n → ℝ) :
    extDeriv ω x = ∑ j, wedge (Pi.single j 1) (partialDerivForm j ω x) := by
  funext s
  simp only [extDeriv_apply, Finset.sum_apply, wedge_apply, partialDerivForm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

theorem IsDeg.extDeriv {k : ℕ} {ω : FormField n} (hω : ∀ x, IsDeg k (ω x)) (x : Fin n → ℝ) :
    IsDeg (k + 1) (extDeriv ω x) := by
  intro s hs
  refine Finset.sum_eq_zero fun j hj => ?_
  have h0 : (fun y => ω y (s.erase j)) = fun _ => 0 := by
    funext y
    refine hω y _ ?_
    rw [Finset.card_erase_of_mem hj]
    have := Finset.card_pos.2 ⟨j, hj⟩
    omega
  rw [h0, partialDeriv_const, mul_zero]

@[simp] theorem extDeriv_const (α : Finset (Fin n) → ℝ) :
    extDeriv (fun _ : Fin n → ℝ => α) = 0 := by
  funext x s; simp [extDeriv_apply]

theorem extDeriv_add_apply {ω η : FormField n} {x : Fin n → ℝ} (hω : DifferentiableAt ℝ ω x)
    (hη : DifferentiableAt ℝ η x) : extDeriv (ω + η) x = extDeriv ω x + extDeriv η x := by
  funext s
  simp only [extDeriv_apply, Pi.add_apply, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [partialDeriv_add (differentiableAt_pi.1 hω _) (differentiableAt_pi.1 hη _)]

theorem extDeriv_smul_const_apply (c : ℝ) {ω : FormField n} {x : Fin n → ℝ}
    (hω : DifferentiableAt ℝ ω x) : extDeriv (c • ω) x = c • extDeriv ω x := by
  funext s
  simp only [extDeriv_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := partialDeriv_const_smul (differentiableAt_pi.1 hω (s.erase j)) c j
  simp only [smul_eq_mul] at this
  rw [this]; ring

theorem extDeriv_sum_apply {β : Type*} (u : Finset β) {ω : β → FormField n} {x : Fin n → ℝ}
    (hω : ∀ b ∈ u, DifferentiableAt ℝ (ω b) x) :
    extDeriv (∑ b ∈ u, ω b) x = ∑ b ∈ u, extDeriv (ω b) x := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact congrFun (extDeriv_const 0) x
  | insert a u ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      extDeriv_add_apply (hω a (Finset.mem_insert_self a u))
        (DifferentiableAt.sum fun b hb => hω b (Finset.mem_insert_of_mem hb)),
      ih fun b hb => hω b (Finset.mem_insert_of_mem hb)]

theorem extDeriv_extDeriv_apply {ω : FormField n} {x : Fin n → ℝ} (hω : ContDiffAt ℝ 2 ω x) :
    extDeriv (extDeriv ω) x = 0 := by
  have hc : ∀ t, ContDiffAt ℝ 2 (fun y => ω y t) x := fun t => contDiffAt_pi.1 hω t
  funext s
  simp only [extDeriv_apply, Pi.zero_apply]
  have hinner : ∀ j ∈ s, partialDeriv j (fun y => ∑ l ∈ s.erase j, sgn l (s.erase j) *
      partialDeriv l (fun z => ω z ((s.erase j).erase l)) y) x =
      ∑ l ∈ s.erase j, sgn l (s.erase j) *
        partialDeriv j (partialDeriv l (fun z => ω z ((s.erase j).erase l))) x := by
    intro j _
    rw [partialDeriv_sum _ (fun l _ =>
      ((differentiableAt_partialDeriv_of_contDiffAt (hc _) l).const_mul _))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show (fun y => sgn l (s.erase j) * partialDeriv l (fun z => ω z ((s.erase j).erase l)) y)
        = fun y => (sgn l (s.erase j) : ℝ) • partialDeriv l (fun z => ω z ((s.erase j).erase l)) y
        from rfl,
      partialDeriv_const_smul (differentiableAt_partialDeriv_of_contDiffAt (hc _) l)]
    rfl
  rw [Finset.sum_congr rfl fun j hj => by rw [hinner j hj]]
  simp only [Finset.mul_sum]
  refine sum_sum_erase_eq_zero s (fun j l => sgn j s * (sgn l (s.erase j) *
      partialDeriv j (partialDeriv l (fun z => ω z ((s.erase j).erase l))) x))
      fun j hj l hl hjl => ?_
  rw [sgn_erase hj, sgn_erase hl, show (s.erase l).erase j = (s.erase j).erase l from
    Finset.erase_right_comm, partialDeriv_comm_of_contDiffAt (hc _) l j]
  have := ite_lt_add_ite_lt (R := ℝ) hjl
  linear_combination (sgn j s * sgn l s *
    partialDeriv j (partialDeriv l (fun z => ω z ((s.erase j).erase l))) x) * this

/-- **`d ∘ d = 0`** for `C²` forms. -/
theorem extDeriv_extDeriv {ω : FormField n} (hω : ContDiff ℝ 2 ω) : extDeriv (extDeriv ω) = 0 :=
  funext fun _ => extDeriv_extDeriv_apply hω.contDiffAt

/-- **Leibniz rule** `d (f ω) = df ∧ ω + f dω`. -/
theorem extDeriv_smul_apply {f : (Fin n → ℝ) → ℝ} {ω : FormField n} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (hω : DifferentiableAt ℝ ω x) :
    extDeriv (fun y => f y • ω y) x = wedge (grad f x) (ω x) + f x • extDeriv ω x := by
  funext s
  simp only [extDeriv_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, wedge_apply, grad,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [partialDeriv_mul hf (differentiableAt_pi.1 hω _)]
  ring

theorem extDeriv_affine_smul (ξ : Fin n → ℝ) (c : ℝ) (α : Finset (Fin n) → ℝ) :
    extDeriv (fun x => (∑ i, ξ i * x i + c) • α) = fun _ => wedge ξ α := by
  funext x
  have hf : DifferentiableAt ℝ (fun y : Fin n → ℝ => ∑ i, ξ i * y i + c) x := by fun_prop
  rw [extDeriv_smul_apply (ω := fun _ => α) hf (differentiableAt_const _), grad_affine,
    extDeriv_const]
  simp

/-- The affine map `x̂ ↦ B x̂ + b` of `Rᵐ` to `Rⁿ` (`B : n × m`). -/
def affine {R : Type*} [CommSemiring R] (B : Fin n → Fin m → R) (b : Fin n → R) (x : Fin m → R) :
    Fin n → R :=
  fun i => ∑ l, B i l * x l + b i

theorem affine_apply {R : Type*} [CommSemiring R] (B : Fin n → Fin m → R) (b : Fin n → R)
    (x : Fin m → R) (i : Fin n) : affine B b x i = ∑ l, B i l * x l + b i := rfl

theorem affine_comp (C : Fin p → Fin n → ℝ) (c : Fin p → ℝ) (B : Fin n → Fin m → ℝ)
    (b : Fin n → ℝ) (x : Fin m → ℝ) :
    affine C c (affine B b x) = affine (fun j l => ∑ i, C j i * B i l) (affine C c b) x := by
  funext j
  simp only [affine_apply, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]
  ring

theorem hasFDerivAt_affine (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (x : Fin m → ℝ) :
    HasFDerivAt (affine B b) (Matrix.toLin' (Matrix.of B)).toContinuousLinearMap x := by
  have : affine B b = fun y => (Matrix.toLin' (Matrix.of B)).toContinuousLinearMap y + b := by
    funext y i
    simp [affine_apply, Matrix.mulVec, dotProduct]
  rw [this]
  exact (ContinuousLinearMap.hasFDerivAt _).add_const b

theorem differentiable_affine (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) :
    Differentiable ℝ (affine B b) := fun x => (hasFDerivAt_affine B b x).differentiableAt

theorem continuous_affine (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) : Continuous (affine B b) :=
  (differentiable_affine B b).continuous

theorem partialDeriv_comp_affine {f : (Fin n → ℝ) → ℝ} (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ)
    {x : Fin m → ℝ} (hf : DifferentiableAt ℝ f (affine B b x)) (i : Fin m) :
    partialDeriv i (fun y => f (affine B b y)) x =
      ∑ j, B j i * partialDeriv j f (affine B b x) := by
  rw [show (fun y => f (affine B b y)) = f ∘ affine B b from rfl,
    (hf.hasFDerivAt.comp x (hasFDerivAt_affine B b x)).partialDeriv_eq]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_toContinuousLinearMap']
  rw [fderiv_apply_eq_sum_partialDeriv]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The pullback `F^* ω` of a form field along the affine map `F(x̂) = B x̂ + b`. -/
def affinePullback (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (ω : FormField n) : FormField m :=
  fun x => ExteriorFibre.pullback B (ω (affine B b x))

theorem affinePullback_apply (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (ω : FormField n)
    (x : Fin m → ℝ) : affinePullback B b ω x = ExteriorFibre.pullback B (ω (affine B b x)) := rfl

theorem IsDeg.affinePullback {k : ℕ} {ω : FormField n} (hω : ∀ x, IsDeg k (ω x))
    (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (x : Fin m → ℝ) :
    IsDeg k (affinePullback B b ω x) :=
  (hω _).pullback B

theorem affinePullback_affinePullback (C : Fin p → Fin n → ℝ) (c : Fin p → ℝ)
    (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (ω : FormField p) :
    affinePullback B b (affinePullback C c ω) =
      affinePullback (fun j l => ∑ i, C j i * B i l) (affine C c b) ω := by
  funext x
  simp only [affinePullback_apply, ExteriorFibre.pullback_pullback, affine_comp]

theorem affinePullback_add (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (ω η : FormField n) :
    affinePullback B b (ω + η) = affinePullback B b ω + affinePullback B b η := by
  funext x; simp [affinePullback_apply, pullback_add]

theorem affinePullback_sub (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (ω η : FormField n) :
    affinePullback B b (ω - η) = affinePullback B b ω - affinePullback B b η := by
  funext x; simp [affinePullback_apply, pullback_sub]

theorem affinePullback_smul (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (c : ℝ) (ω : FormField n) :
    affinePullback B b (c • ω) = c • affinePullback B b ω := by
  funext x; simp [affinePullback_apply, pullback_smul]

theorem contDiff_affine {r : WithTop ℕ∞} (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) :
    ContDiff ℝ r (affine B b) := by
  have : affine B b = fun y => (Matrix.toLin' (Matrix.of B)).toContinuousLinearMap y + b := by
    funext y i
    simp [affine_apply, Matrix.mulVec, dotProduct]
  rw [this]
  exact (ContinuousLinearMap.contDiff _).add contDiff_const

theorem contDiff_affinePullback {r : WithTop ℕ∞} {ω : FormField n} (B : Fin n → Fin m → ℝ)
    (b : Fin n → ℝ) (hω : ContDiff ℝ r ω) : ContDiff ℝ r (affinePullback B b ω) := by
  rw [contDiff_pi]
  intro t
  simp only [affinePullback_apply, ExteriorFibre.pullback_apply]
  refine ContDiff.sum fun s _ => ?_
  exact ((contDiff_pi.1 hω s).comp (contDiff_affine B b)).mul contDiff_const

theorem contDiffOn_affinePullback {r : WithTop ℕ∞} {ω : FormField n} {U : Set (Fin n → ℝ)}
    (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (hω : ContDiffOn ℝ r ω U) :
    ContDiffOn ℝ r (affinePullback B b ω) (affine B b ⁻¹' U) := by
  rw [contDiffOn_pi]
  intro t
  simp only [affinePullback_apply, ExteriorFibre.pullback_apply]
  refine ContDiffOn.sum fun s _ => ?_
  exact ((contDiffOn_pi.1 hω s).comp (contDiff_affine B b).contDiffOn
    (Set.mapsTo_preimage _ _)).mul contDiffOn_const

/-- **The pullback commutes with the exterior derivative**: `d (F^* ω) = F^* (d ω)` for an affine
map `F`, at every point where `ω` is differentiable. -/
theorem extDeriv_affinePullback_apply {ω : FormField n} (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ)
    {x : Fin m → ℝ} (hω : DifferentiableAt ℝ ω (affine B b x)) :
    extDeriv (affinePullback B b ω) x = affinePullback B b (extDeriv ω) x := by
  have hc : ∀ s, DifferentiableAt ℝ (fun y => ω y s) (affine B b x) :=
    fun s => differentiableAt_pi.1 hω s
  -- the partial derivatives of the pullback
  have hD : ∀ i, partialDerivForm i (affinePullback B b ω) x =
      ∑ j, B j i • ExteriorFibre.pullback B (partialDerivForm j ω (affine B b x)) := by
    intro i
    funext t
    simp only [partialDerivForm, affinePullback_apply, ExteriorFibre.pullback_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [partialDeriv_sum (f := fun s y => ω (affine B b y) s * wedgeProd B s t) _ fun s _ =>
      ((hc s).comp x (differentiable_affine B b x)).mul_const _]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [partialDeriv_mul (f := fun y => ω (affine B b y) s) (g := fun _ => wedgeProd B s t)
      ((hc s).comp x (differentiable_affine B b x)) (differentiableAt_const _),
      partialDeriv_const, mul_zero, add_zero]
    change partialDeriv i (fun y => (fun z => ω z s) (affine B b y)) x * _ = _
    rw [partialDeriv_comp_affine B b (hc s), Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [extDeriv_eq_sum_wedge, affinePullback_apply, extDeriv_eq_sum_wedge, pullback_sum]
  simp only [hD, wedge_sum, wedge_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pullback_wedge]
  simp only [← wedge_smul_left]
  rw [← wedge_sum_left]
  congr 1
  funext l
  simp [covPullback, Finset.sum_apply, Pi.single_apply]

end Feec.FiniteElement
