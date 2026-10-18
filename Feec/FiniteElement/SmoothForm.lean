module

public import Feec.Algebra.ExteriorFibre
public import Feec.ForMathlib.Calculus.Partial
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Smooth differential forms on `ℝⁿ`: exterior derivative and affine pullback

A differential `k`-form field on `ℝⁿ = Fin n → ℝ` is a coefficient function
`ω : (Fin n → ℝ) → (Finset (Fin n) → ℝ)` in the basis `dx_s` (`Feec.ExteriorFibre`), supported
on `k`-subsets (`Feec.ExteriorFibre.IsDeg`). This file develops the classical calculus of such
forms used by the finite element spaces of [AFW2006], §3–4 and [Arnold2018], Ch. 7:

* the exterior derivative `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`, with `d ∘ d = 0` for `C²`
  forms and the Leibniz rule `d (f ω) = df ∧ ω + f dω`;
* the pullback along an affine map `F(x̂) = B x̂ + b`, whose coefficients are the `k × k` minors
  of `B`, and which commutes with `d`.

The algebra of the pullback lives on the fibre: the iterated wedge product
`wedgeProd θ s = θ_{s₁} ∧ ⋯ ∧ θ_{s_k}` of covectors, and the pullback
`pullback B α = Σ_s α_s θ_{s₁} ∧ ⋯ ∧ θ_{s_k}` of a fibre form by the rows `θ_i = B_{i·}` of a
matrix. Its coefficients are minors (`wedgeProd_apply_eq_det_submatrix`), it is multiplicative
(`pullback_wedge`), functorial (`pullback_pullback`), and on top-degree forms it is
multiplication by the determinant (`pullback_apply_univ`).

## Main definitions

* `Feec.ExteriorFibre.wedgeProd θ s`, `Feec.ExteriorFibre.pullback B α`;
* `Feec.FiniteElement.FormField n`, `Feec.FiniteElement.extDeriv`,
  `Feec.FiniteElement.FormField.pullback B b`, `Feec.FiniteElement.grad`.

## Main results

* `Feec.ExteriorFibre.wedgeProd_apply_eq_det_submatrix`: the coefficients of
  `θ_{s₁} ∧ ⋯ ∧ θ_{s_k}` are the `k × k` minors of `θ`;
* `Feec.ExteriorFibre.pullback_wedge`, `Feec.ExteriorFibre.pullback_pullback`,
  `Feec.ExteriorFibre.pullback_apply_univ`;
* `Feec.FiniteElement.extDeriv_extDeriv_apply`, `Feec.FiniteElement.extDeriv_extDeriv`:
  `d ∘ d = 0` for `C²` forms;
* `Feec.FiniteElement.extDeriv_smul_apply`: the Leibniz rule `d (f ω) = df ∧ ω + f dω`, and
  `Feec.FiniteElement.extDeriv_affine_smul`: `d (λ α) = dλ ∧ α` for affine `λ` and constant `α`;
* `Feec.FiniteElement.extDeriv_pullback_apply`: `d (F^* ω) = F^* (d ω)` for affine `F`;
* `Feec.FiniteElement.IsDeg.extDeriv`, `Feec.FiniteElement.IsDeg.pullback`: degrees.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2–3 (differential forms, pullback, exterior derivative)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6–7
-/

open Finset

@[expose] public noncomputable section

namespace Feec.ExteriorFibre

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d]

/-! ### Linearity of the exterior product in both arguments -/

@[simp] theorem wedge_zero (ξ : d → R) : wedge ξ (0 : Finset d → R) = 0 := by
  funext s; simp [wedge_apply]

@[simp] theorem wedge_zero_left (ω : Finset d → R) : wedge (0 : d → R) ω = 0 := by
  funext s; simp [wedge_apply]

theorem wedge_smul_left (c : R) (ξ : d → R) (ω : Finset d → R) :
    wedge (c • ξ) ω = c • wedge ξ ω := by
  funext s; simp only [wedge_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

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

theorem wedge_sub_left (ξ η : d → R) (ω : Finset d → R) :
    wedge (ξ - η) ω = wedge ξ ω - wedge η ω := by
  rw [sub_eq_add_neg, wedge_add_left, wedge_neg_left, sub_eq_add_neg]

/-- `dx_j ∧ dx_s = ε(j, s) dx_{s ∪ j}` for `j ∉ s`. -/
theorem wedge_single_single {j : d} {s : Finset d} (hj : j ∉ s) :
    wedge (Pi.single j (1 : R)) (Pi.single s (1 : R)) =
      (sgn j s : R) • (Pi.single (insert j s) 1 : Finset d → R) := by
  funext t
  rw [wedge_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hjt : j ∈ t
  · rw [sum_eq_single j (fun l _ hlj => by simp [hlj]) (fun h => absurd hjt h)]
    simp only [Pi.single_eq_same, mul_one]
    by_cases hts : t = insert j s
    · subst hts; simp [erase_insert hj, sgn_insert_self]
    · have : t.erase j ≠ s := fun h => hts (by rw [← h, insert_erase hjt])
      simp [this, hts]
  · have hts : t ≠ insert j s := fun h => hjt (h ▸ mem_insert_self j s)
    rw [sum_eq_zero fun l hl => by
      have : l ≠ j := fun h => hjt (h ▸ hl)
      simp [this]]
    simp [hts]

/-! ### Iterated exterior products of covectors -/

variable {ι : Type*} [LinearOrder ι]

/-- The iterated exterior product `θ_{s₁} ∧ ⋯ ∧ θ_{s_k}` (`s₁ < ⋯ < s_k`) of a family of covectors
`θ : ι → (d → R)`; for `s = ∅` it is the unit `0`-form `dx_∅`. -/
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

/-- Moving a covector into place: `θ_{s ∪ j}^∧ = ε(j, s) θ_j ∧ θ_s^∧` for `j ∉ s`. -/
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

/-- Removing a covector: `θ_s^∧ = ε(j, s) θ_j ∧ θ_{s ∖ j}^∧` for `j ∈ s`. -/
theorem wedgeProd_eq_sgn_smul_wedge_erase (θ : ι → d → R) {j : ι} {s : Finset ι} (hj : j ∈ s) :
    wedgeProd θ s = (sgn j s : R) • wedge (θ j) (wedgeProd θ (s.erase j)) := by
  conv_lhs => rw [← insert_erase hj]
  rw [wedgeProd_insert θ (notMem_erase j s), sgn_erase_self]

/-- An iterated exterior product vanishes as soon as one of its factors does. -/
theorem wedgeProd_eq_zero_of_mem {θ : ι → d → R} {j : ι} {s : Finset ι} (hj : j ∈ s)
    (h : θ j = 0) : wedgeProd θ s = 0 := by
  rw [wedgeProd_eq_sgn_smul_wedge_erase θ hj, h, wedge_zero_left, smul_zero]

/-- `θ_{s₁} ∧ ⋯ ∧ θ_{s_k}` is a `k`-form. -/
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

/-- The products of the coordinate covectors are the basis forms: `dx_{s₁} ∧ ⋯ ∧ dx_{s_k} = dx_s`. -/
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

/-- Iterated products along an order embedding: `θ_{e(s)}^∧ = (θ ∘ e)_s^∧`. -/
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

/-! ### Restriction of a fibre form to a subset of the coordinates -/

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

/-! ### Top-degree coefficients are determinants; coefficients are minors -/

section Det

variable [Fintype ι]

omit [Fintype ι] in
/-- Replacing the covector `θ_i` (`i ∈ s`) only changes the factor `θ_i` of `θ_s^∧`. -/
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

/-- **The top coefficient is the determinant**: `(θ₁ ∧ ⋯ ∧ θ_m)_{univ} = det θ`. -/
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

/-! ### Pullback of fibre forms by a matrix -/

section Pullback

variable [Fintype ι] {κ : Type*} [LinearOrder κ]

/-- The pulled-back covector `(Bᵀ ξ)_l = Σ_i ξ_i B_{il}`. -/
def covPullback (B : ι → κ → R) (ξ : ι → R) : κ → R := fun l => ∑ i, ξ i * B i l

omit [LinearOrder ι] [LinearOrder κ] in
theorem covPullback_eq_sum (B : ι → κ → R) (ξ : ι → R) : covPullback B ξ = ∑ i, ξ i • B i := by
  funext l; simp [covPullback, Finset.sum_apply]

/-- The pullback of a fibre form `α` on `ι` by the matrix `B : ι × κ` (the linear map
`R^κ → R^ι`): `B^* α = Σ_s α_s B_{s₁·} ∧ ⋯ ∧ B_{s_k·}`, i.e. `B^*(dx_i) = Σ_l B_{il} dx̂_l`. -/
def pullback (B : ι → κ → R) (α : Finset ι → R) : Finset κ → R :=
  ∑ s, α s • wedgeProd B s

theorem pullback_apply (B : ι → κ → R) (α : Finset ι → R) (t : Finset κ) :
    pullback B α t = ∑ s, α s * wedgeProd B s t := by
  simp [pullback, Finset.sum_apply]

/-- The coefficients of the pullback are the minors of `B`. -/
theorem pullback_apply_eq_sum_det (B : ι → κ → R) (α : Finset ι → R) {k : ℕ}
    (t : Finset κ) (ht : #t = k) :
    pullback B α t = ∑ s, α s * if hs : #s = k then
      (Matrix.of fun i j : Fin k => B (s.orderEmbOfFin hs i) (t.orderEmbOfFin ht j)).det
      else 0 := by
  rw [pullback_apply]
  refine sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · rw [wedgeProd_apply_eq_det_submatrix B hs ht]
  · rw [isDeg_wedgeProd B s t (by rw [ht]; exact Ne.symm hs)]

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

theorem pullback_neg (B : ι → κ → R) (α : Finset ι → R) :
    pullback B (-α) = -pullback B α := by
  simp [pullback]

theorem pullback_sub (B : ι → κ → R) (α β : Finset ι → R) :
    pullback B (α - β) = pullback B α - pullback B β := by
  simp [pullback, sub_smul, sum_sub_distrib]

theorem pullback_single_empty (B : ι → κ → R) :
    pullback B (Pi.single ∅ 1) = Pi.single ∅ 1 := by
  rw [pullback, sum_eq_single ∅ (fun s _ hs => by simp [hs]) (by simp)]
  simp

/-- The pullback is multiplicative: `B^*(ξ ∧ α) = (Bᵀ ξ) ∧ B^* α`. -/
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

/-- The pullback of an iterated product is the iterated product of the pulled-back covectors. -/
theorem pullback_wedgeProd {μ : Type*} [LinearOrder μ] (B : ι → κ → R) (θ : μ → ι → R)
    (s : Finset μ) : pullback B (wedgeProd θ s) = wedgeProd (fun j => covPullback B (θ j)) s := by
  induction s using Finset.induction_on_min with
  | empty => simp [pullback_single_empty]
  | insert a s ha ih =>
    rw [wedgeProd_insert_of_lt _ ha, wedgeProd_insert_of_lt _ ha, pullback_wedge, ih]

/-- **Functoriality** `C^* ∘ B^* = (B C)^*`. -/
theorem pullback_pullback [Fintype κ] {μ : Type*} [LinearOrder μ] (B : ι → κ → R)
    (C : κ → μ → R) (α : Finset ι → R) :
    pullback C (pullback B α) = pullback (fun j l => ∑ i, B j i * C i l) α := by
  have : pullback B α = ∑ s, α s • wedgeProd B s := rfl
  rw [this, pullback_sum]
  simp only [pullback_smul, pullback_wedgeProd]
  rfl

theorem pullback_id (α : Finset ι → R) : pullback (fun i j => if i = j then (1 : R) else 0) α = α := by
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

/-- The pullback preserves the form degree. -/
theorem IsDeg.pullback {k : ℕ} {α : Finset ι → R} (hα : IsDeg k α) (B : ι → κ → R) :
    IsDeg k (pullback B α) := by
  intro t ht
  rw [pullback_apply]
  refine sum_eq_zero fun s _ => ?_
  by_cases hs : #s = k
  · rw [isDeg_wedgeProd B s t (by rw [hs]; exact ht), mul_zero]
  · rw [hα s hs, zero_mul]

/-- On top-degree coefficients the pullback is multiplication by the determinant. -/
theorem pullback_apply_univ (B : ι → ι → R) (α : Finset ι → R) :
    pullback B α univ = (Matrix.of B).det * α univ := by
  rw [pullback_apply, sum_eq_single univ (fun s _ hs => ?_) (by simp),
    wedgeProd_univ_apply_univ, mul_comm]
  rw [isDeg_wedgeProd B s univ, mul_zero]
  intro h
  exact hs (eq_univ_of_card s (by rw [← h, card_univ]))

end Pullback

end Feec.ExteriorFibre

namespace Feec.FiniteElement

open ExteriorFibre

/-- Differential form fields on `ℝⁿ`: coefficient functions `ω x s` in the basis `dx_s`. A
`k`-form field is one with `IsDeg k (ω x)` for every `x`. -/
abbrev FormField (n : ℕ) := (Fin n → ℝ) → Finset (Fin n) → ℝ

variable {n m p : ℕ}

/-! ### Partial derivatives -/

/-- Schwarz's theorem at a point: partial derivatives of a function that is `C²` at `x` commute
at `x`. -/
theorem partialDeriv_comm_of_contDiffAt {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (a b : Fin n) :
    partialDeriv a (partialDeriv b f) x = partialDeriv b (partialDeriv a f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [partialDeriv_partialDeriv hd, partialDeriv_partialDeriv hd]
  exact (ContDiffAt.isSymmSndFDerivAt hf (by simp)) _ _

/-- A partial derivative of a function that is `C²` at `x` is differentiable at `x`. -/
theorem differentiableAt_partialDeriv_of_contDiffAt {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (j : Fin n) : DifferentiableAt ℝ (partialDeriv j f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [partialDeriv_fun]
  exact hd.clm_apply (differentiableAt_const _)

/-- The derivative in any direction is the combination of the partial derivatives. -/
theorem fderiv_apply_eq_sum_partialDeriv (f : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) :
    fderiv ℝ f x v = ∑ j, v j * partialDeriv j f x := by
  conv_lhs => rw [pi_eq_sum_univ v]
  simp only [map_sum, map_smul, smul_eq_mul, partialDeriv]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  funext i
  simp [Pi.single_apply, eq_comm]

/-- The gradient covector `df = Σⱼ ∂ⱼ f dxⱼ` of a function at a point. -/
def grad (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ := fun j => partialDeriv j f x

/-- The gradient of an affine function `λ(x) = Σᵢ ξᵢ xᵢ + c` is `ξ`. -/
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

/-! ### The exterior derivative -/

/-- The **exterior derivative** `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`. -/
def extDeriv (ω : FormField n) : FormField n :=
  fun x s => ∑ j ∈ s, sgn j s * partialDeriv j (fun y => ω y (s.erase j)) x

theorem extDeriv_apply (ω : FormField n) (x : Fin n → ℝ) (s : Finset (Fin n)) :
    extDeriv ω x s = ∑ j ∈ s, sgn j s * partialDeriv j (fun y => ω y (s.erase j)) x := rfl

/-- The fibre form `(∂_j ω)(x)` of coefficientwise partial derivatives. -/
def partialDerivForm (j : Fin n) (ω : FormField n) (x : Fin n → ℝ) : Finset (Fin n) → ℝ :=
  fun s => partialDeriv j (fun y => ω y s) x

/-- `d = Σⱼ dxⱼ ∧ ∂ⱼ`. -/
theorem extDeriv_eq_sum_wedge (ω : FormField n) (x : Fin n → ℝ) :
    extDeriv ω x = ∑ j, wedge (Pi.single j 1) (partialDerivForm j ω x) := by
  funext s
  simp only [extDeriv_apply, Finset.sum_apply, wedge_apply, partialDerivForm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

/-- `d` raises the form degree by one. -/
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

/-- The exterior derivative of a constant form vanishes. -/
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

/-- **`d ∘ d = 0`** at every point where the form is `C²`. -/
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

/-- `d (λ α) = dλ ∧ α` for an affine function `λ(x) = Σᵢ ξᵢ xᵢ + c` and a constant form `α`. -/
theorem extDeriv_affine_smul (ξ : Fin n → ℝ) (c : ℝ) (α : Finset (Fin n) → ℝ) :
    extDeriv (fun x => (∑ i, ξ i * x i + c) • α) = fun _ => wedge ξ α := by
  funext x
  have hf : DifferentiableAt ℝ (fun y : Fin n → ℝ => ∑ i, ξ i * y i + c) x := by fun_prop
  rw [extDeriv_smul_apply (ω := fun _ => α) hf (differentiableAt_const _), grad_affine,
    extDeriv_const]
  simp

/-! ### Pullback along affine maps -/

/-- The affine map `x̂ ↦ B x̂ + b` of `ℝᵐ` to `ℝⁿ` (`B : n × m`). -/
def affine (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (x : Fin m → ℝ) : Fin n → ℝ :=
  fun i => ∑ l, B i l * x l + b i

theorem affine_apply (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (x : Fin m → ℝ) (i : Fin n) :
    affine B b x i = ∑ l, B i l * x l + b i := rfl

theorem affine_comp (C : Fin p → Fin n → ℝ) (c : Fin p → ℝ) (B : Fin n → Fin m → ℝ)
    (b : Fin n → ℝ) (x : Fin m → ℝ) :
    affine C c (affine B b x) = affine (fun j l => ∑ i, C j i * B i l) (affine C c b) x := by
  funext j
  simp only [affine_apply, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]
  ring

/-- The derivative of `x̂ ↦ B x̂ + b`. -/
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

/-- Chain rule for an affine change of variables:
`∂ᵢ (f ∘ F)(x) = Σⱼ Bⱼᵢ (∂ⱼ f)(F x)`. -/
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

/-- The **pullback** `F^* ω` of a form field along `F(x̂) = B x̂ + b`: its coefficients are the
`k × k` minors of `B` (`Feec.ExteriorFibre.pullback_apply_eq_sum_det`) times the coefficients of
`ω ∘ F`. -/
def affinePullback (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (ω : FormField n) : FormField m :=
  fun x => ExteriorFibre.pullback B (ω (affine B b x))

theorem affinePullback_apply (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (ω : FormField n)
    (x : Fin m → ℝ) : affinePullback B b ω x = ExteriorFibre.pullback B (ω (affine B b x)) := rfl

theorem IsDeg.affinePullback {k : ℕ} {ω : FormField n} (hω : ∀ x, IsDeg k (ω x))
    (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (x : Fin m → ℝ) :
    IsDeg k (affinePullback B b ω x) :=
  (hω _).pullback B

/-- Functoriality of the pullback: `F^* (G^* ω) = (G ∘ F)^* ω`. -/
theorem affinePullback_affinePullback (C : Fin p → Fin n → ℝ) (c : Fin p → ℝ)
    (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (ω : FormField p) :
    affinePullback B b (affinePullback C c ω) =
      affinePullback (fun j l => ∑ i, C j i * B i l) (affine C c b) ω := by
  funext x
  simp only [affinePullback_apply, ExteriorFibre.pullback_pullback, affine_comp]

theorem affinePullback_add (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (ω η : FormField n) :
    affinePullback B b (ω + η) = affinePullback B b ω + affinePullback B b η := by
  funext x; simp [affinePullback_apply, pullback_add]

theorem affinePullback_smul (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (c : ℝ) (ω : FormField n) :
    affinePullback B b (c • ω) = c • affinePullback B b ω := by
  funext x; simp [affinePullback_apply, pullback_smul]

theorem differentiableAt_affinePullback {ω : FormField n} (B : Fin n → Fin m → ℝ)
    (b : Fin n → ℝ) {x : Fin m → ℝ} (hω : DifferentiableAt ℝ ω (affine B b x)) :
    DifferentiableAt ℝ (affinePullback B b ω) x := by
  rw [differentiableAt_pi]
  intro t
  simp only [affinePullback_apply, ExteriorFibre.pullback_apply]
  refine DifferentiableAt.fun_sum fun s _ => ?_
  exact ((differentiableAt_pi.1 hω s).comp x (differentiable_affine B b x)).mul_const _

theorem contDiff_affinePullback {r : WithTop ℕ∞} {ω : FormField n} (B : Fin n → Fin m → ℝ)
    (b : Fin n → ℝ) (hω : ContDiff ℝ r ω) : ContDiff ℝ r (affinePullback B b ω) := by
  rw [contDiff_pi]
  intro t
  simp only [affinePullback_apply, ExteriorFibre.pullback_apply]
  refine ContDiff.sum fun s _ => ?_
  have hA : ContDiff ℝ r (affine B b) := by
    have : affine B b = fun y => (Matrix.toLin' (Matrix.of B)).toContinuousLinearMap y + b := by
      funext y i
      simp [affine_apply, Matrix.mulVec, dotProduct]
    rw [this]
    exact (ContinuousLinearMap.contDiff _).add contDiff_const
  exact ((contDiff_pi.1 hω s).comp hA).mul contDiff_const

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
