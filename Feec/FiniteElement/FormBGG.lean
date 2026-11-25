module

public import Feec.FiniteElement.TensorElement
public import Feec.FiniteElement.WeakSymmetryMaps
public import Feec.Domain.RegularDecomposition
public import Feec.HilbertComplex.BGG.DomainData

/-!
# BGG diagrams of differential forms: the Hessian and div–div diagrams

On an open `Ω ⊆ ℝⁿ`, the maximal `L²` de Rham complex `HΛ(Ω)` (`formRow hΩ`) and its `n`-fold
product `HΛ(Ω) ⊗ ℝⁿ` (`vecRow hΩ`, vectors of forms, `Feec.HilbertComplex.pi`) are linked by
constant-coefficient maps built from **the exterior product with `dxₐ`** (`dxL2`,
`(dxₐ ∧ φ)_t = ε(a, t) φ_{t ∖ a}`), the `L²` realization of `S(φ eₐ)` for the map
`S v = Σₐ dxₐ ∧ vₐ` of `Feec.FiniteElement.wsL2`:

* `S v = Σₐ dxₐ ∧ vₐ` (`wsL2`, vectors of forms to forms): **the Hessian diagram**, `HΛ(Ω)` over
  `HΛ(Ω) ⊗ ℝⁿ` (`hessianFormData`); on `ℝ³` these are the maps `I`, `2 vskw`, `tr` of the vector
  proxies of `Feec.Domain.hessianMaximalData` ([ArnoldHu2021], §4.1);
* `(S φ)ₐ = dxₐ ∧ φ` (`dxVecL2`, forms to vectors of forms): **the div–div diagram**,
  `HΛ(Ω) ⊗ ℝⁿ` over `HΛ(Ω)` (`divDivFormData`); on `ℝ³` the maps `· I`, `v ↦ v × ·`, `I`.

Both map the maximal domains into each other with `d S = −S d` (`wsL2_mem_maximal`,
`dxL2_mem_maximal`), so they are analytic BGG data (`Feec.BGG.HilbertData`). The algebra of the
fibre maps decides the hypotheses of the analytic BGG theorem (`Feec.BGG.HilbertData.bggVerdict`):

* **the Hessian diagram at `J = 0`**: `S` on vector `0`-forms is an isometry
  (`wsL2Adj_wsL2_zero`, `Sᵀ S = 1`), and `S Sᵀ = k + 1` on `(k + 1)`-forms (`wsL2_wsL2Adj`, the
  Euler identity `Σₐ dxₐ ∧ ι_{eₐ} = k + 1`), so `S` has an `H¹`-preserving right inverse in every
  degree and the `H¹`-regular decompositions of `HΛ(Ω)` from `0` on give the regular
  decompositions of the diagram (`hessianFormData_regularDecomposition`);
* **the div–div diagram at `J = n − 1`**: `Sᵀ S = n − k` on `k`-forms (`dxVecAdj_dxVecL2`, the
  identity `Σₐ ι_{eₐ} (dxₐ ∧ ·) = n − k`), so `S` is bounded below in the degrees `k < n`, and
  `S Sᵀ = 1` in the top degree `k + 1 = n` (`dxVecL2_dxVecAdj`), so the `H¹`-regular
  decompositions of the rows from `n − 1` on give those of the diagram
  (`divDivFormData_regularDecomposition`).

The adjoints are the contractions `ι_c` (`ιL2`), with the Cartan identity
`ι_c (dx_{c'} ∧ ·) + dx_{c'} ∧ ι_c = δ_{cc'}` (`ιL2_dxL2_add_dxL2_ιL2`) and the Euler identities
`Σ_c dx_c ∧ ι_c = k + 1`, `Σ_c ι_c (dx_c ∧ ·) = n − k` (`sum_dxL2_ιL2`, `sum_ιL2_dxL2`), from which
`Feec.FiniteElement.FormBGGElasticity` builds the elasticity diagram on `ℝ³`; the anticommutation
`dxₐ ∧ dx_c ∧ · = −dx_c ∧ dxₐ ∧ ·` (`dxL2_dxL2_add_dxL2_dxL2`) gives its identity
`S^{k+1} S^k = −D W` (`Feec.FiniteElement.crossL2_crossL2`).

**`Sᴶ` is not onto between the domains** on every nonempty open `Ω`, `n ≥ 1`, at the `J` of both
diagrams (`hessianFormData_exists_forall_S_ne`, `divDivFormData_exists_forall_S_ne`): (23) of
[ArnoldHu2021] fails between the `L²` domains, and the weaker hypothesis "onto modulo `d`" of
`Feec.BGG.HilbertData.bggVerdict` is the one the regular decompositions give. The rescalings of a
test field `φ` with `d (Sᴶ φ) = 0` (a gradient `Sᵀ dχ`, resp. any `(n − 1)`-form) make
`‖d̃ᴶ φ‖ / ‖φ‖` unbounded, which an onto `Sᴶ` forbids (`Feec.BGG.HilbertData.exists_forall_S_ne`).

## Main definitions

* `dxL2`, `dxVecL2`, `dxVecAdj`, `ιL2`; `formRow`, `vecRow`; `hessianFormData`, `divDivFormData`.

## Main results

* `sum_wsCoeff_mul_wsCoeff`, `wsL2_wsL2Adj`, `wsL2Adj_wsL2_zero`, `sum_sum_wsCoeff_mul_wsCoeff`,
  `dxVecAdj_dxVecL2`, `sum_wsCoeff_mul_wsCoeff_right`, `dxVecL2_dxVecAdj`.
* `inner_dxL2`, `sum_dxL2_ιL2`, `sum_ιL2_dxL2`, **`ιL2_dxL2_add_dxL2_ιL2`**, `ιL2_dxL2_zero`.
* `dxL2_mem_maximal`.
* `hessianFormData_antilipschitz`, **`hessianFormData_regularDecomposition`**;
  `divDivFormData_antilipschitz`, **`divDivFormData_regularDecomposition`**.
* `dxL2_dxL2_add_dxL2_dxL2`, `dxL2_dxL2_self`, `wsFields_wsFieldsAdj`.
* `hessianFormData_exists_lt_norm`, **`hessianFormData_exists_forall_S_ne`**;
  `divDivFormData_exists_lt_norm`, **`divDivFormData_exists_forall_S_ne`**.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §4.1 (the Hessian and div–div
  diagrams), §2 (regular decompositions), §3 ((23), the hypothesis of Theorem 7)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (exterior algebra: `dxₐ ∧ ·` and its adjoint, the contraction)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Finset
open MeasureTheory

@[expose] public noncomputable section

/-! ### The exterior product with `dxₐ` -/

namespace Feec.FiniteElement

open Feec.Domain

variable {n : ℕ} {Ω : Set (Fin n → ℝ)}

/-- **The exterior product with `dxₐ`** on `L²(Ω; Λᵏ)`, `dxₐ ∧ φ = S(φ eₐ)` (`wsL2` of the vector
with `φ` in place `a`): `(dxₐ ∧ φ)_t = ε(a, t) φ_{t ∖ a}` for `a ∈ t`, and `0` otherwise
(`dxL2_apply`). -/
def dxL2 (k : ℤ) (a : Fin n) : L2F ℝ Ω (formIdx n k) →L[ℝ] L2F ℝ Ω (formIdx n (k + 1)) :=
  wsL2 k ∘L (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n =>
      L2F ℝ Ω (formIdx n k)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℝ (fun _ : Fin n => L2F ℝ Ω (formIdx n k)) a

theorem dxL2_eq (k : ℤ) (a : Fin n) (φ : L2F ℝ Ω (formIdx n k)) :
    dxL2 k a φ = wsL2 k (PiLp.single 2 a φ) := rfl

theorem dxL2_apply (k : ℤ) (a : Fin n) (φ : L2F ℝ Ω (formIdx n k)) (t : formIdx n (k + 1)) :
    dxL2 k a φ t = ∑ r, wsCoeff k t (a, r) • φ r := by
  rw [dxL2_eq, wsL2_apply, Fintype.sum_prod_type, Finset.sum_eq_single a (fun b _ hb => by
    simp [hb]) (by simp)]
  simp

/-- **The div–div connecting map** `(S φ)ₐ = dxₐ ∧ φ`, `L²(Ω; Λᵏ) → L²(Ω; Λᵏ⁺¹)ⁿ`. -/
def dxVecL2 (k : ℤ) :
    L2F ℝ Ω (formIdx n k) →L[ℝ] PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n (k + 1))) :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n =>
      L2F ℝ Ω (formIdx n (k + 1))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun a => dxL2 k a

@[simp] theorem dxVecL2_apply (k : ℤ) (φ : L2F ℝ Ω (formIdx n k)) (a : Fin n) :
    dxVecL2 k φ a = dxL2 k a φ := rfl

/-- The adjoint of `dxVecL2`, the sum of the contractions `Σₐ ι_{eₐ} wₐ`:
`(Sᵀ w)_r = Σₐ Σ_t c(t; a, r) (wₐ)_t`. -/
def dxVecAdj (k : ℤ) :
    PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n (k + 1))) →L[ℝ] L2F ℝ Ω (formIdx n k) :=
  ∑ a : Fin n, PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k)) a ∘L wsL2Adj k ∘L
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n (k + 1))) a

theorem dxVecAdj_apply (k : ℤ) (w : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n (k + 1))))
    (r : formIdx n k) : dxVecAdj k w r = ∑ a, ∑ t, wsCoeff k t (a, r) • w a t := by
  simp [dxVecAdj, wsL2Adj_apply]

/-! ### The fibre identities -/

theorem wsCoeff_mul_self {k : ℤ} (t : formIdx n (k + 1)) (p : Fin n × formIdx n k) :
    wsCoeff k t p * wsCoeff k t p = if p.1 ∈ t.1 ∧ t.1.erase p.1 = p.2.1 then 1 else 0 := by
  rw [← abs_mul_abs_self, abs_wsCoeff]
  split_ifs <;> norm_num

/-- `t = r ∪ {a}` is determined by `(a, r)`. -/
theorem eq_of_wsCoeff_ne_zero {k : ℤ} {t t' : formIdx n (k + 1)} {p : Fin n × formIdx n k}
    (h : wsCoeff k t p ≠ 0) (h' : wsCoeff k t' p ≠ 0) : t = t' := by
  rw [wsCoeff_eq] at h h'
  split_ifs at h h' with h1 h2
  · exact Subtype.ext (by rw [← Finset.insert_erase h1.1, ← Finset.insert_erase h2.1, h1.2, h2.2])
  all_goals exact absurd rfl ‹_›

/-- **`S Sᵀ = k + 1`** on the coefficients: `Σ_{a,r} c(t; a, r) c(t'; a, r) = (k + 1) [t = t']`
(the Euler identity `Σₐ dxₐ ∧ ι_{eₐ} = k + 1` on `(k + 1)`-forms). -/
theorem sum_wsCoeff_mul_wsCoeff (k : ℤ) (t t' : formIdx n (k + 1)) :
    ∑ p : Fin n × formIdx n k, wsCoeff k t p * wsCoeff k t' p =
      if t = t' then (k : ℝ) + 1 else 0 := by
  split_ifs with h
  · subst h
    rw [← sum_abs_wsCoeff_left k t]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [wsCoeff_mul_self, abs_wsCoeff]
  · refine Finset.sum_eq_zero fun p _ => ?_
    by_contra hp
    exact h (eq_of_wsCoeff_ne_zero (left_ne_zero_of_mul hp) (right_ne_zero_of_mul hp))

/-- **`S Sᵀ = k + 1` on coefficient fields**: `S (Sᵀ ψ) = (k + 1) ψ` (`sum_wsCoeff_mul_wsCoeff`). -/
theorem wsFields_wsFieldsAdj {F : Type*} [AddCommMonoid F] [Module ℝ F] (k : ℤ)
    (ψ : formIdx n (k + 1) → F) : wsFields k (wsFieldsAdj k ψ) = ((k : ℝ) + 1) • ψ := by
  funext t
  simp only [wsFields, wsFieldsAdj, Finset.smul_sum, smul_smul, Pi.smul_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, sum_wsCoeff_mul_wsCoeff, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **`S Sᵀ = k + 1`**: `S (Sᵀ w) = (k + 1) w` on `L²(Ω; Λᵏ⁺¹)` (`wsFields_wsFieldsAdj`). -/
theorem wsL2_wsL2Adj (k : ℤ) (w : L2F ℝ Ω (formIdx n (k + 1))) :
    wsL2 k (wsL2Adj k w) = ((k : ℝ) + 1) • w := by
  refine PiLp.ext fun t => ?_
  rw [wsL2_apply, PiLp.smul_apply]
  simp only [wsL2Adj_apply]
  exact congrFun (wsFields_wsFieldsAdj k fun t => w t) t

/-- The `0`-forms have one coefficient, that of `∅`. -/
theorem formIdx_zero_eq (r s : formIdx n 0) : r = s := by
  have hr : r.1 = ∅ := Finset.card_eq_zero.1 (by have := r.2; omega)
  have hs : s.1 = ∅ := Finset.card_eq_zero.1 (by have := s.2; omega)
  exact Subtype.ext (hr.trans hs.symm)

/-- The coefficients of `S` on the vector `0`-forms: `Σ_t c(t; a, ∅) c(t; b, ∅) = [a = b]`. -/
theorem sum_wsCoeff_mul_wsCoeff_zero (a b : Fin n) (r s : formIdx n 0) :
    ∑ t : formIdx n (0 + 1), wsCoeff 0 t (a, r) * wsCoeff 0 t (b, s) =
      if a = b then 1 else 0 := by
  have hr : ∀ r : formIdx n 0, r.1 = ∅ := fun r => Finset.card_eq_zero.1 (by have := r.2; omega)
  have hc : ∀ (t : formIdx n (0 + 1)) (c : Fin n) (r : formIdx n 0),
      wsCoeff 0 t (c, r) = if t.1 = {c} then 1 else 0 := by
    intro t c r
    rw [wsCoeff_eq]
    simp only [hr r]
    by_cases ht : t.1 = {c}
    · rw [ite_eq_left ⟨by simp [ht], by simp [ht]⟩, ite_eq_left ht, ht]
      simp [ExteriorFibre.sgn, Finset.filter_singleton]
    · rw [ite_eq_right ht, ite_eq_right]
      rintro ⟨hc, he⟩
      exact ht (by rw [← Finset.insert_erase hc, he]; rfl)
  simp only [hc]
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left rfl, Finset.sum_eq_single ⟨{a}, by simp⟩ (fun t _ ht => by
      rw [ite_eq_right fun h => ht (Subtype.ext h), zero_mul]) (by simp)]
    simp
  · rw [ite_eq_right hab]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ha : t.1 = {a}
    · rw [ite_eq_left ha,
        ite_eq_right (fun hb => hab (Finset.singleton_injective (ha.symm.trans hb))), mul_zero]
    · rw [ite_eq_right ha, zero_mul]

/-- **`S` is an isometry on vector `0`-forms** (`S⁰ = I` in vector proxies): `Sᵀ S = 1`. -/
theorem wsL2Adj_wsL2_zero (v : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n 0))) :
    wsL2Adj 0 (wsL2 0 v) = v := by
  refine PiLp.ext fun a => PiLp.ext fun r => ?_
  rw [wsL2Adj_apply]
  simp only [wsL2_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  simp only [← Finset.sum_smul, sum_wsCoeff_mul_wsCoeff_zero, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single a (fun b _ hb => Finset.sum_eq_zero fun s _ => ite_eq_right (Ne.symm hb))
    (by simp)]
  simp only [ite_true]
  exact Finset.sum_eq_single r (fun s _ hs => absurd (formIdx_zero_eq s r) hs) (by simp)

/-- `Σ_t c(t; a, r) c(t; a, r') = [r = r', a ∉ r]`: `t = r ∪ {a}`. -/
theorem sum_wsCoeff_mul_wsCoeff_left (k : ℤ) (a : Fin n) (r r' : formIdx n k) :
    ∑ t : formIdx n (k + 1), wsCoeff k t (a, r) * wsCoeff k t (a, r') =
      if r = r' ∧ a ∉ r.1 then 1 else 0 := by
  by_cases hrr : r = r'
  · subst hrr
    simp only [wsCoeff_mul_self, true_and]
    by_cases ha : a ∈ r.1
    · rw [ite_eq_right (not_not.2 ha)]
      refine Finset.sum_eq_zero fun t _ => ite_eq_right ?_
      rintro ⟨-, he⟩
      rw [← he] at ha
      exact Finset.notMem_erase a t.1 ha
    · rw [ite_eq_left ha, Finset.sum_eq_single ⟨insert a r.1, card_insert_of_formIdx r ha⟩]
      · rw [ite_eq_left ⟨Finset.mem_insert_self a r.1, Finset.erase_insert ha⟩]
      · intro t _ ht
        refine ite_eq_right ?_
        rintro ⟨hat, he⟩
        exact ht (Subtype.ext (by rw [← Finset.insert_erase hat, he]))
      · simp
  · rw [ite_eq_right (fun h => hrr h.1)]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [wsCoeff_eq, wsCoeff_eq]
    split_ifs with h1 h2
    · exact absurd (Subtype.ext (h1.2.symm.trans h2.2)) hrr
    all_goals simp

/-- **`Sᵀ S = n − k` for the div–div map** on the coefficients:
`Σₐ Σ_t c(t; a, r) c(t; a, r') = (n − k) [r = r']` (`Σₐ ι_{eₐ} (dxₐ ∧ ·) = n − k` on `k`-forms). -/
theorem sum_sum_wsCoeff_mul_wsCoeff (k : ℤ) (r r' : formIdx n k) :
    ∑ a : Fin n, ∑ t : formIdx n (k + 1), wsCoeff k t (a, r) * wsCoeff k t (a, r') =
      if r = r' then (n : ℝ) - k else 0 := by
  simp only [sum_wsCoeff_mul_wsCoeff_left]
  split_ifs with hrr
  · subst hrr
    simp only [true_and, Finset.sum_boole]
    have hcard : #({a : Fin n | a ∉ r.1} : Finset (Fin n)) = n - #r.1 := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
        Finset.card_univ, Fintype.card_fin, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hcard, Nat.cast_sub (by simpa using Finset.card_le_univ r.1)]
    have h : ((#r.1 : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast r.2
    rw [h]
  · simp [hrr]

/-- **`Sᵀ S = n − k`**: `Sᵀ (S φ) = (n − k) φ` for the div–div map. -/
theorem dxVecAdj_dxVecL2 (k : ℤ) (φ : L2F ℝ Ω (formIdx n k)) :
    dxVecAdj k (dxVecL2 k φ) = ((n : ℝ) - k) • φ := by
  refine PiLp.ext fun r => ?_
  rw [dxVecAdj_apply, PiLp.smul_apply]
  simp only [dxVecL2_apply, dxL2_apply, Finset.smul_sum, smul_smul]
  have key : ∀ a : Fin n, ∑ t : formIdx n (k + 1), ∑ r' : formIdx n k,
      (wsCoeff k t (a, r) * wsCoeff k t (a, r')) • φ r' = ∑ r' : formIdx n k,
        (∑ t : formIdx n (k + 1), wsCoeff k t (a, r) * wsCoeff k t (a, r')) • φ r' := fun a => by
    rw [Finset.sum_comm]
    simp only [Finset.sum_smul]
  rw [Finset.sum_congr rfl fun a _ => key a, Finset.sum_comm]
  simp only [← Finset.sum_smul, sum_sum_wsCoeff_mul_wsCoeff, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- `Σ_r c(t; a, r) c(t; b, r) = [a = b, a ∈ t]`: `r = t ∖ {a}`. -/
theorem sum_wsCoeff_mul_wsCoeff_right (k : ℤ) (t : formIdx n (k + 1)) (a b : Fin n) :
    ∑ r : formIdx n k, wsCoeff k t (a, r) * wsCoeff k t (b, r) =
      if a = b ∧ a ∈ t.1 then 1 else 0 := by
  by_cases hab : a = b
  · subst hab
    simp only [wsCoeff_mul_self, true_and]
    by_cases ha : a ∈ t.1
    · rw [ite_eq_left ha, Finset.sum_eq_single ⟨t.1.erase a, card_erase_of_formIdx t ha⟩]
      · rw [ite_eq_left ⟨ha, rfl⟩]
      · intro r _ hr
        exact ite_eq_right fun h => hr (Subtype.ext h.2.symm)
      · simp
    · rw [ite_eq_right ha]
      exact Finset.sum_eq_zero fun r _ => ite_eq_right fun h => ha h.1
  · rw [ite_eq_right fun h => hab h.1]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [wsCoeff_eq, wsCoeff_eq]
    split_ifs with h1 h2
    · have hb : b ∈ t.1.erase a := Finset.mem_erase.2 ⟨Ne.symm hab, h2.1⟩
      rw [h1.2, ← h2.2] at hb
      exact absurd hb (Finset.notMem_erase b t.1)
    all_goals simp

/-- In the top degree there is one coefficient, that of `{0, …, n - 1}`. -/
theorem formIdx_top_univ {k : ℤ} (hk : k + 1 = n) (t : formIdx n (k + 1)) :
    t.1 = Finset.univ :=
  Finset.eq_univ_of_card _ (by have := t.2; rw [Fintype.card_fin]; omega)

theorem formIdx_top_eq {k : ℤ} (hk : k + 1 = n) (t t' : formIdx n (k + 1)) : t = t' :=
  Subtype.ext ((formIdx_top_univ hk t).trans (formIdx_top_univ hk t').symm)

/-- **`S Sᵀ = 1` for the div–div map in the top degree** `k + 1 = n`. -/
theorem dxVecL2_dxVecAdj {k : ℤ} (hk : k + 1 = n)
    (w : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n (k + 1)))) :
    dxVecL2 k (dxVecAdj k w) = w := by
  refine PiLp.ext fun a => PiLp.ext fun t => ?_
  rw [dxVecL2_apply, dxL2_apply]
  simp only [dxVecAdj_apply, Finset.smul_sum, smul_smul]
  calc ∑ r, ∑ b, ∑ t', (wsCoeff k t (a, r) * wsCoeff k t' (b, r)) • w b t'
      = ∑ b, (∑ r, wsCoeff k t (a, r) * wsCoeff k t (b, r)) • w b t := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_eq_single t (fun t' _ ht' => absurd (formIdx_top_eq hk t' t) ht')
          (by simp)]
    _ = w a t := by
        simp only [sum_wsCoeff_mul_wsCoeff_right, ite_smul, one_smul, zero_smul]
        rw [Finset.sum_eq_single a (fun b _ hb => ite_eq_right fun h => hb h.1.symm) (by simp),
          ite_eq_left ⟨rfl, (formIdx_top_univ hk t).symm ▸ Finset.mem_univ a⟩]

/-! ### The contraction and the Cartan identity -/

/-- **The contraction** `ι_c = ι_{e_c}` on `L²(Ω; Λᵏ⁺¹)`, the component `c` of `Sᵀ`:
`(ι_c w)_r = Σ_t c(t; c, r) w_t`, the adjoint of `dx_c ∧ ·` (`inner_dxL2`). -/
def ιL2 (k : ℤ) (c : Fin n) : L2F ℝ Ω (formIdx n (k + 1)) →L[ℝ] L2F ℝ Ω (formIdx n k) :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k)) c ∘L wsL2Adj k

theorem ιL2_eq (k : ℤ) (c : Fin n) (w : L2F ℝ Ω (formIdx n (k + 1))) :
    ιL2 k c w = wsL2Adj k w c := rfl

theorem ιL2_apply (k : ℤ) (c : Fin n) (w : L2F ℝ Ω (formIdx n (k + 1))) (r : formIdx n k) :
    ιL2 k c w r = ∑ t, wsCoeff k t (c, r) • w t :=
  wsL2Adj_apply w c r

/-- `⟪dx_c ∧ φ, w⟫ = ⟪φ, ι_c w⟫`. -/
theorem inner_dxL2 (k : ℤ) (c : Fin n) (φ : L2F ℝ Ω (formIdx n k))
    (w : L2F ℝ Ω (formIdx n (k + 1))) : ⟪dxL2 k c φ, w⟫_ℝ = ⟪φ, ιL2 k c w⟫_ℝ := by
  rw [dxL2_eq, inner_wsL2, real_inner_comm, PiLp.single, inner_toLp_single, real_inner_comm,
    ιL2_eq]

/-- `S v = Σ_c dx_c ∧ v_c`. -/
theorem wsL2_eq_sum (k : ℤ) (v : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) :
    wsL2 k v = ∑ c, dxL2 k c (v c) := by
  conv_lhs => rw [show v = ∑ c, PiLp.single 2 c (v c) from
    PiLp.ext fun a => by simp [Finset.sum_apply]]
  rw [map_sum]
  rfl

/-- **The Euler identity** `Σ_c dx_c ∧ ι_c = k + 1` on `L²(Ω; Λᵏ⁺¹)` (`S Sᵀ = k + 1`). -/
theorem sum_dxL2_ιL2 (k : ℤ) (w : L2F ℝ Ω (formIdx n (k + 1))) :
    ∑ c, dxL2 k c (ιL2 k c w) = ((k : ℝ) + 1) • w := by
  rw [← wsL2_wsL2Adj, wsL2_eq_sum]
  rfl

/-- `Sᵀ w = Σ_c ι_c w_c` for the div–div map. -/
theorem dxVecAdj_eq_sum (k : ℤ) (w : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n (k + 1)))) :
    dxVecAdj k w = ∑ c, ιL2 k c (w c) := by
  simp [dxVecAdj, ιL2]

/-- **`Σ_c ι_c (dx_c ∧ ·) = n − k`** on `L²(Ω; Λᵏ)` (`Sᵀ S = n − k` for the div–div map). -/
theorem sum_ιL2_dxL2 (k : ℤ) (φ : L2F ℝ Ω (formIdx n k)) :
    ∑ c, ιL2 k c (dxL2 k c φ) = ((n : ℝ) - k) • φ := by
  rw [← dxVecAdj_dxVecL2, dxVecAdj_eq_sum]
  rfl

/-- `Σ_s c(r; a, s) c(r'; a, s) = [r = r', a ∈ r]`: `s = r ∖ {a}`. -/
theorem sum_wsCoeff_mul_wsCoeff_same (k : ℤ) (a : Fin n) (r r' : formIdx n (k + 1)) :
    ∑ s : formIdx n k, wsCoeff k r (a, s) * wsCoeff k r' (a, s) =
      if r = r' ∧ a ∈ r.1 then 1 else 0 := by
  by_cases hrr : r = r'
  · subst hrr
    rw [sum_wsCoeff_mul_wsCoeff_right]
    simp
  · rw [ite_eq_right fun h => hrr h.1]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_contra hs
    exact hrr (eq_of_wsCoeff_ne_zero (left_ne_zero_of_mul hs) (right_ne_zero_of_mul hs))

/-- **The Cartan identity on the coefficients**:
`Σ_t c(t; c, r) c(t; c', r') + Σ_s c(r; c', s) c(r'; c, s) = [c = c'] [r = r']`
(`ι_c (dx_{c'} ∧ ·) + dx_{c'} ∧ ι_c · = δ_{cc'}`). -/
theorem wsCoeff_cartan (k : ℤ) (c c' : Fin n) (r r' : formIdx n (k + 1)) :
    ∑ t : formIdx n (k + 1 + 1), wsCoeff (k + 1) t (c, r) * wsCoeff (k + 1) t (c', r') +
      ∑ s : formIdx n k, wsCoeff k r (c', s) * wsCoeff k r' (c, s) =
        if c = c' ∧ r = r' then 1 else 0 := by
  by_cases hcc : c = c'
  · subst hcc
    rw [sum_wsCoeff_mul_wsCoeff_left, sum_wsCoeff_mul_wsCoeff_same]
    by_cases hrr : r = r'
    · subst hrr
      by_cases hc : c ∈ r.1 <;> simp [hc]
    · simp [hrr]
  rw [ite_eq_right fun h => hcc h.1]
  by_cases hP : c ∉ r.1 ∧ c' ∈ r.1 ∧ r'.1 = insert c (r.1.erase c')
  · -- one term each: `t = r ∪ {c}` and `s = r ∖ {c'}`
    obtain ⟨hcr, hc'r, hr'⟩ := hP
    have ht : (#(insert c r.1) : ℤ) = k + 1 + 1 := card_insert_of_formIdx r hcr
    have hs : (#(r.1.erase c') : ℤ) = k := card_erase_of_formIdx r hc'r
    have hcs : c ∉ r.1.erase c' := fun h => hcr (Finset.mem_of_mem_erase h)
    rw [Finset.sum_eq_single ⟨insert c r.1, ht⟩ (fun t _ ht' => by
        refine mul_eq_zero.2 (Or.inl ?_)
        rw [wsCoeff_eq, ite_eq_right]
        rintro ⟨h1, h2⟩
        exact ht' (Subtype.ext (by rw [← Finset.insert_erase h1, h2]))) (by simp),
      Finset.sum_eq_single ⟨r.1.erase c', hs⟩ (fun s _ hs' => by
        refine mul_eq_zero.2 (Or.inl ?_)
        rw [wsCoeff_eq, ite_eq_right]
        rintro ⟨-, h2⟩
        exact hs' (Subtype.ext h2.symm)) (by simp)]
    simp only [wsCoeff_eq]
    have h1 : c ∈ insert c r.1 ∧ (insert c r.1).erase c = r.1 :=
      ⟨Finset.mem_insert_self c r.1, Finset.erase_insert hcr⟩
    have h2 : c' ∈ insert c r.1 ∧ (insert c r.1).erase c' = r'.1 := by
      refine ⟨Finset.mem_insert_of_mem hc'r, ?_⟩
      rw [hr', Finset.erase_insert_of_ne hcc]
    have h3 : c' ∈ r.1 ∧ True := ⟨hc'r, trivial⟩
    have h4 : c ∈ r'.1 ∧ r'.1.erase c = r.1.erase c' := by
      rw [hr']
      exact ⟨Finset.mem_insert_self c _, Finset.erase_insert hcs⟩
    rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h3, ite_eq_left h4, hr',
      ExteriorFibre.sgn_insert_self, ExteriorFibre.sgn_insert hcr, ExteriorFibre.sgn_insert_self,
      ExteriorFibre.sgn_erase hc'r]
    have := ExteriorFibre.ite_lt_add_ite_lt (R := ℝ) hcc
    linear_combination (ExteriorFibre.sgn c r.1 * ExteriorFibre.sgn c' r.1 : ℝ) * this
  · -- off the pattern `r' = r ∖ {c'} ∪ {c}`, both sums vanish termwise
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro s _
      rw [wsCoeff_eq, wsCoeff_eq]
      split_ifs with h1 h2
      · exfalso
        refine hP ⟨fun hcr => ?_, h1.1, ?_⟩
        · have : c ∈ s.1 := by
            rw [← h1.2]; exact Finset.mem_erase.2 ⟨hcc, hcr⟩
          rw [← h2.2] at this
          exact Finset.notMem_erase c r'.1 this
        · rw [← Finset.insert_erase h2.1, h2.2, h1.2]
      all_goals simp
    · intro t _
      rw [wsCoeff_eq, wsCoeff_eq]
      split_ifs with h1 h2
      · exfalso
        refine hP ⟨by rw [← h1.2]; exact Finset.notMem_erase c t.1,
          by rw [← h1.2]; exact Finset.mem_erase.2 ⟨Ne.symm hcc, h2.1⟩, ?_⟩
        rw [← h2.2, ← h1.2]
        conv_lhs => rw [← Finset.insert_erase h1.1]
        rw [Finset.erase_insert_of_ne hcc]
      all_goals simp

/-- **The Cartan identity** `ι_c (dx_{c'} ∧ w) + dx_{c'} ∧ ι_c w = δ_{cc'} w` on
`L²(Ω; Λᵏ⁺¹)`. -/
theorem ιL2_dxL2_add_dxL2_ιL2 (k : ℤ) (c c' : Fin n) (w : L2F ℝ Ω (formIdx n (k + 1))) :
    ιL2 (k + 1) c (dxL2 (k + 1) c' w) + dxL2 k c' (ιL2 k c w) = if c = c' then w else 0 := by
  refine PiLp.ext fun r => ?_
  rw [PiLp.add_apply, ιL2_apply, dxL2_apply]
  simp only [dxL2_apply, ιL2_apply, Finset.smul_sum, smul_smul]
  calc ∑ t, ∑ r', (wsCoeff (k + 1) t (c, r) * wsCoeff (k + 1) t (c', r')) • w r' +
        ∑ s, ∑ t', (wsCoeff k r (c', s) * wsCoeff k t' (c, s)) • w t'
      = ∑ r', (∑ t, wsCoeff (k + 1) t (c, r) * wsCoeff (k + 1) t (c', r') +
          ∑ s, wsCoeff k r (c', s) * wsCoeff k r' (c, s)) • w r' := by
        rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := formIdx n k)),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun r' _ => ?_
        rw [add_smul, Finset.sum_smul, Finset.sum_smul]
    _ = (if c = c' then w else 0) r := by
        simp only [wsCoeff_cartan, ite_smul, one_smul, zero_smul]
        split_ifs with h
        · rw [Finset.sum_eq_single r (fun r' _ hr' => ite_eq_right fun h' => hr' h'.2.symm)
            (by simp), ite_eq_left ⟨h, rfl⟩]
        · rw [PiLp.zero_apply]
          exact Finset.sum_eq_zero fun r' _ => ite_eq_right fun h' => h h'.1

/-- **The Cartan identity on `0`-forms** `ι_c (dx_{c'} ∧ φ) = δ_{cc'} φ` (`Sᵀ S = 1` on vector
`0`-forms). -/
theorem ιL2_dxL2_zero (c c' : Fin n) (φ : L2F ℝ Ω (formIdx n 0)) :
    ιL2 0 c (dxL2 0 c' φ) = if c = c' then φ else 0 := by
  rw [ιL2_eq, dxL2_eq, wsL2Adj_wsL2_zero]
  by_cases h : c = c'
  · subst h
    simp
  · simp [h]

/-- The Cartan identity as `ι_c (dx_{c'} ∧ w) = δ_{cc'} w - dx_{c'} ∧ ι_c w`. -/
theorem ιL2_dxL2 (k : ℤ) (c c' : Fin n) (w : L2F ℝ Ω (formIdx n (k + 1))) :
    ιL2 (k + 1) c (dxL2 (k + 1) c' w) = (if c = c' then w else 0) - dxL2 k c' (ιL2 k c w) :=
  eq_sub_of_add_eq (ιL2_dxL2_add_dxL2_ιL2 k c c' w)

/-! ### `dxₐ ∧ dx_c ∧ · = -dx_c ∧ dxₐ ∧ ·` -/

/-- `Σ_{r'} c(t; a, r') X(r') = ε(a, t) X(t ∖ a)` for `a ∈ t`, and `0` otherwise. -/
theorem sum_wsCoeff_mul (k : ℤ) (a : Fin n) (t : formIdx n (k + 1)) (X : formIdx n k → ℝ) :
    ∑ r, wsCoeff k t (a, r) * X r =
      if h : a ∈ t.1 then ExteriorFibre.sgn a t.1 * X ⟨t.1.erase a, card_erase_of_formIdx t h⟩
      else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨t.1.erase a, card_erase_of_formIdx t h⟩ (fun r _ hr => by
        rw [wsCoeff_eq, ite_eq_right fun h' => hr (Subtype.ext h'.2.symm), zero_mul]) (by simp),
      wsCoeff_eq, ite_eq_left ⟨h, rfl⟩]
  · exact Finset.sum_eq_zero fun r _ => by rw [wsCoeff_eq, ite_eq_right fun h' => h h'.1, zero_mul]

/-- **`dxₐ ∧ dx_c ∧ · = -dx_c ∧ dxₐ ∧ ·` on the coefficients**:
`Σ_{r'} (c(t; a, r') c(r'; c, r) + c(t; c, r') c(r'; a, r)) = 0`. -/
theorem sum_wsCoeff_mul_wsCoeff_add (k : ℤ) (a c : Fin n) (t : formIdx n (k + 1 + 1))
    (r : formIdx n k) :
    ∑ r', (wsCoeff (k + 1) t (a, r') * wsCoeff k r' (c, r) +
      wsCoeff (k + 1) t (c, r') * wsCoeff k r' (a, r)) = 0 := by
  rw [Finset.sum_add_distrib, sum_wsCoeff_mul, sum_wsCoeff_mul]
  by_cases hac : a = c
  · subst hac
    split_ifs with h
    · rw [wsCoeff_eq, ite_eq_right fun h' => Finset.notMem_erase a t.1 h'.1]; ring
    · ring
  by_cases ha : a ∈ t.1
  · by_cases hc : c ∈ t.1
    · simp only [ha, hc, ↓reduceDIte]
      rw [wsCoeff_eq, wsCoeff_eq]
      have hca : c ∈ t.1.erase a := Finset.mem_erase.2 ⟨Ne.symm hac, hc⟩
      have hac' : a ∈ t.1.erase c := Finset.mem_erase.2 ⟨hac, ha⟩
      simp only [hca, hac', true_and, Finset.erase_right_comm (s := t.1) (a := a) (b := c)]
      split_ifs
      · rw [ExteriorFibre.sgn_erase ha, ExteriorFibre.sgn_erase hc]
        have := ExteriorFibre.ite_lt_add_ite_lt (R := ℝ) hac
        linear_combination (ExteriorFibre.sgn a t.1 * ExteriorFibre.sgn c t.1 : ℝ) * this
      · ring
    · simp only [ha, hc, ↓reduceDIte]
      rw [wsCoeff_eq, ite_eq_right fun h' => hc (Finset.mem_of_mem_erase h'.1)]; ring
  · simp only [ha, ↓reduceDIte]
    split_ifs with hc
    · rw [wsCoeff_eq, ite_eq_right fun h' => ha (Finset.mem_of_mem_erase h'.1)]; ring
    · ring

/-- **`dxₐ ∧ dx_c ∧ φ + dx_c ∧ dxₐ ∧ φ = 0`** on `L²(Ω; Λᵏ)`. -/
theorem dxL2_dxL2_add_dxL2_dxL2 (k : ℤ) (a c : Fin n) (φ : L2F ℝ Ω (formIdx n k)) :
    dxL2 (k + 1) a (dxL2 k c φ) + dxL2 (k + 1) c (dxL2 k a φ) = 0 := by
  refine PiLp.ext fun t => ?_
  rw [PiLp.add_apply, dxL2_apply, dxL2_apply, PiLp.zero_apply]
  simp only [dxL2_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := formIdx n (k + 1))),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [← Finset.sum_add_distrib]
  simp only [← add_smul]
  rw [← Finset.sum_smul, sum_wsCoeff_mul_wsCoeff_add, zero_smul]

/-- **`dxₐ ∧ dxₐ ∧ φ = 0`** on `L²(Ω; Λᵏ)`. -/
theorem dxL2_dxL2_self (k : ℤ) (a : Fin n) (φ : L2F ℝ Ω (formIdx n k)) :
    dxL2 (k + 1) a (dxL2 k a φ) = 0 := by
  have h := dxL2_dxL2_add_dxL2_dxL2 k a a φ
  rw [← two_smul ℝ] at h
  exact (smul_eq_zero.1 h).resolve_left two_ne_zero

/-! ### `H¹` fields -/

variable (hΩ : IsOpen Ω)
include hΩ

omit hΩ in
theorem wsL2Adj_apply_eq_ofMatrixCLM (k : ℤ) (w : L2F ℝ Ω (formIdx n (k + 1))) (a : Fin n) :
    wsL2Adj k w a = L2F.ofMatrixCLM (Matrix.of fun r t => wsCoeff k t (a, r)) w :=
  PiLp.ext fun r => by rw [wsL2Adj_apply, L2F.ofMatrixCLM_apply]; rfl

/-- `Sᵀ` maps `H¹` to `H¹` (constant coefficients). -/
theorem wsL2Adj_mem_fieldH1 (k : ℤ) {w : L2F ℝ Ω (formIdx n (k + 1))}
    (hw : w ∈ fieldH1 ℝ Ω (formIdx n (k + 1))) (a : Fin n) :
    wsL2Adj k w a ∈ fieldH1 ℝ Ω (formIdx n k) := by
  rw [wsL2Adj_apply_eq_ofMatrixCLM]
  exact ofMatrixCLM_mem_fieldH1 hΩ _ hw

/-- The sum of the contractions maps vectors of `H¹` fields to `H¹`. -/
theorem dxVecAdj_mem_fieldH1 (k : ℤ) {w : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n (k + 1)))}
    (hw : ∀ a, w a ∈ fieldH1 ℝ Ω (formIdx n (k + 1))) :
    dxVecAdj k w ∈ fieldH1 ℝ Ω (formIdx n k) := by
  have : dxVecAdj k w = ∑ a, wsL2Adj k (w a) a := by simp [dxVecAdj]
  rw [this]
  exact Submodule.sum_mem _ fun a _ => wsL2Adj_mem_fieldH1 hΩ k (hw a) a

/-- `dx_c ∧ ·` maps `H¹` to `H¹` (constant coefficients). -/
theorem dxL2_mem_fieldH1 (k : ℤ) (c : Fin n) {φ : L2F ℝ Ω (formIdx n k)}
    (hφ : φ ∈ fieldH1 ℝ Ω (formIdx n k)) : dxL2 k c φ ∈ fieldH1 ℝ Ω (formIdx n (k + 1)) := by
  have : dxL2 k c φ = L2F.ofMatrixCLM (Matrix.of fun t r => wsCoeff k t (c, r)) φ :=
    PiLp.ext fun t => by rw [dxL2_apply, L2F.ofMatrixCLM_apply]; rfl
  rw [this]
  exact ofMatrixCLM_mem_fieldH1 hΩ _ hφ

/-- `S = Σₐ dxₐ ∧ ·` maps vectors of `H¹` fields to `H¹`. -/
theorem wsL2_mem_fieldH1 (k : ℤ) {v : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))}
    (hv : ∀ a, v a ∈ fieldH1 ℝ Ω (formIdx n k)) : wsL2 k v ∈ fieldH1 ℝ Ω (formIdx n (k + 1)) := by
  rw [wsL2_eq_sum]
  exact Submodule.sum_mem _ fun c _ => dxL2_mem_fieldH1 hΩ k c (hv c)

/-! ### The maps on the maximal domains -/

/-- **`dxₐ ∧ ·` maps `D(d_max)` into `D(d_max)` with `d (dxₐ ∧ φ) = −dxₐ ∧ dφ`.** -/
theorem dxL2_mem_maximal (k : ℤ) (a : Fin n) {φ : L2F ℝ Ω (formIdx n k)}
    (hφ : φ ∈ ((extDerivOp ℝ n k).maximal Ω).domain) :
    ∃ h : dxL2 k a φ ∈ ((extDerivOp ℝ n (k + 1)).maximal Ω).domain,
      (extDerivOp ℝ n (k + 1)).maximal Ω ⟨_, h⟩ =
        -dxL2 (k + 1) a ((extDerivOp ℝ n k).maximal Ω ⟨φ, hφ⟩) := by
  have hv : ∀ b, (PiLp.single 2 a φ : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) b ∈
      ((extDerivOp ℝ n k).maximal Ω).domain := fun b => by
    by_cases hb : b = a
    · subst hb; simpa using hφ
    · simp [hb]
  obtain ⟨h, e⟩ := wsL2_mem_maximal hΩ k hv
  refine ⟨h, e.trans ?_⟩
  rw [dxL2_eq]
  congr 2
  refine PiLp.ext fun b => ?_
  by_cases hb : b = a
  · subst hb
    exact (LinearPMap.apply_eq_of_eq rfl _ ⟨φ, hφ⟩ (by simp)).trans
      (PiLp.single_eq_same (β := fun _ : Fin n => L2F ℝ Ω (formIdx n (k + 1))) 2 b _).symm
  · exact (LinearPMap.apply_eq_of_eq rfl _ 0 (by simp [hb])).trans
      ((LinearPMap.map_zero _).trans
        (PiLp.single_eq_of_ne (β := fun _ : Fin n => L2F ℝ Ω (formIdx n (k + 1))) 2 hb _).symm)

/-! ### The rows and the BGG data -/

variable (n) in
/-- `HΛ(Ω)`: the maximal `L²` de Rham complex. -/
abbrev formRow : HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ Ω (formIdx n k) :=
  (deRham ℝ n).maximalComplex hΩ

variable (n) in
/-- `HΛ(Ω) ⊗ ℝⁿ`: vectors of forms, with the componentwise exterior derivative. -/
abbrev vecRow :
    HilbertComplex ℝ (ComplexShape.up ℤ) fun k => PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k)) :=
  (formRow n hΩ).pi (Fin n)

theorem formRow_d (k : ℤ) : (formRow n hΩ).d k (k + 1) = (extDerivOp ℝ n k).maximal Ω :=
  deRham_maximalComplex_d hΩ k

theorem mem_formRow_domain {k : ℤ} {φ : L2F ℝ Ω (formIdx n k)} :
    φ ∈ ((formRow n hΩ).d k (k + 1)).domain ↔ φ ∈ ((extDerivOp ℝ n k).maximal Ω).domain := by
  rw [formRow_d]

theorem mem_vecRow_domain {k : ℤ} {v : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))} :
    v ∈ ((vecRow n hΩ).d k (k + 1)).domain ↔
      ∀ a, v a ∈ ((extDerivOp ℝ n k).maximal Ω).domain := by
  rw [HilbertComplex.pi_d, HilbertComplex.piD_domain, HilbertComplex.mem_piDomain, formRow_d]

theorem vecRow_d_apply {k : ℤ} (v : ((vecRow n hΩ).d k (k + 1)).domain) (a : Fin n) :
    (vecRow n hΩ).d k (k + 1) v a =
      (extDerivOp ℝ n k).maximal Ω ⟨(v : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) a,
        (mem_vecRow_domain hΩ).1 v.2 a⟩ := by
  rw [HilbertComplex.pi_d_apply]
  exact LinearPMap.apply_eq_of_eq (formRow_d hΩ k) _ _ rfl

/-- **The Hessian diagram of forms** on `Ω`: `HΛ(Ω)` over `HΛ(Ω) ⊗ ℝⁿ`, linked by
`S v = Σₐ dxₐ ∧ vₐ` ([ArnoldHu2021], §4.1). -/
def hessianFormData : BGG.HilbertData ℝ (ComplexShape.up ℤ) (fun k => L2F ℝ Ω (formIdx n k))
    (fun k => PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) :=
  BGG.HilbertData.ofSucc (formRow n hΩ) (vecRow n hΩ) (fun k => wsL2 k)
    (fun k φ => by
      rw [formRow_d]
      exact (wsL2_mem_maximal hΩ k ((mem_vecRow_domain hΩ).1 φ.2)).1)
    (fun k φ => by
      obtain ⟨h, e⟩ := wsL2_mem_maximal hΩ k ((mem_vecRow_domain hΩ).1 φ.2)
      rw [LinearPMap.apply_eq_of_eq (formRow_d hΩ (k + 1)) _ ⟨_, h⟩ rfl, e]
      congr 2
      exact PiLp.ext fun a => (vecRow_d_apply hΩ φ a).symm)

@[simp] theorem hessianFormData_S (k : ℤ) : (hessianFormData hΩ).S k (k + 1) = wsL2 k :=
  BGG.HilbertData.succCLM_succ (X := fun k => PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k)))
    (Y := fun k => L2F ℝ Ω (formIdx n k)) (fun k => wsL2 k) k

/-- **The div–div diagram of forms** on `Ω`: `HΛ(Ω) ⊗ ℝⁿ` over `HΛ(Ω)`, linked by
`(S φ)ₐ = dxₐ ∧ φ` ([ArnoldHu2021], §4.1). -/
def divDivFormData : BGG.HilbertData ℝ (ComplexShape.up ℤ)
    (fun k => PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) (fun k => L2F ℝ Ω (formIdx n k)) :=
  BGG.HilbertData.ofSucc (vecRow n hΩ) (formRow n hΩ) (fun k => dxVecL2 k)
    (fun k φ => (mem_vecRow_domain hΩ).2 fun a =>
      (dxL2_mem_maximal hΩ k a ((mem_formRow_domain hΩ).1 φ.2)).1)
    (fun k φ => by
      have hφ := (mem_formRow_domain hΩ).1 φ.2
      refine PiLp.ext fun a => ?_
      obtain ⟨h, e⟩ := dxL2_mem_maximal hΩ k a hφ
      rw [vecRow_d_apply, PiLp.neg_apply,
        LinearPMap.apply_eq_of_eq (formRow_d hΩ k) φ ⟨_, hφ⟩ rfl]
      exact (LinearPMap.apply_eq_of_eq rfl _ ⟨_, h⟩ rfl).trans e)

@[simp] theorem divDivFormData_S (k : ℤ) : (divDivFormData hΩ).S k (k + 1) = dxVecL2 k :=
  BGG.HilbertData.succCLM_succ (X := fun k => L2F ℝ Ω (formIdx n k))
    (Y := fun k => PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) (fun k => dxVecL2 k) k

/-! ### Bounded below -/

/-- **`S` is bounded below up to `0`** in the Hessian diagram (`S⁰` is an isometry; below the
spaces are zero). -/
theorem hessianFormData_antilipschitz :
    ∀ i ≤ 0, ∃ K, AntilipschitzWith K ((hessianFormData hΩ).S i (i + 1)) := by
  intro i hi
  rw [hessianFormData_S]
  rcases lt_or_eq_of_le hi with hi | rfl
  · have := subsingleton_vec_formIdx (Ω := Ω) (n := n) hi
    exact ⟨0, AntilipschitzWith.of_subsingleton⟩
  · exact ⟨_, (wsL2Adj 0).lipschitzWith.to_rightInverse wsL2Adj_wsL2_zero⟩

/-- **`S` is bounded below up to `n − 1`** in the div–div diagram (`Sᵀ S = n − k`). -/
theorem divDivFormData_antilipschitz :
    ∀ i ≤ (n : ℤ) - 1, ∃ K, AntilipschitzWith K ((divDivFormData hΩ).S i (i + 1)) := by
  intro i hi
  rw [divDivFormData_S]
  have hne : ((n : ℝ) - i) ≠ 0 := by
    have : (i : ℝ) ≤ (n : ℝ) - 1 := by exact_mod_cast hi
    linarith
  refine ⟨_, (((n : ℝ) - i)⁻¹ • dxVecAdj i).lipschitzWith.to_rightInverse fun φ => ?_⟩
  rw [_root_.smul_apply, dxVecAdj_dxVecL2, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-! ### Regular decompositions -/

omit hΩ in
/-- **The `H¹`-regular decompositions of `HΛ(Ω) ⊗ ℝⁿ`**, componentwise from those of `HΛ(Ω)`. -/
theorem vecRow_exists_sub_mem_fieldH1 {J : ℤ} (h : (deRham ℝ n).HasRegularDecomposition Ω J)
    {i : ℤ} (hi : J ≤ i) {u : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n (i + 1)))}
    (hu : ∀ a, u a ∈ ((extDerivOp ℝ n (i + 1)).maximal Ω).domain) :
    ∃ p : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n i)),
      ∃ hp : ∀ a, p a ∈ ((extDerivOp ℝ n i).maximal Ω).domain,
        ∀ a, u a - (extDerivOp ℝ n i).maximal Ω ⟨p a, hp a⟩ ∈ fieldH1 ℝ Ω (formIdx n (i + 1)) := by
  have h' : ∀ a, ∃ p : ((extDerivOp ℝ n i).maximal Ω).domain,
      u a - (extDerivOp ℝ n i).maximal Ω p ∈ fieldH1 ℝ Ω (formIdx n (i + 1)) :=
    fun a => h i hi (u a) (hu a)
  choose p hp using h'
  exact ⟨WithLp.toLp 2 fun a => (p a).1, fun a => (p a).2, hp⟩

/-- **The `L²` splittings of the Hessian diagram** from the `H¹`-regular decompositions of `HΛ(Ω)`
from `0` on: every `u ∈ D(dⁱ⁺¹)`, `i ≥ 0`, is `dⁱ p + Sⁱ φ`; for `u = d p + w`, `w ∈ H¹`, take
`φ = (i + 1)⁻¹ Sᵀ w`, an `H¹` field, so `S φ = w` (`wsL2_wsL2Adj`) ([ArnoldHu2021], §2, Theorem 3
and §4). -/
theorem hessianFormData_exists_add_eq (h : (deRham ℝ n).HasRegularDecomposition Ω 0) {i : ℤ}
    (hi : 0 ≤ i) {u : L2F ℝ Ω (formIdx n (i + 1))}
    (hu : u ∈ ((formRow n hΩ).d (i + 1) (i + 1 + 1)).domain) :
    ∃ (p : ((formRow n hΩ).d i (i + 1)).domain) (φ : ((vecRow n hΩ).d i (i + 1)).domain),
      (formRow n hΩ).d i (i + 1) p + (hessianFormData hΩ).S i (i + 1) φ = u := by
  rw [formRow_d] at hu
  have h' : ∃ p : ((extDerivOp ℝ n i).maximal Ω).domain,
      u - (extDerivOp ℝ n i).maximal Ω p ∈ fieldH1 ℝ Ω (formIdx n (i + 1)) := h i hi u hu
  obtain ⟨p, hp⟩ := h'
  have hcoef : ((i : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) ≤ i := by exact_mod_cast hi
    linarith
  set w := u - (extDerivOp ℝ n i).maximal Ω p
  have hφ : ((i : ℝ) + 1)⁻¹ • wsL2Adj i w ∈ ((vecRow n hΩ).d i (i + 1)).domain :=
    (mem_vecRow_domain hΩ).2 fun a => fieldH1_le_extDerivOp_maximal hΩ i
      (Submodule.smul_mem _ _ (wsL2Adj_mem_fieldH1 hΩ i hp a))
  have hpm : (p : L2F ℝ Ω (formIdx n i)) ∈ ((formRow n hΩ).d i (i + 1)).domain :=
    (mem_formRow_domain hΩ).2 p.2
  refine ⟨⟨_, hpm⟩, ⟨_, hφ⟩, ?_⟩
  rw [hessianFormData_S, LinearPMap.apply_eq_of_eq (formRow_d hΩ i) ⟨_, hpm⟩ p rfl, map_smul,
    wsL2_wsL2Adj, smul_smul, inv_mul_cancel₀ hcoef, one_smul]
  simp only [w]
  abel

/-- **The regular decompositions of the Hessian diagram** (`hessianFormData_exists_add_eq`). -/
theorem hessianFormData_regularDecomposition (h : (deRham ℝ n).HasRegularDecomposition Ω 0) :
    (hessianFormData hΩ).RegularDecomposition 0 :=
  (hessianFormData hΩ).regularDecomposition_of_forall_exists fun _ hi _ hu =>
    hessianFormData_exists_add_eq hΩ h hi hu

/-- **The `L²` splittings of the div–div diagram** from the `H¹`-regular decompositions of `HΛ(Ω)`
from `n − 1` on: in the top degree `u = d p + w` with `w ∈ H¹` and `w = S (Sᵀ w)`
(`dxVecL2_dxVecAdj`); above it the spaces are zero ([ArnoldHu2021], §2, Theorem 3 and §4). -/
theorem divDivFormData_exists_add_eq
    (h : (deRham ℝ n).HasRegularDecomposition Ω ((n : ℤ) - 1)) {i : ℤ} (hi : (n : ℤ) - 1 ≤ i)
    {u : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n (i + 1)))}
    (hu : u ∈ ((vecRow n hΩ).d (i + 1) (i + 1 + 1)).domain) :
    ∃ (p : ((vecRow n hΩ).d i (i + 1)).domain) (φ : ((formRow n hΩ).d i (i + 1)).domain),
      (vecRow n hΩ).d i (i + 1) p + (divDivFormData hΩ).S i (i + 1) φ = u := by
  rcases lt_or_eq_of_le hi with hi' | rfl
  · -- above the top degree the spaces are zero
    have : IsEmpty (formIdx n (i + 1)) := ⟨fun s => by
      have h1 := s.2
      have h2 : #s.1 ≤ n := by simpa using Finset.card_le_univ s.1
      omega⟩
    have hu0 : u = 0 := PiLp.ext fun a => PiLp.ext fun s => isEmptyElim s
    refine ⟨0, 0, ?_⟩
    rw [hu0, LinearPMap.map_zero, ZeroMemClass.coe_zero, map_zero, add_zero]
  · obtain ⟨p, hp, hw⟩ := vecRow_exists_sub_mem_fieldH1 h le_rfl ((mem_vecRow_domain hΩ).1 hu)
    have hpm : p ∈ ((vecRow n hΩ).d ((n : ℤ) - 1) ((n : ℤ) - 1 + 1)).domain :=
      (mem_vecRow_domain hΩ).2 hp
    set w : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n ((n : ℤ) - 1 + 1))) :=
      u - (vecRow n hΩ).d ((n : ℤ) - 1) ((n : ℤ) - 1 + 1) ⟨p, hpm⟩
    have hwa : ∀ a, w a ∈ fieldH1 ℝ Ω (formIdx n ((n : ℤ) - 1 + 1)) := fun a => by
      simp only [w, PiLp.sub_apply, vecRow_d_apply]
      exact hw a
    have hφ : dxVecAdj ((n : ℤ) - 1) w ∈
        ((formRow n hΩ).d ((n : ℤ) - 1) ((n : ℤ) - 1 + 1)).domain := by
      exact (mem_formRow_domain hΩ).2
        (fieldH1_le_extDerivOp_maximal hΩ _ (dxVecAdj_mem_fieldH1 hΩ _ hwa))
    refine ⟨⟨p, hpm⟩, ⟨_, hφ⟩, ?_⟩
    rw [divDivFormData_S, dxVecL2_dxVecAdj (sub_add_cancel _ _)]
    simp only [w]
    abel

/-- **The regular decompositions of the div–div diagram** (`divDivFormData_exists_add_eq`). -/
theorem divDivFormData_regularDecomposition
    (h : (deRham ℝ n).HasRegularDecomposition Ω ((n : ℤ) - 1)) :
    (divDivFormData hΩ).RegularDecomposition ((n : ℤ) - 1) :=
  (divDivFormData hΩ).regularDecomposition_of_forall_exists fun _ hi _ hu =>
    divDivFormData_exists_add_eq hΩ h hi hu

/-! ### `S` is not onto between the `L²` domains

At `J = 0` (Hessian) and `J = n − 1` (div–div) the regular decompositions make `Sᴶ` onto modulo
`d`, but not onto: (23) of [ArnoldHu2021] fails between the domains. The rescalings of a test
field `φ` with `d (Sᴶ φ) = 0` make `‖d̃ᴶ φ‖ / ‖φ‖` unbounded
(`Feec.Domain.ConstCoeffOp.exists_lt_norm_toLp_testField_comp_aff`), which an onto `Sᴶ` forbids
(`Feec.BGG.HilbertData.exists_forall_S_ne`). -/

/-- **`d̃⁰` is unbounded on the gradients of the Hessian diagram**: on every nonempty open
`Ω ⊆ ℝⁿ`, `n ≥ 1`, for every `C` some vector `0`-form `φ ∈ D(d̃⁰)`, the rescaled gradient
`Sᵀ dχ` of a test function `χ`, has `S φ` closed and `C ‖φ‖ < ‖d̃⁰ φ‖`. -/
theorem hessianFormData_exists_lt_norm (hne : Ω.Nonempty) (hn : 0 < n) (C : ℝ) :
    ∃ φ : ((hessianFormData hΩ).Ht.d 0 (0 + 1)).domain,
      (hessianFormData hΩ).H.d (0 + 1) (0 + 1 + 1)
          ⟨_, (hessianFormData hΩ).S_mapsTo 0 (0 + 1) (0 + 1 + 1) φ⟩ = 0 ∧
        C * ‖(φ : PiLp 2 fun _ : Fin n => L2F ℝ Ω (formIdx n 0))‖ <
          ‖(hessianFormData hΩ).Ht.d 0 (0 + 1) φ‖ := by
  obtain ⟨χ, hχ, hχ0⟩ := exists_isTest_univ_ne_zero (Fin n → ℝ) ℝ
  set j₀ : Fin n := ⟨0, hn⟩
  set B₀ := extDerivOp ℝ n 0
  set χ' : formIdx n 0 → (Fin n → ℝ) → ℝ := fun _ => χ
  have hχ' : IsTestField Set.univ χ' := fun _ => hχ
  set Ψ := wsFieldsAdj 0 (B₀.apply χ')
  have hΨ : ∀ c, IsTestField Set.univ (Ψ c) := isTestField_wsFieldsAdj (B₀.isTestField_apply hχ')
  have hSΨ : wsFields 0 Ψ = B₀.apply χ' := by
    rw [wsFields_wsFieldsAdj]; simp
  have hBΨ : ∃ c, B₀.apply (Ψ c) ≠ 0 := by
    by_contra! h
    have hΨ0 : ∀ c r, Ψ c r = 0 := fun c r => by
      obtain rfl := formIdx_zero_eq r ⟨∅, by simp⟩
      by_contra hne0
      refine (hΨ c ⟨∅, by simp⟩).fderiv_apply_ne_zero hne0 (v := coordDir j₀) (by simp)
        (funext fun x => ?_)
      have := congrFun (congrFun (h c) ⟨{j₀}, by simp⟩) x
      rwa [extDerivOp_zero_apply] at this
    have hB0 : B₀.apply χ' = 0 := by
      rw [← hSΨ]
      funext t x
      simp [wsFields, hΨ0]
    refine hχ.fderiv_apply_ne_zero hχ0 (v := coordDir j₀) (by simp) (funext fun x => ?_)
    have := congrFun (congrFun hB0 ⟨{j₀}, by simp⟩) x
    rwa [extDerivOp_zero_apply] at this
  obtain ⟨a, b, hφ, hlt⟩ := ConstCoeffOp.exists_lt_norm_toLp_testField_comp_aff hΩ hne
    (isHomogeneous_extDerivOp 0) one_pos hΨ hBΨ C
  have hmem : ∀ c, testField (hφ c) ∈ ((extDerivOp ℝ n 0).maximal Ω).domain := fun c =>
    ((extDerivOp ℝ n 0).minimal_le_maximal hΩ).1
      ((extDerivOp ℝ n 0).testField_mem_minimal_domain hΩ (hφ c))
  have hφmem : (WithLp.toLp 2 fun c => testField (hφ c)) ∈
      ((hessianFormData hΩ).Ht.d 0 (0 + 1)).domain :=
    (mem_vecRow_domain hΩ).2 hmem
  refine ⟨⟨_, hφmem⟩, ?_, ?_⟩
  · have hG := isTestField_wsFields hφ
    have hGe : (wsFields 0 fun c r x => Ψ c r (aff a b x)) =
        fun t x => B₀.apply χ' t (aff a b x) := by
      rw [← hSΨ]; funext t x; simp [wsFields, Finset.sum_apply]
    have hB1 : (extDerivOp ℝ n (0 + 1)).apply (wsFields 0 fun c r x => Ψ c r (aff a b x)) = 0 := by
      rw [hGe, ConstCoeffOp.apply_comp_aff (isHomogeneous_extDerivOp _)
        (fun t => (B₀.isTestField_apply hχ' t).contDiff) a b,
        isComplexPair_extDerivOp 0 χ' (fun _ => hχ.contDiff)]
      funext j x; simp
    have hmin := (extDerivOp ℝ n (0 + 1)).testField_mem_minimal_domain hΩ hG
    have hmax := ((extDerivOp ℝ n (0 + 1)).minimal_le_maximal hΩ).1 hmin
    have e1 : (hessianFormData hΩ).S 0 (0 + 1) (WithLp.toLp 2 fun c => testField (hφ c)) =
        testField hG := by
      rw [hessianFormData_S, wsL2_testField]
    change (formRow n hΩ).d (0 + 1) (0 + 1 + 1) ⟨_, _⟩ = 0
    rw [LinearPMap.apply_eq_of_eq (formRow_d hΩ (0 + 1)) _ ⟨_, hmax⟩ e1,
      ← ((extDerivOp ℝ n (0 + 1)).minimal_le_maximal hΩ).2 (x := ⟨_, hmin⟩) rfl,
      (extDerivOp ℝ n (0 + 1)).minimal_testField hΩ hG, testField_congr _ IsTestField.zero hB1,
      testField_zero]
  · have e2 : (hessianFormData hΩ).Ht.d 0 (0 + 1) ⟨_, hφmem⟩ =
        WithLp.toLp 2 fun c => testField (B₀.isTestField_apply (hφ c)) := by
      refine PiLp.ext fun c => ?_
      change (vecRow n hΩ).d 0 (0 + 1) ⟨_, hφmem⟩ c = _
      have hmin := (extDerivOp ℝ n 0).testField_mem_minimal_domain hΩ (hφ c)
      rw [vecRow_d_apply]
      refine (LinearPMap.apply_eq_of_eq rfl _ ⟨_, hmem c⟩ rfl).trans ?_
      rw [← ((extDerivOp ℝ n 0).minimal_le_maximal hΩ).2 (x := ⟨_, hmin⟩) rfl,
        (extDerivOp ℝ n 0).minimal_testField hΩ (hφ c)]
    rw [e2]
    exact hlt

/-- **`S⁰` is not onto between the `L²` domains of the Hessian diagram** on every nonempty open
`Ω ⊆ ℝⁿ`, `n ≥ 1`: some `u ∈ HΛ¹(Ω)` is `S φ = Σₐ dxₐ ∧ φₐ` for no `φ ∈ HΛ⁰(Ω) ⊗ ℝⁿ` (for `n = 3`,
in vector proxies, `S⁰ = I` maps `H¹(Ω; ℝ³)` onto a proper subspace of `H(curl; Ω)`;
`Feec.Domain.hessianMaximalData_not_surjective`). -/
theorem hessianFormData_exists_forall_S_ne (hne : Ω.Nonempty) (hn : 0 < n) :
    ∃ u ∈ ((formRow n hΩ).d (0 + 1) (0 + 1 + 1)).domain,
      ∀ φ ∈ ((vecRow n hΩ).d 0 (0 + 1)).domain, wsL2 0 φ ≠ u := by
  have h := (hessianFormData hΩ).exists_forall_S_ne (i := 0) (j := 0 + 1) (k := 0 + 1 + 1)
    rfl rfl ((hessianFormData_antilipschitz hΩ 0 le_rfl).choose_spec.injective)
    (hessianFormData_exists_lt_norm hΩ hne hn)
  rw [hessianFormData_S] at h
  exact h

/-- **`d` is unbounded on the `(n - 1)`-forms of the div–div diagram**: on every nonempty open
`Ω ⊆ ℝⁿ`, `n ≥ 1`, for every `C` some `φ ∈ HΛⁿ⁻¹(Ω)`, a rescaled test form `χ dx_{{j}ᶜ}`, has
`C ‖φ‖ < ‖dφ‖`; `d (S φ) = 0` holds for every `φ` (no `(n + 1)`-forms). -/
theorem divDivFormData_exists_lt_norm (hne : Ω.Nonempty) (hn : 0 < n) (C : ℝ) :
    ∃ φ : ((divDivFormData hΩ).Ht.d ((n : ℤ) - 1) ((n : ℤ) - 1 + 1)).domain,
      (divDivFormData hΩ).H.d ((n : ℤ) - 1 + 1) ((n : ℤ) - 1 + 1 + 1)
          ⟨_, (divDivFormData hΩ).S_mapsTo _ _ ((n : ℤ) - 1 + 1 + 1) φ⟩ = 0 ∧
        C * ‖(φ : L2F ℝ Ω (formIdx n ((n : ℤ) - 1)))‖ <
          ‖(divDivFormData hΩ).Ht.d ((n : ℤ) - 1) ((n : ℤ) - 1 + 1) φ‖ := by
  obtain ⟨χ, hχ, hχ0⟩ := exists_isTest_univ_ne_zero (Fin n → ℝ) ℝ
  set j₀ : Fin n := ⟨0, hn⟩
  have hc : ((Finset.univ.erase j₀).card : ℤ) = (n : ℤ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  set r₀ : formIdx n ((n : ℤ) - 1) := ⟨Finset.univ.erase j₀, hc⟩
  set ψ : formIdx n ((n : ℤ) - 1) → (Fin n → ℝ) → ℝ := fun r => if r = r₀ then χ else 0
  have hψ : IsTestField Set.univ ψ := fun r => by
    by_cases h : r = r₀
    · simp only [ψ, h, ite_true]; exact hχ
    · simp only [ψ, h, ite_false]; exact IsTest.zero
  set B := extDerivOp ℝ n ((n : ℤ) - 1)
  have hBψ : B.apply ψ ≠ 0 := by
    intro h
    have ht : ((Finset.univ : Finset (Fin n)).card : ℤ) = (n : ℤ) - 1 + 1 := by simp
    refine hχ.fderiv_apply_ne_zero hχ0 (v := coordDir j₀) (by simp) (funext fun x => ?_)
    have h0 := congrFun (congrFun h ⟨Finset.univ, ht⟩) x
    rw [extDerivOp_apply] at h0
    simp only [extD] at h0
    rw [Finset.sum_eq_single j₀ (fun j _ hj => ?_) (by simp)] at h0
    · rw [formExt_of_card ψ hc] at h0
      simp only [ψ, show (⟨Finset.univ.erase j₀, hc⟩ : formIdx n ((n : ℤ) - 1)) = r₀ from rfl,
        ↓reduceIte] at h0
      have hs : (ExteriorFibre.sgn j₀ (Finset.univ : Finset (Fin n)) : ℝ) ≠ 0 := by
        intro h1
        have := ExteriorFibre.sgn_mul_self (R := ℝ) j₀ (Finset.univ : Finset (Fin n))
        rw [h1, zero_mul] at this
        exact zero_ne_one this
      simpa using (mul_eq_zero.1 h0).resolve_left hs
    · have hne' : (⟨Finset.univ.erase j, by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
          omega⟩ : formIdx n ((n : ℤ) - 1)) ≠ r₀ := fun he => by
        have := congrArg (fun r : formIdx n ((n : ℤ) - 1) => j₀ ∈ r.1) he
        simp [r₀, hj.symm] at this
      rw [formExt_of_card ψ (by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
          omega)]
      simp only [ψ, hne', ite_false]
      simp
  obtain ⟨a, b, hφ, hlt⟩ := ConstCoeffOp.exists_lt_norm_testField_comp_aff hΩ hne
    (isHomogeneous_extDerivOp _) one_pos hψ hBψ C
  have hmin := B.testField_mem_minimal_domain hΩ hφ
  have hmax := (B.minimal_le_maximal hΩ).1 hmin
  have hφmem : testField hφ ∈ ((divDivFormData hΩ).Ht.d ((n : ℤ) - 1) ((n : ℤ) - 1 + 1)).domain :=
    (mem_formRow_domain hΩ).2 hmax
  have hE : IsEmpty (formIdx n ((n : ℤ) - 1 + 1 + 1)) := ⟨fun s => by
    have h1 := s.2
    have h2 := Finset.card_le_univ s.1
    rw [Fintype.card_fin] at h2
    omega⟩
  have hsub : Subsingleton (PiLp 2 fun _ : Fin n => L2F ℝ Ω (formIdx n ((n : ℤ) - 1 + 1 + 1))) :=
    ⟨fun x y => PiLp.ext fun c => PiLp.ext fun t => isEmptyElim t⟩
  refine ⟨⟨_, hφmem⟩, Subsingleton.elim _ _, ?_⟩
  change C * ‖testField hφ‖ < ‖(formRow n hΩ).d ((n : ℤ) - 1) ((n : ℤ) - 1 + 1) ⟨_, hφmem⟩‖
  rw [LinearPMap.apply_eq_of_eq (formRow_d hΩ _) _ ⟨_, hmax⟩ rfl,
    ← (B.minimal_le_maximal hΩ).2 (x := ⟨_, hmin⟩) rfl, B.minimal_testField hΩ hφ]
  exact hlt

/-- **`Sⁿ⁻¹` is not onto between the `L²` domains of the div–div diagram** on every nonempty
open `Ω ⊆ ℝⁿ`, `n ≥ 1`: some `u ∈ L²(Ω; Λⁿ ⊗ ℝⁿ)` is `S φ = (dxₐ ∧ φ)ₐ` for no
`φ ∈ HΛⁿ⁻¹(Ω)` (for `n = 3`, in vector proxies, `S² = I` maps `H(div; Ω)` onto a proper subspace
of `L²(Ω; ℝ³)`; `Feec.Domain.divDivMaximalData_not_surjective`). -/
theorem divDivFormData_exists_forall_S_ne (hne : Ω.Nonempty) (hn : 0 < n) :
    ∃ u ∈ ((vecRow n hΩ).d ((n : ℤ) - 1 + 1) ((n : ℤ) - 1 + 1 + 1)).domain,
      ∀ φ ∈ ((formRow n hΩ).d ((n : ℤ) - 1) ((n : ℤ) - 1 + 1)).domain, dxVecL2 _ φ ≠ u := by
  have h := (divDivFormData hΩ).exists_forall_S_ne (i := (n : ℤ) - 1)
    (j := (n : ℤ) - 1 + 1) (k := (n : ℤ) - 1 + 1 + 1) rfl rfl
    ((divDivFormData_antilipschitz hΩ _ le_rfl).choose_spec.injective)
    (divDivFormData_exists_lt_norm hΩ hne hn)
  rw [divDivFormData_S] at h
  exact h

end Feec.FiniteElement
