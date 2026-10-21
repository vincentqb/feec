module

public import Feec.Domain.Operators
public import Feec.Algebra.ExteriorFibre

/-!
# The `L²` de Rham complex of `k`-forms on an open set `Ω ⊆ ℝⁿ`

Coordinates on `ℝⁿ = Fin n → ℝ` as in `Feec.Domain.Operators`. A `k`-form is a field indexed
by the `k`-subsets of `Fin n` (`Feec.Domain.formIdx n k`, empty unless `0 ≤ k ≤ n`), the
coefficients of `dx_{s₁} ∧ ⋯ ∧ dx_{s_k}`, `s₁ < ⋯ < s_k`. With the sign
`ε(j, s) = (-1)^{#{l ∈ s | l < j}}` of `Feec.ExteriorFibre.sgn`:

* the **exterior derivative** `Feec.Domain.extDerivOp n k`, a first-order constant-coefficient
  operator, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}` (`extDerivOp_apply`);
* its **formal adjoint** is minus the codifferential,
  `(dᵗψ)_s = -Σ_{j ∉ s} ε(j, s) ∂_j ψ_{s ∪ j}` (`formalAdj_extDerivOp_apply`);
* `d ∘ d = 0` and `dᵗ ∘ dᵗ = 0` on smooth forms (Schwarz; `isComplexPair_extDerivOp`,
  `isComplexPair_formalAdj_extDerivOp`);
* the complex `Feec.Domain.deRham n` of constant-coefficient operators indexed by `ℤ`, whose
  minimal realization on any open `Ω` is `H̊Λ⁰(Ω) → H̊Λ¹(Ω) → ⋯` (the closure of `d` on
  `C_c^∞(Ω)`; for Lipschitz `Ω` these are the forms with vanishing tangential trace), whose maximal realization is `HΛ⁰(Ω) → HΛ¹(Ω) → ⋯` (no boundary
  condition), and each is the dual of the other through the codifferentials
  (`deRham_dual_minimalComplex_d`, `deRham_dual_maximalComplex_d`).
* the components in low degree: `(d f)_{j} = ∂_j f` (`extDerivOp_zero_apply`),
  `(d w)_{jl} = ∂_j w_l - ∂_l w_j` for `j < l` (`extDerivOp_one_apply_pair`) and
  `(d w)_{ijl} = ∂_i w_{jl} - ∂_j w_{il} + ∂_l w_{ij}` for `i < j < l`
  (`extDerivOp_two_apply_triple`).

## Implementation notes

In `ℝ³`, with the vector proxies of `Feec.Algebra.Proxy3` (`v = (w_0, w_1, w_2)` for a 1-form,
`v = (w_{12}, -w_{02}, w_{01})` for a 2-form), the last three lemmas say that `d` is grad, curl
and div componentwise. The identification of `deRham 3` with
`Feec.Models.BoundedDomain.deRham3` as complexes cannot be stated here (`Feec.Models` is a higher
layer); it follows from these component formulas.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (the de Rham complex, `HΛᵏ` and `H̊Λᵏ`)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4 (the `L²` de Rham complex and its dual)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff ComplexConjugate
open MeasureTheory Set Finset

@[expose] public noncomputable section

namespace Feec.Domain

open ConstCoeffOp ExteriorFibre

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The index type of `k`-forms on `ℝⁿ`: the `k`-subsets of `Fin n` (empty unless `0 ≤ k ≤ n`). -/
abbrev formIdx (n : ℕ) (k : ℤ) : Type := {s : Finset (Fin n) // (#s : ℤ) = k}

/-- A `k`-form extended by zero to a family indexed by all subsets of `Fin n`. -/
def formExt {k : ℤ} {F : Type*} [Zero F] (w : formIdx n k → F) (s : Finset (Fin n)) : F :=
  if h : (#s : ℤ) = k then w ⟨s, h⟩ else 0

theorem formExt_val {k : ℤ} {F : Type*} [Zero F] (w : formIdx n k → F) (s : formIdx n k) :
    formExt w s.1 = w s := by
  simp [formExt, s.2]

theorem formExt_of_card {k : ℤ} {F : Type*} [Zero F] (w : formIdx n k → F) {s : Finset (Fin n)}
    (h : (#s : ℤ) = k) : formExt w s = w ⟨s, h⟩ := by
  simp [formExt, h]

theorem contDiff_formExt {k : ℤ} {w : formIdx n k → (Fin n → ℝ) → 𝕜}
    (hw : ∀ s, ContDiff ℝ ∞ (w s)) (s : Finset (Fin n)) : ContDiff ℝ ∞ (formExt w s) := by
  unfold formExt
  split_ifs
  · exact hw _
  · exact contDiff_const

/-! ## The exterior derivative on families indexed by all subsets -/

/-- `(dF)_s = Σ_{j ∈ s} ε(j, s) ∂_j F_{s ∖ j}` for a family `F` indexed by all subsets. -/
def extD (F : Finset (Fin n) → (Fin n → ℝ) → 𝕜) (s : Finset (Fin n)) (x : Fin n → ℝ) : 𝕜 :=
  ∑ j ∈ s, sgn j s * fderiv ℝ (F (s.erase j)) x (coordDir j)

/-- `(δF)_s = -Σ_{j ∉ s} ε(j, s) ∂_j F_{s ∪ j}`: minus the codifferential, the formal adjoint of
`extD`. -/
def extDAdj (F : Finset (Fin n) → (Fin n → ℝ) → 𝕜) (s : Finset (Fin n)) (x : Fin n → ℝ) : 𝕜 :=
  -∑ j ∈ sᶜ, sgn j s * fderiv ℝ (F (insert j s)) x (coordDir j)

theorem contDiff_extD {F : Finset (Fin n) → (Fin n → ℝ) → 𝕜} (hF : ∀ s, ContDiff ℝ ∞ (F s))
    (s : Finset (Fin n)) : ContDiff ℝ ∞ (extD F s) :=
  ContDiff.sum fun _ _ => contDiff_const.mul (contDiff_fderiv_apply (hF _) _)

theorem contDiff_extDAdj {F : Finset (Fin n) → (Fin n → ℝ) → 𝕜} (hF : ∀ s, ContDiff ℝ ∞ (F s))
    (s : Finset (Fin n)) : ContDiff ℝ ∞ (extDAdj F s) :=
  (ContDiff.sum fun _ _ => contDiff_const.mul (contDiff_fderiv_apply (hF _) _)).neg

/-- `∂_v (Σ_j c_j G_j) = Σ_j c_j ∂_v G_j` for smooth `G_j`. -/
theorem fderiv_sum_const_mul {α : Type*} (t : Finset α) (c : α → 𝕜)
    {G : α → (Fin n → ℝ) → 𝕜} (hG : ∀ a, ContDiff ℝ ∞ (G a)) (x v : Fin n → ℝ) :
    fderiv ℝ (fun y => ∑ a ∈ t, c a * G a y) x v = ∑ a ∈ t, c a * fderiv ℝ (G a) x v := by
  have hd : ∀ a, DifferentiableAt ℝ (G a) x := fun a => (hG a).differentiable (by simp) x
  rw [fderiv_fun_sum fun a _ => (hd a).const_mul (c a)]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fderiv_const_mul (hd a)]
  simp

/-- **`d ∘ d = 0`** on smooth families (Schwarz). -/
theorem extD_extD {F : Finset (Fin n) → (Fin n → ℝ) → 𝕜} (hF : ∀ s, ContDiff ℝ ∞ (F s))
    (s : Finset (Fin n)) (x : Fin n → ℝ) : extD (extD F) s x = 0 := by
  have e : ∀ j, fderiv ℝ (extD F (s.erase j)) x (coordDir j) =
      ∑ l ∈ s.erase j, sgn l (s.erase j) * fderiv ℝ (fun y => fderiv ℝ (F ((s.erase j).erase l)) y
        (coordDir l)) x (coordDir j) := fun j =>
    fderiv_sum_const_mul _ _ (fun l => contDiff_fderiv_apply (hF _) _) x _
  simp only [extD] at e ⊢
  simp only [e, Finset.mul_sum]
  refine sum_sum_erase_eq_zero s _ fun j hj l hl hjl => ?_
  rw [sgn_erase hj, sgn_erase hl, erase_right_comm,
    fderiv_fderiv_comm ((hF ((s.erase j).erase l)).of_le (by simp)) (coordDir l) (coordDir j) x]
  have := ite_lt_add_ite_lt (R := 𝕜) hjl
  linear_combination (sgn j s * sgn l s * fderiv ℝ (fun y => fderiv ℝ (F ((s.erase j).erase l))
    y (coordDir j)) x (coordDir l)) * this

/-- **`δ ∘ δ = 0`** on smooth families (Schwarz). -/
theorem extDAdj_extDAdj {F : Finset (Fin n) → (Fin n → ℝ) → 𝕜} (hF : ∀ s, ContDiff ℝ ∞ (F s))
    (s : Finset (Fin n)) (x : Fin n → ℝ) : extDAdj (extDAdj F) s x = 0 := by
  have hd : ∀ j, fderiv ℝ (extDAdj F (insert j s)) x (coordDir j) =
      -∑ l ∈ sᶜ.erase j, sgn l (insert j s) * fderiv ℝ (fun y => fderiv ℝ
        (F (insert l (insert j s))) y (coordDir l)) x (coordDir j) := by
    intro j
    have h1 := fderiv_sum_const_mul ((insert j s)ᶜ) (fun l => sgn l (insert j s))
      (G := fun l y => fderiv ℝ (F (insert l (insert j s))) y (coordDir l))
      (fun l => contDiff_fderiv_apply (hF _) _) x (coordDir j)
    change fderiv ℝ (fun y => -∑ l ∈ (insert j s)ᶜ, sgn l (insert j s) *
        fderiv ℝ (F (insert l (insert j s))) y (coordDir l)) x (coordDir j) = _
    rw [fderiv_fun_neg, neg_apply, h1, compl_insert]
  simp only [extDAdj]
  simp only [hd, mul_neg, Finset.sum_neg_distrib, neg_neg, Finset.mul_sum]
  refine sum_sum_erase_eq_zero sᶜ _ fun j hj l hl hjl => ?_
  have hj' : j ∉ s := Finset.mem_compl.1 hj
  have hl' : l ∉ s := Finset.mem_compl.1 hl
  rw [sgn_insert hj', sgn_insert hl', Finset.insert_comm l j,
    fderiv_fderiv_comm ((hF (insert j (insert l s))).of_le (by simp)) (coordDir j) (coordDir l) x]
  have := ite_lt_add_ite_lt (R := 𝕜) hjl
  linear_combination (sgn j s * sgn l s * fderiv ℝ (fun y => fderiv ℝ (F (insert j (insert l s)))
    y (coordDir l)) x (coordDir j)) * this

/-! ## The exterior derivative as a constant-coefficient operator -/

variable (𝕜 n) in
/-- The **exterior derivative** `d : Λᵏ → Λᵏ⁺¹` on `ℝⁿ` as a first-order constant-coefficient
operator: `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`. -/
def extDerivOp (k : ℤ) : ConstCoeffOp (Fin n → ℝ) 𝕜 (formIdx n k) (formIdx n (k + 1)) where
  coeff t r := ({j ∈ t.1 | t.1.erase j = r.1}).toList.map fun j => ([coordDir j], sgn j t.1)

theorem card_erase_of_formIdx {k : ℤ} (t : formIdx n (k + 1)) {j : Fin n} (hj : j ∈ t.1) :
    (#(t.1.erase j) : ℤ) = k := by
  have h1 := Finset.card_erase_add_one hj
  have h2 := t.2
  omega

theorem card_insert_of_formIdx {k : ℤ} (r : formIdx n k) {j : Fin n} (hj : j ∉ r.1) :
    (#(insert j r.1) : ℤ) = k + 1 := by
  rw [Finset.card_insert_of_notMem hj]
  push_cast
  rw [r.2]

theorem applyEntry_extDerivOp_coeff {k : ℤ} (t : formIdx n (k + 1)) (r : formIdx n k)
    (f : (Fin n → ℝ) → 𝕜) (x : Fin n → ℝ) :
    applyEntry ((extDerivOp 𝕜 n k).coeff t r) f x =
      ∑ j ∈ t.1 with t.1.erase j = r.1, sgn j t.1 * fderiv ℝ f x (coordDir j) := by
  simp only [applyEntry, extDerivOp, List.map_map]
  rw [← Finset.sum_map_toList]
  rfl

/-- **The exterior derivative in coordinates**: `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`, for any
field `w` (no smoothness needed: `∂_j` is `fderiv`). -/
theorem extDerivOp_apply {k : ℤ} (w : formIdx n k → (Fin n → ℝ) → 𝕜) (t : formIdx n (k + 1))
    (x : Fin n → ℝ) :
    (extDerivOp 𝕜 n k).apply w t x = extD (formExt w) t.1 x := by
  simp only [ConstCoeffOp.apply, applyEntry_extDerivOp_coeff, Finset.sum_filter, extD]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  set r₀ : formIdx n k := ⟨t.1.erase j, card_erase_of_formIdx t hj⟩
  have e : ∀ r : formIdx n k, (t.1.erase j = r.1) ↔ r = r₀ := fun r => by
    rw [Subtype.ext_iff]; exact eq_comm
  simp only [e, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [formExt_of_card w (card_erase_of_formIdx t hj)]

/-- **The formal adjoint of `d` is minus the codifferential**:
`(dᵗψ)_s = -Σ_{j ∉ s} ε(j, s) ∂_j ψ_{s ∪ j}`. -/
theorem formalAdj_extDerivOp_apply {k : ℤ} (ψ : formIdx n (k + 1) → (Fin n → ℝ) → 𝕜)
    (r : formIdx n k) (x : Fin n → ℝ) :
    (extDerivOp 𝕜 n k).formalAdj.apply ψ r x = extDAdj (formExt ψ) r.1 x := by
  have hc : ∀ t : formIdx n (k + 1), applyEntry ((extDerivOp 𝕜 n k).formalAdj.coeff r t) (ψ t) x =
      ∑ j ∈ t.1 with t.1.erase j = r.1, -(sgn j t.1 * fderiv ℝ (ψ t) x (coordDir j)) := by
    intro t
    simp only [ConstCoeffOp.formalAdj, adjEntry, extDerivOp, applyEntry, List.map_map]
    rw [← Finset.sum_map_toList]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp [sgn, iterDeriv_singleton]
  simp only [ConstCoeffOp.apply, hc, Finset.sum_filter, extDAdj]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.univ.filter fun t : formIdx n (k + 1) => j ∈ t.1)
    (by intro t j; simp)]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_compl_add_sum r.1]
  rw [show (∑ j ∈ r.1, ∑ t ∈ Finset.univ.filter fun t : formIdx n (k + 1) => j ∈ t.1,
      (if t.1.erase j = r.1 then -(sgn j t.1 * fderiv ℝ (ψ t) x (coordDir j)) else 0)) = 0 from
    Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun t _ => ite_eq_right_iff.2 fun h => by
      have : j ∈ t.1.erase j := h ▸ hj
      simp at this, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ∉ r.1 := Finset.mem_compl.1 hj
  set t₀ : formIdx n (k + 1) := ⟨insert j r.1, card_insert_of_formIdx r hj'⟩
  have e : ∀ t : formIdx n (k + 1), (j ∈ t.1 ∧ t.1.erase j = r.1) ↔ t = t₀ := by
    intro t
    rw [Subtype.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      change t.1 = insert j r.1
      rw [← h2, Finset.insert_erase h1]
    · intro h
      rw [h]
      exact ⟨Finset.mem_insert_self _ _, Finset.erase_insert hj'⟩
  rw [Finset.sum_filter]
  simp only [← ite_and, e, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [formExt_of_card ψ (card_insert_of_formIdx r hj'), sgn_insert_self]

theorem extDerivOp_isOrderLE (k : ℤ) : (extDerivOp 𝕜 n k).IsOrderLE 1 := by
  intro t r p hp
  simp only [extDerivOp, List.mem_map] at hp
  obtain ⟨j, -, rfl⟩ := hp
  simp

theorem formalAdj_extDerivOp_isOrderLE (k : ℤ) : (extDerivOp 𝕜 n k).formalAdj.IsOrderLE 1 :=
  (extDerivOp_isOrderLE k).formalAdj

/-- `d ω` extended by zero is `extD` of the extension of `ω`, in degree `k + 1`. -/
theorem formExt_extDerivOp_apply {k : ℤ} (w : formIdx n k → (Fin n → ℝ) → 𝕜)
    {s : Finset (Fin n)} (hs : (#s : ℤ) = k + 1) :
    formExt ((extDerivOp 𝕜 n k).apply w) s = extD (formExt w) s := by
  rw [formExt_of_card _ hs]
  funext x
  exact extDerivOp_apply w ⟨s, hs⟩ x

/-- `dᵗ ψ` extended by zero is `extDAdj` of the extension of `ψ`, in degree `k`. -/
theorem formExt_formalAdj_extDerivOp_apply {k : ℤ} (w : formIdx n (k + 1) → (Fin n → ℝ) → 𝕜)
    {s : Finset (Fin n)} (hs : (#s : ℤ) = k) :
    formExt ((extDerivOp 𝕜 n k).formalAdj.apply w) s = extDAdj (formExt w) s := by
  rw [formExt_of_card _ hs]
  funext x
  exact formalAdj_extDerivOp_apply w ⟨s, hs⟩ x

/-- **`d ∘ d = 0`** on smooth `k`-forms. -/
theorem isComplexPair_extDerivOp (k : ℤ) :
    (extDerivOp 𝕜 n k).IsComplexPair (extDerivOp 𝕜 n (k + 1)) := by
  intro w hw
  funext u x
  rw [extDerivOp_apply, Pi.zero_apply, Pi.zero_apply]
  have e : ∀ j ∈ u.1, formExt ((extDerivOp 𝕜 n k).apply w) (u.1.erase j) =
      extD (formExt w) (u.1.erase j) := fun j hj =>
    formExt_extDerivOp_apply w (card_erase_of_formIdx u hj)
  have : extD (formExt ((extDerivOp 𝕜 n k).apply w)) u.1 x = extD (extD (formExt w)) u.1 x := by
    simp only [extD]
    exact Finset.sum_congr rfl fun j hj => by rw [e j hj]
  rw [this, extD_extD (contDiff_formExt hw)]

/-- **`dᵗ ∘ dᵗ = 0`**: the codifferentials form a complex. -/
theorem isComplexPair_formalAdj_extDerivOp (k : ℤ) :
    (extDerivOp 𝕜 n (k + 1)).formalAdj.IsComplexPair (extDerivOp 𝕜 n k).formalAdj := by
  intro w hw
  funext r x
  rw [formalAdj_extDerivOp_apply, Pi.zero_apply, Pi.zero_apply]
  have e : ∀ j ∈ r.1ᶜ, formExt ((extDerivOp 𝕜 n (k + 1)).formalAdj.apply w) (insert j r.1) =
      extDAdj (formExt w) (insert j r.1) := fun j hj =>
    formExt_formalAdj_extDerivOp_apply w (card_insert_of_formIdx r (Finset.mem_compl.1 hj))
  have : extDAdj (formExt ((extDerivOp 𝕜 n (k + 1)).formalAdj.apply w)) r.1 x =
      extDAdj (extDAdj (formExt w)) r.1 x := by
    simp only [extDAdj]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun j hj => by rw [e j hj])
  rw [this, extDAdj_extDAdj (contDiff_formExt hw)]

/-- **In degree `0`, `d` is the gradient**: `(d f)_{{j}} = ∂_j f`. -/
theorem extDerivOp_zero_apply (f : formIdx n 0 → (Fin n → ℝ) → 𝕜) (j : Fin n)
    (x : Fin n → ℝ) :
    (extDerivOp 𝕜 n 0).apply f ⟨{j}, by simp⟩ x =
      fderiv ℝ (f ⟨∅, by simp⟩) x (coordDir j) := by
  rw [extDerivOp_apply]
  simp only [extD, Finset.sum_singleton, Finset.erase_singleton]
  rw [formExt_of_card f (by simp)]
  have : ({l ∈ ({j} : Finset (Fin n)) | l < j}) = ∅ := by
    ext l; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨rfl, h⟩; exact lt_irrefl _ h
  simp [sgn, this]

/-- **`d` on 1-forms**: `(d w)_{jl} = ∂_j w_l - ∂_l w_j` for `j < l` (in `ℝ³`, the curl of the
proxy `(w_0, w_1, w_2)`). -/
theorem extDerivOp_one_apply_pair (w : formIdx n 1 → (Fin n → ℝ) → 𝕜) {j l : Fin n}
    (hjl : j < l) (x : Fin n → ℝ) :
    (extDerivOp 𝕜 n 1).apply w ⟨{j, l}, by rw [card_pair hjl.ne]; norm_num⟩ x =
      fderiv ℝ (w ⟨{l}, by simp⟩) x (coordDir j) - fderiv ℝ (w ⟨{j}, by simp⟩) x (coordDir l) := by
  rw [extDerivOp_apply]
  have hj : j ∉ ({l} : Finset (Fin n)) := by simpa using hjl.ne
  simp only [extD, sum_insert hj, sum_singleton, erase_insert hj,
    erase_insert_of_ne hjl.ne, erase_singleton, Finset.insert_empty]
  rw [formExt_of_card w (by simp), formExt_of_card w (by simp)]
  have h1 : ({m ∈ ({j, l} : Finset (Fin n)) | m < j}) = ∅ := by
    ext m; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨rfl | rfl, h⟩ <;> order
  have h2 : ({m ∈ ({j, l} : Finset (Fin n)) | m < l}) = {j} := by
    ext m; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · rfl
      · exact absurd h (lt_irrefl _)
    · rintro rfl; exact ⟨Or.inl rfl, hjl⟩
  simp [sgn, h1, h2]
  ring

/-- **`d` on 2-forms**: `(d w)_{ijl} = ∂_i w_{jl} - ∂_j w_{il} + ∂_l w_{ij}` for `i < j < l` (in
`ℝ³`, the divergence of the proxy `(w_{12}, -w_{02}, w_{01})`). -/
theorem extDerivOp_two_apply_triple (w : formIdx n 2 → (Fin n → ℝ) → 𝕜) {i j l : Fin n}
    (hij : i < j) (hjl : j < l) (x : Fin n → ℝ) :
    (extDerivOp 𝕜 n 2).apply w ⟨{i, j, l}, by
        rw [card_insert_of_notMem (by simp [hij.ne, (hij.trans hjl).ne]), card_pair hjl.ne]
        norm_num⟩ x =
      fderiv ℝ (w ⟨{j, l}, by rw [card_pair hjl.ne]; norm_num⟩) x (coordDir i) -
        fderiv ℝ (w ⟨{i, l}, by rw [card_pair (hij.trans hjl).ne]; norm_num⟩) x (coordDir j) +
        fderiv ℝ (w ⟨{i, j}, by rw [card_pair hij.ne]; norm_num⟩) x (coordDir l) := by
  rw [extDerivOp_apply]
  have hil := hij.trans hjl
  have hi : i ∉ ({j, l} : Finset (Fin n)) := by simp [hij.ne, hil.ne]
  have hj : j ∉ ({l} : Finset (Fin n)) := by simpa using hjl.ne
  simp only [extD, sum_insert hi, sum_insert hj, sum_singleton, erase_insert hi,
    erase_insert_of_ne hij.ne, erase_insert_of_ne hil.ne, erase_insert hj,
    erase_insert_of_ne hjl.ne, erase_singleton, Finset.insert_empty]
  rw [formExt_of_card w (by rw [card_pair hjl.ne]; norm_num),
    formExt_of_card w (by rw [card_pair hil.ne]; norm_num),
    formExt_of_card w (by rw [card_pair hij.ne]; norm_num)]
  have h1 : ({m ∈ ({i, j, l} : Finset (Fin n)) | m < i}) = ∅ := by
    ext m; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨rfl | rfl | rfl, h⟩ <;> order
  have h2 : ({m ∈ ({i, j, l} : Finset (Fin n)) | m < j}) = {i} := by
    ext m; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, h⟩ <;> first | rfl | order
    · rintro rfl; exact ⟨Or.inl rfl, hij⟩
  have h3 : ({m ∈ ({i, j, l} : Finset (Fin n)) | m < l}) = {i, j} := by
    ext m; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, h⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · order
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, hil⟩
      · exact ⟨Or.inr (Or.inl rfl), hjl⟩
  simp [sgn, h1, h2, h3, card_pair hij.ne]
  ring

/-! ## The de Rham complex and its two boundary-condition families -/

variable (𝕜 n) in
/-- **The de Rham complex of `ℝⁿ`** as a complex of constant-coefficient operators indexed by
`ℤ`: `k`-forms in degree `k` (no components outside `0 ≤ k ≤ n`), `d = extDerivOp`. -/
def deRham : ConstCoeffComplex (Fin n → ℝ) 𝕜 where
  ι := formIdx n
  A := extDerivOp 𝕜 n
  comp := isComplexPair_extDerivOp

@[simp] theorem deRham_ι (k : ℤ) : (deRham 𝕜 n).ι k = formIdx n k := rfl

@[simp] theorem deRham_A (k : ℤ) : (deRham 𝕜 n).A k = extDerivOp 𝕜 n k := rfl

variable {Ω : Set (Fin n → ℝ)}

/-- The minimal complex `H̊Λ⁰(Ω) → H̊Λ¹(Ω) → ⋯`: the closure of `d` on `C_c^∞(Ω)` (for Lipschitz
`Ω`, `d` with vanishing tangential trace). -/
theorem deRham_minimalComplex_d (hΩ : IsOpen Ω) (k : ℤ) :
    ((deRham 𝕜 n).minimalComplex hΩ).d k (k + 1) = (extDerivOp 𝕜 n k).minimal Ω :=
  (deRham 𝕜 n).minimalComplex_d hΩ k

/-- The maximal complex `HΛ⁰(Ω) → HΛ¹(Ω) → ⋯`: the weak `d`, no boundary condition. -/
theorem deRham_maximalComplex_d (hΩ : IsOpen Ω) (k : ℤ) :
    ((deRham 𝕜 n).maximalComplex hΩ).d k (k + 1) = (extDerivOp 𝕜 n k).maximal Ω :=
  (deRham 𝕜 n).maximalComplex_d hΩ k

/-- **Duality**: the dual of `H̊Λ` is the maximal codifferential complex, `(d_min)† = (dᵗ)_max`
with `dᵗ = -δ` (`formalAdj_extDerivOp_apply`). -/
theorem deRham_dual_minimalComplex_d (hΩ : IsOpen Ω) (k : ℤ) :
    ((deRham 𝕜 n).minimalComplex hΩ).dual.d (k + 1) k = (extDerivOp 𝕜 n k).formalAdj.maximal Ω :=
  (deRham 𝕜 n).dual_minimalComplex_d hΩ k

/-- **Duality**: the dual of `HΛ` is the minimal codifferential complex, `(d_max)† = (dᵗ)_min`. -/
theorem deRham_dual_maximalComplex_d (hΩ : IsOpen Ω) (k : ℤ) :
    ((deRham 𝕜 n).maximalComplex hΩ).dual.d (k + 1) k = (extDerivOp 𝕜 n k).formalAdj.minimal Ω :=
  (deRham 𝕜 n).dual_maximalComplex_d hΩ k

/-- `H̊Λᵏ(Ω) ⊆ HΛᵏ(Ω)`: `d_min ≤ d_max`. -/
theorem extDerivOp_minimal_le_maximal (hΩ : IsOpen Ω) (k : ℤ) :
    (extDerivOp 𝕜 n k).minimal Ω ≤ (extDerivOp 𝕜 n k).maximal Ω :=
  (extDerivOp 𝕜 n k).minimal_le_maximal hΩ

/-- Smooth forms with `ω, dω ∈ L²(Ω)` lie in `HΛᵏ(Ω)`, where the weak `d` is the classical
one, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}` (`extDerivOp_apply`). -/
theorem extDerivOp_smooth_mem_maximal_domain (hΩ : IsOpen Ω) {k : ℤ}
    {w : formIdx n k → (Fin n → ℝ) → 𝕜} (hws : ∀ s, ContDiff ℝ 1 (w s))
    (hw : ∀ s, MemLp (w s) 2 (volume.restrict Ω))
    (hdw : ∀ t, MemLp ((extDerivOp 𝕜 n k).apply w t) 2 (volume.restrict Ω)) :
    ∃ h : toL2F hw ∈ ((extDerivOp 𝕜 n k).maximal Ω).domain,
      (extDerivOp 𝕜 n k).maximal Ω ⟨_, h⟩ = toL2F hdw :=
  (extDerivOp 𝕜 n k).smooth_mem_maximal_domain hΩ (extDerivOp_isOrderLE k) hws hw hdw

/-- On test forms, `d_min` is the classical exterior derivative. -/
theorem extDerivOp_minimal_testField (hΩ : IsOpen Ω) {k : ℤ}
    {w : formIdx n k → (Fin n → ℝ) → 𝕜} (hw : IsTestField Ω w) :
    (extDerivOp 𝕜 n k).minimal Ω ⟨testField hw, (extDerivOp 𝕜 n k).testField_mem_minimal_domain hΩ hw⟩ =
      testField ((extDerivOp 𝕜 n k).isTestField_apply hw) :=
  (extDerivOp 𝕜 n k).minimal_testField hΩ hw

end Feec.Domain
