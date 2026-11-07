module

public import Feec.Domain.H1Restriction
public import Feec.Models.Cube.WeakSymmetrySobolevRate

/-!
# Restrictions of `H¹(ℝ³)` with vanishing tangential traces lie in the relative class `H¹_univ`

A form `x` on the cube `Q = (0, ½)³` with `H¹(ℝ³)` data (`Feec.Domain.H1Data`) lies in the domain
of `d_min†` (`Feec.Domain.H1Data.mem_adjoint`); if it also lies in the domain of `d_min` (vanishing
tangential traces), Gaffney's identity on the cube (`sobRel_zero_of_mem`, `sobRel_one_of_mem`,
`sobRel_two_of_mem`) puts it in the relative parity class `H¹_univ` of `SobRel` with norm `O(B)`
(`sobRel_of_h1_zero`, `sobRel_of_h1_one`, `sobRel_of_h1_two`). For the connecting maps of the
complex with weak symmetry, `S v = Σₐ dxₐ ∧ vₐ` lies in the domain of `d_min†` when the `vₐ` have
`H¹(ℝⁿ)` data (`mem_adjoint_wsL2_of_h1Data`), so `S⁰φ` (closed, in `D(d_min)`) and `S¹u` (`uₐ` in
`D(d_min)`) lie in `H¹_univ` (`sobRel_wsL2_zero`, `sobRel_wsL2_one`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4.3 (Gaffney's inequality)
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open MeasureTheory Set

@[expose] public noncomputable section

namespace Feec.Models.Cube.WeakSymmetry

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM

variable {n : ℕ} {Ω : Set (Fin n → ℝ)}

private theorem sqrt_sq_add_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    √(a ^ 2 + b ^ 2) ≤ a + b :=
  Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [mul_nonneg ha hb]⟩

private theorem sqrt_sq_add_sq_add_sq_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    √(a ^ 2 + b ^ 2 + c ^ 2) ≤ a + b + c :=
  Real.sqrt_le_iff.2 ⟨by positivity, by
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]⟩

/-- **`S v` lies in the domain of `(d_min)†`** for a vector `v` of `k`-forms with `H¹(ℝⁿ)` data
`hv a`, with `‖(d_min)† S v‖ ≤ c B` for a constant `c` depending only on `n` and `k`. -/
theorem mem_adjoint_wsL2_of_h1Data (hΩ : IsOpen Ω) {k : ℤ} :
    ∃ c : ℝ, ∀ {B : ℝ} {v : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))}
      (_ : ∀ a, H1Data Ω (v a) B), ∃ hx : wsL2 k v ∈ ((extDerivOp ℝ n k).minimal Ω)†.domain,
        ‖((extDerivOp ℝ n k).minimal Ω)† ⟨_, hx⟩‖ ≤ c * B := by
  let b : Fin n → formIdx n k → formIdx n k → Fin n → ℝ := fun a j i m =>
    -∑ t, wsCoeff k t (a, i) * dCoef k t j m
  refine ⟨∑ a, coefSum (b a), fun {B v} hv => ?_⟩
  set w : L2F ℝ Ω (formIdx n k) := ∑ a, (hv a).weak' (b a)
  have key : ∀ φ : formIdx n k → (Fin n → ℝ) → ℝ, ∀ hφ : IsTestField Ω φ,
      ⟪w, testField hφ⟫ = ⟪wsL2 k v, testField ((extDerivOp ℝ n k).isTestField_apply hφ)⟫ := by
    intro φ hφ
    rw [inner_wsL2, wsL2Adj_testField, PiLp.inner_apply v]
    change ⟪∑ a, (hv a).weak' (b a), testField hφ⟫ = _
    rw [sum_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine ((hv a).inner_eq (b a) hφ _ fun i y => ?_).symm
    simp only [wsFieldsAdj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      extDerivOp_apply_eq_dCoef,
      b, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib, neg_neg, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  have hx := ((extDerivOp ℝ n k).mem_adjoint_minimal_domain_iff hΩ).2 ⟨_, key⟩
  refine ⟨hx, ?_⟩
  rw [(extDerivOp ℝ n k).adjoint_minimal_apply_eq hΩ ⟨_, hx⟩ key, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  exact (hv a).norm_weak_le (b a)

/-- **Degree `0`**: `x ∈ H̊Λ⁰(Q)` with `H¹` data is in `H¹_univ`. -/
theorem sobRel_of_h1_zero : ∃ c : ℝ, 0 ≤ c ∧ ∀ {B : ℝ} {x : W0}, 0 ≤ B → x ∈ D0.domain →
    H1Data (cubeDomain 3) x B → SobRel 1 (c * B) 0 x := by
  refine ⟨Fintype.card (formIdx 3 0) + coefSum (dCoef (n := 3) 0), by
    have := coefSum_nonneg (dCoef (n := 3) 0); positivity, fun {B x} hB hx h => ?_⟩
  refine (sobRel_zero_of_mem hx).mono ?_
  have e := h.minimal_apply (isOpen_cubeDomain 3) hx
  have h1 : ‖D0 ⟨x, hx⟩‖ ≤ coefSum (dCoef (n := 3) 0) * B := by
    change ‖(extDerivOp ℝ 3 0).minimal (cubeDomain 3) ⟨x, hx⟩‖ ≤ _
    rw [e]; exact h.norm_weak_le _
  refine (sqrt_sq_add_sq_le (norm_nonneg _) (norm_nonneg _)).trans ?_
  have := h.norm_le
  linarith

/-- **Degree `1`**: `x ∈ H̊Λ¹(Q)` with `H¹` data is in `H¹_univ`. -/
theorem sobRel_of_h1_one : ∃ c : ℝ, 0 ≤ c ∧ ∀ {B : ℝ} {x : W1}, 0 ≤ B → x ∈ D1.domain →
    H1Data (cubeDomain 3) x B → SobRel 1 (c * B) 1 x := by
  refine ⟨Fintype.card (formIdx 3 1) + coefSum (dCoef (n := 3) 1) +
    coefSum (fun r t m => -dCoef (n := 3) 0 t r m), by
      have := coefSum_nonneg (dCoef (n := 3) 1)
      have := coefSum_nonneg (fun r t m => -dCoef (n := 3) 0 t r m)
      positivity, fun {B x} hB hx h => ?_⟩
  obtain ⟨hx', e'⟩ := h.mem_adjoint (isOpen_cubeDomain 3) (k := 0)
  refine (sobRel_one_of_mem hx hx').mono ?_
  have e := h.minimal_apply (isOpen_cubeDomain 3) hx
  have h1 : ‖D1 ⟨x, hx⟩‖ ≤ coefSum (dCoef (n := 3) 1) * B := by
    change ‖(extDerivOp ℝ 3 1).minimal (cubeDomain 3) ⟨x, hx⟩‖ ≤ _
    rw [e]; exact h.norm_weak_le _
  have h2 : ‖D0† ⟨x, hx'⟩‖ ≤ coefSum (fun r t m => -dCoef (n := 3) 0 t r m) * B := by
    change ‖((extDerivOp ℝ 3 0).minimal (cubeDomain 3))† ⟨x, hx'⟩‖ ≤ _
    rw [e']; exact h.norm_weak_le _
  refine (sqrt_sq_add_sq_add_sq_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)).trans ?_
  have := h.norm_le
  linarith

/-- **Degree `2`**: `x ∈ H̊Λ²(Q)` with `H¹` data is in `H¹_univ`. -/
theorem sobRel_of_h1_two : ∃ c : ℝ, 0 ≤ c ∧ ∀ {B : ℝ} {x : W2}, 0 ≤ B → x ∈ D2min.domain →
    H1Data (cubeDomain 3) x B → SobRel 1 (c * B) 2 x := by
  refine ⟨Fintype.card (formIdx 3 2) + coefSum (dCoef (n := 3) 2) +
    coefSum (fun r t m => -dCoef (n := 3) 1 t r m), by
      have := coefSum_nonneg (dCoef (n := 3) 2)
      have := coefSum_nonneg (fun r t m => -dCoef (n := 3) 1 t r m)
      positivity, fun {B x} hB hx h => ?_⟩
  obtain ⟨hx', e'⟩ := h.mem_adjoint (isOpen_cubeDomain 3) (k := 1)
  refine (sobRel_two_of_mem hx hx').mono ?_
  have e := h.minimal_apply (isOpen_cubeDomain 3) hx
  have h1 : ‖D2min ⟨x, hx⟩‖ ≤ coefSum (dCoef (n := 3) 2) * B := by
    change ‖(extDerivOp ℝ 3 2).minimal (cubeDomain 3) ⟨x, hx⟩‖ ≤ _
    rw [e]; exact h.norm_weak_le _
  have h2 : ‖D1† ⟨x, hx'⟩‖ ≤ coefSum (fun r t m => -dCoef (n := 3) 1 t r m) * B := by
    change ‖((extDerivOp ℝ 3 1).minimal (cubeDomain 3))† ⟨x, hx'⟩‖ ≤ _
    rw [e']; exact h.norm_weak_le _
  refine (sqrt_sq_add_sq_add_sq_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)).trans ?_
  have := h.norm_le
  linarith

/-- `‖v‖ ≤ card ι · B` in `PiLp 2` when every `‖vₐ‖ ≤ B`. -/
theorem norm_le_card_mul {ι V : Type*} [Fintype ι] [NormedAddCommGroup V]
    {v : PiLp 2 (fun _ : ι => V)} {B : ℝ} (h : ∀ a, ‖v a‖ ≤ B) : ‖v‖ ≤ Fintype.card ι * B := by
  refine (PiLp.norm_le_sum_norm v).trans ?_
  calc ∑ a, ‖v a‖ ≤ ∑ _a : ι, B := Finset.sum_le_sum fun a _ => h a
    _ = Fintype.card ι * B := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- **`S⁰φ` in degree `1`**: a closed `x = S⁰v ∈ H̊Λ¹(Q)` with `H¹` data `vₐ` is in `H¹_univ`. -/
theorem sobRel_wsL2_zero : ∃ c : ℝ, 0 ≤ c ∧ ∀ {B : ℝ} {v : Wv W0} {x : W1}, 0 ≤ B →
    (∀ a, H1Data (cubeDomain 3) (v a) B) → x = wsL2 (Ω := cubeDomain 3) 0 v →
    ∀ hx : x ∈ D1.domain, D1 ⟨x, hx⟩ = 0 →
      SobRel 1 (c * B) 1 x := by
  obtain ⟨cS, hcS⟩ := mem_adjoint_wsL2_of_h1Data (isOpen_cubeDomain 3) (n := 3) (k := 0)
  refine ⟨‖wsL2 (Ω := cubeDomain 3) (n := 3) 0‖ *
      (Fintype.card (Fin 3) * Fintype.card (formIdx 3 0)) + |cS|, by positivity,
    fun {B v x} hB hv hxv hx h0 => ?_⟩
  subst hxv
  obtain ⟨hx', h2⟩ := hcS hv
  refine (sobRel_one_of_mem hx hx').mono ?_
  rw [h0, norm_zero]
  have h1 : ‖wsL2 (Ω := cubeDomain 3) (n := 3) 0 v‖ ≤
      ‖wsL2 (Ω := cubeDomain 3) (n := 3) 0‖ *
        (Fintype.card (Fin 3) * (Fintype.card (formIdx 3 0) * B)) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
      (norm_le_card_mul fun a => (hv a).norm_le) (norm_nonneg _))
  have h2' : ‖D0† ⟨_, hx'⟩‖ ≤ |cS| * B :=
    h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hB)
  refine (sqrt_sq_add_sq_add_sq_le (norm_nonneg _) le_rfl (norm_nonneg _)).trans ?_
  nlinarith [norm_nonneg (wsL2 (Ω := cubeDomain 3) (n := 3) 0)]

/-- **`S¹u` in degree `2`**: `S¹v` for `vₐ ∈ H̊Λ¹(Q)` with `H¹` data is in `H¹_univ`. -/
theorem sobRel_wsL2_one : ∃ c : ℝ, 0 ≤ c ∧ ∀ {B : ℝ} {v : Wv W1}, 0 ≤ B →
    (∀ a, v a ∈ D1.domain) → (∀ a, H1Data (cubeDomain 3) (v a) B) →
      SobRel 1 (c * B) 2 (wsL2 (Ω := cubeDomain 3) 1 v) := by
  obtain ⟨cS, hcS⟩ := mem_adjoint_wsL2_of_h1Data (isOpen_cubeDomain 3) (n := 3) (k := 1)
  refine ⟨‖wsL2 (Ω := cubeDomain 3) (n := 3) 1‖ *
      (Fintype.card (Fin 3) * Fintype.card (formIdx 3 1)) +
    ‖wsL2 (Ω := cubeDomain 3) (n := 3) 2‖ * (Fintype.card (Fin 3) * coefSum (dCoef (n := 3) 1)) +
      |cS|, by
      have := coefSum_nonneg (dCoef (n := 3) 1); positivity, fun {B v} hB hvD hv => ?_⟩
  obtain ⟨hx', h3⟩ := hcS hv
  obtain ⟨hx, e⟩ := wsL2_mem_minimal (isOpen_cubeDomain 3) 1 (v := v) hvD
  have hx2 : wsL2 (Ω := cubeDomain 3) (n := 3) 1 v ∈ D2min.domain := hx
  refine (sobRel_two_of_mem hx2 hx').mono ?_
  have h1 : ‖wsL2 (Ω := cubeDomain 3) (n := 3) 1 v‖ ≤
      ‖wsL2 (Ω := cubeDomain 3) (n := 3) 1‖ *
        (Fintype.card (Fin 3) * (Fintype.card (formIdx 3 1) * B)) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
      (norm_le_card_mul fun a => (hv a).norm_le) (norm_nonneg _))
  have h2 : ‖D2min ⟨_, hx2⟩‖ ≤
      ‖wsL2 (Ω := cubeDomain 3) (n := 3) 2‖ *
        (Fintype.card (Fin 3) * (coefSum (dCoef (n := 3) 1) * B)) := by
    change ‖(extDerivOp ℝ 3 ((1 : ℕ) + 1)).minimal (cubeDomain 3) ⟨_, hx⟩‖ ≤ _
    rw [e, norm_neg]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
      (norm_le_card_mul fun a => ?_) (norm_nonneg _))
    change ‖(extDerivOp ℝ 3 1).minimal (cubeDomain 3) ⟨v a, hvD a⟩‖ ≤ _
    rw [(hv a).minimal_apply (isOpen_cubeDomain 3) (hvD a)]
    exact (hv a).norm_weak_le _
  have h3' : ‖D1† ⟨_, hx'⟩‖ ≤ |cS| * B :=
    h3.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hB)
  refine (sqrt_sq_add_sq_add_sq_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)).trans ?_
  have := coefSum_nonneg (dCoef (n := 3) 1)
  nlinarith [norm_nonneg (wsL2 (Ω := cubeDomain 3) (n := 3) 1),
    norm_nonneg (wsL2 (Ω := cubeDomain 3) (n := 3) 2)]

end Feec.Models.Cube.WeakSymmetry
