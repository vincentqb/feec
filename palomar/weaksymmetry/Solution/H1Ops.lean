module

public import Solution.H1
public import Feec.Domain.DeRham
public import Feec.FiniteElement.WeakSymmetryMaps

/-!
# `d`, `d*` and `d* S` on restrictions of `H¹(ℝⁿ)` forms

The exterior derivative has the constant coefficients `dCoef`
(`(dω)_t = Σ_{r, m} dCoef k t r m ∂_m ω_r`, `extDerivOp_apply_eq_dCoef`,
`formalAdj_apply_eq_dCoef`). For a
form `x` with `H¹(ℝⁿ)` data (`H1Data`): `d_min x` is the weak `dx` (`H1Data.minimal_apply`), `x`
lies in the domain of `(d_min)†` (`H1Data.mem_adjoint`), and for a vector `v` of such forms,
`S v = Σₐ dxₐ ∧ vₐ` lies in the domain of `(d_min)†` (`mem_adjoint_wsL2`), all with norms bounded
by a constant times the bound of the data.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open MeasureTheory Set

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement

variable {n : ℕ} {Ω : Set (Fin n → ℝ)}

/-- The coefficients of `d`: `(dω)_t = Σ_{r, m} dCoef k t r m ∂_m ω_r`. -/
def dCoef (k : ℤ) (t : formIdx n (k + 1)) (r : formIdx n k) (m : Fin n) : ℝ :=
  if m ∈ t.1 ∧ t.1.erase m = r.1 then Feec.ExteriorFibre.sgn m t.1 else 0

theorem sum_dCoef_mul (k : ℤ) (t : formIdx n (k + 1)) (r : formIdx n k) (g : Fin n → ℝ) :
    ∑ m, dCoef k t r m * g m = ∑ j ∈ t.1 with t.1.erase j = r.1,
      Feec.ExteriorFibre.sgn j t.1 * g j := by
  rw [Finset.sum_filter]
  simp only [dCoef, ite_mul, zero_mul, ite_and]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem extDerivOp_apply_eq_dCoef (k : ℤ) (φ : formIdx n k → (Fin n → ℝ) → ℝ)
    (t : formIdx n (k + 1)) (x : Fin n → ℝ) : (extDerivOp ℝ n k).apply φ t x =
      ∑ r, ∑ m, dCoef k t r m * fderiv ℝ (φ r) x (coordDir m) := by
  simp only [ConstCoeffOp.apply, applyEntry_extDerivOp_coeff, sum_dCoef_mul]

theorem formalAdj_apply_eq_dCoef (k : ℤ) (ψ : formIdx n (k + 1) → (Fin n → ℝ) → ℝ)
    (r : formIdx n k) (x : Fin n → ℝ) : (extDerivOp ℝ n k).formalAdj.apply ψ r x =
      -∑ t, ∑ m, dCoef k t r m * fderiv ℝ (ψ t) x (coordDir m) := by
  have hc : ∀ t : formIdx n (k + 1),
      ConstCoeffOp.applyEntry ((extDerivOp ℝ n k).formalAdj.coeff r t) (ψ t) x =
        -∑ m, dCoef k t r m * fderiv ℝ (ψ t) x (coordDir m) := by
    intro t
    rw [sum_dCoef_mul, ← Finset.sum_neg_distrib]
    simp only [ConstCoeffOp.formalAdj, ConstCoeffOp.adjEntry, extDerivOp,
      ConstCoeffOp.applyEntry, List.map_map]
    rw [← Finset.sum_map_toList]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp [iterDeriv_singleton]
  simp only [ConstCoeffOp.apply, hc, Finset.sum_neg_distrib]

namespace H1Data

variable {B : ℝ}

/-- **`d_min x` is the weak `dx`** for a form with `H¹(ℝⁿ)` data. -/
theorem minimal_apply (hΩ : IsOpen Ω) {k : ℤ} {x : L2F ℝ Ω (formIdx n k)}
    (hx : x ∈ ((extDerivOp ℝ n k).minimal Ω).domain) (h : H1Data Ω x B) :
    (extDerivOp ℝ n k).minimal Ω ⟨x, hx⟩ = h.weak' (dCoef k) := by
  have hmax : x ∈ ((extDerivOp ℝ n k).maximal Ω).domain :=
    ((extDerivOp ℝ n k).minimal_le_maximal hΩ).1 hx
  rw [((extDerivOp ℝ n k).minimal_le_maximal hΩ).2 (x := ⟨x, hx⟩) (y := ⟨x, hmax⟩) rfl]
  refine (extDerivOp ℝ n k).maximal_apply_eq hΩ ⟨x, hmax⟩ fun φ hφ => ?_
  exact (h.inner_eq (dCoef k) hφ ((extDerivOp ℝ n k).formalAdj.isTestField_apply hφ)
    fun i y => formalAdj_apply_eq_dCoef k φ i y).symm

/-- **A form with `H¹(ℝⁿ)` data lies in the domain of `(d_min)†`**, with value the weak `d*x`. -/
theorem mem_adjoint (hΩ : IsOpen Ω) {k : ℤ} {x : L2F ℝ Ω (formIdx n (k + 1))}
    (h : H1Data Ω x B) : ∃ hx : x ∈ ((extDerivOp ℝ n k).minimal Ω)†.domain,
      ((extDerivOp ℝ n k).minimal Ω)† ⟨x, hx⟩ = h.weak' fun r t m => -dCoef k t r m := by
  have key : ∀ φ : formIdx n k → (Fin n → ℝ) → ℝ, ∀ hφ : IsTestField Ω φ,
      ⟪h.weak' fun r t m => -dCoef k t r m, testField hφ⟫ =
        ⟪x, testField ((extDerivOp ℝ n k).isTestField_apply hφ)⟫ := fun φ hφ =>
    (h.inner_eq _ hφ ((extDerivOp ℝ n k).isTestField_apply hφ) fun i y => by
      rw [extDerivOp_apply_eq_dCoef]
      simp [neg_mul, Finset.sum_neg_distrib]).symm
  have hx := ((extDerivOp ℝ n k).mem_adjoint_minimal_domain_iff hΩ).2 ⟨_, key⟩
  exact ⟨hx, (extDerivOp ℝ n k).adjoint_minimal_apply_eq hΩ ⟨x, hx⟩ key⟩

end H1Data

/-- **`S v` lies in the domain of `(d_min)†`** for a vector `v` of `k`-forms with `H¹(ℝⁿ)` data
`hv a`, with `‖(d_min)† S v‖ ≤ c B` for a constant `c` depending only on `n` and `k`. -/
theorem mem_adjoint_wsL2 (hΩ : IsOpen Ω) {k : ℤ} :
    ∃ c : ℝ, ∀ {B : ℝ} {v : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))}
      (_ : ∀ a, H1Data Ω (v a) B), ∃ hx : wsL2 k v ∈ ((extDerivOp ℝ n k).minimal Ω)†.domain,
        ‖((extDerivOp ℝ n k).minimal Ω)† ⟨_, hx⟩‖ ≤ c * B := by
  let b : Fin n → formIdx n k → formIdx n k → Fin n → ℝ := fun a j i m =>
    -∑ t, wsCoeff k t (a, i) * dCoef k t j m
  refine ⟨∑ a, ∑ j, ∑ i, ∑ m, |b a j i m|, fun {B v} hv => ?_⟩
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
  refine ((hv a).norm_weak_le (b a)).trans (le_of_eq ?_)
  simp only [Finset.sum_mul]

end FEEC
