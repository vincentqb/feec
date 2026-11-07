module

public import Solution.Cube
public import Solution.H1Ops
public import Feec.Physics.EinsteinBianchi.WaveFEMRegularity

/-!
# The `H¹` classes of the challenge and `Feec`'s relative parity class

A form `x ∈ H¹(Q)` (`IsSobolevForm (cube 3) 1`) has `H¹(ℝⁿ)` data (`h1Data_of_isSobolevForm`), so
it lies in the domain of `d_min†` (`H1Data.mem_adjoint`); if it also lies in the domain of `d_min`
(vanishing tangential traces), Gaffney's identity on the cube (`sobRel_zero_of_mem`,
`sobRel_one_of_mem`, `sobRel_two_of_mem`) puts it in `Feec`'s relative parity class `H¹_univ`
with norm `O(L)` (`sobRel_of_h1_zero`, `_one`, `_two`). `S⁰φ` and `S¹u` are of that class when the
`φₐ`, `uₐ` are (`sobRel_wsL2_of_h1`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4.3 (Gaffney's inequality)
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open MeasureTheory Set

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

/-! ### From `IsSobolevForm` to `H1Data` -/

theorem norm_toLp_le_of_integral_sq_le {f : (Fin 3 → ℝ) → ℝ} (hf : MemLp f 2 volume) {L : ℝ}
    (h : ∫ y, f y ^ 2 ≤ L ^ 2) : ‖hf.toLp f‖ ≤ |L| := by
  have e : ‖hf.toLp f‖ ^ 2 = ∫ y, f y ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with y hy
    rw [hy, real_inner_eq_re_inner, RCLike.inner_apply]
    simp [sq]
  have h2 : ‖hf.toLp f‖ ^ 2 ≤ L ^ 2 := e ▸ h
  have := sq_le_sq.1 h2
  rwa [abs_norm] at this

/-- **`H¹(Q)` forms have `H¹(ℝⁿ)` data** with bound `|L|`. -/
theorem h1Data_of_isSobolevForm {k : ℕ} {L : ℝ} {x : L2Form (cube 3) k}
    (hx : IsSobolevForm (cube 3) 1 k L x) :
    Nonempty (H1Data (cubeDomain 3) (x : L2F ℝ (cubeDomain 3) (formIdx 3 k)) |L|) := by
  obtain ⟨D, hD, hsum, hxD⟩ := hx
  have hle0 : ∀ t' l', 0 ≤ ∫ y, D t' l' y ^ 2 := fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hle : ∀ t l, l.length ≤ 1 → ∫ y, D t l y ^ 2 ≤ L ^ 2 := fun t l hl => by
    refine le_trans ?_ hsum
    have h1 := Finset.single_le_sum (f := fun p : ℕ => (∑ r : Fin p → Fin 3,
        ∫ y, D t (List.ofFn r) y ^ 2 : ℝ)) (fun _ _ => Finset.sum_nonneg fun _ _ => hle0 _ _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
    have h2 := Finset.single_le_sum (f := fun r : Fin l.length → Fin 3 =>
        (∫ y, D t (List.ofFn r) y ^ 2 : ℝ)) (fun _ _ => hle0 _ _) (Finset.mem_univ l.get)
    have h3 := Finset.single_le_sum (f := fun t' : FormIdx 3 k => (∑ p ∈ Finset.range (1 + 1),
        ∑ r : Fin p → Fin 3, ∫ y, D t' (List.ofFn r) y ^ 2 : ℝ))
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hle0 _ _)
      (Finset.mem_univ t)
    simp only [List.ofFn_get] at h2
    exact h2.trans (h1.trans h3)
  have h0 : ∀ _t : FormIdx 3 k, ([] : List (Fin 3)).length ≤ 1 := fun _ => by simp
  have h1 : ∀ m : Fin 3, [m].length ≤ 1 := fun _ => by simp
  exact ⟨{
    F := fun t => D t []
    G := fun t m => D t [m]
    memF := fun t => (hD t [] (h0 t)).1
    memG := fun t m => (hD t [m] (h1 m)).1
    weak := fun t m φ hφ => by
      have := (hD t [m] (h1 m)).2 φ (isTestFn_of hφ)
      simpa [partialDeriv, coordDir] using this
    ae := hxD
    normF := fun t => norm_toLp_le_of_integral_sq_le _ (hle t [] (h0 t))
    normG := fun t m => norm_toLp_le_of_integral_sq_le _ (hle t [m] (h1 m)) }⟩

/-! ### Gaffney: `H¹` forms with vanishing tangential traces are in the relative class -/

theorem sqrt_sq_add_sq_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a ^ 2 + b ^ 2) ≤ a + b :=
  Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩

theorem sqrt_sq_add_sq_add_sq_le' {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    √(a ^ 2 + b ^ 2 + c ^ 2) ≤ a + b + c :=
  Real.sqrt_le_iff.2 ⟨by positivity, by
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]⟩

/-- The coefficient sum `Σ |a|` of `H1Data.norm_weak_le`. -/
def coefSum {ι κ : Type*} [Fintype ι] [Fintype κ] (a : κ → ι → Fin 3 → ℝ) : ℝ :=
  ∑ j, ∑ i, ∑ m, |a j i m|

theorem coefSum_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (a : κ → ι → Fin 3 → ℝ) :
    0 ≤ coefSum a := by unfold coefSum; positivity

theorem H1Data.norm_weak_le' {ι κ : Type*} [Fintype ι] [Fintype κ] {Ω : Set (Fin 3 → ℝ)}
    {u : L2F ℝ Ω ι} {B : ℝ} (h : H1Data Ω u B) (a : κ → ι → Fin 3 → ℝ) :
    ‖h.weak' a‖ ≤ coefSum a * B := by
  refine (h.norm_weak_le a).trans (le_of_eq ?_)
  simp only [coefSum, Finset.sum_mul]

theorem H1Data.norm_le' {ι : Type*} [Fintype ι] {Ω : Set (Fin 3 → ℝ)}
    {u : L2F ℝ Ω ι} {B : ℝ} (h : H1Data Ω u B) : ‖u‖ ≤ Fintype.card ι * B := by
  refine h.norm_le.trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- **Degree `0`**: `x ∈ H̊Λ⁰(Q)` with `H¹` data is in `H¹_univ`. -/
theorem sobRel_of_h1_zero : ∃ c : ℝ, 0 ≤ c ∧ ∀ {B : ℝ} {x : W0}, 0 ≤ B → x ∈ D0.domain →
    H1Data (cubeDomain 3) x B → Feec.Models.Cube.WeakSymmetry.SobRel 1 (c * B) 0 x := by
  refine ⟨Fintype.card (formIdx 3 0) + coefSum (dCoef (n := 3) 0), by
    have := coefSum_nonneg (dCoef (n := 3) 0); positivity, fun {B x} hB hx h => ?_⟩
  refine (sobRel_zero_of_mem hx).mono ?_
  have e := h.minimal_apply (isOpen_cubeDomain 3) hx
  have h1 : ‖D0 ⟨x, hx⟩‖ ≤ coefSum (dCoef (n := 3) 0) * B := by
    change ‖(extDerivOp ℝ 3 0).minimal (cubeDomain 3) ⟨x, hx⟩‖ ≤ _
    rw [e]; exact h.norm_weak_le' _
  refine (sqrt_sq_add_sq_le' (norm_nonneg _) (norm_nonneg _)).trans ?_
  have := h.norm_le'
  linarith

/-- **Degree `1`**: `x ∈ H̊Λ¹(Q)` with `H¹` data is in `H¹_univ`. -/
theorem sobRel_of_h1_one : ∃ c : ℝ, 0 ≤ c ∧ ∀ {B : ℝ} {x : W1}, 0 ≤ B → x ∈ D1.domain →
    H1Data (cubeDomain 3) x B → Feec.Models.Cube.WeakSymmetry.SobRel 1 (c * B) 1 x := by
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
    rw [e]; exact h.norm_weak_le' _
  have h2 : ‖D0† ⟨x, hx'⟩‖ ≤ coefSum (fun r t m => -dCoef (n := 3) 0 t r m) * B := by
    change ‖((extDerivOp ℝ 3 0).minimal (cubeDomain 3))† ⟨x, hx'⟩‖ ≤ _
    rw [e']; exact h.norm_weak_le' _
  refine (sqrt_sq_add_sq_add_sq_le' (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)).trans ?_
  have := h.norm_le'
  linarith

/-- **Degree `2`**: `x ∈ H̊Λ²(Q)` with `H¹` data is in `H¹_univ`. -/
theorem sobRel_of_h1_two : ∃ c : ℝ, 0 ≤ c ∧ ∀ {B : ℝ} {x : W2}, 0 ≤ B → x ∈ D2min.domain →
    H1Data (cubeDomain 3) x B → Feec.Models.Cube.WeakSymmetry.SobRel 1 (c * B) 2 x := by
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
    rw [e]; exact h.norm_weak_le' _
  have h2 : ‖D1† ⟨x, hx'⟩‖ ≤ coefSum (fun r t m => -dCoef (n := 3) 1 t r m) * B := by
    change ‖((extDerivOp ℝ 3 1).minimal (cubeDomain 3))† ⟨x, hx'⟩‖ ≤ _
    rw [e']; exact h.norm_weak_le' _
  refine (sqrt_sq_add_sq_add_sq_le' (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)).trans ?_
  have := h.norm_le'
  linarith

theorem norm_le_three_mul {V : Type*} [NormedAddCommGroup V] {v : PiLp 2 (fun _ : Fin 3 => V)}
    {B : ℝ} (h : ∀ a, ‖v a‖ ≤ B) : ‖v‖ ≤ 3 * B := by
  refine (H1Data.norm_le_sum v).trans ?_
  calc ∑ a, ‖v a‖ ≤ ∑ _a : Fin 3, B := Finset.sum_le_sum fun a _ => h a
    _ = 3 * B := by simp

/-- **`S⁰φ` in degree `1`**: a closed `x = S⁰v ∈ H̊Λ¹(Q)` with `H¹` data `vₐ` is in `H¹_univ`. -/
theorem sobRel_wsL2_zero : ∃ c : ℝ, 0 ≤ c ∧ ∀ {B : ℝ} {v : Wv W0} {x : W1}, 0 ≤ B →
    (∀ a, H1Data (cubeDomain 3) (v a) B) → x = wsL2 (Ω := cubeDomain 3) 0 v →
    ∀ hx : x ∈ D1.domain, D1 ⟨x, hx⟩ = 0 →
      Feec.Models.Cube.WeakSymmetry.SobRel 1 (c * B) 1 x := by
  obtain ⟨cS, hcS⟩ := mem_adjoint_wsL2 (isOpen_cubeDomain 3) (n := 3) (k := 0)
  refine ⟨‖wsL2 (Ω := cubeDomain 3) (n := 3) 0‖ * (3 * Fintype.card (formIdx 3 0)) + |cS|,
    by positivity, fun {B v x} hB hv hxv hx h0 => ?_⟩
  subst hxv
  obtain ⟨hx', h2⟩ := hcS hv
  refine (sobRel_one_of_mem hx hx').mono ?_
  rw [h0, norm_zero]
  have h1 : ‖wsL2 (Ω := cubeDomain 3) (n := 3) 0 v‖ ≤
      ‖wsL2 (Ω := cubeDomain 3) (n := 3) 0‖ * (3 * (Fintype.card (formIdx 3 0) * B)) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
      (norm_le_three_mul fun a => (hv a).norm_le') (norm_nonneg _))
  have h2' : ‖D0† ⟨_, hx'⟩‖ ≤ |cS| * B := h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hB)
  refine (sqrt_sq_add_sq_add_sq_le' (norm_nonneg _) le_rfl (norm_nonneg _)).trans ?_
  nlinarith [norm_nonneg (wsL2 (Ω := cubeDomain 3) (n := 3) 0)]

/-- **`S¹u` in degree `2`**: `S¹v` for `vₐ ∈ H̊Λ¹(Q)` with `H¹` data is in `H¹_univ`. -/
theorem sobRel_wsL2_one : ∃ c : ℝ, 0 ≤ c ∧ ∀ {B : ℝ} {v : Wv W1}, 0 ≤ B →
    (∀ a, v a ∈ D1.domain) → (∀ a, H1Data (cubeDomain 3) (v a) B) →
      Feec.Models.Cube.WeakSymmetry.SobRel 1 (c * B) 2 (wsL2 (Ω := cubeDomain 3) 1 v) := by
  obtain ⟨cS, hcS⟩ := mem_adjoint_wsL2 (isOpen_cubeDomain 3) (n := 3) (k := 1)
  refine ⟨‖wsL2 (Ω := cubeDomain 3) (n := 3) 1‖ * (3 * Fintype.card (formIdx 3 1)) +
    ‖wsL2 (Ω := cubeDomain 3) (n := 3) 2‖ * (3 * coefSum (dCoef (n := 3) 1)) + |cS|, by
      have := coefSum_nonneg (dCoef (n := 3) 1); positivity, fun {B v} hB hvD hv => ?_⟩
  obtain ⟨hx', h3⟩ := hcS hv
  obtain ⟨hx, e⟩ := wsL2_mem_minimal (isOpen_cubeDomain 3) 1 (v := v) hvD
  have hx2 : wsL2 (Ω := cubeDomain 3) (n := 3) 1 v ∈ D2min.domain := hx
  refine (sobRel_two_of_mem hx2 hx').mono ?_
  have h1 : ‖wsL2 (Ω := cubeDomain 3) (n := 3) 1 v‖ ≤
      ‖wsL2 (Ω := cubeDomain 3) (n := 3) 1‖ * (3 * (Fintype.card (formIdx 3 1) * B)) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
      (norm_le_three_mul fun a => (hv a).norm_le') (norm_nonneg _))
  have h2 : ‖D2min ⟨_, hx2⟩‖ ≤
      ‖wsL2 (Ω := cubeDomain 3) (n := 3) 2‖ * (3 * (coefSum (dCoef (n := 3) 1) * B)) := by
    change ‖(extDerivOp ℝ 3 ((1 : ℕ) + 1)).minimal (cubeDomain 3) ⟨_, hx⟩‖ ≤ _
    rw [e, norm_neg]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
      (norm_le_three_mul fun a => ?_) (norm_nonneg _))
    change ‖(extDerivOp ℝ 3 1).minimal (cubeDomain 3) ⟨v a, hvD a⟩‖ ≤ _
    rw [(hv a).minimal_apply (isOpen_cubeDomain 3) (hvD a)]
    exact (hv a).norm_weak_le' _
  have h3' : ‖D1† ⟨_, hx'⟩‖ ≤ |cS| * B := h3.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hB)
  refine (sqrt_sq_add_sq_add_sq_le' (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)).trans ?_
  have := coefSum_nonneg (dCoef (n := 3) 1)
  nlinarith [norm_nonneg (wsL2 (Ω := cubeDomain 3) (n := 3) 1),
    norm_nonneg (wsL2 (Ω := cubeDomain 3) (n := 3) 2)]

end FEEC
