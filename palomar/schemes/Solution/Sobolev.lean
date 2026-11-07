module

public import Solution.Cube
public import Feec.Models.Cube.WeakSymmetryH1

/-!
# The `H¹` classes of the challenge and `Feec`'s `H¹(ℝⁿ)` data

`IsSobolevForm (cube 3) 1` is `Feec.Domain.H1Data` on the cube: a form `x ∈ H¹(Q)` has `H¹(ℝⁿ)`
data with bound `|L|` (`h1Data_of_isSobolevForm`), and `H¹(ℝⁿ)` data with bound `B` give
`x ∈ H¹(Q)` with norm at most `16 B` (`isSobolevForm_of_h1Data`). Feec's Gaffney transfer
(`Feec.Models.Cube.WeakSymmetry.sobRel_of_h1_zero` and its siblings) then puts the `H¹` classes
of the challenge in Feec's relative parity class `H¹_univ` (`Solution.CubeSobolev`).

## References

* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open MeasureTheory Set

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

/-! ### `IsSobolevForm` and `H1Data` -/

theorem norm_toLp_sq {f : (Fin 3 → ℝ) → ℝ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ y, f y ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with y hy
  rw [hy, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [sq]

theorem norm_toLp_le_of_integral_sq_le {f : (Fin 3 → ℝ) → ℝ} (hf : MemLp f 2 volume) {L : ℝ}
    (h : ∫ y, f y ^ 2 ≤ L ^ 2) : ‖hf.toLp f‖ ≤ |L| := by
  have h2 : ‖hf.toLp f‖ ^ 2 ≤ L ^ 2 := (norm_toLp_sq hf) ▸ h
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

/-- The words of length `≤ 1` of `H¹(ℝⁿ)` data: `[] ↦ F`, `[m] ↦ G m`. -/
def h1Word {j : ℤ} {x : L2F ℝ (cubeDomain 3) (formIdx 3 j)} {B : ℝ}
    (h : H1Data (cubeDomain 3) x B) : FormIdx 3 j → List (Fin 3) → (Fin 3 → ℝ) → ℝ
  | t, [] => h.F t
  | t, [m] => h.G t m
  | _, _ => 0

/-- **`H¹(ℝⁿ)` data give `H¹(Q)`**, with norm at most `16 B`. -/
theorem isSobolevForm_of_h1Data {j : ℤ} {B : ℝ} {x : L2Form (cube 3) j}
    (h : H1Data (cubeDomain 3) (x : L2F ℝ (cubeDomain 3) (formIdx 3 j)) B) :
    IsSobolevForm (cube 3) 1 j (16 * B) x := by
  have hl : ∀ t (l : List (Fin 3)), l.length ≤ 1 → MemLp (h1Word h t l) 2 volume ∧
      ∫ y, h1Word h t l y ^ 2 ≤ B ^ 2 := by
    intro t l hl
    match l, hl with
    | [], _ => exact ⟨h.memF t, (norm_toLp_sq (h.memF t)) ▸
        pow_le_pow_left₀ (norm_nonneg _) (h.normF t) 2⟩
    | [m], _ => exact ⟨h.memG t m, (norm_toLp_sq (h.memG t m)) ▸
        pow_le_pow_left₀ (norm_nonneg _) (h.normG t m) 2⟩
    | _ :: _ :: _, hl => simp at hl
  refine ⟨h1Word h, fun t l hl' => ⟨(hl t l hl').1, fun φ hφ => ?_⟩, ?_, h.ae⟩
  · match l, hl' with
    | [], _ => simp [h1Word]
    | [m], _ =>
      have := h.weak t m φ (isTest_of hφ)
      simpa [h1Word, partialDeriv, coordDir] using this
    | _ :: _ :: _, hl => simp at hl
  · have hle : ∀ t, ∀ p ∈ Finset.range (1 + 1), ∀ l : Fin p → Fin 3,
        ∫ y, h1Word h t (List.ofFn l) y ^ 2 ≤ B ^ 2 := fun t p hp l =>
      (hl t _ (by simpa using Nat.lt_succ_iff.1 (Finset.mem_range.1 hp))).2
    refine (Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun p hp =>
      Finset.sum_le_sum fun l _ => hle t p hp l).trans ?_
    have hc : Fintype.card (FormIdx 3 j) ≤ 8 :=
      (Fintype.card_subtype_le _).trans (by simp)
    have hc' : (Fintype.card (FormIdx 3 j) : ℝ) ≤ 8 := by exact_mod_cast hc
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, nsmul_eq_mul]
    norm_num
    nlinarith [sq_nonneg B, mul_le_mul_of_nonneg_right hc' (sq_nonneg B)]

theorem isSobolevForm_mono {j : ℤ} {L L' : ℝ} (hL : 0 ≤ L) (h : L ≤ L') {x : L2Form (cube 3) j}
    (hx : IsSobolevForm (cube 3) 1 j L x) : IsSobolevForm (cube 3) 1 j L' x := by
  obtain ⟨D, hD, hs, hx⟩ := hx
  exact ⟨D, hD, hs.trans (pow_le_pow_left₀ hL h 2), hx⟩

end FEEC
