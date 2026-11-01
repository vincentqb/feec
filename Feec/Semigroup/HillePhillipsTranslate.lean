module

public import Feec.Semigroup.HillePhillips
public import Feec.ForMathlib.Analysis.HalfLineTranslate

/-!
# The Hille–Phillips calculus on translates and on the Taylor kernel

For a bounded semigroup `‖S(t)‖ ≤ M` on a complex Banach space with generator `A`:

* `S(τ m) = S(τ)ᵐ` (`C0Semigroup.S_mul_natCast`) and, on kernels, the calculus is the kernel
  calculus, `Φ(inr k) = Φ_kernel(k)` (`C0Semigroup.hillePhillips_inr`);
* **point masses act as the semigroup**: `Φ(δ_s ⋆ f) = Φ(f) S(s)` for `s ≥ 0`
  (`C0Semigroup.hillePhillipsKernel_translate`), so `Φ` extends to the kernels translated by
  `δ_s` without adjoining `δ_s` to the algebra;
* **Taylor's formula for the semigroup with integral remainder**: for `x ∈ D(A^{p+1})` (a chain
  `u` in the graph of `A`) and `τ > 0`,
  `S(τ) x = Σ_{j≤p} τʲ/j! Aʲ x + τ^{p+1} Φ_τ(eₚ) A^{p+1} x`, `Φ_τ` the calculus of `S(τ ·)` and
  `eₚ = (1 - t)ᵖ/p!` the Taylor kernel (`C0Semigroup.S_apply_eq_sum_add_taylor`), from Taylor's
  formula along a chain of derivatives (`Feec.eq_sum_add_integral_of_hasDerivAt`).

## References

* [E. Hille, R. S. Phillips, *Functional Analysis and Semi-Groups*][HillePhillips1957]
  (the operational calculus of a semigroup)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.2, Thm 2.4 (`S(t) x - x = ∫₀ᵗ S(s) A x ds`; iterated, Taylor's formula along the semigroup)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Finset MeasureTheory

@[expose] public noncomputable section

namespace Feec

namespace C0Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (G : C0Semigroup ℂ E) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M)

omit [CompleteSpace E] in
/-- `S(τ m) = S(τ)ᵐ` for `τ ≥ 0`. -/
theorem S_mul_natCast {τ : ℝ} (hτ : 0 ≤ τ) (m : ℕ) : G.S (τ * m) = G.S τ ^ m := by
  induction m with
  | zero => simp [G.map_zero]
  | succ m ih =>
    rw [Nat.cast_succ, mul_add, mul_one, G.map_add _ _ (by positivity) hτ, ih, pow_succ]

include hM

/-- `Φ(inr k) = Φ_kernel(k)`: on kernels (no atom), the calculus is the kernel calculus. -/
theorem hillePhillips_inr (k : HalfLineKernel) :
    G.hillePhillips hM (Unitization.inr k) = G.hillePhillipsKernel hM k := by
  rw [hillePhillips_apply, Unitization.fst_inr, Unitization.snd_inr, _root_.map_zero, zero_add]

omit [CompleteSpace E] in
/-- **Point masses act as the semigroup**: `Φ(δ_s ⋆ f) = Φ(f) S(s)`, i.e.
`∫ f(t - s) S(t) x dt = ∫ f(t) S(t) S(s) x dt`. -/
theorem hillePhillipsKernel_translate {s : ℝ} (hs : 0 ≤ s) (f : HalfLineKernel) :
    G.hillePhillipsKernel hM (HalfLineKernel.translate s hs f) =
      G.hillePhillipsKernel hM f * G.S s := by
  ext x
  simp only [hillePhillipsKernel_apply, HalfLineKernel.translate_apply]
  rw [← integral_add_right_eq_self (fun t => f (t - s) • G.extS t x) s]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_sub_cancel_right]
  rcases lt_or_ge u 0 with hu | hu
  · simp [f.eq_zero_of_neg u hu]
  · rw [G.extS_of_nonneg (add_nonneg hu hs), G.extS_of_nonneg hu, G.S_add_apply hu hs]
    rfl

/-- **Taylor's formula for the semigroup with integral remainder**: for `τ > 0` and a chain `u`
in the graph of the generator, `S(τ) u₀ = Σ_{j≤p} τʲ/j! uⱼ + τ^{p+1} Φ_τ(eₚ) u_{p+1}`, with
`Φ_τ` the Hille–Phillips calculus of `S(τ ·)` and `eₚ` the Taylor kernel.
Cf. [Pazy1983], §1.2, Thm 2.4 (iterated) -/
theorem S_apply_eq_sum_add_taylor {τ : ℝ} (hτ : 0 < τ) (p : ℕ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    G.S τ (u 0) = ∑ j ∈ range (p + 1), ((τ : ℂ) ^ j / j.factorial) • u j +
      (τ : ℂ) ^ (p + 1) • (G.dilate τ hτ.le).hillePhillipsKernel (G.norm_dilate_S_le hM hτ.le)
        (HalfLineKernel.taylor p) (u (p + 1)) := by
  set f : ℕ → ℝ → E := fun j s => G.extS (τ * s) (((τ : ℂ) ^ j) • u j)
  have hc : ∀ j ≤ p + 1, ContinuousOn (f j) (Icc 0 1) := fun j _ =>
    ((G.continuous_extS_apply _).comp (continuous_const.mul continuous_id)).continuousOn
  have hd : ∀ j ≤ p, ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (f j) (f (j + 1) s) s := by
    intro j hj s hs
    have hg : ((τ : ℂ) ^ j • u j, (τ : ℂ) ^ j • u (j + 1)) ∈ G.generator.graph :=
      G.generator.graph.smul_mem ((τ : ℂ) ^ j) (hu j (by omega))
    obtain ⟨hx, hAx⟩ := LinearPMap.mem_graph_iff_exists.1 hg
    have h1 := G.hasDerivAt_extS_apply ⟨_, hx⟩ (mul_pos hτ hs.1)
    have h2 := h1.scomp s ((hasDerivAt_id s).const_mul τ)
    convert h2 using 1
    · rfl
    simp only [f, hAx, G.extS_of_nonneg (mul_pos hτ hs.1).le]
    rw [_root_.map_smul, _root_.map_smul, ← Complex.coe_smul, smul_smul, pow_succ, mul_one,
      mul_comm]
  have key := eq_sum_add_integral_of_hasDerivAt p hc hd
  simp only [f, mul_one, mul_zero, G.extS_of_nonneg hτ.le, G.extS_of_nonneg le_rfl, G.map_zero,
    pow_zero, one_smul] at key
  rw [key]
  congr 1
  · refine sum_congr rfl fun j _ => ?_
    rw [one_apply_eq_self, ← Complex.coe_smul, smul_smul, div_eq_inv_mul]
    push_cast; rfl
  · rw [hillePhillipsKernel_apply, HalfLineKernel.integral_smul_taylor,
      ← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [Set.uIcc_of_le zero_le_one] at hs; exact hs.1
    rw [(G.dilate τ hτ.le).extS_of_nonneg hs0, _root_.map_smul, smul_comm,
      G.extS_of_nonneg (mul_nonneg hτ.le hs0)]
    rfl

end C0Semigroup

end Feec
