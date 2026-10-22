module

public import Feec.Models.Cube.DeRham

/-!
# The de Rham complex of the cube `(0, ½)ⁿ` with boundary conditions on part of the boundary:
the parity model

The relative and absolute classes of `Feec.Models.Cube.DeRham` are the fixed complexes of the
reflections `-R_j^*` (resp. `R_j^*`) of the torus de Rham window, for every direction `j`. Mixing
the two signs gives the **mixed classes**: for a set `J` of directions (those with a boundary
condition), the class `mixed d J` is the fixed complex of `ε_j R_j^*`, `ε_j = -1` for `j ∈ J`
and `ε_j = 1` otherwise (`mixedSign`). The coefficient `ω_s` of `dx_s` is then odd in `x_j` iff
`j ∈ J` and `j ∉ s` (the tangential components vanish on the faces `x_j ∈ {0, ½}`, `j ∈ J`) or
`j ∉ J` and `j ∈ s` (the normal components vanish on the other faces): **vanishing tangential
traces on the faces normal to the directions of `J`, vanishing normal traces on the others**
([AFW2010], §4.3; [Arnold2018], Ch. 6, the de Rham complex with boundary conditions on part of
the boundary).

This file proves, in every dimension and degree:

* **the compactness property** (`hasCompactProperty_mixed`) and the **Poincaré inequality**
  `‖u‖ ≤ (2π)⁻¹ ‖d u‖` on `D(d) ∩ N(d)ᗮ` (`norm_le_of_mem_orthogonal_mixed`);
* **the harmonic forms**: only the zero Fourier mode is harmonic, and a constant form `dx_s` is
  fixed by every `ε_j R_j^*` iff `s = J` (`forall_mixedSign_mul_reflSign_eq_one_iff`), so
  `ℌᵏ = 0` for `k ≠ |J|` (`mixed_harmonic_eq_bot`) and `ℌ^{|J|}` is the line of `dx_J`
  (`finrank_mixed_harmonic`, `mixed_harmonic_eq_span`): `Hᵏ(Q, Γ_J) ≅ ℝ` for `k = |J|`;
* **the extreme cases are the relative and absolute classes**: `mixedSymmetries d univ` and
  `mixedSymmetries d ∅` are the symmetries of `relative d` and `absolute d`
  (`mixedSymmetries_univ`, `mixedSymmetries_empty`).

The identification of the mixed class with the `L²` de Rham complex of `Q` with vanishing
tangential traces on the faces normal to `J` is `Feec.Models.Cube.DeRhamPartialIdent`.

The name `partial` of the task is a Lean keyword; the mixed class is `mixed`.

## Main definitions

* `mixedSign`, `mixedSymmetries`, `mixedAction`, `mixed`; `constMode`.

## Main results

* `mem_mixed_fixed_iff`, **`hasCompactProperty_mixed`**, **`norm_le_of_mem_orthogonal_mixed`**.
* `mem_mixed_harmonic_iff`, **`forall_mixedSign_mul_reflSign_eq_one_iff`**,
  **`mixed_harmonic_eq_bot`**, **`finrank_mixed_harmonic`**, `mixed_harmonic_eq_span`.
* **`mixedSymmetries_univ`**, **`mixedSymmetries_empty`**.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4.3 (the de Rham complex with boundary conditions, compactness)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6 (boundary conditions on
  part of the boundary; harmonic forms)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set Feec.Fourier Feec.Fourier.Exterior Finset

namespace Feec.Models.Cube.DeRham

open Feec.Models.Torus.DeRham (window windowSymbol)

variable {d : Type*} [LinearOrder d]

/-! ### The mixed signs -/

/-- The sign `ε_j` of the mixed class: `-1` for the directions with a boundary condition
(`j ∈ J`), `1` otherwise. -/
def mixedSign (J : Finset d) (j : d) : ℂ := if j ∈ J then -1 else 1

theorem mixedSign_mul_self (J : Finset d) (j : d) : mixedSign J j * mixedSign J j = 1 := by
  unfold mixedSign; split_ifs <;> norm_num

theorem conj_mixedSign_mul_self (J : Finset d) (j : d) :
    (starRingEnd ℂ) (mixedSign J j) * mixedSign J j = 1 := by
  unfold mixedSign; split_ifs <;> norm_num

@[simp] theorem mixedSign_univ [Fintype d] (j : d) : mixedSign Finset.univ j = parSign true := by
  simp [mixedSign, parSign]

/-- **A constant form `dx_s` is fixed by every `ε_j R_j^*` iff `s = J`**: `ε_j ε_j(s) = 1` iff
(`j ∈ J` iff `j ∈ s`). -/
theorem forall_mixedSign_mul_reflSign_eq_one_iff {J s : Finset d} :
    (∀ j, mixedSign J j * reflSign j s = 1) ↔ s = J := by
  constructor
  · intro h
    ext j
    have := h j
    unfold mixedSign reflSign at this
    by_cases hJ : j ∈ J <;> by_cases hs : j ∈ s <;> simp_all <;> norm_num at this
  · rintro rfl j
    unfold mixedSign reflSign
    split_ifs <;> norm_num

variable [Fintype d]

variable (d) in
/-- **The reflections of the cube in the mixed class `J`**, as fibre symmetries of the torus de
Rham window: `n ↦ flip_j n` on the frequencies, `v ↦ ε_j R_j^* v` on the coefficients. -/
def mixedSymmetries (J : Finset d) : (windowSymbol d).Symmetries d where
  R j := Reflection.count_of_involutive (flipAt j) (flipAt_flipAt j)
  ρ j i := mixedSign J j • reflForm j (i : ℕ)
  invol j i v := by
    simp only [_root_.smul_apply, _root_.map_smul, reflForm_reflForm, smul_smul,
      mixedSign_mul_self, one_smul]
  inner_ρ j i v w := by
    simp only [_root_.smul_apply, inner_smul_left, inner_smul_right, inner_reflForm, ← mul_assoc]
    rw [mul_comm (mixedSign J j), conj_mixedSign_mul_self, one_mul]
  symm j i i' n v := by
    change (deRham d).m i i' (Fourier.Torus.freq (flipAt j n)) (mixedSign J j • reflForm j i v) =
      mixedSign J j • reflForm j i' ((deRham d).m i i' (Fourier.Torus.freq n) v)
    rw [freq_flipAt, _root_.map_smul, deRham_reflForm]
  comm_σ j l n := flipAt_comm j l n
  comm_ρ j l i v := by
    simp only [_root_.smul_apply, _root_.map_smul, reflForm_comm j l, smul_smul, mul_comm]

variable (d) in
/-- The action of `(ℤ/2)ᵈ` on the torus de Rham window generated by the mixed reflections. -/
abbrev mixedAction (J : Finset d) : (window d).Action (Multiplicative (d → ZMod 2)) :=
  (mixedSymmetries d J).toAction

instance instCompleteSpaceMixedFixed (J : Finset d) (i : Fin (Fintype.card d + 1)) :
    CompleteSpace ((mixedAction d J).fixed i) :=
  ((mixedAction d J).isClosed_fixed i).completeSpace_coe

variable (d) in
/-- **The de Rham complex of the cube in the mixed class `J`**: vanishing tangential traces on
the faces `x_j ∈ {0, ½}`, `j ∈ J`, vanishing normal traces on the other faces (the method of
images). -/
abbrev mixed (J : Finset d) :
    HilbertComplex ℂ (ComplexShape.window (Fintype.card d + 1))
      fun i => (mixedAction d J).fixed i :=
  (mixedAction d J).fixedComplex

/-- **The mixed class, coefficientwise**: `u` is fixed iff `ε_j R_j^* u(flip_j n) = u(n)` for all
`j` and `n`. -/
theorem mem_mixed_fixed_iff {J : Finset d} {i : Fin (Fintype.card d + 1)}
    {u : Lp (Form ℂ d i) 2 (Measure.count : Measure (d → ℤ))} :
    u ∈ (mixedAction d J).fixed i ↔
      ∀ j n, mixedSign J j • reflForm j i (u (flipAt j n)) = u n := by
  rw [(mixedSymmetries d J).mem_fixed_toAction]
  refine forall_congr' fun j => ⟨fun h n => ?_, fun h => Lp.ext_count fun n => ?_⟩
  · have e := Measure.ae_count_iff.1 (coeFn_symLp ((mixedSymmetries d J).R j)
      ((mixedSymmetries d J).ρ j i) u) n
    rw [h] at e
    exact e.symm
  · rw [Measure.ae_count_iff.1 (coeFn_symLp ((mixedSymmetries d J).R j)
      ((mixedSymmetries d J).ρ j i) u) n]
    exact h n

/-! ### Compactness -/

/-- **The compactness property of the de Rham complex of the cube in the mixed class `J`**, in
every degree (Rellich and Gaffney with mixed boundary conditions, in this model). [AFW2010], §4.3 -/
theorem hasCompactProperty_mixed (J : Finset d) : (mixed d J).HasCompactProperty :=
  (mixedAction d J).hasCompactProperty_fixedComplex Torus.DeRham.window_hasCompactProperty

/-- **The Poincaré inequality on the cube in the mixed class `J`**, every degree:
`‖u‖ ≤ (2π)⁻¹ ‖d u‖` for `u ∈ D(d) ∩ N(d)ᗮ`. -/
theorem norm_le_of_mem_orthogonal_mixed (J : Finset d) {i j : Fin (Fintype.card d + 1)}
    (u : ((mixed d J).d i j).domain)
    (hu : (u : (mixedAction d J).fixed i) ∈ ((mixed d J).d i j).kerᗮ) :
    ‖(u : (mixedAction d J).fixed i)‖ ≤ (2 * Real.pi)⁻¹ * ‖(mixed d J).d i j u‖ :=
  (mixedAction d J).reducingSubcomplex_fixed.norm_le_of_mem_orthogonal
    window_norm_le_of_mem_orthogonal u hu

/-- **The harmonic forms of the mixed class** are the fixed constant forms. -/
theorem mem_mixed_harmonic_iff {J : Finset d} {i : Fin (Fintype.card d + 1)}
    {x : (mixedAction d J).fixed i} :
    x ∈ (mixed d J).harmonic i ↔
      ∀ n, n ≠ 0 → (x : Lp (Form ℂ d i) 2 (Measure.count : Measure (d → ℤ))) n = 0 :=
  ((mixedAction d J).mem_harmonic_fixedComplex_iff).trans mem_window_harmonic_iff

/-- The zero mode of a fixed form is fixed by every `ε_j R_j^*`. -/
theorem mixedSign_reflForm_zero {J : Finset d} {i : Fin (Fintype.card d + 1)}
    (x : (mixedAction d J).fixed i) (j : d) (t : {s : Finset d // #s = (i : ℕ)}) :
    mixedSign J j * reflSign j t.1 *
        (x : Lp (Form ℂ d i) 2 (Measure.count : Measure (d → ℤ))) 0 t =
      (x : Lp (Form ℂ d i) 2 (Measure.count : Measure (d → ℤ))) 0 t := by
  have h := congrArg (fun v : Form ℂ d i => v t) (mem_mixed_fixed_iff.1 x.2 j 0)
  simp only [flipAt_zero, PiLp.smul_apply, reflForm_apply, smul_eq_mul] at h
  rw [mul_assoc]; exact h

/-- **The zero mode of a fixed form vanishes off `J`.** -/
theorem coeff_zero_eq_zero_of_ne {J : Finset d} {i : Fin (Fintype.card d + 1)}
    (x : (mixedAction d J).fixed i) {t : {s : Finset d // #s = (i : ℕ)}} (ht : t.1 ≠ J) :
    (x : Lp (Form ℂ d i) 2 (Measure.count : Measure (d → ℤ))) 0 t = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, mixedSign J j * reflSign j t.1 ≠ 1 := by
    by_contra h
    push Not at h
    exact ht (forall_mixedSign_mul_reflSign_eq_one_iff.1 h)
  by_contra hne
  exact hj (mul_right_cancel₀ hne ((mixedSign_reflForm_zero x j t).trans (one_mul _).symm))

/-- **No harmonic forms of the mixed class outside degree `|J|`.** -/
theorem mixed_harmonic_eq_bot {J : Finset d} {i : Fin (Fintype.card d + 1)}
    (hi : (i : ℕ) ≠ #J) : (mixed d J).harmonic i = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  refine Subtype.ext (Lp.ext_count fun n => ?_)
  rw [ZeroMemClass.coe_zero, coeFn_zero_count]
  by_cases hn : n = 0
  · subst hn
    ext t
    have ht : t.1 ≠ J := fun h => hi (by rw [← t.2, h])
    rw [coeff_zero_eq_zero_of_ne x ht]; rfl
  · exact mem_mixed_harmonic_iff.1 hx n hn

/-- The constant form `dx_J` in degree `i = |J|`, on the Fourier side: the zero mode `dx_J`. -/
def constMode (J : Finset d) {i : Fin (Fintype.card d + 1)} (hi : (i : ℕ) = #J) :
    Lp (Form ℂ d i) 2 (Measure.count : Measure (d → ℤ)) :=
  Torus.DeRham.const i (EuclideanSpace.single ⟨J, hi.symm⟩ 1)

theorem constMode_apply (J : Finset d) {i : Fin (Fintype.card d + 1)} (hi : (i : ℕ) = #J)
    (n : d → ℤ) :
    (constMode J hi : (d → ℤ) → Form ℂ d i) n =
      if n = 0 then EuclideanSpace.single ⟨J, hi.symm⟩ 1 else 0 :=
  Torus.DeRham.const_apply i _ n

theorem constMode_mem_fixed (J : Finset d) {i : Fin (Fintype.card d + 1)} (hi : (i : ℕ) = #J) :
    constMode J hi ∈ (mixedAction d J).fixed i := by
  refine mem_mixed_fixed_iff.2 fun j n => ?_
  rw [constMode_apply, constMode_apply]
  by_cases hn : n = 0
  · subst hn
    simp only [flipAt_zero, ite_true]
    ext t
    rw [PiLp.smul_apply, reflForm_apply, smul_eq_mul, ← mul_assoc]
    by_cases ht : t = ⟨J, hi.symm⟩
    · subst ht
      rw [forall_mixedSign_mul_reflSign_eq_one_iff.2 rfl j, one_mul]
    · simp [ht]
  · have hn' : flipAt j n ≠ 0 := (flipAt_eq_zero_iff j).not.2 hn
    simp [hn, hn']

theorem constMode_mem_harmonic (J : Finset d) {i : Fin (Fintype.card d + 1)} (hi : (i : ℕ) = #J) :
    (⟨constMode J hi, constMode_mem_fixed J hi⟩ : (mixedAction d J).fixed i) ∈
      (mixed d J).harmonic i :=
  mem_mixed_harmonic_iff.2 fun n hn => by
    change (constMode J hi : (d → ℤ) → Form ℂ d i) n = 0
    simp [constMode_apply, hn]

theorem constMode_ne_zero (J : Finset d) {i : Fin (Fintype.card d + 1)} (hi : (i : ℕ) = #J) :
    (⟨constMode J hi, constMode_mem_fixed J hi⟩ : (mixedAction d J).fixed i) ≠ 0 := by
  intro h0
  have h1 : (constMode J hi : (d → ℤ) → Form ℂ d i) 0 ⟨J, hi.symm⟩ = 1 := by
    simp [constMode_apply]
  have h2 : constMode J hi = 0 := congrArg Subtype.val h0
  rw [h2, coeFn_zero_count] at h1
  simp at h1

/-- **The harmonic `|J|`-forms of the mixed class are the line of `dx_J`.** -/
theorem mixed_harmonic_eq_span (J : Finset d) {i : Fin (Fintype.card d + 1)}
    (hi : (i : ℕ) = #J) :
    ((mixed d J).harmonic i : Submodule ℂ ((mixedAction d J).fixed i)) =
      ℂ ∙ (⟨constMode J hi, constMode_mem_fixed J hi⟩ : (mixedAction d J).fixed i) := by
  refine le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2
    (constMode_mem_harmonic J hi))
  rw [Submodule.mem_span_singleton]
  refine ⟨(w : Lp (Form ℂ d i) 2 (Measure.count : Measure (d → ℤ))) 0 ⟨J, hi.symm⟩,
    Subtype.ext (Lp.ext_count fun n => ?_)⟩
  rw [Submodule.coe_smul, coeFn_smul_count]
  change _ • (constMode J hi : (d → ℤ) → Form ℂ d i) n = _
  rw [constMode_apply]
  by_cases hn : n = 0
  · subst hn
    simp only [ite_true]
    ext t
    by_cases ht : t = ⟨J, hi.symm⟩
    · subst ht; simp
    · have ht' : t.1 ≠ J := fun h => ht (Subtype.ext h)
      simp [ht, coeff_zero_eq_zero_of_ne w ht']
  · rw [mem_mixed_harmonic_iff.1 hw n hn]
    simp [hn]

/-- **The harmonic forms of the mixed class are one-dimensional in degree `|J|`**
(`H^{|J|}(Q, Γ_J) ≅ ℂ`). -/
theorem finrank_mixed_harmonic (J : Finset d) {i : Fin (Fintype.card d + 1)}
    (hi : (i : ℕ) = #J) : Module.finrank ℂ ((mixed d J).harmonic i) = 1 := by
  rw [mixed_harmonic_eq_span J hi]
  exact finrank_span_singleton (constMode_ne_zero J hi)

/-- **`J = univ` is the relative class**: the mixed symmetries are those of `relative d`. -/
theorem mixedSymmetries_univ : mixedSymmetries d Finset.univ = symmetries d true := by
  unfold mixedSymmetries symmetries
  congr 1
  all_goals (funext j i; rw [mixedSign_univ])

/-- **`J = ∅` is the absolute class**: the mixed symmetries are those of `absolute d`. -/
theorem mixedSymmetries_empty : mixedSymmetries d ∅ = symmetries d false := by
  unfold mixedSymmetries symmetries
  congr 1

end Feec.Models.Cube.DeRham
