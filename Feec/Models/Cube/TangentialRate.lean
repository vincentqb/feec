module

public import Feec.Models.Cube.PolyRate
public import Feec.Models.Cube.DeRhamIdentCutoff

/-!
# Rates of convergence on the cube for solutions with vanishing tangential traces

The rates of `Feec.Models.Cube.PolyRate` in `H̊Λ(Q)` are stated for `FEM.IsCsFormMin`, `C^{s+2}`
forms on `ℝⁿ` vanishing outside `Q = (0, ½)ⁿ`, which are flat at `∂Q`. This module replaces that
class by the natural one, `C^{s+2}` forms whose **tangential components vanish on the faces**:

* `FEM.IsTangentialZero w`: for `j ∉ t` and `y ∈ cl Q` with `y_j ∈ {0, ½}`, `(w y)_t = 0`;
  `extDeriv` preserves it (`IsTangentialZero.extDeriv`).
* `FEM.IsCsFormTr s j L x`: `x = w|_Q` for a `C^{s+2}` `j`-form `w` with `IsTangentialZero w`
  and `‖Dⁱw‖, ‖Dⁱ dw‖ ≤ L` on `cl Q` for `i ≤ s + 1` (sup bounds included). Satisfiable
  (`exists_isCsFormTr`); it contains the flat class with the same bound
  (`IsCsFormMin.isCsFormTr`: flatness and the mean value theorem bound the lower derivatives) and
  is strictly larger (`isCsFormTr_normalWitness`, `not_isCsFormMin_normalWitness`: the `1`-form
  `(∏_{j ≠ 0} sin 2πy_j) dx₀` has nonzero normal component on `∂Q`).
* `IsCsFormTr.add`, `IsCsFormTr.smul` (the class is a cone, bounds add) and `IsCsFormMin.sub`
  (differences of flat forms are flat).
* **`IsCsFormTr.mem_domain`**, `IsCsFormTr.d_eq`: `x ∈ D(d_min) = H̊Λʲ(Q)` and
  `d_min x = (dw)|_Q`, for `C¹` forms with bounded first derivatives
  (`mem_minimal_of_isTangentialZero`; the cut-off argument of
  `Feec.Models.Cube.DeRhamIdent.mem_closure_extDerivOp_of_tangential`, which needs `C^∞`, with
  the cut-offs `χ_m w ∈ C¹_c(Q)` placed in `D(d_min)` by
  `Feec.Domain.ConstCoeffOp.mem_minimal_of_maximal_of_support_subset`).
* **`IsTangentialZero.dof_eq_zero`**: the canonical-interpolant DOFs of `w` vanish on every face of
  a boundary facet: a boundary facet lies in one face `{y_j = c}` of the cube
  (`exists_face_of_isBoundaryFacet`), and a simplex there only sees the components `t` with
  `j ∉ t`. So the interpolant has vanishing boundary DOFs (`globalInterp_mem_globalSpace₀_of_tr`)
  and `exists_mem_polyMin_le_of_tr`, `IsCsFormTr.exists_mem_polyMin_le` give
  `‖x − v‖, ‖d(x − v)‖ ≤ B_j L h^{s+1}` for some `v ∈ V̊ₕʲ`.
* The rates on the new class: `mixed_rate_polyTr`, `mixed_rate_polyTr_of_polyOrderAt`,
  `mixed_rate_lagrangeP2Tr`, `norm_sub_le_windowTr_poly_smooth`, `norm_sub_le_windowTr_lagrangeP2`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.9 (quasi-optimality of the mixed method)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §6.2 (vanishing tangential
  traces), Ch. 7 (approximation estimates)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.4 (cut-off arguments)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.14 (convergence of the semi-discrete Hodge wave equation)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff ENNReal

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.ExteriorFibre

variable {n : ℕ}

/-! ### The closed cube -/

theorem mem_closure_cubeDomain {y : Fin n → ℝ} :
    y ∈ closure (cubeDomain n) ↔ ∀ i, y i ∈ Icc (0 : ℝ) (1 / 2) := by
  rw [cubeDomain, closure_pi_set]
  simp only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 2), Set.mem_pi, Set.mem_univ, true_imp_iff]

theorem convex_closure_cubeDomain : Convex ℝ (closure (cubeDomain n)) :=
  (convex_cubeDomain n).closure

/-- A point of `cl Q` not in `Q` lies on a face `{y_j ∈ {0, ½}}`. -/
theorem exists_face_of_mem_closure_of_notMem {y : Fin n → ℝ} (hy : y ∈ closure (cubeDomain n))
    (hyQ : y ∉ cubeDomain n) : ∃ j, y j = 0 ∨ y j = 1 / 2 := by
  have h := mem_closure_cubeDomain.1 hy
  by_contra hne
  push Not at hne
  exact hyQ fun i _ => ⟨lt_of_le_of_ne (h i).1 (hne i).1.symm,
    lt_of_le_of_ne (h i).2 (hne i).2⟩

/-! ### Forms with vanishing tangential components on the faces -/

/-- The **tangential components of `w` vanish on the faces** of `Q = (0, ½)ⁿ`: for `j ∉ t` and
`y ∈ cl Q` with `y_j ∈ {0, ½}`, `(w y)_t = 0` (`dx_t` is tangent to `{y_j = c}` iff `j ∉ t`). -/
def IsTangentialZero (w : FormField n) : Prop :=
  ∀ y ∈ closure (cubeDomain n), ∀ (j : Fin n) (t : Finset (Fin n)), j ∉ t →
    (y j = 0 ∨ y j = 1 / 2) → w y t = 0

/-- A form vanishing outside `Q` (continuous) has vanishing tangential components. -/
theorem isTangentialZero_of_vanish {w : FormField n}
    (hsupp : ∀ y ∉ cubeDomain n, w y = 0) : IsTangentialZero w := by
  intro y hy j t _ hyj
  have hyQ : y ∉ cubeDomain n := fun h => by
    have := h j (mem_univ j)
    rcases hyj with h0 | h1
    · rw [h0] at this; exact lt_irrefl _ this.1
    · rw [h1] at this; exact lt_irrefl _ this.2
  rw [hsupp y hyQ]; rfl

/-- **The derivative along a face of a function vanishing on the face vanishes**: if
`f = 0` on `{y ∈ cl Q : y_j = c}` and `i ≠ j`, then `∂ᵢ f = 0` there (one-sided derivative). -/
theorem partialDeriv_eq_zero_of_face {f : (Fin n → ℝ) → ℝ} {j i : Fin n} (hij : i ≠ j) {c : ℝ}
    {y : Fin n → ℝ} (hy : y ∈ closure (cubeDomain n)) (hyj : y j = c)
    (hf0 : ∀ z ∈ closure (cubeDomain n), z j = c → f z = 0)
    (hd : DifferentiableAt ℝ f y) : partialDeriv i f y = 0 := by
  have hl : HasDerivAt (fun s : ℝ => f (y + s • (Pi.single i (1 : ℝ) : Fin n → ℝ)))
      (fderiv ℝ f y (Pi.single i 1)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => y + s • (Pi.single i (1 : ℝ) : Fin n → ℝ))
        (Pi.single i 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Fin n → ℝ)).const_add y
    have h2 : HasFDerivAt f (fderiv ℝ f y) (y + (0 : ℝ) • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
      simpa using hd.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hyi := (mem_closure_cubeDomain.1 hy) i
  have hmem : ∀ s : ℝ, y i + s ∈ Icc (0 : ℝ) (1 / 2) →
      f (y + s • (Pi.single i (1 : ℝ) : Fin n → ℝ)) = 0 := by
    intro s hs
    refine hf0 _ (mem_closure_cubeDomain.2 fun l => ?_) ?_
    · by_cases hl : l = i
      · subst hl; simpa [add_comm] using hs
      · simpa [Pi.single_apply, hl] using (mem_closure_cubeDomain.1 hy) l
    · simp [Ne.symm hij, hyj]
  rw [partialDeriv]
  rcases lt_or_eq_of_le hyi.2 with hlt | heq
  · -- the right-sided derivative
    have hw : HasDerivWithinAt (fun s : ℝ => f (y + s • (Pi.single i (1 : ℝ) : Fin n → ℝ)))
        0 (Icc 0 (1 / 2 - y i)) 0 := by
      refine (hasDerivWithinAt_const (0 : ℝ) (Icc 0 (1 / 2 - y i)) (0 : ℝ)).congr
        (fun s hs => hmem s ⟨by linarith [hs.1, hyi.1], by linarith [hs.2]⟩)
        (hmem 0 (by simpa using hyi))
    exact (uniqueDiffOn_Icc (by linarith)).uniqueDiffWithinAt
      ⟨le_rfl, by linarith⟩ |>.eq_deriv _ hl.hasDerivWithinAt hw
  · have hw : HasDerivWithinAt (fun s : ℝ => f (y + s • (Pi.single i (1 : ℝ) : Fin n → ℝ)))
        0 (Icc (-(1 / 2)) 0) 0 := by
      refine (hasDerivWithinAt_const (0 : ℝ) (Icc (-(1 / 2)) 0) (0 : ℝ)).congr
        (fun s hs => hmem s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
        (hmem 0 (by simpa using hyi))
    exact (uniqueDiffOn_Icc (by norm_num)).uniqueDiffWithinAt
      ⟨by norm_num, le_rfl⟩ |>.eq_deriv _ hl.hasDerivWithinAt hw

/-- **`d` preserves vanishing tangential traces**: the tangential components of `dw` are
tangential derivatives of tangential components of `w`. -/
theorem IsTangentialZero.extDeriv {w : FormField n} (hw : Differentiable ℝ w)
    (h : IsTangentialZero w) : IsTangentialZero (FiniteElement.extDeriv w) := by
  intro y hy j t hjt hyj
  rw [extDeriv_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hij : i ≠ j := fun e => hjt (e ▸ hi)
  have hj' : j ∉ t.erase i := fun h' => hjt (Finset.mem_of_mem_erase h')
  rcases hyj with h0 | h1
  · rw [partialDeriv_eq_zero_of_face hij hy h0
      (fun z hz hzj => h z hz j _ hj' (Or.inl hzj)) (differentiableAt_pi.1 (hw y) _), mul_zero]
  · rw [partialDeriv_eq_zero_of_face hij hy h1
      (fun z hz hzj => h z hz j _ hj' (Or.inr hzj)) (differentiableAt_pi.1 (hw y) _), mul_zero]

/-! ### The class `IsCsFormTr` -/

/-- `x ∈ L²(Q; Λʲ)` is a `C^{s+2}` form of degree `j` **with vanishing tangential traces on
`∂Q`** (`IsTangentialZero`) whose derivatives of order `≤ s + 1` (including the values) and those
of its exterior derivative are bounded by `L` on `cl Q` (trivially true in negative degrees).
No condition is put on the normal components. -/
def IsCsFormTr (s : ℕ) (j : ℤ) (L : ℝ) (x : L2F ℝ (cubeDomain n) (formIdx n j)) : Prop :=
  j < 0 ∨ ∃ k : ℕ, (k : ℤ) = j ∧ ∃ w : FormField n,
    ∃ hw : ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w, (∀ y, IsDeg k (w y)) ∧
    IsTangentialZero w ∧
    (∀ i ≤ s + 1, ∀ y ∈ closure (cubeDomain n),
      ‖iteratedFDeriv ℝ i w y‖ ≤ L ∧ ‖iteratedFDeriv ℝ i (FiniteElement.extDeriv w) y‖ ≤ L) ∧
    x = formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j ⟨w, hw.continuous⟩

theorem IsCsFormTr.mono {s : ℕ} {j : ℤ} {L L' : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)}
    (hx : IsCsFormTr s j L x) (hLL' : L ≤ L') : IsCsFormTr s j L' x := by
  rcases hx with hj | ⟨k, hk, w, hw, hdeg, htan, hL, he⟩
  · exact Or.inl hj
  · exact Or.inr ⟨k, hk, w, hw, hdeg, htan, fun i hi y hy =>
      ⟨(hL i hi y hy).1.trans hLL', (hL i hi y hy).2.trans hLL'⟩, he⟩

/-- The class with vanishing traces is contained in the class with no boundary condition. -/
theorem IsCsFormTr.isCsForm {s : ℕ} {j : ℤ} {L : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)}
    (hx : IsCsFormTr s j L x) : IsCsForm s j L x := by
  rcases hx with hj | ⟨k, hk, w, hw, hdeg, -, hL, he⟩
  · exact Or.inl hj
  · exact Or.inr ⟨k, hk, w, hw, hdeg, fun y hy => (hL (s + 1) le_rfl y hy).1,
      fun y hy => (hL (s + 1) le_rfl y hy).2, he⟩

/-- A bound on the derivatives of order `≤ m` on the compact `cl Q`. -/
theorem exists_bound_iteratedFDeriv_le {m : ℕ} {w : FormField n} (hw : ContDiff ℝ m w) :
    ∃ L, 0 ≤ L ∧ ∀ i ≤ m, ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ i w y‖ ≤ L := by
  have hb : ∀ i ∈ Finset.range (m + 1), ∃ L, 0 ≤ L ∧
      ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ i w y‖ ≤ L := fun i hi =>
    exists_bound_iteratedFDeriv (hw.of_le (by exact_mod_cast Finset.mem_range_succ_iff.1 hi))
  choose! B hB0 hB using hb
  refine ⟨∑ i ∈ Finset.range (m + 1), B i, Finset.sum_nonneg hB0, fun i hi y hy => ?_⟩
  have hi' : i ∈ Finset.range (m + 1) := Finset.mem_range_succ_iff.2 hi
  exact (hB i hi' y hy).trans (Finset.single_le_sum hB0 hi')

/-- **Every `C^{s+2}` form with vanishing tangential traces is `IsCsFormTr s`** for some bound
`L ≥ 0`. -/
theorem exists_isCsFormTr (s : ℕ) {k : ℕ} {w : FormField n}
    (hw : ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w) (hdeg : ∀ y, IsDeg k (w y))
    (htan : IsTangentialZero w) :
    ∃ L, 0 ≤ L ∧ IsCsFormTr s (k : ℤ) L
      (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
        ⟨w, hw.continuous⟩) := by
  obtain ⟨L, hL0, hL⟩ := exists_bound_iteratedFDeriv_le (m := s + 1)
    (hw.of_le (by exact_mod_cast Nat.le_succ (s + 1)))
  have hw' : ContDiff ℝ (((s + 1 : ℕ) : WithTop ℕ∞) + 1) w := by exact_mod_cast hw
  have hdw : ContDiff ℝ ((s + 1 : ℕ) : WithTop ℕ∞) (FiniteElement.extDeriv w) :=
    contDiff_extDeriv hw'
  obtain ⟨L', hL'0, hL'⟩ := exists_bound_iteratedFDeriv_le hdw
  exact ⟨max L L', le_max_of_le_left hL0, Or.inr ⟨k, rfl, w, hw, hdeg, htan,
    fun i hi y hy => ⟨(hL i hi y hy).trans (le_max_left _ _),
      (hL' i hi y hy).trans (le_max_right _ _)⟩, rfl⟩⟩

/-- The zero form is `IsCsFormTr` with every bound `L ≥ 0`. -/
theorem isCsFormTr_zero (s : ℕ) (k : ℕ) {L : ℝ} (hL0 : 0 ≤ L) :
    IsCsFormTr s (k : ℤ) L (0 : L2F ℝ (cubeDomain n) (formIdx n k)) := by
  refine Or.inr ⟨k, rfl, 0, contDiff_const, fun y t _ => rfl, fun y _ j t _ _ => rfl,
    fun i _ y _ => ?_, ?_⟩
  · have e : FiniteElement.extDeriv (0 : FormField n) = 0 :=
      extDeriv_const (0 : Finset (Fin n) → ℝ)
    rw [e]
    simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero, and_self, hL0]
  · exact (map_zero _).symm

/-- **Scaling of the class**: `c • x` is `IsCsFormTr` with bound `|c| L`. -/
theorem IsCsFormTr.smul {s : ℕ} {j : ℤ} {L : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)}
    (hx : IsCsFormTr s j L x) (c : ℝ) : IsCsFormTr s j (|c| * L) (c • x) := by
  rcases hx with hj | ⟨k, hk, w, hw, hdeg, htan, hL, rfl⟩
  · exact Or.inl hj
  have hw' : ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) (c • w) := hw.const_smul c
  have hdw : FiniteElement.extDeriv (c • w) = c • FiniteElement.extDeriv w := funext fun y =>
    extDeriv_smul_const_apply c ((hw.differentiable (by simp)) y)
  have hw1 : ContDiff ℝ (((s + 1 : ℕ) : WithTop ℕ∞) + 1) w := by exact_mod_cast hw
  have hdwc : ContDiff ℝ ((s + 1 : ℕ) : WithTop ℕ∞) (FiniteElement.extDeriv w) :=
    contDiff_extDeriv hw1
  refine Or.inr ⟨k, hk, c • w, hw', fun y t ht => by simp [hdeg y t ht],
    fun y hy i t hit hyi => by simp [htan y hy i t hit hyi], fun i hi y hy => ⟨?_, ?_⟩, ?_⟩
  · rw [iteratedFDeriv_const_smul_apply
      ((hw.of_le (by exact_mod_cast (by omega : i ≤ s + 2))).contDiffAt), norm_smul,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hL i hi y hy).1 (abs_nonneg c)
  · rw [hdw, iteratedFDeriv_const_smul_apply
      ((hdwc.of_le (by exact_mod_cast hi)).contDiffAt), norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hL i hi y hy).2 (abs_nonneg c)
  · rw [← map_smul]; rfl

/-- `d` is additive on differentiable form fields. -/
theorem extDeriv_add_eq {w w' : FormField n} (hw : Differentiable ℝ w)
    (hw' : Differentiable ℝ w') :
    FiniteElement.extDeriv (w + w') = FiniteElement.extDeriv w + FiniteElement.extDeriv w' :=
  funext fun x => extDeriv_add_apply (hw x) (hw' x)

/-- `d` commutes with differences of differentiable form fields. -/
theorem extDeriv_sub_eq {w w' : FormField n} (hw : Differentiable ℝ w)
    (hw' : Differentiable ℝ w') :
    FiniteElement.extDeriv (w - w') = FiniteElement.extDeriv w - FiniteElement.extDeriv w' := by
  funext x
  have e : w - w' = w + (-1 : ℝ) • w' := by
    funext y; simp [sub_eq_add_neg]
  rw [e, extDeriv_add_apply (hw x) ((hw' x).const_smul (-1 : ℝ)),
    extDeriv_smul_const_apply _ (hw' x)]
  simp [sub_eq_add_neg]

/-- **Sums in the class**: `x + y` is `IsCsFormTr` with bound `L + L'`. -/
theorem IsCsFormTr.add {s : ℕ} {j : ℤ} {L L' : ℝ} {x y : L2F ℝ (cubeDomain n) (formIdx n j)}
    (hx : IsCsFormTr s j L x) (hy : IsCsFormTr s j L' y) : IsCsFormTr s j (L + L') (x + y) := by
  rcases hx with hj | ⟨k, hk, w, hw, hdeg, htan, hL, rfl⟩
  · exact Or.inl hj
  rcases hy with hj | ⟨k', hk', w', hw', hdeg', htan', hL', rfl⟩
  · exact Or.inl hj
  obtain rfl : k' = k := by omega
  have hd : Differentiable ℝ w := hw.differentiable (by simp)
  have hd' : Differentiable ℝ w' := hw'.differentiable (by simp)
  have hw1 : ContDiff ℝ (((s + 1 : ℕ) : WithTop ℕ∞) + 1) w := by exact_mod_cast hw
  have hw1' : ContDiff ℝ (((s + 1 : ℕ) : WithTop ℕ∞) + 1) w' := by exact_mod_cast hw'
  have hdw := contDiff_extDeriv hw1
  have hdw' := contDiff_extDeriv hw1'
  refine Or.inr ⟨k', hk, w + w', hw.add hw', fun y t ht => by simp [hdeg y t ht, hdeg' y t ht],
    fun y hy i t hit hyi => by simp [htan y hy i t hit hyi, htan' y hy i t hit hyi],
    fun i hi y hy => ⟨?_, ?_⟩, ?_⟩
  · have hi' : (i : WithTop ℕ∞) ≤ ((s + 2 : ℕ) : WithTop ℕ∞) := by exact_mod_cast (by omega)
    rw [iteratedFDeriv_add_apply ((hw.of_le hi').contDiffAt) ((hw'.of_le hi').contDiffAt)]
    exact (norm_add_le _ _).trans (add_le_add (hL i hi y hy).1 (hL' i hi y hy).1)
  · have hi' : (i : WithTop ℕ∞) ≤ ((s + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hi
    rw [extDeriv_add_eq hd hd', iteratedFDeriv_add_apply ((hdw.of_le hi').contDiffAt)
      ((hdw'.of_le hi').contDiffAt)]
    exact (norm_add_le _ _).trans (add_le_add (hL i hi y hy).2 (hL' i hi y hy).2)
  · rw [← map_add]; rfl

/-- **Differences in the flat class**: `x − y` is `IsCsFormMin` with bound `L + L'`. -/
theorem IsCsFormMin.sub {s : ℕ} {j : ℤ} {L L' : ℝ} {x y : L2F ℝ (cubeDomain n) (formIdx n j)}
    (hx : IsCsFormMin s j L x) (hy : IsCsFormMin s j L' y) : IsCsFormMin s j (L + L') (x - y) := by
  rcases hx with hj | ⟨k, hk, w, hw, hdeg, hsupp, hL, hdL, rfl⟩
  · exact Or.inl hj
  rcases hy with hj | ⟨k', hk', w', hw', hdeg', hsupp', hL', hdL', rfl⟩
  · exact Or.inl hj
  obtain rfl : k' = k := by omega
  have hd : Differentiable ℝ w := hw.differentiable (by simp)
  have hd' : Differentiable ℝ w' := hw'.differentiable (by simp)
  have hw1 : ContDiff ℝ (((s + 1 : ℕ) : WithTop ℕ∞) + 1) w := by exact_mod_cast hw
  have hw1' : ContDiff ℝ (((s + 1 : ℕ) : WithTop ℕ∞) + 1) w' := by exact_mod_cast hw'
  have hdw := contDiff_extDeriv hw1
  have hdw' := contDiff_extDeriv hw1'
  refine Or.inr ⟨k', hk, w - w', hw.sub hw', fun y t ht => by simp [hdeg y t ht, hdeg' y t ht],
    fun y hy => by simp [hsupp y hy, hsupp' y hy], fun y hy => ?_, fun y hy => ?_, ?_⟩
  · have hi' : ((s + 1 : ℕ) : WithTop ℕ∞) ≤ ((s + 2 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (by omega)
    rw [iteratedFDeriv_sub_apply ((hw.of_le hi').contDiffAt) ((hw'.of_le hi').contDiffAt)]
    exact (norm_sub_le _ _).trans (add_le_add (hL y hy) (hL' y hy))
  · rw [extDeriv_sub_eq hd hd', iteratedFDeriv_sub_apply (hdw.contDiffAt) (hdw'.contDiffAt)]
    exact (norm_sub_le _ _).trans (add_le_add (hdL y hy) (hdL' y hy))
  · rw [← map_sub]; rfl

/-- A component of `formL2` vanishes if the component of the form vanishes identically. -/
theorem formL2_apply_eq_zero {j : ℤ} {w : contForms n} {t : formIdx n j}
    (h : ∀ y, (w : FormField n) y t.1 = 0) :
    formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j w t = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j w t,
    Lp.coeFn_zero ℝ 2 (volume.restrict (cubeDomain n))] with y h1 h2
  rw [h1, h2, h y]; rfl

/-! ### Flat forms are in the class, with the same bound -/

/-- `update y 0 ½` lies in `cl Q` for `y ∈ cl Q`. -/
theorem update_mem_closure_cubeDomain [NeZero n] {y : Fin n → ℝ}
    (hy : y ∈ closure (cubeDomain n)) :
    Function.update y 0 (1 / 2) ∈ closure (cubeDomain n) := by
  refine mem_closure_cubeDomain.2 fun i => ?_
  by_cases hi : i = 0
  · subst hi; simp
  · rw [Function.update_of_ne hi]; exact mem_closure_cubeDomain.1 hy i

theorem norm_update_sub_le [NeZero n] {y : Fin n → ℝ} (hy : y ∈ closure (cubeDomain n)) :
    ‖Function.update y 0 (1 / 2) - y‖ ≤ 1 / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  by_cases hi : i = 0
  · subst hi
    have h0 := mem_closure_cubeDomain.1 hy 0
    simp only [Pi.sub_apply, Function.update_self, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith [h0.2])]
    linarith [h0.1]
  · simp [Function.update_of_ne hi]

/-- **Derivatives of a field vanishing beyond the face `{y₀ = ½}`**: if `f = 0` on `{y₀ > ½}`
and `‖D^p f‖ ≤ L` on `cl Q`, then `‖Dⁱ f‖ ≤ L` on `cl Q` for every `i ≤ p` (`Dⁱ f = 0` on the face
by continuity, and the mean value theorem along a segment of length `≤ ½`). -/
theorem norm_iteratedFDeriv_le_of_flat [NeZero n] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : (Fin n → ℝ) → E} {p : ℕ} (hf : ContDiff ℝ p f)
    (h0 : ∀ z : Fin n → ℝ, 1 / 2 < z 0 → f z = 0) {L : ℝ}
    (hL : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ p f y‖ ≤ L) :
    ∀ i ≤ p, ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ i f y‖ ≤ L := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL _ (subset_closure (center_mem_cubeDomain n)))
  set U : Set (Fin n → ℝ) := {z | 1 / 2 < z 0}
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_apply 0)
  -- `Dⁱ f = 0` on `U`, hence on `{z₀ ≥ ½}`
  have hzero : ∀ i ≤ p, ∀ z : Fin n → ℝ, 1 / 2 ≤ z 0 → iteratedFDeriv ℝ i f z = 0 := by
    intro i hi z hz
    have hU : ∀ z ∈ U, iteratedFDeriv ℝ i f z = 0 := fun z hz => by
      have hev : f =ᶠ[𝓝 z] fun _ => 0 :=
        Filter.eventually_of_mem (hUo.mem_nhds hz) fun x hx => h0 x hx
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev i).eq_of_nhds]; simp
    have hc : Continuous (iteratedFDeriv ℝ i f) :=
      hf.continuous_iteratedFDeriv (by exact_mod_cast hi)
    have hcl : z ∈ closure U := by
      refine Metric.mem_closure_iff.2 fun ε hε => ⟨Function.update z 0 (z 0 + ε / 2), ?_, ?_⟩
      · change 1 / 2 < Function.update z 0 (z 0 + ε / 2) 0
        rw [Function.update_self]; linarith
      · rw [dist_comm, dist_eq_norm]
        refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun l => ?_)
          (by linarith : ε / 2 < ε)
        by_cases hl : l = 0
        · subst hl; simp [abs_of_pos hε]
        · simp [Function.update_of_ne hl]; positivity
    exact (isClosed_eq hc continuous_const).closure_subset_iff.2 hU hcl
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = p - d := ⟨p - i, by omega⟩
  induction d with
  | zero => simpa using hL
  | succ d ih =>
    intro y hy
    by_cases hd : p ≤ d
    · have : p - (d + 1) = p - d := by omega
      rw [this]; exact ih (by omega) y hy
    have hlt : p - (d + 1) < p := by omega
    set i := p - (d + 1)
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ i f) :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast hlt)
    have hbd : ∀ z ∈ closure (cubeDomain n), ‖fderiv ℝ (iteratedFDeriv ℝ i f) z‖ ≤ L := by
      intro z hz
      rw [norm_fderiv_iteratedFDeriv, show i + 1 = p - d by omega]
      exact ih (by omega) z hz
    have hmvt := convex_closure_cubeDomain.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hdiff z) hbd hy (update_mem_closure_cubeDomain hy)
    rw [hzero i hlt.le _ (by simp), zero_sub, norm_neg] at hmvt
    calc ‖iteratedFDeriv ℝ i f y‖ ≤ L * ‖Function.update y 0 (1 / 2) - y‖ := hmvt
      _ ≤ L * (1 / 2) := mul_le_mul_of_nonneg_left (norm_update_sub_le hy) hL0
      _ ≤ L := by linarith

/-- **The flat class is contained in `IsCsFormTr`, with the same bound**: a `C^{s+2}` form
vanishing outside `Q` has vanishing tangential traces, and its derivatives of order `≤ s + 1`
(and those of `dw`) are bounded by the bound `L` of the `(s+1)`-st ones
(`norm_iteratedFDeriv_le_of_flat`). -/
theorem IsCsFormMin.isCsFormTr [NeZero n] {s : ℕ} {j : ℤ} {L : ℝ}
    {x : L2F ℝ (cubeDomain n) (formIdx n j)} (hx : IsCsFormMin s j L x) : IsCsFormTr s j L x := by
  rcases hx with hj | ⟨k, hk, w, hw, hdeg, hsupp, hL, hL', he⟩
  · exact Or.inl hj
  have hout : ∀ z : Fin n → ℝ, 1 / 2 < z 0 → z ∉ cubeDomain n := fun z hz h => by
    have := (h 0 (mem_univ 0)).2; linarith
  have hw1 : ContDiff ℝ ((s + 1 : ℕ) : WithTop ℕ∞) w :=
    hw.of_le (by exact_mod_cast Nat.le_succ (s + 1))
  have hw' : ContDiff ℝ (((s + 1 : ℕ) : WithTop ℕ∞) + 1) w := by exact_mod_cast hw
  have hdw : ContDiff ℝ ((s + 1 : ℕ) : WithTop ℕ∞) (FiniteElement.extDeriv w) :=
    contDiff_extDeriv hw'
  have hdw0 : ∀ z : Fin n → ℝ, 1 / 2 < z 0 → FiniteElement.extDeriv w z = 0 := by
    intro z hz
    have hU : IsOpen {z : Fin n → ℝ | 1 / 2 < z 0} :=
      isOpen_lt continuous_const (continuous_apply 0)
    have hev : w =ᶠ[𝓝 z] fun _ => 0 :=
      Filter.eventually_of_mem (hU.mem_nhds hz) fun x hx => hsupp x (hout x hx)
    funext t
    rw [extDeriv_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have hev' : (fun y => w y (t.erase l)) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with y hy; rw [hy]; rfl
    rw [partialDeriv, hev'.fderiv_eq]; simp
  have b1 := norm_iteratedFDeriv_le_of_flat hw1 (fun z hz => hsupp z (hout z hz)) hL
  have b2 := norm_iteratedFDeriv_le_of_flat hdw hdw0 hL'
  exact Or.inr ⟨k, hk, w, hw, hdeg, isTangentialZero_of_vanish hsupp,
    fun i hi y hy => ⟨b1 i hi y hy, b2 i hi y hy⟩, he⟩

/-! ### A non-flat form of the class -/

/-- **The witness**: the `1`-form `(∏_{j ≠ 0} sin 2πy_j) dx₀`, whose only (normal) component on
the faces `{y₀ ∈ {0, ½}}` does not vanish; its tangential components vanish on all faces. -/
def normalWitness [NeZero n] : FormField n := fun y t =>
  if t = {0} then ∏ j ∈ Finset.univ.erase (0 : Fin n), Real.sin (2 * Real.pi * y j) else 0

theorem contDiff_normalWitness [NeZero n] : ContDiff ℝ ∞ (normalWitness (n := n)) := by
  refine contDiff_pi.2 fun t => ?_
  unfold normalWitness
  split_ifs
  · exact contDiff_prod fun j _ =>
      Real.contDiff_sin.comp (contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin n => ℝ) j))
  · exact contDiff_const

theorem isDeg_normalWitness [NeZero n] (y : Fin n → ℝ) : IsDeg 1 (normalWitness y) := by
  intro t ht
  simp only [normalWitness]
  split_ifs with h
  · subst h; simp at ht
  · rfl

theorem isTangentialZero_normalWitness [NeZero n] :
    IsTangentialZero (normalWitness (n := n)) := by
  intro y _ j t hjt hyj
  simp only [normalWitness]
  split_ifs with ht
  · subst ht
    have hj : j ∈ Finset.univ.erase (0 : Fin n) :=
      Finset.mem_erase.2 ⟨fun h => hjt (by simp [h]), Finset.mem_univ j⟩
    refine Finset.prod_eq_zero hj ?_
    rcases hyj with h | h
    · simp [h]
    · rw [h, show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.sin_pi]
  · rfl

/-- The boundary point `(0, ⅛, …, ⅛)` of the face `{y₀ = 0}`. -/
def normalWitnessPoint [NeZero n] : Fin n → ℝ := fun i => if i = 0 then 0 else 1 / 8

theorem normalWitnessPoint_mem_closure [NeZero n] :
    normalWitnessPoint (n := n) ∈ closure (cubeDomain n) := by
  refine mem_closure_cubeDomain.2 fun i => ?_
  unfold normalWitnessPoint
  split_ifs <;> norm_num

theorem normalWitnessPoint_notMem [NeZero n] : normalWitnessPoint (n := n) ∉ cubeDomain n :=
  fun h => by have := (h 0 (mem_univ 0)).1; simp [normalWitnessPoint] at this

/-- **The normal component of the witness does not vanish on `∂Q`.** -/
theorem normalWitness_ne_zero [NeZero n] :
    normalWitness normalWitnessPoint ({0} : Finset (Fin n)) ≠ 0 := by
  simp only [normalWitness, ↓reduceIte]
  refine ne_of_gt (Finset.prod_pos fun j hj => ?_)
  have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
  simp only [normalWitnessPoint, hj0, ↓reduceIte]
  rw [show 2 * Real.pi * (1 / 8) = Real.pi / 4 by ring, Real.sin_pi_div_four]
  positivity

/-- **The class is nonempty beyond the flat forms**: the witness lies in `IsCsFormTr s 1` for
some bound. -/
theorem isCsFormTr_normalWitness [NeZero n] (s : ℕ) : ∃ L, 0 ≤ L ∧ IsCsFormTr s 1 L
    (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) 1
      ⟨normalWitness, contDiff_normalWitness.continuous⟩) := by
  have h := exists_isCsFormTr (n := n) s (k := 1) (contDiff_infty.1 contDiff_normalWitness _)
    isDeg_normalWitness isTangentialZero_normalWitness
  exact_mod_cast h

/-- **The witness is not flat**: it is not `IsCsFormMin s 1 L` for any `s, L` (every
representative vanishing outside `Q` vanishes on `∂Q`, while the witness does not). -/
theorem not_isCsFormMin_normalWitness [NeZero n] (s : ℕ) (L : ℝ) : ¬ IsCsFormMin s 1 L
    (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) 1
      ⟨normalWitness, contDiff_normalWitness.continuous⟩) := by
  rintro (hj | ⟨k, hk, w, hw, -, hsupp, -, -, he⟩)
  · norm_num at hj
  obtain rfl : k = 1 := by exact_mod_cast hk
  set t0 : formIdx n 1 := ⟨{0}, by simp⟩
  have hae := congrArg (fun z : L2F ℝ (cubeDomain n) (formIdx n 1) => (z t0 : (Fin n → ℝ) → ℝ)) he
  have h1 := coeFn_formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) 1
    ⟨normalWitness, contDiff_normalWitness.continuous⟩ t0
  have h2 := coeFn_formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) 1
    ⟨w, hw.continuous⟩ t0
  have hae' : (fun y => normalWitness y t0.1) =ᵐ[volume.restrict (cubeDomain n)]
      fun y => w y t0.1 := by
    refine h1.symm.trans (EventuallyEq.trans ?_ h2)
    exact Filter.EventuallyEq.of_eq hae
  have hc1 : Continuous fun y => normalWitness (n := n) y t0.1 :=
    (contDiff_pi.1 contDiff_normalWitness t0.1).continuous
  have hc2 : Continuous fun y => w y t0.1 := (continuous_apply _).comp hw.continuous
  have heq := (MeasureTheory.Measure.eqOn_of_ae_eq hae' hc1.continuousOn hc2.continuousOn
    (by rw [(isOpen_cubeDomain n).interior_eq]; exact subset_closure)).closure hc1 hc2
  have := heq normalWitnessPoint_mem_closure
  simp only [hsupp _ normalWitnessPoint_notMem, Pi.zero_apply] at this
  exact normalWitness_ne_zero this

/-! ### Vanishing tangential traces put a smooth form in `H̊Λ(Q)` -/

theorem Q_subset_cubeDomain : Geometry.Q (Fin n) ⊆ cubeDomain n := fun _ hy i _ =>
  Geometry.mem_Q.1 hy i

/-- **`L²(Q)`-convergence of uniformly bounded, pointwise convergent sequences** (dominated
convergence on the bounded cube). -/
theorem tendsto_toLp_cubeDomain_of_bdd {g : ℕ → (Fin n → ℝ) → ℝ} {h : (Fin n → ℝ) → ℝ}
    (hg : ∀ m, MemLp (g m) 2 (volume.restrict (cubeDomain n)))
    (hh : MemLp h 2 (volume.restrict (cubeDomain n))) {K : ℝ}
    (hK : ∀ m, ∀ y ∈ cubeDomain n, |g m y| ≤ K)
    (hlim : ∀ y ∈ cubeDomain n, Tendsto (fun m => g m y) atTop (𝓝 (h y))) :
    Tendsto (fun m => (hg m).toLp (g m)) atTop (𝓝 (hh.toLp h)) := by
  have : IsFiniteMeasure (volume.restrict (cubeDomain n)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isBounded_cubeDomain n).measure_lt_top⟩
  rw [tendsto_iff_edist_tendsto_0]
  simp_rw [Lp.edist_toLp_toLp]
  have hui : UnifIntegrable g 2 (volume.restrict (cubeDomain n)) := by
    refine (unifIntegrable_const (ι := ℕ) one_le_two (by norm_num)
      (memLp_const (μ := volume.restrict (cubeDomain n)) K)).ae_mono
      (fun m => (hg m).aestronglyMeasurable) fun m => ?_
    filter_upwards [ae_restrict_mem (isOpen_cubeDomain n).measurableSet] with y hy
    rw [enorm_le_iff_norm_le, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hK m y hy).trans (le_abs_self K)
  exact tendsto_Lp_finite_of_tendsto_ae one_le_two (by norm_num)
    (fun m => (hg m).aestronglyMeasurable) hh hui
    (by filter_upwards [ae_restrict_mem (isOpen_cubeDomain n).measurableSet] with y hy
        exact hlim y hy)

/-- Dominated convergence for the classes `formL2` of continuous forms. -/
theorem tendsto_formL2_of_bdd (j : ℤ) {f : ℕ → contForms n} {g : contForms n} {K : ℝ}
    (hK : ∀ m, ∀ y ∈ cubeDomain n, ∀ t, |(f m : FormField n) y t| ≤ K)
    (hlim : ∀ y ∈ cubeDomain n, ∀ t,
      Tendsto (fun m => (f m : FormField n) y t) atTop (𝓝 ((g : FormField n) y t))) :
    Tendsto (fun m => formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j (f m))
      atTop (𝓝 (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j g)) := by
  refine DeRhamIdent.tendsto_L2F_of_forall fun s => ?_
  exact tendsto_toLp_cubeDomain_of_bdd (g := fun m => formComp (k := j) (f m : FormField n) s)
    (h := formComp (k := j) (g : FormField n) s)
    (fun m => memLp_of_continuous (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n)
      (continuous_formComp (f m).2 s))
    (memLp_of_continuous (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n)
      (continuous_formComp g.2 s)) (fun m y hy => hK m y hy s.1)
    (fun y hy => hlim y hy s.1)

/-- **A tangential component is `O(dist)` to its faces**: for `j ∉ r` and `y ∈ Q`,
`|(w y)_r| ≤ L min(y_j, ½ - y_j)` if `‖Dw‖ ≤ L` on `cl Q`. -/
theorem abs_le_of_isTangentialZero {w : FormField n} (hw : Differentiable ℝ w)
    (htan : IsTangentialZero w) {L : ℝ} (hD : ∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L)
    {y : Fin n → ℝ} (hy : y ∈ cubeDomain n) {j : Fin n} {r : Finset (Fin n)} (hjr : j ∉ r) :
    |w y r| ≤ L * min (y j) (1 / 2 - y j) := by
  have hyc : y ∈ closure (cubeDomain n) := subset_closure hy
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hD y hyc)
  have hyj : y j ∈ Ioo (0 : ℝ) (1 / 2) := hy j (mem_univ j)
  have key : ∀ c : ℝ, (c = 0 ∨ c = 1 / 2) → |w y r| ≤ L * |y j - c| := by
    intro c hc
    set y' := Function.update y j c
    have hy' : y' ∈ closure (cubeDomain n) := by
      refine mem_closure_cubeDomain.2 fun i => ?_
      by_cases hi : i = j
      · subst hi; rcases hc with rfl | rfl <;> simp [y']
      · simp only [y', Function.update_of_ne hi]; exact mem_closure_cubeDomain.1 hyc i
    have h0 : w y' r = 0 := htan y' hy' j r hjr (by simpa [y'] using hc)
    have hmvt := convex_closure_cubeDomain.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hw z) hD hy' hyc
    have hd : ‖y - y'‖ ≤ |y j - c| := by
      refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => ?_
      by_cases hi : i = j
      · subst hi; simp [y']
      · simp [y', Function.update_of_ne hi]
    calc |w y r| = |w y r - w y' r| := by rw [h0, sub_zero]
      _ ≤ ‖w y - w y'‖ := by
          have := norm_le_pi_norm (w y - w y') r
          rwa [Pi.sub_apply, Real.norm_eq_abs] at this
      _ ≤ L * ‖y - y'‖ := hmvt
      _ ≤ L * |y j - c| := mul_le_mul_of_nonneg_left hd hL0
  have h1 := key 0 (Or.inl rfl)
  have h2 := key (1 / 2) (Or.inr rfl)
  rw [sub_zero, abs_of_pos hyj.1] at h1
  rw [abs_sub_comm, abs_of_pos (by linarith [hyj.2] : (0 : ℝ) < 1 / 2 - y j)] at h2
  rw [mul_min_of_nonneg _ _ hL0]
  exact le_min h1 h2

/-- **Smooth forms with vanishing tangential traces lie in `H̊Λ(Q)`**, `C¹` version: a `C¹`
`k`-form `w` on `ℝⁿ` with `IsTangentialZero w` and `‖w‖, ‖Dw‖, ‖dw‖ ≤ L` on `cl Q` restricts to
`x ∈ D(d_min)` with `d_min x = (dw)|_Q`. The cut-offs `χ_m w` are `C¹` with compact support in
`Q`, hence in `D(d_min)` (`mem_minimal_of_maximal_of_support_subset`); they converge to `w` with
`d(χ_m w) = dχ_m ∧ w + χ_m dw → dw`, dominated by the commutator bound
`|∂ⱼχ_m · w_{t∖j}| ≤ 4 M₀ L` (`abs_le_of_isTangentialZero`, `abs_deriv_eta_mul_le`); `d_min` is
closed. -/
theorem mem_minimal_of_isTangentialZero [NeZero n] {k : ℕ} {w : FormField n}
    (hw : ContDiff ℝ 1 w) (hdeg : ∀ y, IsDeg k (w y)) (htan : IsTangentialZero w) {L : ℝ}
    (hM : ∀ y ∈ closure (cubeDomain n), ‖w y‖ ≤ L)
    (hD : ∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L)
    (hdM : ∀ y ∈ closure (cubeDomain n), ‖FiniteElement.extDeriv w y‖ ≤ L) :
    ∃ h : formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
        ⟨w, hw.continuous⟩ ∈ ((extDerivOp ℝ n k).minimal (cubeDomain n)).domain,
      (extDerivOp ℝ n k).minimal (cubeDomain n) ⟨_, h⟩ =
        formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
          ⟨FiniteElement.extDeriv w, continuous_extDeriv hw⟩ := by
  set A := extDerivOp ℝ n (k : ℤ)
  have hwd : Differentiable ℝ w := hw.differentiable one_ne_zero
  set χ : ℕ → (Fin n → ℝ) → ℝ := fun m => DeRhamIdent.chi (d := Fin n) m
  have hχ : ∀ m, ContDiff ℝ 1 (χ m) := fun m =>
    (DeRhamIdent.contDiff_chi (d := Fin n) m).of_le (by exact_mod_cast le_top)
  set u : ℕ → FormField n := fun m y => χ m y • w y
  have hu : ∀ m, ContDiff ℝ 1 (u m) := fun m => (hχ m).smul hw
  have hudeg : ∀ m y, IsDeg k (u m y) := fun m y t ht => by
    simp [u, hdeg y t ht]
  -- the cut-offs lie in the graph of `d_min`
  have hmem : ∀ m, (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
      ⟨u m, (hu m).continuous⟩,
      formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
        ⟨FiniteElement.extDeriv (u m), continuous_extDeriv (hu m)⟩) ∈
        (A.minimal (cubeDomain n)).graph := by
    intro m
    obtain ⟨h, hval⟩ := formL2_mem_domain k (hu m) (hudeg m)
    have hDm := deRham_maximalComplex_d (𝕜 := ℝ) (n := n) (isOpen_cubeDomain n) (k : ℤ)
    have h' : formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
        ⟨u m, (hu m).continuous⟩ ∈ (A.maximal (cubeDomain n)).domain := hDm ▸ h
    have hval' : A.maximal (cubeDomain n) ⟨_, h'⟩ =
        formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
          ⟨FiniteElement.extDeriv (u m), continuous_extDeriv (hu m)⟩ :=
      (LinearPMap.apply_eq_of_eq' hDm ⟨_, h⟩).symm.trans hval
    obtain ⟨hmin, hmv⟩ := A.mem_minimal_of_maximal_of_support_subset (isOpen_cubeDomain n)
      (DeRhamIdent.isCompact_chiBox (d := Fin n) m)
      ((DeRhamIdent.chiBox_subset_Q m).trans Q_subset_cubeDomain) ⟨_, h'⟩ fun i => by
        filter_upwards [coeFn_formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n)
          k ⟨u m, (hu m).continuous⟩ i] with x hx hxK
        change (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨u m, (hu m).continuous⟩ i : (Fin n → ℝ) → ℝ) x = 0
        rw [hx]
        have hχ0 : χ m x = 0 := Function.notMem_support.1 fun h =>
          hxK (DeRhamIdent.support_chi_subset m h)
        simp [u, hχ0]
    exact (LinearPMap.mem_graph_iff _).2 ⟨⟨_, hmin⟩, rfl, hmv.trans hval'⟩
  -- the commutator bound
  obtain ⟨M₀, -, hM₀⟩ := RowWise.exists_bound_deriv_smoothTransition
  have hM00 : 0 ≤ M₀ := (abs_nonneg _).trans (hM₀ 0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hM _ (subset_closure (center_mem_cubeDomain n)))
  have hdu : ∀ m y, FiniteElement.extDeriv (u m) y =
      wedge (grad (χ m) y) (w y) + χ m y • FiniteElement.extDeriv w y := fun m y =>
    extDeriv_smul_apply ((hχ m).differentiable one_ne_zero y) (hwd y)
  have hbu : ∀ m, ∀ y ∈ cubeDomain n, ∀ t, |u m y t| ≤ L := by
    intro m y hy t
    have h1 : |w y t| ≤ L := by
      have := norm_le_pi_norm (w y) t
      rw [Real.norm_eq_abs] at this
      exact this.trans (hM y (subset_closure hy))
    simp only [u, Pi.smul_apply, smul_eq_mul, abs_mul]
    calc |χ m y| * |w y t| ≤ 1 * L :=
          mul_le_mul (DeRhamIdent.abs_chi_le_one m y) h1 (abs_nonneg _) zero_le_one
      _ = L := one_mul L
  have hbdu : ∀ m, ∀ y ∈ cubeDomain n, ∀ t,
      |FiniteElement.extDeriv (u m) y t| ≤ n * (4 * M₀ * L) + L := by
    intro m y hy t
    rw [hdu, Pi.add_apply, Pi.smul_apply, smul_eq_mul, wedge_apply]
    have hterm : ∀ j ∈ t, |sgn j t * grad (χ m) y j * w y (t.erase j)| ≤ 4 * M₀ * L := by
      intro j _
      have hyj : y j ∈ Ioo (0 : ℝ) (1 / 2) := hy j (mem_univ j)
      have hg : |grad (χ m) y j| ≤ |deriv (RowWise.eta m) (y j)| :=
        DeRhamIdent.abs_fderiv_chi_le (d := Fin n) m j y
      have hw' := abs_le_of_isTangentialZero hwd htan hD hy (Finset.notMem_erase j t)
      rw [abs_mul, abs_mul, show |(sgn j t : ℝ)| = 1 by simp [sgn], one_mul]
      calc |grad (χ m) y j| * |w y (t.erase j)| ≤
            |deriv (RowWise.eta m) (y j)| * (L * min (y j) (1 / 2 - y j)) :=
            mul_le_mul hg hw' (abs_nonneg _) (abs_nonneg _)
        _ = L * (|deriv (RowWise.eta m) (y j)| * min (y j) (1 / 2 - y j)) := by ring
        _ ≤ L * (4 * M₀) :=
            mul_le_mul_of_nonneg_left (RowWise.abs_deriv_eta_mul_le hM₀ m hyj) hL0
        _ = 4 * M₀ * L := by ring
    have hdw : |χ m y * FiniteElement.extDeriv w y t| ≤ L := by
      have := norm_le_pi_norm (FiniteElement.extDeriv w y) t
      rw [Real.norm_eq_abs] at this
      rw [abs_mul]
      calc |χ m y| * |FiniteElement.extDeriv w y t| ≤ 1 * L :=
            mul_le_mul (DeRhamIdent.abs_chi_le_one m y) (this.trans (hdM y (subset_closure hy)))
              (abs_nonneg _) zero_le_one
        _ = L := one_mul L
    have hcard : (t.card : ℝ) ≤ n := by exact_mod_cast (Finset.card_le_univ t).trans (by simp)
    refine (abs_add_le _ _).trans (add_le_add ?_ hdw)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  -- pointwise convergence on `Q`
  have hev : ∀ y ∈ cubeDomain n, ∀ᶠ m in atTop, u m y = w y ∧
      FiniteElement.extDeriv (u m) y = FiniteElement.extDeriv w y := by
    intro y hy
    filter_upwards [DeRhamIdent.eventually_chi_eq_one (d := Fin n) (cubeDomain_subset_Q n hy)]
      with m hm
    have h1 : χ m y = 1 := hm.eq_of_nhds
    have hg : grad (χ m) y = 0 := by
      funext j
      change fderiv ℝ (χ m) y (Pi.single j 1) = 0
      rw [hm.fderiv_eq]; simp
    refine ⟨by simp [u, h1], ?_⟩
    rw [hdu, hg, h1, wedge_zero_left, one_smul, zero_add]
  have hlim1 := tendsto_formL2_of_bdd (n := n) (k : ℤ)
    (f := fun m => (⟨u m, (hu m).continuous⟩ : contForms n)) (g := ⟨w, hw.continuous⟩)
    (fun m y hy t => hbu m y hy t) fun y hy t => tendsto_const_nhds.congr' (by
      filter_upwards [hev y hy] with m hm; exact (congrFun hm.1 t).symm)
  have hlim2 := tendsto_formL2_of_bdd (n := n) ((k : ℤ) + 1)
    (f := fun m => (⟨FiniteElement.extDeriv (u m), continuous_extDeriv (hu m)⟩ : contForms n))
    (g := ⟨FiniteElement.extDeriv w, continuous_extDeriv hw⟩)
    (fun m y hy t => hbdu m y hy t) fun y hy t => tendsto_const_nhds.congr' (by
      filter_upwards [hev y hy] with m hm; exact (congrFun hm.2 t).symm)
  have hg := (A.isClosed_minimal (isOpen_cubeDomain n)).mem_of_tendsto
    (hlim1.prodMk_nhds hlim2) (Eventually.of_forall hmem)
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hg
  have hy1' : (y : L2F ℝ (cubeDomain n) (formIdx n k)) =
      formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k ⟨w, hw.continuous⟩ :=
    hy1
  refine ⟨hy1' ▸ y.2, ?_⟩
  have e : (⟨_, hy1' ▸ y.2⟩ : (A.minimal (cubeDomain n)).domain) = y := Subtype.ext hy1'.symm
  rw [e]
  exact hy2

/-- **`IsCsFormTr` gives `H̊Λ(Q)`**: `x ∈ D(d_min)`. -/
theorem IsCsFormTr.mem_domain [NeZero n] {s : ℕ} {j : ℤ} {L : ℝ}
    {x : L2F ℝ (cubeDomain n) (formIdx n j)} (hx : IsCsFormTr s j L x) :
    x ∈ ((complexMin n).d j (j + 1)).domain := by
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, htan, hL, rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))
  obtain ⟨h, -⟩ := mem_minimal_of_isTangentialZero hw1 hdeg htan (L := L)
    (fun y hy => by simpa using (hL 0 (Nat.zero_le _) y hy).1)
    (fun y hy => by simpa [norm_iteratedFDeriv_one] using (hL 1 (by omega) y hy).1)
    (fun y hy => by simpa using (hL 0 (Nat.zero_le _) y hy).2)
  rw [deRham_minimalComplex_d]; exact h

/-- **`d_min` of an `IsCsFormTr` class is the class of `dw`.** -/
theorem IsCsFormTr.d_eq [NeZero n] {s k : ℕ} {L : ℝ} {w : FormField n}
    (hw : ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w) (hdeg : ∀ y, IsDeg k (w y))
    (hx : IsCsFormTr s k L
      (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k ⟨w, hw.continuous⟩)) :
    (complexMin n).d k (k + 1) ⟨_, hx.mem_domain⟩ =
      formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
        ⟨FiniteElement.extDeriv w, continuous_extDeriv
          (hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1)))⟩ :=
  complexMin_d_formL2 k (hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))) hdeg _ rfl

/-! ### Vanishing boundary DOFs of the canonical interpolant -/

/-- **Tangential traces on a face of the cube**: if the vertices of `g` lie in `cl Q ∩ {y_j = c}`
(`c ∈ {0, ½}`), a form with vanishing tangential components has zero tangential trace on the
simplex of `g` (the edge vectors have `j`-th coordinate `0`, so every minor of a row set containing
`j` vanishes, and the other components vanish). -/
theorem IsTangentialZero.tangentialTraceEq_zero {k : ℕ} {w : FormField n}
    (htan : IsTangentialZero w) {g : Finset (Fin n → ℝ)} {j : Fin n} {c : ℝ}
    (hc : c = 0 ∨ c = 1 / 2) (hg : ∀ v ∈ g, v ∈ closure (cubeDomain n) ∧ v j = c) :
    ∀ x ∈ convexHull ℝ (g : Set (Fin n → ℝ)), TangentialTraceEq g k (w x) 0 := by
  intro x hx V hV
  have hconv : Convex ℝ {v : Fin n → ℝ | v j = c} := by
    intro a ha b hb p q hp hq hpq
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
    rw [ha, hb, ← add_mul, hpq, one_mul]
  have hS : convexHull ℝ (g : Set (Fin n → ℝ)) ⊆ closure (cubeDomain n) ∩ {v | v j = c} :=
    convexHull_min (fun v hv => hg v hv) (convex_closure_cubeDomain.inter hconv)
  obtain ⟨hxQ, hxj⟩ := hS hx
  have hspan : vectorSpan ℝ (g : Set (Fin n → ℝ)) ≤
      LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) := by
    rw [vectorSpan_def]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    simp [(hg a ha).2, (hg b hb).2]
  have hVj : V j = 0 := funext fun l => by simpa using hspan (hV l)
  rw [pullback_zero, Pi.zero_apply, pullback_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases hjt : j ∈ t
  · rw [wedgeProd_eq_sgn_smul_wedge_erase V hjt, hVj, wedge_zero_left, smul_zero, Pi.zero_apply,
      mul_zero]
  · rw [htan x hxQ j t hjt (by rw [hxj]; exact hc), zero_mul]

/-- **A boundary facet of the cube mesh lies in a face** `{y_j = c}`, `c ∈ {0, ½}`: its barycentre
lies on `∂Q`, so some coordinate is `0` or `½` there, and then at every vertex. -/
theorem exists_face_of_isBoundaryFacet [NeZero n] {N : ℕ} {F : Finset (Fin n → ℝ)}
    (hF : (mesh n N).IsBoundaryFacet F) :
    ∃ j : Fin n, ∃ c : ℝ, (c = 0 ∨ c = 1 / 2) ∧
      ∀ v ∈ F, v ∈ closure (cubeDomain n) ∧ v j = c := by
  obtain ⟨⟨hcard, -⟩, -, hfr⟩ := hF
  have hne : F.Nonempty := Finset.card_pos.1 (by rw [hcard]; exact NeZero.pos n)
  have hfr' : convexHull ℝ (F : Set (Fin n → ℝ)) ⊆ frontier (closure (cubeDomain n)) := by
    rw [← mesh_domain n N]; exact hfr
  have hsub : frontier (closure (cubeDomain n)) ⊆ closure (cubeDomain n) :=
    isClosed_closure.frontier_subset
  have hvQ : ∀ v ∈ F, v ∈ closure (cubeDomain n) := fun v hv =>
    hsub (hfr' (subset_convexHull ℝ _ (Finset.mem_coe.2 hv)))
  set b := F.centerMass (fun _ => (1 : ℝ)) id
  have hcpos : (0 : ℝ) < ∑ _v ∈ F, (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast hne.card_pos
  have hb : b ∈ convexHull ℝ (F : Set (Fin n → ℝ)) :=
    F.centerMass_id_mem_convexHull (fun _ _ => zero_le_one) hcpos
  have hbfr := hfr' hb
  have hbQ : b ∉ cubeDomain n := fun h => hbfr.2
    (interior_maximal subset_closure (isOpen_cubeDomain n) h)
  obtain ⟨j, hj⟩ := exists_face_of_mem_closure_of_notMem (hsub hbfr) hbQ
  have hbj : b j = (∑ _v ∈ F, (1 : ℝ))⁻¹ * ∑ v ∈ F, v j := by
    simp [b, Finset.centerMass, Finset.sum_apply]
  have hcne : (∑ _v ∈ F, (1 : ℝ))⁻¹ ≠ 0 := inv_ne_zero hcpos.ne'
  have hv01 : ∀ v ∈ F, v j ∈ Icc (0 : ℝ) (1 / 2) := fun v hv =>
    mem_closure_cubeDomain.1 (hvQ v hv) j
  rcases hj with h0 | h1
  · refine ⟨j, 0, Or.inl rfl, fun v hv => ⟨hvQ v hv, ?_⟩⟩
    have hs : ∑ v ∈ F, v j = 0 := by
      rw [h0] at hbj
      exact (mul_eq_zero.1 hbj.symm).resolve_left hcne
    exact (Finset.sum_eq_zero_iff_of_nonneg fun v hv => (hv01 v hv).1).1 hs v hv
  · refine ⟨j, 1 / 2, Or.inr rfl, fun v hv => ⟨hvQ v hv, ?_⟩⟩
    have hs : ∑ v ∈ F, (1 / 2 - v j) = 0 := by
      rw [h1] at hbj
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      have hc : (∑ _v ∈ F, (1 : ℝ)) = F.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hc] at hbj hcpos
      field_simp at hbj
      linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg fun v hv =>
      (sub_nonneg.2 (hv01 v hv).2)).1 hs v hv
    linarith

/-- **The canonical DOFs of a form with vanishing tangential traces vanish on the faces of
boundary facets** (any element family: the DOFs of `g` only see the tangential trace on `g`). -/
theorem IsTangentialZero.dof_eq_zero [NeZero n] (E : LocalElement n) {N k : ℕ} {w : contForms n}
    (htan : IsTangentialZero (w : FormField n)) {F : Finset (Fin n → ℝ)}
    (hF : (mesh n N).IsBoundaryFacet F) {g : Finset (Fin n → ℝ)} (hg : g ⊆ F)
    (i : E.DofIdx g k) : E.dof g k i w = 0 := by
  obtain ⟨j, c, hc, hFj⟩ := exists_face_of_isBoundaryFacet hF
  have h0 : E.dof g k i w = E.dof g k i 0 :=
    E.dof_congr i (htan.tangentialTraceEq_zero hc fun v hv => hFj v (hg hv))
  rw [h0, map_zero]

/-- **The canonical interpolant of a form with vanishing tangential traces has vanishing boundary
DOFs**: `Π_h w ∈ Λ̊_hᵏ`. -/
theorem globalInterp_mem_globalSpace₀_of_tr [NeZero n] (E : LocalElement n) (N k : ℕ)
    {w : contForms n} (htan : IsTangentialZero (w : FormField n)) :
    (E.globalInterp (mesh n N) k w : E.Piecewise (mesh n N) k) ∈ E.globalSpace₀ (mesh n N) k := by
  refine ⟨(E.globalInterp (mesh n N) k w).2, fun T F hF hFT g hg i => ?_⟩
  rw [LocalElement.localDof_globalInterp _ _ _ _ _ _ (hg.trans hFT)]
  exact htan.dof_eq_zero E hF hg i

/-! ### Interpolation errors for vanishing tangential traces -/

section Rates

variable [NeZero n]

/-- **Interpolation error with vanishing boundary DOFs for vanishing tangential traces**: for a
`C^{s+2}` form `w` whose tangential components vanish on the faces (no condition on the normal
components), the canonical interpolant lies in `V̊ₕᵏ ⊆ H̊Λᵏ(Q)` with the estimates of
`exists_mem_poly_le`. -/
theorem exists_mem_polyMin_le_of_tr (S : PolySeq) (N k s : ℕ) (hs : polySpace n s k ≤ S.space n k)
    (hs' : polySpace n s (k + 1) ≤ S.space n (k + 1)) {w : FormField n}
    (hw : ContDiff ℝ (s + 2) w) (hdeg : ∀ x, IsDeg k (w x))
    (htan : IsTangentialZero w) {L L' : ℝ}
    (hL : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L)
    (hL' : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L') :
    ∃ v ∈ (polyMin n S N).V k,
      ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩ - v‖ ≤ polyInterpConst n S k * (meshSize N ^ (s + 1) * L) ∧
      ∃ hv : v ∈ ((complexMin n).d k (k + 1)).domain,
        ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by
              exact_mod_cast Nat.le_add_left 1 (s + 1)))⟩ -
          (complexMin n).d k (k + 1) ⟨v, hv⟩‖ ≤
            polyInterpConst n S (k + 1) * (meshSize N ^ (s + 1) * L') := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))
  have hws : ContDiff ℝ (s + 1) w := hw.of_le (by exact_mod_cast Nat.le_succ (s + 1))
  have hdw : ContDiff ℝ (s + 1) (extDeriv w) := contDiff_extDeriv (m := s + 1) (by
    exact_mod_cast hw)
  have hdw1 : ContDiff ℝ 1 (extDeriv w) := hdw.of_le (by exact_mod_cast Nat.le_add_left 1 s)
  have hdeg' : ∀ x, IsDeg (k + 1) (extDeriv w x) := fun x => IsDeg.extDeriv hdeg x
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL _ (subset_closure (center_mem_cubeDomain n)))
  have hL'0 : 0 ≤ L' := (norm_nonneg _).trans (hL' _ (subset_closure (center_mem_cubeDomain n)))
  refine (deRham ℝ n).minimalSubcomplexOfEq_induction (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    (S.subcomplexMin (mesh n N) (isOpen_mesh_domain n N) (center n) (strictStar_mesh n N))
    (fun Θ hΘ S' => ∀ hb : Bornology.IsBounded Θ,
      ∀ hvol : volume.real Θ = volume.real (cubeDomain n),
      ∃ v ∈ S'.V k,
        ‖formL2 hΘ.measurableSet hb k ⟨w, hw.continuous⟩ - asForm n v‖ ≤
          polyInterpConst n S k * (meshSize N ^ (s + 1) * L) ∧
        ∃ hv : v ∈ (((deRham ℝ n).minimalComplex hΘ).d k (k + 1)).domain,
          ‖formL2 hΘ.measurableSet hb ((k : ℤ) + 1)
              ⟨extDeriv w, continuous_extDeriv hw1⟩ -
            asForm n (((deRham ℝ n).minimalComplex hΘ).d k (k + 1) ⟨v, hv⟩)‖ ≤
            polyInterpConst n S (k + 1) * (meshSize N ^ (s + 1) * L')) ?_
    (isBounded_cubeDomain n) rfl
  intro hb hvol
  set M := mesh n N
  have hΩo := isOpen_mesh_domain n N
  set w' : c1Forms n := ⟨w, hw1⟩
  set u := (polyElement n S).globalInterp M k (Submodule.inclusion c1Forms_le_contForms w')
  have hu₀ : (u : (polyElement n S).Piecewise M k) ∈ (polyElement n S).globalSpace₀ M k :=
    globalInterp_mem_globalSpace₀_of_tr (polyElement n S) N k htan
  obtain ⟨hmem, hval⟩ := (polyElement n S).glue_mem_minimal M hΩo (center n)
    (strictStar_mesh n N) k ⟨_, hu₀⟩
  have hB1 : 0 ≤ (1 + dofConst n S k * Module.finrank ℝ (S.space n k) * coeffConst n S k) *
      (meshSize N ^ (s + 1) * L) := by
    have := dofConst_nonneg (n := n) S k; have := coeffConst_nonneg (n := n) S k
    have := (meshSize_pos N).le; positivity
  have hB2 : 0 ≤ (1 + dofConst n S (k + 1) * Module.finrank ℝ (S.space n (k + 1)) *
      coeffConst n S (k + 1)) * (meshSize N ^ (s + 1) * L') := by
    have := dofConst_nonneg (n := n) S (k + 1); have := coeffConst_nonneg (n := n) S (k + 1)
    have := (meshSize_pos N).le; positivity
  refine ⟨(polyElement n S).glue M k (u : (polyElement n S).Piecewise M k),
    ⟨⟨_, hu₀⟩, rfl⟩, ?_, ?_⟩
  · have h := norm_formL2_sub_glue_le_of_forall (polyElement n S) M hΩo.measurableSet k
      ⟨w, hw.continuous⟩ (u : (polyElement n S).Piecewise M k) hB1
      fun T x hx t _ => abs_sub_globalInterp_le_cube S hs hws hdeg hL T (interior_subset hx) t
    refine h.trans (le_of_eq ?_)
    rw [hvol, polyInterpConst]; ring
  · refine ⟨by rw [deRham_minimalComplex_d]; exact hmem, ?_⟩
    rw [LinearPMap.apply_eq_of_eq' (deRham_minimalComplex_d hΩo (k : ℤ))]
    have h := norm_formL2_sub_glue_le_of_forall (polyElement n S) M hΩo.measurableSet (k + 1)
      ⟨extDeriv w, hdw.continuous⟩ ((polyElement n S).globalInterp M (k + 1)
        ⟨extDeriv w, hdw.continuous⟩ : (polyElement n S).Piecewise M (k + 1)) hB2
      fun T x hx t _ => abs_sub_globalInterp_le_cube S hs' hdw hdeg' hL' T (interior_subset hx) t
    have h1 : (polyElement n S).dPiecewise M k (u : (polyElement n S).Piecewise M k) =
        ((polyElement n S).dGlobal M k u : (polyElement n S).Piecewise M (k + 1)) := rfl
    have e : (extDerivOp ℝ n k).minimal M.domain
        ⟨(polyElement n S).glue M k (u : (polyElement n S).Piecewise M k), hmem⟩ =
        (polyElement n S).glue M ((k + 1 : ℕ) : ℤ) ((polyElement n S).globalInterp M (k + 1)
          ⟨extDeriv w, hdw.continuous⟩ : (polyElement n S).Piecewise M (k + 1)) := by
      rw [hval]
      change (polyElement n S).glue M ((k : ℤ) + 1)
        ((polyElement n S).dPiecewise M k (u : (polyElement n S).Piecewise M k)) = _
      rw [h1, ← LocalElement.globalInterp_extDeriv]
      rfl
    erw [e]
    refine h.trans (le_of_eq ?_)
    rw [hvol, polyInterpConst]; push_cast; ring


/-- **Degreewise interpolation error of order `s + 1` with vanishing boundary DOFs** in
`H̊Λ(Q)`, for forms with vanishing tangential traces. -/
theorem IsCsFormTr.exists_mem_polyMin_le {S : PolySeq} {s : ℕ} {j : ℤ}
    (hS : PolyOrderAt n S s j)
    {L : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)} (hx : IsCsFormTr s j L x) (hL0 : 0 ≤ L)
    (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (polyMin n S N).V j,
      ‖x - v‖ ≤ polyInterpBound n S j * L * meshSize N ^ (s + 1) ∧
      ∀ j' (hxj : x ∈ ((complexMin n).d j j').domain),
        ‖(complexMin n).d j j'
            ⟨x - v, Submodule.sub_mem _ hxj ((polyMin n S N).le_domain j j' hv)⟩‖ ≤
          polyInterpBound n S j * L * meshSize N ^ (s + 1) := by
  have hh := pow_nonneg (meshSize_pos N).le (s + 1)
  have hB0 := mul_nonneg (mul_nonneg (polyInterpBound_nonneg (n := n) S j) hL0) hh
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, htan, hL, rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    refine ⟨0, Submodule.zero_mem _, ?_, fun j' hxj => ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hB0
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ :=
    exists_mem_polyMin_le_of_tr S N k s (hS k rfl).1 (hS k rfl).2 hw hdeg htan
      (fun y hy => (hL (s + 1) le_rfl y hy).1) (fun y hy => (hL (s + 1) le_rfl y hy).2)
  have hA0 := mul_nonneg (polyInterpConst_nonneg (n := n) S k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (polyInterpConst_nonneg (n := n) S (k + 1)) (mul_nonneg hh hL0)
  have e : polyInterpBound n S k * L * meshSize N ^ (s + 1) =
      polyInterpConst n S k * (meshSize N ^ (s + 1) * L) +
        polyInterpConst n S (k + 1) * (meshSize N ^ (s + 1) * L) := by
    simp only [polyInterpBound, Int.toNat_natCast]; ring
  refine ⟨v, hv, ?_, fun j' hxj => ?_⟩
  · rw [e]; linarith
  by_cases hj : (k : ℤ) + 1 = j'
  · subst hj
    have e' : (complexMin n).d k (k + 1)
        ⟨_ - v, Submodule.sub_mem _ hxj ((polyMin n S N).le_domain k (k + 1) hv)⟩ =
        (complexMin n).d k (k + 1) ⟨_, hxj⟩ - (complexMin n).d k (k + 1) ⟨v, hdv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e', complexMin_d_formL2 k (hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))) hdeg
      ⟨_, hxj⟩ rfl, e]
    linarith
  · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]
    exact hB0

/-- **Graph-norm distance of a smooth form with vanishing tangential traces to `V̊ₕʲ`**:
`dist_V(σ, V̊ₕʲ) ≤ 2 B_j L h_N^{s+1}`. -/
theorem IsCsFormTr.infDist_domainSub_polyMin_le {S : PolySeq} {s : ℕ} {j : ℤ}
    (hS : PolyOrderAt n S s j) {L : ℝ} {σ : (complexMin n).domainSpace j}
    (hσ : IsCsFormTr s j L ((complexMin n).domainIncl j σ)) (hL0 : 0 ≤ L) (N : ℕ) :
    Metric.infDist σ ((polyMin n S N).domainSub j) ≤
      2 * (polyInterpBound n S j * L * meshSize N ^ (s + 1)) := by
  obtain ⟨v, hv, h1, h2⟩ := hσ.exists_mem_polyMin_le hS hL0 N
  refine (Subcomplex.infDist_domainSub_le (S := polyMin n S N)
    (rfl : (ComplexShape.up ℤ).Rel j (j + 1)) σ hv).trans ?_
  have e : (complexMin n).d j (j + 1) ((complexMin n).domainCoord j (j + 1) σ) -
      (complexMin n).d j (j + 1) ⟨v, (polyMin n S N).le_domain j (j + 1) hv⟩ =
      (complexMin n).d j (j + 1) ⟨(complexMin n).domainIncl j σ - v,
        Submodule.sub_mem _ ((complexMin n).domainCoord j (j + 1) σ).2
          ((polyMin n S N).le_domain j (j + 1) hv)⟩ := by
    rw [← LinearPMap.map_sub]; rfl
  rw [e, two_mul]
  exact add_le_add h1 (h2 (j + 1) ((complexMin n).domainCoord j (j + 1) σ).2)


/-! ### The rates on the class `IsCsFormTr` -/

variable (n) in
/-- **The Jackson estimate of the complexes of `S` with vanishing boundary DOFs for forms with
vanishing tangential traces**: the forms of class `IsCsFormTr s` of the degrees where `S`
reproduces `P_s` at the order `h_N^{s+1}` (`IsCsFormTr.exists_mem_polyMin_le`). -/
def polyJacksonTr (S : PolySeq) : (polyFamilyMin n S).Jackson ℕ where
  meshSize := meshSize
  meshSize_nonneg N := (meshSize_pos N).le
  tendsto_meshSize := tendsto_meshSize
  Reg s j L x := PolyOrderAt n S s j ∧ IsCsFormTr s j L x
  ord s := ((s + 1 : ℕ) : ℝ)
  B _ := polyInterpBound n S
  B_nonneg _ := polyInterpBound_nonneg S
  jackson s N _ _ _ hL hx := by
    rw [Real.rpow_natCast, ← mul_assoc]; exact hx.2.exists_mem_polyMin_le hx.1 hL N

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method with vanishing traces on
the cube**, with no hypothesis beyond the regularity of the solution (components `IsCsFormTr`,
i.e. `C^{s+2}` with vanishing tangential traces on `∂Q`, no condition on the normal components). -/
theorem mixed_rate_polyTr_of_polyOrderAt (S : PolySeq) {s : ℕ} {i j k : ℤ}
    (hSi : PolyOrderAt n S s i) (hSj : PolyOrderAt n S s j) (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j},
    (complexMin n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsCsFormTr s i L ((complexMin n).domainIncl i σ) →
    IsCsFormTr s j L ((complexMin n).domainIncl j u) →
    IsCsFormTr s j L ((complexMin n).domainIncl j
      ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))) →
    IsCsFormTr s j L (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (polyMin n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).fst‖ +
        ‖u - (polyMin n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyMin n S N) hij hjk f).snd.snd :
            (polyMin n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N ^ (s + 1) := by
  obtain ⟨K, hK⟩ := ((polyFamilyMin n S).staticFEEC closedRangeAt_min j).rate
    (polyJacksonTr n S) s hij hjk
  refine ⟨K, fun hs _ hL hσ hu hb hq N => ?_⟩
  have h := hK hs hL ⟨hSi, hσ⟩ ⟨hSj, hu⟩ ⟨hSj, hb⟩ ⟨hSj, hq⟩ N
  simp only [polyFamilyMin_V] at h
  rw [← Real.rpow_natCast]
  exact h

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method with vanishing traces** for
a sequence of order `s` in every degree; see `mixed_rate_polyTr_of_polyOrderAt`. -/
theorem mixed_rate_polyTr (S : PolySeq) {s : ℕ} (hS : PolyOrder n S s) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j},
    (complexMin n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsCsFormTr s i L ((complexMin n).domainIncl i σ) →
    IsCsFormTr s j L ((complexMin n).domainIncl j u) →
    IsCsFormTr s j L ((complexMin n).domainIncl j
      ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))) →
    IsCsFormTr s j L (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (polyMin n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).fst‖ +
        ‖u - (polyMin n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyMin n S N) hij hjk f).snd.snd :
            (polyMin n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N ^ (s + 1) :=
  mixed_rate_polyTr_of_polyOrderAt S (hS.polyOrderAt i) (hS.polyOrderAt j) hij hjk

/-- **Second-order convergence of the mixed method of the bottom row of Tables 5.1/6.1 with
vanishing boundary DOFs for the Hodge Laplacian on `1`-forms** (`H̊Λ(Q)`, data with vanishing
tangential traces): error `≤ K L h_N²`. -/
theorem mixed_rate_lagrangeP2Tr :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n 1)} {σ : (complexMin n).domainSpace 0}
    {u : (complexMin n).domainSpace 1} {q : (complexMin n).harmonic 1},
    (complexMin n).IsMixedSolution 0 1 2 f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsCsFormTr 1 0 L ((complexMin n).domainIncl 0 σ) →
    IsCsFormTr 1 1 L ((complexMin n).domainIncl 1 u) →
    IsCsFormTr 1 1 L ((complexMin n).domainIncl 1
      ((complexMin n).boundaryPart 1 ((complexMin n).domainIncl 1 u))) →
    IsCsFormTr 1 1 L (q : L2F ℝ (cubeDomain n) (formIdx n 1)) → ∀ N : ℕ,
    ‖σ - (polyMin n PolySeq.lagrangeP2 N).embD 0
          (Subcomplex.CochainProjection.discreteMixedSolution
            (polyMin n PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl f).fst‖ +
        ‖u - (polyMin n PolySeq.lagrangeP2 N).embD 1
          (Subcomplex.CochainProjection.discreteMixedSolution
            (polyMin n PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n 1)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyMin n PolySeq.lagrangeP2 N)
            (i := 0) (j := 1) (k := 2) rfl rfl f).snd.snd :
            (polyMin n PolySeq.lagrangeP2 N).V 1) : L2F ℝ (cubeDomain n) (formIdx n 1))‖ ≤
      K * L * meshSize N ^ 2 :=
  mixed_rate_polyTr_of_polyOrderAt (n := n) PolySeq.lagrangeP2 lagrangeP2_polyOrderAt_zero
    lagrangeP2_polyOrderAt_one rfl rfl

/-- **Graph-norm rate in the total space of a window of `H̊Λ(Q)`** for a sequence of order `s`. -/
theorem exists_mem_windowTr_poly_le {S : PolySeq} {s : ℕ} {a : ℤ} {m : ℕ}
    (hS : ∀ i : Fin m, PolyOrderAt n S s (a + i))
    (ζ : ((complexMin n).window a m).totalD.GraphSpace) {L : ℝ} (hL0 : 0 ≤ L)
    (hζ : ∀ i : Fin m,
      IsCsFormTr s (a + i) L (((complexMin n).window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((polyMin n S N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * (∑ i : Fin m, polyInterpBound n S (a + i)) * L *
        meshSize N ^ (s + 1) := by
  obtain ⟨x, rfl, -, -⟩ := ((complexMin n).window a m).totalD.exists_toGraphSpace_eq ζ
  simp only [LinearPMap.graphFst_toGraphSpace] at hζ
  have hh := pow_nonneg (meshSize_pos N).le (s + 1)
  have hle : ∀ i : Fin m, polyInterpBound n S (a + i) * L * meshSize N ^ (s + 1) ≤
      (∑ i : Fin m, polyInterpBound n S (a + i)) * L * meshSize N ^ (s + 1) := fun i =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun i : Fin m => polyInterpBound n S (a + i))
        (fun _ _ => polyInterpBound_nonneg _ _) (Finset.mem_univ i)) hL0) hh
  obtain ⟨w, hw, hlt⟩ := Subcomplex.exists_mem_graphSub_le ((polyMin n S N).window a m) x
    (ε := (∑ i : Fin m, polyInterpBound n S (a + i)) * L * meshSize N ^ (s + 1)) fun i => by
      obtain ⟨v, hv, h1, h2⟩ := (hζ i).exists_mem_polyMin_le (hS i) hL0 N
      exact ⟨v, hv, h1.trans (hle i), fun j hx => (h2 (a + j) hx).trans (hle i)⟩
  refine ⟨w, hw, hlt.trans (le_of_eq ?_)⟩
  rw [Fintype.card_fin]; ring

/-- **Convergence of order `h^{s+1}` of the semi-discrete Hodge wave equation with vanishing
traces** for the higher-order complexes, on every window of `H̊Λ(Q)` (components with vanishing
tangential traces). -/
theorem norm_sub_le_windowTr_poly_smooth_of_polyOrderAt {S : PolySeq} {s : ℕ} {a : ℤ}
    {m : ℕ} (hS : ∀ i : Fin m, PolyOrderAt n S s (a + i)) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complexMin n).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complexMin n).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((polyMin n S N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ =
      HodgeWave.ellipticProjection (((polyMin n S N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      IsCsFormTr s (a + i) L (((complexMin n).window a m).totalD.graphFst (ξ τ) i) ∧
        IsCsFormTr s (a + i) L (((complexMin n).window a m).totalD.graphFst (ξ' τ) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complexMin n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complexMin n).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((m : ℝ) + m * m) * (∑ i : Fin m, polyInterpBound n S (a + i)) * L *
            meshSize N ^ (s + 1)) :=
  ((polyMin n S N).window a m).norm_sub_le_of_approx hξ (hξh N) (h0 N) (fun τ hτ =>
    ⟨exists_mem_windowTr_poly_le hS (ξ τ) hL0 (fun i => (hreg τ hτ i).1) N,
      exists_mem_windowTr_poly_le hS (ξ' τ) hL0 (fun i => (hreg τ hτ i).2) N⟩) ht

/-- The case of a sequence of order `s` in every degree (`PolyOrder`) of
`norm_sub_le_windowTr_poly_smooth_of_polyOrderAt`. -/
theorem norm_sub_le_windowTr_poly_smooth {S : PolySeq} {s : ℕ} (hS : PolyOrder n S s) (a : ℤ)
    (m : ℕ) {t₀ t₁ : ℝ} {ξ ξ' : ℝ → ((complexMin n).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complexMin n).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((polyMin n S N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ =
      HodgeWave.ellipticProjection (((polyMin n S N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      IsCsFormTr s (a + i) L (((complexMin n).window a m).totalD.graphFst (ξ τ) i) ∧
        IsCsFormTr s (a + i) L (((complexMin n).window a m).totalD.graphFst (ξ' τ) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complexMin n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complexMin n).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((m : ℝ) + m * m) * (∑ i : Fin m, polyInterpBound n S (a + i)) * L *
            meshSize N ^ (s + 1)) :=
  norm_sub_le_windowTr_poly_smooth_of_polyOrderAt (fun _ => hS.polyOrderAt _) hξ hξh h0 hL0
    hreg N ht

/-- **Second-order convergence of the semi-discrete Hodge wave equation for the bottom row of
Tables 5.1/6.1 with vanishing boundary DOFs** on the window `H̊Λ⁰ → H̊Λ¹ → H̊Λ²` (degrees `0, 1`
of `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ²`; [QuennevilleBelair2015], Thm 4.14): for `C³` data with vanishing
tangential traces, `‖ξ(t) - ξₕ(t)‖ ≤ A (1 + (t - t₀))² · 6 (B₀ + B₁) L h_N²`. -/
theorem norm_sub_le_windowTr_lagrangeP2 {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complexMin n).window 0 2).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complexMin n).window 0 2).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution
      (((polyMin n PolySeq.lagrangeP2 N).window 0 2).graphSub) (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ = HodgeWave.ellipticProjection
      (((polyMin n PolySeq.lagrangeP2 N).window 0 2).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin 2,
      IsCsFormTr 1 (0 + i) L (((complexMin n).window 0 2).totalD.graphFst (ξ τ) i) ∧
        IsCsFormTr 1 (0 + i) L (((complexMin n).window 0 2).totalD.graphFst (ξ' τ) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complexMin n).window 0 2).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complexMin n).window 0 2).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((2 : ℕ) + (2 : ℕ) * (2 : ℕ) : ℝ) *
            (∑ i : Fin 2, polyInterpBound n PolySeq.lagrangeP2 (0 + i)) * L * meshSize N ^ 2) :=
  norm_sub_le_windowTr_poly_smooth_of_polyOrderAt lagrangeP2_polyOrderAt_window hξ hξh h0 hL0
    hreg N ht

end Rates

end Feec.Models.Cube.FEM
