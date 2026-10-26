module

public import Feec.FiniteElement.CubeConformity
public import Feec.FiniteElement.BrambleHilbert
public import Feec.FiniteElement.InterpolationError
public import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Interpolation error of the canonical interpolants of `Q_r⁻Λᵏ`

The degrees of freedom of `Q_b⁻Λᵏ` (`Feec.FiniteElement.CubeDof`) are moments
`∫_g tr_g w ∧ η` over faces of `[0, 1]ⁿ`, defined for every form field `w` continuous on the cube
(`fieldMoment`, `fieldDof`; on polynomial forms they are the algebraic ones,
`fieldMoment_evalForm`). The canonical interpolant `Π̂ w ∈ Q_b⁻Λᵏ` (`cubeFieldInterp`)
reproduces `Q_b⁻Λᵏ ⊇ P_{r-1}Λᵏ` (`1 ≤ r ≤ b_j`) and is bounded in `C⁰`; the Bramble–Hilbert
argument with the Taylor polynomial at the centre of the cube
(`Feec.FiniteElement.norm_iteratedFDeriv_sub_taylorPoly_le`) gives the reference estimate, which
the homotheties `F_m(y) = (y + m)/N` transport to the cells (`cellInterp`): the error is
`O(hʳ)`, `h = 1/N` ([ArnoldBoffiBonizzoni2015], §4; [Ciarlet2002], Thm 3.1.4). The field degrees
of freedom are single-valued on the mesh, so the local interpolants glue into the global
canonical interpolant `Π_h w ∈ Q_b⁻Λᵏ(𝒯_h)` (`cubeFieldGlobalInterp`); as in
`Feec.FiniteElement.CubeConformity`, the coordinates are `Fin n` and the mesh is isotropic.
Integrating the
moments of `d w` by parts in one direction at a time expresses them through the moments of `w` on
the faces (`fieldDofAt_extDeriv`, `cubeT_partialDeriv`), so `Π̂` commutes with `d` on `C¹`
fields (`cubeFieldInterp_extDeriv`), and so do `Π_m` and `Π_h`, the cell pullbacks commuting
with `d` (`cubeGlue_cubeFieldGlobalInterp_extDeriv`).

## Main definitions

* `Feec.FiniteElement.Cube.planePoint`, `fieldTrace`, `fieldMoment`, `fieldDof`: traces and moments
  of form fields on the faces of the cube;
* `Feec.FiniteElement.Cube.cubeFieldInterp k hb`: the canonical interpolant on the reference cube;
* `Feec.FiniteElement.Cube.cellPullback`, `cellInterp`: the pullback to and the interpolant on the
  cell `m`;
* `Feec.FiniteElement.Cube.cubeFieldGlobalInterp k hb`: the global canonical interpolant.

## Main results

* `cubeFieldInterp_evalForm`, `cubeFieldInterp_sub`, `exists_norm_cubeFieldInterp_le`:
  reproduction of `Q_b⁻Λᵏ`, additivity and `C⁰`-stability of `Π̂`;
* `exists_norm_sub_cubeFieldInterp_le`: **`sup ‖w - Π̂ w‖ ≤ C sup ‖Dʳ w‖` on `[0, 1]ⁿ`**;
* `exists_norm_sub_cellInterp_le`: **`sup_m ‖w - Π_m w‖ ≤ C hʳ sup_m ‖Dʳ w‖` on each cell**, `C`
  independent of `h`;
* `fieldDof_cellPullback_eq_of_toGlobal_eq`, `cubeFieldGlobalInterp_mem`,
  `cellField_cubeFieldGlobalInterp`: the global interpolant is tangentially continuous (it lies
  in `Q_b⁻Λᵏ(𝒯_h) ⊆ HΛᵏ`) and is the local interpolant on each cell;
* `exists_norm_sub_cubeFieldGlobalInterp_le`: **`sup ‖w - Π_h w‖ ≤ C hʳ sup ‖Dʳ w‖` on the
  mesh**;
* `setIntegral_closedCube_partialDeriv`: the fundamental theorem of calculus on `[0, 1]ⁿ` in one
  direction;
* `cubeFieldInterp_extDeriv`: **`Π̂ (d w) = d (Π̂ w)`** for `w` of class `C¹` near `[0, 1]ⁿ`.
* `cellInterp_extDeriv`, `cubeFieldGlobalInterp_extDeriv`,
  `cubeGlue_cubeFieldGlobalInterp_extDeriv`: **`Π_h (d w) = d_max (Π_h w)`** on the mesh.

## References

* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §4 (approximation by `Q_r⁻Λᵏ` on affine cubical meshes), §3 (commuting degrees of freedom)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], Thm 3.1.4
  (interpolation error for affine-equivalent families)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.FiniteElement.Cube

open Koszul ExteriorFibre

variable {n : ℕ}

/-! ### Traces and moments of form fields -/

/-- The point of the plane `g` above `y`: the fixed coordinates replaced by their values. -/
def planePoint (g : Fin n → Option ℝ) (y : Fin n → ℝ) : Fin n → ℝ := fun j => (g j).getD (y j)

theorem continuous_planePoint (g : Fin n → Option ℝ) : Continuous (planePoint g) :=
  continuous_pi fun j => by
    unfold planePoint
    cases g j with
    | none => exact continuous_apply j
    | some c => exact continuous_const

/-- The substituted polynomial at `y` is the polynomial at the point of the plane above `y`. -/
theorem eval_faceSubst_planePoint (g : Fin n → Option ℝ) (y : Fin n → ℝ)
    (p : MvPolynomial (Fin n) ℝ) : eval y (faceSubst g p) = eval (planePoint g y) p := by
  rw [eval_faceSubst_congr (y' := planePoint g y) (fun j hj => by simp [planePoint, hj]),
    eval_faceSubst fun j c hc => by simp [planePoint, hc]]

/-- The trace of a form field on the plane `g`: the components along the free directions, at the
point of the plane. -/
def fieldTrace (g : Fin n → Option ℝ) (w : FormField n) : FormField n := fun y s =>
  if ∀ j ∈ s, (g j).isNone then w (planePoint g y) s else 0

theorem evalForm_cubeTrace (g : Fin n → Option ℝ) (ω : PolyForm ℝ (Fin n)) :
    evalForm n (cubeTrace g ω) = fieldTrace g (evalForm n ω) := by
  funext y s
  simp only [evalForm_apply, cubeTrace, fieldTrace]
  split_ifs
  · exact eval_faceSubst_planePoint g y _
  · simp

theorem continuous_fieldTrace (g : Fin n → Option ℝ) {w : FormField n} (hw : Continuous w) :
    Continuous (fieldTrace g w) :=
  continuous_pi fun s => by
    unfold fieldTrace
    split_ifs
    · exact (continuous_apply s).comp (hw.comp (continuous_planePoint g))
    · exact continuous_const

/-- The unit cube `[0, 1]ⁿ`. -/
abbrev closedCube (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi fun _ => Set.Icc 0 1

/-- The moment `∫_g tr_g w ∧ η` of a form field on the face `g`. -/
def fieldMoment (g : Fin n → Option ℝ) (η : PolyForm ℝ (Fin n)) (w : FormField n) : ℝ :=
  ∫ y in closedCube n, wedgeForm (fieldTrace g w y) (evalForm n η y) (freeSet g)

/-- On polynomial forms, the moments of fields are the moments of `Feec.FiniteElement.CubeDof`. -/
theorem fieldMoment_evalForm (g : Fin n → Option ℝ) (η ω : PolyForm ℝ (Fin n)) :
    fieldMoment g η (evalForm n ω) = cubeMoment g η ω := by
  simp only [fieldMoment, cubeMoment, LinearMap.coe_mk, AddHom.coe_mk, unitIntegral_eq_integral]
  refine MeasureTheory.setIntegral_congr_fun (by measurability) fun y _ => ?_
  rw [← evalForm_cubeTrace, ← evalForm_wedgeForm, evalForm_apply]

theorem planePoint_mem_closedCube {g : Fin n → Option ℝ}
    (hg : ∀ j c, g j = some c → c ∈ Set.Icc (0 : ℝ) 1) {y : Fin n → ℝ} (hy : y ∈ closedCube n) :
    planePoint g y ∈ closedCube n := fun j _ => by
  unfold planePoint
  cases hgj : g j with
  | none => exact hy j (Set.mem_univ j)
  | some c => exact hg j c hgj

theorem continuousOn_fieldMoment_integrand {g : Fin n → Option ℝ}
    (hg : ∀ j c, g j = some c → c ∈ Set.Icc (0 : ℝ) 1) (η : PolyForm ℝ (Fin n))
    {w : FormField n} (hw : ContinuousOn w (closedCube n)) :
    ContinuousOn (fun y => wedgeForm (fieldTrace g w y) (evalForm n η y) (freeSet g))
      (closedCube n) := by
  have htr : ContinuousOn (fieldTrace g w) (closedCube n) := continuousOn_pi.2 fun s => by
    unfold fieldTrace
    split_ifs
    · exact (continuous_apply s).comp_continuousOn (hw.comp (continuous_planePoint g).continuousOn
        fun y hy => planePoint_mem_closedCube hg hy)
    · exact continuousOn_const
  simp only [wedgeForm_apply]
  exact continuousOn_finsetSum _ fun s _ =>
    (continuousOn_const.mul ((continuous_apply s).comp_continuousOn htr)).mul
      ((continuous_apply _).comp (contDiff_evalForm η (r := 0)).continuous).continuousOn

theorem fieldMoment_sub {g : Fin n → Option ℝ}
    (hg : ∀ j c, g j = some c → c ∈ Set.Icc (0 : ℝ) 1) (η : PolyForm ℝ (Fin n))
    {w w' : FormField n} (hw : ContinuousOn w (closedCube n))
    (hw' : ContinuousOn w' (closedCube n)) :
    fieldMoment g η (w - w') = fieldMoment g η w - fieldMoment g η w' := by
  have hint : ∀ {v : FormField n}, ContinuousOn v (closedCube n) → MeasureTheory.IntegrableOn
      (fun y => wedgeForm (fieldTrace g v y) (evalForm n η y) (freeSet g)) (closedCube n) :=
    fun hv => (continuousOn_fieldMoment_integrand hg η hv).integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)
  rw [fieldMoment, fieldMoment, fieldMoment, ← MeasureTheory.integral_sub (hint hw) (hint hw')]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [fieldTrace, wedgeForm_apply, Pi.sub_apply, ← sum_sub_distrib]
  refine sum_congr rfl fun t _ => ?_
  split_ifs <;> ring

/-- The moments are bounded in `C⁰([0, 1]ⁿ)` (on faces of the cube). -/
theorem exists_abs_fieldMoment_le {g : Fin n → Option ℝ}
    (hg : ∀ j c, g j = some c → c ∈ Set.Icc (0 : ℝ) 1) (η : PolyForm ℝ (Fin n)) :
    ∃ C, ∀ (w : FormField n) (B : ℝ), (∀ y ∈ closedCube n, ‖w y‖ ≤ B) →
      |fieldMoment g η w| ≤ C * B := by
  obtain ⟨A, hA⟩ := (isCompact_univ_pi fun _ : Fin n => isCompact_Icc (a := (0 : ℝ)) (b := 1)
    ).exists_bound_of_continuousOn (contDiff_evalForm η (r := 0)).continuous.continuousOn
  refine ⟨2 ^ n * max A 0 * (MeasureTheory.volume (closedCube n)).toReal, fun w B hB => ?_⟩
  have hplane : ∀ y ∈ closedCube n, planePoint g y ∈ closedCube n :=
    fun y hy => planePoint_mem_closedCube hg hy
  have hpt : ∀ y ∈ closedCube n, |wedgeForm (fieldTrace g w y) (evalForm n η y) (freeSet g)| ≤
      2 ^ n * max A 0 * B := fun y hy => by
    have hwB : ∀ t, |fieldTrace g w y t| ≤ B := fun t => by
      unfold fieldTrace
      split_ifs
      · exact (norm_le_pi_norm (w (planePoint g y)) t).trans (hB _ (hplane y hy))
      · have := (norm_nonneg _).trans (hB y hy); simpa using this
    have hηA : ∀ t, |evalForm n η y t| ≤ max A 0 := fun t =>
      ((norm_le_pi_norm (evalForm n η y) t).trans (hA y hy)).trans (le_max_left _ _)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB y hy)
    rw [wedgeForm_apply]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s ∈ (freeSet g).powerset, |shuffleSgn s (freeSet g \ s) * fieldTrace g w y s *
            evalForm n η y (freeSet g \ s)|
        ≤ ∑ _s ∈ (freeSet g).powerset, B * max A 0 := sum_le_sum fun s _ => by
          rw [abs_mul, abs_mul, show |(shuffleSgn s (freeSet g \ s) : ℝ)| = 1 by
            rcases mul_self_eq_one_iff.1 (shuffleSgn_mul_self (R := ℝ) s (freeSet g \ s)) with
              h | h <;> simp [h]]
          rw [one_mul]
          exact mul_le_mul (hwB s) (hηA _) (abs_nonneg _) hB0
      _ ≤ 2 ^ n * max A 0 * B := by
          rw [sum_const, card_powerset, nsmul_eq_mul]
          have : (2 : ℝ) ^ #(freeSet g) ≤ 2 ^ n := by
            have := card_le_univ (freeSet g)
            rw [Fintype.card_fin] at this
            exact_mod_cast Nat.pow_le_pow_right (by norm_num) this
          push_cast
          have h2 := mul_le_mul_of_nonneg_right this (mul_nonneg hB0 (le_max_right A 0))
          linarith
  rw [fieldMoment]
  have := MeasureTheory.norm_setIntegral_le_of_norm_le_const (C := 2 ^ n * max A 0 * B)
    (μ := MeasureTheory.volume) (s := closedCube n) (f := fun y =>
      wedgeForm (fieldTrace g w y) (evalForm n η y) (freeSet g))
    (by
      rw [show closedCube n = Set.Icc (0 : Fin n → ℝ) 1 from (Set.pi_univ_Icc 0 1)]
      exact measure_Icc_lt_top)
    fun y hy => by rw [Real.norm_eq_abs]; exact hpt y hy
  rw [Real.norm_eq_abs] at this
  calc _ ≤ 2 ^ n * max A 0 * B * (MeasureTheory.volume (closedCube n)).toReal := this
    _ = _ := by ring

/-! ### The canonical interpolant on form fields -/

variable {b : Fin n → ℕ} {k : ℕ}

/-- The moment `(s, α)` of the cube on form fields. -/
def fieldDofAt (s : Finset (Fin n)) (α : Fin n →₀ ℕ) (w : FormField n) : ℝ :=
  fieldMoment (dofFace (fun _ => none) s α)
    (Pi.single (freeSet (dofFace (fun _ => none) s α) \ s) (monomial (dofTest s α) 1)) w

/-- The degree of freedom `i` of `Q_b⁻Λᵏ` on form fields. -/
def fieldDof (i : CubeDofIdx b k) (w : FormField n) : ℝ := fieldDofAt i.1.1 i.2.1 w

theorem fieldDof_evalForm (i : CubeDofIdx b k) (ω : PolyForm ℝ (Fin n)) :
    fieldDof i (evalForm n ω) = cubeDof (fun _ => none) i ω :=
  fieldMoment_evalForm _ _ _

theorem dofFace_mem_Icc (s : Finset (Fin n)) (α : Fin n →₀ ℕ) :
    ∀ j c, dofFace (fun _ => none) s α j = some c → c ∈ Set.Icc (0 : ℝ) 1 := fun j c h => by
  simp only [dofFace, Option.none_or] at h
  split_ifs at h with h1
  cases h
  push Not at h1
  exact ⟨by positivity, by exact_mod_cast (show α j ≤ 1 by omega)⟩

theorem fieldDof_sub (i : CubeDofIdx b k) {w w' : FormField n}
    (hw : ContinuousOn w (closedCube n)) (hw' : ContinuousOn w' (closedCube n)) :
    fieldDof i (w - w') = fieldDof i w - fieldDof i w' :=
  fieldMoment_sub (dofFace_mem_Icc _ _) _ hw hw'

variable (k) in
/-- **The canonical interpolant** `Π w ∈ Q_b⁻Λᵏ` of a form field continuous on `[0, 1]ⁿ`:
`ℓ_i(Π w) = ∫_g tr_g w ∧ η_i`. -/
def cubeFieldInterp (hb : ∀ j, 1 ≤ b j) (w : FormField n) : FormField n :=
  evalForm n ((isUnisolvent_cubeDof (isFaceDeg_none hb) k).equiv.symm fun i => fieldDof i w :
    PolyForm ℝ (Fin n))

/-- `Π` reproduces `Q_b⁻Λᵏ`. -/
theorem cubeFieldInterp_evalForm (hb : ∀ j, 1 ≤ b j) {ω : PolyForm ℝ (Fin n)}
    (hω : ω ∈ cubeFormMinus ℝ b k) : cubeFieldInterp k hb (evalForm n ω) = evalForm n ω := by
  have : (fun i => fieldDof i (evalForm n ω)) =
      (isUnisolvent_cubeDof (isFaceDeg_none hb) k).equiv ⟨ω, hω⟩ :=
    funext fun i => fieldDof_evalForm i ω
  rw [cubeFieldInterp, this, LinearEquiv.symm_apply_apply]

theorem cubeFieldInterp_sub (hb : ∀ j, 1 ≤ b j) {w w' : FormField n}
    (hw : ContinuousOn w (closedCube n)) (hw' : ContinuousOn w' (closedCube n)) :
    cubeFieldInterp k hb (w - w') = cubeFieldInterp k hb w - cubeFieldInterp k hb w' := by
  have : (fun i : CubeDofIdx b k => fieldDof i (w - w')) =
      (fun i => fieldDof i w) - fun i => fieldDof i w' :=
    funext fun i => fieldDof_sub i hw hw'
  simp only [cubeFieldInterp, this, map_sub, Submodule.coe_sub]

/-- **Stability of `Π` in `C⁰([0, 1]ⁿ)`**. -/
theorem exists_norm_cubeFieldInterp_le (hb : ∀ j, 1 ≤ b j) :
    ∃ C, ∀ (w : FormField n) (B : ℝ), (∀ y ∈ closedCube n, ‖w y‖ ≤ B) →
      ∀ x ∈ closedCube n, ‖cubeFieldInterp k hb w x‖ ≤ C * B := by
  set e := (isUnisolvent_cubeDof (isFaceDeg_none hb) k).equiv
  set φ : CubeDofIdx b k → FormField n := fun i =>
    evalForm n (e.symm (Pi.single i 1) : PolyForm ℝ (Fin n))
  have hC : ∀ i : CubeDofIdx b k, ∃ C, ∀ (w : FormField n) (B : ℝ),
      (∀ y ∈ closedCube n, ‖w y‖ ≤ B) → |fieldDof i w| ≤ C * B :=
    fun i => exists_abs_fieldMoment_le (dofFace_mem_Icc _ _) _
  choose C hC using hC
  have hA : ∀ i, ∃ A, ∀ x ∈ closedCube n, ‖φ i x‖ ≤ A := fun i =>
    (isCompact_univ_pi fun _ : Fin n => isCompact_Icc (a := (0 : ℝ)) (b := 1)
      ).exists_bound_of_continuousOn (contDiff_evalForm _ (r := 0)).continuous.continuousOn
  choose A hA using hA
  refine ⟨∑ i, max (C i) 0 * max (A i) 0, fun w B hB x hx => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x hx)
  have hdecomp : cubeFieldInterp k hb w x = ∑ i, fieldDof i w • φ i x := by
    have : (fun i => fieldDof i w) = ∑ i, fieldDof i w • (Pi.single i 1 : CubeDofIdx b k → ℝ) := by
      funext j; simp [Pi.single_apply]
    rw [cubeFieldInterp, this, map_sum]
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
      Finset.sum_apply, Pi.smul_apply, φ]
    rfl
  rw [hdecomp, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  calc |fieldDof i w| * ‖φ i x‖ ≤ (max (C i) 0 * B) * max (A i) 0 :=
        mul_le_mul ((hC i w B hB).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hB0))
          ((hA i x hx).trans (le_max_left _ _)) (norm_nonneg _)
          (mul_nonneg (le_max_right _ _) hB0)
    _ = max (C i) 0 * max (A i) 0 * B := by ring

/-! ### The interpolation error on the reference cube -/

/-- A polynomial function with values in the fibre `Λ(ℝⁿ)` is an evaluated polynomial form of
the same degree. -/
theorem exists_evalForm_eq_of_mem_polyFunctions {s : ℕ}
    {p : (Fin n → ℝ) → Finset (Fin n) → ℝ} (hp : p ∈ polyFunctions n s (Finset (Fin n) → ℝ)) :
    ∃ ω : PolyForm ℝ (Fin n), (∀ t, (ω t).totalDegree ≤ s) ∧ p = evalForm n ω := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, hq, c, rfl⟩ := hx
    refine ⟨fun t => C (c t) * q, fun t => (totalDegree_mul _ _).trans (by simpa using hq),
      funext fun x => funext fun t => ?_⟩
    simp [evalForm_apply, mul_comm]
  | zero => exact ⟨0, fun t => by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨ω, hω, rfl⟩ := hx
    obtain ⟨η, hη, rfl⟩ := hy
    exact ⟨ω + η, fun t => (totalDegree_add _ _).trans (max_le (hω t) (hη t)), by simp⟩
  | smul a x _ hx =>
    obtain ⟨ω, hω, rfl⟩ := hx
    exact ⟨a • ω, fun t => (totalDegree_smul_le a _).trans (hω t), by simp⟩

/-- `P_{r-1}Λᵏ ⊆ Q_b⁻Λᵏ` for `r ≤ b_j`. -/
theorem polyForm_le_cubeFormMinus {s : ℕ} (hsb : ∀ j, s + 1 ≤ b j) (k : ℕ) :
    polyForm ℝ (Fin n) s k ≤ cubeFormMinus ℝ b k := fun ω hω =>
  ⟨hω.1, fun t α hα j => by
    have := (degreeOf_le_iff.1 le_rfl α hα).trans ((degreeOf_le_totalDegree _ j).trans (hω.2 t))
    have := hsb j
    split_ifs <;> omega⟩

/-- **Interpolation error on the reference cube** (classical form): for a `C^r` `k`-form field
on a neighbourhood of `[0, 1]ⁿ` (`1 ≤ r ≤ b_j`), `sup ‖w - Π w‖ ≤ C sup ‖Dʳ w‖`, since `Π`
reproduces `P_{r-1}Λᵏ ⊆ Q_b⁻Λᵏ` and is bounded in `C⁰` (Bramble–Hilbert with the Taylor
polynomial at the centre). [ArnoldBoffiBonizzoni2015], §4 -/
theorem exists_norm_sub_cubeFieldInterp_le {r : ℕ} (hr : 1 ≤ r) (hrb : ∀ j, r ≤ b j) :
    ∃ C, ∀ (w : FormField n) (U : Set (Fin n → ℝ)), IsOpen U → closedCube n ⊆ U →
      ContDiffOn ℝ r w U → (∀ x, IsDeg k (w x)) → ∀ M : ℝ,
      (∀ y ∈ closedCube n, ‖iteratedFDeriv ℝ r w y‖ ≤ M) →
      ∀ x ∈ closedCube n, ‖w x - cubeFieldInterp k (fun j => hr.trans (hrb j)) w x‖ ≤ C * M := by
  set hb : ∀ j, 1 ≤ b j := fun j => hr.trans (hrb j)
  obtain ⟨C, hC⟩ := exists_norm_cubeFieldInterp_le (k := k) hb
  refine ⟨1 + C, fun w U hU hKU hw hk M hM x hx => ?_⟩
  set x₀ : Fin n → ℝ := fun _ => 1 / 2
  have hcube : Convex ℝ (closedCube n) := convex_pi fun _ _ => convex_Icc 0 1
  have hx₀ : x₀ ∈ closedCube n := fun _ _ => ⟨by norm_num, by norm_num⟩
  have hd : ∀ y ∈ closedCube n, ‖y - x₀‖ ≤ 1 := fun y hy =>
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
      have := hy j (Set.mem_univ j)
      simp only [Set.mem_Icc] at this
      rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
      simp only [x₀]
      constructor <;> linarith [this.1, this.2]
  -- the Taylor polynomial, as a polynomial `k`-form of `Q_b⁻Λᵏ`
  obtain ⟨ωp, hωp, hpω⟩ := exists_evalForm_eq_of_mem_polyFunctions (s := r - 1)
    (by have := taylorPoly_mem_polyFunctions w x₀ (r - 1); rwa [Nat.sub_add_cancel hr] at this)
  set ωk : PolyForm ℝ (Fin n) := fun t => if #t = k then ωp t else 0
  have hωk : ωk ∈ cubeFormMinus ℝ b k :=
    polyForm_le_cubeFormMinus (s := r - 1) (fun j => by have := hrb j; omega) k
      ⟨fun t ht => by simp [ωk, ht], fun t => by
        simp only [ωk]; split_ifs
        · exact hωp t
        · simp⟩
  set pk := evalForm n ωk
  have hpk : ContinuousOn pk (closedCube n) :=
    (contDiff_evalForm ωk (r := 0)).continuous.continuousOn
  have hwc : ContinuousOn w (closedCube n) := (hw.continuousOn).mono hKU
  -- the Taylor estimate
  have hT : ∀ y ∈ closedCube n, ‖(w - pk) y‖ ≤ M := fun y hy => by
    have h := norm_iteratedFDeriv_sub_taylorPoly_le (k := r) hU hKU hcube hx₀ hw hd hM hy
      (Nat.zero_le r)
    rw [norm_iteratedFDeriv_zero, one_pow, one_mul, hpω] at h
    refine le_trans ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun t => ?_) h
    by_cases ht : #t = k
    · have hpt : pk y t = evalForm n ωp y t := by simp [pk, ωk, evalForm_apply, ht]
      rw [Pi.sub_apply, Pi.sub_apply, hpt]
      exact norm_le_pi_norm (w y - evalForm n ωp y) t
    · rw [Pi.sub_apply, Pi.sub_apply, hk y t ht]
      simp [pk, ωk, evalForm_apply, ht]
  have hsplit : w x - cubeFieldInterp k hb w x = (w - pk) x - cubeFieldInterp k hb (w - pk) x := by
    rw [cubeFieldInterp_sub hb hwc hpk, cubeFieldInterp_evalForm hb hωk]
    simp only [Pi.sub_apply, pk]
    abel
  rw [hsplit]
  calc _ ≤ ‖(w - pk) x‖ + ‖cubeFieldInterp k hb (w - pk) x‖ := norm_sub_le _ _
    _ ≤ M + C * M := add_le_add (hT x hx) (hC _ M hT x hx)
    _ = (1 + C) * M := by ring

/-! ### The local interpolants on the cells of the mesh -/

variable {N : ℕ} [NeZero N]

/-- The pullback `ŵ = F_m^* w` of a form field to the local coordinates of the cell `m`,
`F_m(y) = (y + m) / N`. -/
def cellPullback (m : CubeCell fun _ : Fin n => N) (w : FormField n) : FormField n :=
  affinePullback (scalarMat n (N : ℝ)⁻¹) (fun i => ((m i : ℕ) : ℝ) / N) w

/-- `F_m` maps the closed unit cube onto the closed cell `m`. -/
theorem cellMap_mem_closedCell (m : CubeCell fun _ : Fin n => N) {y : Fin n → ℝ}
    (hy : y ∈ closedCube n) :
    affine (scalarMat n (N : ℝ)⁻¹) (fun i => ((m i : ℕ) : ℝ) / N) y ∈ closedCell m := fun j => by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have := hy j (Set.mem_univ j)
  simp only [Set.mem_Icc] at this
  rw [affine_scalarMat, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    show (N : ℝ) * ((N : ℝ)⁻¹ * y j + ((m j : ℕ) : ℝ) / N) = y j + (m j : ℕ) by field_simp]
  constructor <;> linarith [this.1, this.2]

theorem closedCell_subset_closedCube (m : CubeCell fun _ : Fin n => N) :
    closedCell m ⊆ closedCube n := fun y hy j _ => by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have := hy j
  have hm' : ((m j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast (m j).isLt
  constructor
  · nlinarith [this.1, (Nat.cast_nonneg (m j : ℕ) : (0 : ℝ) ≤ (m j : ℕ))]
  · nlinarith [this.2]

variable (k) in
/-- **The canonical interpolant on the cell `m`**: `Π_m w = F_m^{-*} Π̂ F_m^* w`. -/
def cellInterp (hb : ∀ j, 1 ≤ b j) (m : CubeCell fun _ : Fin n => N) (w : FormField n) :
    FormField n :=
  affinePullback (scalarMat n N) (cellOffset m) (cubeFieldInterp k hb (cellPullback m w))

theorem affinePullback_cellPullback (m : CubeCell fun _ : Fin n => N) (w : FormField n) :
    affinePullback (scalarMat n N) (cellOffset m) (cellPullback m w) = w := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  refine affinePullback_affinePullback_of_comp_eq_id _ _ _ _ (fun x => funext fun i => ?_) w
  rw [affine_scalarMat, Pi.add_apply, Pi.smul_apply, affine_cellOffset, smul_eq_mul]
  field_simp
  ring

/-- **Local interpolation error on the cells**: for a `C^r` `k`-form field near the cell `m` of
the mesh with `N` cells per direction (`1 ≤ r ≤ b_j`),
`sup_m ‖w - Π_m w‖ ≤ C hʳ sup_m ‖Dʳ w‖`, `h = 1/N`, with `C` independent of `N`, `m` and `w`.
[ArnoldBoffiBonizzoni2015], §4 -/
theorem exists_norm_sub_cellInterp_le {r : ℕ} (hr : 1 ≤ r) (hrb : ∀ j, r ≤ b j) :
    ∃ C, ∀ (N : ℕ) [NeZero N] (m : CubeCell fun _ : Fin n => N) (w : FormField n)
      (U : Set (Fin n → ℝ)), IsOpen U → closedCell m ⊆ U → ContDiffOn ℝ r w U →
      (∀ x, IsDeg k (w x)) → ∀ M : ℝ, (∀ x ∈ closedCell m, ‖iteratedFDeriv ℝ r w x‖ ≤ M) →
      ∀ x ∈ closedCell m,
        ‖w x - cellInterp k (fun j => hr.trans (hrb j)) m w x‖ ≤ C * ((N : ℝ)⁻¹) ^ r * M := by
  set hb : ∀ j, 1 ≤ b j := fun j => hr.trans (hrb j)
  obtain ⟨C, hC⟩ := exists_norm_sub_cubeFieldInterp_le (k := k) hr hrb
  refine ⟨C, fun N _ m w U hU hKU hw hk M hM x hx => ?_⟩
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hN0 : (0 : ℝ) < N := by positivity
  set h : ℝ := (N : ℝ)⁻¹
  have hh : 0 < h := inv_pos.2 hN0
  set t : Fin n → ℝ := fun i => ((m i : ℕ) : ℝ) / N
  set A := affine (scalarMat n h) t
  have hA : ∀ y, A y = h • y + t := affine_scalarMat h t
  set wh := cellPullback m w
  have hwh : ∀ y, wh y = h ^ k • w (A y) := fun y => by
    rw [hA]; exact affinePullback_scalarMat h t hk y
  -- the cell is the image of the unit cube
  have hcube : ∀ y ∈ closedCube n, A y ∈ closedCell m := fun _ hy => cellMap_mem_closedCell m hy
  have hU' : IsOpen (A ⁻¹' U) := hU.preimage (continuous_affine _ _)
  have hKU' : closedCube n ⊆ A ⁻¹' U := fun y hy => hKU (hcube y hy)
  have hcd : ContDiffOn ℝ r wh (A ⁻¹' U) := by
    have : wh = fun y => h ^ k • w (A y) := funext hwh
    rw [this]
    exact (hw.comp (contDiff_affine _ _).contDiffOn (fun y hy => hy)).const_smul _
  have hdeg : ∀ y, IsDeg k (wh y) := fun y => IsDeg.affinePullback hk _ _ y
  -- the derivatives scale like `h^{k+r}`
  have hD : ∀ y ∈ closedCube n, ‖iteratedFDeriv ℝ r wh y‖ ≤ h ^ k * h ^ r * M := fun y hy => by
    set L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
      (LinearEquiv.smulOfNeZero ℝ (Fin n → ℝ) h hh.ne').toContinuousLinearEquiv
    set Φ : (Finset (Fin n) → ℝ) ≃L[ℝ] (Finset (Fin n) → ℝ) :=
      (LinearEquiv.smulOfNeZero ℝ (Finset (Fin n) → ℝ) (h ^ k) (pow_ne_zero _ hh.ne')
        ).toContinuousLinearEquiv
    have hwh' : wh = Φ ∘ fun y => w (L y + t) := funext fun y => by
      rw [hwh, hA]; rfl
    rw [hwh', ContinuousLinearEquiv.iteratedFDeriv_comp_left, iteratedFDeriv_comp_affine]
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    have hΦ : ‖(Φ : (Finset (Fin n) → ℝ) →L[ℝ] Finset (Fin n) → ℝ)‖ ≤ h ^ k :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => by
        change ‖h ^ k • v‖ ≤ _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hL : ‖(L : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ≤ h :=
      ContinuousLinearMap.opNorm_le_bound _ hh.le fun v => by
        change ‖h • v‖ ≤ _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    have hDw : ‖(iteratedFDeriv ℝ r w (L y + t)).compContinuousLinearMap
        fun _ => (L : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ≤ h ^ r * M := by
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
      have hML := hM _ (by have := hcube y hy; rwa [hA] at this)
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hL r) hML (norm_nonneg _)
        (by positivity)
    calc _ ≤ h ^ k * (h ^ r * M) := mul_le_mul hΦ hDw (norm_nonneg _) (by positivity)
      _ = _ := by ring
  -- back to the cell
  set y := affine (scalarMat n N) (cellOffset m) x
  have hy : y ∈ closedCube n := fun j _ => by
    have := hx j
    simp only [y, affine_cellOffset]
    constructor <;> linarith [this.1, this.2]
  have hdeg' : ∀ z, IsDeg k ((wh - cubeFieldInterp k hb wh) z) := fun z s hs => by
    have h1 := hdeg z s hs
    have h2 : cubeFieldInterp k hb wh z s = 0 := by
      simp only [cubeFieldInterp, evalForm_apply]
      rw [(Subtype.prop ((isUnisolvent_cubeDof (isFaceDeg_none hb) k).equiv.symm
        fun i => fieldDof i wh)).1 s hs, map_zero]
    simp [h1, h2]
  have hsplit : w x - cellInterp k hb m w x =
      affinePullback (scalarMat n N) (cellOffset m) (wh - cubeFieldInterp k hb wh) x := by
    have e : w x = affinePullback (scalarMat n N) (cellOffset m) wh x := by
      rw [affinePullback_cellPullback]
    rw [e]
    simp only [cellInterp, affinePullback_apply, ← pullback_sub]
    rfl
  rw [hsplit, show affinePullback (scalarMat n N) (cellOffset m) (wh - cubeFieldInterp k hb wh) x
      = (N : ℝ) ^ k • (wh - cubeFieldInterp k hb wh) y by
    rw [affinePullback_apply, pullback_scalarMat _ (hdeg' _)], norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have hest := hC wh _ hU' hKU' hcd hdeg _ hD y hy
  calc (N : ℝ) ^ k * ‖(wh - cubeFieldInterp k hb wh) y‖
      ≤ (N : ℝ) ^ k * (C * (h ^ k * h ^ r * M)) := by
        gcongr
        exact hest
    _ = C * h ^ r * M := by
        rw [show (N : ℝ) ^ k * (C * (h ^ k * h ^ r * M)) = ((N : ℝ) * h) ^ k * (C * h ^ r * M) by
          ring, show (N : ℝ) * h = 1 from mul_inv_cancel₀ hN, one_pow, one_mul]

/-! ### The global canonical interpolant of a form field -/

/-- **Field degrees of freedom are single-valued**: local degrees of freedom of two cells with the
same global number take the same value on the pullbacks of a form field (they are the same
moment on the common face). -/
theorem fieldDof_cellPullback_eq_of_toGlobal_eq {m m' : CubeCell fun _ : Fin n => N}
    {i i' : CubeDofIdx b k} (h : toGlobal m i = toGlobal m' i') (w : FormField n) :
    fieldDof i (cellPullback m w) = fieldDof i' (cellPullback m' w) := by
  obtain ⟨s, α⟩ := i
  obtain ⟨s', α'⟩ := i'
  obtain rfl : s = s' := Subtype.ext (congrArg (fun A => A.1.1) h)
  have tri := toGlobal_eq_iff h
  have hnone : ∀ j, (dofFace (fun _ => none) s.1 α.1 j).isNone =
      (dofFace (fun _ => none) s.1 α'.1 j).isNone := fun j => by
    rcases tri j with ⟨-, h2⟩ | ⟨hjs, -, h2, h3⟩ | ⟨hjs, -, h2, h3⟩
    · rw [dofFace, dofFace, h2]
    · simp [dofFace, hjs, h2, h3]
    · simp [dofFace, hjs, h2, h3]
  have hfree : freeSet (dofFace (fun _ => none) s.1 α.1) =
      freeSet (dofFace (fun _ => none) s.1 α'.1) := by
    ext j; simp only [mem_freeSet, hnone j]
  have htest : dofTest s.1 α.1 = dofTest s.1 α'.1 := Finsupp.ext fun j => by
    rcases tri j with ⟨-, h2⟩ | ⟨hjs, -, h2, h3⟩ | ⟨hjs, -, h2, h3⟩
    · simp [dofTest, h2]
    · simp [dofTest, hjs, h2, h3]
    · simp [dofTest, hjs, h2, h3]
  -- the traces agree: the points of the two faces are the same points of the mesh
  have hpt : ∀ y, (fun i => ((m i : ℕ) : ℝ) / N) +
        (N : ℝ)⁻¹ • planePoint (dofFace (fun _ => none) s.1 α.1) y =
      (fun i => ((m' i : ℕ) : ℝ) / N) +
        (N : ℝ)⁻¹ • planePoint (dofFace (fun _ => none) s.1 α'.1) y := fun y => funext fun j => by
    have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, planePoint]
    rcases tri j with ⟨h1, h2⟩ | ⟨hjs, h1, h2, h3⟩ | ⟨hjs, h1, h2, h3⟩
    · rw [h1, dofFace, dofFace, h2]
    · simp only [dofFace, hjs, h2, h3, Option.none_or, false_or]
      norm_num
      have : ((m' j : ℕ) : ℝ) = (m j : ℕ) + 1 := by exact_mod_cast h1
      rw [this]; field_simp
    · simp only [dofFace, hjs, h2, h3, Option.none_or, false_or]
      norm_num
      have : ((m j : ℕ) : ℝ) = (m' j : ℕ) + 1 := by exact_mod_cast h1
      rw [this]; field_simp
  have htr : ∀ y, fieldTrace (dofFace (fun _ => none) s.1 α.1) (cellPullback m w) y =
      fieldTrace (dofFace (fun _ => none) s.1 α'.1) (cellPullback m' w) y := fun y => by
    funext t
    simp only [fieldTrace, hnone, cellPullback, affinePullback_apply, affine_scalarMat]
    rw [add_comm, hpt y, add_comm]
  simp only [fieldDof, fieldDofAt, fieldMoment, hfree, htest, htr]

variable (k) in
/-- **The global canonical interpolant of a form field**: the global degrees of freedom of `w`,
read in the cells, glued into `Q_b⁻Λᵏ(𝒯_h)`. -/
def cubeFieldGlobalInterp (hb : ∀ j, 1 ≤ b j) (w : FormField n) :
    CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n) :=
  ofGlobalDof (k := k) hb fun A => fieldDof (globalLocal
    (fun _ => Nat.one_le_iff_ne_zero.2 (NeZero.ne N)) hb A)
    (cellPullback (globalCell (fun _ => Nat.one_le_iff_ne_zero.2 (NeZero.ne N)) A) w)

/-- `Π_h w` is tangentially continuous: it lies in `Q_b⁻Λᵏ(𝒯_h)` (hence in `HΛᵏ`). -/
theorem cubeFieldGlobalInterp_mem (hb : ∀ j, 1 ≤ b j) (w : FormField n) :
    cubeFieldGlobalInterp (N := N) k hb w ∈ cubeGlobalSpace (fun _ : Fin n => N) b k :=
  ofGlobalDof_mem hb _

/-- On each cell, `Π_h w` is the local canonical interpolant. -/
theorem cellField_cubeFieldGlobalInterp (hb : ∀ j, 1 ≤ b j) (w : FormField n)
    (m : CubeCell fun _ : Fin n => N) :
    cellField (cubeFieldGlobalInterp k hb w) m = cellInterp k hb m w := by
  have hN : ∀ j : Fin n, 1 ≤ (fun _ => N) j := fun _ => Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  set e := (isUnisolvent_cubeDof (isFaceDeg_none hb) k).equiv
  have hloc : (⟨cubeFieldGlobalInterp k hb w m, Subtype.prop _⟩ : cubeFormMinus ℝ b k) =
      e.symm fun i => fieldDof i (cellPullback m w) := by
    refine (isUnisolvent_cubeDof (isFaceDeg_none hb) k).ext fun i => ?_
    change cubeDof (fun _ => none) i (ofGlobalDof hb _ m) = cubeDof (fun _ => none) i
      (e.symm fun i => fieldDof i (cellPullback m w) : PolyForm ℝ (Fin n))
    rw [cubeDof_ofGlobalDof, fieldDof_cellPullback_eq_of_toGlobal_eq
      (toGlobal_globalLocal hN hb (toGlobal m i))]
    exact ((isUnisolvent_cubeDof (isFaceDeg_none hb) k).dof_equiv_symm
      (fun i => fieldDof i (cellPullback m w)) i).symm
  simp only [cellField, cellInterp, cubeFieldInterp]
  rw [← hloc]

/-- **Interpolation error of the global interpolant**: on the mesh with `N` cells per direction,
`sup_{[0,1]ⁿ} ‖w - Π_h w‖ ≤ C hʳ sup_{[0,1]ⁿ} ‖Dʳ w‖`, `h = 1/N`, for `C^r` `k`-form fields near the
closed unit cube (`1 ≤ r ≤ b_j`), with `C` independent of `N` and `w`: the cell fields of
`Π_h w ∈ Q_b⁻Λᵏ(𝒯_h) ⊆ HΛᵏ` approximate `w` on each cell. [ArnoldBoffiBonizzoni2015], §4 -/
theorem exists_norm_sub_cubeFieldGlobalInterp_le {r : ℕ} (hr : 1 ≤ r) (hrb : ∀ j, r ≤ b j) :
    ∃ C, ∀ (N : ℕ) [NeZero N] (w : FormField n) (U : Set (Fin n → ℝ)), IsOpen U →
      closedCube n ⊆ U → ContDiffOn ℝ r w U → (∀ x, IsDeg k (w x)) → ∀ M : ℝ,
      (∀ x ∈ closedCube n, ‖iteratedFDeriv ℝ r w x‖ ≤ M) →
      ∀ (m : CubeCell fun _ : Fin n => N), ∀ x ∈ closedCell m,
        ‖w x - cellField (cubeFieldGlobalInterp k (fun j => hr.trans (hrb j)) w) m x‖ ≤
          C * ((N : ℝ)⁻¹) ^ r * M := by
  obtain ⟨C, hC⟩ := exists_norm_sub_cellInterp_le (k := k) hr hrb
  refine ⟨C, fun N _ w U hU hKU hw hk M hM m x hx => ?_⟩
  have hcell := closedCell_subset_closedCube m
  rw [cellField_cubeFieldGlobalInterp]
  exact hC N m w U hU (hcell.trans hKU) hw hk M (fun y hy => hM y (hcell hy)) x hx

/-! ### Integration by parts on the unit cube -/

section Slices

theorem continuousOn_partialDeriv {f : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (j : Fin n) : ContinuousOn (partialDeriv j f) U := by
  have := (ContinuousLinearMap.apply ℝ ℝ (Pi.single j (1 : ℝ))).continuous.comp_continuousOn
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl)
  exact this

theorem update_mem_closedCube {x : Fin n → ℝ} (hx : x ∈ closedCube n) (j : Fin n) {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) : Function.update x j c ∈ closedCube n := fun i _ => by
  by_cases hi : i = j
  · subst hi; simpa using hc
  · rw [Function.update_of_ne hi]; exact hx i (Set.mem_univ i)

variable {m : ℕ}

theorem insertNth_mem_closedCube_iff (j : Fin (m + 1)) (t : ℝ) (y : Fin m → ℝ) :
    Fin.insertNth j t y ∈ closedCube (m + 1) ↔ t ∈ Set.Icc 0 1 ∧ y ∈ closedCube m := by
  simp only [closedCube, Set.mem_pi, Set.mem_univ, true_implies]
  rw [Fin.forall_iff_succAbove j, Fin.insertNth_apply_same]
  simp only [Fin.insertNth_apply_succAbove]

/-- **Fubini on the unit cube**, slicing along the coordinate `j`. -/
theorem setIntegral_closedCube_succ (j : Fin (m + 1)) {g : (Fin (m + 1) → ℝ) → ℝ}
    (hg : MeasureTheory.IntegrableOn g (closedCube (m + 1))) :
    ∫ x in closedCube (m + 1), g x =
      ∫ y in closedCube m, ∫ t in (0 : ℝ)..1, g (Fin.insertNth j t y) := by
  have hmeas : ∀ k, MeasurableSet (closedCube k) := fun k =>
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j
  have he : MeasureTheory.MeasurePreserving e.symm :=
    (MeasureTheory.volume_preserving_piFinSuccAbove _ j).symm e
  have hes : ∀ z : ℝ × (Fin m → ℝ), e.symm z = Fin.insertNth j z.1 z.2 := fun z => rfl
  set G := (closedCube (m + 1)).indicator g
  have hG : MeasureTheory.Integrable G :=
    (MeasureTheory.integrable_indicator_iff (hmeas _)).2 hg
  have hGe : MeasureTheory.Integrable (fun z => G (e.symm z))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    rw [← MeasureTheory.Measure.volume_eq_prod]
    exact (he.integrable_comp_emb e.symm.measurableEmbedding).2 hG
  rw [← MeasureTheory.integral_indicator (hmeas _), ← he.integral_comp' G,
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hGe,
    ← MeasureTheory.integral_indicator (hmeas _)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hes, G]
  by_cases hy : y ∈ closedCube m
  · rw [Set.indicator_of_mem hy]
    have : (fun t => (closedCube (m + 1)).indicator g (Fin.insertNth j t y)) =
        (Set.Icc (0 : ℝ) 1).indicator fun t => g (Fin.insertNth j t y) := by
      funext t
      by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem
          ((insertNth_mem_closedCube_iff j t y).2 ⟨ht, hy⟩)]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem
          (fun h => ht ((insertNth_mem_closedCube_iff j t y).1 h).1)]
    rw [this, MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]
  · rw [Set.indicator_of_notMem hy]
    refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
    exact Set.indicator_of_notMem (fun h => hy ((insertNth_mem_closedCube_iff j t y).1 h).2) _

/-- **The fundamental theorem of calculus on the unit cube**:
`∫_{[0,1]ⁿ} ∂ⱼ Φ = ∫_{[0,1]ⁿ} (Φ|_{x_j = 1} - Φ|_{x_j = 0})`. -/
theorem setIntegral_closedCube_partialDeriv (j : Fin (m + 1)) {Φ : (Fin (m + 1) → ℝ) → ℝ}
    {U : Set (Fin (m + 1) → ℝ)} (hU : IsOpen U) (hKU : closedCube (m + 1) ⊆ U)
    (hΦ : ContDiffOn ℝ 1 Φ U) :
    ∫ x in closedCube (m + 1), partialDeriv j Φ x =
      ∫ x in closedCube (m + 1), (Φ (Function.update x j 1) - Φ (Function.update x j 0)) := by
  have hcpt : IsCompact (closedCube (m + 1)) := isCompact_univ_pi fun _ => isCompact_Icc
  have hd := continuousOn_partialDeriv hU hΦ j
  have hupd : ∀ c ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun x => Φ (Function.update x j c)) (closedCube (m + 1)) := fun c hc =>
    hΦ.continuousOn.comp (continuous_id.update j continuous_const).continuousOn
      fun x hx => hKU (update_mem_closedCube hx j hc)
  rw [setIntegral_closedCube_succ j ((hd.mono hKU).integrableOn_compact hcpt),
    setIntegral_closedCube_succ j
      (g := fun x => Φ (Function.update x j 1) - Φ (Function.update x j 0))
      (((hupd 1 ⟨zero_le_one, le_rfl⟩).sub (hupd 0 ⟨le_rfl, zero_le_one⟩)).integrableOn_compact
        hcpt)]
  refine MeasureTheory.setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
    fun y hy => ?_
  simp only [Fin.update_insertNth]
  rw [intervalIntegral.integral_const, sub_zero, one_smul]
  have hfun : (fun t : ℝ => (Fin.insertNth j t y : Fin (m + 1) → ℝ)) =
      fun t => Function.update (Fin.insertNth j (0 : ℝ) y : Fin (m + 1) → ℝ) j t :=
    funext fun t => by rw [Fin.update_insertNth]
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, Fin.insertNth j t y ∈ U := fun t ht =>
    hKU ((insertNth_mem_closedCube_iff j t y).2 ⟨ht, hy⟩)
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => Φ (Fin.insertNth j t y)) (fun t ht => ?_) ?_
  · rw [Set.uIcc_of_le zero_le_one] at ht
    have hF : HasFDerivAt Φ (fderiv ℝ Φ (Fin.insertNth j t y)) (Fin.insertNth j t y) :=
      (((hΦ.differentiableOn one_ne_zero) _ (hmem t ht)).differentiableAt
        (hU.mem_nhds (hmem t ht))).hasFDerivAt
    have hg : HasDerivAt (fun t => (Fin.insertNth j t y : Fin (m + 1) → ℝ)) (Pi.single j 1) t := by
      rw [hfun]
      exact hasDerivAt_update _ j t
    exact hF.comp_hasDerivAt t hg
  · refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
    refine hd.comp ?_ fun t ht => hmem t ht
    rw [hfun]
    exact fun t _ => (hasDerivAt_update _ j t).continuousAt.continuousWithinAt

end Slices

/-! ### The commuting property on smooth form fields -/

section Commuting

/-- The scalar moment `f ↦ ∫_{[0,1]ⁿ} f(P y) y^β` of the degree of freedom `(s, α)`, `P` the
point of its face, `β = dofTest s α`. -/
def cubeT (s : Finset (Fin n)) (α : Fin n →₀ ℕ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ y in closedCube n, f (planePoint (dofFace (fun _ => none) s α) y) *
    eval y (monomial (dofTest s α) 1)

theorem subset_freeSet_dofFace (s : Finset (Fin n)) (α : Fin n →₀ ℕ) :
    s ⊆ freeSet (dofFace (fun _ => none) s α) := fun j hj => by simp [dofFace, hj]

/-- **The field moments are tensor products**: `ℓ_{s,α}(w) = ± ∫_{[0,1]ⁿ} w_s(P y) y^β`. -/
theorem fieldDofAt_apply (s : Finset (Fin n)) (α : Fin n →₀ ℕ) (w : FormField n) :
    fieldDofAt s α w =
      shuffleSgn s (freeSet (dofFace (fun _ => none) s α) \ s) * cubeT s α (fun z => w z s) := by
  have hsub := subset_freeSet_dofFace s α
  rw [fieldDofAt, fieldMoment, cubeT, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [wedgeForm_apply, sum_eq_single s (fun u hu hus => by
      rw [evalForm_apply, Pi.single_eq_of_ne (fun h => hus ?_), map_zero, mul_zero]
      rw [← Finset.sdiff_sdiff_eq_self (mem_powerset.1 hu), h, Finset.sdiff_sdiff_eq_self hsub])
    (fun h => absurd (mem_powerset.2 hsub) h), evalForm_apply, Pi.single_eq_same, fieldTrace,
    ite_eq_left fun j hj => by simpa using hsub hj]
  ring

/-- The linear part of `planePoint g`: keep the free coordinates, kill the fixed ones. -/
def planeProj (g : Fin n → Option ℝ) : (Fin n → ℝ) →L[ℝ] Fin n → ℝ :=
  ContinuousLinearMap.pi fun i =>
    if (g i).isNone then (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) else 0

theorem planePoint_eq (g : Fin n → Option ℝ) :
    planePoint g = fun z => planeProj g z + fun i => (g i).getD 0 :=
  funext fun z => funext fun i => by
    simp only [planePoint, planeProj, Pi.add_apply, ContinuousLinearMap.pi_apply]
    cases g i <;> simp

theorem contDiff_planePoint (g : Fin n → Option ℝ) {r : WithTop ℕ∞} :
    ContDiff ℝ r (planePoint g) := by
  rw [planePoint_eq]; exact (planeProj g).contDiff.add contDiff_const

theorem hasFDerivAt_planePoint (g : Fin n → Option ℝ) (y : Fin n → ℝ) :
    HasFDerivAt (planePoint g) (planeProj g) y := by
  rw [planePoint_eq]; exact (planeProj g).hasFDerivAt.add_const _

theorem integrableOn_cubeT (s : Finset (Fin n)) (α : Fin n →₀ ℕ) {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (closedCube n)) :
    MeasureTheory.IntegrableOn (fun y => f (planePoint (dofFace (fun _ => none) s α) y) *
      eval y (monomial (dofTest s α) 1)) (closedCube n) :=
  ((hf.comp (continuous_planePoint _).continuousOn fun _ hy =>
      planePoint_mem_closedCube (dofFace_mem_Icc s α) hy).mul
    (MvPolynomial.continuous_eval _).continuousOn).integrableOn_compact
    (isCompact_univ_pi fun _ => isCompact_Icc)

/-- **One-dimensional integration by parts in the moments**:
`T_{s,α}(∂ⱼ f) = T_{s∖j,α[j↦1]}(f) - 0^{α_j} T_{s∖j,α[j↦0]}(f) - α_j T_{s∖j,α[j↦α_j+1]}(f)`
for `j ∈ s` and `f` of class `C¹` near `[0, 1]ⁿ`. -/
theorem cubeT_partialDeriv {s : Finset (Fin n)} {α : Fin n →₀ ℕ} {j : Fin n} (hj : j ∈ s)
    {f : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hKU : closedCube n ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) :
    cubeT s α (partialDeriv j f) = cubeT (s.erase j) (α.update j 1) f -
      0 ^ α j * cubeT (s.erase j) (α.update j 0) f -
        (α j : ℝ) * cubeT (s.erase j) (α.update j (α j + 1)) f := by
  set g := dofFace (fun _ => none) s α
  set P := planePoint g
  set β := dofTest s α
  set μ : (Fin n → ℝ) → ℝ := fun y => eval y (monomial β 1)
  have hgj : g j = none := by simp [g, dofFace, hj]
  have hβj : β j = α j := by simp [β, dofTest, hj]
  have hPc : ∀ y ∈ closedCube n, P y ∈ closedCube n := fun y hy =>
    planePoint_mem_closedCube (dofFace_mem_Icc s α) hy
  -- the faces and the test monomials of the three moments of `s ∖ j`
  have hface1 : dofFace (fun _ => none) (s.erase j) (α.update j 1) =
      Function.update g j (some 1) := funext fun i => by
    by_cases hi : i = j
    · subst hi; simp [dofFace]
    · simp [g, dofFace, hi, Finsupp.update_apply]
  have hface0 : dofFace (fun _ => none) (s.erase j) (α.update j 0) =
      Function.update g j (some 0) := funext fun i => by
    by_cases hi : i = j
    · subst hi; simp [dofFace]
    · simp [g, dofFace, hi, Finsupp.update_apply]
  have hface2 : 1 ≤ α j → dofFace (fun _ => none) (s.erase j) (α.update j (α j + 1)) = g :=
    fun h1 => funext fun i => by
      by_cases hi : i = j
      · subst hi; simp [g, dofFace, hj, show 2 ≤ α i + 1 by omega]
      · simp [g, dofFace, hi, Finsupp.update_apply]
  have hP1 : ∀ y, planePoint (Function.update g j (some 1)) y = P (Function.update y j 1) :=
    fun y => funext fun i => by
      by_cases hi : i = j
      · subst hi; simp [P, planePoint, hgj]
      · simp [P, planePoint, hi]
  have hP0 : ∀ y, planePoint (Function.update g j (some 0)) y = P (Function.update y j 0) :=
    fun y => funext fun i => by
      by_cases hi : i = j
      · subst hi; simp [P, planePoint, hgj]
      · simp [P, planePoint, hi]
  -- the test monomials of the three moments of `s ∖ j`
  have htest : ∀ c : ℕ, ∀ i ≠ j, dofTest (s.erase j) (α.update j c) i = β i := fun c i hi => by
    simp [β, dofTest, hi, Finsupp.update_apply]
  have hμc : ∀ (c : ℝ) (e : ℕ), dofTest (s.erase j) (α.update j e) j = 0 → ∀ y,
      μ (Function.update y j c) =
        c ^ α j * eval y (monomial (dofTest (s.erase j) (α.update j e)) 1) :=
    fun c e he y => by
      simp only [μ, eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      rw [Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j, he, pow_zero, one_mul,
        Function.update_self, hβj]
      congr 1
      refine prod_congr rfl fun i hi => ?_
      have hij : i ≠ j := by simpa using hi
      rw [Function.update_of_ne hij, htest e i hij]
  have hμ1 := hμc 1 1 (by simp [dofTest])
  have hμ0 := hμc 0 0 (by simp [dofTest])
  have hβ2 : dofTest (s.erase j) (α.update j (α j + 1)) = β - Finsupp.single j 1 :=
    Finsupp.ext fun i => by
      by_cases hi : i = j
      · subst hi; simp [dofTest, hβj]
      · rw [htest _ i hi]; simp [Ne.symm hi]
  have hdμ : ∀ y, partialDeriv j μ y =
      α j * eval y (monomial (dofTest (s.erase j) (α.update j (α j + 1))) 1) := fun y => by
    rw [partialDeriv_eval, pderiv_monomial, hβ2, hβj, eval_monomial, eval_monomial]
    ring
  -- the integration by parts
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := j.pos; omega⟩
  set V := P ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_planePoint g)
  have hKV : closedCube (m + 1) ⊆ V := fun y hy => hKU (hPc y hy)
  have hfP : ContDiffOn ℝ 1 (fun y => f (P y)) V :=
    hf.comp (contDiff_planePoint g).contDiffOn fun y hy => hy
  have hμd : ContDiff ℝ 1 μ := contDiff_eval _
  set Φ : (Fin (m + 1) → ℝ) → ℝ := fun y => f (P y) * μ y
  have hΦ : ContDiffOn ℝ 1 Φ V := hfP.mul hμd.contDiffOn
  have hdΦ : ∀ y ∈ V, partialDeriv j Φ y =
      partialDeriv j f (P y) * μ y + f (P y) * partialDeriv j μ y := fun y hy => by
    have hfd : DifferentiableAt ℝ (fun y => f (P y)) y :=
      (hfP.differentiableOn one_ne_zero y hy).differentiableAt (hV.mem_nhds hy)
    rw [partialDeriv_mul hfd (hμd.differentiable one_ne_zero y)]
    congr 2
    have hfa : HasFDerivAt f (fderiv ℝ f (P y)) (P y) :=
      ((hf.differentiableOn one_ne_zero _ hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
    rw [show (fun y => f (P y)) = f ∘ P from rfl,
      (hfa.comp y (hasFDerivAt_planePoint g y)).partialDeriv_eq]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    congr 1
    funext i
    by_cases hi : i = j
    · subst hi; simp [planeProj, hgj]
    · simp only [planeProj, ContinuousLinearMap.pi_apply]
      split_ifs <;> simp [hi]
  -- continuity of the integrands
  have hcpt : IsCompact (closedCube (m + 1)) := isCompact_univ_pi fun _ => isCompact_Icc
  have hfc : ContinuousOn (fun y => f (P y)) (closedCube (m + 1)) := hfP.continuousOn.mono hKV
  have hdfc : ContinuousOn (fun y => partialDeriv j f (P y)) (closedCube (m + 1)) :=
    (continuousOn_partialDeriv hU hf j).comp (continuous_planePoint g).continuousOn
      fun y hy => hKV hy
  have hμc : Continuous μ := hμd.continuous
  have hdμc : Continuous (partialDeriv j μ) := by
    have : partialDeriv j μ = fun y : Fin (m + 1) → ℝ =>
        (α j : ℝ) * eval y (monomial (dofTest (s.erase j) (α.update j (α j + 1))) 1) := funext hdμ
    rw [this]; exact continuous_const.mul (MvPolynomial.continuous_eval _)
  have hint1 : MeasureTheory.IntegrableOn (fun y => partialDeriv j Φ y) (closedCube (m + 1)) :=
    ((hdfc.mul hμc.continuousOn).add (hfc.mul hdμc.continuousOn)).integrableOn_compact hcpt
      |>.congr_fun (fun y hy => (hdΦ y (hKV hy)).symm) (MeasurableSet.univ_pi fun _ =>
        measurableSet_Icc)
  have hint2 : MeasureTheory.IntegrableOn (fun y => f (P y) * partialDeriv j μ y)
      (closedCube (m + 1)) := (hfc.mul hdμc.continuousOn).integrableOn_compact hcpt
  have hintu : ∀ c ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.IntegrableOn (fun y => Φ (Function.update y j c)) (closedCube (m + 1)) :=
    fun c hc => (hΦ.continuousOn.comp (continuous_id.update j continuous_const).continuousOn
      fun y hy => hKV (update_mem_closedCube hy j hc)).integrableOn_compact hcpt
  have hmeas : MeasurableSet (closedCube (m + 1)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  calc cubeT s α (partialDeriv j f)
      = ∫ y in closedCube (m + 1), (partialDeriv j Φ y - f (P y) * partialDeriv j μ y) :=
        MeasureTheory.setIntegral_congr_fun hmeas fun y hy => by
          rw [hdΦ y (hKV hy)]; ring
    _ = (∫ y in closedCube (m + 1), Φ (Function.update y j 1)) -
          (∫ y in closedCube (m + 1), Φ (Function.update y j 0)) -
          ∫ y in closedCube (m + 1), f (P y) * partialDeriv j μ y := by
        rw [MeasureTheory.integral_sub hint1 hint2, setIntegral_closedCube_partialDeriv j hV hKV hΦ,
          MeasureTheory.integral_sub (hintu 1 ⟨zero_le_one, le_rfl⟩)
            (hintu 0 ⟨le_rfl, zero_le_one⟩)]
    _ = _ := by
        congr 1
        · congr 1
          · simp only [cubeT, Φ, hface1, hP1, hμ1, one_pow, one_mul]
          · simp only [cubeT, Φ, hface0, hP0, hμ0]
            rw [← MeasureTheory.integral_const_mul]
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            simp only; ring
        · simp only [cubeT, hdμ]
          rcases Nat.eq_zero_or_pos (α j) with h0 | h1
          · simp [h0]
          · rw [hface2 h1, ← MeasureTheory.integral_const_mul]
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            simp only [P]; ring

theorem cubeT_eq_fieldDofAt (s : Finset (Fin n)) (α : Fin n →₀ ℕ) (w : FormField n) :
    cubeT s α (fun z => w z s) =
      shuffleSgn s (freeSet (dofFace (fun _ => none) s α) \ s) * fieldDofAt s α w := by
  rw [fieldDofAt_apply, ← mul_assoc, shuffleSgn_mul_self, one_mul]

/-- **The moments of `d w`**: `ℓ_{s,α}(d w) = ± Σ_{j ∈ s} ε(j, s) T_{s,α}(∂ⱼ w_{s∖j})`, each
term integrated by parts in the direction `j` (`Feec.FiniteElement.Cube.cubeT_partialDeriv`). -/
theorem fieldDofAt_extDeriv (s : Finset (Fin n)) (α : Fin n →₀ ℕ) {w : FormField n}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hKU : closedCube n ⊆ U) (hw : ContDiffOn ℝ 1 w U) :
    fieldDofAt s α (extDeriv w) = shuffleSgn s (freeSet (dofFace (fun _ => none) s α) \ s) *
      ∑ j ∈ s, sgn j s * (cubeT (s.erase j) (α.update j 1) (fun z => w z (s.erase j)) -
        0 ^ α j * cubeT (s.erase j) (α.update j 0) (fun z => w z (s.erase j)) -
          (α j : ℝ) * cubeT (s.erase j) (α.update j (α j + 1)) (fun z => w z (s.erase j))) := by
  have hc : ∀ t, ContDiffOn ℝ 1 (fun z => w z t) U := contDiffOn_pi.1 hw
  have hsum : cubeT s α (fun z => extDeriv w z s) =
      ∑ j ∈ s, sgn j s * cubeT s α (partialDeriv j fun y => w y (s.erase j)) := by
    simp only [cubeT, extDeriv_apply, Finset.sum_mul, mul_assoc]
    rw [MeasureTheory.integral_finsetSum _ fun j _ =>
      (integrableOn_cubeT s α ((continuousOn_partialDeriv hU (hc _) j).mono hKU)).const_mul _]
    simp only [MeasureTheory.integral_const_mul]
  rw [fieldDofAt_apply, hsum]
  congr 1
  exact sum_congr rfl fun j hj => by rw [cubeT_partialDeriv hj hU hKU (hc _)]

variable {b : Fin n → ℕ} {k : ℕ}

theorem fieldDof_cubeFieldInterp (hb : ∀ j, 1 ≤ b j) (i : CubeDofIdx b k) (w : FormField n) :
    fieldDof i (cubeFieldInterp k hb w) = fieldDof i w := by
  rw [cubeFieldInterp, fieldDof_evalForm]
  exact congrFun ((isUnisolvent_cubeDof (isFaceDeg_none hb) k).equiv.apply_symm_apply _) i

theorem cubeFieldInterp_congr (hb : ∀ j, 1 ≤ b j) {w w' : FormField n}
    (h : ∀ i : CubeDofIdx b k, fieldDof i w = fieldDof i w') :
    cubeFieldInterp k hb w = cubeFieldInterp k hb w' := by
  rw [cubeFieldInterp, cubeFieldInterp, funext h]

theorem cubeT_cubeFieldInterp (hb : ∀ j, 1 ≤ b j) {t : Finset (Fin n)} {β : Fin n →₀ ℕ}
    (ht : #t = k) (hβ : β ∈ cubeSupport b t) (w : FormField n) :
    cubeT t β (fun z => cubeFieldInterp k hb w z t) = cubeT t β (fun z => w z t) := by
  rw [cubeT_eq_fieldDofAt, cubeT_eq_fieldDofAt]
  exact congrArg _ (fieldDof_cubeFieldInterp hb ⟨⟨t, ht⟩, ⟨β, hβ⟩⟩ w)

/-- **The canonical interpolant commutes with `d`** on fields of class `C¹` near `[0, 1]ⁿ`:
`Π(d w) = d(Π w)` ([ArnoldBoffiBonizzoni2015], §3). -/
theorem cubeFieldInterp_extDeriv (hb : ∀ j, 1 ≤ b j) {w : FormField n} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hKU : closedCube n ⊆ U) (hw : ContDiffOn ℝ 1 w U) :
    cubeFieldInterp (k + 1) hb (extDeriv w) = extDeriv (cubeFieldInterp k hb w) := by
  have hω := ((isUnisolvent_cubeDof (isFaceDeg_none hb) k).equiv.symm fun i => fieldDof i w).2
  have hdI : extDeriv (cubeFieldInterp k hb w) =
      cubeFieldInterp (k + 1) hb (extDeriv (cubeFieldInterp k hb w)) := by
    rw [cubeFieldInterp, extDeriv_evalForm,
      cubeFieldInterp_evalForm hb (extDeriv_mem_cubeFormMinus hω)]
  rw [hdI]
  refine cubeFieldInterp_congr hb fun ⟨⟨s, hs⟩, ⟨α, hα⟩⟩ => ?_
  have hmem : ∀ j ∈ s, ∀ v ≤ α j + 1, α.update j v ∈ cubeSupport b (s.erase j) :=
    fun _ hj _ hv => update_mem_cubeSupport_erase hα hj hv
  have hcard : ∀ j ∈ s, #(s.erase j) = k := fun j hj => by rw [card_erase_of_mem hj, hs]; rfl
  have hcd : ContDiffOn ℝ 1 (cubeFieldInterp k hb w) Set.univ :=
    (contDiff_evalForm _).contDiffOn
  change fieldDofAt s α _ = fieldDofAt s α _
  rw [fieldDofAt_extDeriv s α hU hKU hw,
    fieldDofAt_extDeriv s α isOpen_univ (Set.subset_univ _) hcd]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [cubeT_cubeFieldInterp hb (hcard j hj) (hmem j hj 1 (by omega)),
    cubeT_cubeFieldInterp hb (hcard j hj) (hmem j hj 0 (Nat.zero_le _)),
    cubeT_cubeFieldInterp hb (hcard j hj) (hmem j hj _ le_rfl)]

end Commuting

/-! ### The global interpolant commutes with `d` -/

section GlobalCommuting

variable {b : Fin n → ℕ} {k : ℕ}

theorem fieldTrace_congr {g : Fin n → Option ℝ}
    (hg : ∀ j c, g j = some c → c ∈ Set.Icc (0 : ℝ) 1) {w w' : FormField n}
    (h : ∀ y ∈ closedCube n, w y = w' y) {y : Fin n → ℝ} (hy : y ∈ closedCube n) :
    fieldTrace g w y = fieldTrace g w' y := by
  funext s
  unfold fieldTrace
  rw [h _ (planePoint_mem_closedCube hg hy)]

/-- `Π̂` only sees the values on the closed cube. -/
theorem cubeFieldInterp_congr_on (hb : ∀ j, 1 ≤ b j) {w w' : FormField n}
    (h : ∀ y ∈ closedCube n, w y = w' y) : cubeFieldInterp k hb w = cubeFieldInterp k hb w' :=
  cubeFieldInterp_congr hb fun _ =>
    MeasureTheory.setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
      fun _ hy => by rw [fieldTrace_congr (dofFace_mem_Icc _ _) h hy]

/-- **The cell interpolants commute with `d`**: `Π_m (d w) = d (Π_m w)` for `w` of class `C¹`
near the closed unit cube. -/
theorem cellInterp_extDeriv (hb : ∀ j, 1 ≤ b j) (m : CubeCell fun _ : Fin n => N)
    {w : FormField n} {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hKU : closedCube n ⊆ U)
    (hw : ContDiffOn ℝ 1 w U) :
    cellInterp (k + 1) hb m (extDeriv w) = extDeriv (cellInterp k hb m w) := by
  set A := affine (scalarMat n (N : ℝ)⁻¹) (fun i => ((m i : ℕ) : ℝ) / N)
  have hmem : ∀ y ∈ closedCube n, A y ∈ U := fun _ hy =>
    hKU (closedCell_subset_closedCube m (cellMap_mem_closedCell m hy))
  have hd : ∀ y ∈ closedCube n, extDeriv (cellPullback m w) y = cellPullback m (extDeriv w) y :=
    fun y hy => extDeriv_affinePullback_apply _ _
      (((hw.differentiableOn one_ne_zero) _ (hmem y hy)).differentiableAt
        (hU.mem_nhds (hmem y hy)))
  have hI := cubeFieldInterp_extDeriv (k := k) hb (hU.preimage (continuous_affine _ _)) hmem
    (contDiffOn_affinePullback _ _ hw)
  change cubeFieldInterp (k + 1) hb (extDeriv (cellPullback m w)) =
    extDeriv (cubeFieldInterp k hb (cellPullback m w)) at hI
  rw [cubeFieldInterp_congr_on hb hd] at hI
  funext x
  rw [cellInterp, cellInterp, hI]
  exact (extDeriv_affinePullback_apply (ω := cubeFieldInterp k hb (cellPullback m w)) _ _
    ((contDiff_evalForm _ (r := 1)).differentiable one_ne_zero _)).symm

/-- **The global interpolant commutes with `d`**: `Π_h (d w) = d (Π_h w)` cellwise, for `w` of
class `C¹` near `[0, 1]ⁿ`. -/
theorem cubeFieldGlobalInterp_extDeriv (hb : ∀ j, 1 ≤ b j) {w : FormField n}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hKU : closedCube n ⊆ U) (hw : ContDiffOn ℝ 1 w U) :
    cubeFieldGlobalInterp (N := N) (k + 1) hb (extDeriv w) =
      fun m => Koszul.extDeriv (cubeFieldGlobalInterp k hb w m) := by
  funext m
  have h : cellField (cubeFieldGlobalInterp (N := N) (k + 1) hb (extDeriv w)) m =
      cellField (fun m => Koszul.extDeriv (cubeFieldGlobalInterp k hb w m)) m := by
    rw [cellField_cubeFieldGlobalInterp, cellInterp_extDeriv hb m hU hKU hw,
      ← cellField_cubeFieldGlobalInterp, extDeriv_cellField]
  have h' := congrArg (affinePullback (fun i l => if i = l then (N : ℝ)⁻¹ else 0)
    (fun i => ((m i : ℕ) : ℝ) / N)) h
  rw [← evalForm_eq_affinePullback_cellField, ← evalForm_eq_affinePullback_cellField] at h'
  exact evalForm_injective h'

open Feec.Domain in
/-- **Commuting diagram on the mesh**: `Π_h w ∈ D(d_max)` and `d_max (Π_h w) = Π_h (d w)` in
`L²((0, 1)ⁿ; Λ^{k+1})`, for `w` of class `C¹` near `[0, 1]ⁿ`. -/
theorem cubeGlue_cubeFieldGlobalInterp_extDeriv [NeZero n] (hb : ∀ j, 1 ≤ b j)
    {w : FormField n} {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hKU : closedCube n ⊆ U)
    (hw : ContDiffOn ℝ 1 w U) :
    ∃ h : cubeGlue n N k (cubeFieldGlobalInterp k hb w) ∈
        ((extDerivOp ℝ n k).maximal (cubeRefinement n N).domain).domain,
      (extDerivOp ℝ n k).maximal (cubeRefinement n N).domain ⟨_, h⟩ =
        cubeGlue n N ((k : ℤ) + 1) (cubeFieldGlobalInterp (k + 1) hb (extDeriv w)) := by
  have hω := mem_cubeGlobalSpace.1 (cubeFieldGlobalInterp_mem (N := N) (k := k) hb w)
  obtain ⟨h, hval⟩ := cellField_mem_maximal_domain k hω.1 fun m => (hω.2 m).1
  refine ⟨h, hval.trans ?_⟩
  rw [cubeFieldGlobalInterp_extDeriv hb hU hKU hw]
  rfl

end GlobalCommuting

end Feec.FiniteElement.Cube
