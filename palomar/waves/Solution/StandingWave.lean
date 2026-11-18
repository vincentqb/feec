module

public import Solution.Wave
public import Solution.Forms
public import Solution.Mesh
public import Feec.Models.Cube.DeRhamIdentForms
public import Feec.Models.Cube.TangentialRate
public import Feec.Models.Cube.DeRhamIdentFEM
public import Feec.Models.Parallelepiped.StarShaped

/-!
# A standing wave of the cube with the natural boundary conditions

The non-vacuity witness of `FEEC.fem_wave` (`exists_standingWave`): on `Q = (0, ½)ⁿ`, the window
`[0, 2)` of `HΛ(Q)` carries the standing wave `U(t) = cos(2πt) A + sin(2πt) B`,
`A = (cos 2πx₀, 0)`, `B = (0, -sin 2πx₀ dx₀)` (`stateA`, `stateB`), with `L A = 2π B` and
`L B = -2π A` for the wave operator `L` of the window (`wave_stateA`, `wave_stateB`):
`d (cos 2πx₀) = -2π sin 2πx₀ dx₀` (`dMax_cosL2`), and `sin 2πx₀ dx₀`, whose normal component
vanishes on `∂Q`, lies in `D(dᵗ_min) = D(d_max†)` with `dᵗ (sin 2πx₀ dx₀) = -2π cos 2πx₀`
(`adjoint_sinL2`, the cut-off argument of
`Feec.Models.Cube.DeRhamIdent.mem_closure_formalAdj_single1`). On a window `W₀ → W₁`,
`L (σ, 0) = (0, dσ)` and `L (0, e) = (-d†e, 0)` (`graph_single_zero`, `graph_single_one`). Both
components are smooth with bounded derivatives on `cl Q` (`isCsForm_smul_modeL2`), and neither
vanishes in `L²(Q)` (`cosL2_ne_zero`, `sinL2_ne_zero`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Set Filter MeasureTheory LinearPMap

@[expose] public noncomputable section

namespace FEEC

namespace StandingWave

/-! ### The wave operator of a window `W₀ → W₁` -/

section Window2

variable {V : Fin 2 → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
  [∀ i, CompleteSpace (V i)] (W : Feec.HilbertComplex ℝ (ComplexShape.window 2) V)

theorem mem_domain_of_not_rel {i j : Fin 2} (h : ¬ (ComplexShape.window 2).Rel i j) (v : V i) :
    v ∈ (W.d i j).domain := by
  rw [W.domain_eq_top_of_not_rel h]; exact Submodule.mem_top

theorem mem_adjoint_domain_of_not_rel {i j : Fin 2} (h : ¬ (ComplexShape.window 2).Rel i j)
    (v : V j) : v ∈ ((W.d i j)†).domain := by
  rw [W.shape _ _ h, LinearPMap.adjoint_zero]; exact Submodule.mem_top

theorem not_rel_zero (i : Fin 2) : ¬ (ComplexShape.window 2).Rel i 0 := by
  simp [ComplexShape.window_rel]

theorem not_rel_one (k : Fin 2) : ¬ (ComplexShape.window 2).Rel 1 k := by
  simp only [ComplexShape.window_rel, Fin.val_one]; omega

theorem not_rel_zero_zero : ¬ (ComplexShape.window 2).Rel 0 0 := not_rel_zero 0

/-- **`L (σ, 0) = (0, d σ)`** on a window `W₀ → W₁`. -/
theorem graph_single_zero {σ : V 0} {v : V 1} (h : (σ, v) ∈ (W.d 0 1).graph) :
    (PiLp.single 2 (0 : Fin 2) σ, PiLp.single 2 (1 : Fin 2) v) ∈ W.wave.graph := by
  obtain ⟨σ', h1, h2⟩ := (LinearPMap.mem_graph_iff _).1 h
  change (σ' : V 0) = σ at h1
  change W.d 0 1 σ' = v at h2
  have e0 : (PiLp.single 2 (0 : Fin 2) σ : PiLp 2 V) 0 = σ := PiLp.single_eq_same (p := 2) _ _
  have e1 : (PiLp.single 2 (0 : Fin 2) σ : PiLp 2 V) 1 = 0 :=
    PiLp.single_eq_of_ne (p := 2) (by decide) _
  have r0 : (PiLp.single 2 (1 : Fin 2) v : PiLp 2 V) 0 = 0 :=
    PiLp.single_eq_of_ne (p := 2) (by decide) _
  have r1 : (PiLp.single 2 (1 : Fin 2) v : PiLp 2 V) 1 = v := PiLp.single_eq_same (p := 2) _ _
  have hx : PiLp.single 2 (0 : Fin 2) σ ∈ W.wave.domain := by
    refine (W.mem_wave_domain).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i
      · fin_cases j
        · exact mem_domain_of_not_rel W not_rel_zero_zero _
        · change (PiLp.single 2 (0 : Fin 2) σ : PiLp 2 V) 0 ∈ (W.d 0 1).domain
          rw [e0, ← h1]; exact σ'.2
      · change (PiLp.single 2 (0 : Fin 2) σ : PiLp 2 V) 1 ∈ (W.d 1 j).domain
        rw [e1]; exact Submodule.zero_mem _
    · fin_cases j
      · exact mem_adjoint_domain_of_not_rel W (not_rel_zero i) _
      · change (PiLp.single 2 (0 : Fin 2) σ : PiLp 2 V) 1 ∈ ((W.d i 1)†).domain
        rw [e1]; exact Submodule.zero_mem _
  refine (LinearPMap.mem_graph_iff _).2 ⟨⟨_, hx⟩, rfl, ?_⟩
  have z : ∀ {j k : Fin 2} (T : V j →ₗ.[ℝ] V k) (h : (0 : V j) ∈ T.domain), T ⟨0, h⟩ = 0 :=
    fun T h => LinearPMap.apply_mk_eq_zero T h rfl
  have hσ : ∀ hs : σ ∈ (W.d 0 1).domain, W.d 0 1 ⟨σ, hs⟩ = v := fun hs => by
    rw [← h2]; exact congrArg _ (Subtype.ext h1.symm)
  refine PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
    rw [Feec.HilbertComplex.wave_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  · simp only [W.apply_eq_zero_of_not_rel not_rel_zero_zero,
      W.apply_eq_zero_of_not_rel (not_rel_zero 1),
      LinearPMap.adjoint_apply_eq_zero_of_eq_zero (W.shape 0 0 not_rel_zero_zero), e1, z, r0,
      add_zero, sub_zero]
  · simp only [W.apply_eq_zero_of_not_rel (not_rel_one 1),
      LinearPMap.adjoint_apply_eq_zero_of_eq_zero (W.shape 1 0 (not_rel_one 0)),
      LinearPMap.adjoint_apply_eq_zero_of_eq_zero (W.shape 1 1 (not_rel_one 1)), e0, hσ, r1,
      add_zero, sub_zero]

/-- **`L (0, e) = (-d† e, 0)`** on a window `W₀ → W₁`. -/
theorem graph_single_one {e : V 1} {v : V 0} (h : (e, v) ∈ ((W.d 0 1)†).graph) :
    (PiLp.single 2 (1 : Fin 2) e, PiLp.single 2 (0 : Fin 2) (-v)) ∈ W.wave.graph := by
  obtain ⟨e', h1, h2⟩ := (LinearPMap.mem_graph_iff _).1 h
  change (e' : V 1) = e at h1
  change (W.d 0 1)† e' = v at h2
  have e0 : (PiLp.single 2 (1 : Fin 2) e : PiLp 2 V) 0 = 0 :=
    PiLp.single_eq_of_ne (p := 2) (by decide) _
  have e1 : (PiLp.single 2 (1 : Fin 2) e : PiLp 2 V) 1 = e := PiLp.single_eq_same (p := 2) _ _
  have r0 : (PiLp.single 2 (0 : Fin 2) (-v) : PiLp 2 V) 0 = -v := PiLp.single_eq_same (p := 2) _ _
  have r1 : (PiLp.single 2 (0 : Fin 2) (-v) : PiLp 2 V) 1 = 0 :=
    PiLp.single_eq_of_ne (p := 2) (by decide) _
  have hx : PiLp.single 2 (1 : Fin 2) e ∈ W.wave.domain := by
    refine (W.mem_wave_domain).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i
      · change (PiLp.single 2 (1 : Fin 2) e : PiLp 2 V) 0 ∈ (W.d 0 j).domain
        rw [e0]; exact Submodule.zero_mem _
      · exact mem_domain_of_not_rel W (not_rel_one j) _
    · fin_cases j
      · change (PiLp.single 2 (1 : Fin 2) e : PiLp 2 V) 0 ∈ ((W.d i 0)†).domain
        rw [e0]; exact Submodule.zero_mem _
      · fin_cases i
        · change (PiLp.single 2 (1 : Fin 2) e : PiLp 2 V) 1 ∈ ((W.d 0 1)†).domain
          rw [e1, ← h1]; exact e'.2
        · exact mem_adjoint_domain_of_not_rel W (not_rel_one 1) _
  refine (LinearPMap.mem_graph_iff _).2 ⟨⟨_, hx⟩, rfl, ?_⟩
  have z : ∀ {j k : Fin 2} (T : V j →ₗ.[ℝ] V k) (h : (0 : V j) ∈ T.domain), T ⟨0, h⟩ = 0 :=
    fun T h => LinearPMap.apply_mk_eq_zero T h rfl
  have he : ∀ hs : e ∈ ((W.d 0 1)†).domain, (W.d 0 1)† ⟨e, hs⟩ = v := fun hs => by
    rw [← h2]; exact congrArg _ (Subtype.ext h1.symm)
  refine PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
    rw [Feec.HilbertComplex.wave_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  · simp only [W.apply_eq_zero_of_not_rel not_rel_zero_zero,
      W.apply_eq_zero_of_not_rel (not_rel_zero 1),
      LinearPMap.adjoint_apply_eq_zero_of_eq_zero (W.shape 0 0 not_rel_zero_zero), e1, he, r0,
      zero_add, zero_sub]
  · simp only [W.apply_eq_zero_of_not_rel (not_rel_one 1),
      LinearPMap.adjoint_apply_eq_zero_of_eq_zero (W.shape 1 0 (not_rel_one 0)),
      LinearPMap.adjoint_apply_eq_zero_of_eq_zero (W.shape 1 1 (not_rel_one 1)), e0, z, r1,
      add_zero, sub_zero]

end Window2

/-! ### Continuous forms in `L²` -/

section L2

open Feec.Models.StarShaped

variable {n : ℕ}

theorem measurableSet_cube : MeasurableSet (cube n) :=
  (Feec.Models.Cube.FEM.isOpen_cubeDomain n).measurableSet

theorem isOpen_cube : IsOpen (cube n) := Feec.Models.Cube.FEM.isOpen_cubeDomain n

theorem isBounded_cube : Bornology.IsBounded (cube n) := (CubeWitness.starDomain n).isBounded

/-- The class in `L²(Θ; Λᵏ)` of the degree-`k` coefficients of a continuous form field `w`. -/
def modeL2 {Θ : Set (Fin n → ℝ)} (hm : MeasurableSet Θ) (hb : Bornology.IsBounded Θ) (k : ℤ)
    {w : FormField n} (hw : Continuous w) : Feec.Domain.L2F ℝ Θ (Feec.Domain.formIdx n k) :=
  Feec.Domain.toL2F fun s : Feec.Domain.formIdx n k => Feec.Domain.memLp_of_continuous hm hb
    (show Continuous fun y => w y s.1 from (continuous_apply s.1).comp hw)

theorem coeFn_modeL2 {Θ : Set (Fin n → ℝ)} (hm : MeasurableSet Θ) (hb : Bornology.IsBounded Θ)
    (k : ℤ) {w : FormField n} (hw : Continuous w) (s : Feec.Domain.formIdx n k) :
    (modeL2 hm hb k hw s : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Θ] fun y => w y s.1 :=
  MemLp.coeFn_toLp (Feec.Domain.memLp_of_continuous hm hb
    (show Continuous fun y => w y s.1 from (continuous_apply s.1).comp hw))

end L2

/-! ### The modes `cos 2πx₀` and `sin 2πx₀ dx₀` -/

section Modes

open Real Feec.Models.StarShaped

variable {n : ℕ} [NeZero n]

/-- `cos 2πx₀` as a `0`-form field. -/
def cosMode : FormField n := fun y r => if r = ∅ then Real.cos (2 * π * y 0) else 0

/-- `sin 2πx₀ dx₀` as a `1`-form field. -/
def sinMode : FormField n := fun y r => if r = {0} then Real.sin (2 * π * y 0) else 0

theorem contDiff_coord {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun y : Fin n → ℝ => f (2 * π * y 0) :=
  hf.comp (contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin n => ℝ) (0 : Fin n)))

theorem contDiff_cosMode : ContDiff ℝ ∞ (cosMode (n := n)) := by
  refine contDiff_pi.2 fun r => ?_
  unfold cosMode
  split_ifs
  · exact contDiff_coord Real.contDiff_cos
  · exact contDiff_const

theorem contDiff_sinMode : ContDiff ℝ ∞ (sinMode (n := n)) := by
  refine contDiff_pi.2 fun r => ?_
  unfold sinMode
  split_ifs
  · exact contDiff_coord Real.contDiff_sin
  · exact contDiff_const

theorem hasFDerivAt_cos_coord (y : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => Real.cos (2 * π * y 0))
      ((-Real.sin (2 * π * y 0) * (2 * π)) • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin n => ℝ) 0) y := by
  have h := HasFDerivAt.const_mul (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ)
    (0 : Fin n) y) (2 * π)
  have := (Real.hasDerivAt_cos (2 * π * y 0)).comp_hasFDerivAt y h
  rw [smul_smul] at this
  exact this

theorem hasFDerivAt_sin_coord (y : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => Real.sin (2 * π * y 0))
      ((Real.cos (2 * π * y 0) * (2 * π)) • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin n => ℝ) 0) y := by
  have h := HasFDerivAt.const_mul (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ)
    (0 : Fin n) y) (2 * π)
  have := (Real.hasDerivAt_sin (2 * π * y 0)).comp_hasFDerivAt y h
  rw [smul_smul] at this
  exact this

/-- **`d (cos 2πx₀) = -2π sin 2πx₀ dx₀`.** -/
theorem extDeriv_cosMode : extDeriv (cosMode (n := n)) = (-(2 * π)) • sinMode := by
  funext y r
  have key : ∀ j, partialDeriv j (fun y => cosMode y (r.erase j)) y =
      if r.erase j = ∅ then
        -Real.sin (2 * π * y 0) * (2 * π) * (Pi.single j (1 : ℝ) : Fin n → ℝ) 0 else 0 := by
    intro j
    by_cases h : r.erase j = ∅
    · simp only [cosMode, h, ↓reduceIte]
      change fderiv ℝ (fun y : Fin n → ℝ => Real.cos (2 * π * y 0)) y (Pi.single j 1) = _
      rw [(hasFDerivAt_cos_coord y).fderiv]
      simp
    · simp only [cosMode, h, ↓reduceIte]
      change fderiv ℝ (fun _ : Fin n → ℝ => (0 : ℝ)) y (Pi.single j 1) = 0
      simp
  simp only [Pi.smul_apply, smul_eq_mul, sinMode]
  change ∑ j ∈ r, sgn j r * partialDeriv j (fun y => cosMode y (r.erase j)) y = _
  simp only [key]
  by_cases hr : r = {0}
  · subst hr
    simp [sgn]
    ring
  · simp only [hr, ↓reduceIte, mul_zero]
    refine Finset.sum_eq_zero fun j hj => ?_
    by_cases he : r.erase j = ∅
    · have hrj : r = {j} := by
        rcases (Finset.erase_eq_empty_iff _ _).1 he with h | h
        · exact absurd hj (by simp [h])
        · exact h
      have hj0 : (0 : Fin n) ≠ j := fun h => hr (by rw [hrj, h])
      simp only [he, ↓reduceIte, Pi.single_eq_of_ne hj0, mul_zero]
    · simp only [he, ↓reduceIte, mul_zero]

theorem cosMode_deg (y : Fin n → ℝ) (r : Finset (Fin n)) (hr : (r.card : ℤ) ≠ 0) :
    cosMode y r = 0 := by
  have : r ≠ ∅ := fun h => hr (by simp [h])
  simp [cosMode, this]

theorem sinMode_deg (y : Fin n → ℝ) (r : Finset (Fin n)) (hr : (r.card : ℤ) ≠ 1) :
    sinMode y r = 0 := by
  have : r ≠ {0} := fun h => hr (by simp [h])
  simp [sinMode, this]

/-- The class of `cos 2πx₀` in `L²(Q; Λ⁰)`. -/
def cosL2 : L2Form (cube n) 0 :=
  modeL2 measurableSet_cube isBounded_cube 0 contDiff_cosMode.continuous

/-- The class of `sin 2πx₀ dx₀` in `L²(Q; Λ¹)`. -/
def sinL2 : L2Form (cube n) 1 :=
  modeL2 measurableSet_cube isBounded_cube 1 contDiff_sinMode.continuous

/-- **`d (cos 2πx₀) = -2π sin 2πx₀ dx₀` in `HΛ(Q)`.** -/
theorem dMax_cosL2 : (cosL2 (n := n), (-(2 * π)) • sinL2) ∈ (dMax (cube n) 0).graph := by
  rw [dMax_eq]
  set w : Feec.Domain.formIdx n 0 → (Fin n → ℝ) → ℝ := fun s y => cosMode y s.1 with hw_def
  have hws : ∀ s, ContDiff ℝ 1 (w s) := fun s =>
    (contDiff_pi.1 (contDiff_cosMode.of_le (by exact_mod_cast le_top)) s.1)
  have hw : ∀ s, MemLp (w s) 2 (volume.restrict (cube n)) := fun s =>
    Feec.Domain.memLp_of_continuous measurableSet_cube isBounded_cube (hws s).continuous
  have happly : ∀ t, (Feec.Domain.extDerivOp ℝ n 0).apply w t =
      fun y => (-(2 * π)) * sinMode y t.1 := fun t => funext fun y => by
    rw [extDerivOp_apply_eq cosMode w (fun _ _ => rfl), extDeriv_cosMode]; rfl
  have hdw : ∀ t, MemLp ((Feec.Domain.extDerivOp ℝ n 0).apply w t) 2
      (volume.restrict (cube n)) := fun t => by
    rw [happly t]
    exact Feec.Domain.memLp_of_continuous measurableSet_cube isBounded_cube
      (continuous_const.mul ((continuous_apply t.1).comp contDiff_sinMode.continuous))
  obtain ⟨h, hv⟩ := Feec.Domain.extDerivOp_smooth_mem_maximal_domain isOpen_cube hws hw hdw
  refine (LinearPMap.mem_graph_iff _).2 ⟨⟨_, h⟩, rfl, hv.trans ?_⟩
  refine PiLp.ext fun t => Lp.ext ?_
  filter_upwards [(hdw t).coeFn_toLp, Lp.coeFn_smul (-(2 * π)) (sinL2 (n := n) t),
    coeFn_modeL2 measurableSet_cube isBounded_cube 1 contDiff_sinMode.continuous t]
    with y h1 h2 h3
  change ((hdw t).toLp _ : (Fin n → ℝ) → ℝ) y = ((-(2 * π)) • sinL2 (n := n) t : _) y
  rw [h1, h2, Pi.smul_apply, smul_eq_mul, happly t]
  change _ = _ * (modeL2 measurableSet_cube isBounded_cube 1 contDiff_sinMode.continuous t :
    (Fin n → ℝ) → ℝ) y
  rw [h3]

/-- **`sin 2πx₀ dx₀ ∈ D(d_max†)` and `d_max† (sin 2πx₀ dx₀) = -2π cos 2πx₀`**: the form has
vanishing normal component on `∂Q`, so it lies in `D(dᵗ_min) = D(d_max†)` (the cut-off argument
of `Feec.Models.Cube.DeRhamIdent.mem_closure_formalAdj_single1`). -/
theorem adjoint_sinL2 :
    (sinL2 (n := n), (-(2 * π)) • cosL2) ∈ ((dMax (cube n) 0)†).graph := by
  rw [dMax_eq, (Feec.Domain.extDerivOp ℝ n 0).adjoint_maximal isOpen_cube,
    (Feec.Domain.extDerivOp ℝ n 0).formalAdj.minimal_graph isOpen_cube, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe]
  have key : ∀ (Θ : Set (Fin n → ℝ)), Θ = Feec.Models.Cube.Geometry.Q (Fin n) →
      ∀ (hm : MeasurableSet Θ) (hb : Bornology.IsBounded Θ),
      (modeL2 hm hb (0 + 1) contDiff_sinMode.continuous,
          (-(2 * π)) • modeL2 hm hb 0 contDiff_cosMode.continuous) ∈
        closure ((Feec.Domain.extDerivOp ℝ n 0).formalAdj.testGraph Θ :
          Set (Feec.Domain.L2F ℝ Θ (Feec.Domain.formIdx n (0 + 1)) ×
            Feec.Domain.L2F ℝ Θ (Feec.Domain.formIdx n 0))) := by
    rintro Θ rfl hm hb
    set φ : (Fin n → ℝ) → ℝ := fun y => Real.sin (2 * π * y 0) with hφ_def
    set t : Feec.Domain.formIdx n (0 + 1) := ⟨{0}, by simp⟩ with ht_def
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := contDiff_coord Real.contDiff_sin
    have hφd : ∀ y j, fderiv ℝ φ y (Pi.single j 1) =
        Real.cos (2 * π * y 0) * (2 * π) * (Pi.single j (1 : ℝ) : Fin n → ℝ) 0 := fun y j => by
      rw [(hasFDerivAt_sin_coord y).fderiv]; simp
    have hM : ∀ y, |φ y| ≤ 1 := fun y => Real.abs_sin_le_one _
    have hL : ∀ j y, |fderiv ℝ φ y (Pi.single j 1)| ≤ 2 * π := fun j y => by
      rw [hφd, abs_mul, abs_mul]
      have h1 : |(Pi.single j (1 : ℝ) : Fin n → ℝ) 0| ≤ 1 := by
        rw [Pi.single_apply]; split_ifs <;> simp
      have h2 : |2 * π| = 2 * π := abs_of_pos (by positivity)
      rw [h2]
      calc |Real.cos (2 * π * y 0)| * (2 * π) * |(Pi.single j (1 : ℝ) : Fin n → ℝ) 0| ≤
            1 * (2 * π) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)) h1
            (abs_nonneg _) (by positivity)
        _ = 2 * π := by ring
    have hV : ∀ j ∈ t.1, ∀ y : Fin n → ℝ, (y j = 0 ∨ y j = 1 / 2) → φ y = 0 := by
      intro j hj y hy
      have hj0 : j = 0 := Finset.mem_singleton.1 hj
      subst hj0
      rcases hy with hy | hy
      · simp [hφ_def, hy]
      · simp only [hφ_def, hy]
        rw [show 2 * π * (1 / 2) = π by ring, Real.sin_pi]
    have hcl := Feec.Models.Cube.DeRhamIdent.mem_closure_formalAdj_single1 (k := 0) t hφ hM hL hV
    convert hcl using 2
    · refine PiLp.ext fun r => Lp.ext ?_
      filter_upwards [coeFn_modeL2 hm hb (0 + 1) contDiff_sinMode.continuous r,
        MemLp.coeFn_toLp (Feec.Models.Cube.DeRhamIdent.memLp_single1 t hφ r)] with y h1 h2
      change (modeL2 hm hb (0 + 1) contDiff_sinMode.continuous r : (Fin n → ℝ) → ℝ) y =
        ((Feec.Models.Cube.DeRhamIdent.memLp_single1 t hφ r).toLp _ : (Fin n → ℝ) → ℝ) y
      rw [h1, h2]
      by_cases hr : r.1 = {0}
      · have : r = t := Subtype.ext hr
        subst this
        simp [sinMode, hr, Feec.Models.Cube.DeRhamIdent.single1, hφ_def]
      · have : r ≠ t := fun h => hr (by rw [h])
        simp [sinMode, hr, Feec.Models.Cube.DeRhamIdent.single1, this]
    · refine PiLp.ext fun r => Lp.ext ?_
      filter_upwards [Lp.coeFn_smul (-(2 * π)) (modeL2 hm hb 0 contDiff_cosMode.continuous r),
        coeFn_modeL2 hm hb 0 contDiff_cosMode.continuous r,
        MemLp.coeFn_toLp (Feec.Models.Cube.DeRhamIdent.memLp_formalAdj_single1 t hφ r)]
        with y h1 h2 h3
      rw [PiLp.smul_apply, h1]
      change _ = ((Feec.Models.Cube.DeRhamIdent.memLp_formalAdj_single1 t hφ r).toLp _ :
          (Fin n → ℝ) → ℝ) y
      rw [h3, Pi.smul_apply, h2, Feec.Models.Cube.DeRhamIdent.formalAdj_single1_apply]
      have hr : r.1 = ∅ := Finset.card_eq_zero.1 (by exact_mod_cast r.2)
      simp [cosMode, hr, ht_def, hφd, Feec.ExteriorFibre.sgn]
      ring
  exact key _ (Feec.Models.Cube.FEM.cubeDomain_eq_Q n) measurableSet_cube isBounded_cube

end Modes

/-! ### Regularity of the modes -/

section Regularity

variable {n : ℕ}

theorem natCast_le_infty (m : ℕ) : ((m : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top

/-- A smooth form field of degree `j`, times `a`, is in the class `IsCsForm` of `Q` with every
bound `L ≥ |a| K`, `K` a bound of the `(s + 1)`-st derivatives of `w` and `dw` on `cl Q`. -/
theorem isCsForm_smul_modeL2 {j : ℤ} {w : FormField n} (hw : ContDiff ℝ ∞ w)
    (hdeg : ∀ y (r : Finset (Fin n)), (r.card : ℤ) ≠ j → w y r = 0) (s : ℕ) {K : ℝ}
    (hK1 : ∀ y ∈ closure (cube n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ K)
    (hK2 : ∀ y ∈ closure (cube n), ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ K)
    (a : ℝ) {L : ℝ} (hL : |a| * K ≤ L) :
    IsCsForm (cube n) s j L (a • modeL2 measurableSet_cube isBounded_cube j hw.continuous) := by
  have hws : ContDiff ℝ (s + 1) w := hw.of_le (by exact_mod_cast le_top)
  have hdw : ContDiff ℝ (s + 1) (extDeriv w) :=
    Feec.FiniteElement.contDiff_extDeriv (m := ((s + 1 : ℕ) : WithTop ℕ∞))
      (hw.of_le (by exact_mod_cast le_top))
  have hext : extDeriv (a • w) = a • extDeriv w := funext fun x =>
    Feec.FiniteElement.extDeriv_smul_const_apply a (hw.differentiable (by simp) x)
  refine Or.inr ⟨a • w, (hw.of_le (natCast_le_infty (s + 2))).const_smul a,
    fun y r hr => ?_, fun y hy => ?_, fun y hy => ?_, fun r => ?_⟩
  · simp [hdeg y r hr]
  · rw [iteratedFDeriv_const_smul_apply hws.contDiffAt, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hK1 y hy) (abs_nonneg a)).trans hL
  · rw [hext, iteratedFDeriv_const_smul_apply hdw.contDiffAt, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hK2 y hy) (abs_nonneg a)).trans hL
  · filter_upwards [Lp.coeFn_smul a (modeL2 measurableSet_cube isBounded_cube j hw.continuous r),
      coeFn_modeL2 measurableSet_cube isBounded_cube j hw.continuous r] with y h1 h2
    rw [PiLp.smul_apply, h1, Pi.smul_apply, h2]
    rfl

/-- A common bound of the `(s + 1)`-st derivatives of a smooth form field and of its exterior
derivative on `cl Q`. -/
theorem exists_bound_mode {w : FormField n} (hw : ContDiff ℝ ∞ w) (s : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ y ∈ closure (cube n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ K ∧
      ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ K := by
  obtain ⟨K₁, hK₁, h₁⟩ := Feec.Models.Cube.FEM.exists_bound_iteratedFDeriv_le (n := n)
    (m := s + 1) (hw.of_le (by exact_mod_cast le_top))
  obtain ⟨K₂, hK₂, h₂⟩ := Feec.Models.Cube.FEM.exists_bound_iteratedFDeriv_le (n := n)
    (m := s + 1) (Feec.FiniteElement.contDiff_extDeriv (m := ((s + 1 : ℕ) : WithTop ℕ∞))
      (hw.of_le (by exact_mod_cast le_top)))
  exact ⟨K₁ + K₂, by positivity, fun y hy =>
    ⟨(h₁ (s + 1) le_rfl y hy).trans (le_add_of_nonneg_right hK₂),
      (h₂ (s + 1) le_rfl y hy).trans (le_add_of_nonneg_left hK₁)⟩⟩

end Regularity

/-! ### The standing wave -/

section Wave

open Real

variable {n : ℕ} [NeZero n]

/-- `A = (cos 2πx₀, 0)` in the window `[0, 2)` of `L²(Q; Λ)`. -/
def stateA : Total (L2Form (cube n)) 0 2 := PiLp.single 2 (0 : Fin 2) cosL2

/-- `B = (0, -sin 2πx₀ dx₀)` in the window `[0, 2)` of `L²(Q; Λ)`. -/
def stateB : Total (L2Form (cube n)) 0 2 := PiLp.single 2 (1 : Fin 2) (-sinL2)

theorem smul_single {V : Fin 2 → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, NormedSpace ℝ (V i)] (c : ℝ) (i : Fin 2) (x : V i) :
    c • (PiLp.single 2 i x : PiLp 2 V) = PiLp.single 2 i (c • x) := by
  refine PiLp.ext fun j => ?_
  by_cases h : j = i
  · subst h; simp
  · simp [PiLp.single_eq_of_ne (p := 2) h]

variable (H : HilbertComplex ℝ (L2Form (cube n))) (hH : ∀ k, H.d k (k + 1) = dMax (cube n) k)
include hH

omit [NeZero n] hH in
theorem wave_eq_window : H.wave 0 2 = (H.toFeec.window 0 2).wave := by
  rw [Feec.HilbertComplex.wave_eq, ← HilbertComplex.totalD_eq]; rfl

omit [NeZero n] in
theorem window_d_zero_one : (H.toFeec.window 0 2).d 0 1 = dMax (cube n) 0 := hH 0

/-- **`L A = 2π B`.** -/
theorem wave_stateA : (stateA, (2 * π) • stateB) ∈ (H.wave 0 2).graph := by
  rw [wave_eq_window H]
  have h := StandingWave.graph_single_zero (H.toFeec.window 0 2) (σ := cosL2)
    (v := (-(2 * π)) • sinL2) (by rw [window_d_zero_one H hH]; exact dMax_cosL2)
  have e : (2 * π) • (stateB : Total (L2Form (cube n)) 0 2) =
      PiLp.single 2 (1 : Fin 2) ((-(2 * π)) • sinL2) := by
    simp only [stateB, smul_single, smul_neg, neg_smul]
  rw [e]
  exact h

/-- **`L B = -2π A`.** -/
theorem wave_stateB : (stateB, (-(2 * π)) • stateA) ∈ (H.wave 0 2).graph := by
  rw [wave_eq_window H]
  have h := StandingWave.graph_single_one (H.toFeec.window 0 2) (e := sinL2)
    (v := (-(2 * π)) • cosL2) (by rw [window_d_zero_one H hH]; exact adjoint_sinL2)
  have h' := Submodule.neg_mem _ h
  have e1 : (stateB : Total (L2Form (cube n)) 0 2) =
      -(PiLp.single 2 (1 : Fin 2) sinL2 : Total (L2Form (cube n)) 0 2) := by
    simp only [stateB, PiLp.single_neg]
  have e2 : (-(2 * π)) • (stateA : Total (L2Form (cube n)) 0 2) =
      -(PiLp.single 2 (0 : Fin 2) (-((-(2 * π)) • cosL2)) : Total (L2Form (cube n)) 0 2) := by
    simp only [stateA, smul_single, PiLp.single_neg, neg_neg]
  rw [e1, e2, ← Prod.neg_mk]
  exact h'

omit hH in
/-- `cos 2πx₀ ≠ 0` in `L²(Q)`. -/
theorem cosL2_ne_zero : (cosL2 : L2Form (cube n) 0) ≠ 0 := by
  intro h0
  set s₀ : Feec.Domain.formIdx n 0 := ⟨∅, by simp⟩
  have hae : (fun y : Fin n → ℝ => Real.cos (2 * π * y 0)) =ᵐ[volume.restrict (cube n)] 0 := by
    filter_upwards [coeFn_modeL2 measurableSet_cube isBounded_cube 0
      contDiff_cosMode.continuous s₀, Lp.coeFn_zero ℝ 2 (volume.restrict (cube n))] with y h1 h2
    have e : (cosL2 : L2Form (cube n) 0) s₀ = 0 := by rw [h0]; rfl
    change (modeL2 measurableSet_cube isBounded_cube 0 contDiff_cosMode.continuous s₀ :
      (Fin n → ℝ) → ℝ) y = _ at h1
    rw [show (modeL2 measurableSet_cube isBounded_cube 0 contDiff_cosMode.continuous s₀ :
      Lp ℝ 2 (volume.restrict (cube n))) = 0 from e, h2] at h1
    simpa [cosMode, s₀] using h1.symm
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq hae isOpen_cube
    (contDiff_coord (n := n) Real.contDiff_cos).continuous.continuousOn continuousOn_const
  have hy : (fun _ : Fin n => (1 / 8 : ℝ)) ∈ cube n :=
    Set.mem_univ_pi.2 fun _ => ⟨by norm_num, by norm_num⟩
  have := heq hy
  simp only [Pi.zero_apply] at this
  have hpos : 0 < Real.cos (2 * π * (1 / 8)) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  exact hpos.ne' this

omit hH in
/-- `sin 2πx₀ dx₀ ≠ 0` in `L²(Q; Λ¹)`. -/
theorem sinL2_ne_zero : (sinL2 : L2Form (cube n) 1) ≠ 0 := by
  intro h0
  set s₀ : Feec.Domain.formIdx n 1 := ⟨{0}, by simp⟩
  have hae : (fun y : Fin n → ℝ => Real.sin (2 * π * y 0)) =ᵐ[volume.restrict (cube n)] 0 := by
    filter_upwards [coeFn_modeL2 measurableSet_cube isBounded_cube 1
      contDiff_sinMode.continuous s₀, Lp.coeFn_zero ℝ 2 (volume.restrict (cube n))] with y h1 h2
    have e : (sinL2 : L2Form (cube n) 1) s₀ = 0 := by rw [h0]; rfl
    change (modeL2 measurableSet_cube isBounded_cube 1 contDiff_sinMode.continuous s₀ :
      (Fin n → ℝ) → ℝ) y = _ at h1
    rw [show (modeL2 measurableSet_cube isBounded_cube 1 contDiff_sinMode.continuous s₀ :
      Lp ℝ 2 (volume.restrict (cube n))) = 0 from e, h2] at h1
    simpa [sinMode, s₀] using h1.symm
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq hae isOpen_cube
    (contDiff_coord (n := n) Real.contDiff_sin).continuous.continuousOn continuousOn_const
  have hy : (fun _ : Fin n => (1 / 8 : ℝ)) ∈ cube n :=
    Set.mem_univ_pi.2 fun _ => ⟨by norm_num, by norm_num⟩
  have := heq hy
  simp only [Pi.zero_apply] at this
  have hpos : 0 < Real.sin (2 * π * (1 / 8)) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  exact hpos.ne' this

omit [NeZero n] hH in
theorem abs_triple_le {ν x : ℝ} (hν : 0 ≤ ν) (hx : |x| ≤ 1) : |ν * (ν * (ν * x))| ≤ ν ^ 3 := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hν]
  have h1 : ν * |x| ≤ ν := by nlinarith [abs_nonneg x]
  have h2 : ν * (ν * |x|) ≤ ν * ν := mul_le_mul_of_nonneg_left h1 hν
  have h3 : ν * (ν * (ν * |x|)) ≤ ν * (ν * ν) := mul_le_mul_of_nonneg_left h2 hν
  calc _ ≤ ν * (ν * ν) := h3
    _ = ν ^ 3 := by ring

/-- **The standing wave `U(t) = cos(2πt) A + sin(2πt) B`** of the window `[0, 2)` of `HΛ(Q)`
meets the hypotheses of `FEEC.fem_wave` on the exact solution, at all times. -/
theorem exists_standingWave (s : ℕ) :
    ∃ (L : ℝ) (U U₁ U₂ U₃ : ℝ → Total (L2Form (cube n)) 0 2),
      (∀ t, HasDerivAt U (U₁ t) t ∧ HasDerivAt U₁ (U₂ t) t ∧ HasDerivAt U₂ (U₃ t) t) ∧
      (∀ t, ‖U₃ t‖ ≤ L ∧ (U t, U₁ t) ∈ (H.wave 0 2).graph) ∧
      (∀ t t' (i : Fin 2), IsCsForm (cube n) s ((0 : ℤ) + (i : ℕ)) L (U t i) ∧
        IsCsForm (cube n) s ((0 : ℤ) + (i : ℕ)) (L * |t' - t|) (U t' i - U t i)) ∧
      ∀ t, U t ≠ 0 ∧ U₁ t ≠ 0 := by
  obtain ⟨ν, hν_def⟩ : ∃ ν : ℝ, ν = 2 * π := ⟨_, rfl⟩
  have hν : 0 < ν := by rw [hν_def]; positivity
  have hwA := wave_stateA H hH
  have hwB := wave_stateB H hH
  rw [← hν_def] at hwA hwB
  obtain ⟨K₀, hK₀, hb₀⟩ := exists_bound_mode (contDiff_cosMode (n := n)) s
  obtain ⟨K₁, hK₁, hb₁⟩ := exists_bound_mode (contDiff_sinMode (n := n)) s
  set A : Total (L2Form (cube n)) 0 2 := stateA with hA_def
  set B : Total (L2Form (cube n)) 0 2 := stateB with hB_def
  obtain ⟨L, hL0, hL1, hL2⟩ : ∃ L : ℝ, K₀ + K₁ ≤ L ∧ ν * (K₀ + K₁) ≤ L ∧
      ν ^ 3 * (‖A‖ + ‖B‖) ≤ L := by
    have h3 : 0 ≤ ν ^ 3 * (‖A‖ + ‖B‖) := by positivity
    have h4 : 0 ≤ ν * (K₀ + K₁) := by positivity
    have h5 : 0 ≤ K₀ + K₁ := by positivity
    exact ⟨(K₀ + K₁) + ν * (K₀ + K₁) + ν ^ 3 * (‖A‖ + ‖B‖), by linarith, by linarith,
      by linarith⟩
  have hcos : ∀ t, HasDerivAt (fun t => Real.cos (ν * t)) (-(ν * Real.sin (ν * t))) t :=
    fun t => by
      have := ((hasDerivAt_id t).const_mul ν).cos
      simp only [id, mul_one] at this
      convert this using 1; ring
  have hsin : ∀ t, HasDerivAt (fun t => Real.sin (ν * t)) (ν * Real.cos (ν * t)) t :=
    fun t => by
      have := ((hasDerivAt_id t).const_mul ν).sin
      simp only [id, mul_one] at this
      convert this using 1; ring
  set U : ℝ → Total (L2Form (cube n)) 0 2 := fun t =>
    Real.cos (ν * t) • A + Real.sin (ν * t) • B with hU_def
  set U₁ : ℝ → Total (L2Form (cube n)) 0 2 := fun t =>
    (-(ν * Real.sin (ν * t))) • A + (ν * Real.cos (ν * t)) • B with hU₁_def
  set U₂ : ℝ → Total (L2Form (cube n)) 0 2 := fun t =>
    (-(ν * (ν * Real.cos (ν * t)))) • A + (ν * -(ν * Real.sin (ν * t))) • B with hU₂_def
  set U₃ : ℝ → Total (L2Form (cube n)) 0 2 := fun t =>
    (-(ν * (ν * -(ν * Real.sin (ν * t))))) • A + (ν * -(ν * (ν * Real.cos (ν * t)))) • B
    with hU₃_def
  have hA0 : A 0 = cosL2 := PiLp.single_eq_same (p := 2) _ _
  have hA1 : A 1 = 0 := PiLp.single_eq_of_ne (p := 2) (by decide) _
  have hB0 : B 0 = 0 := PiLp.single_eq_of_ne (p := 2) (by decide) _
  have hB1 : B 1 = -sinL2 := PiLp.single_eq_same (p := 2) _ _
  have hU0 : ∀ t, U t 0 = Real.cos (ν * t) • cosL2 := fun t => by
    simp only [hU_def, PiLp.add_apply, PiLp.smul_apply, hA0, hB0, smul_zero, add_zero]
  have hU1 : ∀ t, U t 1 = (-Real.sin (ν * t)) • sinL2 := fun t => by
    simp only [hU_def, PiLp.add_apply, PiLp.smul_apply, hA1, hB1, smul_zero, zero_add,
      smul_neg, neg_smul]
  have hcosd : ∀ y (r : Finset (Fin n)), (r.card : ℤ) ≠ (0 : ℤ) + ((0 : Fin 2) : ℕ) →
      cosMode y r = 0 := fun y r hr => cosMode_deg y r (by simpa using hr)
  have hsind : ∀ y (r : Finset (Fin n)), (r.card : ℤ) ≠ (0 : ℤ) + ((1 : Fin 2) : ℕ) →
      sinMode y r = 0 := fun y r hr => sinMode_deg y r (by simpa using hr)
  refine ⟨L, U, U₁, U₂, U₃, fun t => ⟨?_, ?_, ?_⟩, fun t => ⟨?_, ?_⟩, fun t t' => ?_, fun t => ?_⟩
  · exact ((hcos t).smul_const A).add ((hsin t).smul_const B)
  · exact (((hsin t).const_mul ν).neg.smul_const A).add (((hcos t).const_mul ν).smul_const B)
  · exact ((((hcos t).const_mul ν).const_mul ν).neg.smul_const A).add
      ((((hsin t).const_mul ν).neg.const_mul ν).smul_const B)
  · have ha : |-(ν * (ν * -(ν * Real.sin (ν * t))))| ≤ ν ^ 3 := by
      rw [show -(ν * (ν * -(ν * Real.sin (ν * t)))) = ν * (ν * (ν * Real.sin (ν * t))) by ring]
      exact abs_triple_le hν.le (Real.abs_sin_le_one _)
    have hb : |ν * -(ν * (ν * Real.cos (ν * t)))| ≤ ν ^ 3 := by
      rw [show ν * -(ν * (ν * Real.cos (ν * t))) = -(ν * (ν * (ν * Real.cos (ν * t)))) by ring,
        abs_neg]
      exact abs_triple_le hν.le (Real.abs_cos_le_one _)
    have hn : ‖U₃ t‖ ≤ ν ^ 3 * ‖A‖ + ν ^ 3 * ‖B‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    calc ‖U₃ t‖ ≤ ν ^ 3 * ‖A‖ + ν ^ 3 * ‖B‖ := hn
      _ = ν ^ 3 * (‖A‖ + ‖B‖) := by ring
      _ ≤ L := hL2
  · have hsum := (H.wave 0 2).graph.add_mem
      ((H.wave 0 2).graph.smul_mem (Real.cos (ν * t)) hwA)
      ((H.wave 0 2).graph.smul_mem (Real.sin (ν * t)) hwB)
    convert hsum using 1
    refine Prod.ext ?_ ?_
    · simp [hU_def, hA_def, hB_def]
    · simp only [hU₁_def, Prod.snd_add, Prod.smul_snd, hA_def, hB_def]
      module
  · have hνK₀ : ν * K₀ ≤ L := by
      have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hK₁ : K₀ ≤ K₀ + K₁) hν.le
      linarith
    have hνK₁ : ν * K₁ ≤ L := by
      have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hK₀ : K₁ ≤ K₀ + K₁) hν.le
      linarith
    have hc1 : |Real.cos (ν * t)| * K₀ ≤ L := by
      have := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one (ν * t)) hK₀
      linarith
    have hs1 : |-Real.sin (ν * t)| * K₁ ≤ L := by
      have := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (ν * t)) hK₁
      rw [abs_neg]
      linarith
    have hc2 : |Real.cos (ν * t') - Real.cos (ν * t)| * K₀ ≤ L * |t' - t| := by
      have h1 : |Real.cos (ν * t') - Real.cos (ν * t)| ≤ ν * |t' - t| := by
        have := Real.abs_cos_sub_cos_le (ν * t') (ν * t)
        rwa [← mul_sub, abs_mul, abs_of_pos hν] at this
      calc |Real.cos (ν * t') - Real.cos (ν * t)| * K₀ ≤ ν * |t' - t| * K₀ :=
            mul_le_mul_of_nonneg_right h1 hK₀
        _ = ν * K₀ * |t' - t| := by ring
        _ ≤ L * |t' - t| := mul_le_mul_of_nonneg_right hνK₀ (abs_nonneg _)
    have hs2 : |-Real.sin (ν * t') - -Real.sin (ν * t)| * K₁ ≤ L * |t' - t| := by
      have h1 : |-Real.sin (ν * t') - -Real.sin (ν * t)| ≤ ν * |t' - t| := by
        have := Real.abs_sin_sub_sin_le (ν * t') (ν * t)
        rw [← mul_sub, abs_mul, abs_of_pos hν] at this
        rw [neg_sub_neg, abs_sub_comm]
        exact this
      calc |-Real.sin (ν * t') - -Real.sin (ν * t)| * K₁ ≤ ν * |t' - t| * K₁ :=
            mul_le_mul_of_nonneg_right h1 hK₁
        _ = ν * K₁ * |t' - t| := by ring
        _ ≤ L * |t' - t| := mul_le_mul_of_nonneg_right hνK₁ (abs_nonneg _)
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · rw [hU0, hU0, ← sub_smul]
      exact ⟨isCsForm_smul_modeL2 contDiff_cosMode hcosd s (fun y hy => (hb₀ y hy).1)
        (fun y hy => (hb₀ y hy).2) _ hc1, isCsForm_smul_modeL2 contDiff_cosMode hcosd s
        (fun y hy => (hb₀ y hy).1) (fun y hy => (hb₀ y hy).2) _ hc2⟩
    · rw [hU1, hU1, ← sub_smul]
      exact ⟨isCsForm_smul_modeL2 contDiff_sinMode hsind s (fun y hy => (hb₁ y hy).1)
        (fun y hy => (hb₁ y hy).2) _ hs1, isCsForm_smul_modeL2 contDiff_sinMode hsind s
        (fun y hy => (hb₁ y hy).1) (fun y hy => (hb₁ y hy).2) _ hs2⟩
  · have hsc := Real.sin_sq_add_cos_sq (ν * t)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h0 : U t 0 = 0 := by rw [h]; rfl
      have h1 : U t 1 = 0 := by rw [h]; rfl
      rw [hU0] at h0
      rw [hU1] at h1
      have hc := (smul_eq_zero.1 h0).resolve_right cosL2_ne_zero
      have hs := neg_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right sinL2_ne_zero)
      rw [hc, hs] at hsc
      norm_num at hsc
    · have h0 : U₁ t 0 = 0 := by rw [h]; rfl
      have h1 : U₁ t 1 = 0 := by rw [h]; rfl
      simp only [hU₁_def, PiLp.add_apply, PiLp.smul_apply, hA0, hA1, hB0, hB1, smul_zero,
        add_zero, zero_add, smul_neg] at h0 h1
      have hs := (smul_eq_zero.1 h0).resolve_right cosL2_ne_zero
      have hc := (smul_eq_zero.1 (neg_eq_zero.1 h1)).resolve_right sinL2_ne_zero
      have hs' : Real.sin (ν * t) = 0 := by
        rcases mul_eq_zero.1 (neg_eq_zero.1 hs) with h | h
        · exact absurd h hν.ne'
        · exact h
      have hc' : Real.cos (ν * t) = 0 := by
        rcases mul_eq_zero.1 hc with h | h
        · exact absurd h hν.ne'
        · exact h
      rw [hc', hs'] at hsc
      norm_num at hsc

end Wave

end StandingWave

end FEEC
