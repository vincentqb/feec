module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Extension from a shell into the cube `Q = (0, ½)³`

Let `S = (-¼, ¾)³ ∖ [0, ½]³` be the shell around `Q` (`shell`). For a smooth `q` on `ℝ³` this
file constructs a smooth `s = lift q` such that

* `s = q` and `∇s = ∇q` on the hyperplanes `xᵢ ∈ {0, ½}` containing the faces of `Q`: the
  remainder `r = q - s` and its first derivatives vanish there (`rem_of_face`, `pd_rem_of_face`);
* on `Q`, `s` depends only on `q|_S`, with the `H²` bound `n2 s Q ≤ C n2 q S`
  (`exists_n2_lift_le`, `C` independent of `q`), where
  `n2 F B = ‖F‖ + Σⱼ ‖∂ⱼF‖ + Σⱼₖ ‖∂ₖ∂ⱼF‖` in `L²(B)` (`n2`).

**Construction.** In the coordinate `i`, the Hestenes reflection
`E_i F (x) = h(xᵢ) (-5 F(-xᵢ/2) + 6 F(-xᵢ/4)) + h(½ - xᵢ) (-5 F(¾ - xᵢ/2) + 6 F(⅝ - xᵢ/4))`
(`hest`; the other coordinates fixed, `h(t) = 1 - 12t² + 16t³` the cubic Hermite blend) reproduces
the value and the first derivatives of `F` on `xᵢ ∈ {0, ½}` (`hest_of_face`, `pd_hest_of_face`),
and for `xᵢ ∈ (0, ½)` it only samples `F` at points with `xᵢ ∈ (-¼, 0) ∪ (½, ¾)`. So
`T_i = I - E_i` kills the value and the first derivatives on these faces, the `T_i` commute
(`tI_comm`), `r = T₀ T₁ T₂ q` (`rem`) vanishes with its gradient on all six faces, and
`s = q - r = Σ_{A ≠ ∅} (-1)^{|A|+1} E_A q` (`lift_eq`) only samples `q` on the shell.

**Estimates.** Each `E_i` is a sum of four affine pull-backs in one coordinate,
`x ↦ x` with `xᵢ ↦ λ xᵢ + μ` (`refl`), with polynomial weights in `xᵢ` (`ext1`); the derivatives
of such an operator are operators of the same kind with the weights differentiated or scaled
(`pd_ext1`), and their `L²` bounds follow from the change of variables
`refl_* vol = |λ|⁻¹ vol` (`map_refl_volume`, `eLpNorm_comp_refl_le`, `eLpNorm_ext1_le`,
`n2_ext1_le`). Iterating over the coordinates moves the estimate from `Q` to the boxes of the
shell (`box`, `exists_n2_hest_le`). This is the extension step of the regular decomposition of
`Feec.Models.Cube.RegularDecomposition`; the two-point reflection is the one of [Hestenes1941].

## Main definitions

* `pd`, `refl`, `ext1`, `hest`, `tI`, `rem`, `lift`; `n2`, `In`, `Out`, `box`, `shell`.

## Main results

* `map_refl_volume`, `eLpNorm_comp_refl_le`, `pd_ext1`, `ext1_comm`.
* `hest_of_face`, `pd_hest_of_face`, **`rem_of_face`**, **`pd_rem_of_face`**.
* `eLpNorm_ext1_le`, `n2_ext1_le`, `exists_n2_hest_le`, **`exists_n2_lift_le`**.

## References

* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (extension operators by reflection)
* [M. R. Hestenes, *Extension of the Range of a Differentiable Function*][Hestenes1941]
  (the reflection `hest`)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ENNReal NNReal Topology

namespace Feec.Models.Cube.ShellExtension

/-! ### Partial derivatives and one-coordinate affine maps -/

/-- The partial derivative `∂_j F`. -/
def pd (j : Fin 3) (F : (Fin 3 → ℝ) → ℝ) : (Fin 3 → ℝ) → ℝ :=
  fun x => fderiv ℝ F x (Pi.single j 1)

/-- The affine map `x ↦ x + ((a - 1) xᵢ + b) eᵢ`, acting by `t ↦ a t + b` in the coordinate `i`
and by the identity in the others. -/
def refl (i : Fin 3) (a b : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  x + ((a - 1) * x i + b) • (Pi.single i 1 : Fin 3 → ℝ)

@[simp] theorem refl_apply_self (i : Fin 3) (a b : ℝ) (x : Fin 3 → ℝ) :
    refl i a b x i = a * x i + b := by
  simp only [refl, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  ring

theorem refl_apply_of_ne {i j : Fin 3} (h : j ≠ i) (a b : ℝ) (x : Fin 3 → ℝ) :
    refl i a b x j = x j := by
  simp [refl, Pi.single_eq_of_ne h]

theorem refl_add_single (i j : Fin 3) (a b : ℝ) (x : Fin 3 → ℝ) (s : ℝ) :
    refl i a b (x + Pi.single j s) =
      refl i a b x + Pi.single j ((if j = i then a else 1) * s) := by
  funext k
  simp only [refl, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> subst_vars <;> first | (exfalso; tauto) | ring

theorem refl_comm {i j : Fin 3} (h : i ≠ j) (a b c e : ℝ) (x : Fin 3 → ℝ) :
    refl i a b (refl j c e x) = refl j c e (refl i a b x) := by
  funext k
  by_cases hki : k = i
  · subst hki
    rw [refl_apply_self, refl_apply_of_ne h, refl_apply_of_ne h, refl_apply_self]
  · by_cases hkj : k = j
    · subst hkj
      rw [refl_apply_of_ne hki, refl_apply_self, refl_apply_self, refl_apply_of_ne hki]
    · rw [refl_apply_of_ne hki, refl_apply_of_ne hkj, refl_apply_of_ne hkj, refl_apply_of_ne hki]

theorem refl_of_eq (i : Fin 3) {a b : ℝ} {x : Fin 3 → ℝ} (h : a * x i + b = x i) :
    refl i a b x = x := by
  have : (a - 1) * x i + b = 0 := by linarith
  simp [refl, this]

theorem contDiff_refl (i : Fin 3) (a b : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (refl i a b) := by
  unfold refl; fun_prop

theorem continuous_refl (i : Fin 3) (a b : ℝ) : Continuous (refl i a b) :=
  (contDiff_refl i a b (n := 0)).continuous

/-- The linear part of `refl`: the diagonal matrix with `a` in position `i`. -/
theorem refl_eq_toLin' (i : Fin 3) (a b : ℝ) (x : Fin 3 → ℝ) :
    refl i a b x = Matrix.toLin' (Matrix.diagonal (Function.update (1 : Fin 3 → ℝ) i a)) x +
      Pi.single i b := by
  funext k
  rw [Matrix.toLin'_apply, Pi.add_apply, Matrix.mulVec_diagonal]
  by_cases hk : k = i
  · subst hk; simp
  · rw [refl_apply_of_ne hk, Function.update_of_ne hk, Pi.single_eq_of_ne hk]; simp

/-- **The image measure of `refl`**: `refl_* vol = |a|⁻¹ vol`. -/
theorem map_refl_volume (i : Fin 3) {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Measure.map (refl i a b) volume = ENNReal.ofReal |a⁻¹| • (volume : Measure (Fin 3 → ℝ)) := by
  set L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
    Matrix.toLin' (Matrix.diagonal (Function.update (1 : Fin 3 → ℝ) i a))
  have hdet : LinearMap.det L = a := by
    rw [LinearMap.det_toLin', Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hL : Measurable L := L.continuous_of_finiteDimensional.measurable
  have e : refl i a b = (fun y => y + Pi.single i b) ∘ L := by
    funext x; exact refl_eq_toLin' i a b x
  rw [e, ← Measure.map_map (measurable_add_const _) hL,
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ (hdet.symm ▸ ha), hdet,
    Measure.map_smul, map_add_right_eq_self]
  exact (measurable_add_const _).aemeasurable

/-- **Pull-back by `refl`**: `‖G ∘ refl‖_{L²(B)} ≤ |a|^{-1/2} ‖G‖_{L²(B')}` if `refl (B) ⊆ B'`. -/
theorem eLpNorm_comp_refl_le (i : Fin 3) {a : ℝ} (ha : a ≠ 0) (b : ℝ) {G : (Fin 3 → ℝ) → ℝ}
    (hG : Continuous G) {B B' : Set (Fin 3 → ℝ)} (hB' : MeasurableSet B')
    (h : MapsTo (refl i a b) B B') :
    eLpNorm (G ∘ refl i a b) 2 (volume.restrict B) ≤
      ENNReal.ofReal |a⁻¹| ^ (1 / 2 : ℝ) * eLpNorm G 2 (volume.restrict B') := by
  have hm : Measurable (refl i a b) := (continuous_refl i a b).measurable
  calc eLpNorm (G ∘ refl i a b) 2 (volume.restrict B)
      ≤ eLpNorm (G ∘ refl i a b) 2 (volume.restrict (refl i a b ⁻¹' B')) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono h le_rfl)
    _ = eLpNorm G 2 (Measure.map (refl i a b) (volume.restrict (refl i a b ⁻¹' B'))) :=
        (eLpNorm_map_measure hG.aestronglyMeasurable hm.aemeasurable).symm
    _ = eLpNorm G 2 ((ENNReal.ofReal |a⁻¹| • volume).restrict B') := by
        rw [← Measure.restrict_map hm hB', map_refl_volume i ha b]
    _ = _ := by
        rw [Measure.restrict_smul, eLpNorm_smul_measure_of_ne_top (by norm_num) _ _
          hG.aestronglyMeasurable, smul_eq_mul]
        norm_num

/-! ### Derivatives along coordinate lines -/

theorem hasDerivAt_line {F : (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ} (hF : DifferentiableAt ℝ F y)
    (j : Fin 3) : HasDerivAt (fun s => F (y + Pi.single j s)) (pd j F y) 0 := by
  have hl : HasDerivAt (fun s : ℝ => y + Pi.single j s) (Pi.single j 1) 0 := by
    have : (fun s : ℝ => y + Pi.single j s) =
        fun s => y + s • (Pi.single j (1 : ℝ) : Fin 3 → ℝ) := by
      funext s; rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this]
    simpa using (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ))
      (Pi.single j (1 : ℝ) : Fin 3 → ℝ)).const_add y
  have h := (show HasFDerivAt F (fderiv ℝ F (y + Pi.single j 0)) (y + Pi.single j 0) by
    rw [Pi.single_zero, add_zero]; exact hF.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hl
  simp only [Pi.single_zero, add_zero] at h
  exact h

theorem pd_eq_of_hasDerivAt {F : (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ} (hF : DifferentiableAt ℝ F y)
    {j : Fin 3} {D : ℝ} (h : HasDerivAt (fun s => F (y + Pi.single j s)) D 0) : pd j F y = D :=
  (hasDerivAt_line hF j).unique h

theorem contDiff_pd {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (pd j F) :=
  (hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem pd_add {F G : (Fin 3 → ℝ) → ℝ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (j : Fin 3) : pd j (F + G) = pd j F + pd j G := by
  funext x; simp [pd, fderiv_add (hF x) (hG x)]

theorem pd_sub {F G : (Fin 3 → ℝ) → ℝ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (j : Fin 3) : pd j (F - G) = pd j F - pd j G := by
  funext x; simp [pd, fderiv_sub (hF x) (hG x)]

/-! ### One-coordinate reflection operators with polynomial weights -/

theorem contDiff_eval (P : ℝ[X]) {n : WithTop ℕ∞} : ContDiff ℝ n fun t : ℝ => P.eval t := by
  simpa using P.contDiff_aeval (𝕜 := ℝ) n

/-- The slopes of the four reflections of the Hestenes extension: `t ↦ -t/2`, `t ↦ -t/4` about
`0` and `t ↦ ¾ - t/2`, `t ↦ ⅝ - t/4` about `½`. -/
def lam : Fin 4 → ℝ := ![-1 / 2, -1 / 4, -1 / 2, -1 / 4]

/-- The offsets of the four reflections. -/
def mu : Fin 4 → ℝ := ![0, 0, 3 / 4, 5 / 8]

theorem lam_ne_zero (m : Fin 4) : lam m ≠ 0 := by fin_cases m <;> norm_num [lam]

/-- A reflection operator in the coordinate `i` with polynomial weights `ω`:
`(R F)(x) = Σₘ ωₘ(xᵢ) F(x with xᵢ ↦ λₘ xᵢ + μₘ)`. -/
def ext1 (i : Fin 3) (ω : Fin 4 → ℝ[X]) (F : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ m, (ω m).eval (x i) * F (refl i (lam m) (mu m) x)

theorem contDiff_ext1 (i : Fin 3) (ω : Fin 4 → ℝ[X]) {F : (Fin 3 → ℝ) → ℝ} {n : WithTop ℕ∞}
    (hF : ContDiff ℝ n F) : ContDiff ℝ n (ext1 i ω F) := by
  unfold ext1
  exact ContDiff.sum fun m _ =>
    ((contDiff_eval (ω m)).comp (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) i)).mul
    (hF.comp (contDiff_refl _ _ _))

/-- Weights of the term with the weight differentiated. -/
def dω (j i : Fin 3) (ω : Fin 4 → ℝ[X]) : Fin 4 → ℝ[X] :=
  fun m => if j = i then derivative (ω m) else 0

/-- Weights of the term with `F` differentiated (chain-rule factor `λₘ` if `j = i`). -/
def cω (j i : Fin 3) (ω : Fin 4 → ℝ[X]) : Fin 4 → ℝ[X] :=
  fun m => if j = i then C (lam m) * ω m else ω m

/-- **The derivative of a reflection operator**:
`∂ⱼ (R_ω F) = R_{dω} F + R_{cω} (∂ⱼ F)`. -/
theorem pd_ext1 (i j : Fin 3) (ω : Fin 4 → ℝ[X]) {F : (Fin 3 → ℝ) → ℝ}
    (hF : Differentiable ℝ F) :
    pd j (ext1 i ω F) = ext1 i (dω j i ω) F + ext1 i (cω j i ω) (pd j F) := by
  funext x
  have hd : Differentiable ℝ (ext1 i ω F) := by
    unfold ext1
    exact Differentiable.fun_sum fun m _ =>
      (((ω m).differentiable).comp (differentiable_apply i)).mul (hF.comp
        ((contDiff_refl i _ _ (n := 1)).differentiable one_ne_zero))
  refine pd_eq_of_hasDerivAt (hd x) ?_
  have hsi : ∀ s : ℝ, (Pi.single j s : Fin 3 → ℝ) i = s * (Pi.single j (1 : ℝ) : Fin 3 → ℝ) i :=
    fun s => by rw [← smul_eq_mul, ← Pi.smul_apply, ← Pi.single_smul, smul_eq_mul, mul_one]
  have key : ∀ m, HasDerivAt (fun s : ℝ => (ω m).eval ((x + Pi.single j s : Fin 3 → ℝ) i) *
      F (refl i (lam m) (mu m) (x + Pi.single j s)))
      ((dω j i ω m).eval (x i) * F (refl i (lam m) (mu m) x) +
        (cω j i ω m).eval (x i) * pd j F (refl i (lam m) (mu m) x)) 0 := by
    intro m
    have h1 : HasDerivAt (fun s : ℝ => (ω m).eval ((x + Pi.single j s : Fin 3 → ℝ) i))
        ((derivative (ω m)).eval (x i) * (Pi.single j (1 : ℝ) : Fin 3 → ℝ) i) 0 := by
      have hlin : HasDerivAt (fun s : ℝ => x i + s * (Pi.single j (1 : ℝ) : Fin 3 → ℝ) i)
          ((Pi.single j (1 : ℝ) : Fin 3 → ℝ) i) 0 := by
        simpa using (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ)) _).const_add (x i)
      have := ((ω m).hasDerivAt (x i + 0 * (Pi.single j (1 : ℝ) : Fin 3 → ℝ) i)).comp
        (0 : ℝ) hlin
      simp only [zero_mul, add_zero] at this
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
      simp [hsi s]
    have h2 : HasDerivAt (fun s : ℝ => F (refl i (lam m) (mu m) (x + Pi.single j s)))
        ((if j = i then lam m else 1) * pd j F (refl i (lam m) (mu m) x)) 0 := by
      have hl := hasDerivAt_line (hF (refl i (lam m) (mu m) x)) j
      have hc : HasDerivAt (fun s : ℝ => (if j = i then lam m else 1) * s)
          (if j = i then lam m else 1) 0 := by
        simpa using HasDerivAt.const_mul (if j = i then lam m else 1) (hasDerivAt_id (0 : ℝ))
      have := (show HasDerivAt (fun s => F (refl i (lam m) (mu m) x + Pi.single j s))
          (pd j F (refl i (lam m) (mu m) x)) ((if j = i then lam m else 1) * 0) by
        rw [mul_zero]; exact hl).comp (0 : ℝ) hc
      refine (this.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).congr_deriv
        (by ring)
      simp only [Function.comp_apply, refl_add_single]
    have := h1.mul h2
    simp only [Pi.single_zero, add_zero] at this
    refine this.congr_deriv ?_
    simp only [dω, cω]
    by_cases hji : j = i
    · subst hji; simp; ring
    · simp [hji]
  have := HasDerivAt.fun_sum (u := Finset.univ) fun m _ => key m
  simp only [Pi.add_apply, ext1, Finset.sum_add_distrib] at this ⊢
  exact this

theorem ext1_sub (i : Fin 3) (ω : Fin 4 → ℝ[X]) (F G : (Fin 3 → ℝ) → ℝ) :
    ext1 i ω (F - G) = ext1 i ω F - ext1 i ω G := by
  funext x; simp [ext1, mul_sub, Finset.sum_sub_distrib]

theorem ext1_add (i : Fin 3) (ω : Fin 4 → ℝ[X]) (F G : (Fin 3 → ℝ) → ℝ) :
    ext1 i ω (F + G) = ext1 i ω F + ext1 i ω G := by
  funext x; simp [ext1, mul_add, Finset.sum_add_distrib]

theorem ext1_zero_weight (i : Fin 3) (F : (Fin 3 → ℝ) → ℝ) : ext1 i (fun _ => 0) F = 0 := by
  funext x; simp [ext1]

/-- **Reflection operators in different coordinates commute.** -/
theorem ext1_comm {i j : Fin 3} (h : i ≠ j) (ω ω' : Fin 4 → ℝ[X]) (F : (Fin 3 → ℝ) → ℝ) :
    ext1 i ω (ext1 j ω' F) = ext1 j ω' (ext1 i ω F) := by
  funext x
  simp only [ext1, Finset.mul_sum, refl_apply_of_ne h, refl_apply_of_ne (Ne.symm h)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  rw [refl_comm h]
  ring

/-! ### The Hestenes extension -/

/-- The cubic Hermite blend `h(t) = 1 - 12 t² + 16 t³`: `h(0) = 1`, `h(½) = 0`,
`h'(0) = h'(½) = 0`. -/
def herm : ℝ[X] := 1 - C 12 * X ^ 2 + C 16 * X ^ 3

/-- The reversed blend `h(½ - t)`. -/
def hermR : ℝ[X] := herm.comp (C (1 / 2) - X)

/-- The Hestenes weights: `-5 h`, `6 h` on the reflections about `0`, `-5 h(½ - ·)`, `6 h(½ - ·)`
on the reflections about `½`. -/
def ωE : Fin 4 → ℝ[X] := ![C (-5) * herm, C 6 * herm, C (-5) * hermR, C 6 * hermR]

/-- **The Hestenes extension** in the coordinate `i` ([Hestenes1941]):
`E_i F (x) = h(xᵢ) (-5 F(-xᵢ/2) + 6 F(-xᵢ/4)) + h(½ - xᵢ) (-5 F(¾ - xᵢ/2) + 6 F(⅝ - xᵢ/4))`
(the other coordinates fixed). On the faces `xᵢ ∈ {0, ½}` it reproduces the value and the first
derivatives of `F` (`hest_of_face`, `pd_hest_of_face`); for `xᵢ ∈ (0, ½)` it only samples `F`
at points with `xᵢ ∈ (-¼, 0) ∪ (½, ¾)`. -/
def hest (i : Fin 3) (F : (Fin 3 → ℝ) → ℝ) : (Fin 3 → ℝ) → ℝ := ext1 i ωE F

@[simp] theorem herm_eval_zero : herm.eval 0 = 1 := by simp [herm]
@[simp] theorem herm_eval_half : herm.eval 2⁻¹ = 0 := by simp [herm]; norm_num
@[simp] theorem hermR_eval_zero : hermR.eval 0 = 0 := by simp [hermR, herm]; norm_num
@[simp] theorem hermR_eval_half : hermR.eval 2⁻¹ = 1 := by simp [hermR, herm]
@[simp] theorem herm_deriv_eval_zero : (derivative herm).eval 0 = 0 := by simp [herm]
@[simp] theorem herm_deriv_eval_half : (derivative herm).eval 2⁻¹ = 0 := by
  simp [herm]; norm_num
@[simp] theorem hermR_deriv_eval_zero : (derivative hermR).eval 0 = 0 := by
  simp [hermR, herm, derivative_pow]; norm_num
@[simp] theorem hermR_deriv_eval_half : (derivative hermR).eval 2⁻¹ = 0 := by
  simp [hermR, herm, derivative_pow]

theorem refl_zero_of_face0 {i : Fin 3} {x : Fin 3 → ℝ} (h : x i = 0) (m : Fin 4) (hm : m.val < 2) :
    refl i (lam m) (mu m) x = x := by
  refine refl_of_eq i ?_
  rw [h]
  fin_cases m <;> simp_all [mu]

theorem refl_zero_of_face1 {i : Fin 3} {x : Fin 3 → ℝ} (h : x i = 1 / 2) (m : Fin 4)
    (hm : 2 ≤ m.val) : refl i (lam m) (mu m) x = x := by
  refine refl_of_eq i ?_
  rw [h]
  fin_cases m <;> simp_all [lam, mu] <;> norm_num

/-- **The Hestenes extension reproduces the value on the faces.** -/
theorem hest_of_face {i : Fin 3} {x : Fin 3 → ℝ} (h : x i = 0 ∨ x i = 1 / 2)
    (F : (Fin 3 → ℝ) → ℝ) : hest i F x = F x := by
  simp only [hest, ext1, Fin.sum_univ_four]
  rcases h with h | h
  · rw [refl_zero_of_face0 h 0 (by decide), refl_zero_of_face0 h 1 (by decide), h]
    simp [ωE]
    ring
  · rw [refl_zero_of_face1 h 2 (by decide), refl_zero_of_face1 h 3 (by decide), h]
    simp [ωE]
    ring

/-- **The Hestenes extension reproduces the first derivatives on the faces.** -/
theorem pd_hest_of_face {i : Fin 3} {x : Fin 3 → ℝ} (h : x i = 0 ∨ x i = 1 / 2)
    {F : (Fin 3 → ℝ) → ℝ} (hF : Differentiable ℝ F) (j : Fin 3) :
    pd j (hest i F) x = pd j F x := by
  rw [hest, pd_ext1 i j ωE hF, Pi.add_apply]
  by_cases hji : j = i
  · subst hji
    simp only [ext1, dω, cω, ite_true, Fin.sum_univ_four]
    rcases h with h | h
    · rw [refl_zero_of_face0 h 0 (by decide), refl_zero_of_face0 h 1 (by decide), h]
      simp [ωE, lam]
      ring
    · rw [refl_zero_of_face1 h 2 (by decide), refl_zero_of_face1 h 3 (by decide), h]
      simp [ωE, lam]
      ring
  · have h0 : dω j i ωE = fun _ => 0 := by funext m; simp [dω, hji]
    have h1 : cω j i ωE = ωE := by funext m; simp [cω, hji]
    rw [h0, h1, ext1_zero_weight, Pi.zero_apply, zero_add]
    exact hest_of_face h _

theorem contDiff_hest (i : Fin 3) {F : (Fin 3 → ℝ) → ℝ} {n : WithTop ℕ∞} (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (hest i F) := contDiff_ext1 i ωE hF

/-! ### The extension `s = q - (I - E₀)(I - E₁)(I - E₂) q` -/

/-- `T_i = I - E_i`: kills the value and the first derivatives on the faces `xᵢ ∈ {0, ½}`. -/
def tI (i : Fin 3) (F : (Fin 3 → ℝ) → ℝ) : (Fin 3 → ℝ) → ℝ := F - hest i F

theorem tI_comm {i j : Fin 3} (h : i ≠ j) (F : (Fin 3 → ℝ) → ℝ) :
    tI i (tI j F) = tI j (tI i F) := by
  simp only [tI, hest, ext1_sub, ext1_comm h]
  abel

theorem contDiff_tI (i : Fin 3) {F : (Fin 3 → ℝ) → ℝ} {n : WithTop ℕ∞} (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (tI i F) := hF.sub (contDiff_hest i hF)

theorem tI_of_face {i : Fin 3} {x : Fin 3 → ℝ} (h : x i = 0 ∨ x i = 1 / 2)
    (F : (Fin 3 → ℝ) → ℝ) : tI i F x = 0 := by
  simp [tI, hest_of_face h]

theorem pd_tI_of_face {i : Fin 3} {x : Fin 3 → ℝ} (h : x i = 0 ∨ x i = 1 / 2)
    {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) (j : Fin 3) : pd j (tI i F) x = 0 := by
  have hd := hF.differentiable one_ne_zero
  rw [tI, pd_sub hd ((contDiff_hest i hF).differentiable one_ne_zero), Pi.sub_apply,
    pd_hest_of_face h hd, sub_self]

/-- The remainder `r = (I - E₀)(I - E₁)(I - E₂) q`. -/
def rem (q : (Fin 3 → ℝ) → ℝ) : (Fin 3 → ℝ) → ℝ := tI 0 (tI 1 (tI 2 q))

/-- **The shell extension** `s = q - r`: on `Q` it depends only on the values of `q` on the
shell (`n2_lift_le`), and on `∂Q` it agrees with `q` together with its first derivatives
(`rem_of_face`, `pd_rem_of_face`). -/
def lift (q : (Fin 3 → ℝ) → ℝ) : (Fin 3 → ℝ) → ℝ := q - rem q

theorem contDiff_rem {q : (Fin 3 → ℝ) → ℝ} {n : WithTop ℕ∞} (hq : ContDiff ℝ n q) :
    ContDiff ℝ n (rem q) := contDiff_tI 0 (contDiff_tI 1 (contDiff_tI 2 hq))

theorem contDiff_lift {q : (Fin 3 → ℝ) → ℝ} {n : WithTop ℕ∞} (hq : ContDiff ℝ n q) :
    ContDiff ℝ n (lift q) := hq.sub (contDiff_rem hq)

theorem rem_eq_tI1 (q : (Fin 3 → ℝ) → ℝ) : rem q = tI 1 (tI 0 (tI 2 q)) :=
  tI_comm (by decide) _

theorem rem_eq_tI2 (q : (Fin 3 → ℝ) → ℝ) : rem q = tI 2 (tI 0 (tI 1 q)) := by
  rw [rem, tI_comm (show (1 : Fin 3) ≠ 2 by decide), tI_comm (show (0 : Fin 3) ≠ 2 by decide)]

/-- The faces of `Q` (as hyperplanes): `xᵢ ∈ {0, ½}` for some `i`. -/
def OnFace (x : Fin 3 → ℝ) : Prop := ∃ i, x i = 0 ∨ x i = 1 / 2

/-- **The remainder vanishes on the faces.** -/
theorem rem_of_face {x : Fin 3 → ℝ} (hx : OnFace x) (q : (Fin 3 → ℝ) → ℝ) : rem q x = 0 := by
  obtain ⟨i, hi⟩ := hx
  fin_cases i
  · exact tI_of_face hi _
  · rw [rem_eq_tI1]; exact tI_of_face hi _
  · rw [rem_eq_tI2]; exact tI_of_face hi _

/-- **The first derivatives of the remainder vanish on the faces.** -/
theorem pd_rem_of_face {x : Fin 3 → ℝ} (hx : OnFace x) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ 1 q) (j : Fin 3) : pd j (rem q) x = 0 := by
  obtain ⟨i, hi⟩ := hx
  fin_cases i
  · exact pd_tI_of_face hi (contDiff_tI 1 (contDiff_tI 2 hq)) j
  · rw [rem_eq_tI1]; exact pd_tI_of_face hi (contDiff_tI 0 (contDiff_tI 2 hq)) j
  · rw [rem_eq_tI2]; exact pd_tI_of_face hi (contDiff_tI 0 (contDiff_tI 1 hq)) j

/-! ### `L²` estimates -/

/-- `‖F‖ + Σⱼ ‖∂ⱼF‖ + Σⱼₖ ‖∂ₖ∂ⱼF‖` in `L²(B)` (a quantity equivalent to the `H²(B)` norm). -/
def n2 (F : (Fin 3 → ℝ) → ℝ) (B : Set (Fin 3 → ℝ)) : ℝ≥0∞ :=
  eLpNorm F 2 (volume.restrict B) + ∑ j, eLpNorm (pd j F) 2 (volume.restrict B) +
    ∑ j, ∑ k, eLpNorm (pd k (pd j F)) 2 (volume.restrict B)

theorem n2_mono (F : (Fin 3 → ℝ) → ℝ) {B B' : Set (Fin 3 → ℝ)} (h : B ⊆ B') :
    n2 F B ≤ n2 F B' := by
  have hm : ∀ G : (Fin 3 → ℝ) → ℝ, eLpNorm G 2 (volume.restrict B) ≤
      eLpNorm G 2 (volume.restrict B') := fun G =>
    eLpNorm_mono_measure _ (Measure.restrict_mono h le_rfl)
  unfold n2
  exact add_le_add (add_le_add (hm _) (Finset.sum_le_sum fun j _ => hm _))
    (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hm _)

theorem eLpNorm_le_n2 (F : (Fin 3 → ℝ) → ℝ) (B : Set (Fin 3 → ℝ)) :
    eLpNorm F 2 (volume.restrict B) ≤ n2 F B := by
  unfold n2; rw [add_assoc]; exact le_self_add

theorem eLpNorm_pd_le_n2 (F : (Fin 3 → ℝ) → ℝ) (B : Set (Fin 3 → ℝ)) (j : Fin 3) :
    eLpNorm (pd j F) 2 (volume.restrict B) ≤ n2 F B := by
  unfold n2
  calc eLpNorm (pd j F) 2 (volume.restrict B)
      ≤ ∑ j, eLpNorm (pd j F) 2 (volume.restrict B) :=
        Finset.single_le_sum (f := fun j => eLpNorm (pd j F) 2 (volume.restrict B))
          (fun _ _ => zero_le) (Finset.mem_univ j)
    _ ≤ _ := le_add_self.trans le_self_add

theorem eLpNorm_pd_pd_le_n2 (F : (Fin 3 → ℝ) → ℝ) (B : Set (Fin 3 → ℝ)) (j k : Fin 3) :
    eLpNorm (pd k (pd j F)) 2 (volume.restrict B) ≤ n2 F B := by
  unfold n2
  calc eLpNorm (pd k (pd j F)) 2 (volume.restrict B)
      ≤ ∑ k, eLpNorm (pd k (pd j F)) 2 (volume.restrict B) :=
        Finset.single_le_sum (f := fun k => eLpNorm (pd k (pd j F)) 2 (volume.restrict B))
          (fun _ _ => zero_le) (Finset.mem_univ k)
    _ ≤ ∑ j, ∑ k, eLpNorm (pd k (pd j F)) 2 (volume.restrict B) :=
        Finset.single_le_sum (f := fun j => ∑ k, eLpNorm (pd k (pd j F)) 2 (volume.restrict B))
          (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ _ := le_add_self

theorem n2_add_le {F G : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (B : Set (Fin 3 → ℝ)) : n2 (F + G) B ≤ n2 F B + n2 G B := by
  have d1 : ∀ {H : (Fin 3 → ℝ) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) H → Differentiable ℝ H := fun h =>
    h.differentiable (by simp)
  have e1 : ∀ j, pd j (F + G) = pd j F + pd j G := fun j => pd_add (d1 hF) (d1 hG) j
  have e2 : ∀ j k, pd k (pd j F + pd j G) = pd k (pd j F) + pd k (pd j G) :=
    fun j k => pd_add (d1 (contDiff_pd hF j)) (d1 (contDiff_pd hG j)) k
  unfold n2
  simp only [e1, e2]
  calc _ ≤ (eLpNorm F 2 (volume.restrict B) + eLpNorm G 2 (volume.restrict B)) +
        ∑ j, (eLpNorm (pd j F) 2 (volume.restrict B) + eLpNorm (pd j G) 2 (volume.restrict B)) +
        ∑ j, ∑ k, (eLpNorm (pd k (pd j F)) 2 (volume.restrict B) +
          eLpNorm (pd k (pd j G)) 2 (volume.restrict B)) := by
        gcongr with j _ j _ k _
        · exact eLpNorm_add_le one_le_two
        · exact eLpNorm_add_le one_le_two
        · exact eLpNorm_add_le one_le_two
    _ = _ := by
        simp only [Finset.sum_add_distrib]
        ring

theorem n2_sub_le {F G : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (B : Set (Fin 3 → ℝ)) : n2 (F - G) B ≤ n2 F B + n2 G B := by
  have d1 : ∀ {H : (Fin 3 → ℝ) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) H → Differentiable ℝ H := fun h =>
    h.differentiable (by simp)
  have e1 : ∀ j, pd j (F - G) = pd j F - pd j G := fun j => pd_sub (d1 hF) (d1 hG) j
  have e2 : ∀ j k, pd k (pd j F - pd j G) = pd k (pd j F) - pd k (pd j G) :=
    fun j k => pd_sub (d1 (contDiff_pd hF j)) (d1 (contDiff_pd hG j)) k
  unfold n2
  simp only [e1, e2]
  calc _ ≤ (eLpNorm F 2 (volume.restrict B) + eLpNorm G 2 (volume.restrict B)) +
        ∑ j, (eLpNorm (pd j F) 2 (volume.restrict B) + eLpNorm (pd j G) 2 (volume.restrict B)) +
        ∑ j, ∑ k, (eLpNorm (pd k (pd j F)) 2 (volume.restrict B) +
          eLpNorm (pd k (pd j G)) 2 (volume.restrict B)) := by
        gcongr with j _ j _ k _
        · exact eLpNorm_sub_le one_le_two
        · exact eLpNorm_sub_le one_le_two
        · exact eLpNorm_sub_le one_le_two
    _ = _ := by
        simp only [Finset.sum_add_distrib]
        ring

/-- A bound `M` for a weight family on `[0, ½]`. -/
def Bd (ω : Fin 4 → ℝ[X]) (M : ℝ≥0) : Prop := ∀ m, ∀ t ∈ Icc (0 : ℝ) (1 / 2), |(ω m).eval t| ≤ M

theorem exists_bd (ω : Fin 4 → ℝ[X]) : ∃ M, Bd ω M := by
  have h : ∀ m, ∃ M : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) (1 / 2), |(ω m).eval t| ≤ M := fun m => by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((ω m).continuous.continuousOn (s := Icc (0 : ℝ) (1 / 2)))
    exact ⟨M.toNNReal, fun t ht => (hM t ht).trans (le_max_left _ _)⟩
  choose M hM using h
  refine ⟨∑ m, M m, fun m t ht => (hM m t ht).trans ?_⟩
  exact_mod_cast Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ m)

theorem Bd.mono {ω : Fin 4 → ℝ[X]} {M M' : ℝ≥0} (h : Bd ω M) (hM : M ≤ M') : Bd ω M' :=
  fun m t ht => (h m t ht).trans (by exact_mod_cast hM)

/-- Termwise derivatives of a weight family. -/
def Dω (ω : Fin 4 → ℝ[X]) : Fin 4 → ℝ[X] := fun m => derivative (ω m)

theorem abs_lam_le (m : Fin 4) : |lam m| ≤ 1 := by
  fin_cases m <;> norm_num [lam, abs_of_neg]

theorem Bd.cω {ω : Fin 4 → ℝ[X]} {M : ℝ≥0} (h : Bd ω M) (j i : Fin 3) : Bd (cω j i ω) M := by
  intro m t ht
  simp only [ShellExtension.cω]
  split_ifs
  · rw [eval_mul, eval_C, abs_mul]
    calc |lam m| * |(ω m).eval t| ≤ 1 * M :=
          mul_le_mul (abs_lam_le m) (h m t ht) (abs_nonneg _) zero_le_one
      _ = M := one_mul _
  · exact h m t ht

theorem Bd.dω {ω : Fin 4 → ℝ[X]} {M : ℝ≥0} (h : Bd (Dω ω) M) (j i : Fin 3) :
    Bd (dω j i ω) M := by
  intro m t ht
  simp only [ShellExtension.dω]
  split_ifs
  · exact h m t ht
  · simp

theorem Dω_cω (ω : Fin 4 → ℝ[X]) (j i : Fin 3) : Dω (cω j i ω) = cω j i (Dω ω) := by
  funext m; simp only [Dω, cω]; split_ifs <;> simp

theorem Dω_dω (ω : Fin 4 → ℝ[X]) (j i : Fin 3) : Dω (dω j i ω) = dω j i (Dω ω) := by
  funext m; simp only [Dω, dω]; split_ifs <;> simp

theorem eLpNorm_four_le {M : ℝ≥0} (m : Fin 4) :
    (M : ℝ≥0∞) * ENNReal.ofReal |(lam m)⁻¹| ^ (1 / 2 : ℝ) ≤ 2 * M := by
  rw [mul_comm]
  gcongr
  have h4 : |(lam m)⁻¹| ≤ 4 := by fin_cases m <;> norm_num [lam, abs_of_neg]
  calc ENNReal.ofReal |(lam m)⁻¹| ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal 4 ^ (1 / 2 : ℝ) := by
        gcongr
    _ = 2 := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num),
          show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num

/-- **`L²` estimate of a reflection operator**: `‖R_ω G‖_{L²(B)} ≤ 8 M ‖G‖_{L²(B')}` when the
four reflections map `B` into `B'` and the weights are bounded by `M` on `[0, ½]`. -/
theorem eLpNorm_ext1_le (i : Fin 3) {ω : Fin 4 → ℝ[X]} {M : ℝ≥0} (hM : Bd ω M)
    {G : (Fin 3 → ℝ) → ℝ} (hG : Continuous G) {B B' : Set (Fin 3 → ℝ)} (hB : MeasurableSet B)
    (hB' : MeasurableSet B') (hBi : ∀ x ∈ B, x i ∈ Icc (0 : ℝ) (1 / 2))
    (hmaps : ∀ m, MapsTo (refl i (lam m) (mu m)) B B') :
    eLpNorm (ext1 i ω G) 2 (volume.restrict B) ≤ 8 * M * eLpNorm G 2 (volume.restrict B') := by
  have e : ext1 i ω G = ∑ m, fun x => (ω m).eval (x i) * G (refl i (lam m) (mu m) x) := by
    funext x; simp [ext1]
  rw [e]
  refine (eLpNorm_sum_le one_le_two).trans ?_
  have hterm : ∀ m, eLpNorm (fun x => (ω m).eval (x i) * G (refl i (lam m) (mu m) x)) 2
      (volume.restrict B) ≤ 2 * M * eLpNorm G 2 (volume.restrict B') := by
    intro m
    have hc : Continuous fun x : Fin 3 → ℝ => (ω m).eval (x i) * G (refl i (lam m) (mu m) x) :=
      ((ω m).continuous.comp (continuous_apply i)).mul (hG.comp (continuous_refl _ _ _))
    calc eLpNorm (fun x => (ω m).eval (x i) * G (refl i (lam m) (mu m) x)) 2 (volume.restrict B)
        ≤ M • eLpNorm (G ∘ refl i (lam m) (mu m)) 2 (volume.restrict B) := by
          refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hc.aestronglyMeasurable ?_ 2
          refine ae_restrict_of_forall_mem hB fun x hx => ?_
          rw [nnnorm_mul, Function.comp_apply]
          gcongr
          rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
          exact hM m _ (hBi x hx)
      _ ≤ M * (ENNReal.ofReal |(lam m)⁻¹| ^ (1 / 2 : ℝ) * eLpNorm G 2 (volume.restrict B')) := by
          rw [ENNReal.smul_def, smul_eq_mul]
          gcongr
          exact eLpNorm_comp_refl_le i (lam_ne_zero m) (mu m) hG hB' (hmaps m)
      _ ≤ 2 * M * eLpNorm G 2 (volume.restrict B') := by
          rw [← mul_assoc]
          exact mul_le_mul' (eLpNorm_four_le m) le_rfl
  calc ∑ m, eLpNorm (fun x => (ω m).eval (x i) * G (refl i (lam m) (mu m) x)) 2
        (volume.restrict B) ≤ ∑ _m : Fin 4, 2 * M * eLpNorm G 2 (volume.restrict B') :=
        Finset.sum_le_sum fun m _ => hterm m
    _ = 8 * M * eLpNorm G 2 (volume.restrict B') := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- **`H²`-type estimate of a reflection operator**:
`n2 (R_ω G) B ≤ 43 · 8 M · n2 G B'` when `ω`, `ω'`, `ω''` are bounded by `M` on `[0, ½]`. -/
theorem n2_ext1_le (i : Fin 3) {ω : Fin 4 → ℝ[X]} {M : ℝ≥0} (h0 : Bd ω M) (h1 : Bd (Dω ω) M)
    (h2 : Bd (Dω (Dω ω)) M) {G : (Fin 3 → ℝ) → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    {B B' : Set (Fin 3 → ℝ)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hBi : ∀ x ∈ B, x i ∈ Icc (0 : ℝ) (1 / 2))
    (hmaps : ∀ m, MapsTo (refl i (lam m) (mu m)) B B') :
    n2 (ext1 i ω G) B ≤ 43 * (8 * M) * n2 G B' := by
  set K : ℝ≥0∞ := 8 * M
  have d1 : ∀ {H : (Fin 3 → ℝ) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) H → Differentiable ℝ H := fun h =>
    h.differentiable (by simp)
  have est : ∀ {ρ : Fin 4 → ℝ[X]}, Bd ρ M → ∀ {H : (Fin 3 → ℝ) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) H →
      eLpNorm (ext1 i ρ H) 2 (volume.restrict B) ≤ K * eLpNorm H 2 (volume.restrict B') :=
    fun hρ _ hH => eLpNorm_ext1_le i hρ hH.continuous hB hB' hBi hmaps
  have hGj : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (pd j G) := contDiff_pd hG
  set N := n2 G B'
  have T0 : eLpNorm (ext1 i ω G) 2 (volume.restrict B) ≤ K * N :=
    (est h0 hG).trans (by gcongr; exact eLpNorm_le_n2 G B')
  have T1 : ∀ j, eLpNorm (pd j (ext1 i ω G)) 2 (volume.restrict B) ≤ 2 * K * N := by
    intro j
    rw [pd_ext1 i j ω (d1 hG)]
    refine (eLpNorm_add_le one_le_two).trans ?_
    calc _ ≤ K * N + K * N := add_le_add
          ((est (h1.dω j i) hG).trans (by gcongr; exact eLpNorm_le_n2 G B'))
          ((est (h0.cω j i) (hGj j)).trans (by gcongr; exact eLpNorm_pd_le_n2 G B' j))
      _ = 2 * K * N := by ring
  have T2 : ∀ j k, eLpNorm (pd k (pd j (ext1 i ω G))) 2 (volume.restrict B) ≤ 4 * K * N := by
    intro j k
    rw [pd_ext1 i j ω (d1 hG), pd_add (d1 (contDiff_ext1 i _ hG)) (d1 (contDiff_ext1 i _ (hGj j))),
      pd_ext1 i k _ (d1 hG), pd_ext1 i k _ (d1 (hGj j))]
    have b1 : Bd (dω k i (dω j i ω)) M := by
      refine Bd.dω ?_ k i; rw [Dω_dω]; exact h2.dω j i
    have b2 : Bd (cω k i (dω j i ω)) M := (h1.dω j i).cω k i
    have b3 : Bd (dω k i (cω j i ω)) M := by
      refine Bd.dω ?_ k i; rw [Dω_cω]; exact h1.cω j i
    have b4 : Bd (cω k i (cω j i ω)) M := (h0.cω j i).cω k i
    refine (eLpNorm_add_le one_le_two).trans ?_
    refine (add_le_add (eLpNorm_add_le one_le_two) (eLpNorm_add_le one_le_two)).trans ?_
    calc _ ≤ (K * N + K * N) + (K * N + K * N) := add_le_add (add_le_add
          ((est b1 hG).trans (by gcongr; exact eLpNorm_le_n2 G B'))
          ((est b2 (hGj k)).trans (by gcongr; exact eLpNorm_pd_le_n2 G B' k)))
          (add_le_add ((est b3 (hGj j)).trans (by gcongr; exact eLpNorm_pd_le_n2 G B' j))
          ((est b4 (contDiff_pd (hGj j) k)).trans
            (by gcongr; exact eLpNorm_pd_pd_le_n2 G B' j k)))
      _ = 4 * K * N := by ring
  unfold n2
  calc _ ≤ K * N + ∑ _j : Fin 3, 2 * K * N + ∑ _j : Fin 3, ∑ _k : Fin 3, 4 * K * N :=
        add_le_add (add_le_add T0 (Finset.sum_le_sum fun j _ => T1 j))
          (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => T2 j k)
    _ = 43 * K * N := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

theorem exists_bd_hest : ∃ M, Bd ωE M ∧ Bd (Dω ωE) M ∧ Bd (Dω (Dω ωE)) M := by
  obtain ⟨M0, h0⟩ := exists_bd ωE
  obtain ⟨M1, h1⟩ := exists_bd (Dω ωE)
  obtain ⟨M2, h2⟩ := exists_bd (Dω (Dω ωE))
  exact ⟨M0 + M1 + M2, h0.mono (by simp [add_assoc]), h1.mono (by
    rw [add_comm M0, add_assoc]; exact le_self_add), h2.mono le_add_self⟩

/-! ### The boxes around `Q` and the shell -/

/-- The inner interval `(0, ½)`. -/
def In : Set ℝ := Ioo 0 (1 / 2)

/-- The two outer intervals `(-¼, 0) ∪ (½, ¾)`. -/
def Out : Set ℝ := Ioo (-1 / 4) 0 ∪ Ioo (1 / 2) (3 / 4)

/-- The box with the outer intervals in the coordinates `P j = true`. -/
def box (P : Fin 3 → Bool) : Set (Fin 3 → ℝ) := univ.pi fun j => if P j then Out else In

/-- **The shell** `(-¼, ¾)³ ∖ [0, ½]³` around the cube. -/
def shell : Set (Fin 3 → ℝ) := {x | (∀ i, x i ∈ Ioo (-1 / 4) (3 / 4)) ∧ ∃ i, x i ∉ Icc 0 (1 / 2)}

theorem mem_box {P : Fin 3 → Bool} {x : Fin 3 → ℝ} :
    x ∈ box P ↔ ∀ j, x j ∈ if P j = true then Out else In := by
  simp [box, Set.mem_pi]

theorem measurableSet_box (P : Fin 3 → Bool) : MeasurableSet (box P) :=
  MeasurableSet.univ_pi fun j => by
    split_ifs
    · exact measurableSet_Ioo.union measurableSet_Ioo
    · exact measurableSet_Ioo

theorem box_false : box (fun _ => false) = univ.pi fun _ => Ioo (0 : ℝ) (1 / 2) := by
  simp [box, In]

theorem box_subset_shell {P : Fin 3 → Bool} (h : ∃ i, P i = true) : box P ⊆ shell := by
  intro x hx
  have hx' := mem_box.1 hx
  refine ⟨fun j => ?_, ?_⟩
  · have := hx' j
    split_ifs at this
    · rcases this with h | h
      · exact ⟨h.1, by linarith [h.2]⟩
      · exact ⟨by linarith [h.1], h.2⟩
    · exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · obtain ⟨i, hi⟩ := h
    refine ⟨i, fun hc => ?_⟩
    have := hx' i
    rw [hi, ite_eq_left rfl] at this
    rcases this with h | h
    · linarith [h.2, hc.1]
    · linarith [h.1, hc.2]

theorem mem_In_of_box {P : Fin 3 → Bool} {i : Fin 3} (hP : P i = false) {x : Fin 3 → ℝ}
    (hx : x ∈ box P) : x i ∈ Icc (0 : ℝ) (1 / 2) := by
  have := mem_box.1 hx i
  rw [hP] at this
  exact ⟨this.1.le, this.2.le⟩

theorem mapsTo_refl_box {P : Fin 3 → Bool} {i : Fin 3} (hP : P i = false) (m : Fin 4) :
    MapsTo (refl i (lam m) (mu m)) (box P) (box (Function.update P i true)) := by
  intro x hx
  rw [mem_box] at hx ⊢
  intro j
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self, ite_eq_left rfl, refl_apply_self]
    have := hx j
    rw [hP] at this
    obtain ⟨h1, h2⟩ := this
    fin_cases m
    · left; constructor <;> simp [lam, mu] <;> linarith
    · left; constructor <;> simp [lam, mu] <;> linarith
    · right; constructor <;> simp [lam, mu] <;> linarith
    · right; constructor <;> simp [lam, mu] <;> linarith
  · rw [Function.update_of_ne hji, refl_apply_of_ne hji]
    exact hx j

/-- **`H²` estimate of the Hestenes extension on a box**: from `xᵢ ∈ (0, ½)` to
`xᵢ ∈ (-¼, 0) ∪ (½, ¾)`. -/
theorem exists_n2_hest_le : ∃ C : ℝ≥0, ∀ (i : Fin 3) {G : (Fin 3 → ℝ) → ℝ},
    ContDiff ℝ (⊤ : ℕ∞) G → ∀ {P : Fin 3 → Bool}, P i = false →
      n2 (hest i G) (box P) ≤ C * n2 G (box (Function.update P i true)) := by
  obtain ⟨M, h0, h1, h2⟩ := exists_bd_hest
  refine ⟨43 * (8 * M), fun i G hG P hP => ?_⟩
  have := n2_ext1_le i h0 h1 h2 hG (measurableSet_box P) (measurableSet_box _)
    (fun x hx => mem_In_of_box hP hx) (mapsTo_refl_box hP)
  simpa [hest] using this

/-- `s = q - (I - E₀)(I - E₁)(I - E₂) q` as a sum of extensions:
`s = E₀ q + s' - E₀ s'`, `s' = E₁ q + s'' - E₁ s''`, `s'' = E₂ q`. -/
theorem lift_eq (q : (Fin 3 → ℝ) → ℝ) :
    lift q = hest 0 q + (hest 1 q + hest 2 q - hest 1 (hest 2 q)) -
      hest 0 (hest 1 q + hest 2 q - hest 1 (hest 2 q)) := by
  simp only [lift, rem, tI, hest, ext1_sub, ext1_add]
  abel

/-- **The `H²` estimate of the shell extension**: `n2 s Q ≤ C n2 q S`; on `Q` the extension
`s` depends only on `q` on the shell `S`. -/
theorem exists_n2_lift_le : ∃ C : ℝ≥0, ∀ {q : (Fin 3 → ℝ) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) q →
    n2 (lift q) (univ.pi fun _ => Ioo (0 : ℝ) (1 / 2)) ≤ C * n2 q shell := by
  obtain ⟨C, hC⟩ := exists_n2_hest_le
  refine ⟨C + (2 * C + C * C) + C * (2 * C + C * C), fun {q} hq => ?_⟩
  have hE : ∀ i {G : (Fin 3 → ℝ) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) G → ContDiff ℝ (⊤ : ℕ∞) (hest i G) :=
    fun i _ hG => contDiff_hest i hG
  set s2 := hest 2 q
  set s1 := hest 1 q + s2 - hest 1 s2
  have hs2 : ContDiff ℝ (⊤ : ℕ∞) s2 := hE 2 hq
  have hs1 : ContDiff ℝ (⊤ : ℕ∞) s1 := ((hE 1 hq).add hs2).sub (hE 1 hs2)
  have hsh : ∀ {P : Fin 3 → Bool}, (∃ i, P i = true) → n2 q (box P) ≤ n2 q shell :=
    fun h => n2_mono q (box_subset_shell h)
  -- the estimate of `s'` on a box with `P 1 = P 2 = false` and every derived box in the shell
  have key : ∀ {P : Fin 3 → Bool}, P 1 = false → P 2 = false →
      (∃ i, Function.update P 1 true i = true) → (∃ i, Function.update P 2 true i = true) →
      (∃ i, Function.update (Function.update P 1 true) 2 true i = true) →
      n2 s1 (box P) ≤ (2 * C + C * C) * n2 q shell := by
    intro P h1 h2 e1 e2 e12
    have h21 : Function.update P 1 true 2 = false := by
      rw [Function.update_of_ne (by decide)]; exact h2
    calc n2 s1 (box P) ≤ n2 (hest 1 q) (box P) + n2 s2 (box P) + n2 (hest 1 s2) (box P) :=
          (n2_sub_le ((hE 1 hq).add hs2) (hE 1 hs2) _).trans
            (add_le_add (n2_add_le (hE 1 hq) hs2 _) le_rfl)
      _ ≤ C * n2 q shell + C * n2 q shell + C * (C * n2 q shell) := by
          gcongr
          · exact (hC 1 hq h1).trans (by gcongr; exact hsh e1)
          · exact (hC 2 hq h2).trans (by gcongr; exact hsh e2)
          · have h3 : n2 s2 (box (Function.update P 1 true)) ≤ C * n2 q shell :=
              (hC 2 hq h21).trans (by gcongr; exact hsh e12)
            exact (hC 1 hs2 h1).trans (by gcongr)
      _ = (2 * C + C * C) * n2 q shell := by ring
  have hF0 : (fun _ : Fin 3 => false) 0 = false := rfl
  have b0 : n2 s1 (box fun _ => false) ≤ (2 * C + C * C) * n2 q shell :=
    key rfl rfl ⟨1, by simp⟩ ⟨2, by simp⟩ ⟨2, by simp⟩
  have b1 : n2 s1 (box (Function.update (fun _ => false) 0 true)) ≤
      (2 * C + C * C) * n2 q shell :=
    key (by simp) (by simp) ⟨0, by simp⟩ ⟨0, by simp⟩ ⟨0, by simp⟩
  rw [lift_eq, ← box_false]
  calc n2 (hest 0 q + s1 - hest 0 s1) (box fun _ => false)
      ≤ n2 (hest 0 q) (box fun _ => false) + n2 s1 (box fun _ => false) +
          n2 (hest 0 s1) (box fun _ => false) :=
        (n2_sub_le ((hE 0 hq).add hs1) (hE 0 hs1) _).trans
          (add_le_add (n2_add_le (hE 0 hq) hs1 _) le_rfl)
    _ ≤ C * n2 q shell + (2 * C + C * C) * n2 q shell +
          C * ((2 * C + C * C) * n2 q shell) := by
        gcongr
        · exact (hC 0 hq hF0).trans (by gcongr; exact hsh ⟨0, by simp⟩)
        · exact (hC 0 hs1 hF0).trans (by gcongr)
    _ = _ := by push_cast; ring

end Feec.Models.Cube.ShellExtension
