module

public import Feec.Numerics.PlaneWaveCube
public import Feec.Models.Cube.InhomogeneousError
public import Feec.Domain.Affine

/-!
# Convergence of the Ch. 7 plane-wave run, on `(0, ½)³` and on the unit cube of `fem4gr`

The plane-wave test of [QuennevilleBelair2015], Ch. 7 (`Feec.Numerics.PlaneWaveCube`) with the
Crank–Nicolson Whitney scheme with Dirichlet DOFs (`Feec.Models.Cube.InhomogeneousError`), for
every amplitude `A₊`, `Aₓ` and frequency `ω`.

## On `Q = (0, ½)³`

* `planeWaveSmooth`: the plane wave has bounded derivatives on every `[0, T] × cl Q`, with the
  bound `pwBound A₊ Aₓ ω = (|A₊| + |Aₓ|) (1 + |ω|)³` (`WholeSpaceTSD.Smooth`).
* **`planeWave_cn_error_le`**: the iterates from the interpolated plane wave with the interpolated
  boundary data satisfy `‖u_M − U(t_M)‖ ≤ C (|A₊| + |Aₓ|) (1 + |ω|)³ (1 + T) (h_N + Δt²)`, and so
  do the five monitors; `planeWave_cnIterates_error_le`: the run exists (`cnIterates`).
* **Non-vacuity** (`exactField_planeWave_ne_zero`): for `A₊ ≠ 0`, `ω ≠ 0` the exact field is
  nonzero and TSD at every time.

## Dilation to the unit cube `(0, 1)³`

`fem4gr` runs on `(0, 1)³`. With `dil u = u(·/2)` (`Feec.Domain.pullF` along `x ↦ x/2`):

* `freudenthalMesh_unit_eq_map`: the Freudenthal meshes of `(0, 1)³` are the images of those of
  `(0, ½)³` under `x ↦ 2x`.
* `inner_dil`: `⟪dil u, dil v⟫ = 8 ⟪u, v⟫`; `complexU_eq`, `complexUMin_eq`: `HΛ((0, 1)³)` and
  `H̊Λ((0, 1)³)` are the transports of `HΛ(Q)`, `H̊Λ(Q)` with chain-rule factor `½`
  (`Feec.Domain.ConstCoeffComplex.maximalComplex_pull`), so `d (dil u) = ½ dil (d u)`.
* `whitneyU`, `whitneyUMin`: the Whitney spaces of the unit cube, defined as the dilations of
  those of `Q`, are subcomplexes of `HΛ((0, 1)³)` and `H̊Λ((0, 1)³)`; `unitRow`, `unitInterior3`.
  That they coincide with the spaces assembled directly on the mesh `freudenthalMesh 0 1` is not
  formalized here: it follows from `freudenthalMesh_unit_eq_map` and the affine invariance of the
  Whitney element (`Feec.Models.Parallelepiped.fieldPull_mem_whitney_cast`), but that module
  cannot be imported together with `Feec.Domain.Affine` (both declare `Feec.Domain.pull`).
* **`isDirichletCNStep_dilRow3_iff`**: a Crank–Nicolson step with parameter `s` on the unit cube
  is a step with parameter `s / 2` on `Q`; with `s = Δt / 2`, the unit-cube scheme with step `Δt`
  is the scheme on `Q` with step `Δt / 2` (the system is invariant under `(t, x) ↦ (2t, 2x)`;
  the time steps of Table 7.1 are `Feec.Numerics.CrankNicolson.dt`).
* **Transported results**: well-posedness `unit_existsUnique_cnStep3`, the error
  `unit_cn_error_le` (`‖u_M − U(t_M)‖_{L²(0,1)³} ≤ √8 C L (1 + T) (h_N + (Δt/2)²)` for
  `U(t, x) = V(t/2, x/2)`) and the monitors `unit_cn_monitors_le`.
* **The `fem4gr` run**: the unit-cube plane wave with frequency `ω` is the dilation of the plane
  wave on `Q` with frequency `2ω` (`dilAmb3_exactField_planeWave`), so
  `unit_planeWave_cn_error_le` gives `‖u_M − U_ω(t_M)‖_{L²(0,1)³}` and the five monitors
  `≤ √8 C (|A₊| + |Aₓ|) (1 + 2|ω|)³ (1 + T_U / 2) (h_N + (Δt/2)²)` for `M Δt ≤ T_U`;
  `unit_planeWave_cnIterates_error_le`: the run exists (`unitCnIterates`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7 (the plane-wave test, Table 7.1)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory Set Filter Real Feec.Domain Feec.Models.BoundedDomain
  Feec.Models.Cube.Inhomogeneous Feec.Numerics.CrankNicolson Feec.Models.Cube.FEM

namespace Feec.Numerics.PlaneWaveCube

/-! ## Derivatives of the plane wave -/

/-- The `z`-projection `y ↦ y₂`. -/
abbrev projZ : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2

theorem norm_smul_projZ_le (a : ℝ) : ‖a • projZ‖ ≤ |a| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg a) fun v => ?_
  change ‖a * v 2‖ ≤ |a| * ‖v‖
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v 2) (abs_nonneg a)

theorem hasFDerivAt_sinZ (w t k : ℝ) (y : Fin 3 → ℝ) :
    HasFDerivAt (fun y : Fin 3 → ℝ => Real.sin (w * (y 2 - t)) * k)
      ((w * Real.cos (w * (y 2 - t)) * k) • projZ) y := by
  have h1 : HasFDerivAt (fun y : Fin 3 → ℝ => y 2) projZ y := hasFDerivAt_apply 2 y
  have h2 := ((h1.sub_const t).const_mul w).sin.mul_const k
  convert h2 using 1
  ext v; simp; ring

theorem hasFDerivAt_cosZ (w t k : ℝ) (y : Fin 3 → ℝ) :
    HasFDerivAt (fun y : Fin 3 → ℝ => w * Real.cos (w * (y 2 - t)) * k)
      ((-(w * w * Real.sin (w * (y 2 - t))) * k) • projZ) y := by
  have h1 : HasFDerivAt (fun y : Fin 3 → ℝ => y 2) projZ y := hasFDerivAt_apply 2 y
  have h2 := (((h1.sub_const t).const_mul w).cos.const_mul w).mul_const k
  convert h2 using 1
  ext v; simp; ring

theorem planeWave_fun (P : Matrix (Fin 3) (Fin 3) ℝ) (w t : ℝ) (a b : Fin 3) :
    (fun y => planeWave P w t y a b) = fun y => Real.sin (w * (y 2 - t)) * P a b := by
  funext y; exact planeWave_apply P w t y a b

theorem curlM_planeWave_fun (P : Matrix (Fin 3) (Fin 3) ℝ) (w t : ℝ) (ik : Ix) :
    curlM (fun ij y => planeWave P w t y ij.1 ij.2) ik =
      fun y => w * Real.cos (w * (y 2 - t)) * curlZ P ik.1 ik.2 := by
  funext y; exact curlM_planeWave P w t ik y

/-- Every entry of the plane-wave amplitudes is bounded by `|A₊| + |Aₓ|`. -/
theorem abs_amplitudeE_le (Ap Ax : ℝ) (a b : Fin 3) : |amplitudeE Ap Ax a b| ≤ |Ap| + |Ax| := by
  have := abs_nonneg Ap; have := abs_nonneg Ax
  fin_cases a <;> fin_cases b <;> simp [amplitudeE] <;> linarith

theorem abs_amplitudeB_le (Ap Ax : ℝ) (a b : Fin 3) : |amplitudeB Ap Ax a b| ≤ |Ap| + |Ax| := by
  have := abs_nonneg Ap; have := abs_nonneg Ax
  fin_cases a <;> fin_cases b <;> simp [amplitudeB] <;> linarith

theorem abs_curlZ_amplitudeE_le (Ap Ax : ℝ) (a b : Fin 3) :
    |curlZ (amplitudeE Ap Ax) a b| ≤ |Ap| + |Ax| := by
  rw [(planeWave_amplitudes Ap Ax).2.1, Matrix.neg_apply, abs_neg]
  exact abs_amplitudeB_le Ap Ax a b

theorem abs_curlZ_amplitudeB_le (Ap Ax : ℝ) (a b : Fin 3) :
    |curlZ (amplitudeB Ap Ax) a b| ≤ |Ap| + |Ax| := by
  rw [(planeWave_amplitudes Ap Ax).1]
  exact abs_amplitudeE_le Ap Ax a b


/-! ## The plane wave has bounded derivatives -/

/-- The bound `(|A₊| + |Aₓ|) (1 + |ω|)³` of the derivatives of the plane wave. -/
def pwBound (Ap Ax w : ℝ) : ℝ := (|Ap| + |Ax|) * (1 + |w|) ^ 3

theorem pwBound_nonneg (Ap Ax w : ℝ) : 0 ≤ pwBound Ap Ax w := by
  unfold pwBound; positivity

theorem le_pwBound {Ap Ax w c : ℝ} (hc : |c| ≤ |Ap| + |Ax|) {k : ℕ} (hk : k ≤ 3) :
    |w| ^ k * |c| ≤ pwBound Ap Ax w := by
  have h1 : |w| ^ k ≤ (1 + |w|) ^ 3 :=
    (pow_le_pow_left₀ (abs_nonneg w) (by linarith) k).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg w]) hk)
  unfold pwBound
  calc |w| ^ k * |c| ≤ (1 + |w|) ^ 3 * (|Ap| + |Ax|) :=
        mul_le_mul h1 hc (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem hasDerivAt_sinT (w y2 k t : ℝ) :
    HasDerivAt (fun s => Real.sin (w * (y2 - s)) * k) (-(w * Real.cos (w * (y2 - t))) * k) t := by
  have h := (((hasDerivAt_id' t).const_sub y2).const_mul w).sin.mul_const k
  convert h using 1
  ring

theorem hasDerivAt_cosT (w y2 k t : ℝ) :
    HasDerivAt (fun s => Real.cos (w * (y2 - s)) * k) (w * Real.sin (w * (y2 - t)) * k) t := by
  have h := (((hasDerivAt_id' t).const_sub y2).const_mul w).cos.mul_const k
  convert h using 1
  ring

theorem abs_mul_trig_le₁ (w z c : ℝ) (hz : |z| ≤ 1) : |w * z * c| ≤ |w| ^ 1 * |c| := by
  rw [abs_mul, abs_mul, pow_one]
  have := abs_nonneg w
  have := abs_nonneg c
  have : |w| * |z| ≤ |w| := by nlinarith [abs_nonneg z]
  nlinarith

theorem abs_mul_trig_le₂ (w z c : ℝ) (hz : |z| ≤ 1) : |-(w * w * z) * c| ≤ |w| ^ 2 * |c| := by
  rw [abs_mul, abs_neg, abs_mul, abs_mul, sq]
  have := mul_nonneg (abs_nonneg w) (abs_nonneg w)
  have := abs_nonneg c
  have : |w| * |w| * |z| ≤ |w| * |w| := by nlinarith [abs_nonneg z]
  nlinarith

theorem abs_mul_trig_le₃ (w z c : ℝ) (hz : |z| ≤ 1) : |w * w * w * z * c| ≤ |w| ^ 3 * |c| := by
  rw [abs_mul, abs_mul, abs_mul, abs_mul, pow_three]
  have := mul_nonneg (mul_nonneg (abs_nonneg w) (abs_nonneg w)) (abs_nonneg w)
  have := abs_nonneg c
  have : |w| * |w| * |w| * |z| ≤ |w| * |w| * |w| := by nlinarith [abs_nonneg z]
  nlinarith [mul_assoc |w| |w| |w|]

theorem abs_lip_cos (w c y2 t t' : ℝ) :
    |w * Real.cos (w * (y2 - t')) * c - w * Real.cos (w * (y2 - t)) * c| ≤
      |w| ^ 2 * |c| * |t' - t| := by
  have e : w * Real.cos (w * (y2 - t')) * c - w * Real.cos (w * (y2 - t)) * c =
      w * c * (Real.cos (w * (y2 - t')) - Real.cos (w * (y2 - t))) := by ring
  have hz : |w * (y2 - t') - w * (y2 - t)| = |w| * |t' - t| := by
    rw [show w * (y2 - t') - w * (y2 - t) = -(w * (t' - t)) by ring, abs_neg, abs_mul]
  rw [e, abs_mul, abs_mul]
  have h := abs_cos_sub_cos_le (w * (y2 - t')) (w * (y2 - t))
  rw [hz] at h
  have := abs_nonneg w; have := abs_nonneg c
  calc |w| * |c| * |Real.cos (w * (y2 - t')) - Real.cos (w * (y2 - t))| ≤
      |w| * |c| * (|w| * |t' - t|) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem abs_lip_sin (w c y2 t t' : ℝ) :
    |-(w * w * Real.sin (w * (y2 - t'))) * c - -(w * w * Real.sin (w * (y2 - t))) * c| ≤
      |w| ^ 3 * |c| * |t' - t| := by
  have e : -(w * w * Real.sin (w * (y2 - t'))) * c - -(w * w * Real.sin (w * (y2 - t))) * c =
      -(w * w * c) * (Real.sin (w * (y2 - t')) - Real.sin (w * (y2 - t))) := by ring
  have hz : |w * (y2 - t') - w * (y2 - t)| = |w| * |t' - t| := by
    rw [show w * (y2 - t') - w * (y2 - t) = -(w * (t' - t)) by ring, abs_neg, abs_mul]
  rw [e, abs_mul, abs_neg, abs_mul, abs_mul]
  have h := abs_sin_sub_sin_le (w * (y2 - t')) (w * (y2 - t))
  rw [hz] at h
  have := abs_nonneg w; have := abs_nonneg c
  calc |w| * |w| * |c| * |Real.sin (w * (y2 - t')) - Real.sin (w * (y2 - t))| ≤
      |w| * |w| * |c| * (|w| * |t' - t|) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem le_pwBound_mul {Ap Ax w c τ : ℝ} (hc : |c| ≤ |Ap| + |Ax|) {k : ℕ} (hk : k ≤ 3)
    (hτ : 0 ≤ τ) : |w| ^ k * |c| * τ ≤ pwBound Ap Ax w * τ :=
  mul_le_mul_of_nonneg_right (le_pwBound hc hk) hτ

theorem norm_smul_projZ_sub_le (a b : ℝ) : ‖a • projZ - b • projZ‖ ≤ |a - b| := by
  have e : a • projZ - b • projZ = (a - b) • projZ := (sub_smul a b projZ).symm
  rw [e]; exact norm_smul_projZ_le _

/-- **The plane wave of Ch. 7 has bounded derivatives on every `[0, T] × cl Q`**, with the
bound `pwBound A₊ Aₓ ω = (|A₊| + |Aₓ|) (1 + |ω|)³`. -/
def planeWaveSmooth (Ap Ax w T : ℝ) : (planeWaveTSD Ap Ax w).Smooth T (pwBound Ap Ax w) where
  E₂ t ij x := -(w * w * Real.sin (w * (x 2 - t))) * amplitudeE Ap Ax ij.1 ij.2
  E₃ t ij x := w * w * w * Real.cos (w * (x 2 - t)) * amplitudeE Ap Ax ij.1 ij.2
  B₂ t ij x := -(w * w * Real.sin (w * (x 2 - t))) * amplitudeB Ap Ax ij.1 ij.2
  B₃ t ij x := w * w * w * Real.cos (w * (x 2 - t)) * amplitudeB Ap Ax ij.1 ij.2
  contDiff_E t ij := by
    change ContDiff ℝ 2 fun y => planeWave (amplitudeE Ap Ax) w t y ij.1 ij.2
    rw [planeWave_fun]; fun_prop
  contDiff_B t ij := by
    change ContDiff ℝ 2 fun y => planeWave (amplitudeB Ap Ax) w t y ij.1 ij.2
    rw [planeWave_fun]; fun_prop
  continuous_E₂ ij := by fun_prop
  continuous_E₃ ij := by fun_prop
  continuous_B₂ ij := by fun_prop
  continuous_B₃ ij := by fun_prop
  hasDerivAt_E₁ t ij x := by
    change HasDerivAt (fun s => -curlM (fun ij y => planeWave (amplitudeB Ap Ax) w s y ij.1 ij.2)
      ij x) _ t
    simp only [curlM_planeWave, (planeWave_amplitudes Ap Ax).1]
    have h := ((hasDerivAt_cosT w (x 2) (amplitudeE Ap Ax ij.1 ij.2) t).const_mul w).neg
    convert h using 1
    · funext s; simp only [Pi.neg_apply]; ring
    · ring
  hasDerivAt_E₂ t ij x := by
    have h := ((hasDerivAt_sinT w (x 2) (amplitudeE Ap Ax ij.1 ij.2) t).const_mul (w * w)).neg
    convert h using 1
    · funext s; simp only [Pi.neg_apply]; ring
    · ring
  hasDerivAt_B₁ t ij x := by
    change HasDerivAt (fun s => curlM (fun ij y => planeWave (amplitudeE Ap Ax) w s y ij.1 ij.2)
      ij x) _ t
    simp only [curlM_planeWave, (planeWave_amplitudes Ap Ax).2.1, Matrix.neg_apply]
    have h := ((hasDerivAt_cosT w (x 2) (amplitudeB Ap Ax ij.1 ij.2) t).const_mul w).neg
    convert h using 1
    · funext s; simp only [Pi.neg_apply]; ring
    · ring
  hasDerivAt_B₂ t ij x := by
    have h := ((hasDerivAt_sinT w (x 2) (amplitudeB Ap Ax ij.1 ij.2) t).const_mul (w * w)).neg
    convert h using 1
    · funext s; simp only [Pi.neg_apply]; ring
    · ring
  bound t _ ij y _ := by
    change ‖fderiv ℝ (fun y => planeWave (amplitudeE Ap Ax) w t y ij.1 ij.2) y‖ ≤ _ ∧
      ‖fderiv ℝ (curlM (fun ij y => planeWave (amplitudeE Ap Ax) w t y ij.1 ij.2) ij) y‖ ≤ _ ∧
      ‖fderiv ℝ (fun y => planeWave (amplitudeB Ap Ax) w t y ij.1 ij.2) y‖ ≤ _ ∧
      ‖fderiv ℝ (curlM (fun ij y => planeWave (amplitudeB Ap Ax) w t y ij.1 ij.2) ij) y‖ ≤ _
    simp only [planeWave_fun, curlM_planeWave_fun, (hasFDerivAt_sinZ _ _ _ y).fderiv,
      (hasFDerivAt_cosZ _ _ _ y).fderiv]
    exact ⟨(norm_smul_projZ_le _).trans ((abs_mul_trig_le₁ _ _ _ (abs_cos_le_one _)).trans
        (le_pwBound (abs_amplitudeE_le Ap Ax ij.1 ij.2) (by norm_num))),
      (norm_smul_projZ_le _).trans ((abs_mul_trig_le₂ _ _ _ (abs_sin_le_one _)).trans
        (le_pwBound (abs_curlZ_amplitudeE_le Ap Ax ij.1 ij.2) (by norm_num))),
      (norm_smul_projZ_le _).trans ((abs_mul_trig_le₁ _ _ _ (abs_cos_le_one _)).trans
        (le_pwBound (abs_amplitudeB_le Ap Ax ij.1 ij.2) (by norm_num))),
      (norm_smul_projZ_le _).trans ((abs_mul_trig_le₂ _ _ _ (abs_sin_le_one _)).trans
        (le_pwBound (abs_curlZ_amplitudeB_le Ap Ax ij.1 ij.2) (by norm_num)))⟩
  lipschitz t _ t' _ ij y _ := by
    change ‖fderiv ℝ (fun y => planeWave (amplitudeE Ap Ax) w t' y ij.1 ij.2) y -
        fderiv ℝ (fun y => planeWave (amplitudeE Ap Ax) w t y ij.1 ij.2) y‖ ≤ _ ∧
      ‖fderiv ℝ (curlM (fun ij y => planeWave (amplitudeE Ap Ax) w t' y ij.1 ij.2) ij) y -
        fderiv ℝ (curlM (fun ij y => planeWave (amplitudeE Ap Ax) w t y ij.1 ij.2) ij) y‖ ≤ _ ∧
      ‖fderiv ℝ (fun y => planeWave (amplitudeB Ap Ax) w t' y ij.1 ij.2) y -
        fderiv ℝ (fun y => planeWave (amplitudeB Ap Ax) w t y ij.1 ij.2) y‖ ≤ _ ∧
      ‖fderiv ℝ (curlM (fun ij y => planeWave (amplitudeB Ap Ax) w t' y ij.1 ij.2) ij) y -
        fderiv ℝ (curlM (fun ij y => planeWave (amplitudeB Ap Ax) w t y ij.1 ij.2) ij) y‖ ≤ _
    simp only [planeWave_fun, curlM_planeWave_fun, (hasFDerivAt_sinZ _ _ _ y).fderiv,
      (hasFDerivAt_cosZ _ _ _ y).fderiv]
    have hτ := abs_nonneg (t' - t)
    exact ⟨(norm_smul_projZ_sub_le _ _).trans ((abs_lip_cos _ _ _ _ _).trans
        (le_pwBound_mul (abs_amplitudeE_le Ap Ax ij.1 ij.2) (by norm_num) hτ)),
      (norm_smul_projZ_sub_le _ _).trans ((abs_lip_sin _ _ _ _ _).trans
        (le_pwBound_mul (abs_curlZ_amplitudeE_le Ap Ax ij.1 ij.2) le_rfl hτ)),
      (norm_smul_projZ_sub_le _ _).trans ((abs_lip_cos _ _ _ _ _).trans
        (le_pwBound_mul (abs_amplitudeB_le Ap Ax ij.1 ij.2) (by norm_num) hτ)),
      (norm_smul_projZ_sub_le _ _).trans ((abs_lip_sin _ _ _ _ _).trans
        (le_pwBound_mul (abs_curlZ_amplitudeB_le Ap Ax ij.1 ij.2) le_rfl hτ))⟩
  bound₃ t _ ij y _ :=
    ⟨(abs_mul_trig_le₃ _ _ _ (abs_cos_le_one _)).trans
        (le_pwBound (abs_amplitudeE_le Ap Ax ij.1 ij.2) le_rfl),
      (abs_mul_trig_le₃ _ _ _ (abs_cos_le_one _)).trans
        (le_pwBound (abs_amplitudeB_le Ap Ax ij.1 ij.2) le_rfl)⟩

/-! ## `O(h + Δt²)` convergence of the Ch. 7 plane-wave run on `(0, ½)³` -/

/-- The three rows `(0, E_r, B_r)` of the plane wave as smooth row solutions on `[0, T] × cl Q`. -/
def planeWaveRows (Ap Ax w T : ℝ) : Fin 3 → RowSolution T (pwBound Ap Ax w) :=
  fun r => (planeWaveSmooth Ap Ax w T).row (pwBound_nonneg Ap Ax w) r

/-- **The Ch. 7 plane-wave run converges at rate `O(h + Δt²)`** (on the cube `(0, ½)³` of the
Freudenthal meshes; every `A₊`, `Aₓ`, `ω`, `T`): the Crank–Nicolson Whitney iterates `uₙ`
started from the canonical interpolant of the plane wave, with the boundary DOFs of the
interpolated plane wave prescribed at every step (`fem4gr`'s `DirichletBC` data), satisfy
`‖u_M − U(t_M)‖ ≤ C (|A₊| + |Aₓ|) (1 + |ω|)³ (1 + T) (h_N + Δt²)` for `M Δt ≤ T`, and so do the
five constraint monitors of `u_M`; `C = cnConst`. -/
theorem planeWave_cn_error_le (Ap Ax w T : ℝ) (N : ℕ) {Δt : ℝ} (hΔt : 0 < Δt) {M : ℕ}
    (hM : (M : ℝ) * Δt ≤ T) {u : ℕ → DState3 (whitneyRow N)}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep (whitneyInterior3 N)
      (discreteWave3 (whitneyRow N)) (Δt / 2) 0
        (exactInterp (planeWaveRows Ap Ax w T) N ((n + 1 : ℕ) * Δt)) (u n) (u (n + 1)))
    (hu0 : u 0 = exactInterp (planeWaveRows Ap Ax w T) N 0) :
    ‖dEmb3 (whitneyRow N) (u M) - exactField (planeWaveRows Ap Ax w T) (M * Δt)‖ ≤
        cnConst * pwBound Ap Ax w * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖skewPart (entryE N) (u M)‖ ≤ cnConst * pwBound Ap Ax w * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖skewPart (entryB N) (u M)‖ ≤ cnConst * pwBound Ap Ax w * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖tracePart (entryE N) (u M)‖ ≤ cnConst * pwBound Ap Ax w * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖tracePart (entryB N) (u M)‖ ≤ cnConst * pwBound Ap Ax w * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖sigmaPart N (u M)‖ ≤ cnConst * pwBound Ap Ax w * (1 + T) * (meshSize N + Δt ^ 2) :=
  (planeWaveSmooth Ap Ax w T).whitney_cn_error_monitors_le (pwBound_nonneg Ap Ax w) N hΔt hM
    (u := u) (g := fun n => exactInterp (planeWaveRows Ap Ax w T) N (n * Δt)) hstep
    (fun _ _ => sub_self_mem_submodule _ _) hu0

/-- **The run exists**: the iterates of the scheme from the interpolated plane wave with the
interpolated boundary data (`cnIterates`) satisfy the bounds of `planeWave_cn_error_le` at every
`M` with `M Δt ≤ T`. -/
theorem planeWave_cnIterates_error_le (Ap Ax w T : ℝ) (N : ℕ) {Δt : ℝ} (hΔt : 0 < Δt) {M : ℕ}
    (hM : (M : ℝ) * Δt ≤ T) :
    ‖dEmb3 (whitneyRow N) (cnIterates N (Δt / 2)
        (fun n => exactInterp (planeWaveRows Ap Ax w T) N (n * Δt))
        (exactInterp (planeWaveRows Ap Ax w T) N 0) M) -
      exactField (planeWaveRows Ap Ax w T) (M * Δt)‖ ≤
        cnConst * pwBound Ap Ax w * (1 + T) * (meshSize N + Δt ^ 2) :=
  (planeWave_cn_error_le Ap Ax w T N hΔt hM
    (u := cnIterates N (Δt / 2) (fun n => exactInterp (planeWaveRows Ap Ax w T) N (n * Δt))
      (exactInterp (planeWaveRows Ap Ax w T) N 0))
    (fun n _ => cnIterates_spec N (Δt / 2) _ _ n) rfl).1

/-! ## Non-vacuity: the plane wave with `A₊ ≠ 0` is a nonzero exact solution -/

theorem sin_ne_zero_of_abs_lt {x : ℝ} (h0 : x ≠ 0) (hπ : |x| < π) : Real.sin x ≠ 0 := by
  rcases lt_or_gt_of_ne h0 with hx | hx
  · exact (sin_neg_of_neg_of_neg_pi_lt hx (by linarith [neg_abs_le x, abs_lt.1 hπ])).ne
  · exact (sin_pos_of_pos_of_lt_pi hx (by linarith [le_abs_self x])).ne'

theorem planeWaveRows_u_one (Ap Ax w T t : ℝ) (r : Fin 3) :
    (planeWaveRows Ap Ax w T r).u t 1 =
      oneForm fun j y => planeWave (amplitudeE Ap Ax) w t y r j := rfl

/-- The component `E₀₀` of row `0` of the plane wave on `Q`: `sin ω(z − t) · E₀₀`. -/
theorem exactField_planeWave_comp (Ap Ax w T t : ℝ) :
    entryE' 0 0 (exactField (planeWaveRows Ap Ax w T) t) =
      (memLp_of_continuous (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3)
        ((Real.continuous_sin.comp (continuous_const.mul ((continuous_apply 2).sub
          continuous_const))).mul continuous_const)).toLp
        (fun y : Fin 3 → ℝ => Real.sin (w * (y 2 - t)) * amplitudeE Ap Ax 0 0) := by
  rw [entryE'_exactField]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun y => ?_)
  change oneForm (fun j y => planeWave (amplitudeE Ap Ax) w t y 0 j) y {0} = _
  rw [oneForm_apply_singleton, planeWave_apply]

/-- **Non-vacuity of `planeWave_cn_error_le`**: for `A₊ ≠ 0` and `ω ≠ 0` the exact field
`U(0)` of the plane wave on `Q` is nonzero (its `E₀₀ = −A₊ sin ωz` component does not vanish on
`Q`), and it is TSD at every time (`IsTSDAt`), so the monitors of `U` vanish while `U ≠ 0`. -/
theorem exactField_planeWave_ne_zero {Ap Ax w T : ℝ} (hAp : Ap ≠ 0) (hw : w ≠ 0) :
    exactField (planeWaveRows Ap Ax w T) 0 ≠ 0 ∧
      ∀ t, IsTSDAt (planeWaveRows Ap Ax w T) t := by
  refine ⟨fun h => ?_, fun t => (planeWaveSmooth Ap Ax w T).isTSDAt (pwBound_nonneg Ap Ax w) t⟩
  set c : ℝ := 1 / (4 + 4 * |w|)
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [abs_nonneg w]
  have hwc : |w * c| < π := by
    rw [abs_mul, abs_of_pos hc0]
    have : |w| * c < 1 := by
      rw [show |w| * c = |w| / (4 + 4 * |w|) by ring, div_lt_one (by positivity)]
      linarith [abs_nonneg w]
    linarith [Real.two_le_pi]
  have hp : (fun _ : Fin 3 => c) ∈ cubeDomain 3 := fun i _ => ⟨hc0, hc1⟩
  have hcomp := exactField_planeWave_comp Ap Ax w T 0
  rw [h, map_zero] at hcomp
  have hae : (fun y : Fin 3 → ℝ => Real.sin (w * (y 2 - 0)) * amplitudeE Ap Ax 0 0) =ᵐ[
      volume.restrict (cubeDomain 3)] fun _ => (0 : ℝ) := by
    have h1 := (memLp_of_continuous
      (f := fun y : Fin 3 → ℝ => Real.sin (w * (y 2 - 0)) * amplitudeE Ap Ax 0 0)
      (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3)
      ((Real.continuous_sin.comp (continuous_const.mul ((continuous_apply 2).sub
          continuous_const))).mul continuous_const)).coeFn_toLp
    rw [← hcomp] at h1
    filter_upwards [h1, Lp.coeFn_zero ℝ 2 (volume.restrict (cubeDomain 3))] with y h2 h3
    rw [← h2]
    exact h3
  have hcont : Continuous fun y : Fin 3 → ℝ => Real.sin (w * (y 2 - 0)) * amplitudeE Ap Ax 0 0 :=
    (Real.continuous_sin.comp (continuous_const.mul ((continuous_apply 2).sub
      continuous_const))).mul continuous_const
  have heq := Measure.eqOn_open_of_ae_eq hae (isOpen_cubeDomain 3) hcont.continuousOn
    continuousOn_const hp
  simp only [sub_zero, amplitudeE] at heq
  have hs := sin_ne_zero_of_abs_lt (mul_ne_zero hw hc0.ne') hwc
  have : Real.sin (w * c) * -Ap ≠ 0 := mul_ne_zero hs (neg_ne_zero.2 hAp)
  exact this (by simpa using heq)

end Feec.Numerics.PlaneWaveCube

/-! ## Dilation to the unit cube `(0, 1)³` of `fem4gr` -/

namespace Feec.Numerics.PlaneWaveCube

open Feec.FiniteElement HilbertComplex

theorem extDerivOp_isHomogeneous (k : ℤ) : (extDerivOp ℝ 3 k).IsHomogeneous 1 := by
  intro t r p hp
  simp only [extDerivOp, List.mem_map] at hp
  obtain ⟨j, -, rfl⟩ := hp
  rfl

theorem half_ne_zero' : (1 / 2 : ℝ) ≠ 0 := by norm_num

theorem preimage_unitCube : aff (1 / 2 : ℝ) (0 : Fin 3 → ℝ) ⁻¹' cubeDomain 3 = unitCube := by
  ext x
  simp only [mem_preimage, aff, add_zero, cubeDomain, unitCube, Models.Cube.Geometry.openCube,
    Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply, zero_add]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem jac_half : jac (E := Fin 3 → ℝ) (1 / 2 : ℝ) = 1 / 8 := by
  rw [jac, Module.finrank_fin_fun]; norm_num

/-- **The dilation** `u ↦ u(·/2)`, `L²((0, ½)³; Λᵏ) ≃ L²((0, 1)³; Λᵏ)` (componentwise pull-back
along `x ↦ x/2`, the inverse of `x ↦ 2x`). -/
def dil (k : ℤ) :
    L2F ℝ (cubeDomain 3) (formIdx 3 k) ≃L[ℝ] L2F ℝ unitCube (formIdx 3 k) :=
  pullF (𝕜 := ℝ) half_ne_zero' (0 : Fin 3 → ℝ) (isOpen_cubeDomain 3).measurableSet
    preimage_unitCube (formIdx 3 k)

theorem inner_dil (k : ℤ) (u v : L2F ℝ (cubeDomain 3) (formIdx 3 k)) :
    ⟪dil k u, dil k v⟫ = 8 * ⟪u, v⟫ := by
  rw [dil, inner_pullF, jac_half]; norm_num

/-- The de Rham complex `HΛ((0, 1)³)` of the unit cube. -/
abbrev complexU := (deRham ℝ 3).maximalComplex isOpen_unitCube

/-- The de Rham complex `H̊Λ((0, 1)³)` of the unit cube. -/
abbrev complexUMin := (deRham ℝ 3).minimalComplex isOpen_unitCube

theorem complexU_eq : complexU = (complex 3).transport dil
    (ConstCoeffComplex.chainFactor (1 / 2 : ℝ) fun _ => 1)
    (ConstCoeffComplex.chainFactor_ne_zero half_ne_zero' _) :=
  (deRham ℝ 3).maximalComplex_pull extDerivOp_isHomogeneous half_ne_zero' 0
    (isOpen_cubeDomain 3) isOpen_unitCube preimage_unitCube

theorem complexUMin_eq : complexUMin = (complexMin 3).transport dil
    (ConstCoeffComplex.chainFactor (1 / 2 : ℝ) fun _ => 1)
    (ConstCoeffComplex.chainFactor_ne_zero half_ne_zero' _) :=
  (deRham ℝ 3).minimalComplex_pull extDerivOp_isHomogeneous half_ne_zero' 0
    (isOpen_cubeDomain 3) isOpen_unitCube preimage_unitCube

end Feec.Numerics.PlaneWaveCube
namespace Feec.Numerics.PlaneWaveCube
open Feec.FiniteElement HilbertComplex

/-- The chain-rule factor of the dilation: `½` for `d k (k + 1)`. -/
abbrev κU : ℤ → ℤ → ℝ := ConstCoeffComplex.chainFactor (1 / 2 : ℝ) fun _ => 1

theorem transport_d_dil {H : HilbertComplex ℝ (ComplexShape.up ℤ)
    fun k => L2F ℝ (cubeDomain 3) (formIdx 3 k)} (i j : ℤ) {x : L2F ℝ (cubeDomain 3) (formIdx 3 i)}
    (hx : x ∈ (H.d i j).domain) :
    dil i x ∈ ((H.transport dil κU (ConstCoeffComplex.chainFactor_ne_zero half_ne_zero' _)).d
      i j).domain ∧
      ∀ h, (H.transport dil κU (ConstCoeffComplex.chainFactor_ne_zero half_ne_zero' _)).d i j
        ⟨dil i x, h⟩ = κU i j • dil j (H.d i j ⟨x, hx⟩) := by
  have hm : dil i x ∈ ((H.transport dil κU
      (ConstCoeffComplex.chainFactor_ne_zero half_ne_zero' _)).d i j).domain := by
    rw [transport_d, mem_transportD_domain, ContinuousLinearEquiv.symm_apply_apply]; exact hx
  refine ⟨hm, fun h => (transportD_apply (H := H) (e := dil) (κ := κU) ⟨dil i x, h⟩).trans ?_⟩
  congr 3
  exact Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)

theorem complexU_d_dil (i j : ℤ) {x : L2F ℝ (cubeDomain 3) (formIdx 3 i)}
    (hx : x ∈ ((complex 3).d i j).domain) :
    dil i x ∈ (complexU.d i j).domain ∧
      ∀ h, complexU.d i j ⟨dil i x, h⟩ = κU i j • dil j ((complex 3).d i j ⟨x, hx⟩) := by
  rw [complexU_eq]; exact transport_d_dil i j hx

theorem complexUMin_d_dil (i j : ℤ) {x : L2F ℝ (cubeDomain 3) (formIdx 3 i)}
    (hx : x ∈ ((complexMin 3).d i j).domain) :
    dil i x ∈ (complexUMin.d i j).domain ∧
      ∀ h, complexUMin.d i j ⟨dil i x, h⟩ = κU i j • dil j ((complexMin 3).d i j ⟨x, hx⟩) := by
  rw [complexUMin_eq]; exact transport_d_dil i j hx

end Feec.Numerics.PlaneWaveCube
namespace Feec.Numerics.PlaneWaveCube
open Feec.FiniteElement HilbertComplex

/-- The dilation as a linear map on the spaces of the de Rham complex. -/
def dilL (k : ℤ) : L2F ℝ (cubeDomain 3) ((deRham ℝ 3).ι k) →ₗ[ℝ]
    L2F ℝ unitCube ((deRham ℝ 3).ι k) :=
  (dil k).toLinearEquiv.toLinearMap

@[simp] theorem dilL_apply (k : ℤ) (x : L2F ℝ (cubeDomain 3) ((deRham ℝ 3).ι k)) :
    dilL k x = dil k x := rfl

/-- **The Whitney spaces of the unit cube**: the dilations `Vₕ(0, 1)³ = {u(·/2) : u ∈ Vₕ(0, ½)³}`
of the Whitney spaces of the level-`(N + 1)` Freudenthal mesh of `(0, ½)³`, a subcomplex of
`HΛ((0, 1)³)`. -/
def whitneyU (N : ℕ) : complexU.Subcomplex where
  V k := ((whitney 3 N).V k).map (dilL k)
  le_domain i j := by
    rintro _ ⟨x, hx, rfl⟩
    exact (complexU_d_dil i j ((whitney 3 N).le_domain i j hx)).1
  mapsTo i j y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    have key := (complexU_d_dil i j ((whitney 3 N).le_domain i j hx)).2
      (complexU_d_dil i j ((whitney 3 N).le_domain i j hx)).1
    refine ⟨κU i j • (complex 3).d i j ⟨x, (whitney 3 N).le_domain i j hx⟩,
      Submodule.smul_mem _ _ ((whitney 3 N).mapsTo i j x hx), ?_⟩
    exact ((dil j).map_smul _ _).trans key.symm

/-- The unit-cube Whitney spaces with vanishing boundary DOFs (dilations of `V̊ₕ`), a subcomplex
of `H̊Λ((0, 1)³)`. -/
def whitneyUMin (N : ℕ) : complexUMin.Subcomplex where
  V k := ((whitneyMin 3 N).V k).map (dilL k)
  le_domain i j := by
    rintro _ ⟨x, hx, rfl⟩
    exact (complexUMin_d_dil i j ((whitneyMin 3 N).le_domain i j hx)).1
  mapsTo i j y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    have key := (complexUMin_d_dil i j ((whitneyMin 3 N).le_domain i j hx)).2
      (complexUMin_d_dil i j ((whitneyMin 3 N).le_domain i j hx)).1
    refine ⟨κU i j • (complexMin 3).d i j ⟨x, (whitneyMin 3 N).le_domain i j hx⟩,
      Submodule.smul_mem _ _ ((whitneyMin 3 N).mapsTo i j x hx), ?_⟩
    exact ((dil j).map_smul _ _).trans key.symm

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((whitneyU N).V k) :=
  have : FiniteDimensional ℝ ((whitney 3 N).V k) := inferInstance
  Module.Finite.map ((whitney 3 N).V k) (dilL k)

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((whitneyUMin N).V k) :=
  have : FiniteDimensional ℝ ((whitneyMin 3 N).V k) := inferInstance
  Module.Finite.map ((whitneyMin 3 N).V k) (dilL k)

/-- One row `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ²` of the unit-cube Whitney spaces. -/
abbrev unitRow (N : ℕ) := (whitneyU N).window 0 3

instance (N : ℕ) (i : Fin 3) : FiniteDimensional ℝ ((unitRow N).V i) :=
  inferInstanceAs (FiniteDimensional ℝ ((whitneyU N).V (0 + (i : ℤ))))

/-- The three-row unit-cube fields with vanishing boundary DOFs. -/
abbrev unitInterior3 (N : ℕ) :=
  interior3 (unitRow N) fun i => (whitneyUMin N).V (0 + (i : ℤ))

/-- **Well-posedness of the `fem4gr` scheme on the unit cube**, for every time step. -/
theorem unit_existsUnique_cnStep3 (N : ℕ) (s : ℝ) (f g' u : DState3 (unitRow N)) :
    ∃! u', TimeStepping.IsDirichletCNStep (unitInterior3 N) (discreteWave3 (unitRow N)) s f g'
      u u' :=
  existsUnique_isDirichletCNStep3 _ _ s f g' u

end Feec.Numerics.PlaneWaveCube
namespace Feec.Numerics.PlaneWaveCube
open Feec.FiniteElement HilbertComplex

/-- **Conjugacy of Dirichlet Crank–Nicolson steps under a scaled isometry**: if
`⟪Φ x, Φ y⟫ = c ⟪x, y⟫` (`c > 0`), `⟪A' Φ x, Φ y⟫ = c κ ⟪A x, y⟫` and `Φ V₀ = V₀'`, then a step
with parameter `s` for `(V₀', A')` from `Φ`-images is exactly a step with parameter `κ s` for
`(V₀, A)`. -/
theorem isDirichletCNStep_conj_iff {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] (Φ : V ≃ₗ[ℝ] V') {c κ : ℝ} (hc : 0 < c)
    (hΦ : ∀ x y, ⟪Φ x, Φ y⟫ = c * ⟪x, y⟫) {A : V →ₗ[ℝ] V} {A' : V' →ₗ[ℝ] V'}
    (hA : ∀ x y, ⟪A' (Φ x), Φ y⟫ = c * κ * ⟪A x, y⟫) {V₀ : Submodule ℝ V} {V₀' : Submodule ℝ V'}
    (hV₀ : ∀ x, Φ x ∈ V₀' ↔ x ∈ V₀) (s : ℝ) (f g' u u' : V) :
    TimeStepping.IsDirichletCNStep V₀' A' s (Φ f) (Φ g') (Φ u) (Φ u') ↔
      TimeStepping.IsDirichletCNStep V₀ A (κ * s) f g' u u' := by
  have key : ∀ v, (⟪Φ u' - Φ u, Φ v⟫ = s * ⟪A' (Φ u' + Φ u), Φ v⟫ + ⟪Φ f, Φ v⟫ ↔
      ⟪u' - u, v⟫ = κ * s * ⟪A (u' + u), v⟫ + ⟪f, v⟫) := fun v => by
    rw [← map_sub, ← map_add, hΦ, hΦ, hA]
    constructor <;> intro h
    · have : c * ⟪u' - u, v⟫ = c * (κ * s * ⟪A (u' + u), v⟫ + ⟪f, v⟫) := by rw [h]; ring
      exact mul_left_cancel₀ hc.ne' this
    · rw [h]; ring
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(hV₀ _).1 (by rwa [map_sub]), fun v hv => (key v).1 (h2 _ ((hV₀ v).2 hv))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [← map_sub]; exact (hV₀ _).2 h1, fun w hw => ?_⟩
    obtain ⟨v, rfl⟩ := Φ.surjective w
    exact (key v).2 (h2 v ((hV₀ v).1 hw))

end Feec.Numerics.PlaneWaveCube
namespace Feec.Numerics.PlaneWaveCube
open Feec.FiniteElement HilbertComplex

theorem dil_symm_mem {N : ℕ} {k : ℤ} {y : L2F ℝ unitCube (formIdx 3 k)}
    (hy : y ∈ (whitneyU N).V k) : (dil k).symm y ∈ (whitney 3 N).V k := by
  obtain ⟨z, hz, hzy⟩ := hy
  have : (dil k).symm y = z := by rw [← hzy]; exact (dil k).symm_apply_apply z
  rw [this]; exact hz

theorem dil_symm_mem_min {N : ℕ} {k : ℤ} {y : L2F ℝ unitCube (formIdx 3 k)}
    (hy : y ∈ (whitneyUMin N).V k) : (dil k).symm y ∈ (whitneyMin 3 N).V k := by
  obtain ⟨z, hz, hzy⟩ := hy
  have : (dil k).symm y = z := by rw [← hzy]; exact (dil k).symm_apply_apply z
  rw [this]; exact hz

/-- **The dilation of one Whitney row** `Vₕ(0, ½)³ ≃ Vₕ(0, 1)³`. -/
def dilRow (N : ℕ) : DState (whitneyRow N) ≃ₗ[ℝ] DState (unitRow N) where
  toFun x := WithLp.toLp 2 fun i => ⟨dil _ (x i).1, ⟨(x i).1, (x i).2, rfl⟩⟩
  invFun y := WithLp.toLp 2 fun i => ⟨(dil _).symm (y i).1, dil_symm_mem (y i).2⟩
  map_add' x y := PiLp.ext fun i => Subtype.ext (map_add (dil _) (x i).1 (y i).1)
  map_smul' a x := PiLp.ext fun i => Subtype.ext (map_smul (dil _) a (x i).1)
  left_inv x := PiLp.ext fun i => Subtype.ext ((dil _).symm_apply_apply (x i).1)
  right_inv y := PiLp.ext fun i => Subtype.ext ((dil _).apply_symm_apply (y i).1)

theorem dilRow_apply (N : ℕ) (x : DState (whitneyRow N)) (i : Fin 3) :
    (dilRow N x i).1 = dil _ (x i).1 := rfl

theorem inner_dilRow (N : ℕ) (x y : DState (whitneyRow N)) :
    ⟪dilRow N x, dilRow N y⟫ = 8 * ⟪x, y⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_inner, Submodule.coe_inner]
  exact inner_dil _ _ _

theorem mem_dilRow_iff (N : ℕ) (x : DState (whitneyRow N)) :
    dilRow N x ∈ interior (unitRow N) (fun i => (whitneyUMin N).V (0 + (i : ℤ))) ↔
      x ∈ interior (whitneyRow N) (fun i => (whitneyMin 3 N).V (0 + (i : ℤ))) := by
  refine forall_congr' fun i => ?_
  constructor
  · intro h
    have := dil_symm_mem_min h
    rwa [dilRow_apply, ContinuousLinearEquiv.symm_apply_apply] at this
  · intro h
    exact ⟨_, h, rfl⟩

end Feec.Numerics.PlaneWaveCube
namespace Feec.Numerics.PlaneWaveCube
open Feec.FiniteElement HilbertComplex

theorem κU_smul_d (N : ℕ) (i j : Fin 3) (x : (whitneyRow N).V i) :
    κU ((0 : ℤ) + ((i : ℕ) : ℤ)) ((0 : ℤ) + ((j : ℕ) : ℤ)) •
        dil _ ((complex 3).d ((0 : ℤ) + ((i : ℕ) : ℤ)) ((0 : ℤ) + ((j : ℕ) : ℤ))
          ⟨x.1, (whitneyRow N).le_domain i j x.2⟩) =
      (1 / 2 : ℝ) • dil _ ((complex 3).d ((0 : ℤ) + ((i : ℕ) : ℤ)) ((0 : ℤ) + ((j : ℕ) : ℤ))
          ⟨x.1, (whitneyRow N).le_domain i j x.2⟩) := by
  by_cases h : (0 : ℤ) + ((i : ℕ) : ℤ) + 1 = (0 : ℤ) + ((j : ℕ) : ℤ)
  · have h' : ((i : ℕ) : ℤ) + 1 = ((j : ℕ) : ℤ) := by simpa using h
    simp [κU, ConstCoeffComplex.chainFactor, h']
  · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using h), map_zero, smul_zero,
      smul_zero]

/-- **`d` scales by `½` under the dilation**: `𝐝ₕ (u(·/2)) = ½ (𝐝ₕ u)(·/2)`. -/
theorem discreteD_dilRow (N : ℕ) (x : DState (whitneyRow N)) :
    discreteD (unitRow N) (dilRow N x) = (1 / 2 : ℝ) • dilRow N (discreteD (whitneyRow N) x) := by
  refine PiLp.ext fun j => Subtype.ext ?_
  have hterm : ∀ i, ((unitRow N).dLin i j (dilRow N x i)).1 =
      (1 / 2 : ℝ) • dil _ ((whitneyRow N).dLin i j (x i)).1 := fun i => by
    change complexU.d _ _ ⟨dil _ (x i).1, _⟩ = (1 / 2 : ℝ) •
      dil _ ((complex 3).d ((0 : ℤ) + ((i : ℕ) : ℤ)) ((0 : ℤ) + ((j : ℕ) : ℤ))
        ⟨(x i).1, (whitneyRow N).le_domain i j (x i).2⟩)
    exact ((complexU_d_dil _ _ ((whitneyRow N).le_domain i j (x i).2)).2 _).trans
      (κU_smul_d N i j (x i))
  change (∑ i, (unitRow N).dLin i j (dilRow N x i)).1 =
    (1 / 2 : ℝ) • dil _ (∑ i, (whitneyRow N).dLin i j (x i)).1
  rw [Submodule.coe_sum, Submodule.coe_sum, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => hterm i

end Feec.Numerics.PlaneWaveCube
namespace Feec.Numerics.PlaneWaveCube
open Feec.FiniteElement HilbertComplex

/-- The dilation of the three-row space. -/
def dilRow3 (N : ℕ) : DState3 (whitneyRow N) ≃ₗ[ℝ] DState3 (unitRow N) where
  toFun u := WithLp.toLp 2 fun r => dilRow N (u r)
  invFun v := WithLp.toLp 2 fun r => (dilRow N).symm (v r)
  map_add' u v := PiLp.ext fun r => (dilRow N).map_add (u r) (v r)
  map_smul' a u := PiLp.ext fun r => (dilRow N).map_smul a (u r)
  left_inv u := PiLp.ext fun r => (dilRow N).symm_apply_apply (u r)
  right_inv v := PiLp.ext fun r => (dilRow N).apply_symm_apply (v r)

theorem dilRow3_apply (N : ℕ) (u : DState3 (whitneyRow N)) (r : Fin 3) :
    dilRow3 N u r = dilRow N (u r) := rfl

theorem inner_dilRow3 (N : ℕ) (u v : DState3 (whitneyRow N)) :
    ⟪dilRow3 N u, dilRow3 N v⟫ = 8 * ⟪u, v⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => inner_dilRow N (u r) (v r)

theorem discreteD3_dilRow3 (N : ℕ) (u : DState3 (whitneyRow N)) :
    discreteD3 (unitRow N) (dilRow3 N u) =
      (1 / 2 : ℝ) • dilRow3 N (discreteD3 (whitneyRow N) u) :=
  PiLp.ext fun r => discreteD_dilRow N (u r)

theorem inner_discreteWave3_dilRow3 (N : ℕ) (u v : DState3 (whitneyRow N)) :
    ⟪discreteWave3 (unitRow N) (dilRow3 N u), dilRow3 N v⟫ =
      8 * (1 / 2) * ⟪discreteWave3 (whitneyRow N) u, v⟫ := by
  have hD1 := discreteD3_dilRow3 N u
  have hD2 := discreteD3_dilRow3 N v
  calc ⟪discreteWave3 (unitRow N) (dilRow3 N u), dilRow3 N v⟫ =
        ⟪discreteD3 (unitRow N) (dilRow3 N u), dilRow3 N v⟫ -
          ⟪dilRow3 N u, discreteD3 (unitRow N) (dilRow3 N v)⟫ :=
        inner_discreteWave3 (unitRow N) (dilRow3 N u) (dilRow3 N v)
    _ = ⟪(1 / 2 : ℝ) • dilRow3 N (discreteD3 (whitneyRow N) u), dilRow3 N v⟫ -
          ⟪dilRow3 N u, (1 / 2 : ℝ) • dilRow3 N (discreteD3 (whitneyRow N) v)⟫ :=
        congrArg₂ (fun a b => ⟪a, dilRow3 N v⟫ - ⟪dilRow3 N u, b⟫) hD1 hD2
    _ = (1 / 2) * (8 * ⟪discreteD3 (whitneyRow N) u, v⟫) -
          (1 / 2) * (8 * ⟪u, discreteD3 (whitneyRow N) v⟫) :=
        congrArg₂ (· - ·)
          ((real_inner_smul_left _ _ _).trans (congrArg _ (inner_dilRow3 N _ _)))
          ((real_inner_smul_right _ _ _).trans (congrArg _ (inner_dilRow3 N _ _)))
    _ = 8 * (1 / 2) * ⟪discreteWave3 (whitneyRow N) u, v⟫ := by
        rw [inner_discreteWave3 (whitneyRow N) u v]; ring

theorem mem_dilRow3_iff (N : ℕ) (u : DState3 (whitneyRow N)) :
    dilRow3 N u ∈ unitInterior3 N ↔ u ∈ whitneyInterior3 N :=
  forall_congr' fun r => mem_dilRow_iff N (u r)

/-- **The scheme on the unit cube with step `Δt` is the scheme on `(0, ½)³` with step `Δt / 2`**:
a Dirichlet Crank–Nicolson step with parameter `s` on the dilated Whitney spaces of `(0, 1)³`
(inner products `×8`, `d` `×½`) is exactly a step with parameter `s / 2` on the Whitney spaces of
`(0, ½)³`. -/
theorem isDirichletCNStep_dilRow3_iff (N : ℕ) (s : ℝ) (f g' u u' : DState3 (whitneyRow N)) :
    TimeStepping.IsDirichletCNStep (unitInterior3 N) (discreteWave3 (unitRow N)) s
        (dilRow3 N f) (dilRow3 N g') (dilRow3 N u) (dilRow3 N u') ↔
      TimeStepping.IsDirichletCNStep (whitneyInterior3 N) (discreteWave3 (whitneyRow N)) (s / 2)
        f g' u u' := by
  have h := isDirichletCNStep_conj_iff (dilRow3 N) (by norm_num : (0 : ℝ) < 8)
    (inner_dilRow3 N) (inner_discreteWave3_dilRow3 N) (mem_dilRow3_iff N) s f g' u u'
  rwa [show (1 / 2 : ℝ) * s = s / 2 by ring] at h

end Feec.Numerics.PlaneWaveCube
namespace Feec.Numerics.PlaneWaveCube
open Feec.FiniteElement HilbertComplex

/-- The `L²` space of one row on the unit cube. -/
abbrev RowSpaceU : Type :=
  PiLp 2 fun i : Fin 3 => L2F ℝ unitCube ((deRham ℝ 3).ι ((0 : ℤ) + ((i : ℕ) : ℤ)))

/-- The dilation of three-row fields, `U ↦ U(·/2)`. -/
def dilAmb3 : (PiLp 2 fun _ : Fin 3 => RowSpace) →ₗ[ℝ] PiLp 2 fun _ : Fin 3 => RowSpaceU where
  toFun y := WithLp.toLp 2 fun r => WithLp.toLp 2 fun i => dil _ (y r i)
  map_add' y z := PiLp.ext fun r => PiLp.ext fun i => map_add (dil _) (y r i) (z r i)
  map_smul' a y := PiLp.ext fun r => PiLp.ext fun i => map_smul (dil _) a (y r i)

theorem inner_dilAmb3 (y z : PiLp 2 fun _ : Fin 3 => RowSpace) :
    ⟪dilAmb3 y, dilAmb3 z⟫ = 8 * ⟪y, z⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [PiLp.inner_apply, PiLp.inner_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => inner_dil _ (y r i) (z r i)

theorem norm_dilAmb3 (y : PiLp 2 fun _ : Fin 3 => RowSpace) :
    ‖dilAmb3 y‖ = Real.sqrt 8 * ‖y‖ := by
  have h := inner_dilAmb3 y y
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [← Real.sqrt_sq (norm_nonneg (dilAmb3 y)), h, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (norm_nonneg y)]

theorem dEmb3_dilRow3 (N : ℕ) (u : DState3 (whitneyRow N)) :
    dEmb3 (unitRow N) (dilRow3 N u) = dilAmb3 (dEmb3 (whitneyRow N) u) := rfl

end Feec.Numerics.PlaneWaveCube
namespace Feec.Numerics.PlaneWaveCube
open Feec.FiniteElement HilbertComplex

theorem isDirichletCNStep_of_conj {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] (Φ : V ≃ₗ[ℝ] V') {c κ : ℝ} (hc : 0 < c)
    (hΦ : ∀ x y, ⟪Φ x, Φ y⟫ = c * ⟪x, y⟫) {A : V →ₗ[ℝ] V} {A' : V' →ₗ[ℝ] V'}
    (hA : ∀ x y, ⟪A' (Φ x), Φ y⟫ = c * κ * ⟪A x, y⟫) {V₀ : Submodule ℝ V} {V₀' : Submodule ℝ V'}
    (hV₀ : ∀ x, Φ x ∈ V₀' ↔ x ∈ V₀) {s : ℝ} {g' : V} {u u' : V'}
    (h : TimeStepping.IsDirichletCNStep V₀' A' s 0 (Φ g') u u') :
    TimeStepping.IsDirichletCNStep V₀ A (κ * s) 0 g' (Φ.symm u) (Φ.symm u') := by
  have := (isDirichletCNStep_conj_iff Φ hc hΦ hA hV₀ s 0 g' (Φ.symm u) (Φ.symm u')).1
  rw [map_zero, Φ.apply_symm_apply, Φ.apply_symm_apply] at this
  exact this h

theorem norm_conj_sub {V V' X X' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V']
    [Module ℝ V'] [SeminormedAddCommGroup X] [NormedSpace ℝ X] [SeminormedAddCommGroup X']
    [NormedSpace ℝ X'] (Φ : V ≃ₗ[ℝ] V') (emb : V →ₗ[ℝ] X) (emb' : V' →ₗ[ℝ] X')
    (Ψ : X →ₗ[ℝ] X') {c : ℝ} (hΨ : ∀ y, ‖Ψ y‖ = c * ‖y‖) (hcomm : ∀ x, emb' (Φ x) = Ψ (emb x))
    (u : V') (Y : X) : ‖emb' u - Ψ Y‖ = c * ‖emb (Φ.symm u) - Y‖ := by
  conv_lhs => rw [← Φ.apply_symm_apply u]
  rw [hcomm, ← map_sub, hΨ]

/-- **`O(h + Δt²)` convergence of the scheme on the unit cube `(0, 1)³` of `fem4gr`** (the
dilation `x ↦ 2x` of `whitney_cn_error_le`): let `V = (V_r)_r` be a smooth solution of (4.14) on
`[0, T] × cl (0, ½)³` and `U(t, x) = V(t/2, x/2)` the corresponding solution on
`[0, 2T] × cl (0, 1)³` (the system is invariant under `(t, x) ↦ (2t, 2x)`). The Crank–Nicolson
iterates `uₙ` on the dilated Whitney spaces of `(0, 1)³` with step `Δt`, started from the
(dilated) interpolant of `U(0)` and with the boundary DOFs of the interpolants of `U(tₙ)`, satisfy
for `M Δt ≤ 2T`: `‖u_M − U(t_M)‖_{L²(0,1)³} ≤ √8 C L (1 + T) (h_N + (Δt / 2)²)` (the `L²` norm
scales by `√8 = 2^{3/2}`, the step by `½`). -/
theorem unit_cn_error_le {T L : ℝ} (X : Fin 3 → RowSolution T L) (hL0 : 0 ≤ L) (N : ℕ)
    {Δt : ℝ} (hΔt : 0 < Δt) {M : ℕ} (hM : (M : ℝ) * (Δt / 2) ≤ T)
    {u : ℕ → DState3 (unitRow N)}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep (unitInterior3 N) (discreteWave3 (unitRow N))
      (Δt / 2) 0 (dilRow3 N (exactInterp X N ((n + 1 : ℕ) * (Δt / 2)))) (u n) (u (n + 1)))
    (hu0 : u 0 = dilRow3 N (exactInterp X N 0)) :
    ‖dEmb3 (unitRow N) (u M) - dilAmb3 (exactField X (M * (Δt / 2)))‖ ≤
      Real.sqrt 8 * (cnConst * L * (1 + T) * (meshSize N + (Δt / 2) ^ 2)) := by
  have hstep' : ∀ n < M, TimeStepping.IsDirichletCNStep (whitneyInterior3 N)
      (discreteWave3 (whitneyRow N)) (Δt / 2 / 2) 0
      (exactInterp X N ((n + 1 : ℕ) * (Δt / 2))) ((dilRow3 N).symm (u n))
      ((dilRow3 N).symm (u (n + 1))) := fun n hn => by
    have h := isDirichletCNStep_of_conj (dilRow3 N) (by norm_num : (0 : ℝ) < 8)
      (inner_dilRow3 N) (inner_discreteWave3_dilRow3 N) (mem_dilRow3_iff N) (hstep n hn)
    rwa [show (1 / 2 : ℝ) * (Δt / 2) = Δt / 2 / 2 by ring] at h
  have hv0 : (dilRow3 N).symm (u 0) = exactInterp X N 0 := by
    rw [hu0]; exact (dilRow3 N).symm_apply_apply _
  obtain ⟨-, -, -, herr⟩ := whitney_cn_error_le X N (Δt := Δt / 2) (half_pos hΔt) hL0 hM
    (u := fun n => (dilRow3 N).symm (u n)) (g := fun n => exactInterp X N (n * (Δt / 2)))
    hstep' (fun _ _ => sub_self_mem_submodule _ _) hv0
  rw [norm_conj_sub (dilRow3 N) (dEmb3 (whitneyRow N)) (dEmb3 (unitRow N)) dilAmb3 norm_dilAmb3
    (dEmb3_dilRow3 N)]
  exact mul_le_mul_of_nonneg_left herr (Real.sqrt_nonneg _)

end Feec.Numerics.PlaneWaveCube
namespace Feec.Numerics.PlaneWaveCube
open Feec.FiniteElement HilbertComplex

/-- The scalar dilation `f ↦ f(·/2)`, `L²(0, ½)³ → L²(0, 1)³`. -/
abbrev pullU : L2 ℝ (cubeDomain 3) →L[ℝ] L2 ℝ unitCube :=
  pull (𝕜 := ℝ) half_ne_zero' (0 : Fin 3 → ℝ) (isOpen_cubeDomain 3).measurableSet
    preimage_unitCube

theorem norm_pullU (f : L2 ℝ (cubeDomain 3)) : ‖pullU f‖ = Real.sqrt 8 * ‖f‖ := by
  rw [pull_apply, norm_pullₗ, jac_half]; norm_num

theorem inner_pullU (f g : L2 ℝ (cubeDomain 3)) : ⟪pullU f, pullU g⟫ = 8 * ⟪f, g⟫ := by
  rw [pull_apply, pull_apply, inner_pullₗ, jac_half]; norm_num

/-- The entry `E_{rj}` on the unit cube. -/
def entryEU (N : ℕ) (r j : Fin 3) : DState3 (unitRow N) →ₗ[ℝ] L2 ℝ unitCube where
  toFun u := (u r 1).1 (edgeIdx j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The entry `B_{rj}` on the unit cube. -/
def entryBU (N : ℕ) (r j : Fin 3) : DState3 (unitRow N) →ₗ[ℝ] L2 ℝ unitCube where
  toFun u := faceSign j • (u r 2).1 (faceIdx j)
  map_add' u v := smul_add (faceSign j) ((u r 2).1 (faceIdx j)) ((v r 2).1 (faceIdx j))
  map_smul' a u := smul_comm (faceSign j) a ((u r 2).1 (faceIdx j))

/-- The field `σ` on the unit cube (in `L²(0, 1)³`). -/
def sigmaPartU (N : ℕ) : DState3 (unitRow N) →ₗ[ℝ]
    PiLp 2 fun _ : Fin 3 => L2F ℝ unitCube (formIdx 3 ((0 : ℤ) + ((0 : Fin 3) : ℕ))) where
  toFun u := WithLp.toLp 2 fun r => (u r 0).1
  map_add' _ _ := PiLp.ext fun _ => rfl
  map_smul' _ _ := PiLp.ext fun _ => rfl

theorem entryEU_dilRow3 (N : ℕ) (r j : Fin 3) (u : DState3 (whitneyRow N)) :
    entryEU N r j (dilRow3 N u) = pullU (entryE N r j u) := rfl

theorem entryBU_dilRow3 (N : ℕ) (r j : Fin 3) (u : DState3 (whitneyRow N)) :
    entryBU N r j (dilRow3 N u) = pullU (entryB N r j u) := by
  change faceSign j • pullU _ = pullU (faceSign j • _)
  rw [map_smul]
  rfl

/-- The componentwise scalar dilation of a family of `L²` functions. -/
def pullPi {κ : Type*} [Fintype κ] :
    (PiLp 2 fun _ : κ => L2 ℝ (cubeDomain 3)) →ₗ[ℝ] PiLp 2 fun _ : κ => L2 ℝ unitCube where
  toFun z := WithLp.toLp 2 fun p => pullU (z p)
  map_add' z w := PiLp.ext fun p => map_add pullU (z p) (w p)
  map_smul' a z := PiLp.ext fun p => map_smul pullU a (z p)

theorem norm_pullPi {κ : Type*} [Fintype κ] (z : PiLp 2 fun _ : κ => L2 ℝ (cubeDomain 3)) :
    ‖pullPi z‖ = Real.sqrt 8 * ‖z‖ := by
  have h : ⟪pullPi z, pullPi z⟫ = 8 * ⟪z, z⟫ := by
    rw [PiLp.inner_apply, PiLp.inner_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => inner_pullU (z p) (z p)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [← Real.sqrt_sq (norm_nonneg (pullPi z)), h, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (norm_nonneg z)]

theorem norm_skewPart_entryEU (N : ℕ) (u : DState3 (whitneyRow N)) :
    ‖skewPart (entryEU N) (dilRow3 N u)‖ = Real.sqrt 8 * ‖skewPart (entryE N) u‖ := by
  have e : skewPart (entryEU N) (dilRow3 N u) = pullPi (skewPart (entryE N) u) :=
    PiLp.ext fun p => by
      change (1 / 2 : ℝ) • (entryEU N p.1 p.2 (dilRow3 N u) - entryEU N p.2 p.1 (dilRow3 N u)) =
        pullU ((1 / 2 : ℝ) • (entryE N p.1 p.2 u - entryE N p.2 p.1 u))
      rw [entryEU_dilRow3, entryEU_dilRow3, map_smul, map_sub]
  rw [e, norm_pullPi]

theorem norm_skewPart_entryBU (N : ℕ) (u : DState3 (whitneyRow N)) :
    ‖skewPart (entryBU N) (dilRow3 N u)‖ = Real.sqrt 8 * ‖skewPart (entryB N) u‖ := by
  have e : skewPart (entryBU N) (dilRow3 N u) = pullPi (skewPart (entryB N) u) :=
    PiLp.ext fun p => by
      change (1 / 2 : ℝ) • (entryBU N p.1 p.2 (dilRow3 N u) - entryBU N p.2 p.1 (dilRow3 N u)) =
        pullU ((1 / 2 : ℝ) • (entryB N p.1 p.2 u - entryB N p.2 p.1 u))
      rw [entryBU_dilRow3, entryBU_dilRow3, map_smul, map_sub]
  rw [e, norm_pullPi]

theorem norm_tracePart_entryEU (N : ℕ) (u : DState3 (whitneyRow N)) :
    ‖tracePart (entryEU N) (dilRow3 N u)‖ = Real.sqrt 8 * ‖tracePart (entryE N) u‖ := by
  have e : tracePart (entryEU N) (dilRow3 N u) = pullU (tracePart (entryE N) u) := by
    simp only [tracePart, LinearMap.smul_apply, LinearMap.sum_apply, entryEU_dilRow3, map_smul,
      map_sum]
  rw [e, norm_pullU]

theorem norm_tracePart_entryBU (N : ℕ) (u : DState3 (whitneyRow N)) :
    ‖tracePart (entryBU N) (dilRow3 N u)‖ = Real.sqrt 8 * ‖tracePart (entryB N) u‖ := by
  have e : tracePart (entryBU N) (dilRow3 N u) = pullU (tracePart (entryB N) u) := by
    simp only [tracePart, LinearMap.smul_apply, LinearMap.sum_apply, entryBU_dilRow3, map_smul,
      map_sum]
  rw [e, norm_pullU]

theorem norm_toLp_dil {k : ℤ} (z : PiLp 2 fun _ : Fin 3 => L2F ℝ (cubeDomain 3) (formIdx 3 k)) :
    ‖(WithLp.toLp 2 fun r => dil k (z r) : PiLp 2 fun _ : Fin 3 => L2F ℝ unitCube (formIdx 3 k))‖ =
      Real.sqrt 8 * ‖z‖ := by
  have h : ⟪(WithLp.toLp 2 fun r => dil k (z r) : PiLp 2 fun _ : Fin 3 => L2F ℝ unitCube _),
      WithLp.toLp 2 fun r => dil k (z r)⟫ = 8 * ⟪z, z⟫ := by
    rw [PiLp.inner_apply, PiLp.inner_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => inner_dil k (z r) (z r)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg z)]

theorem norm_sigmaPartU (N : ℕ) (u : DState3 (whitneyRow N)) :
    ‖sigmaPartU N (dilRow3 N u)‖ = Real.sqrt 8 * ‖sigmaPart N u‖ := by
  rw [norm_sigmaPart_eq, ← norm_toLp_dil]
  rfl

end Feec.Numerics.PlaneWaveCube
namespace Feec.Numerics.PlaneWaveCube
open Feec.FiniteElement HilbertComplex

/-- The unit-cube iterates are the dilations of half-cube iterates with step `Δt / 2`. -/
theorem unit_half_iterates {T L : ℝ} (X : Fin 3 → RowSolution T L) (N : ℕ) {Δt : ℝ} {M : ℕ}
    {u : ℕ → DState3 (unitRow N)}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep (unitInterior3 N) (discreteWave3 (unitRow N))
      (Δt / 2) 0 (dilRow3 N (exactInterp X N ((n + 1 : ℕ) * (Δt / 2)))) (u n) (u (n + 1)))
    (hu0 : u 0 = dilRow3 N (exactInterp X N 0)) :
    (∀ n < M, TimeStepping.IsDirichletCNStep (whitneyInterior3 N)
      (discreteWave3 (whitneyRow N)) (Δt / 2 / 2) 0
      (exactInterp X N ((n + 1 : ℕ) * (Δt / 2))) ((dilRow3 N).symm (u n))
      ((dilRow3 N).symm (u (n + 1)))) ∧ (dilRow3 N).symm (u 0) = exactInterp X N 0 := by
  refine ⟨fun n hn => ?_, by rw [hu0]; exact (dilRow3 N).symm_apply_apply _⟩
  have h := isDirichletCNStep_of_conj (dilRow3 N) (by norm_num : (0 : ℝ) < 8)
    (inner_dilRow3 N) (inner_discreteWave3_dilRow3 N) (mem_dilRow3_iff N) (hstep n hn)
  rwa [show (1 / 2 : ℝ) * (Δt / 2) = Δt / 2 / 2 by ring] at h

theorem norm_monitorsU_eq (N : ℕ) (u : DState3 (unitRow N)) :
    ‖skewPart (entryEU N) u‖ = Real.sqrt 8 * ‖skewPart (entryE N) ((dilRow3 N).symm u)‖ ∧
      ‖skewPart (entryBU N) u‖ = Real.sqrt 8 * ‖skewPart (entryB N) ((dilRow3 N).symm u)‖ ∧
      ‖tracePart (entryEU N) u‖ = Real.sqrt 8 * ‖tracePart (entryE N) ((dilRow3 N).symm u)‖ ∧
      ‖tracePart (entryBU N) u‖ = Real.sqrt 8 * ‖tracePart (entryB N) ((dilRow3 N).symm u)‖ ∧
      ‖sigmaPartU N u‖ = Real.sqrt 8 * ‖sigmaPart N ((dilRow3 N).symm u)‖ := by
  have hu : u = dilRow3 N ((dilRow3 N).symm u) := ((dilRow3 N).apply_symm_apply u).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [hu]
    exact norm_skewPart_entryEU N _
  · conv_lhs => rw [hu]
    exact norm_skewPart_entryBU N _
  · conv_lhs => rw [hu]
    exact norm_tracePart_entryEU N _
  · conv_lhs => rw [hu]
    exact norm_tracePart_entryBU N _
  · conv_lhs => rw [hu]
    exact norm_sigmaPartU N _

/-- **The `fem4gr` monitors on the unit cube are `O(h + Δt²)` for TSD exact solutions**: in the
setting of `unit_cn_error_le`, if the solution is TSD at `t_M / 2` (half-cube time), the skew and
trace parts of `E`, `B` and `σ` of the unit-cube discrete solution `u_M` are at most
`√8 C L (1 + T) (h_N + (Δt / 2)²)`. -/
theorem unit_cn_monitors_le {T L : ℝ} (X : Fin 3 → RowSolution T L) (hL0 : 0 ≤ L) (N : ℕ)
    {Δt : ℝ} (hΔt : 0 < Δt) {M : ℕ} (hM : (M : ℝ) * (Δt / 2) ≤ T)
    {u : ℕ → DState3 (unitRow N)}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep (unitInterior3 N) (discreteWave3 (unitRow N))
      (Δt / 2) 0 (dilRow3 N (exactInterp X N ((n + 1 : ℕ) * (Δt / 2)))) (u n) (u (n + 1)))
    (hu0 : u 0 = dilRow3 N (exactInterp X N 0)) (hX : IsTSDAt X (M * (Δt / 2))) :
    ‖skewPart (entryEU N) (u M)‖ ≤
        Real.sqrt 8 * (cnConst * L * (1 + T) * (meshSize N + (Δt / 2) ^ 2)) ∧
      ‖skewPart (entryBU N) (u M)‖ ≤
        Real.sqrt 8 * (cnConst * L * (1 + T) * (meshSize N + (Δt / 2) ^ 2)) ∧
      ‖tracePart (entryEU N) (u M)‖ ≤
        Real.sqrt 8 * (cnConst * L * (1 + T) * (meshSize N + (Δt / 2) ^ 2)) ∧
      ‖tracePart (entryBU N) (u M)‖ ≤
        Real.sqrt 8 * (cnConst * L * (1 + T) * (meshSize N + (Δt / 2) ^ 2)) ∧
      ‖sigmaPartU N (u M)‖ ≤
        Real.sqrt 8 * (cnConst * L * (1 + T) * (meshSize N + (Δt / 2) ^ 2)) := by
  obtain ⟨hstep', hv0⟩ := unit_half_iterates X N hstep hu0
  obtain ⟨h1, h2, h3, h4, h5⟩ := whitney_cn_monitors_le X N (Δt := Δt / 2) (half_pos hΔt) hL0 hM
    (u := fun n => (dilRow3 N).symm (u n)) (g := fun n => exactInterp X N (n * (Δt / 2)))
    hstep' (fun _ _ => sub_self_mem_submodule _ _) hv0 hX
  have e := norm_monitorsU_eq N (u M)
  have h8 := Real.sqrt_nonneg 8
  exact ⟨e.1.le.trans (mul_le_mul_of_nonneg_left h1 h8),
    e.2.1.le.trans (mul_le_mul_of_nonneg_left h2 h8),
    e.2.2.1.le.trans (mul_le_mul_of_nonneg_left h3 h8),
    e.2.2.2.1.le.trans (mul_le_mul_of_nonneg_left h4 h8),
    e.2.2.2.2.le.trans (mul_le_mul_of_nonneg_left h5 h8)⟩

end Feec.Numerics.PlaneWaveCube
namespace Feec.Numerics.PlaneWaveCube
open Feec.FiniteElement HilbertComplex

/-- **The dilation of the `L²` class of a continuous form**:
`(w|_{(0,½)³})(·/2) = (w(·/2))|_{(0,1)³}`. -/
theorem dil_formL2Q (k : ℤ) {w : FormField 3} (hw : Continuous w) :
    dil k (formL2Q k w hw) = formL2 isOpen_unitCube.measurableSet isBounded_unitCube k
      ⟨fun x => w ((1 / 2 : ℝ) • x), hw.comp (continuous_const_smul _)⟩ := by
  refine PiLp.ext fun s => Lp.ext ?_
  change (pull half_ne_zero' (0 : Fin 3 → ℝ) (isOpen_cubeDomain 3).measurableSet preimage_unitCube
    (formL2Q k w hw s) : (Fin 3 → ℝ) → ℝ) =ᵐ[_] _
  filter_upwards [coeFn_pullₗ half_ne_zero' (0 : Fin 3 → ℝ) (isOpen_cubeDomain 3).measurableSet
      preimage_unitCube (formL2Q k w hw s),
    ae_comp_aff half_ne_zero' (0 : Fin 3 → ℝ) (isOpen_cubeDomain 3).measurableSet
      preimage_unitCube (coeFn_formL2 (isOpen_cubeDomain 3).measurableSet
        (isBounded_cubeDomain 3) k ⟨w, hw⟩ s),
    coeFn_formL2 isOpen_unitCube.measurableSet isBounded_unitCube k
      ⟨fun x => w ((1 / 2 : ℝ) • x), hw.comp (continuous_const_smul _)⟩ s] with x h1 h2 h3
  rw [pull_apply, h1, h2, h3]
  simp [aff]

/-- **The plane wave of Ch. 7 on the unit cube** `(0, 1)³` at time `t`, as three rows of
`L²((0, 1)³)` forms `(0, E_r, B_r)`. -/
def unitPlaneWave (Ap Ax w t : ℝ) : PiLp 2 fun _ : Fin 3 => RowSpaceU :=
  WithLp.toLp 2 fun r => WithLp.toLp 2 fun i =>
    formL2 isOpen_unitCube.measurableSet isBounded_unitCube _
      ⟨WholeSpaceTSD.rowForms ((planeWaveTSD Ap Ax w).E t) ((planeWaveTSD Ap Ax w).B t) r i,
        (((planeWaveSmooth Ap Ax w 0).row (pwBound_nonneg Ap Ax w) r).contDiff t i).continuous⟩

theorem rowForms_planeWave_half (Ap Ax w t : ℝ) (r i : Fin 3) (x : Fin 3 → ℝ) :
    WholeSpaceTSD.rowForms ((planeWaveTSD Ap Ax (2 * w)).E (t / 2))
        ((planeWaveTSD Ap Ax (2 * w)).B (t / 2)) r i ((1 / 2 : ℝ) • x) =
      WholeSpaceTSD.rowForms ((planeWaveTSD Ap Ax w).E t) ((planeWaveTSD Ap Ax w).B t) r i x := by
  have e : ∀ (P : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3),
      planeWave P (2 * w) (t / 2) ((1 / 2 : ℝ) • x) a b = planeWave P w t x a b := fun P a b => by
    rw [planeWave_apply, planeWave_apply]
    congr 2
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  fin_cases i
  · rfl
  · funext s
    change oneForm (fun j y => planeWave (amplitudeE Ap Ax) (2 * w) (t / 2) y r j)
        ((1 / 2 : ℝ) • x) s = oneForm (fun j y => planeWave (amplitudeE Ap Ax) w t y r j) x s
    simp only [oneForm, e]
  · funext s
    change twoForm (fun j y => planeWave (amplitudeB Ap Ax) (2 * w) (t / 2) y r j)
        ((1 / 2 : ℝ) • x) s = twoForm (fun j y => planeWave (amplitudeB Ap Ax) w t y r j) x s
    simp only [twoForm, e]

/-- **The unit-cube plane wave with frequency `ω` is the dilation of the `(0, ½)³` plane wave with
frequency `2ω`**: `U_ω(t, x) = V_{2ω}(t/2, x/2)`. -/
theorem dilAmb3_exactField_planeWave (Ap Ax w T t : ℝ) :
    dilAmb3 (exactField (planeWaveRows Ap Ax (2 * w) T) (t / 2)) = unitPlaneWave Ap Ax w t := by
  refine PiLp.ext fun r => PiLp.ext fun i => ?_
  change dil _ (formL2Q _ _ _) = formL2 _ _ _ _
  rw [dil_formL2Q]
  exact formL2_congr _ _ _ fun x _ => rowForms_planeWave_half Ap Ax w t r i x

end Feec.Numerics.PlaneWaveCube
namespace Feec.Numerics.PlaneWaveCube
open Feec.FiniteElement HilbertComplex

/-- One step of the scheme on the unit cube. -/
def unitCnStep (N : ℕ) (s : ℝ) (f g' u : DState3 (unitRow N)) : DState3 (unitRow N) :=
  (unit_existsUnique_cnStep3 N s f g' u).exists.choose

/-- The iterates of the scheme on the unit cube with boundary data `gₙ`, no load, from `u₀`. -/
def unitCnIterates (N : ℕ) (s : ℝ) (g : ℕ → DState3 (unitRow N)) (u₀ : DState3 (unitRow N)) :
    ℕ → DState3 (unitRow N)
  | 0 => u₀
  | n + 1 => unitCnStep N s 0 (g (n + 1)) (unitCnIterates N s g u₀ n)

theorem unitCnIterates_spec (N : ℕ) (s : ℝ) (g : ℕ → DState3 (unitRow N))
    (u₀ : DState3 (unitRow N)) (n : ℕ) :
    TimeStepping.IsDirichletCNStep (unitInterior3 N) (discreteWave3 (unitRow N)) s 0
      (g (n + 1)) (unitCnIterates N s g u₀ n) (unitCnIterates N s g u₀ (n + 1)) :=
  (unit_existsUnique_cnStep3 N s 0 (g (n + 1)) _).exists.choose_spec

/-- **The Ch. 7 plane-wave run of `fem4gr` on the unit cube converges at rate `O(h + Δt²)`**
(every `A₊`, `Aₓ`, `ω`): the Crank–Nicolson iterates `uₙ` with step `Δt` on the Whitney spaces
of `(0, 1)³` (dilations of those of `(0, ½)³`), from the interpolated plane wave and with the
interpolated boundary data, satisfy for `M Δt ≤ T_U`
`‖u_M − U_ω(t_M)‖_{L²(0,1)³} ≤ √8 C (|A₊| + |Aₓ|) (1 + 2|ω|)³ (1 + T_U / 2) (h_N + (Δt / 2)²)`,
and so do the five constraint monitors of `u_M`. -/
theorem unit_planeWave_cn_error_le (Ap Ax w T : ℝ) (N : ℕ) {Δt : ℝ} (hΔt : 0 < Δt) {M : ℕ}
    (hM : (M : ℝ) * Δt ≤ 2 * T) {u : ℕ → DState3 (unitRow N)}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep (unitInterior3 N) (discreteWave3 (unitRow N))
      (Δt / 2) 0 (dilRow3 N (exactInterp (planeWaveRows Ap Ax (2 * w) T) N
        ((n + 1 : ℕ) * (Δt / 2)))) (u n) (u (n + 1)))
    (hu0 : u 0 = dilRow3 N (exactInterp (planeWaveRows Ap Ax (2 * w) T) N 0)) :
    ‖dEmb3 (unitRow N) (u M) - unitPlaneWave Ap Ax w (M * Δt)‖ ≤
        Real.sqrt 8 * (cnConst * pwBound Ap Ax (2 * w) * (1 + T) * (meshSize N + (Δt / 2) ^ 2)) ∧
      ‖skewPart (entryEU N) (u M)‖ ≤
        Real.sqrt 8 * (cnConst * pwBound Ap Ax (2 * w) * (1 + T) * (meshSize N + (Δt / 2) ^ 2)) ∧
      ‖skewPart (entryBU N) (u M)‖ ≤
        Real.sqrt 8 * (cnConst * pwBound Ap Ax (2 * w) * (1 + T) * (meshSize N + (Δt / 2) ^ 2)) ∧
      ‖tracePart (entryEU N) (u M)‖ ≤
        Real.sqrt 8 * (cnConst * pwBound Ap Ax (2 * w) * (1 + T) * (meshSize N + (Δt / 2) ^ 2)) ∧
      ‖tracePart (entryBU N) (u M)‖ ≤
        Real.sqrt 8 * (cnConst * pwBound Ap Ax (2 * w) * (1 + T) * (meshSize N + (Δt / 2) ^ 2)) ∧
      ‖sigmaPartU N (u M)‖ ≤
        Real.sqrt 8 *
          (cnConst * pwBound Ap Ax (2 * w) * (1 + T) * (meshSize N + (Δt / 2) ^ 2)) := by
  have hM' : (M : ℝ) * (Δt / 2) ≤ T := by linarith
  have herr := unit_cn_error_le (planeWaveRows Ap Ax (2 * w) T) (pwBound_nonneg _ _ _) N hΔt hM'
    hstep hu0
  have e : dilAmb3 (exactField (planeWaveRows Ap Ax (2 * w) T) (M * (Δt / 2))) =
      unitPlaneWave Ap Ax w (M * Δt) := by
    rw [← dilAmb3_exactField_planeWave Ap Ax w T (M * Δt)]
    congr 2
    ring
  rw [e] at herr
  exact ⟨herr, unit_cn_monitors_le (planeWaveRows Ap Ax (2 * w) T) (pwBound_nonneg _ _ _) N hΔt
    hM' hstep hu0 ((planeWaveSmooth Ap Ax (2 * w) T).isTSDAt (pwBound_nonneg _ _ _) _)⟩

/-- **The unit-cube run exists**: `unitCnIterates` with the interpolated plane-wave data satisfies
the bound of `unit_planeWave_cn_error_le`. -/
theorem unit_planeWave_cnIterates_error_le (Ap Ax w T : ℝ) (N : ℕ) {Δt : ℝ} (hΔt : 0 < Δt)
    {M : ℕ} (hM : (M : ℝ) * Δt ≤ 2 * T) :
    ‖dEmb3 (unitRow N) (unitCnIterates N (Δt / 2)
        (fun n => dilRow3 N (exactInterp (planeWaveRows Ap Ax (2 * w) T) N (n * (Δt / 2))))
        (dilRow3 N (exactInterp (planeWaveRows Ap Ax (2 * w) T) N 0)) M) -
      unitPlaneWave Ap Ax w (M * Δt)‖ ≤
        Real.sqrt 8 * (cnConst * pwBound Ap Ax (2 * w) * (1 + T) * (meshSize N + (Δt / 2) ^ 2)) :=
  (unit_planeWave_cn_error_le Ap Ax w T N hΔt hM
    (u := unitCnIterates N (Δt / 2)
        (fun n => dilRow3 N (exactInterp (planeWaveRows Ap Ax (2 * w) T) N (n * (Δt / 2))))
        (dilRow3 N (exactInterp (planeWaveRows Ap Ax (2 * w) T) N 0)))
    (fun n _ => unitCnIterates_spec N (Δt / 2) _ _ n) rfl).1

end Feec.Numerics.PlaneWaveCube

namespace Feec.Numerics.PlaneWaveCube

open Feec.Mesh

/-- The dilation `x ↦ 2x` of `ℝ³`. -/
def dilate2 : (Fin 3 → ℝ) ≃ᵃ[ℝ] (Fin 3 → ℝ) := boxMap 0 2 two_ne_zero

theorem mesh_ext' {M M' : SimplicialMesh 3} (h1 : M.simplices = M'.simplices)
    (h2 : M.domain = M'.domain) : M = M' := by
  cases M; cases M'; simp only at h1 h2; subst h1; subst h2; rfl

theorem dilate2_boxMap (N : ℕ) (x : Fin 3 → ℝ) :
    dilate2 (boxMap 0 ((1 / 2 : ℝ) / ((N + 1 : ℕ) : ℝ))
      (freudenthalScale_ne_zero (by norm_num : (0 : ℝ) < 1 / 2) (N + 1)) x) =
    boxMap 0 ((1 : ℝ) / ((N + 1 : ℕ) : ℝ)) (freudenthalScale_ne_zero one_pos (N + 1)) x := by
  simp only [dilate2, boxMap_apply, zero_add, smul_smul]
  congr 1
  ring

/-- **The Freudenthal meshes of the unit cube are the images of those of `(0, ½)³` under
`x ↦ 2x`**: `freudenthalMesh 0 1 (N + 1) = (mesh 3 N).map (x ↦ 2x)`. -/
theorem freudenthalMesh_unit_eq_map (N : ℕ) :
    freudenthalMesh (0 : Fin 3 → ℝ) 1 one_pos (N + 1) = (mesh 3 N).map dilate2 := by
  refine mesh_ext' (Finset.ext fun T => ?_) ?_
  · rw [mem_freudenthalMesh_simplices, SimplicialMesh.mem_map_simplices]
    constructor
    · rintro ⟨m, σ, rfl⟩
      refine ⟨_, mem_freudenthalMesh_simplices.2 ⟨m, σ, rfl⟩, Affine.Simplex.ext fun i => ?_⟩
      simp only [mapEquiv_points]
      exact dilate2_boxMap N _
    · rintro ⟨T', hT', rfl⟩
      obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT'
      refine ⟨m, σ, Affine.Simplex.ext fun i => ?_⟩
      simp only [mapEquiv_points]
      exact (dilate2_boxMap N _).symm
  · rw [SimplicialMesh.map_domain, mesh_domain, freudenthalMesh_domain]
    ext x
    simp only [Set.mem_image, cubeDomain, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo,
      dilate2, boxMap_apply, zero_add, Pi.zero_apply]
    constructor
    · intro hx
      refine ⟨(1 / 2 : ℝ) • x, fun i => ?_, by ext i; simp⟩
      have := hx i
      simp only [Pi.smul_apply, smul_eq_mul]
      constructor <;> linarith [this.1, this.2]
    · rintro ⟨y, hy, rfl⟩ i
      have := hy i
      simp only [Pi.smul_apply, smul_eq_mul]
      constructor <;> linarith [this.1, this.2]

end Feec.Numerics.PlaneWaveCube
