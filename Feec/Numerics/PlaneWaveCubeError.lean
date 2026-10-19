module

public import Feec.Numerics.PlaneWaveCube
public import Feec.Models.Cube.InhomogeneousError

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
