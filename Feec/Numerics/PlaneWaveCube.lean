module

public import Feec.Models.Cube.Inhomogeneous
public import Feec.Numerics.CrankNicolsonTable
public import Feec.Counterexamples.BoundedDomainTSD
public import Feec.Models.Torus.GradCurl
public import Feec.TimeStepping.Cayley

/-!
# The Ch. 7 plane-wave run on the unit cube, as implemented

The experiment of [QuennevilleBelair2015], Ch. 7, in its `fem4gr` implementation
(<https://github.com/vincentqb/fem4gr>, example `'z-direction plane wave'`): the Einstein–Bianchi
system (4.14) (up to `σ ↦ −σ`, as assembled in `fem4gr`) on the unit cube `(0, 1)³`, Crank–Nicolson in time, with the essential boundary data
`σ = 0`, `E × n = E_ex × n`, `B · n = B_ex · n` and the initial value of the exact solution

`E_ex = [[-A₊, -Aₓ, 0], [-Aₓ, A₊, 0], [0, 0, 0]] sin ω(z − t)`,
`B_ex = [[-Aₓ, A₊, 0], [A₊, Aₓ, 0], [0, 0, 0]] sin ω(z − t)`, `σ_ex = 0`

(`Feec.Numerics.CrankNicolson.amplitudeE`, `amplitudeB`, `planeWave`). The thesis states
`ω = 20`, `A₊ = 2`, `Aₓ = ½`; the script runs `ω = 10` with the same amplitudes. Every statement
below holds for all `A₊, Aₓ, ω`.

## Main results

* `planeWaveTSD`: the plane wave is a classical TSD solution of `E' = −curl B`, `B' = curl E` on
  `ℝ³` (`Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD`).
* On every bounded open `Ω`, in particular the unit cube, the restriction of the plane wave is
  the unique solution of `U' = L_max U` with its own boundary data and initial value, and it is
  TSD at every time (`Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD.restrict_unique` for
  `planeWaveTSD`): TSD propagates for the datum actually run.
* **`exists_not_propagates`**: for **every** whole-space TSD solution `R` and every nonempty bounded
  open `Ω`, there is a TSD perturbation `W₀ ∈ D(L) ∩ K` of the initial value such that the
  solution with the boundary data of `R` from the TSD datum `R(0) + W₀` exists and leaves `K` on
  every `[0, T]`, `T > 0` — the homogeneous refutation
  (`Feec.Counterexamples.BoundedDomainTSD.tsd_not_propagates`) transported by the lifting. By
  `Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD.mem_iff` propagation for such data holds exactly
  when it holds for the homogeneous problem from `U(0) − R(0)`.

The spatial discretization of this run (the Crank–Nicolson Whitney scheme with Dirichlet DOFs)
converges at rate `O(h + Δt²)`, with the same rate for the five constraint monitors, on `(0, ½)³`
and on the unit cube of `fem4gr` (`planeWave_cn_error_le`, `unit_planeWave_cn_error_le` in
`Feec/Numerics/PlaneWaveCubeError.lean`).

## The periodic run on `𝕋³`

`fem4gr`'s example `'periodic z-direction plane wave'` runs `ω = 6π`, `A₊ = 1`, `Aₓ = 0` on the
flat torus. On the Fourier side of `Feec.Models.Torus.GradCurl` (coefficients in `ℓ²(ℤ³)`):

* `wave_modeVec`: for every fibre complex, single-frequency fields `δ_k v` lie in `D(L)` and
  `L (δ_k v) = δ_k (L_{2πk} v)`; `fibreWave_pwVec`: `(0, E₀, B₀)` is an eigenvector of the fibre
  wave operator at `2πn e_z` with eigenvalue `−2πi n`.
* `torusPlaneWave`: `U(t) = (2i)⁻¹ (e^{-iωt} u₊ − e^{iωt} u₋)`, `ω = 2πn`, the Fourier
  coefficients of `(0, E₀, B₀) sin ω(z − t)`; `modeVec_kz_mem`: `u±` are TSD.
* **`cnTorusPlaneWave_props`**: the Crank–Nicolson iterates (time-discrete, space-continuous) from
  `U(0)` are `(2i)⁻¹ (λ₊ᵏ u₊ − λ₋ᵏ u₋)` with `|λ±| = 1`: exact energy conservation
  `‖Uₖ‖ = ‖U₀‖`, TSD at every step, and a pure phase error.

Only `ω ∈ 2πℤ` is periodic on the unit torus. Two observations on the `fem4gr` source (read, not
formalized): its periodicity check `near(omega/pi, int(omega/pi + .5))` accepts odd multiples of `π`,
which are not `1`-periodic; and its periodic initial datum has `E0[1][1] = −A₊ sin ωz` instead of
`+A₊ sin ωz`, so `E0` is neither `E_ex(0)` nor trace-free (`tr E0 = −2A₊ sin ωz`). The spatial
discretization of the periodic run (periodic Whitney spaces) is not formalized.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7 (the plane-wave test), §4.10 (Prop 4.17)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ContDiff LinearPMap
open MeasureTheory Set Filter Real Feec.Domain Feec.Models.BoundedDomain
  Feec.Models.Cube.Inhomogeneous Feec.Numerics.CrankNicolson

namespace Feec.Numerics.PlaneWaveCube

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

/-! ## The plane wave as a whole-space TSD solution -/

theorem planeWave_apply (P : Matrix (Fin 3) (Fin 3) ℝ) (w t : ℝ) (x : R3) (a b : Fin 3) :
    planeWave P w t x a b = Real.sin (w * (x 2 - t)) * P a b := by
  simp [planeWave]

/-- `∂ₖ (P_{ab} sin ω(z − t)) = δ_{k2} ω cos ω(z − t) P_{ab}`. -/
theorem pd_planeWave (P : Matrix (Fin 3) (Fin 3) ℝ) (w t : ℝ) (a b k : Fin 3) (x : R3) :
    partialDeriv k (fun y => planeWave P w t y a b) x =
      if k = 2 then w * Real.cos (w * (x 2 - t)) * P a b else 0 := by
  rw [partialDeriv, (hasFDerivAt_planeWave P w t x a b).fderiv]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, Pi.single_apply,
    smul_eq_mul]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

/-- `curl (P sin ω(z − t)) = ω cos ω(z − t) curl_z P`. -/
theorem curlM_planeWave (P : Matrix (Fin 3) (Fin 3) ℝ) (w t : ℝ) (ik : Ix) (x : R3) :
    curlM (fun ij y => planeWave P w t y ij.1 ij.2) ik x =
      w * Real.cos (w * (x 2 - t)) * curlZ P ik.1 ik.2 := by
  obtain ⟨i, k⟩ := ik
  simp only [curlM, pd_planeWave]
  fin_cases k <;> simp [curlZ]

theorem contDiff_planeWave (P : Matrix (Fin 3) (Fin 3) ℝ) (w t : ℝ) (a b : Fin 3) :
    ContDiff ℝ 1 fun y : R3 => planeWave P w t y a b := by
  simp only [planeWave_apply]
  exact ((Real.contDiff_sin.comp ((contDiff_const.mul
    ((contDiff_apply ℝ (fun _ : Fin 3 => ℝ) 2).sub contDiff_const)))).mul contDiff_const)

theorem continuous_curlM_planeWave (P : Matrix (Fin 3) (Fin 3) ℝ) (w : ℝ) (ik : Ix) :
    Continuous fun p : ℝ × R3 => curlM (fun ij y => planeWave P w p.1 y ij.1 ij.2) ik p.2 := by
  simp only [curlM_planeWave]
  fun_prop

/-- **The plane-wave test solution of Ch. 7 is a whole-space TSD solution** (`σ = 0`): `E_ex`,
`B_ex` are `C^∞`, solve `E' = −curl B`, `B' = curl E` on `ℝ × ℝ³`, and are symmetric, trace-free
and divergence-free everywhere (`Feec.Numerics.CrankNicolson.planeWave_solves`). -/
def planeWaveTSD (Ap Ax w : ℝ) : WholeSpaceTSD where
  E t ij y := planeWave (amplitudeE Ap Ax) w t y ij.1 ij.2
  B t ij y := planeWave (amplitudeB Ap Ax) w t y ij.1 ij.2
  contDiff_E t ij := contDiff_planeWave _ w t ij.1 ij.2
  contDiff_B t ij := contDiff_planeWave _ w t ij.1 ij.2
  continuous_curl_E ij := continuous_curlM_planeWave _ w ij
  continuous_curl_B ij := continuous_curlM_planeWave _ w ij
  hasDerivAt_E t ij x := by
    rw [curlM_planeWave, (planeWave_amplitudes Ap Ax).1]
    convert hasDerivAt_planeWave (amplitudeE Ap Ax) w t x ij.1 ij.2 using 1
    ring
  hasDerivAt_B t ij x := by
    rw [curlM_planeWave, (planeWave_amplitudes Ap Ax).2.1]
    convert hasDerivAt_planeWave (amplitudeB Ap Ax) w t x ij.1 ij.2 using 1
    simp only [Matrix.neg_apply]
    ring
  symm_E t i j x := by
    simp only [planeWave_apply]
    fin_cases i <;> fin_cases j <;> simp [amplitudeE]
  symm_B t i j x := by
    simp only [planeWave_apply]
    fin_cases i <;> fin_cases j <;> simp [amplitudeB]
  trace_E t x := by
    simp only [planeWave_apply, Fin.sum_univ_three]
    simp [amplitudeE]
  trace_B t x := by
    simp only [planeWave_apply, Fin.sum_univ_three]
    simp [amplitudeB]
  div_E t j x := by
    simp only [pd_planeWave, Fin.sum_univ_three]
    fin_cases j <;> simp [amplitudeE]
  div_B t j x := by
    simp only [pd_planeWave, Fin.sum_univ_three]
    fin_cases j <;> simp [amplitudeB]

/-! ## The unit cube -/

/-- The unit cube `(0, 1)³`. -/
abbrev unitCube : Set R3 := Models.Cube.Geometry.openCube 0 1

theorem isOpen_unitCube : IsOpen unitCube := Models.Cube.Geometry.isOpen_openCube 0 1

theorem isBounded_unitCube : Bornology.IsBounded unitCube :=
  Models.Cube.Geometry.isBounded_openCube 0 1

/-! ## The homogeneous refutation transported to data from whole-space solutions -/

/-- **TSD propagation fails for perturbed data with the same boundary values**: for every
whole-space TSD solution `R` and every nonempty bounded open `Ω` there is `W₀ ∈ D(L) ∩ K`
(`K = {0} × L²(TSD) × L²(TSD)`) such that, for every `T > 0`, the solution of `U' = L_max U` with
the boundary data of `R` and the TSD initial value `R(0) + W₀` exists, and every such solution
leaves `K` at some `t ∈ [0, T]`. (The homogeneous problem from `W₀ = (0, 0, β)` fails to propagate,
`Feec.Counterexamples.BoundedDomainTSD.tsd_not_propagates`, and `U = R + W`.) -/
theorem exists_not_propagates (W : WholeSpaceTSD) {Ω : Set R3} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ∃ W₀ ∈ (gradCurl ℝ hΩ).wave.domain, W₀ ∈ constraint Ω ∧
      W.restrict hΩ hb 0 + W₀ ∈ constraint Ω ∧ ∀ T > 0,
        (∃ U, U 0 = W.restrict hΩ hb 0 + W₀ ∧ Evolution.IsBoundarySolution (thesisWaveMax hΩ)
          (gradCurl ℝ hΩ).wave (Icc 0 T) 0 (W.restrict hΩ hb) U) ∧
        ∀ U, U 0 = W.restrict hΩ hb 0 + W₀ → Evolution.IsBoundarySolution (thesisWaveMax hΩ)
          (gradCurl ℝ hΩ).wave (Icc 0 T) 0 (W.restrict hΩ hb) U →
          ∃ t ∈ Icc 0 T, U t ∉ constraint Ω := by
  obtain ⟨W₀, hD, hK, hall⟩ :=
    Counterexamples.BoundedDomainTSD.tsd_not_propagates hΩ hb hne (gradCurl ℝ hΩ) le_rfl
  refine ⟨W₀, hD, hK, Submodule.add_mem _ (W.restrict_mem hΩ hb 0) hK, fun T hT => ⟨?_, ?_⟩⟩
  · obtain ⟨U, hU0, hU, -⟩ := W.existsUnique hΩ hb (a := 0) (b := T)
      (U₀ := W.restrict hΩ hb 0 + W₀) (by rwa [add_sub_cancel_left])
    exact ⟨U, hU0, hU⟩
  · intro U hU0 hU
    have hW := (Evolution.isBoundarySolution_iff (wave_le_thesisWaveMax hΩ)
      (W.isLifting hΩ hb _)).1 hU
    rw [W.forcing_eq_zero hΩ hb] at hW
    obtain ⟨t, ht, hnot⟩ := hall T hT (U - W.restrict hΩ hb) (by simp [hU0]) hW
    refine ⟨t, ht, fun hmem => hnot ?_⟩
    exact Submodule.sub_mem _ hmem (W.restrict_mem hΩ hb t)

/-! ## The periodic run on `𝕋³` (Fourier side) -/

open Feec.Fourier.Torus (mode coeFn_mode mode_smul mode_sub mode_sum mode_mem_mulDomain mulOp_mode)

/-- Rewriting the operator in an application. -/
theorem _root_.LinearPMap.apply_of_eq' {G H : Type*} [AddCommGroup G] [Module ℂ G]
    [AddCommGroup H] [Module ℂ H] {f g : G →ₗ.[ℂ] H} (h : f = g) (x : G) (hx : x ∈ f.domain) :
    f ⟨x, hx⟩ = g ⟨x, h ▸ hx⟩ := by
  subst h; rfl

section TorusModes

open Feec.Fourier

variable {d : Type*} [Fintype d] {ι : Type*} [Fintype ι] {c : ComplexShape ι}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, FiniteDimensional ℂ (E i)] [∀ i, CompleteSpace (E i)]
  (S : FibreComplex ℂ (EuclideanSpace ℝ d) c E)

/-- The point `(δ_k vᵢ)ᵢ` of the total space of the torus complex. -/
def modeVec (k : d → ℤ) (v : ∀ i, E i) :
    PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure (d → ℤ)) :=
  WithLp.toLp 2 fun i => mode k (v i)

/-- The fibre wave operator `(L_ξ v)_j = Σᵢ m i j ξ vᵢ − Σₗ (m j l ξ)* vₗ`. -/
def fibreWave (ξ : EuclideanSpace ℝ d) (v : ∀ i, E i) : ∀ j, E j := fun j =>
  ∑ i, S.m i j ξ (v i) - ∑ l, ContinuousLinearMap.adjoint (S.m j l ξ) (v l)

theorem modeVec_mem_wave_domain (k : d → ℤ) (v : ∀ i, E i) :
    modeVec k v ∈ (Torus.complex S).wave.domain := by
  rw [HilbertComplex.mem_wave_domain]
  refine ⟨fun i j => mode_mem_mulDomain _ k (v i), fun i j => ?_⟩
  have e := (Torus.symbolComplex S).adjoint_d i j
  change modeVec k v j ∈ ((Torus.symbolComplex S).toHilbertComplex.d i j)†.domain
  rw [e]
  exact mode_mem_mulDomain _ k (v j)

/-- **Modes are mapped to modes**: `L (δ_k v) = δ_k (L_{2πk} v)` for the wave operator of the
torus complex. -/
theorem wave_modeVec (k : d → ℤ) (v : ∀ i, E i) :
    (Torus.complex S).wave ⟨modeVec k v, modeVec_mem_wave_domain S k v⟩ =
      modeVec k (fibreWave S (Torus.freq k) v) := by
  refine PiLp.ext fun j => ?_
  rw [HilbertComplex.wave_apply]
  simp only [modeVec, fibreWave, mode_sub, mode_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact mulOp_mode _ k (v i) _
  · refine Finset.sum_congr rfl fun l _ => ?_
    have e : ((Torus.complex S).d j l)† = Operator.mulOp (Measure.count : Measure (d → ℤ))
        fun a => ContinuousLinearMap.adjoint (S.m j l (Torus.freq a)) :=
      (Torus.symbolComplex S).adjoint_d j l
    rw [LinearPMap.apply_of_eq' e]
    exact mulOp_mode _ k (v l) _

end TorusModes

section PeriodicRun

open Feec.Fourier Feec.Fourier.GradCurl ShortHilbertComplex

/-- A real amplitude as a complex matrix. -/
def cAmp (P : Matrix (Fin 3) (Fin 3) ℝ) : Mat := ofMatrix (P.map fun r : ℝ => (r : ℂ))

@[simp] theorem cAmp_apply (P : Matrix (Fin 3) (Fin 3) ℝ) (ab : Fin 3 × Fin 3) :
    cAmp P ab = (P ab.1 ab.2 : ℂ) := rfl

/-- The fibre vector `(0, E₀, B₀)` of the plane wave. -/
def pwVec (Ap Ax : ℝ) : ∀ i : Fin 3, W3 Vec Mat Mat i
  | 0 => (0 : Vec)
  | 1 => cAmp (amplitudeE Ap Ax)
  | 2 => cAmp (amplitudeB Ap Ax)

/-- The wave vector `(0, 0, n) ∈ ℤ³`: the mode `e^{2πi n z}`. -/
def kz (n : ℤ) : Fin 3 → ℤ := Pi.single 2 n

theorem freq_kz (n : ℤ) (j : Fin 3) :
    Torus.freq (kz n) j = if j = 2 then 2 * Real.pi * n else 0 := by
  fin_cases j <;> simp [kz, Torus.freq_apply]

/-- `curl_ξ (P) = i ω curl_z P` at `ξ = 2πn e_z`, `ω = 2πn`. -/
theorem curl_kz (n : ℤ) (P : Matrix (Fin 3) (Fin 3) ℝ) :
    curl (Torus.freq (kz n)) (cAmp P) =
      (Complex.I * (2 * Real.pi * n : ℝ)) • cAmp (curlZ P) := by
  ext ⟨a, b⟩
  rw [curl_apply]
  simp only [freq_kz, Fin.sum_univ_three, leviCivita3_apply, PiLp.smul_apply, smul_eq_mul,
    cAmp_apply]
  fin_cases b <;> simp [curlZ] <;> ring

/-- `div_ξ P = 0` at `ξ = 2πn e_z` for an amplitude with vanishing third column. -/
theorem div_kz_eq_zero (n : ℤ) (P : Matrix (Fin 3) (Fin 3) ℝ) (hP : ∀ a, P a 2 = 0) :
    div (Torus.freq (kz n)) (cAmp P) = 0 := by
  ext a
  rw [div_apply]
  simp [kz, Pi.single_apply, Fin.sum_univ_three, hP]

theorem fibreWave_zero (ξ : Freq) (v : ∀ i : Fin 3, W3 Vec Mat Mat i) :
    fibreWave Fourier.GradCurl.gradCurl ξ v 0 = -div ξ (v 1) := by
  unfold fibreWave
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  have h0 : Fourier.GradCurl.gradCurl.m 0 0 ξ = 0 := rfl
  have h1 : Fourier.GradCurl.gradCurl.m 1 0 ξ = 0 := rfl
  have h2 : Fourier.GradCurl.gradCurl.m 2 0 ξ = 0 := rfl
  have h4 : Fourier.GradCurl.gradCurl.m 0 2 ξ = 0 := rfl
  have h5 : ContinuousLinearMap.adjoint (Fourier.GradCurl.gradCurl.m 0 1 ξ) = div ξ :=
    adjoint_grad ξ
  rw [h0, h1, h2, h4, h5]
  simp; rfl

theorem fibreWave_one (ξ : Freq) (v : ∀ i : Fin 3, W3 Vec Mat Mat i) :
    fibreWave Fourier.GradCurl.gradCurl ξ v 1 = grad ξ (v 0) - curl ξ (v 2) := by
  unfold fibreWave
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  have h0 : Fourier.GradCurl.gradCurl.m 0 1 ξ = grad ξ := rfl
  have h1 : Fourier.GradCurl.gradCurl.m 1 1 ξ = 0 := rfl
  have h2 : Fourier.GradCurl.gradCurl.m 2 1 ξ = 0 := rfl
  have h3 : Fourier.GradCurl.gradCurl.m 1 0 ξ = 0 := rfl
  have h5 : ContinuousLinearMap.adjoint (Fourier.GradCurl.gradCurl.m 1 2 ξ) = curl ξ :=
    adjoint_curl ξ
  rw [h0, h1, h2, h3, h5]
  simp; rfl

theorem fibreWave_two (ξ : Freq) (v : ∀ i : Fin 3, W3 Vec Mat Mat i) :
    fibreWave Fourier.GradCurl.gradCurl ξ v 2 = curl ξ (v 1) := by
  unfold fibreWave
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  have h0 : Fourier.GradCurl.gradCurl.m 0 2 ξ = 0 := rfl
  have h1 : Fourier.GradCurl.gradCurl.m 1 2 ξ = curl ξ := rfl
  have h2 : Fourier.GradCurl.gradCurl.m 2 2 ξ = 0 := rfl
  have h3 : Fourier.GradCurl.gradCurl.m 2 0 ξ = 0 := rfl
  have h4 : Fourier.GradCurl.gradCurl.m 2 1 ξ = 0 := rfl
  rw [h0, h1, h2, h3, h4]
  simp; rfl

theorem cAmp_neg (P : Matrix (Fin 3) (Fin 3) ℝ) : cAmp (-P) = -cAmp P := by
  ext ab; simp

/-- **The plane-wave mode is an eigenvector of the fibre wave operator**:
`L_ξ (0, E₀, B₀) = −i ω (0, E₀, B₀)` at `ξ = 2πn e_z`, `ω = 2πn`. -/
theorem fibreWave_pwVec (Ap Ax : ℝ) (n : ℤ) :
    fibreWave Fourier.GradCurl.gradCurl (Torus.freq (kz n)) (pwVec Ap Ax) =
      (-(Complex.I * (2 * Real.pi * n : ℝ))) • pwVec Ap Ax := by
  obtain ⟨hB, hE, -, -, -, -, cE, -⟩ := planeWave_amplitudes Ap Ax
  funext j
  match j with
  | 0 =>
    rw [fibreWave_zero]
    change -div (Torus.freq (kz n)) (cAmp (amplitudeE Ap Ax)) =
      (-(Complex.I * (2 * Real.pi * n : ℝ))) • (0 : Vec)
    rw [div_kz_eq_zero n _ cE, neg_zero, smul_zero]
  | 1 =>
    rw [fibreWave_one]
    change grad (Torus.freq (kz n)) (0 : Vec) - curl (Torus.freq (kz n)) (cAmp (amplitudeB Ap Ax)) =
      (-(Complex.I * (2 * Real.pi * n : ℝ))) • cAmp (amplitudeE Ap Ax)
    rw [map_zero, zero_sub, curl_kz, hB, neg_smul]
  | 2 =>
    rw [fibreWave_two]
    change curl (Torus.freq (kz n)) (cAmp (amplitudeE Ap Ax)) =
      (-(Complex.I * (2 * Real.pi * n : ℝ))) • cAmp (amplitudeB Ap Ax)
    rw [curl_kz, hE, cAmp_neg, smul_neg, neg_smul]

end PeriodicRun

section PeriodicSolution

open Feec.Fourier Feec.Fourier.GradCurl ShortHilbertComplex Models.Torus.GradCurl

theorem modeVec_smul {d : Type*} [Fintype d] {ι : Type*} {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] (k : d → ℤ) (c : ℂ)
    (v : ∀ i, E i) : modeVec k (c • v) = c • modeVec k v :=
  PiLp.ext fun i => mode_smul k c (v i)

/-- The coefficients of `(0, E₀, B₀) e^{2πi n z}` (positive frequency). -/
abbrev uPlus (Ap Ax : ℝ) (n : ℤ) : PiLp 2 Space := modeVec (kz n) (pwVec Ap Ax)

/-- The coefficients of `(0, E₀, B₀) e^{-2πi n z}` (negative frequency). -/
abbrev uMinus (Ap Ax : ℝ) (n : ℤ) : PiLp 2 Space := modeVec (kz (-n)) (pwVec Ap Ax)

theorem mem_domain_modeVec (Ap Ax : ℝ) (n : ℤ) :
    modeVec (kz n) (pwVec Ap Ax) ∈ complex.wave.domain :=
  modeVec_mem_wave_domain Fourier.GradCurl.gradCurl (kz n) (pwVec Ap Ax)

/-- **`L u₊ = −i ω u₊`** with `ω = 2πn`. -/
theorem wave_modeVec_kz (Ap Ax : ℝ) (n : ℤ) :
    complex.wave ⟨_, mem_domain_modeVec Ap Ax n⟩ =
      (-(Complex.I * (2 * Real.pi * n : ℝ))) • modeVec (kz n) (pwVec Ap Ax) := by
  exact (wave_modeVec Fourier.GradCurl.gradCurl (kz n) (pwVec Ap Ax)).trans
    (by rw [fibreWave_pwVec, modeVec_smul])

/-- The plane wave modes are TSD: `δ_k (0, E₀, B₀) ∈ K = {0} × L²(TSD) × L²(TSD)`. -/
theorem modeVec_kz_mem (Ap Ax : ℝ) (n : ℤ) :
    modeVec (kz n) (pwVec Ap Ax) ∈ HilbertComplex.totalSub Models.Torus.GradCurl.constraint := by
  obtain ⟨-, -, sE, sB, tE, tB, cE, cB⟩ := planeWave_amplitudes Ap Ax
  intro i
  refine Operator.mem_fibreSub.2 (ae_of_all _ fun a => ?_)
  change mode (kz n) (pwVec Ap Ax i) a ∈ tsdK i (Torus.freq a)
  rw [coeFn_mode]
  by_cases ha : a = kz n
  · subst ha
    rw [Pi.single_eq_same]
    have hmem : ∀ P : Matrix (Fin 3) (Fin 3) ℝ, P.IsSymm → P.trace = 0 → (∀ i, P i 2 = 0) →
        cAmp P ∈ tsd (Torus.freq (kz n)) := fun P hs ht hc => by
      refine mem_tsd.2 ⟨?_, ?_, ?_⟩
      · ext a b
        simp only [Matrix.transpose_apply, toMatrix_apply, cAmp_apply]
        rw [show P b a = P a b from by simpa using congrFun (congrFun hs a) b]
      · simp only [Matrix.trace, Matrix.diag, toMatrix_apply, cAmp_apply]
        have := ht
        simp only [Matrix.trace, Matrix.diag] at this
        exact_mod_cast this
      · ext a
        simp [Matrix.mulVec, dotProduct, cfreq, kz, Pi.single_apply, Fin.sum_univ_three, hc]
    match i with
    | 0 => exact Submodule.zero_mem _
    | 1 => exact hmem _ sE tE cE
    | 2 => exact hmem _ sB tB cB
  · rw [Pi.single_eq_of_ne ha]
    exact Submodule.zero_mem _

/-- **The periodic plane wave on `𝕋³`** (`ω = 2πn`, `n ∈ ℤ`; `fem4gr` runs `ω = 6π`), on the
Fourier side: the coefficients of `(0, E₀, B₀) sin ω(z − t)` are
`U(t) = (2i)⁻¹ (e^{-iωt} u₊ − e^{iωt} u₋)`. -/
def torusPlaneWave (Ap Ax : ℝ) (n : ℤ) (t : ℝ) : PiLp 2 Space :=
  (2 * Complex.I)⁻¹ • (Complex.exp (-(Complex.I * (2 * Real.pi * n : ℝ)) * t) • uPlus Ap Ax n -
    Complex.exp (Complex.I * (2 * Real.pi * n : ℝ) * t) • uMinus Ap Ax n)

end PeriodicSolution

section PeriodicTheorems

open Feec.Fourier Feec.Fourier.GradCurl ShortHilbertComplex Models.Torus.GradCurl

variable (Ap Ax : ℝ) (n : ℤ)

/-- The frequency `ω = 2πn` as a complex number. -/
abbrev omegaC : ℂ := ((2 * Real.pi * n : ℝ) : ℂ)

theorem wave_uMinus :
    complex.wave ⟨uMinus Ap Ax n, mem_domain_modeVec Ap Ax (-n)⟩ =
      (Complex.I * omegaC n) • uMinus Ap Ax n := by
  rw [wave_modeVec_kz]
  congr 1
  push_cast
  ring

/-! ### Crank–Nicolson for the periodic run -/

/-- The CN amplification factor `λ(μ) = (1 + s μ) / (1 − s μ)` at the eigenvalue `μ`. -/
abbrev amp (s : ℝ) (μ : ℂ) : ℂ := (1 + (s : ℂ) * μ) / (1 - (s : ℂ) * μ)

theorem one_sub_ne_zero (s : ℝ) {μ : ℂ} (hμ : μ.re = 0) : 1 - (s : ℂ) * μ ≠ 0 := fun h => by
  have := congrArg Complex.re h
  simp [hμ] at this

/-- **The Crank–Nicolson solution of the periodic run, in closed form**:
`Uₖ = (2i)⁻¹ (λ₊ᵏ u₊ − λ₋ᵏ u₋)`, `λ± = (1 ∓ i s ω) / (1 ± i s ω)`, `s = Δt / 2`. -/
def cnTorusPlaneWave (s : ℝ) (k : ℕ) : PiLp 2 Space :=
  (2 * Complex.I)⁻¹ • (amp s (-(Complex.I * omegaC n)) ^ k • uPlus Ap Ax n -
    amp s (Complex.I * omegaC n) ^ k • uMinus Ap Ax n)

theorem cnTorusPlaneWave_zero (s : ℝ) :
    cnTorusPlaneWave Ap Ax n s 0 = torusPlaneWave Ap Ax n 0 := by
  simp [cnTorusPlaneWave, torusPlaneWave]

/-- Each `Uₖ ↦ Uₖ₊₁` is a Crank–Nicolson step of the periodic Hodge wave operator. -/
theorem isCNStep_cnTorusPlaneWave (s : ℝ) (k : ℕ) :
    TimeStepping.IsCNStep complex.wave s (cnTorusPlaneWave Ap Ax n s k)
      (cnTorusPlaneWave Ap Ax n s (k + 1)) := by
  have hp := TimeStepping.isCNStep_of_eigen (mem_domain_modeVec Ap Ax n) (wave_modeVec_kz Ap Ax n)
    (s := s) (one_sub_ne_zero s (by simp))
  have hm := TimeStepping.isCNStep_of_eigen (mem_domain_modeVec Ap Ax (-n)) (wave_uMinus Ap Ax n)
    (s := s) (one_sub_ne_zero s (by simp))
  have := ((hp.smul (amp s (-(Complex.I * omegaC n)) ^ k)).add
    ((hm.smul (amp s (Complex.I * omegaC n) ^ k)).smul (-1))).smul (2 * Complex.I)⁻¹
  convert this using 1
  · simp only [cnTorusPlaneWave]
    module
  · simp only [cnTorusPlaneWave, amp, pow_succ]
    module

/-- **Discrete energy identity and constraint preservation for the periodic run**: the CN
iterates conserve the `L²` energy exactly, `‖Uₖ‖ = ‖U₀‖`, stay TSD, and the amplification factors
have modulus one (`TimeStepping.norm_amplification_eq_one`): CN has a pure phase error,
`λ₊ = e^{-iθ}`, `θ = 2 arctan(s ω) ≠ 2 s ω` (`amp_eq_exp_phase`). Every CN sequence from `U₀` is
this one. -/
theorem cnTorusPlaneWave_props (s : ℝ) :
    (∀ k, ‖cnTorusPlaneWave Ap Ax n s k‖ = ‖torusPlaneWave Ap Ax n 0‖) ∧
    (∀ k, cnTorusPlaneWave Ap Ax n s k ∈
      HilbertComplex.totalSub Models.Torus.GradCurl.constraint) ∧
    ‖amp s (-(Complex.I * omegaC n))‖ = 1 ∧ ‖amp s (Complex.I * omegaC n)‖ = 1 ∧
    ∀ V : ℕ → PiLp 2 Space, V 0 = torusPlaneWave Ap Ax n 0 →
      (∀ k, TimeStepping.IsCNStep complex.wave s (V k) (V (k + 1))) →
        ∀ k, V k = cnTorusPlaneWave Ap Ax n s k := by
  refine ⟨fun k => ?_, fun k => ?_, ?_, ?_, fun V hV0 hV k => ?_⟩
  · rw [TimeStepping.norm_eq_of_forall_isCNStep complex.isSkewAdjoint_wave.isSkewSymmetric
      (isCNStep_cnTorusPlaneWave Ap Ax n s) k, cnTorusPlaneWave_zero]
  · exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.smul_mem _ _ (modeVec_kz_mem Ap Ax n))
      (Submodule.smul_mem _ _ (modeVec_kz_mem Ap Ax (-n))))
  · have e : -(Complex.I * omegaC n) = Complex.I * ((-(2 * Real.pi * n) : ℝ) : ℂ) := by
      rw [Complex.ofReal_neg]; ring
    rw [e]
    exact TimeStepping.norm_amplification_eq_one s _
  · exact TimeStepping.norm_amplification_eq_one s _
  · induction k with
    | zero => rw [hV0, cnTorusPlaneWave_zero]
    | succ k ih =>
      have h1 := hV k
      rw [ih] at h1
      exact h1.unique_of_isSkewSymmetric complex.isSkewAdjoint_wave.isSkewSymmetric
        (isCNStep_cnTorusPlaneWave Ap Ax n s k)

/-- **The phase error of the periodic run**: the CN amplification factor of the mode `e^{-iω(z−t)}`
is `e^{-iθ}` with `θ = 2 arctan(s ω)`, while the exact flow over `Δt = 2 s` is `e^{-2isω}`; for
`s ≠ 0` and `n ≠ 0` the phases differ (`θ < 2 s ω` for `s ω > 0`). -/
theorem amp_eq_exp_phase (s : ℝ) :
    amp s (-(Complex.I * omegaC n)) =
      Complex.exp (-(((2 * Real.arctan (s * (2 * Real.pi * n)) : ℝ) : ℂ) * Complex.I)) ∧
    (s ≠ 0 → n ≠ 0 → 2 * Real.arctan (s * (2 * Real.pi * n)) ≠ 2 * (s * (2 * Real.pi * n))) := by
  refine ⟨?_, fun hs hn => TimeStepping.two_mul_arctan_ne_two_mul ?_⟩
  · have e : -(Complex.I * omegaC n) = Complex.I * ((-(2 * Real.pi * n) : ℝ) : ℂ) := by
      rw [Complex.ofReal_neg]; ring
    rw [amp, e, TimeStepping.amplification_eq_exp, mul_neg, Real.arctan_neg]
    congr 1; push_cast; ring
  · have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have := Real.pi_pos
    positivity

end PeriodicTheorems

end Feec.Numerics.PlaneWaveCube
