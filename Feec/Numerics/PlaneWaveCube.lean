module

public import Feec.Models.Cube.Inhomogeneous
public import Feec.Numerics.CrankNicolsonTable
public import Feec.Counterexamples.BoundedDomainTSD

/-!
# The Ch. 7 plane-wave run on the unit cube, as implemented

The experiment of [QuennevilleBelair2015], Ch. 7, in its `fem4gr` implementation
(<https://github.com/vincentqb/fem4gr>, example `'z-direction plane wave'`): the Einstein–Bianchi
system (4.14) on the unit cube `(0, 1)³`, Crank–Nicolson in time, with the essential boundary data
`σ = 0`, `E × n = E_ex × n`, `B · n = B_ex · n` and the initial value of the exact solution

`E_ex = [[-A₊, -Aₓ, 0], [-Aₓ, A₊, 0], [0, 0, 0]] sin ω(z − t)`,
`B_ex = [[-Aₓ, A₊, 0], [A₊, Aₓ, 0], [0, 0, 0]] sin ω(z − t)`, `σ_ex = 0`

(`Feec.Numerics.CrankNicolson.amplitudeE`, `amplitudeB`, `planeWave`). The thesis states
`ω = 20`, `A₊ = 2`, `Aₓ = ½`; the script runs `ω = 10` with the same amplitudes. Every statement
below holds for all `A₊, Aₓ, ω`.

## Main results

* `planeWaveTSD`: the plane wave is a classical TSD solution of `E' = −curl B`, `B' = curl E` on
  `ℝ³` (`Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD`).
* **`planeWave_unique`**: on the unit cube, the plane wave is the unique solution of
  `U' = L_max U` with its own boundary data and initial value, and it is TSD at every time: TSD
  propagates for the datum actually run. (On every bounded open `Ω`: `planeWave_unique_of_bounded`.)
* **`exists_not_propagates`**: for **every** whole-space TSD solution `R` and every nonempty bounded
  open `Ω`, there is a TSD perturbation `W₀ ∈ D(L) ∩ K` of the initial value such that the
  solution with the boundary data of `R` from the TSD datum `R(0) + W₀` exists and leaves `K` on
  every `[0, T]`, `T > 0` — the homogeneous refutation
  (`Feec.Counterexamples.BoundedDomainTSD.tsd_not_propagates`) transported by the lifting. By
  `Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD.mem_iff` propagation for such data holds exactly
  when it holds for the homogeneous problem from `U(0) − R(0)`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7 (the plane-wave test), §4.10 (Prop 4.17)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ContDiff
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
    pd k (fun y => planeWave P w t y a b) x =
      if k = 2 then w * Real.cos (w * (x 2 - t)) * P a b else 0 := by
  rw [pd, (hasFDerivAt_planeWave P w t x a b).fderiv]
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

/-! ## Uniqueness and TSD propagation for the datum actually run -/

/-- **On every bounded open `Ω`, the plane wave is the unique solution with its own data, and it
is TSD for all time**: every solution `V` of `V' = L_max V` on `[a, b]` with the boundary data of
the plane wave (`σ = 0`, `E × n = E_ex × n`) and `V(a) = (0, E_ex(a), B_ex(a))` is the plane wave,
and `V(t) ∈ {0} × L²(TSD) × L²(TSD)` for all `t ∈ [a, b]`. -/
theorem planeWave_unique_of_bounded (Ap Ax w : ℝ) {Ω : Set R3} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) {a b : ℝ} {V : ℝ → State Ω}
    (hV : Evolution.IsBoundarySolution (thesisWaveMax hΩ) (gradCurl ℝ hΩ).wave (Icc a b) 0
      ((planeWaveTSD Ap Ax w).restrict hΩ hb) V)
    (hV0 : V a = (planeWaveTSD Ap Ax w).restrict hΩ hb a) :
    EqOn V ((planeWaveTSD Ap Ax w).restrict hΩ hb) (Icc a b) ∧
      ∀ t ∈ Icc a b, V t ∈ constraint Ω :=
  ⟨(planeWaveTSD Ap Ax w).restrict_unique hΩ hb hV hV0,
    (planeWaveTSD Ap Ax w).restrict_propagates hΩ hb hV hV0⟩

/-- The unit cube `(0, 1)³`. -/
abbrev unitCube : Set R3 := Models.Cube.Geometry.openCube 0 1

theorem isOpen_unitCube : IsOpen unitCube := Models.Cube.Geometry.isOpen_openCube 0 1

theorem isBounded_unitCube : Bornology.IsBounded unitCube :=
  Models.Cube.Geometry.isBounded_openCube 0 1

theorem nonempty_unitCube : unitCube.Nonempty :=
  ⟨fun _ => 1 / 2, fun i _ => by simp; norm_num⟩

/-- **The Ch. 7 run on the unit cube**: with the thesis' boundary conditions and the inhomogeneous
data of `fem4gr` (`σ = 0`, `E × n = E_ex × n` on `∂(0, 1)³`) and the initial value of the plane
wave, the plane wave is the unique solution on `[0, T]` (the run uses `T = 7.5`), and it is TSD at
every time. -/
theorem planeWave_unique (Ap Ax w T : ℝ) {V : ℝ → State unitCube}
    (hV : Evolution.IsBoundarySolution (thesisWaveMax isOpen_unitCube)
      (gradCurl ℝ isOpen_unitCube).wave (Icc 0 T) 0
      ((planeWaveTSD Ap Ax w).restrict isOpen_unitCube isBounded_unitCube) V)
    (hV0 : V 0 = (planeWaveTSD Ap Ax w).restrict isOpen_unitCube isBounded_unitCube 0) :
    EqOn V ((planeWaveTSD Ap Ax w).restrict isOpen_unitCube isBounded_unitCube) (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, V t ∈ constraint unitCube :=
  planeWave_unique_of_bounded Ap Ax w isOpen_unitCube isBounded_unitCube hV hV0

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

end Feec.Numerics.PlaneWaveCube
