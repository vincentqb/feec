module

public import Feec.Algebra.MatrixSymbol
public import Feec.ForMathlib.Calculus.Partial
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Crank–Nicolson experiment: plane-wave test solution and Table 7.1

Numerical checks behind the thesis' Crank–Nicolson experiment for the linearized
Einstein–Bianchi system.

* **The plane-wave test solution.** The thesis gives only the electric part
  `E = E₀ sin(ω(z - t))`. With the magnetic partner `B = B₀ sin(ω(z - t))`, both fields are
  symmetric, trace-free and row-wise divergence-free, and solve `Ė = -curl B`, `Ḃ = curl E`
  classically on `ℝ³` (`planeWave_solves`; amplitude identities `planeWave_amplitudes`). The
  row-wise `curl`/`div` are `Feec.MatrixSymbol.curl`/`div` applied to the true spatial jet.
* **Table 7.1.** Step counts `⌊T/Δt_k⌋ = 900, 1272, 1800, 2545` for `Δt_k = 1/(120 √2^k)` and
  `T = 7.5` (`stepCount_table`); the runs on meshes `k = 1, 3` stop short of `T`
  (`finalTime_table`); cell counts `6 (4·2^k)³` (`cellCount_table`).

The Crank–Nicolson schemes themselves are `Feec.TimeStepping.cayley` (any skew-adjoint
generator) with the block-matrix form in `Feec.TimeStepping.BlockMatrix`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7 (Table 7.1, the plane-wave test), §3.5 (plane waves)
* [R. M. Wald, *General Relativity*][Wald1984] (linearized plane waves in TT gauge)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Real

@[expose] public noncomputable section

namespace Feec.Numerics.CrankNicolson

/-! ### The plane-wave test solution -/

/-- Jet of a matrix field depending on `z = x₂` only, with `∂_z` part `P`. -/
def zJet (P : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ := Pi.single 2 P

/-- Amplitude of the row-wise curl of `P φ(z)`: `(curl (P φ))ᵢ = φ'(z) (-P i 1, P i 0, 0)`. -/
def curlZ (P : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => ![-P i 1, P i 0, 0] j

/-- Electric amplitude of the plane wave. [QuennevilleBelair2015], Ch. 7 -/
def amplitudeE (Ap Ax : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-Ap, -Ax, 0; -Ax, Ap, 0; 0, 0, 0]

/-- Magnetic amplitude of the plane wave (absent from the thesis). [QuennevilleBelair2015], Ch. 7 -/
def amplitudeB (Ap Ax : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-Ax, Ap, 0; Ap, Ax, 0; 0, 0, 0]

theorem curl_zJet (P : Matrix (Fin 3) (Fin 3) ℝ) : MatrixSymbol.curl (zJet P) = curlZ P := by
  ext a b
  simp only [MatrixSymbol.curl, zJet, Matrix.of_apply, Fin.sum_univ_three, Pi.single_apply,
    leviCivita3_apply]
  fin_cases b <;> simp [curlZ]

theorem div_zJet (P : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3) :
    MatrixSymbol.div (zJet P) a = P a 2 := by
  simp [MatrixSymbol.div, zJet, Fin.sum_univ_three, Pi.single_apply]

theorem curl_smul (c : ℝ) (J : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) :
    MatrixSymbol.curl (c • J) = c • MatrixSymbol.curl J :=
  MatrixSymbol.curl_smul c J

theorem div_smul (c : ℝ) (J : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) :
    MatrixSymbol.div (c • J) = c • MatrixSymbol.div J := by
  ext a
  simp [MatrixSymbol.div, Finset.mul_sum]

/-- **Amplitude identities** for `Ė = -curl B`, `Ḃ = curl E`: `curl_z B₀ = E₀`,
`curl_z E₀ = -B₀`, both symmetric, trace-free, with vanishing third column. [QuennevilleBelair2015], Ch. 7 -/
theorem planeWave_amplitudes (Ap Ax : ℝ) :
    curlZ (amplitudeB Ap Ax) = amplitudeE Ap Ax ∧ curlZ (amplitudeE Ap Ax) = -amplitudeB Ap Ax ∧
    (amplitudeE Ap Ax).IsSymm ∧ (amplitudeB Ap Ax).IsSymm ∧
    Matrix.trace (amplitudeE Ap Ax) = 0 ∧ Matrix.trace (amplitudeB Ap Ax) = 0 ∧
    (∀ i, amplitudeE Ap Ax i 2 = 0) ∧ (∀ i, amplitudeB Ap Ax i 2 = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  first
  | (ext i j; fin_cases i <;> fin_cases j <;> simp [curlZ, amplitudeE, amplitudeB])
  | (intro i; fin_cases i <;> simp [amplitudeE, amplitudeB])
  | (simp [Matrix.trace, Fin.sum_univ_succ, amplitudeE, amplitudeB])

/-- The plane-wave field `P sin(ω(z - t))`, `z = x₂`. -/
def planeWave (P : Matrix (Fin 3) (Fin 3) ℝ) (ω t : ℝ) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Real.sin (ω * (x 2 - t)) • P

/-- Spatial jet `(∂_c F_{ab})(x)` of a matrix field. -/
def jetOf (F : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    Fin 3 → Matrix (Fin 3) (Fin 3) ℝ :=
  fun c => Matrix.of fun a b => partialDeriv c (fun y => F y a b) x

theorem hasFDerivAt_planeWave (P : Matrix (Fin 3) (Fin 3) ℝ) (ω t : ℝ) (x : Fin 3 → ℝ)
    (a b : Fin 3) :
    HasFDerivAt (fun y : Fin 3 → ℝ => planeWave P ω t y a b)
      ((ω * Real.cos (ω * (x 2 - t)) * P a b) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2) x := by
  have h1 : HasFDerivAt (fun y : Fin 3 → ℝ => y 2)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2) x :=
    hasFDerivAt_apply 2 x
  have h2 := ((h1.sub_const t).const_mul ω).sin.mul_const (P a b)
  convert h2 using 1
  · ext y; simp [planeWave, mul_comm]
  · ext v; simp; ring

/-- The spatial jet of `P sin(ω(z - t))` is `ω cos(ω(z - t))` times the `z`-jet `P`. -/
theorem jetOf_planeWave (P : Matrix (Fin 3) (Fin 3) ℝ) (ω t : ℝ) (x : Fin 3 → ℝ) :
    jetOf (planeWave P ω t) x = (ω * Real.cos (ω * (x 2 - t))) • zJet P := by
  ext c a b
  simp only [jetOf, Matrix.of_apply, (hasFDerivAt_planeWave P ω t x a b).partialDeriv_eq]
  fin_cases c <;> simp [zJet]

theorem hasDerivAt_planeWave (P : Matrix (Fin 3) (Fin 3) ℝ) (ω t : ℝ) (x : Fin 3 → ℝ)
    (a b : Fin 3) :
    HasDerivAt (fun t => planeWave P ω t x a b) (-(ω * Real.cos (ω * (x 2 - t))) * P a b) t := by
  have h := (((hasDerivAt_id t).const_sub (x 2)).const_mul ω).sin.mul_const (P a b)
  convert h using 1
  · ext t; simp [planeWave, mul_comm]
  · simp only [_root_.id]; ring

/-- **The plane-wave test solution** is a classical TSD solution of `Ė = -curl B`, `Ḃ = curl E`
on `ℝ³`: `E = E₀ sin(ω(z - t))`, `B = B₀ sin(ω(z - t))` are symmetric, trace-free and row-wise
divergence-free, and solve the system entrywise at every `(x, t)`. Not claimed: the homogeneous
essential boundary conditions on the unit cube, which this wave violates. [QuennevilleBelair2015], Ch. 7 -/
theorem planeWave_solves (Ap Ax ω t : ℝ) (x : Fin 3 → ℝ) :
    (∀ a b, HasDerivAt (fun t => planeWave (amplitudeE Ap Ax) ω t x a b)
      (-(MatrixSymbol.curl (jetOf (planeWave (amplitudeB Ap Ax) ω t) x)) a b) t) ∧
    (∀ a b, HasDerivAt (fun t => planeWave (amplitudeB Ap Ax) ω t x a b)
      (MatrixSymbol.curl (jetOf (planeWave (amplitudeE Ap Ax) ω t) x) a b) t) ∧
    MatrixSymbol.div (jetOf (planeWave (amplitudeE Ap Ax) ω t) x) = 0 ∧
    MatrixSymbol.div (jetOf (planeWave (amplitudeB Ap Ax) ω t) x) = 0 ∧
    (planeWave (amplitudeE Ap Ax) ω t x).IsSymm ∧ (planeWave (amplitudeB Ap Ax) ω t x).IsSymm ∧
    (planeWave (amplitudeE Ap Ax) ω t x).trace = 0 ∧
    (planeWave (amplitudeB Ap Ax) ω t x).trace = 0 := by
  obtain ⟨hB, hE, sE, sB, tE, tB, cE, cB⟩ := planeWave_amplitudes Ap Ax
  refine ⟨fun a b => ?_, fun a b => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [jetOf_planeWave, curl_smul, curl_zJet, hB]
    convert hasDerivAt_planeWave (amplitudeE Ap Ax) ω t x a b using 1
    simp
  · rw [jetOf_planeWave, curl_smul, curl_zJet, hE]
    convert hasDerivAt_planeWave (amplitudeB Ap Ax) ω t x a b using 1
    simp
  · ext a; rw [jetOf_planeWave, div_smul]; simp [div_zJet, cE]
  · ext a; rw [jetOf_planeWave, div_smul]; simp [div_zJet, cB]
  · exact sE.smul _
  · exact sB.smul _
  · simp [planeWave, Matrix.trace_smul, tE]
  · simp [planeWave, Matrix.trace_smul, tB]

/-! ### Table 7.1 -/

/-- Time step on mesh `k = 0, …, 3`: `Δt_k = 1 / (120 √2^k)`. [QuennevilleBelair2015], Ch. 7 -/
def dt (k : ℕ) : ℝ := 1 / (120 * Real.sqrt 2 ^ k)

/-- Number of Crank–Nicolson steps taken to reach `T = 7.5`. -/
def stepCount (k : ℕ) : ℕ := ⌊(7.5 : ℝ) / dt k⌋₊

theorem sqrt_two_bounds : (1.4142 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.4143 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem div_dt (k : ℕ) : (7.5 : ℝ) / dt k = 7.5 * (120 * Real.sqrt 2 ^ k) := by
  rw [dt, div_div_eq_mul_div, div_one]

/-- `⌊7.5 · 120√2⌋ = 1272`. -/
theorem floor_mesh_one : ⌊(7.5 : ℝ) * (120 * Real.sqrt 2)⌋₊ = 1272 := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  rw [Nat.floor_eq_iff (by positivity)]
  constructor <;> push_cast <;> nlinarith

/-- `⌊7.5 · 240√2⌋ = 2545`. -/
theorem floor_mesh_three : ⌊(7.5 : ℝ) * (240 * Real.sqrt 2)⌋₊ = 2545 := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  rw [Nat.floor_eq_iff (by positivity)]
  constructor <;> push_cast <;> nlinarith

/-- **Step counts** `⌊7.5 / Δt_k⌋ = 900, 1272, 1800, 2545`. [QuennevilleBelair2015], Ch. 7 -/
theorem stepCount_table :
    stepCount 0 = 900 ∧ stepCount 1 = 1272 ∧ stepCount 2 = 1800 ∧ stepCount 3 = 2545 := by
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    rw [pow_succ, s2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [stepCount, div_dt]
  · norm_num
  · rw [pow_one]; exact floor_mesh_one
  · rw [s2]; norm_num
  · rw [s3, show (7.5 : ℝ) * (120 * (2 * Real.sqrt 2)) = 7.5 * (240 * Real.sqrt 2) by ring]
    exact floor_mesh_three

/-- **Final times**: on meshes `k = 1, 3` the final time `N_k Δt_k` falls short of `T = 7.5`
(`T/Δt` is not an integer there); on meshes `k = 0, 2` it is exactly `7.5`. [QuennevilleBelair2015], Ch. 7 -/
theorem finalTime_table :
    (stepCount 0 : ℝ) * dt 0 = 7.5 ∧ (stepCount 1 : ℝ) * dt 1 < 7.5 ∧
    (stepCount 2 : ℝ) * dt 2 = 7.5 ∧ (stepCount 3 : ℝ) * dt 3 < 7.5 := by
  obtain ⟨c0, c1, c2, c3⟩ := stepCount_table
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := by positivity
  rw [c0, c1, c2, c3]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [dt]
  · norm_num
  · rw [pow_one, mul_one_div, div_lt_iff₀ (by positivity)]; push_cast; nlinarith
  · rw [s2]; norm_num
  · rw [pow_succ, s2, mul_one_div, div_lt_iff₀ (by positivity)]; push_cast; nlinarith

/-- **Cell counts** `6 (4·2^k)³` of the structured 6-tetrahedra-per-cube meshes. [QuennevilleBelair2015], Ch. 7 -/
theorem cellCount_table :
    (List.range 4).map (fun k => 6 * (4 * 2 ^ k) ^ 3) = [384, 3072, 24576, 196608] := by
  decide

end Feec.Numerics.CrankNicolson
