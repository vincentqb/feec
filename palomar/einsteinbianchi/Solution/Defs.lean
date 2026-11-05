module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but the compared theorems of
`comparator.json`), compiled against Mathlib alone so that their elaborated values are those of
the challenge. The solution imports this module, the bridge to `Feec` and proves the compared
theorems (`Solution.lean`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §4.2
* [T. Cazenave, A. Haraux, *An Introduction to Semilinear Evolution Equations*][CazenaveHaraux1998],
  Prop 4.1.6

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set

@[expose] public noncomputable section

namespace FEEC.EinsteinBianchi

variable (b : Fin 3 → ℝ) (s : ℝ)

/-! ### Fields on the cube -/

/-- The open cube `C = ∏ᵢ (bᵢ, bᵢ + s)` of `ℝ³`. -/
def cube : Set (Fin 3 → ℝ) := univ.pi fun i => Ioo (b i) (b i + s)

/-- `L²(C; ℂ)`, for the Lebesgue measure restricted to `C`. -/
abbrev L2 := Lp ℂ 2 (volume.restrict (cube b s))

/-- The vector fields `L²(C; ℂ³)`, with components `σ a`. -/
abbrev Vec := PiLp 2 fun _ : Fin 3 => L2 b s

/-- The matrix fields `L²(C; ℂ³ˣ³)`, with entries `E (a, c)`. -/
abbrev Mat := PiLp 2 fun _ : Fin 3 × Fin 3 => L2 b s

/-- The states `(σ, E, B)` of the system. -/
abbrev State := Vec b s × Mat b s × Mat b s

/-- The **test functions vanishing on the faces normal to `e_j`, `j ∈ S`**: `ψ ∈ C¹(ℝ³; ℂ)` with
`ψ = 0` on the closed faces `{x_j = b_j}` and `{x_j = b_j + s}` of the closed cube `C̄` for
`j ∈ S`; no condition is imposed on the other faces. -/
structure IsTest (S : Set (Fin 3)) (ψ : (Fin 3 → ℝ) → ℂ) : Prop where
  contDiff : ContDiff ℝ 1 ψ
  vanish : ∀ j ∈ S, ∀ x ∈ Icc b (b + fun _ => s), (x j = b j ∨ x j = b j + s) → ψ x = 0

/-! ### The operators, with the mirror boundary conditions -/

/-- **`G = grad σ` with `σ · n = 0` on `∂C`**, `G_{ac} = ∂_c σ_a`: for all `a`, `c` and every test
function `ψ` vanishing on the faces normal to `e_j` for the `j` equal to exactly one of `a`, `c`,
`∫_C σ_a ∂_c ψ = -∫_C G_{ac} ψ`. For `c = a` the trace of `ψ` is free on the faces normal to
`e_a`, which imposes `σ_a = 0` there. -/
def IsGrad (σ : Vec b s) (G : Mat b s) : Prop :=
  ∀ a c : Fin 3, ∀ ψ, IsTest b s {j | ¬(j = a ↔ j = c)} ψ →
    ∫ x in cube b s, (σ a : (Fin 3 → ℝ) → ℂ) x * fderiv ℝ ψ x (Pi.single c 1) =
      -∫ x in cube b s, (G (a, c) : (Fin 3 → ℝ) → ℂ) x * ψ x

/-- **`C = curl E` row by row**, `C_{ac} = ∂_{c+1} E_{a,c+2} - ∂_{c+2} E_{a,c+1}` (indices mod 3),
tested against the functions vanishing on the faces normal to `e_j`, `j ∈ S a c`:
`∫_C (E_{a,c+2} ∂_{c+1} ψ - E_{a,c+1} ∂_{c+2} ψ) = -∫_C C_{ac} ψ`. The boundary condition is
carried by `S`: `S a c = {j | j = a ↔ j = c}` imposes `E_{nτ} = 0`,
`S a c = {j | ¬(j = a ↔ j = c)}` imposes `E_{ττ} = 0`. -/
def IsCurl (S : Fin 3 → Fin 3 → Set (Fin 3)) (E C : Mat b s) : Prop :=
  ∀ a c : Fin 3, ∀ ψ, IsTest b s (S a c) ψ →
    (∫ x in cube b s, (E (a, c + 2) : (Fin 3 → ℝ) → ℂ) x * fderiv ℝ ψ x (Pi.single (c + 1) 1)) -
      ∫ x in cube b s, (E (a, c + 1) : (Fin 3 → ℝ) → ℂ) x * fderiv ℝ ψ x (Pi.single (c + 2) 1) =
      -∫ x in cube b s, (C (a, c) : (Fin 3 → ℝ) → ℂ) x * ψ x

/-- **`D = div E` row by row**, `D_a = Σ_c ∂_c E_{ac}`, tested against the functions vanishing on
the faces normal to `e_j`, `j ∈ S a`: `Σ_c ∫_C E_{ac} ∂_c ψ = -∫_C D_a ψ`. The boundary condition
is carried by `S`: `S a = {a}` imposes `E_{τn} = 0`, `S a = {j | j ≠ a}` imposes `E_{nn} = 0`. -/
def IsDiv (S : Fin 3 → Set (Fin 3)) (E : Mat b s) (D : Vec b s) : Prop :=
  ∀ a : Fin 3, ∀ ψ, IsTest b s (S a) ψ →
    ∑ c, ∫ x in cube b s, (E (a, c) : (Fin 3 → ℝ) → ℂ) x * fderiv ℝ ψ x (Pi.single c 1) =
      -∫ x in cube b s, (D a : (Fin 3 → ℝ) → ℂ) x * ψ x

/-- **`V = L U` for the linearized Einstein–Bianchi operator with mirror boundary conditions**,
`L (σ, E, B) = (div E, grad σ - curl B, curl E)`, with `σ · n = 0` (`grad σ`), `E_{nτ} = 0`
(`curl E`), `E_{τn} = 0` (`div E`) and `B_{ττ} = 0` (`curl B`) on `∂C`. The domain `D(L)` is the
set of the `U` with `IsWave U V` for some `V`. -/
def IsWave (U V : State b s) : Prop :=
  ∃ G CE D CB, IsGrad b s U.1 G ∧ IsCurl b s (fun a c => {j | j = a ↔ j = c}) U.2.1 CE ∧
    IsDiv b s (fun a => {a}) U.2.1 D ∧ IsCurl b s (fun a c => {j | ¬(j = a ↔ j = c)}) U.2.2 CB ∧
      V = (D, G - CB, CE)

/-- `E` is **TSD**, with the boundary condition carried by `S` (as in `IsDiv`): symmetric,
trace-free and divergence-free, `Σ_c ∫_C E_{ac} ∂_c ψ = 0` for every test function `ψ` vanishing
on the faces normal to `e_j`, `j ∈ S a`. -/
def IsTSD (S : Fin 3 → Set (Fin 3)) (E : Mat b s) : Prop :=
  (∀ i j, E (i, j) = E (j, i)) ∧ ∑ i, E (i, i) = 0 ∧ IsDiv b s S E 0

/-- **The constraint** `{0} × TSD × TSD`: `σ = 0`, `E` TSD with `E_{τn} = 0` and `B` TSD with
`B_{nn} = 0` on `∂C`. -/
def Constraint (U : State b s) : Prop :=
  U.1 = 0 ∧ IsTSD b s (fun a => {a}) U.2.1 ∧ IsTSD b s (fun a => {j | j ≠ a}) U.2.2

/-! ### Solutions -/

/-- `U` is a **strong solution** of `U' = L U + F` on the time set `I`: `U` is continuous on `I`
and at every `t ∈ I`, `U t ∈ D(L)` and `U' t = L (U t) + F t` (the derivative within `I`). This
asks for the equation at every time, not almost every time as for the strong solutions of
[Pazy1983], §4.2. -/
def IsStrongSolution (I : Set ℝ) (F U : ℝ → State b s) : Prop :=
  ContinuousOn U I ∧ ∀ t ∈ I, ∃ V, IsWave b s (U t) V ∧ HasDerivWithinAt U (V + F t) I t

/-- `U` is a **classical solution** of `U' = L U + F` on `I`: a strong solution with
`t ↦ L (U t)` continuous on `I`; for continuous `F`, `U ∈ C(I; D(L)) ∩ C¹(I; L²)`. -/
def IsClassicalSolution (I : Set ℝ) (F U : ℝ → State b s) : Prop :=
  IsStrongSolution b s I F U ∧
    ∃ V : ℝ → State b s, ContinuousOn V I ∧ ∀ t ∈ I, IsWave b s (U t) (V t)

/-- **Admissible forcing** on `[t₀, t₁]` ([CazenaveHaraux1998], Prop 4.1.6 and Cor 2.4.9): `F` is
continuous on `[t₀, t₁]` and either `F ∈ W^{1,1}(t₀, t₁; L²)`, i.e. `F = x₀ + ∫_{t₀}^· g` a.e. on
`(t₀, t₁)` with `g` integrable, or `F ∈ L¹(t₀, t₁; D(L))`, i.e. `F t ∈ D(L)` for a.e. `t` with
`t ↦ L (F t)` a.e. equal to an integrable function. -/
def IsAdmissible (t₀ t₁ : ℝ) (F : ℝ → State b s) : Prop :=
  ContinuousOn F (Icc t₀ t₁) ∧
    ((∃ (x₀ : State b s) (g : ℝ → State b s), IntegrableOn g (Ioc t₀ t₁) ∧
        F =ᵐ[volume.restrict (Ioo t₀ t₁)] fun t => x₀ + ∫ τ in t₀..t, g τ) ∨
      ∃ H : ℝ → State b s, IntegrableOn H (Ioc t₀ t₁) ∧
        ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)), IsWave b s (F t) (H t))

/-! ### The theorems -/

end FEEC.EinsteinBianchi
