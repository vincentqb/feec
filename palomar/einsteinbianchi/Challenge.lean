module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Constraint propagation for the linearized Einstein–Bianchi system on a cube

The **linearized Einstein–Bianchi system** ([ACBY1997]; [QuennevilleBelair2015], §3.4, (4.14))
evolves the electric and magnetic parts `E`, `B` of the linearized Weyl curvature of a perturbation
of Minkowski space, two `3 × 3` matrix fields which are symmetric, trace-free and divergence-free
(**TSD**). As in [QuennevilleBelair2015], §4.10, it is written as the Hodge wave equation of the
matrix grad–curl complex `H¹(C; ℂ³) --grad--> H(curl; C; ℂ³ˣ³) --curl--> L²(C; ℂ³ˣ³)`, with an
auxiliary vector field `σ` and a forcing `f = (f_σ, f_E, f_B)`:

    σ' = div E + f_σ,    E' = grad σ - curl B + f_E,    B' = curl E + f_B,

where `(grad σ)_{ab} = ∂_b σ_a`, and `div` and `curl` act row by row:
`(div E)_a = Σ_c ∂_c E_{ac}`, `(curl E)_{ac} = ∂_{c+1} E_{a,c+2} - ∂_{c+2} E_{a,c+1}` (indices
mod 3). The constraint is `σ = 0`, `E` and `B` TSD. (The change of sign `B ↦ -B` gives the
convention `E' = curl B`, `B' = -curl E`.)

The domain is an open cube `C = ∏ᵢ (bᵢ, bᵢ + s)` of `ℝ³` (the unit cube meshed in
[QuennevilleBelair2015], Ch. 7, is `b = 0`, `s = 1`), with the **tensorial mirror boundary
conditions**: on a face with normal `n` and tangents `τ`,

| field | condition | definition | test functions vanish on the faces normal to `e_j` for |
|---|---|---|---|
| `σ` (`grad σ`) | `σ · n = 0` | `IsGrad` | `j` equal to exactly one of `a`, `c` (entry `(a, c)`) |
| `E` (`curl E`) | `E_{nτ} = 0` | `IsCurl` | `j` equal to both or neither of `a`, `c` |
| `E` (`div E`) | `E_{τn} = 0` | `IsDiv` | `j = a` (row `a`) |
| `B` (`curl B`) | `B_{ττ} = 0` | `IsCurl` | `j` equal to exactly one of `a`, `c` |
| `B` (`div B = 0`) | `B_{nn} = 0` | `IsDiv` | `j ≠ a` (row `a`) |

These are the conditions on the faces of the fields on `ℝ³` that are symmetric under the
reflections in the faces of `C`, with `σ` a vector, `E` a tensor and `B` a pseudotensor (`B` is
the curl of a tensor): on each face, the components that are odd under the reflection vanish.

Constraint propagation is a question about the boundary. On `ℝ³` and on the torus the constraints
of the linearized system propagate; on a domain with boundary they propagate only under suitable
boundary conditions, and constraint-preserving boundary conditions are a central problem of the
initial–boundary value problem of general relativity ([FriedrichNagy1999]; [CPRST2003]). The
theorems below give boundary conditions on the cube under which the TSD constraints of this first
order system propagate, with existence and uniqueness of solutions.

Each operator is defined by its Green's formula against the `C¹` test functions of the last column
(`IsTest`), which carry no condition on the other faces: for test functions compactly supported in
`C` the formula is the weak derivative, and the free traces of the test functions on the remaining
faces impose the boundary condition. The operator is `L (σ, E, B) = (div E, grad σ - curl B,
curl E)` (`IsWave`), and the solutions of `U' = L U + F` considered are `IsStrongSolution` and
`IsClassicalSolution` (cf. [Pazy1983], §4.2).

The theorems state, for every open cube:

1. (`FEEC.EinsteinBianchi.tsd_propagates`) every strong solution on `[t₀, t₁]` with data and
   forcing in the constraint stays in the constraint;
2. (`FEEC.EinsteinBianchi.tsd_existsUnique`) for data in `D(L)` and in the constraint, and
   admissible forcing in the constraint (`IsAdmissible`, [CazenaveHaraux1998], Prop 4.1.6), the
   system has a classical solution on `[t₀, t₁]`, unique among the strong solutions, and it stays
   in the constraint ([QuennevilleBelair2015], Prop 4.17 with these boundary conditions);
3. (`FEEC.EinsteinBianchi.exists_nonstationary`) the constraint has dynamical content: some datum
   of `D(L)` in the constraint has `L U ≠ 0`.

The fields are complex-valued.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §3.4, §4.10 (Prop 4.17, (4.14)), Ch. 7
* [A. Anderson, Y. Choquet-Bruhat, J. W. York, Jr., *Einstein–Bianchi hyperbolic system for general relativity*][ACBY1997]
* [H. Friedrich, G. Nagy, *The Initial Boundary Value Problem for Einstein's Vacuum Field Equation*][FriedrichNagy1999]
* [G. Calabrese, J. Pullin, O. Reula, O. Sarbach, M. Tiglio, *Well Posed Constraint-Preserving Boundary Conditions for the Linearized Einstein Equations*][CPRST2003]
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §4.2
* [T. Cazenave, A. Haraux, *An Introduction to Semilinear Evolution Equations*][CazenaveHaraux1998],
  Prop 4.1.6

Bibliography: [references.bib](../../docs/references.bib)
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

/-- **The TSD constraints propagate on the cube with mirror boundary conditions**
([QuennevilleBelair2015], Prop 4.17): a strong solution of the linearized Einstein–Bianchi system
on `[t₀, t₁]` whose initial value and forcing lie in the constraint stays in the constraint. -/
theorem tsd_propagates (hs : 0 < s) {t₀ t₁ : ℝ} {F U : ℝ → State b s}
    (hU : IsStrongSolution b s (Icc t₀ t₁) F U) (h0 : Constraint b s (U t₀))
    (hF : ∀ t ∈ Icc t₀ t₁, Constraint b s (F t)) : ∀ t ∈ Icc t₀ t₁, Constraint b s (U t) := by
  sorry

/-- **Well-posedness in the constraint** ([QuennevilleBelair2015], Prop 4.17): for `U₀ ∈ D(L)` in
the constraint and admissible forcing in the constraint, the linearized Einstein–Bianchi system
with mirror boundary conditions has a classical solution on `[t₀, t₁]` with `U t₀ = U₀`, it stays
in the constraint, and every strong solution with the same initial value agrees with it. -/
theorem tsd_existsUnique (hs : 0 < s) {U₀ : State b s} (hU₀ : ∃ V, IsWave b s U₀ V)
    (hU₀K : Constraint b s U₀) {t₀ t₁ : ℝ} {F : ℝ → State b s} (hF : IsAdmissible b s t₀ t₁ F)
    (hFK : ∀ t ∈ Icc t₀ t₁, Constraint b s (F t)) :
    ∃ U, U t₀ = U₀ ∧ IsClassicalSolution b s (Icc t₀ t₁) F U ∧
      (∀ t ∈ Icc t₀ t₁, Constraint b s (U t)) ∧
      ∀ V, V t₀ = U₀ → IsStrongSolution b s (Icc t₀ t₁) F V → EqOn V U (Icc t₀ t₁) := by
  sorry

/-- **The constraint has dynamical content**: on every open cube some datum `U₀ ∈ D(L)` in the
constraint has `L U₀ ≠ 0`, so the solution from it is not stationary. -/
theorem exists_nonstationary (hs : 0 < s) :
    ∃ U₀ V, IsWave b s U₀ V ∧ Constraint b s U₀ ∧ V ≠ 0 := by
  sorry

end FEEC.EinsteinBianchi
