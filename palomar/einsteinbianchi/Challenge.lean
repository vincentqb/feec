module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Which boundary conditions preserve the constraints of the linearized Einstein–Bianchi system

The **linearized Einstein–Bianchi system** ([ACBY1997]; [QuennevilleBelair2015], §3.4, (4.14))
evolves the electric and magnetic parts `E`, `B` of the linearized Weyl curvature of a perturbation
of Minkowski space, two `3 × 3` matrix fields which are symmetric, trace-free and divergence-free
(**TSD**). As in [QuennevilleBelair2015], §4.10, it is written as the Hodge wave equation of a
matrix grad–curl complex `H¹(C; 𝕜³) --grad--> H(curl; C; 𝕜³ˣ³) --curl--> L²(C; 𝕜³ˣ³)`, with an
auxiliary vector field `σ` and a forcing `f = (f_σ, f_E, f_B)`:

    σ' = div E + f_σ,    E' = grad σ - curl B + f_E,    B' = curl E + f_B,

where `(grad σ)_{ab} = ∂_b σ_a`, and `div` and `curl` act row by row:
`(div E)_a = Σ_c ∂_c E_{ac}`, `(curl E)_{ac} = ∂_{c+1} E_{a,c+2} - ∂_{c+2} E_{a,c+1}` (indices
mod 3). The constraint is `σ = 0`, `E` and `B` TSD.

On `ℝ³` and on the torus the constraints propagate. On a domain with boundary they propagate only
under suitable boundary conditions, and constraint-preserving boundary conditions are a central
problem of the initial–boundary value problem of general relativity ([FriedrichNagy1999];
[CPRST2003]; [KreissWinicour2006]). This file answers the question for three boundary conditions
on an open cube `C = ∏ᵢ (bᵢ, bᵢ + s)` of `ℝ³`.

**Mirror conditions: the constraints propagate.** On a face with normal `n` and tangents `τ`,

| field | condition | definition | test functions vanish on the faces normal to `e_j` for |
|---|---|---|---|
| `σ` (`grad σ`) | `σ · n = 0` | `IsGrad` | `j` equal to exactly one of `a`, `c` (entry `(a, c)`) |
| `E` (`curl E`) | `E_{nτ} = 0` | `IsCurl` | `j` equal to both or neither of `a`, `c` |
| `E` (`div E`) | `E_{τn} = 0` | `IsDiv` | `j = a` (row `a`) |
| `B` (`curl B`) | `B_{ττ} = 0` | `IsCurl` | `j` equal to exactly one of `a`, `c` |
| `B` (`div B = 0`) | `B_{nn} = 0` | `IsDiv` | `j ≠ a` (row `a`) |

These are the face conditions of the fields on `ℝ³` symmetric under the reflections in the faces
of `C`, with `σ` a vector, `E` a tensor and `B` a pseudotensor: on each face the components that
are odd under the reflection vanish. Each operator is defined by its Green's formula against the
`C¹` test functions of the last column (`IsTest`), free on the other faces: for test functions
compactly supported in `C` the formula is the weak derivative, and the free traces of the test
functions impose the boundary condition. For every open cube, with complex fields:

1. (`tsd_propagates`) every strong solution on `[t₀, t₁]` with data and forcing in the constraint
   stays in the constraint;
2. (`tsd_existsUnique`) for data in `D(L)` and in the constraint, and admissible forcing in the
   constraint (`IsAdmissible`, [CazenaveHaraux1998], Prop 4.1.6), the system has a classical
   solution on `[t₀, t₁]`, unique among the strong solutions, and it stays in the constraint;
3. (`exists_nonstationary`) the constraint has dynamical content: some datum of `D(L)` in the
   constraint has `L U ≠ 0`.

**Electric conditions: only stationary data propagate.** The conditions `σ = 0` and
`n × Eₐ = 0` (`E_{aτ} = 0`) on `∂C` are those of the minimal realizations
`H̊¹(C) --grad--> H̊(curl; C) --curl--> L²(C)`; their adjoints are the distributional `div` and
`curl`, with no boundary condition (`IsCompactTest`, `IsGrad₀`, `IsCurl₀`, `IsWave₀`), and the
constraint is `σ = 0` with `E`, `B` TSD in the sense of distributions (`IsTSD₀`, `Constraint₀`).
For every open cube, with real fields:

4. (`electric_forward_iff`) for every datum of `D(L)` the system has a strong solution on
   `[0, ∞)`, and for any sets `K₁`, `K₂` of TSD fields (whatever boundary conditions they carry)
   a strong solution stays in `{0} × K₁ × K₂` iff its datum lies there and is stationary;
5. (`electric_tsd_leaves`) some TSD datum of `D(L)` leaves the constraint at once: on every
   `[0, T]` it has a strong solution, and every strong solution from it leaves the constraint.

**Absorbing conditions: the constraints do not propagate.** On `Q = (0, ½)³` (`cube 0 (1/2)`),
for the system `E' = -curl B`, `B' = curl E` in `(E, B)` (the constraint `σ = 0` imposed), the
absorbing (Silver–Müller) condition `n × Eₐ + (Bₐ)_τ = 0` on `∂Q` ([Monk2003], §1.4) sets the
incoming characteristic fields to zero. Its generator `A` is defined by the energy space of the
`L²` fields with an `L²` curl and an `L²` tangential trace (`IsEnergy`, the closure of the `C¹`
fields) and a Green's formula with a boundary term (`IsAbsorbing`); its solutions are mild
solutions (`IsMildSolution`, [Pazy1983], §4.2). With real fields:

6. (`absorbing_not_propagates`) some TSD datum has a mild solution that leaves the TSD
   constraint.

The fields are elements of `L²` for the Lebesgue measure restricted to the domain, over
`𝕜 = ℝ` or `ℂ` (`RCLike 𝕜`); solutions are those of `U' = L U + F` for an operator `L` given by its
graph (`IsStrongSolution`, `IsClassicalSolution`; cf. [Pazy1983], §4.2).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §3.4, §4.10 (Prop 4.17, (4.14)), Ch. 7
* [A. Anderson, Y. Choquet-Bruhat, J. W. York, Jr., *Einstein–Bianchi hyperbolic system for general relativity*][ACBY1997]
* [H. Friedrich, G. Nagy, *The Initial Boundary Value Problem for Einstein's Vacuum Field Equation*][FriedrichNagy1999]
* [G. Calabrese, J. Pullin, O. Reula, O. Sarbach, M. Tiglio, *Well Posed Constraint-Preserving Boundary Conditions for the Linearized Einstein Equations*][CPRST2003]
* [H.-O. Kreiss, J. Winicour, *Problems which are well posed in a generalized sense with applications to the Einstein equations*][KreissWinicour2006]
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003], §1.4
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §4.2
* [T. Cazenave, A. Haraux, *An Introduction to Semilinear Evolution Equations*][CazenaveHaraux1998],
  Prop 4.1.6

Bibliography: [references.bib](../../docs/references.bib)
-/

open MeasureTheory Set
open scoped ContDiff

@[expose] public noncomputable section

namespace FEEC.EinsteinBianchi

/-- The open cube `∏ᵢ (bᵢ, bᵢ + s)` of `ℝⁿ`. -/
def cube {n : ℕ} (b : Fin n → ℝ) (s : ℝ) : Set (Fin n → ℝ) := univ.pi fun i => Ioo (b i) (b i + s)

variable {𝕜 : Type*} [RCLike 𝕜] (b : Fin 3 → ℝ) (s : ℝ)

/-! ### Fields on the cube -/

variable (𝕜) in
/-- `L²(C; 𝕜)`, for the Lebesgue measure restricted to `C = cube b s`. -/
abbrev L2 := Lp 𝕜 2 (volume.restrict (cube b s))

variable (𝕜) in
/-- The vector fields `L²(C; 𝕜³)`, with components `σ a`. -/
abbrev Vec := PiLp 2 fun _ : Fin 3 => L2 𝕜 b s

variable (𝕜) in
/-- The matrix fields `L²(C; 𝕜³ˣ³)`, with entries `E (a, c)`. -/
abbrev Mat := PiLp 2 fun _ : Fin 3 × Fin 3 => L2 𝕜 b s

variable (𝕜) in
/-- The states `(σ, E, B)` of the system. -/
abbrev State := Vec 𝕜 b s × Mat 𝕜 b s × Mat 𝕜 b s

/-- The **test functions vanishing on the faces normal to `e_j`, `j ∈ S`**: `ψ ∈ C¹(ℝ³; 𝕜)` with
`ψ = 0` on the closed faces `{x_j = b_j}` and `{x_j = b_j + s}` of the closed cube `C̄` for
`j ∈ S`; no condition is imposed on the other faces. -/
structure IsTest (S : Set (Fin 3)) (ψ : (Fin 3 → ℝ) → 𝕜) : Prop where
  contDiff : ContDiff ℝ 1 ψ
  vanish : ∀ j ∈ S, ∀ x ∈ Icc b (b + fun _ => s), (x j = b j ∨ x j = b j + s) → ψ x = 0

/-- The **test functions `C_c^∞(C; 𝕜)`**: smooth, compactly supported, with support in `C`. -/
structure IsCompactTest (ψ : (Fin 3 → ℝ) → 𝕜) : Prop where
  contDiff : ContDiff ℝ ∞ ψ
  hasCompactSupport : HasCompactSupport ψ
  tsupport_subset : tsupport ψ ⊆ cube b s

/-! ### Green's formulas -/

/-- **`G = grad σ` with `σ · n = 0` on `∂C`**, `G_{ac} = ∂_c σ_a`: for all `a`, `c` and every test
function `ψ` vanishing on the faces normal to `e_j` for the `j` equal to exactly one of `a`, `c`,
`∫_C σ_a ∂_c ψ = -∫_C G_{ac} ψ`. For `c = a` the trace of `ψ` is free on the faces normal to
`e_a`, which imposes `σ_a = 0` there. -/
def IsGrad (σ : Vec 𝕜 b s) (G : Mat 𝕜 b s) : Prop :=
  ∀ a c : Fin 3, ∀ ψ, IsTest b s {j | ¬(j = a ↔ j = c)} ψ →
    ∫ x in cube b s, (σ a : (Fin 3 → ℝ) → 𝕜) x * fderiv ℝ ψ x (Pi.single c 1) =
      -∫ x in cube b s, (G (a, c) : (Fin 3 → ℝ) → 𝕜) x * ψ x

/-- **`C = curl E` row by row**, `C_{ac} = ∂_{c+1} E_{a,c+2} - ∂_{c+2} E_{a,c+1}` (indices mod 3),
tested against the functions `ψ` of the class `T a c`:
`∫_C (E_{a,c+2} ∂_{c+1} ψ - E_{a,c+1} ∂_{c+2} ψ) = -∫_C C_{ac} ψ`. The boundary condition is
carried by `T`: `IsTest b s {j | j = a ↔ j = c}` imposes `E_{nτ} = 0`,
`IsTest b s {j | ¬(j = a ↔ j = c)}` imposes `E_{ττ} = 0`, and `IsCompactTest b s` imposes none
(the distributional curl). -/
def IsCurl (T : Fin 3 → Fin 3 → ((Fin 3 → ℝ) → 𝕜) → Prop) (E C : Mat 𝕜 b s) : Prop :=
  ∀ a c : Fin 3, ∀ ψ, T a c ψ →
    (∫ x in cube b s, (E (a, c + 2) : (Fin 3 → ℝ) → 𝕜) x * fderiv ℝ ψ x (Pi.single (c + 1) 1)) -
      ∫ x in cube b s, (E (a, c + 1) : (Fin 3 → ℝ) → 𝕜) x * fderiv ℝ ψ x (Pi.single (c + 2) 1) =
      -∫ x in cube b s, (C (a, c) : (Fin 3 → ℝ) → 𝕜) x * ψ x

/-- **`D = div E` row by row**, `D_a = Σ_c ∂_c E_{ac}`, tested against the functions `ψ` of the
class `T a`: `Σ_c ∫_C E_{ac} ∂_c ψ = -∫_C D_a ψ`. The boundary condition is carried by `T`:
`IsTest b s {a}` imposes `E_{τn} = 0`, `IsTest b s {j | j ≠ a}` imposes `E_{nn} = 0`, and
`IsCompactTest b s` imposes none (the distributional divergence). -/
def IsDiv (T : Fin 3 → ((Fin 3 → ℝ) → 𝕜) → Prop) (E : Mat 𝕜 b s) (D : Vec 𝕜 b s) : Prop :=
  ∀ a : Fin 3, ∀ ψ, T a ψ →
    ∑ c, ∫ x in cube b s, (E (a, c) : (Fin 3 → ℝ) → 𝕜) x * fderiv ℝ ψ x (Pi.single c 1) =
      -∫ x in cube b s, (D a : (Fin 3 → ℝ) → 𝕜) x * ψ x

/-- `E` is **TSD**, with the boundary condition carried by `T` (as in `IsDiv`): symmetric,
trace-free and divergence-free, `Σ_c ∫_C E_{ac} ∂_c ψ = 0` for every `ψ` of the class `T a`. -/
def IsTSD (T : Fin 3 → ((Fin 3 → ℝ) → 𝕜) → Prop) (E : Mat 𝕜 b s) : Prop :=
  (∀ i j, E (i, j) = E (j, i)) ∧ ∑ i, E (i, i) = 0 ∧ IsDiv b s T E 0

/-- `E` is **TSD in the sense of distributions** (no boundary condition): symmetric, trace-free and
`div E = 0` tested against `C_c^∞(C)`. -/
def IsTSD₀ (E : Mat 𝕜 b s) : Prop := IsTSD b s (fun _ => IsCompactTest b s) E

/-! ### Mirror boundary conditions -/

/-- **`V = L U` for the linearized Einstein–Bianchi operator with mirror boundary conditions**,
`L (σ, E, B) = (div E, grad σ - curl B, curl E)`, with `σ · n = 0` (`grad σ`), `E_{nτ} = 0`
(`curl E`), `E_{τn} = 0` (`div E`) and `B_{ττ} = 0` (`curl B`) on `∂C`. The domain `D(L)` is the
set of the `U` with `IsWave U V` for some `V`. -/
def IsWave (U V : State 𝕜 b s) : Prop :=
  ∃ G CE D CB, IsGrad b s U.1 G ∧ IsCurl b s (fun a c => IsTest b s {j | j = a ↔ j = c}) U.2.1 CE ∧
    IsDiv b s (fun a => IsTest b s {a}) U.2.1 D ∧
      IsCurl b s (fun a c => IsTest b s {j | ¬(j = a ↔ j = c)}) U.2.2 CB ∧ V = (D, G - CB, CE)

/-- **The constraint with mirror boundary conditions** `{0} × TSD × TSD`: `σ = 0`, `E` TSD with
`E_{τn} = 0` and `B` TSD with `B_{nn} = 0` on `∂C`. -/
def Constraint (U : State 𝕜 b s) : Prop :=
  U.1 = 0 ∧ IsTSD b s (fun a => IsTest b s {a}) U.2.1 ∧
    IsTSD b s (fun a => IsTest b s {j | j ≠ a}) U.2.2

/-! ### Electric boundary conditions -/

/-- **`G = grad σ` with `σ = 0` on `∂C`** (`σ ∈ H̊¹(C; 𝕜³)`): Green's formula with no boundary
term against every `E ∈ H(div; C)`, `Σ_a ∫_C σ_a D_a = -Σ_{a,c} ∫_C G_{ac} E_{ac}` whenever
`D = div E` in the sense of distributions. -/
def IsGrad₀ (σ : Vec 𝕜 b s) (G : Mat 𝕜 b s) : Prop :=
  ∀ E D, IsDiv b s (fun _ => IsCompactTest b s) E D →
    ∑ a, ∫ x in cube b s, (σ a : (Fin 3 → ℝ) → 𝕜) x * (D a : (Fin 3 → ℝ) → 𝕜) x =
      -∑ p, ∫ x in cube b s, (G p : (Fin 3 → ℝ) → 𝕜) x * (E p : (Fin 3 → ℝ) → 𝕜) x

/-- **`C = curl E` with `n × Eₐ = 0` on `∂C`** (`E ∈ H̊(curl; C)` row by row): Green's formula
with no boundary term against every `B ∈ H(curl; C)`, `Σ ∫_C E_p C'_p = Σ ∫_C C_p B_p` whenever
`C' = curl B` in the sense of distributions. -/
def IsCurl₀ (E C : Mat 𝕜 b s) : Prop :=
  ∀ B C', IsCurl b s (fun _ _ => IsCompactTest b s) B C' →
    ∑ p, ∫ x in cube b s, (E p : (Fin 3 → ℝ) → 𝕜) x * (C' p : (Fin 3 → ℝ) → 𝕜) x =
      ∑ p, ∫ x in cube b s, (C p : (Fin 3 → ℝ) → 𝕜) x * (B p : (Fin 3 → ℝ) → 𝕜) x

/-- **`V = L U` with electric boundary conditions**, `L (σ, E, B) = (div E, grad σ - curl B,
curl E)` with `σ = 0` (`grad σ`) and `n × Eₐ = 0` (`curl E`) on `∂C`, and the distributional
`div E` and `curl B`. -/
def IsWave₀ (U V : State 𝕜 b s) : Prop :=
  ∃ G CE D CB, IsGrad₀ b s U.1 G ∧ IsCurl₀ b s U.2.1 CE ∧
    IsDiv b s (fun _ => IsCompactTest b s) U.2.1 D ∧
      IsCurl b s (fun _ _ => IsCompactTest b s) U.2.2 CB ∧ V = (D, G - CB, CE)

/-- **The constraint with no boundary condition** `{0} × TSD × TSD`: `σ = 0`, `E` and `B` TSD in
the sense of distributions. -/
def Constraint₀ (U : State 𝕜 b s) : Prop := U.1 = 0 ∧ IsTSD₀ b s U.2.1 ∧ IsTSD₀ b s U.2.2

/-! ### Absorbing boundary conditions on `Q = (0, ½)³` -/

/-- The faces of `Q = cube 0 (1/2)`: `{x_m = ½}` for `f = (m, true)`, `{x_m = 0}` for
`f = (m, false)`, parametrized by the square `(0, ½)²` (`y ↦ x` with the coordinate `x_m`
inserted). -/
def faceMap (f : Fin 3 × Bool) (y : Fin 2 → ℝ) : Fin 3 → ℝ :=
  Fin.insertNth f.1 (if f.2 then 1 / 2 else 0) y

/-- `L²(∂Q; ℝ³ˣ³_τ)`, the tangential parts of matrix fields on `∂Q`: for each face `f`, row `i`
and tangential slot `j'` (the column `f.1.succAbove j'`, tangential to the face), a function of
`L²((0, ½)²)`. -/
abbrev Bdry := PiLp 2 fun _ : (Fin 3 × Bool) × Fin 3 × Fin 2 =>
  Lp ℝ 2 (volume.restrict (cube (0 : Fin 2 → ℝ) (1 / 2)))

/-- The row-wise curl `(curl Φ)_{ac} = ∂_{c+1} Φ_{a,c+2} - ∂_{c+2} Φ_{a,c+1}` of a matrix field
`Φ` on `ℝ³`. -/
def curlF (Φ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ) (p : Fin 3 × Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ (Φ (p.1, p.2 + 2)) x (Pi.single (p.2 + 1) 1) -
    fderiv ℝ (Φ (p.1, p.2 + 1)) x (Pi.single (p.2 + 2) 1)

/-- **The energy space** (row-wise `H_imp(curl; Q)`): `E ∈ L²(Q; ℝ³ˣ³)` with `curl E = C ∈ L²` and
tangential trace `E_τ = β ∈ L²(∂Q)`, i.e. `(E, C, β)` is a limit of the triples `(Φ, curl Φ, Φ_τ)`
of `C¹` fields: for every `ε > 0` some `Φ` has
`‖E - Φ‖²_{L²(Q)} + ‖C - curl Φ‖²_{L²(Q)} + ‖β - Φ_τ‖²_{L²(∂Q)} < ε`. -/
def IsEnergy (E C : Mat ℝ 0 (1 / 2)) (β : Bdry) : Prop :=
  ∀ ε > 0, ∃ Φ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ, (∀ p, ContDiff ℝ 1 (Φ p)) ∧
    (∑ p, ∫ x in cube 0 (1 / 2), ((E p : (Fin 3 → ℝ) → ℝ) x - Φ p x) ^ 2) +
      (∑ p, ∫ x in cube 0 (1 / 2), ((C p : (Fin 3 → ℝ) → ℝ) x - curlF Φ p x) ^ 2) +
      (∑ q, ∫ y in cube 0 (1 / 2),
        ((β q : (Fin 2 → ℝ) → ℝ) y - Φ (q.2.1, q.1.1.succAbove q.2.2) (faceMap q.1 y)) ^ 2) < ε

/-- **`V = A U` for the absorbing condition** `n × Eₐ + (Bₐ)_τ = 0` on `∂Q`,
`A (E, B) = (-curl B, curl E)`: `E` lies in the energy space with `curl E = V.2` and tangential
trace `β`, and `V.1 = -curl B` in the weak form whose boundary term is `-∫_{∂Q} β · Ψ_τ`: for
every `C¹` field `Ψ`, `∫_Q V.1 : Ψ = -∫_Q B : curl Ψ - ∫_{∂Q} β · Ψ_τ`. -/
def IsAbsorbing (U V : Mat ℝ 0 (1 / 2) × Mat ℝ 0 (1 / 2)) : Prop :=
  ∃ β, IsEnergy U.1 V.2 β ∧ ∀ Ψ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ, (∀ p, ContDiff ℝ 1 (Ψ p)) →
    ∑ p, ∫ x in cube 0 (1 / 2), (V.1 p : (Fin 3 → ℝ) → ℝ) x * Ψ p x =
      -(∑ p, ∫ x in cube 0 (1 / 2), (U.2 p : (Fin 3 → ℝ) → ℝ) x * curlF Ψ p x) -
        ∑ q, ∫ y in cube 0 (1 / 2),
          (β q : (Fin 2 → ℝ) → ℝ) y * Ψ (q.2.1, q.1.1.succAbove q.2.2) (faceMap q.1 y)

/-! ### Solutions -/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `U` is a **strong solution** of `U' = L U + F` on the time set `I`, for an operator `L` given
by its graph (`L U V` for `V = L U`): `U` is continuous on `I` and at every `t ∈ I`, `U t ∈ D(L)`
and `U' t = L (U t) + F t` (the derivative within `I`). This asks for the equation at every time,
not almost every time as for the strong solutions of [Pazy1983], §4.2. -/
def IsStrongSolution (L : X → X → Prop) (I : Set ℝ) (F U : ℝ → X) : Prop :=
  ContinuousOn U I ∧ ∀ t ∈ I, ∃ V, L (U t) V ∧ HasDerivWithinAt U (V + F t) I t

/-- `U` is a **classical solution** of `U' = L U + F` on `I`: a strong solution with
`t ↦ L (U t)` continuous on `I`; for continuous `F`, `U ∈ C(I; D(L)) ∩ C¹(I; X)`. -/
def IsClassicalSolution (L : X → X → Prop) (I : Set ℝ) (F U : ℝ → X) : Prop :=
  IsStrongSolution L I F U ∧ ∃ V : ℝ → X, ContinuousOn V I ∧ ∀ t ∈ I, L (U t) (V t)

/-- `U` is a **mild solution** of `U' = L U` on `[0, ∞)` ([Pazy1983], §4.2): `U` is continuous on
`[0, ∞)` and for every `t ≥ 0`, `∫₀ᵗ U ∈ D(L)` with `L ∫₀ᵗ U = U t - U 0`. -/
def IsMildSolution (L : X → X → Prop) (U : ℝ → X) : Prop :=
  ContinuousOn U (Ici 0) ∧ ∀ t ∈ Ici (0 : ℝ), L (∫ τ in (0 : ℝ)..t, U τ) (U t - U 0)

/-- **Admissible forcing** on `[t₀, t₁]` ([CazenaveHaraux1998], Prop 4.1.6 and Cor 2.4.9): `F` is
continuous on `[t₀, t₁]` and either `F ∈ W^{1,1}(t₀, t₁; X)`, i.e. `F = x₀ + ∫_{t₀}^· g` a.e. on
`(t₀, t₁)` with `g` integrable, or `F ∈ L¹(t₀, t₁; D(L))`, i.e. `F t ∈ D(L)` for a.e. `t` with
`t ↦ L (F t)` a.e. equal to an integrable function. -/
def IsAdmissible (L : X → X → Prop) (t₀ t₁ : ℝ) (F : ℝ → X) : Prop :=
  ContinuousOn F (Icc t₀ t₁) ∧
    ((∃ (x₀ : X) (g : ℝ → X), IntegrableOn g (Ioc t₀ t₁) ∧
        F =ᵐ[volume.restrict (Ioo t₀ t₁)] fun t => x₀ + ∫ τ in t₀..t, g τ) ∨
      ∃ H : ℝ → X, IntegrableOn H (Ioc t₀ t₁) ∧
        ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)), L (F t) (H t))

/-! ### Mirror conditions: the constraints propagate -/

/-- **The TSD constraints propagate on the cube with mirror boundary conditions**
([QuennevilleBelair2015], Prop 4.17): a strong solution of the linearized Einstein–Bianchi system
on `[t₀, t₁]` whose initial value and forcing lie in the constraint stays in the constraint. -/
theorem tsd_propagates (hs : 0 < s) {t₀ t₁ : ℝ} {F U : ℝ → State ℂ b s}
    (hU : IsStrongSolution (IsWave b s) (Icc t₀ t₁) F U) (h0 : Constraint b s (U t₀))
    (hF : ∀ t ∈ Icc t₀ t₁, Constraint b s (F t)) : ∀ t ∈ Icc t₀ t₁, Constraint b s (U t) := by
  sorry

/-- **Well-posedness in the constraint** ([QuennevilleBelair2015], Prop 4.17): for `U₀ ∈ D(L)` in
the constraint and admissible forcing in the constraint, the linearized Einstein–Bianchi system
with mirror boundary conditions has a classical solution on `[t₀, t₁]` with `U t₀ = U₀`, it stays
in the constraint, and every strong solution with the same initial value agrees with it. -/
theorem tsd_existsUnique (hs : 0 < s) {U₀ : State ℂ b s} (hU₀ : ∃ V, IsWave b s U₀ V)
    (hU₀K : Constraint b s U₀) {t₀ t₁ : ℝ} {F : ℝ → State ℂ b s}
    (hF : IsAdmissible (IsWave b s) t₀ t₁ F) (hFK : ∀ t ∈ Icc t₀ t₁, Constraint b s (F t)) :
    ∃ U, U t₀ = U₀ ∧ IsClassicalSolution (IsWave b s) (Icc t₀ t₁) F U ∧
      (∀ t ∈ Icc t₀ t₁, Constraint b s (U t)) ∧
      ∀ V, V t₀ = U₀ → IsStrongSolution (IsWave b s) (Icc t₀ t₁) F V → EqOn V U (Icc t₀ t₁) := by
  sorry

/-- **The constraint has dynamical content**: on every open cube some datum `U₀ ∈ D(L)` in the
constraint has `L U₀ ≠ 0`, so the solution from it is not stationary. -/
theorem exists_nonstationary (hs : 0 < s) :
    ∃ U₀ V : State ℂ b s, IsWave b s U₀ V ∧ Constraint b s U₀ ∧ V ≠ 0 := by
  sorry

/-! ### Electric conditions: only stationary data propagate -/

/-- **With electric boundary conditions only stationary data propagate**: for every
`U₀ ∈ D(L)` the system `U' = L U` has a strong solution on `[0, ∞)` from `U₀`, and for any sets
`K₁`, `K₂` of TSD fields a strong solution from `U₀` stays in `{0} × K₁ × K₂` iff `U₀` lies there
and `L U₀ = 0`. -/
theorem electric_forward_iff (hs : 0 < s) {K₁ K₂ : Set (Mat ℝ b s)}
    (h₁ : ∀ E ∈ K₁, IsTSD₀ b s E) (h₂ : ∀ B ∈ K₂, IsTSD₀ b s B) {U₀ : State ℝ b s}
    (hU₀ : ∃ V, IsWave₀ b s U₀ V) :
    (∃ U, U 0 = U₀ ∧ IsStrongSolution (IsWave₀ b s) (Ici 0) 0 U) ∧
      ∀ U, U 0 = U₀ → IsStrongSolution (IsWave₀ b s) (Ici 0) 0 U →
        ((∀ t ∈ Ici (0 : ℝ), (U t).1 = 0 ∧ (U t).2.1 ∈ K₁ ∧ (U t).2.2 ∈ K₂) ↔
          (U₀.1 = 0 ∧ U₀.2.1 ∈ K₁ ∧ U₀.2.2 ∈ K₂) ∧ IsWave₀ b s U₀ 0) := by
  sorry

/-- **With electric boundary conditions TSD data leave the constraint at once**: some datum
`U₀ ∈ D(L)` in the constraint has, for every `T > 0`, a strong solution on `[0, T]`, and every
strong solution from it on `[0, T]` leaves the constraint. -/
theorem electric_tsd_leaves (hs : 0 < s) :
    ∃ U₀ : State ℝ b s, (∃ V, IsWave₀ b s U₀ V) ∧ Constraint₀ b s U₀ ∧ ∀ T > 0,
      (∃ U, U 0 = U₀ ∧ IsStrongSolution (IsWave₀ b s) (Icc 0 T) 0 U) ∧
      ∀ U, U 0 = U₀ → IsStrongSolution (IsWave₀ b s) (Icc 0 T) 0 U →
        ∃ t ∈ Icc 0 T, ¬Constraint₀ b s (U t) := by
  sorry

/-! ### Absorbing conditions: the constraints do not propagate -/

/-- **The absorbing boundary conditions do not preserve the TSD constraint**: on `Q = (0, ½)³`
some datum `(E₀, B₀)` with `E₀`, `B₀` TSD has a mild solution of `(E, B)' = A (E, B)` that
leaves the TSD constraint. -/
theorem absorbing_not_propagates :
    ∃ U₀ : Mat ℝ 0 (1 / 2) × Mat ℝ 0 (1 / 2), IsTSD₀ 0 (1 / 2) U₀.1 ∧ IsTSD₀ 0 (1 / 2) U₀.2 ∧
      ∃ U, U 0 = U₀ ∧ IsMildSolution IsAbsorbing U ∧
        ∃ t ∈ Ici (0 : ℝ), ¬(IsTSD₀ 0 (1 / 2) (U t).1 ∧ IsTSD₀ 0 (1 / 2) (U t).2) := by
  sorry

end FEEC.EinsteinBianchi
