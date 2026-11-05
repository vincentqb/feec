module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
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
  §4.1, §4.10 (Prop 4.17)
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.4, §1.10, §4.2
* [T. Cazenave, A. Haraux, *An Introduction to Semilinear Evolution Equations*][CazenaveHaraux1998],
  Prop 4.1.6

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

@[expose] public noncomputable section

namespace FEEC.ConstraintPropagation

/-! ### Solutions -/

section Solutions

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

/-- `U` is a **mild solution** of `U' = L U` on the time set `I` (used for the intervals `ℝ` and
`[0, ∞)`, which contain `0`), for an operator `L` given by its graph, in the integrated form
(cf. [Pazy1983], §4.2, where mild solutions are given by the variation-of-constants formula; the
two agree for generators): `U` is continuous on `I` and
for every `t ∈ I`, `∫₀ᵗ U ∈ D(L)` with `L ∫₀ᵗ U = U t - U 0` (for `t < 0`, `∫₀ᵗ = -∫ₜ⁰`). For
the generator of a strongly continuous semigroup or group the mild solutions are its orbits, and
the strong solutions of `U' = L U` on such an interval are mild solutions. -/
def IsMildSolution (L : X → X → Prop) (I : Set ℝ) (U : ℝ → X) : Prop :=
  ContinuousOn U I ∧ ∀ t ∈ I, L (∫ τ in (0 : ℝ)..t, U τ) (U t - U 0)

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

end Solutions

/-! ### The general criterion -/

section Criterion

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- `A : D(A) ⊆ H → H` is **skew-adjoint**: `A† = -A`, with equal domains (Mathlib's adjoint of
a densely defined operator). By Stone's theorem these are the generators of the strongly
continuous unitary groups. -/
def IsSkewAdjoint (A : H →ₗ.[𝕜] H) : Prop := A.adjoint = -A

/-- `A` is **m-dissipative**: `re ⟪A x, x⟫ ≤ 0` on `D(A)`, and `1 - A : D(A) → H` is onto. By
the Lumer–Phillips theorem these are the generators of the strongly continuous contraction
semigroups ([Pazy1983], §1.4). -/
def IsMDissipative (A : H →ₗ.[𝕜] H) : Prop :=
  (∀ x : A.domain, RCLike.re ⟪A x, (x : H)⟫_𝕜 ≤ 0) ∧ ∀ y : H, ∃ x : A.domain, (x : H) - A x = y

/-- The closed subspace `K` **reduces** `A` ([Kato1995], §III.5.6): `P_K D(A) ⊆ D(A)` and
`A P_K = P_K A` on `D(A)`, for the orthogonal projection `P_K` onto `K`. -/
def IsReducing (A : H →ₗ.[𝕜] H) (K : Submodule 𝕜 H) [K.HasOrthogonalProjection] : Prop :=
  ∀ x : A.domain, ∃ hx : K.starProjection (x : H) ∈ A.domain,
    A ⟨_, hx⟩ = K.starProjection (A x)

variable [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

end Criterion

/-! ### Hilbert complexes -/

section Complex

open LinearPMap

/-- A **Hilbert complex** over `𝕜` on `ℤ`: closed densely defined operators `d i j : Wⁱ → Wʲ`,
zero unless `j = i + 1`, with `R(d i j) ⊆ D(d j k)` and `d j k ∘ d i j = 0`. -/
structure HilbertComplex (𝕜 : Type*) [RCLike 𝕜] (W : ℤ → Type*) [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] where
  /-- the differentials -/
  d : ∀ i j, W i →ₗ.[𝕜] W j
  shape : ∀ i j, ¬ i + 1 = j → d i j = 0
  dense : ∀ i j, Dense ((d i j).domain : Set (W i))
  closed : ∀ i j, (d i j).IsClosed
  mapsTo : ∀ i j k (x : (d i j).domain), (d i j x : W j) ∈ (d j k).domain
  d_comp_d : ∀ i j k (x : (d i j).domain), d j k ⟨_, mapsTo i j k x⟩ = 0

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-- The total space `Wᵃ ⊕ ⋯ ⊕ W^{a+m-1}` of a window (an `ℓ²` sum). -/
abbrev Total (W : ℤ → Type*) (a : ℤ) (m : ℕ) : Type _ := PiLp 2 fun i : Fin m => W (a + (i : ℕ))

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W) (a : ℤ) (m : ℕ)

/-- The domain `{x | ∀ i j, xᵢ ∈ D(d (a + i) (a + j))}` of the total differential. -/
def totalDomain : Submodule 𝕜 (Total W a m) where
  carrier := {x | ∀ i j : Fin m, x i ∈ (H.d (a + (i : ℕ)) (a + (j : ℕ))).domain}
  add_mem' hx hy i j := (H.d _ _).domain.add_mem (hx i j) (hy i j)
  zero_mem' _ _ := (H.d _ _).domain.zero_mem
  smul_mem' c _ hx i j := (H.d _ _).domain.smul_mem c (hx i j)

/-- The **total differential** `(𝐝 x)ⱼ = ∑ᵢ d (a + i) (a + j) xᵢ` of the window. -/
def totalD : Total W a m →ₗ.[𝕜] Total W a m where
  domain := H.totalDomain a m
  toFun :=
    { toFun := fun x => WithLp.toLp 2 fun j : Fin m =>
        ∑ i : Fin m, H.d (a + (i : ℕ)) (a + (j : ℕ)) ⟨(x : Total W a m) i, x.2 i j⟩
      map_add' := fun x y => PiLp.ext fun j => by
        rw [PiLp.add_apply, PiLp.toLp_apply, PiLp.toLp_apply, PiLp.toLp_apply,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => (H.d _ _).map_add ⟨_, x.2 i j⟩ ⟨_, y.2 i j⟩
      map_smul' := fun c x => PiLp.ext fun j => by
        rw [PiLp.smul_apply, PiLp.toLp_apply, PiLp.toLp_apply, RingHom.id_apply,
          Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => (H.d _ _).map_smul c ⟨_, x.2 i j⟩ }

/-- The **Hodge–Dirac (wave) operator** `L = 𝐝 - 𝐝*` of the window; `L² = -Δ`. -/
def wave : Total W a m →ₗ.[𝕜] Total W a m := H.totalD a m - (H.totalD a m)†

/-- A **reducing subcomplex** of `H` ([QuennevilleBelair2015], Props 4.16, 4.17): closed subspaces
`Sⁱ ⊆ Wⁱ` (given with their orthogonal projections `P_{Sⁱ}`) reducing every differential:
`P_{Sⁱ} D(d i j) ⊆ D(d i j)` and `d i j P_{Sⁱ} = P_{Sʲ} d i j` on `D(d i j)`. -/
def IsReducingSubcomplex (S : ∀ i, Submodule 𝕜 (W i)) [∀ i, (S i).HasOrthogonalProjection] :
    Prop :=
  ∀ i j (x : (H.d i j).domain), ∃ hx : (S i).starProjection (x : W i) ∈ (H.d i j).domain,
    H.d i j ⟨_, hx⟩ = (S j).starProjection (H.d i j x)

end HilbertComplex

end Complex

/-! ### The linearized Einstein–Bianchi system on a cube -/

/-- The open cube `∏ᵢ (bᵢ, bᵢ + s)` of `ℝⁿ`. -/
def cube {n : ℕ} (b : Fin n → ℝ) (s : ℝ) : Set (Fin n → ℝ) := univ.pi fun i => Ioo (b i) (b i + s)

variable {𝕜 : Type*} [RCLike 𝕜] (b : Fin 3 → ℝ) (s : ℝ)

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
/-- The states `(σ, E, B)` of the system: the Hilbert space `L²(C; 𝕜³) ⊕ L²(C; 𝕜³ˣ³) ⊕
L²(C; 𝕜³ˣ³)` (an `ℓ²` sum), with `U.fst = σ`, `U.snd.fst = E`, `U.snd.snd = B`. -/
abbrev State := WithLp 2 (Vec 𝕜 b s × WithLp 2 (Mat 𝕜 b s × Mat 𝕜 b s))

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
`L (σ, E, B) = (div E, grad σ - curl B, curl E)`, with `E_{τn} = 0` (`div E`), `σ · n = 0`
(`grad σ`), `B_{ττ} = 0` (`curl B`) and `E_{nτ} = 0` (`curl E`) on `∂C`. The domain `D(L)` is
the set of the `U` with `IsWave U V` for some `V`. -/
def IsWave (U V : State 𝕜 b s) : Prop :=
  IsDiv b s (fun a => IsTest b s {a}) U.snd.fst V.fst ∧
    (∃ G CB, IsGrad b s U.fst G ∧
      IsCurl b s (fun a c => IsTest b s {j | ¬(j = a ↔ j = c)}) U.snd.snd CB ∧
        V.snd.fst = G - CB) ∧
    IsCurl b s (fun a c => IsTest b s {j | j = a ↔ j = c}) U.snd.fst V.snd.snd

/-- **The constraint with mirror boundary conditions** `{0} × TSD × TSD`: `σ = 0`, `E` TSD with
`E_{τn} = 0` and `B` TSD with `B_{nn} = 0` on `∂C`. -/
def Constraint (U : State 𝕜 b s) : Prop :=
  U.fst = 0 ∧ IsTSD b s (fun a => IsTest b s {a}) U.snd.fst ∧
    IsTSD b s (fun a => IsTest b s {j | j ≠ a}) U.snd.snd

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
  IsDiv b s (fun _ => IsCompactTest b s) U.snd.fst V.fst ∧
    (∃ G CB, IsGrad₀ b s U.fst G ∧ IsCurl b s (fun _ _ => IsCompactTest b s) U.snd.snd CB ∧
      V.snd.fst = G - CB) ∧
    IsCurl₀ b s U.snd.fst V.snd.snd

/-- **The constraint with no boundary condition** `{0} × TSD × TSD`: `σ = 0`, `E` and `B` TSD in
the sense of distributions. -/
def Constraint₀ (U : State 𝕜 b s) : Prop :=
  U.fst = 0 ∧ IsTSD₀ b s U.snd.fst ∧ IsTSD₀ b s U.snd.snd

/-! ### Absorbing boundary conditions on `Q = (0, ½)³` -/

/-- The states `(E, B)` on `Q = cube 0 (1/2)` with real fields: the Hilbert space
`L²(Q; ℝ³ˣ³) ⊕ L²(Q; ℝ³ˣ³)` (an `ℓ²` sum), with `U.fst = E`, `U.snd = B`. -/
abbrev StateQ := WithLp 2 (Mat ℝ 0 (1 / 2) × Mat ℝ 0 (1 / 2))

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
`A (E, B) = (-curl B, curl E)`: `E` lies in the energy space with `curl E = V.snd` and tangential
trace `β`, and `V.fst = -curl B` in the weak form whose boundary term is `-∫_{∂Q} β · Ψ_τ`: for
every `C¹` field `Ψ`, `∫_Q V.fst : Ψ = -∫_Q B : curl Ψ - ∫_{∂Q} β · Ψ_τ`. -/
def IsAbsorbing (U V : StateQ) : Prop :=
  ∃ β, IsEnergy U.fst V.snd β ∧ ∀ Ψ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ, (∀ p, ContDiff ℝ 1 (Ψ p)) →
    ∑ p, ∫ x in cube 0 (1 / 2), (V.fst p : (Fin 3 → ℝ) → ℝ) x * Ψ p x =
      -(∑ p, ∫ x in cube 0 (1 / 2), (U.snd p : (Fin 3 → ℝ) → ℝ) x * curlF Ψ p x) -
        ∑ q, ∫ y in cube 0 (1 / 2),
          (β q : (Fin 2 → ℝ) → ℝ) y * Ψ (q.2.1, q.1.1.succAbove q.2.2) (faceMap q.1 y)

/-! ### Mirror conditions: `K* = K` -/

/-! ### Electric conditions: `K*` is the stationary data -/

/-! ### Absorbing conditions: `K* ≠ K` -/

end FEEC.ConstraintPropagation
