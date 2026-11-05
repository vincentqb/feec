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
# Constraint propagation for wave equations of Hilbert complexes

A linear evolution `u' = A u` often carries a **constraint**: a closed subspace `K` of the state
space that the solutions should not leave. For the Hodge wave equation `u' = L u`,
`L = d - d*`, of a Hilbert complex the constraints are typically divergence conditions (Gauss's
laws, the TSD conditions of linearized gravity), and whether they propagate depends on the
boundary conditions built into the complex. This file states a general criterion, places it on
Hilbert complexes, and decides it for three boundary conditions of the linearized
Einstein–Bianchi system.

**The criterion.** Let `A` be a skew-adjoint operator on a Hilbert space `H` (`A† = -A`; by
Stone's theorem `A` generates a unitary group), and `K` a closed subspace. Solutions are the mild
solutions (`IsMildSolution`, in integrated form, cf. [Pazy1983], §4.2), which exist and are
unique for every datum (`existsUnique_mild`). Then:

1. (`isReducing_iff_propagates`) every solution starting in `K` stays in `K` for all `t ∈ ℝ`
   (forward and backward; forward invariance alone does not suffice) iff `K` **reduces**
   `A` (`IsReducing`: the orthogonal projection `P_K` maps `D(A)` into `D(A)` and commutes with
   `A` there; [Kato1995], §III.5.6);
2. (`exists_invariantCore`) the set `K*` of data whose solutions stay in `K` for all `t ∈ ℝ` is
   the largest closed subspace of `K` reducing `A`: the constraint propagates exactly on `K*`,
   `A` maps `D(A) ∩ K*` into `K*`, and `D(A) ∩ K*` is dense in `K*`.

For an m-dissipative `A` (`IsMDissipative`, a contraction semigroup by Lumer–Phillips, e.g.
absorbing boundary conditions), solutions on `[0, ∞)` exist and are unique
(`existsUnique_mild_of_isMDissipative`), and `K` reduces `A` iff both `K` and `Kᗮ` propagate
(`isReducing_iff_propagates_of_isMDissipative`).

**Hilbert complexes.** For a Hilbert complex `H` (`HilbertComplex`, closed densely defined
`d` with `d ∘ d = 0`, as in [AFW2010], §3.1) and a window `Wᵃ ⊕ ⋯ ⊕ W^{a+m-1}`:

3. (`HilbertComplex.isSkewAdjoint_wave`) the Hodge wave operator `L = 𝐝 - 𝐝*` is skew-adjoint;
4. (`HilbertComplex.isReducing_wave`) the total space `∏ Sⁱ` of a reducing subcomplex `S`
   (`IsReducingSubcomplex`: closed `Sⁱ ⊆ Wⁱ` with `d P_{Sⁱ} = P_{Sʲ} d` on `D(d)`) reduces `L`,
   so the constraint `∏ Sⁱ` propagates ([QuennevilleBelair2015], Prop 4.16).

**Instances: the linearized Einstein–Bianchi system.** The system ([ACBY1997];
[QuennevilleBelair2015], §3.4, (4.14)) evolves the electric and magnetic parts `E`, `B` of the
linearized Weyl curvature, two `3 × 3` matrix fields that are symmetric, trace-free and
divergence-free (**TSD**). As in [QuennevilleBelair2015], §4.10, it is the Hodge wave equation
of a matrix grad–curl complex `H¹(C; 𝕜³) --grad--> H(curl; C; 𝕜³ˣ³) --curl--> L²(C; 𝕜³ˣ³)`,
with an auxiliary vector field `σ` and a forcing `f = (f_σ, f_E, f_B)`:

    σ' = div E + f_σ,    E' = grad σ - curl B + f_E,    B' = curl E + f_B,

where `(grad σ)_{ab} = ∂_b σ_a`, and `div` and `curl` act row by row:
`(div E)_a = Σ_c ∂_c E_{ac}`, `(curl E)_{ac} = ∂_{c+1} E_{a,c+2} - ∂_{c+2} E_{a,c+1}` (indices
mod 3). The constraint is `σ = 0`, `E` and `B` TSD. Constraint-preserving boundary conditions
are a central problem of the initial–boundary value problem of general relativity
([FriedrichNagy1999]; [CPRST2003]; [KreissWinicour2006]). On an open cube
`C = ∏ᵢ (bᵢ, bᵢ + s)` of `ℝ³` the states `(σ, E, B)` form the Hilbert space
`L²(C; 𝕜³) ⊕ L²(C; 𝕜³ˣ³) ⊕ L²(C; 𝕜³ˣ³)` (`State`, an `ℓ²` sum; `StateQ` for the absorbing
case), `L` is given by Green's formulas and shown skew-adjoint (or m-dissipative), and the
invariant core `K*` of the constraint `K` is decided for three boundary conditions. (That these
`L` are the Hodge wave operators of grad–curl complexes is used in the proof, not stated.)

**Mirror conditions: `K* = K`.** On a face with normal `n` and tangents `τ`,

| field | condition | definition | test functions vanish on the faces normal to `e_j` for |
|---|---|---|---|
| `σ` (`grad σ`) | `σ · n = 0` | `IsGrad` | `j` equal to exactly one of `a`, `c` (entry `(a, c)`) |
| `E` (`curl E`) | `E_{nτ} = 0` | `IsCurl` | `j` equal to both or neither of `a`, `c` |
| `E` (`div E`) | `E_{τn} = 0` | `IsDiv` | `j = a` (row `a`) |
| `B` (`curl B`) | `B_{ττ} = 0` | `IsCurl` | `j` equal to exactly one of `a`, `c` |
| `B` (`div B = 0`) | `B_{nn} = 0` | `IsDiv` | `j ≠ a` (row `a`) |

These are the face conditions of the fields on `ℝ³` symmetric under the reflections in the faces
of `C`, with `σ` a vector, `E` a tensor and `B` a pseudotensor. Each operator is defined by its
Green's formula against the `C¹` test functions of the last column (`IsTest`), free on the other
faces: for test functions compactly supported in `C` the formula is the weak derivative, and the
free traces of the test functions impose the boundary condition. For every open cube, with
complex fields:

5. (`mirror_propagates`) `L` is skew-adjoint and the constraint reduces it (`K* = K`): every
   datum has a unique solution, and every solution starting in the constraint stays in it;
6. (`tsd_propagates`) with forcing in the constraint, every strong solution on `[t₀, t₁]` from
   the constraint stays in it;
7. (`tsd_existsUnique`) for data in `D(L)` and in the constraint, and admissible forcing in the
   constraint (`IsAdmissible`, [CazenaveHaraux1998], Prop 4.1.6, Cor 2.4.9), the system has a classical
   solution on `[t₀, t₁]`, unique among the strong solutions, and it stays in the constraint;
8. (`exists_nonstationary`) the constraint has dynamical content: some datum of `D(L)` in the
   constraint has `L U ≠ 0`.

**Electric (perfect conductor) conditions: `K*` is the stationary data.** The conditions `σ = 0`
and `n × Eₐ = 0` (`E_{aτ} = 0`) on `∂C` are those of the minimal realizations
`H̊¹(C) --grad--> H̊(curl; C) --curl--> L²(C)` (`IsGrad₀`, `IsCurl₀`); their adjoints are the
distributional `div` and `curl`, with no boundary condition (`IsDiv`, `IsCurl` against
`IsCompactTest`); the operator is `IsWave₀`, and the
constraint is `σ = 0` with `E`, `B` TSD in the sense of distributions (`IsTSD₀`,
`Constraint₀`). For every open cube, with real fields:

9. (`electric_propagates_iff`) `L` is skew-adjoint, and a solution stays in the constraint for
   all `t ≥ 0` iff its datum lies in the constraint and is stationary, `L U₀ = 0`; boundary
   conditions on the TSD fields only shrink the constraint, so none of them lets non-stationary
   data propagate;
10. (`electric_tsd_leaves`) some TSD datum of `D(L)` leaves the constraint at once: on every
    `[0, T]` it has a strong solution, and every strong solution from it leaves the constraint.

**Absorbing conditions: `K* ≠ K`.** On `Q = (0, ½)³` (`cube 0 (1/2)`), for the system
`E' = -curl B`, `B' = curl E` in `(E, B)` (the constraint `σ = 0` imposed), the absorbing
(Silver–Müller) condition `n × Eₐ + (Bₐ)_τ = 0` on `∂Q` ([Monk2003], §1.4) sets the incoming
characteristic fields to zero. Its generator `A` is defined by the energy space of the `L²`
fields with an `L²` curl and an `L²` tangential trace (`IsEnergy`, the closure of the `C¹`
fields) and a Green's formula with a boundary term (`IsAbsorbing`). With real fields:

11. (`absorbing_not_propagates`) `A` is m-dissipative, the TSD pairs do not reduce it, and some
    TSD datum has a solution on `[0, ∞)` and every solution from it leaves the TSD constraint.

The fields are elements of `L²` for the Lebesgue measure restricted to the domain, over
`𝕜 = ℝ` or `ℂ` (`RCLike 𝕜`); on the cube the operators are given by their graphs, and solutions
are those of `U' = L U + F` (`IsStrongSolution`, `IsClassicalSolution`, `IsMildSolution`; cf.
[Pazy1983], §4.2).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §3.4, §4.1, §4.4, §4.10 (Thm 4.6, Props 4.16, 4.17, (4.14))
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1
* [A. Anderson, Y. Choquet-Bruhat, J. W. York, Jr., *Einstein–Bianchi hyperbolic system for general relativity*][ACBY1997]
* [H. Friedrich, G. Nagy, *The Initial Boundary Value Problem for Einstein's Vacuum Field Equation*][FriedrichNagy1999]
* [G. Calabrese, J. Pullin, O. Reula, O. Sarbach, M. Tiglio, *Well Posed Constraint-Preserving Boundary Conditions for the Linearized Einstein Equations*][CPRST2003]
* [H.-O. Kreiss, J. Winicour, *Problems which are well posed in a generalized sense with applications to the Einstein equations*][KreissWinicour2006]
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003], §1.4
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.4, §1.10, §4.2
* [T. Cazenave, A. Haraux, *An Introduction to Semilinear Evolution Equations*][CazenaveHaraux1998],
  Prop 4.1.6, Cor 2.4.9

Bibliography: [references.bib](../../docs/references.bib)
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

/-- **Well-posedness** (Stone): for a skew-adjoint `A`, every datum `x` has exactly one mild
solution of `u' = A u` on `ℝ` with `u 0 = x`. -/
theorem existsUnique_mild {A : H →ₗ.[𝕜] H} (hA : IsSkewAdjoint A) (x : H) :
    ∃! u : ℝ → H, u 0 = x ∧ IsMildSolution (fun v w => (v, w) ∈ A.graph) univ u := by
  sorry

/-- **The constraint propagates iff it reduces the generator**: for a skew-adjoint `A` and a
closed subspace `K`, every mild solution of `u' = A u` starting in `K` stays in `K` for all
`t ∈ ℝ` iff `K` reduces `A`. -/
theorem isReducing_iff_propagates {A : H →ₗ.[𝕜] H} (hA : IsSkewAdjoint A) (K : Submodule 𝕜 H)
    [K.HasOrthogonalProjection] :
    IsReducing A K ↔ ∀ u : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) univ u →
      u 0 ∈ K → ∀ t, u t ∈ K := by
  sorry

/-- **The invariant core**: for a skew-adjoint `A` and a closed subspace `K`, the data `x` whose
mild solutions stay in `K` for all `t ∈ ℝ` form a closed subspace `K*` (with an orthogonal
projection) such that `K* ⊆ K`; `K*` reduces `A`, so it propagates and `A` maps `D(A) ∩ K*`
into `K*`; `D(A) ∩ K*` is dense in `K*`; and every closed subspace of `K` reducing `A` lies in
`K*`. -/
theorem exists_invariantCore {A : H →ₗ.[𝕜] H} (hA : IsSkewAdjoint A) (K : Submodule 𝕜 H)
    [K.HasOrthogonalProjection] :
    ∃ (Ks : Submodule 𝕜 H) (_ : Ks.HasOrthogonalProjection),
      (∀ x, x ∈ Ks ↔ ∀ u : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) univ u →
        u 0 = x → ∀ t, u t ∈ K) ∧
      Ks ≤ K ∧ IsReducing A Ks ∧
      (∀ u : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) univ u →
        u 0 ∈ Ks → ∀ t, u t ∈ Ks) ∧
      (∀ x : A.domain, (x : H) ∈ Ks → A x ∈ Ks) ∧
      (Ks : Set H) ⊆ closure ((A.domain : Set H) ∩ Ks) ∧
      ∀ (M : Submodule 𝕜 H) [M.HasOrthogonalProjection], M ≤ K → IsReducing A M → M ≤ Ks := by
  sorry

/-- **Well-posedness** (Lumer–Phillips): for an m-dissipative `A`, every datum `x` has a mild
solution of `u' = A u` on `[0, ∞)` with `u 0 = x`, and two mild solutions with the same datum
agree on `[0, ∞)`. -/
theorem existsUnique_mild_of_isMDissipative {A : H →ₗ.[𝕜] H} (hA : IsMDissipative A) (x : H) :
    (∃ u : ℝ → H, u 0 = x ∧ IsMildSolution (fun v w => (v, w) ∈ A.graph) (Ici 0) u) ∧
      ∀ u v : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) (Ici 0) u →
        IsMildSolution (fun v w => (v, w) ∈ A.graph) (Ici 0) v → u 0 = v 0 → EqOn u v (Ici 0) := by
  sorry

/-- **Reducing subspaces of an m-dissipative operator**: a closed subspace `K` reduces `A` iff
the mild solutions of `u' = A u` on `[0, ∞)` starting in `K` stay in `K` and those starting in
`Kᗮ` stay in `Kᗮ`. -/
theorem isReducing_iff_propagates_of_isMDissipative {A : H →ₗ.[𝕜] H} (hA : IsMDissipative A)
    (K : Submodule 𝕜 H) [K.HasOrthogonalProjection] :
    IsReducing A K ↔
      (∀ u : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) (Ici 0) u →
        u 0 ∈ K → ∀ t ∈ Ici (0 : ℝ), u t ∈ K) ∧
      ∀ u : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) (Ici 0) u →
        u 0 ∈ Kᗮ → ∀ t ∈ Ici (0 : ℝ), u t ∈ Kᗮ := by
  sorry

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

/-- **The Hodge wave operator is skew-adjoint** ([QuennevilleBelair2015], Thm 4.6): for every
Hilbert complex and every window `[a, a + m)`, `L = 𝐝 - 𝐝*` on `Wᵃ ⊕ ⋯ ⊕ W^{a+m-1}` (`𝐝` the
differentials inside the window) has `L† = -L`, with no closed-range hypothesis. So
(`existsUnique_mild`) the Hodge wave equation `u' = L u` has a unique mild solution on `ℝ` from
every datum (with the `ℝ`-structure of `W` by restriction of scalars, e.g. for `𝕜 = ℝ, ℂ`). -/
theorem isSkewAdjoint_wave : IsSkewAdjoint (H.wave a m) := by
  sorry

/-- **The constraint of a reducing subcomplex propagates** ([QuennevilleBelair2015], Prop 4.16):
for a reducing subcomplex `S`, the total space `∏ᵢ S^{a+i}` reduces the wave operator of every
window. So (`isReducing_iff_propagates`, `isSkewAdjoint_wave`) every mild solution of `u' = L u`
starting in `∏ᵢ S^{a+i}` stays in it for all `t ∈ ℝ` (with the `ℝ`-structure by restriction of
scalars). -/
theorem isReducing_wave {S : ∀ i, Submodule 𝕜 (W i)} [∀ i, (S i).HasOrthogonalProjection]
    (hS : H.IsReducingSubcomplex S) :
    ∃ (K : Submodule 𝕜 (Total W a m)) (_ : K.HasOrthogonalProjection),
      (∀ x, x ∈ K ↔ ∀ i : Fin m, x i ∈ S (a + (i : ℕ))) ∧ IsReducing (H.wave a m) K := by
  sorry

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

/-- **With mirror boundary conditions the TSD constraints propagate** ([QuennevilleBelair2015],
Prop 4.17): on every open cube `IsWave` is the graph of a skew-adjoint operator `L` on `State`,
and the constraint is a closed subspace `K` reducing `L`. So (`existsUnique_mild`,
`isReducing_iff_propagates`, `exists_invariantCore`) every datum has a unique mild solution of
`U' = L U` on `ℝ`, every mild solution starting in the constraint stays in it, and `K* = K`. -/
theorem mirror_propagates (hs : 0 < s) :
    ∃ L : State ℂ b s →ₗ.[ℂ] State ℂ b s, (∀ U V, (U, V) ∈ L.graph ↔ IsWave b s U V) ∧
      IsSkewAdjoint L ∧ ∃ (K : Submodule ℂ (State ℂ b s)) (_ : K.HasOrthogonalProjection),
        (∀ U, U ∈ K ↔ Constraint b s U) ∧ IsReducing L K := by
  sorry

/-- **The TSD constraints propagate under forcing** ([QuennevilleBelair2015], Prop 4.17): a strong
solution of the linearized Einstein–Bianchi system with mirror boundary conditions on `[t₀, t₁]`
whose initial value and forcing lie in the constraint stays in the constraint. -/
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

/-! ### Electric conditions: `K*` is the stationary data -/

/-- **With electric boundary conditions only stationary data propagate**: on every open cube
`IsWave₀` is the graph of a skew-adjoint operator `L` on `State` (so, by `existsUnique_mild`,
every datum has a unique mild solution of `U' = L U` on `ℝ`), and a mild solution stays in the
constraint `{0} × TSD × TSD` for all `t ≥ 0` iff its datum lies in the constraint and
`L U₀ = 0`. So `K*` is the stationary data of the constraint. -/
theorem electric_propagates_iff (hs : 0 < s) :
    ∃ L : State ℝ b s →ₗ.[ℝ] State ℝ b s, (∀ U V, (U, V) ∈ L.graph ↔ IsWave₀ b s U V) ∧
      IsSkewAdjoint L ∧ ∀ U : ℝ → State ℝ b s, IsMildSolution (IsWave₀ b s) univ U →
        ((∀ t ∈ Ici (0 : ℝ), Constraint₀ b s (U t)) ↔
          Constraint₀ b s (U 0) ∧ IsWave₀ b s (U 0) 0) := by
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

/-! ### Absorbing conditions: `K* ≠ K` -/

/-- **The absorbing boundary conditions do not preserve the TSD constraint**: on `Q = (0, ½)³`
`IsAbsorbing` is the graph of an m-dissipative operator `A` on `StateQ` (so, by
`existsUnique_mild_of_isMDissipative`, mild solutions on `[0, ∞)` exist and are unique), and
some datum `(E₀, B₀)` with `E₀`, `B₀` TSD has a mild solution of `(E, B)' = A (E, B)` on
`[0, ∞)` and every mild solution from it leaves the TSD constraint; the TSD pairs form a closed
subspace `K` not reducing `A` (`K* ≠ K`). -/
theorem absorbing_not_propagates :
    ∃ A : StateQ →ₗ.[ℝ] StateQ, (∀ U V, (U, V) ∈ A.graph ↔ IsAbsorbing U V) ∧
      IsMDissipative A ∧ (∃ (K : Submodule ℝ StateQ) (_ : K.HasOrthogonalProjection),
        (∀ U, U ∈ K ↔ IsTSD₀ 0 (1 / 2) U.fst ∧ IsTSD₀ 0 (1 / 2) U.snd) ∧ ¬IsReducing A K) ∧
      ∃ U₀ : StateQ, IsTSD₀ 0 (1 / 2) U₀.fst ∧ IsTSD₀ 0 (1 / 2) U₀.snd ∧
        (∃ U, U 0 = U₀ ∧ IsMildSolution IsAbsorbing (Ici 0) U) ∧
        ∀ U, U 0 = U₀ → IsMildSolution IsAbsorbing (Ici 0) U →
          ∃ t ∈ Ici (0 : ℝ), ¬(IsTSD₀ 0 (1 / 2) (U t).fst ∧ IsTSD₀ 0 (1 / 2) (U t).snd) := by
  sorry

end FEEC.ConstraintPropagation
