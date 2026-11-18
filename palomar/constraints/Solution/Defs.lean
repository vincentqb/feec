module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but the theorems
`FEEC.constraint_propagation` and `FEEC.tsd_boundary_conditions`), compiled against Mathlib alone
so that their elaborated values are those of the challenge. The solution imports this module and
the bridges to `Feec`, and proves the theorems (`Solution.lean`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10, §6.1, §6.3
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003], §4.6
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4
* [D. N. Arnold, R. S. Falk, R. Winther, *Mixed finite element methods for linear elasticity with weakly imposed symmetry*][AFW2007]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace Topology ContDiff
open Filter Set LinearPMap MeasureTheory

@[expose] public noncomputable section

universe u

namespace FEEC

/-! ### Differential forms on `ℝⁿ` and the minimal exterior derivative (from `palomar/fem`) -/

-- palomar-shared: forms
/-- The coefficients of a `k`-form on `ℝⁿ`: the `k`-subsets `s = {s₁ < ⋯ < s_k}` of `Fin n`,
`s` indexing `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}` (none unless `0 ≤ k ≤ n`). -/
abbrev FormIdx (n : ℕ) (k : ℤ) : Type := {s : Finset (Fin n) // (s.card : ℤ) = k}
/-- `L²(Ω; Λᵏ)`: an `L²(Ω)` coefficient (Lebesgue measure) for each `dx_s`, an `ℓ²` sum. -/
abbrev L2Form {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : Type :=
  PiLp 2 fun _ : FormIdx n k => Lp ℝ 2 (volume.restrict Ω)
/-- A **form field** on `ℝⁿ`: at each point a coefficient of `dx_s` for every subset `s` of
`Fin n` (a `k`-form when those off the `k`-subsets vanish). -/
abbrev FormField (n : ℕ) : Type := (Fin n → ℝ) → Finset (Fin n) → ℝ
/-- The sign `ε(j, s) = (-1)^{#{l ∈ s | l < j}}` of moving `dx_j` to its place in `dx_s`. -/
def sgn {n : ℕ} {R : Type*} [Ring R] (j : Fin n) (s : Finset (Fin n)) : R :=
  (-1) ^ (s.filter fun l => l < j).card
/-- The partial derivative `∂_j f(x) = Df(x) e_j` (`0` where `f` is not differentiable). -/
def partialDeriv {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single j 1)
/-- The **exterior derivative** of a form field, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`. -/
def extDeriv {n : ℕ} (w : FormField n) : FormField n :=
  fun x s => ∑ j ∈ s, sgn j s * partialDeriv j (fun y => w y (s.erase j)) x
/-- The **codifferential** `(dᵗψ)_s = -Σ_{j ∉ s} ε(j, s) ∂_j ψ_{s ∪ j}`, formal adjoint of `d`. -/
def codiff {n : ℕ} (ψ : FormField n) : FormField n :=
  fun x s => -∑ j ∈ sᶜ, sgn j s * partialDeriv j (fun y => ψ y (insert j s)) x
open scoped ContDiff in
/-- `f` is a **test function** on `Ω`: smooth, with compact support contained in `Ω`. -/
def IsTestFn {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω
/-- The **weak exterior derivative** `d : L²(Ω; Λᵏ) → L²(Ω; Λᵏ⁺¹)`: the adjoint of the closure of
the codifferential on test forms (the span of the pairs `(ψ, dᵗψ)`), so `du = w` iff
`⟪w, ψ⟫ = ⟪u, dᵗψ⟫` for every test form `ψ`; its domain is `HΛᵏ(Ω)` ([AFW2010], §4). -/
def dMax {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Form Ω k →ₗ.[ℝ] L2Form Ω (k + 1) :=
  (Submodule.span ℝ {p : L2Form Ω (k + 1) × L2Form Ω k | ∃ ψ : FormField n,
    (∀ s, IsTestFn Ω fun x => ψ x s) ∧
    (∀ t : FormIdx n (k + 1), ⇑(p.1 t) =ᵐ[volume.restrict Ω] fun x => ψ x t.1) ∧
    ∀ s : FormIdx n k, ⇑(p.2 s) =ᵐ[volume.restrict Ω] fun x => codiff ψ x s.1}
    ).topologicalClosure.toLinearPMap†
/-- The cube `(0, ½)ⁿ`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := univ.pi fun _ => Ioo 0 (1 / 2)
-- palomar-shared-end: forms
-- palomar-shared: dMin
/-- The **minimal exterior derivative** `d̊ : L²(Ω; Λᵏ) → L²(Ω; Λᵏ⁺¹)`, the closure of `d` on test
forms, that is of the span of the pairs `(φ, dφ)`, `φ` a test `k`-form (the closure is a graph:
`d` is closable, its formal adjoint being densely defined); its domain is `H̊Λᵏ(Ω)` (for Lipschitz
`Ω`, the forms of `HΛᵏ(Ω)` with vanishing tangential trace) ([AFW2010], §4). -/
def dMin {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Form Ω k →ₗ.[ℝ] L2Form Ω (k + 1) :=
  (Submodule.span ℝ {p : L2Form Ω k × L2Form Ω (k + 1) | ∃ φ : FormField n,
    (∀ s, IsTestFn Ω fun x => φ x s) ∧
    (∀ s : FormIdx n k, ⇑(p.1 s) =ᵐ[volume.restrict Ω] fun x => φ x s.1) ∧
    ∀ t : FormIdx n (k + 1), ⇑(p.2 t) =ᵐ[volume.restrict Ω] fun x => extDeriv φ x t.1}
    ).topologicalClosure.toLinearPMap
-- palomar-shared-end: dMin

/-! ### Evolutions, invariant cores and reducing subspaces -/

-- palomar-shared: IsStrongSolution
/-- `u` is a **strong solution** of `u' = A u` on `I ⊆ ℝ` for an operator given by its graph, a
relation `A ⊆ X × X` (a `LinearPMap` through its `graph`): `u` is continuous on `I` and at every
`t ∈ I` has, within `I`, a derivative `v` with `(u(t), v) ∈ A` (so `u(t)` lies in `D(A)`). -/
def IsStrongSolution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : SetRel X X)
    (I : Set ℝ) (u : ℝ → X) : Prop :=
  ContinuousOn u I ∧ ∀ t ∈ I, ∃ v, (u t, v) ∈ A ∧ HasDerivWithinAt u v I t
-- palomar-shared-end: IsStrongSolution

/-- `S` is an **evolution** of `u' = A u` on `I` (`I = ℝ`: a group; `I = [0, ∞)`: a semigroup),
for an operator given by its graph, a relation `A ⊆ X × X`: bounded operators `S t` with `S 0 = 1`
such that from every `x ∈ D(A)` the orbit `t ↦ S t x` is a strong solution of `u' = A u` on `I`.
(When strong solutions on intervals are unique and `D(A)` is dense, `S t`, `t ∈ I`, is
determined by `A`.) -/
def IsEvolution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : SetRel X X)
    (I : Set ℝ) (S : ℝ → X →L[ℝ] X) : Prop :=
  (∀ x, S 0 x = x) ∧ ∀ x y, (x, y) ∈ A → IsStrongSolution A I fun t => S t x

/-- The **invariant core** `K* = {x | S t x ∈ K for all t ∈ ℝ}` of a constraint `K ⊆ X` under an
evolution group `S`: the data whose evolution stays in `K` at all times. -/
def invariantCore {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (S : ℝ → X →L[ℝ] X)
    (K : Set X) : Set X :=
  {x | ∀ t, S t x ∈ K}

/-- The closed subspace `K` **reduces** `A`: `P_K D(A) ⊆ D(A)` and `A P_K = P_K A` on `D(A)`
(`P_K` the orthogonal projection; [Kato1995], §III.5.6). -/
def IsReducing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] : Prop :=
  ∀ x : A.domain, ∃ hx : K.starProjection (x : E) ∈ A.domain, A ⟨_, hx⟩ = K.starProjection (A x)

/-! ### The linearized Einstein–Bianchi system (4.14) -/

/-- `L²(Ω; Λᵏ ⊗ ℝⁿ)`: the vectors `v = (v₀, …, v_{n-1})` of `k`-forms of `L²(Ω; Λᵏ)`, an `ℓ²`
sum. -/
abbrev L2Vec {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : Type := PiLp 2 fun _ : Fin n => L2Form Ω k

/-- The operators `Tₐ` acting componentwise on vectors, `(vₐ) ↦ (Tₐ vₐ)`, with domain
`∏ₐ D(Tₐ)`. -/
def vecOp {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (T : Fin n → E →ₗ.[ℝ] F) :
    PiLp 2 (fun _ : Fin n => E) →ₗ.[ℝ] PiLp 2 (fun _ : Fin n => F) where
  domain :=
    { carrier := {v | ∀ a, v a ∈ (T a).domain}
      add_mem' := fun hv hw a => (T a).domain.add_mem (hv a) (hw a)
      zero_mem' := fun a => (T a).domain.zero_mem
      smul_mem' := fun c _ hv a => (T a).domain.smul_mem c (hv a) }
  toFun :=
    { toFun := fun v => WithLp.toLp 2 fun a => T a ⟨(v : PiLp 2 fun _ : Fin n => E) a, v.2 a⟩
      map_add' := fun v w => PiLp.ext fun a => (T a).map_add ⟨_, v.2 a⟩ ⟨_, w.2 a⟩
      map_smul' := fun c v => PiLp.ext fun a => (T a).map_smul c ⟨_, v.2 a⟩ }

/-- **The Hodge wave operator `L (σ, u, ρ) = (d⁰*u, -d⁰σ - d¹*ρ, d¹u)` of `W⁰ → W¹ → W²`**
([QuennevilleBelair2015], (4.5)): `L U = V` iff `σ ∈ D(d⁰)`, `u ∈ D(d¹)`, `⟪V_σ, τ⟫ = ⟪u, d⁰τ⟫`
for all `τ ∈ D(d⁰)`, `⟪V_u, v⟫ = -⟪d⁰σ, v⟫ - ⟪ρ, d¹v⟫` for all `v ∈ D(d¹)`, and `V_ρ = d¹u`. -/
def IsHodgeWave {W0 W1 W2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
    [InnerProductSpace ℝ W2] (d0 : W0 →ₗ.[ℝ] W1) (d1 : W1 →ₗ.[ℝ] W2) (U V : W0 × W1 × W2) :
    Prop :=
  ∃ (σ : d0.domain) (u : d1.domain), (σ : W0) = U.1 ∧ (u : W1) = U.2.1 ∧
    (∀ τ : d0.domain, ⟪V.1, τ⟫_ℝ = ⟪(u : W1), d0 τ⟫_ℝ) ∧
    (∀ v : d1.domain, ⟪V.2.1, v⟫_ℝ = -⟪d0 σ, v⟫_ℝ - ⟪U.2.2, d1 v⟫_ℝ) ∧ V.2.2 = d1 u

/-- **The electric field** `E_{ab} = (uₐ)_{dx_b}` of a vector `1`-form `u` (its rows are the
`uₐ`). -/
def mat1 {Ω : Set (Fin 3 → ℝ)} (u : L2Vec Ω 1) (a b : Fin 3) : Lp ℝ 2 (volume.restrict Ω) :=
  u a ⟨{b}, by simp⟩

/-- **The magnetic field** `B_{ai} = (-1)ⁱ (ρₐ)_{{i}ᶜ}` of a vector `2`-form `ρ` (its rows are
the `⋆ρₐ`, `⋆dxᵢ = (-1)ⁱ dx_{{i}ᶜ}`). -/
def mat2 {Ω : Set (Fin 3 → ℝ)} (ρ : L2Vec Ω 2) (a i : Fin 3) : Lp ℝ 2 (volume.restrict Ω) :=
  (-1 : ℝ) ^ (i : ℕ) • ρ a ⟨Finset.univ.erase i, by simp⟩

/-- A matrix field `E` on `Ω` is **TSD**: symmetric, trace-free and weakly divergence-free in
`Ω`, `Σ_c ∫_Ω E_{ac} ∂_c ψ = 0` for every row `a` and every test function `ψ` (no boundary
condition). -/
def IsTSD {Ω : Set (Fin 3 → ℝ)} (E : Fin 3 → Fin 3 → Lp ℝ 2 (volume.restrict Ω)) : Prop :=
  (∀ a b, E a b = E b a) ∧ ∑ a, E a a = 0 ∧
    ∀ a ψ, IsTestFn Ω ψ → ∑ c, ∫ x in Ω, E a c x * partialDeriv c ψ x = 0

/-- A matrix field `E` on a bounded `Ω` lies in **`L²(TSD₀)`**: it is TSD and its rows are weakly
divergence-free with vanishing normal component on `∂Ω`, `Σ_c ∫_Ω E_{ac} ∂_c φ = 0` for every
row `a` and every `C¹` function `φ` on `ℝ³` (no compact support; for `φ = x_c` this gives
`∫_Ω E_{ac} = 0`: such fields have zero mean). -/
def IsTSD₀ {Ω : Set (Fin 3 → ℝ)} (E : Fin 3 → Fin 3 → Lp ℝ 2 (volume.restrict Ω)) : Prop :=
  IsTSD E ∧ ∀ a (φ : (Fin 3 → ℝ) → ℝ), ContDiff ℝ 1 φ →
    ∑ c, ∫ x in Ω, E a c x * partialDeriv c φ x = 0

/-- **The linearized Einstein–Bianchi system (4.14) with the boundary conditions natural for its
complex** on `Ω ⊆ ℝ³` ([QuennevilleBelair2015], §4.10): the Hodge wave equation `U' = L U`
(`IsHodgeWave`) of `H̊Λ⁰(Ω) ⊗ ℝ³ → H̊Λ¹(Ω) ⊗ ℝ³ → L²Λ²(Ω) ⊗ ℝ³`, the minimal exterior
derivative row by row (in vector proxies `H̊¹(Ω; ℝ³) → H̊(curl, Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)`, the
`grad` and `curl` of the rows), on states `U = (σ, u, ρ)` with electric field `E = mat1 u` and
magnetic field `B = mat2 ρ`: `σ' = -div E`, `E' = -grad σ - curl* B`, `B' = curl E`, with
`σ = 0` and the electric boundary condition `n × E = 0` on `∂Ω`. -/
def gradCurlWave (Ω : Set (Fin 3 → ℝ)) :
    SetRel (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) :=
  {p | IsHodgeWave (vecOp fun _ => dMin Ω 0) (vecOp fun _ => dMin Ω 1) p.1 p.2}

/-- **The constraint** `K = {0} × L²(TSD) × L²(TSD)` of the system (4.14): `σ = 0`, and the
electric and magnetic fields are TSD. -/
def tsdConstraint (Ω : Set (Fin 3 → ℝ)) : Set (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) :=
  {U | U.1 = 0 ∧ IsTSD (mat1 U.2.1) ∧ IsTSD (mat2 U.2.2)}

/-- `v ∈ L²(Ω; Λ¹ ⊗ ℝ³)` is an **eigenfield** of `curl* curl` with frequency `ξ` (the natural
boundary conditions, row by row): `v ∈ D(d¹) = H̊(curl)`, `d¹v ∈ D(d¹*)` and `d¹* d¹ v = ξ² v`
(for `v` also weakly divergence-free, e.g. TSD, `(0, v, 0)` and `(0, 0, d¹v)` then span a plane
invariant under the system (4.14), on which `L² = -ξ²`). -/
def IsEigenfield (Ω : Set (Fin 3 → ℝ)) (ξ : ℝ) (v : L2Vec Ω 1) : Prop :=
  ∃ (h1 : v ∈ (vecOp fun _ => dMin Ω 1).domain)
    (h2 : (vecOp fun _ => dMin Ω 1) ⟨v, h1⟩ ∈ (vecOp fun _ => dMin Ω 1)†.domain),
    (vecOp fun _ => dMin Ω 1)† ⟨_, h2⟩ = (ξ ^ 2) • v

/-- The Euclidean unit ball `{x | x₀² + x₁² + x₂² < 1}` of `ℝ³`. -/
def unitBall : Set (Fin 3 → ℝ) := {x | ∑ i, x i ^ 2 < 1}

/-- The open box `∏ᵢ (aᵢ, aᵢ + ℓᵢ)`. -/
def box (a ℓ : Fin 3 → ℝ) : Set (Fin 3 → ℝ) := univ.pi fun i => Ioo (a i) (a i + ℓ i)

/-! ### The complex with weak symmetry ([QuennevilleBelair2015], Ch. 5–6) -/

/-- **The connecting map** `S v = Σₐ dxₐ ∧ vₐ : L²(Ω; Λᵏ ⊗ ℝⁿ) → L²(Ω; Λᵏ⁺¹)`,
`(S v)_s = Σ_{a ∈ s} ε(a, s) (vₐ)_{s ∖ a}`. On vector proxies, `S` is the identity `S⁰ = I` on
vector `0`-forms (`(S v)_{a} = vₐ`), and on vector `1`-forms `vₐ = Σ_b u_{ab} dx_b`,
`(S v)_{ab} = u_{ab} - u_{ba}`, i.e. `S¹ = 2 vskw` ([QuennevilleBelair2015], §5.3; [AFW2007]). -/
def wedge {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Vec Ω k →L[ℝ] L2Form Ω (k + 1) :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : FormIdx n (k + 1) =>
      Lp ℝ 2 (volume.restrict Ω)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun s => ∑ a : Fin n, if h : a ∈ s.1 then (sgn a s.1 : ℝ) •
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : FormIdx n k => Lp ℝ 2 (volume.restrict Ω))
          ⟨s.1.erase a, by
            rw [Finset.card_erase_of_mem h, Nat.cast_sub (Finset.card_pos.2 ⟨a, h⟩), s.2]
            ring⟩) ∘L PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => L2Form Ω k) a) else 0

/-- **BGG data with weak symmetry**: two segments `W⁰ → W¹ → W²` and `W̃⁰ → W̃¹ → W̃²` of
operators `d`, `d̃` between real Hilbert spaces (unbounded, `LinearPMap`s), with bounded
connecting maps `S⁰ : W̃⁰ → W¹`, `S¹ : W̃¹ → W²`. -/
structure WeakSymmetryData (W0 W1 W2 Wt0 Wt1 Wt2 : Type*) [NormedAddCommGroup W0]
    [InnerProductSpace ℝ W0] [NormedAddCommGroup W1] [InnerProductSpace ℝ W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0]
    [InnerProductSpace ℝ Wt0] [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1]
    [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2] where
  /-- the top row -/
  (d0 : W0 →ₗ.[ℝ] W1) (d1 : W1 →ₗ.[ℝ] W2)
  /-- the bottom row -/
  (dt0 : Wt0 →ₗ.[ℝ] Wt1) (dt1 : Wt1 →ₗ.[ℝ] Wt2)
  /-- the connecting maps -/
  (S0 : Wt0 →L[ℝ] W1) (S1 : Wt1 →L[ℝ] W2)

namespace WeakSymmetryData

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2)

/-- **The Hodge wave operator `L` of the complex with weak symmetry** `Γ → Ṽ¹ → W² × W̃²`,
`Γ = {(σ, φ) ∈ D(d⁰) × D(d̃⁰) | d⁰σ = S⁰φ}`, with the operators `(σ, φ) ↦ d̃φ` and
`u ↦ (S¹u, d̃u)` ([QuennevilleBelair2015], (6.1), (6.2)): `L U = V` for `U = (σ, u, M, ρ)` iff `σ`
lies in `Γ` with some `φ`, `u ∈ D(d̃¹)`, `⟪V_σ, τ⟫ = ⟪u, d̃ψ⟫` for all `(τ, ψ) ∈ Γ`,
`⟪V_u, v⟫ = -⟪d̃φ, v⟫ - ⟪M, S¹v⟫ - ⟪ρ, d̃v⟫` for all `v ∈ D(d̃¹)`, `V_M = S¹u` and `V_ρ = d̃u`. -/
def IsWave (U V : W0 × Wt1 × W2 × Wt2) : Prop :=
  ∃ (σ : D.d0.domain) (φ : D.dt0.domain) (u : D.dt1.domain), (σ : W0) = U.1 ∧
    (u : Wt1) = U.2.1 ∧ D.d0 σ = D.S0 φ ∧
    (∀ (τ : D.d0.domain) (ψ : D.dt0.domain), D.d0 τ = D.S0 ψ →
      ⟪V.1, τ⟫_ℝ = ⟪(u : Wt1), D.dt0 ψ⟫_ℝ) ∧
    (∀ v : D.dt1.domain, ⟪V.2.1, v⟫_ℝ =
      -⟪D.dt0 φ, v⟫_ℝ - ⟪U.2.2.1, D.S1 v⟫_ℝ - ⟪U.2.2.2, D.dt1 v⟫_ℝ) ∧
    V.2.2.1 = D.S1 u ∧ V.2.2.2 = D.dt1 u

end WeakSymmetryData

/-- BGG data on the forms of `Ω ⊆ ℝ³`: the rows `L²Λ⁰ → L²Λ¹ → L²Λ²` and
`L²Λ⁰ ⊗ ℝ³ → L²Λ¹ ⊗ ℝ³ → L²Λ² ⊗ ℝ³`. -/
abbrev FormData (Ω : Set (Fin 3 → ℝ)) : Type :=
  WeakSymmetryData (L2Form Ω 0) (L2Form Ω 1) (L2Form Ω 2) (L2Vec Ω 0) (L2Vec Ω 1) (L2Vec Ω 2)

/-- **The BGG data (4.16) on `Ω ⊆ ℝ³` with the boundary conditions natural for the complex**
([QuennevilleBelair2015], §5.3, §6.3): the top row `H̊Λ⁰(Ω) → H̊Λ¹(Ω) → L²Λ²(Ω)` and,
componentwise, the bottom row `H̊Λ⁰(Ω) ⊗ ℝ³ → H̊Λ¹(Ω) ⊗ ℝ³ → L²Λ²(Ω) ⊗ ℝ³` of the minimal
exterior derivative, with `S⁰ = S¹ = Σₐ dxₐ ∧ ·` (`wedge`). In vector proxies the rows are
`H̊¹ → H̊(curl) → L²(ℝ³)` and `S⁰ = I`, `S¹ = 2 vskw`. -/
def bggData (Ω : Set (Fin 3 → ℝ)) : FormData Ω :=
  ⟨dMin Ω 0, dMin Ω 1, vecOp fun _ => dMin Ω 0, vecOp fun _ => dMin Ω 1, wedge Ω 0, wedge Ω 1⟩

/-- A state `(σ, u, M, ρ)` of the system (6.1) satisfies **the constraint**: `σ = 0`, `M = 0`,
and the electric and magnetic fields are TSD. -/
def IsTSDState {Ω : Set (Fin 3 → ℝ)} (U : L2Form Ω 0 × L2Vec Ω 1 × L2Form Ω 2 × L2Vec Ω 2) :
    Prop :=
  U.1 = 0 ∧ U.2.2.1 = 0 ∧ IsTSD (mat1 U.2.1) ∧ IsTSD (mat2 U.2.2.2)

/-- **The exterior derivative with vanishing tangential traces on the faces normal to `eⱼ`,
`j ∈ J`**, of the cube `(0, ½)ⁿ`: the closure of `dMax` on the forms of its domain vanishing
almost everywhere near the faces `{y_j = 0}`, `{y_j = ½}`, `j ∈ J` (its domain is `H_JΛᵏ`;
`J = ∅` gives `dMax`). -/
def dPart {n : ℕ} (J : Finset (Fin n)) (k : ℤ) :
    L2Form (cube n) k →ₗ.[ℝ] L2Form (cube n) (k + 1) :=
  (Submodule.span ℝ {p : L2Form (cube n) k × L2Form (cube n) (k + 1) |
    ∃ h : p.1 ∈ (dMax (cube n) k).domain, dMax (cube n) k ⟨p.1, h⟩ = p.2 ∧
      ∃ δ > 0, ∀ s, ∀ᵐ y ∂volume.restrict (cube n),
        (∃ j ∈ J, y j < δ ∨ 1 / 2 - δ < y j) → p.1 s y = 0}).topologicalClosure.toLinearPMap

/-- **The BGG data on the cube `Q = (0, ½)³` with mirror boundary conditions**: the top row
`HΛ⁰(Q) → HΛ¹(Q) → L²Λ²(Q)` (no boundary condition) and the bottom row with component `a` in
`H_{a}Λ⁰(Q) → H_{a}Λ¹(Q) → L²Λ²(Q)` (vanishing tangential traces on the faces normal to `eₐ`),
`S = Σₐ dxₐ ∧ ·`. These are the conditions satisfied by fields invariant under the reflections in
the faces with `E` a tensor, `B` a pseudotensor and `M` a pseudovector. -/
def mirrorData : FormData (cube 3) :=
  ⟨dMax (cube 3) 0, dMax (cube 3) 1, vecOp fun a => dPart {a} 0, vecOp fun a => dPart {a} 1,
    wedge (cube 3) 0, wedge (cube 3) 1⟩

/-! ### Absorbing boundary conditions on the cube -/

/-- `L²(Ω; ℝ³ˣ³)`: the matrix fields `E = (E_{ij})` with entries in `L²(Ω)`, an `ℓ²` sum. -/
abbrev L2Mat (Ω : Set (Fin 3 → ℝ)) : Type :=
  PiLp 2 fun _ : Fin 3 × Fin 3 => Lp ℝ 2 (volume.restrict Ω)

/-- The **row-wise curl** of a matrix field on `ℝ³`,
`(curl Φ)_{ik} = ∂_{k+1} Φ_{i,k+2} - ∂_{k+2} Φ_{i,k+1}` (indices mod `3`). -/
def curlMat (Φ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ) (ik : Fin 3 × Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  partialDeriv (ik.2 + 1) (Φ (ik.1, ik.2 + 2)) x - partialDeriv (ik.2 + 2) (Φ (ik.1, ik.2 + 1)) x

/-- The face `{x_m = s}` of the cube `(0, ½)³` (`s = ½` for `true`, `s = 0` for `false`),
parametrized by the square `(0, ½)²`: `y ↦ x` with `x_m = s` and the other coordinates `y`. -/
def faceMap (f : Fin 3 × Bool) (y : Fin 2 → ℝ) : Fin 3 → ℝ :=
  f.1.insertNth (if f.2 then 1 / 2 else 0) y

/-- `L²(∂Q; ℝ³ˣ³_τ)`, the tangential parts of matrix fields on the boundary of the cube
`Q = (0, ½)³`: a function of `L²((0, ½)²)` for every face `f = (m, s)`, row `i` and tangential slot
`j'`, standing for the direction `m.succAbove j'` of the face (surface measure through `faceMap`). -/
abbrev BdryMat : Type :=
  PiLp 2 fun _ : (Fin 3 × Bool) × Fin 3 × Fin 2 => Lp ℝ 2 (volume.restrict (cube 2))

/-- **The energy space** `V ⊆ L²(Q; ℝ³ˣ³) × L²(Q; ℝ³ˣ³) × L²(∂Q; ℝ³ˣ³_τ)` of the absorbing problem
on `Q = (0, ½)³` (the row-wise `H(curl, Q)` with tangential traces in `L²(∂Q)`, [Monk2003], §4.6):
the closure of the triples `(Φ, curl Φ, Φ_τ)` of the `C¹` matrix fields `Φ` on `ℝ³`, `Φ_τ` the
tangential components `Φ_{i, m.succAbove j'}` on the faces `(m, s)`. -/
def energySpace : Submodule ℝ (L2Mat (cube 3) × L2Mat (cube 3) × BdryMat) :=
  (Submodule.span ℝ {v : L2Mat (cube 3) × L2Mat (cube 3) × BdryMat |
    ∃ Φ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ, (∀ ij, ContDiff ℝ 1 (Φ ij)) ∧
    (∀ ij, ⇑(v.1 ij) =ᵐ[volume.restrict (cube 3)] Φ ij) ∧
    (∀ ij, ⇑(v.2.1 ij) =ᵐ[volume.restrict (cube 3)] curlMat Φ ij) ∧
    ∀ b, ⇑(v.2.2 b) =ᵐ[volume.restrict (cube 2)] fun y =>
      Φ (b.2.1, b.1.1.succAbove b.2.2) (faceMap b.1 y)}).topologicalClosure

/-- **The first-order Einstein–Bianchi system `Ė = -curl B`, `Ḃ = curl E` on the cube with the
absorbing (Silver–Müller) boundary condition** `n × Eᵢ + (Bᵢ)_τ = 0` on `∂Q` for every row `i`
([QuennevilleBelair2015], §3.4; [Monk2003], §1.4, §4.6), on states `(E, B)` of matrix fields:
`A (E, B) = (Ė, Ḃ)` iff some `(E, C, β) ∈ V` (so `C = curl E` and `β = E_τ`) has `Ḃ = C` and
`⟪Ė, E'⟫ = -⟪B, C'⟫ - ⟪β, β'⟫` for all `(E', C', β') ∈ V`: `Ė = -curl B` in `Q`, and, by Green's
formula, the boundary condition `n × B = E_τ`. -/
def absorbing : SetRel (WithLp 2 (L2Mat (cube 3) × L2Mat (cube 3)))
    (WithLp 2 (L2Mat (cube 3) × L2Mat (cube 3))) :=
  {p | ∃ v ∈ energySpace, v.1 = p.1.fst ∧ v.2.1 = p.2.snd ∧
    ∀ v' ∈ energySpace, ⟪p.2.fst, v'.1⟫_ℝ = -⟪p.1.snd, v'.2.1⟫_ℝ - ⟪v.2.2, v'.2.2⟫_ℝ}

/-- **The constraint** `L²(TSD) × L²(TSD)` of the first-order system: `E` and `B` TSD. -/
def tsdPair : Set (WithLp 2 (L2Mat (cube 3) × L2Mat (cube 3))) :=
  {x | IsTSD (fun a b => x.fst (a, b)) ∧ IsTSD (fun a b => x.snd (a, b))}

/-! ### The theorems -/

end FEEC
