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
  §4.4, §4.9, §4.10, §6.1, §6.3
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.4, §1.10
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

-- palomar-shared: FormField
/-- A **form field** on `ℝⁿ`: at each point a coefficient of `dx_s` for every subset `s` of
`Fin n` (a `k`-form when those off the `k`-subsets vanish). -/
abbrev FormField (n : ℕ) : Type := (Fin n → ℝ) → Finset (Fin n) → ℝ
/-- The sign `ε(j, s) = (-1)^{#{l ∈ s | l < j}}` of moving `dx_j` to its place in `dx_s`. -/
def sgn {n : ℕ} {R : Type*} [Ring R] (j : Fin n) (s : Finset (Fin n)) : R :=
  (-1) ^ (s.filter fun l => l < j).card
-- palomar-shared-end: FormField
-- palomar-shared: forms
/-- The coefficients of a `k`-form on `ℝⁿ`: the `k`-subsets `s = {s₁ < ⋯ < s_k}` of `Fin n`,
`s` indexing `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}` (none unless `0 ≤ k ≤ n`). -/
abbrev FormIdx (n : ℕ) (k : ℤ) : Type := {s : Finset (Fin n) // (s.card : ℤ) = k}
/-- `L²(Ω; Λᵏ)`: an `L²(Ω)` coefficient (Lebesgue measure) for each `dx_s`, an `ℓ²` sum. -/
abbrev L2Form {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : Type :=
  PiLp 2 fun _ : FormIdx n k => Lp ℝ 2 (volume.restrict Ω)
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

/-- `S` is an **evolution** of `u' = A u` on `I` (`I = ℝ` or `[0, ∞)`), for an operator given by
its graph, a relation `A ⊆ X × X`: bounded `𝕜`-linear operators `S t` (`𝕜 = ℝ` or `ℂ`) with
`S 0 = 1` such that from every `x ∈ D(A)` the orbit `t ↦ S t x` is a strong solution of
`u' = A u` on `I`. No group or semigroup law is assumed: for the generators of
`PropagationCriterion` the evolution is unique (on `I = [0, ∞)`, at `t ≥ 0`), the unitary group or
the contraction semigroup. -/
def IsEvolution (𝕜 : Type*) {X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedSpace ℝ X] (A : SetRel X X) (I : Set ℝ) (S : ℝ → X →L[𝕜] X) : Prop :=
  (∀ x, S 0 x = x) ∧ ∀ x y, (x, y) ∈ A → IsStrongSolution A I fun t => S t x

/-- The **invariant core** `K* = {x | S t x ∈ K for all t ∈ ℝ}` of a constraint `K ⊆ X` under an
evolution `S` on `ℝ`: the data whose evolution stays in `K` at all times. -/
def invariantCore {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (S : ℝ → X →L[𝕜] X) (K : Set X) : Set X :=
  {x | ∀ t, S t x ∈ K}

/-- The closed subspace `K` **reduces** `A`: `P_K D(A) ⊆ D(A)` and `A P_K = P_K A` on `D(A)`
(`P_K` the orthogonal projection; [Kato1995], §III.5.6). -/
def IsReducing {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (A : E →ₗ.[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] : Prop :=
  ∀ x : A.domain, ∃ hx : K.starProjection (x : E) ∈ A.domain, A ⟨_, hx⟩ = K.starProjection (A x)

/-! ### Hilbert complexes and their windows (from `palomar/feec`) -/

-- palomar-shared: HilbertComplex
/-- A **Hilbert complex** over `𝕜` on `ℤ`: closed densely defined operators `d i j : Wⁱ → Wʲ`,
zero unless `j = i + 1`, with `R(d i j) ⊆ D(d j k)` and `d j k ∘ d i j = 0`. -/
structure HilbertComplex (𝕜 : Type*) [RCLike 𝕜] (W : ℤ → Type*) [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] where
  d : ∀ i j, W i →ₗ.[𝕜] W j
  shape : ∀ i j, ¬ i + 1 = j → d i j = 0
  dense : ∀ i j, Dense ((d i j).domain : Set (W i))
  closed : ∀ i j, (d i j).IsClosed
  mapsTo : ∀ i j k (x : (d i j).domain), (d i j x : W j) ∈ (d j k).domain
  d_comp_d : ∀ i j k (x : (d i j).domain), d j k ⟨_, mapsTo i j k x⟩ = 0
-- palomar-shared-end: HilbertComplex
-- palomar-shared: window
/-- The total space `Wᵃ ⊕ ⋯ ⊕ W^{a+m-1}` of the **window** `[a, a + m)` (an `ℓ²` sum). -/
abbrev Total (W : ℤ → Type*) (a : ℤ) (m : ℕ) : Type _ := PiLp 2 fun i : Fin m => W (a + (i : ℕ))
namespace HilbertComplex
variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] (H : HilbertComplex 𝕜 W) (a : ℤ)
  (m : ℕ)
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
end HilbertComplex
-- palomar-shared-end: window
-- palomar-shared: sq
/-- The square `A²` on `D(A²) = {x ∈ D(A) | A x ∈ D(A)}`. -/
def sq {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (A : E →ₗ.[𝕜] E) : E →ₗ.[𝕜] E :=
  A.comp (A.domRestrict ((A.domain.comap A.toFun).map A.domain.subtype)) fun x => by
    obtain ⟨y, hy, hyx⟩ := x.2.1
    exact (congrArg (A · ∈ A.domain) (Subtype.ext hyx.symm : (⟨x, x.2.2⟩ : A.domain) = y)).mpr hy
-- palomar-shared-end: sq

/-! ### The linearized Einstein–Bianchi system (4.14) -/

-- palomar-shared: L2Vec
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
-- palomar-shared-end: L2Vec

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

/-- Closed subspaces `Z⁰ ⊆ W⁰`, `Z¹ ⊆ W¹`, `Z² ⊆ W²` form a **reducing subcomplex** of
`W⁰ → W¹ → W²` ([QuennevilleBelair2015], Prop 4.16): the orthogonal projections preserve the
domains and commute with the operators, `P_{Zⁱ} D(dⁱ) ⊆ D(dⁱ)` and `dⁱ P_{Zⁱ} = P_{Zⁱ⁺¹} dⁱ`. -/
def IsReducingSubcomplex {W0 W1 W2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
    [InnerProductSpace ℝ W2] (d0 : W0 →ₗ.[ℝ] W1) (d1 : W1 →ₗ.[ℝ] W2) (Z0 : Submodule ℝ W0)
    (Z1 : Submodule ℝ W1) (Z2 : Submodule ℝ W2) [Z0.HasOrthogonalProjection]
    [Z1.HasOrthogonalProjection] [Z2.HasOrthogonalProjection] : Prop :=
  (∀ x : d0.domain, ∃ h : Z0.starProjection (x : W0) ∈ d0.domain,
    d0 ⟨_, h⟩ = Z1.starProjection (d0 x)) ∧
  ∀ x : d1.domain, ∃ h : Z1.starProjection (x : W1) ∈ d1.domain,
    d1 ⟨_, h⟩ = Z2.starProjection (d1 x)

-- palomar-shared: IsTSD
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
-- palomar-shared-end: IsTSD

/-- A matrix field `E` on a bounded `Ω` lies in **`L²(TSD₀)`**: it is TSD and its rows are weakly
divergence-free with vanishing normal component on `∂Ω`, `Σ_c ∫_Ω E_{ac} ∂_c φ = 0` for every
row `a` and every `C¹` function `φ` on `ℝ³` (no compact support; for `φ = x_c` this gives
`∫_Ω E_{ac} = 0`: such fields have zero mean). -/
def IsTSD₀ {Ω : Set (Fin 3 → ℝ)} (E : Fin 3 → Fin 3 → Lp ℝ 2 (volume.restrict Ω)) : Prop :=
  IsTSD E ∧ ∀ a (φ : (Fin 3 → ℝ) → ℝ), ContDiff ℝ 1 φ →
    ∑ c, ∫ x in Ω, E a c x * partialDeriv c φ x = 0

/-- A matrix field `E` on `Ω` satisfies **the Gauss law**: its rows are weakly divergence-free
in `Ω`, `Σ_c ∫_Ω E_{ac} ∂_c ψ = 0` for every row `a` and every test function `ψ` (the last
condition of `IsTSD`). -/
def IsDivFree {Ω : Set (Fin 3 → ℝ)} (E : Fin 3 → Fin 3 → Lp ℝ 2 (volume.restrict Ω)) : Prop :=
  ∀ a ψ, IsTestFn Ω ψ → ∑ c, ∫ x in Ω, E a c x * partialDeriv c ψ x = 0

/-- A matrix field `E` on `Ω` is **symmetric and trace-free almost everywhere on `D`**:
`E_{ab}(y) = E_{ba}(y)` and `Σₐ E_{aa}(y) = 0` for almost every `y ∈ D` (for `D ⊆ Ω` this does
not depend on the representatives of the entries; for `D = Ω`, with `IsDivFree`, it is `IsTSD`). -/
def IsSymTFOn {Ω : Set (Fin 3 → ℝ)} (D : Set (Fin 3 → ℝ))
    (E : Fin 3 → Fin 3 → Lp ℝ 2 (volume.restrict Ω)) : Prop :=
  ∀ᵐ y ∂volume.restrict D, (∀ a b, E a b y = E b a y) ∧ ∑ a, E a a y = 0

/-- The **domain of dependence** of `Ω ⊆ ℝ³` at time `t ≥ 0`: the points `y` whose Euclidean
distance to `ℝ³ \ Ω` exceeds `t`, the centres of the Euclidean balls of radii `r > t` contained
in `Ω` (all of `ℝ³` if `Ω = ℝ³`). Its complement `Ω \ depDomain Ω t` in `Ω` is the **boundary
layer** of width `t`, the points that a signal of unit speed from `∂Ω` reaches by time `t`. -/
def depDomain (Ω : Set (Fin 3 → ℝ)) (t : ℝ) : Set (Fin 3 → ℝ) :=
  {y | ∃ r > t, ∀ z, ∑ i, (z i - y i) ^ 2 < r ^ 2 → z ∈ Ω}

/-- **The linearized Einstein–Bianchi system (4.14) with the electric boundary conditions** on
`Ω ⊆ ℝ³` ([QuennevilleBelair2015], §4.10): the Hodge wave equation `U' = L U`
(`IsHodgeWave`) of `H̊Λ⁰(Ω) ⊗ ℝ³ → H̊Λ¹(Ω) ⊗ ℝ³ → L²Λ²(Ω) ⊗ ℝ³`, the minimal exterior
derivative row by row (in vector proxies `H̊¹(Ω; ℝ³) → H̊(curl, Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)`, the
`grad` and `curl` of the rows), on states `U = (σ, u, ρ)` with electric field `E = mat1 u` and
magnetic field `B = mat2 ρ`: `σ' = -div E`, `E' = -grad σ - curl* B`, `B' = curl E`, with
`σ = 0` and the electric boundary condition `n × E = 0` on `∂Ω` (vanishing tangential traces). -/
def gradCurlWave (Ω : Set (Fin 3 → ℝ)) :
    SetRel (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) :=
  {p | IsHodgeWave (vecOp fun _ => dMin Ω 0) (vecOp fun _ => dMin Ω 1) p.1 p.2}

/-- **The constraint** `K = {0} × L²(TSD) × L²(TSD)` of the system (4.14): `σ = 0`, and the
electric and magnetic fields are TSD. -/
def tsdConstraint (Ω : Set (Fin 3 → ℝ)) : Set (L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) :=
  {U | U.1 = 0 ∧ IsTSD (mat1 U.2.1) ∧ IsTSD (mat2 U.2.2)}

/-- `v ∈ L²(Ω; Λ¹ ⊗ ℝ³)` is an **eigenfield** of `curl* curl` with frequency `ξ` (the electric
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

-- palomar-shared: wedge
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
-- palomar-shared-end: wedge

-- palomar-shared: WeakSymmetryData
/-- **BGG data with weak symmetry**: two segments `W⁰ → W¹ → W²` and `W̃⁰ → W̃¹ → W̃²` of
operators `d`, `d̃` between real inner product spaces (unbounded, `LinearPMap`s; densely defined
and closed in the applications, which is not required), with bounded connecting maps
`S⁰ : W̃⁰ → W¹`, `S¹ : W̃¹ → W²`. No law is imposed: the complex and anticommutation laws are
hypotheses where they are used. -/
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
`u ↦ (S¹u, d̃u)` ([QuennevilleBelair2015], (6.1), (6.2)), given by its graph in the sign
convention of (6.2): `L U = V` for `U = (σ, u, M, ρ)` iff `σ` lies in `Γ` with some `φ`,
`u ∈ D(d̃¹)`, `⟪V_σ, τ⟫ = ⟪u, d̃ψ⟫` for all `(τ, ψ) ∈ Γ`,
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
-- palomar-shared-end: WeakSymmetryData

-- palomar-shared: bggData
/-- BGG data on the forms of `Ω ⊆ ℝ³`: the rows `L²Λ⁰ → L²Λ¹ → L²Λ²` and
`L²Λ⁰ ⊗ ℝ³ → L²Λ¹ ⊗ ℝ³ → L²Λ² ⊗ ℝ³`. -/
abbrev FormData (Ω : Set (Fin 3 → ℝ)) : Type :=
  WeakSymmetryData (L2Form Ω 0) (L2Form Ω 1) (L2Form Ω 2) (L2Vec Ω 0) (L2Vec Ω 1) (L2Vec Ω 2)
/-- **The BGG data (4.16) on `Ω ⊆ ℝ³` with the electric boundary conditions**
([QuennevilleBelair2015], §5.3, §6.3), vanishing tangential traces on `∂Ω` in both rows (on the
states, `σ = 0` and `n × E = 0`): the top row `H̊Λ⁰(Ω) → H̊Λ¹(Ω) → L²Λ²(Ω)` and, componentwise,
the bottom row `H̊Λ⁰(Ω) ⊗ ℝ³ → H̊Λ¹(Ω) ⊗ ℝ³ → L²Λ²(Ω) ⊗ ℝ³` of the minimal exterior derivative,
with `S⁰ = S¹ = Σₐ dxₐ ∧ ·` (`wedge`). In vector proxies the rows are `H̊¹ → H̊(curl) → L²(ℝ³)`
and `S⁰ = I`, `S¹ = 2 vskw`. -/
def bggData (Ω : Set (Fin 3 → ℝ)) : FormData Ω :=
  ⟨dMin Ω 0, dMin Ω 1, vecOp fun _ => dMin Ω 0, vecOp fun _ => dMin Ω 1, wedge Ω 0, wedge Ω 1⟩
-- palomar-shared-end: bggData

-- palomar-shared: IsTSDState
/-- A state `(σ, u, M, ρ)` of the system (6.1) satisfies **the constraint**: `σ = 0`, `M = 0`,
and the electric and magnetic fields are TSD. -/
def IsTSDState {Ω : Set (Fin 3 → ℝ)} (U : L2Form Ω 0 × L2Vec Ω 1 × L2Form Ω 2 × L2Vec Ω 2) :
    Prop :=
  U.1 = 0 ∧ U.2.2.1 = 0 ∧ IsTSD (mat1 U.2.1) ∧ IsTSD (mat2 U.2.2.2)
-- palomar-shared-end: IsTSDState

-- palomar-shared: mirrorData
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
-- palomar-shared-end: mirrorData

/-- **The linearized Einstein–Bianchi system (4.14) on the cube `Q = (0, ½)³` with the mirror
boundary conditions**: the Hodge wave equation `U' = L U` (`IsHodgeWave`) of the bottom row of
`mirrorData`, `H_{a}Λ⁰(Q) → H_{a}Λ¹(Q) → L²Λ²(Q)` in the component `a` (`dPart`), on states
`U = (σ, u, ρ)` with electric field `E = mat1 u` and magnetic field `B = mat2 ρ`:
`σ' = -div E`, `E' = -grad σ - curl* B`, `B' = curl E`, with `σ · n = 0` and `E_{nτ} = 0` on
`∂Q` (the conditions satisfied by `σ` and `E` invariant under the reflections in the faces, `σ` a
vector and `E` a tensor). -/
def gradCurlMirror :
    SetRel (L2Vec (cube 3) 0 × L2Vec (cube 3) 1 × L2Vec (cube 3) 2)
      (L2Vec (cube 3) 0 × L2Vec (cube 3) 1 × L2Vec (cube 3) 2) :=
  {p | IsHodgeWave (vecOp fun a => dPart {a} 0) (vecOp fun a => dPart {a} 1) p.1 p.2}

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


/-! ### The criterion -/

/-- **Constraint propagation is reduction** ([Kato1995], §III.5.6; [Pazy1983], §1.4, §1.10;
[QuennevilleBelair2015], Thm 4.6, Prop 4.16), over `𝕜 = ℝ` or `ℂ`; the real structure of a space,
for the derivatives in time, is any one (it is the restriction of scalars). -/
structure PropagationCriterion : Prop where
  /-- (**groups**) A densely defined skew-adjoint `L` (`L* = -L`) has a unique evolution `S` on
  `ℝ`, a group of isometries (Stone's theorem: a unitary group), and every strong solution on
  `[0, T]` from `x ∈ D(L)` is its orbit. A closed subspace `K` reduces `L` iff `S t K ⊆ K` for all
  `t ∈ ℝ`, iff `S t`, `t ≥ 0`, keeps `K` and `Kᗮ`; and the invariant core `K*` is a closed
  subspace reducing `L` that contains every closed subspace of `K` reducing `L`: `K*` is the
  largest of them. -/
  group {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E] (L : E →ₗ.[𝕜] E) (hL : Dense (L.domain : Set E))
    (hskew : L† = -L) :
    ∃ S, IsEvolution 𝕜 L.graph univ S ∧ (∀ S', IsEvolution 𝕜 L.graph univ S' → S' = S) ∧
      (∀ s t, S (s + t) = S s ∘L S t) ∧ (∀ t x, ‖S t x‖ = ‖x‖) ∧
      (∀ x ∈ L.domain, ∀ T (u : ℝ → E), u 0 = x → IsStrongSolution L.graph (Icc 0 T) u →
        EqOn u (fun t => S t x) (Icc 0 T)) ∧
      ∀ (K : Submodule 𝕜 E) [K.HasOrthogonalProjection],
        (IsReducing L K ↔ ∀ t, ∀ x ∈ K, S t x ∈ K) ∧
        (IsReducing L K ↔ (∀ t, 0 ≤ t → ∀ x ∈ K, S t x ∈ K) ∧
          ∀ t, 0 ≤ t → ∀ x ∈ Kᗮ, S t x ∈ Kᗮ) ∧
        ∃ (Ks : Submodule 𝕜 E) (_ : Ks.HasOrthogonalProjection),
          (Ks : Set E) = invariantCore S K ∧ IsReducing L Ks ∧
          ∀ (M : Submodule 𝕜 E) [M.HasOrthogonalProjection], M ≤ K → IsReducing L M → M ≤ Ks
  /-- (**semigroups**) An m-dissipative `A` (`re ⟪A x, x⟫ ≤ 0`, `1 - A` onto) has an evolution
  `S` on `[0, ∞)`, unique at `t ≥ 0`, a semigroup of contractions (Lumer–Phillips), and every
  strong solution on `[0, T]` from `x ∈ D(A)` is its orbit; a closed subspace `K` reduces `A` iff
  `S t`, `t ≥ 0`, keeps `K` and `Kᗮ`. -/
  semigroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E] (A : E →ₗ.[𝕜] E)
    (hdiss : ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ 0)
    (hsurj : ∀ y, ∃ x : A.domain, (x : E) - A x = y) :
    ∃ S, IsEvolution 𝕜 A.graph (Ici 0) S ∧
      (∀ S', IsEvolution 𝕜 A.graph (Ici 0) S' → ∀ t, 0 ≤ t → S' t = S t) ∧
      (∀ s t, 0 ≤ s → 0 ≤ t → S (s + t) = S s ∘L S t) ∧ (∀ t, 0 ≤ t → ∀ x, ‖S t x‖ ≤ ‖x‖) ∧
      (∀ x ∈ A.domain, ∀ T (u : ℝ → E), u 0 = x → IsStrongSolution A.graph (Icc 0 T) u →
        EqOn u (fun t => S t x) (Icc 0 T)) ∧
      ∀ (K : Submodule 𝕜 E) [K.HasOrthogonalProjection],
        IsReducing A K ↔ (∀ t, 0 ≤ t → ∀ x ∈ K, S t x ∈ K) ∧
          ∀ t, 0 ≤ t → ∀ x ∈ Kᗮ, S t x ∈ Kᗮ
  /-- (**windows of Hilbert complexes**) On every window `[a, a + m)` of a Hilbert complex the
  Hodge wave operator `L = 𝐝 - 𝐝*` is densely defined and skew-adjoint, so `group` applies to it,
  and the heat operator `L² = -Δ` is m-dissipative, so `semigroup` applies to it; and the product
  of a reducing subcomplex, closed `Zⁱ` with `P_{Zⁱ} D(d i j) ⊆ D(d i j)` and
  `d i j P_{Zⁱ} = P_{Zʲ} d i j`, is kept by every evolution of `L`. -/
  window {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] [∀ i, NormedSpace ℝ (W i)]
    (H : HilbertComplex 𝕜 W) (a : ℤ) (m : ℕ) :
    Dense ((H.wave a m).domain : Set (Total W a m)) ∧ (H.wave a m)† = -H.wave a m ∧
      (∀ x : (sq (H.wave a m)).domain,
        RCLike.re ⟪sq (H.wave a m) x, (x : Total W a m)⟫_𝕜 ≤ 0) ∧
      (∀ y, ∃ x : (sq (H.wave a m)).domain, (x : Total W a m) - sq (H.wave a m) x = y) ∧
      ∀ (Z : ∀ i, Submodule 𝕜 (W i)) [∀ i, (Z i).HasOrthogonalProjection],
        (∀ i j (x : (H.d i j).domain), ∃ hx : (Z i).starProjection (x : W i) ∈ (H.d i j).domain,
          H.d i j ⟨_, hx⟩ = (Z j).starProjection (H.d i j x)) →
        ∀ S, IsEvolution 𝕜 (H.wave a m).graph univ S → ∀ t (x : Total W a m),
          (∀ i : Fin m, x i ∈ Z (a + (i : ℕ))) → ∀ i : Fin m, S t x i ∈ Z (a + (i : ℕ))
  /-- (**short complexes, in the relation form of the systems below**) For a real short Hilbert
  complex `W⁰ → W¹ → W²` of closed densely defined `d⁰`, `d¹` (`d¹ d⁰ = 0`) and a reducing
  subcomplex `Z⁰ × Z¹ × Z²` (`IsReducingSubcomplex`), every strong solution of the Hodge wave
  equation (`IsHodgeWave`) on `[0, T]` starting in `Z⁰ × Z¹ × Z²` stays in it. -/
  shortComplex {W0 W1 W2 : Type u} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
    [CompleteSpace W0] [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    (d0 : W0 →ₗ.[ℝ] W1) (d1 : W1 →ₗ.[ℝ] W2) (hd0 : Dense (d0.domain : Set W0))
    (hd1 : Dense (d1.domain : Set W1)) (hc0 : d0.IsClosed) (hc1 : d1.IsClosed)
    (hcomp : ∀ x : d0.domain, ∃ h : d0 x ∈ d1.domain, d1 ⟨_, h⟩ = 0)
    (Z0 : Submodule ℝ W0) (Z1 : Submodule ℝ W1) (Z2 : Submodule ℝ W2)
    [Z0.HasOrthogonalProjection] [Z1.HasOrthogonalProjection] [Z2.HasOrthogonalProjection]
    (hZ : IsReducingSubcomplex d0 d1 Z0 Z1 Z2) (T : ℝ) (U : ℝ → W0 × W1 × W2)
    (hU : IsStrongSolution {p | IsHodgeWave d0 d1 p.1 p.2} (Icc 0 T) U)
    (h0 : (U 0).1 ∈ Z0) (h1 : (U 0).2.1 ∈ Z1) (h2 : (U 0).2.2 ∈ Z2) :
    ∀ t ∈ Icc 0 T, (U t).1 ∈ Z0 ∧ (U t).2.1 ∈ Z1 ∧ (U t).2.2 ∈ Z2

/-! ### The verdicts -/

/-- **The verdict of the electric boundary conditions on `Ω ⊆ ℝ³`** ([QuennevilleBelair2015],
§4.10, Prop 4.17; §6.1, §6.3) for the system (4.14) (`gradCurlWave`, constraint `tsdConstraint`)
and the system (6.1) with weak symmetry (`bggData`, constraint `IsTSDState`);
`TSDVerdict.electric` asserts it on every nonempty bounded open `Ω`, with no regularity of
`∂Ω`. The clauses `beta`, `projection_electric`, `projection_magnetic` and `not_dense` state
their conclusions also for every boundary condition containing `n × E = 0`. -/
structure ElectricVerdict (Ω : Set (Fin 3 → ℝ)) : Prop where
  /-- the complex `H̊Λ⁰(Ω)³ → H̊Λ¹(Ω)³ → L²Λ²(Ω)³` of (4.14) is a short Hilbert complex: densely
  defined closed operators with `d¹ d⁰ = 0` -/
  complex :
    Dense ((vecOp fun _ => dMin Ω 0 : L2Vec Ω 0 →ₗ.[ℝ] L2Vec Ω 1).domain : Set (L2Vec Ω 0)) ∧
      Dense ((vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain : Set (L2Vec Ω 1)) ∧
      (vecOp fun _ => dMin Ω 0 : L2Vec Ω 0 →ₗ.[ℝ] L2Vec Ω 1).IsClosed ∧
      (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).IsClosed ∧
      ∀ x : (vecOp fun _ => dMin Ω 0 : L2Vec Ω 0 →ₗ.[ℝ] L2Vec Ω 1).domain,
        ∃ h : (vecOp fun _ => dMin Ω 0) x ∈ (vecOp fun _ => dMin Ω 1 :
          L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain, (vecOp fun _ => dMin Ω 1) ⟨_, h⟩ = 0
  /-- the system (4.14) has an evolution -/
  evolution : ∃ S, IsEvolution ℝ (gradCurlWave Ω) univ S
  /-- for every evolution, `K* = {0} × S₁* × S₂*` is the largest reducing subcomplex of the
  complex in `K` (so `PropagationCriterion.shortComplex` applies to it); its electric part lies in
  `L²(TSD₀)` (vanishing normal trace, zero mean); both parts are strictly smaller than `L²(TSD)`;
  and `S₂*` contains nonzero stationary data -/
  core (S : ℝ → _ →L[ℝ] _) (hS : IsEvolution ℝ (gradCurlWave Ω) univ S) :
    ∃ (S₁ : Submodule ℝ (L2Vec Ω 1)) (S₂ : Submodule ℝ (L2Vec Ω 2))
      (_ : S₁.HasOrthogonalProjection) (_ : S₂.HasOrthogonalProjection),
      invariantCore S (tsdConstraint Ω) = {U | U.1 = 0 ∧ U.2.1 ∈ S₁ ∧ U.2.2 ∈ S₂} ∧
      IsReducingSubcomplex (vecOp fun _ => dMin Ω 0) (vecOp fun _ => dMin Ω 1) ⊥ S₁ S₂ ∧
      (∀ (S₁' : Submodule ℝ (L2Vec Ω 1)) (S₂' : Submodule ℝ (L2Vec Ω 2))
        [S₁'.HasOrthogonalProjection] [S₂'.HasOrthogonalProjection],
        (∀ u ∈ S₁', IsTSD (mat1 u)) → (∀ ρ ∈ S₂', IsTSD (mat2 ρ)) →
        IsReducingSubcomplex (vecOp fun _ => dMin Ω 0) (vecOp fun _ => dMin Ω 1) ⊥ S₁' S₂' →
        S₁' ≤ S₁ ∧ S₂' ≤ S₂) ∧
      (∀ u ∈ S₁, IsTSD₀ (mat1 u)) ∧ (∀ ρ ∈ S₂, IsTSD (mat2 ρ)) ∧
      (∃ u, IsTSD (mat1 u) ∧ u ∉ S₁) ∧ (∃ ρ, IsTSD (mat2 ρ) ∧ ρ ∉ S₂) ∧
      ∃ ρ ∈ S₂, ρ ≠ 0 ∧ ((0, 0, ρ), 0) ∈ gradCurlWave Ω
  /-- the magnetic datum `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)` is TSD; and for every boundary condition
  containing `n × E = 0`, that is for every short Hilbert complex `W⁰ → L²Λ¹(Ω)³ → L²Λ²(Ω)³`
  whose `d¹` is a restriction of the minimal curl (that of (4.14) among them, `W⁰` and `d⁰`
  arbitrary), `(0, 0, β) ∈ D(L)`, and every strong solution of its Hodge wave equation on
  `[0, T]`, `T > 0`, from any `(0, E₀, β)` has a non-TSD electric field at some `t ∈ [0, T]` -/
  beta : ∃ ρ : L2Vec Ω 2, (∀ a b, ⇑(mat2 ρ a b) =ᵐ[volume.restrict Ω]
      fun x => if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then x 2 else 0) ∧
    (0, 0, ρ) ∈ tsdConstraint Ω ∧
    ∀ (W0 : Type) [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
      (d0 : W0 →ₗ.[ℝ] L2Vec Ω 1) (d1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2),
      Dense (d0.domain : Set W0) → Dense (d1.domain : Set (L2Vec Ω 1)) → d0.IsClosed →
      d1.IsClosed → (∀ x : d0.domain, ∃ h : d0 x ∈ d1.domain, d1 ⟨_, h⟩ = 0) →
      d1 ≤ vecOp (fun _ => dMin Ω 1) → (∃ V, IsHodgeWave d0 d1 (0, 0, ρ) V) ∧
        ∀ u T (U : ℝ → W0 × L2Vec Ω 1 × L2Vec Ω 2), 0 < T → U 0 = (0, u, ρ) →
          IsStrongSolution {p | IsHodgeWave d0 d1 p.1 p.2} (Icc 0 T) U →
          ∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (U t).2.1)
  /-- `K` does not reduce `L`, already because `P_K D(L) ⊄ D(L)` in the electric slot: the
  orthogonal projection onto `L²(TSD)` of some field with test-function entries (so
  `(0, u, 0) ∈ D(L)`) leaves `H̊(curl)`; and for every boundary condition containing `n × E = 0`,
  that is for every short Hilbert complex `W⁰ → L²Λ¹(Ω)³ → L²Λ²(Ω)³` whose `d¹` is a
  restriction of the minimal curl, the orthogonal projection onto `L²(TSD)` of some `u` with
  `(0, u, 0) ∈ D(L)` leaves `H̊(curl) ⊇ D(d¹)`, so that `P_K (0, u, 0) ∉ D(L)` -/
  projection_electric : (∃ u : L2Vec Ω 1,
      (∀ a b, ∃ φ, IsTestFn Ω φ ∧ ⇑(mat1 u a b) =ᵐ[volume.restrict Ω] φ) ∧
        ∀ v, IsTSD (mat1 v) → (∀ w, IsTSD (mat1 w) → ⟪u - v, w⟫_ℝ = 0) →
          v ∉ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain) ∧
    ∀ (W0 : Type) [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
      (d0 : W0 →ₗ.[ℝ] L2Vec Ω 1) (d1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2),
      Dense (d0.domain : Set W0) → Dense (d1.domain : Set (L2Vec Ω 1)) → d0.IsClosed →
      d1.IsClosed → (∀ x : d0.domain, ∃ h : d0 x ∈ d1.domain, d1 ⟨_, h⟩ = 0) →
      d1 ≤ vecOp (fun _ => dMin Ω 1) → ∃ u : L2Vec Ω 1, (∃ V, IsHodgeWave d0 d1 (0, u, 0) V) ∧
        ∀ v, IsTSD (mat1 v) → (∀ w, IsTSD (mat1 w) → ⟪u - v, w⟫_ℝ = 0) →
          v ∉ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain
  /-- `P_K D(L) ⊄ D(L)` in the magnetic slot too, whatever the electric one: the orthogonal
  projection onto `L²(TSD)` of some field with rows in `H(curl)` (`HΛ¹(Ω)³`) leaves `H(curl)`
  (for the electric boundary conditions `(0, 0, ρ) ∈ D(L)` iff the rows of `B` lie in `H(curl)`,
  the adjoint of the minimal curl being the maximal one), although on domains star-shaped with
  respect to a ball `L²(TSD) ∩ H(curl)` is dense in `L²(TSD)` (`StarShapedVerdict.density`);
  and for every boundary condition containing `n × E = 0`, the orthogonal projection `ρ'` onto
  `L²(TSD)` of some `ρ` with `(0, 0, ρ) ∈ D(L)` has `(0, 0, ρ') ∉ D(L)`, where
  `P_K (0, 0, ρ) = (0, 0, ρ')` (also for any closed electric part of `K` in place of
  `L²(TSD)`) -/
  projection_magnetic : (∃ u : L2Vec Ω 1,
      u ∈ (vecOp fun _ => dMax Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain ∧
        ∀ v, IsTSD (mat1 v) → (∀ w, IsTSD (mat1 w) → ⟪u - v, w⟫_ℝ = 0) →
          v ∉ (vecOp fun _ => dMax Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain) ∧
    ∀ (W0 : Type) [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
      (d0 : W0 →ₗ.[ℝ] L2Vec Ω 1) (d1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2),
      Dense (d0.domain : Set W0) → Dense (d1.domain : Set (L2Vec Ω 1)) → d0.IsClosed →
      d1.IsClosed → (∀ x : d0.domain, ∃ h : d0 x ∈ d1.domain, d1 ⟨_, h⟩ = 0) →
      d1 ≤ vecOp (fun _ => dMin Ω 1) → ∃ ρ : L2Vec Ω 2, (∃ V, IsHodgeWave d0 d1 (0, 0, ρ) V) ∧
        ∀ ρ', IsTSD (mat2 ρ') → (∀ w, IsTSD (mat2 w) → ⟪ρ - ρ', w⟫_ℝ = 0) →
          ¬∃ V, IsHodgeWave d0 d1 (0, 0, ρ') V
  /-- for every restriction `d¹` of the minimal curl (so for every boundary condition containing
  `n × E = 0`), `L²(TSD) ∩ D(d¹)` is not dense in `L²(TSD)` (for the electric boundary
  conditions, `L²(TSD) ∩ H̊(curl)`) -/
  not_dense : ∀ d1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2, d1 ≤ vecOp (fun _ => dMin Ω 1) →
    closure {u : L2Vec Ω 1 | IsTSD (mat1 u) ∧ u ∈ d1.domain} ≠ {u | IsTSD (mat1 u)}
  /-- the system (6.1) of the complex with weak symmetry loses the constraints too: from the TSD
  datum `(0, 0, 0, ⋆β)` of `D(L)` strong solutions exist on every `[0, T]`, and every one has at
  some times a non-TSD `E` and a non-symmetric `B` -/
  weakSymmetry : ∃ U₀, (∃ V, (bggData Ω).IsWave U₀ V) ∧ IsTSDState U₀ ∧ ∀ T > 0,
    (∃ U, U 0 = U₀ ∧ IsStrongSolution {p | (bggData Ω).IsWave p.1 p.2} (Icc 0 T) U) ∧
    ∀ U, U 0 = U₀ → IsStrongSolution {p | (bggData Ω).IsWave p.1 p.2} (Icc 0 T) U →
      (∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (U t).2.1)) ∧
      ∃ t ∈ Icc 0 T, ∃ a i, mat2 (U t).2.2.2 a i ≠ mat2 (U t).2.2.2 i a

/-- **The verdict of the electric boundary conditions on a domain `Ω` star-shaped with respect to
a ball** ([QuennevilleBelair2015], Prop 4.17), for the system (4.14): the density gap of
`ElectricVerdict` is the boundary condition of `H̊(curl)`, and whether only stationary data keep
the constraint is a spectral question. -/
structure StarShapedVerdict (Ω : Set (Fin 3 → ℝ)) : Prop where
  /-- `L²(TSD) ∩ HΛ¹(Ω)³` (the rows in `H(curl)`) is dense in `L²(TSD)`, while the closure of
  `L²(TSD) ∩ H̊(curl)` is `L²(TSD₀)` -/
  density : closure {u : L2Vec Ω 1 | IsTSD (mat1 u) ∧
      u ∈ (vecOp fun _ => dMax Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain} = {u | IsTSD (mat1 u)} ∧
    closure {u : L2Vec Ω 1 | IsTSD (mat1 u) ∧
      u ∈ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain} = {u | IsTSD₀ (mat1 u)}
  /-- for every evolution, `K*` consists of stationary data iff no nonzero TSD eigenfield `u` of
  `curl* curl` (`IsEigenfield`, `ξ > 0`) has `curl u ∉ H̊(curl)` -/
  stationary_iff (S : ℝ → _ →L[ℝ] _) (hS : IsEvolution ℝ (gradCurlWave Ω) univ S) :
    invariantCore S (tsdConstraint Ω) ⊆ {U | (U, 0) ∈ gradCurlWave Ω} ↔
      ¬∃ ξ > 0, ∃ v : L2Vec Ω 1, v ≠ 0 ∧ IsTSD (mat1 v) ∧ IsEigenfield Ω ξ v ∧
        ∀ h, ¬∃ w ∈ (vecOp fun _ => dMin Ω 1 : L2Vec Ω 1 →ₗ.[ℝ] L2Vec Ω 2).domain,
          mat1 w = mat2 ((vecOp fun _ => dMin Ω 1) ⟨v, h⟩)

/-- **The verdict of the electric boundary conditions on the box `∏ᵢ (aᵢ, aᵢ + ℓᵢ)`**, for the
system (4.14): only stationary data keep the constraint. -/
structure BoxVerdict (a ℓ : Fin 3 → ℝ) : Prop where
  /-- for every evolution, `K* = K ∩ N(L)`, with vanishing electric field -/
  core (S : ℝ → _ →L[ℝ] _) (hS : IsEvolution ℝ (gradCurlWave (box a ℓ)) univ S) :
    invariantCore S (tsdConstraint (box a ℓ)) =
        tsdConstraint (box a ℓ) ∩ {U | (U, 0) ∈ gradCurlWave (box a ℓ)} ∧
      ∀ U ∈ invariantCore S (tsdConstraint (box a ℓ)), U.2.1 = 0
  /-- forward invariance suffices: for all subspaces `S₁`, `S₂` of TSD fields, a strong solution
  on `[0, ∞)` stays in `{0} × S₁ × S₂` iff it starts there with `L U(0) = 0` -/
  forward (S₁ : Submodule ℝ (L2Vec (box a ℓ) 1)) (S₂ : Submodule ℝ (L2Vec (box a ℓ) 2))
    (h₁ : ∀ u ∈ S₁, IsTSD (mat1 u)) (h₂ : ∀ ρ ∈ S₂, IsTSD (mat2 ρ))
    (U : ℝ → L2Vec (box a ℓ) 0 × L2Vec (box a ℓ) 1 × L2Vec (box a ℓ) 2)
    (hU : IsStrongSolution (gradCurlWave (box a ℓ)) (Ici 0) U) :
    (∀ t ≥ 0, (U t).1 = 0 ∧ (U t).2.1 ∈ S₁ ∧ (U t).2.2 ∈ S₂) ↔
      ((U 0).1 = 0 ∧ (U 0).2.1 ∈ S₁ ∧ (U 0).2.2 ∈ S₂) ∧ (U 0, 0) ∈ gradCurlWave (box a ℓ)

/-- **The verdict of the absorbing (Silver–Müller) boundary conditions on the cube**
([QuennevilleBelair2015], §3.4), for the first-order system (`absorbing`, constraint `tsdPair`):
energy radiates, and the constraint is lost within every time interval `[0, T]`, in the boundary
layer only. -/
structure AbsorbingVerdict : Prop where
  /-- the first-order system is the graph of an m-dissipative operator (so
  `PropagationCriterion.semigroup` gives its evolution) -/
  mDissipative : ∃ A : WithLp 2 (L2Mat (cube 3) × L2Mat (cube 3)) →ₗ.[ℝ]
      WithLp 2 (L2Mat (cube 3) × L2Mat (cube 3)),
    (A.graph : SetRel _ _) = absorbing ∧ (∀ x : A.domain, ⟪A x, (x : _)⟫_ℝ ≤ 0) ∧
      ∀ y, ∃ x : A.domain, (x : _) - A x = y
  /-- some state radiates: `⟪A x, x⟫ < 0` -/
  radiates : ∃ p ∈ absorbing, ⟪p.2, p.1⟫_ℝ < 0
  /-- for every evolution and every `T > 0`, some TSD datum leaves `L²(TSD) × L²(TSD)` at some
  `t ∈ [0, T]` -/
  lost (S : ℝ → _ →L[ℝ] _) (hS : IsEvolution ℝ absorbing (Ici 0) S) (T : ℝ) (hT : 0 < T) :
    ∃ t ∈ Icc 0 T, ∃ x ∈ tsdPair, S t x ∉ tsdPair
  /-- for every evolution and every TSD datum `x`, the fields of `S t x`, `t ≥ 0`, keep the
  Gauss laws and are symmetric and trace-free almost everywhere on the domain of dependence
  `depDomain (cube 3) t`; so `S t x ∈ tsdPair` iff they are symmetric and trace-free almost
  everywhere on the boundary layer of width `t`, where the losses of `lost` occur (from `t = ¼` on,
  the boundary layer is the cube) -/
  interior (S : ℝ → _ →L[ℝ] _) (hS : IsEvolution ℝ absorbing (Ici 0) S)
    (x : WithLp 2 (L2Mat (cube 3) × L2Mat (cube 3))) (hx : x ∈ tsdPair) (t : ℝ) (ht : 0 ≤ t) :
    IsDivFree (fun a b => (S t x).fst (a, b)) ∧ IsDivFree (fun a b => (S t x).snd (a, b)) ∧
      IsSymTFOn (depDomain (cube 3) t) (fun a b => (S t x).fst (a, b)) ∧
      IsSymTFOn (depDomain (cube 3) t) (fun a b => (S t x).snd (a, b))

/-- **The verdict of the mirror boundary conditions on the cube** (tensorial reflections;
[QuennevilleBelair2015], §4.10, §6.1, §6.3) for a system `U' = A U` on the cube, an operator given
by its graph `A ⊆ X × X`, with a constraint `K ⊆ X`: the constraint is kept, with moving data.
`TSDVerdict.mirror` asserts it for the system (4.14) (`gradCurlMirror`, constraint
`tsdConstraint`) and for the system (6.1) (`mirrorData`, constraint `IsTSDState`). -/
structure MirrorVerdict {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : SetRel X X)
    (K : Set X) : Prop where
  /-- strong solutions are determined by their initial value -/
  unique (T : ℝ) (U U' : ℝ → X) (hU : IsStrongSolution A (Icc 0 T) U)
    (hU' : IsStrongSolution A (Icc 0 T) U') (h0 : U 0 = U' 0) : EqOn U U' (Icc 0 T)
  /-- strong solutions exist on every `[0, T]` from every datum of `D(A)` in `K` -/
  exists_solution (U₀ V : X) (hV : (U₀, V) ∈ A) (hU₀ : U₀ ∈ K) (T : ℝ) :
    ∃ U, U 0 = U₀ ∧ IsStrongSolution A (Icc 0 T) U
  /-- strong solutions from data in `K` stay in `K` -/
  propagates (T : ℝ) (U : ℝ → X) (hU : IsStrongSolution A (Icc 0 T) U) (h0 : U 0 ∈ K) :
    ∀ t ∈ Icc 0 T, U t ∈ K
  /-- some datum `U₀ ∈ K`, with `U₀`, `A U₀` and `A² U₀` in `D(A)`, is not stationary -/
  moving : ∃ U₀ V₁ V₂ V₃, (U₀, V₁) ∈ A ∧ (V₁, V₂) ∈ A ∧ (V₂, V₃) ∈ A ∧ U₀ ∈ K ∧ V₁ ≠ 0

/-- **The verdict of each boundary condition on the TSD constraints** ([QuennevilleBelair2015],
§4.10 (Prop 4.17), §6.1, §6.3), one field per row of the table of the module docstring; by
`PropagationCriterion` each verdict is about the invariant core `K*`. Whether on every bounded
domain only stationary data keep the constraint is open and not claimed: on the ball it is
equivalent to the absence of TSD eigenfields `u` with `curl u ∉ H̊(curl)` (`StarShapedVerdict`),
which `ball` proves only for the eigenfields `C²` up to the boundary. -/
structure TSDVerdict : Prop where
  /-- the electric boundary conditions on every open `Ω ⊆ ℝ³`, bounded or not (for `Ω = ℝ³`
  there is no boundary): every strong solution of (4.14) on `[0, T]` from data in `K` keeps
  `σ = 0` and the Gauss laws, and its fields are symmetric and trace-free almost everywhere on the
  domain of dependence `depDomain Ω t` (finite speed of propagation). So `U t ∈ K` iff they are
  symmetric and trace-free almost everywhere on the boundary layer `Ω \ depDomain Ω t`: on `ℝ³`
  the constraint is kept, and on a bounded `Ω` the loss of `ElectricVerdict.beta` from
  `(0, E₀, β)`, `E₀` TSD, occurs in the boundary layer -/
  interior (Ω : Set (Fin 3 → ℝ)) (hΩ : IsOpen Ω) (T : ℝ)
    (U : ℝ → L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) (hU : IsStrongSolution (gradCurlWave Ω) (Icc 0 T) U)
    (h0 : U 0 ∈ tsdConstraint Ω) (t : ℝ) (ht : t ∈ Icc 0 T) :
    (U t).1 = 0 ∧ IsDivFree (mat1 (U t).2.1) ∧ IsDivFree (mat2 (U t).2.2) ∧
      IsSymTFOn (depDomain Ω t) (mat1 (U t).2.1) ∧ IsSymTFOn (depDomain Ω t) (mat2 (U t).2.2)
  /-- the electric boundary conditions on every nonempty bounded open `Ω ⊆ ℝ³` -/
  electric (Ω : Set (Fin 3 → ℝ)) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : ElectricVerdict Ω
  /-- the electric boundary conditions on every nonempty bounded open `Ω ⊆ ℝ³` star-shaped with
  respect to a ball -/
  starShaped (Ω : Set (Fin 3 → ℝ)) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty)
    (hstar : ∃ x₀ s, 0 < s ∧ ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    StarShapedVerdict Ω
  /-- the electric boundary conditions on the unit ball: every TSD eigenfield of `curl* curl`
  (`ξ ≠ 0`) that is `C²` on a neighbourhood of the closed ball vanishes -/
  ball (ξ : ℝ) (hξ : ξ ≠ 0) (v : L2Vec unitBall 1) (hv : IsTSD (mat1 v))
    (hE : IsEigenfield unitBall ξ v)
    (hC : ∃ O : Set (Fin 3 → ℝ), IsOpen O ∧ {x | ∑ i, x i ^ 2 ≤ 1} ⊆ O ∧
      ∃ Φ : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ, (∀ a b, ContDiffOn ℝ 2 (Φ a b) O) ∧
        ∀ a b, ⇑(mat1 v a b) =ᵐ[volume.restrict unitBall] Φ a b) : v = 0
  /-- the electric boundary conditions on every box -/
  box (a ℓ : Fin 3 → ℝ) (hℓ : ∀ i, 0 < ℓ i) : BoxVerdict a ℓ
  /-- the absorbing boundary conditions on the cube -/
  absorbing : AbsorbingVerdict
  /-- the mirror boundary conditions on the cube, for the system (4.14) and for the system (6.1)
  with weak symmetry -/
  mirror : MirrorVerdict gradCurlMirror (tsdConstraint (cube 3)) ∧
    MirrorVerdict {p | mirrorData.IsWave p.1 p.2} {U | IsTSDState U}

/-! ### The theorems -/

end FEEC
