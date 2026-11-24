module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Variational crimes for Hilbert complexes

Galerkin methods for a Hilbert complex often do not use subspaces of its domain: on curved or
approximated domains and on hypersurfaces, with quadrature or with nonconforming spaces, the
discrete complex `(Xₕ, 𝐝ₕ)` has its own inner product and is compared with the continuous one
through reading maps `iₕ : Xₕ → W` that are not isometries and need not be cochain maps. What
survives of the approximation theory of finite element exterior calculus? Holst and Stern
([HolstStern2012], §3) answered for the mixed Hodge Laplacian with cochain reading maps, and Holst
and Tiee ([HolstTiee2018], §4) for the semidiscrete Hodge heat equation, with error estimates.
`FEEC.crimeFEEC` states the answer on every window `Wᵃ ⊕ ⋯ ⊕ W^{a+m-1}` with closed ranges of a
Hilbert complex (on `ℤ`, over `ℝ` or `ℂ`), for every family of discrete differential spaces
(`CrimeFamily`: finite-dimensional, `𝐝ₕ² = 0`, uniformly bounded reading maps with uniformly
bounded left inverses), in three clauses; the first and the third need no cochain reading maps,
beyond both sources:

1. **Stability and the Strang lemma.** Under a uniform discrete Poincaré inequality, the mixed
   Hodge Laplacian of the window and its discretizations with the load `iₕ* f` are uniquely
   solvable, the discrete solutions are uniformly stable, and their error is at most the read
   error of any discrete triple plus a constant times its residual; so the method converges for
   every datum once it is consistent on a dense set of data. The reading maps need not be cochain
   maps.
2. **Cochain reading maps.** If the `iₕ` are cochain maps with cochain projections bounded in the
   graph norm, the discrete Poincaré inequality holds, the method converges for every datum when
   the inner-product defect tends to `0` and `iₕ πₕ → 1` on `D(𝐝)`, the discrete cohomology is
   eventually that of the window (for finite-dimensional harmonic forms, with `iₕ πₕ → 1` on
   them), and the error is bounded by the approximation of the solution and the defect.
3. **The heat equation.** Under a uniform discrete Poincaré inequality, when the inner-product
   defect tends to `0` and the static method converges for every datum, the Hodge heat equation
   `u' = -Δ u` of the window is well posed and the semidiscrete and A-stable fully discrete
   solutions of `uₕ' = (𝐝ₕ - 𝐝ₕ*)² uₕ`, read by `iₕ`, converge to its solutions, with the temporal
   error of [BrennerThomee1979] (the route of [GilletteHolstZhu2017] with the elliptic projection
   of [Wheeler1973] built from the static theory with crimes).

The defects are the price of the crimes: the inner-product defect enters the estimates. It is
measured from the discrete graph norm, as the least `δ` with
`‖(1 - iₕ* iₕ) v‖ ≤ δ (‖v‖ + ‖𝐝ₕ v‖)`, since the estimates apply `1 - iₕ* iₕ` only to discrete
forms whose graph norm they control. It is at most the operator norm `‖1 - iₕ* iₕ‖`, which
[HolstStern2012], §3.3, require to tend to `0` for convergence, and can be much smaller: for mass
lumping of `P₁` elements ([Thomee2006], Ch. 15) it is `O(h)`, `h` the longest edge, while
`‖1 - iₕ* iₕ‖ ≥ n / (n + 2)` on every mesh of dimension `n`. The witness
`FEEC.crime_nonvacuous` shows that the hypotheses admit genuine crimes: on a Hilbert complex with
nonzero harmonic forms, non-isometric cochain reading maps with `‖1 - iₕ* iₕ‖ → 0`, hence a
vanishing defect, meet the hypotheses of the three clauses, read a discrete harmonic form off the
harmonic forms, and leave a positive error at every level. The witness
`FEEC.crime_defect_nonvacuous` shows that a vanishing defect is a strictly weaker hypothesis than
`‖1 - iₕ* iₕ‖ → 0`: on a Hilbert complex with `ℓ²(ℕ, ℝ)` in every degree, cochain reading maps with
`‖1 - iₙ* iₙ‖ = 1` at every level and a vanishing defect meet the hypotheses of the convergence
conjunct of the cochain clause and of the heat clause. The conforming case (subcomplexes with
cochain projections) is the Palomar entry `palomar/feec`.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996]
* [M. Holst, C. Tiee, *Finite element exterior calculus for parabolic evolution problems on Riemannian hypersurfaces*][HolstTiee2018]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006]
* [M. F. Wheeler, *A priori L₂ error estimates for Galerkin approximations to parabolic partial differential equations*][Wheeler1973]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace lp
open Filter Topology Set LinearPMap

universe u

@[expose] public noncomputable section

namespace FEEC

/-! ### Hilbert complexes and their windows -/
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
-- palomar-shared: boundaries
/-- The **boundaries** `𝔅ⁱ = R(d (i - 1) i) ⊆ Wⁱ` of a Hilbert complex, the range of its
differential into degree `i`. -/
def HilbertComplex.boundaries {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    (H : HilbertComplex 𝕜 W) (i : ℤ) : Submodule 𝕜 (W i) :=
  LinearMap.range (H.d (i - 1) i).toFun
-- palomar-shared-end: boundaries

/-! ### Mixed problems, evolutions and time schemes -/
-- palomar-shared: mixed
section Mixed
variable {𝕜 : Type*} [RCLike 𝕜] {E₀ E₁ E₂ : Type*} [NormedAddCommGroup E₀]
  [InnerProductSpace 𝕜 E₀] [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂]
  [InnerProductSpace 𝕜 E₂] (d₀ : E₀ →ₗ.[𝕜] E₁) (d₁ : E₁ →ₗ.[𝕜] E₂)
/-- The **mixed space** `D(d₀) × D(d₁) × E₁` of the Hodge Laplacian `d₀ d₀* + d₁* d₁` on `E₁`. -/
abbrev MixedSpace : Type _ := d₀.domain × d₁.domain × E₁
/-- The **mixed form** `B(σ, u, p; τ, v, q) = ⟪τ, σ⟫ - ⟪d₀τ, u⟫ + ⟪v, d₀σ⟫ + ⟪d₁v, d₁u⟫ + ⟪v, p⟫ -
⟪q, u⟫` at `x = (σ, u, p)`, `y = (τ, v, q)`. -/
def mixedForm (x y : MixedSpace d₀ d₁) : 𝕜 :=
  ⟪(y.1 : E₀), x.1⟫_𝕜 - ⟪d₀ y.1, x.2.1⟫_𝕜 + ⟪(y.2.1 : E₁), d₀ x.1⟫_𝕜 + ⟪d₁ y.2.1, d₁ x.2.1⟫_𝕜 +
    ⟪(y.2.1 : E₁), x.2.2⟫_𝕜 - ⟪y.2.2, (x.2.1 : E₁)⟫_𝕜
/-- The **Galerkin space** `(A ∩ D(d₀)) × (B ∩ D(d₁)) × Q` of `A ⊆ E₀` and `B, Q ⊆ E₁`. -/
def galerkin (A : Submodule 𝕜 E₀) (B Q : Submodule 𝕜 E₁) : Submodule 𝕜 (MixedSpace d₀ d₁) :=
  (A.comap d₀.domain.subtype).prod ((B.comap d₁.domain.subtype).prod Q)
variable {d₀ d₁} in
/-- `x = (σ, u, p)` solves the **mixed problem** with data `f` in `X`: `x ∈ X`, `B(x; y) = ⟪v, f⟫`
for all `y = (τ, v, q) ∈ X`; on a Galerkin space `A × B × Q` (test `(τ, 0, 0)`, `(0, v, 0)`,
`(0, 0, q)`) the equations `⟪τ, σ⟫ = ⟪d₀τ, u⟫`, `⟪v, d₀σ⟫ + ⟪d₁v, d₁u⟫ + ⟪v, p⟫ = ⟪v, f⟫` and
`u ⊥ Q` of [AFW2010], §3.2. -/
def IsMixedSolution (X : Submodule 𝕜 (MixedSpace d₀ d₁)) (f : E₁) (x : MixedSpace d₀ d₁) : Prop :=
  x ∈ X ∧ ∀ y ∈ X, mixedForm d₀ d₁ x y = ⟪(y.2.1 : E₁), f⟫_𝕜
end Mixed
-- palomar-shared-end: mixed
-- palomar-shared: IsStrongSolution
/-- `u` is a **strong solution** of `u' = A u` on `I ⊆ ℝ` for an operator given by its graph, a
relation `A ⊆ X × X` (a `LinearPMap` through its `graph`): `u` is continuous on `I` and at every
`t ∈ I` has, within `I`, a derivative `v` with `(u(t), v) ∈ A` (so `u(t)` lies in `D(A)`). -/
def IsStrongSolution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : SetRel X X)
    (I : Set ℝ) (u : ℝ → X) : Prop :=
  ContinuousOn u I ∧ ∀ t ∈ I, ∃ v, (u t, v) ∈ A ∧ HasDerivWithinAt u v I t
-- palomar-shared-end: IsStrongSolution
-- palomar-shared: rationalScheme
/-- `r = p/q` is **A-stable** ([HairerWanner1996], §IV.3): on the closed left half-plane `q` has
no zero and `|r| ≤ 1` (a property of the pair `p`, `q`; for coprime `p`, `q`, of `r`). -/
def IsAStable (p q : Polynomial ℝ) : Prop :=
  ∀ z : ℂ, z.re ≤ 0 → Polynomial.aeval z q ≠ 0 ∧
    ‖Polynomial.aeval z p / Polynomial.aeval z q‖ ≤ 1
/-- `r = p/q` has **order `m`**: `r(z) - e^z = O(z^{m+1})` as `z → 0` (with `q(0) ≠ 0`, as for
A-stable `p/q`, the quotient is the rational function near `0`). -/
def HasOrder (p q : Polynomial ℝ) (m : ℕ) : Prop :=
  (fun z : ℂ => Polynomial.aeval z p / Polynomial.aeval z q - Complex.exp z) =O[𝓝 0]
    fun z => z ^ (m + 1)
/-- **The rational scheme of a bounded operator**: `r(L) = p(L) q(L)⁻¹` for `r = p/q` (`0` if
`q(L)` is not invertible; for A-stable `p/q` and dissipative `L` on a Hilbert space it is). -/
def rationalApply {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (p q : Polynomial ℝ) (L : E →L[𝕜] E) : E →L[𝕜] E :=
  Polynomial.aeval L (p.map (algebraMap ℝ 𝕜)) *
    Ring.inverse (Polynomial.aeval L (q.map (algebraMap ℝ 𝕜)))
-- palomar-shared-end: rationalScheme
-- palomar-shared: evolution
section Evolution
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {κ : Type*} [NormedSpace ℝ E]
/-- The **flow** `t ↦ exp(t B)` of a bounded operator `B`: the solution operators of `u' = B u`
(for a discrete operator `Bₕ`, the semidiscrete evolution). -/
def semiflow {X : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] (B : X →L[𝕜] X) (t : ℝ) :
    X →L[𝕜] X := NormedSpace.exp ((t : 𝕜) • B)
/-- **The conclusions of the FEEC theorem for an evolution** `u' = A u` approximated by
`uₕ' = Bₕ uₕ` on spaces `Xₕ` read in `E` by `ιₕ`, exact evolution `S`: `S t x` is the unique strong
solution from `x ∈ D(A)` (dense), `S 0 = 1`, `‖S t x‖ ≤ ‖x‖`; for `ιₕ vₕ → x`, `ιₕ exp(t Bₕ) vₕ →
S t x` uniformly on `[0, T]` and `ιₕ r(τₕ Bₕ)ⁿ vₕ → S(nτₕ) x` (`r = P/Q` A-stable of order
`p ≥ 1`), with temporal error `K nτ τᵖ ‖Bₕ^{p+1} w‖` (`K` independent of `h`, `τ`, `n`, `w`). -/
structure EvolutionVerdict (A : E →ₗ.[𝕜] E) (l : Filter κ) (X : κ → Type*)
    [∀ h, NormedAddCommGroup (X h)] [∀ h, InnerProductSpace 𝕜 (X h)] (ι : ∀ h, X h →L[𝕜] E)
    (B : ∀ h, X h →L[𝕜] X h) (S : ℝ → E →L[𝕜] E) : Prop where
  dense : Dense (A.domain : Set E)
  solution (x : E) (hx : x ∈ A.domain) (T : ℝ) : IsStrongSolution A.graph (Icc 0 T) fun t => S t x
  unique (x : E) (hx : x ∈ A.domain) (T : ℝ) (u : ℝ → E) (hu0 : u 0 = x)
    (hu : IsStrongSolution A.graph (Icc 0 T) u) : EqOn u (fun t => S t x) (Icc 0 T)
  initial (x : E) : S 0 x = x
  contraction (x : E) {t : ℝ} (ht : 0 ≤ t) : ‖S t x‖ ≤ ‖x‖
  semidiscrete (x : E) (v : ∀ h, X h) (hv : Tendsto (fun h => ι h (v h)) l (𝓝 x)) (T : ℝ) :
    TendstoUniformlyOn (fun h (t : ℝ) => ι h (semiflow (B h) t (v h))) (fun t => S t x) l (Icc 0 T)
  rational (P Q : Polynomial ℝ) (hr : IsAStable P Q) {p : ℕ} (hp : HasOrder P Q p) (hp0 : 0 < p)
    (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) (hτ0 : Tendsto τ l (𝓝 0)) (x : E) (v : ∀ h, X h)
    (hv : Tendsto (fun h => ι h (v h)) l (𝓝 x)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in l, ∀ n : ℕ, (n : ℝ) * τ h ∈ Icc 0 T →
      ‖S (n * τ h) x - ι h ((rationalApply P Q ((τ h : 𝕜) • B h) ^ n) (v h))‖ < ε
  rational_temporal (P Q : Polynomial ℝ) (hr : IsAStable P Q) {p : ℕ} (hp : HasOrder P Q p) :
    ∃ K : ℝ, ∀ (h : κ) {τ : ℝ}, 0 ≤ τ → ∀ (n : ℕ) (w : X h),
      ‖semiflow (B h) (n * τ) w - (rationalApply P Q ((τ : 𝕜) • B h) ^ n) w‖ ≤
        K * (n * τ) * τ ^ p * ‖(B h ^ (p + 1)) w‖
end Evolution
-- palomar-shared-end: evolution

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex
/-! ### The mixed Hodge Laplacian of a window -/
section Window
variable (H : HilbertComplex 𝕜 W) (a : ℤ) (m : ℕ)
/-- The harmonic forms `ℌ = N(𝐝) ∩ N(𝐝*)` of the window. -/
def totalHarmonic : Submodule 𝕜 (Total W a m) := (H.totalD a m).ker ⊓ (H.totalD a m)†.ker
/-- The space `D(𝐝) × D(𝐝) × ℌ` of the mixed Hodge Laplacian of the window. -/
def totalMixedSpace : Submodule 𝕜 (MixedSpace (H.totalD a m) (H.totalD a m)) :=
  galerkin _ _ ⊤ ⊤ (H.totalHarmonic a m)

end Window

/-! ### Variational crimes -/

/-- A **family of discrete differential spaces** read in the window `[a, a + m)`
([HolstStern2012], §3), along the filter `l`: finite-dimensional Hilbert spaces `Xₕ` with
`𝐝ₕ 𝐝ₕ = 0`, uniformly bounded reading maps `iₕ : Xₕ → W` with uniformly bounded left inverses
(not necessarily cochain maps, isometries, or into `D(𝐝)`; no approximation property:
consistency, convergence and the limit of the defect are hypotheses of the theorem). -/
structure CrimeFamily (H : HilbertComplex 𝕜 W) (a : ℤ) (m : ℕ) (κ : Type*) where
  l : Filter κ
  X : κ → Type u
  [normedAddCommGroup : ∀ h, NormedAddCommGroup (X h)]
  [innerProductSpace : ∀ h, InnerProductSpace 𝕜 (X h)]
  [completeSpace : ∀ h, CompleteSpace (X h)]
  [finiteDimensional : ∀ h, FiniteDimensional 𝕜 (X h)]
  D : ∀ h, X h →L[𝕜] X h
  D_D : ∀ h v, D h (D h v) = 0
  incl : ∀ h, X h →L[𝕜] Total W a m
  proj : ∀ h, Total W a m →L[𝕜] X h
  proj_incl : ∀ h v, proj h (incl h v) = v
  bound : ∃ C, ∀ h, ‖incl h‖ ≤ C ∧ ‖proj h‖ ≤ C
attribute [instance] CrimeFamily.normedAddCommGroup CrimeFamily.innerProductSpace
  CrimeFamily.completeSpace CrimeFamily.finiteDimensional

namespace CrimeFamily
variable {H : HilbertComplex 𝕜 W} {a : ℤ} {m : ℕ} {κ : Type*} (S : H.CrimeFamily a m κ)
local notation "𝐝" => H.totalD a m
/-- The discrete harmonic forms `ℌₕ = N(𝐝ₕ) ∩ N(𝐝ₕ*)`. -/
def harmonic (h : κ) : Submodule 𝕜 (S.X h) :=
  LinearMap.ker (S.D h : S.X h →ₗ[𝕜] S.X h) ⊓ LinearMap.ker ((S.D h).adjoint : S.X h →ₗ[𝕜] S.X h)
/-- The discrete graph norm `‖τ‖ + ‖𝐝ₕτ‖ + ‖v‖ + ‖𝐝ₕv‖ + ‖q‖` of `y = (τ, v, q) ∈ Xₕ³`. -/
def graphNorm (h : κ) (y : S.X h × S.X h × S.X h) : ℝ :=
  ‖y.1‖ + ‖S.D h y.1‖ + ‖y.2.1‖ + ‖S.D h y.2.1‖ + ‖y.2.2‖
/-- The residual `B(x; y) - ⟪iₕ v, f⟫` of `x = (σ, u, p)` at `y = (τ, v, q)` in the discrete mixed
problem with the load `iₕ* f`, `B` the mixed form of `𝐝ₕ`. -/
def residual (h : κ) (f : Total W a m) (x y : S.X h × S.X h × S.X h) : 𝕜 :=
  ⟪y.1, x.1⟫_𝕜 - ⟪S.D h y.1, x.2.1⟫_𝕜 + ⟪y.2.1, S.D h x.1⟫_𝕜 + ⟪S.D h y.2.1, S.D h x.2.1⟫_𝕜 +
    ⟪y.2.1, x.2.2⟫_𝕜 - ⟪y.2.2, x.2.1⟫_𝕜 - ⟪S.incl h y.2.1, f⟫_𝕜
/-- `x = (σₕ, uₕ, pₕ)` solves the **discrete mixed problem** with the load `iₕ* f`: `pₕ ∈ ℌₕ` and
the residual vanishes at every `y ∈ Xₕ × Xₕ × ℌₕ`. -/
def IsSolution (h : κ) (f : Total W a m) (x : S.X h × S.X h × S.X h) : Prop :=
  x.2.2 ∈ S.harmonic h ∧ ∀ y, y.2.2 ∈ S.harmonic h → S.residual h f x y = 0
/-- `x' ∈ Xₕ × Xₕ × ℌₕ` has **residual at most `ε`** at `f` in the dual discrete graph norm. -/
def ResidualLE (h : κ) (f : Total W a m) (x' : S.X h × S.X h × S.X h) (ε : ℝ) : Prop :=
  x'.2.2 ∈ S.harmonic h ∧ ∀ y, y.2.2 ∈ S.harmonic h → ‖S.residual h f x' y‖ ≤ ε * S.graphNorm h y
/-- The **read gap** `‖y - iₕ v‖ + ‖z - iₕ 𝐝ₕ v‖` of `v ∈ Xₕ` from a form `y` with `𝐝y = z`. -/
def readGap (h : κ) (y z : Total W a m) (v : S.X h) : ℝ :=
  ‖y - S.incl h v‖ + ‖z - S.incl h (S.D h v)‖
/-- The **read error** `‖σ - iₕ σ'‖ + ‖𝐝σ - iₕ 𝐝ₕ σ'‖ + ‖u - iₕ u'‖ + ‖𝐝u - iₕ 𝐝ₕ u'‖ + ‖p - iₕ p'‖`
of `x' = (σ', u', p')` against `x = (σ, u, p)`. -/
def readError (h : κ) (x : MixedSpace 𝐝 𝐝) (x' : S.X h × S.X h × S.X h) : ℝ :=
  S.readGap h x.1 (𝐝 x.1) x'.1 + S.readGap h x.2.1 (𝐝 x.2.1) x'.2.1 + ‖x.2.2 - S.incl h x'.2.2‖
/-- The static method **converges** at the data `f`: the read errors of the discrete solutions
against the solution tend to `0`. -/
def ConvergesAt (f : Total W a m) : Prop :=
  ∀ x, IsMixedSolution (H.totalMixedSpace a m) f x → ∀ xh : ∀ h, S.X h × S.X h × S.X h,
    (∀ h, S.IsSolution h f (xh h)) → Tendsto (fun h => S.readError h x (xh h)) S.l (𝓝 0)
/-- The **inner-product defect** of the reading map in the discrete graph norm: the least `δ ≥ 0`
with `‖(1 - iₕ* iₕ) v‖ ≤ δ (‖v‖ + ‖𝐝ₕ v‖)` for every `v ∈ Xₕ`, the norm of `1 - iₕ* iₕ` from `Xₕ`
with the graph norm of `𝐝ₕ` to `Xₕ` (the set of these `δ` is closed, so the infimum is attained,
and contains `‖1 - iₕ* iₕ‖`, so the defect is at most `‖1 - iₕ* iₕ‖`). -/
def defect (h : κ) : ℝ :=
  sInf {δ | 0 ≤ δ ∧ ∀ v, ‖(1 - (S.incl h).adjoint ∘L S.incl h) v‖ ≤ δ * (‖v‖ + ‖S.D h v‖)}
/-- The **uniform discrete Poincaré inequality** `‖v‖ ≤ c_P ‖𝐝ₕ v‖` on `N(𝐝ₕ)ᗮ`. -/
def IsPoincare (cP : ℝ) : Prop :=
  ∀ h (v : S.X h), v ∈ (LinearMap.ker (S.D h : S.X h →ₗ[𝕜] S.X h))ᗮ → ‖v‖ ≤ cP * ‖S.D h v‖
/-- **Consistent approximation** at the data `f`: discrete triples whose read error against the
solution and whose residual tend to `0`. -/
def IsConsistentAt (f : Total W a m) : Prop :=
  ∀ x, IsMixedSolution (H.totalMixedSpace a m) f x → ∀ ε > 0, ∀ᶠ h in S.l,
    ∃ x', S.readError h x x' ≤ ε ∧ S.ResidualLE h f x' ε
/-- The reading maps are **cochain maps**: `iₕ Xₕ ⊆ D(𝐝)` and `𝐝 iₕ = iₕ 𝐝ₕ`. -/
structure IsCochain : Prop where
  incl_mem : ∀ h v, S.incl h v ∈ (𝐝).domain
  totalD_incl : ∀ h v, 𝐝 ⟨S.incl h v, incl_mem h v⟩ = S.incl h (S.D h v)
/-- **Cochain projections bounded by `C_π` in the graph norm** ([HolstStern2012], §3.3): linear
`πₕ : W → Xₕ` with `πₕ iₕ = 1`, `πₕ 𝐝 = 𝐝ₕ πₕ` and `‖πₕ x‖ ≤ C_π (‖x‖ + ‖𝐝 x‖)` on `D(𝐝)`. -/
structure CochainProj (Cπ : ℝ) where
  π : ∀ h, Total W a m →ₗ[𝕜] S.X h
  π_incl : ∀ h v, π h (S.incl h v) = v
  norm_π_le : ∀ h (x : (𝐝).domain), ‖π h x‖ ≤ Cπ * (‖(x : Total W a m)‖ + ‖𝐝 x‖)
  π_totalD : ∀ h (z : (𝐝).domain), π h (𝐝 z) = S.D h (π h z)

/-- **The static FEEC theorem with variational crimes**, constant `C`: unique solvability,
stability, the Strang lemma (error at most the read error of any discrete triple plus `C` times
its residual), and convergence for every datum from consistency on a dense set. -/
structure StaticVerdict (C : ℝ) : Prop where
  existsUnique (f : Total W a m) : (∃! x, IsMixedSolution (H.totalMixedSpace a m) f x) ∧
    ∀ h, ∃! x, S.IsSolution h f x
  stable (h : κ) {f x} (hs : S.IsSolution h f x) : S.graphNorm h x ≤ C * ‖f‖
  strang (h : κ) {f x} (hs : IsMixedSolution (H.totalMixedSpace a m) f x) {xh}
    (hsh : S.IsSolution h f xh) {x' ε} (hε : 0 ≤ ε) (hres : S.ResidualLE h f x' ε) :
    S.readError h x xh ≤ S.readError h x x' + C * ε
  converges {D : Set (Total W a m)} (hD : Dense D) (hc : ∀ g ∈ D, S.IsConsistentAt g) (f) :
    S.ConvergesAt f

/-- **The static FEEC theorem with cochain reading maps** and the cochain projections `P`
([HolstStern2012], Thms 3.3, 3.5, 3.10, Cors 3.4, 3.11). -/
structure CochainVerdict {Cπ : ℝ} (P : S.CochainProj Cπ) : Prop where
  poincare : ∃ cP, S.IsPoincare cP
  /-- convergence for every datum when the inner-product defect tends to `0` and `iₕ πₕ → 1` on
  `D(𝐝)` -/
  converges (hJ : Tendsto S.defect S.l (𝓝 0))
    (hπ : ∀ x : (𝐝).domain, Tendsto (fun h => ‖(x : Total W a m) - S.incl h (P.π h x)‖) S.l (𝓝 0))
    (f) : S.ConvergesAt f
  /-- eventually `[z] ↦ [πₕ z]` is an isomorphism `H(𝐝) ≅ H(𝐝ₕ)`: onto (every discrete cycle is
  `πₕ` of a cycle up to a discrete boundary) and one-to-one (a cycle `z` with `πₕ z` a discrete
  boundary is a boundary) -/
  cohomology [FiniteDimensional 𝕜 (H.totalHarmonic a m)]
    (hπ : ∀ q ∈ H.totalHarmonic a m, Tendsto (fun h => ‖q - S.incl h (P.π h q)‖) S.l (𝓝 0)) :
    ∀ᶠ h in S.l, (∀ w : S.X h, S.D h w = 0 → ∃ z : (𝐝).domain, 𝐝 z = 0 ∧
        ∃ y, w - P.π h z = S.D h y) ∧
      ∀ z : (𝐝).domain, 𝐝 z = 0 → (∃ y, P.π h z = S.D h y) →
        ∃ y : (𝐝).domain, (z : Total W a m) = 𝐝 y
  /-- the error is at most `K ε` when `σ, u, p` and `P_𝔅 u` are within `ε` of `iₕ Xₕ` in the read
  error and the inner-product defect times `‖σ‖ + ‖𝐝σ‖ + ‖u‖ + ‖𝐝u‖ + ‖p‖` is at most `ε` -/
  rate : ∃ K : ℝ, ∀ (h : κ) {f x}, IsMixedSolution (H.totalMixedSpace a m) f x → ∀ {xh},
    S.IsSolution h f xh → ∀ {ε : ℝ}, (∃ v, S.readGap h x.1 (𝐝 x.1) v ≤ ε) →
      (∃ v, S.readGap h x.2.1 (𝐝 x.2.1) v ≤ ε) → (∃ v, S.readGap h x.2.2 0 v ≤ ε) →
      (∃ v, S.readGap h ((LinearMap.range (𝐝).toFun).topologicalClosure.starProjection x.2.1) 0 v
        ≤ ε) →
      S.defect h * (‖(x.1 : Total W a m)‖ + ‖𝐝 x.1‖ + ‖(x.2.1 : Total W a m)‖ + ‖𝐝 x.2.1‖ +
        ‖x.2.2‖) ≤ ε → S.readError h x xh ≤ K * ε

end CrimeFamily
end HilbertComplex

/-! ### Variational crimes: the theorem and its witness -/

variable [∀ i, NormedSpace ℝ (W i)]
/-- **Variational crimes** ([HolstStern2012], §3: Thms 3.3, 3.5, 3.9, 3.10,
Cors 3.4, 3.11). On a window with closed ranges, for a family of discrete differential spaces
read by `iₕ`: under a uniform discrete Poincaré inequality, the static verdict (unique
solvability, stability, the Strang lemma, convergence from consistency on a dense set); for
cochain reading maps with cochain projections bounded in the graph norm, the cochain verdict
(discrete Poincaré inequality, convergence, cohomology isomorphisms, error bound); and under a
uniform discrete Poincaré inequality, when the inner-product defect (in the discrete graph norm)
tends to `0` and the static method converges for every datum, the evolution verdict of
`u' = L² u` by `(𝐝ₕ - 𝐝ₕ*)²` read by `iₕ`. -/
theorem crimeFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} {a : ℤ} {m : ℕ} (S : H.CrimeFamily a m κ)
    (hcr : ∀ i : Fin m, 0 < (i : ℕ) →
      IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ))))) :
    (∀ {cP : ℝ}, S.IsPoincare cP → ∃ C, S.StaticVerdict C) ∧
    (S.IsCochain → ∀ {Cπ : ℝ} (P : S.CochainProj Cπ), S.CochainVerdict P) ∧
    ∀ {cP : ℝ}, S.IsPoincare cP → Tendsto S.defect S.l (𝓝 0) → (∀ f, S.ConvergesAt f) →
      ∃ U, EvolutionVerdict (sq (H.wave a m)) S.l S.X S.incl
        (fun h => (S.D h - (S.D h).adjoint) ^ 2) U := by
  sorry

/-- **Non-vacuity of `FEEC.crimeFEEC`**: a Hilbert complex with `ℝ` in every degree, with closed
ranges and nonzero harmonic forms on the window `[0, 3)`, carries a family of discrete
differential spaces with cochain reading maps `iₙ` and cochain projections `πₙ`, `iₙ πₙ = 1`, not
isometric (`iₙ* iₙ ≠ 1`) but with `‖1 - iₙ* iₙ‖ → 0`, so with a vanishing inner-product defect
(at most `‖1 - iₙ* iₙ‖`), that meets the hypotheses of the three clauses (with the discrete
Poincaré inequality and convergence for every datum); a discrete harmonic form is read off `ℌ`,
and the error at some datum is positive at every level. -/
theorem crime_nonvacuous : ∃ (H : HilbertComplex ℝ fun _ : ℤ => ℝ)
    (S : H.CrimeFamily.{0} 0 3 ℕ) (P : S.CochainProj 2),
    (∀ i : Fin 3, 0 < (i : ℕ) → IsClosed (H.boundaries (0 + (i : ℕ)) : Set ℝ)) ∧
    S.l = atTop ∧ S.IsCochain ∧ (∃ cP, S.IsPoincare cP) ∧
    (∀ n, (S.incl n).adjoint ∘L S.incl n ≠ 1) ∧
    Tendsto (fun n => ‖1 - (S.incl n).adjoint ∘L S.incl n‖) atTop (𝓝 0) ∧
    Tendsto S.defect atTop (𝓝 0) ∧ (∀ n (x : (H.totalD 0 3).domain), S.incl n (P.π n x) = x) ∧
    (∀ f, S.ConvergesAt f) ∧
    (∃ q ∈ H.totalHarmonic 0 3, q ≠ 0) ∧
    (∀ n, ∃ q ∈ S.harmonic n, S.incl n q ∉ H.totalHarmonic 0 3) ∧
    ∃ f, ∀ x, IsMixedSolution (H.totalMixedSpace 0 3) f x → ∀ n xh,
      S.IsSolution n f xh → 0 < S.readError n x xh := by
  sorry

/-- **Non-vacuity of the defect in the graph norm**: a Hilbert complex with `ℓ²(ℕ, ℝ)` in every
degree, with closed ranges on the window `[0, 2)`, carries a family of discrete differential spaces
with cochain reading maps `iₙ` and cochain projections `πₙ` bounded by `1` in the graph norm, with
`iₙ πₙ → 1` on `D(𝐝)`, such that `‖1 - iₙ* iₙ‖ = 1` at every level (so `‖1 - iₙ* iₙ‖ ↛ 0`) while
the inner-product defect tends to `0`; with the discrete Poincaré inequality and convergence for
every datum, it meets the hypotheses of the convergence conjunct of the cochain clause and of the
heat clause of `FEEC.crimeFEEC`, which the hypothesis `‖1 - iₙ* iₙ‖ → 0` would exclude. -/
theorem crime_defect_nonvacuous : ∃ (H : HilbertComplex ℝ fun _ : ℤ => ℓ²(ℕ, ℝ))
    (S : H.CrimeFamily.{0} 0 2 ℕ) (P : S.CochainProj 1),
    (∀ i : Fin 2, 0 < (i : ℕ) → IsClosed (H.boundaries (0 + (i : ℕ)) : Set ℓ²(ℕ, ℝ))) ∧
    S.l = atTop ∧ S.IsCochain ∧ (∃ cP, S.IsPoincare cP) ∧
    (∀ n, ‖1 - (S.incl n).adjoint ∘L S.incl n‖ = 1) ∧ Tendsto S.defect atTop (𝓝 0) ∧
    (∀ x : (H.totalD 0 2).domain, Tendsto (fun n =>
      ‖(x : Total (fun _ : ℤ => ℓ²(ℕ, ℝ)) 0 2) - S.incl n (P.π n x)‖) atTop (𝓝 0)) ∧
    ∀ f, S.ConvergesAt f := by
  sorry

end FEEC
