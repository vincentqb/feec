module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but the theorems `FEEC.fem`,
`FEEC.femMin`, `FEEC.fem_parallelepiped` and `FEEC.maxwell`), compiled against Mathlib alone so
that their elaborated values are those of the challenge. The solution imports this module and the bridges to
`Feec`, and proves the theorems (`Solution.lean`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3, §5
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–§3.5, §4, §5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6, 7
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.3
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 4

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Filter Topology Set LinearPMap MeasureTheory

@[expose] public noncomputable section

namespace FEEC

/-! ### Hilbert complexes and families of subcomplexes (verbatim from `palomar/feec`) -/

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

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W)

/-- The **graph norm** `‖x‖_V = (‖x‖² + ‖d x‖²)^½` on `D(d i j)`. -/
def graphNorm (i j : ℤ) (x : (H.d i j).domain) : ℝ := √(‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2)

/-- A **subcomplex**: subspaces `Vⁱ ⊆ D(d i j)` with `d Vⁱ ⊆ Vʲ`. -/
structure Subcomplex where
  /-- the subspaces -/
  V : ∀ i, Submodule 𝕜 (W i)
  le_domain : ∀ i j, V i ≤ (H.d i j).domain
  mapsTo : ∀ i j (x : W i) (hx : x ∈ V i), (H.d i j ⟨x, le_domain i j hx⟩ : W j) ∈ V j

/-- A **cochain projection** onto `S`: projections `πⁱ : D(dⁱ) → Sⁱ` of the domain complex
commuting with `d`. -/
structure Subcomplex.CochainProjection {H : HilbertComplex 𝕜 W} (S : H.Subcomplex) where
  /-- the projections -/
  π : ∀ i, (H.d i (i + 1)).domain →ₗ[𝕜] S.V i
  proj : ∀ i (x : (H.d i (i + 1)).domain), (x : W i) ∈ S.V i → (π i x : W i) = x
  comm : ∀ i (x : (H.d i (i + 1)).domain),
    H.d i (i + 1) ⟨π i x, S.le_domain i (i + 1) (π i x).2⟩ =
      π (i + 1) ⟨H.d i (i + 1) x, H.mapsTo i (i + 1) (i + 1 + 1) x⟩

/-- A **family of subcomplexes** of `H` along the filter `l` (the refinement `h → 0`):
finite-dimensional subcomplexes `Vₕ` with cochain projections `πₕ`. It carries no bound and no
approximation property: these are hypotheses of the theorem. -/
structure SubcomplexFamily (κ : Type*) where
  /-- the filter of the refinement `h → 0` -/
  l : Filter κ
  /-- the subcomplexes -/
  V : κ → H.Subcomplex
  [finiteDimensional : ∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
  /-- the cochain projections -/
  π : ∀ h, (V h).CochainProjection

attribute [instance] SubcomplexFamily.finiteDimensional

/-- The boundaries `𝔅ⁱ = R(d (i - 1) i)`. -/
def boundaries (i : ℤ) : Submodule 𝕜 (W i) := LinearMap.range (H.d (i - 1) i).toFun

/-- The distance `E(x) = inf_{v ∈ Vⁱ} ‖x - v‖_V` from `x ∈ D(d i j)` to `Vⁱ` in the graph norm. -/
def Subcomplex.graphDist {H : HilbertComplex 𝕜 W} (S : H.Subcomplex) (i j : ℤ)
    (x : (H.d i j).domain) : ℝ :=
  ⨅ v : S.V i, H.graphNorm i j (x - ⟨v, S.le_domain i j v.2⟩)

variable {H} {κ : Type*}

/-- The cochain projections of `F` are **bounded in the graph norm by `C`** in degree `i`,
uniformly in `h`: `‖πₕ x‖_V ≤ C ‖x‖_V` on `D(d i (i + 1))`. -/
def SubcomplexFamily.IsGraphBoundedBy (F : H.SubcomplexFamily κ) (i : ℤ) (C : ℝ) : Prop :=
  ∀ (h : κ) (x : (H.d i (i + 1)).domain),
    H.graphNorm i (i + 1) ⟨(F.π h).π i x, (F.V h).le_domain i (i + 1) ((F.π h).π i x).2⟩ ≤
      C * H.graphNorm i (i + 1) x

/-- The cochain projections of `F` are **bounded in the graph norm** in degree `i`, uniformly in
`h`. -/
def SubcomplexFamily.IsGraphBounded (F : H.SubcomplexFamily κ) (i : ℤ) : Prop :=
  ∃ C : ℝ, F.IsGraphBoundedBy i C

/-- `F` **approximates** in degree `i` in the graph norm: the distance from every `x ∈ D(d)` to
`Vₕⁱ` in the graph norm tends to `0`. -/
def SubcomplexFamily.Approximates (F : H.SubcomplexFamily κ) (i : ℤ) : Prop :=
  ∀ x : (H.d i (i + 1)).domain, Tendsto (fun h => (F.V h).graphDist i (i + 1) x) F.l (𝓝 0)

/-- **A Jackson estimate** for `F` ([AFW2010], §3.5): a mesh size `hₕ → 0` and, for every
regularity index `s : ρ`, classes `Reg s i L` of `s`-regular forms in `Wⁱ` with bound `L`,
approximated in `Vₕⁱ` at the order `hₕ^{ord s}`: some `v ∈ Vₕⁱ` has `‖x - v‖ ≤ B L hₕ^{ord s}`
and `‖d (x - v)‖ ≤ B L hₕ^{ord s}`. -/
structure SubcomplexFamily.Jackson (F : H.SubcomplexFamily κ) (ρ : Type*) where
  /-- the mesh size -/
  meshSize : κ → ℝ
  meshSize_nonneg : ∀ h, 0 ≤ meshSize h
  tendsto_meshSize : Tendsto meshSize F.l (𝓝 0)
  /-- `Reg s i L x`: `x ∈ Wⁱ` is `s`-regular with bound `L` -/
  Reg : ρ → ∀ i, ℝ → W i → Prop
  /-- the order of the class `s` -/
  ord : ρ → ℝ
  /-- the constants -/
  B : ρ → ℤ → ℝ
  jackson : ∀ s h i {L : ℝ} (x : W i), 0 ≤ L → Reg s i L x → ∃ v, ∃ hv : v ∈ (F.V h).V i,
    ‖x - v‖ ≤ B s i * (L * meshSize h ^ ord s) ∧ ∀ j (hx : x ∈ (H.d i j).domain),
      ‖H.d i j ⟨x - v, Submodule.sub_mem _ hx ((F.V h).le_domain i j hv)⟩‖ ≤
        B s i * (L * meshSize h ^ ord s)

end HilbertComplex

/-! ### Evolutions and time schemes (verbatim from `palomar/feec`) -/

section Evolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {κ : Type*}

/-- The square `A²` on `D(A²) = {x ∈ D(A) | A x ∈ D(A)}`. -/
def sq (A : E →ₗ.[𝕜] E) : E →ₗ.[𝕜] E :=
  A.comp (A.domRestrict ((A.domain.comap A.toFun).map A.domain.subtype)) fun x => by
    obtain ⟨y, hy, hyx⟩ := x.2.1
    have : (⟨x, x.2.2⟩ : A.domain) = y := Subtype.ext hyx.symm
    change A ⟨(x : E), x.2.2⟩ ∈ A.domain
    rw [this]
    exact hy

/-- The closed subspace `K` **reduces** `A`: `P_K D(A) ⊆ D(A)` and `A P_K = P_K A` on `D(A)`. -/
def IsReducing (A : E →ₗ.[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] : Prop :=
  ∀ x : A.domain, ∃ hx : K.starProjection (x : E) ∈ A.domain,
    A ⟨_, hx⟩ = K.starProjection (A x)

/-- A **rational time scheme** `r = n/d` ([HairerWanner1996], §IV.3): real polynomials with
`deg n ≤ deg d` and `d(z) ≠ 0` for `re z ≤ 0`; a step is `wₙ₊₁ = r(τ B) wₙ`. The θ-scheme
`wₙ₊₁ - wₙ = τ B (θ wₙ₊₁ + (1 - θ) wₙ)` is `n = 1 + (1 - θ) X`, `d = 1 - θ X`, A-stable for
`θ ≥ 1/2`, of order 1, and 2 for Crank–Nicolson `θ = 1/2`. -/
structure RationalScheme where
  /-- the numerator -/
  num : Polynomial ℝ
  /-- the denominator -/
  den : Polynomial ℝ
  natDegree_num_le : num.natDegree ≤ den.natDegree
  aeval_den_ne_zero : ∀ z : ℂ, z.re ≤ 0 → Polynomial.aeval z den ≠ 0

namespace RationalScheme

variable (r : RationalScheme)

/-- **A-stability**: `|r(iy)| ≤ 1` for every real `y`; with no poles in `re z ≤ 0` and
`deg n ≤ deg d`, equivalent to `|r(z)| ≤ 1` on `re z ≤ 0` by the maximum principle. -/
def IsAStable : Prop :=
  ∀ y : ℝ, ‖Polynomial.aeval ((y : ℂ) * Complex.I) r.num /
    Polynomial.aeval ((y : ℂ) * Complex.I) r.den‖ ≤ 1

/-- **Order `p`**: `r(z) - e^z = O(z^{p+1})` at `0`, i.e. `X^{p+1}` divides `n - d Tₚ`,
`Tₚ = ∑_{j ≤ p} Xʲ/j!`. -/
def HasOrder (p : ℕ) : Prop :=
  Polynomial.X ^ (p + 1) ∣ r.num - r.den * ∑ j ∈ Finset.range (p + 1),
    Polynomial.C (1 / (j.factorial : ℝ)) * Polynomial.X ^ j

/-- `r(B) = n(B) d(B)⁻¹` for a bounded operator `B` (`d(B)` is invertible for dissipative `B`). -/
def apply (B : E →L[𝕜] E) : E →L[𝕜] E :=
  Polynomial.aeval B (r.num.map (algebraMap ℝ 𝕜)) *
    Ring.inverse (Polynomial.aeval B (r.den.map (algebraMap ℝ 𝕜)))

end RationalScheme

variable [NormedSpace ℝ E]

/-- `u` is a **strong solution** of `u' = A u` on `I`. -/
def IsStrongSolution (A : E →ₗ.[𝕜] E) (I : Set ℝ) (u : ℝ → E) : Prop :=
  ContinuousOn u I ∧ ∀ t ∈ I, ∃ v, (u t, v) ∈ A.graph ∧ HasDerivWithinAt u v I t

/-- The semidiscrete evolution `exp(t B)`. -/
def semiflow {X : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] (B : X →L[𝕜] X)
    (t : ℝ) : X →L[𝕜] X :=
  NormedSpace.exp ((t : 𝕜) • B)

/-- **The FEEC theorem for an evolution** `u' = A u` approximated by `uₕ' = Bₕ uₕ` on the
finite-dimensional `Xₕ ⊆ E`, with exact evolution `S`: `S t x` is the unique strong solution
from `x ∈ D(A)` (`D(A)` dense), `S 0 = 1`, `‖S t x‖ ≤ ‖x‖`; the semidiscrete solutions
`exp(t Bₕ) vₕ` and the iterates `r(τₕ Bₕ)ⁿ vₕ` of every A-stable rational scheme of order
`p ≥ 1` converge as `h, τₕ → 0`, the latter with the temporal error `K nτ τᵖ ‖Bₕ^{p+1} w‖`; and
a closed `K` reduces `A` iff `S` keeps both `K` and `Kᗮ` forward in time. -/
structure EvolutionVerdict (A : E →ₗ.[𝕜] E) (l : Filter κ) (X : κ → Submodule 𝕜 E)
    (B : ∀ h, X h →L[𝕜] X h) (S : ℝ → E →L[𝕜] E) : Prop where
  dense : Dense (A.domain : Set E)
  solution (x : E) (hx : x ∈ A.domain) (T : ℝ) : IsStrongSolution A (Icc 0 T) fun t => S t x
  unique (x : E) (hx : x ∈ A.domain) (T : ℝ) (u : ℝ → E) (hu0 : u 0 = x)
    (hu : IsStrongSolution A (Icc 0 T) u) : EqOn u (fun t => S t x) (Icc 0 T)
  initial (x : E) : S 0 x = x
  contraction (x : E) {t : ℝ} (ht : 0 ≤ t) : ‖S t x‖ ≤ ‖x‖
  semidiscrete (x : E) (v : ∀ h, X h) (hv : Tendsto (fun h => (v h : E)) l (𝓝 x)) (T : ℝ) :
    TendstoUniformlyOn (fun h (t : ℝ) => (semiflow (B h) t (v h) : E))
      (fun t => S t x) l (Icc 0 T)
  rational (r : RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) (hp0 : 0 < p)
    (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) (hτ0 : Tendsto τ l (𝓝 0)) (x : E) (v : ∀ h, X h)
    (hv : Tendsto (fun h => (v h : E)) l (𝓝 x)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in l, ∀ n : ℕ, (n : ℝ) * τ h ∈ Icc 0 T →
      ‖S (n * τ h) x - ((r.apply ((τ h : 𝕜) • B h) ^ n) (v h) : E)‖ < ε
  /-- `K` independent of `h`, `τ`, `n`, `w` -/
  rational_temporal (r : RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) :
    ∃ K : ℝ, ∀ (h : κ) {τ : ℝ}, 0 ≤ τ → ∀ (n : ℕ) (w : X h),
      ‖semiflow (B h) (n * τ) w - (r.apply ((τ : 𝕜) • B h) ^ n) w‖ ≤
        K * (n * τ) * τ ^ p * ‖(B h ^ (p + 1)) w‖
  /-- a closed `K` reduces `A` iff `S t`, `t ≥ 0`, maps `K` into `K` and `Kᗮ` into `Kᗮ` (the
  criterion for m-dissipative `A`; for a unitary group, `WaveVerdict.propagates_iff` asks `K`
  alone, for all `t`) -/
  reducing_iff (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] : IsReducing A K ↔
    (∀ t, 0 ≤ t → ∀ x ∈ K, S t x ∈ K) ∧ ∀ t, 0 ≤ t → ∀ x ∈ Kᗮ, S t x ∈ Kᗮ

end Evolution

/-! ### Windows and the wave and heat verdicts (verbatim from `palomar/feec`) -/

/-- The total space `Wᵃ ⊕ ⋯ ⊕ W^{a+m-1}` of a window (an `ℓ²` sum). -/
abbrev Total (W : ℤ → Type*) (a : ℤ) (m : ℕ) : Type _ := PiLp 2 fun i : Fin m => W (a + (i : ℕ))

namespace HilbertComplex

section Window

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

end Window

namespace SubcomplexFamily

variable {H : HilbertComplex 𝕜 W} {κ : Type*} (F : H.SubcomplexFamily κ) (a : ℤ) (m : ℕ)

/-- The discrete total space `Xₕ = Vₕᵃ ⊕ ⋯ ⊕ Vₕ^{a+m-1}`. -/
def Xh (h : κ) : Submodule 𝕜 (Total W a m) where
  carrier := {x | ∀ i : Fin m, x i ∈ (F.V h).V (a + (i : ℕ))}
  add_mem' hx hy i := add_mem (hx i) (hy i)
  zero_mem' _ := zero_mem _
  smul_mem' c _ hx i := Submodule.smul_mem _ c (hx i)

instance (h : κ) : FiniteDimensional 𝕜 (F.Xh a m h) :=
  Module.Finite.of_injective
    (LinearMap.pi fun i : Fin m => LinearMap.codRestrict ((F.V h).V (a + (i : ℕ)))
      ((PiLp.projₗ 2 _ i).comp (F.Xh a m h).subtype) fun x => x.2 i)
    fun _ _ hxy => Subtype.ext (PiLp.ext fun i => congrArg Subtype.val (congrFun hxy i))

theorem Xh_le (h : κ) : F.Xh a m h ≤ H.totalDomain a m :=
  fun _ hx _ _ => (F.V h).le_domain _ _ (hx _)

/-- The discrete total differential `𝐝ₕ : Xₕ → Xₕ`. -/
def Dh (h : κ) : F.Xh a m h →L[𝕜] F.Xh a m h :=
  LinearMap.toContinuousLinearMap <| LinearMap.codRestrict _
    ((H.totalD a m).toFun ∘ₗ Submodule.inclusion (F.Xh_le a m h)) fun x j =>
      show (∑ i : Fin m, H.d (a + (i : ℕ)) (a + (j : ℕ)) ⟨(x : Total W a m) i, _⟩) ∈ _ from
        Submodule.sum_mem _ fun i _ => (F.V h).mapsTo _ _ _ (x.2 i)

/-- The discrete wave operator `Lₕ = 𝐝ₕ - 𝐝ₕ*`. -/
def Lh (h : κ) : F.Xh a m h →L[𝕜] F.Xh a m h := F.Dh a m h - (F.Dh a m h).adjoint

/-- The distance `inf_{w ∈ Xₕ} ‖y - w‖ + ‖𝐝 y - 𝐝 w‖` from `y ∈ D(𝐝)` to `Xₕ` in the graph
norm of the window. -/
def graphDist (h : κ) (y : (H.totalD a m).domain) : ℝ :=
  ⨅ w : F.Xh a m h, ‖(y : Total W a m) - w‖ +
    ‖H.totalD a m y - H.totalD a m ⟨w, F.Xh_le a m h w.2⟩‖

variable [∀ i, NormedSpace ℝ (W i)]

/-- **The conclusions of the FEEC theorem for the Hodge wave equation** on the window, with
exact evolution `S`. -/
structure WaveVerdict (S : ℝ → Total W a m →L[𝕜] Total W a m) : Prop where
  /-- well-posedness and convergence of the semidiscrete and fully discrete solutions -/
  evolution : EvolutionVerdict (H.wave a m) F.l (F.Xh a m) (F.Lh a m) S
  /-- `S` is a unitary group -/
  norm_eq (t : ℝ) (x : Total W a m) : ‖S t x‖ = ‖x‖
  add (s t : ℝ) : S (s + t) = S s ∘L S t
  /-- the semidiscrete error bound: for `x ∈ D(L²)`, if the graph-norm distances of `S(s) x` and
  `S(s) L x` to `Xₕ` are at most `M` for `s ∈ [0, t]`, then
  `‖S(t) x - exp(t Lₕ) v‖ ≤ ‖v - x‖ + 2 (1 + C_P) (1 + t) M`, `C_P = 4√3` the uniform bound of
  the elliptic projections -/
  error (x : Total W a m) (hx : x ∈ (H.wave a m).domain)
    (hx2 : H.wave a m ⟨x, hx⟩ ∈ (H.wave a m).domain) (h : κ) (v : F.Xh a m h) {t M : ℝ}
    (ht : 0 ≤ t) (hM : ∀ s ∈ Icc 0 t, ∀ y : (H.totalD a m).domain,
      (y : Total W a m) = S s x ∨ (y : Total W a m) = S s (H.wave a m ⟨x, hx⟩) →
        F.graphDist a m h y ≤ M) :
    ‖S t x - (semiflow (F.Lh a m h) t v : Total W a m)‖ ≤
      ‖(v : Total W a m) - x‖ + 2 * (1 + 4 * √3) * (1 + t) * M
  /-- a closed constraint `K` propagates (for all `t`, forward and backward) iff it reduces `L`
  (`IsReducing`, [Kato1995], §III.5.6) -/
  propagates_iff (K : Submodule 𝕜 (Total W a m)) [K.HasOrthogonalProjection] :
    IsReducing (H.wave a m) K ↔ ∀ t, ∀ x ∈ K, S t x ∈ K
  /-- the invariant core: the data whose solutions stay in `K` form the largest closed subspace
  `K* ⊆ K` reducing `L` -/
  invariantCore (K : Submodule 𝕜 (Total W a m)) [K.HasOrthogonalProjection] :
    ∃ (Ks : Submodule 𝕜 (Total W a m)) (_ : Ks.HasOrthogonalProjection),
      (∀ x, x ∈ Ks ↔ ∀ t, S t x ∈ K) ∧ IsReducing (H.wave a m) Ks ∧
      ∀ (M : Submodule 𝕜 (Total W a m)) [M.HasOrthogonalProjection], M ≤ K →
        IsReducing (H.wave a m) M → M ≤ Ks
  /-- the constraint of a reducing subcomplex propagates: closed `Zⁱ ⊆ Wⁱ` with
  `P_{Zⁱ} D(d) ⊆ D(d)` and `d P_{Zⁱ} = P_{Zʲ} d` ([QuennevilleBelair2015], Prop 4.16) -/
  subcomplex (Z : ∀ i, Submodule 𝕜 (W i)) [∀ i, (Z i).HasOrthogonalProjection]
    (hZ : ∀ i j (x : (H.d i j).domain), ∃ hx : (Z i).starProjection (x : W i) ∈ (H.d i j).domain,
      H.d i j ⟨_, hx⟩ = (Z j).starProjection (H.d i j x))
    (t : ℝ) (x : Total W a m) (hx : ∀ i : Fin m, x i ∈ Z (a + (i : ℕ))) (i : Fin m) :
    S t x i ∈ Z (a + (i : ℕ))

/-- **The conclusions of the FEEC theorem for the Hodge wave and heat equations** on the
window. -/
structure DynamicVerdict : Prop where
  /-- the wave equation `ξ' = L ξ` -/
  wave : ∃ S, F.WaveVerdict a m S
  /-- the heat equation `u' = L² u`, with projections bounded in the graph norm in the degrees
  `a, …, a + m - 2` and in `W` in the last degree `a + m - 1` (which has no differential in the
  window), and closed ranges in the window -/
  heat (hπ : ∀ i : Fin m, (i : ℕ) + 1 < m → F.IsGraphBounded (a + (i : ℕ)))
    (hπ' : ∀ i : Fin m, (i : ℕ) + 1 = m → ∃ C : ℝ, ∀ (h : κ)
      (x : (H.d (a + (i : ℕ)) (a + (i : ℕ) + 1)).domain),
        ‖((F.π h).π _ x : W (a + (i : ℕ)))‖ ≤ C * ‖(x : W (a + (i : ℕ)))‖)
    (hcr : ∀ i : Fin m, 0 < (i : ℕ) →
      IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ))))) :
    ∃ S : ℝ → Total W a m →L[𝕜] Total W a m,
    EvolutionVerdict (sq (H.wave a m)) F.l (F.Xh a m) (fun h => F.Lh a m h ^ 2) S

end SubcomplexFamily

end HilbertComplex

/-! ### Differential forms on `ℝⁿ` and the `L²` de Rham complexes -/

variable {n : ℕ}

/-- The index set of the coefficients of a `k`-form on `ℝⁿ`: the `k`-subsets
`s = {s₁ < ⋯ < s_k}` of `Fin n`, `s` indexing `dx_{s₁} ∧ ⋯ ∧ dx_{s_k}` (empty unless
`0 ≤ k ≤ n`). -/
abbrev FormIdx (n : ℕ) (k : ℤ) : Type := {s : Finset (Fin n) // (s.card : ℤ) = k}

/-- `L²(Ω; Λᵏ)`: the square-integrable `k`-forms on `Ω ⊆ ℝⁿ` (Lebesgue measure), the `ℓ²` sum
of a copy of `L²(Ω)` for each coefficient. -/
abbrev L2Form (Ω : Set (Fin n → ℝ)) (k : ℤ) : Type :=
  PiLp 2 fun _ : FormIdx n k => Lp ℝ 2 (volume.restrict Ω)

/-- A **form field** on `ℝⁿ`: at each point, a coefficient for every subset `s` of `Fin n` (the
coefficient of `dx_s`); it is a `k`-form when the coefficients off the `k`-subsets vanish. -/
abbrev FormField (n : ℕ) : Type := (Fin n → ℝ) → Finset (Fin n) → ℝ

/-- The sign `ε(j, s) = (-1)^{#{l ∈ s | l < j}}` of moving `dx_j` to its place in `dx_s`. -/
def sgn (j : Fin n) (s : Finset (Fin n)) : ℝ := (-1) ^ (s.filter fun l => l < j).card

/-- The partial derivative `∂_j f(x)`. -/
def partialDeriv (j : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single j 1)

/-- The **exterior derivative** of a form field, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`. -/
def extDeriv (w : FormField n) : FormField n :=
  fun x s => ∑ j ∈ s, sgn j s * partialDeriv j (fun y => w y (s.erase j)) x

/-- The **formal adjoint** of `d`, the codifferential `δ`,
`(dᵗψ)_s = -Σ_{j ∉ s} ε(j, s) ∂_j ψ_{s ∪ j}`: `∫ ⟨dφ, ψ⟩ = ∫ ⟨φ, dᵗψ⟩` for test forms. -/
def codiff (ψ : FormField n) : FormField n :=
  fun x s => -∑ j ∈ sᶜ, sgn j s * partialDeriv j (fun y => ψ y (insert j s)) x

/-- `f` is a **test function** on `Ω`: smooth, with compact support contained in `Ω`. -/
def IsTestFn (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω

/-- The graph `{(φ, dφ)}` of the exterior derivative on the test `k`-forms `φ ∈ C_c^∞(Ω; Λᵏ)`
(every coefficient a test function), as a subspace of `L²(Ω; Λᵏ) × L²(Ω; Λᵏ⁺¹)`. -/
def testGraph (Ω : Set (Fin n → ℝ)) (k : ℤ) : Submodule ℝ (L2Form Ω k × L2Form Ω (k + 1)) :=
  Submodule.span ℝ {p | ∃ φ : FormField n, (∀ s, IsTestFn Ω fun x => φ x s) ∧
    (∀ s : FormIdx n k, ⇑(p.1 s) =ᵐ[volume.restrict Ω] fun x => φ x s.1) ∧
    ∀ t : FormIdx n (k + 1), ⇑(p.2 t) =ᵐ[volume.restrict Ω] fun x => extDeriv φ x t.1}

/-- The graph `{(ψ, dᵗψ)}` of the formal adjoint on the test `(k + 1)`-forms, as a subspace of
`L²(Ω; Λᵏ⁺¹) × L²(Ω; Λᵏ)`. -/
def codiffGraph (Ω : Set (Fin n → ℝ)) (k : ℤ) : Submodule ℝ (L2Form Ω (k + 1) × L2Form Ω k) :=
  Submodule.span ℝ {p | ∃ ψ : FormField n, (∀ s, IsTestFn Ω fun x => ψ x s) ∧
    (∀ t : FormIdx n (k + 1), ⇑(p.1 t) =ᵐ[volume.restrict Ω] fun x => ψ x t.1) ∧
    ∀ s : FormIdx n k, ⇑(p.2 s) =ᵐ[volume.restrict Ω] fun x => codiff ψ x s.1}

/-- The **minimal exterior derivative** `d̊ : L²(Ω; Λᵏ) → L²(Ω; Λᵏ⁺¹)`, the closure of `d` on
test forms (the closure of the graph is a graph: `d` is closable, its formal adjoint being
densely defined): its domain is `H̊Λᵏ(Ω)` (for Lipschitz `Ω`, the forms of `HΛᵏ(Ω)` with vanishing
tangential trace) ([AFW2010], §4; [Arnold2018], Ch. 6). -/
def dMin (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Form Ω k →ₗ.[ℝ] L2Form Ω (k + 1) :=
  (testGraph Ω k).topologicalClosure.toLinearPMap

/-- The closure of the formal adjoint `dᵗ` on test `(k + 1)`-forms. -/
def codiffMin (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Form Ω (k + 1) →ₗ.[ℝ] L2Form Ω k :=
  (codiffGraph Ω k).topologicalClosure.toLinearPMap

/-- The **weak exterior derivative** `d : L²(Ω; Λᵏ) → L²(Ω; Λᵏ⁺¹)`, the adjoint of the formal
adjoint on test forms: `u ∈ D(d)` iff some `w ∈ L²(Ω; Λᵏ⁺¹)` has `⟪w, ψ⟫ = ⟪u, dᵗψ⟫` for every
test `(k + 1)`-form `ψ`, and then `du = w`. Its domain is `HΛᵏ(Ω)` ([AFW2010], §4;
[Arnold2018], Ch. 6). -/
def dMax (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Form Ω k →ₗ.[ℝ] L2Form Ω (k + 1) :=
  (codiffMin Ω k)†

/-! ### Polynomial differential forms ([AFW2006], §3) -/

/-- **Polynomial differential forms** on `ℝⁿ` in coordinates: a polynomial coefficient `ω_s` for
every subset `s` of `Fin n`, the form `Σ_s ω_s dx_s`. -/
abbrev PolyForm (n : ℕ) : Type := Finset (Fin n) → MvPolynomial (Fin n) ℝ

/-- `P_rΛᵏ`: the polynomial `k`-forms (`ω_s = 0` unless `#s = k`) with coefficients of degree at
most `r`. -/
def polyForm (r k : ℕ) : Submodule ℝ (PolyForm n) :=
  Submodule.pi Set.univ fun s =>
    if s.card = k then MvPolynomial.restrictTotalDegree (Fin n) ℝ r else ⊥

/-- `H_rΛᵏ`: the polynomial `k`-forms with coefficients homogeneous of degree `r`. -/
def homForm (r k : ℕ) : Submodule ℝ (PolyForm n) :=
  Submodule.pi Set.univ fun s =>
    if s.card = k then MvPolynomial.homogeneousSubmodule (Fin n) ℝ r else ⊥

/-- The **Koszul differential** `κ`, the contraction with the position vector field `x`:
`(κω)_s = Σ_{j ∉ s} ε(j, s) x_j ω_{s ∪ j}`. -/
def koszul : PolyForm n →ₗ[ℝ] PolyForm n :=
  LinearMap.pi fun s => ∑ j ∈ sᶜ,
    sgn j s • (LinearMap.mulLeft ℝ (MvPolynomial.X j) ∘ₗ LinearMap.proj (insert j s))

/-- `P_r⁻Λᵏ = P_{r-1}Λᵏ + κ H_{r-1}Λ^{k+1}`, the trimmed polynomial `k`-forms (`r ≥ 1`), and
`P_0⁻Λᵏ = 0` ([AFW2006], §3.3). -/
def polyFormMinus : ℕ → ℕ → Submodule ℝ (PolyForm n)
  | 0, _ => ⊥
  | r + 1, k => polyForm r k ⊔ (homForm r (k + 1)).map koszul

/-- The **evaluation** of a polynomial form: the form field `x ↦ (ω_s(x))_s`. -/
def evalForm : PolyForm n →ₗ[ℝ] FormField n :=
  LinearMap.pi fun x => LinearMap.pi fun s =>
    (MvPolynomial.aeval x).toLinearMap ∘ₗ LinearMap.proj s

/-- **An admissible sequence** of polynomial families ([AFW2006], §5; [AFW2010], §5.2): in every
form degree `k` the full space `P_{r_k}Λᵏ` (`full k = true`) or the trimmed space `P_{r_k}⁻Λᵏ`,
`r_k ≥ 1`, followed in degree `k + 1` by `P_{r_k}⁻Λᵏ⁺¹` or by `P_{r_k - 1}Λᵏ⁺¹`. (The piecewise
constants `P_0Λⁿ` are represented by the equal space `P_1⁻Λⁿ`; the spaces of degree `k > n`
are `0`.) -/
structure PolySeq where
  /-- `P_{r_k}Λᵏ` (`true`) or `P_{r_k}⁻Λᵏ` (`false`) in degree `k` -/
  full : ℕ → Bool
  /-- the polynomial degree `r_k` -/
  deg : ℕ → ℕ
  one_le_deg : ∀ k, 1 ≤ deg k
  transition : ∀ k, (full (k + 1) = false ∧ deg (k + 1) = deg k) ∨
    (full (k + 1) = true ∧ deg (k + 1) + 1 = deg k)

namespace PolySeq

variable (S : PolySeq)

/-- The space `P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` of form fields on `ℝⁿ` of the sequence in degree `k`. -/
def space (n k : ℕ) : Submodule ℝ (FormField n) :=
  (if S.full k then polyForm (n := n) (S.deg k) k else polyFormMinus (S.deg k) k).map evalForm

/-- `S` **reproduces polynomial forms of degree `s`** in the form degrees `j` and `j + 1`:
`P_sΛʲ ⊆ S_j` and `P_sΛʲ⁺¹ ⊆ S_{j+1}` (vacuous for `j < 0`). -/
def PolyOrderAt (n s : ℕ) (j : ℤ) : Prop :=
  ∀ k : ℕ, (k : ℤ) = j → (polyForm (n := n) s k).map evalForm ≤ S.space n k ∧
    (polyForm (n := n) s (k + 1)).map evalForm ≤ S.space n (k + 1)

end PolySeq

/-! ### Simplicial meshes -/

/-- The vertex set `{v₀, …, v_k}` of a simplex. -/
def vertexSet {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) : Finset (Fin n → ℝ) :=
  Finset.univ.image T.points

/-- A **conforming simplicial mesh** of `closure domain ⊆ ℝⁿ`: a finite set of `n`-simplices
whose closed simplices cover `closure domain`, have pairwise disjoint interiors, and meet face to
face (the intersection of two closed simplices is the convex hull of their common vertices). -/
structure SimplicialMesh (n : ℕ) where
  /-- the `n`-simplices -/
  simplices : Finset (Affine.Simplex ℝ (Fin n → ℝ) n)
  /-- the meshed set `Ω`; the mesh covers its closure -/
  domain : Set (Fin n → ℝ)
  biUnion_closedInterior : ⋃ T ∈ simplices, T.closedInterior = closure domain
  pairwise_disjoint_interior :
    (simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)).Pairwise fun T T' =>
      Disjoint (interior T.closedInterior) (interior T'.closedInterior)
  inter_closedInterior : ∀ T ∈ simplices, ∀ T' ∈ simplices,
    T.closedInterior ∩ T'.closedInterior =
      convexHull ℝ ((vertexSet T : Set (Fin n → ℝ)) ∩ vertexSet T')

/-- `h_T`: the diameter of the closed simplex `T`. -/
def diam {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) : ℝ := Metric.diam T.closedInterior

/-- The **mesh size** `h = max_T h_T`. -/
def meshSize (M : SimplicialMesh n) : ℝ :=
  ⨆ T : M.simplices, diam (T : Affine.Simplex ℝ (Fin n → ℝ) n)

/-- The mesh is **shape regular** with constant `σ` ([Ciarlet2002], §3.1): every simplex `T`
contains a ball `B(x, ρ)` with `h_T ≤ σ ρ`, that is `h_T / ρ_T ≤ σ` for the inradius `ρ_T` (the
largest radius of a ball in `T`). Balls and `h_T` are those of the sup norm (Conventions). -/
def IsShapeRegular (M : SimplicialMesh n) (σ : ℝ) : Prop :=
  ∀ T ∈ M.simplices, ∃ x ρ, 0 < ρ ∧ Metric.ball x ρ ⊆ T.closedInterior ∧ diam T ≤ σ * ρ

/-- The mesh is **quasi-uniform** with constant `q`: `q h ≤ h_T` for every simplex. -/
def IsQuasiUniform (M : SimplicialMesh n) (q : ℝ) : Prop :=
  ∀ T ∈ M.simplices, q * meshSize M ≤ diam T

/-- `M_N` is a **shape-regular, quasi-uniform family of meshes of `Ω`** with mesh size `h_N → 0`:
meshes of `Ω`, shape regular and quasi-uniform with constants independent of `N`. -/
def IsMeshFamily (Ω : Set (Fin n → ℝ)) (M : ℕ → SimplicialMesh n) : Prop :=
  (∀ N, (M N).domain = Ω) ∧
    (∃ σ q : ℝ, 0 < q ∧ ∀ N, IsShapeRegular (M N) σ ∧ IsQuasiUniform (M N) q) ∧
    (∀ N, 0 < meshSize (M N)) ∧ Tendsto (fun N => meshSize (M N)) atTop (𝓝 0)

/-- `Ω` is a **bounded open domain star-shaped with respect to a ball** `B(x₀, s₀)`: the segment
from every point of the ball to every point of `Ω` lies in `Ω`. -/
def IsStarShapedBall (Ω : Set (Fin n → ℝ)) : Prop :=
  IsOpen Ω ∧ Bornology.IsBounded Ω ∧ ∃ x₀ : Fin n → ℝ, ∃ s₀ : ℝ, 0 < s₀ ∧
    ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ Ω

/-- The **parallelepiped** `A (0, 1)ⁿ + b` (an open box when `A` is diagonal). -/
def parallelepiped (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Set (Fin n → ℝ) :=
  (fun x => A.mulVec x + b) '' Set.univ.pi fun _ => Set.Ioo 0 1

/-! ### The finite element spaces -/

/-- The value `α(v₁, …, v_k) = Σ_{#s = k} α_s det (v_l(s_i))_{i,l}` of the `k`-covector `α` on
the vectors `v₁, …, v_k`. -/
def covEval {k : ℕ} (α : Finset (Fin n) → ℝ) (v : Fin k → Fin n → ℝ) : ℝ :=
  ∑ s : Finset (Fin n), if h : s.card = k then
    α s * (Matrix.of fun i l => v l (s.orderEmbOfFin h i)).det else 0

/-- The `k`-covectors `α`, `β` have the **same tangential trace** on the face spanned by the
points `g`: they agree on all `k`-tuples of vectors tangent to the face. -/
def TraceEq (g : Finset (Fin n → ℝ)) (k : ℕ) (α β : Finset (Fin n) → ℝ) : Prop :=
  ∀ v : Fin k → Fin n → ℝ, (∀ l, v l ∈ vectorSpan ℝ (g : Set (Fin n → ℝ))) →
    covEval α v = covEval β v

/-- `p = (p_T)_T` are **finite element pieces** of `u ∈ L²(Ω; Λᵏ)` on the mesh `M` for the
sequence `S`: on every simplex `T`, `u` is (almost everywhere) the polynomial form `p_T ∈ S_k`,
and the tangential traces of `p_T` and `p_{T'}` agree on the common face of any two simplices. -/
def IsFemPieces (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (S : PolySeq) (k : ℤ)
    (u : L2Form Ω k) (p : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n) : Prop :=
  (∀ T ∈ M.simplices, p T ∈ S.space n k.toNat) ∧
    (∀ T ∈ M.simplices, ∀ s : FormIdx n k,
      ⇑(u s) =ᵐ[volume.restrict (Ω ∩ T.closedInterior)] fun x => p T x s.1) ∧
    ∀ T ∈ M.simplices, ∀ T' ∈ M.simplices,
      ∀ x ∈ convexHull ℝ ((vertexSet T ∩ vertexSet T' : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)),
        TraceEq (vertexSet T ∩ vertexSet T') k.toNat (p T x) (p T' x)

/-- **The finite element space** `S_k(M) ⊆ L²(Ω; Λᵏ)` of the admissible sequence `S` on the mesh
`M` ([AFW2006], §5; [Arnold2018], Ch. 7): the forms that are on every simplex a polynomial form
of `S_k`, with single-valued tangential traces on the faces of the mesh. -/
def femSpace (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (S : PolySeq) (k : ℤ) :
    Set (L2Form Ω k) :=
  {u | ∃ p, IsFemPieces Ω M S k u p}

/-- **The finite element space with vanishing boundary traces** `S̊_k(M)`: the forms of
`S_k(M)` whose tangential traces vanish on the boundary facets (the facets of a single simplex of
the mesh). -/
def femSpaceMin (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (S : PolySeq) (k : ℤ) :
    Set (L2Form Ω k) :=
  {u | ∃ p, IsFemPieces Ω M S k u p ∧ ∀ T ∈ M.simplices, ∀ F ⊆ vertexSet T, F.card = n →
    (∀ T' ∈ M.simplices, F ⊆ vertexSet T' → T' = T) →
      ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), TraceEq F k.toNat (p T x) 0}

/-! ### Smooth forms -/

/-- `x ∈ L²(Ω; Λʲ)` is (almost everywhere) a `C^{s+2}` form `w` of degree `j` whose
`(s+1)`-st derivative and that of `dw` are bounded by `L` on `cl Ω` (true in negative degrees):
the regularity class of the order `h^{s+1}`. -/
def IsCsForm (Ω : Set (Fin n → ℝ)) (s : ℕ) (j : ℤ) (L : ℝ) (x : L2Form Ω j) : Prop :=
  j < 0 ∨ ∃ w : FormField n, ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w ∧
    (∀ y (t : Finset (Fin n)), (t.card : ℤ) ≠ j → w y t = 0) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L) ∧
    ∀ t : FormIdx n j, ⇑(x t) =ᵐ[volume.restrict Ω] fun y => w y t.1

/-- `IsCsForm` for a form `w` vanishing outside `Ω` (the regularity class of `H̊Λ(Ω)`): `w` is
`C^{s+2}` on `ℝⁿ`, so all its derivatives of order at most `s + 2` vanish on `∂Ω`, a class
smaller than the forms of `H̊Λ(Ω)` of Sobolev regularity `s + 1`. -/
def IsCsFormMin (Ω : Set (Fin n → ℝ)) (s : ℕ) (j : ℤ) (L : ℝ) (x : L2Form Ω j) : Prop :=
  j < 0 ∨ ∃ w : FormField n, ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w ∧
    (∀ y (t : Finset (Fin n)), (t.card : ℤ) ≠ j → w y t = 0) ∧ (∀ y ∉ Ω, w y = 0) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L) ∧
    ∀ t : FormIdx n j, ⇑(x t) =ᵐ[volume.restrict Ω] fun y => w y t.1

/-- `x ∈ L²(Ω; Λʲ)` **lies in `Hᵐ(Ω; Λʲ)` with norm at most `L`**, for `Hᵐ(Ω) = Hᵐ(ℝⁿ)|_Ω` (the
restriction definition, weak derivatives as in [Evans2010], §5.2; on Lipschitz domains, by
Stein's extension theorem, the space of weak derivatives in `L²(Ω)` with an equivalent norm): each
coefficient is the restriction of a function `D t []` on `ℝⁿ` with weak derivatives `D t l` in
`L²(ℝⁿ)` along the words `l` of length at most `m` (`∫ D t [] ∂_{l₁} ⋯ ∂_{l_p} φ =
(-1)^p ∫ D t l φ` for test functions `φ`), with `Σ_t Σ_{|l| ≤ m} ‖D t l‖² ≤ L²` (norm at most
`|L|`; a sum over words: a derivative of multi-index `α` is counted `|α|!/α!` times). -/
def IsSobolevForm (Ω : Set (Fin n → ℝ)) (m : ℕ) (j : ℤ) (L : ℝ) (x : L2Form Ω j) : Prop :=
  ∃ D : FormIdx n j → List (Fin n) → (Fin n → ℝ) → ℝ,
    (∀ t l, l.length ≤ m → MemLp (D t l) 2 volume ∧ ∀ φ, IsTestFn univ φ →
      ∫ y, D t [] y * l.foldr partialDeriv φ y = (-1) ^ l.length * ∫ y, D t l y * φ y) ∧
    ∑ t, ∑ p ∈ Finset.range (m + 1), ∑ l : Fin p → Fin n, ∫ y, D t (List.ofFn l) y ^ 2 ≤ L ^ 2 ∧
    ∀ t, ⇑(x t) =ᵐ[volume.restrict Ω] D t []

/-- The cube `(0, ½)ⁿ` (half a period of the torus `ℝⁿ/ℤⁿ` of the proof's Fourier series). -/
def cube (n : ℕ) : Set (Fin n → ℝ) := univ.pi fun _ => Ioo 0 (1 / 2)

/-! ### Maxwell's equations in vector proxies (`n = 3`) -/

/-- `L²(Ω; ℝ^ι)`: the square-integrable fields on `Ω ⊆ ℝ³` with components indexed by `ι`
(`Fin 1`: scalar fields, `Fin 3`: vector fields), an `ℓ²` sum of copies of `L²(Ω)`. -/
abbrev L2Field (Ω : Set (Fin 3 → ℝ)) (ι : Type) [Fintype ι] : Type :=
  PiLp 2 fun _ : ι => Lp ℝ 2 (volume.restrict Ω)

/-- The **weak realization** `A : L²(Ω; ℝ^ι) → L²(Ω; ℝ^κ)` of the first-order operator with
formal adjoint `Aᵗ` (as `dMax`): the adjoint of the closure of `Aᵗ` on test fields, so that
`u ∈ D(A)` iff some `w` has `⟪w, ψ⟫ = ⟪u, Aᵗψ⟫` for every test field `ψ`, and then `A u = w`. -/
def weakOp (Ω : Set (Fin 3 → ℝ)) {ι κ : Type} [Fintype ι] [Fintype κ]
    (At : ((Fin 3 → ℝ) → κ → ℝ) → (Fin 3 → ℝ) → ι → ℝ) : L2Field Ω ι →ₗ.[ℝ] L2Field Ω κ :=
  (Submodule.span ℝ {p : L2Field Ω κ × L2Field Ω ι | ∃ ψ : (Fin 3 → ℝ) → κ → ℝ,
    (∀ j, IsTestFn Ω fun x => ψ x j) ∧ (∀ j, ⇑(p.1 j) =ᵐ[volume.restrict Ω] fun x => ψ x j) ∧
    ∀ i, ⇑(p.2 i) =ᵐ[volume.restrict Ω] fun x => At ψ x i}).topologicalClosure.toLinearPMap†

/-- The **weak gradient** `grad : H¹(Ω) ⊆ L²(Ω) → L²(Ω; ℝ³)` (formal adjoint `-div`). -/
def grad (Ω : Set (Fin 3 → ℝ)) : L2Field Ω (Fin 1) →ₗ.[ℝ] L2Field Ω (Fin 3) :=
  weakOp Ω fun ψ x _ => -∑ j, partialDeriv j (fun y => ψ y j) x

/-- The **weak curl** `curl : H(curl, Ω) ⊆ L²(Ω; ℝ³) → L²(Ω; ℝ³)`,
`(curl v)ᵢ = ∂_{i+1} v_{i+2} - ∂_{i+2} v_{i+1}` (indices mod 3; formally self-adjoint). -/
def curl (Ω : Set (Fin 3 → ℝ)) : L2Field Ω (Fin 3) →ₗ.[ℝ] L2Field Ω (Fin 3) :=
  weakOp Ω fun ψ x i =>
    partialDeriv (i + 1) (fun y => ψ y (i + 2)) x - partialDeriv (i + 2) (fun y => ψ y (i + 1)) x

/-- The **weak divergence** `div : H(div, Ω) ⊆ L²(Ω; ℝ³) → L²(Ω)` (formal adjoint `-grad`). -/
def div (Ω : Set (Fin 3 → ℝ)) : L2Field Ω (Fin 3) →ₗ.[ℝ] L2Field Ω (Fin 1) :=
  weakOp Ω fun ψ x j => -partialDeriv j (fun y => ψ y 0) x

/-- The **vector proxy** of a `0`-form: the scalar `f_∅`. -/
def proxy0 {Ω : Set (Fin 3 → ℝ)} (u : L2Form Ω 0) : L2Field Ω (Fin 1) :=
  WithLp.toLp 2 fun _ => u ⟨∅, rfl⟩

/-- The **vector proxy** of a `1`-form `Σⱼ vⱼ dxⱼ`: the vector `v`. -/
def proxy1 {Ω : Set (Fin 3 → ℝ)} (u : L2Form Ω 1) : L2Field Ω (Fin 3) :=
  WithLp.toLp 2 fun j => u ⟨{j}, by simp⟩

/-- The **vector proxy** of a `2`-form `ω`: the vector `(ω₁₂, -ω₀₂, ω₀₁)`. -/
def proxy2 {Ω : Set (Fin 3 → ℝ)} (u : L2Form Ω 2) : L2Field Ω (Fin 3) :=
  WithLp.toLp 2 fun i => (-1 : ℝ) ^ (i : ℕ) • u ⟨Finset.univ.erase i, by simp⟩

/-- `(σ, E, B)` is a **strong solution of Maxwell's equations** on `[0, T]`: `σ' = -grad* E`,
`E' = grad σ - curl* B`, `B' = curl E` for the weak `grad`, `curl` and their adjoints
(`grad* = -div` with `E · n = 0`, `curl* = curl` with `B × n = 0`), the derivatives in `L²`;
`B ∈ L²(Ω; ℝ³)` is the last space of the window `H¹ → H(curl) → L²(Ω; ℝ³)`. -/
def IsMaxwellSolution (Ω : Set (Fin 3 → ℝ)) (T : ℝ) (σ : ℝ → L2Field Ω (Fin 1))
    (E B : ℝ → L2Field Ω (Fin 3)) : Prop :=
  ∀ t ∈ Icc 0 T, ∃ σ' E' B' g c, HasDerivWithinAt σ σ' (Icc 0 T) t ∧
    HasDerivWithinAt E E' (Icc 0 T) t ∧ HasDerivWithinAt B B' (Icc 0 T) t ∧
    (E t, -σ') ∈ (grad Ω)†.graph ∧ (σ t, g) ∈ (grad Ω).graph ∧ (B t, c) ∈ (curl Ω)†.graph ∧
    E' = g - c ∧ (E t, B') ∈ (curl Ω).graph

/-- `(σ, E, B)` is a **semi-discrete (Galerkin) solution of Maxwell's equations** on `[0, T]` in
`V⁰ × V¹ × V²`: `⟪σ', τ⟫ + ⟪E', F⟫ + ⟪B', G⟫ = ⟪grad σ, F⟫ + ⟪curl E, G⟫ - ⟪E, grad τ⟫ -
⟪B, curl F⟫` for all `τ ∈ V⁰`, `F ∈ V¹`, `G ∈ V²`. -/
def IsMaxwellGalerkin (Ω : Set (Fin 3 → ℝ)) (V₀ : Set (L2Field Ω (Fin 1)))
    (V₁ V₂ : Set (L2Field Ω (Fin 3))) (T : ℝ) (σ : ℝ → L2Field Ω (Fin 1))
    (E B : ℝ → L2Field Ω (Fin 3)) : Prop :=
  ∀ t ∈ Icc 0 T, σ t ∈ V₀ ∧ E t ∈ V₁ ∧ B t ∈ V₂ ∧ ∃ σ' E' B', HasDerivWithinAt σ σ' (Icc 0 T) t ∧
    HasDerivWithinAt E E' (Icc 0 T) t ∧ HasDerivWithinAt B B' (Icc 0 T) t ∧
    ∀ τ ∈ V₀, ∀ F ∈ V₁, ∀ G ∈ V₂, ∀ gσ gτ cE cF, (σ t, gσ) ∈ (grad Ω).graph →
      (τ, gτ) ∈ (grad Ω).graph → (E t, cE) ∈ (curl Ω).graph → (F, cF) ∈ (curl Ω).graph →
        ⟪σ', τ⟫_ℝ + ⟪E', F⟫_ℝ + ⟪B', G⟫_ℝ =
          ⟪gσ, F⟫_ℝ + ⟪cE, G⟫_ℝ - ⟪E t, gτ⟫_ℝ - ⟪B t, cF⟫_ℝ

/-! ### The theorems -/

end FEEC
