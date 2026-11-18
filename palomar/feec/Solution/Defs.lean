module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but the compared theorems of
`comparator.json`), compiled against Mathlib alone so
that their elaborated values are those of the challenge. The solution imports this module and the
bridges to `Feec`, and proves the theorems (`Solution.lean`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996]
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Filter Topology Set LinearPMap MeasureTheory

universe u v w

@[expose] public noncomputable section

namespace FEEC

/-! ### Hilbert complexes and families of subcomplexes -/
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
namespace HilbertComplex
variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] {H : HilbertComplex 𝕜 W} {κ : Type*}
/-- The **graph norm** `‖x‖_V = (‖x‖² + ‖d x‖²)^½` on `D(d i j)`. -/
def graphNorm (H : HilbertComplex 𝕜 W) (i j : ℤ) (x : (H.d i j).domain) : ℝ :=
  √(‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2)
/-- A **subcomplex**: subspaces `Vⁱ ⊆ D(d i j)` with `d Vⁱ ⊆ Vʲ`. -/
structure Subcomplex (H : HilbertComplex 𝕜 W) where
  V : ∀ i, Submodule 𝕜 (W i)
  le_domain : ∀ i j, V i ≤ (H.d i j).domain
  mapsTo : ∀ i j (x : W i) (hx : x ∈ V i), (H.d i j ⟨x, le_domain i j hx⟩ : W j) ∈ V j
/-- A **cochain projection** onto `S`: projections `πⁱ : D(dⁱ) → Sⁱ` of the domain complex
commuting with `d`. -/
structure Subcomplex.CochainProjection (S : H.Subcomplex) where
  π : ∀ i, (H.d i (i + 1)).domain →ₗ[𝕜] S.V i
  proj : ∀ i (x : (H.d i (i + 1)).domain), (x : W i) ∈ S.V i → (π i x : W i) = x
  comm : ∀ i (x : (H.d i (i + 1)).domain),
    H.d i (i + 1) ⟨π i x, S.le_domain i (i + 1) (π i x).2⟩ =
      π (i + 1) ⟨H.d i (i + 1) x, H.mapsTo i (i + 1) (i + 1 + 1) x⟩
/-- The distance `E(x) = inf_{v ∈ Vⁱ} ‖x - v‖_V` from `x ∈ D(d i j)` to `Vⁱ` in the graph norm. -/
def Subcomplex.graphDist (S : H.Subcomplex) (i j : ℤ) (x : (H.d i j).domain) : ℝ :=
  ⨅ v : S.V i, H.graphNorm i j (x - ⟨v, S.le_domain i j v.2⟩)
/-- A **family of subcomplexes** of `H` along the filter `l` (the refinement `h → 0`):
finite-dimensional subcomplexes `Vₕ` with cochain projections `πₕ` (no bound and no
approximation property: these are hypotheses of the theorems). -/
structure SubcomplexFamily (H : HilbertComplex 𝕜 W) (κ : Type*) where
  l : Filter κ
  V : κ → H.Subcomplex
  [finiteDimensional : ∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
  π : ∀ h, (V h).CochainProjection
attribute [instance] SubcomplexFamily.finiteDimensional
/-- The cochain projections of `F` are **bounded in the graph norm by `C`** in degree `i`,
uniformly in `h`: `‖πₕ x‖_V ≤ C ‖x‖_V` on `D(d i (i + 1))`. -/
def SubcomplexFamily.IsGraphBoundedBy (F : H.SubcomplexFamily κ) (i : ℤ) (C : ℝ) : Prop :=
  ∀ (h : κ) (x : (H.d i (i + 1)).domain),
    H.graphNorm i (i + 1) ⟨(F.π h).π i x, (F.V h).le_domain i (i + 1) ((F.π h).π i x).2⟩ ≤
      C * H.graphNorm i (i + 1) x
/-- The cochain projections of `F` are **bounded in the graph norm** in degree `i`, uniformly in
`h`: bounded by some `C`. -/
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
  meshSize : κ → ℝ
  meshSize_nonneg : ∀ h, 0 ≤ meshSize h
  tendsto_meshSize : Tendsto meshSize F.l (𝓝 0)
  /-- `Reg s i L x`: `x ∈ Wⁱ` is `s`-regular with bound `L` -/
  Reg : ρ → ∀ i, ℝ → W i → Prop
  ord : ρ → ℝ
  B : ρ → ℤ → ℝ
  jackson : ∀ s h i {L : ℝ} (x : W i), 0 ≤ L → Reg s i L x → ∃ v, ∃ hv : v ∈ (F.V h).V i,
    ‖x - v‖ ≤ B s i * (L * meshSize h ^ ord s) ∧ ∀ j (hx : x ∈ (H.d i j).domain),
      ‖H.d i j ⟨x - v, Submodule.sub_mem _ hx ((F.V h).le_domain i j hv)⟩‖ ≤
        B s i * (L * meshSize h ^ ord s)
end HilbertComplex
-- palomar-shared-end: HilbertComplex
variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
/-- The kernel of a closed operator is closed. -/
theorem isClosed_ker {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [Module 𝕜 E]
    [Module 𝕜 F] {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) : IsClosed (T.ker : Set E) := by
  convert hT.preimage (continuous_id.prodMk continuous_const :
    Continuous fun x : E => (x, (0 : F))) using 1
  ext x
  exact mem_ker_iff.trans ((exists_congr fun _ => and_congr_left' eq_comm).trans
    (mem_graph_iff T (x := (id x, (0 : F)))).symm)

section Mixed
variable {E₀ E₁ E₂ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  (d₀ : E₀ →ₗ.[𝕜] E₁) (d₁ : E₁ →ₗ.[𝕜] E₂)
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

/-! ### Evolutions and time schemes -/
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

section Evolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {κ : Type*}
/-- The square `A²` on `D(A²) = {x ∈ D(A) | A x ∈ D(A)}`. -/
def sq (A : E →ₗ.[𝕜] E) : E →ₗ.[𝕜] E :=
  A.comp (A.domRestrict ((A.domain.comap A.toFun).map A.domain.subtype)) fun x => by
    obtain ⟨y, hy, hyx⟩ := x.2.1
    exact (congrArg (A · ∈ A.domain) (Subtype.ext hyx.symm : (⟨x, x.2.2⟩ : A.domain) = y)).mpr hy

variable [NormedSpace ℝ E]
/-- The semidiscrete evolution `exp(t B)`. -/
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

/-- The total space `Wᵃ ⊕ ⋯ ⊕ W^{a+m-1}` of a window (an `ℓ²` sum). -/
abbrev Total (W : ℤ → Type*) (a : ℤ) (m : ℕ) : Type _ := PiLp 2 fun i : Fin m => W (a + (i : ℕ))

namespace HilbertComplex
/-! ### Cohomology and harmonic forms -/
variable (H : HilbertComplex 𝕜 W)
/-- The cycles `𝔷ⁱ = N(d i (i + 1))`. -/
def cycles (i : ℤ) : Submodule 𝕜 (W i) := (H.d i (i + 1)).ker
/-- The boundaries `𝔅ⁱ = R(d (i - 1) i)`. -/
def boundaries (i : ℤ) : Submodule 𝕜 (W i) := LinearMap.range (H.d (i - 1) i).toFun
/-- The harmonic forms `ℌⁱ = 𝔷ⁱ ∩ N(d (i - 1) i)*`. -/
def harmonic (i : ℤ) : Submodule 𝕜 (W i) := H.cycles i ⊓ (H.d (i - 1) i)†.ker
/-- The cohomology `Hⁱ = 𝔷ⁱ / 𝔅ⁱ`. -/
abbrev cohomology (i : ℤ) : Type _ := H.cycles i ⧸ (H.boundaries i).comap (H.cycles i).subtype

theorem cycles_le_domain (i : ℤ) : H.cycles i ≤ (H.d i (i + 1)).domain := ker_le_domain
theorem harmonic_le_domain (i : ℤ) : H.harmonic i ≤ (H.d i (i + 1)).domain :=
  inf_le_left.trans (H.cycles_le_domain i)
/-- `𝔅ⁱ ⊆ 𝔷ⁱ ⊆ D(dⁱ)`, and `𝔷ⁱ` is closed. -/
theorem topologicalClosure_boundaries_le_domain (i : ℤ) :
    (H.boundaries i).topologicalClosure ≤ (H.d i (i + 1)).domain := by
  refine (Submodule.topologicalClosure_minimal _ ?_ (isClosed_ker (H.closed i (i + 1)))).trans
    ker_le_domain
  rintro _ ⟨x, rfl⟩
  exact mem_ker_iff.2 ⟨⟨_, H.mapsTo (i - 1) i (i + 1) x⟩, rfl, H.d_comp_d (i - 1) i (i + 1) x⟩
/-- The harmonic forms are closed, so `P_ℌ`, the orthogonal projection onto them, exists. -/
instance instHasOrthogonalProjectionHarmonic (i : ℤ) : (H.harmonic i).HasOrthogonalProjection :=
  have hc : IsClosed (H.harmonic i : Set (W i)) :=
    (isClosed_ker (H.closed i (i + 1))).inter (isClosed_ker (adjoint_isClosed (H.dense (i - 1) i)))
  have : CompleteSpace (H.harmonic i) := hc.completeSpace_coe
  inferInstance

/-- The mixed space `D(dʲ⁻¹) × D(dʲ) × Wʲ` of the Hodge Laplacian in degree `j`. -/
abbrev Mixed (j : ℤ) : Type _ := MixedSpace (H.d (j - 1) j) (H.d j (j + 1))
/-- The space `D(dʲ⁻¹) × D(dʲ) × ℌʲ` of the exact mixed problem in degree `j`. -/
def mixedSpace (j : ℤ) : Submodule 𝕜 (H.Mixed j) := galerkin _ _ ⊤ ⊤ (H.harmonic j)
/-- The norm `‖σ‖_V + ‖u‖_V + ‖p‖` of `(σ, u, p) ∈ Vʲ⁻¹ × Vʲ × Wʲ`. -/
def mixedNorm {j : ℤ} (x : H.Mixed j) : ℝ :=
  H.graphNorm (j - 1) j x.1 + H.graphNorm j (j + 1) x.2.1 + ‖x.2.2‖

namespace Subcomplex
variable {H} (S : H.Subcomplex)
/-- The discrete cycles `𝔷ₕⁱ = Vⁱ ∩ 𝔷ⁱ`. -/
def cycles (i : ℤ) : Submodule 𝕜 (W i) := S.V i ⊓ H.cycles i
/-- The discrete boundaries `𝔅ₕⁱ = d Vⁱ⁻¹`. -/
def boundaries (i : ℤ) : Submodule 𝕜 (W i) :=
  LinearMap.range ((H.d (i - 1) i).toFun ∘ₗ Submodule.inclusion (S.le_domain (i - 1) i))
/-- The discrete harmonic forms `ℌₕⁱ = 𝔷ₕⁱ ∩ (𝔅ₕⁱ)ᗮ`. -/
def harmonic (i : ℤ) : Submodule 𝕜 (W i) := S.cycles i ⊓ (S.boundaries i)ᗮ
/-- The discrete cohomology `Hⁱ(V) = 𝔷ₕⁱ / 𝔅ₕⁱ`. -/
abbrev cohomology (i : ℤ) : Type _ := S.cycles i ⧸ (S.boundaries i).comap (S.cycles i).subtype
/-- The map `Hⁱ(V) → Hⁱ` induced by the inclusion `V ⊆ W`. -/
def cohomologyIncl (i : ℤ) : S.cohomology i →ₗ[𝕜] H.cohomology i :=
  Submodule.mapQ _ _ (Submodule.inclusion inf_le_right) fun x hx => by
    obtain ⟨y, hy⟩ := hx
    exact ⟨Submodule.inclusion (S.le_domain (i - 1) i) y, hy⟩
/-- The Galerkin space `Vʲ⁻¹ × Vʲ × ℌₕʲ` of the discrete mixed problem in degree `j`. -/
def mixedSpace (j : ℤ) : Submodule 𝕜 (H.Mixed j) :=
  galerkin _ _ (S.V (j - 1)) (S.V j) (S.harmonic j)
/-- The map `Hⁱ → Hⁱ(V)`, `[z] ↦ [π z]`, induced by the cochain projection. -/
def CochainProjection.cohomologyMap {S : H.Subcomplex} (P : S.CochainProjection) (i : ℤ) :
    H.cohomology i →ₗ[𝕜] S.cohomology i :=
  Submodule.mapQ _ _ (LinearMap.codRestrict (S.cycles i)
    ((S.V i).subtype ∘ₗ P.π i ∘ₗ Submodule.inclusion (H.cycles_le_domain i)) fun z => by
      refine ⟨(P.π i _).2, mem_ker_iff.2 ⟨⟨_, S.le_domain i (i + 1) (P.π i _).2⟩, rfl, ?_⟩⟩
      have h0 : (⟨H.d i (i + 1) (Submodule.inclusion (H.cycles_le_domain i) z),
          H.mapsTo i (i + 1) (i + 1 + 1) _⟩ : (H.d (i + 1) (i + 1 + 1)).domain) = 0 :=
        Subtype.ext ((coe_mem_ker_iff (x := Submodule.inclusion (H.cycles_le_domain i) z)).1 z.2)
      rw [P.comm, h0, _root_.map_zero, ZeroMemClass.coe_zero]) fun z hz => by
    obtain ⟨w, hw⟩ := hz
    have key : ∀ k l (_ : k + 1 = l) (x : (H.d k l).domain), ∃ y : S.V k,
        H.d k l ⟨y, S.le_domain k l y.2⟩ = P.π l ⟨H.d k l x, H.mapsTo k l (l + 1) x⟩ := by
      rintro k _ rfl x; exact ⟨P.π k x, P.comm k x⟩
    obtain ⟨y, hy⟩ := key _ _ (sub_add_cancel i 1) w
    exact ⟨y, hy.trans (congrArg (fun x => (P.π i x : W i)) (Subtype.ext hw))⟩
/-- The error `‖q - π q‖` of `π` at `q ∈ ℌʲ`. -/
def CochainProjection.harmonicError {S : H.Subcomplex} (P : S.CochainProjection) {j : ℤ}
    (q : H.harmonic j) : ℝ :=
  ‖(q : W j) - P.π j ⟨q, H.harmonic_le_domain j q.2⟩‖
/-- The **harmonic gap** `μ = sup_{q ∈ ℌʲ, ‖q‖ ≤ 1} ‖q - π q‖`. -/
def CochainProjection.harmonicGap {S : H.Subcomplex} (P : S.CochainProjection) (j : ℤ) : ℝ :=
  ⨆ q : {q : H.harmonic j // ‖(q : W j)‖ ≤ 1}, P.harmonicError q.1

end Subcomplex

/-! ### The static theory -/
variable {H} {κ : Type*}
variable (H) in
/-- The **Poincaré inequality** `‖v‖_V ≤ c ‖d v‖` on `Vⁱ ⊥ 𝔷ⁱ` with constant `c`; some `c` exists
iff the range `𝔅ⁱ⁺¹` of `dⁱ` is closed. -/
def PoincareBy (i : ℤ) (c : ℝ) : Prop :=
  ∀ v : (H.d i (i + 1)).domain, (v : W i) ∈ (H.cycles i)ᗮ →
    H.graphNorm i (i + 1) v ≤ c * ‖H.d i (i + 1) v‖
/-- The **discrete Poincaré inequality** `‖v‖_V ≤ c ‖d v‖` on `Vⁱ ⊥ 𝔷ₕⁱ` with constant `c`. -/
def Subcomplex.PoincareBy (S : H.Subcomplex) (i : ℤ) (c : ℝ) : Prop :=
  ∀ (v : W i) (hv : v ∈ S.V i), (∀ z ∈ S.cycles i, ⟪z, v⟫_𝕜 = 0) →
    H.graphNorm i (i + 1) ⟨v, S.le_domain i (i + 1) hv⟩ ≤
      c * ‖H.d i (i + 1) ⟨v, S.le_domain i (i + 1) hv⟩‖
/-- The **harmonic bound** `‖q‖ ≤ c ‖P_ℌ q‖` on the discrete harmonic forms `ℌₕⁱ` with constant
`c` (on cycles the graph norm is the norm of `W`). -/
def Subcomplex.HarmonicBoundBy (S : H.Subcomplex) (i : ℤ) (c : ℝ) : Prop :=
  ∀ q ∈ S.harmonic i, ‖q‖ ≤ c * ‖(H.harmonic i).starProjection q‖
/-- **The conclusions of the static FEEC theorem** in degree `j` for `F`, with the constant `C`
(independent of `h`) in every bound. -/
structure SubcomplexFamily.StaticVerdict (F : H.SubcomplexFamily κ) (j : ℤ) (C : ℝ) : Prop where
  /-- the gap from `ℌʲ` to `ℌₕʲ`: `dist(q, ℌₕʲ) ≤ ‖q - πₕ q‖` -/
  harmonicDist (h : κ) (q : H.harmonic j) :
    Metric.infDist (q : W j) ((F.V h).harmonic j) ≤ (F.π h).harmonicError q
  /-- the gap from `ℌₕʲ` to `ℌʲ`: `‖q - P_ℌ q‖ ≤ ‖P_ℌ q - πₕ P_ℌ q‖` -/
  discreteHarmonicDist (h : κ) (q : W j) (hq : q ∈ (F.V h).harmonic j) :
    ‖q - (H.harmonic j).starProjection q‖ ≤
      (F.π h).harmonicError ⟨_, Submodule.starProjection_apply_mem _ q⟩
  /-- `πₕ` induces a left inverse of the map induced by the inclusion -/
  cohomologyMap_comp_incl (h : κ) :
    (F.π h).cohomologyMap j ∘ₗ (F.V h).cohomologyIncl j = LinearMap.id
  /-- where `‖q - πₕ q‖ < ‖q‖` on `ℌʲ \ 0`, both are isomorphisms `Hʲ ≅ Hʲ(Vₕ)` -/
  cohomology_of_lt (h : κ) (hgap : ∀ q : H.harmonic j, q ≠ 0 → (F.π h).harmonicError q < ‖q‖) :
    Function.Bijective ((F.π h).cohomologyMap j) ∧ Function.Bijective ((F.V h).cohomologyIncl j)
  /-- where `F` approximates in degree `j` (`ℌʲ` finite-dimensional), `μₕ → 0` and eventually both
  maps are isomorphisms -/
  cohomology (ha : F.Approximates j) [FiniteDimensional 𝕜 (H.harmonic j)] :
    Tendsto (fun h => (F.π h).harmonicGap j) F.l (𝓝 0) ∧ ∀ᶠ h in F.l,
      Function.Bijective ((F.π h).cohomologyMap j) ∧ Function.Bijective ((F.V h).cohomologyIncl j)
  /-- the uniform discrete Poincaré inequality `‖v‖_V ≤ C ‖d v‖` on `Vₕʲ ⊥ 𝔷ₕʲ` -/
  poincare (h : κ) : (F.V h).PoincareBy j C
  /-- the mixed problem and its Galerkin discretizations are uniquely solvable -/
  existsUnique (f : W j) : (∃! x, IsMixedSolution (H.mixedSpace j) f x) ∧
    ∀ h, ∃! x, IsMixedSolution ((F.V h).mixedSpace j) f x
  /-- the uniform inf-sup condition: each `x ∈ Vₕʲ⁻¹ × Vₕʲ × ℌₕʲ` has `y` there, `‖y‖ ≤ ‖x‖`,
  `‖x‖² ≤ C |B(x; y)|` -/
  infSup (h : κ) : ∀ x ∈ (F.V h).mixedSpace j, ∃ y ∈ (F.V h).mixedSpace j,
    H.mixedNorm y ≤ H.mixedNorm x ∧ H.mixedNorm x ^ 2 ≤ C * ‖mixedForm _ _ x y‖
  /-- the discrete solutions are stable: `‖σₕ‖_V + ‖uₕ‖_V + ‖pₕ‖ ≤ C ‖f‖` -/
  stable (h : κ) {f x} (hx : IsMixedSolution ((F.V h).mixedSpace j) f x) : H.mixedNorm x ≤ C * ‖f‖
  /-- they are quasi-optimal in the graph norm, `P_𝔅` the orthogonal projection onto `cl 𝔅ʲ` -/
  quasiOptimal {f x} (hs : IsMixedSolution (H.mixedSpace j) f x) (h : κ) {xh}
    (hsh : IsMixedSolution ((F.V h).mixedSpace j) f xh) :
    H.mixedNorm (x - xh) ≤ C * ((F.V h).graphDist (j - 1) j x.1 +
      (F.V h).graphDist j (j + 1) x.2.1 +
      (F.V h).graphDist j (j + 1) ⟨x.2.2, H.harmonic_le_domain j hs.1.2.2⟩ +
      (F.π h).harmonicGap j * (F.V h).graphDist j (j + 1)
        ⟨_, H.topologicalClosure_boundaries_le_domain j
          (Submodule.starProjection_apply_mem (H.boundaries j).topologicalClosure x.2.1)⟩)
  /-- where `F` approximates in degrees `j - 1` and `j`, they converge in the graph norm -/
  converges (ha : F.Approximates (j - 1)) (ha' : F.Approximates j) {f x}
    (hs : IsMixedSolution (H.mixedSpace j) f x) {xh : κ → H.Mixed j}
    (hsh : ∀ h, IsMixedSolution ((F.V h).mixedSpace j) f (xh h)) :
    Tendsto (fun h => H.mixedNorm (x - xh h)) F.l (𝓝 0)

/-! ### Windows -/
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
/-- The harmonic forms `ℌ = N(𝐝) ∩ N(𝐝*)` of the window. -/
def totalHarmonic : Submodule 𝕜 (Total W a m) := (H.totalD a m).ker ⊓ (H.totalD a m)†.ker
/-- The space `D(𝐝) × D(𝐝) × ℌ` of the mixed Hodge Laplacian of the window. -/
def totalMixedSpace : Submodule 𝕜 (MixedSpace (H.totalD a m) (H.totalD a m)) :=
  galerkin _ _ ⊤ ⊤ (H.totalHarmonic a m)

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
  ⨅ w : F.Xh a m h, ‖(y : Total W a m) - w‖ + ‖H.totalD a m y - H.totalD a m ⟨w, F.Xh_le a m h w.2⟩‖
/-- `F` **approximates on the window** `[a, a + m)`: in the graph norm in the degrees
`a, …, a + m - 2`, and in `W` in the last degree `a + m - 1` (no differential in the window). -/
def ApproximatesOn : Prop :=
  (∀ i : Fin m, (i : ℕ) + 1 < m → F.Approximates (a + (i : ℕ))) ∧
    ∀ i : Fin m, (i : ℕ) + 1 = m → ∀ x : W (a + (i : ℕ)),
      Tendsto (fun h => Metric.infDist x ((F.V h).V (a + (i : ℕ)))) F.l (𝓝 0)

/-- The mixed method of `F` in degree `j` **has the rate `r`** on the regularity classes `Reg`:
for some `C`, `‖x - xₕ‖ ≤ C L r(h)` when `σ`, `u`, `p` and `P_𝔅 u` are regular with bound `L`. -/
def HasRate (j : ℤ) (Reg : ∀ i, ℝ → W i → Prop) (r : κ → ℝ) : Prop :=
  ∃ C, ∀ {f : W j} {x : H.Mixed j}, IsMixedSolution (H.mixedSpace j) f x → ∀ {L : ℝ}, 0 ≤ L →
    Reg (j - 1) L x.1 → Reg j L x.2.1 → Reg j L x.2.2 →
    Reg j L ((H.boundaries j).topologicalClosure.starProjection x.2.1) → ∀ (h : κ) {xh},
    IsMixedSolution ((F.V h).mixedSpace j) f xh → H.mixedNorm (x - xh) ≤ C * L * r h
/-- The fully discrete wave method of `F` on the window, with the exact group `S`, **has the rate
`r`** on the regularity classes `Reg`: for every A-stable `r = P/Q` of order `p`, some `C`, `K`
(independent of `h`, `τ`, `n`, `L` and the data) bound the error of `r(τ Lₕ)ⁿ v` by
`‖v - x‖ + C (1 + nτ) L r(h) + K nτ τᵖ ‖Lₕ^{p+1} v‖` when the components of `S(t) x` and
`S(t) L x` are regular with bound `L` on `[0, nτ]`. -/
def HasWaveRate (S : ℝ → Total W a m →L[𝕜] Total W a m) (Reg : ∀ i, ℝ → W i → Prop)
    (r : κ → ℝ) : Prop :=
  ∀ P Q : Polynomial ℝ, IsAStable P Q → ∀ {p : ℕ}, HasOrder P Q p → ∃ C K : ℝ,
    ∀ (x : Total W a m) (hx : x ∈ (H.wave a m).domain), H.wave a m ⟨x, hx⟩ ∈ (H.wave a m).domain →
    ∀ {L : ℝ}, 0 ≤ L → ∀ (h : κ) {τ : ℝ}, 0 ≤ τ → ∀ (n : ℕ) (v : F.Xh a m h),
    (∀ t ∈ Icc 0 (n * τ), ∀ i : Fin m,
      Reg (a + (i : ℕ)) L (S t x i) ∧ Reg (a + (i : ℕ)) L (S t (H.wave a m ⟨x, hx⟩) i)) →
    ‖S (n * τ) x - ((rationalApply P Q ((τ : 𝕜) • F.Lh a m h) ^ n) v : Total W a m)‖ ≤
      ‖(v : Total W a m) - x‖ + C * (1 + n * τ) * L * r h +
        K * (n * τ) * τ ^ p * ‖(F.Lh a m h ^ (p + 1)) v‖

variable [∀ i, NormedSpace ℝ (W i)]
/-- **The conclusions of the FEEC theorem for the Hodge wave equation** on the window, group `S`. -/
structure WaveVerdict (S : ℝ → Total W a m →L[𝕜] Total W a m) : Prop where
  /-- well-posedness and convergence of the semidiscrete and fully discrete solutions -/
  evolution : EvolutionVerdict (H.wave a m) F.l (fun h => F.Xh a m h)
    (fun h => (F.Xh a m h).subtypeL) (F.Lh a m) S
  /-- `S` is a unitary group -/
  norm_eq (t : ℝ) (x : Total W a m) : ‖S t x‖ = ‖x‖
  add (s t : ℝ) : S (s + t) = S s ∘L S t
  /-- the semidiscrete error bound: for `x ∈ D(L²)` with `S(s) x`, `S(s) L x` within `M` of `Xₕ` in
  the graph norm on `[0, t]`, `‖S(t) x - exp(t Lₕ) v‖ ≤ ‖v - x‖ + 2 (1 + C_P) (1 + t) M`, with
  `C_P = 4√3` the uniform bound of the elliptic projections -/
  error (x : Total W a m) (hx : x ∈ (H.wave a m).domain)
    (hx2 : H.wave a m ⟨x, hx⟩ ∈ (H.wave a m).domain) (h : κ) (v : F.Xh a m h) {t M : ℝ}
    (ht : 0 ≤ t) (hM : ∀ s ∈ Icc 0 t, ∀ y : (H.totalD a m).domain,
      (y : Total W a m) = S s x ∨ (y : Total W a m) = S s (H.wave a m ⟨x, hx⟩) →
        F.graphDist a m h y ≤ M) :
    ‖S t x - (semiflow (F.Lh a m h) t v : Total W a m)‖ ≤
      ‖(v : Total W a m) - x‖ + 2 * (1 + 4 * √3) * (1 + t) * M

end SubcomplexFamily

/-! ### Variational crimes -/

/-- An **approximating family of discrete differential spaces** on `[a, a + m)` ([HolstStern2012],
§3): finite-dimensional `Xₕ`, `𝐝ₕ 𝐝ₕ = 0`, uniformly bounded reading maps `iₕ : Xₕ → W` with
uniformly bounded left inverses (not necessarily cochain maps, isometries, or into `D(𝐝)`). -/
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
/-- The **inner-product defect** `‖1 - iₕ* iₕ‖` of the reading map. -/
def defect (h : κ) : ℝ := ‖1 - (S.incl h).adjoint ∘L S.incl h‖
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
  /-- convergence for every datum when `‖1 - iₕ* iₕ‖ → 0` and `iₕ πₕ → 1` on `D(𝐝)` -/
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
  error and `‖1 - iₕ* iₕ‖ (‖σ‖ + ‖𝐝σ‖ + ‖u‖ + ‖𝐝u‖ + ‖p‖) ≤ ε` -/
  rate : ∃ K : ℝ, ∀ (h : κ) {f x}, IsMixedSolution (H.totalMixedSpace a m) f x → ∀ {xh},
    S.IsSolution h f xh → ∀ {ε : ℝ}, (∃ v, S.readGap h x.1 (𝐝 x.1) v ≤ ε) →
      (∃ v, S.readGap h x.2.1 (𝐝 x.2.1) v ≤ ε) → (∃ v, S.readGap h x.2.2 0 v ≤ ε) →
      (∃ v, S.readGap h ((LinearMap.range (𝐝).toFun).topologicalClosure.starProjection x.2.1) 0 v
        ≤ ε) →
      S.defect h * (‖(x.1 : Total W a m)‖ + ‖𝐝 x.1‖ + ‖(x.2.1 : Total W a m)‖ + ‖𝐝 x.2.1‖ +
        ‖x.2.2‖) ≤ ε → S.readError h x xh ≤ K * ε

end CrimeFamily
end HilbertComplex

/-! ### The four theorems -/

variable [∀ i, NormedSpace ℝ (W i)]
/-! ### A finite element instance: Whitney forms on the cube, in the `L²` de Rham complex -/
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
-- palomar-shared: IsCsForm
/-- `x ∈ L²(Ω; Λʲ)` is a.e. a `C^{s+2}` form `w` of degree `j` with `‖D^{s+1} w‖, ‖D^{s+1} dw‖ ≤ L`
on `cl Ω` (true in negative degrees): the regularity class of the order `h^{s+1}`. -/
def IsCsForm {n : ℕ} (Ω : Set (Fin n → ℝ)) (s : ℕ) (j : ℤ) (L : ℝ) (x : L2Form Ω j) : Prop :=
  j < 0 ∨ ∃ w : FormField n, ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w ∧
    (∀ y (t : Finset (Fin n)), (t.card : ℤ) ≠ j → w y t = 0) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) ∧
    (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L) ∧
    ∀ t : FormIdx n j, ⇑(x t) =ᵐ[volume.restrict Ω] fun y => w y t.1
-- palomar-shared-end: IsCsForm
end FEEC
