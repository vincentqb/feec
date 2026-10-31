module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# The FEEC theorem for the Hodge wave and heat equations

Finite element exterior calculus ([AFW2006], [AFW2010]) approximates a Hilbert complex
`⋯ → Wⁱ → Wⁱ⁺¹ → ⋯` of closed densely defined operators by finite-dimensional subcomplexes `Vₕ`
with commuting cochain projections `πₕ`. The theorem below (`FEEC.dynamicFEEC`) states, on every
window `Wᵃ ⊕ ⋯ ⊕ W^{a+m-1}` (with total differential `𝐝`) of a family of subcomplexes with the
approximation property of [AFW2010], §3.3 in the graph norm of the window (the graph norm in the
degrees `a, …, a + m - 2`, the norm of `W` in the last degree, which has no differential in the
window):

1. (**wave**) the Hodge wave equation `ξ' = L ξ`, `L = 𝐝 - 𝐝*`, is well posed (strong solutions,
   a unitary group `S`); its semidiscrete Galerkin solutions `exp(t Lₕ) vₕ` converge to `S(t) x`
   uniformly on `[0, T]` for every datum `x` and every family `vₕ → x`, with the error bound
   `‖S(t) x - exp(t Lₕ) vₕ‖ ≤ ‖vₕ - x‖ + 2 (1 + C_P) (1 + t) M` for `x ∈ D(L²)`, `M` a bound of
   the graph-norm distances of `S(s) x` and `S(s) L x` to `Xₕ = ⊕ Vₕ` for `s ∈ [0, t]` and
   `C_P = 4√3` the bound of the elliptic projections; the θ-schemes, `θ ≥ 1/2`, converge as
   `h, τ → 0`, with the temporal error `(θ + 1/2) nτ τ ‖Lₕ² w₀‖` (`5/12 nτ τ² ‖Lₕ³ w₀‖` for
   Crank–Nicolson) and the fully discrete error bounds; a closed constraint `K` is propagated by
   the flow iff it reduces `L`, and then the constraint residual of the discrete solutions is
   bounded by their error
   ([QuennevilleBelair2015], Thms 4.6, 4.7, 4.14, Prop. 4.13, 4.17; [Thomee2006], Ch. 7);
2. (**heat**) with projections bounded in the graph norm of the window (in `W` in its last
   degree) and closed ranges in the window, the same convergence for the Hodge heat equation
   `u' = L² u = -Δ u` with the discrete generators `Lₕ²` ([GilletteHolstZhu2017], via the
   elliptic convergence of [AFW2010], Thm 3.9).

Mathlib has no `C₀`-semigroups: the exact evolutions are the operator families `S` that the
theorem asserts to exist, characterized by their strong solutions (unique, so `S` is unique on
the dense domain for `t ≥ 0`).

The differential of the complex is encoded as a family `d i j : Wⁱ → Wʲ` of all pairs, zero
unless `j = i + 1`, so that windows and their total differentials need no casts.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–§3.4
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4–§4.6, §4.10
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

/-! ### Hilbert complexes and families of subcomplexes -/

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

/-- A **subcomplex**: subspaces `Vⁱ ⊆ D(d i j)` with `d Vⁱ ⊆ Vʲ`. -/
structure Subcomplex where
  /-- the subspaces -/
  V : ∀ i, Submodule 𝕜 (W i)
  le_domain : ∀ i j, V i ≤ (H.d i j).domain
  mapsTo : ∀ i j (x : W i) (hx : x ∈ V i), (H.d i j ⟨x, le_domain i j hx⟩ : W j) ∈ V j

/-- A **cochain projection** onto `S`: projections `πⁱ : Wⁱ → Vⁱ` commuting with `d`. -/
structure Subcomplex.CochainProjection {H : HilbertComplex 𝕜 W} (S : H.Subcomplex) where
  /-- the projections -/
  π : ∀ i, W i →ₗ[𝕜] W i
  mem : ∀ i x, π i x ∈ S.V i
  proj : ∀ i x, x ∈ S.V i → π i x = x
  comm : ∀ i j (x : (H.d i j).domain),
    H.d i j ⟨π i x, S.le_domain i j (mem i x)⟩ = π j (H.d i j x)

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

/-- The distance `inf_{v ∈ Vⁱ} ‖x - v‖ + ‖y - d i j v‖`; for `y = d x`, the distance from `x` to
`Vⁱ` in the graph norm of `d i j`. -/
def Subcomplex.graphDist {H : HilbertComplex 𝕜 W} (S : H.Subcomplex) (i j : ℤ) (x : W i)
    (y : W j) : ℝ :=
  ⨅ v : S.V i, ‖x - v‖ + ‖y - H.d i j ⟨v, S.le_domain i j v.2⟩‖

variable {H} {κ : Type*}

/-- The cochain projections of `F` are **bounded in the graph norm** in degree `i`, uniformly in
`h`: `‖πₕ x‖ + ‖d πₕ x‖ ≤ C (‖x‖ + ‖d x‖)` on `D(d i (i + 1))`. -/
def SubcomplexFamily.IsGraphBounded (F : H.SubcomplexFamily κ) (i : ℤ) : Prop :=
  ∃ C : ℝ, ∀ (h : κ) (x : (H.d i (i + 1)).domain), ‖(F.π h).π i x‖ +
    ‖H.d i (i + 1) ⟨(F.π h).π i x, (F.V h).le_domain i (i + 1) ((F.π h).mem i x)⟩‖ ≤
      C * (‖(x : W i)‖ + ‖H.d i (i + 1) x‖)

/-- `F` **approximates** in degree `i` in the graph norm: the distance from every `x ∈ D(d)` to
`Vₕⁱ` in the graph norm tends to `0`. -/
def SubcomplexFamily.Approximates (F : H.SubcomplexFamily κ) (i : ℤ) : Prop :=
  ∀ x : (H.d i (i + 1)).domain,
    Tendsto (fun h => (F.V h).graphDist i (i + 1) x (H.d i (i + 1) x)) F.l (𝓝 0)

end HilbertComplex

/-! ### Evolutions -/

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

variable [NormedSpace ℝ E]

/-- `u` is a **strong solution** of `u' = A u` on `I`. -/
def IsStrongSolution (A : E →ₗ.[𝕜] E) (I : Set ℝ) (u : ℝ → E) : Prop :=
  ContinuousOn u I ∧ ∀ t ∈ I, ∃ v, (u t, v) ∈ A.graph ∧ HasDerivWithinAt u v I t

/-- The semidiscrete evolution `exp(t B)` on `X ⊆ E`. -/
def semiflow {X : Submodule 𝕜 E} (B : X →L[𝕜] X) (t : ℝ) : X →L[𝕜] X :=
  NormedSpace.exp ((t : 𝕜) • B)

/-- **The FEEC theorem for an evolution** `u' = A u` approximated by `uₕ' = Bₕ uₕ` on the
finite-dimensional `Xₕ ⊆ E`, with exact evolution `S`: `S t x` is the unique strong solution
from `x ∈ D(A)` (`D(A)` dense), `S 0 = 1`, and `S t x` has nonincreasing norm; the semidiscrete solutions
`exp(t Bₕ) vₕ` (`semiflow`) converge to `S t x` uniformly on `[0, T]` from every family
`vₕ → x`; and so do the θ-schemes `wₙ₊₁ - wₙ = τₕ Bₕ (θ wₙ₊₁ + (1 - θ) wₙ)`, `θ ≥ 1/2`, as
`h, τₕ → 0`, with the temporal error `‖exp(nτ Bₕ) w₀ - wₙ‖ ≤ (θ + 1/2) nτ τ ‖Bₕ² w₀‖`, of second
order `5/12 nτ τ² ‖Bₕ³ w₀‖` for Crank–Nicolson (`θ = 1/2`). -/
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
  theta (θ : ℝ) (hθ : 1 / 2 ≤ θ) (τ : κ → ℝ) (hτ : ∀ h, 0 < τ h) (hτ0 : Tendsto τ l (𝓝 0))
    (x : E) (w : ∀ h, ℕ → X h) (hw : ∀ h n, w h (n + 1) - w h n =
      (τ h : 𝕜) • B h ((θ : 𝕜) • w h (n + 1) + (1 - (θ : 𝕜)) • w h n))
    (hw0 : Tendsto (fun h => (w h 0 : E)) l (𝓝 x)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in l, ∀ n : ℕ, (n : ℝ) * τ h ∈ Icc 0 T → ‖S (n * τ h) x - w h n‖ < ε
  theta_temporal (θ : ℝ) (hθ : 1 / 2 ≤ θ) (h : κ) {τ : ℝ} (hτ : 0 < τ) (w : ℕ → X h)
    (hw : ∀ n, w (n + 1) - w n = (τ : 𝕜) • B h ((θ : 𝕜) • w (n + 1) + (1 - (θ : 𝕜)) • w n))
    (n : ℕ) :
    ‖semiflow (B h) (n * τ) (w 0) - w n‖ ≤ (θ + 1 / 2) * (n * τ) * τ * ‖(B h ^ 2) (w 0)‖
  crankNicolson_temporal (h : κ) {τ : ℝ} (hτ : 0 < τ) (w : ℕ → X h)
    (hw : ∀ n, w (n + 1) - w n = (τ : 𝕜) • B h ((1 / 2 : 𝕜) • (w (n + 1) + w n))) (n : ℕ) :
    ‖semiflow (B h) (n * τ) (w 0) - w n‖ ≤ 5 / 12 * (n * τ) * τ ^ 2 * ‖(B h ^ 3) (w 0)‖

end Evolution

/-! ### Windows -/

/-- The total space `Wᵃ ⊕ ⋯ ⊕ W^{a+m-1}` of a window (an `ℓ²` sum). -/
abbrev Total (W : ℤ → Type*) (a : ℤ) (m : ℕ) : Type _ := PiLp 2 fun i : Fin m => W (a + (i : ℕ))

namespace HilbertComplex

/-- The boundaries `𝔅ⁱ = R(d (i - 1) i)`. -/
def boundaries (H : HilbertComplex 𝕜 W) (i : ℤ) : Submodule 𝕜 (W i) :=
  LinearMap.range (H.d (i - 1) i).toFun

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

/-- The **Hodge–Dirac (wave) operator** `L = 𝐝 - 𝐝*` of the window. -/
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
norm. -/
def graphDist (h : κ) (y : (H.totalD a m).domain) : ℝ :=
  ⨅ w : F.Xh a m h, ‖(y : Total W a m) - w‖ +
    ‖H.totalD a m y - H.totalD a m ⟨w, F.Xh_le a m h w.2⟩‖

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The conclusions of the FEEC theorem for the Hodge wave equation** on the window, with
exact evolution `S`. -/
structure WaveVerdict (S : ℝ → Total W a m →L[𝕜] Total W a m) : Prop where
  /-- well-posedness and convergence of the semidiscrete solutions and the θ-schemes -/
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
  /-- the fully discrete error bound of the θ-schemes, `θ ≥ 1/2`: under the hypotheses of `error`
  at `t = nτ`, `‖S(nτ) x - wₙ‖ ≤ ‖w₀ - x‖ + 2 (1 + C_P) (1 + nτ) M + (θ + 1/2) nτ τ ‖Lₕ² w₀‖`
  (from `error` and the temporal error) -/
  theta_error (x : Total W a m) (hx : x ∈ (H.wave a m).domain)
    (hx2 : H.wave a m ⟨x, hx⟩ ∈ (H.wave a m).domain) (θ : ℝ) (hθ : 1 / 2 ≤ θ) (h : κ) {τ : ℝ}
    (hτ : 0 < τ) (w : ℕ → F.Xh a m h) (hw : ∀ n, w (n + 1) - w n =
      (τ : 𝕜) • F.Lh a m h ((θ : 𝕜) • w (n + 1) + (1 - (θ : 𝕜)) • w n)) (n : ℕ) {M : ℝ}
    (hM : ∀ s ∈ Icc 0 (n * τ), ∀ y : (H.totalD a m).domain,
      (y : Total W a m) = S s x ∨ (y : Total W a m) = S s (H.wave a m ⟨x, hx⟩) →
        F.graphDist a m h y ≤ M) :
    ‖S (n * τ) x - (w n : Total W a m)‖ ≤ ‖(w 0 : Total W a m) - x‖ +
      2 * (1 + 4 * √3) * (1 + n * τ) * M + (θ + 1 / 2) * (n * τ) * τ * ‖(F.Lh a m h ^ 2) (w 0)‖
  /-- the fully discrete error bound of Crank–Nicolson, of second order in time:
  `‖S(nτ) x - wₙ‖ ≤ ‖w₀ - x‖ + 2 (1 + C_P) (1 + nτ) M + 5/12 nτ τ² ‖Lₕ³ w₀‖` -/
  crankNicolson_error (x : Total W a m) (hx : x ∈ (H.wave a m).domain)
    (hx2 : H.wave a m ⟨x, hx⟩ ∈ (H.wave a m).domain) (h : κ) {τ : ℝ} (hτ : 0 < τ)
    (w : ℕ → F.Xh a m h)
    (hw : ∀ n, w (n + 1) - w n = (τ : 𝕜) • F.Lh a m h ((1 / 2 : 𝕜) • (w (n + 1) + w n)))
    (n : ℕ) {M : ℝ} (hM : ∀ s ∈ Icc 0 (n * τ), ∀ y : (H.totalD a m).domain,
      (y : Total W a m) = S s x ∨ (y : Total W a m) = S s (H.wave a m ⟨x, hx⟩) →
        F.graphDist a m h y ≤ M) :
    ‖S (n * τ) x - (w n : Total W a m)‖ ≤ ‖(w 0 : Total W a m) - x‖ +
      2 * (1 + 4 * √3) * (1 + n * τ) * M + 5 / 12 * (n * τ) * τ ^ 2 * ‖(F.Lh a m h ^ 3) (w 0)‖
  /-- a closed constraint `K` propagates iff it reduces `L` -/
  propagates_iff (K : Submodule 𝕜 (Total W a m)) [K.HasOrthogonalProjection] :
    IsReducing (H.wave a m) K ↔ ∀ t, ∀ x ∈ K, S t x ∈ K
  /-- and then the residual `dist(uₕ(t), K)` of a discrete solution is at most its error (from
  `propagates_iff`, since `S t x ∈ K`) -/
  residual_le (K : Submodule 𝕜 (Total W a m)) [K.HasOrthogonalProjection]
    (hK : IsReducing (H.wave a m) K) {x : Total W a m} (hx : x ∈ K) (h : κ) (v : F.Xh a m h)
    (t : ℝ) : Metric.infDist (semiflow (F.Lh a m h) t v : Total W a m) K ≤
      ‖S t x - (semiflow (F.Lh a m h) t v : Total W a m)‖

/-- **The conclusions of the FEEC theorem for the Hodge wave and heat equations** on the
window. -/
structure DynamicVerdict : Prop where
  /-- the wave equation `ξ' = L ξ` -/
  wave : ∃ S, F.WaveVerdict a m S
  /-- the heat equation `u' = L² u`, with projections bounded in the graph norm in the degrees
  `a, …, a + m - 2` and in `W` in the last degree `a + m - 1` (which has no differential in the
  window), and closed ranges in the window -/
  heat (hπ : ∀ i : Fin m, (i : ℕ) + 1 < m → F.IsGraphBounded (a + (i : ℕ)))
    (hπ' : ∀ i : Fin m, (i : ℕ) + 1 = m →
      ∃ C : ℝ, ∀ (h : κ) (x : W (a + (i : ℕ))), ‖(F.π h).π _ x‖ ≤ C * ‖x‖)
    (hcr : ∀ i : Fin m, 0 < (i : ℕ) →
      IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ))))) :
    ∃ S : ℝ → Total W a m →L[𝕜] Total W a m,
    EvolutionVerdict (sq (H.wave a m)) F.l (F.Xh a m) (fun h => F.Lh a m h ^ 2) S

end SubcomplexFamily

end HilbertComplex

/-! ### The theorem -/

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The FEEC theorem for the Hodge wave and heat equations** ([QuennevilleBelair2015], Thms 4.6,
4.7, 4.14, Props 4.13, 4.17; [Thomee2006], Ch. 7; [GilletteHolstZhu2017]). Let `F` be a family of
subcomplexes which approximates in the graph norm in the degrees `a, …, a + m - 2` and in `W` in
the degree `a + m - 1`. On the window `[a, a + m)`, `F` satisfies the wave and heat verdicts
(`SubcomplexFamily.DynamicVerdict`). -/
theorem dynamicFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} (F : H.SubcomplexFamily κ) (a : ℤ)
    (m : ℕ) (happrox : ∀ i : Fin m, (i : ℕ) + 1 < m → F.Approximates (a + (i : ℕ)))
    (happrox' : ∀ i : Fin m, (i : ℕ) + 1 = m → ∀ x : W (a + (i : ℕ)),
      Tendsto (fun h => Metric.infDist x ((F.V h).V (a + (i : ℕ)))) F.l (𝓝 0)) :
    F.DynamicVerdict a m := by
  sorry

end FEEC
