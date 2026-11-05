module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but the compared theorems
`FEEC.feec`, `FEEC.feec_rated`, `FEEC.staticFEEC_uniform`, `FEEC.exists_cochainProjection`,
`FEEC.exists_subcomplexFamily_iff`, `FEEC.crimeFEEC` and `FEEC.crime_nonvacuous`), compiled
against Mathlib alone so that their elaborated values are those of the challenge. The solution
imports this module and the bridges to `Feec`, and proves the theorems (`Solution.lean`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3–§3.4
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012], §3
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015], Ch. 4
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.3
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

universe u v w

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

/-- The kernel of a closed operator is closed. -/
theorem isClosed_ker {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [Module 𝕜 E]
    [Module 𝕜 F] {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) : IsClosed (T.ker : Set E) := by
  convert hT.preimage (continuous_id.prodMk continuous_const :
    Continuous fun x : E => (x, (0 : F))) using 1
  ext x
  exact mem_ker_iff.trans ((exists_congr fun _ => and_congr_left' eq_comm).trans
    (mem_graph_iff T (x := (id x, (0 : F)))).symm)

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

/-! ### Cohomology and harmonic forms -/

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

/-- The distance `E(x) = inf_{v ∈ Vⁱ} ‖x - v‖_V` from `x ∈ D(d i j)` to `Vⁱ` in the graph norm. -/
def graphDist (i j : ℤ) (x : (H.d i j).domain) : ℝ :=
  ⨅ v : S.V i, H.graphNorm i j (x - ⟨v, S.le_domain i j v.2⟩)

namespace CochainProjection

variable {S} (P : S.CochainProjection)

/-- `d π = π d` from `i` to any `k = i + 1`. -/
theorem exists_d_eq {i k : ℤ} (hk : i + 1 = k) (x : (H.d i k).domain) :
    ∃ y : S.V i, H.d i k ⟨y, S.le_domain i k y.2⟩ = P.π k ⟨H.d i k x, H.mapsTo i k (k + 1) x⟩ := by
  subst hk
  exact ⟨P.π i x, P.comm i x⟩

/-- The map `Hⁱ → Hⁱ(V)`, `[z] ↦ [π z]`, induced by the cochain projection. -/
def cohomologyMap (i : ℤ) : H.cohomology i →ₗ[𝕜] S.cohomology i :=
  Submodule.mapQ _ _ (LinearMap.codRestrict (S.cycles i)
    ((S.V i).subtype ∘ₗ P.π i ∘ₗ Submodule.inclusion (H.cycles_le_domain i)) fun z => by
      refine ⟨(P.π i _).2, mem_ker_iff.2 ⟨⟨_, S.le_domain i (i + 1) (P.π i _).2⟩, rfl, ?_⟩⟩
      have h0 : (⟨H.d i (i + 1) (Submodule.inclusion (H.cycles_le_domain i) z),
          H.mapsTo i (i + 1) (i + 1 + 1) _⟩ : (H.d (i + 1) (i + 1 + 1)).domain) = 0 :=
        Subtype.ext ((coe_mem_ker_iff (x := Submodule.inclusion (H.cycles_le_domain i) z)).1 z.2)
      rw [P.comm, h0, _root_.map_zero, ZeroMemClass.coe_zero]) fun z hz => by
    obtain ⟨w, hw⟩ := hz
    obtain ⟨y, hy⟩ := P.exists_d_eq (sub_add_cancel i 1) w
    exact ⟨y, hy.trans (congrArg (fun x => (P.π i x : W i)) (Subtype.ext hw))⟩

/-- The **harmonic gap** `μ = sup_{q ∈ ℌʲ, ‖q‖ ≤ 1} ‖q - π q‖`. -/
def harmonicGap (j : ℤ) : ℝ :=
  ⨆ q : {q : H.harmonic j // ‖(q : W j)‖ ≤ 1},
    ‖((q : H.harmonic j) : W j) - P.π j ⟨q, H.harmonic_le_domain j (q : H.harmonic j).2⟩‖

end CochainProjection

end Subcomplex

/-! ### The mixed Hodge Laplacian -/

/-- `(σ, u, p) ∈ A × B × Q` solves the **mixed Hodge Laplacian** in degree `j` with data `f`,
Galerkin in `A ⊆ Wʲ⁻¹`, `B ⊆ Wʲ` and `Q ⊆ Wʲ` (the harmonic forms for the exact problem):
`⟪τ, σ⟫ - ⟪dτ, u⟫ = 0`, `⟪v, dσ⟫ + ⟪dv, du⟫ + ⟪v, p⟫ = ⟪v, f⟫`, `⟪q, u⟫ = 0`. -/
structure IsMixedSolution (j : ℤ) (A : Submodule 𝕜 (W (j - 1))) (B Q : Submodule 𝕜 (W j))
    (f : W j) (σ : (H.d (j - 1) j).domain) (u : (H.d j (j + 1)).domain) (p : W j) : Prop where
  mem : (σ : W (j - 1)) ∈ A ∧ (u : W j) ∈ B ∧ p ∈ Q
  fst : ∀ τ : (H.d (j - 1) j).domain, (τ : W (j - 1)) ∈ A →
    ⟪(τ : W (j - 1)), (σ : W (j - 1))⟫_𝕜 - ⟪H.d (j - 1) j τ, (u : W j)⟫_𝕜 = 0
  snd : ∀ v : (H.d j (j + 1)).domain, (v : W j) ∈ B →
    ⟪(v : W j), H.d (j - 1) j σ⟫_𝕜 + ⟪H.d j (j + 1) v, H.d j (j + 1) u⟫_𝕜 + ⟪(v : W j), p⟫_𝕜 =
      ⟪(v : W j), f⟫_𝕜
  harm : ∀ q ∈ Q, ⟪q, (u : W j)⟫_𝕜 = 0

/-- The **mixed form** `B(σ, u, p; τ, v, q) = ⟪τ, σ⟫ - ⟪dτ, u⟫ + ⟪v, dσ⟫ + ⟪dv, du⟫ + ⟪v, p⟫ -
⟪q, u⟫` of the mixed Hodge Laplacian in degree `j`. -/
def mixedForm (j : ℤ) (σ : (H.d (j - 1) j).domain) (u : (H.d j (j + 1)).domain) (p : W j)
    (τ : (H.d (j - 1) j).domain) (v : (H.d j (j + 1)).domain) (q : W j) : 𝕜 :=
  ⟪(τ : W (j - 1)), (σ : W (j - 1))⟫_𝕜 - ⟪H.d (j - 1) j τ, (u : W j)⟫_𝕜 +
    ⟪(v : W j), H.d (j - 1) j σ⟫_𝕜 + ⟪H.d j (j + 1) v, H.d j (j + 1) u⟫_𝕜 + ⟪(v : W j), p⟫_𝕜 -
    ⟪q, (u : W j)⟫_𝕜

/-- The norm `‖σ‖_V + ‖u‖_V + ‖p‖` of the mixed space `Vʲ⁻¹ × Vʲ × Wʲ`. -/
def mixedNorm (j : ℤ) (σ : (H.d (j - 1) j).domain) (u : (H.d j (j + 1)).domain) (p : W j) : ℝ :=
  H.graphNorm (j - 1) j σ + H.graphNorm j (j + 1) u + ‖p‖

/-- The error `‖σ - σ'‖_V + ‖u - u'‖_V + ‖p - p'‖`. -/
def mixedError (j : ℤ) (σ σ' : (H.d (j - 1) j).domain) (u u' : (H.d j (j + 1)).domain)
    (p p' : W j) : ℝ :=
  H.mixedNorm j (σ - σ') (u - u') (p - p')

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

/-- `F` **approximates** in degree `i` in the graph norm: the distance from every `x ∈ D(d)` to
`Vₕⁱ` in the graph norm tends to `0`. -/
def SubcomplexFamily.Approximates (F : H.SubcomplexFamily κ) (i : ℤ) : Prop :=
  ∀ x : (H.d i (i + 1)).domain, Tendsto (fun h => (F.V h).graphDist i (i + 1) x) F.l (𝓝 0)

/-- **The conclusions of the static FEEC theorem** in degree `j` for the family of subcomplexes
`F`, with the constant `C` (independent of `h`) in every bound. -/
structure SubcomplexFamily.StaticVerdict (F : H.SubcomplexFamily κ) (j : ℤ) (C : ℝ) : Prop where
  /-- the gap from `ℌʲ` to `ℌₕʲ`: `dist(q, ℌₕʲ) ≤ ‖q - πₕ q‖` -/
  harmonicDist (h : κ) (q : W j) (hq : q ∈ H.harmonic j) :
    Metric.infDist q ((F.V h).harmonic j) ≤ ‖q - (F.π h).π j ⟨q, H.harmonic_le_domain j hq⟩‖
  /-- the gap from `ℌₕʲ` to `ℌʲ`: `‖q - P_ℌ q‖ ≤ ‖P_ℌ q - πₕ P_ℌ q‖` -/
  discreteHarmonicDist (h : κ) (q : W j) (hq : q ∈ (F.V h).harmonic j) :
    ‖q - (H.harmonic j).starProjection q‖ ≤ ‖(H.harmonic j).starProjection q -
      (F.π h).π j ⟨_, H.harmonic_le_domain j (Submodule.starProjection_apply_mem _ q)⟩‖
  /-- `πₕ` induces a left inverse of the map induced by the inclusion -/
  cohomologyMap_comp_incl (h : κ) :
    (F.π h).cohomologyMap j ∘ₗ (F.V h).cohomologyIncl j = LinearMap.id
  /-- where `‖q - πₕ q‖ < ‖q‖` on `ℌʲ \ 0`, both are isomorphisms `Hʲ ≅ Hʲ(Vₕ)` -/
  cohomology_of_lt (h : κ)
    (hgap : ∀ (q : W j) (hq : q ∈ H.harmonic j), q ≠ 0 →
      ‖q - (F.π h).π j ⟨q, H.harmonic_le_domain j hq⟩‖ < ‖q‖) :
    Function.Bijective ((F.π h).cohomologyMap j) ∧ Function.Bijective ((F.V h).cohomologyIncl j)
  /-- where `F` approximates in degree `j` and `ℌʲ` is finite-dimensional, the harmonic gap tends
  to `0` -/
  harmonicGap (ha : F.Approximates j) [FiniteDimensional 𝕜 (H.harmonic j)] :
    Tendsto (fun h => (F.π h).harmonicGap j) F.l (𝓝 0)
  /-- and both maps are eventually isomorphisms `Hʲ ≅ Hʲ(Vₕ)` -/
  cohomology (ha : F.Approximates j) [FiniteDimensional 𝕜 (H.harmonic j)] :
    ∀ᶠ h in F.l, Function.Bijective ((F.π h).cohomologyMap j) ∧
      Function.Bijective ((F.V h).cohomologyIncl j)
  /-- the uniform discrete Poincaré inequality `‖v‖_V ≤ C ‖d v‖` on `Vₕʲ ⊥ 𝔷ₕʲ` -/
  poincare (h : κ) : (F.V h).PoincareBy j C
  /-- the mixed problem is uniquely solvable -/
  existsUnique (f : W j) : ∃! x : (H.d (j - 1) j).domain × (H.d j (j + 1)).domain × W j,
    H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f x.1 x.2.1 x.2.2
  /-- and so is its Galerkin discretization in `Vₕ` -/
  existsUnique_discrete (h : κ) (f : W j) :
    ∃! x : (H.d (j - 1) j).domain × (H.d j (j + 1)).domain × W j,
      H.IsMixedSolution j ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) f x.1 x.2.1 x.2.2
  /-- the uniform discrete inf-sup condition: every `x = (σ, u, p) ∈ Vₕʲ⁻¹ × Vₕʲ × ℌₕʲ` has a
  `y = (τ, v, q)` there with `‖y‖ ≤ ‖x‖` and `‖x‖² ≤ C |B(x; y)|` (inf-sup constant `1 / C`) -/
  infSup : ∀ (h : κ) (σ : (H.d (j - 1) j).domain) (u : (H.d j (j + 1)).domain) (p : W j),
    (σ : W (j - 1)) ∈ (F.V h).V (j - 1) → (u : W j) ∈ (F.V h).V j → p ∈ (F.V h).harmonic j →
    ∃ (τ : (H.d (j - 1) j).domain) (v : (H.d j (j + 1)).domain) (q : W j),
      (τ : W (j - 1)) ∈ (F.V h).V (j - 1) ∧ (v : W j) ∈ (F.V h).V j ∧ q ∈ (F.V h).harmonic j ∧
      H.mixedNorm j τ v q ≤ H.mixedNorm j σ u p ∧
      H.mixedNorm j σ u p ^ 2 ≤ C * ‖H.mixedForm j σ u p τ v q‖
  /-- the discrete solutions are stable: `‖σₕ‖_V + ‖uₕ‖_V + ‖pₕ‖ ≤ C ‖f‖` -/
  stable : ∀ (h : κ) {f : W j} {σh : (H.d (j - 1) j).domain}
    {uh : (H.d j (j + 1)).domain} {ph : W j},
    H.IsMixedSolution j ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) f σh uh ph →
      H.mixedNorm j σh uh ph ≤ C * ‖f‖
  /-- the discrete solutions are quasi-optimal in the graph norm, `P_𝔅` the orthogonal
  projection onto the closure of `𝔅ʲ` -/
  quasiOptimal : ∀ {f : W j} {σ : (H.d (j - 1) j).domain} {u : (H.d j (j + 1)).domain}
    {p : W j} (hs : H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f σ u p)
    (h : κ) {σh : (H.d (j - 1) j).domain} {uh : (H.d j (j + 1)).domain} {ph : W j},
    H.IsMixedSolution j ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) f σh uh ph →
    H.mixedError j σ σh u uh p ph ≤ C * ((F.V h).graphDist (j - 1) j σ +
      (F.V h).graphDist j (j + 1) u +
      (F.V h).graphDist j (j + 1) ⟨p, H.harmonic_le_domain j hs.mem.2.2⟩ +
      (F.π h).harmonicGap j * (F.V h).graphDist j (j + 1)
        ⟨_, H.topologicalClosure_boundaries_le_domain j
          (Submodule.starProjection_apply_mem (H.boundaries j).topologicalClosure (u : W j))⟩)
  /-- where `F` approximates in degrees `j - 1` and `j`, the discrete solutions converge in the
  graph norm -/
  converges (ha : F.Approximates (j - 1)) (ha' : F.Approximates j) {f : W j}
    {σ : (H.d (j - 1) j).domain} {u : (H.d j (j + 1)).domain} {p : W j}
    (hs : H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f σ u p)
    {σh : κ → (H.d (j - 1) j).domain} {uh : κ → (H.d j (j + 1)).domain} {ph : κ → W j}
    (hsh : ∀ h, H.IsMixedSolution j ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) f
      (σh h) (uh h) (ph h)) :
    Tendsto (fun h => H.mixedError j σ (σh h) u (uh h) p (ph h)) F.l (𝓝 0)

end HilbertComplex

/-! ### Evolutions and time schemes -/

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

/-! ### Windows -/

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

/-- The harmonic forms `ℌ = N(𝐝) ∩ N(𝐝*)` of the window. -/
def totalHarmonic : Submodule 𝕜 (Total W a m) := (H.totalD a m).ker ⊓ (H.totalD a m)†.ker

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

/-- `F` **approximates on the window** `[a, a + m)`: in the graph norm in the degrees
`a, …, a + m - 2`, and in `W` in the last degree `a + m - 1` (no differential in the window). -/
def ApproximatesOn : Prop :=
  (∀ i : Fin m, (i : ℕ) + 1 < m → F.Approximates (a + (i : ℕ))) ∧
    ∀ i : Fin m, (i : ℕ) + 1 = m → ∀ x : W (a + (i : ℕ)),
      Tendsto (fun h => Metric.infDist x ((F.V h).V (a + (i : ℕ)))) F.l (𝓝 0)

/-- **A Jackson estimate** for `F` ([AFW2010], §3.5): a mesh size `hₕ → 0` and, for every
regularity index `s : ρ`, classes `Reg s i L` of `s`-regular forms in `Wⁱ` with bound `L`,
approximated in `Vₕⁱ` at the order `hₕ^{ord s}`: some `v ∈ Vₕⁱ` has `‖x - v‖ ≤ B L hₕ^{ord s}`
and `‖d (x - v)‖ ≤ B L hₕ^{ord s}`. -/
structure Jackson (ρ : Type*) where
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

/-- **The conclusions of the FEEC theorem** for `F`: skew-adjointness of the wave operators, the
static verdict in every degree with bounded projections and closed ranges, the wave and heat
verdicts on every window `F` approximates. -/
structure Verdict : Prop where
  /-- the wave operator `L = 𝐝 - 𝐝*` of every window is skew-adjoint, `L† = -L`, with no
  closed-range or approximation hypothesis ([QuennevilleBelair2015], Thm 4.6) -/
  skewAdjoint (a : ℤ) (m : ℕ) : (H.wave a m)† = -H.wave a m
  /-- the static FEEC theorem in degree `j` -/
  static (j : ℤ) (hπ : F.IsGraphBounded (j - 1)) (hπ' : F.IsGraphBounded j)
    (hj : IsClosed (H.boundaries j : Set (W j)))
    (hj' : IsClosed (H.boundaries (j + 1) : Set (W (j + 1)))) : ∃ C, F.StaticVerdict j C
  /-- the wave and heat FEEC theorems on the window `[a, a + m)` -/
  dynamic (a : ℤ) (m : ℕ) (ha : F.ApproximatesOn a m) : F.DynamicVerdict a m

/-- **The rates of a Jackson estimate** `J` of `F`, constants independent of `h`, `τ`, `n`, `L`
and the data. -/
structure Rated {ρ : Type*} (J : F.Jackson ρ) : Prop where
  /-- the mixed method in degree `j` is `O(L hᵒʳᵈ⁽ˢ⁾)` when `σ`, `u`, `p`, `P_𝔅 u` are `s`-regular
  with bound `L` ([AFW2010], Thm 3.9, §3.5) -/
  static (j : ℤ) (hπ : F.IsGraphBounded (j - 1)) (hπ' : F.IsGraphBounded j)
    (hj : IsClosed (H.boundaries j : Set (W j)))
    (hj' : IsClosed (H.boundaries (j + 1) : Set (W (j + 1)))) (s : ρ) :
    ∃ C, ∀ {f : W j} {σ : (H.d (j - 1) j).domain} {u : (H.d j (j + 1)).domain} {p : W j},
      H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f σ u p → ∀ {L : ℝ}, 0 ≤ L →
      J.Reg s (j - 1) L σ → J.Reg s j L u → J.Reg s j L p →
      J.Reg s j L ((H.boundaries j).topologicalClosure.starProjection (u : W j)) →
      ∀ (h : κ) {σh : (H.d (j - 1) j).domain} {uh : (H.d j (j + 1)).domain} {ph : W j},
      H.IsMixedSolution j ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) f σh uh ph →
      H.mixedError j σ σh u uh p ph ≤ C * L * J.meshSize h ^ J.ord s
  /-- on a window `F` approximates, with its group `S`, the iterates `r(τ Lₕ)ⁿ v` of an A-stable
  rational scheme of order `p` have the error
  `‖v - x‖ + C (1 + nτ) L hᵒʳᵈ⁽ˢ⁾ + K nτ τᵖ ‖Lₕ^{p+1} v‖` when the components of `S(t) x`,
  `S(t) L x` are `s`-regular with bound `L` on `[0, nτ]` ([QuennevilleBelair2015], Thm 4.14;
  [BrennerThomee1979]) -/
  wave (a : ℤ) (m : ℕ) (ha : F.ApproximatesOn a m) (r : RationalScheme) (hr : r.IsAStable)
    {p : ℕ} (hp : r.HasOrder p) (s : ρ) : ∃ S, F.WaveVerdict a m S ∧ ∃ C K : ℝ,
      ∀ (x : Total W a m) (hx : x ∈ (H.wave a m).domain),
      H.wave a m ⟨x, hx⟩ ∈ (H.wave a m).domain → ∀ {L : ℝ}, 0 ≤ L → ∀ (h : κ) {τ : ℝ}, 0 ≤ τ →
      ∀ (n : ℕ) (v : F.Xh a m h), (∀ t ∈ Icc 0 (n * τ), ∀ i : Fin m,
        J.Reg s (a + (i : ℕ)) L (S t x i) ∧ J.Reg s (a + (i : ℕ)) L (S t (H.wave a m ⟨x, hx⟩) i)) →
      ‖S (n * τ) x - ((r.apply ((τ : 𝕜) • F.Lh a m h) ^ n) v : Total W a m)‖ ≤
        ‖(v : Total W a m) - x‖ + C * (1 + n * τ) * L * J.meshSize h ^ J.ord s +
          K * (n * τ) * τ ^ p * ‖(F.Lh a m h ^ (p + 1)) v‖

end SubcomplexFamily

/-! ### Variational crimes -/

/-- An **approximating family of discrete differential spaces** on the window `[a, a + m)`
([HolstStern2012], §3): finite-dimensional inner product spaces `Xₕ` (their own inner products),
differentials `𝐝ₕ` with `𝐝ₕ 𝐝ₕ = 0`, and uniformly bounded reading maps `iₕ : Xₕ → W` with
uniformly bounded left inverses. Nothing relates `𝐝ₕ` to `𝐝`: `iₕ` need not be a cochain map,
an isometry, nor map into `D(𝐝)`. -/
structure CrimeFamily (H : HilbertComplex 𝕜 W) (a : ℤ) (m : ℕ) (κ : Type*) where
  /-- the filter of the refinement -/
  l : Filter κ
  /-- the discrete spaces -/
  X : κ → Type u
  [normedAddCommGroup : ∀ h, NormedAddCommGroup (X h)]
  [innerProductSpace : ∀ h, InnerProductSpace 𝕜 (X h)]
  [completeSpace : ∀ h, CompleteSpace (X h)]
  [finiteDimensional : ∀ h, FiniteDimensional 𝕜 (X h)]
  /-- the discrete differentials -/
  D : ∀ h, X h →L[𝕜] X h
  D_D : ∀ h v, D h (D h v) = 0
  /-- the reading maps `iₕ` -/
  incl : ∀ h, X h →L[𝕜] Total W a m
  /-- their left inverses -/
  proj : ∀ h, Total W a m →L[𝕜] X h
  proj_incl : ∀ h v, proj h (incl h v) = v
  bound : ∃ C, ∀ h, ‖incl h‖ ≤ C ∧ ‖proj h‖ ≤ C

attribute [instance] CrimeFamily.normedAddCommGroup CrimeFamily.innerProductSpace
  CrimeFamily.completeSpace CrimeFamily.finiteDimensional

/-- `(σ, u, p)` solves the **mixed Hodge Laplacian of the window** with data `f`: `p ∈ ℌ`, and
`⟪τ, σ⟫ - ⟪𝐝τ, u⟫ = 0`, `⟪v, 𝐝σ⟫ + ⟪𝐝v, 𝐝u⟫ + ⟪v, p⟫ = ⟪v, f⟫` for `τ, v ∈ D(𝐝)`, `u ⊥ ℌ`. -/
structure IsTotalMixedSolution (H : HilbertComplex 𝕜 W) (a : ℤ) (m : ℕ) (f : Total W a m)
    (σ u : (H.totalD a m).domain) (p : Total W a m) : Prop where
  mem : p ∈ H.totalHarmonic a m
  fst : ∀ τ : (H.totalD a m).domain,
    ⟪(τ : Total W a m), (σ : Total W a m)⟫_𝕜 - ⟪H.totalD a m τ, (u : Total W a m)⟫_𝕜 = 0
  snd : ∀ v : (H.totalD a m).domain, ⟪(v : Total W a m), H.totalD a m σ⟫_𝕜 +
    ⟪H.totalD a m v, H.totalD a m u⟫_𝕜 + ⟪(v : Total W a m), p⟫_𝕜 = ⟪(v : Total W a m), f⟫_𝕜
  harm : ∀ q ∈ H.totalHarmonic a m, ⟪q, (u : Total W a m)⟫_𝕜 = 0

namespace CrimeFamily

variable {H : HilbertComplex 𝕜 W} {a : ℤ} {m : ℕ} {κ : Type*} (S : H.CrimeFamily a m κ)

/-- The discrete harmonic forms `ℌₕ = N(𝐝ₕ) ∩ N(𝐝ₕ*)`. -/
def harmonic (h : κ) : Submodule 𝕜 (S.X h) :=
  LinearMap.ker (S.D h : S.X h →ₗ[𝕜] S.X h) ⊓ LinearMap.ker ((S.D h).adjoint : S.X h →ₗ[𝕜] S.X h)

/-- The residual `B(σ, u, p; τ, v, q) - ⟪iₕ v, f⟫` of `(σ, u, p)` in the discrete mixed problem
with the load `iₕ* f`, at the test function `(τ, v, q)`. -/
def residual (h : κ) (f : Total W a m) (σ u p τ v q : S.X h) : 𝕜 :=
  ⟪τ, σ⟫_𝕜 - ⟪S.D h τ, u⟫_𝕜 + ⟪v, S.D h σ⟫_𝕜 + ⟪S.D h v, S.D h u⟫_𝕜 + ⟪v, p⟫_𝕜 - ⟪q, u⟫_𝕜 -
    ⟪S.incl h v, f⟫_𝕜

/-- `(σₕ, uₕ, pₕ)` solves the **discrete mixed problem** with the load `iₕ* f`: `pₕ ∈ ℌₕ` and the
residual vanishes at every test function `(τ, v, q) ∈ Xₕ × Xₕ × ℌₕ`. -/
def IsMixedSolution (h : κ) (f : Total W a m) (σ u p : S.X h) : Prop :=
  p ∈ S.harmonic h ∧ ∀ τ v q, q ∈ S.harmonic h → S.residual h f σ u p τ v q = 0

/-- The **read error** `‖σ - iₕ σ̃‖ + ‖𝐝σ - iₕ 𝐝ₕ σ̃‖ + ‖u - iₕ ũ‖ + ‖𝐝u - iₕ 𝐝ₕ ũ‖ + ‖p - iₕ p̃‖`
of a discrete triple against a continuous one. -/
def readError (h : κ) (σ u : (H.totalD a m).domain) (p : Total W a m) (σ' u' p' : S.X h) : ℝ :=
  ‖(σ : Total W a m) - S.incl h σ'‖ + ‖H.totalD a m σ - S.incl h (S.D h σ')‖ +
    ‖(u : Total W a m) - S.incl h u'‖ + ‖H.totalD a m u - S.incl h (S.D h u')‖ +
    ‖p - S.incl h p'‖

/-- The **uniform discrete Poincaré inequality** `‖v‖ ≤ c_P ‖𝐝ₕ v‖` on `N(𝐝ₕ)ᗮ`. -/
def IsPoincare (cP : ℝ) : Prop :=
  ∀ h (v : S.X h), v ∈ (LinearMap.ker (S.D h : S.X h →ₗ[𝕜] S.X h))ᗮ → ‖v‖ ≤ cP * ‖S.D h v‖

/-- **Consistent approximation** at the data `f`: discrete triples whose read error against the
solution and whose residual (in the dual graph norm) tend to `0`. -/
def IsConsistentAt (f : Total W a m) : Prop :=
  ∀ σ u p, H.IsTotalMixedSolution a m f σ u p → ∀ ε > 0, ∀ᶠ h in S.l,
    ∃ σ' u' p' : S.X h, p' ∈ S.harmonic h ∧ S.readError h σ u p σ' u' p' ≤ ε ∧
      ∀ τ v q, q ∈ S.harmonic h → ‖S.residual h f σ' u' p' τ v q‖ ≤
        ε * (‖τ‖ + ‖S.D h τ‖ + ‖v‖ + ‖S.D h v‖ + ‖q‖)

/-- The reading maps are **cochain maps**: `iₕ Xₕ ⊆ D(𝐝)` and `𝐝 iₕ = iₕ 𝐝ₕ`. -/
structure IsCochain : Prop where
  incl_mem : ∀ h v, S.incl h v ∈ (H.totalD a m).domain
  totalD_incl : ∀ h v, H.totalD a m ⟨S.incl h v, incl_mem h v⟩ = S.incl h (S.D h v)

/-- **Cochain projections bounded by `C_π` in the graph norm** ([HolstStern2012], §3.3): linear
`πₕ : W → Xₕ` with `πₕ iₕ = 1`, `πₕ 𝐝 = 𝐝ₕ πₕ` and `‖πₕ x‖ ≤ C_π (‖x‖ + ‖𝐝 x‖)` on `D(𝐝)`. -/
structure CochainProj (Cπ : ℝ) where
  /-- the projections -/
  π : ∀ h, Total W a m →ₗ[𝕜] S.X h
  π_incl : ∀ h v, π h (S.incl h v) = v
  norm_π_le : ∀ h (x : (H.totalD a m).domain),
    ‖π h x‖ ≤ Cπ * (‖(x : Total W a m)‖ + ‖H.totalD a m x‖)
  π_totalD : ∀ h (z : (H.totalD a m).domain), π h (H.totalD a m z) = S.D h (π h z)

/-- **The static FEEC theorem with variational crimes**, constant `C`: unique solvability,
stability, the Strang lemma (error at most the read error of any discrete triple plus `C` times
its residual), and convergence for every datum from consistency on a dense set. -/
structure StaticVerdict (C : ℝ) : Prop where
  /-- the mixed problem of the window is uniquely solvable -/
  existsUnique (f : Total W a m) : ∃! x : (H.totalD a m).domain × (H.totalD a m).domain ×
    Total W a m, H.IsTotalMixedSolution a m f x.1 x.2.1 x.2.2
  /-- and so is the discrete one -/
  existsUnique_discrete (h : κ) (f : Total W a m) :
    ∃! x : S.X h × S.X h × S.X h, S.IsMixedSolution h f x.1 x.2.1 x.2.2
  /-- uniformly stable in the discrete graph norm -/
  stable (h : κ) {f : Total W a m} {σ u p : S.X h} (hs : S.IsMixedSolution h f σ u p) :
    ‖σ‖ + ‖S.D h σ‖ + ‖u‖ + ‖S.D h u‖ + ‖p‖ ≤ C * ‖f‖
  /-- the Strang lemma: best read approximation plus residual -/
  strang (h : κ) {f : Total W a m} {σ u : (H.totalD a m).domain} {p : Total W a m}
    (hs : H.IsTotalMixedSolution a m f σ u p) {σh uh ph : S.X h}
    (hsh : S.IsMixedSolution h f σh uh ph) (σ' u' p' : S.X h) (hp' : p' ∈ S.harmonic h) {ε : ℝ}
    (hε : 0 ≤ ε) (hres : ∀ τ v q, q ∈ S.harmonic h → ‖S.residual h f σ' u' p' τ v q‖ ≤
      ε * (‖τ‖ + ‖S.D h τ‖ + ‖v‖ + ‖S.D h v‖ + ‖q‖)) :
    S.readError h σ u p σh uh ph ≤ S.readError h σ u p σ' u' p' + C * ε
  /-- convergence for every datum from consistency on a dense set -/
  converges {D : Set (Total W a m)} (hD : Dense D) (hc : ∀ g ∈ D, S.IsConsistentAt g)
    {f : Total W a m} {σ u : (H.totalD a m).domain} {p : Total W a m}
    (hs : H.IsTotalMixedSolution a m f σ u p) {σh uh ph : ∀ h, S.X h}
    (hsh : ∀ h, S.IsMixedSolution h f (σh h) (uh h) (ph h)) :
    Tendsto (fun h => S.readError h σ u p (σh h) (uh h) (ph h)) S.l (𝓝 0)

/-- **The static FEEC theorem with cochain reading maps** and the cochain projections `P`
([HolstStern2012], Thms 3.3, 3.5, 3.10, Cors 3.4, 3.11). -/
structure CochainVerdict {Cπ : ℝ} (P : S.CochainProj Cπ) : Prop where
  /-- the uniform discrete Poincaré inequality -/
  poincare : ∃ cP, S.IsPoincare cP
  /-- convergence for every datum when `‖1 - iₕ* iₕ‖ → 0` and `iₕ πₕ → 1` on `D(𝐝)` -/
  converges (hJ : Tendsto (fun h => ‖1 - (S.incl h).adjoint ∘L S.incl h‖) S.l (𝓝 0))
    (hπ : ∀ x : (H.totalD a m).domain,
      Tendsto (fun h => ‖(x : Total W a m) - S.incl h (P.π h x)‖) S.l (𝓝 0))
    {f : Total W a m} {σ u : (H.totalD a m).domain} {p : Total W a m}
    (hs : H.IsTotalMixedSolution a m f σ u p) {σh uh ph : ∀ h, S.X h}
    (hsh : ∀ h, S.IsMixedSolution h f (σh h) (uh h) (ph h)) :
    Tendsto (fun h => S.readError h σ u p (σh h) (uh h) (ph h)) S.l (𝓝 0)
  /-- eventually `[z] ↦ [πₕ z]` is an isomorphism `H(𝐝) ≅ H(𝐝ₕ)`: onto (every discrete cycle is
  `πₕ` of a cycle up to a discrete boundary) and one-to-one (a cycle `z` with `πₕ z` a discrete
  boundary is a boundary) -/
  cohomology [FiniteDimensional 𝕜 (H.totalHarmonic a m)]
    (hπ : ∀ q ∈ H.totalHarmonic a m, Tendsto (fun h => ‖q - S.incl h (P.π h q)‖) S.l (𝓝 0)) :
    ∀ᶠ h in S.l, (∀ w : S.X h, S.D h w = 0 → ∃ z : (H.totalD a m).domain,
        H.totalD a m z = 0 ∧ ∃ y, w - P.π h z = S.D h y) ∧
      ∀ z : (H.totalD a m).domain, H.totalD a m z = 0 → (∃ y, P.π h z = S.D h y) →
        ∃ y : (H.totalD a m).domain, (z : Total W a m) = H.totalD a m y
  /-- the error is at most `K ε` when `σ, u, p` and `P_𝔅 u` are within `ε` of `iₕ Xₕ` in the graph
  norm and `‖1 - iₕ* iₕ‖ (‖σ‖ + ‖𝐝σ‖ + ‖u‖ + ‖𝐝u‖ + ‖p‖) ≤ ε` -/
  rate : ∃ K : ℝ, ∀ (h : κ) {f : Total W a m} {σ u : (H.totalD a m).domain} {p : Total W a m},
    H.IsTotalMixedSolution a m f σ u p → ∀ {σh uh ph : S.X h}, S.IsMixedSolution h f σh uh ph →
    ∀ {ε : ℝ}, (∃ v, ‖(σ : Total W a m) - S.incl h v‖ +
        ‖H.totalD a m σ - S.incl h (S.D h v)‖ ≤ ε) →
      (∃ v, ‖(u : Total W a m) - S.incl h v‖ + ‖H.totalD a m u - S.incl h (S.D h v)‖ ≤ ε) →
      (∃ v, ‖p - S.incl h v‖ + ‖S.incl h (S.D h v)‖ ≤ ε) →
      (∃ v, ‖(LinearMap.range (H.totalD a m).toFun).topologicalClosure.starProjection
        (u : Total W a m) - S.incl h v‖ + ‖S.incl h (S.D h v)‖ ≤ ε) →
      ‖1 - (S.incl h).adjoint ∘L S.incl h‖ * (‖(σ : Total W a m)‖ + ‖H.totalD a m σ‖ +
        ‖(u : Total W a m)‖ + ‖H.totalD a m u‖ + ‖p‖) ≤ ε →
      S.readError h σ u p σh uh ph ≤ K * ε

variable [∀ i, NormedSpace ℝ (W i)]

/-- **The conclusions of the FEEC theorem with variational crimes** for `S`: the static verdict
under the uniform discrete Poincaré inequality, the cochain verdict for cochain reading maps. -/
structure Verdict : Prop where
  static {cP : ℝ} (hP : S.IsPoincare cP) : ∃ C, S.StaticVerdict C
  cochain (hi : S.IsCochain) {Cπ : ℝ} (P : S.CochainProj Cπ) : S.CochainVerdict P
  /-- the heat equation `u' = L² u`, `-Δₕ = -(𝐝ₕ 𝐝ₕ* + 𝐝ₕ* 𝐝ₕ)`, when the static method converges
  for every datum and `‖1 - iₕ* iₕ‖ → 0`: well posed, and `iₕ exp(-t Δₕ) vₕ → U(t) x` uniformly on
  `[0, T]` for every family with `iₕ vₕ → x` -/
  heat {cP : ℝ} (hP : S.IsPoincare cP)
    (hJ : Tendsto (fun h => ‖1 - (S.incl h).adjoint ∘L S.incl h‖) S.l (𝓝 0))
    (hconv : ∀ f σ u p, H.IsTotalMixedSolution a m f σ u p → ∀ σh uh ph : ∀ h, S.X h,
      (∀ h, S.IsMixedSolution h f (σh h) (uh h) (ph h)) →
        Tendsto (fun h => S.readError h σ u p (σh h) (uh h) (ph h)) S.l (𝓝 0)) :
    ∃ U : ℝ → Total W a m →L[𝕜] Total W a m,
      (∀ x ∈ (sq (H.wave a m)).domain, ∀ T,
        IsStrongSolution (sq (H.wave a m)) (Icc 0 T) fun t => U t x) ∧
      (∀ x ∈ (sq (H.wave a m)).domain, ∀ T (y : ℝ → Total W a m), y 0 = x →
        IsStrongSolution (sq (H.wave a m)) (Icc 0 T) y → EqOn y (fun t => U t x) (Icc 0 T)) ∧
      (∀ x, U 0 x = x) ∧ (∀ x t, 0 ≤ t → ‖U t x‖ ≤ ‖x‖) ∧
      ∀ (x : Total W a m) (v : ∀ h, S.X h), Tendsto (fun h => S.incl h (v h)) S.l (𝓝 x) →
        ∀ T, TendstoUniformlyOn (fun h (t : ℝ) => S.incl h (semiflow
          (-(S.D h ∘L (S.D h).adjoint + (S.D h).adjoint ∘L S.D h)) t (v h)))
          (fun t => U t x) S.l (Icc 0 T)

end CrimeFamily

end HilbertComplex

/-! ### The theorems -/

variable [∀ i, NormedSpace ℝ (W i)]

end FEEC
