module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The static FEEC theorem

Finite element exterior calculus ([AFW2006], [AFW2010]) approximates a Hilbert complex
`⋯ → Wʲ⁻¹ → Wʲ → Wʲ⁺¹ → ⋯` of closed densely defined operators `d` by finite-dimensional
subcomplexes `Vₕ`. The theorem below (`FEEC.staticFEEC`) is the a priori theory of [AFW2010],
§3.3–§3.4 for the mixed Hodge Laplacian in degree `j`: if the cochain projections `πₕ` onto `Vₕ`
are bounded uniformly in `h` in the graph norm `‖x‖ + ‖d x‖`, `Vₕ` approximates every `x ∈ D(d)`
in the graph norm, the ranges of `dʲ⁻¹` and `dʲ` are closed and the harmonic forms `ℌʲ` are
finite-dimensional, then

1. the inclusion `Vₕ ⊆ W` eventually induces an isomorphism `Hʲ(Vₕ) ≅ Hʲ` ([AFW2010], Thm 3.4)
   and the harmonic gap `μₕ = sup_{q ∈ ℌʲ, ‖q‖ ≤ 1} ‖q - πₕ q‖` tends to `0` (Thm 3.5);
2. the discrete Poincaré inequality `‖v‖ ≤ C ‖d v‖` on `Vₕʲ ⊥ 𝔷ₕʲ` holds with `C` independent of
   `h` (Thm 3.6);
3. the mixed Hodge Laplacian and its Galerkin discretizations are uniquely solvable (Thm 3.8);
4. the discrete solutions are quasi-optimal in the graph norm (Thm 3.9),
   `‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖ ≤ C (E(σ) + E(u) + E(p) + μₕ E(P_𝔅 u))`,
   `E` the graph-norm distance to `Vₕ`, hence converge.

The differential of the complex is encoded as a family `d i j : Wⁱ → Wʲ` of all pairs, zero
unless `j = i + 1`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–§3.4

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology LinearPMap

@[expose] public noncomputable section

namespace FEEC

/-! ### Hilbert complexes and conforming families -/

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

/-- A **conforming family** of `H` along the filter `l` (the refinement `h → 0`):
finite-dimensional subcomplexes `Vₕ` with cochain projections `πₕ`. -/
structure ConformingFamily (κ : Type*) where
  /-- the filter of the refinement `h → 0` -/
  l : Filter κ
  /-- the subcomplexes -/
  V : κ → H.Subcomplex
  [finiteDimensional : ∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
  /-- the cochain projections -/
  π : ∀ h, (V h).CochainProjection

attribute [instance] ConformingFamily.finiteDimensional

/-! ### Cohomology and harmonic forms -/

/-- The cycles `𝔷ⁱ = N(d i (i + 1))`. -/
def cycles (i : ℤ) : Submodule 𝕜 (W i) := (H.d i (i + 1)).ker

/-- The boundaries `𝔅ⁱ = R(d (i - 1) i)`. -/
def boundaries (i : ℤ) : Submodule 𝕜 (W i) := LinearMap.range (H.d (i - 1) i).toFun

/-- The harmonic forms `ℌⁱ = 𝔷ⁱ ∩ N(d (i - 1) i)*`. -/
def harmonic (i : ℤ) : Submodule 𝕜 (W i) := H.cycles i ⊓ (H.d (i - 1) i)†.ker

/-- The cohomology `Hⁱ = 𝔷ⁱ / 𝔅ⁱ`. -/
abbrev cohomology (i : ℤ) : Type _ := H.cycles i ⧸ (H.boundaries i).comap (H.cycles i).subtype

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

/-- The distance `inf_{v ∈ Vⁱ} ‖x - v‖ + ‖y - d i j v‖`; for `y = d x`, the distance from `x` to
`Vⁱ` in the graph norm of `d i j`. -/
def graphDist (i j : ℤ) (x : W i) (y : W j) : ℝ :=
  ⨅ v : S.V i, ‖x - v‖ + ‖y - H.d i j ⟨v, S.le_domain i j v.2⟩‖

/-- The **harmonic gap** `μ = sup_{q ∈ ℌʲ, ‖q‖ ≤ 1} ‖q - π q‖` of a cochain projection. -/
def CochainProjection.harmonicGap {S : H.Subcomplex} (P : S.CochainProjection) (j : ℤ) : ℝ :=
  ⨆ q : {q : H.harmonic j // ‖(q : W j)‖ ≤ 1}, ‖((q : H.harmonic j) : W j) - P.π j q‖

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

/-- The graph-norm error `‖σ - σ'‖ + ‖dσ - dσ'‖ + ‖u - u'‖ + ‖du - du'‖ + ‖p - p'‖`. -/
def mixedError (j : ℤ) (σ σ' : (H.d (j - 1) j).domain) (u u' : (H.d j (j + 1)).domain)
    (p p' : W j) : ℝ :=
  ‖(σ : W (j - 1)) - σ'‖ + ‖H.d (j - 1) j σ - H.d (j - 1) j σ'‖ + ‖(u : W j) - u'‖ +
    ‖H.d j (j + 1) u - H.d j (j + 1) u'‖ + ‖p - p'‖

variable {H} {κ : Type*}

/-- **The conclusions of the static FEEC theorem** in degree `j` for the conforming family `F`,
with constants independent of `h`. -/
structure ConformingFamily.StaticVerdict (F : H.ConformingFamily κ) (j : ℤ) : Prop where
  /-- the inclusion `Vₕ ⊆ W` eventually induces an isomorphism `Hʲ(Vₕ) ≅ Hʲ` -/
  cohomology : ∀ᶠ h in F.l, Function.Bijective ((F.V h).cohomologyIncl j)
  /-- the harmonic gap tends to `0` -/
  harmonicGap : Tendsto (fun h => (F.π h).harmonicGap j) F.l (𝓝 0)
  /-- the uniform discrete Poincaré inequality on `Vₕʲ ⊥ 𝔷ₕʲ` -/
  poincare : ∃ C : ℝ, ∀ (h : κ) (v : W j) (hv : v ∈ (F.V h).V j),
    (∀ z ∈ (F.V h).cycles j, ⟪z, v⟫_𝕜 = 0) →
      ‖v‖ ≤ C * ‖H.d j (j + 1) ⟨v, (F.V h).le_domain j (j + 1) hv⟩‖
  /-- the mixed problem is uniquely solvable -/
  existsUnique (f : W j) : ∃! x : (H.d (j - 1) j).domain × (H.d j (j + 1)).domain × W j,
    H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f x.1 x.2.1 x.2.2
  /-- and so is its Galerkin discretization in `Vₕ` -/
  existsUnique_discrete (h : κ) (f : W j) :
    ∃! x : (H.d (j - 1) j).domain × (H.d j (j + 1)).domain × W j,
      H.IsMixedSolution j ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) f x.1 x.2.1 x.2.2
  /-- the discrete solutions are quasi-optimal in the graph norm, `P_𝔅` the orthogonal
  projection onto the closure of `𝔅ʲ` -/
  quasiOptimal : ∃ C : ℝ, ∀ {f : W j} {σ : (H.d (j - 1) j).domain} {u : (H.d j (j + 1)).domain}
    {p : W j}, H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f σ u p →
    ∀ (h : κ) {σh : (H.d (j - 1) j).domain} {uh : (H.d j (j + 1)).domain} {ph : W j},
    H.IsMixedSolution j ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) f σh uh ph →
    H.mixedError j σ σh u uh p ph ≤ C * ((F.V h).graphDist (j - 1) j σ (H.d (j - 1) j σ) +
      (F.V h).graphDist j (j + 1) u (H.d j (j + 1) u) + (F.V h).graphDist j (j + 1) p 0 +
      (F.π h).harmonicGap j *
        (F.V h).graphDist j (j + 1) ((H.boundaries j).topologicalClosure.starProjection u) 0)
  /-- the discrete solutions converge in the graph norm -/
  converges {f : W j} {σ : (H.d (j - 1) j).domain} {u : (H.d j (j + 1)).domain} {p : W j}
    (hs : H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f σ u p)
    {σh : κ → (H.d (j - 1) j).domain} {uh : κ → (H.d j (j + 1)).domain} {ph : κ → W j}
    (hsh : ∀ h, H.IsMixedSolution j ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) f
      (σh h) (uh h) (ph h)) :
    Tendsto (fun h => H.mixedError j σ (σh h) u (uh h) p (ph h)) F.l (𝓝 0)

end HilbertComplex

/-! ### The theorem -/

/-- **The static FEEC theorem** ([AFW2010], Thms 3.4–3.6, 3.8, 3.9). Let `F` be a conforming
family whose cochain projections are bounded uniformly in the graph norm,
`‖πₕ x‖ + ‖d πₕ x‖ ≤ C (‖x‖ + ‖d x‖)`, and which approximates every `x ∈ D(d)` in the graph norm.
In a degree `j` where the ranges `𝔅ʲ` of `dʲ⁻¹` and `𝔅ʲ⁺¹` of `dʲ` are closed and `ℌʲ` is
finite-dimensional, `F` satisfies the static verdict (`ConformingFamily.StaticVerdict`). -/
theorem staticFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} (F : H.ConformingFamily κ)
    (hπ : ∃ C : ℝ, ∀ (h : κ) (i : ℤ) (x : (H.d i (i + 1)).domain),
      ‖(F.π h).π i x‖ +
        ‖H.d i (i + 1) ⟨(F.π h).π i x, (F.V h).le_domain i (i + 1) ((F.π h).mem i x)⟩‖ ≤
          C * (‖(x : W i)‖ + ‖H.d i (i + 1) x‖))
    (happrox : ∀ (i : ℤ) (x : (H.d i (i + 1)).domain),
      Tendsto (fun h => (F.V h).graphDist i (i + 1) x (H.d i (i + 1) x)) F.l (𝓝 0))
    (j : ℤ) (hj : IsClosed (H.boundaries j : Set (W j)))
    (hj' : IsClosed (H.boundaries (j + 1) : Set (W (j + 1)))) [FiniteDimensional 𝕜 (H.harmonic j)] :
    F.StaticVerdict j := by
  sorry

end FEEC
