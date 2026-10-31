module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The static FEEC theorem

Finite element exterior calculus ([AFW2006], [AFW2010]) approximates a Hilbert complex
`⋯ → Wʲ⁻¹ → Wʲ → Wʲ⁺¹ → ⋯` of closed densely defined operators `d` by finite-dimensional
subcomplexes `Vₕ` of its domain complex `Vⁱ = D(dⁱ)`, normed by the graph norm
`‖x‖_V = (‖x‖² + ‖d x‖²)^½`. The theorem below (`FEEC.staticFEEC`) is the a priori theory of
[AFW2010], §3.3–§3.4 for the mixed Hodge Laplacian in degree `j`: if the cochain projections
`πₕ : V → Vₕ` are bounded in the graph norm uniformly in `h` in degrees `j - 1` and `j` and the
ranges of `dʲ⁻¹` and `dʲ` are closed, then, with a constant `C` independent of `h`,

1. (Thm 3.5) `dist(q, ℌₕʲ) ≤ ‖q - πₕ q‖` on the harmonic forms `ℌʲ`, and
   `‖q - P_ℌ q‖ ≤ ‖P_ℌ q - πₕ P_ℌ q‖` on the discrete harmonic forms `ℌₕʲ`;
2. (Thm 3.4) `πₕ` induces a left inverse `Hʲ → Hʲ(Vₕ)` of the map induced by the inclusion
   `Vₕ ⊆ W`; if `‖q - πₕ q‖ < ‖q‖` on `ℌʲ \ 0`, both are isomorphisms; if `Vₕ` approximates `Vʲ`
   and `ℌʲ` is finite-dimensional, the harmonic gap `μₕ = sup_{q ∈ ℌʲ, ‖q‖ ≤ 1} ‖q - πₕ q‖` tends
   to `0` (Thm 3.5) and they are eventually isomorphisms;
3. (Thm 3.6) the discrete Poincaré inequality `‖v‖_V ≤ C ‖d v‖` holds on `Vₕʲ ⊥ 𝔷ₕʲ`;
4. (Thm 3.8) the mixed Hodge Laplacian and its Galerkin discretizations are uniquely solvable, the
   discrete mixed form satisfies the inf-sup condition uniformly in `h`, and the discrete solutions
   are bounded by `C ‖f‖`;
5. (Thm 3.9) the discrete solutions are quasi-optimal,
   `‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖ ≤ C (E(σ) + E(u) + E(p) + μₕ E(P_𝔅 u))`,
   `E` the graph-norm distance to `Vₕ`; so they converge where `Vₕ` approximates `Vʲ⁻¹` and `Vʲ`.

`FEEC.staticFEEC_uniform` states that `C` depends only on the bound `c` of `πₕ` and the Poincaré
constant `c_P` of `‖v‖_V ≤ c_P ‖d v‖` on `Vⁱ ⊥ 𝔷ⁱ` in degrees `j - 1` and `j` (which exists iff the
ranges are closed): `C = Φ(c, c_P)` for one function `Φ` and every complex, family and degree.

Conversely ([AFW2010], Thm 3.7), `FEEC.exists_cochainProjection`: a finite-dimensional
subcomplex with the discrete Poincaré inequality `‖v‖_V ≤ c₁ ‖d v‖` on `Vₕⁱ ⊥ 𝔷ₕⁱ` and the bound
`‖q‖ ≤ c₂ ‖P_ℌ q‖` on `ℌₕⁱ` in every degree has a cochain projection bounded by
`(1 + c₁)(1 + c₂)` in the graph norm (no closed range needed); with Thm 3.6 and (30),
`FEEC.exists_subcomplexFamily_iff`: for a complex with closed ranges, uniformly bounded cochain
projections exist iff these two conditions hold uniformly in `h`.

The differential of the complex is encoded as a family `d i j : Wⁱ → Wʲ` of all pairs, zero
unless `j = i + 1`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–§3.4 (Thm 3.7 for the converse)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology LinearPMap

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
  poincare : ∀ (h : κ) (v : W j) (hv : v ∈ (F.V h).V j),
    (∀ z ∈ (F.V h).cycles j, ⟪z, v⟫_𝕜 = 0) →
      H.graphNorm j (j + 1) ⟨v, (F.V h).le_domain j (j + 1) hv⟩ ≤
        C * ‖H.d j (j + 1) ⟨v, (F.V h).le_domain j (j + 1) hv⟩‖
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

/-! ### The theorem -/

/-- **The static FEEC theorem** ([AFW2010], Thms 3.4–3.6, 3.8, 3.9). Let `F` be a family of
subcomplexes whose cochain projections are bounded uniformly in the graph norm in degrees `j - 1`
and `j`. If the ranges `𝔅ʲ` of `dʲ⁻¹` and `𝔅ʲ⁺¹` of `dʲ` are closed, `F` satisfies the static
verdict in degree `j` (`SubcomplexFamily.StaticVerdict`) with a constant independent of `h`. -/
theorem staticFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} (F : H.SubcomplexFamily κ) (j : ℤ)
    (hπ : F.IsGraphBounded (j - 1)) (hπ' : F.IsGraphBounded j)
    (hj : IsClosed (H.boundaries j : Set (W j)))
    (hj' : IsClosed (H.boundaries (j + 1) : Set (W (j + 1)))) : ∃ C, F.StaticVerdict j C := by
  sorry

/-- **The constants of the static FEEC theorem** depend only on the bound `c` of the cochain
projections and the Poincaré constant `c_P` ([AFW2010], §3.3–§3.4): one function `Φ` serves every
Hilbert complex, family of subcomplexes and degree. -/
theorem staticFEEC_uniform : ∃ Φ : ℝ → ℝ → ℝ, ∀ {𝕜 : Type u} [RCLike 𝕜] {W : ℤ → Type v}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    {κ : Type w} {H : HilbertComplex 𝕜 W} (F : H.SubcomplexFamily κ) (j : ℤ) {c cP : ℝ},
    F.IsGraphBoundedBy (j - 1) c → F.IsGraphBoundedBy j c →
    H.PoincareBy (j - 1) cP → H.PoincareBy j cP → F.StaticVerdict j (Φ c cP) := by
  sorry

/-- **Bounded cochain projections from discrete stability** ([AFW2010], Thm 3.7). Let `S` be a
finite-dimensional subcomplex. If in every degree `i` the discrete Poincaré inequality
`‖v‖_V ≤ c₁ⁱ ‖d v‖` holds on `Vⁱ ⊥ 𝔷ₕⁱ` and `‖q‖ ≤ c₂ⁱ ‖P_ℌ q‖` holds on `ℌₕⁱ`, then `S` has a
cochain projection bounded in the graph norm by `(1 + c₁ⁱ)(1 + c₂ⁱ)` in every degree `i`. -/
theorem exists_cochainProjection {H : HilbertComplex 𝕜 W} (S : H.Subcomplex)
    [∀ i, FiniteDimensional 𝕜 (S.V i)] {c₁ c₂ : ℤ → ℝ} (hc₁ : ∀ i, 0 ≤ c₁ i)
    (hc₂ : ∀ i, 0 ≤ c₂ i) (hP : ∀ i, S.PoincareBy i (c₁ i))
    (hH : ∀ i, S.HarmonicBoundBy i (c₂ i)) :
    ∃ P : S.CochainProjection, ∀ i (x : (H.d i (i + 1)).domain),
      H.graphNorm i (i + 1) ⟨P.π i x, S.le_domain i (i + 1) (P.π i x).2⟩ ≤
        (1 + c₁ i) * (1 + c₂ i) * H.graphNorm i (i + 1) x := by
  sorry

/-- **Uniformly bounded cochain projections exist iff discrete stability holds uniformly**
([AFW2010], Thms 3.6, 3.7 and (30)). Let `Vₕ` be finite-dimensional subcomplexes of a complex
whose ranges are closed. A family of subcomplexes on `Vₕ` with cochain projections bounded in
the graph norm uniformly in `h` in every degree exists iff in every degree the discrete Poincaré
inequality and the harmonic bound hold with constants independent of `h`. -/
theorem exists_subcomplexFamily_iff {κ : Type*} {H : HilbertComplex 𝕜 W} (l : Filter κ)
    (V : κ → H.Subcomplex) [∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
    (hcr : ∀ i, IsClosed (H.boundaries i : Set (W i))) :
    (∃ F : H.SubcomplexFamily κ, F.l = l ∧ F.V = V ∧ ∀ i, F.IsGraphBounded i) ↔
      ∀ i, ∃ c₁ c₂ : ℝ, ∀ h, (V h).PoincareBy i c₁ ∧ (V h).HarmonicBoundBy i c₂ := by
  sorry

end FEEC
