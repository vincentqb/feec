# Formalization blueprint: Quenneville-Bélair (2015), *A New Approach to Finite Element Simulations of General Relativity*

**Target:** Lean 4 + Mathlib, pinned at `6e2a148e` (see `lakefile.toml`). The project lives at `/local/home/quennv/feec`.

**Status of this document:**
- The foundation code in §2 compiles with no errors, no warnings and no `sorry`. Checked with `lake env lean /tmp/feec_scratch_architect/Foundation.lean`; `#print axioms` shows only `propext, Classical.choice, Quot.sound`.
- `/tmp/feec_scratch_architect/Sig.lean` is the foundation plus `sorry`-stubbed statements for the new signatures. It also elaborates cleanly: `adjoint_adjoint`, the closed range theorem, `skewAdjoint_restrict`, `constraint_propagation`, `cor_4_5`, `waveOp_isSkewAdjoint`, `brezzi`, `hodge_V` and `poincare_iff`.
- Signatures marked **[S]** below are already proved, sorry-free, in the cited scratch file. Port them; do not re-derive them.

---

## 1. Scope

### 1.1 What we formalize

The thesis is mostly abstract functional analysis and linear algebra, and that is where the formal value is. Priorities, highest first:

| Tier | Content | Thesis ids |
|---|---|---|
| **A (core)** | Unbounded-operator facts: (4.1a–d), T†† = T, density of D(T†), closed range theorem, closed kernels | §4.1 |
| A | Hilbert complexes: B ⊆ Z, the Hodge decomposition (in V; in W via closures, and exact under closed range), harmonic forms, Poincaré ⇔ closed range, compactness ⇒ finite-dimensional ℌ | Thm 4.1, 4.2, §4.2 |
| A | Skew-adjoint restriction to an invariant subspace, energy uniqueness, constraint propagation | Thm 4.4, Cor 4.5, §4.3, Props 4.16, 4.18 (abstract) |
| A | Hodge wave operator: skew-adjointness **without closed range**, density of D(L), weak form, weak uniqueness, strong ⇔ weak | Thm 4.6, 4.7 |
| A | Lax–Milgram restatement, Babuška–Nečas (corrected), quasi-optimality, Brezzi (corrected) | Thm 4.8–4.11 |
| A | Lemma 4.12 (corrected), Prop 4.13 (constant 1/√12), elliptic projection, Thm 4.14 (corrected), convergence | §4.6 |
| A | BGG Props 5.1–5.4, Prop 5.6, Thm 5.5 (quantitative, under corrected hypotheses) | Ch 5 |
| A | Ch 6: energy identity, Prop 6.1 (both parts, corrected), Prop 6.2 (refuted, then corrected), Prop 6.3, a new conditional convergence theorem | Ch 6 |
| B | Ch 3 matrix/jet identities: Props 3.2, 3.3, the Weyl block form, Prop 3.1, Lemma 3.5, Prop 3.4 (jet level), the Prop 3.6 algebraic core, the §3.5 plane wave | Ch 3 |
| B | Ch 2 algebraic curvature and symbol-level linearized gravity: the [10] Bianchi lemma, Ricci symmetry, G=0 ⇔ Ric=0 for n≠2, Thm 2.3 identities, gauge invariance, corrected Prop 2.4(b), TT form, corrected Prop 2.6, geodesic-deviation accelerations | Ch 2 |
| B | Ch 4.7 polynomial algebra: the Koszul homotopy core, and the counterexample showing that two of the four §4.10 discretizations are not subcomplexes | §4.7, §4.10 |
| B | Ch 7: discrete equivalence of the full and reduced Crank–Nicolson (CN) schemes, uniqueness, energy conservation, MINRES symmetrization, plane-wave amplitudes, step counts | Ch 7 |

### 1.2 Out of scope, and why

- **Sobolev spaces on domains** (H¹, H(curl), H(div), traces, Rellich, regular decompositions), finite element spaces, meshes, degrees of freedom, Bramble–Hilbert. Mathlib has Sobolev spaces only as tempered distributions on all of ℝⁿ, with no domains, weak derivatives or traces. Every concrete complex therefore enters only as an *instance* of an abstract structure, with its analytic facts as fields.

  Consequence: Props 5.7–5.9, §5.3 and §6.3 are formalized only in their abstract or algebraic cores. These are the degree-of-freedom lemma behind Prop 5.7, the local-scaling form of Prop 5.8, the polynomial counterexample to Prop 5.9 (optional), and the pointwise trace identity. The bounded-domain counterexample to Props 4.17 and 4.19 stays as prose.
- **Hille–Yosida, Stone, C₀-semigroups.** Mathlib has none of these, so existence of time evolutions is the explicit hypothesis `WellPosedExistence L T Adm` (or `WellPosedHom`). It is **never an `axiom` and never a `sorry`.** Uniqueness, energy estimates and constraint propagation are *proved* with the energy method. The time-reversal and reducing-subspace necessity argument also needs a unitary group; it is optional, under a `UnitaryGroupGenerator` hypothesis structure.
- **Pseudo-Riemannian geometry.** Mathlib's Levi-Civita machinery is Riemannian only. Ch 2 is done in components on `Fin n` and `Fin 4`, at the symbol/jet level, with optional calculus bridges. The general Bianchi II, naturality, flows and the nonlinear EB system (§3.4) are out of scope.
- **Numerics** in Ch 7 (rates, tables) are not formalizable. Only exact arithmetic facts are checked.
- **Bibliography** fixes go in the README and docs, not in Lean.

### 1.3 Policy for missing theory

1. Missing analytic existence (semigroups, elliptic solvers, wave solvers, regular decompositions) is a hypothesis predicate or a structure field, with a docstring naming the classical theorem it stands for.
2. Missing *provable* facts are proved in a dedicated module rather than assumed: T†† = T, the closed range theorem, density of D(L), Brezzi.
- **Temporary fallback:** while `Feec/Ch4/Adjoint.lean` is unfinished, a downstream theorem may take `h : H.d0†† = H.d0` as an explicit hypothesis. The final pass discharges it.
3. A CI gate rejects any `axiom`, `sorry` or `admit`: `#print axioms` on every main theorem must show only the three standard axioms.

---

## 2. Core modeling design

Three models of a Hilbert complex coexist. Each module uses whichever fits.

| Model | Structure | Used for | Why |
|---|---|---|---|
| Unbounded (W-level) | `HilbertComplex2`, `UHilbertComplex` (`LinearPMap`s) | §4.1–4.4, Thm 4.6/4.7, constraint propagation | Adjoints d* are genuinely unbounded; matches the thesis |
| Bounded domain complex (AFW) | `HilbertComplex V W` (V carries the graph inner product, ι : V → W) | Hodge decomposition, Poincaré, closedness, Prop 5.1 | All of `ᗮ`, `starProjection` and Banach work directly in V |
| Algebraic segment ("type = domain") | `Complex3`, `BGGData` (linear maps; types carry the **W** inner product) | Prop 4.13, Thm 4.14, Ch 5.2, Ch 6, Ch 7 | Pure algebra and inner products; graph norms stay explicit (`nV2`) |

Bridges, built inside the consuming modules:
- `HilbertComplex2.toComplex3 : Complex3 H.d0.domain H.d1.domain W2`. Here d0 corestricts via `map_mem`, and the subtypes carry the W inner product. The weak form of Thm 4.7 is stated through it.
- Graph of a closed `LinearPMap` → complete subspace of `WithLp 2 (E × F)`. This is in `/tmp/feec_scratch_api/Design.lean`.

Conventions:
- Real scalars throughout, and `open scoped RealInnerProductSpace`.
- Segments are indexed `k, k+1, k+2`; never write `k-1`.
- Files are non-module, matching `Feec/Basic.lean`.
- Use `(f : E →L F).ker` and `.range`, `Submodule.starProjection` and `orthogonalProjectionOnto`.

### 2.1 Foundation code (compiles; split into `Feec/Foundation/{Operators,Evolution,Complex,BGG,Tensor}.lean` as indicated, each repeating `open scoped RealInnerProductSpace`, `open Set`, `noncomputable section`, `namespace Feec`)

```lean
import Mathlib

/-!
# Feec foundation: shared definitions

Split in the repository as
* `Feec/Foundation/Operators.lean`  (§A)
* `Feec/Foundation/Evolution.lean`  (§B)
* `Feec/Foundation/Complex.lean`    (§C, §D, §E)
* `Feec/Foundation/BGG.lean`        (§F)
* `Feec/Foundation/Tensor.lean`     (§G)

Conventions: real scalars only; `open scoped RealInnerProductSpace` (so `⟪x, y⟫ = ⟪x, y⟫_ℝ`);
complexes indexed by explicit segments `k, k+1, k+2` (no `k-1`).
No `axiom`, no `sorry`: missing theory (Hille–Yosida/Stone, Sobolev spaces, traces)
enters only as explicit hypotheses / structure fields.
-/

open scoped RealInnerProductSpace
open Set

noncomputable section

namespace Feec

/-! ## §A. Unbounded operators -/

section Operators
open LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Skew-adjoint (possibly unbounded) operator: `A† = -A` (equal domains). -/
def IsSkewAdjoint [CompleteSpace E] (A : E →ₗ.[ℝ] E) : Prop := A† = -A

/-- Skew-symmetry on the domain: `⟪A x, y⟫ = -⟪x, A y⟫`. (Weaker than skew-adjoint;
enough for all energy/uniqueness/constraint-propagation arguments.) -/
def IsSkewSymm (A : E →ₗ.[ℝ] E) : Prop :=
  ∀ x y : A.domain, ⟪A x, (y : E)⟫ = -⟪(x : E), A y⟫

/-- Restriction of `L` to an invariant subspace `K`, as an operator `K → K`
(domain `D(L) ∩ K`). Used by Thm 4.4. -/
def restrictTo (L : E →ₗ.[ℝ] E) (K : Submodule ℝ E)
    (hinv : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) : K →ₗ.[ℝ] K where
  domain := L.domain.comap K.subtype
  toFun :=
    { toFun := fun x => ⟨L ⟨(x : K), x.2⟩, hinv ⟨_, x.2⟩ (x : K).2⟩
      map_add' := fun x y => by ext; simp [← LinearPMap.map_add]; rfl
      map_smul' := fun c x => by ext; simp [← LinearPMap.map_smul]; rfl }

/-- (4.1a) `(range T)ᗮ = ker T†` for densely defined `T` (no closedness needed). -/
theorem orth_range_eq_ker_adjoint {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) :
    (LinearMap.range T.toFun)ᗮ = T†.ker := by
  ext y
  constructor
  · intro hy
    have key : ∀ x : T.domain, ⟪(0 : E), (x : E)⟫ = ⟪y, T x⟫ := fun x => by
      have := (Submodule.mem_orthogonal _ _).1 hy (T x) ⟨x, rfl⟩
      rw [inner_zero_left, real_inner_comm, this]
    have hmem : y ∈ T†.domain := mem_adjoint_domain_of_exists y ⟨0, key⟩
    rw [LinearPMap.mem_ker_iff]
    exact ⟨⟨y, hmem⟩, rfl, adjoint_apply_eq hT ⟨y, hmem⟩ key⟩
  · intro hy
    rw [LinearPMap.mem_ker_iff] at hy
    obtain ⟨y', rfl, hy0⟩ := hy
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    have := (adjoint_isFormalAdjoint hT) y' x
    rw [hy0] at this
    simpa [real_inner_comm] using this.symm

/-- Skew-adjoint ⇒ skew-symmetric. -/
theorem IsSkewAdjoint.isSkewSymm [CompleteSpace E] {L : E →ₗ.[ℝ] E}
    (hD : Dense (L.domain : Set E)) (hL : IsSkewAdjoint L) : IsSkewSymm L := by
  intro x y
  have hle : -L ≤ L† := hL ▸ le_rfl
  have hx : (x : E) ∈ L†.domain := hle.1 x.2
  have h1 := adjoint_isFormalAdjoint hD ⟨x, hx⟩ y
  have h2 : L† ⟨x, hx⟩ = -L x := (hle.2 (x := x) (y := ⟨x, hx⟩) rfl).symm
  rw [h2, inner_neg_left] at h1
  linarith

end Operators

/-! ## §B. Evolution problems: solutions and the well-posedness hypothesis -/

section Evolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strong solution of `U' = L U + F` on `[0,T]` with `U 0 = U₀`.
Derivatives are within `Icc 0 T` (one-sided at the endpoints). Continuity of `U` in `E`
follows from `deriv`; graph-norm continuity is NOT part of the predicate (no module needs it). -/
structure IsStrongSolution (L : E →ₗ.[ℝ] E) (T : ℝ) (U₀ : E) (F U : ℝ → E) : Prop where
  mem : ∀ t ∈ Icc 0 T, U t ∈ L.domain
  deriv : ∀ t (ht : t ∈ Icc 0 T), HasDerivWithinAt U (L ⟨U t, mem t ht⟩ + F t) (Icc 0 T) t
  init : U 0 = U₀

/-- **Explicit hypothesis standing in for Thm 4.3 (Hille–Yosida / Stone), which Mathlib lacks.**
For every initial datum in `D(L)` and every admissible forcing there is a strong solution.
`Adm` abstracts the class "`C([0,T];X) ∩ (W^{1,1}(0,T;X) ∪ L¹(0,T;D(L)))`".
Never assumed as an `axiom`; always a theorem hypothesis. Uniqueness is *proved* (energy). -/
def WellPosedExistence (L : E →ₗ.[ℝ] E) (T : ℝ) (Adm : (ℝ → E) → Prop) : Prop :=
  ∀ U₀ ∈ L.domain, ∀ F, Adm F → ∃ U, IsStrongSolution L T U₀ F U

/-- Homogeneous version (`F = 0`), the form used in Thm 4.6. -/
def WellPosedHom (L : E →ₗ.[ℝ] E) (T : ℝ) : Prop :=
  ∀ U₀ ∈ L.domain, ∃ U, IsStrongSolution L T U₀ 0 U

/-- Energy lemma: if `⟪e', e⟫ = 0` on `[0,T)` then `e(0) = 0` forces `e ≡ 0` on `[0,T]`.
The single engine behind every uniqueness statement (Thm 4.3/4.6/4.7, Cor 4.5, Ch 6). -/
theorem energy_zero {e e' : ℝ → E} {T : ℝ}
    (hcont : ContinuousOn e (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (e' t) (Ici t) t)
    (horth : ∀ t ∈ Ico 0 T, ⟪e' t, e t⟫ = 0) (h0 : e 0 = 0) :
    ∀ t ∈ Icc 0 T, e t = 0 := by
  have hc : ∀ t ∈ Icc (0:ℝ) T, ‖e t‖ ^ 2 = ‖e 0‖ ^ 2 := by
    refine constant_of_has_deriv_right_zero (f := fun t => ‖e t‖ ^ 2)
      (hcont.norm.pow 2) ?_
    intro t ht
    have := (hd t ht).norm_sq
    rw [real_inner_comm, horth t ht, mul_zero] at this; exact this
  intro t ht
  simpa [h0] using hc t ht

end Evolution

/-! ## §C. Unbounded Hilbert complexes (the thesis' / Brüning–Lesch picture) -/

/-- A length-2 Hilbert complex `W0 --d0--> W1 --d1--> W2` of closed, densely defined operators
(§4.4 setup). Closed range is **not** part of the structure (see `HilbertComplex2.ClosedRange`). -/
structure HilbertComplex2 (W0 W1 W2 : Type*)
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2] where
  d0 : W0 →ₗ.[ℝ] W1
  d1 : W1 →ₗ.[ℝ] W2
  dense0 : Dense (d0.domain : Set W0)
  dense1 : Dense (d1.domain : Set W1)
  closed0 : d0.IsClosed
  closed1 : d1.IsClosed
  /-- `d0 V0 ⊂ V1` (missing from the thesis' definition). -/
  map_mem : ∀ x : d0.domain, d0 x ∈ d1.domain
  comp_zero : ∀ x : d0.domain, d1 ⟨d0 x, map_mem x⟩ = 0

namespace HilbertComplex2
open LinearPMap

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    (H : HilbertComplex2 W0 W1 W2)

/-- Closed-range hypothesis (a closed complex in AFW's sense). -/
def ClosedRange : Prop :=
  IsClosed (LinearMap.range H.d0.toFun : Set W1) ∧ IsClosed (LinearMap.range H.d1.toFun : Set W2)

/-- Domain of the middle space of the Hodge wave operator: `V1 ∩ V1*`. -/
def midDomain : Submodule ℝ W1 := H.d1.domain ⊓ H.d0†.domain

/-- The product space `W = W0 × W1 × W2` with the ℓ² inner product. -/
abbrev Tot (W0 W1 W2 : Type*) := WithLp 2 (W0 × WithLp 2 (W1 × W2))

/-- coordinates of `Tot` -/
def tot (W0 W1 W2 : Type*)
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] : Tot W0 W1 W2 ≃ₗ[ℝ] W0 × W1 × W2 :=
  (WithLp.linearEquiv 2 ℝ _).trans ((LinearEquiv.refl ℝ W0).prodCongr (WithLp.linearEquiv 2 ℝ _))
/-- domain `V0 × (V1 ∩ V1*) × V2*` of the Hodge wave operator, as a submodule of `Tot`. -/
def domL : Submodule ℝ (Tot W0 W1 W2) :=
  (H.d0.domain.prod (H.midDomain.prod H.d1†.domain)).comap (tot W0 W1 W2).toLinearMap
/-- the coordinate projections of `domL` into the operator domains -/
def pr0 : H.domL →ₗ[ℝ] H.d0.domain :=
  LinearMap.codRestrict _ ((LinearMap.fst ℝ _ _).comp ((tot W0 W1 W2).toLinearMap.comp
    H.domL.subtype)) (fun x => x.2.1)
def prV1 : H.domL →ₗ[ℝ] H.d1.domain :=
  LinearMap.codRestrict _ ((LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    ((tot W0 W1 W2).toLinearMap.comp H.domL.subtype))) (fun x => x.2.2.1.1)
def prV1s : H.domL →ₗ[ℝ] H.d0†.domain :=
  LinearMap.codRestrict _ ((LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    ((tot W0 W1 W2).toLinearMap.comp H.domL.subtype))) (fun x => x.2.2.1.2)
def prV2s : H.domL →ₗ[ℝ] H.d1†.domain :=
  LinearMap.codRestrict _ ((LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    ((tot W0 W1 W2).toLinearMap.comp H.domL.subtype))) (fun x => x.2.2.2)

/-- Hodge wave operator (4.5): `L(σ,u,ρ) = (-d0* u, d0 σ + d1* ρ, -d1 u)` on `domL`. -/
def waveOp : Tot W0 W1 W2 →ₗ.[ℝ] Tot W0 W1 W2 where
  domain := H.domL
  toFun := (tot W0 W1 W2).symm.toLinearMap.comp
    ((-(H.d0†.toFun.comp H.prV1s)).prod
      (((H.d0.toFun.comp H.pr0) + (H.d1†.toFun.comp H.prV2s)).prod
        (-(H.d1.toFun.comp H.prV1))))

end HilbertComplex2

/-- ℕ-indexed unbounded Hilbert complex (W-level). `segment k` gives the length-2 piece. -/
structure UHilbertComplex (W : ℕ → Type*)
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    where
  d : ∀ k, W k →ₗ.[ℝ] W (k + 1)
  dense : ∀ k, Dense ((d k).domain : Set (W k))
  closed : ∀ k, (d k).IsClosed
  map_mem : ∀ k (x : (d k).domain), d k x ∈ (d (k + 1)).domain
  comp_zero : ∀ k (x : (d k).domain), d (k + 1) ⟨d k x, map_mem k x⟩ = 0

namespace UHilbertComplex

variable {W : ℕ → Type*}
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    (C : UHilbertComplex W)

def segment (k : ℕ) : HilbertComplex2 (W k) (W (k + 1)) (W (k + 2)) where
  d0 := C.d k
  d1 := C.d (k + 1)
  dense0 := C.dense k
  dense1 := C.dense (k + 1)
  closed0 := C.closed k
  closed1 := C.closed (k + 1)
  map_mem := C.map_mem k
  comp_zero := C.comp_zero k

end UHilbertComplex

/-! ## §D. Bounded "domain complex" (AFW): `V k` carries the graph inner product -/

/-- `V k` = domain of `d k` with its graph inner product, `ι k : V k → W k` the inclusion.
All Hodge/Poincaré/cohomology arguments live in `V` using Mathlib's `ᗮ`/`starProjection`. -/
structure HilbertComplex (V W : ℕ → Type*)
    [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)] [∀ k, CompleteSpace (V k)]
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    where
  ι : ∀ k, V k →L[ℝ] W k
  ι_injective : ∀ k, Function.Injective (ι k)
  d : ∀ k, V k →L[ℝ] V (k + 1)
  d_comp_d : ∀ k, (d (k + 1)).comp (d k) = 0
  inner_graph : ∀ k (u v : V k),
    ⟪u, v⟫ = ⟪ι k u, ι k v⟫ + ⟪ι (k + 1) (d k u), ι (k + 1) (d k v)⟫

namespace HilbertComplex

variable {V W : ℕ → Type*}
    [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)] [∀ k, CompleteSpace (V k)]
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    (C : HilbertComplex V W)

/-- cycles `𝔷^k = ker d^k ⊂ V^k` -/
def Z (k : ℕ) : Submodule ℝ (V k) := (C.d k).ker
/-- boundaries `𝔅^{k+1} = d^k V^k ⊂ V^{k+1}` -/
def B (k : ℕ) : Submodule ℝ (V (k + 1)) := (C.d k).range
/-- harmonic forms `ℌ^{k+1} = 𝔅^{k+1}ᗮ ∩ 𝔷^{k+1}` -/
def H (k : ℕ) : Submodule ℝ (V (k + 1)) := (C.B k)ᗮ ⊓ C.Z (k + 1)
/-- closed complex at position `k → k+1` -/
def IsClosedAt (k : ℕ) : Prop := IsClosed (C.B k : Set (V (k + 1)))

theorem d_d (k : ℕ) (u : V k) : C.d (k + 1) (C.d k u) = 0 := by
  simpa using congrArg (fun f => f u) (C.d_comp_d k)

theorem B_le_Z (k : ℕ) : C.B k ≤ C.Z (k + 1) := by
  rintro _ ⟨u, rfl⟩; exact C.d_d k u

theorem isClosed_Z (k : ℕ) : IsClosed (C.Z k : Set (V k)) := (C.d k).isClosed_ker

instance (k : ℕ) : (C.Z k).HasOrthogonalProjection := by
  have : CompleteSpace (C.Z k) := (C.isClosed_Z k).completeSpace_coe
  infer_instance

/-- On cycles the `V`- and `W`-inner products agree. -/
theorem inner_of_mem_Z {k : ℕ} {u v : V k} (hu : u ∈ C.Z k) :
    ⟪u, v⟫ = ⟪C.ι k u, C.ι k v⟫ := by
  have : C.d k u = 0 := hu
  simp [C.inner_graph, this]

/-- A subcomplex: subspaces `Vh k` with `d (Vh k) ⊆ Vh (k+1)`. -/
structure Subcomplex where
  Vh : ∀ k, Submodule ℝ (V k)
  d_mem : ∀ k, ∀ u ∈ Vh k, C.d k u ∈ Vh (k + 1)

/-- Bounded cochain projections onto a subcomplex (AFW 2010, Thm 5.9 abstracted). -/
structure CochainProjection (S : C.Subcomplex) where
  π : ∀ k, V k →L[ℝ] V k
  mem : ∀ k u, π k u ∈ S.Vh k
  proj : ∀ k, ∀ u ∈ S.Vh k, π k u = u
  comm : ∀ k u, C.d k (π k u) = π (k + 1) (C.d k u)

end HilbertComplex

/-! ## §E. Algebraic complex segment with W-inner products ("type = domain" model)

Used where only algebra + inner products are needed (Prop 4.13, Thm 4.14, Ch 5.2, Ch 6.2, Ch 7):
each type carries the **W** inner product and `d` is a linear map on the domain type.
Graph norms are explicit functions. -/

structure Complex3 (X0 X1 X2 : Type*) [AddCommGroup X0] [Module ℝ X0]
    [AddCommGroup X1] [Module ℝ X1] [AddCommGroup X2] [Module ℝ X2] where
  d0 : X0 →ₗ[ℝ] X1
  d1 : X1 →ₗ[ℝ] X2
  d1_d0 : ∀ x, d1 (d0 x) = 0

namespace Complex3

variable {X0 X1 X2 : Type*}
  [NormedAddCommGroup X0] [InnerProductSpace ℝ X0]
  [NormedAddCommGroup X1] [InnerProductSpace ℝ X1]
  [NormedAddCommGroup X2] [InnerProductSpace ℝ X2]
  (C : Complex3 X0 X1 X2)

/-- skew form `a(σ,u,ρ; τ,v,μ)` of the weak Hodge wave (4.7). -/
def a (σ : X0) (u : X1) (ρ : X2) (τ : X0) (v : X1) (μ : X2) : ℝ :=
  -⟪u, C.d0 τ⟫ + ⟪C.d0 σ, v⟫ + ⟪ρ, C.d1 v⟫ - ⟪C.d1 u, μ⟫

/-- `A = (·,·)_W + a` (the shifted form of §4.6). -/
def bigA (σ : X0) (u : X1) (ρ : X2) (τ : X0) (v : X1) (μ : X2) : ℝ :=
  ⟪σ, τ⟫ + ⟪u, v⟫ + ⟪ρ, μ⟫ + C.a σ u ρ τ v μ

/-- squared `V`-norm on `V0 × V1 × W2`. -/
def nV2 (σ : X0) (u : X1) (ρ : X2) : ℝ :=
  ‖σ‖ ^ 2 + ‖C.d0 σ‖ ^ 2 + ‖u‖ ^ 2 + ‖C.d1 u‖ ^ 2 + ‖ρ‖ ^ 2

theorem a_self (σ : X0) (u : X1) (ρ : X2) : C.a σ u ρ σ u ρ = 0 := by
  simp only [a, real_inner_comm (C.d0 σ) u, real_inner_comm (C.d1 u) ρ]; ring

/-- A subcomplex of the algebraic segment. -/
structure Sub where
  V0h : Submodule ℝ X0
  V1h : Submodule ℝ X1
  V2h : Submodule ℝ X2
  d0_mem : ∀ σ ∈ V0h, C.d0 σ ∈ V1h
  d1_mem : ∀ u ∈ V1h, C.d1 u ∈ V2h

end Complex3

/-! ## §F. BGG data (Ch 5–6): two complexes linked by `S₀, S₁` -/

/-- Top complex `V0 → V1 → W2`, bottom complex `Ṽ0 → Ṽ1 → W̃2`, connecting maps
`S0 : Ṽ0 → V1`, `S1 : Ṽ1 → W2`, anticommuting. Algebraic core only; analytic hypotheses
(closed ranges, continuity, completeness, regularity `d¹V¹ ⊆ d¹S₀Ṽ⁰`) are added per theorem. -/
structure BGGData (V0 V1 W2 Vt0 Vt1 Wt2 : Type*)
    [AddCommGroup V0] [Module ℝ V0] [AddCommGroup V1] [Module ℝ V1]
    [AddCommGroup W2] [Module ℝ W2] [AddCommGroup Vt0] [Module ℝ Vt0]
    [AddCommGroup Vt1] [Module ℝ Vt1] [AddCommGroup Wt2] [Module ℝ Wt2] where
  d0 : V0 →ₗ[ℝ] V1
  d1 : V1 →ₗ[ℝ] W2
  dt0 : Vt0 →ₗ[ℝ] Vt1
  dt1 : Vt1 →ₗ[ℝ] Wt2
  S0 : Vt0 →ₗ[ℝ] V1
  S1 : Vt1 →ₗ[ℝ] W2
  d1_d0 : ∀ σ, d1 (d0 σ) = 0
  dt1_dt0 : ∀ φ, dt1 (dt0 φ) = 0
  anticomm : ∀ φ, d1 (S0 φ) = -S1 (dt0 φ)

namespace BGGData

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [AddCommGroup V0] [Module ℝ V0] [AddCommGroup V1] [Module ℝ V1]
  [AddCommGroup W2] [Module ℝ W2] [AddCommGroup Vt0] [Module ℝ Vt0]
  [AddCommGroup Vt1] [Module ℝ Vt1] [AddCommGroup Wt2] [Module ℝ Wt2]
  (D : BGGData V0 V1 W2 Vt0 Vt1 Wt2)

/-- exactness hypotheses, stated separately so that they appear explicitly in theorems -/
def ExactTop : Prop := LinearMap.ker D.d1 = LinearMap.range D.d0
def ExactBot : Prop := LinearMap.ker D.dt1 = LinearMap.range D.dt0

/-- `Γ = {(σ, φ) | d σ = S φ}` -/
def Γ : Submodule ℝ (V0 × Vt0) :=
  LinearMap.ker (D.d0.comp (LinearMap.fst ℝ V0 Vt0) - D.S0.comp (LinearMap.snd ℝ V0 Vt0))

theorem mem_Γ {x : V0 × Vt0} : x ∈ D.Γ ↔ D.d0 x.1 = D.S0 x.2 := by
  simp [Γ, sub_eq_zero]

/-- first operator `(0 d) : Γ → Ṽ¹` of the complex (5.1) -/
def D0 : D.Γ →ₗ[ℝ] Vt1 := D.dt0.comp ((LinearMap.snd ℝ V0 Vt0).comp D.Γ.subtype)

/-- second operator `(S, d) : Ṽ¹ → W² × W̃²` of the complex (5.1) -/
def D1 : Vt1 →ₗ[ℝ] W2 × Wt2 := D.S1.prod D.dt1

theorem D1_D0 (x : D.Γ) : D.D1 (D.D0 x) = 0 := by
  obtain ⟨⟨σ, φ⟩, hx⟩ := x
  have h := D.d1_d0 σ
  rw [(D.mem_Γ).1 hx, D.anticomm] at h
  simp [D0, D1, neg_eq_zero.mp h, D.dt1_dt0]

end BGGData

/-! ## §G. Component tensors (Ch 2–3) -/

section Tensor

/-- (0,4)-tensor in components over an index type `ι`. -/
abbrev T4 (ι : Type*) := ι → ι → ι → ι → ℝ

variable {ι : Type*}

def PairSkew (C : T4 ι) : Prop :=
  ∀ a b c d, C a b c d = -C b a c d ∧ C a b c d = -C a b d c
def Bianchi1 (C : T4 ι) : Prop := ∀ a b c d, C a b c d + C a c d b + C a d b c = 0
def Interchange (C : T4 ι) : Prop := ∀ a b c d, C a b c d = C c d a b

/-- Minkowski metric, signature (−+++), diagonal entries. -/
def η : Fin 4 → ℝ := ![-1, 1, 1, 1]

/-- Levi-Civita symbol on `Fin 3` (determinant of basis rows). -/
def eps3 (i j k : Fin 3) : ℝ :=
  Matrix.det (Matrix.of ![Pi.single i (1 : ℝ), Pi.single j 1, Pi.single k 1])

/-- Levi-Civita symbol on `Fin 4`. -/
def eps4 (a b c d : Fin 4) : ℝ :=
  Matrix.det (Matrix.of ![Pi.single a (1 : ℝ), Pi.single b 1, Pi.single c 1, Pi.single d 1])

/-- first jet of a 3×3 matrix field: `dA c = ∂_c A`. -/
abbrev Jet1 := Fin 3 → Matrix (Fin 3) (Fin 3) ℝ

/-- row-wise curl, thesis convention `(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}`. -/
def curl (dA : Jet1) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => ∑ c, ∑ d, eps3 b c d * dA c a d

/-- row-wise divergence `(div A)_a = ∂_b A_{ab}`. -/
def div (dA : Jet1) : Fin 3 → ℝ := fun a => ∑ b, dA b a b

/-- `(vskw A)_a = ½ ε_{abc} A_{bc}`. NB: the BGG map is `S₁ = 2·vskw` (thesis says `vskw`). -/
def vskw (A : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  fun a => (1 / 2 : ℝ) * ∑ b, ∑ c, eps3 a b c * A b c

/-- partial derivative of a scalar field on `ℝⁿ` (coordinates). -/
def pd {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

end Tensor

end Feec

/-! Sanity checks that the API elaborates. -/
section Checks
open Feec
example {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : E →ₗ.[ℝ] E) (T : ℝ) :
    WellPosedHom L T ↔ ∀ U₀ ∈ L.domain, ∃ U, IsStrongSolution L T U₀ 0 U := Iff.rfl
example : eps3 0 1 2 = 1 := by simp [eps3, Matrix.det_fin_three]
end Checks
```

---

## 3. Modules

All modules import the foundation. "Wave 1" modules depend only on the foundation and can be built in parallel. "Wave 2" modules depend on the Wave-1 modules named in their entries. Statements below are signatures; the variable contexts are the obvious ones from the foundation.

### Wave 1 (parallel)

#### M1 `Feec/Ch2/Curvature.lean`: algebraic curvature tensors (easy)

Covers the [10] lemma, the deviation "iff", Ricci symmetry, G=0 ⇔ Ric=0, and optionally the dimension count.

```lean
theorem interchange_of_bianchi {C : T4 ι} (hs : PairSkew C) (hb : Bianchi1 C) : Interchange C  -- [S] ch2/Ch2.lean
def alt4 (C : T4 ι) (a b c d : ι) : ℝ   -- 24-term unnormalised alternation (port from Ch2.lean)
theorem bianchi_iff {C : T4 ι} (hs : PairSkew C) :
    Bianchi1 C ↔ Interchange C ∧ ∀ a b c d, alt4 C a b c d = 0                  -- [S]
theorem eq_zero_of_deviation [Fintype ι] {C : T4 ι} (hs : PairSkew C) (hb : Bianchi1 C)
    (h : ∀ Y Tv X : ι → ℝ, ∑ a, ∑ b, ∑ c, ∑ d, C a b c d * Y a * Tv b * X c * Tv d = 0) : C = 0
theorem ricci_symm [Fintype ι] (gi : Matrix ι ι ℝ) (hgi : gi.IsSymm) {C : T4 ι}
    (hi : Interchange C) (a b : ι) :
    ∑ c, ∑ e, gi c e * C e a c b = ∑ c, ∑ e, gi c e * C e b c a
theorem einstein_zero_iff {n : ℕ} (hn : n ≠ 2) (g gi Ric : Matrix (Fin n) (Fin n) ℝ)
    (hinv : gi * g = 1) :
    Ric - ((1/2 : ℝ) * Matrix.trace (gi * Ric)) • g = 0 ↔ Ric = 0
-- optional: finrank of {C : T4 (Fin 4) | PairSkew ∧ Bianchi1} = 20
```

The hole being filled is the unproved cited lemma and the unproved "iff". Proof route for `eq_zero_of_deviation`: polarize at T = e_b + e_d to get C_abcd + C_adcb = 0, then derive 4C = C with `linarith`.

#### M2 `Feec/Ch2/Linearized.lean`: symbol-level linearized gravity (easy–medium)

Covers Thm 2.3 (both forms), (2.5), gauge invariance, linearized Bianchi, Prop 2.4(b) corrected, (2.11), Prop 2.5, (2.13), Prop 2.6 corrected, and the deviation formulas.

Port `Hsym`, `trRev`, `divSym`, `Hsym_eq`, `Hsym_gauge`, `Hsym_lorentz` and `tt_form` from `/tmp/feec_scratch_ch2/Ch2.lean` [S]. Add:

```lean
theorem trRev_trace (h) : tr (trRev h) = - tr h
theorem trRev_trRev (h) : trRev (trRev h) = h
theorem trRev_gauge (h ξ k) : trRev (fun a b => h a b + k a * ξ b + k b * ξ a) = ...
theorem Hsym_div (k h) (hs : ∀ i j, h i j = h j i) (d) : ∑ b, η b * k b * Hsym k h b d = 0
theorem lorentz_eq_iff (hs) (hL : ∀ b, divSym k h b = 0) (T : Fin 4 → Fin 4 → ℝ) (b d) :
    Hsym k h b d = 8 * π * T b d ↔ dot k k * trRev h b d = -16 * π * T b d
def Bcorr (κ : ℝ) (A : Fin 4 → Fin 4 → ℝ) : Fin 4 → ℝ   -- corrected gauge vector
def gaugeAmp (κ) (A) (B : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ
theorem tt_gauge (hκ : κ ≠ 0) (hA : ∀ i j, A i j = A j i) (hk : ∀ a, A a 0 + A a 3 = 0) :
    let A' := gaugeAmp κ A (Bcorr κ A)
    (∀ a, A' a 0 = 0) ∧ tr A' = 0 ∧ (∀ a, A' a 0 + A' a 3 = 0) ∧
    A' 1 1 = (A 1 1 - A 2 2)/2 ∧ A' 1 2 = A 1 2
theorem thesis_gauge_fails : ∃ κ A, κ ≠ 0 ∧ ... ∧ tr (gaugeAmp κ A (Bthesis κ A)) ≠ 0
theorem tt_accel (κ Ap Ax v1 v2) : ... = κ^2/2 * (Ap*v1 + Ax*v2) ∧ ... = κ^2/2 * (Ax*v1 - Ap*v2)
theorem plane_wave (hk : ∑ i, η i * k i * k i = 0) (hA : symm A) (hker) (hf : ContDiff ℝ 2 f) :
    (∀ x a b, ∑ i, η i * pd i (fun y => pd i (fun z => A a b * f (∑ c, k c * z c)) y) x = 0) ∧ ...
-- optional: einstein constant bound; Thm 2.2 for a C² family Ψ (hard)
```

#### M3 `Feec/Ch3/Bivector.lean`: duality and Weyl block structure (medium; heavy `fin_cases`)

Covers Props 3.1, 3.2 and 3.3, the corollary, (3.2), *W = W*, and dim Weyl = 10. Port `Ix, p, q, β, T, tr` from `/tmp/feec_scratch_ch3/Biv2.lean` and the 16-entry table from `/tmp/feec_scratch_ch3/Biv3.lean` [S]. Use the foundation's `η` and `eps4`.

```lean
def rdual (C : T4 (Fin 4)) : T4 (Fin 4)  -- with the factor 1/2
def ldual (C : T4 (Fin 4)) : T4 (Fin 4)
theorem rdual_T : rdual (T E B H D) = T B (-E) D (-H)
theorem ldual_T : ldual (T E B H D) = T H D (-E) (-B)
theorem eq_T_blocks (C) (hC : PairSkew C) : C = T (blkE C) (blkB C) (blkH C) (blkD C)
theorem interchange_iff : Interchange (T E B H D) ↔ Eᵀ = E ∧ Dᵀ = D ∧ H = Bᵀ
theorem alt_iff : (∀ a b c d, alt4 (T E B H D) a b c d = 0) ↔ trace B + trace H = 0
theorem tracefree_iff : (∀ b c, tr E B H D b c = 0) ↔ trace E = 0 ∧ Bᵀ = B ∧ Hᵀ = H ∧ D = -Eᵀ
structure IsWeylLike (C : T4 (Fin 4)) : Prop  -- PairSkew, Bianchi1, η-trace-free
theorem weyl_iff (C) : IsWeylLike C ↔ ∃ E B, Eᵀ = E ∧ trace E = 0 ∧ Bᵀ = B ∧ trace B = 0 ∧ C = T E B B (-E)
theorem prop_3_1 (hW : IsWeylLike W) : (E,B extracted) symmetric, trace-free, n-orthogonal
theorem ldual_eq_rdual (hW : IsWeylLike W) : ldual W = rdual W
-- optional: weyl_reconstruct (3.2); finrank Weyl = 10
```

`alt4` and the Bianchi lemma are needed here. To keep M3 parallel, either restate the 6-term `C_[0123]` formula locally, or move `bianchi_iff` into the foundation's §G when M1 lands, since it is short.

#### M4 `Feec/Ch4/Adjoint.lean`: unbounded operator theory (hard)

Covers (4.1b–d), the graph relations, density of D(T*), T** = T, closed kernels, and the closed range theorem.

```lean
theorem isClosed_ker (T : E →ₗ.[ℝ] F) (hc : T.IsClosed) : IsClosed (T.ker : Set E)
theorem orth_ker_adjoint ... -- (4.1c) (range T†)ᗮ = T.ker, needs hc
theorem dense_adjoint_domain (T) (hT : Dense ..) (hc : T.IsClosed) : Dense (T†.domain : Set F)
theorem adjoint_adjoint (T) (hT) (hc) : T†† = T
theorem range_adjoint_eq_orthogonal_ker (T) (hT) (hc)
    (hR : IsClosed (LinearMap.range T.toFun : Set F)) : LinearMap.range T†.toFun = T.kerᗮ
theorem isClosed_range_adjoint_iff (T) (hT) (hc) : IsClosed (range T†) ↔ IsClosed (range T)
theorem IsSkewAdjoint.dense_domain {L : E →ₗ.[ℝ] E} (hL : IsSkewAdjoint L) : Dense (L.domain : Set E)
theorem isSkewAdjoint_iff (L) (hD) : IsSkewAdjoint L ↔ IsSkewSymm L ∧ L†.domain ≤ L.domain
```

Proof routes are `adjoint_graph_eq_graph_adjoint`, `Submodule.adjoint`, `orthogonal_orthogonal_eq_closure` and `orthogonal_eq_bot_iff`. The closed range theorem goes Poincaré, then Riesz on `↥range`, then `mem_adjoint_domain_of_exists` (about 150 lines). This module also fills the false claim "kernel of an unbounded operator is closed".

#### M5 `Feec/Ch4/Hodge.lean`: bounded-model Hodge theory (medium)

Covers Thm 4.1, Thm 4.2 and its converse, the harmonic-form lemmas, compactness ⇒ closed with finite-dimensional ℌ, and the Fredholm counterexample. The starting point is `poincare` from `/tmp/feec_scratch_api/Design.lean` [S].

```lean
theorem B_sup_H (k) (hB : C.IsClosedAt k) : C.B k ⊔ C.H k = C.Z (k + 1)                         -- [S]
theorem poincare (k) (hB : C.IsClosedAt k) : ∃ c, ∀ u ∈ (C.Z k)ᗮ, ‖u‖ ≤ c * ‖C.d k u‖        -- [S]
theorem poincare_iff (k) : C.IsClosedAt k ↔ ∃ c, ∀ u ∈ (C.Z k)ᗮ, ‖u‖ ≤ c * ‖C.d k u‖
theorem hodge_V (k) (hB : C.IsClosedAt k) :
    C.B k ⊔ C.H k ⊔ (C.Z (k+1))ᗮ = ⊤ ∧ C.B k ⟂ C.H k ∧ C.B k ⟂ (C.Z (k+1))ᗮ ∧ C.H k ⟂ (C.Z (k+1))ᗮ
theorem orth_Z_eq (k) {v} : v ∈ (C.Z k)ᗮ ↔ ∀ z ∈ C.Z k, ⟪C.ι k v, C.ι k z⟫ = 0  -- Zᗮ_V = V ∩ Zᗮ_W
theorem finiteDimensional_H_of_compact (k) (hcpt : <sequential compactness of the V∩V* ball>) :
    FiniteDimensional ℝ (C.H k)
theorem isClosedAt_of_finite_cohomology (k) (h : FiniteDimensional ℝ (C.Z (k+1) ⧸ (C.B k).comap ..)) : C.IsClosedAt k
-- counterexample to "Fredholm ⇒ closed": diag(1/(n+1)) on ℓ² has trivial ℌ, non-closed range
theorem fredholm_not_closed : ∃ (A : ℓ²(ℕ) →L[ℝ] ℓ²(ℕ)), Function.Injective A ∧ Dense (range A) ∧ ¬ IsClosed (range A)
```

The unbounded W-level Hodge decomposition, W = cl B ⊕ ℌ ⊕ cl B*, with the closures dropped under closed range, is stated in M8 using M4. It is optional.

#### M6 `Feec/Ch4/Restriction.lean`: Thm 4.4, Cor 4.5, constraint propagation (medium)

Ports `/tmp/feec_scratch_ch4a/A.lean` and `B.lean` [S], plus `/tmp/feec_scratch_ch4b/Prop.lean` [S].

```lean
theorem skewAdjoint_restrict (L) (hD) (hL : IsSkewAdjoint L) (K) [K.HasOrthogonalProjection] [CompleteSpace K]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) : IsSkewAdjoint (restrictTo L K h3)        -- [S]
theorem dense_inter_of_proj_mem ...   -- the thesis' density hypothesis (ii) is redundant      [S]
theorem proj_orth_mem_of_le ...                                                               -- [S]
theorem commute_proj (hD hL K h1 h3) (x : L.domain) : L ⟨K.starProjection x, h1 x⟩ = K.starProjection (L x)
theorem strongSolution_unique (L) (hL : IsSkewSymm L) (h h' : IsStrongSolution L T U₀ F _) : EqOn U U' (Icc 0 T)
theorem constraint_propagation (L) (hL : IsSkewSymm L) (K) [K.HasOrthogonalProjection] (h1) (h3)
    (hU : IsStrongSolution L T U₀ F U) (hU₀ : U₀ ∈ K) (hFK : ∀ t ∈ Icc 0 T, F t ∈ K) :
    ∀ t ∈ Icc 0 T, U t ∈ K                         -- no density, no skew-adjointness needed
theorem cor_4_5 (L) (hD) (hL : IsSkewAdjoint L) (K) [..] (h1) (h3) (hHY : WellPosedExistence L T Adm)
    (hU₀ : U₀ ∈ L.domain ⊓ K) (hF : Adm F) (hFK) :
    ∃ U, IsStrongSolution L T U₀ F U ∧ (∀ t ∈ Icc 0 T, U t ∈ K) ∧ ∀ U', IsStrongSolution L T U₀ F U' → EqOn U U' (Icc 0 T)
theorem constraint_ker (M : E →ₗ.[ℝ] Y) (hM : M.IsClosed) ... : ∀ t ∈ Icc 0 T, U t ∈ M.ker
```

`constraint_ker` needs M closed, which is a corrected hypothesis. Its closed-kernel lemma can be proved locally with the 3-line graph-preimage argument, so M6 does not have to wait for M4. The F-version of `constraint_propagation` decomposes V = (I−P)U and uses `energy_zero`.

#### M7 `Feec/Ch4/Galerkin.lean`: Lax–Milgram, Babuška–Nečas, Céa, Brezzi (medium–hard)

Port `/tmp/feec_scratch_ch45/InfSup.lean` [S]: `InfSupCond`, `DenseRangeCond`, `existsUnique_solution`, `denseRange_of_solvable`, `infSup_of_bijective` and `quasi_opt`. Add:

```lean
theorem lax_milgram (h : IsCoercive B) (f : StrongDual ℝ V) : ∃! u, ∀ v, B u v = f v
theorem babuska_necas_iff : (InfSupCond B ∧ DenseRangeCond B) ↔ ∀ f : V, ∃! u, ∀ v, B u v = ⟪f, v⟫
theorem surjective_not_infSup : ∃ (B : ℓ² →L ℓ² →L ℝ), (∀ f, ∃ u, ∀ v, B u v = ⟪f,v⟫) ∧ ¬ InfSupCond B  -- backward shift
theorem quasi_opt (B) (K : Submodule ℝ X) (hγ : 0 < γ) (hinf : ∀ w ∈ K, ∃ v ∈ K, ‖v‖ ≤ 1 ∧ γ * ‖w‖ ≤ B w v)
    (huh : uh ∈ K) (horth : ∀ v ∈ K, B (u - uh) v = 0) : ∀ w ∈ K, ‖u - uh‖ ≤ (1 + ‖B‖ / γ) * ‖u - w‖  -- [S]
theorem brezzi (a : X →L[ℝ] X →L[ℝ] ℝ) (Bs : X →L[ℝ] Y)
    (hZ : ∃ γ > 0, ∀ z ∈ Bs.ker, ∃ z' ∈ Bs.ker, ‖z'‖ ≤ 1 ∧ γ * ‖z‖ ≤ a z z')
    (hZd : ∀ z' ∈ Bs.ker, (∀ z ∈ Bs.ker, a z z' = 0) → z' = 0)
    (hb : ∃ β > 0, ∀ q, β * ‖q‖ ≤ ‖ContinuousLinearMap.adjoint Bs q‖) (F : X) (G : Y) :
    ∃! up : X × Y, (∀ v, a up.1 v + ⟪Bs v, up.2⟫ = ⟪F, v⟫) ∧ ∀ q, ⟪Bs up.1, q⟫ = ⟪G, q⟫  -- (signature checked)
theorem brezzi_stability ... : ‖u‖ ≤ γ⁻¹‖F‖ + β⁻¹(1 + ‖a‖/γ)‖G‖ ∧ ‖p‖ ≤ β⁻¹(‖F‖ + ‖a‖‖u‖)
```

#### M8 `Feec/Ch4/Constraints.lean`: §4.7–4.11 algebra plus abstract Props 4.16 and 4.18 (medium)

Ports `/tmp/feec_scratch_ch4b/{Koszul,Ned,Curl}.lean` [S].

```lean
theorem koszul_homotopy_core (A) [Ring A] (D X e ι : Fin n → A) (hDX hDι hXe hCAR) : ... = ∑ X i * D i + ∑ e i * ι i   -- [S]
theorem grad_sq_not_whitney : ¬ ∃ a b : Fin 3 → ℝ, ∀ x, 2 * x 0 = a 0 + (b 1 * x 2 - b 2 * x 1)                -- [S]
theorem tr_curl / two_vskw_curl / curl_TSD   -- pointwise Lemma 3.5 used in 4.17/4.19                           [S]
-- abstract Prop 4.16 (both BCs, no density hypotheses), with K = ⊥ × ker d0† × Y, Yᗮ ≤ ker d1†:
theorem prop_4_16 (H : HilbertComplex2 W0 W1 W2) (Y : Submodule ℝ W2) [Y.HasOrthogonalProjection]
    (hY : Yᗮ ≤ H.d1†.ker) (hYinv : ∀ u ∈ H.midDomain, H.d1 u ∈ Y) {U} (hU : IsStrongSolution H.waveOp T U₀ 0 U)
    (hU₀ : U₀ ∈ K) : ∀ t ∈ Icc 0 T, U t ∈ K
theorem prop_4_18 (H) ... : σ ≡ 0 ∧ (E,B) solves the reduced 2-term system; and conversely
```

Skew-symmetry of `waveOp` comes from M9. For Wave-1 parallelism, state the two abstract props against `IsSkewSymm H.waveOp` as an explicit hypothesis, and discharge it in the final integration. The optional `UnitaryGroupGenerator` necessity argument also lives here.

#### M10 `Feec/Ch5/Discrete.lean`: Ch 5.2 (medium; Thm 5.5 is long)

Ports `/tmp/feec_scratch_ch52/*` [S]: `prop54_unique`, `prop54_hB_necessary`, `sysForm_bijective`, `prop56_error_eq`, `thm55_lhs_identity` and `minNorm_bound`.

```lean
theorem discrete_anticomm (Π1 Π2 ...) (hcomm) (hanti) : dX1 (Π1 (S0 ψ)) = -(Π2 (S1 (dY0 ψ)))
theorem surj_of_54 (h54 : S0h ∘ₗ Pt0 = P1S0) (hs : Surjective P1S0) : Surjective S0h
theorem exact_55 (hanti) (hY1) (hX1) (u) (hS : S1h u = 0) (hd : dY1 u = 0) : ∃ ρ χ, dX0 ρ = S0h χ ∧ dY0 χ = u
theorem prop54_counterexample_noTopExact : ∃ data satisfying all thesis hyps but ¬ exactness at V_h¹, with a nonzero homogeneous solution
theorem prop_5_3_b (… explicit constants, Poincaré/open-mapping constants as hypotheses …) :
    ∀ u ∈ (LinearMap.ker (S1h.prod dY1))ᗮ, ‖u‖ ≤ Cb * (‖S1h u‖ + ‖dY1 u‖)
theorem thm_5_5 (…) : ‖σ-σh‖V^2 + ‖φ-φh‖V^2 + ‖u-uh‖Γh^2 ≤ C * (…)  -- corrected hypotheses: λ ∈ W¹, total projections
theorem dof_commute (ℓ : ι → X →ₗ ℝ) (Π1 Π0) (hΠ1 : ∀ x y, (∀ i, ℓ i x = ℓ i y) → Π1 x = Π1 y)
    (hΠ0 : ∀ i, ℓ i ∘ₗ Π0 = ℓ i) : Π1 ∘ₗ Π0 = Π1     -- abstract core of Prop 5.7
```

#### M11 `Feec/Ch6/TimeDependent.lean`: Ch 6 (medium)

Ports `/tmp/feec_scratch_ch6/{Energy,Discrete,Prop61,EnergyEst}.lean` [S]: `energy_const` (both versions), `hidden_constraint`, `no_solution_of_incompatible`, `uniq`, `prop61_part2_core`, `prop63_a` and `energy_estimate`. Add:

```lean
theorem prop_6_1_i (s : sol of (6.1)) : ∃ Λ : ℝ → (V0 × Vt0) →ₗ[ℝ] ℝ, (Λ vanishes on Γ) ∧ (6.2) holds   -- multiplier in W̌¹
theorem prop_6_2_necessary (s : D.Sol T f) : (C1) ∧ (C2) ∧ (C3)
theorem prop_6_2_exists [FiniteDimensional ..] (hdinj) (hS : Surjective D.S0) (hanti) (hf : Continuous f)
    (hC1 hC2 hC3) : ∃ s : D.Sol T f, initial data match     -- via NormedSpace.exp + variation of constants
theorem prop_6_3_b / _c / _d / _e   -- remaining error identities (bilinearity)
theorem ch6_convergence (P_h, skew Ah, hyps) : ∀ t ∈ Icc 0 T, ‖ξ t - ξh t‖ ≤ ‖(1-P_h) ξ t‖ + ‖e_h 0‖ + ∫ ‖(1-P_h) ξ' s‖
```

#### M12 `Feec/Ch7/CrankNicolson.lean`: Ch 7 (easy)

Ports `/tmp/feec_scratch_ch7/{CN,Wave}.lean` [S]: `red_to_full`, `full_step_unique`, `full_step_energy`, `planeWave` and `steps_mesh8`. Add:

```lean
theorem cn_iterates_agree (hd : d1 ∘ₗ d0 = 0) (hE0 : adjoint d0 (E 0) = 0)
    (hred : ∀ n, RedStep d1 s (E n) (E (n+1)) (B n) (B (n+1)))
    (hfull : ∀ n, FullStep d0 d1 s (σ n) (σ (n+1)) (E' n) (E' (n+1)) (B' n) (B' (n+1)))
    (h0 : σ 0 = 0 ∧ E' 0 = E 0 ∧ B' 0 = B 0) : ∀ n, σ n = 0 ∧ E' n = E n ∧ B' n = B n
theorem cn_invertible [FiniteDimensional ..] : Function.Bijective (full CN map)
theorem minres_symm (M0 M1 M2 G C) (hM : symmetric) : (J * (M + s • K)).IsSymm
theorem steps_mesh32 : ⌊(7.5:ℝ) * (240 * Real.sqrt 2)⌋₊ = 2545
```

### Wave 2

#### M9 `Feec/Ch4/HodgeWave.lean`: Thm 4.6, Thm 4.7 (hard). Depends on M4.

`sigma_step` comes from `/tmp/feec_scratch_ch44/Sigma.lean` [S]. `energy_zero` is in the foundation.

```lean
def toComplex3 (H : HilbertComplex2 W0 W1 W2) : Complex3 H.d0.domain H.d1.domain W2
theorem skew (H) : IsSkewSymm H.waveOp                                        -- 4 adjoint identities
theorem kerAdj0_eq : H.d0†.ker = (LinearMap.range H.d0.toFun)ᗮ                 -- foundation (4.1a)
theorem closure_range_d1adj_le : (H.d1.ker)ᗮ ≤ H.d0†.ker                       -- no closed range
theorem dense_midDomain : Dense (H.midDomain : Set W1)                        -- von Neumann/Riesz, part (b) hard
theorem waveOp_dense : Dense (H.waveOp.domain : Set (Tot W0 W1 W2))
theorem waveOp_isSkewAdjoint : IsSkewAdjoint H.waveOp                         -- Thm 4.6, NO closed range
theorem neg_isSkewAdjoint (hL : IsSkewAdjoint L) : IsSkewAdjoint (-L)          -- sign fix ξ' = -Lξ
theorem thm_4_6 (hHY : WellPosedHom (-H.waveOp) T) (ξ₀ ∈ domL) :
    ∃ ξ, IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ ∧ (∀ ξ', … → EqOn ξ ξ' (Icc 0 T)) ∧ ∀ t ∈ Icc 0 T, ‖ξ t‖ = ‖ξ₀‖
def IsWeakSolution (H) (T) (ξ : ℝ → H.d0.domain × H.d1.domain × W2) (ξ' : ℝ → Tot ..) : Prop
theorem weak_unique : IsWeakSolution .. ξ1 → IsWeakSolution .. ξ2 → ξ1 0 = ξ2 0 → EqOn ξ1 ξ2 (Icc 0 T)
theorem strong_imp_weak / weak_imp_strong (hHY : WellPosedHom (-H.waveOp) T)   -- Thm 4.7 (cites 4.6)
theorem norm_embed : ‖d0σ + d1†ρ‖² = ‖d0σ‖² + ‖d1†ρ‖²
```

Only `waveOp_isSkewAdjoint` and `dense_midDomain` need M4 (`adjoint_adjoint`, `dense_adjoint_domain`). The fallback rule in §1.3 applies.

#### M13 `Feec/Ch4/ErrorEstimate.lean`: Lemma 4.12 through convergence (medium). Depends on M7.

Ports `/tmp/feec_scratch_ch45/{Lemma412,Prop413,Thm414}.lean` [S], restated against `Complex3`.

```lean
theorem lemma_4_12 (hQc) (hQ0) (hq : Q² right-diff) (hGc) (hG) (hF : 0 ≤ F) (hle : q' ≤ F*Q) : Q t ≤ Q 0 + (G t - G 0)/2  -- [S]
theorem prop_4_13 (C : Complex3 X0 X1 X2) (σ u ρ) :
    √(C.nV2 σ u ρ) * √(C.nV2 σ (u + C.d0 σ) (ρ - C.d1 u)) / √12 ≤ C.bigA σ u ρ σ (u + C.d0 σ) (ρ - C.d1 u)  -- [S]
theorem bigA_bound : |C.bigA ξ ψ| ≤ 2 * √(nV2 ξ) * √(nV2 ψ)        -- or golden ratio
theorem ellProj_exists_unique (S : C.Sub) [FiniteDimensional ..] (ζ) : ∃! p ∈ Vh, ∀ ψ ∈ Vh, bigA p ψ = bigA ζ ψ
theorem ellProj_quasiopt (S) : nV2 (ζ - Πζ) ≤ (1 + 2*√12)^2 * nV2 (ζ - ψ) ∀ ψ ∈ Vh   -- via quasi_opt (M7)
theorem discrete_solution_exists_unique [FiniteDimensional] : ∃! ξh, ODE (4.10) with ξh 0   -- NormedSpace.exp
theorem thm_4_14_pointwise (…) : ‖ε t - e t‖ ≤ ‖ε 0‖ + ‖e t‖ + t*‖e 0‖ + (1+t) ∫₀ᵗ ‖e'‖   -- [S]
theorem thm_4_14 (glue: derive herr from (4.8),(4.10),(4.11), a_self; ξ ∈ C¹(V) hypothesis)
theorem convergence (density along filter l; ξ ∈ C¹([0,T];V); ε_h(0) → 0) : Tendsto (sup_t ‖ξ - ξh‖) l (𝓝 0)
```

#### M14 `Feec/Ch5/BGG.lean`: Props 5.1 and 5.2 (medium–hard). Depends on M7 (Brezzi) and M5 (Poincaré, optional).

Ports `/tmp/feec_scratch_ch51/{A,B}.lean` [S] onto the foundation's `BGGData`: `range_D0`, `exact_mid`, `D0_injective`, `isClosed_range_S1_dt1` and `eq_zero_of_dense`.

```lean
theorem range_D0 (hT : D.ExactTop) : LinearMap.range D.D0 = LinearMap.range D.dt0 ⊓ LinearMap.ker D.S1   -- [S]
theorem exact_mid (hT) (hB : D.ExactBot) : LinearMap.ker D.D1 = LinearMap.range D.D0                       -- [S] (missing in thesis)
theorem isClosed_Γ (continuity hyps) : IsClosed (D.Γ : Set (V0 × Vt0))
theorem D0_closed / D0_isClosed_range / D1_isClosed_range (…, hreg : range d1 ⊆ range (d1 ∘ S0))           -- [S] for D1
theorem poincare_Γ (…) : ∃ C, ∀ x ∈ D.Γ, ‖x.1‖ ≤ C * ‖D.dt0 x.2‖
theorem tripleNorm_definite (hdense : Dense (range d0 + range S0)) : |||λ||| = 0 → λ = 0
theorem prop_5_2 (…, hdense) : ∃! (σ φ u Λ), saddle-point system with Λ ∈ annihilator of Γ  -- via brezzi
theorem saddle_iff_reduced : solutions of (5.3) ↔ solutions of (5.2) + unique multiplier
```

### Dependency summary

```
Foundation ─┬─ M1 Ch2/Curvature ─┐ (alt4 → M3 optional)
            ├─ M2 Ch2/Linearized
            ├─ M3 Ch3/Bivector ──── M15* Ch3/EB  (Lemma 3.5, Prop 3.4 jets, Prop 3.6 core, §3.5 wave)
            ├─ M4 Ch4/Adjoint ───── M9 Ch4/HodgeWave ── (discharges IsSkewSymm hyp in M8)
            ├─ M5 Ch4/Hodge ─────┐
            ├─ M6 Ch4/Restriction│
            ├─ M7 Ch4/Galerkin ──┼─ M13 Ch4/ErrorEstimate
            │                    └─ M14 Ch5/BGG
            ├─ M8 Ch4/Constraints
            ├─ M10 Ch5/Discrete
            ├─ M11 Ch6/TimeDependent
            └─ M12 Ch7/CrankNicolson
```

\*M15 `Feec/Ch3/EB.lean` (medium–hard, Wave 2 after M3):
- Lemma 3.5 at jet level: `trace_curl`, `two_vskw_curl`, `div_curl`, ported from `/tmp/feec_scratch_ch3/Jet.lean` [S].
- `pd_comm` from `/tmp/feec_scratch_ch3/Field.lean` [S].
- `linBianchi_iff` (Prop 3.4 at jet level, plus the rank-16 count as the trace/skew identities).
- The Prop 3.6 algebraic core: the closed evolution system for (tr, vskw) violations, and the flux identity ½∂ₜe = div F (via `crossProduct`).
- The divergence part of Prop 3.6 via `is_const_of_deriv_eq_zero`.
- The §3.5 plane-wave amplitudes, shared with M12's `planeWave`.

That makes 15 modules besides the foundation. If 14 is a hard cap, merge M12 into M15: both are plane-wave and finite-dimensional EB.

Difficulty: easy = M1, M12. Medium = M2, M3, M5, M6, M8, M10, M11, M13, M15. Hard = M4, M7 (Brezzi), M9, M14.

---

## 4. Holes and corrections (for README/docs)

| Thesis id | Issue | Fix |
|---|---|---|
| §2.3 def. of Riemann | ∇_[c∇_d] carries ½, inconsistent with (2.2) | Define R by the commutator (∇_c∇_d − ∇_d∇_c) |
| Prop 2.1 | Writes R_[abcd] where R^b_[acd] is meant; "d²v=0 for a vector" | Bianchi is R^a_[bcd]=0; v is a 1-form |
| Riemann count, [10] lemma | Unproved | Proved (M1); the dimension count is optional |
| §2.4 constant | 8πG/c⁴ ≈ 5·10⁻⁴⁴ is wrong (that is 2πG/c⁴) | ≈ 2.08·10⁻⁴³ s²/(m·kg) |
| §2.4 G=0 ⇔ Ric=0 | Fails for n=2 | Assume n≠2 (M1) |
| §2.5–2.6, Thm 2.2 | Needs a diffeomorphism and a complete ξ; joint smoothness unstated | Any C² family Ψ with Ψ₀=id and ∂Ψ=ξ |
| (2.5), Thm 2.3 | n=4 used silently; ε dropped | State n=4; general n uses 1/(n−2) |
| §2.7 gauge check | Trace written 4∇·ξ (should be 2∇·ξ); display equals 2H | Corrected; linearized Bianchi added |
| **Prop 2.4(b)** | H = −□h̄ | **H = −½□h̄** (consistent with (2.11)) |
| Prop 2.4(a), (2.11) | Wave solver uncited; "Theorem 2.4" does not exist; T_ab should be T_bd | Wave solver taken as a hypothesis |
| **Prop 2.6** | Sign of gauge vector B wrong; TT fails | Use −B; A'₊=(A₁₁−A₂₂)/2, A'×=A₁₂ |
| **(2.15) accelerations** | Sign wrong, and f where f'' belongs | a¹=(κ²/2)(A₊v¹+A×v²)f'', and similarly for a² |
| §3.1 contraction identity | Off by (−1)^{kl}; symbol "−1 for even" (should be odd) | Same-slot identity |
| Prop 3.1 | 3D contraction needs the spatial projector; two volume-form conventions | Prove via Prop 3.3 block form |
| Prop 3.2 | Missing factor ½ in B and the dual | Add ½ |
| Prop 3.3 | Drops the D-term; wrong cross-reference | Full 16-entry trace table |
| Prop 3.4 | ε missing; div/curl undefined; "24 equations" | 16 independent: 6 constraints + 10 evolution |
| Lemma 3.5 | Typo "A" for curl A; distributional use unstated | Pointwise version proved; distributional version by linearity |
| Prop 3.6 | Rests on hypotheses later only conjectured; "curl E" should be curl B | Energy proof on ℝ³/𝕋³, or via the abstract Cor 4.5 |
| §3.4 nonlinear B-eq. | "+ sym curl E" (sign) | Minus sign |
| [15] | Wrong authors | Brüning & Lesch, JFA 108 (1992) |
| §4.1 graph norm | ‖dv‖ should be ‖Tv‖ | Corrected |
| §4.1 / §4.3 | "Kernel of an unbounded operator is closed" is false | Needs M closed |
| (4.1a–d), T**=T, D(T*) dense | Unproved | Proved (M4) |
| Def. Hilbert complex | Omits d V^k ⊂ V^{k+1} | Added (`map_mem`) |
| "Compact subspace" | Meaningless | Compact *inclusion* |
| **"Fredholm ⇒ closed"** | False (diag(1/n) on ℓ²) | Compactness ⇒ closed; finite algebraic cohomology ⇒ closed |
| **Dual complex closed / B*=Zᗮ** | Needs the closed range theorem, not (4.1) | Proved (M4) |
| Thm 4.1 | One-line proof | Closure version unconditional; exact under closed range |
| Thm 4.2 | "Closed complex" missing; bounded inverse unnamed; converse missing | Closed range ⇔ Poincaré |
| de Rham examples | Bounded Lipschitz (contractible) Ω missing | Added (out of formal scope) |
| Thm 4.3 | Citation; "D(L) dense" redundant | `WellPosedExistence` hypothesis; uniqueness proved |
| Thm 4.4 | Hypothesis (ii) redundant; typos L* for L̃* | Dropped; exact identity in place of the estimate |
| Cor 4.5 | Constraint propagation implicit | Explicit; simpler energy proof |
| **Thm 4.6** | Closed range unnecessary; density of D(L) missing; sign U'=LU vs ξ'=−Lξ; ρ-step omitted; uses d**=d | No closed range; density proved; apply to −L; ρ-step written out |
| **Thm 4.7** | Cites itself | Cites Thm 4.6 |
| Weak uniqueness | Skips the energy identity | a(e,e)=0 ⇒ d/dt‖e‖²=0 |
| Dense-range def. | "Equivalently" swaps arguments | Quantify over v |
| **Thm 4.9 converse** | Surjectivity ⇏ inf-sup (backward shift) | "unique u" |
| Thm 4.10 | a bounded only on X_h | Bounded on X |
| **Thm 4.11 (Brezzi)** | B: Y→X* should be X→Y*; inf over wrong argument; no proof | Corrected and proved (M7) |
| Discretization | dV_h¹ ⊂ W_h²; uniform bounds unstated | V_h²; uniform bounds |
| **Lemma 4.12** | Q∈C¹ fails where it is applied | Q continuous, Q² differentiable |
| Prop 4.13 | V⁰×V¹×V² | V⁰×V¹×W²; √3 bound proved |
| **Thm 4.14** | Needs ξ∈C¹(V); "(1+T)" loose; cites equations as theorems | Regularity hypothesis; sharp bound |
| Convergence remark | "Requires compactness" | Not needed: density + Prop 4.13 suffice |
| §4.7 decomposition | Fails at r=k=0 | Assume r+k>0 |
| §4.7 2^{n−1} complexes | Last space misdescribed | Path-dependent last space |
| §4.8 | RT/DG degree mismatch; Neumann equivalence misses the constant mode | ∫u̇(0)=0 condition |
| **§4.10 discretizations** | Two of four are not subcomplexes (grad P_{r+1} ⊄ P_r⁻Λ¹) | Use P_r Λ⁰ with P_r⁻Λ¹ |
| Prop 4.16 | Wrong complex in proof; wrong Hodge decomposition; false P H(curl) ⊂ H̊(curl); density hypotheses redundant | Holds unconditionally (abstract proof) |
| **Props 4.17, 4.19** | Projection hypothesis false on smooth bounded Ω, so the props are vacuous; "Theorem 4.5" does not exist | True on 𝕋³; otherwise stated as a conditional theorem |
| Prop 4.18 | No proof | Proved abstractly |
| §5.1 / Prop 5.1 | Typos Z̃ = N(d⁰), W¹→W²; φ undefined on Γ̄ | Γ closed in V⁰×Ṽ⁰; norm-equivalence proof |
| **(5.1) exactness at Ṽ¹** | Never proved; needed for (5.2), the Hodge split and transposed Brezzi | Proved (M14) |
| Prop 5.2 | Density hypothesis missing; transposed condition missing; λ in W̌¹ not W¹; ε's lost | All added |
| (5.4) / Prop 5.3 | Canonical projections applied to non-discrete fields; final norm step wrong; min-norm step missing | Total bounded projections; min-norm lemma |
| **Prop 5.4** | Needs top exactness at V_h¹ (counterexample otherwise) | Minimal hypotheses, plus a necessity result |
| Thm 5.5 | λ ∈ W¹ needed; ‖·‖_{Γ_h} misnamed | h-dependent graph norm on Ṽ¹ |
| **§5.3 S₁** | S₁ = vskw violates anticommutation | S₁ = 2·vskw |
| Prop 5.7 | Invalid density step; needs moment DOFs | Direct DOF argument |
| Prop 5.8 | ℓ¹ sums off by h^{-3/2}; S₁,h half not proved | ℓ² local scaling |
| **Prop 5.9(2)** | False (edge-bubble gradient, ratio √(2/3)) | Broken-H¹ estimate; Thm 5.5 not established for these elements |
| §6.1 | M missing; λ₀ overprescribed; λ∈C⁰(W¹) unjustified | λ ∈ C⁰(W̌¹), no λ₀ |
| Prop 6.1(ii) | dS⁻¹dτ undefined; cites (6.1) for (6.2); M≡0 unneeded | Density-plus-regularity version |
| **Prop 6.2** | False: DAE with ker S₀,h≠0; φ_h=0 not shown | Compatibility (C1)–(C3), with existence and uniqueness |
| (6.4), Ch 6 convergence | Garbled; no theorem | New conditional convergence theorem |
| Ch 7 | B field never given; BCs; truncated step counts; MINRES on non-symmetric matrix; promised content absent | B₀ given; full ⇔ reduced CN exact; J-symmetrization |
| Bibliography | [8], [10], [23], [25] incomplete or wrong | Fixed BibTeX; add Arnold (2018), SIAM CBMS 93 |

Scratch artifacts:
- `/tmp/feec_scratch_architect/Foundation.lean`: the foundation in §2, which compiles.
- `/tmp/feec_scratch_architect/Sig.lean`: the foundation plus `sorry`-stubbed new signatures, which elaborate.
- All other [S] files under `/tmp/feec_scratch_*`.

The repository itself was not modified.