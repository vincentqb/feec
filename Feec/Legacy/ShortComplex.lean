module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Feec.HilbertComplex.Short

/-!
# Feec foundation §C–§E: Hilbert complexes

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

* §C unbounded Hilbert complexes (`HilbertComplex2`, `UHilbertComplex`) and the Hodge wave
  operator (4.5);
* §E the algebraic segment `AlgSegment` with W-inner products and the forms `a`, `A`.

Conventions: real scalars only; complexes indexed by explicit segments `k, k+1, k+2` (no `k-1`).

## References

* [QuennevilleBelair2015], §4.2 (Hilbert complexes, domain complex, cycles/boundaries/harmonic
  forms), §4.4 (Hodge wave operator (4.5), Thm 4.6, weak form (4.7)), §4.6 (subcomplexes,
  bounded cochain projections, the form `A`)
* [Arnold2018] (FEEC framework: Hilbert complexes, domain complexes, subcomplexes and bounded
  cochain projections)
* [AFW2010] (closed Hilbert complexes, Hodge decomposition, approximation by subcomplexes with
  bounded cochain projections; the thesis' main FEEC source, cited there as [5])
* [AFW2006] (FEEC, cited by the thesis together with [AFW2010])
* [BruningLesch1992] (unbounded Hilbert complexes; cited by the thesis for §4.2)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open Set

namespace Feec.Legacy

/-! ## §C. Unbounded Hilbert complexes (the thesis' / Brüning–Lesch picture) -/

/-- A length-2 Hilbert complex `W0 --d0--> W1 --d1--> W2` of closed, densely defined operators
(§4.4 setup). Closed range is **not** part of the structure (see `HilbertComplex2.ClosedRange`).
See [QuennevilleBelair2015, §4.2, §4.4]; cf. [BruningLesch1992], [AFW2010], [Arnold2018]. -/
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

/-- Closed-range hypothesis (a closed complex in AFW's sense).
See [QuennevilleBelair2015, §4.2] ("closed" Hilbert complex); cf. [AFW2010]. -/
def ClosedRange : Prop :=
  IsClosed (LinearMap.range H.d0.toFun : Set W1) ∧ IsClosed (LinearMap.range H.d1.toFun : Set W2)

/-- Domain of the middle space of the Hodge wave operator: `V1 ∩ V1*`.
See [QuennevilleBelair2015, §4.4] (`D(L)` in (4.5)). -/
def midDomain : Submodule ℝ W1 := H.d1.domain ⊓ H.d0†.domain

/-- The product space `W = W0 × W1 × W2` with the ℓ² inner product.
See [QuennevilleBelair2015, §4.4]. -/
abbrev Tot (W0 W1 W2 : Type*) := WithLp 2 (W0 × WithLp 2 (W1 × W2))

/-- coordinates of `Tot` -/
def tot (W0 W1 W2 : Type*)
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] : Tot W0 W1 W2 ≃ₗ[ℝ] W0 × W1 × W2 :=
  (WithLp.linearEquiv 2 ℝ _).trans ((LinearEquiv.refl ℝ W0).prodCongr (WithLp.linearEquiv 2 ℝ _))
/-- domain `V0 × (V1 ∩ V1*) × V2*` of the Hodge wave operator, as a submodule of `Tot`.
See [QuennevilleBelair2015, §4.4, (4.5)]. -/
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

/-- Hodge wave operator (4.5): `L(σ,u,ρ) = (-d0* u, d0 σ + d1* ρ, -d1 u)` on `domL`.
See [QuennevilleBelair2015, §4.4, (4.5)] and Thm 4.6. -/
def waveOp : Tot W0 W1 W2 →ₗ.[ℝ] Tot W0 W1 W2 where
  domain := H.domL
  toFun := (tot W0 W1 W2).symm.toLinearMap.comp
    ((-(H.d0†.toFun.comp H.prV1s)).prod
      (((H.d0.toFun.comp H.pr0) + (H.d1†.toFun.comp H.prV2s)).prod
        (-(H.d1.toFun.comp H.prV1))))

end HilbertComplex2

/-- ℕ-indexed unbounded Hilbert complex (W-level). `segment k` gives the length-2 piece.
See [QuennevilleBelair2015, §4.2]; cf. [BruningLesch1992], [AFW2010], [Arnold2018]. -/
structure UHilbertComplex (W : ℕ → Type*)
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    where
  d : ∀ k, W k →ₗ.[ℝ] W (k + 1)
  dense : ∀ k, Dense ((d k).domain : Set (W k))
  closed : ∀ k, (d k).IsClosed
  map_mem : ∀ k (x : (d k).domain), d k x ∈ (d (k + 1)).domain
  comp_zero : ∀ k (x : (d k).domain), d (k + 1) ⟨d k x, map_mem k x⟩ = 0

/-! ### Bridges to `Feec.HilbertComplex` and `Feec.ShortHilbertComplex`

Strangler shims (`docs/REFACTOR_PLAN.md` §5): the old complexes are instances of the new
ones. -/

namespace HilbertComplex2

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    (H : HilbertComplex2 W0 W1 W2)

/-- A length-2 Hilbert complex as a real `ShortHilbertComplex`. -/
def toShort : ShortHilbertComplex ℝ W0 W1 W2 where
  d₀ := H.d0
  d₁ := H.d1
  dense₀ := H.dense0
  dense₁ := H.dense1
  closed₀ := H.closed0
  closed₁ := H.closed1
  mapsTo := H.map_mem
  comp := H.comp_zero

@[simp] theorem toShort_d₀ : H.toShort.d₀ = H.d0 := rfl
@[simp] theorem toShort_d₁ : H.toShort.d₁ = H.d1 := rfl

end HilbertComplex2

/-! ## §D. Bounded "domain complex" (AFW): `V k` carries the graph inner product -/

/-- `V k` = domain of `d k` with its graph inner product, `ι k : V k → W k` the inclusion.
All Hodge/Poincaré/cohomology arguments live in `V` using Mathlib's `ᗮ`/`starProjection`.
See [QuennevilleBelair2015, §4.2] (the domain complex, Thms 4.1–4.2); cf. [AFW2010],
[Arnold2018]. -/
structure DomainComplex (V W : ℕ → Type*)
    [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)] [∀ k, CompleteSpace (V k)]
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    where
  ι : ∀ k, V k →L[ℝ] W k
  ι_injective : ∀ k, Function.Injective (ι k)
  d : ∀ k, V k →L[ℝ] V (k + 1)
  d_comp_d : ∀ k, (d (k + 1)).comp (d k) = 0
  inner_graph : ∀ k (u v : V k),
    ⟪u, v⟫ = ⟪ι k u, ι k v⟫ + ⟪ι (k + 1) (d k u), ι (k + 1) (d k v)⟫

namespace DomainComplex

variable {V W : ℕ → Type*}
    [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)] [∀ k, CompleteSpace (V k)]
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    (C : DomainComplex V W)

/-- cycles `𝔷^k = ker d^k ⊂ V^k`. See [QuennevilleBelair2015, §4.2]. -/
def Z (k : ℕ) : Submodule ℝ (V k) := (C.d k).ker

end DomainComplex

/-! ## §E. Algebraic complex segment with W-inner products ("type = domain" model)

Used where only algebra + inner products are needed (Prop 4.13, Thm 4.14, Ch 5.2, Ch 6.2, Ch 7):
each type carries the **W** inner product and `d` is a linear map on the domain type.
Graph norms are explicit functions. -/

/-- Algebraic length-2 complex segment `X0 → X1 → X2`.
See [QuennevilleBelair2015, §4.4, §4.6]. -/
structure AlgSegment (X0 X1 X2 : Type*) [AddCommGroup X0] [Module ℝ X0]
    [AddCommGroup X1] [Module ℝ X1] [AddCommGroup X2] [Module ℝ X2] where
  d0 : X0 →ₗ[ℝ] X1
  d1 : X1 →ₗ[ℝ] X2
  d1_d0 : ∀ x, d1 (d0 x) = 0

namespace AlgSegment

variable {X0 X1 X2 : Type*}
  [NormedAddCommGroup X0] [InnerProductSpace ℝ X0]
  [NormedAddCommGroup X1] [InnerProductSpace ℝ X1]
  [NormedAddCommGroup X2] [InnerProductSpace ℝ X2]
  (C : AlgSegment X0 X1 X2)

/-- skew form `a(σ,u,ρ; τ,v,μ)` of the weak Hodge wave (4.7).
See [QuennevilleBelair2015, §4.4, (4.7)–(4.8)]. -/
def a (σ : X0) (u : X1) (ρ : X2) (τ : X0) (v : X1) (μ : X2) : ℝ :=
  -⟪u, C.d0 τ⟫ + ⟪C.d0 σ, v⟫ + ⟪ρ, C.d1 v⟫ - ⟪C.d1 u, μ⟫

/-- `A = (·,·)_W + a` (the shifted form of §4.6).
See [QuennevilleBelair2015, §4.6] (definition before Prop 4.13). -/
def formA (σ : X0) (u : X1) (ρ : X2) (τ : X0) (v : X1) (μ : X2) : ℝ :=
  ⟪σ, τ⟫ + ⟪u, v⟫ + ⟪ρ, μ⟫ + C.a σ u ρ τ v μ

/-- squared `V`-norm on `V0 × V1 × W2`. See [QuennevilleBelair2015, §4.4, §4.6]. -/
def normVSq (σ : X0) (u : X1) (ρ : X2) : ℝ :=
  ‖σ‖ ^ 2 + ‖C.d0 σ‖ ^ 2 + ‖u‖ ^ 2 + ‖C.d1 u‖ ^ 2 + ‖ρ‖ ^ 2

/-- `a` is alternating: `a(ξ, ξ) = 0`, the identity behind weak uniqueness in
[QuennevilleBelair2015, §4.4] and the nonsingularity of (4.11) in §4.6. -/
theorem a_self (σ : X0) (u : X1) (ρ : X2) : C.a σ u ρ σ u ρ = 0 := by
  simp only [a, real_inner_comm (C.d0 σ) u, real_inner_comm (C.d1 u) ρ]; ring

/-- A subcomplex of the algebraic segment.
See [QuennevilleBelair2015, §4.6] (subcomplex property `dVh⁰ ⊂ Vh¹`, `dVh¹ ⊂ Vh²`). -/
structure Sub where
  V0h : Submodule ℝ X0
  V1h : Submodule ℝ X1
  V2h : Submodule ℝ X2
  d0_mem : ∀ σ ∈ V0h, C.d0 σ ∈ V1h
  d1_mem : ∀ u ∈ V1h, C.d1 u ∈ V2h

end AlgSegment

end Feec.Legacy
