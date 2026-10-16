module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Feec.HilbertComplex.Short

/-!
# Feec foundation §C–§E: Hilbert complexes

* §C unbounded Hilbert complexes (`HilbertComplex2`, `UHilbertComplex`) and the Hodge wave
  operator (4.5);
* §D the bounded domain complex (`DomainComplex`, formerly `HilbertComplex`; that name is now
  the general complex of `Feec.HilbertComplex.Basic`): cycles, boundaries, harmonic forms,
  subcomplexes and bounded cochain projections;
* §E the algebraic segment `Complex3` with W-inner products and the forms `a`, `A`.

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

namespace Feec

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

namespace HilbertComplex2

universe u

variable {W0 W1 W2 : Type u}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    (H : HilbertComplex2 W0 W1 W2)

/-- `ClosedRange` is closed range of the window complex at the indices `1` and `2`. -/
theorem closedRange_iff_closedRangeAt : H.ClosedRange ↔
    H.toShort.toHilbertComplex.ClosedRangeAt 1 ∧ H.toShort.toHilbertComplex.ClosedRangeAt 2 := by
  rw [HilbertComplex.ClosedRangeAt, HilbertComplex.ClosedRangeAt,
    HilbertComplex.boundaries_eq _ (show ComplexShape.fin3.Rel 0 1 from rfl),
    HilbertComplex.boundaries_eq _ (show ComplexShape.fin3.Rel 1 2 from rfl)]
  rfl

end HilbertComplex2

namespace UHilbertComplex

variable {W : ℕ → Type*}
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    (C : UHilbertComplex W)

/-- An `ℕ`-indexed Hilbert complex as a `Feec.HilbertComplex` on `ComplexShape.up ℕ`. -/
def toComplex : HilbertComplex ℝ (ComplexShape.up ℕ) W :=
  HilbertComplex.ofSucc C.d C.dense C.closed C.map_mem C.comp_zero

@[simp] theorem toComplex_d_succ (k : ℕ) : C.toComplex.d k (k + 1) = C.d k :=
  HilbertComplex.ofSuccD_succ _ k

theorem segment_d0 (k : ℕ) : (C.segment k).d0 = C.toComplex.d k (k + 1) := by simp [segment]

theorem segment_d1 (k : ℕ) : (C.segment k).d1 = C.toComplex.d (k + 1) (k + 2) := by
  simp [segment]

end UHilbertComplex

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
/-- boundaries `𝔅^{k+1} = d^k V^k ⊂ V^{k+1}`. See [QuennevilleBelair2015, §4.2]. -/
def B (k : ℕ) : Submodule ℝ (V (k + 1)) := (C.d k).range
/-- harmonic forms `ℌ^{k+1} = 𝔅^{k+1}ᗮ ∩ 𝔷^{k+1}`.
See [QuennevilleBelair2015, §4.2] (and Thm 4.1, Hodge decomposition); cf. [AFW2010]. -/
def H (k : ℕ) : Submodule ℝ (V (k + 1)) := (C.B k)ᗮ ⊓ C.Z (k + 1)
/-- closed complex at position `k → k+1`. See [QuennevilleBelair2015, §4.2]. -/
def IsClosedAt (k : ℕ) : Prop := IsClosed (C.B k : Set (V (k + 1)))

theorem d_d (k : ℕ) (u : V k) : C.d (k + 1) (C.d k u) = 0 := by
  simpa using congrArg (fun f => f u) (C.d_comp_d k)

theorem B_le_Z (k : ℕ) : C.B k ≤ C.Z (k + 1) := by
  rintro _ ⟨u, rfl⟩; exact C.d_d k u

theorem isClosed_Z (k : ℕ) : IsClosed (C.Z k : Set (V k)) := (C.d k).isClosed_ker

instance (k : ℕ) : (C.Z k).HasOrthogonalProjection := by
  have : CompleteSpace (C.Z k) := (C.isClosed_Z k).completeSpace_coe
  infer_instance

/-- On cycles the `V`- and `W`-inner products agree.
See [QuennevilleBelair2015, §4.2] (equivalence of the `V`- and `W`-norms on `𝔷^k`). -/
theorem inner_of_mem_Z {k : ℕ} {u v : V k} (hu : u ∈ C.Z k) :
    ⟪u, v⟫ = ⟪C.ι k u, C.ι k v⟫ := by
  have : C.d k u = 0 := hu
  simp [C.inner_graph, this]

/-- A subcomplex: subspaces `Vh k` with `d (Vh k) ⊆ Vh (k+1)`.
See [QuennevilleBelair2015, §4.6] (subcomplex property); cf. [AFW2010], [Arnold2018]. -/
structure Subcomplex where
  Vh : ∀ k, Submodule ℝ (V k)
  d_mem : ∀ k, ∀ u ∈ Vh k, C.d k u ∈ Vh (k + 1)

/-- Bounded cochain projections onto a subcomplex (AFW 2010, Thm 5.9 abstracted).
See [QuennevilleBelair2015, §4.6] (third standing assumption) and Thm 4.15 (citing [AFW2010]);
cf. [Arnold2018]. -/
structure CochainProjection (S : C.Subcomplex) where
  π : ∀ k, V k →L[ℝ] V k
  mem : ∀ k u, π k u ∈ S.Vh k
  proj : ∀ k, ∀ u ∈ S.Vh k, π k u = u
  comm : ∀ k u, C.d k (π k u) = π (k + 1) (C.d k u)

end DomainComplex

/-! ## §E. Algebraic complex segment with W-inner products ("type = domain" model)

Used where only algebra + inner products are needed (Prop 4.13, Thm 4.14, Ch 5.2, Ch 6.2, Ch 7):
each type carries the **W** inner product and `d` is a linear map on the domain type.
Graph norms are explicit functions. -/

/-- Algebraic length-2 complex segment `X0 → X1 → X2`.
See [QuennevilleBelair2015, §4.4, §4.6]. -/
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

/-- skew form `a(σ,u,ρ; τ,v,μ)` of the weak Hodge wave (4.7).
See [QuennevilleBelair2015, §4.4, (4.7)–(4.8)]. -/
def a (σ : X0) (u : X1) (ρ : X2) (τ : X0) (v : X1) (μ : X2) : ℝ :=
  -⟪u, C.d0 τ⟫ + ⟪C.d0 σ, v⟫ + ⟪ρ, C.d1 v⟫ - ⟪C.d1 u, μ⟫

/-- `A = (·,·)_W + a` (the shifted form of §4.6).
See [QuennevilleBelair2015, §4.6] (definition before Prop 4.13). -/
def bigA (σ : X0) (u : X1) (ρ : X2) (τ : X0) (v : X1) (μ : X2) : ℝ :=
  ⟪σ, τ⟫ + ⟪u, v⟫ + ⟪ρ, μ⟫ + C.a σ u ρ τ v μ

/-- squared `V`-norm on `V0 × V1 × W2`. See [QuennevilleBelair2015, §4.4, §4.6]. -/
def nV2 (σ : X0) (u : X1) (ρ : X2) : ℝ :=
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

end Complex3

end Feec
