module

public import Feec.Legacy.Adjoint
public import Feec.Legacy.Hodge
public import Feec.HilbertComplex.Compactness

/-!
# `W`-level Hodge theory: compactness, Fredholm, and the bounded-model bridge (Thesis §4.2)

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use.
Most of the original module was re-derived in the general layers (see
`docs/migration/map.tsv`); what remains is listed below.

## Contents

* `HilbertComplex2.isClosed_toPMap_top`: An everywhere-defined continuous operator is closed.
* `HilbertComplex2.ker_toPMap_top`: `N(f|_⊤) = N(f)`.
* `HilbertComplex2.range_toPMap_top`: `R(f|_⊤) = R(f)`.
* `HilbertComplex2.ofBounded`: A bounded complex `W0 --A--> W1 --B--> W2` (`B A = 0`) as a Hilbert complex of everywhere-defined operators.
* `FredholmCE.R0`: The trivial Hilbert space `ℝ⁰`.
* `FredholmCE.cxW`: The `W`-level complex `0 → ℓ² --A--> ℓ² --0--> ℝ⁰ → 0`, `A = diag(1/(n+1))`, as a `HilbertComplex2`, i.e.
* `FredholmCE.Atr`: Truncation `A_N = Σ_{n<N} (1/(n+1)) ⟨e_n, ·⟩ e_n` of `A` (finite rank).
* `FredholmCE.invA`: The unbounded operator `A⁻¹ = diag(n+1)` on `ℓ²`, with domain `R(A)`.
* `FredholmCE.ker_A_toPMap`: `N(A) = 0`.
* `FredholmCE.invA_domain`: `D(A⁻¹) = R(A)`.
* `FredholmCE.invA_isClosed`: `A⁻¹` is closed (its graph is the flipped graph of `A`).
* `FredholmCE.A_invA`: `A (A⁻¹ u) = u`.
* `FredholmCE.dense_invA_domain`: `A⁻¹` is densely defined.
* `FredholmCE.cxK1`: `0 → ℝ⁰ --0--> ℓ² --A⁻¹--> ℓ² → 0`: `V¹ ∩ V₁* = D(A⁻¹)` with compact inclusion in `ℓ²`.

## References

* [QuennevilleBelair2015], §4.2 (Hilbert complexes, domain complex, harmonic forms, the
  compactness property and the claims "compactness ⇒ Fredholm ⇒ closed", Thm 4.1, Thm 4.2);
  the thesis follows [BruningLesch1992] and [AFW2010] there. §4.4 (Thms 4.6–4.7) is the
  length-2 setting `W0 → W1 → W2` of `HilbertComplex2`.
* [BruningLesch1992] (Hilbert complexes; Fredholm = finite-dimensional cohomology, which
  implies closed range).
* [AFW2010], §3 (abstract Hilbert complexes: domain complex, closed and Fredholm complexes,
  Hodge decomposition, Poincaré inequality, compactness property).
* [Arnold2018] (book treatment of Hilbert complexes and the compactness property in finite
  element exterior calculus).
-/

open scoped RealInnerProductSpace Topology
open Set Filter LinearPMap

@[expose] public noncomputable section

namespace Feec.Legacy

/-! ### The compactness property at the `W` level -/

namespace HilbertComplex2

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    (H : HilbertComplex2 W0 W1 W2)

-- `orthogonal_ker_d1_le` and `orthogonal_ker_adjoint_d0_le` live in `Feec.Legacy.Adjoint`.

/-! ### Bounded complexes as `HilbertComplex2` -/

section Bounded

omit [CompleteSpace W0] [CompleteSpace W1] in
/-- An everywhere-defined continuous operator is closed. -/
theorem isClosed_toPMap_top (A : W0 →L[ℝ] W1) : ((A : W0 →ₗ[ℝ] W1).toPMap ⊤).IsClosed := by
  have : (((A : W0 →ₗ[ℝ] W1).toPMap ⊤).graph : Set (W0 × W1)) = {p | p.2 = A p.1} := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearPMap.mem_graph_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hz]; rfl
    · intro h
      exact ⟨⟨x, Submodule.mem_top⟩, rfl, h.symm⟩
  rw [LinearPMap.IsClosed, this]
  exact isClosed_eq continuous_snd (A.continuous.comp continuous_fst)

omit [CompleteSpace W0] [CompleteSpace W1] in
/-- `N(f|_⊤) = N(f)`. -/
theorem ker_toPMap_top (f : W0 →ₗ[ℝ] W1) : (f.toPMap ⊤).ker = LinearMap.ker f := by
  rw [LinearMap.toPMap_ker, top_inf_eq]

omit [CompleteSpace W0] [CompleteSpace W1] in
/-- `R(f|_⊤) = R(f)`. -/
theorem range_toPMap_top (f : W0 →ₗ[ℝ] W1) :
    LinearMap.range (f.toPMap ⊤).toFun = LinearMap.range f := by
  change LinearMap.range (f.comp (⊤ : Submodule ℝ W0).subtype) = _
  rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_top]

/-- A bounded complex `W0 --A--> W1 --B--> W2` (`B A = 0`) as a Hilbert complex of
everywhere-defined operators. Cf. [QuennevilleBelair2015, §4.2]; [AFW2010, §3]. -/
def ofBounded (A : W0 →L[ℝ] W1) (B : W1 →L[ℝ] W2) (hBA : ∀ x, B (A x) = 0) :
    HilbertComplex2 W0 W1 W2 where
  d0 := (A : W0 →ₗ[ℝ] W1).toPMap ⊤
  d1 := (B : W1 →ₗ[ℝ] W2).toPMap ⊤
  dense0 := by simp
  dense1 := by simp
  closed0 := isClosed_toPMap_top A
  closed1 := isClosed_toPMap_top B
  map_mem _ := Submodule.mem_top
  comp_zero x := hBA x

end Bounded

end HilbertComplex2

/-! ### Counterexample to "Fredholm ⇒ closed" with the `W`-level definitions -/

namespace FredholmCE

/-- The trivial Hilbert space `ℝ⁰`. -/
abbrev R0 := EuclideanSpace ℝ (Fin 0)

/-- The `W`-level complex `0 → ℓ² --A--> ℓ² --0--> ℝ⁰ → 0`, `A = diag(1/(n+1))`, as a
`HilbertComplex2`, i.e. a Hilbert complex of three spaces `W0 → W1 → W2` as in Thesis §4.2. -/
def cxW : HilbertComplex2 L2 L2 R0 :=
  HilbertComplex2.ofBounded A 0 fun _ => rfl

/-! #### An infinite-dimensional witness of the compactness property -/

/-- Truncation `A_N = Σ_{n<N} (1/(n+1)) ⟨e_n, ·⟩ e_n` of `A` (finite rank). -/
def Atr (N : ℕ) : L2 →L[ℝ] L2 :=
  ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1)) •
    (ContinuousLinearMap.toSpanSingleton ℝ (lp.single 2 n (1 : ℝ) : L2)).comp
      (innerSL ℝ (lp.single 2 n (1 : ℝ) : L2))

/-- The unbounded operator `A⁻¹ = diag(n+1)` on `ℓ²`, with domain `R(A)`. -/
def invA : L2 →ₗ.[ℝ] L2 := ((A : L2 →ₗ[ℝ] L2).toPMap ⊤).inverse

/-- `N(A) = 0`. -/
theorem ker_A_toPMap : ((A : L2 →ₗ[ℝ] L2).toPMap ⊤).ker = ⊥ := by
  rw [HilbertComplex2.ker_toPMap_top, LinearMap.ker_eq_bot]; exact A_injective

/-- `D(A⁻¹) = R(A)`. -/
theorem invA_domain : invA.domain = LinearMap.range (A : L2 →ₗ[ℝ] L2) := by
  rw [invA, inverse_domain, HilbertComplex2.range_toPMap_top]

/-- `A⁻¹` is closed (its graph is the flipped graph of `A`). -/
theorem invA_isClosed : invA.IsClosed :=
  (inverse_closed_iff ker_A_toPMap).2 (HilbertComplex2.isClosed_toPMap_top A)

/-- `A (A⁻¹ u) = u`. -/
theorem A_invA (u : invA.domain) : A (invA u) = u := by
  have h : ((u : L2), invA u) ∈ ((A : L2 →ₗ[ℝ] L2).toPMap ⊤).inverse.graph := invA.mem_graph u
  rw [inverse_graph ker_A_toPMap] at h
  obtain ⟨⟨a, b⟩, hab, he⟩ := h
  obtain ⟨y, hy1, hy2⟩ := (mem_graph_iff _).1 hab
  simp only [LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.swap_prod_mk, Prod.mk.injEq] at he
  dsimp only at hy1 hy2
  rw [← he.1, ← he.2, ← hy2, ← hy1]; rfl

/-- `A⁻¹` is densely defined. -/
theorem dense_invA_domain : Dense (invA.domain : Set L2) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    eq_bot_iff]
  intro y hy
  refine (Submodule.mem_bot ℝ).2 (eq_zero_of_inner_A_single fun n => ?_)
  exact (Submodule.mem_orthogonal _ _).1 hy _ (invA_domain ▸ ⟨_, rfl⟩)

/-- `0 → ℝ⁰ --0--> ℓ² --A⁻¹--> ℓ² → 0`: `V¹ ∩ V₁* = D(A⁻¹)` with compact inclusion in `ℓ²`. -/
def cxK1 : HilbertComplex2 R0 L2 L2 where
  d0 := ((0 : R0 →L[ℝ] L2) : R0 →ₗ[ℝ] L2).toPMap ⊤
  d1 := invA
  dense0 := by simp
  dense1 := dense_invA_domain
  closed0 := HilbertComplex2.isClosed_toPMap_top 0
  closed1 := invA_isClosed
  map_mem _ := invA.domain.zero_mem
  comp_zero _ := invA.map_zero

end FredholmCE

end Feec.Legacy
