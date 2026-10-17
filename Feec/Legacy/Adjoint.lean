module

public import Feec.Legacy.ShortComplex
public import Feec.Legacy.Operators
public import Feec.Operator.Adjoint
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Feec.Counterexamples.Ell2

/-!
# Unbounded operators: adjoints, graph relations, closed range (Thesis §4.1–4.2)

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use.
Most of the original module was re-derived in the general layers (see
`docs/migration/map.tsv`); what remains is listed below.

## Contents

* `mem_graph_iff_of_isClosed`: Weak characterisation of the graph of a closed densely defined operator: `(x, y) ∈ Γ(T)` iff `⟪T* w, x⟫ = ⟪w, y⟫` for all `w ∈ D(T*)` (Thesis §4.1, the relation `Γ(T) = Γ̃(T*)ᗮ` unpacked).
* `dense_adjoint_domain`: The adjoint of a closed densely defined operator is densely defined (Thesis §4.1).
* `adjoint_adjoint`: von Neumann: `T** = T` for closed densely defined `T`.
* `orthogonal_range_adjoint`: Thesis (4.1c): `R(T*)ᗮ = N(T)` for closed densely defined `T`.
* `range_adjoint_eq_orthogonal_ker`: **Closed range theorem**, first half: if `T` is closed, densely defined and `R(T)` is closed, then `R(T*) = N(T)ᗮ`.
* `isClosed_range_adjoint_iff`: **Closed range theorem**: for closed densely defined `T`, `R(T*)` is closed iff `R(T)` is.
* `isSkewAdjoint_iff`: Thesis §4.1: `T` is skew-adjoint iff it is skew-symmetric and `D(T*) ⊂ D(T)`.
* `HilbertComplex2.inner_adjoint_d0`: `⟪d1* u, d0 v⟫ = 0` (auxiliary for the dual complex, Thesis §4.2).
* `HilbertComplex2.adjoint_map_mem`: `d1* V₂* ⊂ V₁*` (Thesis §4.2, dual complex).
* `HilbertComplex2.adjoint_comp_zero`: `d0* d1* = 0` (Thesis §4.2, dual complex).
* `HilbertComplex2.dual`: The dual Hilbert complex `W2 --d1*--> W1 --d0*--> W0` (Thesis §4.2).
* `HilbertComplex2.range_adjoint_d1_eq`: `B*₁ = (Z¹)ᗮ` for a closed complex (Thesis §4.2, used in Thm 4.1).
* `HilbertComplex2.harmonic`: Harmonic forms `ℌ¹ = Z¹ ∩ Z*₁ = N(d1) ∩ N(d0*)` (Thesis §4.2, Thm 4.1).
* `HilbertComplex2.orthogonal_range_d0`: `(B⁰)ᗮ = Z*₀`, i.e.
* `HilbertComplex2.orthogonal_range_adjoint_d1`: `(B*₁)ᗮ = Z¹`, i.e.
* `HilbertComplex2.range_d0_le_ker_d1`: `B⁰ ⊂ Z¹` (from `d1 d0 = 0`).
* `HilbertComplex2.orthogonal_ker_d1_le`: `(Z¹)ᗮ ⊆ Z*₁`, i.e.
* `HilbertComplex2.orthogonal_ker_adjoint_d0_le`: `(Z*₁)ᗮ = cl B⁰ ⊆ Z¹`, i.e.
* `HilbertComplex2.harmonic_eq`: `ℌ = (cl B⁰)ᗮ ∩ (cl B*₁)ᗮ` (Thesis Thm 4.1, `W`-level).
* `HilbertComplex2.isOrtho_closure_range_d0_harmonic`: `cl B⁰ ⟂ ℌ` (Thesis Thm 4.1, `W`-level).
* `HilbertComplex2.isOrtho_harmonic_closure_range_adjoint_d1`: `ℌ ⟂ cl B*₁` (Thesis Thm 4.1, `W`-level).
* `HilbertComplex2.isOrtho_closure_range_d0_closure_range_adjoint_d1`: `cl B⁰ ⟂ cl B*₁` (Thesis Thm 4.1, `W`-level).
* `HilbertComplex2.ker_d1_eq`: `Z¹ = cl B⁰ ⊕ ℌ` (orthogonal sum; Thesis §4.2, `W`-level).
* `HilbertComplex2.hodge_W`: **Hodge decomposition in `W`** (Thesis Thm 4.1, `W`-level, no closed-range hypothesis): `W1 = cl B⁰ ⊕ ℌ ⊕ cl B*₁`, an orthogonal sum of closed subspaces.
* `HilbertComplex2.hodge_W_of_closedRange`: **Hodge decomposition in `W` for a closed complex** (Thesis Thm 4.1, `W`-level): `W1 = B⁰ ⊕ ℌ ⊕ B*₁` without closures, with `B*₁ = (Z¹)ᗮ` (`range_adjoint_d1_eq`).

## References

* [QuennevilleBelair2015], §4.1 (unbounded operators, graph relations, (4.1a–d)), §4.2
  (Hilbert complexes, dual complex, Thm 4.1 Hodge decomposition, Thm 4.2 Poincaré inequality),
  §4.3 (closed-kernel claim), proof of Thm 4.6 (`d** = d`)
* [AFW2010], §3 (Hilbert complexes: dual complex, Hodge decomposition, Poincaré inequality;
  followed by the thesis in §4.2)
* [BruningLesch1992] (Hilbert complexes; followed by the thesis in §4.2)
* [Arnold2018] (abstract Hilbert complex framework of FEEC)
-/

open scoped RealInnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.Legacy

/-! ### Graph relations, `T** = T`, (4.1a–d), closed range, skew-adjointness

The statements below are the real-scalar (`𝕜 := ℝ`) specializations of the `RCLike` results in
`Feec.ForMathlib.LinearPMap.{GraphSpace,ClosedRange,Skew}`, kept with their old statements. -/

section Adjoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Weak characterisation of the graph of a closed densely defined operator:
`(x, y) ∈ Γ(T)` iff `⟪T* w, x⟫ = ⟪w, y⟫` for all `w ∈ D(T*)` (Thesis §4.1, the relation
`Γ(T) = Γ̃(T*)ᗮ` unpacked). -/
theorem mem_graph_iff_of_isClosed {T : E →ₗ.[ℝ] F} (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) {x : E} {y : F} :
    (x, y) ∈ T.graph ↔ ∀ w : T†.domain, ⟪T† w, x⟫ = ⟪(w : F), y⟫ :=
  LinearPMap.mem_graph_iff_of_isClosed hT hc

/-- The adjoint of a closed densely defined operator is densely defined (Thesis §4.1).
See [QuennevilleBelair2015, §4.1]. -/
theorem dense_adjoint_domain (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) : Dense (T†.domain : Set F) :=
  LinearPMap.dense_adjoint_domain T hT hc

/-- von Neumann: `T** = T` for closed densely defined `T`.

Thesis gap: stated in passing in the proof of Thm 4.6 ("`d` is a closed operator and so
`d** = d`") and equivalent to the §4.1 graph relation `Γ(T) = Γ̃(T*)ᗮ`, but not proved; density
of `D(d)` is also needed and not mentioned.

See [QuennevilleBelair2015, §4.1 and proof of Thm 4.6]. -/
theorem adjoint_adjoint (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) (hc : T.IsClosed) :
    T†† = T :=
  LinearPMap.adjoint_adjoint T hT hc

/-- Thesis (4.1c): `R(T*)ᗮ = N(T)` for closed densely defined `T`.
See [QuennevilleBelair2015, (4.1c)]. -/
theorem orthogonal_range_adjoint (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) : (LinearMap.range T†.toFun)ᗮ = T.ker :=
  LinearPMap.orthogonal_range_adjoint T hT hc

end Adjoint

/-! ### The closed range theorem -/

section ClosedRange

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Closed range theorem**, first half: if `T` is closed, densely defined and `R(T)` is
closed, then `R(T*) = N(T)ᗮ`. Thesis gap (§4.2): asserted without proof.
See [QuennevilleBelair2015, §4.2]; cf. [BruningLesch1992]. -/
theorem range_adjoint_eq_orthogonal_ker (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) (hR : IsClosed (LinearMap.range T.toFun : Set F)) :
    LinearMap.range T†.toFun = T.kerᗮ :=
  LinearPMap.range_adjoint_eq_orthogonal_ker T hT hc hR

/-- **Closed range theorem**: for closed densely defined `T`, `R(T*)` is closed iff `R(T)` is.
See [QuennevilleBelair2015, §4.2]; cf. [BruningLesch1992], [AFW2010, §3]. -/
theorem isClosed_range_adjoint_iff (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) :
    IsClosed (LinearMap.range T†.toFun : Set E) ↔ IsClosed (LinearMap.range T.toFun : Set F) :=
  LinearPMap.isClosed_range_adjoint_iff T hT hc

end ClosedRange

/-! ### Skew-adjoint operators -/

section Skew

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Thesis §4.1: `T` is skew-adjoint iff it is skew-symmetric and `D(T*) ⊂ D(T)`.
See [QuennevilleBelair2015, §4.1]. -/
theorem isSkewAdjoint_iff (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E)) :
    IsSkewAdjoint L ↔ IsSkewSymm L ∧ L†.domain ≤ L.domain :=
  LinearPMap.isSkewAdjoint_iff hD

end Skew

/-! ### Counterexample: kernels of non-closed operators

Moved to `Feec.Counterexamples.Ell2` (over any `RCLike 𝕜`); the old names are shims. -/

section KerCounterexample

/-- `ℓ²(ℕ, ℝ)`. -/
local notation "ℓ2" => lp (fun _ : ℕ => ℝ) 2

end KerCounterexample

/-! ### The dual complex (Thesis §4.2) -/

namespace HilbertComplex2

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    (H : HilbertComplex2 W0 W1 W2)

/-- `⟪d1* u, d0 v⟫ = 0` (auxiliary for the dual complex, Thesis §4.2). -/
theorem inner_adjoint_d0 (u : H.d1†.domain) (v : H.d0.domain) : ⟪H.d1† u, H.d0 v⟫ = 0 :=
  Operator.inner_adjoint_apply_eq_zero H.dense1 H.map_mem H.comp_zero u v

/-- `d1* V₂* ⊂ V₁*` (Thesis §4.2, dual complex). -/
theorem adjoint_map_mem (u : H.d1†.domain) : H.d1† u ∈ H.d0†.domain :=
  Operator.adjoint_mapsTo H.dense1 H.map_mem H.comp_zero u

/-- `d0* d1* = 0` (Thesis §4.2, dual complex). -/
theorem adjoint_comp_zero (u : H.d1†.domain) : H.d0† ⟨H.d1† u, H.adjoint_map_mem u⟩ = 0 :=
  Operator.adjoint_comp_eq_zero H.dense0 H.dense1 H.map_mem H.comp_zero u

/-- The dual Hilbert complex `W2 --d1*--> W1 --d0*--> W0` (Thesis §4.2).

Thesis gap: that the `dₖ*` are closed and densely defined and satisfy `d* V* ⊂ V*`,
`d* d* = 0` is asserted without proof; density of `D(d*)` is `dense_adjoint_domain`.

See [QuennevilleBelair2015, §4.2]; cf. [AFW2010, §3], [BruningLesch1992]. -/
def dual : HilbertComplex2 W2 W1 W0 where
  d0 := H.d1†
  d1 := H.d0†
  dense0 := dense_adjoint_domain _ H.dense1 H.closed1
  dense1 := dense_adjoint_domain _ H.dense0 H.closed0
  closed0 := adjoint_isClosed H.dense1
  closed1 := adjoint_isClosed H.dense0
  map_mem := H.adjoint_map_mem
  comp_zero := H.adjoint_comp_zero

/-- `B*₁ = (Z¹)ᗮ` for a closed complex (Thesis §4.2, used in Thm 4.1).
See [QuennevilleBelair2015, §4.2]. -/
theorem range_adjoint_d1_eq (h : H.ClosedRange) :
    LinearMap.range H.d1†.toFun = H.d1.kerᗮ :=
  range_adjoint_eq_orthogonal_ker _ H.dense1 H.closed1 h.2

/-! ### Hodge decomposition in `W` (Thesis Thm 4.1, `W`-level) -/

/-- Harmonic forms `ℌ¹ = Z¹ ∩ Z*₁ = N(d1) ∩ N(d0*)` (Thesis §4.2, Thm 4.1).
See [QuennevilleBelair2015, §4.2]; cf. [AFW2010, §3]. -/
def harmonic : Submodule ℝ W1 := H.d1.ker ⊓ H.d0†.ker

/-- `(B⁰)ᗮ = Z*₀`, i.e. (4.1a) for `d0`. -/
theorem orthogonal_range_d0 : (LinearMap.range H.d0.toFun)ᗮ = H.d0†.ker :=
  orth_range_eq_ker_adjoint _ H.dense0

/-- `(B*₁)ᗮ = Z¹`, i.e. (4.1c) for `d1`. -/
theorem orthogonal_range_adjoint_d1 : (LinearMap.range H.d1†.toFun)ᗮ = H.d1.ker :=
  orthogonal_range_adjoint _ H.dense1 H.closed1

/-- `B⁰ ⊂ Z¹` (from `d1 d0 = 0`). -/
theorem range_d0_le_ker_d1 : LinearMap.range H.d0.toFun ≤ H.d1.ker :=
  Operator.range_le_ker H.map_mem H.comp_zero

/-- `(Z¹)ᗮ ⊆ Z*₁`, i.e. `(ker d1)ᗮ ⊆ ker d0*`, **without closed range**: since `B⁰ ⊆ Z¹`,
`(Z¹)ᗮ ⊆ (B⁰)ᗮ = Z*₀` (Thesis Thm 4.6, σ-step).

Thesis gap: the thesis uses `(Z¹)ᗮ = B*₁`, which needs closed range; only the inclusion
`(ker d1)ᗮ ⊆ ker d0*` is needed, and it holds in every Hilbert complex.

See [QuennevilleBelair2015, proof of Thm 4.6]. -/
theorem orthogonal_ker_d1_le : H.d1.kerᗮ ≤ H.d0†.ker :=
  Operator.orthogonal_ker_le_ker_adjoint H.dense0 H.map_mem H.comp_zero

/-- `(Z*₁)ᗮ = cl B⁰ ⊆ Z¹`, i.e. `(ker d0*)ᗮ ⊆ ker d1`, **without closed range**
(Thesis Thm 4.6, ρ-step, omitted in the thesis as "similar").
See [QuennevilleBelair2015, proof of Thm 4.6]. -/
theorem orthogonal_ker_adjoint_d0_le : H.d0†.kerᗮ ≤ H.d1.ker :=
  Operator.orthogonal_ker_adjoint_le_ker H.dense0 H.closed1 H.map_mem H.comp_zero

/-- `ℌ = (cl B⁰)ᗮ ∩ (cl B*₁)ᗮ` (Thesis Thm 4.1, `W`-level). -/
theorem harmonic_eq :
    H.harmonic = (LinearMap.range H.d0.toFun).topologicalClosureᗮ ⊓
      (LinearMap.range H.d1†.toFun).topologicalClosureᗮ := by
  rw [Submodule.orthogonal_closure, Submodule.orthogonal_closure, orthogonal_range_d0,
    orthogonal_range_adjoint_d1, harmonic, inf_comm]

/-- `cl B⁰ ⟂ ℌ` (Thesis Thm 4.1, `W`-level). -/
theorem isOrtho_closure_range_d0_harmonic :
    (LinearMap.range H.d0.toFun).topologicalClosure ⟂ H.harmonic :=
  (Submodule.isOrtho_iff_le.2 (H.harmonic_eq ▸ inf_le_left)).symm

/-- `ℌ ⟂ cl B*₁` (Thesis Thm 4.1, `W`-level). -/
theorem isOrtho_harmonic_closure_range_adjoint_d1 :
    H.harmonic ⟂ (LinearMap.range H.d1†.toFun).topologicalClosure :=
  Submodule.isOrtho_iff_le.2 (H.harmonic_eq ▸ inf_le_right)

/-- `cl B⁰ ⟂ cl B*₁` (Thesis Thm 4.1, `W`-level). -/
theorem isOrtho_closure_range_d0_closure_range_adjoint_d1 :
    (LinearMap.range H.d0.toFun).topologicalClosure ⟂
      (LinearMap.range H.d1†.toFun).topologicalClosure := by
  rw [Submodule.isOrtho_iff_le, Submodule.orthogonal_closure, orthogonal_range_adjoint_d1]
  exact Submodule.topologicalClosure_minimal _ H.range_d0_le_ker_d1 (isClosed_ker H.closed1)

/-- `Z¹ = cl B⁰ ⊕ ℌ` (orthogonal sum; Thesis §4.2, `W`-level). -/
theorem ker_d1_eq :
    H.d1.ker = (LinearMap.range H.d0.toFun).topologicalClosure ⊔ H.harmonic := by
  set A := (LinearMap.range H.d0.toFun).topologicalClosure
  set C := (LinearMap.range H.d1†.toFun).topologicalClosure
  have : CompleteSpace A := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hC : Cᗮ = H.d1.ker := by
    rw [Submodule.orthogonal_closure, orthogonal_range_adjoint_d1]
  have hAC : A ≤ Cᗮ := Submodule.isOrtho_iff_le.1
    H.isOrtho_closure_range_d0_closure_range_adjoint_d1
  rw [H.harmonic_eq, ← hC]
  exact (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hAC).symm

/-- **Hodge decomposition in `W`** (Thesis Thm 4.1, `W`-level, no closed-range hypothesis):
`W1 = cl B⁰ ⊕ ℌ ⊕ cl B*₁`, an orthogonal sum of closed subspaces.

Extension: the thesis states the decomposition only for closed complexes, obtaining
`B*ₖ = (Zᵏ)ᗮ` from (4.1); this unconditional form with closures strengthens it. The closed
case is `hodge_W_of_closedRange`.

See [QuennevilleBelair2015, Thm 4.1]; cf. [BruningLesch1992] (decomposition with closures,
no closed-range hypothesis), [AFW2010, §3], [Arnold2018]. -/
theorem hodge_W :
    (LinearMap.range H.d0.toFun).topologicalClosure ⊔ H.harmonic ⊔
        (LinearMap.range H.d1†.toFun).topologicalClosure = ⊤ ∧
      (LinearMap.range H.d0.toFun).topologicalClosure ⟂ H.harmonic ∧
      H.harmonic ⟂ (LinearMap.range H.d1†.toFun).topologicalClosure ∧
      (LinearMap.range H.d0.toFun).topologicalClosure ⟂
        (LinearMap.range H.d1†.toFun).topologicalClosure := by
  refine ⟨?_, H.isOrtho_closure_range_d0_harmonic, H.isOrtho_harmonic_closure_range_adjoint_d1,
    H.isOrtho_closure_range_d0_closure_range_adjoint_d1⟩
  set C := (LinearMap.range H.d1†.toFun).topologicalClosure
  have : CompleteSpace C := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hC : Cᗮ = H.d1.ker := by
    rw [Submodule.orthogonal_closure, orthogonal_range_adjoint_d1]
  rw [← H.ker_d1_eq, ← hC, sup_comm]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- **Hodge decomposition in `W` for a closed complex** (Thesis Thm 4.1, `W`-level):
`W1 = B⁰ ⊕ ℌ ⊕ B*₁` without closures, with `B*₁ = (Z¹)ᗮ` (`range_adjoint_d1_eq`).

Thesis gap: closedness of `B*₁` (needed to drop the closure) is the closed range theorem
`isClosed_range_adjoint_iff`, which the thesis does not prove.

See [QuennevilleBelair2015, Thm 4.1]; cf. [AFW2010, §3], [Arnold2018]. -/
theorem hodge_W_of_closedRange (h : H.ClosedRange) :
    LinearMap.range H.d0.toFun ⊔ H.harmonic ⊔ LinearMap.range H.d1†.toFun = ⊤ ∧
      LinearMap.range H.d0.toFun ⟂ H.harmonic ∧
      H.harmonic ⟂ LinearMap.range H.d1†.toFun ∧
      LinearMap.range H.d0.toFun ⟂ LinearMap.range H.d1†.toFun := by
  have h1 : IsClosed (LinearMap.range H.d1†.toFun : Set W1) :=
    (isClosed_range_adjoint_iff _ H.dense1 H.closed1).2 h.2
  have := H.hodge_W
  rwa [h.1.submodule_topologicalClosure_eq, h1.submodule_topologicalClosure_eq] at this

end HilbertComplex2

end Feec.Legacy
