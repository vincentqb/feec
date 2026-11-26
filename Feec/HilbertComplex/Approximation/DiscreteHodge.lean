module

public import Feec.HilbertComplex.Approximation.CochainProjection

/-!
# The discrete Hodge decomposition and the harmonic gap

The Hodge decomposition of a finite-dimensional subcomplex of a Hilbert complex, and the bound of
the harmonic gap by a cochain projection.

## Main results

* `Subcomplex.hodge`: `Vₕⁱ = 𝔅ₕⁱ ⊕ ℌₕⁱ ⊕ 𝔅ₕ*ⁱ`, orthogonally, at every index.
* `CochainProjection.norm_sub_starProjection_harmonicW_le`: `‖q - P_{ℌₕ} q‖ ≤ ‖q - π q‖` on `ℌ`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace Subcomplex

variable (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)]

theorem closedRangeAt (i : ι) : S.toHilbertComplex.ClosedRangeAt i :=
  Submodule.closed_of_finiteDimensional _

theorem dual_closedRangeAt (i : ι) : S.toHilbertComplex.dual.ClosedRangeAt i :=
  Submodule.closed_of_finiteDimensional _

/-- **Discrete Hodge decomposition**: `Vₕⁱ = 𝔅ₕⁱ ⊕ ℌₕⁱ ⊕ 𝔅ₕ*ⁱ`, pairwise orthogonal. -/
theorem hodge (i : ι) :
    S.toHilbertComplex.boundaries i ⊔ S.toHilbertComplex.harmonic i ⊔
        S.toHilbertComplex.dual.boundaries i = ⊤ ∧
      S.toHilbertComplex.boundaries i ⟂ S.toHilbertComplex.harmonic i ∧
      S.toHilbertComplex.harmonic i ⟂ S.toHilbertComplex.dual.boundaries i ∧
      S.toHilbertComplex.boundaries i ⟂ S.toHilbertComplex.dual.boundaries i :=
  S.toHilbertComplex.hodge_of_closedRangeAt (S.closedRangeAt i) (S.dual_closedRangeAt i)

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
private theorem map_subtype_eq {i : ι} {M : Submodule 𝕜 (S.V i)} {N : Submodule 𝕜 (W i)}
    (hN : N ≤ S.V i) (h : ∀ x : S.V i, x ∈ M ↔ (x : W i) ∈ N) : M.map (S.V i).subtype = N := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact (h y).1 hy
  · intro hx; exact ⟨⟨x, hN hx⟩, (h _).2 hx, rfl⟩

theorem map_cycles (i : ι) : (S.toHilbertComplex.cycles i).map (S.V i).subtype = S.cyclesW i :=
  S.map_subtype_eq (S.cyclesW_le i) fun x => S.mem_cycles_iff.trans
    ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem map_boundaries (i : ι) :
    (S.toHilbertComplex.boundaries i).map (S.V i).subtype = S.boundariesW i :=
  S.map_subtype_eq (S.boundariesW_le_V i) fun _ => S.mem_boundaries_iff

theorem map_harmonic (i : ι) :
    (S.toHilbertComplex.harmonic i).map (S.V i).subtype = S.harmonicW i :=
  S.map_subtype_eq (S.harmonicW_le_V i) fun _ => S.mem_harmonic_iff

theorem cyclesW_eq (i : ι) : S.cyclesW i = S.boundariesW i ⊔ S.harmonicW i := by
  rw [← S.map_cycles, ← S.map_boundaries, ← S.map_harmonic, ← Submodule.map_sup,
    S.toHilbertComplex.boundaries_sup_harmonic (S.closedRangeAt i)]

/-- Discrete cohomology `≅` discrete harmonic forms. -/
def cohomologyEquivHarmonic (i : ι) :
    S.toHilbertComplex.cohomology i ≃ₗ[𝕜] S.toHilbertComplex.harmonic i :=
  S.toHilbertComplex.cohomologyEquivHarmonic (S.closedRangeAt i)

theorem starProjection_harmonicW_eq {i : ι} {q : W i} (hq : q ∈ H.harmonic i) :
    (S.harmonicW i).starProjection q = (S.cyclesW i).starProjection q := by
  set p := (S.cyclesW i).starProjection q
  have hp : p ∈ S.cyclesW i := Submodule.starProjection_apply_mem _ _
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw =>
    Submodule.starProjection_inner_eq_zero q w (S.harmonicW_le_cyclesW i hw)
  refine S.mem_harmonicW_iff.2 ⟨S.cyclesW_le i hp, S.cyclesW_le_cycles i hp, fun b hb => ?_⟩
  have h1 : ⟪b, q⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (S.boundariesW_le i hb) (H.mem_harmonic_iff.1 hq).2
  have h2 : ⟪q - p, b⟫ = 0 :=
    Submodule.starProjection_inner_eq_zero q b (S.boundariesW_le_cyclesW i hb)
  rw [inner_sub_left, sub_eq_zero] at h2
  rw [← inner_conj_symm, ← h2, inner_conj_symm, h1]

namespace CochainProjection

variable {S} (P : S.CochainProjection)

/-- **The harmonic gap**: `‖q - P_{ℌₕ} q‖ ≤ ‖q - π q‖` for harmonic `q` ([AFW2010], Thm 3.5). -/
theorem norm_sub_starProjection_harmonicW_le {i : ι} {q : W i} (hq : q ∈ H.harmonic i) :
    ‖q - (S.harmonicW i).starProjection q‖ ≤ ‖q - P.π i q‖ := by
  rw [S.starProjection_harmonicW_eq hq, ← dist_eq_norm, ← dist_eq_norm,
    Submodule.dist_starProjection_eq_infDist]
  exact Metric.infDist_le_dist_of_mem (P.mem_cyclesW (H.harmonic_le_cycles i hq))

end CochainProjection

end Subcomplex

end Feec.HilbertComplex
