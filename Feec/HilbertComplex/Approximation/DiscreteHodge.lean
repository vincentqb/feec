module

public import Feec.HilbertComplex.Approximation.CochainProjection

/-!
# The discrete Hodge decomposition and the harmonic gap

For a finite-dimensional subcomplex `Vₕ` of a Hilbert complex, the discrete complex has closed
range at every index, so the strong Hodge decomposition holds on `Vₕ`:
`Vₕⁱ = 𝔅ₕⁱ ⊕ ℌₕⁱ ⊕ 𝔅ₕ*ⁱ`, `𝔷ₕⁱ = 𝔅ₕⁱ ⊕ ℌₕⁱ`, and `ℌₕⁱ ≅ 𝔷ₕⁱ / 𝔅ₕⁱ`. The discrete harmonic
forms are in general *not* harmonic (`𝔅ₕ ⊆ 𝔅` but `𝔅ₕᗮ ⊉ 𝔅ᗮ`); a cochain projection controls the
gap between `ℌ` and `ℌₕ`.

## Main results

* `Subcomplex.closedRangeAt`, `Subcomplex.dual_closedRangeAt`, `Subcomplex.hodge`: the discrete
  Hodge decomposition (strong form, every index).
* `Subcomplex.cyclesW_eq`: `𝔷ₕⁱ = 𝔅ₕⁱ ⊕ ℌₕⁱ` in `Wⁱ`.
* `Subcomplex.cohomologyEquivHarmonic`: discrete cohomology `≅` discrete harmonic forms.
* `CochainProjection.norm_sub_starProjection_harmonicW_le`: the **harmonic gap**
  `‖q - P_{ℌₕ} q‖ ≤ ‖q - π q‖` for `q ∈ ℌ`.
* `CochainProjection.injective_starProjection_harmonicW`: if `‖q - π q‖ < ‖q‖` on `ℌ ∖ 0`, then
  `P_{ℌₕ}` is injective on `ℌ` (so `dim ℌ ≤ dim ℌₕ`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–3.4 (discrete Hodge decomposition, Thm 3.5 gap estimate)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5
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

/-- The discrete complex has closed range at every index. -/
theorem closedRangeAt (i : ι) : S.toHilbertComplex.ClosedRangeAt i :=
  Submodule.closed_of_finiteDimensional _

/-- The dual of the discrete complex has closed range at every index. -/
theorem dual_closedRangeAt (i : ι) : S.toHilbertComplex.dual.ClosedRangeAt i :=
  Submodule.closed_of_finiteDimensional _

/-- **Discrete Hodge decomposition**: `Vₕⁱ = 𝔅ₕⁱ ⊕ ℌₕⁱ ⊕ 𝔅ₕ*ⁱ`, pairwise orthogonal, at every
index. -/
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

/-- **`𝔷ₕⁱ = 𝔅ₕⁱ ⊕ ℌₕⁱ`** (orthogonal), in `Wⁱ`. -/
theorem cyclesW_eq (i : ι) : S.cyclesW i = S.boundariesW i ⊔ S.harmonicW i := by
  rw [← S.map_cycles, ← S.map_boundaries, ← S.map_harmonic, ← Submodule.map_sup,
    S.toHilbertComplex.boundaries_sup_harmonic (S.closedRangeAt i)]

/-- **Discrete cohomology ≅ discrete harmonic forms**. -/
def cohomologyEquivHarmonic (i : ι) :
    S.toHilbertComplex.cohomology i ≃ₗ[𝕜] S.toHilbertComplex.harmonic i :=
  S.toHilbertComplex.cohomologyEquivHarmonic (S.closedRangeAt i)

/-- On harmonic `q`, the orthogonal projections onto `𝔷ₕ` and `ℌₕ` agree. -/
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

/-- **The harmonic gap**: for a harmonic `q`, `‖q - P_{ℌₕ} q‖ ≤ ‖q - π q‖`. -/
theorem norm_sub_starProjection_harmonicW_le {i : ι} {q : W i} (hq : q ∈ H.harmonic i) :
    ‖q - (S.harmonicW i).starProjection q‖ ≤ ‖q - P.π i q‖ := by
  rw [S.starProjection_harmonicW_eq hq, ← dist_eq_norm, ← dist_eq_norm,
    Submodule.dist_starProjection_eq_infDist]
  exact Metric.infDist_le_dist_of_mem (P.mem_cyclesW (H.harmonic_le_cycles i hq))

/-- If `‖q - π q‖ < ‖q‖` for every nonzero harmonic `q`, the projection onto `ℌₕ` is injective
on `ℌ`. -/
theorem injective_starProjection_harmonicW {i : ι}
    (hgap : ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - P.π i q‖ < ‖q‖) :
    Function.Injective fun q : H.harmonic i => (S.harmonicW i).starProjection (q : W i) := by
  intro q q' hqq'
  by_contra hne
  have hd : (q : W i) - q' ≠ 0 := sub_ne_zero.2 fun h => hne (Subtype.ext h)
  have hmem : (q : W i) - q' ∈ H.harmonic i := sub_mem q.2 q'.2
  have h0 : (S.harmonicW i).starProjection ((q : W i) - q') = 0 := by
    rw [_root_.map_sub, sub_eq_zero]; exact hqq'
  have := P.norm_sub_starProjection_harmonicW_le hmem
  rw [h0, sub_zero] at this
  exact absurd (hgap _ hmem hd) (not_lt.2 this)

end CochainProjection

end Subcomplex

end Feec.HilbertComplex
