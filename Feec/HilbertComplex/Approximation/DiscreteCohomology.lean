module

public import Feec.HilbertComplex.Approximation.QuasiOptimal

/-!
# Discrete cohomology: a cochain projection is an isomorphism on cohomology

Let `Vₕ` be a finite-dimensional subcomplex of a Hilbert complex `H` and `π` a cochain projection
onto `Vₕ`. Since `π` maps cycles to discrete cycles and boundaries to discrete boundaries, it
induces a map `Hⁱ(H) → Hⁱ(Vₕ)` on cohomology (`CochainProjection.cohomologyMap`), and since `π`
fixes `Vₕ` this map is **onto** (`cohomologyMap_surjective`): every discrete cycle is a cycle.
If `H` has closed range at `i` and `π` moves no harmonic form by its own length,

`‖q - π q‖ < ‖q‖`  for `0 ≠ q ∈ ℌⁱ`,

the map is also **one-to-one** (`cohomologyMap_injective`): write a cycle `z = b + q` with
`b ∈ 𝔅ⁱ`, `q ∈ ℌⁱ`; if `π z ∈ 𝔅ₕⁱ` then `π q ∈ 𝔅ₕⁱ ⊆ 𝔅ⁱ ⊥ q`, and the strict gap forces `q = 0`.
Hence `Hⁱ(Vₕ) ≅ Hⁱ(H)` (`CochainProjection.cohomologyEquiv`) and
`dim ℌₕⁱ = dim ℌⁱ` (`finrank_harmonicW_eq`); in particular `ℌⁱ` is finite-dimensional. No bound
on `π` is needed for the isomorphism itself.

The strict gap holds as soon as the harmonic gap `μ = sup_{q ∈ ℌ, ‖q‖ ≤ 1} ‖q - π q‖` is below
`1` (`norm_sub_π_lt_of_harmonicGap_lt_one`), so for a family of subcomplexes whose harmonic gap
tends to zero (`CochainProjection.tendsto_harmonicGap`: uniformly `W`-bounded projections
approximating `ℌ`) the discrete cohomology is **eventually the continuous cohomology**
(`eventually_finrank_cohomology_eq`, `eventually_finrank_harmonicW_eq`).

## Main definitions

* `Subcomplex.CochainProjection.cyclesMap`: `π : 𝔷ⁱ → 𝔷ₕⁱ`.
* `Subcomplex.CochainProjection.cohomologyMap`: the induced map `Hⁱ(H) → Hⁱ(Vₕ)`.
* `Subcomplex.CochainProjection.cohomologyEquiv`: `Hⁱ(H) ≃ Hⁱ(Vₕ)` under the strict gap.

## Main results

* `CochainProjection.cohomologyMap_surjective`, **`CochainProjection.cohomologyMap_injective`**.
* **`CochainProjection.finrank_cohomology_eq`**, **`CochainProjection.finrank_harmonicW_eq`**,
  `CochainProjection.finiteDimensional_harmonic`.
* `CochainProjection.norm_sub_π_lt_of_harmonicGap_lt_one`.
* **`CochainProjection.eventually_finrank_cohomology_eq`**,
  `CochainProjection.eventually_finrank_harmonicW_eq`: along any filter on which the harmonic gap
  tends to zero.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.4 (a cochain projection with `‖q - π q‖ < ‖q‖` on `ℌ \ 0` induces an isomorphism on
  cohomology), Thm 3.5 (the gap between `ℌ` and `ℌₕ`), §5.6 (finite element de Rham complexes)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  (cochain projections onto the finite element de Rham complexes)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Filter Topology

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace Subcomplex

namespace CochainProjection

section Single

variable {S : H.Subcomplex} [∀ i, FiniteDimensional 𝕜 (S.V i)] (P : S.CochainProjection)

/-- `π` on the cycles, valued in the discrete cycles `𝔷ₕⁱ` (the cycles of `S.toHilbertComplex`). -/
def cyclesMap (i : ι) : H.cycles i →ₗ[𝕜] S.toHilbertComplex.cycles i where
  toFun z := ⟨⟨P.π i z, P.mem i z⟩, S.mem_cycles_iff.2 (S.cyclesW_le_cycles i (P.mem_cyclesW z.2))⟩
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

@[simp] theorem coe_cyclesMap_apply (i : ι) (z : H.cycles i) :
    ((P.cyclesMap i z : S.V i) : W i) = P.π i z := rfl

/-- **The map induced on cohomology** `Hⁱ(H) → Hⁱ(Vₕ)`, `[z] ↦ [π z]`. [AFW2010], §3.3 -/
def cohomologyMap (i : ι) : H.cohomology i →ₗ[𝕜] S.toHilbertComplex.cohomology i :=
  Submodule.mapQ _ _ (P.cyclesMap i) fun _ hz => S.mem_boundaries_iff.2 (P.mem_boundariesW hz)

/-- **The induced map on cohomology is onto**: a discrete cycle `z` is a cycle with `π z = z`.
[AFW2010], §3.3 -/
theorem cohomologyMap_surjective (i : ι) : Function.Surjective (P.cohomologyMap i) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine ⟨Submodule.Quotient.mk ⟨((x : S.V i) : W i), S.mem_cycles_iff.1 x.2⟩, ?_⟩
  rw [cohomologyMap, Submodule.mapQ_apply]
  congr 1
  ext
  exact P.proj i _ (x : S.V i).2

/-- **The induced map on cohomology is one-to-one** under closed range and the strict gap
`‖q - π q‖ < ‖q‖` on `ℌⁱ \ 0`. [AFW2010], Thm 3.4 -/
theorem cohomologyMap_injective {i : ι} (hi : H.ClosedRangeAt i)
    (hgap : ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - P.π i q‖ < ‖q‖) :
    Function.Injective (P.cohomologyMap i) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [cohomologyMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  have hz : P.π i z ∈ S.boundariesW i := S.mem_boundaries_iff.1 hy
  have hz' : (z : W i) ∈ H.boundaries i ⊔ H.harmonic i := by
    rw [H.boundaries_sup_harmonic hi]; exact z.2
  obtain ⟨b, hb, q, hq, hbq⟩ := Submodule.mem_sup.1 hz'
  have hπq : P.π i q ∈ H.boundaries i := by
    have := (S.boundariesW i).sub_mem hz (P.mem_boundariesW hb)
    rw [← hbq, _root_.map_add, add_sub_cancel_left] at this
    exact S.boundariesW_le i this
  have hq0 : q = 0 := by
    by_contra hq0
    have h0 : ⟪P.π i q, q⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hπq (H.mem_harmonic_iff.1 hq).2
    have hle : ‖q‖ ^ 2 ≤ ‖q - P.π i q‖ * ‖q‖ := by
      rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), show ⟪q, q⟫ = ⟪q - P.π i q, q⟫ by
        rw [inner_sub_left, h0, sub_zero]]
      exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    have hpos : 0 < ‖q‖ := norm_pos_iff.2 hq0
    nlinarith [hgap q hq hq0]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, ← hbq, hq0,
    add_zero]
  exact hb

/-- **A cochain projection is an isomorphism on cohomology** `Hⁱ(H) ≃ Hⁱ(Vₕ)` under closed range
and the strict gap `‖q - π q‖ < ‖q‖` on `ℌⁱ \ 0`. [AFW2010], Thm 3.4 -/
def cohomologyEquiv {i : ι} (hi : H.ClosedRangeAt i)
    (hgap : ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - P.π i q‖ < ‖q‖) :
    H.cohomology i ≃ₗ[𝕜] S.toHilbertComplex.cohomology i :=
  LinearEquiv.ofBijective _ ⟨P.cohomologyMap_injective hi hgap, P.cohomologyMap_surjective i⟩

@[simp] theorem cohomologyEquiv_apply {i : ι} (hi : H.ClosedRangeAt i)
    (hgap : ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - P.π i q‖ < ‖q‖) (x : H.cohomology i) :
    P.cohomologyEquiv hi hgap x = P.cohomologyMap i x := rfl

/-- **`dim Hⁱ(Vₕ) = dim Hⁱ(H)`**. [AFW2010], Thm 3.4 -/
theorem finrank_cohomology_eq {i : ι} (hi : H.ClosedRangeAt i)
    (hgap : ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - P.π i q‖ < ‖q‖) :
    Module.finrank 𝕜 (S.toHilbertComplex.cohomology i) = Module.finrank 𝕜 (H.cohomology i) :=
  (P.cohomologyEquiv hi hgap).finrank_eq.symm

/-- **`dim ℌₕⁱ = dim ℌⁱ`**: the discrete harmonic forms have the dimension of the harmonic
forms. [AFW2010], Thm 3.4, Thm 3.5 -/
theorem finrank_harmonicW_eq {i : ι} (hi : H.ClosedRangeAt i)
    (hgap : ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - P.π i q‖ < ‖q‖) :
    Module.finrank 𝕜 (S.harmonicW i) = Module.finrank 𝕜 (H.harmonic i) := by
  rw [← S.map_harmonic, ← (Submodule.equivMapOfInjective _ (S.V i).injective_subtype _).finrank_eq,
    ← (S.cohomologyEquivHarmonic i).finrank_eq, P.finrank_cohomology_eq hi hgap,
    (H.cohomologyEquivHarmonic hi).finrank_eq]

/-- A cochain projection onto a finite-dimensional subcomplex with the strict gap forces `ℌⁱ` to be
finite-dimensional. -/
theorem finiteDimensional_harmonic {i : ι} (hi : H.ClosedRangeAt i)
    (hgap : ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - P.π i q‖ < ‖q‖) :
    FiniteDimensional 𝕜 (H.harmonic i) :=
  have := (P.cohomologyEquiv hi hgap).symm.finiteDimensional
  (H.cohomologyEquivHarmonic hi).finiteDimensional

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- A harmonic gap below `1` is the strict gap. -/
theorem norm_sub_π_lt_of_harmonicGap_lt_one {i : ι} {μ : ℝ}
    (hμ : ∀ q ∈ H.harmonic i, ‖q - P.π i q‖ ≤ μ * ‖q‖) (h : P.harmonicGap i < 1) {q : W i}
    (hq : q ∈ H.harmonic i) (hq0 : q ≠ 0) : ‖q - P.π i q‖ < ‖q‖ :=
  (P.norm_sub_le_harmonicGap_mul hμ hq).trans_lt (mul_lt_of_lt_one_left (norm_pos_iff.2 hq0) h)

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- A cochain projection bounded by `C` in `W` moves harmonic forms by at most `(1 + C) ‖q‖`. -/
theorem norm_sub_π_le_of_norm_le {i : ι} {C : ℝ} (hπ : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖) (q : W i) :
    ‖q - P.π i q‖ ≤ (1 + C) * ‖q‖ :=
  (norm_sub_le _ _).trans (by linarith [hπ q])

end Single

/-! ### Families of subcomplexes with vanishing harmonic gap -/

section Family

variable {κ : Type*} {l : Filter κ} {S : κ → H.Subcomplex} [∀ h i, FiniteDimensional 𝕜 ((S h).V i)]
  (P : ∀ h, (S h).CochainProjection) {i : ι} {C : ℝ} (hπ : ∀ h x, ‖(P h).π i x‖ ≤ C * ‖x‖)
  (hgap : Tendsto (fun h => (P h).harmonicGap i) l (𝓝 0))
include hπ hgap

omit [∀ h i, FiniteDimensional 𝕜 ((S h).V i)] in
/-- Eventually along `l`, the strict gap holds. -/
theorem eventually_norm_sub_π_lt :
    ∀ᶠ h in l, ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - (P h).π i q‖ < ‖q‖ :=
  (hgap.eventually (gt_mem_nhds one_pos)).mono fun h h1 _ hq hq0 =>
    (P h).norm_sub_π_lt_of_harmonicGap_lt_one (fun q _ => (P h).norm_sub_π_le_of_norm_le (hπ h) q)
      h1 hq hq0

/-- **The discrete cohomology is eventually the cohomology**: for `W`-bounded cochain projections
whose harmonic gap tends to zero along `l` (`tendsto_harmonicGap`), and `H` with closed range at
`i`, `dim Hⁱ(Vₕ) = dim Hⁱ(H)` eventually. [AFW2010], Thm 3.4 and the remark after it -/
theorem eventually_finrank_cohomology_eq (hi : H.ClosedRangeAt i) :
    ∀ᶠ h in l, Module.finrank 𝕜 ((S h).toHilbertComplex.cohomology i) =
      Module.finrank 𝕜 (H.cohomology i) :=
  (eventually_norm_sub_π_lt P hπ hgap).mono fun h hh => (P h).finrank_cohomology_eq hi hh

/-- **`dim ℌₕⁱ = dim ℌⁱ` eventually.** [AFW2010], Thm 3.4, Thm 3.5 -/
theorem eventually_finrank_harmonicW_eq (hi : H.ClosedRangeAt i) :
    ∀ᶠ h in l, Module.finrank 𝕜 ((S h).harmonicW i) = Module.finrank 𝕜 (H.harmonic i) :=
  (eventually_norm_sub_π_lt P hπ hgap).mono fun h hh => (P h).finrank_harmonicW_eq hi hh

end Family

end CochainProjection

end Subcomplex

end Feec.HilbertComplex
