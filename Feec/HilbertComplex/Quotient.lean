module

public import Feec.HilbertComplex.Homology

/-!
# Subquotients of a complex of bounded operators

A **subquotient** (`Feec.HilbertComplex.Subquotient`) of a complex of bounded operators
`d i j : Wⁱ → Wʲ` on Hilbert spaces is a pair of subcomplexes `Δ ≤ Γ` (`d Γⁱ ⊆ Γʲ`, `d Δⁱ ⊆ Δʲ`)
with `Γ` closed. Its quotient `Γ / Δ`, with the quotient norm and the differentials
`[x] ↦ [d x]` (`Subquotient.quotD`), is realized as the Hilbert complex
(`Subquotient.complex`) of the orthogonal complements `Γⁱ ⊖ Δⁱ = Γⁱ ∩ (Δⁱ)ᗮ`
(`Subquotient.space`) with the compressed differentials `y ↦ P_{(Δʲ)ᗮ} (d y)`
(`Subquotient.spaceD`); it exists for every `Δ`, and `d d = 0` holds on it since compressions of
maps keeping `Δ` compose (`Subquotient.coe_compress_compress`). The quotient norm of `Γⁱ / Δⁱ` is
the norm of `Γⁱ ⊖ Δⁱ`: `y ↦ [y]` is an isometry (`Subquotient.toQuot`); when `Δ` is closed it is
onto (`Subquotient.toQuotEquiv`), so the quotient norm is a Hilbert norm, and it carries the
compressed differentials to those of the quotient (`Subquotient.quotD_toQuot`): `Γ / Δ` with the
quotient norm is, as a complex, the Hilbert complex `Subquotient.complex`, with the same cohomology
(`Subquotient.cohomologyEquiv`).

The same compression `y ↦ P_{(Δʲ)ᗮ} (f y)` (`Subquotient.compress`) carries a bounded map keeping
`Γ` and `Δ` and commuting with `d`, e.g. a cochain projection, to one commuting with the
compressed differentials (`Subquotient.spaceD_compress`). For the output complex of the
BGG construction (`Feec.BGG.BoundedData.derivedComplex`) this is the Hilbert-space structure of
[ArnoldHu2021], Theorem 6, whose argument is the one given here for every subquotient.

## Main definitions

* `Feec.HilbertComplex.Subquotient 𝕜 c W`: bounded differentials and subcomplexes `Δ ≤ Γ`,
  `Γ` closed.
* `Subquotient.space`, `Subquotient.spaceD`, `Subquotient.complex`: `Γ ⊖ Δ` as a Hilbert complex;
  `Subquotient.compress`: the compression `y ↦ P_{(Δʲ)ᗮ} (f y)` of a bounded map keeping `Γ`.
* `Subquotient.QuotSpace i = Γⁱ / Δⁱ` with the quotient norm, `Subquotient.quotD`: its bounded
  differentials; `Subquotient.quotModuleCat`: `Γ / Δ` as a complex of modules.
* `Subquotient.toQuot : Γⁱ ⊖ Δⁱ →ₗᵢ Γⁱ / Δⁱ`, `y ↦ [y]`.

## Main results

* `Subquotient.coe_compress_compress`, `Subquotient.spaceD_compress`: compressions of maps keeping
  `Δ` compose; those of maps commuting with `d` commute with the compressed differentials.
* `Subquotient.norm_toQuot`: **the quotient norm is the norm of `Γ ⊖ Δ`**, `‖[y]‖ = ‖y‖`.
* `Subquotient.toQuotEquiv`, `Subquotient.quotD_toQuot`: for closed `Δ`, `Γ ⊖ Δ ≃ Γ / Δ`
  isometrically, intertwining the differentials.
* `Subquotient.complexIso`, `Subquotient.cohomologyEquiv`: for closed `Δ`, the Hilbert complex is
  the quotient complex, with the same cohomology.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3, Theorem 6 (the output
  complex of bounded Hilbert complexes is a Hilbert complex with the quotient norm)
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992] (Hilbert complexes)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Feec.HilbertComplex

/-- **A subquotient of a complex of bounded operators**: bounded differentials
`d i j : Wⁱ → Wʲ`, zero off the relation of `c`, with `d d = 0`, and subcomplexes `Δ ≤ Γ`
(`d Γⁱ ⊆ Γʲ`, `d Δⁱ ⊆ Δʲ`) with `Γ` closed. [ArnoldHu2021], §3 -/
structure Subquotient (𝕜 : Type*) [RCLike 𝕜] {ι : Type*} (c : ComplexShape ι) (W : ι → Type u)
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] where
  /-- the differentials -/
  d : ∀ i j, W i →L[𝕜] W j
  shape : ∀ i j, ¬ c.Rel i j → d i j = 0
  d_comp_d : ∀ i j k x, d j k (d i j x) = 0
  /-- the subcomplex `Γ` -/
  Γ : ∀ i, Submodule 𝕜 (W i)
  /-- the subcomplex `Δ ≤ Γ` quotiented -/
  Δ : ∀ i, Submodule 𝕜 (W i)
  Δ_le_Γ : ∀ i, Δ i ≤ Γ i
  isClosed_Γ : ∀ i, IsClosed (Γ i : Set (W i))
  d_mem_Γ : ∀ i j {x}, x ∈ Γ i → d i j x ∈ Γ j
  d_mem_Δ : ∀ i j {x}, x ∈ Δ i → d i j x ∈ Δ j

namespace Subquotient

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type u}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] (Q : Subquotient 𝕜 c W)

/-- A bounded map keeping `Δ` keeps its closure. -/
theorem map_mem_closure_Δ {i j : ι} {f : W i →L[𝕜] W j} (hf : ∀ {x}, x ∈ Q.Δ i → f x ∈ Q.Δ j)
    {x : W i} (hx : x ∈ (Q.Δ i).topologicalClosure) : f x ∈ (Q.Δ j).topologicalClosure :=
  Submodule.topologicalClosure_minimal (s := Q.Δ i)
    (t := (Q.Δ j).topologicalClosure.comap f.toLinearMap)
    (fun _ hy => (Q.Δ j).le_topologicalClosure (hf hy))
    ((Submodule.isClosed_topologicalClosure _).preimage f.continuous) hx

/-! ### The Hilbert complex `Γ ⊖ Δ` -/

/-- **The space** `Γⁱ ⊖ Δⁱ = Γⁱ ∩ (Δⁱ)ᗮ`, the orthogonal model of `Γⁱ / Δⁱ`. -/
def space (i : ι) : Submodule 𝕜 (W i) := Q.Γ i ⊓ (Q.Δ i)ᗮ

/-! ### The quotient norm of `Γ / Δ` -/

/-- **`Γⁱ / Δⁱ` with the quotient norm** (seminormed; isometric to the Hilbert space `Γⁱ ⊖ Δⁱ`
when `Δ` is closed, `toQuotEquiv`). -/
abbrev QuotSpace (i : ι) : Type _ := Q.Γ i ⧸ (Q.Δ i).comap (Q.Γ i).subtype

/-- **`Γⁱ ⊖ Δⁱ → Γⁱ / Δⁱ`, `y ↦ [y]`, is an isometry** for the quotient norm: `‖y‖ ≤ ‖y - δ‖`
for `y ⊥ Δ ∋ δ`. The argument of [ArnoldHu2021], Theorem 6 -/
def toQuot (i : ι) : Q.space i →ₗᵢ[𝕜] Q.QuotSpace i where
  toLinearMap := ((Q.Δ i).comap (Q.Γ i).subtype).mkQ ∘ₗ
    LinearMap.codRestrict (Q.Γ i) (Q.space i).subtype fun y => y.2.1
  norm_map' y := by
    refine le_antisymm (Submodule.Quotient.norm_mk_le _ (⟨y, y.2.1⟩ : Q.Γ i))
      (le_of_forall_pos_lt_add fun ε hε => ?_)
    obtain ⟨m, hm, hlt⟩ := Submodule.Quotient.norm_mk_lt
      (Submodule.Quotient.mk (p := (Q.Δ i).comap (Q.Γ i).subtype) ⟨y, y.2.1⟩) hε
    have hδ : (y : W i) - m ∈ Q.Δ i :=
      (Submodule.Quotient.eq ((Q.Δ i).comap (Q.Γ i).subtype)).1 hm.symm
    have h0 : inner 𝕜 (y : W i) (m - y) = 0 := by
      rw [← neg_sub, inner_neg_right, Submodule.inner_left_of_mem_orthogonal hδ y.2.2, neg_zero]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
    rw [add_sub_cancel] at h
    have : ‖(y : W i)‖ ≤ ‖(m : W i)‖ := by nlinarith [norm_nonneg (y : W i), norm_nonneg (m : W i)]
    exact this.trans_lt hlt

/-- **The quotient norm of `Γⁱ / Δⁱ` is the norm of `Γⁱ ⊖ Δⁱ`**: `‖[y]‖ = ‖y‖`.
The argument of [ArnoldHu2021], Theorem 6 -/
theorem norm_toQuot {i : ι} (y : Q.space i) : ‖Q.toQuot i y‖ = ‖y‖ := (Q.toQuot i).norm_map y

theorem toQuot_apply (i : ι) (y : Q.space i) :
    Q.toQuot i y = Submodule.Quotient.mk ⟨y, y.2.1⟩ := rfl

/-- The differential `Γⁱ → Γʲ`, a bounded operator. -/
def dΓ (i j : ι) : Q.Γ i →L[𝕜] Q.Γ j :=
  (Q.d i j ∘L (Q.Γ i).subtypeL).codRestrict (Q.Γ j) fun x => Q.d_mem_Γ i j x.2

/-- **The bounded differentials of `Γ / Δ`** for the quotient norm, `[x] ↦ [d x]`. -/
def quotD (i j : ι) : Q.QuotSpace i →L[𝕜] Q.QuotSpace j :=
  ((Q.Δ i).comap (Q.Γ i).subtype).liftQL (((Q.Δ j).comap (Q.Γ j).subtype).mkQL ∘L Q.dΓ i j)
    fun _ hx => (Submodule.Quotient.mk_eq_zero _).2 (Q.d_mem_Δ i j hx)

theorem quotD_mk (i j : ι) (x : Q.Γ i) :
    Q.quotD i j (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Q.dΓ i j x) := rfl

/-- **`Γ / Δ` as a complex of modules**, with the differentials `[x] ↦ [d x]`. -/
def quotModuleCat : HomologicalComplex (ModuleCat.{u} 𝕜) c where
  X i := ModuleCat.of 𝕜 (Q.QuotSpace i)
  d i j := ModuleCat.ofHom (Q.quotD i j : Q.QuotSpace i →ₗ[𝕜] Q.QuotSpace j)
  shape i j h := ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 (by
      change Q.d i j x ∈ Q.Δ j
      rw [Q.shape i j h]; exact (Q.Δ j).zero_mem)))
  d_comp_d' i j k _ _ := ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 (by
      change Q.d j k (Q.d i j x) ∈ Q.Δ k
      rw [Q.d_comp_d]; exact (Q.Δ k).zero_mem)))

variable [∀ i, CompleteSpace (W i)]

instance (i : ι) : CompleteSpace (Q.space i) :=
  ((Q.isClosed_Γ i).inter (Q.Δ i).isClosed_orthogonal).completeSpace_coe

/-- The projection onto `(Δ)ᗮ` keeps `Γ`. -/
theorem starProjection_mem_Γ {i : ι} {x : W i} (hx : x ∈ Q.Γ i) :
    (Q.Δ i)ᗮ.starProjection x ∈ Q.Γ i := by
  have hr : x - (Q.Δ i)ᗮ.starProjection x ∈ Q.Γ i := by
    have := Submodule.sub_starProjection_mem_orthogonal (K := (Q.Δ i)ᗮ) x
    rw [Submodule.orthogonal_orthogonal_eq_closure] at this
    exact Submodule.topologicalClosure_minimal _ (Q.Δ_le_Γ i) (Q.isClosed_Γ i) this
  simpa using sub_mem hx hr

/-- `P_{(Δⁱ)ᗮ}` identifies points that differ by the closure of `Δⁱ`. -/
theorem starProjection_eq_of_sub_mem {i : ι} {u w : W i}
    (h : u - w ∈ (Q.Δ i).topologicalClosure) :
    (Q.Δ i)ᗮ.starProjection u = (Q.Δ i)ᗮ.starProjection w := by
  rw [← sub_eq_zero, ← map_sub, Submodule.starProjection_apply_eq_zero_iff,
    Submodule.orthogonal_orthogonal_eq_closure]
  exact h

theorem sub_starProjection_mem_closure {i : ι} (u : W i) :
    u - (Q.Δ i)ᗮ.starProjection u ∈ (Q.Δ i).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  exact Submodule.sub_starProjection_mem_orthogonal _

/-- For `f` keeping `Δ`, `P_{(Δʲ)ᗮ} (f (P_{(Δⁱ)ᗮ} u)) = P_{(Δʲ)ᗮ} (f u)`. -/
theorem starProjection_map_starProjection {i j : ι} {f : W i →L[𝕜] W j}
    (hf : ∀ {x}, x ∈ Q.Δ i → f x ∈ Q.Δ j) (u : W i) :
    (Q.Δ j)ᗮ.starProjection (f ((Q.Δ i)ᗮ.starProjection u)) = (Q.Δ j)ᗮ.starProjection (f u) := by
  refine Q.starProjection_eq_of_sub_mem ?_
  rw [← map_sub, ← neg_sub, map_neg, neg_mem_iff]
  exact Q.map_mem_closure_Δ hf (Q.sub_starProjection_mem_closure u)

/-- **The compression** `y ↦ P_{(Δʲ)ᗮ} (f y)` to `Γ ⊖ Δ` of a bounded map `f` keeping `Γ`. -/
def compress {i j : ι} (f : W i →L[𝕜] W j) (hf : ∀ {x}, x ∈ Q.Γ i → f x ∈ Q.Γ j) :
    Q.space i →L[𝕜] Q.space j :=
  ((Q.Δ j)ᗮ.starProjection ∘L f ∘L (Q.space i).subtypeL).codRestrict (Q.space j) fun y =>
    ⟨Q.starProjection_mem_Γ (hf y.2.1), Submodule.starProjection_apply_mem _ _⟩

theorem coe_compress {i j : ι} (f : W i →L[𝕜] W j) (hf : ∀ {x}, x ∈ Q.Γ i → f x ∈ Q.Γ j)
    (y : Q.space i) : (Q.compress f hf y : W j) = (Q.Δ j)ᗮ.starProjection (f y) := rfl

/-- **Compressions compose** when the second map keeps `Δ`:
`P_{(Δᵏ)ᗮ} (g (P_{(Δʲ)ᗮ} (f y))) = P_{(Δᵏ)ᗮ} (g (f y))`. -/
theorem coe_compress_compress {i j k : ι} {f : W i →L[𝕜] W j} {g : W j →L[𝕜] W k}
    (hf : ∀ {x}, x ∈ Q.Γ i → f x ∈ Q.Γ j) (hg : ∀ {x}, x ∈ Q.Γ j → g x ∈ Q.Γ k)
    (hgΔ : ∀ {x}, x ∈ Q.Δ j → g x ∈ Q.Δ k) (y : Q.space i) :
    (Q.compress g hg (Q.compress f hf y) : W k) = (Q.Δ k)ᗮ.starProjection (g (f y)) :=
  Q.starProjection_map_starProjection hgΔ (f y)

/-- **The compressed differentials** `y ↦ P_{(Δʲ)ᗮ} (d y)` of `Γ ⊖ Δ`. -/
def spaceD (i j : ι) : Q.space i →L[𝕜] Q.space j := Q.compress (Q.d i j) (Q.d_mem_Γ i j)

theorem coe_spaceD (i j : ι) (y : Q.space i) :
    (Q.spaceD i j y : W j) = (Q.Δ j)ᗮ.starProjection (Q.d i j y) := rfl

theorem spaceD_eq_zero {i j : ι} (h : ¬ c.Rel i j) : Q.spaceD i j = 0 := by
  ext y : 2
  rw [coe_spaceD, Q.shape i j h]
  simp

/-- **Compressions of maps commuting with `d` commute with the compressed differentials.** -/
theorem spaceD_compress {i j : ι} {f : W i →L[𝕜] W i} {g : W j →L[𝕜] W j}
    (hf : ∀ {x}, x ∈ Q.Γ i → f x ∈ Q.Γ i) (hg : ∀ {x}, x ∈ Q.Γ j → g x ∈ Q.Γ j)
    (hgΔ : ∀ {x}, x ∈ Q.Δ j → g x ∈ Q.Δ j) (hfg : ∀ x, Q.d i j (f x) = g (Q.d i j x))
    (y : Q.space i) : Q.spaceD i j (Q.compress f hf y) = Q.compress g hg (Q.spaceD i j y) :=
  Subtype.ext <| (Q.coe_compress_compress hf (Q.d_mem_Γ i j) (Q.d_mem_Δ i j) y).trans <|
    (congrArg _ (hfg y)).trans (Q.coe_compress_compress (Q.d_mem_Γ i j) hg hgΔ y).symm

theorem spaceD_spaceD (i j k : ι) (y : Q.space i) : Q.spaceD j k (Q.spaceD i j y) = 0 := by
  refine Subtype.ext ((Q.coe_compress_compress (Q.d_mem_Γ i j) (Q.d_mem_Γ j k) (Q.d_mem_Δ j k)
    y).trans ?_)
  rw [Q.d_comp_d, map_zero]
  rfl

/-- **`Γ ⊖ Δ` as a Hilbert complex**: the spaces `Γⁱ ∩ (Δⁱ)ᗮ` with the bounded compressed
differentials `y ↦ P_{(Δʲ)ᗮ} (d y)`. The argument of [ArnoldHu2021], Theorem 6 -/
def complex : HilbertComplex 𝕜 c fun i => Q.space i :=
  ofBounded Q.spaceD (fun _ _ h => Q.spaceD_eq_zero h) Q.spaceD_spaceD

/-! ### Closed `Δ`: the quotient is the Hilbert complex `Γ ⊖ Δ` -/

variable {Q} (hΔ : ∀ i, IsClosed (Q.Δ i : Set (W i)))
include hΔ

/-- With `Δ` closed, `x - P_{(Δⁱ)ᗮ} x ∈ Δⁱ`. -/
theorem sub_starProjection_mem_Δ {i : ι} (x : W i) : x - (Q.Δ i)ᗮ.starProjection x ∈ Q.Δ i := by
  have := Q.sub_starProjection_mem_closure x
  rwa [IsClosed.submodule_topologicalClosure_eq (hΔ i)] at this

theorem toQuot_surjective (i : ι) : Function.Surjective (Q.toQuot i) := by
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨⟨(Q.Δ i)ᗮ.starProjection x, Q.starProjection_mem_Γ x.2,
    Submodule.starProjection_apply_mem _ _⟩, ?_⟩
  rw [toQuot_apply, Submodule.Quotient.eq]
  have h := neg_mem (sub_starProjection_mem_Δ hΔ (x : W i))
  rw [neg_sub] at h
  exact h

/-- **`Γⁱ / Δⁱ` with the quotient norm is isometric to the Hilbert space `Γⁱ ⊖ Δⁱ`** when `Δ` is
closed: the quotient norm is a Hilbert norm. The argument of [ArnoldHu2021], Theorem 6 -/
def toQuotEquiv (i : ι) : Q.space i ≃ₗᵢ[𝕜] Q.QuotSpace i :=
  LinearIsometryEquiv.ofSurjective _ (toQuot_surjective hΔ i)

@[simp] theorem toQuotEquiv_apply (i : ι) (y : Q.space i) : toQuotEquiv hΔ i y = Q.toQuot i y :=
  rfl

/-- **The isometry intertwines the differentials**: `[·]` carries the compressed differentials of
`Γ ⊖ Δ` to the bounded differentials of `Γ / Δ`. -/
theorem quotD_toQuot (i j : ι) (y : Q.space i) :
    Q.quotD i j (Q.toQuot i y) = Q.toQuot j (Q.spaceD i j y) := by
  rw [toQuot_apply, quotD_mk, toQuot_apply, Submodule.Quotient.eq]
  exact sub_starProjection_mem_Δ hΔ _

/-- **The Hilbert complex `Γ ⊖ Δ` is the quotient complex `Γ / Δ`** when `Δ` is closed.
The argument of [ArnoldHu2021], Theorem 6 -/
def complexIso : Q.complex.toModuleCat ≅ Q.quotModuleCat :=
  toModuleCatIso Q.complex Q.quotModuleCat
    (fun i => (LinearEquiv.ofTop _ rfl).trans (toQuotEquiv hΔ i).toLinearEquiv)
    fun i j y => (quotD_toQuot hΔ i j y).symm

/-- **The cohomology of `Γ ⊖ Δ` is that of `Γ / Δ`** when `Δ` is closed. -/
def cohomologyEquiv (i : ι) :
    Q.complex.cohomology i ≃ₗ[𝕜] Q.quotModuleCat.homology i :=
  cohomologyEquivOfIso (complexIso hΔ) i

end Subquotient

end Feec.HilbertComplex
