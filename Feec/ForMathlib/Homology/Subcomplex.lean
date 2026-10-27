module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Subcomplexes and quotient complexes of complexes of modules

A family of submodules `P i ⊆ Kⁱ` stable under the differentials of a complex `K` of `R`-modules
gives the subcomplex `K.sub P` and the quotient complex `K.quo P`, and the short exact sequence
`0 → K.sub P → K → K.quo P → 0`. Its long exact sequence in homology shows that **removing an
exact piece does not change the homology**: the inclusion is a quasi-isomorphism when the
quotient is acyclic, the projection when the subcomplex is. This is the homological step of the
BGG construction ([ArnoldHu2021], §5.2: the twisted complex splits off an exact subcomplex).

## Main definitions

* `HomologicalComplex.sub K P hP`, `HomologicalComplex.quo K P hP`: the subcomplex and the
  quotient complex, with `subι : K.sub P hP ⟶ K` and `quoπ : K ⟶ K.quo P hP`.
* `HomologicalComplex.subQuo K P hP`: the short exact sequence `0 → K.sub P → K → K.quo P → 0`.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.quasiIso_f`, `…quasiIso_g`: in a short exact sequence
  of complexes in an abelian category, `f` is a quasi-isomorphism if the third complex is
  acyclic, `g` if the first is.
* `HomologicalComplex.quo_acyclic`, `HomologicalComplex.sub_acyclic`: elementwise criteria.
* `HomologicalComplex.quasiIso_subι`, `HomologicalComplex.quasiIso_quoπ`.
* `CategoryTheory.ShortComplex.ShortExact.finiteDimensional_homology₂`, `…finrank_homology₂_le`:
  over a field, `dim H(X₂) ≤ dim H(X₁) + dim H(X₃)` in a short exact sequence of complexes.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §5.2 (removing an exact
  subcomplex)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.ShortComplex.ShortExact

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}

/-- In a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of complexes with `X₃` acyclic,
`X₁ → X₂` is a quasi-isomorphism. -/
theorem quasiIso_f (hS : S.ShortExact) (h₃ : S.X₃.Acyclic) : _root_.QuasiIso S.f := by
  rw [_root_.quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (HomologicalComplex.homologyMap S.f j) := by
    by_cases hj : ∃ i, c.Rel i j
    · obtain ⟨i, hij⟩ := hj
      exact (hS.homology_exact₁ i j hij).mono_g ((h₃ i).isZero_homology.eq_of_src _ _)
    · have := hS.mono_f
      exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f j (by simpa using hj)
  have hepi : Epi (HomologicalComplex.homologyMap S.f j) :=
    (hS.homology_exact₂ j).epi_f ((h₃ j).isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- In a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of complexes with `X₁` acyclic,
`X₂ → X₃` is a quasi-isomorphism. -/
theorem quasiIso_g (hS : S.ShortExact) (h₁ : S.X₁.Acyclic) : _root_.QuasiIso S.g := by
  rw [_root_.quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hepi : Epi (HomologicalComplex.homologyMap S.g i) := by
    by_cases hi : ∃ j, c.Rel i j
    · obtain ⟨j, hij⟩ := hi
      exact (hS.homology_exact₃ i j hij).epi_f ((h₁ j).isZero_homology.eq_of_tgt _ _)
    · have := hS.epi_g
      exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g i (by simpa using hi)
  have hmono : Mono (HomologicalComplex.homologyMap S.g i) :=
    (hS.homology_exact₂ i).mono_g ((h₁ i).isZero_homology.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

end CategoryTheory.ShortComplex.ShortExact

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{v} R) c) (P : ∀ i, Submodule R (K.X i))
  (hP : ∀ i j, ∀ x ∈ P i, K.d i j x ∈ P j)

/-- **The subcomplex** of a family of submodules stable under the differentials. -/
def sub : HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (P i)
  d i j := ModuleCat.ofHom ((K.d i j).hom.restrict (hP i j))
  shape i j h := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
    change K.d i j x = 0
    rw [K.shape i j h]; rfl))
  d_comp_d' i j k _ _ := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
    change K.d j k (K.d i j x) = 0
    rw [← ModuleCat.comp_apply, K.d_comp_d]; rfl))

theorem sub_d_hom (i j : ι) :
    ((K.sub P hP).d i j).hom = (K.d i j).hom.restrict (hP i j) := rfl

/-- **The quotient complex** by a family of submodules stable under the differentials. -/
def quo : HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (K.X i ⧸ P i)
  d i j := ModuleCat.ofHom ((P i).mapQ (P j) (K.d i j).hom (hP i j))
  shape i j h := ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 (by
      change K.d i j x ∈ P j
      rw [K.shape i j h]; exact (P j).zero_mem)))
  d_comp_d' i j k _ _ := ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 (by
      change K.d j k (K.d i j x) ∈ P k
      rw [← ModuleCat.comp_apply, K.d_comp_d]; exact (P k).zero_mem)))

theorem quo_d_hom (i j : ι) :
    ((K.quo P hP).d i j).hom = (P i).mapQ (P j) (K.d i j).hom (hP i j) := rfl

/-- The inclusion of the subcomplex. -/
def subι : K.sub P hP ⟶ K where
  f i := ModuleCat.ofHom (P i).subtype
  comm' _ _ _ := rfl

/-- The projection onto the quotient complex. -/
def quoπ : K ⟶ K.quo P hP where
  f i := ModuleCat.ofHom (P i).mkQ
  comm' _ _ _ := rfl

/-- The short exact sequence `0 → K.sub P → K → K.quo P → 0`. -/
def subQuo : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c) :=
  ShortComplex.mk (K.subι P hP) (K.quoπ P hP) (by
    ext i x
    exact (Submodule.Quotient.mk_eq_zero _).2 x.2)

theorem subQuo_shortExact : (K.subQuo P hP).ShortExact :=
  shortExact_of_degreewise_shortExact _ fun i =>
    { exact := by
        rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero _).1 hx⟩, rfl⟩
      mono_f := (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
      epi_g := (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _) }

/-- Exactness of a complex of modules at `j`, elementwise. -/
theorem exactAt_iff_of_modules (L : HomologicalComplex (ModuleCat.{v} R) c) (j : ι) :
    L.ExactAt j ↔ ∀ x : L.X j, L.d j (c.next j) x = 0 → ∃ y : L.X (c.prev j),
      L.d (c.prev j) j y = x := by
  rw [L.exactAt_iff' (c.prev j) j (c.next j) rfl rfl, ShortComplex.moduleCat_exact_iff]
  rfl

/-- **The quotient complex is acyclic** when every `x` with `d x ∈ P` is a boundary modulo `P`. -/
theorem quo_acyclic (h : ∀ i (x : K.X i), K.d i (c.next i) x ∈ P (c.next i) →
    ∃ y : K.X (c.prev i), x - K.d (c.prev i) i y ∈ P i) : (K.quo P hP).Acyclic := by
  intro i
  rw [exactAt_iff_of_modules]
  intro x hx
  induction x using Submodule.Quotient.induction_on with | _ x
  obtain ⟨y, hy⟩ := h i x ((Submodule.Quotient.mk_eq_zero _).1 hx)
  exact ⟨Submodule.Quotient.mk y, (Submodule.Quotient.eq _).2 (by
    rw [← neg_mem_iff, neg_sub]; exact hy)⟩

/-- **The subcomplex is acyclic** when every cycle in `P` is the boundary of an element of `P`. -/
theorem sub_acyclic (h : ∀ i, ∀ x ∈ P i, K.d i (c.next i) x = 0 →
    ∃ y ∈ P (c.prev i), K.d (c.prev i) i y = x) : (K.sub P hP).Acyclic := by
  intro i
  rw [exactAt_iff_of_modules]
  intro (x : P i) hx
  obtain ⟨y, hy, hyx⟩ := h i x x.2 (congrArg Subtype.val hx)
  exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩

/-- The inclusion of a subcomplex with acyclic quotient is a quasi-isomorphism. -/
theorem quasiIso_subι (h : (K.quo P hP).Acyclic) : QuasiIso (K.subι P hP) :=
  (K.subQuo_shortExact P hP).quasiIso_f h

/-- The projection onto the quotient by an acyclic subcomplex is a quasi-isomorphism. -/
theorem quasiIso_quoπ (h : (K.sub P hP).Acyclic) : QuasiIso (K.quoπ P hP) :=
  (K.subQuo_shortExact P hP).quasiIso_g h

end HomologicalComplex

/-! ### Finite-dimensional homology in a short exact sequence -/

namespace CategoryTheory.ShortComplex.ShortExact

open Module

variable {K : Type u} [Field K] {ι : Type*} {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex (ModuleCat.{v} K) c)}

/-- In a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of complexes of vector spaces, the homology
of `X₂` at `i` is finite-dimensional when those of `X₁` and `X₃` are: `H(X₁) → H(X₂) → H(X₃)`
is exact. -/
theorem finiteDimensional_homology₂ (hS : S.ShortExact) (i : ι)
    [FiniteDimensional K (S.X₁.homology i)] [FiniteDimensional K (S.X₃.homology i)] :
    FiniteDimensional K (S.X₂.homology i) := by
  have he := (hS.homology_exact₂ i).moduleCat_range_eq_ker
  set g := (HomologicalComplex.homologyMap S.g i).hom
  have : FiniteDimensional K (LinearMap.ker g) := by
    rw [← he]; exact LinearMap.finiteDimensional_range _
  have : FiniteDimensional K (S.X₂.homology i ⧸ LinearMap.ker g) :=
    g.quotKerEquivRange.symm.finiteDimensional
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

/-- `dim H(X₂) ≤ dim H(X₁) + dim H(X₃)` in a short exact sequence of complexes of vector spaces. -/
theorem finrank_homology₂_le (hS : S.ShortExact) (i : ι)
    [FiniteDimensional K (S.X₁.homology i)] [FiniteDimensional K (S.X₃.homology i)] :
    finrank K (S.X₂.homology i) ≤ finrank K (S.X₁.homology i) + finrank K (S.X₃.homology i) := by
  have := hS.finiteDimensional_homology₂ i
  have he := (hS.homology_exact₂ i).moduleCat_range_eq_ker
  set g := (HomologicalComplex.homologyMap S.g i).hom
  have h1 : finrank K (LinearMap.ker g) ≤ finrank K (S.X₁.homology i) := by
    rw [← he]; exact LinearMap.finrank_range_le _
  have h3 : finrank K (LinearMap.range g) ≤ finrank K (S.X₃.homology i) := Submodule.finrank_le _
  have := LinearMap.finrank_range_add_finrank_ker g
  omega

end CategoryTheory.ShortComplex.ShortExact
