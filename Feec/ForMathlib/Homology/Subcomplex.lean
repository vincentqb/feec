module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Subcomplexes and quotient complexes of complexes of modules

A family of submodules `P i ⊆ Kⁱ` stable under the differentials of a complex `K` of `R`-modules
gives the subcomplex `K.sub P`, the quotient complex `K.quo P` and the short exact sequence
`0 → K.sub P → K → K.quo P → 0`; the inclusion is a quasi-isomorphism when the quotient is
acyclic, and the projection when the subcomplex is ([ArnoldHu2021], §5.2).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.ShortComplex.ShortExact

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}

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

/-- The subcomplex of a family of submodules stable under the differentials. -/
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

/-- The quotient complex by a family of submodules stable under the differentials. -/
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

theorem exactAt_iff_of_modules (L : HomologicalComplex (ModuleCat.{v} R) c) (j : ι) :
    L.ExactAt j ↔ ∀ x : L.X j, L.d j (c.next j) x = 0 → ∃ y : L.X (c.prev j),
      L.d (c.prev j) j y = x := by
  rw [L.exactAt_iff' (c.prev j) j (c.next j) rfl rfl, ShortComplex.moduleCat_exact_iff]
  rfl

theorem quo_acyclic (h : ∀ i (x : K.X i), K.d i (c.next i) x ∈ P (c.next i) →
    ∃ y : K.X (c.prev i), x - K.d (c.prev i) i y ∈ P i) : (K.quo P hP).Acyclic := by
  intro i
  rw [exactAt_iff_of_modules]
  intro x hx
  induction x using Submodule.Quotient.induction_on with | _ x
  obtain ⟨y, hy⟩ := h i x ((Submodule.Quotient.mk_eq_zero _).1 hx)
  exact ⟨Submodule.Quotient.mk y, (Submodule.Quotient.eq _).2 (by
    rw [← neg_mem_iff, neg_sub]; exact hy)⟩

theorem sub_acyclic (h : ∀ i, ∀ x ∈ P i, K.d i (c.next i) x = 0 →
    ∃ y ∈ P (c.prev i), K.d (c.prev i) i y = x) : (K.sub P hP).Acyclic := by
  intro i
  rw [exactAt_iff_of_modules]
  intro (x : P i) hx
  obtain ⟨y, hy, hyx⟩ := h i x x.2 (congrArg Subtype.val hx)
  exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩

theorem quasiIso_subι (h : (K.quo P hP).Acyclic) : QuasiIso (K.subι P hP) :=
  (K.subQuo_shortExact P hP).quasiIso_f h

theorem quasiIso_quoπ (h : (K.sub P hP).Acyclic) : QuasiIso (K.quoπ P hP) :=
  (K.subQuo_shortExact P hP).quasiIso_g h

end HomologicalComplex

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{v} R) c)

theorem homologyπ_eq_zero_iff_moduleCat {i j : ι} (hij : c.prev j = i) (z : K.cycles j) :
    K.homologyπ j z = 0 ↔ ∃ y : K.X i, K.d i j y = K.iCycles j z := by
  have hex := ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk _ _ (K.toCycles_comp_homologyπ i j)) (K.homologyIsCokernel i j hij)
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hi : Function.Injective (K.iCycles j) :=
    (ModuleCat.mono_iff_injective (K.iCycles j)).1 inferInstance
  constructor
  · intro hz
    obtain ⟨y, rfl⟩ := hex z hz
    exact ⟨y, by rw [← ModuleCat.comp_apply, K.toCycles_i]⟩
  · rintro ⟨y, hy⟩
    obtain rfl : K.toCycles i j y = z := hi (by rw [← ModuleCat.comp_apply, K.toCycles_i, hy])
    rw [← ModuleCat.comp_apply, K.toCycles_comp_homologyπ]; rfl

theorem exists_homologyπ_cyclesMk_moduleCat {i j : ι} (hij : c.next i = j) (x : K.homology i) :
    ∃ (y : K.X i) (hy : K.d i j y = 0), K.homologyπ i (K.cyclesMk y j hij hy) = x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ i)).1 inferInstance x
  refine ⟨K.iCycles i z, ?_, ?_⟩
  · rw [← ModuleCat.comp_apply, ← hij, K.iCycles_d]; rfl
  · congr 1
    exact (ModuleCat.mono_iff_injective (K.iCycles i)).1 inferInstance (K.i_cyclesMk _ j hij _)

theorem exists_homology_linearMap {h i k : ι} (hh : c.prev i = h) (hk : c.next i = k)
    [Subsingleton (K.X h)] {F : Type*} [AddCommGroup F] [Module R F] (g : K.X i →ₗ[R] F)
    (hg : ∀ x, K.d i k x = 0 → g x = 0 → x = 0) :
    ∃ f : K.homology i →ₗ[R] F, Function.Injective f ∧
      LinearMap.range f = (LinearMap.ker (K.d i k).hom).map g ∧
      ∀ z : K.cycles i, f (K.homologyπ i z) = g (K.iCycles i z) := by
  have hι : Function.Injective (K.iCycles i) :=
    (ModuleCat.mono_iff_injective (K.iCycles i)).1 inferInstance
  have hπ : Function.Bijective (K.homologyπ i) := by
    refine ⟨fun a b hab => ?_, (ModuleCat.epi_iff_surjective _).1 inferInstance⟩
    obtain ⟨y, hy⟩ := (K.homologyπ_eq_zero_iff_moduleCat hh (a - b)).1 (by
      rw [map_sub, hab, sub_self])
    rw [Subsingleton.elim y 0, map_zero, eq_comm, map_sub, sub_eq_zero] at hy
    exact hι hy
  have hcyc : ∀ z : K.cycles i, K.d i k (K.iCycles i z) = 0 := fun z => by
    subst hk; rw [← ModuleCat.comp_apply, K.iCycles_d]; rfl
  let e := LinearEquiv.ofBijective (K.homologyπ i).hom hπ
  refine ⟨g ∘ₗ (K.iCycles i).hom ∘ₗ e.symm.toLinearMap, ?_, ?_, fun z => ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have h0 := hg _ (hcyc (e.symm a)) ha
    exact e.symm.map_eq_zero_iff.1 (hι (h0.trans (map_zero (K.iCycles i).hom).symm))
  · rw [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
    congr 1
    ext x
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨z, rfl⟩; exact hcyc z
    · subst hk
      exact ⟨K.cyclesMk x _ rfl hx, K.i_cyclesMk x _ rfl hx⟩
  · change g (K.iCycles i (e.symm (e z))) = _
    rw [e.symm_apply_apply]

end HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

open Module

variable {K : Type u} [Field K] {ι : Type*} {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex (ModuleCat.{v} K) c)}

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

theorem finrank_homology₂_eq_iff (hS : S.ShortExact) (i : ι)
    [FiniteDimensional K (S.X₁.homology i)] [FiniteDimensional K (S.X₃.homology i)] :
    finrank K (S.X₂.homology i) = finrank K (S.X₁.homology i) + finrank K (S.X₃.homology i) ↔
      Function.Injective (HomologicalComplex.homologyMap S.f i) ∧
        Function.Surjective (HomologicalComplex.homologyMap S.g i) := by
  have := hS.finiteDimensional_homology₂ i
  have he := (hS.homology_exact₂ i).moduleCat_range_eq_ker
  set f := (HomologicalComplex.homologyMap S.f i).hom
  set g := (HomologicalComplex.homologyMap S.g i).hom
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker g
  rw [← he] at h2
  have h3 : finrank K (LinearMap.range g) ≤ finrank K (S.X₃.homology i) := Submodule.finrank_le _
  change _ ↔ Function.Injective f ∧ Function.Surjective g
  rw [← LinearMap.ker_eq_bot, ← LinearMap.range_eq_top, ← Submodule.finrank_eq_zero]
  constructor
  · intro h
    exact ⟨by omega, Submodule.eq_top_of_finrank_eq (by omega)⟩
  · rintro ⟨hf, hg⟩
    rw [hg, finrank_top] at h2
    omega

end CategoryTheory.ShortComplex.ShortExact

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{v} R) c}

variable (K) in
/-- `H` represents the cohomology of `K` at `i`: `N(dⁱ) = R(dⁱ⁻¹) ⊕ H`. -/
structure Represents (i : ι) (H : Submodule R (K.X i)) : Prop where
  sup_eq : LinearMap.range (K.d (c.prev i) i).hom ⊔ H = LinearMap.ker (K.d i (c.next i)).hom
  disjoint : Disjoint (LinearMap.range (K.d (c.prev i) i).hom) H

theorem represents_ker_of_subsingleton {i : ι} (h : Subsingleton (K.X (c.prev i))) :
    K.Represents i (LinearMap.ker (K.d i (c.next i)).hom) := by
  have hr : LinearMap.range (K.d (c.prev i) i).hom = ⊥ := by
    refine eq_bot_iff.2 ?_
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y 0, map_zero]
    exact Submodule.zero_mem _
  exact ⟨by rw [hr, bot_sup_eq], by rw [hr]; exact disjoint_bot_left⟩

theorem d_f_eq_zero (f : K ⟶ L) {i j : ι} {x : K.X i} (hx : K.d i j x = 0) :
    L.d i j (f.f i x) = 0 := by
  rw [← ModuleCat.comp_apply, f.comm, ModuleCat.comp_apply, hx, map_zero]

theorem homologyMap_homologyπ_cyclesMk (f : K ⟶ L) {i j : ι} (hj : c.next i = j) (x : K.X i)
    (hx : K.d i j x = 0) :
    homologyMap f i (K.homologyπ i (K.cyclesMk x j hj hx)) =
      L.homologyπ i (L.cyclesMk (f.f i x) j hj (d_f_eq_zero f hx)) := by
  rw [← ModuleCat.comp_apply, homologyπ_naturality, ModuleCat.comp_apply]
  congr 1
  refine (ModuleCat.mono_iff_injective (L.iCycles i)).1 inferInstance ?_
  rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply]
  exact (congrArg (f.f i) (K.i_cyclesMk x j hj hx)).trans (L.i_cyclesMk _ j hj _).symm

/-- A quasi-isomorphism carries cohomology representatives to cohomology representatives
([ArnoldHu2021], Corollary 1). -/
theorem Represents.map (f : K ⟶ L) {i : ι} [QuasiIsoAt f i] {H : Submodule R (K.X i)}
    (h : K.Represents i H) : L.Represents i (H.map (f.f i).hom) := by
  have hb : Function.Bijective (homologyMap f i) := by
    have := (quasiIsoAt_iff_isIso_homologyMap f i).1 inferInstance
    exact ConcreteCategory.bijective_of_isIso (homologyMap f i)
  have hH : H ≤ LinearMap.ker (K.d i (c.next i)).hom := h.sup_eq ▸ le_sup_right
  have hf : ∀ b, f.f i (K.d (c.prev i) i b) = L.d (c.prev i) i (f.f (c.prev i) b) := fun b => by
    rw [← ModuleCat.comp_apply, ← f.comm, ModuleCat.comp_apply]
  refine ⟨le_antisymm (sup_le ?_ ?_) fun y hy => ?_, Submodule.disjoint_def.2 ?_⟩
  · rintro _ ⟨y, rfl⟩
    change L.d i (c.next i) (L.d (c.prev i) i y) = 0
    rw [← ModuleCat.comp_apply, L.d_comp_d]; rfl
  · rintro _ ⟨x, hx, rfl⟩
    exact d_f_eq_zero f (hH hx)
  · obtain ⟨a, ha⟩ := hb.2 (L.homologyπ i (L.cyclesMk y _ rfl hy))
    obtain ⟨x, hx, rfl⟩ := K.exists_homologyπ_cyclesMk_moduleCat rfl a
    rw [homologyMap_homologyπ_cyclesMk] at ha
    have h0 : L.homologyπ i (L.cyclesMk y _ rfl hy -
        L.cyclesMk (f.f i x) _ rfl (d_f_eq_zero f hx)) = 0 := by
      rw [map_sub, ha, sub_self]
    obtain ⟨w, hw⟩ := (L.homologyπ_eq_zero_iff_moduleCat rfl _).1 h0
    have hw' : L.d (c.prev i) i w = y - f.f i x := hw.trans (by
      rw [map_sub]
      exact congrArg₂ (· - ·) (L.i_cyclesMk _ _ rfl _) (L.i_cyclesMk _ _ rfl _))
    obtain ⟨_, ⟨b, rfl⟩, k, hk, rfl⟩ := Submodule.mem_sup.1 (h.sup_eq ▸ hx :
      x ∈ LinearMap.range (K.d (c.prev i) i).hom ⊔ H)
    rw [map_add, hf, eq_sub_iff_add_eq, ← add_assoc, ← map_add] at hw'
    rw [← hw']
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨k, hk, rfl⟩
  · rintro _ ⟨w, hw⟩ ⟨k, hk, rfl⟩
    have h0 : homologyMap f i (K.homologyπ i (K.cyclesMk k _ rfl (hH hk))) =
        homologyMap f i 0 :=
      (homologyMap_homologyπ_cyclesMk f rfl k (hH hk)).trans
        (((L.homologyπ_eq_zero_iff_moduleCat rfl _).2
          ⟨w, hw.trans (L.i_cyclesMk _ _ rfl _).symm⟩).trans (map_zero _).symm)
    obtain ⟨b, hb'⟩ := (K.homologyπ_eq_zero_iff_moduleCat rfl _).1 (hb.1 h0)
    rw [Submodule.disjoint_def.1 h.disjoint k ⟨b, hb'.trans (K.i_cyclesMk _ _ rfl _)⟩ hk,
      map_zero]

end HomologicalComplex
