module

public import Feec.HilbertComplex.DomainComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The cohomology of a Hilbert complex is the homology of its complex of domains

A Hilbert complex restricts to a complex of `𝕜`-modules on the domains `D(d i (c.next i))`, whose
homology is the cohomology `𝔷ⁱ / 𝔅ⁱ` of the Hilbert complex.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

/-! ### The complex of domains -/

/-- `d i j` restricted to the domain `D(d i (c.next i))`, with values in `D(d j (c.next j))`. -/
def domainMap (i j : ι) : (H.d i (c.next i)).domain →ₗ[𝕜] (H.d j (c.next j)).domain :=
  LinearMap.codRestrict _ ((H.d i j).toFun ∘ₗ Submodule.inclusion (H.domain_next_le i j))
    fun _ => H.mapsTo i j _ _

@[simp] theorem coe_domainMap (i j : ι) (x : (H.d i (c.next i)).domain) :
    (H.domainMap i j x : W j) = H.d i j ⟨x, H.domain_next_le i j x.2⟩ := rfl

/-- **The complex of domains** `D(d i (c.next i))`, with the differentials `d i j`, as modules. -/
def toModuleCat : HomologicalComplex (ModuleCat 𝕜) c where
  X i := ModuleCat.of 𝕜 (H.d i (c.next i)).domain
  d i j := ModuleCat.ofHom (H.domainMap i j)
  shape _ _ h := ModuleCat.hom_ext (LinearMap.ext fun _ =>
    Subtype.ext (H.apply_eq_zero_of_not_rel h _))
  d_comp_d' i j k _ _ := ModuleCat.hom_ext (LinearMap.ext fun x =>
    Subtype.ext (H.d_comp_d i j k ⟨x, H.domain_next_le i j x.2⟩))

theorem toModuleCat_d_hom (i j : ι) : (H.toModuleCat.d i j).hom = H.domainMap i j := rfl

/-- The vector of `Wⁱ` underlying an element of the `i`-th module of `toModuleCat`. -/
abbrev toModuleCatVal {i : ι} (x : H.toModuleCat.X i) : W i :=
  Subtype.val (p := fun w => w ∈ (H.d i (c.next i)).domain) x

/-! ### Cycles and boundaries -/

theorem mem_cycles_iff {i : ι} {w : W i} :
    w ∈ H.cycles i ↔ ∃ h : w ∈ (H.d i (c.next i)).domain, H.d i (c.next i) ⟨w, h⟩ = 0 := by
  rw [cycles, LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨y, rfl, hy⟩; exact ⟨y.2, hy⟩
  · rintro ⟨h, hw⟩; exact ⟨⟨w, h⟩, rfl, hw⟩

/-- The cycles are the kernel of `d i (c.next i)` on its domain. -/
def cyclesEquiv (i : ι) : H.cycles i ≃ₗ[𝕜] LinearMap.ker (H.toModuleCat.sc i).g.hom where
  toFun z := ⟨⟨z, (H.mem_cycles_iff.1 z.2).1⟩, Subtype.ext (H.mem_cycles_iff.1 z.2).2⟩
  invFun x := ⟨H.toModuleCatVal x.1,
    H.mem_cycles_iff.2 ⟨(x.1 : (H.d i (c.next i)).domain).2, congrArg Subtype.val x.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem coe_cyclesEquiv (i : ι) (z : H.cycles i) :
    H.toModuleCatVal (H.cyclesEquiv i z).1 = z := rfl

theorem mem_boundaries_iff {i : ι} {w : W i} :
    w ∈ H.boundaries i ↔ ∃ x : (H.d (c.prev i) (c.next (c.prev i))).domain,
      H.d (c.prev i) i ⟨x, H.domain_next_le _ i x.2⟩ = w := by
  constructor
  · rintro ⟨y, rfl⟩
    by_cases hr : c.Rel (c.prev i) i
    · have he : c.next (c.prev i) = i := c.next_eq' hr
      exact ⟨⟨y, by rw [he]; exact y.2⟩, rfl⟩
    · refine ⟨0, ?_⟩
      rw [H.apply_eq_zero_of_not_rel hr]
      exact (H.apply_eq_zero_of_not_rel hr y).symm
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩

theorem map_cyclesEquiv_boundaries (i : ι) :
    ((H.boundaries i).comap (H.cycles i).subtype).map (H.cyclesEquiv i : H.cycles i →ₗ[𝕜] _) =
      LinearMap.range (H.toModuleCat.sc i).moduleCatToCycles := by
  refine Submodule.ext fun z => ⟨?_, fun hz => ?_⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx⟩ := H.mem_boundaries_iff.1 hw
    exact ⟨x, Subtype.ext (Subtype.ext hx)⟩
  · obtain ⟨x, hx⟩ := LinearMap.mem_range.1 hz
    refine ⟨(H.cyclesEquiv i).symm z, H.mem_boundaries_iff.2 ⟨x, ?_⟩,
      (H.cyclesEquiv i).apply_symm_apply z⟩
    exact congrArg (fun y : LinearMap.ker (H.toModuleCat.sc i).g.hom => H.toModuleCatVal y.1) hx

/-- **The cohomology of a Hilbert complex is the homology of its complex of domains.** -/
def cohomologyEquivHomology (i : ι) : H.cohomology i ≃ₗ[𝕜] H.toModuleCat.homology i :=
  (Submodule.Quotient.equiv _ _ (H.cyclesEquiv i) (H.map_cyclesEquiv_boundaries i)).trans
    (H.toModuleCat.sc i).moduleCatHomologyIso.symm.toLinearEquiv

/-- Linear equivalences commuting with the differentials give `H.toModuleCat ≅ K`. -/
def toModuleCatIso {W : ι → Type u} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] (H : HilbertComplex 𝕜 c W)
    (K : HomologicalComplex (ModuleCat.{u} 𝕜) c) (e : ∀ i, (H.d i (c.next i)).domain ≃ₗ[𝕜] K.X i)
    (he : ∀ i j x, e j (H.domainMap i j x) = (K.d i j).hom (e i x)) : H.toModuleCat ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (e i).toModuleIso) fun i j _ =>
    ModuleCat.hom_ext (LinearMap.ext fun x => (he i j x).symm)

/-- `H.cohomology i ≃ K.homology i` for every complex `K` isomorphic to `H.toModuleCat`. -/
def cohomologyEquivOfIso {W : ι → Type u} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] {H : HilbertComplex 𝕜 c W}
    {K : HomologicalComplex (ModuleCat.{u} 𝕜) c} (e : H.toModuleCat ≅ K) (i : ι) :
    H.cohomology i ≃ₗ[𝕜] K.homology i :=
  (H.cohomologyEquivHomology i).trans
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} 𝕜) c i).mapIso e).toLinearEquiv

/-! ### The domain complex -/

section DomainComplex

variable {W : ι → Type u} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)] (H : HilbertComplex 𝕜 c W)

/-- The graph space of `d i (c.next i)` is its domain: `v ↦ ι v`. -/
def domainSpaceEquiv (i : ι) : H.domainSpace i ≃ₗ[𝕜] (H.d i (c.next i)).domain :=
  LinearEquiv.ofBijective (H.domainCoord i (c.next i))
    ⟨fun _ _ h => H.domainIncl_injective i (congrArg Subtype.val h),
      fun x => ⟨(H.d i (c.next i)).toGraphSpace x, rfl⟩⟩

/-- **The domain complex has the cohomology of the complex**: `Hⁱ(V) ≃ Hⁱ(W)`. -/
def domainComplexCohomologyEquiv (i : ι) :
    H.domainComplex.cohomology i ≃ₗ[𝕜] H.cohomology i :=
  (cohomologyEquivOfIso (toModuleCatIso H.domainComplex H.toModuleCat
      (fun i => (LinearEquiv.ofTop _ rfl).trans (H.domainSpaceEquiv i))
      fun _ _ _ => rfl) i).trans (H.cohomologyEquivHomology i).symm

end DomainComplex

end Feec.HilbertComplex
