module

public import Feec.HilbertComplex.BGG.Derived
public import Feec.HilbertComplex.Quotient
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The analytic BGG construction: the derived complex is a closed Hilbert complex

For BGG data on Hilbert spaces with bounded differentials and connecting maps, the derived complex
is the Hilbert complex of `Υⁱ = Γⁱ ⊖ Δⁱ`; for closed `Δ F` and under the elimination hypotheses
it has the cohomology of the twisted complex and closed range wherever the rows have
finite-dimensional cohomology ([ArnoldHu2021], Theorem 6; [CapHu2024]).

## Main results

* `BoundedData.derivedQuotLEquiv`: for closed `Δ F`, `Υⁱ` is isometric to `Γⁱ / Δⁱ`.
* `BoundedData.derivedComplex_closedRangeAt`: closed range where `dim Hⁱ(V) + dim Hⁱ(Ṽ) < ∞`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3, §5
* [A. Čap, K. Hu, *BGG sequences with weak regularity and applications*][CapHu2024]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Feec.BGG

/-- BGG data on inner product spaces with bounded `d`, `d̃` and `S`. [ArnoldHu2021], §3, (19) -/
structure BoundedData (𝕜 : Type*) [RCLike 𝕜] {ι : Type*} (c : ComplexShape ι) (V Vt : ι → Type u)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
    [∀ i, NormedAddCommGroup (Vt i)] [∀ i, InnerProductSpace 𝕜 (Vt i)]
    extends Data 𝕜 c V Vt where
  continuous_d : ∀ i j, Continuous (d i j)
  continuous_dt : ∀ i j, Continuous (dt i j)
  continuous_S : ∀ i j, Continuous (S i j)

namespace BoundedData

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {V Vt : ι → Type u}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, NormedAddCommGroup (Vt i)] [∀ i, InnerProductSpace 𝕜 (Vt i)]
  (D : BoundedData 𝕜 c V Vt)

/-! ### The rows -/

section Rows

variable [∀ i, CompleteSpace (V i)] [∀ i, CompleteSpace (Vt i)]

/-- The top row `(V, d)` as a Hilbert complex of bounded operators. -/
def rowTopComplex : HilbertComplex 𝕜 c V :=
  HilbertComplex.ofBounded (fun i j => ⟨D.d i j, D.continuous_d i j⟩)
    (fun i j h => ContinuousLinearMap.coe_injective (D.shape_d i j h)) D.d_comp_d

/-- The bottom row `(Ṽ, d̃)` as a Hilbert complex of bounded operators. -/
def rowBotComplex : HilbertComplex 𝕜 c Vt :=
  HilbertComplex.ofBounded (fun i j => ⟨D.dt i j, D.continuous_dt i j⟩)
    (fun i j h => ContinuousLinearMap.coe_injective (D.shape_dt i j h)) D.dt_comp_dt

/-- The cohomology of the top row is the homology of `Data.rowTop`. -/
def rowTopCohomologyEquiv (i : ι) : D.rowTopComplex.cohomology i ≃ₗ[𝕜] D.rowTop.homology i :=
  HilbertComplex.cohomologyEquivOfIso
    (HilbertComplex.toModuleCatIso D.rowTopComplex D.rowTop (fun _ => LinearEquiv.ofTop _ rfl)
      fun _ _ _ => rfl) i

/-- The cohomology of the bottom row is the homology of `Data.rowBot`. -/
def rowBotCohomologyEquiv (i : ι) : D.rowBotComplex.cohomology i ≃ₗ[𝕜] D.rowBot.homology i :=
  HilbertComplex.cohomologyEquivOfIso
    (HilbertComplex.toModuleCatIso D.rowBotComplex D.rowBot (fun _ => LinearEquiv.ofTop _ rfl)
      fun _ _ _ => rfl) i

end Rows

/-! ### The twisted differential on `Vⁱ ⊕ Ṽⁱ` -/

theorem continuous_twist (i j : ι) : Continuous (D.twist i j) := by
  change Continuous fun x : V i × Vt i => (D.d i j x.1 - D.S i j x.2, D.dt i j x.2)
  exact (((D.continuous_d i j).comp continuous_fst).sub
    ((D.continuous_S i j).comp continuous_snd)).prodMk ((D.continuous_dt i j).comp continuous_snd)

/-- The twisted differential `(σ, φ) ↦ (dσ - Sφ, d̃φ)` on the `ℓ²` product `Vⁱ ⊕ Ṽⁱ`. -/
def twistL (i j : ι) : WithLp 2 (V i × Vt i) →L[𝕜] WithLp 2 (V j × Vt j) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 (V j) (Vt j)).symm.toContinuousLinearMap ∘L
    ⟨D.twist i j, D.continuous_twist i j⟩ ∘L
      (WithLp.prodContinuousLinearEquiv 2 𝕜 (V i) (Vt i)).toContinuousLinearMap

@[simp] theorem ofLp_twistL (i j : ι) (x : WithLp 2 (V i × Vt i)) :
    (D.twistL i j x).ofLp = D.twist i j x.ofLp := rfl

theorem twistL_twistL (i j k : ι) (x : WithLp 2 (V i × Vt i)) :
    D.twistL j k (D.twistL i j x) = 0 :=
  WithLp.ofLp_injective 2 (D.twist_twist i j k _)

theorem twistL_eq_zero {i j : ι} (h : ¬ c.Rel i j) : D.twistL i j = 0 := by
  ext x : 1
  exact WithLp.ofLp_injective 2 (by rw [ofLp_twistL, D.twist_eq_zero h]; rfl)

/-! ### The eliminations as subspaces of `Vⁱ ⊕ Ṽⁱ` -/

variable (E F : ι → Prop)

/-- The elimination `Γ E` in `Vⁱ ⊕ Ṽⁱ`. -/
def ΓL (i : ι) : Submodule 𝕜 (WithLp 2 (V i × Vt i)) :=
  (D.Γ E i).comap (WithLp.linearEquiv 2 𝕜 (V i × Vt i)).toLinearMap

/-- The exact part `Δ F ∩ Γ E` in `Vⁱ ⊕ Ṽⁱ`. -/
def ΔL (i : ι) : Submodule 𝕜 (WithLp 2 (V i × Vt i)) :=
  (D.Δ F i ⊓ D.Γ E i).comap (WithLp.linearEquiv 2 𝕜 (V i × Vt i)).toLinearMap

theorem mem_ΓL {i : ι} {x : WithLp 2 (V i × Vt i)} : x ∈ D.ΓL E i ↔ x.ofLp ∈ D.Γ E i := Iff.rfl

theorem mem_ΔL {i : ι} {x : WithLp 2 (V i × Vt i)} :
    x ∈ D.ΔL E F i ↔ x.ofLp ∈ D.Δ F i ∧ x.ofLp ∈ D.Γ E i := Iff.rfl

theorem ΔL_le_ΓL (i : ι) : D.ΔL E F i ≤ D.ΓL E i := fun _ hx => hx.2

theorem isClosed_Γ (i : ι) : IsClosed (D.Γ E i : Set (V i × Vt i)) := by
  rw [Data.Γ, Submodule.coe_inf, Submodule.coe_iInf, Submodule.coe_iInf]
  exact (isClosed_iInter fun _ => isClosed_eq continuous_fst continuous_const).inter
    (isClosed_iInter fun _ => isClosed_eq (continuous_fst.comp (D.continuous_twist _ _))
      continuous_const)

theorem isClosed_ΓL (i : ι) : IsClosed (D.ΓL E i : Set (WithLp 2 (V i × Vt i))) :=
  (D.isClosed_Γ E i).preimage (WithLp.prodContinuousLinearEquiv 2 𝕜 (V i) (Vt i)).continuous

theorem twistL_mem_ΓL (i j : ι) {x : WithLp 2 (V i × Vt i)} (hx : x ∈ D.ΓL E i) :
    D.twistL i j x ∈ D.ΓL E j :=
  D.twist_mem_Γ E i j hx

theorem twistL_mem_ΔL (i j : ι) {x : WithLp 2 (V i × Vt i)} (hx : x ∈ D.ΔL E F i) :
    D.twistL i j x ∈ D.ΔL E F j :=
  ⟨D.twist_mem_Δ F i j hx.1, D.twist_mem_Γ E i j hx.2⟩

/-- The subquotient `Γ E / (Δ F ∩ Γ E)` of the twisted complex on `Vⁱ ⊕ Ṽⁱ`. -/
def subquotient : HilbertComplex.Subquotient 𝕜 c fun i => WithLp 2 (V i × Vt i) where
  d := D.twistL
  shape _ _ h := D.twistL_eq_zero h
  d_comp_d := D.twistL_twistL
  Γ := D.ΓL E
  Δ := D.ΔL E F
  Δ_le_Γ := D.ΔL_le_ΓL E F
  isClosed_Γ := D.isClosed_ΓL E
  d_mem_Γ := D.twistL_mem_ΓL E
  d_mem_Δ := D.twistL_mem_ΔL E F

/-! ### The derived complex as a Hilbert complex -/

variable [∀ i, CompleteSpace (V i)] [∀ i, CompleteSpace (Vt i)]

/-- The derived space `Υⁱ = Γⁱ ⊖ (Δⁱ ∩ Γⁱ)`, the orthogonal model of `Γⁱ / Δⁱ`. -/
def derivedSpace (i : ι) : Submodule 𝕜 (WithLp 2 (V i × Vt i)) := (D.subquotient E F).space i

/-- The norm of `Υⁱ`. -/
instance (i : ι) : NormedAddCommGroup (D.derivedSpace E F i) := Submodule.normedAddCommGroup _

/-- The inner product of `Υⁱ`. -/
instance (i : ι) : InnerProductSpace 𝕜 (D.derivedSpace E F i) := Submodule.innerProductSpace _

instance (i : ι) : CompleteSpace (D.derivedSpace E F i) :=
  ((D.isClosed_ΓL E i).inter (D.ΔL E F i).isClosed_orthogonal).completeSpace_coe

theorem starProjection_mem_ΓL {i : ι} {t : WithLp 2 (V i × Vt i)} (ht : t ∈ D.ΓL E i) :
    (D.ΔL E F i)ᗮ.starProjection t ∈ D.ΓL E i :=
  (D.subquotient E F).starProjection_mem_Γ ht

/-- The differentials of the derived complex, `y ↦ P_{(Δʲ)ᗮ} (twist y)`. -/
def derivedD (i j : ι) : D.derivedSpace E F i →L[𝕜] D.derivedSpace E F j :=
  (D.subquotient E F).spaceD i j

theorem coe_derivedD (i j : ι) (y : D.derivedSpace E F i) :
    (D.derivedD E F i j y : WithLp 2 (V j × Vt j)) =
      (D.ΔL E F j)ᗮ.starProjection (D.twistL i j y) := rfl

/-- The derived complex as the Hilbert complex of the spaces `Υⁱ`. [ArnoldHu2021], Theorem 6 -/
def derivedComplex : HilbertComplex 𝕜 c (fun i => D.derivedSpace E F i) :=
  (D.subquotient E F).complex

/-! ### The quotient norm of `Γⁱ / Δⁱ` -/

/-- `Γⁱ / Δⁱ` with the quotient norm of the `ℓ²` norm of `Vⁱ ⊕ Ṽⁱ`. -/
abbrev derivedQuotL (i : ι) : Type u := D.ΓL E i ⧸ (D.ΔL E F i).comap (D.ΓL E i).subtype

/-- `Υⁱ → Γⁱ / Δⁱ`, `y ↦ [y]`, an isometry for the quotient norm. -/
def toDerivedQuotL (i : ι) : D.derivedSpace E F i →ₗᵢ[𝕜] D.derivedQuotL E F i :=
  (D.subquotient E F).toQuot i

/-- The bounded differentials of `Γ / Δ` for the quotient norm, `[x] ↦ [twist x]`. -/
def derivedQuotD (i j : ι) : D.derivedQuotL E F i →L[𝕜] D.derivedQuotL E F j :=
  (D.subquotient E F).quotD i j

omit [∀ i, CompleteSpace (V i)] [∀ i, CompleteSpace (Vt i)] in
/-- `Γⁱ / Δⁱ` in `Vⁱ ⊕ Ṽⁱ` is `Γⁱ / Δⁱ` in `Vⁱ × Ṽⁱ`, the space of `derived E F`. -/
def derivedQuotLEquivDerived (i : ι) :
    D.derivedQuotL E F i ≃ₗ[𝕜] D.Γ E i ⧸ (D.Δ F i).comap (D.Γ E i).subtype :=
  Submodule.Quotient.equiv _ _
    { toFun x := ⟨(x : WithLp 2 (V i × Vt i)).ofLp, x.2⟩
      invFun x := ⟨WithLp.toLp 2 (x : V i × Vt i), x.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl } <|
    Submodule.ext fun x => ⟨by rintro ⟨y, hy, rfl⟩; exact hy.1, fun h =>
      ⟨⟨WithLp.toLp 2 (x : V i × Vt i), x.2⟩, ⟨h, x.2⟩, rfl⟩⟩

omit [∀ i, CompleteSpace (V i)] [∀ i, CompleteSpace (Vt i)] in
variable {F} in
theorem isClosed_ΔL (hΔ : ∀ i, IsClosed (D.Δ F i : Set (V i × Vt i))) (i : ι) :
    IsClosed (D.ΔL E F i : Set (WithLp 2 (V i × Vt i))) :=
  ((hΔ i).inter (D.isClosed_Γ E i)).preimage
    (WithLp.prodContinuousLinearEquiv 2 𝕜 (V i) (Vt i)).continuous

variable {F} (hΔ : ∀ i, IsClosed (D.Δ F i : Set (V i × Vt i)))
include hΔ

theorem sub_starProjection_mem_ΔL {i : ι} (t : WithLp 2 (V i × Vt i)) :
    t - (D.ΔL E F i)ᗮ.starProjection t ∈ D.ΔL E F i :=
  HilbertComplex.Subquotient.sub_starProjection_mem_Δ (Q := D.subquotient E F)
    (D.isClosed_ΔL E hΔ) t

theorem toDerivedQuotL_surjective (i : ι) : Function.Surjective (D.toDerivedQuotL E F i) :=
  HilbertComplex.Subquotient.toQuot_surjective (Q := D.subquotient E F) (D.isClosed_ΔL E hΔ) i

/-- When `Δ` is closed, `Γⁱ / Δⁱ` with the quotient norm is isometric to `Υⁱ`. -/
def derivedQuotLEquiv (i : ι) : D.derivedSpace E F i ≃ₗᵢ[𝕜] D.derivedQuotL E F i :=
  HilbertComplex.Subquotient.toQuotEquiv (Q := D.subquotient E F) (D.isClosed_ΔL E hΔ) i

theorem derivedQuotD_toDerivedQuotL (i j : ι) (y : D.derivedSpace E F i) :
    D.derivedQuotD E F i j (D.toDerivedQuotL E F i y) =
      D.toDerivedQuotL E F j (D.derivedD E F i j y) :=
  HilbertComplex.Subquotient.quotD_toQuot (Q := D.subquotient E F) (D.isClosed_ΔL E hΔ) i j y

/-- When `Δ F` is closed, the derived Hilbert complex is the derived complex `Γ E / Δ F`. -/
def derivedComplexIso : (D.derivedComplex E F).toModuleCat ≅ D.derived E F :=
  HilbertComplex.Subquotient.complexIso (Q := D.subquotient E F) (D.isClosed_ΔL E hΔ) ≪≫
    HomologicalComplex.Hom.isoOfComponents (fun i => (D.derivedQuotLEquivDerived E F i).toModuleIso)
      fun _ _ _ => by
        ext x
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rfl

/-- The cohomology of the derived Hilbert complex is the homology of `derived E F`. -/
def derivedComplexCohomologyEquivDerived (i : ι) :
    (D.derivedComplex E F).cohomology i ≃ₗ[𝕜] (D.derived E F).homology i :=
  HilbertComplex.cohomologyEquivOfIso (D.derivedComplexIso E hΔ) i

variable {E} (h : D.Eliminates E F)
include h

/-- The cohomology of the derived Hilbert complex is that of the twisted complex. -/
def derivedComplexCohomologyEquiv (i : ι) :
    (D.derivedComplex E F).cohomology i ≃ₗ[𝕜] D.twistComplex.homology i :=
  (D.derivedComplexCohomologyEquivDerived E hΔ i).trans (D.derivedHomologyIso h i).toLinearEquiv

variable (i : ι) [FiniteDimensional 𝕜 (D.rowTopComplex.cohomology i)]
  [FiniteDimensional 𝕜 (D.rowBotComplex.cohomology i)]
include i

open Module

theorem finiteDimensional_derivedComplex_cohomology :
    FiniteDimensional 𝕜 ((D.derivedComplex E F).cohomology i) :=
  have := (D.rowTopCohomologyEquiv i).finiteDimensional
  have := (D.rowBotCohomologyEquiv i).finiteDimensional
  have := D.finiteDimensional_derived_homology i h
  (D.derivedComplexCohomologyEquivDerived E hΔ i).symm.finiteDimensional

theorem finrank_derivedComplex_cohomology_le :
    finrank 𝕜 ((D.derivedComplex E F).cohomology i) ≤
      finrank 𝕜 (D.rowTopComplex.cohomology i) + finrank 𝕜 (D.rowBotComplex.cohomology i) := by
  have := (D.rowTopCohomologyEquiv i).finiteDimensional
  have := (D.rowBotCohomologyEquiv i).finiteDimensional
  rw [(D.derivedComplexCohomologyEquivDerived E hΔ i).finrank_eq,
    (D.rowTopCohomologyEquiv i).finrank_eq, (D.rowBotCohomologyEquiv i).finrank_eq]
  exact D.finrank_derived_homology_le i h

/-- For closed `Δ F` and under the elimination hypotheses, the derived complex has closed range
wherever the rows have finite-dimensional cohomology. [ArnoldHu2021], Theorem 6; [CapHu2024] -/
theorem derivedComplex_closedRangeAt : (D.derivedComplex E F).ClosedRangeAt i :=
  have := D.finiteDimensional_derivedComplex_cohomology hΔ h i
  HilbertComplex.closedRangeAt_of_finiteDimensional_cohomology _ i

theorem isClosed_Δ_sup_map_twist :
    IsClosed ((D.Δ F i ⊔ (D.Γ E (c.prev i)).map (D.twist (c.prev i) i) : Submodule 𝕜 _) :
      Set (V i × Vt i)) := by
  have hc := D.derivedComplex_closedRangeAt hΔ h i
  set P := (D.ΔL E F i)ᗮ.starProjection
  set toL := (WithLp.prodContinuousLinearEquiv 2 𝕜 (V i) (Vt i)).symm
  set Bd : Set (WithLp 2 (V i × Vt i)) :=
    Subtype.val '' ((D.derivedComplex E F).boundaries i : Set (D.derivedSpace E F i))
  have hP0 : ∀ t ∈ D.ΔL E F i, P t = 0 := fun t ht => by
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal_eq_closure]
    exact Submodule.le_topologicalClosure _ ht
  have hBd : IsClosed Bd :=
    ((D.isClosed_ΓL E i).inter (D.ΔL E F i).isClosed_orthogonal).isClosedMap_subtype_val _ hc
  have key : ((D.Δ F i ⊔ (D.Γ E (c.prev i)).map (D.twist (c.prev i) i) : Submodule 𝕜 _) :
      Set (V i × Vt i)) = (D.Γ E i : Set (V i × Vt i)) ∩ (fun x => P (toL x)) ⁻¹' Bd := by
    ext x
    constructor
    · intro hx
      obtain ⟨δ, hδ, _, ⟨y, hy, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
      refine ⟨add_mem (h.Δ_le_Γ i hδ) (D.twist_mem_Γ E _ i hy), ?_⟩
      set y' : WithLp 2 (V (c.prev i) × Vt (c.prev i)) := WithLp.toLp 2 y
      let u : D.derivedSpace E F (c.prev i) :=
        ⟨(D.ΔL E F (c.prev i))ᗮ.starProjection y', D.starProjection_mem_ΓL E F hy,
          Submodule.starProjection_apply_mem _ _⟩
      refine ⟨D.derivedD E F (c.prev i) i u, ⟨⟨u, trivial⟩, rfl⟩, ?_⟩
      have h1 : P (toL δ) = 0 := hP0 _ ⟨hδ, h.Δ_le_Γ i hδ⟩
      have h2 : P (D.twistL (c.prev i) i (y' - u)) = 0 :=
        hP0 _ (D.twistL_mem_ΔL E F _ i (D.sub_starProjection_mem_ΔL E hΔ y'))
      rw [map_sub, map_sub, sub_eq_zero] at h2
      rw [coe_derivedD, ← h2]
      change _ = P (toL δ + D.twistL (c.prev i) i y')
      rw [map_add, h1, zero_add]
    · rintro ⟨hxΓ, hxB⟩
      obtain ⟨b, hbB, hb⟩ := hxB
      obtain ⟨y, hu⟩ := hbB
      set u : D.derivedSpace E F (c.prev i) := y.1
      have hb : (D.derivedD E F (c.prev i) i u : WithLp 2 (V i × Vt i)) = P (toL x) := by
        exact (congrArg Subtype.val hu).trans hb
      have ht := D.sub_starProjection_mem_ΔL E hΔ (toL x - D.twistL (c.prev i) i u)
      rw [map_sub, ← hb, coe_derivedD, sub_self, sub_zero] at ht
      have hu : (u : WithLp 2 _).ofLp ∈ D.Γ E (c.prev i) := u.2.1
      have hx : x = (x - D.twist (c.prev i) i (u : WithLp 2 _).ofLp) +
          D.twist (c.prev i) i (u : WithLp 2 _).ofLp := (sub_add_cancel _ _).symm
      rw [SetLike.mem_coe, hx]
      exact add_mem (Submodule.mem_sup_left ht.1) (Submodule.mem_sup_right ⟨_, hu, rfl⟩)
  rw [key]
  exact (D.isClosed_Γ E i).inter (hBd.preimage (P.continuous.comp toL.continuous))

theorem derivedComplex_boundaries_eq [Subsingleton (D.rowTopComplex.cohomology i)]
    [Subsingleton (D.rowBotComplex.cohomology i)] :
    (D.derivedComplex E F).boundaries i = (D.derivedComplex E F).cycles i := by
  have := D.finiteDimensional_derivedComplex_cohomology hΔ h i
  have h0 : finrank 𝕜 ((D.derivedComplex E F).cohomology i) = 0 := by
    have := D.finrank_derivedComplex_cohomology_le hΔ h i
    have h1 : finrank 𝕜 (D.rowTopComplex.cohomology i) = 0 := finrank_zero_of_subsingleton
    have h2 : finrank 𝕜 (D.rowBotComplex.cohomology i) = 0 := finrank_zero_of_subsingleton
    omega
  have hs := Module.finrank_zero_iff.1 h0
  refine le_antisymm ((D.derivedComplex E F).boundaries_le_cycles i) fun z hz => ?_
  have := hs.elim (Submodule.Quotient.mk (p := ((D.derivedComplex E F).boundaries i).comap
    ((D.derivedComplex E F).cycles i).subtype) ⟨z, hz⟩) 0
  rwa [Submodule.Quotient.mk_eq_zero] at this

end BoundedData

/-! ### The BGG complex on `ComplexShape.up ℤ` -/

namespace BoundedData

variable {𝕜 : Type*} [RCLike 𝕜] {V Vt : ℤ → Type u} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, NormedAddCommGroup (Vt i)]
  [∀ i, InnerProductSpace 𝕜 (Vt i)] [∀ i, CompleteSpace (Vt i)]
  (D : BoundedData 𝕜 (ComplexShape.up ℤ) V Vt)

/-- The exact part of `bgg J` is closed when the connecting maps `Sⁱ` before `J` are bounded
below. -/
theorem isClosed_bgg_Δ {J : ℤ} (hS : ∀ i < J, ∃ K, AntilipschitzWith K (D.S i (i + 1))) (i : ℤ) :
    IsClosed (D.Δ (· < J) i : Set (V i × Vt i)) := by
  rcases lt_trichotomy i J with hi | rfl | hi
  · obtain ⟨K, hK⟩ := hS (i - 1) (by omega)
    rw [sub_add_cancel] at hK
    have : (D.Δ (· < J) i : Set (V i × Vt i)) = Prod.fst ⁻¹' Set.range (D.S (i - 1) i) := by
      ext x
      rw [SetLike.mem_coe, D.mem_bgg_Δ_of_le hi.le]
      constructor
      · rintro ⟨φ, ψ, -, rfl⟩
        exact ⟨-ψ, map_neg _ _⟩
      · rintro ⟨ψ, hψ⟩
        exact ⟨x.2 + D.dt (i - 1) i ψ, -ψ, Or.inl hi, by simp [hψ]⟩
    rw [this]
    exact (hK.isClosed_range (⟨D.S (i - 1) i, D.continuous_S _ _⟩ :
      Vt (i - 1) →L[𝕜] V i).uniformContinuous).preimage continuous_fst
  · obtain ⟨K, hK⟩ := hS (i - 1) (by omega)
    rw [sub_add_cancel] at hK
    let S : Vt (i - 1) →L[𝕜] V i := ⟨D.S (i - 1) i, D.continuous_S _ _⟩
    let g : Vt (i - 1) →L[𝕜] V i × Vt i := (-S).prod ⟨D.dt (i - 1) i, D.continuous_dt _ _⟩
    have : (D.Δ (· < i) i : Set (V i × Vt i)) = Set.range g := by
      ext x
      rw [SetLike.mem_coe, D.mem_bgg_Δ_of_le le_rfl]
      constructor
      · rintro ⟨φ, ψ, hφ, rfl⟩
        obtain rfl : φ = 0 := hφ.resolve_left (lt_irrefl i)
        exact ⟨ψ, by simp [g, S]⟩
      · rintro ⟨ψ, rfl⟩
        exact ⟨0, ψ, Or.inr rfl, by simp [g, S]⟩
    rw [this]
    refine (g.antilipschitz_of_bound (K := K) fun ψ =>
      (S.bound_of_antilipschitz hK ψ).trans ?_).isClosed_range g.uniformContinuous
    gcongr
    exact (norm_neg (S ψ)).symm.le.trans (norm_fst_le (g ψ))
  · rw [D.bgg_Δ_of_gt hi, Submodule.bot_coe]
    exact isClosed_singleton

variable (𝕜) in
/-- `Data.idShift` on `𝕜` (`Sⁱ = id`), as bounded data. -/
def idShift : BoundedData 𝕜 (ComplexShape.up ℤ) (fun _ => 𝕜) (fun _ => 𝕜) where
  toData := Data.idShift 𝕜
  continuous_d _ _ := LinearMap.continuous_of_finiteDimensional _
  continuous_dt _ _ := LinearMap.continuous_of_finiteDimensional _
  continuous_S _ _ := LinearMap.continuous_of_finiteDimensional _

variable (𝕜) in
theorem idShift_derivedComplex_closedRangeAt (J i : ℤ) :
    ((idShift 𝕜).derivedComplex (J < ·) (· < J)).ClosedRangeAt i ∧
      Module.finrank 𝕜 (((idShift 𝕜).derivedComplex (J < ·) (· < J)).cohomology i) ≤ 2 := by
  have hΔ : ∀ i, IsClosed ((idShift 𝕜).Δ (· < J) i : Set (𝕜 × 𝕜)) :=
    fun i => Submodule.closed_of_finiteDimensional _
  have h := (Data.injSurj_idShift 𝕜 J).eliminates
  refine ⟨(idShift 𝕜).derivedComplex_closedRangeAt hΔ h i,
    ((idShift 𝕜).finrank_derivedComplex_cohomology_le hΔ h i).trans ?_⟩
  have h₁ : Module.finrank 𝕜 ((idShift 𝕜).rowTopComplex.cohomology i) ≤ 1 :=
    (Submodule.finrank_quotient_le _).trans ((Submodule.finrank_le _).trans_eq
      (Module.finrank_self 𝕜))
  have h₂ : Module.finrank 𝕜 ((idShift 𝕜).rowBotComplex.cohomology i) ≤ 1 :=
    (Submodule.finrank_quotient_le _).trans ((Submodule.finrank_le _).trans_eq
      (Module.finrank_self 𝕜))
  omega

end BoundedData

end Feec.BGG
