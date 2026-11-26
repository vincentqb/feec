module

public import Feec.HilbertComplex.BGG.Connecting

/-!
# The sum complex and the explicit cochain map of the BGG complex

If the connecting maps are null-homotopic, `S = dK - Kd̃`, the sum complex is isomorphic to the
twisted complex, and the explicit cochain map (30) from the sum complex to the BGG complex is a
quasi-isomorphism ([ArnoldHu2021], Theorem 7) carrying cohomology representatives of the rows to
those of the BGG complex ([ArnoldHu2021], Corollary 1).

## Main results

* `Data.IsNullHomotopy.inducesZero`: null-homotopic connecting maps induce zero on cohomology.
* `Data.quasiIso_bggSumMap`: (30) is a quasi-isomorphism.
* `Data.bgg_represents`: cohomology representatives of the BGG complex.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3, §5

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace Feec.BGG.Data

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι} {V Vt : ι → Type v}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [∀ i, AddCommGroup (Vt i)]
  [∀ i, Module R (Vt i)] (D : Data R c V Vt)

/-! ## The sum complex -/

/-- The rows of `D` without the connecting maps. -/
def sumData : Data R c V Vt where
  d := D.d
  dt := D.dt
  S _ _ := 0
  shape_d := D.shape_d
  shape_dt := D.shape_dt
  shape_S _ _ _ := rfl
  d_comp_d := D.d_comp_d
  dt_comp_dt := D.dt_comp_dt
  anticomm _ _ _ _ := by simp

/-- The sum complex `V × Ṽ` with the differential `d × d̃`. [ArnoldHu2021], §5.1 -/
abbrev sumComplex : HomologicalComplex (ModuleCat.{v} R) c := D.sumData.twistComplex

@[simp] theorem sumData_twist_apply (i j : ι) (x : V i × Vt i) :
    D.sumData.twist i j x = (D.d i j x.1, D.dt i j x.2) := by
  simp [sumData]

/-- The connecting maps are null-homotopic, `S = dK - Kd̃`. [ArnoldHu2021], (28) -/
def IsNullHomotopy (K : ∀ i, Vt i →ₗ[R] V i) : Prop :=
  ∀ i j, c.Rel i j → ∀ μ, D.S i j μ = D.d i j (K i μ) - K j (D.dt i j μ)

variable {D}

/-- Null-homotopic connecting maps induce zero on cohomology. [ArnoldHu2021], Proposition 1 -/
theorem IsNullHomotopy.inducesZero {K : ∀ i, Vt i →ₗ[R] V i} (hK : D.IsNullHomotopy K) {i j : ι}
    (hij : c.Rel i j) : D.InducesZero i j :=
  fun φ hφ => ⟨K i φ, by rw [hK i j hij, hφ, map_zero, sub_zero]⟩

/-- The shear `(ω, μ) ↦ (ω + Kμ, μ)`. -/
def shear {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (K : N →ₗ[R] M) : (M × N) ≃ₗ[R] (M × N) where
  toFun x := (x.1 + K x.2, x.2)
  invFun x := (x.1 - K x.2, x.2)
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]; abel_nf
  map_smul' a x := by simp
  left_inv x := by simp
  right_inv x := by simp

/-- If `S = dK - Kd̃`, the shear is an isomorphism from the sum complex onto the twisted complex. -/
def sumIso {K : ∀ i, Vt i →ₗ[R] V i} (hK : D.IsNullHomotopy K) : D.sumComplex ≅ D.twistComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (shear (K i)).toModuleIso) fun i j hij =>
    ModuleCat.hom_ext (LinearMap.ext fun (x : V i × Vt i) => Prod.ext (by
      change D.d i j (x.1 + K i x.2) - D.S i j x.2 =
        (D.sumData.twist i j x).1 + K j (D.sumData.twist i j x).2
      rw [sumData_twist_apply, hK i j hij, map_add]
      abel) rfl)

theorem sumIso_hom_apply {K : ∀ i, Vt i →ₗ[R] V i} (hK : D.IsNullHomotopy K) (i : ι)
    (x : V i × Vt i) : ((D.sumIso hK).hom.f i).hom x = (x.1 + K i x.2, x.2) := by
  simp [sumIso]; rfl

/-! ## Cochain maps from the twisted complex to the derived complex -/

variable {E F : ι → Prop}

theorem quasiIso_of_Γι_comp (h : D.Eliminates E F) {r : D.twistComplex ⟶ D.derived E F}
    (hr : D.Γι E ≫ r = D.derivedπ E F) : QuasiIso r := by
  have := quasiIso_Γ (D := D) h.top
  have : QuasiIso (D.Γι E ≫ r) := hr ▸ quasiIso_derived h
  exact quasiIso_of_comp_left (D.Γι E) r

theorem quasiIso_sumIso_comp {K : ∀ i, Vt i →ₗ[R] V i} (hK : D.IsNullHomotopy K)
    (h : D.Eliminates E F) {r : D.twistComplex ⟶ D.derived E F}
    (hr : D.Γι E ≫ r = D.derivedπ E F) : QuasiIso ((D.sumIso hK).hom ≫ r) :=
  have := quasiIso_of_Γι_comp h hr
  inferInstance

theorem range_sumData_twist (i j : ι) :
    LinearMap.range (D.sumData.twist i j) =
      (LinearMap.range (D.d i j)).prod (LinearMap.range (D.dt i j)) := by
  ext x
  simp only [LinearMap.mem_range, Submodule.mem_prod, sumData_twist_apply]
  exact ⟨fun ⟨y, hy⟩ => ⟨⟨y.1, by rw [← hy]⟩, ⟨y.2, by rw [← hy]⟩⟩,
    fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => ⟨(a, b), Prod.ext ha hb⟩⟩

theorem ker_sumData_twist (i j : ι) :
    LinearMap.ker (D.sumData.twist i j) =
      (LinearMap.ker (D.d i j)).prod (LinearMap.ker (D.dt i j)) := by
  ext x
  simp [sumData, Prod.ext_iff]

theorem represents_sumComplex {i : ι} {H : Submodule R (V i)} {Ht : Submodule R (Vt i)}
    (hH : D.rowTop.Represents i H) (hHt : D.rowBot.Represents i Ht) :
    D.sumComplex.Represents i (H.prod Ht) where
  sup_eq := by
    have h1 : LinearMap.range (D.d (c.prev i) i) ⊔ H = LinearMap.ker (D.d i (c.next i)) :=
      hH.sup_eq
    have h2 : LinearMap.range (D.dt (c.prev i) i) ⊔ Ht = LinearMap.ker (D.dt i (c.next i)) :=
      hHt.sup_eq
    change LinearMap.range (D.sumData.twist _ i) ⊔ _ = LinearMap.ker (D.sumData.twist i _)
    rw [range_sumData_twist, ker_sumData_twist, Submodule.prod_sup_prod, h1, h2]
  disjoint := by
    have h1 : LinearMap.range (D.d (c.prev i) i) ⊓ H = ⊥ := disjoint_iff.1 hH.disjoint
    have h2 : LinearMap.range (D.dt (c.prev i) i) ⊓ Ht = ⊥ := disjoint_iff.1 hHt.disjoint
    change Disjoint (LinearMap.range (D.sumData.twist _ i)) _
    rw [range_sumData_twist, disjoint_iff, Submodule.prod_inf_prod, h1, h2, Submodule.prod_bot]

theorem derived_represents {K : ∀ i, Vt i →ₗ[R] V i} (hK : D.IsNullHomotopy K)
    (h : D.Eliminates E F) {r : D.twistComplex ⟶ D.derived E F}
    (hr : D.Γι E ≫ r = D.derivedπ E F) {i : ι} {H : Submodule R (V i)} {Ht : Submodule R (Vt i)}
    (hH : D.rowTop.Represents i H) (hHt : D.rowBot.Represents i Ht) :
    (D.derived E F).Represents i ((H.prod Ht).map (((D.sumIso hK).hom ≫ r).f i).hom) :=
  have := quasiIso_sumIso_comp hK h hr
  (represents_sumComplex hH hHt).map _

/-! ## The BGG complex: the explicit cochain map (30) -/

section Up

variable {V Vt : ℤ → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  [∀ i, AddCommGroup (Vt i)] [∀ i, Module R (Vt i)] (D : Data R (ComplexShape.up ℤ) V Vt)
  (J : ℤ) (t : ∀ i j, V j →ₗ[R] Vt i)

/-- `Sⁱ` injective for `i ≤ J`, with right inverses `tⁱ⁺¹` for `i ≥ J`. [ArnoldHu2021], (23) -/
structure InjSurjWith : Prop where
  injective : ∀ i ≤ J, Function.Injective (D.S i (i + 1))
  S_t : ∀ i j, i + 1 = j → J ≤ i → ∀ v, D.S i j (t i j v) = v

/-- `P = 1 - tⁱ⁺¹ Sⁱ`, the projection onto `N(Sⁱ)` along `R(tⁱ⁺¹)` when `Sⁱ tⁱ⁺¹ = 1`. -/
def kerProj (i : ℤ) : Vt i →ₗ[R] Vt i := LinearMap.id - t i (i + 1) ∘ₗ D.S i (i + 1)

/-- The cochain retraction `Π : T → Γ` in degree `i`. [ArnoldHu2021], (67) -/
def bggProjMap (i : ℤ) : V i × Vt i →ₗ[R] V i × Vt i :=
  if i < J then LinearMap.id
  else if i = J then
    (LinearMap.fst R _ _).prod (t i (i + 1) ∘ₗ D.d i (i + 1) ∘ₗ LinearMap.fst R _ _)
  else (0 : V i × Vt i →ₗ[R] V i).prod (D.kerProj t i ∘ₗ
    (LinearMap.snd R _ _ + D.dt (i - 1) i ∘ₗ t (i - 1) i ∘ₗ LinearMap.fst R _ _))

variable {D J t}

theorem bggProjMap_of_lt {i : ℤ} (hi : i < J) (x : V i × Vt i) : D.bggProjMap J t i x = x := by
  simp [bggProjMap, hi]

theorem bggProjMap_of_eq {i : ℤ} (hi : i = J) (x : V i × Vt i) :
    D.bggProjMap J t i x = (x.1, t i (i + 1) (D.d i (i + 1) x.1)) := by
  simp [bggProjMap, hi]

theorem bggProjMap_of_gt {i : ℤ} (hi : J < i) (x : V i × Vt i) :
    D.bggProjMap J t i x = (0, D.kerProj t i (x.2 + D.dt (i - 1) i (t (i - 1) i x.1))) := by
  simp [bggProjMap, not_lt.2 hi.le, hi.ne']

theorem kerProj_apply (i : ℤ) (φ : Vt i) :
    D.kerProj t i φ = φ - t i (i + 1) (D.S i (i + 1) φ) := rfl

theorem dt_t_prev {a k : ℤ} (h : a + 1 = k) (v : V k) :
    D.dt (k - 1) k (t (k - 1) k v) = D.dt a k (t a k v) := by
  subst h; rw [add_sub_cancel_right]

theorem kerProj_of_S {i : ℤ} {φ : Vt i} (hφ : D.S i (i + 1) φ = 0) : D.kerProj t i φ = φ := by
  rw [kerProj_apply, hφ, map_zero, sub_zero]

variable (h : D.InjSurjWith J t)
include h

theorem InjSurjWith.S_t' {i : ℤ} (hi : J ≤ i) (v : V (i + 1)) :
    D.S i (i + 1) (t i (i + 1) v) = v :=
  h.S_t i _ rfl hi v

theorem InjSurjWith.t_S (φ : Vt J) : t J (J + 1) (D.S J (J + 1) φ) = φ :=
  h.injective J le_rfl (h.S_t' le_rfl _)

theorem InjSurjWith.S_kerProj {i : ℤ} (hi : J ≤ i) (φ : Vt i) :
    D.S i (i + 1) (D.kerProj t i φ) = 0 := by
  rw [kerProj_apply, map_sub, h.S_t' hi, sub_self]

theorem bggProjMap_mem_Γ (i : ℤ) (x : V i × Vt i) : D.bggProjMap J t i x ∈ D.Γ (J < ·) i := by
  rcases lt_trichotomy i J with hi | rfl | hi
  · rw [D.bgg_Γ_of_lt hi]; trivial
  · rw [bggProjMap_of_eq rfl, D.mem_bgg_Γ_self, h.S_t' le_rfl]
  · rw [bggProjMap_of_gt hi, D.mem_bgg_Γ_of_gt hi]
    exact ⟨rfl, h.S_kerProj hi.le _⟩

theorem twist_bggProjMap (i : ℤ) (x : V i × Vt i) :
    D.twist i (i + 1) (D.bggProjMap J t i x) = D.bggProjMap J t (i + 1) (D.twist i (i + 1) x) := by
  obtain ⟨ω, μ⟩ := x
  rcases lt_trichotomy (i + 1) J with hi | hi | hi
  · rw [bggProjMap_of_lt (by omega), bggProjMap_of_lt hi]
  · rw [bggProjMap_of_lt (by omega), bggProjMap_of_eq hi]
    obtain rfl := hi
    refine Prod.ext rfl ?_
    simp only [twist_apply, map_sub, D.d_comp_d, D.anticomm, zero_sub, neg_neg]
    exact (h.t_S _).symm
  · rcases (by omega : i = J ∨ J < i) with rfl | hi'
    · rw [bggProjMap_of_eq rfl, bggProjMap_of_gt hi, dt_t_prev rfl]
      have hd := h.S_t' le_rfl (D.d i (i + 1) ω)
      have hk : D.S (i + 1) (i + 1 + 1) (D.dt i (i + 1) (t i (i + 1) (D.d i (i + 1) ω))) = 0 := by
        rw [← neg_eq_zero, ← D.anticomm, hd, D.d_comp_d]
      refine Prod.ext (by simp [hd]) ?_
      change D.dt i (i + 1) (t i (i + 1) (D.d i (i + 1) ω)) = D.kerProj t (i + 1)
        (D.dt i (i + 1) μ + D.dt i (i + 1) (t i (i + 1) (D.d i (i + 1) ω - D.S i (i + 1) μ)))
      rw [map_sub, h.t_S, map_sub, add_sub_cancel, kerProj_of_S hk]
    · rw [bggProjMap_of_gt hi', bggProjMap_of_gt hi, dt_t_prev rfl]
      have hd : D.S i (i + 1) (D.dt (i - 1) i (t (i - 1) i ω)) = -D.d i (i + 1) ω := by
        rw [← neg_neg (D.S i (i + 1) _), ← D.anticomm, h.S_t (i - 1) i (by omega) (by omega)]
      set y := μ + D.dt (i - 1) i (t (i - 1) i ω)
      have hk : D.S (i + 1) (i + 1 + 1) (D.dt i (i + 1) (D.kerProj t i y)) = 0 := by
        rw [← neg_eq_zero, ← D.anticomm, h.S_kerProj hi'.le, map_zero]
      have key : D.dt i (i + 1) (D.kerProj t i y) = D.dt i (i + 1) μ +
          D.dt i (i + 1) (t i (i + 1) (D.d i (i + 1) ω - D.S i (i + 1) μ)) := by
        simp only [y, kerProj_apply, map_add, map_sub, map_neg, hd, D.dt_comp_dt]
        abel
      refine Prod.ext (by simp [h.S_kerProj hi'.le]) ?_
      change D.dt i (i + 1) (D.kerProj t i y) = D.kerProj t (i + 1)
        (D.dt i (i + 1) μ + D.dt i (i + 1) (t i (i + 1) (D.d i (i + 1) ω - D.S i (i + 1) μ)))
      rw [← key, kerProj_of_S hk]

theorem bggProjMap_of_mem {i : ℤ} {x : V i × Vt i} (hx : x ∈ D.Γ (J < ·) i) :
    D.bggProjMap J t i x = x := by
  obtain ⟨σ, φ⟩ := x
  rcases lt_trichotomy i J with hi | rfl | hi
  · exact bggProjMap_of_lt hi _
  · rw [bggProjMap_of_eq rfl, (D.mem_bgg_Γ_self).1 hx, h.t_S]
  · obtain ⟨h1, h2⟩ := (D.mem_bgg_Γ_of_gt hi).1 hx
    simp only at h1 h2
    rw [bggProjMap_of_gt hi, h1, map_zero, map_zero, add_zero, kerProj_of_S h2]

variable (D t) in
/-- The cochain retraction `Π : T → Γ` of the inclusion. [ArnoldHu2021], (67), Lemma 9 -/
def bggProj : D.twistComplex ⟶ D.ΓComplex (J < ·) where
  f i := ModuleCat.ofHom (X := D.twistComplex.X i) (Y := (D.ΓComplex (J < ·)).X i)
    ((D.bggProjMap J t i).codRestrict (D.Γ (J < ·) i) (D.bggProjMap_mem_Γ h i))
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (D.twist_bggProjMap h i x))

theorem Γι_bggProj : D.Γι (J < ·) ≫ D.bggProj t h = 𝟙 _ := by
  ext i x : 3
  exact Subtype.ext (D.bggProjMap_of_mem h x.2)

theorem InjSurjWith.injSurj : D.InjSurj J :=
  ⟨fun i hi => h.injective i hi.le, fun i hi v => ⟨t i (i + 1) v, h.S_t' hi v⟩⟩

theorem InjSurjWith.bijective : Function.Bijective (D.S J (J + 1)) :=
  ⟨h.injective J le_rfl, h.injSurj.2 J le_rfl⟩

theorem quasiIso_bggProj : QuasiIso (D.bggProj t h) := by
  have := quasiIso_Γ (D := D) h.injSurj.eliminates.top
  have : QuasiIso (D.Γι (J < ·) ≫ D.bggProj t h) := by rw [Γι_bggProj]; infer_instance
  exact quasiIso_of_comp_left (D.Γι (J < ·)) (D.bggProj t h)

omit h in
variable (D t) in
/-- The cochain map (30) from the sum complex to the BGG complex. [ArnoldHu2021], (30) -/
def bggSumMap {K : ∀ i, Vt i →ₗ[R] V i} (hK : D.IsNullHomotopy K) (h : D.InjSurjWith J t) :
    D.sumComplex ⟶ D.bgg J :=
  (D.sumIso hK).hom ≫ D.bggProj t h ≫ D.derivedπ _ _

variable {K : ∀ i, Vt i →ₗ[R] V i} (hK : D.IsNullHomotopy K)

theorem bggSumMap_apply (i : ℤ) (x : V i × Vt i) :
    ((D.bggSumMap t hK h).f i).hom x =
      Submodule.Quotient.mk ⟨D.bggProjMap J t i (x.1 + K i x.2, x.2), D.bggProjMap_mem_Γ h i _⟩ := by
  simp only [bggSumMap, HomologicalComplex.comp_f, ModuleCat.hom_comp]
  rfl

theorem bggXEquivOfLt_bggSumMap {i : ℤ} (hi : i < J) (x : V i × Vt i) :
    D.bggXEquivOfLt hi (((D.bggSumMap t hK h).f i).hom x) =
      Submodule.Quotient.mk (x.1 + K i x.2) := by
  rw [bggSumMap_apply]
  exact (D.bggXEquivOfLt_mk hi _).trans (congrArg _ (congrArg Prod.fst (bggProjMap_of_lt hi _)))

theorem bggXEquivOfBijective_bggSumMap (x : V J × Vt J) :
    D.bggXEquivOfBijective h.bijective (((D.bggSumMap t hK h).f J).hom x) =
      Submodule.Quotient.mk (x.1 + K J x.2) := by
  rw [bggSumMap_apply]
  exact (D.bggXEquivOfBijective_mk h.bijective _).trans
    (congrArg _ (congrArg Prod.fst (bggProjMap_of_eq rfl _)))

theorem bggSumMap_of_gt {i : ℤ} (hi : J < i) (x : V i × Vt i) :
    ((D.derivedXEquiv _ _ (D.bgg_Δ_of_gt hi) (((D.bggSumMap t hK h).f i).hom x) :
        D.Γ (J < ·) i) : V i × Vt i) =
      (0, D.kerProj t i (D.dt (i - 1) i (t (i - 1) i x.1) +
        (x.2 + D.dt (i - 1) i (t (i - 1) i (K i x.2))))) := by
  rw [bggSumMap_apply]
  refine (congrArg Subtype.val (Submodule.quotEquivOfEqBot_apply_mk _ _ _)).trans ?_
  change D.bggProjMap J t i (x.1 + K i x.2, x.2) = _
  rw [bggProjMap_of_gt hi]
  congr 2
  rw [map_add, map_add]
  abel

theorem Γι_bggProj_derivedπ :
    D.Γι (J < ·) ≫ D.bggProj t h ≫ D.derivedπ (J < ·) (· < J) = D.derivedπ _ _ := by
  rw [← Category.assoc, Γι_bggProj, Category.id_comp]

/-- The cochain map (30) induces an isomorphism on cohomology. [ArnoldHu2021], Theorem 7 -/
theorem quasiIso_bggSumMap : QuasiIso (D.bggSumMap t hK h) :=
  quasiIso_sumIso_comp hK h.injSurj.eliminates (D.Γι_bggProj_derivedπ h)

/-- If `H`, `H̃` represent the cohomology of the rows at `i`, then `(30)(H × H̃)` represents the
cohomology of the BGG complex. [ArnoldHu2021], Corollary 1, (31) -/
theorem bgg_represents {i : ℤ} {H : Submodule R (V i)} {Ht : Submodule R (Vt i)}
    (hH : D.rowTop.Represents i H) (hHt : D.rowBot.Represents i Ht) :
    (D.bgg J).Represents i ((H.prod Ht).map ((D.bggSumMap t hK h).f i).hom) :=
  derived_represents hK h.injSurj.eliminates (D.Γι_bggProj_derivedπ h) hH hHt

end Up

/-! ### Non-vacuity -/

variable (R) in
theorem idShift_injSurjWith (J : ℤ) :
    (idShift R).InjSurjWith J fun i j => if i + 1 = j then LinearMap.id else 0 where
  injective i _ := by
    rw [show (idShift R).S i (i + 1) = LinearMap.id from ite_eq_left rfl]
    exact Function.injective_id
  S_t i j hij _ v := by simp [idShift, hij]

variable (R) in
/-- `R` with `dⁱ = id` for even `i`, `0` for odd `i`, its shift `d̃ⁱ = -dⁱ⁺¹`, and `Sⁱ = id`. -/
def altShift : Data R (ComplexShape.up ℤ) (fun _ => R) (fun _ => R) where
  d i j := if i + 1 = j ∧ Even i then LinearMap.id else 0
  dt i j := if i + 1 = j ∧ Odd i then -LinearMap.id else 0
  S i j := if i + 1 = j then LinearMap.id else 0
  shape_d _ _ h := ite_eq_right fun h' => h h'.1
  shape_dt _ _ h := ite_eq_right fun h' => h h'.1
  shape_S _ _ h := ite_eq_right h
  d_comp_d i j k x := by
    by_cases h : j + 1 = k ∧ Even j
    · obtain ⟨rfl, hj⟩ := h
      have : ¬ (i + 1 = j ∧ Even i) := fun h' => Int.not_even_iff_odd.2 (h'.1 ▸ h'.2.add_one) hj
      simp only [ite_eq_right this, LinearMap.zero_apply, map_zero]
    · simp only [ite_eq_right h, LinearMap.zero_apply]
  dt_comp_dt i j k x := by
    by_cases h : j + 1 = k ∧ Odd j
    · obtain ⟨rfl, hj⟩ := h
      have : ¬ (i + 1 = j ∧ Odd i) := fun h' => Int.not_odd_iff_even.2 (h'.1 ▸ h'.2.add_one) hj
      simp only [ite_eq_right this, LinearMap.zero_apply, map_zero]
    · simp only [ite_eq_right h, LinearMap.zero_apply]
  anticomm i j k φ := by
    by_cases hij : i + 1 = j
    · subst hij
      by_cases hjk : i + 1 + 1 = k
      · rcases Int.even_or_odd i with hi | hi
        · simp [hjk, Int.not_even_iff_odd.2 hi.add_one, Int.not_odd_iff_even.2 hi]
        · simp [hjk, hi.add_one, hi]
      · simp [hjk]
    · simp [hij]

variable (R) in
theorem altShift_isNullHomotopy : (altShift R).IsNullHomotopy fun _ => LinearMap.id := by
  rintro i _ rfl μ
  rcases Int.even_or_odd i with hi | hi
  · simp [altShift, hi, Int.not_odd_iff_even.2 hi]
  · simp [altShift, hi, Int.not_even_iff_odd.2 hi]

variable (R) in
theorem altShift_injSurjWith (J : ℤ) :
    (altShift R).InjSurjWith J fun i j => if i + 1 = j then LinearMap.id else 0 where
  injective i _ := by
    rw [show (altShift R).S i (i + 1) = LinearMap.id from ite_eq_left rfl]
    exact Function.injective_id
  S_t i j hij _ v := by simp [altShift, hij]

variable (R) in
/-- The cochain map (30) of `altShift` is a quasi-isomorphism at every `J`. -/
theorem altShift_quasiIso_bggSumMap (J : ℤ) :
    QuasiIso ((altShift R).bggSumMap _ (altShift_isNullHomotopy R) (altShift_injSurjWith R J)) :=
  quasiIso_bggSumMap _ _

variable (R) in
theorem altShift_bgg_represents (J : ℤ) {i : ℤ} {H Ht : Submodule R R}
    (hH : (altShift R).rowTop.Represents i H) (hHt : (altShift R).rowBot.Represents i Ht) :
    ((altShift R).bgg J).Represents i ((H.prod Ht).map
      (((altShift R).bggSumMap _ (altShift_isNullHomotopy R) (altShift_injSurjWith R J)).f i).hom) :=
  bgg_represents _ _ hH hHt

end Feec.BGG.Data
