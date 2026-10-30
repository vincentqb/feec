module

public import Solution.Defs
public import Feec.HilbertComplex.BGG.Derived

/-!
# The bridge from the challenge to `Feec`

A stacked diagram `S : Ṽ ⟶ V⟦1⟧` of the challenge is `Feec` BGG data on `ComplexShape.up ℤ`
(`BGG.toData`: the differentials of the rows and the connecting maps `BGG.conn S`). Its twisted
complex is that of `Feec` (`BGG.twistComplex_toData`, by definition), the subcomplexes `Γ` and
`Δ` at `J` are the eliminations `Feec.BGG.Data.Γ (J < ·)` and `Feec.BGG.Data.Δ (· < J)` of the
BGG complex of `Feec` (`BGG.Γ_toData`, `BGG.Δ_toData`), and the injectivity/surjectivity
hypothesis is `Feec.BGG.Data.InjSurj J` (`BGG.injSurj_toData`). The quasi-isomorphisms of
`Feec.BGG.Data.quasiIso_Γ` and `Feec.BGG.Data.quasiIso_derived` give the verdict
(`BGG.verdict`).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §5.2

Bibliography: [references.bib](../../../docs/references.bib)
-/

open CategoryTheory

@[expose] public noncomputable section

universe u v

namespace FEEC.BGG

variable {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
  (S : Vt ⟶ V⟦(1 : ℤ)⟧)

/-- The stacked diagram as `Feec` BGG data on `ComplexShape.up ℤ`. -/
def toData : Feec.BGG.Data R (ComplexShape.up ℤ) (fun i => V.X i) (fun i => Vt.X i) where
  d i j := (V.d i j).hom
  dt i j := (Vt.d i j).hom
  S := conn S
  shape_d i j h := by rw [V.shape i j h]; rfl
  shape_dt i j h := by rw [Vt.shape i j h]; rfl
  shape_S i j h := by simp [conn, show i + 1 ≠ j from h]
  d_comp_d i j k x := by rw [← ModuleCat.comp_apply, V.d_comp_d]; rfl
  dt_comp_dt i j k x := by rw [← ModuleCat.comp_apply, Vt.d_comp_d]; rfl
  anticomm := d_conn S

theorem twistComplex_toData : (toData S).twistComplex = twisted S := rfl

theorem conn_succ (i : ℤ) : conn S i (i + 1) = (S.f i).hom := by
  simp [conn]

theorem Γ_toData (J : ℤ) : (toData S).Γ (J < ·) = Γ S J := by
  funext i
  ext x
  rw [Feec.BGG.Data.mem_Γ, CochainComplex.next]
  simp only [Γ, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.fst_apply]
  rfl

theorem Δ_toData (J : ℤ) : (toData S).Δ (· < J) = Δ S J := by
  funext i
  change (⨆ _ : i < J, _) ⊔ ⨆ _ : (ComplexShape.up ℤ).prev i < J,
    (LinearMap.range (LinearMap.inr R _ _)).map
      ((toData S).twist ((ComplexShape.up ℤ).prev i) i) = _
  generalize hp : (ComplexShape.up ℤ).prev i = p
  rw [CochainComplex.prev] at hp
  subst hp
  rfl

theorem injSurj_toData {J : ℤ} (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i → Function.Surjective (S.f i)) : (toData S).InjSurj J := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · change Function.Injective (conn S i (i + 1))
    rw [conn_succ]; exact hinj i hi
  · change Function.Surjective (conn S i (i + 1))
    rw [conn_succ]; exact hsurj i hi

variable {S}

theorem quasiIso_bggΓι {J : ℤ} (h : (toData S).InjSurj J) : QuasiIso (bggΓι S J) := by
  have key : ∀ (G : ∀ i, Submodule R (V.X i × Vt.X i)) (hG : (toData S).Γ (J < ·) = G)
      (hs : ∀ i j, ∀ x ∈ G i, (twisted S).d i j x ∈ G j),
      QuasiIso (subcomplexι (twisted S) G hs) := by
    rintro G rfl hs
    exact (toData S).quasiIso_Γ h.eliminates.top
  exact key _ (Γ_toData S J) _

theorem quasiIso_bggπ {J : ℤ} (h : (toData S).InjSurj J) : QuasiIso (bggπ S J) := by
  have key : ∀ (G H : ∀ i, Submodule R (V.X i × Vt.X i)) (hG : (toData S).Γ (J < ·) = G)
      (hH : (toData S).Δ (· < J) = H) (hs : ∀ i j, ∀ x ∈ G i, (twisted S).d i j x ∈ G j)
      (hs' : ∀ i j, ∀ x ∈ (fun i => (H i).comap (G i).subtype) i,
        (subcomplex (twisted S) G hs).d i j x ∈ (fun i => (H i).comap (G i).subtype) j),
      QuasiIso (quotientπ (subcomplex (twisted S) G hs) _ hs') := by
    rintro G H rfl rfl hs hs'
    exact (toData S).quasiIso_derived h.eliminates
  exact key _ _ (Γ_toData S J) (Δ_toData S J) _ _

theorem rows_shortExact : (rows S).ShortExact := (toData S).twistShortComplex_shortExact

/-- **The BGG verdict** from `Feec.BGG.Data.quasiIso_Γ` and `Feec.BGG.Data.quasiIso_derived`. -/
theorem verdict {J : ℤ} (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i → Function.Surjective (S.f i)) : Verdict S J := by
  have h := injSurj_toData S hinj hsurj
  have := quasiIso_bggΓι h
  have := quasiIso_bggπ h
  have hiso : ∀ i, Nonempty ((bgg S J).homology i ≅ (twisted S).homology i) := fun i =>
    ⟨(isoOfQuasiIsoAt (bggπ S J) i).symm ≪≫ isoOfQuasiIsoAt (bggΓι S J) i⟩
  refine ⟨‹_›, ‹_›, hiso, rows_shortExact, fun hV hVt i => ?_⟩
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((rows_shortExact.acyclic_X₂ hV hVt) i).isZero_homology.of_iso (hiso i).some

end FEEC.BGG
