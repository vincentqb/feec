module

public import Solution.Defs
public import Feec.HilbertComplex.BGG.Analytic
public import Feec.HilbertComplex.BGG.Connecting
public import Feec.HilbertComplex.BGG.Orthogonal
public import Feec.HilbertComplex.BGG.SumComplex

/-!
# The bridge from the BGG complexes of the challenge to `Feec`

A stacked diagram `S : Ṽ ⟶ V⟦1⟧` of the challenge is `Feec` BGG data on `ComplexShape.up ℤ`
(`BGG.toData`: the differentials of the rows and the connecting maps `BGG.conn S`). Its twisted
complex is that of `Feec` (`BGG.twistComplex_toData`, by definition), the subcomplexes `Γ` and
`Δ` at `J` are the eliminations `Feec.BGG.Data.Γ (J < ·)` and `Feec.BGG.Data.Δ (· < J)` of the
BGG complex of `Feec` (`BGG.Γ_toData`, `BGG.Δ_toData`), and the hypothesis of the challenge gives
`Feec.BGG.Data.Eliminates` (`BGG.eliminates_toData`). The quasi-isomorphisms of
`Feec.BGG.Data.quasiIso_Γ` and `Feec.BGG.Data.quasiIso_derived` give the verdict (`BGG.verdict`);
with the long exact sequence of the rows, the dimension bound over a field
(`BGG.finiteDimensional_and_finrank_le`). The identification with the output complex
(`BGG.identification`), the sum complex (`BGG.sum`), the explicit map (30) (`BGG.explicit`), the
bounded Hilbert complex (`BGG.hilbert`) and the orthogonal form of (30) (`BGG.orthogonal`) follow
from the BGG space lemmas of `Feec.HilbertComplex.BGG.Derived`, `Feec.BGG.Data.bggSumMap`,
`Feec.HilbertComplex.Subquotient` and `Feec.BGG.BoundedData.orthSumMap`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], (24)–(31), Theorems 6 and 7, §5

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

theorem eliminates_toData {J : ℤ} (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i →
      LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (conn S i (i + 1)) = ⊤) :
    (toData S).Eliminates (J < ·) (· < J) :=
  Feec.BGG.Data.eliminates_bgg (fun i hi => by
      change Function.Injective (conn S i (i + 1))
      rw [conn_succ]; exact hinj i hi)
    fun j hj => by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [add_sub_cancel_right]
      exact hsurj i (by omega)

variable {S}

theorem quasiIso_bggΓι {J : ℤ} (h : (toData S).Eliminates (J < ·) (· < J)) :
    QuasiIso (bggΓι S J) := by
  have key : ∀ (G : ∀ i, Submodule R (V.X i × Vt.X i)) (hG : (toData S).Γ (J < ·) = G)
      (hs : ∀ i j, ∀ x ∈ G i, (twisted S).d i j x ∈ G j),
      QuasiIso (subcomplexι (twisted S) G hs) := by
    rintro G rfl hs
    exact (toData S).quasiIso_Γ h.top
  exact key _ (Γ_toData S J) _

theorem quasiIso_bggπ {J : ℤ} (h : (toData S).Eliminates (J < ·) (· < J)) :
    QuasiIso (bggπ S J) := by
  have key : ∀ (G H : ∀ i, Submodule R (V.X i × Vt.X i)) (hG : (toData S).Γ (J < ·) = G)
      (hH : (toData S).Δ (· < J) = H) (hs : ∀ i j, ∀ x ∈ G i, (twisted S).d i j x ∈ G j)
      (hs' : ∀ i j, ∀ x ∈ (fun i => (H i).comap (G i).subtype) i,
        (subcomplex (twisted S) G hs).d i j x ∈ (fun i => (H i).comap (G i).subtype) j),
      QuasiIso (quotientπ (subcomplex (twisted S) G hs) _ hs') := by
    rintro G H rfl rfl hs hs'
    exact (toData S).quasiIso_derived h
  exact key _ _ (Γ_toData S J) (Δ_toData S J) _ _

theorem rows_shortExact : (rows S).ShortExact := (toData S).twistShortComplex_shortExact

variable (S) in
/-- **The conclusions of the BGG construction at `J`** (the clauses of `FEEC.bggCohomology` under
its hypotheses, with the short exact sequence of the rows). -/
structure Verdict (J : ℤ) : Prop where
  /-- the inclusion `Γ → T` is a quasi-isomorphism -/
  quasiIso_ι : QuasiIso (bggΓι S J)
  /-- the projection `Γ → Γ / Δ` is a quasi-isomorphism -/
  quasiIso_π : QuasiIso (bggπ S J)
  /-- the BGG complex has the cohomology of the twisted complex, in every degree -/
  homology : ∀ i, Nonempty ((bgg S J).homology i ≅ (twisted S).homology i)
  /-- the twisted complex is an extension `0 → V → T → Ṽ → 0` -/
  shortExact : (rows S).ShortExact
  /-- the BGG complex is exact when both rows are -/
  acyclic : V.Acyclic → Vt.Acyclic → (bgg S J).Acyclic

/-- **The BGG verdict** from `Feec.BGG.Data.quasiIso_Γ` and `Feec.BGG.Data.quasiIso_derived`. -/
theorem verdict {J : ℤ} (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i →
      LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (conn S i (i + 1)) = ⊤) :
    Verdict S J := by
  have h := eliminates_toData S hinj hsurj
  have := quasiIso_bggΓι h
  have := quasiIso_bggπ h
  have hiso : ∀ i, Nonempty ((bgg S J).homology i ≅ (twisted S).homology i) := fun i =>
    ⟨(isoOfQuasiIsoAt (bggπ S J) i).symm ≪≫ isoOfQuasiIsoAt (bggΓι S J) i⟩
  refine ⟨‹_›, ‹_›, hiso, rows_shortExact, fun hV hVt i => ?_⟩
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((rows_shortExact.acyclic_X₂ hV hVt) i).isZero_homology.of_iso (hiso i).some

theorem inducesZero_iff {k j : ℤ} (h : k + 1 = j) :
    InducesZero S k ↔ (toData S).InducesZero k j := by
  subst h; rfl

/-- **The dimension bound and the equality criterion (27)**: `Hⁱ(Γ / Δ) ≅ Hⁱ(T)` and
`0 → V → T → Ṽ → 0` (`Feec`'s `CategoryTheory.ShortComplex.ShortExact.finrank_homology₂_le`,
`Feec.BGG.Data.finrank_twistComplex_homology_eq_iff`). -/
theorem finiteDimensional_and_finrank_le {K : Type u} [Field K]
    {V Vt : CochainComplex (ModuleCat.{v} K) ℤ} {S : Vt ⟶ V⟦(1 : ℤ)⟧} {J : ℤ}
    (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i →
      LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (conn S i (i + 1)) = ⊤) (i : ℤ)
    [FiniteDimensional K (V.homology i)] [FiniteDimensional K (Vt.homology i)] :
    FiniteDimensional K ((bgg S J).homology i) ∧
      Module.finrank K ((bgg S J).homology i) ≤
        Module.finrank K (V.homology i) + Module.finrank K (Vt.homology i) ∧
      (Module.finrank K ((bgg S J).homology i) =
          Module.finrank K (V.homology i) + Module.finrank K (Vt.homology i) ↔
        InducesZero S (i - 1) ∧ InducesZero S i) := by
  have hv := verdict hinj hsurj
  obtain ⟨e⟩ := hv.homology i
  have : FiniteDimensional K ((rows S).X₁.homology i) := ‹FiniteDimensional K (V.homology i)›
  have : FiniteDimensional K ((rows S).X₃.homology i) := ‹FiniteDimensional K (Vt.homology i)›
  have : FiniteDimensional K ((twisted S).homology i) :=
    hv.shortExact.finiteDimensional_homology₂ i
  refine ⟨e.toLinearEquiv.symm.finiteDimensional, ?_, ?_⟩
  · rw [e.toLinearEquiv.finrank_eq]
    exact hv.shortExact.finrank_homology₂_le i
  · have : FiniteDimensional K ((toData S).rowTop.homology i) :=
      ‹FiniteDimensional K (V.homology i)›
    have : FiniteDimensional K ((toData S).rowBot.homology i) :=
      ‹FiniteDimensional K (Vt.homology i)›
    rw [e.toLinearEquiv.finrank_eq, inducesZero_iff (S := S) (sub_add_cancel i 1),
      inducesZero_iff (S := S) rfl]
    exact (toData S).finrank_twistComplex_homology_eq_iff (h := i - 1) (j := i + 1)
      (sub_add_cancel i 1) rfl

/-! ### The identification with [ArnoldHu2021], (24)–(26) -/

section Identification

variable (S)

theorem mem_Γ_of_lt {J i : ℤ} (hi : i < J) (x : V.X i × Vt.X i) : x ∈ Γ S J i := by
  rw [← Γ_toData, (toData S).bgg_Γ_of_lt hi]; trivial

theorem mem_Γ_self {J : ℤ} {x : V.X J × Vt.X J} :
    x ∈ Γ S J J ↔ V.d J (J + 1) x.1 = conn S J (J + 1) x.2 := by
  rw [← Γ_toData]; exact (toData S).mem_bgg_Γ_self

theorem mem_Γ_of_gt {J i : ℤ} (hi : J < i) {x : V.X i × Vt.X i} :
    x ∈ Γ S J i ↔ x.1 = 0 ∧ conn S i (i + 1) x.2 = 0 := by
  rw [← Γ_toData]; exact (toData S).mem_bgg_Γ_of_gt hi

theorem mem_Δ_of_lt {J i : ℤ} (hi : i < J) {x : V.X i × Vt.X i} :
    x ∈ Δ S J i ↔ x.1 ∈ rangeS S i := by
  rw [← Δ_toData]; exact (toData S).mem_bgg_Δ_of_lt hi

theorem mem_Δ_self {J : ℤ} {x : V.X J × Vt.X J} :
    x ∈ Δ S J J ↔ ∃ ψ, x = (-conn S (J - 1) J ψ, Vt.d (J - 1) J ψ) := by
  rw [← Δ_toData, (toData S).mem_bgg_Δ_of_le le_rfl]
  constructor
  · rintro ⟨φ, ψ, hφ, rfl⟩
    obtain rfl := hφ.resolve_left (lt_irrefl J)
    exact ⟨ψ, Prod.ext rfl (zero_add _)⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨0, ψ, Or.inr rfl, Prod.ext rfl (zero_add _).symm⟩

theorem Δ_of_gt {J i : ℤ} (hi : J < i) : Δ S J i = ⊥ := by
  rw [← Δ_toData]; exact (toData S).bgg_Δ_of_gt hi

theorem bggπ_surjective (J i : ℤ) : Function.Surjective ((bggπ S J).f i) :=
  Submodule.Quotient.mk_surjective _

theorem bggπ_eq_iff {J i : ℤ} (y y' : (bggΓ S J).X i) :
    (bggπ S J).f i y = (bggπ S J).f i y' ↔ y.1 - y'.1 ∈ Δ S J i :=
  Submodule.Quotient.eq _

theorem toQuotS_bggπ {J i : ℤ} (y : (bggΓ S J).X i) :
    (toQuotS S J).f i ((bggπ S J).f i y) = Submodule.Quotient.mk (p := rangeS S i) y.1.1 := rfl

theorem ofKerS_apply {J i : ℤ} (φ : (kerS S).X i) :
    (ofKerS S J).f i φ = (bggπ S J).f i ⟨((0 : V.X i), φ.1), inr_mem_Γ S J i φ⟩ := rfl

theorem bgg_d_bggπ {J : ℤ} (i j : ℤ) (y : (bggΓ S J).X i) :
    (bgg S J).d i j ((bggπ S J).f i y) = (bggπ S J).f j ((bggΓ S J).d i j y) :=
  (congrArg (fun g : (bggΓ S J).X i ⟶ (bgg S J).X j => g y) ((bggπ S J).comm i j)).symm

theorem Sf_apply (i : ℤ) (φ : Vt.X i) : S.f i φ = conn S i (i + 1) φ := by
  rw [conn_succ]

/-- `Γⁱ / Δⁱ → Vⁱ / R(Sⁱ⁻¹)` is injective where `x₁ ∈ R(Sⁱ⁻¹)` forces `x ∈ Δⁱ`. -/
theorem toQuotS_injective {J i : ℤ}
    (hΔ : ∀ y : (bggΓ S J).X i, y.1.1 ∈ rangeS S i → y.1 ∈ Δ S J i) :
    Function.Injective ((toQuotS S J).f i) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := bggπ_surjective S J i a
  obtain ⟨b, rfl⟩ := bggπ_surjective S J i b
  exact (bggπ_eq_iff S a b).2 (hΔ (a - b) ((Submodule.Quotient.eq (rangeS S i)).1 hab))

theorem identification (J : ℤ) : Identification S J where
  lt i hi := by
    refine ⟨toQuotS_injective S fun y hy => (mem_Δ_of_lt S hi).2 hy, fun q => ?_⟩
    obtain ⟨σ, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨(bggπ S J).f i ⟨(σ, 0), mem_Γ_of_lt S hi _⟩, rfl⟩
  self hS := by
    refine ⟨toQuotS_injective S fun y hy => ?_, fun q => ?_⟩
    · obtain ⟨ψ, hψ⟩ := hy
      refine (mem_Δ_self S).2 ⟨-ψ, Prod.ext (by rw [map_neg, neg_neg]; exact hψ.symm) (hS.1 ?_)⟩
      change S.f J y.1.2 = S.f J (Vt.d (J - 1) J (-ψ))
      rw [Sf_apply, Sf_apply, ← (mem_Γ_self S).1 y.2, ← hψ, d_conn, map_neg, map_neg]
    · obtain ⟨σ, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨φ, hφ⟩ := hS.2 (V.d J (J + 1) σ)
      exact ⟨(bggπ S J).f J ⟨(σ, φ), (mem_Γ_self S).2 (by rw [← Sf_apply]; exact hφ.symm)⟩, rfl⟩
  gt i hi := by
    refine ⟨fun a b hab => ?_, fun q => ?_⟩
    · have h : ((0 : V.X i), a.1) - ((0 : V.X i), b.1) ∈ Δ S J i := (bggπ_eq_iff S _ _).1 hab
      rw [Δ_of_gt S hi, Submodule.mem_bot] at h
      exact Subtype.ext (sub_eq_zero.1 (congrArg Prod.snd h))
    · obtain ⟨y, rfl⟩ := bggπ_surjective S J i q
      obtain ⟨h1, h2⟩ := (mem_Γ_of_gt S hi).1 y.2
      refine ⟨⟨y.1.2, by rw [LinearMap.mem_ker, ← conn_succ]; exact h2⟩,
        (ofKerS_apply S _).trans (congrArg _ (Subtype.ext (Prod.ext h1.symm rfl)))⟩
  d_self hS x σ φ hx hφ := by
    obtain ⟨⟨⟨σ', φ'⟩, hy⟩, rfl⟩ := bggπ_surjective S J J x
    obtain ⟨ψ, hψ⟩ := (Submodule.Quotient.eq (rangeS S J)).1 hx
    change conn S (J - 1) J ψ = σ' - σ at hψ
    have hΓ : V.d J (J + 1) σ' = conn S J (J + 1) φ' := (mem_Γ_self S).1 hy
    have h1 := d_conn S (J - 1) J (J + 1) ψ
    rw [hψ, map_sub] at h1
    have h2 : conn S J (J + 1) (Vt.d (J - 1) J ψ) = V.d J (J + 1) σ - V.d J (J + 1) σ' := by
      rw [← neg_sub (V.d J (J + 1) σ'), h1, neg_neg]
    have hy2 : φ' = φ - Vt.d (J - 1) J ψ := by
      apply hS
      rw [Sf_apply, Sf_apply, map_sub, ← hΓ, hφ, h2, sub_sub_cancel]
    have hm : Vt.d J (J + 1) φ' ∈ LinearMap.ker (S.f (J + 1)).hom := by
      rw [LinearMap.mem_ker, ← conn_succ, ← neg_eq_zero, ← d_conn, ← hΓ,
        ← ModuleCat.comp_apply, V.d_comp_d]; rfl
    have hd : (bggΓ S J).d J (J + 1) ⟨(σ', φ'), hy⟩ =
        ⟨((0 : V.X (J + 1)), Vt.d J (J + 1) φ'), inr_mem_Γ S J (J + 1) ⟨_, hm⟩⟩ := by
      refine Subtype.ext (Prod.ext ?_ rfl)
      change V.d J (J + 1) σ' - conn S J (J + 1) φ' = 0
      rw [hΓ, sub_self]
    refine ⟨⟨_, hm⟩, ?_, ?_⟩
    · exact (ofKerS_apply S _).trans ((congrArg _ hd.symm).trans (bgg_d_bggπ S J (J + 1) _).symm)
    · change Vt.d J (J + 1) φ' = _
      rw [hy2, map_sub, ← ModuleCat.comp_apply, Vt.d_comp_d]; simp

/-- **The cohomology of the BGG complex in the lowest degree of the rows**
(`Feec.BGG.Data.exists_bgg_homology_lowCycles`): if the rows vanish in degree `i - 1` and `i ≤ J`,
with `Sⁱ` one-to-one if `J = i` and `Sⁱ⁺¹` one-to-one if `i + 2 ≤ J`, then `[(σ, φ)] ↦ σ`
embeds `Hⁱ(Γ / Δ)` into `Vⁱ` with range `{σ | dσ ∈ Sⁱ N(d̃ⁱ)}`. -/
theorem exists_bgg_homology_lowCycles {i J : ℤ} (hiJ : i ≤ J) [Subsingleton (V.X (i - 1))]
    [Subsingleton (Vt.X (i - 1))] (hS : J = i → Function.Injective (S.f i))
    (hS' : i + 2 ≤ J → Function.Injective (S.f (i + 1))) :
    ∃ f : (bgg S J).homology i →ₗ[R] V.X i, Function.Injective f ∧
      LinearMap.range f = (toData S).lowCycles i ∧
      ∀ (z : (bgg S J).cycles i) (y : Γ S J i), (bgg S J).iCycles i z = Submodule.Quotient.mk y →
        f ((bgg S J).homologyπ i z) = y.1.1 := by
  have hS₁ : J = i → Function.Injective ((toData S).S i (i + 1)) := fun h => by
    change Function.Injective (conn S i (i + 1))
    rw [conn_succ]; exact hS h
  have hS₂ : i + 2 ≤ J → Function.Injective ((toData S).S (i + 1) (i + 1 + 1)) := fun h => by
    change Function.Injective (conn S (i + 1) (i + 1 + 1))
    rw [conn_succ]; exact hS' h
  have key : ∀ (G H : ∀ i, Submodule R (V.X i × Vt.X i)) (hG : (toData S).Γ (J < ·) = G)
      (hH : (toData S).Δ (· < J) = H) (hs : ∀ i j, ∀ x ∈ G i, (twisted S).d i j x ∈ G j)
      (hs' : ∀ i j, ∀ x ∈ (fun i => (H i).comap (G i).subtype) i,
        (subcomplex (twisted S) G hs).d i j x ∈ (fun i => (H i).comap (G i).subtype) j),
      ∃ f : (quotient (subcomplex (twisted S) G hs) _ hs').homology i →ₗ[R] V.X i,
        Function.Injective f ∧ LinearMap.range f = (toData S).lowCycles i ∧
        ∀ (z : (quotient (subcomplex (twisted S) G hs) _ hs').cycles i) (y : G i),
          (quotient (subcomplex (twisted S) G hs) _ hs').iCycles i z =
              Submodule.Quotient.mk y →
            f ((quotient (subcomplex (twisted S) G hs) _ hs').homologyπ i z) = y.1.1 := by
    rintro G H rfl rfl hs hs'
    exact (toData S).exists_bgg_homology_lowCycles hiJ hS₁ hS₂
  exact key _ _ (Γ_toData S J) (Δ_toData S J) _ _

end Identification

/-! ### The sum complex ([ArnoldHu2021], Theorem 7) -/

theorem isIso_sumToTwisted {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (K : ∀ i, Vt.X i →ₗ[R] V.X i)
    (hK : ∀ i μ, conn S i (i + 1) μ = V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ)) :
    IsIso (sumToTwisted S K hK) := by
  refine @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ fun i => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b hab => ?_, fun x => ⟨((x.1 - K i x.2, x.2) : V.X i × Vt.X i), ?_⟩⟩
  · have h2' := congrArg (fun y : V.X i × Vt.X i => y.2) hab
    have h1' := congrArg (fun y : V.X i × Vt.X i => y.1) hab
    have h2 : a.2 = b.2 := h2'
    have h1 : a.1 + K i a.2 = b.1 + K i b.2 := h1'
    rw [h2, add_left_inj] at h1
    exact Prod.ext h1 h2
  · exact Prod.ext (sub_add_cancel x.1 (K i x.2)) rfl

theorem sum {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (K : ∀ i, Vt.X i →ₗ[R] V.X i)
    (hK : ∀ i μ, conn S i (i + 1) μ = V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ)) :
    (∀ i, InducesZero S i) ∧ IsIso (sumToTwisted S K hK) ∧
      ∀ J, (∀ i < J, Function.Injective (S.f i)) →
        (∀ i, J ≤ i →
          LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (conn S i (i + 1)) = ⊤) →
        ∀ i, Nonempty ((bgg S J).homology i ≅ (twisted (0 : Vt ⟶ V⟦(1 : ℤ)⟧)).homology i) := by
  have hiso := isIso_sumToTwisted S K hK
  refine ⟨fun i φ hφ => ⟨K i φ, by rw [hK, hφ, map_zero, sub_zero]⟩, hiso, fun J hinj hsurj i => ?_⟩
  obtain ⟨e⟩ := (verdict hinj hsurj).homology i
  exact ⟨e ≪≫ ((HomologicalComplex.homologyFunctor _ _ i).mapIso (asIso (sumToTwisted S K hK))).symm⟩

/-! ### The explicit cochain map (30) and Corollary 1 ([ArnoldHu2021], Theorem 7) -/

section Explicit

variable {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}

theorem represents_iff {C : CochainComplex (ModuleCat.{v} R) ℤ} {i : ℤ} {H : Submodule R (C.X i)} :
    Represents C i H ↔ C.Represents i H := by
  have hp : (ComplexShape.up ℤ).prev i = i - 1 := CochainComplex.prev ℤ i
  have hn : (ComplexShape.up ℤ).next i = i + 1 := CochainComplex.next ℤ i
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [hp, hn]; exact h1, by rw [hp]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [hp, hn] at h1; exact h1, by rw [hp] at h2; exact h2⟩

/-- The rows of `toData S` without connecting maps are the data of `S = 0`. -/
theorem sumData_toData (S : Vt ⟶ V⟦(1 : ℤ)⟧) :
    (toData S).sumData = toData (0 : Vt ⟶ V⟦(1 : ℤ)⟧) := by
  have h : (fun i j => (0 : Vt.X i →ₗ[R] V.X j)) = conn (0 : Vt ⟶ V⟦(1 : ℤ)⟧) := by
    funext i j
    by_cases hij : i + 1 = j <;> simp [conn, hij]
  unfold Feec.BGG.Data.sumData toData
  congr

variable {S : Vt ⟶ V⟦(1 : ℤ)⟧} {K : ∀ i, Vt.X i →ₗ[R] V.X i} {J : ℤ}
  {t : ∀ i j, V.X j →ₗ[R] Vt.X i}

theorem sumMap_eq (i : ℤ) (x : V.X i × Vt.X i) :
    sumMap S K t J i x = (toData S).bggProjMap J t i (x.1 + K i x.2, x.2) := by
  rcases lt_trichotomy i J with hi | rfl | hi
  · rw [Feec.BGG.Data.bggProjMap_of_lt hi]; simp [sumMap, hi]
  · rw [Feec.BGG.Data.bggProjMap_of_eq rfl]; simp [sumMap]; rfl
  · rw [Feec.BGG.Data.bggProjMap_of_gt hi, Feec.BGG.Data.kerProj_apply]
    simp only [sumMap, not_lt.2 hi.le, hi.ne', ↓reduceIte]
    refine Prod.ext rfl ?_
    have e : (toData S).dt (i - 1) i = (Vt.d (i - 1) i).hom := rfl
    have e' : (toData S).S i (i + 1) = conn S i (i + 1) := rfl
    simp only [e, e', map_add]
    abel

theorem quasiIso_eqToHom_comp {A B C : CochainComplex (ModuleCat.{v} R) ℤ} (e : A = B) (g : B ⟶ C)
    [QuasiIso g] : QuasiIso (eqToHom e ≫ g) := by
  subst e
  rwa [eqToHom_refl, Category.id_comp]

theorem explicit_aux
    (hK : ∀ i μ, conn S i (i + 1) μ = V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ))
    (h : (toData S).InjSurjWith J t) (G H : ∀ i, Submodule R (V.X i × Vt.X i))
    (hG : (toData S).Γ (J < ·) = G) (hH : (toData S).Δ (· < J) = H)
    (hs : ∀ i j, ∀ x ∈ G i, (twisted S).d i j x ∈ G j)
    (hs' : ∀ i j, ∀ x ∈ (fun i => (H i).comap (G i).subtype) i,
      (subcomplex (twisted S) G hs).d i j x ∈ (fun i => (H i).comap (G i).subtype) j) :
    ∃ κ : twisted (0 : Vt ⟶ V⟦(1 : ℤ)⟧) ⟶
        quotient (subcomplex (twisted S) G hs) (fun i => (H i).comap (G i).subtype) hs',
      (∀ i x, ∃ hx : sumMap S K t J i x ∈ G i,
        (κ.f i).hom x = Submodule.Quotient.mk ⟨_, hx⟩) ∧ QuasiIso κ ∧
      ∀ i (H' : Submodule R (V.X i)) (Ht' : Submodule R (Vt.X i)), Represents V i H' →
        Represents Vt i Ht' → Represents (quotient (subcomplex (twisted S) G hs)
          (fun i => (H i).comap (G i).subtype) hs') i ((H'.prod Ht').map (κ.f i).hom) := by
  subst hG hH
  have hK' : (toData S).IsNullHomotopy K := fun i _ hij μ => by
    obtain rfl : i + 1 = _ := hij
    exact hK i μ
  have e : (toData (0 : Vt ⟶ V⟦(1 : ℤ)⟧)).twistComplex = (toData S).sumComplex :=
    (congrArg Feec.BGG.Data.twistComplex (sumData_toData S)).symm
  let κ : twisted (0 : Vt ⟶ V⟦(1 : ℤ)⟧) ⟶ (toData S).bgg J :=
    eqToHom e ≫ (toData S).bggSumMap t hK' h
  have hκ (i : ℤ) : κ.f i = ((toData S).bggSumMap t hK' h).f i := by
    erw [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f]
    exact Category.id_comp _
  have : QuasiIso κ :=
    have := Feec.BGG.Data.quasiIso_bggSumMap h hK'
    quasiIso_eqToHom_comp e _
  refine ⟨κ, fun i x => ⟨sumMap_eq (S := S) (K := K) i x ▸ (toData S).bggProjMap_mem_Γ h i _, ?_⟩,
    this, fun i H' Ht' hH' hHt' => represents_iff.2 ?_⟩
  · rw [hκ]
    exact (Feec.BGG.Data.bggSumMap_apply h hK' i x).trans
      (congrArg Submodule.Quotient.mk (Subtype.ext (sumMap_eq i x).symm))
  · rw [hκ]
    exact Feec.BGG.Data.bgg_represents h hK' ⟨(represents_iff.1 hH').1, (represents_iff.1 hH').2⟩
      ⟨(represents_iff.1 hHt').1, (represents_iff.1 hHt').2⟩

/-- **The explicit cochain map (30) of Theorem 7 and Corollary 1**, from
`Feec.BGG.Data.bggSumMap`, `Feec.BGG.Data.quasiIso_bggSumMap` and `Feec.BGG.Data.bgg_represents`. -/
theorem explicit (S : Vt ⟶ V⟦(1 : ℤ)⟧) (K : ∀ i, Vt.X i →ₗ[R] V.X i)
    (hK : ∀ i μ, conn S i (i + 1) μ = V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ))
    (J : ℤ) (t : ∀ i j, V.X j →ₗ[R] Vt.X i) (hinj : ∀ i ≤ J, Function.Injective (S.f i))
    (ht : ∀ i, J ≤ i → ∀ v, conn S i (i + 1) (t i (i + 1) v) = v) :
    ∃ κ : twisted (0 : Vt ⟶ V⟦(1 : ℤ)⟧) ⟶ bgg S J,
      (∀ i x, ∃ hx : sumMap S K t J i x ∈ Γ S J i,
        (κ.f i).hom x = Submodule.Quotient.mk ⟨_, hx⟩) ∧ QuasiIso κ ∧
      ∀ i (H : Submodule R (V.X i)) (Ht : Submodule R (Vt.X i)), Represents V i H →
        Represents Vt i Ht → Represents (bgg S J) i ((H.prod Ht).map (κ.f i).hom) := by
  have h : (toData S).InjSurjWith J t :=
    ⟨fun i hi => by
      change Function.Injective (conn S i (i + 1))
      rw [conn_succ]; exact hinj i hi,
     fun i j hij hi v => by subst hij; exact ht i hi v⟩
  exact explicit_aux hK h _ _ (Γ_toData S J) (Δ_toData S J) _ _

end Explicit

/-! ### Bounded Hilbert complexes -/

section Hilbert

variable {𝕜 : Type u} [RCLike 𝕜] {H Ht : ℤ → Type v}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace 𝕜 (H i)]
  [∀ i, NormedAddCommGroup (Ht i)] [∀ i, InnerProductSpace 𝕜 (Ht i)]
  {d : ∀ i, H i →L[𝕜] H (i + 1)} {hd : ∀ i x, d (i + 1) (d i x) = 0}
  {dt : ∀ i, Ht i →L[𝕜] Ht (i + 1)} {hdt : ∀ i x, dt (i + 1) (dt i x) = 0}
  (s : ∀ i, Ht i →L[𝕜] H (i + 1)) (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x))

theorem ofBounded_d_succ (i : ℤ) : ((ofBounded d hd).d i (i + 1)).hom = (d i : H i →ₗ[𝕜] _) := by
  simp

theorem continuous_ofBounded_d (i j : ℤ) : Continuous ((ofBounded d hd).d i j).hom := by
  by_cases h : i + 1 = j
  · subst h
    rw [ofBounded_d_succ]; exact (d i).continuous
  · rw [(ofBounded d hd).shape i j h]; exact continuous_const

theorem conn_ofBoundedHom (i : ℤ) :
    conn (ofBoundedHom (hd := hd) (hdt := hdt) s hs) i (i + 1) = (s i : Ht i →ₗ[𝕜] H (i + 1)) :=
  conn_succ _ i

/-- The bounded BGG data of `Feec` of the Hilbert rows. -/
def boundedData : Feec.BGG.BoundedData 𝕜 (ComplexShape.up ℤ) H Ht where
  toData := toData (ofBoundedHom (hd := hd) (hdt := hdt) s hs)
  continuous_d := continuous_ofBounded_d
  continuous_dt := continuous_ofBounded_d
  continuous_S i j := by
    by_cases h : i + 1 = j
    · subst h
      change Continuous (conn (ofBoundedHom (hd := hd) (hdt := hdt) s hs) i (i + 1))
      rw [conn_ofBoundedHom]; exact (s i).continuous
    · change Continuous (conn (ofBoundedHom (hd := hd) (hdt := hdt) s hs) i j)
      simp only [conn, h, dite_false]; exact continuous_const

theorem eliminates_boundedData {J : ℤ} (hinj : ∀ i < J, ∃ C, AntilipschitzWith C (s i))
    (hsurj : ∀ i, J ≤ i → LinearMap.range (d i : H i →ₗ[𝕜] H (i + 1)) ⊔
      LinearMap.range (s i : Ht i →ₗ[𝕜] H (i + 1)) = ⊤) :
    (toData (ofBoundedHom (hd := hd) (hdt := hdt) s hs)).Eliminates (J < ·) (· < J) :=
  eliminates_toData _ (fun i hi => (hinj i hi).choose_spec.injective) fun i hi => by
    rw [conn_ofBoundedHom, ofBounded_d_succ]; exact hsurj i hi

theorem closedRange [∀ i, CompleteSpace (H i)] [∀ i, CompleteSpace (Ht i)] (J : ℤ)
    (hinj : ∀ i < J, ∃ C, AntilipschitzWith C (s i)) (i : ℤ) :
    let S := ofBoundedHom (hd := hd) (hdt := hdt) s hs
    IsClosed (Γ S J i : Set (H i × Ht i)) ∧ IsClosed (Δ S J i : Set (H i × Ht i)) := by
  intro S
  set D := boundedData (hd := hd) (hdt := hdt) s hs
  have hΓ : D.Γ (J < ·) = Γ S J := Γ_toData S J
  have hΔ' : D.Δ (· < J) = Δ S J := Δ_toData S J
  have hS : ∀ i < J, ∃ C, AntilipschitzWith C (D.S i (i + 1)) := fun i hi => by
    obtain ⟨C, hC⟩ := hinj i hi
    refine ⟨C, ?_⟩
    change AntilipschitzWith C (conn S i (i + 1))
    rw [conn_ofBoundedHom]; exact hC
  refine ⟨?_, ?_⟩
  · have := D.isClosed_Γ (J < ·) i
    rwa [hΓ] at this
  · have := D.isClosed_bgg_Δ hS i
    rwa [hΔ'] at this

/-- `Γ / Δ` on the `ℓ²` products as a subquotient of the twisted complex (`Feec`). -/
def subquot (J : ℤ)
    (hle : ∀ i, Δ (ofBoundedHom (hd := hd) (hdt := hdt) s hs) J i ≤
      Γ (ofBoundedHom (hd := hd) (hdt := hdt) s hs) J i)
    (hΓ : ∀ i, IsClosed (Γ (ofBoundedHom (hd := hd) (hdt := hdt) s hs) J i : Set (H i × Ht i))) :
    Feec.HilbertComplex.Subquotient 𝕜 (ComplexShape.up ℤ) fun i => WithLp 2 (H i × Ht i) where
  d := (boundedData (hd := hd) (hdt := hdt) s hs).twistL
  shape _ _ h := (boundedData (hd := hd) (hdt := hdt) s hs).twistL_eq_zero h
  d_comp_d := (boundedData (hd := hd) (hdt := hdt) s hs).twistL_twistL
  Γ := ΓL (hd := hd) (hdt := hdt) s hs J
  Δ := ΔL (hd := hd) (hdt := hdt) s hs J
  Δ_le_Γ i _ hx := hle i hx
  isClosed_Γ i := (hΓ i).preimage (WithLp.prodContinuousLinearEquiv 2 𝕜 (H i) (Ht i)).continuous
  d_mem_Γ i j _ hx := twist_mem_Γ _ J i j hx
  d_mem_Δ i j _ hx := twist_mem_Δ _ J i j hx

/-- **The BGG complex with the quotient norm is a bounded Hilbert complex with closed ranges**
(`FEEC.bggHilbert`), from `Feec.HilbertComplex.Subquotient.toQuotEquiv`, `quotD_toQuot`,
`cohomologyEquiv` and `Feec.HilbertComplex.closedRangeAt_of_finiteDimensional_cohomology`. -/
theorem hilbert [∀ i, CompleteSpace (H i)] [∀ i, CompleteSpace (Ht i)] (J : ℤ)
    (hinj : ∀ i < J, ∃ C, AntilipschitzWith C (s i))
    (hsurj : ∀ i, J ≤ i → LinearMap.range (d i : H i →ₗ[𝕜] H (i + 1)) ⊔
      LinearMap.range (s i : Ht i →ₗ[𝕜] H (i + 1)) = ⊤) :
    let S := ofBoundedHom (hd := hd) (hdt := hdt) s hs
    let ΓL := ΓL (hd := hd) (hdt := hdt) s hs J
    let ΔL := ΔL (hd := hd) (hdt := hdt) s hs J
    let Q := QuotL (hd := hd) (hdt := hdt) s hs J
    (∀ i, IsClosed (Γ S J i : Set (H i × Ht i)) ∧ IsClosed (Δ S J i : Set (H i × Ht i))) ∧
      (∀ i, ∃ e : ↥(ΓL i ⊓ (ΔL i)ᗮ) ≃ₗᵢ[𝕜] Q i, ∀ y, e y = Submodule.Quotient.mk ⟨y, y.2.1⟩) ∧
      ∃ D : ∀ i, Q i →L[𝕜] Q (i + 1),
        (∀ i (x : ΓL i) (x' : ΓL (i + 1)), (x' : WithLp 2 (H (i + 1) × Ht (i + 1))).ofLp =
          twist S i (i + 1) (x : WithLp 2 (H i × Ht i)).ofLp →
            D i (Submodule.Quotient.mk x) = Submodule.Quotient.mk x') ∧
        ∀ i, [FiniteDimensional 𝕜 ((ofBounded d hd).homology (i + 1))] →
          [FiniteDimensional 𝕜 ((ofBounded dt hdt).homology (i + 1))] →
          IsClosed (Set.range (D i)) := by
  intro S ΓL' ΔL' Q
  have hel := eliminates_boundedData (hd := hd) (hdt := hdt) s hs hinj hsurj
  have hcl := closedRange (hd := hd) (hdt := hdt) s hs J hinj
  have hle : ∀ i, Δ S J i ≤ Γ S J i := fun i => by
    have := hel.Δ_le_Γ i
    rwa [Γ_toData, Δ_toData] at this
  let q := subquot s hs J hle fun i => (hcl i).1
  have hΔ : ∀ i, IsClosed (q.Δ i : Set (WithLp 2 (H i × Ht i))) := fun i =>
    (hcl i).2.preimage (WithLp.prodContinuousLinearEquiv 2 𝕜 (H i) (Ht i)).continuous
  refine ⟨hcl, fun i => ⟨Feec.HilbertComplex.Subquotient.toQuotEquiv hΔ i, fun y => rfl⟩,
    fun i => q.quotD i (i + 1), fun i x x' hx => ?_, fun i _ _ => ?_⟩
  · refine (q.quotD_mk i (i + 1) x).trans (congrArg _ (Subtype.ext ?_))
    exact WithLp.ofLp_injective 2 hx.symm
  · -- `Γ / Δ` with the quotient norm is the BGG complex as a complex of modules
    let f : ∀ j, q.Γ j ≃ₗ[𝕜] ↥(Γ S J j) := fun j =>
      { toFun x := ⟨(x : WithLp 2 (H j × Ht j)).ofLp, x.2⟩
        invFun x := ⟨WithLp.toLp 2 (x : H j × Ht j), x.2⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl
        left_inv _ := rfl
        right_inv _ := rfl }
    let eX : ∀ j, q.QuotSpace j ≃ₗ[𝕜] (bgg S J).X j := fun j =>
      Submodule.Quotient.equiv _ ((Δ S J j).comap (Γ S J j).subtype) (f j) <|
        Submodule.ext fun x => ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun h =>
          ⟨(f j).symm x, h, (f j).apply_symm_apply x⟩⟩
    let iso : q.quotModuleCat ≅ bgg S J :=
      HomologicalComplex.Hom.isoOfComponents (fun j => (eX j).toModuleIso) fun _ _ _ => by
        ext x
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rfl
    have hfd := (finiteDimensional_and_finrank_le (S := S) (fun i hi =>
      (hinj i hi).choose_spec.injective) (fun i hi => by
        rw [conn_ofBoundedHom, ofBounded_d_succ]; exact hsurj i hi) (i + 1)).1
    have : FiniteDimensional 𝕜
        ((HomologicalComplex.homologyFunctor (ModuleCat 𝕜) _ (i + 1)).obj (bgg S J)) := hfd
    have : ∀ j, CompleteSpace (WithLp 2 (H j × Ht j)) := fun _ => inferInstance
    have : ∀ j, CompleteSpace (q.space j) := fun j =>
      ((q.isClosed_Γ j).inter (q.Δ j).isClosed_orthogonal).completeSpace_coe
    have : FiniteDimensional 𝕜 (q.quotModuleCat.homology (i + 1)) :=
      ((HomologicalComplex.homologyFunctor _ _ (i + 1)).mapIso iso).toLinearEquiv.symm
        |>.finiteDimensional
    have : FiniteDimensional 𝕜 (q.complex.cohomology (i + 1)) :=
      (Feec.HilbertComplex.Subquotient.cohomologyEquiv hΔ (i + 1)).symm.finiteDimensional
    have hc := Feec.HilbertComplex.closedRangeAt_of_finiteDimensional_cohomology q.complex (i + 1)
    rw [Feec.HilbertComplex.ClosedRangeAt,
      Feec.HilbertComplex.boundaries_eq (c := ComplexShape.up ℤ) q.complex rfl] at hc
    set e := Feec.HilbertComplex.Subquotient.toQuotEquiv hΔ (i + 1)
    have hr : Set.range (q.quotD i (i + 1)) =
        e '' (LinearMap.range (q.complex.d i (i + 1)).toFun : Set _) := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        obtain ⟨y, rfl⟩ := (Feec.HilbertComplex.Subquotient.toQuotEquiv hΔ i).surjective w
        exact ⟨q.spaceD i (i + 1) y, ⟨⟨y, trivial⟩, rfl⟩,
          (Feec.HilbertComplex.Subquotient.quotD_toQuot hΔ i (i + 1) y).symm⟩
      · rintro ⟨_, ⟨⟨y, _⟩, rfl⟩, rfl⟩
        exact ⟨q.toQuot i y, Feec.HilbertComplex.Subquotient.quotD_toQuot hΔ i (i + 1) y⟩
    change IsClosed (Set.range (q.quotD i (i + 1)))
    rw [hr]
    exact e.toHomeomorph.isClosedMap _ hc

/-- The challenge's Moore–Penrose inverse is that of `Feec`. -/
theorem moorePenrose_eq {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (f : E →L[𝕜] F) : moorePenrose f = f.moorePenrose := rfl

theorem bgg_toData_aux {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) (G H : ∀ i, Submodule R (V.X i × Vt.X i))
    (hG : (toData S).Γ (J < ·) = G) (hH : (toData S).Δ (· < J) = H)
    (hs : ∀ i j, ∀ x ∈ G i, (twisted S).d i j x ∈ G j)
    (hs' : ∀ i j, ∀ x ∈ (fun i => (H i).comap (G i).subtype) i,
      (subcomplex (twisted S) G hs).d i j x ∈ (fun i => (H i).comap (G i).subtype) j) :
    (toData S).bgg J = quotient (subcomplex (twisted S) G hs)
      (fun i => (H i).comap (G i).subtype) hs' := by
  subst hG hH
  rfl

/-- The BGG complex of the challenge is that of `Feec`. -/
theorem bgg_toData {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) : (toData S).bgg J = bgg S J :=
  bgg_toData_aux S J _ _ (Γ_toData S J) (Δ_toData S J) _ _

theorem SL_boundedData (i : ℤ) : (boundedData (hd := hd) (hdt := hdt) s hs).SL i (i + 1) = s i :=
  ContinuousLinearMap.ext fun φ => by
    change conn (ofBoundedHom (hd := hd) (hdt := hdt) s hs) i (i + 1) φ = s i φ
    rw [conn_ofBoundedHom]; rfl

theorem Υ_boundedData (J i : ℤ) :
    (boundedData (hd := hd) (hdt := hdt) s hs).Υ J i = Υ (hd := hd) (hdt := hdt) s hs J i := by
  unfold Feec.BGG.BoundedData.Υ Υ
  split_ifs
  · rfl
  · rw [SL_boundedData]

variable [∀ i, CompleteSpace (H i)] [∀ i, CompleteSpace (Ht i)]

/-- **The orthogonal form of (30) and Corollary 1** (the second clause of `FEEC.bggHilbert`), from
`Feec.BGG.BoundedData.quasiIso_orthSumMap`, `Feec.BGG.BoundedData.isIso_toOrth` and
`Feec.BGG.BoundedData.orth_represents`. -/
theorem orthogonal (d : ∀ i, H i →L[𝕜] H (i + 1)) (hd : ∀ i x, d (i + 1) (d i x) = 0)
    (dt : ∀ i, Ht i →L[𝕜] Ht (i + 1)) (hdt : ∀ i x, dt (i + 1) (dt i x) = 0)
    (s : ∀ i, Ht i →L[𝕜] H (i + 1)) (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x))
    (K : ∀ i, Ht i →ₗ[𝕜] H i) (hK : ∀ i μ, s i μ = d i (K i μ) - K (i + 1) (dt i μ))
    (J : ℤ) (hinj : ∀ i ≤ J, Function.Injective (s i))
    (hsurj : ∀ i, J ≤ i → Function.Surjective (s i))
    (hR : ∀ i < J, IsClosed (Set.range (s i))) :
    let S := ofBoundedHom (hd := hd) (hdt := hdt) s hs
    let P := fun i => (rangeS S i : Submodule 𝕜 (H i))ᗮ.starProjection
    ∃ (Y : CochainComplex (ModuleCat.{v} 𝕜) ℤ) (e : ∀ i, Y.X i ≃ₗ[𝕜] Υ (hd := hd) (hdt := hdt) s hs J i)
      (κ : twisted (0 : ofBounded dt hdt ⟶ (ofBounded d hd)⟦(1 : ℤ)⟧) ⟶ Y),
      (∀ i < J, ∀ y, (e (i + 1) (Y.d i (i + 1) y) : H (i + 1) × Ht (i + 1)) =
        (P (i + 1) (d i (e i y : H i × Ht i).1), 0)) ∧
      (∀ y, (e (J + 1) (Y.d J (J + 1) y) : H (J + 1) × Ht (J + 1)) =
        (0, dt J (moorePenrose (s J) (d J (e J y : H J × Ht J).1)))) ∧
      (∀ i, J < i → ∀ y, (e (i + 1) (Y.d i (i + 1) y) : H (i + 1) × Ht (i + 1)) =
        (0, dt i (e i y : H i × Ht i).2)) ∧
      (∀ i ≤ J, ∀ x : H i × Ht i, (e i ((κ.f i).hom x) : H i × Ht i) = (P i (x.1 + K i x.2), 0)) ∧
      (∀ i, J ≤ i → ∀ x : H (i + 1) × Ht (i + 1),
        (e (i + 1) ((κ.f (i + 1)).hom x) : H (i + 1) × Ht (i + 1)) =
          (0, (s (i + 1)).ker.starProjection (dt i (moorePenrose (s i) x.1) +
            (x.2 + dt i (moorePenrose (s i) (K (i + 1) x.2)))))) ∧
      QuasiIso κ ∧ Nonempty (Y ≅ bgg S J) ∧
      ∀ i (A : Submodule 𝕜 (H i)) (At : Submodule 𝕜 (Ht i)),
        Represents (ofBounded d hd) i A → Represents (ofBounded dt hdt) i At →
          Represents Y i ((A.prod At).map (κ.f i).hom) := by
  intro S P
  set D := boundedData (hd := hd) (hdt := hdt) s hs
  have hS (i : ℤ) (φ : Ht i) : D.S i (i + 1) φ = s i φ := by
    change conn S i (i + 1) φ = s i φ
    rw [conn_ofBoundedHom]; rfl
  have hdD (i : ℤ) (x : H i) : D.d i (i + 1) x = d i x := by
    change ((ofBounded d hd).d i (i + 1)).hom x = d i x
    rw [ofBounded_d_succ]; rfl
  have hdtD (i : ℤ) (x : Ht i) : D.dt i (i + 1) x = dt i x := by
    change ((ofBounded dt hdt).d i (i + 1)).hom x = dt i x
    rw [ofBounded_d_succ]; rfl
  have hmp (i : ℤ) (y : H (i + 1)) : D.mpInv i (i + 1) y = moorePenrose (s i) y := by
    change (D.SL i (i + 1)).moorePenrose y = _
    rw [SL_boundedData, moorePenrose_eq]
  have hinj' : ∀ i ≤ J, Function.Injective (D.S i (i + 1)) := fun i hi a b hab =>
    hinj i hi (by rwa [hS, hS] at hab)
  have hsurj' : ∀ i, J ≤ i → Function.Surjective (D.S i (i + 1)) := fun i hi y => by
    obtain ⟨φ, rfl⟩ := hsurj i hi y
    exact ⟨φ, hS i φ⟩
  have hK' : D.IsNullHomotopy K := by
    rintro i _ rfl μ
    rw [hS, hdD, hdtD]
    exact hK i μ
  have hR' : ∀ i ≤ J, IsClosed ((D.SL (i - 1) i).range : Set (H i)) := fun i hi => by
    obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by ring⟩
    rw [add_sub_cancel_right, SL_boundedData, LinearMap.coe_range]
    exact hR a (by omega)
  have hJb : Function.Bijective (D.S J (J + 1)) := ⟨hinj' J le_rfl, hsurj' J le_rfl⟩
  have e₀ : twisted (0 : ofBounded dt hdt ⟶ (ofBounded d hd)⟦(1 : ℤ)⟧) = D.sumComplex :=
    (congrArg Feec.BGG.Data.twistComplex (sumData_toData S)).symm
  let κ := eqToHom e₀ ≫ D.orthSumMap J hinj' hsurj' hK'
  have hκ (i : ℤ) : κ.f i = (D.orthSumMap J hinj' hsurj' hK').f i := by
    erw [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f]
    exact Category.id_comp _
  refine ⟨D.orthComplex J hJb, fun i => LinearEquiv.ofEq _ _ (Υ_boundedData s hs J i), κ,
    fun i hi y => ?_, fun y => ?_, fun i hi y => ?_, fun i hi x => ?_, fun i hi x => ?_, ?_, ?_,
    fun i A At hA hAt => ?_⟩
  · refine (Feec.BGG.BoundedData.coe_orthComplex_d hJb i y).trans ?_
    rw [Feec.BGG.BoundedData.orthDMap_of_lt hi, hdD]
    rfl
  · refine (Feec.BGG.BoundedData.coe_orthComplex_d hJb J y).trans ?_
    rw [Feec.BGG.BoundedData.orthDMap_of_eq, hdD, hmp, hdtD]
    rfl
  · refine (Feec.BGG.BoundedData.coe_orthComplex_d hJb i y).trans ?_
    rw [Feec.BGG.BoundedData.orthDMap_of_gt hi, hdtD]
    rfl
  · change Subtype.val ((κ.f i).hom x) = _
    rw [hκ]
    exact Feec.BGG.BoundedData.orthSumMap_of_le hK' hinj' hsurj' hi x
  · change Subtype.val ((κ.f (i + 1)).hom x) = _
    rw [hκ]
    refine (Feec.BGG.BoundedData.orthSumMap_of_gt hK' hinj' hsurj' (i := i + 1) (by omega) x).trans ?_
    rw [Feec.BGG.Data.dt_t_prev rfl, Feec.BGG.Data.dt_t_prev rfl, hmp, hmp, hdtD, hdtD,
      SL_boundedData]
  · have := Feec.BGG.BoundedData.quasiIso_orthSumMap hK' hinj' hsurj' hR'
    exact quasiIso_eqToHom_comp e₀ _
  · have := Feec.BGG.BoundedData.isIso_toOrth hJb hR'
    exact ⟨(asIso (D.toOrth J hJb)).symm ≪≫ eqToIso (bgg_toData S J)⟩
  · refine represents_iff.2 ?_
    rw [hκ]
    exact Feec.BGG.BoundedData.orth_represents hK' hinj' hsurj' hR'
      ⟨(represents_iff.1 hA).1, (represents_iff.1 hA).2⟩
      ⟨(represents_iff.1 hAt).1, (represents_iff.1 hAt).2⟩

end Hilbert

end FEEC.BGG
