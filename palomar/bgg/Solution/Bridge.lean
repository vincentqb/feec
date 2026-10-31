module

public import Solution.Defs
public import Feec.HilbertComplex.BGG.Analytic
public import Feec.HilbertComplex.BGG.Connecting
public import Feec.HilbertComplex.BGG.SumComplex

/-!
# The bridge from the challenge to `Feec`

A stacked diagram `S : Ṽ ⟶ V⟦1⟧` of the challenge is `Feec` BGG data on `ComplexShape.up ℤ`
(`BGG.toData`: the differentials of the rows and the connecting maps `BGG.conn S`). Its twisted
complex is that of `Feec` (`BGG.twistComplex_toData`, by definition), the subcomplexes `Γ` and
`Δ` at `J` are the eliminations `Feec.BGG.Data.Γ (J < ·)` and `Feec.BGG.Data.Δ (· < J)` of the
BGG complex of `Feec` (`BGG.Γ_toData`, `BGG.Δ_toData`), and the injectivity/surjectivity
hypothesis is `Feec.BGG.Data.InjSurj J` (`BGG.injSurj_toData`). The quasi-isomorphisms of
`Feec.BGG.Data.quasiIso_Γ` and `Feec.BGG.Data.quasiIso_derived` give the verdict
(`BGG.verdict`); with the long exact sequence of the rows, the dimension bound over a field
(`BGG.finiteDimensional_and_finrank_le`).

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

end Identification

/-! ### The sum complex ([ArnoldHu2021], Theorem 7) -/

theorem sum {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (K : ∀ i, Vt.X i →ₗ[R] V.X i)
    (hK : ∀ i μ, conn S i (i + 1) μ = V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ)) :
    (∀ i, InducesZero S i) ∧ IsIso (sumToTwisted S K hK) ∧
      ∀ J, (∀ i < J, Function.Injective (S.f i)) →
        (∀ i, J ≤ i →
          LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (conn S i (i + 1)) = ⊤) →
        ∀ i, Nonempty ((bgg S J).homology i ≅ (twisted (0 : Vt ⟶ V⟦(1 : ℤ)⟧)).homology i) := by
  have hiso : IsIso (sumToTwisted S K hK) := by
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

theorem isIso_sumToTwisted (S : Vt ⟶ V⟦(1 : ℤ)⟧) (K : ∀ i, Vt.X i →ₗ[R] V.X i)
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
    sumMap S K t J i x = (toData S).bggLift J t i (x.1 + K i x.2, x.2) := by
  rcases lt_trichotomy i J with hi | rfl | hi
  · rw [Feec.BGG.Data.bggLift_of_lt hi]; simp [sumMap, hi]
  · rw [Feec.BGG.Data.bggLift_of_eq rfl]; simp [sumMap]; rfl
  · rw [Feec.BGG.Data.bggLift_of_gt hi, Feec.BGG.Data.kerProj_apply]
    simp only [sumMap, not_lt.2 hi.le, hi.ne', ↓reduceIte]
    refine Prod.ext rfl ?_
    have e : (toData S).dt (i - 1) i = (Vt.d (i - 1) i).hom := rfl
    have e' : (toData S).S i (i + 1) = conn S i (i + 1) := rfl
    simp only [e, e', map_add]
    abel

theorem explicit_aux
    (hK : ∀ i μ, conn S i (i + 1) μ = V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ))
    (h : (toData S).IsRightInverse J t) (G H : ∀ i, Submodule R (V.X i × Vt.X i))
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
  let r : twisted S ⟶ (toData S).bgg J := (toData S).bggProj t h ≫ (toData S).derivedπ _ _
  have : QuasiIso r := Feec.BGG.Data.quasiIso_of_Γι_comp h.injSurj.eliminates
    ((toData S).Γι_bggProj_derivedπ h)
  have := isIso_sumToTwisted S K hK
  have hκ : QuasiIso (sumToTwisted S K hK ≫ r) := inferInstance
  refine ⟨sumToTwisted S K hK ≫ r,
    fun i x => ⟨sumMap_eq (S := S) (K := K) i x ▸ (toData S).bggLift_mem_Γ h i _, ?_⟩,
    hκ, fun i H' Ht' hH' hHt' => represents_iff.2 ?_⟩
  · exact congrArg Submodule.Quotient.mk (Subtype.ext (sumMap_eq i x).symm)
  · have hs0 := (toData S).represents_sumComplex (i := i) (H := H') (Ht := Ht')
      ⟨(represents_iff.1 hH').1, (represents_iff.1 hH').2⟩
      ⟨(represents_iff.1 hHt').1, (represents_iff.1 hHt').2⟩
    change (toData S).sumData.twistComplex.Represents i _ at hs0
    rw [sumData_toData] at hs0
    exact hs0.map (sumToTwisted S K hK ≫ r)

/-- **The explicit cochain map (30) of Theorem 7 and Corollary 1**, from `Feec.BGG.Data.bggProj`,
`Feec.BGG.Data.quasiIso_of_Γι_comp` and `HomologicalComplex.Represents.map`. -/
theorem explicit (S : Vt ⟶ V⟦(1 : ℤ)⟧) (K : ∀ i, Vt.X i →ₗ[R] V.X i)
    (hK : ∀ i μ, conn S i (i + 1) μ = V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ))
    (J : ℤ) (t : ∀ i j, V.X j →ₗ[R] Vt.X i) (hinj : ∀ i ≤ J, Function.Injective (S.f i))
    (ht : ∀ i, J ≤ i → ∀ v, conn S i (i + 1) (t i (i + 1) v) = v) :
    ∃ κ : twisted (0 : Vt ⟶ V⟦(1 : ℤ)⟧) ⟶ bgg S J,
      (∀ i x, ∃ hx : sumMap S K t J i x ∈ Γ S J i,
        (κ.f i).hom x = Submodule.Quotient.mk ⟨_, hx⟩) ∧ QuasiIso κ ∧
      ∀ i (H : Submodule R (V.X i)) (Ht : Submodule R (Vt.X i)), Represents V i H →
        Represents Vt i Ht → Represents (bgg S J) i ((H.prod Ht).map (κ.f i).hom) := by
  have h : (toData S).IsRightInverse J t :=
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

theorem closedRange [∀ i, CompleteSpace (H i)] [∀ i, CompleteSpace (Ht i)] (J : ℤ)
    (hinj : ∀ i < J, ∃ C, AntilipschitzWith C (s i))
    (hsurj : ∀ i, J ≤ i → LinearMap.range (d i : H i →ₗ[𝕜] H (i + 1)) ⊔
      LinearMap.range (s i : Ht i →ₗ[𝕜] H (i + 1)) = ⊤) (i : ℤ) :
    let S := ofBoundedHom (hd := hd) (hdt := hdt) s hs
    IsClosed (Γ S J i : Set (H i × Ht i)) ∧ IsClosed (Δ S J i : Set (H i × Ht i)) ∧
      ([FiniteDimensional 𝕜 ((ofBounded d hd).homology i)] →
        [FiniteDimensional 𝕜 ((ofBounded dt hdt).homology i)] →
        IsClosed ((Δ S J i ⊔ (Γ S J (i - 1)).map (twist S (i - 1) i) :
          Submodule 𝕜 _) : Set (H i × Ht i))) := by
  intro S
  set D := boundedData (hd := hd) (hdt := hdt) s hs
  have hΓ : D.Γ (J < ·) = Γ S J := Γ_toData S J
  have hΔ' : D.Δ (· < J) = Δ S J := Δ_toData S J
  have hS : ∀ i < J, ∃ C, AntilipschitzWith C (D.S i (i + 1)) := fun i hi => by
    obtain ⟨C, hC⟩ := hinj i hi
    refine ⟨C, ?_⟩
    change AntilipschitzWith C (conn S i (i + 1))
    rw [conn_ofBoundedHom]; exact hC
  have hΔ := D.isClosed_bgg_Δ hS
  refine ⟨?_, ?_, ?_⟩
  · have := D.isClosed_Γ (J < ·) i
    rwa [hΓ] at this
  · have := hΔ i
    rwa [hΔ'] at this
  · intro hV hVt
    have hel : D.Eliminates (J < ·) (· < J) := eliminates_toData S
      (fun i hi => (hinj i hi).choose_spec.injective) fun i hi => by
        rw [conn_ofBoundedHom, ofBounded_d_succ]; exact hsurj i hi
    have : FiniteDimensional 𝕜 (D.rowTop.homology i) := hV
    have : FiniteDimensional 𝕜 (D.rowBot.homology i) := hVt
    have : FiniteDimensional 𝕜 (D.rowTopComplex.cohomology i) :=
      (D.rowTopCohomologyEquiv i).symm.finiteDimensional
    have : FiniteDimensional 𝕜 (D.rowBotComplex.cohomology i) :=
      (D.rowBotCohomologyEquiv i).symm.finiteDimensional
    have := D.isClosed_Δ_sup_map_twist hΔ hel i
    rw [hΓ, hΔ', CochainComplex.prev] at this
    exact this

end Hilbert

end FEEC.BGG
