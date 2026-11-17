module

public import Solution.Defs
public import Feec.HilbertComplex.BGG.Analytic
public import Feec.HilbertComplex.BGG.Connecting

/-!
# The bridge from the BGG complexes of the challenge to `Feec`

A stacked diagram `S : Ṽ ⟶ V⟦1⟧` of the challenge is `Feec` BGG data on `ComplexShape.up ℤ`
(`BGG.toData`: the differentials of the rows and the connecting maps `BGG.conn S`). Its twisted
complex is that of `Feec` (`BGG.twistComplex_toData`, by definition), the subcomplexes `Γ` and
`Δ` at `J` are the eliminations `Feec.BGG.Data.Γ (J < ·)` and `Feec.BGG.Data.Δ (· < J)` of the
BGG complex of `Feec` (`BGG.Γ_toData`, `BGG.Δ_toData`), and the injectivity/surjectivity
hypothesis is `Feec.BGG.Data.InjSurj J` (`BGG.injSurj_toData`). The quasi-isomorphisms of
`Feec.BGG.Data.quasiIso_Γ` and `Feec.BGG.Data.quasiIso_derived` give the verdict
(`BGG.verdict`); with the long exact sequence of the rows, the dimension bound over a field
(`BGG.finiteDimensional_and_finrank_le`); for bounded Hilbert rows, the bounded Hilbert complex
with closed ranges (`BGG.hilbert`).

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

theorem conn_succ (i : ℤ) : conn S i (i + 1) = (S.f i).hom := by
  simp [conn]

/-- `0 → V → T → Ṽ → 0`, `σ ↦ (σ, 0)` and `(σ, φ) ↦ φ`. -/
def rows : ShortComplex (CochainComplex (ModuleCat.{v} R) ℤ) where
  X₁ := V
  X₂ := twisted S
  X₃ := Vt
  f := { f i := ModuleCat.ofHom (LinearMap.inl R _ _)
         comm' i j _ := ModuleCat.hom_ext (LinearMap.ext fun σ => by
           change twist S i j (σ, 0) = (V.d i j σ, 0)
           simp [twist]) }
  g := { f i := ModuleCat.ofHom (LinearMap.snd R _ _)
         comm' _ _ _ := rfl }
  zero := by ext; rfl

/-- **The BGG verdict at `J`.** Its content, under the hypotheses of `FEEC.bggCohomology`, is
the two quasi-isomorphisms `quasiIso_ι` and `quasiIso_π`; `homology` follows from them,
`shortExact` holds for every `S` and `J`, and `acyclic` follows from `shortExact` and
`homology`. They are stated for the reader. -/
structure VerdictFull (J : ℤ) : Prop where
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
    VerdictFull S J := by
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

end Hilbert

end FEEC.BGG
