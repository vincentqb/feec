module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.HilbertComplex.BGG.DomainData

/-!
# Discrete BGG complexes: conforming families of the derived complex

**Discrete BGG data** are stacked conforming families (`Feec.BGG.BoundedData.StackedFamily`):
conforming families `Vₕ`, `Ṽₕ` of the two rows of BGG data along one filter, linked by the
connecting maps, `S Ṽₕⁱ ⊆ Vₕʲ`, whose cochain projections commute with them, `πₕ S = S π̃ₕ` (the
discrete BGG diagrams of [BonizzoniHuKanschatSap2024]). Then `πₕ × π̃ₕ` commutes with the twisted
differential and keeps the eliminations `Γ E`, `Δ F` and the closure of `Δ F`, so

* the discrete derived spaces `Υₕⁱ = P_{(Δⁱ)ᗮ} (Γⁱ ∩ (Vₕⁱ × Ṽₕⁱ))` (`derivedSubcomplex`, the range
  of `derivedπ`) form a finite-dimensional subcomplex of the derived Hilbert complex
  `Υⁱ = Γⁱ ⊖ Δⁱ` (`BoundedData.derivedComplex`), with the cochain projection
  `y ↦ P_{(Δⁱ)ᗮ} (πₕ × π̃ₕ) y` (`derivedCochainProjection`), bounded by `max C C̃`, and the
  approximation property of the rows passes to them: **the discrete derived complexes form a
  conforming family of the derived complex** (`StackedFamily.derived`);
* hence **the FEEC theorem holds for discrete BGG complexes** (`StackedFamily.feecVerdict`):
  when the exact part is closed, the elimination hypotheses hold and the rows have
  finite-dimensional cohomology, the derived complex has closed range
  (`BoundedData.derivedComplex_closedRangeAt`), so the static FEEC theorem holds in every degree,
  and the conclusions of `ConformingFamily.feec` hold for the derived complex.

For two Hilbert complexes linked by bounded connecting maps (`Feec.BGG.HilbertData`), stacked
conforming families in `L²` (`HilbertData.StackedFamily`) give conforming families of the domain
complexes in the graph norms (`ConformingFamily.domain`: `‖πₕ v‖_V ≤ C ‖v‖_V` since
`d πₕ = πₕ d`), so stacked families of the bounded data `HilbertData.domainData`
(`HilbertData.StackedFamily.toDomain`) and a conforming family of the derived complex of the
domain complexes; the discrete twisted complexes `Vₕ × Ṽₕ` are moreover a conforming family of
the `L²` twisted complex (`HilbertData.StackedFamily.twist`). With the analytic BGG theorem
(`HilbertData.derivedVerdict`, `HilbertData.bggVerdict`) this is
`HilbertData.StackedFamily.feecVerdict` and, for the BGG complexes `bgg J` of [ArnoldHu2021] with
the connecting maps up to `J` bounded below and the regular decompositions after `J`,
`HilbertData.StackedFamily.bggVerdict`.

The derived complex of the domain complexes is a Hilbert complex of bounded operators in the
graph norms (the bounded Hilbert complexes of [ArnoldHu2021], §3), so the verdicts are statements
in these norms; the `L²` realization of the derived complex as a complex of closed unbounded
operators is not formalized. The weak-symmetry discretizations of
`Feec.HilbertComplex.BGG.Discrete` are not stacked families: their discrete connecting maps are
`Πₕ S` (the compatibility condition `Discrete.Compatible`), not `S`, so their discrete complexes are
not subcomplexes of the derived complex.

## Main definitions

* `HilbertComplex.Subcomplex.domain`, `CochainProjection.domain`, **`ConformingFamily.domain`**:
  a conforming family in the domain complex; `ConformingFamily.full`: the whole spaces of a
  complex of bounded operators on finite-dimensional spaces.
* `Feec.BGG.BoundedData.StackedFamily`: stacked conforming families of bounded BGG data;
  `StackedFamily.twistπL`, `StackedFamily.derivedπ`, `StackedFamily.derivedSubcomplex`,
  **`StackedFamily.derived`**; `StackedFamily.full`.
* `Feec.BGG.HilbertData.StackedFamily`, `StackedFamily.toDomain`, `StackedFamily.derived`,
  **`StackedFamily.twist`**.
* `BoundedData.StackedFamily.Verdict`, `HilbertData.StackedFamily.Verdict`.

## Main results

* `BoundedData.StackedFamily.derivedD_derivedπ`, `derivedπ_derivedπ`: the derived projection is a
  cochain projection; `mem_derivedSubcomplex_iff`: its range is `P_{(Δⁱ)ᗮ} (Γⁱ ∩ (Vₕⁱ × Ṽₕⁱ))`.
* **`BoundedData.StackedFamily.feecVerdict`**, **`HilbertData.StackedFamily.feecVerdict`**,
  **`HilbertData.StackedFamily.bggVerdict`**: the FEEC theorem for discrete BGG complexes.
* `HilbertData.finiteDimensional_derivedComplex_harmonic`.
* `BoundedData.idShift_feecVerdict`: non-vacuity (`BoundedData.idShift`, the full family).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3 (bounded Hilbert complexes
  and linking maps, Theorem 6), §5 (the twisted complex)
* [F. Bonizzoni, K. Hu, G. Kanschat, D. Sap, *Discrete tensor product BGG sequences: splines and finite elements*][BonizzoniHuKanschatSap2024]
  (discrete BGG diagrams)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1.2 (domain complex), §3.3 (bounded cochain projections), Thms 3.4–3.9

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Filter Topology Metric

@[expose] public noncomputable section

universe u v

/-! ### Conforming families of the domain complex -/

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*}

/-- `N.comap f` is finite-dimensional for `f` injective and `N` finite-dimensional. -/
theorem _root_.Submodule.finiteDimensional_comap_of_injective {K X Y : Type*} [Field K]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] {f : X →ₗ[K] Y}
    (hf : Function.Injective f) (N : Submodule K Y) [FiniteDimensional K N] :
    FiniteDimensional K (N.comap f) :=
  .of_injective (f.restrict (p := N.comap f) (q := N) fun _ hx => hx)
    fun _ _ hab => Subtype.ext (hf (congrArg Subtype.val hab))

/-- `‖x‖ ≤ ‖x₁‖ + ‖x₂‖` on the `ℓ²` product. -/
theorem _root_.WithLp.norm_le_norm_fst_add_norm_snd {α β : Type*} [SeminormedAddCommGroup α]
    [SeminormedAddCommGroup β] (x : WithLp 2 (α × β)) : ‖x‖ ≤ ‖x.fst‖ + ‖x.snd‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [WithLp.prod_norm_sq_eq_of_L2, add_sq]
  nlinarith [norm_nonneg x.fst, norm_nonneg x.snd]

/-- Maps bounded by `C` act componentwise on the `ℓ²` product with bound `C`. -/
theorem _root_.WithLp.norm_toLp_map_le {α β : Type*} [SeminormedAddCommGroup α]
    [SeminormedAddCommGroup β] {p : α → α} {q : β → β} {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ a, ‖p a‖ ≤ C * ‖a‖) (hq : ∀ b, ‖q b‖ ≤ C * ‖b‖) (x : WithLp 2 (α × β)) :
    ‖WithLp.toLp 2 (p x.fst, q x.snd)‖ ≤ C * ‖x‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [WithLp.prod_norm_sq_eq_of_L2, mul_pow, WithLp.prod_norm_sq_eq_of_L2 x, mul_add,
    ← mul_pow, ← mul_pow]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hp _) 2)
    (pow_le_pow_left₀ (norm_nonneg _) (hq _) 2)

namespace Subcomplex

/-- **A subcomplex in the domain complex**: `Vₕⁱ ⊆ D(dⁱ)` as a subspace of the graph space. -/
def domain (S : H.Subcomplex) : H.domainComplex.Subcomplex where
  V i := (S.V i).comap (H.domainIncl i).toLinearMap
  le_domain _ _ := le_top
  mapsTo i j x hx := by
    change H.domainIncl j (H.domainD i j x) ∈ S.V j
    rw [domainIncl_domainD]
    exact S.mapsTo i j _ hx

theorem mem_domain_iff {S : H.Subcomplex} {i : ι} {v : H.domainSpace i} :
    v ∈ S.domain.V i ↔ H.domainIncl i v ∈ S.V i := Iff.rfl

instance (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)] (i : ι) :
    FiniteDimensional 𝕜 (S.domain.V i) :=
  Submodule.finiteDimensional_comap_of_injective (H.domainIncl_injective i) _

namespace CochainProjection

variable {S : H.Subcomplex} (P : S.CochainProjection)

/-- `π` on the graph space, `v ↦ (π v, d π v)`. -/
def domainπ (i : ι) : H.domainSpace i →ₗ[𝕜] H.domainSpace i where
  toFun v := (H.d i (c.next i)).toGraphSpace
    ⟨P.π i (H.domainIncl i v), S.le_domain i _ (P.mem i _)⟩
  map_add' u v := H.domainIncl_injective i (by simp)
  map_smul' a v := H.domainIncl_injective i (by simp)

@[simp] theorem domainIncl_domainπ (i : ι) (v : H.domainSpace i) :
    H.domainIncl i (P.domainπ i v) = P.π i (H.domainIncl i v) := rfl

/-- `d π = π d` on the graph space. -/
theorem d_domainCoord_domainπ (i j : ι) (v : H.domainSpace i) :
    H.d i j (H.domainCoord i j (P.domainπ i v)) = P.π j (H.d i j (H.domainCoord i j v)) :=
  P.comm i j (H.domainCoord i j v)

/-- **The cochain projection in the domain complex**. -/
def domain : S.domain.CochainProjection where
  π := P.domainπ
  mem i v := P.mem i _
  proj i v hv := H.domainIncl_injective i (P.proj i _ hv)
  comm i j x := H.domainIncl_injective j (by
    change H.domainIncl j (H.domainD i j (P.domainπ i x)) =
      H.domainIncl j (P.domainπ j (H.domainD i j x))
    rw [domainIncl_domainD, domainIncl_domainπ, domainIncl_domainD]
    exact P.d_domainCoord_domainπ i j x)

/-- A cochain projection bounded by `C` in `W` is bounded by `C` in the graph norm. -/
theorem norm_domainπ_le {C : ℝ} (hC : 0 ≤ C) (hπ : ∀ i x, ‖P.π i x‖ ≤ C * ‖x‖) (i : ι)
    (v : H.domainSpace i) : ‖P.domainπ i v‖ ≤ C * ‖v‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [H.norm_sq_domainSpace i (P.domainπ i v), mul_pow, H.norm_sq_domainSpace i v, mul_add,
    domainIncl_domainπ, d_domainCoord_domainπ, ← mul_pow, ← mul_pow]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hπ _ _) 2)
    (pow_le_pow_left₀ (norm_nonneg _) (hπ _ _) 2)

/-- `‖v - π v‖_V ≤ ‖x - π x‖ + ‖d x - π d x‖` for `x = ι v`. -/
theorem norm_sub_domainπ_le (i : ι) (v : H.domainSpace i) :
    ‖v - P.domainπ i v‖ ≤ ‖H.domainIncl i v - P.π i (H.domainIncl i v)‖ +
      ‖H.d i (c.next i) (H.domainCoord i _ v) - P.π _ (H.d i (c.next i) (H.domainCoord i _ v))‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [H.norm_sq_domainSpace, map_sub, map_sub, LinearPMap.map_sub, domainIncl_domainπ,
    d_domainCoord_domainπ, add_sq]
  nlinarith [norm_nonneg (H.domainIncl i v - P.π i (H.domainIncl i v)),
    norm_nonneg (H.d i (c.next i) (H.domainCoord i _ v) -
      P.π _ (H.d i (c.next i) (H.domainCoord i _ v)))]

end CochainProjection

end Subcomplex

namespace ConformingFamily

/-- **A conforming family in the domain complex**: the spaces `Vₕⁱ ⊆ D(dⁱ)` with the graph norm
and the cochain projections `v ↦ (πₕ v, d πₕ v)`, bounded in the graph norm by the bound of `πₕ`
in `W` (`d πₕ = πₕ d`), with the approximation property in the graph norm from that of `πₕ` in
`W` at `v` and `d v`. -/
def domain (F : ConformingFamily H κ) : ConformingFamily H.domainComplex κ where
  l := F.l
  V h := (F.V h).domain
  π h := (F.π h).domain
  bound_π := ⟨F.projBound, fun h i v => (F.π h).norm_domainπ_le
    (zero_le_one.trans F.one_le_projBound) (fun i => F.norm_π_le h i) i v⟩
  approx i v := by
    have hC : 0 ≤ F.projBound := zero_le_one.trans F.one_le_projBound
    have h0 := ((F.approx i (H.domainIncl i v)).const_mul (1 + F.projBound)).add
      ((F.approx _ (H.d i (c.next i) (H.domainCoord i _ v))).const_mul (1 + F.projBound))
    rw [mul_zero, add_zero] at h0
    refine squeeze_zero (fun _ => infDist_nonneg) (fun h => ?_) h0
    refine (infDist_le_dist_of_mem ((F.π h).domain.mem i v)).trans ?_
    rw [dist_eq_norm]
    exact ((F.π h).norm_sub_domainπ_le i v).trans (add_le_add
      ((F.π h).norm_sub_π_le_infDist hC (F.norm_π_le h i) _)
      ((F.π h).norm_sub_π_le_infDist hC (F.norm_π_le h _) _))

/-- **The full conforming family** of a Hilbert complex of bounded operators on
finite-dimensional spaces: the whole spaces with the identity projections, along any filter. -/
def full {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, InnerProductSpace 𝕜 (X i)]
    [∀ i, CompleteSpace (X i)] [∀ i, FiniteDimensional 𝕜 (X i)] (δ : ∀ i j, X i →L[𝕜] X j)
    (shape : ∀ i j, ¬ c.Rel i j → δ i j = 0) (comp : ∀ i j k x, δ j k (δ i j x) = 0)
    (l : Filter κ) : ConformingFamily (ofBounded δ shape comp) κ where
  l := l
  V _ := ⟨fun _ => ⊤, fun _ _ => le_top, fun _ _ _ _ => Submodule.mem_top⟩
  π _ := ⟨fun _ => LinearMap.id, fun _ _ => Submodule.mem_top, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  bound_π := ⟨1, fun _ _ x => by simp⟩
  approx _ w := by
    simp only [Submodule.top_coe, infDist_zero_of_mem (Set.mem_univ w)]
    exact tendsto_const_nhds

end ConformingFamily

end Feec.HilbertComplex

/-! ### Stacked conforming families of bounded BGG data -/

namespace Feec.BGG.BoundedData

open HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {V Vt : ι → Type u}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]
  [∀ i, NormedAddCommGroup (Vt i)] [∀ i, InnerProductSpace 𝕜 (Vt i)]
  [∀ i, CompleteSpace (Vt i)] (D : BoundedData 𝕜 c V Vt) (κ : Type*)

/-- The real structure of the derived spaces of complex BGG data, declared on `derivedSpace`
itself so that instance search does not compare the generic submodule norms. -/
instance instNormedSpaceRealDerivedSpace [∀ i, NormedSpace ℝ (V i)] [∀ i, NormedSpace ℝ (Vt i)]
    [∀ i, IsScalarTower ℝ 𝕜 (V i)] [∀ i, IsScalarTower ℝ 𝕜 (Vt i)] (E F : ι → Prop) (i : ι) :
    NormedSpace ℝ (D.derivedSpace E F i) where
  norm_smul_le r x := norm_smul_le r (x : WithLp 2 (V i × Vt i))

instance instIsScalarTowerRealDerivedSpace [∀ i, NormedSpace ℝ (V i)] [∀ i, NormedSpace ℝ (Vt i)]
    [∀ i, IsScalarTower ℝ 𝕜 (V i)] [∀ i, IsScalarTower ℝ 𝕜 (Vt i)] (E F : ι → Prop) (i : ι) :
    IsScalarTower ℝ 𝕜 (D.derivedSpace E F i) :=
  Submodule.isScalarTower' _

/-- **Stacked conforming families** of bounded BGG data, the discrete BGG data: conforming
families `Vₕ`, `Ṽₕ` of the two rows along one filter, linked by the connecting maps
(`S Ṽₕⁱ ⊆ Vₕʲ`), whose cochain projections commute with them (`πₕ S = S π̃ₕ`). -/
structure StackedFamily where
  /-- the family of the top row -/
  top : ConformingFamily D.rowTopComplex κ
  /-- the family of the bottom row -/
  bot : ConformingFamily D.rowBotComplex κ
  l_eq : bot.l = top.l
  S_mem : ∀ h i j (φ : Vt i), φ ∈ (bot.V h).V i → D.S i j φ ∈ (top.V h).V j
  S_comm : ∀ h i j (φ : Vt i), (top.π h).π j (D.S i j φ) = D.S i j ((bot.π h).π i φ)

namespace StackedFamily

variable {D κ} (G : D.StackedFamily κ)

theorem d_top_π (h : κ) (i j : ι) (σ : V i) :
    D.d i j ((G.top.π h).π i σ) = (G.top.π h).π j (D.d i j σ) :=
  (G.top.π h).comm i j ⟨σ, Submodule.mem_top⟩

theorem dt_bot_π (h : κ) (i j : ι) (φ : Vt i) :
    D.dt i j ((G.bot.π h).π i φ) = (G.bot.π h).π j (D.dt i j φ) :=
  (G.bot.π h).comm i j ⟨φ, Submodule.mem_top⟩

/-- The cochain projection `(σ, φ) ↦ (πₕ σ, π̃ₕ φ)` of the twisted complex. -/
def twistπ (h : κ) (i : ι) : V i × Vt i →ₗ[𝕜] V i × Vt i :=
  ((G.top.π h).π i).prodMap ((G.bot.π h).π i)

@[simp] theorem twistπ_apply (h : κ) (i : ι) (x : V i × Vt i) :
    G.twistπ h i x = ((G.top.π h).π i x.1, (G.bot.π h).π i x.2) := rfl

theorem twist_twistπ (h : κ) (i j : ι) (x : V i × Vt i) :
    D.twist i j (G.twistπ h i x) = G.twistπ h j (D.twist i j x) := by
  simp [G.d_top_π, G.dt_bot_π, G.S_comm]

theorem twistπ_twistπ (h : κ) (i : ι) (x : V i × Vt i) :
    G.twistπ h i (G.twistπ h i x) = G.twistπ h i x := by
  simp [(G.top.π h).proj i _ ((G.top.π h).mem i _), (G.bot.π h).proj i _ ((G.bot.π h).mem i _)]

variable (E F : ι → Prop)

theorem twistπ_mem_Γ (h : κ) {i : ι} {x : V i × Vt i} (hx : x ∈ D.Γ E i) :
    G.twistπ h i x ∈ D.Γ E i := by
  rw [Data.mem_Γ] at hx ⊢
  refine ⟨fun hi => by simp [hx.1 hi], fun hi => ?_⟩
  rw [G.twist_twistπ, twistπ_apply, hx.2 hi, map_zero]

theorem twistπ_mem_Δ (h : κ) {i : ι} {x : V i × Vt i} (hx : x ∈ D.Δ F i) :
    G.twistπ h i x ∈ D.Δ F i := by
  obtain ⟨φ, ψ, hφ, hψ, rfl⟩ := (D.mem_Δ F).1 hx
  refine (D.mem_Δ F).2 ⟨(G.bot.π h).π i φ, (G.bot.π h).π _ ψ, hφ.imp_right fun h0 => by simp [h0],
    hψ.imp_right fun h0 => by simp [h0], ?_⟩
  rw [map_add, ← G.twist_twistπ]
  simp


/-! #### On the `ℓ²` product -/

/-- A common bound `max C C̃ ≥ 1` of the projections of the two rows. -/
def projBound : ℝ := max G.top.projBound G.bot.projBound

theorem one_le_projBound : 1 ≤ G.projBound := G.top.one_le_projBound.trans (le_max_left _ _)

theorem norm_twistπ_le (h : κ) (i : ι) (x : WithLp 2 (V i × Vt i)) :
    ‖WithLp.toLp 2 (G.twistπ h i x.ofLp)‖ ≤ G.projBound * ‖x‖ :=
  WithLp.norm_toLp_map_le (zero_le_one.trans G.one_le_projBound)
    (fun _ => (G.top.norm_π_le h i _).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
    (fun _ => (G.bot.norm_π_le h i _).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))) x

/-- The cochain projection of the twisted complex on `Vⁱ ⊕ Ṽⁱ`, bounded by `projBound`. -/
def twistπL (h : κ) (i : ι) : WithLp 2 (V i × Vt i) →L[𝕜] WithLp 2 (V i × Vt i) :=
  LinearMap.mkContinuous
    ((WithLp.linearEquiv 2 𝕜 (V i × Vt i)).symm.toLinearMap ∘ₗ G.twistπ h i ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (V i × Vt i)).toLinearMap) G.projBound (G.norm_twistπ_le h i)

@[simp] theorem ofLp_twistπL (h : κ) (i : ι) (x : WithLp 2 (V i × Vt i)) :
    (G.twistπL h i x).ofLp = G.twistπ h i x.ofLp := rfl

theorem norm_twistπL_le (h : κ) (i : ι) (x : WithLp 2 (V i × Vt i)) :
    ‖G.twistπL h i x‖ ≤ G.projBound * ‖x‖ := G.norm_twistπ_le h i x

theorem twistL_twistπL (h : κ) (i j : ι) (x : WithLp 2 (V i × Vt i)) :
    D.twistL i j (G.twistπL h i x) = G.twistπL h j (D.twistL i j x) :=
  WithLp.ofLp_injective 2 (G.twist_twistπ h i j x.ofLp)

theorem twistπL_twistπL (h : κ) (i : ι) (x : WithLp 2 (V i × Vt i)) :
    G.twistπL h i (G.twistπL h i x) = G.twistπL h i x :=
  WithLp.ofLp_injective 2 (G.twistπ_twistπ h i x.ofLp)

theorem twistπL_mem_ΓL (h : κ) {i : ι} {x : WithLp 2 (V i × Vt i)} (hx : x ∈ D.ΓL E i) :
    G.twistπL h i x ∈ D.ΓL E i :=
  G.twistπ_mem_Γ E h hx

theorem twistπL_mem_ΔL (h : κ) {i : ι} {x : WithLp 2 (V i × Vt i)} (hx : x ∈ D.ΔL E F i) :
    G.twistπL h i x ∈ D.ΔL E F i :=
  ⟨G.twistπ_mem_Δ F h hx.1, G.twistπ_mem_Γ E h hx.2⟩

/-- `πₕ × π̃ₕ` maps the closure of the exact part into itself. -/
theorem twistπL_mem_closure_ΔL (h : κ) {i : ι} {x : WithLp 2 (V i × Vt i)}
    (hx : x ∈ (D.ΔL E F i).topologicalClosure) :
    G.twistπL h i x ∈ (D.ΔL E F i).topologicalClosure :=
  Submodule.topologicalClosure_minimal (s := D.ΔL E F i)
    (t := (D.ΔL E F i).topologicalClosure.comap (G.twistπL h i).toLinearMap)
    (fun _ hy => (D.ΔL E F i).le_topologicalClosure (G.twistπL_mem_ΔL E F h hy))
    ((Submodule.isClosed_topologicalClosure _).preimage (G.twistπL h i).continuous) hx

/-! #### The derived subcomplex -/

omit G in
/-- `P_{(Δⁱ)ᗮ}` identifies points that differ by the closure of `Δⁱ`. -/
theorem starProjection_eq_of_sub_mem {i : ι} {u w : WithLp 2 (V i × Vt i)}
    (h : u - w ∈ (D.ΔL E F i).topologicalClosure) :
    (D.ΔL E F i)ᗮ.starProjection u = (D.ΔL E F i)ᗮ.starProjection w := by
  rw [← sub_eq_zero, ← map_sub, Submodule.starProjection_apply_eq_zero_iff,
    Submodule.orthogonal_orthogonal_eq_closure]
  exact h

omit G in
theorem sub_starProjection_mem_closure {i : ι} (u : WithLp 2 (V i × Vt i)) :
    u - (D.ΔL E F i)ᗮ.starProjection u ∈ (D.ΔL E F i).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  exact Submodule.sub_starProjection_mem_orthogonal _

theorem starProjection_twistπL_starProjection (h : κ) {i : ι} (u : WithLp 2 (V i × Vt i)) :
    (D.ΔL E F i)ᗮ.starProjection (G.twistπL h i ((D.ΔL E F i)ᗮ.starProjection u)) =
      (D.ΔL E F i)ᗮ.starProjection (G.twistπL h i u) := by
  refine starProjection_eq_of_sub_mem E F ?_
  rw [← map_sub, ← neg_sub, map_neg, neg_mem_iff]
  exact G.twistπL_mem_closure_ΔL E F h (sub_starProjection_mem_closure E F u)

/-- **The derived cochain projection** `y ↦ P_{(Δⁱ)ᗮ} (πₕ × π̃ₕ) y` on `Υⁱ = Γⁱ ⊖ Δⁱ`. -/
def derivedπ (h : κ) (i : ι) : D.derivedSpace E F i →L[𝕜] D.derivedSpace E F i :=
  ((D.ΔL E F i)ᗮ.starProjection ∘L G.twistπL h i ∘L (D.derivedSpace E F i).subtypeL).codRestrict
    (D.derivedSpace E F i) fun y =>
      ⟨D.starProjection_mem_ΓL E F (G.twistπL_mem_ΓL E h y.2.1),
        Submodule.starProjection_apply_mem _ _⟩

theorem coe_derivedπ (h : κ) (i : ι) (y : D.derivedSpace E F i) :
    (G.derivedπ E F h i y : WithLp 2 (V i × Vt i)) =
      (D.ΔL E F i)ᗮ.starProjection (G.twistπL h i y) := rfl

theorem derivedπ_derivedπ (h : κ) (i : ι) (y : D.derivedSpace E F i) :
    G.derivedπ E F h i (G.derivedπ E F h i y) = G.derivedπ E F h i y := by
  ext : 1
  rw [coe_derivedπ, coe_derivedπ, G.starProjection_twistπL_starProjection, G.twistπL_twistπL]

/-- **The derived projection commutes with the derived differential.** -/
theorem derivedD_derivedπ (h : κ) (i j : ι) (y : D.derivedSpace E F i) :
    D.derivedD E F i j (G.derivedπ E F h i y) = G.derivedπ E F h j (D.derivedD E F i j y) := by
  ext : 1
  rw [coe_derivedD, coe_derivedπ, coe_derivedπ, coe_derivedD,
    G.starProjection_twistπL_starProjection, ← G.twistL_twistπL]
  refine starProjection_eq_of_sub_mem E F ?_
  rw [← map_sub, ← neg_sub, map_neg, neg_mem_iff]
  exact D.twistL_mem_closure_ΔL E F i j (sub_starProjection_mem_closure E F _)

/-- The discrete twisted space `Vₕⁱ × Ṽₕⁱ ⊆ Vⁱ ⊕ Ṽⁱ`. -/
def twistV (h : κ) (i : ι) : Submodule 𝕜 (WithLp 2 (V i × Vt i)) :=
  LinearMap.range ((WithLp.linearEquiv 2 𝕜 (V i × Vt i)).symm.toLinearMap ∘ₗ
    ((G.top.V h).V i).subtype.prodMap ((G.bot.V h).V i).subtype)

theorem twistπL_mem_twistV (h : κ) (i : ι) (x : WithLp 2 (V i × Vt i)) :
    G.twistπL h i x ∈ G.twistV h i :=
  ⟨(⟨_, (G.top.π h).mem i x.ofLp.1⟩, ⟨_, (G.bot.π h).mem i x.ofLp.2⟩), rfl⟩

/-- **The discrete derived spaces** `Υₕⁱ`, the range of the derived projection: the projections
`P_{(Δⁱ)ᗮ} (Γⁱ ∩ (Vₕⁱ × Ṽₕⁱ))` (`mem_derivedSubcomplex_iff`), a subcomplex of the derived
complex. -/
def derivedSubcomplex (h : κ) : (D.derivedComplex E F).Subcomplex where
  V i := LinearMap.range (G.derivedπ E F h i : D.derivedSpace E F i →ₗ[𝕜] D.derivedSpace E F i)
  le_domain _ _ := le_top
  mapsTo i j _ := by
    rintro ⟨z, rfl⟩
    exact ⟨D.derivedD E F i j z, (G.derivedD_derivedπ E F h i j z).symm⟩

theorem twistπL_of_mem_twistV (h : κ) {i : ι} {x : WithLp 2 (V i × Vt i)}
    (hx : x ∈ G.twistV h i) : G.twistπL h i x = x := by
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  exact WithLp.ofLp_injective 2 (Prod.ext ((G.top.π h).proj i a a.2) ((G.bot.π h).proj i b b.2))

/-- **The discrete derived spaces are `P_{(Δⁱ)ᗮ} (Γⁱ ∩ (Vₕⁱ × Ṽₕⁱ))`.** -/
theorem mem_derivedSubcomplex_iff (h : κ) {i : ι} {y : D.derivedSpace E F i} :
    y ∈ (G.derivedSubcomplex E F h).V i ↔ ∃ x ∈ D.ΓL E i ⊓ G.twistV h i,
      (y : WithLp 2 (V i × Vt i)) = (D.ΔL E F i)ᗮ.starProjection x := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨G.twistπL_mem_ΓL E h z.2.1, G.twistπL_mem_twistV h i z⟩, rfl⟩
  · rintro ⟨x, ⟨-, hx⟩, hy⟩
    refine ⟨y, Subtype.ext ?_⟩
    change (G.derivedπ E F h i y : WithLp 2 (V i × Vt i)) = y
    rw [coe_derivedπ, hy, G.starProjection_twistπL_starProjection, G.twistπL_of_mem_twistV h hx]

instance (h : κ) (i : ι) : FiniteDimensional 𝕜 ((G.derivedSubcomplex E F h).V i) := by
  have : FiniteDimensional 𝕜 (((G.twistV h i).map
      ((D.ΔL E F i)ᗮ.starProjection : WithLp 2 (V i × Vt i) →ₗ[𝕜] _)).comap
        (D.derivedSpace E F i).subtype) :=
    have : FiniteDimensional 𝕜 (G.twistV h i) := LinearMap.finiteDimensional_range _
    Submodule.finiteDimensional_comap_of_injective (Submodule.injective_subtype _) _
  refine Submodule.finiteDimensional_of_le (S₂ := ((G.twistV h i).map
      ((D.ΔL E F i)ᗮ.starProjection : WithLp 2 (V i × Vt i) →ₗ[𝕜] _)).comap
        (D.derivedSpace E F i).subtype) ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨_, G.twistπL_mem_twistV h i y, rfl⟩

/-- The derived projection as a cochain projection onto `derivedSubcomplex`. -/
def derivedCochainProjection (h : κ) : (G.derivedSubcomplex E F h).CochainProjection where
  π i := G.derivedπ E F h i
  mem i y := ⟨y, rfl⟩
  proj i _ := by
    rintro ⟨z, rfl⟩
    exact G.derivedπ_derivedπ E F h i z
  comm i j y := G.derivedD_derivedπ E F h i j y

theorem norm_derivedπ_le (h : κ) (i : ι) (y : D.derivedSpace E F i) :
    ‖G.derivedπ E F h i y‖ ≤ G.projBound * ‖y‖ :=
  (Submodule.norm_starProjection_apply_le _ _).trans (G.norm_twistπL_le h i _)

theorem norm_sub_derivedπ_le (h : κ) (i : ι) (y : D.derivedSpace E F i) :
    ‖y - G.derivedπ E F h i y‖ ≤ ‖(y : WithLp 2 (V i × Vt i)).fst - (G.top.π h).π i
      (y : WithLp 2 (V i × Vt i)).fst‖ + ‖(y : WithLp 2 (V i × Vt i)).snd -
        (G.bot.π h).π i (y : WithLp 2 (V i × Vt i)).snd‖ := by
  have hy : (D.ΔL E F i)ᗮ.starProjection (y : WithLp 2 (V i × Vt i)) = y :=
    Submodule.starProjection_eq_self_iff.2 y.2.2
  rw [← Submodule.norm_coe, Submodule.coe_sub, coe_derivedπ]
  nth_rw 1 [← hy]
  rw [← map_sub]
  exact (Submodule.norm_starProjection_apply_le _ _).trans
    (WithLp.norm_le_norm_fst_add_norm_snd _)

/-- **The conforming family of the derived complex**: the discrete derived spaces
(`derivedSubcomplex`), with the derived projections, bounded by `max C C̃`, and the approximation
property from those of the two rows. -/
def derived : ConformingFamily (D.derivedComplex E F) κ where
  l := G.top.l
  V := G.derivedSubcomplex E F
  π := G.derivedCochainProjection E F
  bound_π := ⟨G.projBound, G.norm_derivedπ_le E F⟩
  approx i y := by
    have hC := zero_le_one.trans G.top.one_le_projBound
    have hC' := zero_le_one.trans G.bot.one_le_projBound
    have hb := G.bot.approx i (y : WithLp 2 (V i × Vt i)).snd
    rw [G.l_eq] at hb
    have h0 := ((G.top.approx i (y : WithLp 2 (V i × Vt i)).fst).const_mul
      (1 + G.top.projBound)).add (hb.const_mul (1 + G.bot.projBound))
    rw [mul_zero, mul_zero, add_zero] at h0
    refine squeeze_zero (fun _ => infDist_nonneg) (fun h => ?_) h0
    refine (infDist_le_dist_of_mem (G.derivedCochainProjection E F h |>.mem i y)).trans ?_
    rw [dist_eq_norm]
    exact (G.norm_sub_derivedπ_le E F h i y).trans (add_le_add
      ((G.top.π h).norm_sub_π_le_infDist hC (G.top.norm_π_le h i) _)
      ((G.bot.π h).norm_sub_π_le_infDist hC' (G.bot.norm_π_le h i) _))

variable (D) in
/-- **The full stacked family** of bounded BGG data of finite-dimensional spaces
(`ConformingFamily.full`), along any filter. -/
def full [∀ i, FiniteDimensional 𝕜 (V i)] [∀ i, FiniteDimensional 𝕜 (Vt i)] (l : Filter κ) :
    D.StackedFamily κ where
  top := ConformingFamily.full _ _ _ l
  bot := ConformingFamily.full _ _ _ l
  l_eq := rfl
  S_mem _ _ _ _ _ := Submodule.mem_top
  S_comm _ _ _ _ := rfl

end StackedFamily

end Feec.BGG.BoundedData

/-! ### Stacked conforming families of two Hilbert complexes -/

namespace Feec.BGG.HilbertData

open HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W Wt : ι → Type v}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (Wt i)] [∀ i, InnerProductSpace 𝕜 (Wt i)]
  [∀ i, CompleteSpace (Wt i)] (D : HilbertData 𝕜 c W Wt) (κ : Type*)

/-- **Stacked conforming families** of analytic BGG data, the discrete BGG data: conforming
families `Vₕ`, `Ṽₕ` of the two Hilbert complexes along one filter (commuting cochain projections
bounded in `L²`), linked by the connecting maps, `S Ṽₕⁱ ⊆ Vₕʲ`, with `πₕ S = S π̃ₕ`. -/
structure StackedFamily where
  /-- the family of the top complex -/
  top : ConformingFamily D.H κ
  /-- the family of the bottom complex -/
  bot : ConformingFamily D.Ht κ
  l_eq : bot.l = top.l
  S_mem : ∀ h i j (φ : Wt i), φ ∈ (bot.V h).V i → D.S i j φ ∈ (top.V h).V j
  S_comm : ∀ h i j (φ : Wt i), (top.π h).π j (D.S i j φ) = D.S i j ((bot.π h).π i φ)

namespace StackedFamily

variable {D κ} (G : D.StackedFamily κ)

/-- The stacked families in the domain complexes (`ConformingFamily.domain`), stacked conforming
families of the bounded BGG data `domainData`. -/
def toDomain : D.domainData.StackedFamily κ where
  top := G.top.domain
  bot := G.bot.domain
  l_eq := G.l_eq
  S_mem h i j _ hφ := G.S_mem h i j _ hφ
  S_comm h i j _ := D.H.domainIncl_injective j (G.S_comm h i j _)

/-! #### The `L²` twisted complex -/

/-- The cochain projection `(σ, φ) ↦ (πₕ σ, π̃ₕ φ)` of the `L²` twisted complex. -/
def twistπ (h : κ) (i : ι) : WithLp 2 (W i × Wt i) →ₗ[𝕜] WithLp 2 (W i × Wt i) :=
  (WithLp.linearEquiv 2 𝕜 (W i × Wt i)).symm.toLinearMap ∘ₗ
    ((G.top.π h).π i).prodMap ((G.bot.π h).π i) ∘ₗ (WithLp.linearEquiv 2 𝕜 (W i × Wt i)).toLinearMap

@[simp] theorem fst_twistπ (h : κ) (i : ι) (x : WithLp 2 (W i × Wt i)) :
    (G.twistπ h i x).fst = (G.top.π h).π i x.fst := rfl

@[simp] theorem snd_twistπ (h : κ) (i : ι) (x : WithLp 2 (W i × Wt i)) :
    (G.twistπ h i x).snd = (G.bot.π h).π i x.snd := rfl

/-- The inclusion `Vₕⁱ × Ṽₕⁱ → Wⁱ ⊕ W̃ⁱ`. -/
def twistIncl (h : κ) (i : ι) : (G.top.V h).V i × (G.bot.V h).V i →ₗ[𝕜] WithLp 2 (W i × Wt i) :=
  (WithLp.linearEquiv 2 𝕜 (W i × Wt i)).symm.toLinearMap ∘ₗ
    ((G.top.V h).V i).subtype.prodMap ((G.bot.V h).V i).subtype

/-- **The discrete twisted complex** `Vₕ × Ṽₕ`, a subcomplex of the `L²` twisted complex
(`S Ṽₕ ⊆ Vₕ`). -/
def twistSubcomplex (h : κ) : D.twistComplex.Subcomplex where
  V i := LinearMap.range (G.twistIncl h i)
  le_domain i j := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact D.mem_twistD_domain.2 ⟨(G.top.V h).le_domain i j a.2, (G.bot.V h).le_domain i j b.2⟩
  mapsTo i j _ := by
    rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨(⟨_, sub_mem ((G.top.V h).mapsTo i j a a.2) (G.S_mem h i j b b.2)⟩,
      ⟨_, (G.bot.V h).mapsTo i j b b.2⟩), WithLp.prod_ext' ?_ ?_⟩
    · exact (D.twistD_apply_fst (i := i) (j := j) ⟨G.twistIncl h i (a, b), _⟩).symm
    · exact (D.twistD_apply_snd (i := i) (j := j) ⟨G.twistIncl h i (a, b), _⟩).symm

instance (h : κ) (i : ι) : FiniteDimensional 𝕜 ((G.twistSubcomplex h).V i) :=
  LinearMap.finiteDimensional_range _

/-- `πₕ × π̃ₕ` as a cochain projection onto the discrete twisted complex. -/
def twistCochainProjection (h : κ) : (G.twistSubcomplex h).CochainProjection where
  π := G.twistπ h
  mem i x := ⟨(⟨_, (G.top.π h).mem i x.fst⟩, ⟨_, (G.bot.π h).mem i x.snd⟩), rfl⟩
  proj i _ := by
    rintro ⟨⟨a, b⟩, rfl⟩
    exact WithLp.prod_ext' ((G.top.π h).proj i a a.2) ((G.bot.π h).proj i b b.2)
  comm i j x := by
    have hx := D.mem_twistD_domain.1 x.2
    change D.twistD i j ⟨G.twistπ h i x, _⟩ = G.twistπ h j (D.twistD i j x)
    refine WithLp.prod_ext' ?_ ?_
    · rw [twistD_apply_fst]
      refine (congrArg₂ (· - ·) ((G.top.π h).comm i j ⟨_, hx.1⟩)
        (G.S_comm h i j _).symm).trans ?_
      rw [fst_twistπ, D.twistD_apply_fst (i := i) (j := j) x, map_sub]
      rfl
    · rw [twistD_apply_snd]
      refine ((G.bot.π h).comm i j ⟨_, hx.2⟩).trans ?_
      rw [snd_twistπ, D.twistD_apply_snd (i := i) (j := j) x]

/-- **The conforming family of the `L²` twisted complex**: the discrete twisted complexes
`Vₕ × Ṽₕ` with the projections `πₕ × π̃ₕ`, bounded in `L²` by `max C C̃`. -/
def twist : ConformingFamily D.twistComplex κ where
  l := G.top.l
  V := G.twistSubcomplex
  π := G.twistCochainProjection
  bound_π := ⟨max G.top.projBound G.bot.projBound, fun h i x =>
    WithLp.norm_toLp_map_le (zero_le_one.trans (G.top.one_le_projBound.trans (le_max_left _ _)))
      (fun _ => (G.top.norm_π_le h i _).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
      (fun _ => (G.bot.norm_π_le h i _).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))) x⟩
  approx i x := by
    have hC := zero_le_one.trans G.top.one_le_projBound
    have hC' := zero_le_one.trans G.bot.one_le_projBound
    have hb := G.bot.approx i x.snd
    rw [G.l_eq] at hb
    have h0 := ((G.top.approx i x.fst).const_mul (1 + G.top.projBound)).add
      (hb.const_mul (1 + G.bot.projBound))
    rw [mul_zero, mul_zero, add_zero] at h0
    refine squeeze_zero (fun _ => infDist_nonneg) (fun h => ?_) h0
    refine (infDist_le_dist_of_mem ((G.twistCochainProjection h).mem i x)).trans ?_
    rw [dist_eq_norm]
    exact (WithLp.norm_le_norm_fst_add_norm_snd _).trans (add_le_add
      ((G.top.π h).norm_sub_π_le_infDist hC (G.top.norm_π_le h i) _)
      ((G.bot.π h).norm_sub_π_le_infDist hC' (G.bot.norm_π_le h i) _))

variable (E F : ι → Prop)

/-- **The conforming family of the derived complex** of the domain complexes
(`BoundedData.StackedFamily.derived`). -/
abbrev derived : ConformingFamily (D.domainData.derivedComplex E F) κ := G.toDomain.derived E F

end StackedFamily

/-- **The harmonic forms of the derived complex are finite-dimensional** under the hypotheses of
the analytic BGG theorem (`derivedVerdict`). -/
theorem finiteDimensional_derivedComplex_harmonic {E F : ι → Prop}
    (hΔ : ∀ i, IsClosed (D.domainData.Δ F i : Set (D.H.domainSpace i × D.Ht.domainSpace i)))
    (he : D.domainData.Eliminates E F) (i : ι) [FiniteDimensional 𝕜 (D.H.cohomology i)]
    [FiniteDimensional 𝕜 (D.Ht.cohomology i)] :
    FiniteDimensional 𝕜 ((D.domainData.derivedComplex E F).harmonic i) :=
  have := (D.derivedVerdict hΔ he i).finiteDimensional
  ((D.domainData.derivedComplex E F).finiteDimensional_harmonic_iff
    (D.derivedVerdict hΔ he i).closedRangeAt).2 this

end Feec.BGG.HilbertData

/-! ### The FEEC theorem for discrete BGG complexes -/

namespace Feec.BGG.BoundedData.StackedFamily

open HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α]
  [CharZero α] {V Vt : α → Type u} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)] [∀ i, NormedAddCommGroup (Vt i)]
  [∀ i, InnerProductSpace 𝕜 (Vt i)] [∀ i, CompleteSpace (Vt i)] [∀ i, NormedSpace ℝ (V i)]
  [∀ i, IsScalarTower ℝ 𝕜 (V i)] [∀ i, NormedSpace ℝ (Vt i)] [∀ i, IsScalarTower ℝ 𝕜 (Vt i)]
  {D : BoundedData 𝕜 (ComplexShape.up α) V Vt} {κ : Type*} (G : D.StackedFamily κ)
  (E F : α → Prop)

/-- **The conclusions of the FEEC theorem for a discrete BGG complex** (`feecVerdict`): the
derived complex has closed range in every degree, the static FEEC theorem holds in every degree
with finite-dimensional harmonic forms, and the FEEC theorem (`ConformingFamily.Verdict`) holds
for the conforming family of the derived complex. -/
structure Verdict : Prop where
  /-- the derived complex has closed range ([ArnoldHu2021], Theorem 6) -/
  closedRangeAt (i : α) : (D.derivedComplex E F).ClosedRangeAt i
  /-- the static FEEC theorem in every degree ([AFW2010], Thms 3.4–3.9) -/
  static (j : α) [FiniteDimensional 𝕜 ((D.derivedComplex E F).harmonic j)] :
    (G.derived E F).StaticVerdict j
  /-- the FEEC theorem for the derived complex -/
  feec : (G.derived E F).Verdict

variable {E F}

/-- **The FEEC theorem for discrete BGG complexes of bounded data.** If the exact part is closed,
the elimination hypotheses hold and the rows have finite-dimensional cohomology, then for stacked
conforming families the derived complex has closed range (`derivedComplex_closedRangeAt`), so
the static FEEC theorem holds in every degree, and the FEEC theorem holds for the discrete
derived complexes. [ArnoldHu2021], Theorem 6; [AFW2010], Thms 3.4–3.9 -/
theorem feecVerdict (hΔ : ∀ i, IsClosed (D.Δ F i : Set (V i × Vt i))) (he : D.Eliminates E F)
    [∀ i, FiniteDimensional 𝕜 (D.rowTopComplex.cohomology i)]
    [∀ i, FiniteDimensional 𝕜 (D.rowBotComplex.cohomology i)] : G.Verdict E F :=
  have hcr := fun i => D.derivedComplex_closedRangeAt hΔ he i
  ⟨hcr, fun j _ => (G.derived E F).staticFEEC hcr j, (G.derived E F).feec⟩

end Feec.BGG.BoundedData.StackedFamily

namespace Feec.BGG.BoundedData

variable (𝕜 : Type*) [RCLike 𝕜]

/-- **Non-vacuity of the FEEC theorem for discrete BGG complexes**: the full stacked family of
`idShift` (`Sⁱ = id` on `𝕜`) along `atTop`, for every `J`. -/
theorem idShift_feecVerdict (J : ℤ) :
    (StackedFamily.full (idShift 𝕜) (κ := ℕ) atTop).Verdict (J < ·) (· < J) :=
  StackedFamily.feecVerdict _ (fun _ => Submodule.closed_of_finiteDimensional _)
    (Data.injSurj_idShift 𝕜 J).eliminates

end Feec.BGG.BoundedData

namespace Feec.BGG.HilbertData.StackedFamily

open HilbertComplex

section Up

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α]
  [CharZero α] {W Wt : α → Type v} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] [∀ i, NormedAddCommGroup (Wt i)]
  [∀ i, InnerProductSpace 𝕜 (Wt i)] [∀ i, CompleteSpace (Wt i)] [∀ i, NormedSpace ℝ (W i)]
  [∀ i, IsScalarTower ℝ 𝕜 (W i)] [∀ i, NormedSpace ℝ (Wt i)] [∀ i, IsScalarTower ℝ 𝕜 (Wt i)]
  {D : HilbertData 𝕜 (ComplexShape.up α) W Wt} {κ : Type*} (G : D.StackedFamily κ)
  (E F : α → Prop)

/-- **The conclusions of the FEEC theorem for a discrete BGG complex of two Hilbert complexes**
(`feecVerdict`): those for the stacked families in the domain complexes
(`BoundedData.StackedFamily.Verdict`), and the analytic BGG verdict in every degree (cohomology of
dimension at most `dim Hⁱ(W) + dim Hⁱ(W̃)`). -/
structure Verdict : Prop extends G.toDomain.Verdict E F where
  /-- the analytic BGG theorem in every degree ([ArnoldHu2021], Theorem 6) -/
  derived (i : α) : D.DerivedVerdict E F i
  /-- the FEEC theorem for the discrete `L²` twisted complexes `Vₕ × Ṽₕ` -/
  twist : G.twist.Verdict

variable {E F}

/-- **The FEEC theorem for discrete BGG complexes.** For two Hilbert complexes linked by bounded
connecting maps with closed exact part and the elimination hypotheses, whose cohomology is
finite-dimensional, and stacked conforming families of them (`S Ṽₕ ⊆ Vₕ`, `πₕ S = S π̃ₕ`): the
discrete derived complexes form a conforming family of the derived complex of the domain
complexes, which has closed range and finite-dimensional cohomology, so the static FEEC theorem
holds in every degree and the whole FEEC theorem holds for it. [ArnoldHu2021], Theorem 6;
[AFW2010], Thms 3.4–3.9 -/
theorem feecVerdict
    (hΔ : ∀ i, IsClosed (D.domainData.Δ F i : Set (D.H.domainSpace i × D.Ht.domainSpace i)))
    (he : D.domainData.Eliminates E F) [∀ i, FiniteDimensional 𝕜 (D.H.cohomology i)]
    [∀ i, FiniteDimensional 𝕜 (D.Ht.cohomology i)] : G.Verdict E F :=
  have := fun i => (D.domainRowTopCohomologyEquiv i).symm.finiteDimensional
  have := fun i => (D.domainRowBotCohomologyEquiv i).symm.finiteDimensional
  ⟨G.toDomain.feecVerdict hΔ he, fun i => D.derivedVerdict hΔ he i, G.twist.feec⟩

end Up

section BGG

variable {𝕜 : Type*} [RCLike 𝕜] {W Wt : ℤ → Type v} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] [∀ i, NormedAddCommGroup (Wt i)]
  [∀ i, InnerProductSpace 𝕜 (Wt i)] [∀ i, CompleteSpace (Wt i)] [∀ i, NormedSpace ℝ (W i)]
  [∀ i, IsScalarTower ℝ 𝕜 (W i)] [∀ i, NormedSpace ℝ (Wt i)] [∀ i, IsScalarTower ℝ 𝕜 (Wt i)]
  {D : HilbertData 𝕜 (ComplexShape.up ℤ) W Wt} {κ : Type*} (G : D.StackedFamily κ)

/-- **The FEEC theorem for discrete BGG complexes `bgg J`**: if the connecting maps up to `J` are
bounded below, the regular decompositions hold after `J` and the two complexes have
finite-dimensional cohomology, then for stacked conforming families the FEEC theorem holds for
the discrete BGG complexes (`feecVerdict`). [ArnoldHu2021], Theorem 6 -/
theorem bggVerdict {J : ℤ} (hS : ∀ i ≤ J, ∃ K, AntilipschitzWith K (D.S i (i + 1)))
    (htop : D.RegularDecomposition J) [∀ i, FiniteDimensional 𝕜 (D.H.cohomology i)]
    [∀ i, FiniteDimensional 𝕜 (D.Ht.cohomology i)] : G.Verdict (J < ·) (· < J) := by
  have hS' : ∀ i < J, ∃ K, AntilipschitzWith K (D.domainData.S i (i + 1)) := fun i hi => by
    obtain ⟨K₁, h₁⟩ := hS i hi.le
    obtain ⟨K₂, h₂⟩ := hS (i + 1) (by omega)
    exact ⟨_, D.antilipschitz_domainS rfl rfl h₁ h₂⟩
  exact G.feecVerdict (D.domainData.isClosed_bgg_Δ hS')
    (Data.eliminates_bgg (fun i hi => (hS' i hi).choose_spec.injective) htop)

end BGG

end Feec.BGG.HilbertData.StackedFamily
