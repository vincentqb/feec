module

public import Feec.ForMathlib.Homology.Subcomplex
public import Feec.HilbertComplex.BGG.Basic

/-!
# The derived (BGG) complex of a stacked diagram, of any length

BGG data `D` (two complexes `(V, d)`, `(Ṽ, d̃)` on a complex shape `c`, connecting maps
`S : Ṽⁱ → Vʲ` with `d S = -S d̃`) has the twisted complex `T = (V × Ṽ, (σ, φ) ↦ (dσ - Sφ, d̃φ))`
(`Feec.BGG.Data.twistComplex`). The BGG construction eliminates from `T` the pairs of spaces that
`S` matches: a top space `Vʲ` against the bottom space before it (`j ∈ E`), a bottom space `Ṽⁱ`
against the top space after it (`i ∈ F`). Both eliminations are canonical subcomplexes of `T`,
over any ring and on any complex shape:

* `Γ E`, with `Γ Eⁱ = {x ∈ Tⁱ | x₁ = 0 if i ∈ E, (d x)₁ = 0 if next i ∈ E}`;
* `Δ F ⊆ Γ E`, spanned by `0 × Ṽⁱ` (`i ∈ F`) and its image `{(-Sψ, d̃ψ)}` under the twisted
  differential.

The **derived complex** is the subquotient `derived E F = Γ E / Δ F`. If `S` is "onto modulo `d`"
at the eliminated top spaces, `R(d) + R(S) = Vʲ`, and "one-to-one modulo `d̃`" at the eliminated
bottom spaces, `N(d̃) ∩ N(S) = 0`, and no `S` is used twice, then `T / Γ E` and `Δ F` are exact, and
**the derived complex has the cohomology of the twisted complex** (`Data.derivedHomologyIso`).
The cohomology of the twisted complex comes from the rows through the long exact sequence of
`0 → V → T → Ṽ → 0` (`Data.twistShortComplex_shortExact`); in particular the derived complex is
exact when both rows are (`Data.derived_acyclic`). For bounded data on Hilbert spaces the derived
complex is a Hilbert complex of bounded operators; when moreover `Δ F` is closed and the
elimination hypotheses hold, it has closed range wherever the rows have finite-dimensional
cohomology (`Feec.HilbertComplex.BGG.Analytic`).

On `ComplexShape.up ℤ`, eliminating the top spaces after `J` and the bottom spaces before `J`
is the BGG complex of Arnold and Hu ([ArnoldHu2021], (24)–(26)):

  `Υⁱ = Vⁱ / R(Sⁱ⁻¹)` (`i < J`), `Υᴶ = {(σ, φ) | dσ = Sᴶφ} / {(-Sψ, d̃ψ)}`, `Υⁱ = N(Sⁱ)` (`i > J`),

with differentials `d` (modulo `R(S)`), `σ ↦ d̃ (Sᴶ)⁻¹ dσ` at `J`, and `d̃`. The hypothesis
`Data.InjSurj J` (`Sⁱ` injective for `i < J`, surjective for `i ≥ J`) is weaker than the
`J`-injectivity/surjectivity condition [ArnoldHu2021], (23), which also asks `Sᴶ` injective;
with it, `Υᴶ ≅ Vᴶ / R(Sᴶ⁻¹)` and the theorem is [ArnoldHu2021], §5.2 (the cohomology of the
output complex is that of the twisted complex). The complex with weak symmetries (5.1) of
[QuennevilleBelair2015], §5.1 is the elimination of the one top space `V¹`: `Γ (· = j)` at the
index before `j` is `Feec.BGG.Segment.Γ` (`Data.Γ_eq_segment_Γ`), and the regularity hypothesis
of the thesis with exactness of the top row is the condition `R(d⁰) + R(S⁰) = V¹`
(`Segment.sup_range_eq_top`).

## Main definitions

* `Feec.BGG.Data.rowTop`, `Data.rowBot`: the two rows as complexes of modules;
  `Data.twistShortComplex`: `0 → V → T → Ṽ → 0`.
* `Data.Γ E`, `Data.Δ F`: the two eliminations; `Data.derived E F`: the derived complex.
* `Data.Eliminates E F`: the hypotheses (onto modulo `d` on `E`, one-to-one modulo `d̃` on `F`, no
  connecting map used twice).
* `Data.InjSurj J`, `Data.bgg J`: the BGG complex of [ArnoldHu2021] on `ComplexShape.up ℤ`.

## Main results

* `Data.twistShortComplex_shortExact`, `Data.twistComplex_acyclic`.
* `Data.quasiIso_Γ`, `Data.quasiIso_derived`: the two eliminations are quasi-isomorphisms.
* `Data.derivedHomologyIso`, `Data.derived_acyclic`: **the derived complex has the cohomology of
  the twisted complex**, any length, any shape, any ring.
* `Data.finiteDimensional_derived_homology`, `Data.finrank_derived_homology_le`: over a field,
  `dim Hⁱ(derived) ≤ dim Hⁱ(V) + dim Hⁱ(Ṽ)` (through `Data.finrank_twistComplex_homology_le`).
* `Data.bggHomologyIso`, `Data.bgg_acyclic`: the BGG complex of [ArnoldHu2021];
  `Data.eliminates_bgg`: its elimination hypotheses from `Sⁱ` one-to-one before `J` and onto
  modulo `d` after `J`.
* `Data.bggXEquivOfLt`, `Data.bggXEquivOfBijective`, `Data.bggΓEquivKer`: its spaces
  `Vⁱ / R(Sⁱ⁻¹)` before `J`, `Vᴶ / R(Sᴶ⁻¹)` at `J` (`Sᴶ` bijective) and `N(Sⁱ)` after `J`
  ([ArnoldHu2021], (24)–(26)).
* `Data.Γ_eq_segment_Γ`, `Segment.sup_range_eq_top`: the complex (5.1) as an elimination.
* `Data.injSurj_idShift`: non-vacuity, nonzero connecting maps (`Data.idShift`: `Sⁱ = id`) with
  the condition at every `J`. The de Rham instance is the Hessian diagram on smooth fields
  (`Feec.Domain.injSurj_hessianBGG`, whose BGG complex is the Hessian complex,
  `Feec.Domain.hessianBGGIso`). On the plain `HΛ` rows `S⁰ : H¹ ⊗ ℝ³ → H(curl)` is not onto;
  [ArnoldHu2021] use rows of shifted regularity (not formalized).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3 ((23)–(26), the output
  complex) and §5 (twisted complex, splitting off an exact subcomplex)
* [I. N. Bernstein, I. M. Gelfand, S. I. Gelfand, *Differential operators on the base affine space and a study of g-modules*][BernsteinGelfandGelfand1975]
  (the BGG resolution)
* [A. Čap, J. Slovák, V. Souček, *Bernstein–Gelfand–Gelfand sequences*][CapSlovakSoucek2001]
  (BGG sequences in differential geometry)
* [A. Čap, K. Hu, *BGG sequences with weak regularity and applications*][CapHu2024] (BGG
  sequences on Sobolev spaces)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §11 (the elasticity complex from two de Rham complexes)
* [M. Eastwood, *A complex from linear elasticity*][Eastwood2000] (the elasticity complex from
  the BGG resolution)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.1 (the complex with weak symmetries (5.1))

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace Feec.BGG

/-- Under exactness of the top row at `V¹` and the regularity `d¹V¹ ⊆ d¹S₀Ṽ⁰`, every `v ∈ V¹`
is `d⁰σ + S₀φ`: the hypotheses of [QuennevilleBelair2015], Prop 5.1 make `V¹` eliminable
(`Data.Eliminates`). -/
theorem Segment.sup_range_eq_top {R : Type*} [Ring R] {V0 V1 V2 Vt0 Vt1 Vt2 : Type*}
    [AddCommGroup V0] [Module R V0] [AddCommGroup V1] [Module R V1]
    [AddCommGroup V2] [Module R V2] [AddCommGroup Vt0] [Module R Vt0]
    [AddCommGroup Vt1] [Module R Vt1] [AddCommGroup Vt2] [Module R Vt2]
    (D : Segment R V0 V1 V2 Vt0 Vt1 Vt2) (hT : D.ExactTop)
    (hreg : LinearMap.range D.d1 ≤ LinearMap.range (D.d1 ∘ₗ D.S0)) :
    LinearMap.range D.d0 ⊔ LinearMap.range D.S0 = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨φ, hφ⟩ := hreg ⟨v, rfl⟩
  have : v - D.S0 φ ∈ LinearMap.ker D.d1 := by
    simp only [LinearMap.mem_ker, map_sub]; rw [← hφ]; simp
  rw [hT] at this
  rw [← sub_add_cancel v (D.S0 φ)]
  exact Submodule.add_mem_sup this ⟨φ, rfl⟩

namespace Data

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι} {V Vt : ι → Type v}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [∀ i, AddCommGroup (Vt i)]
  [∀ i, Module R (Vt i)] (D : Data R c V Vt)

@[simp] theorem twistComplex_d_apply (i j : ι) (x : V i × Vt i) :
    (D.twistComplex.d i j).hom x = D.twist i j x := rfl

/-! ## The rows and the short exact sequence `0 → V → T → Ṽ → 0` -/

/-- The top row `(V, d)` as a complex of modules. -/
def rowTop : HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (V i)
  d i j := ModuleCat.ofHom (D.d i j)
  shape i j h := by rw [D.shape_d i j h]; rfl
  d_comp_d' i j k _ _ := ModuleCat.hom_ext (LinearMap.ext fun x => D.d_comp_d i j k x)

/-- The bottom row `(Ṽ, d̃)` as a complex of modules. -/
def rowBot : HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (Vt i)
  d i j := ModuleCat.ofHom (D.dt i j)
  shape i j h := by rw [D.shape_dt i j h]; rfl
  d_comp_d' i j k _ _ := ModuleCat.hom_ext (LinearMap.ext fun x => D.dt_comp_dt i j k x)

/-- `σ ↦ (σ, 0)`: the top row is a subcomplex of the twisted complex. -/
def rowTopι : D.rowTop ⟶ D.twistComplex where
  f i := ModuleCat.ofHom (LinearMap.inl R (V i) (Vt i))
  comm' i j _ := ModuleCat.hom_ext (LinearMap.ext fun σ => by
    change D.twist i j (σ, 0) = (D.d i j σ, (0 : Vt j))
    simp)

/-- `(σ, φ) ↦ φ`: the bottom row is a quotient of the twisted complex. -/
def rowBotπ : D.twistComplex ⟶ D.rowBot where
  f i := ModuleCat.ofHom (LinearMap.snd R (V i) (Vt i))
  comm' _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- `0 → V → T → Ṽ → 0`: the twisted complex is an extension of the bottom row by the top row;
its connecting map in cohomology is induced by `S` ([ArnoldHu2021], §5.1; not formalized here). -/
def twistShortComplex : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c) :=
  ShortComplex.mk D.rowTopι D.rowBotπ (by ext i σ; rfl)

theorem twistShortComplex_shortExact : D.twistShortComplex.ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i =>
    { exact := by
        rw [ShortComplex.moduleCat_exact_iff]
        rintro ⟨σ, φ⟩ (h : φ = 0)
        exact ⟨σ, by subst h; rfl⟩
      mono_f := (ModuleCat.mono_iff_injective _).2 fun (a b : V i) h => congrArg Prod.fst h
      epi_g := (ModuleCat.epi_iff_surjective _).2 fun (φ : Vt i) =>
        ⟨((0 : V i), φ), rfl⟩ }

/-- **The twisted complex is exact when both rows are.** [ArnoldHu2021], §5.1 -/
theorem twistComplex_acyclic (hV : D.rowTop.Acyclic) (hVt : D.rowBot.Acyclic) :
    D.twistComplex.Acyclic :=
  D.twistShortComplex_shortExact.acyclic_X₂ hV hVt

/-! ## The two eliminations and the derived complex -/

variable (E F : ι → Prop)

/-- **The elimination of the top spaces `Vʲ`, `j ∈ E`**: `x₁ = 0` at `j ∈ E` and `(d x)₁ = 0`
before it. For `E = {j}` and the index `i` before `j` this is `Γ = {(σ, φ) | dσ = Sφ}` of the
complex (5.1) (`Data.Γ_eq_segment_Γ`). -/
def Γ (i : ι) : Submodule R (V i × Vt i) :=
  (⨅ _ : E i, LinearMap.ker (LinearMap.fst R (V i) (Vt i))) ⊓
    ⨅ _ : E (c.next i), LinearMap.ker (LinearMap.fst R _ _ ∘ₗ D.twist i (c.next i))

theorem mem_Γ {i : ι} {x : V i × Vt i} :
    x ∈ D.Γ E i ↔ (E i → x.1 = 0) ∧ (E (c.next i) → (D.twist i (c.next i) x).1 = 0) := by
  simp [Γ]

theorem twist_mem_Γ (i j : ι) {x : V i × Vt i} (hx : x ∈ D.Γ E i) :
    D.twist i j x ∈ D.Γ E j := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.next_eq' hij
    rw [mem_Γ] at hx ⊢
    exact ⟨hx.2, fun _ => by rw [D.twist_twist]; rfl⟩
  · rw [D.twist_eq_zero hij]; exact zero_mem _

/-- **The exact part carried by the bottom spaces `Ṽⁱ`, `i ∈ F`**: `0 × Ṽⁱ` (`i ∈ F`) and its
image `{(-Sψ, d̃ψ)}` under the twisted differential (previous index in `F`). -/
def Δ (i : ι) : Submodule R (V i × Vt i) :=
  (⨆ _ : F i, LinearMap.range (LinearMap.inr R (V i) (Vt i))) ⊔
    ⨆ _ : F (c.prev i),
      (LinearMap.range (LinearMap.inr R _ _)).map (D.twist (c.prev i) i)

theorem mem_Δ {i : ι} {x : V i × Vt i} :
    x ∈ D.Δ F i ↔ ∃ φ ψ, (F i ∨ φ = 0) ∧ (F (c.prev i) ∨ ψ = 0) ∧
      x = (0, φ) + D.twist (c.prev i) i (0, ψ) := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    have ha' : ∃ φ, (F i ∨ φ = 0) ∧ a = (0, φ) := by
      by_cases hF : F i
      · rw [iSup_pos hF] at ha
        obtain ⟨φ, rfl⟩ := ha
        exact ⟨φ, Or.inl hF, rfl⟩
      · rw [iSup_neg hF, Submodule.mem_bot] at ha
        exact ⟨0, Or.inr rfl, by rw [ha]; rfl⟩
    have hb' : ∃ ψ, (F (c.prev i) ∨ ψ = 0) ∧ b = D.twist (c.prev i) i (0, ψ) := by
      by_cases hF : F (c.prev i)
      · rw [iSup_pos hF] at hb
        obtain ⟨_, ⟨ψ, rfl⟩, rfl⟩ := hb
        exact ⟨ψ, Or.inl hF, rfl⟩
      · rw [iSup_neg hF, Submodule.mem_bot] at hb
        exact ⟨0, Or.inr rfl, by
          rw [hb, show ((0 : V (c.prev i)), (0 : Vt (c.prev i))) = 0 from rfl, map_zero]⟩
    obtain ⟨φ, hφ, rfl⟩ := ha'
    obtain ⟨ψ, hψ, rfl⟩ := hb'
    exact ⟨φ, ψ, hφ, hψ, rfl⟩
  · rintro ⟨φ, ψ, hφ, hψ, rfl⟩
    refine Submodule.add_mem_sup ?_ ?_
    · rcases hφ with hF | rfl
      · rw [iSup_pos hF]; exact ⟨φ, rfl⟩
      · exact zero_mem _
    · rcases hψ with hF | rfl
      · rw [iSup_pos hF]; exact ⟨(0, ψ), ⟨ψ, rfl⟩, rfl⟩
      · rw [show ((0 : V (c.prev i)), (0 : Vt (c.prev i))) = 0 from rfl, map_zero]
        exact zero_mem _

theorem twist_mem_Δ (i j : ι) {x : V i × Vt i} (hx : x ∈ D.Δ F i) :
    D.twist i j x ∈ D.Δ F j := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.prev_eq' hij
    obtain ⟨φ, ψ, hφ, -, rfl⟩ := (D.mem_Δ F).1 hx
    exact (D.mem_Δ F).2 ⟨0, φ, Or.inr rfl, hφ, by
      rw [map_add, D.twist_twist]; simp⟩
  · rw [D.twist_eq_zero hij]; exact zero_mem _

/-- **The hypotheses of the elimination**: `S` is onto modulo `d` at the eliminated top spaces,
one-to-one modulo `d̃` at the eliminated bottom spaces, and no connecting map is used twice. -/
structure Eliminates : Prop where
  top : ∀ j, E j → LinearMap.range (D.d (c.prev j) j) ⊔ LinearMap.range (D.S (c.prev j) j) = ⊤
  bot : ∀ i, F i → LinearMap.ker (D.dt i (c.next i)) ⊓ LinearMap.ker (D.S i (c.next i)) = ⊥
  disjoint : ∀ i j, c.Rel i j → F i → ¬ E j

variable {D E F}

theorem Eliminates.Δ_le_Γ (h : D.Eliminates E F) (i : ι) : D.Δ F i ≤ D.Γ E i := by
  intro x hx
  obtain ⟨φ, ψ, hφ, hψ, rfl⟩ := (D.mem_Δ F).1 hx
  rw [mem_Γ]
  refine ⟨fun hE => ?_, fun hE => ?_⟩
  · by_cases hr : c.Rel (c.prev i) i
    · rcases hψ with hF | rfl
      · exact absurd hE (h.disjoint _ _ hr hF)
      · simp
    · simp [D.twist_eq_zero hr]
  · by_cases hr : c.Rel i (c.next i)
    · rcases hφ with hF | rfl
      · exact absurd hE (h.disjoint _ _ hr hF)
      · rw [map_add, D.twist_twist]; simp
    · simp [D.twist_eq_zero hr]

variable (D E F)

/-- The subcomplex `Γ E` of the twisted complex. -/
abbrev ΓComplex : HomologicalComplex (ModuleCat.{v} R) c :=
  D.twistComplex.sub (D.Γ E) fun i j _ hx => D.twist_mem_Γ E i j hx

/-- **The derived complex** `Γ E / Δ F`. Without the hypotheses `Data.Eliminates`, `Δ F ⊓ Γ E` is
quotiented. -/
def derived : HomologicalComplex (ModuleCat.{v} R) c :=
  (D.ΓComplex E).quo (fun i => (D.Δ F i).comap (D.Γ E i).subtype) fun i j _ hx =>
    D.twist_mem_Δ F i j hx

/-- Where the exact part vanishes, the derived space `Γⁱ / Δⁱ` is `Γⁱ`. -/
def derivedXEquiv {i : ι} (h : D.Δ F i = ⊥) :
    (D.Γ E i ⧸ (D.Δ F i).comap (D.Γ E i).subtype) ≃ₗ[R] D.Γ E i :=
  Submodule.quotEquivOfEqBot _ (by rw [h, Submodule.comap_bot, Submodule.ker_subtype])

/-- The projection `Γ E → derived E F`. -/
def derivedπ : D.ΓComplex E ⟶ D.derived E F := HomologicalComplex.quoπ _ _ _

/-- The inclusion `Γ E → T`. -/
def Γι : D.ΓComplex E ⟶ D.twistComplex := HomologicalComplex.subι _ _ _

variable {D E F}

/-- **The elimination of the top spaces is a quasi-isomorphism**: `T / Γ E` is exact when
`R(d) + R(S)` is everything at the eliminated top spaces. [ArnoldHu2021], §5.2 -/
theorem quasiIso_Γ (h : ∀ j, E j →
    LinearMap.range (D.d (c.prev j) j) ⊔ LinearMap.range (D.S (c.prev j) j) = ⊤) :
    QuasiIso (D.Γι E) := by
  refine HomologicalComplex.quasiIso_subι _ _ _ (HomologicalComplex.quo_acyclic _ _ _ ?_)
  intro i (x : V i × Vt i) hx
  change D.twist i (c.next i) x ∈ D.Γ E (c.next i) at hx
  have hx1 : E (c.next i) → (D.twist i (c.next i) x).1 = 0 := ((D.mem_Γ E).1 hx).1
  by_cases hE : E i
  · have : x.1 ∈ LinearMap.range (D.d (c.prev i) i) ⊔ LinearMap.range (D.S (c.prev i) i) := by
      rw [h i hE]; trivial
    obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.1 this
    refine ⟨((a, -b) : V (c.prev i) × Vt (c.prev i)), ?_⟩
    change x - D.twist (c.prev i) i (a, -b) ∈ D.Γ E i
    rw [mem_Γ]
    refine ⟨fun _ => ?_, fun hE' => ?_⟩
    · simp [hab]
    · rw [map_sub, D.twist_twist, sub_zero]; exact hx1 hE'
  · refine ⟨0, ?_⟩
    change x - D.twist (c.prev i) i 0 ∈ D.Γ E i
    rw [map_zero, sub_zero, mem_Γ]
    exact ⟨fun h' => absurd h' hE, hx1⟩

/-- **The elimination of the bottom spaces is a quasi-isomorphism**: `Δ F` is exact when
`N(d̃) ∩ N(S) = 0` at the eliminated bottom spaces. [ArnoldHu2021], §5.2 -/
theorem quasiIso_derived (h : D.Eliminates E F) : QuasiIso (D.derivedπ E F) := by
  refine HomologicalComplex.quasiIso_quoπ _ _ _ (HomologicalComplex.sub_acyclic _ _ _ ?_)
  intro i (x : D.Γ E i) hx hdx
  change (x : V i × Vt i) ∈ D.Δ F i at hx
  replace hdx : D.twist i (c.next i) x = 0 := congrArg Subtype.val hdx
  obtain ⟨φ, ψ, hφ, hψ, hxe⟩ := (D.mem_Δ F).1 hx
  have hφ0 : φ = 0 := by
    rcases hφ with hF | rfl
    · have hd : D.twist i (c.next i) (0, φ) = 0 := by
        rw [hxe, map_add, D.twist_twist, add_zero] at hdx; exact hdx
      have : φ ∈ LinearMap.ker (D.dt i (c.next i)) ⊓ LinearMap.ker (D.S i (c.next i)) := by
        simp only [twist_apply, map_zero, zero_sub, Prod.mk_eq_zero, neg_eq_zero] at hd
        exact ⟨hd.2, hd.1⟩
      rw [h.bot i hF] at this
      exact this
    · rfl
  subst hφ0
  have hy : ((0 : V (c.prev i)), ψ) ∈ D.Δ F (c.prev i) := by
    rcases hψ with hF | rfl
    · rw [mem_Δ]
      exact ⟨ψ, 0, Or.inl hF, Or.inr rfl, by
        rw [show ((0 : V (c.prev (c.prev i))), (0 : Vt (c.prev (c.prev i)))) = 0 from rfl,
          map_zero, add_zero]⟩
    · exact zero_mem _
  refine ⟨⟨(0, ψ), h.Δ_le_Γ _ hy⟩, hy, Subtype.ext ?_⟩
  change D.twist (c.prev i) i (0, ψ) = x
  rw [hxe]; simp

/-- **BGG elimination: the derived complex has the cohomology of the twisted complex**, for BGG
data of any length on any complex shape over any ring, under `Data.Eliminates`. The long exact
sequence of `Data.twistShortComplex_shortExact` relates it to the cohomology of the two rows.
[ArnoldHu2021], §5.2 (in the Hilbert setting, for the eliminations of `Data.bgg`). -/
def derivedHomologyIso (h : D.Eliminates E F) (i : ι) :
    (D.derived E F).homology i ≅ D.twistComplex.homology i :=
  have := quasiIso_derived h
  have := quasiIso_Γ (D := D) h.top
  (isoOfQuasiIsoAt (D.derivedπ E F) i).symm ≪≫ isoOfQuasiIsoAt (D.Γι E) i

/-- **The derived complex is exact when both rows are.** [ArnoldHu2021], §5.2 -/
theorem derived_acyclic (h : D.Eliminates E F) (hV : D.rowTop.Acyclic) (hVt : D.rowBot.Acyclic) :
    (D.derived E F).Acyclic := fun i => by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((D.twistComplex_acyclic hV hVt) i).isZero_homology.of_iso (D.derivedHomologyIso h i)

/-! ## Finite-dimensional cohomology -/

section Field

variable {K : Type u} [Field K] {V Vt : ι → Type v} [∀ i, AddCommGroup (V i)]
  [∀ i, Module K (V i)] [∀ i, AddCommGroup (Vt i)] [∀ i, Module K (Vt i)]
  (D : Data K c V Vt) (i : ι) [FiniteDimensional K (D.rowTop.homology i)]
  [FiniteDimensional K (D.rowBot.homology i)]

open Module

/-- **The twisted complex has finite-dimensional cohomology where both rows do**, through the
long exact sequence of `0 → V → T → Ṽ → 0`. -/
theorem finiteDimensional_twistComplex_homology :
    FiniteDimensional K (D.twistComplex.homology i) :=
  have : FiniteDimensional K (D.twistShortComplex.X₁.homology i) :=
    ‹FiniteDimensional K (D.rowTop.homology i)›
  have : FiniteDimensional K (D.twistShortComplex.X₃.homology i) :=
    ‹FiniteDimensional K (D.rowBot.homology i)›
  D.twistShortComplex_shortExact.finiteDimensional_homology₂ i

/-- `dim Hⁱ(T) ≤ dim Hⁱ(V) + dim Hⁱ(Ṽ)`. -/
theorem finrank_twistComplex_homology_le :
    finrank K (D.twistComplex.homology i) ≤
      finrank K (D.rowTop.homology i) + finrank K (D.rowBot.homology i) :=
  have : FiniteDimensional K (D.twistShortComplex.X₁.homology i) :=
    ‹FiniteDimensional K (D.rowTop.homology i)›
  have : FiniteDimensional K (D.twistShortComplex.X₃.homology i) :=
    ‹FiniteDimensional K (D.rowBot.homology i)›
  D.twistShortComplex_shortExact.finrank_homology₂_le i

variable {D} {E F : ι → Prop} (h : D.Eliminates E F)
include h

/-- **The derived complex has finite-dimensional cohomology where both rows do.** -/
theorem finiteDimensional_derived_homology : FiniteDimensional K ((D.derived E F).homology i) :=
  have := D.finiteDimensional_twistComplex_homology i
  (D.derivedHomologyIso h i).toLinearEquiv.symm.finiteDimensional

/-- **`dim Hⁱ(derived) ≤ dim Hⁱ(V) + dim Hⁱ(Ṽ)`.** [ArnoldHu2021], Theorem 6 -/
theorem finrank_derived_homology_le :
    finrank K ((D.derived E F).homology i) ≤
      finrank K (D.rowTop.homology i) + finrank K (D.rowBot.homology i) := by
  rw [(D.derivedHomologyIso h i).toLinearEquiv.finrank_eq]
  exact D.finrank_twistComplex_homology_le i

end Field

/-! ## The complex with weak symmetries (5.1) -/

variable (D)

/-- **(5.1) is an elimination**: at the index `i` before `j`, the elimination of `Vʲ` is
`Γ = {(σ, φ) | dσ = Sφ}` of the segment at `i → j → k`. [QuennevilleBelair2015], §5.1 -/
theorem Γ_eq_segment_Γ {i j k : ι} (hij : c.Rel i j) (hne : i ≠ j) :
    D.Γ (· = j) i = (D.segment i j k).Γ := by
  obtain rfl := c.next_eq' hij
  ext x
  rw [mem_Γ, Segment.mem_Γ]
  simp [hne, segment, sub_eq_zero]

/-! ## The BGG complex of Arnold and Hu -/

section Up

variable {V Vt : ℤ → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  [∀ i, AddCommGroup (Vt i)] [∀ i, Module R (Vt i)] (D : Data R (ComplexShape.up ℤ) V Vt)

/-- **The injectivity/surjectivity condition at `J`**: `Sⁱ : Ṽⁱ → Vⁱ⁺¹` is injective for
`i < J` and surjective for `i ≥ J`. [ArnoldHu2021], (23) also asks `Sᴶ` injective. -/
def InjSurj (J : ℤ) : Prop :=
  (∀ i < J, Function.Injective (D.S i (i + 1))) ∧ ∀ i, J ≤ i → Function.Surjective (D.S i (i + 1))

/-- **The BGG complex** of [ArnoldHu2021], (24)–(26): eliminate the top spaces after `J` and
the bottom spaces before `J`. -/
abbrev bgg (J : ℤ) : CochainComplex (ModuleCat.{v} R) ℤ := D.derived (J < ·) (· < J)

variable {D}

/-- **The elimination hypotheses of the BGG complex** reduce to the onto-modulo-`d` conditions
after `J`, `R(dʲ⁻¹) + R(Sʲ⁻¹) = Vʲ` (regular decompositions, in the Sobolev setting), once the `Sⁱ`
before `J` are one-to-one. -/
theorem eliminates_bgg {J : ℤ} (hinj : ∀ i < J, Function.Injective (D.S i (i + 1)))
    (htop : ∀ j, J < j → LinearMap.range (D.d (j - 1) j) ⊔ LinearMap.range (D.S (j - 1) j) = ⊤) :
    D.Eliminates (J < ·) (· < J) where
  top j hj := by
    rw [CochainComplex.prev]
    exact htop j hj
  bot i hi := by
    rw [CochainComplex.next, LinearMap.ker_eq_bot.2 (hinj i hi), inf_bot_eq]
  disjoint i j hij hi hj := by
    change i + 1 = j at hij
    omega

theorem InjSurj.eliminates {J : ℤ} (h : D.InjSurj J) : D.Eliminates (J < ·) (· < J) :=
  eliminates_bgg h.1 fun j hj => by
    have := h.2 (j - 1) (by omega)
    rw [sub_add_cancel] at this
    rw [LinearMap.range_eq_top.2 this, sup_top_eq]

variable (D) in
/-- Before `J`, nothing is eliminated from the top: `Γⁱ = Vⁱ × Ṽⁱ`. -/
theorem bgg_Γ_of_lt {J i : ℤ} (hi : i < J) : D.Γ (J < ·) i = ⊤ :=
  eq_top_iff.2 fun x _ => by
    rw [mem_Γ, CochainComplex.next]
    exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

variable (D) in
/-- At `J`: `Γᴶ = {(σ, φ) | dσ = Sᴶφ}`, the graph of `(Sᴶ)⁻¹ d` when `Sᴶ` is bijective. -/
theorem mem_bgg_Γ_self {J : ℤ} {x : V J × Vt J} :
    x ∈ D.Γ (J < ·) J ↔ D.d J (J + 1) x.1 = D.S J (J + 1) x.2 := by
  rw [mem_Γ, CochainComplex.next]
  simp [sub_eq_zero]

variable (D) in
/-- After `J`: `Γⁱ = 0 × N(Sⁱ)`. -/
theorem mem_bgg_Γ_of_gt {J i : ℤ} (hi : J < i) {x : V i × Vt i} :
    x ∈ D.Γ (J < ·) i ↔ x.1 = 0 ∧ D.S i (i + 1) x.2 = 0 := by
  rw [mem_Γ, CochainComplex.next]
  simp only [hi, true_implies, twist_apply, show J < i + 1 by omega]
  constructor
  · rintro ⟨h1, h2⟩
    rw [h1, map_zero, zero_sub, neg_eq_zero] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h1, h2, map_zero, sub_zero]⟩

variable (D) in
/-- Up to `J`, the exact part is `R(Sⁱ⁻¹) × Ṽⁱ` before `J` and `{(-Sψ, d̃ψ)}` at `J`, so the
derived space is `Vⁱ / R(Sⁱ⁻¹)` before `J` (and at `J` when `Sᴶ` is injective). -/
theorem mem_bgg_Δ_of_le {J i : ℤ} (hi : i ≤ J) {x : V i × Vt i} :
    x ∈ D.Δ (· < J) i ↔ ∃ φ ψ, (i < J ∨ φ = 0) ∧
      x = (-D.S (i - 1) i ψ, φ + D.dt (i - 1) i ψ) := by
  rw [mem_Δ, CochainComplex.prev]
  simp only [show i - 1 < J by omega, true_or, true_and, twist_apply, map_zero, zero_sub,
    Prod.mk_add_mk, zero_add]

variable (D) in
/-- After `J`, nothing is eliminated from the bottom: `Δⁱ = 0`, so the derived space is
`Γⁱ = 0 × N(Sⁱ)`. -/
theorem bgg_Δ_of_gt {J i : ℤ} (hi : J < i) : D.Δ (· < J) i = ⊥ :=
  eq_bot_iff.2 fun x hx => by
    obtain ⟨φ, ψ, hφ, hψ, rfl⟩ := (D.mem_Δ _).1 hx
    obtain rfl : φ = 0 := hφ.resolve_left (by omega)
    obtain rfl : ψ = 0 := hψ.resolve_left (by rw [CochainComplex.prev]; omega)
    simp

variable (D) in
/-- After `J`, `Γⁱ = 0 × N(Sⁱ)` is `N(Sⁱ)`: `x ↦ x₂`. -/
def bggΓEquivKer {J i : ℤ} (hi : J < i) : D.Γ (J < ·) i ≃ₗ[R] LinearMap.ker (D.S i (i + 1)) where
  toFun x := ⟨(x : V i × Vt i).2, ((D.mem_bgg_Γ_of_gt hi).1 x.2).2⟩
  invFun u := ⟨(0, u), (D.mem_bgg_Γ_of_gt hi).2 ⟨rfl, u.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := Subtype.ext (Prod.ext ((D.mem_bgg_Γ_of_gt hi).1 x.2).1.symm rfl)
  right_inv _ := rfl

variable (D) in
/-- At `J`, when `Sᴶ` is bijective, `Γᴶ = {(σ, (Sᴶ)⁻¹ dσ)}` is `Vᴶ`: `x ↦ x₁`. -/
def bggΓEquivOfBijective {J : ℤ} (hS : Function.Bijective (D.S J (J + 1))) :
    D.Γ (J < ·) J ≃ₗ[R] V J where
  toFun x := (x : V J × Vt J).1
  invFun σ := ⟨(σ, (LinearEquiv.ofBijective _ hS).symm (D.d J (J + 1) σ)),
    (D.mem_bgg_Γ_self).2 ((LinearEquiv.ofBijective _ hS).apply_symm_apply _).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := Subtype.ext (Prod.ext rfl (by
    change (LinearEquiv.ofBijective _ hS).symm (D.d J (J + 1) (x : V J × Vt J).1) = _
    rw [(D.mem_bgg_Γ_self).1 x.2]
    exact (LinearEquiv.ofBijective _ hS).symm_apply_apply _))
  right_inv _ := rfl

variable (D) in
/-- Before `J`: `x ∈ Δⁱ` iff `x₁ ∈ R(Sⁱ⁻¹)`. -/
theorem mem_bgg_Δ_of_lt {J i : ℤ} (hi : i < J) {x : V i × Vt i} :
    x ∈ D.Δ (· < J) i ↔ x.1 ∈ LinearMap.range (D.S (i - 1) i) := by
  rw [D.mem_bgg_Δ_of_le hi.le]
  constructor
  · rintro ⟨φ, ψ, -, rfl⟩
    exact ⟨-ψ, by simp⟩
  · rintro ⟨ψ, hψ⟩
    refine ⟨x.2 - D.dt (i - 1) i (-ψ), -ψ, Or.inl hi, Prod.ext ?_ ?_⟩
    · simp [hψ]
    · simp

variable (D) in
/-- **Before `J` the derived space is `Vⁱ / R(Sⁱ⁻¹)`**, `[(σ, φ)] ↦ [σ]`. [ArnoldHu2021], (24) -/
def bggXEquivOfLt {J i : ℤ} (hi : i < J) :
    (D.Γ (J < ·) i ⧸ (D.Δ (· < J) i).comap (D.Γ (J < ·) i).subtype) ≃ₗ[R]
      (V i ⧸ LinearMap.range (D.S (i - 1) i)) :=
  (Submodule.quotEquivOfEq _ _ (by
      ext x
      rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, D.mem_bgg_Δ_of_lt hi]
      rfl)).trans
    (LinearMap.quotKerEquivOfSurjective
      ((LinearMap.range (D.S (i - 1) i)).mkQ ∘ₗ LinearMap.fst R (V i) (Vt i) ∘ₗ
        (D.Γ (J < ·) i).subtype)
      fun q => by
        obtain ⟨σ, rfl⟩ := Submodule.mkQ_surjective _ q
        exact ⟨⟨(σ, 0), by rw [D.bgg_Γ_of_lt hi]; trivial⟩, rfl⟩)

theorem bggXEquivOfLt_mk {J i : ℤ} (hi : i < J) (x : D.Γ (J < ·) i) :
    D.bggXEquivOfLt hi (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (x : V i × Vt i).1 := rfl

variable (D) in
/-- **At `J`, when `Sᴶ` is bijective, the derived space is `Vᴶ / R(Sᴶ⁻¹)`**,
`[(σ, (Sᴶ)⁻¹ dσ)] ↦ [σ]`. [ArnoldHu2021], (25) -/
def bggXEquivOfBijective {J : ℤ} (hS : Function.Bijective (D.S J (J + 1))) :
    (D.Γ (J < ·) J ⧸ (D.Δ (· < J) J).comap (D.Γ (J < ·) J).subtype) ≃ₗ[R]
      (V J ⧸ LinearMap.range (D.S (J - 1) J)) :=
  Submodule.Quotient.equiv _ _ (D.bggΓEquivOfBijective hS) (by
    ext σ
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨φ, ψ, hφ, hx⟩ := (D.mem_bgg_Δ_of_le le_rfl).1 hx
      refine ⟨-ψ, ?_⟩
      change _ = (x : V J × Vt J).1
      rw [hx]
      simp
    · rintro ⟨ψ, rfl⟩
      refine ⟨(D.bggΓEquivOfBijective hS).symm (D.S (J - 1) J ψ), ?_,
        (D.bggΓEquivOfBijective hS).apply_symm_apply _⟩
      rw [D.mem_bgg_Δ_of_le le_rfl]
      refine ⟨0, -ψ, Or.inr rfl, Prod.ext (by simp; rfl) ?_⟩
      change (LinearEquiv.ofBijective _ hS).symm (D.d J (J + 1) (D.S (J - 1) J ψ)) = _
      rw [(LinearEquiv.ofBijective _ hS).symm_apply_eq]
      have := D.anticomm (J - 1) J (J + 1) ψ
      simp only [LinearEquiv.ofBijective_apply, zero_add, map_neg]
      rw [this])

theorem bggXEquivOfBijective_mk {J : ℤ} (hS : Function.Bijective (D.S J (J + 1)))
    (x : D.Γ (J < ·) J) :
    D.bggXEquivOfBijective hS (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (x : V J × Vt J).1 := rfl

/-- **The BGG complex has the cohomology of the twisted complex** [ArnoldHu2021], §5.2, under
the injectivity/surjectivity condition at `J`. -/
def bggHomologyIso {J : ℤ} (h : D.InjSurj J) (i : ℤ) :
    (D.bgg J).homology i ≅ D.twistComplex.homology i :=
  derivedHomologyIso h.eliminates i

/-- **The BGG complex is exact when both rows are.** [ArnoldHu2021], §5.2 -/
theorem bgg_acyclic {J : ℤ} (h : D.InjSurj J) (hV : D.rowTop.Acyclic) (hVt : D.rowBot.Acyclic) :
    (D.bgg J).Acyclic :=
  derived_acyclic h.eliminates hV hVt

/-! ### Non-vacuity -/

variable (R) in
/-- **Two copies of the zero complex `R` on `ℤ`, connected by the identity** `Sⁱ = id : Ṽⁱ → Vⁱ⁺¹`:
BGG data with nonzero connecting maps, satisfying the injectivity/surjectivity condition at every
`J` (`injSurj_idShift`). -/
def idShift : Data R (ComplexShape.up ℤ) (fun _ => R) (fun _ => R) where
  d _ _ := 0
  dt _ _ := 0
  S i j := if i + 1 = j then LinearMap.id else 0
  shape_d _ _ _ := rfl
  shape_dt _ _ _ := rfl
  shape_S _ _ h := ite_eq_right h
  d_comp_d _ _ _ _ := rfl
  dt_comp_dt _ _ _ _ := rfl
  anticomm _ _ _ _ := by simp

variable (R) in
/-- **`idShift` satisfies the injectivity/surjectivity condition at every `J`**, so its BGG
complexes `(idShift R).bgg J` have the cohomology of its twisted complex (`bggHomologyIso`). -/
theorem injSurj_idShift (J : ℤ) : (idShift R).InjSurj J := by
  have h : ∀ i : ℤ, (idShift R).S i (i + 1) = LinearMap.id := fun _ => ite_eq_left rfl
  exact ⟨fun i _ => by rw [h]; exact Function.injective_id,
    fun i _ => by rw [h]; exact Function.surjective_id⟩

end Up

end Data

end Feec.BGG
