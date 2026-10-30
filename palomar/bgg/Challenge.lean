module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# The algebraic Bernstein–Gelfand–Gelfand construction

A **stacked diagram** over a ring `R` is a pair of cochain complexes of `R`-modules
`(V, d)` and `(Ṽ, d̃)` on `ℤ` with connecting maps `Sⁱ : Ṽⁱ → Vⁱ⁺¹` such that `d S = -S d̃`;
with the sign convention of Mathlib for the shift (`(V⟦1⟧)ⁱ = Vⁱ⁺¹`, differential `-d`), this is
exactly a morphism of cochain complexes `S : Ṽ ⟶ V⟦1⟧`. The **twisted complex** `T` has
`Tⁱ = Vⁱ × Ṽⁱ` and differential `(σ, φ) ↦ (dσ - Sφ, d̃φ)` ([ArnoldHu2021], (58)–(59)); it is an
extension `0 → V → T → Ṽ → 0` of the bottom row by the top row.

The **BGG complex** at the index `J` eliminates from `T` the top spaces `Vⁱ`, `i > J`, against
the bottom spaces `Ṽⁱ⁻¹`, and the bottom spaces `Ṽⁱ`, `i < J`, against the top spaces `Vⁱ⁺¹`
([ArnoldHu2021], (24)–(26)). It is the subquotient `Γ / Δ` of `T`:

* `Γⁱ = {(σ, φ) ∈ Tⁱ | σ = 0 if i > J, dσ = Sφ if i + 1 > J}`, a subcomplex of `T`;
* `Δⁱ ⊆ Tⁱ` is spanned by `0 × Ṽⁱ` if `i < J` and by its image `{(-Sψ, d̃ψ) | ψ ∈ Ṽⁱ⁻¹}` under
  the twisted differential if `i - 1 < J`, a subcomplex of `T`.

Its spaces are `Vⁱ / R(Sⁱ⁻¹)` for `i < J`, `{(σ, φ) | dσ = Sᴶφ} / {(-Sψ, d̃ψ)}` for `i = J`
(`Vᴶ / R(Sᴶ⁻¹)` when `Sᴶ` is bijective) and `N(Sⁱ)` for `i > J`, with the differentials
induced by `d`, `σ ↦ d̃ (Sᴶ)⁻¹ dσ` and `d̃` ([ArnoldHu2021], (24)–(26)).

The theorem (`FEEC.bggCohomology`): if `Sⁱ` is injective for `i < J` and surjective for `i ≥ J`
(the condition [ArnoldHu2021], (23) also asks `Sᴶ` injective), the inclusion `Γ → T` and the
projection `Γ → Γ / Δ` are quasi-isomorphisms, so **the BGG complex has the cohomology of the
twisted complex** in every degree ([ArnoldHu2021], §5.2); the twisted complex is an extension of
`Ṽ` by `V`, whose long exact sequence in cohomology relates it to the rows; and the BGG complex
is exact when both rows are. Complexes of any length are included (rows vanishing outside a
window).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3 ((19)–(26), Theorem 6:
  the input diagram and the output complex) and §5 ((58)–(59): the twisted complex; §5.2:
  splitting off an exact subcomplex)
* [I. N. Bernstein, I. M. Gelfand, S. I. Gelfand, *Differential operators on the base affine space and a study of g-modules*][BernsteinGelfandGelfand1975]
  (the BGG resolution)
* [A. Čap, J. Slovák, V. Souček, *Bernstein–Gelfand–Gelfand sequences*][CapSlovakSoucek2001]
  (BGG sequences in differential geometry)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §11 (the elasticity complex from two de Rham complexes)

Bibliography: [references.bib](../../docs/references.bib)
-/

open CategoryTheory

@[expose] public noncomputable section

universe u v

namespace FEEC

/-! ### Subcomplexes and quotient complexes of complexes of modules -/

section Sub

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{v} R) c) (P : ∀ i, Submodule R (K.X i))
  (hP : ∀ i j, ∀ x ∈ P i, K.d i j x ∈ P j)

/-- The **subcomplex** of a family of submodules `P i ⊆ Kⁱ` stable under the differentials. -/
def subcomplex : HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (P i)
  d i j := ModuleCat.ofHom ((K.d i j).hom.restrict (hP i j))
  shape i j h := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
    change K.d i j x = 0
    rw [K.shape i j h]; rfl))
  d_comp_d' i j k _ _ := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
    change K.d j k (K.d i j x) = 0
    rw [← ModuleCat.comp_apply, K.d_comp_d]; rfl))

/-- The **quotient complex** `K / P` by a family of submodules stable under the differentials. -/
def quotient : HomologicalComplex (ModuleCat.{v} R) c where
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

/-- The inclusion of the subcomplex. -/
def subcomplexι : subcomplex K P hP ⟶ K where
  f i := ModuleCat.ofHom (P i).subtype
  comm' _ _ _ := rfl

/-- The projection onto the quotient complex. -/
def quotientπ : K ⟶ quotient K P hP where
  f i := ModuleCat.ofHom (P i).mkQ
  comm' _ _ _ := rfl

end Sub

/-! ### Stacked diagrams, the twisted complex and the BGG complex -/

namespace BGG

variable {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
  (S : Vt ⟶ V⟦(1 : ℤ)⟧)

/-- The connecting map `Sⁱ : Ṽⁱ → Vⁱ⁺¹` as a map `Ṽⁱ → Vʲ`, zero unless `j = i + 1`. -/
def conn (i j : ℤ) : Vt.X i →ₗ[R] V.X j :=
  if h : i + 1 = j then (S.f i ≫ (V.XIsoOfEq h).hom).hom else 0

/-- `d S = -S d̃`: `S` is a morphism `Ṽ ⟶ V⟦1⟧`. -/
theorem d_conn (i j k : ℤ) (φ : Vt.X i) :
    V.d j k (conn S i j φ) = -conn S j k (Vt.d i j φ) := by
  by_cases hij : i + 1 = j
  · subst hij
    by_cases hjk : i + 1 + 1 = k
    · subst hjk
      have := congrArg (fun f => f.hom φ) (S.comm i (i + 1))
      simp only [CochainComplex.shiftFunctor_obj_d', Int.negOnePow_one] at this
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Units.neg_smul,
        one_smul] at this
      simp only [conn, dite_eq_left, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
      exact neg_eq_iff_eq_neg.1 this
    · simp [conn, hjk]
  · simp [conn, hij]

/-- The twisted differential `(σ, φ) ↦ (dσ - Sφ, d̃φ)` on `Vⁱ × Ṽⁱ`. -/
def twist (i j : ℤ) : V.X i × Vt.X i →ₗ[R] V.X j × Vt.X j :=
  ((V.d i j).hom ∘ₗ LinearMap.fst R _ _ - conn S i j ∘ₗ LinearMap.snd R _ _).prod
    ((Vt.d i j).hom ∘ₗ LinearMap.snd R _ _)

theorem twist_twist (i j k : ℤ) (x : V.X i × Vt.X i) : twist S j k (twist S i j x) = 0 := by
  refine Prod.ext ?_ ?_
  · change V.d j k (V.d i j x.1 - conn S i j x.2) - conn S j k (Vt.d i j x.2) = 0
    rw [map_sub, d_conn, ← ModuleCat.comp_apply, V.d_comp_d]
    simp
  · change Vt.d j k (Vt.d i j x.2) = 0
    rw [← ModuleCat.comp_apply, Vt.d_comp_d]; rfl

theorem twist_of_ne {i j : ℤ} (h : i + 1 ≠ j) : twist S i j = 0 := by
  ext x <;> simp [twist, conn, h]

/-- **The twisted complex** `T`, `Tⁱ = Vⁱ × Ṽⁱ`, `(σ, φ) ↦ (dσ - Sφ, d̃φ)`. -/
def twisted : CochainComplex (ModuleCat.{v} R) ℤ where
  X i := ModuleCat.of R (V.X i × Vt.X i)
  d i j := ModuleCat.ofHom (twist S i j)
  shape i j h := by rw [twist_of_ne S h]; rfl
  d_comp_d' i j k _ _ := ModuleCat.hom_ext (LinearMap.ext fun x => twist_twist S i j k x)

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

/-- `Γⁱ = {(σ, φ) | σ = 0 if i > J, dσ = Sφ if i + 1 > J}`: the elimination of the top spaces
after `J`. -/
def Γ (J i : ℤ) : Submodule R (V.X i × Vt.X i) :=
  (⨅ _ : J < i, LinearMap.ker (LinearMap.fst R _ _)) ⊓
    ⨅ _ : J < i + 1, LinearMap.ker (LinearMap.fst R _ _ ∘ₗ twist S i (i + 1))

/-- `Δⁱ = 0 × Ṽⁱ (i < J) + {(-Sψ, d̃ψ) | ψ ∈ Ṽⁱ⁻¹} (i - 1 < J)`: the exact part carried by the
bottom spaces before `J`. -/
def Δ (J i : ℤ) : Submodule R (V.X i × Vt.X i) :=
  (⨆ _ : i < J, LinearMap.range (LinearMap.inr R _ _)) ⊔
    ⨆ _ : i - 1 < J, (LinearMap.range (LinearMap.inr R _ _)).map (twist S (i - 1) i)

theorem twist_mem_Γ (J i j : ℤ) {x : V.X i × Vt.X i} (hx : x ∈ Γ S J i) :
    twist S i j x ∈ Γ S J j := by
  by_cases hij : i + 1 = j
  · subst hij
    refine Submodule.mem_inf.2 ⟨(Submodule.mem_iInf _).2 fun h => ?_,
      (Submodule.mem_iInf _).2 fun _ => ?_⟩
    · exact (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hx).2 h
    · change (twist S (i + 1) (i + 1 + 1) (twist S i (i + 1) x)).1 = 0
      rw [twist_twist]; rfl
  · rw [twist_of_ne S hij]; exact zero_mem _

theorem twist_mem_Δ (J i j : ℤ) {x : V.X i × Vt.X i} (hx : x ∈ Δ S J i) :
    twist S i j x ∈ Δ S J j := by
  by_cases hij : i + 1 = j
  · subst hij
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    have hb : twist S i (i + 1) b = 0 := by
      by_cases h : i - 1 < J
      · rw [iSup_pos h] at hb
        obtain ⟨y, -, rfl⟩ := hb
        exact twist_twist S _ _ _ y
      · rw [iSup_neg h, Submodule.mem_bot] at hb
        rw [hb, map_zero]
    rw [map_add, hb, add_zero]
    by_cases h : i < J
    · rw [iSup_pos h] at ha
      obtain ⟨φ, rfl⟩ := ha
      refine Submodule.mem_sup_right ?_
      rw [iSup_pos (by rw [add_sub_cancel_right]; exact h)]
      have key : ∀ i', i' = i → twist S i (i + 1) (LinearMap.inr R _ _ φ) ∈
          (LinearMap.range (LinearMap.inr R _ _)).map (twist S i' (i + 1)) := by
        rintro _ rfl; exact ⟨_, ⟨φ, rfl⟩, rfl⟩
      exact key _ (add_sub_cancel_right i 1)
    · rw [iSup_neg h, Submodule.mem_bot] at ha
      rw [ha, map_zero]; exact zero_mem _
  · rw [twist_of_ne S hij]; exact zero_mem _

/-- The subcomplex `Γ ⊆ T`. -/
def bggΓ (J : ℤ) : CochainComplex (ModuleCat.{v} R) ℤ :=
  subcomplex (twisted S) (Γ S J) fun i j _ hx => twist_mem_Γ S J i j hx

/-- **The BGG complex** `Γ / Δ` at `J` ([ArnoldHu2021], (24)–(26)). -/
def bgg (J : ℤ) : CochainComplex (ModuleCat.{v} R) ℤ :=
  quotient (bggΓ S J) (fun i => (Δ S J i).comap (Γ S J i).subtype)
    fun i j _ hx => twist_mem_Δ S J i j hx

/-- The inclusion `Γ → T`. -/
def bggΓι (J : ℤ) : bggΓ S J ⟶ twisted S := subcomplexι _ _ _

/-- The projection `Γ → Γ / Δ`. -/
def bggπ (J : ℤ) : bggΓ S J ⟶ bgg S J := quotientπ _ _ _

/-- **The BGG verdict at `J`.** -/
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

end BGG

/-! ### The theorem -/

/-- **The BGG construction** ([ArnoldHu2021], §5.2). For a stacked diagram `S : Ṽ ⟶ V⟦1⟧` of
cochain complexes of modules over any ring, with `Sⁱ` injective for `i < J` and surjective for
`i ≥ J`, the BGG complex at `J` has the cohomology of the twisted complex
(`BGG.Verdict`). -/
theorem bggCohomology {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i → Function.Surjective (S.f i)) : BGG.Verdict S J := by
  sorry

end FEEC
