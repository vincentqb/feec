module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Bernstein–Gelfand–Gelfand complexes and their discretization with weak symmetry

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

The theorems (hypotheses: `Sⁱ` injective for `i < J` and onto modulo `d` for `i ≥ J`,
`R(dⁱ) + R(Sⁱ) = Vⁱ⁺¹`, weaker than the condition (23) of [ArnoldHu2021]; exact hypotheses in
the docstrings):

* `FEEC.bggCohomology` (§5.2): `Γ → T` and `Γ → Γ / Δ` are quasi-isomorphisms.
* `FEEC.bggIdentification` ((24)–(26), every `S`, `J`): `Γ / Δ` is the output complex, `V / R(S)`
  before `J`, `N(S)` after `J`, with the differential `d̃ (Sᴶ)⁻¹ d` at `J`.
* `FEEC.bggFinrank` (Theorem 6, (27)): `dim Hⁱ(Γ / Δ) ≤ dim Hⁱ(V) + dim Hⁱ(Ṽ)`, with equality
  iff `Sⁱ⁻¹` and `Sⁱ` induce zero on cohomology.
* `FEEC.bggSum` (Theorem 7, Proposition 1): under `S = dK - Kd̃` ((28)), the BGG complex has the
  cohomology of the sum complex `V × Ṽ`.
* `FEEC.bggExplicit` ((30), Theorem 7, Corollary 1): the explicit map `BGG.sumMap` is a
  quasi-isomorphism from the sum complex carrying cohomology representatives to representatives.
* `FEEC.bggHilbert` (Theorem 6 and the remark after it): for bounded Hilbert rows, `Γ / Δ` with
  the quotient norm is a bounded Hilbert complex, with closed ranges where the rows have
  finite-dimensional cohomology.
* `FEEC.bggOrthogonal` ((24)–(31), Theorem 7, Corollary 1): for bounded Hilbert rows under (23),
  with closed ranges of `sⁱ` for `i < J`, the orthogonal output complex of [ArnoldHu2021] with the
  Moore–Penrose form of (30).

Complexes of any length are included (rows vanishing outside a window). Non-vacuity:
`BGG.hypotheses_id` (`S = 𝟙 : V⟦1⟧ ⟶ V⟦1⟧`) and `BGG.hypotheses_bounded_id` (`sⁱ = id`,
`d̃ⁱ = -dⁱ⁺¹`) satisfy the hypotheses at every `J`.

**Discretization with weak symmetry** ([QuennevilleBelair2015], Ch. 5). For unbounded rows
(segments `W⁰ → W¹ → W²`, `W̃⁰ → W̃¹ → W̃²` of unbounded operators, `WeakSymmetryData`),
eliminating `V¹` against `Ṽ⁰` weakly, by a Lagrange multiplier `λ`, gives the complex with weak
symmetry `Γ → Ṽ¹ → W² × W̃²`, `Γ = {(σ, φ) | dσ = S⁰φ}` ([QuennevilleBelair2015], (5.1)), and
its mixed Hodge Laplacian, the saddle point problem (5.3): find `σ ∈ V⁰`, `φ ∈ Ṽ⁰`, `u ∈ Ṽ¹`
and `λ` with `⟪σ, τ⟫ - ⟪u, d̃ψ⟫ - ⟪λ, dτ - S⁰ψ⟫ = 0` for all `τ`, `ψ`,
`⟪d̃φ, v⟫ + ⟪S¹u, S¹v⟫ + ⟪d̃u, d̃v⟫ = F(v)` for all `v`, and `dσ = S⁰φ`. In `ℝ³`, with the rows
`H̊¹ → H̊(curl) → L²` and `S⁰ = I`, `S¹ = 2 vskw` in vector proxies, this is the complex of the
linearized Einstein equations, `Γ = {(σ, grad σ) | σ ∈ H̊²}`: a conforming discretization of `Γ`
needs `C¹` elements, which the multiplier avoids. A discretization
(`WeakSymmetryData.Discretization`) consists of subcomplexes of both rows with bounded cochain
projections `π`, `π̃`; the method (5.6) replaces `S` by `Sₕ = πS` (a variational crime), and
the compatibility condition (5.4) `π¹S⁰π̃⁰ = π¹S⁰` replaces the surjectivity of `S⁰ₕ`.

* `FEEC.bggWeakSymmetry` (Prop 5.4, Thm 5.5): under uniform constants (Poincaré inequalities,
  exactness, the Hodge and regular decompositions, `‖S‖ ≤ C`, `‖π‖ ≤ C`) and (5.4), the discrete
  problem is uniquely solvable, and under consistency of `Sₕ` at the order `h` the error is
  bounded by the projection error plus `h²` times the data plus `‖(S¹ - S¹ₕ)u‖²`.
* `FEEC.bggWeakSymmetry_nonvacuous`: data on `ℝ` satisfying all the hypotheses, with a solution
  of (5.3) whose four unknowns are nonzero.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3 ((19)–(31), Theorems 6
  and 7, Proposition 1, Corollary 1: the input diagram, the output complex and its cohomology)
  and §5 ((58)–(59): the twisted complex; §5.2: splitting off an exact subcomplex)
* [I. N. Bernstein, I. M. Gelfand, S. I. Gelfand, *Differential operators on the base affine space and a study of g-modules*][BernsteinGelfandGelfand1975]
  (the BGG resolution)
* [A. Čap, J. Slovák, V. Souček, *Bernstein–Gelfand–Gelfand sequences*][CapSlovakSoucek2001]
  (BGG sequences in differential geometry)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §11 (the elasticity complex from two de Rham complexes)
* [D. N. Arnold, R. S. Falk, R. Winther, *Mixed finite element methods for linear elasticity with weakly imposed symmetry*][AFW2007]
  (weak symmetry from the same two-row diagram)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3 (stability of Hilbert complexes and their discretizations)
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], Lemma 2.4
  (regular decompositions)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 5 ((5.1)–(5.6), Props 5.3, 5.4, Thm 5.5: the complex with weak symmetry and its
  discretization)

Bibliography: [references.bib](../../docs/references.bib)
-/

open CategoryTheory
open scoped InnerProductSpace

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

theorem conn_succ (i : ℤ) : conn S i (i + 1) = (S.f i).hom := by
  simp [conn]

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

/-! ### The spaces of Arnold and Hu: `Vⁱ / R(Sⁱ⁻¹)` before `J`, `N(Sⁱ)` after `J` -/

/-- `R(Sⁱ⁻¹) ⊆ Vⁱ`. -/
def rangeS (i : ℤ) : Submodule R (V.X i) := LinearMap.range (conn S (i - 1) i)

theorem conn_mem_rangeS (i j : ℤ) (φ : Vt.X i) : conn S i j φ ∈ rangeS S j := by
  by_cases h : i + 1 = j
  · obtain rfl : i = j - 1 := eq_sub_of_add_eq h
    exact ⟨φ, rfl⟩
  · simp [conn, h]

/-- The quotient complex `V / R(S)`, `Vⁱ / R(Sⁱ⁻¹)` with the differentials induced by `d`. -/
def quotS : CochainComplex (ModuleCat.{v} R) ℤ :=
  quotient V (rangeS S) fun i j _ ⟨ψ, h⟩ => h ▸ d_conn S (i - 1) i j ψ ▸
    neg_mem (conn_mem_rangeS S i j _)

/-- The subcomplex `N(S) ⊆ Ṽ`, `N(Sⁱ)` with the differentials induced by `d̃`. -/
def kerS : CochainComplex (ModuleCat.{v} R) ℤ :=
  subcomplex Vt (fun i => LinearMap.ker (S.f i).hom) fun i j φ hφ => by
    have h := d_conn S i j (j + 1) φ
    by_cases hij : i + 1 = j
    · subst hij
      rw [conn_succ, conn_succ, LinearMap.mem_ker.1 hφ, map_zero, eq_comm, neg_eq_zero] at h
      exact h
    · rw [Vt.shape i j hij]; exact zero_mem _

theorem fst_mem_rangeS (J i : ℤ) {x : V.X i × Vt.X i} (hx : x ∈ Δ S J i) : x.1 ∈ rangeS S i := by
  refine (sup_le (iSup_le fun _ => ?_) (iSup_le fun _ => ?_) : Δ S J i ≤ (rangeS S i).comap
    (LinearMap.fst R _ _)) hx
  · rintro _ ⟨φ, rfl⟩; exact (rangeS S i).zero_mem
  · rintro _ ⟨_, ⟨ψ, rfl⟩, rfl⟩
    simpa [twist] using neg_mem (conn_mem_rangeS S (i - 1) i ψ)

/-- `[(σ, φ)] ↦ [σ]`, the cochain map `Γ / Δ → V / R(S)` ([ArnoldHu2021], (24)–(26) up to `J`). -/
def toQuotS (J : ℤ) : bgg S J ⟶ quotS S where
  f i := ModuleCat.ofHom (Submodule.mapQ _ _ (LinearMap.fst R _ _ ∘ₗ (Γ S J i).subtype)
    fun _ hx => fst_mem_rangeS S J i hx)
  comm' i j _ := ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x =>
    (Submodule.Quotient.eq _).2 (by
      change V.d i j x.1.1 - (V.d i j x.1.1 - conn S i j x.1.2) ∈ rangeS S j
      rw [sub_sub_cancel]; exact conn_mem_rangeS S i j _)))

theorem inr_mem_Γ (J i : ℤ) (φ : LinearMap.ker (S.f i).hom) :
    ((0 : V.X i), (φ : Vt.X i)) ∈ Γ S J i :=
  Submodule.mem_inf.2 ⟨(Submodule.mem_iInf _).2 fun _ => rfl, (Submodule.mem_iInf _).2 fun _ => by
    simp [twist, conn_succ]⟩

/-- `φ ↦ [(0, φ)]`, the cochain map `N(S) → Γ / Δ` ([ArnoldHu2021], (24)–(26) after `J`). -/
def ofKerS (J : ℤ) : kerS S ⟶ bgg S J where
  f i := ModuleCat.ofHom (Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (Γ S J i)
    (LinearMap.inr R _ _ ∘ₗ (LinearMap.ker (S.f i).hom).subtype) (inr_mem_Γ S J i))
  comm' i j _ := ModuleCat.hom_ext (LinearMap.ext fun φ => congrArg Submodule.Quotient.mk
    (Subtype.ext (Prod.ext (by
      change V.d i j 0 - conn S i j φ.1 = 0
      by_cases h : i + 1 = j
      · subst h; simpa [conn_succ] using φ.2
      · simp [conn, h]) rfl)))

/-- **The spaces and differentials of the BGG complex are those of [ArnoldHu2021], (24)–(26).**
The cochain maps `toQuotS : Γ / Δ → V / R(S)` and `ofKerS : N(S) → Γ / Δ` are bijective in
degrees `i < J` and `i > J` respectively, and in degree `J` when `Sᴶ` is bijective; the
differential from `J` to `J + 1` is then `[σ] ↦ d̃ (Sᴶ)⁻¹ dσ`. Hence the BGG complex is
`Vⁱ / R(Sⁱ⁻¹)` with the differentials induced by `d` up to `J`, `N(Sⁱ)` with `d̃` after `J`. -/
structure Identification (J : ℤ) : Prop where
  /-- `Γⁱ / Δⁱ ≅ Vⁱ / R(Sⁱ⁻¹)` before `J` -/
  lt : ∀ i < J, Function.Bijective ((toQuotS S J).f i)
  /-- `Γᴶ / Δᴶ ≅ Vᴶ / R(Sᴶ⁻¹)` when `Sᴶ` is bijective -/
  self : Function.Bijective (S.f J) → Function.Bijective ((toQuotS S J).f J)
  /-- `N(Sⁱ) ≅ Γⁱ / Δⁱ` after `J` -/
  gt : ∀ i, J < i → Function.Bijective ((ofKerS S J).f i)
  /-- the differential at `J` is `[σ] ↦ d̃φ` with `Sᴶφ = dσ` -/
  d_self : Function.Injective (S.f J) → ∀ (x : (bgg S J).X J) (σ : V.X J) (φ : Vt.X J),
    (toQuotS S J).f J x = Submodule.Quotient.mk σ → conn S J (J + 1) φ = V.d J (J + 1) σ →
      ∃ y : (kerS S).X (J + 1), (ofKerS S J).f (J + 1) y = (bgg S J).d J (J + 1) x ∧
        y.1 = Vt.d J (J + 1) φ

/-- **The BGG verdict at `J`.** Its content, under the hypotheses of `FEEC.bggCohomology`, is
the two quasi-isomorphisms `quasiIso_ι` and `quasiIso_π`; `homology` follows from them,
`shortExact` holds for every `S` and `J`, and `acyclic` follows from `shortExact` and
`homology`. They are stated for the reader. -/
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

/-- **`Sᵏ` induces the zero map on cohomology**, `Sᵏ N(d̃ᵏ) ⊆ R(dᵏ)` ([ArnoldHu2021], (27)). -/
def InducesZero (k : ℤ) : Prop :=
  ∀ φ : Vt.X k, Vt.d k (k + 1) φ = 0 → conn S k (k + 1) φ ∈ LinearMap.range (V.d k (k + 1)).hom

/-- **The cochain map `(ω, μ) ↦ (ω + Kμ, μ)`** from the sum complex `V ⊕ Ṽ` (the twisted complex
of `S = 0`) to the twisted complex, for `Sⁱ = dKⁱ - Kⁱ⁺¹d̃` ([ArnoldHu2021], (28) and §5). -/
def sumToTwisted (K : ∀ i, Vt.X i →ₗ[R] V.X i)
    (hK : ∀ i μ, conn S i (i + 1) μ = V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ)) :
    twisted (0 : Vt ⟶ V⟦(1 : ℤ)⟧) ⟶ twisted S where
  f i := ModuleCat.ofHom (((LinearMap.fst R _ _ + K i ∘ₗ LinearMap.snd R _ _)).prod
    (LinearMap.snd R _ _))
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext ?_ rfl)
    change V.d i (i + 1) (x.1 + K i x.2) - conn S i (i + 1) x.2 =
      V.d i (i + 1) x.1 - conn 0 i (i + 1) x.2 + K (i + 1) (Vt.d i (i + 1) x.2)
    rw [hK, conn_succ, map_add]
    simp only [HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply, sub_zero]
    rw [sub_sub_eq_add_sub, add_right_comm, add_sub_cancel_right]

/-- **`H` represents the cohomology of `C` in degree `i`**: `N(dⁱ) = R(dⁱ⁻¹) ⊕ H`. -/
def Represents (C : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) (H : Submodule R (C.X i)) :
    Prop :=
  LinearMap.range (C.d (i - 1) i).hom ⊔ H = LinearMap.ker (C.d i (i + 1)).hom ∧
    Disjoint (LinearMap.range (C.d (i - 1) i).hom) H

/-- **The cochain map (30)** ([ArnoldHu2021], Theorem 7) from the sum complex to the BGG complex
at `J`, for maps `Kⁱ : Ṽⁱ → Vⁱ` and right inverses `tⁱ⁺¹ : Vⁱ⁺¹ → Ṽⁱ` of `Sⁱ` (`i ≥ J`; e.g. the
Moore–Penrose inverses of (29)), with `P = 1 - tⁱ⁺¹Sⁱ` (onto `N(Sⁱ)` along `R(tⁱ⁺¹)`): a
representative in `Γⁱ` of the image of `(ω, μ)`. Before `J` it is `(ω + Kμ, μ)` and at `J`
`(ω + Kμ, tᴶ⁺¹d(ω + Kμ))`, of class `[ω + Kμ]` in `Vⁱ / R(Sⁱ⁻¹)` (Arnold–Hu: `P_{R^⊥}(ω + Kμ)`);
after `J` it is `(0, P(d̃ tω + (I + d̃ tK)μ))`. -/
def sumMap (K : ∀ i, Vt.X i →ₗ[R] V.X i) (t : ∀ i j, V.X j →ₗ[R] Vt.X i) (J i : ℤ)
    (x : V.X i × Vt.X i) : V.X i × Vt.X i :=
  if i < J then (x.1 + K i x.2, x.2)
  else if i = J then (x.1 + K i x.2, t i (i + 1) (V.d i (i + 1) (x.1 + K i x.2)))
  else
    let φ := Vt.d (i - 1) i (t (i - 1) i x.1) + (x.2 + Vt.d (i - 1) i (t (i - 1) i (K i x.2)))
    (0, φ - t i (i + 1) (conn S i (i + 1) φ))

/-- **Non-vacuity**: `Ṽ = V⟦1⟧` with `S = 𝟙` (`Sⁱ = id`) satisfies the hypotheses of
`FEEC.bggCohomology` at every `J`. -/
theorem hypotheses_id (V : CochainComplex (ModuleCat.{v} R) ℤ) (J : ℤ) :
    (∀ i < J, Function.Injective (HomologicalComplex.Hom.f (𝟙 (V⟦(1 : ℤ)⟧)) i)) ∧ ∀ i, J ≤ i →
      LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (conn (𝟙 (V⟦(1 : ℤ)⟧)) i (i + 1)) =
        ⊤ :=
  ⟨fun _ _ _ _ h => h, fun i _ => by
    rw [conn_succ]
    exact eq_top_iff.2 fun x _ => Submodule.mem_sup_right ⟨x, rfl⟩⟩

end BGG

/-! ### Bounded Hilbert complexes -/

namespace BGG

variable {𝕜 : Type u} [RCLike 𝕜] {H : ℤ → Type v} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace 𝕜 (H i)]

/-- The cochain complex of modules of bounded maps `dⁱ : Hⁱ → Hⁱ⁺¹` with `d d = 0`. -/
abbrev ofBounded (d : ∀ i, H i →L[𝕜] H (i + 1)) (hd : ∀ i x, d (i + 1) (d i x) = 0) :
    CochainComplex (ModuleCat.{v} 𝕜) ℤ :=
  CochainComplex.of (fun i => ModuleCat.of 𝕜 (H i)) (fun i => ModuleCat.ofHom (d i))
    fun i => ModuleCat.hom_ext (LinearMap.ext (hd i))

/-- **Non-vacuity** of `FEEC.bggHilbert`: `H̃ⁱ = Hⁱ⁺¹`, `d̃ⁱ = -dⁱ⁺¹` and `sⁱ = id` form a
complex and connecting maps with `d s = -s d̃`, bounded below and onto at every `J`. -/
theorem hypotheses_bounded_id (d : ∀ i, H i →L[𝕜] H (i + 1)) (hd : ∀ i x, d (i + 1) (d i x) = 0)
    (J : ℤ) :
    (∀ i x, (-d (i + 1 + 1)) ((-d (i + 1)) x) = 0) ∧
    (∀ i x, d (i + 1) (ContinuousLinearMap.id 𝕜 (H (i + 1)) x) =
      -ContinuousLinearMap.id 𝕜 (H (i + 1 + 1)) ((-d (i + 1)) x)) ∧
    (∀ i < J, ∃ C, AntilipschitzWith C (ContinuousLinearMap.id 𝕜 (H (i + 1)))) ∧
    ∀ i, J ≤ i → LinearMap.range (d i : H i →ₗ[𝕜] H (i + 1)) ⊔
      LinearMap.range (ContinuousLinearMap.id 𝕜 (H (i + 1)) : H (i + 1) →ₗ[𝕜] H (i + 1)) = ⊤ :=
  ⟨fun _ _ => by simp [hd], fun _ _ => by simp, fun _ _ => ⟨1, AntilipschitzWith.id⟩,
    fun _ _ => by simp⟩

variable {Ht : ℤ → Type v} [∀ i, NormedAddCommGroup (Ht i)] [∀ i, InnerProductSpace 𝕜 (Ht i)]
  {d : ∀ i, H i →L[𝕜] H (i + 1)} {hd : ∀ i x, d (i + 1) (d i x) = 0}
  {dt : ∀ i, Ht i →L[𝕜] Ht (i + 1)} {hdt : ∀ i x, dt (i + 1) (dt i x) = 0}

/-- Bounded connecting maps `sⁱ : H̃ⁱ → Hⁱ⁺¹` with `d s = -s d̃`, as a morphism
`ofBounded dt hdt ⟶ (ofBounded d hd)⟦1⟧`. -/
def ofBoundedHom (s : ∀ i, Ht i →L[𝕜] H (i + 1))
    (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x)) :
    ofBounded dt hdt ⟶ (ofBounded d hd)⟦(1 : ℤ)⟧ where
  f i := ModuleCat.ofHom (s i)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    ext x
    simp [CochainComplex.shiftFunctor_obj_d', hs]

/-- **The Moore–Penrose inverse** `s†` of a bounded operator `s : E → F` between Hilbert spaces
with closed range ([ArnoldHu2021], (29)): the inverse of the bijection `s : N(s)ᗮ → R(s)` on
`R(s)`, zero on `R(s)ᗮ` (`0` if the range is not closed). -/
def moorePenrose {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (s : E →L[𝕜] F) :
    F →L[𝕜] E :=
  open scoped Classical in
  if h : IsClosed (s.range : Set F) then
    haveI := h.completeSpace_coe
    let r : s.kerᗮ →L[𝕜] s.range :=
      (s ∘L s.kerᗮ.subtypeL).codRestrict s.range fun x => ⟨x, rfl⟩
    s.kerᗮ.subtypeL ∘L ((ContinuousLinearEquiv.ofBijective r
        (LinearMap.ker_eq_bot'.2 fun x hx => Subtype.ext <| (Submodule.mem_bot 𝕜).1 <|
          s.ker.inf_orthogonal_eq_bot ▸ (⟨congrArg Subtype.val hx, x.2⟩ : (x : E) ∈ s.ker ⊓ s.kerᗮ))
        (LinearMap.range_eq_top.2 fun ⟨_, x, hx⟩ =>
          ⟨⟨_, s.kerᗮ.starProjection_apply_mem x⟩, Subtype.ext (Eq.trans (by
            have h0 : s (s.ker.starProjection x) = 0 := s.ker.starProjection_apply_mem x
            change s _ = s x
            conv_rhs => rw [← s.ker.starProjection_add_starProjection_orthogonal x, map_add, h0,
              zero_add]
            rfl) hx)⟩)).symm : s.range →L[𝕜] s.kerᗮ) ∘L
      s.range.orthogonalProjectionOnto
  else 0

/-- **The output spaces** of [ArnoldHu2021], (25), inside `Hⁱ × H̃ⁱ`: `R(Sⁱ⁻¹)ᗮ × 0` up to `J`,
`0 × N(sⁱ)` after `J`. -/
def Υ (s : ∀ i, Ht i →L[𝕜] H (i + 1)) (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x))
    (J i : ℤ) : Submodule 𝕜 (H i × Ht i) :=
  if i ≤ J then
    Submodule.prod (rangeS (ofBoundedHom (hd := hd) (hdt := hdt) s hs) i : Submodule 𝕜 (H i))ᗮ ⊥
  else Submodule.prod ⊥ (s i).ker

/-- `Γⁱ` in the `ℓ²` product `WithLp 2 (Hⁱ × H̃ⁱ)`, of norm `(‖σ‖² + ‖φ‖²)^½`. -/
def ΓL (s : ∀ i, Ht i →L[𝕜] H (i + 1)) (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x))
    (J i : ℤ) : Submodule 𝕜 (WithLp 2 (H i × Ht i)) :=
  (Γ (ofBoundedHom (hd := hd) (hdt := hdt) s hs) J i).comap
    (WithLp.linearEquiv 2 𝕜 (H i × Ht i)).toLinearMap

/-- `Δⁱ` in the `ℓ²` product `WithLp 2 (Hⁱ × H̃ⁱ)`. -/
def ΔL (s : ∀ i, Ht i →L[𝕜] H (i + 1)) (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x))
    (J i : ℤ) : Submodule 𝕜 (WithLp 2 (H i × Ht i)) :=
  (Δ (ofBoundedHom (hd := hd) (hdt := hdt) s hs) J i).comap
    (WithLp.linearEquiv 2 𝕜 (H i × Ht i)).toLinearMap

/-- **The space `Γⁱ / Δⁱ` of the BGG complex with the quotient norm** of the `ℓ²` norm,
`‖[x]‖ = inf_{δ ∈ Δⁱ} ‖x - δ‖`. For `i ≠ J` it is the norm of the output space `Υⁱ` of
[ArnoldHu2021], (25) (`‖[(σ, φ)]‖ = ‖P_{R(Sⁱ⁻¹)ᗮ} σ‖` before `J`, `‖φ‖` on `0 × N(Sⁱ)` after `J`);
at `J` it is `inf_ψ (‖σ + Sψ‖² + ‖φ - d̃ψ‖²)^½`, under (23) equivalent to, not equal to,
`‖P_{R(Sᴶ⁻¹)ᗮ} σ‖`. -/
abbrev QuotL (s : ∀ i, Ht i →L[𝕜] H (i + 1))
    (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x)) (J i : ℤ) : Type v :=
  ΓL (hd := hd) (hdt := hdt) s hs J i ⧸
    (ΔL (hd := hd) (hdt := hdt) s hs J i).comap (ΓL (hd := hd) (hdt := hdt) s hs J i).subtype

end BGG

/-! ### The complex with weak symmetry and its discretization ([QuennevilleBelair2015], Ch. 5) -/

/-- **BGG data with weak symmetry**: two segments `W⁰ → W¹ → W²` and `W̃⁰ → W̃¹ → W̃²` of
operators `d`, `d̃` between real Hilbert spaces (unbounded, `LinearPMap`s; their domains
`V = D(d)` carry the inner product of `W`; in the application densely defined and closed, which
is not required), with bounded connecting maps `S⁰ : W̃⁰ → W¹`, `S¹ : W̃¹ → W²`. The complex and
anticommutation laws are `WeakSymmetryData.IsBGG`. -/
structure WeakSymmetryData (W0 W1 W2 Wt0 Wt1 Wt2 : Type*) [NormedAddCommGroup W0]
    [InnerProductSpace ℝ W0] [NormedAddCommGroup W1] [InnerProductSpace ℝ W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0]
    [InnerProductSpace ℝ Wt0] [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1]
    [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2] where
  /-- the top row -/
  d0 : W0 →ₗ.[ℝ] W1
  d1 : W1 →ₗ.[ℝ] W2
  /-- the bottom row -/
  dt0 : Wt0 →ₗ.[ℝ] Wt1
  dt1 : Wt1 →ₗ.[ℝ] Wt2
  /-- the connecting maps -/
  S0 : Wt0 →L[ℝ] W1
  S1 : Wt1 →L[ℝ] W2

namespace WeakSymmetryData

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2)

/-- The rows are complexes, `R(d⁰) ⊆ D(d¹)`, `d¹d⁰ = 0` and `R(d̃⁰) ⊆ D(d̃¹)`, `d̃¹d̃⁰ = 0`, and
`S` anticommutes with them: `S⁰D(d̃⁰) ⊆ D(d¹)` and `d¹S⁰ = -S¹d̃⁰` (a morphism `Ṽ → V[1]`). -/
def IsBGG : Prop :=
  (∀ x : D.d0.domain, ∃ h : D.d0 x ∈ D.d1.domain, D.d1 ⟨_, h⟩ = 0) ∧
    (∀ x : D.dt0.domain, ∃ h : D.dt0 x ∈ D.dt1.domain, D.dt1 ⟨_, h⟩ = 0) ∧
    ∀ ψ : D.dt0.domain, ∃ h : D.S0 ψ ∈ D.d1.domain, D.d1 ⟨_, h⟩ = -D.S1 (D.dt0 ψ)

/-- **The continuous hypotheses with constant `C`** ([QuennevilleBelair2015], §5.1, Prop 5.3):
Poincaré inequalities on `V⁰` and `Ṽ⁰` (so `d⁰`, `d̃⁰` are injective, with closed range when
closed), exactness of the top row at `V¹`, the Hodge decomposition `v = d̃ψ + w`,
`‖w‖ ≤ C ‖d̃v‖`, on `Ṽ¹` (exactness of the bottom row at `Ṽ¹` and the Poincaré inequality), the
**regular decomposition** `d¹V¹ = d¹S⁰Ṽ⁰` with the bound `‖d̃φ‖ ≤ C ‖d¹x‖` ([Hiptmair2002],
Lemma 2.4, in the application), and `‖S⁰‖, ‖S¹‖ ≤ C`. -/
structure IsStable (C : ℝ) : Prop where
  poincare : ∀ σ : D.d0.domain, ‖(σ : W0)‖ ≤ C * ‖D.d0 σ‖
  poincare_t : ∀ φ : D.dt0.domain, ‖(φ : Wt0)‖ ≤ C * ‖D.dt0 φ‖
  exact : ∀ μ : D.d1.domain, D.d1 μ = 0 → ∃ ρ : D.d0.domain, D.d0 ρ = μ
  hodge_t : ∀ v : D.dt1.domain, ∃ (ψ : D.dt0.domain) (w : D.dt1.domain),
    (v : Wt1) = D.dt0 ψ + w ∧ ‖(w : Wt1)‖ ≤ C * ‖D.dt1 v‖
  regular : ∀ x : D.d1.domain, ∃ (φ : D.dt0.domain) (h : D.S0 φ ∈ D.d1.domain),
    D.d1 ⟨_, h⟩ = D.d1 x ∧ ‖D.dt0 φ‖ ≤ C * ‖D.d1 x‖
  norm_S0 : ‖D.S0‖ ≤ C
  norm_S1 : ‖D.S1‖ ≤ C

/-- `(σ, φ, u)` with the multiplier `λ ∈ W¹` solves **the mixed problem (5.3)** with datum `F`
([QuennevilleBelair2015], (5.3), with an `L²` multiplier): `⟪σ, τ⟫ - ⟪u, d̃ψ⟫ - ⟪λ, dτ - S⁰ψ⟫ = 0`,
`⟪d̃φ, v⟫ + ⟪S¹u, S¹v⟫ + ⟪d̃u, d̃v⟫ = F v` for all `τ ∈ V⁰`, `ψ ∈ Ṽ⁰`, `v ∈ Ṽ¹`, and `dσ = S⁰φ`. -/
def IsSolution (F : D.dt1.domain →ₗ[ℝ] ℝ) (σ : D.d0.domain) (φ : D.dt0.domain)
    (u : D.dt1.domain) (lam : W1) : Prop :=
  (∀ (τ : D.d0.domain) (ψ : D.dt0.domain),
      ⟪(σ : W0), τ⟫_ℝ - ⟪(u : Wt1), D.dt0 ψ⟫_ℝ - ⟪lam, D.d0 τ - D.S0 ψ⟫_ℝ = 0) ∧
    (∀ v : D.dt1.domain,
      ⟪D.dt0 φ, v⟫_ℝ + ⟪D.S1 u, D.S1 v⟫_ℝ + ⟪D.dt1 u, D.dt1 v⟫_ℝ = F v) ∧
    D.d0 σ = D.S0 φ

/-- **A discretization** of `D` ([QuennevilleBelair2015], §5.2): finite-dimensional subspaces of
the domains forming subcomplexes of both rows, with bounded cochain projections `π : W → W` onto
them (identity on the subspaces, `d π = π d` on the domains). The method (5.6) couples the rows by
`S⁰ₕ = π¹S⁰`, `S¹ₕ = π²S¹`. -/
structure Discretization where
  /-- the finite element spaces -/
  V0 : Submodule ℝ W0
  V1 : Submodule ℝ W1
  V2 : Submodule ℝ W2
  Vt0 : Submodule ℝ Wt0
  Vt1 : Submodule ℝ Wt1
  Vt2 : Submodule ℝ Wt2
  [fd0 : FiniteDimensional ℝ V0]
  [fd1 : FiniteDimensional ℝ V1]
  [fd2 : FiniteDimensional ℝ V2]
  [fdt0 : FiniteDimensional ℝ Vt0]
  [fdt1 : FiniteDimensional ℝ Vt1]
  [fdt2 : FiniteDimensional ℝ Vt2]
  le0 : V0 ≤ D.d0.domain
  le1 : V1 ≤ D.d1.domain
  let0 : Vt0 ≤ D.dt0.domain
  let1 : Vt1 ≤ D.dt1.domain
  d0_mem : ∀ x : D.d0.domain, (x : W0) ∈ V0 → D.d0 x ∈ V1
  d1_mem : ∀ x : D.d1.domain, (x : W1) ∈ V1 → D.d1 x ∈ V2
  dt0_mem : ∀ x : D.dt0.domain, (x : Wt0) ∈ Vt0 → D.dt0 x ∈ Vt1
  dt1_mem : ∀ x : D.dt1.domain, (x : Wt1) ∈ Vt1 → D.dt1 x ∈ Vt2
  /-- the cochain projections -/
  π0 : W0 →L[ℝ] W0
  π1 : W1 →L[ℝ] W1
  π2 : W2 →L[ℝ] W2
  πt0 : Wt0 →L[ℝ] Wt0
  πt1 : Wt1 →L[ℝ] Wt1
  πt2 : Wt2 →L[ℝ] Wt2
  π0_mem : ∀ x, π0 x ∈ V0
  π1_mem : ∀ x, π1 x ∈ V1
  π2_mem : ∀ x, π2 x ∈ V2
  πt0_mem : ∀ x, πt0 x ∈ Vt0
  πt1_mem : ∀ x, πt1 x ∈ Vt1
  πt2_mem : ∀ x, πt2 x ∈ Vt2
  π0_id : ∀ x ∈ V0, π0 x = x
  π1_id : ∀ x ∈ V1, π1 x = x
  π2_id : ∀ x ∈ V2, π2 x = x
  πt0_id : ∀ x ∈ Vt0, πt0 x = x
  πt1_id : ∀ x ∈ Vt1, πt1 x = x
  πt2_id : ∀ x ∈ Vt2, πt2 x = x
  comm0 : ∀ x : D.d0.domain, D.d0 ⟨π0 x, le0 (π0_mem x)⟩ = π1 (D.d0 x)
  comm1 : ∀ x : D.d1.domain, D.d1 ⟨π1 x, le1 (π1_mem x)⟩ = π2 (D.d1 x)
  commt0 : ∀ x : D.dt0.domain, D.dt0 ⟨πt0 x, let0 (πt0_mem x)⟩ = πt1 (D.dt0 x)
  commt1 : ∀ x : D.dt1.domain, D.dt1 ⟨πt1 x, let1 (πt1_mem x)⟩ = πt2 (D.dt1 x)

namespace Discretization

variable {D} (Q : D.Discretization)

/-- The projections are **bounded by `C`**: `‖π‖ ≤ C`, `‖π̃‖ ≤ C` in every degree. -/
def IsBounded (C : ℝ) : Prop :=
  ‖Q.π0‖ ≤ C ∧ ‖Q.π1‖ ≤ C ∧ ‖Q.π2‖ ≤ C ∧ ‖Q.πt0‖ ≤ C ∧ ‖Q.πt1‖ ≤ C ∧ ‖Q.πt2‖ ≤ C

/-- **The compatibility condition (5.4)** `π¹S⁰π̃⁰ = π¹S⁰` ([QuennevilleBelair2015], (5.4)). -/
def Compatible : Prop := ∀ ψ, Q.π1 (D.S0 (Q.πt0 ψ)) = Q.π1 (D.S0 ψ)

/-- **Consistency of `Sₕ` at the order `h`** with constant `C` (cf. [QuennevilleBelair2015],
Prop 5.9): `‖(S⁰ - S⁰ₕ)ψ‖ ≤ C h ‖d̃ψ‖` on `Ṽₕ⁰`, and every `d̃v`, `v ∈ Ṽₕ¹`, has a **regular
potential** `w`, `d̃w = d̃v`, `‖w‖ ≤ C ‖d̃v‖`, on which `π̃¹` and `S¹ₕ` are accurate,
`‖(1 - π̃¹)w‖, ‖(S¹ - S¹ₕ)w‖ ≤ C h ‖d̃v‖`. -/
def IsConsistent (C h : ℝ) : Prop :=
  (∀ ψ : D.dt0.domain, (ψ : Wt0) ∈ Q.Vt0 → ‖D.S0 ψ - Q.π1 (D.S0 ψ)‖ ≤ C * h * ‖D.dt0 ψ‖) ∧
    ∀ v : D.dt1.domain, (v : Wt1) ∈ Q.Vt1 → ∃ w : D.dt1.domain, D.dt1 w = D.dt1 v ∧
      ‖(w : Wt1)‖ ≤ C * ‖D.dt1 v‖ ∧ ‖(w : Wt1) - Q.πt1 w‖ ≤ C * h * ‖D.dt1 v‖ ∧
      ‖D.S1 w - Q.π2 (D.S1 w)‖ ≤ C * h * ‖D.dt1 v‖

/-- `(σₕ, φₕ, uₕ, λₕ) ∈ Vₕ⁰ × Ṽₕ⁰ × Ṽₕ¹ × Vₕ¹` solves **the discrete problem (5.6)** with datum
`F`: (5.3) on the discrete spaces with `S⁰ₕ = π¹S⁰`, `S¹ₕ = π²S¹` in place of `S⁰`, `S¹`. -/
def IsDiscreteSolution (F : D.dt1.domain →ₗ[ℝ] ℝ) (σ : D.d0.domain) (φ : D.dt0.domain)
    (u : D.dt1.domain) (lam : W1) : Prop :=
  (σ : W0) ∈ Q.V0 ∧ (φ : Wt0) ∈ Q.Vt0 ∧ (u : Wt1) ∈ Q.Vt1 ∧ lam ∈ Q.V1 ∧
    (∀ (τ : D.d0.domain) (ψ : D.dt0.domain), (τ : W0) ∈ Q.V0 → (ψ : Wt0) ∈ Q.Vt0 →
      ⟪(σ : W0), τ⟫_ℝ - ⟪(u : Wt1), D.dt0 ψ⟫_ℝ - ⟪lam, D.d0 τ - Q.π1 (D.S0 ψ)⟫_ℝ = 0) ∧
    (∀ v : D.dt1.domain, (v : Wt1) ∈ Q.Vt1 → ⟪D.dt0 φ, v⟫_ℝ +
      ⟪Q.π2 (D.S1 u), Q.π2 (D.S1 v)⟫_ℝ + ⟪D.dt1 u, D.dt1 v⟫_ℝ = F v) ∧
    D.d0 σ = Q.π1 (D.S0 φ)

/-- The squared **error** in the graph norms of `V⁰`, `Ṽ⁰` and in `‖w‖² + ‖S¹ₕw‖² + ‖d̃w‖²` on
`Ṽ¹`. -/
def errorSq (σ σh : D.d0.domain) (φ φh : D.dt0.domain) (u uh : D.dt1.domain) : ℝ :=
  ‖((σ - σh : D.d0.domain) : W0)‖ ^ 2 + ‖D.d0 (σ - σh)‖ ^ 2 +
    ‖((φ - φh : D.dt0.domain) : Wt0)‖ ^ 2 + ‖D.dt0 (φ - φh)‖ ^ 2 +
    ‖((u - uh : D.dt1.domain) : Wt1)‖ ^ 2 + ‖Q.π2 (D.S1 (u - uh))‖ ^ 2 + ‖D.dt1 (u - uh)‖ ^ 2

/-- The squared **projection error** of `(σ, φ, u)` in the norms of `errorSq` (with `d π = π d`). -/
def projErrorSq (σ : D.d0.domain) (φ : D.dt0.domain) (u : D.dt1.domain) : ℝ :=
  ‖Q.π0 σ - σ‖ ^ 2 + ‖Q.π1 (D.d0 σ) - D.d0 σ‖ ^ 2 + ‖Q.πt0 φ - φ‖ ^ 2 +
    ‖Q.πt1 (D.dt0 φ) - D.dt0 φ‖ ^ 2 + ‖Q.πt1 u - u‖ ^ 2 + ‖Q.π2 (D.S1 (Q.πt1 u - u))‖ ^ 2 +
    ‖Q.πt2 (D.dt1 u) - D.dt1 u‖ ^ 2

end Discretization

end WeakSymmetryData

/-! ### The theorems -/

/-- **The BGG construction** ([ArnoldHu2021], §5.2). For a stacked diagram `S : Ṽ ⟶ V⟦1⟧` of
cochain complexes of modules over any ring, with `Sⁱ` injective for `i < J` and onto modulo `d`
for `i ≥ J` (`R(dⁱ) + R(Sⁱ) = Vⁱ⁺¹`; in particular when `Sⁱ` is surjective, [ArnoldHu2021], (23)),
the BGG complex at `J` has the cohomology of the twisted complex (`BGG.Verdict`). -/
theorem bggCohomology {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i →
      LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (BGG.conn S i (i + 1)) = ⊤) :
    BGG.Verdict S J := by
  sorry

/-- **The BGG complex is the output complex of [ArnoldHu2021], (24)–(26)**, for every stacked
diagram and every `J` (`BGG.Identification`). -/
theorem bggIdentification {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) : BGG.Identification S J := by
  sorry

/-- **The cohomology of the BGG complex** ([ArnoldHu2021], Theorem 6). Over a field, under the
hypotheses of `FEEC.bggCohomology`, if both rows have finite-dimensional cohomology in degree `i`,
so does the BGG complex, `dim Hⁱ(Γ / Δ) ≤ dim Hⁱ(V) + dim Hⁱ(Ṽ)`, with equality if and only if
`Sⁱ⁻¹` and `Sⁱ` induce the zero maps on cohomology ([ArnoldHu2021], (27)). -/
theorem bggFinrank {K : Type u} [Field K] {V Vt : CochainComplex (ModuleCat.{v} K) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i →
      LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (BGG.conn S i (i + 1)) = ⊤) (i : ℤ)
    [FiniteDimensional K (V.homology i)] [FiniteDimensional K (Vt.homology i)] :
    FiniteDimensional K ((BGG.bgg S J).homology i) ∧
      Module.finrank K ((BGG.bgg S J).homology i) ≤
        Module.finrank K (V.homology i) + Module.finrank K (Vt.homology i) ∧
      (Module.finrank K ((BGG.bgg S J).homology i) =
          Module.finrank K (V.homology i) + Module.finrank K (Vt.homology i) ↔
        BGG.InducesZero S (i - 1) ∧ BGG.InducesZero S i) := by
  sorry

/-- **Cohomology through the sum complex** ([ArnoldHu2021], Theorem 7 and Proposition 1). If
`Sⁱ = dKⁱ - Kⁱ⁺¹d̃` for maps `Kⁱ : Ṽⁱ → Vⁱ` ((28)), then `S` induces the zero maps on cohomology
((27), Proposition 1) and the cochain map `(ω, μ) ↦ (ω + Kμ, μ)` from the sum complex (the
twisted complex of `S = 0`: `Vⁱ × Ṽⁱ` with differential `d × d̃`) to the twisted complex is an
isomorphism; under the hypotheses of `FEEC.bggCohomology` at any `J`, the BGG complex has the
cohomology of the sum complex (Theorem 7). -/
theorem bggSum {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (K : ∀ i, Vt.X i →ₗ[R] V.X i)
    (hK : ∀ i μ, BGG.conn S i (i + 1) μ = V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ)) :
    (∀ i, BGG.InducesZero S i) ∧ IsIso (BGG.sumToTwisted S K hK) ∧
      ∀ J, (∀ i < J, Function.Injective (S.f i)) →
        (∀ i, J ≤ i →
          LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (BGG.conn S i (i + 1)) = ⊤) →
        ∀ i, Nonempty ((BGG.bgg S J).homology i ≅
          (BGG.twisted (0 : Vt ⟶ V⟦(1 : ℤ)⟧)).homology i) := by
  sorry

/-- **The explicit cochain map of Theorem 7 and the cohomology representatives of Corollary 1**
([ArnoldHu2021], (30), (31)). If `Sⁱ = dKⁱ - Kⁱ⁺¹d̃` ((28)), `Sⁱ` is injective for `i ≤ J` and
`tⁱ⁺¹` is a right inverse of `Sⁱ` for `i ≥ J` ((23), (29)), then `BGG.sumMap` defines a cochain
map `κ` from the sum complex to the BGG complex at `J` (with values in `Γ`), `κ` induces an
isomorphism on cohomology (Theorem 7), and if `H`, `H̃` represent the cohomology of the rows in
degree `i`, then `κ(H × H̃)` represents the cohomology of the BGG complex (Corollary 1). -/
theorem bggExplicit {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (K : ∀ i, Vt.X i →ₗ[R] V.X i)
    (hK : ∀ i μ, BGG.conn S i (i + 1) μ = V.d i (i + 1) (K i μ) - K (i + 1) (Vt.d i (i + 1) μ))
    (J : ℤ) (t : ∀ i j, V.X j →ₗ[R] Vt.X i) (hinj : ∀ i ≤ J, Function.Injective (S.f i))
    (ht : ∀ i, J ≤ i → ∀ v, BGG.conn S i (i + 1) (t i (i + 1) v) = v) :
    ∃ κ : BGG.twisted (0 : Vt ⟶ V⟦(1 : ℤ)⟧) ⟶ BGG.bgg S J,
      (∀ i x, ∃ hx : BGG.sumMap S K t J i x ∈ BGG.Γ S J i,
        (κ.f i).hom x = Submodule.Quotient.mk ⟨_, hx⟩) ∧ QuasiIso κ ∧
      ∀ i (H : Submodule R (V.X i)) (Ht : Submodule R (Vt.X i)), BGG.Represents V i H →
        BGG.Represents Vt i Ht → BGG.Represents (BGG.bgg S J) i ((H.prod Ht).map (κ.f i).hom) := by
  sorry

/-- **The BGG complex of bounded Hilbert complexes is a bounded Hilbert complex, with the
quotient norm, and has closed ranges** ([ArnoldHu2021], Theorem 6 and the remark after it). Let
`d`, `d̃` be complexes of bounded operators on Hilbert spaces and `s` bounded connecting maps with
`d s = -s d̃`, bounded below for `i < J` and onto modulo `d` for `i ≥ J`. Then `Γⁱ` and `Δⁱ` are
closed in `Hⁱ × H̃ⁱ`; for the quotient norm of the `ℓ²` norm, `y ↦ [y]` is an isometry of the
closed subspace `Γⁱ ⊖ Δⁱ = Γⁱ ∩ (Δⁱ)ᗮ` of the Hilbert space `Hⁱ ⊕ H̃ⁱ` onto `Γⁱ / Δⁱ` (so the
quotient norm is a Hilbert norm); the differentials `[(σ, φ)] ↦ [(dσ - sφ, d̃φ)]` of the BGG
complex are bounded for it; and where both rows have finite-dimensional cohomology in degree
`i + 1`, the differential into `Γⁱ⁺¹ / Δⁱ⁺¹` has closed range. -/
theorem bggHilbert {𝕜 : Type u} [RCLike 𝕜] {H Ht : ℤ → Type v}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace 𝕜 (H i)] [∀ i, CompleteSpace (H i)]
    [∀ i, NormedAddCommGroup (Ht i)] [∀ i, InnerProductSpace 𝕜 (Ht i)]
    [∀ i, CompleteSpace (Ht i)]
    (d : ∀ i, H i →L[𝕜] H (i + 1)) (hd : ∀ i x, d (i + 1) (d i x) = 0)
    (dt : ∀ i, Ht i →L[𝕜] Ht (i + 1)) (hdt : ∀ i x, dt (i + 1) (dt i x) = 0)
    (s : ∀ i, Ht i →L[𝕜] H (i + 1)) (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x))
    (J : ℤ) (hinj : ∀ i < J, ∃ C, AntilipschitzWith C (s i))
    (hsurj : ∀ i, J ≤ i → LinearMap.range (d i : H i →ₗ[𝕜] H (i + 1)) ⊔
      LinearMap.range (s i : Ht i →ₗ[𝕜] H (i + 1)) = ⊤) :
    let S := BGG.ofBoundedHom (hd := hd) (hdt := hdt) s hs
    let ΓL := BGG.ΓL (hd := hd) (hdt := hdt) s hs J
    let ΔL := BGG.ΔL (hd := hd) (hdt := hdt) s hs J
    let Q := BGG.QuotL (hd := hd) (hdt := hdt) s hs J
    (∀ i, IsClosed (BGG.Γ S J i : Set (H i × Ht i)) ∧ IsClosed (BGG.Δ S J i : Set (H i × Ht i))) ∧
      (∀ i, ∃ e : ↥(ΓL i ⊓ (ΔL i)ᗮ) ≃ₗᵢ[𝕜] Q i, ∀ y, e y = Submodule.Quotient.mk ⟨y, y.2.1⟩) ∧
      ∃ D : ∀ i, Q i →L[𝕜] Q (i + 1),
        (∀ i (x : ΓL i) (x' : ΓL (i + 1)), (x' : WithLp 2 (H (i + 1) × Ht (i + 1))).ofLp =
          BGG.twist S i (i + 1) (x : WithLp 2 (H i × Ht i)).ofLp →
            D i (Submodule.Quotient.mk x) = Submodule.Quotient.mk x') ∧
        ∀ i, [FiniteDimensional 𝕜 ((BGG.ofBounded d hd).homology (i + 1))] →
          [FiniteDimensional 𝕜 ((BGG.ofBounded dt hdt).homology (i + 1))] →
          IsClosed (Set.range (D i)) := by
  sorry

/-- **The orthogonal form of Theorem 7: the cochain map (30) with Moore–Penrose inverses**
([ArnoldHu2021], (24)–(26), (23), (28)–(30), Theorem 7). Let `d`, `d̃` be complexes of bounded
operators on Hilbert spaces and `s` bounded connecting maps with `d s = -s d̃`, null-homotopic,
`sⁱ = dKⁱ - Kⁱ⁺¹d̃` ((28)), with `sⁱ` injective for `i ≤ J`, surjective for `i ≥ J` ((23)) and
of closed range for `i < J`; let `tⁱ⁺¹ = (sⁱ)†` (`BGG.moorePenrose`). Then there is a complex `Y`
with isomorphisms `Yⁱ ≅ Υⁱ` onto the output spaces (`BGG.Υ`: `R(sⁱ⁻¹)ᗮ` up to `J`, `N(sⁱ)` after)
carrying its differential to the output differentials (26), `P_{R(sⁱ)ᗮ} d` before `J`,
`d̃ (sᴶ)† d` at `J`, `d̃` after `J`, and a quasi-isomorphism `κ` from the sum complex to `Y` which
is the map (30): `(ω, μ) ↦ P_{R(sⁱ⁻¹)ᗮ}(ω + Kμ)` up to `J`, and in degree `i + 1 > J`,
`(ω, μ) ↦ P_{N(sⁱ⁺¹)}(d̃ tⁱ⁺¹ω + (I + d̃ tⁱ⁺¹ K)μ)`; `Y` is isomorphic to the BGG complex (as
a complex of modules); and
(Corollary 1, (31)) if `A`, `Ã` represent the cohomology of the rows in degree `i`, then `κ(A × Ã)`
represents that of `Y`. -/
theorem bggOrthogonal {𝕜 : Type u} [RCLike 𝕜] {H Ht : ℤ → Type v}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace 𝕜 (H i)] [∀ i, CompleteSpace (H i)]
    [∀ i, NormedAddCommGroup (Ht i)] [∀ i, InnerProductSpace 𝕜 (Ht i)]
    [∀ i, CompleteSpace (Ht i)]
    (d : ∀ i, H i →L[𝕜] H (i + 1)) (hd : ∀ i x, d (i + 1) (d i x) = 0)
    (dt : ∀ i, Ht i →L[𝕜] Ht (i + 1)) (hdt : ∀ i x, dt (i + 1) (dt i x) = 0)
    (s : ∀ i, Ht i →L[𝕜] H (i + 1)) (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x))
    (K : ∀ i, Ht i →ₗ[𝕜] H i) (hK : ∀ i μ, s i μ = d i (K i μ) - K (i + 1) (dt i μ))
    (J : ℤ) (hinj : ∀ i ≤ J, Function.Injective (s i))
    (hsurj : ∀ i, J ≤ i → Function.Surjective (s i))
    (hR : ∀ i < J, IsClosed (Set.range (s i))) :
    let S := BGG.ofBoundedHom (hd := hd) (hdt := hdt) s hs
    let P := fun i => (BGG.rangeS S i : Submodule 𝕜 (H i))ᗮ.starProjection
    ∃ (Y : CochainComplex (ModuleCat.{v} 𝕜) ℤ)
      (e : ∀ i, Y.X i ≃ₗ[𝕜] BGG.Υ (hd := hd) (hdt := hdt) s hs J i)
      (κ : BGG.twisted (0 : BGG.ofBounded dt hdt ⟶ (BGG.ofBounded d hd)⟦(1 : ℤ)⟧) ⟶ Y),
      (∀ i < J, ∀ y, (e (i + 1) (Y.d i (i + 1) y) : H (i + 1) × Ht (i + 1)) =
        (P (i + 1) (d i (e i y : H i × Ht i).1), 0)) ∧
      (∀ y, (e (J + 1) (Y.d J (J + 1) y) : H (J + 1) × Ht (J + 1)) =
        (0, dt J (BGG.moorePenrose (s J) (d J (e J y : H J × Ht J).1)))) ∧
      (∀ i, J < i → ∀ y, (e (i + 1) (Y.d i (i + 1) y) : H (i + 1) × Ht (i + 1)) =
        (0, dt i (e i y : H i × Ht i).2)) ∧
      (∀ i ≤ J, ∀ x : H i × Ht i, (e i ((κ.f i).hom x) : H i × Ht i) = (P i (x.1 + K i x.2), 0)) ∧
      (∀ i, J ≤ i → ∀ x : H (i + 1) × Ht (i + 1),
        (e (i + 1) ((κ.f (i + 1)).hom x) : H (i + 1) × Ht (i + 1)) =
          (0, (s (i + 1)).ker.starProjection (dt i (BGG.moorePenrose (s i) x.1) +
            (x.2 + dt i (BGG.moorePenrose (s i) (K (i + 1) x.2)))))) ∧
      QuasiIso κ ∧ Nonempty (Y ≅ BGG.bgg S J) ∧
      ∀ i (A : Submodule 𝕜 (H i)) (At : Submodule 𝕜 (Ht i)),
        BGG.Represents (BGG.ofBounded d hd) i A → BGG.Represents (BGG.ofBounded dt hdt) i At →
          BGG.Represents Y i ((A.prod At).map (κ.f i).hom) :=
  sorry

/-- **Stability and convergence of the discretizations of the complex with weak symmetry**
([QuennevilleBelair2015], Prop 5.4 and Thm 5.5; [AFW2007]; [AFW2010], §3). For every
constant `C` there is `K` such that, for all BGG data `D` satisfying the continuous hypotheses
with constant `C` and every discretization `Q` with projections bounded by `C` satisfying (5.4):
the discrete problem (5.6) has exactly one solution for every datum `F` (Prop 5.4); and if `Sₕ`
is consistent at the order `h` with constant `C`, then for every solution `(σ, φ, u, λ)` of (5.3)
with `‖λ‖ ≤ Λ` and `|⟪S¹u, d¹w⟫| ≤ Λ ‖w‖` on `V¹` (for densely defined `d¹`: `S¹u ∈ D(d¹*)`,
`‖d¹*S¹u‖ ≤ Λ`), and the solution of (5.6) with the same
datum, the squared error is at most `K` times the squared projection error of `(σ, φ, u)` plus
`h² (Λ² + ‖S¹u‖²)` plus the consistency error `‖(S¹ - S¹ₕ)u‖²` (Thm 5.5). -/
theorem bggWeakSymmetry (C : ℝ) : ∃ K : ℝ, ∀ {W0 W1 W2 Wt0 Wt1 Wt2 : Type u}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [NormedAddCommGroup W1]
    [InnerProductSpace ℝ W1] [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
    [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0] [NormedAddCommGroup Wt1]
    [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
    (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2) (Q : D.Discretization), D.IsBGG →
    D.IsStable C → Q.IsBounded C → Q.Compatible →
    (∀ F, ∃! x : D.d0.domain × D.dt0.domain × D.dt1.domain × W1,
      Q.IsDiscreteSolution F x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
    ∀ (h Λ : ℝ), 0 ≤ h → Q.IsConsistent C h → ∀ F σ φ u lam σh φh uh lamh,
      D.IsSolution F σ φ u lam → ‖lam‖ ≤ Λ →
      (∀ w : D.d1.domain, |⟪D.S1 u, D.d1 w⟫_ℝ| ≤ Λ * ‖(w : W1)‖) →
      Q.IsDiscreteSolution F σh φh uh lamh →
      Q.errorSq σ σh φ φh u uh ≤ K * (Q.projErrorSq σ φ u + h ^ 2 * (Λ ^ 2 + ‖D.S1 u‖ ^ 2) +
        ‖D.S1 u - Q.π2 (D.S1 u)‖ ^ 2) := by
  sorry

/-- **Non-vacuity of `FEEC.bggWeakSymmetry`**: BGG data on `ℝ` in every degree and a
discretization of them satisfy all its hypotheses with `C = 1`, consistency at every order
`h ≥ 0` included, and (5.3) has a solution with `σ`, `φ`, `u` and `λ` all nonzero. -/
theorem bggWeakSymmetry_nonvacuous : ∃ (D : WeakSymmetryData ℝ ℝ ℝ ℝ ℝ ℝ) (Q : D.Discretization),
    D.IsBGG ∧ D.IsStable 1 ∧ Q.IsBounded 1 ∧ Q.Compatible ∧ (∀ h, 0 ≤ h → Q.IsConsistent 1 h) ∧
    ∃ F σ φ u lam, D.IsSolution F σ φ u lam ∧ (σ : ℝ) ≠ 0 ∧ (φ : ℝ) ≠ 0 ∧ (u : ℝ) ≠ 0 ∧
      lam ≠ 0 := by
  sorry

end FEEC
