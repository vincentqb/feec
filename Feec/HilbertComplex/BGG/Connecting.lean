module

public import Feec.HilbertComplex.BGG.Derived

/-!
# The connecting map of the twisted complex is induced by `S`

The twisted complex `T` of BGG data is an extension `0 → V → T → Ṽ → 0` of the bottom row by the
top row (`Feec.BGG.Data.twistShortComplex_shortExact`). Its connecting map in cohomology
`Hⁱ(Ṽ) → Hʲ(V)` is induced by `-S`: `δ[φ] = [-Sφ]` (`Data.δ_twistShortComplex`). It vanishes
iff `S` maps the cycles of `Ṽⁱ` into the boundaries of `Vʲ`, `Sⁱ N(d̃ⁱ) ⊆ R(dⁱ)`
(`Data.InducesZero`, `Data.δ_eq_zero_iff`), so by the long exact sequence, over a field,
**`dim Hⁱ(T) = dim Hⁱ(V) + dim Hⁱ(Ṽ)` iff `Sⁱ⁻¹` and `Sⁱ` induce the zero maps on cohomology**
(`Data.finrank_twistComplex_homology_eq_iff`), and the same for the derived complexes
(`Data.finrank_derived_homology_eq_iff`): the equality criterion (27) of [ArnoldHu2021],
Theorem 6.

## Main results

* `Data.δ_twistShortComplex`: `δ[φ] = [-Sφ]`.
* `Data.δ_eq_zero_iff`, `Data.injective_homologyMap_rowTopι_iff`,
  `Data.surjective_homologyMap_rowBotπ_iff`; `Data.inducesZero_of_isZero_rowBot`,
  `Data.inducesZero_of_isZero_rowTop`.
* `Data.finrank_twistComplex_homology_eq_iff`, `Data.finrank_derived_homology_eq_iff`,
  `Data.finrank_derived_homology_eq_add` (where a row has no cohomology at each connecting map).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], Theorem 6 ((27): equality
  in the dimension bound) and §5.1 (the twisted complex and the sum complex)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Feec.BGG.Data

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι} {V Vt : ι → Type v}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [∀ i, AddCommGroup (Vt i)]
  [∀ i, Module R (Vt i)] (D : Data R c V Vt)

/-- **`S` induces the zero map `Hⁱ(Ṽ) → Hʲ(V)`**: `S N(d̃) ⊆ R(d)`. [ArnoldHu2021], (27) -/
def InducesZero (i j : ι) : Prop :=
  ∀ φ : Vt i, D.dt i j φ = 0 → D.S i j φ ∈ LinearMap.range (D.d i j)

theorem d_neg_S_eq_zero {i j : ι} (k : ι) {φ : Vt i} (hφ : D.dt i j φ = 0) :
    D.d j k (-D.S i j φ) = 0 := by
  rw [map_neg, D.anticomm, hφ, map_zero, neg_neg]

/-- **The connecting map of `0 → V → T → Ṽ → 0` is induced by `-S`**: `δ[φ] = [-Sφ]`.
[ArnoldHu2021], §5.1 -/
theorem δ_twistShortComplex {i j : ι} (hij : c.Rel i j) (φ : Vt i) (hφ : D.dt i j φ = 0)
    (k : ι) (hk : c.next j = k) :
    D.twistShortComplex_shortExact.δ i j hij
        (D.rowBot.homologyπ i (D.rowBot.cyclesMk φ j (c.next_eq' hij) hφ)) =
      D.rowTop.homologyπ j (D.rowTop.cyclesMk (-D.S i j φ) k hk (D.d_neg_S_eq_zero k hφ)) :=
  D.twistShortComplex_shortExact.δ_apply i j hij φ hφ ((0 : V i), φ) rfl (-D.S i j φ)
    (by change ((-D.S i j φ, (0 : Vt j)) : V j × Vt j) = (D.d i j 0 - D.S i j φ, D.dt i j φ)
        rw [hφ]; simp) k hk

/-- **The connecting map vanishes iff `S` induces the zero map on cohomology.** -/
theorem δ_eq_zero_iff {i j : ι} (hij : c.Rel i j) :
    D.twistShortComplex_shortExact.δ i j hij = 0 ↔ D.InducesZero i j := by
  have hp : c.prev j = i := c.prev_eq' hij
  constructor
  · intro h φ hφ
    have := D.δ_twistShortComplex hij φ hφ _ rfl
    rw [h] at this
    obtain ⟨y, hy⟩ := (D.rowTop.homologyπ_eq_zero_iff_moduleCat hp _).1 this.symm
    have hy' : D.d i j y = -D.S i j φ := hy.trans (D.rowTop.i_cyclesMk _ _ rfl _)
    exact ⟨-y, ((D.d i j).map_neg y).trans (by rw [hy', neg_neg])⟩
  · intro h
    ext x
    obtain ⟨φ, hφ, rfl⟩ := D.rowBot.exists_homologyπ_cyclesMk_moduleCat (c.next_eq' hij) x
    change D.twistShortComplex_shortExact.δ i j hij _ = 0
    rw [D.δ_twistShortComplex hij φ hφ _ rfl]
    refine (D.rowTop.homologyπ_eq_zero_iff_moduleCat hp _).2 ?_
    obtain ⟨y, hy⟩ := h φ hφ
    exact ⟨(-y : V i), (map_neg _ _).trans ((congrArg Neg.neg hy).trans
      (D.rowTop.i_cyclesMk _ _ rfl _).symm)⟩

/-- `Hʲ(V) → Hʲ(T)` is injective iff `S` induces the zero map `Hⁱ(Ṽ) → Hʲ(V)`. -/
theorem injective_homologyMap_rowTopι_iff {i j : ι} (hij : c.Rel i j) :
    Function.Injective (HomologicalComplex.homologyMap D.rowTopι j) ↔ D.InducesZero i j := by
  have he : LinearMap.range (D.twistShortComplex_shortExact.δ i j hij).hom =
      LinearMap.ker (HomologicalComplex.homologyMap D.rowTopι j).hom :=
    (D.twistShortComplex_shortExact.homology_exact₁ i j hij).moduleCat_range_eq_ker
  rw [← D.δ_eq_zero_iff hij, ← ModuleCat.hom_injective.eq_iff, ModuleCat.hom_zero,
    ← LinearMap.range_eq_bot, he]
  exact LinearMap.ker_eq_bot.symm

/-- `Hⁱ(T) → Hⁱ(Ṽ)` is surjective iff `S` induces the zero map `Hⁱ(Ṽ) → Hʲ(V)`. -/
theorem surjective_homologyMap_rowBotπ_iff {i j : ι} (hij : c.Rel i j) :
    Function.Surjective (HomologicalComplex.homologyMap D.rowBotπ i) ↔ D.InducesZero i j := by
  have he : LinearMap.range (HomologicalComplex.homologyMap D.rowBotπ i).hom =
      LinearMap.ker (D.twistShortComplex_shortExact.δ i j hij).hom :=
    (D.twistShortComplex_shortExact.homology_exact₃ i j hij).moduleCat_range_eq_ker
  rw [← D.δ_eq_zero_iff hij, ← ModuleCat.hom_injective.eq_iff, ModuleCat.hom_zero,
    ← LinearMap.ker_eq_top, ← he]
  exact LinearMap.range_eq_top.symm

/-- `S` induces the zero map `Hⁱ(Ṽ) → Hʲ(V)` when `Hⁱ(Ṽ) = 0`. -/
theorem inducesZero_of_isZero_rowBot {i j : ι} (hij : c.Rel i j)
    (h : IsZero (D.rowBot.homology i)) : D.InducesZero i j :=
  (D.δ_eq_zero_iff hij).1 (h.eq_of_src _ _)

/-- `S` induces the zero map `Hⁱ(Ṽ) → Hʲ(V)` when `Hʲ(V) = 0`. -/
theorem inducesZero_of_isZero_rowTop {i j : ι} (hij : c.Rel i j)
    (h : IsZero (D.rowTop.homology j)) : D.InducesZero i j :=
  (D.δ_eq_zero_iff hij).1 (h.eq_of_tgt _ _)

section Field

variable {K : Type u} [Field K] {V Vt : ι → Type v} [∀ i, AddCommGroup (V i)]
  [∀ i, Module K (V i)] [∀ i, AddCommGroup (Vt i)] [∀ i, Module K (Vt i)]
  (D : Data K c V Vt) {h i j : ι} (hhi : c.Rel h i) (hij : c.Rel i j)
  [FiniteDimensional K (D.rowTop.homology i)] [FiniteDimensional K (D.rowBot.homology i)]
include hhi hij

open Module

/-- **`dim Hⁱ(T) = dim Hⁱ(V) + dim Hⁱ(Ṽ)` iff `S` induces the zero maps `Hʰ(Ṽ) → Hⁱ(V)` and
`Hⁱ(Ṽ) → Hʲ(V)`.** [ArnoldHu2021], §5.1 -/
theorem finrank_twistComplex_homology_eq_iff :
    finrank K (D.twistComplex.homology i) =
        finrank K (D.rowTop.homology i) + finrank K (D.rowBot.homology i) ↔
      D.InducesZero h i ∧ D.InducesZero i j := by
  have : FiniteDimensional K (D.twistShortComplex.X₁.homology i) :=
    ‹FiniteDimensional K (D.rowTop.homology i)›
  have : FiniteDimensional K (D.twistShortComplex.X₃.homology i) :=
    ‹FiniteDimensional K (D.rowBot.homology i)›
  rw [← D.injective_homologyMap_rowTopι_iff hhi, ← D.surjective_homologyMap_rowBotπ_iff hij]
  exact D.twistShortComplex_shortExact.finrank_homology₂_eq_iff i

variable {D} {E F : ι → Prop} (hEF : D.Eliminates E F)
include hEF

/-- **Equality in the dimension bound of the derived complex** iff `S` induces the zero maps on
cohomology at `h → i` and `i → j`. [ArnoldHu2021], Theorem 6, (27) -/
theorem finrank_derived_homology_eq_iff :
    finrank K ((D.derived E F).homology i) =
        finrank K (D.rowTop.homology i) + finrank K (D.rowBot.homology i) ↔
      D.InducesZero h i ∧ D.InducesZero i j := by
  rw [(D.derivedHomologyIso hEF i).toLinearEquiv.finrank_eq]
  exact D.finrank_twistComplex_homology_eq_iff hhi hij

/-- **Equality in the dimension bound where a row has no cohomology at each connecting map**: if
`Hʰ(Ṽ) = 0` or `Hⁱ(V) = 0`, and `Hⁱ(Ṽ) = 0` or `Hʲ(V) = 0`, then `S` induces the zero maps on
cohomology at `h → i` and `i → j`, and `dim Hⁱ = dim Hⁱ(V) + dim Hⁱ(Ṽ)`.
[ArnoldHu2021], Theorem 6, (27) -/
theorem finrank_derived_homology_eq_add
    (h₁ : IsZero (D.rowBot.homology h) ∨ IsZero (D.rowTop.homology i))
    (h₂ : IsZero (D.rowBot.homology i) ∨ IsZero (D.rowTop.homology j)) :
    finrank K ((D.derived E F).homology i) =
      finrank K (D.rowTop.homology i) + finrank K (D.rowBot.homology i) :=
  (finrank_derived_homology_eq_iff hhi hij hEF).2
    ⟨h₁.elim (D.inducesZero_of_isZero_rowBot hhi) (D.inducesZero_of_isZero_rowTop hhi),
      h₂.elim (D.inducesZero_of_isZero_rowBot hij) (D.inducesZero_of_isZero_rowTop hij)⟩

end Field

end Feec.BGG.Data
