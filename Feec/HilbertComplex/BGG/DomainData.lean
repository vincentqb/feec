module

public import Feec.HilbertComplex.BGG.Derived
public import Feec.HilbertComplex.BGG.Twisted
public import Feec.HilbertComplex.DomainComplex

/-!
# Analytic BGG data restricted to the domains

Analytic BGG data `D : HilbertData 𝕜 c W Wt` (two Hilbert complexes and bounded connecting maps
`S` with `S D(d̃) ⊆ D(d)` and `d S = -S d̃`) restricts to the domain complexes: the domain spaces
`Vⁱ = D(dⁱ)`, `Ṽⁱ = D(d̃ⁱ)` (graph spaces), the bounded differentials and `S` form algebraic BGG
data (`HilbertData.domainData`). This is the bounded setting of [ArnoldHu2021], §3 (bounded
Hilbert complexes, e.g. the domain complexes, linked by bounded maps), so every algebraic result
of `Feec.HilbertComplex.BGG.Derived` applies: the BGG complex of the domain complexes has the
cohomology of their twisted complex (`HilbertData.domainBggHomologyIso`), and is exact when both
domain complexes are.

## Main definitions

* `Feec.BGG.HilbertData.domainS`: `S` between the domain spaces.
* `Feec.BGG.HilbertData.domainData`: the algebraic BGG data of the domain complexes.

## Main results

* `HilbertData.domainIncl_domainS`: `ι (S v) = S (ι v)`.
* `HilbertData.domainBggHomologyIso`, `HilbertData.domainBgg_acyclic`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3 (bounded Hilbert complexes
  and linking maps)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1.2 (domain complex)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

universe v

namespace Feec.BGG.HilbertData

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W Wt : ι → Type v}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (Wt i)] [∀ i, InnerProductSpace 𝕜 (Wt i)]
  [∀ i, CompleteSpace (Wt i)] (D : HilbertData 𝕜 c W Wt)

/-- `S` between the domain spaces: `D(d̃ⁱ) → D(dʲ)`, `v ↦ S v`. -/
def domainS (i j : ι) : D.Ht.domainSpace i →ₗ[𝕜] D.H.domainSpace j where
  toFun v := (D.H.d j (c.next j)).toGraphSpace
    ⟨D.S i j (D.Ht.domainIncl i v), D.S_mapsTo i j (c.next j) (D.Ht.domainCoord i j v)⟩
  map_add' u v := D.H.domainIncl_injective j (by simp [HilbertComplex.domainIncl])
  map_smul' a v := D.H.domainIncl_injective j (by simp [HilbertComplex.domainIncl])

@[simp] theorem domainIncl_domainS (i j : ι) (v : D.Ht.domainSpace i) :
    D.H.domainIncl j (D.domainS i j v) = D.S i j (D.Ht.domainIncl i v) := rfl

/-- **Analytic BGG data restricted to the domains** is algebraic BGG data on the domain
spaces, with the bounded differentials. -/
def domainData : Data 𝕜 c D.H.domainSpace D.Ht.domainSpace where
  d i j := D.H.domainD i j
  dt i j := D.Ht.domainD i j
  S := D.domainS
  shape_d i j h := by rw [D.H.domainD_eq_zero_of_not_rel h]; rfl
  shape_dt i j h := by rw [D.Ht.domainD_eq_zero_of_not_rel h]; rfl
  shape_S i j h := LinearMap.ext fun v => D.H.domainIncl_injective j (by
    rw [domainIncl_domainS, D.shape_S i j h]; simp)
  d_comp_d i j k x := D.H.domainD_comp_domainD i j k x
  dt_comp_dt i j k x := D.Ht.domainD_comp_domainD i j k x
  anticomm i j k v := D.H.domainIncl_injective k (by
    change D.H.domainIncl k (D.H.domainD j k (D.domainS i j v)) =
      D.H.domainIncl k (-D.domainS j k (D.Ht.domainD i j v))
    rw [map_neg, domainIncl_domainS, HilbertComplex.domainIncl_domainD,
      HilbertComplex.domainIncl_domainD]
    exact D.anticomm i j k (D.Ht.domainCoord i j v))

/-- **The BGG complex of the domain complexes has the cohomology of their twisted complex**,
for analytic BGG data on `ℤ` satisfying the injectivity/surjectivity condition at `J` between
the domains. [ArnoldHu2021], §5.2 -/
def domainBggHomologyIso {W Wt : ℤ → Type v} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    [∀ i, NormedAddCommGroup (Wt i)] [∀ i, InnerProductSpace 𝕜 (Wt i)]
    [∀ i, CompleteSpace (Wt i)] (D : HilbertData 𝕜 (ComplexShape.up ℤ) W Wt) {J : ℤ}
    (h : D.domainData.InjSurj J) (i : ℤ) :
    (D.domainData.bgg J).homology i ≅ D.domainData.twistComplex.homology i :=
  Data.bggHomologyIso h i

/-- **The BGG complex of the domain complexes is exact when both domain complexes are.** -/
theorem domainBgg_acyclic {W Wt : ℤ → Type v} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    [∀ i, NormedAddCommGroup (Wt i)] [∀ i, InnerProductSpace 𝕜 (Wt i)]
    [∀ i, CompleteSpace (Wt i)] (D : HilbertData 𝕜 (ComplexShape.up ℤ) W Wt) {J : ℤ}
    (h : D.domainData.InjSurj J) (hV : D.domainData.rowTop.Acyclic)
    (hVt : D.domainData.rowBot.Acyclic) : (D.domainData.bgg J).Acyclic :=
  Data.bgg_acyclic h hV hVt

end Feec.BGG.HilbertData
