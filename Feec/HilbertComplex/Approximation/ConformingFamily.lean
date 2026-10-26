module

public import Feec.HilbertComplex.Approximation.CochainProjection
public import Feec.HilbertComplex.Window

/-!
# Conforming families of subcomplexes

A **conforming family** of a Hilbert complex `H` (`Feec.HilbertComplex.ConformingFamily`) is
finite-dimensional subcomplexes `Vₕ`, indexed by any type `κ` and refined along a filter `l`
(e.g. `h → 0` or `N → ∞`), with commuting cochain projections `πₕ` bounded in `W` uniformly in
`h`, and the **approximation property** `dist(w, Vₕⁱ) → 0` for every `w ∈ Wⁱ` in every degree.
This strengthens the data of the approximation theory of [AFW2010], §3.3, whose projections are
bounded and whose approximation holds in the graph norm of `V`: a commuting projection bounded in
`W` is bounded in `V` (`‖d πₕ x‖ = ‖πₕ d x‖`), and with it approximation in `W` gives
approximation in `V`. Projections bounded in `W` are the smoothed projections of [AFW2010], §5.5
and [ChristiansenWinther2008]; the canonical interpolants, bounded in `V` on smooth subspaces
only, are not. The complex is arbitrary: any scalar field,
any `ComplexShape`, any index type (a whole complex on `ℤ`, a window on `Fin m`, a short complex).

With a closed constraint a conforming family is a constrained FEEC discretization
(`ConformingFamily.withConstraint`, `Feec.HilbertComplex.ConstrainedFEEC`), and so falls under the
constrained FEEC theorem `Feec.HilbertComplex.constrainedFEEC` and the approximating FEEC theorem
`Feec.HilbertComplex.approxFEEC`. Every finite element family with uniformly bounded smoothed
projections (Whitney forms, every admissible sequence `P_rΛ`/`P_r⁻Λ`, on the Freudenthal cube,
parallelepipeds and domains star-shaped with respect to a ball) is one
(`Feec.Models.ConformingFamilies`).

## Main definitions

* `Feec.HilbertComplex.ConformingFamily H κ`; the constructor `ConformingFamily.ofExists` from the
  existence of uniformly bounded cochain projections.
* `Subcomplex.window`, `Subcomplex.CochainProjection.window`, `ConformingFamily.window`: the window
  `Vₕᵃ → ⋯ → Vₕ^{a+m-1}` of a family of a complex on `ComplexShape.up α` (`α = ℕ, ℤ`), a family of
  the window `H.window a m`.

## Main results

* `tendsto_infDist_submodule_iff`: the approximation property is eventual `ε`-approximation
  (`ConformingFamily.eventually_exists_lt`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (the approximation property, bounded cochain projections, in `V`), §5.5 (bounded smoothed
  projections in `W`)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (subcomplexes with bounded cochain projections)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.6 (the subcomplexes `Vₕ`)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

/-- **The approximation property, two ways**: `dist(y, Vₕ) → 0` along `l` iff for every `ε > 0`,
eventually some `v ∈ Vₕ` has `‖y - v‖ < ε`. -/
theorem tendsto_infDist_submodule_iff {𝕜 E κ : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup E] [Module 𝕜 E] {l : Filter κ} (V : κ → Submodule 𝕜 E) (y : E) :
    Tendsto (fun h => infDist y (V h : Set E)) l (𝓝 0) ↔
      ∀ ε > 0, ∀ᶠ h in l, ∃ v ∈ V h, ‖y - v‖ < ε := by
  refine ⟨fun hy ε hε => ?_, fun hy => tendsto_order.2 ⟨fun a ha =>
    Eventually.of_forall fun _ => ha.trans_le infDist_nonneg, fun a ha => ?_⟩⟩
  · filter_upwards [(tendsto_order.1 hy).2 ε hε] with h hh
    obtain ⟨v, hv, hd⟩ := (infDist_lt_iff ⟨0, (V h).zero_mem⟩).1 hh
    exact ⟨v, hv, by rwa [← dist_eq_norm]⟩
  · filter_upwards [hy a ha] with h ⟨v, hv, hlt⟩
    exact (infDist_le_dist_of_mem hv).trans_lt (by rwa [dist_eq_norm])

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-- A **conforming family** of the Hilbert complex `H`: finite-dimensional subcomplexes `Vₕ`
(`h : κ`, refined along the filter `l`) with commuting cochain projections `πₕ`, uniformly bounded
in `W`, and the approximation property `dist(w, Vₕⁱ) → 0` for every `w ∈ Wⁱ`. These strengthen
the hypotheses of the approximation theory of [AFW2010], §3.3 (bounds and approximation in `V`)
to bounds and approximation in `W`, as for the smoothed projections of [AFW2010], §5.5 (cf.
[Arnold2018], Ch. 5, [HolstStern2012], §3, [QuennevilleBelair2015], §4.6). -/
structure ConformingFamily (H : HilbertComplex 𝕜 c W) (κ : Type*) where
  /-- the filter along which the discretization is refined (e.g. `h → 0`) -/
  l : Filter κ
  /-- the discrete subcomplexes -/
  V : κ → H.Subcomplex
  [finiteDimensional : ∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
  /-- the commuting cochain projections -/
  π : ∀ h, (V h).CochainProjection
  bound_π : ∃ C, ∀ h i x, ‖(π h).π i x‖ ≤ C * ‖x‖
  /-- the approximation property: `dist(w, Vₕⁱ) → 0` for every `w ∈ Wⁱ` -/
  approx : ∀ i (w : W i), Tendsto (fun h => infDist w ((V h).V i : Set (W i))) l (𝓝 0)

attribute [instance] ConformingFamily.finiteDimensional

namespace ConformingFamily

variable {H : HilbertComplex 𝕜 c W} {κ : Type*}

/-- **A conforming family from uniformly bounded cochain projections**, when they are only known
to exist (as for the smoothed projections): the projections are chosen. -/
def ofExists (l : Filter κ) (V : κ → H.Subcomplex) [∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
    (hπ : ∃ (C : ℝ) (π : ∀ h, (V h).CochainProjection), ∀ h i x, ‖(π h).π i x‖ ≤ C * ‖x‖)
    (happrox : ∀ i (w : W i), Tendsto (fun h => infDist w ((V h).V i : Set (W i))) l (𝓝 0)) :
    ConformingFamily H κ where
  l := l
  V := V
  π := hπ.choose_spec.choose
  bound_π := ⟨hπ.choose, hπ.choose_spec.choose_spec⟩
  approx := happrox

variable (F : ConformingFamily H κ)

/-- The approximation property as eventual `ε`-approximation in every degree. -/
theorem eventually_exists_lt (i : ι) (w : W i) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in F.l, ∃ v ∈ (F.V h).V i, ‖w - v‖ < ε :=
  (tendsto_infDist_submodule_iff (fun h => (F.V h).V i) w).1 (F.approx i w) ε hε

end ConformingFamily

/-! ### Windows -/

section Window

variable {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α] [CharZero α] {V : α → Type*}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]
  {H : HilbertComplex 𝕜 (ComplexShape.up α) V}

/-- The window `Vₕᵃ → ⋯ → Vₕ^{a + m - 1}` of a subcomplex, a subcomplex of `H.window a m`
(reducible, so that instances on `Vₕ^{a+i}` apply to its spaces). -/
abbrev Subcomplex.window (S : H.Subcomplex) (a : α) (m : ℕ) : (H.window a m).Subcomplex where
  V i := S.V (a + i)
  le_domain _ _ := S.le_domain _ _
  mapsTo _ _ := S.mapsTo _ _

/-- The window of a cochain projection, a cochain projection onto the window of the subcomplex. -/
def Subcomplex.CochainProjection.window {S : H.Subcomplex} (P : S.CochainProjection) (a : α)
    (m : ℕ) : (S.window a m).CochainProjection where
  π i := P.π (a + i)
  mem _ x := P.mem _ x
  proj _ x hx := P.proj _ x hx
  comm _ _ x := P.comm _ _ x

variable {κ : Type*}

/-- **The window of a conforming family**: the windows `Vₕᵃ → ⋯ → Vₕ^{a + m - 1}` of the
subcomplexes, with the windows of the cochain projections, a conforming family of the window
`H.window a m`. -/
def ConformingFamily.window (F : ConformingFamily H κ) (a : α) (m : ℕ) :
    ConformingFamily (H.window a m) κ where
  l := F.l
  V h := (F.V h).window a m
  finiteDimensional h i := inferInstanceAs (FiniteDimensional 𝕜 ((F.V h).V (a + i)))
  π h := (F.π h).window a m
  bound_π := by
    obtain ⟨C, hC⟩ := F.bound_π
    exact ⟨C, fun h i x => hC h _ x⟩
  approx i w := F.approx (a + i) w

end Window

end Feec.HilbertComplex
