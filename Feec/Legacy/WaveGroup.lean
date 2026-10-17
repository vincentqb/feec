module

public import Feec.Legacy.Stone
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Feec.Legacy.Restriction
public import Feec.Evolution.Forcing
public import Feec.Evolution.WellPosed
public import Feec.Legacy.Torus.Group
public import Feec.Legacy.BoundedDomain.Basic

/-!
# Consequences of Stone's theorem: the existence hypotheses of Ch. 4 discharged

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use.
Most of the original module was re-derived in the general layers (see
`docs/migration/map.tsv`); what remains is listed below.

## Contents

* `IsSkewAdjoint.wellPosedHom`: `WellPosedHom A T` for every skew-adjoint `A` and every `T` (the hypothesis of Thm 4.6 and of the bounded-domain Prop 4.17 analysis), from `Feec.Legacy.stoneGroup`.
* `IsSkewAdjoint.wellPosedClassical`: Classical solutions `U ∈ C⁰([0,T]; D(A)) ∩ C¹([0,T]; X)` of `U' = A U`, `U(0) = U₀`, for every skew-adjoint `A`.
* `HilbertComplex2.waveGroup`: The Hodge wave group `e^{-tL}` of any Hilbert complex: `-L` is skew-adjoint (`neg_waveOp_isSkewAdjoint`), so Stone's theorem applies.
* `HilbertComplex2.existsUnique_classicalSolution_neg_waveOp`: **Existence and uniqueness for the Hodge wave equation** (Thesis Thm 4.6): for every Hilbert complex, every `ξ₀ ∈ D(L)` and every horizon `T`, the Hodge wave equation `ξ' = -L ξ`, `ξ(0) = ξ₀` has a solution in `C⁰([0,T]; D(L)) ∩ C¹([0,T]; W)`, unique among strong solutions, conserving energy.
* `HilbertComplex2.isClassicalSolution_of_isWeakSolution`: **Weak solutions are classical** (Thesis Thm 4.7, second bullet, with the thesis' regularity): for every Hilbert complex, a weak solution of (4.7)/(4.8) with initial value in `D(L)` lies in `C⁰([0,T]; D(L)) ∩ C¹([0,T]; W)` and solves (4.4).
* `Constraints.propagates_iff_projKc_mem_domL`: **Props 4.17/4.19, characterization**, with no group hypothesis: if `D(L) ∩ K` is dense in `K`, TSD-type constraints propagate for all data iff `P_K D(L) ⊆ D(L)`.
* `Constraints.existsUnique_classicalSolution_mem_K`: **Prop 4.16 with existence and the thesis' regularity**: for every closed `Y ⊇ range d1` and data in `D(L) ∩ K`, `K = {0} × ker d0* × Y`, the Hodge wave equation has a solution in `C⁰([0,T]; D(L)) ∩ C¹([0,T]; W)`, unique among strong solutions, which stays in `K`.
* `Constraints.existsUnique_divFree_mem`: **Prop 4.16 with existence** (strong-solution form): data in `D(L) ∩ K` have a unique strong solution of the Hodge wave equation, and it stays in `K = {0} × ker d0* × Y`.
* `Constraints.existsUnique_reducedSolution`: **Prop 4.18**: for `E₀ ∈ V1 ∩ ker d0*`, `B₀ ∈ V2*`, the reduced system (4.15) has a unique strong solution, `E` stays in `ker d0*`, and `(0, E, B)` solves (4.14).
* `BoundedDomain.exists_tsd_not_propagates`: **TSD constraints do not propagate on bounded domains**, for every Hilbert complex `W0 → L²(Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)` whose `d1` is contained in the closed curl: some TSD datum `(0, 0, β) ∈ D(L) ∩ K` has, on every `[0, T]` with `T > 0`, a strong solution of (4.14), and every strong solution with this datum leaves `K = {0} × L²(TSD) × L²(TSD)`.
* `BoundedDomain.thesisComplex_tsd_not_propagates`: **TSD constraints do not propagate for the thesis' complex** `H̊¹ → H̊(curl) → L²` on every nonempty bounded open `Ω ⊆ ℝ³`: there is TSD data `(0, 0, β) ∈ D(L) ∩ K` such that, for every `T > 0`, (4.14) has a strong solution on `[0, T]` (Stone's theorem) and every strong solution leaves `K = {0} × L²(TSD) × L²(TSD)` somewhere in `[0, T]`.

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3, Thm 4.4, Cor 4.5), §4.4 (Thm 4.6), §4.10
  (Props 4.16–4.19), §4.4 (Thm 4.7)
* [Pazy1983], §1.10 (Stone's theorem), §4.2 (Duhamel's formula, Cor 4.2.5)
* [CazenaveHaraux1998], Prop 4.1.6 and Cor 2.4.9 (the results cited by the thesis for Thm 4.3)
* [Arnold2018] (Hilbert complexes and the Hodge wave operator)
-/

open scoped RealInnerProductSpace LinearPMap
open Set

@[expose] public noncomputable section

namespace Feec.Legacy

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {A : E →ₗ.[ℝ] E}

/-- `WellPosedHom A T` for every skew-adjoint `A` and every `T` (the hypothesis of Thm 4.6
and of the bounded-domain Prop 4.17 analysis), from `Feec.Legacy.stoneGroup`.
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, §1.10]. -/
theorem IsSkewAdjoint.wellPosedHom (hA : IsSkewAdjoint A) (T : ℝ) : WellPosedHom A T :=
  (stoneGroup hA).wellPosedHom T

/-- Classical solutions `U ∈ C⁰([0,T]; D(A)) ∩ C¹([0,T]; X)` of `U' = A U`, `U(0) = U₀`, for
every skew-adjoint `A`. See [QuennevilleBelair2015, Thm 4.3] (homogeneous case). -/
theorem IsSkewAdjoint.wellPosedClassical (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedClassical A T (fun F => F = 0) :=
  (stoneGroup hA).wellPosedClassical T

end General

namespace HilbertComplex2

variable {W0 W1 W2 : Type*}
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
  (H : HilbertComplex2 W0 W1 W2)

/-- The Hodge wave group `e^{-tL}` of any Hilbert complex: `-L` is skew-adjoint
(`neg_waveOp_isSkewAdjoint`), so Stone's theorem applies.
See [QuennevilleBelair2015, §4.4, (4.5)]; cf. [Arnold2018]. -/
def waveGroup : UnitaryGroupGenerator (-H.waveOp) := stoneGroup H.neg_waveOp_isSkewAdjoint

/-- **Existence and uniqueness for the Hodge wave equation** (Thesis Thm 4.6): for every
Hilbert complex, every `ξ₀ ∈ D(L)` and every horizon `T`, the Hodge wave equation
`ξ' = -L ξ`, `ξ(0) = ξ₀` has a solution in `C⁰([0,T]; D(L)) ∩ C¹([0,T]; W)`, unique among strong
solutions, conserving energy. The existence hypothesis of `existsUnique_classical_of_wellPosed` is discharged by
Stone's theorem (`waveGroup`). See [QuennevilleBelair2015, Thm 4.6]. -/
theorem existsUnique_classicalSolution_neg_waveOp (T : ℝ) {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) :
    ∃ ξ, IsClassicalSolution (-H.waveOp) T ξ₀ 0 ξ ∧
      (∀ ξ', IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ' → EqOn ξ' ξ (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, ‖ξ t‖ = ‖ξ₀‖ :=
  H.existsUnique_classical_of_unitaryGroupGenerator H.waveGroup T h0

/-- **Weak solutions are classical** (Thesis Thm 4.7, second bullet, with the thesis'
regularity): for every Hilbert complex, a weak solution of (4.7)/(4.8) with initial value in
`D(L)` lies in `C⁰([0,T]; D(L)) ∩ C¹([0,T]; W)` and solves (4.4). `weak_imp_classical` with its
existence hypothesis discharged by Stone's theorem. See [QuennevilleBelair2015, Thm 4.7]. -/
theorem isClassicalSolution_of_isWeakSolution {T : ℝ} {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) {ξ : ℝ → Tot W0 W1 W2} (hξ : H.IsWeakSolution T ξ₀ ξ) :
    IsClassicalSolution (-H.waveOp) T ξ₀ 0 ξ :=
  H.weak_imp_classical (H.neg_waveOp_isSkewAdjoint.wellPosedClassical T) rfl h0 hξ

end HilbertComplex2

namespace Constraints

open HilbertComplex2

variable {W0 W1 W2 : Type*}
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
  (H : HilbertComplex2 W0 W1 W2) {S1 : Submodule ℝ W1} {S2 : Submodule ℝ W2}
  [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection]

/-- **Props 4.17/4.19, characterization**, with no group hypothesis: if `D(L) ∩ K` is dense
in `K`, TSD-type constraints propagate for all data iff `P_K D(L) ⊆ D(L)`.
Cf. [QuennevilleBelair2015, Props 4.17 and 4.19]. -/
theorem propagates_iff_projKc_mem_domL (hS1 : S1 ≤ H.d0†.ker)
    (hd1 : ∀ u : H.d1.domain, (u : W1) ∈ S1 → H.d1 u ∈ S2)
    (hd1s : ∀ ρ : H.d1†.domain, (ρ : W2) ∈ S2 → H.d1† ρ ∈ S1)
    (hdense : ∀ k ∈ Kc W0 S1 S2, k ∈ closure ((H.domL : Set (Tot W0 W1 W2)) ∩ Kc W0 S1 S2)) :
    (∀ (T : ℝ) (U₀ : Tot W0 W1 W2) (U : ℝ → Tot W0 W1 W2), U₀ ∈ Kc W0 S1 S2 →
      IsStrongSolution (-H.waveOp) T U₀ 0 U → ∀ t ∈ Icc 0 T, U t ∈ Kc W0 S1 S2) ↔
      ∀ x ∈ H.domL, projKc W0 S1 S2 x ∈ H.domL :=
  Kc_propagates_iff H.waveGroup hS1 hd1 hd1s hdense

variable {H} in
/-- **Prop 4.16 with existence and the thesis' regularity**: for every closed `Y ⊇ range d1` and
data in `D(L) ∩ K`, `K = {0} × ker d0* × Y`, the Hodge wave equation has a solution in
`C⁰([0,T]; D(L)) ∩ C¹([0,T]; W)`, unique among strong solutions, which stays in `K`.
See [QuennevilleBelair2015, Prop 4.16]. -/
theorem existsUnique_classicalSolution_mem_K (Y : Submodule ℝ W2) [Y.HasOrthogonalProjection]
    (hY : LinearMap.range H.d1.toFun ≤ Y) (T : ℝ) {U₀ : Tot W0 W1 W2} (hD : U₀ ∈ H.domL)
    (hU₀ : U₀ ∈ K H Y) :
    ∃ U, IsClassicalSolution (-H.waveOp) T U₀ 0 U ∧ (∀ t ∈ Icc 0 T, U t ∈ K H Y) ∧
      ∀ U', IsStrongSolution (-H.waveOp) T U₀ 0 U' → EqOn U' U (Icc 0 T) := by
  obtain ⟨U, hU, huniq, -⟩ := H.existsUnique_classicalSolution_neg_waveOp T hD
  exact ⟨U, hU, divFree_propagates hY hU.toIsStrongSolution hU₀, huniq⟩

/-- **Prop 4.16 with existence** (strong-solution form): data in `D(L) ∩ K` have a unique strong
solution of the Hodge wave equation, and it stays in `K = {0} × ker d0* × Y`. Corollary of
`existsUnique_classicalSolution_mem_K`. See [QuennevilleBelair2015, Prop 4.16]. -/
theorem existsUnique_divFree_mem (Y : Submodule ℝ W2) [Y.HasOrthogonalProjection]
    (hY : LinearMap.range H.d1.toFun ≤ Y) (T : ℝ) {U₀ : Tot W0 W1 W2} (hD : U₀ ∈ H.domL)
    (hU₀ : U₀ ∈ K H Y) :
    ∃ U, IsStrongSolution (-H.waveOp) T U₀ 0 U ∧ (∀ t ∈ Icc 0 T, U t ∈ K H Y) ∧
      ∀ U', IsStrongSolution (-H.waveOp) T U₀ 0 U' → EqOn U U' (Icc 0 T) := by
  obtain ⟨U, hU, hK, huniq⟩ := existsUnique_classicalSolution_mem_K Y hY T hD hU₀
  exact ⟨U, hU.toIsStrongSolution, hK, fun U' hU' => (huniq U' hU').symm⟩

/-- **Prop 4.18**: for `E₀ ∈ V1 ∩ ker d0*`, `B₀ ∈ V2*`, the reduced system (4.15) has a unique
strong solution, `E` stays in `ker d0*`, and `(0, E, B)` solves (4.14). `reducedSolution_of_wellPosedHom` with its
existence hypothesis discharged by Stone's theorem. See [QuennevilleBelair2015, Prop 4.18]. -/
theorem existsUnique_reducedSolution (T : ℝ) {E₀ : W1} {B₀ : W2}
    (hE₀ : E₀ ∈ H.d1.domain) (hE₀k : E₀ ∈ H.d0†.ker) (hB₀ : B₀ ∈ H.d1†.domain) :
    ∃ E B, IsReducedSolution H T E₀ B₀ E B ∧ (∀ t ∈ Icc 0 T, E t ∈ H.d0†.ker) ∧
      IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0
        (fun t => (tot W0 W1 W2).symm (0, E t, B t)) ∧
      ∀ E' B', IsReducedSolution H T E₀ B₀ E' B' → EqOn E E' (Icc 0 T) ∧ EqOn B B' (Icc 0 T) :=
  reducedSolution_of_wellPosedHom (H.neg_waveOp_isSkewAdjoint.wellPosedHom T) hE₀ hE₀k hB₀

end Constraints

namespace BoundedDomain

open HilbertComplex2 Constraints

variable {Ω : Set R3}

variable {W0 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0] in
/-- **TSD constraints do not propagate on bounded domains**, for every Hilbert complex
`W0 → L²(Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)` whose `d1` is contained in the closed curl: some TSD datum
`(0, 0, β) ∈ D(L) ∩ K` has, on every `[0, T]` with `T > 0`, a strong solution of (4.14), and
every strong solution with this datum leaves `K = {0} × L²(TSD) × L²(TSD)`.

Correction: [QuennevilleBelair2015, §4.10, Prop 4.17]. `exists_orbit_not_propagate` with its
Stone-group hypothesis discharged by `HilbertComplex2.waveGroup`; the "every solution" half is
uniqueness of strong solutions (`IsStrongSolution.unique`). -/
theorem exists_tsd_not_propagates (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (H : HilbertComplex2 W0 (L2M Ω) (L2M Ω))
    (hd1 : ∀ u : H.d1.domain, ((u : L2M Ω), H.d1 u) ∈ closure (curlGraph Ω)) :
    ∃ B₀ : L2M Ω, B₀ ∈ TSD Ω ∧ ini W0 0 B₀ ∈ H.domL ∧
      ini W0 0 B₀ ∈ Kc W0 (TSD Ω) (TSD Ω) ∧
      ∀ T > 0, (∃ U : ℝ → Tot W0 (L2M Ω) (L2M Ω),
          IsStrongSolution (-H.waveOp) T (ini W0 0 B₀) 0 U) ∧
        ∀ U : ℝ → Tot W0 (L2M Ω) (L2M Ω),
          IsStrongSolution (-H.waveOp) T (ini W0 0 B₀) 0 U →
            ∃ t ∈ Icc 0 T, U t ∉ Kc W0 (TSD Ω) (TSD Ω) := by
  obtain ⟨B₀, hB, hD, hK, hall⟩ := exists_orbit_not_propagate hΩ hb hne H hd1 H.waveGroup
  have hdiss := (H.neg_waveOp_isSkewAdjoint.isSkewSymm
    H.neg_waveOp_isSkewAdjoint.dense_domain).isDissipative
  refine ⟨B₀, hB, hD, hK, fun T hT => ?_⟩
  obtain ⟨hS, t, ht, hn⟩ := hall T hT
  refine ⟨⟨_, hS⟩, fun U hU => ⟨t, ht, ?_⟩⟩
  rw [hU.unique hdiss hS ht]
  exact hn

/-- **TSD constraints do not propagate for the thesis' complex** `H̊¹ → H̊(curl) → L²` on every
nonempty bounded open `Ω ⊆ ℝ³`: there is TSD data `(0, 0, β) ∈ D(L) ∩ K` such that, for every
`T > 0`, (4.14) has a strong solution on `[0, T]` (Stone's theorem) and every strong solution
leaves `K = {0} × L²(TSD) × L²(TSD)` somewhere in `[0, T]`.

Correction: [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem thesisComplex_tsd_not_propagates (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ∃ B₀ : L2M Ω, B₀ ∈ TSD Ω ∧ ini (L2V Ω) 0 B₀ ∈ (thesisComplex hΩ hb).domL ∧
      ini (L2V Ω) 0 B₀ ∈ Kc (L2V Ω) (TSD Ω) (TSD Ω) ∧
      ∀ T > 0, (∃ U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω),
          IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) 0 B₀) 0 U) ∧
        ∀ U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω),
          IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) 0 B₀) 0 U →
            ∃ t ∈ Icc 0 T, U t ∉ Kc (L2V Ω) (TSD Ω) (TSD Ω) :=
  exists_tsd_not_propagates hΩ hb hne _ (mem_closure_curlClosure hΩ hb)

end BoundedDomain

end Feec.Legacy
