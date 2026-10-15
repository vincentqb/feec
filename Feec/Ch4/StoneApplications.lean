module

public import Feec.Ch4.Stone
public import Feec.Ch4.TorusGroup
public import Feec.Ch4.BoundedDomain

/-!
# Consequences of Stone's theorem: the existence hypotheses of Ch. 4 discharged

`Feec.stoneGroup` (`Feec.Ch4.Stone`) constructs the orthogonal group of every skew-adjoint
operator. Every Ch. 4 result that took existence as a hypothesis (`WellPosedHom`,
`WellPosedExistence`, `WellPosedClassical`, or a `UnitaryGroupGenerator`) for a skew-adjoint
operator therefore holds unconditionally. This module records the unconditional forms.

## Main results

* Abstract Thm 4.3 for skew-adjoint `A`: `IsSkewAdjoint.wellPosedHom`,
  `IsSkewAdjoint.wellPosedClassical` (homogeneous, classical regularity),
  `IsSkewAdjoint.wellPosedClassical_forcing`, `IsSkewAdjoint.wellPosedExistence`
  (forcing in `ForcingDL A T = C([0,T]; D(A))`), and `thm_4_3_of_isSkewAdjoint` (existence of a
  classical solution, uniqueness among strong solutions).
* Thesis Cor 4.5 without its existence hypothesis: `cor_4_5_of_isSkewAdjoint`.
* Hodge wave equation of any Hilbert complex: `HilbertComplex2.waveGroup`,
  `HilbertComplex2.thm_4_6_unconditional` (Thm 4.6 with the thesis' regularity) and
  `HilbertComplex2.thm_4_3_hodgeWave` (inhomogeneous).
* Props 4.17/4.19, abstract: `Constraints.prop_4_17_necessary_unconditional`,
  `Constraints.prop_4_17_iff_unconditional` (constraint propagation iff `P_K D(L) ⊆ D(L)`, given
  `D(L) ∩ K` dense in `K`; no group hypothesis).
* Bounded domains: `BoundedDomain.exists_orbit_not_propagate_unconditional` and
  `BoundedDomain.thesisComplex_orbit_not_propagate_unconditional`: for the thesis' complex
  `H̊¹ → H̊(curl) → L²` on any nonempty bounded open `Ω ⊆ ℝ³` there are TSD data in `D(L)`
  whose (existing, unique) solution of (4.14) leaves `K = {0} × L²(TSD) × L²(TSD)` on every
  `[0, T]`, `T > 0`.

Correction: the conclusion of [QuennevilleBelair2015, §4.10, Prop 4.17] fails on every nonempty
bounded open domain, now with no hypothesis at all: `thesisComplex_orbit_not_propagate`
(`Feec.Ch4.BoundedDomain`) assumed a Stone group, which `HilbertComplex2.waveGroup` supplies.

Correction: the forcing class here is `C([0,T]; D(A))`, a subclass of the thesis'
`C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(A)))` in Thm 4.3.

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3, Thm 4.4, Cor 4.5), §4.4 (Thm 4.6), §4.10
  (Props 4.17, 4.19)
* [Pazy1983], §1.10 (Stone's theorem), §4.2 (Duhamel's formula)
* [CazenaveHaraux1998], Prop 4.1.6 and Cor 2.4.9 (the results cited by the thesis for Thm 4.3)
* [Arnold2018] (Hilbert complexes and the Hodge wave operator)
-/

open scoped RealInnerProductSpace LinearPMap
open Set

@[expose] public noncomputable section

namespace Feec

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {A : E →ₗ.[ℝ] E}

/-- `WellPosedHom A T` for every skew-adjoint `A` and every `T` (the hypothesis of Thm 4.6
and of the bounded-domain Prop 4.17 analysis), from `Feec.stoneGroup`.
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, §1.10]. -/
theorem IsSkewAdjoint.wellPosedHom (hA : IsSkewAdjoint A) (T : ℝ) : WellPosedHom A T :=
  (stoneGroup hA).wellPosedHom T

/-- Classical solutions `U ∈ C⁰([0,T]; D(A)) ∩ C¹([0,T]; X)` of `U' = A U`, `U(0) = U₀`, for
every skew-adjoint `A`. See [QuennevilleBelair2015, Thm 4.3] (homogeneous case). -/
theorem IsSkewAdjoint.wellPosedClassical (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedClassical A T (fun F => F = 0) :=
  (stoneGroup hA).wellPosedClassical T

/-- Classical solutions of `U' = A U + F` for every skew-adjoint `A` and forcing
`F ∈ C([0,T]; D(A))` (Duhamel's formula, `UnitaryGroupGenerator.wellPosedClassical_forcing`).
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, §4.2]. -/
theorem IsSkewAdjoint.wellPosedClassical_forcing (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedClassical A T (ForcingDL A T) :=
  (stoneGroup hA).wellPosedClassical_forcing T

/-- `WellPosedExistence A T (ForcingDL A T)` for every skew-adjoint `A`: the explicit
existence hypothesis of `Feec.Foundation.Evolution` is a theorem for this forcing class.
See [QuennevilleBelair2015, Thm 4.3]. -/
theorem IsSkewAdjoint.wellPosedExistence (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedExistence A T (ForcingDL A T) :=
  (hA.wellPosedClassical_forcing T).wellPosedExistence

/-- **Thesis Thm 4.3** for skew-adjoint `A` (dense domain is automatic) and forcing
`F ∈ C([0,T]; D(A))`: there is a classical solution `U ∈ C⁰([0,T]; D(A)) ∩ C¹([0,T]; X)` of
`U' = A U + F`, `U(0) = U₀`, unique among strong solutions.

Correction: the thesis' forcing class is `C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(A)))`;
this covers its subclass `C([0,T]; D(A))`.
See [QuennevilleBelair2015, Thm 4.3]; cf. [CazenaveHaraux1998, Prop 4.1.6], [Pazy1983, §4.2]. -/
theorem thm_4_3_of_isSkewAdjoint (hA : IsSkewAdjoint A) (T : ℝ) {U₀ : E} (hU₀ : U₀ ∈ A.domain)
    {F : ℝ → E} (hF : ForcingDL A T F) :
    ∃ U, IsClassicalSolution A T U₀ F U ∧
      ∀ U', IsStrongSolution A T U₀ F U' → EqOn U' U (Icc 0 T) := by
  obtain ⟨U, hU⟩ := hA.wellPosedClassical_forcing T U₀ hU₀ F hF
  exact ⟨U, hU, fun U' hU' => strongSolution_unique A (hA.isSkewSymm hA.dense_domain) hU'
    hU.toIsStrongSolution⟩

/-- **Thesis Cor 4.5**, unconditional (forcing in `C([0,T]; D(L))`): under the hypotheses
of Thm 4.4 (`P_K D(L) ⊆ D(L)`, `L (D(L) ∩ K) ⊆ K`), the restricted problem in `K` has a unique
classical solution, which coincides with the solution in `X`.
See [QuennevilleBelair2015, Thm 4.4, Cor 4.5]. -/
theorem cor_4_5_of_isSkewAdjoint (L : E →ₗ.[ℝ] E) (hL : IsSkewAdjoint L)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] [CompleteSpace K]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    (T : ℝ) (U₀ : K) (hU₀ : (U₀ : E) ∈ L.domain) (F : ℝ → K)
    (hF : ForcingDL L T fun t => (F t : E)) :
    IsSkewAdjoint (Feec.restrictTo L K h3) ∧
    ∃ Ut : ℝ → K, IsClassicalSolution (Feec.restrictTo L K h3) T U₀ F Ut ∧
      (∀ V, IsStrongSolution (Feec.restrictTo L K h3) T U₀ F V → EqOn V Ut (Icc 0 T)) ∧
      ∀ U, IsStrongSolution L T U₀ (fun t => F t) U → ∀ t ∈ Icc 0 T, (Ut t : E) = U t :=
  cor_4_5_classical L hL.dense_domain hL K h1 h3 (hL.wellPosedClassical_forcing T) U₀ hU₀ F hF

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

/-- **Thesis Thm 4.6**, unconditional: for every Hilbert complex, every `ξ₀ ∈ D(L)` and
every horizon `T`, the Hodge wave equation `ξ' = -L ξ`, `ξ(0) = ξ₀` has a solution in
`C⁰([0,T]; D(L)) ∩ C¹([0,T]; W)`, unique among strong solutions, conserving energy.
See [QuennevilleBelair2015, Thm 4.6]. -/
theorem thm_4_6_unconditional (T : ℝ) {ξ₀ : Tot W0 W1 W2} (h0 : ξ₀ ∈ H.waveOp.domain) :
    ∃ ξ, IsClassicalSolution (-H.waveOp) T ξ₀ 0 ξ ∧
      (∀ ξ', IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ' → EqOn ξ' ξ (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, ‖ξ t‖ = ‖ξ₀‖ :=
  H.thm_4_6_classical_of_unitaryGroupGenerator H.waveGroup T h0

/-- The inhomogeneous Hodge wave equation `ξ' = -L ξ + F`, `F ∈ C([0,T]; D(L))`, has a unique
classical solution, for every Hilbert complex.
See [QuennevilleBelair2015, Thm 4.3, §4.4]. -/
theorem thm_4_3_hodgeWave (T : ℝ) {ξ₀ : Tot W0 W1 W2} (h0 : ξ₀ ∈ H.waveOp.domain)
    {F : ℝ → Tot W0 W1 W2} (hF : ForcingDL (-H.waveOp) T F) :
    ∃ ξ, IsClassicalSolution (-H.waveOp) T ξ₀ F ξ ∧
      ∀ ξ', IsStrongSolution (-H.waveOp) T ξ₀ F ξ' → EqOn ξ' ξ (Icc 0 T) :=
  thm_4_3_of_isSkewAdjoint H.neg_waveOp_isSkewAdjoint T h0 hF

end HilbertComplex2

namespace Constraints

open HilbertComplex2

variable {W0 W1 W2 : Type*}
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
  (H : HilbertComplex2 W0 W1 W2) {S1 : Submodule ℝ W1} {S2 : Submodule ℝ W2}
  [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection]

/-- **Necessity of the projection hypothesis in Props 4.17/4.19**, with no group hypothesis:
if `D(L) ∩ K` is dense in `K` and every strong solution of (4.14) starting in `K` stays in `K`,
then `P_K D(L) ⊆ D(L)`. (Not in the thesis.)
Cf. [QuennevilleBelair2015, Props 4.17 and 4.19]. -/
theorem prop_4_17_necessary_unconditional
    (hdense : ∀ k ∈ Kc W0 S1 S2, k ∈ closure ((H.domL : Set (Tot W0 W1 W2)) ∩ Kc W0 S1 S2))
    (hprop : ∀ (T : ℝ) (U₀ : Tot W0 W1 W2) (U : ℝ → Tot W0 W1 W2), U₀ ∈ Kc W0 S1 S2 →
      IsStrongSolution (-H.waveOp) T U₀ 0 U → ∀ t ∈ Icc 0 T, U t ∈ Kc W0 S1 S2) :
    ∀ x ∈ H.domL, projKc W0 S1 S2 x ∈ H.domL :=
  prop_4_17_necessary H.waveGroup hdense hprop

/-- **Props 4.17/4.19, characterization**, with no group hypothesis: if `D(L) ∩ K` is dense
in `K`, TSD-type constraints propagate for all data iff `P_K D(L) ⊆ D(L)`.
Cf. [QuennevilleBelair2015, Props 4.17 and 4.19]. -/
theorem prop_4_17_iff_unconditional (hS1 : S1 ≤ H.d0†.ker)
    (hd1 : ∀ u : H.d1.domain, (u : W1) ∈ S1 → H.d1 u ∈ S2)
    (hd1s : ∀ ρ : H.d1†.domain, (ρ : W2) ∈ S2 → H.d1† ρ ∈ S1)
    (hdense : ∀ k ∈ Kc W0 S1 S2, k ∈ closure ((H.domL : Set (Tot W0 W1 W2)) ∩ Kc W0 S1 S2)) :
    (∀ (T : ℝ) (U₀ : Tot W0 W1 W2) (U : ℝ → Tot W0 W1 W2), U₀ ∈ Kc W0 S1 S2 →
      IsStrongSolution (-H.waveOp) T U₀ 0 U → ∀ t ∈ Icc 0 T, U t ∈ Kc W0 S1 S2) ↔
      ∀ x ∈ H.domL, projKc W0 S1 S2 x ∈ H.domL :=
  prop_4_17_iff H.waveGroup hS1 hd1 hd1s hdense

end Constraints

namespace BoundedDomain

open HilbertComplex2 Constraints

variable {Ω : Set R3}

variable {W0 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0] in
/-- **Prop 4.17's conclusion fails on bounded domains**, for every Hilbert complex
`W0 → L²(Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)` whose `d1` is contained in the closed curl: some TSD datum in
`D(L)` has a strong solution of (4.14) (the Stone orbit) that leaves `K` on every `[0, T]`.

Correction: [QuennevilleBelair2015, §4.10, Prop 4.17]; `exists_orbit_not_propagate` with its
Stone-group hypothesis discharged. -/
theorem exists_orbit_not_propagate_unconditional (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (H : HilbertComplex2 W0 (L2M Ω) (L2M Ω))
    (hd1 : ∀ u : H.d1.domain, ((u : L2M Ω), H.d1 u) ∈ closure (curlGraph Ω)) :
    ∃ B₀ : L2M Ω, B₀ ∈ TSD Ω ∧ ini W0 0 B₀ ∈ H.domL ∧
      ini W0 0 B₀ ∈ Kc W0 (TSD Ω) (TSD Ω) ∧
      ∀ T > 0, ∃ U : ℝ → Tot W0 (L2M Ω) (L2M Ω),
        IsStrongSolution (-H.waveOp) T (ini W0 0 B₀) 0 U ∧
        ∃ t ∈ Icc 0 T, U t ∉ Kc W0 (TSD Ω) (TSD Ω) := by
  obtain ⟨B₀, hB, hD, hK, hall⟩ := exists_orbit_not_propagate hΩ hb hne H hd1 H.waveGroup
  exact ⟨B₀, hB, hD, hK, fun T hT => ⟨_, hall T hT⟩⟩

/-- **The conclusion of Prop 4.17 fails for the thesis' complex** `H̊¹ → H̊(curl) → L²` on
every nonempty bounded open `Ω`, unconditionally: there is TSD data `(0, 0, β) ∈ D(L) ∩ K` whose
solution of (4.14) exists (Stone) and leaves `K = {0} × L²(TSD) × L²(TSD)` on every `[0, T]`,
`T > 0`. By `thesisComplex_not_propagate` every strong solution with this datum leaves `K`.

Correction: [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem thesisComplex_orbit_not_propagate_unconditional (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ∃ B₀ : L2M Ω, B₀ ∈ TSD Ω ∧ ini (L2V Ω) 0 B₀ ∈ (thesisComplex hΩ hb).domL ∧
      ini (L2V Ω) 0 B₀ ∈ Kc (L2V Ω) (TSD Ω) (TSD Ω) ∧
      ∀ T > 0, ∃ U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω),
        IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) 0 B₀) 0 U ∧
        ∃ t ∈ Icc 0 T, U t ∉ Kc (L2V Ω) (TSD Ω) (TSD Ω) := by
  obtain ⟨B₀, hB, hD, hK, hall⟩ :=
    thesisComplex_orbit_not_propagate hΩ hb hne (thesisComplex hΩ hb).waveGroup
  exact ⟨B₀, hB, hD, hK, fun T hT => ⟨_, hall T hT⟩⟩

end BoundedDomain

end Feec
