module

public import Feec.Ch4.Stone
public import Feec.Ch4.StoneDuhamel
public import Feec.Ch4.TorusGroup
public import Feec.Ch4.BoundedDomain

/-!
# Consequences of Stone's theorem: the existence hypotheses of Ch. 4 discharged

`Feec.stoneGroup` (`Feec.Ch4.Stone`) constructs the orthogonal group of every skew-adjoint
operator. The Ch. 4 results that take existence as a hypothesis (`WellPosedHom`,
`WellPosedExistence`, `WellPosedClassical`, or a `UnitaryGroupGenerator`) therefore hold
unconditionally for skew-adjoint operators. This module records the unconditional forms of
Thm 4.3, Cor 4.5 (strong, classical and ambient forms), Thm 4.6, Thm 4.7 (strong and classical),
Prop 4.16 with existence, Prop 4.18, Props 4.17/4.19 and the bounded-domain counterexample to
Prop 4.17. Forcing is in `ForcingThm43 A T = C([0,T]; D(A)) ∪ ForcingW11 T`.

## Main results

* Abstract Thm 4.3 for skew-adjoint `A`: `IsSkewAdjoint.wellPosedHom`,
  `IsSkewAdjoint.wellPosedClassical` (homogeneous, classical regularity),
  `IsSkewAdjoint.wellPosedClassical_forcing`, `IsSkewAdjoint.wellPosedExistence`
  (forcing in `ForcingDL A T = C([0,T]; D(A))`), `IsSkewAdjoint.wellPosedClassical_W11`
  (`W^{1,1}`-type forcing), `IsSkewAdjoint.wellPosedClassical_thm43`,
  `IsSkewAdjoint.wellPosedExistence_thm43`, `thm_4_3_of_isSkewAdjoint` and
  `thm_4_3_unconditional` (existence of a classical solution, uniqueness among strong
  solutions).
* Cor 4.5 without its existence hypothesis: `cor_4_5_of_isSkewAdjoint`,
  `cor_4_5_unconditional`, `cor_4_5_classical_unconditional`, `cor_4_5_ambient_unconditional`.
* Hodge wave equation of any Hilbert complex: `HilbertComplex2.waveGroup`,
  `HilbertComplex2.thm_4_6_unconditional` (Thm 4.6 with the thesis' regularity),
  `HilbertComplex2.thm_4_3_hodgeWave` (inhomogeneous), `HilbertComplex2.thm_4_7_unconditional`
  and `HilbertComplex2.thm_4_7_classical_unconditional` (strong = weak solutions).
* Props 4.16/4.18: `Constraints.prop_4_16_exists_unconditional`,
  `Constraints.prop_4_18_unconditional`.
* Props 4.17/4.19, abstract: `Constraints.prop_4_17_necessary_unconditional`,
  `Constraints.prop_4_17_iff_unconditional` (constraint propagation iff `P_K D(L) ⊆ D(L)`, given
  `D(L) ∩ K` dense in `K`; no group hypothesis).
* Bounded domains: `BoundedDomain.exists_orbit_not_propagate_unconditional` and
  `BoundedDomain.thesisComplex_orbit_not_propagate_unconditional`: for the thesis' complex
  `H̊¹ → H̊(curl) → L²` on any nonempty bounded open `Ω ⊆ ℝ³` there are TSD data in `D(L) ∩ K`
  such that on every `[0, T]`, `T > 0`, (4.14) has a strong solution and every strong solution
  leaves `K = {0} × L²(TSD) × L²(TSD)`.

Correction: the conclusion of [QuennevilleBelair2015, §4.10, Prop 4.17] fails on every nonempty
bounded open domain, with no hypothesis: `thesisComplex_orbit_not_propagate`
(`Feec.Ch4.BoundedDomain`) assumed a Stone group, which `HilbertComplex2.waveGroup` supplies.

Correction: the forcing class `ForcingThm43` is `C([0,T]; D(A))` together with the continuous
`F` that are differentiable off a countable set with integrable derivative. The thesis' class in
Thm 4.3 is `C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(A)))`. Not covered: `W^{1,1}` forcing
that is only differentiable almost everywhere, and `L¹(0,T; D(A))` forcing that is not
continuous into `D(A)`.

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

/-- Classical solutions of `U' = A U + F` for every skew-adjoint `A` and `W^{1,1}`-type forcing
(`ForcingW11`, Duhamel's formula with integration by parts; `Feec.Ch4.StoneDuhamel`).
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, §4.2, Cor 4.2.5]. -/
theorem IsSkewAdjoint.wellPosedClassical_W11 (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedClassical A T (ForcingW11 T) :=
  (stoneGroup hA).wellPosedClassical_W11 T

/-- Classical solutions for the combined forcing class
`ForcingThm43 = C([0,T]; D(A)) ∪ ForcingW11`, for every skew-adjoint `A`.
See [QuennevilleBelair2015, Thm 4.3]. -/
theorem IsSkewAdjoint.wellPosedClassical_thm43 (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedClassical A T (ForcingThm43 A T) :=
  (stoneGroup hA).wellPosedClassical_thm43 T

/-- `WellPosedExistence A T (ForcingThm43 A T)` for every skew-adjoint `A`.
See [QuennevilleBelair2015, Thm 4.3]. -/
theorem IsSkewAdjoint.wellPosedExistence_thm43 (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedExistence A T (ForcingThm43 A T) :=
  (hA.wellPosedClassical_thm43 T).wellPosedExistence

/-- **Thesis Thm 4.3** for skew-adjoint `A` and forcing in `ForcingThm43 A T`
(`C([0,T]; D(A))`, or continuous with integrable derivative off a countable set): there is a
classical solution `U ∈ C⁰([0,T]; D(A)) ∩ C¹([0,T]; X)` of `U' = A U + F`, `U(0) = U₀`, unique
among strong solutions.

Correction: the thesis' class is `C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(A)))`.
`ForcingThm43` covers `C([0,T]; D(A))` and the `W^{1,1}` functions that are differentiable off a
countable set (including `C¹([0,T]; X)`), but not general `L¹(0,T; D(A))` forcing.
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, §4.2], [CazenaveHaraux1998, Prop 4.1.6]. -/
theorem thm_4_3_unconditional (hA : IsSkewAdjoint A) (T : ℝ) {U₀ : E} (hU₀ : U₀ ∈ A.domain)
    {F : ℝ → E} (hF : ForcingThm43 A T F) :
    ∃ U, IsClassicalSolution A T U₀ F U ∧
      ∀ U', IsStrongSolution A T U₀ F U' → EqOn U' U (Icc 0 T) := by
  obtain ⟨U, hU⟩ := hA.wellPosedClassical_thm43 T U₀ hU₀ F hF
  exact ⟨U, hU, fun U' hU' => strongSolution_unique A (hA.isSkewSymm hA.dense_domain) hU'
    hU.toIsStrongSolution⟩

/-- **Thesis Cor 4.5** (strong-solution form), unconditional, forcing in `ForcingThm43`: under
the hypotheses of Thm 4.4, the restricted problem in `K` has a unique strong solution, which
coincides with the solution in `X`. `Feec.cor_4_5` with its `WellPosedExistence` hypothesis
discharged. See [QuennevilleBelair2015, Thm 4.4, Cor 4.5]. -/
theorem cor_4_5_unconditional (L : E →ₗ.[ℝ] E) (hL : IsSkewAdjoint L)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] [CompleteSpace K]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    (T : ℝ) (U₀ : K) (hU₀ : (U₀ : E) ∈ L.domain) (F : ℝ → K)
    (hF : ForcingThm43 L T fun t => (F t : E)) :
    IsSkewAdjoint (Feec.restrictTo L K h3) ∧
    ∃ Ut : ℝ → K, IsStrongSolution (Feec.restrictTo L K h3) T U₀ F Ut ∧
      (∀ V, IsStrongSolution (Feec.restrictTo L K h3) T U₀ F V → EqOn V Ut (Icc 0 T)) ∧
      ∀ U, IsStrongSolution L T U₀ (fun t => F t) U → ∀ t ∈ Icc 0 T, (Ut t : E) = U t :=
  cor_4_5 L hL.dense_domain hL K h1 h3 (hL.wellPosedExistence_thm43 T) U₀ hU₀ F hF

/-- **Thesis Cor 4.5** (classical form), unconditional, forcing in `ForcingThm43`.
See [QuennevilleBelair2015, Thm 4.4, Cor 4.5]. -/
theorem cor_4_5_classical_unconditional (L : E →ₗ.[ℝ] E) (hL : IsSkewAdjoint L)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] [CompleteSpace K]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    (T : ℝ) (U₀ : K) (hU₀ : (U₀ : E) ∈ L.domain) (F : ℝ → K)
    (hF : ForcingThm43 L T fun t => (F t : E)) :
    IsSkewAdjoint (Feec.restrictTo L K h3) ∧
    ∃ Ut : ℝ → K, IsClassicalSolution (Feec.restrictTo L K h3) T U₀ F Ut ∧
      (∀ V, IsStrongSolution (Feec.restrictTo L K h3) T U₀ F V → EqOn V Ut (Icc 0 T)) ∧
      ∀ U, IsStrongSolution L T U₀ (fun t => F t) U → ∀ t ∈ Icc 0 T, (Ut t : E) = U t :=
  cor_4_5_classical L hL.dense_domain hL K h1 h3 (hL.wellPosedClassical_thm43 T) U₀ hU₀ F hF

/-- **Thesis Cor 4.5, ambient form**, unconditional: for data in `D(L) ∩ K` and forcing in
`ForcingThm43` with values in `K`, the unique strong solution in `X` stays in `K`.
`Feec.cor_4_5_ambient` with its `WellPosedExistence` hypothesis discharged.
See [QuennevilleBelair2015, Thm 4.4, Cor 4.5]. -/
theorem cor_4_5_ambient_unconditional (L : E →ₗ.[ℝ] E) (hL : IsSkewAdjoint L)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    {T : ℝ} {U₀ : E} (hU₀ : U₀ ∈ L.domain ⊓ K) {F : ℝ → E} (hF : ForcingThm43 L T F)
    (hFK : ∀ t ∈ Icc 0 T, F t ∈ K) :
    ∃ U, IsStrongSolution L T U₀ F U ∧ (∀ t ∈ Icc 0 T, U t ∈ K) ∧
      ∀ U', IsStrongSolution L T U₀ F U' → EqOn U U' (Icc 0 T) :=
  cor_4_5_ambient L hL.dense_domain hL K h1 h3 (hL.wellPosedExistence_thm43 T) hU₀ hF hFK

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

/-- **Thesis Thm 4.7**, unconditional: for every Hilbert complex and data in `D(L)`, strong and
weak solutions of the Hodge wave equation coincide. `thm_4_7` with its `WellPosedHom` hypothesis
discharged. See [QuennevilleBelair2015, Thm 4.7]. -/
theorem thm_4_7_unconditional (T : ℝ) {ξ₀ : Tot W0 W1 W2} (h0 : ξ₀ ∈ H.waveOp.domain)
    (ξ : ℝ → Tot W0 W1 W2) :
    IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ ↔ H.IsWeakSolution T ξ₀ ξ :=
  H.thm_4_7 (H.neg_waveOp_isSkewAdjoint.wellPosedHom T) h0 ξ

/-- **Thesis Thm 4.7** with the thesis' regularity classes, unconditional: classical strong
solutions (`C⁰(D(L)) ∩ C¹(W)`) and classical weak solutions (`C⁰(V) ∩ C¹(W)`) coincide.
See [QuennevilleBelair2015, Thm 4.7]. -/
theorem thm_4_7_classical_unconditional (T : ℝ) {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) (ξ : ℝ → Tot W0 W1 W2) :
    IsClassicalSolution (-H.waveOp) T ξ₀ 0 ξ ↔ H.IsClassicalWeakSolution T ξ₀ ξ :=
  H.thm_4_7_classical (H.neg_waveOp_isSkewAdjoint.wellPosedClassical T) rfl h0 ξ

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

/-- **Prop 4.16 with existence**, unconditional: for every Hilbert complex and every closed
`Y ⊇ range d1`, data in `D(L) ∩ K` have a unique strong solution of the Hodge wave equation, and
it stays in `K = {0} × ker d0* × Y`. `prop_4_16_exists` with its `WellPosedHom` hypothesis
discharged. See [QuennevilleBelair2015, Prop 4.16]. -/
theorem prop_4_16_exists_unconditional (Y : Submodule ℝ W2) [Y.HasOrthogonalProjection]
    (hY : LinearMap.range H.d1.toFun ≤ Y) (T : ℝ) {U₀ : Tot W0 W1 W2} (hD : U₀ ∈ H.domL)
    (hU₀ : U₀ ∈ K H Y) :
    ∃ U, IsStrongSolution (-H.waveOp) T U₀ 0 U ∧ (∀ t ∈ Icc 0 T, U t ∈ K H Y) ∧
      ∀ U', IsStrongSolution (-H.waveOp) T U₀ 0 U' → EqOn U U' (Icc 0 T) :=
  prop_4_16_exists hY (H.neg_waveOp_isSkewAdjoint.wellPosedHom T) hD hU₀

/-- **Prop 4.18**, unconditional: for `E₀ ∈ V1 ∩ ker d0*`, `B₀ ∈ V2*`, the reduced system
(4.15) has a unique strong solution, `E` stays in `ker d0*`, and `(0, E, B)` solves (4.14).
`prop_4_18` with its `WellPosedHom` hypothesis discharged.
See [QuennevilleBelair2015, Prop 4.18]. -/
theorem prop_4_18_unconditional (T : ℝ) {E₀ : W1} {B₀ : W2}
    (hE₀ : E₀ ∈ H.d1.domain) (hE₀k : E₀ ∈ H.d0†.ker) (hB₀ : B₀ ∈ H.d1†.domain) :
    ∃ E B, IsReducedSolution H T E₀ B₀ E B ∧ (∀ t ∈ Icc 0 T, E t ∈ H.d0†.ker) ∧
      IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0
        (fun t => (tot W0 W1 W2).symm (0, E t, B t)) ∧
      ∀ E' B', IsReducedSolution H T E₀ B₀ E' B' → EqOn E E' (Icc 0 T) ∧ EqOn B B' (Icc 0 T) :=
  prop_4_18 (H.neg_waveOp_isSkewAdjoint.wellPosedHom T) hE₀ hE₀k hB₀

end Constraints

namespace BoundedDomain

open HilbertComplex2 Constraints

variable {Ω : Set R3}

variable {W0 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0] in
/-- **Prop 4.17's conclusion fails on bounded domains**, for every Hilbert complex
`W0 → L²(Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)` whose `d1` is contained in the closed curl: some TSD datum
`(0, 0, β) ∈ D(L) ∩ K` has, on every `[0, T]` with `T > 0`, a strong solution of (4.14), and
every strong solution with this datum leaves `K = {0} × L²(TSD) × L²(TSD)`.

Correction: [QuennevilleBelair2015, §4.10, Prop 4.17]. `exists_orbit_not_propagate` with its
Stone-group hypothesis discharged by `HilbertComplex2.waveGroup`; the "every solution" half is
uniqueness of strong solutions (`strongSolution_unique`). -/
theorem exists_orbit_not_propagate_unconditional (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
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
  have skew := H.neg_waveOp_isSkewAdjoint.isSkewSymm H.neg_waveOp_isSkewAdjoint.dense_domain
  refine ⟨B₀, hB, hD, hK, fun T hT => ?_⟩
  obtain ⟨hS, t, ht, hn⟩ := hall T hT
  refine ⟨⟨_, hS⟩, fun U hU => ⟨t, ht, ?_⟩⟩
  rw [strongSolution_unique _ skew hU hS ht]
  exact hn

/-- **The conclusion of Prop 4.17 fails for the thesis' complex** `H̊¹ → H̊(curl) → L²` on
every nonempty bounded open `Ω ⊆ ℝ³`, unconditionally: there is TSD data `(0, 0, β) ∈ D(L) ∩ K`
such that, for every `T > 0`, (4.14) has a strong solution on `[0, T]` (Stone's theorem) and
every strong solution leaves `K = {0} × L²(TSD) × L²(TSD)` somewhere in `[0, T]`.

Correction: [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem thesisComplex_orbit_not_propagate_unconditional (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ∃ B₀ : L2M Ω, B₀ ∈ TSD Ω ∧ ini (L2V Ω) 0 B₀ ∈ (thesisComplex hΩ hb).domL ∧
      ini (L2V Ω) 0 B₀ ∈ Kc (L2V Ω) (TSD Ω) (TSD Ω) ∧
      ∀ T > 0, (∃ U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω),
          IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) 0 B₀) 0 U) ∧
        ∀ U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω),
          IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) 0 B₀) 0 U →
            ∃ t ∈ Icc 0 T, U t ∉ Kc (L2V Ω) (TSD Ω) (TSD Ω) :=
  exists_orbit_not_propagate_unconditional hΩ hb hne _ (mem_closure_curlClosure hΩ hb)

end BoundedDomain

end Feec
