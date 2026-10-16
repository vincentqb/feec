module

public import Feec.Ch4.Stone
public import Feec.Ch4.StoneForcing
public import Feec.Ch4.TorusGroup
public import Feec.Ch4.BoundedDomain

/-!
# Consequences of Stone's theorem: the existence hypotheses of Ch. 4 discharged

`Feec.stoneGroup` (`Feec.Ch4.Stone`) constructs the orthogonal group of every skew-adjoint
operator. The Ch. 4 results that take existence as a hypothesis (`WellPosedHom`,
`WellPosedExistence`, `WellPosedClassical`, or a `UnitaryGroupGenerator`) therefore hold for
every skew-adjoint operator. Each fact is stated once, for the largest forcing class
(`ForcingClass.admissible`, the thesis' class `C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(A)))`)
and the thesis' regularity; the statements for smaller classes or weaker regularity are kept as
corollaries under their former names.

## Main results

* Thm 4.3: `IsSkewAdjoint.existsUnique_classicalSolution` (`Feec.Ch4.StoneForcing`), and
  `IsSkewAdjoint.wellPosedClassical_of_le`; corollaries `IsSkewAdjoint.wellPosedClassical_forcing`,
  `IsSkewAdjoint.wellPosedExistence`, `IsSkewAdjoint.wellPosedClassical_W11`,
  `IsSkewAdjoint.wellPosedClassical_thm43`, `IsSkewAdjoint.wellPosedExistence_thm43`,
  `thm_4_3_of_isSkewAdjoint`, `thm_4_3_unconditional`.
* Cor 4.5: `IsSkewAdjoint.existsUnique_classicalSolution_restrictTo` (restricted form) and
  `IsSkewAdjoint.existsUnique_classicalSolution_mem` (ambient form, by
  `IsStrongSolution.mem_of_invariant`); corollaries `cor_4_5_of_isSkewAdjoint`,
  `cor_4_5_unconditional`, `cor_4_5_classical_unconditional`, `cor_4_5_ambient_unconditional`.
* Hodge wave equation of any Hilbert complex: `HilbertComplex2.waveGroup`,
  `HilbertComplex2.existsUnique_classicalSolution_neg_waveOp` (Thm 4.6),
  `HilbertComplex2.thm_4_3_hodgeWave` (inhomogeneous),
  `HilbertComplex2.isClassicalSolution_of_isWeakSolution`,
  `HilbertComplex2.isStrongSolution_iff_isWeakSolution` and
  `HilbertComplex2.isClassicalSolution_iff_isClassicalWeakSolution` (Thm 4.7).
* Props 4.16/4.18: `Constraints.existsUnique_classicalSolution_mem_K`,
  `Constraints.existsUnique_reducedSolution`.
* Props 4.17/4.19, abstract: `Constraints.projKc_mem_domL_of_propagates`,
  `Constraints.propagates_iff_projKc_mem_domL` (constraint propagation iff `P_K D(L) ⊆ D(L)`,
  given `D(L) ∩ K` dense in `K`; no group hypothesis).
* Bounded domains: `BoundedDomain.exists_tsd_not_propagates` and
  `BoundedDomain.thesisComplex_tsd_not_propagates`: for the thesis' complex
  `H̊¹ → H̊(curl) → L²` on any nonempty bounded open `Ω ⊆ ℝ³` there are TSD data in `D(L) ∩ K`
  such that on every `[0, T]`, `T > 0`, (4.14) has a strong solution and every strong solution
  leaves `K = {0} × L²(TSD) × L²(TSD)`.

Correction: the conclusion of [QuennevilleBelair2015, §4.10, Prop 4.17] fails on every nonempty
bounded open domain, with no hypothesis: `thesisComplex_orbit_not_propagate`
(`Feec.Ch4.BoundedDomain`) assumed a Stone group, which `HilbertComplex2.waveGroup` supplies.

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
`F ∈ C([0,T]; D(A))`. Corollary of `IsSkewAdjoint.wellPosedClassical_of_le`.
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, §4.2]. -/
theorem IsSkewAdjoint.wellPosedClassical_forcing (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedClassical A T (ForcingDL A T) :=
  hA.wellPosedClassical_of_le fun _ hF => ForcingClass.contDomain.admissible hF

/-- `WellPosedExistence A T (ForcingDL A T)` for every skew-adjoint `A`: the explicit
existence hypothesis of `Feec.Foundation.Evolution` is a theorem for this forcing class.
See [QuennevilleBelair2015, Thm 4.3]. -/
theorem IsSkewAdjoint.wellPosedExistence (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedExistence A T (ForcingDL A T) :=
  (hA.wellPosedClassical_forcing T).wellPosedExistence

/-- **Thesis Thm 4.3** for skew-adjoint `A` and forcing `F ∈ C([0,T]; D(A))`: a classical
solution exists and is unique among strong solutions. Corollary of
`IsSkewAdjoint.existsUnique_classicalSolution` (`C([0,T]; D(A))` is admissible).
See [QuennevilleBelair2015, Thm 4.3]. -/
theorem thm_4_3_of_isSkewAdjoint (hA : IsSkewAdjoint A) (T : ℝ) {U₀ : E} (hU₀ : U₀ ∈ A.domain)
    {F : ℝ → E} (hF : ForcingDL A T F) :
    ∃ U, IsClassicalSolution A T U₀ F U ∧
      ∀ U', IsStrongSolution A T U₀ F U' → EqOn U' U (Icc 0 T) :=
  hA.existsUnique_classicalSolution T hU₀ (ForcingClass.contDomain.admissible hF)

/-- **Thesis Cor 4.5** (restricted form, thesis' regularity) for skew-adjoint `L` and admissible
forcing: under the hypotheses of Thm 4.4 (`P_K D(L) ⊆ D(L)`, `L (D(L) ∩ K) ⊆ K`), the restriction
`L̃ = L|_{D(L) ∩ K}` is skew-adjoint on `K`, and for `U₀ ∈ D(L̃)` and `K`-valued admissible forcing
the restricted problem has a classical solution `U ∈ C⁰([0,T]; D(L̃)) ∩ C¹([0,T]; K)`, unique
among `K`-valued strong solutions, which coincides with every `X`-valued strong solution.
`cor_4_5_classical` with its existence hypothesis discharged by Stone's theorem; the smaller
forcing classes and the strong-solution form are corollaries.
See [QuennevilleBelair2015, Thm 4.4, Cor 4.5]. -/
theorem IsSkewAdjoint.existsUnique_classicalSolution_restrictTo {L : E →ₗ.[ℝ] E}
    (hL : IsSkewAdjoint L) (K : Submodule ℝ E) [K.HasOrthogonalProjection] [CompleteSpace K]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    (T : ℝ) (U₀ : K) (hU₀ : (U₀ : E) ∈ L.domain) (F : ℝ → K)
    (hF : ForcingClass.admissible L T fun t => (F t : E)) :
    IsSkewAdjoint (Feec.restrictTo L K h3) ∧
    ∃ Ut : ℝ → K, IsClassicalSolution (Feec.restrictTo L K h3) T U₀ F Ut ∧
      (∀ V, IsStrongSolution (Feec.restrictTo L K h3) T U₀ F V → EqOn V Ut (Icc 0 T)) ∧
      ∀ U, IsStrongSolution L T U₀ (fun t => F t) U → ∀ t ∈ Icc 0 T, (Ut t : E) = U t :=
  cor_4_5_classical L hL.dense_domain hL K h1 h3 (hL.wellPosedClassical_of_le fun _ h => h) U₀
    hU₀ F hF

/-- **Thesis Cor 4.5, ambient form**, for skew-adjoint `L` and admissible forcing: if
`P_K D(L) ⊆ D(L)` and `L (D(L) ∩ K) ⊆ K`, then for data in `D(L) ∩ K` and `K`-valued admissible
forcing, the classical solution in `X` (unique among strong solutions) stays in `K`.
Existence is `IsSkewAdjoint.existsUnique_classicalSolution`, propagation is
`IsStrongSolution.mem_of_invariant`. See [QuennevilleBelair2015, Thm 4.4, Cor 4.5]. -/
theorem IsSkewAdjoint.existsUnique_classicalSolution_mem {L : E →ₗ.[ℝ] E}
    (hL : IsSkewAdjoint L) {K : Submodule ℝ E} [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    {T : ℝ} {U₀ : E} (hU₀ : U₀ ∈ L.domain ⊓ K) {F : ℝ → E} (hF : ForcingClass.admissible L T F)
    (hFK : ∀ t ∈ Icc 0 T, F t ∈ K) :
    ∃ U, IsClassicalSolution L T U₀ F U ∧ (∀ t ∈ Icc 0 T, U t ∈ K) ∧
      ∀ U', IsStrongSolution L T U₀ F U' → EqOn U' U (Icc 0 T) := by
  obtain ⟨U, hU, huniq⟩ := hL.existsUnique_classicalSolution T hU₀.1 hF
  exact ⟨U, hU, hU.toIsStrongSolution.mem_of_invariant
    (hL.isSkewSymm hL.dense_domain).isDissipative h1 h3 hU₀.2 hFK, huniq⟩

/-- **Thesis Cor 4.5**, forcing in `C([0,T]; D(L))`. Corollary of
`IsSkewAdjoint.existsUnique_classicalSolution_restrictTo`.
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
  hL.existsUnique_classicalSolution_restrictTo K h1 h3 T U₀ hU₀ F
    (ForcingClass.contDomain.admissible hF)

/-- Classical solutions of `U' = A U + F` for every skew-adjoint `A` and `W^{1,1}`-type forcing
(`ForcingW11`). Corollary of `IsSkewAdjoint.wellPosedClassical_of_le`.
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, §4.2, Cor 4.2.5]. -/
theorem IsSkewAdjoint.wellPosedClassical_W11 (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedClassical A T (ForcingW11 T) :=
  hA.wellPosedClassical_of_le fun _ hF => ForcingClass.derivOffCountable.admissible hF

/-- Classical solutions for `ForcingThm43 = C([0,T]; D(A)) ∪ ForcingW11`, for every
skew-adjoint `A`. Corollary of `IsSkewAdjoint.wellPosedClassical_of_le`.
See [QuennevilleBelair2015, Thm 4.3]. -/
theorem IsSkewAdjoint.wellPosedClassical_thm43 (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedClassical A T (ForcingThm43 A T) :=
  hA.wellPosedClassical_of_le fun _ hF => hF.admissible

/-- `WellPosedExistence A T (ForcingThm43 A T)` for every skew-adjoint `A`.
See [QuennevilleBelair2015, Thm 4.3]. -/
theorem IsSkewAdjoint.wellPosedExistence_thm43 (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedExistence A T (ForcingThm43 A T) :=
  (hA.wellPosedClassical_thm43 T).wellPosedExistence

/-- **Thesis Thm 4.3** for skew-adjoint `A` and forcing in `ForcingThm43 A T`. Corollary of
`IsSkewAdjoint.existsUnique_classicalSolution` (`ForcingThm43` is admissible).
See [QuennevilleBelair2015, Thm 4.3]. -/
theorem thm_4_3_unconditional (hA : IsSkewAdjoint A) (T : ℝ) {U₀ : E} (hU₀ : U₀ ∈ A.domain)
    {F : ℝ → E} (hF : ForcingThm43 A T F) :
    ∃ U, IsClassicalSolution A T U₀ F U ∧
      ∀ U', IsStrongSolution A T U₀ F U' → EqOn U' U (Icc 0 T) :=
  hA.existsUnique_classicalSolution T hU₀ hF.admissible

/-- **Thesis Cor 4.5** (strong-solution form), forcing in `ForcingThm43`. Corollary of
`IsSkewAdjoint.existsUnique_classicalSolution_restrictTo`.
See [QuennevilleBelair2015, Thm 4.4, Cor 4.5]. -/
theorem cor_4_5_unconditional (L : E →ₗ.[ℝ] E) (hL : IsSkewAdjoint L)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] [CompleteSpace K]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    (T : ℝ) (U₀ : K) (hU₀ : (U₀ : E) ∈ L.domain) (F : ℝ → K)
    (hF : ForcingThm43 L T fun t => (F t : E)) :
    IsSkewAdjoint (Feec.restrictTo L K h3) ∧
    ∃ Ut : ℝ → K, IsStrongSolution (Feec.restrictTo L K h3) T U₀ F Ut ∧
      (∀ V, IsStrongSolution (Feec.restrictTo L K h3) T U₀ F V → EqOn V Ut (Icc 0 T)) ∧
      ∀ U, IsStrongSolution L T U₀ (fun t => F t) U → ∀ t ∈ Icc 0 T, (Ut t : E) = U t := by
  obtain ⟨hs, Ut, hUt, h⟩ :=
    hL.existsUnique_classicalSolution_restrictTo K h1 h3 T U₀ hU₀ F hF.admissible
  exact ⟨hs, Ut, hUt.toIsStrongSolution, h⟩

/-- **Thesis Cor 4.5** (classical form), forcing in `ForcingThm43`. Corollary of
`IsSkewAdjoint.existsUnique_classicalSolution_restrictTo`.
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
  hL.existsUnique_classicalSolution_restrictTo K h1 h3 T U₀ hU₀ F hF.admissible

/-- **Thesis Cor 4.5, ambient form**, forcing in `ForcingThm43` with values in `K`: the unique
strong solution in `X` stays in `K`. Corollary of `IsSkewAdjoint.existsUnique_classicalSolution_mem`.
See [QuennevilleBelair2015, Thm 4.4, Cor 4.5]. -/
theorem cor_4_5_ambient_unconditional (L : E →ₗ.[ℝ] E) (hL : IsSkewAdjoint L)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    {T : ℝ} {U₀ : E} (hU₀ : U₀ ∈ L.domain ⊓ K) {F : ℝ → E} (hF : ForcingThm43 L T F)
    (hFK : ∀ t ∈ Icc 0 T, F t ∈ K) :
    ∃ U, IsStrongSolution L T U₀ F U ∧ (∀ t ∈ Icc 0 T, U t ∈ K) ∧
      ∀ U', IsStrongSolution L T U₀ F U' → EqOn U U' (Icc 0 T) := by
  obtain ⟨U, hU, hK, huniq⟩ := hL.existsUnique_classicalSolution_mem h1 h3 hU₀ hF.admissible hFK
  exact ⟨U, hU.toIsStrongSolution, hK, fun U' hU' => (huniq U' hU').symm⟩

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
solutions, conserving energy. The existence hypothesis of `thm_4_6_classical` is discharged by
Stone's theorem (`waveGroup`). See [QuennevilleBelair2015, Thm 4.6]. -/
theorem existsUnique_classicalSolution_neg_waveOp (T : ℝ) {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) :
    ∃ ξ, IsClassicalSolution (-H.waveOp) T ξ₀ 0 ξ ∧
      (∀ ξ', IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ' → EqOn ξ' ξ (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, ‖ξ t‖ = ‖ξ₀‖ :=
  H.thm_4_6_classical_of_unitaryGroupGenerator H.waveGroup T h0

alias thm_4_6_unconditional := existsUnique_classicalSolution_neg_waveOp

/-- The inhomogeneous Hodge wave equation `ξ' = -L ξ + F`, `F ∈ C([0,T]; D(L))`, has a unique
classical solution, for every Hilbert complex. Corollary of
`IsSkewAdjoint.existsUnique_classicalSolution` (any admissible `F` works).
See [QuennevilleBelair2015, Thm 4.3, §4.4]. -/
theorem thm_4_3_hodgeWave (T : ℝ) {ξ₀ : Tot W0 W1 W2} (h0 : ξ₀ ∈ H.waveOp.domain)
    {F : ℝ → Tot W0 W1 W2} (hF : ForcingDL (-H.waveOp) T F) :
    ∃ ξ, IsClassicalSolution (-H.waveOp) T ξ₀ F ξ ∧
      ∀ ξ', IsStrongSolution (-H.waveOp) T ξ₀ F ξ' → EqOn ξ' ξ (Icc 0 T) :=
  H.neg_waveOp_isSkewAdjoint.existsUnique_classicalSolution T h0
    (ForcingClass.contDomain.admissible hF)

/-- **Weak solutions are classical** (Thesis Thm 4.7, second bullet, with the thesis'
regularity): for every Hilbert complex, a weak solution of (4.7)/(4.8) with initial value in
`D(L)` lies in `C⁰([0,T]; D(L)) ∩ C¹([0,T]; W)` and solves (4.4). `weak_imp_classical` with its
existence hypothesis discharged by Stone's theorem. See [QuennevilleBelair2015, Thm 4.7]. -/
theorem isClassicalSolution_of_isWeakSolution {T : ℝ} {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) {ξ : ℝ → Tot W0 W1 W2} (hξ : H.IsWeakSolution T ξ₀ ξ) :
    IsClassicalSolution (-H.waveOp) T ξ₀ 0 ξ :=
  H.weak_imp_classical (H.neg_waveOp_isSkewAdjoint.wellPosedClassical T) rfl h0 hξ

/-- **Thesis Thm 4.7**: for every Hilbert complex and data in `D(L)`, strong and weak solutions
of the Hodge wave equation coincide (`isWeakSolution_of_isStrongSolution` and
`isClassicalSolution_of_isWeakSolution`). See [QuennevilleBelair2015, Thm 4.7]. -/
theorem isStrongSolution_iff_isWeakSolution (T : ℝ) {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) (ξ : ℝ → Tot W0 W1 W2) :
    IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ ↔ H.IsWeakSolution T ξ₀ ξ :=
  ⟨H.isWeakSolution_of_isStrongSolution,
    fun hξ => (H.isClassicalSolution_of_isWeakSolution h0 hξ).toIsStrongSolution⟩

@[deprecated (since := "2026-10-16")] alias thm_4_7_unconditional :=
  isStrongSolution_iff_isWeakSolution

/-- **Thesis Thm 4.7** with the thesis' regularity classes: classical strong solutions
(`C⁰(D(L)) ∩ C¹(W)`) and classical weak solutions (`C⁰(V) ∩ C¹(W)`) coincide.
See [QuennevilleBelair2015, Thm 4.7]. -/
theorem isClassicalSolution_iff_isClassicalWeakSolution (T : ℝ) {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) (ξ : ℝ → Tot W0 W1 W2) :
    IsClassicalSolution (-H.waveOp) T ξ₀ 0 ξ ↔ H.IsClassicalWeakSolution T ξ₀ ξ :=
  H.thm_4_7_classical (H.neg_waveOp_isSkewAdjoint.wellPosedClassical T) rfl h0 ξ

@[deprecated (since := "2026-10-16")] alias thm_4_7_classical_unconditional :=
  isClassicalSolution_iff_isClassicalWeakSolution

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
theorem projKc_mem_domL_of_propagates
    (hdense : ∀ k ∈ Kc W0 S1 S2, k ∈ closure ((H.domL : Set (Tot W0 W1 W2)) ∩ Kc W0 S1 S2))
    (hprop : ∀ (T : ℝ) (U₀ : Tot W0 W1 W2) (U : ℝ → Tot W0 W1 W2), U₀ ∈ Kc W0 S1 S2 →
      IsStrongSolution (-H.waveOp) T U₀ 0 U → ∀ t ∈ Icc 0 T, U t ∈ Kc W0 S1 S2) :
    ∀ x ∈ H.domL, projKc W0 S1 S2 x ∈ H.domL :=
  prop_4_17_necessary H.waveGroup hdense hprop

@[deprecated (since := "2026-10-16")] alias prop_4_17_necessary_unconditional :=
  projKc_mem_domL_of_propagates

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
  prop_4_17_iff H.waveGroup hS1 hd1 hd1s hdense

@[deprecated (since := "2026-10-16")] alias prop_4_17_iff_unconditional :=
  propagates_iff_projKc_mem_domL

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
  exact ⟨U, hU, prop_4_16 hY hU.toIsStrongSolution hU₀, huniq⟩

@[deprecated (since := "2026-10-16")] alias prop_4_16_classical_unconditional :=
  existsUnique_classicalSolution_mem_K

/-- **Prop 4.16 with existence** (strong-solution form): data in `D(L) ∩ K` have a unique strong
solution of the Hodge wave equation, and it stays in `K = {0} × ker d0* × Y`. Corollary of
`existsUnique_classicalSolution_mem_K`. See [QuennevilleBelair2015, Prop 4.16]. -/
theorem prop_4_16_exists_unconditional (Y : Submodule ℝ W2) [Y.HasOrthogonalProjection]
    (hY : LinearMap.range H.d1.toFun ≤ Y) (T : ℝ) {U₀ : Tot W0 W1 W2} (hD : U₀ ∈ H.domL)
    (hU₀ : U₀ ∈ K H Y) :
    ∃ U, IsStrongSolution (-H.waveOp) T U₀ 0 U ∧ (∀ t ∈ Icc 0 T, U t ∈ K H Y) ∧
      ∀ U', IsStrongSolution (-H.waveOp) T U₀ 0 U' → EqOn U U' (Icc 0 T) := by
  obtain ⟨U, hU, hK, huniq⟩ := existsUnique_classicalSolution_mem_K Y hY T hD hU₀
  exact ⟨U, hU.toIsStrongSolution, hK, fun U' hU' => (huniq U' hU').symm⟩

/-- **Prop 4.18**: for `E₀ ∈ V1 ∩ ker d0*`, `B₀ ∈ V2*`, the reduced system (4.15) has a unique
strong solution, `E` stays in `ker d0*`, and `(0, E, B)` solves (4.14). `prop_4_18` with its
existence hypothesis discharged by Stone's theorem. See [QuennevilleBelair2015, Prop 4.18]. -/
theorem existsUnique_reducedSolution (T : ℝ) {E₀ : W1} {B₀ : W2}
    (hE₀ : E₀ ∈ H.d1.domain) (hE₀k : E₀ ∈ H.d0†.ker) (hB₀ : B₀ ∈ H.d1†.domain) :
    ∃ E B, IsReducedSolution H T E₀ B₀ E B ∧ (∀ t ∈ Icc 0 T, E t ∈ H.d0†.ker) ∧
      IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0
        (fun t => (tot W0 W1 W2).symm (0, E t, B t)) ∧
      ∀ E' B', IsReducedSolution H T E₀ B₀ E' B' → EqOn E E' (Icc 0 T) ∧ EqOn B B' (Icc 0 T) :=
  prop_4_18 (H.neg_waveOp_isSkewAdjoint.wellPosedHom T) hE₀ hE₀k hB₀

alias prop_4_18_unconditional := existsUnique_reducedSolution

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

@[deprecated (since := "2026-10-16")] alias exists_orbit_not_propagate_unconditional :=
  exists_tsd_not_propagates

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

alias thesisComplex_orbit_not_propagate_unconditional := thesisComplex_tsd_not_propagates

end BoundedDomain

end Feec
