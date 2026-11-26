module

public import Feec.Evolution.WellPosed
public import Feec.ForMathlib.LinearPMap.Bounded
public import Feec.HilbertComplex.HodgeWave
public import Feec.HilbertComplex.Reducing
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Non-vacuity witnesses

Concrete operators and complexes over `𝕜 = ℝ` or `ℂ` that satisfy the standing hypotheses of the
existence, constraint-propagation and Hodge wave theorems.

## Main results

* `bounded_standing_hypotheses`: a bounded skew-symmetric `B` generates unique classical solutions
  for continuous forcing.
* `ker_standing_hypotheses`: for bounded `A`, `B` with `A` skew and `AB = BA`, `ker B` reduces
  `A` and is kept.
* `rotGen_standing_hypotheses`: the rotation generator on `𝕜²`, a nonzero witness.
* `idComplex_nonvacuous`: `𝕜 --id--> 𝕜 → 0` has a nonzero, well-posed Hodge wave operator.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.3, §4.4

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace LinearPMap
open Set

@[expose] public noncomputable section

namespace Feec.Examples

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Bounded skew generators -/

section Bounded

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem contDomain_toPMap_top (B : E →L[𝕜] E) {a b : ℝ} {F : ℝ → E}
    (hF : ContinuousOn F (Icc a b)) :
    Evolution.ForcingClass.contDomain ((B : E →ₗ[𝕜] E).toPMap ⊤) a b F :=
  ⟨fun _ _ => Submodule.mem_top, hF, fun t => B (F t), B.continuous.comp_continuousOn hF,
    fun _ _ => rfl⟩

variable [CompleteSpace E]

theorem isSkewAdjoint_toPMap_top {B : E →L[𝕜] E} (hB : ∀ x y, ⟪B x, y⟫_𝕜 = -⟪x, B y⟫_𝕜) :
    ((B : E →ₗ[𝕜] E).toPMap ⊤).IsSkewAdjoint :=
  (ContinuousLinearMap.isSkewAdjoint_toPMap_top_iff B).2
    ((ContinuousLinearMap.adjoint_eq_neg_iff B).2 hB)

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **The standing hypotheses of Thm 4.3 are satisfiable**: a bounded skew-symmetric `B` is
skew-adjoint, with classical solutions for continuous forcing, unique among strong ones.
[QuennevilleBelair2015], Thm 4.3 -/
theorem bounded_standing_hypotheses (B : E →L[𝕜] E) (hB : ∀ x y, ⟪B x, y⟫_𝕜 = -⟪x, B y⟫_𝕜) :
    Dense (((B : E →ₗ[𝕜] E).toPMap ⊤).domain : Set E) ∧
      ((B : E →ₗ[𝕜] E).toPMap ⊤).IsSkewAdjoint ∧
      ∀ (U₀ : E) (a b : ℝ) (F : ℝ → E), ContinuousOn F (Icc a b) →
        ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution ((B : E →ₗ[𝕜] E).toPMap ⊤) (Icc a b) F U ∧
          ∀ V, V a = U₀ → Evolution.IsStrongSolution ((B : E →ₗ[𝕜] E).toPMap ⊤) (Icc a b) F V →
            EqOn V U (Icc a b) := by
  refine ⟨by simp [dense_univ], isSkewAdjoint_toPMap_top hB, fun U₀ a b F hF => ?_⟩
  exact (isSkewAdjoint_toPMap_top hB).existsUnique_classicalSolution Submodule.mem_top
    (contDomain_toPMap_top B hF).admissible

/-- **The hypotheses of Cor 4.5 are satisfiable**: for bounded `A` skew and `B` commuting with `A`,
`ker B` reduces `A` and is kept by the solutions. [QuennevilleBelair2015], Cor 4.5 -/
theorem ker_standing_hypotheses (A B : E →L[𝕜] E) (hA : ∀ x y, ⟪A x, y⟫_𝕜 = -⟪x, A y⟫_𝕜)
    (hAB : A.comp B = B.comp A) :
    ∃ _ : (LinearMap.ker (B : E →ₗ[𝕜] E)).HasOrthogonalProjection,
      ((A : E →ₗ[𝕜] E).toPMap ⊤).IsReducing (LinearMap.ker (B : E →ₗ[𝕜] E)) ∧
      ∀ U₀ ∈ LinearMap.ker (B : E →ₗ[𝕜] E), ∀ (a b : ℝ) (F : ℝ → E), ContinuousOn F (Icc a b) →
        (∀ t ∈ Icc a b, F t ∈ LinearMap.ker (B : E →ₗ[𝕜] E)) →
        ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution ((A : E →ₗ[𝕜] E).toPMap ⊤) (Icc a b) F U ∧
          ∀ t ∈ Icc a b, U t ∈ LinearMap.ker (B : E →ₗ[𝕜] E) := by
  have : CompleteSpace (LinearMap.ker (B : E →ₗ[𝕜] E)) := B.isClosed_ker.completeSpace_coe
  have hK : ((A : E →ₗ[𝕜] E).toPMap ⊤).IsReducing (LinearMap.ker (B : E →ₗ[𝕜] E)) := by
    refine (isSkewAdjoint_toPMap_top hA).isReducing (fun _ => trivial) fun x hx => ?_
    rw [LinearMap.mem_ker] at hx ⊢
    have := congrArg (fun C : E →L[𝕜] E => C (x : E)) hAB
    simp only [ContinuousLinearMap.comp_apply] at this
    change B (A (x : E)) = 0
    rw [← this, show B (x : E) = 0 from hx, _root_.map_zero]
  refine ⟨inferInstance, hK, fun U₀ hU₀ a b F hF hFK => ?_⟩
  obtain ⟨U, h0, hU, -⟩ := (bounded_standing_hypotheses A hA).2.2 U₀ a b F hF
  exact ⟨U, h0, hU, hU.toIsStrongSolution.mem_of_isReducing
    (isSkewAdjoint_toPMap_top hA).isDissipative hK (h0 ▸ hU₀) hFK⟩

end Bounded

/-! ### The rotation generator on `𝕜²` -/

variable (𝕜) in
/-- The rotation generator `J (x₀, x₁) = (-x₁, x₀)` on `EuclideanSpace 𝕜 (Fin 2)`. -/
def rotGen : EuclideanSpace 𝕜 (Fin 2) →L[𝕜] EuclideanSpace 𝕜 (Fin 2) :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : 𝕜)) -
    (EuclideanSpace.proj (1 : Fin 2)).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : 𝕜))

theorem rotGen_apply (x : EuclideanSpace 𝕜 (Fin 2)) :
    rotGen 𝕜 x = x 0 • EuclideanSpace.single (1 : Fin 2) (1 : 𝕜) -
      x 1 • EuclideanSpace.single (0 : Fin 2) (1 : 𝕜) := by
  simp [rotGen]

theorem rotGen_skew (x y : EuclideanSpace 𝕜 (Fin 2)) :
    ⟪rotGen 𝕜 x, y⟫_𝕜 = -⟪x, rotGen 𝕜 y⟫_𝕜 := by
  simp only [rotGen_apply, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  simp
  ring

theorem rotGen_ne_zero : rotGen 𝕜 ≠ 0 := by
  intro h
  have := congrArg (fun f : EuclideanSpace 𝕜 (Fin 2) →L[𝕜] EuclideanSpace 𝕜 (Fin 2) =>
    f (EuclideanSpace.single 0 1) 1) h
  simp [rotGen_apply] at this

/-- **A concrete nonzero witness** for the standing hypotheses of Thm 4.3: the rotation
generator `J ≠ 0` on `𝕜²`. [QuennevilleBelair2015], Thm 4.3 -/
theorem rotGen_standing_hypotheses :
    rotGen 𝕜 ≠ 0 ∧ ((rotGen 𝕜 : EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] _).toPMap ⊤).IsSkewAdjoint ∧
      ∀ (U₀ : EuclideanSpace 𝕜 (Fin 2)) (a b : ℝ) (F : ℝ → EuclideanSpace 𝕜 (Fin 2)),
        ContinuousOn F (Icc a b) → ∃ U, U a = U₀ ∧
          Evolution.IsClassicalSolution ((rotGen 𝕜 : _ →ₗ[𝕜] _).toPMap ⊤) (Icc a b) F U :=
  ⟨rotGen_ne_zero, isSkewAdjoint_toPMap_top rotGen_skew, fun U₀ a b F hF => by
    obtain ⟨U, h0, hU, -⟩ := (bounded_standing_hypotheses (rotGen 𝕜) rotGen_skew).2.2 U₀ a b F hF
    exact ⟨U, h0, hU⟩⟩

/-! ### A Hodge wave equation with nonzero wave operator -/

variable (𝕜) in
/-- The short complex `𝕜 --id--> 𝕜 → 0`. -/
def idComplex : ShortHilbertComplex 𝕜 𝕜 𝕜 PUnit :=
  ShortHilbertComplex.ofOp ((LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤) (by simp [dense_univ])
    (ContinuousLinearMap.id 𝕜 𝕜).isClosed_toPMap_top

/-- The datum `(1, 0, 0)`. -/
def idDatum : PiLp 2 (ShortHilbertComplex.W3 𝕜 𝕜 PUnit) :=
  WithLp.toLp 2 fun i => match i with
    | 0 => (1 : 𝕜)
    | 1 => (0 : 𝕜)
    | 2 => PUnit.unit

theorem idDatum_mem : (idDatum : PiLp 2 (ShortHilbertComplex.W3 𝕜 𝕜 PUnit)) ∈
    (idComplex 𝕜).wave.domain := by
  rw [ShortHilbertComplex.mem_wave_domain]
  refine ⟨trivial, trivial, ?_, ?_⟩
  · change (0 : 𝕜) ∈ ((LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤)†.domain
    exact Submodule.zero_mem _
  · rw [show (idComplex 𝕜).d₁ = 0 from rfl, LinearPMap.adjoint_zero]
    trivial

/-- **The hypotheses of Thms 4.6/4.7 hold with a nonzero Hodge wave operator** on `𝕜 --id--> 𝕜 → 0`,
with classical solutions of the homogeneous equation unique among weak ones.
[QuennevilleBelair2015], Thm 4.6, Thm 4.7 -/
theorem idComplex_nonvacuous :
    (∃ x : (idComplex 𝕜).wave.domain, (idComplex 𝕜).wave x ≠ 0) ∧
      ∀ U₀ ∈ (idComplex 𝕜).wave.domain, ∀ a b : ℝ,
        ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (idComplex 𝕜).wave (Icc a b) 0 U ∧
          (∀ V, V a = U₀ → HilbertComplex.HodgeWave.IsWeakSolution (idComplex 𝕜).toHilbertComplex
            (Icc a b) 0 V → EqOn V U (Icc a b)) := by
  refine ⟨⟨⟨idDatum, idDatum_mem⟩, fun h => ?_⟩, fun U₀ hU₀ a b => ?_⟩
  · have := congrArg (fun x : PiLp 2 (ShortHilbertComplex.W3 𝕜 𝕜 PUnit) => (x 1 : 𝕜)) h
    rw [ShortHilbertComplex.wave_apply_one] at this
    have e2 : (idComplex 𝕜).d₁† ⟨(idDatum : PiLp 2 (ShortHilbertComplex.W3 𝕜 𝕜 PUnit)) 2,
        idDatum_mem.2 2 1⟩ = 0 :=
      LinearPMap.adjoint_apply_eq_zero_of_eq_zero rfl _
    rw [e2, sub_zero] at this
    exact one_ne_zero (α := 𝕜) this
  · obtain ⟨U, h0, hU, -, hW, -⟩ :=
      HilbertComplex.HodgeWave.existsUnique_hom (idComplex 𝕜).toHilbertComplex hU₀ a b
    exact ⟨U, h0, hU, hW⟩

end Feec.Examples
