module

public import Feec.Instances.Corollaries
public import Feec.HilbertComplex.Approximation.ApproxComplexCrimeWitness
public import Feec.HilbertComplex.Approximation.StaticCochainWitness
public import Feec.Counterexamples.Fredholm
public import Feec.Examples.NonVacuity
public import Feec.Domain.BGGKoszul
public import Feec.Models.Cube.FiniteDifferenceHeat
public import Feec.Models.Cube.MaxNormHeat
public import Feec.Models.Cube.MaxNormNeumann

/-!
# Non-vacuity of the crown

The FEEC theorem with rates holds on the Whitney forms of the cube of dimension `n ≥ 2`, with
nonzero data exercising its clauses; this file collects it with the non-vacuity witnesses of the
layers of the crown.

## Main results

* `cube_nonvacuous`: the crown on the cube, not vacuously.
* `crownNonVacuity`: the crown is not vacuous.
-/

open scoped InnerProductSpace
open Filter Topology Metric Set

@[expose] public noncomputable section

namespace Feec.Instances

open HilbertComplex Models.Cube FEM
open Feec.Domain (L2F formIdx)

/-! ### The crown on the cube -/

variable {n : ℕ}

theorem cube_exists_d_ne_zero (hn : 2 ≤ n) :
    ∃ σ : (((complex n).window 1 3).d 0 1).domain, ((complex n).window 1 3).d 0 1 σ ≠ 0 := by
  set W := (complex n).window 1 3
  have hrel : (ComplexShape.window 3).Rel 0 1 := rfl
  have hcyc : W.cycles 0 ≠ ⊤ :=
    (W.cycles_eq hrel).symm ▸ ((complex n).cycles_eq (show (ComplexShape.up ℤ).Rel (1 : ℤ) (1 + 1)
      from rfl)) ▸ Feec.Domain.maximalComplex_cycles_one_ne_top (isOpen_cubeDomain n)
        (isBounded_cubeDomain n) ⟨center n, center_mem_cubeDomain n⟩ hn
  obtain ⟨u, hu, hu0⟩ := W.exists_mem_orthogonal_cycles_inf_domain hrel hcyc
  refine ⟨⟨u, hu.2⟩, fun h => hu0 ?_⟩
  have hz : u ∈ W.cycles 0 := (W.cycles_eq hrel) ▸ LinearPMap.mem_ker_iff.2 ⟨_, rfl, h⟩
  exact inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hz hu.1)

variable (n) in
/-- The vanishing-field constraint `E = 0`, `B = 0` on the window `HΛ¹(Q) → HΛ²(Q) → HΛ³(Q)`. -/
abbrev cubePotential :
    Submodule ℝ (PiLp 2 fun i : Fin 3 => L2F ℝ (cubeDomain n) (formIdx n (1 + i))) :=
  Maxwell.potential ℝ _

theorem cube_not_isReducing_potential (hn : 2 ≤ n) :
    ¬ ((complex n).window 1 3).wave.IsReducing (cubePotential n) :=
  Maxwell.not_isReducing_potential _ (cube_exists_d_ne_zero hn)

variable [NeZero n]

/-- **The crown on the cube, not vacuously** (`n ≥ 2`): the rated FEEC verdict of the Whitney forms,
with closed ranges, `ℌ⁰ ≠ 0`, a constraint left by some datum, and a nonzero heat datum. -/
theorem cube_nonvacuous (hn : 2 ≤ n) :
    ConformingFamily.Verdict.Rated (whitneyFamily n) (whitneyJackson n) ∧
      (∀ j, (complex n).ClosedRangeAt j) ∧ (complex n).harmonic 0 ≠ ⊥ ∧
      ¬ ((complex n).window 1 3).wave.IsReducing (cubePotential n) ∧
      (∀ T : ℝ, 0 < T → ∃ x : ((complex n).window 1 3).wave.domain,
        (x : PiLp 2 _) ∈ cubePotential n ∧
          ∃ t ∈ Icc (-T) T, ((complex n).window 1 3).waveGroup.S t x ∉ cubePotential n) ∧
      ∃ x ∈ (((whitneyFamily n).windowFEEC 0 (n + 1) ⊤
        (by rw [Submodule.top_coe]; exact isClosed_univ)).heatCore
          (closedRangeAt_heatWindow n) ((whitneyFamily n).isGraphBounded_windowFEEC _ _ _ _)).Data,
        x ≠ 0 := by
  have hV := (whitneyFamily n).feec_rated (whitneyJackson n)
  refine ⟨hV, closedRangeAt, ?_, cube_not_isReducing_potential hn, fun T hT => ?_,
    exists_mem_heatCore_data_ne_zero n _ _⟩
  · rw [harmonic_zero_eq_span, Ne, Submodule.span_singleton_eq_bot]
    exact oneForm_ne_zero
  · obtain ⟨x, hxK, t, ht, hout, -⟩ := (hV.constrained 1 3 _ Maxwell.isClosed_potential).leaves_symm
      (cube_not_isReducing_potential hn) (Maxwell.dense_potential _) hT
    exact ⟨x, hxK, t, ht, hout⟩

/-! ### The non-vacuity of the crown -/

universe u

/-- **The non-vacuity of the crown**: the statements of the non-vacuity witnesses. -/
structure CrownNonVacuity : Prop where
  /-- the crown on the cube, with nonzero data -/
  cube : type_of% @cube_nonvacuous
  /-- the fully discrete heat clause on the cube -/
  full : type_of% @Corollaries.Cube.FEM.heat_crankNicolson
  /-- a non-reducing wave clause on `𝕋ᵈ` -/
  torus : type_of% @Maxwell.torus_potential_approxFEEC.{u}
  /-- the compactness property on `ℓ²` -/
  compact : type_of% @Counterexamples.hasCompactProperty_infiniteDimensional.{u}
  /-- inner-product and differential crimes -/
  perturbed : type_of% @ApproxFEEC.perturbed_nonvacuous.{u}
  /-- a non-scalar reading map -/
  projPerturbed : type_of% @ApproxFEEC.projPerturbed_nonvacuous.{u}
  /-- a non-conforming discrete complex -/
  scaled : type_of% @ApproxComplex.scaled_nonvacuous.{u}
  /-- a reading map that is not a cochain map -/
  shifted : type_of% @ApproxComplexCrime.shifted_nonvacuous.{u}
  /-- both crimes -/
  mixed : type_of% @ApproxComplexCrime.mixed_nonvacuous.{u}
  /-- a Hodge wave equation with `L ≠ 0` -/
  idComplex : type_of% @Examples.idComplex_nonvacuous.{u}
  /-- a nonzero bounded skew generator -/
  rotGen : type_of% @Examples.rotGen_standing_hypotheses.{u}
  /-- the explicit BGG cochain map on smooth fields -/
  bgg : type_of% @Domain.smoothBGGVerdict.{u}
  /-- the lumped-mass `P₁` heat equation in the maximum norm -/
  maxNorm : type_of% @Models.Cube.MaxNormHeat.maxNormHeat_nonvacuous
  /-- the same with natural boundary conditions -/
  neumann : type_of% @Models.Cube.MaxNormNeumann.maxNormNeumann_nonvacuous
  /-- the finite difference heat scheme in the maximum norm -/
  finiteDifference : type_of% @Models.Cube.FiniteDifferenceHeat.finiteDifferenceHeat_nonvacuous
  /-- the static theory with crimes in the cochain case -/
  shear : type_of% @ApproxComplexCrime.shear_nonvacuous.{u}

/-- **The crown is not vacuous.** -/
theorem crownNonVacuity : CrownNonVacuity.{u} :=
  ⟨@cube_nonvacuous, @Corollaries.Cube.FEM.heat_crankNicolson,
    @Maxwell.torus_potential_approxFEEC, Counterexamples.hasCompactProperty_infiniteDimensional,
    ApproxFEEC.perturbed_nonvacuous, ApproxFEEC.projPerturbed_nonvacuous,
    ApproxComplex.scaled_nonvacuous, ApproxComplexCrime.shifted_nonvacuous,
    ApproxComplexCrime.mixed_nonvacuous, Examples.idComplex_nonvacuous,
    Examples.rotGen_standing_hypotheses, Domain.smoothBGGVerdict,
    @Models.Cube.MaxNormHeat.maxNormHeat_nonvacuous,
    @Models.Cube.MaxNormNeumann.maxNormNeumann_nonvacuous,
    @Models.Cube.FiniteDifferenceHeat.finiteDifferenceHeat_nonvacuous,
    ApproxComplexCrime.shear_nonvacuous⟩

end Feec.Instances
