module

public import Feec.Instances.Corollaries
public import Feec.HilbertComplex.Approximation.ApproxComplexCrimeWitness
public import Feec.Counterexamples.Fredholm
public import Feec.Examples.NonVacuity
public import Feec.Domain.BGGKoszul
public import Feec.Models.Cube.MaxNormHeat
public import Feec.Models.Cube.MaxNormNeumann

/-!
# Non-vacuity of the crown

The FEEC theorem with rates (`Feec.HilbertComplex.ConformingFamily.feec_rated`) on a genuine
conforming family, with nonzero data where the clauses can be exercised, collected with the
non-vacuity witnesses of the layers in `CrownNonVacuity` (`crownNonVacuity`).

* **The crown on the cube** (`cube_nonvacuous`): the de Rham complex `HΛ(Q)` of the cube
  `Q = (0, ½)ⁿ`, `n ≥ 2` (infinite-dimensional `L²` spaces), with the lowest-order Whitney forms
  of the Freudenthal meshes and the smoothed projections (`FEM.whitneyFamily`, a refining family
  `h_N → 0`) and their Jackson estimate (`FEM.whitneyJackson`): the rated verdict
  `ConformingFamily.Verdict.Rated` holds; the static clause applies in every degree (closed
  range, `FEM.closedRangeAt`) with nonzero harmonic forms (`ℌ⁰ = ℝ · 1`); on the window
  `HΛ¹ → HΛ² → HΛ³` the vanishing-field constraint `E = 0`, `B = 0` (`Maxwell.potential`) does
  not reduce `L`, and the departure clause `leaves_symm` of `Verdict.constrained` fires: a datum
  of `D(L) ∩ K` leaves `K`; the heat clause applies on the window `HΛ⁰ → ⋯ → HΛⁿ` with a nonzero
  datum of its core.
* **The heat clause, fully discrete** (`Corollaries.Cube.FEM.heat_crankNicolson`): Crank–Nicolson
  and the θ-schemes for every admissible sequence on the cube, with a nonzero datum of the core.
* **The wave clause with a non-reducing constraint** (`Maxwell.torus_potential_approxFEEC`): the
  spectral Galerkin family of `𝕋ᵈ`.
* **Closed range and finite-dimensional harmonic forms in infinite dimension**: the compactness
  property, which gives both, holds on `ℓ²`
  (`Feec.Counterexamples.hasCompactProperty_infiniteDimensional`).
* **The layers, beyond conforming families** (not crown instances: finite-dimensional complexes
  and bounded generators): variational crimes with nonzero defects instantiate the approximating
  FEEC theorem, with rates and both residual branches (`ApproxFEEC.perturbed_nonvacuous`,
  `ApproxFEEC.projPerturbed_nonvacuous`, `ApproxComplex.scaled_nonvacuous`,
  `ApproxComplexCrime.shifted_nonvacuous`, `ApproxComplexCrime.mixed_nonvacuous`); a Hodge wave
  equation with `L ≠ 0` (`Feec.Examples.idComplex_nonvacuous`) and a nonzero skew generator
  (`Feec.Examples.rotGen_standing_hypotheses`).
* **The Banach layer in a norm that is not Hilbert-contractive** (`maxNorm`,
  `Feec.Models.Cube.MaxNormHeat.maxNormHeat_nonvacuous`): lumped-mass `P₁` elements for the heat
  equation on the Freudenthal meshes of every cube, Dirichlet data, in the maximum norm at the
  nodes: non-obtuse meshes, the difference stencil, the discrete maximum principle (`M = 1`),
  consistency `n B₄ h² / 12`, and the errors of the semidiscrete equation, of backward Euler and
  of every A-stable rational scheme against every classical solution, through
  `Feec.TimeStepping.stableFamily`, also in `L^∞(Q)` for the finite element function (the
  scheme is the lumped-mass Galerkin method on the global `P₁` space); the first eigenmode `e^{-λt} ∏ᵢ sin(π(xᵢ - bᵢ)/s)` is such a
  solution, nonzero, with bounded second derivatives
  (`Feec.Models.Cube.MaxNormHeat.sineSolution`).
* **Natural boundary conditions in the maximum norm** (`neumann`,
  `Feec.Models.Cube.MaxNormNeumann.maxNormNeumann_nonvacuous`): lumped-mass `P₁` elements on all
  nodes of the Freudenthal meshes, the discrete maximum principle (`Lₕ 𝟙 = 0`), consistency
  `O(h²)` at the interior and `O(1)` at the boundary nodes, and the semidiscrete error `O(h)` in
  the maximum norm at the nodes (barrier `|x - c|²`); the first Neumann eigenmode
  `e^{-λt} ∏ᵢ cos(π(xᵢ - bᵢ)/s)` is a nonzero classical solution
  (`Feec.Models.Cube.MaxNormNeumann.cosSolution`).
* **The explicit map of the BGG layer on smooth fields (algebraic layer)**
  (`Feec.Domain.smoothBGGVerdict`): the cochain map (30) of Theorem 7 of [ArnoldHu2021] is a
  quasi-isomorphism on the smooth Hessian, elasticity and div-div complexes, with the Koszul
  null-homotopies and explicit right inverses, and the image of the constant pairs represents
  their degree-`0` cohomology (informally `[c + K⁰ c̃]`: the affine functions, the infinitesimal
  rigid motions, the lowest-order Raviart–Thomas fields). The explicit-map fields of the analytic
  `Feec.BGG.HilbertData.BGGVerdict` remain vacuous for these complexes on `L²`: their hypothesis
  fails there (`Feec.Domain.hessianMaximalData_not_injSurjWith`, recorded in
  `Feec.Counterexamples.CrownSharpness`).

Not exercised here: a nonzero datum of a Jackson rate class with a non-stationary orbit (the zero
datum lies in every Whitney class, `Maxwell.zero_mem_cubePMC_ofJackson`).

## Main definitions

* `cubePotential`; `CrownNonVacuity`.

## Main results

* **`cube_nonvacuous`**, **`crownNonVacuity`**; `cube_exists_d_ne_zero`,
  `cube_not_isReducing_potential`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3, §5
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], Theorem 7, Corollary 1
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4, §4.6, §4.10, Prop. 4.17

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Metric Set

@[expose] public noncomputable section

namespace Feec.Instances

open HilbertComplex Models.Cube FEM
open Feec.Domain (L2F formIdx)

/-! ### The crown on the cube -/

variable {n : ℕ}

/-- **`d : HΛ¹(Q) → HΛ²(Q)` is not zero** (`n ≥ 2`): the closed `1`-forms are a proper closed
subspace (`Feec.Domain.maximalComplex_cycles_one_ne_top`), so some form of `D(d)` orthogonal to
them is not closed. -/
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

/-- **The vanishing-field constraint does not reduce the wave operator of `HΛ¹ → HΛ² → HΛ³`** on
the cube (`n ≥ 2`, `Maxwell.not_isReducing_potential`). -/
theorem cube_not_isReducing_potential (hn : 2 ≤ n) :
    ¬ ((complex n).window 1 3).wave.IsReducing (cubePotential n) :=
  Maxwell.not_isReducing_potential _ (cube_exists_d_ne_zero hn)

variable [NeZero n]

/-- **The crown on the cube, not vacuously** (`n ≥ 2`). For the Whitney forms of the Freudenthal
meshes (`FEM.whitneyFamily`) with their Jackson estimate (`FEM.whitneyJackson`):

* the rated FEEC theorem holds (`ConformingFamily.feec_rated`);
* `static`: closed range in every degree, and `ℌ⁰ ≠ 0` (the constants);
* `constrained`: on `HΛ¹ → HΛ² → HΛ³` the vanishing-field constraint does not reduce `L`, and
  the departure clause of the crown gives, for every `T > 0`, a datum of `D(L) ∩ K` that leaves
  `K` at some `t ∈ [-T, T]`;
* `heat`: on `HΛ⁰ → ⋯ → HΛⁿ` (closed range, finite-dimensional harmonic forms) the core has a
  nonzero datum. -/
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

/-- **The non-vacuity of the crown**: the rated crown on the Whitney forms of the cube with its
clauses exercised by nonzero data, the fully discrete heat clause and the non-reducing wave clause
on genuine families, and the non-vacuity witnesses of its layers. Each field is the statement of
the named theorem. -/
structure CrownNonVacuity : Prop where
  /-- the rated crown on the Whitney forms of the cube, with nonzero data -/
  cube : type_of% @cube_nonvacuous
  /-- the fully discrete heat clause on the cube, every admissible sequence, nonzero datum -/
  full : type_of% @Corollaries.Cube.FEM.heat_crankNicolson
  /-- the wave clause on `𝕋ᵈ` with a constraint that does not reduce `L` -/
  torus : type_of% @Maxwell.torus_potential_approxFEEC.{u}
  /-- closed range and finite-dimensional harmonic forms (the compactness property) on `ℓ²` -/
  compact : type_of% @Counterexamples.hasCompactProperty_infiniteDimensional.{u}
  /-- the approximating layer: inner-product and differential crimes, nonzero defect -/
  perturbed : type_of% @ApproxFEEC.perturbed_nonvacuous.{u}
  /-- the approximating layer: a non-scalar reading map, nonzero commutator defect -/
  projPerturbed : type_of% @ApproxFEEC.projPerturbed_nonvacuous.{u}
  /-- the approximating layer: a non-conforming discrete complex -/
  scaled : type_of% @ApproxComplex.scaled_nonvacuous.{u}
  /-- the approximating layer: a reading map that is not a cochain map -/
  shifted : type_of% @ApproxComplexCrime.shifted_nonvacuous.{u}
  /-- the approximating layer: both crimes, rate `min(α, β, γ)` -/
  mixed : type_of% @ApproxComplexCrime.mixed_nonvacuous.{u}
  /-- the Hodge wave equation of `𝕜 --id--> 𝕜 → 0`: `L ≠ 0`, well posed -/
  idComplex : type_of% @Examples.idComplex_nonvacuous.{u}
  /-- a nonzero bounded skew generator -/
  rotGen : type_of% @Examples.rotGen_standing_hypotheses.{u}
  /-- the explicit cochain map (30) of the BGG layer (Theorem 7, Corollary 1 in degree `0`) on
  smooth fields (algebraic layer) of the Hessian, elasticity and div-div complexes; the `L²`
  explicit-map fields remain vacuous for these complexes -/
  bgg : type_of% @Domain.smoothBGGVerdict.{u}
  /-- the Banach layer in the maximum norm at the nodes: the lumped-mass `P₁` heat equation on
  Freudenthal meshes, with a nonzero classical solution -/
  maxNorm : type_of% @Models.Cube.MaxNormHeat.maxNormHeat_nonvacuous
  /-- the Banach layer in the maximum norm with natural boundary conditions: the lumped-mass
  `P₁` heat equation on all nodes of the Freudenthal meshes, first order, with a nonzero
  classical solution -/
  neumann : type_of% @Models.Cube.MaxNormNeumann.maxNormNeumann_nonvacuous

/-- **The crown is not vacuous** (`CrownNonVacuity`). -/
theorem crownNonVacuity : CrownNonVacuity.{u} :=
  ⟨@cube_nonvacuous, @Corollaries.Cube.FEM.heat_crankNicolson,
    @Maxwell.torus_potential_approxFEEC, Counterexamples.hasCompactProperty_infiniteDimensional,
    ApproxFEEC.perturbed_nonvacuous, ApproxFEEC.projPerturbed_nonvacuous,
    ApproxComplex.scaled_nonvacuous, ApproxComplexCrime.shifted_nonvacuous,
    ApproxComplexCrime.mixed_nonvacuous, Examples.idComplex_nonvacuous,
    Examples.rotGen_standing_hypotheses, Domain.smoothBGGVerdict,
    @Models.Cube.MaxNormHeat.maxNormHeat_nonvacuous,
    @Models.Cube.MaxNormNeumann.maxNormNeumann_nonvacuous⟩

end Feec.Instances
