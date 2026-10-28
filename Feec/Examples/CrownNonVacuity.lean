module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.HilbertComplex.Approximation.ApproxComplexCrimeWitness
public import Feec.Counterexamples.Fredholm
public import Feec.Examples.NonVacuity

/-!
# Non-vacuity of the crown

The FEEC theorem (`Feec.HilbertComplex.ConformingFamily.feec`) on a concrete conforming family,
with nonzero data for every clause, and the non-vacuity witnesses of the layers it is assembled
from, collected in `CrownNonVacuity` (`crownNonVacuity`).

* **The crown itself** (`lineFamily_nonvacuous`): the line complex `𝕜 --id--> 𝕜 --0--> 𝕜 → ⋯`
  on `ComplexShape.up ℕ` (`lineComplex`) with the constant family `Vₕ = W` (`lineFamily`) meets
  the hypotheses of every field of `ConformingFamily.Verdict` with nonzero data: closed range and
  `ℌ² ≠ 0` (`static`), `L x ≠ 0` on the window `𝕜 --id--> 𝕜` (`wave`), a reducing and a
  non-reducing constraint (`constrained`), closed range of the window (`heat`), and a time scheme
  (`full`).
* **Closed range and finite-dimensional harmonic forms in infinite dimension**: the compactness
  property, which gives both, holds on `ℓ²`
  (`Feec.Counterexamples.hasCompactProperty_infiniteDimensional`).
* **The approximating layer beyond conforming families** (`Verdict.wave` is the approximating FEEC
  verdict of the conforming windows): variational crimes with nonzero defects instantiate the
  approximating FEEC theorem, with rates and both residual branches
  (`ApproxFEEC.perturbed_nonvacuous`, `ApproxFEEC.projPerturbed_nonvacuous`,
  `ApproxComplex.scaled_nonvacuous`, `ApproxComplexCrime.shifted_nonvacuous`,
  `ApproxComplexCrime.mixed_nonvacuous`).
* **The standing hypotheses of the wave equation**: a Hodge wave equation with `L ≠ 0`
  (`Feec.Examples.idComplex_nonvacuous`) and a nonzero skew generator
  (`Feec.Examples.rotGen_standing_hypotheses`).

## Main definitions

* `lineComplex`, `lineFamily`, `lineWindow`, `lineFirst`; `CrownNonVacuity`.

## Main results

* **`lineFamily_nonvacuous`**, **`crownNonVacuity`**.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4, §4.6, §4.10

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace LinearPMap
open Filter Topology Metric Set

@[expose] public noncomputable section

namespace Feec.Examples

open HilbertComplex

variable (𝕜 : Type*) [RCLike 𝕜]

/-! ### The line complex and its constant family -/

/-- The differentials of `𝕜 --id--> 𝕜 --0--> 𝕜 --0--> ⋯`. -/
def lineD (k : ℕ) : 𝕜 →ₗ.[𝕜] 𝕜 :=
  ((if k = 0 then ContinuousLinearMap.id 𝕜 𝕜 else 0 : 𝕜 →L[𝕜] 𝕜) : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤

/-- Only `d 0 1` is nonzero. -/
theorem lineD_succ (k : ℕ) : lineD 𝕜 (k + 1) = 0 := by
  simp only [lineD, Nat.add_one_ne_zero, ite_false]; rfl

/-- **The line complex** `𝕜 --id--> 𝕜 --0--> 𝕜 --0--> ⋯` on `ComplexShape.up ℕ`. -/
def lineComplex : HilbertComplex 𝕜 (ComplexShape.up ℕ) (fun _ => 𝕜) :=
  HilbertComplex.ofSucc (lineD 𝕜) (fun _ => by simp [lineD, dense_univ])
    (fun _ => ContinuousLinearMap.isClosed_toPMap_top _) (fun _ _ => Submodule.mem_top)
    fun k _ => LinearPMap.apply_eq_zero_of_eq_zero (lineD_succ 𝕜 k) _

/-- `d i j` is the identity for `(i, j) = (0, 1)` and `0` otherwise, everywhere defined. -/
theorem lineComplex_d (i j : ℕ) : (lineComplex 𝕜).d i j =
    ((if i = 0 ∧ j = 1 then .id 𝕜 𝕜 else 0 : 𝕜 →L[𝕜] 𝕜) : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤ := by
  by_cases h : i + 1 = j
  · subst h
    change HilbertComplex.ofSuccD (lineD 𝕜) i (i + 1) = _
    rw [HilbertComplex.ofSuccD_succ]
    simp only [lineD, Nat.add_eq_right, and_self]
  · refine ((lineComplex 𝕜).shape i j h).trans ?_
    simp only [show ¬(i = 0 ∧ j = 1) by omega, ite_false]; rfl


/-- Every differential is everywhere defined. -/
theorem lineComplex_domain (i j : ℕ) : ((lineComplex 𝕜).d i j).domain = ⊤ := by
  rw [lineComplex_d]; rfl

/-- Every adjoint is everywhere defined. -/
theorem lineComplex_adjoint_domain (i j : ℕ) : ((lineComplex 𝕜).d i j)†.domain = ⊤ := by
  rw [lineComplex_d, ContinuousLinearMap.adjoint_toPMap_top]; rfl

/-- The whole complex as its own subcomplex. -/
def lineTop : (lineComplex 𝕜).Subcomplex where
  V _ := ⊤
  le_domain i j := (lineComplex_domain 𝕜 i j).ge
  mapsTo _ _ _ _ := Submodule.mem_top

/-- The constant conforming family `Vₕ = W`, `πₕ = 1`. -/
noncomputable def lineFamily : ConformingFamily (lineComplex 𝕜) ℕ where
  l := atTop
  V _ := lineTop 𝕜
  finiteDimensional _ _ := inferInstanceAs (FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 𝕜))
  π _ :=
    { π := fun _ => LinearMap.id
      mem := fun _ _ => Submodule.mem_top
      proj := fun _ _ _ => rfl
      comm := fun _ _ _ => rfl }
  bound_π := ⟨1, fun _ _ _ => by simp⟩
  approx _ w := tendsto_const_nhds.congr fun _ =>
    (infDist_zero_of_mem (Submodule.mem_top : w ∈ (⊤ : Submodule 𝕜 𝕜))).symm

/-- The line complex has closed range (its spaces are finite-dimensional). -/
theorem lineComplex_closedRangeAt (i : ℕ) : (lineComplex 𝕜).ClosedRangeAt i :=
  Submodule.closed_of_finiteDimensional _

/-- `ℌ² = 𝕜`: the static clause concerns nonzero harmonic forms. -/
theorem lineComplex_harmonic_two : (lineComplex 𝕜).harmonic 2 = ⊤ := by
  refine eq_top_iff.2 fun x _ => (lineComplex 𝕜).mem_harmonic_iff.2 ⟨?_, ?_⟩
  · rw [(lineComplex 𝕜).cycles_eq (show (ComplexShape.up ℕ).Rel 2 3 from rfl)]
    refine LinearPMap.mem_ker_iff.2 ⟨⟨x, by rw [lineComplex_domain]; trivial⟩, rfl, ?_⟩
    rw [LinearPMap.apply_of_eq_toPMap (lineComplex_d 𝕜 2 3)]
    simp
  · rw [(lineComplex 𝕜).boundaries_eq (show (ComplexShape.up ℕ).Rel 1 2 from rfl)]
    rintro _ ⟨z, rfl⟩
    change ⟪(lineComplex 𝕜).d 1 2 z, x⟫_𝕜 = 0
    rw [LinearPMap.apply_of_eq_toPMap (lineComplex_d 𝕜 1 2)]
    simp

/-- The window `𝕜 --id--> 𝕜` of the line complex. -/
abbrev lineWindow := (lineComplex 𝕜).window 0 2

/-- `D(L)` is the whole window. -/
theorem mem_lineWindow_wave_domain (x : PiLp 2 fun _ : Fin 2 => 𝕜) :
    x ∈ (lineWindow 𝕜).wave.domain :=
  (lineWindow 𝕜).mem_wave_domain.2
    ⟨fun i j => by
      change x i ∈ ((lineComplex 𝕜).d _ _).domain
      rw [lineComplex_domain]; trivial,
     fun i j => by
      change x j ∈ ((lineComplex 𝕜).d _ _)†.domain
      rw [lineComplex_adjoint_domain]; trivial⟩

/-- The differentials of the window. -/
theorem lineWindow_d (i j : Fin 2) : (lineWindow 𝕜).d i j =
    ((if i = 0 ∧ j = 1 then .id 𝕜 𝕜 else 0 : 𝕜 →L[𝕜] 𝕜) : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤ := by
  change (lineComplex 𝕜).d (0 + (i : ℕ)) (0 + (j : ℕ)) = _
  rw [lineComplex_d]
  fin_cases i <;> fin_cases j <;> simp

/-- `(L x)₁ = x₀`. -/
theorem lineWindow_wave_apply_one (x : (lineWindow 𝕜).wave.domain) :
    ((lineWindow 𝕜).wave x) 1 = (x : PiLp 2 fun _ : Fin 2 => 𝕜) 0 := by
  rw [HilbertComplex.wave_apply, Fin.sum_univ_two, Fin.sum_univ_two,
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero ((lineWindow 𝕜).shape 1 0 (by simp)),
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero ((lineWindow 𝕜).shape 1 1 (by simp)),
    LinearPMap.apply_eq_zero_of_eq_zero ((lineWindow 𝕜).shape 1 1 (by simp)),
    LinearPMap.apply_of_eq_toPMap (lineWindow_d 𝕜 0 1)]
  simp

/-- The first factor `𝕜 × 0` of the window. -/
def lineFirst : Submodule 𝕜 (PiLp 2 fun _ : Fin 2 => 𝕜) :=
  totalSub fun i => if i = 0 then ⊤ else ⊥

/-- `𝕜 × 0` does not reduce `L`: `L (1, 0) = (0, 1)`. -/
theorem not_isReducing_lineFirst : ¬ (lineWindow 𝕜).wave.IsReducing (lineFirst 𝕜) := fun h => by
  set x : PiLp 2 (fun _ : Fin 2 => 𝕜) := PiLp.single 2 0 1
  have hxK : x ∈ lineFirst 𝕜 := fun i => by
    fin_cases i
    · simp
    · simp [x]
  have hm := h.mapsTo ⟨x, mem_lineWindow_wave_domain 𝕜 x⟩ hxK 1
  simp only [Fin.isValue, one_ne_zero, ite_false, Submodule.mem_bot] at hm
  rw [lineWindow_wave_apply_one] at hm
  simp [x] at hm

/-- **The crown on the line complex, with nonzero data in every clause.** The constant family
`lineFamily` is a conforming family of the line complex, so its `ConformingFamily.Verdict` holds
(`ConformingFamily.feec`), and the hypotheses of every field are met by nonzero data:

* `static`: closed range in every degree, and `ℌ² = 𝕜 ≠ 0`;
* `wave`: on the window `𝕜 --id--> 𝕜`, a datum with `L x ≠ 0`;
* `constrained`: both branches occur, `K = W` reduces `L` and `K = 𝕜 × 0` does not (so `leaves`
  applies to it);
* `heat`: the window has closed range;
* `full`: the window discretization has a time scheme (Crank–Nicolson). -/
theorem lineFamily_nonvacuous :
    (lineFamily 𝕜).Verdict ∧ (∀ i, (lineComplex 𝕜).ClosedRangeAt i) ∧
      (lineComplex 𝕜).harmonic 2 ≠ ⊥ ∧
      (∃ x : (lineWindow 𝕜).wave.domain, (lineWindow 𝕜).wave x ≠ 0) ∧
      (lineWindow 𝕜).wave.IsReducing ⊤ ∧ ¬ (lineWindow 𝕜).wave.IsReducing (lineFirst 𝕜) ∧
      (∀ i, (lineWindow 𝕜).ClosedRangeAt i) ∧
      Nonempty ((lineFamily 𝕜).windowFEEC 0 2 ⊤ (by simp)).toApprox.TimeScheme := by
  refine ⟨(lineFamily 𝕜).feec, lineComplex_closedRangeAt 𝕜, by
      rw [lineComplex_harmonic_two]; exact top_ne_bot,
    ⟨⟨PiLp.single 2 0 1, mem_lineWindow_wave_domain 𝕜 _⟩, fun h => ?_⟩,
    LinearPMap.isReducingPair_top _, not_isReducing_lineFirst 𝕜,
    fun _ => Submodule.closed_of_finiteDimensional _,
    ⟨DissipFEEC.crankNicolson _ (fun n : ℕ => 1 / ((n : ℝ) + 1)) fun _ => by positivity⟩⟩
  have := congrArg (fun y : PiLp 2 (fun _ : Fin 2 => 𝕜) => y 1) h
  simp only at this
  rw [lineWindow_wave_apply_one] at this
  simp at this

/-! ### The non-vacuity of the crown -/

universe u

/-- **The non-vacuity of the crown**: the crown on a conforming family with nonzero data in every
clause, and the non-vacuity witnesses of its layers. Each field is the statement of the named
theorem. -/
structure CrownNonVacuity : Prop where
  /-- the crown on the line complex, nonzero data in every clause -/
  crown : type_of% @lineFamily_nonvacuous.{u}
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
  idComplex : type_of% @idComplex_nonvacuous.{u}
  /-- a nonzero bounded skew generator -/
  rotGen : type_of% @rotGen_standing_hypotheses.{u}

/-- **The crown is not vacuous** (`CrownNonVacuity`). -/
theorem crownNonVacuity : CrownNonVacuity.{u} :=
  ⟨lineFamily_nonvacuous, Counterexamples.hasCompactProperty_infiniteDimensional,
    ApproxFEEC.perturbed_nonvacuous, ApproxFEEC.projPerturbed_nonvacuous,
    ApproxComplex.scaled_nonvacuous, ApproxComplexCrime.shifted_nonvacuous,
    ApproxComplexCrime.mixed_nonvacuous, idComplex_nonvacuous, rotGen_standing_hypotheses⟩

end Feec.Examples
