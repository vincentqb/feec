module

public import Feec.Physics.EinsteinBianchi.Propagation
public import Feec.Physics.EinsteinBianchi.Nonlinear
public import Feec.Models.Torus.GradCurl
public import Feec.Models.Euclidean.GradCurl
public import Feec.Models.Cube.Mirror

/-!
# Constraint propagation for the linearized Einstein–Bianchi system: headline statements

The linearized EB system (4.14) is the Hodge wave equation of the matrix grad–curl complex
`H¹(·; ℂ³) --grad--> H(curl; ℂ³ˣ³) --curl--> L²(ℂ³ˣ³)`, with the constraint
`{0} × L²(TSD) × L²(TSD)` (symmetric, trace-free, divergence-free `E` and `B`). Whether the
constraints propagate depends on the domain and the boundary conditions:

* **on `ℝ³`**, classically (`C²` fields with compact spatial support, the energy method):
  `tsd_propagates_classical`; for the first variation of every family of solutions of the
  nonlinear EB system through Minkowski space (linearized gravity: the frame data of a family of
  vacuum metrics, `vacuum_nonlinearEB`), `tsd_propagates_variation`; and in `L²` (any strong
  solution, any forcing in the constraint): `euclidean_tsd_propagates`;
* **on the torus `𝕋³`**: `torus_tsd_propagates`;
* **on every open cube with tensorial mirror boundary conditions**: `cube_tsd_propagates`,
  `cube_tsd_existsUnique`;
* **on bounded domains with the thesis' boundary conditions** (`H̊(curl)` for the curl, i.e.
  any complex with `d₁ ≤ curl_min`) the constraints do **not** propagate:
  `Feec.Counterexamples.BoundedDomainTSD.tsd_not_propagates`.

These are the physical readings of `Feec.HilbertComplex.ReducingSubcomplex.propagates` for the
model complexes of `Feec.Models.*`; the proofs are one-line references.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 3.6, §4.10 (Prop 4.17)
* [A. Anderson, Y. Choquet-Bruhat, J. W. York, Jr., *Einstein–Bianchi hyperbolic system for general relativity*][ACBY1997]
* [H. Friedrich, *Hyperbolic reductions for Einstein's equations*][Friedrich1996]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi

/-- **Prop 3.6 on `ℝ³`, classical form**: `C²` solutions of the linearized EB system with
compact spatial support and TSD data stay TSD (`tsd_propagates`). [QuennevilleBelair2015], Prop 3.6 (corrected) -/
theorem tsd_propagates_classical {E B : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hEc : ∀ i j, ContDiff ℝ 2 fun Y => E Y i j) (hBc : ∀ i j, ContDiff ℝ 2 fun Y => B Y i j)
    (hsupp : ∀ s : ℝ, ∃ K : Set (Fin 3 → ℝ), IsCompact K ∧
      ∀ r ∈ Metric.closedBall s 1, ∀ x ∉ K, E (ev r x) = 0 ∧ B (ev r x) = 0)
    (hEeq : ∀ Y : Fin 4 → ℝ, 0 < Y 0 →
      jet4 E Y 0 = -MatrixSymbol.curl (sp (jet4 B Y)))
    (hBeq : ∀ Y : Fin 4 → ℝ, 0 < Y 0 → jet4 B Y 0 = MatrixSymbol.curl (sp (jet4 E Y)))
    (h0 : ∀ x, TSDAt E (ev 0 x) ∧ TSDAt B (ev 0 x)) (t : ℝ) (ht : 0 ≤ t) (x : Fin 3 → ℝ) :
    TSDAt E (ev t x) ∧ TSDAt B (ev t x) :=
  tsd_propagates hEc hBc hsupp hEeq hBeq h0 t ht x

/-- **Prop 3.6 for linearized gravity**: along a family of solutions of the nonlinear EB system
through Minkowski space (`γ 0 = 0`, `E 0 = B 0 = 0`; e.g. the frame data of a family of vacuum
metrics, `vacuum_nonlinearEB`), the first variations `E'`, `B'`, whose jets are the variations of
the jets, solve the linearized EB system at every point (`ebJet_of_nonlinearEB`); when they are
`C²` with compact spatial support, TSD data stay TSD (`tsd_propagates_classical`).
[QuennevilleBelair2015], §3.4, Prop 3.6 (corrected) -/
theorem tsd_propagates_variation {γ : ℝ → (Fin 4 → ℝ) → FrameConn}
    {E B : ℝ → (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {dE dB : ℝ → (Fin 4 → ℝ) → Jet4}
    {γ' : (Fin 4 → ℝ) → FrameConn} {E' B' : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hN : ∀ ε Y, NonlinearEB (γ ε Y) (E ε Y) (B ε Y) (dE ε Y) (dB ε Y))
    (hγ : ∀ Y l κ ν, HasDerivAt (fun ε => γ ε Y l κ ν) (γ' Y l κ ν) 0)
    (hE : ∀ Y i j, HasDerivAt (fun ε => E ε Y i j) (E' Y i j) 0)
    (hB : ∀ Y i j, HasDerivAt (fun ε => B ε Y i j) (B' Y i j) 0)
    (hdE : ∀ Y μ i j, HasDerivAt (fun ε => dE ε Y μ i j) (jet4 E' Y μ i j) 0)
    (hdB : ∀ Y μ i j, HasDerivAt (fun ε => dB ε Y μ i j) (jet4 B' Y μ i j) 0)
    (hγ0 : ∀ Y, γ 0 Y = 0) (hE0 : ∀ Y, E 0 Y = 0) (hB0 : ∀ Y, B 0 Y = 0)
    (hEc : ∀ i j, ContDiff ℝ 2 fun Y => E' Y i j) (hBc : ∀ i j, ContDiff ℝ 2 fun Y => B' Y i j)
    (hsupp : ∀ s : ℝ, ∃ K : Set (Fin 3 → ℝ), IsCompact K ∧
      ∀ r ∈ Metric.closedBall s 1, ∀ x ∉ K, E' (ev r x) = 0 ∧ B' (ev r x) = 0)
    (h0 : ∀ x, TSDAt E' (ev 0 x) ∧ TSDAt B' (ev 0 x)) (t : ℝ) (ht : 0 ≤ t) (x : Fin 3 → ℝ) :
    TSDAt E' (ev t x) ∧ TSDAt B' (ev t x) := by
  have hJ : ∀ Y, EBJet (jet4 E' Y) (jet4 B' Y) := fun Y =>
    ebJet_of_nonlinearEB (hγ Y) (hE Y) (hB Y) (hdE Y) (hdB Y) (hγ0 Y) (hE0 Y) (hB0 Y)
      fun ε => hN ε Y
  exact tsd_propagates_classical hEc hBc hsupp
    (fun Y _ => eq_neg_of_add_eq_zero_left (hJ Y).2.2.1) (fun Y _ => sub_eq_zero.1 (hJ Y).2.2.2)
    h0 t ht x

/-- **EB constraints propagate on `ℝ³`** (`L²` strong solutions, with forcing).
[QuennevilleBelair2015], Prop 4.17 -/
theorem euclidean_tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Models.Euclidean.GradCurl.Space}
    (hU : Evolution.IsStrongSolution Models.Euclidean.GradCurl.complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub Models.Euclidean.GradCurl.constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub Models.Euclidean.GradCurl.constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub Models.Euclidean.GradCurl.constraint :=
  Models.Euclidean.GradCurl.tsd_propagates hU h0 hF

/-- **EB constraints propagate on the torus `𝕋³`**. [QuennevilleBelair2015], Prop 4.17 -/
theorem torus_tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Models.Torus.GradCurl.Space}
    (hU : Evolution.IsStrongSolution Models.Torus.GradCurl.complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub Models.Torus.GradCurl.constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub Models.Torus.GradCurl.constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub Models.Torus.GradCurl.constraint :=
  Models.Torus.GradCurl.tsd_propagates hU h0 hF

/-- **EB constraints propagate on every open cube `∏ (bᵢ, bᵢ + s)` with mirror boundary
conditions** (the thesis' row-wise conditions only propagate stationary data,
`Feec.Counterexamples.CubeStationary`): strong solutions of the Hodge wave equation of the mirror
complex `Feec.Models.Cube.Mirror.complexCube` with data and forcing in the constraint
`Feec.Models.Cube.Mirror.tsdCube` stay there. [QuennevilleBelair2015], Prop 4.17 (corrected) -/
theorem cube_tsd_propagates {b : Models.BoundedDomain.R3} {s : ℝ} (hs : 0 < s) {a c : ℝ}
    {F U : ℝ → PiLp 2 (Models.Cube.Mirror.SpaceCube b s)}
    (hU : Evolution.IsStrongSolution (Models.Cube.Mirror.complexCube b s hs).wave (Icc a c) F U)
    (h0 : U a ∈ HilbertComplex.totalSub (Models.Cube.Mirror.tsdCube b s hs))
    (hF : ∀ t ∈ Icc a c, F t ∈ HilbertComplex.totalSub (Models.Cube.Mirror.tsdCube b s hs)) :
    ∀ t ∈ Icc a c, U t ∈ HilbertComplex.totalSub (Models.Cube.Mirror.tsdCube b s hs) :=
  Models.Cube.Mirror.propagatesCube hs hU h0 hF

/-- **The EB system on every open cube with mirror boundary conditions, with existence and
uniqueness**: for TSD data in `D(L)` and admissible TSD forcing, the Hodge wave equation has a
classical solution, unique among strong solutions, which stays TSD.
[QuennevilleBelair2015], Prop 4.17 (corrected) -/
theorem cube_tsd_existsUnique {b : Models.BoundedDomain.R3} {s : ℝ} (hs : 0 < s)
    {U₀ : PiLp 2 (Models.Cube.Mirror.SpaceCube b s)}
    (hU₀ : U₀ ∈ (Models.Cube.Mirror.complexCube b s hs).wave.domain)
    (hU₀S : U₀ ∈ HilbertComplex.totalSub (Models.Cube.Mirror.tsdCube b s hs))
    {F : ℝ → PiLp 2 (Models.Cube.Mirror.SpaceCube b s)} {a c : ℝ}
    (hF : Evolution.ForcingClass.admissible (Models.Cube.Mirror.complexCube b s hs).wave a c F)
    (hFS : ∀ t ∈ Icc a c, F t ∈ HilbertComplex.totalSub (Models.Cube.Mirror.tsdCube b s hs)) :
    ∃ U, U a = U₀ ∧
      Evolution.IsClassicalSolution (Models.Cube.Mirror.complexCube b s hs).wave (Icc a c) F U ∧
      (∀ t ∈ Icc a c, U t ∈ HilbertComplex.totalSub (Models.Cube.Mirror.tsdCube b s hs)) ∧
      ∀ V, V a = U₀ →
        Evolution.IsStrongSolution (Models.Cube.Mirror.complexCube b s hs).wave (Icc a c) F V →
          EqOn V U (Icc a c) :=
  Models.Cube.Mirror.existsUnique_memCube hs hU₀ hU₀S hF hFS

end Feec.EinsteinBianchi
