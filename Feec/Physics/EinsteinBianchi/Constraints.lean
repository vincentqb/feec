module

public import Feec.Physics.EinsteinBianchi.Propagation
public import Feec.Physics.EinsteinBianchi.Nonlinear
public import Feec.Models.Torus.GradCurl
public import Feec.Models.Euclidean.GradCurl
public import Feec.Models.Cube.Mirror

/-!
# Constraint propagation for the linearized Einstein–Bianchi system: headline statements

The TSD constraints of the linearized Einstein–Bianchi system propagate on `ℝ³`, on the torus
`𝕋³` and on every open cube with mirror boundary conditions ([QuennevilleBelair2015], Prop 3.6,
Prop 4.17).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi

/-- On `ℝ³`, `C²` solutions of the linearized system with compact spatial support, locally
uniformly in time, and TSD data stay TSD for `t ≥ 0`. [QuennevilleBelair2015], Prop 3.6 (adapted) -/
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

/-- `C²` first variations, with compact spatial support locally uniformly in time, of solutions of
the nonlinear system through Minkowski space stay TSD if their data are.
[QuennevilleBelair2015], Prop 3.6 (adapted) -/
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

/-- On `ℝ³`, strong `L²` solutions of the Hodge wave equation of the grad–curl complex with data
and forcing in the constraint stay in the constraint. [QuennevilleBelair2015], Prop 4.17 -/
theorem euclidean_tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Models.Euclidean.GradCurl.Space}
    (hU : Evolution.IsStrongSolution Models.Euclidean.GradCurl.complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub Models.Euclidean.GradCurl.constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub Models.Euclidean.GradCurl.constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub Models.Euclidean.GradCurl.constraint :=
  Models.Euclidean.GradCurl.tsd_propagates hU h0 hF

/-- On the torus `𝕋³`, strong solutions of the Hodge wave equation of the grad–curl complex with
data and forcing in the constraint stay in the constraint. [QuennevilleBelair2015], Prop 4.17 -/
theorem torus_tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Models.Torus.GradCurl.Space}
    (hU : Evolution.IsStrongSolution Models.Torus.GradCurl.complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub Models.Torus.GradCurl.constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub Models.Torus.GradCurl.constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub Models.Torus.GradCurl.constraint :=
  Models.Torus.GradCurl.tsd_propagates hU h0 hF

/-- On every open cube with mirror boundary conditions, strong solutions with data and forcing in
the constraint stay there. [QuennevilleBelair2015], Prop 4.17 (adapted) -/
theorem cube_tsd_propagates {b : Models.BoundedDomain.R3} {s : ℝ} (hs : 0 < s) {a c : ℝ}
    {F U : ℝ → PiLp 2 (Models.Cube.Mirror.SpaceCube b s)}
    (hU : Evolution.IsStrongSolution (Models.Cube.Mirror.complexCube b s hs).wave (Icc a c) F U)
    (h0 : U a ∈ HilbertComplex.totalSub (Models.Cube.Mirror.tsdCube b s hs))
    (hF : ∀ t ∈ Icc a c, F t ∈ HilbertComplex.totalSub (Models.Cube.Mirror.tsdCube b s hs)) :
    ∀ t ∈ Icc a c, U t ∈ HilbertComplex.totalSub (Models.Cube.Mirror.tsdCube b s hs) :=
  Models.Cube.Mirror.propagatesCube hs hU h0 hF

/-- On every open cube with mirror boundary conditions, TSD data in `D(L)` and admissible TSD
forcing give a unique solution, which stays TSD. [QuennevilleBelair2015], Prop 4.17 (adapted) -/
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
