module

public import Feec.Physics.EinsteinBianchi.Propagation
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
  `tsd_propagates_classical`; and in `L²` (any strong solution, any forcing in the constraint):
  `euclidean_tsd_propagates`;
* **on the torus `𝕋³`**: `torus_tsd_propagates`;
* **on every open cube with tensorial mirror boundary conditions**: `cube_tsd_propagates`;
* **on bounded domains with the thesis' boundary conditions** (`H̊(curl)` for the curl, i.e.
  any complex with `d₁ ≤ curl_min`) the constraints do **not** propagate:
  `Feec.Counterexamples.BoundedDomainTSD.tsd_not_propagates`.

These are the physical readings of `Feec.HilbertComplex.ReducingSubcomplex.propagates` for the
model complexes of `Feec.Models.*`; the proofs are one-line references.

## References

* [QuennevilleBelair2015], Prop 3.6, §4.10 (Prop 4.17)
* [ACBY1997], [Friedrich1996]
-/

open Set

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi

/-- **Prop 3.6 on `ℝ³`, classical form**: `C²` solutions of the linearized EB system with
compact spatial support and TSD data stay TSD (`tsd_propagates`). Thesis: Prop 3.6 (corrected) -/
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

/-- **EB constraints propagate on `ℝ³`** (`L²` strong solutions, with forcing).
Thesis: Prop 4.17 -/
theorem euclidean_tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Models.Euclidean.GradCurl.Space}
    (hU : Evolution.IsStrongSolution Models.Euclidean.GradCurl.complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub Models.Euclidean.GradCurl.constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub Models.Euclidean.GradCurl.constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub Models.Euclidean.GradCurl.constraint :=
  Models.Euclidean.GradCurl.tsd_propagates hU h0 hF

/-- **EB constraints propagate on the torus `𝕋³`**. Thesis: Prop 4.17 -/
theorem torus_tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Models.Torus.GradCurl.Space}
    (hU : Evolution.IsStrongSolution Models.Torus.GradCurl.complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub Models.Torus.GradCurl.constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub Models.Torus.GradCurl.constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub Models.Torus.GradCurl.constraint :=
  Models.Torus.GradCurl.tsd_propagates hU h0 hF

/-- **EB constraints propagate on every open cube `∏ (bᵢ, bᵢ + s)` with mirror boundary
conditions** (the thesis' row-wise conditions only propagate stationary data); this is
`Feec.Models.Cube.Mirror.propagatesCube`. Thesis: Prop 4.17 (corrected) -/
alias cube_tsd_propagates := Models.Cube.Mirror.propagatesCube

end Feec.EinsteinBianchi
