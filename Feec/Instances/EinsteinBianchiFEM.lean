module

public import Feec.Instances.EinsteinBianchiFEMMirrorCore
public import Feec.Instances.EinsteinBianchiFEMCubeCore

/-!
# The thesis' scheme (6.5) as an instance of the approximating FEEC theorem

The finite element scheme (6.5) of [QuennevilleBelair2015], §6.3, is not a discretization by
subcomplexes: its discrete complex couples the two rows of the BGG construction by
`S₀,ₕ = π¹S⁰ ≠ S⁰` (a variational crime, [HolstStern2012]), so it is not an instance of the
constrained FEEC theorem (`Feec.HilbertComplex.constrainedFEEC`). It is an instance of the
**approximating FEEC theorem** `Feec.HilbertComplex.approxFEEC` (statement
`Feec.HilbertComplex.ApproxFEEC.Verdict`), with both boundary conditions:

* **mirror boundary conditions** (`einsteinBianchi_mirrorFEM_approxFEEC`): the discretization
  `Feec.Instances.EinsteinBianchi.FEM.mirrorFEMApprox` of the real mirror BGG complex
  (`complexQℝ`) with the TSD constraint `tsdQℝ`, which reduces `L`; its core (TSD data of `D(L²)`)
  has closure the whole TSD constraint, so for every TSD datum and every convergent family of
  discrete initial values the scheme converges to the TSD solution uniformly on `[0, T]` and the
  residual tends to `0`; the rate classes give `O(h)` for TSD data of `D(L³)`
  (`einsteinBianchi_mirrorFEM_rate`) and `O(hˢ)` for TSD data in `H^{2+s}`, `0 ≤ s ≤ 1`
  (`einsteinBianchi_mirrorFEM_rate_sobolev`): the strength of
  `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM`, `mirror_waveFEM_rate_of_mem_domain` and
  `mirror_waveFEM_rate_sobolev_of_add_two`, for complex data and every convergent family of
  initial values (`MirrorFEMApproxVerdict`);
* **the thesis' boundary conditions** (`einsteinBianchi_standardCube_approxFEEC`): the
  discretization `Feec.Instances.EinsteinBianchi.FEM.standardCubeApprox` of the matrix model with
  the TSD constraint `thesisTSD`, which does not reduce `L`; its core `D(L²)` is dense, so the
  scheme converges for every datum; from the TSD datum `(0, 0, (0, β))` the exact solution leaves
  TSD and the residuals of every convergent family of discrete solutions tend to the positive
  distance of the exact solution from TSD (`standardCube_residual_not_mem`, the converse part
  of the approximating FEEC theorem; `StandardCubeApproxVerdict`).

In both instances the discrete solutions of the approximating discretization are the solutions
of (6.5) without source (`mirrorFEMApprox_sol_eq_scheme`, `standardCube_sol_eq_scheme`).

**Faithfulness caveat.** The (6.5) instances are faithful to `cubeWave`/`mirrorWave` (the
scheme (6.5) with `S₀,ₕ = π¹S⁰` for the smoothed, resp. parity-smoothed, cochain projections), not
to the variant with the canonical interpolant `Π`.

**The cores are orbit cores**: the comparison trajectory of a datum is the discrete orbit from
its orthogonal projection (zero consistency defect, `ApproxFEEC.orbitCore`); the approximation
hypothesis of the core is the model convergence theorem of (6.5) from the elliptic projection
(6.4), with which the orthogonal projection competes by best approximation
(`ApproxFEEC.IsOrthogonal.norm_sub_sol_proj_le`). What the approximating FEEC theorem adds to
the model theorems: complex data (real and imaginary parts), the closure of the core (all TSD
data, resp. all data, not only `D(L²)`), every convergent family of initial values, and the
constraint residual in both directions.

`einsteinBianchi_summary` is `Feec.Instances.EinsteinBianchi.einsteinBianchi_constrainedFEEC_summary`
together with `MirrorFEMApproxVerdict` and `StandardCubeApproxVerdict`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 4.17, §6.3 ((6.5), Table 6.1)
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3
-/

open scoped InnerProductSpace Topology
open Set Filter Metric

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi

open Feec.HilbertComplex Feec.Instances.EinsteinBianchi.FEM

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-! ### Mirror boundary conditions -/

section MirrorFEM

open Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.FEM (ParitySmoothingEstimates meshSize)
open Feec.FiniteElement (PolySeq)
open Feec.Models.Cube.MirrorBGG (SpaceQ)

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- **The mirror scheme (6.5) is an instance of the approximating FEEC theorem.**
[QuennevilleBelair2015], §6.3, (6.5) -/
theorem einsteinBianchi_mirrorFEM_approxFEEC :
    (mirrorFEMApprox hT hB).Verdict (mirrorFEMCore hT hB) :=
  approxFEEC _ _

end MirrorFEM

end Feec.Instances.EinsteinBianchi
