import Feec.Instances.Maxwell

/-!
# Regression tests: the concrete Maxwell verdicts

The per-instance headline statements of `Feec.Instances.Maxwell` (`cubePMC_approxFEEC`,
`cubePMC_converges`, `torus_gauss_propagates`, ...) were folded into the generic statements
`Maxwell.wellPosed`, `Maxwell.gauss_propagates`, `Maxwell.converges` and the approximating FEEC
theorem `approxFEEC`, since every instance is `feec F a` for a conforming family `F`. The
examples below pin the concrete instances: each fails to elaborate if the generic statement stops
applying to a concrete discretization.

This file is part of the `FeecCheck` library, not of `Feec`.
-/

open Set Filter

namespace FeecCheck.MaxwellInstances

open Feec Feec.HilbertComplex Feec.Instances.Maxwell
open Feec.FiniteElement (PolySeq)

section Torus

open Feec.Models.Torus.DeRham

variable (d : Type*) [Fintype d] [LinearOrder d] (a : ℕ)

example : (torus d a).toApprox.Verdict (torus d a).toCore := approxFEEC _ _

example : ∀ t, ∀ x ∈ (torus d a).K, ((complex d).window a 3).waveGroup.S t x ∈ (torus d a).K :=
  gauss_propagates (torusFamily d) a

end Torus

section Cube

open Feec.Models.Cube

variable (n : ℕ) [NeZero n] (a : ℤ) (S : PolySeq)

example : (cubePMC n a).toApprox.Verdict (cubePMC n a).toCore := approxFEEC _ _
example : (cubePEC n a).toApprox.Verdict (cubePEC n a).toCore := approxFEEC _ _
example : (cubePolyPMC n S a).toApprox.Verdict (cubePolyPMC n S a).toCore := approxFEEC _ _
example : (cubePolyPEC n S a).toApprox.Verdict (cubePolyPEC n S a).toCore := approxFEEC _ _

example {x} (hx : x ∈ ((FEM.complex n).window a 3).wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution ((FEM.complex n).window a 3).wave (Icc 0 T) 0
      (fun t => ((FEM.complex n).window a 3).waveGroup.S t x) :=
  (wellPosed _ a hx T).1

example : ∀ t, ∀ x ∈ (cubePMC n a).K,
    ((FEM.complex n).window a 3).waveGroup.S t x ∈ (cubePMC n a).K :=
  gauss_propagates (FEM.whitneyFamily n) a

example : ∀ t, ∀ x ∈ (cubePEC n a).K,
    ((FEM.complexMin n).window a 3).waveGroup.S t x ∈ (cubePEC n a).K :=
  gauss_propagates (FEM.whitneyFamilyMin n) a

example (T : ℝ) (x : ((FEM.complex n).window a 3).wave.domain) :
    TendstoUniformlyOn
      (fun N t => ((FEM.complex n).window a 3).totalD.graphFst
        ((cubePMC n a).discrete N (waveLift _ x) t))
      (fun t => ((FEM.complex n).window a 3).waveGroup.S t x) atTop (Icc 0 T) :=
  (converges (FEM.whitneyFamily n) a T).1 x

end Cube

section Parallelepiped

variable {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)
  (a : ℤ)

example : (paraPMC A hA b a).toApprox.Verdict (paraPMC A hA b a).toCore := approxFEEC _ _
example : (paraPEC A hA b a).toApprox.Verdict (paraPEC A hA b a).toCore := approxFEEC _ _

end Parallelepiped

section StarShaped

open Feec.Models.StarShaped

variable {n : ℕ} [NeZero n] {D : StarDomain n} (M : MeshFamily D) (a : ℤ)

example : (starPMC M a).toApprox.Verdict (starPMC M a).toCore := approxFEEC _ _
example : (starPEC M a).toApprox.Verdict (starPEC M a).toCore := approxFEEC _ _

end StarShaped

end FeecCheck.MaxwellInstances
