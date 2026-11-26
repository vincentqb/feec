module

public import Feec.HilbertComplex.Approximation.ConformingFamily
public import Feec.HilbertComplex.Approximation.DiscreteCohomology
public import Feec.Models.Cube.CubicalFiniteElementConvergence
public import Feec.Models.Cube.FiniteElementConvergence
public import Feec.Models.Cube.PolyFiniteElementConvergence
public import Feec.Models.Parallelepiped.FiniteElement
public import Feec.Models.Parallelepiped.StarShaped

/-!
# The discrete cohomology of the finite element families

The finite element families of the models (the Whitney forms, every admissible sequence `P_rΛ`,
`P_r⁻Λ`, and the cubical elements `Q_b⁻Λ` of [ArnoldBoffiBonizzoni2015]) eventually have the
cohomology of their complex, `HΛ` or, with vanishing boundary DOFs, `H̊Λ` ([AFW2010], Thm 3.4); on
star-shaped domains, in the degrees with closed range and finite-dimensional harmonic forms.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Filter Topology

@[expose] public noncomputable section

namespace Feec.Models

open Feec.HilbertComplex Feec.FiniteElement

namespace Cube.FEM

variable {n : ℕ} [NeZero n]

/-- The projections of every admissible sequence on the cube induce `Hᵏ(HΛ(Q)) ≅ Hᵏ(Vₕ)` for `N`
large. [AFW2010], Thm 3.4 -/
theorem eventually_bijective_cohomologyMap_poly (S : PolySeq) (k : ℤ) :
    ∀ᶠ N in atTop, haveI := (polyFamily n S).finiteDimensional N
      Function.Bijective (((polyFamily n S).π N).cohomologyMap k) :=
  (polyFamily n S).eventually_bijective_cohomologyMap (closedRangeAt k)

theorem eventually_bijective_cohomologyMap_polyMin (S : PolySeq) (k : ℤ) :
    ∀ᶠ N in atTop, haveI := (polyFamilyMin n S).finiteDimensional N
      Function.Bijective (((polyFamilyMin n S).π N).cohomologyMap k) :=
  (polyFamilyMin n S).eventually_bijective_cohomologyMap (closedRangeAt_min k)

theorem eventually_bijective_cohomologyMap_qMinus {b : Fin n → ℕ} (hb : ∀ j, 1 ≤ b j) (k : ℤ) :
    ∀ᶠ N in atTop, haveI := (qMinusFamily n hb).finiteDimensional N
      Function.Bijective (((qMinusFamily n hb).π N).cohomologyMap k) :=
  (qMinusFamily n hb).eventually_bijective_cohomologyMap (closedRangeAt k)

theorem eventually_finrank_cohomology_whitney (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((whitney n N).toHilbertComplex.cohomology k) =
      if k = 0 then 1 else 0 :=
  ((whitneyFamily n).eventually_finrank_cohomology_eq (closedRangeAt k)).mono fun _ h =>
    h.trans (finrank_cohomology k)

theorem eventually_finrank_cohomology_whitneyMin (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((whitneyMin n N).toHilbertComplex.cohomology k) =
      if k = n then 1 else 0 :=
  ((whitneyFamilyMin n).eventually_finrank_cohomology_eq (closedRangeAt_min k)).mono fun _ h =>
    h.trans (finrank_cohomology_min k)

/-- On the cube, the complexes of every admissible sequence have `dim Hᵏ(Vₕ) = [k = 0]` for `N`
large. [AFW2010], Thm 3.4 -/
theorem eventually_finrank_cohomology_poly (S : PolySeq) (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((poly n S N).toHilbertComplex.cohomology k) =
      if k = 0 then 1 else 0 :=
  ((polyFamily n S).eventually_finrank_cohomology_eq (closedRangeAt k)).mono fun _ h =>
    h.trans (finrank_cohomology k)

theorem eventually_finrank_cohomology_polyMin (S : PolySeq) (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((polyMin n S N).toHilbertComplex.cohomology k) =
      if k = n then 1 else 0 :=
  ((polyFamilyMin n S).eventually_finrank_cohomology_eq (closedRangeAt_min k)).mono fun _ h =>
    h.trans (finrank_cohomology_min k)

theorem eventually_finrank_cohomology_qMinus {b : Fin n → ℕ} (hb : ∀ j, 1 ≤ b j) (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((qMinus n b N).toHilbertComplex.cohomology k) =
      if k = 0 then 1 else 0 :=
  ((qMinusFamily n hb).eventually_finrank_cohomology_eq (closedRangeAt k)).mono fun _ h =>
    h.trans (finrank_cohomology k)

end Cube.FEM

namespace Parallelepiped

variable {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

theorem eventually_finrank_cohomology_whitney (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((whitney A hA b N).toHilbertComplex.cohomology k) =
      if k = 0 then 1 else 0 :=
  haveI := finiteDimensional_harmonic A hA b k
  ((whitneyFamily A hA b).eventually_finrank_cohomology_eq (closedRangeAt A hA b k)).mono
    fun _ h => h.trans (finrank_cohomology A hA b k)

theorem eventually_finrank_cohomology_whitneyMin (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((whitneyMin A hA b N).toHilbertComplex.cohomology k) =
      if k = n then 1 else 0 :=
  haveI := finiteDimensional_harmonic_min A hA b k
  ((whitneyFamilyMin A hA b).eventually_finrank_cohomology_eq (closedRangeAt_min A hA b k)).mono
    fun _ h => h.trans (finrank_cohomology_min A hA b k)

/-- On `T(M_N)`, the complexes of every admissible sequence have `dim Hᵏ(Vₕ) = [k = 0]` for `N`
large. [AFW2010], Thm 3.4 -/
theorem eventually_finrank_cohomology_poly (S : PolySeq) (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((poly A hA b S N).toHilbertComplex.cohomology k) =
      if k = 0 then 1 else 0 :=
  haveI := finiteDimensional_harmonic A hA b k
  ((polyFamily A hA b S).eventually_finrank_cohomology_eq (closedRangeAt A hA b k)).mono
    fun _ h => h.trans (finrank_cohomology A hA b k)

theorem eventually_finrank_cohomology_polyMin (S : PolySeq) (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((polyMin A hA b S N).toHilbertComplex.cohomology k) =
      if k = n then 1 else 0 :=
  haveI := finiteDimensional_harmonic_min A hA b k
  ((polyFamilyMin A hA b S).eventually_finrank_cohomology_eq (closedRangeAt_min A hA b k)).mono
    fun _ h => h.trans (finrank_cohomology_min A hA b k)

end Parallelepiped

namespace StarShaped.MeshFamily

variable {n : ℕ} [NeZero n] {D : StarDomain n} (M : MeshFamily D)

theorem eventually_finrank_cohomology_whitney {k : ℤ}
    [FiniteDimensional ℝ (D.complex.harmonic k)] (hk : D.complex.ClosedRangeAt k) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((M.whitney N).toHilbertComplex.cohomology k) =
      Module.finrank ℝ (D.complex.cohomology k) :=
  M.whitneyFamily.eventually_finrank_cohomology_eq hk

theorem eventually_finrank_cohomology_whitneyMin {k : ℤ}
    [FiniteDimensional ℝ (D.complexMin.harmonic k)] (hk : D.complexMin.ClosedRangeAt k) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((M.whitneyMin N).toHilbertComplex.cohomology k) =
      Module.finrank ℝ (D.complexMin.cohomology k) :=
  M.whitneyFamilyMin.eventually_finrank_cohomology_eq hk

/-- The complexes of every admissible sequence have the cohomology of `HΛ(Ω)` for `N` large, in
every degree with closed range and finite-dimensional harmonic forms. [AFW2010], Thm 3.4 -/
theorem eventually_finrank_cohomology_poly (S : PolySeq) {k : ℤ}
    [FiniteDimensional ℝ (D.complex.harmonic k)] (hk : D.complex.ClosedRangeAt k) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((M.poly S N).toHilbertComplex.cohomology k) =
      Module.finrank ℝ (D.complex.cohomology k) :=
  (M.polyFamily S).eventually_finrank_cohomology_eq hk

theorem eventually_finrank_cohomology_polyMin (S : PolySeq) {k : ℤ}
    [FiniteDimensional ℝ (D.complexMin.harmonic k)] (hk : D.complexMin.ClosedRangeAt k) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((M.polyMin S N).toHilbertComplex.cohomology k) =
      Module.finrank ℝ (D.complexMin.cohomology k) :=
  (M.polyFamilyMin S).eventually_finrank_cohomology_eq hk

end StarShaped.MeshFamily

namespace StarShaped.Parallelepiped

variable {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)
  (M : MeshFamily (ParallelepipedWitness.starDomain A hA b)) (S : PolySeq)

/-- On every quasi-uniform shape-regular mesh family of a parallelepiped, the higher-order
complexes have `dim Hᵏ(Vₕ) = [k = 0]` for `N` large. [AFW2010], Thm 3.4 -/
theorem eventually_finrank_cohomology_poly_general (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((M.poly S N).toHilbertComplex.cohomology k) =
      if k = 0 then 1 else 0 :=
  (M.eventually_finrank_cohomology_poly S (Models.Parallelepiped.closedRangeAt A hA b k)).mono
    fun _ h => h.trans (Models.Parallelepiped.finrank_cohomology A hA b k)

theorem eventually_finrank_cohomology_polyMin_general (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((M.polyMin S N).toHilbertComplex.cohomology k) =
      if k = n then 1 else 0 :=
  (M.eventually_finrank_cohomology_polyMin S
    (Models.Parallelepiped.closedRangeAt_min A hA b k)).mono
    fun _ h => h.trans (Models.Parallelepiped.finrank_cohomology_min A hA b k)

end StarShaped.Parallelepiped

end Feec.Models
