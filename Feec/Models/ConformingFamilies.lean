module

public import Feec.HilbertComplex.Approximation.ConformingFamily
public import Feec.HilbertComplex.Approximation.DiscreteCohomology
public import Feec.Models.Cube.CubicalFiniteElementConvergence
public import Feec.Models.Cube.FiniteElementConvergence
public import Feec.Models.Cube.PolyFiniteElementConvergence
public import Feec.Models.Parallelepiped.FiniteElement
public import Feec.Models.StarShapedWitness

/-!
# The discrete cohomology of the finite element families

Every finite element family of the models with uniformly bounded smoothed cochain projections is a
conforming family (`Feec.HilbertComplex.ConformingFamily`, the hypotheses of [AFW2010], §3.3 with
the bounds in `W`), of the maximal complex `HΛ` (natural boundary conditions) and, with vanishing
boundary DOFs, of the minimal complex `H̊Λ` (essential boundary conditions), defined with its
model:

* **the lowest-order Whitney forms** (`Cube.FEM.whitneyFamily`, `whitneyFamilyMin`);
* **every admissible sequence** `S : PolySeq` of the periodic table (every `P_rΛᵏ`, `P_r⁻Λᵏ` and the
  mixed sequences, any degree `r ≥ 1`; `Cube.FEM.polyFamily`, `polyFamilyMin`);
* on the cube, **the cubical elements `Q_b⁻Λᵏ`** of [ArnoldBoffiBonizzoni2015] on the uniform
  cubical meshes (`Q_r⁻Λᵏ` for `b = fun _ => r`, any `b_j ≥ 1`; `Cube.FEM.qMinusFamily`, with the
  smoothed projections of `Feec.Models.Cube.CubicalSmoothingEstimates` and the Jackson estimate
  `Cube.FEM.qMinusJackson` at every order `h^{s+1}`, `s + 1 ≤ min b`);

on **the Freudenthal meshes of the cube** `Q = (0, ½)ⁿ` (`Cube.FEM`, `ConformingFamily.ofSmoothing`
in `Feec.Models.Cube.FiniteElementConvergence` and `Feec.Models.Cube.PolyFiniteElementConvergence`),
**the image meshes of parallelepipeds** `Ω = A · Q + b` (`Parallelepiped`, transported by
`IsChainIso.comapFamily`) and **every shape-regular, quasi-uniform mesh family of a domain
star-shaped with respect to a ball** (`StarShaped.MeshFamily`). The smoothed projections are those
of [AFW2010], §5.5 and [ChristiansenWinther2008]; the approximation property is the density of the
finite element spaces in `L²`. Each family comes with its Jackson estimates (`whitneyJackson`,
`polyJackson`, …), the hypotheses of the rates of the static FEEC theorem.

With a closed constraint (`ConformingFamily.withConstraint`) each family, and each of its windows
(`ConformingFamily.window`), is a constrained FEEC discretization, so the constrained and the
approximating FEEC theorems hold for it at every polynomial order (e.g. the Maxwell instances
`Feec.Instances.Maxwell`).

**Discrete cohomology** ([AFW2010], Thm 3.4; `ConformingFamily.eventually_finrank_cohomology_eq`):
each family eventually has the cohomology of its complex. On the cube and on parallelepipeds,
`dim Hᵏ(Vₕ) = [k = 0]` and `dim Hᵏ(V̊ₕ) = [k = n]` for `N` large
(**`Cube.FEM.eventually_finrank_cohomology_poly`**, `_polyMin`, `_whitney`, `_whitneyMin`, and
the same in `Parallelepiped`), and the projections induce the isomorphisms
(`Cube.FEM.eventually_bijective_cohomologyMap_poly`, `_polyMin`, `_qMinus`; the cubical
elements also have `Cube.FEM.eventually_finrank_cohomology_qMinus`); on a star-shaped domain,
`dim Hᵏ(Vₕ) = dim Hᵏ(Ω)` in every degree `k` with closed range and finite-dimensional harmonic
forms (`StarShaped.MeshFamily.eventually_finrank_cohomology_poly` and the others), with no
hypothesis on every mesh family of a parallelepiped
(`StarShaped.Parallelepiped.eventually_finrank_cohomology_poly_general`, `_polyMin_general`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (the approximation property, bounded cochain projections), Thm 3.4 (cohomology), §5 (the
  spaces `P_rΛ`, `P_r⁻Λ`), §5.5 (smoothed projections)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3–§5 (the periodic table of the spaces `P_rΛ`, `P_r⁻Λ`)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §5 (the spaces `Q_r⁻Λᵏ`)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Filter Topology

@[expose] public noncomputable section

namespace Feec.Models

open Feec.HilbertComplex Feec.FiniteElement

/-! ### The cube -/

namespace Cube.FEM

variable {n : ℕ} [NeZero n]

/-! #### Discrete cohomology -/

/-- **The projections of every admissible sequence on the cube induce `Hᵏ(HΛ(Q)) ≅ Hᵏ(Vₕ)`** for
`N` large ([AFW2010], Thm 3.4; `ConformingFamily.eventually_bijective_cohomologyMap`). -/
theorem eventually_bijective_cohomologyMap_poly (S : PolySeq) (k : ℤ) :
    ∀ᶠ N in atTop, haveI := (polyFamily n S).finiteDimensional N
      Function.Bijective (((polyFamily n S).π N).cohomologyMap k) :=
  (polyFamily n S).eventually_bijective_cohomologyMap (closedRangeAt k)

/-- **The same with vanishing boundary DOFs**: `Hᵏ(H̊Λ(Q)) ≅ Hᵏ(V̊ₕ)` for `N` large. -/
theorem eventually_bijective_cohomologyMap_polyMin (S : PolySeq) (k : ℤ) :
    ∀ᶠ N in atTop, haveI := (polyFamilyMin n S).finiteDimensional N
      Function.Bijective (((polyFamilyMin n S).π N).cohomologyMap k) :=
  (polyFamilyMin n S).eventually_bijective_cohomologyMap (closedRangeAt_min k)

/-- **The projections of the cubical elements `Q_b⁻Λ` induce `Hᵏ(HΛ(Q)) ≅ Hᵏ(Vₕ)`** for `N`
large ([AFW2010], Thm 3.4). -/
theorem eventually_bijective_cohomologyMap_qMinus {b : Fin n → ℕ} (hb : ∀ j, 1 ≤ b j) (k : ℤ) :
    ∀ᶠ N in atTop, haveI := (qMinusFamily n hb).finiteDimensional N
      Function.Bijective (((qMinusFamily n hb).π N).cohomologyMap k) :=
  (qMinusFamily n hb).eventually_bijective_cohomologyMap (closedRangeAt k)

/-- **The Whitney complexes of the cube have the cohomology of `HΛ(Q)`** for `N` large
([AFW2010], Thm 3.4): `dim Hᵏ(Vₕ) = [k = 0]`. -/
theorem eventually_finrank_cohomology_whitney (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((whitney n N).toHilbertComplex.cohomology k) =
      if k = 0 then 1 else 0 :=
  ((whitneyFamily n).eventually_finrank_cohomology_eq (closedRangeAt k)).mono fun _ h =>
    h.trans (finrank_cohomology k)

/-- **The Whitney complexes with vanishing boundary DOFs have the cohomology of `H̊Λ(Q)`** for `N`
large: `dim Hᵏ(V̊ₕ) = [k = n]`. -/
theorem eventually_finrank_cohomology_whitneyMin (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((whitneyMin n N).toHilbertComplex.cohomology k) =
      if k = n then 1 else 0 :=
  ((whitneyFamilyMin n).eventually_finrank_cohomology_eq (closedRangeAt_min k)).mono fun _ h =>
    h.trans (finrank_cohomology_min k)

/-- **The complexes of every admissible sequence `S` have the cohomology of `HΛ(Q)`** for `N`
large ([AFW2010], Thm 3.4, §5.6): `dim Hᵏ(Vₕ) = [k = 0]`. -/
theorem eventually_finrank_cohomology_poly (S : PolySeq) (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((poly n S N).toHilbertComplex.cohomology k) =
      if k = 0 then 1 else 0 :=
  ((polyFamily n S).eventually_finrank_cohomology_eq (closedRangeAt k)).mono fun _ h =>
    h.trans (finrank_cohomology k)

/-- **The complexes of `S` with vanishing boundary DOFs have the cohomology of `H̊Λ(Q)`** for `N`
large: `dim Hᵏ(V̊ₕ) = [k = n]`. -/
theorem eventually_finrank_cohomology_polyMin (S : PolySeq) (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((polyMin n S N).toHilbertComplex.cohomology k) =
      if k = n then 1 else 0 :=
  ((polyFamilyMin n S).eventually_finrank_cohomology_eq (closedRangeAt_min k)).mono fun _ h =>
    h.trans (finrank_cohomology_min k)

/-- **The cubical complexes `Q_b⁻Λ` of the cube have the cohomology of `HΛ(Q)`** for `N` large
([AFW2010], Thm 3.4): `dim Hᵏ(Vₕ) = [k = 0]`. -/
theorem eventually_finrank_cohomology_qMinus {b : Fin n → ℕ} (hb : ∀ j, 1 ≤ b j) (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((qMinus n b N).toHilbertComplex.cohomology k) =
      if k = 0 then 1 else 0 :=
  ((qMinusFamily n hb).eventually_finrank_cohomology_eq (closedRangeAt k)).mono fun _ h =>
    h.trans (finrank_cohomology k)

end Cube.FEM

/-! ### Parallelepipeds -/

namespace Parallelepiped

variable {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

/-! #### Discrete cohomology -/

/-- **The Whitney complexes of `T(M_N)` have the cohomology of `HΛ(Ω)`** for `N` large
([AFW2010], Thm 3.4): `dim Hᵏ(Vₕ) = [k = 0]`. -/
theorem eventually_finrank_cohomology_whitney (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((whitney A hA b N).toHilbertComplex.cohomology k) =
      if k = 0 then 1 else 0 :=
  haveI := finiteDimensional_harmonic A hA b k
  ((whitneyFamily A hA b).eventually_finrank_cohomology_eq (closedRangeAt A hA b k)).mono
    fun _ h => h.trans (finrank_cohomology A hA b k)

/-- **The Whitney complexes with vanishing boundary DOFs have the cohomology of `H̊Λ(Ω)`** for
`N` large: `dim Hᵏ(V̊ₕ) = [k = n]`. -/
theorem eventually_finrank_cohomology_whitneyMin (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((whitneyMin A hA b N).toHilbertComplex.cohomology k) =
      if k = n then 1 else 0 :=
  haveI := finiteDimensional_harmonic_min A hA b k
  ((whitneyFamilyMin A hA b).eventually_finrank_cohomology_eq (closedRangeAt_min A hA b k)).mono
    fun _ h => h.trans (finrank_cohomology_min A hA b k)

/-- **The complexes of every admissible sequence `S` on `T(M_N)` have the cohomology of `HΛ(Ω)`**
for `N` large ([AFW2010], Thm 3.4, §5.6): `dim Hᵏ(Vₕ) = [k = 0]`. -/
theorem eventually_finrank_cohomology_poly (S : PolySeq) (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((poly A hA b S N).toHilbertComplex.cohomology k) =
      if k = 0 then 1 else 0 :=
  haveI := finiteDimensional_harmonic A hA b k
  ((polyFamily A hA b S).eventually_finrank_cohomology_eq (closedRangeAt A hA b k)).mono
    fun _ h => h.trans (finrank_cohomology A hA b k)

/-- **The complexes of `S` with vanishing boundary DOFs have the cohomology of `H̊Λ(Ω)`** for `N`
large: `dim Hᵏ(V̊ₕ) = [k = n]`. -/
theorem eventually_finrank_cohomology_polyMin (S : PolySeq) (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((polyMin A hA b S N).toHilbertComplex.cohomology k) =
      if k = n then 1 else 0 :=
  haveI := finiteDimensional_harmonic_min A hA b k
  ((polyFamilyMin A hA b S).eventually_finrank_cohomology_eq (closedRangeAt_min A hA b k)).mono
    fun _ h => h.trans (finrank_cohomology_min A hA b k)

end Parallelepiped

/-! ### Domains star-shaped with respect to a ball -/

namespace StarShaped.MeshFamily

variable {n : ℕ} [NeZero n] {D : StarDomain n} (M : MeshFamily D)

/-! #### Discrete cohomology -/

/-- **The Whitney complexes have the cohomology of `HΛ(Ω)`** for `N` large ([AFW2010], Thm 3.4),
in every degree `k` where `HΛ(Ω)` has closed range and finite-dimensional harmonic forms. -/
theorem eventually_finrank_cohomology_whitney {k : ℤ}
    [FiniteDimensional ℝ (D.complex.harmonic k)] (hk : D.complex.ClosedRangeAt k) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((M.whitney N).toHilbertComplex.cohomology k) =
      Module.finrank ℝ (D.complex.cohomology k) :=
  M.whitneyFamily.eventually_finrank_cohomology_eq hk

/-- **The Whitney complexes with vanishing boundary DOFs have the cohomology of `H̊Λ(Ω)`** for
`N` large. -/
theorem eventually_finrank_cohomology_whitneyMin {k : ℤ}
    [FiniteDimensional ℝ (D.complexMin.harmonic k)] (hk : D.complexMin.ClosedRangeAt k) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((M.whitneyMin N).toHilbertComplex.cohomology k) =
      Module.finrank ℝ (D.complexMin.cohomology k) :=
  M.whitneyFamilyMin.eventually_finrank_cohomology_eq hk

/-- **The complexes of every admissible sequence `S` have the cohomology of `HΛ(Ω)`** for `N`
large ([AFW2010], Thm 3.4, §5.6). -/
theorem eventually_finrank_cohomology_poly (S : PolySeq) {k : ℤ}
    [FiniteDimensional ℝ (D.complex.harmonic k)] (hk : D.complex.ClosedRangeAt k) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((M.poly S N).toHilbertComplex.cohomology k) =
      Module.finrank ℝ (D.complex.cohomology k) :=
  (M.polyFamily S).eventually_finrank_cohomology_eq hk

/-- **The complexes of `S` with vanishing boundary DOFs have the cohomology of `H̊Λ(Ω)`** for `N`
large. -/
theorem eventually_finrank_cohomology_polyMin (S : PolySeq) {k : ℤ}
    [FiniteDimensional ℝ (D.complexMin.harmonic k)] (hk : D.complexMin.ClosedRangeAt k) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((M.polyMin S N).toHilbertComplex.cohomology k) =
      Module.finrank ℝ (D.complexMin.cohomology k) :=
  (M.polyFamilyMin S).eventually_finrank_cohomology_eq hk

end StarShaped.MeshFamily

/-! ### Every quasi-uniform shape-regular mesh family of a parallelepiped -/

namespace StarShaped.Parallelepiped

variable {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)
  (M : MeshFamily (ParallelepipedWitness.starDomain A hA b)) (S : PolySeq)

/-- **The higher-order complexes of every quasi-uniform shape-regular mesh family of a
parallelepiped have the cohomology of `HΛ(Ω)`** for `N` large ([AFW2010], Thm 3.4), with no
hypothesis: `dim Hᵏ(Vₕ) = [k = 0]`. -/
theorem eventually_finrank_cohomology_poly_general (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((M.poly S N).toHilbertComplex.cohomology k) =
      if k = 0 then 1 else 0 :=
  (M.eventually_finrank_cohomology_poly S (Models.Parallelepiped.closedRangeAt A hA b k)).mono
    fun _ h => h.trans (Models.Parallelepiped.finrank_cohomology A hA b k)

/-- **The higher-order complexes with vanishing boundary DOFs of every quasi-uniform
shape-regular mesh family of a parallelepiped have the cohomology of `H̊Λ(Ω)`** for `N` large:
`dim Hᵏ(V̊ₕ) = [k = n]`. -/
theorem eventually_finrank_cohomology_polyMin_general (k : ℤ) :
    ∀ᶠ N in atTop, Module.finrank ℝ ((M.polyMin S N).toHilbertComplex.cohomology k) =
      if k = n then 1 else 0 :=
  (M.eventually_finrank_cohomology_polyMin S
    (Models.Parallelepiped.closedRangeAt_min A hA b k)).mono
    fun _ h => h.trans (Models.Parallelepiped.finrank_cohomology_min A hA b k)

end StarShaped.Parallelepiped

end Feec.Models
