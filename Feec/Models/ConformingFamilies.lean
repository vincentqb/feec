module

public import Feec.HilbertComplex.Approximation.ConformingFamily
public import Feec.Models.Cube.FiniteElementConvergence
public import Feec.Models.Cube.PolyFiniteElementConvergence
public import Feec.Models.Parallelepiped.FiniteElement
public import Feec.Models.StarShaped.FiniteElement
public import Feec.Models.StarShaped.PolyFiniteElement

/-!
# The finite element families as conforming families

Every finite element family of the models with uniformly bounded smoothed cochain projections is a
conforming family (`Feec.HilbertComplex.ConformingFamily`, the hypotheses of [AFW2010], §3.3), of
the maximal complex `HΛ` (natural boundary conditions) and, with vanishing boundary DOFs, of the
minimal complex `H̊Λ` (essential boundary conditions):

* **the lowest-order Whitney forms** (`whitneyFamily`, `whitneyFamilyMin`);
* **every admissible sequence** `S : PolySeq` of the periodic table (every `P_rΛᵏ`, `P_r⁻Λᵏ` and the
  mixed sequences, any degree `r ≥ 1`; `polyFamily`, `polyFamilyMin`);

on **the Freudenthal meshes of the cube** `Q = (0, ½)ⁿ` (`Cube.FEM`), **the image meshes of
parallelepipeds** `Ω = A · Q + b` (`Parallelepiped`) and **every shape-regular, quasi-uniform mesh
family of a domain star-shaped with respect to a ball** (`StarShaped.MeshFamily`). The smoothed
projections are those of [AFW2010], §5.4 and [ChristiansenWinther2008]; the approximation
property is the density of the finite element spaces in `L²`.

With a closed constraint (`ConformingFamily.withConstraint`) each family, and each of its windows
(`ConformingFamily.window`), is a constrained FEEC discretization, so the constrained and the
approximating FEEC theorems hold for it at every polynomial order (e.g. the Maxwell instances
`Feec.Instances.Maxwell`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (the approximation property, bounded cochain projections), §5 (the spaces `P_rΛ`,
  `P_r⁻Λ`), §5.4 (smoothed projections)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3–§5 (the periodic table of the spaces `P_rΛ`, `P_r⁻Λ`)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Filter Topology

@[expose] public noncomputable section

namespace Feec.Models

open Feec.HilbertComplex Feec.FiniteElement

/-! ### The cube -/

namespace Cube.FEM

variable (n : ℕ) [NeZero n]

/-- **The Whitney forms of the Freudenthal meshes of the cube** with the smoothed projections, a
conforming family of `HΛ(Q)`. -/
def whitneyFamily : ConformingFamily (complex n) ℕ :=
  .ofExists atTop (whitney n)
    (by obtain ⟨_, _, hE, hb, -⟩ := smoothedProjection_uniform (n := n); exact ⟨_, hE.proj, hb⟩)
    fun k y => (tendsto_infDist_submodule_iff _ y).2 fun _ hε => eventually_exists_whitney_lt k y hε

/-- **The Whitney forms with vanishing boundary DOFs**, a conforming family of `H̊Λ(Q)`. -/
def whitneyFamilyMin : ConformingFamily (complexMin n) ℕ :=
  .ofExists atTop (whitneyMin n)
    (by obtain ⟨_, _, hE, hb, -⟩ := smoothedProjection_uniform_min (n := n); exact ⟨_, hE.proj, hb⟩)
    fun k y => (tendsto_infDist_submodule_iff _ y).2 fun _ hε =>
      eventually_exists_whitneyMin_lt k y hε

/-- **The finite element complexes of an admissible sequence `S` on the Freudenthal meshes of the
cube** (every `P_rΛ`, `P_r⁻Λ` and mixed sequence) with the smoothed projections, a conforming
family of `HΛ(Q)`. -/
def polyFamily (S : PolySeq) : ConformingFamily (complex n) ℕ :=
  .ofExists atTop (poly n S)
    (by
      obtain ⟨_, _, hE, hb, -⟩ := polySmoothedProjection_uniform (n := n) S
      exact ⟨_, hE.proj, hb⟩)
    fun j q => tendsto_infDist_poly S j q

/-- **The finite element complexes of `S` with vanishing boundary DOFs**, a conforming family of
`H̊Λ(Q)`. -/
def polyFamilyMin (S : PolySeq) : ConformingFamily (complexMin n) ℕ :=
  .ofExists atTop (polyMin n S)
    (by
      obtain ⟨_, _, hE, hb, -⟩ := polySmoothedProjection_uniform_min (n := n) S
      exact ⟨_, hE.proj, hb⟩)
    fun j q => tendsto_infDist_polyMin S j q

end Cube.FEM

/-! ### Parallelepipeds -/

namespace Parallelepiped

variable {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

/-- **The Whitney forms of the image Freudenthal meshes of `Ω = A · Q + b`** with the transported
smoothed projections, a conforming family of `HΛ(Ω)`. -/
def whitneyFamily : ConformingFamily (complex A b) ℕ :=
  .ofExists atTop (whitney A hA b)
    (by obtain ⟨C, π, -, hb, -⟩ := smoothedProjection_uniform A hA b; exact ⟨C, π, hb⟩)
    fun k y => (tendsto_infDist_submodule_iff _ y).2 fun _ hε =>
      (eventually_exists_whitney_near A hA b k y hε).mono fun _ ⟨v, hv, h1, _⟩ => ⟨v, hv, h1⟩

/-- **The Whitney forms with vanishing boundary DOFs on `Ω`**, a conforming family of `H̊Λ(Ω)`. -/
def whitneyFamilyMin : ConformingFamily (complexMin A b) ℕ :=
  .ofExists atTop (whitneyMin A hA b)
    (by obtain ⟨C, π, -, hb, -⟩ := smoothedProjection_uniform_min A hA b; exact ⟨C, π, hb⟩)
    fun k y => (tendsto_infDist_submodule_iff _ y).2 fun _ hε =>
      (eventually_exists_whitneyMin_near A hA b k y hε).mono fun _ ⟨v, hv, h1, _⟩ => ⟨v, hv, h1⟩

/-- **The finite element complexes of an admissible sequence `S` on the meshes of `Ω`**, a
conforming family of `HΛ(Ω)`. -/
def polyFamily (S : PolySeq) : ConformingFamily (complex A b) ℕ :=
  .ofExists atTop (poly A hA b S)
    (by obtain ⟨C, π, -, hb, -⟩ := polySmoothedProjection_uniform A hA b S; exact ⟨C, π, hb⟩)
    fun j x => IsChainIso.tendsto_infDist_comapSub (e := pullEquiv A hA b) (poly A hA b S)
      (fun N k x => mem_poly_V_iff A hA b S N k x) (Cube.FEM.tendsto_infDist_poly S j) x

/-- **The finite element complexes of `S` with vanishing boundary DOFs on `Ω`**, a conforming
family of `H̊Λ(Ω)`. -/
def polyFamilyMin (S : PolySeq) : ConformingFamily (complexMin A b) ℕ :=
  .ofExists atTop (polyMin A hA b S)
    (by obtain ⟨C, π, -, hb, -⟩ := polySmoothedProjection_uniform_min A hA b S; exact ⟨C, π, hb⟩)
    fun j x => IsChainIso.tendsto_infDist_comapSub (e := pullEquiv A hA b) (polyMin A hA b S)
      (fun N k x => mem_polyMin_V_iff A hA b S N k x) (Cube.FEM.tendsto_infDist_polyMin S j) x

end Parallelepiped

/-! ### Domains star-shaped with respect to a ball -/

namespace StarShaped.MeshFamily

variable {n : ℕ} [NeZero n] {D : StarDomain n} (M : MeshFamily D)

/-- **The Whitney forms of a shape-regular, quasi-uniform mesh family** of a domain star-shaped
with respect to a ball, with the smoothed projections, a conforming family of `HΛ(Ω)`. -/
def whitneyFamily : ConformingFamily D.complex ℕ :=
  .ofExists atTop M.whitney
    (by
      obtain ⟨K, -, hK⟩ := M.exists_uniform_proj
      choose π hb _ using hK
      exact ⟨K, π, hb⟩)
    fun k y => (tendsto_infDist_submodule_iff _ y).2 fun _ hε =>
      M.eventually_exists_whitney_lt k y hε

/-- **The Whitney forms with vanishing boundary DOFs of the mesh family**, a conforming family of
`H̊Λ(Ω)`. -/
def whitneyFamilyMin : ConformingFamily D.complexMin ℕ :=
  .ofExists atTop M.whitneyMin
    (by
      obtain ⟨K, -, hK⟩ := M.exists_uniform_projMin
      choose π hb _ using hK
      exact ⟨K, π, hb⟩)
    fun k y => (tendsto_infDist_submodule_iff _ y).2 fun _ hε =>
      M.eventually_exists_whitneyMin_lt k y hε

/-- **The finite element complexes of an admissible sequence `S` on the mesh family**, a
conforming family of `HΛ(Ω)`. -/
def polyFamily (S : PolySeq) : ConformingFamily D.complex ℕ :=
  .ofExists atTop (M.poly S)
    (by
      obtain ⟨K, -, hK⟩ := M.exists_uniform_polyProj S
      choose π hb _ using hK
      exact ⟨K, π, hb⟩)
    fun j q => M.tendsto_infDist_poly S j q

/-- **The finite element complexes of `S` with vanishing boundary DOFs on the mesh family**, a
conforming family of `H̊Λ(Ω)`. -/
def polyFamilyMin (S : PolySeq) : ConformingFamily D.complexMin ℕ :=
  .ofExists atTop (M.polyMin S)
    (by
      obtain ⟨K, -, hK⟩ := M.exists_uniform_polyProjMin S
      choose π hb _ using hK
      exact ⟨K, π, hb⟩)
    fun j q => M.tendsto_infDist_polyMin S j q

end StarShaped.MeshFamily

end Feec.Models
