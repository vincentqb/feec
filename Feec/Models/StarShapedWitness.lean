module

public import Feec.Models.StarShaped.PolyFiniteElement
public import Feec.Models.Cube.SmoothingEstimates
public import Feec.Models.Cube.DeRhamIdentFEM
public import Feec.Models.Parallelepiped.FiniteElement

/-!
# The cube and the parallelepipeds as star-shaped domains

The hypotheses of the finite element theory on domains star-shaped with respect to a ball
(`Feec.Models.StarShaped.FiniteElement`, `Feec.Models.StarShaped.PolyFiniteElement`) are
satisfiable:

* **The cube** `Q = (0, ½)ⁿ` with its Freudenthal meshes ([Freudenthal1942]) is a `StarDomain`
  with a `MeshFamily` (`CubeWitness.starDomain`, `CubeWitness.meshFamily`: shape constants
  `max n 2`, `1`, `q = 1`), with the Poincaré inequalities ([AFW2010], Thm 3.6) `c_P = (2π)⁻¹`
  (`CubeWitness.hasPoincare`, `CubeWitness.hasPoincareMin`) and finite-dimensional harmonic
  forms; the bottom row
  `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` converges at order `h²` on `1`-forms
  (`CubeWitness.mixed_rate_lagrangeP2`).
* **Every parallelepiped** `A · Q + b` (every box) with its image Freudenthal meshes, through the
  affine images `StarDomain.map`, `MeshFamily.map` (`ParallelepipedWitness.starDomain`,
  `ParallelepipedWitness.meshFamily`, `ParallelepipedWitness.mixed_rate_lagrangeP2`).
* **Parallelepipeds, with no hypothesis**: for **every** quasi-uniform shape-regular mesh family of
  a parallelepiped (not only the image Freudenthal meshes) the Poincaré inequalities are theorems
  (`Parallelepiped.hasPoincare`, `Parallelepiped.hasPoincareMin`, from
  `Feec.Models.Parallelepiped.norm_le_of_mem_orthogonal_cycles` and `_min`), and so are the
  harmonic finite-dimensionality instances; hence the static FEEC theorem for
  `MeshFamily.polyFamily` and **`Parallelepiped.mixed_rate_poly_general`**
  (`Parallelepiped.mixed_rate_poly_general_of_polyOrderAt`, the instance
  `Parallelepiped.mixed_rate_lagrangeP2_general`: order `h²` of the bottom row on `1`-forms) hold
  unconditionally; with vanishing boundary DOFs `Parallelepiped.hasPoincareMin` discharges the
  hypothesis of the `Min` theorems. The discrete cohomology of these families is in
  `Feec.Models.ConformingFamilies`.

## References

* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.6, Thm 3.9
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (rates for smooth
  solutions)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter Topology
open scoped ContDiff

namespace Feec.Models.StarShaped

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre Feec.Models.Cube

variable {n : ℕ}

/-! ### Non-vacuity: the cube and its Freudenthal meshes -/

namespace CubeWitness

variable (n)

/-- The cube `Q = (0, ½)ⁿ` as a domain star-shaped with respect to `B((¼, …, ¼), ¼)`, with
`cl Q ⊆ B̄((¼, …, ¼), ¼)`. -/
def starDomain : StarDomain n where
  Ω := FEM.cubeDomain n
  isOpen := FEM.isOpen_cubeDomain n
  x₀ := FEM.center n
  s₀ := 1 / 4
  R := 1 / 4
  s₀_pos := by norm_num
  R_pos := by norm_num
  starBall := FEM.starBall n
  norm_sub_le := fun _ hy => FEM.norm_sub_center_le hy

variable [NeZero n]

/-- **The Freudenthal meshes of the cube** are uniformly shape regular (constants `max n 2`,
`1`) and quasi-uniform (`q = 1`), with mesh size `h_N = 1 / (2 (N + 1)) → 0`. -/
def meshFamily : MeshFamily (starDomain n) where
  mesh := FEM.mesh n
  C := ((max n 2 : ℕ) : ℝ)
  c := 1
  q := 1
  C_nonneg := Nat.cast_nonneg _
  c_pos := one_pos
  q_pos := one_pos
  domain_eq := FEM.mesh_domain n
  data := FEM.meshData
  tendsto_meshSize := by
    simp only [FEM.meshSize_mesh, FEM.hN_eq_meshSize]; exact FEM.tendsto_meshSize

omit [NeZero n] in
/-- The Poincaré inequality of `HΛ(Q)`, `c_P = (2π)⁻¹` (`FEM.norm_le_of_mem_orthogonal_cycles`). -/
theorem hasPoincare : HasPoincare (starDomain n).complex (2 * Real.pi)⁻¹ :=
  fun _ _ hij z hz => FEM.norm_le_of_mem_orthogonal_cycles hij z hz

omit [NeZero n] in
/-- The Poincaré inequality of `H̊Λ(Q)`, `c_P = (2π)⁻¹`. -/
theorem hasPoincareMin : HasPoincare (starDomain n).complexMin (2 * Real.pi)⁻¹ :=
  fun _ _ hij z hz => FEM.norm_le_of_mem_orthogonal_cycles_min hij z hz

instance (j : ℤ) : FiniteDimensional ℝ ((starDomain n).complex.harmonic j) :=
  FEM.finiteDimensional_harmonic j

instance (j : ℤ) : FiniteDimensional ℝ ((starDomain n).complexMin.harmonic j) :=
  FEM.finiteDimensional_harmonic_min j

end CubeWitness

namespace ParallelepipedWitness

variable (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

/-- The parallelepiped `Ω = A · (0, ½)ⁿ + b` as a star-shaped domain: the image of the cube
(`CubeWitness.starDomain`) under `T x = A x + b`. -/
def starDomain : StarDomain n :=
  (CubeWitness.starDomain n).map (Parallelepiped.affEquiv A hA b) (Parallelepiped.domain A b)
    (Parallelepiped.domain_eq_image A hA b)

variable [NeZero n]

/-- The image Freudenthal meshes `T(M_N)` of the parallelepiped as a mesh family. -/
def meshFamily : MeshFamily (starDomain A hA b) :=
  (CubeWitness.meshFamily n).map (Parallelepiped.affEquiv A hA b) _ _

end ParallelepipedWitness

/-! ### Parallelepipeds: every quasi-uniform shape-regular mesh family, with no hypothesis -/

namespace Parallelepiped

variable (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

/-- **The Poincaré inequality of `HΛ(Ω)` on the parallelepiped** `Ω = A · Q + b`, with
`c_P(A) = Feec.Models.Parallelepiped.poincareConst A`
(`Feec.Models.Parallelepiped.norm_le_of_mem_orthogonal_cycles`, by affine transport from the
cube). -/
theorem hasPoincare : HasPoincare (ParallelepipedWitness.starDomain A hA b).complex
    (Feec.Models.Parallelepiped.poincareConst A) := fun _ _ hij z hz =>
  (Feec.Models.Parallelepiped.norm_le_of_mem_orthogonal_cycles A hA b hij z hz).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- **The Poincaré inequality of `H̊Λ(Ω)` on the parallelepiped**
(`Feec.Models.Parallelepiped.norm_le_of_mem_orthogonal_cycles_min`). -/
theorem hasPoincareMin : HasPoincare (ParallelepipedWitness.starDomain A hA b).complexMin
    (Feec.Models.Parallelepiped.poincareConst A) := fun _ _ hij z hz =>
  (Feec.Models.Parallelepiped.norm_le_of_mem_orthogonal_cycles_min A hA b hij z hz).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

instance (j : ℤ) :
    FiniteDimensional ℝ ((ParallelepipedWitness.starDomain A hA b).complex.harmonic j) :=
  Feec.Models.Parallelepiped.finiteDimensional_harmonic A hA b j

instance (j : ℤ) :
    FiniteDimensional ℝ ((ParallelepipedWitness.starDomain A hA b).complexMin.harmonic j) :=
  Feec.Models.Parallelepiped.finiteDimensional_harmonic_min A hA b j

variable [NeZero n] (F : MeshFamily (ParallelepipedWitness.starDomain A hA b)) (S : PolySeq)

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method on every quasi-uniform
shape-regular mesh family of a parallelepiped** ([AFW2010], Thm 3.9; [Arnold2018], Ch. 7),
degreewise form, with no hypothesis beyond the regularity of the solution (`IsCsForm s`). -/
theorem mixed_rate_poly_general_of_polyOrderAt {s : ℕ} {i j k : ℤ}
    (hSi : PolyOrderAt n S s i) (hSj : PolyOrderAt n S s j)
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)}
    {σ : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace i}
    {u : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace j}
    {q : (ParallelepipedWitness.starDomain A hA b).complex.harmonic j},
    (ParallelepipedWitness.starDomain A hA b).complex.IsMixedSolution i j k f σ u q →
    ∀ {L : ℝ}, 0 ≤ L →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s i L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl i σ) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s j L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j u) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s j L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j
        ((ParallelepipedWitness.starDomain A hA b).complex.boundaryPart j
          ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j u))) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s j L
      (q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (F.poly S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).fst‖ +
      ‖u - (F.poly S N).embD j
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.fst‖ +
      ‖(q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.snd :
          (F.poly S N).V j) : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize ^ (s + 1) :=
  F.mixed_rate_poly_of_polyOrderAt S (hasPoincare A hA b) hSi hSj hij hjk

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method on every quasi-uniform
shape-regular mesh family of every parallelepiped `A · Q + b`** (not only the image Freudenthal
meshes; [AFW2010], Thm 3.9; [Arnold2018], Ch. 7), for a sequence of order `s` and solutions of
class `IsCsForm s`, with **no hypothesis**: the Poincaré inequality of `HΛ(Ω)` is discharged by
`Feec.Models.Parallelepiped.norm_le_of_mem_orthogonal_cycles` (`hasPoincare`). -/
theorem mixed_rate_poly_general {s : ℕ} (hS : PolyOrder n S s) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)}
    {σ : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace i}
    {u : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace j}
    {q : (ParallelepipedWitness.starDomain A hA b).complex.harmonic j},
    (ParallelepipedWitness.starDomain A hA b).complex.IsMixedSolution i j k f σ u q →
    ∀ {L : ℝ}, 0 ≤ L →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s i L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl i σ) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s j L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j u) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s j L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j
        ((ParallelepipedWitness.starDomain A hA b).complex.boundaryPart j
          ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j u))) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s j L
      (q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (F.poly S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).fst‖ +
      ‖u - (F.poly S N).embD j
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.fst‖ +
      ‖(q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.snd :
          (F.poly S N).V j) : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize ^ (s + 1) :=
  F.mixed_rate_poly S (hasPoincare A hA b) hS hij hjk

/-- **Second-order convergence of the bottom row `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` of Tables 5.1/6.1
for the Hodge Laplacian on `1`-forms** on every quasi-uniform shape-regular mesh family of a
parallelepiped (the problem in degree `1` only uses `P₂Λ⁰, P₂⁻Λ¹, P₁Λ²`, which contain `P₁`):
error `≤ K L h_N²` for `C³` solutions, with no hypothesis. -/
theorem mixed_rate_lagrangeP2_general :
    ∃ K : ℝ, ∀ {f : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n 1)}
    {σ : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace 0}
    {u : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace 1}
    {q : (ParallelepipedWitness.starDomain A hA b).complex.harmonic 1},
    (ParallelepipedWitness.starDomain A hA b).complex.IsMixedSolution 0 1 2 f σ u q →
    ∀ {L : ℝ}, 0 ≤ L →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm 1 0 L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl 0 σ) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm 1 1 L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl 1 u) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm 1 1 L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl 1
        ((ParallelepipedWitness.starDomain A hA b).complex.boundaryPart 1
          ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl 1 u))) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm 1 1 L
      (q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n 1)) → ∀ N : ℕ,
    ‖σ - (F.poly PolySeq.lagrangeP2 N).embD 0
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly PolySeq.lagrangeP2 N)
          (i := 0) (j := 1) (k := 2) rfl rfl f).fst‖ +
      ‖u - (F.poly PolySeq.lagrangeP2 N).embD 1
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly PolySeq.lagrangeP2 N)
          (i := 0) (j := 1) (k := 2) rfl rfl f).snd.fst‖ +
      ‖(q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n 1)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution (F.poly PolySeq.lagrangeP2 N)
          (i := 0) (j := 1) (k := 2) rfl rfl f).snd.snd : (F.poly PolySeq.lagrangeP2 N).V 1) :
            L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n 1))‖ ≤
      K * L * (F.mesh N).meshSize ^ (1 + 1) :=
  F.mixed_rate_poly_of_polyOrderAt PolySeq.lagrangeP2 (hasPoincare A hA b)
    lagrangeP2_polyOrderAt_zero lagrangeP2_polyOrderAt_one rfl rfl

end Parallelepiped

/-! ### Non-vacuity: the cube and the parallelepipeds -/

namespace CubeWitness

variable (n) [NeZero n]

/-- **Second-order convergence of the bottom row `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` on the Freudenthal
meshes of the cube, as a mesh family of a star-shaped domain** (`CubeWitness.meshFamily`): the
star-shaped theory instantiated, with the Poincaré inequality `CubeWitness.hasPoincare`. -/
theorem mixed_rate_lagrangeP2 :
    ∃ K : ℝ, ∀ {f : L2F ℝ (starDomain n).Ω (formIdx n 1)}
    {σ : (starDomain n).complex.domainSpace 0} {u : (starDomain n).complex.domainSpace 1}
    {q : (starDomain n).complex.harmonic 1},
    (starDomain n).complex.IsMixedSolution 0 1 2 f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    (starDomain n).IsCsForm 1 0 L ((starDomain n).complex.domainIncl 0 σ) →
    (starDomain n).IsCsForm 1 1 L ((starDomain n).complex.domainIncl 1 u) →
    (starDomain n).IsCsForm 1 1 L ((starDomain n).complex.domainIncl 1
      ((starDomain n).complex.boundaryPart 1 ((starDomain n).complex.domainIncl 1 u))) →
    (starDomain n).IsCsForm 1 1 L (q : L2F ℝ (starDomain n).Ω (formIdx n 1)) → ∀ N : ℕ,
    ‖σ - ((meshFamily n).poly PolySeq.lagrangeP2 N).embD 0
        (Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily n).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl f).fst‖ +
      ‖u - ((meshFamily n).poly PolySeq.lagrangeP2 N).embD 1
        (Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily n).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl
            f).snd.fst‖ +
      ‖(q : L2F ℝ (starDomain n).Ω (formIdx n 1)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily n).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl
            f).snd.snd : ((meshFamily n).poly PolySeq.lagrangeP2 N).V 1) :
              L2F ℝ (starDomain n).Ω (formIdx n 1))‖ ≤
      K * L * ((meshFamily n).mesh N).meshSize ^ (1 + 1) :=
  (meshFamily n).mixed_rate_poly_of_polyOrderAt PolySeq.lagrangeP2 (hasPoincare n)
    lagrangeP2_polyOrderAt_zero lagrangeP2_polyOrderAt_one rfl rfl

end CubeWitness

namespace ParallelepipedWitness

variable (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ) [NeZero n]

/-- **Second-order convergence of the bottom row on the image Freudenthal meshes of a
parallelepiped**, as an instance of `Parallelepiped.mixed_rate_lagrangeP2_general` for the mesh
family `ParallelepipedWitness.meshFamily`. -/
theorem mixed_rate_lagrangeP2 :
    ∃ K : ℝ, ∀ {f : L2F ℝ (starDomain A hA b).Ω (formIdx n 1)}
    {σ : (starDomain A hA b).complex.domainSpace 0}
    {u : (starDomain A hA b).complex.domainSpace 1}
    {q : (starDomain A hA b).complex.harmonic 1},
    (starDomain A hA b).complex.IsMixedSolution 0 1 2 f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    (starDomain A hA b).IsCsForm 1 0 L ((starDomain A hA b).complex.domainIncl 0 σ) →
    (starDomain A hA b).IsCsForm 1 1 L ((starDomain A hA b).complex.domainIncl 1 u) →
    (starDomain A hA b).IsCsForm 1 1 L ((starDomain A hA b).complex.domainIncl 1
      ((starDomain A hA b).complex.boundaryPart 1
        ((starDomain A hA b).complex.domainIncl 1 u))) →
    (starDomain A hA b).IsCsForm 1 1 L
      (q : L2F ℝ (starDomain A hA b).Ω (formIdx n 1)) → ∀ N : ℕ,
    ‖σ - ((meshFamily A hA b).poly PolySeq.lagrangeP2 N).embD 0
        (Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily A hA b).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl
            f).fst‖ +
      ‖u - ((meshFamily A hA b).poly PolySeq.lagrangeP2 N).embD 1
        (Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily A hA b).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl
            f).snd.fst‖ +
      ‖(q : L2F ℝ (starDomain A hA b).Ω (formIdx n 1)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily A hA b).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl
            f).snd.snd : ((meshFamily A hA b).poly PolySeq.lagrangeP2 N).V 1) :
              L2F ℝ (starDomain A hA b).Ω (formIdx n 1))‖ ≤
      K * L * ((meshFamily A hA b).mesh N).meshSize ^ (1 + 1) :=
  Parallelepiped.mixed_rate_lagrangeP2_general A hA b (meshFamily A hA b)

end ParallelepipedWitness

end Feec.Models.StarShaped
