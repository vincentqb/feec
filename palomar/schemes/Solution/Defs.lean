module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but the theorems
`FEEC.weakSymmetry`, `FEEC.weakSymmetry_cube` and `FEEC.weakSymmetry_cube_nonvacuous`), compiled
against Mathlib alone so that their elaborated values are those of the challenge. The solution
imports this module and the bridges to `Feec`, and proves the theorems (`Solution.lean`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Mixed finite element methods for linear elasticity with weakly imposed symmetry*][AFW2007]
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3, §5, §11
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3, §4, §5.5
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [F. Brezzi, *On the existence, uniqueness and approximation of saddle-point problems arising from Lagrangian multipliers*][Brezzi1974]
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], Lemma 2.4
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6, 7
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 5 ((5.1)–(5.6), Props 5.3, 5.4, 5.7, Thm 5.5, Table 5.1), Ch. 6 ((6.2)–(6.5), Prop 6.2,
  Table 6.1)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Filter Topology Set LinearPMap MeasureTheory

@[expose] public noncomputable section

universe u

namespace FEEC

/-! ### Differential forms on `ℝⁿ` and the minimal `L²` de Rham complex (from `palomar/fem`) -/

variable {n : ℕ}

/-- The index set of the coefficients of a `k`-form on `ℝⁿ`: the `k`-subsets
`s = {s₁ < ⋯ < s_k}` of `Fin n`, `s` indexing `dx_{s₁} ∧ ⋯ ∧ dx_{s_k}` (empty unless
`0 ≤ k ≤ n`). -/
abbrev FormIdx (n : ℕ) (k : ℤ) : Type := {s : Finset (Fin n) // (s.card : ℤ) = k}

/-- `L²(Ω; Λᵏ)`: the square-integrable `k`-forms on `Ω ⊆ ℝⁿ` (Lebesgue measure), the `ℓ²` sum
of a copy of `L²(Ω)` for each coefficient. -/
abbrev L2Form (Ω : Set (Fin n → ℝ)) (k : ℤ) : Type :=
  PiLp 2 fun _ : FormIdx n k => Lp ℝ 2 (volume.restrict Ω)

/-- A **form field** on `ℝⁿ`: at each point, a coefficient for every subset `s` of `Fin n` (the
coefficient of `dx_s`); it is a `k`-form when the coefficients off the `k`-subsets vanish. -/
abbrev FormField (n : ℕ) : Type := (Fin n → ℝ) → Finset (Fin n) → ℝ

/-- The sign `ε(j, s) = (-1)^{#{l ∈ s | l < j}}` of moving `dx_j` to its place in `dx_s`. -/
def sgn (j : Fin n) (s : Finset (Fin n)) : ℝ := (-1) ^ (s.filter fun l => l < j).card

/-- The partial derivative `∂_j f(x)`. -/
def partialDeriv (j : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single j 1)

/-- The **exterior derivative** of a form field, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`. -/
def extDeriv (w : FormField n) : FormField n :=
  fun x s => ∑ j ∈ s, sgn j s * partialDeriv j (fun y => w y (s.erase j)) x

/-- `f` is a **test function** on `Ω`: smooth, with compact support contained in `Ω`. -/
def IsTestFn (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω

/-- The graph `{(φ, dφ)}` of the exterior derivative on the test `k`-forms `φ ∈ C_c^∞(Ω; Λᵏ)`
(every coefficient a test function), as a subspace of `L²(Ω; Λᵏ) × L²(Ω; Λᵏ⁺¹)`. -/
def testGraph (Ω : Set (Fin n → ℝ)) (k : ℤ) : Submodule ℝ (L2Form Ω k × L2Form Ω (k + 1)) :=
  Submodule.span ℝ {p | ∃ φ : FormField n, (∀ s, IsTestFn Ω fun x => φ x s) ∧
    (∀ s : FormIdx n k, ⇑(p.1 s) =ᵐ[volume.restrict Ω] fun x => φ x s.1) ∧
    ∀ t : FormIdx n (k + 1), ⇑(p.2 t) =ᵐ[volume.restrict Ω] fun x => extDeriv φ x t.1}

/-- The **minimal exterior derivative** `d̊ : L²(Ω; Λᵏ) → L²(Ω; Λᵏ⁺¹)`, the closure of `d` on
test forms (the closure of the graph is a graph: `d` is closable, its formal adjoint being
densely defined): its domain is `H̊Λᵏ(Ω)` (for Lipschitz `Ω`, the forms of `HΛᵏ(Ω)` with vanishing
tangential trace) ([AFW2010], §4; [Arnold2018], Ch. 6). -/
def dMin (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Form Ω k →ₗ.[ℝ] L2Form Ω (k + 1) :=
  (testGraph Ω k).topologicalClosure.toLinearPMap

/-! ### Polynomial differential forms ([AFW2006], §3) -/

/-- **Polynomial differential forms** on `ℝⁿ` in coordinates: a polynomial coefficient `ω_s` for
every subset `s` of `Fin n`, the form `Σ_s ω_s dx_s`. -/
abbrev PolyForm (n : ℕ) : Type := Finset (Fin n) → MvPolynomial (Fin n) ℝ

/-- `P_rΛᵏ`: the polynomial `k`-forms (`ω_s = 0` unless `#s = k`) with coefficients of degree at
most `r`. -/
def polyForm (r k : ℕ) : Submodule ℝ (PolyForm n) :=
  Submodule.pi Set.univ fun s =>
    if s.card = k then MvPolynomial.restrictTotalDegree (Fin n) ℝ r else ⊥

/-- `H_rΛᵏ`: the polynomial `k`-forms with coefficients homogeneous of degree `r`. -/
def homForm (r k : ℕ) : Submodule ℝ (PolyForm n) :=
  Submodule.pi Set.univ fun s =>
    if s.card = k then MvPolynomial.homogeneousSubmodule (Fin n) ℝ r else ⊥

/-- The **Koszul differential** `κ`, the contraction with the position vector field `x`:
`(κω)_s = Σ_{j ∉ s} ε(j, s) x_j ω_{s ∪ j}`. -/
def koszul : PolyForm n →ₗ[ℝ] PolyForm n :=
  LinearMap.pi fun s => ∑ j ∈ sᶜ,
    sgn j s • (LinearMap.mulLeft ℝ (MvPolynomial.X j) ∘ₗ LinearMap.proj (insert j s))

/-- `P_r⁻Λᵏ = P_{r-1}Λᵏ + κ H_{r-1}Λ^{k+1}`, the trimmed polynomial `k`-forms (`r ≥ 1`), and
`P_0⁻Λᵏ = 0` ([AFW2006], §3.3). -/
def polyFormMinus : ℕ → ℕ → Submodule ℝ (PolyForm n)
  | 0, _ => ⊥
  | r + 1, k => polyForm r k ⊔ (homForm r (k + 1)).map koszul

/-- The **evaluation** of a polynomial form: the form field `x ↦ (ω_s(x))_s`. -/
def evalForm : PolyForm n →ₗ[ℝ] FormField n :=
  LinearMap.pi fun x => LinearMap.pi fun s =>
    (MvPolynomial.aeval x).toLinearMap ∘ₗ LinearMap.proj s

/-- **An admissible sequence** of polynomial families ([AFW2006], §5; [AFW2010], §5.2): in every
form degree `k` the full space `P_{r_k}Λᵏ` (`full k = true`) or the trimmed space `P_{r_k}⁻Λᵏ`,
`r_k ≥ 1`, followed in degree `k + 1` by `P_{r_k}⁻Λᵏ⁺¹` or by `P_{r_k - 1}Λᵏ⁺¹`. (The piecewise
constants `P_0Λⁿ` are represented by the equal space `P_1⁻Λⁿ`; the spaces of degree `k > n`
are `0`.) -/
structure PolySeq where
  /-- `P_{r_k}Λᵏ` (`true`) or `P_{r_k}⁻Λᵏ` (`false`) in degree `k` -/
  full : ℕ → Bool
  /-- the polynomial degree `r_k` -/
  deg : ℕ → ℕ
  one_le_deg : ∀ k, 1 ≤ deg k
  transition : ∀ k, (full (k + 1) = false ∧ deg (k + 1) = deg k) ∨
    (full (k + 1) = true ∧ deg (k + 1) + 1 = deg k)

namespace PolySeq

variable (S : PolySeq)

/-- The space `P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` of form fields on `ℝⁿ` of the sequence in degree `k`. -/
def space (n k : ℕ) : Submodule ℝ (FormField n) :=
  (if S.full k then polyForm (n := n) (S.deg k) k else polyFormMinus (S.deg k) k).map evalForm

/-- `S` **reproduces polynomial forms of degree `s`** in the form degrees `j` and `j + 1`:
`P_sΛʲ ⊆ S_j` and `P_sΛʲ⁺¹ ⊆ S_{j+1}` (vacuous for `j < 0`). -/
def PolyOrderAt (n s : ℕ) (j : ℤ) : Prop :=
  ∀ k : ℕ, (k : ℤ) = j → (polyForm (n := n) s k).map evalForm ≤ S.space n k ∧
    (polyForm (n := n) s (k + 1)).map evalForm ≤ S.space n (k + 1)

end PolySeq

/-! ### Simplicial meshes -/

/-- The vertex set `{v₀, …, v_k}` of a simplex. -/
def vertexSet {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) : Finset (Fin n → ℝ) :=
  Finset.univ.image T.points

/-- A **conforming simplicial mesh** of `closure domain ⊆ ℝⁿ`: a finite set of `n`-simplices
whose closed simplices cover `closure domain`, have pairwise disjoint interiors, and meet face to
face (the intersection of two closed simplices is the convex hull of their common vertices). -/
structure SimplicialMesh (n : ℕ) where
  /-- the `n`-simplices -/
  simplices : Finset (Affine.Simplex ℝ (Fin n → ℝ) n)
  /-- the meshed set `Ω`; the mesh covers its closure -/
  domain : Set (Fin n → ℝ)
  biUnion_closedInterior : ⋃ T ∈ simplices, T.closedInterior = closure domain
  pairwise_disjoint_interior :
    (simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)).Pairwise fun T T' =>
      Disjoint (interior T.closedInterior) (interior T'.closedInterior)
  inter_closedInterior : ∀ T ∈ simplices, ∀ T' ∈ simplices,
    T.closedInterior ∩ T'.closedInterior =
      convexHull ℝ ((vertexSet T : Set (Fin n → ℝ)) ∩ vertexSet T')

/-- `h_T`: the diameter of the closed simplex `T`. -/
def diam {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) : ℝ := Metric.diam T.closedInterior

/-- The **mesh size** `h = max_T h_T`. -/
def meshSize (M : SimplicialMesh n) : ℝ :=
  ⨆ T : M.simplices, diam (T : Affine.Simplex ℝ (Fin n → ℝ) n)

/-- The mesh is **shape regular** with constant `σ` ([Ciarlet2002], §3.1): every simplex `T`
contains a ball `B(x, ρ)` with `h_T ≤ σ ρ`, that is `h_T / ρ_T ≤ σ` for the inradius `ρ_T` (the
largest radius of a ball in `T`). Balls and `h_T` are those of the sup norm (Conventions). -/
def IsShapeRegular (M : SimplicialMesh n) (σ : ℝ) : Prop :=
  ∀ T ∈ M.simplices, ∃ x ρ, 0 < ρ ∧ Metric.ball x ρ ⊆ T.closedInterior ∧ diam T ≤ σ * ρ

/-- The mesh is **quasi-uniform** with constant `q`: `q h ≤ h_T` for every simplex. -/
def IsQuasiUniform (M : SimplicialMesh n) (q : ℝ) : Prop :=
  ∀ T ∈ M.simplices, q * meshSize M ≤ diam T

/-- `M_N` is a **shape-regular, quasi-uniform family of meshes of `Ω`** with mesh size `h_N → 0`:
meshes of `Ω`, shape regular and quasi-uniform with constants independent of `N`. -/
def IsMeshFamily (Ω : Set (Fin n → ℝ)) (M : ℕ → SimplicialMesh n) : Prop :=
  (∀ N, (M N).domain = Ω) ∧
    (∃ σ q : ℝ, 0 < q ∧ ∀ N, IsShapeRegular (M N) σ ∧ IsQuasiUniform (M N) q) ∧
    (∀ N, 0 < meshSize (M N)) ∧ Tendsto (fun N => meshSize (M N)) atTop (𝓝 0)


/-! ### The finite element spaces -/

/-- The value `α(v₁, …, v_k) = Σ_{#s = k} α_s det (v_l(s_i))_{i,l}` of the `k`-covector `α` on
the vectors `v₁, …, v_k`. -/
def covEval {k : ℕ} (α : Finset (Fin n) → ℝ) (v : Fin k → Fin n → ℝ) : ℝ :=
  ∑ s : Finset (Fin n), if h : s.card = k then
    α s * (Matrix.of fun i l => v l (s.orderEmbOfFin h i)).det else 0

/-- The `k`-covectors `α`, `β` have the **same tangential trace** on the face spanned by the
points `g`: they agree on all `k`-tuples of vectors tangent to the face. -/
def TraceEq (g : Finset (Fin n → ℝ)) (k : ℕ) (α β : Finset (Fin n) → ℝ) : Prop :=
  ∀ v : Fin k → Fin n → ℝ, (∀ l, v l ∈ vectorSpan ℝ (g : Set (Fin n → ℝ))) →
    covEval α v = covEval β v

/-- `p = (p_T)_T` are **finite element pieces** of `u ∈ L²(Ω; Λᵏ)` on the mesh `M` for the
sequence `S`: on every simplex `T`, `u` is (almost everywhere) the polynomial form `p_T ∈ S_k`,
and the tangential traces of `p_T` and `p_{T'}` agree on the common face of any two simplices. -/
def IsFemPieces (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (S : PolySeq) (k : ℤ)
    (u : L2Form Ω k) (p : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n) : Prop :=
  (∀ T ∈ M.simplices, p T ∈ S.space n k.toNat) ∧
    (∀ T ∈ M.simplices, ∀ s : FormIdx n k,
      ⇑(u s) =ᵐ[volume.restrict (Ω ∩ T.closedInterior)] fun x => p T x s.1) ∧
    ∀ T ∈ M.simplices, ∀ T' ∈ M.simplices,
      ∀ x ∈ convexHull ℝ ((vertexSet T ∩ vertexSet T' : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)),
        TraceEq (vertexSet T ∩ vertexSet T') k.toNat (p T x) (p T' x)

/-- **The finite element space with vanishing boundary traces** `S̊_k(M)`: the forms of
`S_k(M)` whose tangential traces vanish on the boundary facets (the facets of a single simplex of
the mesh). -/
def femSpaceMin (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (S : PolySeq) (k : ℤ) :
    Set (L2Form Ω k) :=
  {u | ∃ p, IsFemPieces Ω M S k u p ∧ ∀ T ∈ M.simplices, ∀ F ⊆ vertexSet T, F.card = n →
    (∀ T' ∈ M.simplices, F ⊆ vertexSet T' → T' = T) →
      ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), TraceEq F k.toNat (p T x) 0}

/-- The cube `(0, ½)ⁿ` (half a period of the torus `ℝⁿ/ℤⁿ` of the proof's Fourier series). -/
def cube (n : ℕ) : Set (Fin n → ℝ) := univ.pi fun _ => Ioo 0 (1 / 2)


/-! ### Vector-valued forms and the connecting maps -/

/-- `L²(Ω; Λᵏ ⊗ ℝⁿ)`: the vectors `v = (v₀, …, v_{n-1})` of `k`-forms of `L²(Ω; Λᵏ)`, an `ℓ²`
sum. -/
abbrev L2Vec (Ω : Set (Fin n → ℝ)) (k : ℤ) : Type := PiLp 2 fun _ : Fin n => L2Form Ω k

/-- The operator `T` acting componentwise on vectors, with domain `D(T)ⁿ`. -/
def vecOp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (T : E →ₗ.[ℝ] F) :
    PiLp 2 (fun _ : Fin n => E) →ₗ.[ℝ] PiLp 2 (fun _ : Fin n => F) where
  domain :=
    { carrier := {v | ∀ a, v a ∈ T.domain}
      add_mem' := fun hv hw a => T.domain.add_mem (hv a) (hw a)
      zero_mem' := fun _ => T.domain.zero_mem
      smul_mem' := fun c _ hv a => T.domain.smul_mem c (hv a) }
  toFun :=
    { toFun := fun v => WithLp.toLp 2 fun a => T ⟨(v : PiLp 2 fun _ : Fin n => E) a, v.2 a⟩
      map_add' := fun v w => PiLp.ext fun a => T.map_add ⟨_, v.2 a⟩ ⟨_, w.2 a⟩
      map_smul' := fun c v => PiLp.ext fun a => T.map_smul c ⟨_, v.2 a⟩ }

/-- **The connecting map** `S v = Σₐ dxₐ ∧ vₐ : L²(Ω; Λᵏ ⊗ ℝⁿ) → L²(Ω; Λᵏ⁺¹)`,
`(S v)_s = Σ_{a ∈ s} ε(a, s) (vₐ)_{s ∖ a}`. On vector proxies, `S` is the identity `S⁰ = I` on
vector `0`-forms (`(S v)_{a} = vₐ`), and on vector `1`-forms `vₐ = Σ_b u_{ab} dx_b`,
`(S v)_{ab} = u_{ab} - u_{ba}`, i.e. `S¹ = 2 vskw` ([QuennevilleBelair2015], §5.3; [AFW2007]). -/
def wedge (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Vec Ω k →L[ℝ] L2Form Ω (k + 1) :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : FormIdx n (k + 1) =>
      Lp ℝ 2 (volume.restrict Ω)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun s => ∑ a : Fin n, if h : a ∈ s.1 then sgn a s.1 •
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : FormIdx n k => Lp ℝ 2 (volume.restrict Ω))
          ⟨s.1.erase a, by
            rw [Finset.card_erase_of_mem h, Nat.cast_sub (Finset.card_pos.2 ⟨a, h⟩), s.2]
            ring⟩) ∘L PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => L2Form Ω k) a) else 0

/-! ### BGG data with weak symmetry and their discretization -/

/-- **BGG data**: two segments `W⁰ → W¹ → W²` and `W̃⁰ → W̃¹ → W̃²` of complexes of densely
defined operators `d`, `d̃` between Hilbert spaces (unbounded, `LinearPMap`s; their domains
`V = D(d)` carry the inner product of `W`), with bounded connecting maps `S⁰ : W̃⁰ → W¹`,
`S¹ : W̃¹ → W²`. The complex and anticommutation laws are `WeakSymmetryData.IsBGG`. -/
structure WeakSymmetryData (W0 W1 W2 Wt0 Wt1 Wt2 : Type*) [NormedAddCommGroup W0]
    [InnerProductSpace ℝ W0] [NormedAddCommGroup W1] [InnerProductSpace ℝ W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0]
    [InnerProductSpace ℝ Wt0] [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1]
    [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2] where
  /-- the top row -/
  d0 : W0 →ₗ.[ℝ] W1
  d1 : W1 →ₗ.[ℝ] W2
  /-- the bottom row -/
  dt0 : Wt0 →ₗ.[ℝ] Wt1
  dt1 : Wt1 →ₗ.[ℝ] Wt2
  /-- the connecting maps -/
  S0 : Wt0 →L[ℝ] W1
  S1 : Wt1 →L[ℝ] W2

namespace WeakSymmetryData

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2)

/-- The rows are complexes, `R(d⁰) ⊆ D(d¹)`, `d¹d⁰ = 0` and `R(d̃⁰) ⊆ D(d̃¹)`, `d̃¹d̃⁰ = 0`, and
`S` anticommutes with them: `S⁰D(d̃⁰) ⊆ D(d¹)` and `d¹S⁰ = -S¹d̃⁰` (a morphism `Ṽ → V[1]`). -/
def IsBGG : Prop :=
  (∀ x : D.d0.domain, ∃ h : D.d0 x ∈ D.d1.domain, D.d1 ⟨_, h⟩ = 0) ∧
    (∀ x : D.dt0.domain, ∃ h : D.dt0 x ∈ D.dt1.domain, D.dt1 ⟨_, h⟩ = 0) ∧
    ∀ ψ : D.dt0.domain, ∃ h : D.S0 ψ ∈ D.d1.domain, D.d1 ⟨_, h⟩ = -D.S1 (D.dt0 ψ)

/-- **The continuous hypotheses with constant `C`** ([QuennevilleBelair2015], §5.1, Prop 5.3):
Poincaré inequalities on `V⁰` and `Ṽ⁰` (so `d⁰`, `d̃⁰` are injective with closed range), exactness
of the top row at `V¹`, the Hodge decomposition `v = d̃ψ + w`, `‖w‖ ≤ C ‖d̃v‖`, on `Ṽ¹` (exactness
of the bottom row at `Ṽ¹` and the Poincaré inequality), the **regular decomposition** `d¹V¹ =
d¹S⁰Ṽ⁰` with the bound `‖d̃φ‖ ≤ C ‖d¹x‖` ([Hiptmair2002], Lemma 2.4, in the application), and
`‖S⁰‖, ‖S¹‖ ≤ C`. -/
structure IsStable (C : ℝ) : Prop where
  poincare : ∀ σ : D.d0.domain, ‖(σ : W0)‖ ≤ C * ‖D.d0 σ‖
  poincare_t : ∀ φ : D.dt0.domain, ‖(φ : Wt0)‖ ≤ C * ‖D.dt0 φ‖
  exact : ∀ μ : D.d1.domain, D.d1 μ = 0 → ∃ ρ : D.d0.domain, D.d0 ρ = μ
  hodge_t : ∀ v : D.dt1.domain, ∃ (ψ : D.dt0.domain) (w : D.dt1.domain),
    (v : Wt1) = D.dt0 ψ + w ∧ ‖(w : Wt1)‖ ≤ C * ‖D.dt1 v‖
  regular : ∀ x : D.d1.domain, ∃ (φ : D.dt0.domain) (h : D.S0 φ ∈ D.d1.domain),
    D.d1 ⟨_, h⟩ = D.d1 x ∧ ‖D.dt0 φ‖ ≤ C * ‖D.d1 x‖
  norm_S0 : ‖D.S0‖ ≤ C
  norm_S1 : ‖D.S1‖ ≤ C

/-- `(σ, φ, u)` with the multiplier `λ ∈ W¹` solves **the mixed problem (5.3)** with datum `F`
([QuennevilleBelair2015], (5.3), with an `L²` multiplier): `⟪σ, τ⟫ - ⟪u, d̃ψ⟫ - ⟪λ, dτ - S⁰ψ⟫ = 0`,
`⟪d̃φ, v⟫ + ⟪S¹u, S¹v⟫ + ⟪d̃u, d̃v⟫ = F v` for all `τ ∈ V⁰`, `ψ ∈ Ṽ⁰`, `v ∈ Ṽ¹`, and `dσ = S⁰φ`. -/
def IsSolution (F : D.dt1.domain →ₗ[ℝ] ℝ) (σ : D.d0.domain) (φ : D.dt0.domain)
    (u : D.dt1.domain) (lam : W1) : Prop :=
  (∀ (τ : D.d0.domain) (ψ : D.dt0.domain),
      ⟪(σ : W0), τ⟫_ℝ - ⟪(u : Wt1), D.dt0 ψ⟫_ℝ - ⟪lam, D.d0 τ - D.S0 ψ⟫_ℝ = 0) ∧
    (∀ v : D.dt1.domain,
      ⟪D.dt0 φ, v⟫_ℝ + ⟪D.S1 u, D.S1 v⟫_ℝ + ⟪D.dt1 u, D.dt1 v⟫_ℝ = F v) ∧
    D.d0 σ = D.S0 φ

/-- **A discretization** of `D` ([QuennevilleBelair2015], §5.2): finite-dimensional subspaces of
the domains forming subcomplexes of both rows, with bounded cochain projections `π : W → W` onto
them (identity on the subspaces, `d π = π d` on the domains). The method (5.6) couples the rows by
`S⁰ₕ = π¹S⁰`, `S¹ₕ = π²S¹`. -/
structure Discretization where
  /-- the finite element spaces -/
  V0 : Submodule ℝ W0
  V1 : Submodule ℝ W1
  V2 : Submodule ℝ W2
  Vt0 : Submodule ℝ Wt0
  Vt1 : Submodule ℝ Wt1
  Vt2 : Submodule ℝ Wt2
  [fd0 : FiniteDimensional ℝ V0]
  [fd1 : FiniteDimensional ℝ V1]
  [fd2 : FiniteDimensional ℝ V2]
  [fdt0 : FiniteDimensional ℝ Vt0]
  [fdt1 : FiniteDimensional ℝ Vt1]
  [fdt2 : FiniteDimensional ℝ Vt2]
  le0 : V0 ≤ D.d0.domain
  le1 : V1 ≤ D.d1.domain
  let0 : Vt0 ≤ D.dt0.domain
  let1 : Vt1 ≤ D.dt1.domain
  d0_mem : ∀ x : D.d0.domain, (x : W0) ∈ V0 → D.d0 x ∈ V1
  d1_mem : ∀ x : D.d1.domain, (x : W1) ∈ V1 → D.d1 x ∈ V2
  dt0_mem : ∀ x : D.dt0.domain, (x : Wt0) ∈ Vt0 → D.dt0 x ∈ Vt1
  dt1_mem : ∀ x : D.dt1.domain, (x : Wt1) ∈ Vt1 → D.dt1 x ∈ Vt2
  /-- the cochain projections -/
  π0 : W0 →L[ℝ] W0
  π1 : W1 →L[ℝ] W1
  π2 : W2 →L[ℝ] W2
  πt0 : Wt0 →L[ℝ] Wt0
  πt1 : Wt1 →L[ℝ] Wt1
  πt2 : Wt2 →L[ℝ] Wt2
  π0_mem : ∀ x, π0 x ∈ V0
  π1_mem : ∀ x, π1 x ∈ V1
  π2_mem : ∀ x, π2 x ∈ V2
  πt0_mem : ∀ x, πt0 x ∈ Vt0
  πt1_mem : ∀ x, πt1 x ∈ Vt1
  πt2_mem : ∀ x, πt2 x ∈ Vt2
  π0_id : ∀ x ∈ V0, π0 x = x
  π1_id : ∀ x ∈ V1, π1 x = x
  π2_id : ∀ x ∈ V2, π2 x = x
  πt0_id : ∀ x ∈ Vt0, πt0 x = x
  πt1_id : ∀ x ∈ Vt1, πt1 x = x
  πt2_id : ∀ x ∈ Vt2, πt2 x = x
  comm0 : ∀ x : D.d0.domain, D.d0 ⟨π0 x, le0 (π0_mem x)⟩ = π1 (D.d0 x)
  comm1 : ∀ x : D.d1.domain, D.d1 ⟨π1 x, le1 (π1_mem x)⟩ = π2 (D.d1 x)
  commt0 : ∀ x : D.dt0.domain, D.dt0 ⟨πt0 x, let0 (πt0_mem x)⟩ = πt1 (D.dt0 x)
  commt1 : ∀ x : D.dt1.domain, D.dt1 ⟨πt1 x, let1 (πt1_mem x)⟩ = πt2 (D.dt1 x)

namespace Discretization

variable {D} (Q : D.Discretization)

/-- The projections are **bounded by `C`**: `‖π‖ ≤ C`, `‖π̃‖ ≤ C` in every degree. -/
def IsBounded (C : ℝ) : Prop :=
  ‖Q.π0‖ ≤ C ∧ ‖Q.π1‖ ≤ C ∧ ‖Q.π2‖ ≤ C ∧ ‖Q.πt0‖ ≤ C ∧ ‖Q.πt1‖ ≤ C ∧ ‖Q.πt2‖ ≤ C

/-- **The compatibility condition (5.4)** `π¹S⁰π̃⁰ = π¹S⁰` ([QuennevilleBelair2015], (5.4)). -/
def Compatible : Prop := ∀ ψ, Q.π1 (D.S0 (Q.πt0 ψ)) = Q.π1 (D.S0 ψ)

/-- **Consistency of `Sₕ` at the order `h`** with constant `C` (cf. [QuennevilleBelair2015],
Prop 5.9): `‖(S⁰ - S⁰ₕ)ψ‖ ≤ C h ‖d̃ψ‖` on `Ṽₕ⁰`, and every `d̃v`, `v ∈ Ṽₕ¹`, has a **regular
potential** `w`, `d̃w = d̃v`, `‖w‖ ≤ C ‖d̃v‖`, on which `π̃¹` and `S¹ₕ` are accurate,
`‖(1 - π̃¹)w‖, ‖(S¹ - S¹ₕ)w‖ ≤ C h ‖d̃v‖`. -/
def IsConsistent (C h : ℝ) : Prop :=
  (∀ ψ : D.dt0.domain, (ψ : Wt0) ∈ Q.Vt0 → ‖D.S0 ψ - Q.π1 (D.S0 ψ)‖ ≤ C * h * ‖D.dt0 ψ‖) ∧
    ∀ v : D.dt1.domain, (v : Wt1) ∈ Q.Vt1 → ∃ w : D.dt1.domain, D.dt1 w = D.dt1 v ∧
      ‖(w : Wt1)‖ ≤ C * ‖D.dt1 v‖ ∧ ‖(w : Wt1) - Q.πt1 w‖ ≤ C * h * ‖D.dt1 v‖ ∧
      ‖D.S1 w - Q.π2 (D.S1 w)‖ ≤ C * h * ‖D.dt1 v‖

/-- `(σₕ, φₕ, uₕ, λₕ) ∈ Vₕ⁰ × Ṽₕ⁰ × Ṽₕ¹ × Vₕ¹` solves **the discrete problem (5.6)** with datum
`F`: (5.3) on the discrete spaces with `S⁰ₕ = π¹S⁰`, `S¹ₕ = π²S¹` in place of `S⁰`, `S¹`. -/
def IsDiscreteSolution (F : D.dt1.domain →ₗ[ℝ] ℝ) (σ : D.d0.domain) (φ : D.dt0.domain)
    (u : D.dt1.domain) (lam : W1) : Prop :=
  (σ : W0) ∈ Q.V0 ∧ (φ : Wt0) ∈ Q.Vt0 ∧ (u : Wt1) ∈ Q.Vt1 ∧ lam ∈ Q.V1 ∧
    (∀ (τ : D.d0.domain) (ψ : D.dt0.domain), (τ : W0) ∈ Q.V0 → (ψ : Wt0) ∈ Q.Vt0 →
      ⟪(σ : W0), τ⟫_ℝ - ⟪(u : Wt1), D.dt0 ψ⟫_ℝ - ⟪lam, D.d0 τ - Q.π1 (D.S0 ψ)⟫_ℝ = 0) ∧
    (∀ v : D.dt1.domain, (v : Wt1) ∈ Q.Vt1 → ⟪D.dt0 φ, v⟫_ℝ +
      ⟪Q.π2 (D.S1 u), Q.π2 (D.S1 v)⟫_ℝ + ⟪D.dt1 u, D.dt1 v⟫_ℝ = F v) ∧
    D.d0 σ = Q.π1 (D.S0 φ)

/-- The squared **error** in the graph norms of `V⁰`, `Ṽ⁰` and in `‖w‖² + ‖S¹ₕw‖² + ‖d̃w‖²` on
`Ṽ¹`. -/
def errorSq (σ σh : D.d0.domain) (φ φh : D.dt0.domain) (u uh : D.dt1.domain) : ℝ :=
  ‖((σ - σh : D.d0.domain) : W0)‖ ^ 2 + ‖D.d0 (σ - σh)‖ ^ 2 +
    ‖((φ - φh : D.dt0.domain) : Wt0)‖ ^ 2 + ‖D.dt0 (φ - φh)‖ ^ 2 +
    ‖((u - uh : D.dt1.domain) : Wt1)‖ ^ 2 + ‖Q.π2 (D.S1 (u - uh))‖ ^ 2 + ‖D.dt1 (u - uh)‖ ^ 2

/-- The squared **projection error** of `(σ, φ, u)` in the norms of `errorSq` (with `d π = π d`). -/
def projErrorSq (σ : D.d0.domain) (φ : D.dt0.domain) (u : D.dt1.domain) : ℝ :=
  ‖Q.π0 σ - σ‖ ^ 2 + ‖Q.π1 (D.d0 σ) - D.d0 σ‖ ^ 2 + ‖Q.πt0 φ - φ‖ ^ 2 +
    ‖Q.πt1 (D.dt0 φ) - D.dt0 φ‖ ^ 2 + ‖Q.πt1 u - u‖ ^ 2 + ‖Q.π2 (D.S1 (Q.πt1 u - u))‖ ^ 2 +
    ‖Q.πt2 (D.dt1 u) - D.dt1 u‖ ^ 2

end Discretization

/-! ### The wave problem with weak symmetry ([QuennevilleBelair2015], Ch. 6) -/

/-- `x` is **continuous on `[0, T]` with right derivative `x'` on `[0, T)`**, `x'` continuous on
`[0, T]`. -/
def IsC1On {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ) (x x' : ℝ → E) : Prop :=
  ContinuousOn x (Icc 0 T) ∧ ContinuousOn x' (Icc 0 T) ∧
    ∀ t ∈ Ico 0 T, HasDerivWithinAt x (x' t) (Ici t) t

/-- A **classical solution of the wave problem (6.2)** on `[0, T]` with source `f` and an `L²`
multiplier `λ` ([QuennevilleBelair2015], (6.2)): paths `σ` in `D(d⁰)`, `φ` in `D(d̃⁰)`, `u` in
`D(d̃¹)`, `M` in `W²`, `ρ` in `W̃²`, `λ` in `W¹`, with `L²`-continuous right derivatives
`σ', u', M', ρ', λ'` and `(d̃φ)' = d̃φ'`, `(d̃u)' = d̃u'` (the energy class of the thesis), such
that on `[0, T)`, for all `τ ∈ D(d⁰)`, `ψ ∈ D(d̃⁰)`, `v ∈ D(d̃¹)`:
`⟪σ', τ⟫ - ⟪u, d̃ψ⟫ - ⟪λ, dτ - S⁰ψ⟫ = 0`, `⟪u', v⟫ + ⟪d̃φ, v⟫ + ⟪M, S¹v⟫ + ⟪ρ, d̃v⟫ = ⟪f, v⟫`,
`M' = S¹u`, `ρ' = d̃u`; and on `[0, T]` the constraint `dσ = S⁰φ`, also for `σ'`, `φ'`. -/
def IsWaveSolution (T : ℝ) (f : ℝ → Wt1) (σ σ' : ℝ → D.d0.domain) (φ φ' : ℝ → D.dt0.domain)
    (u u' : ℝ → D.dt1.domain) (M M' : ℝ → W2) (ρ ρ' : ℝ → Wt2) (lam lam' : ℝ → W1) : Prop :=
  IsC1On T σ σ' ∧ IsC1On T u u' ∧
    IsC1On T (fun t => D.dt0 (φ t)) (fun t => D.dt0 (φ' t)) ∧
    IsC1On T (fun t => D.dt1 (u t)) (fun t => D.dt1 (u' t)) ∧ IsC1On T M M' ∧ IsC1On T ρ ρ' ∧
    IsC1On T lam lam' ∧
    (∀ t ∈ Ico 0 T, (∀ (τ : D.d0.domain) (ψ : D.dt0.domain), ⟪(σ' t : W0), τ⟫_ℝ -
        ⟪(u t : Wt1), D.dt0 ψ⟫_ℝ - ⟪lam t, D.d0 τ - D.S0 ψ⟫_ℝ = 0) ∧
      (∀ v : D.dt1.domain, ⟪(u' t : Wt1), v⟫_ℝ + ⟪D.dt0 (φ t), v⟫_ℝ + ⟪M t, D.S1 v⟫_ℝ +
        ⟪ρ t, D.dt1 v⟫_ℝ = ⟪f t, v⟫_ℝ) ∧ M' t = D.S1 (u t) ∧ ρ' t = D.dt1 (u t)) ∧
    ∀ t ∈ Icc 0 T, D.d0 (σ t) = D.S0 (φ t) ∧ D.d0 (σ' t) = D.S0 (φ' t)

variable {D} in
/-- `(σₕ, φₕ, uₕ, Mₕ, ρₕ, λₕ)` solves **the semi-discrete problem (6.5)** of `Q` on `[0, T]`
([QuennevilleBelair2015], (6.3), (6.5)): values in `Vₕ⁰ × Ṽₕ⁰ × Ṽₕ¹ × Vₕ² × Ṽₕ² × Vₕ¹`, `σₕ, uₕ,
Mₕ, ρₕ` continuous on `[0, T]` and right-differentiable on `[0, T)`, where (6.2) holds on the
discrete spaces with `S⁰ₕ = π¹S⁰`, `S¹ₕ = π²S¹` (`φₕ` and `λₕ` are algebraic unknowns). -/
def Discretization.IsDiscreteWave (Q : D.Discretization) (T : ℝ) (f : ℝ → Wt1)
    (σ : ℝ → D.d0.domain) (φ : ℝ → D.dt0.domain) (u : ℝ → D.dt1.domain) (M : ℝ → W2)
    (ρ : ℝ → Wt2) (lam : ℝ → W1) : Prop :=
  ContinuousOn (fun t => (σ t : W0)) (Icc 0 T) ∧ ContinuousOn (fun t => (u t : Wt1)) (Icc 0 T) ∧
    ContinuousOn M (Icc 0 T) ∧ ContinuousOn ρ (Icc 0 T) ∧
    (∀ t ∈ Icc 0 T, (σ t : W0) ∈ Q.V0 ∧ (φ t : Wt0) ∈ Q.Vt0 ∧ (u t : Wt1) ∈ Q.Vt1 ∧
      M t ∈ Q.V2 ∧ ρ t ∈ Q.Vt2 ∧ lam t ∈ Q.V1 ∧ D.d0 (σ t) = Q.π1 (D.S0 (φ t))) ∧
    ∃ (σ' : ℝ → W0) (u' : ℝ → Wt1) (M' : ℝ → W2) (ρ' : ℝ → Wt2), ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => (σ s : W0)) (σ' t) (Ici t) t ∧
      HasDerivWithinAt (fun s => (u s : Wt1)) (u' t) (Ici t) t ∧
      HasDerivWithinAt M (M' t) (Ici t) t ∧ HasDerivWithinAt ρ (ρ' t) (Ici t) t ∧
      (∀ (τ : D.d0.domain) (ψ : D.dt0.domain), (τ : W0) ∈ Q.V0 → (ψ : Wt0) ∈ Q.Vt0 →
        ⟪σ' t, τ⟫_ℝ - ⟪(u t : Wt1), D.dt0 ψ⟫_ℝ - ⟪lam t, D.d0 τ - Q.π1 (D.S0 ψ)⟫_ℝ = 0) ∧
      (∀ v : D.dt1.domain, (v : Wt1) ∈ Q.Vt1 → ⟪u' t, v⟫_ℝ + ⟪D.dt0 (φ t), v⟫_ℝ +
        ⟪M t, Q.π2 (D.S1 v)⟫_ℝ + ⟪ρ t, D.dt1 v⟫_ℝ = ⟪f t, v⟫_ℝ) ∧
      (∀ z ∈ Q.V2, ⟪M' t, z⟫_ℝ = ⟪Q.π2 (D.S1 (u t)), z⟫_ℝ) ∧
      ∀ z ∈ Q.Vt2, ⟪ρ' t, z⟫_ℝ = ⟪D.dt1 (u t), z⟫_ℝ

end WeakSymmetryData

/-! ### The cube: the BGG data (4.16) and the elements of Table 5.1 -/

/-- **The top row of Table 5.1**, `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ² → P₁⁻Λ³` (Lagrange, Nédélec edge,
Raviart–Thomas face elements and piecewise constants). -/
def topSeq : PolySeq where
  full k := k == 0
  deg _ := 1
  one_le_deg _ := le_rfl
  transition _ := Or.inl ⟨rfl, rfl⟩

/-- **The bottom row of Table 5.1**, `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₁⁻Λ³` (Lagrange `P₂`, second-order
Nédélec edge elements of the first kind, `BDM₁` and piecewise constants). -/
def bottomSeq : PolySeq where
  full k := k == 0 || k == 2
  deg k := if k ≤ 1 then 2 else 1
  one_le_deg
    | 0 => Nat.le_succ 1
    | 1 => Nat.le_succ 1
    | _ + 2 => le_rfl
  transition
    | 0 => Or.inl ⟨rfl, rfl⟩
    | 1 => Or.inr ⟨rfl, rfl⟩
    | 2 => Or.inl ⟨rfl, rfl⟩
    | _ + 3 => Or.inl ⟨rfl, rfl⟩

/-- **The BGG data (4.16) on the cube** `Q = (0, ½)³` with the thesis' boundary conditions
([QuennevilleBelair2015], §5.3): the top row `H̊Λ⁰(Q) → H̊Λ¹(Q) → L²Λ²(Q)` and, componentwise, the
bottom row `H̊Λ⁰(Q) ⊗ ℝ³ → H̊Λ¹(Q) ⊗ ℝ³ → L²Λ²(Q) ⊗ ℝ³` of the minimal exterior derivative, with
`S⁰ = S¹ = Σₐ dxₐ ∧ ·` (`wedge`). In vector proxies the rows are `H̊¹ → H̊(curl) → L²(ℝ³)` and
`S⁰ = I`, `S¹ = 2 vskw`. -/
def cubeData : WeakSymmetryData (L2Form (cube 3) 0) (L2Form (cube 3) 1) (L2Form (cube 3) 2)
    (L2Vec (cube 3) 0) (L2Vec (cube 3) 1) (L2Vec (cube 3) 2) :=
  ⟨dMin (cube 3) 0, dMin (cube 3) 1, vecOp (dMin (cube 3) 0), vecOp (dMin (cube 3) 1),
    wedge (cube 3) 0, wedge (cube 3) 1⟩

/-- `x ∈ L²(Q; Λʲ)` on the cube `Q = (0, ½)ⁿ` is (almost everywhere) a `C²` form `w` on `ℝⁿ` of
degree `j` whose **tangential components vanish on `∂Q`** (`(w y)_t = 0` for `y ∈ cl Q` on a face
`y_i ∈ {0, ½}` with `i ∉ t`; no condition on the normal components), the values and first
derivatives of `w` and `dw` being bounded by `L` on `cl Q`. -/
def IsTangentialC2 (j : ℤ) (L : ℝ) (x : L2Form (cube n) j) : Prop :=
  ∃ w : FormField n, ContDiff ℝ 2 w ∧ (∀ y (t : Finset (Fin n)), (t.card : ℤ) ≠ j → w y t = 0) ∧
    (∀ y ∈ closure (cube n), ∀ (i : Fin n) (t : Finset (Fin n)), i ∉ t →
      (y i = 0 ∨ y i = 1 / 2) → w y t = 0) ∧
    (∀ m ≤ 1, ∀ y ∈ closure (cube n),
      ‖iteratedFDeriv ℝ m w y‖ ≤ L ∧ ‖iteratedFDeriv ℝ m (extDeriv w) y‖ ≤ L) ∧
    ∀ t : FormIdx n j, ⇑(x t) =ᵐ[volume.restrict (cube n)] fun y => w y t.1

/-- A state `(σ, φ, u, M, ρ)` of the cube is **regular with bound `L`**: all components are
`IsTangentialC2` with bound `L`. -/
def IsRegularState (L : ℝ) (σ : L2Form (cube 3) 0) (φ : L2Vec (cube 3) 0) (u : L2Vec (cube 3) 1)
    (M : L2Form (cube 3) 2) (ρ : L2Vec (cube 3) 2) : Prop :=
  IsTangentialC2 0 L σ ∧ (∀ a, IsTangentialC2 0 L (φ a)) ∧ (∀ a, IsTangentialC2 1 L (u a)) ∧
    IsTangentialC2 2 L M ∧ ∀ a, IsTangentialC2 2 L (ρ a)

/-- `x ∈ L²(Ω; Λʲ)` **lies in `Hᵐ(Ω; Λʲ)` with norm at most `L`**, for `Hᵐ(Ω) = Hᵐ(ℝⁿ)|_Ω` (the
restriction definition, weak derivatives as in [Evans2010], §5.2; on Lipschitz domains, by
Stein's extension theorem, the space of weak derivatives in `L²(Ω)` with an equivalent norm): each
coefficient is the restriction of a function `D t []` on `ℝⁿ` with weak derivatives `D t l` in
`L²(ℝⁿ)` along the words `l` of length at most `m` (`∫ D t [] ∂_{l₁} ⋯ ∂_{l_p} φ =
(-1)^p ∫ D t l φ` for test functions `φ`), with `Σ_t Σ_{|l| ≤ m} ‖D t l‖² ≤ L²` (norm at most
`|L|`; a sum over words: a derivative of multi-index `α` is counted `|α|!/α!` times). -/
def IsSobolevForm (Ω : Set (Fin n → ℝ)) (m : ℕ) (j : ℤ) (L : ℝ) (x : L2Form Ω j) : Prop :=
  ∃ D : FormIdx n j → List (Fin n) → (Fin n → ℝ) → ℝ,
    (∀ t l, l.length ≤ m → MemLp (D t l) 2 volume ∧ ∀ φ, IsTestFn univ φ →
      ∫ y, D t [] y * l.foldr partialDeriv φ y = (-1) ^ l.length * ∫ y, D t l y * φ y) ∧
    ∑ t, ∑ p ∈ Finset.range (m + 1), ∑ l : Fin p → Fin n, ∫ y, D t (List.ofFn l) y ^ 2 ≤ L ^ 2 ∧
    ∀ t, ⇑(x t) =ᵐ[volume.restrict Ω] D t []

/-- A state `(σ, φ, u, M, ρ)` of the cube is **of class `H¹` with bound `L`**: `σ`, the `uₐ`, `M`
and the `ρₐ` lie in `H¹(Q)` with norms at most `L` (`IsSobolevForm`), so do the `d̊φₐ` and `d̊uₐ`
(when `φₐ`, `uₐ` lie in the domain of `dMin`), and `M` and the `ρₐ` have vanishing tangential
traces: they lie in `H̊Λ²(Q)`, the domain of `dMin`. -/
def IsH1State (L : ℝ) (σ : L2Form (cube 3) 0) (φ : L2Vec (cube 3) 0) (u : L2Vec (cube 3) 1)
    (M : L2Form (cube 3) 2) (ρ : L2Vec (cube 3) 2) : Prop :=
  IsSobolevForm (cube 3) 1 0 L σ ∧
    (∀ a (h : φ a ∈ (dMin (cube 3) 0).domain),
      IsSobolevForm (cube 3) 1 1 L (dMin (cube 3) 0 ⟨φ a, h⟩)) ∧
    (∀ a, IsSobolevForm (cube 3) 1 1 L (u a)) ∧
    (∀ a (h : u a ∈ (dMin (cube 3) 1).domain),
      IsSobolevForm (cube 3) 1 2 L (dMin (cube 3) 1 ⟨u a, h⟩)) ∧
    IsSobolevForm (cube 3) 1 2 L M ∧ (∀ a, IsSobolevForm (cube 3) 1 2 L (ρ a)) ∧
    M ∈ (dMin (cube 3) 2).domain ∧ ∀ a, ρ a ∈ (dMin (cube 3) 2).domain

/-! ### The theorems -/

end FEEC
