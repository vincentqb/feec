module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Affinely invariant polynomial differential forms and their degrees of freedom

Which spaces of polynomial differential forms are the local spaces of finite element exterior
calculus, and do they have degrees of freedom? A polynomial `k`-form on `Kⁿ` is given by its
coefficients on the `dx_s` (`PolyForm`); `P_rΛᵏ` has coefficients of degree at most `r`, `H_rΛᵏ`
homogeneous coefficients of degree `r`, `κ` is the Koszul differential and
`P_r⁻Λᵏ = P_{r-1}Λᵏ + κH_{r-1}Λᵏ⁺¹` ([AFW2006], §3).

* **The affinely invariant spaces are classified** (`affineInvariantForms`; [AFW2006], §3.4,
  Theorems 3.5–3.6, over every field of characteristic `0`): the summands `dH_{r+1}Λᵏ⁻¹` and
  `κH_{r-1}Λᵏ⁺¹` of `H_rΛᵏ` are its only nontrivial `GL(n)`-invariant subspaces (`r, k ≥ 1`),
  and for `0 < k < n` the nonzero finite-dimensional affinely invariant spaces of `k`-forms are
  exactly `P_rΛᵏ` (`r ≥ 0`), `P_r⁻Λᵏ` (`r ≥ 1`), `dP_{r+1}Λᵏ⁻¹` (`r ≥ 0`) and
  `X(r, s, k) = dP_{r+1}Λᵏ⁻¹ + κP_sΛᵏ⁺¹` with `0 ≤ s ≤ r - 2`. The statement has the spaces
  `dP_{r+1}Λᵏ⁻¹` and `X(r, s, k)`, `s ≤ r`, with `X(r, r, k) = P_{r+1}⁻Λᵏ`,
  `X(r + 1, r, k) = P_{r+1}Λᵏ` and `dP_1Λᵏ⁻¹ = P_0Λᵏ`.
* **Characteristic `0` is necessary**: over a field `K`, the classification of the invariant
  subspaces of `H_rΛᵏ` (`charZero_iff_classification`) and the homogeneous Poincaré lemma
  (`charZero_iff_closed_eq_exact`) hold in every dimension iff `K` has characteristic `0`.
* **The degrees of freedom of [AFW2006], §4 are unisolvent** (`unisolvent`; Theorems 4.10,
  4.14): on every `n`-simplex, for `r ≥ 1`, the moments `∫_f tr_f ω ∧ η` on its `m`-faces `f`,
  `k ≤ m < r + k`, against `η ∈ P⁻_{r+k-m}Λ^{m-k}` for `ω ∈ P_rΛᵏ` and `η ∈ P_{r+k-m-1}Λ^{m-k}` for
  `ω ∈ P_r⁻Λᵏ`, vanish only for `ω = 0`, and they are as many as the dimension.
* **They are local: they assemble the finite element spaces** (`assembly`; [AFW2010], §5.2;
  [AFW2006], §5.1). On every simplicial mesh `M`, for every admissible sequence `S`
  (`P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` in each degree `k`), forms that are on every simplex a form of
  `S_k` have single-valued tangential traces, the condition of the finite element space `S_k(M)`
  (`femSpace`), iff their face moments are single-valued (the same from any two simplices of a
  common face, along one or every enumeration of its vertices); the face moments are free
  coordinates on `S_k(M)`: prescribed on every face, they are those of exactly one of its
  elements; and when `M` meshes an open set, `S_k(M)` has the dimension
  `Σ_m #{m-faces of M} · dim (test forms on m-faces)`, the number of face moments.

Not claimed: the classification of the affinely invariant complexes built from these spaces (the
periodic table of finite element exterior calculus, cf. [AFW2006], §3.5; the theorems classify
spaces, not complexes), and the identification of the finite element spaces with the piecewise
polynomial forms of `HΛᵏ(Ω)` ([AFW2010], Theorem 5.7).

## Conventions

Polynomial forms are coefficient functions `Finset (Fin n) → MvPolynomial (Fin n) K`, the
coefficient of `dx_s`, `s` a set of indices; real polynomial forms are evaluated to form fields on
`ℝⁿ = Fin n → ℝ` (`evalForm`) for the moments. A moment is taken over a simplex given by the list
of its vertices; the faces of a simplex are listed in the increasing order of their vertex indices
(`unisolvent`), the faces of a mesh, sets of vertices of its simplices, by any enumeration
(`assembly`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3–§5
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4, §5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Filter Set LinearPMap MeasureTheory

@[expose] public noncomputable section

universe u

namespace FEEC

/-! ### Form fields on `ℝⁿ` and `L²` forms (the shared blocks) -/

variable {n : ℕ}

-- palomar-shared: FormField
/-- A **form field** on `ℝⁿ`: at each point a coefficient of `dx_s` for every subset `s` of
`Fin n` (a `k`-form when those off the `k`-subsets vanish). -/
abbrev FormField (n : ℕ) : Type := (Fin n → ℝ) → Finset (Fin n) → ℝ
/-- The sign `ε(j, s) = (-1)^{#{l ∈ s | l < j}}` of moving `dx_j` to its place in `dx_s`. -/
def sgn {n : ℕ} {R : Type*} [Ring R] (j : Fin n) (s : Finset (Fin n)) : R :=
  (-1) ^ (s.filter fun l => l < j).card
-- palomar-shared-end: FormField

-- palomar-shared: forms
/-- The coefficients of a `k`-form on `ℝⁿ`: the `k`-subsets `s = {s₁ < ⋯ < s_k}` of `Fin n`,
`s` indexing `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}` (none unless `0 ≤ k ≤ n`). -/
abbrev FormIdx (n : ℕ) (k : ℤ) : Type := {s : Finset (Fin n) // (s.card : ℤ) = k}
/-- `L²(Ω; Λᵏ)`: an `L²(Ω)` coefficient (Lebesgue measure) for each `dx_s`, an `ℓ²` sum. -/
abbrev L2Form {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : Type :=
  PiLp 2 fun _ : FormIdx n k => Lp ℝ 2 (volume.restrict Ω)
/-- The partial derivative `∂_j f(x) = Df(x) e_j` (`0` where `f` is not differentiable). -/
def partialDeriv {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single j 1)
/-- The **exterior derivative** of a form field, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`. -/
def extDeriv {n : ℕ} (w : FormField n) : FormField n :=
  fun x s => ∑ j ∈ s, sgn j s * partialDeriv j (fun y => w y (s.erase j)) x
/-- The **codifferential** `(dᵗψ)_s = -Σ_{j ∉ s} ε(j, s) ∂_j ψ_{s ∪ j}`, formal adjoint of `d`. -/
def codiff {n : ℕ} (ψ : FormField n) : FormField n :=
  fun x s => -∑ j ∈ sᶜ, sgn j s * partialDeriv j (fun y => ψ y (insert j s)) x
open scoped ContDiff in
/-- `f` is a **test function** on `Ω`: smooth, with compact support contained in `Ω`. -/
def IsTestFn {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω
/-- The **weak exterior derivative** `d : L²(Ω; Λᵏ) → L²(Ω; Λᵏ⁺¹)`: the adjoint of the closure of
the codifferential on test forms (the span of the pairs `(ψ, dᵗψ)`), so `du = w` iff
`⟪w, ψ⟫ = ⟪u, dᵗψ⟫` for every test form `ψ`; its domain is `HΛᵏ(Ω)` ([AFW2010], §4). -/
def dMax {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : L2Form Ω k →ₗ.[ℝ] L2Form Ω (k + 1) :=
  (Submodule.span ℝ {p : L2Form Ω (k + 1) × L2Form Ω k | ∃ ψ : FormField n,
    (∀ s, IsTestFn Ω fun x => ψ x s) ∧
    (∀ t : FormIdx n (k + 1), ⇑(p.1 t) =ᵐ[volume.restrict Ω] fun x => ψ x t.1) ∧
    ∀ s : FormIdx n k, ⇑(p.2 s) =ᵐ[volume.restrict Ω] fun x => codiff ψ x s.1}
    ).topologicalClosure.toLinearPMap†
/-- The cube `(0, ½)ⁿ`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := univ.pi fun _ => Ioo 0 (1 / 2)
-- palomar-shared-end: forms

/-! ### Polynomial differential forms ([AFW2006], §3) -/

-- palomar-shared: PolyForm
/-- **Polynomial differential forms** on `Kⁿ` in coordinates: a polynomial coefficient `ω_s` for
every subset `s` of `Fin n`, the form `Σ_s ω_s dx_s`. -/
abbrev PolyForm (K : Type*) [Field K] (n : ℕ) : Type _ := Finset (Fin n) → MvPolynomial (Fin n) K
/-- `P_rΛᵏ`: the polynomial `k`-forms (`ω_s = 0` unless `#s = k`) with coefficients of degree at
most `r`. -/
def polyForm (K : Type*) [Field K] (n r k : ℕ) : Submodule K (PolyForm K n) :=
  Submodule.pi Set.univ fun s =>
    if s.card = k then MvPolynomial.restrictTotalDegree (Fin n) K r else ⊥
/-- `H_rΛᵏ`: the polynomial `k`-forms with coefficients homogeneous of degree `r`. -/
def homForm (K : Type*) [Field K] (n r k : ℕ) : Submodule K (PolyForm K n) :=
  Submodule.pi Set.univ fun s =>
    if s.card = k then MvPolynomial.homogeneousSubmodule (Fin n) K r else ⊥
/-- The **Koszul differential** `κ`, the contraction with the position vector field `x`:
`(κω)_s = Σ_{j ∉ s} ε(j, s) x_j ω_{s ∪ j}`. -/
def koszul (K : Type*) [Field K] (n : ℕ) : PolyForm K n →ₗ[K] PolyForm K n :=
  LinearMap.pi fun s => ∑ j ∈ sᶜ,
    (sgn j s : K) • (LinearMap.mulLeft K (MvPolynomial.X j) ∘ₗ LinearMap.proj (insert j s))
/-- `P_r⁻Λᵏ = P_{r-1}Λᵏ + κ H_{r-1}Λ^{k+1}`, the trimmed polynomial `k`-forms (`r ≥ 1`), and
`P_0⁻Λᵏ = 0` ([AFW2006], §3.3). -/
def polyFormMinus (K : Type*) [Field K] (n : ℕ) : ℕ → ℕ → Submodule K (PolyForm K n)
  | 0, _ => ⊥
  | r + 1, k => polyForm K n r k ⊔ (homForm K n r (k + 1)).map (koszul K n)
/-- The **evaluation** of a real polynomial form: the form field `x ↦ (ω_s(x))_s`. -/
def evalForm {n : ℕ} : PolyForm ℝ n →ₗ[ℝ] FormField n :=
  LinearMap.pi fun x => LinearMap.pi fun s =>
    (MvPolynomial.aeval x).toLinearMap ∘ₗ LinearMap.proj s
-- palomar-shared-end: PolyForm

section Poly
variable (K : Type*) [Field K] (n : ℕ)

/-- The **exterior derivative** of polynomial forms, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`. -/
def polyExtDeriv : PolyForm K n →ₗ[K] PolyForm K n :=
  LinearMap.pi fun s => ∑ j ∈ s,
    (sgn j s : K) • ((MvPolynomial.pderiv j).toLinearMap ∘ₗ LinearMap.proj (s.erase j))
/-- The **pullback** of polynomial forms along the affine map `φ(x) = B x + b` of `Kⁿ`:
`(φ^*ω)_t = Σ_{#s = #t} det B_{s,t} · (ω_s ∘ φ)`, `B_{s,t}` the submatrix of the rows `s` and the
columns `t` (that is, `φ^* dx_i = Σ_l B_{il} dx_l`). -/
def pullback (B : Matrix (Fin n) (Fin n) K) (b : Fin n → K) : PolyForm K n →ₗ[K] PolyForm K n :=
  LinearMap.pi fun t => ∑ s : Finset (Fin n), if h : s.card = t.card then
    (B.submatrix (s.orderEmbOfFin h) (t.orderEmbOfFin rfl)).det •
      ((MvPolynomial.aeval fun i => ∑ l, MvPolynomial.C (B i l) * MvPolynomial.X l +
        MvPolynomial.C (b i)).toLinearMap ∘ₗ LinearMap.proj s) else 0
/-- `V` is **affinely invariant**: mapped into itself by the pullback along every affine map of
`Kⁿ`, singular ones included. -/
def IsAffineInvariant (V : Submodule K (PolyForm K n)) : Prop :=
  ∀ B b, V.map (pullback K n B b) ≤ V
/-- `V` is mapped into itself by the pullback along every linear map `x ↦ B x` of `Kⁿ`. -/
def IsLinearInvariant (V : Submodule K (PolyForm K n)) : Prop :=
  ∀ B, V.map (pullback K n B 0) ≤ V
/-- `V` is mapped into itself by the pullback along every `g ∈ GL(n, K)`. -/
def IsGLInvariant (V : Submodule K (PolyForm K n)) : Prop :=
  ∀ g : GL (Fin n) K, V.map (pullback K n g 0) ≤ V
/-- `X(r, s, k) = dP_{r+1}Λ^{k-1} + κP_sΛ^{k+1}` ([AFW2006], Theorem 3.5), used for `k ≥ 1` and
`s ≥ 0`; the source's case `s = -1` is `dP_{r+1}Λ^{k-1}`. -/
def invariantForm (r s k : ℕ) : Submodule K (PolyForm K n) :=
  (polyForm K n (r + 1) (k - 1)).map (polyExtDeriv K n) ⊔
    (polyForm K n s (k + 1)).map (koszul K n)
/-- **The classification of the invariant spaces of polynomial forms** on `Kⁿ`, `K` of
characteristic `0` ([AFW2006], §3.4). -/
structure AffineInvariantForms [CharZero K] : Prop where
  /-- the images `dH_rΛᵏ` and `κH_rΛᵏ` are linearly invariant, among them the summands
  `dH_{r+1}Λ^{k-1}` and `κH_{r-1}Λ^{k+1}` of `H_rΛᵏ` (§3.4) -/
  isLinearInvariant_map_homForm (r k : ℕ) :
    IsLinearInvariant K n ((homForm K n r k).map (polyExtDeriv K n)) ∧
      IsLinearInvariant K n ((homForm K n r k).map (koszul K n))
  /-- every `GL(n)`-invariant subspace of `H_{r+1}Λ^{k+1}` is `0`, `dH_{r+2}Λᵏ`, `κH_rΛ^{k+2}`
  or `H_{r+1}Λ^{k+1}`: the summands of (3.10) are irreducible (§3.4, before Lemma 3.7) -/
  eq_of_le_homForm (r k : ℕ) (W : Submodule K (PolyForm K n)) (hW : IsGLInvariant K n W)
    (hle : W ≤ homForm K n (r + 1) (k + 1)) :
    W = ⊥ ∨ W = (homForm K n (r + 2) k).map (polyExtDeriv K n) ∨
      W = (homForm K n r (k + 2)).map (koszul K n) ∨ W = homForm K n (r + 1) (k + 1)
  /-- `dP_{r+1}Λ^{k-1}` is affinely invariant ((3.18)) -/
  isAffineInvariant_map_extDeriv (r k : ℕ) :
    IsAffineInvariant K n ((polyForm K n (r + 1) (k - 1)).map (polyExtDeriv K n))
  /-- `X(r, s, k)` is affinely invariant for `s ≤ r`, `k ≥ 1` (Theorem 3.5) -/
  isAffineInvariant_invariantForm (r s k : ℕ) (hk : 1 ≤ k) (hs : s ≤ r) :
    IsAffineInvariant K n (invariantForm K n r s k)
  /-- `X(r, r, k) = P_{r+1}⁻Λᵏ` (Theorem 3.5, case `s = r`) -/
  invariantForm_eq_polyFormMinus (r k : ℕ) (hk : 1 ≤ k) :
    invariantForm K n r r k = polyFormMinus K n (r + 1) k
  /-- `X(r + 1, r, k) = P_{r+1}Λᵏ` (Theorem 3.5, case `s = r - 1`) -/
  invariantForm_eq_polyForm (r k : ℕ) (hk : 1 ≤ k) :
    invariantForm K n (r + 1) r k = polyForm K n (r + 1) k
  /-- `dP_1Λ^{k-1} = P_0Λᵏ`, `X(0, -1, k)` (Theorem 3.5, case `s = r - 1`, `r = 0`) -/
  map_extDeriv_polyForm_one (k : ℕ) (hk : 1 ≤ k) :
    (polyForm K n 1 (k - 1)).map (polyExtDeriv K n) = polyForm K n 0 k
  /-- for `0 < k < n` every nonzero finite-dimensional space of `k`-forms invariant under the
  invertible affine maps is `dP_{r+1}Λ^{k-1}` or `X(r, s, k)`, `s ≤ r` (Theorem 3.6) -/
  eq_invariantForm (k : ℕ) (hk : 0 < k) (hkn : k < n) (V : Submodule K (PolyForm K n))
    [FiniteDimensional K V] (hV : ∀ (g : GL (Fin n) K) b, V.map (pullback K n g b) ≤ V)
    (hdeg : ∀ w ∈ V, ∀ s, s.card ≠ k → w s = 0) (hne : V ≠ ⊥) :
    ∃ r, V = (polyForm K n (r + 1) (k - 1)).map (polyExtDeriv K n) ∨
      ∃ s ≤ r, V = invariantForm K n r s k
end Poly

/-! ### The degrees of freedom ([AFW2006], §4) -/

-- palomar-shared: covEval
/-- The value `α(v₁, …, v_k) = Σ_{#s = k} α_s det (v_l(s_i))_{i,l}` of the `k`-covector `α` on
the vectors `v₁, …, v_k`. -/
def covEval {n k : ℕ} (α : Finset (Fin n) → ℝ) (v : Fin k → Fin n → ℝ) : ℝ :=
  ∑ s : Finset (Fin n), if h : s.card = k then
    α s * (Matrix.of fun i l => v l (s.orderEmbOfFin h i)).det else 0
-- palomar-shared-end: covEval

/-- The **moment** `∫_f tr_f w ∧ η` ([AFW2006], §4) of a form field `w` on `ℝⁿ` against `η` on
`ℝᵐ`, over the `m`-simplex `f` with the vertices `v_0, …, v_m` (a face of a simplex, its vertices
listed in the order of `v`), parametrized by `φ(y) = v_0 + Σ_l y_l (v_{l+1} - v_0)` on the
reference simplex `T̂_m = {y ≥ 0, Σ_l y_l ≤ 1}`: the integrand is the `dy_0 ∧ ⋯ ∧ dy_{m-1}`
coefficient `Σ_s ε(s, sᶜ) (φ^*w)_s η_{sᶜ}` of `φ^*w ∧ η`, `(φ^*w)_s(y) = w(φ y)(∂_{s₁}φ, …)` and
`ε(s, sᶜ) = Π_{a ∈ s} ε(a, sᶜ)` the sign of `dy_s ∧ dy_{sᶜ}`. -/
def faceMoment {m : ℕ} (v : Fin (m + 1) → Fin n → ℝ) (η : FormField m) (w : FormField n) : ℝ :=
  ∫ y in {y : Fin m → ℝ | (∀ l, 0 ≤ y l) ∧ ∑ l, y l ≤ 1}, ∑ s : Finset (Fin m),
    (∏ a ∈ s, sgn a sᶜ) *
      covEval (w fun i => v 0 i + ∑ l, y l * (v l.succ i - v 0 i))
        (fun j i => v (s.orderEmbOfFin rfl j).succ i - v 0 i) * η y sᶜ

/-! ### Finite element spaces on simplicial meshes (the shared blocks) -/

-- palomar-shared: PolySeq
/-- **An admissible sequence** of polynomial families ([AFW2006], §5; [AFW2010], §5.2): in every
form degree `k` the full space `P_{r_k}Λᵏ` (`full k = true`) or the trimmed space `P_{r_k}⁻Λᵏ`,
`r_k ≥ 1`, followed in degree `k + 1` by `P_{r_k}⁻Λᵏ⁺¹` or by `P_{r_k - 1}Λᵏ⁺¹`. (The piecewise
constants `P_0Λⁿ` are represented by the equal space `P_1⁻Λⁿ`; the spaces of degree `k > n`
are `0`. A full space `P_0Λᵏ` with `k < n` is excluded: it is followed by `P_0⁻Λᵏ⁺¹ = 0`, and
such a family could not approximate `HΛᵏ⁺¹(Ω)`.) -/
structure PolySeq where
  /-- `P_{r_k}Λᵏ` (`true`) or `P_{r_k}⁻Λᵏ` (`false`) in degree `k` -/
  full : ℕ → Bool
  /-- the polynomial degree `r_k` -/
  deg : ℕ → ℕ
  one_le_deg : ∀ k, 1 ≤ deg k
  transition : ∀ k, (full (k + 1) = false ∧ deg (k + 1) = deg k) ∨
    (full (k + 1) = true ∧ deg (k + 1) + 1 = deg k)
/-- The space `P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` of form fields on `ℝⁿ` of the sequence in degree `k`. -/
def PolySeq.space (S : PolySeq) (n k : ℕ) : Submodule ℝ (FormField n) :=
  (if S.full k then polyForm ℝ n (S.deg k) k else polyFormMinus ℝ n (S.deg k) k).map evalForm
-- palomar-shared-end: PolySeq

-- palomar-shared: SimplicialMesh
/-- The vertex set `{v₀, …, v_k}` of a simplex. -/
def vertexSet {n k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) : Finset (Fin n → ℝ) :=
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
-- palomar-shared-end: SimplicialMesh

-- palomar-shared: femSpace
/-- The `k`-covectors `α`, `β` have the **same tangential trace** on the face spanned by the
points `g`: they agree on all `k`-tuples of vectors tangent to the face. -/
def TraceEq {n : ℕ} (g : Finset (Fin n → ℝ)) (k : ℕ) (α β : Finset (Fin n) → ℝ) : Prop :=
  ∀ v : Fin k → Fin n → ℝ, (∀ l, v l ∈ vectorSpan ℝ (g : Set (Fin n → ℝ))) →
    covEval α v = covEval β v
/-- `p = (p_T)_T` are **finite element pieces** of `u ∈ L²(Ω; Λᵏ)` on the mesh `M` for the
sequence `S`: on every simplex `T`, `u` is (almost everywhere) the polynomial form `p_T ∈ S_k`,
and the tangential traces of `p_T` and `p_{T'}` agree on the common face of any two simplices. -/
def IsFemPieces {n : ℕ} (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (S : PolySeq) (k : ℤ)
    (u : L2Form Ω k) (p : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n) : Prop :=
  (∀ T ∈ M.simplices, p T ∈ S.space n k.toNat) ∧
    (∀ T ∈ M.simplices, ∀ s : FormIdx n k,
      ⇑(u s) =ᵐ[volume.restrict (Ω ∩ T.closedInterior)] fun x => p T x s.1) ∧
    ∀ T ∈ M.simplices, ∀ T' ∈ M.simplices,
      ∀ x ∈ convexHull ℝ ((vertexSet T ∩ vertexSet T' : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)),
        TraceEq (vertexSet T ∩ vertexSet T') k.toNat (p T x) (p T' x)
/-- **The finite element space** `S_k(M) ⊆ L²(Ω; Λᵏ)` of the admissible sequence `S` on the mesh
`M` **with vanishing traces on the facets `Γ`** ([AFW2006], §5; [Arnold2018], Ch. 7): the forms
that are on every simplex a polynomial form of `S_k`, with single-valued tangential traces on the
faces of the mesh, vanishing on the facets of the mesh in `Γ` (`Γ = ∅`: no boundary condition,
the spaces of `HΛ(Ω)`; `Γ = M.boundaryFacets`: vanishing traces on `∂Ω`, those of `H̊Λ(Ω)`). -/
def femSpace {n : ℕ} (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (S : PolySeq)
    (Γ : Set (Finset (Fin n → ℝ))) (k : ℤ) : Set (L2Form Ω k) :=
  {u | ∃ p, IsFemPieces Ω M S k u p ∧ ∀ T ∈ M.simplices, ∀ F ⊆ vertexSet T, F.card = n →
    F ∈ Γ → ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), TraceEq F k.toNat (p T x) 0}
-- palomar-shared-end: femSpace

/-- The **`m`-faces of the mesh** `M`: the sets of `m + 1` vertices of one of its simplices (none
for `m > n`; a face of several simplices is counted once). -/
def SimplicialMesh.faces (M : SimplicialMesh n) (m : ℕ) : Finset (Finset (Fin n → ℝ)) :=
  M.simplices.biUnion fun T => (vertexSet T).powersetCard (m + 1)

/-- The **test forms of the moments of `S_k` on the `m`-faces** ([AFW2006], §4; [AFW2010],
Theorem 5.5), as in `unisolvent`: for `k ≤ m < r + k`, `r = r_k`, the forms `P⁻_{r+k-m}Λ^{m-k}` on
`ℝᵐ` if `S_k = P_rΛᵏ`, and `P_{r+k-m-1}Λ^{m-k}` if `S_k = P_r⁻Λᵏ`; none for the other `m`. -/
def PolySeq.testForms (S : PolySeq) (k m : ℕ) : Submodule ℝ (FormField m) :=
  if k ≤ m ∧ m < S.deg k + k then
    (if S.full k then polyFormMinus ℝ m (S.deg k + k - m) (m - k)
      else polyForm ℝ m (S.deg k + k - m - 1) (m - k)).map evalForm
  else ⊥

/-! ### The affinely invariant spaces -/

/-- **The classification of the invariant spaces of polynomial differential forms** on `Kⁿ`, `K`
of characteristic `0` ([AFW2006], §3.4, Theorems 3.5–3.6, over `ℝ`): for `0 < k < n` the nonzero
finite-dimensional affinely invariant spaces of `k`-forms are exactly `P_rΛᵏ`, `P_r⁻Λᵏ`,
`dP_{r+1}Λ^{k-1}` and `X(r, s, k) = dP_{r+1}Λ^{k-1} + κP_sΛ^{k+1}` with `0 ≤ s ≤ r - 2`; the
summands `dH_{r+1}Λ^{k-1}` and `κH_{r-1}Λ^{k+1}` of `H_rΛᵏ` are irreducible under `GL(n)`
(`AffineInvariantForms`). -/
theorem affineInvariantForms (K : Type u) [Field K] [CharZero K] (n : ℕ) :
    AffineInvariantForms K n := by
  sorry

/-- **Characteristic `0` is necessary for the classification**: every `GL(n)`-invariant subspace
of `H_{r+1}Λ^{k+1}` is `0`, `dH_{r+2}Λᵏ`, `κH_rΛ^{k+2}` or `H_{r+1}Λ^{k+1}`, in every dimension
`n` and all degrees, iff `K` has characteristic `0`: the hypothesis `CharZero K` of
`affineInvariantForms` cannot be dropped. -/
theorem charZero_iff_classification (K : Type u) [Field K] :
    CharZero K ↔ ∀ (n r k : ℕ) (W : Submodule K (PolyForm K n)), IsGLInvariant K n W →
      W ≤ homForm K n (r + 1) (k + 1) →
        W = ⊥ ∨ W = (homForm K n (r + 2) k).map (polyExtDeriv K n) ∨
          W = (homForm K n r (k + 2)).map (koszul K n) ∨ W = homForm K n (r + 1) (k + 1) := by
  sorry

/-- **Characteristic `0` is necessary for the homogeneous Poincaré lemma** ([AFW2006], (3.2)):
the closed forms of `H_rΛ^{k+1}` are the exact forms `dH_{r+1}Λᵏ` in every dimension `n` and all
degrees iff `K` has characteristic `0`. -/
theorem charZero_iff_closed_eq_exact (K : Type u) [Field K] :
    CharZero K ↔ ∀ n r k : ℕ, LinearMap.ker (polyExtDeriv K n) ⊓ homForm K n r (k + 1) =
      (homForm K n (r + 1) k).map (polyExtDeriv K n) := by
  sorry

/-! ### Unisolvence -/

/-- **Unisolvence of the degrees of freedom of `P_rΛᵏ` and `P_r⁻Λᵏ`** ([AFW2006], Thms 4.10, 4.14;
[AFW2010], Thm 5.5): on every `n`-simplex `T`, `r ≥ 1`, a form of `P_rΛᵏ` (resp. `P_r⁻Λᵏ`) whose
moments `∫_f tr_f ω ∧ η` (`faceMoment`) vanish for all `m`-faces `f` of `T`, with the vertices
listed as `T.points ∘ e` (`e` increasing), and all
`η ∈ P⁻_{r+k-m}Λ^{m-k}(ℝᵐ)` (resp. `P_{r+k-m-1}Λ^{m-k}(ℝᵐ)`), `k ≤ m < r + k`, is zero, and these
moments, `C(n + 1, m + 1)` faces of each dimension `m`, are as many as `dim P_rΛᵏ(ℝⁿ)` (resp.
`dim P_r⁻Λᵏ(ℝⁿ)`): for bases of the test spaces they are a basis of the dual space. -/
theorem unisolvent (T : Affine.Simplex ℝ (Fin n → ℝ) n) {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    (∀ w ∈ (polyForm ℝ n r k).map evalForm, (∀ m (e : Fin (m + 1) ↪o Fin (n + 1)), k ≤ m →
      m < r + k → ∀ η ∈ (polyFormMinus ℝ m (r + k - m) (m - k)).map evalForm,
        faceMoment (T.points ∘ e) η w = 0) → w = 0) ∧
    (∀ w ∈ (polyFormMinus ℝ n r k).map evalForm, (∀ m (e : Fin (m + 1) ↪o Fin (n + 1)), k ≤ m →
      m < r + k → ∀ η ∈ (polyForm ℝ m (r + k - m - 1) (m - k)).map evalForm,
        faceMoment (T.points ∘ e) η w = 0) → w = 0) ∧
    Module.finrank ℝ (polyForm ℝ n r k) = ∑ m ∈ Finset.range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then Module.finrank ℝ (polyFormMinus ℝ m (r + k - m) (m - k)) else 0) ∧
    Module.finrank ℝ (polyFormMinus ℝ n r k) = ∑ m ∈ Finset.range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then Module.finrank ℝ (polyForm ℝ m (r + k - m - 1) (m - k))
        else 0) := by
  sorry

/-! ### Assembly -/

/-- **The face moments assemble the finite element spaces** ([AFW2010], §5.2; [AFW2006], §5.1): on
every simplicial mesh `M`, for every admissible sequence `S` and form degree `k`,
* for forms `p_T ∈ S_k` on the simplices `T` of `M`, the following are equivalent: their tangential
  traces are single-valued (they agree on the common face of any two simplices, the condition of
  `femSpace`); their face moments are single-valued, `∫_f tr_f p_T ∧ η = ∫_f tr_f p_{T'} ∧ η` for
  any two simplices `T`, `T'`, every common face `f` (`faceMoment` along every enumeration `v` of
  its vertices) and every test form `η` of `S_k` on `(dim f)`-faces (`PolySeq.testForms`); and the
  same along one enumeration of each common face;
* the face moments are free coordinates on the finite element space `S_k(M)` (`femSpace` with no
  boundary condition): for every enumeration `v m g` of the vertices of every `m`-face `g` of `M`
  and every assignment of a linear functional `c m g` on the test forms to each face, exactly one
  element `u` of `S_k(M)` has pieces `p` with the moments `∫_g tr_g p_T ∧ η = c m g η` on every
  face `g` of every simplex `T`;
* if `M` meshes an open set `Ω`, the pieces of an element of `S_k(M)` are unique, so that its face
  moments are well defined (by the first item and the uniqueness of the pieces) and the second
  item makes them a bijection of `S_k(M)` onto the assignments `(c m g)` on the faces `g` of `M`,
  and `S_k(M)` is a finite-dimensional subspace of `L²(Ω; Λᵏ)` of dimension
  `Σ_m #{m-faces of M} · dim (test forms on m-faces)`, the number of face moments. -/
theorem assembly (M : SimplicialMesh n) (S : PolySeq) (k : ℕ) :
    (∀ p : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n, (∀ T ∈ M.simplices, p T ∈ S.space n k) →
      List.TFAE [∀ T ∈ M.simplices, ∀ T' ∈ M.simplices,
          ∀ x ∈ convexHull ℝ ((vertexSet T ∩ vertexSet T' : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)),
            TraceEq (vertexSet T ∩ vertexSet T') k (p T x) (p T' x),
        ∀ T ∈ M.simplices, ∀ T' ∈ M.simplices, ∀ m,
          ∀ g ∈ (vertexSet T ∩ vertexSet T').powersetCard (m + 1),
            ∀ v : Fin (m + 1) → Fin n → ℝ, Set.range v = g → ∀ η ∈ S.testForms k m,
              faceMoment v η (p T) = faceMoment v η (p T'),
        ∀ T ∈ M.simplices, ∀ T' ∈ M.simplices, ∀ m,
          ∀ g ∈ (vertexSet T ∩ vertexSet T').powersetCard (m + 1),
            ∃ v : Fin (m + 1) → Fin n → ℝ, Set.range v = g ∧ ∀ η ∈ S.testForms k m,
              faceMoment v η (p T) = faceMoment v η (p T')]) ∧
    (∀ v : ∀ m, Finset (Fin n → ℝ) → Fin (m + 1) → Fin n → ℝ,
      (∀ m, ∀ g ∈ M.faces m, Set.range (v m g) = g) →
      ∀ c : ∀ m, Finset (Fin n → ℝ) → Module.Dual ℝ (S.testForms k m),
        ∃! u : L2Form M.domain k, ∃ p, IsFemPieces M.domain M S k u p ∧
          ∀ T ∈ M.simplices, ∀ m, ∀ g ∈ (vertexSet T).powersetCard (m + 1),
            ∀ η : S.testForms k m, faceMoment (v m g) η (p T) = c m g η) ∧
    (IsOpen M.domain → (∀ (u : L2Form M.domain k) p p', IsFemPieces M.domain M S k u p →
        IsFemPieces M.domain M S k u p' → ∀ T ∈ M.simplices, p T = p' T) ∧
      ∃ V : Submodule ℝ (L2Form M.domain k), FiniteDimensional ℝ V ∧
        (V : Set (L2Form M.domain k)) = femSpace M.domain M S ∅ k ∧
        Module.finrank ℝ V =
          ∑ m ∈ Finset.range (n + 1), (M.faces m).card * Module.finrank ℝ (S.testForms k m)) := by
  sorry

end FEEC
