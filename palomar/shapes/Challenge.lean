module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
  `dP_{r+1}Λᵏ⁻¹` and the `X(r, s, k) = dP_{r+1}Λᵏ⁻¹ + κP_sΛᵏ⁺¹`, `s ≤ r`, which lie between
  `P_{s+1}⁻Λᵏ` and `P_{r+1}⁻Λᵏ`; the full and trimmed spaces are `P_{r+1}Λᵏ = X(r + 1, r, k)` and
  `P_{r+1}⁻Λᵏ = X(r, r, k)`.
* **Characteristic `0` is necessary**: over a field `K`, the classification of the invariant
  subspaces of `H_rΛᵏ` (`charZero_iff_classification`) and the homogeneous Poincaré lemma
  (`charZero_iff_closed_eq_exact`) hold in every dimension iff `K` has characteristic `0`.
* **The degrees of freedom of [AFW2006], §4 are unisolvent** (`unisolvent`; Theorems 4.10,
  4.14): on every `n`-simplex, for `r ≥ 1`, the moments `∫_f tr_f ω ∧ η` on its `m`-faces `f`,
  `k ≤ m < r + k`, against `η ∈ P⁻_{r+k-m}Λ^{m-k}` for `ω ∈ P_rΛᵏ` and `η ∈ P_{r+k-m-1}Λ^{m-k}` for
  `ω ∈ P_r⁻Λᵏ`, vanish only for `ω = 0`, and they are as many as the dimension.

Not claimed: the classification of the affinely invariant complexes built from these spaces (the
periodic table of finite element exterior calculus; cf. [AFW2006], §3.5). The theorems classify
spaces, not complexes.

## Conventions

Polynomial forms are coefficient functions `Finset (Fin n) → MvPolynomial (Fin n) K`, the
coefficient of `dx_s`, `s` a set of indices; real polynomial forms are evaluated to form fields on
`ℝⁿ = Fin n → ℝ` (`evalForm`) for the moments. The faces of a simplex are oriented by the
increasing order of their vertices. The shared block `forms` (differential forms on `ℝⁿ`) is
copied whole; this entry uses its form fields and the sign `ε(j, s)`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3–§4
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4, §5

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Filter Topology Set LinearPMap MeasureTheory

@[expose] public noncomputable section

universe u

namespace FEEC

/-! ### Differential forms on `ℝⁿ` (the shared block) -/

variable {n : ℕ}

-- palomar-shared: forms
/-- The coefficients of a `k`-form on `ℝⁿ`: the `k`-subsets `s = {s₁ < ⋯ < s_k}` of `Fin n`,
`s` indexing `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}` (none unless `0 ≤ k ≤ n`). -/
abbrev FormIdx (n : ℕ) (k : ℤ) : Type := {s : Finset (Fin n) // (s.card : ℤ) = k}
/-- `L²(Ω; Λᵏ)`: an `L²(Ω)` coefficient (Lebesgue measure) for each `dx_s`, an `ℓ²` sum. -/
abbrev L2Form {n : ℕ} (Ω : Set (Fin n → ℝ)) (k : ℤ) : Type :=
  PiLp 2 fun _ : FormIdx n k => Lp ℝ 2 (volume.restrict Ω)
/-- A **form field** on `ℝⁿ`: at each point a coefficient of `dx_s` for every subset `s` of
`Fin n` (a `k`-form when those off the `k`-subsets vanish). -/
abbrev FormField (n : ℕ) : Type := (Fin n → ℝ) → Finset (Fin n) → ℝ
/-- The sign `ε(j, s) = (-1)^{#{l ∈ s | l < j}}` of moving `dx_j` to its place in `dx_s`. -/
def sgn {n : ℕ} {R : Type*} [Ring R] (j : Fin n) (s : Finset (Fin n)) : R :=
  (-1) ^ (s.filter fun l => l < j).card
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
`ℝᵐ`, over the `m`-face `f` of the simplex `p` with the vertices `p_{e 0}, …, p_{e m}`,
parametrized by `φ(y) = p_{e 0} + Σ_l y_l (p_{e (l+1)} - p_{e 0})` on the reference simplex
`T̂_m = {y ≥ 0, Σ_l y_l ≤ 1}`: the integrand is the `dy_0 ∧ ⋯ ∧ dy_{m-1}` coefficient
`Σ_s ε(s, sᶜ) (φ^*w)_s η_{sᶜ}` of `φ^*w ∧ η`, `(φ^*w)_s(y) = w(φ y)(∂_{s₁}φ, …)` and
`ε(s, sᶜ) = Π_{a ∈ s} ε(a, sᶜ)` the sign of `dy_s ∧ dy_{sᶜ}`. -/
def faceMoment (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1))
    (η : FormField m) (w : FormField n) : ℝ :=
  ∫ y in {y : Fin m → ℝ | (∀ l, 0 ≤ y l) ∧ ∑ l, y l ≤ 1}, ∑ s : Finset (Fin m),
    (∏ a ∈ s, sgn a sᶜ) *
      covEval (w fun i => p (e 0) i + ∑ l, y l * (p (e l.succ) i - p (e 0) i))
        (fun j i => p (e (s.orderEmbOfFin rfl j).succ) i - p (e 0) i) * η y sᶜ

/-! ### The affinely invariant spaces -/

/-- **The classification of the invariant spaces of polynomial differential forms** on `Kⁿ`, `K`
of characteristic `0` ([AFW2006], §3.4, Theorems 3.5–3.6, over `ℝ`): for `0 < k < n` the nonzero
finite-dimensional affinely invariant spaces of `k`-forms are the `dP_{r+1}Λ^{k-1} + κP_sΛ^{k+1}`,
`-1 ≤ s ≤ r`, among them `P_rΛᵏ` and `P_{r+1}⁻Λᵏ`; the summands `dH_{r+1}Λ^{k-1}` and
`κH_{r-1}Λ^{k+1}` of `H_rΛᵏ` are irreducible under `GL(n)` (`AffineInvariantForms`). -/
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
moments `∫_f tr_f ω ∧ η` (`faceMoment`) vanish for all `m`-faces `f` and all
`η ∈ P⁻_{r+k-m}Λ^{m-k}(ℝᵐ)` (resp. `P_{r+k-m-1}Λ^{m-k}(ℝᵐ)`), `k ≤ m < r + k`, is zero, and these
moments, `C(n + 1, m + 1)` faces of each dimension `m`, are as many as `dim P_rΛᵏ(ℝⁿ)` (resp.
`dim P_r⁻Λᵏ(ℝⁿ)`): for bases of the test spaces they are a basis of the dual space. -/
theorem unisolvent (T : Affine.Simplex ℝ (Fin n → ℝ) n) {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    (∀ w ∈ (polyForm ℝ n r k).map evalForm, (∀ m (e : Fin (m + 1) ↪o Fin (n + 1)), k ≤ m →
      m < r + k → ∀ η ∈ (polyFormMinus ℝ m (r + k - m) (m - k)).map evalForm,
        faceMoment T.points e η w = 0) → w = 0) ∧
    (∀ w ∈ (polyFormMinus ℝ n r k).map evalForm, (∀ m (e : Fin (m + 1) ↪o Fin (n + 1)), k ≤ m →
      m < r + k → ∀ η ∈ (polyForm ℝ m (r + k - m - 1) (m - k)).map evalForm,
        faceMoment T.points e η w = 0) → w = 0) ∧
    Module.finrank ℝ (polyForm ℝ n r k) = ∑ m ∈ Finset.range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then Module.finrank ℝ (polyFormMinus ℝ m (r + k - m) (m - k)) else 0) ∧
    Module.finrank ℝ (polyFormMinus ℝ n r k) = ∑ m ∈ Finset.range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then Module.finrank ℝ (polyForm ℝ m (r + k - m - 1) (m - k))
        else 0) := by
  sorry

end FEEC
