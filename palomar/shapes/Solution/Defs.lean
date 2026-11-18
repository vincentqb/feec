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
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but the compared theorems of
`comparator.json`), compiled against Mathlib alone so that their elaborated values are those of
the challenge. The solution imports this module and the bridges to `Feec`, and proves the
theorems (`Solution.lean`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3–§4

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Filter Topology Set LinearPMap MeasureTheory

@[expose] public noncomputable section

universe u

namespace FEEC

/-! ### Form fields on `ℝⁿ` (the shared block) -/

variable {n : ℕ}

-- palomar-shared: FormField
/-- A **form field** on `ℝⁿ`: at each point a coefficient of `dx_s` for every subset `s` of
`Fin n` (a `k`-form when those off the `k`-subsets vanish). -/
abbrev FormField (n : ℕ) : Type := (Fin n → ℝ) → Finset (Fin n) → ℝ
/-- The sign `ε(j, s) = (-1)^{#{l ∈ s | l < j}}` of moving `dx_j` to its place in `dx_s`. -/
def sgn {n : ℕ} {R : Type*} [Ring R] (j : Fin n) (s : Finset (Fin n)) : R :=
  (-1) ^ (s.filter fun l => l < j).card
-- palomar-shared-end: FormField

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

/-! ### Unisolvence -/

end FEEC
