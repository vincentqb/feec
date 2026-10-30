module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but the theorem
`FEEC.periodicTable`), compiled against Mathlib alone so that their elaborated values are those of
the challenge. The solution imports this module, the bridge to `Feec` and proves
`FEEC.periodicTable` (`Solution.lean`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3
* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Finset MvPolynomial Module LinearMap

@[expose] public noncomputable section

universe u

namespace FEEC

variable (K : Type*) [Field K] (n : ℕ)

/-- **Polynomial differential forms** on `Kⁿ`, `ω = Σ_s ω_s dx_s`: the coefficient `ω_s` of
`dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}` for each subset `s = {s₁ < ⋯ < s_k}` of `Fin n`. -/
abbrev PolyForm := Finset (Fin n) → MvPolynomial (Fin n) K

variable {K n} in
/-- The sign `ε(j, s) = (-1)^#{l ∈ s | l < j}`: `dx_j ∧ dx_{s ∖ j} = ε(j, s) dx_s` for `j ∈ s`. -/
def sign (j : Fin n) (s : Finset (Fin n)) : MvPolynomial (Fin n) K := (-1) ^ #{l ∈ s | l < j}

/-- The **exterior derivative** `d = Σⱼ dx_j ∧ ∂ⱼ`, `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂ⱼ ω_{s ∖ j}`. -/
def extDeriv : PolyForm K n →ₗ[K] PolyForm K n where
  toFun ω s := ∑ j ∈ s, sign j s * pderiv j (ω (s.erase j))
  map_add' ω η := by ext s : 1; simp [sum_add_distrib, mul_add]
  map_smul' c ω := by ext s : 1; simp [smul_sum]

/-- The **Koszul differential** `κ = Σⱼ xⱼ ι_{∂ⱼ}`, the contraction with the position vector field,
`(κω)_s = Σ_{j ∉ s} ε(j, s) xⱼ ω_{s ∪ j}`. -/
def koszul : PolyForm K n →ₗ[K] PolyForm K n where
  toFun ω s := ∑ j ∈ sᶜ, sign j s * X j * ω (insert j s)
  map_add' ω η := by ext s : 1; simp [sum_add_distrib, mul_add]
  map_smul' c ω := by ext s : 1; simp [smul_sum]

/-- The `k`-forms with coefficients `ω_s ∈ S s` (and `ω_s = 0` unless `#s = k`). -/
def kForm (k : ℕ) (S : Finset (Fin n) → Submodule K (MvPolynomial (Fin n) K)) :
    Submodule K (PolyForm K n) :=
  Submodule.pi Set.univ fun s => if #s = k then S s else ⊥

/-- `H_rΛᵏ`: the `k`-forms with homogeneous coefficients of degree `r`. -/
def homForm (r k : ℕ) : Submodule K (PolyForm K n) :=
  kForm K n k fun _ => homogeneousSubmodule (Fin n) K r

/-- `P_rΛᵏ`: the `k`-forms with polynomial coefficients of degree at most `r`. -/
def polyForm (r k : ℕ) : Submodule K (PolyForm K n) :=
  kForm K n k fun _ => restrictTotalDegree (Fin n) K r

/-- `P_r⁻Λᵏ = P_{r-1}Λᵏ + κ H_{r-1}Λ^{k+1}`, the trimmed polynomial `k`-forms (for `r ≥ 1`). -/
def polyFormMinus (r k : ℕ) : Submodule K (PolyForm K n) :=
  polyForm K n (r - 1) k ⊔ (homForm K n (r - 1) (k + 1)).map (koszul K n)

/-- `Q_r⁻Λᵏ`: the `k`-forms whose coefficient `ω_s` is a combination of monomials `x^α` with
`α_j ≤ r - 1` for `j ∈ s` and `α_j ≤ r` for `j ∉ s`. -/
def cubeFormMinus (r k : ℕ) : Submodule K (PolyForm K n) :=
  kForm K n k fun s => restrictSupport K {α | ∀ j, α j + (if j ∈ s then 1 else 0) ≤ r}

/-- **The algebra of the periodic table** over `K` in dimension `n`: dimensions, exactness of the
polynomial de Rham complexes, the homotopy formula and the Koszul decompositions. -/
structure PeriodicTable : Prop where
  /-- `dim P_rΛᵏ = C(r + n, r + k) C(r + k, k)` -/
  finrank_polyForm (r k : ℕ) :
    finrank K (polyForm K n r k) = (r + n).choose (r + k) * (r + k).choose k
  /-- `dim P_r⁻Λᵏ = C(r + n, r + k) C(r + k - 1, k)` -/
  finrank_polyFormMinus [CharZero K] (r k : ℕ) (hr : 1 ≤ r) :
    finrank K (polyFormMinus K n r k) = (r + n).choose (r + k) * (r + k - 1).choose k
  /-- `dim Q_r⁻Λᵏ = C(n, k) rᵏ (r + 1)ⁿ⁻ᵏ` -/
  finrank_cubeFormMinus (r k : ℕ) :
    finrank K (cubeFormMinus K n r k) = n.choose k * r ^ k * (r + 1) ^ (n - k)
  /-- `P_{r+1}Λᵏ → P_rΛ^{k+1} → P_{r-1}Λ^{k+2}` is exact -/
  exact_polyForm [CharZero K] (r k : ℕ) :
    ker (extDeriv K n) ⊓ polyForm K n r (k + 1) = (polyForm K n (r + 1) k).map (extDeriv K n)
  /-- `P_r⁻Λᵏ → P_r⁻Λ^{k+1} → P_r⁻Λ^{k+2}` is exact -/
  exact_polyFormMinus [CharZero K] (r k : ℕ) (hr : 1 ≤ r) :
    ker (extDeriv K n) ⊓ polyFormMinus K n r (k + 1) =
      (polyFormMinus K n r k).map (extDeriv K n)
  /-- `Q_r⁻Λᵏ → Q_r⁻Λ^{k+1} → Q_r⁻Λ^{k+2}` is exact -/
  exact_cubeFormMinus [CharZero K] (r k : ℕ) :
    ker (extDeriv K n) ⊓ cubeFormMinus K n r (k + 1) =
      (cubeFormMinus K n r k).map (extDeriv K n)
  /-- the closed `0`-forms of `P_rΛ⁰` are the constants `P_0Λ⁰` -/
  closed_polyForm [CharZero K] (r : ℕ) :
    ker (extDeriv K n) ⊓ polyForm K n r 0 = polyForm K n 0 0
  /-- the closed `0`-forms of `P_r⁻Λ⁰` are the constants -/
  closed_polyFormMinus [CharZero K] (r : ℕ) (hr : 1 ≤ r) :
    ker (extDeriv K n) ⊓ polyFormMinus K n r 0 = polyForm K n 0 0
  /-- the closed `0`-forms of `Q_r⁻Λ⁰` are the constants -/
  closed_cubeFormMinus [CharZero K] (r : ℕ) :
    ker (extDeriv K n) ⊓ cubeFormMinus K n r 0 = polyForm K n 0 0
  /-- the homotopy formula `(dκ + κd) ω = (r + k) ω` for `ω ∈ H_rΛᵏ` -/
  homotopy (r k : ℕ) (ω : PolyForm K n) (hω : ω ∈ homForm K n r k) :
    extDeriv K n (koszul K n ω) + koszul K n (extDeriv K n ω) = ((r + k : ℕ) : K) • ω
  /-- `H_{r+1}Λ⁰ = κ H_rΛ¹` -/
  homForm_zero_eq [CharZero K] (r : ℕ) :
    (homForm K n r 1).map (koszul K n) = homForm K n (r + 1) 0
  /-- `P_rΛ^{k+1} = P_r⁻Λ^{k+1} ⊕ d H_{r+1}Λᵏ` -/
  polyForm_eq [CharZero K] (r k : ℕ) (hr : 1 ≤ r) :
    polyFormMinus K n r (k + 1) ⊔ (homForm K n (r + 1) k).map (extDeriv K n) =
        polyForm K n r (k + 1) ∧
      Disjoint (polyFormMinus K n r (k + 1)) ((homForm K n (r + 1) k).map (extDeriv K n))
  /-- `H_{r+1}Λ^{k+1} = κ H_rΛ^{k+2} ⊕ d H_{r+2}Λᵏ` -/
  homForm_eq [CharZero K] (r k : ℕ) :
    (homForm K n r (k + 2)).map (koszul K n) ⊔ (homForm K n (r + 2) k).map (extDeriv K n) =
        homForm K n (r + 1) (k + 1) ∧
      Disjoint ((homForm K n r (k + 2)).map (koszul K n))
        ((homForm K n (r + 2) k).map (extDeriv K n))

/-! ### The theorem -/

end FEEC
