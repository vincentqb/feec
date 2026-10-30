module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The algebra of the periodic table of the finite elements

The finite element spaces of differential forms of the periodic table ([ArnoldLogg2014]) are
built from four families of polynomial differential forms on `Kⁿ` ([AFW2006], §3;
[ArnoldBoffiBonizzoni2015], §3): `k`-forms `ω = Σ_{#s = k} ω_s dx_s` whose coefficients are

* `H_rΛᵏ`: homogeneous polynomials of degree `r`;
* `P_rΛᵏ`: polynomials of degree at most `r`;
* `P_r⁻Λᵏ = P_{r-1}Λᵏ + κ H_{r-1}Λ^{k+1}` (`r ≥ 1`), the trimmed spaces, `κ` the Koszul
  differential (contraction with the position vector field `x`);
* `Q_r⁻Λᵏ`: the tensor-product spaces of the cube, `ω_s` of degree at most `r - 1` in the
  variables `x_j`, `j ∈ s`, and at most `r` in the others.

The theorem below (`FEEC.periodicTable`) states, over every field of characteristic `0` and in
every dimension `n`, form degree `k` and polynomial degree `r`:

1. the dimensions `dim P_rΛᵏ = C(r + n, r + k) C(r + k, k)`,
   `dim P_r⁻Λᵏ = C(r + n, r + k) C(r + k - 1, k)` and `dim Q_r⁻Λᵏ = C(n, k) rᵏ (r + 1)ⁿ⁻ᵏ`;
2. the exactness of the polynomial de Rham complexes
   `P_rΛ⁰ → P_{r-1}Λ¹ → ⋯ → P_{r-n}Λⁿ`, `P_r⁻Λ⁰ → P_r⁻Λ¹ → ⋯ → P_r⁻Λⁿ` and
   `Q_r⁻Λ⁰ → Q_r⁻Λ¹ → ⋯ → Q_r⁻Λⁿ`: the closed forms are the images of `d` in positive degree,
   the constants in degree `0`;
3. the Koszul decompositions `P_{r+1}⁻Λᵏ = P_rΛᵏ ⊕ κ H_rΛ^{k+1}`,
   `P_rΛᵏ = P_r⁻Λᵏ ⊕ d H_{r+1}Λᵏ⁻¹` and `H_rΛᵏ = κ H_{r-1}Λ^{k+1} ⊕ d H_{r+1}Λᵏ⁻¹`
   (`r, k ≥ 1`).

A form is the function `s ↦ ω_s` on the subsets `s = {s₁ < ⋯ < s_k}` of `Fin n`, the coefficients
of `ω` in the basis `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}`; a `k`-form vanishes off `#s = k`.

## References

* [D. N. Arnold, A. Logg, *Periodic table of the finite elements*][ArnoldLogg2014]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3 (the Koszul complex and the spaces `P_rΛᵏ`, `P_r⁻Λᵏ`)
* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §3 (the spaces `Q_r⁻Λᵏ`)

Bibliography: [references.bib](../../docs/references.bib)
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
polynomial de Rham complexes and the Koszul decompositions. -/
structure PeriodicTable : Prop where
  /-- `dim P_rΛᵏ = C(r + n, r + k) C(r + k, k)` -/
  finrank_polyForm (r k : ℕ) :
    finrank K (polyForm K n r k) = (r + n).choose (r + k) * (r + k).choose k
  /-- `dim P_r⁻Λᵏ = C(r + n, r + k) C(r + k - 1, k)` -/
  finrank_polyFormMinus (r k : ℕ) (hr : 1 ≤ r) :
    finrank K (polyFormMinus K n r k) = (r + n).choose (r + k) * (r + k - 1).choose k
  /-- `dim Q_r⁻Λᵏ = C(n, k) rᵏ (r + 1)ⁿ⁻ᵏ` -/
  finrank_cubeFormMinus (r k : ℕ) :
    finrank K (cubeFormMinus K n r k) = n.choose k * r ^ k * (r + 1) ^ (n - k)
  /-- `P_{r+1}Λᵏ → P_rΛ^{k+1} → P_{r-1}Λ^{k+2}` is exact -/
  exact_polyForm (r k : ℕ) :
    ker (extDeriv K n) ⊓ polyForm K n r (k + 1) = (polyForm K n (r + 1) k).map (extDeriv K n)
  /-- `P_r⁻Λᵏ → P_r⁻Λ^{k+1} → P_r⁻Λ^{k+2}` is exact -/
  exact_polyFormMinus (r k : ℕ) (hr : 1 ≤ r) :
    ker (extDeriv K n) ⊓ polyFormMinus K n r (k + 1) =
      (polyFormMinus K n r k).map (extDeriv K n)
  /-- `Q_r⁻Λᵏ → Q_r⁻Λ^{k+1} → Q_r⁻Λ^{k+2}` is exact -/
  exact_cubeFormMinus (r k : ℕ) :
    ker (extDeriv K n) ⊓ cubeFormMinus K n r (k + 1) =
      (cubeFormMinus K n r k).map (extDeriv K n)
  /-- the closed `0`-forms of `P_rΛ⁰` are the constants `P_0Λ⁰` -/
  closed_polyForm (r : ℕ) : ker (extDeriv K n) ⊓ polyForm K n r 0 = polyForm K n 0 0
  /-- the closed `0`-forms of `P_r⁻Λ⁰` are the constants -/
  closed_polyFormMinus (r : ℕ) (hr : 1 ≤ r) :
    ker (extDeriv K n) ⊓ polyFormMinus K n r 0 = polyForm K n 0 0
  /-- the closed `0`-forms of `Q_r⁻Λ⁰` are the constants -/
  closed_cubeFormMinus (r : ℕ) : ker (extDeriv K n) ⊓ cubeFormMinus K n r 0 = polyForm K n 0 0
  /-- `P_{r+1}⁻Λᵏ = P_rΛᵏ ⊕ κ H_rΛ^{k+1}`: the sum defining `P_{r+1}⁻Λᵏ` is direct -/
  disjoint_koszul (r k : ℕ) :
    Disjoint (polyForm K n r k) ((homForm K n r (k + 1)).map (koszul K n))
  /-- `P_rΛ^{k+1} = P_r⁻Λ^{k+1} ⊕ d H_{r+1}Λᵏ` -/
  polyForm_eq (r k : ℕ) (hr : 1 ≤ r) :
    polyFormMinus K n r (k + 1) ⊔ (homForm K n (r + 1) k).map (extDeriv K n) =
        polyForm K n r (k + 1) ∧
      Disjoint (polyFormMinus K n r (k + 1)) ((homForm K n (r + 1) k).map (extDeriv K n))
  /-- `H_{r+1}Λ^{k+1} = κ H_rΛ^{k+2} ⊕ d H_{r+2}Λᵏ` -/
  homForm_eq (r k : ℕ) :
    (homForm K n r (k + 2)).map (koszul K n) ⊔ (homForm K n (r + 2) k).map (extDeriv K n) =
        homForm K n (r + 1) (k + 1) ∧
      Disjoint ((homForm K n r (k + 2)).map (koszul K n))
        ((homForm K n (r + 2) k).map (extDeriv K n))

/-! ### The theorem -/

/-- **The algebra of the periodic table of the finite elements** ([AFW2006], §3;
[ArnoldBoffiBonizzoni2015], §3). Over every field of characteristic `0`, in every dimension `n`,
the spaces `P_rΛᵏ`, `P_r⁻Λᵏ` and `Q_r⁻Λᵏ` have the dimensions of the periodic table, their
polynomial de Rham complexes are exact with the constants as cohomology in degree `0`, and the
Koszul decompositions hold (`PeriodicTable`). -/
theorem periodicTable (K : Type u) [Field K] [CharZero K] (n : ℕ) : PeriodicTable K n := by
  sorry

end FEEC
