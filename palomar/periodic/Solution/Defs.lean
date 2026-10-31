module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but the theorem
`FEEC.periodicTable`), compiled against Mathlib alone so that their elaborated values are those of
the challenge. The solution imports this module, the bridge to `Feec` and proves
`FEEC.periodicTable` (`Solution.lean`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.1–§3.3, §3.5
* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §5

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Finset MvPolynomial Module LinearMap CategoryTheory
open scoped TensorProduct

@[expose] public noncomputable section

universe u

namespace FEEC

variable (K : Type u) [Field K] (n : ℕ)

/-- The coordinate covector `dx_j` of `Kⁿ`. -/
def dx (j : Fin n) : Module.Dual K (Fin n → K) := LinearMap.proj j

/-- **Polynomial differential forms** on `Kⁿ`, `PΛ(Kⁿ) = P(Kⁿ) ⊗ Λ(Kⁿ)*`: polynomial combinations
of the constant forms `dx_{σ₁} ∧ ⋯ ∧ dx_{σ_k}`, elements of the exterior algebra of the covectors
(`ω = Σ p ⊗ θ` is the form `x ↦ Σ p(x) θ`, the wedge product is the product of the algebra). -/
abbrev Form := MvPolynomial (Fin n) K ⊗[K] ExteriorAlgebra K (Module.Dual K (Fin n → K))

/-- The **exterior derivative** `d = Σⱼ dx_j ∧ ∂ⱼ`: `d (p ⊗ θ) = Σⱼ ∂ⱼp ⊗ (dx_j ∧ θ)`. -/
def extDeriv : Form K n →ₗ[K] Form K n :=
  ∑ j, TensorProduct.map (pderiv j).toLinearMap
    (LinearMap.mulLeft K (ExteriorAlgebra.ι K (dx K n j)))

/-- The **Koszul differential** `κ = Σⱼ xⱼ ι_{∂ⱼ}`, the contraction with the position vector field
`x = Σⱼ xⱼ ∂ⱼ`: `κ (p ⊗ θ) = Σⱼ xⱼ p ⊗ ι_{eⱼ} θ`, `ι_{eⱼ}` Mathlib's contraction with the vector
`eⱼ` (`ι_{eⱼ} dx_l = δ_{jl}`). -/
def koszul : Form K n →ₗ[K] Form K n :=
  ∑ j, TensorProduct.map (LinearMap.mulLeft K (X j))
    (CliffordAlgebra.contractLeft (Module.Dual.eval K (Fin n → K) (Pi.single j 1)))

/-- `S Λᵏ = S ⊗ Λᵏ(Kⁿ)*`: the `k`-forms with coefficients in the space `S` of polynomials. -/
def kForm (S : Submodule K (MvPolynomial (Fin n) K)) (k : ℕ) : Submodule K (Form K n) :=
  range (TensorProduct.mapIncl S (⋀[K]^k (Module.Dual K (Fin n → K))))

/-- `H_rΛᵏ`: the `k`-forms with homogeneous coefficients of degree `r`. -/
def homForm (r k : ℕ) : Submodule K (Form K n) :=
  kForm K n (homogeneousSubmodule (Fin n) K r) k

/-- `P_rΛᵏ`: the `k`-forms with polynomial coefficients of degree at most `r`. -/
def polyForm (r k : ℕ) : Submodule K (Form K n) :=
  kForm K n (restrictTotalDegree (Fin n) K r) k

/-- `P_r⁻Λᵏ = P_{r-1}Λᵏ + κ H_{r-1}Λ^{k+1}`, the trimmed polynomial `k`-forms (`r ≥ 1`), and
`P_0⁻Λᵏ = 0` ([AFW2006], §3.3). -/
def polyFormMinus : ℕ → ℕ → Submodule K (Form K n)
  | 0, _ => ⊥
  | r + 1, k => polyForm K n r k ⊔ (homForm K n r (k + 1)).map (koszul K n)

/-- `Q_b⁻Λᵏ = ⨁_σ [⊗ⱼ P_{b_j - [j ∈ σ]}(I)] dx_σ`: the sums of `p dx_{σ₁} ∧ ⋯ ∧ dx_{σ_k}`,
`σ₁ < ⋯ < σ_k`, `p` a combination of monomials `x^α` with `α_j ≤ b_j - 1` for `j ∈ σ` and
`α_j ≤ b_j` otherwise; `Q_r⁻Λᵏ` for `b = (r, …, r)` ([ArnoldBoffiBonizzoni2015], §5). -/
def cubeFormMinus (b : Fin n → ℕ) (k : ℕ) : Submodule K (Form K n) :=
  ⨆ (σ : Fin k → Fin n) (_ : StrictMono σ),
    (restrictSupport K {α | ∀ j, α j + (if j ∈ Set.range σ then 1 else 0) ≤ b j}).map
      ((TensorProduct.mk K _ _).flip (ExteriorAlgebra.ιMulti K k fun i => dx K n (σ i)))

/-- The spaces `P_{r-k}Λᵏ` of the complex `P_rΛ⁰ → P_{r-1}Λ¹ → ⋯ → P_0Λʳ → 0` (`0` for
`k > r`). -/
def polyFormSeq (r k : ℕ) : Submodule K (Form K n) :=
  if k ≤ r then polyForm K n (r - k) k else ⊥

variable {K n} in
/-- The cochain complex `S 0 → S 1 → S 2 → ⋯` of `K`-vector spaces of a family of spaces of forms
with `d S_k ⊆ S_{k+1}`, the differential the restriction of `d` (`d² = 0`). -/
def deRham (hd : extDeriv K n ∘ₗ extDeriv K n = 0) {S : ℕ → Submodule K (Form K n)}
    (hS : ∀ k, (S k).map (extDeriv K n) ≤ S (k + 1)) : CochainComplex (ModuleCat.{u} K) ℕ :=
  CochainComplex.of (fun k => ModuleCat.of K (S k))
    (fun k => ModuleCat.ofHom
      ((extDeriv K n).restrict fun _ h => hS k (Submodule.mem_map_of_mem h)))
    fun _ => by ext ω; exact LinearMap.congr_fun hd ω.1

/-- **The algebra of the periodic table** over `K` in dimension `n`: dimensions, the polynomial
de Rham complexes and their exactness, the homotopy formula and the Koszul decompositions. -/
structure PeriodicTable : Prop where
  /-- `dim P_rΛᵏ = C(r + n, r + k) C(r + k, k)` -/
  finrank_polyForm (r k : ℕ) :
    finrank K (polyForm K n r k) = (r + n).choose (r + k) * (r + k).choose k
  /-- `dim H_rΛᵏ = C(n, k) C(n + r - 1, r)` (`dim H_r(Kⁿ) = dim P_r(Kⁿ⁻¹)`) -/
  finrank_homForm (r k : ℕ) :
    finrank K (homForm K n r k) = n.choose k * (n + r - 1).choose r
  /-- `dim P_r⁻Λᵏ = C(r + n, r + k) C(r + k - 1, k)` (`r ≥ 1`) -/
  finrank_polyFormMinus [CharZero K] (r k : ℕ) (hr : 1 ≤ r) :
    finrank K (polyFormMinus K n r k) = (r + n).choose (r + k) * (r + k - 1).choose k
  /-- `dim κ H_rΛ^{k+1} = dim d H_{r+1}Λᵏ = C(n + r, r + k + 1) C(r + k, k)` -/
  finrank_map_koszul_homForm [CharZero K] (r k : ℕ) :
    finrank K ((homForm K n r (k + 1)).map (koszul K n)) =
        (n + r).choose (r + k + 1) * (r + k).choose k ∧
      finrank K ((homForm K n (r + 1) k).map (extDeriv K n)) =
        (n + r).choose (r + k + 1) * (r + k).choose k
  /-- `dim Q_b⁻Λᵏ = Σ_{#s = k} Πⱼ (b_j + 1 - [j ∈ s])` -/
  finrank_cubeFormMinus (b : Fin n → ℕ) (k : ℕ) :
    finrank K (cubeFormMinus K n b k) =
      ∑ s ∈ powersetCard k univ, ∏ j, (b j + 1 - if j ∈ s then 1 else 0)
  /-- `dim Q_r⁻Λᵏ = C(n, k) rᵏ (r + 1)ⁿ⁻ᵏ` -/
  finrank_cubeFormMinus_const (r k : ℕ) :
    finrank K (cubeFormMinus K n (fun _ => r) k) = n.choose k * r ^ k * (r + 1) ^ (n - k)
  /-- `d ∘ d = 0` -/
  extDeriv_comp_extDeriv : extDeriv K n ∘ₗ extDeriv K n = 0
  /-- `κ ∘ κ = 0` -/
  koszul_comp_koszul : koszul K n ∘ₗ koszul K n = 0
  /-- the Leibniz rule `κ(ω ∧ η) = κω ∧ η + (-1)ᵏ ω ∧ κη` for a `k`-form `ω` -/
  koszul_mul (k : ℕ) (ω η : Form K n) (hω : ω ∈ kForm K n ⊤ k) :
    koszul K n (ω * η) = koszul K n ω * η + (-1 : K) ^ k • (ω * koszul K n η)
  /-- `P_rΛᵏ ∧ P_sΛˡ ⊆ P_{r+s}Λ^{k+l}` -/
  polyForm_mul_le (r s k l : ℕ) :
    polyForm K n r k * polyForm K n s l ≤ polyForm K n (r + s) (k + l)
  /-- `P_r⁻Λᵏ ∧ P_s⁻Λˡ ⊆ P_{r+s}⁻Λ^{k+l}` -/
  polyFormMinus_mul_le [CharZero K] (r s k l : ℕ) :
    polyFormMinus K n r k * polyFormMinus K n s l ≤ polyFormMinus K n (r + s) (k + l)
  /-- `P_s P_r⁻Λᵏ ⊆ P_{r+s}⁻Λᵏ` -/
  polyForm_zero_mul_le [CharZero K] (r s k : ℕ) :
    polyForm K n s 0 * polyFormMinus K n r k ≤ polyFormMinus K n (r + s) k
  /-- `d P_{r-k}Λᵏ ⊆ P_{r-k-1}Λ^{k+1}` -/
  map_polyFormSeq_le (r k : ℕ) :
    (polyFormSeq K n r k).map (extDeriv K n) ≤ polyFormSeq K n r (k + 1)
  /-- `d P_r⁻Λᵏ ⊆ P_r⁻Λ^{k+1}` -/
  map_polyFormMinus_le (r k : ℕ) :
    (polyFormMinus K n r k).map (extDeriv K n) ≤ polyFormMinus K n r (k + 1)
  /-- `d Q_b⁻Λᵏ ⊆ Q_b⁻Λ^{k+1}` -/
  map_cubeFormMinus_le (b : Fin n → ℕ) (k : ℕ) :
    (cubeFormMinus K n b k).map (extDeriv K n) ≤ cubeFormMinus K n b (k + 1)
  /-- `P_rΛ⁰ → P_{r-1}Λ¹ → ⋯ → P_0Λʳ → 0` is a subcomplex of `P_r⁻Λ⁰ → P_r⁻Λ¹ → ⋯` (`r ≥ 1`) -/
  polyFormSeq_le_polyFormMinus [CharZero K] (r k : ℕ) (hr : 1 ≤ r) :
    polyFormSeq K n r k ≤ polyFormMinus K n r k
  /-- `P_rΛ⁰ → P_{r-1}Λ¹ → ⋯ → P_0Λʳ → 0` is exact in positive degree -/
  exactAt_polyForm [CharZero K] (r k : ℕ) :
    (deRham extDeriv_comp_extDeriv (map_polyFormSeq_le r)).ExactAt (k + 1)
  /-- `P_r⁻Λ⁰ → P_r⁻Λ¹ → ⋯ → P_r⁻Λⁿ` is exact in positive degree -/
  exactAt_polyFormMinus [CharZero K] (r k : ℕ) :
    (deRham extDeriv_comp_extDeriv (map_polyFormMinus_le r)).ExactAt (k + 1)
  /-- `Q_b⁻Λ⁰ → Q_b⁻Λ¹ → ⋯ → Q_b⁻Λⁿ` is exact in positive degree -/
  exactAt_cubeFormMinus [CharZero K] (b : Fin n → ℕ) (k : ℕ) :
    (deRham extDeriv_comp_extDeriv (map_cubeFormMinus_le b)).ExactAt (k + 1)
  /-- the closed `0`-forms of `P_rΛ⁰` are the constants `P_0Λ⁰` -/
  closed_polyForm [CharZero K] (r : ℕ) :
    ker (extDeriv K n) ⊓ polyForm K n r 0 = polyForm K n 0 0
  /-- the closed `0`-forms of `P_r⁻Λ⁰` are the constants (`r ≥ 1`) -/
  closed_polyFormMinus [CharZero K] (r : ℕ) (hr : 1 ≤ r) :
    ker (extDeriv K n) ⊓ polyFormMinus K n r 0 = polyForm K n 0 0
  /-- the closed `0`-forms of `Q_b⁻Λ⁰` are the constants -/
  closed_cubeFormMinus [CharZero K] (b : Fin n → ℕ) :
    ker (extDeriv K n) ⊓ cubeFormMinus K n b 0 = polyForm K n 0 0
  /-- `H_rΛ⁰ → H_{r-1}Λ¹ → ⋯ → H_{r-n}Λⁿ` is exact in positive degree:
  `ker d ∩ H_rΛ^{k+1} ⊆ d H_{r+1}Λᵏ` -/
  ker_extDeriv_inf_homForm_le [CharZero K] (r k : ℕ) :
    ker (extDeriv K n) ⊓ homForm K n r (k + 1) ≤ (homForm K n (r + 1) k).map (extDeriv K n)
  /-- and in degree `0` for `r ≥ 1`: `ker d ∩ H_{r+1}Λ⁰ = 0` -/
  ker_extDeriv_inf_homForm_zero [CharZero K] (r : ℕ) :
    ker (extDeriv K n) ⊓ homForm K n (r + 1) 0 = ⊥
  /-- the Koszul complex `0 → H_{r-n}Λⁿ → ⋯ → H_{r-1}Λ¹ → H_rΛ⁰ → 0` is exact (`r ≥ 1`):
  `ker κ ∩ H_{r+1}Λᵏ ⊆ κ H_rΛ^{k+1}` -/
  ker_koszul_inf_homForm_le [CharZero K] (r k : ℕ) :
    ker (koszul K n) ⊓ homForm K n (r + 1) k ≤ (homForm K n r (k + 1)).map (koszul K n)
  /-- and `ker κ ∩ H_0Λ^{k+1} = 0` -/
  ker_koszul_inf_homForm_zero [CharZero K] (k : ℕ) :
    ker (koszul K n) ⊓ homForm K n 0 (k + 1) = ⊥
  /-- the Koszul complex `0 → P_{r-n}Λⁿ → ⋯ → P_{r-1}Λ¹ → P_rΛ⁰ → 0` is exact in positive
  degree: `ker κ ∩ P_{r+1}Λ^{k+1} ⊆ κ P_rΛ^{k+2}` -/
  ker_koszul_inf_polyForm_le [CharZero K] (r k : ℕ) :
    ker (koszul K n) ⊓ polyForm K n (r + 1) (k + 1) ≤ (polyForm K n r (k + 2)).map (koszul K n)
  /-- and `ker κ ∩ P_0Λ^{k+1} = 0` -/
  ker_koszul_inf_polyForm_zero [CharZero K] (k : ℕ) :
    ker (koszul K n) ⊓ polyForm K n 0 (k + 1) = ⊥
  /-- its cohomology at `P_{r+1}Λ⁰` is the constants: `P_{r+1}Λ⁰ = κ P_rΛ¹ ⊕ P_0Λ⁰` -/
  polyForm_zero_eq_koszul [CharZero K] (r : ℕ) :
    (polyForm K n r 1).map (koszul K n) ⊔ polyForm K n 0 0 = polyForm K n (r + 1) 0 ∧
      Disjoint ((polyForm K n r 1).map (koszul K n)) (polyForm K n 0 0)
  /-- the homotopy formula `(dκ + κd) ω = (r + k) ω` for `ω ∈ H_rΛᵏ` -/
  homotopy (r k : ℕ) (ω : Form K n) (hω : ω ∈ homForm K n r k) :
    extDeriv K n (koszul K n ω) + koszul K n (extDeriv K n ω) = ((r + k : ℕ) : K) • ω
  /-- `d` is injective on the range of `κ`: `dκω = 0 → κω = 0` -/
  koszul_eq_zero_of_extDeriv_koszul [CharZero K] (ω : Form K n)
    (h : extDeriv K n (koszul K n ω) = 0) : koszul K n ω = 0
  /-- `κ` is injective on the range of `d`: `κdω = 0 → dω = 0` -/
  extDeriv_eq_zero_of_koszul_extDeriv [CharZero K] (ω : Form K n)
    (h : koszul K n (extDeriv K n ω) = 0) : extDeriv K n ω = 0
  /-- `H_{r+1}Λ^{k+1} = κ H_rΛ^{k+2} ⊕ d H_{r+2}Λᵏ` -/
  homForm_eq [CharZero K] (r k : ℕ) :
    (homForm K n r (k + 2)).map (koszul K n) ⊔ (homForm K n (r + 2) k).map (extDeriv K n) =
        homForm K n (r + 1) (k + 1) ∧
      Disjoint ((homForm K n r (k + 2)).map (koszul K n))
        ((homForm K n (r + 2) k).map (extDeriv K n))
  /-- `H_{r+1}Λ⁰ = κ H_rΛ¹` -/
  homForm_zero_eq [CharZero K] (r : ℕ) :
    (homForm K n r 1).map (koszul K n) = homForm K n (r + 1) 0
  /-- `H_0Λ^{k+1} = d H_1Λᵏ` -/
  homForm_zero_left_eq [CharZero K] (k : ℕ) :
    (homForm K n 1 k).map (extDeriv K n) = homForm K n 0 (k + 1)
  /-- `P_{r+1}Λ^{k+1} = κ P_rΛ^{k+2} ⊕ d P_{r+2}Λᵏ` -/
  polyForm_eq_koszul [CharZero K] (r k : ℕ) :
    (polyForm K n r (k + 2)).map (koszul K n) ⊔ (polyForm K n (r + 2) k).map (extDeriv K n) =
        polyForm K n (r + 1) (k + 1) ∧
      Disjoint ((polyForm K n r (k + 2)).map (koszul K n))
        ((polyForm K n (r + 2) k).map (extDeriv K n))
  /-- `P_0Λ^{k+1} = d P_1Λᵏ` -/
  polyForm_zero_left_eq [CharZero K] (k : ℕ) :
    (polyForm K n 1 k).map (extDeriv K n) = polyForm K n 0 (k + 1)
  /-- `P_rΛ^{k+1} = P_r⁻Λ^{k+1} ⊕ d H_{r+1}Λᵏ` -/
  polyForm_eq [CharZero K] (r k : ℕ) :
    polyFormMinus K n r (k + 1) ⊔ (homForm K n (r + 1) k).map (extDeriv K n) =
        polyForm K n r (k + 1) ∧
      Disjoint (polyFormMinus K n r (k + 1)) ((homForm K n (r + 1) k).map (extDeriv K n))
  /-- the sum `P_{r+1}⁻Λᵏ = P_rΛᵏ ⊕ κ H_rΛ^{k+1}` is direct -/
  disjoint_polyForm_map_koszul (r k : ℕ) :
    Disjoint (polyForm K n r k) ((homForm K n r (k + 1)).map (koszul K n))
  /-- `P_{r+1}⁻Λᵏ = P_rΛᵏ + κ P_rΛ^{k+1}` -/
  polyFormMinus_eq_sup_map_koszul (r k : ℕ) :
    polyFormMinus K n (r + 1) k = polyForm K n r k ⊔ (polyForm K n r (k + 1)).map (koszul K n)
  /-- `d P_r⁻Λᵏ = d P_rΛᵏ` -/
  map_extDeriv_polyFormMinus [CharZero K] (r k : ℕ) :
    (polyFormMinus K n r k).map (extDeriv K n) = (polyForm K n r k).map (extDeriv K n)
  /-- `P_r⁻Λ⁰ = P_rΛ⁰` (`r ≥ 1`) -/
  polyFormMinus_zero [CharZero K] (r : ℕ) (hr : 1 ≤ r) :
    polyFormMinus K n r 0 = polyForm K n r 0
  /-- `P_r⁻Λⁿ = P_{r-1}Λⁿ` (`r ≥ 1`) -/
  polyFormMinus_top [CharZero K] (r : ℕ) (hr : 1 ≤ r) :
    polyFormMinus K n r n = polyForm K n (r - 1) n
  /-- `P_r⁻Λᵏ = {ω ∈ P_rΛᵏ | κω ∈ P_rΛᵏ⁻¹}` (`r + k ≥ 1`), the equivalent definition -/
  polyFormMinus_eq_inf_comap [CharZero K] (r k : ℕ) (hrk : 1 ≤ r + k) :
    polyFormMinus K n r k = polyForm K n r k ⊓ (polyForm K n r (k - 1)).comap (koszul K n)
  /-- `P_{r-1}Λᵏ ⊊ P_r⁻Λᵏ` (`r ≥ 1`, `k < n`) -/
  polyForm_lt_polyFormMinus (r k : ℕ) (hr : 1 ≤ r) (hk : k < n) :
    polyForm K n (r - 1) k < polyFormMinus K n r k
  /-- `P_r⁻Λ^{k+1} ⊊ P_rΛ^{k+1}` (`r ≥ 1`, `k < n`) -/
  polyFormMinus_lt_polyForm [CharZero K] (r k : ℕ) (hr : 1 ≤ r) (hk : k < n) :
    polyFormMinus K n r (k + 1) < polyForm K n r (k + 1)
  /-- a closed form of `P_{r+1}⁻Λᵏ` lies in `P_rΛᵏ` -/
  ker_inf_polyFormMinus_le [CharZero K] (r k : ℕ) :
    ker (extDeriv K n) ⊓ polyFormMinus K n (r + 1) k ≤ polyForm K n r k

/-! ### The theorem -/

end FEEC
