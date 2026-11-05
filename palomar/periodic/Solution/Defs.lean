module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but the theorems
`FEEC.affineInvariantForms`, `FEEC.charZero_iff_classification`,
`FEEC.charZero_iff_closed_eq_exact` and `FEEC.periodicTable`), compiled against Mathlib alone so
that their elaborated values are those of the challenge. The solution imports this module and the
bridges to `Feec`, and proves the theorems (`Solution.lean`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.1–§3.5, §5 (admissible sequences)
* [D. N. Arnold, A. Logg, *Periodic table of the finite elements*][ArnoldLogg2014]
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

/-! ### Invariant spaces of polynomial forms on `Kⁿ` ([AFW2006], §3.4) -/

/-- The **pullback** of polynomial forms on `Kⁿ` along the affine map `φ(x) = B x + b`:
`φ^*(p ⊗ θ) = (p ∘ φ) ⊗ Λ(Bᵀ) θ`, with `Bᵀ ξ = ξ ∘ B` on the covectors. -/
def pullback (B : Matrix (Fin n) (Fin n) K) (b : Fin n → K) : Form K n →ₗ[K] Form K n :=
  TensorProduct.map (aeval fun i => ∑ l, C (B i l) * X l + C (b i)).toLinearMap
    (ExteriorAlgebra.map (Matrix.toLin' B).dualMap).toLinearMap

/-- `V` is mapped into itself by the pullback along every affine map `φ : Kⁿ → Kⁿ`. -/
def IsAffineInvariant (V : Submodule K (Form K n)) : Prop :=
  ∀ B b, V.map (pullback K n B b) ≤ V

/-- `V` is mapped into itself by the pullback along every linear map `x ↦ B x` of `Kⁿ`. -/
def IsLinearInvariant (V : Submodule K (Form K n)) : Prop :=
  ∀ B, V.map (pullback K n B 0) ≤ V

/-- `V` is mapped into itself by the pullback along every invertible linear map `x ↦ g x`,
`g ∈ GL(n, K)`. -/
def IsGLInvariant (V : Submodule K (Form K n)) : Prop :=
  ∀ g : GL (Fin n) K, V.map (pullback K n g 0) ≤ V

/-- `X(r, s, k) = dP_{r+1}Λ^{k-1} + κP_sΛ^{k+1}` ([AFW2006], Theorem 3.5), used for `k ≥ 1` and
`s ≥ 0`; the source's case `s = -1` is `dP_{r+1}Λ^{k-1}`. -/
def invariantForm (r s k : ℕ) : Submodule K (Form K n) :=
  (polyForm K n (r + 1) (k - 1)).map (extDeriv K n) ⊔ (polyForm K n s (k + 1)).map (koszul K n)

/-- **The classification of the invariant spaces of polynomial forms** on `Kⁿ`, `K` of
characteristic `0` ([AFW2006], §3.4). -/
structure AffineInvariantForms [CharZero K] : Prop where
  /-- the images `dH_rΛᵏ` and `κH_rΛᵏ` are linearly invariant, among them the summands
  `dH_{r+1}Λ^{k-1}` and `κH_{r-1}Λ^{k+1}` of `H_rΛᵏ` (§3.4) -/
  isLinearInvariant_map_homForm (r k : ℕ) :
    IsLinearInvariant K n ((homForm K n r k).map (extDeriv K n)) ∧
      IsLinearInvariant K n ((homForm K n r k).map (koszul K n))
  /-- every `GL(n)`-invariant subspace of `H_{r+1}Λ^{k+1}` is `0`, `dH_{r+2}Λᵏ`, `κH_rΛ^{k+2}`
  or `H_{r+1}Λ^{k+1}`: the summands of (3.10) are irreducible (§3.4, before Lemma 3.7) -/
  eq_of_le_homForm (r k : ℕ) (W : Submodule K (Form K n)) (hW : IsGLInvariant K n W)
    (hle : W ≤ homForm K n (r + 1) (k + 1)) :
    W = ⊥ ∨ W = (homForm K n (r + 2) k).map (extDeriv K n) ∨
      W = (homForm K n r (k + 2)).map (koszul K n) ∨ W = homForm K n (r + 1) (k + 1)
  /-- `dP_{r+1}Λ^{k-1}` is affinely invariant ((3.18)) -/
  isAffineInvariant_map_extDeriv (r k : ℕ) :
    IsAffineInvariant K n ((polyForm K n (r + 1) (k - 1)).map (extDeriv K n))
  /-- `X(r, s, k)` is affinely invariant for `s ≤ r`, `k ≥ 1` (Theorem 3.5) -/
  isAffineInvariant_invariantForm (r s k : ℕ) (hk : 1 ≤ k) (hs : s ≤ r) :
    IsAffineInvariant K n (invariantForm K n r s k)
  /-- `X(r, r, k) = P_{r+1}⁻Λᵏ` (Theorem 3.5, case `s = r`) -/
  invariantForm_eq_polyFormMinus (r k : ℕ) (hk : 1 ≤ k) :
    invariantForm K n r r k = polyFormMinus K n (r + 1) k
  /-- `X(r + 1, r, k) = P_{r+1}Λᵏ` (Theorem 3.5, case `s = r - 1`) -/
  invariantForm_eq_polyForm (r k : ℕ) (hk : 1 ≤ k) :
    invariantForm K n (r + 1) r k = polyForm K n (r + 1) k
  /-- `dP_1Λ^{k-1} = P_0Λᵏ`, that is `X(0, -1, k) = P_0Λᵏ` (Theorem 3.5, case `s = r - 1`,
  `r = 0`) -/
  map_extDeriv_polyForm_one (k : ℕ) (hk : 1 ≤ k) :
    (polyForm K n 1 (k - 1)).map (extDeriv K n) = polyForm K n 0 k
  /-- for `0 < k < n` every nonzero finite-dimensional space of `k`-forms mapped into itself by the
  pullback along every invertible affine map is `dP_{r+1}Λ^{k-1}` or `X(r, s, k)`, `s ≤ r`
  (Theorem 3.6) -/
  eq_invariantForm (k : ℕ) (hk : 0 < k) (hkn : k < n) (V : Submodule K (Form K n))
    [FiniteDimensional K V] (hV : ∀ (g : GL (Fin n) K) b, V.map (pullback K n g b) ≤ V)
    (hdeg : V ≤ kForm K n ⊤ k) (hne : V ≠ ⊥) :
    ∃ r, V = (polyForm K n (r + 1) (k - 1)).map (extDeriv K n) ∨
      ∃ s ≤ r, V = invariantForm K n r s k

/-! ### The classification -/

/-! ### The algebra of the spaces `P_rΛᵏ`, `P_r⁻Λᵏ` and `Q_b⁻Λᵏ` -/

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

/-- **An admissible sequence** ([AFW2006], §3.5, §5.5): in every form degree `k` the full space
`P_{r_k}Λᵏ` (`full k = true`) or the trimmed space `P_{r_k}⁻Λᵏ`, `r_k ≥ 1`, followed in degree
`k + 1` by `P_{r_k}⁻Λᵏ⁺¹` or by `P_{r_k - 1}Λᵏ⁺¹` (the spaces of degree `k > n` are `0`;
`P_0Λⁿ = P_1⁻Λⁿ` enters as the trimmed space). -/
structure Admissible (full : ℕ → Bool) (r : ℕ → ℕ) : Prop where
  one_le (k : ℕ) : 1 ≤ r k
  transition (k : ℕ) :
    (full (k + 1) = false ∧ r (k + 1) = r k) ∨ (full (k + 1) = true ∧ r (k + 1) + 1 = r k)

/-- The space `P_{r_k}Λᵏ` (`full k = true`) or `P_{r_k}⁻Λᵏ` in degree `k` of a sequence. -/
def seqForm (full : ℕ → Bool) (r : ℕ → ℕ) (k : ℕ) : Submodule K (Form K n) :=
  if full k then polyForm K n (r k) k else polyFormMinus K n (r k) k

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
  /-- `dim P_rΛᵏ = Σ_{m ≤ n} C(n + 1, m + 1) dim P⁻_{r+k-m}Λ^{m-k}(Kᵐ)` (`r ≥ 1`, the summand `0`
  unless `k ≤ m < r + k`): the degrees of freedom of `P_rΛᵏ` on the `m`-faces of a simplex -/
  finrank_polyForm_eq_sum [CharZero K] (r k : ℕ) (hr : 1 ≤ r) :
    finrank K (polyForm K n r k) = ∑ m ∈ range (n + 1), (n + 1).choose (m + 1) *
      if k ≤ m ∧ m < r + k then finrank K (polyFormMinus K m (r + k - m) (m - k)) else 0
  /-- `dim P_r⁻Λᵏ = Σ_{m ≤ n} C(n + 1, m + 1) dim P_{r+k-m-1}Λ^{m-k}(Kᵐ)` (`r ≥ 1`, the summand `0`
  unless `k ≤ m < r + k`): the degrees of freedom of `P_r⁻Λᵏ` on the `m`-faces of a simplex -/
  finrank_polyFormMinus_eq_sum [CharZero K] (r k : ℕ) (hr : 1 ≤ r) :
    finrank K (polyFormMinus K n r k) = ∑ m ∈ range (n + 1), (n + 1).choose (m + 1) *
      if k ≤ m ∧ m < r + k then finrank K (polyForm K m (r + k - m - 1) (m - k)) else 0
  /-- `d` maps each space of an admissible sequence into the next one -/
  map_seqForm_le (full : ℕ → Bool) (r : ℕ → ℕ) (h : Admissible full r) (k : ℕ) :
    (seqForm K n full r k).map (extDeriv K n) ≤ seqForm K n full r (k + 1)
  /-- the complex `S₀ → S₁ → ⋯` of an admissible sequence is exact in positive degree -/
  exactAt_seqForm [CharZero K] (full : ℕ → Bool) (r : ℕ → ℕ) (h : Admissible full r) (k : ℕ) :
    (deRham extDeriv_comp_extDeriv (map_seqForm_le full r h)).ExactAt (k + 1)
  /-- the closed `0`-forms of an admissible sequence are the constants -/
  closed_seqForm [CharZero K] (full : ℕ → Bool) (r : ℕ → ℕ) (h : Admissible full r) :
    ker (extDeriv K n) ⊓ seqForm K n full r 0 = polyForm K n 0 0

end FEEC
