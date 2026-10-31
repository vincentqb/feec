module

public import Feec.FiniteElement.LocalSpace
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Linearly invariant spaces of homogeneous polynomial forms

The linear maps `x ↦ B x` of `ℝⁿ` act on polynomial forms by pullback (`polyPullback B 0`). A
subspace is *linearly invariant* (`IsLinearInvariant`) if it is mapped into itself by the pullback
of every linear map, and *affinely invariant* (`IsAffineInvariant`) if also by the translations.
The main result: **the linearly invariant subspaces of `H_mΛᵏ`** (`m + k > 0`) are `0`, the closed
forms `dH_{m+1}Λ^{k-1}`, the `κ`-closed forms `κH_{m-1}Λ^{k+1}` and `H_mΛᵏ`, so the two summands
of the Koszul decomposition `H_mΛᵏ = κH_{m-1}Λ^{k+1} ⊕ dH_{m+1}Λ^{k-1}` are irreducible
([AFW2006], §3.4, which takes it from the representation theory of `GL(n)`, [FultonHarris1991],
§6.1, (6.9)). The proof is elementary, by pullbacks and linear algebra:

* **weight parts**: the diagonal pullback along `diag(c^{e₁}, …, c^{eₙ})` is `Σⱼ cʲ ω_{(j)}` for
  the parts `ω_{(j)}` of weight `j` (`exists_polyPullback_diag_pow`), so a linearly invariant
  space contains the weight parts of its elements (the coefficients of a polynomial curve in a
  subspace lie in it, `mem_of_forall_sum_pow_smul_mem`): the homogeneous components
  (`IsLinearInvariant.homComp_mem`) and the multi-weight parts (`IsLinearInvariant.multiPart_mem`),
  which commute with `d` and `κ` (`extDeriv_multiPart`, `koszul_multiPart`), as `d` and `κ` commute
  with linear pullbacks (`polyPullback_extDeriv`, `polyPullback_koszul_linear`);
* **generation** (`IsLinearInvariant.extDeriv_mem`): from `x_p^m dx_{p ∪ s}` = `d(x_p^{m+1} dx_s)`
  up to a factor, the pullback along `x_p ↦ Σ_l x_l`, `dx_s ↦ dx_u` and the multi-weight part
  `β + 𝟙_u` give `d(x^β dx_u)` times a multinomial coefficient;
* **reaching the generator** (`IsLinearInvariant.closed_le`): if `κω ≠ 0`, with `(κω)_s(a) ≠ 0`,
  the pullback along `x̂ ↦ a x̂_p + Σ_{l ∈ s} x̂_l e_l` followed by a multi-weight part is a nonzero
  multiple of `x_p^m dx_{p ∪ s}`;
* **the `κ`-closed summand** (`IsLinearInvariant.koszulClosed_le`,
  `IsLinearInvariant.koszulClosed_le_of_extDeriv_ne_zero`): `κ` maps the closed forms of
  `H_{m-1}Λ^{k+1}` onto the `κ`-closed forms of `H_mΛᵏ` equivariantly, and the preimage of an
  invariant space is invariant.

The invariance is under all linear maps, singular ones included, as in the hypothesis of
[AFW2006], Theorem 3.6 (all affine maps); invariance under `GL(n)` alone is not treated.

## Main definitions

* `Feec.FiniteElement.IsLinearInvariant`, `Feec.FiniteElement.IsAffineInvariant`;
* `Feec.FiniteElement.weightPart e j`, `Feec.FiniteElement.multiPart μ`: the parts of weight `j`
  for the coordinate weights `e`, and of multi-weight `μ` (`x^α dx_t` with `α + 𝟙_t = μ`).

## Main results

* `IsLinearInvariant.eq_of_le_homForm`: **the linearly invariant subspaces of `H_mΛᵏ`**, and
  `IsLinearInvariant.eq_of_le_homForm_succ` with the summands as the images `dH_{m+1}Λ^{k-1}`,
  `κH_{m-1}Λ^{k+1}` (`homForm_inf_ker_extDeriv`, `homForm_inf_ker_koszul`), which are linearly
  invariant (`isLinearInvariant_map_extDeriv_homForm`, `isLinearInvariant_map_koszul_homForm`);
* `IsLinearInvariant.closed_le`, `IsLinearInvariant.koszulClosed_le_of_extDeriv_ne_zero`: a form
  of an invariant space with `κω ≠ 0` (resp. `dω ≠ 0`) brings the whole closed (resp. `κ`-closed)
  summand;
* `homForm_split`: the Koszul decomposition by the homotopy formula.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.4 (the decomposition (3.10) into irreducible linear-invariant subspaces, before Lemma 3.7)
* [W. Fulton, J. Harris, *Representation Theory: A First Course*][FultonHarris1991], §6.1, (6.9)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre
open Koszul (PolyForm homForm polyForm polyFormMinus homComp koszulₗ extDerivₗ)

/-! ### Polynomial identities in a module -/

/-- **Coefficients of a polynomial curve in a subspace**: if `Σ_{i<N} cⁱ vᵢ ∈ W` for every scalar
`c` of an infinite field, then every `vᵢ ∈ W`. -/
theorem mem_of_forall_sum_pow_smul_mem {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
    [Module K V] {W : Submodule K V} {N : ℕ} {v : ℕ → V}
    (h : ∀ c : K, ∑ i ∈ range N, c ^ i • v i ∈ W) {i : ℕ} (hi : i < N) : v i ∈ W := by
  rw [← Submodule.Quotient.mk_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff K _).1 fun φ => ?_
  set ψ := φ ∘ₗ W.mkQ
  set P : Polynomial K := ∑ j ∈ range N, Polynomial.C (ψ (v j)) * Polynomial.X ^ j with hPdef
  have hP : P = 0 := Polynomial.funext fun c => by
    have h1 : ψ (∑ i ∈ range N, c ^ i • v i) = 0 := by
      change φ (W.mkQ _) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 (h c), map_zero]
    rw [map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    simp only [hPdef, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero, ← h1]
    exact sum_congr rfl fun j _ => mul_comm _ _
  have := congrArg (Polynomial.coeff · i) hP
  simpa [hPdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hi,
    ψ] using this

/-! ### Parts of polynomial forms selected by their monomials -/

theorem wedgeProd_smul_left {ι d : Type*} [LinearOrder ι] [LinearOrder d] (c : ι → ℝ)
    (θ : ι → d → ℝ) (s : Finset ι) :
    wedgeProd (fun i => c i • θ i) s = (∏ i ∈ s, c i) • wedgeProd θ s := by
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [wedgeProd_insert_of_lt _ ha, wedgeProd_insert_of_lt _ ha, ih, wedge_smul_left, wedge_smul,
      smul_smul, prod_insert has]

variable {n : ℕ}

theorem polyForm_ext_coeff {ω η : PolyForm ℝ (Fin n)}
    (h : ∀ t α, (ω t).coeff α = (η t).coeff α) : ω = η :=
  funext fun t => MvPolynomial.ext _ _ (h t)

open scoped Classical in
/-- The part of `ω` on the monomial forms `x^α dx_t` with `P t α`. -/
def restrictForm (P : Finset (Fin n) → (Fin n →₀ ℕ) → Prop) (ω : PolyForm ℝ (Fin n)) :
    PolyForm ℝ (Fin n) :=
  fun t => ∑ α ∈ (ω t).support with P t α, monomial α ((ω t).coeff α)

open scoped Classical in
theorem coeff_restrictForm (P : Finset (Fin n) → (Fin n →₀ ℕ) → Prop) (ω : PolyForm ℝ (Fin n))
    (t : Finset (Fin n)) (α : Fin n →₀ ℕ) :
    (restrictForm P ω t).coeff α = if P t α then (ω t).coeff α else 0 := by
  rw [restrictForm, coeff_sum]
  simp only [coeff_monomial]
  rw [sum_ite_eq']
  by_cases hα : α ∈ (ω t).support
  · simp [hα]
  · rw [mem_support_iff, not_not] at hα
    simp [hα]

theorem restrictForm_restrictForm (P Q : Finset (Fin n) → (Fin n →₀ ℕ) → Prop)
    (ω : PolyForm ℝ (Fin n)) :
    restrictForm P (restrictForm Q ω) = restrictForm (fun t α => P t α ∧ Q t α) ω := by
  classical
  refine polyForm_ext_coeff fun t α => ?_
  simp only [coeff_restrictForm]
  by_cases hP : P t α <;> by_cases hQ : Q t α <;> simp [hP, hQ]

/-! ### Diagonal pullbacks -/

/-- The diagonal matrix `diag μ`, as the coefficient function taken by `polyPullback`. -/
def diagMatrix (μ : Fin n → ℝ) : Fin n → Fin n → ℝ := fun i l => if i = l then μ i else 0

theorem coeff_aeval_C_mul_X (μ : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (α : Fin n →₀ ℕ) :
    (aeval (fun i => C (μ i) * X i) p).coeff α = (∏ i, μ i ^ α i) * p.coeff α := by
  induction p using MvPolynomial.induction_on' with
  | monomial β c =>
    have hm : aeval (fun i => C (μ i) * X i) (monomial β c) =
        monomial β (c * ∏ i, μ i ^ β i) := by
      rw [aeval_monomial, monomial_eq, algebraMap_eq, Finsupp.prod, Finsupp.prod]
      simp only [mul_pow, prod_mul_distrib, ← C_pow, ← map_prod, ← mul_assoc, ← C_mul]
      congr 2
      rw [prod_subset (subset_univ _) fun i _ hi => by rw [Finsupp.notMem_support_iff.1 hi, pow_zero]]
    rw [hm, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  | add p q hp hq => simp [hp, hq, mul_add]

/-- **The diagonal pullback** `x ↦ diag(μ) x` scales `x^α dx_t` by `μ^α μ_t`. -/
theorem coeff_polyPullback_diag (μ : Fin n → ℝ) (ω : PolyForm ℝ (Fin n)) (t : Finset (Fin n))
    (α : Fin n →₀ ℕ) :
    (polyPullback (diagMatrix μ) 0 ω t).coeff α =
      (∏ i, μ i ^ α i) * (∏ i ∈ t, μ i) * (ω t).coeff α := by
  have hB : diagMatrix μ = fun i => μ i • (Pi.single i 1 : Fin n → ℝ) := by
    funext i l; simp [diagMatrix, Pi.single_apply, eq_comm]
  have hW : ∀ s, wedgeProd (diagMatrix μ) s t = if s = t then ∏ i ∈ t, μ i else 0 := by
    intro s
    rw [hB, wedgeProd_smul_left, wedgeProd_single, Pi.smul_apply, Pi.single_apply]
    by_cases h : s = t
    · subst h; simp
    · simp [h, Ne.symm h]
  have hS : polySubst (diagMatrix μ) 0 = aeval fun i => C (μ i) * X i := by
    rw [polySubst]
    congr 1
    funext i
    rw [sum_eq_single i (fun l _ hl => by simp [diagMatrix, Ne.symm hl]) (by simp)]
    simp [diagMatrix]
  rw [polyPullback_apply]
  simp only [hW, apply_ite C, C_0, mul_ite, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [mul_comm, coeff_C_mul, hS, coeff_aeval_C_mul_X]
  ring

/-! ### Weight parts -/

/-- The weight `Σᵢ eᵢ (αᵢ + [i ∈ t])` of the monomial form `x^α dx_t` for the weights `e` of the
coordinates. -/
def formWeight (e : Fin n → ℕ) (t : Finset (Fin n)) (α : Fin n →₀ ℕ) : ℕ :=
  ∑ i, e i * α i + ∑ i ∈ t, e i

/-- The part of weight `j` of `ω` for the weights `e` of the coordinates. -/
def weightPart (e : Fin n → ℕ) (j : ℕ) (ω : PolyForm ℝ (Fin n)) : PolyForm ℝ (Fin n) :=
  restrictForm (fun t α => formWeight e t α = j) ω

theorem restrictForm_congr {P Q : Finset (Fin n) → (Fin n →₀ ℕ) → Prop}
    (h : ∀ t α, P t α ↔ Q t α) (ω : PolyForm ℝ (Fin n)) : restrictForm P ω = restrictForm Q ω := by
  have : P = Q := funext fun t => funext fun α => propext (h t α)
  rw [this]

theorem restrictForm_true (ω : PolyForm ℝ (Fin n)) : restrictForm (fun _ _ => True) ω = ω := by
  classical
  exact polyForm_ext_coeff fun t α => by simp [coeff_restrictForm]

/-- **The diagonal pullback along `c^e`**: `diag(c^{e₁}, …)^* ω = Σⱼ cʲ ω_{(j)}` for the weight
parts `ω_{(j)}`, for every `N` beyond the weights of `ω`. -/
theorem exists_polyPullback_diag_pow (e : Fin n → ℕ) (ω : PolyForm ℝ (Fin n)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∀ c : ℝ, polyPullback (diagMatrix fun i => c ^ e i) 0 ω =
      ∑ j ∈ range N, c ^ j • weightPart e j ω := by
  classical
  refine ⟨∑ t, ∑ α ∈ (ω t).support, formWeight e t α + 1, fun N hN c => ?_⟩
  refine polyForm_ext_coeff fun t α => ?_
  rw [coeff_polyPullback_diag, Finset.sum_apply, coeff_sum]
  simp only [Pi.smul_apply, coeff_smul, weightPart, coeff_restrictForm, smul_eq_mul, mul_ite,
    mul_zero]
  have hw : (∏ i, (c ^ e i) ^ α i) * ∏ i ∈ t, c ^ e i = c ^ formWeight e t α := by
    simp only [formWeight, ← pow_mul, prod_pow_eq_pow_sum, pow_add]
  rw [hw]
  by_cases hα : α ∈ (ω t).support
  · have : formWeight e t α < N := by
      have h1 : formWeight e t α ≤ ∑ α ∈ (ω t).support, formWeight e t α :=
        single_le_sum (f := fun α => formWeight e t α) (fun _ _ => Nat.zero_le _) hα
      have h2 : ∑ α ∈ (ω t).support, formWeight e t α ≤
          ∑ t, ∑ α ∈ (ω t).support, formWeight e t α :=
        single_le_sum (f := fun t => ∑ α ∈ (ω t).support, formWeight e t α)
          (fun _ _ => Nat.zero_le _) (mem_univ t)
      omega
    simp [this]
  · rw [mem_support_iff, not_not] at hα
    simp [hα]

/-- Invariance under the pullbacks `x ↦ B x` by all linear maps of `ℝⁿ`. -/
def IsLinearInvariant (W : Submodule ℝ (PolyForm ℝ (Fin n))) : Prop :=
  ∀ (B : Fin n → Fin n → ℝ), ∀ ω ∈ W, polyPullback B 0 ω ∈ W

/-- Invariance under the pullbacks `x ↦ B x + b` by all affine maps of `ℝⁿ`. -/
def IsAffineInvariant (X : Submodule ℝ (PolyForm ℝ (Fin n))) : Prop :=
  ∀ (B : Fin n → Fin n → ℝ) (b : Fin n → ℝ), ∀ ω ∈ X, polyPullback B b ω ∈ X

theorem IsAffineInvariant.isLinearInvariant {X : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hX : IsAffineInvariant X) : IsLinearInvariant X := fun B => hX B 0

/-- **A linearly invariant space contains the weight parts of its elements.** -/
theorem IsLinearInvariant.weightPart_mem {W : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hW : IsLinearInvariant W) {ω : PolyForm ℝ (Fin n)} (hω : ω ∈ W) (e : Fin n → ℕ) (j : ℕ) :
    weightPart e j ω ∈ W := by
  obtain ⟨N₀, hN⟩ := exists_polyPullback_diag_pow e ω
  refine mem_of_forall_sum_pow_smul_mem (N := max N₀ (j + 1)) (v := fun j => weightPart e j ω)
    (fun c => ?_) (by omega)
  rw [← hN _ (le_max_left _ _)]
  exact hW _ _ hω

/-- An operator commuting with the diagonal pullbacks commutes with the weight parts. -/
theorem weightPart_comm (e : Fin n → ℕ) (T : PolyForm ℝ (Fin n) →ₗ[ℝ] PolyForm ℝ (Fin n))
    (hT : ∀ (c : ℝ) ω, T (polyPullback (diagMatrix fun i => c ^ e i) 0 ω) =
      polyPullback (diagMatrix fun i => c ^ e i) 0 (T ω)) (j : ℕ) (ω : PolyForm ℝ (Fin n)) :
    T (weightPart e j ω) = weightPart e j (T ω) := by
  obtain ⟨N₀, hN₀⟩ := exists_polyPullback_diag_pow e ω
  obtain ⟨N₁, hN₁⟩ := exists_polyPullback_diag_pow e (T ω)
  set N := max (max N₀ N₁) (j + 1)
  have h := mem_of_forall_sum_pow_smul_mem (W := (⊥ : Submodule ℝ (PolyForm ℝ (Fin n)))) (N := N)
    (v := fun j => T (weightPart e j ω) - weightPart e j (T ω)) (fun c => ?_) (i := j) (by omega)
  · simpa [sub_eq_zero] using h
  · rw [Submodule.mem_bot]
    simp only [smul_sub, sum_sub_distrib, ← map_smul, ← map_sum]
    rw [← hN₀ N (by omega), ← hN₁ N (by omega), hT, sub_self]

/-! ### Pullbacks commute with `d`, linear pullbacks with `κ` -/

/-- `F^* dω = d F^* ω` for affine `F`. -/
theorem polyPullback_extDeriv (B : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (ω : PolyForm ℝ (Fin n)) :
    polyPullback B b (Koszul.extDeriv ω) = Koszul.extDeriv (polyPullback B b ω) := by
  apply evalForm_injective
  rw [evalForm_polyPullback, ← extDeriv_evalForm, ← extDeriv_evalForm, evalForm_polyPullback]
  funext x
  exact (extDeriv_affinePullback_apply B b
    (((contDiff_evalForm ω (r := 1)).differentiable one_ne_zero) _)).symm

theorem polyPullback_zero_form (B : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    polyPullback B b (0 : PolyForm ℝ (Fin n)) = 0 := by
  funext t; simp [polyPullback_apply]

/-- `B^* κω = κ B^* ω` for linear `B` ([AFW2006], (3.7)). -/
theorem polyPullback_koszul_linear (B : Fin n → Fin n → ℝ) (ω : PolyForm ℝ (Fin n)) :
    polyPullback B 0 (Koszul.koszul ω) = Koszul.koszul (polyPullback B 0 ω) := by
  have h0 : interior (fun j => C ((0 : Fin n → ℝ) j)) ω = 0 := by
    funext s; simp [interior_apply]
  rw [polyPullback_koszul, h0, polyPullback_zero_form, add_zero]

theorem isDeg_polyPullback {k : ℕ} {ω : PolyForm ℝ (Fin n)} (h : IsDeg k ω)
    (B : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : IsDeg k (polyPullback B b ω) :=
  IsDeg.pullback (fun t ht => by simp [h t ht]) _

theorem polyPullback_smul (B : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (c : ℝ)
    (ω : PolyForm ℝ (Fin n)) : polyPullback B b (c • ω) = c • polyPullback B b ω := by
  funext t
  simp only [polyPullback_apply, Pi.smul_apply, smul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, mul_assoc]
  simp [polySubst]

/-- The pullback as a linear map. -/
def polyPullbackₗ (B : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    PolyForm ℝ (Fin n) →ₗ[ℝ] PolyForm ℝ (Fin n) where
  toFun := polyPullback B b
  map_add' := polyPullback_add B b
  map_smul' := polyPullback_smul B b

theorem extDeriv_weightPart (e : Fin n → ℕ) (j : ℕ) (ω : PolyForm ℝ (Fin n)) :
    Koszul.extDeriv (weightPart e j ω) = weightPart e j (Koszul.extDeriv ω) :=
  weightPart_comm e (extDerivₗ ℝ (Fin n)) (fun _ ω => (polyPullback_extDeriv _ _ ω).symm) j ω

theorem koszul_weightPart (e : Fin n → ℕ) (j : ℕ) (ω : PolyForm ℝ (Fin n)) :
    Koszul.koszul (weightPart e j ω) = weightPart e j (Koszul.koszul ω) :=
  weightPart_comm e (koszulₗ ℝ (Fin n)) (fun _ ω => (polyPullback_koszul_linear _ ω).symm) j ω

/-! ### Multi-weight parts -/

/-- The part of `ω` of multi-weight `μ`: the monomial forms `x^α dx_t` with `α + 𝟙_t = μ`. -/
def multiPart (μ : Fin n → ℕ) (ω : PolyForm ℝ (Fin n)) : PolyForm ℝ (Fin n) :=
  restrictForm (fun t α => ∀ i, α i + (if i ∈ t then 1 else 0) = μ i) ω

theorem formWeight_single (i : Fin n) (t : Finset (Fin n)) (α : Fin n →₀ ℕ) :
    formWeight (Pi.single i 1) t α = α i + if i ∈ t then 1 else 0 := by
  simp [formWeight, Pi.single_apply, sum_ite_eq']

theorem restrictForm_insert_eq (μ : Fin n → ℕ) (i : Fin n) (S : Finset (Fin n))
    (ω : PolyForm ℝ (Fin n)) :
    restrictForm (fun t α => ∀ l ∈ insert i S, α l + (if l ∈ t then 1 else 0) = μ l) ω =
      weightPart (Pi.single i 1) (μ i)
        (restrictForm (fun t α => ∀ l ∈ S, α l + (if l ∈ t then 1 else 0) = μ l) ω) := by
  rw [weightPart, restrictForm_restrictForm]
  exact restrictForm_congr (fun t α => by simp [formWeight_single]) ω

/-- **A linearly invariant space contains the multi-weight parts of its elements.** -/
theorem IsLinearInvariant.multiPart_mem {W : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hW : IsLinearInvariant W) {ω : PolyForm ℝ (Fin n)} (hω : ω ∈ W) (μ : Fin n → ℕ) :
    multiPart μ ω ∈ W := by
  suffices h : ∀ S : Finset (Fin n),
      restrictForm (fun t α => ∀ l ∈ S, α l + (if l ∈ t then 1 else 0) = μ l) ω ∈ W by
    simpa [multiPart] using h univ
  intro S
  induction S using Finset.induction_on with
  | empty => simpa [restrictForm_true] using hω
  | insert i S _ ih => rw [restrictForm_insert_eq]; exact hW.weightPart_mem ih _ _

theorem multiPart_comm (μ : Fin n → ℕ) (T : PolyForm ℝ (Fin n) →ₗ[ℝ] PolyForm ℝ (Fin n))
    (hT : ∀ (e : Fin n → ℕ) (j : ℕ) ω, T (weightPart e j ω) = weightPart e j (T ω))
    (ω : PolyForm ℝ (Fin n)) : T (multiPart μ ω) = multiPart μ (T ω) := by
  suffices h : ∀ S : Finset (Fin n),
      T (restrictForm (fun t α => ∀ l ∈ S, α l + (if l ∈ t then 1 else 0) = μ l) ω) =
        restrictForm (fun t α => ∀ l ∈ S, α l + (if l ∈ t then 1 else 0) = μ l) (T ω) by
    simpa [multiPart] using h univ
  intro S
  induction S using Finset.induction_on with
  | empty => simp [restrictForm_true]
  | insert i S _ ih => rw [restrictForm_insert_eq, restrictForm_insert_eq, hT, ih]

theorem extDeriv_multiPart (μ : Fin n → ℕ) (ω : PolyForm ℝ (Fin n)) :
    Koszul.extDeriv (multiPart μ ω) = multiPart μ (Koszul.extDeriv ω) :=
  multiPart_comm μ (extDerivₗ ℝ (Fin n)) (fun e j ω => extDeriv_weightPart e j ω) ω

theorem koszul_multiPart (μ : Fin n → ℕ) (ω : PolyForm ℝ (Fin n)) :
    Koszul.koszul (multiPart μ ω) = multiPart μ (Koszul.koszul ω) :=
  multiPart_comm μ (koszulₗ ℝ (Fin n)) (fun e j ω => koszul_weightPart e j ω) ω

/-- **A linearly invariant space contains the homogeneous components of its elements.** -/
theorem IsLinearInvariant.homComp_mem {W : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hW : IsLinearInvariant W) {k : ℕ} {ω : PolyForm ℝ (Fin n)} (hω : ω ∈ W) (hk : IsDeg k ω)
    (j : ℕ) : homComp j ω ∈ W := by
  classical
  have : homComp j ω = weightPart (fun _ => 1) (j + k) ω := by
    refine polyForm_ext_coeff fun t α => ?_
    rw [weightPart, coeff_restrictForm, Koszul.homComp_apply, coeff_homogeneousComponent]
    by_cases ht : #t = k
    · simp [formWeight, ht, Finsupp.degree_eq_sum]
    · simp [hk t ht]
  rw [this]
  exact hW.weightPart_mem hω _ _

/-! ### Coefficient lemmas -/

theorem polyPullback_single (B : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (s : Finset (Fin n))
    (q : MvPolynomial (Fin n) ℝ) (t : Finset (Fin n)) :
    polyPullback B b (Pi.single s q) t = polySubst B b q * C (wedgeProd B s t) := by
  rw [polyPullback_apply, sum_eq_single s (fun s' _ hs' => by simp [hs']) (by simp)]
  simp

/-- `x^β dx_u` has multi-weight `β + 𝟙_u`, and it is the only monomial form of that weight with
the basis form `dx_u`. -/
theorem multiPart_single (β : Fin n →₀ ℕ) (u : Finset (Fin n)) (q : MvPolynomial (Fin n) ℝ) :
    multiPart (fun i => β i + if i ∈ u then 1 else 0) (Pi.single u q) =
      Pi.single u (monomial β (q.coeff β)) := by
  classical
  refine polyForm_ext_coeff fun t α => ?_
  rw [multiPart, coeff_restrictForm]
  by_cases ht : t = u
  · subst ht
    simp only [Pi.single_eq_same, coeff_monomial]
    by_cases hα : α = β
    · subst hα; simp
    · rw [ite_eq_right_iff.2 fun h => absurd h (Ne.symm hα), ite_eq_right_iff.2 fun h =>
        absurd (Finsupp.ext fun i => by simpa using h i) hα]
  · simp [ht]

/-- The coefficient of `x_p^N` in a homogeneous polynomial of degree `N` is its value at `e_p`. -/
theorem coeff_single_eq_eval {f : MvPolynomial (Fin n) ℝ} {N : ℕ} (hf : f.IsHomogeneous N)
    (p : Fin n) : f.coeff (Finsupp.single p N) = eval (Pi.single p 1) f := by
  classical
  rw [eval_eq', sum_eq_single (Finsupp.single p N)]
  · simp [Pi.single_apply, Finsupp.single_apply]
  · intro β _ hβ
    by_cases h0 : f.coeff β = 0
    · simp [h0]
    · have hdeg := hf h0
      obtain ⟨i, hi, hβi⟩ : ∃ i, i ≠ p ∧ β i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        refine hβ (Finsupp.ext fun i => ?_)
        by_cases hip : i = p
        · subst hip
          rw [Finsupp.single_eq_same, ← hdeg, Finsupp.weight_apply, Finsupp.sum_fintype _ _
            (by simp)]
          rw [sum_eq_single i (fun l _ hl => by simp [hcon l hl]) (by simp)]
          simp
        · rw [hcon i hip, Finsupp.single_apply, ite_eq_right_iff.2 fun h => absurd h (Ne.symm hip)]
      rw [prod_eq_zero (mem_univ i) (by simp [hi, hβi]), mul_zero]
  · intro h; rw [notMem_support_iff.1 h, zero_mul]

theorem isHomogeneous_polySubst_zero (B : Fin n → Fin n → ℝ) {q : MvPolynomial (Fin n) ℝ}
    {N : ℕ} (hq : q.IsHomogeneous N) : (polySubst B 0 q).IsHomogeneous N := by
  have := hq.aeval (g := fun i => ∑ l, C (B i l) * X l + C ((0 : Fin n → ℝ) i)) (n := 1)
    fun i => by
      simp only [Pi.zero_apply, C_0, add_zero]
      exact IsHomogeneous.sum _ _ _ fun l _ => isHomogeneous_C_mul_X _ _
  simpa [polySubst] using this

/-- Two matrices that agree on the columns `s` have the same products on subsets of `s`. -/
theorem wedgeProd_congr_cols {B B' : Fin n → Fin n → ℝ} {s : Finset (Fin n)}
    (h : ∀ i, ∀ l ∈ s, B i l = B' i l) (u : Finset (Fin n)) :
    ∀ t ⊆ s, wedgeProd B u t = wedgeProd B' u t := by
  induction u using Finset.induction_on_min with
  | empty => intro t _; simp
  | insert a u ha ih =>
    intro t ht
    rw [wedgeProd_insert_of_lt _ ha, wedgeProd_insert_of_lt _ ha, wedge_apply, wedge_apply]
    refine sum_congr rfl fun j hj => ?_
    rw [h a j (ht hj), ih _ ((erase_subset j t).trans ht)]

/-- The products of coordinate covectors relabelled by a map strictly increasing on `s`. -/
theorem wedgeProd_single_comp {σ : Fin n → Fin n} {s : Finset (Fin n)}
    (hσ : StrictMonoOn σ s) :
    wedgeProd (fun i => (Pi.single (σ i) 1 : Fin n → ℝ)) s = Pi.single (s.image σ) 1 := by
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h' => lt_irrefl a (ha a h')
    have hσs : StrictMonoOn σ s := hσ.mono (by intro x hx; simp [Finset.mem_coe.1 hx])
    have hlt : ∀ x ∈ s.image σ, σ a < x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      exact hσ (by simp) (by simp [hy]) (ha y hy)
    have hna : σ a ∉ s.image σ := fun h => lt_irrefl _ (hlt _ h)
    rw [wedgeProd_insert_of_lt _ ha, ih hσs, image_insert, wedge_single_single hna]
    have : sgn (σ a) (s.image σ) = (1 : ℝ) := by
      rw [sgn, filter_eq_empty_iff.2 fun x hx => not_lt.2 (hlt x hx).le]; simp
    rw [this, one_smul]

theorem wedgeProd_id_cols {B : Fin n → Fin n → ℝ} {s : Finset (Fin n)}
    (h : ∀ i, ∀ l ∈ s, B i l = if i = l then 1 else 0) (u : Finset (Fin n)) :
    wedgeProd B u s = if u = s then 1 else 0 := by
  rw [wedgeProd_congr_cols (B' := fun i => (Pi.single i 1 : Fin n → ℝ))
    (fun i l hl => by rw [h i l hl]; simp [Pi.single_apply, eq_comm]) u s subset_rfl,
    wedgeProd_single, Pi.single_apply]
  by_cases hu : u = s
  · subst hu; simp
  · simp [Ne.symm hu, hu]

theorem polyForm_eq_sum_monomial (ω : PolyForm ℝ (Fin n)) :
    ω = ∑ u, ∑ β ∈ (ω u).support, (ω u).coeff β • Pi.single u (monomial β (1 : ℝ)) := by
  classical
  funext t
  rw [Finset.sum_apply, sum_eq_single t (fun u _ hu => by
    rw [Finset.sum_apply]; exact sum_eq_zero fun β _ => by simp [Ne.symm hu])
    (by simp)]
  rw [Finset.sum_apply]
  conv_lhs => rw [(ω t).as_sum]
  refine sum_congr rfl fun β _ => ?_
  simp [smul_monomial]

/-- The monomial forms of multi-weight `β + 𝟙_{t₀}` with `β` supported in `t₀`, among the
`#t₀`-forms, are the multiples of `x^β dx_{t₀}`. -/
theorem multiPart_eq_single {t₀ : Finset (Fin n)} {β : Fin n →₀ ℕ} (hβ : ∀ i ∉ t₀, β i = 0)
    {ω : PolyForm ℝ (Fin n)} (hω : IsDeg #t₀ ω) :
    multiPart (fun i => β i + if i ∈ t₀ then 1 else 0) ω =
      Pi.single t₀ (monomial β ((ω t₀).coeff β)) := by
  classical
  have h1 : multiPart (fun i => β i + if i ∈ t₀ then 1 else 0) ω =
      multiPart (fun i => β i + if i ∈ t₀ then 1 else 0) (Pi.single t₀ (ω t₀)) := by
    refine polyForm_ext_coeff fun t α => ?_
    rw [multiPart, multiPart, coeff_restrictForm, coeff_restrictForm]
    by_cases ht : t = t₀
    · subst ht; simp
    · simp only [Pi.single_apply, ht, ↓reduceIte]
      by_cases hc : ∀ i, α i + (if i ∈ t then 1 else 0) = β i + if i ∈ t₀ then 1 else 0
      · have hsub : t ⊆ t₀ := fun i hi => by
          by_contra hi0
          have := hc i
          simp only [hi, hi0, hβ i hi0, ↓reduceIte] at this
          omega
        by_cases hcard : #t = #t₀
        · exact absurd (eq_of_subset_of_card_le hsub hcard.ge) ht
        · simp [hω t hcard]
      · simp [hc]
  rw [h1, multiPart_single]

/-- A map strictly increasing on `s` with image `u`, for `#s = #u`. -/
theorem exists_strictMonoOn_image {s u : Finset (Fin n)} (h : #s = #u) :
    ∃ σ : Fin n → Fin n, StrictMonoOn σ s ∧ s.image σ = u := by
  classical
  let e := s.orderIsoOfFin rfl
  let f := u.orderEmbOfFin h.symm
  refine ⟨fun i => if hi : i ∈ s then f (e.symm ⟨i, hi⟩) else i, fun i hi j hj hij => ?_, ?_⟩
  · simp only [Finset.mem_coe.1 hi, Finset.mem_coe.1 hj, dite_true]
    exact f.strictMono (e.symm.strictMono (Subtype.mk_lt_mk.2 hij))
  · have hsub : s.image (fun i => if hi : i ∈ s then f (e.symm ⟨i, hi⟩) else i) ⊆ u := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
      simp only [hi, dite_true]
      exact orderEmbOfFin_mem u h.symm _
    refine eq_of_subset_of_card_le hsub ?_
    rw [card_image_of_injOn, h]
    intro i hi j hj hij
    simp only [Finset.mem_coe.1 hi, Finset.mem_coe.1 hj, dite_true] at hij
    have := e.symm.injective (f.injective hij)
    simpa using congrArg Subtype.val this

/-- `d(x_p^{m+1} dx_s) = (m+1) ε(p, s) x_p^m dx_{p ∪ s}` for `p ∉ s`. -/
theorem extDeriv_single_X_pow {p : Fin n} {s : Finset (Fin n)} (hp : p ∉ s) (m : ℕ) :
    Koszul.extDeriv (Pi.single s (X p ^ (m + 1)) : PolyForm ℝ (Fin n)) =
      (((m + 1 : ℕ) : ℝ) * sgn p s) • Pi.single (insert p s) (X p ^ m) := by
  classical
  have hd : ∀ j, pderiv j (X p ^ (m + 1) : MvPolynomial (Fin n) ℝ) =
      if j = p then C ((m + 1 : ℕ) : ℝ) * X p ^ m else 0 := by
    intro j
    rw [pderiv_pow, Nat.add_sub_cancel]
    by_cases hj : j = p
    · subst hj; simp
    · simp [pderiv_X_of_ne (Ne.symm hj), hj]
  funext t
  rw [Koszul.extDeriv_apply, Pi.smul_apply]
  by_cases ht : t = insert p s
  · subst ht
    rw [sum_eq_single p (fun j hj hjp => ?_) (by simp), erase_insert hp, Pi.single_eq_same,
      Pi.single_eq_same, sgn_insert_self, hd, smul_eq_C_mul]
    · simp only [↓reduceIte, map_mul]
      rw [show (sgn p s : MvPolynomial (Fin n) ℝ) = C (sgn p s) by simp [sgn]]
      ring
    · have : (insert p s).erase j ≠ s := fun h =>
        hp (h ▸ mem_erase.2 ⟨Ne.symm hjp, mem_insert_self p s⟩)
      simp [this]
  · simp only [Pi.single_apply, ht, ↓reduceIte, smul_zero]
    refine sum_eq_zero fun j hj => ?_
    by_cases hjs : t.erase j = s
    · have hjp : j ≠ p := by
        rintro rfl
        exact ht (by rw [← hjs, insert_erase hj])
      simp [hjs, hd, hjp]
    · simp [hjs]

/-! ### The irreducible summands of `H_rΛᵏ` -/

/-- **Generation**: a linearly invariant space containing `x_p^m dx_{p ∪ s}` (`p ∉ s`) contains
`d H_{m+1}Λ^{#s}`: pulling `x_p^{m+1} dx_s` back along a map with `x_p ↦ Σ_l x_l` and
`dx_s ↦ dx_u` and taking multi-weight parts gives every `d(x^β dx_u)`, as the coefficients of
`(Σ_l x_l)^{m+1}` are multinomial coefficients, nonzero. -/
theorem IsLinearInvariant.extDeriv_mem {W : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hW : IsLinearInvariant W) {m : ℕ} {p : Fin n} {s : Finset (Fin n)} (hp : p ∉ s)
    (hg : (Pi.single (insert p s) (X p ^ m) : PolyForm ℝ (Fin n)) ∈ W) {η : PolyForm ℝ (Fin n)}
    (hη : η ∈ homForm ℝ (Fin n) (m + 1) #s) : Koszul.extDeriv η ∈ W := by
  classical
  set ζ : PolyForm ℝ (Fin n) := Pi.single s (X p ^ (m + 1))
  have hc0 : (((m + 1 : ℕ) : ℝ) * sgn p s) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)) (by rw [sgn]; exact pow_ne_zero _ (by norm_num))
  have hdζ : Koszul.extDeriv ζ ∈ W := by
    rw [extDeriv_single_X_pow hp]; exact W.smul_mem _ hg
  -- every `d(x^β dx_u)` with `#u = #s` and `|β| = m + 1`
  have key : ∀ u : Finset (Fin n), #u = #s → ∀ β : Fin n →₀ ℕ, β.degree = m + 1 →
      Koszul.extDeriv (Pi.single u (monomial β (1 : ℝ))) ∈ W := by
    intro u hu β hβ
    obtain ⟨σ, hσ, hσu⟩ := exists_strictMonoOn_image hu.symm
    set B : Fin n → Fin n → ℝ := fun i l =>
      if i = p then 1 else if i ∈ s then (Pi.single (σ i) 1 : Fin n → ℝ) l else 0
    have hBζ : polyPullback B 0 ζ = Pi.single u ((∑ l, X l) ^ (m + 1)) := by
      funext t
      rw [polyPullback_single]
      have hsub : polySubst B 0 (X p ^ (m + 1)) = (∑ l, X l) ^ (m + 1) := by
        simp [polySubst, B]
      have hw : wedgeProd B s = Pi.single u 1 := by
        rw [wedgeProd_congr (θ' := fun i => (Pi.single (σ i) 1 : Fin n → ℝ)) fun j hj => ?_,
          wedgeProd_single_comp hσ, hσu]
        funext l
        have hjp : j ≠ p := fun h => hp (h ▸ hj)
        simp [B, hjp, hj]
      rw [hsub, hw, Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    have h1 : Koszul.extDeriv (polyPullback B 0 ζ) ∈ W := by
      rw [← polyPullback_extDeriv]; exact hW B _ hdζ
    have h2 := hW.multiPart_mem h1 (fun i => β i + if i ∈ u then 1 else 0)
    rw [← extDeriv_multiPart, hBζ, multiPart_single, coeff_sum_X_pow_of_fintype] at h2
    have hsum : (β.sum fun _ m => m) = m + 1 := by
      rw [← hβ, Finsupp.degree]; rfl
    simp only [hsum, ↓reduceIte] at h2
    rw [← mul_one ((β.multinomial : ℕ) : ℝ), ← smul_eq_mul, ← smul_monomial,
      show (Pi.single u (((β.multinomial : ℕ) : ℝ) • monomial β (1 : ℝ)) : PolyForm ℝ (Fin n)) =
        ((β.multinomial : ℕ) : ℝ) • Pi.single u (monomial β 1) from Pi.single_smul' _ _ _,
      Koszul.extDeriv_smul] at h2
    refine (W.smul_mem_iff (Nat.cast_ne_zero.2 (Nat.multinomial_pos _ _).ne')).1 h2
  -- `η` is a combination of the monomial forms
  have hlin : ∀ ω, Koszul.extDeriv ω = extDerivₗ ℝ (Fin n) ω := fun _ => rfl
  rw [polyForm_eq_sum_monomial η, hlin, map_sum]
  refine W.sum_mem fun u _ => ?_
  rw [map_sum]
  refine W.sum_mem fun β hβ => ?_
  rw [map_smul, ← hlin]
  refine W.smul_mem _ ?_
  have hu : #u = #s := by
    by_contra h
    simp [hη.1 u h] at hβ
  have hw := (hη.2 u) (mem_support_iff.1 hβ)
  exact key u hu β (by rw [Finsupp.degree_eq_weight_one]; exact hw)

/-- **Reaching the generator**: a linearly invariant space containing `ω ∈ H_mΛ^{k+1}` with
`κω ≠ 0` contains the closed forms of `H_mΛ^{k+1}` (`κ` vanishes on `0`-forms). With `(κω)_s(a) ≠ 0` and `p ∉ s`, the pullback
along `x̂ ↦ a x̂_p + Σ_{l ∈ s} x̂_l e_l` followed by the multi-weight part `x_p^m dx_{p ∪ s}` is a
multiple of `x_p^m dx_{p ∪ s}`, nonzero as its `κ` has the coefficient `(κω)_s(a)` at
`x_p^{m+1} dx_s`; `IsLinearInvariant.extDeriv_mem` and the polynomial Poincaré lemma conclude. -/
theorem IsLinearInvariant.closed_le {W : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hW : IsLinearInvariant W) {m k : ℕ} {ω : PolyForm ℝ (Fin n)} (hω : ω ∈ W)
    (hωH : ω ∈ homForm ℝ (Fin n) m k) (hκ : Koszul.koszul ω ≠ 0) :
    homForm ℝ (Fin n) m k ⊓ LinearMap.ker (extDerivₗ ℝ (Fin n)) ≤ W := by
  classical
  obtain _ | k := k
  · exact absurd (Koszul.IsDeg.koszul_eq_zero hωH.1) hκ
  obtain ⟨s, hs⟩ : ∃ s, Koszul.koszul ω s ≠ 0 := by
    by_contra h
    push Not at h
    exact hκ (funext h)
  have hsk : #s = k := by
    by_contra h
    exact hs (Koszul.IsDeg.koszul hωH.1 s h)
  obtain ⟨a, ha⟩ : ∃ a, eval a (Koszul.koszul ω s) ≠ 0 := by
    by_contra h
    push Not at h
    exact hs (MvPolynomial.funext fun x => by simp [h x])
  obtain ⟨p, hp⟩ : ∃ p, p ∉ s := by
    by_contra h
    push Not at h
    refine hs ?_
    rw [Koszul.koszul_apply, (compl_eq_empty_iff s).2 (eq_univ_of_forall h), sum_empty]
  set B : Fin n → Fin n → ℝ := fun i l =>
    if l ∈ s then (if i = l then 1 else 0) else if l = p then a i else 0
  have hBcols : ∀ i, ∀ l ∈ s, B i l = if i = l then 1 else 0 := fun i l hl => by simp [B, hl]
  set ω₁ := polyPullback B 0 ω
  have hω₁ : ω₁ ∈ W := hW B ω hω
  set μ : Fin n → ℕ := fun i => (Finsupp.single p m) i + if i ∈ insert p s then 1 else 0
  set ω₂ := multiPart μ ω₁
  have hω₂ : ω₂ ∈ W := hW.multiPart_mem hω₁ μ
  set c := (ω₁ (insert p s)).coeff (Finsupp.single p m)
  have hcard : #(insert p s) = k + 1 := by rw [card_insert_of_notMem hp, hsk]
  have hω₂eq : ω₂ = c • (Pi.single (insert p s) (X p ^ m) : PolyForm ℝ (Fin n)) := by
    have hdeg : IsDeg #(insert p s) ω₁ := by rw [hcard]; exact isDeg_polyPullback hωH.1 B 0
    rw [show ω₂ = multiPart (fun i => (Finsupp.single p m) i +
        if i ∈ insert p s then 1 else 0) ω₁ from rfl, multiPart_eq_single (fun i hi => by
        rw [Finsupp.single_apply, ite_eq_right]; exact fun h => hi (h ▸ mem_insert_self p s)) hdeg,
      ← Pi.single_smul', X_pow_eq_monomial, smul_monomial, smul_eq_mul, mul_one]
  -- `κ ω₂` has the coefficient `(κω)_s(a)` at `x_p^{m+1} dx_s`
  have hκω₂ : (Koszul.koszul ω₂ s).coeff (Finsupp.single p (m + 1)) = eval a (Koszul.koszul ω s) := by
    have hμ : ∀ i, (Finsupp.single p (m + 1)) i + (if i ∈ s then 1 else 0) = μ i := by
      intro i
      by_cases hip : i = p
      · subst hip; simp [μ, hp]
      · by_cases his : i ∈ s
        · simp [μ, Finsupp.single_apply, Ne.symm hip, his]
        · simp [μ, Finsupp.single_apply, Ne.symm hip, his, hip]
    rw [koszul_multiPart, multiPart, coeff_restrictForm, ite_eq_left hμ, ← polyPullback_koszul_linear]
    rw [polyPullback_apply, sum_eq_single s (fun u _ hu => by
      rw [wedgeProd_id_cols hBcols, ite_eq_right hu, C_0, mul_zero]) (by simp),
      wedgeProd_id_cols hBcols, ite_eq_left rfl, C_1, mul_one]
    have hhom := isHomogeneous_polySubst_zero B ((Koszul.koszul_mem_homForm hωH).2 s)
    have haff : affine B 0 (Pi.single p 1) = a := by
      funext i; simp [affine_apply, B, Pi.single_apply, hp]
    rw [coeff_single_eq_eval hhom, eval_polySubst, haff]
  have hc : c ≠ 0 := by
    intro hc0
    rw [hω₂eq, hc0, zero_smul, Koszul.koszul_zero] at hκω₂
    exact ha (by simpa using hκω₂.symm)
  have hg : (Pi.single (insert p s) (X p ^ m) : PolyForm ℝ (Fin n)) ∈ W := by
    have := W.smul_mem c⁻¹ hω₂
    rwa [hω₂eq, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  rintro ξ ⟨hξ, hdξ⟩
  obtain ⟨η, hη, rfl⟩ := Koszul.exists_extDeriv_eq_of_extDeriv_eq_zero (by omega) hξ hdξ
  rw [Nat.add_sub_cancel, ← hsk] at hη
  exact hW.extDeriv_mem hp hg hη

/-- `κ d ξ = (r + k) ξ` for `ξ ∈ H_rΛᵏ` with `κ ξ = 0` (homotopy formula). -/
theorem koszul_extDeriv_of_koszul_eq_zero {r k : ℕ} {ξ : PolyForm ℝ (Fin n)}
    (h : ξ ∈ homForm ℝ (Fin n) r k) (hκ : Koszul.koszul ξ = 0) :
    Koszul.koszul (Koszul.extDeriv ξ) = ((r + k : ℕ) : ℝ) • ξ := by
  have := Koszul.extDeriv_koszul_add_koszul_extDeriv_of_mem h
  rwa [hκ, Koszul.extDeriv_zero, zero_add] at this

/-- `d κ ξ = (r + k) ξ` for `ξ ∈ H_rΛᵏ` with `d ξ = 0` (homotopy formula). -/
theorem extDeriv_koszul_of_extDeriv_eq_zero {r k : ℕ} {ξ : PolyForm ℝ (Fin n)}
    (h : ξ ∈ homForm ℝ (Fin n) r k) (hd : Koszul.extDeriv ξ = 0) :
    Koszul.extDeriv (Koszul.koszul ξ) = ((r + k : ℕ) : ℝ) • ξ := by
  have := Koszul.extDeriv_koszul_add_koszul_extDeriv_of_mem h
  rwa [hd, Koszul.koszul_zero, add_zero] at this

theorem IsLinearInvariant.comap_koszul {W : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hW : IsLinearInvariant W) : IsLinearInvariant (W.comap (koszulₗ ℝ (Fin n))) :=
  fun B ω hω => by
    change Koszul.koszul (polyPullback B 0 ω) ∈ W
    rw [← polyPullback_koszul_linear]
    exact hW B _ hω

/-- **The `κ`-closed summand**: a linearly invariant space containing a nonzero `κ`-closed
`ω ∈ H_{m+1}Λᵏ` contains every `κ`-closed form of `H_{m+1}Λᵏ`. As `κ` maps the closed forms of
`H_mΛ^{k+1}` onto them, equivariantly, this is `IsLinearInvariant.closed_le` for the preimage. -/
theorem IsLinearInvariant.koszulClosed_le {W : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hW : IsLinearInvariant W) {m k : ℕ} {ω : PolyForm ℝ (Fin n)} (hω : ω ∈ W)
    (hωH : ω ∈ homForm ℝ (Fin n) (m + 1) k) (hκ : Koszul.koszul ω = 0) (h0 : ω ≠ 0) :
    homForm ℝ (Fin n) (m + 1) k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n)) ≤ W := by
  set c : ℝ := ((m + 1 + k : ℕ) : ℝ)
  have hc : c ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpre : ∀ {ξ : PolyForm ℝ (Fin n)}, ξ ∈ homForm ℝ (Fin n) (m + 1) k →
      Koszul.koszul ξ = 0 → Koszul.koszul (c⁻¹ • Koszul.extDeriv ξ) = ξ := fun hξ hκξ => by
    rw [Koszul.koszul_smul, koszul_extDeriv_of_koszul_eq_zero hξ hκξ, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  have hmem : ∀ {ξ : PolyForm ℝ (Fin n)}, ξ ∈ homForm ℝ (Fin n) (m + 1) k →
      c⁻¹ • Koszul.extDeriv ξ ∈ homForm ℝ (Fin n) m (k + 1) := fun hξ =>
    Submodule.smul_mem _ _ (by simpa using Koszul.extDeriv_mem_homForm hξ)
  have hle := hW.comap_koszul.closed_le (ω := c⁻¹ • Koszul.extDeriv ω)
    (by change Koszul.koszul _ ∈ W; rw [hpre hωH hκ]; exact hω) (hmem hωH)
    (by rw [hpre hωH hκ]; exact h0)
  rintro ξ ⟨hξ, hκξ⟩
  have hκξ' : Koszul.koszul ξ = 0 := LinearMap.mem_ker.1 hκξ
  have := hle ⟨hmem hξ, LinearMap.mem_ker.2 (show Koszul.extDeriv (c⁻¹ • Koszul.extDeriv ξ) = 0 by
    rw [Koszul.extDeriv_smul, Koszul.extDeriv_extDeriv, smul_zero])⟩
  change Koszul.koszul _ ∈ W at this
  rwa [hpre hξ hκξ'] at this

/-- **The Koszul decomposition by the homotopy formula**: for `ω ∈ H_mΛᵏ`, `m + k > 0`,
`ω = c⁻¹ κdω + c⁻¹ dκω` (`c = m + k`) with `κdω` `κ`-closed and `dκω` closed, both in `H_mΛᵏ`. -/
theorem homForm_split {m k : ℕ} (hmk : 0 < m + k) {ω : PolyForm ℝ (Fin n)}
    (hω : ω ∈ homForm ℝ (Fin n) m k) :
    ((m + k : ℕ) : ℝ)⁻¹ • Koszul.koszul (Koszul.extDeriv ω) ∈
        homForm ℝ (Fin n) m k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n)) ∧
      ((m + k : ℕ) : ℝ)⁻¹ • Koszul.extDeriv (Koszul.koszul ω) ∈
        homForm ℝ (Fin n) m k ⊓ LinearMap.ker (extDerivₗ ℝ (Fin n)) ∧
      ω = ((m + k : ℕ) : ℝ)⁻¹ • Koszul.koszul (Koszul.extDeriv ω) +
        ((m + k : ℕ) : ℝ)⁻¹ • Koszul.extDeriv (Koszul.koszul ω) := by
  set c : ℝ := ((m + k : ℕ) : ℝ)
  have hc : c ≠ 0 := Nat.cast_ne_zero.2 hmk.ne'
  have heq : ω = c⁻¹ • Koszul.koszul (Koszul.extDeriv ω) +
      c⁻¹ • Koszul.extDeriv (Koszul.koszul ω) := by
    rw [← smul_add, add_comm, Koszul.extDeriv_koszul_add_koszul_extDeriv_of_mem hω, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  have hb : c⁻¹ • Koszul.extDeriv (Koszul.koszul ω) ∈ homForm ℝ (Fin n) m k := by
    refine Submodule.smul_mem _ _ ?_
    obtain _ | k := k
    · rw [Koszul.IsDeg.koszul_eq_zero hω.1, Koszul.extDeriv_zero]; exact Submodule.zero_mem _
    · simpa using Koszul.extDeriv_mem_homForm (Koszul.koszul_mem_homForm hω)
  refine ⟨⟨?_, LinearMap.mem_ker.2 ?_⟩, ⟨hb, LinearMap.mem_ker.2 ?_⟩, heq⟩
  · rw [eq_sub_of_add_eq heq.symm]; exact Submodule.sub_mem _ hω hb
  · change Koszul.koszul (c⁻¹ • _) = 0
    rw [Koszul.koszul_smul, Koszul.koszul_koszul, smul_zero]
  · change Koszul.extDeriv (c⁻¹ • _) = 0
    rw [Koszul.extDeriv_smul, Koszul.extDeriv_extDeriv, smul_zero]

/-- **The `κ`-closed summand is reached from every non-closed form**: a linearly invariant space
containing `ω ∈ H_mΛᵏ` with `dω ≠ 0` contains the `κ`-closed forms of `H_mΛᵏ` (its `κ`-closed
part is nonzero, and in the space once the closed summand is, `IsLinearInvariant.closed_le`). -/
theorem IsLinearInvariant.koszulClosed_le_of_extDeriv_ne_zero
    {W : Submodule ℝ (PolyForm ℝ (Fin n))} (hW : IsLinearInvariant W) {m k : ℕ}
    {ω : PolyForm ℝ (Fin n)} (hω : ω ∈ W) (hωH : ω ∈ homForm ℝ (Fin n) m k)
    (hd : Koszul.extDeriv ω ≠ 0) :
    homForm ℝ (Fin n) m k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n)) ≤ W := by
  obtain _ | m := m
  · exact absurd (extDeriv_eq_zero_of_mem_polyForm_zero (Koszul.homForm_le_polyForm _ _ hωH)) hd
  obtain ⟨hK, hD, heq⟩ := homForm_split (by omega) hωH
  by_cases hκ : Koszul.koszul ω = 0
  · exact hW.koszulClosed_le hω hωH hκ fun h => hd (by rw [h, Koszul.extDeriv_zero])
  have hDW := hW.closed_le hω hωH hκ
  have hω' := W.sub_mem hω (hDW hD)
  rw [eq_sub_of_add_eq heq.symm] at hK
  refine hW.koszulClosed_le hω' hK.1 (LinearMap.mem_ker.1 hK.2) fun h => hd ?_
  have := congrArg (extDerivₗ ℝ (Fin n)) h
  rw [map_sub, map_zero, Koszul.extDerivₗ_apply, Koszul.extDerivₗ_apply] at this
  rwa [Koszul.extDeriv_smul, Koszul.extDeriv_extDeriv, smul_zero, sub_zero] at this

/-- **The linearly invariant subspaces of `H_mΛᵏ`** (`m + k > 0`): `0`, the closed forms
`dH_{m+1}Λ^{k-1}`, the `κ`-closed forms `κH_{m-1}Λ^{k+1}` and `H_mΛᵏ`; that is, the two summands
of the Koszul decomposition `H_mΛᵏ = κH_{m-1}Λ^{k+1} ⊕ dH_{m+1}Λ^{k-1}` are irreducible.
[AFW2006], §3.4 (before Lemma 3.7, from [FultonHarris1991], (6.9)) -/
theorem IsLinearInvariant.eq_of_le_homForm {W : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hW : IsLinearInvariant W) {m k : ℕ} (hmk : 0 < m + k) (hle : W ≤ homForm ℝ (Fin n) m k) :
    W = ⊥ ∨ W = homForm ℝ (Fin n) m k ⊓ LinearMap.ker (extDerivₗ ℝ (Fin n)) ∨
      W = homForm ℝ (Fin n) m k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n)) ∨ W = homForm ℝ (Fin n) m k := by
  by_cases hA : ∃ ω ∈ W, Koszul.koszul ω ≠ 0 <;> by_cases hB : ∃ ω ∈ W, Koszul.extDeriv ω ≠ 0
  · obtain ⟨ω, hω, hκ⟩ := hA
    obtain ⟨ω', hω', hd⟩ := hB
    refine Or.inr (Or.inr (Or.inr (le_antisymm hle fun ξ hξ => ?_)))
    obtain ⟨h1, h2, h3⟩ := homForm_split hmk hξ
    rw [h3]
    exact W.add_mem (hW.koszulClosed_le_of_extDeriv_ne_zero hω' (hle hω') hd h1)
      (hW.closed_le hω (hle hω) hκ h2)
  · obtain ⟨ω, hω, hκ⟩ := hA
    push Not at hB
    exact Or.inr (Or.inl (le_antisymm (fun ξ hξ => ⟨hle hξ, LinearMap.mem_ker.2 (hB ξ hξ)⟩)
      (hW.closed_le hω (hle hω) hκ)))
  · obtain ⟨ω, hω, hd⟩ := hB
    push Not at hA
    exact Or.inr (Or.inr (Or.inl (le_antisymm
      (fun ξ hξ => ⟨hle hξ, LinearMap.mem_ker.2 (hA ξ hξ)⟩)
      (hW.koszulClosed_le_of_extDeriv_ne_zero hω (hle hω) hd))))
  · push Not at hA hB
    refine Or.inl (eq_bot_iff.2 fun ω hω => ?_)
    obtain ⟨-, -, h3⟩ := homForm_split hmk (hle hω)
    rw [Submodule.mem_bot, h3, hA ω hω, hB ω hω, Koszul.koszul_zero, Koszul.extDeriv_zero,
      smul_zero, add_zero]

/-- The closed forms of `H_mΛ^{k+1}` are `dH_{m+1}Λᵏ`. -/
theorem homForm_inf_ker_extDeriv (m k : ℕ) :
    homForm ℝ (Fin n) m (k + 1) ⊓ LinearMap.ker (extDerivₗ ℝ (Fin n)) =
      (homForm ℝ (Fin n) (m + 1) k).map (extDerivₗ ℝ (Fin n)) := by
  refine le_antisymm ?_ ?_
  · rintro ξ ⟨hξ, hd⟩
    obtain ⟨η, hη, rfl⟩ := Koszul.exists_extDeriv_eq_of_extDeriv_eq_zero (by omega) hξ hd
    exact ⟨η, by simpa using hη, rfl⟩
  · rintro _ ⟨η, hη, rfl⟩
    exact ⟨by simpa using Koszul.extDeriv_mem_homForm hη,
      LinearMap.mem_ker.2 (Koszul.extDeriv_extDeriv η)⟩

/-- The `κ`-closed forms of `H_{m+1}Λᵏ` are `κH_mΛ^{k+1}`. -/
theorem homForm_inf_ker_koszul (m k : ℕ) :
    homForm ℝ (Fin n) (m + 1) k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n)) =
      (homForm ℝ (Fin n) m (k + 1)).map (koszulₗ ℝ (Fin n)) := by
  refine le_antisymm ?_ ?_
  · rintro ξ ⟨hξ, hκ⟩
    obtain ⟨η, hη, rfl⟩ := Koszul.exists_koszul_eq_of_koszul_eq_zero (by omega) hξ hκ
    exact ⟨η, by simpa using hη, rfl⟩
  · rintro _ ⟨η, hη, rfl⟩
    exact ⟨by simpa using Koszul.koszul_mem_homForm hη,
      LinearMap.mem_ker.2 (Koszul.koszul_koszul η)⟩

/-- `H_mΛᵏ` is linearly invariant: linear substitutions preserve homogeneity. -/
theorem isLinearInvariant_homForm (m k : ℕ) : IsLinearInvariant (homForm ℝ (Fin n) m k) :=
  fun B ω hω => ⟨isDeg_polyPullback hω.1 B 0, fun t => by
    rw [polyPullback_apply]
    exact IsHomogeneous.sum _ _ _ fun s _ => by
      simpa using (isHomogeneous_polySubst_zero B (hω.2 s)).mul (isHomogeneous_C _ _)⟩

/-- **`dH_mΛᵏ` is linearly invariant**, as `B^* d = d B^*` ([AFW2006], §3.4). -/
theorem isLinearInvariant_map_extDeriv_homForm (m k : ℕ) :
    IsLinearInvariant ((homForm ℝ (Fin n) m k).map (extDerivₗ ℝ (Fin n))) := by
  rintro B _ ⟨η, hη, rfl⟩
  exact ⟨_, isLinearInvariant_homForm m k B η hη, (polyPullback_extDeriv B 0 η).symm⟩

/-- **`κH_mΛᵏ` is linearly invariant**, as `B^* κ = κ B^*` for linear `B` ([AFW2006], §3.4,
(3.7)). -/
theorem isLinearInvariant_map_koszul_homForm (m k : ℕ) :
    IsLinearInvariant ((homForm ℝ (Fin n) m k).map (koszulₗ ℝ (Fin n))) := by
  rintro B _ ⟨η, hη, rfl⟩
  exact ⟨_, isLinearInvariant_homForm m k B η hη, (polyPullback_koszul_linear B η).symm⟩

/-- **[AFW2006], §3.4: `H_rΛᵏ` has exactly the invariant subspaces `0`, `κH_{r-1}Λ^{k+1}`,
`dH_{r+1}Λ^{k-1}` and `H_rΛᵏ`** (`r, k ≥ 1`; with `r = m + 1`, `k = k' + 1`). -/
theorem IsLinearInvariant.eq_of_le_homForm_succ {W : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hW : IsLinearInvariant W) {m k : ℕ} (hle : W ≤ homForm ℝ (Fin n) (m + 1) (k + 1)) :
    W = ⊥ ∨ W = (homForm ℝ (Fin n) (m + 2) k).map (extDerivₗ ℝ (Fin n)) ∨
      W = (homForm ℝ (Fin n) m (k + 2)).map (koszulₗ ℝ (Fin n)) ∨
        W = homForm ℝ (Fin n) (m + 1) (k + 1) := by
  rw [← homForm_inf_ker_extDeriv, ← homForm_inf_ker_koszul]
  exact hW.eq_of_le_homForm (by omega) hle

end Feec.FiniteElement
