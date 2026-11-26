module

public import Feec.FiniteElement.LocalSpace
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Linearly invariant spaces of homogeneous polynomial forms

In characteristic `0`, the `GL(n)`-invariant subspaces of `H_mΛᵏ`, `m + k > 0`, are `0`, the closed
forms, the `κ`-closed forms and `H_mΛᵏ` ([AFW2006], §3.4; [FultonHarris1991], §6.1).

## Main results

* `IsGLInvariant.eq_of_le_homForm`: the `GL(n)`-invariant subspaces of `H_mΛᵏ`.
* `IsLinearInvariant.eq_of_le_homForm`: the linearly invariant subspaces of `H_mΛᵏ`.
* `IsGLInvariant.isLinearInvariant`: `GL(n)`-invariance is linear invariance (`K` infinite).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006], §3.4
* [W. Fulton, J. Harris, *Representation Theory: A First Course*][FultonHarris1991], §6.1

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre
open Koszul (PolyForm homForm polyForm polyFormMinus homComp koszulₗ extDerivₗ)

/-! ### Polynomial identities in a module -/

theorem mem_of_eventually_sum_pow_smul_mem {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
    [Module K V] {W : Submodule K V} {N : ℕ} {v : ℕ → V}
    (h : ∀ᶠ c : K in Filter.cofinite, ∑ i ∈ range N, c ^ i • v i ∈ W) {i : ℕ} (hi : i < N) :
    v i ∈ W := by
  rw [← Submodule.Quotient.mk_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff K _).1 fun φ => ?_
  set ψ := φ ∘ₗ W.mkQ
  set P : Polynomial K := ∑ j ∈ range N, Polynomial.C (ψ (v j)) * Polynomial.X ^ j with hPdef
  have hP : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P
      (Filter.frequently_cofinite_iff_infinite.1 (h.mono fun c hc => ?_).frequently)
    have h1 : ψ (∑ i ∈ range N, c ^ i • v i) = 0 := by
      change φ (W.mkQ _) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hc, map_zero]
    rw [map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    simp only [Polynomial.IsRoot, hPdef, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← h1]
    exact sum_congr rfl fun j _ => mul_comm _ _
  have := congrArg (Polynomial.coeff · i) hP
  simpa [hPdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hi,
    ψ] using this

/-! ### Parts of polynomial forms selected by their monomials -/

theorem wedgeProd_smul_left {R ι d : Type*} [CommRing R] [LinearOrder ι] [LinearOrder d]
    (c : ι → R) (θ : ι → d → R) (s : Finset ι) :
    wedgeProd (fun i => c i • θ i) s = (∏ i ∈ s, c i) • wedgeProd θ s := by
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [wedgeProd_insert_of_lt _ ha, wedgeProd_insert_of_lt _ ha, ih, wedge_smul_left, wedge_smul,
      smul_smul, prod_insert has]

variable {K : Type*} [Field K] {n : ℕ}

theorem polyForm_ext_coeff {ω η : PolyForm K (Fin n)}
    (h : ∀ t α, (ω t).coeff α = (η t).coeff α) : ω = η :=
  funext fun t => MvPolynomial.ext _ _ (h t)

open scoped Classical in
/-- The part of `ω` on the monomial forms `x^α dx_t` with `P t α`. -/
def restrictForm (P : Finset (Fin n) → (Fin n →₀ ℕ) → Prop) (ω : PolyForm K (Fin n)) :
    PolyForm K (Fin n) :=
  fun t => ∑ α ∈ (ω t).support with P t α, monomial α ((ω t).coeff α)

open scoped Classical in
theorem coeff_restrictForm (P : Finset (Fin n) → (Fin n →₀ ℕ) → Prop) (ω : PolyForm K (Fin n))
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
    (ω : PolyForm K (Fin n)) :
    restrictForm P (restrictForm Q ω) = restrictForm (fun t α => P t α ∧ Q t α) ω := by
  classical
  refine polyForm_ext_coeff fun t α => ?_
  simp only [coeff_restrictForm]
  by_cases hP : P t α <;> by_cases hQ : Q t α <;> simp [hP, hQ]

/-! ### Diagonal pullbacks -/

/-- The diagonal matrix `diag μ`, as the coefficient function taken by `polyPullback`. -/
def diagMatrix (μ : Fin n → K) : Fin n → Fin n → K := fun i l => if i = l then μ i else 0

theorem coeff_aeval_C_mul_X (μ : Fin n → K) (p : MvPolynomial (Fin n) K) (α : Fin n →₀ ℕ) :
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

theorem coeff_polyPullback_diag (μ : Fin n → K) (ω : PolyForm K (Fin n)) (t : Finset (Fin n))
    (α : Fin n →₀ ℕ) :
    (polyPullback (diagMatrix μ) 0 ω t).coeff α =
      (∏ i, μ i ^ α i) * (∏ i ∈ t, μ i) * (ω t).coeff α := by
  have hB : diagMatrix μ = fun i => μ i • (Pi.single i 1 : Fin n → K) := by
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

/-- The weight `Σᵢ eᵢ (αᵢ + [i ∈ t])` of the monomial form `x^α dx_t`. -/
def formWeight (e : Fin n → ℕ) (t : Finset (Fin n)) (α : Fin n →₀ ℕ) : ℕ :=
  ∑ i, e i * α i + ∑ i ∈ t, e i

/-- The part of weight `j` of `ω` for the weights `e` of the coordinates. -/
def weightPart (e : Fin n → ℕ) (j : ℕ) (ω : PolyForm K (Fin n)) : PolyForm K (Fin n) :=
  restrictForm (fun t α => formWeight e t α = j) ω

theorem restrictForm_congr {P Q : Finset (Fin n) → (Fin n →₀ ℕ) → Prop}
    (h : ∀ t α, P t α ↔ Q t α) (ω : PolyForm K (Fin n)) : restrictForm P ω = restrictForm Q ω := by
  have : P = Q := funext fun t => funext fun α => propext (h t α)
  rw [this]

theorem restrictForm_true (ω : PolyForm K (Fin n)) : restrictForm (fun _ _ => True) ω = ω := by
  classical
  exact polyForm_ext_coeff fun t α => by simp [coeff_restrictForm]

theorem exists_polyPullback_diag_pow (e : Fin n → ℕ) (ω : PolyForm K (Fin n)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∀ c : K, polyPullback (diagMatrix fun i => c ^ e i) 0 ω =
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

/-- Invariance under the pullbacks `x ↦ B x` by all linear maps of `Kⁿ`. -/
def IsLinearInvariant (W : Submodule K (PolyForm K (Fin n))) : Prop :=
  ∀ (B : Fin n → Fin n → K), ∀ ω ∈ W, polyPullback B 0 ω ∈ W

/-- Invariance under the pullbacks `x ↦ B x + b` by all affine maps of `Kⁿ`. -/
def IsAffineInvariant (X : Submodule K (PolyForm K (Fin n))) : Prop :=
  ∀ (B : Fin n → Fin n → K) (b : Fin n → K), ∀ ω ∈ X, polyPullback B b ω ∈ X

theorem IsAffineInvariant.isLinearInvariant {X : Submodule K (PolyForm K (Fin n))}
    (hX : IsAffineInvariant X) : IsLinearInvariant X := fun B => hX B 0

theorem IsLinearInvariant.weightPart_mem [Infinite K] {W : Submodule K (PolyForm K (Fin n))}
    (hW : IsLinearInvariant W) {ω : PolyForm K (Fin n)} (hω : ω ∈ W) (e : Fin n → ℕ) (j : ℕ) :
    weightPart e j ω ∈ W := by
  obtain ⟨N₀, hN⟩ := exists_polyPullback_diag_pow e ω
  refine mem_of_eventually_sum_pow_smul_mem (N := max N₀ (j + 1))
    (v := fun j => weightPart e j ω) (Filter.Eventually.of_forall fun c => ?_) (by omega)
  rw [← hN _ (le_max_left _ _)]
  exact hW _ _ hω

theorem weightPart_comm [Infinite K] (e : Fin n → ℕ)
    (T : PolyForm K (Fin n) →ₗ[K] PolyForm K (Fin n))
    (hT : ∀ (c : K) ω, T (polyPullback (diagMatrix fun i => c ^ e i) 0 ω) =
      polyPullback (diagMatrix fun i => c ^ e i) 0 (T ω)) (j : ℕ) (ω : PolyForm K (Fin n)) :
    T (weightPart e j ω) = weightPart e j (T ω) := by
  obtain ⟨N₀, hN₀⟩ := exists_polyPullback_diag_pow e ω
  obtain ⟨N₁, hN₁⟩ := exists_polyPullback_diag_pow e (T ω)
  set N := max (max N₀ N₁) (j + 1)
  have h := mem_of_eventually_sum_pow_smul_mem (W := (⊥ : Submodule K (PolyForm K (Fin n))))
    (N := N) (v := fun j => T (weightPart e j ω) - weightPart e j (T ω))
    (Filter.Eventually.of_forall fun c => ?_) (i := j) (by omega)
  · simpa [sub_eq_zero] using h
  · rw [Submodule.mem_bot]
    simp only [smul_sub, sum_sub_distrib, ← map_smul, ← map_sum]
    rw [← hN₀ N (by omega), ← hN₁ N (by omega), hT, sub_self]

/-! ### Pullbacks commute with `d`, linear pullbacks with `κ` -/

theorem pderiv_polySubst {m : ℕ} (B : Fin n → Fin m → K) (b : Fin n → K)
    (p : MvPolynomial (Fin n) K) (l : Fin m) : pderiv l (polySubst B b p) = ∑ i, polySubst B b (pderiv i p) * C (B i l) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [polySubst]
  | add p q hp hq => simp [hp, hq, add_mul, sum_add_distrib]
  | mul_X p j hp =>
    have hX : pderiv l (polySubst B b (X j)) = C (B j l) := by
      simp [polySubst, pderiv_X, Pi.single_apply]
    rw [map_mul, Derivation.leibniz, hp, hX, smul_eq_mul, smul_eq_mul]
    simp only [Derivation.leibniz, pderiv_X, map_add, map_mul, smul_eq_mul, add_mul,
      sum_add_distrib, mul_sum]
    simp only [Pi.single_apply, apply_ite (polySubst B b), map_one, map_zero, mul_ite, ite_mul,
      mul_one, mul_zero, zero_mul, sum_ite_eq, mem_univ, ite_true]
    congr 1
    exact sum_congr rfl fun i _ => by ring

theorem polyPullback_extDeriv {m : ℕ} (B : Fin n → Fin m → K) (b : Fin n → K)
    (ω : PolyForm K (Fin n)) :
    polyPullback B b (Koszul.extDeriv ω) = Koszul.extDeriv (polyPullback B b ω) := by
  have hpd : ∀ (l : Fin m) (α : Finset (Fin n) → MvPolynomial (Fin m) K),
      (fun t => pderiv l (pullback (fun i l => C (B i l)) α t)) =
        pullback (fun i l => C (B i l)) (fun s => pderiv l (α s)) := by
    intro l α
    funext t
    simp only [pullback_apply, map_sum, Derivation.leibniz, smul_eq_mul]
    refine sum_congr rfl fun s _ => ?_
    rw [show wedgeProd (fun i l => C (B i l)) s t = C (wedgeProd B s t) from
      (map_wedgeProd C B s t).symm, pderiv_C, mul_zero, zero_add, mul_comm]
  have hsub : ∀ i, (fun s => polySubst B b (wedge (Pi.single i 1) (Koszul.pderivForm i ω) s)) =
      wedge (Pi.single i 1) (fun s => polySubst B b (pderiv i (ω s))) := by
    intro i
    funext s
    rw [show polySubst B b (wedge (Pi.single i 1) (Koszul.pderivForm i ω) s) =
      (polySubst B b).toRingHom _ from rfl, map_wedge]
    congr 1
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  have hcov : ∀ i, covPullback (fun i l => (C (B i l) : MvPolynomial (Fin m) K)) (Pi.single i 1) =
      ∑ l, (C (B i l) : MvPolynomial (Fin m) K) •
        (Pi.single l 1 : Fin m → MvPolynomial (Fin m) K) := by
    intro i
    funext l
    simp [covPullback, Finset.sum_apply, Pi.single_apply]
  rw [polyPullback, polyPullback, Koszul.extDeriv_eq_sum_wedge, Koszul.extDeriv_eq_sum_wedge]
  simp only [Finset.sum_apply, map_sum]
  rw [show (fun s => ∑ i, polySubst B b (wedge (Pi.single i 1) (Koszul.pderivForm i ω) s)) =
    ∑ i, (fun s => polySubst B b (wedge (Pi.single i 1) (Koszul.pderivForm i ω) s)) from by
      funext s; simp [Finset.sum_apply]]
  simp only [hsub, pullback_sum, pullback_wedge, hcov, wedge_sum_left, wedge_smul_left]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  rw [show Koszul.pderivForm l _ = _ from hpd l _]
  simp only [pderiv_polySubst]
  rw [show (fun s => ∑ i, polySubst B b (pderiv i (ω s)) * C (B i l)) =
    ∑ i, (C (B i l) : MvPolynomial (Fin m) K) • (fun s => polySubst B b (pderiv i (ω s))) from by
      funext s; rw [Finset.sum_apply]
      exact sum_congr rfl fun i _ => (mul_comm _ _).trans (smul_eq_mul _ _).symm]
  rw [pullback_sum, wedge_sum]
  exact sum_congr rfl fun i _ => by rw [pullback_smul, wedge_smul]

theorem polyPullback_zero_form (B : Fin n → Fin n → K) (b : Fin n → K) :
    polyPullback B b (0 : PolyForm K (Fin n)) = 0 := by
  funext t; simp [polyPullback_apply]

theorem polyPullback_koszul_linear (B : Fin n → Fin n → K) (ω : PolyForm K (Fin n)) :
    polyPullback B 0 (Koszul.koszul ω) = Koszul.koszul (polyPullback B 0 ω) := by
  have h0 : interior (fun j => C ((0 : Fin n → K) j)) ω = 0 := by
    funext s; simp [interior_apply]
  rw [polyPullback_koszul, h0, polyPullback_zero_form, add_zero]

theorem isDeg_polyPullback {k : ℕ} {ω : PolyForm K (Fin n)} (h : IsDeg k ω)
    (B : Fin n → Fin n → K) (b : Fin n → K) : IsDeg k (polyPullback B b ω) :=
  IsDeg.pullback (fun t ht => by simp [h t ht]) _

theorem polyPullback_smul (B : Fin n → Fin n → K) (b : Fin n → K) (c : K)
    (ω : PolyForm K (Fin n)) : polyPullback B b (c • ω) = c • polyPullback B b ω := by
  funext t
  simp only [polyPullback_apply, Pi.smul_apply, smul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, mul_assoc]
  simp [polySubst]

/-- The pullback as a linear map. -/
def polyPullbackₗ (B : Fin n → Fin n → K) (b : Fin n → K) :
    PolyForm K (Fin n) →ₗ[K] PolyForm K (Fin n) where
  toFun := polyPullback B b
  map_add' := polyPullback_add B b
  map_smul' := polyPullback_smul B b

theorem extDeriv_weightPart [Infinite K] (e : Fin n → ℕ) (j : ℕ) (ω : PolyForm K (Fin n)) :
    Koszul.extDeriv (weightPart e j ω) = weightPart e j (Koszul.extDeriv ω) :=
  weightPart_comm e (extDerivₗ K (Fin n)) (fun _ ω => (polyPullback_extDeriv _ _ ω).symm) j ω

theorem koszul_weightPart [Infinite K] (e : Fin n → ℕ) (j : ℕ) (ω : PolyForm K (Fin n)) :
    Koszul.koszul (weightPart e j ω) = weightPart e j (Koszul.koszul ω) :=
  weightPart_comm e (koszulₗ K (Fin n)) (fun _ ω => (polyPullback_koszul_linear _ ω).symm) j ω

/-! ### Multi-weight parts -/

/-- The part of `ω` of multi-weight `μ`: the monomial forms `x^α dx_t` with `α + 𝟙_t = μ`. -/
def multiPart (μ : Fin n → ℕ) (ω : PolyForm K (Fin n)) : PolyForm K (Fin n) :=
  restrictForm (fun t α => ∀ i, α i + (if i ∈ t then 1 else 0) = μ i) ω

theorem formWeight_single (i : Fin n) (t : Finset (Fin n)) (α : Fin n →₀ ℕ) :
    formWeight (Pi.single i 1) t α = α i + if i ∈ t then 1 else 0 := by
  simp [formWeight, Pi.single_apply, sum_ite_eq']

theorem restrictForm_insert_eq (μ : Fin n → ℕ) (i : Fin n) (S : Finset (Fin n))
    (ω : PolyForm K (Fin n)) :
    restrictForm (fun t α => ∀ l ∈ insert i S, α l + (if l ∈ t then 1 else 0) = μ l) ω =
      weightPart (Pi.single i 1) (μ i)
        (restrictForm (fun t α => ∀ l ∈ S, α l + (if l ∈ t then 1 else 0) = μ l) ω) := by
  rw [weightPart, restrictForm_restrictForm]
  exact restrictForm_congr (fun t α => by simp [formWeight_single]) ω

theorem IsLinearInvariant.multiPart_mem [Infinite K] {W : Submodule K (PolyForm K (Fin n))}
    (hW : IsLinearInvariant W) {ω : PolyForm K (Fin n)} (hω : ω ∈ W) (μ : Fin n → ℕ) :
    multiPart μ ω ∈ W := by
  suffices h : ∀ S : Finset (Fin n),
      restrictForm (fun t α => ∀ l ∈ S, α l + (if l ∈ t then 1 else 0) = μ l) ω ∈ W by
    simpa [multiPart] using h univ
  intro S
  induction S using Finset.induction_on with
  | empty => simpa [restrictForm_true] using hω
  | insert i S _ ih => rw [restrictForm_insert_eq]; exact hW.weightPart_mem ih _ _

theorem multiPart_comm (μ : Fin n → ℕ) (T : PolyForm K (Fin n) →ₗ[K] PolyForm K (Fin n))
    (hT : ∀ (e : Fin n → ℕ) (j : ℕ) ω, T (weightPart e j ω) = weightPart e j (T ω))
    (ω : PolyForm K (Fin n)) : T (multiPart μ ω) = multiPart μ (T ω) := by
  suffices h : ∀ S : Finset (Fin n),
      T (restrictForm (fun t α => ∀ l ∈ S, α l + (if l ∈ t then 1 else 0) = μ l) ω) =
        restrictForm (fun t α => ∀ l ∈ S, α l + (if l ∈ t then 1 else 0) = μ l) (T ω) by
    simpa [multiPart] using h univ
  intro S
  induction S using Finset.induction_on with
  | empty => simp [restrictForm_true]
  | insert i S _ ih => rw [restrictForm_insert_eq, restrictForm_insert_eq, hT, ih]

theorem extDeriv_multiPart [Infinite K] (μ : Fin n → ℕ) (ω : PolyForm K (Fin n)) :
    Koszul.extDeriv (multiPart μ ω) = multiPart μ (Koszul.extDeriv ω) :=
  multiPart_comm μ (extDerivₗ K (Fin n)) (fun e j ω => extDeriv_weightPart e j ω) ω

theorem koszul_multiPart [Infinite K] (μ : Fin n → ℕ) (ω : PolyForm K (Fin n)) :
    Koszul.koszul (multiPart μ ω) = multiPart μ (Koszul.koszul ω) :=
  multiPart_comm μ (koszulₗ K (Fin n)) (fun e j ω => koszul_weightPart e j ω) ω

theorem IsLinearInvariant.homComp_mem [Infinite K] {W : Submodule K (PolyForm K (Fin n))}
    (hW : IsLinearInvariant W) {k : ℕ} {ω : PolyForm K (Fin n)} (hω : ω ∈ W) (hk : IsDeg k ω)
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

theorem polyPullback_single (B : Fin n → Fin n → K) (b : Fin n → K) (s : Finset (Fin n))
    (q : MvPolynomial (Fin n) K) (t : Finset (Fin n)) :
    polyPullback B b (Pi.single s q) t = polySubst B b q * C (wedgeProd B s t) := by
  rw [polyPullback_apply, sum_eq_single s (fun s' _ hs' => by simp [hs']) (by simp)]
  simp

theorem multiPart_single (β : Fin n →₀ ℕ) (u : Finset (Fin n)) (q : MvPolynomial (Fin n) K) :
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

theorem coeff_single_eq_eval {f : MvPolynomial (Fin n) K} {N : ℕ} (hf : f.IsHomogeneous N)
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

theorem isHomogeneous_polySubst_zero (B : Fin n → Fin n → K) {q : MvPolynomial (Fin n) K}
    {N : ℕ} (hq : q.IsHomogeneous N) : (polySubst B 0 q).IsHomogeneous N := by
  have := hq.aeval (g := fun i => ∑ l, C (B i l) * X l + C ((0 : Fin n → K) i)) (n := 1)
    fun i => by
      simp only [Pi.zero_apply, C_0, add_zero]
      exact IsHomogeneous.sum _ _ _ fun l _ => isHomogeneous_C_mul_X _ _
  simpa [polySubst] using this

theorem wedgeProd_congr_cols {B B' : Fin n → Fin n → K} {s : Finset (Fin n)}
    (h : ∀ i, ∀ l ∈ s, B i l = B' i l) (u : Finset (Fin n)) :
    ∀ t ⊆ s, wedgeProd B u t = wedgeProd B' u t := by
  induction u using Finset.induction_on_min with
  | empty => intro t _; simp
  | insert a u ha ih =>
    intro t ht
    rw [wedgeProd_insert_of_lt _ ha, wedgeProd_insert_of_lt _ ha, wedge_apply, wedge_apply]
    refine sum_congr rfl fun j hj => ?_
    rw [h a j (ht hj), ih _ ((erase_subset j t).trans ht)]

theorem wedgeProd_single_comp {σ : Fin n → Fin n} {s : Finset (Fin n)}
    (hσ : StrictMonoOn σ s) :
    wedgeProd (fun i => (Pi.single (σ i) 1 : Fin n → K)) s = Pi.single (s.image σ) 1 := by
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
    have : sgn (σ a) (s.image σ) = (1 : K) := by
      rw [sgn, filter_eq_empty_iff.2 fun x hx => not_lt.2 (hlt x hx).le]; simp
    rw [this, one_smul]

theorem wedgeProd_id_cols {B : Fin n → Fin n → K} {s : Finset (Fin n)}
    (h : ∀ i, ∀ l ∈ s, B i l = if i = l then 1 else 0) (u : Finset (Fin n)) :
    wedgeProd B u s = if u = s then 1 else 0 := by
  rw [wedgeProd_congr_cols (B' := fun i => (Pi.single i 1 : Fin n → K))
    (fun i l hl => by rw [h i l hl]; simp [Pi.single_apply, eq_comm]) u s subset_rfl,
    wedgeProd_single, Pi.single_apply]
  by_cases hu : u = s
  · subst hu; simp
  · simp [Ne.symm hu, hu]

theorem polyForm_eq_sum_monomial (ω : PolyForm K (Fin n)) :
    ω = ∑ u, ∑ β ∈ (ω u).support, (ω u).coeff β • Pi.single u (monomial β (1 : K)) := by
  classical
  funext t
  rw [Finset.sum_apply, sum_eq_single t (fun u _ hu => by
    rw [Finset.sum_apply]; exact sum_eq_zero fun β _ => by simp [Ne.symm hu])
    (by simp)]
  rw [Finset.sum_apply]
  conv_lhs => rw [(ω t).as_sum]
  refine sum_congr rfl fun β _ => ?_
  simp [smul_monomial]

theorem multiPart_eq_single {t₀ : Finset (Fin n)} {β : Fin n →₀ ℕ} (hβ : ∀ i ∉ t₀, β i = 0)
    {ω : PolyForm K (Fin n)} (hω : IsDeg #t₀ ω) :
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

theorem extDeriv_single_X_pow {p : Fin n} {s : Finset (Fin n)} (hp : p ∉ s) (m : ℕ) :
    Koszul.extDeriv (Pi.single s (X p ^ (m + 1)) : PolyForm K (Fin n)) =
      (((m + 1 : ℕ) : K) * sgn p s) • Pi.single (insert p s) (X p ^ m) := by
  classical
  have hd : ∀ j, pderiv j (X p ^ (m + 1) : MvPolynomial (Fin n) K) =
      if j = p then C ((m + 1 : ℕ) : K) * X p ^ m else 0 := by
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
      rw [show (sgn p s : MvPolynomial (Fin n) K) = C (sgn p s) by simp [sgn]]
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

/-! ### The invariant subspaces of `H_rΛᵏ` -/

theorem IsLinearInvariant.extDeriv_mem [CharZero K] {W : Submodule K (PolyForm K (Fin n))}
    (hW : IsLinearInvariant W) {m : ℕ} {p : Fin n} {s : Finset (Fin n)} (hp : p ∉ s)
    (hg : (Pi.single (insert p s) (X p ^ m) : PolyForm K (Fin n)) ∈ W) {η : PolyForm K (Fin n)}
    (hη : η ∈ homForm K (Fin n) (m + 1) #s) : Koszul.extDeriv η ∈ W := by
  classical
  set ζ : PolyForm K (Fin n) := Pi.single s (X p ^ (m + 1))
  have hc0 : (((m + 1 : ℕ) : K) * sgn p s) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)) (by rw [sgn]; exact pow_ne_zero _ (by norm_num))
  have hdζ : Koszul.extDeriv ζ ∈ W := by
    rw [extDeriv_single_X_pow hp]; exact W.smul_mem _ hg
  -- every `d(x^β dx_u)` with `#u = #s` and `|β| = m + 1`
  have key : ∀ u : Finset (Fin n), #u = #s → ∀ β : Fin n →₀ ℕ, β.degree = m + 1 →
      Koszul.extDeriv (Pi.single u (monomial β (1 : K))) ∈ W := by
    intro u hu β hβ
    obtain ⟨σ, hσ, hσu⟩ := exists_strictMonoOn_image hu.symm
    set B : Fin n → Fin n → K := fun i l =>
      if i = p then 1 else if i ∈ s then (Pi.single (σ i) 1 : Fin n → K) l else 0
    have hBζ : polyPullback B 0 ζ = Pi.single u ((∑ l, X l) ^ (m + 1)) := by
      funext t
      rw [polyPullback_single]
      have hsub : polySubst B 0 (X p ^ (m + 1)) = (∑ l, X l) ^ (m + 1) := by
        simp [polySubst, B]
      have hw : wedgeProd B s = Pi.single u 1 := by
        rw [wedgeProd_congr (θ' := fun i => (Pi.single (σ i) 1 : Fin n → K)) fun j hj => ?_,
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
    rw [← mul_one ((β.multinomial : ℕ) : K), ← smul_eq_mul, ← smul_monomial,
      show (Pi.single u (((β.multinomial : ℕ) : K) • monomial β (1 : K)) : PolyForm K (Fin n)) =
        ((β.multinomial : ℕ) : K) • Pi.single u (monomial β 1) from Pi.single_smul' _ _ _,
      Koszul.extDeriv_smul] at h2
    refine (W.smul_mem_iff (Nat.cast_ne_zero.2 (Nat.multinomial_pos _ _).ne')).1 h2
  -- `η` is a combination of the monomial forms
  have hlin : ∀ ω, Koszul.extDeriv ω = extDerivₗ K (Fin n) ω := fun _ => rfl
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

theorem IsLinearInvariant.closed_le [CharZero K] {W : Submodule K (PolyForm K (Fin n))}
    (hW : IsLinearInvariant W) {m k : ℕ} {ω : PolyForm K (Fin n)} (hω : ω ∈ W)
    (hωH : ω ∈ homForm K (Fin n) m k) (hκ : Koszul.koszul ω ≠ 0) :
    homForm K (Fin n) m k ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ≤ W := by
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
  set B : Fin n → Fin n → K := fun i l =>
    if l ∈ s then (if i = l then 1 else 0) else if l = p then a i else 0
  have hBcols : ∀ i, ∀ l ∈ s, B i l = if i = l then 1 else 0 := fun i l hl => by simp [B, hl]
  set ω₁ := polyPullback B 0 ω
  have hω₁ : ω₁ ∈ W := hW B ω hω
  set μ : Fin n → ℕ := fun i => (Finsupp.single p m) i + if i ∈ insert p s then 1 else 0
  set ω₂ := multiPart μ ω₁
  have hω₂ : ω₂ ∈ W := hW.multiPart_mem hω₁ μ
  set c := (ω₁ (insert p s)).coeff (Finsupp.single p m)
  have hcard : #(insert p s) = k + 1 := by rw [card_insert_of_notMem hp, hsk]
  have hω₂eq : ω₂ = c • (Pi.single (insert p s) (X p ^ m) : PolyForm K (Fin n)) := by
    have hdeg : IsDeg #(insert p s) ω₁ := by rw [hcard]; exact isDeg_polyPullback hωH.1 B 0
    rw [show ω₂ = multiPart (fun i => (Finsupp.single p m) i +
        if i ∈ insert p s then 1 else 0) ω₁ from rfl, multiPart_eq_single (fun i hi => by
        rw [Finsupp.single_apply, ite_eq_right]; exact fun h => hi (h ▸ mem_insert_self p s)) hdeg,
      ← Pi.single_smul', X_pow_eq_monomial, smul_monomial, smul_eq_mul, mul_one]
  -- `κ ω₂` has the coefficient `(κω)_s(a)` at `x_p^{m+1} dx_s`
  have hκω₂ :
      (Koszul.koszul ω₂ s).coeff (Finsupp.single p (m + 1)) = eval a (Koszul.koszul ω s) := by
    have hμ : ∀ i, (Finsupp.single p (m + 1)) i + (if i ∈ s then 1 else 0) = μ i := by
      intro i
      by_cases hip : i = p
      · subst hip; simp [μ, hp]
      · by_cases his : i ∈ s
        · simp [μ, Finsupp.single_apply, Ne.symm hip, his]
        · simp [μ, Finsupp.single_apply, Ne.symm hip, his, hip]
    rw [koszul_multiPart, multiPart, coeff_restrictForm, ite_eq_left hμ,
      ← polyPullback_koszul_linear]
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
  have hg : (Pi.single (insert p s) (X p ^ m) : PolyForm K (Fin n)) ∈ W := by
    have := W.smul_mem c⁻¹ hω₂
    rwa [hω₂eq, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  rintro ξ ⟨hξ, hdξ⟩
  obtain ⟨η, hη, rfl⟩ := Koszul.exists_extDeriv_eq_of_extDeriv_eq_zero (by omega) hξ hdξ
  rw [Nat.add_sub_cancel, ← hsk] at hη
  exact hW.extDeriv_mem hp hg hη

theorem koszul_extDeriv_of_koszul_eq_zero {r k : ℕ} {ξ : PolyForm K (Fin n)}
    (h : ξ ∈ homForm K (Fin n) r k) (hκ : Koszul.koszul ξ = 0) :
    Koszul.koszul (Koszul.extDeriv ξ) = ((r + k : ℕ) : K) • ξ := by
  have := Koszul.extDeriv_koszul_add_koszul_extDeriv_of_mem h
  rwa [hκ, Koszul.extDeriv_zero, zero_add] at this

theorem extDeriv_koszul_of_extDeriv_eq_zero {r k : ℕ} {ξ : PolyForm K (Fin n)}
    (h : ξ ∈ homForm K (Fin n) r k) (hd : Koszul.extDeriv ξ = 0) :
    Koszul.extDeriv (Koszul.koszul ξ) = ((r + k : ℕ) : K) • ξ := by
  have := Koszul.extDeriv_koszul_add_koszul_extDeriv_of_mem h
  rwa [hd, Koszul.koszul_zero, add_zero] at this

theorem IsLinearInvariant.comap_koszul {W : Submodule K (PolyForm K (Fin n))}
    (hW : IsLinearInvariant W) : IsLinearInvariant (W.comap (koszulₗ K (Fin n))) :=
  fun B ω hω => by
    change Koszul.koszul (polyPullback B 0 ω) ∈ W
    rw [← polyPullback_koszul_linear]
    exact hW B _ hω

theorem IsLinearInvariant.koszulClosed_le [CharZero K] {W : Submodule K (PolyForm K (Fin n))}
    (hW : IsLinearInvariant W) {m k : ℕ} {ω : PolyForm K (Fin n)} (hω : ω ∈ W)
    (hωH : ω ∈ homForm K (Fin n) (m + 1) k) (hκ : Koszul.koszul ω = 0) (h0 : ω ≠ 0) :
    homForm K (Fin n) (m + 1) k ⊓ LinearMap.ker (koszulₗ K (Fin n)) ≤ W := by
  set c : K := ((m + 1 + k : ℕ) : K)
  have hc : c ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpre : ∀ {ξ : PolyForm K (Fin n)}, ξ ∈ homForm K (Fin n) (m + 1) k →
      Koszul.koszul ξ = 0 → Koszul.koszul (c⁻¹ • Koszul.extDeriv ξ) = ξ := fun hξ hκξ => by
    rw [Koszul.koszul_smul, koszul_extDeriv_of_koszul_eq_zero hξ hκξ, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  have hmem : ∀ {ξ : PolyForm K (Fin n)}, ξ ∈ homForm K (Fin n) (m + 1) k →
      c⁻¹ • Koszul.extDeriv ξ ∈ homForm K (Fin n) m (k + 1) := fun hξ =>
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

theorem homForm_split [CharZero K] {m k : ℕ} (hmk : 0 < m + k) {ω : PolyForm K (Fin n)}
    (hω : ω ∈ homForm K (Fin n) m k) :
    ((m + k : ℕ) : K)⁻¹ • Koszul.koszul (Koszul.extDeriv ω) ∈
        homForm K (Fin n) m k ⊓ LinearMap.ker (koszulₗ K (Fin n)) ∧
      ((m + k : ℕ) : K)⁻¹ • Koszul.extDeriv (Koszul.koszul ω) ∈
        homForm K (Fin n) m k ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ∧
      ω = ((m + k : ℕ) : K)⁻¹ • Koszul.koszul (Koszul.extDeriv ω) +
        ((m + k : ℕ) : K)⁻¹ • Koszul.extDeriv (Koszul.koszul ω) := by
  set c : K := ((m + k : ℕ) : K)
  have hc : c ≠ 0 := Nat.cast_ne_zero.2 hmk.ne'
  have heq : ω = c⁻¹ • Koszul.koszul (Koszul.extDeriv ω) +
      c⁻¹ • Koszul.extDeriv (Koszul.koszul ω) := by
    rw [← smul_add, add_comm, Koszul.extDeriv_koszul_add_koszul_extDeriv_of_mem hω, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  have hb : c⁻¹ • Koszul.extDeriv (Koszul.koszul ω) ∈ homForm K (Fin n) m k := by
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

theorem IsLinearInvariant.koszulClosed_le_of_extDeriv_ne_zero [CharZero K]
    {W : Submodule K (PolyForm K (Fin n))} (hW : IsLinearInvariant W) {m k : ℕ}
    {ω : PolyForm K (Fin n)} (hω : ω ∈ W) (hωH : ω ∈ homForm K (Fin n) m k)
    (hd : Koszul.extDeriv ω ≠ 0) :
    homForm K (Fin n) m k ⊓ LinearMap.ker (koszulₗ K (Fin n)) ≤ W := by
  obtain _ | m := m
  · exact absurd (Koszul.extDeriv_eq_zero_of_mem_polyForm_zero (Koszul.homForm_le_polyForm _ _ hωH)) hd
  obtain ⟨hK, hD, heq⟩ := homForm_split (by omega) hωH
  by_cases hκ : Koszul.koszul ω = 0
  · exact hW.koszulClosed_le hω hωH hκ fun h => hd (by rw [h, Koszul.extDeriv_zero])
  have hDW := hW.closed_le hω hωH hκ
  have hω' := W.sub_mem hω (hDW hD)
  rw [eq_sub_of_add_eq heq.symm] at hK
  refine hW.koszulClosed_le hω' hK.1 (LinearMap.mem_ker.1 hK.2) fun h => hd ?_
  have := congrArg (extDerivₗ K (Fin n)) h
  rw [map_sub, map_zero, Koszul.extDerivₗ_apply, Koszul.extDerivₗ_apply] at this
  rwa [Koszul.extDeriv_smul, Koszul.extDeriv_extDeriv, smul_zero, sub_zero] at this

/-- In characteristic `0`, the linearly invariant subspaces of `H_mΛᵏ`, `m + k > 0`, are `0`, the
closed forms, the `κ`-closed forms and `H_mΛᵏ` ([AFW2006], §3.4; [FultonHarris1991], (6.9)). -/
theorem IsLinearInvariant.eq_of_le_homForm [CharZero K] {W : Submodule K (PolyForm K (Fin n))}
    (hW : IsLinearInvariant W) {m k : ℕ} (hmk : 0 < m + k) (hle : W ≤ homForm K (Fin n) m k) :
    W = ⊥ ∨ W = homForm K (Fin n) m k ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ∨
      W = homForm K (Fin n) m k ⊓ LinearMap.ker (koszulₗ K (Fin n)) ∨ W = homForm K (Fin n) m k := by
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

theorem homForm_inf_ker_extDeriv [CharZero K] (m k : ℕ) :
    homForm K (Fin n) m (k + 1) ⊓ LinearMap.ker (extDerivₗ K (Fin n)) =
      (homForm K (Fin n) (m + 1) k).map (extDerivₗ K (Fin n)) := by
  refine le_antisymm ?_ ?_
  · rintro ξ ⟨hξ, hd⟩
    obtain ⟨η, hη, rfl⟩ := Koszul.exists_extDeriv_eq_of_extDeriv_eq_zero (by omega) hξ hd
    exact ⟨η, by simpa using hη, rfl⟩
  · rintro _ ⟨η, hη, rfl⟩
    exact ⟨by simpa using Koszul.extDeriv_mem_homForm hη,
      LinearMap.mem_ker.2 (Koszul.extDeriv_extDeriv η)⟩

theorem homForm_inf_ker_koszul [CharZero K] (m k : ℕ) :
    homForm K (Fin n) (m + 1) k ⊓ LinearMap.ker (koszulₗ K (Fin n)) =
      (homForm K (Fin n) m (k + 1)).map (koszulₗ K (Fin n)) := by
  refine le_antisymm ?_ ?_
  · rintro ξ ⟨hξ, hκ⟩
    obtain ⟨η, hη, rfl⟩ := Koszul.exists_koszul_eq_of_koszul_eq_zero (by omega) hξ hκ
    exact ⟨η, by simpa using hη, rfl⟩
  · rintro _ ⟨η, hη, rfl⟩
    exact ⟨by simpa using Koszul.koszul_mem_homForm hη,
      LinearMap.mem_ker.2 (Koszul.koszul_koszul η)⟩

theorem isLinearInvariant_homForm (m k : ℕ) : IsLinearInvariant (homForm K (Fin n) m k) :=
  fun B ω hω => ⟨isDeg_polyPullback hω.1 B 0, fun t => by
    rw [polyPullback_apply]
    exact IsHomogeneous.sum _ _ _ fun s _ => by
      simpa using (isHomogeneous_polySubst_zero B (hω.2 s)).mul (isHomogeneous_C _ _)⟩

theorem isLinearInvariant_map_extDeriv_homForm (m k : ℕ) :
    IsLinearInvariant ((homForm K (Fin n) m k).map (extDerivₗ K (Fin n))) := by
  rintro B _ ⟨η, hη, rfl⟩
  exact ⟨_, isLinearInvariant_homForm m k B η hη, (polyPullback_extDeriv B 0 η).symm⟩

theorem isLinearInvariant_map_koszul_homForm (m k : ℕ) :
    IsLinearInvariant ((homForm K (Fin n) m k).map (koszulₗ K (Fin n))) := by
  rintro B _ ⟨η, hη, rfl⟩
  exact ⟨_, isLinearInvariant_homForm m k B η hη, (polyPullback_koszul_linear B η).symm⟩

theorem IsLinearInvariant.eq_of_le_homForm_succ [CharZero K] {W : Submodule K (PolyForm K (Fin n))}
    (hW : IsLinearInvariant W) {m k : ℕ} (hle : W ≤ homForm K (Fin n) (m + 1) (k + 1)) :
    W = ⊥ ∨ W = (homForm K (Fin n) (m + 2) k).map (extDerivₗ K (Fin n)) ∨
      W = (homForm K (Fin n) m (k + 2)).map (koszulₗ K (Fin n)) ∨
        W = homForm K (Fin n) (m + 1) (k + 1) := by
  rw [← homForm_inf_ker_extDeriv, ← homForm_inf_ker_koszul]
  exact hW.eq_of_le_homForm (by omega) hle

/-! ### Invariance under `GL(n)` -/

theorem exists_polyPullback_add_smul {m : ℕ} (B A : Fin n → Fin m → K) (b : Fin n → K)
    (ω : PolyForm K (Fin n)) : ∃ N, ∃ v : ℕ → PolyForm K (Fin m), 0 < N ∧
      ∀ c : K, polyPullback (fun i l => B i l + c * A i l) b ω = ∑ i ∈ range N, c ^ i • v i := by
  classical
  let ev (c : K) : Polynomial (MvPolynomial (Fin m) K) →+* MvPolynomial (Fin m) K :=
    Polynomial.evalRingHom (C c)
  let Bt : Fin n → Fin m → Polynomial (MvPolynomial (Fin m) K) := fun i l =>
    Polynomial.C (C (B i l)) + Polynomial.X * Polynomial.C (C (A i l))
  have hB : ∀ c i l, ev c (Bt i l) = C (B i l + c * A i l) := fun c i l => by
    simp only [ev, Bt, Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X, map_add,
      map_mul]
  let Q : MvPolynomial (Fin n) K →ₐ[K] Polynomial (MvPolynomial (Fin m) K) :=
    aeval fun i => ∑ l, Bt i l * Polynomial.C (X l) + Polynomial.C (C (b i))
  have hQ : ∀ c p, ev c (Q p) = polySubst (fun i l => B i l + c * A i l) b p := fun c p => by
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [algHom_C, algHom_C, Polynomial.algebraMap_apply]
      exact Polynomial.eval_C
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p i hp =>
      rw [map_mul, map_mul, hp, map_mul]
      simp only [Q, aeval_X, polySubst, map_add, map_sum, map_mul, hB]
      simp [ev]
  let P (t : Finset (Fin m)) : Polynomial (MvPolynomial (Fin m) K) :=
    ∑ s, Q (ω s) * wedgeProd Bt s t
  have hP : ∀ c t, ev c (P t) = polyPullback (fun i l => B i l + c * A i l) b ω t := fun c t => by
    rw [polyPullback_apply, map_sum]
    refine sum_congr rfl fun s _ => ?_
    rw [map_mul, hQ, map_wedgeProd, map_wedgeProd]
    congr 2
    funext i l
    exact hB c i l
  refine ⟨∑ t, (P t).natDegree + 1, fun i t => (P t).coeff i, by omega, fun c => ?_⟩
  funext t
  rw [← hP, Polynomial.coe_evalRingHom,
    Polynomial.eval_eq_sum_range' (n := ∑ t, (P t).natDegree + 1)
    (Nat.lt_succ_of_le (single_le_sum (f := fun t => (P t).natDegree) (fun _ _ => Nat.zero_le _)
      (mem_univ t))), Finset.sum_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_C_mul, C_pow, mul_comm]

theorem polyPullback_mem_of_forall_units [Infinite K] {W : Submodule K (PolyForm K (Fin n))}
    {b : Fin n → K} {ω : PolyForm K (Fin n)}
    (h : ∀ g : GL (Fin n) K, polyPullback (g : Matrix (Fin n) (Fin n) K) b ω ∈ W)
    (B : Fin n → Fin n → K) : polyPullback B b ω ∈ W := by
  obtain ⟨N, v, hN, hv⟩ := exists_polyPullback_add_smul B (1 : Matrix (Fin n) (Fin n) K) b ω
  have hev : ∀ᶠ c : K in Filter.cofinite, ∑ i ∈ range N, c ^ i • v i ∈ W := by
    have hp := (Matrix.charpoly_monic (-Matrix.of B)).ne_zero
    refine Filter.eventually_cofinite.2 ((Polynomial.finite_setOfPred_isRoot hp).subset
      fun c hc => ?_)
    by_contra hdet
    refine hc ?_
    rw [← hv]
    have hu : IsUnit (Matrix.of fun i l => B i l + c * (1 : Matrix (Fin n) (Fin n) K) i l).det := by
      rw [isUnit_iff_ne_zero]
      intro h0
      refine hdet ?_
      rw [Set.mem_ofPred_eq, Polynomial.IsRoot, Matrix.eval_charpoly, Matrix.scalar_apply,
        sub_neg_eq_add, add_comm, ← h0]
      congr 2
      ext i l
      by_cases hil : i = l
      · subst hil; simp [Matrix.diagonal]
      · simp [Matrix.diagonal, hil]
    exact h (Matrix.nonsingInvUnit _ hu)
  have h0 := hv 0
  simp only [zero_mul, add_zero] at h0
  rw [sum_eq_single 0 (fun i _ hi => by rw [zero_pow hi, zero_smul])
    (fun h => absurd (mem_range.2 hN) h), pow_zero, one_smul] at h0
  rw [h0]
  exact mem_of_eventually_sum_pow_smul_mem hev hN

/-- Invariance under the pullbacks `x ↦ g x` by the invertible linear maps, `g ∈ GL(n)`. -/
def IsGLInvariant (W : Submodule K (PolyForm K (Fin n))) : Prop :=
  ∀ g : GL (Fin n) K, ∀ ω ∈ W, polyPullback (g : Matrix (Fin n) (Fin n) K) 0 ω ∈ W

theorem IsLinearInvariant.isGLInvariant {W : Submodule K (PolyForm K (Fin n))}
    (hW : IsLinearInvariant W) : IsGLInvariant W := fun g => hW g

/-- Over an infinite field, invariance under `GL(n)` is invariance under all linear maps. -/
theorem IsGLInvariant.isLinearInvariant [Infinite K] {W : Submodule K (PolyForm K (Fin n))}
    (hW : IsGLInvariant W) : IsLinearInvariant W :=
  fun B ω hω => polyPullback_mem_of_forall_units (fun g => hW g ω hω) B

/-- In characteristic `0`, the `GL(n)`-invariant subspaces of `H_mΛᵏ`, `m + k > 0`, are `0`, the
closed forms, the `κ`-closed forms and `H_mΛᵏ` ([AFW2006], §3.4). -/
theorem IsGLInvariant.eq_of_le_homForm [CharZero K] {W : Submodule K (PolyForm K (Fin n))}
    (hW : IsGLInvariant W) {m k : ℕ} (hmk : 0 < m + k) (hle : W ≤ homForm K (Fin n) m k) :
    W = ⊥ ∨ W = homForm K (Fin n) m k ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ∨
      W = homForm K (Fin n) m k ⊓ LinearMap.ker (koszulₗ K (Fin n)) ∨
        W = homForm K (Fin n) m k :=
  hW.isLinearInvariant.eq_of_le_homForm hmk hle

theorem IsGLInvariant.eq_of_le_homForm_succ [CharZero K] {W : Submodule K (PolyForm K (Fin n))}
    (hW : IsGLInvariant W) {m k : ℕ} (hle : W ≤ homForm K (Fin n) (m + 1) (k + 1)) :
    W = ⊥ ∨ W = (homForm K (Fin n) (m + 2) k).map (extDerivₗ K (Fin n)) ∨
      W = (homForm K (Fin n) m (k + 2)).map (koszulₗ K (Fin n)) ∨
        W = homForm K (Fin n) (m + 1) (k + 1) :=
  hW.isLinearInvariant.eq_of_le_homForm_succ hle

theorem isAffineInvariant_of_forall_units [Infinite K] {X : Submodule K (PolyForm K (Fin n))}
    (hX : ∀ (g : GL (Fin n) K) (b : Fin n → K), ∀ ω ∈ X,
      polyPullback (g : Matrix (Fin n) (Fin n) K) b ω ∈ X) : IsAffineInvariant X :=
  fun B b ω hω => polyPullback_mem_of_forall_units (fun g => hX g b ω hω) B

end Feec.FiniteElement
