module

public import Feec.FiniteElement.InvariantForm
public import Feec.Counterexamples.PolynomialForms

/-!
# Invariant polynomial forms in positive characteristic

Over a field `K` of characteristic `0`, the `GL(n)`-invariant subspaces of `H_mΛᵏ` (`m + k > 0`)
are `0`, the closed forms `dH_{m+1}Λ^{k-1}`, the `κ`-closed forms `κH_{m-1}Λ^{k+1}` and `H_mΛᵏ`
(`Feec.FiniteElement.IsGLInvariant.eq_of_le_homForm`, [AFW2006], §3.4), and the closed forms of
`H_mΛ^{k+1}` are exact (`Feec.FiniteElement.homForm_inf_ker_extDeriv`). Both fail over **every**
field of characteristic `p > 0`, so both hold in all dimensions and degrees exactly in
characteristic `0` (`charZero_iff_classification_ker`, `charZero_iff_classification`,
`charZero_iff_closed_eq_exact`):

* **a Frobenius-twisted invariant subspace** (`coeffForm_powSpan_not_classified`,
  `coeffForm_powSpan_not_classified_succ`): with `q = p²`, the span `U` of the `q`-th powers
  `x_i^q` is mapped into itself by every linear substitution, as `(Σ_l b_l x_l)^q = Σ_l b_l^q x_l^q`
  (`polySubst_mem_powSpan`), so the `1`-forms `UΛ¹` with coefficients in `U` are a linearly
  invariant subspace of `H_qΛ¹` (`isLinearInvariant_coeffForm`). For `n ≥ 2` it contains
  `x_i^q dx_i`, which is not `κ`-closed (`κ(x_i^q dx_i) = x_i^{q+1}`), and it misses the exact form
  `d(x_i^{q-1} x_j^2)`, whose coefficient `q - 1 = -1` on `x_i^{q-2} x_j^2 dx_i` does not vanish
  while `x_i^{q-2} x_j^2 ∉ U`; so it is none of `0`, the closed forms, `dH_{q+1}Λ⁰`, the
  `κ`-closed forms, `κH_{q-1}Λ²` and `H_qΛ¹`;
* **a closed form that is not exact** (`closed_not_exact`): `x_i^{p-1} dx_i ∈ H_{p-1}Λ¹` is
  closed, and not `dη` for any `η ∈ H_pΛ⁰`, since the homotopy formula
  `(dκ + κd) η = (p + 0) η = 0` and `κη = 0` would give `κ(x_i^{p-1} dx_i) = x_i^p = 0`.

The constant `p + 0` of the homotopy formula is one of the integers that the proofs in
characteristic `0` invert. In dimension `1` every subspace of `H_mΛᵏ` is `0` or `H_mΛᵏ`
(`dim H_mΛᵏ ≤ 1`), so the first counterexample needs `n ≥ 2`.

## Main definitions

* `powSpan K n q`: the span of the `q`-th powers `x_i^q` of the coordinates.

## Main results

* `charZero_iff_classification_ker`, `charZero_iff_classification`: the classification of the
  `GL(n)`-invariant subspaces of `H_mΛᵏ` holds in every dimension iff `K` has characteristic `0`;
* `charZero_iff_closed_eq_exact`: the closed forms of `H_mΛ^{k+1}` are `dH_{m+1}Λᵏ` in every
  dimension iff `K` has characteristic `0`;
* `coeffForm_powSpan_not_classified`, `coeffForm_powSpan_not_classified_succ`,
  `closed_not_exact`: the counterexamples.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.2 (Theorem 3.1, the homotopy formula), §3.4 (the decomposition (3.10) into irreducible
  invariant subspaces)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.Counterexamples.PositiveCharacteristic

open Feec.FiniteElement ExteriorFibre
open Koszul (PolyForm homForm coeffForm koszulₗ extDerivₗ)

variable {K : Type*} [Field K] {n : ℕ}

/-! ### Forms with coefficients in an invariant space of polynomials -/

/-- **Forms with coefficients in a space of polynomials closed under linear substitutions are
linearly invariant.** -/
theorem isLinearInvariant_coeffForm {S : Submodule K (MvPolynomial (Fin n) K)}
    (hS : ∀ (B : Fin n → Fin n → K), ∀ f ∈ S, polySubst B 0 f ∈ S) (k : ℕ) :
    IsLinearInvariant (coeffForm K k S) := fun B ω hω =>
  ⟨isDeg_polyPullback hω.1 B 0, fun t => by
    rw [polyPullback_apply]
    exact S.sum_mem fun s _ => by
      rw [mul_comm, ← smul_eq_C_mul]
      exact S.smul_mem _ (hS B _ (hω.2 s))⟩

/-! ### Powers of the coordinates -/

variable (K n) in
/-- The span of the `q`-th powers `x_i^q` of the coordinates. -/
def powSpan (q : ℕ) : Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K (Set.range fun i => X i ^ q)

theorem powSpan_le_homogeneousSubmodule (q : ℕ) :
    powSpan K n q ≤ homogeneousSubmodule (Fin n) K q :=
  Submodule.span_le.2 <| Set.range_subset_iff.2 fun i =>
    (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X_pow i q)

/-- The polynomials of `powSpan K n q` have no monomial `x^α` other than the `x_i^q`. -/
theorem coeff_eq_zero_of_mem_powSpan {q : ℕ} {f : MvPolynomial (Fin n) K}
    (hf : f ∈ powSpan K n q) {α : Fin n →₀ ℕ} (hα : ∀ i, Finsupp.single i q ≠ α) :
    f.coeff α = 0 := by
  have : powSpan K n q ≤ LinearMap.ker (lcoeff K α) :=
    Submodule.span_le.2 <| Set.range_subset_iff.2 fun i => by
      simp [coeff_X_pow, hα i]
  exact this hf

/-- **`(Σ_l b_l x_l)^{p^e} = Σ_l b_l^{p^e} x_l^{p^e}`**: in characteristic `p` the span of the
`p^e`-th powers of the coordinates is closed under linear substitutions. -/
theorem polySubst_mem_powSpan (p : ℕ) [ExpChar K p] (e : ℕ) (B : Fin n → Fin n → K)
    {f : MvPolynomial (Fin n) K} (hf : f ∈ powSpan K n (p ^ e)) :
    polySubst B 0 f ∈ powSpan K n (p ^ e) := by
  induction hf using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨i, rfl⟩ := h
    rw [map_pow, polySubst, aeval_X, Pi.zero_apply, C_0, add_zero, sum_pow_char_pow]
    exact Submodule.sum_mem _ fun l _ => by
      rw [mul_pow, ← C_pow, ← smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
  | smul c f _ hf => rw [map_smul]; exact Submodule.smul_mem _ c hf

/-! ### A Frobenius-twisted invariant subspace of `H_{p²}Λ¹` -/

section Frobenius

variable (p : ℕ) [CharP K p]

theorem isLinearInvariant_coeffForm_powSpan [Fact p.Prime] (k : ℕ) :
    IsLinearInvariant (coeffForm K k (powSpan K n (p ^ 2))) :=
  isLinearInvariant_coeffForm (fun B _ hf => polySubst_mem_powSpan p 2 B hf) k

theorem coeffForm_powSpan_le_homForm (q k : ℕ) :
    coeffForm K k (powSpan K n q) ≤ homForm K (Fin n) q k := fun _ hω =>
  ⟨hω.1, fun s => (mem_homogeneousSubmodule _ _).1 (powSpan_le_homogeneousSubmodule q (hω.2 s))⟩

/-- `x_i^q dx_i`. -/
def powDx (i : Fin n) (q : ℕ) : PolyForm K (Fin n) := Pi.single {i} (X i ^ q)

theorem powDx_mem_coeffForm (i : Fin n) (q : ℕ) :
    powDx i q ∈ coeffForm K 1 (powSpan K n q) := by
  refine ⟨fun s hs => ?_, fun s => ?_⟩
  · rw [powDx, Pi.single_apply, ite_eq_right fun h => absurd (by rw [h, card_singleton]) hs]
  · rw [powDx, Pi.single_apply]
    split_ifs
    · exact Submodule.subset_span ⟨i, rfl⟩
    · exact zero_mem _

/-- `κ(x_i^q dx_i) = x_i^{q+1}`. -/
theorem koszul_powDx (i : Fin n) (q : ℕ) :
    Koszul.koszul (powDx (K := K) i q) ∅ = X i ^ (q + 1) := by
  rw [Koszul.koszul_apply, compl_empty, sum_eq_single i (fun l _ hl => by
    simp [powDx, hl]) (by simp)]
  simp [powDx, sgn, pow_succ, mul_comm]

theorem koszul_powDx_ne_zero (i : Fin n) (q : ℕ) : Koszul.koszul (powDx (K := K) i q) ≠ 0 :=
  fun h => by simpa [koszul_powDx] using congrFun h ∅

/-- `d(x_i^m x_j^2)`, an exact `1`-form. -/
def dPowMulSq (i j : Fin n) (m : ℕ) : PolyForm K (Fin n) :=
  Koszul.extDeriv (Pi.single ∅ (X i ^ m * X j ^ 2))

theorem dPowMulSq_mem_map (i j : Fin n) (m : ℕ) :
    dPowMulSq (K := K) i j m ∈ (homForm K (Fin n) (m + 2) 0).map (extDerivₗ K (Fin n)) := by
  refine ⟨Pi.single ∅ (X i ^ m * X j ^ 2), ⟨fun s hs => ?_, fun s => ?_⟩, rfl⟩
  · rw [Pi.single_apply, ite_eq_right fun h => absurd (by rw [h, card_empty]) hs]
  · rw [Pi.single_apply]
    split_ifs
    · exact (isHomogeneous_X_pow i m).mul (isHomogeneous_X_pow j 2)
    · exact isHomogeneous_zero _ _ _

/-- The coefficient of `x_i^{m-1} x_j^2 dx_i` in `d(x_i^m x_j^2)` is `m`. -/
theorem coeff_dPowMulSq {i j : Fin n} (hij : i ≠ j) {m : ℕ} (hm : 1 ≤ m) :
    (dPowMulSq (K := K) i j m {i}).coeff (Finsupp.single i (m - 1) + Finsupp.single j 2) =
      (m : K) := by
  have he : Finsupp.single i m + Finsupp.single j 2 - Finsupp.single i 1 =
      Finsupp.single i (m - 1) + Finsupp.single j 2 := by
    ext l
    simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
      Finsupp.single_apply]
    split_ifs <;> omega
  rw [dPowMulSq, Koszul.extDeriv_apply, sum_singleton, erase_singleton, Pi.single_eq_same,
    X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul, pderiv_monomial, he]
  simp [sgn, Finset.filter_singleton, hij.symm]

theorem dPowMulSq_mem_homForm (i j : Fin n) (m : ℕ) :
    dPowMulSq (K := K) i j m ∈
      homForm K (Fin n) (m + 1) 1 ⊓ LinearMap.ker (extDerivₗ K (Fin n)) := by
  obtain ⟨η, hη, hηd⟩ := dPowMulSq_mem_map (K := K) i j m
  rw [← hηd, Koszul.extDerivₗ_apply]
  exact ⟨by simpa using Koszul.extDeriv_mem_homForm hη, by
    rw [SetLike.mem_coe, LinearMap.mem_ker, Koszul.extDerivₗ_apply, Koszul.extDeriv_extDeriv]⟩

/-- `d(x_i^{q-1} x_j^2) ∉ UΛ¹` for `q = p²`: its coefficient `q - 1 = -1` on `x_i^{q-2} x_j^2 dx_i`
does not vanish, and `x_i^{q-2} x_j^2` is not a `q`-th power of a coordinate. -/
theorem dPowMulSq_notMem [Fact p.Prime] {i j : Fin n} (hij : i ≠ j) {m : ℕ} (hm : m + 1 = p ^ 2) :
    dPowMulSq (K := K) i j m ∉ coeffForm K 1 (powSpan K n (m + 1)) := fun h => by
  have hp := (Fact.out : p.Prime).two_le
  have hq : 4 ≤ p ^ 2 := by nlinarith
  have h0 := coeff_eq_zero_of_mem_powSpan (h.2 {i})
    (α := Finsupp.single i (m - 1) + Finsupp.single j 2) fun l hl => by
      have := DFunLike.congr_fun hl j
      simp only [Finsupp.add_apply, Finsupp.single_apply, hij, ite_true] at this
      split_ifs at this <;> omega
  rw [coeff_dPowMulSq hij (by omega)] at h0
  have hq0 : ((m + 1 : ℕ) : K) = 0 := by
    rw [hm, Nat.cast_pow, CharP.cast_eq_zero, zero_pow two_ne_zero]
  push_cast at hq0
  exact one_ne_zero (by linear_combination hq0 - h0)

/-- **In characteristic `p > 0`, `UΛ¹` (`U` spanned by the `x_l^{p²}`) is a linearly invariant
subspace of `H_{p²}Λ¹` that is none of `0`, the closed forms, the `κ`-closed forms and
`H_{p²}Λ¹`** (`n ≥ 2`), against `IsLinearInvariant.eq_of_le_homForm`. -/
theorem coeffForm_powSpan_not_classified [Fact p.Prime] {i j : Fin n} (hij : i ≠ j) {m : ℕ}
    (hm : m + 1 = p ^ 2) :
    ¬ (coeffForm K 1 (powSpan K n (m + 1)) = ⊥ ∨
      coeffForm K 1 (powSpan K n (m + 1)) =
        homForm K (Fin n) (m + 1) 1 ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ∨
      coeffForm K 1 (powSpan K n (m + 1)) =
        homForm K (Fin n) (m + 1) 1 ⊓ LinearMap.ker (koszulₗ K (Fin n)) ∨
      coeffForm K 1 (powSpan K n (m + 1)) = homForm K (Fin n) (m + 1) 1) := by
  have hψ := dPowMulSq_notMem (K := K) p hij hm
  have hξ := powDx_mem_coeffForm (K := K) i (m + 1)
  rintro (h | h | h | h) <;> rw [h] at hξ hψ
  · exact koszul_powDx_ne_zero i _ (by rw [(Submodule.mem_bot K).1 hξ, Koszul.koszul_zero])
  · exact hψ (dPowMulSq_mem_homForm i j m)
  · exact koszul_powDx_ne_zero i _ (LinearMap.mem_ker.1 hξ.2)
  · exact hψ (dPowMulSq_mem_homForm i j m).1

/-- **In characteristic `p > 0`, `UΛ¹` is none of `0`, `dH_{p²+1}Λ⁰`, `κH_{p²-1}Λ²` and
`H_{p²}Λ¹`** (`n ≥ 2`), against `IsLinearInvariant.eq_of_le_homForm_succ` ([AFW2006], §3.4). -/
theorem coeffForm_powSpan_not_classified_succ [Fact p.Prime] {i j : Fin n} (hij : i ≠ j) {m : ℕ}
    (hm : m + 1 = p ^ 2) :
    ¬ (coeffForm K 1 (powSpan K n (m + 1)) = ⊥ ∨
      coeffForm K 1 (powSpan K n (m + 1)) =
        (homForm K (Fin n) (m + 2) 0).map (extDerivₗ K (Fin n)) ∨
      coeffForm K 1 (powSpan K n (m + 1)) = (homForm K (Fin n) m 2).map (koszulₗ K (Fin n)) ∨
      coeffForm K 1 (powSpan K n (m + 1)) = homForm K (Fin n) (m + 1) 1) := by
  have hψ := dPowMulSq_notMem (K := K) p hij hm
  have hξ := powDx_mem_coeffForm (K := K) i (m + 1)
  rintro (h | h | h | h) <;> rw [h] at hξ hψ
  · exact koszul_powDx_ne_zero i _ (by rw [(Submodule.mem_bot K).1 hξ, Koszul.koszul_zero])
  · exact hψ (dPowMulSq_mem_map i j m)
  · obtain ⟨η, -, hη⟩ := hξ
    exact koszul_powDx_ne_zero i _ (by rw [← hη, Koszul.koszulₗ_apply, Koszul.koszul_koszul])
  · exact hψ (dPowMulSq_mem_homForm i j m).1

/-! ### A closed form that is not exact -/

theorem extDeriv_powDx (i : Fin n) (m : ℕ) : Koszul.extDeriv (powDx (K := K) i m) = 0 := by
  funext s
  refine sum_eq_zero fun l hl => ?_
  by_cases h : s.erase l = {i}
  · have hli : l ≠ i := by
      rintro rfl
      exact notMem_erase l s (by rw [h]; exact mem_singleton_self l)
    simp [powDx, h, (pderiv l).leibniz_pow, pderiv_X_of_ne (Ne.symm hli)]
  · simp [powDx, h]

/-- **In characteristic `p > 0`, `x_i^{p-1} dx_i ∈ H_{p-1}Λ¹` is closed and not exact**: were
it `dη`, `η ∈ H_pΛ⁰`, the homotopy formula `(dκ + κd) η = p η = 0` and `κη = 0` would give
`κ(x_i^{p-1} dx_i) = x_i^p = 0`. Against `homForm_inf_ker_extDeriv`. -/
theorem closed_not_exact (i : Fin n) {m : ℕ} (hm : m + 1 = p) :
    powDx (K := K) i m ∈ homForm K (Fin n) m 1 ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ∧
      powDx (K := K) i m ∉ (homForm K (Fin n) (m + 1) 0).map (extDerivₗ K (Fin n)) := by
  refine ⟨⟨coeffForm_powSpan_le_homForm m 1 (powDx_mem_coeffForm i m), extDeriv_powDx i m⟩, ?_⟩
  rintro ⟨η, hη, hηd⟩
  have h := Koszul.extDeriv_koszul_add_koszul_extDeriv_of_isHomogeneous hη.2 hη.1
  rw [PolynomialForms.koszul_eq_zero_of_isDeg_zero hη.1, Koszul.extDeriv_zero, zero_add,
    add_zero, hm, CharP.cast_eq_zero, zero_smul] at h
  exact koszul_powDx_ne_zero i m (by rw [← hηd, Koszul.extDerivₗ_apply, h])

end Frobenius

/-! ### Characteristic `0` is necessary -/

variable (K) in
/-- **The classification of the `GL(n)`-invariant subspaces of `H_mΛᵏ` (`m + k > 0`) as `0`, the
closed forms, the `κ`-closed forms and `H_mΛᵏ` holds in every dimension iff `K` has characteristic
`0`** (`IsGLInvariant.eq_of_le_homForm`, `coeffForm_powSpan_not_classified`). -/
theorem charZero_iff_classification_ker :
    CharZero K ↔ ∀ (n : ℕ) (W : Submodule K (PolyForm K (Fin n))), IsGLInvariant W →
      ∀ m k, 0 < m + k → W ≤ homForm K (Fin n) m k →
        W = ⊥ ∨ W = homForm K (Fin n) m k ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ∨
          W = homForm K (Fin n) m k ⊓ LinearMap.ker (koszulₗ K (Fin n)) ∨
            W = homForm K (Fin n) m k := by
  refine ⟨fun _ n W hW m k hmk hle => hW.eq_of_le_homForm hmk hle, fun h => ?_⟩
  by_contra hK
  obtain ⟨p, _, _⟩ := (CharP.exists' K).resolve_left hK
  have hp := (Fact.out : p.Prime).pos
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = p ^ 2 := ⟨p ^ 2 - 1, by have := Nat.one_le_pow 2 p hp; omega⟩
  exact coeffForm_powSpan_not_classified (n := 2) p (i := 0) (j := 1) (by decide) hm
    (h 2 _ (hm ▸ isLinearInvariant_coeffForm_powSpan p 1).isGLInvariant (m + 1) 1 (by omega)
      (coeffForm_powSpan_le_homForm _ 1))

variable (K) in
/-- **[AFW2006], §3.4: the `GL(n)`-invariant subspaces of `H_rΛᵏ` (`r, k ≥ 1`) are `0`,
`dH_{r+1}Λ^{k-1}`, `κH_{r-1}Λ^{k+1}` and `H_rΛᵏ` in every dimension iff `K` has characteristic
`0`** (`IsGLInvariant.eq_of_le_homForm_succ`, `coeffForm_powSpan_not_classified_succ`). -/
theorem charZero_iff_classification :
    CharZero K ↔ ∀ (n : ℕ) (W : Submodule K (PolyForm K (Fin n))), IsGLInvariant W →
      ∀ m k, W ≤ homForm K (Fin n) (m + 1) (k + 1) →
        W = ⊥ ∨ W = (homForm K (Fin n) (m + 2) k).map (extDerivₗ K (Fin n)) ∨
          W = (homForm K (Fin n) m (k + 2)).map (koszulₗ K (Fin n)) ∨
            W = homForm K (Fin n) (m + 1) (k + 1) := by
  refine ⟨fun _ n W hW m k hle => hW.eq_of_le_homForm_succ hle, fun h => ?_⟩
  by_contra hK
  obtain ⟨p, _, _⟩ := (CharP.exists' K).resolve_left hK
  have hp := (Fact.out : p.Prime).pos
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = p ^ 2 := ⟨p ^ 2 - 1, by have := Nat.one_le_pow 2 p hp; omega⟩
  exact coeffForm_powSpan_not_classified_succ (n := 2) p (i := 0) (j := 1) (by decide) hm
    (h 2 _ (hm ▸ isLinearInvariant_coeffForm_powSpan p 1).isGLInvariant m 0
      (coeffForm_powSpan_le_homForm _ 1))

variable (K) in
/-- **The closed forms of `H_mΛ^{k+1}` are `dH_{m+1}Λᵏ` in every dimension iff `K` has
characteristic `0`** (`homForm_inf_ker_extDeriv`, `closed_not_exact`). -/
theorem charZero_iff_closed_eq_exact :
    CharZero K ↔ ∀ n m k, homForm K (Fin n) m (k + 1) ⊓ LinearMap.ker (extDerivₗ K (Fin n)) =
      (homForm K (Fin n) (m + 1) k).map (extDerivₗ K (Fin n)) := by
  refine ⟨fun _ n m k => homForm_inf_ker_extDeriv m k, fun h => ?_⟩
  by_contra hK
  obtain ⟨p, _, _⟩ := (CharP.exists' K).resolve_left hK
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = p := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
  obtain ⟨h1, h2⟩ := closed_not_exact (K := K) p (0 : Fin 1) hm
  exact h2 (h 1 m 0 ▸ h1)

end Feec.Counterexamples.PositiveCharacteristic
