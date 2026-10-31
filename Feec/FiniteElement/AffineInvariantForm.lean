module

public import Feec.FiniteElement.InvariantForm

/-!
# The affinely invariant spaces of polynomial differential forms

For `0 < k < n`, the nonzero finite-dimensional spaces of polynomial `k`-forms on `ℝⁿ` mapped into
themselves by the pullback of every affine map `φ : ℝⁿ → ℝⁿ` are exactly the spaces

  `X(r, s, k, n) = dP_{r+1}Λ^{k-1} + κP_sΛ^{k+1}`,  `r ≥ 0`, `-1 ≤ s ≤ r`

(`κP_{-1} = 0`) of [AFW2006], Theorems 3.5–3.6: the full spaces `P_rΛᵏ = X(r, r - 1)`, the trimmed
spaces `P_{r+1}⁻Λᵏ = X(r, r)` and, for `s < r - 1`, the spaces of forms of `P_rΛᵏ` with
`dω ∈ P_sΛ^{k+1}`. The proof follows [AFW2006], §3.4, with the representation theory of `GL(n)`
replaced by the elementary `IsLinearInvariant.eq_of_le_homForm` (`Feec.FiniteElement.InvariantForm`):
an affinely invariant space is the sum of the summands `dH_{j+1}Λ^{k-1}` and `κH_{j-1}Λ^{k+1}` of
its homogeneous components that it contains (`IsLinearInvariant.le_of_summands`), and the
translations force these to be initial segments in `j` (Lemma 3.7).

## Main results

* **[AFW2006], Theorem 3.5**: `isAffineInvariant_sup` (`X(r, s, k, n)` is affinely invariant for
  `s ≤ r`, `k ≥ 1`), `isAffineInvariant_map_extDeriv` (`s = -1`); the cases `s = r`
  (`sup_eq_polyFormMinus`: `X(r, r) = P_{r+1}⁻Λᵏ`), `s = r - 1` (`sup_eq_polyForm`:
  `X(r + 1, r) = P_{r+1}Λᵏ`; `map_extDeriv_polyForm_one_eq`: `X(0, -1) = P_0Λᵏ`). The description
  of the third kind (`s < r - 1`) as `P_{s+1}Λᵏ + dP_{r+1}Λ^{k-1} = {ω ∈ P_rΛᵏ | dω ∈ P_sΛ^{k+1}}`
  is not formalized.
* **[AFW2006], Lemma 3.7** (translations): `IsAffineInvariant.closed_le_of_succ`,
  `IsAffineInvariant.koszulClosed_le_of_succ`, `IsAffineInvariant.closed_le_of_koszulClosed_le`.
* **[AFW2006], Theorem 3.6**: `IsAffineInvariant.eq_sup`, **the classification of the affinely
  invariant spaces of polynomial `k`-forms**, `0 < k < n`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.4: (3.18), (3.19), Theorem 3.5, Theorem 3.6, Lemma 3.7

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre
open Koszul (PolyForm homForm polyForm polyFormMinus homComp koszulₗ extDerivₗ)

variable {n : ℕ}

/-! ### Monomial forms `x_p^j dx_t` -/

/-- The identity matrix, as the coefficient function taken by `polyPullback`. -/
def idMatrix : Fin n → Fin n → ℝ := fun i l => if i = l then 1 else 0

theorem single_X_pow_mem_homForm {t : Finset (Fin n)} {k : ℕ} (ht : #t = k) (p : Fin n)
    (j : ℕ) : (Pi.single t (X p ^ j) : PolyForm ℝ (Fin n)) ∈ homForm ℝ (Fin n) j k := by
  refine ⟨fun s hs => ?_, fun s => ?_⟩
  · have : s ≠ t := fun h => hs (h ▸ ht)
    simp [this]
  · by_cases h : s = t
    · subst h; simpa using isHomogeneous_X_pow p j
    · simpa [h] using isHomogeneous_zero (Fin n) ℝ j

theorem single_X_pow_ne_zero (t : Finset (Fin n)) (p : Fin n) (j : ℕ) :
    (Pi.single t (X p ^ j) : PolyForm ℝ (Fin n)) ≠ 0 := fun h => by
  have := congrFun h t
  simp at this

/-- `x_p^j dx_t` is closed for `p ∈ t`: it is a multiple of `d(x_p^{j+1} dx_{t ∖ p})`. -/
theorem extDeriv_single_X_pow_of_mem {t : Finset (Fin n)} {p : Fin n} (hp : p ∈ t) (j : ℕ) :
    Koszul.extDeriv (Pi.single t (X p ^ j) : PolyForm ℝ (Fin n)) = 0 := by
  have h := extDeriv_single_X_pow (notMem_erase p t) j
  rw [insert_erase hp] at h
  have hc : (((j + 1 : ℕ) : ℝ) * sgn p (t.erase p)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero j))
      (by rw [sgn]; exact pow_ne_zero _ (by norm_num))
  have : (Pi.single t (X p ^ j) : PolyForm ℝ (Fin n)) =
      (((j + 1 : ℕ) : ℝ) * sgn p (t.erase p))⁻¹ •
        Koszul.extDeriv (Pi.single (t.erase p) (X p ^ (j + 1))) := by
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [this, Koszul.extDeriv_smul, Koszul.extDeriv_extDeriv, smul_zero]

/-- A nonzero closed form of `H_rΛᵏ`, `r + k > 0`, is not `κ`-closed. -/
theorem koszul_ne_zero_of_extDeriv_eq_zero {r k : ℕ} (hrk : 0 < r + k) {ω : PolyForm ℝ (Fin n)}
    (h : ω ∈ homForm ℝ (Fin n) r k) (hd : Koszul.extDeriv ω = 0) (h0 : ω ≠ 0) :
    Koszul.koszul ω ≠ 0 := fun hκ => h0 <| by
  have := extDeriv_koszul_of_extDeriv_eq_zero h hd
  rw [hκ, Koszul.extDeriv_zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hrk.ne')

/-- A nonzero `κ`-closed form of `H_rΛᵏ`, `r + k > 0`, is not closed. -/
theorem extDeriv_ne_zero_of_koszul_eq_zero {r k : ℕ} (hrk : 0 < r + k) {ω : PolyForm ℝ (Fin n)}
    (h : ω ∈ homForm ℝ (Fin n) r k) (hκ : Koszul.koszul ω = 0) (h0 : ω ≠ 0) :
    Koszul.extDeriv ω ≠ 0 := fun hd => h0 <| by
  have := koszul_extDeriv_of_koszul_eq_zero h hκ
  rw [hd, Koszul.koszul_zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hrk.ne')

/-! ### Translations -/

theorem polyPullback_idMatrix_single (b : Fin n → ℝ) (t : Finset (Fin n))
    (q : MvPolynomial (Fin n) ℝ) :
    polyPullback idMatrix b (Pi.single t q) =
      Pi.single t (polySubst idMatrix b q) := by
  funext s
  rw [polyPullback_single, wedgeProd_id_cols (B := idMatrix) (s := s) (fun i l _ => rfl)]
  by_cases h : t = s
  · subst h; simp
  · simp [h, Ne.symm h]

theorem polySubst_idMatrix_X (b : Fin n → ℝ) (q : Fin n) :
    polySubst idMatrix b (X q) = X q + C (b q) := by
  simp [polySubst, idMatrix]

theorem homogeneousComponent_X_add_C_pow (p : Fin n) (c : ℝ) {j m : ℕ} (hj : j ≤ m) :
    homogeneousComponent j ((X p + C c) ^ m : MvPolynomial (Fin n) ℝ) =
      C (c ^ (m - j) * (m.choose j : ℝ)) * X p ^ j := by
  have hterm : ∀ i, (X p ^ i * C c ^ (m - i) * (m.choose i : MvPolynomial (Fin n) ℝ)) =
      C (c ^ (m - i) * (m.choose i : ℝ)) * X p ^ i := fun i => by
    rw [map_mul, map_pow, map_natCast]; ring
  have hX : ∀ i, homogeneousComponent j (X p ^ i : MvPolynomial (Fin n) ℝ) =
      if i = j then X p ^ i else 0 := fun i => by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X_pow p i))]
    simp only [eq_comm]
  simp_rw [add_pow, map_sum, hterm, homogeneousComponent_C_mul, hX, mul_ite, mul_zero]
  rw [sum_ite_eq' (range (m + 1)), ite_eq_left (mem_range.2 (by omega))]

theorem homComp_single (j : ℕ) (t : Finset (Fin n)) (q : MvPolynomial (Fin n) ℝ) :
    homComp j (Pi.single t q : PolyForm ℝ (Fin n)) = Pi.single t (homogeneousComponent j q) := by
  funext s
  rw [Koszul.homComp_apply]
  by_cases h : s = t
  · subst h; simp
  · simp [h]

theorem homComp_smul (j : ℕ) (c : ℝ) (ω : PolyForm ℝ (Fin n)) :
    homComp j (c • ω) = c • homComp j ω := by
  funext s; simp [Koszul.homComp_apply]

/-- The translate of `x_q^m dx_t` by `c e_p`: `(x_q + c [q = p])^m dx_t`. -/
theorem translate_single_X_pow (p : Fin n) (c : ℝ) (t : Finset (Fin n)) (q : Fin n) (m : ℕ) :
    polyPullback idMatrix (Pi.single p c : Fin n → ℝ) (Pi.single t (X q ^ m)) =
      Pi.single t ((X q + C ((Pi.single p c : Fin n → ℝ) q)) ^ m) := by
  rw [polyPullback_idMatrix_single, map_pow, polySubst_idMatrix_X]

/-- `homComp j` of the translate of `x_p^{j+1} dx_t` by `e_p` is `(j + 1) x_p^j dx_t`. -/
theorem homComp_translate_single_X_pow (p : Fin n) (t : Finset (Fin n)) (j : ℕ) :
    homComp j (polyPullback idMatrix (Pi.single p 1 : Fin n → ℝ)
        (Pi.single t (X p ^ (j + 1)))) =
      ((j + 1 : ℕ) : ℝ) • (Pi.single t (X p ^ j) : PolyForm ℝ (Fin n)) := by
  rw [translate_single_X_pow, homComp_single, Pi.single_eq_same,
    homogeneousComponent_X_add_C_pow _ _ (Nat.le_succ j), ← Pi.single_smul', smul_eq_C_mul]
  simp [Nat.choose_succ_self_right]

/-- Contraction with `e_p`: `ι_{e_p}(f dx_t) = ε(p, t ∖ p) f dx_{t ∖ p}` for `p ∈ t`. -/
theorem interior_single_single {p : Fin n} {t : Finset (Fin n)} (hp : p ∈ t)
    (f : MvPolynomial (Fin n) ℝ) :
    interior (fun l => C ((Pi.single p 1 : Fin n → ℝ) l)) (Pi.single t f : PolyForm ℝ (Fin n)) =
      Pi.single (t.erase p) (C (sgn p (t.erase p)) * f) := by
  funext s
  rw [interior_apply]
  by_cases hps : p ∈ s
  · rw [sum_eq_zero fun l hl => ?_]
    · have : s ≠ t.erase p := fun h => notMem_erase p t (h ▸ hps)
      simp [this]
    · have hlp : l ≠ p := fun h => (mem_compl.1 hl) (h ▸ hps)
      simp [Pi.single_apply, hlp]
  · rw [sum_eq_single p (fun l _ hlp => by simp [Pi.single_apply, hlp]) (fun h => absurd
      (mem_compl.2 hps) h)]
    by_cases hs : s = t.erase p
    · subst hs
      rw [insert_erase hp]
      simp [show (sgn p (t.erase p) : MvPolynomial (Fin n) ℝ) = C (sgn p (t.erase p)) by
        simp [sgn]]
    · have : insert p s ≠ t := fun h => hs (by rw [← h, erase_insert hps])
      simp [hs, this]

theorem exists_card_eq_mem {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ t : Finset (Fin n), #t = k ∧ t.Nonempty := by
  obtain ⟨t, -, ht⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := k)
    (by simpa using hkn)
  exact ⟨t, ht, card_pos.1 (by omega)⟩

/-! ### The translation lemmas ([AFW2006], Lemma 3.7) -/

/-- **[AFW2006], Lemma 3.7 (1)**, in the form used in the proof of Theorem 3.6: in an affinely
invariant space, the closed forms of degree `j + 1` bring those of degree `j` (`1 ≤ k ≤ n`): the
translate of `x_p^{j+1} dx_t` (`p ∈ t`) by `e_p` has the degree-`j` part `(j + 1) x_p^j dx_t`,
closed, nonzero, hence not `κ`-closed. -/
theorem IsAffineInvariant.closed_le_of_succ {V : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hV : IsAffineInvariant V) {j k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (h : homForm ℝ (Fin n) (j + 1) k ⊓ LinearMap.ker (extDerivₗ ℝ (Fin n)) ≤ V) :
    homForm ℝ (Fin n) j k ⊓ LinearMap.ker (extDerivₗ ℝ (Fin n)) ≤ V := by
  obtain ⟨t, ht, p, hp⟩ := exists_card_eq_mem hk hkn
  have hg := h ⟨single_X_pow_mem_homForm ht p (j + 1),
    LinearMap.mem_ker.2 (extDeriv_single_X_pow_of_mem hp _)⟩
  have hτ := hV idMatrix (Pi.single p 1 : Fin n → ℝ) _ hg
  have hμ := hV.isLinearInvariant.homComp_mem hτ
    (isDeg_polyPullback (single_X_pow_mem_homForm ht p (j + 1)).1 _ _) j
  rw [homComp_translate_single_X_pow] at hμ
  have hν := V.smul_mem (((j + 1 : ℕ) : ℝ))⁻¹ hμ
  rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)), one_smul] at hν
  exact hV.isLinearInvariant.closed_le hν (single_X_pow_mem_homForm ht p j)
    (koszul_ne_zero_of_extDeriv_eq_zero (by omega) (single_X_pow_mem_homForm ht p j)
      (extDeriv_single_X_pow_of_mem hp j) (single_X_pow_ne_zero t p j))

/-- **[AFW2006], Lemma 3.7 (2)**, in the form used in the proof of Theorem 3.6: the `κ`-closed forms
of degree `j + 2` bring those of degree `j + 1` (`k < n`): for `ω = κ(x_p^{j+1} dx_t)` (`p ∈ t`,
`#t = k + 1`) the degree-`(j+1)` part `μ` of the translate by `e_p` has
`dμ = (j + k + 2)(j + 1) x_p^j dx_t ≠ 0`. -/
theorem IsAffineInvariant.koszulClosed_le_of_succ {V : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hV : IsAffineInvariant V) {j k : ℕ} (hkn : k + 1 ≤ n)
    (h : homForm ℝ (Fin n) (j + 2) k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n)) ≤ V) :
    homForm ℝ (Fin n) (j + 1) k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n)) ≤ V := by
  obtain ⟨t, ht, p, hp⟩ := exists_card_eq_mem (by omega) hkn
  set η : PolyForm ℝ (Fin n) := Pi.single t (X p ^ (j + 1))
  have hηH : η ∈ homForm ℝ (Fin n) (j + 1) (k + 1) := single_X_pow_mem_homForm ht p (j + 1)
  have hηd : Koszul.extDeriv η = 0 := extDeriv_single_X_pow_of_mem hp _
  have hωH : Koszul.koszul η ∈ homForm ℝ (Fin n) (j + 2) k := by
    simpa using Koszul.koszul_mem_homForm hηH
  have hω := h ⟨hωH, LinearMap.mem_ker.2 (Koszul.koszul_koszul η)⟩
  have hτ := hV idMatrix (Pi.single p 1 : Fin n → ℝ) _ hω
  have hdeg := isDeg_polyPullback hωH.1 idMatrix (Pi.single p 1 : Fin n → ℝ)
  have hμ := hV.isLinearInvariant.homComp_mem hτ hdeg (j + 1)
  refine hV.isLinearInvariant.koszulClosed_le_of_extDeriv_ne_zero hμ
    (Koszul.homComp_mem_homForm hdeg _) ?_
  rw [← Koszul.homComp_extDeriv, ← polyPullback_extDeriv, extDeriv_koszul_of_extDeriv_eq_zero hηH hηd,
    polyPullback_smul, homComp_smul, homComp_translate_single_X_pow, smul_smul]
  exact smul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 (by omega))
    (Nat.cast_ne_zero.2 (by omega))) (single_X_pow_ne_zero t p j)

/-- **[AFW2006], Lemma 3.7 (3)**, in the form used in the proof of Theorem 3.6: the `κ`-closed forms
of degree `j + 1` bring the closed forms of degree `j` (`1 ≤ k < n`): for `ω = κ(x_q^j dx_t)`
(`p ≠ q` in `t`, `#t = k + 1`) the translate by `e_p` is
`ω + ι_{e_p}(x_q^j dx_t) = ω ± x_q^j dx_{t ∖ p}`, whose degree-`j` part is closed, nonzero, hence
not `κ`-closed. -/
theorem IsAffineInvariant.closed_le_of_koszulClosed_le {V : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hV : IsAffineInvariant V) {j k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (h : homForm ℝ (Fin n) (j + 1) k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n)) ≤ V) :
    homForm ℝ (Fin n) j k ⊓ LinearMap.ker (extDerivₗ ℝ (Fin n)) ≤ V := by
  obtain ⟨t, ht, -⟩ := exists_card_eq_mem (by omega) hkn
  obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.1 (show 1 < #t by omega)
  set η : PolyForm ℝ (Fin n) := Pi.single t (X q ^ j)
  have hηH : η ∈ homForm ℝ (Fin n) j (k + 1) := single_X_pow_mem_homForm ht q j
  have hωH : Koszul.koszul η ∈ homForm ℝ (Fin n) (j + 1) k := by
    simpa using Koszul.koszul_mem_homForm hηH
  have hω := h ⟨hωH, LinearMap.mem_ker.2 (Koszul.koszul_koszul η)⟩
  have hτ := hV idMatrix (Pi.single p 1 : Fin n → ℝ) _ hω
  have hμ := hV.isLinearInvariant.homComp_mem hτ
    (isDeg_polyPullback hωH.1 idMatrix (Pi.single p 1 : Fin n → ℝ)) j
  have hτη : polyPullback idMatrix (Pi.single p 1 : Fin n → ℝ) η = η := by
    rw [translate_single_X_pow, Pi.single_apply, ite_eq_right (Ne.symm hpq), C_0, add_zero]
  set u := t.erase p
  have hqu : q ∈ u := mem_erase.2 ⟨Ne.symm hpq, hq⟩
  have hu : #u = k := by rw [card_erase_of_mem hp, ht, Nat.add_sub_cancel]
  have hι : interior (fun l => C ((Pi.single p 1 : Fin n → ℝ) l)) η =
      (sgn p u : ℝ) • (Pi.single u (X q ^ j) : PolyForm ℝ (Fin n)) := by
    rw [interior_single_single hp, ← Pi.single_smul', smul_eq_C_mul]
  have hτι : polyPullback idMatrix (Pi.single p 1 : Fin n → ℝ)
      (interior (fun l => C ((Pi.single p 1 : Fin n → ℝ) l)) η) =
        interior (fun l => C ((Pi.single p 1 : Fin n → ℝ) l)) η := by
    rw [hι, polyPullback_smul, translate_single_X_pow, Pi.single_apply, ite_eq_right (Ne.symm hpq), C_0,
      add_zero]
  rw [polyPullback_koszul, hτη, hτι, Koszul.homComp_add,
    Koszul.homComp_of_mem_homForm hωH, ite_eq_right (Nat.succ_ne_self j).symm, zero_add, hι,
    homComp_smul, Koszul.homComp_of_mem_homForm (single_X_pow_mem_homForm hu q j), ite_eq_left rfl]
    at hμ
  have hν := V.smul_mem (sgn p u : ℝ)⁻¹ hμ
  rw [smul_smul, inv_mul_cancel₀ (by rw [sgn]; exact pow_ne_zero _ (by norm_num)), one_smul] at hν
  exact hV.isLinearInvariant.closed_le hν (single_X_pow_mem_homForm hu q j)
    (koszul_ne_zero_of_extDeriv_eq_zero (by omega) (single_X_pow_mem_homForm hu q j)
      (extDeriv_single_X_pow_of_mem hqu j) (single_X_pow_ne_zero u q j))

/-! ### The affinely invariant spaces `X(r, s, k, n)` ([AFW2006], Theorem 3.5) -/

/-- **`dP_{r+1}Λ^{k-1}` is affinely invariant** ([AFW2006], (3.18)): `φ^* d = d φ^*` and
`φ^* P_{r+1}Λ^{k-1} ⊆ P_{r+1}Λ^{k-1}`. -/
theorem isAffineInvariant_map_extDeriv (r k : ℕ) :
    IsAffineInvariant ((polyForm ℝ (Fin n) r k).map (extDerivₗ ℝ (Fin n))) := by
  rintro B b _ ⟨η, hη, rfl⟩
  exact ⟨_, polyPullback_mem_polyForm B b hη, (polyPullback_extDeriv B b η).symm⟩

/-- `P_sΛᵏ ⊆ dP_{s+1}Λ^{k-1} + κP_sΛ^{k+1}` for `k ≥ 1` ((3.11), and `P_0Λᵏ = dP_1Λ^{k-1}`). -/
theorem polyForm_le_sup {s k : ℕ} (hk : 1 ≤ k) :
    polyForm ℝ (Fin n) s k ≤ (polyForm ℝ (Fin n) (s + 1) (k - 1)).map (extDerivₗ ℝ (Fin n)) ⊔
      (polyForm ℝ (Fin n) s (k + 1)).map (koszulₗ ℝ (Fin n)) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  obtain _ | s := s
  · rw [Koszul.polyForm_zero_eq_homForm, ← Koszul.map_extDeriv_homForm_one]
    exact le_sup_of_le_left (Submodule.map_mono (Koszul.homForm_le_polyForm _ _))
  · rw [← Koszul.map_koszul_polyForm_sup_map_extDeriv s k, sup_comm]
    exact sup_le_sup_left (Submodule.map_mono (Koszul.polyForm_mono (Nat.le_succ s) _)) _

/-- **[AFW2006], Theorem 3.5**: for `1 ≤ k` and `s ≤ r`, the space
`X(r, s, k, n) = dP_{r+1}Λ^{k-1} + κP_sΛ^{k+1}` is affinely invariant: by (3.18) and
`φ^* κ ω - κ φ^* ω = φ^* ι_b ω ∈ P_sΛᵏ ⊆ dP_{s+1}Λ^{k-1} + κP_sΛ^{k+1}` ((3.19), (3.11)). -/
theorem isAffineInvariant_sup {r s k : ℕ} (hk : 1 ≤ k) (hs : s ≤ r) :
    IsAffineInvariant ((polyForm ℝ (Fin n) (r + 1) (k - 1)).map (extDerivₗ ℝ (Fin n)) ⊔
      (polyForm ℝ (Fin n) s (k + 1)).map (koszulₗ ℝ (Fin n))) := by
  intro B b ω hω
  obtain ⟨_, ⟨η, hη, rfl⟩, _, ⟨ζ, hζ, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hω
  rw [polyPullback_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left
    ⟨_, polyPullback_mem_polyForm B b hη, (polyPullback_extDeriv B b η).symm⟩) ?_
  change polyPullback B b (Koszul.koszul ζ) ∈ _
  rw [polyPullback_koszul]
  refine Submodule.add_mem _ (Submodule.mem_sup_right
    ⟨_, polyPullback_mem_polyForm B b hζ, rfl⟩) ?_
  have h1 := polyPullback_mem_polyForm B b (Koszul.interior_C_mem_polyForm b hζ)
  have h2 := polyForm_le_sup hk h1
  have h3 : (polyForm ℝ (Fin n) (s + 1) (k - 1)).map (extDerivₗ ℝ (Fin n)) ⊔
      (polyForm ℝ (Fin n) s (k + 1)).map (koszulₗ ℝ (Fin n)) ≤
      (polyForm ℝ (Fin n) (r + 1) (k - 1)).map (extDerivₗ ℝ (Fin n)) ⊔
      (polyForm ℝ (Fin n) s (k + 1)).map (koszulₗ ℝ (Fin n)) :=
    sup_le_sup_right (Submodule.map_mono (Koszul.polyForm_mono (by omega) _)) _
  exact h3 h2

theorem map_extDeriv_polyForm_le {r k : ℕ} (hk : 1 ≤ k) :
    (polyForm ℝ (Fin n) (r + 1) (k - 1)).map (extDerivₗ ℝ (Fin n)) ≤ polyForm ℝ (Fin n) r k := by
  rintro _ ⟨η, hη, rfl⟩
  have := Koszul.extDeriv_mem_polyForm hη
  rwa [Nat.add_sub_cancel, Nat.sub_add_cancel hk] at this

/-- **[AFW2006], Theorem 3.5, case `s = r`**: `X(r, r, k, n) = P_{r+1}⁻Λᵏ`. -/
theorem sup_eq_polyFormMinus {r k : ℕ} (hk : 1 ≤ k) :
    (polyForm ℝ (Fin n) (r + 1) (k - 1)).map (extDerivₗ ℝ (Fin n)) ⊔
      (polyForm ℝ (Fin n) r (k + 1)).map (koszulₗ ℝ (Fin n)) = polyFormMinus ℝ (Fin n) (r + 1) k := by
  rw [Koszul.polyFormMinus_succ_eq_sup_map_koszul_polyForm]
  exact le_antisymm (sup_le_sup_right (map_extDeriv_polyForm_le hk) _)
    (sup_le (polyForm_le_sup hk) le_sup_right)

/-- **[AFW2006], Theorem 3.5, case `s = r - 1`**: `X(r, r - 1, k, n) = P_rΛᵏ` (`r ≥ 1`; for
`r = 0`, `s = -1`: `dP_1Λ^{k-1} = P_0Λᵏ`). -/
theorem sup_eq_polyForm {r k : ℕ} (hk : 1 ≤ k) :
    (polyForm ℝ (Fin n) (r + 2) (k - 1)).map (extDerivₗ ℝ (Fin n)) ⊔
      (polyForm ℝ (Fin n) r (k + 1)).map (koszulₗ ℝ (Fin n)) = polyForm ℝ (Fin n) (r + 1) k := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, sup_comm]
  exact Koszul.map_koszul_polyForm_sup_map_extDeriv r k

theorem map_extDeriv_polyForm_one_eq {k : ℕ} (hk : 1 ≤ k) :
    (polyForm ℝ (Fin n) 1 (k - 1)).map (extDerivₗ ℝ (Fin n)) = polyForm ℝ (Fin n) 0 k := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Koszul.polyForm_zero_eq_homForm, ← Koszul.map_extDeriv_homForm_one]
  refine le_antisymm (fun _ ⟨η, hη, he⟩ => ?_) (Submodule.map_mono (Koszul.homForm_le_polyForm _ _))
  rw [← he, ← Koszul.sum_homComp hη, map_sum, Finset.sum_range_succ, Finset.sum_range_one]
  refine Submodule.add_mem _ ?_ ⟨_, Koszul.homComp_mem_homForm hη.1 1, rfl⟩
  rw [show extDerivₗ ℝ (Fin n) (homComp 0 η) = 0 from extDeriv_eq_zero_of_mem_polyForm_zero
    (Koszul.homForm_le_polyForm _ _ (Koszul.homComp_mem_homForm hη.1 0))]
  exact Submodule.zero_mem _

/-! ### The classification ([AFW2006], Theorem 3.6) -/

/-- A finite-dimensional space of polynomial `k`-forms lies in some `P_NΛᵏ`. -/
theorem exists_le_polyForm {V : Submodule ℝ (PolyForm ℝ (Fin n))} [FiniteDimensional ℝ V]
    {k : ℕ} (hdeg : ∀ ω ∈ V, IsDeg k ω) : ∃ N, V ≤ polyForm ℝ (Fin n) N k := by
  obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional V).2 inferInstance
  refine ⟨S.sup fun ω => univ.sup fun t => (ω t).totalDegree, ?_⟩
  rw [← hS, Submodule.span_le]
  intro ω hω
  have hωV : ω ∈ V := hS ▸ Submodule.subset_span hω
  exact ⟨hdeg ω hωV, fun t => le_trans (le_sup (f := fun t => (ω t).totalDegree) (mem_univ t))
    (le_sup (f := fun ω => univ.sup fun t => (ω t).totalDegree) hω)⟩

/-- The closed forms of `H_jΛᵏ` (`k ≥ 1`) lie in `dP_{a+1}Λ^{k-1}` for `j ≤ a`. -/
theorem closed_le_map_extDeriv {j a k : ℕ} (hk : 1 ≤ k) (hja : j ≤ a) :
    homForm ℝ (Fin n) j k ⊓ LinearMap.ker (extDerivₗ ℝ (Fin n)) ≤
      (polyForm ℝ (Fin n) (a + 1) (k - 1)).map (extDerivₗ ℝ (Fin n)) := by
  rintro ξ ⟨hξ, hdξ⟩
  obtain ⟨η, hη, rfl⟩ := Koszul.exists_extDeriv_eq_of_extDeriv_eq_zero (by omega) hξ hdξ
  exact ⟨η, Koszul.polyForm_mono (by omega) _ (Koszul.homForm_le_polyForm _ _ hη), rfl⟩

/-- The `κ`-closed forms of `H_{i+1}Λᵏ` lie in `κP_bΛ^{k+1}` for `i ≤ b`. -/
theorem koszulClosed_le_map_koszul {i b k : ℕ} (hib : i ≤ b) :
    homForm ℝ (Fin n) (i + 1) k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n)) ≤
      (polyForm ℝ (Fin n) b (k + 1)).map (koszulₗ ℝ (Fin n)) := by
  rintro ξ ⟨hξ, hκξ⟩
  obtain ⟨η, hη, rfl⟩ := Koszul.exists_koszul_eq_of_koszul_eq_zero (by omega) hξ hκξ
  rw [Nat.add_sub_cancel] at hη
  exact ⟨η, Koszul.polyForm_mono hib _ (Koszul.homForm_le_polyForm _ _ hη), rfl⟩

theorem koszulClosed_zero_eq_bot {k : ℕ} (hk : 1 ≤ k) :
    homForm ℝ (Fin n) 0 k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n)) = ⊥ := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact eq_bot_iff.2 fun ξ ⟨hξ, hκξ⟩ => (Submodule.mem_bot ℝ).2
    (Koszul.eq_zero_of_mem_homForm_zero_of_koszul_eq_zero hξ hκξ)

/-- **A linearly invariant space of `k`-forms of bounded degree is the sum of the summands
`dH_{j+1}Λ^{k-1}`, `κH_{j-1}Λ^{k+1}` it contains**: it lies in every `T` containing them, as each
homogeneous component of its elements splits into the two summands (`homForm_split`) and a
nonzero part reaches its whole summand (`IsLinearInvariant.closed_le`,
`IsLinearInvariant.koszulClosed_le_of_extDeriv_ne_zero`). -/
theorem IsLinearInvariant.le_of_summands {V T : Submodule ℝ (PolyForm ℝ (Fin n))}
    (hV : IsLinearInvariant V) {k N : ℕ} (hk : 1 ≤ k) (hN : V ≤ polyForm ℝ (Fin n) N k)
    (hD : ∀ j, homForm ℝ (Fin n) j k ⊓ LinearMap.ker (extDerivₗ ℝ (Fin n)) ≤ V →
      homForm ℝ (Fin n) j k ⊓ LinearMap.ker (extDerivₗ ℝ (Fin n)) ≤ T)
    (hK : ∀ j, homForm ℝ (Fin n) j k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n)) ≤ V →
      homForm ℝ (Fin n) j k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n)) ≤ T) : V ≤ T := by
  intro ω hω
  rw [← Koszul.sum_homComp (hN hω)]
  refine T.sum_mem fun j _ => ?_
  have hξ := hV.homComp_mem hω (hN hω).1 j
  have hξH := Koszul.homComp_mem_homForm (hN hω).1 j
  obtain ⟨h1, h2, h3⟩ := homForm_split (by omega) hξH
  rw [h3]
  refine T.add_mem ?_ ?_
  · by_cases hd : Koszul.extDeriv (homComp j ω) = 0
    · rw [hd, Koszul.koszul_zero, smul_zero]; exact T.zero_mem
    · exact hK j (hV.koszulClosed_le_of_extDeriv_ne_zero hξ hξH hd) h1
  · by_cases hκ : Koszul.koszul (homComp j ω) = 0
    · rw [hκ, Koszul.extDeriv_zero, smul_zero]; exact T.zero_mem
    · exact hD j (hV.closed_le hξ hξH hκ) h2

/-- **[AFW2006], Theorem 3.6: the affinely invariant spaces of polynomial `k`-forms.** For
`0 < k < n`, a nonzero finite-dimensional space `V` of polynomial `k`-forms on `ℝⁿ` with
`φ^* V ⊆ V` for every affine map `φ : ℝⁿ → ℝⁿ` is one of the spaces `X(r, s, k, n)` of
`isAffineInvariant_sup`: `V = dP_{r+1}Λ^{k-1}` (`s = -1`) or
`V = dP_{r+1}Λ^{k-1} + κP_sΛ^{k+1}` with `0 ≤ s ≤ r`. Proof of [AFW2006] with the
representation theory of `GL(n)` replaced by `IsLinearInvariant.eq_of_le_homForm` (elementary:
pullbacks and multi-weight parts): `V` is the sum of the summands `dH_{j+1}Λ^{k-1}` and
`κH_{j-1}Λ^{k+1}` it contains (`IsLinearInvariant.le_of_summands`), and by the translation
lemmas (Lemma 3.7) those summands form initial segments, the `κ`-segment ending at most one
degree above the `d`-segment. -/
theorem IsAffineInvariant.eq_sup {V : Submodule ℝ (PolyForm ℝ (Fin n))} (hV : IsAffineInvariant V)
    [FiniteDimensional ℝ V] {k : ℕ} (hdeg : ∀ ω ∈ V, IsDeg k ω) (hk : 0 < k) (hkn : k < n)
    (hne : V ≠ ⊥) :
    ∃ r, V = (polyForm ℝ (Fin n) (r + 1) (k - 1)).map (extDerivₗ ℝ (Fin n)) ∨
      ∃ s ≤ r, V = (polyForm ℝ (Fin n) (r + 1) (k - 1)).map (extDerivₗ ℝ (Fin n)) ⊔
        (polyForm ℝ (Fin n) s (k + 1)).map (koszulₗ ℝ (Fin n)) := by
  classical
  have hL := hV.isLinearInvariant
  obtain ⟨N, hN⟩ := exists_le_polyForm hdeg
  set D : ℕ → Submodule ℝ (PolyForm ℝ (Fin n)) :=
    fun j => homForm ℝ (Fin n) j k ⊓ LinearMap.ker (extDerivₗ ℝ (Fin n))
  set K : ℕ → Submodule ℝ (PolyForm ℝ (Fin n)) :=
    fun j => homForm ℝ (Fin n) j k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n))
  -- the summands in `V` have degree `≤ N`
  have hDN : ∀ j, D j ≤ V → j ≤ N := by
    intro j hj
    by_contra hlt
    obtain ⟨t, ht, p, hp⟩ := exists_card_eq_mem hk hkn.le
    have hmem := hN (hj ⟨single_X_pow_mem_homForm ht p j,
      LinearMap.mem_ker.2 (extDeriv_single_X_pow_of_mem hp j)⟩)
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact single_X_pow_ne_zero t p _ (Koszul.eq_zero_of_mem_homForm_of_mem_polyForm
      (single_X_pow_mem_homForm ht p _) (Koszul.polyForm_mono (by omega) _ hmem))
  have hKN : ∀ i, K (i + 1) ≤ V → i ≤ N := by
    intro i hi
    by_contra hlt
    obtain ⟨t, ht, p, hp⟩ := exists_card_eq_mem (k := k + 1) (by omega) hkn
    have hηH := single_X_pow_mem_homForm ht p i
    have hωH : Koszul.koszul (Pi.single t (X p ^ i)) ∈ homForm ℝ (Fin n) (i + 1) k := by
      simpa using Koszul.koszul_mem_homForm hηH
    have hmem := hN (hi ⟨hωH, LinearMap.mem_ker.2 (Koszul.koszul_koszul _)⟩)
    exact koszul_ne_zero_of_extDeriv_eq_zero (by omega) hηH (extDeriv_single_X_pow_of_mem hp i)
      (single_X_pow_ne_zero t p i) (Koszul.eq_zero_of_mem_homForm_of_mem_polyForm hωH
        (Koszul.polyForm_mono (by omega) _ hmem))
  -- some closed summand lies in `V`
  have hDex : ∃ j, D j ≤ V := by
    obtain ⟨ω, hω, h0⟩ := (Submodule.ne_bot_iff V).1 hne
    have : ∃ j, homComp j ω ≠ 0 := by
      by_contra h
      push Not at h
      exact h0 (by rw [← Koszul.sum_homComp (hN hω)]; exact sum_eq_zero fun j _ => h j)
    obtain ⟨j, hj⟩ := this
    have hξ := hL.homComp_mem hω (hN hω).1 j
    have hξH := Koszul.homComp_mem_homForm (hN hω).1 j
    by_cases hκ : Koszul.koszul (homComp j ω) = 0
    · have hd := extDeriv_ne_zero_of_koszul_eq_zero (by omega) hξH hκ hj
      have hKj := hL.koszulClosed_le_of_extDeriv_ne_zero hξ hξH hd
      obtain _ | i := j
      · exact absurd (extDeriv_eq_zero_of_mem_polyForm_zero (Koszul.homForm_le_polyForm _ _ hξH))
          hd
      · exact ⟨i, hV.closed_le_of_koszulClosed_le hk hkn hKj⟩
    · exact ⟨j, hL.closed_le hξ hξH hκ⟩
  -- the closed summands in `V`: the degrees `≤ a`
  set a := Nat.findGreatest (fun j => D j ≤ V) N
  have hDa : ∀ j, D j ≤ V ↔ j ≤ a := by
    obtain ⟨j₀, hj₀⟩ := hDex
    have ha : D a ≤ V := Nat.findGreatest_spec (P := fun j => D j ≤ V) (hDN j₀ hj₀) hj₀
    exact fun j => ⟨fun hj => Nat.le_findGreatest (hDN j hj) hj,
      fun hj => Nat.decreasingInduction (motive := fun j _ => D j ≤ V)
        (fun _ _ hm => hV.closed_le_of_succ hk hkn.le hm) ha hj⟩
  have hdP : (polyForm ℝ (Fin n) (a + 1) (k - 1)).map (extDerivₗ ℝ (Fin n)) ≤ V := by
    rintro _ ⟨η, hη, rfl⟩
    change Koszul.extDeriv η ∈ V
    rw [← Koszul.sum_homComp hη]
    rw [show Koszul.extDeriv (∑ j ∈ range (a + 1 + 1), homComp j η) =
      ∑ j ∈ range (a + 1 + 1), Koszul.extDeriv (homComp j η) from map_sum (extDerivₗ ℝ (Fin n)) _ _]
    refine V.sum_mem fun j hj => ?_
    obtain _ | i := j
    · rw [extDeriv_eq_zero_of_mem_polyForm_zero (Koszul.homForm_le_polyForm _ _
        (Koszul.homComp_mem_homForm hη.1 0))]
      exact V.zero_mem
    · refine (hDa i).2 (by simp at hj; omega) ⟨?_, LinearMap.mem_ker.2 (Koszul.extDeriv_extDeriv _)⟩
      have := Koszul.extDeriv_mem_homForm (Koszul.homComp_mem_homForm hη.1 (i + 1))
      rwa [Nat.add_sub_cancel, Nat.sub_add_cancel hk] at this
  refine ⟨a, ?_⟩
  by_cases hKex : ∃ i, K (i + 1) ≤ V
  · -- the `κ`-closed summands in `V`: the degrees `1, …, s + 1`
    set b := Nat.findGreatest (fun i => K (i + 1) ≤ V) N
    have hKb : ∀ i, K (i + 1) ≤ V ↔ i ≤ b := by
      obtain ⟨i₀, hi₀⟩ := hKex
      have hb : K (b + 1) ≤ V :=
        Nat.findGreatest_spec (P := fun i => K (i + 1) ≤ V) (hKN i₀ hi₀) hi₀
      exact fun i => ⟨fun hi => Nat.le_findGreatest (hKN i hi) hi,
        fun hi => Nat.decreasingInduction (motive := fun i _ => K (i + 1) ≤ V)
          (fun _ _ hm => hV.koszulClosed_le_of_succ hkn hm) hb hi⟩
    have hba : b ≤ a :=
      (hDa b).1 (hV.closed_le_of_koszulClosed_le hk hkn ((hKb b).2 le_rfl))
    refine Or.inr ⟨b, hba, le_antisymm ?_ (sup_le hdP ?_)⟩
    · refine hL.le_of_summands hk hN (fun j hj => le_sup_of_le_left
        (closed_le_map_extDeriv hk ((hDa j).1 hj))) fun j hj => ?_
      obtain _ | i := j
      · rw [koszulClosed_zero_eq_bot hk]; exact bot_le
      · exact le_sup_of_le_right (koszulClosed_le_map_koszul ((hKb i).1 hj))
    · rintro _ ⟨η, hη, rfl⟩
      change Koszul.koszul η ∈ V
      rw [← Koszul.sum_homComp hη]
      rw [show Koszul.koszul (∑ j ∈ range (b + 1), homComp j η) =
        ∑ j ∈ range (b + 1), Koszul.koszul (homComp j η) from map_sum (koszulₗ ℝ (Fin n)) _ _]
      refine V.sum_mem fun i hi => (hKb i).2 (by simp at hi; omega)
        ⟨?_, LinearMap.mem_ker.2 (Koszul.koszul_koszul _)⟩
      simpa using Koszul.koszul_mem_homForm (Koszul.homComp_mem_homForm hη.1 i)
  · push Not at hKex
    refine Or.inl (le_antisymm ?_ hdP)
    refine hL.le_of_summands hk hN (fun j hj => closed_le_map_extDeriv hk ((hDa j).1 hj))
      fun j hj => ?_
    obtain _ | i := j
    · rw [koszulClosed_zero_eq_bot hk]; exact bot_le
    · exact absurd hj (hKex i)

end Feec.FiniteElement
