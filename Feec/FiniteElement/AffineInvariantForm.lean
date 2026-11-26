module

public import Feec.FiniteElement.InvariantForm

/-!
# The affinely invariant spaces of polynomial differential forms

For `0 < k < n` in characteristic `0`, every nonzero finite-dimensional affinely invariant space of
polynomial `k`-forms is one of the spaces `X(r, s, k, n)`, `-1 ≤ s ≤ r` (`κP_{-1} = 0`)
([AFW2006], Thms 3.5–3.6).

## Main results

* `isAffineInvariant_sup`: `X(r, s, k, n) = dP_{r+1}Λ^{k-1} + κP_sΛ^{k+1}` is affinely invariant.
* `sup_eq_polyFormMinus`, `sup_eq_polyForm`: `P_{r+1}⁻Λᵏ` and `P_{r+1}Λᵏ` are such spaces.
* `IsAffineInvariant.eq_sup`: the classification of the affinely invariant spaces.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006], §3.4

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre
open Koszul (PolyForm homForm polyForm polyFormMinus homComp koszulₗ extDerivₗ)

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-! ### Monomial forms `x_p^j dx_t` -/

/-- The identity matrix, as the coefficient function taken by `polyPullback`. -/
def idMatrix : Fin n → Fin n → K := fun i l => if i = l then 1 else 0

omit [CharZero K] in
theorem single_X_pow_mem_homForm {t : Finset (Fin n)} {k : ℕ} (ht : #t = k) (p : Fin n)
    (j : ℕ) : (Pi.single t (X p ^ j) : PolyForm K (Fin n)) ∈ homForm K (Fin n) j k := by
  refine ⟨fun s hs => ?_, fun s => ?_⟩
  · have : s ≠ t := fun h => hs (h ▸ ht)
    simp [this]
  · by_cases h : s = t
    · subst h; simpa using isHomogeneous_X_pow p j
    · simpa [h] using isHomogeneous_zero (Fin n) K j

omit [CharZero K] in
theorem single_X_pow_ne_zero (t : Finset (Fin n)) (p : Fin n) (j : ℕ) :
    (Pi.single t (X p ^ j) : PolyForm K (Fin n)) ≠ 0 := fun h => by
  have := congrFun h t
  simp at this

theorem extDeriv_single_X_pow_of_mem {t : Finset (Fin n)} {p : Fin n} (hp : p ∈ t) (j : ℕ) :
    Koszul.extDeriv (Pi.single t (X p ^ j) : PolyForm K (Fin n)) = 0 := by
  have h := extDeriv_single_X_pow (K := K) (notMem_erase p t) j
  rw [insert_erase hp] at h
  have hc : (((j + 1 : ℕ) : K) * sgn p (t.erase p)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero j))
      (by rw [sgn]; exact pow_ne_zero _ (by norm_num))
  have : (Pi.single t (X p ^ j) : PolyForm K (Fin n)) =
      (((j + 1 : ℕ) : K) * sgn p (t.erase p))⁻¹ •
        Koszul.extDeriv (Pi.single (t.erase p) (X p ^ (j + 1))) := by
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [this, Koszul.extDeriv_smul, Koszul.extDeriv_extDeriv, smul_zero]

theorem koszul_ne_zero_of_extDeriv_eq_zero {r k : ℕ} (hrk : 0 < r + k) {ω : PolyForm K (Fin n)}
    (h : ω ∈ homForm K (Fin n) r k) (hd : Koszul.extDeriv ω = 0) (h0 : ω ≠ 0) :
    Koszul.koszul ω ≠ 0 := fun hκ => h0 <| by
  have := extDeriv_koszul_of_extDeriv_eq_zero h hd
  rw [hκ, Koszul.extDeriv_zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hrk.ne')

theorem extDeriv_ne_zero_of_koszul_eq_zero {r k : ℕ} (hrk : 0 < r + k) {ω : PolyForm K (Fin n)}
    (h : ω ∈ homForm K (Fin n) r k) (hκ : Koszul.koszul ω = 0) (h0 : ω ≠ 0) :
    Koszul.extDeriv ω ≠ 0 := fun hd => h0 <| by
  have := koszul_extDeriv_of_koszul_eq_zero h hκ
  rw [hd, Koszul.koszul_zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hrk.ne')

/-! ### Translations -/

omit [CharZero K] in
theorem polyPullback_idMatrix_single (b : Fin n → K) (t : Finset (Fin n))
    (q : MvPolynomial (Fin n) K) :
    polyPullback idMatrix b (Pi.single t q) =
      Pi.single t (polySubst idMatrix b q) := by
  funext s
  rw [polyPullback_single, wedgeProd_id_cols (B := idMatrix) (s := s) (fun i l _ => rfl)]
  by_cases h : t = s
  · subst h; simp
  · simp [h, Ne.symm h]

omit [CharZero K] in
theorem polySubst_idMatrix_X (b : Fin n → K) (q : Fin n) :
    polySubst idMatrix b (X q) = X q + C (b q) := by
  simp [polySubst, idMatrix]

omit [CharZero K] in
theorem homogeneousComponent_X_add_C_pow (p : Fin n) (c : K) {j m : ℕ} (hj : j ≤ m) :
    homogeneousComponent j ((X p + C c) ^ m : MvPolynomial (Fin n) K) =
      C (c ^ (m - j) * (m.choose j : K)) * X p ^ j := by
  have hterm : ∀ i, (X p ^ i * C c ^ (m - i) * (m.choose i : MvPolynomial (Fin n) K)) =
      C (c ^ (m - i) * (m.choose i : K)) * X p ^ i := fun i => by
    rw [map_mul, map_pow, map_natCast]; ring
  have hX : ∀ i, homogeneousComponent j (X p ^ i : MvPolynomial (Fin n) K) =
      if i = j then X p ^ i else 0 := fun i => by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X_pow p i))]
    simp only [eq_comm]
  simp_rw [add_pow, map_sum, hterm, homogeneousComponent_C_mul, hX, mul_ite, mul_zero]
  rw [sum_ite_eq' (range (m + 1)), ite_eq_left (mem_range.2 (by omega))]

omit [CharZero K] in
theorem homComp_single (j : ℕ) (t : Finset (Fin n)) (q : MvPolynomial (Fin n) K) :
    homComp j (Pi.single t q : PolyForm K (Fin n)) = Pi.single t (homogeneousComponent j q) := by
  funext s
  rw [Koszul.homComp_apply]
  by_cases h : s = t
  · subst h; simp
  · simp [h]

omit [CharZero K] in
theorem homComp_smul (j : ℕ) (c : K) (ω : PolyForm K (Fin n)) :
    homComp j (c • ω) = c • homComp j ω := by
  funext s; simp [Koszul.homComp_apply]

omit [CharZero K] in
theorem translate_single_X_pow (p : Fin n) (c : K) (t : Finset (Fin n)) (q : Fin n) (m : ℕ) :
    polyPullback idMatrix (Pi.single p c : Fin n → K) (Pi.single t (X q ^ m)) =
      Pi.single t ((X q + C ((Pi.single p c : Fin n → K) q)) ^ m) := by
  rw [polyPullback_idMatrix_single, map_pow, polySubst_idMatrix_X]

omit [CharZero K] in
theorem homComp_translate_single_X_pow (p : Fin n) (t : Finset (Fin n)) (j : ℕ) :
    homComp j (polyPullback idMatrix (Pi.single p 1 : Fin n → K)
        (Pi.single t (X p ^ (j + 1)))) =
      ((j + 1 : ℕ) : K) • (Pi.single t (X p ^ j) : PolyForm K (Fin n)) := by
  rw [translate_single_X_pow, homComp_single, Pi.single_eq_same,
    homogeneousComponent_X_add_C_pow _ _ (Nat.le_succ j), ← Pi.single_smul', smul_eq_C_mul]
  simp [Nat.choose_succ_self_right]

omit [CharZero K] in
theorem interior_single_single {p : Fin n} {t : Finset (Fin n)} (hp : p ∈ t)
    (f : MvPolynomial (Fin n) K) :
    interior (fun l => C ((Pi.single p 1 : Fin n → K) l)) (Pi.single t f : PolyForm K (Fin n)) =
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
      simp [show (sgn p (t.erase p) : MvPolynomial (Fin n) K) = C (sgn p (t.erase p)) by
        simp [sgn]]
    · have : insert p s ≠ t := fun h => hs (by rw [← h, erase_insert hps])
      simp [hs, this]

theorem exists_card_eq_mem {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ t : Finset (Fin n), #t = k ∧ t.Nonempty := by
  obtain ⟨t, -, ht⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := k)
    (by simpa using hkn)
  exact ⟨t, ht, card_pos.1 (by omega)⟩

/-! ### The translation lemmas ([AFW2006], Lemma 3.7) -/

theorem IsAffineInvariant.closed_le_of_succ {V : Submodule K (PolyForm K (Fin n))}
    (hV : IsAffineInvariant V) {j k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (h : homForm K (Fin n) (j + 1) k ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ≤ V) :
    homForm K (Fin n) j k ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ≤ V := by
  obtain ⟨t, ht, p, hp⟩ := exists_card_eq_mem hk hkn
  have hg := h ⟨single_X_pow_mem_homForm ht p (j + 1),
    LinearMap.mem_ker.2 (extDeriv_single_X_pow_of_mem hp _)⟩
  have hτ := hV idMatrix (Pi.single p 1 : Fin n → K) _ hg
  have hμ := hV.isLinearInvariant.homComp_mem hτ
    (isDeg_polyPullback (single_X_pow_mem_homForm ht p (j + 1)).1 _ _) j
  rw [homComp_translate_single_X_pow] at hμ
  have hν := V.smul_mem (((j + 1 : ℕ) : K))⁻¹ hμ
  rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)), one_smul] at hν
  exact hV.isLinearInvariant.closed_le hν (single_X_pow_mem_homForm ht p j)
    (koszul_ne_zero_of_extDeriv_eq_zero (by omega) (single_X_pow_mem_homForm ht p j)
      (extDeriv_single_X_pow_of_mem hp j) (single_X_pow_ne_zero t p j))

theorem IsAffineInvariant.koszulClosed_le_of_succ {V : Submodule K (PolyForm K (Fin n))}
    (hV : IsAffineInvariant V) {j k : ℕ} (hkn : k + 1 ≤ n)
    (h : homForm K (Fin n) (j + 2) k ⊓ LinearMap.ker (koszulₗ K (Fin n)) ≤ V) :
    homForm K (Fin n) (j + 1) k ⊓ LinearMap.ker (koszulₗ K (Fin n)) ≤ V := by
  obtain ⟨t, ht, p, hp⟩ := exists_card_eq_mem (by omega) hkn
  set η : PolyForm K (Fin n) := Pi.single t (X p ^ (j + 1))
  have hηH : η ∈ homForm K (Fin n) (j + 1) (k + 1) := single_X_pow_mem_homForm ht p (j + 1)
  have hηd : Koszul.extDeriv η = 0 := extDeriv_single_X_pow_of_mem hp _
  have hωH : Koszul.koszul η ∈ homForm K (Fin n) (j + 2) k := by
    simpa using Koszul.koszul_mem_homForm hηH
  have hω := h ⟨hωH, LinearMap.mem_ker.2 (Koszul.koszul_koszul η)⟩
  have hτ := hV idMatrix (Pi.single p 1 : Fin n → K) _ hω
  have hdeg := isDeg_polyPullback hωH.1 idMatrix (Pi.single p 1 : Fin n → K)
  have hμ := hV.isLinearInvariant.homComp_mem hτ hdeg (j + 1)
  refine hV.isLinearInvariant.koszulClosed_le_of_extDeriv_ne_zero hμ
    (Koszul.homComp_mem_homForm hdeg _) ?_
  rw [← Koszul.homComp_extDeriv, ← polyPullback_extDeriv,
    extDeriv_koszul_of_extDeriv_eq_zero hηH hηd, polyPullback_smul, homComp_smul, homComp_translate_single_X_pow, smul_smul]
  exact smul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 (by omega))
    (Nat.cast_ne_zero.2 (by omega))) (single_X_pow_ne_zero t p j)

theorem IsAffineInvariant.closed_le_of_koszulClosed_le {V : Submodule K (PolyForm K (Fin n))}
    (hV : IsAffineInvariant V) {j k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (h : homForm K (Fin n) (j + 1) k ⊓ LinearMap.ker (koszulₗ K (Fin n)) ≤ V) :
    homForm K (Fin n) j k ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ≤ V := by
  obtain ⟨t, ht, -⟩ := exists_card_eq_mem (by omega) hkn
  obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.1 (show 1 < #t by omega)
  set η : PolyForm K (Fin n) := Pi.single t (X q ^ j)
  have hηH : η ∈ homForm K (Fin n) j (k + 1) := single_X_pow_mem_homForm ht q j
  have hωH : Koszul.koszul η ∈ homForm K (Fin n) (j + 1) k := by
    simpa using Koszul.koszul_mem_homForm hηH
  have hω := h ⟨hωH, LinearMap.mem_ker.2 (Koszul.koszul_koszul η)⟩
  have hτ := hV idMatrix (Pi.single p 1 : Fin n → K) _ hω
  have hμ := hV.isLinearInvariant.homComp_mem hτ
    (isDeg_polyPullback hωH.1 idMatrix (Pi.single p 1 : Fin n → K)) j
  have hτη : polyPullback idMatrix (Pi.single p 1 : Fin n → K) η = η := by
    rw [translate_single_X_pow, Pi.single_apply, ite_eq_right (Ne.symm hpq), C_0, add_zero]
  set u := t.erase p
  have hqu : q ∈ u := mem_erase.2 ⟨Ne.symm hpq, hq⟩
  have hu : #u = k := by rw [card_erase_of_mem hp, ht, Nat.add_sub_cancel]
  have hι : interior (fun l => C ((Pi.single p 1 : Fin n → K) l)) η =
      (sgn p u : K) • (Pi.single u (X q ^ j) : PolyForm K (Fin n)) := by
    rw [interior_single_single hp, ← Pi.single_smul', smul_eq_C_mul]
  have hτι : polyPullback idMatrix (Pi.single p 1 : Fin n → K)
      (interior (fun l => C ((Pi.single p 1 : Fin n → K) l)) η) =
        interior (fun l => C ((Pi.single p 1 : Fin n → K) l)) η := by
    rw [hι, polyPullback_smul, translate_single_X_pow, Pi.single_apply, ite_eq_right (Ne.symm hpq), C_0,
      add_zero]
  rw [polyPullback_koszul, hτη, hτι, Koszul.homComp_add,
    Koszul.homComp_of_mem_homForm hωH, ite_eq_right (Nat.succ_ne_self j).symm, zero_add, hι,
    homComp_smul, Koszul.homComp_of_mem_homForm (single_X_pow_mem_homForm hu q j), ite_eq_left rfl]
    at hμ
  have hν := V.smul_mem (sgn p u : K)⁻¹ hμ
  rw [smul_smul, inv_mul_cancel₀ (by rw [sgn]; exact pow_ne_zero _ (by norm_num)), one_smul] at hν
  exact hV.isLinearInvariant.closed_le hν (single_X_pow_mem_homForm hu q j)
    (koszul_ne_zero_of_extDeriv_eq_zero (by omega) (single_X_pow_mem_homForm hu q j)
      (extDeriv_single_X_pow_of_mem hqu j) (single_X_pow_ne_zero u q j))

/-! ### The affinely invariant spaces `X(r, s, k, n)` ([AFW2006], Theorem 3.5) -/

omit [CharZero K] in
/-- `dP_rΛᵏ` is affinely invariant; [AFW2006], (3.18). -/
theorem isAffineInvariant_map_extDeriv (r k : ℕ) :
    IsAffineInvariant ((polyForm K (Fin n) r k).map (extDerivₗ K (Fin n))) := by
  rintro B b _ ⟨η, hη, rfl⟩
  exact ⟨_, polyPullback_mem_polyForm B b hη, (polyPullback_extDeriv B b η).symm⟩

theorem polyForm_le_sup {s k : ℕ} (hk : 1 ≤ k) :
    polyForm K (Fin n) s k ≤ (polyForm K (Fin n) (s + 1) (k - 1)).map (extDerivₗ K (Fin n)) ⊔
      (polyForm K (Fin n) s (k + 1)).map (koszulₗ K (Fin n)) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  obtain _ | s := s
  · rw [Koszul.polyForm_zero_eq_homForm, ← Koszul.map_extDeriv_homForm_one]
    exact le_sup_of_le_left (Submodule.map_mono (Koszul.homForm_le_polyForm _ _))
  · rw [← Koszul.map_koszul_polyForm_sup_map_extDeriv s k, sup_comm]
    exact sup_le_sup_left (Submodule.map_mono (Koszul.polyForm_mono (Nat.le_succ s) _)) _

/-- `X(r, s, k, n)` is affinely invariant for `k ≥ 1`, `s ≤ r`; [AFW2006], Thm 3.5. -/
theorem isAffineInvariant_sup {r s k : ℕ} (hk : 1 ≤ k) (hs : s ≤ r) :
    IsAffineInvariant ((polyForm K (Fin n) (r + 1) (k - 1)).map (extDerivₗ K (Fin n)) ⊔
      (polyForm K (Fin n) s (k + 1)).map (koszulₗ K (Fin n))) := by
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
  have h3 : (polyForm K (Fin n) (s + 1) (k - 1)).map (extDerivₗ K (Fin n)) ⊔
      (polyForm K (Fin n) s (k + 1)).map (koszulₗ K (Fin n)) ≤
      (polyForm K (Fin n) (r + 1) (k - 1)).map (extDerivₗ K (Fin n)) ⊔
      (polyForm K (Fin n) s (k + 1)).map (koszulₗ K (Fin n)) :=
    sup_le_sup_right (Submodule.map_mono (Koszul.polyForm_mono (by omega) _)) _
  exact h3 h2

omit [CharZero K] in
theorem map_extDeriv_polyForm_le {r k : ℕ} (hk : 1 ≤ k) :
    (polyForm K (Fin n) (r + 1) (k - 1)).map (extDerivₗ K (Fin n)) ≤ polyForm K (Fin n) r k := by
  rintro _ ⟨η, hη, rfl⟩
  have := Koszul.extDeriv_mem_polyForm hη
  rwa [Nat.add_sub_cancel, Nat.sub_add_cancel hk] at this

/-- `X(r, r, k, n) = P_{r+1}⁻Λᵏ` for `k ≥ 1`; [AFW2006], Thm 3.5. -/
theorem sup_eq_polyFormMinus {r k : ℕ} (hk : 1 ≤ k) :
    (polyForm K (Fin n) (r + 1) (k - 1)).map (extDerivₗ K (Fin n)) ⊔
      (polyForm K (Fin n) r (k + 1)).map (koszulₗ K (Fin n)) = polyFormMinus K (Fin n) (r + 1) k := by
  rw [Koszul.polyFormMinus_succ_eq_sup_map_koszul_polyForm]
  exact le_antisymm (sup_le_sup_right (map_extDeriv_polyForm_le hk) _)
    (sup_le (polyForm_le_sup hk) le_sup_right)

/-- `X(r + 1, r, k, n) = P_{r+1}Λᵏ` for `k ≥ 1`; [AFW2006], Thm 3.5. -/
theorem sup_eq_polyForm {r k : ℕ} (hk : 1 ≤ k) :
    (polyForm K (Fin n) (r + 2) (k - 1)).map (extDerivₗ K (Fin n)) ⊔
      (polyForm K (Fin n) r (k + 1)).map (koszulₗ K (Fin n)) = polyForm K (Fin n) (r + 1) k := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, sup_comm]
  exact Koszul.map_koszul_polyForm_sup_map_extDeriv r k

theorem map_extDeriv_polyForm_one_eq {k : ℕ} (hk : 1 ≤ k) :
    (polyForm K (Fin n) 1 (k - 1)).map (extDerivₗ K (Fin n)) = polyForm K (Fin n) 0 k := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Koszul.polyForm_zero_eq_homForm, ← Koszul.map_extDeriv_homForm_one]
  refine le_antisymm (fun _ ⟨η, hη, he⟩ => ?_) (Submodule.map_mono (Koszul.homForm_le_polyForm _ _))
  rw [← he, ← Koszul.sum_homComp hη, map_sum, Finset.sum_range_succ, Finset.sum_range_one]
  refine Submodule.add_mem _ ?_ ⟨_, Koszul.homComp_mem_homForm hη.1 1, rfl⟩
  rw [show extDerivₗ K (Fin n) (homComp 0 η) = 0 from Koszul.extDeriv_eq_zero_of_mem_polyForm_zero
    (Koszul.homForm_le_polyForm _ _ (Koszul.homComp_mem_homForm hη.1 0))]
  exact Submodule.zero_mem _

/-! ### The classification ([AFW2006], Theorem 3.6) -/

omit [CharZero K] in
theorem exists_le_polyForm {V : Submodule K (PolyForm K (Fin n))} [FiniteDimensional K V]
    {k : ℕ} (hdeg : ∀ ω ∈ V, IsDeg k ω) : ∃ N, V ≤ polyForm K (Fin n) N k := by
  obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional V).2 inferInstance
  refine ⟨S.sup fun ω => univ.sup fun t => (ω t).totalDegree, ?_⟩
  rw [← hS, Submodule.span_le]
  intro ω hω
  have hωV : ω ∈ V := hS ▸ Submodule.subset_span hω
  exact ⟨hdeg ω hωV, fun t => le_trans (le_sup (f := fun t => (ω t).totalDegree) (mem_univ t))
    (le_sup (f := fun ω => univ.sup fun t => (ω t).totalDegree) hω)⟩

theorem closed_le_map_extDeriv {j a k : ℕ} (hk : 1 ≤ k) (hja : j ≤ a) :
    homForm K (Fin n) j k ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ≤
      (polyForm K (Fin n) (a + 1) (k - 1)).map (extDerivₗ K (Fin n)) := by
  rintro ξ ⟨hξ, hdξ⟩
  obtain ⟨η, hη, rfl⟩ := Koszul.exists_extDeriv_eq_of_extDeriv_eq_zero (by omega) hξ hdξ
  exact ⟨η, Koszul.polyForm_mono (by omega) _ (Koszul.homForm_le_polyForm _ _ hη), rfl⟩

theorem koszulClosed_le_map_koszul {i b k : ℕ} (hib : i ≤ b) :
    homForm K (Fin n) (i + 1) k ⊓ LinearMap.ker (koszulₗ K (Fin n)) ≤
      (polyForm K (Fin n) b (k + 1)).map (koszulₗ K (Fin n)) := by
  rintro ξ ⟨hξ, hκξ⟩
  obtain ⟨η, hη, rfl⟩ := Koszul.exists_koszul_eq_of_koszul_eq_zero (by omega) hξ hκξ
  rw [Nat.add_sub_cancel] at hη
  exact ⟨η, Koszul.polyForm_mono hib _ (Koszul.homForm_le_polyForm _ _ hη), rfl⟩

theorem koszulClosed_zero_eq_bot {k : ℕ} (hk : 1 ≤ k) :
    homForm K (Fin n) 0 k ⊓ LinearMap.ker (koszulₗ K (Fin n)) = ⊥ := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact eq_bot_iff.2 fun ξ ⟨hξ, hκξ⟩ => (Submodule.mem_bot K).2
    (Koszul.eq_zero_of_mem_homForm_zero_of_koszul_eq_zero hξ hκξ)

theorem IsLinearInvariant.le_of_summands {V T : Submodule K (PolyForm K (Fin n))}
    (hV : IsLinearInvariant V) {k N : ℕ} (hk : 1 ≤ k) (hN : V ≤ polyForm K (Fin n) N k)
    (hD : ∀ j, homForm K (Fin n) j k ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ≤ V →
      homForm K (Fin n) j k ⊓ LinearMap.ker (extDerivₗ K (Fin n)) ≤ T)
    (hK : ∀ j, homForm K (Fin n) j k ⊓ LinearMap.ker (koszulₗ K (Fin n)) ≤ V →
      homForm K (Fin n) j k ⊓ LinearMap.ker (koszulₗ K (Fin n)) ≤ T) : V ≤ T := by
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

/-- For `0 < k < n`, a nonzero finite-dimensional affinely invariant space of polynomial `k`-forms
is `dP_{r+1}Λ^{k-1}` or `dP_{r+1}Λ^{k-1} + κP_sΛ^{k+1}`, `s ≤ r`; [AFW2006], Thm 3.6. -/
theorem IsAffineInvariant.eq_sup {V : Submodule K (PolyForm K (Fin n))} (hV : IsAffineInvariant V)
    [FiniteDimensional K V] {k : ℕ} (hdeg : ∀ ω ∈ V, IsDeg k ω) (hk : 0 < k) (hkn : k < n)
    (hne : V ≠ ⊥) :
    ∃ r, V = (polyForm K (Fin n) (r + 1) (k - 1)).map (extDerivₗ K (Fin n)) ∨
      ∃ s ≤ r, V = (polyForm K (Fin n) (r + 1) (k - 1)).map (extDerivₗ K (Fin n)) ⊔
        (polyForm K (Fin n) s (k + 1)).map (koszulₗ K (Fin n)) := by
  classical
  have hL := hV.isLinearInvariant
  obtain ⟨N, hN⟩ := exists_le_polyForm hdeg
  set D : ℕ → Submodule K (PolyForm K (Fin n)) :=
    fun j => homForm K (Fin n) j k ⊓ LinearMap.ker (extDerivₗ K (Fin n))
  set Z : ℕ → Submodule K (PolyForm K (Fin n)) :=
    fun j => homForm K (Fin n) j k ⊓ LinearMap.ker (koszulₗ K (Fin n))
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
  have hKN : ∀ i, Z (i + 1) ≤ V → i ≤ N := by
    intro i hi
    by_contra hlt
    obtain ⟨t, ht, p, hp⟩ := exists_card_eq_mem (k := k + 1) (by omega) hkn
    have hηH := single_X_pow_mem_homForm (K := K) ht p i
    have hωH : Koszul.koszul (Pi.single t (X p ^ i)) ∈ homForm K (Fin n) (i + 1) k := by
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
      · exact absurd (Koszul.extDeriv_eq_zero_of_mem_polyForm_zero (Koszul.homForm_le_polyForm _ _ hξH))
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
  have hdP : (polyForm K (Fin n) (a + 1) (k - 1)).map (extDerivₗ K (Fin n)) ≤ V := by
    rintro _ ⟨η, hη, rfl⟩
    change Koszul.extDeriv η ∈ V
    rw [← Koszul.sum_homComp hη]
    rw [show Koszul.extDeriv (∑ j ∈ range (a + 1 + 1), homComp j η) =
      ∑ j ∈ range (a + 1 + 1), Koszul.extDeriv (homComp j η) from map_sum (extDerivₗ K (Fin n)) _ _]
    refine V.sum_mem fun j hj => ?_
    obtain _ | i := j
    · rw [Koszul.extDeriv_eq_zero_of_mem_polyForm_zero (Koszul.homForm_le_polyForm _ _
        (Koszul.homComp_mem_homForm hη.1 0))]
      exact V.zero_mem
    · refine (hDa i).2 (by simp at hj; omega) ⟨?_, LinearMap.mem_ker.2 (Koszul.extDeriv_extDeriv _)⟩
      have := Koszul.extDeriv_mem_homForm (Koszul.homComp_mem_homForm hη.1 (i + 1))
      rwa [Nat.add_sub_cancel, Nat.sub_add_cancel hk] at this
  refine ⟨a, ?_⟩
  by_cases hKex : ∃ i, Z (i + 1) ≤ V
  · -- the `κ`-closed summands in `V`: the degrees `1, …, s + 1`
    set b := Nat.findGreatest (fun i => Z (i + 1) ≤ V) N
    have hKb : ∀ i, Z (i + 1) ≤ V ↔ i ≤ b := by
      obtain ⟨i₀, hi₀⟩ := hKex
      have hb : Z (b + 1) ≤ V :=
        Nat.findGreatest_spec (P := fun i => Z (i + 1) ≤ V) (hKN i₀ hi₀) hi₀
      exact fun i => ⟨fun hi => Nat.le_findGreatest (hKN i hi) hi,
        fun hi => Nat.decreasingInduction (motive := fun i _ => Z (i + 1) ≤ V)
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
        ∑ j ∈ range (b + 1), Koszul.koszul (homComp j η) from map_sum (koszulₗ K (Fin n)) _ _]
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
