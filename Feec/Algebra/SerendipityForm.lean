module

public import Feec.Algebra.CubicalForm

/-!
# The serendipity polynomial forms `S_rΛᵏ` of the cube

The serendipity forms `S_rΛᵏ = P_rΛᵏ + κ M_{r-1}Λ^{k+1} + d κ M_rΛᵏ` of the cube, after
[ArnoldAwanou2014], (17), where `M_rΛᵏ` is spanned by the monomial forms of superlinear degree
`≤ r`: a subcomplex, increasing in `r`, contained in `M_{r+1}Λᵏ` and, over a field of
characteristic zero, stable under the traces on coordinate planes.

## References

* [D. N. Arnold, G. Awanou, *Finite element differential forms on cubical meshes*][ArnoldAwanou2014]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.Koszul

open ExteriorFibre

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d] [Fintype d]

/-! ### Superlinear degree -/

/-- The superlinear degree `|α| - #{j ∉ s | α_j = 1}` of the monomial form `x^α dx_s`. -/
def superlinDeg (s : Finset d) (α : d →₀ ℕ) : ℕ := ∑ j, if j ∉ s ∧ α j = 1 then 0 else α j

/-- The exponents `α` with `x^α dx_s` of superlinear degree `≤ r`. -/
def superlinSupport (r : ℕ) (s : Finset d) : Set (d →₀ ℕ) := {α | superlinDeg s α ≤ r}

private theorem sum_le_sum_add_one {f g : d → ℕ} (j : d) (h : ∀ i, f i ≤ g i + if i = j then 1 else 0) :
    ∑ i, f i ≤ ∑ i, g i + 1 := by
  calc ∑ i, f i ≤ ∑ i, (g i + if i = j then 1 else 0) := sum_le_sum fun i _ => h i
    _ = ∑ i, g i + 1 := by rw [sum_add_distrib, sum_ite_eq' univ j]; simp

theorem superlinDeg_le (s : Finset d) (α : d →₀ ℕ) : superlinDeg s α ≤ α.sum fun _ e => e := by
  rw [Finsupp.sum_fintype _ _ fun _ => rfl]
  exact sum_le_sum fun j _ => by split_ifs <;> omega

theorem superlinDeg_sub_single_le {s : Finset d} {j : d} (hj : j ∈ s) (α : d →₀ ℕ) :
    superlinDeg s (α - Finsupp.single j 1) ≤ superlinDeg (s.erase j) α := by
  refine sum_le_sum fun i _ => ?_
  by_cases hi : i = j
  · subst hi; simp [hj]; split_ifs <;> omega
  · simp [hi]

theorem superlinDeg_add_single_le {s : Finset d} {j : d} (hj : j ∉ s) (α : d →₀ ℕ) :
    superlinDeg s (α + Finsupp.single j 1) ≤ superlinDeg (insert j s) α + 1 := by
  refine sum_le_sum_add_one j fun i => ?_
  by_cases hi : i = j
  · subst hi; simp [hj]; split_ifs <;> omega
  · simp [hi]

omit [CommRing R] in
theorem superlinDeg_filter_le {f : d → Option R} {s t : Finset d} (hs : s ⊆ t)
    (hst : ∀ j ∈ t, j ∉ s → f j ≠ none) (γ : d →₀ ℕ) :
    superlinDeg s (γ.filter fun j => (f j).isNone) ≤ superlinDeg t γ := by
  refine sum_le_sum fun i _ => ?_
  by_cases hf : f i = none
  · have : i ∈ s ↔ i ∈ t := ⟨fun h => hs h, fun h => by_contra fun his => hst i h his hf⟩
    simp [hf, this]
  · simp [hf]

/-! ### The spaces -/

theorem superlinSupport_mono {r r' : ℕ} (h : r ≤ r') (s : Finset d) :
    superlinSupport r s ⊆ superlinSupport r' s := fun _ hα => le_trans hα h


variable (R d) in
/-- `M_rΛᵏ`: the span of the monomial `k`-forms of superlinear degree `≤ r`. -/
def superlinForm (r k : ℕ) : Submodule R (PolyForm R d) := supportForm R d k (superlinSupport r)

theorem mem_superlinForm {r k : ℕ} {ω : PolyForm R d} :
    ω ∈ superlinForm R d r k ↔ IsDeg k ω ∧ ∀ s, ω s ∈ restrictSupport R (superlinSupport r s) :=
  Iff.rfl

theorem superlinForm_mono {r r' : ℕ} (h : r ≤ r') (k : ℕ) :
    superlinForm R d r k ≤ superlinForm R d r' k :=
  supportForm_mono (fun s => superlinSupport_mono h s) k

theorem superlinSupport_subset_cubeSupport (r : ℕ) (s : Finset d) :
    superlinSupport r s ⊆ cubeSupport (fun _ => r + 1) s := fun α (hα : superlinDeg s α ≤ r) j => by
  have := (single_le_sum (f := fun i => if i ∉ s ∧ α i = 1 then 0 else α i)
    (fun _ _ => Nat.zero_le _) (mem_univ j)).trans hα
  show α j + _ ≤ r + 1
  by_cases hj : j ∈ s
  · simp only [hj, not_true_eq_false, false_and, ↓reduceIte] at this ⊢; omega
  · by_cases h1 : α j = 1
    · simp [hj, h1]
    · simp only [hj, h1, not_false_eq_true, and_false, ↓reduceIte] at this ⊢; omega

theorem superlinForm_le_cubeFormMinus (r k : ℕ) :
    superlinForm R d r k ≤ cubeFormMinus R (fun _ => r + 1) k :=
  supportForm_mono (superlinSupport_subset_cubeSupport r) k

instance {K : Type*} [Field K] (r k : ℕ) : FiniteDimensional K (superlinForm K d r k) :=
  Submodule.finiteDimensional_of_le (superlinForm_le_cubeFormMinus r k)

theorem finrank_superlinForm {K : Type*} [Field K] (r k : ℕ) :
    Module.finrank K (superlinForm K d r k) =
      ∑ s ∈ powersetCard k univ, Nat.card (superlinSupport (d := d) r s) :=
  finrank_supportForm fun s =>
    (Set.toFinite (cubeSupport (fun _ => r + 1) s)).subset (superlinSupport_subset_cubeSupport r s)

theorem polyForm_le_superlinForm (r k : ℕ) : polyForm R d r k ≤ superlinForm R d r k :=
  fun ω hω => ⟨hω.1, fun s => restrictSupport_mono R (fun α hα => (superlinDeg_le s α).trans hα)
    (show ω s ∈ restrictTotalDegree d R r from (mem_restrictTotalDegree _ _ _).2 (hω.2 s))⟩

theorem extDeriv_mem_superlinForm {r k : ℕ} {ω : PolyForm R d} (h : ω ∈ superlinForm R d r k) :
    extDeriv ω ∈ superlinForm R d r (k + 1) :=
  ⟨IsDeg.extDeriv h.1, fun s => Submodule.sum_mem _ fun j hj => sgn_mul_mem j s
    (pderiv_mem_restrictSupport j (fun α hα _ =>
      (superlinDeg_sub_single_le hj α).trans hα) (h.2 _))⟩

omit [LinearOrder d] [Fintype d] in
theorem X_mul_mem_restrictSupport {S T : Set (d →₀ ℕ)} (j : d)
    (h : ∀ α ∈ S, α + Finsupp.single j 1 ∈ T) {p : MvPolynomial d R}
    (hp : p ∈ restrictSupport R S) : X j * p ∈ restrictSupport R T :=
  map_mem_of_mem_restrictSupport (LinearMap.mulLeft R (X j)) (fun α hα => by
    rw [LinearMap.mulLeft_apply, X, monomial_mul_monomial, one_mul]
    exact (monomial_mem_restrictSupport R).2 (Or.inl (by rw [add_comm]; exact h α hα))) hp

theorem koszul_mem_superlinForm {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ superlinForm R d r (k + 1)) : koszul ω ∈ superlinForm R d (r + 1) k := by
  refine ⟨IsDeg.koszul h.1, fun s => Submodule.sum_mem _ fun j hj => ?_⟩
  rw [mul_assoc]
  exact sgn_mul_mem j s (X_mul_mem_restrictSupport j (fun α hα =>
    (superlinDeg_add_single_le (mem_compl.1 hj) α).trans (Nat.add_le_add_right hα 1)) (h.2 _))

variable (R d) in
/-- The serendipity forms `S_rΛᵏ = P_rΛᵏ + κ M_{r-1}Λ^{k+1} + d κ M_rΛᵏ`. -/
def serendipityForm (r k : ℕ) : Submodule R (PolyForm R d) :=
  polyForm R d r k ⊔
    (if r = 0 then ⊥ else (superlinForm R d (r - 1) (k + 1)).map (koszulₗ R d)) ⊔
      ((superlinForm R d r k).map (koszulₗ R d)).map (extDerivₗ R d)

theorem polyForm_le_serendipityForm (r k : ℕ) : polyForm R d r k ≤ serendipityForm R d r k :=
  le_sup_left.trans le_sup_left

theorem koszul_mem_serendipityForm {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ superlinForm R d r (k + 1)) : koszul ω ∈ serendipityForm R d (r + 1) k :=
  Submodule.mem_sup_left (Submodule.mem_sup_right (by
    rw [ite_eq_right r.succ_ne_zero]; exact Submodule.mem_map_of_mem h))

theorem extDeriv_koszul_mem_serendipityForm {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ superlinForm R d r k) : extDeriv (koszul ω) ∈ serendipityForm R d r k :=
  Submodule.mem_sup_right (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem h))

theorem serendipityForm_induction {r k : ℕ} {P : PolyForm R d → Prop}
    (h0 : ∀ ω ∈ polyForm R d r k, P ω)
    (h1 : ∀ r', r' + 1 = r → ∀ ω ∈ superlinForm R d r' (k + 1), P (koszul ω))
    (h2 : ∀ ω ∈ superlinForm R d r k, P (extDeriv (koszul ω)))
    (hadd : ∀ ω η, P ω → P η → P (ω + η)) {ω : PolyForm R d} (h : ω ∈ serendipityForm R d r k) :
    P ω := by
  obtain ⟨a, ha, c, ⟨γ, hγ, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
  obtain ⟨p, hp, b, hb, rfl⟩ := Submodule.mem_sup.1 ha
  obtain ⟨γ, hγ, rfl⟩ := hγ
  refine hadd _ _ (hadd _ _ (h0 p hp) ?_) (h2 γ hγ)
  split_ifs at hb with hr
  · rw [(Submodule.mem_bot R).1 hb]; simpa using h0 0 (Submodule.zero_mem _)
  · obtain ⟨β, hβ, rfl⟩ := hb
    exact h1 (r - 1) (by omega) β hβ

/-- `S_rΛᵏ ⊆ M_{r+1}Λᵏ` ([ArnoldAwanou2014], Thm 3.2). -/
theorem serendipityForm_le_superlinForm (r k : ℕ) :
    serendipityForm R d r k ≤ superlinForm R d (r + 1) k := fun ω h =>
  serendipityForm_induction
    (fun _ hω => superlinForm_mono (Nat.le_succ r) k (polyForm_le_superlinForm r k hω))
    (fun _ h _ hω => superlinForm_mono (by omega) k (koszul_mem_superlinForm hω))
    (fun _ hω => by
      cases k with
      | zero => rw [IsDeg.koszul_eq_zero hω.1, extDeriv_zero]; exact Submodule.zero_mem _
      | succ k => exact extDeriv_mem_superlinForm (koszul_mem_superlinForm hω))
    (fun _ _ => add_mem) h

instance {K : Type*} [Field K] (r k : ℕ) : FiniteDimensional K (serendipityForm K d r k) :=
  Submodule.finiteDimensional_of_le (serendipityForm_le_superlinForm r k)

/-- `d S_{r+1}Λᵏ ⊆ S_rΛ^{k+1}` ([ArnoldAwanou2014], Thm 3.3). -/
theorem extDeriv_mem_serendipityForm {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ serendipityForm R d (r + 1) k) : extDeriv ω ∈ serendipityForm R d r (k + 1) :=
  serendipityForm_induction
    (fun _ hω => polyForm_le_serendipityForm r (k + 1) (extDeriv_mem_polyForm hω))
    (fun _ h _ hω => extDeriv_koszul_mem_serendipityForm (by rwa [Nat.succ_injective h] at hω))
    (fun _ _ => by rw [extDeriv_extDeriv]; exact Submodule.zero_mem _)
    (fun ω η hω hη => by rw [extDeriv_add]; exact add_mem hω hη) h

theorem isSubcomplex_serendipityForm (r k : ℕ) :
    IsSubcomplex (serendipityForm R d (r + 2) k) (serendipityForm R d (r + 1) (k + 1))
      (serendipityForm R d r (k + 2)) :=
  ⟨fun _ h => extDeriv_mem_serendipityForm h, fun _ h => extDeriv_mem_serendipityForm h⟩

/-- `S_rΛᵏ ⊆ S_{r'}Λᵏ` for `r ≤ r'` ([ArnoldAwanou2014], Thm 3.4). -/
theorem serendipityForm_mono {r r' : ℕ} (h : r ≤ r') (k : ℕ) :
    serendipityForm R d r k ≤ serendipityForm R d r' k :=
  sup_le_sup (sup_le_sup (polyForm_mono h k) (by
    split_ifs with hr hr'
    · exact le_rfl
    · exact bot_le
    · omega
    · exact Submodule.map_mono (superlinForm_mono (Nat.sub_le_sub_right h 1) _)))
    (Submodule.map_mono (Submodule.map_mono (superlinForm_mono h k)))

/-! ### `0`-forms: the serendipity space -/

theorem koszul_single_singleton (j : d) (p : MvPolynomial d R) :
    koszul (Pi.single {j} p : PolyForm R d) = Pi.single ∅ (X j * p) := by
  funext t
  rw [koszul_apply]
  by_cases ht : t = ∅
  · subst ht
    rw [compl_empty, sum_eq_single j (fun q _ hq => by simp [hq]) (by simp)]
    simp [sgn]
  · rw [Pi.single_eq_of_ne ht]
    refine sum_eq_zero fun q hq => ?_
    have : insert q t ≠ {j} := fun h => by
      have := congrArg card h
      rw [card_insert_of_notMem (mem_compl.1 hq), card_singleton] at this
      exact ht (card_eq_zero.1 (by omega))
    rw [Pi.single_eq_of_ne this, mul_zero]

private theorem sum_add_one_le {f g : d → ℕ} (j : d) (h : ∀ i, f i + (if i = j then 1 else 0) ≤ g i) :
    ∑ i, f i + 1 ≤ ∑ i, g i := by
  calc ∑ i, f i + 1 = ∑ i, (f i + if i = j then 1 else 0) := by
        rw [sum_add_distrib, sum_ite_eq' univ j]; simp
    _ ≤ ∑ i, g i := sum_le_sum fun i _ => h i

theorem superlinDeg_sub_single_add_one {s : Finset d} {α : d →₀ ℕ} {j : d} (hjs : j ∈ s)
    (hj : 2 ≤ α j) : superlinDeg s (α - Finsupp.single j 1) + 1 ≤ superlinDeg (s.erase j) α :=
  sum_add_one_le j fun i => by
    by_cases hi : i = j
    · subst hi; simp [hjs]; split_ifs <;> omega
    · simp [hi]

theorem superlinDeg_eq_zero {s : Finset d} {α : d →₀ ℕ}
    (h : ∀ i, α i + (if i ∈ s then 1 else 0) ≤ 1) : superlinDeg s α = 0 :=
  sum_eq_zero fun i _ => by have := h i; split_ifs at this ⊢ <;> simp_all; omega

theorem serendipityForm_zero {r : ℕ} (hr : 1 ≤ r) :
    serendipityForm R d r 0 = superlinForm R d r 0 := by
  refine le_antisymm (fun ω h => serendipityForm_induction
    (fun _ hω => polyForm_le_superlinForm r 0 hω)
    (fun _ h _ hω => h ▸ koszul_mem_superlinForm hω)
    (fun _ hω => by rw [IsDeg.koszul_eq_zero hω.1, extDeriv_zero]; exact Submodule.zero_mem _)
    (fun _ _ => add_mem) h) (supportForm_le_of_single fun s hs α hα => ?_)
  obtain rfl := card_eq_zero.1 hs
  by_cases hdeg : α.degree ≤ r
  · refine polyForm_le_serendipityForm r 0 ⟨fun t ht => ?_, fun t => ?_⟩
    · exact Pi.single_eq_of_ne (fun h => ht (by rw [h]; rfl)) _
    · by_cases ht : t = ∅
      · subst ht; simpa using (totalDegree_monomial_le α (1 : R)).trans hdeg
      · simp [Pi.single_eq_of_ne ht]
  -- `x^α = κ(x^{α - e_j} dx_j)`
  have hκ : ∀ j, 1 ≤ α j → α - Finsupp.single j 1 ∈ superlinSupport (r - 1) {j} →
      (Pi.single ∅ (monomial α 1) : PolyForm R d) ∈ serendipityForm R d r 0 := fun j hj hβ => by
    have hm : X j * monomial (α - Finsupp.single j 1) (1 : R) = monomial α 1 := by
      rw [X, monomial_mul_monomial, one_mul,
        add_tsub_cancel_of_le (Finsupp.single_le_iff.2 hj)]
    rw [← hm, ← koszul_single_singleton]
    have h1 := single_monomial_mem_supportForm (R := R) hβ
    rw [card_singleton] at h1
    simpa [Nat.sub_add_cancel hr] using koszul_mem_serendipityForm h1
  by_cases hsup : ∃ j, 2 ≤ α j
  · obtain ⟨j, hj⟩ := hsup
    exact hκ j (by omega) (by
      have := superlinDeg_sub_single_add_one (mem_singleton_self j) hj
      rw [erase_singleton] at this
      exact le_trans (by omega) (Nat.sub_le_sub_right hα 1))
  · push Not at hsup
    obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
      by_contra h0; push Not at h0
      exact hdeg (by simp [Finsupp.degree_eq_sum, h0])
    exact hκ j (by omega) (by
      show superlinDeg _ _ ≤ _
      rw [superlinDeg_eq_zero fun i => by
        have := hsup i
        by_cases hi : i = j
        · subst hi; simp; omega
        · simp [hi]; omega]
      exact Nat.zero_le _)

theorem serendipityForm_zero_le_cubeFormMinus {r : ℕ} (hr : 1 ≤ r) :
    serendipityForm R d r 0 ≤ cubeFormMinus R (fun _ => r) 0 := by
  rw [serendipityForm_zero hr]
  refine fun ω hω => ⟨hω.1, fun s => ?_⟩
  by_cases hs : s = ∅
  · subst hs
    have hsub : superlinSupport r (∅ : Finset d) ⊆ cubeSupport (fun _ => r) ∅ := fun α hα j => by
      have := single_le_sum (f := fun i => if i ∉ (∅ : Finset d) ∧ α i = 1 then 0 else α i)
        (fun _ _ => Nat.zero_le _) (mem_univ j)
      have h' : (∑ i, if i ∉ (∅ : Finset d) ∧ α i = 1 then 0 else α i) ≤ r := hα
      simp only [notMem_empty, ↓reduceIte, add_zero]
      simp only [notMem_empty, not_false_eq_true, true_and] at this h'
      split_ifs at this <;> omega
    exact restrictSupport_mono R hsub (hω.2 ∅)
  · rw [hω.1 s (fun h => hs (card_eq_zero.1 h))]; exact Submodule.zero_mem _

/-! ### Traces -/

theorem faceSubst_X_mul (f : d → Option R) (q : d) (p : MvPolynomial d R) :
    faceSubst f (X q * p) = (f q).elim (X q) C * faceSubst f p := by
  have : faceSubst f ∘ₗ LinearMap.mulLeft R (X q) =
      LinearMap.mulLeft R ((f q).elim (X q) C) ∘ₗ faceSubst f :=
    (basisMonomials d R).ext fun γ => by
      simp only [coe_basisMonomials, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.mulLeft_apply]
      rw [show X q * monomial γ (1 : R) = monomial (Finsupp.single q 1 + γ) 1 by
        rw [X, monomial_mul_monomial, one_mul], faceSubst_monomial, faceSubst_monomial, one_mul,
        one_mul]
      have hw : faceWeight f (Finsupp.single q 1 + γ) = (f q).elim 1 id * faceWeight f γ := by
        simp only [faceWeight]
        rw [← mul_prod_erase univ _ (mem_univ q),
          ← mul_prod_erase univ (fun j => (f j).elim 1 fun c => c ^ γ j) (mem_univ q), ← mul_assoc]
        congr 1
        · cases f q <;> simp [pow_add]
        · exact prod_congr rfl fun j hj => by simp [Ne.symm (ne_of_mem_erase hj)]
      rw [hw]
      cases hq : f q with
      | none =>
        have hf : (Finsupp.single q 1 + γ).filter (fun j => (f j).isNone) =
            Finsupp.single q 1 + γ.filter (fun j => (f j).isNone) := by
          ext j
          by_cases hj : j = q
          · subst hj; simp [hq]
          · simp [Finsupp.filter_apply, Ne.symm hj]
        rw [hf]
        simp [X, monomial_mul_monomial]
      | some c =>
        have hf : (Finsupp.single q 1 + γ).filter (fun j => (f j).isNone) =
            γ.filter (fun j => (f j).isNone) := by
          ext j
          by_cases hj : j = q
          · subst hj; simp [hq]
          · simp [Finsupp.filter_apply, Ne.symm hj]
        rw [hf]
        simp [C_mul_monomial]
  exact LinearMap.congr_fun this p

omit [LinearOrder d] in
theorem totalDegree_faceSubst_le (f : d → Option R) (p : MvPolynomial d R) :
    (faceSubst f p).totalDegree ≤ p.totalDegree := by
  rw [← mem_restrictTotalDegree]
  refine faceSubst_mem_restrictSupport f (fun γ (hγ : (γ.sum fun _ e => e) ≤ _) =>
    show ((γ.filter _).sum fun _ e => e) ≤ _ from le_trans ?_ hγ)
    ((mem_restrictTotalDegree _ _ _).2 le_rfl)
  rw [Finsupp.sum_fintype _ _ fun _ => rfl, Finsupp.sum_fintype _ _ fun _ => rfl]
  exact sum_le_sum fun j _ => by simp only [Finsupp.filter_apply]; split_ifs <;> omega

theorem IsDeg.cubeTrace {k : ℕ} {ω : PolyForm R d} (h : IsDeg k ω) (f : d → Option R) :
    IsDeg k (cubeTrace f ω) := fun s hs => by simp [Koszul.cubeTrace, h s hs]

theorem cubeTrace_mem_polyForm (f : d → Option R) {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ polyForm R d r k) : cubeTrace f ω ∈ polyForm R d r k :=
  ⟨IsDeg.cubeTrace h.1 f, fun s => by
    unfold Koszul.cubeTrace
    split_ifs
    · exact (totalDegree_faceSubst_le f _).trans (h.2 s)
    · simp⟩

theorem cubeTrace_mem_superlinForm (f : d → Option R) {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ superlinForm R d r k) : cubeTrace f ω ∈ superlinForm R d r k :=
  ⟨IsDeg.cubeTrace h.1 f, fun s => by
    unfold Koszul.cubeTrace
    split_ifs
    · exact faceSubst_mem_restrictSupport f (fun γ hγ => (superlinDeg_filter_le subset_rfl
        (fun _ hj hj' => absurd hj hj') γ).trans hγ) (h.2 s)
    · exact Submodule.zero_mem _⟩

theorem cubeTrace_koszul_sub_mem_superlinForm (f : d → Option R) {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ superlinForm R d r (k + 1)) :
    cubeTrace f (koszul ω) - koszul (cubeTrace f ω) ∈ superlinForm R d r k := by
  refine ⟨fun s hs => by
    rw [Pi.sub_apply, IsDeg.cubeTrace (IsDeg.koszul h.1) f s hs,
      IsDeg.koszul (IsDeg.cubeTrace h.1 f) s hs, sub_zero],
    fun s => ?_⟩
  rw [Pi.sub_apply, koszul_apply]
  unfold Koszul.cubeTrace
  by_cases hs : ∀ j ∈ s, (f j).isNone
  · rw [ite_eq_left hs, koszul_apply, map_sum, ← sum_sub_distrib]
    refine Submodule.sum_mem _ fun q hq => ?_
    rw [mul_assoc, map_sgn_mul, faceSubst_X_mul, mul_assoc, ← mul_sub]
    refine sgn_mul_mem q s ?_
    cases hfq : f q with
    | none =>
      rw [ite_eq_left fun j hj => by
        rcases mem_insert.1 hj with rfl | hj
        · simp [hfq]
        · exact hs j hj]
      simp
    | some c =>
      rw [ite_eq_right fun h' => by simpa [hfq] using h' q (mem_insert_self q s), mul_zero, sub_zero]
      simp only [Option.elim_some]
      rw [← smul_eq_C_mul]
      refine Submodule.smul_mem _ c (faceSubst_mem_restrictSupport f (fun γ hγ =>
        (superlinDeg_filter_le (subset_insert q s) (fun j hj hjs => ?_) γ).trans hγ) (h.2 _))
      rcases mem_insert.1 hj with rfl | hj
      · simp [hfq]
      · exact absurd hj hjs
  · rw [ite_eq_right hs, zero_sub, neg_mem_iff, sum_eq_zero fun q _ => by
      rw [ite_eq_right fun h' => hs fun j hj => h' j (mem_insert_of_mem hj), mul_zero]]
    exact Submodule.zero_mem _

/-! ### `M_rΛᵏ ⊆ S_{r+1}Λᵏ` and stability under traces -/

variable {K : Type*} [Field K] [CharZero K]

theorem superlinForm_le_serendipityForm (r k : ℕ) :
    superlinForm K d r k ≤ serendipityForm K d (r + 1) k := by
  refine supportForm_le_of_single fun s hs α hα => ?_
  set μ : PolyForm K d := Pi.single s (monomial α 1)
  have hμ : μ ∈ superlinForm K d r k := hs ▸ single_monomial_mem_supportForm hα
  have hhom : IsHomogeneousForm α.degree μ := fun t => by
    by_cases ht : t = s
    · subst ht; simpa [μ] using isHomogeneous_monomial (1 : K) rfl
    · simpa [μ, Pi.single_eq_of_ne ht] using isHomogeneous_zero _ _ _
  have H := extDeriv_koszul_add_koszul_extDeriv_of_isHomogeneous hhom hμ.1
  rw [Nat.cast_smul_eq_nsmul] at H
  by_cases h0 : α.degree + k = 0
  · -- a constant `0`-form
    refine polyForm_le_serendipityForm (r + 1) k ⟨hμ.1, fun t => ?_⟩
    by_cases ht : t = s
    · subst ht
      have : (α.sum fun _ => id) = α.degree := rfl
      simpa [μ] using (totalDegree_monomial_le α (1 : K)).trans (by omega)
    · simp [μ, Pi.single_eq_of_ne ht]
  · have hμ' : μ = ((α.degree + k : ℕ) : K)⁻¹ •
        (extDeriv (koszul μ) + koszul (extDeriv μ)) := by
      rw [H, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 h0),
        one_smul]
    rw [hμ']
    refine Submodule.smul_mem _ _ (add_mem
      (extDeriv_koszul_mem_serendipityForm (superlinForm_mono r.le_succ k hμ))
      (koszul_mem_serendipityForm (extDeriv_mem_superlinForm hμ)))

/-- In characteristic zero, `tr_f S_rΛᵏ ⊆ S_rΛᵏ` on every coordinate plane `f`
([ArnoldAwanou2014], Thm 3.5 (adapted)). -/
theorem cubeTrace_mem_serendipityForm (f : d → Option K) {r k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ serendipityForm K d r k) : cubeTrace f ω ∈ serendipityForm K d r k :=
  serendipityForm_induction
    (fun _ hp => polyForm_le_serendipityForm r k (cubeTrace_mem_polyForm f hp))
    (fun r' hr a ha => by
      subst hr
      rw [← sub_add_cancel (cubeTrace f (koszul a)) (koszul (cubeTrace f a))]
      exact add_mem (superlinForm_le_serendipityForm r' k
        (cubeTrace_koszul_sub_mem_superlinForm f ha))
        (koszul_mem_serendipityForm (cubeTrace_mem_superlinForm f ha)))
    (fun b hb => by
      cases k with
      | zero =>
        rw [IsDeg.koszul_eq_zero hb.1, extDeriv_zero, cubeTrace_zero]
        exact Submodule.zero_mem _
      | succ k =>
        rw [← extDeriv_cubeTrace, ← sub_add_cancel (cubeTrace f (koszul b))
          (koszul (cubeTrace f b)), extDeriv_add]
        have hρ := cubeTrace_koszul_sub_mem_superlinForm f hb
        exact add_mem (extDeriv_mem_serendipityForm (superlinForm_le_serendipityForm r k hρ))
          (extDeriv_koszul_mem_serendipityForm (cubeTrace_mem_superlinForm f hb)))
    (fun ω η hω hη => by rw [cubeTrace_add]; exact add_mem hω hη) h

theorem image_cubeTrace_serendipityForm (f : d → Option K) (r k : ℕ) :
    cubeTrace f '' (serendipityForm K d r k : Set (PolyForm K d)) =
      {θ | θ ∈ serendipityForm K d r k ∧ cubeTrace f θ = θ} := by
  ext θ
  refine ⟨?_, fun ⟨hθ, he⟩ => ⟨θ, hθ, he⟩⟩
  rintro ⟨ω, hω, rfl⟩
  refine ⟨cubeTrace_mem_serendipityForm f hω, ?_⟩
  rw [cubeTrace_cubeTrace]
  congr 1
  funext j
  cases f j <;> rfl

end Feec.Koszul
