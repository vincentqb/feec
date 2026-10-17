module

public import Feec.Algebra.Koszul

/-!
# The polynomial form spaces `P_rΛᵏ`, `H_rΛᵏ`, `P_r⁻Λᵏ` in any dimension

For polynomial differential forms on `R^d` (`Feec.Koszul.PolyForm`, any finite linearly ordered
index type `d`):

* `homForm r k = H_rΛᵏ`: `k`-forms with coefficients homogeneous of degree `r`;
* `polyForm r k = P_rΛᵏ`: `k`-forms with coefficients of total degree `≤ r`;
* `polyFormMinus r k = P_r⁻Λᵏ = P_{r-1}Λᵏ + κ H_{r-1}Λ^{k+1}` (the first-kind Nédélec /
  trimmed space).

## Main results

* degree bookkeeping: `d : H_rΛᵏ → H_{r-1}Λ^{k+1}`, `κ : H_rΛ^{k+1} → H_{r+1}Λᵏ`,
  `d : P_rΛᵏ → P_{r-1}Λ^{k+1}`, `κ : P_rΛ^{k+1} → P_{r+1}Λᵏ` (`totalDegree_pderiv_le`);
* inclusions `P_{r-1}Λᵏ ⊆ P_r⁻Λᵏ ⊆ P_rΛᵏ` (`1 ≤ r`), and the subcomplex properties
  `d P_r⁻Λᵏ ⊆ P_{r-1}Λ^{k+1} ⊆ P_r⁻Λ^{k+1}`;
* over a field of characteristic zero, for `r + k > 0`:
  **exactness** of the homogeneous Koszul and polynomial de Rham complexes
  (`exists_koszul_eq_of_koszul_eq_zero`, `exists_extDeriv_eq_of_extDeriv_eq_zero`) and the
  **decomposition** `H_rΛᵏ = κ H_{r-1}Λ^{k+1} ⊕ d H_{r+1}Λ^{k-1}` (`homForm_le_sup`,
  `eq_zero_of_eq_koszul_of_eq_extDeriv`). The hypothesis `r + k > 0` is necessary (constants,
  `r = k = 0`); the thesis omits it.

## References

* [QuennevilleBelair2015], §4.7, §4.10
* [AFW2006], §3; [Arnold2018], Ch. 7
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.Koszul

open ExteriorFibre

/-! ### Degrees of partial derivatives -/

section Degree

variable {R : Type*} [CommRing R] {d : Type*}

/-- `∂ᵢ` lowers the total degree by one. -/
theorem totalDegree_pderiv_le (i : d) (p : MvPolynomial d R) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  conv_lhs => rw [← sum_homogeneousComponent p, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun n hn => ?_)
  have hn := Finset.mem_range.1 hn
  exact ((homogeneousComponent_isHomogeneous n p).pderiv (i := i)).totalDegree_le.trans
    (by omega)

end Degree

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d] [Fintype d]

/-! ### The differentials as linear maps -/

omit [Fintype d] in
theorem extDeriv_smul (c : R) (ω : PolyForm R d) : extDeriv (c • ω) = c • extDeriv ω := by
  funext s; simp [extDeriv_apply, Finset.smul_sum]

theorem koszul_smul (c : R) (ω : PolyForm R d) : koszul (c • ω) = c • koszul ω := by
  funext s; simp [koszul_apply, Finset.smul_sum]

variable (R d) in
/-- The exterior derivative as an `R`-linear map. -/
def extDerivₗ : PolyForm R d →ₗ[R] PolyForm R d where
  toFun := extDeriv
  map_add' := extDeriv_add
  map_smul' := extDeriv_smul

variable (R d) in
/-- The Koszul differential as an `R`-linear map. -/
def koszulₗ : PolyForm R d →ₗ[R] PolyForm R d where
  toFun := koszul
  map_add' := koszul_add
  map_smul' := koszul_smul

omit [Fintype d] in
@[simp] theorem extDerivₗ_apply (ω : PolyForm R d) : extDerivₗ R d ω = extDeriv ω := rfl

@[simp] theorem koszulₗ_apply (ω : PolyForm R d) : koszulₗ R d ω = koszul ω := rfl

/-! ### The spaces -/

omit [Fintype d] in
/-- The signs have total degree zero. -/
theorem totalDegree_sgn (j : d) (s : Finset d) : (sgn j s : MvPolynomial d R).totalDegree = 0 :=
  Nat.le_zero.1 (isHomogeneous_sgn j s).totalDegree_le

variable (R d) in
/-- `H_rΛᵏ`: `k`-forms with coefficients homogeneous of degree `r`. Thesis: §4.7 -/
def homForm (r k : ℕ) : Submodule R (PolyForm R d) where
  carrier := {ω | IsDeg k ω ∧ IsHomogeneousForm r ω}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => isHomogeneous_zero _ _ _⟩
  add_mem' {ω η} hω hη := ⟨fun s hs => by simp [hω.1 s hs, hη.1 s hs],
    fun s => (hω.2 s).add (hη.2 s)⟩
  smul_mem' c ω hω := ⟨fun s hs => by simp [hω.1 s hs], fun s =>
    (mem_homogeneousSubmodule _ _).1 (Submodule.smul_mem _ c ((mem_homogeneousSubmodule _ _).2
      (hω.2 s)))⟩

variable (R d) in
/-- `P_rΛᵏ`: `k`-forms with polynomial coefficients of total degree `≤ r`. Thesis: §4.7 -/
def polyForm (r k : ℕ) : Submodule R (PolyForm R d) where
  carrier := {ω | IsDeg k ω ∧ ∀ s, (ω s).totalDegree ≤ r}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => by simp⟩
  add_mem' {ω η} hω hη := ⟨fun s hs => by simp [hω.1 s hs, hη.1 s hs],
    fun s => (totalDegree_add _ _).trans (max_le (hω.2 s) (hη.2 s))⟩
  smul_mem' c ω hω := ⟨fun s hs => by simp [hω.1 s hs], fun s =>
    (totalDegree_smul_le c (ω s)).trans (hω.2 s)⟩

variable (R d) in
/-- `P_r⁻Λᵏ = P_{r-1}Λᵏ + κ H_{r-1}Λ^{k+1}` (`r ≥ 1`), the trimmed (first-kind Nédélec)
polynomial forms. Thesis: §4.7, §4.10 -/
def polyFormMinus (r k : ℕ) : Submodule R (PolyForm R d) :=
  polyForm R d (r - 1) k ⊔ (homForm R d (r - 1) (k + 1)).map (koszulₗ R d)

omit [LinearOrder d] [Fintype d] in
theorem homForm_le_polyForm (r k : ℕ) : homForm R d r k ≤ polyForm R d r k :=
  fun _ hω => ⟨hω.1, fun s => (hω.2 s).totalDegree_le⟩

omit [LinearOrder d] [Fintype d] in
theorem polyForm_mono {r r' : ℕ} (h : r ≤ r') (k : ℕ) : polyForm R d r k ≤ polyForm R d r' k :=
  fun _ hω => ⟨hω.1, fun s => (hω.2 s).trans h⟩

/-! ### Degree bookkeeping -/

omit [Fintype d] in
/-- `d : H_rΛᵏ → H_{r-1}Λ^{k+1}`. Thesis: §4.7 -/
theorem extDeriv_mem_homForm {r k : ℕ} {ω : PolyForm R d} (h : ω ∈ homForm R d r k) :
    extDeriv ω ∈ homForm R d (r - 1) (k + 1) :=
  ⟨IsDeg.extDeriv h.1, IsHomogeneousForm.extDeriv h.2⟩

/-- `κ : H_rΛᵏ → H_{r+1}Λ^{k-1}` (for `k = 0` the image is `0`). Thesis: §4.7 -/
theorem koszul_mem_homForm {r k : ℕ} {ω : PolyForm R d} (h : ω ∈ homForm R d r k) :
    koszul ω ∈ homForm R d (r + 1) (k - 1) := by
  refine ⟨fun s hs => sum_eq_zero fun j hj => ?_, h.2.koszul⟩
  rw [h.1 (insert j s) (by rw [card_insert_of_notMem (mem_compl.1 hj)]; omega), mul_zero]

omit [Fintype d] in
/-- `d : P_rΛᵏ → P_{r-1}Λ^{k+1}`. Thesis: §4.7 -/
theorem extDeriv_mem_polyForm {r k : ℕ} {ω : PolyForm R d} (h : ω ∈ polyForm R d r k) :
    extDeriv ω ∈ polyForm R d (r - 1) (k + 1) := by
  refine ⟨IsDeg.extDeriv h.1, fun s => (totalDegree_finsetSum _ _).trans
    (Finset.sup_le fun j _ => (totalDegree_mul _ _).trans ?_)⟩
  rw [totalDegree_sgn, zero_add]
  exact (totalDegree_pderiv_le j _).trans (Nat.sub_le_sub_right (h.2 _) 1)

/-- `κ : P_rΛᵏ → P_{r+1}Λ^{k-1}`. Thesis: §4.7 -/
theorem koszul_mem_polyForm {r k : ℕ} {ω : PolyForm R d} (h : ω ∈ polyForm R d r k) :
    koszul ω ∈ polyForm R d (r + 1) (k - 1) := by
  refine ⟨fun s hs => sum_eq_zero fun j hj => ?_, fun s => (totalDegree_finsetSum _ _).trans
    (Finset.sup_le fun j _ => (totalDegree_mul _ _).trans ?_)⟩
  · rw [h.1 (insert j s) (by rw [card_insert_of_notMem (mem_compl.1 hj)]; omega), mul_zero]
  · have hX : (sgn j s * X j : MvPolynomial d R).totalDegree ≤ 1 := by
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_sgn, zero_add]
      exact (isHomogeneous_X R j).totalDegree_le
    exact le_trans (add_le_add hX (h.2 (insert j s))) (by omega)

/-! ### `P_r⁻Λᵏ` -/

theorem polyForm_le_polyFormMinus (r k : ℕ) :
    polyForm R d (r - 1) k ≤ polyFormMinus R d r k := le_sup_left

/-- `κ H_{r-1}Λ^{k+1} ⊆ H_rΛᵏ` for `r ≥ 1`. -/
theorem map_koszul_homForm_le {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    (homForm R d (r - 1) (k + 1)).map (koszulₗ R d) ≤ homForm R d r k := by
  rintro _ ⟨ω, hω, rfl⟩
  have := koszul_mem_homForm hω
  rwa [Nat.sub_add_cancel hr, Nat.add_sub_cancel] at this

/-- `P_{r-1}Λᵏ ⊆ P_r⁻Λᵏ ⊆ P_rΛᵏ` (`r ≥ 1`). Thesis: §4.7 -/
theorem polyFormMinus_le_polyForm {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    polyFormMinus R d r k ≤ polyForm R d r k :=
  sup_le (polyForm_mono (Nat.sub_le r 1) k)
    ((map_koszul_homForm_le hr k).trans (homForm_le_polyForm r k))

/-- **`d P_r⁻Λᵏ ⊆ P_{r-1}Λ^{k+1}`**: on `κ H_{r-1}Λ^{k+1}`, `dκω` is homogeneous of degree
`r - 1`. Thesis: §4.7 -/
theorem extDeriv_mem_polyForm_of_mem_polyFormMinus {r k : ℕ} (hr : 1 ≤ r) {ω : PolyForm R d}
    (h : ω ∈ polyFormMinus R d r k) : extDeriv ω ∈ polyForm R d (r - 1) (k + 1) := by
  refine Submodule.mem_sup.1 h |>.elim fun a ⟨ha, b, hb, hab⟩ => ?_
  rw [← hab, extDeriv_add]
  refine add_mem (polyForm_mono (Nat.sub_le _ 1) _ (extDeriv_mem_polyForm ha)) ?_
  obtain ⟨η, hη, rfl⟩ := hb
  have := extDeriv_mem_homForm (map_koszul_homForm_le hr k ⟨η, hη, rfl⟩)
  exact homForm_le_polyForm _ _ this

/-- **`P_r⁻Λ` is a subcomplex**: `d P_r⁻Λᵏ ⊆ P_r⁻Λ^{k+1}`. Thesis: §4.7, §4.10 -/
theorem extDeriv_mem_polyFormMinus {r k : ℕ} (hr : 1 ≤ r) {ω : PolyForm R d}
    (h : ω ∈ polyFormMinus R d r k) : extDeriv ω ∈ polyFormMinus R d r (k + 1) :=
  polyForm_le_polyFormMinus r (k + 1) (extDeriv_mem_polyForm_of_mem_polyFormMinus hr h)

omit [Fintype d] in
/-- `P_rΛ` is a subcomplex: `d P_rΛᵏ ⊆ P_rΛ^{k+1}`. -/
theorem extDeriv_mem_polyForm_same {r k : ℕ} {ω : PolyForm R d} (h : ω ∈ polyForm R d r k) :
    extDeriv ω ∈ polyForm R d r (k + 1) :=
  polyForm_mono (Nat.sub_le r 1) _ (extDeriv_mem_polyForm h)

/-! ### Exactness and the Koszul decomposition (characteristic zero) -/

section Field

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- The homotopy formula on `H_rΛᵏ` with `K`-scalars: `(dκ + κd) ω = (r + k) ω`. -/
theorem extDeriv_koszul_add_koszul_extDeriv_of_mem {r k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ homForm K d r k) :
    extDeriv (koszul ω) + koszul (extDeriv ω) = ((r + k : ℕ) : K) • ω := by
  rw [extDeriv_koszul_add_koszul_extDeriv_of_isHomogeneous h.2 h.1, Nat.cast_smul_eq_nsmul,
    Nat.cast_smul_eq_nsmul]

/-- **The Koszul decomposition, spanning part**: for `r + k > 0`, every `ω ∈ H_rΛᵏ` is
`κ α + d β` with `α = (r+k)⁻¹ dω ∈ H_{r-1}Λ^{k+1}` and `β = (r+k)⁻¹ κω ∈ H_{r+1}Λ^{k-1}`.
Thesis: §4.7 (corrected: needs `r + k > 0`) -/
theorem eq_koszul_add_extDeriv {r k : ℕ} (hrk : 0 < r + k) {ω : PolyForm K d}
    (h : ω ∈ homForm K d r k) :
    ω = koszul (((r + k : ℕ) : K)⁻¹ • extDeriv ω) + extDeriv (((r + k : ℕ) : K)⁻¹ • koszul ω) := by
  have hc : ((r + k : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hrk.ne'
  rw [koszul_smul, extDeriv_smul, ← smul_add, add_comm (koszul _),
    extDeriv_koszul_add_koszul_extDeriv_of_mem h, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- `H_rΛᵏ ⊆ κ H_{r-1}Λ^{k+1} + d H_{r+1}Λ^{k-1}` for `r + k > 0`. Thesis: §4.7 -/
theorem homForm_le_sup {r k : ℕ} (hrk : 0 < r + k) :
    homForm K d r k ≤ (homForm K d (r - 1) (k + 1)).map (koszulₗ K d) ⊔
      (homForm K d (r + 1) (k - 1)).map (extDerivₗ K d) := fun ω h => by
  rw [eq_koszul_add_extDeriv hrk h]
  exact Submodule.add_mem_sup ⟨_, Submodule.smul_mem _ _ (extDeriv_mem_homForm h), rfl⟩
    ⟨_, Submodule.smul_mem _ _ (koszul_mem_homForm h), rfl⟩

/-- **The Koszul decomposition is direct**: for `r + k > 0`, an element of `H_rΛᵏ` that is both
`κ α` and `d β` vanishes (`κ² = 0`, `d² = 0`, homotopy formula). Thesis: §4.7 -/
theorem eq_zero_of_eq_koszul_of_eq_extDeriv {r k : ℕ} (hrk : 0 < r + k) {ω α β : PolyForm K d}
    (h : ω ∈ homForm K d r k) (hα : ω = koszul α) (hβ : ω = extDeriv β) : ω = 0 := by
  have h1 : koszul ω = 0 := by rw [hα, koszul_koszul]
  have h2 : extDeriv ω = 0 := by rw [hβ, extDeriv_extDeriv]
  have := extDeriv_koszul_add_koszul_extDeriv_of_mem h
  rw [h1, h2, extDeriv_zero, koszul_zero, add_zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hrk.ne')

/-- **Exactness of the homogeneous Koszul complex**: for `r + k > 0`, `ω ∈ H_rΛᵏ` with
`κω = 0` is `κ η` with `η ∈ H_{r-1}Λ^{k+1}`. Thesis: §4.7 -/
theorem exists_koszul_eq_of_koszul_eq_zero {r k : ℕ} (hrk : 0 < r + k) {ω : PolyForm K d}
    (h : ω ∈ homForm K d r k) (hκ : koszul ω = 0) :
    ∃ η ∈ homForm K d (r - 1) (k + 1), koszul η = ω := by
  refine ⟨((r + k : ℕ) : K)⁻¹ • extDeriv ω, Submodule.smul_mem _ _ (extDeriv_mem_homForm h), ?_⟩
  conv_rhs => rw [eq_koszul_add_extDeriv hrk h]
  rw [hκ, smul_zero, extDeriv_zero, add_zero]

/-- **Polynomial Poincaré lemma** (exactness of the homogeneous polynomial de Rham complex):
for `r + k > 0`, a closed `ω ∈ H_rΛᵏ` is `d η` with `η ∈ H_{r+1}Λ^{k-1}`. Thesis: §4.7 -/
theorem exists_extDeriv_eq_of_extDeriv_eq_zero {r k : ℕ} (hrk : 0 < r + k) {ω : PolyForm K d}
    (h : ω ∈ homForm K d r k) (hd : extDeriv ω = 0) :
    ∃ η ∈ homForm K d (r + 1) (k - 1), extDeriv η = ω := by
  refine ⟨((r + k : ℕ) : K)⁻¹ • koszul ω, Submodule.smul_mem _ _ (koszul_mem_homForm h), ?_⟩
  conv_rhs => rw [eq_koszul_add_extDeriv hrk h]
  rw [hd, smul_zero, koszul_zero, zero_add]

end Field

end Feec.Koszul
