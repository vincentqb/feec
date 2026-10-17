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

/-! ### `d P_r⁻Λᵏ` for every `r` -/

/-- `d (κ H_{r-1}Λ^{k+1}) ⊆ H_{r-1}Λ^{k+1}`, for every `r`. -/
theorem extDeriv_koszul_mem_homForm {r k : ℕ} {η : PolyForm R d}
    (h : η ∈ homForm R d (r - 1) (k + 1)) : extDeriv (koszul η) ∈ homForm R d (r - 1) (k + 1) := by
  have h1 := koszul_mem_homForm h
  rw [Nat.add_sub_cancel] at h1
  have := extDeriv_mem_homForm h1
  rwa [Nat.add_sub_cancel] at this

/-- **`d P_r⁻Λᵏ ⊆ P_{r-1}Λ^{k+1}`** for every `r` (at `r = 0`, `P_0⁻Λᵏ = P_0Λᵏ + κ H_0Λ^{k+1}`).
Thesis: §4.7 -/
theorem extDeriv_mem_polyForm_sub_one_of_mem_polyFormMinus {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ polyFormMinus R d r k) : extDeriv ω ∈ polyForm R d (r - 1) (k + 1) := by
  refine Submodule.mem_sup.1 h |>.elim fun a ⟨ha, b, hb, hab⟩ => ?_
  rw [← hab, extDeriv_add]
  refine add_mem (polyForm_mono (Nat.sub_le _ 1) _ (extDeriv_mem_polyForm ha)) ?_
  obtain ⟨η, hη, rfl⟩ := hb
  exact homForm_le_polyForm _ _ (extDeriv_koszul_mem_homForm hη)

/-- `d P_r⁻Λᵏ ⊆ P_r⁻Λ^{k+1}` for every `r`. Thesis: §4.7, §4.10 -/
theorem extDeriv_mem_polyFormMinus_of_mem_polyFormMinus {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ polyFormMinus R d r k) : extDeriv ω ∈ polyFormMinus R d r (k + 1) :=
  polyForm_le_polyFormMinus r (k + 1) (extDeriv_mem_polyForm_sub_one_of_mem_polyFormMinus h)

/-- `d P_rΛᵏ ⊆ P_r⁻Λ^{k+1}`. Thesis: §4.10 -/
theorem extDeriv_mem_polyFormMinus_of_mem_polyForm {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ polyForm R d r k) : extDeriv ω ∈ polyFormMinus R d r (k + 1) :=
  polyForm_le_polyFormMinus r (k + 1) (extDeriv_mem_polyForm h)

/-- The Koszul differential vanishes on `0`-forms. -/
theorem IsDeg.koszul_eq_zero {ω : PolyForm R d} (hω : IsDeg 0 ω) : Koszul.koszul ω = 0 := by
  funext s
  rw [koszul_apply]
  refine sum_eq_zero fun j hj => ?_
  rw [hω (insert j s) (by rw [card_insert_of_notMem (mem_compl.1 hj)]; omega), mul_zero]

/-- **`κ P_r⁻Λ^{k+1} ⊆ P_rΛᵏ`** (`r ≥ 1`): `κ P_{r-1}Λ^{k+1} ⊆ P_rΛᵏ` and `κ κ = 0`. -/
theorem koszul_mem_polyForm_of_mem_polyFormMinus_succ {r k : ℕ} (hr : 1 ≤ r)
    {ω : PolyForm R d}
    (h : ω ∈ polyFormMinus R d r (k + 1)) : koszul ω ∈ polyForm R d r k := by
  obtain ⟨a, ha, b, ⟨c, -, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
  change koszul (a + koszul c) ∈ _
  rw [koszul_add, koszul_koszul, add_zero]
  have := koszul_mem_polyForm ha
  rwa [Nat.sub_add_cancel hr, Nat.add_sub_cancel] at this

/-! ### Segments of the polynomial de Rham complex -/

/-- `V₀ → V₁ → V₂` is a **subcomplex** (a segment of a subcomplex) of the polynomial de Rham
complex: `d V₀ ⊆ V₁` and `d V₁ ⊆ V₂`. Thesis: §4.6, §4.10 -/
structure IsSubcomplex (V₀ V₁ V₂ : Submodule R (PolyForm R d)) : Prop where
  extDeriv_mem₀ : ∀ ω ∈ V₀, extDeriv ω ∈ V₁
  extDeriv_mem₁ : ∀ ω ∈ V₁, extDeriv ω ∈ V₂

variable (R d) in
/-- `S ⊗ V` for `V = R^ι`: `ι`-tuples of forms in `S` (for `ι = Fin 3`, matrix fields with
every row in `S`). -/
def tensorForm (ι : Type*) (S : Submodule R (PolyForm R d)) : Submodule R (ι → PolyForm R d) :=
  Submodule.pi Set.univ fun _ => S

omit [LinearOrder d] [Fintype d] in
@[simp] theorem mem_tensorForm {ι : Type*} {S : Submodule R (PolyForm R d)}
    {A : ι → PolyForm R d} : A ∈ tensorForm R d ι S ↔ ∀ a, A a ∈ S := by
  simp [tensorForm, Submodule.mem_pi]

/-- `V₀ ⊗ V → V₁ ⊗ V → V₂ ⊗ V` is a subcomplex for the row-wise exterior derivative. -/
structure IsTensorSubcomplex (ι : Type*) (V₀ V₁ V₂ : Submodule R (PolyForm R d)) : Prop where
  extDeriv_mem₀ : ∀ A ∈ tensorForm R d ι V₀, (fun a => extDeriv (A a)) ∈ tensorForm R d ι V₁
  extDeriv_mem₁ : ∀ A ∈ tensorForm R d ι V₁, (fun a => extDeriv (A a)) ∈ tensorForm R d ι V₂

omit [Fintype d] in
/-- A scalar subcomplex lifts row-wise to `⊗ V`, and conversely (`ι` nonempty). -/
theorem isTensorSubcomplex_iff {ι : Type*} [Nonempty ι] {V₀ V₁ V₂ : Submodule R (PolyForm R d)} :
    IsTensorSubcomplex ι V₀ V₁ V₂ ↔ IsSubcomplex V₀ V₁ V₂ := by
  obtain ⟨a⟩ := ‹Nonempty ι›
  refine ⟨fun h => ⟨fun ω hω => ?_, fun ω hω => ?_⟩, fun h => ⟨fun A hA => ?_, fun A hA => ?_⟩⟩
  · exact mem_tensorForm.1 (h.extDeriv_mem₀ (fun _ => ω) (mem_tensorForm.2 fun _ => hω)) a
  · exact mem_tensorForm.1 (h.extDeriv_mem₁ (fun _ => ω) (mem_tensorForm.2 fun _ => hω)) a
  · exact mem_tensorForm.2 fun b => h.extDeriv_mem₀ _ (mem_tensorForm.1 hA b)
  · exact mem_tensorForm.2 fun b => h.extDeriv_mem₁ _ (mem_tensorForm.1 hA b)

omit [Fintype d] in
theorem IsSubcomplex.tensor {ι : Type*} {V₀ V₁ V₂ : Submodule R (PolyForm R d)}
    (h : IsSubcomplex V₀ V₁ V₂) : IsTensorSubcomplex ι V₀ V₁ V₂ :=
  ⟨fun _ hA => mem_tensorForm.2 fun b => h.extDeriv_mem₀ _ (mem_tensorForm.1 hA b),
    fun _ hA => mem_tensorForm.2 fun b => h.extDeriv_mem₁ _ (mem_tensorForm.1 hA b)⟩

/-- **The corrected list of polynomial discretizations** (thesis §4.9, p. 63 for the vector
wave equation, and §4.10, p. 66 for (4.14), corrected), in every dimension and form degree:
`P_{r+1}Λᵏ × P_rΛ^{k+1} × {P_{r-1}Λ^{k+2}, P_r⁻Λ^{k+2}}` and
`P_rΛᵏ × P_r⁻Λ^{k+1} × {P_{r-1}Λ^{k+2}, P_r⁻Λ^{k+2}}` are subcomplexes. No hypothesis on `r`.
The thesis' `P_{r+1}Λ⁰ × P_r⁻Λ¹` is not (`Feec.Counterexamples.PolynomialForms`).
See [QuennevilleBelair2015], §4.10. -/
theorem isSubcomplex_corrected (r k : ℕ) :
    IsSubcomplex (polyForm R d (r + 1) k) (polyForm R d r (k + 1)) (polyForm R d (r - 1) (k + 2)) ∧
    IsSubcomplex (polyForm R d (r + 1) k) (polyForm R d r (k + 1)) (polyFormMinus R d r (k + 2)) ∧
    IsSubcomplex (polyForm R d r k) (polyFormMinus R d r (k + 1)) (polyForm R d (r - 1) (k + 2)) ∧
    IsSubcomplex (polyForm R d r k) (polyFormMinus R d r (k + 1))
      (polyFormMinus R d r (k + 2)) := by
  have h0 : ∀ ω ∈ polyForm R d (r + 1) k, extDeriv ω ∈ polyForm R d r (k + 1) := fun ω hω => by
    simpa using extDeriv_mem_polyForm hω
  have h1 : ∀ ω ∈ polyForm R d r (k + 1), extDeriv ω ∈ polyForm R d (r - 1) (k + 2) :=
    fun _ hω => extDeriv_mem_polyForm hω
  exact ⟨⟨h0, h1⟩, ⟨h0, fun _ hω => extDeriv_mem_polyFormMinus_of_mem_polyForm hω⟩,
    ⟨fun _ hω => extDeriv_mem_polyFormMinus_of_mem_polyForm hω,
      fun _ hω => extDeriv_mem_polyForm_sub_one_of_mem_polyFormMinus hω⟩,
    ⟨fun _ hω => extDeriv_mem_polyFormMinus_of_mem_polyForm hω,
      fun _ hω => extDeriv_mem_polyFormMinus_of_mem_polyFormMinus hω⟩⟩

/-- **The corrected list, `⊗ V`** (row-wise, the matrix wave equation (4.14) for `ι = Fin 3`,
`k = 0`). See [QuennevilleBelair2015], §4.10. -/
theorem isTensorSubcomplex_corrected (ι : Type*) (r k : ℕ) :
    IsTensorSubcomplex ι (polyForm R d (r + 1) k) (polyForm R d r (k + 1))
      (polyForm R d (r - 1) (k + 2)) ∧
    IsTensorSubcomplex ι (polyForm R d (r + 1) k) (polyForm R d r (k + 1))
      (polyFormMinus R d r (k + 2)) ∧
    IsTensorSubcomplex ι (polyForm R d r k) (polyFormMinus R d r (k + 1))
      (polyForm R d (r - 1) (k + 2)) ∧
    IsTensorSubcomplex ι (polyForm R d r k) (polyFormMinus R d r (k + 1))
      (polyFormMinus R d r (k + 2)) :=
  have h := isSubcomplex_corrected (R := R) (d := d) r k
  ⟨h.1.tensor, h.2.1.tensor, h.2.2.1.tensor, h.2.2.2.tensor⟩

/-- **The alternative repair** of thesis §4.10: keep `P_{r+1}Λᵏ` and raise the trimmed index,
`P_{r+1}Λᵏ × P_{r+1}⁻Λ^{k+1} × {P_rΛ^{k+2}, P_{r+1}⁻Λ^{k+2}}` (`⊗ V`).
See [QuennevilleBelair2015], §4.10. -/
theorem isTensorSubcomplex_alt (ι : Type*) (r k : ℕ) :
    IsTensorSubcomplex ι (polyForm R d (r + 1) k) (polyFormMinus R d (r + 1) (k + 1))
      (polyForm R d r (k + 2)) ∧
    IsTensorSubcomplex ι (polyForm R d (r + 1) k) (polyFormMinus R d (r + 1) (k + 1))
      (polyFormMinus R d (r + 1) (k + 2)) :=
  ⟨(isTensorSubcomplex_corrected ι (r + 1) k).2.2.1,
    (isTensorSubcomplex_corrected ι (r + 1) k).2.2.2⟩

/-- **The discretizations of the reduced system (4.15)** (thesis §4.10, after Prop 4.18):
`d` maps each of `P_rΛ^{k+1} ⊗ V`, `P_r⁻Λ^{k+1} ⊗ V` into each of `P_{r-1}Λ^{k+2} ⊗ V`,
`P_r⁻Λ^{k+2} ⊗ V`, as printed. See [QuennevilleBelair2015], §4.10. -/
theorem extDeriv_mem_tensorForm_reduced (ι : Type*) (r k : ℕ) :
    (∀ A ∈ tensorForm R d ι (polyForm R d r (k + 1)),
      (fun a => extDeriv (A a)) ∈ tensorForm R d ι (polyForm R d (r - 1) (k + 2))) ∧
    (∀ A ∈ tensorForm R d ι (polyForm R d r (k + 1)),
      (fun a => extDeriv (A a)) ∈ tensorForm R d ι (polyFormMinus R d r (k + 2))) ∧
    (∀ A ∈ tensorForm R d ι (polyFormMinus R d r (k + 1)),
      (fun a => extDeriv (A a)) ∈ tensorForm R d ι (polyForm R d (r - 1) (k + 2))) ∧
    (∀ A ∈ tensorForm R d ι (polyFormMinus R d r (k + 1)),
      (fun a => extDeriv (A a)) ∈ tensorForm R d ι (polyFormMinus R d r (k + 2))) :=
  have h := isTensorSubcomplex_corrected (R := R) (d := d) ι r k
  ⟨h.1.extDeriv_mem₁, h.2.1.extDeriv_mem₁, h.2.2.1.extDeriv_mem₁, h.2.2.2.extDeriv_mem₁⟩

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

/-- **`d ω ∉ P_r⁻Λ^{k+1}`** for every nonzero `ω ∈ H_sΛᵏ` with `κ ω = 0` and `s > r ≥ 1`, in every
dimension and form degree: otherwise `(s + k) ω = κ d ω ∈ P_rΛᵏ`. (Every `0`-form has
`κ ω = 0`.) Thesis: §4.10 -/
theorem extDeriv_not_mem_polyFormMinus_of_koszul_eq_zero {r s k : ℕ} (hr : 1 ≤ r)
    (hs : r + 1 ≤ s) {ω : PolyForm K d} (hω : ω ∈ homForm K d s k) (hκ : koszul ω = 0)
    (hne : ω ≠ 0) : extDeriv ω ∉ polyFormMinus K d r (k + 1) := by
  intro hv
  have h1 := koszul_mem_polyForm_of_mem_polyFormMinus_succ hr hv
  have h2 := extDeriv_koszul_add_koszul_extDeriv_of_mem hω
  rw [hκ, extDeriv_zero, zero_add] at h2
  rw [h2] at h1
  obtain ⟨t, ht⟩ : ∃ t, ω t ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    exact hne (funext h)
  have hc : ((s + k : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hhom : ((((s + k : ℕ) : K) • ω) t).IsHomogeneous s := by
    rw [Pi.smul_apply, smul_eq_C_mul]
    have := (isHomogeneous_C d ((s + k : ℕ) : K)).mul (hω.2 t)
    rwa [zero_add] at this
  have hne' : (((s + k : ℕ) : K) • ω) t ≠ 0 := by
    rw [Pi.smul_apply]
    exact smul_ne_zero hc ht
  have := h1.2 t
  rw [hhom.totalDegree hne'] at this
  omega

omit [CharZero K] [Fintype d] in
/-- The `0`-form `x_j^s` lies in `H_sΛ⁰`. -/
theorem single_pow_mem_homForm (j : d) (s : ℕ) :
    (Pi.single ∅ (X j ^ s) : PolyForm K d) ∈ homForm K d s 0 := by
  refine ⟨fun t ht => Pi.single_eq_of_ne (by rintro rfl; exact ht (by simp)) _, fun t => ?_⟩
  by_cases h : t = ∅
  · subst h; rw [Pi.single_eq_same]; exact isHomogeneous_X_pow j s
  · rw [Pi.single_eq_of_ne h]; exact isHomogeneous_zero _ _ _

/-- **Maximality of `P_rΛ⁰` for `P_r⁻Λ¹`** (`r ≥ 1`), in every dimension: `d P_sΛ⁰ ⊆ P_r⁻Λ¹` iff
`s ≤ r`. See [QuennevilleBelair2015], §4.10. -/
theorem map_extDeriv_polyForm_le_polyFormMinus_iff [Nonempty d] {r s : ℕ} (hr : 1 ≤ r) :
    (polyForm K d s 0).map (extDerivₗ K d) ≤ polyFormMinus K d r 1 ↔ s ≤ r := by
  refine ⟨fun h => ?_, fun hs => ?_⟩
  · by_contra hs
    obtain ⟨j⟩ := ‹Nonempty d›
    have hm := single_pow_mem_homForm (K := K) j s
    refine extDeriv_not_mem_polyFormMinus_of_koszul_eq_zero (k := 0) hr (by omega) hm
      (IsDeg.koszul_eq_zero hm.1) (fun h0 => ?_) (h ⟨_, homForm_le_polyForm _ _ hm, rfl⟩)
    have := congrFun h0 ∅
    rw [Pi.single_eq_same, Pi.zero_apply] at this
    exact pow_ne_zero s (X_ne_zero j) this
  · rintro _ ⟨ω, hω, rfl⟩
    exact extDeriv_mem_polyFormMinus_of_mem_polyForm (polyForm_mono hs 0 hω)

omit [Fintype d] in
/-- **Maximality of `P_{r+1}Λ⁰` for `P_rΛ¹`**, in every dimension: `d P_sΛ⁰ ⊆ P_rΛ¹` iff
`s ≤ r + 1` (witness `x_j^s`, whose differential has degree `s - 1`).
See [QuennevilleBelair2015], §4.10. -/
theorem map_extDeriv_polyForm_le_polyForm_iff [Nonempty d] {r s : ℕ} :
    (polyForm K d s 0).map (extDerivₗ K d) ≤ polyForm K d r 1 ↔ s ≤ r + 1 := by
  refine ⟨fun h => ?_, fun hs => ?_⟩
  · by_contra hs
    obtain ⟨j⟩ := ‹Nonempty d›
    have hm := single_pow_mem_homForm (K := K) j s
    have h1 := (h ⟨_, homForm_le_polyForm _ _ hm, rfl⟩).2 {j}
    rw [extDerivₗ_apply, extDeriv_apply, Finset.sum_singleton, Finset.erase_singleton,
      Pi.single_eq_same, (pderiv j).leibniz_pow, pderiv_X_self, smul_eq_mul, mul_one] at h1
    have hsg : (sgn j {j} : MvPolynomial d K) = 1 := by
      simp [sgn, Finset.filter_singleton]
    have hs0 : ((s : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [hsg, one_mul, nsmul_eq_mul, ← C_eq_coe_nat, C_mul_X_pow_eq_monomial,
      totalDegree_monomial _ hs0, Finsupp.sum_single_index rfl] at h1
    omega
  · rintro _ ⟨ω, hω, rfl⟩
    have := extDeriv_mem_polyForm (polyForm_mono hs 0 hω)
    simpa using this

/-- **The `0`-form spaces behind the reduced discretizations** (thesis §4.10, after Prop 4.18):
`P_sΛ⁰ ⊗ V` is admissible below `P_rΛ¹ ⊗ V` iff `s ≤ r + 1`, and below `P_r⁻Λ¹ ⊗ V` iff `s ≤ r`
(`r ≥ 1`), in every dimension. See [QuennevilleBelair2015], §4.10. -/
theorem tensorForm_reduced_iff (ι : Type*) [Nonempty ι] [Nonempty d] {r : ℕ} (hr : 1 ≤ r)
    (s : ℕ) :
    ((∀ A ∈ tensorForm K d ι (polyForm K d s 0),
      (fun a => extDeriv (A a)) ∈ tensorForm K d ι (polyForm K d r 1)) ↔ s ≤ r + 1) ∧
    ((∀ A ∈ tensorForm K d ι (polyForm K d s 0),
      (fun a => extDeriv (A a)) ∈ tensorForm K d ι (polyFormMinus K d r 1)) ↔ s ≤ r) := by
  have row : ∀ V : Submodule K (PolyForm K d),
      (∀ A ∈ tensorForm K d ι (polyForm K d s 0),
        (fun a => extDeriv (A a)) ∈ tensorForm K d ι V) ↔
        (polyForm K d s 0).map (extDerivₗ K d) ≤ V := fun V => by
    obtain ⟨a⟩ := ‹Nonempty ι›
    refine ⟨fun h => ?_, fun h A hA => mem_tensorForm.2 fun b =>
      h ⟨_, mem_tensorForm.1 hA b, rfl⟩⟩
    rintro _ ⟨ω, hω, rfl⟩
    exact mem_tensorForm.1 (h (fun _ => ω) (mem_tensorForm.2 fun _ => hω)) a
  rw [row, row]
  exact ⟨map_extDeriv_polyForm_le_polyForm_iff, map_extDeriv_polyForm_le_polyFormMinus_iff hr⟩

/-- **`P_r⁻Λ¹ ⊊ P_rΛ¹`** (`r ≥ 1`), in every dimension `≥ 1`: `d x_j^{r+1}` lies in `P_rΛ¹` but
not in `P_r⁻Λ¹`. See [QuennevilleBelair2015], §4.10. -/
theorem polyFormMinus_lt_polyForm_one [Nonempty d] {r : ℕ} (hr : 1 ≤ r) :
    polyFormMinus K d r 1 < polyForm K d r 1 := by
  refine lt_of_le_of_ne (polyFormMinus_le_polyForm hr 1) fun h => ?_
  obtain ⟨j⟩ := ‹Nonempty d›
  have hm := single_pow_mem_homForm (K := K) j (r + 1)
  have h1 : extDeriv (Pi.single ∅ (X j ^ (r + 1)) : PolyForm K d) ∈ polyForm K d r 1 := by
    simpa using extDeriv_mem_polyForm (homForm_le_polyForm _ _ hm)
  refine extDeriv_not_mem_polyFormMinus_of_koszul_eq_zero (k := 0) hr le_rfl hm
    (IsDeg.koszul_eq_zero hm.1) (fun h0 => ?_) (h ▸ h1)
  have := congrFun h0 ∅
  rw [Pi.single_eq_same, Pi.zero_apply] at this
  exact pow_ne_zero _ (X_ne_zero j) this

omit [CharZero K] in
/-- **`P_{r-1}Λᵏ ⊊ P_r⁻Λᵏ`** (`r ≥ 1`, `k < dim`): `κ (x_j^{r-1} dx_s)`, `j ∈ s`, `|s| = k + 1`,
has a coefficient `± x_j^r` of degree `r`. (In `ℝ³` with `k = 2`: `x₀^{r-1} x ∈ P_r⁻Λ²`.)
See [QuennevilleBelair2015], §4.10. -/
theorem polyForm_lt_polyFormMinus {r k : ℕ} (hr : 1 ≤ r)
    (hk : k + 1 ≤ Fintype.card d) : polyForm K d (r - 1) k < polyFormMinus K d r k := by
  refine lt_of_le_of_ne (polyForm_le_polyFormMinus r k) fun h => ?_
  have hd : 0 < Fintype.card d := by omega
  obtain ⟨j⟩ : Nonempty d := Fintype.card_pos_iff.1 hd
  obtain ⟨t, ht, htk⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset d).erase j)
    (n := k) (by rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]; omega)
  have hjt : j ∉ t := fun hj => (Finset.notMem_erase j _) (ht hj)
  set η : PolyForm K d := Pi.single (insert j t) (X j ^ (r - 1))
  have hη : η ∈ homForm K d (r - 1) (k + 1) := by
    refine ⟨fun u hu => Pi.single_eq_of_ne (by
      rintro rfl; exact hu (by rw [Finset.card_insert_of_notMem hjt, htk])) _, fun u => ?_⟩
    by_cases hu : u = insert j t
    · subst hu; simp only [η, Pi.single_eq_same]; exact isHomogeneous_X_pow j (r - 1)
    · simp only [η, Pi.single_eq_of_ne hu]; exact isHomogeneous_zero _ _ _
  have hmem : koszul η ∈ polyFormMinus K d r k :=
    Submodule.mem_sup_right ⟨η, hη, rfl⟩
  rw [← h] at hmem
  have hcoef : koszul η t = sgn j t * X j ^ r := by
    rw [koszul_apply, Finset.sum_eq_single j]
    · simp only [η, Pi.single_eq_same]
      rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hr]
    · intro i _ hij
      have : insert i t ≠ insert j t := fun e => by
        have hi : i ∈ insert j t := e ▸ Finset.mem_insert_self i t
        rcases Finset.mem_insert.1 hi with hi | hi
        · exact hij hi
        · exact (Finset.mem_compl.1 ‹i ∈ tᶜ›) hi
      simp [η, Pi.single_eq_of_ne this]
    · intro hj; exact absurd (Finset.mem_compl.2 hjt) hj
  have hdeg := hmem.2 t
  rw [hcoef] at hdeg
  have hs : (sgn j t : MvPolynomial d K) * X j ^ r =
      monomial (Finsupp.single j r) ((-1 : K) ^ #({l ∈ t | l < j})) := by
    rw [sgn, show ((-1 : MvPolynomial d K)) ^ #({l ∈ t | l < j}) =
      C ((-1 : K) ^ #({l ∈ t | l < j})) by simp, C_mul_X_pow_eq_monomial]
  have h0 : ((-1 : K) ^ #({l ∈ t | l < j})) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  rw [hs, totalDegree_monomial _ h0, Finsupp.sum_single_index rfl] at hdeg
  omega

end Field

end Feec.Koszul
