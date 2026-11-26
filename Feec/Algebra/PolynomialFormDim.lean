module

public import Feec.Algebra.PolynomialForm
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Fintype.Powerset

/-!
# Dimensions, direct sums and exact sequences of polynomial form spaces

The spaces `H_rΛᵏ`, `P_rΛᵏ` and `P_r⁻Λᵏ` on `K^d`, `n = #d`, over a field: their dimensions and
direct sums, and in characteristic zero the Koszul decompositions, `dim P_r⁻Λᵏ` and the exactness
of the polynomial de Rham and Koszul complexes ([AFW2006], §3; [AFW2010], §5.1).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.Koszul

open ExteriorFibre

variable {R : Type*} [CommRing R] {d : Type*}

/-! ### Homogeneous components of polynomial forms -/

variable (j : ℕ) in
/-- The homogeneous component of polynomial degree `j` of a polynomial form, coefficientwise. -/
def homComp (ω : PolyForm R d) : PolyForm R d := fun s => homogeneousComponent j (ω s)

theorem homComp_apply (j : ℕ) (ω : PolyForm R d) (s : Finset d) :
    homComp j ω s = homogeneousComponent j (ω s) := rfl

@[simp] theorem homComp_zero (j : ℕ) : homComp j (0 : PolyForm R d) = 0 := by
  funext s; simp [homComp_apply]

theorem homComp_add (j : ℕ) (ω η : PolyForm R d) :
    homComp j (ω + η) = homComp j ω + homComp j η := by
  funext s; simp [homComp_apply]

theorem isDeg_homComp {k : ℕ} {ω : PolyForm R d} (h : IsDeg k ω) (j : ℕ) :
    IsDeg k (homComp j ω) := fun s hs => by simp [homComp_apply, h s hs]

theorem homComp_mem_homForm {k : ℕ} {ω : PolyForm R d} (h : IsDeg k ω) (j : ℕ) :
    homComp j ω ∈ homForm R d j k :=
  ⟨isDeg_homComp h j, fun s => homogeneousComponent_isHomogeneous j (ω s)⟩

theorem homComp_of_mem_homForm {m k : ℕ} {ω : PolyForm R d} (h : ω ∈ homForm R d m k) (j : ℕ) :
    homComp j ω = if j = m then ω else 0 := by
  funext s
  rw [homComp_apply, homogeneousComponent_of_mem (h.2 s)]
  split_ifs <;> rfl

theorem homComp_eq_zero_of_mem_polyForm {r k : ℕ} {ω : PolyForm R d} (h : ω ∈ polyForm R d r k)
    {j : ℕ} (hj : r < j) : homComp j ω = 0 := by
  funext s
  exact homogeneousComponent_eq_zero _ _ (lt_of_le_of_lt (h.2 s) hj)

theorem sum_homComp {r k : ℕ} {ω : PolyForm R d} (h : ω ∈ polyForm R d r k) :
    ∑ j ∈ range (r + 1), homComp j ω = ω := by
  funext s
  rw [Finset.sum_apply]
  simp only [homComp_apply]
  conv_rhs => rw [← sum_homogeneousComponent (ω s)]
  have hle : (ω s).totalDegree + 1 ≤ r + 1 := by have := h.2 s; omega
  rw [← Finset.sum_range_add_sum_Ico _ hle]
  rw [Finset.sum_eq_zero (s := Ico _ _) fun j hj => homogeneousComponent_eq_zero _ _
    (by simp at hj; omega), add_zero]

theorem homComp_mem_polyForm_iff {r k : ℕ} {ω : PolyForm R d} (hk : IsDeg k ω) :
    ω ∈ polyForm R d r k ↔ ∀ j, r < j → homComp j ω = 0 := by
  refine ⟨fun h j hj => homComp_eq_zero_of_mem_polyForm h hj, fun h => ⟨hk, fun s => ?_⟩⟩
  rw [totalDegree, Finset.sup_le_iff]
  intro m hm
  by_contra hlt
  push Not at hlt
  have h0 := congrFun (h _ hlt) s
  rw [homComp_apply, Pi.zero_apply] at h0
  have := congrArg (fun p : MvPolynomial d R => p.coeff m) h0
  simp only [coeff_homogeneousComponent, AddMonoidAlgebra.coeff_zero] at this
  rw [ite_eq_left_iff.2 (fun h => absurd (by rw [Finsupp.degree]; rfl) h)] at this
  exact (mem_support_iff.1 hm) this

section Order

variable [LinearOrder d]

omit [LinearOrder d] in
theorem homogeneousComponent_pderiv (j : ℕ) (i : d) (p : MvPolynomial d R) :
    homogeneousComponent j (pderiv i p) = pderiv i (homogeneousComponent (j + 1) p) := by
  conv_lhs => rw [← sum_homogeneousComponent p, map_sum, map_sum]
  rw [Finset.sum_eq_single (j + 1)]
  · have := ((homogeneousComponent_isHomogeneous (j + 1) p).pderiv (i := i))
    rw [Nat.add_sub_cancel] at this
    exact homogeneousComponent_eq_self this
  · intro m _ hm
    have hh := (homogeneousComponent_isHomogeneous m p).pderiv (i := i)
    rw [homogeneousComponent_of_mem hh]
    split_ifs with h
    · rcases m with _ | m
      · rw [homogeneousComponent_zero, pderiv_C]
      · simp at h; omega
    · rfl
  · intro hj
    rw [homogeneousComponent_eq_zero _ p (by simp at hj; omega), map_zero, map_zero]

theorem homComp_extDeriv (j : ℕ) (ω : PolyForm R d) :
    homComp j (extDeriv ω) = extDeriv (homComp (j + 1) ω) := by
  funext s
  simp only [homComp_apply, extDeriv_apply, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show (sgn i s : MvPolynomial d R) = C (sgn i s) by simp [sgn], homogeneousComponent_C_mul,
    homogeneousComponent_pderiv]

omit [LinearOrder d] in
theorem degree_sub_single_add_one {α : d →₀ ℕ} {j : d} (hj : 1 ≤ α j) :
    (α - Finsupp.single j 1).degree + 1 = α.degree := by
  conv_rhs => rw [← tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hj)]
  rw [map_add, Finsupp.degree_single]

variable [Fintype d]

theorem homComp_koszul (j : ℕ) (ω : PolyForm R d) :
    homComp (j + 1) (koszul ω) = koszul (homComp j ω) := by
  funext s
  simp only [homComp_apply, koszul_apply, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show (sgn i s : MvPolynomial d R) = C (sgn i s) by simp [sgn], mul_assoc, mul_assoc,
    homogeneousComponent_C_mul]
  congr 1
  ext α
  rw [coeff_homogeneousComponent, coeff_X_mul', coeff_X_mul', coeff_homogeneousComponent]
  by_cases hi : i ∈ α.support
  · rw [ite_eq_left hi, ite_eq_left hi]
    have := degree_sub_single_add_one (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi))
    by_cases hd : α.degree = j + 1
    · rw [ite_eq_left hd, ite_eq_left (by omega)]
    · rw [ite_eq_right hd, ite_eq_right (by omega)]
  · rw [ite_eq_right hi]; split_ifs <;> rfl

theorem homComp_zero_koszul (ω : PolyForm R d) : homComp 0 (koszul ω) = 0 := by
  funext s
  ext α
  rw [homComp_apply, coeff_homogeneousComponent, Pi.zero_apply]
  split_ifs with hα
  · obtain rfl : α = 0 := (Finsupp.degree_eq_zero_iff α).1 hα
    rw [koszul_apply, coeff_sum]
    refine sum_eq_zero fun j _ => ?_
    rw [show (sgn j s : MvPolynomial d R) = C (sgn j s) by simp [sgn], mul_assoc, coeff_C_mul,
      coeff_X_mul']
    simp
  · rfl

end Order

/-! ### Forms with coefficients in a submodule -/

variable (R) in
/-- The `k`-forms all of whose coefficients lie in the submodule `S`. -/
def coeffForm (k : ℕ) (S : Submodule R (MvPolynomial d R)) : Submodule R (PolyForm R d) where
  carrier := {ω | IsDeg k ω ∧ ∀ s, ω s ∈ S}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => S.zero_mem⟩
  add_mem' {ω η} hω hη := ⟨fun s hs => by simp [hω.1 s hs, hη.1 s hs],
    fun s => S.add_mem (hω.2 s) (hη.2 s)⟩
  smul_mem' c ω hω := ⟨fun s hs => by simp [hω.1 s hs], fun s => S.smul_mem c (hω.2 s)⟩

/-- `k`-forms with coefficients in `S`, as families of elements of `S` on the `k`-subsets. -/
def coeffFormEquiv (k : ℕ) (S : Submodule R (MvPolynomial d R)) :
    coeffForm R k S ≃ₗ[R] ({s : Finset d // #s = k} → S) where
  toFun ω := fun s => ⟨ω.1 s.1, ω.2.2 s.1⟩
  invFun c := ⟨fun s => if h : #s = k then (c ⟨s, h⟩ : MvPolynomial d R) else 0,
    fun s hs => by simp [hs], fun s => by by_cases h : #s = k <;> simp [h]⟩
  left_inv ω := by
    refine Subtype.ext (funext fun s => ?_)
    simp only
    split_ifs with h
    · rfl
    · exact (ω.2.1 s h).symm
  right_inv c := funext fun s => Subtype.ext (by simp [s.2])
  map_add' ω η := rfl
  map_smul' c ω := rfl

theorem homForm_eq_coeffForm (r k : ℕ) :
    homForm R d r k = coeffForm R k (homogeneousSubmodule d R r) := rfl

theorem polyForm_eq_coeffForm (r k : ℕ) :
    polyForm R d r k = coeffForm R k (restrictTotalDegree d R r) := by
  ext ω
  exact and_congr_right fun _ => forall_congr' fun s =>
    (mem_restrictTotalDegree d (m := r) (ω s)).symm

/-! ### Direct sums -/

theorem eq_zero_of_mem_homForm_of_mem_polyForm {r k k' : ℕ} {ω : PolyForm R d}
    (h : ω ∈ homForm R d (r + 1) k) (h' : ω ∈ polyForm R d r k') : ω = 0 := by
  have h1 := homComp_of_mem_homForm h (r + 1)
  rw [homComp_eq_zero_of_mem_polyForm h' (Nat.lt_succ_self r)] at h1
  simpa using h1.symm

theorem disjoint_polyForm_homForm (r k : ℕ) :
    Disjoint (polyForm R d r k) (homForm R d (r + 1) k) := by
  rw [Submodule.disjoint_def]
  exact fun ω h h' => eq_zero_of_mem_homForm_of_mem_polyForm h' h

theorem polyForm_sup_homForm (r k : ℕ) :
    polyForm R d r k ⊔ homForm R d (r + 1) k = polyForm R d (r + 1) k := by
  refine le_antisymm (sup_le (polyForm_mono (Nat.le_succ r) k) (homForm_le_polyForm _ _))
    fun ω h => ?_
  rw [← sum_homComp h, Finset.sum_range_succ]
  refine Submodule.add_mem_sup (Submodule.sum_mem _ fun j hj => ?_)
    (homComp_mem_homForm h.1 (r + 1))
  exact polyForm_mono (by simp at hj; omega) k
    (homForm_le_polyForm _ _ (homComp_mem_homForm h.1 j))

theorem polyForm_zero_eq_homForm (k : ℕ) : polyForm R d 0 k = homForm R d 0 k := by
  refine le_antisymm (fun ω h => ?_) (homForm_le_polyForm _ _)
  rw [← sum_homComp h, Finset.sum_range_one]
  exact homComp_mem_homForm h.1 0

section Order

variable [LinearOrder d] [Fintype d]

theorem map_koszul_homForm_le_succ (r k : ℕ) :
    (homForm R d r (k + 1)).map (koszulₗ R d) ≤ homForm R d (r + 1) k :=
  map_koszul_homForm_le (r := r + 1) (Nat.le_add_left 1 r) k

theorem disjoint_polyForm_map_koszul (r k : ℕ) :
    Disjoint (polyForm R d r k) ((homForm R d r (k + 1)).map (koszulₗ R d)) :=
  (disjoint_polyForm_homForm r k).mono_right (map_koszul_homForm_le_succ r k)

theorem polyFormMinus_succ_eq_sup_map_koszul_polyForm (r k : ℕ) :
    polyFormMinus R d (r + 1) k =
      polyForm R d r k ⊔ (polyForm R d r (k + 1)).map (koszulₗ R d) := by
  refine le_antisymm (sup_le_sup_left (Submodule.map_mono (homForm_le_polyForm r _)) _)
    (sup_le le_sup_left ?_)
  rintro _ ⟨ω, hω, rfl⟩
  rw [← sum_homComp hω, map_sum, Finset.sum_range_succ]
  refine Submodule.add_mem_sup (Submodule.sum_mem _ fun j hj => ?_)
    ⟨_, homComp_mem_homForm hω.1 r, rfl⟩
  have := koszul_mem_homForm (homComp_mem_homForm hω.1 j)
  exact polyForm_mono (by simp at hj; omega) k (homForm_le_polyForm _ _ this)

end Order

/-! ### Binomial identities -/

theorem choose_mul_add_choose (n r k : ℕ) :
    n.choose k * (n + r).choose r = (r + n).choose (r + k) * (r + k).choose k := by
  have h := Nat.choose_mul (n := r + n) (k := r + k) (s := r) (Nat.le_add_right r k)
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h
  rw [← @Nat.choose_symm_add r k, h, add_comm n r, mul_comm]

/-! ### Dimensions (over a field) -/

section Field

variable {K : Type*} [Field K] [LinearOrder d] [Fintype d]

instance (k : ℕ) (S : Submodule K (MvPolynomial d K)) [FiniteDimensional K S] :
    FiniteDimensional K (coeffForm K k S) :=
  LinearEquiv.finiteDimensional (coeffFormEquiv k S).symm

omit [LinearOrder d] in
theorem finrank_coeffForm (k : ℕ) (S : Submodule K (MvPolynomial d K)) [FiniteDimensional K S] :
    Module.finrank K (coeffForm K k S) = (Fintype.card d).choose k * Module.finrank K S := by
  rw [(coeffFormEquiv k S).finrank_eq, Module.finrank_pi_fintype, sum_const, card_univ,
    Fintype.card_finset_len, smul_eq_mul]

instance (r k : ℕ) : FiniteDimensional K (polyForm K d r k) := by
  rw [polyForm_eq_coeffForm]; infer_instance

instance (r k : ℕ) : FiniteDimensional K (homForm K d r k) :=
  Submodule.finiteDimensional_of_le (homForm_le_polyForm r k)

theorem polyFormMinus_le_polyForm_succ (r k : ℕ) :
    polyFormMinus K d r k ≤ polyForm K d (r + 1) k :=
  (polyFormMinus_le_polyForm r k).trans (polyForm_mono (Nat.le_succ r) k)

instance (r k : ℕ) : FiniteDimensional K (polyFormMinus K d r k) :=
  Submodule.finiteDimensional_of_le (polyFormMinus_le_polyForm_succ r k)

theorem finrank_homogeneousSubmodule (r : ℕ) :
    Module.finrank K (homogeneousSubmodule d K r) = (Fintype.card d + r - 1).choose r := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank K (restrictSupport K {f : d →₀ ℕ | f.degree = r}) = _
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K {f : d →₀ ℕ | f.degree = r})]
  have hset : {f : d →₀ ℕ | f.degree = r} = ↑((univ : Finset d).finsuppAntidiag r) := by
    ext f
    simp [Finsupp.degree_eq_sum]
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    card_finsuppAntidiag_nat_eq_choose, card_univ]

theorem finrank_homForm (r k : ℕ) :
    Module.finrank K (homForm K d r k) =
      (Fintype.card d).choose k * (Fintype.card d + r - 1).choose r := by
  rw [homForm_eq_coeffForm]
  have : FiniteDimensional K (homogeneousSubmodule d K r) :=
    Module.Finite.iff_fg.2 (homogeneousSubmodule_fg d K r)
  rw [finrank_coeffForm, finrank_homogeneousSubmodule]

theorem finrank_polyForm_eq_mul (r k : ℕ) :
    Module.finrank K (polyForm K d r k) =
      (Fintype.card d).choose k * (Fintype.card d + r).choose r := by
  induction r with
  | zero => rw [polyForm_zero_eq_homForm, finrank_homForm]; simp
  | succ r ih =>
    have h := Submodule.finrank_sup_add_finrank_inf_eq (polyForm K d r k) (homForm K d (r + 1) k)
    rw [polyForm_sup_homForm, (disjoint_polyForm_homForm r k).eq_bot, finrank_bot, add_zero,
      ih, finrank_homForm, show Fintype.card d + (r + 1) - 1 = Fintype.card d + r by omega] at h
    rw [h, ← mul_add, ← Nat.choose_succ_succ']
    rfl

/-- `dim P_rΛᵏ(Kⁿ) = (r + n choose r + k) (r + k choose k)` ([AFW2006], §3; [AFW2010], §5.1). -/
theorem finrank_polyForm (r k : ℕ) :
    Module.finrank K (polyForm K d r k) =
      (r + Fintype.card d).choose (r + k) * (r + k).choose k := by
  rw [finrank_polyForm_eq_mul, choose_mul_add_choose]

end Field

/-! ### The Koszul decompositions and their dimensions (characteristic zero) -/

theorem finrank_map_of_injOn {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (V : Submodule K M)
    (hf : ∀ x ∈ V, f x = 0 → x = 0) : Module.finrank K (V.map f) = Module.finrank K V := by
  have hinj : Function.Injective (f ∘ₗ V.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hf x x.2 hx)
  have hr : LinearMap.range (f ∘ₗ V.subtype) = V.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hr, ← (LinearEquiv.ofInjective _ hinj).finrank_eq]

theorem extDeriv_homComp_zero [LinearOrder d] (ω : PolyForm R d) :
    extDeriv (homComp 0 ω) = 0 := by
  funext s
  simp [extDeriv_apply, homComp_apply]

theorem extDeriv_homComp_eq_zero [LinearOrder d] {ω : PolyForm R d} (hω : extDeriv ω = 0)
    (j : ℕ) : extDeriv (homComp j ω) = 0 := by
  rcases j with _ | j
  · exact extDeriv_homComp_zero ω
  · rw [← homComp_extDeriv, hω]
    funext s; simp [homComp_apply]

section CharZero

variable {K : Type*} [Field K] [CharZero K] [LinearOrder d] [Fintype d]

theorem extDeriv_smul_koszul_of_mem {r k : ℕ} (hrk : 0 < r + k) {ω : PolyForm K d}
    (h : ω ∈ homForm K d r k) (hd : extDeriv ω = 0) :
    extDeriv (((r + k : ℕ) : K)⁻¹ • koszul ω) = ω := by
  conv_rhs => rw [eq_koszul_add_extDeriv hrk h]
  rw [hd, smul_zero, koszul_zero, zero_add]

theorem mem_polyForm_of_mem_polyFormMinus_of_extDeriv_eq_zero {r k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ polyFormMinus K d r k) (hd : extDeriv ω = 0) : ω ∈ polyForm K d (r - 1) k := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [(Submodule.mem_bot K).1 h]; exact zero_mem _
  rw [polyFormMinus_eq_sup hr] at h
  obtain ⟨a, ha, b, ⟨c, hc, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
  change a + koszul c ∈ _
  change extDeriv (a + koszul c) = 0 at hd
  -- the degree-`r` part `κ c` of `ω` is closed
  have hκc : koszul c ∈ homForm K d r k := map_koszul_homForm_le hr k ⟨c, hc, rfl⟩
  have hdκ : extDeriv (koszul c) = 0 := by
    have h1 := congrArg (homComp (r - 1)) hd
    rw [extDeriv_add, homComp_add, homComp_extDeriv, homComp_extDeriv, Nat.sub_add_cancel hr,
      homComp_eq_zero_of_mem_polyForm ha (Nat.sub_lt hr Nat.one_pos),
      homComp_of_mem_homForm hκc] at h1
    simpa using h1
  have hzero : koszul c = 0 := by
    have := extDeriv_koszul_add_koszul_extDeriv_of_mem hκc
    rw [hdκ, koszul_koszul, extDeriv_zero, koszul_zero, add_zero] at this
    exact (smul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 (by omega))
  rw [hzero, add_zero]
  exact ha

/-! #### Exactness of the polynomial complexes -/

/-- Exactness of the polynomial de Rham complex ([AFW2010], §5.1.4, (71)). -/
theorem exists_extDeriv_eq_of_mem_polyForm {r k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ polyForm K d r (k + 1)) (hd : extDeriv ω = 0) :
    ∃ η ∈ polyForm K d (r + 1) k, extDeriv η = ω := by
  refine ⟨∑ j ∈ range (r + 1), ((j + (k + 1) : ℕ) : K)⁻¹ • koszul (homComp j ω),
    Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_, ?_⟩
  · have := koszul_mem_homForm (homComp_mem_homForm h.1 j)
    exact polyForm_mono (by simp at hj; omega) k (homForm_le_polyForm _ _ this)
  · rw [← extDerivₗ_apply, map_sum]
    conv_rhs => rw [← sum_homComp h]
    refine sum_congr rfl fun j _ => ?_
    exact extDeriv_smul_koszul_of_mem (by omega) (homComp_mem_homForm h.1 j)
      (extDeriv_homComp_eq_zero hd j)

theorem mem_polyForm_zero_of_extDeriv_eq_zero {ω : PolyForm K d} (h0 : IsDeg 0 ω)
    (hd : extDeriv ω = 0) : ω ∈ polyForm K d 0 0 := by
  refine (homComp_mem_polyForm_iff h0).2 fun j hj => ?_
  have hm := homComp_mem_homForm h0 j
  have := extDeriv_koszul_add_koszul_extDeriv_of_mem hm
  rw [IsDeg.koszul_eq_zero hm.1, extDeriv_zero, extDeriv_homComp_eq_zero hd j, koszul_zero,
    add_zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 (by omega))

theorem polyFormMinus_zero_right {r : ℕ} (hr : 1 ≤ r) :
    polyFormMinus K d r 0 = polyForm K d r 0 := by
  refine le_antisymm (polyFormMinus_le_polyForm r 0) fun ω h => ?_
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [← sum_homComp h, Finset.sum_range_succ]
  refine Submodule.add_mem_sup (Submodule.sum_mem _ fun j hj => ?_) ?_
  · exact polyForm_mono (by simp at hj; omega) 0
      (homForm_le_polyForm _ _ (homComp_mem_homForm h.1 j))
  · have hm := homComp_mem_homForm h.1 (r + 1)
    rw [eq_koszul_add_extDeriv (by omega) hm, IsDeg.koszul_eq_zero hm.1, smul_zero, extDeriv_zero,
      add_zero]
    exact ⟨_, Submodule.smul_mem _ _ (extDeriv_mem_homForm hm), rfl⟩

theorem polyFormMinus_succ_eq_inf_comap (r k : ℕ) :
    polyFormMinus K d (r + 1) k =
      polyForm K d (r + 1) k ⊓ (polyForm K d (r + 1) (k - 1)).comap (koszulₗ K d) := by
  refine le_antisymm (le_inf (polyFormMinus_le_polyForm _ k) fun ω h => ?_) ?_
  · cases k with
    | zero =>
      have h0 : IsDeg 0 ω := (polyFormMinus_le_polyForm _ 0 h).1
      change koszulₗ K d ω ∈ polyForm K d (r + 1) (0 - 1)
      rw [koszulₗ_apply, IsDeg.koszul_eq_zero h0]
      exact Submodule.zero_mem _
    | succ k => exact koszul_mem_polyForm_of_mem_polyFormMinus_succ h
  · rintro ω ⟨h, hκ⟩
    have hlow : ∑ j ∈ range (r + 1), homComp j ω ∈ polyForm K d r k :=
      Submodule.sum_mem _ fun j hj => polyForm_mono (by simp at hj; omega) k
        (homForm_le_polyForm _ _ (homComp_mem_homForm h.1 j))
    have htop := homComp_mem_homForm h.1 (r + 1)
    have hsum := sum_homComp h
    rw [Finset.sum_range_succ] at hsum
    have hκtop : koszul (homComp (r + 1) ω) = 0 := by
      refine eq_zero_of_mem_homForm_of_mem_polyForm (r := r + 1) (k' := k - 1)
        (koszul_mem_homForm htop) ?_
      rw [eq_sub_of_add_eq' hsum]
      change koszulₗ K d (ω - ∑ j ∈ range (r + 1), homComp j ω) ∈ polyForm K d (r + 1) (k - 1)
      rw [map_sub]
      exact Submodule.sub_mem _ hκ (koszul_mem_polyForm hlow)
    obtain ⟨η, hη, he⟩ := exists_koszul_eq_of_koszul_eq_zero (by omega) htop hκtop
    rw [← hsum]
    exact Submodule.add_mem_sup hlow ⟨η, by simpa using hη, he⟩

/-- Exactness of the trimmed complex ([AFW2010], §5.1.4, (72)). -/
theorem exists_extDeriv_eq_of_mem_polyFormMinus {r k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ polyFormMinus K d r (k + 1)) (hd : extDeriv ω = 0) :
    ∃ η ∈ polyFormMinus K d r k, extDeriv η = ω := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨0, zero_mem _, by rw [extDeriv_zero, (Submodule.mem_bot K).1 h]⟩
  have h' := mem_polyForm_of_mem_polyFormMinus_of_extDeriv_eq_zero h hd
  rw [polyFormMinus_eq_sup hr]
  refine ⟨∑ j ∈ range (r - 1 + 1), ((j + (k + 1) : ℕ) : K)⁻¹ • koszul (homComp j ω),
    Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_, ?_⟩
  · have hj' : j ≤ r - 1 := by simp at hj; omega
    have hm := homComp_mem_homForm h'.1 j
    rcases Nat.lt_or_ge j (r - 1) with hlt | hge
    · refine Submodule.mem_sup_left (polyForm_mono (show j + 1 ≤ r - 1 by omega) k ?_)
      exact homForm_le_polyForm (j + 1) k (by simpa using koszul_mem_homForm hm)
    · have : j = r - 1 := le_antisymm hj' hge
      subst this
      exact Submodule.mem_sup_right ⟨_, hm, rfl⟩
  · rw [← extDerivₗ_apply, map_sum]
    conv_rhs => rw [← sum_homComp h']
    refine sum_congr rfl fun j _ => ?_
    exact extDeriv_smul_koszul_of_mem (by omega) (homComp_mem_homForm h'.1 j)
      (extDeriv_homComp_eq_zero hd j)

/-! #### `P_rΛᵏ = P_r⁻Λᵏ ⊕ d H_{r+1}Λ^{k-1}` -/

theorem map_extDeriv_homForm_one (k : ℕ) :
    (homForm K d 1 k).map (extDerivₗ K d) = homForm K d 0 (k + 1) := by
  refine le_antisymm ?_ fun ω hm => ?_
  · rintro _ ⟨η, hη, rfl⟩
    simpa using extDeriv_mem_homForm hη
  · obtain ⟨η, hη, he⟩ := exists_extDeriv_eq_of_extDeriv_eq_zero (by omega) hm
      (extDeriv_eq_zero_of_mem_polyForm_zero (homForm_le_polyForm _ _ hm))
    exact ⟨η, by simpa using hη, he⟩

theorem polyFormMinus_sup_map_extDeriv (r k : ℕ) :
    polyFormMinus K d r (k + 1) ⊔ (homForm K d (r + 1) k).map (extDerivₗ K d) =
      polyForm K d r (k + 1) := by
  rcases r with _ | r
  · rw [polyFormMinus_zero_left, bot_sup_eq, polyForm_zero_eq_homForm, map_extDeriv_homForm_one]
  refine le_antisymm (sup_le (polyFormMinus_le_polyForm _ _) ?_) fun ω h => ?_
  · rintro _ ⟨η, hη, rfl⟩
    exact homForm_le_polyForm _ _ (by simpa using extDeriv_mem_homForm hη)
  · rw [← sum_homComp h, Finset.sum_range_succ]
    have hm := homComp_mem_homForm h.1 (r + 1)
    rw [eq_koszul_add_extDeriv (by omega) hm, ← add_assoc]
    refine Submodule.add_mem_sup (Submodule.add_mem _ (Submodule.mem_sup_left
      (Submodule.sum_mem _ fun j hj => ?_)) (Submodule.mem_sup_right ⟨_,
        Submodule.smul_mem _ _ (extDeriv_mem_homForm hm), rfl⟩))
      ⟨_, Submodule.smul_mem _ _ (by simpa using koszul_mem_homForm hm), rfl⟩
    exact polyForm_mono (by simp at hj; omega) _
      (homForm_le_polyForm _ _ (homComp_mem_homForm h.1 j))

theorem disjoint_polyFormMinus_map_extDeriv (r k : ℕ) :
    Disjoint (polyFormMinus K d r (k + 1)) ((homForm K d (r + 1) k).map (extDerivₗ K d)) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [polyFormMinus_zero_left]; exact disjoint_bot_left
  rw [Submodule.disjoint_def]
  rintro x hx ⟨β, hβ, rfl⟩
  have hxh : extDeriv β ∈ homForm K d r (k + 1) := by simpa using extDeriv_mem_homForm hβ
  rw [polyFormMinus_eq_sup hr] at hx
  obtain ⟨a, ha, b, ⟨c, hc, rfl⟩, hab⟩ := Submodule.mem_sup.1 hx
  have hκc : koszul c ∈ homForm K d r (k + 1) := map_koszul_homForm_le hr _ ⟨c, hc, rfl⟩
  have h1 := congrArg (homComp r) hab
  change homComp r (a + koszul c) = homComp r (extDeriv β) at h1
  rw [homComp_add, homComp_eq_zero_of_mem_polyForm ha (Nat.sub_lt hr Nat.one_pos),
    homComp_of_mem_homForm hκc, homComp_of_mem_homForm hxh] at h1
  simp only [↓reduceIte, zero_add] at h1
  exact eq_zero_of_eq_koszul_of_eq_extDeriv (by omega) hxh h1.symm rfl

/-! #### Dimensions of `κ H_rΛ^{k+1}`, `d H_{r+1}Λᵏ` and `P_r⁻Λᵏ` -/

theorem map_koszul_homForm_one (s : ℕ) :
    (homForm K d s 1).map (koszulₗ K d) = homForm K d (s + 1) 0 := by
  refine le_antisymm (map_koszul_homForm_le_succ s 0) fun ω hm => ?_
  rw [eq_koszul_add_extDeriv (by omega) hm, IsDeg.koszul_eq_zero hm.1, smul_zero, extDeriv_zero,
    add_zero]
  exact ⟨_, Submodule.smul_mem _ _ (by simpa using extDeriv_mem_homForm hm), rfl⟩

theorem map_extDeriv_homForm_eq (r k : ℕ) :
    (homForm K d (r + 1) k).map (extDerivₗ K d) =
      ((homForm K d r (k + 1)).map (koszulₗ K d)).map (extDerivₗ K d) := by
  refine le_antisymm ?_ (Submodule.map_mono (map_koszul_homForm_le_succ r k))
  rintro _ ⟨ω, hm, rfl⟩
  refine ⟨_, ⟨_, Submodule.smul_mem _ (((r + 1 + k : ℕ) : K)⁻¹)
    (by simpa using extDeriv_mem_homForm hm), rfl⟩, ?_⟩
  conv_rhs => rw [extDerivₗ_apply, eq_koszul_add_extDeriv (by omega) hm, extDeriv_add,
    extDeriv_extDeriv, add_zero]
  rfl

theorem eq_zero_of_extDeriv_eq_zero_of_mem_map_koszul {r k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ (homForm K d r (k + 1)).map (koszulₗ K d)) (hd : extDeriv ω = 0) : ω = 0 := by
  have hm := map_koszul_homForm_le_succ r k h
  obtain ⟨c, -, rfl⟩ := h
  change koszul c ∈ _ at hm
  change extDeriv (koszul c) = 0 at hd
  change koszul c = 0
  have := extDeriv_koszul_add_koszul_extDeriv_of_mem hm
  rw [koszul_koszul, extDeriv_zero, zero_add, hd, koszul_zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 (by omega))

theorem finrank_map_extDeriv_homForm (r k : ℕ) :
    Module.finrank K ((homForm K d (r + 1) k).map (extDerivₗ K d)) =
      Module.finrank K ((homForm K d r (k + 1)).map (koszulₗ K d)) := by
  rw [map_extDeriv_homForm_eq]
  exact finrank_map_of_injOn _ _ fun x hx hd => eq_zero_of_extDeriv_eq_zero_of_mem_map_koszul hx hd

theorem map_koszul_sup_map_extDeriv (r k : ℕ) :
    (homForm K d r (k + 2)).map (koszulₗ K d) ⊔ (homForm K d (r + 2) k).map (extDerivₗ K d) =
      homForm K d (r + 1) (k + 1) := by
  refine le_antisymm (sup_le (map_koszul_homForm_le_succ r (k + 1)) ?_) ?_
  · rintro _ ⟨η, hη, rfl⟩
    simpa using extDeriv_mem_homForm hη
  · have := homForm_le_sup (K := K) (d := d) (r := r + 1) (k := k + 1) (by omega)
    simpa using this

theorem disjoint_map_koszul_map_extDeriv (r k : ℕ) :
    Disjoint ((homForm K d r (k + 2)).map (koszulₗ K d))
      ((homForm K d (r + 2) k).map (extDerivₗ K d)) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨a, ha, rfl⟩ ⟨b, -, hb⟩
  exact eq_zero_of_eq_koszul_of_eq_extDeriv (r := r + 1) (k := k + 1) (by omega)
    (map_koszul_homForm_le_succ r (k + 1) ⟨a, ha, rfl⟩) rfl hb.symm

theorem finrank_homForm_eq_add (r k : ℕ) :
    Module.finrank K (homForm K d (r + 1) (k + 1)) =
      Module.finrank K ((homForm K d r (k + 2)).map (koszulₗ K d)) +
        Module.finrank K ((homForm K d (r + 1) (k + 1)).map (koszulₗ K d)) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    ((homForm K d r (k + 2)).map (koszulₗ K d)) ((homForm K d (r + 2) k).map (extDerivₗ K d))
  rw [map_koszul_sup_map_extDeriv, (disjoint_map_koszul_map_extDeriv r k).eq_bot, finrank_bot,
    add_zero, finrank_map_extDeriv_homForm] at h
  exact h

theorem choose_identity_koszul (n s j : ℕ) :
    n.choose (j + 1) * (n + s).choose (s + 1) =
      (n + s).choose (s + j + 2) * (s + j + 1).choose (j + 1) +
        (n + s + 1).choose (s + j + 2) * (s + j + 1).choose j := by
  have hP := choose_mul_add_choose n s (j + 1)
  have hP' := choose_mul_add_choose n (s + 1) (j + 1)
  have h1 : (n + (s + 1)).choose (s + 1) = (n + s).choose s + (n + s).choose (s + 1) :=
    Nat.choose_succ_succ' (n + s) s
  have h2 : (s + 1 + (j + 1)).choose (j + 1) =
      (s + j + 1).choose j + (s + j + 1).choose (j + 1) := by
    rw [show s + 1 + (j + 1) = s + j + 1 + 1 by omega]; exact Nat.choose_succ_succ' _ _
  have h3 : (s + 1 + n).choose (s + 1 + (j + 1)) =
      (n + s).choose (s + j + 1) + (n + s).choose (s + j + 2) := by
    rw [show s + 1 + n = n + s + 1 by omega, show s + 1 + (j + 1) = s + j + 1 + 1 by omega]
    exact Nat.choose_succ_succ' _ _
  rw [h1, h2, h3] at hP'
  rw [show s + n = n + s by omega, show s + (j + 1) = s + j + 1 by omega] at hP
  have h4 : (n + s + 1).choose (s + j + 2) =
      (n + s).choose (s + j + 1) + (n + s).choose (s + j + 2) := Nat.choose_succ_succ' _ _
  rw [h4]
  zify at hP hP' ⊢
  linear_combination hP' - hP

theorem finrank_map_koszul_homForm (r k : ℕ) :
    Module.finrank K ((homForm K d r (k + 1)).map (koszulₗ K d)) =
      (Fintype.card d + r).choose (r + k + 1) * (r + k).choose k := by
  induction k generalizing r with
  | zero =>
    rw [map_koszul_homForm_one, finrank_homForm]
    simp [show Fintype.card d + (r + 1) - 1 = Fintype.card d + r by omega]
  | succ k ih =>
    have h := finrank_homForm_eq_add (K := K) (d := d) r k
    rw [ih (r + 1), finrank_homForm,
      show Fintype.card d + (r + 1) - 1 = Fintype.card d + r by omega,
      choose_identity_koszul] at h
    rw [show r + (k + 1) + 1 = r + k + 2 by omega, show r + (k + 1) = r + k + 1 by omega,
      show k + 1 + 1 = k + 2 from rfl]
    rw [show r + 1 + k + 1 = r + k + 2 by omega, show r + 1 + k = r + k + 1 by omega,
      show Fintype.card d + (r + 1) = Fintype.card d + r + 1 by omega] at h
    omega

theorem finrank_map_extDeriv_homForm' (r k : ℕ) :
    Module.finrank K ((homForm K d (r + 1) k).map (extDerivₗ K d)) =
      (Fintype.card d + r).choose (r + k + 1) * (r + k).choose k := by
  rw [finrank_map_extDeriv_homForm, finrank_map_koszul_homForm]

/-- `dim P_r⁻Λᵏ(Kⁿ) = (r + n choose r + k) (r + k - 1 choose k)` for `r ≥ 1` ([AFW2006], §3;
[AFW2010], §5.1.3). -/
theorem finrank_polyFormMinus {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    Module.finrank K (polyFormMinus K d r k) =
      (r + Fintype.card d).choose (r + k) * (r + k - 1).choose k := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq (polyForm K d r k)
    ((homForm K d r (k + 1)).map (koszulₗ K d))
  rw [← polyFormMinus_succ, (disjoint_polyForm_map_koszul r k).eq_bot, finrank_bot, add_zero,
    finrank_polyForm, finrank_map_koszul_homForm] at h
  rw [h, show r + 1 + k - 1 = r + k by omega, show r + 1 + Fintype.card d =
    r + Fintype.card d + 1 by omega, show r + 1 + k = r + k + 1 by omega,
    Nat.choose_succ_succ', add_mul, show Fintype.card d + r = r + Fintype.card d by omega]

theorem polyFormMinus_top {r : ℕ} (hr : 1 ≤ r) :
    polyFormMinus K d r (Fintype.card d) = polyForm K d (r - 1) (Fintype.card d) := by
  refine (Submodule.eq_of_le_of_finrank_eq (polyForm_le_polyFormMinus hr _) ?_).symm
  rw [finrank_polyForm, finrank_polyFormMinus hr, Nat.choose_self, Nat.choose_self,
    show r - 1 + Fintype.card d = r + Fintype.card d - 1 by omega]

theorem polyFormMinus_lt_polyForm (r : ℕ) {k : ℕ} (hk : k + 1 ≤ Fintype.card d) :
    polyFormMinus K d r (k + 1) < polyForm K d r (k + 1) := by
  refine lt_of_le_of_ne (polyFormMinus_le_polyForm r _) fun h => ?_
  have hle : (homForm K d (r + 1) k).map (extDerivₗ K d) ≤ polyFormMinus K d r (k + 1) := by
    rw [h, ← polyFormMinus_sup_map_extDeriv r k]
    exact le_sup_right
  have h0 := finrank_map_extDeriv_homForm' (K := K) (d := d) r k
  rw [(disjoint_polyFormMinus_map_extDeriv r k).symm.eq_bot_of_le hle, finrank_bot] at h0
  exact absurd h0.symm (Nat.mul_ne_zero (Nat.choose_pos (by omega)).ne'
    (Nat.choose_pos (by omega)).ne')

omit [CharZero K] [LinearOrder d] in
theorem homogeneousComponent_sum_X_mul_pderiv (m : ℕ) (p : MvPolynomial d K) :
    homogeneousComponent m (∑ j, X j * pderiv j p) = m • homogeneousComponent m p := by
  have hE : ∑ j, X j * pderiv j p =
      ∑ i ∈ range (p.totalDegree + 1), i • homogeneousComponent i p := by
    conv_lhs => rw [← sum_homogeneousComponent p]
    simp_rw [map_sum, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => (homogeneousComponent_isHomogeneous i p).sum_X_mul_pderiv
  simp_rw [hE, map_sum, map_nsmul]
  rw [sum_eq_single m]
  · rw [homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous m p), ite_eq_left rfl]
  · intro i _ hi
    rw [homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous i p),
      ite_eq_right (Ne.symm hi), smul_zero]
  · intro hm
    rw [homogeneousComponent_eq_zero _ p (by simp at hm; omega), map_zero, smul_zero]

theorem eq_zero_of_extDeriv_eq_zero_of_koszul_eq_zero {θ : PolyForm K d}
    (hd : extDeriv θ = 0) (hκ : koszul θ = 0) (h0 : (θ ∅).coeff 0 = 0) : θ = 0 := by
  funext s
  have key := extDeriv_koszul_add_koszul_extDeriv θ s
  rw [hκ, hd, extDeriv_zero, koszul_zero, Pi.zero_apply, add_zero] at key
  rw [Pi.zero_apply, ← sum_homogeneousComponent (θ s)]
  refine sum_eq_zero fun m _ => ?_
  have hm := congrArg (homogeneousComponent m) key
  rw [map_zero, map_add, homogeneousComponent_sum_X_mul_pderiv,
    show (#s : MvPolynomial d K) = C (#s : K) by simp, homogeneousComponent_C_mul,
    ← Nat.cast_smul_eq_nsmul K, smul_eq_C_mul, ← add_mul, ← C_add] at hm
  by_cases hsm : #s + m = 0
  · obtain ⟨hs, rfl⟩ : #s = 0 ∧ m = 0 := by omega
    rw [card_eq_zero.1 hs, homogeneousComponent_zero, h0, C_0]
  · refine (mul_eq_zero.1 hm.symm).resolve_left fun hC => hsm ?_
    exact_mod_cast C_eq_zero.1 hC

theorem koszul_eq_zero_of_extDeriv_koszul_eq_zero {ω : PolyForm K d}
    (h : extDeriv (koszul ω) = 0) : koszul ω = 0 := by
  refine eq_zero_of_extDeriv_eq_zero_of_koszul_eq_zero h (koszul_koszul ω) ?_
  rw [koszul_apply, coeff_sum]
  exact sum_eq_zero fun j _ => by
    rw [mul_comm, ← mul_assoc, coeff_mul_X']
    simp

theorem extDeriv_eq_zero_of_koszul_extDeriv_eq_zero {ω : PolyForm K d}
    (h : koszul (extDeriv ω) = 0) : extDeriv ω = 0 :=
  eq_zero_of_extDeriv_eq_zero_of_koszul_eq_zero (extDeriv_extDeriv ω) h (by simp [extDeriv_apply])

theorem map_koszul_polyForm_sup_map_extDeriv (r k : ℕ) :
    (polyForm K d r (k + 2)).map (koszulₗ K d) ⊔ (polyForm K d (r + 2) k).map (extDerivₗ K d) =
      polyForm K d (r + 1) (k + 1) := by
  refine le_antisymm (sup_le ?_ ?_) fun ω h => ?_
  · rintro _ ⟨η, hη, rfl⟩
    simpa using koszul_mem_polyForm hη
  · rintro _ ⟨η, hη, rfl⟩
    simpa using extDeriv_mem_polyForm hη
  · rw [← sum_homComp h]
    refine Submodule.sum_mem _ fun j hj => ?_
    have hm := homComp_mem_homForm h.1 j
    have hj' : j ≤ r + 1 := by simp at hj; omega
    rw [eq_koszul_add_extDeriv (by omega) hm]
    refine Submodule.add_mem_sup ⟨_, Submodule.smul_mem _ _ ?_, rfl⟩
      ⟨_, Submodule.smul_mem _ _ ?_, rfl⟩
    · exact polyForm_mono (by omega) _ (homForm_le_polyForm _ _ (extDeriv_mem_homForm hm))
    · exact polyForm_mono (by omega) _ (homForm_le_polyForm _ _ (koszul_mem_homForm hm))

theorem disjoint_map_koszul_polyForm_map_extDeriv (r k : ℕ) :
    Disjoint ((polyForm K d r (k + 2)).map (koszulₗ K d))
      ((polyForm K d (r + 2) k).map (extDerivₗ K d)) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨a, ha, rfl⟩ ⟨b, -, hb⟩
  have hdeg : IsDeg (k + 1) (koszul a) := by simpa using (koszul_mem_polyForm ha).1
  refine eq_zero_of_extDeriv_eq_zero_of_koszul_eq_zero ?_ (koszul_koszul a) ?_
  · change extDeriv (koszulₗ K d a) = 0
    rw [← hb, extDerivₗ_apply, extDeriv_extDeriv]
  · rw [show koszulₗ K d a ∅ = 0 from hdeg ∅ (by simp)]
    simp

/-! #### The Koszul complexes -/

theorem eq_zero_of_mem_homForm_zero_of_koszul_eq_zero {k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ homForm K d 0 (k + 1)) (hκ : koszul ω = 0) : ω = 0 := by
  obtain ⟨η, hη, rfl⟩ := exists_koszul_eq_of_koszul_eq_zero (by omega) h hκ
  exact eq_zero_of_mem_homForm_of_mem_polyForm (koszul_mem_homForm hη) (homForm_le_polyForm _ _ h)

/-- Exactness of the polynomial Koszul complex ([AFW2006], §3.2). -/
theorem exists_koszul_eq_of_mem_polyForm {r k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ polyForm K d (r + 1) (k + 1)) (hκ : koszul ω = 0) :
    ∃ η ∈ polyForm K d r (k + 2), koszul η = ω := by
  refine ⟨∑ j ∈ range (r + 2), ((j + (k + 1) : ℕ) : K)⁻¹ • extDeriv (homComp j ω),
    Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_, ?_⟩
  · have := extDeriv_mem_homForm (homComp_mem_homForm h.1 j)
    exact polyForm_mono (by simp at hj; omega) _ (homForm_le_polyForm _ _ this)
  · rw [← koszulₗ_apply, map_sum]
    conv_rhs => rw [← sum_homComp h]
    refine sum_congr rfl fun j _ => ?_
    have hκj : koszul (homComp j ω) = 0 := by rw [← homComp_koszul, hκ, homComp_zero]
    have := extDeriv_koszul_add_koszul_extDeriv_of_mem (homComp_mem_homForm h.1 j)
    rw [hκj, extDeriv_zero, zero_add] at this
    rw [map_smul, koszulₗ_apply, this, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (by omega)),
      one_smul]

theorem map_koszul_polyForm_sup_polyForm_zero (r : ℕ) :
    (polyForm K d r 1).map (koszulₗ K d) ⊔ polyForm K d 0 0 = polyForm K d (r + 1) 0 := by
  refine le_antisymm (sup_le ?_ (polyForm_mono (by omega) 0)) fun ω h => ?_
  · rintro _ ⟨η, hη, rfl⟩
    simpa using koszul_mem_polyForm hη
  · rw [← sum_homComp h, Finset.sum_range_succ']
    refine Submodule.add_mem_sup (Submodule.sum_mem _ fun j hj => ?_)
      (homForm_le_polyForm _ _ (homComp_mem_homForm h.1 0))
    obtain ⟨η, hη, he⟩ := (map_koszul_homForm_one j).ge (homComp_mem_homForm h.1 (j + 1))
    exact ⟨η, polyForm_mono (by simp at hj; omega) 1 (homForm_le_polyForm _ _ hη), he⟩

omit [CharZero K] in
theorem disjoint_map_koszul_polyForm_polyForm_zero (r : ℕ) :
    Disjoint ((polyForm K d r 1).map (koszulₗ K d)) (polyForm K d 0 0) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨η, -, rfl⟩ h
  rw [← sum_homComp h, Finset.sum_range_one, koszulₗ_apply, homComp_zero_koszul]

end CharZero

end Feec.Koszul
