module

public import Feec.Algebra.CubicalForm

/-!
# The serendipity polynomial forms `S_rΛᵏ` of the cube

The second cubical family of [ArnoldAwanou2014], the analogue for cubes of the full polynomial
family `P_rΛᵏ`, is built from the *superlinear degree* of a monomial form,

  `sdeg (x^α dx_s) = |α| - #{j ∉ s | α_j = 1}`,

the degree ignoring the variables which enter linearly and do not enter the alternator
([ArnoldAwanou2014], §2: `sdeg = deg - ldeg`). With `M_rΛᵏ` the span of the monomial `k`-forms of
superlinear degree `≤ r`, the serendipity forms are

  `S_rΛᵏ = P_rΛᵏ + κ M_{r-1}Λ^{k+1} + d κ M_rΛᵏ`.

This is the space `P_rΛᵏ + J_rΛᵏ + d J_{r+1}Λ^{k-1}` of [ArnoldAwanou2014], (17): by
[ArnoldAwanou2014], Prop 3.1, `J_rΛᵏ = κ M_{r-1}Λ^{k+1}` restricted to the polynomial degrees
`≥ r`, and the parts of lower degree, `κ` and `d κ` of forms of `M_{r-1}` and `M_r` of degree
`< r` and `≤ r`, lie in `P_rΛᵏ`. For `k = 0` it is the serendipity space of all polynomials of
superlinear degree `≤ r`.

## Main definitions

* `Feec.Koszul.superlinDeg s α`: the superlinear degree of `x^α dx_s`;
* `Feec.Koszul.supportForm R d k S`: the span of the monomial `k`-forms `x^α dx_s`, `α ∈ S s`;
* `Feec.Koszul.superlinForm R d r k`: `M_rΛᵏ`, the `k`-forms whose coefficient `ω_s` is supported
  on the exponents of superlinear degree `≤ r`;
* `Feec.Koszul.serendipityForm R d r k`: `S_rΛᵏ`.

## Main results

* `extDeriv_mem_superlinForm`, `koszul_mem_superlinForm`: `d M_rΛᵏ ⊆ M_rΛ^{k+1}`,
  `κ M_rΛ^{k+1} ⊆ M_{r+1}Λᵏ` ([ArnoldAwanou2014], Lemma 2.2);
* `extDeriv_mem_serendipityForm`: **`d S_{r+1}Λᵏ ⊆ S_rΛ^{k+1}`**, the subcomplex property
  ([ArnoldAwanou2014], Thm 3.3; `isSubcomplex_serendipityForm`);
* `serendipityForm_mono`: **`S_rΛᵏ ⊆ S_{r+1}Λᵏ`** ([ArnoldAwanou2014], Thm 3.4);
* `superlinForm_le_serendipityForm`, `serendipityForm_le_superlinForm`:
  **`M_{r-1}Λᵏ ⊆ S_rΛᵏ ⊆ M_{r+1}Λᵏ`** (the second inclusion is the degree property,
  [ArnoldAwanou2014], Thm 3.2); `serendipityForm_zero`: **`S_rΛ⁰ = M_rΛ⁰`** (`r ≥ 1`), the
  serendipity space, and `serendipityForm_zero_le_cubeFormMinus`: `P_rΛ⁰ ⊆ S_rΛ⁰ ⊆ Q_rΛ⁰`;
* `cubeTrace_mem_serendipityForm`: **the trace property** `tr_f S_rΛᵏ ⊆ S_rΛᵏ` on every
  coordinate plane `f` ([ArnoldAwanou2014], Thm 3.5), and `image_cubeTrace_serendipityForm`: the
  traces of `S_rΛᵏ` on `f` are exactly the forms of `S_rΛᵏ` living on `f` (fixed by `tr_f`;
  [ArnoldAwanou2014], (27)).

## Implementation notes

Every space is defined by monomial supports, coefficientwise, as `Q_b⁻Λᵏ`
(`Feec.Algebra.CubicalForm`); the forms on a coordinate plane are the forms fixed by its trace
`Feec.Koszul.cubeTrace`. The trace property is proved without induction on the form degree: the
trace commutes with `κ` up to a form of `M_rΛᵏ` (`cubeTrace_koszul_sub_mem_superlinForm`), and
`M_{r-1}Λᵏ ⊆ S_rΛᵏ` by the homotopy formula.

The dimension, `dim S_rΛᵏ = dim M_rΛᵏ`, is in `Feec.Algebra.SerendipityFormDim`. The degrees of
freedom and their unisolvence ([ArnoldAwanou2014], (21), Thm 3.6 (2)) are not formalized, nor the
trimmed serendipity forms `S_r⁻Λᵏ` [GilletteKloefkorn2019].

## References

* [D. N. Arnold, G. Awanou, *Finite element differential forms on cubical meshes*][ArnoldAwanou2014],
  §2 (linear degree, Lemma 2.2), §3 ((17), Prop 3.1, Thms 3.2–3.5)
* [A. Gillette, T. Kloefkorn, *Trimmed serendipity finite element differential forms*][GilletteKloefkorn2019]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.Koszul

open ExteriorFibre

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d] [Fintype d]

/-! ### Superlinear degree -/

/-- The superlinear degree `|α| - #{j ∉ s | α_j = 1}` of the monomial form `x^α dx_s`: the degree
not counting the variables entering linearly outside the alternator. -/
def superlinDeg (s : Finset d) (α : d →₀ ℕ) : ℕ := ∑ j, if j ∉ s ∧ α j = 1 then 0 else α j

/-- The exponents `α` with `x^α dx_s` of superlinear degree `≤ r`. -/
def superlinSupport (r : ℕ) (s : Finset d) : Set (d →₀ ℕ) := {α | superlinDeg s α ≤ r}

/-- A termwise bound with one extra unit at `j`. -/
theorem sum_le_sum_add_one {f g : d → ℕ} (j : d) (h : ∀ i, f i ≤ g i + if i = j then 1 else 0) :
    ∑ i, f i ≤ ∑ i, g i + 1 := by
  calc ∑ i, f i ≤ ∑ i, (g i + if i = j then 1 else 0) := sum_le_sum fun i _ => h i
    _ = ∑ i, g i + 1 := by rw [sum_add_distrib, sum_ite_eq' univ j]; simp

/-- The superlinear degree is at most the degree. -/
theorem superlinDeg_le (s : Finset d) (α : d →₀ ℕ) : superlinDeg s α ≤ α.sum fun _ e => e := by
  rw [Finsupp.sum_fintype _ _ fun _ => rfl]
  exact sum_le_sum fun j _ => by split_ifs <;> omega

/-- `∂ⱼ` (`j ∈ s`, from `dx_{s ∖ j}` to `dx_s`) does not raise the superlinear degree. -/
theorem superlinDeg_sub_single_le {s : Finset d} {j : d} (hj : j ∈ s) (α : d →₀ ℕ) :
    superlinDeg s (α - Finsupp.single j 1) ≤ superlinDeg (s.erase j) α := by
  refine sum_le_sum fun i _ => ?_
  by_cases hi : i = j
  · subst hi; simp [hj]; split_ifs <;> omega
  · simp [hi]

/-- Multiplication by `x_j` (`j ∉ s`, from `dx_{s ∪ j}` to `dx_s`) raises the superlinear degree
by at most one. -/
theorem superlinDeg_add_single_le {s : Finset d} {j : d} (hj : j ∉ s) (α : d →₀ ℕ) :
    superlinDeg s (α + Finsupp.single j 1) ≤ superlinDeg (insert j s) α + 1 := by
  refine sum_le_sum_add_one j fun i => ?_
  by_cases hi : i = j
  · subst hi; simp [hj]; split_ifs <;> omega
  · simp [hi]

omit [CommRing R] in
/-- The substitution `x_j = c` (`f j = some c`) does not raise the superlinear degree, even when
the fixed directions `t ∖ s` are dropped from the alternator. -/
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

section Support

omit [LinearOrder d] [Fintype d]
variable [DecidableEq d]

variable (R d) in
/-- The `k`-forms whose coefficients `ω_s` are supported on `S s`: the span of the monomial forms
`x^α dx_s`, `#s = k`, `α ∈ S s`. -/
def supportForm (k : ℕ) (S : Finset d → Set (d →₀ ℕ)) : Submodule R (PolyForm R d) where
  carrier := {ω | IsDeg k ω ∧ ∀ s, ω s ∈ restrictSupport R (S s)}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => Submodule.zero_mem _⟩
  add_mem' {ω η} hω hη := ⟨fun s hs => by simp [hω.1 s hs, hη.1 s hs],
    fun s => Submodule.add_mem _ (hω.2 s) (hη.2 s)⟩
  smul_mem' c ω hω := ⟨fun s hs => by simp [hω.1 s hs], fun s => Submodule.smul_mem _ c (hω.2 s)⟩

omit [DecidableEq d] in
theorem supportForm_mono {S T : Finset d → Set (d →₀ ℕ)} (h : ∀ s, S s ⊆ T s) (k : ℕ) :
    supportForm R d k S ≤ supportForm R d k T :=
  fun _ hω => ⟨hω.1, fun s => restrictSupport_mono R (h s) (hω.2 s)⟩

/-- The monomial form `x^α dx_s` lies in `supportForm #s S` when `α ∈ S s`. -/
theorem single_monomial_mem_supportForm {S : Finset d → Set (d →₀ ℕ)} {s : Finset d}
    {α : d →₀ ℕ} (hα : α ∈ S s) :
    (Pi.single s (monomial α 1) : PolyForm R d) ∈ supportForm R d #s S := by
  refine ⟨fun t ht => Pi.single_eq_of_ne (fun h => ht (by rw [h])) _, fun t => ?_⟩
  by_cases ht : t = s
  · subst ht; rw [Pi.single_eq_same]
    exact (monomial_mem_restrictSupport R).2 (Or.inl hα)
  · rw [Pi.single_eq_of_ne ht]; exact Submodule.zero_mem _

/-- A form of `supportForm k S` is a combination of its monomial forms: a submodule containing
them contains `supportForm k S`. -/
theorem supportForm_le_of_single [Fintype d] {k : ℕ} {S : Finset d → Set (d →₀ ℕ)}
    {V : Submodule R (PolyForm R d)}
    (h : ∀ s : Finset d, #s = k → ∀ α ∈ S s, (Pi.single s (monomial α 1) : PolyForm R d) ∈ V) :
    supportForm R d k S ≤ V := fun ω hω => by
  rw [← univ_sum_single ω]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : #s = k
  · exact map_mem_of_mem_restrictSupport (LinearMap.single R (fun _ => MvPolynomial d R) s)
      (fun α hα => h s hs α hα) (hω.2 s)
  · rw [hω.1 s hs, Pi.single_zero]; exact Submodule.zero_mem _

end Support

variable (R d) in
/-- `M_rΛᵏ`: the `k`-forms spanned by the monomial forms of superlinear degree `≤ r`.
[ArnoldAwanou2014], Thm 3.2 -/
def superlinForm (r k : ℕ) : Submodule R (PolyForm R d) := supportForm R d k (superlinSupport r)

theorem mem_superlinForm {r k : ℕ} {ω : PolyForm R d} :
    ω ∈ superlinForm R d r k ↔ IsDeg k ω ∧ ∀ s, ω s ∈ restrictSupport R (superlinSupport r s) :=
  Iff.rfl

theorem superlinForm_mono {r r' : ℕ} (h : r ≤ r') (k : ℕ) :
    superlinForm R d r k ≤ superlinForm R d r' k :=
  supportForm_mono (fun s => superlinSupport_mono h s) k

/-- `M_rΛᵏ ⊆ Q_{r+1}⁻Λᵏ`: a monomial form of superlinear degree `≤ r` has degree `≤ r` in the
variables of the alternator and `≤ r + 1` in the others. -/
theorem superlinForm_le_cubeFormMinus (r k : ℕ) :
    superlinForm R d r k ≤ cubeFormMinus R (fun _ => r + 1) k :=
  fun _ hω => ⟨hω.1, fun s => restrictSupport_mono R (s := superlinSupport r s)
    (t := cubeSupport (fun _ => r + 1) s) (fun α hα j => by
      have := (single_le_sum (f := fun i => if i ∉ s ∧ α i = 1 then 0 else α i)
        (fun _ _ => Nat.zero_le _) (mem_univ j)).trans hα
      show α j + _ ≤ r + 1
      by_cases hj : j ∈ s
      · simp only [hj, not_true_eq_false, false_and, ↓reduceIte] at this ⊢; omega
      · by_cases h1 : α j = 1
        · simp [hj, h1]
        · simp only [hj, h1, not_false_eq_true, and_false, ↓reduceIte] at this ⊢; omega)
    (hω.2 s)⟩

instance {K : Type*} [Field K] (r k : ℕ) : FiniteDimensional K (superlinForm K d r k) :=
  Submodule.finiteDimensional_of_le (superlinForm_le_cubeFormMinus r k)

/-- **`P_rΛᵏ ⊆ M_rΛᵏ`**: the superlinear degree is at most the degree. -/
theorem polyForm_le_superlinForm (r k : ℕ) : polyForm R d r k ≤ superlinForm R d r k :=
  fun ω hω => ⟨hω.1, fun s => restrictSupport_mono R (fun α hα => (superlinDeg_le s α).trans hα)
    (show ω s ∈ restrictTotalDegree d R r from (mem_restrictTotalDegree _ _ _).2 (hω.2 s))⟩

/-- **`d M_rΛᵏ ⊆ M_rΛ^{k+1}`**: `d` lowers the degree by one and the linear degree by at most one.
[ArnoldAwanou2014], §2 -/
theorem extDeriv_mem_superlinForm {r k : ℕ} {ω : PolyForm R d} (h : ω ∈ superlinForm R d r k) :
    extDeriv ω ∈ superlinForm R d r (k + 1) :=
  ⟨IsDeg.extDeriv h.1, fun s => Submodule.sum_mem _ fun j hj => sgn_mul_mem j s
    (pderiv_mem_restrictSupport j (fun α hα _ =>
      (superlinDeg_sub_single_le hj α).trans hα) (h.2 _))⟩

omit [LinearOrder d] [Fintype d] in
/-- Multiplication by `x_j` maps `restrictSupport S` into `restrictSupport T` when raising `α_j`
by one maps `S` into `T`. -/
theorem X_mul_mem_restrictSupport {S T : Set (d →₀ ℕ)} (j : d)
    (h : ∀ α ∈ S, α + Finsupp.single j 1 ∈ T) {p : MvPolynomial d R}
    (hp : p ∈ restrictSupport R S) : X j * p ∈ restrictSupport R T :=
  map_mem_of_mem_restrictSupport (LinearMap.mulLeft R (X j)) (fun α hα => by
    rw [LinearMap.mulLeft_apply, X, monomial_mul_monomial, one_mul]
    exact (monomial_mem_restrictSupport R).2 (Or.inl (by rw [add_comm]; exact h α hα))) hp

/-- **`κ M_rΛ^{k+1} ⊆ M_{r+1}Λᵏ`**: `κ` raises the degree by one and does not lower the linear
degree. [ArnoldAwanou2014], Lemma 2.2 -/
theorem koszul_mem_superlinForm {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ superlinForm R d r (k + 1)) : koszul ω ∈ superlinForm R d (r + 1) k := by
  refine ⟨IsDeg.koszul h.1, fun s => Submodule.sum_mem _ fun j hj => ?_⟩
  rw [mul_assoc]
  exact sgn_mul_mem j s (X_mul_mem_restrictSupport j (fun α hα =>
    (superlinDeg_add_single_le (mem_compl.1 hj) α).trans (Nat.add_le_add_right hα 1)) (h.2 _))

variable (R d) in
/-- **The serendipity forms** `S_rΛᵏ = P_rΛᵏ + κ M_{r-1}Λ^{k+1} + d κ M_rΛᵏ`, the space
`P_rΛᵏ + J_rΛᵏ + d J_{r+1}Λ^{k-1}` of [ArnoldAwanou2014], (17). -/
def serendipityForm (r k : ℕ) : Submodule R (PolyForm R d) :=
  polyForm R d r k ⊔ (superlinForm R d (r - 1) (k + 1)).map (koszulₗ R d) ⊔
    ((superlinForm R d r k).map (koszulₗ R d)).map (extDerivₗ R d)

theorem polyForm_le_serendipityForm (r k : ℕ) : polyForm R d r k ≤ serendipityForm R d r k :=
  le_sup_left.trans le_sup_left

theorem koszul_mem_serendipityForm {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ superlinForm R d (r - 1) (k + 1)) : koszul ω ∈ serendipityForm R d r k :=
  Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_map_of_mem h))

theorem extDeriv_koszul_mem_serendipityForm {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ superlinForm R d r k) : extDeriv (koszul ω) ∈ serendipityForm R d r k :=
  Submodule.mem_sup_right (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem h))

/-- Membership in `S_rΛᵏ` by its three summands. -/
theorem serendipityForm_induction {r k : ℕ} {P : PolyForm R d → Prop} (h0 : ∀ ω ∈ polyForm R d r k, P ω)
    (h1 : ∀ ω ∈ superlinForm R d (r - 1) (k + 1), P (koszul ω))
    (h2 : ∀ ω ∈ superlinForm R d r k, P (extDeriv (koszul ω)))
    (hadd : ∀ ω η, P ω → P η → P (ω + η)) {ω : PolyForm R d} (h : ω ∈ serendipityForm R d r k) :
    P ω := by
  obtain ⟨a, ha, c, ⟨γ, hγ, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
  obtain ⟨p, hp, b, ⟨β, hβ, rfl⟩, rfl⟩ := Submodule.mem_sup.1 ha
  obtain ⟨γ, hγ, rfl⟩ := hγ
  exact hadd _ _ (hadd _ _ (h0 p hp) (h1 β hβ)) (h2 γ hγ)

/-- **The degree property** `S_rΛᵏ ⊆ M_{r+1}Λᵏ`: every monomial of a serendipity form has
superlinear degree `≤ r + 1`. [ArnoldAwanou2014], Thm 3.2 -/
theorem serendipityForm_le_superlinForm (r k : ℕ) :
    serendipityForm R d r k ≤ superlinForm R d (r + 1) k := fun ω h =>
  serendipityForm_induction
    (fun _ hω => superlinForm_mono (Nat.le_succ r) k (polyForm_le_superlinForm r k hω))
    (fun _ hω => superlinForm_mono (by omega) k (koszul_mem_superlinForm hω))
    (fun _ hω => by
      cases k with
      | zero => rw [IsDeg.koszul_eq_zero hω.1, extDeriv_zero]; exact Submodule.zero_mem _
      | succ k => exact extDeriv_mem_superlinForm (koszul_mem_superlinForm hω))
    (fun _ _ => add_mem) h

instance {K : Type*} [Field K] (r k : ℕ) : FiniteDimensional K (serendipityForm K d r k) :=
  Submodule.finiteDimensional_of_le (serendipityForm_le_superlinForm r k)

/-- **The subcomplex property** `d S_{r+1}Λᵏ ⊆ S_rΛ^{k+1}`. [ArnoldAwanou2014], Thm 3.3 -/
theorem extDeriv_mem_serendipityForm {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ serendipityForm R d (r + 1) k) : extDeriv ω ∈ serendipityForm R d r (k + 1) :=
  serendipityForm_induction
    (fun _ hω => polyForm_le_serendipityForm r (k + 1) (extDeriv_mem_polyForm hω))
    (fun _ hω => extDeriv_koszul_mem_serendipityForm (by simpa using hω))
    (fun _ _ => by rw [extDeriv_extDeriv]; exact Submodule.zero_mem _)
    (fun ω η hω hη => by rw [extDeriv_add]; exact add_mem hω hη) h

/-- `S_{r+2}Λᵏ → S_{r+1}Λ^{k+1} → S_rΛ^{k+2}` is a subcomplex of the polynomial de Rham complex.
[ArnoldAwanou2014], Thm 3.3 -/
theorem isSubcomplex_serendipityForm (r k : ℕ) :
    IsSubcomplex (serendipityForm R d (r + 2) k) (serendipityForm R d (r + 1) (k + 1))
      (serendipityForm R d r (k + 2)) :=
  ⟨fun _ h => extDeriv_mem_serendipityForm h, fun _ h => extDeriv_mem_serendipityForm h⟩

/-- **The inclusion property** `S_rΛᵏ ⊆ S_{r'}Λᵏ` (`r ≤ r'`). [ArnoldAwanou2014], Thm 3.4 -/
theorem serendipityForm_mono {r r' : ℕ} (h : r ≤ r') (k : ℕ) :
    serendipityForm R d r k ≤ serendipityForm R d r' k :=
  sup_le_sup (sup_le_sup (polyForm_mono h k)
    (Submodule.map_mono (superlinForm_mono (Nat.sub_le_sub_right h 1) _)))
    (Submodule.map_mono (Submodule.map_mono (superlinForm_mono h k)))

/-! ### `0`-forms: the serendipity space -/

/-- `κ (p dx_j) = x_j p`. -/
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

/-- A termwise bound with one unit to spare at `j`. -/
theorem sum_add_one_le {f g : d → ℕ} (j : d) (h : ∀ i, f i + (if i = j then 1 else 0) ≤ g i) :
    ∑ i, f i + 1 ≤ ∑ i, g i := by
  calc ∑ i, f i + 1 = ∑ i, (f i + if i = j then 1 else 0) := by
        rw [sum_add_distrib, sum_ite_eq' univ j]; simp
    _ ≤ ∑ i, g i := sum_le_sum fun i _ => h i

/-- Moving a superlinear variable `x_j` (`α_j ≥ 2`, `j ∈ s`) into the alternator, from
`x^α dx_{s ∖ j}` to `x^{α - e_j} dx_s`, lowers the superlinear degree. -/
theorem superlinDeg_sub_single_add_one {s : Finset d} {α : d →₀ ℕ} {j : d} (hjs : j ∈ s)
    (hj : 2 ≤ α j) : superlinDeg s (α - Finsupp.single j 1) + 1 ≤ superlinDeg (s.erase j) α :=
  sum_add_one_le j fun i => by
    by_cases hi : i = j
    · subst hi; simp [hjs]; split_ifs <;> omega
    · simp [hi]

/-- A monomial form of weight `α_i + [i ∈ s] ≤ 1` in each variable has superlinear degree `0`. -/
theorem superlinDeg_eq_zero {s : Finset d} {α : d →₀ ℕ}
    (h : ∀ i, α i + (if i ∈ s then 1 else 0) ≤ 1) : superlinDeg s α = 0 :=
  sum_eq_zero fun i _ => by have := h i; split_ifs at this ⊢ <;> simp_all; omega

/-- **`S_rΛ⁰ = M_rΛ⁰`** (`r ≥ 1`): the serendipity `0`-forms are the polynomials of superlinear
degree `≤ r`, the serendipity space ([ArnoldAwanou2014], §3; a monomial `x^α` of degree `> r` is
`κ(x^{α - e_j} dx_j)`, `j` superlinear if some is). -/
theorem serendipityForm_zero {r : ℕ} (hr : 1 ≤ r) :
    serendipityForm R d r 0 = superlinForm R d r 0 := by
  refine le_antisymm (fun ω h => serendipityForm_induction
    (fun _ hω => polyForm_le_superlinForm r 0 hω)
    (fun _ hω => by simpa [Nat.sub_add_cancel hr] using koszul_mem_superlinForm hω)
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
    exact koszul_mem_serendipityForm h1
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

/-- **`P_rΛ⁰ ⊆ S_rΛ⁰ ⊆ Q_rΛ⁰`** (`r ≥ 1`): a polynomial of superlinear degree `≤ r` has degree
`≤ r` in each variable. -/
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

/-- `tr_f (x_q p) = x_q tr_f p` in a free direction, `c tr_f p` in a direction fixed at `x_q = c`. -/
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
/-- The substitution does not raise the total degree. -/
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

/-- `tr_f P_rΛᵏ ⊆ P_rΛᵏ`. -/
theorem cubeTrace_mem_polyForm (f : d → Option R) {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ polyForm R d r k) : cubeTrace f ω ∈ polyForm R d r k :=
  ⟨IsDeg.cubeTrace h.1 f, fun s => by
    unfold Koszul.cubeTrace
    split_ifs
    · exact (totalDegree_faceSubst_le f _).trans (h.2 s)
    · simp⟩

/-- `tr_f M_rΛᵏ ⊆ M_rΛᵏ`. -/
theorem cubeTrace_mem_superlinForm (f : d → Option R) {r k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ superlinForm R d r k) : cubeTrace f ω ∈ superlinForm R d r k :=
  ⟨IsDeg.cubeTrace h.1 f, fun s => by
    unfold Koszul.cubeTrace
    split_ifs
    · exact faceSubst_mem_restrictSupport f (fun γ hγ => (superlinDeg_filter_le subset_rfl
        (fun _ hj hj' => absurd hj hj') γ).trans hγ) (h.2 s)
    · exact Submodule.zero_mem _⟩

/-- **The trace commutes with `κ` up to `M_rΛᵏ`**: `tr_f κω - κ tr_f ω ∈ M_rΛᵏ` for
`ω ∈ M_rΛ^{k+1}` (the components `x_q ω_{s ∪ q}`, `q` fixed at `x_q = c`, become `c ω_{s ∪ q}`).
[ArnoldAwanou2014], Thm 3.5 -/
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

/-! ### `M_{r-1}Λᵏ ⊆ S_rΛᵏ` and the trace property -/

variable {K : Type*} [Field K] [CharZero K]

/-- **`M_{r-1}Λᵏ ⊆ S_rΛᵏ`**: by the homotopy formula, a monomial form `μ` of degree `j` is
`(j + k)⁻¹ (κ dμ + d κμ)` with `dμ ∈ M_{r-1}Λ^{k+1}` and `μ ∈ M_rΛᵏ`. -/
theorem superlinForm_le_serendipityForm (r k : ℕ) :
    superlinForm K d (r - 1) k ≤ serendipityForm K d r k := by
  refine supportForm_le_of_single fun s hs α hα => ?_
  set μ : PolyForm K d := Pi.single s (monomial α 1)
  have hμ : μ ∈ superlinForm K d (r - 1) k := hs ▸ single_monomial_mem_supportForm hα
  have hhom : IsHomogeneousForm α.degree μ := fun t => by
    by_cases ht : t = s
    · subst ht; simpa [μ] using isHomogeneous_monomial (1 : K) rfl
    · simpa [μ, Pi.single_eq_of_ne ht] using isHomogeneous_zero _ _ _
  have H := extDeriv_koszul_add_koszul_extDeriv_of_isHomogeneous hhom hμ.1
  rw [Nat.cast_smul_eq_nsmul] at H
  by_cases h0 : α.degree + k = 0
  · -- a constant `0`-form
    refine polyForm_le_serendipityForm r k ⟨hμ.1, fun t => ?_⟩
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
      (extDeriv_koszul_mem_serendipityForm (superlinForm_mono (Nat.sub_le r 1) k hμ))
      (koszul_mem_serendipityForm (extDeriv_mem_superlinForm hμ)))

/-- **The trace property** `tr_f S_rΛᵏ ⊆ S_rΛᵏ` on every coordinate plane
`f = {x_j = c_j : f j = some c_j}`: `tr_f κ M_{r-1}Λ^{k+1} ⊆ κ M_{r-1}Λ^{k+1} + M_{r-1}Λᵏ`,
`tr_f dκ M_rΛᵏ = d tr_f κ M_rΛᵏ ⊆ dκ M_rΛᵏ + d M_rΛ^{k-1}`, and `M_{r-1}Λᵏ ⊆ S_rΛᵏ`,
`d M_rΛ^{k-1} ⊆ d S_{r+1}Λ^{k-1} ⊆ S_rΛᵏ`. [ArnoldAwanou2014], Thm 3.5 -/
theorem cubeTrace_mem_serendipityForm (f : d → Option K) {r k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ serendipityForm K d r k) : cubeTrace f ω ∈ serendipityForm K d r k :=
  serendipityForm_induction
    (fun _ hp => polyForm_le_serendipityForm r k (cubeTrace_mem_polyForm f hp))
    (fun a ha => by
      rw [← sub_add_cancel (cubeTrace f (koszul a)) (koszul (cubeTrace f a))]
      exact add_mem (superlinForm_le_serendipityForm r k
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
        exact add_mem (extDeriv_mem_serendipityForm (superlinForm_le_serendipityForm (r + 1) k
          (by simpa using hρ)))
          (extDeriv_koszul_mem_serendipityForm (cubeTrace_mem_superlinForm f hb)))
    (fun ω η hω hη => by rw [cubeTrace_add]; exact add_mem hω hη) h

/-- **The traces of `S_rΛᵏ` on a coordinate plane `f` are the serendipity forms on `f`**: the
image of `tr_f` is the set of the forms of `S_rΛᵏ` fixed by `tr_f` (which live on `f`: no
`dx_j` and no `x_j` in the fixed directions). [ArnoldAwanou2014], (27) -/
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
