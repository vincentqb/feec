module

public import Feec.Algebra.PolynomialFormDim

/-!
# The tensor-product polynomial forms `Q_r⁻Λᵏ` of the cube

On the cube `[0, 1]ⁿ` the trimmed tensor-product family of [ArnoldBoffiBonizzoni2015] (the
cubical column of the periodic table [ArnoldLogg2014]) is

  `Q_r⁻Λᵏ = Σ_{k₁ + ⋯ + kₙ = k} P_r⁻Λ^{k₁}(I) ⊗ ⋯ ⊗ P_r⁻Λ^{kₙ}(I)`

(a direct sum; only the spanning is formalized), the span of the products of `1`-dimensional
factors in `P_r⁻Λ⁰(I) = P_rΛ⁰(I)` and `P_r⁻Λ¹(I) = P_{r-1}Λ¹(I)`. In coordinates, `ω = Σ_s ω_s dx_s` lies in `Q_r⁻Λᵏ` when every
coefficient `ω_s` has degree at most `r - 1` in the variables `x_j`, `j ∈ s`, and at most `r` in
the others. We allow a degree `b_j` in each direction (`cubeFormMinus R b k`, the isotropic family
being `b = fun _ => r`): the faces of the cube are then the directions with `b_j = 0`
(`Q_0⁻Λ⁰ = ℝ`, `Q_0⁻Λ¹ = 0`).

## Main definitions

* `Feec.Koszul.supportForm R d k S`: the span of the monomial `k`-forms `x^α dx_s`, `α ∈ S s`
  (`finrank_supportForm`: its dimension is the number of these monomials);
* `Feec.Koszul.cubeSupport b s`: the exponents `α` with `α_j + [j ∈ s] ≤ b_j`;
* `Feec.Koszul.cubeFormMinus R b k`: `Q_b⁻Λᵏ`, the `k`-forms whose coefficient `ω_s` is supported
  on `cubeSupport b s`;
* `Feec.Koszul.prodForm ω`: the tensor product `ω₁ ⊗ ⋯ ⊗ ωₙ` of `1`-dimensional polynomial forms
  (`PolyForm R Unit`), `(⊗ⱼ ωⱼ)_s = ∏ⱼ ωⱼ(x_j)_{[j ∈ s]}`;
* `Feec.Koszul.antideriv K j`, `Feec.Koszul.zeroSubst R t`: the antiderivative in `x_j` and the
  substitution `x_j = 0` (`j ∈ t`); `Feec.Koszul.cubeHomotopy`, `Feec.Koszul.cubeProj`: their
  coefficientwise extensions to forms.

## Main results

* `cubeFormMinus_eq_span`: **`Q_b⁻Λᵏ` is the span of the tensor products** of factors in
  `P_{b_j}Λ⁰(I)` and `P_{b_j - 1}Λ¹(I)` with form degrees summing to `k`
  ([ArnoldBoffiBonizzoni2015], §3);
* `extDeriv_mem_cubeFormMinus`: **`d Q_b⁻Λᵏ ⊆ Q_b⁻Λ^{k+1}`** (a subcomplex of the polynomial
  de Rham complex, `isSubcomplex_cubeFormMinus`);
* `finrank_cubeFormMinus`: `dim Q_b⁻Λᵏ = Σ_{#s = k} Πⱼ (b_j + 1 - [j ∈ s])`, and
  `finrank_cubeFormMinus_const`: **`dim Q_r⁻Λᵏ = (n choose k) rᵏ (r + 1)ⁿ⁻ᵏ`**
  ([ArnoldBoffiBonizzoni2015], §3; [ArnoldAwanou2014], §2);
* the homotopy formula `extDeriv_cubeHomotopy_add`: `d hⱼ + hⱼ d = 1 - Pⱼ` for the integration
  `hⱼ` in the direction `x_j` and the restriction `Pⱼ` to the hyperplane `x_j = 0`;
* **polynomial exactness** (characteristic zero): `exists_extDeriv_eq_of_mem_cubeFormMinus`, a
  closed form of `Q_b⁻Λ^{k+1}` is `d η` with `η ∈ Q_b⁻Λᵏ`, and
  `eq_const_of_extDeriv_eq_zero`, a closed `0`-form of `Q_b⁻Λ⁰` is a constant: the cohomology of
  the complex `Q_b⁻Λ` is that of a point.

## Implementation notes

Unlike the Koszul arguments for the simplicial families (`Feec.Algebra.PolynomialFormDim`), the
exactness proof is the classical Poincaré lemma by integration along one coordinate at a time:
the operators `hⱼ` and `Pⱼ` preserve the tensor-product degree bounds direction by direction, so
it works for any multidegree `b`.

The serendipity forms `S_rΛᵏ` [ArnoldAwanou2014] are in `Feec.Algebra.SerendipityForm`; the
trimmed serendipity forms `S_r⁻Λᵏ` [GilletteKloefkorn2019] are not formalized.

## References

* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §3 (the spaces `Q_r⁻Λᵏ`, their dimension and degrees of freedom)
* [D. N. Arnold, G. Awanou, *Finite element differential forms on cubical meshes*][ArnoldAwanou2014],
  §2 (the tensor-product family `Q_r⁻Λᵏ`)
* [A. Gillette, T. Kloefkorn, *Trimmed serendipity finite element differential forms*][GilletteKloefkorn2019]
* [D. N. Arnold, A. Logg, *Periodic table of the finite elements*][ArnoldLogg2014]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3 (the polynomial de Rham complex)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.Koszul

open ExteriorFibre

variable {R : Type*} [CommRing R] {d : Type*}

/-! ### Linear maps on monomial supports -/

/-- A linear map sending the monomials of `S` into `T` maps `restrictSupport S` into `T`. -/
theorem map_mem_of_mem_restrictSupport {M : Type*} [AddCommGroup M] [Module R M]
    {S : Set (d →₀ ℕ)} {T : Submodule R M} (f : MvPolynomial d R →ₗ[R] M)
    (h : ∀ α ∈ S, f (monomial α 1) ∈ T) {p : MvPolynomial d R}
    (hp : p ∈ restrictSupport R S) : f p ∈ T := by
  rw [restrictSupport_eq_span] at hp
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨α, hα, rfl⟩ := hx; exact h α hα
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact T.add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact T.smul_mem c hx

/-- `∂ⱼ` maps `restrictSupport S` into `restrictSupport T` when lowering `α_j ≠ 0` maps `S`
into `T`. -/
theorem pderiv_mem_restrictSupport [DecidableEq d] {S T : Set (d →₀ ℕ)} (j : d)
    (h : ∀ α ∈ S, α j ≠ 0 → α - Finsupp.single j 1 ∈ T) {p : MvPolynomial d R}
    (hp : p ∈ restrictSupport R S) : pderiv j p ∈ restrictSupport R T := by
  refine map_mem_of_mem_restrictSupport (pderiv j).toLinearMap (fun α hα => ?_) hp
  change pderiv j (monomial α 1) ∈ _
  rw [pderiv_monomial]
  by_cases h0 : α j = 0
  · simp [h0]
  · exact (monomial_mem_restrictSupport R).2 (Or.inl (h α hα h0))

/-- Linear maps commute with the signs. -/
theorem map_sgn_mul [LinearOrder d] {A : Type*} [CommRing A] [Algebra R A]
    (f : MvPolynomial d R →ₗ[R] A) (j : d) (s : Finset d) (p : MvPolynomial d R) :
    f (sgn j s * p) = sgn j s * f p := by
  rw [show (sgn j s : MvPolynomial d R) = C (sgn j s) by simp [sgn], ← smul_eq_C_mul, map_smul,
    Algebra.smul_def, show algebraMap R A (sgn j s) = sgn j s by simp [sgn]]

/-- Multiplying by a sign stays in a submodule. -/
theorem sgn_mul_mem [LinearOrder d] {M : Submodule R (MvPolynomial d R)} (j : d) (s : Finset d)
    {p : MvPolynomial d R} (hp : p ∈ M) : sgn j s * p ∈ M := by
  rw [show (sgn j s : MvPolynomial d R) = C (sgn j s) by simp [sgn], ← smul_eq_C_mul]
  exact M.smul_mem _ hp

/-! ### Monomial spaces of forms -/

section Support

variable (R d) in
/-- The `k`-forms whose coefficients `ω_s` are supported on `S s`: the span of the monomial forms
`x^α dx_s`, `#s = k`, `α ∈ S s`. -/
def supportForm (k : ℕ) (S : Finset d → Set (d →₀ ℕ)) : Submodule R (PolyForm R d) where
  carrier := {ω | IsDeg k ω ∧ ∀ s, ω s ∈ restrictSupport R (S s)}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => Submodule.zero_mem _⟩
  add_mem' {ω η} hω hη := ⟨fun s hs => by simp [hω.1 s hs, hη.1 s hs],
    fun s => Submodule.add_mem _ (hω.2 s) (hη.2 s)⟩
  smul_mem' c ω hω := ⟨fun s hs => by simp [hω.1 s hs], fun s => Submodule.smul_mem _ c (hω.2 s)⟩

theorem supportForm_mono {S T : Finset d → Set (d →₀ ℕ)} (h : ∀ s, S s ⊆ T s) (k : ℕ) :
    supportForm R d k S ≤ supportForm R d k T :=
  fun _ hω => ⟨hω.1, fun s => restrictSupport_mono R (h s) (hω.2 s)⟩

/-- The monomial form `x^α dx_s` lies in `supportForm #s S` when `α ∈ S s`. -/
theorem single_monomial_mem_supportForm [DecidableEq d] {S : Finset d → Set (d →₀ ℕ)}
    {s : Finset d} {α : d →₀ ℕ} (hα : α ∈ S s) :
    (Pi.single s (monomial α 1) : PolyForm R d) ∈ supportForm R d #s S := by
  refine ⟨fun t ht => Pi.single_eq_of_ne (fun h => ht (by rw [h])) _, fun t => ?_⟩
  by_cases ht : t = s
  · subst ht; rw [Pi.single_eq_same]
    exact (monomial_mem_restrictSupport R).2 (Or.inl hα)
  · rw [Pi.single_eq_of_ne ht]; exact Submodule.zero_mem _

/-- A form of `supportForm k S` is a combination of its monomial forms: a submodule containing
them contains `supportForm k S`. -/
theorem supportForm_le_of_single [DecidableEq d] [Fintype d] {k : ℕ}
    {S : Finset d → Set (d →₀ ℕ)} {V : Submodule R (PolyForm R d)}
    (h : ∀ s : Finset d, #s = k → ∀ α ∈ S s, (Pi.single s (monomial α 1) : PolyForm R d) ∈ V) :
    supportForm R d k S ≤ V := fun ω hω => by
  rw [← univ_sum_single ω]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : #s = k
  · exact map_mem_of_mem_restrictSupport (LinearMap.single R (fun _ => MvPolynomial d R) s)
      (fun α hα => h s hs α hα) (hω.2 s)
  · rw [hω.1 s hs, Pi.single_zero]; exact Submodule.zero_mem _

variable (R) in
/-- A form of `supportForm k S` is the family of its coefficients on the `k`-subsets. -/
def supportFormEquiv (k : ℕ) (S : Finset d → Set (d →₀ ℕ)) :
    supportForm R d k S ≃ₗ[R] ((s : {s : Finset d // #s = k}) → restrictSupport R (S s.1)) where
  toFun ω := fun s => ⟨ω.1 s.1, ω.2.2 s.1⟩
  invFun c := ⟨fun s => if h : #s = k then (c ⟨s, h⟩ : MvPolynomial d R) else 0,
    fun s hs => by simp [hs], fun s => by
      by_cases h : #s = k
      · simp only [h, ↓reduceDIte]; exact (c ⟨s, h⟩).2
      · simp only [h, ↓reduceDIte]; exact Submodule.zero_mem _⟩
  left_inv ω := by
    refine Subtype.ext (funext fun s => ?_)
    simp only
    split_ifs with h
    · rfl
    · exact (ω.2.1 s h).symm
  right_inv c := funext fun s => Subtype.ext (by simp [s.2])
  map_add' ω η := rfl
  map_smul' c ω := rfl

/-- **The dimension of a monomial space** is the number of its monomial forms:
`dim supportForm k S = Σ_{#s = k} #(S s)`. -/
theorem finrank_supportForm {K : Type*} [Field K] [Fintype d] {k : ℕ}
    {S : Finset d → Set (d →₀ ℕ)} (hS : ∀ s, (S s).Finite) :
    Module.finrank K (supportForm K d k S) = ∑ s ∈ powersetCard k univ, Nat.card (S s) := by
  have : ∀ s : {s : Finset d // #s = k}, Module.Finite K (restrictSupport K (S s.1)) :=
    fun s => haveI := (hS s.1).to_subtype; Module.Finite.of_basis (basisRestrictSupport K _)
  rw [(supportFormEquiv K k S).finrank_eq, Module.finrank_pi_fintype]
  simp_rw [fun s : {s : Finset d // #s = k} =>
    Module.finrank_eq_nat_card_basis (basisRestrictSupport K (S s.1))]
  exact (Finset.sum_subtype (powersetCard k univ) (fun s => by simp [mem_powersetCard])
    (fun s => Nat.card (S s))).symm

end Support

/-! ### The spaces -/

section Spaces

variable [LinearOrder d]

/-- The exponents `α` with `α_j + [j ∈ s] ≤ b_j` for all `j`: degree `≤ b_j - 1` in the
variables `x_j` of `dx_s`, `≤ b_j` in the others. -/
def cubeSupport (b : d → ℕ) (s : Finset d) : Set (d →₀ ℕ) :=
  {α | ∀ j, α j + (if j ∈ s then 1 else 0) ≤ b j}

/-- Lowering `j ∈ s` to a face exponent `v ≤ α_j + 1` stays in the support of `s ∖ j`. -/
theorem update_mem_cubeSupport_erase {b : d → ℕ} {s : Finset d} {α : d →₀ ℕ}
    (hα : α ∈ cubeSupport b s) {j : d} (hj : j ∈ s) {v : ℕ} (hv : v ≤ α j + 1) :
    α.update j v ∈ cubeSupport b (s.erase j) := fun l => by
  have := hα l
  by_cases hl : l = j
  · subst hl; simp only [hj, ↓reduceIte] at this; simp [Finsupp.update_apply]; omega
  · simpa [Finsupp.update_apply, hl] using this

variable (R) in
/-- `Q_b⁻Λᵏ`: the `k`-forms whose coefficient `ω_s` has degree `≤ b_j - [j ∈ s]` in each
variable `x_j`; for `b = fun _ => r` the trimmed tensor-product space `Q_r⁻Λᵏ` of the cube.
[ArnoldBoffiBonizzoni2015], §3 -/
def cubeFormMinus (b : d → ℕ) (k : ℕ) : Submodule R (PolyForm R d) :=
  supportForm R d k (cubeSupport b)

theorem mem_cubeFormMinus {b : d → ℕ} {k : ℕ} {ω : PolyForm R d} :
    ω ∈ cubeFormMinus R b k ↔ IsDeg k ω ∧ ∀ s, ω s ∈ restrictSupport R (cubeSupport b s) :=
  Iff.rfl

/-- **`Q_b⁻Λᵏ ⊆ P_{Σ b}Λᵏ`**: a coefficient of degree `≤ b_j` in each variable `x_j` has total
degree `≤ Σⱼ b_j`. -/
theorem cubeFormMinus_le_polyForm [Fintype d] (b : d → ℕ) (k : ℕ) :
    cubeFormMinus R b k ≤ polyForm R d (∑ j, b j) k := fun ω hω =>
  ⟨hω.1, fun s => Finset.sup_le fun α hα => by
    have hα' : α ∈ cubeSupport b s := (mem_restrictSupport_iff R).1 (hω.2 s) hα
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    exact sum_le_sum fun j _ => (Nat.le_add_right _ _).trans (hα' j)⟩

/-- **`d Q_b⁻Λᵏ ⊆ Q_b⁻Λ^{k+1}`**: `∂ⱼ` lowers the degree in `x_j` exactly where `dx_j` is added.
[ArnoldBoffiBonizzoni2015], §3 -/
theorem extDeriv_mem_cubeFormMinus {b : d → ℕ} {k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ cubeFormMinus R b k) : extDeriv ω ∈ cubeFormMinus R b (k + 1) := by
  refine ⟨IsDeg.extDeriv h.1, fun s => Submodule.sum_mem _ fun j hj => sgn_mul_mem j s
    (pderiv_mem_restrictSupport j (fun α hα h0 l => ?_) (h.2 _))⟩
  have := hα l
  by_cases hl : l = j
  · subst hl
    simp only [mem_erase, ne_eq, not_true_eq_false, false_and, ↓reduceIte, add_zero] at this
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same, hj, ↓reduceIte]
    omega
  · simp only [mem_erase, hl, ne_eq, not_false_eq_true, true_and] at this
    simpa [Finsupp.single_apply, Ne.symm hl] using this

/-- `Q_b⁻Λᵏ → Q_b⁻Λ^{k+1} → Q_b⁻Λ^{k+2}` is a subcomplex of the polynomial de Rham complex. -/
theorem isSubcomplex_cubeFormMinus (b : d → ℕ) (k : ℕ) :
    IsSubcomplex (cubeFormMinus R b k) (cubeFormMinus R b (k + 1)) (cubeFormMinus R b (k + 2)) :=
  ⟨fun _ h => extDeriv_mem_cubeFormMinus h, fun _ h => extDeriv_mem_cubeFormMinus h⟩

end Spaces

/-! ### Dimension -/

section Dim

variable [LinearOrder d]

/-- The exponents of `cubeSupport b s` are the tuples `α_j < b_j + 1 - [j ∈ s]`. -/
def cubeSupportEquiv [Fintype d] (b : d → ℕ) (s : Finset d) :
    cubeSupport b s ≃ ((j : d) → Fin (b j + 1 - if j ∈ s then 1 else 0)) where
  toFun α j := ⟨α.1 j, by have := α.2 j; split_ifs at this ⊢ <;> omega⟩
  invFun x := ⟨Finsupp.equivFunOnFinite.symm fun j => (x j : ℕ), fun j => by
    have := (x j).2
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    split_ifs at this ⊢ <;> omega⟩
  left_inv α := Subtype.ext (Finsupp.ext fun j => by simp)
  right_inv x := funext fun j => Fin.ext (by simp)

instance [Fintype d] (b : d → ℕ) (s : Finset d) : Fintype (cubeSupport b s) :=
  Fintype.ofEquiv _ (cubeSupportEquiv b s).symm

instance [Fintype d] (b : d → ℕ) (s : Finset d) :
    Module.Finite R (restrictSupport R (cubeSupport b s)) :=
  Module.Finite.of_basis (basisRestrictSupport R _)

variable (R) in
/-- A form of `Q_b⁻Λᵏ` is the family of its coefficients on the `k`-subsets. -/
def cubeFormMinusEquiv (b : d → ℕ) (k : ℕ) :
    cubeFormMinus R b k ≃ₗ[R]
      ((s : {s : Finset d // #s = k}) → restrictSupport R (cubeSupport b s.1)) :=
  supportFormEquiv R k (cubeSupport b)

variable {K : Type*} [Field K] [Fintype d]

instance (b : d → ℕ) (k : ℕ) : FiniteDimensional K (cubeFormMinus K b k) :=
  LinearEquiv.finiteDimensional (cubeFormMinusEquiv K b k).symm

theorem finrank_restrictSupport_cubeSupport (b : d → ℕ) (s : Finset d) :
    Module.finrank K (restrictSupport K (cubeSupport b s)) =
      ∏ j, (b j + 1 - if j ∈ s then 1 else 0) := by
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K _),
    Nat.card_congr (cubeSupportEquiv b s), Nat.card_eq_fintype_card, Fintype.card_pi]
  simp

/-- **`dim Q_b⁻Λᵏ = Σ_{#s = k} Πⱼ (b_j + 1 - [j ∈ s])`**. [ArnoldBoffiBonizzoni2015], §3 -/
theorem finrank_cubeFormMinus (b : d → ℕ) (k : ℕ) :
    Module.finrank K (cubeFormMinus K b k) =
      ∑ s ∈ powersetCard k univ, ∏ j, (b j + 1 - if j ∈ s then 1 else 0) := by
  rw [(cubeFormMinusEquiv K b k).finrank_eq, Module.finrank_pi_fintype]
  simp_rw [finrank_restrictSupport_cubeSupport]
  exact (Finset.sum_subtype (powersetCard k univ) (fun s => by simp [mem_powersetCard])
    (fun s => ∏ j, (b j + 1 - if j ∈ s then 1 else 0))).symm

/-- **`dim Q_r⁻Λᵏ = (n choose k) rᵏ (r + 1)ⁿ⁻ᵏ`** on the `n`-cube. [ArnoldBoffiBonizzoni2015], §3;
[ArnoldAwanou2014], §2 -/
theorem finrank_cubeFormMinus_const (r k : ℕ) :
    Module.finrank K (cubeFormMinus K (fun _ : d => r) k) =
      (Fintype.card d).choose k * (r ^ k * (r + 1) ^ (Fintype.card d - k)) := by
  rw [finrank_cubeFormMinus, ← card_univ (α := d), ← card_powersetCard, ← smul_eq_mul,
    ← sum_const]
  refine sum_congr rfl fun s hs => ?_
  rw [mem_powersetCard] at hs
  have : ∀ j, (r + 1 - if j ∈ s then 1 else 0) = if j ∈ s then r else r + 1 := fun j => by
    split_ifs <;> omega
  simp_rw [this, prod_ite, prod_const, filter_mem_eq_inter, univ_inter, hs.2]
  rw [show ({x | x ∉ s} : Finset d) = sᶜ by ext; simp, card_compl, hs.2, card_univ]

end Dim

/-! ### Traces on coordinate planes -/

section Trace

variable [Fintype d]

/-- The weight `∏_{f j = some c} c^{γ_j}` of the substitution `x_j = c` (`f j = some c`). -/
def faceWeight (f : d → Option R) (γ : d →₀ ℕ) : R := ∏ j, (f j).elim 1 fun c => c ^ γ j

/-- The substitution `x_j = c` in the directions with `f j = some c`:
`x^γ ↦ (∏_{f j = some c} c^{γ_j}) x^{γ'}`, `γ'` the free part of `γ`. -/
def faceSubst (f : d → Option R) : MvPolynomial d R →ₗ[R] MvPolynomial d R :=
  (basisMonomials d R).constr R fun γ =>
    monomial (γ.filter fun j => (f j).isNone) (faceWeight f γ)

theorem faceSubst_monomial (f : d → Option R) (γ : d →₀ ℕ) (a : R) :
    faceSubst f (monomial γ a) =
      monomial (γ.filter fun j => (f j).isNone) (a * faceWeight f γ) := by
  rw [show monomial γ a = a • (basisMonomials d R) γ by simp [smul_monomial], map_smul,
    faceSubst, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

theorem faceSubst_none (p : MvPolynomial d R) :
    faceSubst (fun _ : d => (none : Option R)) p = p := by
  have : faceSubst (fun _ : d => (none : Option R)) = LinearMap.id :=
    (basisMonomials d R).ext fun γ => by
      have : γ.filter (fun _ => True) = γ := Finsupp.ext fun j => by simp
      simp [faceSubst_monomial, faceWeight, this]
  rw [this, LinearMap.id_apply]

/-- Successive substitutions: `x_j = c` from `g`, then from `f` in the remaining directions. -/
theorem faceSubst_faceSubst (f g : d → Option R) (p : MvPolynomial d R) :
    faceSubst f (faceSubst g p) = faceSubst (fun j => (g j).or (f j)) p := by
  have : faceSubst f ∘ₗ faceSubst g = faceSubst (fun j => (g j).or (f j)) :=
    (basisMonomials d R).ext fun γ => by
      simp only [coe_basisMonomials, LinearMap.coe_comp, Function.comp_apply, faceSubst_monomial,
        one_mul]
      refine congrArg₂ (fun a c => monomial a c) ?_ ?_
      · refine Finsupp.ext fun j => ?_
        simp only [Finsupp.filter_apply]
        cases g j <;> cases f j <;> simp
      · simp only [faceWeight, ← prod_mul_distrib]
        refine prod_congr rfl fun j _ => ?_
        simp only [Finsupp.filter_apply]
        cases g j <;> cases f j <;> simp
  exact LinearMap.congr_fun this p

/-- `∂_l` commutes with the substitution in the other directions. -/
theorem pderiv_faceSubst [DecidableEq d] {f : d → Option R} {l : d} (hl : f l = none)
    (p : MvPolynomial d R) : pderiv l (faceSubst f p) = faceSubst f (pderiv l p) := by
  have : (pderiv l).toLinearMap ∘ₗ faceSubst f = faceSubst f ∘ₗ (pderiv l).toLinearMap :=
    (basisMonomials d R).ext fun γ => by
      simp only [coe_basisMonomials, LinearMap.coe_comp, Function.comp_apply, faceSubst_monomial,
        Derivation.coeFn_coe, pderiv_monomial, one_mul]
      refine congrArg₂ (fun a c => monomial a c) ?_ ?_
      · refine Finsupp.ext fun j => ?_
        simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.filter_apply, Finsupp.single_apply]
        by_cases hj : l = j
        · subst hj; simp [hl]
        · simp [hj]
      · have hw : faceWeight f (γ - Finsupp.single l 1) = faceWeight f γ :=
          prod_congr rfl fun j _ => by
            by_cases hj : l = j
            · subst hj; simp [hl]
            · simp [hj]
        simp [hw, hl, mul_comm]
  exact LinearMap.congr_fun this p

/-- `∂_l` kills the polynomials where `x_l` has been substituted. -/
theorem pderiv_faceSubst_of_ne_none {f : d → Option R} {l : d} (hl : f l ≠ none)
    (p : MvPolynomial d R) : pderiv l (faceSubst f p) = 0 := by
  have : (pderiv l).toLinearMap ∘ₗ faceSubst f = 0 :=
    (basisMonomials d R).ext fun γ => by
      simp [faceSubst_monomial, pderiv_monomial, Option.isNone_iff_eq_none, hl]
  exact LinearMap.congr_fun this p

theorem faceSubst_mem_restrictSupport {S T : Set (d →₀ ℕ)} (f : d → Option R)
    (h : ∀ γ ∈ S, γ.filter (fun j => (f j).isNone) ∈ T) {p : MvPolynomial d R}
    (hp : p ∈ restrictSupport R S) : faceSubst f p ∈ restrictSupport R T :=
  map_mem_of_mem_restrictSupport _ (fun γ hγ => by
    rw [faceSubst_monomial]; exact (monomial_mem_restrictSupport R).2 (Or.inl (h γ hγ))) hp

/-- The substitution `x = 0` leaves the constant coefficient. -/
theorem faceSubst_zero (p : MvPolynomial d R) :
    faceSubst (fun _ : d => some (0 : R)) p = C (p.coeff 0) := by
  classical
  have : faceSubst (fun _ : d => some (0 : R)) =
      Algebra.linearMap R (MvPolynomial d R) ∘ₗ lcoeff R 0 :=
    (basisMonomials d R).ext fun γ => by
      simp only [coe_basisMonomials, faceSubst_monomial, LinearMap.coe_comp, Function.comp_apply,
        lcoeff_apply, coeff_monomial, Algebra.linearMap_apply, algebraMap_eq, faceWeight,
        Option.elim_some, Option.isNone_some, one_mul]
      by_cases h : γ = 0
      · subst h; simp [Finsupp.filter_zero]
      · obtain ⟨j, hj⟩ : ∃ j, γ j ≠ 0 := by
          by_contra h'; push Not at h'; exact h (Finsupp.ext h')
        rw [prod_eq_zero (mem_univ j) (zero_pow hj), ite_eq_right h, map_zero, map_zero]
  simpa using LinearMap.congr_fun this p

/-- The substitution `x_j = c` does not change the values on the plane `{x_j = c}`. -/
theorem eval_faceSubst {f : d → Option R} {y : d → R} (hy : ∀ j c, f j = some c → y j = c)
    (p : MvPolynomial d R) : eval y (faceSubst f p) = eval y p := by
  have : (aeval y).toLinearMap ∘ₗ faceSubst f = (aeval y).toLinearMap :=
    (basisMonomials d R).ext fun γ => by
      simp only [coe_basisMonomials, LinearMap.coe_comp, Function.comp_apply, faceSubst_monomial,
        one_mul, AlgHom.toLinearMap_apply, aeval_monomial, Algebra.algebraMap_self,
        RingHom.id_apply, faceWeight, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_one,
        ← prod_mul_distrib]
      refine prod_congr rfl fun j _ => ?_
      cases hf : f j with
      | none => simp [hf]
      | some c => simp [hf, hy j c hf]
  simpa using LinearMap.congr_fun this p

/-- After the substitution, the values only depend on the free coordinates. -/
theorem eval_faceSubst_congr {f : d → Option R} {y y' : d → R} (h : ∀ j, f j = none → y j = y' j)
    (p : MvPolynomial d R) : eval y (faceSubst f p) = eval y' (faceSubst f p) := by
  have : (aeval y).toLinearMap ∘ₗ faceSubst f = (aeval y').toLinearMap ∘ₗ faceSubst f :=
    (basisMonomials d R).ext fun γ => by
      simp only [coe_basisMonomials, LinearMap.coe_comp, Function.comp_apply, faceSubst_monomial,
        one_mul, AlgHom.toLinearMap_apply, aeval_monomial, Algebra.algebraMap_self,
        RingHom.id_apply, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      congr 1
      refine prod_congr rfl fun j _ => ?_
      cases hf : f j with
      | none => simp [hf, h j hf]
      | some c => simp [hf]
  simpa using LinearMap.congr_fun this p

variable [LinearOrder d]

/-- The trace `tr_f` on the coordinate plane `{x_j = c : f j = some c}`: the components `dx_s`
along the free directions, with `x_j = c` substituted. -/
def cubeTrace (f : d → Option R) (ω : PolyForm R d) : PolyForm R d := fun s =>
  if ∀ j ∈ s, (f j).isNone then faceSubst f (ω s) else 0

/-- The degrees `b` in the free directions of `f`, `0` in the others: `Q_{faceDeg b f}⁻Λᵏ` is the
space `Q_b⁻Λᵏ(f)` of the plane `f` (`Q_0⁻Λ⁰ = ℝ`, `Q_0⁻Λ¹ = 0` across it). -/
def faceDeg (b : d → ℕ) (f : d → Option R) (j : d) : ℕ := if (f j).isNone then b j else 0

theorem cubeTrace_none (ω : PolyForm R d) : cubeTrace (fun _ : d => (none : Option R)) ω = ω := by
  funext s; simp [cubeTrace, faceSubst_none]

@[simp] theorem cubeTrace_zero (f : d → Option R) : cubeTrace f (0 : PolyForm R d) = 0 := by
  funext s; simp [cubeTrace]

theorem cubeTrace_add (f : d → Option R) (ω η : PolyForm R d) :
    cubeTrace f (ω + η) = cubeTrace f ω + cubeTrace f η := by
  funext s; simp only [cubeTrace, Pi.add_apply, map_add]; split_ifs <;> simp

theorem cubeTrace_smul (f : d → Option R) (c : R) (ω : PolyForm R d) :
    cubeTrace f (c • ω) = c • cubeTrace f ω := by
  funext s; simp only [cubeTrace, Pi.smul_apply, map_smul]; split_ifs <;> simp

/-- Traces compose: `tr_f ∘ tr_g = tr_{g, then f}`. -/
theorem cubeTrace_cubeTrace (f g : d → Option R) (ω : PolyForm R d) :
    cubeTrace f (cubeTrace g ω) = cubeTrace (fun j => (g j).or (f j)) ω := by
  funext s
  have hiff : (∀ j ∈ s, ((g j).or (f j)).isNone) ↔
      (∀ j ∈ s, (f j).isNone) ∧ ∀ j ∈ s, (g j).isNone := by
    simp only [← forall₂_and]
    exact forall₂_congr fun j _ => by cases g j <;> cases f j <;> simp
  simp only [cubeTrace]
  by_cases hf : ∀ j ∈ s, (f j).isNone
  · by_cases hg : ∀ j ∈ s, (g j).isNone
    · rw [ite_eq_left hf, ite_eq_left hg, ite_eq_left (hiff.2 ⟨hf, hg⟩), faceSubst_faceSubst]
    · rw [ite_eq_left hf, ite_eq_right hg, ite_eq_right (fun h => hg (hiff.1 h).2), map_zero]
  · rw [ite_eq_right hf, ite_eq_right (fun h => hf (hiff.1 h).1)]

/-- **`d` commutes with the traces**: `d tr_f = tr_f d`. -/
theorem extDeriv_cubeTrace (f : d → Option R) (ω : PolyForm R d) :
    extDeriv (cubeTrace f ω) = cubeTrace f (extDeriv ω) := by
  funext s
  simp only [extDeriv_apply, cubeTrace]
  by_cases hs : ∀ j ∈ s, (f j).isNone
  · rw [ite_eq_left hs, map_sum]
    refine sum_congr rfl fun l hl => ?_
    rw [ite_eq_left fun j hj => hs j (mem_of_mem_erase hj), map_sgn_mul,
      pderiv_faceSubst (Option.isNone_iff_eq_none.1 (hs l hl))]
  · rw [ite_eq_right hs]
    refine sum_eq_zero fun l hl => ?_
    split_ifs with h
    · obtain ⟨m, hms, hm⟩ : ∃ m ∈ s, ¬(f m).isNone := by
        by_contra h'; push Not at h'; exact hs h'
      have hml : m = l := by
        by_contra hml; exact hm (h m (mem_erase.2 ⟨hml, hms⟩))
      subst hml
      rw [pderiv_faceSubst_of_ne_none (by simpa [Option.isNone_iff_eq_none] using hm), mul_zero]
    · rw [map_zero, mul_zero]

omit [Fintype d] in
theorem cubeFormMinus_mono {b b' : d → ℕ} (h : ∀ j, b j ≤ b' j) (k : ℕ) :
    cubeFormMinus R b k ≤ cubeFormMinus R b' k :=
  fun _ hω => ⟨hω.1, fun s => restrictSupport_mono R
    (show cubeSupport b s ⊆ cubeSupport b' s from fun _ hα j => (hα j).trans (h j)) (hω.2 s)⟩

omit [CommRing R] [Fintype d] [LinearOrder d] in
theorem faceDeg_le (b : d → ℕ) (f : d → Option R) (j : d) : faceDeg b f j ≤ b j := by
  unfold faceDeg; split_ifs <;> omega

/-- **The trace property**: `tr_f Q_b⁻Λᵏ ⊆ Q_b⁻Λᵏ(f)`. [ArnoldBoffiBonizzoni2015], §3 -/
theorem cubeTrace_mem {b : d → ℕ} {k : ℕ} {ω : PolyForm R d} (h : ω ∈ cubeFormMinus R b k)
    (f : d → Option R) : cubeTrace f ω ∈ cubeFormMinus R (faceDeg b f) k := by
  refine ⟨fun s hs => by simp [cubeTrace, h.1 s hs], fun s => ?_⟩
  unfold cubeTrace
  split_ifs with hs
  · refine faceSubst_mem_restrictSupport f (fun γ hγ j => ?_) (h.2 s)
    have := hγ j
    simp only [Finsupp.filter_apply, faceDeg]
    by_cases hj : (f j).isNone
    · simp only [hj, ↓reduceIte]; exact this
    · simp only [hj, Bool.false_eq_true, ↓reduceIte, zero_add, nonpos_iff_eq_zero,
        ite_eq_right_iff, one_ne_zero, imp_false]
      exact fun hjs => hj (hs j hjs)
  · exact Submodule.zero_mem _

/-- A form of `Q_b⁻Λᵏ(f)` is its own trace. -/
theorem cubeTrace_eq_self {b : d → ℕ} {f : d → Option R} {k : ℕ} {ω : PolyForm R d}
    (h : ω ∈ cubeFormMinus R (faceDeg b f) k) : cubeTrace f ω = ω := by
  funext s
  -- the coefficients are supported on exponents vanishing in the fixed directions
  have hsupp : ∀ γ ∈ cubeSupport (faceDeg b f) s, ∀ j, ¬(f j).isNone → γ j = 0 ∧ j ∉ s :=
    fun γ hγ j hj => by
      have := hγ j
      have h0 : faceDeg b f j = 0 := by simp [faceDeg, hj]
      rw [h0] at this
      exact ⟨by split_ifs at this <;> omega, fun hjs => by simp [hjs] at this⟩
  have hfix : ∀ p ∈ restrictSupport R (cubeSupport (faceDeg b f) s), faceSubst f p = p := by
    intro p hp
    rw [restrictSupport_eq_span] at hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨γ, hγ, rfl⟩ := hx
      rw [faceSubst_monomial, one_mul]
      refine congrArg₂ (fun a c => monomial a c) ?_ ?_
      · refine Finsupp.ext fun j => ?_
        simp only [Finsupp.filter_apply]
        split_ifs with hj
        · rfl
        · exact ((hsupp γ hγ j hj).1).symm
      · refine prod_eq_one fun j _ => ?_
        cases hj : f j with
        | none => rfl
        | some c =>
          simp [(hsupp γ hγ j (by simp [hj])).1]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  unfold cubeTrace
  split_ifs with hs
  · exact hfix _ (h.2 s)
  · push Not at hs
    obtain ⟨j, hjs, hj⟩ := hs
    -- a component along a fixed direction vanishes
    refine (support_eq_empty.1 (eq_empty_of_forall_notMem fun γ hγ => ?_)).symm
    exact (hsupp γ (h.2 s hγ) j (by simpa using hj)).2 hjs

/-- **`tr_f Q_b⁻Λᵏ = Q_b⁻Λᵏ(f)`**: the traces of `Q_b⁻Λᵏ` on a coordinate plane are the forms of
the same family on the plane. [ArnoldBoffiBonizzoni2015], §3 -/
theorem image_cubeTrace (b : d → ℕ) (f : d → Option R) (k : ℕ) :
    cubeTrace f '' (cubeFormMinus R b k : Set (PolyForm R d)) =
      cubeFormMinus R (faceDeg b f) k := by
  ext θ
  refine ⟨?_, fun hθ => ⟨θ, cubeFormMinus_mono (faceDeg_le b f) k hθ, cubeTrace_eq_self hθ⟩⟩
  rintro ⟨ω, hω, rfl⟩
  exact cubeTrace_mem hω f

end Trace

/-! ### The Poincaré homotopy along one coordinate -/

section Homotopy

variable {K : Type*} [Field K]

variable (K) in
/-- The antiderivative `x^α ↦ x^{α + e_j} / (α_j + 1)` in the variable `x_j`. -/
def antideriv (j : d) : MvPolynomial d K →ₗ[K] MvPolynomial d K :=
  (basisMonomials d K).constr K fun α => monomial (α + Finsupp.single j 1) ((α j + 1 : K)⁻¹)

theorem antideriv_monomial (j : d) (α : d →₀ ℕ) (c : K) :
    antideriv K j (monomial α c) = monomial (α + Finsupp.single j 1) (c * (α j + 1 : K)⁻¹) := by
  rw [show monomial α c = c • (basisMonomials d K) α by simp [smul_monomial], map_smul,
    antideriv, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

/-- `∂ⱼ Iⱼ = 1`. -/
theorem pderiv_antideriv [CharZero K] [DecidableEq d] (j : d) (p : MvPolynomial d K) :
    pderiv j (antideriv K j p) = p := by
  have : (pderiv j).toLinearMap ∘ₗ antideriv K j = LinearMap.id :=
    (basisMonomials d K).ext fun α => by
      simp only [coe_basisMonomials, LinearMap.coe_comp, Function.comp_apply, antideriv_monomial,
        Derivation.coeFn_coe, pderiv_monomial, LinearMap.id_apply, Finsupp.coe_add, Pi.add_apply,
        Finsupp.single_eq_same, add_tsub_cancel_right, one_mul]
      congr 1
      push_cast
      exact inv_mul_cancel₀ (Nat.cast_add_one_ne_zero _)
  exact LinearMap.congr_fun this p

/-- `∂_l Iⱼ = Iⱼ ∂_l` for `l ≠ j`. -/
theorem pderiv_antideriv_of_ne [DecidableEq d] {l j : d} (hlj : l ≠ j) (p : MvPolynomial d K) :
    pderiv l (antideriv K j p) = antideriv K j (pderiv l p) := by
  have : (pderiv l).toLinearMap ∘ₗ antideriv K j = antideriv K j ∘ₗ (pderiv l).toLinearMap :=
    (basisMonomials d K).ext fun α => by
      simp only [coe_basisMonomials, LinearMap.coe_comp, Function.comp_apply, antideriv_monomial,
        Derivation.coeFn_coe, pderiv_monomial, one_mul]
      have he : α + Finsupp.single j 1 - Finsupp.single l 1 =
          α - Finsupp.single l 1 + Finsupp.single j 1 := by
        refine Finsupp.ext fun i => ?_
        simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
          Finsupp.single_apply]
        split_ifs <;> (try subst_vars) <;> first | omega | exact absurd rfl hlj
      rw [he]
      congr 1
      simp [hlj, Ne.symm hlj, mul_comm]
  exact LinearMap.congr_fun this p

theorem antideriv_mem_restrictSupport {S T : Set (d →₀ ℕ)} (j : d)
    (h : ∀ α ∈ S, α + Finsupp.single j 1 ∈ T) {p : MvPolynomial d K}
    (hp : p ∈ restrictSupport K S) : antideriv K j p ∈ restrictSupport K T :=
  map_mem_of_mem_restrictSupport _ (fun α hα => by
    rw [antideriv_monomial]; exact (monomial_mem_restrictSupport K).2 (Or.inl (h α hα))) hp

/-- The coordinate plane `{x_j = 0 : j ∈ t}`. -/
def zeroFace [DecidableEq d] (t : Finset d) : d → Option K := fun j =>
  if j ∈ t then some 0 else none

/-- `Iⱼ ∂ⱼ = 1 - (x_j = 0)`. -/
theorem antideriv_pderiv [Fintype d] [CharZero K] [DecidableEq d] (j : d) (p : MvPolynomial d K) :
    antideriv K j (pderiv j p) = p - faceSubst (zeroFace {j}) p := by
  have : antideriv K j ∘ₗ (pderiv j).toLinearMap = LinearMap.id - faceSubst (zeroFace {j}) :=
    (basisMonomials d K).ext fun α => by
      have hw : faceWeight (zeroFace (K := K) {j}) α = 0 ^ α j := by
        rw [faceWeight, prod_eq_single j (fun i _ hij => by simp [zeroFace, hij]) (by simp)]
        simp [zeroFace]
      simp only [coe_basisMonomials, LinearMap.coe_comp, Function.comp_apply, Derivation.coeFn_coe,
        pderiv_monomial, one_mul, antideriv_monomial, LinearMap.sub_apply, LinearMap.id_apply,
        faceSubst_monomial, hw]
      by_cases h : α j = 0
      · have hf : α.filter (fun i => zeroFace (K := K) {j} i = none) = α :=
          Finsupp.ext fun i => by
            by_cases hi : i = j
            · subst hi; simp [Finsupp.filter_apply, h]
            · simp [zeroFace, hi]
        simp [h, hf]
      · rw [zero_pow h, monomial_zero, sub_zero]
        have h1 : 1 ≤ α j := Nat.one_le_iff_ne_zero.2 h
        rw [tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h1)]
        congr 1
        simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
        rw [show ((α j - 1 : ℕ) : K) + 1 = α j by rw [Nat.cast_sub h1]; ring]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 h)
  exact LinearMap.congr_fun this p

variable [LinearOrder d]

/-- The integration `hⱼ` along `x_j` from the plane `x_j = 0`:
`(hⱼ ω)_s = ε(j, s) Iⱼ ω_{s ∪ j}` for `j ∉ s` (contraction with `∂ⱼ`, then antiderivative). -/
def cubeHomotopy (j : d) (ω : PolyForm K d) : PolyForm K d := fun s =>
  if j ∈ s then 0 else sgn j s * antideriv K j (ω (insert j s))

@[simp] theorem cubeHomotopy_zero (j : d) : cubeHomotopy j (0 : PolyForm K d) = 0 := by
  funext s; simp [cubeHomotopy]

theorem zeroFace_empty : zeroFace (K := K) (∅ : Finset d) = fun _ => none := by
  funext j; simp [zeroFace]

theorem zeroFace_insert (j : d) (t : Finset d) :
    (fun i => (zeroFace (K := K) t i).or (zeroFace {j} i)) = zeroFace (insert j t) := by
  funext i
  by_cases hi : i ∈ t
  · simp [zeroFace, hi]
  · by_cases hij : i = j
    · subst hij; simp [zeroFace, hi]
    · simp [zeroFace, hi, hij]

theorem cubeHomotopy_mem {b : d → ℕ} {k : ℕ} {ω : PolyForm K d} (h : ω ∈ cubeFormMinus K b k)
    (j : d) : cubeHomotopy j ω ∈ cubeFormMinus K b (k - 1) := by
  refine ⟨fun s hs => ?_, fun s => ?_⟩
  · unfold cubeHomotopy
    split_ifs with hj
    · rfl
    · rw [h.1 _ (by rw [card_insert_of_notMem hj]; omega), map_zero, mul_zero]
  · unfold cubeHomotopy
    split_ifs with hj
    · exact Submodule.zero_mem _
    · refine sgn_mul_mem j s (antideriv_mem_restrictSupport j (fun α hα l => ?_) (h.2 _))
      have := hα l
      by_cases hl : l = j
      · subst hl; simp_all
      · simp_all

variable [Fintype d]

theorem zeroFace_univ : zeroFace (K := K) (univ : Finset d) = fun _ => some 0 := by
  funext j; simp [zeroFace]

/-- **The homotopy formula** along `x_j`: `d hⱼ + hⱼ d = 1 - tr_{x_j = 0}`. -/
theorem extDeriv_cubeHomotopy_add [CharZero K] (j : d) (ω : PolyForm K d) :
    extDeriv (cubeHomotopy j ω) + cubeHomotopy j (extDeriv ω) =
      ω - cubeTrace (zeroFace {j}) ω := by
  funext s
  have hfree : (∀ i ∈ s, (zeroFace (K := K) {j} i).isNone) ↔ j ∉ s := by
    simp only [zeroFace, mem_singleton]
    exact ⟨fun h hj => by simpa using h j hj, fun h i hi => by simp [show i ≠ j by grind]⟩
  simp only [Pi.add_apply, Pi.sub_apply, extDeriv_apply, cubeHomotopy, cubeTrace, hfree]
  by_cases hj : j ∈ s
  · rw [ite_eq_left hj, ite_eq_right (not_not.2 hj), add_zero, sub_zero, sum_eq_single j]
    · rw [ite_eq_right (by simp), pderiv_sgn_mul, ← mul_assoc, sgn_erase_self, sgn_mul_self,
        one_mul, insert_erase hj, pderiv_antideriv]
    · intro l _ hlj
      rw [ite_eq_left (mem_erase.2 ⟨Ne.symm hlj, hj⟩), map_zero, mul_zero]
    · exact fun h => absurd hj h
  · rw [ite_eq_right hj, ite_eq_left hj, sum_insert hj, erase_insert hj, map_add, map_sgn_mul,
      antideriv_pderiv, map_sum, mul_add, ← mul_assoc, sgn_insert_self, sgn_mul_self, one_mul]
    have hcross : ∑ l ∈ s, sgn l s * pderiv l (if j ∈ s.erase l then 0 else
        sgn j (s.erase l) * antideriv K j (ω (insert j (s.erase l)))) +
        sgn j s * ∑ l ∈ s, antideriv K j (sgn l (insert j s) *
          pderiv l (ω ((insert j s).erase l))) = 0 := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_eq_zero fun l hl => ?_
      have hlj : l ≠ j := fun h => hj (h ▸ hl)
      rw [ite_eq_right (fun h => hj (mem_of_mem_erase h)), pderiv_sgn_mul,
        pderiv_antideriv_of_ne hlj, map_sgn_mul, erase_insert_of_ne (Ne.symm hlj), sgn_erase hl,
        sgn_insert hj]
      have := ite_lt_add_ite_lt (R := MvPolynomial d K) hlj
      linear_combination (sgn l s * sgn j s *
        antideriv K j (pderiv l (ω (insert j (s.erase l))))) * this
    linear_combination hcross

/-- The telescoped homotopy: a closed `ω ∈ Q_b⁻Λᵏ` differs from its trace on `{x_j = 0 : j ∈ t}`
by `d η`, `η ∈ Q_b⁻Λ^{k-1}`. -/
theorem exists_sub_cubeTrace_eq_extDeriv [CharZero K] {b : d → ℕ} {k : ℕ} {ω : PolyForm K d}
    (h : ω ∈ cubeFormMinus K b k) (hd : extDeriv ω = 0) (t : Finset d) :
    ∃ η ∈ cubeFormMinus K b (k - 1), ω - cubeTrace (zeroFace t) ω = extDeriv η := by
  induction t using Finset.induction_on with
  | empty => exact ⟨0, Submodule.zero_mem _, by
      rw [zeroFace_empty, cubeTrace_none, sub_self, extDeriv_zero]⟩
  | insert j t _ ih =>
    obtain ⟨η, hη, he⟩ := ih
    have hmem : cubeTrace (zeroFace t) ω ∈ cubeFormMinus K b k :=
      cubeFormMinus_mono (faceDeg_le b _) k (cubeTrace_mem h _)
    refine ⟨η + cubeHomotopy j (cubeTrace (zeroFace t) ω),
      Submodule.add_mem _ hη (cubeHomotopy_mem hmem j), ?_⟩
    have H := extDeriv_cubeHomotopy_add j (cubeTrace (zeroFace t) ω)
    rw [extDeriv_cubeTrace, hd, cubeTrace_zero, cubeHomotopy_zero, add_zero,
      cubeTrace_cubeTrace, zeroFace_insert] at H
    rw [extDeriv_add, ← he, H]
    abel

/-- The trace on the vertex `0`. -/
theorem cubeTrace_zeroFace_univ (ω : PolyForm K d) :
    cubeTrace (zeroFace univ) ω =
      (Pi.single (∅ : Finset d) (C ((ω ∅).coeff 0)) : PolyForm K d) := by
  funext s
  simp only [cubeTrace, zeroFace_univ, Option.isNone_some, Bool.false_eq_true, imp_false,
    faceSubst_zero]
  by_cases hs : s = ∅
  · subst hs; simp
  · rw [ite_eq_right fun h => hs (eq_empty_of_forall_notMem h), Pi.single_eq_of_ne hs]

/-- **Polynomial exactness of `Q_b⁻Λ`**: a closed form of `Q_b⁻Λ^{k+1}` is `d η` with
`η ∈ Q_b⁻Λᵏ`. [ArnoldBoffiBonizzoni2015], §3 -/
theorem exists_extDeriv_eq_of_mem_cubeFormMinus [CharZero K] {b : d → ℕ} {k : ℕ}
    {ω : PolyForm K d} (h : ω ∈ cubeFormMinus K b (k + 1)) (hd : extDeriv ω = 0) :
    ∃ η ∈ cubeFormMinus K b k, extDeriv η = ω := by
  obtain ⟨η, hη, he⟩ := exists_sub_cubeTrace_eq_extDeriv h hd univ
  rw [cubeTrace_zeroFace_univ, h.1 ∅ (by simp)] at he
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero,
    Pi.single_zero, sub_zero] at he
  exact ⟨η, hη, he.symm⟩

/-- **The cohomology in degree `0` is the constants**: a closed `0`-form of `Q_b⁻Λ⁰` is
constant. -/
theorem eq_const_of_extDeriv_eq_zero [CharZero K] {b : d → ℕ} {ω : PolyForm K d}
    (h : ω ∈ cubeFormMinus K b 0) (hd : extDeriv ω = 0) :
    ω = (Pi.single (∅ : Finset d) (C ((ω ∅).coeff 0)) : PolyForm K d) := by
  obtain ⟨η, hη, he⟩ := exists_sub_cubeTrace_eq_extDeriv h hd univ
  have h0 : ω - cubeTrace (zeroFace univ) ω = 0 := by
    funext s
    by_cases hs : #s = 0
    · rw [he]; exact IsDeg.extDeriv hη.1 s (by omega)
    · simp [cubeTrace, h.1 s hs]
  rw [sub_eq_zero, cubeTrace_zeroFace_univ] at h0
  exact h0

end Homotopy

/-! ### Tensor products of `1`-dimensional forms -/

section Tensor

variable [LinearOrder d]

/-- A polynomial in `x_j` alone has degree `≤ deg q` in `x_j` and `0` in the other variables. -/
theorem degreeOf_rename_le (q : MvPolynomial Unit R) (i j : d) :
    degreeOf i (rename (fun _ => j) q) ≤ if i = j then q.totalDegree else 0 := by
  have hinj : Function.Injective (fun _ : Unit => j) := fun _ _ _ => rfl
  refine degreeOf_le_iff.2 fun m hm => ?_
  rw [support_rename_of_injective hinj] at hm
  obtain ⟨n, hn, rfl⟩ := mem_image.1 hm
  split_ifs with h
  · subst h
    rw [Finsupp.mapDomain_apply_of_injective hinj n ()]
    exact le_of_eq_of_le (by simp [Finsupp.sum_fintype]) (le_totalDegree hn)
  · exact (Finsupp.mapDomain_of_notMem_range _ _ (by simpa [eq_comm] using h)).le

/-- Degree bounds in each variable give membership in `restrictSupport (cubeSupport b s)`. -/
theorem mem_restrictSupport_cubeSupport {b : d → ℕ} {s : Finset d} {p : MvPolynomial d R}
    (h : ∀ j, degreeOf j p + (if j ∈ s then 1 else 0) ≤ b j) :
    p ∈ restrictSupport R (cubeSupport b s) := fun α hα j =>
  le_trans (Nat.add_le_add_right (degreeOf_le_iff.1 le_rfl α hα) _) (h j)

variable [Fintype d]

/-- The tensor product `ω₁ ⊗ ⋯ ⊗ ωₙ` of `1`-dimensional polynomial forms `ωⱼ ∈ PolyForm R Unit`,
the factor `ωⱼ` in the variable `x_j`: `(⊗ⱼ ωⱼ)_s = ∏ⱼ ωⱼ(x_j)_{[j ∈ s]}`, `dx_s` being the
increasing product of the `dx_j`. -/
def prodForm (ω : d → PolyForm R Unit) : PolyForm R d := fun s =>
  ∏ j, rename (fun _ => j) (ω j (if j ∈ s then univ else ∅))

/-- The monomial form `x^α dx_s` is the tensor product of the `1`-dimensional forms
`x^{α_j} dx^{[j ∈ s]}`. -/
theorem prodForm_monomial (s : Finset d) (α : d →₀ ℕ) :
    prodForm (fun j => Pi.single (if j ∈ s then univ else ∅) (X () ^ α j)) =
      (Pi.single s (monomial α 1) : PolyForm R d) := by
  funext t
  by_cases ht : t = s
  · subst ht
    simp only [prodForm, Pi.single_eq_same, map_pow, rename_X, Pi.single_eq_same]
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  · rw [Pi.single_eq_of_ne ht]
    obtain ⟨j, hj⟩ : ∃ j, ¬(j ∈ t ↔ j ∈ s) := by
      by_contra h
      push Not at h
      exact ht (Finset.ext h)
    refine prod_eq_zero (mem_univ j) ?_
    dsimp only
    rw [Pi.single_eq_of_ne, map_zero]
    by_cases h : j ∈ t <;> simp_all [eq_comm]

/-- **`Q_b⁻Λᵏ` is spanned by tensor products** of `1`-dimensional factors `ωⱼ ∈ P_{b_j}Λ⁰(I)`
or `P_{b_j - 1}Λ¹(I)` (`= P_{b_j}⁻Λ⁰(I)`, `P_{b_j}⁻Λ¹(I)`) whose form degrees `e_j` sum to `k`:
`Q_b⁻Λᵏ = Σ_{Σ e_j = k} ⊗ⱼ P_{b_j}⁻Λ^{e_j}(I)` (`b_j ≥ 1`). [ArnoldBoffiBonizzoni2015], §3 -/
theorem cubeFormMinus_eq_span {b : d → ℕ} (hb : ∀ j, 1 ≤ b j) (k : ℕ) :
    cubeFormMinus R b k = Submodule.span R {θ | ∃ (e : d → ℕ) (ω : d → PolyForm R Unit),
      ∑ j, e j = k ∧ (∀ j, ω j ∈ polyForm R Unit (b j - e j) (e j)) ∧ prodForm ω = θ} := by
  refine le_antisymm (fun ω hω => ?_) (Submodule.span_le.2 ?_)
  · rw [← univ_sum_single ω]
    refine Submodule.sum_mem _ fun s _ => ?_
    by_cases hs : #s = k
    · refine map_mem_of_mem_restrictSupport (LinearMap.single R (fun _ => MvPolynomial d R) s)
        (fun α hα => Submodule.subset_span ?_) (hω.2 s)
      refine ⟨fun j => if j ∈ s then 1 else 0, _, ?_, fun j => ⟨fun u hu => ?_, fun u => ?_⟩,
        prodForm_monomial s α⟩
      · rw [sum_boole, Nat.cast_id, filter_mem_eq_inter, univ_inter, hs]
      · refine Pi.single_eq_of_ne (fun h => hu ?_) _
        subst h; split_ifs with h' <;> simp [h']
      · have := hα j
        show _ ≤ b j - (if j ∈ s then 1 else 0)
        by_cases hu : u = if j ∈ s then univ else ∅
        · subst hu
          rw [Pi.single_eq_same, X_pow_eq_monomial]
          refine (totalDegree_monomial_le _ _).trans ?_
          rw [Finsupp.sum_single_index rfl]
          exact Nat.le_sub_of_add_le this
        · rw [Pi.single_eq_of_ne hu, totalDegree_zero]; exact Nat.zero_le _
    · rw [hω.1 s hs, Pi.single_zero]; exact Submodule.zero_mem _
  · rintro _ ⟨e, ω, he, hω, rfl⟩
    -- a factor vanishes unless the form degrees match `t`
    have hzero : ∀ t : Finset d, (∃ j, (if j ∈ t then 1 else 0) ≠ e j) → prodForm ω t = 0 := by
      rintro t ⟨j, hj⟩
      refine prod_eq_zero (mem_univ j) ?_
      rw [(hω j).1 _ (by split_ifs at hj ⊢ <;> simp_all), map_zero]
    refine ⟨fun t ht => hzero t ?_, fun t => ?_⟩
    · by_contra h
      push Not at h
      refine ht ?_
      rw [← he, ← sum_congr rfl fun j _ => h j, sum_boole, Nat.cast_id, filter_mem_eq_inter,
        univ_inter]
    · by_cases h : ∃ j, (if j ∈ t then 1 else 0) ≠ e j
      · rw [hzero t h]; exact Submodule.zero_mem _
      · push Not at h
        refine mem_restrictSupport_cubeSupport fun i => ?_
        have hdeg := (degreeOf_prod_le i univ _).trans (sum_le_sum fun j _ =>
          degreeOf_rename_le (R := R) (ω j (if j ∈ t then univ else ∅)) i j)
        rw [sum_ite_eq univ i, ite_eq_left (mem_univ i)] at hdeg
        have h1 := (hω i).2 (if i ∈ t then univ else ∅)
        have h2 := hb i
        have h3 := h i
        have h4 := hdeg.trans h1
        have h5 : e i ≤ 1 := by rw [← h3]; split_ifs <;> omega
        change degreeOf i (∏ j, rename (fun _ => j) (ω j (if j ∈ t then univ else ∅))) + _ ≤ _
        rw [h3]
        omega

end Tensor

end Feec.Koszul
