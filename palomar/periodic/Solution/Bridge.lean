module

public import Solution.Defs
public import Feec.Algebra.ExteriorAlgebraForm
public import Feec.FiniteElement.PolyKind
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The bridge from the challenge to `Feec`

The polynomial forms of `Challenge.lean` live in `P(Kⁿ) ⊗ Λ(Kⁿ)*`, Mathlib's exterior algebra of
the covectors with polynomial coefficients; those of `Feec` are coefficient functions
`Finset (Fin n) → K[x]` in the basis `dx_s` (`Feec.Koszul.PolyForm`). The linear equivalence
`Feec.Koszul.formEquiv` between them (`Feec.Algebra.ExteriorAlgebraForm`) carries the exterior
derivative and the Koszul differential of the challenge to `Feec.Koszul.extDeriv` and
`Feec.Koszul.koszul` (`comp_extDeriv`, `comp_koszul`) and the spaces `H_rΛᵏ`, `P_rΛᵏ`, `P_r⁻Λᵏ`,
`Q_b⁻Λᵏ` to `Feec.Koszul.homForm`, `Feec.Koszul.polyForm`, `Feec.Koszul.polyFormMinus`,
`Feec.Koszul.cubeFormMinus` (`map_homForm`, …). The conclusions of the challenge then follow
from the dimension counts, the polynomial Poincaré lemmas and the Koszul decompositions of
`Feec.Algebra.PolynomialFormDim` and `Feec.Algebra.CubicalForm` (`periodicTable_of_feec`);
exactness of a complex `deRham` is the identity `ker d ∩ S_{k+1} ⊆ d S_k`
(`exactAt_deRham_iff`). The wedge closures of `P_r⁻Λ` follow from the Leibniz rule for `κ`
(`Feec.Koszul.tensorKoszul_mul`) and the equivalent definition `ω ∈ P_rΛᵏ, κω ∈ P_rΛᵏ⁻¹`
(`mul_mem_of_koszul_mem`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3
* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §5

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Finset MvPolynomial Module LinearMap CategoryTheory

@[expose] public noncomputable section

universe u

namespace FEEC

variable {K : Type u} [Field K] {n : ℕ}

local notation "Φ" => Feec.Koszul.formEquiv K (Fin n)

/-! ### The differentials -/

theorem comp_extDeriv :
    (Φ).toLinearMap ∘ₗ extDeriv K n = Feec.Koszul.extDerivₗ K (Fin n) ∘ₗ (Φ).toLinearMap :=
  LinearMap.ext fun ω => Feec.Koszul.formEquiv_tensorExtDeriv ω

theorem comp_koszul :
    (Φ).toLinearMap ∘ₗ koszul K n = Feec.Koszul.koszulₗ K (Fin n) ∘ₗ (Φ).toLinearMap :=
  LinearMap.ext fun ω => Feec.Koszul.formEquiv_tensorKoszul ω

theorem formEquiv_extDeriv (ω : Form K n) :
    Φ (extDeriv K n ω) = Feec.Koszul.extDeriv (Φ ω) :=
  Feec.Koszul.formEquiv_tensorExtDeriv ω

theorem formEquiv_koszul (ω : Form K n) : Φ (koszul K n ω) = Feec.Koszul.koszul (Φ ω) :=
  Feec.Koszul.formEquiv_tensorKoszul ω

/-! ### Transport of subspaces -/

theorem map_map_extDeriv (A : Submodule K (Form K n)) :
    (A.map (extDeriv K n)).map (Φ).toLinearMap =
      (A.map (Φ).toLinearMap).map (Feec.Koszul.extDerivₗ K (Fin n)) := by
  rw [← Submodule.map_comp, comp_extDeriv, Submodule.map_comp]

theorem map_map_koszul (A : Submodule K (Form K n)) :
    (A.map (koszul K n)).map (Φ).toLinearMap =
      (A.map (Φ).toLinearMap).map (Feec.Koszul.koszulₗ K (Fin n)) := by
  rw [← Submodule.map_comp, comp_koszul, Submodule.map_comp]

theorem map_ker_extDeriv :
    (ker (extDeriv K n)).map (Φ).toLinearMap = ker (Feec.Koszul.extDerivₗ K (Fin n)) := by
  ext ω
  simp only [Submodule.mem_map_equiv, mem_ker, Feec.Koszul.extDerivₗ_apply]
  rw [← (Φ).map_eq_zero_iff, formEquiv_extDeriv, LinearEquiv.apply_symm_apply]

theorem map_ker_koszul :
    (ker (koszul K n)).map (Φ).toLinearMap = ker (Feec.Koszul.koszulₗ K (Fin n)) := by
  ext ω
  simp only [Submodule.mem_map_equiv, mem_ker, Feec.Koszul.koszulₗ_apply]
  rw [← (Φ).map_eq_zero_iff, formEquiv_koszul, LinearEquiv.apply_symm_apply]

theorem map_inf (A B : Submodule K (Form K n)) :
    (A ⊓ B).map (Φ).toLinearMap = A.map (Φ).toLinearMap ⊓ B.map (Φ).toLinearMap :=
  Submodule.map_inf _ (Φ).injective

theorem map_eq_iff {A B : Submodule K (Form K n)} :
    A.map (Φ).toLinearMap = B.map (Φ).toLinearMap ↔ A = B :=
  (Submodule.map_injective_of_injective (Φ).injective).eq_iff

theorem map_le_iff {A B : Submodule K (Form K n)} :
    A.map (Φ).toLinearMap ≤ B.map (Φ).toLinearMap ↔ A ≤ B :=
  Submodule.map_le_map_iff_of_injective (Φ).injective A B

theorem map_lt_iff {A B : Submodule K (Form K n)} :
    A.map (Φ).toLinearMap < B.map (Φ).toLinearMap ↔ A < B := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, map_le_iff, Ne, map_eq_iff]

theorem map_comap_koszul (B : Submodule K (Form K n)) :
    (B.comap (koszul K n)).map (Φ).toLinearMap =
      (B.map (Φ).toLinearMap).comap (Feec.Koszul.koszulₗ K (Fin n)) := by
  ext ω
  simp only [Submodule.mem_map_equiv, Submodule.mem_comap, Feec.Koszul.koszulₗ_apply]
  rw [show (Φ).symm (Feec.Koszul.koszul ω) = koszul K n ((Φ).symm ω) by
    rw [LinearEquiv.symm_apply_eq, formEquiv_koszul, LinearEquiv.apply_symm_apply]]

theorem disjoint_of_map {A B : Submodule K (Form K n)}
    (h : Disjoint (A.map (Φ).toLinearMap) (B.map (Φ).toLinearMap)) : Disjoint A B := by
  rw [Submodule.disjoint_def] at h ⊢
  exact fun x ha hb => (Φ).injective (by simpa using h (Φ x) ⟨x, ha, rfl⟩ ⟨x, hb, rfl⟩)

theorem finrank_eq (A : Submodule K (Form K n)) :
    finrank K A = finrank K (A.map (Φ).toLinearMap) :=
  (LinearEquiv.finrank_map_eq Φ A).symm

/-! ### The spaces -/

theorem map_kForm (S : Submodule K (MvPolynomial (Fin n) K)) (k : ℕ) :
    (kForm K n S k).map (Φ).toLinearMap = Feec.Koszul.coeffForm K k S :=
  Feec.Koszul.map_formEquiv_range_mapIncl S k

theorem map_homForm (r k : ℕ) :
    (homForm K n r k).map (Φ).toLinearMap = Feec.Koszul.homForm K (Fin n) r k := by
  rw [homForm, map_kForm, Feec.Koszul.homForm_eq_coeffForm]

theorem map_polyForm (r k : ℕ) :
    (polyForm K n r k).map (Φ).toLinearMap = Feec.Koszul.polyForm K (Fin n) r k := by
  rw [polyForm, map_kForm, Feec.Koszul.polyForm_eq_coeffForm]

theorem map_polyFormMinus (r k : ℕ) :
    (polyFormMinus K n r k).map (Φ).toLinearMap = Feec.Koszul.polyFormMinus K (Fin n) r k := by
  cases r with
  | zero => exact Submodule.map_bot _
  | succ r =>
    rw [polyFormMinus, Submodule.map_sup, map_polyForm, map_map_koszul, map_homForm,
      Feec.Koszul.polyFormMinus_succ]

theorem map_cubeFormMinus (b : Fin n → ℕ) (k : ℕ) :
    (cubeFormMinus K n b k).map (Φ).toLinearMap = Feec.Koszul.cubeFormMinus K b k := by
  have h : ∀ σ : Fin k → Fin n,
      {α : Fin n →₀ ℕ | ∀ j, α j + (if j ∈ Set.range σ then 1 else 0) ≤ b j} =
        Feec.Koszul.cubeSupport b (univ.image σ) := fun σ => by
    ext α; simp [Feec.Koszul.cubeSupport]
  simp only [cubeFormMinus, h]
  exact Feec.Koszul.map_formEquiv_iSup _ k

theorem map_polyFormSeq (r k : ℕ) :
    (polyFormSeq K n r k).map (Φ).toLinearMap =
      if k ≤ r then Feec.Koszul.polyForm K (Fin n) (r - k) k else ⊥ := by
  unfold polyFormSeq
  split_ifs
  · exact map_polyForm _ _
  · exact Submodule.map_bot _

/-! ### Exactness -/

/-- A complex `deRham` is exact at `k + 1` iff the closed forms of `S_{k+1}` are differentials
of forms of `S_k`. -/
theorem exactAt_deRham_iff (hd : extDeriv K n ∘ₗ extDeriv K n = 0)
    {S : ℕ → Submodule K (Form K n)} (hS : ∀ k, (S k).map (extDeriv K n) ≤ S (k + 1)) (k : ℕ) :
    (deRham hd hS).ExactAt (k + 1) ↔ ker (extDeriv K n) ⊓ S (k + 1) ≤ (S k).map (extDeriv K n) := by
  rw [HomologicalComplex.exactAt_iff' _ k (k + 1) (k + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g, deRham, CochainComplex.of_d]
  refine ⟨fun h ω ⟨hk, hω⟩ => ?_, fun h ω h0 => ?_⟩
  · obtain ⟨η, he⟩ := h ⟨ω, hω⟩ (Subtype.ext hk)
    exact ⟨η.1, η.2, congrArg Subtype.val he⟩
  · obtain ⟨η, hη, he⟩ := h ⟨congrArg Subtype.val h0, ω.2⟩
    exact ⟨⟨η, hη⟩, Subtype.ext he⟩

/-- Exactness transported to `Feec`. -/
theorem exactAt_deRham_of_feec (hd : extDeriv K n ∘ₗ extDeriv K n = 0)
    {S : ℕ → Submodule K (Form K n)} (hS : ∀ k, (S k).map (extDeriv K n) ≤ S (k + 1)) (k : ℕ)
    (he : ∀ ω ∈ (S (k + 1)).map (Φ).toLinearMap, Feec.Koszul.extDeriv ω = 0 →
      ∃ η ∈ (S k).map (Φ).toLinearMap, Feec.Koszul.extDeriv η = ω) :
    (deRham hd hS).ExactAt (k + 1) := by
  rw [exactAt_deRham_iff, ← map_le_iff, map_inf, map_ker_extDeriv, map_map_extDeriv]
  rintro ω ⟨hω, hS⟩
  obtain ⟨η, hη, rfl⟩ := he ω hS hω
  exact ⟨η, hη, rfl⟩

/-- A space `B` of `0`-forms containing the constants, inside some `P_rΛ⁰`: its closed forms
are the constants. -/
theorem ker_inf_eq_const [CharZero K] {B : Submodule K (Feec.Koszul.PolyForm K (Fin n))} {r : ℕ}
    (hB : B ≤ Feec.Koszul.polyForm K (Fin n) r 0)
    (h0 : Feec.Koszul.polyForm K (Fin n) 0 0 ≤ B) :
    ker (Feec.Koszul.extDerivₗ K (Fin n)) ⊓ B = Feec.Koszul.polyForm K (Fin n) 0 0 := by
  ext ω
  simp only [Submodule.mem_inf, mem_ker, Feec.Koszul.extDerivₗ_apply]
  exact ⟨fun h => Feec.Koszul.mem_polyForm_zero_of_extDeriv_eq_zero (hB h.2).1 h.1,
    fun h => ⟨Feec.Koszul.extDeriv_eq_zero_of_mem_polyForm_zero h, h0 h⟩⟩

/-- The constants are in `Q_b⁻Λ⁰`. -/
theorem polyForm_zero_le_cubeFormMinus (b : Fin n → ℕ) :
    Feec.Koszul.polyForm K (Fin n) 0 0 ≤ Feec.Koszul.cubeFormMinus K b 0 := by
  intro ω h
  refine ⟨h.1, fun s => (mem_restrictSupport_iff K).2 fun α hα j => ?_⟩
  have hs : s = ∅ := by
    by_contra hs
    exact (mem_support_iff.1 hα) (by rw [h.1 s (by simpa using hs)]; rfl)
  subst hs
  have := (monomial_le_degreeOf j hα).trans ((degreeOf_le_totalDegree _ j).trans (h.2 ∅))
  simp only [notMem_empty, ite_false]
  omega

/-! ### Standalone forms of the fields used by other fields -/

section Helpers

variable (K n)

theorem extDeriv_comp_extDeriv' : extDeriv K n ∘ₗ extDeriv K n = 0 :=
  LinearMap.ext fun ω => (Feec.Koszul.formEquiv K (Fin n)).injective
    (by simp [formEquiv_extDeriv, Feec.Koszul.extDeriv_extDeriv])

variable {K n}

theorem polyForm_le_kForm_top (r k : ℕ) : polyForm K n r k ≤ kForm K n ⊤ k :=
  TensorProduct.range_mapIncl_mono le_top le_rfl

/-- `κ` vanishes on `0`-forms. -/
theorem koszul_eq_zero_of_mem_kForm_zero {S : Submodule K (MvPolynomial (Fin n) K)}
    {ω : Form K n} (h : ω ∈ kForm K n S 0) : koszul K n ω = 0 := by
  have h' : Φ ω ∈ Feec.Koszul.coeffForm K 0 S := map_kForm S 0 ▸ Submodule.mem_map_of_mem h
  exact (Φ).injective (by rw [formEquiv_koszul, map_zero]; exact Feec.Koszul.IsDeg.koszul_eq_zero h'.1)

theorem koszul_mul' {k : ℕ} {ω : Form K n} (hω : ω ∈ kForm K n ⊤ k) (η : Form K n) :
    koszul K n (ω * η) = koszul K n ω * η + (-1 : K) ^ k • (ω * koszul K n η) :=
  Feec.Koszul.tensorKoszul_mul hω η

theorem polyForm_mul_le' (r s k l : ℕ) :
    polyForm K n r k * polyForm K n s l ≤ polyForm K n (r + s) (k + l) :=
  (Feec.Koszul.range_mapIncl_mul_le _ _ k l).trans
    (TensorProduct.range_mapIncl_mono (Feec.Koszul.restrictTotalDegree_mul_le r s) le_rfl)

/-- The products of forms `ω ∈ P_rΛᵏ`, `κω ∈ P_rΛᵏ⁻¹` and `η ∈ P_sΛˡ`, `κη ∈ P_sΛˡ⁻¹`: by the
Leibniz rule, `ωη ∈ P_{r+s}Λ^{k+l}` and `κ(ωη) ∈ P_{r+s}Λ^{k+l-1}`. -/
theorem mul_mem_of_koszul_mem {r s k l : ℕ} {ω η : Form K n}
    (hω : ω ∈ polyForm K n r k) (hκω : koszul K n ω ∈ polyForm K n r (k - 1))
    (hη : η ∈ polyForm K n s l) (hκη : koszul K n η ∈ polyForm K n s (l - 1)) :
    ω * η ∈ polyForm K n (r + s) (k + l) ∧
      koszul K n (ω * η) ∈ polyForm K n (r + s) (k + l - 1) := by
  refine ⟨polyForm_mul_le' r s k l (Submodule.mul_mem_mul hω hη), ?_⟩
  rw [koszul_mul' (polyForm_le_kForm_top r k hω)]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · cases k with
    | zero => rw [koszul_eq_zero_of_mem_kForm_zero hω, zero_mul]; exact Submodule.zero_mem _
    | succ k =>
      rw [show k + 1 + l - 1 = k + l by omega]
      exact polyForm_mul_le' r s k l (Submodule.mul_mem_mul (by simpa using hκω) hη)
  · cases l with
    | zero => rw [koszul_eq_zero_of_mem_kForm_zero hη, mul_zero]; exact Submodule.zero_mem _
    | succ l =>
      rw [show k + (l + 1) - 1 = k + l by omega]
      exact polyForm_mul_le' r s k l (Submodule.mul_mem_mul hω (by simpa using hκη))

theorem extDeriv_eq_zero_of_mem_polyForm_zero' [CharZero K] {k : ℕ} {ω : Form K n}
    (h : ω ∈ polyForm K n 0 k) : extDeriv K n ω = 0 := by
  have h' : Φ ω ∈ Feec.Koszul.polyForm K (Fin n) 0 k :=
    map_polyForm (K := K) 0 k ▸ Submodule.mem_map_of_mem h
  exact (Φ).injective (by
    rw [formEquiv_extDeriv, map_zero]; exact Feec.Koszul.extDeriv_eq_zero_of_mem_polyForm_zero h')

theorem polyForm_eq' [CharZero K] (r k : ℕ) :
    polyFormMinus K n r (k + 1) ⊔ (homForm K n (r + 1) k).map (extDeriv K n) =
        polyForm K n r (k + 1) ∧
      Disjoint (polyFormMinus K n r (k + 1)) ((homForm K n (r + 1) k).map (extDeriv K n)) := by
  cases r with
  | zero =>
    refine ⟨?_, by simp [polyFormMinus]⟩
    rw [polyFormMinus, bot_sup_eq, ← map_eq_iff, map_map_extDeriv, map_homForm, map_polyForm,
      Feec.Koszul.polyForm_zero_eq_homForm]
    exact Feec.Koszul.map_extDeriv_homForm_one k
  | succ r =>
    refine ⟨map_eq_iff.1 ?_, disjoint_of_map ?_⟩
    · rw [Submodule.map_sup, map_polyFormMinus, map_map_extDeriv, map_homForm, map_polyForm]
      exact Feec.Koszul.polyFormMinus_sup_map_extDeriv (by omega) k
    · rw [map_polyFormMinus, map_map_extDeriv, map_homForm]
      exact Feec.Koszul.disjoint_polyFormMinus_map_extDeriv (by omega) k

theorem polyFormMinus_eq_inf_comap' [CharZero K] (r k : ℕ) (hrk : 1 ≤ r + k) :
    polyFormMinus K n r k = polyForm K n r k ⊓ (polyForm K n r (k - 1)).comap (koszul K n) := by
  rw [← map_eq_iff, map_inf, map_comap_koszul, map_polyForm, map_polyForm]
  cases r with
  | zero =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [polyFormMinus, Submodule.map_bot, eq_comm, eq_bot_iff]
    rintro ω ⟨hω, hκ⟩
    rw [Feec.Koszul.polyForm_zero_eq_homForm] at hω
    have hκ0 : Feec.Koszul.koszul ω = 0 := Feec.Koszul.eq_zero_of_mem_homForm_of_mem_polyForm
      (by simpa using Feec.Koszul.koszul_mem_homForm hω) hκ
    exact (Submodule.mem_bot K).2
      (Feec.Koszul.eq_zero_of_mem_homForm_zero_of_koszul_eq_zero hω hκ0)
  | succ r =>
    rw [map_polyFormMinus]
    exact Feec.Koszul.polyFormMinus_succ_eq_inf_comap r k

end Helpers

/-! ### Admissible sequences

An admissible sequence of the challenge is an admissible sequence of families
`Feec.FiniteElement.PolyKind` (`kindOf`, `isAdmissible_of_admissible`), whose spaces are carried to
`Feec.FiniteElement.PolyKind.form` (`map_seqForm`). -/

/-- The family `P_rΛ` (`true`) or `P_r⁻Λ` (`false`). -/
def kindOf (b : Bool) : Feec.FiniteElement.PolyKind := if b then .full else .trimmed

theorem map_seqForm (full : ℕ → Bool) (r : ℕ → ℕ) (k : ℕ) :
    (seqForm K n full r k).map (Φ).toLinearMap = (kindOf (full k)).form K (r k) k := by
  unfold seqForm kindOf
  cases full k
  · exact map_polyFormMinus (r k) k
  · exact map_polyForm (r k) k

theorem isAdmissible_of_admissible {full : ℕ → Bool} {r : ℕ → ℕ} (h : Admissible full r) :
    Feec.FiniteElement.PolyKind.IsAdmissible (fun k => kindOf (full k)) r := by
  refine ⟨h.one_le, fun k => ?_⟩
  rcases h.transition k with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by simp [kindOf, h1], h2⟩
  · exact Or.inr ⟨by simp [kindOf, h1], h2⟩

/-! ### The theorem -/

/-- **The algebra of the periodic table**, from `Feec.Algebra.PolynomialFormDim` and
`Feec.Algebra.CubicalForm`. -/
theorem periodicTable_of_feec (K : Type u) [Field K] (n : ℕ) : PeriodicTable K n where
  finrank_polyForm r k := by
    rw [finrank_eq, map_polyForm, Feec.Koszul.finrank_polyForm, Fintype.card_fin]
  finrank_homForm r k := by
    rw [finrank_eq, map_homForm, Feec.Koszul.finrank_homForm, Fintype.card_fin]
  finrank_polyFormMinus r k hr := by
    rw [finrank_eq, map_polyFormMinus, Feec.Koszul.finrank_polyFormMinus hr,
      Fintype.card_fin]
  finrank_map_koszul_homForm r k := by
    refine ⟨?_, ?_⟩
    · rw [finrank_eq, map_map_koszul, map_homForm, Feec.Koszul.finrank_map_koszul_homForm,
        Fintype.card_fin]
    · rw [finrank_eq, map_map_extDeriv, map_homForm, Feec.Koszul.finrank_map_extDeriv_homForm',
        Fintype.card_fin]
  finrank_cubeFormMinus b k := by
    rw [finrank_eq, map_cubeFormMinus, Feec.Koszul.finrank_cubeFormMinus]
  finrank_cubeFormMinus_const r k := by
    rw [finrank_eq, map_cubeFormMinus, Feec.Koszul.finrank_cubeFormMinus_const, Fintype.card_fin,
      mul_assoc]
  extDeriv_comp_extDeriv := extDeriv_comp_extDeriv' K n
  koszul_comp_koszul := LinearMap.ext fun ω => (Feec.Koszul.formEquiv K (Fin n)).injective
    (by simp [formEquiv_koszul, Feec.Koszul.koszul_koszul])
  koszul_mul _ _ η hω := koszul_mul' hω η
  polyForm_mul_le := polyForm_mul_le'
  polyFormMinus_mul_le r s k l := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [polyFormMinus]
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp [polyFormMinus]
    rw [polyFormMinus_eq_inf_comap' r k (by omega), polyFormMinus_eq_inf_comap' s l (by omega),
      polyFormMinus_eq_inf_comap' (r + s) (k + l) (by omega)]
    exact Submodule.mul_le.2 fun ω hω η hη => mul_mem_of_koszul_mem hω.1 hω.2 hη.1 hη.2
  polyForm_zero_mul_le r s k := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [polyFormMinus]
    rw [polyFormMinus_eq_inf_comap' r k (by omega), polyFormMinus_eq_inf_comap' (r + s) k (by omega)]
    refine Submodule.mul_le.2 fun p hp ω hω => ?_
    have := mul_mem_of_koszul_mem hp
      (by rw [koszul_eq_zero_of_mem_kForm_zero hp]; exact Submodule.zero_mem _) hω.1 hω.2
    rwa [add_comm s r, zero_add] at this
  map_polyFormSeq_le r k := by
    rw [← map_le_iff, map_map_extDeriv, map_polyFormSeq, map_polyFormSeq]
    split_ifs with h1 h2 h2
    · rintro _ ⟨ω, hω, rfl⟩
      have := Feec.Koszul.extDeriv_mem_polyForm hω
      rwa [show r - k - 1 = r - (k + 1) by omega] at this
    · rintro _ ⟨ω, hω, rfl⟩
      rw [show r - k = 0 by omega] at hω
      exact (Submodule.mem_bot K).2 (Feec.Koszul.extDeriv_eq_zero_of_mem_polyForm_zero hω)
    · omega
    · rw [Submodule.map_bot]
  map_polyFormMinus_le r k := by
    rw [← map_le_iff, map_map_extDeriv, map_polyFormMinus, map_polyFormMinus]
    rintro _ ⟨ω, hω, rfl⟩
    exact Feec.Koszul.extDeriv_mem_polyFormMinus hω
  map_cubeFormMinus_le b k := by
    rw [← map_le_iff, map_map_extDeriv, map_cubeFormMinus, map_cubeFormMinus]
    rintro _ ⟨ω, hω, rfl⟩
    exact Feec.Koszul.extDeriv_mem_cubeFormMinus hω
  polyFormSeq_le_polyFormMinus r k hr := by
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    unfold polyFormSeq
    split_ifs with h
    · cases k with
      | zero =>
        rw [← map_le_iff, map_polyForm, map_polyFormMinus, Nat.sub_zero,
          Feec.Koszul.polyFormMinus_zero (by omega)]
      | succ k =>
        refine le_trans ?_ (le_sup_left : polyForm K n r (k + 1) ≤ polyFormMinus K n (r + 1) (k + 1))
        rw [← map_le_iff, map_polyForm, map_polyForm]
        exact Feec.Koszul.polyForm_mono (by omega) _
    · exact bot_le
  exactAt_polyForm r k := by
    refine exactAt_deRham_of_feec _ _ k fun ω hω hd => ?_
    rw [map_polyFormSeq] at hω ⊢
    split_ifs at hω with h
    · obtain ⟨η, hη, he⟩ := Feec.Koszul.exists_extDeriv_eq_of_mem_polyForm hω hd
      simp only [show k ≤ r by omega, ↓reduceIte]
      rw [show r - k = r - (k + 1) + 1 by omega]
      exact ⟨η, hη, he⟩
    · rw [(Submodule.mem_bot K).1 hω]
      exact ⟨0, Submodule.zero_mem _, by simp⟩
  exactAt_polyFormMinus r k := by
    refine exactAt_deRham_of_feec _ _ k fun ω hω hd => ?_
    rw [map_polyFormMinus] at hω ⊢
    exact Feec.FiniteElement.PolyKind.trimmed.exists_extDeriv_eq (Or.inl ⟨rfl, rfl⟩) hω hd
  exactAt_cubeFormMinus b k := by
    refine exactAt_deRham_of_feec _ _ k fun ω hω hd => ?_
    rw [map_cubeFormMinus] at hω ⊢
    exact Feec.Koszul.exists_extDeriv_eq_of_mem_cubeFormMinus hω hd
  closed_polyForm r := by
    rw [← map_eq_iff, map_inf, map_ker_extDeriv, map_polyForm, map_polyForm]
    exact ker_inf_eq_const le_rfl (Feec.Koszul.polyForm_mono (Nat.zero_le r) 0)
  closed_polyFormMinus r hr := by
    rw [← map_eq_iff, map_inf, map_ker_extDeriv, map_polyFormMinus, map_polyForm,
      Feec.Koszul.polyFormMinus_zero hr]
    exact ker_inf_eq_const le_rfl (Feec.Koszul.polyForm_mono (Nat.zero_le r) 0)
  closed_cubeFormMinus b := by
    rw [← map_eq_iff, map_inf, map_ker_extDeriv, map_cubeFormMinus, map_polyForm]
    exact ker_inf_eq_const (Feec.Koszul.cubeFormMinus_le_polyForm _ 0)
      (polyForm_zero_le_cubeFormMinus b)
  ker_extDeriv_inf_homForm_le r k := by
    rw [← map_le_iff, map_inf, map_ker_extDeriv, map_homForm, map_map_extDeriv, map_homForm]
    rintro ω ⟨hd, hω⟩
    obtain ⟨η, hη, he⟩ := Feec.Koszul.exists_extDeriv_eq_of_extDeriv_eq_zero (by omega) hω hd
    exact ⟨η, by simpa using hη, he⟩
  ker_extDeriv_inf_homForm_zero r := by
    rw [← map_eq_iff, map_inf, map_ker_extDeriv, map_homForm, Submodule.map_bot, eq_bot_iff]
    rintro ω ⟨hd, hω⟩
    exact (Submodule.mem_bot K).2 (Feec.Koszul.eq_zero_of_mem_homForm_of_mem_polyForm hω
      (Feec.Koszul.polyForm_mono (Nat.zero_le r) 0
        (Feec.Koszul.mem_polyForm_zero_of_extDeriv_eq_zero hω.1 hd)))
  ker_koszul_inf_homForm_le r k := by
    rw [← map_le_iff, map_inf, map_ker_koszul, map_homForm, map_map_koszul, map_homForm]
    rintro ω ⟨hκ, hω⟩
    obtain ⟨η, hη, he⟩ := Feec.Koszul.exists_koszul_eq_of_koszul_eq_zero (by omega) hω hκ
    exact ⟨η, by simpa using hη, he⟩
  ker_koszul_inf_homForm_zero k := by
    rw [← map_eq_iff, map_inf, map_ker_koszul, map_homForm, Submodule.map_bot, eq_bot_iff]
    rintro ω ⟨hκ, hω⟩
    exact (Submodule.mem_bot K).2
      (Feec.Koszul.eq_zero_of_mem_homForm_zero_of_koszul_eq_zero hω hκ)
  ker_koszul_inf_polyForm_le r k := by
    rw [← map_le_iff, map_inf, map_ker_koszul, map_polyForm, map_map_koszul, map_polyForm]
    rintro ω ⟨hκ, hω⟩
    exact Feec.Koszul.exists_koszul_eq_of_mem_polyForm hω hκ
  ker_koszul_inf_polyForm_zero k := by
    rw [← map_eq_iff, map_inf, map_ker_koszul, map_polyForm, Submodule.map_bot, eq_bot_iff,
      Feec.Koszul.polyForm_zero_eq_homForm]
    rintro ω ⟨hκ, hω⟩
    exact (Submodule.mem_bot K).2
      (Feec.Koszul.eq_zero_of_mem_homForm_zero_of_koszul_eq_zero hω hκ)
  polyForm_zero_eq_koszul r := by
    refine ⟨map_eq_iff.1 ?_, disjoint_of_map ?_⟩
    · rw [Submodule.map_sup, map_map_koszul, map_polyForm, map_polyForm, map_polyForm]
      exact Feec.Koszul.map_koszul_polyForm_sup_polyForm_zero r
    · rw [map_map_koszul, map_polyForm, map_polyForm]
      exact Feec.Koszul.disjoint_map_koszul_polyForm_polyForm_zero r
  homotopy r k ω hω := by
    have hω' : Feec.Koszul.formEquiv K (Fin n) ω ∈ Feec.Koszul.homForm K (Fin n) r k :=
      map_homForm (K := K) r k ▸ Submodule.mem_map_of_mem hω
    refine (Feec.Koszul.formEquiv K (Fin n)).injective ?_
    rw [map_add, formEquiv_extDeriv, formEquiv_koszul, formEquiv_koszul, formEquiv_extDeriv,
      map_smul]
    exact Feec.Koszul.extDeriv_koszul_add_koszul_extDeriv_of_mem hω'
  koszul_eq_zero_of_extDeriv_koszul ω h := (Feec.Koszul.formEquiv K (Fin n)).injective (by
    rw [map_zero, formEquiv_koszul]
    refine Feec.Koszul.koszul_eq_zero_of_extDeriv_koszul_eq_zero ?_
    rw [← formEquiv_koszul, ← formEquiv_extDeriv, h, map_zero])
  extDeriv_eq_zero_of_koszul_extDeriv ω h := (Feec.Koszul.formEquiv K (Fin n)).injective (by
    rw [map_zero, formEquiv_extDeriv]
    refine Feec.Koszul.extDeriv_eq_zero_of_koszul_extDeriv_eq_zero ?_
    rw [← formEquiv_extDeriv, ← formEquiv_koszul, h, map_zero])
  homForm_eq r k := by
    refine ⟨map_eq_iff.1 ?_, disjoint_of_map ?_⟩
    · rw [Submodule.map_sup, map_map_koszul, map_map_extDeriv, map_homForm, map_homForm,
        map_homForm]
      exact Feec.Koszul.map_koszul_sup_map_extDeriv r k
    · rw [map_map_koszul, map_map_extDeriv, map_homForm, map_homForm]
      exact Feec.Koszul.disjoint_map_koszul_map_extDeriv r k
  homForm_zero_eq r := by
    rw [← map_eq_iff, map_map_koszul, map_homForm, map_homForm]
    exact Feec.Koszul.map_koszul_homForm_one r
  homForm_zero_left_eq k := by
    rw [← map_eq_iff, map_map_extDeriv, map_homForm, map_homForm]
    exact Feec.Koszul.map_extDeriv_homForm_one k
  polyForm_eq_koszul r k := by
    refine ⟨map_eq_iff.1 ?_, disjoint_of_map ?_⟩
    · rw [Submodule.map_sup, map_map_koszul, map_map_extDeriv, map_polyForm, map_polyForm,
        map_polyForm]
      exact Feec.Koszul.map_koszul_polyForm_sup_map_extDeriv r k
    · rw [map_map_koszul, map_map_extDeriv, map_polyForm, map_polyForm]
      exact Feec.Koszul.disjoint_map_koszul_polyForm_map_extDeriv r k
  polyForm_zero_left_eq k := by
    rw [← map_eq_iff, map_map_extDeriv, map_polyForm, map_polyForm]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨ω, hω, rfl⟩
      simpa using Feec.Koszul.extDeriv_mem_polyForm hω
    · rw [Feec.Koszul.polyForm_zero_eq_homForm, ← Feec.Koszul.map_extDeriv_homForm_one]
      exact Submodule.map_mono (Feec.Koszul.homForm_le_polyForm 1 k)
  polyForm_eq := polyForm_eq'
  disjoint_polyForm_map_koszul r k := disjoint_of_map (by
    rw [map_polyForm, map_map_koszul, map_homForm]
    exact Feec.Koszul.disjoint_polyForm_map_koszul r k)
  polyFormMinus_eq_sup_map_koszul r k := by
    rw [← map_eq_iff, map_polyFormMinus, Submodule.map_sup, map_polyForm, map_map_koszul,
      map_polyForm]
    exact Feec.Koszul.polyFormMinus_succ_eq_sup_map_koszul_polyForm r k
  map_extDeriv_polyFormMinus r k := by
    cases k with
    | zero =>
      cases r with
      | zero =>
        refine (Submodule.map_bot _).trans (eq_bot_iff.2 ?_).symm
        rintro _ ⟨ω, hω, rfl⟩
        exact (Submodule.mem_bot K).2 (extDeriv_eq_zero_of_mem_polyForm_zero' hω)
      | succ r =>
        rw [← map_eq_iff, map_map_extDeriv, map_map_extDeriv, map_polyFormMinus, map_polyForm,
          Feec.Koszul.polyFormMinus_zero (by omega)]
    | succ k =>
      rw [← (polyForm_eq' r k).1, Submodule.map_sup, ← Submodule.map_comp,
        extDeriv_comp_extDeriv', Submodule.map_zero, sup_bot_eq]
  polyFormMinus_zero r hr := by
    rw [← map_eq_iff, map_polyFormMinus, map_polyForm]
    exact Feec.Koszul.polyFormMinus_zero hr
  polyFormMinus_top r hr := by
    rw [← map_eq_iff, map_polyFormMinus, map_polyForm]
    simpa using Feec.Koszul.polyFormMinus_top (K := K) (d := Fin n) hr
  polyFormMinus_eq_inf_comap := polyFormMinus_eq_inf_comap'
  polyForm_lt_polyFormMinus r k hr hk := by
    rw [← map_lt_iff, map_polyForm, map_polyFormMinus]
    exact Feec.Koszul.polyForm_lt_polyFormMinus hr (by simpa using hk)
  polyFormMinus_lt_polyForm r k hr hk := by
    rw [← map_lt_iff, map_polyForm, map_polyFormMinus]
    exact Feec.Koszul.polyFormMinus_lt_polyForm hr (by simpa using hk)
  ker_inf_polyFormMinus_le r k := by
    rw [← map_le_iff, map_inf, map_ker_extDeriv, map_polyFormMinus, map_polyForm]
    rintro ω ⟨hd, hω⟩
    simpa using Feec.Koszul.mem_polyForm_of_mem_polyFormMinus_of_extDeriv_eq_zero (by omega) hω hd
  finrank_polyForm_eq_sum r k hr := by
    rw [finrank_eq, map_polyForm, ← Feec.FiniteElement.PolyKind.form_full,
      Feec.FiniteElement.PolyKind.finrank_form_eq_sum _ hr]
    refine sum_congr rfl fun m _ => congrArg _ ?_
    by_cases h : k ≤ m ∧ m < r + k
    · rw [Feec.FiniteElement.PolyKind.testForm_full h, finrank_eq,
        map_polyFormMinus]
      simp only [h, and_self, ↓reduceIte]
    · rw [Feec.FiniteElement.PolyKind.testForm_eq_bot _ h, finrank_bot]
      simp only [h, ↓reduceIte]
  finrank_polyFormMinus_eq_sum r k hr := by
    rw [finrank_eq, map_polyFormMinus, ← Feec.FiniteElement.PolyKind.form_trimmed,
      Feec.FiniteElement.PolyKind.finrank_form_eq_sum _ hr]
    refine sum_congr rfl fun m _ => congrArg _ ?_
    by_cases h : k ≤ m ∧ m < r + k
    · rw [Feec.FiniteElement.PolyKind.testForm_trimmed h, finrank_eq, map_polyForm]
      simp only [h, and_self, ↓reduceIte]
    · rw [Feec.FiniteElement.PolyKind.testForm_eq_bot _ h, finrank_bot]
      simp only [h, ↓reduceIte]
  map_seqForm_le full r h k := by
    rw [← map_le_iff, map_map_extDeriv, map_seqForm, map_seqForm]
    rintro _ ⟨ω, hω, rfl⟩
    exact (isAdmissible_of_admissible h).extDeriv_mem hω
  exactAt_seqForm full r h k := by
    refine exactAt_deRham_of_feec _ _ k fun ω hω hd => ?_
    rw [map_seqForm] at hω ⊢
    exact (isAdmissible_of_admissible h).exists_extDeriv_eq hω hd
  closed_seqForm full r h := by
    rw [← map_eq_iff, map_inf, map_ker_extDeriv, map_seqForm, map_polyForm]
    exact ker_inf_eq_const ((kindOf (full 0)).form_le_polyForm h.one_le 0)
      ((Feec.Koszul.polyForm_mono (Nat.zero_le _) 0).trans
        ((Feec.Koszul.polyForm_le_polyFormMinus h.one_le 0).trans
          ((kindOf (full 0)).polyFormMinus_le_form h.one_le 0)))

end FEEC
