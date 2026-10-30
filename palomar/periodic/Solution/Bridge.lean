module

public import Solution.Defs
public import Feec.Algebra.CubicalForm

/-!
# The bridge from the challenge to `Feec`

The polynomial forms of `Challenge.lean` are those of `Feec` (`Feec.Koszul.PolyForm` on the index
type `Fin n`): the exterior derivative and the Koszul differential are `Feec.Koszul.extDerivₗ`
and `Feec.Koszul.koszulₗ` (`extDeriv_eq`, `koszul_eq`), and the spaces `H_rΛᵏ`, `P_rΛᵏ`,
`P_r⁻Λᵏ` and `Q_r⁻Λᵏ`, defined in the challenge through Mathlib's submodules of `MvPolynomial`, are
`Feec.Koszul.homForm`, `Feec.Koszul.polyForm`, `Feec.Koszul.polyFormMinus` and
`Feec.Koszul.cubeFormMinus` (`homForm_eq_feec`, …). The conclusions of the challenge then follow
from the dimension counts, the polynomial Poincaré lemmas and the Koszul decompositions of
`Feec.Algebra.PolynomialFormDim` and `Feec.Algebra.CubicalForm` (`periodicTable_of_feec`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3
* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Finset MvPolynomial Module LinearMap

@[expose] public noncomputable section

namespace FEEC

variable {K : Type*} [Field K] {n : ℕ}

/-! ### The differentials and the spaces in `Feec` -/

theorem sign_eq (j : Fin n) (s : Finset (Fin n)) :
    (sign j s : MvPolynomial (Fin n) K) = Feec.ExteriorFibre.sgn j s := by
  simp only [sign, Feec.ExteriorFibre.sgn]

theorem extDeriv_eq : extDeriv K n = Feec.Koszul.extDerivₗ K (Fin n) := by
  refine LinearMap.ext fun ω => funext fun s => ?_
  simp [extDeriv, Feec.Koszul.extDeriv_apply, sign_eq]

theorem koszul_eq : koszul K n = Feec.Koszul.koszulₗ K (Fin n) := by
  refine LinearMap.ext fun ω => funext fun s => ?_
  simp [koszul, Feec.Koszul.koszul_apply, sign_eq]

theorem mem_kForm {k : ℕ} {S : Finset (Fin n) → Submodule K (MvPolynomial (Fin n) K)}
    {ω : PolyForm K n} : ω ∈ kForm K n k S ↔ Feec.ExteriorFibre.IsDeg k ω ∧ ∀ s, ω s ∈ S s := by
  simp only [kForm, Submodule.mem_pi, Set.mem_univ, true_implies]
  refine ⟨fun h => ⟨fun s hs => by simpa [hs] using h s, fun s => ?_⟩, fun h s => ?_⟩
  · by_cases hs : #s = k
    · simpa [hs] using h s
    · have := h s
      simp only [hs, ite_false, Submodule.mem_bot] at this
      simp [this]
  · split_ifs with hs
    · exact h.2 s
    · simp [h.1 s hs]

theorem homForm_eq_feec (r k : ℕ) : homForm K n r k = Feec.Koszul.homForm K (Fin n) r k := by
  ext ω
  rw [homForm, mem_kForm]
  rfl

theorem polyForm_eq_feec (r k : ℕ) : polyForm K n r k = Feec.Koszul.polyForm K (Fin n) r k := by
  ext ω
  rw [polyForm, mem_kForm]
  simp only [mem_restrictTotalDegree]
  rfl

theorem polyFormMinus_eq_feec (r k : ℕ) :
    polyFormMinus K n r k = Feec.Koszul.polyFormMinus K (Fin n) r k := by
  rw [polyFormMinus, Feec.Koszul.polyFormMinus, polyForm_eq_feec, homForm_eq_feec, koszul_eq]

theorem cubeFormMinus_eq_feec (r k : ℕ) :
    cubeFormMinus K n r k = Feec.Koszul.cubeFormMinus K (fun _ => r) k := by
  ext ω
  rw [cubeFormMinus, mem_kForm, Feec.Koszul.mem_cubeFormMinus]
  simp only [Feec.Koszul.cubeSupport]

/-! ### Exactness -/

/-- A space `B` of forms whose closed forms are the differentials of `A`. -/
theorem ker_inf_eq_map {A B : Submodule K (PolyForm K n)}
    (hd : ∀ η ∈ A, Feec.Koszul.extDeriv η ∈ B)
    (he : ∀ ω ∈ B, Feec.Koszul.extDeriv ω = 0 → ∃ η ∈ A, Feec.Koszul.extDeriv η = ω) :
    ker (extDeriv K n) ⊓ B = A.map (extDeriv K n) := by
  ext ω
  simp only [Submodule.mem_inf, mem_ker, Submodule.mem_map, extDeriv_eq,
    Feec.Koszul.extDerivₗ_apply]
  refine ⟨fun h => he ω h.2 h.1, ?_⟩
  rintro ⟨η, hη, rfl⟩
  exact ⟨Feec.Koszul.extDeriv_extDeriv η, hd η hη⟩

/-- The constants are closed. -/
theorem extDeriv_eq_zero_of_mem_polyForm_zero {ω : PolyForm K n}
    (h : ω ∈ Feec.Koszul.polyForm K (Fin n) 0 0) : Feec.Koszul.extDeriv ω = 0 := by
  funext s
  refine sum_eq_zero fun j _ => ?_
  rw [totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 (h.2 _)), pderiv_C, mul_zero]

/-- A space `B` of `0`-forms containing the constants, inside some `P_rΛ⁰`: its closed forms
are the constants. -/
theorem ker_inf_eq_const [CharZero K] {B : Submodule K (PolyForm K n)} {r : ℕ}
    (hB : B ≤ Feec.Koszul.polyForm K (Fin n) r 0)
    (h0 : Feec.Koszul.polyForm K (Fin n) 0 0 ≤ B) :
    ker (extDeriv K n) ⊓ B = polyForm K n 0 0 := by
  ext ω
  simp only [Submodule.mem_inf, mem_ker, extDeriv_eq, Feec.Koszul.extDerivₗ_apply,
    polyForm_eq_feec]
  exact ⟨fun h => Feec.Koszul.mem_polyForm_zero_of_extDeriv_eq_zero (hB h.2).1 h.1,
    fun h => ⟨extDeriv_eq_zero_of_mem_polyForm_zero h, h0 h⟩⟩

/-- The constants are in `Q_r⁻Λ⁰`. -/
theorem polyForm_zero_le_cubeFormMinus (r : ℕ) :
    Feec.Koszul.polyForm K (Fin n) 0 0 ≤ Feec.Koszul.cubeFormMinus K (fun _ => r) 0 := by
  intro ω h
  refine ⟨h.1, fun s => (mem_restrictSupport_iff K).2 fun α hα j => ?_⟩
  have hs : s = ∅ := by
    by_contra hs
    exact (mem_support_iff.1 hα) (by rw [h.1 s (by simpa using hs)]; rfl)
  subst hs
  have := (monomial_le_degreeOf j hα).trans ((degreeOf_le_totalDegree _ j).trans (h.2 ∅))
  simp only [notMem_empty, ite_false]
  omega

/-! ### The theorem -/

/-- **The algebra of the periodic table**, from `Feec.Algebra.PolynomialFormDim` and
`Feec.Algebra.CubicalForm`. -/
theorem periodicTable_of_feec (K : Type*) [Field K] (n : ℕ) :
    PeriodicTable K n where
  finrank_polyForm r k := by
    rw [polyForm_eq_feec, Feec.Koszul.finrank_polyForm, Fintype.card_fin]
  finrank_polyFormMinus r k hr := by
    rw [polyFormMinus_eq_feec, Feec.Koszul.finrank_polyFormMinus hr, Fintype.card_fin]
  finrank_cubeFormMinus r k := by
    rw [cubeFormMinus_eq_feec, Feec.Koszul.finrank_cubeFormMinus_const, Fintype.card_fin,
      mul_assoc]
  exact_polyForm r k := by
    rw [polyForm_eq_feec, polyForm_eq_feec]
    exact ker_inf_eq_map (fun η hη => Feec.Koszul.extDeriv_mem_polyForm hη)
      fun ω hω hd => Feec.Koszul.exists_extDeriv_eq_of_mem_polyForm hω hd
  exact_polyFormMinus r k hr := by
    rw [polyFormMinus_eq_feec, polyFormMinus_eq_feec]
    exact ker_inf_eq_map
      (fun η hη => Feec.Koszul.extDeriv_mem_polyFormMinus_of_mem_polyFormMinus hη)
      fun ω hω hd => Feec.Koszul.exists_extDeriv_eq_of_mem_polyFormMinus hr hω hd
  exact_cubeFormMinus r k := by
    rw [cubeFormMinus_eq_feec, cubeFormMinus_eq_feec]
    exact ker_inf_eq_map (fun η hη => Feec.Koszul.extDeriv_mem_cubeFormMinus hη)
      fun ω hω hd => Feec.Koszul.exists_extDeriv_eq_of_mem_cubeFormMinus hω hd
  closed_polyForm r := by
    rw [polyForm_eq_feec]
    exact ker_inf_eq_const le_rfl (Feec.Koszul.polyForm_mono (Nat.zero_le r) 0)
  closed_polyFormMinus r hr := by
    rw [polyFormMinus_eq_feec, Feec.Koszul.polyFormMinus_zero hr]
    exact ker_inf_eq_const le_rfl (Feec.Koszul.polyForm_mono (Nat.zero_le r) 0)
  closed_cubeFormMinus r := by
    rw [cubeFormMinus_eq_feec]
    exact ker_inf_eq_const (Feec.Koszul.cubeFormMinus_le_polyForm _ 0)
      (polyForm_zero_le_cubeFormMinus r)
  homotopy r k ω hω := by
    rw [homForm_eq_feec] at hω
    simpa [extDeriv_eq, koszul_eq] using Feec.Koszul.extDeriv_koszul_add_koszul_extDeriv_of_mem hω
  homForm_zero_eq r := by
    rw [homForm_eq_feec, homForm_eq_feec, koszul_eq]
    exact Feec.Koszul.map_koszul_homForm_one r
  polyForm_eq r k hr := by
    rw [polyFormMinus_eq_feec, homForm_eq_feec, polyForm_eq_feec, extDeriv_eq]
    exact ⟨Feec.Koszul.polyFormMinus_sup_map_extDeriv hr k,
      Feec.Koszul.disjoint_polyFormMinus_map_extDeriv hr k⟩
  homForm_eq r k := by
    rw [homForm_eq_feec, homForm_eq_feec, homForm_eq_feec, koszul_eq, extDeriv_eq]
    exact ⟨Feec.Koszul.map_koszul_sup_map_extDeriv r k,
      Feec.Koszul.disjoint_map_koszul_map_extDeriv r k⟩

end FEEC
