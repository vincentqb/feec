module

public import Feec.Models.StarShaped.Smoothing
public import Feec.FiniteElement.PolySmoothingBasic

/-!
# Smoothed projections for the higher-order families on star-shaped domains

On a bounded domain star-shaped with respect to a ball with a shape-regular, quasi-uniform mesh,
the complexes of every admissible sequence, with and without vanishing boundary DOFs, carry
uniformly bounded smoothed cochain projections.

## Main results

* `exists_polyDofBound`, `exists_polyInvBound`: the DOF and the inverse estimates.
* `exists_uniform_polyCochainProjection`: uniformly bounded smoothed cochain projections.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter Topology
open scoped ContDiff

namespace Feec.Models.StarShaped

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre

variable {n : ℕ}

/-! ### Local tools on shape-regular simplices -/

section Local

variable (S : PolySeq)

theorem abs_simplexMatrix_lexEnum_le_diam {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) {m : ℕ} (hg : #g = m + 1) (i : Fin n)
    (l : Fin m) : |simplexMatrix (lexEnum g m) i l| ≤ diam T := by
  have hmem : ∀ a, lexEnum g m a ∈ T.closedInterior := fun a =>
    vertexSet_subset_closedInterior T (hgT (lexEnum_mem hg a))
  have h1 := Metric.dist_le_diam_of_mem T.isCompact_closedInterior.isBounded (hmem l.succ)
    (hmem 0)
  rw [dist_eq_norm] at h1
  refine le_trans ?_ h1
  have h := norm_le_pi_norm (lexEnum g m l.succ - lexEnum g m 0) i
  rwa [Real.norm_eq_abs, Pi.sub_apply] at h

/-- The coefficient fields of the moment DOFs on the faces of a simplex `T` are `O(h_Tᵏ)`. -/
def PolyCoeffBound (n k : ℕ) (D : ℝ) : Prop :=
  ∀ {T : Affine.Simplex ℝ (Fin n → ℝ) n} {g : Finset (Fin n → ℝ)}, g ⊆ vertexSet T →
    ∀ (i : S.DofIdx g k), ∀ ξ ∈ FiniteElement.refSimplex (#g - 1),
      ∑ s, |dofCoeff (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) k
        ξ s| ≤ D * diam T ^ k

theorem exists_polyCoeffBound (k : ℕ) : ∃ D, 0 ≤ D ∧ PolyCoeffBound S n k D := by
  obtain ⟨D, hD0, hD⟩ := S.exists_coeffBound_of_le (n := n) k
  exact ⟨D, hD0, fun {T g} hgT i => hD hgT i (diam_nonneg T)
    (abs_simplexMatrix_lexEnum_le_diam hgT (Nat.succ_pred_eq_of_pos (card_pos.2 i.2)).symm)⟩

theorem abs_polyDof_le {k : ℕ} {D : ℝ} (hD : PolyCoeffBound S n k D)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T)
    (i : S.DofIdx g k) (ψ : contForms n) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ T.closedInterior, ∀ s, |(ψ : FormField n) x s| ≤ B) :
    |S.dof g k i ψ| ≤ D * diam T ^ k * B :=
  S.abs_dof_le_of_coeff_le hgT i ψ (hD hgT i) hB0 hB

/-- The test form `ηᵢ` reparametrized by a vertex permutation `π`, `A_{π⁻¹}^* ηᵢ`. -/
def permTest (k m : ℕ) (π : Equiv.Perm (Fin (m + 1)))
    (i : Fin (Module.finrank ℝ (S.test k m))) : FormField m :=
  affinePullback (simplexMatrix (refVertex m ∘ ⇑(π⁻¹ : Equiv.Perm (Fin (m + 1)))))
    (refVertex m ((π⁻¹ : Equiv.Perm (Fin (m + 1))) 0)) (S.testBasis k m i : FormField m)

theorem permTest_mem (k m : ℕ) (π : Equiv.Perm (Fin (m + 1)))
    (i : Fin (Module.finrank ℝ (S.test k m))) : permTest S k m π i ∈ S.test k m :=
  S.affinePullback_mem_test _ _ k (S.testBasis k m i).2

/-- The size of the reparametrized test forms in the basis of the test forms. -/
def permConst (k m : ℕ) : ℝ :=
  ∑ π : Equiv.Perm (Fin (m + 1)), ∑ i, ∑ l,
    |(S.testBasis k m).repr ⟨permTest S k m π i, permTest_mem S k m π i⟩ l|

theorem permConst_nonneg (k m : ℕ) : 0 ≤ permConst S k m :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_vertexMoment_le_of_dof {g : Finset (Fin n → ℝ)} {m : ℕ} (hg : #g = m + 1) {k : ℕ}
    {η : FormField m} (hη : η ∈ S.test k m) (ψ : contForms n) {D' : ℝ}
    (hD : ∀ i : S.DofIdx g k, |S.dof g k i ψ| ≤ D') :
    |vertexMoment (lexEnum g m) η (degField k ψ)| ≤
      (∑ l, |(S.testBasis k m).repr ⟨η, hη⟩ l|) * D' := by
  obtain rfl : m = #g - 1 := by omega
  have hne : g.Nonempty := card_pos.1 (by omega)
  set b := S.testBasis k (#g - 1)
  conv_lhs => rw [eq_sum_repr_basis b hη]
  rw [vertexMoment_sum_smul_right _ _ _ (fun l => S.continuous_testBasis k _ l)
    (continuous_degField k ψ.2), Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hD ⟨l, hne⟩) (abs_nonneg _)

theorem abs_dof_refPull_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) {g : Finset (Fin n → ℝ)}
    {k : ℕ} (i : S.DofIdx g k) {z : FormField n} (hz : Continuous z) {D' : ℝ}
    (hD : ∀ i' : S.DofIdx (g.image T.refMap) k,
      |S.dof (g.image T.refMap) k i' ⟨z, hz⟩| ≤ D') :
    |S.dof g k i ⟨refPull T z, continuous_refPull T hz⟩| ≤ permConst S k (#g - 1) * D' := by
  set m := #g - 1
  have hg : #g = m + 1 := by have := card_pos.2 i.2; omega
  have hinjr : Function.Injective (T.refMap : (Fin n → ℝ) → Fin n → ℝ) := T.refMap_injective
  have hg' : #(g.image T.refMap) = m + 1 := by rw [card_image_of_injective _ hinjr, hg]
  set q := lexEnum g m
  set q' := lexEnum (g.image T.refMap) m
  have hinj : Function.Injective fun l => affine (simplexMatrix T.points) (T.points 0) (q l) :=
    fun l l' h => by
      simp only [affine_simplexMatrix_eq_refMap] at h
      exact lexEnum_injective hg (hinjr h)
  have hran : Set.range (fun l => affine (simplexMatrix T.points) (T.points 0) (q l)) =
      Set.range q' := by
    rw [range_lexEnum hg', Finset.coe_image, ← range_lexEnum hg, ← Set.range_comp]
    simp only [affine_simplexMatrix_eq_refMap]
    rfl
  obtain ⟨π, hπ⟩ := exists_perm_comp_eq hinj (lexEnum_injective hg') hran
  have he : S.dof g k i ⟨refPull T z, continuous_refPull T hz⟩ =
      ((Equiv.Perm.sign π : ℤ) : ℝ) * vertexMoment q' (permTest S k m π i.1)
        (degField k (⟨z, hz⟩ : contForms n)) := by
    change vertexMoment q (S.testBasis k m i.1 : FormField m)
      (degField k (affinePullback (simplexMatrix T.points) (T.points 0) z)) = _
    rw [degField_affinePullback, vertexMoment_affinePullback, hπ,
      vertexMoment_comp_perm]
    rfl
  have hsign : |((Equiv.Perm.sign π : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have h1 := abs_vertexMoment_le_of_dof S hg' (permTest_mem S k m π i.1) ⟨z, hz⟩ hD
  have h2 : ∑ l, |(S.testBasis k m).repr ⟨permTest S k m π i.1, permTest_mem S k m π i.1⟩ l| ≤
      permConst S k m := by
    have hπ' := Finset.single_le_sum (f := fun π : Equiv.Perm (Fin (m + 1)) => ∑ i, ∑ l,
      |(S.testBasis k m).repr ⟨permTest S k m π i, permTest_mem S k m π i⟩ l|)
      (fun π _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.mem_univ π)
    have hi := Finset.single_le_sum (f := fun i => ∑ l,
      |(S.testBasis k m).repr ⟨permTest S k m π i, permTest_mem S k m π i⟩ l|)
      (fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i.1)
    exact hi.trans hπ'
  have hD0 : 0 ≤ D' := by
    have hne' : (g.image T.refMap).Nonempty := card_pos.1 (by omega)
    have h0 : 0 < Module.finrank ℝ (S.test k (#(g.image T.refMap) - 1)) := by
      rw [show #(g.image T.refMap) - 1 = m by omega]
      exact (Fin.pos_iff_nonempty.2 ⟨i.1⟩)
    exact (abs_nonneg _).trans (hD ⟨⟨0, h0⟩, hne'⟩)
  rw [he, abs_mul, hsign, one_mul]
  exact h1.trans (mul_le_mul_of_nonneg_right h2 hD0)

/-- The DOF estimate on shape-regular simplices: `h_Tᵏ sup_T ‖z‖ ≤ B D'` if the DOFs are `≤ D'`. -/
def PolyDofBound (n k : ℕ) (C c B : ℝ) : Prop :=
  ∀ {Sset : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular Sset C c → ∀ T ∈ Sset,
    0 < diam T → ∀ {z : FormField n} (hz : z ∈ S.space n k) {D' : ℝ}, 0 ≤ D' →
      (∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
        |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ D') →
      ∀ x ∈ T.closedInterior, diam T ^ k * ‖z x‖ ≤ B * D'

/-- The DOF estimate on shape-regular simplices holds with some constant `B ≥ 0`. -/
theorem exists_polyDofBound (k : ℕ) (C c : ℝ) : ∃ B, 0 ≤ B ∧ PolyDofBound S n k C c B := by
  classical
  set J := Σ g : (vertexSet (Mesh.refSimplex n)).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k
  set ℓ : J → S.space n k →ₗ[ℝ] ℝ := fun p =>
    S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ∘ₗ Submodule.inclusion (S.space_le_contForms n k)
  have hℓ : Function.Injective (LinearMap.pi ℓ) := (S.isUnisolvent_dof (Mesh.refSimplex n) k).1
  obtain ⟨B₀, hB₀, hB⟩ := exists_dof_bound_of_le_polySpace (S.space_le_polySpace k)
    (fun B b u hu => S.affinePullback_mem_space B b k hu) ℓ hℓ (C := C)
    (c := c)
  set Kc := ∑ m ∈ Finset.range (n + 1), permConst S k m
  have hKc0 : 0 ≤ Kc := Finset.sum_nonneg fun m _ => permConst_nonneg S k m
  have hKc : ∀ m ≤ n, permConst S k m ≤ Kc := fun m hm =>
    Finset.single_le_sum (f := fun m => permConst S k m) (fun m _ => permConst_nonneg S k m)
      (Finset.mem_range.2 (by omega))
  refine ⟨B₀ * (Fintype.card J * Kc), by positivity,
    fun {Sset} hS T hT hh z hz D' hD0 hD x hx => ?_⟩
  refine (hB hS T hT hh z hz x hx).trans ?_
  have hterm : ∀ p : J, |ℓ p ⟨refPull T z, S.affinePullback_mem_space _ _ k
      hz⟩| ≤ Kc * D' := by
    intro p
    have hsub : (p.1 : Finset (Fin n → ℝ)).image T.refMap ⊆ vertexSet T :=
      image_refMap_subset_vertexSet T (Finset.mem_powerset.1 p.1.2)
    have hp := abs_dof_refPull_le S T p.2 (S.space_le_contForms n k hz) (D' := D')
      (fun i' => hD _ hsub i')
    have hle : #(p.1 : Finset (Fin n → ℝ)) - 1 ≤ n := by
      have := Finset.card_le_card (Finset.mem_powerset.1 p.1.2)
      rw [card_vertexSet] at this; omega
    exact hp.trans (mul_le_mul_of_nonneg_right (hKc _ hle) hD0)
  calc B₀ * ∑ j, |ℓ j ⟨refPull T z, S.affinePullback_mem_space _ _ k hz⟩|
      ≤ B₀ * ∑ _j : J, Kc * D' :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => hterm p) hB₀
    _ = B₀ * (Fintype.card J * Kc) * D' := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Local

/-! ### Local estimates on the simplices of a quasi-uniform shape-regular mesh -/

section MeshTools

variable (S : PolySeq)

theorem abs_le_of_abs_polyDof_le {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q)
    (hq : 0 < q) {k : ℕ} {B : ℝ} (hB : PolyDofBound S n k C c B)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) {z : FormField n}
    (hz : z ∈ S.space n k) {D'' : ℝ} (hD0 : 0 ≤ D'')
    (hD : ∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ M.meshSize ^ k * D'')
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) (s : Finset (Fin n)) :
    |z x s| ≤ B * D'' / q ^ k := by
  have hh := hM.meshSize_pos
  have hzb := hB hM.shape T hT (hM.diam_pos hq hT) hz (by positivity) hD x hx
  have hqh : q * M.meshSize ≤ diam T := hM.quasi T hT
  have hzs : |z x s| ≤ ‖z x‖ := by
    have := norm_le_pi_norm (z x) s; rwa [Real.norm_eq_abs] at this
  have h1 : (q * M.meshSize) ^ k * |z x s| ≤ B * (M.meshSize ^ k * D'') :=
    (mul_le_mul (pow_le_pow_left₀ (by positivity) hqh k) hzs (abs_nonneg _)
      (pow_nonneg (diam_nonneg T) k)).trans hzb
  rw [le_div_iff₀ (pow_pos hq k)]
  have hhk : 0 < M.meshSize ^ k := pow_pos hh k
  refine le_of_mul_le_mul_left ?_ hhk
  calc M.meshSize ^ k * (|z x s| * q ^ k) = (q * M.meshSize) ^ k * |z x s| := by ring
    _ ≤ B * (M.meshSize ^ k * D'') := h1
    _ = M.meshSize ^ k * (B * D'') := by ring

/-- The local inverse estimates on all simplices of `M` for the fields of `V`. -/
def InvBoundV (M : SimplicialMesh n) (V : Submodule ℝ (FormField n)) (A : ℝ) : Prop :=
  ∀ T ∈ M.simplices, ∀ z ∈ V,
    (∀ x ∈ T.closedInterior, ∀ s, √M.meshSize ^ n * |z x s| ≤
      A * √(∑ s, ∫ x in T.closedInterior, (z x s) ^ 2)) ∧
    (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior, ∀ s,
      √M.meshSize ^ n * M.meshSize * |z x s - z x' s| ≤
        A * ‖x - x'‖ * √(∑ s, ∫ x in T.closedInterior, (z x s) ^ 2))

theorem invBoundV_of {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q) (hq : 0 < q)
    {V : Submodule ℝ (FormField n)} {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ {Sset : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular Sset C c →
      ∀ T ∈ Sset, 0 < diam T → ∀ u ∈ V,
        (∀ x ∈ T.closedInterior, √(diam T) ^ n * ‖u x‖ ≤
          A * √(formL2Sq T.closedInterior u)) ∧
        (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior,
          √(diam T) ^ n * diam T * ‖u x - u x'‖ ≤
            A * ‖x - x'‖ * √(formL2Sq T.closedInterior u))) :
    InvBoundV M V (A / √q ^ n / q) := by
  intro T hT z hz
  have hh := hM.meshSize_pos
  have hq1 := hM.q_le_one
  have hTd := hM.diam_pos hq hT
  obtain ⟨h1, h2⟩ := hA hM.shape T hT hTd z hz
  simp only [formL2Sq] at h1 h2
  set F := ∑ s, ∫ x in T.closedInterior, (z x s) ^ 2
  have hqh : q * M.meshSize ≤ diam T := hM.quasi T hT
  have hsq : √M.meshSize ^ n * √q ^ n ≤ √(diam T) ^ n := by
    rw [← mul_pow, ← Real.sqrt_mul hh.le]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith)) n
  have hsqq : 0 < √q ^ n := pow_pos (Real.sqrt_pos.2 hq) n
  have hF : 0 ≤ √F := Real.sqrt_nonneg _
  constructor
  · intro x hx s
    have hxs : |z x s| ≤ ‖z x‖ := by
      have := norm_le_pi_norm (z x) s; rwa [Real.norm_eq_abs] at this
    have := h1 x hx
    have hk : √M.meshSize ^ n * |z x s| ≤ A / √q ^ n * √F := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hsqq]
      calc √M.meshSize ^ n * |z x s| * √q ^ n = (√M.meshSize ^ n * √q ^ n) * |z x s| := by ring
        _ ≤ √(diam T) ^ n * ‖z x‖ :=
            mul_le_mul hsq hxs (abs_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) n)
        _ ≤ _ := this
    refine hk.trans (mul_le_mul_of_nonneg_right ?_ hF)
    exact le_div_self (by positivity) hq hq1
  · intro x hx x' hx' s
    have hxs : |z x s - z x' s| ≤ ‖z x - z x'‖ := by
      have := norm_le_pi_norm (z x - z x') s; rwa [Real.norm_eq_abs, Pi.sub_apply] at this
    have := h2 x hx x' hx'
    rw [div_div]
    rw [show A / (√q ^ n * q) * ‖x - x'‖ * √F =
      ‖x - x'‖ * A * √F / (√q ^ n * q) by ring]
    rw [le_div_iff₀ (by positivity)]
    calc √M.meshSize ^ n * M.meshSize * |z x s - z x' s| * (√q ^ n * q)
        = (√M.meshSize ^ n * √q ^ n) * (q * M.meshSize) * |z x s - z x' s| := by ring
      _ ≤ √(diam T) ^ n * diam T * ‖z x - z x'‖ := by
          gcongr
      _ ≤ A * ‖x - x'‖ * √F := this
      _ = ‖x - x'‖ * A * √F := by ring

/-- Inverse estimates on shape-regular simplices for the spaces of an admissible sequence. -/
theorem exists_polyInvBound (k : ℕ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ A, 0 ≤ A ∧ ∀ {Sset : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular Sset C c →
      ∀ T ∈ Sset, 0 < diam T → ∀ u ∈ S.space n k,
        (∀ x ∈ T.closedInterior, √(diam T) ^ n * ‖u x‖ ≤
          A * √(formL2Sq T.closedInterior u)) ∧
        (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior,
          √(diam T) ^ n * diam T * ‖u x - u x'‖ ≤
            A * ‖x - x'‖ * √(formL2Sq T.closedInterior u)) :=
  exists_inverse_bound_of_le_polySpace (S.space_le_polySpace k)
    (fun B b _ hu => S.affinePullback_mem_space B b k hu) hC hc

end MeshTools

/-! ### The uniform `L²` bound of the smoothed interpolants -/

section Bound

variable (S : PolySeq) {x₀ : Fin n → ℝ} {R σ γ : ℝ}

theorem sum_integral_sq_polyInterp_le {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q)
    (hq : 0 < q) [NeZero n] {k : ℕ} {B D : ℝ} (hB : PolyDofBound S n k C c B)
    (hD0 : 0 ≤ D) (hD : PolyCoeffBound S n k D)
    (hR : 0 < R) (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R)
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm x₀ R σ γ M.meshSize p) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hγh : γ * M.meshSize / R ≤ 1)
    (hΩ : MeasurableSet M.domain) (x : L2F ℝ M.domain (formIdx n k))
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((((polyElement n S).globalInterp M k
        (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k x)) :
          (polyElement n S).Piecewise M k) ⟨T, hT⟩ : (polyElement n S).space T k) :
          FormField n) y s.1) ^ 2 ≤
      2 ^ n * (B * D * 2 ^ k / q ^ k) ^ 2 * (2 / (γ * σ)) ^ n *
        locMass (2 * M.meshSize) x T := by
  set h := M.meshSize
  have hh : 0 < h := hM.meshSize_pos
  have hTh : diam T ≤ h := M.diam_le_meshSize hT
  set z : FormField n := ((((polyElement n S).globalInterp M k
    (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k x)) :
      (polyElement n S).Piecewise M k) ⟨T, hT⟩ : (polyElement n S).space T k) : FormField n)
  have hz : z ∈ S.space n k := ((((polyElement n S).globalInterp M k
    (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k x)) :
      (polyElement n S).Piecewise M k) ⟨T, hT⟩ : (polyElement n S).space T k)).2
  set L := locMass (2 * h) x T
  have hL := locMass_nonneg (2 * h) x T
  set A := 2 ^ k * √((1 / (γ * h * σ)) ^ n * L)
  have hA0 : 0 ≤ A := by positivity
  -- the degrees of freedom of `z` are `O(hᵏ A)`, hence `|z| ≤ B D A / qᵏ` on `T`
  have hdof : ∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ h ^ k * (D * A) := by
    intro g hgT i
    rw [show S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ = S.dof g k i
      (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k x)) from
      (polyElement n S).localDof_globalInterp M k _ ⟨T, hT⟩ g hgT i]
    refine (abs_polyDof_le S hD hgT i _ hA0
      (hp.abs_smoothForm_le_locMass hh hR hRx hγ hγ1 hσ hσ1 hγh hΩ x hT)).trans ?_
    calc D * diam T ^ k * A ≤ D * h ^ k * A :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (diam_nonneg T) hTh k) hD0) hA0
      _ = h ^ k * (D * A) := by ring
  have hzb : ∀ y ∈ T.closedInterior, ∀ s, |z y s| ≤ B * (D * A) / q ^ k :=
    fun y hy s => abs_le_of_abs_polyDof_le S hM hq hB hT hz (mul_nonneg hD0 hA0) hdof hy s
  calc ∑ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2
      ≤ 2 ^ n * ((2 * h) ^ n * (B * (D * A) / q ^ k) ^ 2) :=
        sum_integral_sq_le_of_abs_le hT (PolyKind.contDiff_of_mem_space hz).continuous hzb
    _ = 2 ^ n * (B * D * 2 ^ k / q ^ k) ^ 2 * (2 * h * (1 / (γ * h * σ))) ^ n * L := by
        rw [show B * (D * A) / q ^ k = (B * D / q ^ k) * A by ring, mul_pow (B * D / q ^ k) A,
          mul_pow (2 ^ k), Real.sq_sqrt (by positivity), mul_pow (2 * h),
          show B * D * 2 ^ k / q ^ k = (B * D / q ^ k) * 2 ^ k by ring]
        ring
    _ = 2 ^ n * (B * D * 2 ^ k / q ^ k) ^ 2 * (2 / (γ * σ)) ^ n * L := by
        rw [show 2 * h * (1 / (γ * h * σ)) = 2 / (γ * σ) by field_simp]

theorem exists_norm_polySmoothedInterp_le [NeZero n] {C c q : ℝ} (hc : 0 < c) (hq : 0 < q)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ K, 0 ≤ K ∧ ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩ : MeasurableSet M.domain),
      0 < R → (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) → γ * M.meshSize / R ≤ 1 →
      ∀ (p : SmoothingParam (Fin n → ℝ)), IsAdm x₀ R σ γ M.meshSize p →
      ∀ (k : ℕ) (x : L2F ℝ M.domain (formIdx n k)),
        ‖(polyElement n S).smoothedInterp M p hΩ k x‖ ≤ K * ‖x‖ := by
  choose B hB0 hB using fun k : ℕ => exists_polyDofBound (n := n) S k C c
  choose D hD0 hD using fun k : ℕ => exists_polyCoeffBound (n := n) S k
  have hG : ∀ k, 0 ≤ 2 ^ n * (B k * D k * 2 ^ k / q ^ k) ^ 2 * (2 / (γ * σ)) ^ n *
      covConst n c q := fun k => by
    have := hB0 k; have := hD0 k; simp only [covConst]; positivity
  refine ⟨_, Real.sqrt_nonneg _, fun M hM hΩ hR hRx hγh p hp k x =>
    norm_le_sqrt_sum_of_sq_le hG fun _ => ?_⟩
  rw [(polyElement n S).smoothedInterp_natCast, mul_assoc]
  exact norm_sq_glue_le_locMass _ hM hc hq hΩ x _ (by have := hB0 k; have := hD0 k; positivity)
    fun T hT => sum_integral_sq_polyInterp_le S hM hq (hB k) (hD0 k) (hD k) hR hRx hp hγ hγ1
      hσ hσ1 hγh hΩ x hT

end Bound

/-! ### Closeness of the smoothed interpolants to the identity on `Vₕ` -/

section Close

variable (S : PolySeq) {x₀ : Fin n → ℝ} {R σ γ : ℝ}

/-- The geometric condition: near the points of a face `g`, every sampled simplex contains `g`. -/
def PolyGeomOK (M : SimplicialMesh n) (p : SmoothingParam (Fin n → ℝ)) (θ : ℝ) : Prop :=
  ∀ (T : M.simplices) (g : Finset (Fin n → ℝ)),
    g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) → ∀ {m : ℕ}, #g = m + 1 →
    ∀ ξ ∈ FiniteElement.refSimplex m, ξ ∉ nearBdry m θ →
      ∀ t, dist t (p.center + p.factor • (simplexMap (lexEnum g m) ξ - p.center)) <
        p.bump.rOut → ∀ T' : M.simplices,
        t ∈ interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior →
        g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n)

/-- The sampling condition: samples outside `Ω` near a face `g` force its subface DOFs to vanish. -/
def PolySampleOK {M : SimplicialMesh n} {k : ℕ} (p : SmoothingParam (Fin n → ℝ)) (θ : ℝ)
    (u : (polyElement n S).Piecewise M k) : Prop :=
  ∀ (T : M.simplices) (g : Finset (Fin n → ℝ)),
    g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) → ∀ {m : ℕ}, #g = m + 1 →
    ∀ ξ ∈ FiniteElement.refSimplex m, ξ ∉ nearBdry m θ →
      ∀ t, dist t (p.center + p.factor • (simplexMap (lexEnum g m) ξ - p.center)) <
        p.bump.rOut → t ∉ M.domain →
        ∀ g' ⊆ g, ∀ i : S.DofIdx g' k, (polyElement n S).localDof T k g' i (u T) = 0

open Classical in
theorem sqrt_mul_abs_polyIntegrand_le {M : SimplicialMesh n} (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundV M (S.space n k) A) {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hh : 0 < M.meshSize) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ}
    (hgeom : PolyGeomOK M p θ) {u : (polyElement n S).Piecewise M k}
    (hu : u ∈ (polyElement n S).globalSpace M k) (hs : PolySampleOK S p θ u) (T : M.simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)) {m : ℕ}
    (hg : #g = m + 1) {ξ : Fin m → ℝ} (hξ : ξ ∈ FiniteElement.refSimplex m)
    (c : Finset (Fin n) → ℝ)
    (hc : ∀ α β : Finset (Fin n) → ℝ, IsDeg k α → IsDeg k β →
      pullback (simplexMatrix (lexEnum g m)) α = pullback (simplexMatrix (lexEnum g m)) β →
        ∑ s, α s * c s = ∑ s, β s * c s) :
    √M.meshSize ^ n * |∑ s, (((u T : (polyElement n S).space T k) : FormField n)
        (simplexMap (lexEnum g m) ξ) s -
      (smoothForm p hΩ k ((polyElement n S).glue M k u) : FormField n)
        (simplexMap (lexEnum g m) ξ) s) * c s| ≤
      (∑ s, |c s|) * A *
        √(locMass (2 * M.meshSize) ((polyElement n S).glue M k u)
          (T : Affine.Simplex ℝ (Fin n → ℝ) n)) *
        2 ^ (k + 1) * (if ξ ∈ nearBdry m θ then 1 else (k + 1) * (2 * γ)) := by
  set h := M.meshSize
  have hγ1 : γ ≤ 1 := by linarith
  have hγh : γ * h / R ≤ 1 := by
    rw [div_le_one hR]; nlinarith
  set q := lexEnum g m
  set x := simplexMap q ξ
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  set L := locMass (2 * h) ((polyElement n S).glue M k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
    simplexMap_lexEnum_mem hgT hg hξ
  have hxc : x ∈ closure M.domain := M.closedInterior_subset_closure T.2 hxT
  -- the local fields near `x` obey the inverse estimates against the local mass of `T`
  have hinv : ∀ T' : M.simplices, (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆
      Metric.cthickening (2 * h) (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior →
      (∀ y ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
        √h ^ n * |((u T' : (polyElement n S).space T' k) : FormField n) y s| ≤ A * √L) ∧
      ∀ y ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        ∀ y' ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
        √h ^ n * h * |((u T' : (polyElement n S).space T' k) : FormField n) y s -
          ((u T' : (polyElement n S).space T' k) : FormField n) y' s| ≤ A * ‖y - y'‖ * √L := by
    intro T' hsub
    have hL' := Real.sqrt_le_sqrt (sum_integral_sq_le_of_subset (polyElement n S) hΩ hint u
      T' hsub)
    obtain ⟨h1, h2⟩ := hA T' T'.2 _ (u T').2
    exact ⟨fun y hy s => (h1 y hy s).trans (mul_le_mul_of_nonneg_left hL' hA0),
      fun y hy y' hy' s => (h2 y hy y' hy' s).trans
        (mul_le_mul_of_nonneg_left hL' (by positivity))⟩
  refine sqrt_mul_abs_sum_sub_smoothForm_le hΩ p _ x (uT x) c (ξ ∈ nearBdry m θ)
    (pow_pos (Real.sqrt_pos.2 hh) n) hA0 (by positivity) (hp.pow_factor_le hγh k)
    ((hp.abs_one_sub_pow_le hR hγh k).trans (mul_le_mul_of_nonneg_left
      (by rw [div_le_iff₀ hR]; nlinarith) (by positivity)))
    (fun s => (hinv T (Metric.self_subset_cthickening _)).1 x hxT s) ?_ ?_
  · filter_upwards [ae_extField_glue_eq (polyElement n S) u hΩ] with t ht hdist htΩ
    obtain ⟨T', htT', hext⟩ := ht htΩ
    set u' : FormField n := ((u T' : (polyElement n S).space T' k) : FormField n)
    have hu' : u' ∈ S.space n k := (u T').2
    have htT'c : t ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := interior_subset htT'
    have hxt' : ‖t - x‖ ≤ 2 * (γ * h) := hp.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) hdist.le
    obtain ⟨hb1, hb2⟩ := hinv T' (closedInterior_subset_cthickening hh hγ2 hxT htT'c T'.2 hxt')
    refine ⟨u', hext, fun s => hb1 t htT'c s, fun hbad => ?_⟩
    have hgT' : g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) :=
      hgeom T g hgT hg ξ hξ hbad t hdist T' htT'
    have hxT' := simplexMap_lexEnum_mem hgT' hg hξ
    refine ⟨hc _ _ (PolyKind.isDeg_of_mem_space huT x) (PolyKind.isDeg_of_mem_space hu' x)
      (PolySeq.pullback_eq_of_mem_globalSpace hu T T' hgT hgT' hg ξ), fun s => hb1 x hxT' s,
      fun s => ?_⟩
    refine le_of_mul_le_mul_right ?_ hh
    calc √h ^ n * |u' x s - u' t s| * h = √h ^ n * h * |u' x s - u' t s| := by ring
      _ ≤ A * ‖x - t‖ * √L := hb2 x hxT' t htT'c s
      _ ≤ A * (2 * (γ * h)) * √L := by rw [norm_sub_rev]; gcongr
      _ = 2 * γ * (A * √L) * h := by ring
  · intro hbad t hdist htΩ
    have h0 := hs T g hgT hg ξ hξ hbad t hdist htΩ
    have hpb : pullback (simplexMatrix q) (uT x) =
        pullback (simplexMatrix q) ((0 : FormField n) x) :=
      S.pullback_eq_of_dof_eq hgT hg huT (Submodule.zero_mem _) (fun g' hg' i => by
        rw [show (⟨(0 : FormField n), S.space_le_contForms n k (Submodule.zero_mem _)⟩ :
          contForms n) = 0 from rfl, map_zero]
        exact h0 g' hg' i) ξ
    rw [hc _ _ (PolyKind.isDeg_of_mem_space huT x) (fun s _ => rfl) hpb]
    simp

theorem sqrt_mul_abs_polyDof_err_le {M : SimplicialMesh n} (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A D : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundV M (S.space n k) A) (hD0 : 0 ≤ D)
    (hD : PolyCoeffBound S n k D) {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hh : 0 < M.meshSize) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hgeom : PolyGeomOK M p θ) {u : (polyElement n S).Piecewise M k}
    (hu : u ∈ (polyElement n S).globalSpace M k) (hs : PolySampleOK S p θ u) (T : M.simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (i : S.DofIdx g k) :
    √M.meshSize ^ n * |S.dof g k i ⟨((u T : (polyElement n S).space T k) : FormField n),
        S.space_le_contForms n k (u T).2⟩ -
      S.dof g k i (Submodule.inclusion c1Forms_le_contForms
        (smoothForm p hΩ k ((polyElement n S).glue M k u)))| ≤
      2 * (n + 1) * D * 2 ^ (k + 1) * A * (γ + θ) * M.meshSize ^ k *
        √(locMass (2 * M.meshSize) ((polyElement n S).glue M k u)
          (T : Affine.Simplex ℝ (Fin n → ℝ) n)) := by
  classical
  set h := M.meshSize
  have hne := i.2
  set m := #g - 1
  have hg : #g = m + 1 := (Nat.succ_pred_eq_of_pos (card_pos.2 hne)).symm
  have hkm : k ≤ m := by have := S.card_le_of_dofIdx i; omega
  have hmn : m ≤ n := by
    have := Finset.card_le_card hgT
    rw [card_vertexSet] at this; omega
  set q := lexEnum g m
  set η := (S.testBasis k m i.1 : FormField m)
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  set w : c1Forms n := smoothForm p hΩ k ((polyElement n S).glue M k u)
  set L := locMass (2 * h) ((polyElement n S).glue M k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have huc : Continuous uT := (PolyKind.contDiff_of_mem_space huT).continuous
  have hwc : Continuous (w : FormField n) := (mem_c1Forms.1 w.2).continuous
  set F : (Fin m → ℝ) → ℝ := fun ξ =>
    ∑ s, (uT (simplexMap q ξ) s - (w : FormField n) (simplexMap q ξ) s) * dofCoeff q η k ξ s
  have hdc : Continuous fun ξ : Fin m → ℝ => η ξ := S.continuous_testBasis k m i.1
  have hcoef : ∀ s, Continuous fun ξ => dofCoeff q η k ξ s := fun s => by
    simp only [dofCoeff]
    split_ifs
    · simp only [wedgeForm_apply]
      exact continuous_finsetSum _ fun a _ => continuous_const.mul
        ((continuous_apply _).comp hdc)
    · exact continuous_const
  have hFc : Continuous F := continuous_finsetSum _ fun s _ =>
    ((((continuous_apply s).comp (huc.comp (continuous_simplexMap q))).sub
      ((continuous_apply s).comp (hwc.comp (continuous_simplexMap q)))).mul (hcoef s))
  have herr : S.dof g k i ⟨uT, S.space_le_contForms n k huT⟩ -
      S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) =
        ∫ ξ in FiniteElement.refSimplex m, F ξ := by
    rw [← map_sub, S.dof_eq_integral]
    refine setIntegral_congr_fun (measurableSet_refSimplex _) fun ξ _ => ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    rfl
  set Mc := D * h ^ k
  have hMc : ∀ ξ ∈ FiniteElement.refSimplex m, ∑ s, |dofCoeff q η k ξ s| ≤ Mc :=
    fun ξ hξ => (hD hgT i ξ hξ).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (diam_nonneg _) (M.diam_le_meshSize T.2) k) hD0)
  set c := Mc * A * √L * 2 ^ (k + 1)
  have hc0 : 0 ≤ c := by positivity
  rw [herr]
  refine (mul_abs_integral_refSimplex_le hFc (pow_nonneg (Real.sqrt_nonneg _) n) hc0
    (by positivity) hθ0 hθ1 fun ξ hξ =>
      (sqrt_mul_abs_polyIntegrand_le S hΩ hint hA0 hA hp hR hRx hhR hh hγ hγ2 hσ1 hgeom hu
        hs T hgT hg hξ (dofCoeff q η k ξ)
        (fun α β hα hβ hαβ => sum_mul_dofCoeff_eq_of_pullback_eq q η ξ hα hβ hαβ)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hMc ξ hξ) hA0) (Real.sqrt_nonneg _)) (by positivity))
        (by split_ifs <;> positivity))).trans ?_
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hkm.trans hmn
  have hm' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  calc c * ((k + 1) * (2 * γ) + (m + 1) * θ) ≤ c * (2 * (n + 1) * (γ + θ)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hc0
    _ = _ := by simp only [c, Mc]; ring

theorem sum_integral_sq_sub_polyInterp_le {M : SimplicialMesh n} [NeZero n] {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A B D : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundV M (S.space n k) A) (hB : PolyDofBound S n k C c B)
    (hD0 : 0 ≤ D) (hD : PolyCoeffBound S n k D) {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hgeom : PolyGeomOK M p θ) {u : (polyElement n S).Piecewise M k}
    (hu : u ∈ (polyElement n S).globalSpace M k) (hs : PolySampleOK S p θ u)
    (T : M.simplices) :
    ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      ((((u T : (polyElement n S).space T k) : FormField n) -
        ((((polyElement n S).globalInterp M k
          (Submodule.inclusion c1Forms_le_contForms
            (smoothForm p hΩ k ((polyElement n S).glue M k u))) :
            (polyElement n S).Piecewise M k) T : (polyElement n S).space T k) :
              FormField n)) y s.1) ^ 2 ≤
      4 ^ n * (B * (2 * (n + 1) * D * 2 ^ (k + 1) * A) * (γ + θ) / q ^ k) ^ 2 *
        locMass (2 * M.meshSize) ((polyElement n S).glue M k u)
          (T : Affine.Simplex ℝ (Fin n → ℝ) n) := by
  set h := M.meshSize
  have hh : 0 < h := hM.meshSize_pos
  set w := smoothForm p hΩ k ((polyElement n S).glue M k u)
  set Pw : (polyElement n S).space T k := (((polyElement n S).globalInterp M k
    (Submodule.inclusion c1Forms_le_contForms w) : (polyElement n S).Piecewise M k) T)
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  have hPw : (Pw : FormField n) ∈ S.space n k := Pw.2
  set z : FormField n := uT - (Pw : FormField n)
  have hz : z ∈ S.space n k := Submodule.sub_mem _ huT hPw
  set L := locMass (2 * h) ((polyElement n S).glue M k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hL0 : 0 ≤ L := locMass_nonneg _ _ _
  set C₁ := 2 * (n + 1) * D * 2 ^ (k + 1) * A
  have hC₁ : 0 ≤ C₁ := by positivity
  have hsq : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  have hγθ : 0 ≤ γ + θ := by linarith
  set D'' := C₁ * (γ + θ) * √L / √h ^ n
  have hD''0 : 0 ≤ D'' := by positivity
  have hdof : ∀ g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n), ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ h ^ k * D'' := by
    intro g hgT i
    have e1 : S.dof g k i ⟨(Pw : FormField n), S.space_le_contForms n k hPw⟩ =
        S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) :=
      (polyElement n S).localDof_globalInterp M k
        (Submodule.inclusion c1Forms_le_contForms w) T g hgT i
    have e : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ =
        S.dof g k i ⟨uT, S.space_le_contForms n k huT⟩ -
          S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) := by
      rw [← e1, ← map_sub]; rfl
    rw [e]
    have h1 := sqrt_mul_abs_polyDof_err_le S hΩ hint hA0 hA hD0 hD hp hR hRx hhR hh hγ hγ2 hσ1
      hθ0 hθ1 hgeom hu hs T hgT i
    have e2 : h ^ k * D'' = C₁ * (γ + θ) * h ^ k * √L / √h ^ n := by
      simp only [D'']; ring
    rw [e2, le_div_iff₀ hsq, mul_comm]
    refine h1.trans (le_of_eq ?_)
    simp only [C₁]; ring
  have hzb : ∀ y ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
      |z y s| ≤ B * D'' / q ^ k :=
    fun y hy s => abs_le_of_abs_polyDof_le S hM hq hB T.2 hz hD''0 hdof hy s
  have hhn : h ^ n = (√h ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hh.le]
  calc ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        (z y s.1) ^ 2
      ≤ 2 ^ n * ((2 * h) ^ n * (B * D'' / q ^ k) ^ 2) :=
        sum_integral_sq_le_of_abs_le T.2 (PolyKind.contDiff_of_mem_space hz).continuous hzb
    _ = 4 ^ n * (B * C₁ * (γ + θ) / q ^ k) ^ 2 * (√L) ^ 2 := by
        rw [mul_pow 2 h, hhn, show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by
          rw [← mul_pow]; norm_num]
        simp only [D'']
        field_simp
    _ = 4 ^ n * (B * C₁ * (γ + θ) / q ^ k) ^ 2 * L := by rw [Real.sq_sqrt hL0]

theorem norm_sq_sub_polySmoothedInterp_le {M : SimplicialMesh n} [NeZero n] {C c q : ℝ}
    (hM : MeshData M C c q) (hc : 0 < c) (hq : 0 < q) (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A B D : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundV M (S.space n k) A) (hB : PolyDofBound S n k C c B)
    (hD0 : 0 ≤ D) (hD : PolyCoeffBound S n k D) {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hgeom : PolyGeomOK M p θ) {u : (polyElement n S).Piecewise M k}
    (hu : u ∈ (polyElement n S).globalSpace M k) (hs : PolySampleOK S p θ u) :
    ‖(polyElement n S).glue M k u - (polyElement n S).smoothedInterp M p hΩ k
        ((polyElement n S).glue M k u)‖ ^ 2 ≤
      4 ^ n * (B * (2 * (n + 1) * D * 2 ^ (k + 1) * A) * (γ + θ) / q ^ k) ^ 2 *
        (covConst n c q * ‖(polyElement n S).glue M k u‖ ^ 2) := by
  set v := (polyElement n S).glue M k u
  have hQ := (polyElement n S).smoothedInterp_natCast M p hΩ k v
  set Pw := (polyElement n S).globalInterp M k (Submodule.inclusion c1Forms_le_contForms
    (smoothForm p hΩ k v))
  set d : (polyElement n S).Piecewise M k := u - (Pw : (polyElement n S).Piecewise M k)
  have hsub : v - (polyElement n S).smoothedInterp M p hΩ k v =
      (polyElement n S).glue M k d := by
    rw [hQ, map_sub]
  rw [hsub]
  exact norm_sq_glue_le_locMass _ hM hc hq hΩ v d (by positivity) fun T hT =>
    sum_integral_sq_sub_polyInterp_le S hM hq hΩ hint hA0 hA hB hD0 hD hp hR hRx hhR hγ
      hγ2 hσ1 hθ0 hθ1 hgeom hu hs ⟨T, hT⟩

end Close

/-! ### The geometric and sampling conditions for both families -/

section Families

variable (S : PolySeq) {x₀ : Fin n → ℝ} {s₀ R σ γ : ℝ}

theorem isFacePoint_lexEnum {M : SimplicialMesh n} {m : ℕ} {g : Finset (Fin n → ℝ)}
    (hg : #g = m + 1) {θ : ℝ} {ξ : Fin m → ℝ} (hξ : ξ ∉ nearBdry m θ) :
    StarGeom.IsFacePoint M g θ (simplexMap (lexEnum g m) ξ) := by
  rw [simplexMap_eq_sum]
  refine StarGeom.isFacePoint_sum_smul (lexEnum_injective hg) (range_lexEnum hg)
    (fun a => ?_) (sum_refBary ξ)
  by_contra hlt; push Not at hlt; exact hξ ⟨a, hlt⟩

theorem polyGeomOK_of_isMaximal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀)
    (hs₀ : 0 < s₀) {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMaximal x₀ s₀)
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hγ : 0 < γ) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) : PolyGeomOK M p θ := by
  intro T g hgT _ hg ξ hξ hξb _ ht _ htT'
  exact subset_vertexSet_of_isMaximal hM hq hC hstar hs₀ hp hpA hR hRx hσ1 hγ hθ hgT
    (isFacePoint_lexEnum hg hξb) (simplexMap_lexEnum_mem hgT hg hξ) ht htT'

theorem polyGeomOK_of_isMinimal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀)
    (hs₀ : 0 < s₀) (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain)
    {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMinimal x₀ s₀)
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hσ : σ ≤ s₀ / (8 * R))
    (hγ : 0 < γ) (hγh : γ * M.meshSize / R < 1) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) : PolyGeomOK M p θ := by
  intro T g hgT _ hg ξ hξ hξb _ ht _ htT'
  exact subset_vertexSet_of_isMinimal hM hq hC hstar hs₀ hint hp hpA hR hRx hσ1 hσ hγ hγh hθ hgT
    (isFacePoint_lexEnum hg hξb) (simplexMap_lexEnum_mem hgT hg hξ) ht htT'

theorem polySampleOK_of_isMaximal {M : SimplicialMesh n} (hstar : StarBall M.domain x₀ s₀)
    {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMaximal x₀ s₀) {θ : ℝ} {k : ℕ}
    (u : (polyElement n S).Piecewise M k) : PolySampleOK S p θ u := by
  intro T g hgT m hg ξ hξ _ t ht htΩ
  exfalso
  have hxT := simplexMap_lexEnum_mem hgT hg hξ
  have hxc := M.closedInterior_subset_closure T.2 hxT
  have := closedBall_dil_subset_of_starBall hstar p.half_le_factor hp.factor_lt_one hp.rOut_lt hxc
  rw [← hp.center_eq] at this
  exact htΩ (this (Metric.mem_closedBall.2 ht.le))

theorem polySampleOK_of_isMinimal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀)
    (hs₀ : 0 < s₀) {p : SmoothingParam (Fin n → ℝ)}
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hγ : 0 < γ) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) {k : ℕ}
    {u : (polyElement n S).Piecewise M k} (hu : u ∈ (polyElement n S).globalSpace₀ M k) :
    PolySampleOK S p θ u := by
  classical
  intro T g hgT m hg ξ hξ hξb t ht htΩ
  have hh := hM.meshSize_pos
  set x := simplexMap (lexEnum g m) ξ
  have hx := isFacePoint_lexEnum (M := M) hg hξb
  have hxT := simplexMap_lexEnum_mem hgT hg hξ
  have hxc := M.closedInterior_subset_closure T.2 hxT
  have ht' : ‖t - x‖ ≤ 2 * (γ * M.meshSize) :=
    hpA.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) ht.le
  have htc : t ∉ interior (closure M.domain) := fun h' =>
    htΩ (hstar.interior_closure_subset hs₀ h')
  obtain ⟨F, hF, hgF⟩ := StarGeom.exists_isBoundaryFacet_of_near (by positivity)
    (coordLip_of hM hq hC) hx T.2 hgT hxT htc (coord_near hq hC hh hγ hθ ht')
  obtain ⟨-, T'', hT'', hFT''⟩ := hF.1
  intro g' hg' j
  have h0 := hu.2 ⟨T'', hT''⟩ F hF hFT'' g' (hg'.trans hgF) j
  rw [hu.1 T ⟨T'', hT''⟩ g' (hg'.trans hgT) ((hg'.trans hgF).trans hFT'') j]
  exact h0

end Families

/-! ### The smoothing scale and the uniformly bounded cochain projections -/

section Estimates

variable (S : PolySeq) {x₀ : Fin n → ℝ}

variable (n) in
theorem exists_polyGamma [NeZero n] {C c q : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hq : 0 < q) :
    ∃ γ₀ K₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 4 ∧ 2 * (n * ((n + 1) * C)) / q < K₀ ∧
      ∀ γ, 0 < γ → γ ≤ γ₀ →
      ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩ : MeasurableSet M.domain),
      (∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) →
      ∀ {R σ : ℝ}, 0 < R → (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) → M.meshSize ≤ 2 * R →
      σ ≤ 1 → ∀ (p : SmoothingParam (Fin n → ℝ)), IsAdm x₀ R σ γ M.meshSize p →
      PolyGeomOK M p (K₀ * γ) → ∀ (k : ℕ), ∀ u ∈ (polyElement n S).globalSpace M k,
        PolySampleOK S p (K₀ * γ) u →
        ‖(polyElement n S).glue M k u - (polyElement n S).smoothedInterp M p hΩ k
          ((polyElement n S).glue M k u)‖ ≤ 1 / 2 * ‖(polyElement n S).glue M k u‖ := by
  classical
  choose A hA0 hA using fun k : ℕ => exists_polyInvBound (n := n) S k hC hc
  choose B hB0 hB using fun k : ℕ => exists_polyDofBound (n := n) S k C c
  choose D hD0 hD using fun k : ℕ => exists_polyCoeffBound (n := n) S k
  set K₀ : ℝ := 2 * (n * ((n + 1) * C)) / q + 1
  have hK₀ : 1 ≤ K₀ := by
    simp only [K₀]; have : 0 ≤ 2 * (n * ((n + 1) * C)) / q := by positivity
    linarith
  set A' : ℕ → ℝ := fun k => A k / √q ^ n / q
  have hA'0 : ∀ k, 0 ≤ A' k := fun k => by have := hA0 k; simp only [A']; positivity
  set x : ℕ → ℝ := fun k =>
    B k * (2 * (n + 1) * D k * 2 ^ (k + 1) * A' k) * (1 + K₀) / q ^ k
  have hx0 : ∀ k, 0 ≤ x k := fun k => by
    have := hB0 k; have := hA'0 k; have := hD0 k; simp only [x]; positivity
  set Sx := ∑ k ∈ Finset.range (n + 1), x k
  have hS : 0 ≤ Sx := Finset.sum_nonneg fun k _ => hx0 k
  set Kc : ℝ := max 1 (4 ^ n * covConst n c q)
  have hKc : 1 ≤ Kc := le_max_left _ _
  set γ₁ := 1 / (2 * (1 + Sx * Kc))
  have hpos : 0 < 1 + Sx * Kc := by nlinarith
  have hγ₁ : 0 < γ₁ := by positivity
  set γ₀ := min (min (1 / 4) (1 / K₀)) γ₁
  refine ⟨γ₀, K₀, lt_min (lt_min (by norm_num) (by positivity)) hγ₁,
    (min_le_left _ _).trans (min_le_left _ _), lt_add_one _, fun γ hγ hγγ₀ => ?_⟩
  have hγ4 : γ ≤ 1 / 4 := hγγ₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγK : γ ≤ 1 / K₀ := hγγ₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγγ₀ : γ ≤ γ₁ := hγγ₀.trans (min_le_right _ _)
  intro M hM hΩ hint R σ hR hRx hhR hσ1 p hp hgeom k u hu hs
  by_cases hk : n < k
  · have := subsingleton_L2F_of_lt (Ω := M.domain) hk
    rw [Subsingleton.elim ((polyElement n S).glue M k u) 0]; simp
  push Not at hk
  have hInv := invBoundV_of hM hq (hA0 k) (hA k)
  have hθ0 : 0 ≤ K₀ * γ := by positivity
  have hθ1 : K₀ * γ ≤ 1 := by
    calc K₀ * γ ≤ K₀ * (1 / K₀) := mul_le_mul_of_nonneg_left hγK (by linarith)
      _ = 1 := by field_simp
  have h := norm_sq_sub_polySmoothedInterp_le S hM hc hq hΩ hint (hA'0 k) hInv (hB k) (hD0 k)
    (hD k) hp hR hRx hhR hγ (by linarith) hσ1 hθ0 hθ1 hgeom hu hs
  have hxk : x k ≤ Sx := Finset.single_le_sum (fun k _ => hx0 k) (Finset.mem_range.2 (by omega))
  have he : B k * (2 * (n + 1) * D k * 2 ^ (k + 1) * A' k) * (γ + K₀ * γ) /
      q ^ k = x k * γ := by simp only [x]; ring
  rw [he] at h
  have hq1 : 4 ^ n * (x k * γ) ^ 2 * covConst n c q ≤ 1 / 4 := by
    have h1 : 4 ^ n * (x k * γ) ^ 2 * covConst n c q ≤ Kc * (x k * γ₁) ^ 2 := by
      have hcov : 0 ≤ covConst n c q := by unfold covConst; positivity
      calc 4 ^ n * (x k * γ) ^ 2 * covConst n c q = (4 ^ n * covConst n c q) * (x k * γ) ^ 2 := by
            ring
        _ ≤ Kc * (x k * γ₁) ^ 2 := mul_le_mul (le_max_right _ _)
            (pow_le_pow_left₀ (by have := hx0 k; positivity)
              (mul_le_mul_of_nonneg_left hγγ₀ (hx0 k)) 2) (sq_nonneg _) (by linarith)
    exact h1.trans (sq_le_quarter hS hKc (hx0 k) hxk)
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (h.trans ?_)
  calc 4 ^ n * (x k * γ) ^ 2 * (covConst n c q * ‖(polyElement n S).glue M k u‖ ^ 2)
      = (4 ^ n * (x k * γ) ^ 2 * covConst n c q) * ‖(polyElement n S).glue M k u‖ ^ 2 := by ring
    _ ≤ 1 / 4 * ‖(polyElement n S).glue M k u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hq1 (sq_nonneg _)
    _ = (1 / 2 * ‖(polyElement n S).glue M k u‖) ^ 2 := by ring

/-- Uniformly bounded smoothed cochain projections onto the complexes of an admissible sequence on
quasi-uniform shape-regular meshes. [AFW2010], §5.5; [ChristiansenWinther2008] -/
theorem exists_uniform_polyCochainProjection [NeZero n] {C c q : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hq : 0 < q) {s₀ R : ℝ} (hs₀ : 0 < s₀) (hR : 0 < R) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩo : IsOpen M.domain),
      StarBall M.domain x₀ s₀ → (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) →
      ∃ π : ((polyElement n S).subcomplex M hΩo).CochainProjection,
        (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨γ, K₀, hγ, hγ4, hK₀, hclose⟩ := exists_polyGamma n S (x₀ := x₀) hC hc hq
  have hθ : 2 * (n * ((n + 1) * C)) / q * γ < K₀ * γ := mul_lt_mul_of_pos_right hK₀ hγ
  replace hclose := hclose γ hγ le_rfl
  set σ := sigmaOf s₀ R
  obtain ⟨K', hK'0, hbound⟩ := exists_norm_polySmoothedInterp_le S (x₀ := x₀) (R := R) hc hq hγ
    (by linarith) (sigmaOf_pos hs₀ hR) (sigmaOf_le_one s₀ R)
  refine ⟨max 1 (2 * K'), le_max_left _ _, fun M hM hΩo hstar hRx => ?_⟩
  set h := M.meshSize
  have hh := hM.meshSize_pos
  have hhR := meshSize_le_two_mul hR hRx
  have hγh2 : γ * h / R ≤ 1 / 2 := by
    rw [div_le_iff₀ hR]; nlinarith
  have hpos : 0 < γ * h * σ := by have := sigmaOf_pos hs₀ hR; positivity
  have hnn : 0 ≤ γ * h / R := by positivity
  set p := pMax x₀ R σ γ h hpos hγh2
  have hp : p.IsMaximal x₀ s₀ := pMax_isMaximal hR hpos hγh2 (by positivity) (sigmaOf_lt hs₀ hR)
  have hpA : IsAdm x₀ R σ γ h p := pMax_isAdm hpos hγh2 hnn
  have hint := interior_subset_domain hstar hs₀
  set Q := (polyElement n S).smoothedCommutingMap M p hΩo hstar hp
  have hQ : ∀ i, Q.Q i = (polyElement n S).smoothedInterp M p hΩo.measurableSet i :=
    fun i => rfl
  have hQb : ∀ i x, ‖Q.Q i x‖ ≤ K' * ‖x‖ := by
    intro i x
    rw [hQ]
    rcases i with k | k
    · exact hbound M hM hΩo.measurableSet hR hRx (by linarith) p hpA k x
    · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  have hQc : ∀ i, ∀ v ∈ ((polyElement n S).subcomplex M hΩo).V i,
      ‖v - Q.Q i v‖ ≤ 1 / 2 * ‖v‖ := by
    intro i v hv
    rw [hQ]
    rcases i with k | k
    · obtain ⟨u, rfl⟩ := hv
      exact hclose M hM hΩo.measurableSet hint hR hRx hhR (sigmaOf_le_one s₀ R) p hpA
        (polyGeomOK_of_isMaximal hM hq hC hstar hs₀ hp hpA hR hRx (sigmaOf_le_one s₀ R) hγ hθ)
        k u.1 u.2 (polySampleOK_of_isMaximal S hstar hp u.1)
    · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  have hb : ∀ i x, ‖(Q.toCochainProjection (θ := 1 / 2) (by norm_num) hQc).π i x‖ ≤
      max 1 (2 * K') * ‖x‖ := fun i x =>
    (Q.norm_toCochainProjection_le_two_mul hQc (hQb i) x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  exact ⟨_, hb, fun i j => (Q.toCochainProjection _ hQc).isGraphBounded_of_norm_le (hb i) (hb j)⟩

theorem exists_uniform_polyCochainProjectionMin [NeZero n] {C c q : ℝ} (hC : 0 ≤ C)
    (hc : 0 < c) (hq : 0 < q) {s₀ R : ℝ} (hs₀ : 0 < s₀) (hR : 0 < R) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩo : IsOpen M.domain),
      ∀ (hstar : StarBall M.domain x₀ s₀), (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) →
      ∃ π : ((polyElement n S).subcomplexMin M hΩo x₀
          (fun _ hx _ ht0 ht1 => hstar.strict hs₀ hx ht0 ht1)).CochainProjection,
        (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨γ, K₀, hγ, hγ4, hK₀, hclose⟩ := exists_polyGamma n S (x₀ := x₀) hC hc hq
  have hθ : 2 * (n * ((n + 1) * C)) / q * γ < K₀ * γ := mul_lt_mul_of_pos_right hK₀ hγ
  replace hclose := hclose γ hγ le_rfl
  set σ := sigmaOf s₀ R
  obtain ⟨K', hK'0, hbound⟩ := exists_norm_polySmoothedInterp_le S (x₀ := x₀) (R := R) hc hq hγ
    (by linarith) (sigmaOf_pos hs₀ hR) (sigmaOf_le_one s₀ R)
  refine ⟨max 1 (2 * K'), le_max_left _ _, fun M hM hΩo hstar hRx => ?_⟩
  set h := M.meshSize
  have hh := hM.meshSize_pos
  have hhR := meshSize_le_two_mul hR hRx
  have hγh1 : γ * h / R ≤ 1 / 2 := by
    rw [div_le_iff₀ hR]; nlinarith
  have hpos : 0 < γ * h * σ := by have := sigmaOf_pos hs₀ hR; positivity
  have hnn : 0 ≤ γ * h / R := by positivity
  set p := pMin x₀ R σ γ h hpos hnn
  have hp : p.IsMinimal x₀ s₀ := pMin_isMinimal hR hpos hnn (by positivity) (sigmaOf_lt hs₀ hR)
  have hpA : IsAdm x₀ R σ γ h p := pMin_isAdm hpos hnn
  have hint := interior_subset_domain hstar hs₀
  have hb := isBounded_domain_of hRx
  set Q := (polyElement n S).smoothedCommutingMapMin M p hΩo hb hstar hp x₀
    (fun _ hx _ ht0 ht1 => hstar.strict hs₀ hx ht0 ht1)
  have hQ : ∀ i, Q.Q i = (polyElement n S).smoothedInterp M p hΩo.measurableSet i :=
    fun i => rfl
  have hQb : ∀ i x, ‖Q.Q i x‖ ≤ K' * ‖x‖ := by
    intro i x
    rw [hQ]
    rcases i with k | k
    · exact hbound M hM hΩo.measurableSet hR hRx (by linarith) p hpA k x
    · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  have hQc : ∀ i, ∀ v ∈ ((polyElement n S).subcomplexMin M hΩo x₀
      (fun _ hx _ ht0 ht1 => hstar.strict hs₀ hx ht0 ht1)).V i,
      ‖v - Q.Q i v‖ ≤ 1 / 2 * ‖v‖ := by
    intro i v hv
    rw [hQ]
    rcases i with k | k
    · obtain ⟨u, rfl⟩ := hv
      exact hclose M hM hΩo.measurableSet hint hR hRx hhR (sigmaOf_le_one s₀ R) p hpA
        (polyGeomOK_of_isMinimal hM hq hC hstar hs₀ hint hp hpA hR hRx (sigmaOf_le_one s₀ R)
          (sigmaOf_le s₀ R) hγ (by linarith) hθ)
        k u.1 ((polyElement n S).globalSpace₀_le M k u.2)
        (polySampleOK_of_isMinimal S hM hq hC hstar hs₀ hpA hR hRx (sigmaOf_le_one s₀ R) hγ hθ
          u.2)
    · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  have hb : ∀ i x, ‖(Q.toCochainProjection (θ := 1 / 2) (by norm_num) hQc).π i x‖ ≤
      max 1 (2 * K') * ‖x‖ := fun i x =>
    (Q.norm_toCochainProjection_le_two_mul hQc (hQb i) x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  exact ⟨_, hb, fun i j => (Q.toCochainProjection _ hQc).isGraphBounded_of_norm_le (hb i) (hb j)⟩

end Estimates

end Feec.Models.StarShaped
