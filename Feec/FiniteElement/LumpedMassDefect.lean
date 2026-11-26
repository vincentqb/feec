module

public import Feec.FiniteElement.P1Global
public import Feec.ForMathlib.InnerProductSpace.IsometryDefect

/-!
# The consistent and the lumped mass of `P₁` elements

Mass lumping ([Thomee2006], Ch. 15), an inner-product crime ([HolstStern2012], §3), has a defect
`1 - iₕ* iₕ` of norm at least `n / (n + 2)` but `O(h)` from the discrete graph norm.

## Main results

* `p1Mass_le_lumpedInner`, `lumpedInner_le_mul_p1Mass`: `⟨u, u⟩ ≤ ⟨u, u⟩_L ≤ (n + 2) ⟨u, u⟩`.
* `IsLumpedReading.le_opNorm_one_sub_adjoint_comp_self`: `‖1 - i* i‖ ≥ n / (n + 2)`.
* `IsLumpedReading.norm_one_sub_adjoint_comp_self_apply_le`: `‖(1 - i* i) v‖ ≤ c_n h ‖∇(ν v)_h‖`.
* `opNorm_one_sub_adjoint_comp_self_lumpedReading_freudenthalMesh`: `(n + 1) / (n + 2)`.

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012], §3

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MeasureTheory
open scoped InnerProductSpace

@[expose] public noncomputable section

namespace Feec.FiniteElement

open Feec.Mesh Feec.Domain

variable {n : ℕ}

/-! ### The element masses -/

theorem integral_baryCoord_mul_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i j : Fin (n + 1)) :
    ∫ x in T.closedInterior, baryCoord T.points x i * baryCoord T.points x j =
      |LinearMap.det T.linearPart| *
        ∫ y in FiniteElement.refSimplex n, refBary y i * refBary y j := by
  rw [integral_closedInterior_eq, refSimplex_closedInterior_eq]
  simp only [baryCoord_refMap]

theorem integral_baryCoord_mul_perm (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (π : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    ∫ x in T.closedInterior, baryCoord T.points x (π i) * baryCoord T.points x (π j) =
      ∫ x in T.closedInterior, baryCoord T.points x i * baryCoord T.points x j :=
  integral_comp_baryCoord_perm T π fun l => l i * l j

theorem integral_baryCoord_mul_self (T : Affine.Simplex ℝ (Fin n → ℝ) n) (j : Fin (n + 1)) :
    ∫ x in T.closedInterior, baryCoord T.points x j * baryCoord T.points x j =
      2 * volume.real T.closedInterior / ((n + 1) * (n + 2)) := by
  rw [← Equiv.swap_apply_left 0 j, integral_baryCoord_mul_perm, integral_baryCoord_mul_eq]
  have e : ∫ y in FiniteElement.refSimplex n, refBary y 0 * refBary y 0 =
      ∫ y in FiniteElement.refSimplex n, (1 - ∑ i, y i) ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => by simp [refBary, sq])
  rw [e, setIntegral_refSimplex_one_sub_sum_pow, volume_real_closedInterior,
    Nat.factorial_two, add_comm 2 n, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem integral_baryCoord_mul (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i j : Fin (n + 1)) :
    ∫ x in T.closedInterior, baryCoord T.points x i * baryCoord T.points x j =
      (if i = j then 2 else 1) * volume.real T.closedInterior / ((n + 1) * (n + 2)) := by
  split_ifs with hij
  · subst hij; exact integral_baryCoord_mul_self T i
  have hint : ∀ k, IntegrableOn (fun x => baryCoord T.points x i * baryCoord T.points x k)
      T.closedInterior :=
    fun k => ((continuous_baryCoord T.points i).mul
      (continuous_baryCoord T.points k)).continuousOn.integrableOn_compact
        T.isCompact_closedInterior
  -- every `k ≠ i` gives the same integral as `j`
  have hk : ∀ k ∈ (univ.erase i : Finset (Fin (n + 1))),
      ∫ x in T.closedInterior, baryCoord T.points x i * baryCoord T.points x k =
        ∫ x in T.closedInterior, baryCoord T.points x i * baryCoord T.points x j := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have e := integral_baryCoord_mul_perm T (Equiv.swap j k) i j
    rw [Equiv.swap_apply_of_ne_of_ne hij (Ne.symm hki), Equiv.swap_apply_left] at e
    exact e
  -- `Σₖ ∫ λᵢ λₖ = ∫ λᵢ`
  have hsum : ∑ k, ∫ x in T.closedInterior, baryCoord T.points x i * baryCoord T.points x k =
      volume.real T.closedInterior / (n + 1) := by
    rw [← integral_finsetSum _ fun k _ => hint k, ← integral_baryCoord T i]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ∑ k, baryCoord T.points x i * baryCoord T.points x k = baryCoord T.points x i
    rw [← Finset.mul_sum, sum_baryCoord, mul_one]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Finset.sum_congr rfl hk,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, integral_baryCoord_mul_self, nsmul_eq_mul] at hsum
  have hn : (n : ℝ) ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hij
    · exact_mod_cast h.ne'
  set V := volume.real T.closedInterior
  set I := ∫ x in T.closedInterior, baryCoord T.points x i * baryCoord T.points x j
  push_cast at hsum
  have e2 : V / (n + 1) - 2 * V / ((n + 1) * (n + 2)) = (n : ℝ) * (V / ((n + 1) * (n + 2))) := by
    field_simp
    ring
  have e3 : (n : ℝ) * I = (n : ℝ) * (V / ((n + 1) * (n + 2))) := by
    rw [← e2]
    linarith
  rw [one_mul]
  exact mul_left_cancel₀ hn e3

theorem integral_p1Interp_mul (T : Affine.Simplex ℝ (Fin n → ℝ) n) (u w : (Fin n → ℝ) → ℝ) :
    ∫ x in T.closedInterior, p1Interp T.points u x * p1Interp T.points w x =
      volume.real T.closedInterior * (∑ j, u (T.points j) * w (T.points j) +
        (∑ j, u (T.points j)) * ∑ j, w (T.points j)) / ((n + 1) * (n + 2)) := by
  have hint : ∀ i j, IntegrableOn (fun x => u (T.points i) * baryCoord T.points x i *
      (w (T.points j) * baryCoord T.points x j)) T.closedInterior := fun i j =>
    (((continuous_const.mul (continuous_baryCoord T.points i)).mul
      (continuous_const.mul (continuous_baryCoord T.points j))).continuousOn.integrableOn_compact
        T.isCompact_closedInterior)
  have e : ∀ x, p1Interp T.points u x * p1Interp T.points w x = ∑ i, ∑ j,
      u (T.points i) * baryCoord T.points x i * (w (T.points j) * baryCoord T.points x j) :=
    fun x => by rw [p1Interp_apply, p1Interp_apply, Finset.sum_mul_sum]
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp_rw [integral_finsetSum _ fun j _ => hint _ j]
  have e2 : ∀ i j, ∫ x in T.closedInterior, u (T.points i) * baryCoord T.points x i *
      (w (T.points j) * baryCoord T.points x j) = u (T.points i) * w (T.points j) *
        ∫ x in T.closedInterior, baryCoord T.points x i * baryCoord T.points x j := fun i j => by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show _ = _
    ring
  simp_rw [e2, integral_baryCoord_mul]
  have e3 : ∀ i, ∑ j, u (T.points i) * w (T.points j) *
      ((if i = j then 2 else 1) * volume.real T.closedInterior / ((n + 1) * (n + 2))) =
        volume.real T.closedInterior / ((n + 1) * (n + 2)) *
          (u (T.points i) * w (T.points i) + u (T.points i) * ∑ j, w (T.points j)) := fun i => by
    rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [ite_eq_left rfl]
    have : ∀ j ∈ (univ.erase i : Finset (Fin (n + 1))), u (T.points i) * w (T.points j) *
        ((if i = j then 2 else 1) * volume.real T.closedInterior / ((n + 1) * (n + 2))) =
          volume.real T.closedInterior / ((n + 1) * (n + 2)) *
            (u (T.points i) * w (T.points j)) := fun j hj => by
      rw [ite_eq_right (Ne.symm (Finset.ne_of_mem_erase hj))]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  simp_rw [e3, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem sum_sum_sub_mul_sub (u w : Fin (n + 1) → ℝ) :
    ∑ i, ∑ j, (u i - u j) * (w i - w j) =
      2 * ((n + 1) * ∑ j, u j * w j - (∑ j, u j) * ∑ j, w j) := by
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  push_cast
  ring

theorem lumped_sub_integral_p1Interp_mul (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (u w : (Fin n → ℝ) → ℝ) :
    volume.real T.closedInterior / (n + 1) * ∑ j, u (T.points j) * w (T.points j) -
        ∫ x in T.closedInterior, p1Interp T.points u x * p1Interp T.points w x =
      volume.real T.closedInterior / (2 * (n + 1) * (n + 2)) *
        ∑ i, ∑ j, (u (T.points i) - u (T.points j)) * (w (T.points i) - w (T.points j)) := by
  rw [integral_p1Interp_mul, sum_sum_sub_mul_sub (fun j => u (T.points j)) fun j => w (T.points j)]
  field_simp
  ring

theorem sub_eq_p1Grad_dotProduct {p : Fin (n + 1) → Fin n → ℝ} (hp : IsUnit (edgeMatrix p).det)
    (u : (Fin n → ℝ) → ℝ) (i j : Fin (n + 1)) :
    u (p i) - u (p j) = p1Grad p u ⬝ᵥ (p i - p j) := by
  rw [← p1Interp_vertex hp u i, ← p1Interp_vertex hp u j, p1Interp_sub]

theorem sum_sum_sq_sub_le (w : Fin (n + 1) → ℝ) :
    ∑ i, ∑ j, (w i - w j) ^ 2 ≤ 2 * (n + 1) * ∑ j, w j ^ 2 := by
  have e := sum_sum_sub_mul_sub w w
  simp only [← sq] at e
  rw [e]
  nlinarith [sq_nonneg (∑ j, w j)]

theorem abs_lumped_sub_integral_p1Interp_mul_le (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (u w : (Fin n → ℝ) → ℝ) :
    |volume.real T.closedInterior / (n + 1) * ∑ j, u (T.points j) * w (T.points j) -
        ∫ x in T.closedInterior, p1Interp T.points u x * p1Interp T.points w x| ≤
      volume.real T.closedInterior / (2 * (n + 1) * (n + 2)) *
        (√(∑ i, ∑ j, (u (T.points i) - u (T.points j)) ^ 2) *
          √(∑ i, ∑ j, (w (T.points i) - w (T.points j)) ^ 2)) := by
  rw [lumped_sub_integral_p1Interp_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ volume.real T.closedInterior / (2 * (n + 1) * (n + 2)))]
  refine mul_le_mul_of_nonneg_left (abs_le_of_sq_le_sq ?_ (by positivity)) (by positivity)
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  simp only [← Fintype.sum_prod_type']
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem sum_sum_sq_sub_le_p1Grad {p : Fin (n + 1) → Fin n → ℝ} (hp : IsUnit (edgeMatrix p).det)
    {δ : ℝ} (hδ : ∀ i j, (p i - p j) ⬝ᵥ (p i - p j) ≤ δ ^ 2) (u : (Fin n → ℝ) → ℝ) :
    ∑ i, ∑ j, (u (p i) - u (p j)) ^ 2 ≤ n * (n + 1) * δ ^ 2 * (p1Grad p u ⬝ᵥ p1Grad p u) := by
  have hg : 0 ≤ p1Grad p u ⬝ᵥ p1Grad p u := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have h : ∀ i j, (u (p i) - u (p j)) ^ 2 ≤ δ ^ 2 * (p1Grad p u ⬝ᵥ p1Grad p u) := fun i j => by
    rw [sub_eq_p1Grad_dotProduct hp]
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (p1Grad p u) (p i - p j)
    calc (p1Grad p u ⬝ᵥ (p i - p j)) ^ 2
        ≤ (p1Grad p u ⬝ᵥ p1Grad p u) * ((p i - p j) ⬝ᵥ (p i - p j)) := by
          simpa [dotProduct, sq] using cs
      _ ≤ (p1Grad p u ⬝ᵥ p1Grad p u) * δ ^ 2 := mul_le_mul_of_nonneg_left (hδ i j) hg
      _ = δ ^ 2 * (p1Grad p u ⬝ᵥ p1Grad p u) := by ring
  calc ∑ i, ∑ j, (u (p i) - u (p j)) ^ 2
      = ∑ i, ∑ j ∈ univ.erase i, (u (p i) - u (p j)) ^ 2 := Finset.sum_congr rfl fun i _ => by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), sub_self, sq, mul_zero, zero_add]
    _ ≤ ∑ i : Fin (n + 1), ∑ _j ∈ univ.erase i, δ ^ 2 * (p1Grad p u ⬝ᵥ p1Grad p u) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = n * (n + 1) * δ ^ 2 * (p1Grad p u ⬝ᵥ p1Grad p u) := by
        simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Nat.add_sub_cancel]
        push_cast; ring

theorem abs_lumped_sub_integral_p1Interp_mul_le_p1Grad (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ i j, (T.points i - T.points j) ⬝ᵥ (T.points i - T.points j) ≤ δ ^ 2)
    (u w : (Fin n → ℝ) → ℝ) :
    |volume.real T.closedInterior / (n + 1) * ∑ j, u (T.points j) * w (T.points j) -
        ∫ x in T.closedInterior, p1Interp T.points u x * p1Interp T.points w x| ≤
      √(n * (n + 1) / 2) / (n + 2) * δ *
        (√(volume.real T.closedInterior * (p1Grad T.points u ⬝ᵥ p1Grad T.points u)) *
          √(volume.real T.closedInterior / (n + 1) * ∑ j, w (T.points j) * w (T.points j))) := by
  set V := volume.real T.closedInterior
  set G := p1Grad T.points u ⬝ᵥ p1Grad T.points u
  set W := ∑ j, w (T.points j) * w (T.points j)
  have hV : 0 ≤ V := measureReal_nonneg
  have hG : 0 ≤ G := by
    simp only [G, dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hA := sum_sum_sq_sub_le_p1Grad (isUnit_det_edgeMatrix T) hδ u
  have hB := sum_sum_sq_sub_le fun j => w (T.points j)
  rw [show ∑ j, w (T.points j) ^ 2 = W from Finset.sum_congr rfl fun j _ => sq _] at hB
  have hA0 : 0 ≤ ∑ i, ∑ j, (u (T.points i) - u (T.points j)) ^ 2 := by positivity
  have hB0 : 0 ≤ ∑ i, ∑ j, (w (T.points i) - w (T.points j)) ^ 2 := by positivity
  have hn : (0 : ℝ) ≤ n * (n + 1) / 2 := by positivity
  refine (abs_lumped_sub_integral_p1Interp_mul_le T u w).trans
    ((pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_)
  have hR : (√(n * (n + 1) / 2) / (n + 2) * δ * (√(V * G) * √(V / (n + 1) * W))) ^ 2 =
      n * (n + 1) / 2 / (n + 2) ^ 2 * δ ^ 2 * ((V * G) * (V / (n + 1) * W)) := by
    rw [mul_pow, mul_pow, mul_pow, div_pow, Real.sq_sqrt hn, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
  rw [hR, mul_pow, mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  calc (V / (2 * (n + 1) * (n + 2))) ^ 2 * ((∑ i, ∑ j, (u (T.points i) - u (T.points j)) ^ 2) *
        ∑ i, ∑ j, (w (T.points i) - w (T.points j)) ^ 2)
      ≤ (V / (2 * (n + 1) * (n + 2))) ^ 2 * ((n * (n + 1) * δ ^ 2 * G) * (2 * (n + 1) * W)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hA hB hB0 (by positivity)) (by positivity)
    _ = _ := by field_simp

/-! ### The consistent and the lumped mass of a mesh -/

/-- The consistent mass `⟨u, w⟩ = Σ_T ∫_T Πₜu Πₜw` of the mesh `M` on nodal values `u, w`. -/
def p1Mass (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑ T ∈ M.simplices, ∫ x in T.closedInterior, p1Interp T.points u x * p1Interp T.points w x

/-- The lumped inner product `⟨u, w⟩_L = Σ_T |T| / (n + 1) Σⱼ u(pⱼ) w(pⱼ)` of the mesh `M`. -/
def lumpedInner (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑ T ∈ M.simplices, volume.real T.closedInterior / (n + 1) *
    ∑ j, u (T.points j) * w (T.points j)

theorem lumpedInner_sub_p1Mass (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) :
    lumpedInner M u w - p1Mass M u w = ∑ T ∈ M.simplices,
      volume.real T.closedInterior / (2 * (n + 1) * (n + 2)) *
        ∑ i, ∑ j, (u (T.points i) - u (T.points j)) * (w (T.points i) - w (T.points j)) := by
  rw [lumpedInner, p1Mass, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun T _ => lumped_sub_integral_p1Interp_mul T u w

/-- The lumped norm dominates the consistent one: `⟨u, u⟩ ≤ ⟨u, u⟩_L`. -/
theorem p1Mass_le_lumpedInner (M : SimplicialMesh n) (u : (Fin n → ℝ) → ℝ) :
    p1Mass M u u ≤ lumpedInner M u u := by
  rw [← sub_nonneg, lumpedInner_sub_p1Mass]
  exact Finset.sum_nonneg fun T _ => mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _)

/-- `⟨u, u⟩_L ≤ (n + 2) ⟨u, u⟩`. -/
theorem lumpedInner_le_mul_p1Mass (M : SimplicialMesh n) (u : (Fin n → ℝ) → ℝ) :
    lumpedInner M u u ≤ (n + 2) * p1Mass M u u := by
  rw [p1Mass, Finset.mul_sum, lumpedInner]
  refine Finset.sum_le_sum fun T _ => ?_
  rw [integral_p1Interp_mul]
  have hS : 0 ≤ (∑ j, u (T.points j)) * ∑ j, u (T.points j) := mul_self_nonneg _
  have e : ((n : ℝ) + 2) * (volume.real T.closedInterior *
      (∑ j, u (T.points j) * u (T.points j) + (∑ j, u (T.points j)) * ∑ j, u (T.points j)) /
        ((n + 1) * (n + 2))) = volume.real T.closedInterior / (n + 1) *
      (∑ j, u (T.points j) * u (T.points j) + (∑ j, u (T.points j)) * ∑ j, u (T.points j)) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hS) (by positivity)

theorem lumpedInner_sub_p1Mass_le (M : SimplicialMesh n) (u : (Fin n → ℝ) → ℝ) :
    lumpedInner M u u - p1Mass M u u ≤ (n + 1) / (n + 2) * lumpedInner M u u := by
  have h := lumpedInner_le_mul_p1Mass M u
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

theorem abs_lumpedInner_sub_p1Mass_le_sqrt (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) :
    |lumpedInner M u w - p1Mass M u w| ≤
      √(lumpedInner M u u - p1Mass M u u) * √(lumpedInner M w w - p1Mass M w w) := by
  have hd : ∀ (T : Affine.Simplex ℝ (Fin n → ℝ) n) (v : (Fin n → ℝ) → ℝ),
      volume.real T.closedInterior / (n + 1) * ∑ j, v (T.points j) * v (T.points j) -
          ∫ x in T.closedInterior, p1Interp T.points v x * p1Interp T.points v x =
        volume.real T.closedInterior / (2 * (n + 1) * (n + 2)) *
          ∑ i, ∑ j, (v (T.points i) - v (T.points j)) ^ 2 := fun T v => by
    rw [lumped_sub_integral_p1Interp_mul]
    simp only [sq]
  unfold lumpedInner p1Mass
  simp only [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun T _ => ?_).trans
    (Real.sum_sqrt_mul_sqrt_le _ (fun T => ?_) fun T => ?_))
  · have hκ : 0 ≤ volume.real T.closedInterior / (2 * (n + 1) * (n + 2)) := by positivity
    rw [hd, hd, Real.sqrt_mul hκ, Real.sqrt_mul hκ,
      show ∀ a b c : ℝ, a * b * (a * c) = a * a * (b * c) from fun a b c => by ring,
      Real.mul_self_sqrt hκ]
    exact abs_lumped_sub_integral_p1Interp_mul_le T u w
  · rw [hd]; positivity
  · rw [hd]; positivity

theorem abs_lumpedInner_sub_p1Mass_le_lumpedInner (M : SimplicialMesh n)
    (u w : (Fin n → ℝ) → ℝ) :
    |lumpedInner M u w - p1Mass M u w| ≤
      (n + 1) / (n + 2) * (√(lumpedInner M u u) * √(lumpedInner M w w)) := by
  have hc : (0 : ℝ) ≤ (n + 1) / (n + 2) := by positivity
  refine (abs_lumpedInner_sub_p1Mass_le_sqrt M u w).trans ?_
  calc √(lumpedInner M u u - p1Mass M u u) * √(lumpedInner M w w - p1Mass M w w)
      ≤ √((n + 1) / (n + 2) * lumpedInner M u u) * √((n + 1) / (n + 2) * lumpedInner M w w) :=
        mul_le_mul (Real.sqrt_le_sqrt (lumpedInner_sub_p1Mass_le M u))
          (Real.sqrt_le_sqrt (lumpedInner_sub_p1Mass_le M w)) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = (n + 1) / (n + 2) * (√(lumpedInner M u u) * √(lumpedInner M w w)) := by
        rw [Real.sqrt_mul hc, Real.sqrt_mul hc,
          show ∀ a b c : ℝ, a * b * (a * c) = a * a * (b * c) from fun a b c => by ring,
          Real.mul_self_sqrt hc]

theorem abs_lumpedInner_sub_p1Mass_le (M : SimplicialMesh n) {h : ℝ} (hh : 0 ≤ h)
    (hM : ∀ T ∈ M.simplices, ∀ i j,
      (T.points i - T.points j) ⬝ᵥ (T.points i - T.points j) ≤ h ^ 2)
    (u w : (Fin n → ℝ) → ℝ) :
    |lumpedInner M u w - p1Mass M u w| ≤
      √(n * (n + 1) / 2) / (n + 2) * h * √(p1Stiffness M u u) * √(lumpedInner M w w) := by
  have hc : 0 ≤ √(n * (n + 1) / 2) / (n + 2) * h := by positivity
  unfold lumpedInner p1Mass
  rw [← Finset.sum_sub_distrib, p1Stiffness_eq, mul_assoc]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ T ∈ M.simplices, √(n * (n + 1) / 2) / (n + 2) * h *
          (√(volume.real T.closedInterior * (p1Grad T.points u ⬝ᵥ p1Grad T.points u)) *
            √(volume.real T.closedInterior / (n + 1) * ∑ j, w (T.points j) * w (T.points j))) :=
        Finset.sum_le_sum fun T hT =>
          abs_lumped_sub_integral_p1Interp_mul_le_p1Grad T hh (hM T hT) u w
    _ = √(n * (n + 1) / 2) / (n + 2) * h * ∑ T ∈ M.simplices,
          √(volume.real T.closedInterior * (p1Grad T.points u ⬝ᵥ p1Grad T.points u)) *
            √(volume.real T.closedInterior / (n + 1) * ∑ j, w (T.points j) * w (T.points j)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le _ (fun T => ?_) fun T => ?_) hc
        · refine mul_nonneg measureReal_nonneg ?_
          simp only [dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
        · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)

/-! ### The hat functions and the nodal functions with zero sums -/

theorem card_filter_points_eq_le_one (T : Affine.Simplex ℝ (Fin n → ℝ) n) (x : Fin n → ℝ) :
    #{j | T.points j = x} ≤ 1 :=
  Finset.card_le_one.2 fun _ ha _ hb => T.independent.injective
    ((Finset.mem_filter.1 ha).2.trans (Finset.mem_filter.1 hb).2.symm)

theorem nodalIndicator_mul_self (x y : Fin n → ℝ) :
    nodalIndicator x y * nodalIndicator x y = nodalIndicator x y := by
  unfold nodalIndicator; split_ifs <;> simp

theorem sum_nodalIndicator_points (T : Affine.Simplex ℝ (Fin n → ℝ) n) (x : Fin n → ℝ) :
    ∑ j, nodalIndicator x (T.points j) = (#{j | T.points j = x} : ℝ) := by
  simp [nodalIndicator, Finset.sum_boole]

theorem lumpedInner_nodalIndicator (M : SimplicialMesh n) (x : Fin n → ℝ) :
    lumpedInner M (nodalIndicator x) (nodalIndicator x) = lumpedMass M x := by
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [nodalIndicator_mul_self, sum_nodalIndicator_points]

theorem p1Mass_nodalIndicator (M : SimplicialMesh n) (x : Fin n → ℝ) :
    p1Mass M (nodalIndicator x) (nodalIndicator x) = 2 / (n + 2) * lumpedMass M x := by
  rw [p1Mass, lumpedMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [integral_p1Interp_mul]
  have h3 : (#{j | T.points j = x} : ℝ) * #{j | T.points j = x} = #{j | T.points j = x} := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (card_filter_points_eq_le_one T x) with h | h <;>
      simp [h]
  simp only [nodalIndicator_mul_self, sum_nodalIndicator_points, h3]
  field_simp
  ring

theorem lumpedMass_pos (M : SimplicialMesh n) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ M.simplices) {x : Fin n → ℝ} (hx : x ∈ vertexSet T) : 0 < lumpedMass M x := by
  obtain ⟨j, rfl⟩ := mem_vertexSet.1 hx
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun T' : Affine.Simplex ℝ (Fin n → ℝ) n =>
    volume.real T'.closedInterior / (n + 1) * (#{i | T'.points i = T.points j} : ℝ))
    (fun T' _ => by positivity) hT)
  refine mul_pos (div_pos (volume_real_closedInterior_pos T) (by positivity)) ?_
  exact_mod_cast (Finset.card_pos.2 ⟨j, by simp⟩ : 0 < #{i | T.points i = T.points j})

theorem p1Mass_eq_of_sum_eq_zero (M : SimplicialMesh n) {u : (Fin n → ℝ) → ℝ}
    (hu : ∀ T ∈ M.simplices, ∑ j, u (T.points j) = 0) (w : (Fin n → ℝ) → ℝ) :
    p1Mass M u w = lumpedInner M u w / (n + 2) := by
  rw [p1Mass, lumpedInner, Finset.sum_div]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [integral_p1Interp_mul, hu T hT, zero_mul, add_zero]
  field_simp

/-! ### Lumped readings -/

section Reading

variable {X E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

/-- A lumped `P₁` reading: `⟪v, w⟫ = ⟨ν v, ν w⟩_L` on `X`, and `⟪i v, i w⟫ = ⟨ν v, ν w⟩`. -/
structure IsLumpedReading (M : SimplicialMesh n) (ν : X → (Fin n → ℝ) → ℝ) (i : X →L[ℝ] E) :
    Prop where
  inner_eq : ∀ v w, ⟪v, w⟫_ℝ = lumpedInner M (ν v) (ν w)
  inner_apply_eq : ∀ v w, ⟪i v, i w⟫_ℝ = p1Mass M (ν v) (ν w)

namespace IsLumpedReading

variable {M : SimplicialMesh n} {ν : X → (Fin n → ℝ) → ℝ} {i : X →L[ℝ] E}
  (hr : IsLumpedReading M ν i)
include hr

theorem norm_sq (v : X) : ‖v‖ ^ 2 = lumpedInner M (ν v) (ν v) := by
  rw [← real_inner_self_eq_norm_sq, hr.inner_eq]

theorem norm_apply_sq (v : X) : ‖i v‖ ^ 2 = p1Mass M (ν v) (ν v) := by
  rw [← real_inner_self_eq_norm_sq, hr.inner_apply_eq]

theorem norm_apply_le (v : X) : ‖i v‖ ≤ ‖v‖ := by
  have := p1Mass_le_lumpedInner M (ν v)
  rw [← hr.norm_sq, ← hr.norm_apply_sq] at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

theorem norm_le_sqrt_mul_norm_apply (v : X) : ‖v‖ ≤ √(n + 2) * ‖i v‖ := by
  have := lumpedInner_le_mul_p1Mass M (ν v)
  rw [← hr.norm_sq, ← hr.norm_apply_sq] at this
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact this

variable [CompleteSpace X] [CompleteSpace E]

/-- `‖1 - i* i‖ ≥ n / (n + 2)` as soon as `X` contains the hat function `φₓ` of a vertex `x`. -/
theorem le_opNorm_one_sub_adjoint_comp_self {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ M.simplices)
    {x : Fin n → ℝ} (hx : x ∈ vertexSet T) {v : X} (hv : ν v = nodalIndicator x) :
    n / (n + 2) ≤ ‖1 - i.adjoint ∘L i‖ := by
  have hpos := lumpedMass_pos M hT hx
  have h1 : ‖v‖ ^ 2 = lumpedMass M x := by rw [hr.norm_sq, hv, lumpedInner_nodalIndicator]
  have h2 : ‖i v‖ ^ 2 = 2 / (n + 2) * lumpedMass M x := by
    rw [hr.norm_apply_sq, hv, p1Mass_nodalIndicator]
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [norm_zero, sq, mul_zero] at h1
    exact hpos.ne h1
  refine i.le_opNorm_one_sub_adjoint_comp_self hv0 (le_of_eq ?_)
  rw [h1, h2]
  field_simp
  ring

theorem opNorm_one_sub_adjoint_comp_self_le : ‖1 - i.adjoint ∘L i‖ ≤ (n + 1) / (n + 2) :=
  i.opNorm_one_sub_adjoint_comp_self_le (by positivity) fun v w => by
    rw [Real.norm_eq_abs, hr.inner_eq, hr.inner_apply_eq, ← Real.sqrt_sq (norm_nonneg v),
      ← Real.sqrt_sq (norm_nonneg w), hr.norm_sq, hr.norm_sq]
    exact abs_lumpedInner_sub_p1Mass_le_lumpedInner M (ν v) (ν w)

theorem opNorm_one_sub_adjoint_comp_self_eq_of_sum_eq_zero {v : X} (hv : v ≠ 0)
    (hu : ∀ T ∈ M.simplices, ∑ j, ν v (T.points j) = 0) :
    ‖1 - i.adjoint ∘L i‖ = (n + 1) / (n + 2) := by
  refine le_antisymm hr.opNorm_one_sub_adjoint_comp_self_le
    (i.le_opNorm_one_sub_adjoint_comp_self hv (le_of_eq ?_))
  rw [hr.norm_sq, hr.norm_apply_sq, p1Mass_eq_of_sum_eq_zero M hu]
  field_simp
  ring

/-- The defect from the graph norm is `O(h)`: if every edge of `M` has Euclidean length at most
`h`, then `‖(1 - i* i) v‖ ≤ c_n h ‖∇(ν v)_h‖`, `c_n = √(n (n + 1) / 2) / (n + 2)`. -/
theorem norm_one_sub_adjoint_comp_self_apply_le {h : ℝ} (hh : 0 ≤ h)
    (hM : ∀ T ∈ M.simplices, ∀ i j,
      (T.points i - T.points j) ⬝ᵥ (T.points i - T.points j) ≤ h ^ 2) (v : X) :
    ‖(1 - i.adjoint ∘L i) v‖ ≤
      √(n * (n + 1) / 2) / (n + 2) * h * √(p1Stiffness M (ν v) (ν v)) :=
  i.norm_one_sub_adjoint_comp_self_apply_le (by positivity) fun w => by
    rw [Real.norm_eq_abs, hr.inner_eq, hr.inner_apply_eq, ← Real.sqrt_sq (norm_nonneg w),
      hr.norm_sq]
    exact abs_lumpedInner_sub_p1Mass_le M hh hM (ν v) (ν w)

end IsLumpedReading

end Reading

/-! ### The lumped-mass method on the nodes of a mesh -/

section Nodes

variable {ι : Type*} [Fintype ι]

theorem nodalFun_mul_nodalFun {x : ι → Fin n → ℝ} (hx : Function.Injective x) (U V : ι → ℝ)
    (y : Fin n → ℝ) :
    nodalFun x U y * nodalFun x V y = ∑ q, if x q = y then U q * V q else 0 := by
  classical
  by_cases h : ∃ q, x q = y
  · obtain ⟨q, rfl⟩ := h
    rw [nodalFun_apply hx, nodalFun_apply hx, Finset.sum_eq_single q
      (fun r _ hr => ite_eq_right (hx.ne hr)) (by simp), ite_eq_left rfl]
  · push Not at h
    simp [nodalFun, h]

theorem sum_nodalFun_mul_nodalFun_points {x : ι → Fin n → ℝ} (hx : Function.Injective x)
    (U V : ι → ℝ) (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    ∑ j, nodalFun x U (T.points j) * nodalFun x V (T.points j) =
      ∑ q, (#{j | T.points j = x q} : ℝ) * (U q * V q) := by
  simp only [nodalFun_mul_nodalFun hx]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.cast_card, Finset.sum_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [eq_comm (a := x q), one_mul]

theorem lumpedInner_nodalFun (M : SimplicialMesh n) {x : ι → Fin n → ℝ}
    (hx : Function.Injective x) (U V : ι → ℝ) :
    lumpedInner M (nodalFun x U) (nodalFun x V) = ∑ q, lumpedMass M (x q) * (U q * V q) := by
  simp only [lumpedInner, lumpedMass, sum_nodalFun_mul_nodalFun_points hx, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun T _ => by ring

variable (M : SimplicialMesh n) (x : ι → Fin n → ℝ)

/-- The nodal function with the values `m(x_q)^{-1/2} ξ_q` at the nodes `x` and `0` elsewhere. -/
def lumpedNodal : EuclideanSpace ℝ ι →ₗ[ℝ] (Fin n → ℝ) → ℝ where
  toFun ξ := ∑ q, (ξ q / √(lumpedMass M (x q))) • nodalIndicator (x q)
  map_add' ξ η := by simp [add_div, add_smul, Finset.sum_add_distrib]
  map_smul' c ξ := by simp [mul_div_assoc, mul_smul, Finset.smul_sum]

theorem lumpedNodal_apply (ξ : EuclideanSpace ℝ ι) :
    lumpedNodal M x ξ = nodalFun x fun q => ξ q / √(lumpedMass M (x q)) :=
  (nodalFun_eq_sum x _).symm

/-- The reading map `iₕ ξ = ξ_h ∈ L²(Ω)` of the lumped-mass method on the nodes `x`. -/
def lumpedReading : EuclideanSpace ℝ ι →L[ℝ] L2F ℝ M.domain (formIdx n ((0 : ℕ) : ℤ)) :=
  LinearMap.toContinuousLinearMap ((whitneyElement n).glue M (0 : ℕ) ∘ₗ
    ((whitneyElement n).globalSpace M 0).subtype ∘ₗ p1Global M ∘ₗ lumpedNodal M x)

/-- The discrete gradient `ξ ↦ ∇ξ_h ∈ L²(Ω; Λ¹)` of the lumped-mass method on the nodes `x`. -/
def lumpedGrad : EuclideanSpace ℝ ι →L[ℝ] L2F ℝ M.domain (formIdx n (((0 : ℕ) : ℤ) + 1)) :=
  LinearMap.toContinuousLinearMap ((whitneyElement n).glue M (((0 : ℕ) : ℤ) + 1) ∘ₗ
    (whitneyElement n).dPiecewise M 0 ∘ₗ ((whitneyElement n).globalSpace M 0).subtype ∘ₗ
      p1Global M ∘ₗ lumpedNodal M x)

variable {M x}

theorem isLumpedReading_lumpedReading
    (hM : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) (hx : Function.Injective x)
    (hxv : ∀ q, ∃ T ∈ M.simplices, x q ∈ vertexSet T) :
    IsLumpedReading M (lumpedNodal M x) (lumpedReading M x) where
  inner_eq ξ η := by
    rw [lumpedNodal_apply, lumpedNodal_apply, lumpedInner_nodalFun M hx]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨T, hT, hq⟩ := hxv q
    have hm := lumpedMass_pos M hT hq
    rw [div_mul_div_comm, Real.mul_self_sqrt hm.le, mul_div_assoc', mul_div_cancel_left₀ _ hm.ne']
    exact mul_comm _ _
  inner_apply_eq ξ η := inner_glue_p1Global M hM _ _

theorem norm_lumpedGrad_sq (hM : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain)
    (ξ : EuclideanSpace ℝ ι) :
    ‖lumpedGrad M x ξ‖ ^ 2 = p1Stiffness M (lumpedNodal M x ξ) (lumpedNodal M x ξ) := by
  rw [← real_inner_self_eq_norm_sq]
  exact inner_glue_dPiecewise_p1Global M hM _ _

theorem lumpedNodal_single [DecidableEq ι] (hxv : ∀ q, ∃ T ∈ M.simplices, x q ∈ vertexSet T)
    (q : ι) :
    lumpedNodal M x (EuclideanSpace.single q √(lumpedMass M (x q))) = nodalIndicator (x q) := by
  obtain ⟨T, hT, hq⟩ := hxv q
  have hs : √(lumpedMass M (x q)) ≠ 0 := (Real.sqrt_pos.2 (lumpedMass_pos M hT hq)).ne'
  change ∑ r, _ = _
  rw [Finset.sum_eq_single q (fun r _ hr => by simp [hr]) (by simp)]
  simp [hs]

theorem le_opNorm_one_sub_adjoint_comp_self_lumpedReading
    (hM : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) (hx : Function.Injective x)
    (hxv : ∀ q, ∃ T ∈ M.simplices, x q ∈ vertexSet T) (q : ι) :
    n / (n + 2) ≤ ‖1 - (lumpedReading M x).adjoint ∘L lumpedReading M x‖ := by
  classical
  obtain ⟨T, hT, hq⟩ := hxv q
  exact (isLumpedReading_lumpedReading hM hx hxv).le_opNorm_one_sub_adjoint_comp_self hT hq
    (lumpedNodal_single hxv q)

theorem norm_one_sub_adjoint_comp_self_lumpedReading_apply_le
    (hM : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) (hx : Function.Injective x)
    (hxv : ∀ q, ∃ T ∈ M.simplices, x q ∈ vertexSet T) {h : ℝ} (hh : 0 ≤ h)
    (hedge : ∀ T ∈ M.simplices, ∀ i j,
      (T.points i - T.points j) ⬝ᵥ (T.points i - T.points j) ≤ h ^ 2)
    (ξ : EuclideanSpace ℝ ι) :
    ‖(1 - (lumpedReading M x).adjoint ∘L lumpedReading M x) ξ‖ ≤
      √(n * (n + 1) / 2) / (n + 2) * h * ‖lumpedGrad M x ξ‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (lumpedGrad M x ξ)), norm_lumpedGrad_sq hM]
  exact (isLumpedReading_lumpedReading hM hx hxv).norm_one_sub_adjoint_comp_self_apply_le hh hedge ξ

end Nodes

theorem exists_isLumpedReading (M : SimplicialMesh n) :
    ∃ (ι : Type) (_ : Fintype ι) (x : ι → Fin n → ℝ)
      (i : EuclideanSpace ℝ ι →L[ℝ] L2F ℝ (closure M.domain) (formIdx n ((0 : ℕ) : ℤ))),
      IsLumpedReading M (lumpedNodal M x) i ∧
        ∀ T ∈ M.simplices, ∀ y ∈ vertexSet T, ∃ ξ, lumpedNodal M x ξ = nodalIndicator y := by
  classical
  let M' : SimplicialMesh n :=
    { M with
      domain := closure M.domain
      biUnion_closedInterior := M.biUnion_closedInterior.trans closure_closure.symm }
  let V := M.simplices.biUnion vertexSet
  have hxv : ∀ q : V, ∃ T ∈ M'.simplices, (q : Fin n → ℝ) ∈ vertexSet T := fun q =>
    Finset.mem_biUnion.1 q.2
  have hr := isLumpedReading_lumpedReading (M := M') (x := ((↑) : V → Fin n → ℝ))
    (fun T hT => interior_subset.trans (M.closedInterior_subset_closure hT))
    Subtype.val_injective hxv
  refine ⟨V, inferInstance, (↑), lumpedReading M' (↑), ⟨hr.inner_eq, hr.inner_apply_eq⟩,
    fun T hT y hy => ?_⟩
  have hyV : y ∈ V := Finset.mem_biUnion.2 ⟨T, hT, hy⟩
  exact ⟨EuclideanSpace.single ⟨y, hyV⟩ √(lumpedMass M y),
    lumpedNodal_single (M := M') hxv ⟨y, hyV⟩⟩

/-! ### Freudenthal meshes: the exact operator-norm defect -/

theorem sum_kuhnLattice (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    ∑ l, kuhnLattice σ j l = j := by
  induction j using Fin.induction with
  | zero => simp [kuhnLattice]
  | succ k ih =>
    simp only [kuhnLattice_succ, Pi.add_apply, Finset.sum_add_distrib, ih,
      Finset.sum_pi_single', Finset.mem_univ, ite_true, Fin.val_succ, Fin.val_castSucc]
    push_cast; ring

section Color

open Fin.CommRing

/-- The color `Σₗ qₗ mod (n + 1)` of the lattice node `b + h q`, read off a point. -/
def freudenthalColor (b : Fin n → ℝ) (h : ℝ) (x : Fin n → ℝ) : Fin (n + 1) :=
  ((round ((∑ l, (x l - b l)) / h) : ℤ) : Fin (n + 1))

theorem freudenthalColor_node (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0) (q : Fin n → ℤ) :
    freudenthalColor b h (node b h q) = ((∑ l, q l : ℤ) : Fin (n + 1)) := by
  have e : (∑ l, (node b h q l - b l)) / h = ((∑ l, q l : ℤ) : ℝ) := by
    simp only [node_coord, add_sub_cancel_left, ← Finset.mul_sum, Int.cast_sum]
    field_simp
  rw [freudenthalColor, e, round_intCast]

theorem sum_freudenthalColor_points (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N]
    (g : Fin (n + 1) → ℝ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (freudenthalMesh b s hs N).simplices) :
    ∑ j, g (freudenthalColor b (s / N) (T.points j)) = ∑ c, g c := by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  have e : ∀ j, freudenthalColor b (s / N)
      ((mapEquiv (boxMap b (s / N) (freudenthalScale_ne_zero hs N))
        (freudenthalSimplex (finLattice m) σ)).points j) =
      ((∑ l, finLattice m l : ℤ) : Fin (n + 1)) + j := fun j => by
    rw [mapEquiv_boxMap_freudenthalSimplex_points, freudenthalPoints_eq_node,
      freudenthalColor_node b (freudenthalScale_ne_zero hs N)]
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_kuhnLattice, Int.cast_add,
      Int.cast_natCast, Fin.cast_val_eq_self]
  simp only [e]
  exact Equiv.sum_comp (Equiv.addLeft ((∑ l, finLattice m l : ℤ) : Fin (n + 1))) g

theorem exists_sum_points_eq_zero_freudenthalMesh (hn : n ≠ 0) (b : Fin n → ℝ) {s : ℝ}
    (hs : 0 < s) (N : ℕ) [NeZero N] :
    ∃ u : (Fin n → ℝ) → ℝ, u b = 1 ∧
      ∀ T ∈ (freudenthalMesh b s hs N).simplices, ∑ j, u (T.points j) = 0 := by
  have h10 : (1 : Fin (n + 1)) ≠ 0 := by
    rw [Ne, Fin.one_eq_zero_iff]; omega
  refine ⟨fun y => (Pi.single 0 1 - Pi.single 1 1 : Fin (n + 1) → ℝ)
    (freudenthalColor b (s / N) y), ?_, fun T hT => ?_⟩
  · have : freudenthalColor b (s / N) b = 0 := by simp [freudenthalColor]
    simp [this, h10.symm]
  · rw [sum_freudenthalColor_points b hs N _ hT]
    simp [Finset.sum_sub_distrib]

end Color

theorem exists_mem_vertexSet_freudenthalMesh (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ)
    [NeZero N] : ∃ T ∈ (freudenthalMesh b s hs N).simplices, b ∈ vertexSet T :=
  ⟨_, mem_freudenthalMesh_simplices.2 ⟨0, 1, rfl⟩, mem_vertexSet.2 ⟨0, by
    rw [mapEquiv_boxMap_freudenthalSimplex_points]
    funext i
    simp [freudenthalPoints, latticePoint_apply, finLattice]⟩⟩

/-- Mass lumping on the Freudenthal meshes, `n ≥ 1`, with every vertex a node:
`‖1 - iₕ* iₕ‖ = (n + 1) / (n + 2)` at every level. -/
theorem opNorm_one_sub_adjoint_comp_self_lumpedReading_freudenthalMesh {ι : Type*} [Fintype ι]
    (hn : n ≠ 0) (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N] {x : ι → Fin n → ℝ}
    (hx : Function.Injective x)
    (hxv : ∀ q, ∃ T ∈ (freudenthalMesh b s hs N).simplices, x q ∈ vertexSet T)
    (hall : ∀ T ∈ (freudenthalMesh b s hs N).simplices, ∀ j, ∃ q, x q = T.points j) :
    ‖1 - (lumpedReading (freudenthalMesh b s hs N) x).adjoint ∘L
      lumpedReading (freudenthalMesh b s hs N) x‖ = (n + 1) / (n + 2) := by
  set M := freudenthalMesh b s hs N
  obtain ⟨u, hub, hu⟩ := exists_sum_points_eq_zero_freudenthalMesh hn b hs N
  set ξ : EuclideanSpace ℝ ι := WithLp.toLp 2 fun q => √(lumpedMass M (x q)) * u (x q)
  have hsq : ∀ q, √(lumpedMass M (x q)) ≠ 0 := fun q => by
    obtain ⟨T, hT, hq⟩ := hxv q
    exact (Real.sqrt_pos.2 (lumpedMass_pos M hT hq)).ne'
  have hν : ∀ q, lumpedNodal M x ξ (x q) = u (x q) := fun q => by
    rw [lumpedNodal_apply, nodalFun_apply hx]
    simp only [ξ]
    field_simp [hsq q]
  refine (isLumpedReading_lumpedReading (fun T hT => interior_subset_freudenthalMesh_domain b hs
    N hT) hx hxv).opNorm_one_sub_adjoint_comp_self_eq_of_sum_eq_zero (v := ξ) ?_ fun T hT => ?_
  · obtain ⟨T, hT, hb⟩ := exists_mem_vertexSet_freudenthalMesh b hs N
    obtain ⟨j, hj⟩ := mem_vertexSet.1 hb
    obtain ⟨q, hq⟩ := hall T hT j
    intro h0
    have := congrArg (fun ξ : EuclideanSpace ℝ ι => ξ q) h0
    simp only [ξ, PiLp.zero_apply, hq, hj, hub, mul_one] at this
    exact hsq q (by rwa [hq, hj])
  · rw [← hu T hT]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨q, hq⟩ := hall T hT j
    rw [← hq, hν]

end Feec.FiniteElement
