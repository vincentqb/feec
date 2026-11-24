module

public import Feec.FiniteElement.P1Global

/-!
# The consistent and the lumped mass of `P₁` elements

On a simplex `T` of `ℝⁿ` with vertices `p₀, …, pₙ` and barycentric coordinates `λ₀, …, λₙ`, the
`P₁` interpolant of the nodal values `u` is `Πₜu = Σⱼ uⱼ λⱼ`, `uⱼ = u(pⱼ)`. Its **consistent
element mass** `∫_T Πₜu Πₜw` is computed exactly, and the **lumped element mass**
`|T| / (n + 1) Σⱼ uⱼ wⱼ` is its vertex quadrature (summed over the simplices at a vertex, the
weights are the lumped mass `Feec.FiniteElement.lumpedMass`, [Thomee2006], Ch. 15). Their
difference is a sum over the pairs of vertices, which the gradient controls: on each element it is
at most a constant times the edge length, the gradient of `Πₜu` and the lumped norm of `w`. These
are element-level identities and bounds; they are not assembled over a mesh here.

## Main results

* `integral_baryCoord_mul`: `∫_T λᵢ λⱼ = |T| (1 + δᵢⱼ) / ((n + 1) (n + 2))`, from the change of
  variables to the reference simplex (`integral_baryCoord_mul_eq`), its invariance under the
  permutations of the vertices (`integral_baryCoord_mul_perm`, from
  `Feec.FiniteElement.integral_comp_baryCoord_perm`),
  `∫_T λⱼ² = 2 |T| / ((n + 1) (n + 2))` (`integral_baryCoord_mul_self`) and `Σₖ λₖ = 1`.
* `integral_p1Interp_mul`: **the consistent element mass**,
  `∫_T Πₜu Πₜw = |T| (Σⱼ uⱼ wⱼ + (Σⱼ uⱼ) (Σⱼ wⱼ)) / ((n + 1) (n + 2))`.
* `lumped_sub_integral_p1Interp_mul`: **the lumped minus the consistent element mass** is
  `|T| / (2 (n + 1) (n + 2)) Σᵢ Σⱼ (uᵢ - uⱼ) (wᵢ - wⱼ)` (`sum_sum_sub_mul_sub`), nonnegative for
  `u = w`; with `abs_lumped_sub_integral_p1Interp_mul_le` (Cauchy–Schwarz over the pairs of
  vertices), the edge differences `uᵢ - uⱼ = ∇Πₜu · (pᵢ - pⱼ)` (`sub_eq_p1Grad_dotProduct`) and
  their bound `Σᵢ Σⱼ (uᵢ - uⱼ)² ≤ (n + 1)² δ² |∇Πₜu|²` by the edge length `δ`
  (`sum_sum_sq_sub_le_p1Grad`),
  and `Σᵢ Σⱼ (wᵢ - wⱼ)² ≤ 2 (n + 1) Σⱼ wⱼ²` (`sum_sum_sq_sub_le`): **the defect of an element is
  at most a constant times `δ ‖∇Πₜu‖_{L²(T)}` times the lumped norm of `w`**
  (`abs_lumped_sub_integral_p1Interp_mul_le_p1Grad`), with no shape regularity.

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
  (the lumped mass method)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MeasureTheory

@[expose] public noncomputable section

namespace Feec.FiniteElement

open Feec.Mesh

variable {n : ℕ}

/-- **Change of variables for products of barycentric coordinates**:
`∫_T λᵢ λⱼ = |det B_T| ∫_{T̂} λ̂ᵢ λ̂ⱼ`. -/
theorem integral_baryCoord_mul_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i j : Fin (n + 1)) :
    ∫ x in T.closedInterior, baryCoord T.points x i * baryCoord T.points x j =
      |LinearMap.det T.linearPart| *
        ∫ y in FiniteElement.refSimplex n, refBary y i * refBary y j := by
  rw [integral_closedInterior_eq, refSimplex_closedInterior_eq]
  simp only [baryCoord_refMap]

/-- **Permutation invariance**: `∫_T λ_{π i} λ_{π j} = ∫_T λᵢ λⱼ`
(`integral_comp_baryCoord_perm`). -/
theorem integral_baryCoord_mul_perm (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (π : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    ∫ x in T.closedInterior, baryCoord T.points x (π i) * baryCoord T.points x (π j) =
      ∫ x in T.closedInterior, baryCoord T.points x i * baryCoord T.points x j :=
  integral_comp_baryCoord_perm T π fun l => l i * l j

/-- `∫_T λⱼ² = 2 |T| / ((n + 1) (n + 2))`. -/
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

/-- **The integral of a product of two barycentric coordinates**:
`∫_T λᵢ λⱼ = |T| (1 + δᵢⱼ) / ((n + 1) (n + 2))`. For `i ≠ j`: by permutation invariance the
`n` integrals `∫_T λᵢ λₖ`, `k ≠ i`, are equal, and they sum to `∫_T λᵢ - ∫_T λᵢ²`
(`Σₖ λₖ = 1`). -/
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

/-- **The consistent element mass** of `P₁` interpolants:
`∫_T Πₜu Πₜw = |T| (Σⱼ uⱼ wⱼ + (Σⱼ uⱼ) (Σⱼ wⱼ)) / ((n + 1) (n + 2))`, `uⱼ = u(pⱼ)`. -/
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

/-- **The sum over the pairs of vertices**:
`Σᵢ Σⱼ (uᵢ - uⱼ) (wᵢ - wⱼ) = 2 ((n + 1) Σⱼ uⱼ wⱼ - (Σⱼ uⱼ) (Σⱼ wⱼ))` over the `n + 1` vertices. -/
theorem sum_sum_sub_mul_sub (u w : Fin (n + 1) → ℝ) :
    ∑ i, ∑ j, (u i - u j) * (w i - w j) =
      2 * ((n + 1) * ∑ j, u j * w j - (∑ j, u j) * ∑ j, w j) := by
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  push_cast
  ring

/-- **The lumped minus the consistent element mass**:
`|T| / (n + 1) Σⱼ uⱼ wⱼ - ∫_T Πₜu Πₜw = |T| / (2 (n + 1) (n + 2)) Σᵢ Σⱼ (uᵢ - uⱼ) (wᵢ - wⱼ)`
(so the lumped element mass dominates the consistent one, `u = w`). -/
theorem lumped_sub_integral_p1Interp_mul (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (u w : (Fin n → ℝ) → ℝ) :
    volume.real T.closedInterior / (n + 1) * ∑ j, u (T.points j) * w (T.points j) -
        ∫ x in T.closedInterior, p1Interp T.points u x * p1Interp T.points w x =
      volume.real T.closedInterior / (2 * (n + 1) * (n + 2)) *
        ∑ i, ∑ j, (u (T.points i) - u (T.points j)) * (w (T.points i) - w (T.points j)) := by
  rw [integral_p1Interp_mul, sum_sum_sub_mul_sub (fun j => u (T.points j)) fun j => w (T.points j)]
  field_simp
  ring

/-- **The edge differences of a `P₁` interpolant** are its gradient against the edges:
`u(pᵢ) - u(pⱼ) = ∇Πₜu · (pᵢ - pⱼ)`. -/
theorem sub_eq_p1Grad_dotProduct {p : Fin (n + 1) → Fin n → ℝ} (hp : IsUnit (edgeMatrix p).det)
    (u : (Fin n → ℝ) → ℝ) (i j : Fin (n + 1)) :
    u (p i) - u (p j) = p1Grad p u ⬝ᵥ (p i - p j) := by
  rw [← p1Interp_vertex hp u i, ← p1Interp_vertex hp u j, p1Interp_sub]

/-- `Σᵢ Σⱼ (wᵢ - wⱼ)² ≤ 2 (n + 1) Σⱼ wⱼ²` over the `n + 1` vertices. -/
theorem sum_sum_sq_sub_le (w : Fin (n + 1) → ℝ) :
    ∑ i, ∑ j, (w i - w j) ^ 2 ≤ 2 * (n + 1) * ∑ j, w j ^ 2 := by
  have e := sum_sum_sub_mul_sub w w
  simp only [← sq] at e
  rw [e]
  nlinarith [sq_nonneg (∑ j, w j)]

/-- **The lumped-mass defect of an element**, by Cauchy–Schwarz over the pairs of vertices:
`|(|T| / (n + 1)) Σⱼ uⱼ wⱼ - ∫_T Πₜu Πₜw| ≤
|T| / (2 (n + 1) (n + 2)) √(Σᵢ Σⱼ (uᵢ - uⱼ)²) √(Σᵢ Σⱼ (wᵢ - wⱼ)²)`. -/
theorem abs_lumped_sub_integral_p1Interp_mul_le (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (u w : (Fin n → ℝ) → ℝ) :
    |volume.real T.closedInterior / (n + 1) * ∑ j, u (T.points j) * w (T.points j) -
        ∫ x in T.closedInterior, p1Interp T.points u x * p1Interp T.points w x| ≤
      volume.real T.closedInterior / (2 * (n + 1) * (n + 2)) *
        (√(∑ i, ∑ j, (u (T.points i) - u (T.points j)) ^ 2) *
          √(∑ i, ∑ j, (w (T.points i) - w (T.points j)) ^ 2)) := by
  rw [lumped_sub_integral_p1Interp_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ volume.real T.closedInterior / (2 * (n + 1) * (n + 2)))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set du : Fin (n + 1) × Fin (n + 1) → ℝ := fun q => u (T.points q.1) - u (T.points q.2)
  set dw : Fin (n + 1) × Fin (n + 1) → ℝ := fun q => w (T.points q.1) - w (T.points q.2)
  have e1 : ∑ i, ∑ j, (u (T.points i) - u (T.points j)) * (w (T.points i) - w (T.points j)) =
      ∑ q ∈ univ ×ˢ univ, du q * dw q := (Finset.sum_product' _ _ _).symm
  have e2 : ∑ i, ∑ j, (u (T.points i) - u (T.points j)) ^ 2 = ∑ q ∈ univ ×ˢ univ, du q ^ 2 :=
    (Finset.sum_product' _ _ _).symm
  have e3 : ∑ i, ∑ j, (w (T.points i) - w (T.points j)) ^ 2 = ∑ q ∈ univ ×ˢ univ, dw q ^ 2 :=
    (Finset.sum_product' _ _ _).symm
  rw [e1, e2, e3]
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt (univ ×ˢ univ) du dw
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (univ ×ˢ univ) (fun q => -du q) dw
  simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at h2
  rw [abs_le]
  constructor <;> linarith

/-- **The edge differences are bounded by the gradient**: if every edge of `p` has Euclidean length
at most `δ`, `Σᵢ Σⱼ (u(pᵢ) - u(pⱼ))² ≤ (n + 1)² δ² |∇Πₜu|²` (`sub_eq_p1Grad_dotProduct`,
Cauchy–Schwarz). -/
theorem sum_sum_sq_sub_le_p1Grad {p : Fin (n + 1) → Fin n → ℝ} (hp : IsUnit (edgeMatrix p).det)
    {δ : ℝ} (hδ : ∀ i j, (p i - p j) ⬝ᵥ (p i - p j) ≤ δ ^ 2) (u : (Fin n → ℝ) → ℝ) :
    ∑ i, ∑ j, (u (p i) - u (p j)) ^ 2 ≤ (n + 1) ^ 2 * δ ^ 2 * (p1Grad p u ⬝ᵥ p1Grad p u) := by
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
      ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), δ ^ 2 * (p1Grad p u ⬝ᵥ p1Grad p u) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul];
                push_cast; ring

/-- **The lumped-mass defect of an element in the graph norm**: if every edge of `T` has Euclidean
length at most `δ`, then
`|(|T| / (n + 1)) Σⱼ uⱼ wⱼ - ∫_T Πₜu Πₜw| ≤
|T| / (2 (n + 1) (n + 2)) ((n + 1) δ |∇Πₜu|) √(2 (n + 1) Σⱼ wⱼ²)`: a constant times
`δ ‖∇Πₜu‖_{L²(T)}` times the lumped norm `(|T| / (n + 1) Σⱼ wⱼ²)^{1/2}` of `w`. -/
theorem abs_lumped_sub_integral_p1Interp_mul_le_p1Grad (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ i j, (T.points i - T.points j) ⬝ᵥ (T.points i - T.points j) ≤ δ ^ 2)
    (u w : (Fin n → ℝ) → ℝ) :
    |volume.real T.closedInterior / (n + 1) * ∑ j, u (T.points j) * w (T.points j) -
        ∫ x in T.closedInterior, p1Interp T.points u x * p1Interp T.points w x| ≤
      volume.real T.closedInterior / (2 * (n + 1) * (n + 2)) *
        ((n + 1) * δ * √(p1Grad T.points u ⬝ᵥ p1Grad T.points u) *
          √(2 * (n + 1) * ∑ j, w (T.points j) ^ 2)) := by
  refine (abs_lumped_sub_integral_p1Interp_mul_le T u w).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (by positivity))
      (by positivity))
  · have hg : 0 ≤ p1Grad T.points u ⬝ᵥ p1Grad T.points u := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    calc √(∑ i, ∑ j, (u (T.points i) - u (T.points j)) ^ 2)
        ≤ √((n + 1) ^ 2 * δ ^ 2 * (p1Grad T.points u ⬝ᵥ p1Grad T.points u)) :=
          Real.sqrt_le_sqrt (sum_sum_sq_sub_le_p1Grad (isUnit_det_edgeMatrix T) hδ u)
      _ = (n + 1) * δ * √(p1Grad T.points u ⬝ᵥ p1Grad T.points u) := by
          rw [show ((n : ℝ) + 1) ^ 2 * δ ^ 2 * (p1Grad T.points u ⬝ᵥ p1Grad T.points u) =
            ((n + 1) * δ) ^ 2 * (p1Grad T.points u ⬝ᵥ p1Grad T.points u) by ring,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  · exact Real.sqrt_le_sqrt (sum_sum_sq_sub_le fun j => w (T.points j))

end Feec.FiniteElement
