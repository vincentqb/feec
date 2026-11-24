module

public import Solution.Defs
public import Feec.ForMathlib.InnerProductSpace.Diagonal
public import Feec.ForMathlib.Lp.Diagonal

/-!
# The witness of the defect in the graph norm

The complex `ℓ²(ℕ, ℝ)` in every degree with `d⁰ = Λ`, `Λ (xₖ) = ((k + 1) xₖ)` (closed, densely
defined and onto, `lp.diagOp`), and all other differentials `0` (`HighMode.complex`), on the window
`ℓ² --Λ--> ℓ²` (`𝐝 (x⁰, x¹) = (0, Λ x⁰)`); the discrete spaces `Xₙ = ℝⁿ⁺¹ ⊕ ℝⁿ⁺¹` of the modes
`k ≤ n` of both degrees, read by `iₙ (u, w) = (Σₖ σₖ uₖ eₖ, Σₖ wₖ eₖ)` with `σₙ = √2` and `σₖ = 1`
for `k < n` (`HighMode.incl`), with the discrete differential `𝐝ₙ (u, w) = (0, ((k + 1) σₖ uₖ))`
that makes `iₙ` a cochain map (`HighMode.totalD_incl`) and the cochain projections
`πₙ x = ((σₖ⁻¹ x⁰ₖ), (x¹ₖ))` (`HighMode.family`, `HighMode.proj`): `iₙ πₙ` is the truncation to the
modes `k ≤ n` (`HighMode.tendsto_incl_proj`). The reading maps double the square norm of the
highest mode of degree `0`, `⟪iₙ v, iₙ w⟫ = ⟪v, w⟫ + v⁰ₙ w⁰ₙ` (`HighMode.inner_incl`), so
`1 - iₙ* iₙ` is minus the projection on that mode (`HighMode.one_sub_J_apply`) and
`‖1 - iₙ* iₙ‖ = 1` (`HighMode.norm_one_sub_J`), while `𝐝ₙ` is `(n + 1) √2` on it:
`‖(1 - iₙ* iₙ) v‖ ≤ (‖v‖ + ‖𝐝ₙ v‖) / (n + 1)` (`HighMode.norm_one_sub_J_apply_le`), and the
inner-product defect in the graph norm tends to `0`.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012], §3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace lp
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC.HighMode

/-- The weights of the differentials: `k + 1` for `d⁰ = d 0 1`, `0` for the others. -/
def weight (i j : ℤ) (k : ℕ) : ℝ := if i = 0 ∧ j = 1 then (k : ℝ) + 1 else 0

theorem weight_mul_weight (i j k : ℤ) (n : ℕ) : weight j k n * weight i j n = 0 := by
  unfold weight
  split_ifs with h1 h2 <;> first | (exfalso; omega) | simp

/-- **The witness complex**: `ℓ²` in every degree, `d⁰ = Λ`, `Λ (xₖ) = ((k + 1) xₖ)`, all other
differentials `0`. -/
def complex : HilbertComplex ℝ fun _ : ℤ => ℓ²(ℕ, ℝ) where
  d i j := lp.diagOp (weight i j)
  shape i j h := by
    have hij : ¬ (i = 0 ∧ j = 1) := fun hij => h (by rw [hij.1, hij.2]; norm_num)
    rw [show weight i j = 0 from funext fun k => by simp [weight, hij]]
    exact lp.diagOp_zero
  dense _ _ := lp.dense_diagOp_domain _
  closed _ _ := lp.isClosed_diagOp _
  mapsTo i j k x := by
    rw [lp.mem_diagOp_domain]
    simp_rw [lp.diagOp_apply, ← mul_assoc, weight_mul_weight, zero_mul]
    exact zero_mem_ℓp'
  d_comp_d i j k x := lp.ext (funext fun n => by
    simp only [lp.diagOp_apply, ← mul_assoc, weight_mul_weight, zero_mul]
    rfl)

/-- The window `[0, 2)`: `ℓ² ⊕ ℓ²`. -/
abbrev T : Type := Total (fun _ : ℤ => ℓ²(ℕ, ℝ)) 0 2

theorem totalD_apply (x : (complex.totalD 0 2).domain) (j : Fin 2) (k : ℕ) :
    (complex.totalD 0 2 x : T) j k =
      ∑ i : Fin 2, weight (0 + (i : ℕ)) (0 + (j : ℕ)) k * (x : T) i k := by
  change (∑ i : Fin 2, complex.d (0 + ((i : ℕ) : ℤ)) (0 + ((j : ℕ) : ℤ))
    ⟨(x : T) i, x.2 i j⟩ : ℓ²(ℕ, ℝ)) k = _
  rw [lp.coeFn_sum, Finset.sum_apply]
  rfl

/-- `(𝐝 x)⁰ = 0`. -/
theorem totalD_apply_zero (x : (complex.totalD 0 2).domain) : (complex.totalD 0 2 x : T) 0 = 0 :=
  lp.ext (funext fun k => by rw [totalD_apply]; simp [weight])

/-- `(𝐝 x)¹ = Λ x⁰`. -/
theorem totalD_apply_one (x : (complex.totalD 0 2).domain) (k : ℕ) :
    (complex.totalD 0 2 x : T) 1 k = ((k : ℝ) + 1) * (x : T) 0 k := by
  rw [totalD_apply]; simp [weight]

theorem mem_totalD_domain {x : T} (hx : ∀ i (a : ℕ → ℝ), x i ∈ (lp.diagOp a).domain) :
    x ∈ (complex.totalD 0 2).domain := fun i _ => hx i _

/-- The boundaries of degree `1` are all of `ℓ²` (`Λ` is onto), so closed. -/
theorem isClosed_boundaries : ∀ i : Fin 2, 0 < (i : ℕ) →
    IsClosed (complex.boundaries (0 + (i : ℕ)) : Set ℓ²(ℕ, ℝ)) := by
  intro i hi
  fin_cases i
  · exact absurd hi (lt_irrefl 0)
  · change IsClosed (complex.boundaries 1 : Set ℓ²(ℕ, ℝ))
    have e : weight (1 - 1) 1 = fun k : ℕ => (k : ℝ) + 1 := funext fun k => by simp [weight]
    have h : complex.boundaries 1 = ⊤ := by
      change LinearMap.range (lp.diagOp (weight (1 - 1) 1)).toFun = ⊤
      rw [e]
      refine lp.range_diagOp_eq_top fun k => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [h]
    exact Submodule.top_coe (R := ℝ) (M := ℓ²(ℕ, ℝ)) ▸ isClosed_univ

/-! ### The discrete spaces -/

variable (n : ℕ)

/-- The modes `0, …, n` of one degree, `ℝⁿ⁺¹`. -/
abbrev E : Type := EuclideanSpace ℝ (Fin (n + 1))

/-- The discrete space `Xₙ = ℝⁿ⁺¹ ⊕ ℝⁿ⁺¹` of the modes `0, …, n` in degrees `0` and `1`. -/
abbrev X : Type := PiLp 2 fun _ : Fin 2 => E n

/-- The weight of the reading map in degree `0`: `√2` on the highest mode `k = n`, `1` below. -/
def σ (k : Fin (n + 1)) : ℝ := if k = Fin.last n then √2 else 1

theorem one_le_σ (k : Fin (n + 1)) : 1 ≤ σ n k := by
  unfold σ; split_ifs
  · exact Real.one_lt_sqrt_two.le
  · exact le_rfl

theorem σ_pos (k : Fin (n + 1)) : 0 < σ n k := zero_lt_one.trans_le (one_le_σ n k)

theorem σ_sq (k : Fin (n + 1)) : σ n k ^ 2 = 1 + if k = Fin.last n then 1 else 0 := by
  unfold σ; split_ifs
  · rw [Real.sq_sqrt zero_le_two]; norm_num
  · norm_num

/-- The diagonal map `(uₖ) ↦ (cₖ uₖ)` of `ℝⁿ⁺¹`. -/
def scale (c : Fin (n + 1) → ℝ) : E n →L[ℝ] E n :=
  PiLp.diagOp fun k => c k • ContinuousLinearMap.id ℝ ℝ

variable {n} in
@[simp] theorem scale_apply (c : Fin (n + 1) → ℝ) (u : E n) (k : Fin (n + 1)) :
    scale n c u k = c k * u k := by
  simp [scale, PiLp.diagOp_apply, smul_eq_mul]

/-- The element `(u, w)` of `Xₙ`. -/
abbrev pair (u w : E n) : X n := WithLp.toLp 2 ![u, w]


/-- The reading map `iₙ (u, w) = (Σₖ σₖ uₖ eₖ, Σₖ wₖ eₖ)`. -/
def incl : X n →L[ℝ] T := LinearMap.toContinuousLinearMap
  { toFun := fun v => WithLp.toLp 2 ![lp.ofFin ℝ (n + 1) (scale n (σ n) (v 0)),
      lp.ofFin ℝ (n + 1) (v 1)]
    map_add' := fun v w => by ext i : 1; fin_cases i <;> simp
    map_smul' := fun r v => by ext i : 1; fin_cases i <;> simp }

theorem incl_apply_zero (v : X n) : incl n v 0 = lp.ofFin ℝ (n + 1) (scale n (σ n) (v 0)) := rfl

theorem incl_apply_one (v : X n) : incl n v 1 = lp.ofFin ℝ (n + 1) (v 1) := rfl

/-- The weights `(k + 1) σₖ` of the discrete differential. -/
def dWeight (k : Fin (n + 1)) : ℝ := ((k : ℕ) + 1 : ℝ) * σ n k

/-- The discrete differential `𝐝ₙ (u, w) = (0, ((k + 1) σₖ uₖ))`, which makes `iₙ` a cochain
map. -/
def D : X n →L[ℝ] X n := LinearMap.toContinuousLinearMap
  { toFun := fun v => pair n 0 (scale n (dWeight n) (v 0))
    map_add' := fun v w => by ext i : 1; fin_cases i <;> simp
    map_smul' := fun r v => by ext i : 1; fin_cases i <;> simp }

theorem D_apply_zero (v : X n) : D n v 0 = 0 := rfl

theorem D_apply_one (v : X n) : D n v 1 = scale n (dWeight n) (v 0) := rfl

theorem D_D (v : X n) : D n (D n v) = 0 := by
  ext i : 1
  fin_cases i
  · rfl
  · change scale n (dWeight n) (D n v 0) = 0
    rw [D_apply_zero, _root_.map_zero]

/-- The truncation `x ↦ (xₖ)_{k ≤ n}` of `ℓ²`. -/
abbrev tr : ℓ²(ℕ, ℝ) →L[ℝ] E n := lp.truncFin ℝ (n + 1)

theorem norm_tr_le (y : ℓ²(ℕ, ℝ)) : ‖tr n y‖ ≤ ‖y‖ :=
  ((tr n).le_opNorm y).trans (by
    simpa using mul_le_mul_of_nonneg_right (lp.norm_truncFin_le (𝕜 := ℝ) (n := n + 1))
      (norm_nonneg y))

/-- The cochain projections `πₙ x = ((σₖ⁻¹ x⁰ₖ)ₖ, (x¹ₖ)ₖ)`. -/
def projₗ : T →ₗ[ℝ] X n where
  toFun x := pair n (scale n (fun k => (σ n k)⁻¹) (tr n (x 0))) (tr n (x 1))
  map_add' x y := by ext i : 1; fin_cases i <;> simp
  map_smul' r x := by ext i : 1; fin_cases i <;> simp

theorem norm_X_sq (v : X n) : ‖v‖ ^ 2 = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

theorem norm_T_sq (x : T) : ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

theorem norm_scale_le (c : Fin (n + 1) → ℝ) (hc : ∀ k, |c k| ≤ 1) (u : E n) :
    ‖scale n c u‖ ≤ ‖u‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [scale_apply, norm_mul, mul_pow, Real.norm_eq_abs (c k)]
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (abs_nonneg _) (hc k))

theorem norm_projₗ_le (x : T) : ‖projₗ n x‖ ≤ ‖x‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_X_sq, norm_T_sq]
  have h0 : ‖scale n (fun k => (σ n k)⁻¹) (tr n (x 0))‖ ≤ ‖x 0‖ :=
    (norm_scale_le n _ (fun k => by
      rw [abs_of_pos (inv_pos.2 (σ_pos n k))]
      exact inv_le_one_of_one_le₀ (one_le_σ n k)) _).trans (norm_tr_le n _)
  have h1 := norm_tr_le n (x 1)
  change ‖scale n (fun k => (σ n k)⁻¹) (tr n (x 0))‖ ^ 2 + ‖tr n (x 1)‖ ^ 2 ≤ _
  gcongr

/-- The cochain projections as bounded operators, `‖πₙ‖ ≤ 1`. -/
def projL : T →L[ℝ] X n := (projₗ n).mkContinuous 1 fun x => by
  rw [one_mul]; exact norm_projₗ_le n x

theorem projₗ_incl (v : X n) : projₗ n (incl n v) = v := by
  ext i k
  fin_cases i
  · change (scale n _ (tr n (lp.ofFin ℝ (n + 1) (scale n (σ n) (v 0))))) k = v 0 k
    rw [lp.truncFin_ofFin, scale_apply, scale_apply, inv_mul_cancel_left₀ (σ_pos n k).ne']
  · change tr n (lp.ofFin ℝ (n + 1) (v 1)) k = v 1 k
    rw [lp.truncFin_ofFin]

/-! ### The inner-product defect -/

/-- The highest mode `(eₙ, 0)` of degree `0`. -/
def top : X n := pair n (EuclideanSpace.single (Fin.last n) 1) 0

theorem inner_top (w : X n) : ⟪top n, w⟫_ℝ = w 0 (Fin.last n) := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  change ⟪EuclideanSpace.single (Fin.last n) (1 : ℝ), w 0⟫_ℝ + ⟪(0 : E n), w 1⟫_ℝ = _
  rw [EuclideanSpace.inner_single_left, inner_zero_left]
  simp

theorem norm_top : ‖top n‖ = 1 := by
  have e := inner_top n (top n)
  rw [real_inner_self_eq_norm_sq] at e
  have e1 : top n 0 (Fin.last n) = 1 := by simp [top]
  rw [e1] at e
  nlinarith [norm_nonneg (top n)]

theorem inner_scale_scale (u w : E n) :
    ⟪scale n (σ n) u, scale n (σ n) w⟫_ℝ = ⟪u, w⟫_ℝ + u (Fin.last n) * w (Fin.last n) := by
  simp only [PiLp.inner_apply, scale_apply, RCLike.inner_apply, conj_trivial]
  have e : ∀ k, σ n k * w k * (σ n k * u k) =
      w k * u k + if k = Fin.last n then u k * w k else 0 := fun k => by
    rw [show σ n k * w k * (σ n k * u k) = σ n k ^ 2 * (w k * u k) by ring, σ_sq]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- `⟪iₙ v, iₙ w⟫ = ⟪v, w⟫ + v⁰ₙ w⁰ₙ`: the reading maps double the square norm of the highest mode
of degree `0`. -/
theorem inner_incl (v w : X n) :
    ⟪incl n v, incl n w⟫_ℝ = ⟪v, w⟫_ℝ + v 0 (Fin.last n) * w 0 (Fin.last n) := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, PiLp.inner_apply v w, Fin.sum_univ_two]
  change ⟪lp.ofFin ℝ (n + 1) (scale n (σ n) (v 0)), lp.ofFin ℝ (n + 1) (scale n (σ n) (w 0))⟫_ℝ +
    ⟪lp.ofFin ℝ (n + 1) (v 1), lp.ofFin ℝ (n + 1) (w 1)⟫_ℝ = _
  rw [lp.inner_ofFin_ofFin, lp.inner_ofFin_ofFin, inner_scale_scale]
  ring

/-- **`1 - iₙ* iₙ` is minus the projection on the highest mode of degree `0`**:
`(1 - iₙ* iₙ) v = -v⁰ₙ (eₙ, 0)`. -/
theorem one_sub_J_apply (v : X n) :
    (1 - (incl n).adjoint ∘L incl n) v = -(v 0 (Fin.last n)) • top n := by
  refine ext_inner_right ℝ fun w => ?_
  rw [_root_.sub_apply, one_apply_eq_self, inner_sub_left,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left, inner_incl,
    inner_smul_left, inner_top]
  simp

theorem norm_one_sub_J_apply (v : X n) :
    ‖(1 - (incl n).adjoint ∘L incl n) v‖ = |v 0 (Fin.last n)| := by
  rw [one_sub_J_apply, norm_smul, norm_neg, norm_top, mul_one, Real.norm_eq_abs]

theorem abs_top_le (v : X n) : |v 0 (Fin.last n)| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact (PiLp.norm_apply_le (v 0) _).trans (PiLp.norm_apply_le v 0)

/-- **`‖1 - iₙ* iₙ‖ = 1`** for every `n`. -/
theorem norm_one_sub_J : ‖1 - (incl n).adjoint ∘L incl n‖ = 1 := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_) ?_
  · rw [norm_one_sub_J_apply, one_mul]; exact abs_top_le n v
  · have h := (1 - (incl n).adjoint ∘L incl n).le_opNorm (top n)
    rw [norm_one_sub_J_apply, norm_top, mul_one] at h
    have e1 : top n 0 (Fin.last n) = 1 := by simp [top]
    rwa [e1, abs_one] at h

/-- `𝐝ₙ` is `(n + 1) √2` on the highest mode of degree `0`: `(n + 1) |v⁰ₙ| ≤ ‖𝐝ₙ v‖`. -/
theorem mul_abs_top_le (v : X n) : ((n : ℝ) + 1) * |v 0 (Fin.last n)| ≤ ‖D n v‖ := by
  have h := (PiLp.norm_apply_le (D n v 1) (Fin.last n)).trans (PiLp.norm_apply_le (D n v) 1)
  rw [D_apply_one, scale_apply, Real.norm_eq_abs, abs_mul] at h
  refine le_trans ?_ h
  have hw : dWeight n (Fin.last n) = ((n : ℝ) + 1) * √2 := by
    simp [dWeight, σ]
  rw [hw, abs_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) * √2 by positivity)]
  calc ((n : ℝ) + 1) * |v 0 (Fin.last n)| = ((n : ℝ) + 1) * |v 0 (Fin.last n)| * 1 := by ring
    _ ≤ ((n : ℝ) + 1) * |v 0 (Fin.last n)| * √2 :=
        mul_le_mul_of_nonneg_left Real.one_lt_sqrt_two.le (by positivity)
    _ = ((n : ℝ) + 1) * √2 * |v 0 (Fin.last n)| := by ring

/-- **The defect in the graph norm vanishes**: `‖(1 - iₙ* iₙ) v‖ ≤ (‖v‖ + ‖𝐝ₙ v‖) / (n + 1)`. -/
theorem norm_one_sub_J_apply_le (v : X n) :
    ‖(1 - (incl n).adjoint ∘L incl n) v‖ ≤ 1 / ((n : ℝ) + 1) * (‖v‖ + ‖D n v‖) := by
  rw [norm_one_sub_J_apply, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  have := mul_abs_top_le n v
  nlinarith [norm_nonneg v]


theorem norm_incl_apply_le (v : X n) : ‖incl n v‖ ≤ 2 * ‖v‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  have e := inner_incl n v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at e
  have h := abs_top_le n v
  have h2 : v 0 (Fin.last n) * v 0 (Fin.last n) ≤ ‖v‖ ^ 2 := by
    rw [← abs_mul_abs_self, pow_two]
    exact mul_self_le_mul_self (abs_nonneg _) h
  rw [e, mul_pow]
  nlinarith [norm_nonneg v]

theorem norm_incl_le : ‖incl n‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_two (norm_incl_apply_le n)

/-- **The witness family**: the modes `0, …, n` of both degrees, `Xₙ = ℝⁿ⁺¹ ⊕ ℝⁿ⁺¹`, read by
`iₙ`, with the discrete differential `𝐝ₙ` and the left inverses `πₙ`. -/
def family : complex.CrimeFamily.{0} 0 2 ℕ where
  l := atTop
  X := X
  D := D
  D_D := D_D
  incl := incl
  proj := projL
  proj_incl := projₗ_incl
  bound := ⟨2, fun n => ⟨norm_incl_le n,
    (LinearMap.mkContinuous_norm_le _ zero_le_one _).trans one_le_two⟩⟩

theorem incl_mem (v : X n) : incl n v ∈ (complex.totalD 0 2).domain :=
  mem_totalD_domain fun i a => by
    refine (Fin.forall_fin_two.2 ⟨?_, ?_⟩ : ∀ i : Fin 2, (incl n v : T) i ∈ (lp.diagOp a).domain) i
    · exact lp.ofFin_mem_diagOp_domain a _
    · exact lp.ofFin_mem_diagOp_domain a _

/-- **`iₙ` is a cochain map**: `𝐝 iₙ = iₙ 𝐝ₙ`. -/
theorem totalD_incl (v : X n) :
    complex.totalD 0 2 ⟨incl n v, incl_mem n v⟩ = incl n (D n v) := by
  refine PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · rw [totalD_apply_zero]
    change 0 = lp.ofFin ℝ (n + 1) (scale n (σ n) (D n v 0))
    rw [D_apply_zero, _root_.map_zero, _root_.map_zero]
  · refine lp.ext (funext fun k => ?_)
    rw [totalD_apply_one]
    change ((k : ℝ) + 1) * lp.ofFin ℝ (n + 1) (scale n (σ n) (v 0)) k =
      lp.ofFin ℝ (n + 1) (D n v 1) k
    rw [D_apply_one, lp.ofFin_apply, lp.ofFin_apply]
    split_ifs
    · simp only [scale_apply, dWeight]; ring
    · rw [mul_zero]

theorem isCochain : family.IsCochain := ⟨fun n v => incl_mem n v, fun n v => totalD_incl n v⟩

theorem scale_σ_inv (u : E n) : scale n (σ n) (scale n (fun k => (σ n k)⁻¹) u) = u :=
  PiLp.ext fun k => by rw [scale_apply, scale_apply, mul_inv_cancel_left₀ (σ_pos n k).ne']

/-- **`πₙ` commutes with the differentials**: `πₙ 𝐝 = 𝐝ₙ πₙ` on `D(𝐝)`. -/
theorem projₗ_totalD (z : (complex.totalD 0 2).domain) :
    projₗ n (complex.totalD 0 2 z) = D n (projₗ n z) := by
  refine PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · change scale n _ (tr n ((complex.totalD 0 2 z : T) 0)) = D n (projₗ n z) 0
    rw [totalD_apply_zero, _root_.map_zero, _root_.map_zero, D_apply_zero]
  · refine PiLp.ext fun k => ?_
    change tr n ((complex.totalD 0 2 z : T) 1) k = D n (projₗ n (z : T)) 1 k
    rw [D_apply_one, scale_apply, lp.truncFin_apply, totalD_apply_one]
    change ((k : ℕ) + 1 : ℝ) * (z : T) 0 k =
      dWeight n k * (scale n (fun k => (σ n k)⁻¹) (tr n ((z : T) 0)) k)
    rw [scale_apply, lp.truncFin_apply, dWeight, mul_assoc, mul_inv_cancel_left₀ (σ_pos n k).ne']

/-- **The cochain projections** `πₙ`, bounded by `1` in the graph norm. -/
def proj : family.CochainProj 1 where
  π := projₗ
  π_incl := projₗ_incl
  norm_π_le n x := by
    have h1 := norm_projₗ_le n (x : T)
    have h2 := norm_nonneg (complex.totalD 0 2 x)
    change ‖projₗ n (x : T)‖ ≤ 1 * (‖(x : T)‖ + ‖complex.totalD 0 2 x‖)
    linarith
  π_totalD n z := projₗ_totalD n z

theorem norm_T_le (y : T) : ‖y‖ ≤ ‖y 0‖ + ‖y 1‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [norm_T_sq]
  nlinarith [norm_nonneg (y 0), norm_nonneg (y 1)]

theorem tendsto_sub_ofFin_tr (y : ℓ²(ℕ, ℝ)) :
    Tendsto (fun n => ‖y - lp.ofFin ℝ (n + 1) (tr n y)‖) atTop (𝓝 0) := by
  have h := (lp.tendsto_ofFin_truncFin (𝕜 := ℝ) y).comp (tendsto_add_atTop_nat 1)
  simpa [Function.comp_def, norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.1 h

/-- **`iₙ πₙ → 1`**: `iₙ πₙ` is the truncation to the modes `0, …, n` of both degrees. -/
theorem tendsto_incl_proj (x : T) :
    Tendsto (fun n => ‖x - incl n (projₗ n x)‖) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => (norm_T_le _).trans (le_of_eq ?_))
    (by simpa using (tendsto_sub_ofFin_tr (x 0)).add (tendsto_sub_ofFin_tr (x 1)))
  change ‖x 0 - lp.ofFin ℝ (n + 1) (scale n (σ n) (scale n (fun k => (σ n k)⁻¹) (tr n (x 0))))‖ +
    ‖x 1 - lp.ofFin ℝ (n + 1) (tr n (x 1))‖ = _
  rw [scale_σ_inv]

end FEEC.HighMode
