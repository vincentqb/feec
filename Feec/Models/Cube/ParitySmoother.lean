module

public import Feec.Models.Cube.DeRhamPartialIdent
public import Feec.Domain.Mollify
public import Feec.FiniteElement.WeakSymmetryMaps
public import Feec.FiniteElement.InverseEstimate
public import Feec.Domain.StarShapedSmoothing
public import Mathlib.MeasureTheory.Integral.Pi
public import Feec.Models.Cube.PolyRate
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.LinearAlgebra.Lagrange

/-!
# The parity smoother on the cube

For a class `J ⊆ {1, …, n}` of the partially-homogeneous complexes `HΛ_J(Q)` on the unit cube
`Q = (0, ½)ⁿ` (`Feec.Models.Cube.DeRhamPartialIdent`; vanishing tangential trace on the faces
normal to `e_j`, `j ∈ J`), the **parity smoother** is `R^J_ρ u = (ρ ⋆ ext_J u)|_Q`: each coefficient
`u_s` of a `k`-form is extended to `ℝⁿ` by reflections across the faces of `Q`, odd across the
faces where it must vanish and even across the others (the parity vector `c(J, s)`, `pvec`), and
then mollified by a reflection-invariant kernel `ρ` of radius `< ½`. In contrast with the smoothers
of [ChristiansenWinther2008] and [AFW2010], §5.4, no dilation is needed: the reflected extension
already lies in the class `J`, so `R` commutes with `d_J` exactly, with the same smoother for all
classes and both rows of the BGG complex.

## Main definitions

* `triW`, `pieceMap`, `bigCube`: the folding of `ℝ` onto `[0, ½]` and the `3ⁿ` reflected copies of
  `Q` tiling `(-½, 1)ⁿ`.
* `parExt c f`: the parity extension; `ReflKernel n`: reflection-invariant mollifiers;
  `prodKernel`: a product of one-dimensional bumps, of any radius `r < ½`.
* `smoothFun ρ c f = ρ ⋆ ext_c f`, `scalarSmooth ρ c`: the scalar parity smoother on `L²(Q)`.
* `MomentKernel n m`: reflection-invariant (signed) kernels with vanishing moments of the orders
  `1, …, m - 1`.

## Main results

* `integral_sq_smoothFun_le`, `norm_scalarSmoothₗ_le`: `‖R f‖ ≤ 3^{n/2} ‖f‖`.
* `extD_smoothFun_eq`: for `u ∈ D(d_J)` the smoothed parity extension commutes with `d_J`,
  pointwise on `cl Q`.
* `norm_sub_scalarSmooth_le_grad`: `‖f - R f‖ ≤ r √(n 3ⁿ) ‖∇ f‖` for `f ∈ D(d_{J'})` in degree `0`
  ([Brezis2011], §9.2, for the reflection argument).
* `integral_sq_sub_conv_le_of_moments`: the high-order estimate
  `‖G - ρ ⋆ G‖²_{L²(Q)} ≤ ‖ρ‖₁² (rᵐ / (m - 1)!)² 3ⁿ ‖Dᵐ G‖²_{L²(Q)}` for functions `G` of
  parity `c` that are `Cᵐ` on `ℝⁿ` (the parity extensions of data on `Q` satisfying the reflection
  compatibility conditions: for the parity `+1` in the direction `j` the odd-order normal
  derivatives vanish on the faces normal to `e_j`, for `-1` the even-order ones, the value
  included) and kernels with vanishing moments.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §5.4
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011], §9.2

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal Convolution

namespace Feec.Models.Cube.ParitySmoother

open Feec.Domain Feec.Models.Cube.Geometry

variable {n : ℕ}

/-! ### Folding the line onto `[0, ½]` -/

/-- The triangle wave `x ↦ dist(x, ℤ)`, which folds `ℝ` onto `[0, ½]`. -/
def triW (x : ℝ) : ℝ := |x - round x|

theorem triW_eq_min (x : ℝ) : triW x = min (Int.fract x) (1 - Int.fract x) :=
  abs_sub_round_eq_min x

theorem triW_le (x : ℝ) (m : ℤ) : triW x ≤ |x - m| := round_le x m

theorem triW_add_intCast (x : ℝ) (m : ℤ) : triW (x + m) = triW x := by
  rw [triW_eq_min, triW_eq_min, Int.fract_add_intCast]

theorem triW_neg (x : ℝ) : triW (-x) = triW x := by
  refine le_antisymm ?_ ?_
  · calc triW (-x) ≤ |-x - ((-round x : ℤ) : ℝ)| := triW_le _ _
      _ = triW x := by rw [triW]; push_cast; rw [← abs_neg]; ring_nf
  · calc triW x ≤ |x - ((-round (-x) : ℤ) : ℝ)| := triW_le _ _
      _ = triW (-x) := by rw [triW]; push_cast; rw [← abs_neg]; ring_nf

theorem triW_of_mem_Icc {z : ℝ} (hz : z ∈ Icc (0 : ℝ) (1 / 2)) : triW z = z := by
  refine le_antisymm ((triW_le z 0).trans (by simp [abs_of_nonneg hz.1])) ?_
  rw [triW]
  rcases le_or_gt (round z) 0 with h | h
  · have : (round z : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith [hz.1])]; linarith
  · have : (1 : ℝ) ≤ round z := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith [hz.2])]; linarith [hz.2]

/-- The sign of the reflected copy containing `x`: `1` on `[m, m + ½]`, `c` on `(m + ½, m + 1)`. -/
def parSgn (c x : ℝ) : ℝ := if Int.fract x ≤ 1 / 2 then 1 else c

theorem parSgn_add_intCast (c x : ℝ) (m : ℤ) : parSgn c (x + m) = parSgn c x := by
  simp only [parSgn, Int.fract_add_intCast]

/-! ### The three reflected copies of `(0, ½)` in `(-½, 1)` -/

/-- The three affine maps of the folding: `z ↦ -z`, `z ↦ z`, `z ↦ 1 - z`. -/
def piece : Fin 3 → ℝ → ℝ
  | 0 => fun z => -z
  | 1 => fun z => z
  | 2 => fun z => 1 - z

@[simp] theorem piece_zero (z : ℝ) : piece 0 z = -z := rfl
@[simp] theorem piece_one (z : ℝ) : piece 1 z = z := rfl
@[simp] theorem piece_two (z : ℝ) : piece 2 z = 1 - z := rfl

theorem piece_piece (q : Fin 3) (z : ℝ) : piece q (piece q z) = z := by
  fin_cases q <;> simp

/-- The image interval of `(0, ½)` under `piece q`. -/
def pieceIoo : Fin 3 → Set ℝ
  | 0 => Ioo (-(1 / 2)) 0
  | 1 => Ioo 0 (1 / 2)
  | 2 => Ioo (1 / 2) 1

theorem piece_mem_Ioo_iff (q : Fin 3) (z : ℝ) :
    piece q z ∈ Ioo (0 : ℝ) (1 / 2) ↔ z ∈ pieceIoo q := by
  fin_cases q <;> simp [pieceIoo] <;> constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem eq_of_mem_pieceIoo {q q' : Fin 3} {z : ℝ} (h : z ∈ pieceIoo q) (h' : z ∈ pieceIoo q') :
    q = q' := by
  fin_cases q <;> fin_cases q' <;> simp [pieceIoo] at h h' ⊢ <;> linarith [h.1, h.2, h'.1, h'.2]

theorem exists_mem_pieceIoo {z : ℝ} (hz : z ∈ Ioo (-(1 / 2) : ℝ) 1) (h0 : z ≠ 0) (h1 : z ≠ 1 / 2) :
    ∃ q, z ∈ pieceIoo q := by
  rcases lt_or_gt_of_ne h0 with h | h
  · exact ⟨0, hz.1, h⟩
  · rcases lt_or_gt_of_ne h1 with h' | h'
    · exact ⟨1, h, h'⟩
    · exact ⟨2, h', hz.2⟩

theorem pieceIoo_subset (q : Fin 3) : pieceIoo q ⊆ Ioo (-(1 / 2) : ℝ) 1 := by
  intro z hz
  fin_cases q <;> simp [pieceIoo] at hz <;> constructor <;> linarith [hz.1, hz.2]

theorem triW_piece {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) (1 / 2)) (q : Fin 3) : triW (piece q z) = z := by
  have hz' : z ∈ Icc (0 : ℝ) (1 / 2) := Ioo_subset_Icc_self hz
  fin_cases q
  · simp [triW_neg, triW_of_mem_Icc hz']
  · simp [triW_of_mem_Icc hz']
  · simp only [Fin.reduceFinMk, piece_two]
    have : (1 : ℝ) - z = -z + ((1 : ℤ) : ℝ) := by push_cast; ring
    rw [this, triW_add_intCast, triW_neg, triW_of_mem_Icc hz']

/-- The sign of the copy `q` for the parity `c`. -/
def pieceSgn (c : ℝ) (q : Fin 3) : ℝ := if q = 1 then 1 else c

theorem parSgn_piece {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) (1 / 2)) (c : ℝ) (q : Fin 3) :
    parSgn c (piece q z) = pieceSgn c q := by
  fin_cases q
  · have hf : Int.fract (-z) = 1 - z := by
      rw [Int.fract_neg (by rw [Int.fract_eq_self.2 ⟨hz.1.le, by linarith [hz.2]⟩]; exact hz.1.ne'),
        Int.fract_eq_self.2 ⟨hz.1.le, by linarith [hz.2]⟩]
    simp [parSgn, pieceSgn, hf]
    intro h; linarith [hz.2]
  · simp [parSgn, pieceSgn, Int.fract_eq_self.2 ⟨hz.1.le, by linarith [hz.2]⟩]
    intro h; linarith [hz.2]
  · have hf : Int.fract (1 - z) = 1 - z :=
      Int.fract_eq_self.2 ⟨by linarith [hz.2], by linarith [hz.1]⟩
    simp [parSgn, pieceSgn, hf]
    intro h; linarith [hz.2]

/-- `piece q z = pieceOff q + pieceSig q * z`. -/
def pieceSig (q : Fin 3) : ℝ := if q = 1 then 1 else -1

/-- The offset of `piece q`. -/
def pieceOff (q : Fin 3) : ℝ := if q = 2 then 1 else 0

theorem piece_eq (q : Fin 3) (z : ℝ) : piece q z = pieceOff q + pieceSig q * z := by
  fin_cases q <;> simp [pieceOff, pieceSig]; ring

theorem continuous_piece (q : Fin 3) : Continuous (piece q) := by
  have : piece q = fun z => pieceOff q + pieceSig q * z := funext (piece_eq q)
  rw [this]; fun_prop

theorem measurePreserving_piece (q : Fin 3) :
    MeasurePreserving (piece q) (volume : Measure ℝ) volume := by
  fin_cases q
  · exact Measure.measurePreserving_neg volume
  · exact MeasurePreserving.id volume
  · exact volume.measurePreserving_sub_left 1

theorem pieceSgn_neg (c : ℝ) (q : Fin 3) : pieceSgn (-c) q = pieceSig q * pieceSgn c q := by
  fin_cases q <;> simp [pieceSgn, pieceSig]

/-! ### The `3ⁿ` reflected copies of `Q` in `U = (-½, 1)ⁿ` -/

variable (n) in
/-- The cube `U = (-½, 1)ⁿ`, covered (up to a null set) by the `3ⁿ` reflected copies of `Q`. -/
def bigCube : Set (Fin n → ℝ) := univ.pi fun _ => Ioo (-(1 / 2) : ℝ) 1

theorem mem_bigCube {x : Fin n → ℝ} : x ∈ bigCube n ↔ ∀ j, x j ∈ Ioo (-(1 / 2) : ℝ) 1 := by
  simp [bigCube]

/-- The reflection of `Q` onto its copy `p`: `z ↦ (piece (p j) (z j))ⱼ`. -/
def pieceMap (p : Fin n → Fin 3) (z : Fin n → ℝ) : Fin n → ℝ := fun j => piece (p j) (z j)

@[simp] theorem pieceMap_apply (p : Fin n → Fin 3) (z : Fin n → ℝ) (j : Fin n) :
    pieceMap p z j = piece (p j) (z j) := rfl

theorem pieceMap_pieceMap (p : Fin n → Fin 3) (z : Fin n → ℝ) : pieceMap p (pieceMap p z) = z :=
  funext fun _ => piece_piece _ _

theorem continuous_pieceMap (p : Fin n → Fin 3) : Continuous (pieceMap p) :=
  continuous_pi fun j => (continuous_piece (p j)).comp (continuous_apply j)

/-- `pieceMap p` as a measurable involution. -/
def pieceEquiv (p : Fin n → Fin 3) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) where
  toFun := pieceMap p
  invFun := pieceMap p
  left_inv := pieceMap_pieceMap p
  right_inv := pieceMap_pieceMap p
  measurable_toFun := (continuous_pieceMap p).measurable
  measurable_invFun := (continuous_pieceMap p).measurable

theorem measurableEmbedding_pieceMap (p : Fin n → Fin 3) : MeasurableEmbedding (pieceMap p) :=
  (pieceEquiv p).measurableEmbedding

theorem measurePreserving_pieceMap (p : Fin n → Fin 3) :
    MeasurePreserving (pieceMap p) (volume : Measure (Fin n → ℝ)) volume :=
  measurePreserving_pi _ _ fun j => measurePreserving_piece (p j)

theorem pieceMap_mem_Q_iff (p : Fin n → Fin 3) (x : Fin n → ℝ) :
    pieceMap p x ∈ Q (Fin n) ↔ ∀ j, x j ∈ pieceIoo (p j) := by
  rw [mem_Q]; exact forall_congr' fun j => piece_mem_Ioo_iff (p j) (x j)

theorem pieceMap_preimage_preimage (p : Fin n → Fin 3) (s : Set (Fin n → ℝ)) :
    pieceMap p ⁻¹' (pieceMap p ⁻¹' s) = s := by
  ext x; simp [pieceMap_pieceMap]

theorem measurableSet_pieceMap_preimage_Q (p : Fin n → Fin 3) :
    MeasurableSet (pieceMap p ⁻¹' Q (Fin n)) :=
  measurableSet_Q.preimage (continuous_pieceMap p).measurable

theorem mem_bigCube_of_pieceMap_mem_Q {p : Fin n → Fin 3} {x : Fin n → ℝ}
    (hx : pieceMap p x ∈ Q (Fin n)) : x ∈ bigCube n :=
  mem_bigCube.2 fun j => pieceIoo_subset _ ((pieceMap_mem_Q_iff p x).1 hx j)

theorem eq_of_pieceMap_mem_Q {p p' : Fin n → Fin 3} {x : Fin n → ℝ}
    (hx : pieceMap p x ∈ Q (Fin n)) (hx' : pieceMap p' x ∈ Q (Fin n)) : p = p' :=
  funext fun j => eq_of_mem_pieceIoo ((pieceMap_mem_Q_iff p x).1 hx j)
    ((pieceMap_mem_Q_iff p' x).1 hx' j)

/-- Almost every point has no coordinate in `{0, ½}`. -/
theorem ae_coord_ne : ∀ᵐ x : Fin n → ℝ, ∀ j, x j ≠ 0 ∧ x j ≠ 1 / 2 :=
  ae_all_iff.2 fun j => (Measure.ae_eval_ne _ j 0).and (Measure.ae_eval_ne _ j (1 / 2))

/-- **The tiling of `U` by the reflected copies of `Q`**, pointwise. -/
theorem sum_indicator_pieceMap {E : Type*} [AddCommMonoid E] {G : (Fin n → ℝ) → E}
    (hG : ∀ x, x ∉ bigCube n → G x = 0) {x : Fin n → ℝ} (hx : ∀ j, x j ≠ 0 ∧ x j ≠ 1 / 2) :
    ∑ p : Fin n → Fin 3, (pieceMap p ⁻¹' Q (Fin n)).indicator G x = G x := by
  classical
  by_cases hU : x ∈ bigCube n
  · have hq : ∀ j, ∃ q, x j ∈ pieceIoo q := fun j =>
      exists_mem_pieceIoo (mem_bigCube.1 hU j) (hx j).1 (hx j).2
    choose p hp using hq
    have hpQ : pieceMap p x ∈ Q (Fin n) := (pieceMap_mem_Q_iff p x).2 hp
    rw [Finset.sum_eq_single p (fun p' _ hp' => Set.indicator_of_notMem
      (show x ∉ pieceMap p' ⁻¹' Q (Fin n) from fun h => hp' (eq_of_pieceMap_mem_Q h hpQ)) G)
      (by simp), Set.indicator_of_mem (show x ∈ pieceMap p ⁻¹' Q (Fin n) from hpQ)]
  · rw [hG x hU]
    exact Finset.sum_eq_zero fun p _ => Set.indicator_of_notMem
      (show x ∉ pieceMap p ⁻¹' Q (Fin n) from fun h => hU (mem_bigCube_of_pieceMap_mem_Q h)) G

/-- **Integration over `U` by the tiling**: for `G` vanishing off `U` and integrable on each copy,
`G` is integrable and `∫ G = Σ_p ∫_Q G ∘ pieceMap p`. -/
theorem integral_eq_sum_pieceMap {G : (Fin n → ℝ) → ℝ} (hG : ∀ x, x ∉ bigCube n → G x = 0)
    (hint : ∀ p : Fin n → Fin 3, IntegrableOn (fun z => G (pieceMap p z)) (Q (Fin n))) :
    Integrable G ∧ ∫ x, G x = ∑ p : Fin n → Fin 3, ∫ z in Q (Fin n), G (pieceMap p z) := by
  have hInt : ∀ p : Fin n → Fin 3, IntegrableOn G (pieceMap p ⁻¹' Q (Fin n)) := by
    intro p
    have h := (measurePreserving_pieceMap p).integrableOn_comp_preimage
      (measurableEmbedding_pieceMap p) (f := G) (s := pieceMap p ⁻¹' Q (Fin n))
    rw [pieceMap_preimage_preimage] at h
    exact h.1 (hint p)
  have hae : (fun x => ∑ p : Fin n → Fin 3, (pieceMap p ⁻¹' Q (Fin n)).indicator G x) =ᵐ[volume] G := by
    filter_upwards [ae_coord_ne] with x hx
    exact sum_indicator_pieceMap hG hx
  have hsum : Integrable fun x => ∑ p : Fin n → Fin 3, (pieceMap p ⁻¹' Q (Fin n)).indicator G x :=
    integrable_finsetSum _ fun p _ =>
      (hInt p).integrable_indicator (measurableSet_pieceMap_preimage_Q p)
  refine ⟨hsum.congr hae, ?_⟩
  rw [← integral_congr_ae hae, integral_finsetSum _ fun p _ =>
    (hInt p).integrable_indicator (measurableSet_pieceMap_preimage_Q p)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_indicator (measurableSet_pieceMap_preimage_Q p)]
  have h := (measurePreserving_pieceMap p).setIntegral_preimage_emb
    (measurableEmbedding_pieceMap p) (fun z => G (pieceMap p z)) (Q (Fin n))
  simpa only [pieceMap_pieceMap] using h

theorem exists_pieceMap_mem_Q {x : Fin n → ℝ} (hU : x ∈ bigCube n)
    (hx : ∀ j, x j ≠ 0 ∧ x j ≠ 1 / 2) : ∃ p : Fin n → Fin 3, pieceMap p x ∈ Q (Fin n) := by
  have hq : ∀ j, ∃ q, x j ∈ pieceIoo q := fun j =>
    exists_mem_pieceIoo (mem_bigCube.1 hU j) (hx j).1 (hx j).2
  choose p hp using hq
  exact ⟨p, (pieceMap_mem_Q_iff p x).2 hp⟩

/-- **Almost every point of `U` lies in the interior of one copy**, and a property holding a.e. on
`Q` holds at its image there. -/
theorem ae_exists_pieceMap {P : (Fin n → ℝ) → Prop} (h : ∀ᵐ z ∂volume, z ∈ Q (Fin n) → P z) :
    ∀ᵐ t ∂volume, t ∈ bigCube n →
      ∃ p : Fin n → Fin 3, pieceMap p t ∈ Q (Fin n) ∧ P (pieceMap p t) := by
  have hp : ∀ p : Fin n → Fin 3, ∀ᵐ t ∂volume, pieceMap p t ∈ Q (Fin n) → P (pieceMap p t) :=
    fun p => (measurePreserving_pieceMap p).quasiMeasurePreserving.ae h
  filter_upwards [ae_all_iff.2 hp, ae_coord_ne] with t ht ht0 htU
  obtain ⟨p, hpt⟩ := exists_pieceMap_mem_Q htU ht0
  exact ⟨p, hpt, ht p hpt⟩

/-! ### The parity extension -/

/-- A **parity vector**: `c j = ± 1` for every direction. -/
def IsParity (c : Fin n → ℝ) : Prop := ∀ j, c j = 1 ∨ c j = -1

/-- The folding map `ℝⁿ → [0, ½]ⁿ`, coordinatewise `triW`. -/
def foldPt (x : Fin n → ℝ) : Fin n → ℝ := fun j => triW (x j)

/-- The sign of the reflected copy of `Q` containing `x`, for the parity vector `c`. -/
def extSgn (c : Fin n → ℝ) (x : Fin n → ℝ) : ℝ := ∏ j, parSgn (c j) (x j)

/-- **The parity extension** `ext_c f (x) = sign_c(x) f(fold x)` of a function on `Q`: periodic of
period `1` in every variable, with parity `c_j` in `x_j` about `0` and about `½`. -/
def parExt (c : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  extSgn c x * f (foldPt x)

/-- The sign of the copy `p` of `Q` for the parity vector `c`. -/
def pieceSign (c : Fin n → ℝ) (p : Fin n → Fin 3) : ℝ := ∏ j, pieceSgn (c j) (p j)

theorem foldPt_pieceMap {z : Fin n → ℝ} (hz : z ∈ Q (Fin n)) (p : Fin n → Fin 3) :
    foldPt (pieceMap p z) = z :=
  funext fun j => triW_piece (mem_Q.1 hz j) (p j)

theorem extSgn_pieceMap {z : Fin n → ℝ} (hz : z ∈ Q (Fin n)) (c : Fin n → ℝ)
    (p : Fin n → Fin 3) : extSgn c (pieceMap p z) = pieceSign c p :=
  Finset.prod_congr rfl fun j _ => parSgn_piece (mem_Q.1 hz j) (c j) (p j)

theorem parExt_pieceMap {z : Fin n → ℝ} (hz : z ∈ Q (Fin n)) (c : Fin n → ℝ)
    (f : (Fin n → ℝ) → ℝ) (p : Fin n → Fin 3) :
    parExt c f (pieceMap p z) = pieceSign c p * f z := by
  rw [parExt, foldPt_pieceMap hz, extSgn_pieceMap hz]

theorem parExt_eq_of_pieceMap_mem {t : Fin n → ℝ} {p : Fin n → Fin 3}
    (ht : pieceMap p t ∈ Q (Fin n)) (c : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) :
    parExt c f t = pieceSign c p * f (pieceMap p t) := by
  have h := parExt_pieceMap ht c f p
  rwa [pieceMap_pieceMap] at h

theorem abs_pieceSgn {c : ℝ} (hc : c = 1 ∨ c = -1) (q : Fin 3) : |pieceSgn c q| = 1 := by
  unfold pieceSgn; split_ifs <;> rcases hc with h | h <;> simp [h]

theorem abs_pieceSign {c : Fin n → ℝ} (hc : IsParity c) (p : Fin n → Fin 3) :
    |pieceSign c p| = 1 := by
  rw [pieceSign, Finset.abs_prod]
  exact Finset.prod_eq_one fun j _ => abs_pieceSgn (hc j) (p j)

theorem pieceSign_sq {c : Fin n → ℝ} (hc : IsParity c) (p : Fin n → Fin 3) :
    pieceSign c p ^ 2 = 1 := by
  rw [← sq_abs, abs_pieceSign hc]; norm_num

theorem parExt_add (c : Fin n → ℝ) (f g : (Fin n → ℝ) → ℝ) :
    parExt c (f + g) = parExt c f + parExt c g := by
  funext x; simp [parExt, mul_add]

theorem parExt_smul (c : Fin n → ℝ) (a : ℝ) (f : (Fin n → ℝ) → ℝ) :
    parExt c (a • f) = a • parExt c f := by
  funext x; simp [parExt]; ring

/-- **Periodicity of the parity extension.** -/
theorem parExt_add_intCast (c : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (m : Fin n → ℤ) : parExt c f (x + fun j => (m j : ℝ)) = parExt c f x := by
  have h1 : foldPt (x + fun j => (m j : ℝ)) = foldPt x :=
    funext fun j => by simp only [foldPt, Pi.add_apply, triW_add_intCast]
  have h2 : extSgn c (x + fun j => (m j : ℝ)) = extSgn c x :=
    Finset.prod_congr rfl fun j _ => by simp only [Pi.add_apply, parSgn_add_intCast]
  rw [parExt, parExt, h1, h2]

/-- The fold `Σ_p sign_c(p) φ ∘ pieceMap p` of a function on `U`: `∫ ext_c f · φ = ∫_Q f · fold φ`
(`integral_parExt_mul`). -/
def foldFun (c : Fin n → ℝ) (φ : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ p : Fin n → Fin 3, pieceSign c p * φ (pieceMap p z)

/-- **The folding formula**: for `φ` continuous, bounded and vanishing off `U`, and `f`
integrable on `Q`, `∫_{ℝⁿ} ext_c f · φ = ∫_Q f · fold_c φ`. -/
theorem integral_parExt_mul (c : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : IntegrableOn f (Q (Fin n))) {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {M : ℝ}
    (hφM : ∀ x, |φ x| ≤ M) (hφU : ∀ x, x ∉ bigCube n → φ x = 0) :
    Integrable (fun x => parExt c f x * φ x) ∧
      ∫ x, parExt c f x * φ x = ∫ z in Q (Fin n), f z * foldFun c φ z := by
  have hG : ∀ x, x ∉ bigCube n → parExt c f x * φ x = 0 := fun x hx => by
    rw [hφU x hx, mul_zero]
  have hpc : ∀ p : Fin n → Fin 3, IntegrableOn (fun z => f z * φ (pieceMap p z)) (Q (Fin n)) :=
    fun p => Integrable.mul_bdd hf (hφc.comp (continuous_pieceMap p)).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hφM _)
  have hp : ∀ p : Fin n → Fin 3, IntegrableOn
      (fun z => parExt c f (pieceMap p z) * φ (pieceMap p z)) (Q (Fin n)) := by
    intro p
    refine IntegrableOn.congr_fun ((hpc p).const_mul (pieceSign c p)) (fun z hz => ?_)
      measurableSet_Q
    simp only [parExt_pieceMap hz]; ring
  obtain ⟨hI, he⟩ := integral_eq_sum_pieceMap hG hp
  refine ⟨hI, he.trans ?_⟩
  simp only [foldFun, Finset.mul_sum]
  rw [integral_finsetSum _ fun p _ => IntegrableOn.congr_fun ((hpc p).const_mul (pieceSign c p))
    (fun z _ => by ring) measurableSet_Q]
  refine Finset.sum_congr rfl fun p _ => setIntegral_congr_fun measurableSet_Q fun z hz => ?_
  simp only [parExt_pieceMap hz]; ring

theorem abs_sub_le_abs_piece_sub {y z : ℝ} (hy : y ∈ Icc (0 : ℝ) (1 / 2))
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2)) (q : Fin 3) : |z - y| ≤ |piece q z - y| := by
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hz0, hz1⟩ := hz
  fin_cases q
  · simp only [Fin.zero_eta, piece_zero]
    rw [show -z - y = -(z + y) by ring, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ z + y by linarith)]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · simp
  · simp only [Fin.reduceFinMk, piece_two]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 - z - y by linarith)]
    exact abs_le.2 ⟨by linarith, by linarith⟩

theorem norm_sub_le_norm_pieceMap_sub {y z : Fin n → ℝ} (hy : ∀ j, y j ∈ Icc (0 : ℝ) (1 / 2))
    (hz : z ∈ Q (Fin n)) (p : Fin n → Fin 3) : ‖z - y‖ ≤ ‖pieceMap p z - y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  refine le_trans ?_ (norm_le_pi_norm (pieceMap p z - y) j)
  simp only [Pi.sub_apply, pieceMap_apply, Real.norm_eq_abs]
  exact abs_sub_le_abs_piece_sub (hy j) (mem_Q.1 hz j) (p j)

theorem closedBall_subset_bigCube {y : Fin n → ℝ} (hy : ∀ j, y j ∈ Icc (0 : ℝ) (1 / 2)) {r : ℝ}
    (hr : r < 1 / 2) : Metric.closedBall y r ⊆ bigCube n := by
  intro x hx
  rw [mem_bigCube]
  intro j
  have h := (dist_le_pi_dist x y j).trans (Metric.mem_closedBall.1 hx)
  rw [Real.dist_eq, abs_le] at h
  constructor <;> linarith [(hy j).1, (hy j).2, h.1, h.2]

theorem pieceMap_mem_bigCube {z : Fin n → ℝ} (hz : z ∈ Q (Fin n)) (p : Fin n → Fin 3) :
    pieceMap p z ∈ bigCube n :=
  mem_bigCube_of_pieceMap_mem_Q (p := p) (by rwa [pieceMap_pieceMap])

theorem card_pieces : (Finset.univ : Finset (Fin n → Fin 3)).card = 3 ^ n := by
  simp

theorem indicator_sq {s : Set (Fin n → ℝ)} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    s.indicator f x ^ 2 = s.indicator (fun x => f x ^ 2) x := by
  by_cases h : x ∈ s <;> simp [h]

/-- **Local `L²` bound of the parity extension**: on a ball `B̄(y, r)` centred in `cl Q`, `r < ½`,
`∫_B |ext_c f|² ≤ 3ⁿ ∫_B |f̄|²` (`f̄` the extension of `f` by zero). -/
theorem integral_sq_parExt_le {c : Fin n → ℝ} (hc : IsParity c) {f : (Fin n → ℝ) → ℝ}
    (hf : IntegrableOn (fun z => f z ^ 2) (Q (Fin n))) {y : Fin n → ℝ}
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) (1 / 2)) {r : ℝ} (hr : r < 1 / 2) :
    IntegrableOn (fun x => parExt c f x ^ 2) (Metric.closedBall y r) ∧
      ∫ x in Metric.closedBall y r, parExt c f x ^ 2 ≤
        3 ^ n * ∫ x in Metric.closedBall y r, (Q (Fin n)).indicator f x ^ 2 := by
  set B := Metric.closedBall y r
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  set G : (Fin n → ℝ) → ℝ := B.indicator fun x => parExt c f x ^ 2
  have hG : ∀ x, x ∉ bigCube n → G x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun h => hx (closedBall_subset_bigCube hy hr h)) _
  have hGp : ∀ p : Fin n → Fin 3, ∀ z ∈ Q (Fin n),
      G (pieceMap p z) = (pieceMap p ⁻¹' B).indicator (fun z => f z ^ 2) z := by
    intro p z hz
    simp only [G]
    by_cases h : pieceMap p z ∈ B
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show z ∈ pieceMap p ⁻¹' B from h),
        parExt_pieceMap hz, mul_pow, pieceSign_sq hc, one_mul]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show z ∉ pieceMap p ⁻¹' B from h)]
  have hpB : ∀ p : Fin n → Fin 3, MeasurableSet (pieceMap p ⁻¹' B) := fun p =>
    hB.preimage (continuous_pieceMap p).measurable
  have hp : ∀ p : Fin n → Fin 3, IntegrableOn (fun z => G (pieceMap p z)) (Q (Fin n)) :=
    fun p => IntegrableOn.congr_fun (hf.indicator (hpB p)) (fun z hz => (hGp p z hz).symm)
      measurableSet_Q
  obtain ⟨hI, he⟩ := integral_eq_sum_pieceMap hG hp
  refine ⟨(integrable_indicator_iff hB).1 hI, ?_⟩
  rw [← integral_indicator hB, he]
  have hle : ∀ p : Fin n → Fin 3, ∫ z in Q (Fin n), G (pieceMap p z) ≤
      ∫ z in Q (Fin n), B.indicator (fun z => f z ^ 2) z := by
    intro p
    refine setIntegral_mono_on (hp p) (hf.indicator hB) measurableSet_Q fun z hz => ?_
    rw [hGp p z hz]
    by_cases h : pieceMap p z ∈ B
    · have hzB : z ∈ B := by
        have := norm_sub_le_norm_pieceMap_sub hy hz p
        rw [Metric.mem_closedBall, dist_eq_norm] at h ⊢
        linarith
      rw [Set.indicator_of_mem (show z ∈ pieceMap p ⁻¹' B from h), Set.indicator_of_mem hzB]
    · rw [Set.indicator_of_notMem (show z ∉ pieceMap p ⁻¹' B from h)]
      exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  refine (Finset.sum_le_sum fun p _ => hle p).trans (le_of_eq ?_)
  rw [Finset.sum_const, card_pieces, nsmul_eq_mul, setIntegral_indicator hB]
  simp_rw [indicator_sq]
  rw [setIntegral_indicator measurableSet_Q, Set.inter_comm]
  push_cast; ring

/-- **The parity extension on `U`**: `∫_U |ext_c f|² = 3ⁿ ∫_Q |f|²`. -/
theorem integral_sq_parExt_bigCube {c : Fin n → ℝ} (hc : IsParity c) {f : (Fin n → ℝ) → ℝ}
    (hf : IntegrableOn (fun z => f z ^ 2) (Q (Fin n))) :
    IntegrableOn (fun x => parExt c f x ^ 2) (bigCube n) ∧
      ∫ x in bigCube n, parExt c f x ^ 2 = 3 ^ n * ∫ z in Q (Fin n), f z ^ 2 := by
  have hU : MeasurableSet (bigCube n) :=
    (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).measurableSet
  set G : (Fin n → ℝ) → ℝ := (bigCube n).indicator fun x => parExt c f x ^ 2
  have hG : ∀ x, x ∉ bigCube n → G x = 0 := fun x hx => Set.indicator_of_notMem hx _
  have hGp : ∀ p : Fin n → Fin 3, ∀ z ∈ Q (Fin n), G (pieceMap p z) = f z ^ 2 := by
    intro p z hz
    simp only [G]
    rw [Set.indicator_of_mem (pieceMap_mem_bigCube hz p), parExt_pieceMap hz, mul_pow,
      pieceSign_sq hc, one_mul]
  have hp : ∀ p : Fin n → Fin 3, IntegrableOn (fun z => G (pieceMap p z)) (Q (Fin n)) :=
    fun p => IntegrableOn.congr_fun hf (fun z hz => (hGp p z hz).symm) measurableSet_Q
  obtain ⟨hI, he⟩ := integral_eq_sum_pieceMap hG hp
  refine ⟨(integrable_indicator_iff hU).1 hI, ?_⟩
  rw [← integral_indicator hU, he,
    Finset.sum_congr rfl fun p _ => setIntegral_congr_fun measurableSet_Q fun z hz => hGp p z hz,
    Finset.sum_const, card_pieces, nsmul_eq_mul]
  push_cast; ring

/-- The parity extension is integrable on `U` (from `f ∈ L¹(Q)`). -/
theorem integrableOn_parExt_bigCube (c : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : IntegrableOn f (Q (Fin n))) : IntegrableOn (parExt c f) (bigCube n) := by
  have hU : MeasurableSet (bigCube n) :=
    (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).measurableSet
  set G : (Fin n → ℝ) → ℝ := (bigCube n).indicator (parExt c f)
  have hG : ∀ x, x ∉ bigCube n → G x = 0 := fun x hx => Set.indicator_of_notMem hx _
  have hp : ∀ p : Fin n → Fin 3, IntegrableOn (fun z => G (pieceMap p z)) (Q (Fin n)) :=
    fun p => IntegrableOn.congr_fun (hf.const_mul (pieceSign c p)) (fun z hz => by
      simp only [G]
      rw [Set.indicator_of_mem (pieceMap_mem_bigCube hz p), parExt_pieceMap hz]) measurableSet_Q
  exact (integrable_indicator_iff hU).1 (integral_eq_sum_pieceMap hG hp).1

theorem parExt_sub_intCast (c : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (m : Fin n → ℤ) : parExt c f (x - fun j => (m j : ℝ)) = parExt c f x := by
  have h := parExt_add_intCast c f (x - fun j => (m j : ℝ)) m
  rwa [sub_add_cancel, eq_comm] at h

theorem sub_floor_mem_bigCube (x : Fin n → ℝ) : (x - fun j => ((⌊x j⌋ : ℤ) : ℝ)) ∈ bigCube n := by
  rw [mem_bigCube]
  intro j
  simp only [Pi.sub_apply]
  have h1 := Int.floor_le (x j)
  have h2 := Int.lt_floor_add_one (x j)
  constructor <;> linarith

/-- **The parity extension is locally integrable** (periodicity and integrability on `U`). -/
theorem locallyIntegrable_parExt (c : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : IntegrableOn f (Q (Fin n))) : LocallyIntegrable (parExt c f) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set M : ℤ := ⌈R⌉ + 1
  set S : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-M) M
  have hcover : K ⊆ ⋃ m ∈ S, (fun x => x - fun j => (m j : ℝ)) ⁻¹' bigCube n := by
    intro x hx
    refine Set.mem_iUnion₂.2 ⟨fun j => ⌊x j⌋, ?_, sub_floor_mem_bigCube x⟩
    rw [Fintype.mem_piFinset]
    intro j
    have hxj : |x j| ≤ R := by
      have := (norm_le_pi_norm x j).trans (mem_closedBall_zero_iff.1 (hR hx))
      rwa [Real.norm_eq_abs] at this
    rw [abs_le] at hxj
    have h1 := Int.floor_le (x j)
    have h2 := Int.lt_floor_add_one (x j)
    have h3 := Int.le_ceil R
    rw [Finset.mem_Icc]
    constructor
    · have : (-(M : ℝ)) ≤ ⌊x j⌋ := by push_cast [M]; linarith
      exact_mod_cast this
    · have : ((⌊x j⌋ : ℤ) : ℝ) ≤ M := by push_cast [M]; linarith
      exact_mod_cast this
  refine (integrableOn_finset_iUnion.2 fun m _ => ?_).mono_set hcover
  have hτ := measurePreserving_sub_right (volume : Measure (Fin n → ℝ)) (fun j => (m j : ℝ))
  have hemb : MeasurableEmbedding fun x : Fin n → ℝ => x - fun j => (m j : ℝ) :=
    (Homeomorph.subRight _).measurableEmbedding
  have h := (hτ.integrableOn_comp_preimage hemb (f := parExt c f) (s := bigCube n)).2
    (integrableOn_parExt_bigCube c hf)
  have e : (parExt c f ∘ fun x : Fin n → ℝ => x - fun j => (m j : ℝ)) = parExt c f :=
    funext fun x => parExt_sub_intCast c f x m
  rwa [e] at h

/-- **The parity extension respects almost-everywhere equality on `Q`.** -/
theorem parExt_ae_eq (c : Fin n → ℝ) {f g : (Fin n → ℝ) → ℝ}
    (h : f =ᵐ[volume.restrict (Q (Fin n))] g) : parExt c f =ᵐ[volume] parExt c g := by
  have hQ : ∀ᵐ z ∂volume, z ∈ Q (Fin n) → f z = g z := (ae_restrict_iff' measurableSet_Q).1 h
  have hU : ∀ᵐ x ∂volume, x ∈ bigCube n → parExt c f x = parExt c g x := by
    have hp : ∀ p : Fin n → Fin 3, ∀ᵐ x ∂volume,
        pieceMap p x ∈ Q (Fin n) → f (pieceMap p x) = g (pieceMap p x) := fun p =>
      (measurePreserving_pieceMap p).quasiMeasurePreserving.ae hQ
    filter_upwards [ae_all_iff.2 hp, ae_coord_ne] with x hx hx0 hxU
    obtain ⟨p, hpx⟩ := exists_pieceMap_mem_Q hxU hx0
    have e : ∀ f' : (Fin n → ℝ) → ℝ, parExt c f' x = pieceSign c p * f' (pieceMap p x) := by
      intro f'
      have := parExt_pieceMap hpx c f' p
      rwa [pieceMap_pieceMap] at this
    rw [e, e, hx p hpx]
  have hm : ∀ m : Fin n → ℤ, ∀ᵐ x ∂volume,
      (x - fun j => (m j : ℝ)) ∈ bigCube n → parExt c f x = parExt c g x := by
    intro m
    have := (measurePreserving_sub_right (volume : Measure (Fin n → ℝ))
      (fun j => (m j : ℝ))).quasiMeasurePreserving.ae hU
    filter_upwards [this] with x hx hxU
    have h' := hx hxU
    rwa [parExt_sub_intCast, parExt_sub_intCast] at h'
  filter_upwards [ae_all_iff.2 hm] with x hx
  exact hx (fun j => ⌊x j⌋) (sub_floor_mem_bigCube x)

/-! ### Reflections about the faces -/

/-- The index of the reflection `x_j ↦ -x_j` among the copies. -/
def reflIdx (j : Fin n) : Fin n → Fin 3 := fun i => if i = j then 0 else 1

/-- The reflection `x ↦ (…, -x_j, …)` about the hyperplane `{x_j = 0}`. -/
def coordRefl (j : Fin n) : (Fin n → ℝ) → (Fin n → ℝ) := pieceMap (reflIdx j)

theorem coordRefl_apply (j : Fin n) (x : Fin n → ℝ) (i : Fin n) :
    coordRefl j x i = if i = j then -x i else x i := by
  simp only [coordRefl, pieceMap_apply, reflIdx]
  split_ifs <;> simp

theorem coordRefl_sub (j : Fin n) (x y : Fin n → ℝ) :
    coordRefl j x - coordRefl j y = coordRefl j (x - y) := by
  funext i; simp only [Pi.sub_apply, coordRefl_apply]; split_ifs <;> ring

theorem coordRefl_coordRefl (j : Fin n) (x : Fin n → ℝ) : coordRefl j (coordRefl j x) = x :=
  pieceMap_pieceMap _ x

theorem coordRefl_of_eq_zero {j : Fin n} {x : Fin n → ℝ} (h : x j = 0) : coordRefl j x = x := by
  funext i; rw [coordRefl_apply]; split_ifs with hi
  · subst hi; rw [h, neg_zero]
  · rfl

theorem parSgn_neg {c : ℝ} (hc : c = 1 ∨ c = -1) {x : ℝ} (h0 : Int.fract x ≠ 0)
    (h1 : Int.fract x ≠ 1 / 2) : parSgn c (-x) = c * parSgn c x := by
  have hf := Int.fract_neg h0
  have hlt := Int.fract_lt_one x
  unfold parSgn
  rw [hf]
  rcases lt_or_gt_of_ne h1 with h | h
  · have ha : ¬ (1 - Int.fract x ≤ 1 / 2) := by linarith
    have hb : Int.fract x ≤ 1 / 2 := h.le
    simp only [ha, hb, ↓reduceIte, mul_one]
  · have ha : 1 - Int.fract x ≤ 1 / 2 := by linarith
    have hb : ¬ Int.fract x ≤ 1 / 2 := by linarith
    simp only [ha, hb, ↓reduceIte]
    rcases hc with hc | hc <;> rw [hc] <;> norm_num

/-- Almost every point has `fract (x j) ∉ {0, ½}`. -/
theorem ae_fract_ne (j : Fin n) :
    ∀ᵐ x : Fin n → ℝ, Int.fract (x j) ≠ 0 ∧ Int.fract (x j) ≠ 1 / 2 := by
  have h : ∀ᵐ x : Fin n → ℝ, ∀ m : ℤ, x j ≠ m ∧ x j ≠ m + 1 / 2 :=
    ae_all_iff.2 fun m => (Measure.ae_eval_ne _ j _).and (Measure.ae_eval_ne _ j _)
  filter_upwards [h] with x hx
  constructor
  · intro h0
    obtain ⟨m, hm⟩ := Int.fract_eq_zero_iff.1 h0
    exact (hx m).1 hm.symm
  · intro h1
    have := Int.floor_add_fract (x j)
    rw [h1] at this
    exact (hx ⌊x j⌋).2 this.symm

/-- **Parity of the extension about `{x_j = 0}`**: `ext_c f ∘ R_j = c_j ext_c f` a.e. -/
theorem parExt_coordRefl_ae {c : Fin n → ℝ} (hc : IsParity c) (f : (Fin n → ℝ) → ℝ)
    (j : Fin n) : ∀ᵐ x : Fin n → ℝ, parExt c f (coordRefl j x) = c j * parExt c f x := by
  classical
  filter_upwards [ae_fract_ne j] with x hx
  have h1 : foldPt (coordRefl j x) = foldPt x := funext fun i => by
    simp only [foldPt, coordRefl_apply]
    split_ifs
    · exact triW_neg _
    · rfl
  have h2 : extSgn c (coordRefl j x) = c j * extSgn c x := by
    unfold extSgn
    have e1 : coordRefl j x j = -x j := by simp [coordRefl_apply]
    have e2 : ∀ i, i ≠ j → coordRefl j x i = x i := fun i hi => by simp [coordRefl_apply, hi]
    rw [Fintype.prod_eq_mul_prod_compl j,
      Fintype.prod_eq_mul_prod_compl j (fun i => parSgn (c i) (x i)), e1,
      parSgn_neg (hc j) hx.1 hx.2, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [e2 i (by simpa using hi)]
  rw [parExt, parExt, h1, h2, mul_assoc]

/-! ### Reflection-invariant mollifiers -/

/-- **A reflection-invariant mollifier**: a smooth, nonnegative, compactly supported probability
density `ρ` on `ℝⁿ`, supported in the ball `‖x‖_∞ < r` with `r < ½`, and invariant under every
coordinate reflection `x_j ↦ -x_j`. -/
structure ReflKernel (n : ℕ) where
  /-- the density -/
  toFun : (Fin n → ℝ) → ℝ
  isTest : IsTest (univ : Set (Fin n → ℝ)) toFun
  nonneg : ∀ x, 0 ≤ toFun x
  integral_eq_one : ∫ x, toFun x = 1
  /-- the support radius -/
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt : radius < 1 / 2
  eq_zero_of_le : ∀ x, radius ≤ ‖x‖ → toFun x = 0
  refl : ∀ j x, toFun (coordRefl j x) = toFun x

namespace ReflKernel

instance : CoeFun (ReflKernel n) fun _ => (Fin n → ℝ) → ℝ := ⟨ReflKernel.toFun⟩

variable (ρ : ReflKernel n)

theorem continuous : Continuous ρ := ρ.isTest.contDiff.continuous

theorem integrable : Integrable ρ :=
  ρ.continuous.integrable_of_hasCompactSupport ρ.isTest.hasCompactSupport

theorem integrable_comp_sub (y : Fin n → ℝ) : Integrable fun t => ρ (y - t) :=
  (ρ.isTest.comp_sub y).contDiff.continuous.integrable_of_hasCompactSupport
    (ρ.isTest.comp_sub y).hasCompactSupport

theorem integral_comp_sub (y : Fin n → ℝ) : ∫ t, ρ (y - t) = 1 := by
  rw [integral_sub_left_eq_self (fun t => ρ t) volume y]; exact ρ.integral_eq_one

theorem exists_bound : ∃ M, 0 ≤ M ∧ ∀ x, ρ x ≤ M := by
  obtain ⟨M, hM⟩ := ρ.isTest.hasCompactSupport.exists_bound_of_continuous ρ.continuous
  exact ⟨max M 0, le_max_right _ _, fun x => (le_abs_self _).trans
    ((Real.norm_eq_abs _ ▸ hM x).trans (le_max_left _ _))⟩

end ReflKernel

/-! ### The smoothed parity extension -/

/-- **The smoothed parity extension** `ρ ⋆ ext_c f`, a smooth function on `ℝⁿ`. -/
def smoothFun (ρ : ReflKernel n) (c : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  parExt c f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ.toFun

theorem smoothFun_apply (ρ : ReflKernel n) (c : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ)
    (y : Fin n → ℝ) : smoothFun ρ c f y = ∫ t, parExt c f t * ρ (y - t) :=
  convolution_apply_mul _ _ y

theorem contDiff_smoothFun (ρ : ReflKernel n) (c : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : IntegrableOn f (Q (Fin n))) : ContDiff ℝ ∞ (smoothFun ρ c f) :=
  ρ.isTest.hasCompactSupport.contDiff_convolution_right _ (locallyIntegrable_parExt c hf)
    ρ.isTest.contDiff

theorem fderiv_smoothFun (ρ : ReflKernel n) (c : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : IntegrableOn f (Q (Fin n))) (y v : Fin n → ℝ) :
    fderiv ℝ (smoothFun ρ c f) y v = ∫ t, parExt c f t * fderiv ℝ ρ.toFun (y - t) v := by
  rw [smoothFun, fderiv_convolution_apply ρ.isTest (locallyIntegrable_parExt c hf) y v,
    convolution_apply_mul]

/-- Convolution with a periodic function is periodic. -/
theorem convolution_add_intCast {g K : (Fin n → ℝ) → ℝ}
    (hg : ∀ x (m : Fin n → ℤ), g (x + fun j => (m j : ℝ)) = g x) (y : Fin n → ℝ)
    (m : Fin n → ℤ) :
    (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K) (y + fun j => (m j : ℝ)) =
      (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K) y := by
  rw [convolution_apply_mul, convolution_apply_mul]
  rw [← integral_add_right_eq_self (fun t => g t * K (y + (fun j => (m j : ℝ)) - t))
    (fun j => (m j : ℝ))]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [hg]
  congr 2; abel

section SmoothFun

variable (ρ : ReflKernel n) (c : Fin n → ℝ)

theorem integrable_parExt_mul_comp_sub {f : (Fin n → ℝ) → ℝ} (hf : IntegrableOn f (Q (Fin n)))
    (y : Fin n → ℝ) : Integrable fun t => parExt c f t * ρ (y - t) :=
  integrable_mul_isTest (locallyIntegrable_parExt c hf) (ρ.isTest.comp_sub y)

theorem smoothFun_add {f g : (Fin n → ℝ) → ℝ} (hf : IntegrableOn f (Q (Fin n)))
    (hg : IntegrableOn g (Q (Fin n))) :
    smoothFun ρ c (f + g) = smoothFun ρ c f + smoothFun ρ c g := by
  funext y
  simp only [smoothFun_apply, Pi.add_apply, parExt_add, add_mul]
  exact integral_add (integrable_parExt_mul_comp_sub ρ c hf y)
    (integrable_parExt_mul_comp_sub ρ c hg y)

theorem smoothFun_smul (a : ℝ) (f : (Fin n → ℝ) → ℝ) :
    smoothFun ρ c (a • f) = a • smoothFun ρ c f := by
  funext y
  simp only [smoothFun_apply, parExt_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem smoothFun_congr_ae {f g : (Fin n → ℝ) → ℝ} (h : f =ᵐ[volume.restrict (Q (Fin n))] g) :
    smoothFun ρ c f = smoothFun ρ c g := by
  funext y
  simp only [smoothFun_apply]
  refine integral_congr_ae ?_
  filter_upwards [parExt_ae_eq c h] with t ht
  rw [ht]

theorem smoothFun_add_intCast (f : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) (m : Fin n → ℤ) :
    smoothFun ρ c f (y + fun j => (m j : ℝ)) = smoothFun ρ c f y :=
  convolution_add_intCast (fun x m => parExt_add_intCast c f x m) y m

/-- **The smoothed extension has parity `c_j` about `{y_j = 0}`.** -/
theorem smoothFun_coordRefl {c : Fin n → ℝ} (hc : IsParity c) (f : (Fin n → ℝ) → ℝ) (j : Fin n)
    (y : Fin n → ℝ) : smoothFun ρ c f (coordRefl j y) = c j * smoothFun ρ c f y := by
  rw [smoothFun_apply, smoothFun_apply]
  have hmp := measurePreserving_pieceMap (n := n) (reflIdx j)
  rw [← hmp.integral_comp (measurableEmbedding_pieceMap _)
    (fun t => parExt c f t * ρ (coordRefl j y - t)), ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [parExt_coordRefl_ae hc f j] with t ht
  change parExt c f (coordRefl j t) * ρ (coordRefl j y - coordRefl j t) = _
  rw [ht, coordRefl_sub]
  rw [show ρ (coordRefl j (y - t)) = ρ (y - t) from ρ.refl j (y - t)]; ring

theorem update_one_sub_eq (j : Fin n) (y : Fin n → ℝ) :
    Function.update y j (1 - y j) =
      coordRefl j y + fun i => (((Pi.single j (1 : ℤ) : Fin n → ℤ) i : ℤ) : ℝ) := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [coordRefl_apply]; ring
  · simp [coordRefl_apply, hi]

/-- **The smoothed extension has parity `c_j` about `{y_j = ½}`.** -/
theorem smoothFun_update_one_sub {c : Fin n → ℝ} (hc : IsParity c) (f : (Fin n → ℝ) → ℝ)
    (j : Fin n) (y : Fin n → ℝ) :
    smoothFun ρ c f (Function.update y j (1 - y j)) = c j * smoothFun ρ c f y := by
  rw [update_one_sub_eq, smoothFun_add_intCast, smoothFun_coordRefl ρ hc]

/-- **Odd directions: the smoothed extension vanishes on the faces** `{y_j ∈ {0, ½}}` when
`c_j = -1`. -/
theorem smoothFun_eq_zero {c : Fin n → ℝ} (hc : IsParity c) (f : (Fin n → ℝ) → ℝ) {j : Fin n}
    (hcj : c j = -1) {y : Fin n → ℝ} (hy : y j = 0 ∨ y j = 1 / 2) : smoothFun ρ c f y = 0 := by
  rcases hy with hy | hy
  · have h := smoothFun_coordRefl ρ hc f j y
    rw [coordRefl_of_eq_zero hy, hcj] at h
    linarith
  · have h := smoothFun_update_one_sub ρ hc f j y
    have e : Function.update y j (1 - y j) = y := by
      rw [hy, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← hy, Function.update_eq_self]
    rw [e, hcj] at h
    linarith

theorem eq_zero_of_notMem_bigCube {y : Fin n → ℝ} (hy : ∀ j, y j ∈ Icc (0 : ℝ) (1 / 2))
    {t : Fin n → ℝ} (ht : t ∉ bigCube n) : ρ (y - t) = 0 := by
  refine ρ.eq_zero_of_le _ ?_
  rw [mem_bigCube] at ht
  push Not at ht
  obtain ⟨j, hj⟩ := ht
  have h : (1 / 2 : ℝ) ≤ |y j - t j| := by
    rw [Set.mem_Ioo] at hj
    by_cases h1 : -(1 / 2) < t j
    · have h2 : 1 ≤ t j := by
        by_contra h; exact hj ⟨h1, by linarith⟩
      rw [abs_of_nonpos (by linarith [(hy j).2])]; linarith [(hy j).2]
    · rw [abs_of_nonneg (by linarith [(hy j).1])]; linarith [(hy j).1]
  have h2 : |y j - t j| ≤ ‖y - t‖ := by
    have := norm_le_pi_norm (y - t) j; rwa [Pi.sub_apply, Real.norm_eq_abs] at this
  linarith [ρ.radius_lt]

/-- `ρ (y - ·)` vanishes off the closed ball `B̄(y, r)`. -/
theorem eq_zero_of_notMem_closedBall {y t : Fin n → ℝ} (ht : t ∉ Metric.closedBall y ρ.radius) :
    ρ (y - t) = 0 := by
  refine ρ.eq_zero_of_le _ ?_
  rw [Metric.mem_closedBall, dist_comm, dist_eq_norm] at ht
  exact (not_le.1 ht).le

/-- **Jensen's inequality for the mollifier**: `(ρ ⋆ g)(y)² ≤ ∫ g² ρ(y - ·)` at the points of
`cl Q`. -/
theorem sq_smoothFun_le {c : Fin n → ℝ} (hc : IsParity c) {f : (Fin n → ℝ) → ℝ}
    (hf : IntegrableOn f (Q (Fin n))) (hf2 : IntegrableOn (fun z => f z ^ 2) (Q (Fin n)))
    {y : Fin n → ℝ} (hy : ∀ j, y j ∈ Icc (0 : ℝ) (1 / 2)) :
    Integrable (fun t => parExt c f t ^ 2 * ρ (y - t)) ∧
      smoothFun ρ c f y ^ 2 ≤ ∫ t, parExt c f t ^ 2 * ρ (y - t) := by
  set g := parExt c f
  set B := Metric.closedBall y ρ.radius
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  obtain ⟨M, hM0, hM⟩ := ρ.exists_bound
  have hgB := (integral_sq_parExt_le hc hf2 hy ρ.radius_lt).1
  have hi2 : Integrable fun t => parExt c f t ^ 2 * ρ (y - t) := by
    have h1 : Integrable fun t => B.indicator (fun t => g t ^ 2) t * ρ (y - t) :=
      Integrable.mul_bdd (hgB.integrable_indicator hB)
        (ρ.isTest.comp_sub y).contDiff.continuous.aestronglyMeasurable
        (ae_of_all _ fun t => by
          rw [Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg _)]; exact hM _)
    refine h1.congr (ae_of_all _ fun t => ?_)
    by_cases ht : t ∈ B
    · simp [Set.indicator_of_mem ht, g]
    · simp [Set.indicator_of_notMem ht, eq_zero_of_notMem_closedBall ρ ht]
  refine ⟨hi2, ?_⟩
  set a := smoothFun ρ c f y
  have hi1 := integrable_parExt_mul_comp_sub ρ c hf y
  have hi0 := ρ.integrable_comp_sub y
  have hvar : 0 ≤ ∫ t, (g t - a) ^ 2 * ρ (y - t) :=
    integral_nonneg fun t => mul_nonneg (sq_nonneg _) (ρ.nonneg _)
  have hA : Integrable fun t => g t ^ 2 * ρ (y - t) - 2 * a * (g t * ρ (y - t)) :=
    hi2.sub (hi1.const_mul _)
  have e1 : ∫ t, (g t ^ 2 * ρ (y - t) - 2 * a * (g t * ρ (y - t)) + a ^ 2 * ρ (y - t)) =
      (∫ t, (g t ^ 2 * ρ (y - t) - 2 * a * (g t * ρ (y - t)))) + ∫ t, a ^ 2 * ρ (y - t) :=
    integral_add hA (hi0.const_mul _)
  have e2 : ∫ t, (g t ^ 2 * ρ (y - t) - 2 * a * (g t * ρ (y - t))) =
      (∫ t, g t ^ 2 * ρ (y - t)) - ∫ t, 2 * a * (g t * ρ (y - t)) :=
    integral_sub hi2 (hi1.const_mul _)
  have ha : ∫ t, g t * ρ (y - t) = a := (smoothFun_apply ρ c f y).symm
  have e : ∫ t, (g t - a) ^ 2 * ρ (y - t) =
      ∫ t, (g t ^ 2 * ρ (y - t) - 2 * a * (g t * ρ (y - t)) + a ^ 2 * ρ (y - t)) := by
    congr 1; funext t; ring
  rw [e, e1, e2, integral_const_mul, integral_const_mul, ha, ρ.integral_comp_sub] at hvar
  change a ^ 2 ≤ ∫ t, g t ^ 2 * ρ (y - t)
  nlinarith

/-- **The pointwise bound of the smoothed extension by the local mass**: for `y ∈ cl Q` and
`ρ ≤ M`, `(ρ ⋆ ext_c f)(y)² ≤ 3ⁿ M ∫_{B̄(y, r)} |f̄|²` (`f̄` the extension by zero). -/
theorem sq_smoothFun_le_ball {c : Fin n → ℝ} (hc : IsParity c) {f : (Fin n → ℝ) → ℝ}
    (hf : IntegrableOn f (Q (Fin n))) (hf2 : IntegrableOn (fun z => f z ^ 2) (Q (Fin n)))
    {y : Fin n → ℝ} (hy : ∀ j, y j ∈ Icc (0 : ℝ) (1 / 2)) {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    smoothFun ρ c f y ^ 2 ≤
      3 ^ n * M * ∫ x in Metric.closedBall y ρ.radius, (Q (Fin n)).indicator f x ^ 2 := by
  set B := Metric.closedBall y ρ.radius
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  obtain ⟨hgB, hgBle⟩ := integral_sq_parExt_le hc hf2 hy ρ.radius_lt
  obtain ⟨hi2, h1⟩ := sq_smoothFun_le ρ hc hf hf2 hy
  have hM0 : 0 ≤ M := (ρ.nonneg 0).trans (hM 0)
  refine h1.trans ?_
  have h2 : ∫ t, parExt c f t ^ 2 * ρ (y - t) = ∫ t in B, parExt c f t ^ 2 * ρ (y - t) := by
    rw [← integral_indicator hB]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    by_cases ht : t ∈ B
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      change parExt c f t ^ 2 * ρ (y - t) = 0
      rw [eq_zero_of_notMem_closedBall ρ ht, mul_zero]
  rw [h2]
  calc ∫ t in B, parExt c f t ^ 2 * ρ (y - t) ≤ ∫ t in B, parExt c f t ^ 2 * M :=
        setIntegral_mono_on hi2.integrableOn (hgB.mul_const M) hB fun t _ =>
          mul_le_mul_of_nonneg_left (hM _) (sq_nonneg _)
    _ = M * ∫ t in B, parExt c f t ^ 2 := by rw [integral_mul_const]; ring
    _ ≤ M * (3 ^ n * ∫ x in B, (Q (Fin n)).indicator f x ^ 2) :=
        mul_le_mul_of_nonneg_left hgBle hM0
    _ = _ := by ring

/-- **The `L²(Q)` bound of the smoothed extension**: `‖ρ ⋆ ext_c f‖²_{L²(Q)} ≤ 3ⁿ ‖f‖²_{L²(Q)}`. -/
theorem integral_sq_smoothFun_le {c : Fin n → ℝ} (hc : IsParity c) {f : (Fin n → ℝ) → ℝ}
    (hf : IntegrableOn f (Q (Fin n))) (hf2 : IntegrableOn (fun z => f z ^ 2) (Q (Fin n))) :
    ∫ y in Q (Fin n), smoothFun ρ c f y ^ 2 ≤ 3 ^ n * ∫ z in Q (Fin n), f z ^ 2 := by
  have hU : MeasurableSet (bigCube n) :=
    (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).measurableSet
  obtain ⟨hgU, hgUe⟩ := integral_sq_parExt_bigCube hc hf2
  set G : (Fin n → ℝ) → ℝ := (bigCube n).indicator fun t => parExt c f t ^ 2
  have hG : Integrable G := hgU.integrable_indicator hU
  have hGρ : Integrable (G ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ.toFun) :=
    hG.integrable_convolution _ ρ.integrable
  have hGρ0 : ∀ y, 0 ≤ (G ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ.toFun) y := fun y => by
    rw [convolution_apply_mul]
    exact integral_nonneg fun t => mul_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
      (ρ.nonneg _)
  have hQc : IsCompact (closure (Q (Fin n))) := (isBounded_openCube _ _).isCompact_closure
  have hψ : IntegrableOn (fun y => smoothFun ρ c f y ^ 2) (Q (Fin n)) :=
    (((contDiff_smoothFun ρ c hf).continuous.pow 2).continuousOn.integrableOn_compact
      hQc).mono_set subset_closure
  have hpt : ∀ y ∈ Q (Fin n), smoothFun ρ c f y ^ 2 ≤
      (G ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ.toFun) y := by
    intro y hy
    have hy' : ∀ j, y j ∈ Icc (0 : ℝ) (1 / 2) := fun j => Ioo_subset_Icc_self (mem_Q.1 hy j)
    refine (sq_smoothFun_le ρ hc hf hf2 hy').2.trans (le_of_eq ?_)
    rw [convolution_apply_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    by_cases ht : t ∈ bigCube n
    · simp [G, Set.indicator_of_mem ht]
    · simp [G, Set.indicator_of_notMem ht, eq_zero_of_notMem_bigCube ρ hy' ht]
  calc ∫ y in Q (Fin n), smoothFun ρ c f y ^ 2
      ≤ ∫ y in Q (Fin n), (G ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ.toFun) y :=
        setIntegral_mono_on hψ hGρ.integrableOn measurableSet_Q hpt
    _ ≤ ∫ y, (G ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ.toFun) y :=
        setIntegral_le_integral hGρ (ae_of_all _ hGρ0)
    _ = ∫ t, G t := by
        rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hG ρ.integrable, ρ.integral_eq_one]
        simp
    _ = 3 ^ n * ∫ z in Q (Fin n), f z ^ 2 := by rw [integral_indicator hU, hgUe]

end SmoothFun

/-! ### The fold of a test function -/

/-- The linear part of `pieceMap p`. -/
def diagL (p : Fin n → Fin 3) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => pieceSig (p i) • ContinuousLinearMap.proj i

theorem diagL_single (p : Fin n → Fin 3) (j : Fin n) :
    diagL p (Pi.single j 1) = pieceSig (p j) • (Pi.single j 1 : Fin n → ℝ) := by
  funext i
  by_cases h : i = j
  · subst h; simp [diagL]
  · simp [diagL, h]

theorem hasFDerivAt_pieceMap (p : Fin n → Fin 3) (z : Fin n → ℝ) :
    HasFDerivAt (pieceMap p) (diagL p) z := by
  refine hasFDerivAt_pi'.2 fun i => ?_
  have hc : (ContinuousLinearMap.proj i).comp (diagL p) =
      pieceSig (p i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i := by
    ext v; simp [diagL]
  rw [hc]
  have e : (fun z : Fin n → ℝ => pieceMap p z i) = fun z => pieceOff (p i) + pieceSig (p i) * z i :=
    funext fun z => piece_eq _ _
  rw [e]
  exact ((hasFDerivAt_apply i z).const_mul (pieceSig (p i))).const_add _

theorem contDiff_pieceMap (p : Fin n → Fin 3) : ContDiff ℝ ∞ (pieceMap p) := by
  refine contDiff_pi.2 fun i => ?_
  have e : (fun z : Fin n → ℝ => pieceMap p z i) = fun z => pieceOff (p i) + pieceSig (p i) * z i :=
    funext fun z => piece_eq _ _
  rw [e]
  exact contDiff_const.add (contDiff_const.mul (by fun_prop))

theorem contDiff_foldFun (c : Fin n → ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (foldFun c φ) :=
  ContDiff.sum fun p _ => contDiff_const.mul (hφ.comp (contDiff_pieceMap p))

theorem pieceSign_update_neg (c : Fin n → ℝ) (p : Fin n → Fin 3) (j : Fin n) :
    pieceSign (Function.update c j (-c j)) p = pieceSig (p j) * pieceSign c p := by
  classical
  unfold pieceSign
  rw [Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j
    (fun i => pieceSgn (c i) (p i)), Function.update_self, pieceSgn_neg, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (by simpa using hi)]

/-- **The partial derivatives of a fold**: `∂ⱼ fold_c φ = fold_{c'} ∂ⱼ φ`, with the parity of
`x_j` reversed in `c'`. -/
theorem fderiv_foldFun (c : Fin n → ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : Differentiable ℝ φ)
    (z : Fin n → ℝ) (j : Fin n) :
    fderiv ℝ (foldFun c φ) z (Pi.single j 1) =
      foldFun (Function.update c j (-c j)) (fun x => fderiv ℝ φ x (Pi.single j 1)) z := by
  have hd : ∀ p : Fin n → Fin 3, HasFDerivAt (fun z => pieceSign c p * φ (pieceMap p z))
      (pieceSign c p • (fderiv ℝ φ (pieceMap p z)).comp (diagL p)) z := fun p =>
    ((hφ _).hasFDerivAt.comp z (hasFDerivAt_pieceMap p z)).const_mul _
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) fun p _ => hd p
  rw [show foldFun c φ = fun z => ∑ p, pieceSign c p * φ (pieceMap p z) from rfl, hs.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, diagL_single, map_smul,
    smul_eq_mul, foldFun]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [pieceSign_update_neg]; ring

/-- The involution argument for the vanishing of folds on the faces. -/
theorem foldFun_eq_zero_aux {c : Fin n → ℝ} {φ : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ} {j : Fin n}
    (σ : Fin 3 → Fin 3) (hσ : ∀ q, σ (σ q) = q)
    (hfix : ∀ q, σ q = q → ∀ x : Fin n → ℝ, x j = piece q (z j) → φ x = 0)
    (hpt : ∀ q, σ q ≠ q → piece (σ q) (z j) = piece q (z j))
    (hsgn : ∀ q, σ q ≠ q → pieceSgn (c j) (σ q) = -pieceSgn (c j) q) : foldFun c φ z = 0 := by
  classical
  set P : (Fin n → Fin 3) → (Fin n → Fin 3) := fun p => Function.update p j (σ (p j))
  have hPj : ∀ p, P p j = σ (p j) := fun p => Function.update_self _ _ _
  have hPi : ∀ p i, i ≠ j → P p i = p i := fun p i hi => Function.update_of_ne hi _ _
  have hfix' : ∀ p : Fin n → Fin 3, σ (p j) = p j → pieceSign c p * φ (pieceMap p z) = 0 :=
    fun p hp => by rw [hfix (p j) hp _ rfl, mul_zero]
  have hmap : ∀ p : Fin n → Fin 3, σ (p j) ≠ p j → pieceMap (P p) z = pieceMap p z := by
    intro p hp; funext i
    by_cases hi : i = j
    · subst hi; simp only [pieceMap_apply, hPj]; exact hpt _ hp
    · simp only [pieceMap_apply, hPi p i hi]
  have hsign : ∀ p : Fin n → Fin 3, σ (p j) ≠ p j → pieceSign c (P p) = -pieceSign c p := by
    intro p hp
    unfold pieceSign
    rw [Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j
      (fun i => pieceSgn (c i) (p i)), hPj, hsgn _ hp, neg_mul]
    congr 2
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hPi p i (by simpa using hi)]
  refine Finset.sum_ninvolution P (fun p => ?_) (fun p hp hPp => hp ?_) (fun p => Finset.mem_univ _)
    (fun p => ?_)
  · by_cases hp : σ (p j) = p j
    · have : P p = p := by
        funext i; by_cases hi : i = j
        · subst hi; rw [hPj, hp]
        · exact hPi p i hi
      rw [this, hfix' p hp, add_zero]
    · rw [hmap p hp, hsign p hp]; ring
  · have : σ (p j) = p j := by rw [← hPj p, hPp]
    exact hfix' p this
  · funext i; by_cases hi : i = j
    · subst hi; rw [hPj, hPj, hσ]
    · rw [hPi _ i hi, hPi p i hi]

/-- **Odd folds vanish on the faces**: if `c_j = -1` and `φ` vanishes off `U`, then `fold_c φ`
vanishes on `{z_j ∈ {0, ½}}` (everywhere in `ℝⁿ`). -/
theorem foldFun_eq_zero {c : Fin n → ℝ} {φ : (Fin n → ℝ) → ℝ}
    (hφU : ∀ x, x ∉ bigCube n → φ x = 0) {j : Fin n} (hcj : c j = -1) {z : Fin n → ℝ}
    (hz : z j = 0 ∨ z j = 1 / 2) : foldFun c φ z = 0 := by
  have hout : ∀ x : Fin n → ℝ, x j ∉ Ioo (-(1 / 2) : ℝ) 1 → φ x = 0 := fun x hx =>
    hφU x fun h => hx (mem_bigCube.1 h j)
  have hs2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have hs0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  rcases hz with hz | hz
  · refine foldFun_eq_zero_aux (j := j) (Equiv.swap (0 : Fin 3) 1)
      (fun q => Equiv.swap_apply_self _ _ _) (fun q hq x hx => hout x ?_) (fun q hq => ?_)
      (fun q hq => ?_)
    · fin_cases q <;> simp [hs2] at hq ⊢
      rw [hx, hz]; norm_num
    · fin_cases q <;> simp [hs2] at hq ⊢ <;> rw [hz] <;> norm_num
    · fin_cases q <;> simp [pieceSgn, hcj, hs2] at hq ⊢
  · refine foldFun_eq_zero_aux (j := j) (Equiv.swap (1 : Fin 3) 2)
      (fun q => Equiv.swap_apply_self _ _ _) (fun q hq x hx => hout x ?_) (fun q hq => ?_)
      (fun q hq => ?_)
    · fin_cases q <;> simp [hs0] at hq ⊢
      rw [hx, hz]; norm_num
    · fin_cases q <;> simp [hs0] at hq ⊢ <;> rw [hz] <;> norm_num
    · fin_cases q <;> simp [pieceSgn, hcj, hs0] at hq ⊢

/-! ### The parity vectors of the mixed class `J` -/

/-- **The parity vector of the coefficient of `dx_s` in the mixed class `J`**:
`c_j = ε_j(J) ε_j(s)` with `ε_j(J) = -1` iff `j ∈ J` and `ε_j(s) = -1` iff `j ∈ s`
(the real form of `Feec.Models.Cube.DeRhamIdent.pcJ`): odd in `x_j` for the tangential components
(`j ∉ s`) when `j ∈ J`, and for the normal components (`j ∈ s`) when `j ∉ J`. -/
def pvec (J s : Finset (Fin n)) : Fin n → ℝ :=
  fun j => (if j ∈ J then -1 else 1) * (if j ∈ s then -1 else 1)

theorem isParity_pvec (J s : Finset (Fin n)) : IsParity (pvec J s) := fun j => by
  unfold pvec; split_ifs <;> norm_num

theorem pvec_erase (J : Finset (Fin n)) {s : Finset (Fin n)} {j : Fin n} (hj : j ∈ s) :
    pvec J (s.erase j) = Function.update (pvec J s) j (-pvec J s j) := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [pvec, hj]
  · simp [pvec, Finset.mem_erase, hi]

theorem pvec_of_mem_of_notMem {J s : Finset (Fin n)} {j : Fin n} (hJ : j ∈ J) (hs : j ∉ s) :
    pvec J s j = -1 := by simp [pvec, hJ, hs]

theorem pvec_of_notMem_of_mem {J s : Finset (Fin n)} {j : Fin n} (hJ : j ∉ J) (hs : j ∈ s) :
    pvec J s j = -1 := by simp [pvec, hJ, hs]

/-! ### The distributional exterior derivative of the parity extension -/

theorem half_le_norm_sub_of_notMem_bigCube {y : Fin n → ℝ} (hy : ∀ j, y j ∈ Icc (0 : ℝ) (1 / 2))
    {t : Fin n → ℝ} (ht : t ∉ bigCube n) : 1 / 2 ≤ ‖y - t‖ := by
  rw [mem_bigCube] at ht
  push Not at ht
  obtain ⟨j, hj⟩ := ht
  have h : (1 / 2 : ℝ) ≤ |y j - t j| := by
    rw [Set.mem_Ioo] at hj
    by_cases h1 : -(1 / 2) < t j
    · have h2 : 1 ≤ t j := by
        by_contra h; exact hj ⟨h1, by linarith⟩
      rw [abs_of_nonpos (by linarith [(hy j).2])]; linarith [(hy j).2]
    · rw [abs_of_nonneg (by linarith [(hy j).1])]; linarith [(hy j).1]
  have h2 : |y j - t j| ≤ ‖y - t‖ := by
    have := norm_le_pi_norm (y - t) j; rwa [Pi.sub_apply, Real.norm_eq_abs] at this
  linarith

namespace ReflKernel

variable (ρ : ReflKernel n)

theorem fderiv_eq_zero {v : Fin n → ℝ} (hv : ρ.radius < ‖v‖) : fderiv ℝ ρ.toFun v = 0 := by
  have h : ρ.toFun =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hv] with x hx
    exact ρ.eq_zero_of_le x (le_of_lt hx)
  rw [h.fderiv_eq]; simp

theorem exists_bound_fderiv : ∃ L, 0 ≤ L ∧ ∀ v, ‖fderiv ℝ ρ.toFun v‖ ≤ L := by
  obtain ⟨L, hL⟩ := (ρ.isTest.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (ρ.isTest.contDiff.continuous_fderiv (by simp))
  exact ⟨max L 0, le_max_right _ _, fun v => (hL v).trans (le_max_left _ _)⟩

theorem hasFDerivAt_comp_sub (y x : Fin n → ℝ) :
    HasFDerivAt (fun x => ρ (y - x)) (-fderiv ℝ ρ.toFun (y - x)) x := by
  have h := (ρ.isTest.contDiff.differentiable (by simp) (y - x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_sub y)
  exact h.congr_fderiv (by ext v; simp)

end ReflKernel

theorem abs_foldFun_le {c : Fin n → ℝ} (hc : IsParity c) {φ : (Fin n → ℝ) → ℝ} {M : ℝ}
    (hM : ∀ x, |φ x| ≤ M) (z : Fin n → ℝ) : |foldFun c φ z| ≤ 3 ^ n * M := by
  unfold foldFun
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p : Fin n → Fin 3, |pieceSign c p * φ (pieceMap p z)|
      ≤ ∑ _p : Fin n → Fin 3, M := Finset.sum_le_sum fun p _ => by
        rw [abs_mul, abs_pieceSign hc, one_mul]; exact hM _
    _ = 3 ^ n * M := by rw [Finset.sum_const, card_pieces, nsmul_eq_mul]; push_cast; ring

/-- **The smoothed parity extension commutes with `d_J`, pointwise on `cl Q`**: for
`u ∈ D(d_J)` and `ψ_r = ρ ⋆ ext_{c(J, r)} u_r`, the classical exterior derivative of `ψ` at every
point of `cl Q` is the smoothed extension of `d_J u`. The proof folds the kernel `ρ(y - ·)` onto
`Q` (`integral_parExt_mul`); the folded kernel is an admissible test function of Green's identity
for `d_J` (`Feec.Models.Cube.DeRhamIdent.greenForJ_dPart`): it vanishes on the faces where the
normal components of the test forms must (`foldFun_eq_zero`), and its partial derivatives are the
folds of the partial derivatives with the parity of one variable reversed (`fderiv_foldFun`,
`pvec_erase`). -/
theorem extD_smoothFun_eq (ρ : ReflKernel n) (J : Finset (Fin n)) (k : ℕ)
    (u : (DeRhamIdent.dPart (Q (Fin n)) J (k : ℤ)).domain) (t : formIdx n ((k : ℤ) + 1))
    {y : Fin n → ℝ} (hy : ∀ j, y j ∈ Icc (0 : ℝ) (1 / 2)) :
    extD (formExt fun r : formIdx n (k : ℤ) =>
        smoothFun ρ (pvec J r.1) (((u : L2F ℝ (Q (Fin n)) (formIdx n k)) r : L2 ℝ (Q (Fin n))) :
          (Fin n → ℝ) → ℝ)) t.1 y =
      smoothFun ρ (pvec J t.1) ((DeRhamIdent.dPart (Q (Fin n)) J (k : ℤ) u t :
        L2 ℝ (Q (Fin n))) : (Fin n → ℝ) → ℝ) y := by
  classical
  have : IsFiniteMeasure (volume.restrict (Q (Fin n))) :=
    isFiniteMeasure_restrict.2 (isBounded_openCube _ _).measure_lt_top.ne
  set w := DeRhamIdent.dPart (Q (Fin n)) J (k : ℤ) u
  have hG := DeRhamIdent.greenForJ_dPart J k u
  set φ : (Fin n → ℝ) → ℝ := fun x => ρ (y - x)
  have hφs : ContDiff ℝ ∞ φ := ρ.isTest.contDiff.comp (contDiff_const.sub contDiff_id)
  have hφU : ∀ x, x ∉ bigCube n → φ x = 0 := fun x hx => eq_zero_of_notMem_bigCube ρ hy hx
  obtain ⟨M, hM0, hM⟩ := ρ.exists_bound
  have hφM : ∀ x, |φ x| ≤ M := fun x => by rw [abs_of_nonneg (ρ.nonneg _)]; exact hM _
  obtain ⟨L, hL0, hL⟩ := ρ.exists_bound_fderiv
  have hφd : ∀ x v, fderiv ℝ φ x v = -fderiv ℝ ρ.toFun (y - x) v := fun x v => by
    rw [(ρ.hasFDerivAt_comp_sub y x).fderiv]; rfl
  have hφdM : ∀ j x, |fderiv ℝ φ x (Pi.single j 1)| ≤ L := fun j x => by
    rw [hφd, abs_neg, ← Real.norm_eq_abs]
    refine ((fderiv ℝ ρ.toFun (y - x)).le_opNorm _).trans ?_
    have h1 : ‖(Pi.single j 1 : Fin n → ℝ)‖ ≤ 1 := by rw [Pi.norm_single, norm_one]
    calc ‖fderiv ℝ ρ.toFun (y - x)‖ * ‖(Pi.single j 1 : Fin n → ℝ)‖ ≤ L * 1 :=
          mul_le_mul (hL _) h1 (norm_nonneg _) hL0
      _ = L := mul_one L
  have hφdU : ∀ j x, x ∉ bigCube n → fderiv ℝ φ x (Pi.single j 1) = 0 := fun j x hx => by
    rw [hφd, ρ.fderiv_eq_zero (lt_of_lt_of_le ρ.radius_lt
      (half_le_norm_sub_of_notMem_bigCube hy hx))]
    simp
  have hφdc : ∀ j, Continuous fun x => fderiv ℝ φ x (Pi.single j 1) := fun j =>
    (hφs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφdiff : Differentiable ℝ φ := hφs.differentiable (by simp)
  set c := pvec J t.1
  set Φ := foldFun c φ
  have hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ := contDiff_foldFun c hφs
  have hΦM : ∃ M', ∀ z, |Φ z| ≤ M' := ⟨3 ^ n * M, abs_foldFun_le (isParity_pvec J t.1) hφM⟩
  have hΦL : ∃ L', ∀ j z, |fderiv ℝ Φ z (Pi.single j 1)| ≤ L' := by
    refine ⟨3 ^ n * L, fun j z => ?_⟩
    rw [fderiv_foldFun c hφdiff z j]
    refine abs_foldFun_le ?_ (hφdM j) z
    intro i
    by_cases hi : i = j
    · subst hi; rw [Function.update_self]
      obtain h | h : c i = 1 ∨ c i = -1 := isParity_pvec J t.1 i <;> rw [h] <;> norm_num
    · rw [Function.update_of_ne hi]; exact isParity_pvec J t.1 i
  have hΦV : ∀ j ∈ t.1, j ∉ J → ∀ z : Fin n → ℝ, (z j = 0 ∨ z j = 1 / 2) → Φ z = 0 :=
    fun j hjt hjJ z hz => foldFun_eq_zero hφU (pvec_of_notMem_of_mem hjJ hjt) hz
  have hgreen := hG t Φ hΦs hΦM hΦL hΦV
  have hint : ∀ f : L2 ℝ (Q (Fin n)), IntegrableOn (f : (Fin n → ℝ) → ℝ) (Q (Fin n)) := fun f =>
    (Lp.memLp f).integrable one_le_two
  -- the left side of Green's identity
  have hlhs : ∫ z in Q (Fin n), (w t : (Fin n → ℝ) → ℝ) z * Φ z =
      smoothFun ρ c ((w t : L2 ℝ (Q (Fin n))) : (Fin n → ℝ) → ℝ) y := by
    rw [smoothFun_apply, ← (integral_parExt_mul c (hint (w t)) hφs.continuous hφM hφU).2]
  -- the terms of the right side
  have hrhs : ∀ j ∈ t.1, ∫ z in Q (Fin n),
      (DeRhamIdent.uExt (u : L2F ℝ (Q (Fin n)) (formIdx n k)) (t.1.erase j) :
        (Fin n → ℝ) → ℝ) z * fderiv ℝ Φ z (Pi.single j 1) =
      -fderiv ℝ (formExt (fun r : formIdx n (k : ℤ) =>
        smoothFun ρ (pvec J r.1) (((u : L2F ℝ (Q (Fin n)) (formIdx n k)) r :
          L2 ℝ (Q (Fin n))) : (Fin n → ℝ) → ℝ)) (t.1.erase j)) y (Pi.single j 1) := by
    intro j hj
    have hcard := card_erase_of_formIdx t hj
    set r₀ : formIdx n (k : ℤ) := ⟨t.1.erase j, hcard⟩
    have e1 : DeRhamIdent.uExt (u : L2F ℝ (Q (Fin n)) (formIdx n k)) (t.1.erase j) =
        (u : L2F ℝ (Q (Fin n)) (formIdx n k)) r₀ := formExt_of_card _ hcard
    have e2 : formExt (fun r : formIdx n (k : ℤ) =>
        smoothFun ρ (pvec J r.1) (((u : L2F ℝ (Q (Fin n)) (formIdx n k)) r :
          L2 ℝ (Q (Fin n))) : (Fin n → ℝ) → ℝ)) (t.1.erase j) =
        smoothFun ρ (pvec J (t.1.erase j)) (((u : L2F ℝ (Q (Fin n)) (formIdx n k)) r₀ :
          L2 ℝ (Q (Fin n))) : (Fin n → ℝ) → ℝ) := formExt_of_card _ hcard
    rw [e1, e2]
    have hΦd : ∀ z, fderiv ℝ Φ z (Pi.single j 1) =
        foldFun (Function.update c j (-c j)) (fun x => fderiv ℝ φ x (Pi.single j 1)) z :=
      fun z => fderiv_foldFun c hφdiff z j
    have hce : Function.update c j (-c j) = pvec J (t.1.erase j) := (pvec_erase J hj).symm
    simp_rw [hΦd, hce]
    set f₀ := (((u : L2F ℝ (Q (Fin n)) (formIdx n k)) r₀ : L2 ℝ (Q (Fin n))) :
      (Fin n → ℝ) → ℝ)
    rw [← (integral_parExt_mul (pvec J (t.1.erase j)) (hint _) (hφdc j) (hφdM j)
      (hφdU j)).2, fderiv_smoothFun ρ _ (hint _), ← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hφd]; ring
  rw [hlhs, Finset.sum_congr rfl fun j hj => by rw [hrhs j hj]] at hgreen
  rw [extD, hgreen]
  simp only [mul_neg, Finset.sum_neg_distrib, neg_neg]

/-! ### The parity smoother on `L²(Q; Λᵏ)` -/

section Operator

variable (ρ : ReflKernel n)

instance isFiniteMeasure_restrict_Q : IsFiniteMeasure (volume.restrict (Q (Fin n))) :=
  isFiniteMeasure_restrict.2 (isBounded_openCube _ _).measure_lt_top.ne

theorem integrableOn_L2 (f : L2 ℝ (Q (Fin n))) : IntegrableOn (f : (Fin n → ℝ) → ℝ) (Q (Fin n)) :=
  (Lp.memLp f).integrable one_le_two

theorem integrableOn_sq_L2 (f : L2 ℝ (Q (Fin n))) :
    IntegrableOn (fun z => (f : (Fin n → ℝ) → ℝ) z ^ 2) (Q (Fin n)) :=
  (Lp.memLp f).integrable_sq

theorem memLp_smoothFun (c : Fin n → ℝ) (f : L2 ℝ (Q (Fin n))) :
    MemLp (smoothFun ρ c (f : (Fin n → ℝ) → ℝ)) 2 (volume.restrict (Q (Fin n))) :=
  memLp_of_continuous measurableSet_Q (isBounded_openCube _ _)
    (contDiff_smoothFun ρ c (integrableOn_L2 f)).continuous

/-- The scalar parity smoother `f ↦ (ρ ⋆ ext_c f)|_Q`, as a linear map. -/
def scalarSmoothₗ (c : Fin n → ℝ) : L2 ℝ (Q (Fin n)) →ₗ[ℝ] L2 ℝ (Q (Fin n)) where
  toFun f := (memLp_smoothFun ρ c f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
    rw [smoothFun_congr_ae ρ c (Lp.coeFn_add f g),
      smoothFun_add ρ c (integrableOn_L2 f) (integrableOn_L2 g)]
  map_smul' a f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
    rw [smoothFun_congr_ae ρ c (Lp.coeFn_smul a f), smoothFun_smul]

theorem norm_scalarSmoothₗ_le {c : Fin n → ℝ} (hc : IsParity c) (f : L2 ℝ (Q (Fin n))) :
    ‖scalarSmoothₗ ρ c f‖ ≤ √(3 ^ n) * ‖f‖ := by
  have h1 : ‖scalarSmoothₗ ρ c f‖ ^ 2 =
      ∫ y in Q (Fin n), smoothFun ρ c (f : (Fin n → ℝ) → ℝ) y ^ 2 := by
    rw [Feec.FiniteElement.norm_sq_eq_integral_sq]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_smoothFun ρ c f)] with y hy
    change ((memLp_smoothFun ρ c f).toLp _ : (Fin n → ℝ) → ℝ) y ^ 2 = _
    rw [hy]
  have h2 := integral_sq_smoothFun_le ρ hc (integrableOn_L2 f) (integrableOn_sq_L2 f)
  rw [← Feec.FiniteElement.norm_sq_eq_integral_sq, ← h1] at h2
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact h2

/-- **The scalar parity smoother** `R_c f = (ρ ⋆ ext_c f)|_Q` on `L²(Q)`, bounded by
`3^{n/2}` (`norm_scalarSmoothₗ_le`). -/
def scalarSmooth (c : Fin n → ℝ) (hc : IsParity c) : L2 ℝ (Q (Fin n)) →L[ℝ] L2 ℝ (Q (Fin n)) :=
  (scalarSmoothₗ ρ c).mkContinuous (√(3 ^ n)) (norm_scalarSmoothₗ_le ρ hc)

theorem coeFn_scalarSmooth (c : Fin n → ℝ) (hc : IsParity c) (f : L2 ℝ (Q (Fin n))) :
    (scalarSmooth ρ c hc f : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict (Q (Fin n))]
      smoothFun ρ c (f : (Fin n → ℝ) → ℝ) :=
  MemLp.coeFn_toLp (memLp_smoothFun ρ c f)

variable (J : Finset (Fin n))

end Operator

/-! ### The weak-symmetry maps `S⁰`, `S¹` -/

section WeakSymmetry

open Feec.FiniteElement (wsL2 wsCoeff wsL2_apply wsCoeff_eq)

variable (ρ : ReflKernel n)

/-- `c(J ∆ {a}, t ∖ a) = c(J, t)` for `a ∈ t`: the `a`-th row of a vector of forms in the class
`J ∆ {a}` matches the class `J` after `S`. -/
theorem pvec_symmDiff_erase (J : Finset (Fin n)) {t : Finset (Fin n)} {a : Fin n} (ha : a ∈ t) :
    pvec (symmDiff J {a}) (t.erase a) = pvec J t := by
  classical
  funext j
  by_cases hj : j = a
  · subst hj
    by_cases hJ : j ∈ J <;> simp [pvec, Finset.mem_symmDiff, hJ, ha]
  · simp [pvec, Finset.mem_symmDiff, hj, Finset.mem_erase]

end WeakSymmetry

/-! ### Product kernels -/

/-- The one-dimensional bump with radii `r/2 < r`. -/
def bump1 (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by positivity, by linarith⟩

theorem prodKernel_eq_zero {r : ℝ} (hr : 0 < r) {x : Fin n → ℝ} (hx : r ≤ ‖x‖) :
    ∏ j, (bump1 r hr).normed volume (x j) = 0 := by
  have : ∃ j, r ≤ |x j| := by
    by_contra h
    push Not at h
    have : ‖x‖ < r := (pi_norm_lt_iff hr).2 fun j => by rw [Real.norm_eq_abs]; exact h j
    linarith
  obtain ⟨j, hj⟩ := this
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  refine Function.notMem_support.1 fun h => ?_
  rw [ContDiffBump.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at h
  exact absurd hj (not_le.2 h)

/-- **The product kernel** `ρ(x) = ∏ⱼ η_r(xⱼ)`, `η_r` the normalized one-dimensional bump of
radii `r/2 < r`: a reflection-invariant mollifier of radius `r` (`0 < r < ½`), with
`ρ ≤ r⁻ⁿ` (`prodKernel_le`). -/
def prodKernel (r : ℝ) (hr : 0 < r) (hr' : r < 1 / 2) : ReflKernel n where
  toFun x := ∏ j, (bump1 r hr).normed volume (x j)
  isTest := by
    refine ⟨contDiff_prod fun j _ => (bump1 r hr).contDiff_normed.comp (by fun_prop), ?_,
      subset_univ _⟩
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) r) fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact prodKernel_eq_zero hr hx.le
  nonneg x := Finset.prod_nonneg fun j _ => (bump1 r hr).nonneg_normed _
  integral_eq_one := by
    rw [integral_fintype_prod_volume_eq_prod (f := fun _ => (bump1 r hr).normed volume)]
    simp [ContDiffBump.integral_normed]
  radius := r
  radius_pos := hr
  radius_lt := hr'
  eq_zero_of_le x hx := prodKernel_eq_zero hr hx
  refl j x := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [coordRefl_apply]
    split_ifs
    · exact ContDiffBump.normed_neg _ _
    · rfl

theorem prodKernel_apply (r : ℝ) (hr : 0 < r) (hr' : r < 1 / 2) (x : Fin n → ℝ) :
    prodKernel (n := n) r hr hr' x = ∏ j, (bump1 r hr).normed volume (x j) := rfl

/-- **The sup bound of the product kernel**: `ρ ≤ r⁻ⁿ`. -/
theorem prodKernel_le (r : ℝ) (hr : 0 < r) (hr' : r < 1 / 2) (x : Fin n → ℝ) :
    prodKernel (n := n) r hr hr' x ≤ (1 / r) ^ n := by
  rw [prodKernel_apply, show (1 / r) ^ n = ∏ _j : Fin n, (1 / r) by simp]
  refine Finset.prod_le_prod₀ (fun j _ => (bump1 r hr).nonneg_normed _) fun j _ => ?_
  refine ((bump1 r hr).normed_le_div_measure_closedBall_rIn (μ := volume) (x j)).trans
    (le_of_eq ?_)
  rw [Real.volume_real_closedBall (by simp [bump1]; positivity)]
  simp [bump1]
  ring

/-! ### Symmetric functions -/

/-- **A symmetric function** of parity `c`: `F ∘ R_j = c_j F` for every coordinate reflection, and
`F` is `1`-periodic in every variable (the parity extensions of functions on `Q`). -/
structure IsSymm (c : Fin n → ℝ) (F : (Fin n → ℝ) → ℝ) : Prop where
  refl : ∀ j y, F (coordRefl j y) = c j * F y
  periodic : ∀ y (m : Fin n → ℤ), F (y + fun j => (m j : ℝ)) = F y

theorem IsSymm.update_one_sub {c : Fin n → ℝ} {F : (Fin n → ℝ) → ℝ} (hF : IsSymm c F)
    (j : Fin n) (y : Fin n → ℝ) : F (Function.update y j (1 - y j)) = c j * F y := by
  rw [update_one_sub_eq, hF.periodic, hF.refl]

theorem coordRefl_eq_update (j : Fin n) (y : Fin n → ℝ) :
    coordRefl j y = Function.update y j (-y j) := by
  funext i; rw [coordRefl_apply]
  by_cases hi : i = j
  · subst hi; simp
  · simp [hi]

/-- **A symmetric function on the copies of `Q`**: `F ∘ pieceMap p = sign_c(p) F`. -/
theorem IsSymm.apply_pieceMap {c : Fin n → ℝ} {F : (Fin n → ℝ) → ℝ} (hF : IsSymm c F)
    (p : Fin n → Fin 3) (z : Fin n → ℝ) : F (pieceMap p z) = pieceSign c p * F z := by
  classical
  suffices h : ∀ D : Finset (Fin n), ∀ p : Fin n → Fin 3, (∀ i ∉ D, p i = 1) →
      F (pieceMap p z) = pieceSign c p * F z from h Finset.univ p (by simp)
  intro D
  induction D using Finset.induction_on with
  | empty =>
    intro p hp
    have hp1 : p = fun _ => 1 := funext fun i => hp i (by simp)
    subst hp1
    have e : pieceMap (fun _ : Fin n => (1 : Fin 3)) z = z := funext fun _ => rfl
    rw [e]; simp [pieceSign, pieceSgn]
  | insert a D ha ih =>
    intro p hp
    set p' := Function.update p a 1
    have hp' : ∀ i ∉ D, p' i = 1 := fun i hi => by
      by_cases hia : i = a
      · subst hia; simp [p']
      · simp only [p', Function.update_of_ne hia]; exact hp i (by simp [hia, hi])
    have IH := ih p' hp'
    set y := pieceMap p' z
    have hya : y a = z a := by simp [y, p']
    have hmap : pieceMap p z = Function.update y a (piece (p a) (z a)) := by
      funext i
      by_cases hia : i = a
      · subst hia; simp
      · simp [y, p', Function.update_of_ne hia]
    have hsign : pieceSign c p = pieceSgn (c a) (p a) * pieceSign c p' := by
      unfold pieceSign
      rw [Fintype.prod_eq_mul_prod_compl a, Fintype.prod_eq_mul_prod_compl a
        (fun i => pieceSgn (c i) (p' i))]
      simp only [p', Function.update_self, pieceSgn, ↓reduceIte, one_mul]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      simp [Function.update_of_ne (show i ≠ a by simpa using hi)]
    rw [hmap, hsign, mul_assoc, ← IH]
    rcases (show p a = 0 ∨ p a = 1 ∨ p a = 2 by omega) with h | h | h
    · rw [h, piece_zero, ← hya, ← coordRefl_eq_update, hF.refl]; simp [pieceSgn]
    · rw [h, piece_one, ← hya, Function.update_eq_self]; simp [pieceSgn]
    · rw [h, piece_two, ← hya, hF.update_one_sub]; simp [pieceSgn]

/-- **A symmetric function is its own parity extension** (on the copies of `Q`). -/
theorem IsSymm.parExt_eq {c : Fin n → ℝ} {F : (Fin n → ℝ) → ℝ} (hF : IsSymm c F)
    {t : Fin n → ℝ} {p : Fin n → Fin 3} (hp : pieceMap p t ∈ Q (Fin n)) : parExt c F t = F t := by
  rw [parExt_eq_of_pieceMap_mem hp]
  have h := hF.apply_pieceMap p (pieceMap p t)
  rw [pieceMap_pieceMap] at h
  rw [h]

/-- **The smoothed extension of a symmetric function is its mollification** at the points of
`cl Q`. -/
theorem IsSymm.smoothFun_eq (ρ : ReflKernel n) {c : Fin n → ℝ} {F : (Fin n → ℝ) → ℝ}
    (hF : IsSymm c F) {f : (Fin n → ℝ) → ℝ} (hf : f =ᵐ[volume.restrict (Q (Fin n))] F)
    {y : Fin n → ℝ} (hy : ∀ j, y j ∈ Icc (0 : ℝ) (1 / 2)) :
    smoothFun ρ c f y = ∫ t, F t * ρ (y - t) := by
  rw [smoothFun_congr_ae ρ c hf, smoothFun_apply]
  have hae := ae_exists_pieceMap (n := n) (P := fun _ => True) (ae_of_all _ fun _ _ => trivial)
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  by_cases htU : t ∈ bigCube n
  · obtain ⟨p, hp, -⟩ := ht htU
    rw [hF.parExt_eq hp]
  · rw [eq_zero_of_notMem_bigCube ρ hy htU, mul_zero, mul_zero]

/-- **The squared gradient of a symmetric function is even and periodic.** -/
theorem IsSymm.sq_grad {c : Fin n → ℝ} (hc : IsParity c) {F : (Fin n → ℝ) → ℝ}
    (hF : IsSymm c F) (hd : Differentiable ℝ F) :
    IsSymm (fun _ => 1) (fun y => ∑ j, (fderiv ℝ F y (Pi.single j 1)) ^ 2) := by
  refine ⟨fun i y => ?_, fun y m => ?_⟩
  · rw [one_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : HasFDerivAt (fun y => F (coordRefl i y))
        ((fderiv ℝ F (coordRefl i y)).comp (diagL (reflIdx i))) y :=
      (hd _).hasFDerivAt.comp y (hasFDerivAt_pieceMap (reflIdx i) y)
    have h2 : HasFDerivAt (fun y => c i * F y) (c i • fderiv ℝ F y) y :=
      (hd y).hasFDerivAt.const_mul (c i)
    have e : (fun y => F (coordRefl i y)) = fun y => c i * F y := funext (hF.refl i)
    rw [e] at h1
    have h3 := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) (h1.unique h2)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, diagL_single, map_smul,
      smul_eq_mul, FunLike.coe_smul, Pi.smul_apply] at h3
    have hs : pieceSig (reflIdx i j) ^ 2 = 1 := by
      unfold pieceSig reflIdx; split_ifs <;> norm_num
    have hc2 : c i ^ 2 = 1 := by rcases hc i with h | h <;> rw [h] <;> norm_num
    calc (fderiv ℝ F (coordRefl i y) (Pi.single j 1)) ^ 2
        = (pieceSig (reflIdx i j) * fderiv ℝ F (coordRefl i y) (Pi.single j 1)) ^ 2 := by
          rw [mul_pow, hs, one_mul]
      _ = (c i * fderiv ℝ F y (Pi.single j 1)) ^ 2 := by rw [h3]
      _ = _ := by rw [mul_pow, hc2, one_mul]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have e : (fun x => F (x + fun j => (m j : ℝ))) = F := funext fun x => hF.periodic x m
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := y) (fun j => (m j : ℝ))
    rw [e] at h
    rw [← h]

/-- **Integrals of even periodic functions over `U`**: `∫_U G = 3ⁿ ∫_Q G`. -/
theorem integral_bigCube_eq_of_symm {G : (Fin n → ℝ) → ℝ} (hG : IsSymm (fun _ => 1) G)
    (hGi : IntegrableOn G (Q (Fin n))) :
    IntegrableOn G (bigCube n) ∧ ∫ x in bigCube n, G x = 3 ^ n * ∫ z in Q (Fin n), G z := by
  have hU : MeasurableSet (bigCube n) :=
    (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).measurableSet
  set G' : (Fin n → ℝ) → ℝ := (bigCube n).indicator G
  have hG' : ∀ x, x ∉ bigCube n → G' x = 0 := fun x hx => Set.indicator_of_notMem hx _
  have hsign : ∀ p : Fin n → Fin 3, pieceSign (fun _ : Fin n => (1 : ℝ)) p = 1 := fun p => by
    simp [pieceSign, pieceSgn]
  have hGp : ∀ p : Fin n → Fin 3, ∀ z ∈ Q (Fin n), G' (pieceMap p z) = G z := by
    intro p z hz
    simp only [G']
    rw [Set.indicator_of_mem (pieceMap_mem_bigCube hz p), hG.apply_pieceMap, hsign, one_mul]
  have hp : ∀ p : Fin n → Fin 3, IntegrableOn (fun z => G' (pieceMap p z)) (Q (Fin n)) :=
    fun p => IntegrableOn.congr_fun hGi (fun z hz => (hGp p z hz).symm) measurableSet_Q
  obtain ⟨hI, he⟩ := integral_eq_sum_pieceMap hG' hp
  refine ⟨(integrable_indicator_iff hU).1 hI, ?_⟩
  rw [← integral_indicator hU, he,
    Finset.sum_congr rfl fun p _ => setIntegral_congr_fun measurableSet_Q fun z hz => hGp p z hz,
    Finset.sum_const, card_pieces, nsmul_eq_mul]
  push_cast; ring

/-! ### The `H¹` estimate for smooth fields -/

/-- **Jensen's inequality for the mollifier**: `(∫ f ρ(x - ·))² ≤ ∫ f² ρ(x - ·)`. -/
theorem ReflKernel.sq_integral_le (ρ : ReflKernel n) (x : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : Integrable fun t => f t * ρ (x - t)) (hf2 : Integrable fun t => f t ^ 2 * ρ (x - t)) :
    (∫ t, f t * ρ (x - t)) ^ 2 ≤ ∫ t, f t ^ 2 * ρ (x - t) := by
  set a := ∫ t, f t * ρ (x - t)
  have hi0 := ρ.integrable_comp_sub x
  have hvar : 0 ≤ ∫ t, (f t - a) ^ 2 * ρ (x - t) :=
    integral_nonneg fun t => mul_nonneg (sq_nonneg _) (ρ.nonneg _)
  have hA : Integrable fun t => f t ^ 2 * ρ (x - t) - 2 * a * (f t * ρ (x - t)) :=
    hf2.sub (hf.const_mul _)
  have e1 : ∫ t, (f t ^ 2 * ρ (x - t) - 2 * a * (f t * ρ (x - t)) + a ^ 2 * ρ (x - t)) =
      (∫ t, (f t ^ 2 * ρ (x - t) - 2 * a * (f t * ρ (x - t)))) + ∫ t, a ^ 2 * ρ (x - t) :=
    integral_add hA (hi0.const_mul _)
  have e2 : ∫ t, (f t ^ 2 * ρ (x - t) - 2 * a * (f t * ρ (x - t))) =
      (∫ t, f t ^ 2 * ρ (x - t)) - ∫ t, 2 * a * (f t * ρ (x - t)) :=
    integral_sub hf2 (hf.const_mul _)
  have e : ∫ t, (f t - a) ^ 2 * ρ (x - t) =
      ∫ t, (f t ^ 2 * ρ (x - t) - 2 * a * (f t * ρ (x - t)) + a ^ 2 * ρ (x - t)) := by
    congr 1; funext t; ring
  rw [e, e1, e2, integral_const_mul, integral_const_mul, ρ.integral_comp_sub] at hvar
  nlinarith

/-- **Averaging along segments**: if `F x ≤ K₀ ∫ ρ(u) ∫₀¹ H(x - τu) dτ du` with `ρ` supported in
the ball of radius `r` and the segments of length `≤ r` from the points of `U` staying in `V`, then
`∫_U F ≤ K₀ (∫ ρ) ∫_V H`. -/
theorem lintegral_le_of_segment_avg {ρe H F : (Fin n → ℝ) → ℝ≥0∞} (hρm : Measurable ρe)
    (hHc : Continuous H) {U V : Set (Fin n → ℝ)} (hU : MeasurableSet U) (hV : MeasurableSet V)
    {r : ℝ} (hρr : ∀ u, ρe u ≠ 0 → ‖u‖ ≤ r)
    (hseg : ∀ x ∈ U, ∀ u : Fin n → ℝ, ‖u‖ ≤ r → ∀ τ ∈ Icc (0 : ℝ) 1, x - τ • u ∈ V) (K₀ : ℝ)
    (hpt : ∀ x, F x ≤ ENNReal.ofReal K₀ * ∫⁻ u, ρe u * ∫⁻ τ in Icc (0 : ℝ) 1, H (x - τ • u)) :
    ∫⁻ x in U, F x ≤ ENNReal.ofReal K₀ * ((∫⁻ u, ρe u) * ∫⁻ x in V, H x) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞,
      Ψ = fun x u => ∫⁻ τ in Set.Icc (0 : ℝ) 1, H (x - τ • u) := ⟨_, rfl⟩
  have hAc : Continuous fun q : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ => H (q.1.1 - q.2 • q.1.2) :=
    hHc.comp (by fun_prop)
  have hΨm : Measurable fun q : (Fin n → ℝ) × (Fin n → ℝ) => Ψ q.1 q.2 := by
    rw [hΨ]; exact hAc.measurable.lintegral_prod_right'
  -- exchange the integrals
  have h1 : ∫⁻ x in U, F x ≤ ∫⁻ x in U, ENNReal.ofReal K₀ * ∫⁻ u, ρe u * Ψ x u :=
    setLIntegral_mono' hU fun x _ => by rw [hΨ]; exact hpt x
  have h2 : ∫⁻ x in U, ENNReal.ofReal K₀ * ∫⁻ u, ρe u * Ψ x u =
      ENNReal.ofReal K₀ * ∫⁻ u, ρe u * ∫⁻ x in U, Ψ x u := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    rw [lintegral_lintegral_swap ((hρm.comp measurable_snd).mul hΨm).aemeasurable]
    refine lintegral_congr fun u => ?_
    exact lintegral_const_mul _ (hΨm.comp measurable_prodMk_right)
  -- the translations of each sample
  set Y := ∫⁻ x in V, H x
  have h3 : ∀ u, ρe u * ∫⁻ x in U, Ψ x u ≤ ρe u * Y := by
    intro u
    by_cases hu : ρe u = 0
    · simp [hu]
    have hu' := hρr u hu
    refine mul_le_mul' le_rfl ?_
    have hswap : ∫⁻ x in U, Ψ x u = ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ x in U, H (x - τ • u) := by
      rw [hΨ]
      refine lintegral_lintegral_swap ?_
      exact (hHc.comp (by fun_prop : Continuous fun q : (Fin n → ℝ) × ℝ =>
        q.1 - q.2 • u)).measurable.aemeasurable
    rw [hswap]
    calc ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ x in U, H (x - τ • u)
        ≤ ∫⁻ τ in Set.Icc (0 : ℝ) 1, Y := by
          refine setLIntegral_mono' measurableSet_Icc fun τ hτ => ?_
          calc ∫⁻ x in U, H (x - τ • u) = ∫⁻ x in U, V.indicator H (x - τ • u) := by
                refine setLIntegral_congr_fun hU fun x hx => ?_
                rw [Set.indicator_of_mem (hseg x hx u hu' τ hτ)]
            _ ≤ ∫⁻ x, V.indicator H (x - τ • u) := setLIntegral_le_lintegral _ _
            _ = ∫⁻ x, V.indicator H x := lintegral_sub_right_eq_self _ _
            _ = Y := by rw [lintegral_indicator hV]
      _ = Y := by rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ ENNReal.ofReal K₀ * ∫⁻ u, ρe u * Y := mul_le_mul' le_rfl (lintegral_mono fun u => h3 u)
    _ = _ := by rw [lintegral_mul_const _ hρm]

open Feec.Models.Cube.FEM (sq_sub_le_integral_grad ofReal_intervalIntegral_le_lintegral) in
/-- **The `L²` error of the mollifier for a `C¹` function**: if the segments from the points of `U`
to the points sampled by `ρ` stay in `V`,
`∫_U |w - w ⋆ ρ|² ≤ r² n ∫_V |∇w|²` (`r` the radius of `ρ`). -/
theorem lintegral_sq_sub_conv_le (ρ : ReflKernel n) {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ 1 w)
    {U V : Set (Fin n → ℝ)} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hseg : ∀ x ∈ U, ∀ u : Fin n → ℝ, ‖u‖ ≤ ρ.radius → ∀ τ ∈ Icc (0 : ℝ) 1, x - τ • u ∈ V) :
    ∫⁻ x in U, ENNReal.ofReal ((w x - ∫ t, w t * ρ (x - t)) ^ 2) ≤
      ENNReal.ofReal (ρ.radius ^ 2 * n) *
        ∫⁻ x in V, ENNReal.ofReal (∑ j, (partialDeriv j w x) ^ 2) := by
  have hfd := hw.continuous_fderiv one_ne_zero
  have hwc : Continuous w := hw.continuous
  obtain ⟨G, hG⟩ : ∃ G : (Fin n → ℝ) → ℝ≥0∞,
      G = fun y => ENNReal.ofReal (∑ j, (partialDeriv j w y) ^ 2) := ⟨_, rfl⟩
  have hGc : Continuous G := by
    rw [hG]; simp only [partialDeriv]
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞,
      Ψ = fun x u => ∫⁻ τ in Set.Icc (0 : ℝ) 1, G (x - τ • u) := ⟨_, rfl⟩
  obtain ⟨ρe, hρe⟩ : ∃ ρe : (Fin n → ℝ) → ℝ≥0∞, ρe = fun u => ENNReal.ofReal (ρ u) := ⟨_, rfl⟩
  have hρm : Measurable ρe := by
    rw [hρe]; exact (ENNReal.continuous_ofReal.comp ρ.continuous).measurable
  set K₀ := ρ.radius ^ 2 * n
  -- step 1: the pointwise bound
  have hpt : ∀ x, ENNReal.ofReal ((w x - ∫ t, w t * ρ (x - t)) ^ 2) ≤
      ENNReal.ofReal K₀ * ∫⁻ u, ρe u * Ψ x u := by
    intro x
    have hρi := ρ.integrable_comp_sub x
    have hρ1 := ρ.integral_comp_sub x
    set f : (Fin n → ℝ) → ℝ := fun t => w x - w t
    have hfc : Continuous f := continuous_const.sub hwc
    have hwi : Integrable fun t => w t * ρ (x - t) :=
      integrable_mul_isTest hwc.locallyIntegrable (ρ.isTest.comp_sub x)
    have hfi : Integrable fun t => f t * ρ (x - t) :=
      integrable_mul_isTest hfc.locallyIntegrable (ρ.isTest.comp_sub x)
    have hf2i : Integrable fun t => f t ^ 2 * ρ (x - t) :=
      integrable_mul_isTest (hfc.pow 2).locallyIntegrable (ρ.isTest.comp_sub x)
    have e1 : w x - ∫ t, w t * ρ (x - t) = ∫ t, f t * ρ (x - t) := by
      symm
      calc ∫ t, f t * ρ (x - t) = ∫ t, (w x * ρ (x - t) - w t * ρ (x - t)) :=
            integral_congr_ae (Eventually.of_forall fun t => by simp only [f]; ring)
        _ = w x * (∫ t, ρ (x - t)) - ∫ t, w t * ρ (x - t) := by
            rw [integral_sub (hρi.const_mul _) hwi, integral_const_mul]
        _ = _ := by rw [hρ1, mul_one]
    rw [e1]
    refine (ENNReal.ofReal_le_ofReal (ρ.sq_integral_le x hfi hf2i)).trans ?_
    rw [ofReal_integral_eq_lintegral_ofReal hf2i
      (Eventually.of_forall fun t => mul_nonneg (sq_nonneg _) (ρ.nonneg _))]
    rw [← lintegral_sub_left_eq_self (fun t => ENNReal.ofReal (f t ^ 2 * ρ (x - t))) x,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun u => ?_
    simp only [sub_sub_cancel]
    by_cases hu : ρ u = 0
    · rw [hu]; simp
    · have hu' : ‖u‖ < ρ.radius := by
        by_contra h; push Not at h; exact hu (ρ.eq_zero_of_le u h)
      have hL1 := sq_sub_le_integral_grad hw x (x - u)
      have hft : f (x - u) ^ 2 = (w (x - u) - w x) ^ 2 := by simp only [f]; ring
      have hseg' : ∀ τ : ℝ, x + τ • (x - u - x) = x - τ • u := fun τ => by
        rw [show x - u - x = -u by abel, smul_neg]; abel
      simp only [hseg'] at hL1
      have hGc' : Continuous fun τ : ℝ => ∑ j, (partialDeriv j w (x - τ • u)) ^ 2 := by
        simp only [partialDeriv]; fun_prop
      have hG0 : ∀ τ : ℝ, 0 ≤ ∑ j, (partialDeriv j w (x - τ • u)) ^ 2 := fun τ =>
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hI0 : 0 ≤ ∫ τ in (0 : ℝ)..1, ∑ j, (partialDeriv j w (x - τ • u)) ^ 2 :=
        intervalIntegral.integral_nonneg zero_le_one fun τ _ => hG0 τ
      have hK : (w (x - u) - w x) ^ 2 ≤ K₀ *
          ∫ τ in (0 : ℝ)..1, ∑ j, (partialDeriv j w (x - τ • u)) ^ 2 := by
        refine hL1.trans (mul_le_mul_of_nonneg_right ?_ hI0)
        rw [show x - u - x = -u by abel, norm_neg]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hu'.le 2)
          (Nat.cast_nonneg _)
      rw [ENNReal.ofReal_mul (sq_nonneg _), hft]
      calc ENNReal.ofReal ((w (x - u) - w x) ^ 2) * ENNReal.ofReal (ρ u)
          ≤ ENNReal.ofReal (K₀ *
              ∫ τ in (0 : ℝ)..1, ∑ j, (partialDeriv j w (x - τ • u)) ^ 2) *
              ENNReal.ofReal (ρ u) := by gcongr
        _ = ENNReal.ofReal K₀ * ENNReal.ofReal
              (∫ τ in (0 : ℝ)..1, ∑ j, (partialDeriv j w (x - τ • u)) ^ 2) *
              ENNReal.ofReal (ρ u) := by
            rw [ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal K₀ * (∫⁻ τ in Set.Icc (0 : ℝ) 1,
              ENNReal.ofReal (∑ j, (partialDeriv j w (x - τ • u)) ^ 2)) *
              ENNReal.ofReal (ρ u) := by
            gcongr
            exact ofReal_intervalIntegral_le_lintegral hGc' hG0
        _ = _ := by rw [hρe, hΨ, hG]; ring
  have hρr : ∀ u, ρe u ≠ 0 → ‖u‖ ≤ ρ.radius := fun u hu => by
    by_contra h; push Not at h; exact hu (by simp [hρe, ρ.eq_zero_of_le u h.le])
  have hρ1 : ∫⁻ u, ρe u = 1 := by
    rw [hρe, ← ofReal_integral_eq_lintegral_ofReal ρ.integrable
      (Eventually.of_forall fun u => ρ.nonneg u), ρ.integral_eq_one, ENNReal.ofReal_one]
  have h := lintegral_le_of_segment_avg hρm hGc hU hV hρr hseg K₀
    (F := fun x => ENNReal.ofReal ((w x - ∫ t, w t * ρ (x - t)) ^ 2))
    fun x => (hpt x).trans_eq (by rw [hΨ])
  rwa [hρ1, one_mul, hG] at h

/-- **The `H¹` estimate of the parity smoother for smooth symmetric functions**:
`∫_Q |g - R g|² ≤ r² n 3ⁿ ∫_Q |∇g|²`. -/
theorem integral_sq_sub_smoothFun_le_of_symm (ρ : ReflKernel n) {c : Fin n → ℝ}
    (hc : IsParity c) {g : (Fin n → ℝ) → ℝ} (hg : ContDiff ℝ 1 g) (hgs : IsSymm c g) :
    ∫ y in Q (Fin n), (g y - smoothFun ρ c g y) ^ 2 ≤
      ρ.radius ^ 2 * n * 3 ^ n * ∫ y in Q (Fin n), ∑ j, (partialDeriv j g y) ^ 2 := by
  have hU : MeasurableSet (bigCube n) :=
    (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).measurableSet
  have hQc : IsCompact (closure (Q (Fin n))) := (isBounded_openCube _ _).isCompact_closure
  have hgi : IntegrableOn g (Q (Fin n)) :=
    (hg.continuous.continuousOn.integrableOn_compact hQc).mono_set subset_closure
  have hd : Continuous fun y => ∑ j, (partialDeriv j g y) ^ 2 := by
    have := hg.continuous_fderiv one_ne_zero
    simp only [partialDeriv]; fun_prop
  set G : (Fin n → ℝ) → ℝ := fun y => ∑ j, (partialDeriv j g y) ^ 2
  have hGs : IsSymm (fun _ => 1) G := hgs.sq_grad hc (hg.differentiable one_ne_zero)
  have hGi : IntegrableOn G (Q (Fin n)) :=
    (hd.continuousOn.integrableOn_compact hQc).mono_set subset_closure
  obtain ⟨hGU, hGUe⟩ := integral_bigCube_eq_of_symm hGs hGi
  set F : (Fin n → ℝ) → ℝ := fun y => (g y - smoothFun ρ c g y) ^ 2
  have hFc : Continuous F := (hg.continuous.sub (contDiff_smoothFun ρ c hgi).continuous).pow 2
  have hFi : IntegrableOn F (Q (Fin n)) :=
    (hFc.continuousOn.integrableOn_compact hQc).mono_set subset_closure
  have hFe : ∀ y ∈ Q (Fin n), F y = (g y - ∫ t, g t * ρ (y - t)) ^ 2 := fun y hy => by
    simp only [F]
    rw [hgs.smoothFun_eq ρ (ae_eq_refl _) fun j => Ioo_subset_Icc_self (mem_Q.1 hy j)]
  have hseg : ∀ x ∈ Q (Fin n), ∀ u : Fin n → ℝ, ‖u‖ ≤ ρ.radius → ∀ τ ∈ Icc (0 : ℝ) 1,
      x - τ • u ∈ bigCube n := by
    intro x hx u hu τ hτ
    rw [mem_bigCube]
    intro j
    have hxj := mem_Q.1 hx j
    have huj : |u j| ≤ ρ.radius := by
      have := (norm_le_pi_norm u j).trans hu; rwa [Real.norm_eq_abs] at this
    have hτu : |τ * u j| ≤ ρ.radius := by
      rw [abs_mul, abs_of_nonneg hτ.1]
      calc τ * |u j| ≤ 1 * |u j| := mul_le_mul_of_nonneg_right hτ.2 (abs_nonneg _)
        _ ≤ ρ.radius := by rw [one_mul]; exact huj
    rw [abs_le] at hτu
    have := ρ.radius_lt
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    constructor <;> linarith [hxj.1, hxj.2, hτu.1, hτu.2]
  have hL := lintegral_sq_sub_conv_le ρ hg measurableSet_Q hU hseg
  have h1 : ∫⁻ x in Q (Fin n), ENNReal.ofReal (F x) =
      ∫⁻ x in Q (Fin n), ENNReal.ofReal ((g x - ∫ t, g t * ρ (x - t)) ^ 2) :=
    setLIntegral_congr_fun measurableSet_Q fun x hx => by rw [hFe x hx]
  rw [← h1, ← ofReal_integral_eq_lintegral_ofReal hFi
      (Eventually.of_forall fun x => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hGU
      (Eventually.of_forall fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _),
    ← ENNReal.ofReal_mul (by positivity), hGUe] at hL
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hL
  calc ∫ y in Q (Fin n), F y ≤ ρ.radius ^ 2 * n * (3 ^ n * ∫ z in Q (Fin n), G z) := hL
    _ = _ := by ring

/-! ### The `H¹` estimate on `D(d_J)`, by density -/

/-- The `0`-form with coefficient `f`. -/
def zeroForm {Ω : Set (Fin n → ℝ)} (f : L2 ℝ Ω) : L2F ℝ Ω (formIdx n ((0 : ℕ) : ℤ)) :=
  WithLp.toLp 2 fun _ => f

/-- The index of the `0`-forms. -/
def idx₀ : formIdx n ((0 : ℕ) : ℤ) := ⟨∅, by simp⟩

theorem zeroForm_apply {Ω : Set (Fin n → ℝ)} (f : L2 ℝ Ω) (s : formIdx n ((0 : ℕ) : ℤ)) :
    zeroForm f s = f := rfl

theorem eq_idx₀ (s : formIdx n ((0 : ℕ) : ℤ)) : s = idx₀ :=
  Subtype.ext (Finset.card_eq_zero.1 (by exact_mod_cast s.2))

/-- `Σ_t ((dψ)_t)² = |∇ψ|²` for a `0`-form. -/
theorem sum_sq_extDerivOp_zero (ψ : formIdx n ((0 : ℕ) : ℤ) → (Fin n → ℝ) → ℝ)
    (y : Fin n → ℝ) :
    ∑ t : formIdx n (((0 : ℕ) : ℤ) + 1), ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).apply ψ t y) ^ 2 =
      ∑ j, (partialDeriv j (ψ idx₀) y) ^ 2 := by
  change ∑ t : formIdx n 1, ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).apply ψ t y) ^ 2 = _
  rw [← (Feec.Models.Cube.FEM.singletonEquiv n).sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).apply ψ ⟨{j}, by simp⟩ y) ^ 2 = _
  rw [extDerivOp_apply, extD, Finset.sum_singleton, Finset.erase_singleton,
    formExt_of_card _ (by simp)]
  have hsg : (ExteriorFibre.sgn j ({j} : Finset (Fin n)) : ℝ) = 1 := by
    simp [ExteriorFibre.sgn, Finset.filter_singleton]
  rw [hsg, one_mul]
  rfl

section Approx

open DeRhamIdent UnitAddTorus Feec.Fourier.TorusWeak MirrorExt
open Feec.Fourier.Exterior (Form)

/-- **Smooth symmetric approximants in `D(d_J)` for `0`-forms**: the real trigonometric
polynomials of the Fourier truncations of the parity extension
(`Feec.Models.Cube.DeRhamIdent.mem_dPart_of_JfJ`) are smooth, symmetric with the parities of the
class, and converge in the graph norm of `d_J`. -/
theorem exists_symm_approx (J' : Finset (Fin n))
    (u : (dPart (Q (Fin n)) J' ((0 : ℕ) : ℤ)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : formIdx n ((0 : ℕ) : ℤ) → (Fin n → ℝ) → ℝ, (∀ s, ContDiff ℝ (⊤ : ℕ∞) (ψ s)) ∧
      (∀ s, IsSymm (pvec J' ∅) (ψ s)) ∧
      ∃ (hψ : ∀ s, MemLp (ψ s) 2 (volume.restrict (Q (Fin n))))
        (hdψ : ∀ t, MemLp ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).apply ψ t) 2
          (volume.restrict (Q (Fin n)))),
        ‖(u : L2F ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ))) - toL2F hψ‖ < ε ∧
        ‖dPart (Q (Fin n)) J' ((0 : ℕ) : ℤ) u - toL2F hdψ‖ < ε := by
  classical
  set x := JfJ J' 0 (u : L2F ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ)))
  set y := JfJ J' 1 (dPart (Q (Fin n)) J' ((0 : ℕ) : ℤ) u)
  have hx : RealParJ J' 0 x := JfJ_realParJ J' 0 _
  have hxy : ∀ m, (Feec.Fourier.Exterior.deRham (Fin n)).m 0 (0 + 1)
      (Feec.Fourier.Torus.freq m) ((x : (Fin n → ℤ) → Form ℂ (Fin n) 0) m) =
        (y : (Fin n → ℤ) → Form ℂ (Fin n) (0 + 1)) m := coeff_d_dPart J' 0 u
  have hc1 : Tendsto (fun N => Jinvf 0 (trunc N 0 x)) atTop
      (𝓝 (u : L2F ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ)))) := by
    have := ((Jinvf (n := n) 0).continuous.tendsto _).comp (tendsto_trunc 0 x)
    rwa [Jinvf_JfJ] at this
  have hc2 : Tendsto (fun N => Jinvf 1 (trunc N 1 y)) atTop
      (𝓝 (dPart (Q (Fin n)) J' ((0 : ℕ) : ℤ) u)) := by
    have := ((Jinvf (n := n) 1).continuous.tendsto _).comp (tendsto_trunc 1 y)
    rwa [Jinvf_JfJ] at this
  rw [Metric.tendsto_atTop] at hc1 hc2
  obtain ⟨N₁, hN₁⟩ := hc1 ε hε
  obtain ⟨N₂, hN₂⟩ := hc2 ε hε
  set N := max N₁ N₂
  have h1 := hN₁ N (le_max_left _ _)
  have h2 := hN₂ N (le_max_right _ _)
  rw [dist_eq_norm, norm_sub_rev] at h1 h2
  set ψ := trigLift 0 (trunc N 0 x) (bandS N)
  have hxN := realParJ_trunc hx N
  obtain ⟨M, L, hL0, hM, hL⟩ := trigLift_bounds 0 (trunc N 0 x) (bandS N)
  have hcl := mem_dPart_of_smooth (J := J') (contDiff_trigLift 0 (trunc N 0 x) (bandS N))
    hM hL0 hL (fun s j hjJ hj y hy => trigLift_eq_zero_of_faceJ hxN
      (fun j m hm => flipAt_mem_bandS j hm) hjJ hj hy) (memLp_trigLift 0 _ _)
      (memLp_d_trigLift 0 _ _)
  have hJ0 : Jinvf 0 (trunc N 0 x) = toL2F (memLp_trigLift 0 (trunc N 0 x) (bandS N)) :=
    Jinvf_eq_toL2F fun m hm => trunc_eq_zero_of_notMem x hm
  rw [← hJ0] at hcl
  obtain ⟨v, hv1, hv2⟩ := (LinearPMap.mem_graph_iff _).1 hcl
  have hJ : JfJ J' 1 (dPart (Q (Fin n)) J' ((0 : ℕ) : ℤ) v) = trunc N 1 y := by
    refine Lp.ext_count fun m => ?_
    rw [← coeff_d_dPart J' 0 v m, ← symbol_trunc hxy N m,
      show (v : L2F ℝ (Q (Fin n)) _) = Jinvf 0 (trunc N 0 x) from hv1, JfJ_Jinvf hxN]
  have hd : toL2F (memLp_d_trigLift 0 (trunc N 0 x) (bandS N)) = Jinvf 1 (trunc N 1 y) := by
    have hv2' : toL2F (memLp_d_trigLift 0 (trunc N 0 x) (bandS N)) =
        dPart (Q (Fin n)) J' ((0 : ℕ) : ℤ) v := hv2.symm
    rw [hv2', ← hJ, Jinvf_JfJ]
  refine ⟨ψ, fun s => contDiff_trigLift 0 _ _ s, fun s => ?_, memLp_trigLift 0 _ _,
    memLp_d_trigLift 0 _ _, by rw [← hJ0]; exact h1, by rw [hd]; exact h2⟩
  -- the symmetry of the trigonometric polynomials
  set f := mFourierBasis.repr (physF 0 (trunc N 0 x) s)
  refine ⟨fun j z => ?_, fun z m => ?_⟩
  · have hf : ∀ m, f (flipB (single j) m) = (pvec J' ∅ j : ℂ) * f m := fun m => by
      have e : flipB (single j) m = DeRham.flipAt j m := flipAt_eq j m
      simp only [f]
      rw [e, repr_physF, repr_physF, hxN.2]
      have hs : (idx 0 s).1 = ∅ := by
        rw [idx_val, eq_idx₀ s]; rfl
      simp only [DeRham.mixedSign, DeRham.reflSign, pvec, hs, Finset.notMem_empty, ↓reduceIte,
        mul_one]
      split_ifs <;> simp
    have h := trigPoly_reflB (ε := single j) (S := bandS N)
      (fun m hm => by rw [show flipB (single j) m = DeRham.flipAt j m from flipAt_eq j m];
                      exact flipAt_mem_bandS j hm) hf (proj z)
    have hz : proj (coordRefl j z) = reflB (single j) (proj z) := by
      rw [← proj_reflR]
      congr 1
      funext i
      simp [coordRefl_apply, single]
    simp only [ψ, trigLift]
    rw [hz, h, Complex.re_ofReal_mul]
  · have hp : proj (z + fun j => (m j : ℝ)) = proj z := by
      rw [proj_add]
      have : proj (fun j => (m j : ℝ)) = 0 := by funext j; simp [proj]
      rw [this, add_zero]
    simp only [ψ, trigLift, hp]

end Approx

open Feec.Models.Cube.FEM (norm_sub_le_of_approx) in
/-- **The `H¹` estimate of the parity smoother on `D(d_{J'})`** (`0`-forms, i.e. `H¹` with
vanishing trace on the faces normal to `J'`, the functions whose parity extension `ext_{c(J', ∅)}`
is `H¹`): `‖f - R f‖ ≤ r √(n 3ⁿ) ‖∇f‖` ([Brezis2011], §9.2; the factor `3^{n/2}` is
`‖∇ ext f‖_{L²(U)} / ‖∇ f‖_{L²(Q)}`). -/
theorem norm_sub_scalarSmooth_le_grad (ρ : ReflKernel n) (J' : Finset (Fin n))
    (u : (DeRhamIdent.dPart (Q (Fin n)) J' ((0 : ℕ) : ℤ)).domain) :
    ‖(u : L2F ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ))) idx₀ -
      scalarSmooth ρ (pvec J' ∅) (isParity_pvec J' ∅)
        ((u : L2F ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ))) idx₀)‖ ≤
      ρ.radius * √(n * 3 ^ n) * ‖DeRhamIdent.dPart (Q (Fin n)) J' ((0 : ℕ) : ℤ) u‖ := by
  have hK : 0 ≤ ρ.radius * √(n * 3 ^ n) := mul_nonneg ρ.radius_pos.le (Real.sqrt_nonneg _)
  refine norm_sub_le_of_approx _ hK _ fun ε hε => ?_
  obtain ⟨ψ, hψs, hψsym, hψ, hdψ, h1, h2⟩ := exists_symm_approx J' u hε
  refine ⟨(toL2F hψ) idx₀, ‖toL2F hdψ‖, ?_, ?_, ?_⟩
  · refine lt_of_le_of_lt ?_ h1
    exact PiLp.norm_apply_le ((u : L2F ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ))) - toL2F hψ) idx₀
  · have := norm_sub_le (DeRhamIdent.dPart (Q (Fin n)) J' ((0 : ℕ) : ℤ) u)
      (DeRhamIdent.dPart (Q (Fin n)) J' ((0 : ℕ) : ℤ) u - toL2F hdψ)
    rw [sub_sub_cancel] at this
    linarith
  · set g := ψ idx₀
    have hg1 : ContDiff ℝ 1 g := (hψs idx₀).of_le (by exact_mod_cast le_top)
    have hcoe : (((toL2F hψ) idx₀ : L2 ℝ (Q (Fin n))) : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict
        (Q (Fin n))] g := MemLp.coeFn_toLp (hψ idx₀)
    have hsq1 : ‖(toL2F hψ) idx₀ - scalarSmooth ρ (pvec J' ∅) (isParity_pvec J' ∅)
        ((toL2F hψ) idx₀)‖ ^ 2 = ∫ y in Q (Fin n), (g y - smoothFun ρ (pvec J' ∅) g y) ^ 2 := by
      rw [Feec.FiniteElement.norm_sq_eq_integral_sq]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub ((toL2F hψ) idx₀) (scalarSmooth ρ (pvec J' ∅)
        (isParity_pvec J' ∅) ((toL2F hψ) idx₀)), hcoe,
        coeFn_scalarSmooth ρ (pvec J' ∅) (isParity_pvec J' ∅) ((toL2F hψ) idx₀)] with y e1 e2 e3
      rw [e1, Pi.sub_apply, e2, e3, smoothFun_congr_ae ρ _ hcoe]
    have hsq2 : ‖toL2F hdψ‖ ^ 2 = ∫ y in Q (Fin n), ∑ j, (partialDeriv j g y) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      have e : ∀ t : formIdx n (((0 : ℕ) : ℤ) + 1), ‖(toL2F hdψ) t‖ ^ 2 =
          ∫ y in Q (Fin n), ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).apply ψ t y) ^ 2 := fun t => by
        rw [Feec.FiniteElement.norm_sq_eq_integral_sq]
        exact integral_congr_ae ((MemLp.coeFn_toLp (hdψ t)).mono fun y hy => by
          change (((hdψ t).toLp _ : L2 ℝ (Q (Fin n))) : (Fin n → ℝ) → ℝ) y ^ 2 = _
          rw [hy])
      simp_rw [e]
      rw [← integral_finsetSum _ fun t _ => (hdψ t).integrable_sq]
      refine setIntegral_congr_fun measurableSet_Q fun y _ => ?_
      exact sum_sq_extDerivOp_zero ψ y
    have hmain := integral_sq_sub_smoothFun_le_of_symm ρ (isParity_pvec J' ∅) hg1 (hψsym idx₀)
    rw [← hsq1, ← hsq2] at hmain
    refine le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hK (norm_nonneg _)) ?_
    calc _ ≤ ρ.radius ^ 2 * n * 3 ^ n * ‖toL2F hdψ‖ ^ 2 := hmain
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring

theorem pvec_symmDiff_empty (J s : Finset (Fin n)) : pvec (symmDiff J s) ∅ = pvec J s := by
  funext j
  by_cases hJ : j ∈ J <;> by_cases hs : j ∈ s <;> simp [pvec, Finset.mem_symmDiff, hJ, hs]

/-! ### High-order estimates: kernels with vanishing moments -/

/-- **A reflection-invariant kernel with vanishing moments of the orders `1, …, m - 1`** (signed in
general, `m ≥ 3`): a smooth, compactly supported, reflection-invariant `ρ` with `∫ ρ = 1` and
`∫ ρ(x) x_{v₁} ⋯ x_{vᵢ} dx = 0` for `1 ≤ i < m`. The moments of odd order vanish for every
reflection-invariant kernel, so the nonnegative kernels are of this kind for `m = 2`; for every
`m ≥ 1` a Richardson combination of dilates is one. -/
structure MomentKernel (n m : ℕ) where
  /-- the kernel -/
  toFun : (Fin n → ℝ) → ℝ
  isTest : IsTest (univ : Set (Fin n → ℝ)) toFun
  integral_eq_one : ∫ x, toFun x = 1
  /-- the support radius -/
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt : radius < 1 / 2
  eq_zero_of_le : ∀ x, radius ≤ ‖x‖ → toFun x = 0
  refl : ∀ j x, toFun (coordRefl j x) = toFun x
  moment : ∀ i, 1 ≤ i → i < m → ∀ v : Fin i → Fin n, ∫ x, toFun x * ∏ l, x (v l) = 0

namespace MomentKernel

variable {m : ℕ}

instance : CoeFun (MomentKernel n m) fun _ => (Fin n → ℝ) → ℝ := ⟨MomentKernel.toFun⟩

variable (K : MomentKernel n m)

theorem continuous : Continuous K := K.isTest.contDiff.continuous

theorem integrable : Integrable K :=
  K.continuous.integrable_of_hasCompactSupport K.isTest.hasCompactSupport

/-- The `L¹` norm `∫ |ρ|`. -/
def l1 : ℝ := ∫ x, |K x|

theorem l1_nonneg : 0 ≤ K.l1 := integral_nonneg fun _ => abs_nonneg _

theorem eq_zero_of_lt {u : Fin n → ℝ} (h : K u ≠ 0) : ‖u‖ < K.radius := by
  by_contra h'; push Not at h'; exact h (K.eq_zero_of_le u h')

/-- **Moment cancellation**: `∫ ρ(u) L(u, …, u) du = 0` for every multilinear `L` of order
`1 ≤ i < m`. -/
theorem integral_mul_multilinear_eq_zero {i : ℕ} (hi1 : 1 ≤ i) (him : i < m)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin n → ℝ) ℝ) :
    ∫ u, K u * L (fun _ => u) = 0 := by
  classical
  have hexp : ∀ u : Fin n → ℝ, L (fun _ => u) =
      ∑ v : Fin i → Fin n, (∏ l, u (v l)) * L (fun l => Pi.single (v l) 1) := by
    intro u
    have hu : (fun _ : Fin i => u) = fun _ => ∑ j, u j • (Pi.single j 1 : Fin n → ℝ) := by
      funext _ i'; simp [Finset.sum_apply, Pi.single_apply]
    rw [hu, L.map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [L.map_smul_univ, smul_eq_mul]
  have hint : ∀ v : Fin i → Fin n, Integrable fun u => K u * ∏ l, u (v l) := fun v => by
    have hc : Continuous fun u : Fin n → ℝ => ∏ l, u (v l) :=
      continuous_finsetProd _ fun l _ => continuous_apply _
    exact (integrable_mul_isTest hc.locallyIntegrable K.isTest).congr
      (ae_of_all _ fun u => by simp only; ring)
  simp_rw [hexp, Finset.mul_sum]
  rw [integral_finsetSum _ fun v _ => (hint v).mul_const _ |>.congr
    (ae_of_all _ fun u => by simp only; ring)]
  refine Finset.sum_eq_zero fun v _ => ?_
  have e : (fun u => K u * ((∏ l, u (v l)) * L (fun l => Pi.single (v l) 1))) =
      fun u => (K u * ∏ l, u (v l)) * L (fun l => Pi.single (v l) 1) := by funext u; ring
  rw [e, integral_mul_const, K.moment i hi1 him v, zero_mul]

end MomentKernel

/-! ### Kernels with vanishing moments of every order -/

namespace ReflKernel

variable (ρ : ReflKernel n)

/-- **The dilate** `ρ_λ(x) = λ⁻ⁿ ρ(λ⁻¹ x)` of a reflection-invariant mollifier. -/
def dil (l : ℝ) (x : Fin n → ℝ) : ℝ := (l ^ n)⁻¹ * ρ (l⁻¹ • x)

theorem contDiff_dil (l : ℝ) : ContDiff ℝ ∞ (ρ.dil l) :=
  contDiff_const.mul (ρ.isTest.contDiff.comp (contDiff_const_smul _))

end ReflKernel

/-- **Weighted Cauchy–Schwarz**: `(∫ a b)² ≤ (∫ |a|) (∫ |a| b²)`. -/
theorem sq_integral_mul_le {a b : (Fin n → ℝ) → ℝ} (ha : Integrable a)
    (hab : Integrable fun u => |a u| * |b u|) (hab2 : Integrable fun u => |a u| * b u ^ 2) :
    (∫ u, a u * b u) ^ 2 ≤ (∫ u, |a u|) * ∫ u, |a u| * b u ^ 2 := by
  have h1 : |∫ u, a u * b u| ≤ ∫ u, |a u| * |b u| :=
    (abs_integral_le_integral_abs).trans (le_of_eq (integral_congr_ae (ae_of_all _ fun u =>
      abs_mul _ _)))
  have hq : ∀ x : ℝ, 0 ≤ (∫ u, |a u|) * (x * x) + (-2 * ∫ u, |a u| * |b u|) * x +
      ∫ u, |a u| * b u ^ 2 := by
    intro x
    have e : (∫ u, |a u|) * (x * x) + (-2 * ∫ u, |a u| * |b u|) * x + ∫ u, |a u| * b u ^ 2 =
        ∫ u, |a u| * (|b u| - x) ^ 2 := by
      have hI : ∀ u, |a u| * (|b u| - x) ^ 2 =
          |a u| * b u ^ 2 - 2 * x * (|a u| * |b u|) + x ^ 2 * |a u| := fun u => by
        rw [sub_sq, sq_abs]; ring
      simp_rw [hI]
      have e1 : ∫ u, (|a u| * b u ^ 2 - 2 * x * (|a u| * |b u|) + x ^ 2 * |a u|) =
          (∫ u, (|a u| * b u ^ 2 - 2 * x * (|a u| * |b u|))) + ∫ u, x ^ 2 * |a u| :=
        integral_add (hab2.sub (hab.const_mul _)) (ha.abs.const_mul _)
      have e2 : ∫ u, (|a u| * b u ^ 2 - 2 * x * (|a u| * |b u|)) =
          (∫ u, |a u| * b u ^ 2) - ∫ u, 2 * x * (|a u| * |b u|) :=
        integral_sub hab2 (hab.const_mul _)
      rw [e1, e2, integral_const_mul, integral_const_mul]
      ring
    rw [e]
    exact integral_nonneg fun u => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have h2 : (∫ u, |a u| * |b u|) ^ 2 ≤ (∫ u, |a u|) * ∫ u, |a u| * b u ^ 2 := by nlinarith
  calc (∫ u, a u * b u) ^ 2 = |∫ u, a u * b u| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ u, |a u| * |b u|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ ≤ _ := h2

/-- The reflection `R_j` as a linear isometry of `ℝⁿ` (sup norm). -/
def coordReflLIE (j : Fin n) : (Fin n → ℝ) ≃ₗᵢ[ℝ] (Fin n → ℝ) where
  toFun := coordRefl j
  invFun := coordRefl j
  map_add' x y := by funext i; simp only [coordRefl_apply, Pi.add_apply]; split_ifs <;> ring
  map_smul' a x := by
    funext i; simp only [coordRefl_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring
  left_inv := coordRefl_coordRefl j
  right_inv := coordRefl_coordRefl j
  norm_map' x := by
    have h : ∀ y : Fin n → ℝ, ‖coordRefl j y‖ ≤ ‖y‖ := fun y => by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      rw [coordRefl_apply]
      split_ifs
      · rw [norm_neg]; exact norm_le_pi_norm y i
      · exact norm_le_pi_norm y i
    refine le_antisymm (h x) ?_
    have := h (coordRefl j x)
    rwa [coordRefl_coordRefl] at this

/-- **The squared `m`-th derivative of a symmetric function is even and periodic.** -/
theorem IsSymm.sq_iteratedFDeriv {c : Fin n → ℝ} (hc : IsParity c) {F : (Fin n → ℝ) → ℝ}
    (hF : IsSymm c F) {m : ℕ} (hd : ContDiff ℝ m F) :
    IsSymm (fun _ => 1) (fun y => ‖iteratedFDeriv ℝ m F y‖ ^ 2) := by
  refine ⟨fun i y => ?_, fun y p => ?_⟩
  · rw [one_mul]
    have h1 := (coordReflLIE (n := n) i).norm_iteratedFDeriv_comp_right F y m
    have e : F ∘ (coordReflLIE i) = c i • F := funext fun y => hF.refl i y
    rw [e, iteratedFDeriv_const_smul_apply (hd.contDiffAt.of_le le_rfl), norm_smul,
      Real.norm_eq_abs] at h1
    have hci : |c i| = 1 := by rcases hc i with h | h <;> rw [h] <;> norm_num
    rw [hci, one_mul] at h1
    change ‖iteratedFDeriv ℝ m F (coordRefl i y)‖ ^ 2 = _
    rw [show coordRefl i y = coordReflLIE i y from rfl, ← h1]
  · have e : (fun z => F (z + fun j => (p j : ℝ))) = F := funext fun z => hF.periodic z p
    have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := F) m (fun j => (p j : ℝ)) y
    rw [e] at h
    rw [← h]

theorem MomentKernel.integrable_mul {m : ℕ} (K : MomentKernel n m) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable fun u => K u * f u :=
  (integrable_mul_isTest hf.locallyIntegrable K.isTest).congr
    (ae_of_all _ fun u => by simp only; ring)

/-- The Taylor remainder of order `m` of `G` at `x` in the direction `-u`. -/
def taylorRem (G : (Fin n → ℝ) → ℝ) (m : ℕ) (x u : Fin n → ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, (1 - τ) ^ (m - 1) * iteratedFDeriv ℝ m G (x - τ • u) (fun _ => -u)

/-- The Taylor remainder as a combination of values (Taylor's formula). -/
theorem taylorRem_eq {m : ℕ} (hm : 1 ≤ m) {G : (Fin n → ℝ) → ℝ} (hG : ContDiff ℝ m G)
    (x u : Fin n → ℝ) : taylorRem G m x u = ((m - 1).factorial : ℝ) * (G (x - u) -
      ∑ k ∈ Finset.range m, ((k.factorial : ℝ))⁻¹ * iteratedFDeriv ℝ k G x (fun _ => -u)) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hfac : ((m'.factorial : ℝ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m'
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (f := G) (x := x) (y := -u) (n := m')
    (fun t _ => hG.contDiffAt)
  rw [← sub_eq_add_neg] at h
  rw [h]
  simp only [smul_eq_mul, taylorRem, Nat.add_sub_cancel]
  have e : ∫ τ in (0 : ℝ)..1, (1 - τ) ^ m' * iteratedFDeriv ℝ (m' + 1) G (x + τ • -u)
      (fun _ => -u) = ∫ τ in (0 : ℝ)..1, (1 - τ) ^ m' *
        iteratedFDeriv ℝ (m' + 1) G (x - τ • u) (fun _ => -u) :=
    intervalIntegral.integral_congr fun τ _ => by simp only [smul_neg, ← sub_eq_add_neg]
  rw [e]
  field_simp
  ring

theorem continuous_taylorRem {m : ℕ} (hm : 1 ≤ m) {G : (Fin n → ℝ) → ℝ} (hG : ContDiff ℝ m G)
    (x : Fin n → ℝ) : Continuous (taylorRem G m x) := by
  have hcontk : ∀ k, Continuous fun u : Fin n → ℝ => iteratedFDeriv ℝ k G x (fun _ => -u) :=
    fun k => (iteratedFDeriv ℝ k G x).cont.comp (continuous_pi fun _ => continuous_neg)
  have e : taylorRem G m x = fun u => ((m - 1).factorial : ℝ) * (G (x - u) -
      ∑ k ∈ Finset.range m, ((k.factorial : ℝ))⁻¹ * iteratedFDeriv ℝ k G x (fun _ => -u)) :=
    funext (taylorRem_eq hm hG x)
  rw [e]
  exact continuous_const.mul ((hG.continuous.comp (continuous_const.sub continuous_id)).sub
    (continuous_finsetSum _ fun k _ => continuous_const.mul (hcontk k)))

/-- **The error of a moment kernel is the averaged Taylor remainder**:
`G(x) - (G ⋆ ρ)(x) = -((m - 1)!)⁻¹ ∫ ρ(u) R_m(x, u) du` (the polynomial part of degree `< m`
is reproduced by the vanishing moments). -/
theorem sub_conv_eq_taylorRem {m : ℕ} (K : MomentKernel n m) (hm : 1 ≤ m)
    {G : (Fin n → ℝ) → ℝ} (hG : ContDiff ℝ m G) (x : Fin n → ℝ) :
    Integrable (fun u => K u * taylorRem G m x u) ∧
      G x - ∫ t, G t * K (x - t) = -(((m - 1).factorial : ℝ))⁻¹ * ∫ u, K u * taylorRem G m x u := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hfac : ((m'.factorial : ℝ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m'
  -- Taylor's formula in the direction `-u`
  have hT : ∀ u : Fin n → ℝ, G (x - u) = ∑ k ∈ Finset.range (m' + 1),
      ((k.factorial : ℝ))⁻¹ * iteratedFDeriv ℝ k G x (fun _ => -u) +
        ((m'.factorial : ℝ))⁻¹ * taylorRem G (m' + 1) x u := fun u => by
    rw [taylorRem_eq hm hG x u, Nat.add_sub_cancel]; field_simp; ring
  have hcontk : ∀ k, Continuous fun u : Fin n → ℝ => iteratedFDeriv ℝ k G x (fun _ => -u) :=
    fun k => (iteratedFDeriv ℝ k G x).cont.comp (continuous_pi fun _ => continuous_neg)
  have hKR : Integrable fun u => K u * taylorRem G (m' + 1) x u :=
    K.integrable_mul (continuous_taylorRem hm hG x)
  refine ⟨hKR, ?_⟩
  -- the moments kill the polynomial part
  have hmom : ∀ k ∈ Finset.range (m' + 1), 1 ≤ k →
      ∫ u, K u * iteratedFDeriv ℝ k G x (fun _ => -u) = 0 := by
    intro k hk hk1
    have hkm : k < m' + 1 := Finset.mem_range.1 hk
    have h := K.integral_mul_multilinear_eq_zero hk1 hkm
      ((iteratedFDeriv ℝ k G x).compContinuousLinearMap fun _ => -ContinuousLinearMap.id ℝ _)
    simpa using h
  have hconv : ∫ t, G t * K (x - t) = ∫ u, K u * G (x - u) := by
    rw [← integral_sub_left_eq_self (fun t => G t * K (x - t)) volume x]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [sub_sub_cancel]; ring
  have hK1 : ∫ u, K u = 1 := K.integral_eq_one
  have hint : ∀ k, Integrable fun u => K u * (((k.factorial : ℝ))⁻¹ *
      iteratedFDeriv ℝ k G x (fun _ => -u)) := fun k =>
    K.integrable_mul (continuous_const.mul (hcontk k))
  have hexp : ∀ u, K u * G (x - u) = ∑ k ∈ Finset.range (m' + 1), K u * (((k.factorial : ℝ))⁻¹ *
      iteratedFDeriv ℝ k G x (fun _ => -u)) +
        ((m'.factorial : ℝ))⁻¹ * (K u * taylorRem G (m' + 1) x u) := fun u => by
    rw [hT u, mul_add, Finset.mul_sum]; ring
  have hsum : ∫ u, ∑ k ∈ Finset.range (m' + 1), K u * (((k.factorial : ℝ))⁻¹ *
      iteratedFDeriv ℝ k G x (fun _ => -u)) = G x := by
    rw [integral_finsetSum _ fun k _ => hint k, Finset.sum_range_succ']
    rw [Finset.sum_eq_zero fun k hk => by
      rw [show (fun u => K u * (((k + 1).factorial : ℝ)⁻¹ *
          iteratedFDeriv ℝ (k + 1) G x (fun _ => -u))) =
        fun u => ((k + 1).factorial : ℝ)⁻¹ * (K u * iteratedFDeriv ℝ (k + 1) G x (fun _ => -u))
          from funext fun u => by ring, integral_const_mul,
        hmom (k + 1) (Finset.mem_range.2 (by simp at hk; omega)) (by omega), mul_zero]]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, iteratedFDeriv_zero_apply,
      zero_add]
    rw [integral_mul_const, hK1, one_mul]
  rw [hconv, integral_congr_ae (ae_of_all _ hexp),
    integral_add (integrable_finsetSum _ fun k _ => hint k) (hKR.const_mul _), hsum,
    integral_const_mul]
  ring

open Feec.Models.Cube.FEM (sq_intervalIntegral_le) in
/-- **The bound of the Taylor remainder**:
`R_m(x, u)² ≤ ‖u‖^{2m} ∫₀¹ ‖Dᵐ G(x - τ u)‖² dτ`. -/
theorem sq_taylorRem_le {m : ℕ} {G : (Fin n → ℝ) → ℝ} (hG : ContDiff ℝ m G)
    (x u : Fin n → ℝ) :
    taylorRem G m x u ^ 2 ≤
      ‖u‖ ^ (2 * m) * ∫ τ in (0 : ℝ)..1, ‖iteratedFDeriv ℝ m G (x - τ • u)‖ ^ 2 := by
  have hDc : Continuous (iteratedFDeriv ℝ m G) := hG.continuous_iteratedFDeriv le_rfl
  have hfc : Continuous fun τ : ℝ =>
      (1 - τ) ^ (m - 1) * iteratedFDeriv ℝ m G (x - τ • u) (fun _ => -u) := by
    refine (continuous_const.sub continuous_id).pow _ |>.mul ?_
    exact (continuous_eval_const (fun _ : Fin m => -u)).comp
      (hDc.comp (continuous_const.sub (continuous_id.smul continuous_const)))
  refine (sq_intervalIntegral_le hfc).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by norm_num) ((hfc.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul ((hDc.comp (continuous_const.sub (continuous_id.smul
      continuous_const))).norm.pow 2)).intervalIntegrable _ _) fun τ hτ => ?_
  have h1 : |iteratedFDeriv ℝ m G (x - τ • u) (fun _ => -u)| ≤
      ‖iteratedFDeriv ℝ m G (x - τ • u)‖ * ‖u‖ ^ m := by
    have := (iteratedFDeriv ℝ m G (x - τ • u)).le_opNorm (fun _ => -u)
    rw [Real.norm_eq_abs] at this
    simpa [norm_neg] using this
  have h2 : |(1 - τ) ^ (m - 1)| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg (by linarith [hτ.2]) _)]
    exact pow_le_one₀ (by linarith [hτ.2]) (by linarith [hτ.1])
  rw [← sq_abs, abs_mul]
  calc (|(1 - τ) ^ (m - 1)| * |iteratedFDeriv ℝ m G (x - τ • u) (fun _ => -u)|) ^ 2
      ≤ (1 * (‖iteratedFDeriv ℝ m G (x - τ • u)‖ * ‖u‖ ^ m)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul h2 h1 (abs_nonneg _) zero_le_one) 2
    _ = ‖u‖ ^ (2 * m) * ‖iteratedFDeriv ℝ m G (x - τ • u)‖ ^ 2 := by ring

open Feec.Models.Cube.FEM (ofReal_intervalIntegral_le_lintegral) in
/-- **The `L²` error of a kernel with vanishing moments of orders `< m`** for a `Cᵐ` function: if the
segments from the points of `U` to the points sampled by `ρ` stay in `V`,
`∫_U |G - G ⋆ ρ|² ≤ ‖ρ‖₁² (rᵐ / (m - 1)!)² ∫_V ‖Dᵐ G‖²`. -/
theorem lintegral_sq_sub_conv_le_of_moments {m : ℕ} (K : MomentKernel n m) (hm : 1 ≤ m)
    {G : (Fin n → ℝ) → ℝ} (hG : ContDiff ℝ m G) {U V : Set (Fin n → ℝ)} (hU : MeasurableSet U)
    (hV : MeasurableSet V)
    (hseg : ∀ x ∈ U, ∀ u : Fin n → ℝ, ‖u‖ ≤ K.radius → ∀ τ ∈ Icc (0 : ℝ) 1, x - τ • u ∈ V) :
    ∫⁻ x in U, ENNReal.ofReal ((G x - ∫ t, G t * K (x - t)) ^ 2) ≤
      ENNReal.ofReal (K.l1 ^ 2 * (K.radius ^ m / (m - 1).factorial) ^ 2) *
        ∫⁻ x in V, ENNReal.ofReal (‖iteratedFDeriv ℝ m G x‖ ^ 2) := by
  have hDc : Continuous (iteratedFDeriv ℝ m G) := hG.continuous_iteratedFDeriv le_rfl
  obtain ⟨H, hH⟩ : ∃ H : (Fin n → ℝ) → ℝ≥0∞,
      H = fun y => ENNReal.ofReal (‖iteratedFDeriv ℝ m G y‖ ^ 2) := ⟨_, rfl⟩
  have hHc : Continuous H := by
    rw [hH]; exact ENNReal.continuous_ofReal.comp (hDc.norm.pow 2)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞,
      Ψ = fun x u => ∫⁻ τ in Set.Icc (0 : ℝ) 1, H (x - τ • u) := ⟨_, rfl⟩
  obtain ⟨ρe, hρe⟩ : ∃ ρe : (Fin n → ℝ) → ℝ≥0∞, ρe = fun u => ENNReal.ofReal |K u| := ⟨_, rfl⟩
  have hρm : Measurable ρe := by
    rw [hρe]; exact (ENNReal.continuous_ofReal.comp K.continuous.abs).measurable
  set fm := ((m - 1).factorial : ℝ)
  have hfm : 0 < fm := Nat.cast_pos.2 (Nat.factorial_pos _)
  set K₀ := (fm⁻¹) ^ 2 * K.l1 * K.radius ^ (2 * m)
  -- step 1: the pointwise bound
  have hpt : ∀ x, ENNReal.ofReal ((G x - ∫ t, G t * K (x - t)) ^ 2) ≤
      ENNReal.ofReal K₀ * ∫⁻ u, ρe u * Ψ x u := by
    intro x
    obtain ⟨hKR, he⟩ := sub_conv_eq_taylorRem K hm hG x
    have hRc := continuous_taylorRem hm hG x
    have hab : Integrable fun u => |K u| * |taylorRem G m x u| :=
      (K.integrable_mul hRc.abs).abs.congr (ae_of_all _ fun u => by simp [abs_mul])
    have hab2 : Integrable fun u => |K u| * taylorRem G m x u ^ 2 :=
      (K.integrable_mul (hRc.pow 2)).abs.congr (ae_of_all _ fun u => by
        simp only [abs_mul, Pi.pow_apply]; rw [abs_of_nonneg (sq_nonneg (taylorRem G m x u))])
    have hCS := sq_integral_mul_le K.integrable hab hab2
    have hΦc : ∀ u, Continuous fun τ : ℝ => ‖iteratedFDeriv ℝ m G (x - τ • u)‖ ^ 2 := fun u =>
      (hDc.comp (continuous_const.sub (continuous_id.smul continuous_const))).norm.pow 2
    have hΦ0 : ∀ (u : Fin n → ℝ) (τ : ℝ), 0 ≤ ‖iteratedFDeriv ℝ m G (x - τ • u)‖ ^ 2 :=
      fun u τ => sq_nonneg _
    rw [he, mul_pow, neg_sq]
    have hstep1 : (fm⁻¹) ^ 2 * (∫ u, K u * taylorRem G m x u) ^ 2 ≤
        (fm⁻¹) ^ 2 * (K.l1 * ∫ u, |K u| * taylorRem G m x u ^ 2) :=
      mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    refine (ENNReal.ofReal_le_ofReal hstep1).trans ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul K.l1_nonneg,
      ofReal_integral_eq_lintegral_ofReal hab2
        (Eventually.of_forall fun u => mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    have hK₀ : ENNReal.ofReal K₀ = ENNReal.ofReal ((fm⁻¹) ^ 2) * ENNReal.ofReal K.l1 *
        ENNReal.ofReal (K.radius ^ (2 * m)) := by
      simp only [K₀]
      rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) K.l1_nonneg),
        ENNReal.ofReal_mul (sq_nonneg _)]
    rw [hK₀, mul_assoc, mul_assoc]
    refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun u => ?_
    by_cases hu : K u = 0
    · simp [hρe, hu]
    · have hu' := K.eq_zero_of_lt hu
      have hR2 := sq_taylorRem_le hG x u
      have hI : ENNReal.ofReal (∫ τ in (0 : ℝ)..1, ‖iteratedFDeriv ℝ m G (x - τ • u)‖ ^ 2) ≤
          Ψ x u := by
        rw [hΨ, hH]
        exact ofReal_intervalIntegral_le_lintegral (hΦc u) (hΦ0 u)
      calc ENNReal.ofReal (|K u| * taylorRem G m x u ^ 2)
          ≤ ENNReal.ofReal (|K u| * (K.radius ^ (2 * m) *
              ∫ τ in (0 : ℝ)..1, ‖iteratedFDeriv ℝ m G (x - τ • u)‖ ^ 2)) := by
            refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hR2.trans ?_)
              (abs_nonneg _))
            refine mul_le_mul_of_nonneg_right ?_ (intervalIntegral.integral_nonneg zero_le_one
              fun τ _ => hΦ0 u τ)
            exact pow_le_pow_left₀ (norm_nonneg _) hu'.le _
        _ = ENNReal.ofReal (K.radius ^ (2 * m)) * (ρe u * ENNReal.ofReal
              (∫ τ in (0 : ℝ)..1, ‖iteratedFDeriv ℝ m G (x - τ • u)‖ ^ 2)) := by
            have hr := K.radius_pos
            rw [hρe, ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
        _ ≤ ENNReal.ofReal (K.radius ^ (2 * m)) * (ρe u * Ψ x u) := by gcongr
  have hρr : ∀ u, ρe u ≠ 0 → ‖u‖ ≤ K.radius := fun u hu =>
    (K.eq_zero_of_lt fun h => hu (by simp [hρe, h])).le
  set Y := ∫⁻ x in V, H x
  -- step 4: the mass of `|ρ|`
  have hρ1 : ∫⁻ u, ρe u = ENNReal.ofReal K.l1 := by
    rw [hρe, ← ofReal_integral_eq_lintegral_ofReal K.integrable.abs
      (Eventually.of_forall fun u => abs_nonneg _)]
    rfl
  calc _ ≤ ENNReal.ofReal K₀ * ((∫⁻ u, ρe u) * Y) :=
        lintegral_le_of_segment_avg hρm hHc hU hV hρr hseg K₀ fun x =>
          (hpt x).trans_eq (by rw [hΨ])
    _ = ENNReal.ofReal K₀ * (ENNReal.ofReal K.l1 * Y) := by rw [hρ1]
    _ = _ := by
        have hl := K.l1_nonneg
        have hr := K.radius_pos
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        simp only [K₀, Y, hH]
        congr 2
        rw [div_pow, ← pow_mul]; field_simp; ring

theorem seg_mem_bigCube {r : ℝ} (hr : r < 1 / 2) {x : Fin n → ℝ} (hx : x ∈ Q (Fin n))
    {u : Fin n → ℝ} (hu : ‖u‖ ≤ r) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : x - τ • u ∈ bigCube n := by
  rw [mem_bigCube]
  intro j
  have hxj := mem_Q.1 hx j
  have huj : |u j| ≤ r := by
    have := (norm_le_pi_norm u j).trans hu; rwa [Real.norm_eq_abs] at this
  have hτu : |τ * u j| ≤ r := by
    rw [abs_mul, abs_of_nonneg hτ.1]
    calc τ * |u j| ≤ 1 * |u j| := mul_le_mul_of_nonneg_right hτ.2 (abs_nonneg _)
      _ ≤ r := by rw [one_mul]; exact huj
  rw [abs_le] at hτu
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor <;> linarith [hxj.1, hxj.2, hτu.1, hτu.2]

/-- **The high-order estimate of the parity smoother** ([AFW2010], §5.4; [Brezis2011], §9.2): for a
kernel with vanishing moments of the orders `1, …, m - 1` and the parity extension `G = ext_c u`
of a function `u` on `Q` which is `Cᵐ` on `ℝⁿ` (`G` symmetric of parity `c`; this requires the
reflection compatibility conditions of `u` on `∂Q`),
`‖u - R u‖²_{L²(Q)} ≤ ‖ρ‖₁² (εᵐ / (m - 1)!)² 3ⁿ ‖Dᵐ G‖²_{L²(Q)}` (`ε` the radius of `ρ`; the
factor `3ⁿ` is `‖Dᵐ ext_c u‖²_{L²(U)} / ‖Dᵐ G‖²_{L²(Q)}`). Here `R u = (ρ ⋆ ext_c u)|_Q` and
`ext_c u = G` (`IsSymm.parExt_eq`). For `m ≤ 2` every reflection-invariant mollifier qualifies. -/
theorem integral_sq_sub_conv_le_of_moments {m : ℕ} (K : MomentKernel n m) (hm : 1 ≤ m)
    {c : Fin n → ℝ} (hc : IsParity c) {G : (Fin n → ℝ) → ℝ} (hG : ContDiff ℝ m G)
    (hGs : IsSymm c G) :
    ∫ x in Q (Fin n), (G x - ∫ t, parExt c G t * K (x - t)) ^ 2 ≤
      K.l1 ^ 2 * (K.radius ^ m / (m - 1).factorial) ^ 2 * 3 ^ n *
        ∫ x in Q (Fin n), ‖iteratedFDeriv ℝ m G x‖ ^ 2 := by
  have hU : MeasurableSet (bigCube n) :=
    (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).measurableSet
  have hQc : IsCompact (closure (Q (Fin n))) := (isBounded_openCube _ _).isCompact_closure
  have hDc : Continuous (iteratedFDeriv ℝ m G) := hG.continuous_iteratedFDeriv le_rfl
  set D : (Fin n → ℝ) → ℝ := fun y => ‖iteratedFDeriv ℝ m G y‖ ^ 2
  have hDs : IsSymm (fun _ => 1) D := hGs.sq_iteratedFDeriv hc hG
  have hDi : IntegrableOn D (Q (Fin n)) :=
    ((hDc.norm.pow 2).continuousOn.integrableOn_compact hQc).mono_set subset_closure
  obtain ⟨hDU, hDUe⟩ := integral_bigCube_eq_of_symm hDs hDi
  -- the parity extension of a symmetric function is itself
  have hpe : ∀ x ∈ Q (Fin n), ∫ t, parExt c G t * K (x - t) = ∫ t, G t * K (x - t) := by
    intro x hx
    have hae := ae_exists_pieceMap (n := n) (P := fun _ => True) (ae_of_all _ fun _ _ => trivial)
    refine integral_congr_ae ?_
    filter_upwards [hae] with t ht
    by_cases htU : t ∈ bigCube n
    · obtain ⟨p, hp, -⟩ := ht htU
      rw [hGs.parExt_eq hp]
    · have hxt : K (x - t) = 0 := K.eq_zero_of_le _ (le_trans K.radius_lt.le
        (half_le_norm_sub_of_notMem_bigCube (fun j => Ioo_subset_Icc_self (mem_Q.1 hx j)) htU))
      rw [hxt, mul_zero, mul_zero]
  set F : (Fin n → ℝ) → ℝ := fun x => (G x - ∫ t, G t * K (x - t)) ^ 2
  have hFc : Continuous F := by
    have : (fun x => ∫ t, G t * K (x - t)) =
        G ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K.toFun :=
      funext fun x => (convolution_apply_mul _ _ x).symm
    have hc2 : Continuous (fun x => ∫ t, G t * K (x - t)) := by
      rw [this]
      exact (K.isTest.hasCompactSupport.contDiff_convolution_right _
        hG.continuous.locallyIntegrable K.isTest.contDiff).continuous
    exact (hG.continuous.sub hc2).pow 2
  have hFi : IntegrableOn F (Q (Fin n)) :=
    (hFc.continuousOn.integrableOn_compact hQc).mono_set subset_closure
  have hL := lintegral_sq_sub_conv_le_of_moments K hm hG measurableSet_Q hU
    fun x hx u hu τ hτ => seg_mem_bigCube K.radius_lt hx hu hτ
  rw [← ofReal_integral_eq_lintegral_ofReal hFi (Eventually.of_forall fun x => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hDU (Eventually.of_forall fun x => sq_nonneg _),
    ← ENNReal.ofReal_mul (by have := K.l1_nonneg; have := K.radius_pos; positivity),
    hDUe] at hL
  rw [ENNReal.ofReal_le_ofReal_iff (by have := K.l1_nonneg; have := K.radius_pos; positivity)]
    at hL
  rw [setIntegral_congr_fun measurableSet_Q fun x hx => by rw [hpe x hx]]
  calc ∫ x in Q (Fin n), F x
      ≤ K.l1 ^ 2 * (K.radius ^ m / (m - 1).factorial) ^ 2 * (3 ^ n * ∫ z in Q (Fin n), D z) := hL
    _ = _ := by ring

/-! ### Non-vacuity: symmetric trigonometric products of every parity -/

end Feec.Models.Cube.ParitySmoother
