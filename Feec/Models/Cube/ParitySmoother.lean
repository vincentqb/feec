module

public import Feec.Models.Cube.DeRhamPartialIdent
public import Feec.Domain.Mollify
public import Feec.FiniteElement.WeakSymmetryMaps
public import Feec.FiniteElement.InverseEstimate
public import Feec.Domain.StarShapedSmoothing
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Parity smoother (draft)
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

theorem triW_le_add (x y : ℝ) : triW y ≤ |x - y| + triW x :=
  calc triW y ≤ |y - round x| := triW_le y (round x)
    _ = |(y - x) + (x - round x)| := by ring_nf
    _ ≤ |y - x| + |x - round x| := abs_add_le _ _
    _ = |x - y| + triW x := by rw [abs_sub_comm]; rfl

theorem abs_triW_sub_triW_le (x y : ℝ) : |triW x - triW y| ≤ |x - y| := by
  have h1 := triW_le_add x y
  have h2 := triW_le_add y x
  rw [abs_sub_comm y x] at h2
  rw [abs_le]; constructor <;> linarith

theorem triW_mem_Icc (x : ℝ) : triW x ∈ Icc (0 : ℝ) (1 / 2) :=
  ⟨abs_nonneg _, abs_sub_round x⟩

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

theorem coe_pieceEquiv (p : Fin n → Fin 3) : ⇑(pieceEquiv p) = pieceMap p := rfl

theorem measurableEmbedding_pieceMap (p : Fin n → Fin 3) : MeasurableEmbedding (pieceMap p) :=
  (pieceEquiv p).measurableEmbedding

theorem measurePreserving_pieceMap (p : Fin n → Fin 3) :
    MeasurePreserving (pieceMap p) (volume : Measure (Fin n → ℝ)) volume :=
  measurePreserving_pi _ _ fun j => measurePreserving_piece (p j)

theorem pieceMap_mem_Q_iff (p : Fin n → Fin 3) (x : Fin n → ℝ) :
    pieceMap p x ∈ Q (Fin n) ↔ ∀ j, x j ∈ pieceIoo (p j) := by
  rw [mem_Q]; exact forall_congr' fun j => piece_mem_Ioo_iff (p j) (x j)

theorem mem_Q_iff' {z : Fin n → ℝ} : z ∈ Q (Fin n) ↔ ∀ j, z j ∈ Ioo (0 : ℝ) (1 / 2) := mem_Q

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

/-! ### The parity extension -/

/-- A **parity vector**: `c j = ± 1` for every direction. -/
def IsParity (c : Fin n → ℝ) : Prop := ∀ j, c j = 1 ∨ c j = -1

theorem IsParity.mul_self {c : Fin n → ℝ} (hc : IsParity c) (j : Fin n) : c j * c j = 1 := by
  rcases hc j with h | h <;> rw [h] <;> norm_num

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

theorem parExt_of_mem_Q {z : Fin n → ℝ} (hz : z ∈ Q (Fin n)) (c : Fin n → ℝ)
    (f : (Fin n → ℝ) → ℝ) : parExt c f z = f z := by
  have h := parExt_pieceMap hz c f (fun _ => 1)
  have e : pieceMap (fun _ : Fin n => (1 : Fin 3)) z = z := funext fun j => rfl
  rw [e] at h
  rw [h]; simp [pieceSign, pieceSgn]

theorem abs_pieceSgn {c : ℝ} (hc : c = 1 ∨ c = -1) (q : Fin 3) : |pieceSgn c q| = 1 := by
  unfold pieceSgn; split_ifs <;> rcases hc with h | h <;> simp [h]

theorem abs_pieceSign {c : Fin n → ℝ} (hc : IsParity c) (p : Fin n → Fin 3) :
    |pieceSign c p| = 1 := by
  rw [pieceSign, Finset.abs_prod]
  exact Finset.prod_eq_one fun j _ => abs_pieceSgn (hc j) (p j)

theorem pieceSign_sq {c : Fin n → ℝ} (hc : IsParity c) (p : Fin n → Fin 3) :
    pieceSign c p ^ 2 = 1 := by
  rw [← sq_abs, abs_pieceSign hc]; norm_num

theorem abs_extSgn {c : Fin n → ℝ} (hc : IsParity c) (x : Fin n → ℝ) : |extSgn c x| = 1 := by
  rw [extSgn, Finset.abs_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  unfold parSgn; split_ifs <;> rcases hc j with h | h <;> simp [h]

theorem abs_parExt {c : Fin n → ℝ} (hc : IsParity c) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    |parExt c f x| = |f (foldPt x)| := by
  rw [parExt, abs_mul, abs_extSgn hc, one_mul]

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

/-- **A continuous periodic function is bounded.** -/
theorem exists_bound_of_periodic {F : (Fin n → ℝ) → ℝ} (hF : Continuous F)
    (hper : ∀ x (m : Fin n → ℤ), F (x + fun j => (m j : ℝ)) = F x) : ∃ M, ∀ x, |F x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨M, fun x => ?_⟩
  have hmem : (x - fun j => ((⌊x j⌋ : ℤ) : ℝ)) ∈ univ.pi fun _ => Icc (0 : ℝ) 1 := by
    intro j _
    simp only [Pi.sub_apply, Set.mem_Icc]
    exact ⟨sub_nonneg.2 (Int.floor_le _), by linarith [Int.lt_floor_add_one (x j)]⟩
  have h := hM _ hmem
  rw [Real.norm_eq_abs, ← hper _ fun j => ⌊x j⌋, sub_add_cancel] at h
  exact h

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

/-- The smoothed extension is bounded. -/
theorem exists_bound_smoothFun {f : (Fin n → ℝ) → ℝ} (hf : IntegrableOn f (Q (Fin n))) :
    ∃ M, ∀ y, |smoothFun ρ c f y| ≤ M :=
  exists_bound_of_periodic (contDiff_smoothFun ρ c hf).continuous (smoothFun_add_intCast ρ c f)

/-- The first partial derivatives of the smoothed extension are bounded. -/
theorem exists_bound_fderiv_smoothFun {f : (Fin n → ℝ) → ℝ} (hf : IntegrableOn f (Q (Fin n))) :
    ∃ L, 0 ≤ L ∧ ∀ j y, |fderiv ℝ (smoothFun ρ c f) y (Pi.single j 1)| ≤ L := by
  have hb : ∀ j : Fin n, ∃ M, ∀ y, |fderiv ℝ (smoothFun ρ c f) y (Pi.single j 1)| ≤ M := by
    intro j
    have hcont : Continuous fun y => fderiv ℝ (smoothFun ρ c f) y (Pi.single j 1) :=
      ((contDiff_smoothFun ρ c hf).continuous_fderiv (by simp)).clm_apply continuous_const
    refine exists_bound_of_periodic hcont fun y m => ?_
    rw [smoothFun, fderiv_convolution_apply ρ.isTest (locallyIntegrable_parExt c hf),
      fderiv_convolution_apply ρ.isTest (locallyIntegrable_parExt c hf)]
    exact convolution_add_intCast (fun x m => parExt_add_intCast c f x m) y m
  choose M hM using hb
  refine ⟨∑ j, max (M j) 0, Finset.sum_nonneg fun j _ => le_max_right _ _, fun j y => ?_⟩
  exact (hM j y).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (f := fun j => max (M j) 0) (fun j _ => le_max_right _ _)
      (Finset.mem_univ j)))

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

theorem pcJ_eq_pvec (J s : Finset (Fin n)) (j : Fin n) :
    DeRhamIdent.pcJ J s j = (pvec J s j : ℂ) := by
  unfold DeRhamIdent.pcJ DeRham.mixedSign DeRham.reflSign pvec; split_ifs <;> simp

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
    have h1 : ‖(Pi.single j 1 : Fin n → ℝ)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
      by_cases h : i = j
      · subst h; simp
      · simp [h]
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
      obtain h | h : c i = 1 ∨ c i = -1 := isParity_pvec J t.1 i
      · rw [h]; norm_num
      · rw [h]; norm_num
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
`3^{n/2}` (`norm_scalarSmooth_le`). -/
def scalarSmooth (c : Fin n → ℝ) (hc : IsParity c) : L2 ℝ (Q (Fin n)) →L[ℝ] L2 ℝ (Q (Fin n)) :=
  (scalarSmoothₗ ρ c).mkContinuous (√(3 ^ n)) (norm_scalarSmoothₗ_le ρ hc)

theorem scalarSmooth_apply (c : Fin n → ℝ) (hc : IsParity c) (f : L2 ℝ (Q (Fin n))) :
    scalarSmooth ρ c hc f = (memLp_smoothFun ρ c f).toLp _ := rfl

theorem coeFn_scalarSmooth (c : Fin n → ℝ) (hc : IsParity c) (f : L2 ℝ (Q (Fin n))) :
    (scalarSmooth ρ c hc f : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict (Q (Fin n))]
      smoothFun ρ c (f : (Fin n → ℝ) → ℝ) :=
  MemLp.coeFn_toLp (memLp_smoothFun ρ c f)

theorem norm_scalarSmooth_le (c : Fin n → ℝ) (hc : IsParity c) (f : L2 ℝ (Q (Fin n))) :
    ‖scalarSmooth ρ c hc f‖ ≤ √(3 ^ n) * ‖f‖ :=
  norm_scalarSmoothₗ_le ρ hc f

theorem scalarSmooth_congr {c c' : Fin n → ℝ} (hc : IsParity c) (hc' : IsParity c') (h : c = c') :
    scalarSmooth ρ c hc = scalarSmooth ρ c' hc' := by
  subst h; rfl

variable (J : Finset (Fin n))

/-- The parity smoother on `k`-forms of the class `J`, as a linear map. -/
def paritySmoothₗ (k : ℤ) : L2F ℝ (Q (Fin n)) (formIdx n k) →ₗ[ℝ] L2F ℝ (Q (Fin n)) (formIdx n k) where
  toFun u := WithLp.toLp 2 fun s => scalarSmooth ρ (pvec J s.1) (isParity_pvec J s.1) (u s)
  map_add' u v := by
    refine (WithLp.ext_iff 2).2 (funext fun s => ?_)
    simp only [PiLp.add_apply, map_add]
  map_smul' a u := by
    refine (WithLp.ext_iff 2).2 (funext fun s => ?_)
    simp only [PiLp.smul_apply, map_smul, RingHom.id_apply]

theorem norm_paritySmoothₗ_le (k : ℤ) (u : L2F ℝ (Q (Fin n)) (formIdx n k)) :
    ‖paritySmoothₗ ρ J k u‖ ≤ √(3 ^ n) * ‖u‖ :=
  L2F.norm_le_of_forall (by positivity) fun s =>
    norm_scalarSmooth_le ρ (pvec J s.1) (isParity_pvec J s.1) (u s)

/-- **The parity smoother** `R^J_ρ u = (ρ ⋆ ext_J u)|_Q` on `L²(Q; Λᵏ)`: componentwise the
smoothed parity extension with the parities `c(J, s)` of the class `J` (`pvec`). It is bounded by
`3^{n/2}` (`norm_paritySmooth_le`), smooth and in the class `J`, hence in `D(d_J)`
(`paritySmooth_mem_dPart`), and commutes with `d_J` (`dPart_paritySmooth`). -/
def paritySmooth (k : ℤ) : L2F ℝ (Q (Fin n)) (formIdx n k) →L[ℝ] L2F ℝ (Q (Fin n)) (formIdx n k) :=
  (paritySmoothₗ ρ J k).mkContinuous (√(3 ^ n)) (norm_paritySmoothₗ_le ρ J k)

theorem paritySmooth_apply (k : ℤ) (u : L2F ℝ (Q (Fin n)) (formIdx n k)) (s : formIdx n k) :
    paritySmooth ρ J k u s = scalarSmooth ρ (pvec J s.1) (isParity_pvec J s.1) (u s) := rfl

/-- **`L²` bound of the parity smoother**: `‖R u‖ ≤ 3^{n/2} ‖u‖`. -/
theorem norm_paritySmooth_le (k : ℤ) (u : L2F ℝ (Q (Fin n)) (formIdx n k)) :
    ‖paritySmooth ρ J k u‖ ≤ √(3 ^ n) * ‖u‖ :=
  norm_paritySmoothₗ_le ρ J k u

/-- The smoothed components `ψ_s = ρ ⋆ ext_{c(J,s)} u_s`. -/
def smoothComp {k : ℤ} (u : L2F ℝ (Q (Fin n)) (formIdx n k)) (s : formIdx n k) :
    (Fin n → ℝ) → ℝ :=
  smoothFun ρ (pvec J s.1) ((u s : L2 ℝ (Q (Fin n))) : (Fin n → ℝ) → ℝ)

theorem memLp_smoothComp {k : ℤ} (u : L2F ℝ (Q (Fin n)) (formIdx n k)) (s : formIdx n k) :
    MemLp (smoothComp ρ J u s) 2 (volume.restrict (Q (Fin n))) :=
  memLp_smoothFun ρ (pvec J s.1) (u s)

theorem paritySmooth_eq_toL2F {k : ℤ} (u : L2F ℝ (Q (Fin n)) (formIdx n k)) :
    paritySmooth ρ J k u = toL2F (memLp_smoothComp ρ J u) :=
  PiLp.ext fun s => by rw [paritySmooth_apply, scalarSmooth_apply]; rfl

theorem contDiff_smoothComp {k : ℤ} (u : L2F ℝ (Q (Fin n)) (formIdx n k)) (s : formIdx n k) :
    ContDiff ℝ ∞ (smoothComp ρ J u s) :=
  contDiff_smoothFun ρ _ (integrableOn_L2 _)

/-- **The smoothed field is in the class `J`**: its components have the parities `c(J, s)` about
every face of `Q` (and are `1`-periodic). -/
theorem smoothComp_coordRefl {k : ℤ} (u : L2F ℝ (Q (Fin n)) (formIdx n k)) (s : formIdx n k)
    (j : Fin n) (y : Fin n → ℝ) :
    smoothComp ρ J u s (coordRefl j y) = pvec J s.1 j * smoothComp ρ J u s y :=
  smoothFun_coordRefl ρ (isParity_pvec J s.1) _ j y

theorem smoothComp_update_one_sub {k : ℤ} (u : L2F ℝ (Q (Fin n)) (formIdx n k))
    (s : formIdx n k) (j : Fin n) (y : Fin n → ℝ) :
    smoothComp ρ J u s (Function.update y j (1 - y j)) = pvec J s.1 j * smoothComp ρ J u s y :=
  smoothFun_update_one_sub ρ (isParity_pvec J s.1) _ j y

/-- **The tangential components of the smoothed field vanish on the faces normal to `J`.** -/
theorem smoothComp_eq_zero_of_tangential {k : ℤ} (u : L2F ℝ (Q (Fin n)) (formIdx n k))
    (s : formIdx n k) {j : Fin n} (hjJ : j ∈ J) (hjs : j ∉ s.1) {y : Fin n → ℝ}
    (hy : y j = 0 ∨ y j = 1 / 2) : smoothComp ρ J u s y = 0 :=
  smoothFun_eq_zero ρ (isParity_pvec J s.1) _ (pvec_of_mem_of_notMem hjJ hjs) hy

/-- **The normal components of the smoothed field vanish on the faces not normal to `J`.** -/
theorem smoothComp_eq_zero_of_normal {k : ℤ} (u : L2F ℝ (Q (Fin n)) (formIdx n k))
    (s : formIdx n k) {j : Fin n} (hjJ : j ∉ J) (hjs : j ∈ s.1) {y : Fin n → ℝ}
    (hy : y j = 0 ∨ y j = 1 / 2) : smoothComp ρ J u s y = 0 :=
  smoothFun_eq_zero ρ (isParity_pvec J s.1) _ (pvec_of_notMem_of_mem hjJ hjs) hy

theorem exists_graph_paritySmooth {k : ℤ} (u : L2F ℝ (Q (Fin n)) (formIdx n k)) :
    ∃ hdψ : ∀ t, MemLp ((extDerivOp ℝ n k).apply (smoothComp ρ J u) t) 2
        (volume.restrict (Q (Fin n))),
      (paritySmooth ρ J k u, toL2F hdψ) ∈ (DeRhamIdent.dPart (Q (Fin n)) J k).graph := by
  have hb : ∀ s, ∃ M, ∀ y, |smoothComp ρ J u s y| ≤ M := fun s =>
    exists_bound_smoothFun ρ _ (integrableOn_L2 _)
  choose M hM using hb
  have hd : ∀ s, ∃ L, 0 ≤ L ∧ ∀ j y, |fderiv ℝ (smoothComp ρ J u s) y (Pi.single j 1)| ≤ L :=
    fun s => exists_bound_fderiv_smoothFun ρ _ (integrableOn_L2 _)
  choose L hL0 hL using hd
  have hMs : ∀ s y, |smoothComp ρ J u s y| ≤ ∑ s, max (M s) 0 := fun s y =>
    (hM s y).trans ((le_max_left _ _).trans (Finset.single_le_sum (f := fun s => max (M s) 0)
      (fun s _ => le_max_right _ _) (Finset.mem_univ s)))
  have hLs : ∀ s j y, |fderiv ℝ (smoothComp ρ J u s) y (Pi.single j 1)| ≤ ∑ s, L s :=
    fun s j y => (hL s j y).trans (Finset.single_le_sum (f := L) (fun s _ => hL0 s)
      (Finset.mem_univ s))
  obtain ⟨hψL, hdψL, hg⟩ := DeRhamIdent.exists_mem_dPart_of_smooth (J := J)
    (fun s => contDiff_smoothComp ρ J u s) hMs (Finset.sum_nonneg fun s _ => hL0 s) hLs
    (fun s j hjJ hjs y hy => smoothComp_eq_zero_of_tangential ρ J u s hjJ hjs hy)
  rw [paritySmooth_eq_toL2F]
  exact ⟨hdψL, hg⟩

/-- **`R u ∈ D(d_J)`.** -/
theorem paritySmooth_mem_dPart (k : ℤ) (u : L2F ℝ (Q (Fin n)) (formIdx n k)) :
    paritySmooth ρ J k u ∈ (DeRhamIdent.dPart (Q (Fin n)) J k).domain := by
  obtain ⟨hdψ, hg⟩ := exists_graph_paritySmooth ρ J u
  obtain ⟨v, hv, -⟩ := (LinearPMap.mem_graph_iff _).1 hg
  have h := v.2
  rwa [hv] at h

/-- **The parity smoother commutes with `d_J`**: `d_J (R u) = R (d_J u)` for `u ∈ D(d_J)` (no
chain-rule factor: no dilation is involved). -/
theorem dPart_paritySmooth (k : ℕ) (u : (DeRhamIdent.dPart (Q (Fin n)) J (k : ℤ)).domain) :
    DeRhamIdent.dPart (Q (Fin n)) J (k : ℤ) ⟨_, paritySmooth_mem_dPart ρ J k u⟩ =
      paritySmooth ρ J ((k : ℤ) + 1) (DeRhamIdent.dPart (Q (Fin n)) J (k : ℤ) u) := by
  obtain ⟨hdψ, hg⟩ := exists_graph_paritySmooth ρ J (u : L2F ℝ (Q (Fin n)) (formIdx n k))
  obtain ⟨v, hv, hvd⟩ := (LinearPMap.mem_graph_iff _).1 hg
  have hv' : v = ⟨_, paritySmooth_mem_dPart ρ J k u⟩ := Subtype.ext hv
  rw [← hv', hvd]
  refine (WithLp.ext_iff 2).2 (funext fun t => ?_)
  change (hdψ t).toLp _ = (memLp_smoothFun ρ (pvec J t.1) _).toLp _
  refine MemLp.toLp_congr _ _ (ae_restrict_of_forall_mem measurableSet_Q fun y hy => ?_)
  rw [extDerivOp_apply]
  exact extD_smoothFun_eq ρ J k u t fun j => Ioo_subset_Icc_self (mem_Q.1 hy j)

end Operator

/-! ### The weak-symmetry maps `S⁰`, `S¹` -/

section WeakSymmetry

open Feec.FiniteElement (wsL2 wsCoeff wsL2_apply wsCoeff_eq)

variable (ρ : ReflKernel n)

/-- **The parity smoother commutes with the algebraic BGG maps** `S v = Σₐ dxₐ ∧ vₐ`
(`Feec.FiniteElement.wsL2`; `S⁰` for `k = 0`, `S¹` for `k = 1`) as soon as the classes are
compatible: every component `(a, r)` of the vector row that enters the component `t` of `S v`
has the parity vector of `t`. One smoother then serves both rows of the BGG complex. -/
theorem wsL2_paritySmooth (k : ℤ) (J : Finset (Fin n)) (J' : Fin n → Finset (Fin n))
    (hJ' : ∀ (t : formIdx n (k + 1)) (p : Fin n × formIdx n k), wsCoeff k t p ≠ 0 →
      pvec (J' p.1) p.2.1 = pvec J t.1)
    (v : PiLp 2 fun _ : Fin n => L2F ℝ (Q (Fin n)) (formIdx n k)) :
    wsL2 k (WithLp.toLp 2 fun a => paritySmooth ρ (J' a) k (v a)) =
      paritySmooth ρ J (k + 1) (wsL2 k v) := by
  refine PiLp.ext fun t => ?_
  rw [wsL2_apply, paritySmooth_apply, wsL2_apply, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul]
  by_cases hp : wsCoeff k t p = 0
  · simp [hp]
  · congr 1
    change paritySmooth ρ (J' p.1) k (v p.1) p.2 = _
    rw [paritySmooth_apply, scalarSmooth_congr ρ _ _ (hJ' t p hp)]

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

/-- **The compatible classes for `S`**: the rows `a` in the classes `J ∆ {a}`. For `k = 0`
(`S⁰ = I` on vector proxies) the component `ψₐ` of a vector field in the class `J`, as a
`0`-form, lies in the class `J ∆ {a}`. -/
theorem wsL2_paritySmooth_symmDiff (k : ℤ) (J : Finset (Fin n))
    (v : PiLp 2 fun _ : Fin n => L2F ℝ (Q (Fin n)) (formIdx n k)) :
    wsL2 k (WithLp.toLp 2 fun a => paritySmooth ρ (symmDiff J {a}) k (v a)) =
      paritySmooth ρ J (k + 1) (wsL2 k v) := by
  refine wsL2_paritySmooth ρ k J _ (fun t p hp => ?_) v
  rw [wsCoeff_eq] at hp
  split_ifs at hp with h
  · rw [← h.2, pvec_symmDiff_erase J h.1]
  · exact absurd rfl hp

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

end Feec.Models.Cube.ParitySmoother
