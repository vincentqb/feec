module

public import Feec.FiniteElement.ShapeRegularSmoothing
public import Feec.FiniteElement.P1Global
public import Feec.FiniteElement.PolyComplex
public import Feec.FiniteElement.PolyInterpolation

/-!
# The global inverse estimate `‖d v‖ ≤ C h⁻¹ ‖v‖` on shape-regular, quasi-uniform meshes

On shape-regular meshes with `h ≤ h_T`, `h ‖d v‖ ≤ K ‖v‖` on the glued spaces of every admissible
sequence and of the Whitney forms ([Ciarlet2002], §3.2; [BrennerScott2008], §4.5).

## Main results

* `PolySeq.exists_mul_norm_d_le`: the global inverse estimate on the finite element subcomplex.
* `exists_mul_norm_glue_dPiecewise_le_whitney`: the global inverse estimate for the Whitney forms.

## References

* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.2
* [S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*][BrennerScott2008], §4.5

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory Set Finset

namespace Feec.FiniteElement

open Feec.Mesh Feec.Domain ExteriorFibre

variable {n : ℕ}

/-! ### The local inverse estimate for `d` -/

theorem abs_extDeriv_le_of_lipschitz {T : Affine.Simplex ℝ (Fin n → ℝ) n} {u : FormField n}
    {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior, ∀ s, |u x s - u x' s| ≤ K * ‖x - x'‖)
    {x : Fin n → ℝ} (hx : x ∈ interior T.closedInterior) (s : Finset (Fin n)) :
    |extDeriv u x s| ≤ n * K := by
  have hd : ∀ j (t : Finset (Fin n)), |partialDeriv j (fun y => u y t) x| ≤ K := fun j t => by
    have hf : ‖fderiv ℝ (fun y => u y t) x‖ ≤ K := by
      refine norm_fderiv_le_of_lip' ℝ hK ?_
      filter_upwards [mem_interior_iff_mem_nhds.1 hx] with y hy
      rw [Real.norm_eq_abs]
      exact hlip y hy x (interior_subset hx) t
    have he : ‖(Pi.single j (1 : ℝ) : Fin n → ℝ)‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
        by_cases h : i = j
        · subst h; simp
        · simp [h]
    rw [partialDeriv, ← Real.norm_eq_abs]
    refine ((fderiv ℝ (fun y => u y t) x).le_opNorm _).trans ?_
    nlinarith [norm_nonneg (fderiv ℝ (fun y => u y t) x)]
  rw [extDeriv_apply]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ s, |sgn j s * partialDeriv j (fun y => u y (s.erase j)) x|
      ≤ ∑ _j ∈ s, K := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_sgn, one_mul]; exact hd j _
    _ = #s * K := by rw [sum_const, nsmul_eq_mul]
    _ ≤ n * K := by
        gcongr
        exact_mod_cast (card_le_univ s).trans (by simp)

theorem diam_sq_mul_formL2Sq_extDeriv_le {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hh : 0 < diam T) {u : FormField n} (hdu : Continuous (extDeriv u)) {A : ℝ} (hA : 0 ≤ A)
    (hlip : ∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior, ∀ s,
      √(diam T) ^ n * diam T * |u x s - u x' s| ≤ A * ‖x - x'‖ * √(formL2Sq T.closedInterior u)) :
    diam T ^ 2 * formL2Sq T.closedInterior (extDeriv u) ≤
      (2 ^ n * n * A) ^ 2 * formL2Sq T.closedInterior u := by
  set h := diam T
  set L := formL2Sq T.closedInterior u
  have hL : 0 ≤ L := formL2Sq_nonneg T.isClosed_closedInterior.measurableSet u
  have hsh : 0 < √h ^ n * h := mul_pos (pow_pos (Real.sqrt_pos.2 hh) n) hh
  set K := A * √L / (√h ^ n * h)
  have hK : 0 ≤ K := by positivity
  have hlipK : ∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior, ∀ s,
      |u x s - u x' s| ≤ K * ‖x - x'‖ := fun x hx x' hx' s => by
    rw [div_mul_eq_mul_div, le_div_iff₀ hsh]
    have := hlip x hx x' hx' s
    nlinarith
  -- the pointwise bound on `T` (by continuity from the interior)
  have hint : ∀ s, ∀ x ∈ T.closedInterior, (extDeriv u x s) ^ 2 ≤ (n * K) ^ 2 := by
    intro s
    have hcl : closure (interior T.closedInterior) = T.closedInterior := by
      rw [(convex_closedInterior T).closure_interior_eq_closure_of_nonempty_interior
        (interior_closedInterior_nonempty T), T.isClosed_closedInterior.closure_eq]
    have hc : IsClosed {x | (extDeriv u x s) ^ 2 ≤ (n * K) ^ 2} :=
      isClosed_le (((continuous_apply s).comp hdu).pow 2) continuous_const
    rw [← hcl]
    refine closure_minimal (fun x hx => ?_) hc
    have := abs_extDeriv_le_of_lipschitz hK hlipK hx s
    have h0 : 0 ≤ (n : ℝ) * K := by positivity
    simp only [mem_ofPred_eq]
    nlinarith [abs_nonneg (extDeriv u x s), sq_abs (extDeriv u x s)]
  have hsum : formL2Sq T.closedInterior (extDeriv u) ≤ 2 ^ n * ((2 * h) ^ n * (n * K) ^ 2) := by
    unfold formL2Sq
    calc ∑ s, ∫ x in T.closedInterior, (extDeriv u x s) ^ 2
        ≤ ∑ _s : Finset (Fin n), (2 * h) ^ n * (n * K) ^ 2 := Finset.sum_le_sum fun s _ =>
          integral_closedInterior_le (((continuous_apply s).comp hdu).pow 2) (hint s)
            fun x => sq_nonneg _
      _ = _ := by
          rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hKsq : (√h ^ n * h) ^ 2 * K ^ 2 = A ^ 2 * L := by
    rw [← mul_pow, show √h ^ n * h * K = A * √L by simp only [K]; field_simp [hsh.ne'], mul_pow,
      Real.sq_sqrt hL]
  have hpow : (√h ^ n) ^ 2 = h ^ n := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hh.le]
  calc h ^ 2 * formL2Sq T.closedInterior (extDeriv u)
      ≤ h ^ 2 * (2 ^ n * ((2 * h) ^ n * (n * K) ^ 2)) := by gcongr
    _ = (2 ^ n * 2 ^ n * n ^ 2) * ((√h ^ n * h) ^ 2 * K ^ 2) := by
        rw [mul_pow, mul_pow (√h ^ n), hpow]; ring
    _ = (2 ^ n * n * A) ^ 2 * L := by rw [hKsq]; ring

/-! ### The `L²` norm of glued fields -/

namespace LocalElement

variable (E : LocalElement n) (M : SimplicialMesh n)

theorem norm_sq_glue (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {j : ℤ}
    (hj : 0 ≤ j) (u : E.Piecewise M j.toNat) :
    ‖E.glue M j u‖ ^ 2 = ∑ T ∈ M.simplices, formL2Sq T.closedInterior (E.extendPW M u T) := by
  rw [← real_inner_self_eq_norm_sq]
  rw [show E.glue M j u = pieceL2 M M.domain (fun T => formComp (k := j) (E.extendPW M u T))
    (fun T hT s => continuous_formComp (E.contDiff_extendPW M u hT).continuous s) from rfl,
    inner_pieceL2 M hint]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [← sum_formIdx_integral_sq (Int.toNat_of_nonneg hj) (S := T.closedInterior)
    (E.isDeg_extendPW M u hT)]
  refine Finset.sum_congr rfl fun s _ => integral_congr_ae (Filter.Eventually.of_forall
    fun x => ?_)
  simp [formComp, sq]

theorem mul_norm_glue_dPiecewise_le (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain)
    {k : ℕ} {A h : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hdiam : ∀ T ∈ M.simplices, h ≤ diam T)
    (hloc : ∀ T ∈ M.simplices, ∀ u ∈ E.space T k, ∀ x ∈ T.closedInterior,
      ∀ x' ∈ T.closedInterior, ∀ s, √(diam T) ^ n * diam T * |u x s - u x' s| ≤
        A * ‖x - x'‖ * √(formL2Sq T.closedInterior u))
    (u : E.Piecewise M k) :
    h * ‖E.glue M ((k : ℤ) + 1) (E.dPiecewise M k u)‖ ≤ 2 ^ n * n * A * ‖E.glue M k u‖ := by
  have hsq : (h * ‖E.glue M ((k : ℤ) + 1) (E.dPiecewise M k u)‖) ^ 2 ≤
      (2 ^ n * n * A * ‖E.glue M k u‖) ^ 2 := by
    rw [mul_pow, mul_pow (2 ^ n * n * A), norm_sq_glue E M hint (j := (k : ℤ) + 1) (by omega),
      norm_sq_glue E M hint (j := (k : ℤ)) (by omega), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun T hT => ?_
    have hT0 : 0 < diam T := hh.trans_le (hdiam T hT)
    have e : E.extendPW M (E.dPiecewise M k u) T = extDeriv (E.extendPW M u T) := by
      rw [E.extendPW_of_mem M _ hT, E.extendPW_of_mem M _ hT]; rfl
    have hcont : Continuous (extDeriv (E.extendPW M u T)) := by
      rw [← e]; exact (E.contDiff_extendPW M _ hT).continuous
    have hmem : E.extendPW M u T ∈ E.space T k := by
      rw [E.extendPW_of_mem M _ hT]; exact (u ⟨T, hT⟩).2
    have hloc' := diam_sq_mul_formL2Sq_extDeriv_le hT0 hcont hA (hloc T hT _ hmem)
    rw [e]
    have h0 : 0 ≤ formL2Sq T.closedInterior (extDeriv (E.extendPW M u T)) :=
      formL2Sq_nonneg T.isClosed_closedInterior.measurableSet _
    have hh2 : h ^ 2 ≤ diam T ^ 2 := pow_le_pow_left₀ hh.le (hdiam T hT) 2
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq

end LocalElement

/-! ### Instances: admissible sequences and Whitney forms -/

theorem PolySeq.exists_mul_norm_glue_dPiecewise_le (S : PolySeq) (k : ℕ) {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ K, 0 ≤ K ∧ ∀ (M : SimplicialMesh n),
      (∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) →
      IsShapeRegular (M.simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)) C c →
      ∀ {h : ℝ}, 0 < h → (∀ T ∈ M.simplices, h ≤ diam T) → ∀ u : (polyElement n S).Piecewise M k,
        h * ‖(polyElement n S).glue M ((k : ℤ) + 1) ((polyElement n S).dPiecewise M k u)‖ ≤
          K * ‖(polyElement n S).glue M k u‖ := by
  obtain ⟨A, hA, hloc⟩ := exists_inverse_bound_of_le_polySpace (S.space_le_polySpace k)
    (fun B b u hu => S.affinePullback_mem_space B b k hu) hC hc
  refine ⟨2 ^ n * n * A, by positivity, fun M hint hS h hh hdiam u => ?_⟩
  refine (polyElement n S).mul_norm_glue_dPiecewise_le M hint hA hh hdiam
    (fun T hT w hw x hx x' hx' s => ?_) u
  have hT0 : 0 < diam T := hh.trans_le (hdiam T hT)
  refine le_trans ?_ ((hloc hS T hT hT0 w hw).2 x hx x' hx')
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Real.norm_eq_abs, ← Pi.sub_apply]
  exact norm_le_pi_norm (w x - w x') s

/-- The global inverse estimate for the Whitney forms: `h ‖glue (d u)‖ ≤ K ‖glue u‖` on every mesh,
shape regular with constants `C, c`, whose open simplices lie in its domain and have `h ≤ h_T`. -/
theorem exists_mul_norm_glue_dPiecewise_le_whitney (k : ℕ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ K, 0 ≤ K ∧ ∀ (M : SimplicialMesh n),
      (∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) →
      IsShapeRegular (M.simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)) C c →
      ∀ {h : ℝ}, 0 < h → (∀ T ∈ M.simplices, h ≤ diam T) → ∀ u : (whitneyElement n).Piecewise M k,
        h * ‖(whitneyElement n).glue M ((k : ℤ) + 1) ((whitneyElement n).dPiecewise M k u)‖ ≤
          K * ‖(whitneyElement n).glue M k u‖ := by
  obtain ⟨A, hA, hloc⟩ := exists_inverse_bound_p1MinusForms (n := n) k hC hc
  refine ⟨2 ^ n * n * A, by positivity, fun M hint hS h hh hdiam u => ?_⟩
  refine (whitneyElement n).mul_norm_glue_dPiecewise_le M hint hA hh hdiam
    (fun T hT w hw x hx x' hx' s => ?_) u
  exact (hloc hS T hT (hh.trans_le (hdiam T hT)) w (whitneySpace_le_p1MinusForms _ k hw)).2 x hx
    x' hx' s

/-- The global inverse estimate on the subcomplex of an admissible sequence: `h ‖d_max v‖ ≤ K ‖v‖`
on every shape-regular mesh of an open domain whose open simplices lie in it and have `h ≤ h_T`. -/
theorem PolySeq.exists_mul_norm_d_le [NeZero n] (S : PolySeq) (k : ℕ) {C c : ℝ} (hC : 0 ≤ C)
    (hc : 0 < c) :
    ∃ K, 0 ≤ K ∧ ∀ (M : SimplicialMesh n) (hΩ : IsOpen M.domain),
      (∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) →
      IsShapeRegular (M.simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)) C c →
      ∀ {h : ℝ}, 0 < h → (∀ T ∈ M.simplices, h ≤ diam T) →
        ∀ v : ((extDerivOp ℝ n k).maximal M.domain).domain,
          (v : L2F ℝ M.domain (formIdx n k)) ∈ (S.subcomplex M hΩ).V k →
          h * ‖(extDerivOp ℝ n k).maximal M.domain v‖ ≤
            K * ‖(v : L2F ℝ M.domain (formIdx n k))‖ := by
  obtain ⟨K, hK, hb⟩ := S.exists_mul_norm_glue_dPiecewise_le k hC hc
  refine ⟨K, hK, fun M hΩ hint hS h hh hdiam v hv => ?_⟩
  obtain ⟨u, hu⟩ := hv
  obtain ⟨hd, hval⟩ := (polyElement n S).glue_mem_maximal M hΩ k u
  have hvu : v = ⟨_, hd⟩ := Subtype.ext hu.symm
  rw [hvu, hval]
  exact hb M hint hS hh hdiam _

end Feec.FiniteElement
