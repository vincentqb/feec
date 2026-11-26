module

public import Feec.Models.Cube.DeRhamPartial
public import Feec.Models.Cube.DeRhamIdentPoincare

/-!
# The de Rham complex of `(0, ½)ⁿ` with vanishing traces on part of the boundary

The complex `HΛ_J(Q)` with vanishing tangential traces on the faces normal to `J` ([AFW2010], §4.3;
[Arnold2018], Ch. 6), its identification with the mixed parity class, and its Hodge theory.

## Main results

* `greenForJ_iff`: Green's identity characterizes `D(d_J)`.
* `HQpart_eq_compress`: `HΛ_J(Q)` is a compression of the torus window.
* `Hpart_harmonic_card`, `finrank_Hpart_cohomology`: `ℌ^{|J|} = ℝ · dx_J`, `dim Hᵏ = [k = |J|]`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate ContDiff Topology
open Set MeasureTheory Filter UnitAddTorus Feec.Fourier.TorusWeak Finset LinearPMap

@[expose] public noncomputable section

namespace Feec.Models.Cube.DeRhamIdent

open Geometry MirrorExt
open Feec.Fourier (Reflection entryConj entryConj_apply conjLp coeFn_conjLp symLp coeFn_symLp)
open Feec.Domain (formIdx formExt formExt_of_card formExt_val extDerivOp L2F L2 toL2F)
open Feec.Fourier.Exterior (Form Lam)

variable {n : ℕ}

/-! ### The parity vectors of the mixed class -/

/-- The parity vector of the coefficient of `dx_s` in the mixed class `J`, `c_j = ε_j ε_j(s)`. -/
def pcJ (J s : Finset (Fin n)) (j : Fin n) : ℂ := DeRham.mixedSign J j * DeRham.reflSign j s

/-- The parity vector of a component of a `k`-form in the mixed class `J`. -/
def pcJF (J : Finset (Fin n)) {k : ℤ} (s : formIdx n k) : Fin n → ℂ := pcJ J s.1

theorem pcJ_mul_self (J s : Finset (Fin n)) (j : Fin n) : pcJ J s j * pcJ J s j = 1 := by
  unfold pcJ DeRham.mixedSign DeRham.reflSign; split_ifs <;> norm_num

theorem pcJF_mul_self (J : Finset (Fin n)) {k : ℤ} (s : formIdx n k) (j : Fin n) :
    pcJF J s j * pcJF J s j = 1 := pcJ_mul_self J s.1 j

theorem conj_pcJF (J : Finset (Fin n)) {k : ℤ} (s : formIdx n k) (j : Fin n) :
    conj (pcJF J s j) = pcJF J s j := by
  unfold pcJF pcJ DeRham.mixedSign DeRham.reflSign; split_ifs <;> simp

theorem update_pcJ_erase (J : Finset (Fin n)) {s : Finset (Fin n)} {j : Fin n} (hj : j ∈ s) :
    Function.update (pcJ J s) j (-pcJ J s j) = pcJ J (s.erase j) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp [pcJ, DeRham.reflSign, hj]
  · rw [Function.update_of_ne hi]
    simp [pcJ, DeRham.reflSign, Finset.mem_erase, hi]

theorem pcJ_univ : pcJ (Finset.univ : Finset (Fin n)) = pcF true := by
  funext s j; simp [pcJ, pcF]

/-! ### The parity extension in the mixed class -/

/-- **The parity extension of real `k`-forms on `Q`, mixed class `J`**, on the Fourier side. -/
def JfJ (J : Finset (Fin n)) (k : ℕ) : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)) →L[ℝ]
    Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)) :=
  JR (pcJF_mul_self J)

theorem JfJ_apply (J : Finset (Fin n)) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    JfJ J k u = JR (pcJF_mul_self J) u := rfl

theorem JR_congr {d P : Type*} [Fintype d] [DecidableEq d] [Fintype P] {c c' : P → d → ℂ}
    (h : c = c') (hc : ∀ p j, c p j * c p j = 1) (hc' : ∀ p j, c' p j * c' p j = 1) :
    JR hc = JR hc' := by
  subst h; rfl

theorem JfJ_univ (k : ℕ) : JfJ (Finset.univ : Finset (Fin n)) k = Jf true k := by
  unfold JfJ Jf
  rw [JR_congr (show (fun s : formIdx n (k : ℤ) => pcJF Finset.univ s) = fun s => pc true s from
    funext fun s => by rw [pcJF, pcJ_univ]; rfl) _ (pc_mul_self true)]

theorem coeff_JfJ (J : Finset (Fin n)) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)))
    (m : Fin n → ℤ) (t : formIdx n (k : ℤ)) :
    (JfJ J k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m t =
      ∫ y in Q (Fin n), (((u t : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) *
        fold (pcJ J t.1) (mFourier (-m)) y := by
  rw [JfJ_apply, coeff_JR]
  rfl

theorem Jinvf_JfJ (J : Finset (Fin n)) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    Jinvf k (JfJ J k u) = u :=
  Jinv_JR _ u

theorem injective_JfJ (J : Finset (Fin n)) (k : ℕ) : Function.Injective (JfJ (n := n) J k) :=
  fun u v h => by rw [← Jinvf_JfJ J k u, h, Jinvf_JfJ]

theorem inner_JfJ (J : Finset (Fin n)) (k : ℕ) (u v : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    ⟪JfJ J k u, JfJ J k v⟫_ℝ = 2 ^ n * ⟪u, v⟫_ℝ := by
  rw [MeasureTheory.L2.real_inner_eq_re_inner EuclideanSpace.real_inner_eq_re_inner, JfJ_apply,
    JfJ_apply, ← MeasureTheory.L2.real_inner_eq_re_inner EuclideanSpace.real_inner_eq_re_inner,
    inner_JR, Fintype.card_fin]

/-- **The real coefficient sequences of the mixed class `J`.** -/
def RealParJ (J : Finset (Fin n)) (k : ℕ)
    (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))) : Prop :=
  (∀ m t, (x : (Fin n → ℤ) → Form ℂ (Fin n) k) (-m) t =
      conj ((x : (Fin n → ℤ) → Form ℂ (Fin n) k) m t)) ∧
    ∀ j m t, (x : (Fin n → ℤ) → Form ℂ (Fin n) k) (Fourier.Torus.flipAt j m) t =
      DeRham.mixedSign J j * DeRham.reflSign j t.1 * (x : (Fin n → ℤ) → Form ℂ (Fin n) k) m t

theorem JfJ_realParJ (J : Finset (Fin n)) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    RealParJ J k (JfJ J k u) := by
  refine ⟨fun m t => ?_, fun j m t => ?_⟩
  · rw [JfJ_apply]
    exact JR_isReal (pcJF_mul_self J) (conj_pcJF J) u m _
  · rw [JfJ_apply]
    exact (mem_fieldParity_iff.1 (JR_mem_fieldParity (pcJF_mul_self J) u)) j m _

theorem JfJ_Jinvf {J : Finset (Fin n)} {k : ℕ}
    {x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))} (hx : RealParJ J k x) :
    JfJ J k (Jinvf k x) = x := by
  have hw : x ∈ fieldParity (pcJF (n := n) (k := (k : ℤ)) J) :=
    mem_fieldParity_iff.2 fun j m s => by
      rw [hx.2]
      rfl
  have hr : IsReal x := fun m s => hx.1 m s
  exact JR_Jinv (pcJF_mul_self J) hw hr

/-! ### The real mixed parity class as a fixed space -/

/-- The reflection `ε_j R_j^*` of the torus forms (mixed class `J`), as a real unitary. -/
def reflJ (J : Finset (Fin n)) (j : Fin n) (i : Fin (Fintype.card (Fin n) + 1)) :
    TW n i ≃ₗᵢ[ℝ] TW n i where
  toLinearEquiv :=
    ((DeRham.mixedSymmetries (Fin n) J).toInvolutions.R j i).toLinearEquiv.restrictScalars ℝ
  norm_map' := ((DeRham.mixedSymmetries (Fin n) J).toInvolutions.R j i).norm_map

theorem coeFn_reflJ (J : Finset (Fin n)) (j : Fin n) (i : Fin (Fintype.card (Fin n) + 1))
    (u : TW n i) (m : Fin n → ℤ) :
    (reflJ J j i u : (Fin n → ℤ) → Form ℂ (Fin n) i) m =
      DeRham.mixedSign J j • DeRham.reflForm j i (u (Fourier.Torus.flipAt j m)) :=
  Measure.ae_count_iff.1 (coeFn_symLp ((DeRham.mixedSymmetries (Fin n) J).R j)
    ((DeRham.mixedSymmetries (Fin n) J).ρ j i) u) m

theorem reflJ_cnj (J : Finset (Fin n)) (j : Fin n) (i : Fin (Fintype.card (Fin n) + 1))
    (u : TW n i) : reflJ J j i (cnj i u) = cnj i (reflJ J j i u) := by
  refine Lp.ext_count fun m => ?_
  rw [coeFn_reflJ, coeFn_cnj, coeFn_cnj, coeFn_reflJ]
  rw [Fourier.Torus.flipAt_neg]
  ext t
  simp only [PiLp.smul_apply, DeRham.reflForm_apply, Feec.Fourier.entryConj_apply, smul_eq_mul,
    map_mul]
  congr 1
  · simp [DeRham.mixedSign]; split_ifs <;> simp
  · congr 1; simp [DeRham.reflSign]; split_ifs <;> simp

/-- The real unitaries of the real mixed parity model: the conjugation and the reflections. -/
def realRJ (J : Finset (Fin n)) : Option (Fin n) → ∀ i, TW n i ≃ₗᵢ[ℝ] TW n i
  | none => cnj
  | some j => reflJ J j

/-- **The reflections `ε_j R_j^*` and the real structure**: commuting real unitary involutions. -/
def realInvolutionsJ (J : Finset (Fin n)) : (RT n).Involutions (Option (Fin n)) where
  R := realRJ J
  invol k i u := by
    cases k
    · exact Torus.DeRham.windowReal.toConj.invol i u
    · exact (DeRham.mixedSymmetries (Fin n) J).toInvolutions.invol _ i u
  comm k l i u := by
    cases k <;> cases l
    · rfl
    · exact (reflJ_cnj J _ i u).symm
    · exact reflJ_cnj J _ i u
    · exact (DeRham.mixedSymmetries (Fin n) J).toInvolutions.comm _ _ i u
  mapsTo k i j x := by
    cases k
    · exact Torus.DeRham.windowReal.toConj.mapsTo i j ⟨x.1, x.2⟩
    · exact (DeRham.mixedSymmetries (Fin n) J).toInvolutions.mapsTo _ i j ⟨x.1, x.2⟩
  comm_d k i j x := by
    cases k
    · exact Torus.DeRham.windowReal.toConj.comm i j ⟨x.1, x.2⟩
    · exact (DeRham.mixedSymmetries (Fin n) J).toInvolutions.comm_d _ i j ⟨x.1, x.2⟩

/-- The action of `(ℤ/2)^{n+1}` by the mixed reflections and the conjugation. -/
abbrev realActionJ (J : Finset (Fin n)) :
    (RT n).Action (Multiplicative (Option (Fin n) → ZMod 2)) :=
  (realInvolutionsJ J).toAction

instance (J : Finset (Fin n)) (i : Fin (Fintype.card (Fin n) + 1)) :
    CompleteSpace ((realActionJ (n := n) J).fixed i) :=
  ((realActionJ J).isClosed_fixed i).completeSpace_coe

theorem mem_realFixedJ_iff {J : Finset (Fin n)} {i : Fin (Fintype.card (Fin n) + 1)} {u : TW n i} :
    u ∈ (realActionJ J).fixed i ↔ RealParJ J i u := by
  rw [(realInvolutionsJ J).mem_fixed_toAction]
  constructor
  · intro h
    refine ⟨fun m t => ?_, fun j m t => ?_⟩
    · have e := congrArg (fun v : TW n i => (v : (Fin n → ℤ) → Form ℂ (Fin n) i) (-m) t) (h none)
      simp only [realInvolutionsJ, realRJ, coeFn_cnj, neg_neg,
        Feec.Fourier.entryConj_apply] at e
      exact e.symm
    · have e := congrArg (fun v : TW n i => (v : (Fin n → ℤ) → Form ℂ (Fin n) i)
        (Fourier.Torus.flipAt j m) t) (h (some j))
      simp only [realInvolutionsJ, realRJ, coeFn_reflJ, PiLp.smul_apply,
        DeRham.reflForm_apply, smul_eq_mul] at e
      rw [Fourier.Torus.flipAt_flipAt j m] at e
      rw [← e]; ring
  · rintro ⟨h1, h2⟩ k
    cases k with
    | none =>
      refine Lp.ext_count fun m => ?_
      ext t
      simp only [realInvolutionsJ, realRJ, coeFn_cnj, Feec.Fourier.entryConj_apply]
      rw [h1, RCLike.conj_conj]
    | some j =>
      refine Lp.ext_count fun m => ?_
      ext t
      simp only [realInvolutionsJ, realRJ, coeFn_reflJ, PiLp.smul_apply, DeRham.reflForm_apply,
        smul_eq_mul]
      rw [h2]
      linear_combination (DeRham.reflSign j t.1 * DeRham.reflSign j t.1 *
          (u m : Form ℂ (Fin n) i) t) * DeRham.mixedSign_mul_self J j +
        ((u m : Form ℂ (Fin n) i) t) * DeRham.reflSign_mul_self j t.1

/-- **The parity extension of the window** in the mixed class `J`. -/
def JJ (J : Finset (Fin n)) (a : Fin (Fintype.card (Fin n) + 1)) : WQ n a →L[ℝ] TW n a :=
  JfJ J (a : ℕ)

theorem inner_JJ (J : Finset (Fin n)) (a : Fin (Fintype.card (Fin n) + 1)) (x y : WQ n a) :
    ⟪JJ J a x, JJ J a y⟫_ℝ = ((2 ^ n : ℝ) : ℝ) * ⟪x, y⟫_ℝ :=
  inner_JfJ J a x y

theorem range_JJ (J : Finset (Fin n)) (a : Fin (Fintype.card (Fin n) + 1)) :
    LinearMap.range (JJ J a : WQ n a →ₗ[ℝ] TW n a) = (realActionJ J).fixed a := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩; exact mem_realFixedJ_iff.2 (JfJ_realParJ J _ u)
  · intro hx; exact ⟨Jinvf (a : ℕ) x, JfJ_Jinvf (mem_realFixedJ_iff.1 hx)⟩

instance (J : Finset (Fin n)) (a : Fin (Fintype.card (Fin n) + 1)) :
    (LinearMap.range (JJ J a : WQ n a →ₗ[ℝ] TW n a)).HasOrthogonalProjection := by
  rw [range_JJ]; infer_instance

theorem reducing_rangeJ (J : Finset (Fin n)) :
    (RT n).ReducingSubcomplex fun a => LinearMap.range (JJ J a : WQ n a →ₗ[ℝ] TW n a) := by
  have h := (realActionJ (n := n) J).reducingSubcomplex_fixed
  refine ⟨fun a b => ?_⟩
  convert h.reduces a b using 1 <;> exact range_JJ _ _

/-! ### Green's identity with mixed boundary conditions and the torus symbol -/

theorem ext_JfJ (J : Finset (Fin n)) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)))
    (m : Fin n → ℤ) (r : Finset (Fin n)) :
    Feec.Fourier.Exterior.ext k ((JfJ J k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m) r =
      ∫ y in Q (Fin n), (((uExt u r : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) *
        fold (pcJ J r) (mFourier (-m)) y := by
  by_cases h : (#r : ℤ) = k
  · rw [Feec.Fourier.Exterior.ext_apply k _ h, coeff_JfJ, uExt,
      formExt_of_card _ (by exact_mod_cast h)]
  · rw [Feec.Fourier.Exterior.ext_apply_of_ne k _ h, uExt, formExt,
      dite_eq_right (by exact_mod_cast h)]
    symm
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Q (Fin n)))] with y hy
    rw [hy]; simp

/-- **Green's identity of `(u, w)` with mixed boundary conditions**, in coordinates. -/
def GreenForJ (J : Finset (Fin n)) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)))
    (w : L2F ℝ (Q (Fin n)) (formIdx n ((k : ℤ) + 1))) : Prop :=
  ∀ (t : formIdx n ((k : ℤ) + 1)) (φ : (Fin n → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
    (∃ M, ∀ y, |φ y| ≤ M) → (∃ L, ∀ j y, |fderiv ℝ φ y (Pi.single j 1)| ≤ L) →
    (∀ j ∈ t.1, j ∉ J → ∀ y : Fin n → ℝ, (y j = 0 ∨ y j = 1 / 2) → φ y = 0) →
    ∫ y in Q (Fin n), (w t : (Fin n → ℝ) → ℝ) y * φ y =
      -∑ j ∈ t.1, (ExteriorFibre.sgn j t.1 : ℝ) *
        ∫ y in Q (Fin n), (uExt u (t.1.erase j) : (Fin n → ℝ) → ℝ) y *
          fderiv ℝ φ y (Pi.single j 1)

/-- The admissible test functions of `GreenForJ`. -/
def AdmJ (J : Finset (Fin n)) {k : ℤ} (t : formIdx n (k + 1)) (φ : (Fin n → ℝ) → ℝ) : Prop :=
  (∃ M, ∀ y, |φ y| ≤ M) ∧ (∃ L, ∀ j y, |fderiv ℝ φ y (Pi.single j 1)| ≤ L) ∧
    ∀ j ∈ t.1, j ∉ J → ∀ y : Fin n → ℝ, (y j = 0 ∨ y j = 1 / 2) → φ y = 0

theorem greenForJ_of_inner {J : Finset (Fin n)} {k : ℕ}
    {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} {w : L2F ℝ (Q (Fin n)) (formIdx n ((k : ℤ) + 1))}
    (h : ∀ (t : formIdx n ((k : ℤ) + 1)) (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ),
      AdmJ J t φ →
      ⟪w, toL2F (memLp_single1 t hφ)⟫_ℝ = ⟪u, toL2F (memLp_formalAdj_single1 t hφ)⟫_ℝ) :
    GreenForJ J k u w := by
  intro t φ hφ hM hL hV
  have e := h t φ hφ ⟨hM, hL, hV⟩
  obtain ⟨L, hL'⟩ := hL
  rw [Feec.Domain.inner_toL2F, Feec.Domain.inner_toL2F] at e
  simp only [starRingEnd_apply, star_trivial] at e
  rw [Finset.sum_eq_single t (fun s _ hs => by simp [single1, hs]) (by simp)] at e
  rw [show ∫ y in Q (Fin n), (w t : (Fin n → ℝ) → ℝ) y * φ y = _ from by
    simpa [single1] using e]
  have hs : ∀ s : formIdx n (k : ℤ), ∫ y in Q (Fin n), (u s : (Fin n → ℝ) → ℝ) y *
      (extDerivOp ℝ n (k : ℤ)).formalAdj.apply (single1 t φ) s y =
      -∑ j ∈ t.1, (ExteriorFibre.sgn j t.1 : ℝ) * (if t.1.erase j = s.1 then
        ∫ y in Q (Fin n), (u s : (Fin n → ℝ) → ℝ) y * fderiv ℝ φ y (Pi.single j 1) else 0) := by
    intro s
    simp only [formalAdj_single1_apply, mul_neg, Finset.mul_sum]
    rw [integral_neg, integral_finsetSum _ fun j _ => ?_]
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · rw [← integral_const_mul]; congr 1; funext y; ring
      · simp
    · split_ifs
      · exact (integral_real_mul_fderiv_integrable u hφ hL' s j).const_mul _ |>.congr
          (Eventually.of_forall fun y => by simp only; ring)
      · simp
  simp only [hs, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  refine sum_ite_eq_uExt u (t.1.erase j)
    (fun v => ∫ y in Q (Fin n), (v : (Fin n → ℝ) → ℝ) y * fderiv ℝ φ y (Pi.single j 1)) ?_
  refine integral_eq_zero_of_ae ?_
  filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Q (Fin n)))] with y hy
  rw [hy]; simp

theorem coeff_d_of_greenForJ {J : Finset (Fin n)} {k : ℕ}
    {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} {w : L2F ℝ (Q (Fin n)) (formIdx n ((k : ℤ) + 1))}
    (h : GreenForJ J k u w) (m : Fin n → ℤ) :
    (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (Feec.Fourier.Torus.freq m)
        ((JfJ J k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m) =
      (JfJ J (k + 1) w : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m := by
  refine PiLp.ext fun t' => ?_
  set e := mFourier (-m)
  have hc := pcJ_mul_self (n := n) J
  set t : formIdx n ((k : ℤ) + 1) := ⟨t'.1, by exact_mod_cast t'.2⟩
  set F := fold (pcJ J t'.1) e
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F := contDiff_fold _ (isSmooth_mFourier _)
  have hFd : Differentiable ℝ F := hFs.differentiable (by simp)
  have hFc : Continuous F := hFs.continuous
  set B := 2 ^ Fintype.card (Fin n) * ‖e‖
  have hFb : ∀ y, ‖F y‖ ≤ B := norm_fold_le (hc _) e
  set a : Fin n → ℂ := fun i => 2 * Real.pi * Complex.I * (((-m) i : ℤ) : ℂ)
  set L := ∑ i, ‖a i‖ * B
  have hdFb : ∀ j y, ‖fderiv ℝ F y (Pi.single j 1)‖ ≤ L := by
    intro j y
    rw [fderiv_fold_mFourier, norm_mul]
    calc ‖a j‖ * ‖fold (Function.update (pcJ J t'.1) j (-pcJ J t'.1 j)) e y‖ ≤ ‖a j‖ * B :=
          mul_le_mul_of_nonneg_left (norm_fold_le (update_mul_self (hc _) j) e y) (norm_nonneg _)
      _ ≤ L := Finset.single_le_sum (f := fun i => ‖a i‖ * B)
          (fun i _ => mul_nonneg (norm_nonneg _) (by positivity)) (Finset.mem_univ j)
  have hV : ∀ (g : ℂ → ℝ), g 0 = 0 → ∀ j ∈ t.1, j ∉ J → ∀ y : Fin n → ℝ,
      (y j = 0 ∨ y j = 1 / 2) → g (F y) = 0 := by
    intro g hg j hj hjJ y hy
    have hj' : j ∈ t'.1 := hj
    have h0 : F y = 0 := fold_eq_zero_of_face (c := pcJ J t'.1) (hc _) (j := j)
      (by simp [pcJ, DeRham.mixedSign, DeRham.reflSign, hj', hjJ]) e hy
    rw [h0, hg]
  have hre := h t (fun y => (F y).re) (Complex.reCLM.contDiff.comp hFs)
    ⟨B, fun y => (Complex.abs_re_le_norm _).trans (hFb y)⟩
    ⟨L, fun j y => by rw [fderiv_re_comp (hFd y)]; exact (Complex.abs_re_le_norm _).trans (hdFb j y)⟩
    (hV Complex.re Complex.zero_re)
  have him := h t (fun y => (F y).im) (Complex.imCLM.contDiff.comp hFs)
    ⟨B, fun y => (Complex.abs_im_le_norm _).trans (hFb y)⟩
    ⟨L, fun j y => by rw [fderiv_im_comp (hFd y)]; exact (Complex.abs_im_le_norm _).trans (hdFb j y)⟩
    (hV Complex.im Complex.zero_im)
  have hj : ∀ j, ∫ y in Q (Fin n), (((uExt u (t'.1.erase j) : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) *
      fderiv ℝ F y (Pi.single j 1) =
      ((∫ y in Q (Fin n), (uExt u (t'.1.erase j) : (Fin n → ℝ) → ℝ) y *
          fderiv ℝ (fun y => (F y).re) y (Pi.single j 1) : ℝ) : ℂ) +
        Complex.I * ((∫ y in Q (Fin n), (uExt u (t'.1.erase j) : (Fin n → ℝ) → ℝ) y *
          fderiv ℝ (fun y => (F y).im) y (Pi.single j 1) : ℝ) : ℂ) := by
    intro j
    rw [integral_ofReal_mul_eq _ ((hFs.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hdFb j)]
    simp only [fderiv_re_comp (hFd _), fderiv_im_comp (hFd _)]
  have hG : ∫ y in Q (Fin n), (((w t : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) * F y =
      -∑ j ∈ t'.1, ((ExteriorFibre.sgn j t'.1 : ℝ) : ℂ) *
        ∫ y in Q (Fin n), (((uExt u (t'.1.erase j) : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) *
          fderiv ℝ F y (Pi.single j 1) := by
    rw [integral_ofReal_mul_eq (w t) hFc hFb]
    change ((∫ y in Q (Fin n), (w t : (Fin n → ℝ) → ℝ) y * (fun y => (F y).re) y : ℝ) : ℂ) +
      Complex.I * ((∫ y in Q (Fin n), (w t : (Fin n → ℝ) → ℝ) y * (fun y => (F y).im) y : ℝ) : ℂ) = _
    have ht : (t : Finset (Fin n)) = t'.1 := rfl
    rw [hre, him, ht]
    simp only [hj]
    push_cast
    simp only [← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [Feec.Fourier.Exterior.deRham_m_succ_apply, coeff_JfJ]
  change _ = ∫ y in Q (Fin n), (((w t : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) * F y
  rw [hG, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hd : ∀ y, fderiv ℝ F y (Pi.single j 1) = a j * fold (pcJ J (t'.1.erase j)) e y := by
    intro y
    rw [fderiv_fold_mFourier, update_pcJ_erase J hj]
  simp only [hd]
  have hi : ∫ y in Q (Fin n), (((uExt u (t'.1.erase j) : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) *
      (a j * fold (pcJ J (t'.1.erase j)) e y) =
      a j * Feec.Fourier.Exterior.ext k ((JfJ J k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m)
        (t'.1.erase j) := by
    rw [ext_JfJ, ← integral_const_mul]
    congr 1; funext y; ring
  rw [hi, sgn_cast, Feec.Fourier.Torus.freq_apply]
  simp only [a, Pi.neg_apply, Int.cast_neg]
  push_cast
  ring

/-! ### The cut-off in the directions of `J` -/

section CutoffJ

open RowWise (mN mN_pos eta eta_nonneg eta_le_one abs_eta_le_one contDiff_eta eta_eq_zero_of_ne
  eta_eq_one abs_deriv_eta_mul_le exists_bound_deriv_smoothTransition)

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The cut-off in the directions of `J`: `χ_m^J(y) = ∏_{i ∈ J} η_m(yᵢ)`. -/
def chiJ (J : Finset d) (m : ℕ) (y : d → ℝ) : ℝ := ∏ i ∈ J, eta m (y i)

omit [DecidableEq d] in
theorem contDiff_chiJ (J : Finset d) (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (chiJ J m) :=
  contDiff_prod fun i _ => (contDiff_eta m).comp (contDiff_apply ℝ (fun _ : d => ℝ) i)

omit [Fintype d] [DecidableEq d] in
theorem abs_chiJ_le_one (J : Finset d) (m : ℕ) (y : d → ℝ) : |chiJ J m y| ≤ 1 := by
  rw [chiJ, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => abs_eta_le_one m _

omit [Fintype d] [DecidableEq d] in
theorem chiJ_eq_zero_of {J : Finset d} {m : ℕ} {y : d → ℝ} {j : d} (hj : j ∈ J)
    (h : y j ≤ 1 / (2 * mN m) ∨ 1 / 2 - 1 / (2 * mN m) ≤ y j) : chiJ J m y = 0 := by
  refine Finset.prod_eq_zero hj ?_
  by_contra hne
  have := eta_eq_zero_of_ne hne
  rcases h with h | h <;> linarith [this.1, this.2]

omit [Fintype d] [DecidableEq d] in
theorem chiJ_eq_one_of {J : Finset d} {m : ℕ} {y : d → ℝ}
    (h : ∀ j ∈ J, 1 / mN m ≤ y j ∧ y j ≤ 1 / 2 - 1 / mN m) : chiJ J m y = 1 :=
  Finset.prod_eq_one fun j hj => eta_eq_one (h j hj).1 (h j hj).2

omit [DecidableEq d] in
theorem eventually_chiJ_eq_one (J : Finset d) {y : d → ℝ} (hy : y ∈ Q d) :
    ∀ᶠ m in atTop, chiJ J m =ᶠ[𝓝 y] fun _ => 1 := by
  have hy' := mem_Q.1 hy
  have hpos : ∀ i, 0 < min (y i) (1 / 2 - y i) := fun i =>
    lt_min (hy' i).1 (by linarith [(hy' i).2])
  obtain ⟨δ, hδ, hδi⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ min (y i) (1 / 2 - y i) := by
    by_cases he : IsEmpty d
    · exact ⟨1, one_pos, fun i => (he.false i).elim⟩
    · have hne : (Finset.univ : Finset d).Nonempty := by
        rw [Finset.univ_nonempty_iff]; exact not_isEmpty_iff.1 he
      refine ⟨Finset.univ.inf' hne fun i => min (y i) (1 / 2 - y i), ?_, fun i =>
        Finset.inf'_le _ (Finset.mem_univ i)⟩
      rw [Finset.lt_inf'_iff]
      exact fun i _ => hpos i
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  filter_upwards [eventually_ge_atTop N] with m hm
  have hmN : 2 / δ < mN m := by
    unfold mN; linarith [show (N : ℝ) ≤ m from Nat.cast_le.2 hm]
  have hmδ : 1 / mN m < δ / 2 := by
    rw [div_lt_iff₀ (mN_pos m)]
    rw [div_lt_iff₀ hδ] at hmN
    linarith
  filter_upwards [Metric.ball_mem_nhds y (by linarith : (0 : ℝ) < δ / 2)] with z hz
  rw [Metric.mem_ball] at hz
  refine chiJ_eq_one_of fun i _ => ?_
  have hd : |z i - y i| < δ / 2 := by
    have := (dist_le_pi_dist z y i).trans_lt hz
    rwa [Real.dist_eq] at this
  rw [abs_lt] at hd
  have h1 := (hδi i).trans (min_le_left _ _)
  have h2 := (hδi i).trans (min_le_right _ _)
  constructor <;> linarith

theorem abs_fderiv_chiJ_le {J : Finset d} (m : ℕ) {c : d} (hc : c ∈ J) (y : d → ℝ) :
    |fderiv ℝ (chiJ J m) y (Pi.single c 1)| ≤ |deriv (eta m) (y c)| := by
  have hd : ∀ s, HasDerivAt (eta m) (deriv (eta m) s) s := fun s =>
    ((contDiff_eta m).differentiable (by simp) s).hasDerivAt
  have hl := ((contDiff_chiJ (d := d) J m).differentiable (by simp)
    (y + Pi.single c 0)).hasDerivAt_comp_add_single
  rw [Pi.single_zero, add_zero, partialDeriv] at hl
  set R : ℝ := ∏ i ∈ J.erase c, eta m (y i)
  have e : (fun s => chiJ J m (y + Pi.single c s)) = fun s => eta m (y c + s) * R := by
    funext s
    rw [chiJ, ← Finset.mul_prod_erase _ _ hc]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun i hi => by
        simp [Finset.ne_of_mem_erase hi]
  have h2 : HasDerivAt (fun s => eta m (y c + s) * R) (deriv (eta m) (y c) * R) 0 := by
    have := (hd (y c + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add (y c))
    simp only [add_zero, mul_one] at this
    exact this.mul_const R
  rw [e] at hl
  rw [hl.unique h2, abs_mul]
  have hR : |R| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => abs_eta_le_one m _
  calc |deriv (eta m) (y c)| * |R| ≤ |deriv (eta m) (y c)| * 1 :=
        mul_le_mul_of_nonneg_left hR (abs_nonneg _)
    _ = _ := mul_one _

theorem fderiv_chiJ_of_notMem {J : Finset d} (m : ℕ) {c : d} (hc : c ∉ J) (y : d → ℝ) :
    fderiv ℝ (chiJ J m) y (Pi.single c 1) = 0 := by
  have hl := ((contDiff_chiJ (d := d) J m).differentiable (by simp)
    (y + Pi.single c 0)).hasDerivAt_comp_add_single
  rw [Pi.single_zero, add_zero, partialDeriv] at hl
  have e : (fun s => chiJ J m (y + Pi.single c s)) = fun _ => chiJ J m y := by
    funext s
    refine Finset.prod_congr rfl fun i hi => ?_
    have : i ≠ c := fun h => hc (h ▸ hi)
    simp [this]
  rw [e] at hl
  exact hl.unique (hasDerivAt_const _ _)

theorem abs_fderiv_chiJ_mul_le {J : Finset d} {M₀ : ℝ}
    (hM₀ : ∀ x, |deriv Real.smoothTransition x| ≤ M₀) (m : ℕ) {f : (d → ℝ) → ℝ}
    (hf : Differentiable ℝ f) {c : d} (hc : c ∈ J) {L : ℝ}
    (hL : ∀ y, |fderiv ℝ f y (Pi.single c 1)| ≤ L)
    (hV : ∀ y : d → ℝ, (y c = 0 ∨ y c = 1 / 2) → f y = 0) {y : d → ℝ} (hy : y ∈ Q d) :
    |fderiv ℝ (chiJ J m) y (Pi.single c 1) * f y| ≤ 4 * M₀ * L := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL y)
  have hface := abs_le_of_faces hf hL (fun z hz => hV z (Or.inl hz)) (fun z hz => hV z (Or.inr hz))
    hy
  rw [abs_mul]
  calc |fderiv ℝ (chiJ J m) y (Pi.single c 1)| * |f y| ≤
        |deriv (eta m) (y c)| * (L * min (y c) (1 / 2 - y c)) :=
        mul_le_mul (abs_fderiv_chiJ_le m hc y) hface (abs_nonneg _) (abs_nonneg _)
    _ = L * (|deriv (eta m) (y c)| * min (y c) (1 / 2 - y c)) := by ring
    _ ≤ L * (4 * M₀) := mul_le_mul_of_nonneg_left (abs_deriv_eta_mul_le hM₀ m (mem_Q.1 hy c)) hL0
    _ = 4 * M₀ * L := by ring

end CutoffJ

/-! ### The domain spaces `D(d_J)` -/

section Domain

variable {Ω : Set (Fin n → ℝ)}

/-- The open neighbourhood of width `δ` of the faces `{y_j ∈ {0, ½}}`, `j ∈ J`. -/
def faceNbhd (J : Finset (Fin n)) (δ : ℝ) : Set (Fin n → ℝ) :=
  {y | ∃ j ∈ J, y j < δ ∨ 1 / 2 - δ < y j}

theorem isOpen_faceNbhd (J : Finset (Fin n)) (δ : ℝ) : IsOpen (faceNbhd J δ) := by
  have e : faceNbhd J δ = ⋃ j ∈ J, ({y : Fin n → ℝ | y j < δ} ∪ {y | 1 / 2 - δ < y j}) := by
    ext y; simp [faceNbhd]
  rw [e]
  exact isOpen_biUnion fun j _ =>
    (isOpen_lt (continuous_apply j) continuous_const).union
      (isOpen_lt continuous_const (continuous_apply j))

theorem faceNbhd_mono (J : Finset (Fin n)) {δ δ' : ℝ} (h : δ ≤ δ') :
    faceNbhd J δ ⊆ faceNbhd J δ' := by
  rintro y ⟨j, hj, hy⟩
  exact ⟨j, hj, hy.imp (fun h' => h'.trans_le h) fun h' => by linarith⟩

@[simp] theorem faceNbhd_empty (δ : ℝ) : faceNbhd (∅ : Finset (Fin n)) δ = ∅ := by
  ext y; simp [faceNbhd]

variable (Ω) in
/-- **`u` vanishes a.e. near the faces normal to `J`**: on a neighbourhood `faceNbhd J δ`. -/
def VanishNear (J : Finset (Fin n)) {ι : Type*} (u : L2F ℝ Ω ι) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ i, ∀ᵐ y ∂(volume.restrict Ω), y ∈ faceNbhd J δ →
    (u i : (Fin n → ℝ) → ℝ) y = 0

variable (Ω) in
/-- The forms vanishing a.e. near the faces normal to `J`. -/
def coreSub (J : Finset (Fin n)) (ι : Type*) : Submodule ℝ (L2F ℝ Ω ι) where
  carrier := {u | VanishNear Ω J u}
  zero_mem' := ⟨1, one_pos, fun i => by
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with y hy _
    simp only [PiLp.zero_apply] at hy ⊢
    exact hy⟩
  add_mem' := by
    rintro u v ⟨δ, hδ, hu⟩ ⟨δ', hδ', hv⟩
    refine ⟨min δ δ', lt_min hδ hδ', fun i => ?_⟩
    filter_upwards [hu i, hv i, Lp.coeFn_add (u i) (v i)] with y h1 h2 h3 hy
    change ((u i + v i : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) y = 0
    rw [h3, Pi.add_apply, h1 (faceNbhd_mono J (min_le_left _ _) hy),
      h2 (faceNbhd_mono J (min_le_right _ _) hy), add_zero]
  smul_mem' := by
    rintro c u ⟨δ, hδ, hu⟩
    refine ⟨δ, hδ, fun i => ?_⟩
    filter_upwards [hu i, Lp.coeFn_smul c (u i)] with y h1 h2 hy
    change ((c • u i : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) y = 0
    rw [h2, Pi.smul_apply, h1 hy, smul_zero]

variable (Ω) in
/-- `d_max` on the forms of `D(d_max)` vanishing near the faces normal to `J`. -/
abbrev dCore (J : Finset (Fin n)) (k : ℤ) :
    L2F ℝ Ω (formIdx n k) →ₗ.[ℝ] L2F ℝ Ω (formIdx n (k + 1)) :=
  ((extDerivOp ℝ n k).maximal Ω).domRestrict (coreSub Ω J (formIdx n k))

variable (Ω) in
/-- **`d_J`**: the closure of `d_max` on the forms vanishing near the faces normal to `J`. -/
def dPart (J : Finset (Fin n)) (k : ℤ) :
    L2F ℝ Ω (formIdx n k) →ₗ.[ℝ] L2F ℝ Ω (formIdx n (k + 1)) :=
  (dCore Ω J k).closure

theorem mem_graph_dCore {J : Finset (Fin n)} {k : ℤ} {x : L2F ℝ Ω (formIdx n k)}
    {y : L2F ℝ Ω (formIdx n (k + 1))} :
    (x, y) ∈ (dCore Ω J k).graph ↔ ∃ h : x ∈ ((extDerivOp ℝ n k).maximal Ω).domain,
      VanishNear Ω J x ∧ (extDerivOp ℝ n k).maximal Ω ⟨x, h⟩ = y := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨z, hz1, hz2⟩
    simp only at hz1 hz2
    subst hz1 hz2
    exact ⟨(Submodule.mem_inf.1 z.2).2, (Submodule.mem_inf.1 z.2).1, (LinearPMap.domRestrict_apply rfl).symm⟩
  · rintro ⟨h, hv, rfl⟩
    exact ⟨⟨x, Submodule.mem_inf.2 ⟨hv, h⟩⟩, rfl, LinearPMap.domRestrict_apply rfl⟩

theorem isClosable_dCore (hΩ : IsOpen Ω) (J : Finset (Fin n)) (k : ℤ) :
    (dCore Ω J k).IsClosable :=
  ((extDerivOp ℝ n k).isClosed_maximal hΩ).isClosable.leIsClosable domRestrict_le

theorem dPart_graph (hΩ : IsOpen Ω) (J : Finset (Fin n)) (k : ℤ) :
    (dPart Ω J k).graph = (dCore Ω J k).graph.topologicalClosure :=
  (isClosable_dCore hΩ J k).graph_closure_eq_closure_graph.symm

theorem isClosed_dPart (hΩ : IsOpen Ω) (J : Finset (Fin n)) (k : ℤ) : (dPart Ω J k).IsClosed :=
  (isClosable_dCore hΩ J k).closure_isClosed

theorem dPart_le_maximal (hΩ : IsOpen Ω) (J : Finset (Fin n)) (k : ℤ) :
    dPart Ω J k ≤ (extDerivOp ℝ n k).maximal Ω := by
  refine le_of_le_graph ?_
  rw [dPart_graph hΩ]
  exact Submodule.topologicalClosure_minimal _ (le_graph_of_le domRestrict_le)
    ((extDerivOp ℝ n k).isClosed_maximal hΩ)

theorem dPart_apply_eq (hΩ : IsOpen Ω) (J : Finset (Fin n)) (k : ℤ) (x : (dPart Ω J k).domain) :
    dPart Ω J k x = (extDerivOp ℝ n k).maximal Ω ⟨x, (dPart_le_maximal hΩ J k).1 x.2⟩ :=
  (dPart_le_maximal hΩ J k).2 rfl

theorem exists_pos_of_isCompact_subset_Q {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKQ : K ⊆ Q (Fin n)) : ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ K, ∀ j, δ ≤ y j ∧ y j ≤ 1 / 2 - δ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun y hy => hy.elim⟩
  have hδj : ∀ j : Fin n, ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ K, δ ≤ min (y j) (1 / 2 - y j) := by
    intro j
    obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne
      ((continuous_apply j).min (continuous_const.sub (continuous_apply j))).continuousOn
    have h := mem_Q.1 (hKQ hy₀) j
    exact ⟨min (y₀ j) (1 / 2 - y₀ j), lt_min h.1 (by linarith [h.2]), fun y hy => hmin hy⟩
  choose δ hδ hδK using hδj
  by_cases he : IsEmpty (Fin n)
  · exact ⟨1, one_pos, fun y _ j => (he.false j).elim⟩
  · have hne' : (Finset.univ : Finset (Fin n)).Nonempty := by
      rw [Finset.univ_nonempty_iff]; exact not_isEmpty_iff.1 he
    refine ⟨Finset.univ.inf' hne' δ, (Finset.lt_inf'_iff _).2 fun j _ => hδ j,
      fun y hy j => ?_⟩
    have h1 := (Finset.inf'_le δ (Finset.mem_univ j)).trans (hδK j y hy)
    exact ⟨h1.trans (min_le_left _ _), by linarith [h1.trans (min_le_right _ _)]⟩

theorem vanishNear_testField (hΩQ : Ω ⊆ Q (Fin n)) (J : Finset (Fin n)) {ι : Type*} [Fintype ι]
    {φ : ι → (Fin n → ℝ) → ℝ} (hφ : Feec.Domain.IsTestField Ω φ) :
    VanishNear Ω J (Feec.Domain.testField hφ) := by
  set K := ⋃ i, tsupport (φ i)
  have hK : IsCompact K := isCompact_iUnion fun i => (hφ i).hasCompactSupport
  have hKQ : K ⊆ Q (Fin n) := iUnion_subset fun i => (hφ i).tsupport_subset.trans hΩQ
  obtain ⟨δ, hδ, hδK⟩ := exists_pos_of_isCompact_subset_Q hK hKQ
  refine ⟨δ, hδ, fun i => ?_⟩
  filter_upwards [Feec.Domain.coeFn_testField hφ i] with y hy hyN
  rw [hy]
  refine image_eq_zero_of_notMem_tsupport fun hyK => ?_
  obtain ⟨j, -, hj⟩ := hyN
  have := hδK y (mem_iUnion.2 ⟨i, hyK⟩) j
  rcases hj with hj | hj <;> linarith [this.1, this.2]

theorem minimal_le_dPart (hΩ : IsOpen Ω) (hΩQ : Ω ⊆ Q (Fin n)) (J : Finset (Fin n)) (k : ℤ) :
    (extDerivOp ℝ n k).minimal Ω ≤ dPart Ω J k := by
  refine le_of_le_graph ?_
  rw [(extDerivOp ℝ n k).minimal_graph hΩ, dPart_graph hΩ]
  refine Submodule.topologicalClosure_mono ?_
  rintro _ ⟨φ, hφ, rfl⟩
  have hmin := (extDerivOp ℝ n k).testField_mem_minimal_domain hΩ hφ
  have hle := (extDerivOp ℝ n k).minimal_le_maximal hΩ
  refine mem_graph_dCore.2 ⟨hle.1 hmin, vanishNear_testField hΩQ J hφ, ?_⟩
  rw [← (extDerivOp ℝ n k).minimal_testField hΩ hφ]
  exact (hle.2 rfl).symm

theorem dense_dPart (hΩ : IsOpen Ω) (hΩQ : Ω ⊆ Q (Fin n)) (J : Finset (Fin n)) (k : ℤ) :
    Dense ((dPart Ω J k).domain : Set (L2F ℝ Ω (formIdx n k))) :=
  ((extDerivOp ℝ n k).dense_minimal_domain hΩ).mono (minimal_le_dPart hΩ hΩQ J k).1

theorem dPart_empty (hΩ : IsOpen Ω) (k : ℤ) :
    dPart Ω (∅ : Finset (Fin n)) k = (extDerivOp ℝ n k).maximal Ω := by
  have hc : dCore Ω (∅ : Finset (Fin n)) k = (extDerivOp ℝ n k).maximal Ω := by
    refine eq_of_eq_graph (Submodule.ext fun p => ?_)
    rw [show p = (p.1, p.2) from rfl, mem_graph_dCore, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨h, -, hv⟩; exact ⟨⟨p.1, h⟩, rfl, hv⟩
    · rintro ⟨z, hz1, hz2⟩
      refine ⟨hz1 ▸ z.2, ⟨1, one_pos, fun i => Eventually.of_forall fun y hy => by simp at hy⟩,
        ?_⟩
      rw [← hz2]; congr 1; exact Subtype.ext hz1.symm
  refine eq_of_eq_graph ?_
  rw [dPart_graph hΩ, hc]
  exact ((extDerivOp ℝ n k).isClosed_maximal hΩ).submodule_topologicalClosure_eq

/-! ### Locality of `d_max` and the complex `HΛ_J` -/

theorem maximal_vanishNear (hΩ : IsOpen Ω) {J : Finset (Fin n)} {k : ℤ}
    (u : ((extDerivOp ℝ n k).maximal Ω).domain) {δ : ℝ}
    (hu : ∀ i, ∀ᵐ y ∂(volume.restrict Ω), y ∈ faceNbhd J δ →
      ((u : L2F ℝ Ω (formIdx n k)) i : (Fin n → ℝ) → ℝ) y = 0) (t : formIdx n (k + 1)) :
    ∀ᵐ y ∂(volume.restrict Ω), y ∈ faceNbhd J δ →
      ((extDerivOp ℝ n k).maximal Ω u t : (Fin n → ℝ) → ℝ) y = 0 := by
  set U := Ω ∩ faceNbhd J δ
  have hU : IsOpen U := hΩ.inter (isOpen_faceNbhd J δ)
  set f : (Fin n → ℝ) → ℝ := ((extDerivOp ℝ n k).maximal Ω u t : (Fin n → ℝ) → ℝ)
  have hloc : LocallyIntegrableOn f U volume := by
    have h1 : LocallyIntegrable f (volume.restrict Ω) := (Lp.memLp _).locallyIntegrable one_le_two
    exact (locallyIntegrableOn_of_locallyIntegrable_restrict h1).mono_set inter_subset_left
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgU => by
    have hgΩ : Feec.Domain.IsTestField Ω (Pi.single t g : formIdx n (k + 1) → _) := by
      refine Feec.Domain.IsTestField.single t ⟨hg, hgc, hgU.trans inter_subset_left⟩
    have hgU' : Feec.Domain.IsTestField U (Pi.single t g : formIdx n (k + 1) → _) :=
      Feec.Domain.IsTestField.single t ⟨hg, hgc, hgU⟩
    have e := (extDerivOp ℝ n k).maximal_inner_testField hΩ u hgΩ
    rw [Feec.Domain.inner_testField, Feec.Domain.inner_testField] at e
    simp only [starRingEnd_apply, star_trivial] at e
    rw [Finset.sum_eq_single t (fun s _ hs => by simp [hs]) (by simp)] at e
    simp only [Pi.single_eq_same] at e
    have hR : ∀ s : formIdx n k, ∫ x, ((u : L2F ℝ Ω (formIdx n k)) s : (Fin n → ℝ) → ℝ) x *
        (extDerivOp ℝ n k).formalAdj.apply (Pi.single t g) s x ∂volume.restrict Ω = 0 := by
      intro s
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hu s, ae_restrict_mem hΩ.measurableSet] with y hy hyΩ
      by_cases hyN : y ∈ faceNbhd J δ
      · rw [hy hyN, zero_mul]; rfl
      · rw [((extDerivOp ℝ n k).formalAdj.isTestField_apply hgU' s).eq_zero_of_notMem
          fun h => hyN h.2, mul_zero]; rfl
    rw [Finset.sum_eq_zero fun s _ => hR s] at e
    rw [← Feec.Domain.integral_restrict_of_eq_zero (Ω := Ω) fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hx (hgU h).1, zero_smul]]
    simpa [smul_eq_mul, mul_comm] using e
  filter_upwards [ae_restrict_of_ae key, ae_restrict_mem hΩ.measurableSet] with y hy hyΩ hyN
  exact hy ⟨hyΩ, hyN⟩

theorem dCore_mapsTo (hΩ : IsOpen Ω) (J : Finset (Fin n)) (k : ℤ) {x : L2F ℝ Ω (formIdx n k)}
    {y : L2F ℝ Ω (formIdx n (k + 1))} (h : (x, y) ∈ (dCore Ω J k).graph) :
    (y, (0 : L2F ℝ Ω (formIdx n (k + 1 + 1)))) ∈ (dCore Ω J (k + 1)).graph := by
  obtain ⟨hx, ⟨δ, hδ, hv⟩, rfl⟩ := mem_graph_dCore.1 h
  refine mem_graph_dCore.2 ⟨Feec.Domain.ConstCoeffOp.maximal_mapsTo hΩ
      (Feec.Domain.isComplexPair_extDerivOp k) ⟨x, hx⟩,
    ⟨δ, hδ, maximal_vanishNear hΩ ⟨x, hx⟩ hv⟩,
    Feec.Domain.ConstCoeffOp.maximal_comp hΩ (Feec.Domain.isComplexPair_extDerivOp k) ⟨x, hx⟩⟩

theorem dPart_graph_mapsTo (hΩ : IsOpen Ω) (J : Finset (Fin n)) (k : ℤ)
    {x : L2F ℝ Ω (formIdx n k)} {y : L2F ℝ Ω (formIdx n (k + 1))}
    (h : (x, y) ∈ (dPart Ω J k).graph) :
    (y, (0 : L2F ℝ Ω (formIdx n (k + 1 + 1)))) ∈ (dPart Ω J (k + 1)).graph := by
  rw [dPart_graph hΩ] at h ⊢
  set Φ : L2F ℝ Ω (formIdx n k) × L2F ℝ Ω (formIdx n (k + 1)) →
      L2F ℝ Ω (formIdx n (k + 1)) × L2F ℝ Ω (formIdx n (k + 1 + 1)) := fun p => (p.2, 0)
  have hΦ : Continuous Φ := continuous_snd.prodMk continuous_const
  have hsub : Φ '' ((dCore Ω J k).graph : Set _) ⊆ ((dCore Ω J (k + 1)).graph : Set _) := by
    rintro _ ⟨p, hp, rfl⟩
    exact dCore_mapsTo hΩ J k (show (p.1, p.2) ∈ (dCore Ω J k).graph from hp)
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at h ⊢
  exact closure_mono hsub (image_closure_subset_closure_image hΦ ⟨(x, y), h, rfl⟩)

theorem mapsTo_dPart (hΩ : IsOpen Ω) (J : Finset (Fin n)) (k : ℤ) (x : (dPart Ω J k).domain) :
    (dPart Ω J k x : L2F ℝ Ω (formIdx n (k + 1))) ∈ (dPart Ω J (k + 1)).domain :=
  mem_domain_of_mem_graph (dPart_graph_mapsTo hΩ J k ((dPart Ω J k).mem_graph x))

theorem dPart_comp (hΩ : IsOpen Ω) (J : Finset (Fin n)) (k : ℤ) (x : (dPart Ω J k).domain) :
    dPart Ω J (k + 1) ⟨_, mapsTo_dPart hΩ J k x⟩ = 0 :=
  ((image_iff (mapsTo_dPart hΩ J k x)).2 (dPart_graph_mapsTo hΩ J k ((dPart Ω J k).mem_graph x))).symm

/-- **The de Rham complex `HΛ_J(Ω)`** (`Ω ⊆ Q` open), as a Hilbert complex on `ℤ`. -/
def HQpartZ (hΩ : IsOpen Ω) (hΩQ : Ω ⊆ Q (Fin n)) (J : Finset (Fin n)) :
    HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ Ω (formIdx n k) :=
  Feec.HilbertComplex.ofSucc (dPart Ω J) (dense_dPart hΩ hΩQ J) (isClosed_dPart hΩ J)
    (mapsTo_dPart hΩ J) (dPart_comp hΩ J)

theorem HQpartZ_d (hΩ : IsOpen Ω) (hΩQ : Ω ⊆ Q (Fin n)) (J : Finset (Fin n)) (k : ℤ) :
    (HQpartZ hΩ hΩQ J).d k (k + 1) = dPart Ω J k :=
  Feec.HilbertComplex.ofSuccD_succ (dPart Ω J) k

end Domain

/-! ### Green's identity on `D(d_J)` -/

section GreenPart

open RowWise (mN mN_pos abs_deriv_eta_le exists_bound_deriv_smoothTransition)

theorem exists_mN_le {δ : ℝ} (hδ : 0 < δ) : ∃ m : ℕ, 1 / mN m ≤ δ / 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  refine ⟨N, ?_⟩
  have hm := mN_pos N
  rw [div_le_iff₀ hm]
  have : 2 / δ < mN N := by unfold mN; linarith
  rw [div_lt_iff₀ hδ] at this
  linarith

theorem chiJ_eventuallyEq_one {J : Finset (Fin n)} {m : ℕ} {δ : ℝ} (hm : 1 / mN m ≤ δ / 2)
    {y : Fin n → ℝ} (hy : y ∉ faceNbhd J δ) : chiJ J m =ᶠ[𝓝 y] fun _ => 1 := by
  have hδ : 0 < δ := by have := mN_pos m; have : 0 < 1 / mN m := by positivity
                        linarith
  filter_upwards [Metric.ball_mem_nhds y (by linarith : (0 : ℝ) < δ / 2)] with z hz
  rw [Metric.mem_ball] at hz
  refine chiJ_eq_one_of fun j hj => ?_
  have hd : |z j - y j| < δ / 2 := by
    have := (dist_le_pi_dist z y j).trans_lt hz
    rwa [Real.dist_eq] at this
  rw [abs_lt] at hd
  have h1 : δ ≤ y j := by
    by_contra h; exact hy ⟨j, hj, Or.inl (not_le.1 h)⟩
  have h2 : y j ≤ 1 / 2 - δ := by
    by_contra h; exact hy ⟨j, hj, Or.inr (by linarith [not_le.1 h])⟩
  constructor <;> linarith

theorem bounds_chiJ_mul (J : Finset (Fin n)) (m : ℕ) {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {M L : ℝ} (hM : ∀ y, |φ y| ≤ M)
    (hL : ∀ j y, |fderiv ℝ φ y (Pi.single j 1)| ≤ L) :
    (∀ y, |chiJ J m y * φ y| ≤ M) ∧
      ∃ L', ∀ j y, |fderiv ℝ (fun y => chiJ J m y * φ y) y (Pi.single j 1)| ≤ L' := by
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_bound_deriv_smoothTransition
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨fun y => ?_, L + 4 * mN m * M₀ * M, fun j y => ?_⟩
  · rw [abs_mul]
    calc |chiJ J m y| * |φ y| ≤ 1 * M :=
          mul_le_mul (abs_chiJ_le_one J m y) (hM y) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  · have hχd : Differentiable ℝ (chiJ J m) := (contDiff_chiJ J m).differentiable (by simp)
    have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
    rw [fderiv_fun_mul (hχd y) (hφd y)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      calc |chiJ J m y| * |fderiv ℝ φ y (Pi.single j 1)| ≤ 1 * L :=
            mul_le_mul (abs_chiJ_le_one J m y) (hL j y) (abs_nonneg _) zero_le_one
        _ = L := one_mul L
    · rw [abs_mul, mul_comm]
      have hd : |fderiv ℝ (chiJ J m) y (Pi.single j 1)| ≤ 4 * mN m * M₀ := by
        by_cases hj : j ∈ J
        · exact (abs_fderiv_chiJ_le m hj y).trans (abs_deriv_eta_le hM₀ m _)
        · rw [fderiv_chiJ_of_notMem m hj y, abs_zero]; have := mN_pos m; positivity
      calc |fderiv ℝ (chiJ J m) y (Pi.single j 1)| * |φ y| ≤ 4 * mN m * M₀ * M :=
            mul_le_mul hd (hM y) (abs_nonneg _) (by have := mN_pos m; positivity)
        _ = _ := rfl

theorem inner_maximal_single1_of_vanishNear {J : Finset (Fin n)} {k : ℤ}
    (a : ((extDerivOp ℝ n k).maximal (Q (Fin n))).domain)
    (ha : VanishNear (Q (Fin n)) J (a : L2F ℝ (Q (Fin n)) (formIdx n k)))
    (t : formIdx n (k + 1)) {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hadm : AdmJ J t φ) :
    ⟪(extDerivOp ℝ n k).maximal (Q (Fin n)) a, toL2F (memLp_single1 t hφ)⟫_ℝ =
      ⟪(a : L2F ℝ (Q (Fin n)) (formIdx n k)), toL2F (memLp_formalAdj_single1 t hφ)⟫_ℝ := by
  obtain ⟨δ, hδ, hv⟩ := ha
  obtain ⟨⟨M, hM⟩, ⟨L, hL⟩, hV⟩ := hadm
  obtain ⟨m, hm⟩ := exists_mN_le hδ
  set ψ : (Fin n → ℝ) → ℝ := fun y => chiJ J m y * φ y
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := (contDiff_chiJ J m).mul hφ
  obtain ⟨hψM, L', hψL⟩ := bounds_chiJ_mul J m hφ hM hL
  have hψV : ∀ j ∈ t.1, ∀ y : Fin n → ℝ, (y j = 0 ∨ y j = 1 / 2) → ψ y = 0 := by
    intro j hj y hy
    by_cases hjJ : j ∈ J
    · have hm2 := mN_pos m
      have hp : 0 < 1 / (2 * mN m) := by positivity
      rw [show ψ y = chiJ J m y * φ y from rfl, chiJ_eq_zero_of hjJ (by
        rcases hy with hy | hy
        · exact Or.inl (by rw [hy]; exact hp.le)
        · exact Or.inr (by rw [hy]; linarith)), zero_mul]
    · rw [show ψ y = chiJ J m y * φ y from rfl, hV j hj hjJ y hy, mul_zero]
  have hdv := maximal_vanishNear isOpen_Q a hv
  -- `⟪d a, φ⟫ = ⟪d a, χ φ⟫`
  have h1 : ⟪(extDerivOp ℝ n k).maximal (Q (Fin n)) a, toL2F (memLp_single1 t hφ)⟫_ℝ =
      ⟪(extDerivOp ℝ n k).maximal (Q (Fin n)) a, toL2F (memLp_single1 t hψ)⟫_ℝ := by
    rw [Feec.Domain.inner_toL2F, Feec.Domain.inner_toL2F]
    refine Finset.sum_congr rfl fun s _ => integral_congr_ae ?_
    filter_upwards [hdv s] with y hy
    by_cases hyN : y ∈ faceNbhd J δ
    · rw [hy hyN]; simp
    · congr 1
      by_cases hs : s = t
      · subst hs
        simp only [single1, Pi.single_eq_same, ψ]
        rw [(chiJ_eventuallyEq_one hm hyN).eq_of_nhds, one_mul]
      · simp [single1, hs]
  -- `⟪d a, χ φ⟫ = ⟪a, dᵗ (χ φ)⟫`
  have h2 : ⟪(extDerivOp ℝ n k).maximal (Q (Fin n)) a, toL2F (memLp_single1 t hψ)⟫_ℝ =
      ⟪(a : L2F ℝ (Q (Fin n)) (formIdx n k)), toL2F (memLp_formalAdj_single1 t hψ)⟫_ℝ := by
    have hcl := mem_closure_formalAdj_single1 t hψ hψM hψL hψV
    rw [← Submodule.topologicalClosure_coe, SetLike.mem_coe,
      ← (extDerivOp ℝ n k).formalAdj.minimal_graph isOpen_Q] at hcl
    obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).1 hcl
    have := LinearPMap.adjoint_isFormalAdjoint
      ((extDerivOp ℝ n k).formalAdj.dense_minimal_domain isOpen_Q) a x
    change ⟪(extDerivOp ℝ n k).maximal (Q (Fin n)) a, (x : L2F ℝ (Q (Fin n)) _)⟫_ℝ =
      ⟪(a : L2F ℝ (Q (Fin n)) _), (extDerivOp ℝ n k).formalAdj.minimal (Q (Fin n)) x⟫_ℝ at this
    rw [hx1, hx2] at this
    exact this
  -- `⟪a, dᵗ (χ φ)⟫ = ⟪a, dᵗ φ⟫`
  have h3 : ⟪(a : L2F ℝ (Q (Fin n)) (formIdx n k)), toL2F (memLp_formalAdj_single1 t hψ)⟫_ℝ =
      ⟪(a : L2F ℝ (Q (Fin n)) (formIdx n k)), toL2F (memLp_formalAdj_single1 t hφ)⟫_ℝ := by
    rw [Feec.Domain.inner_toL2F, Feec.Domain.inner_toL2F]
    refine Finset.sum_congr rfl fun s _ => integral_congr_ae ?_
    filter_upwards [hv s] with y hy
    by_cases hyN : y ∈ faceNbhd J δ
    · rw [hy hyN]; simp
    · congr 1
      refine apply_congr_of_eventuallyEq _ (fun p => ?_) s
      by_cases hp : p = t
      · subst hp
        simp only [single1, Pi.single_eq_same, ψ]
        filter_upwards [chiJ_eventuallyEq_one hm hyN] with z hz
        rw [hz, one_mul]
      · simp [single1, hp]
  rw [h1, h2, h3]

theorem greenForJ_dPart (J : Finset (Fin n)) (k : ℕ)
    (u : (dPart (Q (Fin n)) J (k : ℤ)).domain) :
    GreenForJ J k u (dPart (Q (Fin n)) J (k : ℤ) u) := by
  refine greenForJ_of_inner fun t φ hφ hadm => ?_
  let S : Set (L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)) × L2F ℝ (Q (Fin n)) (formIdx n ((k : ℤ) + 1))) :=
    {p | ⟪p.2, toL2F (memLp_single1 t hφ)⟫_ℝ = ⟪p.1, toL2F (memLp_formalAdj_single1 t hφ)⟫_ℝ}
  have hS : IsClosed S := isClosed_eq (continuous_snd.inner continuous_const)
    (continuous_fst.inner continuous_const)
  have hsub : ((dCore (Q (Fin n)) J (k : ℤ)).graph : Set _) ⊆ S := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hv, rfl⟩ := mem_graph_dCore.1 hxy
    exact inner_maximal_single1_of_vanishNear ⟨x, hx⟩ hv t hφ hadm
  have hu := (dPart (Q (Fin n)) J (k : ℤ)).mem_graph u
  rw [dPart_graph isOpen_Q, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hu
  exact closure_minimal hsub hS hu

theorem coeff_d_dPart (J : Finset (Fin n)) (k : ℕ) (u : (dPart (Q (Fin n)) J (k : ℤ)).domain)
    (m : Fin n → ℤ) :
    (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (Feec.Fourier.Torus.freq m)
        ((JfJ J k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m) =
      (JfJ J (k + 1) (dPart (Q (Fin n)) J (k : ℤ) u) :
        (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m :=
  coeff_d_of_greenForJ (greenForJ_dPart J k u) m

end GreenPart

/-! ### Smooth forms with vanishing tangential traces on the `J`-faces lie in `D(d_J)` -/

section Smooth

open RowWise (mN mN_pos exists_bound_deriv_smoothTransition)

theorem formExt_chiJ_mul (J : Finset (Fin n)) {k : ℤ} (ψ : formIdx n k → (Fin n → ℝ) → ℝ)
    (m : ℕ) (r : Finset (Fin n)) :
    formExt (fun p y => chiJ J m y * ψ p y) r = fun y => chiJ J m y * formExt ψ r y := by
  unfold formExt
  split_ifs
  · rfl
  · funext y; simp

/-- **Smooth forms with vanishing tangential trace on the faces normal to `J` lie in `D(d_J)`.** -/
theorem mem_dPart_of_smooth {J : Finset (Fin n)} {k : ℤ} {ψ : formIdx n k → (Fin n → ℝ) → ℝ}
    (hψ : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (ψ s)) {M : ℝ} (hM : ∀ s y, |ψ s y| ≤ M) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ s j y, |fderiv ℝ (ψ s) y (Pi.single j 1)| ≤ L)
    (hV : ∀ s j, j ∈ J → j ∉ s.1 → ∀ y : Fin n → ℝ, (y j = 0 ∨ y j = 1 / 2) → ψ s y = 0)
    (hψL : ∀ s, MemLp (ψ s) 2 (volume.restrict (Q (Fin n))))
    (hdψL : ∀ t, MemLp ((extDerivOp ℝ n k).apply ψ t) 2 (volume.restrict (Q (Fin n)))) :
    (toL2F hψL, toL2F hdψL) ∈ (dPart (Q (Fin n)) J k).graph := by
  obtain ⟨M₀, -, hM₀⟩ := exists_bound_deriv_smoothTransition
  have hM00 : 0 ≤ M₀ := (abs_nonneg _).trans (hM₀ 0)
  set Φ : ℕ → formIdx n k → (Fin n → ℝ) → ℝ := fun m p y => chiJ J m y * ψ p y
  have hΦs : ∀ m p, ContDiff ℝ (⊤ : ℕ∞) (Φ m p) := fun m p => (contDiff_chiJ J m).mul (hψ p)
  have hΦL : ∀ m p, MemLp (Φ m p) 2 (volume.restrict (Q (Fin n))) := fun m p =>
    Feec.Domain.memLp_of_continuous measurableSet_Q isBounded_Qn (hΦs m p).continuous
  have hdΦL : ∀ m t, MemLp ((extDerivOp ℝ n k).apply (Φ m) t) 2 (volume.restrict (Q (Fin n))) :=
    fun m t => Feec.Domain.memLp_of_continuous measurableSet_Q isBounded_Qn
      ((extDerivOp ℝ n k).continuous_apply (Feec.Domain.extDerivOp_isOrderLE k)
        (fun s => (hΦs m s).of_le (by exact_mod_cast le_top)) t)
  have hmem : ∀ m, (toL2F (hΦL m), toL2F (hdΦL m)) ∈ (dCore (Q (Fin n)) J k).graph := by
    intro m
    obtain ⟨h, e⟩ := Feec.Domain.extDerivOp_smooth_mem_maximal_domain (Ω := Q (Fin n)) isOpen_Q
      (fun s => (hΦs m s).of_le (by exact_mod_cast le_top)) (hΦL m) (hdΦL m)
    have hm2 := mN_pos m
    refine mem_graph_dCore.2 ⟨h, ⟨1 / (2 * mN m), by positivity, fun p => ?_⟩, e⟩
    filter_upwards [MemLp.coeFn_toLp (hΦL m p)] with y hy hyN
    change ((hΦL m p).toLp (Φ m p) : (Fin n → ℝ) → ℝ) y = 0
    rw [hy]
    obtain ⟨j, hj, hjy⟩ := hyN
    change chiJ J m y * ψ p y = 0
    rw [chiJ_eq_zero_of hj (hjy.imp le_of_lt le_of_lt), zero_mul]
  have hev : ∀ y ∈ Q (Fin n), ∀ᶠ m in atTop, ∀ p, (Φ m p) =ᶠ[𝓝 y] ψ p := fun y hy => by
    filter_upwards [eventually_chiJ_eq_one J hy] with m hm p
    filter_upwards [hm] with z hz
    simp [Φ, hz]
  have hFs : ∀ r, ContDiff ℝ ∞ (formExt ψ r) := Feec.Domain.contDiff_formExt hψ
  have hFd : ∀ r, Differentiable ℝ (formExt ψ r) := fun r => (hFs r).differentiable (by simp)
  have hFL : ∀ r j y, |fderiv ℝ (formExt ψ r) y (Pi.single j 1)| ≤ L := by
    intro r j y
    unfold formExt
    split_ifs with h
    · exact hL _ j y
    · simpa using hL0
  have hFV : ∀ r j, j ∈ J → j ∉ r → ∀ y : Fin n → ℝ, (y j = 0 ∨ y j = 1 / 2) →
      formExt ψ r y = 0 := by
    intro r j hjJ hj y hy
    unfold formExt
    split_ifs with h
    · exact hV _ j hjJ hj y hy
    · rfl
  rw [dPart_graph isOpen_Q, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine mem_closure_of_tendsto (b := (atTop : Filter ℕ))
    (f := fun m => (toL2F (hΦL m), toL2F (hdΦL m))) ?_ (Eventually.of_forall hmem)
  refine Tendsto.prodMk_nhds (tendsto_L2F_of_forall fun p => ?_)
    (tendsto_L2F_of_forall fun q => ?_)
  · refine tendsto_toLp_of_bdd (fun m => hΦL m p) (hψL p) (K := M) (fun m y _ => ?_)
      fun y hy => ?_
    · simp only [Φ, abs_mul]
      calc |chiJ J m y| * |ψ p y| ≤ 1 * M :=
            mul_le_mul (abs_chiJ_le_one J m y) (hM p y) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev y hy] with m hm
      exact (hm p).eq_of_nhds.symm
  · refine tendsto_toLp_of_bdd (fun m => hdΦL m q) (hdψL q)
      (K := ∑ _j : Fin n, (L + 4 * M₀ * L)) (fun m y hy => ?_) fun y hy => ?_
    · rw [Feec.Domain.extDerivOp_apply, Feec.Domain.extD]
      have hχd : Differentiable ℝ (chiJ J m) := (contDiff_chiJ J m).differentiable (by simp)
      have hterm : ∀ j ∈ q.1, |(ExteriorFibre.sgn j q.1 : ℝ) * fderiv ℝ (formExt (Φ m)
          (q.1.erase j)) y (Feec.Domain.coordDir j)| ≤ L + 4 * M₀ * L := by
        intro j hj
        rw [abs_mul, show |(ExteriorFibre.sgn j q.1 : ℝ)| = 1 by simp [ExteriorFibre.sgn],
          one_mul, show Φ m = fun p y => chiJ J m y * ψ p y from rfl, formExt_chiJ_mul,
          fderiv_fun_mul (hχd y) (hFd _ y)]
        simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
          calc |chiJ J m y| * |fderiv ℝ (formExt ψ (q.1.erase j)) y (Pi.single j 1)| ≤ 1 * L :=
                mul_le_mul (abs_chiJ_le_one J m y) (hFL _ j y) (abs_nonneg _) zero_le_one
            _ = L := one_mul L
        · rw [mul_comm]
          by_cases hjJ : j ∈ J
          · exact abs_fderiv_chiJ_mul_le hM₀ m (hFd _) hjJ (hFL _ j)
              (hFV _ j hjJ (Finset.notMem_erase j q.1)) hy
          · rw [fderiv_chiJ_of_notMem m hjJ y, zero_mul, abs_zero]; positivity
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => by
        positivity
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev y hy] with m hm
      exact (apply_congr_of_eventuallyEq _ hm q).symm

theorem exists_mem_dPart_of_smooth {J : Finset (Fin n)} {k : ℤ}
    {ψ : formIdx n k → (Fin n → ℝ) → ℝ} (hψ : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (ψ s)) {M : ℝ}
    (hM : ∀ s y, |ψ s y| ≤ M) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ s j y, |fderiv ℝ (ψ s) y (Pi.single j 1)| ≤ L)
    (hV : ∀ s j, j ∈ J → j ∉ s.1 → ∀ y : Fin n → ℝ, (y j = 0 ∨ y j = 1 / 2) → ψ s y = 0) :
    ∃ (hψL : ∀ s, MemLp (ψ s) 2 (volume.restrict (Q (Fin n))))
      (hdψL : ∀ t, MemLp ((extDerivOp ℝ n k).apply ψ t) 2 (volume.restrict (Q (Fin n)))),
      (toL2F hψL, toL2F hdψL) ∈ (dPart (Q (Fin n)) J k).graph := by
  have hψL : ∀ s, MemLp (ψ s) 2 (volume.restrict (Q (Fin n))) := fun s =>
    Feec.Domain.memLp_of_continuous measurableSet_Q isBounded_Qn (hψ s).continuous
  have hdψL : ∀ t, MemLp ((extDerivOp ℝ n k).apply ψ t) 2 (volume.restrict (Q (Fin n))) :=
    fun t => Feec.Domain.memLp_of_continuous measurableSet_Q isBounded_Qn
      ((extDerivOp ℝ n k).continuous_apply (Feec.Domain.extDerivOp_isOrderLE k)
        (fun s => (hψ s).of_le (by exact_mod_cast le_top)) t)
  exact ⟨hψL, hdψL, mem_dPart_of_smooth hψ hM hL0 hL hV hψL hdψL⟩

end Smooth

/-! ### The extension reflects the domains of `d_J` -/

section Converse

open Feec.Fourier.Torus (bandN finite_bandN)

open scoped Classical in
theorem realParJ_trunc {J : Finset (Fin n)} {k : ℕ}
    {x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))} (hx : RealParJ J k x)
    (N : ℕ) : RealParJ J k (trunc N k x) := by
  refine ⟨fun m t => ?_, fun j m t => ?_⟩
  · rw [coeFn_trunc, coeFn_trunc]
    by_cases hm : m ∈ bandN N
    · simp [hm, neg_mem_bandN.2 hm, hx.1 m t]
    · simp [hm, mt neg_mem_bandN.1 hm]
  · rw [coeFn_trunc, coeFn_trunc]
    by_cases hm : m ∈ bandN N
    · simp [hm, (Fourier.Torus.flipAt_mem_bandN j).2 hm, hx.2 j m t]
    · simp [hm, mt (Fourier.Torus.flipAt_mem_bandN j).1 hm]

theorem trigLift_eq_zero_of_faceJ {J : Finset (Fin n)} {k : ℕ}
    {x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))} (hx : RealParJ J k x)
    {S : Finset (Fin n → ℤ)} (hSr : ∀ j, ∀ m ∈ S, Fourier.Torus.flipAt j m ∈ S)
    {s : formIdx n (k : ℤ)} {j : Fin n} (hjJ : j ∈ J) (hj : j ∉ s.1) {y : Fin n → ℝ}
    (hy : y j = 0 ∨ y j = 1 / 2) : trigLift k x S s y = 0 := by
  have hf : ∀ m, mFourierBasis.repr (physF k x s) (flipB (single j) m) =
      -1 * mFourierBasis.repr (physF k x s) m := fun m => by
    have e : flipB (single j) m = Fourier.Torus.flipAt j m := flipB_single j m
    rw [e, repr_physF, repr_physF, hx.2]
    simp [DeRham.mixedSign, DeRham.reflSign, hj, hjJ]
  have h := trigPoly_reflB (ε := single j) (S := S)
    (fun m hm => by rw [show flipB (single j) m = Fourier.Torus.flipAt j m from flipB_single j m];
                    exact hSr j m hm) hf (proj y)
  rw [show reflB (single j) (proj y) = proj y from reflB_single_proj_of_face hy] at h
  have h0 : trigPoly (mFourierBasis.repr (physF k x s)) S (proj y) = 0 := by
    linear_combination h / 2
  simp [trigLift, h0]

theorem mem_dPart_of_JfJ {J : Finset (Fin n)} {k : ℕ}
    {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    {y : Lp (Form ℂ (Fin n) (k + 1)) 2 (Measure.count : Measure (Fin n → ℤ))}
    (h : ∀ m, (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (Feec.Fourier.Torus.freq m)
      ((JfJ J k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m) =
        (y : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m) :
    ∃ hu : u ∈ (dPart (Q (Fin n)) J (k : ℤ)).domain,
      JfJ J (k + 1) (dPart (Q (Fin n)) J (k : ℤ) ⟨u, hu⟩) = y := by
  set x := JfJ J k u
  have hx : RealParJ J k x := JfJ_realParJ J k u
  have hmem : ∀ N, (Jinvf k (trunc N k x), Jinvf (k + 1) (trunc N (k + 1) y)) ∈
      (dPart (Q (Fin n)) J (k : ℤ)).graph := by
    intro N
    have hxN := realParJ_trunc hx N
    obtain ⟨M, L, hL0, hM, hL⟩ := trigLift_bounds k (trunc N k x) (bandS N)
    have hcl := mem_dPart_of_smooth (J := J) (contDiff_trigLift k (trunc N k x) (bandS N))
      hM hL0 hL (fun s j hjJ hj y hy => trigLift_eq_zero_of_faceJ hxN
        (fun j m hm => flipAt_mem_bandS j hm) hjJ hj hy) (memLp_trigLift k _ _)
        (memLp_d_trigLift k _ _)
    rw [← Jinvf_eq_toL2F fun m hm => trunc_eq_zero_of_notMem x hm] at hcl
    obtain ⟨v, hv1, hv2⟩ := (LinearPMap.mem_graph_iff _).1 hcl
    have hd := coeff_d_dPart J k v
    have hJ : JfJ J (k + 1) (dPart (Q (Fin n)) J (k : ℤ) v) = trunc N (k + 1) y := by
      refine Lp.ext_count fun m => ?_
      rw [← hd m]
      rw [← symbol_trunc h N m, show (v : L2F ℝ (Q (Fin n)) _) = Jinvf k (trunc N k x) from hv1,
        JfJ_Jinvf hxN]
    rw [(LinearPMap.mem_graph_iff _)]
    refine ⟨v, hv1, ?_⟩
    rw [← hJ, Jinvf_JfJ]
  have hlim : Tendsto (fun N => (Jinvf k (trunc N k x), Jinvf (k + 1) (trunc N (k + 1) y)))
      atTop (𝓝 (Jinvf k x, Jinvf (k + 1) y)) :=
    Tendsto.prodMk_nhds (((Jinvf k).continuous.tendsto _).comp (tendsto_trunc k x))
      (((Jinvf (k + 1)).continuous.tendsto _).comp (tendsto_trunc (k + 1) y))
  have hg := (isClosed_dPart isOpen_Q J (k : ℤ)).mem_of_tendsto hlim (Eventually.of_forall hmem)
  rw [show Jinvf k x = u from Jinvf_JfJ J k u] at hg
  obtain ⟨v, hv1, -⟩ := (LinearPMap.mem_graph_iff _).1 hg
  have hu : u ∈ (dPart (Q (Fin n)) J (k : ℤ)).domain := by
    have : (v : L2F ℝ (Q (Fin n)) _) = u := hv1
    exact this ▸ v.2
  refine ⟨hu, Lp.ext_count fun m => ?_⟩
  rw [← coeff_d_dPart J k ⟨u, hu⟩ m]
  exact h m

/-- **Green's identity against the admissible smooth forms characterizes `D(d_J)`.** -/
theorem greenForJ_iff {J : Finset (Fin n)} {k : ℕ} {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    {w : L2F ℝ (Q (Fin n)) (formIdx n ((k : ℤ) + 1))} :
    GreenForJ J k u w ↔ ∃ h : u ∈ (dPart (Q (Fin n)) J (k : ℤ)).domain,
      dPart (Q (Fin n)) J (k : ℤ) ⟨u, h⟩ = w := by
  constructor
  · intro hG
    obtain ⟨h, e⟩ := mem_dPart_of_JfJ (J := J) (k := k) fun m => coeff_d_of_greenForJ hG m
    exact ⟨h, injective_JfJ J (k + 1) e⟩
  · rintro ⟨h, rfl⟩
    exact greenForJ_dPart J k ⟨u, h⟩

end Converse

/-! ### `HΛ_J(Q)` is the compression of the torus complex along the mixed extension -/

section Window

variable (n) in
/-- **The window of `HΛ_J(Q)`**: `HΛ_J⁰(Q) → ⋯ → HΛ_Jⁿ(Q)`. -/
abbrev HQpart (J : Finset (Fin n)) :
    HilbertComplex ℝ (ComplexShape.window (Fintype.card (Fin n) + 1)) (WQ n) :=
  (HQpartZ (isOpen_Q (d := Fin n)) subset_rfl J).restrict (ι n) ι_rel

theorem HQpart_d_succ (J : Finset (Fin n)) (a : Fin (Fintype.card (Fin n) + 1))
    (hb : (a : ℕ) + 1 < Fintype.card (Fin n) + 1) :
    (HQpart n J).d a ⟨(a : ℕ) + 1, hb⟩ = dPart (Q (Fin n)) J ((a : ℕ) : ℤ) :=
  HQpartZ_d isOpen_Q subset_rfl J ((a : ℕ) : ℤ)

theorem mapsTo_comm_part (J : Finset (Fin n)) (a b : Fin (Fintype.card (Fin n) + 1))
    (x : ((HQpart n J).d a b).domain) :
    ∃ h : JJ J a x ∈ ((RT n).d a b).domain,
      (RT n).d a b ⟨_, h⟩ = JJ J b ((HQpart n J).d a b x) := by
  by_cases hab : (ComplexShape.window (Fintype.card (Fin n) + 1)).Rel a b
  · obtain ⟨bv, hbv⟩ := b
    change (a : ℕ) + 1 = bv at hab
    subst hab
    have e := HQpart_d_succ J a hbv
    set x' : (dPart (Q (Fin n)) J ((a : ℕ) : ℤ)).domain := ⟨x.1, e ▸ x.2⟩
    have hx : (HQpart n J).d a ⟨(a : ℕ) + 1, hbv⟩ x = dPart (Q (Fin n)) J ((a : ℕ) : ℤ) x' :=
      apply_eq_of_eq e x x' rfl
    rw [hx]
    exact mem_RT_domain_of_pointwise fun m => coeff_d_dPart J (a : ℕ) x' m
  · have h0 := RT_d_zero hab
    refine ⟨by rw [h0]; exact Submodule.mem_top, ?_⟩
    rw [LinearPMap.apply_eq_zero_of_eq_zero h0,
      LinearPMap.apply_eq_zero_of_eq_zero ((HQpart n J).shape a b hab), _root_.map_zero]

theorem mem_domain_of_JJ_part (J : Finset (Fin n)) (a b : Fin (Fintype.card (Fin n) + 1))
    (x : WQ n a) (h : JJ J a x ∈ ((RT n).d a b).domain) : x ∈ ((HQpart n J).d a b).domain := by
  by_cases hab : (ComplexShape.window (Fintype.card (Fin n) + 1)).Rel a b
  · obtain ⟨bv, hbv⟩ := b
    change (a : ℕ) + 1 = bv at hab
    subst hab
    rw [HQpart_d_succ J a hbv]
    exact (mem_dPart_of_JfJ (u := x) (y := (RT n).d a ⟨(a : ℕ) + 1, hbv⟩ ⟨_, h⟩)
      fun m => (RT_d_apply ⟨_, h⟩ m).symm).1
  · rw [(HQpart n J).shape a b hab]; exact Submodule.mem_top

/-- **`HΛ_J(Q)` is the compression of the real torus de Rham window along the mixed extension.** -/
theorem HQpart_eq_compress (J : Finset (Fin n)) :
    HQpart n J = (RT n).compress (JJ J) two_pow_pos (inner_JJ J) (reducing_rangeJ J) := by
  refine Feec.HilbertComplex.ext_d (funext fun a => funext fun b => ?_)
  refine LinearPMap.ext (Submodule.ext fun x => ?_) fun x hx hx' => ?_
  · rw [Feec.HilbertComplex.mem_compress_domain_iff]
    exact ⟨fun h => (mapsTo_comm_part J a b ⟨x, h⟩).1, mem_domain_of_JJ_part J a b x⟩
  · refine injective_JfJ J (b : ℕ) ?_
    change JJ J b _ = JJ J b _
    rw [Feec.HilbertComplex.J_compress_d, ← (mapsTo_comm_part J a b ⟨x, hx⟩).2]

/-- **`d_univ = d_min` on `Q`**: vanishing tangential traces on all the faces is `H̊Λ(Q)`. -/
theorem dPart_univ (k : ℤ) :
    dPart (Q (Fin n)) Finset.univ k = (extDerivOp ℝ n k).minimal (Q (Fin n)) := by
  rcases k with k | k
  · show dPart (Q (Fin n)) Finset.univ ((k : ℕ) : ℤ) =
      (extDerivOp ℝ n ((k : ℕ) : ℤ)).minimal (Q (Fin n))
    refine LinearPMap.ext (Submodule.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
      fun x hx hx' => ?_
    · have := mem_minimal_of_Jf (u := x)
        (y := JfJ Finset.univ (k + 1) (dPart (Q (Fin n)) Finset.univ (k : ℤ) ⟨x, hx⟩))
        fun m => by rw [← JfJ_univ]; exact coeff_d_dPart Finset.univ k ⟨x, hx⟩ m
      exact this.1
    · have := mem_dPart_of_JfJ (J := Finset.univ) (u := x)
        (y := Jf true (k + 1) ((extDerivOp ℝ n (k : ℤ)).minimal (Q (Fin n)) ⟨x, hx⟩))
        fun m => by rw [JfJ_univ]; exact coeff_d_minimal true k ⟨x, hx⟩ m
      exact this.1
    · refine injective_JfJ Finset.univ (k + 1) (Lp.ext_count fun m => ?_)
      rw [← coeff_d_dPart Finset.univ k ⟨x, hx⟩ m, JfJ_univ, JfJ_univ,
        ← coeff_d_minimal true k ⟨x, hx'⟩ m]
  · have : Subsingleton (L2F ℝ (Q (Fin n)) (formIdx n (Int.negSucc k))) :=
      hlow _ _ (Int.negSucc_lt_zero k)
    refine LinearPMap.ext (Subsingleton.elim _ _) fun x hx hx' => ?_
    have h1 : (⟨x, hx⟩ : (dPart (Q (Fin n)) Finset.univ (Int.negSucc k)).domain) = 0 :=
      Subtype.ext (Subsingleton.elim _ _)
    have h2 : (⟨x, hx'⟩ :
        ((extDerivOp ℝ n (Int.negSucc k)).minimal (Q (Fin n))).domain) = 0 :=
      Subtype.ext (Subsingleton.elim _ _)
    rw [h1, h2, LinearPMap.map_zero, LinearPMap.map_zero]

end Window

/-! ### Hodge theory of `HΛ_J(Q)` -/

section Hodge

theorem HQpart_hasCompactProperty (J : Finset (Fin n)) : (HQpart n J).HasCompactProperty := by
  rw [HQpart_eq_compress]
  exact Feec.HilbertComplex.hasCompactProperty_compress two_pow_pos (inner_JJ J)
    (reducing_rangeJ J) RT_hasCompactProperty

theorem HQpart_norm_le (J : Finset (Fin n)) (a b : Fin (Fintype.card (Fin n) + 1))
    (u : ((HQpart n J).d a b).domain) (hu : (u : WQ n a) ∈ ((HQpart n J).d a b).kerᗮ) :
    ‖(u : WQ n a)‖ ≤ (2 * Real.pi)⁻¹ * ‖(HQpart n J).d a b u‖ := by
  have key : ∀ H' : HilbertComplex ℝ (ComplexShape.window (Fintype.card (Fin n) + 1)) (WQ n),
      H' = (RT n).compress (JJ J) two_pow_pos (inner_JJ J) (reducing_rangeJ J) →
      ∀ u : (H'.d a b).domain, (u : WQ n a) ∈ (H'.d a b).kerᗮ →
        ‖(u : WQ n a)‖ ≤ (2 * Real.pi)⁻¹ * ‖H'.d a b u‖ := by
    rintro _ rfl u hu
    exact Feec.HilbertComplex.norm_le_of_mem_orthogonal_compress two_pow_pos (inner_JJ J)
      (reducing_rangeJ J) (RT_norm_le a b) u hu
  exact key _ (HQpart_eq_compress J) u hu

theorem mem_HQpart_harmonic_iff {J : Finset (Fin n)} {a : Fin (Fintype.card (Fin n) + 1)}
    {x : WQ n a} :
    x ∈ (HQpart n J).harmonic a ↔
      ∀ m, m ≠ 0 → (JfJ J (a : ℕ) x : (Fin n → ℤ) → Form ℂ (Fin n) a) m = 0 := by
  rw [HQpart_eq_compress, Feec.HilbertComplex.mem_harmonic_compress_iff, mem_RT_harmonic_iff]
  rfl

theorem JfJ_zero_eq_zero_of_ne {J : Finset (Fin n)} {k : ℕ}
    (x : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) {t : {s : Finset (Fin n) // (#s : ℤ) = k}}
    (ht : t.1 ≠ J) : (JfJ J k x : (Fin n → ℤ) → Form ℂ (Fin n) k) 0 t = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, DeRham.mixedSign J j * DeRham.reflSign j t.1 ≠ 1 := by
    by_contra h
    push Not at h
    exact ht (DeRham.forall_mixedSign_mul_reflSign_eq_one_iff.1 h)
  have e := (JfJ_realParJ J k x).2 j 0 t
  rw [Fourier.Torus.flipAt_zero] at e
  by_contra hne
  exact hj (mul_right_cancel₀ hne (e.symm.trans (one_mul _).symm))

theorem HQpart_harmonic_eq_bot {J : Finset (Fin n)} {a : Fin (Fintype.card (Fin n) + 1)}
    (ha : (a : ℕ) ≠ #J) : (HQpart n J).harmonic a = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have hx' := mem_HQpart_harmonic_iff.1 hx
  refine injective_JfJ J (a : ℕ) ((Lp.ext_count fun m => ?_).trans (_root_.map_zero _).symm)
  rw [DeRham.coeFn_zero_count]
  by_cases hm : m = 0
  · subst hm
    ext t
    rw [JfJ_zero_eq_zero_of_ne x (fun h => ha (by
      have := t.2; rw [h] at this; exact_mod_cast this.symm))]
    rfl
  · exact hx' m hm

/-- The real part of the zero-mode coefficient `t₀` of the mixed extension. -/
def zeroCoeffJ (J : Finset (Fin n)) (k : ℕ) (t₀ : {s : Finset (Fin n) // (#s : ℤ) = k})
    (S : Submodule ℝ (L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)))) : S →ₗ[ℝ] ℝ where
  toFun x := ((JfJ J k x : (Fin n → ℤ) → Form ℂ (Fin n) k) 0 t₀).re
  map_add' x y := by
    simp only [Submodule.coe_add, _root_.map_add]
    rw [Measure.ae_count_iff.1 (Lp.coeFn_add _ _) 0]; simp
  map_smul' c x := by
    simp only [Submodule.coe_smul, _root_.map_smul, RingHom.id_apply, smul_eq_mul]
    rw [show (c • JfJ J k (x : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
        Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))) = (c : ℂ) • JfJ J k x
      from (RCLike.real_smul_eq_coe_smul c _), DeRham.coeFn_smul_count]
    simp

theorem injective_zeroCoeffJ {J : Finset (Fin n)} {k : ℕ} (hk : (#J : ℤ) = k)
    (S : Submodule ℝ (L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))))
    (hS : ∀ x ∈ S, ∀ m, m ≠ 0 → (JfJ J k x : (Fin n → ℤ) → Form ℂ (Fin n) k) m = 0) :
    Function.Injective (zeroCoeffJ J k ⟨J, hk⟩ S) := by
  intro x y hxy
  refine Subtype.ext (injective_JfJ J k (Lp.ext_count fun m => ?_))
  by_cases hm : m = 0
  · subst hm
    ext t
    by_cases ht : t.1 = J
    · obtain rfl : t = ⟨J, hk⟩ := Subtype.ext ht
      have hr : ∀ z : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)),
          (JfJ J k z : (Fin n → ℤ) → Form ℂ (Fin n) k) 0 ⟨J, hk⟩ =
            (((JfJ J k z : (Fin n → ℤ) → Form ℂ (Fin n) k) 0 ⟨J, hk⟩).re : ℂ) := fun z => by
        have e := (JfJ_realParJ J k z).1 0 ⟨J, hk⟩
        rw [neg_zero] at e
        exact (Complex.conj_eq_iff_re.1 e.symm).symm
      rw [hr x, hr y]
      exact congrArg (fun r : ℝ => (r : ℂ)) hxy
    · rw [JfJ_zero_eq_zero_of_ne _ ht, JfJ_zero_eq_zero_of_ne _ ht]
  · rw [hS _ x.2 m hm, hS _ y.2 m hm]

theorem finiteDimensional_of_zeroCoeffJ {J : Finset (Fin n)} {k : ℕ} (hk : (#J : ℤ) = k)
    (S : Submodule ℝ (L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))))
    (hS : ∀ x ∈ S, ∀ m, m ≠ 0 → (JfJ J k x : (Fin n → ℤ) → Form ℂ (Fin n) k) m = 0) :
    FiniteDimensional ℝ S :=
  Module.Finite.of_injective _ (injective_zeroCoeffJ hk S hS)

theorem finrank_le_one_of_zeroCoeffJ {J : Finset (Fin n)} {k : ℕ} (hk : (#J : ℤ) = k)
    (S : Submodule ℝ (L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))))
    (hS : ∀ x ∈ S, ∀ m, m ≠ 0 → (JfJ J k x : (Fin n → ℤ) → Form ℂ (Fin n) k) m = 0) :
    Module.finrank ℝ S ≤ 1 := by
  have := finiteDimensional_of_zeroCoeffJ hk S hS
  calc Module.finrank ℝ S ≤ Module.finrank ℝ ℝ :=
        LinearMap.finrank_le_finrank_of_injective (injective_zeroCoeffJ hk S hS)
    _ = 1 := Module.finrank_self ℝ

/-! ### The complex `HΛ_J(Q)` on `ℤ` -/

variable (n) in
/-- `HΛ_J(Q)` on `ℤ`. -/
abbrev Hpart (J : Finset (Fin n)) :
    HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ (Q (Fin n)) (formIdx n k) :=
  HQpartZ (isOpen_Q (d := Fin n)) subset_rfl J

/-- **The Poincaré inequality of `HΛ_J(Q)`**: `‖z‖ ≤ (2π)⁻¹ ‖d z‖` on `D(d) ∩ (𝔷ⁱ)ᗮ`. -/
theorem Hpart_norm_le (J : Finset (Fin n)) {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (z : ((Hpart n J).d i j).domain)
    (hz : (z : L2F ℝ (Q (Fin n)) (formIdx n i)) ∈ ((Hpart n J).cycles i)ᗮ) :
    ‖(z : L2F ℝ (Q (Fin n)) (formIdx n i))‖ ≤ (2 * Real.pi)⁻¹ * ‖(Hpart n J).d i j z‖ :=
  Feec.HilbertComplex.norm_le_of_mem_orthogonal_cycles_of_window (Hpart n J) ι_rel
    (by positivity) (hlow _) (hhigh _) (fun a b u hu => HQpart_norm_le J a b u hu) hij z hz

/-- **The compactness property of `HΛ_J(Q)`**, every degree. -/
theorem Hpart_hasCompactProperty (J : Finset (Fin n)) : (Hpart n J).HasCompactProperty :=
  Feec.HilbertComplex.hasCompactProperty_of_window (Hpart n J) ι_rel (hlow _) (hhigh _)
    (HQpart_hasCompactProperty J)

theorem Hpart_closedRangeAt (J : Finset (Fin n)) (j : ℤ) : (Hpart n J).ClosedRangeAt j :=
  ((Hpart n J).closedRangeAt_iff_poincare_of_rel (rel_sub_one j)).2
    ⟨_, Hpart_norm_le J (rel_sub_one j)⟩

theorem Hpart_harmonic_eq_bot {J : Finset (Fin n)} {k : ℤ} (hk : k ≠ (#J : ℤ)) :
    (Hpart n J).harmonic k = ⊥ :=
  harmonic_eq_bot_of_window ι_rel fun m hm e =>
    HQpart_harmonic_eq_bot (a := ⟨m, hm⟩) (by change m ≠ #J; omega)

theorem constForm_mem_dPart (J : Finset (Fin n)) {k : ℤ} (hk : (#J : ℤ) = k) :
    ∃ h : constForm measurableSet_Q (isBounded_openCube _ _) (⟨J, hk⟩ : formIdx n k) ∈
      (dPart (Q (Fin n)) J k).domain, dPart (Q (Fin n)) J k ⟨_, h⟩ = 0 := by
  have hmem := mem_dPart_of_smooth (J := J) (k := k)
    (ψ := constFun (⟨J, hk⟩ : formIdx n k)) (fun _ => contDiff_const)
    (M := 1) (fun s y => by unfold constFun; split_ifs <;> simp) le_rfl
    (fun s j y => by unfold constFun; rw [fderiv_const_apply]; simp)
    (fun s j hjJ hj y _ => by
      unfold constFun
      split_ifs with hs
      · subst hs; exact absurd hjJ hj
      · rfl)
    (memLp_constFun measurableSet_Q (isBounded_openCube _ _) _)
    (fun t => Feec.Domain.memLp_of_continuous measurableSet_Q (isBounded_openCube _ _)
      ((extDerivOp ℝ n k).continuous_apply (Feec.Domain.extDerivOp_isOrderLE _)
        (fun _ => contDiff_const) t))
  obtain ⟨v, hv1, hv2⟩ := (LinearPMap.mem_graph_iff _).1 hmem
  simp only at hv1 hv2
  have hv1' : (v : L2F ℝ (Q (Fin n)) (formIdx n k)) =
      constForm measurableSet_Q (isBounded_openCube _ _) (⟨J, hk⟩ : formIdx n k) := hv1
  have hmemc : constForm measurableSet_Q (isBounded_openCube _ _) (⟨J, hk⟩ : formIdx n k) ∈
      (dPart (Q (Fin n)) J k).domain := hv1' ▸ v.2
  refine ⟨hmemc, ?_⟩
  rw [show (⟨_, hmemc⟩ : (dPart (Q (Fin n)) J k).domain) = v from
    Subtype.ext hv1'.symm, hv2]
  exact toL2F_eq_zero (fun t y => extDerivOp_apply_const _ t y) _

theorem constForm_mem_harmonic (J : Finset (Fin n)) {k : ℤ} (hk : (#J : ℤ) = k) :
    constForm measurableSet_Q (isBounded_openCube _ _) (⟨J, hk⟩ : formIdx n k) ∈
      (Hpart n J).harmonic k := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by ring⟩
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [(Hpart n J).cycles_eq (show (ComplexShape.up ℤ).Rel (q + 1) (q + 1 + 1) from rfl),
      HQpartZ_d]
    obtain ⟨h, e⟩ := constForm_mem_dPart J hk
    exact mem_ker_iff.2 ⟨⟨_, h⟩, rfl, e⟩
  · rw [Feec.HilbertComplex.mem_ker_adjoint_prev_iff (Hpart n J)
      (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl), HQpartZ_d]
    set c := constForm measurableSet_Q (isBounded_openCube _ _) (⟨J, hk⟩ : formIdx n (q + 1))
    have hc : ∀ x : (dPart (Q (Fin n)) J q).domain,
        ⟪(0 : L2F ℝ (Q (Fin n)) (formIdx n q)), (x : L2F ℝ (Q (Fin n)) (formIdx n q))⟫_ℝ =
          ⟪c, dPart (Q (Fin n)) J q x⟫_ℝ := by
      intro x
      rw [inner_zero_left]
      rcases lt_or_ge q 0 with hq | hq
      · have : Subsingleton (L2F ℝ (Q (Fin n)) (formIdx n q)) := hlow _ _ hq
        rw [show x = 0 from Subtype.ext (Subsingleton.elim _ _), LinearPMap.map_zero,
          inner_zero_right]
      · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hq
        have hG := greenForJ_dPart J p x ⟨J, hk⟩ (fun _ => 1) contDiff_const ⟨1, fun y => by simp⟩
          ⟨0, fun j y => by rw [fderiv_const_apply]; simp⟩ (fun j hj hjJ => (hjJ hj).elim)
        simp only [fderiv_const_apply, _root_.zero_apply, mul_zero, integral_zero,
          Finset.sum_const_zero, neg_zero, mul_one] at hG
        rw [real_inner_comm]
        simp only [c, constForm]
        rw [Feec.Domain.inner_toL2F,
          Finset.sum_eq_single (⟨J, hk⟩ : formIdx n ((p : ℤ) + 1))
            (fun s _ hs => by simp [constFun, hs]) (by simp)]
        simp only [constFun, ite_true, starRingEnd_apply, star_trivial, mul_one]
        exact hG.symm
    have hdom : c ∈ ((dPart (Q (Fin n)) J q)†).domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨0, hc⟩
    refine mem_ker_iff.2 ⟨⟨c, hdom⟩, rfl, ?_⟩
    exact LinearPMap.adjoint_apply_eq (dense_dPart isOpen_Q subset_rfl J q) _ hc

variable (n) in
/-- **The constant form `dx_J`** on `Q`, a `|J|`-form. -/
abbrev formJ (J : Finset (Fin n)) : L2F ℝ (Q (Fin n)) (formIdx n (#J : ℤ)) :=
  constForm measurableSet_Q (isBounded_openCube _ _) ⟨J, rfl⟩

theorem formJ_ne_zero (J : Finset (Fin n)) : formJ n J ≠ 0 :=
  constForm_ne_zero _ _ volume_Q_ne_zero _

theorem Hpart_harmonic_card_spec (J : Finset (Fin n)) :
    FiniteDimensional ℝ ((Hpart n J).harmonic (#J : ℤ)) ∧
      Module.finrank ℝ ((Hpart n J).harmonic (#J : ℤ)) ≤ 1 := by
  have hJn : #J < Fintype.card (Fin n) + 1 := Nat.lt_succ_of_le (Finset.card_le_univ J)
  set a : Fin (Fintype.card (Fin n) + 1) := ⟨#J, hJn⟩
  have key : FiniteDimensional ℝ ((Hpart n J).harmonic ((a : ℕ) : ℤ)) ∧
      Module.finrank ℝ ((Hpart n J).harmonic ((a : ℕ) : ℤ)) ≤ 1 := by
    have hS : ∀ x ∈ (Hpart n J).harmonic ((a : ℕ) : ℤ), ∀ m, m ≠ 0 →
        (JfJ J (a : ℕ) x : (Fin n → ℤ) → Form ℂ (Fin n) a) m = 0 := fun x hx =>
      mem_HQpart_harmonic_iff.1 (Feec.HilbertComplex.harmonic_le_window (Hpart n J) ι_rel a hx)
    exact ⟨finiteDimensional_of_zeroCoeffJ (k := (a : ℕ)) rfl _ hS,
      finrank_le_one_of_zeroCoeffJ (k := (a : ℕ)) rfl _ hS⟩
  exact key

/-- **The harmonic `|J|`-forms of `HΛ_J(Q)` are the line of the constant form `dx_J`.** -/
theorem Hpart_harmonic_card (J : Finset (Fin n)) :
    (Hpart n J).harmonic (#J : ℤ) = ℝ ∙ formJ n J := by
  obtain ⟨hfin, hle⟩ := Hpart_harmonic_card_spec J
  have hne := formJ_ne_zero J
  have hmem : formJ n J ∈ (Hpart n J).harmonic (#J : ℤ) := constForm_mem_harmonic J rfl
  have hpos : Module.finrank ℝ ((Hpart n J).harmonic (#J : ℤ)) ≠ 0 := fun h0 => by
    have := (Submodule.finrank_eq_zero (S := (Hpart n J).harmonic (#J : ℤ))).1 h0
    exact hne (by simpa [this] using hmem)
  exact eq_span_singleton_of_mem_of_finrank_eq_one (by omega) hmem hne

theorem finrank_Hpart_harmonic (J : Finset (Fin n)) (k : ℤ) :
    Module.finrank ℝ ((Hpart n J).harmonic k) = if k = (#J : ℤ) then 1 else 0 := by
  split_ifs with hk
  · subst hk
    rw [Hpart_harmonic_card, finrank_span_singleton (formJ_ne_zero J)]
  · rw [Hpart_harmonic_eq_bot hk, finrank_bot]

instance finiteDimensional_Hpart_harmonic (J : Finset (Fin n)) (k : ℤ) :
    FiniteDimensional ℝ ((Hpart n J).harmonic k) := by
  by_cases hk : k = (#J : ℤ)
  · subst hk; rw [Hpart_harmonic_card]; infer_instance
  · rw [Hpart_harmonic_eq_bot hk]; infer_instance

/-- **The cohomology of `HΛ_J(Q)`**: `Hᵏ ≅ ℝ` for `k = |J|`, `0` otherwise. -/
theorem finrank_Hpart_cohomology (J : Finset (Fin n)) (k : ℤ) :
    Module.finrank ℝ ((Hpart n J).cohomology k) = if k = (#J : ℤ) then 1 else 0 := by
  rw [((Hpart n J).cohomologyEquivHarmonic (Hpart_closedRangeAt J k)).finrank_eq,
    finrank_Hpart_harmonic]

end Hodge

end Feec.Models.Cube.DeRhamIdent
