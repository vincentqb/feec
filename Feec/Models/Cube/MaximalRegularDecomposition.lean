module

public import Feec.Domain.OfReal
public import Feec.Models.Cube.Sobolev

/-!
# The regular decompositions of `HΛ((0, ½)ⁿ)`

On `Q = (0, ½)ⁿ` the complex `HΛ(Q)` has the regular decompositions of [ArnoldHu2021], §2,
Theorem 3 (`deRham_hasRegularDecomposition_Q`), and so do its `𝕜ᵐ`-valued versions on `Q ⊆ ℝ³`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open MeasureTheory

@[expose] public noncomputable section

namespace Feec.Models.Cube.Sobolev

open Feec.Domain Feec.HilbertComplex Feec.Models.Cube.DeRhamIdent
open Feec.Models.Cube.Geometry (Q isOpen_Q)

variable {n : ℕ}

/-! ### Gaffney's identity in the absolute class -/

/-- **Gaffney's identity on the torus window**:
`Σ_m (1 + |ξ_m|²) |y(m)|² = ‖y‖² + ‖d y‖² + ‖d* y‖²`. -/
theorem gaffney_RT (a : Fin (Fintype.card (Fin n) + 1)) {y : TW n a}
    (h1 : y ∈ ((RT n).d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a)).domain)
    (h2 : y ∈ (((RT n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)†).domain) :
    MemSob 1 (y : Seq n a) ∧
      sobSum 1 (y : Seq n a) = ‖y‖ ^ 2 +
        ‖(RT n).d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a) ⟨y, h1⟩‖ ^ 2 +
        ‖((RT n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)† ⟨y, h2⟩‖ ^ 2 := by
  have h2' : y ∈ (((Torus.DeRham.window (Fin n)).d
      ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)†).domain := by
    have := h2; rw [RT_adjoint] at this; exact this
  have eadj : ((RT n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)† ⟨y, h2⟩ =
      ((Torus.DeRham.window (Fin n)).d
        ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)† ⟨y, h2'⟩ :=
    LinearPMap.apply_eq_of_eq (RT_adjoint _ a) ⟨y, h2⟩ ⟨y, h2'⟩ rfl
  have h2'' : y ∈ (Operator.mulOp (Measure.count : Measure (Fin n → ℤ)) fun k =>
      ContinuousLinearMap.adjoint ((Torus.DeRham.windowSymbol (Fin n)).m
        ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a k)).domain := by
    have := h2'; rw [Fourier.SymbolComplex.adjoint_d] at this; exact this
  have eadj2 : ((Torus.DeRham.window (Fin n)).d
      ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)† ⟨y, h2'⟩ =
      Operator.mulOp (Measure.count : Measure (Fin n → ℤ)) (fun k =>
        ContinuousLinearMap.adjoint ((Torus.DeRham.windowSymbol (Fin n)).m
          ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a k)) ⟨y, h2''⟩ :=
    LinearPMap.apply_eq_of_eq (Fourier.SymbolComplex.adjoint_d _ _ a) _ _ rfl
  have hpt2 : ∀ m, cf (((RT n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)†
      ⟨y, h2⟩ : Seq n _) m = ContinuousLinearMap.adjoint ((Feec.Fourier.Exterior.deRham (Fin n)).m
        ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a (Fourier.Torus.freq m))
          (cf (y : Seq n a) m) := by
    intro m
    change ((((RT n).d _ a)† ⟨y, h2⟩ : TW n _) : (Fin n → ℤ) → _) m = _
    rw [eadj, eadj2]
    exact Operator.coeFn_mulOp_count _ ⟨y, h2''⟩ m
  have hpt1 : ∀ m, cf ((RT n).d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a)
      ⟨y, h1⟩ : Seq n _) m = (Feec.Fourier.Exterior.deRham (Fin n)).m a
        ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a) (Fourier.Torus.freq m)
          (cf (y : Seq n a) m) := fun m => RT_d_apply ⟨y, h1⟩ m
  have hc : ∀ m, weight 1 m * ‖cf (y : Seq n a) m‖ ^ 2 = ‖cf (y : Seq n a) m‖ ^ 2 +
      ‖cf ((RT n).d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a)
        ⟨y, h1⟩ : Seq n _) m‖ ^ 2 +
      ‖cf (((RT n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)†
        ⟨y, h2⟩ : Seq n _) m‖ ^ 2 := by
    intro m
    rw [weight_one, hpt1, hpt2]
    have := Torus.DeRham.window_cartan a (Fourier.Torus.freq m) (cf (y : Seq n a) m)
    linear_combination -this
  have hs : Summable fun m => ‖cf (y : Seq n a) m‖ ^ 2 +
      ‖cf ((RT n).d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a)
        ⟨y, h1⟩ : Seq n _) m‖ ^ 2 +
      ‖cf (((RT n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)†
        ⟨y, h2⟩ : Seq n _) m‖ ^ 2 :=
    ((summable_norm_sq _).add (summable_norm_sq _)).add (summable_norm_sq _)
  refine ⟨?_, ?_⟩
  · exact hs.congr fun m => (hc m).symm
  · unfold sobSum
    rw [tsum_congr hc, ((summable_norm_sq _).add (summable_norm_sq _)).tsum_add
      (summable_norm_sq _), (summable_norm_sq _).tsum_add (summable_norm_sq _),
      ← norm_sq_eq_tsum, ← norm_sq_eq_tsum, ← norm_sq_eq_tsum]

theorem memSob_one_of_mem_HQmax {a b c : Fin (Fintype.card (Fin n) + 1)}
    (hb : (ComplexShape.window (Fintype.card (Fin n) + 1)).next a = b)
    (hc : (ComplexShape.window (Fintype.card (Fin n) + 1)).prev a = c) {x : WQ n a}
    (h1 : x ∈ ((HQmax n).d a b).domain) (h2 : x ∈ (((HQmax n).d c a)†).domain) :
    MemSob 1 (J false a x : Seq n a) := by
  subst hb hc
  rw [HQmax_eq_compress] at h1 h2
  exact (gaffney_RT a ((Feec.HilbertComplex.mem_compress_domain_iff two_pow_pos (inner_J false)
    (reducing_range false)).1 h1) ((Feec.HilbertComplex.mem_adjoint_compress_iff two_pow_pos
      (inner_J false) (reducing_range false)).1 h2)).1

/-! ### `H¹(Q)` forms are `H¹` fields -/

theorem zeroF_mem_fieldH1 {f : L2 ℝ (Q (Fin n))}
    (hf : zeroF f ∈ ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))).domain) :
    zeroF f ∈ fieldH1 ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ)) := by
  refine ConstCoeffOp.maximal_domain_le_of_apply_eq isOpen_Q
    (L := Matrix.of fun rl (t : formIdx n (((0 : ℕ) : ℤ) + 1)) => if t.1 = {rl.2} then 1 else 0)
    (fun g _ => ?_) hf
  funext rl x
  rw [fieldGradOp_apply, ConstCoeffOp.ofMatrix_apply,
    Finset.sum_eq_single ⟨{rl.2}, by simp⟩ (fun t _ ht => by
      rw [Matrix.of_apply, ite_eq_right fun h => ht (Subtype.ext h), zero_mul]) (by simp)]
  simp only [Matrix.of_apply, ite_true, one_mul]
  rw [show rl.1 = ⟨∅, by simp⟩ from Subtype.ext (Finset.card_eq_zero.1 (by exact_mod_cast rl.1.2))]
  exact (extDerivOp_zero_apply g rl.2 x).symm

theorem sobolevQ_one_le_fieldH1 (k : ℕ) :
    sobolevQ n k 1 ≤ fieldH1 ℝ (Q (Fin n)) (formIdx n (k : ℤ)) := by
  intro u hu
  have hc := (mem_sobolevQ_one_iff (k := k)).1 hu
  let E : formIdx n (k : ℤ) → Matrix (formIdx n (k : ℤ)) (formIdx n ((0 : ℕ) : ℤ)) ℝ :=
    fun t => Matrix.of fun s _ => if s = t then 1 else 0
  have hu : u = ∑ t, L2F.ofMatrixCLM (E t) (zeroF (u t)) := by
    refine (WithLp.ext_iff 2).2 (funext fun s => ?_)
    change u s = (∑ t, L2F.ofMatrixCLM (E t) (zeroF (u t))) s
    rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single s (fun t _ ht => ?_) (by simp)]
    · rw [L2F.ofMatrixCLM_apply]
      simp only [E, Matrix.of_apply, ite_true, one_smul]
      rw [Finset.sum_eq_single (⟨∅, by simp⟩ : formIdx n ((0 : ℕ) : ℤ)) (fun r _ hr => absurd
        (Subtype.ext (Finset.card_eq_zero.1 (by exact_mod_cast r.2))) hr) (by simp)]
      rfl
    · rw [L2F.ofMatrixCLM_apply]
      exact Finset.sum_eq_zero fun r _ => by simp [E, Ne.symm ht]
  rw [hu]
  exact Submodule.sum_mem _ fun t _ => ofMatrixCLM_mem_fieldH1 isOpen_Q _ (zeroF_mem_fieldH1 (hc t))

/-! ### The regular decompositions -/

theorem mem_HQmax_domain_next {m : ℕ} (hm : m + 1 < Fintype.card (Fin n) + 1)
    {u : L2F ℝ (Q (Fin n)) (formIdx n ((m : ℤ) + 1))}
    (hu : u ∈ ((extDerivOp ℝ n ((m : ℤ) + 1)).maximal (Q (Fin n))).domain) :
    (show WQ n ⟨m + 1, hm⟩ from u) ∈ ((HQmax n).d ⟨m + 1, hm⟩
      ((ComplexShape.window (Fintype.card (Fin n) + 1)).next ⟨m + 1, hm⟩)).domain := by
  by_cases h : m + 2 < Fintype.card (Fin n) + 1
  · rw [(ComplexShape.window (Fintype.card (Fin n) + 1)).next_eq' (i := ⟨m + 1, hm⟩)
      (j := ⟨m + 2, h⟩) rfl,
      HQmax_d_succ ⟨m + 1, hm⟩ h]
    exact hu
  · rw [(HQmax n).shape _ _ fun hr => h (by
      have := ((ComplexShape.window (Fintype.card (Fin n) + 1)).next ⟨m + 1, hm⟩).2
      change m + 1 + 1 = _ at hr; omega)]
    exact Submodule.mem_top

/-- **The regular decompositions of `HΛ(Q)`** ([ArnoldHu2021], §2, Theorem 3): every
`u ∈ HΛᵏ⁺¹(Q)` is `d p + w` with `p ∈ HΛᵏ(Q)` and `w` an `H¹` field. -/
theorem deRham_hasRegularDecomposition_Q :
    (deRham ℝ n).HasRegularDecomposition (Q (Fin n)) 0 := by
  intro i hi u hu
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  by_cases hm : m + 1 < Fintype.card (Fin n) + 1
  swap
  · have : IsEmpty ((deRham ℝ n).ι ((m : ℤ) + 1)) :=
      isEmpty_formIdx_of_gt (by simp only [Fintype.card_fin] at hm ⊢; omega)
    exact ⟨0, mem_fieldH1_of_isEmpty _⟩
  let c : Fin (Fintype.card (Fin n) + 1) := ⟨m, by omega⟩
  let a : Fin (Fintype.card (Fin n) + 1) := ⟨m + 1, hm⟩
  have hca : (ComplexShape.window (Fintype.card (Fin n) + 1)).Rel c a := rfl
  have hT : (HQmax n).d c a = (extDerivOp ℝ n (m : ℤ)).maximal (Q (Fin n)) := HQmax_d_succ c hm
  have hcr : (HQmax n).ClosedRangeAt a := ((HQmax n).closedRangeAt_iff_poincare_of_rel hca).2
    ⟨_, fun x hx => HQmax_norm_le c a x ((HQmax n).cycles_eq hca ▸ hx)⟩
  have : CompleteSpace ((HQmax n).boundaries a) := hcr.completeSpace_coe
  let u' : WQ n a := u
  obtain ⟨p, hp⟩ : ((HQmax n).boundaries a).starProjection u' ∈
      LinearMap.range ((HQmax n).d c a).toFun :=
    (HQmax n).boundaries_eq hca ▸ Submodule.starProjection_apply_mem _ u'
  set b := ((HQmax n).boundaries a).starProjection u'
  have hv2 : u' - b ∈ (((HQmax n).d c a)†).domain := by
    have hK : ((HQmax n).boundaries a)ᗮ = ((HQmax n).d c a)†.ker := by
      rw [(HQmax n).boundaries_eq hca,
        LinearPMap.orthogonal_range_eq_ker_adjoint _ ((HQmax n).dense c a)]
    have h := Submodule.sub_starProjection_mem_orthogonal (K := (HQmax n).boundaries a) u'
    rw [hK] at h
    obtain ⟨y, hy, -⟩ := LinearPMap.mem_ker_iff.1 h
    rw [show u' - b = y from hy]
    exact y.2
  have hb : b ∈ ((HQmax n).d a
      ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a)).domain := by
    obtain ⟨y, hy, -⟩ := LinearPMap.mem_ker_iff.1
      ((HQmax n).boundaries_le_cycles a (Submodule.starProjection_apply_mem _ u'))
    rw [show b = y from hy]
    exact y.2
  have hv1 := Submodule.sub_mem _ (mem_HQmax_domain_next hm hu) hb
  have hsob := memSob_one_of_mem_HQmax rfl
    ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev_eq' hca) hv1 hv2
  refine ⟨⟨p.1, hT ▸ p.2⟩, ?_⟩
  have hpb : (extDerivOp ℝ n (m : ℤ)).maximal (Q (Fin n)) ⟨p.1, hT ▸ p.2⟩ = b :=
    (LinearPMap.apply_eq_of_eq hT.symm _ p rfl).trans hp
  change u' - (show WQ n a from
    (extDerivOp ℝ n (m : ℤ)).maximal (Q (Fin n)) ⟨p.1, hT ▸ p.2⟩) ∈
    fieldH1 ℝ (Q (Fin n)) (formIdx n ((m + 1 : ℕ) : ℤ))
  rw [hpb]
  exact sobolevQ_one_le_fieldH1 (m + 1) ⟨_, hsob, Jinvf_Jf false (m + 1) _⟩

/-- **The regular decompositions of the de Rham complexes of `Q ⊆ ℝ³` with values in `𝕜ᵐ`.** -/
theorem deRhamVec_hasRegularDecomposition_Q {𝕜 : Type*} [RCLike 𝕜] (m : ℕ) :
    (deRhamVec 𝕜 m).HasRegularDecomposition (Q (Fin 3)) 0 :=
  deRhamVec_ofReal (𝕜 := 𝕜) m ▸
    (deRhamVec_hasRegularDecomposition isOpen_Q deRham_hasRegularDecomposition_Q m).ofReal isOpen_Q

end Feec.Models.Cube.Sobolev
