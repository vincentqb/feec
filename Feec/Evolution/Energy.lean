module

public import Feec.Evolution.Solution

/-!
# Energy estimates

Energy estimates for curves in inner product spaces and for strong solutions of `U' = A U + F`:
continuous dependence on data and forcing for dissipative `A`, and, without forcing, energy
conservation for skew-symmetric `A`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set

@[expose] public noncomputable section

namespace Feec.Evolution.Energy

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

omit [IsScalarTower ℝ 𝕜 E] in
theorem norm_le_add_integral_of_re_inner_deriv_le {e e' : ℝ → E} {g : ℝ → ℝ} {a b : ℝ}
    (hec : ContinuousOn e (Icc a b)) (he : ∀ t ∈ Ico a b, HasDerivWithinAt e (e' t) (Ici t) t)
    (hgc : ContinuousOn g (Icc a b)) (hg0 : ∀ t ∈ Ico a b, 0 ≤ g t)
    (hle : ∀ t ∈ Ico a b, RCLike.re ⟪e' t, e t⟫ ≤ g t * ‖e t‖) :
    ∀ t ∈ Icc a b, ‖e t‖ ≤ ‖e a‖ + ∫ s in a..t, g s :=
  _root_.norm_le_add_integral_of_re_inner_deriv_le (𝕜 := 𝕜) hec he hgc hg0 hle

/-- **Energy estimate with decay rate `λ`**: `re ⟪e', e⟫ ≤ -λ ‖e‖² + g ‖e‖` gives
`‖e t‖ ≤ e^{-λ(t-a)} ‖e a‖ + ∫ₐᵗ e^{-λ(t-s)} g s`. [QuennevilleBelair2015], Lemma 4.12 (adapted) -/
theorem norm_le_of_re_inner_deriv_le {e e' : ℝ → E} {g : ℝ → ℝ} {a b lam : ℝ}
    (hec : ContinuousOn e (Icc a b)) (he : ∀ t ∈ Ico a b, HasDerivWithinAt e (e' t) (Ici t) t)
    (hgc : ContinuousOn g (Icc a b)) (hg0 : ∀ t ∈ Ico a b, 0 ≤ g t)
    (hle : ∀ t ∈ Ico a b, RCLike.re ⟪e' t, e t⟫ ≤ -lam * ‖e t‖ ^ 2 + g t * ‖e t‖) :
    ∀ t ∈ Icc a b, ‖e t‖ ≤ Real.exp (-lam * (t - a)) * ‖e a‖ +
      ∫ s in a..t, Real.exp (-lam * (t - s)) * g s :=
  _root_.norm_le_of_re_inner_deriv_le (𝕜 := 𝕜) hec he hgc hg0 hle

omit [IsScalarTower ℝ 𝕜 E] in
theorem norm_le_of_re_inner_deriv_nonpos {e e' : ℝ → E} {a b : ℝ}
    (hec : ContinuousOn e (Icc a b)) (he : ∀ t ∈ Ico a b, HasDerivWithinAt e (e' t) (Ici t) t)
    (hle : ∀ t ∈ Ico a b, RCLike.re ⟪e' t, e t⟫ ≤ 0) : ∀ t ∈ Icc a b, ‖e t‖ ≤ ‖e a‖ := by
  intro t ht
  simpa using norm_le_add_integral_of_re_inner_deriv_le (𝕜 := 𝕜) (g := fun _ => 0) hec he
    continuousOn_const (fun _ _ => le_rfl) (fun s hs => by simpa using hle s hs) t ht

end Feec.Evolution.Energy

namespace Feec.Evolution.IsStrongSolution

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] {A : E →ₗ.[𝕜] E} {I : Set ℝ} {F G U V : ℝ → E} {a b : ℝ}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem hasDerivWithinAt_norm_sq (hU : IsStrongSolution A I F U) {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt (fun s => ‖U s‖ ^ 2)
      (2 * RCLike.re ⟪A ⟨U t, hU.mem_domain ht⟩ + F t, U t⟫) I t :=
  (hU.hasDerivWithinAt ht).norm_sq_re_inner

/-- **Continuous dependence on the data** for a dissipative generator:
`‖U t - V t‖ ≤ ‖U a - V a‖ + ∫ₐᵗ ‖F s - G s‖` on `[a,b]`. -/
theorem norm_sub_le_add_integral (hA : A.IsDissipative) (hU : IsStrongSolution A (Icc a b) F U)
    (hV : IsStrongSolution A (Icc a b) G V) (hFG : ContinuousOn (F - G) (Icc a b)) :
    ∀ t ∈ Icc a b, ‖U t - V t‖ ≤ ‖U a - V a‖ + ∫ s in a..t, ‖F s - G s‖ := by
  have hW := hU.sub hV
  refine norm_le_add_integral_of_re_inner_deriv_le (𝕜 := 𝕜) (e := U - V)
    (e' := fun s => if h : s ∈ Icc a b then A ⟨(U - V) s, hW.mem_domain h⟩ + (F - G) s else 0)
    (g := fun s => ‖F s - G s‖) hW.continuousOn (fun s hs => ?_) hFG.norm
    (fun _ _ => norm_nonneg _) (fun s hs => ?_)
  · rw [dite_eq_left (Ico_subset_Icc_self hs)]
    exact hW.hasDerivWithinAt_Ici hs
  · rw [dite_eq_left (Ico_subset_Icc_self hs), inner_add_left, map_add]
    have h1 := hA ⟨(U - V) s, hW.mem_domain (Ico_subset_Icc_self hs)⟩
    have h2 : RCLike.re ⟪(F - G) s, (U - V) s⟫ ≤ ‖F s - G s‖ * ‖(U - V) s‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    simp only [Pi.sub_apply] at h1 h2 ⊢
    linarith

theorem norm_le_add_integral (hA : A.IsDissipative) (hU : IsStrongSolution A (Icc a b) F U)
    (hF : ContinuousOn F (Icc a b)) : ∀ t ∈ Icc a b, ‖U t‖ ≤ ‖U a‖ + ∫ s in a..t, ‖F s‖ := by
  simpa using hU.norm_sub_le_add_integral hA zero (by simpa using hF)

theorem norm_le (hA : A.IsDissipative) (hU : IsStrongSolution A (Icc a b) 0 U) :
    ∀ t ∈ Icc a b, ‖U t‖ ≤ ‖U a‖ := by
  simpa using hU.norm_le_add_integral hA continuousOn_const

/-- **Energy conservation** `‖U t‖ = ‖U a‖` for `U' = A U`, `A` skew-symmetric. -/
theorem norm_eq (hA : A.IsSkewSymmetric) (hU : IsStrongSolution A (Icc a b) 0 U) :
    ∀ t ∈ Icc a b, ‖U t‖ = ‖U a‖ := by
  have h := constant_of_has_deriv_right_zero (f := fun s => ‖U s‖ ^ 2) (hU.continuousOn.norm.pow 2)
    fun s hs => by
      have := (hU.hasDerivWithinAt_norm_sq (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hs)
      rwa [Pi.zero_apply, add_zero, hA.re_inner_self, mul_zero] at this
  intro t ht
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (h t ht)

end Feec.Evolution.IsStrongSolution
