module

public import Feec.Evolution.Energy

/-!
# Error bound skeleton for Galerkin approximations of evolution problems

The energy-method error estimate of a semi-discrete Galerkin scheme: a bound
`re ⟪ε', ε⟫ ≤ -λ ‖ε‖² + g ‖ε‖` on the projected error `ε = p − uₕ` bounds `u − uₕ`, and for an
accretive form and an elliptic projection this gives the error estimate of the scheme.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set

@[expose] public noncomputable section

namespace Feec.Variational

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **Galerkin error bound with decay rate `λ`**: `re ⟪ε', ε⟫ ≤ -λ ‖ε‖² + g ‖ε‖` for `ε = p − uₕ`
gives `‖u t − uₕ t‖ ≤ ‖u t − p t‖ + e^{-λ(t-a)} ‖p a − uₕ a‖ + ∫ₐᵗ e^{-λ(t-s)} g s`.
[QuennevilleBelair2015], Thm 4.14 -/
theorem norm_sub_le_of_projected_error_decay {u p uh ε' : ℝ → E} {g : ℝ → ℝ} {a b lam : ℝ}
    (hεc : ContinuousOn (fun t => p t - uh t) (Icc a b))
    (hε : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => p t - uh t) (ε' t) (Ici t) t)
    (hgc : ContinuousOn g (Icc a b)) (hg0 : ∀ t ∈ Ico a b, 0 ≤ g t)
    (herr : ∀ t ∈ Ico a b,
      RCLike.re ⟪ε' t, p t - uh t⟫ ≤ -lam * ‖p t - uh t‖ ^ 2 + g t * ‖p t - uh t‖) :
    ∀ t ∈ Icc a b, ‖u t - uh t‖ ≤ ‖u t - p t‖ + Real.exp (-lam * (t - a)) * ‖p a - uh a‖ +
      ∫ s in a..t, Real.exp (-lam * (t - s)) * g s := by
  intro t ht
  have h := Evolution.Energy.norm_le_of_re_inner_deriv_le (𝕜 := 𝕜) hεc hε hgc hg0 herr t ht
  calc ‖u t - uh t‖ = ‖(u t - p t) + (p t - uh t)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖u t - p t‖ + ‖p t - uh t‖ := norm_add_le _ _
    _ ≤ _ := by linarith

theorem norm_sub_le_of_projected_error {u p uh ε' : ℝ → E} {g : ℝ → ℝ} {a b : ℝ}
    (hεc : ContinuousOn (fun t => p t - uh t) (Icc a b))
    (hε : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => p t - uh t) (ε' t) (Ici t) t)
    (hgc : ContinuousOn g (Icc a b)) (hg0 : ∀ t ∈ Ico a b, 0 ≤ g t)
    (herr : ∀ t ∈ Ico a b, RCLike.re ⟪ε' t, p t - uh t⟫ ≤ g t * ‖p t - uh t‖) :
    ∀ t ∈ Icc a b, ‖u t - uh t‖ ≤ ‖u t - p t‖ + ‖p a - uh a‖ + ∫ s in a..t, g s := by
  intro t ht
  have h := norm_sub_le_of_projected_error_decay (𝕜 := 𝕜) (u := u) (lam := 0) hεc hε hgc hg0
    (fun s hs => by simpa using herr s hs) t ht
  simpa using h

namespace GalerkinEvolution

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V]
  [IsScalarTower ℝ 𝕜 V]

omit [IsScalarTower ℝ 𝕜 E] in
variable (𝕜) in
include 𝕜 in
theorem integral_norm_le {e e' : ℝ → E} {a b : ℝ} (hec : ContinuousOn e (Icc a b))
    (he : ∀ t ∈ Ico a b, HasDerivWithinAt e (e' t) (Ici t) t)
    (he'c : ContinuousOn e' (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b) :
    ∫ s in a..t, ‖e s‖ ≤ (t - a) * (‖e a‖ + ∫ s in a..t, ‖e' s‖) := by
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hu : uIcc a t ⊆ Icc a b := by rw [uIcc_of_le ht.1]; exact hsub
  have hI1 : IntervalIntegrable (fun s => ‖e' s‖) MeasureTheory.volume a t :=
    (he'c.norm.mono hu).intervalIntegrable
  have hI2 : IntervalIntegrable (fun s => ‖e s‖) MeasureTheory.volume a t :=
    (hec.norm.mono hu).intervalIntegrable
  have hmono : ∀ s ∈ Icc a t, ‖e s‖ ≤ ‖e a‖ + ∫ r in a..t, ‖e' r‖ := by
    intro s hs
    have := Evolution.Energy.norm_le_add_integral_of_re_inner_deriv_le (𝕜 := 𝕜)
      (g := fun r => ‖e' r‖) hec he he'c.norm (fun _ _ => norm_nonneg _)
      (fun r _ => (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)) s (hsub hs)
    have hle : ∫ r in a..s, ‖e' r‖ ≤ ∫ r in a..t, ‖e' r‖ :=
      intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) hI1
    linarith
  have := intervalIntegral.integral_mono_on ht.1 hI2 intervalIntegrable_const hmono
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using this

/-- **Error bound for semi-discrete Galerkin schemes** `⟪J ψ, J ξ'⟫ + a ξ ψ = 0`, `a` accretive on
`K`, `P` an elliptic projection: `‖J (ξ − ξₕ)‖ ≤ ‖e‖ + ‖J (P ξ(t₀) − ξₕ(t₀))‖ + ∫ (‖e'‖ + ‖e‖)`,
`e = J (P ξ − ξ)`. [QuennevilleBelair2015], Thm 4.14 -/
theorem error_bound (J : V →L[𝕜] E) (a : V → V → 𝕜)
    (ha_sub : ∀ x y ψ, a (x - y) ψ = a x ψ - a y ψ) (K : Submodule 𝕜 V)
    (ha : ∀ ψ ∈ K, 0 ≤ RCLike.re (a ψ ψ)) (P : V →L[𝕜] V) (hPK : ∀ ζ, P ζ ∈ K)
    (hP : ∀ ζ, ∀ ψ ∈ K, ⟪J ψ, J (P ζ - ζ)⟫ + a (P ζ - ζ) ψ = 0)
    {ξ ξ' ξh ξh' : ℝ → V} {t₀ t₁ : ℝ}
    (hξc : ContinuousOn ξ (Icc t₀ t₁)) (hξ'c : ContinuousOn ξ' (Icc t₀ t₁))
    (hξd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt ξ (ξ' t) (Ici t) t)
    (hξ : ∀ t ∈ Ico t₀ t₁, ∀ ψ ∈ K, ⟪J ψ, J (ξ' t)⟫ + a (ξ t) ψ = 0)
    (hξhc : ContinuousOn ξh (Icc t₀ t₁)) (hξhK : ∀ t ∈ Icc t₀ t₁, ξh t ∈ K)
    (hξhd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt ξh (ξh' t) (Ici t) t)
    (hξh : ∀ t ∈ Ico t₀ t₁, ∀ ψ ∈ K, ⟪J ψ, J (ξh' t)⟫ + a (ξh t) ψ = 0) :
    ∀ t ∈ Icc t₀ t₁, ‖J (ξ t - ξh t)‖ ≤ ‖J (P (ξ t) - ξ t)‖ + ‖J (P (ξ t₀) - ξh t₀)‖ +
      ∫ s in t₀..t, (‖J (P (ξ' s) - ξ' s)‖ + ‖J (P (ξ s) - ξ s)‖) := by
  have hJP : ContinuousOn (fun t => J (P (ξ t) - ξ t)) (Icc t₀ t₁) :=
    J.continuous.comp_continuousOn ((P.continuous.comp_continuousOn hξc).sub hξc)
  have hJP' : ContinuousOn (fun t => J (P (ξ' t) - ξ' t)) (Icc t₀ t₁) :=
    J.continuous.comp_continuousOn ((P.continuous.comp_continuousOn hξ'c).sub hξ'c)
  have h := norm_sub_le_of_projected_error (𝕜 := 𝕜) (u := fun t => J (ξ t))
    (p := fun t => J (P (ξ t))) (uh := fun t => J (ξh t))
    (ε' := fun t => J (P (ξ' t)) - J (ξh' t))
    (g := fun t => ‖J (P (ξ' t) - ξ' t)‖ + ‖J (P (ξ t) - ξ t)‖)
    ((J.continuous.comp_continuousOn (P.continuous.comp_continuousOn hξc)).sub
      (J.continuous.comp_continuousOn hξhc))
    (fun t ht => (((J.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      ((P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hξd t ht))).sub
      ((J.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hξhd t ht))))
    (hJP'.norm.add hJP.norm) (fun _ _ => by positivity) (fun t ht => by
      show RCLike.re ⟪J (P (ξ' t)) - J (ξh' t), J (P (ξ t)) - J (ξh t)⟫ ≤
        (‖J (P (ξ' t) - ξ' t)‖ + ‖J (P (ξ t) - ξ t)‖) * ‖J (P (ξ t)) - J (ξh t)‖
      set ψ := P (ξ t) - ξh t
      have hψ : ψ ∈ K := K.sub_mem (hPK _) (hξhK t (Ico_subset_Icc_self ht))
      have E1 := hξ t ht ψ hψ
      have E2 := hξh t ht ψ hψ
      have E3 := hP (ξ t) ψ hψ
      have hεψ : J (P (ξ t)) - J (ξh t) = J ψ := (map_sub J _ _).symm
      have key : ⟪J ψ, J (P (ξ' t)) - J (ξh' t)⟫ =
          ⟪J ψ, J (P (ξ' t) - ξ' t)⟫ - ⟪J ψ, J (P (ξ t) - ξ t)⟫ - a ψ ψ := by
        have e1 : a ψ ψ = a (P (ξ t) - ξ t) ψ + a (ξ t) ψ - a (ξh t) ψ := by
          have h1 := ha_sub (P (ξ t) - ξ t) (ξh t - ξ t) ψ
          have h2 := ha_sub (ξh t) (ξ t) ψ
          rw [show (P (ξ t) - ξ t) - (ξh t - ξ t) = ψ by simp only [ψ]; abel] at h1
          linear_combination h1 - h2
        rw [e1]
        simp only [map_sub, inner_sub_right] at E1 E2 E3 ⊢
        linear_combination E1 - E2 + E3
      rw [hεψ, inner_re_symm, key, _root_.map_sub, _root_.map_sub]
      have b1 : RCLike.re ⟪J ψ, J (P (ξ' t) - ξ' t)⟫ ≤ ‖J (P (ξ' t) - ξ' t)‖ * ‖J ψ‖ := by
        rw [mul_comm]; exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
      have b2 : -RCLike.re ⟪J ψ, J (P (ξ t) - ξ t)⟫ ≤ ‖J (P (ξ t) - ξ t)‖ * ‖J ψ‖ := by
        have := RCLike.re_le_norm (-⟪J ψ, J (P (ξ t) - ξ t)⟫)
        rw [_root_.map_neg, norm_neg] at this
        exact this.trans (by rw [mul_comm]; exact norm_inner_le_norm _ _)
      have b3 := ha ψ hψ
      linarith)
  intro t ht
  have := h t ht
  simp only [map_sub] at this ⊢
  rw [norm_sub_rev (J (P (ξ t))) (J (ξ t))]
  exact this

theorem error_bound_refined (J : V →L[𝕜] E) (a : V → V → 𝕜)
    (ha_sub : ∀ x y ψ, a (x - y) ψ = a x ψ - a y ψ) (K : Submodule 𝕜 V)
    (ha : ∀ ψ ∈ K, 0 ≤ RCLike.re (a ψ ψ)) (P : V →L[𝕜] V) (hPK : ∀ ζ, P ζ ∈ K)
    (hP : ∀ ζ, ∀ ψ ∈ K, ⟪J ψ, J (P ζ - ζ)⟫ + a (P ζ - ζ) ψ = 0)
    {ξ ξ' ξh ξh' : ℝ → V} {t₀ t₁ : ℝ}
    (hξc : ContinuousOn ξ (Icc t₀ t₁)) (hξ'c : ContinuousOn ξ' (Icc t₀ t₁))
    (hξd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt ξ (ξ' t) (Ici t) t)
    (hξ : ∀ t ∈ Ico t₀ t₁, ∀ ψ ∈ K, ⟪J ψ, J (ξ' t)⟫ + a (ξ t) ψ = 0)
    (hξhc : ContinuousOn ξh (Icc t₀ t₁)) (hξhK : ∀ t ∈ Icc t₀ t₁, ξh t ∈ K)
    (hξhd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt ξh (ξh' t) (Ici t) t)
    (hξh : ∀ t ∈ Ico t₀ t₁, ∀ ψ ∈ K, ⟪J ψ, J (ξh' t)⟫ + a (ξh t) ψ = 0) :
    ∀ t ∈ Icc t₀ t₁, ‖J (ξ t - ξh t)‖ ≤ ‖J (P (ξ t₀) - ξh t₀)‖ + ‖J (P (ξ t) - ξ t)‖ +
      (t - t₀) * ‖J (P (ξ t₀) - ξ t₀)‖ +
      (1 + (t - t₀)) * ∫ s in t₀..t, ‖J (P (ξ' s) - ξ' s)‖ := by
  intro t ht
  have h := error_bound J a ha_sub K ha P hPK hP hξc hξ'c hξd hξ hξhc hξhK hξhd hξh t ht
  have hu : uIcc t₀ t ⊆ Icc t₀ t₁ := by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  have hec : ContinuousOn (fun t => J (P (ξ t) - ξ t)) (Icc t₀ t₁) :=
    J.continuous.comp_continuousOn ((P.continuous.comp_continuousOn hξc).sub hξc)
  have he'c : ContinuousOn (fun t => J (P (ξ' t) - ξ' t)) (Icc t₀ t₁) :=
    J.continuous.comp_continuousOn ((P.continuous.comp_continuousOn hξ'c).sub hξ'c)
  have hed : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => J (P (ξ t) - ξ t))
      (J (P (ξ' t) - ξ' t)) (Ici t) t := fun t ht =>
    (J.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (((P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hξd t ht)).sub (hξd t ht))
  have hsplit : ∫ s in t₀..t, (‖J (P (ξ' s) - ξ' s)‖ + ‖J (P (ξ s) - ξ s)‖) =
      (∫ s in t₀..t, ‖J (P (ξ' s) - ξ' s)‖) + ∫ s in t₀..t, ‖J (P (ξ s) - ξ s)‖ :=
    intervalIntegral.integral_add (he'c.norm.mono hu).intervalIntegrable
      (hec.norm.mono hu).intervalIntegrable
  have hE := integral_norm_le 𝕜 hec hed he'c ht
  rw [hsplit] at h
  nlinarith [ht.1]

end GalerkinEvolution

end Feec.Variational
