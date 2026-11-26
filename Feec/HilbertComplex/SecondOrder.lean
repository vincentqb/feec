module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Feec.HilbertComplex.HodgeWave

/-!
# Mixed and second-order weak forms of the Hodge wave equation

For `d : W₀ → W₁`, the mixed weak form `(u̇, v) = -(ρ, d v)`, `(ρ̇, μ) = (d u, μ)` of the Hodge wave
equation implies the second-order form `(ü, v) = -(d u, d v)`, and conversely under the
compatibility condition `u̇(a) = -d* ρ₀`; the three-field mixed form eliminates `ρ` likewise.

## Main results

* `HodgeWave.IsMixedWeak.isSecondOrderWeak`: mixed solutions solve the second-order form.
* `HodgeWave.IsSecondOrderWeak.exists_isMixedWeak`: the converse under the compatibility condition.
* `HodgeWave.not_isMixedWeak_of_inner_ne_zero`: a necessary condition.
* `HodgeWave.IsMixedWeak3.eliminate`: the elimination of `ρ` from the three-field form.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [T. Geveci, *On the application of mixed finite element methods to the wave equations*][Geveci1988]
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]
* [G. A. Baker, *Error estimates for finite element methods for second order hyperbolic equations*][Baker1976]
* [T. Dupont, *L²-estimates for Galerkin methods for second order hyperbolic equations*][Dupont1973]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set

@[expose] public noncomputable section

namespace Feec.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜]

theorem eq_of_hasDerivWithinAt_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a b : ℝ} (h : ∀ t ∈ Icc a b, HasDerivWithinAt f 0 (Icc a b) t) :
    ∀ t ∈ Icc a b, f t = f a :=
  constant_of_has_deriv_right_zero (fun t ht => (h t ht).continuousWithinAt) fun t ht =>
    (h t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-! ### The two-space segment (§4.8) -/

section ScalarWave

variable {W₀ W₁ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [NormedSpace ℝ W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [NormedSpace ℝ W₁]

/-- **Mixed weak form** on `I`: `(u̇, v) = -(ρ, d v)` for `v ∈ V₀` and `(ρ̇, μ) = (d u, μ)` for
`μ ∈ W₁`. [QuennevilleBelair2015], §4.8; [Geveci1988]; [GilletteHolstZhu2017] -/
structure IsMixedWeak (d : W₀ →ₗ.[𝕜] W₁) (I : Set ℝ) (w : ℝ → d.domain) (u' : ℝ → W₀)
    (ρ ρ' : ℝ → W₁) : Prop where
  du : ∀ t ∈ I, HasDerivWithinAt (fun s => (w s : W₀)) (u' t) I t
  cont : ContinuousOn (fun s => d (w s)) I
  dρ : ∀ t ∈ I, HasDerivWithinAt ρ (ρ' t) I t
  eq_u : ∀ t ∈ I, ∀ v : d.domain, ⟪u' t, (v : W₀)⟫_𝕜 = -⟪ρ t, d v⟫_𝕜
  eq_ρ : ∀ t ∈ I, ∀ μ : W₁, ⟪ρ' t, μ⟫_𝕜 = ⟪d (w t), μ⟫_𝕜

/-- **Second-order weak form** on `I`: `t ↦ (u̇, v)` has derivative `-(d u, d v)` for `v ∈ V₀`.
[QuennevilleBelair2015], §4.8; [Baker1976]; [Dupont1973] -/
structure IsSecondOrderWeak (d : W₀ →ₗ.[𝕜] W₁) (I : Set ℝ) (w : ℝ → d.domain) (u' : ℝ → W₀) :
    Prop where
  du : ∀ t ∈ I, HasDerivWithinAt (fun s => (w s : W₀)) (u' t) I t
  cont : ContinuousOn (fun s => d (w s)) I
  eq : ∀ t ∈ I, ∀ v : d.domain,
    HasDerivWithinAt (fun s => ⟪u' s, (v : W₀)⟫_𝕜) (-⟪d (w t), d v⟫_𝕜) I t

variable {d : W₀ →ₗ.[𝕜] W₁} {I : Set ℝ} {w : ℝ → d.domain} {u' : ℝ → W₀} {ρ ρ' : ℝ → W₁}

theorem IsMixedWeak.deriv_eq (h : IsMixedWeak d I w u' ρ ρ') {t : ℝ} (ht : t ∈ I) :
    ρ' t = d (w t) := by
  have := h.eq_ρ t ht (ρ' t - d (w t))
  rw [← sub_eq_zero, ← inner_sub_left] at this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

theorem IsMixedWeak.inner_deriv_ker (h : IsMixedWeak d I w u' ρ ρ') {t : ℝ} (ht : t ∈ I)
    (z : d.domain) (hz : d z = 0) : ⟪u' t, (z : W₀)⟫_𝕜 = 0 := by
  rw [h.eq_u t ht z, hz, inner_zero_right, neg_zero]

/-- **Mixed ⇒ second order**: the `u` of a mixed weak solution solves the second-order weak form.
[QuennevilleBelair2015], §4.8 -/
theorem IsMixedWeak.isSecondOrderWeak (h : IsMixedWeak d I w u' ρ ρ') :
    IsSecondOrderWeak d I w u' := by
  refine ⟨h.du, h.cont, fun t ht v => ?_⟩
  have h1 := ((h.dρ t ht).inner 𝕜 (hasDerivWithinAt_const t I (d v))).neg
  refine (h1.congr_of_mem (fun s hs => ?_) ht).congr_deriv ?_
  · rw [h.eq_u s hs v]; rfl
  · rw [inner_zero_right, zero_add, h.deriv_eq ht]

/-- **A necessary condition**: if `(u̇(a), z) ≠ 0` for some `z ∈ ker d`, no mixed weak solution
has this `u`. [QuennevilleBelair2015], §4.8 (adapted) -/
theorem not_isMixedWeak_of_inner_ne_zero {a : ℝ} (ha : a ∈ I) (z : d.domain) (hz : d z = 0)
    (hu : ⟪u' a, (z : W₀)⟫_𝕜 ≠ 0) : ¬ ∃ ρ ρ', IsMixedWeak d I w u' ρ ρ' := by
  rintro ⟨ρ, ρ', h⟩
  exact hu (h.inner_deriv_ker ha z hz)

theorem IsMixedWeak.eqOn_of_eq {a b : ℝ} {ρ₂ ρ₂' : ℝ → W₁}
    (h₁ : IsMixedWeak d (Icc a b) w u' ρ ρ') (h₂ : IsMixedWeak d (Icc a b) w u' ρ₂ ρ₂')
    (h0 : ρ a = ρ₂ a) : EqOn ρ ρ₂ (Icc a b) := by
  intro t ht
  have hd : ∀ s ∈ Icc a b, HasDerivWithinAt (fun s => ρ s - ρ₂ s) 0 (Icc a b) s := by
    intro s hs
    have := (h₁.dρ s hs).sub (h₂.dρ s hs)
    rwa [h₁.deriv_eq hs, h₂.deriv_eq hs, sub_self] at this
  have := eq_of_hasDerivWithinAt_zero hd t ht
  rw [h0, sub_self] at this
  exact sub_eq_zero.1 this

variable [CompleteSpace W₁]

/-- **Second order ⇒ mixed** under the compatibility condition: if `u̇(a) = -d* ρ₀` weakly, `u` is
the `u` of a mixed weak solution with `ρ(a) = ρ₀`. [QuennevilleBelair2015], §4.8 (adapted) -/
theorem IsSecondOrderWeak.exists_isMixedWeak {a b : ℝ} (hab : a ≤ b)
    (h : IsSecondOrderWeak d (Icc a b) w u') (ρ₀ : W₁)
    (hρ₀ : ∀ v : d.domain, ⟪u' a, (v : W₀)⟫_𝕜 = -⟪ρ₀, d v⟫_𝕜) :
    ∃ ρ ρ' : ℝ → W₁, IsMixedWeak d (Icc a b) w u' ρ ρ' ∧ ρ a = ρ₀ := by
  set g : ℝ → W₁ := fun s => d (w (projIcc a b hab s)) with hg
  have hgc : Continuous g := h.cont.comp_continuous (continuous_subtype_val.comp
    continuous_projIcc) (fun s => (projIcc a b hab s).2)
  have hgt : ∀ t ∈ Icc a b, g t = d (w t) := fun t ht => by simp [g, projIcc_of_mem hab ht]
  set ρ : ℝ → W₁ := fun t => ρ₀ + ∫ s in a..t, g s
  have hρd : ∀ t ∈ Icc a b, HasDerivWithinAt ρ (d (w t)) (Icc a b) t := fun t ht => by
    rw [← hgt t ht]
    exact ((hgc.integral_hasStrictDerivAt a t).hasDerivAt.const_add ρ₀).hasDerivWithinAt
  refine ⟨ρ, fun t => d (w t), ⟨h.du, h.cont, hρd, fun t ht v => ?_, fun t ht μ => rfl⟩,
    by simp [ρ]⟩
  have hc := eq_of_hasDerivWithinAt_zero
    (f := fun s => ⟪u' s, (v : W₀)⟫_𝕜 + ⟪ρ s, d v⟫_𝕜) (fun s hs => by
      have h1 := (hρd s hs).inner 𝕜 (hasDerivWithinAt_const s (Icc a b) (d v))
      refine ((h.eq s hs v).add h1).congr_deriv ?_
      rw [inner_zero_right, zero_add, neg_add_cancel]) t ht
  have h0 : ⟪u' a, (v : W₀)⟫_𝕜 + ⟪ρ a, d v⟫_𝕜 = 0 := by simp [ρ, hρ₀ v]
  rw [h0] at hc
  exact eq_neg_of_add_eq_zero_left hc

end ScalarWave

/-! ### The three-space segment (§4.9) -/

section VectorWave

variable {W₀ W₁ W₂ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [NormedSpace ℝ W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [NormedSpace ℝ W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [NormedSpace ℝ W₂]

/-- **Three-field mixed weak form** of `V₀ --d₀--> V₁ --d₁--> W₂`: `(σ̇, τ) = (u, d₀ τ)`,
`(u̇, v) = -(ρ, d₁ v) - (d₀ σ, v)`, `(ρ̇, μ) = (d₁ u, μ)`. [QuennevilleBelair2015], (4.12) -/
structure IsMixedWeak3 (d₀ : W₀ →ₗ.[𝕜] W₁) (d₁ : W₁ →ₗ.[𝕜] W₂) (I : Set ℝ) (σ : ℝ → d₀.domain)
    (σ' : ℝ → W₀) (w : ℝ → d₁.domain) (u' : ℝ → W₁) (ρ ρ' : ℝ → W₂) : Prop where
  dσ : ∀ t ∈ I, HasDerivWithinAt (fun s => (σ s : W₀)) (σ' t) I t
  du : ∀ t ∈ I, HasDerivWithinAt (fun s => (w s : W₁)) (u' t) I t
  dρ : ∀ t ∈ I, HasDerivWithinAt ρ (ρ' t) I t
  eq_σ : ∀ t ∈ I, ∀ τ : d₀.domain, ⟪σ' t, (τ : W₀)⟫_𝕜 = ⟪(w t : W₁), d₀ τ⟫_𝕜
  eq_u : ∀ t ∈ I, ∀ v : d₁.domain,
    ⟪u' t, (v : W₁)⟫_𝕜 = -⟪ρ t, d₁ v⟫_𝕜 - ⟪d₀ (σ t), (v : W₁)⟫_𝕜
  eq_ρ : ∀ t ∈ I, ∀ μ : W₂, ⟪ρ' t, μ⟫_𝕜 = ⟪d₁ (w t), μ⟫_𝕜

variable {d₀ : W₀ →ₗ.[𝕜] W₁} {d₁ : W₁ →ₗ.[𝕜] W₂} {I : Set ℝ} {σ : ℝ → d₀.domain} {σ' : ℝ → W₀}
  {w : ℝ → d₁.domain} {u' : ℝ → W₁} {ρ ρ' : ℝ → W₂}

/-- **Elimination of `ρ`** from (4.12): `(σ̇, τ) = (u, d₀ τ)` and
`d/dt [(u̇, v) + (d₀ σ, v)] = -(d₁ u, d₁ v)`. [QuennevilleBelair2015], §4.9 (adapted) -/
theorem IsMixedWeak3.eliminate (h : IsMixedWeak3 d₀ d₁ I σ σ' w u' ρ ρ') :
    (∀ t ∈ I, ∀ τ : d₀.domain, ⟪σ' t, (τ : W₀)⟫_𝕜 = ⟪(w t : W₁), d₀ τ⟫_𝕜) ∧
      ∀ t ∈ I, ∀ v : d₁.domain, HasDerivWithinAt
        (fun s => ⟪u' s, (v : W₁)⟫_𝕜 + ⟪d₀ (σ s), (v : W₁)⟫_𝕜) (-⟪d₁ (w t), d₁ v⟫_𝕜) I t := by
  refine ⟨h.eq_σ, fun t ht v => ?_⟩
  have h1 := ((h.dρ t ht).inner 𝕜 (hasDerivWithinAt_const t I (d₁ v))).neg
  refine (h1.congr_of_mem (fun s hs => ?_) ht).congr_deriv ?_
  · rw [h.eq_u s hs v, Pi.neg_apply, sub_add_cancel]
  · rw [inner_zero_right, zero_add, h.eq_ρ t ht]

theorem IsMixedWeak3.eliminate_of_hasDerivWithinAt (h : IsMixedWeak3 d₀ d₁ I σ σ' w u' ρ ρ')
    {g : ℝ → W₁} (hg : ∀ t ∈ I, HasDerivWithinAt (fun s => d₀ (σ s)) (g t) I t) :
    ∀ t ∈ I, ∀ v : d₁.domain, HasDerivWithinAt (fun s => ⟪u' s, (v : W₁)⟫_𝕜)
      (-⟪d₁ (w t), d₁ v⟫_𝕜 - ⟪g t, (v : W₁)⟫_𝕜) I t := by
  intro t ht v
  have h2 := (hg t ht).inner 𝕜 (hasDerivWithinAt_const t I (v : W₁))
  have := (h.eliminate.2 t ht v).sub h2
  convert this using 1
  · funext s; simp
  · simp

end VectorWave

end Feec.HodgeWave
