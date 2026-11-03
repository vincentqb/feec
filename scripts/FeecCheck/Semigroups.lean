module

public import Feec.Semigroup.DissipativeInvariance
public import Feec.TimeStepping.StableFamily
public import Feec.Semigroup.HilleYosida

/-!
# Regression test: the semigroup layer before the shared limit argument

The exponential lemmas `Feec.C0Group.exp_ofReal_smul_add`, `C0Group.continuous_exp_ofReal_smul`,
`C0Group.commute_exp_ofReal_smul` and the aliases `C0Group.hasDerivAt_exp_ofReal_smul_apply`,
`Feec.TimeStepping.hasDerivAt_exp_sub_smul_apply` are now the `ContinuousLinearMap` lemmas of
`Feec.ForMathlib.Analysis.ExpFlow`; Stone's theorem and the Lumer–Phillips theorem share one limit
argument (`Feec.ForMathlib.Analysis.ExpLimit`: `ContinuousLinearMap.cauchySeq_exp_apply`,
`ContinuousLinearMap.sub_eq_integral_of_tendsto_exp`, …), so
`Feec.Stone.tendsto_approxU_of_tendsto` is `ContinuousLinearMap.tendsto_apply_of_tendsto`, and
`Feec.Stone.tendsto_apply_of_dense`, `Feec.Stone.cauchySeq_apply_of_dense` are the
`ContinuousLinearMap` lemmas of `Feec.ForMathlib.Analysis.StrongConvergence`; the unused
`LinearPMap.mem_partIn_domain` and `LinearPMap.IsMDissipative.hasDerivWithinAt_semigroup_Ici_zero`
are gone. `C0Semigroup.rescale`
now takes a scalar `w : 𝕜` (it was real, `ω : ℝ`, with the complex rescaling
`C0Semigroup.complexRescale` on complex spaces), and `C0Semigroup.isResolvent_resolvent`,
`C0Semigroup.norm_resolvent_pow_le` hold over `𝕜` (they were on complex spaces). Below, each is
stated verbatim and derived from the new API.

This file is part of the `FeecCheck` library, not of `Feec`.
-/

@[expose] public noncomputable section

namespace FeecCheck.Semigroups

open Set Filter Topology NormedSpace Feec

section Bounded

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The earlier `Stone.tendsto_apply_of_dense`. -/
theorem tendsto_apply_of_dense_old {T : ℕ → E →L[𝕜] E} (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖)
    {D : Set E} (hD : Dense D) (h : ∀ x ∈ D, Tendsto (fun n => T n x) atTop (𝓝 x)) (x : E) :
    Tendsto (fun n => T n x) atTop (𝓝 x) :=
  ContinuousLinearMap.tendsto_apply_of_dense hT hD h x

/-- The earlier `Stone.cauchySeq_apply_of_dense`. -/
theorem cauchySeq_apply_of_dense_old {T : ℕ → E →L[𝕜] E}
    (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖) {D : Set E} (hD : Dense D)
    (h : ∀ x ∈ D, CauchySeq fun n => T n x) (x : E) : CauchySeq fun n => T n x :=
  ContinuousLinearMap.cauchySeq_apply_of_dense hT hD h x

/-- The earlier `C0Group.commute_exp_ofReal_smul`. -/
theorem commute_exp_ofReal_smul_old (B : E →L[𝕜] E) (t : ℝ) : Commute B (exp ((t : 𝕜) • B)) :=
  B.commute_exp_ofReal_smul t

variable [CompleteSpace E]

/-- The earlier `C0Group.exp_ofReal_smul_add`. -/
theorem exp_ofReal_smul_add_old (B : E →L[𝕜] E) (s t : ℝ) :
    exp (((s + t : ℝ) : 𝕜) • B) = exp ((s : 𝕜) • B) * exp ((t : 𝕜) • B) :=
  B.exp_ofReal_smul_add s t

/-- The earlier `C0Group.continuous_exp_ofReal_smul`. -/
theorem continuous_exp_ofReal_smul_old (B : E →L[𝕜] E) :
    Continuous fun t : ℝ => exp ((t : 𝕜) • B) :=
  B.continuous_exp_ofReal_smul

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The earlier `C0Group.hasDerivAt_exp_ofReal_smul_apply`. -/
theorem hasDerivAt_exp_ofReal_smul_apply_old (B : E →L[𝕜] E) (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp ((s : 𝕜) • B) x) (B (exp ((t : 𝕜) • B) x)) t :=
  B.hasDerivAt_exp_ofReal_smul_apply x t

/-- The earlier `TimeStepping.hasDerivAt_exp_sub_smul_apply`. -/
theorem hasDerivAt_exp_sub_smul_apply_old (L : E →L[𝕜] E) (t : ℝ) {U : ℝ → E} {U' : E} {s : ℝ}
    (hU : HasDerivAt U U' s) :
    HasDerivAt (fun r => exp (((t - r : ℝ) : 𝕜) • L) (U r))
      (exp (((t - s : ℝ) : 𝕜) • L) (U' - L (U s))) s :=
  L.hasDerivAt_exp_sub_smul_apply t hU

end Bounded

section Hilbert

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E}

/-- The earlier `Stone.tendsto_approxU_of_tendsto`. -/
theorem tendsto_approxU_of_tendsto_old (hA : A.IsSkewAdjoint) (t : ℝ) {y : ℕ → E} {y₀ : E}
    (hy : Tendsto y atTop (𝓝 y₀)) :
    Tendsto (fun n => Stone.approxU A n t (y n)) atTop (𝓝 (Stone.stoneS hA t y₀)) :=
  ContinuousLinearMap.tendsto_apply_of_tendsto (Stone.norm_approxU_le hA · t)
    (Stone.tendsto_approxU hA t) hy

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- The earlier `LinearPMap.mem_partIn_domain`. -/
theorem mem_partIn_domain_old {K : Submodule 𝕜 E} {u : K} :
    u ∈ (A.partIn K).domain ↔ ∃ h : (u : E) ∈ A.domain, A ⟨u, h⟩ ∈ K := Iff.rfl

/-- The earlier `LinearPMap.IsMDissipative.hasDerivWithinAt_semigroup_Ici_zero`. -/
theorem hasDerivWithinAt_semigroup_Ici_zero_old (hA : A.IsMDissipative) (x : A.domain) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => hA.semigroup.S s x) (hA.semigroup.S t (A x)) (Ici 0) t := by
  have h := hA.semigroup.hasDerivWithinAt_apply ⟨x, hA.mem_semigroup_generator_domain x⟩ ht
  rwa [hA.semigroup_generator_apply] at h

end Hilbert

section Rescale

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] (G : C0Semigroup 𝕜 E)

/-- The earlier `C0Semigroup.rescale_S_apply`. -/
theorem rescale_S_apply_old (ω t : ℝ) (x : E) :
    (G.rescale ω).S t x = ((Real.exp (ω * t) : ℝ) : 𝕜) • G.S t x := by
  rw [C0Semigroup.rescale_S_apply, RCLike.real_smul_eq_coe_mul, ← RCLike.ofReal_mul,
    RCLike.exp_ofReal, mul_comm]

/-- The earlier `C0Semigroup.norm_rescale_S`. -/
theorem norm_rescale_S_old (ω t : ℝ) : ‖(G.rescale ω).S t‖ = Real.exp (ω * t) * ‖G.S t‖ := by
  rw [G.norm_rescale_S, RCLike.ofReal_re]

/-- The earlier `C0Semigroup.rescale_rescale_neg`. -/
theorem rescale_rescale_neg_old (ω : ℝ) : (G.rescale ω).rescale (-ω) = G := by
  simpa using G.rescale_rescale_neg (ω : 𝕜)

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The earlier `C0Semigroup.hasDerivWithinAt_rescale`. -/
theorem hasDerivWithinAt_rescale_old (ω : ℝ) (x : G.generator.domain) :
    HasDerivWithinAt (fun t => (G.rescale ω).S t x) ((ω : 𝕜) • (x : E) + G.generator x)
      (Ici 0) 0 :=
  G.hasDerivWithinAt_rescale ω x

/-- The earlier `C0Semigroup.domain_le_domain_rescale`. -/
theorem domain_le_domain_rescale_old (ω : ℝ) :
    G.generator.domain ≤ (G.rescale ω).generator.domain :=
  G.domain_le_domain_rescale ω

/-- The earlier `C0Semigroup.generator_rescale`. -/
theorem generator_rescale_old (ω : ℝ) :
    (G.rescale ω).generator = ((ω : 𝕜) • (LinearMap.id : E →ₗ[𝕜] E)) +ᵥ G.generator :=
  G.generator_rescale ω

end Rescale

section Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (H : C0Semigroup ℂ F)

/-- The earlier `C0Semigroup.complexRescale`. -/
def complexRescale_old (w : ℂ) : C0Semigroup ℂ F := H.rescale w

/-- The earlier `C0Semigroup.complexRescale_S_apply`. -/
theorem complexRescale_S_apply_old (w : ℂ) (t : ℝ) (x : F) :
    (complexRescale_old H w).S t x = Complex.exp (w * t) • H.S t x := by
  rw [complexRescale_old, C0Semigroup.rescale_S_apply, Complex.exp_eq_exp_ℂ, Complex.real_smul,
    mul_comm]

/-- The earlier `C0Semigroup.norm_complexRescale_S`. -/
theorem norm_complexRescale_S_old (w : ℂ) (t : ℝ) :
    ‖(complexRescale_old H w).S t‖ = Real.exp (w.re * t) * ‖H.S t‖ :=
  H.norm_rescale_S w t

/-- The earlier `C0Semigroup.complexRescale_complexRescale_neg`. -/
theorem complexRescale_complexRescale_neg_old (w : ℂ) :
    complexRescale_old (complexRescale_old H w) (-w) = H :=
  H.rescale_rescale_neg w

/-- The earlier `C0Semigroup.hasDerivWithinAt_complexRescale`. -/
theorem hasDerivWithinAt_complexRescale_old (w : ℂ) (x : H.generator.domain) :
    HasDerivWithinAt (fun t => (complexRescale_old H w).S t x) (w • (x : F) + H.generator x)
      (Ici 0) 0 :=
  H.hasDerivWithinAt_rescale w x

/-- The earlier `C0Semigroup.domain_le_domain_complexRescale`. -/
theorem domain_le_domain_complexRescale_old (w : ℂ) :
    H.generator.domain ≤ (complexRescale_old H w).generator.domain :=
  H.domain_le_domain_rescale w

/-- The earlier `C0Semigroup.generator_complexRescale`. -/
theorem generator_complexRescale_old (w : ℂ) :
    (complexRescale_old H w).generator = (w • (LinearMap.id : F →ₗ[ℂ] F)) +ᵥ H.generator :=
  H.generator_rescale w

variable [CompleteSpace F]

/-- The earlier `C0Semigroup.isResolvent_resolvent` (complex spaces). -/
theorem isResolvent_resolvent_old {M ω : ℝ} (hS : ∀ t, 0 ≤ t → ‖H.S t‖ ≤ M * Real.exp (ω * t))
    {z : ℂ} (hz : ω < z.re) :
    Operator.IsResolvent H.generator z (Operator.resolvent H.generator z) :=
  H.isResolvent_resolvent hS hz

/-- The earlier `C0Semigroup.norm_resolvent_pow_le` (complex spaces). -/
theorem norm_resolvent_pow_le_old {M ω : ℝ} (hS : ∀ t, 0 ≤ t → ‖H.S t‖ ≤ M * Real.exp (ω * t))
    {z : ℂ} (hz : ω < z.re) (m : ℕ) :
    ‖Operator.resolvent H.generator z ^ m‖ ≤ M / (z.re - ω) ^ m :=
  H.norm_resolvent_pow_le hS hz m

end Complex

end FeecCheck.Semigroups
