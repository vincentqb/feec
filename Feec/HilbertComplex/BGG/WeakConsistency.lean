module

public import Feec.HilbertComplex.BGG.Discrete

/-!
# The a priori error estimate under weak consistency

The a priori error estimate of [QuennevilleBelair2015], Thm 5.5 for the discrete BGG system (5.6),
and its form with the consistency of `S₁,ₕ` required only against the exact solution, which
follows from regular potentials of `dṼₕ¹` and `S₁u ∈ D(d¹*)`.

## Main results

* `Feec.BGG.Discrete.error_estimate`: the a priori estimate.
* `Feec.BGG.Discrete.error_estimate_of_weakConsistency`: the estimate under weak consistency.
* `Feec.BGG.Discrete.error_estimate_of_regularPotential`: the estimate from regular potentials.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 5.5, Prop 5.9

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace Feec.BGG.Discrete

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} {Q : Discrete D}

/-! ## The error estimate with weak consistency -/

/-- The a priori estimate of (5.6) under weak consistency of `S₁,ₕ` on `Ṽₕ¹`,
`|⟪S₁u, (S₁ − S₁,ₕ)v⟫| ≤ C_app h K ‖v‖_V`. [QuennevilleBelair2015], Thm 5.5 (adapted) -/
theorem error_estimate_of_weakConsistency {Cp CR CS CP : ℝ} (H : Stability D Cp CR CS)
    (B : Q.Bounded CP) (h54 : Q.Compatible) [FiniteDimensional ℝ Q.Vt1h]
    {h Capp : ℝ} (hh : 0 ≤ h) (hCapp : 0 ≤ Capp)
    (happ0 : ∀ ψ ∈ Q.Vt0h, ‖D.S0 ψ - Q.S0h ψ‖ ^ 2 ≤ (Capp * h) ^ 2 * graphSq D.dt0 ψ)
    {σ : V0} {φ : Vt0} {u : Vt1} {K : ℝ}
    (hwc : ∀ v ∈ Q.Vt1h, |⟪D.S1 u, (D.S1 - Q.S1h) v⟫| ≤ Capp * h * K * √(graphSq D.dt1 v))
    (ℓ : V1 →ₗ[ℝ] ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hℓ : ∀ μ, |ℓ μ| ≤ Λ * ‖μ‖) (F : Vt1 →ₗ[ℝ] ℝ)
    (c1 : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, ⟪σ, τ⟫ - ⟪u, D.dt0 ψ⟫ - ℓ (D.d0 τ - D.S0 ψ) = 0)
    (c2 : ∀ v ∈ Q.Vt1h, ⟪D.dt0 φ, v⟫ + ⟪D.S1 u, D.S1 v⟫ + ⟪D.dt1 u, D.dt1 v⟫ = F v)
    (c3 : D.d0 σ = D.S0 φ)
    {σh : V0} {φh : Vt0} {uh : Vt1} {lh : V1}
    (hσh : σh ∈ Q.V0h) (hφh : φh ∈ Q.Vt0h) (huh : uh ∈ Q.Vt1h)
    (h1 : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, ⟪σh, τ⟫ - ⟪uh, D.dt0 ψ⟫ - ⟪lh, D.d0 τ - Q.S0h ψ⟫ = 0)
    (h2 : ∀ v ∈ Q.Vt1h, ⟪D.dt0 φh, v⟫ + ⟪Q.S1h uh, Q.S1h v⟫ + ⟪D.dt1 uh, D.dt1 v⟫ = F v)
    (h3 : ∀ μ ∈ Q.V1h, ⟪D.d0 σh - Q.S0h φh, μ⟫ = 0) :
    graphSq D.d0 (σ - σh) + graphSq D.dt0 (φ - φh) + Q.gnSq (u - uh) ≤
      errorConst Cp CR CS CP Capp * (graphSq D.d0 (Q.P0 σ - σ) + graphSq D.dt0 (Q.Pt0 φ - φ)
        + Q.gnSq (Q.Pt1 u - u) + h ^ 2 * Λ ^ 2 + h ^ 2 * K ^ 2
        + ‖D.S1 u - Q.S1h u‖ ^ 2) := by
  -- constants
  have hp := H.Cp_nonneg; have hR := H.CR_nonneg; have hS := H.CS_nonneg
  have hP := B.CP_nonneg
  set A := Ca1 Cp CS CP with hA_def
  have hCa0 : 0 ≤ Ca Cp CS CP := by unfold Ca; positivity
  have hA1 : 1 ≤ A := by rw [hA_def, Ca1]; linarith
  have h53a : ∀ {σ' : V0} {φ' : Vt0}, D.d0 σ' = Q.S0h φ' →
      graphSq D.d0 σ' ≤ A ^ 2 * ‖D.dt0 φ'‖ ^ 2 := fun hσφ => by
    refine (poincare_Γh H B hσφ).trans ?_
    gcongr; rw [hA_def, Ca1]; linarith
  set Cb' := Cb Cp CR CS CP with hCb_def
  have hCb0 : 0 ≤ Cb' := by rw [hCb_def, Cb]; positivity
  -- step 0: the discrete constraint and `(e_σ, e_φ) ∈ Γ_h`
  have hcons : D.d0 σh = Q.S0h φh := constraint_of_inner hσh h3
  obtain ⟨eσ, heσ⟩ : ∃ e, e = Q.P0 σ - σh := ⟨_, rfl⟩
  obtain ⟨eφ, heφ⟩ : ∃ e, e = Q.Pt0 φ - φh := ⟨_, rfl⟩
  have heσm : eσ ∈ Q.V0h := heσ ▸ Submodule.sub_mem _ (Q.P0_mem σ) hσh
  have heφm : eφ ∈ Q.Vt0h := heφ ▸ Submodule.sub_mem _ (Q.Pt0_mem φ) hφh
  have heum : Q.Pt1 u - uh ∈ Q.Vt1h := Submodule.sub_mem _ (Q.Pt1_mem u) huh
  have hΓe : D.d0 eσ = Q.S0h eφ := by
    rw [heσ, heφ, map_sub, map_sub, Q.comm0, c3, hcons, S0h_apply, S0h_apply, h54]
  -- step 1: the discrete decomposition `Π̃u - u_h = dχ + ω`
  have : FiniteDimensional ℝ Q.Zh := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨z, hz_def⟩ : ∃ z, z = Q.Zh.starProjection (Q.Pt1 u - uh) := ⟨_, rfl⟩
  have hz : z ∈ Q.Zh := hz_def ▸ Q.Zh.starProjection_apply_mem _
  obtain ⟨ω, hω_def⟩ : ∃ ω, ω = Q.Pt1 u - uh - z := ⟨_, rfl⟩
  have hω : ω ∈ Q.Zhᗮ := hω_def ▸ hz_def ▸ Q.Zh.sub_starProjection_mem_orthogonal _
  obtain ⟨ρ, hρ, χ, hχ, hρχ, hχz⟩ := exact_mid_h H hz
  have hωm : ω ∈ Q.Vt1h := hω_def ▸ Submodule.sub_mem _ heum hz.1
  have heu : Q.Pt1 u - uh = D.dt0 χ + ω := by rw [hχz, hω_def]; abel
  have hSdχ : Q.S1h (D.dt0 χ) = 0 := by rw [hχz]; exact hz.2.1
  have hSdeφ : Q.S1h (D.dt0 eφ) = 0 := by
    have := Q.anticomm_h eφ
    rw [← hΓe, D.d1_d0] at this
    exact neg_eq_zero.1 this.symm
  have hωχ : ⟪ω, D.dt0 χ⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (hχz ▸ hz) hω
  -- step 2: test functions
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℝ, ε = 1 / A ^ 2 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε_def]; positivity
  have hτm : eσ - ε • ρ ∈ Q.V0h := Submodule.sub_mem _ heσm (Submodule.smul_mem _ _ hρ)
  have hψm : eφ - ε • χ ∈ Q.Vt0h := Submodule.sub_mem _ heφm (Submodule.smul_mem _ _ hχ)
  have hvm : D.dt0 eφ + D.dt0 χ + ω ∈ Q.Vt1h :=
    Submodule.add_mem _ (Submodule.add_mem _ (Q.dt0_mem _ heφm) (Q.dt0_mem _ hχ)) hωm
  have hτψ : D.d0 (eσ - ε • ρ) - Q.S0h (eφ - ε • χ) = 0 := by
    rw [map_sub, map_sub, map_smul, map_smul, hΓe, hρχ, sub_self]
  -- step 3: error equation and coercivity identity
  have E := mixed_error_eq D.d0 D.dt0 D.dt1 D.S0 Q.S0h D.S1 Q.S1h ℓ F σ (Q.P0 σ) σh (eσ - ε • ρ)
    φ (Q.Pt0 φ) φh (eφ - ε • χ) u (Q.Pt1 u) uh (D.dt0 eφ + D.dt0 χ + ω) lh
    (c1 _ hτm _ hψm) (c2 _ hvm) (h1 _ hτm _ hψm) (h2 _ hvm)
  rw [hτψ, map_zero, inner_zero_right, sub_self, sub_zero, heu, ← heσ, ← heφ] at E
  have I := mixed_coercivity_eq D.d0 D.dt0 D.dt1 Q.S0h Q.S1h D.dt1_dt0 eσ ρ eφ χ ω 0 ε
    hΓe hρχ hSdχ hSdeφ hωχ
  rw [inner_zero_left, sub_zero] at I
  have key := I.symm.trans E
  have hSv : Q.S1h (D.dt0 eφ + D.dt0 χ + ω) = Q.S1h ω := by
    rw [map_add, map_add, hSdeφ, hSdχ, zero_add, zero_add]
  have hdv : D.dt1 (D.dt0 eφ + D.dt0 χ + ω) = D.dt1 ω := by
    rw [map_add, map_add, D.dt1_dt0, D.dt1_dt0, zero_add, zero_add]
  rw [hSv, hdv] at key
  -- step 4: scalar facts (Prop 5.3 and norms of the test functions)
  have hρn : ‖ρ‖ ^ 2 ≤ A ^ 2 * ‖D.dt0 χ‖ ^ 2 :=
    le_trans (le_add_of_nonneg_right (sq_nonneg _)) (h53a hρχ)
  have heσg : graphSq D.d0 eσ ≤ A ^ 2 * ‖D.dt0 eφ‖ ^ 2 := h53a hΓe
  have heφn : ‖eφ‖ ^ 2 ≤ Cp ^ 2 * ‖D.dt0 eφ‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) (H.poinct0 eφ) 2; rwa [mul_pow] at this
  have hχn : ‖χ‖ ^ 2 ≤ Cp ^ 2 * ‖D.dt0 χ‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) (H.poinct0 χ) 2; rwa [mul_pow] at this
  have hωn2 : ‖ω‖ ^ 2 ≤ 2 * Cb' ^ 2 * (‖Q.S1h ω‖ ^ 2 + ‖D.dt1 ω‖ ^ 2) := by
    have := pow_le_pow_left₀ (norm_nonneg _) (poincare_Zh H B h54 hωm hω) 2
    rw [← hCb_def] at this
    nlinarith only [this, mul_nonneg (sq_nonneg Cb') (sq_nonneg (‖Q.S1h ω‖ - ‖D.dt1 ω‖))]
  have hτ : ‖eσ - ε • ρ‖ ^ 2 ≤ 2 * ‖eσ‖ ^ 2 + 2 * (ε ^ 2 * ‖ρ‖ ^ 2) := by
    have h1 := norm_sub_sq_le_two_mul eσ (ε • ρ)
    rwa [norm_smul, Real.norm_of_nonneg hε0.le, mul_pow] at h1
  have hdψ : ‖D.dt0 (eφ - ε • χ)‖ ^ 2 ≤ 2 * ‖D.dt0 eφ‖ ^ 2 + 2 * (ε ^ 2 * ‖D.dt0 χ‖ ^ 2) := by
    have h1 := norm_sub_sq_le_two_mul (D.dt0 eφ) (ε • D.dt0 χ)
    rw [norm_smul, Real.norm_of_nonneg hε0.le, mul_pow] at h1
    rwa [map_sub, map_smul]
  have hgψ : graphSq D.dt0 (eφ - ε • χ) ≤
      2 * ‖eφ‖ ^ 2 + 2 * (ε ^ 2 * ‖χ‖ ^ 2) + ‖D.dt0 (eφ - ε • χ)‖ ^ 2 := by
    have h1 := norm_sub_sq_le_two_mul eφ (ε • χ)
    rw [norm_smul, Real.norm_of_nonneg hε0.le, mul_pow] at h1
    unfold graphSq; linarith only [h1]
  have hv := norm_add₃_sq_le_three_mul (D.dt0 eφ) (D.dt0 χ) ω
  have hgv : graphSq D.dt1 (D.dt0 eφ + D.dt0 χ + ω) =
      ‖D.dt0 eφ + D.dt0 χ + ω‖ ^ 2 + ‖D.dt1 ω‖ ^ 2 := by
    unfold graphSq; rw [hdv]
  -- step 5: term-by-term bounds of the right-hand side of the error equation
  have hz1 : ‖(D.S0 - Q.S0h) (eφ - ε • χ)‖ ≤ Capp * h * √(graphSq D.dt0 (eφ - ε • χ)) := by
    rw [LinearMap.sub_apply]
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, Real.sq_sqrt (graphSq_nonneg _ _)]; exact happ0 _ hψm
  have b1 := real_inner_le_norm (Q.P0 σ - σ) (eσ - ε • ρ)
  have b2 : -⟪Q.Pt1 u - u, D.dt0 (eφ - ε • χ)⟫ ≤ ‖Q.Pt1 u - u‖ * ‖D.dt0 (eφ - ε • χ)‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have b3 : -ℓ ((D.S0 - Q.S0h) (eφ - ε • χ)) ≤
      (Capp * h * Λ) * √(graphSq D.dt0 (eφ - ε • χ)) := by
    refine ((neg_le_abs _).trans (hℓ _)).trans ?_
    calc Λ * ‖(D.S0 - Q.S0h) (eφ - ε • χ)‖ ≤ Λ * (Capp * h * √(graphSq D.dt0 (eφ - ε • χ))) :=
          mul_le_mul_of_nonneg_left hz1 hΛ
      _ = _ := by ring
  have b4 := real_inner_le_norm (D.dt0 (Q.Pt0 φ - φ)) (D.dt0 eφ + D.dt0 χ + ω)
  -- the only use of the consistency of `S₁,ₕ`: weak consistency against `S₁u`
  have b5 : -⟪D.S1 u, (D.S1 - Q.S1h) (D.dt0 eφ + D.dt0 χ + ω)⟫ ≤
      (Capp * h * K) * √(graphSq D.dt1 (D.dt0 eφ + D.dt0 χ + ω)) :=
    (neg_le_abs _).trans (hwc _ hvm)
  have b6 : -⟪(D.S1 - Q.S1h) u, Q.S1h ω⟫ ≤ ‖D.S1 u - Q.S1h u‖ * ‖Q.S1h ω‖ := by
    rw [LinearMap.sub_apply]; exact (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have b7 := real_inner_le_norm (Q.S1h (Q.Pt1 u - u)) (Q.S1h ω)
  have b8 := real_inner_le_norm (D.dt1 (Q.Pt1 u - u)) (D.dt1 ω)
  have hmain : ‖eσ‖ ^ 2 - ε * ⟪eσ, ρ⟫ + ε * ‖D.dt0 χ‖ ^ 2 + ‖D.dt0 eφ‖ ^ 2 + ‖Q.S1h ω‖ ^ 2
      + ‖D.dt1 ω‖ ^ 2 ≤ ‖Q.P0 σ - σ‖ * ‖eσ - ε • ρ‖ + ‖Q.Pt1 u - u‖ * ‖D.dt0 (eφ - ε • χ)‖
      + (Capp * h * Λ) * √(graphSq D.dt0 (eφ - ε • χ))
      + ‖D.dt0 (Q.Pt0 φ - φ)‖ * ‖D.dt0 eφ + D.dt0 χ + ω‖
      + (Capp * h * K) * √(graphSq D.dt1 (D.dt0 eφ + D.dt0 χ + ω))
      + ‖D.S1 u - Q.S1h u‖ * ‖Q.S1h ω‖ + ‖Q.S1h (Q.Pt1 u - u)‖ * ‖Q.S1h ω‖
      + ‖D.dt1 (Q.Pt1 u - u)‖ * ‖D.dt1 ω‖ := by
    rw [key]; linarith only [b1, b2, b3, b4, b5, b6, b7, b8]
  -- step 6: absorption (pure real arithmetic)
  have hN := errorEstimate_absorb hA1 hε_def (KL_ge Cp CR CS CP) (KL_ge' Cp CR CS CP)
    (graphSq_nonneg _ _) (by rw [hgv]; positivity)
    (real_inner_le_norm eσ ρ) hρn heφn hχn hωn2 hτ hdψ hgψ hv hgv hmain
  -- step 7: back to the errors
  have hE1 : graphSq D.d0 (σ - σh) ≤ 2 * graphSq D.d0 eσ + 2 * graphSq D.d0 (Q.P0 σ - σ) := by
    have : σ - σh = eσ - (Q.P0 σ - σ) := by rw [heσ]; abel
    rw [this]; exact graphSq_sub_le _ _ _
  have hE2 : graphSq D.dt0 (φ - φh) ≤
      2 * graphSq D.dt0 eφ + 2 * graphSq D.dt0 (Q.Pt0 φ - φ) := by
    have : φ - φh = eφ - (Q.Pt0 φ - φ) := by rw [heφ]; abel
    rw [this]; exact graphSq_sub_le _ _ _
  have hE3 : Q.gnSq (u - uh) ≤ 2 * Q.gnSq (D.dt0 χ + ω) + 2 * Q.gnSq (Q.Pt1 u - u) := by
    have : u - uh = (D.dt0 χ + ω) - (Q.Pt1 u - u) := by rw [← heu]; abel
    rw [this]; exact Q.gnSq_sub_le _ _
  have hgn : Q.gnSq (D.dt0 χ + ω) = ‖D.dt0 χ + ω‖ ^ 2 + ‖Q.S1h ω‖ ^ 2 + ‖D.dt1 ω‖ ^ 2 := by
    unfold gnSq; rw [map_add, hSdχ, zero_add, map_add, D.dt1_dt0, zero_add]
  have hgφ : graphSq D.dt0 eφ = ‖eφ‖ ^ 2 + ‖D.dt0 eφ‖ ^ 2 := rfl
  have hg3 : Q.gnSq (Q.Pt1 u - u) = ‖Q.Pt1 u - u‖ ^ 2 + ‖Q.S1h (Q.Pt1 u - u)‖ ^ 2
      + ‖D.dt1 (Q.Pt1 u - u)‖ ^ 2 := rfl
  rw [errorConst, ← hA_def, ← hCb_def]
  exact errorEstimate_final (KL_pos Cp CR CS CP) hA1 hN hE1 hE2 hE3 heσg hgφ heφn hgn
    (norm_add_sq_le_two_mul _ _) hωn2
    (le_add_of_nonneg_right (sq_nonneg _)) (le_add_of_nonneg_left (sq_nonneg _)) hg3
    (graphSq_nonneg _ _) (graphSq_nonneg _ _)

/-- The a priori estimate of (5.6) against (5.3) with `|ℓ| ≤ Λ‖·‖`, under `Stability`, `Bounded`,
(5.4) and `O(h)` consistency of `S₀,ₕ`, `S₁,ₕ`. [QuennevilleBelair2015], Thm 5.5 (adapted) -/
theorem error_estimate {Cp CR CS CP : ℝ} (H : Stability D Cp CR CS) (B : Q.Bounded CP)
    (h54 : Q.Compatible)
    [FiniteDimensional ℝ Q.Vt1h]
    {h Capp : ℝ} (hh : 0 ≤ h) (hCapp : 0 ≤ Capp)
    (happ0 : ∀ ψ ∈ Q.Vt0h, ‖D.S0 ψ - Q.S0h ψ‖ ^ 2 ≤ (Capp * h) ^ 2 * graphSq D.dt0 ψ)
    (happ1 : ∀ v ∈ Q.Vt1h, ‖D.S1 v - Q.S1h v‖ ^ 2 ≤ (Capp * h) ^ 2 * graphSq D.dt1 v)
    {σ : V0} {φ : Vt0} {u : Vt1} (ℓ : V1 →ₗ[ℝ] ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hℓ : ∀ μ, |ℓ μ| ≤ Λ * ‖μ‖) (F : Vt1 →ₗ[ℝ] ℝ)
    (c1 : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, ⟪σ, τ⟫ - ⟪u, D.dt0 ψ⟫ - ℓ (D.d0 τ - D.S0 ψ) = 0)
    (c2 : ∀ v ∈ Q.Vt1h, ⟪D.dt0 φ, v⟫ + ⟪D.S1 u, D.S1 v⟫ + ⟪D.dt1 u, D.dt1 v⟫ = F v)
    (c3 : D.d0 σ = D.S0 φ)
    {σh : V0} {φh : Vt0} {uh : Vt1} {lh : V1}
    (hσh : σh ∈ Q.V0h) (hφh : φh ∈ Q.Vt0h) (huh : uh ∈ Q.Vt1h)
    (h1 : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, ⟪σh, τ⟫ - ⟪uh, D.dt0 ψ⟫ - ⟪lh, D.d0 τ - Q.S0h ψ⟫ = 0)
    (h2 : ∀ v ∈ Q.Vt1h, ⟪D.dt0 φh, v⟫ + ⟪Q.S1h uh, Q.S1h v⟫ + ⟪D.dt1 uh, D.dt1 v⟫ = F v)
    (h3 : ∀ μ ∈ Q.V1h, ⟪D.d0 σh - Q.S0h φh, μ⟫ = 0) :
    graphSq D.d0 (σ - σh) + graphSq D.dt0 (φ - φh) + Q.gnSq (u - uh) ≤
      errorConst Cp CR CS CP Capp * (graphSq D.d0 (Q.P0 σ - σ) + graphSq D.dt0 (Q.Pt0 φ - φ)
        + Q.gnSq (Q.Pt1 u - u) + h ^ 2 * Λ ^ 2 + h ^ 2 * ‖D.S1 u‖ ^ 2
        + ‖D.S1 u - Q.S1h u‖ ^ 2) :=
  error_estimate_of_weakConsistency H B h54 hh hCapp happ0 (fun v hv => by
    have hz : ‖(D.S1 - Q.S1h) v‖ ≤ Capp * h * √(graphSq D.dt1 v) := by
      rw [LinearMap.sub_apply]
      refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
      rw [mul_pow, Real.sq_sqrt (graphSq_nonneg _ _)]; exact happ1 _ hv
    refine (abs_real_inner_le_norm _ _).trans ?_
    nlinarith [norm_nonneg (D.S1 u)])
    ℓ hΛ hℓ F c1 c2 c3 hσh hφh huh h1 h2 h3

/-! ## Weak consistency from a discrete Hodge decomposition -/

/-- Regular potentials of `dṼₕ¹` in a normed space, approximated at rate `h` by `Π̃¹` and `S₁,ₕ`. -/
structure RegularPotential (Q : Discrete D) (Xr : Type*) [NormedAddCommGroup Xr]
    [NormedSpace ℝ Xr] (Cinc Creg Capp h : ℝ) where
  /-- The bounded map `X_reg → Ṽ¹`. -/
  R : Xr →ₗ[ℝ] Vt1
  Cinc_nonneg : 0 ≤ Cinc
  Creg_nonneg : 0 ≤ Creg
  norm_R_le : ∀ y, ‖R y‖ ≤ Cinc * ‖y‖
  exists_potential : ∀ v ∈ Q.Vt1h, ∃ y, D.dt1 (R y) = D.dt1 v ∧ ‖y‖ ≤ Creg * ‖D.dt1 v‖
  approx_Pt1 : ∀ y, ‖R y - Q.Pt1 (R y)‖ ≤ Capp * h * ‖y‖
  approx_S1 : ∀ y, ‖(D.S1 - Q.S1h) (R y)‖ ≤ Capp * h * ‖y‖

theorem S1_sub_S1h_dt0 (ψ : Vt0) : (D.S1 - Q.S1h) (D.dt0 ψ) = D.d1 (Q.S0h ψ - D.S0 ψ) := by
  have h1 := D.anticomm ψ
  have h2 := Q.anticomm_h ψ
  rw [LinearMap.sub_apply, map_sub, h1, h2]; abel

/-- The constant of `weakConsistency_of_regularPotential`. -/
def weakConsistencyConst (Cp CS CP Cinc Creg nz nz' : ℝ) : ℝ :=
  nz' * √(1 + Cp ^ 2) * (1 + CP * (1 + Cinc * Creg)) + nz * (1 + (1 + CP) * CS) * Creg

end Feec.BGG.Discrete

namespace Feec.BGG

namespace HarmonicStability

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]

variable {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} {Hh : Submodule ℝ Vt1} {Cp CS : ℝ}
  (HS : HarmonicStability D Hh Cp CS)
include HS

theorem norm_dt0_le_norm_add (ψ : Vt0) {k : Vt1} (hk : k ∈ Hh) :
    ‖D.dt0 ψ‖ ≤ ‖D.dt0 ψ + k‖ := by
  have h0 : ⟪D.dt0 ψ, k⟫ = 0 := by rw [real_inner_comm]; exact HS.harmonic_orth k hk ψ
  have e := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (D.dt0 ψ) k h0
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  nlinarith [sq_nonneg ‖k‖]

variable {Q : Discrete D}

theorem exact_bot_h (hH : Hh ≤ Q.Vt1h) {u : Vt1} (hu : u ∈ Q.Vt1h) (hd : D.dt1 u = 0) :
    ∃ χ ∈ Q.Vt0h, ∃ k ∈ Hh, D.dt0 χ + k = u := by
  obtain ⟨ψ, w, k, hk, rfl, hw⟩ := HS.hodget1 u
  rw [hd, norm_zero, mul_zero] at hw
  have hw0 : w = 0 := norm_le_zero_iff.1 hw
  subst hw0
  refine ⟨Q.Pt0 ψ, Q.Pt0_mem ψ, k, hk, ?_⟩
  rw [add_zero] at hu ⊢
  have e := Q.Pt1_id _ hu
  rw [map_add, ← Q.commt0, Q.Pt1_id _ (hH hk)] at e
  exact e

theorem S1_sub_S1h_harmonic {k : Vt1} (hk : k ∈ Hh) : (D.S1 - Q.S1h) k = 0 := by
  rw [LinearMap.sub_apply, Discrete.S1h_apply, HS.S1_harmonic k hk, map_zero, sub_zero]

open Discrete

theorem weakConsistency_of_potential_of_bound {CP : ℝ}
    (hH : Hh ≤ Q.Vt1h) (B : Q.Bounded CP) {Cinc Creg h Capp : ℝ} (hι : 0 ≤ Cinc) (hr : 0 ≤ Creg)
    (hh : 0 ≤ h) (hCapp : 0 ≤ Capp)
    (hpot : ∀ v ∈ Q.Vt1h, ∃ w, D.dt1 w = D.dt1 v ∧ ‖w‖ ≤ Cinc * Creg * ‖D.dt1 v‖ ∧
      ‖w - Q.Pt1 w‖ ≤ Capp * h * (Creg * ‖D.dt1 v‖) ∧
      ‖(D.S1 - Q.S1h) w‖ ≤ Capp * h * (Creg * ‖D.dt1 v‖))
    (happ0 : ∀ ψ ∈ Q.Vt0h, ‖D.S0 ψ - Q.S0h ψ‖ ^ 2 ≤ (Capp * h) ^ 2 * graphSq D.dt0 ψ)
    {z : W2} {M : ℝ} (hM : 0 ≤ M) (hz : ∀ w, |⟪z, D.d1 w⟫| ≤ M * ‖w‖) :
    ∀ v ∈ Q.Vt1h, |⟪z, (D.S1 - Q.S1h) v⟫| ≤
      Capp * h * weakConsistencyConst Cp CS CP Cinc Creg ‖z‖ M *
        √(graphSq D.dt1 v) := by
  intro v hv
  have hp := HS.Cp_nonneg; have hS := HS.CS_nonneg; have hP := B.CP_nonneg
  obtain ⟨w, hy1, hwn, hPt, hSw⟩ := hpot v hv
  set G := √(graphSq D.dt1 v) with hG
  have hvG : ‖v‖ ≤ G := (Real.le_sqrt (norm_nonneg _) (graphSq_nonneg _ _)).2 (by
    unfold graphSq; nlinarith [sq_nonneg ‖D.dt1 v‖])
  have hdG : ‖D.dt1 v‖ ≤ G := (Real.le_sqrt (norm_nonneg _) (graphSq_nonneg _ _)).2 (by
    unfold graphSq; nlinarith [sq_nonneg ‖v‖])
  have hdv : D.dt1 v ∈ Q.Wt2h := Q.dt1_mem v hv
  have hdPw : D.dt1 (Q.Pt1 w) = D.dt1 v := by rw [Q.commt1, hy1, Q.Pt2_id _ hdv]
  have hker : D.dt1 (v - Q.Pt1 w) = 0 := by rw [map_sub, hdPw, sub_self]
  obtain ⟨ψ, hψ, k, hk, hψeq⟩ := HS.exact_bot_h hH (Submodule.sub_mem _ hv (Q.Pt1_mem w)) hker
  have hsplit : (D.S1 - Q.S1h) v = D.d1 (Q.S0h ψ - D.S0 ψ) +
      ((D.S1 - Q.S1h) w - (D.S1 - Q.S1h) (w - Q.Pt1 w)) := by
    calc (D.S1 - Q.S1h) v = (D.S1 - Q.S1h) (D.dt0 ψ + k + w - (w - Q.Pt1 w)) := by
          congr 1; rw [hψeq]; abel
      _ = _ := by
          rw [map_sub, map_add, map_add, S1_sub_S1h_dt0, HS.S1_sub_S1h_harmonic hk]; abel
  have hgrad : |⟪z, D.d1 (Q.S0h ψ - D.S0 ψ)⟫| ≤
      M * (Capp * h * √(graphSq D.dt0 ψ)) := by
    refine (hz _).trans (mul_le_mul_of_nonneg_left ?_ hM)
    rw [norm_sub_rev]
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, Real.sq_sqrt (graphSq_nonneg _ _)]; exact happ0 ψ hψ
  have hψg : √(graphSq D.dt0 ψ) ≤ √(1 + Cp ^ 2) * ‖D.dt0 ψ‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (D.dt0 ψ)), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := pow_le_pow_left₀ (norm_nonneg _) (HS.poinct0 ψ) 2
    unfold graphSq; nlinarith
  have hPw : ‖Q.Pt1 w‖ ≤ CP * (1 + Cinc * Creg) * ‖D.dt1 v‖ := by
    have hg := B.Pt1 w
    have hgw : graphSq D.dt1 w ≤ ((1 + Cinc * Creg) * ‖D.dt1 v‖) ^ 2 := by
      unfold graphSq; rw [hy1]
      have := pow_le_pow_left₀ (norm_nonneg _) hwn 2
      nlinarith [norm_nonneg (D.dt1 v), mul_nonneg (mul_nonneg hι hr) (norm_nonneg (D.dt1 v))]
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    calc ‖Q.Pt1 w‖ ^ 2 ≤ graphSq D.dt1 (Q.Pt1 w) := by
          unfold graphSq; nlinarith [sq_nonneg ‖D.dt1 (Q.Pt1 w)‖]
      _ ≤ CP ^ 2 * graphSq D.dt1 w := hg
      _ ≤ CP ^ 2 * ((1 + Cinc * Creg) * ‖D.dt1 v‖) ^ 2 := by gcongr
      _ = _ := by ring
  have hdψ : ‖D.dt0 ψ‖ ≤ (1 + CP * (1 + Cinc * Creg)) * G := by
    refine (HS.norm_dt0_le_norm_add ψ hk).trans ?_
    rw [hψeq]
    calc ‖v - Q.Pt1 w‖ ≤ ‖v‖ + ‖Q.Pt1 w‖ := norm_sub_le _ _
      _ ≤ G + CP * (1 + Cinc * Creg) * G :=
          add_le_add hvG (hPw.trans (mul_le_mul_of_nonneg_left hdG (by positivity)))
      _ = _ := by ring
  have hx : D.dt1 (w - Q.Pt1 w) = 0 := by rw [map_sub, hdPw, hy1, sub_self]
  have hSx : ‖(D.S1 - Q.S1h) (w - Q.Pt1 w)‖ ≤ (1 + CP) * CS * (Capp * h * (Creg * ‖D.dt1 v‖)) := by
    have hS1x : ‖D.S1 (w - Q.Pt1 w)‖ ≤ CS * ‖w - Q.Pt1 w‖ := by
      have := HS.boundS1 (w - Q.Pt1 w)
      unfold graphSq at this; rw [hx, norm_zero] at this
      refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
      rw [mul_pow]; simpa using this
    rw [LinearMap.sub_apply, S1h_apply]
    calc ‖D.S1 (w - Q.Pt1 w) - Q.P2 (D.S1 (w - Q.Pt1 w))‖
        ≤ ‖D.S1 (w - Q.Pt1 w)‖ + ‖Q.P2 (D.S1 (w - Q.Pt1 w))‖ := norm_sub_le _ _
      _ ≤ ‖D.S1 (w - Q.Pt1 w)‖ + CP * ‖D.S1 (w - Q.Pt1 w)‖ := add_le_add le_rfl (B.P2 _)
      _ = (1 + CP) * ‖D.S1 (w - Q.Pt1 w)‖ := by ring
      _ ≤ (1 + CP) * (CS * ‖w - Q.Pt1 w‖) :=
          mul_le_mul_of_nonneg_left hS1x (by linarith)
      _ ≤ (1 + CP) * (CS * (Capp * h * (Creg * ‖D.dt1 v‖))) := by
          gcongr
      _ = _ := by ring
  have hco : ‖(D.S1 - Q.S1h) w - (D.S1 - Q.S1h) (w - Q.Pt1 w)‖ ≤
      (1 + (1 + CP) * CS) * (Capp * h) * (Creg * G) := by
    have hyG : Creg * ‖D.dt1 v‖ ≤ Creg * G := mul_le_mul_of_nonneg_left hdG hr
    calc _ ≤ ‖(D.S1 - Q.S1h) w‖ + ‖(D.S1 - Q.S1h) (w - Q.Pt1 w)‖ := norm_sub_le _ _
      _ ≤ Capp * h * (Creg * ‖D.dt1 v‖) + (1 + CP) * CS * (Capp * h * (Creg * ‖D.dt1 v‖)) :=
          add_le_add hSw hSx
      _ = (1 + (1 + CP) * CS) * (Capp * h) * (Creg * ‖D.dt1 v‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hyG (by positivity)
  rw [hsplit, inner_add_right]
  calc |⟪z, D.d1 (Q.S0h ψ - D.S0 ψ)⟫ + ⟪z, (D.S1 - Q.S1h) w - (D.S1 - Q.S1h) (w - Q.Pt1 w)⟫|
      ≤ |⟪z, D.d1 (Q.S0h ψ - D.S0 ψ)⟫|
        + |⟪z, (D.S1 - Q.S1h) w - (D.S1 - Q.S1h) (w - Q.Pt1 w)⟫| := abs_add_le _ _
    _ ≤ M * (Capp * h * √(graphSq D.dt0 ψ))
        + ‖z‖ * ((1 + (1 + CP) * CS) * (Capp * h) * (Creg * G)) :=
        add_le_add hgrad ((abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left hco (norm_nonneg _)))
    _ ≤ M * (Capp * h * (√(1 + Cp ^ 2) * ((1 + CP * (1 + Cinc * Creg)) * G)))
        + ‖z‖ * ((1 + (1 + CP) * CS) * (Capp * h) * (Creg * G)) := by
        gcongr
        exact hψg.trans (mul_le_mul_of_nonneg_left hdψ (Real.sqrt_nonneg _))
    _ = _ := by unfold weakConsistencyConst; ring

theorem weakConsistency_of_regularPotential_of_bound {CP : ℝ}
    (hH : Hh ≤ Q.Vt1h) (B : Q.Bounded CP) {Xr : Type*} [NormedAddCommGroup Xr]
    [NormedSpace ℝ Xr] {Cinc Creg h Capp : ℝ} (hh : 0 ≤ h) (hCapp : 0 ≤ Capp)
    (Rg : Q.RegularPotential Xr Cinc Creg Capp h)
    (happ0 : ∀ ψ ∈ Q.Vt0h, ‖D.S0 ψ - Q.S0h ψ‖ ^ 2 ≤ (Capp * h) ^ 2 * graphSq D.dt0 ψ)
    {z : W2} {M : ℝ} (hM : 0 ≤ M) (hz : ∀ w, |⟪z, D.d1 w⟫| ≤ M * ‖w‖) :
    ∀ v ∈ Q.Vt1h, |⟪z, (D.S1 - Q.S1h) v⟫| ≤
      Capp * h * weakConsistencyConst Cp CS CP Cinc Creg ‖z‖ M *
        √(graphSq D.dt1 v) :=
  HS.weakConsistency_of_potential_of_bound hH B Rg.Cinc_nonneg Rg.Creg_nonneg hh hCapp
    (fun v hv => by
      obtain ⟨y, hy1, hy2⟩ := Rg.exists_potential v hv
      have hah : 0 ≤ Capp * h := mul_nonneg hCapp hh
      exact ⟨Rg.R y, hy1, (Rg.norm_R_le y).trans (by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hy2 Rg.Cinc_nonneg),
        (Rg.approx_Pt1 y).trans (mul_le_mul_of_nonneg_left hy2 hah),
        (Rg.approx_S1 y).trans (mul_le_mul_of_nonneg_left hy2 hah)⟩)
    happ0 hM hz

end HarmonicStability

end Feec.BGG

namespace Feec.BGG.Discrete

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} {Q : Discrete D}

theorem weakConsistency_of_potential_of_bound {Cp CR CS CP : ℝ}
    (H : Stability D Cp CR CS) (B : Q.Bounded CP) {Cinc Creg h Capp : ℝ} (hι : 0 ≤ Cinc)
    (hr : 0 ≤ Creg) (hh : 0 ≤ h) (hCapp : 0 ≤ Capp)
    (hpot : ∀ v ∈ Q.Vt1h, ∃ w, D.dt1 w = D.dt1 v ∧ ‖w‖ ≤ Cinc * Creg * ‖D.dt1 v‖ ∧
      ‖w - Q.Pt1 w‖ ≤ Capp * h * (Creg * ‖D.dt1 v‖) ∧
      ‖(D.S1 - Q.S1h) w‖ ≤ Capp * h * (Creg * ‖D.dt1 v‖))
    (happ0 : ∀ ψ ∈ Q.Vt0h, ‖D.S0 ψ - Q.S0h ψ‖ ^ 2 ≤ (Capp * h) ^ 2 * graphSq D.dt0 ψ)
    {z : W2} {M : ℝ} (hM : 0 ≤ M) (hz : ∀ w, |⟪z, D.d1 w⟫| ≤ M * ‖w‖) :
    ∀ v ∈ Q.Vt1h, |⟪z, (D.S1 - Q.S1h) v⟫| ≤
      Capp * h * weakConsistencyConst Cp CS CP Cinc Creg ‖z‖ M * √(graphSq D.dt1 v) :=
  H.toHarmonicStability.weakConsistency_of_potential_of_bound bot_le B hι hr hh hCapp hpot happ0
    hM hz

theorem weakConsistency_of_regularPotential_of_bound {Cp CR CS CP : ℝ}
    (H : Stability D Cp CR CS) (B : Q.Bounded CP) {Xr : Type*} [NormedAddCommGroup Xr]
    [NormedSpace ℝ Xr] {Cinc Creg h Capp : ℝ} (hh : 0 ≤ h) (hCapp : 0 ≤ Capp)
    (Rg : Q.RegularPotential Xr Cinc Creg Capp h)
    (happ0 : ∀ ψ ∈ Q.Vt0h, ‖D.S0 ψ - Q.S0h ψ‖ ^ 2 ≤ (Capp * h) ^ 2 * graphSq D.dt0 ψ)
    {z : W2} {M : ℝ} (hM : 0 ≤ M) (hz : ∀ w, |⟪z, D.d1 w⟫| ≤ M * ‖w‖) :
    ∀ v ∈ Q.Vt1h, |⟪z, (D.S1 - Q.S1h) v⟫| ≤
      Capp * h * weakConsistencyConst Cp CS CP Cinc Creg ‖z‖ M * √(graphSq D.dt1 v) :=
  H.toHarmonicStability.weakConsistency_of_regularPotential_of_bound bot_le B hh hCapp Rg happ0
    hM hz

/-- Under `Stability`, `Bounded`, the consistency of `S₀,ₕ` and regular potentials, every
`z ∈ D(d¹*)` has `|⟪z, (S₁ − S₁,ₕ)v⟫| ≤ C_app h K ‖v‖_V` on `Ṽₕ¹`. -/
theorem weakConsistency_of_regularPotential {Cp CR CS CP : ℝ} (H : Stability D Cp CR CS)
    (B : Q.Bounded CP) {Xr : Type*} [NormedAddCommGroup Xr] [NormedSpace ℝ Xr]
    {Cinc Creg h Capp : ℝ} (hh : 0 ≤ h) (hCapp : 0 ≤ Capp)
    (Rg : Q.RegularPotential Xr Cinc Creg Capp h)
    (happ0 : ∀ ψ ∈ Q.Vt0h, ‖D.S0 ψ - Q.S0h ψ‖ ^ 2 ≤ (Capp * h) ^ 2 * graphSq D.dt0 ψ)
    {z : W2} {z' : V1} (hz : ∀ w, ⟪z, D.d1 w⟫ = ⟪z', w⟫) :
    ∀ v ∈ Q.Vt1h, |⟪z, (D.S1 - Q.S1h) v⟫| ≤
      Capp * h * weakConsistencyConst Cp CS CP Cinc Creg ‖z‖ ‖z'‖ * √(graphSq D.dt1 v) :=
  weakConsistency_of_regularPotential_of_bound H B hh hCapp Rg happ0 (norm_nonneg z') fun w => by
    rw [hz]; exact abs_real_inner_le_norm z' w

/-- The a priori estimate of (5.6) under `Stability`, `Bounded`, (5.4), `O(h)` consistency of
`S₀,ₕ`, regular potentials and `S₁u ∈ D(d¹*)`. [QuennevilleBelair2015], Thm 5.5 (adapted) -/
theorem error_estimate_of_regularPotential {Cp CR CS CP : ℝ} (H : Stability D Cp CR CS)
    (B : Q.Bounded CP) (h54 : Q.Compatible) [FiniteDimensional ℝ Q.Vt1h]
    {Xr : Type*} [NormedAddCommGroup Xr] [NormedSpace ℝ Xr] {Cinc Creg h Capp : ℝ}
    (hh : 0 ≤ h) (hCapp : 0 ≤ Capp) (Rg : Q.RegularPotential Xr Cinc Creg Capp h)
    (happ0 : ∀ ψ ∈ Q.Vt0h, ‖D.S0 ψ - Q.S0h ψ‖ ^ 2 ≤ (Capp * h) ^ 2 * graphSq D.dt0 ψ)
    {σ : V0} {φ : Vt0} {u : Vt1} {z' : V1} (hz : ∀ w, ⟪D.S1 u, D.d1 w⟫ = ⟪z', w⟫)
    (ℓ : V1 →ₗ[ℝ] ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hℓ : ∀ μ, |ℓ μ| ≤ Λ * ‖μ‖) (F : Vt1 →ₗ[ℝ] ℝ)
    (c1 : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, ⟪σ, τ⟫ - ⟪u, D.dt0 ψ⟫ - ℓ (D.d0 τ - D.S0 ψ) = 0)
    (c2 : ∀ v ∈ Q.Vt1h, ⟪D.dt0 φ, v⟫ + ⟪D.S1 u, D.S1 v⟫ + ⟪D.dt1 u, D.dt1 v⟫ = F v)
    (c3 : D.d0 σ = D.S0 φ)
    {σh : V0} {φh : Vt0} {uh : Vt1} {lh : V1}
    (hσh : σh ∈ Q.V0h) (hφh : φh ∈ Q.Vt0h) (huh : uh ∈ Q.Vt1h)
    (h1 : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, ⟪σh, τ⟫ - ⟪uh, D.dt0 ψ⟫ - ⟪lh, D.d0 τ - Q.S0h ψ⟫ = 0)
    (h2 : ∀ v ∈ Q.Vt1h, ⟪D.dt0 φh, v⟫ + ⟪Q.S1h uh, Q.S1h v⟫ + ⟪D.dt1 uh, D.dt1 v⟫ = F v)
    (h3 : ∀ μ ∈ Q.V1h, ⟪D.d0 σh - Q.S0h φh, μ⟫ = 0) :
    graphSq D.d0 (σ - σh) + graphSq D.dt0 (φ - φh) + Q.gnSq (u - uh) ≤
      errorConst Cp CR CS CP Capp * (graphSq D.d0 (Q.P0 σ - σ) + graphSq D.dt0 (Q.Pt0 φ - φ)
        + Q.gnSq (Q.Pt1 u - u) + h ^ 2 * Λ ^ 2
        + h ^ 2 * weakConsistencyConst Cp CS CP Cinc Creg ‖D.S1 u‖ ‖z'‖ ^ 2
        + ‖D.S1 u - Q.S1h u‖ ^ 2) :=
  error_estimate_of_weakConsistency H B h54 hh hCapp happ0
    (weakConsistency_of_regularPotential H B hh hCapp Rg happ0 hz) ℓ hΛ hℓ F c1 c2 c3
    hσh hφh huh h1 h2 h3

end Feec.BGG.Discrete
