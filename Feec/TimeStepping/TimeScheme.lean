module

public import Feec.TimeStepping.Convergence

/-!
# Time schemes for families of bounded generators

A **time scheme** (`Feec.TimeStepping.TimeScheme L`) for a family of bounded generators
`Lₕ : Xₕ → Xₕ` on Banach spaces, indexed by `h` (the mesh): time steps `τₕ > 0` and one-step
operators `Pₕ`, power bounded on every horizon, `‖Pₕⁿ‖ ≤ M(T)` for `n τₕ ≤ T`, and consistent of
order `p ≥ 1` with constant `K` with the flows `e^{τₕ Lₕ}` (`Feec.TimeStepping.IsConsistent`), with
`M`, `K`, `p` independent of `h`. The scheme is any operator family: implicit (A-stable,
unconditionally stable) or explicit (stable under a CFL condition, which then enters through
`τₕ`).

When the flows are bounded, `‖e^{tLₕ}‖ ≤ M_L` for `t ≥ 0`:

* `TimeScheme.norm_exp_sub_pow_le`: the temporal error against every smoother datum `w`,
  `‖e^{tₙ Lₕ} v - Pₕⁿ v‖ ≤ (M_L + M(T)) ‖v - w‖ + M(T) K M_L tₙ τₕᵖ ‖Lₕ^{p+1} w‖`
  (stability plus consistency, `Feec.TimeStepping.norm_pow_apply_sub_exp_le_of_norm_exp_le`);
* `TimeScheme.norm_exp_sub_pow_le_of_timeAvg`: no power of `Lₕ` when `w` is the smoothed datum
  `A_δ^{p+1} u` (`Feec.TimeStepping.timeAvg`), for data that move slowly on `[0, δ]`.

With `M_L` independent of `h`, so are all constants. The downstream discretizations
`Feec.TimeStepping.BanachFEEC` (Banach spaces, `M_L` the bound of the discrete semigroups) and
`Feec.HilbertComplex.DissipFEEC` (Hilbert spaces, dissipative `Lₕ`, `M_L = 1`) use these schemes
(`Feec.TimeStepping.BanachFEEC.TimeScheme`, `Feec.HilbertComplex.DissipFEEC.TimeScheme`).

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set NormedSpace Finset

@[expose] public noncomputable section

namespace Feec.TimeStepping

variable {𝕜 : Type*} [RCLike 𝕜] {κ : Type*} {X : κ → Type*} [∀ h, NormedAddCommGroup (X h)]
  [∀ h, NormedSpace 𝕜 (X h)]

/-- A **time scheme** for the family of bounded generators `Lₕ`: time steps `τₕ > 0` and
one-step operators `Pₕ` on `Xₕ`, power bounded on every horizon `[0, T]` by `M T`
(`‖Pₕⁿ‖ ≤ M T` for `n τₕ ≤ T`, so quasi-contractive schemes, `M T = e^{ωT}`, are admitted) and
consistent of order `p ≥ 1` with constant `K` with the flows `e^{τₕ Lₕ}`, all uniformly in `h`.
[Thomee2006], Ch. 7 -/
structure TimeScheme (L : ∀ h, X h →L[𝕜] X h) where
  /-- the time steps -/
  τ : κ → ℝ
  τ_pos : ∀ h, 0 < τ h
  /-- the one-step operators -/
  P : ∀ h, X h →L[𝕜] X h
  /-- the stability constant on `[0, T]` -/
  M : ℝ → ℝ
  stable : ∀ (T : ℝ) (h : κ) (n : ℕ), (n : ℝ) * τ h ≤ T → ‖P h ^ n‖ ≤ M T
  /-- the order -/
  p : ℕ
  p_pos : 0 < p
  /-- the consistency constant -/
  K : ℝ
  K_nonneg : 0 ≤ K
  consistent : ∀ h, IsConsistent (L h) (P h) (τ h) p K

namespace TimeScheme

variable {L : ∀ h, X h →L[𝕜] X h} (Θ : TimeScheme L)

theorem M_nonneg {T : ℝ} (hT : 0 ≤ T) (h : κ) : 0 ≤ Θ.M T :=
  (norm_nonneg _).trans (Θ.stable T h 0 (by simpa using hT))

/-- The powers `Pₕᵏ`, `k ≤ n`, are bounded by `M(T)` when `n τₕ ≤ T`. -/
theorem stable_le {T : ℝ} (h : κ) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ∀ k ≤ n, ‖Θ.P h ^ k‖ ≤ Θ.M T := fun k hk =>
  Θ.stable T h k ((mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (Θ.τ_pos h).le).trans hn)

variable [∀ h, CompleteSpace (X h)] [∀ h, NormedSpace ℝ (X h)] [∀ h, IsScalarTower ℝ 𝕜 (X h)]
  {ML : ℝ}

/-- **The temporal error against any smoother datum** `w`, for flows bounded by `M_L`:
`‖e^{tₙ Lₕ} v - Pₕⁿ v‖ ≤ (M_L + M(T)) ‖v - w‖ + M(T) K M_L tₙ τₕᵖ ‖Lₕ^{p+1} w‖` for `tₙ ≤ T`.
[BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem norm_exp_sub_pow_le {T : ℝ} {h : κ}
    (hL : ∀ t : ℝ, 0 ≤ t → ‖exp ((t : 𝕜) • L h)‖ ≤ ML) (v w : X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) :
    ‖exp (((n * Θ.τ h : ℝ) : 𝕜) • L h) v - (Θ.P h ^ n) v‖ ≤
      (ML + Θ.M T) * ‖v - w‖ +
        Θ.M T * Θ.K * ML * (n * Θ.τ h) * Θ.τ h ^ Θ.p * ‖(L h ^ (Θ.p + 1)) w‖ := by
  have ht : 0 ≤ (n : ℝ) * Θ.τ h := mul_nonneg (Nat.cast_nonneg n) (Θ.τ_pos h).le
  have h1 := ((exp (((n * Θ.τ h : ℝ) : 𝕜) • L h)).le_opNorm (v - w)).trans
    (mul_le_mul_of_nonneg_right (hL _ ht) (norm_nonneg _))
  have h2 := norm_pow_apply_sub_exp_le_of_norm_exp_le hL (Θ.stable_le h hn)
    (Θ.τ_pos h).le Θ.K_nonneg (Θ.consistent h) w
  have h3 := ((Θ.P h ^ n).le_opNorm (v - w)).trans
    (mul_le_mul_of_nonneg_right (Θ.stable T h n hn) (norm_nonneg _))
  have e : exp (((n * Θ.τ h : ℝ) : 𝕜) • L h) v - (Θ.P h ^ n) v =
      exp (((n * Θ.τ h : ℝ) : 𝕜) • L h) (v - w) -
        ((Θ.P h ^ n) w - exp (((n * Θ.τ h : ℝ) : 𝕜) • L h) w) - (Θ.P h ^ n) (v - w) := by
    simp only [_root_.map_sub]; abel
  rw [e]
  have h4 := norm_sub_le (exp (((n * Θ.τ h : ℝ) : 𝕜) • L h) (v - w) -
    ((Θ.P h ^ n) w - exp (((n * Θ.τ h : ℝ) : 𝕜) • L h) w)) ((Θ.P h ^ n) (v - w))
  have h5 := norm_sub_le (exp (((n * Θ.τ h : ℝ) : 𝕜) • L h) (v - w))
    ((Θ.P h ^ n) w - exp (((n * Θ.τ h : ℝ) : 𝕜) • L h) w)
  linarith

/-- **The temporal error of a slowly varying datum**, for flows bounded by `M_L`: if
`‖e^{sLₕ} u - u‖ ≤ η` for `s ∈ [0, δ]`, then for `tₙ ≤ T`
`‖e^{tₙ Lₕ} u - Pₕⁿ u‖ ≤ (M_L + M(T)) (Σ_{j ≤ p} M_Lʲ) η`
`+ M(T) K M_L tₙ τₕᵖ ((M_L + 1)/δ)^{p+1} ‖u‖`: `u` is compared with the smoothed
`A_δ^{p+1} u` (`timeAvg`), so no power of `Lₕ` enters. [BrennerThomee1979] -/
theorem norm_exp_sub_pow_le_of_timeAvg {T δ η : ℝ} {h : κ}
    (hL : ∀ t : ℝ, 0 ≤ t → ‖exp ((t : 𝕜) • L h)‖ ≤ ML) (u : X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ≤ T) (hδ : 0 < δ)
    (hη : ∀ s ∈ Icc 0 δ, ‖exp ((s : 𝕜) • L h) u - u‖ ≤ η) :
    ‖exp (((n * Θ.τ h : ℝ) : 𝕜) • L h) u - (Θ.P h ^ n) u‖ ≤
      (ML + Θ.M T) * ((∑ j ∈ range (Θ.p + 1), ML ^ j) * η) +
        Θ.M T * Θ.K * ML * (n * Θ.τ h) * Θ.τ h ^ Θ.p *
          (((ML + 1) / δ) ^ (Θ.p + 1) * ‖u‖) := by
  have hM := Θ.M_nonneg ((mul_nonneg (Nat.cast_nonneg n) (Θ.τ_pos h).le).trans hn) h
  have hML : 0 ≤ ML := (norm_nonneg _).trans (hL 0 le_rfl)
  have := Θ.K_nonneg
  have := (Θ.τ_pos h).le
  have hLδ : ∀ s ∈ Icc 0 δ, ‖exp ((s : 𝕜) • L h)‖ ≤ ML := fun s hs => hL s hs.1
  refine (Θ.norm_exp_sub_pow_le hL u ((timeAvg (L h) δ)^[Θ.p + 1] u) hn).trans ?_
  gcongr
  · rw [norm_sub_rev]
    refine (norm_timeAvg_iterate_sub_le_of_norm_exp_le hLδ hδ _ u).trans ?_
    gcongr
    exact norm_timeAvg_sub_le hδ hη
  · exact norm_pow_timeAvg_iterate_le_of_norm_exp_le (hL δ hδ.le) hδ _ u

end TimeScheme

end Feec.TimeStepping
