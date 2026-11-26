module

public import Feec.ForMathlib.Analysis.Inequalities
public import Feec.HilbertComplex.BGG.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Discretization of the BGG complex with compatible cochain projections

For subcomplexes of the two rows of real BGG data with cochain projections and discrete
connecting maps `S₀,ₕ = Π¹S₀`, `S₁,ₕ = Π²S₁` satisfying the compatibility condition (5.4), the
discrete mixed system (5.6) of [QuennevilleBelair2015], §5.2 is uniquely solvable under
`Stability`, with discrete Poincaré inequalities uniform in `h` for uniformly bounded projections.

## Main results

* `existsUnique_isMixedSolution`: unique solvability of (5.6).
* `Discrete.poincare_Zh`: a discrete Poincaré inequality uniform in `h`.
* `Discrete.existsUnique_mixed_h`: unique solvability in the discretization.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.2

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace Feec.BGG

/-! ## Part 1: finite-dimensional algebra of the discrete system -/

section Generic

variable {X0 X1 X2 Y0 Y1 Y2 : Type*}
  [NormedAddCommGroup X0] [InnerProductSpace ℝ X0]
  [NormedAddCommGroup X1] [InnerProductSpace ℝ X1]
  [NormedAddCommGroup X2] [InnerProductSpace ℝ X2]
  [NormedAddCommGroup Y0] [InnerProductSpace ℝ Y0]
  [NormedAddCommGroup Y1] [InnerProductSpace ℝ Y1]
  [NormedAddCommGroup Y2] [InnerProductSpace ℝ Y2]

theorem norm_le_of_mem_orthogonal_ker {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →ₗ[ℝ] F) (C : ℝ)
    (hpre : ∀ x : E, ∃ x' : E, T x' = T x ∧ ‖x'‖ ≤ C * ‖T x‖)
    {x : E} (hx : x ∈ (LinearMap.ker T)ᗮ) : ‖x‖ ≤ C * ‖T x‖ := by
  obtain ⟨x', hTx', hx'⟩ := hpre x
  exact (Submodule.norm_le_of_mem_orthogonal_of_sub_mem hx (by simp [hTx'])).trans hx'

theorem anticomm_of_comm_proj (dX1 : X1 →ₗ[ℝ] X2) (dY0 : Y0 →ₗ[ℝ] Y1)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2) (P1 : X1 →ₗ[ℝ] X1) (P2 : X2 →ₗ[ℝ] X2)
    (hcomm : ∀ x, dX1 (P1 x) = P2 (dX1 x)) (hanti : ∀ ψ, dX1 (S0 ψ) = -S1 (dY0 ψ)) (ψ : Y0) :
    dX1 (P1 (S0 ψ)) = -(P2 (S1 (dY0 ψ))) := by
  rw [hcomm, hanti, map_neg]

theorem surjective_of_comp_eq {Dm X1h Y0h : Type*} [AddCommGroup Dm] [Module ℝ Dm]
    [AddCommGroup X1h]
    [Module ℝ X1h] [AddCommGroup Y0h] [Module ℝ Y0h]
    (P1S0 : Dm →ₗ[ℝ] X1h) (S0h : Y0h →ₗ[ℝ] X1h) (Pt0 : Dm →ₗ[ℝ] Y0h)
    (h54 : S0h ∘ₗ Pt0 = P1S0) (hs : Function.Surjective P1S0) : Function.Surjective S0h :=
  fun y => let ⟨ψ, hψ⟩ := hs y; ⟨Pt0 ψ, by rw [← LinearMap.comp_apply, h54, hψ]⟩

theorem exists_of_exact_rows (dX0 : X0 →ₗ[ℝ] X1) (dX1 : X1 →ₗ[ℝ] X2) (dY0 : Y0 →ₗ[ℝ] Y1)
    (dY1 : Y1 →ₗ[ℝ] Y2) (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2)
    (hanti : ∀ ψ, dX1 (S0 ψ) = -S1 (dY0 ψ))
    (hY1 : ∀ u, dY1 u = 0 → ∃ χ, dY0 χ = u) (hX1 : ∀ μ, dX1 μ = 0 → ∃ ρ, dX0 ρ = μ)
    (u : Y1) (hS : S1 u = 0) (hd : dY1 u = 0) : ∃ ρ χ, dX0 ρ = S0 χ ∧ dY0 χ = u := by
  obtain ⟨χ, hχ⟩ := hY1 u hd
  obtain ⟨ρ, hρ⟩ := hX1 (S0 χ) (by rw [hanti, hχ, hS, neg_zero])
  exact ⟨ρ, χ, hρ, hχ⟩

/-- With `dS₀ = -S₁d`, `d` injective on `Ṽ⁰`, both rows exact in the middle and `dV⁰ + S₀Ṽ⁰ = V¹`,
the homogeneous (5.6) has only the trivial solution. [QuennevilleBelair2015], Prop 5.4 (adapted) -/
theorem eq_zero_of_mixed_homogeneous
    (dX0 : X0 →ₗ[ℝ] X1) (dX1 : X1 →ₗ[ℝ] X2) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2)
    (hanti : ∀ ψ, dX1 (S0 ψ) = -S1 (dY0 ψ))
    (hY0 : Function.Injective dY0)
    (hY1 : ∀ u, dY1 u = 0 → ∃ χ, dY0 χ = u)
    (hX1 : ∀ μ, dX1 μ = 0 → ∃ ρ, dX0 ρ = μ)
    (hB : ∀ μ : X1, ∃ τ ψ, dX0 τ - S0 ψ = μ)
    {σ : X0} {φ : Y0} {u : Y1} {l : X1}
    (h1 : ∀ τ ψ, ⟪σ, τ⟫ - ⟪u, dY0 ψ⟫ - ⟪l, dX0 τ - S0 ψ⟫ = 0)
    (h2 : ∀ v, ⟪dY0 φ, v⟫ + ⟪S1 u, S1 v⟫ + ⟪dY1 u, dY1 v⟫ = 0)
    (h3 : ∀ μ, ⟪dX0 σ - S0 φ, μ⟫ = 0) :
    σ = 0 ∧ φ = 0 ∧ u = 0 ∧ l = 0 := by
  have hc : dX0 σ - S0 φ = 0 := inner_self_eq_zero.1 (h3 _)
  have e1 := h1 σ φ
  have e2 := h2 u
  rw [hc, inner_zero_right, sub_zero] at e1
  have hsum : ⟪σ, σ⟫ + ⟪S1 u, S1 u⟫ + ⟪dY1 u, dY1 u⟫ = 0 := by
    rw [real_inner_comm (dY0 φ) u] at e1; linarith
  have n1 := real_inner_self_nonneg (x := σ)
  have n2 := real_inner_self_nonneg (x := S1 u)
  have n3 := real_inner_self_nonneg (x := dY1 u)
  have hσ : σ = 0 := inner_self_eq_zero.1 (le_antisymm (by linarith) n1)
  have hSu : S1 u = 0 := inner_self_eq_zero.1 (le_antisymm (by linarith) n2)
  have hdu : dY1 u = 0 := inner_self_eq_zero.1 (le_antisymm (by linarith) n3)
  have hφ : φ = 0 := by
    have := h2 (dY0 φ)
    rw [hSu, hdu, inner_zero_left, inner_zero_left, add_zero, add_zero] at this
    exact hY0 (by rw [inner_self_eq_zero.1 this, map_zero])
  obtain ⟨ρ, χ, hρ, hχ⟩ := exists_of_exact_rows dX0 dX1 dY0 dY1 S0 S1 hanti hY1 hX1 u hSu hdu
  have hu : u = 0 := by
    have := h1 ρ χ
    rw [hρ, sub_self, inner_zero_right, sub_zero, hσ, inner_zero_left, hχ] at this
    exact (inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith)
  refine ⟨hσ, hφ, hu, ?_⟩
  obtain ⟨τ, ψ, hτψ⟩ := hB l
  have := h1 τ ψ
  rw [hσ, hu, inner_zero_left, inner_zero_left, hτψ] at this
  exact (inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith)

theorem exists_mixed_homogeneous_of_perp
    (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2) {l : X1} (hl : l ≠ 0)
    (hperp : ∀ τ ψ, ⟪l, dX0 τ - S0 ψ⟫ = 0) :
    ∃ (σ : X0) (φ : Y0) (u : Y1) (m : X1), m ≠ 0 ∧
      (∀ τ ψ, ⟪σ, τ⟫ - ⟪u, dY0 ψ⟫ - ⟪m, dX0 τ - S0 ψ⟫ = 0) ∧
      (∀ v, ⟪dY0 φ, v⟫ + ⟪S1 u, S1 v⟫ + ⟪dY1 u, dY1 v⟫ = 0) ∧
      (∀ μ, ⟪dX0 σ - S0 φ, μ⟫ = 0) :=
  ⟨0, 0, 0, l, hl, fun τ ψ => by simp [hperp], fun v => by simp, fun μ => by simp⟩

/-- The discrete system (5.6) with right-hand side `F`, unknown `x = (σ, φ, u, λ)`. -/
def IsMixedSolution (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2) (F : Y1 →ₗ[ℝ] ℝ) (x : X0 × Y0 × Y1 × X1) : Prop :=
  (∀ τ ψ, ⟪x.1, τ⟫ - ⟪x.2.2.1, dY0 ψ⟫ - ⟪x.2.2.2, dX0 τ - S0 ψ⟫ = 0) ∧
  (∀ v, ⟪dY0 x.2.1, v⟫ + ⟪S1 x.2.2.1, S1 v⟫ + ⟪dY1 x.2.2.1, dY1 v⟫ = F v) ∧
  (∀ μ, ⟪dX0 x.1 - S0 x.2.1, μ⟫ = 0)

/-- The bilinear form of the discrete system (5.6), as a map `E_h → E_h^*`. -/
def mixedForm (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2) :
    (X0 × Y0 × Y1 × X1) →ₗ[ℝ] Module.Dual ℝ (X0 × Y0 × Y1 × X1) :=
  LinearMap.mk₂ ℝ (fun x y =>
      ⟪x.1, y.1⟫ - ⟪x.2.2.1, dY0 y.2.1⟫ - ⟪x.2.2.2, dX0 y.1 - S0 y.2.1⟫
      + (⟪dY0 x.2.1, y.2.2.1⟫ + ⟪S1 x.2.2.1, S1 y.2.2.1⟫ + ⟪dY1 x.2.2.1, dY1 y.2.2.1⟫)
      + ⟪dX0 x.1 - S0 x.2.1, y.2.2.2⟫)
    (by intros; simp only [Prod.fst_add, Prod.snd_add, map_add, inner_add_left,
          inner_sub_left, inner_sub_right]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, map_smul, inner_sub_left,
          inner_sub_right, real_inner_smul_left, smul_eq_mul]; ring)
    (by intros; simp only [Prod.fst_add, Prod.snd_add, map_add, inner_add_right,
          inner_sub_left, inner_sub_right]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, map_smul, inner_sub_left,
          inner_sub_right, real_inner_smul_right, smul_eq_mul]; ring)

theorem isMixedSolution_iff (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2) (F : Y1 →ₗ[ℝ] ℝ) (x : X0 × Y0 × Y1 × X1) :
    IsMixedSolution dX0 dY0 dY1 S0 S1 F x ↔
      mixedForm dX0 dY0 dY1 S0 S1 x =
        F ∘ₗ (LinearMap.fst ℝ Y1 X1) ∘ₗ (LinearMap.snd ℝ Y0 (Y1 × X1)) ∘ₗ
          (LinearMap.snd ℝ X0 (Y0 × Y1 × X1)) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine LinearMap.ext fun y => ?_
    simp only [mixedForm, LinearMap.mk₂_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply]
    rw [h1, h2, h3]; ring
  · intro h
    have key := fun y => LinearMap.congr_fun h y
    simp only [mixedForm, LinearMap.mk₂_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply] at key
    refine ⟨fun τ ψ => ?_, fun v => ?_, fun μ => ?_⟩
    · simpa using key (τ, ψ, 0, 0)
    · simpa using key (0, 0, v, 0)
    · simpa using key (0, 0, 0, μ)

theorem mixedForm_bijective (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1)
    (dY1 : Y1 →ₗ[ℝ] Y2) (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2)
    [FiniteDimensional ℝ X0] [FiniteDimensional ℝ X1] [FiniteDimensional ℝ Y0]
    [FiniteDimensional ℝ Y1]
    (huniq : ∀ x, mixedForm dX0 dY0 dY1 S0 S1 x = 0 → x = 0) :
    Function.Bijective (mixedForm dX0 dY0 dY1 S0 S1) := by
  have hinj : Function.Injective (mixedForm dX0 dY0 dY1 S0 S1) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']; exact huniq
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    Subspace.dual_finrank_eq.symm).1 hinj⟩

/-- For finite-dimensional spaces, under the hypotheses of `eq_zero_of_mixed_homogeneous`, (5.6) has
exactly one solution for every right-hand side. [QuennevilleBelair2015], Prop 5.4 (adapted) -/
theorem existsUnique_isMixedSolution
    [FiniteDimensional ℝ X0] [FiniteDimensional ℝ X1] [FiniteDimensional ℝ Y0]
    [FiniteDimensional ℝ Y1]
    (dX0 : X0 →ₗ[ℝ] X1) (dX1 : X1 →ₗ[ℝ] X2) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2)
    (hanti : ∀ ψ, dX1 (S0 ψ) = -S1 (dY0 ψ))
    (hY0 : Function.Injective dY0)
    (hY1 : ∀ u, dY1 u = 0 → ∃ χ, dY0 χ = u)
    (hX1 : ∀ μ, dX1 μ = 0 → ∃ ρ, dX0 ρ = μ)
    (hB : ∀ μ : X1, ∃ τ ψ, dX0 τ - S0 ψ = μ) (F : Y1 →ₗ[ℝ] ℝ) :
    ∃! x, IsMixedSolution dX0 dY0 dY1 S0 S1 F x := by
  have hbij := mixedForm_bijective dX0 dY0 dY1 S0 S1 (fun x hx => by
    have h0 := (isMixedSolution_iff dX0 dY0 dY1 S0 S1 0 x).2 (by rw [hx]; exact LinearMap.ext fun y => by simp)
    obtain ⟨h1, h2, h3⟩ := h0
    obtain ⟨e1, e2, e3, e4⟩ := eq_zero_of_mixed_homogeneous dX0 dX1 dY0 dY1 S0 S1 hanti hY0 hY1 hX1 hB h1
      (fun v => by simpa using h2 v) h3
    ext <;> simp [e1, e2, e3, e4])
  obtain ⟨x, hx⟩ := hbij.2 (F ∘ₗ (LinearMap.fst ℝ Y1 X1) ∘ₗ (LinearMap.snd ℝ Y0 (Y1 × X1)) ∘ₗ
    (LinearMap.snd ℝ X0 (Y0 × Y1 × X1)))
  refine ⟨x, (isMixedSolution_iff _ _ _ _ _ F x).2 hx, fun y hy => hbij.1 ?_⟩
  rw [hx, ← (isMixedSolution_iff _ _ _ _ _ F y).1 hy]

/-- The error equation of (5.6), for arbitrary `Pσ, Pφ, Pu` and any linear functional `ℓ`.
[QuennevilleBelair2015], Prop 5.6 (adapted) -/
theorem mixed_error_eq
    (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 S0h : Y0 →ₗ[ℝ] X1) (S1 S1h : Y1 →ₗ[ℝ] X2) (ℓ : X1 →ₗ[ℝ] ℝ) (F : Y1 →ₗ[ℝ] ℝ)
    (σ Pσ σh τ : X0) (φ Pφ φh ψ : Y0) (u Pu uh v : Y1) (lh : X1)
    (c1 : ⟪σ, τ⟫ - ⟪u, dY0 ψ⟫ - ℓ (dX0 τ - S0 ψ) = 0)
    (c2 : ⟪dY0 φ, v⟫ + ⟪S1 u, S1 v⟫ + ⟪dY1 u, dY1 v⟫ = F v)
    (h1 : ⟪σh, τ⟫ - ⟪uh, dY0 ψ⟫ - ⟪lh, dX0 τ - S0h ψ⟫ = 0)
    (h2 : ⟪dY0 φh, v⟫ + ⟪S1h uh, S1h v⟫ + ⟪dY1 uh, dY1 v⟫ = F v) :
    ⟪Pσ - σh, τ⟫ - ⟪Pu - uh, dY0 ψ⟫ - (ℓ (dX0 τ - S0h ψ) - ⟪lh, dX0 τ - S0h ψ⟫)
      + ⟪dY0 (Pφ - φh), v⟫ + ⟪S1h (Pu - uh), S1h v⟫ + ⟪dY1 (Pu - uh), dY1 v⟫
    = ⟪Pσ - σ, τ⟫ - ⟪Pu - u, dY0 ψ⟫ - ℓ ((S0 - S0h) ψ)
      + ⟪dY0 (Pφ - φ), v⟫ - ⟪S1 u, (S1 - S1h) v⟫ - ⟪(S1 - S1h) u, S1h v⟫
      + ⟪S1h (Pu - u), S1h v⟫ + ⟪dY1 (Pu - u), dY1 v⟫ := by
  simp only [map_sub, LinearMap.sub_apply, inner_sub_left, inner_sub_right] at *
  linear_combination c1 - h1 + c2 - h2

theorem mixed_coercivity_eq
    (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0h : Y0 →ₗ[ℝ] X1) (S1h : Y1 →ₗ[ℝ] X2)
    (hdd : ∀ x, dY1 (dY0 x) = 0)
    (eσ ρ : X0) (eφ χ : Y0) (ω : Y1) (eL : X1) (ε : ℝ)
    (hΓe : dX0 eσ = S0h eφ) (hΓ : dX0 ρ = S0h χ)
    (hSdχ : S1h (dY0 χ) = 0) (hSdeφ : S1h (dY0 eφ) = 0)
    (hωχ : ⟪ω, dY0 χ⟫ = 0) :
    ⟪eσ, eσ - ε • ρ⟫ - ⟪dY0 χ + ω, dY0 (eφ - ε • χ)⟫
      - ⟪eL, dX0 (eσ - ε • ρ) - S0h (eφ - ε • χ)⟫
      + ⟪dY0 eφ, dY0 eφ + dY0 χ + ω⟫ + ⟪S1h (dY0 χ + ω), S1h (dY0 eφ + dY0 χ + ω)⟫
      + ⟪dY1 (dY0 χ + ω), dY1 (dY0 eφ + dY0 χ + ω)⟫
    = ‖eσ‖ ^ 2 - ε * ⟪eσ, ρ⟫ + ε * ‖dY0 χ‖ ^ 2 + ‖dY0 eφ‖ ^ 2 + ‖S1h ω‖ ^ 2
      + ‖dY1 ω‖ ^ 2 := by
  simp only [map_add, map_sub, map_smul, hdd,
    hSdχ, hSdeφ, zero_add, inner_add_left, inner_add_right,
    inner_sub_right, real_inner_smul_right, ← real_inner_self_eq_norm_sq]
  rw [hΓe, hΓ, hωχ, real_inner_comm (dY0 χ) (dY0 eφ), real_inner_comm ω (dY0 eφ)]
  ring

end Generic

/-! ## Part 2: the discretization of the BGG complex -/

/-- Squared graph norm `‖x‖² + ‖d x‖²` (the `V`-norm squared). -/
def graphSq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (d : E →ₗ[ℝ] F) (x : E) : ℝ :=
  ‖x‖ ^ 2 + ‖d x‖ ^ 2

theorem graphSq_nonneg {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (d : E →ₗ[ℝ] F) (x : E) : 0 ≤ graphSq d x := by
  unfold graphSq; positivity

theorem graphSq_sub_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (d : E →ₗ[ℝ] F) (x y : E) :
    graphSq d (x - y) ≤ 2 * graphSq d x + 2 * graphSq d y := by
  unfold graphSq; rw [map_sub]
  nlinarith [norm_sub_sq_le_two_mul x y, norm_sub_sq_le_two_mul (d x) (d y)]

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]

/-- The continuous hypotheses of [QuennevilleBelair2015], Prop 5.3 for the BGG data `D`. -/
structure Stability (D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2) (Cp CR CS : ℝ) : Prop where
  Cp_nonneg : 0 ≤ Cp
  CR_nonneg : 0 ≤ CR
  CS_nonneg : 0 ≤ CS
  poinc0 : ∀ σ, ‖σ‖ ≤ Cp * ‖D.d0 σ‖
  poinct0 : ∀ φ, ‖φ‖ ≤ Cp * ‖D.dt0 φ‖
  exact1 : ∀ μ, D.d1 μ = 0 → ∃ ρ, D.d0 ρ = μ
  hodget1 : ∀ v, ∃ ψ w, v = D.dt0 ψ + w ∧ ‖w‖ ≤ Cp * ‖D.dt1 v‖
  reg : ∀ x, ∃ φ, D.d1 (D.S0 φ) = D.d1 x ∧ ‖D.dt0 φ‖ ≤ CR * ‖D.d1 x‖
  boundS0 : ∀ ψ, graphSq D.d1 (D.S0 ψ) ≤ CS ^ 2 * graphSq D.dt0 ψ
  boundS1 : ∀ v, ‖D.S1 v‖ ^ 2 ≤ CS ^ 2 * graphSq D.dt1 v

theorem hodge_bot_of_poincare (D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2) {Cp : ℝ}
    [(LinearMap.ker D.dt1).HasOrthogonalProjection]
    (hex : LinearMap.ker D.dt1 = LinearMap.range D.dt0)
    (hP : ∀ w ∈ (LinearMap.ker D.dt1)ᗮ, ‖w‖ ≤ Cp * ‖D.dt1 w‖) (v : Vt1) :
    ∃ ψ w, v = D.dt0 ψ + w ∧ ‖w‖ ≤ Cp * ‖D.dt1 v‖ := by
  set K := LinearMap.ker D.dt1
  have hz : K.starProjection v ∈ K := K.starProjection_apply_mem v
  obtain ⟨ψ, hψ⟩ : K.starProjection v ∈ LinearMap.range D.dt0 := hex ▸ hz
  have hw := K.sub_starProjection_mem_orthogonal v
  refine ⟨ψ, v - K.starProjection v, by rw [hψ]; abel, ?_⟩
  have : D.dt1 (v - K.starProjection v) = D.dt1 v := by
    rw [map_sub, LinearMap.mem_ker.1 hz, sub_zero]
  simpa [this] using hP _ hw

/-- The continuous hypotheses on the bottom row, modulo harmonic forms `𝔥`. -/
structure HarmonicStability (D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2) (Hh : Submodule ℝ Vt1)
    (Cp CS : ℝ) : Prop where
  Cp_nonneg : 0 ≤ Cp
  CS_nonneg : 0 ≤ CS
  poinct0 : ∀ φ, ‖φ‖ ≤ Cp * ‖D.dt0 φ‖
  hodget1 : ∀ v, ∃ ψ w, ∃ k ∈ Hh, v = D.dt0 ψ + w + k ∧ ‖w‖ ≤ Cp * ‖D.dt1 v‖
  harmonic_orth : ∀ k ∈ Hh, ∀ ψ, ⟪k, D.dt0 ψ⟫ = 0
  S1_harmonic : ∀ k ∈ Hh, D.S1 k = 0
  boundS1 : ∀ v, ‖D.S1 v‖ ^ 2 ≤ CS ^ 2 * graphSq D.dt1 v

theorem Stability.toHarmonicStability {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} {Cp CR CS : ℝ}
    (H : Stability D Cp CR CS) : HarmonicStability D ⊥ Cp CS where
  Cp_nonneg := H.Cp_nonneg
  CS_nonneg := H.CS_nonneg
  poinct0 := H.poinct0
  hodget1 v := by
    obtain ⟨ψ, w, hv, hw⟩ := H.hodget1 v
    exact ⟨ψ, w, 0, Submodule.zero_mem _, by rw [hv, add_zero], hw⟩
  harmonic_orth k hk ψ := by rw [(Submodule.mem_bot ℝ).1 hk, inner_zero_left]
  S1_harmonic k hk := by rw [(Submodule.mem_bot ℝ).1 hk, map_zero]
  boundS1 := H.boundS1

namespace HarmonicStability

variable {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} {Hh : Submodule ℝ Vt1} {Cp CS : ℝ}
  (HS : HarmonicStability D Hh Cp CS)
include HS

theorem dt0_injective : Function.Injective D.dt0 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  have := HS.poinct0 φ
  rw [hφ, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

end HarmonicStability

/-- Subcomplexes of the two rows with cochain projections commuting with `d`. -/
structure Discrete (D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2) where
  V0h : Submodule ℝ V0
  V1h : Submodule ℝ V1
  W2h : Submodule ℝ W2
  Vt0h : Submodule ℝ Vt0
  Vt1h : Submodule ℝ Vt1
  Wt2h : Submodule ℝ Wt2
  d0_mem : ∀ x ∈ V0h, D.d0 x ∈ V1h
  d1_mem : ∀ x ∈ V1h, D.d1 x ∈ W2h
  dt0_mem : ∀ x ∈ Vt0h, D.dt0 x ∈ Vt1h
  dt1_mem : ∀ x ∈ Vt1h, D.dt1 x ∈ Wt2h
  P0 : V0 →ₗ[ℝ] V0
  P1 : V1 →ₗ[ℝ] V1
  P2 : W2 →ₗ[ℝ] W2
  Pt0 : Vt0 →ₗ[ℝ] Vt0
  Pt1 : Vt1 →ₗ[ℝ] Vt1
  Pt2 : Wt2 →ₗ[ℝ] Wt2
  P0_mem : ∀ x, P0 x ∈ V0h
  P1_mem : ∀ x, P1 x ∈ V1h
  P2_mem : ∀ x, P2 x ∈ W2h
  Pt0_mem : ∀ x, Pt0 x ∈ Vt0h
  Pt1_mem : ∀ x, Pt1 x ∈ Vt1h
  Pt2_mem : ∀ x, Pt2 x ∈ Wt2h
  P0_id : ∀ x ∈ V0h, P0 x = x
  P1_id : ∀ x ∈ V1h, P1 x = x
  P2_id : ∀ x ∈ W2h, P2 x = x
  Pt0_id : ∀ x ∈ Vt0h, Pt0 x = x
  Pt1_id : ∀ x ∈ Vt1h, Pt1 x = x
  Pt2_id : ∀ x ∈ Wt2h, Pt2 x = x
  comm0 : ∀ x, D.d0 (P0 x) = P1 (D.d0 x)
  comm1 : ∀ x, D.d1 (P1 x) = P2 (D.d1 x)
  commt0 : ∀ x, D.dt0 (Pt0 x) = Pt1 (D.dt0 x)
  commt1 : ∀ x, D.dt1 (Pt1 x) = Pt2 (D.dt1 x)

namespace Discrete

variable {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} (Q : Discrete D)

/-- `S₀,h = Π¹S₀` -/
def S0h : Vt0 →ₗ[ℝ] V1 := Q.P1 ∘ₗ D.S0
/-- `S₁,h = Π²S₁` -/
def S1h : Vt1 →ₗ[ℝ] W2 := Q.P2 ∘ₗ D.S1

/-- `Z_h = N(S₁,h) ∩ N(d) ∩ Ṽ_h¹` -/
def Zh : Submodule ℝ Vt1 := Q.Vt1h ⊓ (LinearMap.ker Q.S1h ⊓ LinearMap.ker D.dt1)

/-- `Γ_h = {(σ_h, φ_h) ∈ V_h⁰ × Ṽ_h⁰ | dσ_h = S₀,h φ_h}`. -/
def Γh : Submodule ℝ (V0 × Vt0) :=
  Q.V0h.prod Q.Vt0h ⊓
    LinearMap.ker (D.d0 ∘ₗ LinearMap.fst ℝ V0 Vt0 - Q.S0h ∘ₗ LinearMap.snd ℝ V0 Vt0)

theorem mem_Γh {x : V0 × Vt0} : x ∈ Q.Γh ↔ x.1 ∈ Q.V0h ∧ x.2 ∈ Q.Vt0h ∧ D.d0 x.1 = Q.S0h x.2 := by
  simp [Γh, sub_eq_zero, and_assoc]

/-- The `h`-dependent graph norm `‖w‖² + ‖S₁,h w‖² + ‖dw‖²` on `Ṽ¹` (squared). -/
def gnSq (w : Vt1) : ℝ := ‖w‖ ^ 2 + ‖Q.S1h w‖ ^ 2 + ‖D.dt1 w‖ ^ 2

/-- The compatibility condition (5.4): `Π¹ S₀ Π̃⁰ = Π¹ S₀`. -/
def Compatible : Prop := ∀ ψ, Q.P1 (D.S0 (Q.Pt0 ψ)) = Q.P1 (D.S0 ψ)

/-- Uniform bounds `C_Π` on the projections. -/
structure Bounded (CP : ℝ) : Prop where
  CP_nonneg : 0 ≤ CP
  P1 : ∀ x, graphSq D.d1 (Q.P1 x) ≤ CP ^ 2 * graphSq D.d1 x
  P2 : ∀ z, ‖Q.P2 z‖ ≤ CP * ‖z‖
  Pt1 : ∀ v, graphSq D.dt1 (Q.Pt1 v) ≤ CP ^ 2 * graphSq D.dt1 v

theorem S0h_apply (ψ : Vt0) : Q.S0h ψ = Q.P1 (D.S0 ψ) := rfl
theorem S1h_apply (v : Vt1) : Q.S1h v = Q.P2 (D.S1 v) := rfl
theorem S0h_mem (ψ : Vt0) : Q.S0h ψ ∈ Q.V1h := Q.P1_mem _
theorem S1h_mem (v : Vt1) : Q.S1h v ∈ Q.W2h := Q.P2_mem _

theorem anticomm_h (ψ : Vt0) : D.d1 (Q.S0h ψ) = -Q.S1h (D.dt0 ψ) :=
  anticomm_of_comm_proj D.d1 D.dt0 D.S0 D.S1 Q.P1 Q.P2 Q.comm1 D.anticomm ψ

variable {Q}

theorem exact_bot_h {Cp CR CS : ℝ} (H : Stability D Cp CR CS) {u : Vt1} (hu : u ∈ Q.Vt1h)
    (hd : D.dt1 u = 0) : ∃ χ ∈ Q.Vt0h, D.dt0 χ = u := by
  obtain ⟨ψ, w, rfl, hw⟩ := H.hodget1 u
  rw [hd, norm_zero, mul_zero] at hw
  have hw0 : w = 0 := norm_le_zero_iff.1 hw
  subst hw0
  refine ⟨Q.Pt0 ψ, Q.Pt0_mem ψ, ?_⟩
  rw [Q.commt0, add_zero] at *
  exact Q.Pt1_id _ hu

theorem exact_top_h {Cp CR CS : ℝ} (H : Stability D Cp CR CS) {μ : V1} (hμ : μ ∈ Q.V1h)
    (hd : D.d1 μ = 0) : ∃ ρ ∈ Q.V0h, D.d0 ρ = μ := by
  obtain ⟨ρ, hρ⟩ := H.exact1 μ hd
  exact ⟨Q.P0 ρ, Q.P0_mem ρ, by rw [Q.comm0, hρ, Q.P1_id _ hμ]⟩

theorem dt0_injective {Cp CR CS : ℝ} (H : Stability D Cp CR CS) : Function.Injective D.dt0 :=
  H.toHarmonicStability.dt0_injective

theorem exact_mid_h {Cp CR CS : ℝ} (H : Stability D Cp CR CS) {u : Vt1} (hu : u ∈ Q.Zh) :
    ∃ ρ ∈ Q.V0h, ∃ χ ∈ Q.Vt0h, D.d0 ρ = Q.S0h χ ∧ D.dt0 χ = u := by
  obtain ⟨hu1, hu2, hu3⟩ := hu
  obtain ⟨χ, hχ, rfl⟩ := exact_bot_h H hu1 hu3
  obtain ⟨ρ, hρ, hρ'⟩ := exact_top_h H (Q.S0h_mem χ)
    (by rw [Q.anticomm_h, LinearMap.mem_ker.1 hu2, neg_zero])
  exact ⟨ρ, hρ, χ, hχ, hρ', rfl⟩

theorem constraint_of_inner {σh : V0} {φh : Vt0} (hσh : σh ∈ Q.V0h)
    (h3 : ∀ μ ∈ Q.V1h, ⟪D.d0 σh - Q.S0h φh, μ⟫ = 0) : D.d0 σh = Q.S0h φh :=
  sub_eq_zero.1 (inner_self_eq_zero.1
    (h3 _ (Submodule.sub_mem _ (Q.d0_mem σh hσh) (Q.S0h_mem φh))))

theorem comp_eq_zero_h {x : V0 × Vt0} (hx : x ∈ Q.Γh) :
    Q.S1h (D.dt0 x.2) = 0 ∧ D.dt1 (D.dt0 x.2) = 0 := by
  obtain ⟨-, -, h⟩ := Q.mem_Γh.1 hx
  refine ⟨?_, D.dt1_dt0 _⟩
  have := Q.anticomm_h x.2
  rw [← h, D.d1_d0] at this
  exact neg_eq_zero.1 this.symm

theorem Zh_eq_map {Cp CR CS : ℝ} (H : Stability D Cp CR CS) :
    Q.Zh = Q.Γh.map (D.dt0 ∘ₗ LinearMap.snd ℝ V0 Vt0) := by
  ext u
  constructor
  · intro hu
    obtain ⟨ρ, hρ, χ, hχ, hρχ, rfl⟩ := exact_mid_h H hu
    exact ⟨(ρ, χ), Q.mem_Γh.2 ⟨hρ, hχ, hρχ⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hS, hd⟩ := comp_eq_zero_h hx
    exact ⟨Q.dt0_mem _ (Q.mem_Γh.1 hx).2.1, hS, hd⟩

theorem hodge_h {Cp CR CS : ℝ} (H : Stability D Cp CR CS) [FiniteDimensional ℝ Q.Vt1h]
    {w : Vt1} (hw : w ∈ Q.Vt1h) :
    ∃ x ∈ Q.Γh, ∃ ω ∈ Q.Vt1h, ω ∈ Q.Zhᗮ ∧ w = D.dt0 x.2 + ω ∧
      ∀ x' ∈ Q.Γh, ∀ ω' ∈ Q.Zhᗮ, w = D.dt0 x'.2 + ω' → D.dt0 x'.2 = D.dt0 x.2 ∧ ω' = ω := by
  have : FiniteDimensional ℝ Q.Zh := Submodule.finiteDimensional_of_le inf_le_left
  set z := Q.Zh.starProjection w
  have hz : z ∈ Q.Zh := Q.Zh.starProjection_apply_mem w
  have hω : w - z ∈ Q.Zhᗮ := Q.Zh.sub_starProjection_mem_orthogonal w
  have hzm : z ∈ Q.Γh.map (D.dt0 ∘ₗ LinearMap.snd ℝ V0 Vt0) := by rw [← Zh_eq_map H]; exact hz
  obtain ⟨x, hx, hxz⟩ := hzm
  simp only [LinearMap.comp_apply, LinearMap.snd_apply] at hxz
  refine ⟨x, hx, w - z, Submodule.sub_mem _ hw hz.1, hω, by rw [hxz]; abel, ?_⟩
  intro x' hx' ω' hω' hw'
  have hz' : D.dt0 x'.2 ∈ Q.Zh := by
    rw [Zh_eq_map H]; exact ⟨x', hx', rfl⟩
  -- `a := dx'₂ - z ∈ Z_h ∩ Z_hᗮ`
  have ha1 : D.dt0 x'.2 - z ∈ Q.Zh := Submodule.sub_mem _ hz' hz
  have ha2 : D.dt0 x'.2 - z ∈ Q.Zhᗮ := by
    have : D.dt0 x'.2 - z = (w - z) - ω' := by rw [hw']; abel
    rw [this]; exact Submodule.sub_mem _ hω hω'
  have ha : D.dt0 x'.2 - z = 0 :=
    inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal ha1 ha2)
  have hxz' : D.dt0 x'.2 = z := sub_eq_zero.1 ha
  refine ⟨hxz'.trans hxz.symm, ?_⟩
  rw [hw', hxz']; abel

theorem exists_sub_S0h_eq {Cp CR CS : ℝ} (H : Stability D Cp CR CS) (h54 : Q.Compatible) {μ : V1}
    (hμ : μ ∈ Q.V1h) :
    ∃ τ ∈ Q.V0h, ∃ ψ ∈ Q.Vt0h, D.d0 τ - Q.S0h ψ = μ := by
  obtain ⟨φ, hφ, -⟩ := H.reg μ
  obtain ⟨ρ, hρ⟩ := H.exact1 (μ - D.S0 φ) (by rw [map_sub, hφ, sub_self])
  refine ⟨Q.P0 ρ, Q.P0_mem ρ, -Q.Pt0 φ, Submodule.neg_mem _ (Q.Pt0_mem φ), ?_⟩
  rw [Q.comm0, hρ, map_neg, sub_neg_eq_add, S0h_apply, h54, ← map_add, sub_add_cancel,
    Q.P1_id _ hμ]

/-- The constant `C_a = (1 + C_p²) C_Π C_S` of [QuennevilleBelair2015], Prop 5.3(a). -/
def Ca (Cp CS CP : ℝ) : ℝ := (1 + Cp ^ 2) * CP * CS

/-- If `dσ = S₀,h φ`, then `‖σ‖_V ≤ C_a ‖dφ‖`, with `C_a` independent of `h`.
[QuennevilleBelair2015], Prop 5.3(a) (adapted) -/
theorem poincare_Γh {Cp CR CS CP : ℝ} (H : Stability D Cp CR CS) (B : Q.Bounded CP)
    {σ : V0} {φ : Vt0} (h : D.d0 σ = Q.S0h φ) :
    graphSq D.d0 σ ≤ Ca Cp CS CP ^ 2 * ‖D.dt0 φ‖ ^ 2 := by
  have hp := H.Cp_nonneg
  have hφ : graphSq D.dt0 φ ≤ (1 + Cp ^ 2) * ‖D.dt0 φ‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) (H.poinct0 φ) 2
    unfold graphSq; nlinarith
  have hσ := pow_le_pow_left₀ (norm_nonneg _) (H.poinc0 σ) 2
  have hS : ‖D.d0 σ‖ ^ 2 ≤ CP ^ 2 * CS ^ 2 * ((1 + Cp ^ 2) * ‖D.dt0 φ‖ ^ 2) := by
    have h1 : ‖D.d0 σ‖ ^ 2 ≤ graphSq D.d1 (Q.P1 (D.S0 φ)) := by
      rw [h, S0h_apply]; unfold graphSq; nlinarith [sq_nonneg ‖D.d1 (Q.P1 (D.S0 φ))‖]
    have h2 := B.P1 (D.S0 φ)
    have h3 := H.boundS0 φ
    calc ‖D.d0 σ‖ ^ 2 ≤ CP ^ 2 * graphSq D.d1 (D.S0 φ) := h1.trans h2
      _ ≤ CP ^ 2 * (CS ^ 2 * graphSq D.dt0 φ) := by gcongr
      _ ≤ CP ^ 2 * (CS ^ 2 * ((1 + Cp ^ 2) * ‖D.dt0 φ‖ ^ 2)) := by gcongr
      _ = _ := by ring
  unfold graphSq
  calc ‖σ‖ ^ 2 + ‖D.d0 σ‖ ^ 2 ≤ (1 + Cp ^ 2) * ‖D.d0 σ‖ ^ 2 := by nlinarith
    _ ≤ (1 + Cp ^ 2) * (CP ^ 2 * CS ^ 2 * ((1 + Cp ^ 2) * ‖D.dt0 φ‖ ^ 2)) := by gcongr
    _ = Ca Cp CS CP ^ 2 * ‖D.dt0 φ‖ ^ 2 := by unfold Ca; ring

/-- The constant `C_b` of [QuennevilleBelair2015], Prop 5.3(b). -/
def Cb (Cp CR CS CP : ℝ) : ℝ := CP * CR + CP * (1 + Cp) * (1 + CP ^ 2 * CR * CS)

theorem preimage_bound {Cp CR CS CP : ℝ} (H : Stability D Cp CR CS) (B : Q.Bounded CP)
    (h54 : Q.Compatible) {v : Vt1} (hv : v ∈ Q.Vt1h) :
    ∃ u' ∈ Q.Vt1h, Q.S1h u' = Q.S1h v ∧ D.dt1 u' = D.dt1 v ∧
      ‖u'‖ ≤ Cb Cp CR CS CP * (‖Q.S1h v‖ + ‖D.dt1 v‖) := by
  have hp := H.Cp_nonneg; have hR := H.CR_nonneg; have hS := H.CS_nonneg
  have hP := B.CP_nonneg
  obtain ⟨ψ, w, hvw, hw⟩ := H.hodget1 v
  set ρn := ‖D.dt1 v‖ with hρn
  have hρ0 : 0 ≤ ρn := norm_nonneg _
  have hdw : D.dt1 w = D.dt1 v := by rw [hvw, map_add, D.dt1_dt0, zero_add]
  -- `‖Π̃¹w‖ ≤ C_Π (1 + C_p) ‖dv‖`
  have hgw : graphSq D.dt1 w ≤ ((1 + Cp) * ρn) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hw 2
    unfold graphSq; rw [hdw]; nlinarith
  have hgPw : graphSq D.dt1 (Q.Pt1 w) ≤ (CP * ((1 + Cp) * ρn)) ^ 2 := by
    calc _ ≤ CP ^ 2 * graphSq D.dt1 w := B.Pt1 w
      _ ≤ CP ^ 2 * ((1 + Cp) * ρn) ^ 2 := by gcongr
      _ = _ := by ring
  have hPw : ‖Q.Pt1 w‖ ≤ CP * ((1 + Cp) * ρn) := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (le_trans ?_ hgPw)
    unfold graphSq; nlinarith [sq_nonneg ‖D.dt1 (Q.Pt1 w)‖]
  have hSPw : ‖Q.S1h (Q.Pt1 w)‖ ≤ CP * (CS * (CP * ((1 + Cp) * ρn))) := by
    rw [S1h_apply]
    refine (B.P2 _).trans (mul_le_mul_of_nonneg_left ?_ hP)
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ((H.boundS1 _).trans ?_)
    calc CS ^ 2 * graphSq D.dt1 (Q.Pt1 w) ≤ CS ^ 2 * (CP * ((1 + Cp) * ρn)) ^ 2 := by gcongr
      _ = _ := by ring
  -- `η' := S₁,h v - S₁,h Π̃¹w = -d Π¹ S₀ Π̃⁰ψ`
  set η' := Q.S1h v - Q.S1h (Q.Pt1 w) with hη'
  have hvP : v = D.dt0 (Q.Pt0 ψ) + Q.Pt1 w := by
    rw [Q.commt0, ← map_add, ← hvw, Q.Pt1_id _ hv]
  have hη'd : D.d1 (-(Q.S0h (Q.Pt0 ψ))) = η' := by
    rw [map_neg, Q.anticomm_h, neg_neg, hη', hvP, map_add, add_sub_cancel_right]
  obtain ⟨φ, hφ, hφn⟩ := H.reg (-(Q.S0h (Q.Pt0 ψ)))
  rw [hη'd] at hφ hφn
  have hη'mem : η' ∈ Q.W2h := Submodule.sub_mem _ (Q.S1h_mem _) (Q.S1h_mem _)
  refine ⟨Q.Pt1 w - D.dt0 (Q.Pt0 φ),
    Submodule.sub_mem _ (Q.Pt1_mem w) (Q.dt0_mem _ (Q.Pt0_mem φ)), ?_, ?_, ?_⟩
  · -- `S₁,h u' = S₁,h Π̃w - d Π¹ S₀ Π̃⁰φ = S₁,h Π̃w + Π² η' = S₁,h v`
    have : Q.S1h (D.dt0 (Q.Pt0 φ)) = -η' := by
      rw [← neg_eq_iff_eq_neg, ← Q.anticomm_h, S0h_apply, h54, Q.comm1, hφ, Q.P2_id _ hη'mem]
    rw [map_sub, this, sub_neg_eq_add, hη', add_sub_cancel]
  · rw [map_sub, D.dt1_dt0, sub_zero, Q.commt1, hdw, Q.Pt2_id _ (Q.dt1_mem _ hv)]
  · have hdφ : ‖D.dt0 (Q.Pt0 φ)‖ ≤ CP * (CR * (‖Q.S1h v‖ + CP * (CS * (CP * ((1 + Cp) * ρn))))) := by
      rw [Q.commt0]
      have h1 : ‖Q.Pt1 (D.dt0 φ)‖ ≤ CP * ‖D.dt0 φ‖ := by
        refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
        have := B.Pt1 (D.dt0 φ)
        unfold graphSq at this; rw [D.dt1_dt0, norm_zero] at this
        nlinarith [sq_nonneg ‖D.dt1 (Q.Pt1 (D.dt0 φ))‖]
      refine h1.trans (mul_le_mul_of_nonneg_left (hφn.trans ?_) hP)
      refine mul_le_mul_of_nonneg_left ?_ hR
      exact (norm_sub_le _ _).trans (by linarith)
    have hsum := (norm_sub_le (Q.Pt1 w) (D.dt0 (Q.Pt0 φ))).trans (add_le_add hPw hdφ)
    refine hsum.trans ?_
    unfold Cb
    have hS1v := norm_nonneg (Q.S1h v)
    nlinarith [mul_nonneg hP hR, mul_nonneg (mul_nonneg hP hR) hS1v,
      mul_nonneg (mul_nonneg (mul_nonneg hP hR) (mul_nonneg hP (mul_nonneg hS hP)))
        (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + Cp) hρ0),
      mul_nonneg (mul_nonneg hP (by linarith : (0:ℝ) ≤ 1 + Cp)) hS1v,
      mul_nonneg (mul_nonneg (mul_nonneg hP (by linarith : (0:ℝ) ≤ 1 + Cp))
        (mul_nonneg (mul_nonneg (pow_nonneg hP 2) hR) hS)) hS1v]

/-- For `u ∈ Ṽ_h¹` with `u ⊥ Z_h`, `‖u‖ ≤ C_b (‖S₁,h u‖ + ‖d u‖)`, with `C_b` independent of `h`.
[QuennevilleBelair2015], Prop 5.3(b) (adapted) -/
theorem poincare_Zh {Cp CR CS CP : ℝ} (H : Stability D Cp CR CS) (B : Q.Bounded CP)
    (h54 : Q.Compatible) {u : Vt1} (hu : u ∈ Q.Vt1h) (horth : u ∈ Q.Zhᗮ) :
    ‖u‖ ≤ Cb Cp CR CS CP * (‖Q.S1h u‖ + ‖D.dt1 u‖) := by
  obtain ⟨u', hu', h1, h2, h3⟩ := preimage_bound H B h54 hu
  refine (Submodule.norm_le_of_mem_orthogonal_of_sub_mem horth ?_).trans h3
  exact ⟨Submodule.sub_mem _ hu' hu, by simp [h1], by simp [h2]⟩

/-- Under `Stability` and (5.4), with finite-dimensional discrete spaces, (5.6) has exactly one
solution for every `F`. [QuennevilleBelair2015], Prop 5.4 (adapted) -/
theorem existsUnique_mixed_h {Cp CR CS : ℝ} (H : Stability D Cp CR CS) (h54 : Q.Compatible)
    [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.V1h] [FiniteDimensional ℝ Q.Vt0h]
    [FiniteDimensional ℝ Q.Vt1h] (F : Vt1 →ₗ[ℝ] ℝ) :
    ∃! x : Q.V0h × Q.Vt0h × Q.Vt1h × Q.V1h,
      (∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, ⟪(x.1 : V0), τ⟫ - ⟪(x.2.2.1 : Vt1), D.dt0 ψ⟫
        - ⟪(x.2.2.2 : V1), D.d0 τ - Q.S0h ψ⟫ = 0) ∧
      (∀ v ∈ Q.Vt1h, ⟪D.dt0 x.2.1, v⟫ + ⟪Q.S1h x.2.2.1, Q.S1h v⟫
        + ⟪D.dt1 x.2.2.1, D.dt1 v⟫ = F v) ∧
      (∀ μ ∈ Q.V1h, ⟪D.d0 x.1 - Q.S0h x.2.1, μ⟫ = 0) := by
  let dX0 := D.d0.restrict Q.d0_mem
  let dX1 := D.d1.restrict Q.d1_mem
  let dY0 := D.dt0.restrict Q.dt0_mem
  let dY1 := D.dt1.restrict Q.dt1_mem
  let S0' : Q.Vt0h →ₗ[ℝ] Q.V1h := Q.S0h.restrict (fun x _ => Q.S0h_mem x)
  let S1' : Q.Vt1h →ₗ[ℝ] Q.W2h := Q.S1h.restrict (fun x _ => Q.S1h_mem x)
  have key := existsUnique_isMixedSolution dX0 dX1 dY0 dY1 S0' S1'
    (fun ψ => Subtype.ext (by simp [dX1, S0', S1', dY0, Q.anticomm_h]))
    (fun a b hab => Subtype.ext (dt0_injective H (by simpa [dY0, Subtype.ext_iff] using hab)))
    (fun u hu => by
      obtain ⟨χ, hχ, hχu⟩ := exact_bot_h H u.2 (by simpa [dY1, Subtype.ext_iff] using hu)
      exact ⟨⟨χ, hχ⟩, Subtype.ext (by simpa [dY0] using hχu)⟩)
    (fun μ hμ => by
      obtain ⟨ρ, hρ, hρμ⟩ := exact_top_h H μ.2 (by simpa [dX1, Subtype.ext_iff] using hμ)
      exact ⟨⟨ρ, hρ⟩, Subtype.ext (by simpa [dX0] using hρμ)⟩)
    (fun μ => by
      obtain ⟨τ, hτ, ψ, hψ, h⟩ := exists_sub_S0h_eq H h54 μ.2
      exact ⟨⟨τ, hτ⟩, ⟨ψ, hψ⟩, Subtype.ext (by simpa [dX0, S0'] using h)⟩)
    (F ∘ₗ Q.Vt1h.subtype)
  refine (existsUnique_congr fun x => ?_).1 key
  simp only [IsMixedSolution, Subtype.forall, Submodule.coe_inner, LinearMap.coe_restrict_apply,
    Submodule.coe_sub, LinearMap.comp_apply, Submodule.subtype_apply, dX0, dY0, dY1, S0', S1']

theorem gnSq_sub_le (x y : Vt1) : Q.gnSq (x - y) ≤ 2 * Q.gnSq x + 2 * Q.gnSq y := by
  unfold gnSq; simp only [map_sub]
  nlinarith [norm_sub_sq_le_two_mul x y, norm_sub_sq_le_two_mul (Q.S1h x) (Q.S1h y),
    norm_sub_sq_le_two_mul (D.dt1 x) (D.dt1 y)]

theorem gnSq_nonneg (x : Vt1) : 0 ≤ Q.gnSq x := by unfold gnSq; positivity

/-- The constant `1 + C_a`. -/
def Ca1 (Cp CS CP : ℝ) : ℝ := 1 + Ca Cp CS CP

/-- The constant `K` bounding the squared norms of the test functions of the error estimate. -/
def KL (Cp CR CS CP : ℝ) : ℝ := 8 * (1 + Cp ^ 2) * (1 + Cb Cp CR CS CP ^ 2)

/-- The constant of [QuennevilleBelair2015], Thm 5.5, in the `h`-independent constants only. -/
def errorConst (Cp CR CS CP Capp : ℝ) : ℝ :=
  2 + (2 * Ca1 Cp CS CP ^ 2 + 2 * Cp ^ 2 + 8 * Cb Cp CR CS CP ^ 2 + 8) *
    (36 * KL Cp CR CS CP * Ca1 Cp CS CP ^ 4) * (1 + Capp ^ 2)

theorem KL_ge (Cp CR CS CP : ℝ) : 8 * (1 + Cp ^ 2) ≤ KL Cp CR CS CP := by
  unfold KL
  nlinarith only [mul_nonneg (by positivity : (0:ℝ) ≤ 1 + Cp ^ 2) (sq_nonneg (Cb Cp CR CS CP))]

theorem KL_ge' (Cp CR CS CP : ℝ) : 8 * (1 + Cb Cp CR CS CP ^ 2) ≤ KL Cp CR CS CP := by
  unfold KL
  nlinarith only [mul_nonneg (by positivity : (0:ℝ) ≤ 1 + Cb Cp CR CS CP ^ 2) (sq_nonneg Cp)]

theorem KL_pos (Cp CR CS CP : ℝ) : 0 < KL Cp CR CS CP := by
  nlinarith only [KL_ge Cp CR CS CP, sq_nonneg Cp]

theorem errorEstimate_absorb {Cp Cb A K ε : ℝ} (hA : 1 ≤ A) (hε : ε = 1 / A ^ 2)
    (hK : 8 * (1 + Cp ^ 2) ≤ K) (hK' : 8 * (1 + Cb ^ 2) ≤ K)
    {a b c s t r pφ pχ o nτ ndψ nv gψ gv ip d1 d2 d3 d4 d5 d6 d7 d8 : ℝ}
    (hgψ0 : 0 ≤ gψ) (hgv0 : 0 ≤ gv)
    (hip : ip ≤ a * r) (hrc : r ^ 2 ≤ A ^ 2 * c ^ 2) (hpφ : pφ ^ 2 ≤ Cp ^ 2 * b ^ 2)
    (hpχ : pχ ^ 2 ≤ Cp ^ 2 * c ^ 2) (ho : o ^ 2 ≤ 2 * Cb ^ 2 * (s ^ 2 + t ^ 2))
    (hτ : nτ ^ 2 ≤ 2 * a ^ 2 + 2 * (ε ^ 2 * r ^ 2))
    (hdψ : ndψ ^ 2 ≤ 2 * b ^ 2 + 2 * (ε ^ 2 * c ^ 2))
    (hgψ : gψ ≤ 2 * pφ ^ 2 + 2 * (ε ^ 2 * pχ ^ 2) + ndψ ^ 2)
    (hv : nv ^ 2 ≤ 3 * (b ^ 2 + c ^ 2 + o ^ 2)) (hgv : gv = nv ^ 2 + t ^ 2)
    (hmain : a ^ 2 - ε * ip + ε * c ^ 2 + b ^ 2 + s ^ 2 + t ^ 2 ≤
      d1 * nτ + d2 * ndψ + d3 * √gψ + d4 * nv + d5 * √gv + d6 * s + d7 * s + d8 * t) :
    a ^ 2 + b ^ 2 + c ^ 2 + s ^ 2 + t ^ 2 ≤ 36 * K * A ^ 4 *
      (d1 ^ 2 + d2 ^ 2 + d3 ^ 2 + d4 ^ 2 + d5 ^ 2 + d6 ^ 2 + d7 ^ 2 + d8 ^ 2) := by
  set N := a ^ 2 + b ^ 2 + c ^ 2 + s ^ 2 + t ^ 2 with hN_def
  have hN0 : 0 ≤ N := by positivity
  have hA0 : 0 < A := by linarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεA : ε * A ^ 2 = 1 := by rw [hε]; field_simp
  have hε1 : ε ≤ 1 := by rw [hε, div_le_one (by positivity)]; nlinarith only [hA]
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith only [hε0, hε1]
  have hεc : ε ^ 2 * r ^ 2 ≤ ε * c ^ 2 := by
    calc ε ^ 2 * r ^ 2 ≤ ε ^ 2 * (A ^ 2 * c ^ 2) := by gcongr
      _ = (ε * A ^ 2) * ε * c ^ 2 := by ring
      _ = ε * c ^ 2 := by rw [hεA]; ring
  -- coercivity
  have hlow : ε / 2 * N ≤ a ^ 2 - ε * ip + ε * c ^ 2 + b ^ 2 + s ^ 2 + t ^ 2 := by
    have h2 : ε * (a * r) ≤ a ^ 2 / 2 + ε ^ 2 * r ^ 2 / 2 := by
      nlinarith only [sq_nonneg (a - ε * r)]
    have h3 := mul_le_mul_of_nonneg_left hip hε0.le
    have e1 := mul_le_mul_of_nonneg_right hε1 (sq_nonneg a)
    have e2 := mul_le_mul_of_nonneg_right hε1 (sq_nonneg b)
    have e3 := mul_le_mul_of_nonneg_right hε1 (sq_nonneg s)
    have e4 := mul_le_mul_of_nonneg_right hε1 (sq_nonneg t)
    rw [hN_def]
    nlinarith only [h2, h3, hεc, e1, e2, e3, e4]
  -- the test functions are controlled by `N`
  have hKN1 := mul_le_mul_of_nonneg_right hK hN0
  have hKN2 := mul_le_mul_of_nonneg_right hK' hN0
  have hCpN0 := mul_nonneg (sq_nonneg Cp) hN0
  have hCbN0 := mul_nonneg (sq_nonneg Cb) hN0
  have ha2 := sq_nonneg a; have hb2 := sq_nonneg b; have hc2 := sq_nonneg c
  have hs2 := sq_nonneg s; have ht2 := sq_nonneg t
  have hCpN : Cp ^ 2 * (b ^ 2 + c ^ 2) ≤ Cp ^ 2 * N :=
    mul_le_mul_of_nonneg_left (by rw [hN_def]; linarith only [ha2, hs2, ht2]) (sq_nonneg _)
  have hCbN : Cb ^ 2 * (s ^ 2 + t ^ 2) ≤ Cb ^ 2 * N :=
    mul_le_mul_of_nonneg_left (by rw [hN_def]; linarith only [ha2, hb2, hc2]) (sq_nonneg _)
  have hεc2 := mul_le_mul_of_nonneg_right hε2 hc2
  have hεc1 := mul_le_mul_of_nonneg_right hε1 hc2
  have L1 : nτ ^ 2 ≤ K * N := by
    rw [hN_def] at hKN1 hCpN0 ⊢
    nlinarith only [hτ, hεc, hεc1, hKN1, hCpN0, hb2, hs2, ht2]
  have L2' : ndψ ^ 2 ≤ 2 * b ^ 2 + 2 * c ^ 2 := by nlinarith only [hdψ, hεc2]
  have L2 : ndψ ^ 2 ≤ K * N := by
    rw [hN_def] at hKN1 hCpN0 ⊢
    nlinarith only [L2', hKN1, hCpN0, ha2, hs2, ht2]
  have L3 : √gψ ^ 2 ≤ K * N := by
    rw [Real.sq_sqrt hgψ0]
    have h2 := mul_le_mul_of_nonneg_left hpχ (sq_nonneg ε)
    have h3 : ε ^ 2 * (Cp ^ 2 * c ^ 2) ≤ Cp ^ 2 * c ^ 2 := by
      nlinarith only [hε2, mul_nonneg (sq_nonneg Cp) hc2]
    rw [hN_def] at hKN1 hCpN hCpN0 ⊢
    nlinarith only [hgψ, h2, h3, hpφ, L2', hKN1, hCpN, hCpN0, ha2, hs2, ht2]
  have hv2 : nv ^ 2 ≤ 3 * (b ^ 2 + c ^ 2) + 6 * (Cb ^ 2 * (s ^ 2 + t ^ 2)) := by
    nlinarith only [hv, ho]
  have L4 : nv ^ 2 ≤ K * N := by
    rw [hN_def] at hCbN hKN2 hCbN0 ⊢
    nlinarith only [hv2, hCbN, hKN2, hCbN0, ha2, hb2, hc2, hs2, ht2]
  have L5 : √gv ^ 2 ≤ K * N := by
    rw [Real.sq_sqrt hgv0, hgv]
    rw [hN_def] at hCbN hKN2 hCbN0 ⊢
    nlinarith only [hv2, hCbN, hKN2, hCbN0, ha2, hb2, hc2, hs2, ht2]
  have L6 : s ^ 2 ≤ K * N := by
    rw [hN_def] at hKN1 hCpN0 ⊢; nlinarith only [hKN1, hCpN0, ha2, hb2, hc2, ht2]
  have L8 : t ^ 2 ≤ K * N := by
    rw [hN_def] at hKN1 hCpN0 ⊢; nlinarith only [hKN1, hCpN0, ha2, hb2, hc2, hs2]
  have hK0 : 0 < K := by nlinarith only [hK, sq_nonneg Cp]
  have hκ : 0 < ε / 2 := by positivity
  have hsum : ε / 2 * N ≤ ∑ i : Fin 8, (![d1, d2, d3, d4, d5, d6, d7, d8] i) *
      (![nτ, ndψ, √gψ, nv, √gv, s, s, t] i) := by
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    linarith only [hlow, hmain]
  have hNb := Finset.univ.le_mul_sum_sq_of_mul_le_sum_mul _ _ hκ hK0 (fun i _ => by
    fin_cases i
    · exact L1
    · exact L2
    · exact L3
    · exact L4
    · exact L5
    · exact L6
    · exact L6
    · exact L8) hsum
  have hcard : ((Finset.univ : Finset (Fin 8)).card : ℝ) + 1 = 9 := by
    rw [Finset.card_univ, Fintype.card_fin]; norm_num
  rw [hcard] at hNb
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero] at hNb
  have hκ2 : 9 * K / (ε / 2) ^ 2 = 36 * K * A ^ 4 := by
    rw [hε]; field_simp; ring
  rw [hκ2] at hNb
  linarith only [hNb]

theorem errorEstimate_final {Cp Cb A K Capp h Λ : ℝ} (hK : 0 < K) (hA : 1 ≤ A)
    {a b c s t E1 E2 E3 G3 gσ gφ g1 g2 g3 pφ q o x1 x2 x4 x7 x8 S Su : ℝ}
    (hN : a ^ 2 + b ^ 2 + c ^ 2 + s ^ 2 + t ^ 2 ≤ 36 * K * A ^ 4 *
      (x1 ^ 2 + x2 ^ 2 + (Capp * h * Λ) ^ 2 + x4 ^ 2 + (Capp * h * S) ^ 2 + Su ^ 2 + x7 ^ 2
        + x8 ^ 2))
    (hE1 : E1 ≤ 2 * gσ + 2 * g1) (hE2 : E2 ≤ 2 * gφ + 2 * g2) (hE3 : E3 ≤ 2 * G3 + 2 * g3)
    (hgσ : gσ ≤ A ^ 2 * b ^ 2) (hgφ : gφ = pφ ^ 2 + b ^ 2) (hpφ : pφ ^ 2 ≤ Cp ^ 2 * b ^ 2)
    (hG3 : G3 = q ^ 2 + s ^ 2 + t ^ 2) (hq : q ^ 2 ≤ 2 * c ^ 2 + 2 * o ^ 2)
    (ho : o ^ 2 ≤ 2 * Cb ^ 2 * (s ^ 2 + t ^ 2))
    (hx1 : x1 ^ 2 ≤ g1) (hx4 : x4 ^ 2 ≤ g2) (hg3 : g3 = x2 ^ 2 + x7 ^ 2 + x8 ^ 2)
    (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) :
    E1 + E2 + E3 ≤ (2 + (2 * A ^ 2 + 2 * Cp ^ 2 + 8 * Cb ^ 2 + 8) *
      (36 * K * A ^ 4) * (1 + Capp ^ 2)) *
      (g1 + g2 + g3 + h ^ 2 * Λ ^ 2 + h ^ 2 * S ^ 2 + Su ^ 2) := by
  set Data := g1 + g2 + g3 + h ^ 2 * Λ ^ 2 + h ^ 2 * S ^ 2 + Su ^ 2 with hData
  set N := a ^ 2 + b ^ 2 + c ^ 2 + s ^ 2 + t ^ 2 with hN_def
  have hhΛ := mul_nonneg (sq_nonneg h) (sq_nonneg Λ)
  have hhS := mul_nonneg (sq_nonneg h) (sq_nonneg S)
  have hSu := sq_nonneg Su
  have hg3' : 0 ≤ g3 := by rw [hg3]; positivity
  have hData0 : 0 ≤ Data := by rw [hData]; positivity
  have hX : x1 ^ 2 + x2 ^ 2 + (Capp * h * Λ) ^ 2 + x4 ^ 2 + (Capp * h * S) ^ 2 + Su ^ 2
      + x7 ^ 2 + x8 ^ 2 ≤ (1 + Capp ^ 2) * Data := by
    have e4 := mul_nonneg (sq_nonneg Capp) (add_nonneg (add_nonneg hg1 hg2) hg3')
    have e5 := mul_nonneg (sq_nonneg Capp) hSu
    have hid : (1 + Capp ^ 2) * Data - (x1 ^ 2 + x2 ^ 2 + (Capp * h * Λ) ^ 2 + x4 ^ 2
        + (Capp * h * S) ^ 2 + Su ^ 2 + x7 ^ 2 + x8 ^ 2)
        = (g1 - x1 ^ 2) + (g2 - x4 ^ 2) + h ^ 2 * Λ ^ 2 + h ^ 2 * S ^ 2
          + Capp ^ 2 * (g1 + g2 + g3) + Capp ^ 2 * Su ^ 2 := by
      rw [hData, hg3]; ring
    linarith only [hid, hx1, hx4, e4, e5, hhΛ, hhS]
  have hN' : N ≤ 36 * K * A ^ 4 * ((1 + Capp ^ 2) * Data) :=
    hN.trans (mul_le_mul_of_nonneg_left hX (by positivity))
  have ha2 := sq_nonneg a; have hb2 := sq_nonneg b; have hc2 := sq_nonneg c
  have hs2 := sq_nonneg s; have ht2 := sq_nonneg t
  have hbN : b ^ 2 ≤ N := by rw [hN_def]; linarith only [ha2, hc2, hs2, ht2]
  have hstN : s ^ 2 + t ^ 2 ≤ N := by rw [hN_def]; linarith only [ha2, hb2, hc2]
  have hcN : c ^ 2 ≤ N := by rw [hN_def]; linarith only [ha2, hb2, hs2, ht2]
  have hA2 := mul_le_mul_of_nonneg_left hbN (sq_nonneg A)
  have hCp2 := mul_le_mul_of_nonneg_left hbN (sq_nonneg Cp)
  have hCb2 := mul_le_mul_of_nonneg_left hstN (sq_nonneg Cb)
  have hAb := mul_le_mul_of_nonneg_left hpφ (by norm_num : (0:ℝ) ≤ 2)
  have hErr : E1 + E2 + E3 ≤ 2 * Data + (2 * A ^ 2 + 2 * Cp ^ 2 + 8 * Cb ^ 2 + 8) * N := by
    have : 2 * gσ + 2 * gφ + 2 * G3 ≤ (2 * A ^ 2 + 2 * Cp ^ 2 + 8 * Cb ^ 2 + 8) * N := by
      rw [hgφ, hG3]
      nlinarith only [hgσ, hpφ, hq, ho, hA2, hCp2, hCb2, hbN, hstN, hcN, hb2, hs2, ht2]
    rw [hData]
    linarith only [this, hE1, hE2, hE3, hhΛ, hhS, hSu]
  have hK'0 : 0 ≤ 2 * A ^ 2 + 2 * Cp ^ 2 + 8 * Cb ^ 2 + 8 := by positivity
  have := mul_le_mul_of_nonneg_left hN' hK'0
  nlinarith only [this, hErr, hData0]

/-- The identity discretization `V_h = V`, all projections the identity. -/
def top (D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2) : Discrete D where
  V0h := ⊤
  V1h := ⊤
  W2h := ⊤
  Vt0h := ⊤
  Vt1h := ⊤
  Wt2h := ⊤
  d0_mem _ _ := Submodule.mem_top
  d1_mem _ _ := Submodule.mem_top
  dt0_mem _ _ := Submodule.mem_top
  dt1_mem _ _ := Submodule.mem_top
  P0 := LinearMap.id
  P1 := LinearMap.id
  P2 := LinearMap.id
  Pt0 := LinearMap.id
  Pt1 := LinearMap.id
  Pt2 := LinearMap.id
  P0_mem _ := Submodule.mem_top
  P1_mem _ := Submodule.mem_top
  P2_mem _ := Submodule.mem_top
  Pt0_mem _ := Submodule.mem_top
  Pt1_mem _ := Submodule.mem_top
  Pt2_mem _ := Submodule.mem_top
  P0_id _ _ := rfl
  P1_id _ _ := rfl
  P2_id _ _ := rfl
  Pt0_id _ _ := rfl
  Pt1_id _ _ := rfl
  Pt2_id _ _ := rfl
  comm0 _ := rfl
  comm1 _ := rfl
  commt0 _ := rfl
  commt1 _ := rfl

theorem top_bounded (D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2) : (top D).Bounded 1 where
  CP_nonneg := zero_le_one
  P1 x := by simp [top]
  P2 z := by simp [top]
  Pt1 v := by simp [top]

theorem top_compatible (D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2) : (top D).Compatible := fun _ => rfl

end Discrete

/-- A small BGG-type complex on `0` and `ℝ`, with `S₀ = id` and `S₁ = -id`. -/
def Discrete.exampleSegment : Segment ℝ (EuclideanSpace ℝ (Fin 0)) ℝ ℝ ℝ ℝ ℝ where
  d0 := 0
  d1 := LinearMap.id
  dt0 := LinearMap.id
  dt1 := 0
  S0 := LinearMap.id
  S1 := -LinearMap.id
  d1_d0 _ := by simp
  dt1_dt0 _ := by simp
  anticomm _ := by simp

/-- `Stability`, `Bounded` and `Compatible` hold together with `V_h¹`, `Ṽ_h⁰`, `Ṽ_h¹` nonzero,
`S₀ ≠ 0` and `S₁ ≠ 0`. -/
theorem Discrete.exists_nonvacuous :
    ∃ (D : Segment ℝ (EuclideanSpace ℝ (Fin 0)) ℝ ℝ ℝ ℝ ℝ) (Q : Discrete D),
      Stability D 1 1 1 ∧ Q.Bounded 1 ∧ Q.Compatible ∧ D.S1 ≠ 0 ∧ D.S0 ≠ 0 ∧
      Q.V1h ≠ ⊥ ∧ Q.Vt0h ≠ ⊥ ∧ Q.Vt1h ≠ ⊥ := by
  refine ⟨exampleSegment, Discrete.top _, ?_, Discrete.top_bounded _, Discrete.top_compatible _, ?_, ?_, ?_, ?_, ?_⟩
  · refine
      { Cp_nonneg := zero_le_one, CR_nonneg := zero_le_one, CS_nonneg := zero_le_one,
        poinc0 := fun σ => by simp [Subsingleton.elim σ 0],
        poinct0 := fun φ => by simp [exampleSegment],
        exact1 := fun μ hμ => ⟨0, by simpa [exampleSegment, eq_comm] using hμ⟩,
        hodget1 := fun v => ⟨v, 0, by simp [exampleSegment]⟩,
        reg := fun x => ⟨x, by simp [exampleSegment]⟩,
        boundS0 := fun ψ => by simp [exampleSegment, graphSq],
        boundS1 := fun v => by simp [exampleSegment, graphSq] }
  · intro h
    have := LinearMap.congr_fun h 1
    simp [exampleSegment] at this
  · intro h
    have := LinearMap.congr_fun h 1
    simp [exampleSegment] at this
  all_goals exact top_ne_bot

end Feec.BGG
