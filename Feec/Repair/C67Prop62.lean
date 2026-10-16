module

public import Feec.Ch6.TimeDependent

/-!
# Repair of thesis Prop 6.2: the dynamic-data form, and admissible projected initial data

[QuennevilleBelair2015, §6.2, Prop 6.2] claims: for initial data `(σ₀,ₕ, φ₀,ₕ) ∈ Γₕ` and
arbitrary `u₀,ₕ ∈ Ṽₕ¹`, `M₀,ₕ`, `ρ₀,ₕ`, the semi-discrete system (6.3) has a unique solution
("the system is square", so uniqueness implies existence).

Defect: (6.3) is a differential-algebraic system. It has a hidden constraint
`uₕ(t) ⊥ d(ker S₀,ₕ)` (`Feec.Ch6.Sol63.hidden_constraint`) and the algebraic variable `φₕ` is
not free (`Feec.Ch6.no_solution_of_incompatible`, `Feec.Ch6.no_solution_of_incompatible_phi`,
`Feec.Ch6.prop_6_2_false`). The corrected statement for the full 5-tuple of data is
`Feec.Ch6.prop_6_2`: a solution exists iff (C1) `dσ₀ = S₀,ₕφ₀`, (C2) `u₀ ⊥ d(ker S₀,ₕ)`,
(C3) `(dφ₀ − f(0), dψ) = 0` on `ker S₀,ₕ`.

Repair (this file).
* `sol63_phi_eq`, `sol63_phi_zero`: `φₕ(t) = Φ(σₕ(t), f(t))` on `[0,T)`, where
  `Φ = Feec.Ch6.phiMap` (the algebraic variable is a fixed linear function of `σₕ` and `f`).
  So (C1) and (C3) carry no information about the dynamic data.
* `prop_6_2_dynamic`, `prop_6_2_wellposed`: the thesis-shaped statement. For dynamic data
  `(σ₀, u₀, M₀, ρ₀)`, (6.3) has a solution iff (C2) holds; it is then unique (dynamic
  variables and `λₕ` on `[0,T]`, `φₕ` on `[0,T)`) and `φₕ(0) = Φ(σ₀, f(0))`. (C2) is the only
  compatibility condition; `σ₀`, `M₀`, `ρ₀` are free.
* `projected_C2`: under the hypotheses of `Feec.Ch6.ch6_convergence_Sol63`, the dynamic part of
  the elliptic projection `Pξ(0)` of the exact solution satisfies (C2) (test (6.4) with
  `η = (0, ψ)`, `ψ ∈ ker S₀,ₕ`).
* `projected_C3_iff`: the projected algebraic datum `Q(0)` satisfies (C3) iff
  `(ξ̇(0), ι(0, dψ, 0, 0)) = 0` for all `ψ ∈ ker S₀,ₕ`, a consistency condition on the exact
  solution; so `Q(0)` is in general not an admissible `φₕ(0)`, and the right choice is
  `Φ(σₕ(0), f(0))`. (We do not exhibit a concrete instance where the condition fails.)
* `ch6_convergence_projected`: the convergence theorem without a solution as hypothesis. With
  `ξₕ(0) = Pξ(0)` (dynamic part) and `φₕ(0) = Φ(σₕ(0), f(0))`, a solution of (6.3) exists, and
  `‖ξ(t) − ξₕ(t)‖ ≤ ‖(I − P)ξ(t)‖ + ∫₀ᵗ ‖(P − I)ξ̇‖` (the initial error term vanishes).

Open hypotheses (out of scope here, as in `Feec.Ch6.TimeDependent`): the finite element spaces
of §6.3 / (6.5) are not formalized, so that `S₀,ₕ = Π¹ₕ I` is surjective (thesis (5.4)) and that
`grad` is injective on `P₂Λ⁰ ⊗ V` enter as the hypotheses `hS`, `hdinj`; the elliptic
projection (6.4) enters as the hypotheses `hproj`, `hPmem`, `hPB` (its well-posedness is open).
-/

open scoped RealInnerProductSpace
open Set Feec.Ch6

@[expose] public section

namespace Feec.Repair.C67

section Discrete

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  {D : Feec.BGGData P0 P1 P2 Pt0 Pt1 Pt2}

/-- `S₁,ₕ dψ = 0` for `ψ ∈ ker S₀,ₕ` (anticommutation `d S₀,ₕ = −S₁,ₕ d`). -/
lemma S1_dt0_of_ker {ψ : Pt0} (hψ : D.S0 ψ = 0) : D.S1 (D.dt0 ψ) = 0 := by
  have := D.anticomm ψ; rw [hψ, map_zero] at this; exact neg_eq_zero.mp this.symm

/-- (C3) at every time: every solution of (6.3) has `(dφₕ(t) − f(t), dψ) = 0` for
`ψ ∈ ker S₀,ₕ` and `t ∈ [0,T)` (differentiate the hidden constraint and test (6.3b) with
`v = dψ`). Thesis Prop 6.2, corrected: `φₕ` is not free. -/
theorem sol63_C3 {T : ℝ} {f : ℝ → Pt1} (s : Sol63 D T f) {t : ℝ} (ht : t ∈ Ico 0 T)
    {ψ : Pt0} (hψ : D.S0 ψ = 0) : ⟪D.dt0 (s.φ t), D.dt0 ψ⟫ = ⟪f t, D.dt0 ψ⟫ := by
  have hz : ∀ x ∈ Icc 0 T, ⟪s.u x, D.dt0 ψ⟫ = 0 := fun x hx => s.hidden_constraint hx hψ
  have hd : HasDerivWithinAt (fun x => ⟪s.u x, D.dt0 ψ⟫) ⟪s.u' t, D.dt0 ψ⟫ (Ici t) t := by
    simpa using HasDerivWithinAt.inner ℝ (s.du t ht)
      (hasDerivWithinAt_const t (Ici t) (D.dt0 ψ))
  have hu' := hasDerivWithinAt_Ici_eq_zero ht hz hd
  have hb := s.eb t ht (D.dt0 ψ)
  rw [hu', S1_dt0_of_ker hψ, D.dt1_dt0] at hb
  simpa using hb

/-- **Prop 6.2 repair: `φₕ` is determined.** For every solution of (6.3) and `t ∈ [0,T)`,
`φₕ(t) = Φ(σₕ(t), f(t))` with `Φ = phiMap`, the unique `φ` with `S₀,ₕ φ = dσ` and
`(dφ, dψ) = (f, dψ)` on `ker S₀,ₕ`. Corrects [QuennevilleBelair2015, Prop 6.2]
(`φ₀,ₕ` is not free data). -/
theorem sol63_phi_eq [FiniteDimensional ℝ P1] [FiniteDimensional ℝ Pt0] [FiniteDimensional ℝ Pt1]
    (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)
    {T : ℝ} {f : ℝ → Pt1} (s : Sol63 D T f) {t : ℝ} (ht : t ∈ Ico 0 T) :
    s.φ t = phiMap D hdinj hS (s.σ t, f t) :=
  (phiMap_eq hdinj hS (s.constraint (Ico_subset_Icc_self ht))
    fun _ hψ => sol63_C3 s ht hψ).symm

/-- The initial algebraic datum is determined: `φₕ(0) = Φ(σₕ(0), f(0))` (for `T > 0`).
Corrects [QuennevilleBelair2015, Prop 6.2]. -/
theorem sol63_phi_zero [FiniteDimensional ℝ P1] [FiniteDimensional ℝ Pt0]
    [FiniteDimensional ℝ Pt1] (hdinj : Function.Injective D.dt0)
    (hS : Function.Surjective D.S0) {T : ℝ} (hT : 0 < T) {f : ℝ → Pt1} (s : Sol63 D T f) :
    s.φ 0 = phiMap D hdinj hS (s.σ 0, f 0) :=
  sol63_phi_eq hdinj hS s ⟨le_rfl, hT⟩

variable [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P1] [FiniteDimensional ℝ P2]
  [FiniteDimensional ℝ Pt0] [FiniteDimensional ℝ Pt1] [FiniteDimensional ℝ Pt2]

/-- **Corrected Prop 6.2, dynamic-data form (existence ⇔ (C2)).** Assume `T > 0`,
finite-dimensional FE spaces, `d : Ṽₕ⁰ → Ṽₕ¹` injective, `S₀,ₕ` surjective (thesis (5.4)) and
`f` continuous. For dynamic data `(σ₀, u₀, M₀, ρ₀)` the system (6.3) has a solution iff
`u₀ ⊥ d(ker S₀,ₕ)`. `σ₀`, `M₀`, `ρ₀` are arbitrary.

Thesis claim: data in `Γₕ` and arbitrary `u₀,ₕ` give a solution. Defect: (C2) on `u₀` is
necessary (`no_solution_of_incompatible`), and `φ₀,ₕ` is not free (`sol63_phi_zero`).
Repair: once `φₕ(0) := Φ(σ₀, f(0))` (forced), (C1) and (C3) hold automatically
(`S0_phiMap`, `inner_phiMap`) and (C2) is the only condition. Corrects
[QuennevilleBelair2015, Prop 6.2]. -/
theorem prop_6_2_dynamic {T : ℝ} (hT : 0 < T) (hdinj : Function.Injective D.dt0)
    (hS : Function.Surjective D.S0) {f : ℝ → Pt1} (hf : Continuous f) (σ₀ : P0) (u₀ : Pt1)
    (M₀ : P2) (ρ₀ : Pt2) :
    (∃ s : Sol63 D T f, s.σ 0 = σ₀ ∧ s.u 0 = u₀ ∧ s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ↔
      ∀ ψ, D.S0 ψ = 0 → ⟪u₀, D.dt0 ψ⟫ = 0 := by
  constructor
  · rintro ⟨s, -, hu, -, -⟩ ψ hψ
    rw [← hu]; exact (prop_6_2_necessary hT s).2.1 ψ hψ
  · intro h2
    obtain ⟨s, hσ, -, hu, hM, hρ⟩ := prop_6_2_exists (M₀ := M₀) (ρ₀ := ρ₀) hdinj hS hf T
      (S0_phiMap hdinj hS (σ₀, f 0)).symm h2
      (fun ψ hψ => inner_phiMap hdinj hS (σ₀, f 0) hψ)
    exact ⟨s, hσ, hu, hM, hρ⟩

/-- **Corrected Prop 6.2, well-posedness for dynamic data.** Under the hypotheses of
`prop_6_2_dynamic` and (C2) `u₀ ⊥ d(ker S₀,ₕ)`: there is a solution of (6.3) with data
`(σ₀, u₀, M₀, ρ₀)`, its algebraic datum is `φₕ(0) = Φ(σ₀, f(0))`, and every solution with the
same dynamic data agrees with it (`σₕ, uₕ, Mₕ, ρₕ, λₕ` on `[0,T]`, `φₕ` on `[0,T)`; the value
`φₕ(T)` is not constrained by (6.3)). This is the thesis' Prop 6.2 with the free datum
`φ₀,ₕ` replaced by the forced one and "arbitrary `u₀,ₕ`" replaced by (C2). Corrects
[QuennevilleBelair2015, Prop 6.2]. -/
theorem prop_6_2_wellposed {T : ℝ} (hT : 0 < T) (hdinj : Function.Injective D.dt0)
    (hS : Function.Surjective D.S0) {f : ℝ → Pt1} (hf : Continuous f) (σ₀ : P0) (u₀ : Pt1)
    (M₀ : P2) (ρ₀ : Pt2) (hC2 : ∀ ψ, D.S0 ψ = 0 → ⟪u₀, D.dt0 ψ⟫ = 0) :
    ∃ s : Sol63 D T f, (s.σ 0 = σ₀ ∧ s.u 0 = u₀ ∧ s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ∧
      s.φ 0 = phiMap D hdinj hS (σ₀, f 0) ∧
      ∀ s' : Sol63 D T f, (s'.σ 0 = σ₀ ∧ s'.u 0 = u₀ ∧ s'.M 0 = M₀ ∧ s'.ρ 0 = ρ₀) →
        (∀ t ∈ Icc 0 T, s'.σ t = s.σ t ∧ s'.u t = s.u t ∧ s'.M t = s.M t ∧ s'.ρ t = s.ρ t ∧
          s'.lam t = s.lam t) ∧ (∀ t ∈ Ico 0 T, s'.φ t = s.φ t) := by
  obtain ⟨s, hσ, hu, hM, hρ⟩ := (prop_6_2_dynamic hT hdinj hS hf σ₀ u₀ M₀ ρ₀).2 hC2
  refine ⟨s, ⟨hσ, hu, hM, hρ⟩, by rw [sol63_phi_zero hdinj hS hT s, hσ], fun s' h' => ?_⟩
  exact Sol63.unique s' s hdinj hS
    ⟨h'.1.trans hσ.symm, h'.2.1.trans hu.symm, h'.2.2.1.trans hM.symm, h'.2.2.2.trans hρ.symm⟩

end Discrete

/-! ### Projected initial data for the Ch. 6 convergence theorem -/

section Projected

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [AddCommGroup Z] [Module ℝ Z]

/-- **The projected dynamic datum satisfies (C2).** In the setting of
`Feec.Ch6.ch6_convergence_Sol63` (continuous equation `hcont` tested on `Xh = range (ι × j)`,
elliptic projection `hproj`, discrete forms `hAh`, `hBh`) and `T > 0`: if
`(ι a, j q) = (Pξ(0), Q(0))`, then the `u`-component of `a` is orthogonal to `d(ker S₀,ₕ)`.
Proof: test with `η = (ι 0, j ψ)`, `ψ ∈ ker S₀,ₕ`; then `Bh η = −S₀,ₕψ = 0` and
`Ah((ι a, j q), η) = −(a_u, dψ)`, while `hcont` makes the right side of `hproj` vanish.
Supplies the compatibility condition missing from [QuennevilleBelair2015, §6.2] for the
natural initial data. -/
theorem projected_C2 {D : Feec.BGGData P0 P1 P2 Pt0 Pt1 Pt2}
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X) (j : Pt0 →ₗ[ℝ] Z)
    (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] P1)
    (hAh : ∀ a φ b ψ, Ah (ι a, j φ) (ι b, j ψ) = a63 D (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (ι a, j ψ) = D.d0 a.1 - D.S0 ψ) (P : X →L[ℝ] X) {T : ℝ} (hT : 0 < T)
    (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    (Q : ℝ → Z) (lamP : ℝ → P1)
    (hproj : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      Ah (P (ξ t), Q t) η - ⟪lamP t, Bh η⟫ = A (ξ t, χ t) η - ℓ t η)
    {a : P0 × Pt1 × P2 × Pt2} {q : Pt0} (ha : (ι a, j q) = (P (ξ 0), Q 0))
    {ψ : Pt0} (hψ : D.S0 ψ = 0) : ⟪a.2.1, D.dt0 ψ⟫ = 0 := by
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hη : ((ι 0, j ψ) : X × Z) ∈ LinearMap.range
      ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j) := ⟨(0, ψ), rfl⟩
  have h1 := hcont 0 h0 _ hη
  have h2 := hproj 0 h0 _ hη
  rw [← ha, hAh, hBh, hψ] at h2
  simp only [map_zero, inner_zero_right, zero_add] at h1
  simp [a63] at h2
  linarith

/-- **When is the projected algebraic datum admissible?** In the setting of `projected_C2`,
with `f(t)` representing `F(t)` on `ι(Ṽₕ¹)` (`hF`): if `(ι a, j q) = (Pξ(0), Q(0))`, then `q`
satisfies (C3) `(dq, dψ) = (f(0), dψ)` on `ker S₀,ₕ` iff `(ξ̇(0), ι(0, dψ, 0, 0)) = 0` for all
`ψ ∈ ker S₀,ₕ`. Proof: test with `η = (ι(0, dψ, 0, 0), 0)`, using `S₁,ₕ dψ = 0`, `d dψ = 0`.
So `φₕ(0) = Q(0)` is admissible only under a consistency condition on the exact solution
(a component of `(I − P)u̇(0)` in general); the admissible choice is `Φ(σₕ(0), f(0))`
(`ch6_convergence_projected`). Not shown here: a concrete instance where the condition fails.
Repair of [QuennevilleBelair2015, §6.2] (initial data for (6.3)). -/
theorem projected_C3_iff {D : Feec.BGGData P0 P1 P2 Pt0 Pt1 Pt2}
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X) (j : Pt0 →ₗ[ℝ] Z)
    (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] P1)
    (hAh : ∀ a φ b ψ, Ah (ι a, j φ) (ι b, j ψ) = a63 D (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (ι a, j ψ) = D.d0 a.1 - D.S0 ψ) (P : X →L[ℝ] X) {T : ℝ} (hT : 0 < T)
    {f : ℝ → Pt1} (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hF : ∀ t ∈ Ico 0 T, ∀ a, ⟪F t, ι a⟫ = ⟪f t, a.2.1⟫)
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    (Q : ℝ → Z) (lamP : ℝ → P1)
    (hproj : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      Ah (P (ξ t), Q t) η - ⟪lamP t, Bh η⟫ = A (ξ t, χ t) η - ℓ t η)
    {a : P0 × Pt1 × P2 × Pt2} {q : Pt0} (ha : (ι a, j q) = (P (ξ 0), Q 0)) :
    (∀ ψ, D.S0 ψ = 0 → ⟪D.dt0 q, D.dt0 ψ⟫ = ⟪f 0, D.dt0 ψ⟫) ↔
      ∀ ψ, D.S0 ψ = 0 → ⟪ξ' 0, ι (0, D.dt0 ψ, 0, 0)⟫ = 0 := by
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have key : ∀ ψ, D.S0 ψ = 0 →
      ⟪D.dt0 q, D.dt0 ψ⟫ = ⟪f 0, D.dt0 ψ⟫ - ⟪ξ' 0, ι (0, D.dt0 ψ, 0, 0)⟫ := by
    intro ψ hψ
    have hη : ((ι (0, D.dt0 ψ, 0, 0), j 0) : X × Z) ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j) := ⟨((0, D.dt0 ψ, 0, 0), 0), rfl⟩
    have h1 := hcont 0 h0 _ hη
    have h2 := hproj 0 h0 _ hη
    rw [← ha, hAh, hBh] at h2
    rw [hF 0 h0] at h1
    simp [a63, S1_dt0_of_ker hψ, D.dt1_dt0] at h2
    simp only [map_zero] at h1
    linarith
  constructor
  · intro h ψ hψ; have := key ψ hψ; rw [h ψ hψ] at this; linarith
  · intro h ψ hψ; rw [key ψ hψ, h ψ hψ, sub_zero]

/-- **Ch. 6 convergence from projected initial data (no solution assumed).** Hypotheses of
`Feec.Ch6.ch6_convergence_Sol63` without the discrete solution `s`, plus `T > 0`, `f`
continuous, finite-dimensional FE spaces, `d` injective on `Ṽₕ⁰` and `S₀,ₕ` surjective. Then
there is a solution `s` of (6.3) whose dynamic initial datum is the projection `Pξ(0)` and whose
algebraic datum is the forced `φₕ(0) = Φ(σₕ(0), f(0))`, and for `t ∈ [0,T]`
`‖ξ(t) − ξₕ(t)‖ ≤ ‖ξ(t) − Pξ(t)‖ + ∫₀ᵗ ‖Pξ̇ − ξ̇‖`.

The thesis (§6.2–6.3) states no convergence theorem and does not address whether natural
initial data are admissible for (6.3); this closes that gap for the projected data
(`projected_C2`), avoiding the generally inadmissible `φₕ(0) = Q(0)` (`projected_C3_iff`).
See [QuennevilleBelair2015, §6.2, Prop 6.2, (6.4)]; cf. [QuennevilleBelair2015, Thm 4.14]. -/
theorem ch6_convergence_projected [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P1]
    [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt0] [FiniteDimensional ℝ Pt1]
    [FiniteDimensional ℝ Pt2] {D : Feec.BGGData P0 P1 P2 Pt0 Pt1 Pt2}
    (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X)
    (hι : ∀ a b, ⟪ι a, ι b⟫ = ⟪a.1, b.1⟫ + ⟪a.2.1, b.2.1⟫ + ⟪a.2.2.1, b.2.2.1⟫ +
      ⟪a.2.2.2, b.2.2.2⟫)
    (j : Pt0 →ₗ[ℝ] Z) (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] P1)
    (hAh : ∀ a φ b ψ, Ah (ι a, j φ) (ι b, j ψ) = a63 D (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (ι a, j ψ) = D.d0 a.1 - D.S0 ψ) (P : X →L[ℝ] X) {T : ℝ} (hT : 0 < T)
    {f : ℝ → Pt1} (hf : Continuous f)
    (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hF : ∀ t ∈ Ico 0 T, ∀ a, ⟪F t, ι a⟫ = ⟪f t, a.2.1⟫)
    (hξc : ContinuousOn ξ (Icc 0 T)) (hξ'c : ContinuousOn ξ' (Icc 0 T))
    (hξd : ∀ t ∈ Ico 0 T, HasDerivWithinAt ξ (ξ' t) (Ici t) t)
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    (Q : ℝ → Z) (lamP : ℝ → P1)
    (hPmem : ∀ t ∈ Icc 0 T, (P (ξ t), Q t) ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j))
    (hPB : ∀ t ∈ Icc 0 T, Bh (P (ξ t), Q t) = 0)
    (hproj : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      Ah (P (ξ t), Q t) η - ⟪lamP t, Bh η⟫ = A (ξ t, χ t) η - ℓ t η) :
    ∃ s : Sol63 D T f, ι (s.σ 0, s.u 0, s.M 0, s.ρ 0) = P (ξ 0) ∧
      s.φ 0 = phiMap D hdinj hS (s.σ 0, f 0) ∧
      ∀ t ∈ Icc 0 T, ‖ξ t - ι (s.σ t, s.u t, s.M t, s.ρ t)‖ ≤
        ‖ξ t - P (ξ t)‖ + ∫ r in (0:ℝ)..t, ‖P (ξ' r) - ξ' r‖ := by
  obtain ⟨⟨a, q⟩, hy⟩ := hPmem 0 ⟨le_rfl, hT.le⟩
  have ha : (ι a, j q) = (P (ξ 0), Q 0) := hy
  have hC2 : ∀ ψ, D.S0 ψ = 0 → ⟪a.2.1, D.dt0 ψ⟫ = 0 := fun ψ hψ =>
    projected_C2 ι j A Ah Bh hAh hBh P hT ξ ξ' χ ℓ F hcont Q lamP hproj ha hψ
  obtain ⟨s, hσ, hu, hM, hρ⟩ :=
    (prop_6_2_dynamic hT hdinj hS hf a.1 a.2.1 a.2.2.1 a.2.2.2).2 hC2
  have hinit : ι (s.σ 0, s.u 0, s.M 0, s.ρ 0) = P (ξ 0) := by
    rw [hσ, hu, hM, hρ]; exact congrArg Prod.fst ha
  refine ⟨s, hinit, sol63_phi_zero hdinj hS hT s, fun t ht => ?_⟩
  have := ch6_convergence_Sol63 ι hι j A Ah Bh hAh hBh P s ξ ξ' χ ℓ F hF hξc hξ'c hξd hcont
    Q lamP hPmem hPB hproj t ht
  rwa [hinit, sub_self, norm_zero, add_zero] at this

end Projected

end Feec.Repair.C67
