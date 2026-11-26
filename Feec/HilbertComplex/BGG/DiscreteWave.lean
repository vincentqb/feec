module

public import Feec.HilbertComplex.BGG.EllipticProjection

/-!
# Convergence of the semi-discrete BGG wave system (6.3) through the elliptic projection (6.4)

Convergence of the semi-discrete system (6.3) of [QuennevilleBelair2015], §6.2 through an elliptic
projection with the `L²` term, as in (6.4); for the projection of (6.4) all projection hypotheses
are proved, and for a discretization the convergence is `O(h)`.

## Main results

* `Feec.BGG.norm_sub_le_of_ellipticProjection_L2`: the energy estimate.
* `Feec.BGG.Discrete.exists_discreteSolution_norm_sub_le_rate`: `O(h)` convergence of (6.3).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2, Thm 4.14

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped RealInnerProductSpace
open Set

@[expose] public noncomputable section

namespace Feec.BGG

/-! ## The abstract energy estimate with the `L²` term -/

/-- For a projected trajectory `p` satisfying the shifted projection equation on `Xₕ`,
`‖ξ(t) − ξₕ(t)‖ ≤ ‖ξ(t) − p(t)‖ + ‖p(0) − ξₕ(0)‖ + ∫₀ᵗ (‖p' − ξ'‖ + ‖p − ξ‖)`. -/
theorem norm_sub_le_of_ellipticProjection_L2 {X Z Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X]
    [AddCommGroup Z] [Module ℝ Z] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (Xh : Submodule ℝ (X × Z)) (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ)
    (Bh : (X × Z) →ₗ[ℝ] Y) {T : ℝ}
    -- continuous solution
    (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hξc : ContinuousOn ξ (Icc 0 T)) (hξ'c : ContinuousOn ξ' (Icc 0 T))
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ Xh, ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    -- discrete solution
    (ξh ξh' : ℝ → X) (χh : ℝ → Z) (lamh : ℝ → Y)
    (hmem : ∀ t ∈ Icc 0 T, (ξh t, χh t) ∈ Xh) (hBh : ∀ t ∈ Icc 0 T, Bh (ξh t, χh t) = 0)
    (hξhc : ContinuousOn ξh (Icc 0 T))
    (hξhd : ∀ t ∈ Ico 0 T, HasDerivWithinAt ξh (ξh' t) (Ici t) t)
    (hdisc : ∀ t ∈ Ico 0 T, ∀ η ∈ Xh,
      ⟪ξh' t, η.1⟫ + Ah (ξh t, χh t) η - ⟪lamh t, Bh η⟫ = ⟪F t, η.1⟫)
    -- projection
    (p p' : ℝ → X) (Q : ℝ → Z) (lamP : ℝ → Y)
    (hpc : ContinuousOn p (Icc 0 T)) (hp'c : ContinuousOn p' (Icc 0 T))
    (hpd : ∀ t ∈ Ico 0 T, HasDerivWithinAt p (p' t) (Ici t) t)
    (hPmem : ∀ t ∈ Icc 0 T, (p t, Q t) ∈ Xh) (hPB : ∀ t ∈ Icc 0 T, Bh (p t, Q t) = 0)
    (hproj : ∀ t ∈ Ico 0 T, ∀ η ∈ Xh,
      ⟪p t, η.1⟫ + Ah (p t, Q t) η - ⟪lamP t, Bh η⟫ = ⟪ξ t, η.1⟫ + A (ξ t, χ t) η - ℓ t η)
    (hskew : ∀ η ∈ Xh, Ah η η = 0) :
    ∀ t ∈ Icc 0 T, ‖ξ t - ξh t‖ ≤ ‖ξ t - p t‖ + ‖p 0 - ξh 0‖ +
      ∫ s in (0:ℝ)..t, (‖p' s - ξ' s‖ + ‖p s - ξ s‖) := by
  set e : ℝ → X := fun t => p t - ξh t
  set e' : ℝ → X := fun t => p' t - ξh' t
  have hE : ∀ t ∈ Icc 0 T, (e t, Q t - χh t) ∈ Xh := fun t ht => by
    have := Xh.sub_mem (hPmem t ht) (hmem t ht); simpa [e] using this
  have hEB : ∀ t ∈ Icc 0 T, Bh (e t, Q t - χh t) = 0 := fun t ht => by
    have : ((e t, Q t - χh t) : X × Z) = (p t, Q t) - (ξh t, χh t) := by simp [e]
    rw [this, map_sub, hPB t ht, hBh t ht, sub_zero]
  have herr : ∀ t ∈ Ico 0 T, ⟪e' t, e t⟫ = ⟪p' t - ξ' t, e t⟫ - ⟪p t - ξ t, e t⟫ := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    set η : X × Z := (e t, Q t - χh t)
    have h1 := hcont t ht η (hE t ht')
    have h2 := hdisc t ht η (hE t ht')
    have h3 := hproj t ht η (hE t ht')
    have h4 := hskew η (hE t ht')
    have hsplit : η = (p t, Q t) - (ξh t, χh t) := by simp [η, e]
    rw [hEB t ht', inner_zero_right, sub_zero] at h2
    rw [hEB t ht', inner_zero_right, sub_zero] at h3
    have h5 : Ah η η = Ah (p t, Q t) η - Ah (ξh t, χh t) η := by
      have : Ah η = Ah (p t, Q t) - Ah (ξh t, χh t) := by rw [hsplit, map_sub]
      rw [this, LinearMap.sub_apply]
    simp only [e', inner_sub_left]
    simp only [η] at h1 h2 h3 h4 h5 ⊢
    linarith
  have hgc : ContinuousOn (fun s => ‖p' s - ξ' s‖ + ‖p s - ξ s‖) (Icc 0 T) :=
    (hp'c.sub hξ'c).norm.add (hpc.sub hξc).norm
  exact Variational.norm_sub_le_of_projected_error (𝕜 := ℝ) (u := ξ) (p := p)
    (uh := ξh) (ε' := e') (hpc.sub hξhc) (fun t ht => (hpd t ht).sub (hξhd t ht)) hgc
    (fun _ _ => by positivity)
    fun t ht => by
      rw [RCLike.re_to_real, herr t ht]
      have a1 := real_inner_le_norm (p' t - ξ' t) (e t)
      have a2 : -⟪p t - ξ t, e t⟫ ≤ ‖p t - ξ t‖ * ‖e t‖ :=
        (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
      change _ ≤ (‖p' t - ξ' t‖ + ‖p t - ξ t‖) * ‖e t‖
      linarith

theorem norm_sub_le_mul_of_ellipticProjection_L2 {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X]
    {ξ ξ' ξh p p' : ℝ → X} {T ε : ℝ} (hξc : ContinuousOn ξ (Icc 0 T))
    (hξ'c : ContinuousOn ξ' (Icc 0 T)) (hpc : ContinuousOn p (Icc 0 T))
    (hp'c : ContinuousOn p' (Icc 0 T))
    (hconv : ∀ t ∈ Icc 0 T, ‖ξ t - ξh t‖ ≤ ‖ξ t - p t‖ + ‖p 0 - ξh 0‖ +
      ∫ s in (0:ℝ)..t, (‖p' s - ξ' s‖ + ‖p s - ξ s‖))
    (h1 : ∀ t ∈ Icc 0 T, ‖ξ t - p t‖ ≤ ε) (h2 : ‖p 0 - ξh 0‖ ≤ ε)
    (h3 : ∀ t ∈ Icc 0 T, ‖p' t - ξ' t‖ ≤ ε) :
    ∀ t ∈ Icc 0 T, ‖ξ t - ξh t‖ ≤ ε * (2 + 2 * t) := by
  intro t ht
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hint : ∫ s in (0:ℝ)..t, (‖p' s - ξ' s‖ + ‖p s - ξ s‖) ≤ ∫ s in (0:ℝ)..t, 2 * ε := by
    refine intervalIntegral.integral_mono_on ht.1 ?_ intervalIntegrable_const fun s hs => ?_
    · exact (((hp'c.sub hξ'c).norm.add (hpc.sub hξc).norm).mono hsub).intervalIntegrable_of_Icc
        ht.1
    · have := h1 s (hsub hs); rw [norm_sub_rev] at this
      linarith [h3 s (hsub hs)]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
  have := hconv t ht
  nlinarith [h1 t ht]

/-! ## The discrete side from a solution of (6.3) -/

section Bridge

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [AddCommGroup Z] [Module ℝ Z]

/-- The energy estimate through an elliptic projection with `L²` term, for a solution of (6.3). -/
theorem DiscreteSolution.norm_sub_le_of_ellipticProjection_L2
    {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X)
    (hι : ∀ a b, ⟪ι a, ι b⟫ = ⟪a.1, b.1⟫ + ⟪a.2.1, b.2.1⟫ + ⟪a.2.2.1, b.2.2.1⟫ +
      ⟪a.2.2.2, b.2.2.2⟫)
    (j : Pt0 →ₗ[ℝ] Z) (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] P1)
    (hAh : ∀ a φ b ψ, Ah (ι a, j φ) (ι b, j ψ) = discreteSkewForm D (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (ι a, j ψ) = D.d0 a.1 - D.S0 ψ) {T : ℝ}
    {f : ℝ → Pt1} (s : DiscreteSolution D T f)
    (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hF : ∀ t ∈ Ico 0 T, ∀ a, ⟪F t, ι a⟫ = ⟪f t, a.2.1⟫)
    (hξc : ContinuousOn ξ (Icc 0 T)) (hξ'c : ContinuousOn ξ' (Icc 0 T))
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    (p p' : ℝ → X) (Q : ℝ → Z) (lamP : ℝ → P1)
    (hpc : ContinuousOn p (Icc 0 T)) (hp'c : ContinuousOn p' (Icc 0 T))
    (hpd : ∀ t ∈ Ico 0 T, HasDerivWithinAt p (p' t) (Ici t) t)
    (hPmem : ∀ t ∈ Icc 0 T, (p t, Q t) ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j))
    (hPB : ∀ t ∈ Icc 0 T, Bh (p t, Q t) = 0)
    (hproj : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪p t, η.1⟫ + Ah (p t, Q t) η - ⟪lamP t, Bh η⟫ = ⟪ξ t, η.1⟫ + A (ξ t, χ t) η - ℓ t η) :
    ∀ t ∈ Icc 0 T, ‖ξ t - ι (s.σ t, s.u t, s.M t, s.ρ t)‖ ≤
      ‖ξ t - p t‖ + ‖p 0 - ι (s.σ 0, s.u 0, s.M 0, s.ρ 0)‖ +
        ∫ r in (0:ℝ)..t, (‖p' r - ξ' r‖ + ‖p r - ξ r‖) := by
  set Xh := LinearMap.range ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j)
  have hrange : ∀ η ∈ Xh, ∃ b ψ, η = (ι b, j ψ) := by
    rintro η ⟨⟨b, ψ⟩, rfl⟩; exact ⟨b, ψ, rfl⟩
  refine Feec.BGG.norm_sub_le_of_ellipticProjection_L2 Xh A Ah Bh ξ ξ' χ ℓ F hξc hξ'c hcont
    (fun t => ι (s.σ t, s.u t, s.M t, s.ρ t)) (fun t => ι (s.σ' t, s.u' t, s.M' t, s.ρ' t))
    (fun t => j (s.φ t)) s.lam (fun t _ => ⟨((s.σ t, s.u t, s.M t, s.ρ t), s.φ t), rfl⟩)
    (fun t ht => by simp only [hBh]; exact sub_eq_zero.mpr (s.constraint ht))
    (ι.continuous.comp_continuousOn (s.cσ.prodMk (s.cu.prodMk (s.cM.prodMk s.cρ))))
    (fun t ht => ι.hasFDerivAt.comp_hasDerivWithinAt t
      ((s.dσ t ht).prodMk ((s.du t ht).prodMk ((s.dM t ht).prodMk (s.dρ t ht)))))
    (fun t ht η hη => ?_) p p' Q lamP hpc hp'c hpd hPmem hPB hproj (fun η hη => ?_)
  · obtain ⟨⟨τ, v, N, μ⟩, ψ, rfl⟩ := hrange η hη
    simp only [hι, hAh, hBh, hF t ht, discreteSkewForm]
    have ha := s.ea t (Ico_subset_Icc_self ht) τ ψ
    have hb := s.eb t ht v
    have hc := s.ec t ht N
    have hd := s.ed t ht μ
    linarith
  · obtain ⟨b, ψ, rfl⟩ := hrange η hη
    rw [hAh]; exact discreteSkewForm_self D _

theorem projected_compatible_u_L2 {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X) (j : Pt0 →ₗ[ℝ] Z)
    (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] P1)
    (hAh : ∀ a φ b ψ, Ah (ι a, j φ) (ι b, j ψ) = discreteSkewForm D (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (ι a, j ψ) = D.d0 a.1 - D.S0 ψ) {T : ℝ} (hT : 0 < T)
    (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    (p : ℝ → X) (Q : ℝ → Z) (lamP : ℝ → P1)
    (hproj : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪p t, η.1⟫ + Ah (p t, Q t) η - ⟪lamP t, Bh η⟫ = ⟪ξ t, η.1⟫ + A (ξ t, χ t) η - ℓ t η)
    {a : P0 × Pt1 × P2 × Pt2} {q : Pt0} (ha : (ι a, j q) = (p 0, Q 0))
    {ψ : Pt0} (hψ : D.S0 ψ = 0) : ⟪a.2.1, D.dt0 ψ⟫ = 0 := by
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hη : ((ι 0, j ψ) : X × Z) ∈ LinearMap.range
      ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j) := ⟨(0, ψ), rfl⟩
  have h1 := hcont 0 h0 _ hη
  have h2 := hproj 0 h0 _ hη
  rw [← ha, hAh, hBh, hψ] at h2
  simp only [map_zero, inner_zero_right, zero_add] at h1
  simp [discreteSkewForm] at h2
  linarith

theorem exists_discreteSolution_norm_sub_le_L2 [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P1]
    [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt0] [FiniteDimensional ℝ Pt1]
    [FiniteDimensional ℝ Pt2] {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}
    (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X)
    (hι : ∀ a b, ⟪ι a, ι b⟫ = ⟪a.1, b.1⟫ + ⟪a.2.1, b.2.1⟫ + ⟪a.2.2.1, b.2.2.1⟫ +
      ⟪a.2.2.2, b.2.2.2⟫)
    (j : Pt0 →ₗ[ℝ] Z) (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] P1)
    (hAh : ∀ a φ b ψ, Ah (ι a, j φ) (ι b, j ψ) = discreteSkewForm D (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (ι a, j ψ) = D.d0 a.1 - D.S0 ψ) {T : ℝ} (hT : 0 < T)
    {f : ℝ → Pt1} (hf : ContinuousOn f (Icc 0 T))
    (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hF : ∀ t ∈ Ico 0 T, ∀ a, ⟪F t, ι a⟫ = ⟪f t, a.2.1⟫)
    (hξc : ContinuousOn ξ (Icc 0 T)) (hξ'c : ContinuousOn ξ' (Icc 0 T))
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    (p p' : ℝ → X) (Q : ℝ → Z) (lamP : ℝ → P1)
    (hpc : ContinuousOn p (Icc 0 T)) (hp'c : ContinuousOn p' (Icc 0 T))
    (hpd : ∀ t ∈ Ico 0 T, HasDerivWithinAt p (p' t) (Ici t) t)
    (hPmem : ∀ t ∈ Icc 0 T, (p t, Q t) ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j))
    (hPB : ∀ t ∈ Icc 0 T, Bh (p t, Q t) = 0)
    (hproj : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪p t, η.1⟫ + Ah (p t, Q t) η - ⟪lamP t, Bh η⟫ = ⟪ξ t, η.1⟫ + A (ξ t, χ t) η - ℓ t η) :
    ∃ s : DiscreteSolution D T f, ι (s.σ 0, s.u 0, s.M 0, s.ρ 0) = p 0 ∧
      s.φ 0 = phiMap D hdinj hS (s.σ 0, f 0) ∧
      ∀ t ∈ Icc 0 T, ‖ξ t - ι (s.σ t, s.u t, s.M t, s.ρ t)‖ ≤
        ‖ξ t - p t‖ + ∫ r in (0:ℝ)..t, (‖p' r - ξ' r‖ + ‖p r - ξ r‖) := by
  obtain ⟨⟨a, q⟩, hy⟩ := hPmem 0 ⟨le_rfl, hT.le⟩
  have ha : (ι a, j q) = (p 0, Q 0) := hy
  have hC2 : ∀ ψ, D.S0 ψ = 0 → ⟪a.2.1, D.dt0 ψ⟫ = 0 := fun ψ hψ =>
    projected_compatible_u_L2 ι j A Ah Bh hAh hBh hT ξ ξ' χ ℓ F hcont p Q lamP hproj ha hψ
  obtain ⟨s, hσ, hu, hM, hρ⟩ :=
    (exists_discreteSolution_iff_compatible_u hT hdinj hS hf a.1 a.2.1 a.2.2.1 a.2.2.2).2 hC2
  have hinit : ι (s.σ 0, s.u 0, s.M 0, s.ρ 0) = p 0 := by
    rw [hσ, hu, hM, hρ]; exact congrArg Prod.fst ha
  refine ⟨s, hinit, DiscreteSolution.phi_zero hdinj hS hT s, fun t ht => ?_⟩
  have := DiscreteSolution.norm_sub_le_of_ellipticProjection_L2 ι hι j A Ah Bh hAh hBh s ξ ξ' χ
    ℓ F hF hξc hξ'c hcont p p' Q lamP hpc hp'c hpd hPmem hPB hproj t ht
  rwa [hinit, sub_self, norm_zero, add_zero] at this

/-! ## Convergence with the elliptic projection (6.4) itself -/

variable [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P1] [FiniteDimensional ℝ P2]
  [FiniteDimensional ℝ Pt0] [FiniteDimensional ℝ Pt1] [FiniteDimensional ℝ Pt2]

/-- The embedded dynamic part of the elliptic projection (6.4) with data `G t`. -/
def projectedTrajectory {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}
    (hdinj : Function.Injective D.dt0) (hB : ∀ μ : P1, ∃ τ ψ, D.d0 τ - D.S0 ψ = μ)
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X) (G : ℝ → Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0))
    (t : ℝ) : X :=
  ι (ellipticProjection D hdinj hB (ellipticRhs (G t) 0)).1.1

/-- If the data functional of the exact solution is differentiable on discrete tests, (6.3) has a
solution from (6.4) at `t = 0`, with the estimate of `norm_sub_le_of_ellipticProjection_L2`. -/
theorem exists_discreteSolution_norm_sub_le_ellipticProjection
    {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}
    (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X)
    (hι : ∀ a b, ⟪ι a, ι b⟫ = ⟪a.1, b.1⟫ + ⟪a.2.1, b.2.1⟫ + ⟪a.2.2.1, b.2.2.1⟫ +
      ⟪a.2.2.2, b.2.2.2⟫)
    (j : Pt0 →ₗ[ℝ] Z) (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] P1)
    (hAh : ∀ a φ b ψ, Ah (ι a, j φ) (ι b, j ψ) = discreteSkewForm D (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (ι a, j ψ) = D.d0 a.1 - D.S0 ψ) {T : ℝ} (hT : 0 < T)
    {f : ℝ → Pt1} (hf : ContinuousOn f (Icc 0 T))
    (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hF : ∀ t ∈ Ico 0 T, ∀ a, ⟪F t, ι a⟫ = ⟪f t, a.2.1⟫)
    (hξc : ContinuousOn ξ (Icc 0 T)) (hξ'c : ContinuousOn ξ' (Icc 0 T))
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    (G' : ℝ → Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0))
    (hGc : ∀ y, ContinuousOn (fun s => ellipticData ι j A (ξ s) (χ s) (ℓ s) y) (Icc 0 T))
    (hGd : ∀ t ∈ Ico 0 T, ∀ y,
      HasDerivWithinAt (fun s => ellipticData ι j A (ξ s) (χ s) (ℓ s) y) (G' t y) (Ici t) t)
    (hG'c : ∀ y, ContinuousOn (fun s => G' s y) (Icc 0 T)) :
    ∃ s : DiscreteSolution D T f,
      ι (s.σ 0, s.u 0, s.M 0, s.ρ 0) =
        projectedTrajectory hdinj (exists_sub_eq_of_surjective hS) ι
          (fun r => ellipticData ι j A (ξ r) (χ r) (ℓ r)) 0 ∧
      s.φ 0 = phiMap D hdinj hS (s.σ 0, f 0) ∧
      ∀ t ∈ Icc 0 T, ‖ξ t - ι (s.σ t, s.u t, s.M t, s.ρ t)‖ ≤
        ‖ξ t - projectedTrajectory hdinj (exists_sub_eq_of_surjective hS) ι
            (fun r => ellipticData ι j A (ξ r) (χ r) (ℓ r)) t‖ +
          ∫ r in (0:ℝ)..t,
            (‖projectedTrajectory hdinj (exists_sub_eq_of_surjective hS) ι G' r - ξ' r‖ +
              ‖projectedTrajectory hdinj (exists_sub_eq_of_surjective hS) ι
                (fun r => ellipticData ι j A (ξ r) (χ r) (ℓ r)) r - ξ r‖) := by
  set hB := exists_sub_eq_of_surjective hS
  set G : ℝ → Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0) :=
    fun r => ellipticData ι j A (ξ r) (χ r) (ℓ r) with hG
  set Pr : ℝ → ((P0 × Pt1 × P2 × Pt2) × Pt0) × P1 :=
    fun r => ellipticProjection D hdinj hB (ellipticRhs (G r) 0) with hPr
  -- the linear read-out `x ↦ ι x₁₁` and its continuity
  set L : (((P0 × Pt1 × P2 × Pt2) × Pt0) × P1) →L[ℝ] X :=
    ι.comp ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)) with hL
  have hLp : ∀ H, projectedTrajectory hdinj hB ι H = fun r =>
      L (ellipticProjection D hdinj hB (ellipticRhs (H r) 0)) := fun H => rfl
  have hgal : ∀ r, Bh (ι (Pr r).1.1, j (Pr r).1.2) = 0 ∧
      ∀ η ∈ LinearMap.range ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
        ⟪ι (Pr r).1.1, η.1⟫ + Ah (ι (Pr r).1.1, j (Pr r).1.2) η - ⟪(Pr r).2, Bh η⟫ =
          ⟪ξ r, η.1⟫ + A (ξ r, χ r) η - ℓ r η := fun r =>
    IsEllipticProjection.galerkin ι hι j A Ah Bh hAh hBh (ξ r) (χ r) (ℓ r)
      (isEllipticProjection_ellipticProjection hdinj hB (G r) 0)
  have hpc : ContinuousOn (projectedTrajectory hdinj hB ι G) (Icc 0 T) := by
    rw [hLp]; exact L.continuous.comp_continuousOn (continuousOn_ellipticProjection hdinj hB hGc)
  have hp'c : ContinuousOn (projectedTrajectory hdinj hB ι G') (Icc 0 T) := by
    rw [hLp]; exact L.continuous.comp_continuousOn (continuousOn_ellipticProjection hdinj hB hG'c)
  have hpd : ∀ t ∈ Ico 0 T, HasDerivWithinAt (projectedTrajectory hdinj hB ι G)
      (projectedTrajectory hdinj hB ι G' t) (Ici t) t := fun t ht => by
    rw [hLp, hLp]
    exact L.hasFDerivAt.comp_hasDerivWithinAt t
      (hasDerivWithinAt_ellipticProjection hdinj hB (hGd t ht))
  exact exists_discreteSolution_norm_sub_le_L2 hdinj hS ι hι j A Ah Bh hAh hBh hT hf ξ ξ' χ ℓ F
    hF hξc hξ'c hcont (projectedTrajectory hdinj hB ι G)
    (projectedTrajectory hdinj hB ι G') (fun r => j (Pr r).1.2) (fun r => (Pr r).2) hpc hp'c
    hpd (fun r _ => ⟨(Pr r).1, rfl⟩) (fun r _ => (hgal r).1) (fun r _ => (hgal r).2)

end Bridge

/-! ## End-to-end `O(h)` convergence of (6.3) for a discretization `Q : Discrete D` -/

namespace Discrete

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} {Q : Discrete D}
  {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [AddCommGroup Z] [Module ℝ Z]

/-- An embedding `ιc` of `V⁰ × Ṽ¹ × V² × Ṽ²` into `X` preserving the energy inner product. -/
def IsEnergyEmbedding (ιc : (V0 × Vt1 × W2 × Wt2) →L[ℝ] X) : Prop :=
  ∀ a b, ⟪ιc a, ιc b⟫ = ⟪a.1, b.1⟫ + ⟪a.2.1, b.2.1⟫ + ⟪a.2.2.1, b.2.2.1⟫ + ⟪a.2.2.2, b.2.2.2⟫

variable (Q) in
/-- The embedding `Vₕ⁰ × Ṽₕ¹ × Vₕ² × Ṽₕ² → X` of the discrete dynamic state through `ιc`. -/
def embedH (ιc : (V0 × Vt1 × W2 × Wt2) →L[ℝ] X) : (Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) →L[ℝ] X :=
  ιc.comp (Q.V0h.subtypeL.prodMap (Q.Vt1h.subtypeL.prodMap (Q.W2h.subtypeL.prodMap
    Q.Wt2h.subtypeL)))

theorem embedH_apply (ιc : (V0 × Vt1 × W2 × Wt2) →L[ℝ] X)
    (b : Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) :
    Q.embedH ιc b = ιc ((b.1 : V0), (b.2.1 : Vt1), (b.2.2.1 : W2), (b.2.2.2 : Wt2)) := rfl

theorem embedH_inner {ιc : (V0 × Vt1 × W2 × Wt2) →L[ℝ] X} (hιc : IsEnergyEmbedding ιc)
    (a b : Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) :
    ⟪Q.embedH ιc a, Q.embedH ιc b⟫ = ⟪a.1, b.1⟫ + ⟪a.2.1, b.2.1⟫ + ⟪a.2.2.1, b.2.2.1⟫ +
      ⟪a.2.2.2, b.2.2.2⟫ := by
  rw [embedH_apply, embedH_apply, hιc]; simp only [Submodule.coe_inner]

theorem norm_sub_of_isEnergyEmbedding {ιc : (V0 × Vt1 × W2 × Wt2) →L[ℝ] X}
    (hιc : IsEnergyEmbedding ιc) (a b : V0 × Vt1 × W2 × Wt2) :
    ‖ιc a - ιc b‖ = √(‖a.1 - b.1‖ ^ 2 + ‖a.2.1 - b.2.1‖ ^ 2 + ‖a.2.2.1 - b.2.2.1‖ ^ 2 +
      ‖a.2.2.2 - b.2.2.2‖ ^ 2) := by
  rw [← map_sub, ← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, hιc]
  simp only [Prod.fst_sub, Prod.snd_sub, real_inner_self_eq_norm_sq]

theorem ellipticData_embedH {ιc : (V0 × Vt1 × W2 × Wt2) →L[ℝ] X} (hιc : IsEnergyEmbedding ιc)
    (jc : Vt0 →ₗ[ℝ] Z) (A : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ)
    (hA : ∀ a φ (b : Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) (ψ : Q.Vt0h),
      A (ιc a, jc φ) (Q.embedH ιc b, jc ψ) = discreteSkewForm D (a, φ)
        (((b.1 : V0), (b.2.1 : Vt1), (b.2.2.1 : W2), (b.2.2.2 : Wt2)), (ψ : Vt0)))
    (ℓ : (X × Z) →ₗ[ℝ] ℝ) (ℓ₁ : V1 →ₗ[ℝ] ℝ)
    (hℓ : ∀ (b : Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) (ψ : Q.Vt0h),
      ℓ (Q.embedH ιc b, jc ψ) = ℓ₁ (D.d0 b.1 - D.S0 ψ))
    (a : V0 × Vt1 × W2 × Wt2) (φ : Vt0) :
    ellipticData (Q.embedH ιc) (jc ∘ₗ Q.Vt0h.subtype) A (ιc a) (jc φ) ℓ =
      Q.ellipticDataH a.1 φ a.2.1 a.2.2.1 a.2.2.2 ℓ₁ := by
  refine LinearMap.ext fun y => ?_
  rw [ellipticData_apply]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [hA, hℓ, embedH_apply, hιc]
  simp only [ellipticDataH, LinearMap.coe_mk, AddHom.coe_mk, shiftedFormC, discreteSkewForm]
  ring

end Discrete

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

variable {Q : Discrete D}

variable {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [AddCommGroup Z]
  [Module ℝ Z]

open Discrete

theorem norm_sub_embedH_ellipticProjection_le (h54 : Q.Compatible) [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.V1h]
    [FiniteDimensional ℝ Q.W2h] [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h]
    [FiniteDimensional ℝ Q.Wt2h] {ιc : (V0 × Vt1 × W2 × Wt2) →L[ℝ] X}
    (hιc : IsEnergyEmbedding ιc) (hdinj : Function.Injective Q.toSegmentH.dt0)
    (hB : ∀ μ, ∃ τ ψ, Q.toSegmentH.d0 τ - Q.toSegmentH.S0 ψ = μ)
    {a : V0 × Vt1 × W2 × Wt2} {φ : Vt0} (c3 : D.d0 a.1 = D.S0 φ) (ℓ₁ : V1 →ₗ[ℝ] ℝ)
    {K0 K1 c h : ℝ}
    (hK0 : ∀ ψ ∈ Q.Vt0h, |ℓ₁ ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ v ∈ Q.Vt1h, |⟪a.2.2.1, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hdata : Q.strangData a.1 φ a.2.1 a.2.2.1 a.2.2.2 K0 K1 ≤ (c * h) ^ 2) :
    ‖ιc a - Q.embedH ιc (ellipticProjection Q.toSegmentH hdinj hB
        (ellipticRhs (Q.ellipticDataH a.1 φ a.2.1 a.2.2.1 a.2.2.2 ℓ₁) 0)).1.1‖ ≤
      √(2 * (strangConst Cp + 1)) * |c| * |h| := by
  have hx := isEllipticProjection_ellipticProjection hdinj hB
    (Q.ellipticDataH a.1 φ a.2.1 a.2.2.1 a.2.2.2 ℓ₁) 0
  have hS := (HS.strang_of_isEllipticProjection h54 c3 ℓ₁ hK0 hK1 hx).2
  have hC : 0 ≤ 2 * (strangConst Cp + 1) := by unfold strangConst; positivity
  rw [embedH_apply, norm_sub_of_isEnergyEmbedding hιc, mul_assoc, ← abs_mul,
    ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hC]
  exact Real.sqrt_le_sqrt (hS.trans (mul_le_mul_of_nonneg_left hdata hC))

/-- `O(h)` convergence of (6.3) from the elliptic projection (6.4), under `HarmonicStability`. -/
theorem exists_discreteSolution_norm_sub_le_rate (h54 : Q.Compatible) [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.V1h]
    [FiniteDimensional ℝ Q.W2h] [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h]
    [FiniteDimensional ℝ Q.Wt2h] (hS : Function.Surjective Q.toSegmentH.S0)
    {ιc : (V0 × Vt1 × W2 × Wt2) →L[ℝ] X} (hιc : IsEnergyEmbedding ιc) (jc : Vt0 →ₗ[ℝ] Z)
    (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] Q.V1h)
    (hA : ∀ a φ (b : Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) (ψ : Q.Vt0h),
      A (ιc a, jc φ) (Q.embedH ιc b, jc ψ) = discreteSkewForm D (a, φ)
        (((b.1 : V0), (b.2.1 : Vt1), (b.2.2.1 : W2), (b.2.2.2 : Wt2)), (ψ : Vt0)))
    (hAh : ∀ a φ b ψ, Ah (Q.embedH ιc a, (jc ∘ₗ Q.Vt0h.subtype) φ)
      (Q.embedH ιc b, (jc ∘ₗ Q.Vt0h.subtype) ψ) = discreteSkewForm Q.toSegmentH (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (Q.embedH ιc a, (jc ∘ₗ Q.Vt0h.subtype) ψ) =
      Q.toSegmentH.d0 a.1 - Q.toSegmentH.S0 ψ)
    {T : ℝ} (hT : 0 < T) {f : ℝ → Q.Vt1h} (hf : ContinuousOn f (Icc 0 T))
    (a a' : ℝ → V0 × Vt1 × W2 × Wt2) (φ φ' : ℝ → Vt0) (ℓ₁ ℓ₁' : ℝ → V1 →ₗ[ℝ] ℝ)
    (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ)
    (hℓ : ∀ t (b : Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) (ψ : Q.Vt0h),
      ℓ t (Q.embedH ιc b, jc ψ) = ℓ₁ t (D.d0 b.1 - D.S0 ψ))
    (F : ℝ → X) (hF : ∀ t ∈ Ico 0 T, ∀ b, ⟪F t, Q.embedH ιc b⟫ = ⟪f t, b.2.1⟫)
    (hac : ContinuousOn a (Icc 0 T)) (ha'c : ContinuousOn a' (Icc 0 T))
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((Q.embedH ιc : (Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) →ₗ[ℝ] X).prodMap
          (jc ∘ₗ Q.Vt0h.subtype)),
      ⟪ιc (a' t), η.1⟫ + A (ιc (a t), jc (φ t)) η - ℓ t η = ⟪F t, η.1⟫)
    (hGc : ∀ y, ContinuousOn
      (fun s => Q.ellipticDataH (a s).1 (φ s) (a s).2.1 (a s).2.2.1 (a s).2.2.2 (ℓ₁ s) y)
      (Icc 0 T))
    (hGd : ∀ t ∈ Ico 0 T, ∀ y, HasDerivWithinAt
      (fun s => Q.ellipticDataH (a s).1 (φ s) (a s).2.1 (a s).2.2.1 (a s).2.2.2 (ℓ₁ s) y)
      (Q.ellipticDataH (a' t).1 (φ' t) (a' t).2.1 (a' t).2.2.1 (a' t).2.2.2 (ℓ₁' t) y)
      (Ici t) t)
    (hG'c : ∀ y, ContinuousOn
      (fun s => Q.ellipticDataH (a' s).1 (φ' s) (a' s).2.1 (a' s).2.2.1 (a' s).2.2.2 (ℓ₁' s) y)
      (Icc 0 T))
    {K0 K1 c h : ℝ}
    (c3 : ∀ t ∈ Icc 0 T, D.d0 (a t).1 = D.S0 (φ t))
    (c3' : ∀ t ∈ Icc 0 T, D.d0 (a' t).1 = D.S0 (φ' t))
    (hK0 : ∀ t ∈ Icc 0 T, ∀ ψ ∈ Q.Vt0h, |ℓ₁ t ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK0' : ∀ t ∈ Icc 0 T, ∀ ψ ∈ Q.Vt0h, |ℓ₁' t ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ t ∈ Icc 0 T, ∀ v ∈ Q.Vt1h, |⟪(a t).2.2.1, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hK1' : ∀ t ∈ Icc 0 T, ∀ v ∈ Q.Vt1h,
      |⟪(a' t).2.2.1, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hdata : ∀ t ∈ Icc 0 T,
      Q.strangData (a t).1 (φ t) (a t).2.1 (a t).2.2.1 (a t).2.2.2 K0 K1 ≤ (c * h) ^ 2)
    (hdata' : ∀ t ∈ Icc 0 T,
      Q.strangData (a' t).1 (φ' t) (a' t).2.1 (a' t).2.2.1 (a' t).2.2.2 K0 K1 ≤ (c * h) ^ 2) :
    ∃ s : DiscreteSolution Q.toSegmentH T f,
      Q.embedH ιc (s.σ 0, s.u 0, s.M 0, s.ρ 0) =
        Q.embedH ιc (ellipticProjection Q.toSegmentH HS.toSegmentH_dt0_injective
          (exists_sub_eq_of_surjective hS) (ellipticRhs (Q.ellipticDataH (a 0).1 (φ 0)
            (a 0).2.1 (a 0).2.2.1 (a 0).2.2.2 (ℓ₁ 0)) 0)).1.1 ∧
      ∀ t ∈ Icc 0 T, ‖ιc (a t) - Q.embedH ιc (s.σ t, s.u t, s.M t, s.ρ t)‖ ≤
        √(2 * (strangConst Cp + 1)) * |c| * |h| * (2 + 2 * t) := by
  have hdinj := HS.toSegmentH_dt0_injective (Q := Q)
  set hB := exists_sub_eq_of_surjective hS
  set ι := Q.embedH ιc
  set j := jc ∘ₗ Q.Vt0h.subtype
  set G := fun s => Q.ellipticDataH (a s).1 (φ s) (a s).2.1 (a s).2.2.1 (a s).2.2.2 (ℓ₁ s)
    with hGdef
  set G' := fun s => Q.ellipticDataH (a' s).1 (φ' s) (a' s).2.1 (a' s).2.2.1 (a' s).2.2.2
    (ℓ₁' s) with hG'def
  have hGeq : ∀ s, ellipticData ι j A (ιc (a s)) (jc (φ s)) (ℓ s) = G s := fun s =>
    ellipticData_embedH hιc jc A hA (ℓ s) (ℓ₁ s) (hℓ s) (a s) (φ s)
  have hGeqf : (fun s => ellipticData ι j A (ιc (a s)) (jc (φ s)) (ℓ s)) = G := funext hGeq
  obtain ⟨s, hinit, -, hbd⟩ := exists_discreteSolution_norm_sub_le_ellipticProjection hdinj hS ι
    (embedH_inner hιc) j A Ah Bh hAh hBh hT hf (fun t => ιc (a t)) (fun t => ιc (a' t))
    (fun t => jc (φ t)) ℓ F hF (ιc.continuous.comp_continuousOn hac)
    (ιc.continuous.comp_continuousOn ha'c) hcont G'
    (fun y => by simpa only [hGeq] using hGc y)
    (fun t ht y => by simpa only [hGeq] using hGd t ht y) hG'c
  rw [hGeqf] at hinit hbd
  set ε := √(2 * (strangConst Cp + 1)) * |c| * |h|
  have hε : 0 ≤ ε := by positivity
  set p := projectedTrajectory hdinj hB ι G
  set p' := projectedTrajectory hdinj hB ι G'
  have hp : ∀ t, p t = ι (ellipticProjection Q.toSegmentH hdinj hB (ellipticRhs (G t) 0)).1.1 :=
    fun t => rfl
  have hp' : ∀ t,
      p' t = ι (ellipticProjection Q.toSegmentH hdinj hB (ellipticRhs (G' t) 0)).1.1 :=
    fun t => rfl
  set L : (((Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h) × Q.V1h) →L[ℝ] X :=
    ι.comp ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))
  have hpc : ContinuousOn p (Icc 0 T) :=
    L.continuous.comp_continuousOn (continuousOn_ellipticProjection hdinj hB hGc)
  have hp'c : ContinuousOn p' (Icc 0 T) :=
    L.continuous.comp_continuousOn (continuousOn_ellipticProjection hdinj hB hG'c)
  have h1 : ∀ t ∈ Icc 0 T, ‖ιc (a t) - p t‖ ≤ ε := fun t ht => by
    rw [hp]
    exact HS.norm_sub_embedH_ellipticProjection_le h54 hιc hdinj hB (c3 t ht) (ℓ₁ t)
      (hK0 t ht) (hK1 t ht) (hdata t ht)
  have h3 : ∀ t ∈ Icc 0 T, ‖p' t - ιc (a' t)‖ ≤ ε := fun t ht => by
    rw [norm_sub_rev, hp']
    exact HS.norm_sub_embedH_ellipticProjection_le h54 hιc hdinj hB (c3' t ht) (ℓ₁' t)
      (hK0' t ht) (hK1' t ht) (hdata' t ht)
  refine ⟨s, hinit, ?_⟩
  refine norm_sub_le_mul_of_ellipticProjection_L2 (ξ := fun t => ιc (a t))
    (ξ' := fun t => ιc (a' t)) (ξh := fun t => ι (s.σ t, s.u t, s.M t, s.ρ t)) (p := p)
    (p' := p') (ιc.continuous.comp_continuousOn hac) (ιc.continuous.comp_continuousOn ha'c)
    hpc hp'c (fun t ht => ?_) h1 ?_ h3
  · have hb := hbd t ht
    have : 0 ≤ ‖p 0 - ι (s.σ 0, s.u 0, s.M 0, s.ρ 0)‖ := norm_nonneg _
    linarith
  · rw [show p 0 = ι (s.σ 0, s.u 0, s.M 0, s.ρ 0) from hinit.symm, sub_self, norm_zero]
    exact hε

end HarmonicStability

namespace Discrete

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} {Q : Discrete D}
  {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [AddCommGroup Z] [Module ℝ Z]

theorem norm_sub_embedH_ellipticProjection_le {Cp CR CS : ℝ} (H : Stability D Cp CR CS)
    (h54 : Q.Compatible) [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.V1h]
    [FiniteDimensional ℝ Q.W2h] [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h]
    [FiniteDimensional ℝ Q.Wt2h] {ιc : (V0 × Vt1 × W2 × Wt2) →L[ℝ] X}
    (hιc : IsEnergyEmbedding ιc) (hdinj : Function.Injective Q.toSegmentH.dt0)
    (hB : ∀ μ, ∃ τ ψ, Q.toSegmentH.d0 τ - Q.toSegmentH.S0 ψ = μ)
    {a : V0 × Vt1 × W2 × Wt2} {φ : Vt0} (c3 : D.d0 a.1 = D.S0 φ) (ℓ₁ : V1 →ₗ[ℝ] ℝ)
    {K0 K1 c h : ℝ}
    (hK0 : ∀ ψ ∈ Q.Vt0h, |ℓ₁ ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ v ∈ Q.Vt1h, |⟪a.2.2.1, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hdata : Q.strangData a.1 φ a.2.1 a.2.2.1 a.2.2.2 K0 K1 ≤ (c * h) ^ 2) :
    ‖ιc a - Q.embedH ιc (ellipticProjection Q.toSegmentH hdinj hB
        (ellipticRhs (Q.ellipticDataH a.1 φ a.2.1 a.2.2.1 a.2.2.2 ℓ₁) 0)).1.1‖ ≤
      √(2 * (strangConst Cp + 1)) * |c| * |h| :=
  H.toHarmonicStability.norm_sub_embedH_ellipticProjection_le h54 hιc hdinj hB c3 ℓ₁ hK0 hK1 hdata

/-- Under `Stability`, (5.4), `S₀,ₕ` onto and `strangData ≤ (c h)²` for `a` and `a'`, (6.3) has a
solution from (6.4) with an `O(h)` error on `[0,T]`. Cf. [QuennevilleBelair2015], Thm 4.14 -/
theorem exists_discreteSolution_norm_sub_le_rate {Cp CR CS : ℝ} (H : Stability D Cp CR CS)
    (h54 : Q.Compatible) [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.V1h]
    [FiniteDimensional ℝ Q.W2h] [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h]
    [FiniteDimensional ℝ Q.Wt2h] (hS : Function.Surjective Q.toSegmentH.S0)
    {ιc : (V0 × Vt1 × W2 × Wt2) →L[ℝ] X} (hιc : IsEnergyEmbedding ιc) (jc : Vt0 →ₗ[ℝ] Z)
    (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] Q.V1h)
    (hA : ∀ a φ (b : Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) (ψ : Q.Vt0h),
      A (ιc a, jc φ) (Q.embedH ιc b, jc ψ) = discreteSkewForm D (a, φ)
        (((b.1 : V0), (b.2.1 : Vt1), (b.2.2.1 : W2), (b.2.2.2 : Wt2)), (ψ : Vt0)))
    (hAh : ∀ a φ b ψ, Ah (Q.embedH ιc a, (jc ∘ₗ Q.Vt0h.subtype) φ)
      (Q.embedH ιc b, (jc ∘ₗ Q.Vt0h.subtype) ψ) = discreteSkewForm Q.toSegmentH (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (Q.embedH ιc a, (jc ∘ₗ Q.Vt0h.subtype) ψ) =
      Q.toSegmentH.d0 a.1 - Q.toSegmentH.S0 ψ)
    {T : ℝ} (hT : 0 < T) {f : ℝ → Q.Vt1h} (hf : ContinuousOn f (Icc 0 T))
    (a a' : ℝ → V0 × Vt1 × W2 × Wt2) (φ φ' : ℝ → Vt0) (ℓ₁ ℓ₁' : ℝ → V1 →ₗ[ℝ] ℝ)
    (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ)
    (hℓ : ∀ t (b : Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) (ψ : Q.Vt0h),
      ℓ t (Q.embedH ιc b, jc ψ) = ℓ₁ t (D.d0 b.1 - D.S0 ψ))
    (F : ℝ → X) (hF : ∀ t ∈ Ico 0 T, ∀ b, ⟪F t, Q.embedH ιc b⟫ = ⟪f t, b.2.1⟫)
    (hac : ContinuousOn a (Icc 0 T)) (ha'c : ContinuousOn a' (Icc 0 T))
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((Q.embedH ιc : (Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) →ₗ[ℝ] X).prodMap
          (jc ∘ₗ Q.Vt0h.subtype)),
      ⟪ιc (a' t), η.1⟫ + A (ιc (a t), jc (φ t)) η - ℓ t η = ⟪F t, η.1⟫)
    (hGc : ∀ y, ContinuousOn
      (fun s => Q.ellipticDataH (a s).1 (φ s) (a s).2.1 (a s).2.2.1 (a s).2.2.2 (ℓ₁ s) y)
      (Icc 0 T))
    (hGd : ∀ t ∈ Ico 0 T, ∀ y, HasDerivWithinAt
      (fun s => Q.ellipticDataH (a s).1 (φ s) (a s).2.1 (a s).2.2.1 (a s).2.2.2 (ℓ₁ s) y)
      (Q.ellipticDataH (a' t).1 (φ' t) (a' t).2.1 (a' t).2.2.1 (a' t).2.2.2 (ℓ₁' t) y)
      (Ici t) t)
    (hG'c : ∀ y, ContinuousOn
      (fun s => Q.ellipticDataH (a' s).1 (φ' s) (a' s).2.1 (a' s).2.2.1 (a' s).2.2.2 (ℓ₁' s) y)
      (Icc 0 T))
    {K0 K1 c h : ℝ}
    (c3 : ∀ t ∈ Icc 0 T, D.d0 (a t).1 = D.S0 (φ t))
    (c3' : ∀ t ∈ Icc 0 T, D.d0 (a' t).1 = D.S0 (φ' t))
    (hK0 : ∀ t ∈ Icc 0 T, ∀ ψ ∈ Q.Vt0h, |ℓ₁ t ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK0' : ∀ t ∈ Icc 0 T, ∀ ψ ∈ Q.Vt0h, |ℓ₁' t ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ t ∈ Icc 0 T, ∀ v ∈ Q.Vt1h, |⟪(a t).2.2.1, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hK1' : ∀ t ∈ Icc 0 T, ∀ v ∈ Q.Vt1h,
      |⟪(a' t).2.2.1, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hdata : ∀ t ∈ Icc 0 T,
      Q.strangData (a t).1 (φ t) (a t).2.1 (a t).2.2.1 (a t).2.2.2 K0 K1 ≤ (c * h) ^ 2)
    (hdata' : ∀ t ∈ Icc 0 T,
      Q.strangData (a' t).1 (φ' t) (a' t).2.1 (a' t).2.2.1 (a' t).2.2.2 K0 K1 ≤ (c * h) ^ 2) :
    ∃ s : DiscreteSolution Q.toSegmentH T f,
      Q.embedH ιc (s.σ 0, s.u 0, s.M 0, s.ρ 0) =
        Q.embedH ιc (ellipticProjection Q.toSegmentH (toSegmentH_dt0_injective H)
          (exists_sub_eq_of_surjective hS) (ellipticRhs (Q.ellipticDataH (a 0).1 (φ 0)
            (a 0).2.1 (a 0).2.2.1 (a 0).2.2.2 (ℓ₁ 0)) 0)).1.1 ∧
      ∀ t ∈ Icc 0 T, ‖ιc (a t) - Q.embedH ιc (s.σ t, s.u t, s.M t, s.ρ t)‖ ≤
        √(2 * (strangConst Cp + 1)) * |c| * |h| * (2 + 2 * t) :=
  H.toHarmonicStability.exists_discreteSolution_norm_sub_le_rate h54 hS hιc jc A Ah Bh hA hAh hBh hT
    hf a a' φ φ' ℓ₁ ℓ₁' ℓ hℓ F hF hac ha'c hcont hGc hGd hG'c c3 c3' hK0 hK0' hK1 hK1' hdata
    hdata'

end Discrete

end Feec.BGG
