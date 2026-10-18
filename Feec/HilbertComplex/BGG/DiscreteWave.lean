module

public import Feec.HilbertComplex.BGG.EllipticProjection

/-!
# Convergence of the semi-discrete BGG wave system (6.3) through the elliptic projection (6.4)

The Ch. 6 convergence theorems of `Feec.HilbertComplex.BGG.TimeDependent`
(`norm_sub_le_of_ellipticProjection`, `exists_discreteSolution_norm_sub_le`) take an elliptic
projection *without* the `L²` term as a hypothesis. The thesis' (6.4) has the `L²` (mass) term.
Here the convergence theorems are proved for the projection with the `L²` term: the error bound
gains `∫₀ᵗ ‖Pξ − ξ‖`; the projected trajectory may be any differentiable trajectory (not
necessarily a fixed linear map of `ξ`). For the projection `Feec.BGG.ellipticProjection` of (6.4)
the projection hypotheses are discharged (`exists_discreteSolution_norm_sub_le_ellipticProjection`).

## Main results

* `Feec.BGG.norm_sub_le_of_ellipticProjection_L2`: the abstract energy estimate
  `‖ξ(t) − ξₕ(t)‖ ≤ ‖ξ(t) − p(t)‖ + ‖p(0) − ξₕ(0)‖ + ∫₀ᵗ (‖p' − ξ'‖ + ‖p − ξ‖)`.
* `Feec.BGG.DiscreteSolution.norm_sub_le_of_ellipticProjection_L2`: the same with the discrete
  side discharged by a solution of (6.3).
* `Feec.BGG.projected_compatible_u_L2`: the projected dynamic datum satisfies (C2).
* `Feec.BGG.exists_discreteSolution_norm_sub_le_L2`: existence of the discrete solution from
  the projected initial data and the estimate with no initial error.
* `Feec.BGG.exists_discreteSolution_norm_sub_le_ellipticProjection`: the same for the elliptic
  projection (6.4) itself, all projection hypotheses proved.
* `Feec.BGG.norm_sub_le_mul_of_ellipticProjection_L2`: the rate form
  `‖ξ(t) − ξₕ(t)‖ ≤ ε (2 + 2t)`, e.g. `ε = C h` from `Discrete.strang_energy_rate`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2 ((6.3), (6.4), Prop 6.2, Prop 6.3), Thm 4.14
* [M. F. Wheeler, *A priori L₂ error estimates for Galerkin approximations to parabolic partial differential equations*][Wheeler1973]
  (elliptic projections in evolution problems)
* [G. A. Baker, *Error estimates for finite element methods for second order hyperbolic equations*][Baker1976]
* [T. Dupont, *L²-estimates for Galerkin methods for second order hyperbolic equations*][Dupont1973]
* [T. Geveci, *On the application of mixed finite element methods to the wave equations*][Geveci1988]
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]
-/

open scoped RealInnerProductSpace
open Set

@[expose] public noncomputable section

namespace Feec.BGG

/-! ## The abstract energy estimate with the `L²` term -/

/-- **Ch. 6 convergence through an elliptic projection with `L²` term** (thesis (6.4); the
thesis states no convergence theorem). Abstract setting of `norm_sub_le_of_ellipticProjection`,
with the projected trajectory `p` (derivative `p'`) and the shifted projection equation
`hproj`: `⟪p, η₁⟫ + Aₕ((p, Q), η) − ⟪λₚ, Bₕη⟫ = ⟪ξ, η₁⟫ + A((ξ, χ), η) − ℓη` on `Xₕ`. Then
`‖ξ(t) − ξₕ(t)‖ ≤ ‖ξ(t) − p(t)‖ + ‖p(0) − ξₕ(0)‖ + ∫₀ᵗ (‖p' − ξ'‖ + ‖p − ξ‖)`.
Proof: the error `e = p − ξₕ` satisfies `⟪e', e⟫ = ⟪p' − ξ', e⟫ − ⟪p − ξ, e⟫` (the `L²` term of
the projection is the second summand), then the energy argument.
See [QuennevilleBelair2015], §6.2, (6.4), and Thm 4.14; cf. [Wheeler1973], [Baker1976],
[Dupont1973], [Geveci1988], [GilletteHolstZhu2017]. -/
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

/-- `norm_sub_le_of_ellipticProjection_L2` for a projection given by a fixed continuous linear
map `P` (the form of `norm_sub_le_of_ellipticProjection`): the bound gains `∫₀ᵗ ‖Pξ − ξ‖`. -/
theorem norm_sub_le_of_ellipticProjection_L2' {X Z Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X]
    [AddCommGroup Z] [Module ℝ Z] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (Xh : Submodule ℝ (X × Z)) (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ)
    (Bh : (X × Z) →ₗ[ℝ] Y) (P : X →L[ℝ] X) {T : ℝ}
    (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hξc : ContinuousOn ξ (Icc 0 T)) (hξ'c : ContinuousOn ξ' (Icc 0 T))
    (hξd : ∀ t ∈ Ico 0 T, HasDerivWithinAt ξ (ξ' t) (Ici t) t)
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ Xh, ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    (ξh ξh' : ℝ → X) (χh : ℝ → Z) (lamh : ℝ → Y)
    (hmem : ∀ t ∈ Icc 0 T, (ξh t, χh t) ∈ Xh) (hBh : ∀ t ∈ Icc 0 T, Bh (ξh t, χh t) = 0)
    (hξhc : ContinuousOn ξh (Icc 0 T))
    (hξhd : ∀ t ∈ Ico 0 T, HasDerivWithinAt ξh (ξh' t) (Ici t) t)
    (hdisc : ∀ t ∈ Ico 0 T, ∀ η ∈ Xh,
      ⟪ξh' t, η.1⟫ + Ah (ξh t, χh t) η - ⟪lamh t, Bh η⟫ = ⟪F t, η.1⟫)
    (Q : ℝ → Z) (lamP : ℝ → Y) (hPmem : ∀ t ∈ Icc 0 T, (P (ξ t), Q t) ∈ Xh)
    (hPB : ∀ t ∈ Icc 0 T, Bh (P (ξ t), Q t) = 0)
    (hproj : ∀ t ∈ Ico 0 T, ∀ η ∈ Xh,
      ⟪P (ξ t), η.1⟫ + Ah (P (ξ t), Q t) η - ⟪lamP t, Bh η⟫ =
        ⟪ξ t, η.1⟫ + A (ξ t, χ t) η - ℓ t η)
    (hskew : ∀ η ∈ Xh, Ah η η = 0) :
    ∀ t ∈ Icc 0 T, ‖ξ t - ξh t‖ ≤ ‖ξ t - P (ξ t)‖ + ‖P (ξ 0) - ξh 0‖ +
      ∫ s in (0:ℝ)..t, (‖P (ξ' s) - ξ' s‖ + ‖P (ξ s) - ξ s‖) :=
  norm_sub_le_of_ellipticProjection_L2 Xh A Ah Bh ξ ξ' χ ℓ F hξc hξ'c hcont ξh ξh' χh lamh
    hmem hBh hξhc hξhd hdisc (fun t => P (ξ t)) (fun t => P (ξ' t)) Q lamP
    (P.continuous.comp_continuousOn hξc) (P.continuous.comp_continuousOn hξ'c)
    (fun t ht => P.hasFDerivAt.comp_hasDerivWithinAt t (hξd t ht)) hPmem hPB hproj hskew

/-- **Rate form** of `norm_sub_le_of_ellipticProjection_L2`: if the projection errors
`‖ξ − p‖`, `‖p' − ξ'‖` and the initial discrete error are `≤ ε` on `[0,T]` (e.g. `ε = C h` from
`Discrete.strang_energy_rate` applied to `ξ` and to `ξ'`), then `‖ξ(t) − ξₕ(t)‖ ≤ ε (2 + 2t)`.
Cf. [QuennevilleBelair2015], Thm 4.14. -/
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

/-- **Ch. 6 convergence for (6.3) with the elliptic projection (6.4) (`L²` term included).**
`norm_sub_le_of_ellipticProjection_L2` with its discrete hypotheses discharged by a solution
`s` of (6.3), in the setting of `DiscreteSolution.norm_sub_le_of_ellipticProjection`
(energy-preserving embedding `ι`, `Xₕ = range (ι × j)`, discrete forms `hAh`, `hBh`).
See [QuennevilleBelair2015], §6.2, (6.3), (6.4). -/
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

/-- **The projected dynamic datum satisfies (C2)** for the elliptic projection with `L²` term
(as `projected_compatible_u` for the projection without it): if `(ι a, j q) = (p(0), Q(0))`
then `a_u ⊥ d(ker S₀,ₕ)`. Test with `η = (ι 0, j ψ)`, `ψ ∈ ker S₀,ₕ`: the `L²` term
`⟪p(0), ι 0⟫` vanishes. See [QuennevilleBelair2015], §6.2, Prop 6.2. -/
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

/-- **Ch. 6 convergence from projected initial data, `L²` projection (no solution assumed).**
Hypotheses of `DiscreteSolution.norm_sub_le_of_ellipticProjection_L2` without `s`, plus `T > 0`,
`f` continuous, finite-dimensional FE spaces, `d` injective on `Ṽₕ⁰`, `S₀,ₕ` onto. Then (6.3)
has a solution whose dynamic initial datum is `p(0)` (admissible by
`projected_compatible_u_L2`) and whose algebraic datum is the forced `Φ(σₕ(0), f(0))`, and
`‖ξ(t) − ξₕ(t)‖ ≤ ‖ξ(t) − p(t)‖ + ∫₀ᵗ (‖p' − ξ'‖ + ‖p − ξ‖)`.
See [QuennevilleBelair2015], §6.2, Prop 6.2, (6.4). -/
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

/-- The projected trajectory `p(t) = ι(Πₕ(ξ(t), χ(t), ℓ(t)))₁`: the dynamic part of the elliptic
projection (6.4) of the exact state at time `t`, embedded in `X`. -/
def projectedTrajectory {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}
    (hdinj : Function.Injective D.dt0) (hB : ∀ μ : P1, ∃ τ ψ, D.d0 τ - D.S0 ψ = μ)
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X) (G : ℝ → Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0))
    (t : ℝ) : X :=
  ι (ellipticProjection D hdinj hB (ellipticRhs (G t) 0)).1.1

/-- **Ch. 6 convergence through the elliptic projection (6.4), all projection hypotheses
proved.** Assume the setting of `exists_discreteSolution_norm_sub_le_L2` without any projection
hypothesis, and that the data functional `G(t) = ellipticData ι j A (ξ t) (χ t) (ℓ t)` of the
exact solution is differentiable (`hGd`, derivative `G'`, continuous) on every discrete test
function. Let `p(t) = projectedTrajectory … G t` (the elliptic projection `Πₕ`) and
`p'(t) = projectedTrajectory … G' t`. Then (6.3) has a solution with initial datum `p(0)` (and
the forced `φₕ(0)`), and `‖ξ(t) − ξₕ(t)‖ ≤ ‖ξ(t) − p(t)‖ + ∫₀ᵗ (‖p' − ξ'‖ + ‖p − ξ‖)`.
The thesis defines (6.4) but proves neither its solvability nor any convergence.
See [QuennevilleBelair2015], §6.2, (6.3), (6.4), Prop 6.2. -/
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

end Feec.BGG
