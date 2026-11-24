module

public import Solution.DiscreteWave

/-!
# Stability and well-posedness of the semi-discrete problem (6.5)

For any data `D` and any discretization `Q`, the energy of the difference of two solutions of
(6.5) with sources `f`, `f'` has right derivative `2 ⟪f - f', uₕ - uₕ'⟫`, so trajectories satisfy
`‖U(t) - U'(t)‖ ≤ ‖U(0) - U'(0)‖ + ∫₀ᵗ ‖f - f'‖` (`stateNorm_sub_le_of_mem_trajectories`, by
`Feec.Variational.norm_sub_le_of_projected_error`).

For BGG data every solution satisfies, at every `t ∈ [0, T)` and for every `ψ ∈ Ṽₕ⁰` with
`π¹S⁰ψ = 0`, the hidden constraint `⟪uₕ(t), d̃ψ⟫ = 0` (the first equation at `τ = 0`) and
`⟪d̃φₕ(t) - f(t), d̃ψ⟫ = 0` (its derivative, with the second equation at `v = d̃ψ`, where
`π²S¹d̃ψ = -d π¹S⁰ψ = 0`): `IsDiscreteWave.inner_dt0_eq_zero`. These are the conditions (C2), (C3)
at `t = 0`; with `d̃⁰` injective on `Ṽₕ⁰` and `π¹S⁰` onto `Vₕ¹` they determine `φₕ`, `λₕ` on
`[0, T)` (`IsDiscreteWave.phi_lam_eq`). Conversely, the data satisfying them start solutions:
`Q` is `Feec`'s discrete segment `(Q.toDiscrete hD).toSegmentH` with the source projected onto
`Ṽₕ¹` (`srcH`), whose solutions are solutions of (6.5) (`isDiscreteWave_ofDS`), and `Feec`'s
form of Prop 6.2 gives them (`Feec.BGG.exists_discreteSolution_of_continuousOn`,
`Feec.BGG.exists_discreteSolution_iff_compatible_u`). `wellPosed_of` collects the clause of
`FEEC.bggWeakSymmetry`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2, Prop 6.2, (6.5)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace Topology
open Set Filter MeasureTheory

@[expose] public noncomputable section

namespace FEEC.WeakSymmetryData.Discretization

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] {D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2} (Q : D.Discretization)

/-! ### Stability -/

/-- **Stability of (6.5) in the data and the source**: two trajectories with sources `f`, `f'`,
`f - f'` continuous on `[0, T]`, have `‖U(t) - U'(t)‖ ≤ ‖U(0) - U'(0)‖ + ∫₀ᵗ ‖f - f'‖` in the
state norm (the right derivative of the energy of the difference is `2 ⟪f - f', uₕ - uₕ'⟫`). -/
theorem stateNorm_sub_le_of_mem_trajectories {T : ℝ} {f f' : ℝ → Wt1}
    (hf : ContinuousOn (f - f') (Icc 0 T)) {U U' : ℝ → W0 × Wt1 × W2 × Wt2}
    (hU : U ∈ Q.trajectories T f) (hU' : U' ∈ Q.trajectories T f') :
    ∀ t ∈ Icc 0 T, stateNorm (U t - U' t) ≤
      stateNorm (U 0 - U' 0) + ∫ s in Icc 0 t, ‖f s - f' s‖ := by
  obtain ⟨σ, φ, u, M, ρ, lam, ⟨cσ, cu, cM, cρ, hm, σ', u', M', ρ', hd⟩, e⟩ := hU
  obtain ⟨σ₂, φ₂, u₂, M₂, ρ₂, lam₂, ⟨cσ₂, cu₂, cM₂, cρ₂, hm₂, σ₂', u₂', M₂', ρ₂', hd₂⟩, e₂⟩ := hU'
  set ι := Feec.BGG.energyEmb W0 Wt1 W2 Wt2
  have hι := Feec.BGG.isEnergyEmbedding_energyEmb (V0 := W0) (Vt1 := Wt1) (W2 := W2) (Wt2 := Wt2)
  have hUV : ∀ s, U s - U' s =
      ((σ s : W0) - σ₂ s, (u s : Wt1) - u₂ s, M s - M₂ s, ρ s - ρ₂ s) :=
    fun s => by rw [e, e₂]; rfl
  have hn : ∀ s, ‖ι (U s - U' s) - 0‖ = stateNorm (U s - U' s) := fun s => by
    have h := Feec.BGG.Discrete.norm_sub_of_isEnergyEmbedding hι (U s - U' s) 0
    rw [map_zero] at h
    rw [h, stateNorm]
    simp
  have hc : ContinuousOn (fun s => ι (U s - U' s) - 0) (Icc 0 T) := by
    have h : ContinuousOn (fun s => U s - U' s) (Icc 0 T) := by
      simp only [hUV]
      exact (cσ.sub cσ₂).prodMk ((cu.sub cu₂).prodMk ((cM.sub cM₂).prodMk (cρ.sub cρ₂)))
    exact (ι.continuous.comp_continuousOn h).sub continuousOn_const
  set V' : ℝ → W0 × Wt1 × W2 × Wt2 :=
    fun s => (σ' s - σ₂' s, u' s - u₂' s, M' s - M₂' s, ρ' s - ρ₂' s) with hV'
  have hder : ∀ s ∈ Ico 0 T,
      HasDerivWithinAt (fun s => ι (U s - U' s) - 0) (ι (V' s)) (Ici s) s := by
    intro s hs
    obtain ⟨dσ, du, dM, dρ, -⟩ := hd s hs
    obtain ⟨dσ₂, du₂, dM₂, dρ₂, -⟩ := hd₂ s hs
    have h1 : HasDerivWithinAt (fun r => U r - U' r) (V' s) (Ici s) s := by
      simp only [hUV]
      exact (dσ.sub dσ₂).prodMk ((du.sub du₂).prodMk ((dM.sub dM₂).prodMk (dρ.sub dρ₂)))
    exact (ι.hasFDerivAt.comp_hasDerivWithinAt s h1).sub_const 0
  have herr : ∀ s ∈ Ico 0 T, RCLike.re ⟪ι (V' s), ι (U s - U' s) - 0⟫ ≤
      ‖(f - f') s‖ * ‖ι (U s - U' s) - 0‖ := by
    intro s hs
    have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
    obtain ⟨-, -, -, -, a1, b1, c1, d1⟩ := hd s hs
    obtain ⟨-, -, -, -, a2, b2, c2, d2⟩ := hd₂ s hs
    obtain ⟨mσ, mφ, mu, mM, mρ, -, k1⟩ := hm s hs'
    obtain ⟨mσ₂, mφ₂, mu₂, mM₂, mρ₂, -, k2⟩ := hm₂ s hs'
    have hτ : D.d0 (σ s - σ₂ s) - Q.π1 (D.S0 ((φ s - φ₂ s : D.dt0.domain) : Wt0)) = 0 := by
      rw [LinearPMap.map_sub, Submodule.coe_sub, map_sub, map_sub, k1, k2, sub_self]
    have A1 := a1 (σ s - σ₂ s) (φ s - φ₂ s) (Q.V0.sub_mem mσ mσ₂) (Q.Vt0.sub_mem mφ mφ₂)
    have A2 := a2 (σ s - σ₂ s) (φ s - φ₂ s) (Q.V0.sub_mem mσ mσ₂) (Q.Vt0.sub_mem mφ mφ₂)
    rw [hτ, inner_zero_right, sub_zero] at A1 A2
    have B1 := b1 (u s - u₂ s) (Q.Vt1.sub_mem mu mu₂)
    have B2 := b2 (u s - u₂ s) (Q.Vt1.sub_mem mu mu₂)
    have C1 := c1 (M s - M₂ s) (Q.V2.sub_mem mM mM₂)
    have C2 := c2 (M s - M₂ s) (Q.V2.sub_mem mM mM₂)
    have D1 := d1 (ρ s - ρ₂ s) (Q.Vt2.sub_mem mρ mρ₂)
    have D2 := d2 (ρ s - ρ₂ s) (Q.Vt2.sub_mem mρ mρ₂)
    simp only [Submodule.coe_sub, LinearPMap.map_sub, map_sub, inner_sub_right]
      at A1 A2 B1 B2 C1 C2 D1 D2
    have key : ⟪ι (V' s), ι (U s - U' s) - 0⟫ = ⟪f s - f' s, (u s : Wt1) - u₂ s⟫ := by
      rw [sub_zero, hUV, hι, hV']
      simp only [inner_sub_left, inner_sub_right]
      linarith [real_inner_comm (D.dt0 (φ s)) (u s : Wt1),
        real_inner_comm (D.dt0 (φ₂ s)) (u s : Wt1), real_inner_comm (D.dt0 (φ s)) (u₂ s : Wt1),
        real_inner_comm (D.dt0 (φ₂ s)) (u₂ s : Wt1), real_inner_comm (Q.π2 (D.S1 (u s))) (M s),
        real_inner_comm (Q.π2 (D.S1 (u s))) (M₂ s), real_inner_comm (Q.π2 (D.S1 (u₂ s))) (M s),
        real_inner_comm (Q.π2 (D.S1 (u₂ s))) (M₂ s), real_inner_comm (D.dt1 (u s)) (ρ s),
        real_inner_comm (D.dt1 (u s)) (ρ₂ s), real_inner_comm (D.dt1 (u₂ s)) (ρ s),
        real_inner_comm (D.dt1 (u₂ s)) (ρ₂ s)]
    have hu : ‖(u s : Wt1) - u₂ s‖ ≤ ‖ι (U s - U' s) - 0‖ := by
      rw [hn, hUV, stateNorm]
      exact Real.le_sqrt_of_sq_le (by
        nlinarith [sq_nonneg ‖(σ s : W0) - σ₂ s‖, sq_nonneg ‖M s - M₂ s‖,
          sq_nonneg ‖ρ s - ρ₂ s‖])
    rw [RCLike.re_to_real, key, Pi.sub_apply]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
  have hmain := Feec.Variational.norm_sub_le_of_projected_error (𝕜 := ℝ)
    (u := fun s => ι (U s - U' s)) (p := fun s => ι (U s - U' s)) (uh := fun _ => 0) hc hder
    hf.norm (fun _ _ => norm_nonneg _) herr
  intro t ht
  have h := hmain t ht
  simp only [sub_self, norm_zero, zero_add] at h
  rw [hn, hn] at h
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1]
  simpa only [Pi.sub_apply] using h

/-! ### The hidden constraint and the compatibility conditions -/

/-- A function vanishing on `[t, T)`, `t < T`, has right derivative `0` at `t`. -/
theorem hasDerivWithinAt_Ici_eq_zero_of_eqOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → E} {g' : E} {t T : ℝ} (ht : t < T)
    (hg : ∀ s ∈ Ico t T, g s = 0) (h : HasDerivWithinAt g g' (Ici t) t) : g' = 0 := by
  have hev : g =ᶠ[𝓝[Ici t] t] fun _ => 0 := by
    filter_upwards [Ico_mem_nhdsGE ht] with s hs
    exact hg s hs
  have h0 : HasDerivWithinAt g 0 (Ici t) t :=
    (hasDerivWithinAt_const t (Ici t) (0 : E)).congr_of_eventuallyEq hev (hg t ⟨le_rfl, ht⟩)
  exact (uniqueDiffWithinAt_Ici t).eq_deriv _ h h0

variable {Q}

/-- **The hidden constraint and (C3) along (6.5)**: for BGG data, every solution has, at every
`t ∈ [0, T)` and for every `ψ ∈ Ṽₕ⁰` with `π¹S⁰ψ = 0`, `⟪uₕ(t), d̃ψ⟫ = 0` (the first equation
at `τ = 0`) and `⟪d̃φₕ(t) - f(t), d̃ψ⟫ = 0` (its right derivative, with the second equation at
`v = d̃ψ`: `d̃d̃ψ = 0` and `π²S¹d̃ψ = -d π¹S⁰ψ = 0`). -/
theorem IsDiscreteWave.inner_dt0_eq_zero (hD : D.IsBGG) {T : ℝ} {f : ℝ → Wt1}
    {σ : ℝ → D.d0.domain} {φ : ℝ → D.dt0.domain} {u : ℝ → D.dt1.domain} {M : ℝ → W2}
    {ρ : ℝ → Wt2} {lam : ℝ → W1} (h : Q.IsDiscreteWave T f σ φ u M ρ lam) {t : ℝ}
    (ht : t ∈ Ico 0 T) {ψ : D.dt0.domain} (hψ : (ψ : Wt0) ∈ Q.Vt0) (hψ0 : Q.π1 (D.S0 ψ) = 0) :
    ⟪(u t : Wt1), D.dt0 ψ⟫ = 0 ∧ ⟪D.dt0 (φ t) - f t, D.dt0 ψ⟫ = 0 := by
  obtain ⟨-, -, -, -, -, σ', u', M', ρ', hd⟩ := h
  have hid : ∀ s ∈ Ico 0 T, ⟪(u s : Wt1), D.dt0 ψ⟫ = 0 := fun s hs => by
    have := (hd s hs).2.2.2.2.1 0 ψ Q.V0.zero_mem hψ
    simp only [ZeroMemClass.coe_zero, LinearPMap.map_zero, hψ0, sub_self, inner_zero_right,
      zero_sub, sub_zero, neg_eq_zero] at this
    exact this
  refine ⟨hid t ht, ?_⟩
  obtain ⟨-, du, -, -, -, b, -, -⟩ := hd t ht
  have hg : HasDerivWithinAt (fun s => ⟪(u s : Wt1), D.dt0 ψ⟫) ⟪u' t, D.dt0 ψ⟫ (Ici t) t := by
    simpa using du.inner ℝ (hasDerivWithinAt_const t (Ici t) (D.dt0 ψ))
  have hu' : ⟪u' t, D.dt0 ψ⟫ = 0 :=
    hasDerivWithinAt_Ici_eq_zero_of_eqOn ht.2 (fun s hs => hid s ⟨ht.1.trans hs.1, hs.2⟩) hg
  obtain ⟨hdψ, hdd⟩ := hD.2.1 ψ
  obtain ⟨hSψ, hanti⟩ := hD.2.2 ψ
  have hS : Q.π2 (D.S1 (D.dt0 ψ)) = 0 := by
    have e1 : D.S1 (D.dt0 ψ) = -D.d1 ⟨D.S0 ψ, hSψ⟩ := by rw [hanti, neg_neg]
    rw [e1, map_neg, ← Q.comm1 ⟨D.S0 ψ, hSψ⟩, neg_eq_zero]
    have e2 : (⟨Q.π1 (D.S0 ψ), Q.le1 (Q.π1_mem _)⟩ : D.d1.domain) = 0 := Subtype.ext hψ0
    rw [e2, LinearPMap.map_zero]
  have hb := b ⟨D.dt0 ψ, hdψ⟩ (Q.dt0_mem ψ hψ)
  change ⟪u' t, D.dt0 ψ⟫ + ⟪D.dt0 (φ t), D.dt0 ψ⟫ + ⟪M t, Q.π2 (D.S1 (D.dt0 ψ))⟫ +
    ⟪ρ t, D.dt1 ⟨D.dt0 ψ, hdψ⟩⟫ = ⟪f t, D.dt0 ψ⟫ at hb
  rw [hu', hS, hdd, inner_zero_right, inner_zero_right, add_zero, add_zero, zero_add] at hb
  rw [inner_sub_left, hb, sub_self]

/-- **(C1)–(C3) are necessary** for BGG data and `T > 0`. -/
theorem IsDiscreteWave.compatible (hD : D.IsBGG) {T : ℝ} (hT : 0 < T) {f : ℝ → Wt1}
    {σ : ℝ → D.d0.domain} {φ : ℝ → D.dt0.domain} {u : ℝ → D.dt1.domain} {M : ℝ → W2}
    {ρ : ℝ → Wt2} {lam : ℝ → W1} (h : Q.IsDiscreteWave T f σ φ u M ρ lam) :
    D.d0 (σ 0) = Q.π1 (D.S0 (φ 0)) ∧ ∀ ψ : D.dt0.domain, (ψ : Wt0) ∈ Q.Vt0 →
      Q.π1 (D.S0 ψ) = 0 → ⟪(u 0 : Wt1), D.dt0 ψ⟫ = 0 ∧ ⟪D.dt0 (φ 0) - f 0, D.dt0 ψ⟫ = 0 :=
  ⟨(h.2.2.2.2.1 0 ⟨le_rfl, hT.le⟩).2.2.2.2.2.2, fun _ hψ hψ0 =>
    h.inner_dt0_eq_zero hD ⟨le_rfl, hT⟩ hψ hψ0⟩

/-- **`φₕ`, `λₕ` are determined by `σₕ`, `uₕ` on `[0, T)`**, when `d̃⁰` is injective on `Ṽₕ⁰` and
`π¹S⁰` maps `Ṽₕ⁰` onto `Vₕ¹`: `λₕ` by `⟪λₕ, π¹S⁰ψ⟫ = ⟪uₕ, d̃ψ⟫` (the first equation at `τ = 0`),
and `φₕ` by `π¹S⁰φₕ = dσₕ` with (C3). -/
theorem IsDiscreteWave.phi_lam_eq (hD : D.IsBGG)
    (hinj : ∀ ψ : D.dt0.domain, (ψ : Wt0) ∈ Q.Vt0 → D.dt0 ψ = 0 → (ψ : Wt0) = 0)
    (hS : ∀ μ ∈ Q.V1, ∃ ψ : D.dt0.domain, (ψ : Wt0) ∈ Q.Vt0 ∧ Q.π1 (D.S0 ψ) = μ)
    {T : ℝ} {f : ℝ → Wt1} {σ σ₂ : ℝ → D.d0.domain} {φ φ₂ : ℝ → D.dt0.domain}
    {u u₂ : ℝ → D.dt1.domain} {M M₂ : ℝ → W2} {ρ ρ₂ : ℝ → Wt2} {lam lam₂ : ℝ → W1}
    (h1 : Q.IsDiscreteWave T f σ φ u M ρ lam) (h2 : Q.IsDiscreteWave T f σ₂ φ₂ u₂ M₂ ρ₂ lam₂)
    {t : ℝ} (ht : t ∈ Ico 0 T) (hσ : σ t = σ₂ t) (hu : u t = u₂ t) :
    φ t = φ₂ t ∧ lam t = lam₂ t := by
  have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
  obtain ⟨-, mφ, -, -, -, ml, k1⟩ := h1.2.2.2.2.1 t ht'
  obtain ⟨-, mφ₂, -, -, -, ml₂, k2⟩ := h2.2.2.2.2.1 t ht'
  constructor
  · have hδ : ((φ t - φ₂ t : D.dt0.domain) : Wt0) ∈ Q.Vt0 := Q.Vt0.sub_mem mφ mφ₂
    have hδ0 : Q.π1 (D.S0 (φ t - φ₂ t : D.dt0.domain)) = 0 := by
      rw [Submodule.coe_sub, map_sub, map_sub, ← k1, ← k2, hσ, sub_self]
    have c1 := (h1.inner_dt0_eq_zero hD ht hδ hδ0).2
    have c2 := (h2.inner_dt0_eq_zero hD ht hδ hδ0).2
    have e : D.dt0 (φ t - φ₂ t) = (D.dt0 (φ t) - f t) - (D.dt0 (φ₂ t) - f t) := by
      rw [LinearPMap.map_sub]; abel
    have hdd : ⟪D.dt0 (φ t - φ₂ t), D.dt0 (φ t - φ₂ t)⟫ = 0 := by
      calc ⟪D.dt0 (φ t - φ₂ t), D.dt0 (φ t - φ₂ t)⟫ =
          ⟪(D.dt0 (φ t) - f t) - (D.dt0 (φ₂ t) - f t), D.dt0 (φ t - φ₂ t)⟫ := by rw [← e]
        _ = 0 := by rw [inner_sub_left, c1, c2, sub_self]
    exact sub_eq_zero.1 (Subtype.ext (hinj _ hδ (inner_self_eq_zero.1 hdd)))
  · obtain ⟨-, -, -, -, -, σ', u', M', ρ', hd⟩ := h1
    obtain ⟨-, -, -, -, -, σ₂', u₂', M₂', ρ₂', hd₂⟩ := h2
    have hl : ∀ μ ∈ Q.V1, ⟪lam t - lam₂ t, μ⟫ = 0 := by
      intro μ hμ
      obtain ⟨ψ, hψ, rfl⟩ := hS μ hμ
      have a1 := (hd t ht).2.2.2.2.1 0 ψ Q.V0.zero_mem hψ
      have a2 := (hd₂ t ht).2.2.2.2.1 0 ψ Q.V0.zero_mem hψ
      simp only [ZeroMemClass.coe_zero, LinearPMap.map_zero, inner_zero_right, zero_sub,
        inner_neg_right, sub_neg_eq_add] at a1 a2
      rw [hu] at a1
      rw [inner_sub_left]
      linarith
    exact sub_eq_zero.1 (inner_self_eq_zero.1 (hl _ (Q.V1.sub_mem ml ml₂)))

/-! ### Existence: `Feec`'s solutions of (6.3) -/

variable (Q)

instance : Q.Vt1.HasOrthogonalProjection :=
  have := Q.fdt1
  have : CompleteSpace Q.Vt1 := FiniteDimensional.complete ℝ _
  inferInstance

/-- The orthogonal projection onto `Ṽₕ¹`, into `Feec`'s discrete space: the source of (6.3). -/
def srcH (hD : D.IsBGG) : Wt1 →L[ℝ] (Q.toDiscrete hD).Vt1h :=
  (Q.Vt1.starProjection.codRestrict D.dt1.domain fun x =>
    Q.let1 (Q.Vt1.starProjection_apply_mem x)).codRestrict (Q.toDiscrete hD).Vt1h fun x =>
      Q.Vt1.starProjection_apply_mem x

theorem inner_srcH (hD : D.IsBGG) (x : Wt1) (v : (Q.toDiscrete hD).Vt1h) :
    ⟪Q.srcH hD x, v⟫ = ⟪x, ((v : D.dt1.domain) : Wt1)⟫ := by
  change ⟪Q.Vt1.starProjection x, ((v : D.dt1.domain) : Wt1)⟫ = _
  rw [Submodule.inner_starProjection_left_eq_right, (Submodule.starProjection_eq_self_iff
    (K := Q.Vt1)).2 (show ((v : D.dt1.domain) : Wt1) ∈ Q.Vt1 from v.2)]

/-- **A solution of `Feec`'s (6.3) for `Q`, with the projected source, solves (6.5).** -/
theorem isDiscreteWave_ofDS (hD : D.IsBGG) {T : ℝ} {f : ℝ → Wt1}
    (s : Feec.BGG.DiscreteSolution (Q.toDiscrete hD).toSegmentH T fun t => Q.srcH hD (f t)) :
    Q.IsDiscreteWave T f (fun t => (s.σ t : D.d0.domain)) (fun t => (s.φ t : D.dt0.domain))
      (fun t => (s.u t : D.dt1.domain)) (fun t => (s.M t : W2)) (fun t => (s.ρ t : Wt2))
      (fun t => ((s.lam t : D.d1.domain) : W1)) := by
  set L0 : (Q.toDiscrete hD).V0h →L[ℝ] W0 :=
    D.d0.domain.subtypeL.comp (Q.toDiscrete hD).V0h.subtypeL
  set L1 : (Q.toDiscrete hD).Vt1h →L[ℝ] Wt1 :=
    D.dt1.domain.subtypeL.comp (Q.toDiscrete hD).Vt1h.subtypeL
  refine ⟨L0.continuous.comp_continuousOn s.cσ, L1.continuous.comp_continuousOn s.cu,
    continuous_subtype_val.comp_continuousOn s.cM, continuous_subtype_val.comp_continuousOn s.cρ,
    fun t ht => ⟨(s.σ t).2, (s.φ t).2, (s.u t).2, (s.M t).2, (s.ρ t).2, (s.lam t).2, ?_⟩,
    fun t => L0 (s.σ' t), fun t => L1 (s.u' t), fun t => (s.M' t : W2), fun t => (s.ρ' t : Wt2),
    fun t ht => ⟨L0.hasFDerivAt.comp_hasDerivWithinAt t (s.dσ t ht),
      L1.hasFDerivAt.comp_hasDerivWithinAt t (s.du t ht),
      (Q.toDiscrete hD).W2h.subtypeL.hasFDerivAt.comp_hasDerivWithinAt t (s.dM t ht),
      (Q.toDiscrete hD).Wt2h.subtypeL.hasFDerivAt.comp_hasDerivWithinAt t (s.dρ t ht),
      fun τ ψ hτ hψ => s.ea t (Ico_subset_Icc_self ht) ⟨τ, hτ⟩ ⟨ψ, hψ⟩,
      fun v hv => (s.eb t ht ⟨v, hv⟩).trans (Q.inner_srcH hD _ _), fun z hz => ?_, fun z hz => ?_⟩⟩
  · exact congrArg (fun x : (Q.toDiscrete hD).V1h => ((x : D.d1.domain) : W1)) (s.constraint ht)
  · exact sub_eq_zero.1 (s.ec t ht ⟨z, hz⟩)
  · exact sub_eq_zero.1 (s.ed t ht ⟨z, hz⟩)

theorem toSegmentH_dt0_injective (hD : D.IsBGG)
    (hinj : ∀ ψ : D.dt0.domain, (ψ : Wt0) ∈ Q.Vt0 → D.dt0 ψ = 0 → (ψ : Wt0) = 0) :
    Function.Injective (Q.toDiscrete hD).toSegmentH.dt0 := by
  intro a b hab
  have h : D.dt0 ((a : D.dt0.domain) - b) = 0 := by
    rw [LinearPMap.map_sub, sub_eq_zero]
    exact congrArg (fun x : (Q.toDiscrete hD).Vt1h => ((x : D.dt1.domain) : Wt1)) hab
  have := hinj _ (Q.Vt0.sub_mem a.2 b.2) h
  rw [Submodule.coe_sub, sub_eq_zero] at this
  exact Subtype.ext (Subtype.ext this)

theorem toSegmentH_S0_surjective (hD : D.IsBGG)
    (hS : ∀ μ ∈ Q.V1, ∃ ψ : D.dt0.domain, (ψ : Wt0) ∈ Q.Vt0 ∧ Q.π1 (D.S0 ψ) = μ) :
    Function.Surjective (Q.toDiscrete hD).toSegmentH.S0 := by
  intro μ
  obtain ⟨ψ, hψ, e⟩ := hS ((μ : D.d1.domain) : W1) μ.2
  exact ⟨⟨ψ, hψ⟩, Subtype.ext (Subtype.ext e)⟩

/-- **Well-posedness of (6.5)** (Prop 6.2, adapted): for BGG data, `d̃⁰` injective on `Ṽₕ⁰` and
`π¹S⁰` onto `Vₕ¹`, `T > 0` and `f` continuous on `[0, T]`, (6.5) has a solution from dynamic data
iff (C2), from full data iff (C1)–(C3), and `φₕ`, `λₕ` are determined on `[0, T)`. -/
theorem wellPosed_of (hD : D.IsBGG)
    (hinj : ∀ ψ : D.dt0.domain, (ψ : Wt0) ∈ Q.Vt0 → D.dt0 ψ = 0 → (ψ : Wt0) = 0)
    (hS : ∀ μ ∈ Q.V1, ∃ ψ : D.dt0.domain, (ψ : Wt0) ∈ Q.Vt0 ∧ Q.π1 (D.S0 ψ) = μ)
    {T : ℝ} (hT : 0 < T) {f : ℝ → Wt1} (hf : ContinuousOn f (Icc 0 T)) :
    (∀ (σ₀ : D.d0.domain) (u₀ : D.dt1.domain) M₀ ρ₀, (σ₀ : W0) ∈ Q.V0 → (u₀ : Wt1) ∈ Q.Vt1 →
        M₀ ∈ Q.V2 → ρ₀ ∈ Q.Vt2 →
        ((∃ σ φ u M ρ lam, Q.IsDiscreteWave T f σ φ u M ρ lam ∧ σ 0 = σ₀ ∧ u 0 = u₀ ∧
          M 0 = M₀ ∧ ρ 0 = ρ₀) ↔ ∀ ψ : D.dt0.domain, (ψ : Wt0) ∈ Q.Vt0 →
            Q.π1 (D.S0 ψ) = 0 → ⟪(u₀ : Wt1), D.dt0 ψ⟫_ℝ = 0) ∧
        ∀ φ₀ : D.dt0.domain, (φ₀ : Wt0) ∈ Q.Vt0 →
          ((∃ σ φ u M ρ lam, Q.IsDiscreteWave T f σ φ u M ρ lam ∧ σ 0 = σ₀ ∧ φ 0 = φ₀ ∧
            u 0 = u₀ ∧ M 0 = M₀ ∧ ρ 0 = ρ₀) ↔ D.d0 σ₀ = Q.π1 (D.S0 φ₀) ∧
            ∀ ψ : D.dt0.domain, (ψ : Wt0) ∈ Q.Vt0 → Q.π1 (D.S0 ψ) = 0 →
              ⟪(u₀ : Wt1), D.dt0 ψ⟫_ℝ = 0 ∧ ⟪D.dt0 φ₀ - f 0, D.dt0 ψ⟫_ℝ = 0)) ∧
      ∀ σ φ u M ρ lam σ' φ' u' M' ρ' lam', Q.IsDiscreteWave T f σ φ u M ρ lam →
        Q.IsDiscreteWave T f σ' φ' u' M' ρ' lam' → σ 0 = σ' 0 → u 0 = u' 0 → M 0 = M' 0 →
        ρ 0 = ρ' 0 → ∀ t ∈ Ico 0 T, φ t = φ' t ∧ lam t = lam' t := by
  have := Q.fd0; have := Q.fd1; have := Q.fd2; have := Q.fdt0; have := Q.fdt1; have := Q.fdt2
  have : FiniteDimensional ℝ (Q.toDiscrete hD).V0h := finiteDimensional_comap _ _
  have : FiniteDimensional ℝ (Q.toDiscrete hD).V1h := finiteDimensional_comap _ _
  have : FiniteDimensional ℝ (Q.toDiscrete hD).Vt0h := finiteDimensional_comap _ _
  have : FiniteDimensional ℝ (Q.toDiscrete hD).Vt1h := finiteDimensional_comap _ _
  have : FiniteDimensional ℝ (Q.toDiscrete hD).W2h := Q.fd2
  have : FiniteDimensional ℝ (Q.toDiscrete hD).Wt2h := Q.fdt2
  have hdinj := Q.toSegmentH_dt0_injective hD hinj
  have hS' := Q.toSegmentH_S0_surjective hD hS
  have hfH : ContinuousOn (fun t => Q.srcH hD (f t)) (Icc 0 T) :=
    (Q.srcH hD).continuous.comp_continuousOn hf
  -- `S₀,ₕψ = 0` in `Feec`'s segment is `π¹S⁰ψ = 0`
  have hker : ∀ ψ : (Q.toDiscrete hD).Vt0h, (Q.toDiscrete hD).toSegmentH.S0 ψ = 0 →
      Q.π1 (D.S0 (ψ : D.dt0.domain)) = 0 := fun ψ hψ =>
    congrArg (fun x : (Q.toDiscrete hD).V1h => ((x : D.d1.domain) : W1)) hψ
  refine ⟨fun σ₀ u₀ M₀ ρ₀ hσ₀ hu₀ hM₀ hρ₀ => ⟨⟨?_, fun hC2 => ?_⟩, fun φ₀ hφ₀ => ⟨?_, ?_⟩⟩,
    fun σ φ u M ρ lam σ' φ' u' M' ρ' lam' h1 h2 e0 e1 e2 e3 t ht => ?_⟩
  · rintro ⟨σ, φ, u, M, ρ, lam, h, rfl, rfl, -, -⟩ ψ hψ hψ0
    exact ((h.compatible hD hT).2 ψ hψ hψ0).1
  · obtain ⟨s, h1, h2, h3, h4⟩ := (Feec.BGG.exists_discreteSolution_iff_compatible_u hT hdinj hS'
      hfH ⟨σ₀, hσ₀⟩ ⟨u₀, hu₀⟩ ⟨M₀, hM₀⟩ ⟨ρ₀, hρ₀⟩).2 fun ψ hψ => hC2 ψ ψ.2 (hker ψ hψ)
    exact ⟨_, _, _, _, _, _, Q.isDiscreteWave_ofDS hD s, by rw [h1], by rw [h2], by rw [h3],
      by rw [h4]⟩
  · rintro ⟨σ, φ, u, M, ρ, lam, h, rfl, rfl, rfl, -, -⟩
    exact h.compatible hD hT
  · rintro ⟨hC1, hC⟩
    obtain ⟨s, h1, h2, h3, h4, h5⟩ := Feec.BGG.exists_discreteSolution_of_continuousOn hdinj hS'
      hT.le hfH (σ₀ := ⟨σ₀, hσ₀⟩) (φ₀ := ⟨φ₀, hφ₀⟩) (u₀ := ⟨u₀, hu₀⟩) (M₀ := ⟨M₀, hM₀⟩)
      (ρ₀ := ⟨ρ₀, hρ₀⟩) (Subtype.ext (Subtype.ext hC1)) (fun ψ hψ => (hC ψ ψ.2 (hker ψ hψ)).1)
      fun ψ hψ => by
        have h := (hC ψ ψ.2 (hker ψ hψ)).2
        rw [inner_sub_left, sub_eq_zero] at h
        exact h.trans (Q.inner_srcH hD (f 0) ((Q.toDiscrete hD).toSegmentH.dt0 ψ)).symm
    exact ⟨_, _, _, _, _, _, Q.isDiscreteWave_ofDS hD s, by rw [h1], by rw [h2], by rw [h3],
      by rw [h4], by rw [h5]⟩
  · obtain ⟨hσ, hu, -, -⟩ := IsDiscreteWave.eq_of_eq Q h1 h2 e0 e1 e2 e3 t (Ico_subset_Icc_self ht)
    exact h1.phi_lam_eq hD hinj hS h2 ht hσ hu

end FEEC.WeakSymmetryData.Discretization
