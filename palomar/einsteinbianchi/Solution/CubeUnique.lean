module

public import Solution.CubeWave

/-!
# Uniqueness for the semi-discrete problem (6.5) on the cube

A solution of (6.5) of the challenge for `cubeQ` on `[0, T]` is, on every `[0, T']`, `T' < T`, a
`Feec` semi-discrete solution for `cubeWave` (`exists_toDS`: compose with the projections onto the
discrete spaces, which fix the solution, and identify the derivatives through their uniqueness on
`[t, T)`), so two solutions with the same `(σ, u, M, ρ)(0)` agree
(`Feec.BGG.DiscreteSolution.unique`), on `[0, T)` and, by continuity, at `T`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2, Prop 6.2

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 8000000

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

section Unique

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) (N : ℕ)

/-- The projection onto `Vₕ⁰` as a map into `Feec`'s discrete space. -/
def fe0 : W0 →L[ℝ] (cubeFEM hT hB N).V0h :=
  ((cubeQ hT hB N).π0.codRestrict D0.domain fun x =>
    (cubeQ hT hB N).le0 ((cubeQ hT hB N).π0_mem x)).codRestrict (cubeFEM hT hB N).V0h
    fun x => (cubeQ hT hB N).π0_mem x

/-- The projection onto `Vₕ¹`. -/
def fe1 : W1 →L[ℝ] (cubeFEM hT hB N).V1h :=
  ((cubeQ hT hB N).π1.codRestrict D1.domain fun x =>
    (cubeQ hT hB N).le1 ((cubeQ hT hB N).π1_mem x)).codRestrict (cubeFEM hT hB N).V1h
    fun x => (cubeQ hT hB N).π1_mem x

/-- The projection onto `Vₕ²`. -/
def fe2 : W2 →L[ℝ] (cubeFEM hT hB N).W2h :=
  (cubeQ hT hB N).π2.codRestrict _ fun x => (cubeQ hT hB N).π2_mem x

/-- The projection onto `Ṽₕ⁰`. -/
def fet0 : Wv W0 →L[ℝ] (cubeFEM hT hB N).Vt0h :=
  (e0.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((cubeQ hT hB N).πt0.codRestrict (vecOpC (n := 3) D0).domain fun x =>
      (cubeQ hT hB N).let0 ((cubeQ hT hB N).πt0_mem x))).codRestrict (cubeFEM hT hB N).Vt0h
    fun x a => (cubeQ hT hB N).πt0_mem x a

/-- The projection onto `Ṽₕ¹`. -/
def fet1 : Wv W1 →L[ℝ] (cubeFEM hT hB N).Vt1h :=
  (e1.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((cubeQ hT hB N).πt1.codRestrict (vecOpC (n := 3) D1).domain fun x =>
      (cubeQ hT hB N).let1 ((cubeQ hT hB N).πt1_mem x))).codRestrict (cubeFEM hT hB N).Vt1h
    fun x a => (cubeQ hT hB N).πt1_mem x a

/-- The projection onto `Ṽₕ²`. -/
def fet2 : Wv W2 →L[ℝ] (cubeFEM hT hB N).Wt2h :=
  (cubeQ hT hB N).πt2.codRestrict _ fun x => (cubeQ hT hB N).πt2_mem x

/-- A derivative of a path in a closed subspace `V`, fixed by a bounded projection `π` onto it,
lies in `V`: `π σ = σ` near `t` within `[t, T)`, so `π σ'(t) = σ'(t)`. -/
theorem proj_deriv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (π : E →L[ℝ] E)
    {V : Set E} (hπ : ∀ x ∈ V, π x = x) {T t : ℝ} (ht : t ∈ Ico 0 T) {x : ℝ → E} {x' : E}
    (hx : ∀ s ∈ Icc 0 T, x s ∈ V) (hd : HasDerivWithinAt x x' (Ici t) t) : π x' = x' := by
  have h1 : HasDerivWithinAt (fun s => π (x s)) (π x') (Ici t) t :=
    π.hasFDerivAt.comp_hasDerivWithinAt t hd
  have hev : (fun s => π (x s)) =ᶠ[𝓝[Ici t] t] x := by
    filter_upwards [Ico_mem_nhdsGE ht.2] with s hs
    exact hπ _ (hx s ⟨ht.1.trans hs.1, hs.2.le⟩)
  have h2 := h1.congr_of_eventuallyEq hev.symm (hπ _ (hx t (Ico_subset_Icc_self ht))).symm
  exact (uniqueDiffWithinAt_Ici t).eq_deriv _ h2 hd

/-- **A solution of (6.5) of the challenge is, on `[0, T']`, a solution of `Feec`'s (6.3).** -/
theorem exists_toDS {T T' : ℝ} (hTT : T' < T) {f : ℝ → Wv W1} {σ : ℝ → 𝒟.d0.domain}
    {φ : ℝ → 𝒟.dt0.domain} {u : ℝ → 𝒟.dt1.domain} {M : ℝ → W2} {ρ : ℝ → Wv W2} {lam : ℝ → W1}
    (hw : (cubeQ hT hB N).IsDiscreteWave T f σ φ u M ρ lam) :
    ∃ s : @Feec.BGG.DiscreteSolution (cubeFEM hT hB N).V0h (cubeFEM hT hB N).V1h
      (cubeFEM hT hB N).W2h (cubeFEM hT hB N).Vt0h (cubeFEM hT hB N).Vt1h (cubeFEM hT hB N).Wt2h
      _ _ _ _ _ _ _ _ _ _ _ _ (cubeWave hT hB N) T' (cubeSource hT hB N f),
      ∀ t, s.σ t = fe0 hT hB N (σ t) ∧ s.u t = fet1 hT hB N (u t) ∧ s.M t = fe2 hT hB N (M t) ∧
        s.ρ t = fet2 hT hB N (ρ t) ∧ s.lam t = fe1 hT hB N (lam t) ∧
        s.φ t = fet0 hT hB N (φ t) := by
  obtain ⟨hcσ, hcu, hcM, hcρ, hmem, σ', u', M', ρ', hd⟩ := hw
  have hsub : Icc 0 T' ⊆ Icc 0 T := Icc_subset_Icc_right hTT.le
  have hIco : ∀ t ∈ Ico 0 T', t ∈ Ico 0 T := fun t ht => ⟨ht.1, ht.2.trans hTT⟩
  have hIcc : ∀ t ∈ Icc 0 T', t ∈ Ico 0 T := fun t ht => ⟨ht.1, ht.2.trans_lt hTT⟩
  -- the projections fix the solution and its derivatives
  have pσ : ∀ t ∈ Icc 0 T, (cubeQ hT hB N).π0 (σ t) = σ t := fun t ht =>
    (cubeQ hT hB N).π0_id _ (hmem t ht).1
  have pφ : ∀ t ∈ Icc 0 T, (cubeQ hT hB N).πt0 (φ t) = φ t := fun t ht =>
    (cubeQ hT hB N).πt0_id _ (hmem t ht).2.1
  have pu : ∀ t ∈ Icc 0 T, (cubeQ hT hB N).πt1 (u t) = u t := fun t ht =>
    (cubeQ hT hB N).πt1_id _ (hmem t ht).2.2.1
  have pM : ∀ t ∈ Icc 0 T, (cubeQ hT hB N).π2 (M t) = M t := fun t ht =>
    (cubeQ hT hB N).π2_id _ (hmem t ht).2.2.2.1
  have pρ : ∀ t ∈ Icc 0 T, (cubeQ hT hB N).πt2 (ρ t) = ρ t := fun t ht =>
    (cubeQ hT hB N).πt2_id _ (hmem t ht).2.2.2.2.1
  have pl : ∀ t ∈ Icc 0 T, (cubeQ hT hB N).π1 (lam t) = lam t := fun t ht =>
    (cubeQ hT hB N).π1_id _ (hmem t ht).2.2.2.2.2.1
  have pσ' : ∀ t ∈ Ico 0 T, (cubeQ hT hB N).π0 (σ' t) = σ' t := fun t ht =>
    proj_deriv_eq _ (fun x hx => (cubeQ hT hB N).π0_id x hx) ht
      (x := fun s => (σ s : W0)) (fun s hs => (hmem s hs).1) (hd t ht).1
  have pu' : ∀ t ∈ Ico 0 T, (cubeQ hT hB N).πt1 (u' t) = u' t := fun t ht =>
    proj_deriv_eq _ (fun x hx => (cubeQ hT hB N).πt1_id x hx) ht
      (x := fun s => (u s : Wv W1)) (fun s hs => (hmem s hs).2.2.1) (hd t ht).2.1
  have pM' : ∀ t ∈ Ico 0 T, (cubeQ hT hB N).π2 (M' t) = M' t := fun t ht =>
    proj_deriv_eq _ (fun x hx => (cubeQ hT hB N).π2_id x hx) ht (x := M)
      (fun s hs => (hmem s hs).2.2.2.1) (hd t ht).2.2.1
  have pρ' : ∀ t ∈ Ico 0 T, (cubeQ hT hB N).πt2 (ρ' t) = ρ' t := fun t ht =>
    proj_deriv_eq _ (fun x hx => (cubeQ hT hB N).πt2_id x hx) ht (x := ρ)
      (fun s hs => (hmem s hs).2.2.2.2.1) (hd t ht).2.2.2.1
  -- the projected path agrees with the solution
  have qσ : ∀ t ∈ Icc 0 T, ((fe0 hT hB N (σ t) : U0) : 𝒟.d0.domain) = σ t := fun t ht =>
    Subtype.ext (pσ t ht)
  have qσ' : ∀ t ∈ Ico 0 T, (((fe0 hT hB N (σ' t) : U0) : W0)) = σ' t := fun t ht => pσ' t ht
  have qφ : ∀ t ∈ Icc 0 T, ((fet0 hT hB N (φ t) : Wv U0)) = e0 (φ t) := fun t ht =>
    congrArg e0 (Subtype.ext (pφ t ht) : (⟨_, _⟩ : 𝒟.dt0.domain) = φ t)
  have qu : ∀ t ∈ Icc 0 T, ((fet1 hT hB N (u t) : Wv U1)) = e1 (u t) := fun t ht =>
    congrArg e1 (Subtype.ext (pu t ht) : (⟨_, _⟩ : 𝒟.dt1.domain) = u t)
  have qu' : ∀ t ∈ Ico 0 T, incl1 ((fet1 hT hB N (u' t) : Wv U1)) = u' t := fun t ht => pu' t ht
  have ql : ∀ t ∈ Icc 0 T, (((fe1 hT hB N (lam t) : U1) : W1)) = lam t := fun t ht => pl t ht
  refine ⟨⟨fun t => fe0 hT hB N (σ t), fun t => fet0 hT hB N (φ t), fun t => fet1 hT hB N (u t),
    fun t => fe2 hT hB N (M t), fun t => fet2 hT hB N (ρ t), fun t => fe1 hT hB N (lam t),
    fun t => fe0 hT hB N (σ' t), fun t => fet1 hT hB N (u' t), fun t => fe2 hT hB N (M' t),
    fun t => fet2 hT hB N (ρ' t),
    (fe0 hT hB N).continuous.comp_continuousOn (hcσ.mono hsub),
    (fet1 hT hB N).continuous.comp_continuousOn (hcu.mono hsub),
    (fe2 hT hB N).continuous.comp_continuousOn (hcM.mono hsub),
    (fet2 hT hB N).continuous.comp_continuousOn (hcρ.mono hsub),
    fun t ht => hasDerivWithinAt_subtype _ (hasDerivWithinAt_subtype _
      ((cubeQ hT hB N).π0.hasFDerivAt.comp_hasDerivWithinAt t (hd t (hIco t ht)).1)),
    fun t ht => hasDerivWithinAt_subtype _ (hasDerivWithinAt_piSubtype D1.domain
      (f := fun r => (fet1 hT hB N (u r) : Wv U1)) (f' := (fet1 hT hB N (u' t) : Wv U1))
      ((cubeQ hT hB N).πt1.hasFDerivAt.comp_hasDerivWithinAt t (hd t (hIco t ht)).2.1)),
    fun t ht => hasDerivWithinAt_subtype _
      ((cubeQ hT hB N).π2.hasFDerivAt.comp_hasDerivWithinAt t (hd t (hIco t ht)).2.2.1),
    fun t ht => hasDerivWithinAt_subtype _
      ((cubeQ hT hB N).πt2.hasFDerivAt.comp_hasDerivWithinAt t (hd t (hIco t ht)).2.2.2.1),
    fun t ht τ ψ => ?_, fun t ht v => ?_, fun t ht z => ?_, fun t ht z => ?_, fun t ht z => ?_⟩,
    fun t => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · have ht' := hIcc t ht
    have h := (hd t ht').2.2.2.2.1 (τ : U0) (e0.symm (ψ : Wv U0)) τ.2 ψ.2
    have hu : ((u t : 𝒟.dt1.domain) : Wv W1) = incl1 (fet1 hT hB N (u t) : Wv U1) := by
      rw [qu t (Ico_subset_Icc_self ht'), incl1_e1]
    rw [← qσ' t ht', ← ql t (Ico_subset_Icc_self ht'), hu, dt0_e0_symm, ← inner_wv_U1] at h
    exact h
  · have ht' := hIco t ht
    have h := (hd t ht').2.2.2.2.2.1 (ofWv1 (v : Wv U1)) fun a => v.2 a
    have hφ' : 𝒟.dt0 (φ t) = incl1 (bggSegment.dt0 (fet0 hT hB N (φ t) : Wv U0)) := by
      rw [qφ t (Ico_subset_Icc_self ht'), dt0_e0]
    have hM : M t = (fe2 hT hB N (M t) : W2) := (pM t (Ico_subset_Icc_self ht')).symm
    have hρ : ρ t = (fet2 hT hB N (ρ t) : Wv W2) := (pρ t (Ico_subset_Icc_self ht')).symm
    rw [coe_ofWv1, ← qu' t ht', hφ', ← inner_wv_U1, ← inner_wv_U1, hM, hρ,
      ← inner_cubeSource] at h
    exact h
  · have ht' := hIco t ht
    have h := (hd t ht').2.2.2.2.2.2.1 z z.2
    have hS : 𝒟.S1 (u t) = bggSegment.S1 (fet1 hT hB N (u t) : Wv U1) := by
      rw [qu t (Ico_subset_Icc_self ht'), S1_e1]
    rw [← pM' t ht', hS] at h
    exact sub_eq_zero.2 h
  · have ht' := hIco t ht
    have h := (hd t ht').2.2.2.2.2.2.2 z fun a => z.2 a
    have hS : 𝒟.dt1 (u t) = bggSegment.dt1 (fet1 hT hB N (u t) : Wv U1) := by
      rw [qu t (Ico_subset_Icc_self ht'), dt1_e1]
    rw [← pρ' t ht', hS] at h
    exact sub_eq_zero.2 h
  · have ht' := hsub ht
    have hc := (hmem t ht').2.2.2.2.2.2
    have e : (cubeWave hT hB N).d0 (fe0 hT hB N (σ t)) -
        (cubeWave hT hB N).S0 (fet0 hT hB N (φ t)) = 0 := by
      refine Subtype.ext (Subtype.ext ?_)
      change D0 (fe0 hT hB N (σ t) : U0) - (hT.proj N).π 1 (wsL2 (Ω := cubeDomain 3) 0
        (incl0 (fet0 hT hB N (φ t) : Wv U0))) = 0
      rw [qσ t ht', qφ t ht', incl0_e0]
      exact sub_eq_zero.2 hc
    rw [e]; exact inner_zero_left ((z : U1) : W1)

theorem fe0_inj {x y : W0} (hx : x ∈ (cubeQ hT hB N).V0) (hy : y ∈ (cubeQ hT hB N).V0)
    (h : fe0 hT hB N x = fe0 hT hB N y) : x = y := by
  have := congrArg (fun z : (cubeFEM hT hB N).V0h => ((z : U0) : W0)) h
  change (cubeQ hT hB N).π0 x = (cubeQ hT hB N).π0 y at this
  rwa [(cubeQ hT hB N).π0_id x hx, (cubeQ hT hB N).π0_id y hy] at this

theorem fe1_inj {x y : W1} (hx : x ∈ (cubeQ hT hB N).V1) (hy : y ∈ (cubeQ hT hB N).V1)
    (h : fe1 hT hB N x = fe1 hT hB N y) : x = y := by
  have := congrArg (fun z : (cubeFEM hT hB N).V1h => ((z : U1) : W1)) h
  change (cubeQ hT hB N).π1 x = (cubeQ hT hB N).π1 y at this
  rwa [(cubeQ hT hB N).π1_id x hx, (cubeQ hT hB N).π1_id y hy] at this

theorem fe2_inj {x y : W2} (hx : x ∈ (cubeQ hT hB N).V2) (hy : y ∈ (cubeQ hT hB N).V2)
    (h : fe2 hT hB N x = fe2 hT hB N y) : x = y := by
  have := congrArg (fun z : (cubeFEM hT hB N).W2h => (z : W2)) h
  change (cubeQ hT hB N).π2 x = (cubeQ hT hB N).π2 y at this
  rwa [(cubeQ hT hB N).π2_id x hx, (cubeQ hT hB N).π2_id y hy] at this

theorem fet0_inj {x y : Wv W0} (hx : x ∈ (cubeQ hT hB N).Vt0) (hy : y ∈ (cubeQ hT hB N).Vt0)
    (h : fet0 hT hB N x = fet0 hT hB N y) : x = y := by
  have := congrArg (fun z : (cubeFEM hT hB N).Vt0h => incl0 (z : Wv U0)) h
  change (cubeQ hT hB N).πt0 x = (cubeQ hT hB N).πt0 y at this
  rwa [(cubeQ hT hB N).πt0_id x hx, (cubeQ hT hB N).πt0_id y hy] at this

theorem fet1_inj {x y : Wv W1} (hx : x ∈ (cubeQ hT hB N).Vt1) (hy : y ∈ (cubeQ hT hB N).Vt1)
    (h : fet1 hT hB N x = fet1 hT hB N y) : x = y := by
  have := congrArg (fun z : (cubeFEM hT hB N).Vt1h => incl1 (z : Wv U1)) h
  change (cubeQ hT hB N).πt1 x = (cubeQ hT hB N).πt1 y at this
  rwa [(cubeQ hT hB N).πt1_id x hx, (cubeQ hT hB N).πt1_id y hy] at this

theorem fet2_inj {x y : Wv W2} (hx : x ∈ (cubeQ hT hB N).Vt2) (hy : y ∈ (cubeQ hT hB N).Vt2)
    (h : fet2 hT hB N x = fet2 hT hB N y) : x = y := by
  have := congrArg (fun z : (cubeFEM hT hB N).Wt2h => (z : Wv W2)) h
  change (cubeQ hT hB N).πt2 x = (cubeQ hT hB N).πt2 y at this
  rwa [(cubeQ hT hB N).πt2_id x hx, (cubeQ hT hB N).πt2_id y hy] at this

/-- **Uniqueness for (6.5) on the cube.** -/
theorem cube_wave_unique {T : ℝ} {f : ℝ → Wv W1} {σ σ₂ : ℝ → 𝒟.d0.domain}
    {φ φ₂ : ℝ → 𝒟.dt0.domain} {u u₂ : ℝ → 𝒟.dt1.domain} {M M₂ : ℝ → W2} {ρ ρ₂ : ℝ → Wv W2}
    {lam lam₂ : ℝ → W1} (hT0 : 0 < T) (h1 : (cubeQ hT hB N).IsDiscreteWave T f σ φ u M ρ lam)
    (h2 : (cubeQ hT hB N).IsDiscreteWave T f σ₂ φ₂ u₂ M₂ ρ₂ lam₂) (e0' : σ 0 = σ₂ 0)
    (e1' : u 0 = u₂ 0) (e2' : M 0 = M₂ 0) (e3' : ρ 0 = ρ₂ 0) :
    (∀ t ∈ Icc 0 T, σ t = σ₂ t ∧ u t = u₂ t ∧ M t = M₂ t ∧ ρ t = ρ₂ t) ∧
      ∀ t ∈ Ico 0 T, φ t = φ₂ t ∧ lam t = lam₂ t := by
  have key : ∀ t ∈ Ico 0 T, σ t = σ₂ t ∧ u t = u₂ t ∧ M t = M₂ t ∧ ρ t = ρ₂ t ∧ φ t = φ₂ t ∧
      lam t = lam₂ t := by
    intro t ht
    have hT' : (t + T) / 2 < T := by linarith [ht.2]
    have htT' : t < (t + T) / 2 := by linarith [ht.2]
    obtain ⟨s1, hs1⟩ := exists_toDS hT hB N hT' h1
    obtain ⟨s2, hs2⟩ := exists_toDS hT hB N hT' h2
    have hu := Feec.BGG.DiscreteSolution.unique s1 s2 (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N)
      ⟨by rw [(hs1 0).1, (hs2 0).1, e0'], by rw [(hs1 0).2.1, (hs2 0).2.1, e1'],
        by rw [(hs1 0).2.2.1, (hs2 0).2.2.1, e2'], by rw [(hs1 0).2.2.2.1, (hs2 0).2.2.2.1, e3']⟩
    obtain ⟨a, b, c, d, e⟩ := hu.1 t ⟨ht.1, htT'.le⟩
    have g := hu.2 t ⟨ht.1, htT'⟩
    have m1 := h1.2.2.2.2.1 t (Ico_subset_Icc_self ht)
    have m2 := h2.2.2.2.2.1 t (Ico_subset_Icc_self ht)
    rw [(hs1 t).1, (hs2 t).1] at a
    rw [(hs1 t).2.1, (hs2 t).2.1] at b
    rw [(hs1 t).2.2.1, (hs2 t).2.2.1] at c
    rw [(hs1 t).2.2.2.1, (hs2 t).2.2.2.1] at d
    rw [(hs1 t).2.2.2.2.1, (hs2 t).2.2.2.2.1] at e
    rw [(hs1 t).2.2.2.2.2, (hs2 t).2.2.2.2.2] at g
    exact ⟨Subtype.ext (fe0_inj hT hB N m1.1 m2.1 a),
      Subtype.ext (fet1_inj hT hB N m1.2.2.1 m2.2.2.1 b),
      fe2_inj hT hB N m1.2.2.2.1 m2.2.2.2.1 c, fet2_inj hT hB N m1.2.2.2.2.1 m2.2.2.2.2.1 d,
      Subtype.ext (fet0_inj hT hB N m1.2.1 m2.2.1 g),
      fe1_inj hT hB N m1.2.2.2.2.2.1 m2.2.2.2.2.2.1 e⟩
  have hcl : Icc 0 T ⊆ closure (Ico 0 T) := (closure_Ico hT0.ne).symm.subset
  have eσ : EqOn (fun t => (σ t : W0)) (fun t => (σ₂ t : W0)) (Icc 0 T) :=
    EqOn.of_subset_closure (fun t ht => congrArg Subtype.val (key t ht).1) h1.1 h2.1
      Ico_subset_Icc_self hcl
  have eu : EqOn (fun t => (u t : Wv W1)) (fun t => (u₂ t : Wv W1)) (Icc 0 T) :=
    EqOn.of_subset_closure (fun t ht => congrArg Subtype.val (key t ht).2.1) h1.2.1 h2.2.1
      Ico_subset_Icc_self hcl
  have eM : EqOn M M₂ (Icc 0 T) :=
    EqOn.of_subset_closure (fun t ht => (key t ht).2.2.1) h1.2.2.1 h2.2.2.1 Ico_subset_Icc_self hcl
  have eρ : EqOn ρ ρ₂ (Icc 0 T) :=
    EqOn.of_subset_closure (fun t ht => (key t ht).2.2.2.1) h1.2.2.2.1 h2.2.2.2.1
      Ico_subset_Icc_self hcl
  exact ⟨fun t ht => ⟨Subtype.ext (eσ ht), Subtype.ext (eu ht), eM ht, eρ ht⟩,
    fun t ht => ⟨(key t ht).2.2.2.2.1, (key t ht).2.2.2.2.2⟩⟩

end Unique

end FEEC
