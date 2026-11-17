module

public import Solution.Abstract
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Energy identities for the semi-discrete problem (6.5)

For any data `D` and any discretization `Q`, two solutions of (6.5) with the same source and
the same `(σₕ, uₕ, Mₕ, ρₕ)(0)` agree on `[0, T]` (`IsDiscreteWave.eq_of_eq`): the energy
`‖δσ‖² + ‖δu‖² + ‖δM‖² + ‖δρ‖²` of their difference is constant, the four equations of (6.5)
tested with the difference itself cancelling pairwise.

Without source, the discrete Gauss law propagates when `D` satisfies `IsBGG`
(`IsDiscreteWave.isGauss`): with `Z = span {d̃ψ | (τ, ψ) ∈ Vₕ⁰ × Ṽₕ⁰, dτ = π¹S⁰ψ}` and `P` the
orthogonal projection onto `Z`, the quantity `‖σₕ‖² + ‖P uₕ‖²` is constant. Indeed
`⟪σₕ', σₕ⟫ = ⟪uₕ, d̃φₕ⟫` (first equation at `(σₕ, φₕ)`) and `⟪uₕ', z⟫ = -⟪d̃φₕ, z⟫` on `Z` (second
equation at `v = d̃ψ`: `d̃d̃ψ = 0` and `π²S¹d̃ψ = -π²dS⁰ψ = -d π¹S⁰ψ = -d dτ = 0`), while
`d̃φₕ ∈ Z`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2, Prop 6.2, (6.5)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set

@[expose] public noncomputable section

namespace FEEC.WeakSymmetryData.Discretization

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] {D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2} (Q : D.Discretization)

/-- A vector orthogonal to a set is orthogonal to its span. -/
theorem inner_eq_zero_of_mem_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : Set E} {w : E} (h : ∀ x ∈ s, ⟪w, x⟫ = 0) {x : E} (hx : x ∈ Submodule.span ℝ s) :
    ⟪w, x⟫ = 0 :=
  (Submodule.span_le (p := LinearMap.ker (innerₛₗ ℝ w)) |>.2 fun y hy => h y hy) hx

theorem eq_of_norm_sub_sq {E : Type*} [NormedAddCommGroup E] {x y : E} (h : ‖x - y‖ ^ 2 = 0) :
    x = y :=
  sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h))

/-- **Uniqueness for (6.5)**: two solutions with the same source and the same
`(σₕ, uₕ, Mₕ, ρₕ)(0)` agree on `[0, T]` (their difference has constant energy). -/
theorem IsDiscreteWave.eq_of_eq {T : ℝ} {f : ℝ → Wt1} {σ σ₂ : ℝ → D.d0.domain}
    {φ φ₂ : ℝ → D.dt0.domain} {u u₂ : ℝ → D.dt1.domain} {M M₂ : ℝ → W2} {ρ ρ₂ : ℝ → Wt2}
    {lam lam₂ : ℝ → W1} (h1 : Q.IsDiscreteWave T f σ φ u M ρ lam)
    (h2 : Q.IsDiscreteWave T f σ₂ φ₂ u₂ M₂ ρ₂ lam₂) (e0 : σ 0 = σ₂ 0) (e1 : u 0 = u₂ 0)
    (e2 : M 0 = M₂ 0) (e3 : ρ 0 = ρ₂ 0) :
    ∀ t ∈ Icc 0 T, σ t = σ₂ t ∧ u t = u₂ t ∧ M t = M₂ t ∧ ρ t = ρ₂ t := by
  obtain ⟨cσ, cu, cM, cρ, hm, σ', u', M', ρ', hd⟩ := h1
  obtain ⟨cσ₂, cu₂, cM₂, cρ₂, hm₂, σ₂', u₂', M₂', ρ₂', hd₂⟩ := h2
  set E : ℝ → ℝ := fun t => ‖(σ t : W0) - σ₂ t‖ ^ 2 + ‖(u t : Wt1) - u₂ t‖ ^ 2 +
    ‖M t - M₂ t‖ ^ 2 + ‖ρ t - ρ₂ t‖ ^ 2 with hE
  have hc : ContinuousOn E (Icc 0 T) :=
    ((((cσ.sub cσ₂).norm.pow 2).add ((cu.sub cu₂).norm.pow 2)).add
      ((cM.sub cM₂).norm.pow 2)).add ((cρ.sub cρ₂).norm.pow 2)
  have hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt E 0 (Ici t) t := by
    intro t ht
    have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
    obtain ⟨dσ, du, dM, dρ, a1, b1, c1, d1⟩ := hd t ht
    obtain ⟨dσ₂, du₂, dM₂, dρ₂, a2, b2, c2, d2⟩ := hd₂ t ht
    obtain ⟨mσ, mφ, mu, mM, mρ, -, k1⟩ := hm t ht'
    obtain ⟨mσ₂, mφ₂, mu₂, mM₂, mρ₂, -, k2⟩ := hm₂ t ht'
    have H := ((((HasDerivWithinAt.sub dσ dσ₂).norm_sq).add
      (HasDerivWithinAt.sub du du₂).norm_sq).add
      (HasDerivWithinAt.sub dM dM₂).norm_sq).add (HasDerivWithinAt.sub dρ dρ₂).norm_sq
    refine H.congr_deriv ?_
    -- the first equation at `(σ - σ₂, φ - φ₂)`, whose constraint vanishes
    have hτ : D.d0 (σ t - σ₂ t) - Q.π1 (D.S0 ((φ t - φ₂ t : D.dt0.domain) : Wt0)) = 0 := by
      rw [LinearPMap.map_sub, Submodule.coe_sub, map_sub, map_sub, k1, k2, sub_self]
    have A1 := a1 (σ t - σ₂ t) (φ t - φ₂ t) (Q.V0.sub_mem mσ mσ₂) (Q.Vt0.sub_mem mφ mφ₂)
    have A2 := a2 (σ t - σ₂ t) (φ t - φ₂ t) (Q.V0.sub_mem mσ mσ₂) (Q.Vt0.sub_mem mφ mφ₂)
    rw [hτ, inner_zero_right, sub_zero] at A1 A2
    -- the second equation at `u - u₂`
    have B1 := b1 (u t - u₂ t) (Q.Vt1.sub_mem mu mu₂)
    have B2 := b2 (u t - u₂ t) (Q.Vt1.sub_mem mu mu₂)
    have C1 := c1 (M t - M₂ t) (Q.V2.sub_mem mM mM₂)
    have C2 := c2 (M t - M₂ t) (Q.V2.sub_mem mM mM₂)
    have D1 := d1 (ρ t - ρ₂ t) (Q.Vt2.sub_mem mρ mρ₂)
    have D2 := d2 (ρ t - ρ₂ t) (Q.Vt2.sub_mem mρ mρ₂)
    simp only [Submodule.coe_sub, LinearPMap.map_sub, map_sub, inner_sub_right]
      at A1 A2 B1 B2 C1 C2 D1 D2
    simp only [Pi.sub_apply, inner_sub_left, inner_sub_right]
    simp only [real_inner_comm (σ' t), real_inner_comm (σ₂' t), real_inner_comm (u' t),
      real_inner_comm (u₂' t), real_inner_comm (M' t), real_inner_comm (M₂' t),
      real_inner_comm (ρ' t), real_inner_comm (ρ₂' t)] at A1 A2 B1 B2 C1 C2 D1 D2 ⊢
    simp only [real_inner_comm (D.dt0 (φ t)), real_inner_comm (D.dt0 (φ₂ t)),
      real_inner_comm (Q.π2 (D.S1 (u t))), real_inner_comm (Q.π2 (D.S1 (u₂ t))),
      real_inner_comm (D.dt1 (u t)), real_inner_comm (D.dt1 (u₂ t))] at A1 A2 B1 B2 C1 C2 D1 D2 ⊢
    linarith
  have h0 : E 0 = 0 := by simp [hE, e0, e1, e2, e3]
  intro t ht
  have hEt : E t = 0 := (constant_of_has_deriv_right_zero hc hderiv t ht).trans h0
  have n1 := sq_nonneg ‖(σ t : W0) - σ₂ t‖
  have n2 := sq_nonneg ‖(u t : Wt1) - u₂ t‖
  have n3 := sq_nonneg ‖M t - M₂ t‖
  have n4 := sq_nonneg ‖ρ t - ρ₂ t‖
  simp only [hE] at hEt
  exact ⟨Subtype.ext (eq_of_norm_sub_sq (by linarith)),
    Subtype.ext (eq_of_norm_sub_sq (by linarith)), eq_of_norm_sub_sq (by linarith),
    eq_of_norm_sub_sq (by linarith)⟩

/-- The discrete gradients `d̃ψ` of the discrete pairs `(τ, ψ)`, `dτ = π¹S⁰ψ`. -/
def gaussGen : Set Wt1 :=
  {x | ∃ (τ : D.d0.domain) (ψ : D.dt0.domain), (τ : W0) ∈ Q.V0 ∧ (ψ : Wt0) ∈ Q.Vt0 ∧
    D.d0 τ = Q.π1 (D.S0 ψ) ∧ D.dt0 ψ = x}

/-- Their span `Z ⊆ Ṽₕ¹`. -/
def gaussSpan : Submodule ℝ Wt1 := Submodule.span ℝ Q.gaussGen

theorem gaussSpan_le : Q.gaussSpan ≤ Q.Vt1 :=
  Submodule.span_le.2 fun _ hx => by
    obtain ⟨_, ψ, _, hψ, _, e⟩ := hx
    exact e ▸ Q.dt0_mem ψ hψ

instance : FiniteDimensional ℝ Q.gaussSpan :=
  have := Q.fdt1
  Submodule.finiteDimensional_of_le Q.gaussSpan_le

instance : Q.gaussSpan.HasOrthogonalProjection :=
  have : CompleteSpace Q.gaussSpan := FiniteDimensional.complete ℝ _
  inferInstance

theorem isGauss_iff (σ : W0) (u : Wt1) :
    Q.IsGauss σ u ↔ σ = 0 ∧ Q.gaussSpan.starProjection u = 0 := by
  have hP : ∀ x ∈ Q.gaussSpan, ⟪u, x⟫ = ⟪Q.gaussSpan.starProjection u, x⟫ := fun x hx => by
    have := Q.gaussSpan.starProjection_inner_eq_zero u x hx
    rw [inner_sub_left] at this
    linarith
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h τ ψ hτ hψ hc => ?_⟩
  · have h0 : ∀ x ∈ Q.gaussSpan, ⟪u, x⟫ = 0 :=
      fun x hx => inner_eq_zero_of_mem_span (fun _ hy => by
        obtain ⟨τ, ψ, hτ, hψ, hc, e⟩ := hy
        exact e ▸ h τ ψ hτ hψ hc) hx
    have hm := Q.gaussSpan.starProjection_apply_mem u
    have := (hP _ hm).symm.trans (h0 _ hm)
    exact inner_self_eq_zero.1 this
  · have hx : D.dt0 ψ ∈ Q.gaussSpan := Submodule.subset_span ⟨τ, ψ, hτ, hψ, hc, rfl⟩
    rw [hP _ hx, h, inner_zero_left]

/-- **The discrete Gauss law propagates** along solutions of (6.5) without source, for BGG
data. -/
theorem IsDiscreteWave.isGauss (hD : D.IsBGG) {T : ℝ} {σ : ℝ → D.d0.domain}
    {φ : ℝ → D.dt0.domain} {u : ℝ → D.dt1.domain} {M : ℝ → W2} {ρ : ℝ → Wt2} {lam : ℝ → W1}
    (h : Q.IsDiscreteWave T 0 σ φ u M ρ lam) (h0 : Q.IsGauss (σ 0) (u 0)) :
    ∀ t ∈ Icc 0 T, Q.IsGauss (σ t) (u t) := by
  obtain ⟨cσ, cu, -, -, hm, σ', u', M', ρ', hd⟩ := h
  set P := Q.gaussSpan.starProjection
  have hP : ∀ (w : Wt1), ∀ x ∈ Q.gaussSpan, ⟪w, x⟫ = ⟪P w, x⟫ := fun w x hx => by
    have := Q.gaussSpan.starProjection_inner_eq_zero w x hx
    rw [inner_sub_left] at this
    linarith
  set E : ℝ → ℝ := fun t => ‖(σ t : W0)‖ ^ 2 + ‖P (u t)‖ ^ 2 with hE
  have hc : ContinuousOn E (Icc 0 T) :=
    (cσ.norm.pow 2).add ((P.continuous.comp_continuousOn cu).norm.pow 2)
  have hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt E 0 (Ici t) t := by
    intro t ht
    obtain ⟨dσ, du, -, -, a, b, -, -⟩ := hd t ht
    obtain ⟨mσ, mφ, -, -, -, -, k⟩ := hm t (Ico_subset_Icc_self ht)
    have H := dσ.norm_sq.add (P.hasFDerivAt.comp_hasDerivWithinAt t du).norm_sq
    refine H.congr_deriv ?_
    simp only [Function.comp_apply]
    -- `⟪σ', σ⟫ = ⟪u, d̃φ⟫`
    have A := a (σ t) (φ t) mσ mφ
    rw [k, sub_self, inner_zero_right, sub_zero] at A
    have hφZ : D.dt0 (φ t) ∈ Q.gaussSpan := Submodule.subset_span ⟨σ t, φ t, mσ, mφ, k, rfl⟩
    -- `⟪u', z⟫ = -⟪d̃φ, z⟫` on `Z`
    have hB : ∀ x ∈ Q.gaussSpan, ⟪u' t + D.dt0 (φ t), x⟫ = 0 := fun x hx =>
      inner_eq_zero_of_mem_span (fun _ hy => by
        obtain ⟨τ, ψ, hτ, hψ, hτψ, e⟩ := hy
        subst e
        obtain ⟨hdψ, hdd⟩ := hD.2.1 ψ
        obtain ⟨hSψ, hanti⟩ := hD.2.2 ψ
        have hS : Q.π2 (D.S1 (D.dt0 ψ)) = 0 := by
          have e1 : D.S1 (D.dt0 ψ) = -D.d1 ⟨D.S0 ψ, hSψ⟩ := by rw [hanti, neg_neg]
          rw [e1, map_neg, ← Q.comm1 ⟨D.S0 ψ, hSψ⟩, neg_eq_zero]
          have e2 : (⟨Q.π1 (D.S0 ψ), Q.le1 (Q.π1_mem _)⟩ : D.d1.domain) =
              ⟨D.d0 τ, (hD.1 τ).1⟩ := Subtype.ext hτψ.symm
          rw [e2]
          exact (hD.1 τ).2
        have := b ⟨D.dt0 ψ, hdψ⟩ (Q.dt0_mem ψ hψ)
        change _ + _ + ⟪M t, Q.π2 (D.S1 (D.dt0 ψ))⟫ + _ = _ at this
        rw [hS, hdd, inner_zero_right, inner_zero_right, add_zero, add_zero] at this
        simpa [inner_add_left] using this) hx
    have hPu : P (u t) ∈ Q.gaussSpan := Q.gaussSpan.starProjection_apply_mem (u t)
    have B := hB _ hPu
    rw [inner_add_left] at B
    have e3 : ⟪P (u t), P (u' t)⟫ = ⟪u' t, P (u t)⟫ := by
      rw [real_inner_comm, ← hP _ _ hPu]
    rw [hP _ _ hφZ] at A
    have e4 : ⟪(σ t : W0), σ' t⟫ = ⟪σ' t, (σ t : W0)⟫ := real_inner_comm _ _
    have e5 : ⟪D.dt0 (φ t), P (u t)⟫ = ⟪P (u t), D.dt0 (φ t)⟫ := real_inner_comm _ _
    linarith
  have hE0 : E 0 = 0 := by
    obtain ⟨h1, h2⟩ := (Q.isGauss_iff _ _).1 h0
    have h2' : P (u 0) = 0 := h2
    simp only [hE, h1, h2', norm_zero]
    norm_num
  intro t ht
  have hEt : E t = 0 := (constant_of_has_deriv_right_zero hc hderiv t ht).trans hE0
  have n1 := sq_nonneg ‖(σ t : W0)‖
  have n2 := sq_nonneg ‖P (u t)‖
  simp only [hE] at hEt
  refine (Q.isGauss_iff _ _).2 ⟨norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (by linarith)),
    norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (by linarith))⟩

/-! ### A nonzero state in the discrete Gauss law, and non-stationarity -/

variable {Q} in
/-- **A nonzero `uₕ` in the discrete Gauss law** for BGG data: if `π²S¹v₁ ≠ 0` for some
`v₁ ∈ Ṽₕ¹`, the representative `u₀ ∈ Ṽₕ¹` of `v ↦ ⟪M, π²S¹v⟫`, `M = π²S¹v₁`, is nonzero,
orthogonal to `d̃ψ` for every discrete pair `dτ = π¹S⁰ψ` (there `π²S¹d̃ψ = -d π¹S⁰ψ = -d dτ = 0`)
and has `π²S¹u₀ ≠ 0` (`⟪M, π²S¹u₀⟫ = ‖u₀‖²`). -/
theorem exists_isGauss_ne_zero (hD : D.IsBGG) {v₁ : D.dt1.domain} (hv₁ : (v₁ : Wt1) ∈ Q.Vt1)
    (hne : Q.π2 (D.S1 v₁) ≠ 0) : ∃ u₀ : D.dt1.domain, (u₀ : Wt1) ∈ Q.Vt1 ∧ (u₀ : Wt1) ≠ 0 ∧
      Q.IsGauss 0 u₀ ∧ Q.π2 (D.S1 u₀) ≠ 0 := by
  have := Q.fdt1
  set M := Q.π2 (D.S1 v₁)
  let F : Q.Vt1 →L[ℝ] ℝ := (innerSL ℝ M).comp (Q.π2.comp (D.S1.comp Q.Vt1.subtypeL))
  set r : Q.Vt1 := (InnerProductSpace.toDual ℝ Q.Vt1).symm F with hr
  have key : ∀ v : Q.Vt1, ⟪(r : Wt1), (v : Wt1)⟫ = ⟪M, Q.π2 (D.S1 v)⟫ := fun v => by
    rw [← Submodule.coe_inner, hr, InnerProductSpace.toDual_symm_apply]; rfl
  have hr0 : (r : Wt1) ≠ 0 := fun h => by
    have := key ⟨_, hv₁⟩
    rw [h, inner_zero_left] at this
    exact hne (inner_self_eq_zero.1 this.symm)
  refine ⟨⟨r, Q.let1 r.2⟩, r.2, hr0, ⟨rfl, fun τ ψ _ hψ hτψ => ?_⟩, fun h => ?_⟩
  · obtain ⟨hd, hS⟩ := hD.2.2 ψ
    have hc := Q.comm1 ⟨_, hd⟩
    have e : (⟨Q.π1 (D.S0 ψ), Q.le1 (Q.π1_mem _)⟩ : D.d1.domain) = ⟨D.d0 τ, (hD.1 τ).1⟩ :=
      Subtype.ext hτψ.symm
    rw [e, (hD.1 τ).2, hS, map_neg] at hc
    change ⟪(r : Wt1), D.dt0 ψ⟫ = 0
    rw [key ⟨_, Q.dt0_mem ψ hψ⟩]
    change ⟪M, Q.π2 (D.S1 (D.dt0 ψ))⟫ = 0
    rw [neg_eq_zero.1 hc.symm, inner_zero_right]
  · have := key r
    change ⟪(r : Wt1), (r : Wt1)⟫ = ⟪M, Q.π2 (D.S1 (r : Wt1))⟫ at this
    rw [show D.S1 ((⟨r, Q.let1 r.2⟩ : D.dt1.domain) : Wt1) = D.S1 (r : Wt1) from rfl] at h
    rw [h, inner_zero_right] at this
    exact hr0 (inner_self_eq_zero.1 this)

variable {Q} in
/-- **Solutions of (6.5) with `π²S¹uₕ(0) ≠ 0` are not stationary**: `Mₕ` is not constant on
`[0, T]` (else `Mₕ'(0) = 0`, while `⟪Mₕ'(0), z⟫ = ⟪π²S¹uₕ(0), z⟫` on `Vₕ²`). -/
theorem IsDiscreteWave.exists_M_ne {T : ℝ} (hT : 0 < T) {f : ℝ → Wt1} {σ : ℝ → D.d0.domain}
    {φ : ℝ → D.dt0.domain} {u : ℝ → D.dt1.domain} {M : ℝ → W2} {ρ : ℝ → Wt2} {lam : ℝ → W1}
    (h : Q.IsDiscreteWave T f σ φ u M ρ lam) (hu : Q.π2 (D.S1 (u 0)) ≠ 0) :
    ∃ t ∈ Ioc 0 T, M t ≠ M 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨-, -, -, -, -, σ', u', M', ρ', hd⟩ := h
  obtain ⟨-, -, hM, -, -, -, hM', -⟩ := hd 0 ⟨le_rfl, hT⟩
  have hconst : HasDerivWithinAt M 0 (Ici 0) 0 :=
    (hasDerivWithinAt_const 0 (Ici 0) (M 0)).congr_of_eventuallyEq
      (Filter.mem_of_superset (Icc_mem_nhdsGE hT) fun t ht => by
        rcases eq_or_lt_of_le ht.1 with h0 | h0
        · subst h0; rfl
        · exact hc t ⟨h0, ht.2⟩) rfl
  have h0 : M' 0 = 0 := (uniqueDiffWithinAt_Ici 0).eq_deriv _ hM hconst
  have := hM' _ (Q.π2_mem (D.S1 (u 0)))
  rw [h0, inner_zero_left] at this
  exact hu (inner_self_eq_zero.1 this.symm)

end FEEC.WeakSymmetryData.Discretization
