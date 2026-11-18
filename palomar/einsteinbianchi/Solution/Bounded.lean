module

public import Solution.Proxy

/-!
# The electric boundary conditions lose the constraints on every bounded domain

The limit clause of `FEEC.weakSymmetry_electric` (the exact solution, on `Ω = Q`), from the path
criteria of `Feec.Counterexamples.BoundedBGG` (`datumBeta_spec`). For the datum
`U₀ = (0, 0, 0, ⋆β)`, `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)`, of `bggData Ω`:

* `U₀` lies in the domain of `L`, with `(L U₀)_u = B⁻¹ diag(1, -1, 0)`, from Green's formula for
  `curl_min` against the smooth `β` (`curl β = -diag(1, -1, 0)`, `inner_rhoBeta_dt1`); every
  `V` with `L U₀ = V` has this electric component (`isWave_rhoBeta_eq`), by density of `D(d̃¹)`.
* Along a strong solution, `B' = B(d̃u) = curl_min E` (`fieldE_mem_curl_minimal`) and
  `⟪E'(0), diag(1, -1, 0)⟫ = 2|Ω| ≠ 0`, so `B(t)` is not symmetric for some `t`
  (`Feec.Counterexamples.BoundedBGG.exists_not_symm_of_path`), and `E(t)` is not TSD for some `t`
  (TSD fields of `H̊(curl)` lie in `L²(TSD₀) ⊥ diag(1, -1, 0)`, closed).
* The strong solutions exist: the orbit of `(u, (M, ρ))(0) = (0, (0, ⋆β))` for the skew-adjoint
  operator `(u, w) ↦ (-D₁* w, D₁ u)` of `D₁ u = (S¹u, d̃u)` (`ShortHilbertComplex.ofOp`), with
  `σ ≡ 0`: `u(t) ⊥ d̃ψ` for `(τ, ψ) ∈ Γ` is conserved since `D₁ d̃ψ = 0` (`D1_dt0_eq_zero`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.1, §6.3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace ContDiff LinearPMap
open Set MeasureTheory Filter Topology

@[expose] public noncomputable section

namespace FEEC

open Feec Feec.Domain Feec.Models.BoundedDomain Feec.Counterexamples.BoundedDomainTSD
  Feec.Counterexamples.BoundedBGG

/-! ### Componentwise operators -/

section VecOp

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {n : ℕ}

theorem mem_graph_vecOp_iff (T : E →ₗ.[ℝ] F) (x : PiLp 2 (fun _ : Fin n => E))
    (y : PiLp 2 (fun _ : Fin n => F)) :
    (x, y) ∈ (vecOpC T).graph ↔ ∀ a, (x a, y a) ∈ T.graph := by
  constructor
  · intro h a
    obtain ⟨z, rfl, rfl⟩ := (LinearPMap.mem_graph_iff _).1 h
    exact (LinearPMap.mem_graph_iff _).2 ⟨⟨_, z.2 a⟩, rfl, rfl⟩
  · intro h
    have hx : ∀ a, x a ∈ T.domain := fun a => LinearPMap.mem_domain_of_mem_graph (h a)
    refine (LinearPMap.mem_graph_iff _).2 ⟨⟨x, hx⟩, rfl, PiLp.ext fun a => ?_⟩
    exact ((LinearPMap.image_iff (hx a)).2 (h a)).symm

theorem isClosed_vecOp {T : E →ₗ.[ℝ] F} (hT : T.IsClosed) : (vecOpC (n := n) T).IsClosed := by
  rw [LinearPMap.IsClosed]
  have e : ((vecOpC (n := n) T).graph : Set _) = ⋂ a, (fun p : PiLp 2 (fun _ : Fin n => E) ×
      PiLp 2 (fun _ : Fin n => F) => (p.1 a, p.2 a)) ⁻¹' (T.graph : Set (E × F)) := by
    ext p
    simp only [SetLike.mem_coe, mem_iInter, mem_preimage]
    exact mem_graph_vecOp_iff T p.1 p.2
  rw [e]
  refine isClosed_iInter fun a => hT.preimage ?_
  exact ((PiLp.continuous_apply 2 _ a).comp continuous_fst).prodMk
    ((PiLp.continuous_apply 2 _ a).comp continuous_snd)

theorem dense_vecOp {T : E →ₗ.[ℝ] F} (hT : Dense (T.domain : Set E)) :
    Dense ((vecOpC (n := n) T).domain : Set (PiLp 2 fun _ : Fin n => E)) := by
  have e : ((vecOpC (n := n) T).domain : Set (PiLp 2 fun _ : Fin n => E)) =
      WithLp.toLp 2 '' univ.pi fun _ => (T.domain : Set E) := by
    ext v
    refine ⟨fun hv => ⟨WithLp.ofLp v, fun a _ => hv a, rfl⟩, ?_⟩
    rintro ⟨w, hw, rfl⟩ a
    exact hw a (mem_univ a)
  rw [e]
  exact (WithLp.equiv 2 (∀ _ : Fin n, E)).symm.surjective.denseRange.dense_image
    (PiLp.continuous_toLp 2 _) (dense_pi univ fun _ _ => hT)

end VecOp

/-! ### The second operator `D₁ u = (S¹u, d̃u)` -/

section D1

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2)

/-- **The second operator of the complex with weak symmetry**, `D₁ u = (S¹u, d̃u)` on `D(d̃¹)`. -/
def WeakSymmetryData.opD1 : Wt1 →ₗ.[ℝ] WithLp 2 (W2 × Wt2) where
  domain := D.dt1.domain
  toFun := (WithLp.linearEquiv 2 ℝ (W2 × Wt2)).symm.toLinearMap ∘ₗ
    (((D.S1 : Wt1 →ₗ[ℝ] W2).comp D.dt1.domain.subtype).prod D.dt1.toFun)

theorem WeakSymmetryData.opD1_apply (u : D.opD1.domain) :
    D.opD1 u = WithLp.toLp 2 (D.S1 u, D.dt1 ⟨u, u.2⟩) := rfl

theorem WeakSymmetryData.isClosed_opD1 (h : D.dt1.IsClosed) : D.opD1.IsClosed := by
  rw [LinearPMap.IsClosed]
  have e : (D.opD1.graph : Set (Wt1 × WithLp 2 (W2 × Wt2))) =
      (fun p : Wt1 × WithLp 2 (W2 × Wt2) => (p.1, (WithLp.ofLp p.2).2)) ⁻¹'
        (D.dt1.graph : Set (Wt1 × Wt2)) ∩ {p | (WithLp.ofLp p.2).1 = D.S1 p.1} := by
    ext ⟨u, w⟩
    simp only [SetLike.mem_coe, mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · intro hw
      obtain ⟨z, rfl, rfl⟩ := (LinearPMap.mem_graph_iff _).1 hw
      exact ⟨(LinearPMap.mem_graph_iff _).2 ⟨z, rfl, rfl⟩, rfl⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨z, rfl, hz⟩ := (LinearPMap.mem_graph_iff _).1 h1
      refine (LinearPMap.mem_graph_iff _).2 ⟨z, rfl, ?_⟩
      change WithLp.toLp 2 (D.S1 z, D.dt1 z) = w
      rw [hz, ← h2]
  rw [e]
  refine (h.preimage (continuous_fst.prodMk ?_)).inter
    (isClosed_eq ?_ (D.S1.continuous.comp continuous_fst))
  · exact continuous_snd.comp ((WithLp.prodContinuousLinearEquiv 2 ℝ W2 Wt2).continuous.comp
      continuous_snd)
  · exact continuous_fst.comp ((WithLp.prodContinuousLinearEquiv 2 ℝ W2 Wt2).continuous.comp
      continuous_snd)

theorem WeakSymmetryData.inner_opD1 (w : WithLp 2 (W2 × Wt2)) (u : D.opD1.domain) :
    ⟪w, D.opD1 u⟫ = ⟪(WithLp.ofLp w).1, D.S1 u⟫ + ⟪(WithLp.ofLp w).2, D.dt1 ⟨u, u.2⟩⟫ := by
  rw [D.opD1_apply, WithLp.prod_inner_apply]

/-- `⟪D₁* w, v⟫ = ⟪M, S¹v⟫ + ⟪ρ, d̃v⟫` for `w = (M, ρ)`. -/
theorem WeakSymmetryData.inner_adjoint_opD1 [CompleteSpace Wt1]
    (hd : Dense (D.dt1.domain : Set Wt1))
    (w : D.opD1†.domain) (v : D.dt1.domain) :
    ⟪D.opD1† w, (v : Wt1)⟫ = ⟪(WithLp.ofLp (w : WithLp 2 (W2 × Wt2))).1, D.S1 v⟫ +
      ⟪(WithLp.ofLp (w : WithLp 2 (W2 × Wt2))).2, D.dt1 v⟫ := by
  have h := LinearPMap.adjoint_isFormalAdjoint (T := D.opD1) hd w ⟨(v : Wt1), v.2⟩
  rw [h, D.inner_opD1]

end D1

/-! ### `x = 0` if it is orthogonal to a dense set -/

theorem eq_zero_of_inner_dense {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : Set E} (hs : Dense s) {x : E} (h : ∀ y ∈ s, ⟪x, y⟫ = 0) : x = 0 := by
  have hc : IsClosed {y : E | ⟪x, y⟫ = 0} := isClosed_eq (continuous_const.inner continuous_id)
    continuous_const
  have := hc.closure_subset_iff.2 h (hs.closure_eq.symm ▸ mem_univ x)
  exact inner_self_eq_zero.1 this

/-! ### The datum `(0, 0, 0, ⋆β)` -/

variable {Ω : Set (Fin 3 → ℝ)}

theorem toL2F_congr {ι : Type*} {ψ ψ' : ι → R3 → ℝ} (h : ψ = ψ')
    (hψ : ∀ i, MemLp (ψ i) 2 (volume.restrict Ω)) (hψ' : ∀ i, MemLp (ψ' i) 2 (volume.restrict Ω)) :
    toL2F hψ = toL2F hψ' := by
  subst h; rfl

/-- `S⁰ = Σₐ dxₐ ∧ ·` is injective on vector `0`-forms (`(S⁰φ)_{dxₐ} = φₐ`). -/
theorem wedge_zero_injective {φ : L2Vec Ω 0} (h : wedge Ω 0 φ = 0) : φ = 0 := by
  refine PiLp.ext fun a => PiLp.ext fun s => ?_
  have hs : s = ⟨∅, by simp⟩ := Subtype.ext (Finset.card_eq_zero.1 (by have := s.2; omega))
  have e := congrArg (fun z : L2Form Ω 1 => z (ix1 a)) h
  simp only [wedge_eq] at e
  change Feec.FiniteElement.wsL2 0 φ (ix1 a) = 0 at e
  rw [Feec.FiniteElement.wsL2_apply, Fintype.sum_prod_type, Finset.sum_eq_single a] at e
  · rw [Finset.sum_eq_single ⟨∅, by simp⟩] at e
    · rw [wsCoeff_eq] at e
      subst hs
      simpa [ix1, f1, sgn] using e
    · intro r _ hr
      exact absurd (Subtype.ext (Finset.card_eq_zero.1 (by have := r.2; omega))) hr
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [wsCoeff_eq]
    simp [ix1, f1, hb]
  · simp

/-- `S⁰φ = 0` forces `d̃φ = 0`. -/
theorem dt0_eq_zero_of_S0 (φ : (bggData Ω).dt0.domain) (h : (bggData Ω).S0 φ = 0) :
    (bggData Ω).dt0 φ = 0 := by
  have : φ = 0 := Subtype.ext (wedge_zero_injective h)
  rw [this, LinearPMap.map_zero]

/-- `⋆β`: the vector `2`-form whose magnetic field is `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)`. -/
def rhoBeta (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : L2Vec Ω 2 := fieldB.symm (betaL2 hΩ hb)

/-- `diag(1, -1, 0)` as the electric field of a vector `1`-form. -/
def uDiag (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : L2Vec Ω 1 :=
  fieldE.symm (constField hΩ hb diagA)

theorem curl_minimal_fieldE (hΩ : IsOpen Ω) (v : (bggData Ω).dt1.domain) :
    ∃ h : fieldE (v : L2Vec Ω 1) ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain,
      (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω ⟨_, h⟩ = fieldB ((bggData Ω).dt1 v) := by
  have hg := fieldE_mem_curl_minimal hΩ v
  have hm := LinearPMap.mem_domain_of_mem_graph hg
  exact ⟨hm, ((LinearPMap.image_iff hm).2 hg).symm⟩

/-- **Green's formula against `β`**: `⟪⋆β, d̃v⟫ = ⟪β, curl E_v⟫ = ⟪curl β, E_v⟫ =
-⟪diag(1, -1, 0), E_v⟫` for `v ∈ H̊Λ¹(Ω)³`. -/
theorem inner_rhoBeta_dt1 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (v : (bggData Ω).dt1.domain) :
    ⟪rhoBeta hΩ hb, (bggData Ω).dt1 v⟫ = -⟪uDiag hΩ hb, (v : L2Vec Ω 1)⟫ := by
  obtain ⟨h, e⟩ := curl_minimal_fieldE hΩ v
  have hs : ∀ ij, ContDiff ℝ 1 (betaField ij) := fun ij => (contDiff_betaField ij).of_le (by simp)
  have hg := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal_green hΩ curlOp_isOrderLE ⟨_, h⟩
    (ψ := betaField) hs
    (fun ij => memLp_of_continuous hΩ.measurableSet hb (contDiff_betaField ij).continuous)
    (fun ij => by
      rw [← curlM_eq_formalAdj_apply]
      exact memLp_of_continuous hΩ.measurableSet hb (continuous_curlM hs ij))
  rw [toL2F_congr (curlM_eq_formalAdj_apply betaField).symm _
    (fun i => memLp_of_continuous hΩ.measurableSet hb (continuous_curlM hs i))] at hg
  change ⟪_, betaL2 hΩ hb⟫ = ⟪_, smoothField hΩ hb (curlM betaField) (continuous_curlM hs)⟫ at hg
  rw [curl_betaL2, e] at hg
  rw [← fieldB.inner_map_map, rhoBeta, LinearIsometryEquiv.apply_symm_apply, real_inner_comm, hg,
    inner_neg_right, uDiag, ← fieldE.inner_map_map, LinearIsometryEquiv.apply_symm_apply,
    real_inner_comm]

/-- The datum `U₀ = (0, 0, 0, ⋆β)`. -/
def datumBeta (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    L2Form Ω 0 × L2Vec Ω 1 × L2Form Ω 2 × L2Vec Ω 2 := (0, 0, 0, rhoBeta hΩ hb)

/-- **`L U₀ = (0, B⁻¹ diag(1, -1, 0), 0, 0)`.** -/
theorem isWave_datumBeta (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (bggData Ω).IsWave (datumBeta hΩ hb) (0, uDiag hΩ hb, 0, 0) := by
  refine ⟨0, 0, 0, rfl, rfl, by rw [LinearPMap.map_zero, Submodule.coe_zero, map_zero],
    fun τ ψ _ => by simp, fun v => ?_, by simp, by simp⟩
  change ⟪uDiag hΩ hb, (v : L2Vec Ω 1)⟫ = -⟪(bggData Ω).dt0 0, (v : L2Vec Ω 1)⟫ -
    ⟪(0 : L2Form Ω 2), (bggData Ω).S1 v⟫ - ⟪rhoBeta hΩ hb, (bggData Ω).dt1 v⟫
  rw [inner_rhoBeta_dt1, LinearPMap.map_zero]
  simp

/-- **Every `V` with `L U₀ = V` has `V_u = B⁻¹ diag(1, -1, 0)`** (by density of `H̊Λ¹(Ω)³`). -/
theorem isWave_datumBeta_eq (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {V : L2Form Ω 0 × L2Vec Ω 1 × L2Form Ω 2 × L2Vec Ω 2}
    (h : (bggData Ω).IsWave (datumBeta hΩ hb) V) : V.2.1 = uDiag hΩ hb := by
  obtain ⟨σ, φ, u, hσ, -, hc, -, h2, -, -⟩ := h
  have hσ0 : σ = 0 := Subtype.ext hσ
  rw [hσ0, LinearPMap.map_zero] at hc
  have hφ := dt0_eq_zero_of_S0 φ hc.symm
  refine sub_eq_zero.1 (eq_zero_of_inner_dense
    (dense_vecOp (n := 3) (T := dMin Ω 1) ?_) fun y hy => ?_)
  · rw [dMin_eq]; exact (extDerivOp ℝ 3 1).dense_minimal_domain hΩ
  · have e := h2 ⟨y, hy⟩
    change ⟪V.2.1, y⟫ = -⟪(bggData Ω).dt0 φ, y⟫ - ⟪(0 : L2Form Ω 2), (bggData Ω).S1 y⟫ -
      ⟪rhoBeta hΩ hb, (bggData Ω).dt1 ⟨y, hy⟩⟫ at e
    rw [hφ, inner_rhoBeta_dt1] at e
    rw [inner_sub_left, e]
    simp

/-! ### The BGG data on `Ω` are `Feec`'s -/

variable (Ω) in
theorem bggData_eq : bggData Ω = ⟨(extDerivOp ℝ 3 0).minimal Ω, (extDerivOp ℝ 3 1).minimal Ω,
    vecOpC ((extDerivOp ℝ 3 0).minimal Ω), vecOpC ((extDerivOp ℝ 3 1).minimal Ω),
    Feec.FiniteElement.wsL2 (Ω := Ω) 0, Feec.FiniteElement.wsL2 (Ω := Ω) 1⟩ := by
  change (⟨dMin Ω 0, dMin Ω 1, vecOpC (dMin Ω 0), vecOpC (dMin Ω 1), wedge Ω 0, wedge Ω 1⟩ :
    WeakSymmetryData (L2Form Ω 0) (L2Form Ω 1) (L2Form Ω 2) (L2Vec Ω 0) (L2Vec Ω 1)
      (L2Vec Ω 2)) = _
  rw [dMin_eq, dMin_eq, wedge_eq, wedge_eq]

/-- **The data `bggData Ω` are BGG data** on every open `Ω`. -/
theorem isBGG_bggData (hΩ : IsOpen Ω) : (bggData Ω).IsBGG := by
  rw [bggData_eq]
  refine ⟨fun x => ⟨ConstCoeffOp.minimal_mapsTo hΩ (isComplexPair_extDerivOp 0) x,
    ConstCoeffOp.minimal_comp hΩ (isComplexPair_extDerivOp 0) x⟩,
    fun x => ⟨fun a => ConstCoeffOp.minimal_mapsTo hΩ (isComplexPair_extDerivOp 0) ⟨_, x.2 a⟩,
      PiLp.ext fun a => ConstCoeffOp.minimal_comp hΩ (isComplexPair_extDerivOp 0) ⟨_, x.2 a⟩⟩,
    fun ψ => ?_⟩
  exact Feec.FiniteElement.wsL2_mem_minimal hΩ 0 (v := (ψ : L2Vec Ω 0)) fun a => ψ.2 a

/-- `D₁ d̃ψ = 0` for `(τ, ψ) ∈ Γ`: `S¹d̃ψ = -d S⁰ψ = -d dτ = 0` and `d̃ d̃ = 0`. -/
theorem opD1_dt0 (hΩ : IsOpen Ω) {τ : (bggData Ω).d0.domain} {ψ : (bggData Ω).dt0.domain}
    (h : (bggData Ω).d0 τ = (bggData Ω).S0 ψ) :
    (bggData Ω).opD1 ⟨_, ((isBGG_bggData hΩ).2.1 ψ).1⟩ = 0 := by
  obtain ⟨h1, h2⟩ := (isBGG_bggData hΩ).2.1 ψ
  obtain ⟨h3, h4⟩ := (isBGG_bggData hΩ).2.2 ψ
  obtain ⟨h5, h6⟩ := (isBGG_bggData hΩ).1 τ
  have e : (bggData Ω).S1 ((bggData Ω).dt0 ψ) = 0 := by
    rw [← neg_eq_zero, ← h4, ← h6]
    exact LinearPMap.apply_congr' _ _ _ h.symm
  change WithLp.toLp 2 ((bggData Ω).S1 ((bggData Ω).dt0 ψ), (bggData Ω).dt1 ⟨_, h1⟩) = 0
  rw [e, h2]
  rfl

/-! ### The strong solutions from `U₀` -/

theorem isClosed_bgg_dt1 (hΩ : IsOpen Ω) : (bggData Ω).dt1.IsClosed :=
  isClosed_vecOp (by rw [dMin_eq]; exact (extDerivOp ℝ 3 1).isClosed_minimal hΩ)

theorem dense_bgg_dt1 (hΩ : IsOpen Ω) : Dense ((bggData Ω).dt1.domain : Set (L2Vec Ω 1)) :=
  dense_vecOp (by rw [dMin_eq]; exact (extDerivOp ℝ 3 1).dense_minimal_domain hΩ)

/-- The second operator as the short complex `L²Λ¹(Ω)³ → L²Λ²(Ω) × L²Λ²(Ω)³ → 0`; its wave
operator is `(u, w) ↦ (-D₁* w, D₁ u)`. -/
abbrev shortD1 (hΩ : IsOpen Ω) :
    ShortHilbertComplex ℝ (L2Vec Ω 1) (WithLp 2 (L2Form Ω 2 × L2Vec Ω 2)) PUnit :=
  ShortHilbertComplex.ofOp (bggData Ω).opD1 (dense_bgg_dt1 hΩ)
    ((bggData Ω).isClosed_opD1 (isClosed_bgg_dt1 hΩ))

theorem mem_adjoint_rhoBeta (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (WithLp.toLp 2 (0, rhoBeta hΩ hb) : WithLp 2 (L2Form Ω 2 × L2Vec Ω 2)) ∈
      (bggData Ω).opD1†.domain :=
  LinearPMap.mem_adjoint_domain_of_exists _ ⟨-uDiag hΩ hb, fun v => by
    rw [WeakSymmetryData.inner_opD1]
    simp only [inner_zero_left, zero_add]
    rw [inner_rhoBeta_dt1 hΩ hb ⟨v, v.2⟩, inner_neg_left]⟩

/-- The datum `(u, (M, ρ)) = (0, (0, ⋆β))` of `shortD1`. -/
def stateBeta (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    PiLp 2 (ShortHilbertComplex.W3 (L2Vec Ω 1) (WithLp 2 (L2Form Ω 2 × L2Vec Ω 2)) PUnit) :=
  ShortHilbertComplex.mk3 0 (WithLp.toLp 2 (0, rhoBeta hΩ hb)) PUnit.unit

/-- **The orbit states solve the system**: a state `(0, u, M, ρ)` with `u ∈ D(d̃¹)`,
`(M, ρ) ∈ D(D₁*)` and `u ⊥ d̃ψ` for `(τ, ψ) ∈ Γ` has `L (0, u, M, ρ) = (0, -D₁*(M, ρ), D₁ u)`. -/
theorem isWave_of_orbit (hΩ : IsOpen Ω) {u : L2Vec Ω 1} (hu : u ∈ (bggData Ω).dt1.domain)
    {w : WithLp 2 (L2Form Ω 2 × L2Vec Ω 2)} (hw : w ∈ (bggData Ω).opD1†.domain)
    (hg : ∀ (τ : (bggData Ω).d0.domain) (ψ : (bggData Ω).dt0.domain),
      (bggData Ω).d0 τ = (bggData Ω).S0 ψ → ⟪u, (bggData Ω).dt0 ψ⟫ = 0) :
    (bggData Ω).IsWave (0, u, (WithLp.ofLp w).1, (WithLp.ofLp w).2)
      (0, -((bggData Ω).opD1† ⟨w, hw⟩), (bggData Ω).S1 u, (bggData Ω).dt1 ⟨u, hu⟩) := by
  refine ⟨0, 0, ⟨u, hu⟩, rfl, rfl, by rw [LinearPMap.map_zero, Submodule.coe_zero, map_zero],
    fun τ ψ h => ?_, fun v => ?_, rfl, rfl⟩
  · change ⟪(0 : L2Form Ω 0), (τ : L2Form Ω 0)⟫ = ⟪u, (bggData Ω).dt0 ψ⟫
    rw [inner_zero_left, hg τ ψ h]
  · have key := (bggData Ω).inner_adjoint_opD1 (dense_bgg_dt1 hΩ) ⟨w, hw⟩ v
    have k0 : (bggData Ω).dt0 (0 : (bggData Ω).dt0.domain) = 0 := LinearPMap.map_zero _
    change ⟪-((bggData Ω).opD1† ⟨w, hw⟩), (v : L2Vec Ω 1)⟫ =
      -⟪(bggData Ω).dt0 0, (v : L2Vec Ω 1)⟫ - ⟪(WithLp.ofLp w).1, (bggData Ω).S1 v⟫ -
        ⟪(WithLp.ofLp w).2, (bggData Ω).dt1 v⟫
    rw [inner_neg_left, key, k0, inner_zero_left]
    ring

section Orbit

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

theorem stateBeta_mem (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    stateBeta hΩ hb ∈ (shortD1 hΩ).wave.domain :=
  (shortD1 hΩ).mem_wave_domain.2 ⟨Submodule.zero_mem _, trivial, mem_adjoint_rhoBeta hΩ hb,
    by rw [show (shortD1 hΩ).d₁ = 0 from rfl, LinearPMap.adjoint_zero]; trivial⟩

/-- **A strong solution from `U₀ = (0, 0, 0, ⋆β)`** on every `[0, T]`: `σ ≡ 0` and the orbit of
`stateBeta` for the wave operator of `D₁`. -/
theorem exists_strongSolution_datumBeta (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (T : ℝ) :
    ∃ U, U 0 = datumBeta hΩ hb ∧ IsStrongSolution {p | (bggData Ω).IsWave p.1 p.2} (Icc 0 T) U := by
  set S := shortD1 hΩ
  set X := fun t => S.toHilbertComplex.waveGroup.S t (stateBeta hΩ hb)
  have hX : Evolution.IsStrongSolution S.wave (Icc 0 T) 0 X :=
    S.toHilbertComplex.isStrongSolution_waveGroup (stateBeta_mem hΩ hb) T
  have hX0 : X 0 = stateBeta hΩ hb := by simp [X]
  set P0 := PiLp.proj 2 (𝕜 := ℝ) (ShortHilbertComplex.W3 (L2Vec Ω 1)
    (WithLp 2 (L2Form Ω 2 × L2Vec Ω 2)) PUnit) 0
  set P1 := PiLp.proj 2 (𝕜 := ℝ) (ShortHilbertComplex.W3 (L2Vec Ω 1)
    (WithLp 2 (L2Form Ω 2 × L2Vec Ω 2)) PUnit) 1
  obtain ⟨uX, huX⟩ : ∃ f : ℝ → L2Vec Ω 1, f = fun s => X s 0 := ⟨_, rfl⟩
  obtain ⟨wX, hwX⟩ : ∃ f : ℝ → WithLp 2 (L2Form Ω 2 × L2Vec Ω 2), f = fun s => X s 1 :=
    ⟨_, rfl⟩
  have hS : S.d₀ = (bggData Ω).opD1 := rfl
  have hmem : ∀ t ∈ Icc 0 T, uX t ∈ (bggData Ω).dt1.domain ∧
      wX t ∈ (bggData Ω).opD1†.domain := fun t ht => by
    subst huX hwX
    have h := (S.mem_wave_domain).1 (hX.mem_domain ht)
    rw [hS] at h
    exact ⟨h.1, h.2.2.1⟩
  have hcomp : ∀ t (ht : t ∈ Icc 0 T), HasDerivWithinAt uX
      (-((bggData Ω).opD1† ⟨wX t, (hmem t ht).2⟩)) (Icc 0 T) t ∧
      HasDerivWithinAt wX ((bggData Ω).opD1 ⟨uX t, (hmem t ht).1⟩) (Icc 0 T) t := by
    intro t ht
    have hd := (hX.hasDerivWithinAt ht).congr_deriv (add_zero (S.wave ⟨X t, hX.mem_domain ht⟩))
    subst huX hwX
    refine ⟨(P0.hasFDerivAt.comp_hasDerivWithinAt t hd).congr_deriv
      ((S.wave_apply_zero ⟨X t, hX.mem_domain ht⟩).trans rfl), ?_⟩
    refine (P1.hasFDerivAt.comp_hasDerivWithinAt t hd).congr_deriv ?_
    refine (S.wave_apply_one ⟨X t, hX.mem_domain ht⟩).trans ?_
    rw [LinearPMap.adjoint_apply_eq_zero_of_eq_zero (show S.d₁ = 0 from rfl), sub_zero]
    rfl
  have hcu : ContinuousOn uX (Icc 0 T) := by
    subst huX; exact P0.continuous.comp_continuousOn hX.continuousOn
  have hcw : ContinuousOn wX (Icc 0 T) := by
    subst hwX; exact P1.continuous.comp_continuousOn hX.continuousOn
  have hu0 : uX 0 = 0 := by rw [huX]; simp only [hX0]; rfl
  have hw0 : wX 0 = WithLp.toLp 2 (0, rhoBeta hΩ hb) := by rw [hwX]; simp only [hX0]; rfl
  -- `u(t) ⊥ d̃ψ` for `(τ, ψ) ∈ Γ` is conserved
  have hgauss : ∀ (τ : (bggData Ω).d0.domain) (ψ : (bggData Ω).dt0.domain),
      (bggData Ω).d0 τ = (bggData Ω).S0 ψ →
        ∀ t ∈ Icc 0 T, ⟪uX t, (bggData Ω).dt0 ψ⟫ = 0 := by
    intro τ ψ hτψ
    have hz := ((isBGG_bggData hΩ).2.1 ψ).1
    have e := opD1_dt0 hΩ hτψ
    have hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => ⟪uX s, (bggData Ω).dt0 ψ⟫) 0
        (Icc 0 T) t := by
      intro t ht
      refine (((hcomp t ht).1).inner ℝ (hasDerivWithinAt_const t (Icc 0 T)
        ((bggData Ω).dt0 ψ))).congr_deriv ?_
      rw [inner_zero_right, zero_add, inner_neg_left, neg_eq_zero,
        (bggData Ω).inner_adjoint_opD1 (dense_bgg_dt1 hΩ) _ ⟨_, hz⟩]
      have e' := congrArg WithLp.ofLp e
      rw [WeakSymmetryData.opD1_apply] at e'
      simp only [WithLp.ofLp_zero, Prod.mk_eq_zero] at e'
      rw [e'.1, e'.2, inner_zero_right, inner_zero_right, add_zero]
    have hc : ContinuousOn (fun s => ⟪uX s, (bggData Ω).dt0 ψ⟫) (Icc 0 T) :=
      fun t ht => (hd t ht).continuousWithinAt
    intro t ht
    have := constant_of_has_deriv_right_zero hc (fun x hx =>
      (hd x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)) t ht
    rw [this, hu0]
    exact inner_zero_left _
  set e := (WithLp.prodContinuousLinearEquiv 2 ℝ (L2Form Ω 2) (L2Vec Ω 2)).toContinuousLinearMap
  set e1 := (ContinuousLinearMap.fst ℝ (L2Form Ω 2) (L2Vec Ω 2)).comp e
  set e2 := (ContinuousLinearMap.snd ℝ (L2Form Ω 2) (L2Vec Ω 2)).comp e
  refine ⟨fun s => (0, uX s, (WithLp.ofLp (wX s)).1, (WithLp.ofLp (wX s)).2), ?_, ?_,
    fun t ht => ?_⟩
  · simp only [hu0, hw0]
    rfl
  · exact (continuousOn_const (c := (0 : L2Form Ω 0))).prodMk (hcu.prodMk
      ((e1.continuous.comp_continuousOn hcw).prodMk (e2.continuous.comp_continuousOn hcw)))
  · obtain ⟨hu, hw⟩ := hmem t ht
    have hW := isWave_of_orbit hΩ hu hw fun τ ψ h => hgauss τ ψ h t ht
    refine ⟨_, hW, ?_⟩
    obtain ⟨h1, h2⟩ := hcomp t ht
    have v3 : e1 ((bggData Ω).opD1 ⟨uX t, (hmem t ht).1⟩) = (bggData Ω).S1 (uX t) := by
      rw [WeakSymmetryData.opD1_apply]; rfl
    have v4 : e2 ((bggData Ω).opD1 ⟨uX t, (hmem t ht).1⟩) = (bggData Ω).dt1 ⟨uX t, hu⟩ := by
      rw [WeakSymmetryData.opD1_apply]; rfl
    have h3 := (e1.hasFDerivAt.comp_hasDerivWithinAt t h2).congr_deriv v3
    have h4 := (e2.hasFDerivAt.comp_hasDerivWithinAt t h2).congr_deriv v4
    exact (hasDerivWithinAt_const t _ _).prodMk (h1.prodMk (h3.prodMk h4))

end Orbit

/-! ### The theorem -/

/-- **With the electric boundary conditions the constraints are lost**: the TSD datum
`(0, 0, 0, ⋆β)` of `D(L)` has strong solutions on every `[0, T]`, and every one has at some
times a non-TSD `E` and a non-symmetric `B`. -/
theorem datumBeta_spec (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    (∃ V, (bggData Ω).IsWave (datumBeta hΩ hb) V) ∧ IsTSDState (datumBeta hΩ hb) ∧ ∀ T > 0,
      (∃ U, U 0 = datumBeta hΩ hb ∧
        IsStrongSolution {p | (bggData Ω).IsWave p.1 p.2} (Icc 0 T) U) ∧
      ∀ U, U 0 = datumBeta hΩ hb → IsStrongSolution {p | (bggData Ω).IsWave p.1 p.2} (Icc 0 T) U →
        (∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (U t).2.1)) ∧
        ∃ t ∈ Icc 0 T, ∃ a i, mat2 (U t).2.2.2 a i ≠ mat2 (U t).2.2.2 i a := by
  refine ⟨⟨_, isWave_datumBeta hΩ hb⟩, ⟨rfl, rfl, ?_, ?_⟩, fun T hT =>
    ⟨exists_strongSolution_datumBeta hΩ hb T, fun U hU0 hU => ?_⟩⟩
  · rw [isTSD_iff, toIx_mat1]
    change fieldE (0 : L2Vec Ω 1) ∈ tsd Ω
    rw [map_zero]; exact Submodule.zero_mem _
  · rw [isTSD_iff, toIx_mat2]
    change fieldB (rhoBeta hΩ hb) ∈ tsd Ω
    rw [rhoBeta, LinearIsometryEquiv.apply_symm_apply]; exact betaL2_mem_tsd hΩ hb
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  set PE : L2Form Ω 0 × L2Vec Ω 1 × L2Form Ω 2 × L2Vec Ω 2 →L[ℝ] L2F ℝ Ω Ix :=
    (fieldE : L2Vec Ω 1 ≃ₗᵢ[ℝ] L2F ℝ Ω Ix).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
  set PB : L2Form Ω 0 × L2Vec Ω 1 × L2Form Ω 2 × L2Vec Ω 2 →L[ℝ] L2F ℝ Ω Ix :=
    (fieldB : L2Vec Ω 2 ≃ₗᵢ[ℝ] L2F ℝ Ω Ix).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.snd ℝ _ _).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))
  obtain ⟨V0, hV0, hd0⟩ := hU.2 0 h0T
  rw [hU0] at hV0
  have hV := isWave_datumBeta_eq hΩ hb hV0
  have hE : HasDerivWithinAt (fun t => PE (U t)) (constField hΩ hb diagA) (Icc 0 T) 0 := by
    refine (PE.hasFDerivAt.comp_hasDerivWithinAt 0 hd0).congr_deriv ?_
    change fieldE V0.2.1 = _
    rw [hV, uDiag, LinearIsometryEquiv.apply_symm_apply]
  have hc : ⟪constField hΩ hb diagA, constField hΩ hb diagA⟫ ≠ 0 := by
    rw [inner_constField_diagA]
    have := volume_real_pos hΩ hb hne
    positivity
  have hcurl : ∀ t ∈ Icc 0 T, ∃ C, HasDerivWithinAt (fun t => PB (U t)) C (Icc 0 T) t ∧
      (PE (U t), C) ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).graph := by
    intro t ht
    obtain ⟨V, hV, hd⟩ := hU.2 t ht
    obtain ⟨σ, φ, u, -, hu, -, -, -, -, h4⟩ := hV
    refine ⟨PB V, PB.hasFDerivAt.comp_hasDerivWithinAt t hd, ?_⟩
    change (fieldE (U t).2.1, fieldB V.2.2.2) ∈ _
    rw [h4, ← hu]
    exact fieldE_mem_curl_minimal hΩ u
  refine ⟨?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hmem : ∀ t ∈ Icc 0 T, PE (U t) ∈ tsd₀ Ω hΩ hb := fun t ht => by
      obtain ⟨C, -, hC⟩ := hcurl t ht
      exact inf_le_tsd₀ hΩ hb ⟨(isTSD_iff _).1 (hall t ht),
        LinearPMap.mem_domain_of_mem_graph hC⟩
    have hm := Evolution.deriv_mem_of_eventually_mem_closed (isClosed_tsd₀ hΩ hb) hE
      (Evolution.neBot_nhdsWithin_Icc_diff hT h0T) (eventually_nhdsWithin_of_forall hmem)
      (hmem 0 h0T)
    exact hc ((Submodule.mem_orthogonal' _ _).1
      (constField_mem_orthogonal_tsd₀ hΩ hb diagA) _ hm)
  · obtain ⟨t, ht, hB⟩ := exists_not_symm_of_path hΩ hb hT hE hcurl hc
    refine ⟨t, ht, ?_⟩
    by_contra h
    push Not at h
    exact hB fun i j => h i j

end FEEC

