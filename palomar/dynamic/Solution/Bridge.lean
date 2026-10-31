module

public import Solution.Defs
public import Feec.HilbertComplex.Approximation.Crown

/-!
# The bridge from the challenge to `Feec`

The vocabulary of `Challenge.lean` restates over Mathlib the objects of `Feec`: a Hilbert complex
of the challenge is a `Feec.HilbertComplex` on `ComplexShape.up ℤ` (`HilbertComplex.toFeec`, the
same fields), and so are its subcomplexes, cochain projections and families of subcomplexes
(`SubcomplexFamily.toFeec`). The approximation property in the graph norm in the degrees of a
window makes the window of the family a `Feec.HilbertComplex.ConstrainedFEEC`
(`SubcomplexFamily.windowFEEC`), and the graph-norm bounds of the projections in the window are
those of `Feec` (`SubcomplexFamily.isGraphBounded_window`). This module identifies the challenge's
window operators and discrete operators with those of `Feec`, and turns the verdicts of
`Feec.HilbertComplex.approxFEEC`, `Feec.HilbertComplex.dissipFEEC_fullyDiscrete`,
`Feec.HilbertComplex.ConstrainedFEEC.heatFEEC` and the conforming rate
`Feec.HilbertComplex.ConstrainedFEEC.rate_le` into the conclusions of the challenge
(`SubcomplexFamily.waveVerdict`, `SubcomplexFamily.heatVerdict`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015], §4.4–§4.6, §4.10

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W)

/-! ### The complex, its subcomplexes and conforming families in `Feec` -/

/-- The complex as a `Feec` Hilbert complex on `ComplexShape.up ℤ`. -/
def toFeec : Feec.HilbertComplex 𝕜 (ComplexShape.up ℤ) W where
  d := H.d
  shape := H.shape
  dense := H.dense
  closed := H.closed
  mapsTo := H.mapsTo
  d_comp_d := H.d_comp_d

theorem rel_sub_one (i : ℤ) : (ComplexShape.up ℤ).Rel (i - 1) i := sub_add_cancel i 1

theorem boundaries_eq (i : ℤ) : H.toFeec.boundaries i = H.boundaries i :=
  H.toFeec.boundaries_eq (rel_sub_one i)

theorem closedRangeAt_iff (i : ℤ) :
    H.toFeec.ClosedRangeAt i ↔ IsClosed (H.boundaries i : Set (W i)) := by
  rw [Feec.HilbertComplex.ClosedRangeAt, boundaries_eq]

namespace Subcomplex

variable {H} (S : H.Subcomplex)

/-- The subcomplex as a `Feec` subcomplex. -/
def toFeec : H.toFeec.Subcomplex := ⟨S.V, S.le_domain, S.mapsTo⟩

instance [∀ i, FiniteDimensional 𝕜 (S.V i)] (i : ℤ) : FiniteDimensional 𝕜 (S.toFeec.V i) :=
  ‹∀ i, FiniteDimensional 𝕜 (S.V i)› i

/-- The cochain projection as a `Feec` cochain projection. -/
def CochainProjection.toFeec {S : H.Subcomplex} (P : S.CochainProjection) :
    S.toFeec.CochainProjection :=
  ⟨P.π, P.mem, P.proj, P.comm⟩

end Subcomplex

variable {H} {κ : Type*}

/-- The family of subcomplexes as a `Feec` family of subcomplexes. -/
def SubcomplexFamily.toFeec (F : H.SubcomplexFamily κ) :
    Feec.HilbertComplex.SubcomplexFamily H.toFeec κ where
  l := F.l
  V h := (F.V h).toFeec
  finiteDimensional h i := F.finiteDimensional h i
  π h := (F.π h).toFeec

/-- **The subcomplex `Vₕ` alone** as a `Feec` family over `Unit` (along `⊥`): the setting of the
per-`h` error bound (`SubcomplexFamily.error_le`). -/
def SubcomplexFamily.single (F : H.SubcomplexFamily κ) (h : κ) :
    Feec.HilbertComplex.SubcomplexFamily H.toFeec Unit where
  l := ⊥
  V _ := (F.V h).toFeec
  finiteDimensional _ i := F.finiteDimensional h i
  π _ := (F.π h).toFeec

end HilbertComplex

/-! ### Evolutions -/

section Evolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {κ : Type*}

omit [CompleteSpace E] [IsScalarTower ℝ 𝕜 E] in
theorem IsStrongSolution.congr {A : E →ₗ.[𝕜] E} {I : Set ℝ} {u v : ℝ → E}
    (hu : IsStrongSolution A I u) (h : EqOn v u I) : IsStrongSolution A I v :=
  ⟨hu.1.congr h, fun t ht => by
    obtain ⟨w, hw, hd⟩ := hu.2 t ht
    exact ⟨w, h ht ▸ hw, hd.congr h (h ht)⟩⟩

omit [CompleteSpace E] [IsScalarTower ℝ 𝕜 E] in
theorem isStrongSolution_iff {A : E →ₗ.[𝕜] E} {I : Set ℝ} {u : ℝ → E} :
    IsStrongSolution A I u ↔ Feec.Evolution.IsStrongSolution A I 0 u := by
  refine ⟨fun h => ⟨h.1, fun t ht => ?_⟩, fun h => ⟨h.continuousOn, fun t ht => ?_⟩⟩
  · obtain ⟨v, hv, hd⟩ := h.2 t ht
    exact ⟨v, hv, by simpa using hd⟩
  · obtain ⟨v, hv, hd⟩ := h.deriv t ht
    exact ⟨v, hv, by simpa using hd⟩

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- A dissipative `B` has no nonzero `z = c B z` with `c ≥ 0`. -/
theorem eq_zero_of_eq_smul {B : E →L[𝕜] E} (hB : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0) {c : ℝ}
    (hc : 0 ≤ c) {z : E} (hz : z = (c : 𝕜) • B z) : z = 0 := by
  have h : ⟪z, z⟫_𝕜 = ⟪(c : 𝕜) • B z, z⟫_𝕜 := by rw [← hz]
  rw [inner_smul_left, RCLike.conj_ofReal] at h
  have h' := congrArg RCLike.re h
  rw [RCLike.re_ofReal_mul, inner_self_eq_norm_sq] at h'
  have : ‖z‖ ^ 2 ≤ 0 := h' ▸ mul_nonpos_of_nonneg_of_nonpos hc (hB z)
  exact norm_eq_zero.1 (by nlinarith [norm_nonneg z])

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **The θ-iterates are the powers of the θ-step** `r_θ(τ B)` for a dissipative `B`. -/
theorem theta_eq_pow {B : E →L[𝕜] E} (hB : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0) {θ τ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hτ : 0 < τ) {w : ℕ → E}
    (hw : ∀ n, w (n + 1) - w n = (τ : 𝕜) • B ((θ : 𝕜) • w (n + 1) + (1 - (θ : 𝕜)) • w n))
    (n : ℕ) :
    w n = (Feec.TimeStepping.thetaStep ((B : E →ₗ[𝕜] E).toPMap ⊤) (θ : 𝕜) τ ^ n) (w 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ← ih]
    set u' := Feec.TimeStepping.thetaStep ((B : E →ₗ[𝕜] E).toPMap ⊤) (θ : 𝕜) τ (w n)
    obtain ⟨_, hu'⟩ := Feec.TimeStepping.isThetaStep_thetaStep_of_isMDissipative
      (θ := (θ : 𝕜)) (B.isMDissipative_toPMap_top hB) (by rw [RCLike.ofReal_re]; linarith) hτ (w n)
    change u' - w n = (τ : 𝕜) • B ((θ : 𝕜) • u' + (1 - (θ : 𝕜)) • w n) at hu'
    refine sub_eq_zero.1 (eq_zero_of_eq_smul hB (mul_nonneg hτ.le (by linarith : (0 : ℝ) ≤ θ)) ?_)
    calc w (n + 1) - u' = (w (n + 1) - w n) - (u' - w n) := by abel
      _ = (τ : 𝕜) • (B ((θ : 𝕜) • w (n + 1) + (1 - (θ : 𝕜)) • w n) -
          B ((θ : 𝕜) • u' + (1 - (θ : 𝕜)) • w n)) := by rw [hw n, hu', smul_sub]
      _ = (τ : 𝕜) • B ((θ : 𝕜) • (w (n + 1) - u')) := by
        rw [← _root_.map_sub, smul_sub]; congr 2; abel
      _ = ((τ * θ : ℝ) : 𝕜) • B (w (n + 1) - u') := by
        rw [_root_.map_smul, smul_smul, RCLike.ofReal_mul]

omit [IsScalarTower ℝ 𝕜 E] in
/-- **The evolution verdict from `Feec`'s**: the conclusions of the dissipative and fully discrete
FEEC theorems, restated. -/
theorem evolutionVerdict_of {A : E →ₗ.[𝕜] E} {l : Filter κ} {X : κ → Submodule 𝕜 E}
    [∀ h, CompleteSpace (X h)] {B : ∀ h, X h →L[𝕜] X h} {S S' : ℝ → E →L[𝕜] E} (hSS' : ∀ t, 0 ≤ t → S t = S' t)
    (hA : A.IsMDissipative)
    (hB : ∀ h x, RCLike.re ⟪B h x, x⟫_𝕜 ≤ 0)
    (hsol : ∀ (x : A.domain) (T : ℝ),
      Feec.Evolution.IsClassicalSolution A (Icc 0 T) 0 fun t => S' t x)
    (huniq : ∀ (x : A.domain) (T : ℝ) (U : ℝ → E), U 0 = x →
      Feec.Evolution.IsStrongSolution A (Icc 0 T) 0 U → EqOn U (fun t => S' t x) (Icc 0 T))
    (hanti : ∀ x, AntitoneOn (fun t => ‖S' t x‖) (Ici 0)) (hS0 : ∀ x, S' 0 x = x)
    (hconv : ∀ (x : E) (v : ∀ h, X h), Tendsto (fun h => (v h : E)) l (𝓝 x) → ∀ T : ℝ,
      TendstoUniformlyOn (fun h t => ((Feec.C0Group.ofBounded (B h)).S t (v h) : E))
        (fun t => S' t x) l (Icc 0 T))
    (htheta : ∀ (θ : ℝ) (_ : 1 / 2 ≤ θ) (τ : κ → ℝ) (_ : ∀ h, 0 < τ h), Tendsto τ l (𝓝 0) →
      ∀ (x : E) (v : ∀ h, X h), Tendsto (fun h => (v h : E)) l (𝓝 x) → ∀ (T ε : ℝ), 0 < ε →
        ∀ᶠ h in l, ∀ n : ℕ, (n : ℝ) * τ h ∈ Icc 0 T →
          ‖S' (n * τ h) x - ((Feec.TimeStepping.thetaStep ((B h : X h →ₗ[𝕜] X h).toPMap ⊤)
            (θ : 𝕜) (τ h) ^ n) (v h) : E)‖ < ε) :
    EvolutionVerdict A l X B S where
  dense := hA.dense_domain
  solution x hx T := (isStrongSolution_iff.2 (hsol ⟨x, hx⟩ T).toIsStrongSolution).congr
    fun t ht => by simp only [hSS' t ht.1]
  unique x hx T u hu0 hu := fun t ht => by
    simp only [hSS' t ht.1]; exact huniq ⟨x, hx⟩ T u hu0 (isStrongSolution_iff.1 hu) ht
  initial x := by rw [hSS' 0 le_rfl]; exact hS0 x
  contraction x t ht := by
    have := hanti x (Set.mem_Ici.2 le_rfl) ht ht
    dsimp only at this
    rwa [hS0, ← hSS' t ht] at this
  semidiscrete x v hv T := by
    simpa only [semiflow, Feec.C0Group.ofBounded_S] using
      (hconv x v hv T).congr_right fun t ht => by simp only [hSS' t ht.1]
  theta θ hθ τ hτ hτ0 x w hw hw0 T ε hε := by
    filter_upwards [htheta θ hθ τ hτ hτ0 x (fun h => w h 0) hw0 T ε hε] with h hh n hn
    rw [theta_eq_pow (hB h) hθ (hτ h) (hw h) n, hSS' _ hn.1]
    exact hh n hn
  theta_temporal θ hθ h τ hτ w hw n := by
    rw [theta_eq_pow (hB h) hθ hτ hw n, norm_sub_rev]
    exact Feec.TimeStepping.norm_thetaStep_pow_sub_exp_le (hB h) hθ hτ n (w 0)
  crankNicolson_temporal h τ hτ w hw n := by
    have e1 : ((1 / 2 : ℝ) : 𝕜) = 1 / 2 := by push_cast; ring
    have e2 : (1 - (1 / 2 : 𝕜)) = 1 / 2 := by ring
    have hw' : ∀ n, w (n + 1) - w n = (τ : 𝕜) •
        B h (((1 / 2 : ℝ) : 𝕜) • w (n + 1) + (1 - ((1 / 2 : ℝ) : 𝕜)) • w n) := fun n => by
      rw [hw n, e1, e2, smul_add]
    rw [theta_eq_pow (hB h) le_rfl hτ hw' n, norm_sub_rev,
      ← Feec.TimeStepping.cayley_half_eq_thetaStep]
    exact Feec.TimeStepping.norm_cayley_pow_sub_exp_le (hB h) hτ n (w 0)

end Evolution

/-! ### Windows -/

namespace HilbertComplex

section Window

variable (H : HilbertComplex 𝕜 W) (a : ℤ) (m : ℕ)

theorem totalD_eq : H.totalD a m = (H.toFeec.window a m).totalD := by
  refine LinearPMap.ext rfl fun x hx hy => ?_
  ext j
  rw [Feec.HilbertComplex.totalD_apply]
  rfl

theorem wave_eq : H.wave a m = (H.toFeec.window a m).wave := by
  rw [wave, totalD_eq, Feec.HilbertComplex.wave_eq]

omit [∀ i, CompleteSpace (W i)] in
theorem sq_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : sq A = A.sq := by
  have hd : (sq A).domain = A.sq.domain := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      exact ⟨hx, hy⟩
    · rintro ⟨hx, hAx⟩
      exact ⟨Submodule.mem_map.2 ⟨⟨x, hx⟩, hAx, rfl⟩, hx⟩
  exact LinearPMap.ext hd fun x hx hy => rfl

theorem heat_eq : sq (H.wave a m) = -(H.toFeec.window a m).hodgeLaplacian := by
  rw [sq_eq, wave_eq, Feec.HilbertComplex.hodgeLaplacian, neg_neg]

/-- Closed ranges of `H` in the degrees `a + 1, …, a + m - 1` give closed ranges of the window. -/
theorem closedRangeAt_window
    (hcr : ∀ i : Fin m, 0 < (i : ℕ) → IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ)))))
    (i : Fin m) :
    (H.toFeec.window a m).ClosedRangeAt i := by
  by_cases hi : (ComplexShape.window m).Rel ((ComplexShape.window m).prev i) i
  · rw [Feec.HilbertComplex.ClosedRangeAt, Feec.HilbertComplex.boundaries_eq _ hi]
    have hrel : (ComplexShape.up ℤ).Rel (a + (((ComplexShape.window m).prev i : Fin m) : ℕ))
        (a + ((i : ℕ) : ℤ)) := by
      change _ + 1 = _
      rw [ComplexShape.window_rel] at hi
      omega
    have hi0 : 0 < (i : ℕ) := by rw [ComplexShape.window_rel] at hi; omega
    have := (H.closedRangeAt_iff _).2 (hcr i hi0)
    rwa [Feec.HilbertComplex.ClosedRangeAt, H.toFeec.boundaries_eq hrel] at this
  · rw [Feec.HilbertComplex.ClosedRangeAt, Feec.HilbertComplex.boundaries_eq_bot_of_not_rel _ hi,
      Submodule.bot_coe]
    exact isClosed_singleton

/-- **The window of a `Feec` family of subcomplexes, approximating in the graph norm in every
degree of the window, with a closed constraint**, a constrained FEEC discretization. -/
def windowFEEC {ι' : Type*} (G : Feec.HilbertComplex.SubcomplexFamily H.toFeec ι')
    (hG : ∀ i, (G.window a m).Approximates i) (K : Submodule 𝕜 (Total W a m))
    (hK : IsClosed (K : Set (Total W a m))) :
    Feec.HilbertComplex.ConstrainedFEEC (H.toFeec.window a m) ι' where
  toSubcomplexFamily := G.window a m
  approximates := hG
  K := K
  isClosed_K := hK

/-- The degree after `a + i` is `a + (i + 1)`. -/
theorem add_succ (i : ℕ) : a + (i : ℤ) + 1 = a + ((i + 1 : ℕ) : ℤ) := by push_cast; ring

variable {H} {κ : Type*} (F : H.SubcomplexFamily κ)

/-- The approximation property in degree `i`, read in the graph norm of `d i j`, `j = i + 1`. -/
theorem SubcomplexFamily.Approximates.of_eq {i j : ℤ} (hj : i + 1 = j) (hA : F.Approximates i)
    (x : (H.d i j).domain) :
    Tendsto (fun h => (F.V h).graphDist i j x (H.d i j x)) F.l (𝓝 0) := by
  subst hj; exact hA x

/-- **Eventually a graph-norm `ε`-approximation** in `Vₕⁱ`. -/
theorem SubcomplexFamily.Approximates.eventually {i j : ℤ} (hj : i + 1 = j)
    (hA : F.Approximates i) (x : (H.d i j).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in F.l, ∃ v : (F.V h).V i, ‖(x : W i) - v‖ +
      ‖H.d i j x - H.d i j ⟨v, (F.V h).le_domain i j v.2⟩‖ < ε := by
  filter_upwards [(tendsto_order.1 (hA.of_eq F hj x)).2 ε hε] with h hh
  exact exists_lt_of_ciInf_lt hh

/-- **The window of the family approximates in the graph norm in every degree of the window**:
in a degree with a successor in the window, by the approximation property in the graph norm; in
the last degree (no differential in the window), by the approximation property in `W`. -/
theorem SubcomplexFamily.approximates_window
    (happrox : ∀ i : Fin m, (i : ℕ) + 1 < m → F.Approximates (a + (i : ℕ)))
    (happrox' : ∀ i : Fin m, (i : ℕ) + 1 = m → ∀ x : W (a + (i : ℕ)),
      Tendsto (fun h => Metric.infDist x ((F.V h).V (a + (i : ℕ)))) F.l (𝓝 0))
    (i : Fin m) : (F.toFeec.window a m).Approximates i := by
  intro σ
  refine tendsto_order.2 ⟨fun b hb => Eventually.of_forall fun _ => hb.trans_le
    Metric.infDist_nonneg, fun ε hε => ?_⟩
  by_cases hi : (i : ℕ) + 1 < m
  · have hij : (ComplexShape.window m).Rel i ⟨(i : ℕ) + 1, hi⟩ := rfl
    filter_upwards [(happrox i hi).eventually F (add_succ a i)
      ((H.toFeec.window a m).domainCoord i ⟨(i : ℕ) + 1, hi⟩ σ) hε] with h ⟨v, hv⟩
    have := (F.toFeec.window a m).finiteDimensional h
    exact (Feec.HilbertComplex.Subcomplex.infDist_domainSub_le ((F.toFeec.window a m).V h) hij σ
      (v := (v : W (a + (i : ℕ)))) v.2).trans_lt hv
  · have hni : ∀ k, ¬ (ComplexShape.window m).Rel i k := fun k hk => by
      rw [ComplexShape.window_rel] at hk; omega
    filter_upwards [(tendsto_order.1 (happrox' i (by omega)
      ((H.toFeec.window a m).domainIncl i σ))).2 ε hε] with h hh
    obtain ⟨v, hv, hvd⟩ := (Metric.infDist_lt_iff ⟨0, Submodule.zero_mem _⟩).1 hh
    have := (F.toFeec.window a m).finiteDimensional h
    have hz : ∀ z, (H.toFeec.window a m).d i ((ComplexShape.window m).next i) z = 0 :=
      fun z => (H.toFeec.window a m).apply_eq_zero_of_not_rel (hni _) z
    refine (Feec.HilbertComplex.Subcomplex.infDist_domainSub_le_of_next
      ((F.toFeec.window a m).V h) σ (v := v) hv).trans_lt ?_
    rw [hz, hz, sub_zero, norm_zero, add_zero, ← dist_eq_norm]
    exact hvd

/-- The graph-norm bound in degree `i`, read in the graph norm of `d i j`, `j = i + 1`. -/
theorem SubcomplexFamily.IsGraphBounded.of_eq {i j : ℤ} (hj : i + 1 = j) (hb : F.IsGraphBounded i) :
    ∃ C : ℝ, ∀ (h : κ) (x : (H.d i j).domain), ‖(F.π h).π i x‖ +
      ‖H.d i j ⟨(F.π h).π i x, (F.V h).le_domain i j ((F.π h).mem i x)⟩‖ ≤
        C * (‖(x : W i)‖ + ‖H.d i j x‖) := by
  subst hj; exact hb

/-- **The projections of the window are bounded in the graph norm in every degree of the
window**: in a degree with a successor in the window by the graph-norm bound, in the last degree
(no differential in the window) by the bound in `W`. -/
theorem SubcomplexFamily.isGraphBounded_window
    (hπ : ∀ i : Fin m, (i : ℕ) + 1 < m → F.IsGraphBounded (a + (i : ℕ)))
    (hπ' : ∀ i : Fin m, (i : ℕ) + 1 = m →
      ∃ C : ℝ, ∀ (h : κ) (x : W (a + (i : ℕ))), ‖(F.π h).π _ x‖ ≤ C * ‖x‖)
    (i : Fin m) : (F.toFeec.window a m).IsGraphBounded i := by
  by_cases hi : (i : ℕ) + 1 < m
  · have hij : (ComplexShape.window m).Rel i ⟨(i : ℕ) + 1, hi⟩ := rfl
    obtain ⟨C, hC⟩ := (hπ i hi).of_eq F (add_succ a i)
    refine ⟨√2 * |C|, fun h => ?_⟩
    show ((F.toFeec.window a m).π h).IsGraphBounded i ((ComplexShape.window m).next i) (√2 * |C|)
    rw [ComplexShape.next_eq' _ hij]
    exact Feec.HilbertComplex.Subcomplex.CochainProjection.isGraphBounded_of_add_le _ fun x =>
      (hC h x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  · have hni : ¬ (ComplexShape.window m).Rel i ((ComplexShape.window m).next i) := fun hk => by
      rw [ComplexShape.window_rel] at hk; omega
    obtain ⟨C, hC⟩ := hπ' i (by omega)
    refine ⟨|C|, fun h x => ?_⟩
    have hz : ∀ z, (H.toFeec.window a m).d i ((ComplexShape.window m).next i) z = 0 :=
      fun z => (H.toFeec.window a m).apply_eq_zero_of_not_rel hni z
    rw [hz, hz, norm_zero, sq_abs]
    have h1 : ‖(F.π h).π (a + (i : ℕ)) x‖ ≤ |C| * ‖(x : W (a + (i : ℕ)))‖ :=
      (hC h x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, sq_abs] at h2
    change ‖(F.π h).π (a + (i : ℕ)) x‖ ^ 2 + 0 ^ 2 ≤ C ^ 2 * (‖(x : W (a + (i : ℕ)))‖ ^ 2 + 0 ^ 2)
    nlinarith

end Window

end HilbertComplex

/-! ### The wave and heat verdicts -/

omit [∀ i, CompleteSpace (W i)] in
theorem isReducing_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    IsReducing A K ↔ A.IsReducing K :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun h x => ⟨h.proj_mem x, h.comm x⟩⟩

namespace HilbertComplex.SubcomplexFamily

variable {H : HilbertComplex 𝕜 W} {κ : Type*} (F : H.SubcomplexFamily κ) (a : ℤ) (m : ℕ)
  (happrox : ∀ i, (F.toFeec.window a m).Approximates i)
  (K : Submodule 𝕜 (Total W a m)) (hK : IsClosed (K : Set (Total W a m)))

instance (h : κ) : CompleteSpace (F.Xh a m h) := FiniteDimensional.complete 𝕜 _

/-- The window of `F` with the constraint `K`, a constrained FEEC discretization. -/
abbrev feecWindow : Feec.HilbertComplex.ConstrainedFEEC (H.toFeec.window a m) κ :=
  windowFEEC H a m F.toFeec happrox K hK

/-- The subcomplex `Vₕ` alone on the window, a constrained FEEC discretization over `Unit`. -/
abbrev singleWindow (h : κ) : Feec.HilbertComplex.ConstrainedFEEC (H.toFeec.window a m) Unit :=
  windowFEEC H a m (F.single h) (fun _ _ => tendsto_bot) ⊤
    (by rw [Submodule.top_coe]; exact isClosed_univ)

theorem Dh_eq (h : κ) : F.Dh a m h = (F.feecWindow a m happrox K hK).discreteD h :=
  ContinuousLinearMap.ext fun _ => Subtype.ext (LinearPMap.apply_eq_of_eq (H.totalD_eq a m) _ _ rfl)

theorem Lh_eq (h : κ) : F.Lh a m h = (F.feecWindow a m happrox K hK).discreteWave h := by
  rw [Lh, F.Dh_eq a m happrox K hK]
  rfl

theorem Lh_sq_eq (h : κ) :
    (F.Lh a m h ^ 2 : F.Xh a m h →L[𝕜] F.Xh a m h) = (F.feecWindow a m happrox K hK).heatGen h := by
  set G := F.feecWindow a m happrox K hK
  set D := G.discreteD h
  have hdh : (G.totalSubcomplex h).dh () () = D := ContinuousLinearMap.ext fun _ => rfl
  have hD : D * D = 0 := ContinuousLinearMap.ext fun x => Subtype.ext
    ((H.toFeec.window a m).totalD_comp_totalD ⟨x, G.Xh_mem_domain h x⟩)
  have hD' : D.adjoint * D.adjoint = 0 := by
    rw [ContinuousLinearMap.mul_def, ← ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.mul_def, hD]
    exact LinearIsometryEquiv.map_zero _
  rw [pow_two, F.Lh_eq a m happrox K hK]
  show (G.discreteWave h * G.discreteWave h : G.Xh h →L[𝕜] G.Xh h) = _
  rw [Feec.HilbertComplex.ConstrainedFEEC.discreteWave, sub_mul,
    mul_sub, mul_sub, hD, hD', Feec.HilbertComplex.ConstrainedFEEC.heatGen,
    Feec.HilbertComplex.Subcomplex.laplacian, hdh, ← ContinuousLinearMap.mul_def,
    ← ContinuousLinearMap.mul_def]
  abel

omit [∀ i, CompleteSpace (W i)] in
theorem isClosed_top : IsClosed ((⊤ : Submodule 𝕜 (Total W a m)) : Set (Total W a m)) := by
  rw [Submodule.top_coe]; exact isClosed_univ

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem Lh_single (h : κ) : F.Lh a m h =
    (F.singleWindow a m h).discreteWave () := by
  have hD : F.Dh a m h = (F.singleWindow a m h).discreteD () :=
    ContinuousLinearMap.ext fun _ => Subtype.ext (LinearPMap.apply_eq_of_eq (H.totalD_eq a m) _ _ rfl)
  rw [Lh, hD]
  rfl

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem graphDist_nonneg (h : κ) (y : (H.totalD a m).domain) : 0 ≤ F.graphDist a m h y :=
  le_ciInf fun _ => by positivity

/-- **The per-`h` error bound with slack** `δ > 0`, from the conforming rate
`Feec.HilbertComplex.ConstrainedFEEC.rate_le` on the subcomplex `Vₕ` alone (`SubcomplexFamily.single`), for the
rate class of the single datum `x` with norm `M + δ`. -/
theorem error_le_add (x : Total W a m) (hx : x ∈ (H.wave a m).domain)
    (hx2 : H.wave a m ⟨x, hx⟩ ∈ (H.wave a m).domain) (h : κ) (v : F.Xh a m h) {t M δ : ℝ}
    (ht : 0 ≤ t) (hδ : 0 < δ)
    (hM : ∀ s ∈ Icc 0 t, ∀ y : (H.totalD a m).domain,
      (y : Total W a m) = (H.toFeec.window a m).waveGroup.S s x ∨
        (y : Total W a m) = (H.toFeec.window a m).waveGroup.S s (H.wave a m ⟨x, hx⟩) →
        F.graphDist a m h y ≤ M) :
    ‖(H.toFeec.window a m).waveGroup.S t x - (semiflow (F.Lh a m h) t v : Total W a m)‖ ≤
      ‖(v : Total W a m) - x‖ +
        2 * (1 + Feec.HilbertComplex.ellipticConst (H.toFeec.window a m)) * (1 + t) * (M + δ) := by
  set H' := H.toFeec.window a m
  set G := F.singleWindow a m h
  have hx' : x ∈ H'.wave.domain := by rw [← H.wave_eq a m]; exact hx
  have eL : H.wave a m ⟨x, hx⟩ = H'.wave ⟨x, hx'⟩ :=
    LinearPMap.apply_eq_of_eq (H.wave_eq a m) _ _ rfl
  have hx2' : H'.wave ⟨x, hx'⟩ ∈ H'.wave.domain := by rw [← eL, ← H.wave_eq a m]; exact hx2
  -- every graph-space lift of a point of the two orbits is within `M + δ` of `Kₕ`
  have happ : ∀ s ∈ Icc 0 t, ∀ ζ : H'.totalD.GraphSpace,
      (H'.totalD.graphFst ζ = H'.waveGroup.S s x ∨
        H'.totalD.graphFst ζ = H'.waveGroup.S s (H'.wave ⟨x, hx'⟩)) →
      ∃ w ∈ G.Kh (), ‖ζ - w‖ ≤ 1 * (1 : ℝ) ^ (1 : ℝ) * (M + δ) := by
    intro s hs ζ hζ
    obtain ⟨z, rfl, -, -⟩ := H'.totalD.exists_toGraphSpace_eq ζ
    have hz : (z : Total W a m) ∈ (H.totalD a m).domain := by rw [H.totalD_eq a m]; exact z.2
    have hd := hM s hs ⟨z, hz⟩ (by rw [← eL] at hζ; exact hζ)
    obtain ⟨w, hw⟩ := exists_lt_of_ciInf_lt (hd.trans_lt (lt_add_of_pos_right M hδ))
    refine ⟨G.liftXh () w, G.liftXh_mem () w, ?_⟩
    rw [Real.one_rpow, one_mul, one_mul]
    refine le_of_lt (lt_of_le_of_lt ?_ hw)
    change ‖H'.totalD.toGraphSpace z - H'.totalD.toGraphSpace ⟨w, _⟩‖ ≤ _
    rw [← LinearPMap.toGraphSpace_sub]
    refine (LinearPMap.norm_toGraphSpace_le _ _).trans (le_of_eq ?_)
    rw [LinearPMap.map_sub, LinearPMap.apply_eq_of_eq (H.totalD_eq a m) ⟨(z : Total W a m), hz⟩ z rfl,
      LinearPMap.apply_eq_of_eq (H.totalD_eq a m) ⟨(w : Total W a m), F.Xh_le a m h w.2⟩ _ rfl]
    rfl
  -- the rate class of the single datum `x`
  let R : G.RateClass t :=
    { Data := {x}
      classNorm := fun _ => M + δ
      meshSize := fun _ => 1
      α := 1
      C := 1
      mem_domain := fun y hy => by rw [hy]; exact hx'
      mem_domain_sq := fun y hy hyx => by
        obtain rfl : y = x := hyx
        exact hx2'
      approx := fun y hy _ s hs ζ hζ => by
        obtain rfl : y = x := hy
        exact happ s hs ζ (Or.inl hζ)
      approx_deriv := fun y hy hyx _ s hs ζ hζ => by
        obtain rfl : y = x := hyx
        exact happ s hs ζ (Or.inr hζ) }
  have hr := G.rate_le R rfl () ⟨ht, le_rfl⟩
  simp only [R, Real.one_rpow, one_mul] at hr
  set ζ := Feec.HilbertComplex.waveLift H' ⟨x, hx'⟩
  set P : F.Xh a m h := G.ellipticProj () ζ
  -- the discrete solution is the semiflow of the elliptic projection
  have hsol : H'.totalD.graphFst (G.discrete () ζ t) = (semiflow (F.Lh a m h) t P : Total W a m) := by
    rw [← G.toApprox_sol, Feec.HilbertComplex.ConstrainedFEEC.toApprox_sol_eq, F.Lh_single a m h]
    rfl
  rw [hsol] at hr
  -- the initial error
  obtain ⟨w0, hw0, hw0b⟩ := happ 0 ⟨le_rfl, ht⟩ ζ (Or.inl (by
    rw [Feec.C0Group.S_zero_apply]; rfl))
  rw [Real.one_rpow, one_mul, one_mul] at hw0b
  have hP := G.norm_graphFst_sub_ellipticProj_le () ζ hw0
  have hCP := Feec.HilbertComplex.ellipticConst_nonneg H'
  -- `semiflow` is unitary
  have hiso : ‖(semiflow (F.Lh a m h) t (P - v) : Total W a m)‖ = ‖P - v‖ := by
    rw [F.Lh_single a m h]
    exact Feec.C0Group.isIsometric_ofBounded (G.discreteWave_skew ()) t (P - v)
  have e1 : ‖(H'.waveGroup.S t x : Total W a m) - (semiflow (F.Lh a m h) t v : Total W a m)‖ ≤
      ‖H'.waveGroup.S t x - (semiflow (F.Lh a m h) t P : Total W a m)‖ +
        ‖(semiflow (F.Lh a m h) t (P - v) : Total W a m)‖ := by
    rw [_root_.map_sub, Submodule.coe_sub]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have e2 : ‖P - v‖ ≤ ‖(P : Total W a m) - x‖ + ‖(v : Total W a m) - x‖ := by
    rw [← Submodule.norm_coe, Submodule.coe_sub]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _ |>.trans (by rw [norm_sub_rev (x : Total W a m)])
  have e3 : ‖(P : Total W a m) - x‖ ≤ (1 + Feec.HilbertComplex.ellipticConst H') * (M + δ) := by
    rw [norm_sub_rev]
    exact hP.trans (mul_le_mul_of_nonneg_left hw0b (by linarith))
  rw [hiso] at e1
  nlinarith

/-- **The per-`h` error bound** `‖S(t) x - exp(t Lₕ) v‖ ≤ ‖v - x‖ + 2 (1 + C_P) (1 + t) M`,
`C_P = 4√3` (`error_le_add` with `δ → 0`, `Feec.HilbertComplex.ellipticConst_le`). -/
theorem error_le (x : Total W a m) (hx : x ∈ (H.wave a m).domain)
    (hx2 : H.wave a m ⟨x, hx⟩ ∈ (H.wave a m).domain) (h : κ) (v : F.Xh a m h) {t M : ℝ}
    (ht : 0 ≤ t)
    (hM : ∀ s ∈ Icc 0 t, ∀ y : (H.totalD a m).domain,
      (y : Total W a m) = (H.toFeec.window a m).waveGroup.S s x ∨
        (y : Total W a m) = (H.toFeec.window a m).waveGroup.S s (H.wave a m ⟨x, hx⟩) →
        F.graphDist a m h y ≤ M) :
    ‖(H.toFeec.window a m).waveGroup.S t x - (semiflow (F.Lh a m h) t v : Total W a m)‖ ≤
      ‖(v : Total W a m) - x‖ + 2 * (1 + 4 * √3) * (1 + t) * M := by
  have hM0 : 0 ≤ M := by
    have hxD : x ∈ (H.totalD a m).domain := by
      rw [H.totalD_eq a m]; exact ((H.toFeec.window a m).mem_wave_domain.1 (H.wave_eq a m ▸ hx)).1
    refine (F.graphDist_nonneg a m h ⟨x, hxD⟩).trans (hM 0 ⟨le_rfl, ht⟩ ⟨x, hxD⟩ (Or.inl ?_))
    rw [Feec.C0Group.S_zero_apply]
  set c := 2 * (1 + Feec.HilbertComplex.ellipticConst (H.toFeec.window a m)) * (1 + t)
  have hc : 0 < c := by have := Feec.HilbertComplex.ellipticConst_nonneg (H.toFeec.window a m); positivity
  have hcc : c * M ≤ 2 * (1 + 4 * √3) * (1 + t) * M := by
    have := Feec.HilbertComplex.ellipticConst_le (H.toFeec.window a m)
    have : c ≤ 2 * (1 + 4 * √3) * (1 + t) := by
      simp only [c]
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_right this hM0
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have h1 := F.error_le_add a m x hx hx2 h v ht (div_pos hε (by linarith : (0 : ℝ) < 2 * c)) hM
  have : c * (M + ε / (2 * c)) = c * M + ε / 2 := by field_simp
  linarith

include happrox in
/-- **The wave verdict** from `Feec`'s approximating, skew-adjoint and fully discrete FEEC
theorems on the window and the per-`h` error bound (`error_le`). -/
theorem waveVerdict : ∃ S, F.WaveVerdict a m S := by
  set G := F.feecWindow a m happrox ⊤ (isClosed_top a m)
  have V := Feec.HilbertComplex.approxFEEC G.toApprox G.toCore
  have hprop : ∀ (K : Submodule 𝕜 (Total W a m)) [K.HasOrthogonalProjection],
      IsReducing (H.wave a m) K ↔ ∀ t, ∀ x ∈ K, G.toApprox.U t x ∈ K := fun K _ => by
    have hK : IsClosed (K : Set (Total W a m)) := by
      rw [← K.orthogonal_orthogonal]; exact Kᗮ.isClosed_orthogonal
    have VK := Feec.HilbertComplex.approxFEEC (F.feecWindow a m happrox K hK).toApprox
      (F.feecWindow a m happrox K hK).toCore
    rw [isReducing_iff, H.wave_eq a m]
    exact VK.isReducing_iff_invariant
  have hL : F.Lh a m = fun h => G.discreteWave h := funext (F.Lh_eq a m happrox ⊤ (isClosed_top a m))
  have hEV : EvolutionVerdict (H.wave a m) F.l (F.Xh a m) (F.Lh a m) G.toApprox.U := by
    rw [H.wave_eq a m, hL]
    exact evolutionVerdict_of (S' := G.toApprox.S) (fun t ht => (V.S_eq_U ht).symm)
      G.toApprox.isMDissipative G.toApprox.dissipative V.isClassicalSolution V.unique V.antitone
      (fun x => by rw [Feec.HilbertComplex.DissipFEEC.S_def, Feec.C0Semigroup.S_zero_apply])
      (fun x v hv T => V.converges (G.mem_toCore_closure x) hv T)
      (fun θ hθ τ hτ hτ0 x v hv T ε hε =>
        (Feec.HilbertComplex.dissipFEEC_fullyDiscrete G.toCore
          (Feec.HilbertComplex.DissipFEEC.thetaScheme _ θ hθ τ hτ)).converges_iterates
          (G.mem_toCore_closure x) hv hτ0 T hε)
  refine ⟨G.toApprox.U, ⟨hEV, V.norm_U, fun s t => G.toApprox.isSkewAdjoint.group.map_add s t,
    fun x hx hx2 h v _ _ ht hM => F.error_le a m x hx hx2 h v ht hM,
    fun x hx hx2 θ hθ h τ hτ w hw n M hM => ?_, fun x hx hx2 h τ hτ w hw n M hM => ?_, hprop,
    fun K _ hK x hx h v t => ?_⟩⟩
  · have h1 : ‖G.toApprox.U (n * τ) x - (semiflow (F.Lh a m h) (n * τ) (w 0) : Total W a m)‖ ≤
        ‖(w 0 : Total W a m) - x‖ + 2 * (1 + 4 * √3) * (1 + n * τ) * M :=
      F.error_le a m x hx hx2 h (w 0) (t := n * τ) (M := M) (by positivity) hM
    have h2 := hEV.theta_temporal θ hθ h hτ w hw n
    calc ‖G.toApprox.U (n * τ) x - (w n : Total W a m)‖ ≤
          ‖G.toApprox.U (n * τ) x - (semiflow (F.Lh a m h) (n * τ) (w 0) : Total W a m)‖ +
            ‖semiflow (F.Lh a m h) (n * τ) (w 0) - w n‖ := by
          rw [← Submodule.norm_coe, Submodule.coe_sub]
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by linarith
  · have h1 : ‖G.toApprox.U (n * τ) x - (semiflow (F.Lh a m h) (n * τ) (w 0) : Total W a m)‖ ≤
        ‖(w 0 : Total W a m) - x‖ + 2 * (1 + 4 * √3) * (1 + n * τ) * M :=
      F.error_le a m x hx hx2 h (w 0) (t := n * τ) (M := M) (by positivity) hM
    have h2 := hEV.crankNicolson_temporal h hτ w hw n
    calc ‖G.toApprox.U (n * τ) x - (w n : Total W a m)‖ ≤
          ‖G.toApprox.U (n * τ) x - (semiflow (F.Lh a m h) (n * τ) (w 0) : Total W a m)‖ +
            ‖semiflow (F.Lh a m h) (n * τ) (w 0) - w n‖ := by
          rw [← Submodule.norm_coe, Submodule.coe_sub]
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by linarith
  · rw [norm_sub_rev, ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem ((hprop K).1 hK t x hx)

include happrox in
/-- **The heat verdict** from `Feec`'s heat and fully discrete FEEC theorems on the window. -/
theorem heatVerdict (hπ : ∀ i : Fin m, (i : ℕ) + 1 < m → F.IsGraphBounded (a + (i : ℕ)))
    (hπ' : ∀ i : Fin m, (i : ℕ) + 1 = m →
      ∃ C : ℝ, ∀ (h : κ) (x : W (a + (i : ℕ))), ‖(F.π h).π _ x‖ ≤ C * ‖x‖)
    (hcr : ∀ i : Fin m, 0 < (i : ℕ) → IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ))))) :
    ∃ S : ℝ → Total W a m →L[𝕜] Total W a m,
    EvolutionVerdict (sq (H.wave a m)) F.l (F.Xh a m) (fun h => F.Lh a m h ^ 2) S := by
  have hcrw := H.closedRangeAt_window a m hcr
  have hb := F.isGraphBounded_window a m hπ hπ'
  set G := F.feecWindow a m happrox ⊤ (isClosed_top a m)
  have V := G.heatFEEC hcrw hb
  have hZ : ∀ x, x ∈ (G.heatCore hcrw hb).Data.topologicalClosure := fun x => by
    rw [G.dense_heatCore_data hcrw hb]; exact Submodule.mem_top
  refine ⟨G.toHeat.S, ?_⟩
  have hL : (fun h => F.Lh a m h ^ 2) = fun h => G.heatGen h :=
    funext (F.Lh_sq_eq a m happrox ⊤ (isClosed_top a m))
  rw [H.heat_eq a m, hL]
  exact evolutionVerdict_of (S' := G.toHeat.S) (fun _ _ => rfl) G.toHeat.isMDissipative
    G.toHeat.dissipative V.isClassicalSolution V.unique V.antitone
    (fun x => by rw [Feec.HilbertComplex.DissipFEEC.S_def, Feec.C0Semigroup.S_zero_apply])
    (fun x v hv T => V.converges (hZ x) hv T)
    (fun θ hθ τ hτ hτ0 x v hv T ε hε =>
      (Feec.HilbertComplex.dissipFEEC_fullyDiscrete (G.heatCore hcrw hb)
        (Feec.HilbertComplex.DissipFEEC.thetaScheme _ θ hθ τ hτ)).converges_iterates
        (hZ x) hv hτ0 T hε)

end HilbertComplex.SubcomplexFamily

end FEEC
