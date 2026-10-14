import Feec.Foundation

/-!
# Thesis §4.7–4.11: polynomial complexes, wave equations, constraint propagation

Coverage (thesis ids; see `docs/BLUEPRINT.md`, module M8):

* **Constraint propagation, abstract engine** (fills Thm 4.4/Cor 4.5 as used in §4.9–4.11):
  `propagate` (energy method; skew-symmetry only, no density, no semigroups),
  `strong_unique`, `isClosed_ker`.
* **Hodge wave operator**: `waveOp_isSkewSymm` (proved, so no skew-symmetry hypothesis is
  needed below), `ker_adj0_orth_le` (`cl(range d0) ⊆ ker d1`, no closed range).
* **Prop 4.16** (`prop_4_16`, `prop_4_16_exists`): with `K = {0} × ker d0* × Y` (`K`,
  critic item 12), for any closed `Y ⊇ range d1`; unconditional, both boundary conditions.
* **Prop 4.18** (`prop_4_18_i`, `prop_4_18_ii`, `reduced_unique`, `prop_4_18`): equivalence
  of (4.14) with the reduced system (4.15), with existence and uniqueness (also covers the
  reduced Maxwell system of §4.9).
* **§4.8** (critic item 14): mixed weak scalar wave ⇔ second-order weak form under the
  compatibility condition `u̇(0) ∈ range(-d*)`; `secondOrder_not_mixed` refutes the claimed
  unconditional equivalence under natural boundary conditions.
* **§4.7** Koszul algebra: `koszul_homotopy_core`, `koszul_decomp`, `koszul_direct`
  (the decomposition needs `r + k > 0`).
* **§4.10** (corrected list of discretizations): `pgrad_mem_PminusLambda1` (`P_r Λ⁰ × P_r⁻Λ¹`
  is valid) and `pgrad_not_mem_PminusLambda1` (`P_{r+1}Λ⁰ × P_r⁻Λ¹` is not a subcomplex, all
  `r ≥ 1`; critic item 14), `grad_sq_not_whitney`.
* **Lemma 3.5 (pointwise) / Props 4.17, 4.19** (critic item 4): `trace_curl`,
  `two_vskw_curl`, `div_curl`, `curl_TSD`. The projection hypothesis of Props 4.17/4.19 is
  false, so those statements are vacuous and are not formalized as stated; their
  unconditional content is `prop_4_16`/`prop_4_18_i`, and
  `UnitaryGroupGenerator.projection_hyp_necessary` (with `invariant_of_reversal`) shows the
  projection hypothesis is necessary for TSD propagation.
* **Existence hypotheses**: `UnitaryGroupGenerator` (stand-in for Stone's theorem) and
  `UnitaryGroupGenerator.wellPosedHom` (non-vacuity of `WellPosedHom`, critic item 6).

Solutions are strong solutions in the sense of `Feec.IsStrongSolution` (pointwise derivatives
within `[0,T]`; graph-norm continuity is not required, which makes uniqueness and
propagation statements stronger than in the thesis).
-/

open scoped RealInnerProductSpace
open Set LinearPMap

noncomputable section

namespace Feec.Constraints

/-! ## Generic tools: right derivatives, closed kernels, energy propagation -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A derivative within `Icc 0 T` is a right derivative at every `t ∈ Ico 0 T`. -/
theorem hasDerivWithinAt_Ici {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : F} {T t : ℝ} (h : HasDerivWithinAt f f' (Icc 0 T) t) (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt f f' (Ici t) t :=
  h.mono_of_mem_nhdsWithin (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2)
    (Icc_subset_Icc_left ht.1))

/-- A real function with zero derivative within `Icc 0 T` is constant there. -/
theorem const_of_hasDerivWithinAt_zero {f : ℝ → ℝ} {T : ℝ}
    (h : ∀ t ∈ Icc 0 T, HasDerivWithinAt f 0 (Icc 0 T) t) : ∀ t ∈ Icc 0 T, f t = f 0 :=
  constant_of_has_deriv_right_zero (fun t ht => (h t ht).continuousWithinAt)
    (fun t ht => hasDerivWithinAt_Ici (h t (Ico_subset_Icc_self ht)) ht)

/-- The kernel of a closed operator is closed (graph-preimage argument).
Correction of thesis §4.1/§4.3: "the kernel of an unbounded operator is closed" needs closedness. -/
theorem isClosed_ker {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) : IsClosed (A.ker : Set E) := by
  have : (A.ker : Set E) = (fun x : E => (x, (0 : F))) ⁻¹' (A.graph : Set (E × F)) := by
    ext x
    simp only [SetLike.mem_coe, mem_ker_iff, mem_preimage, mem_graph_iff]
    exact ⟨fun ⟨y, hy, h0⟩ => ⟨y, hy.symm, h0⟩, fun ⟨y, hy, h0⟩ => ⟨y, hy.symm, h0⟩⟩
  rw [this]
  exact hA.preimage (continuous_id.prodMk continuous_const)

/-- **Energy-method constraint propagation** (fills Thm 4.4 / Cor 4.5 as used in §4.9–4.11).
Let `A` be skew-symmetric, `K` a subspace with an orthogonal "projection" `P` (`P x ∈ K`,
`x - P x ⊥ K`) preserving `D(A)`, and `A (D(A) ∩ K) ⊆ K`. Then every strong solution of
`U' = A U` starting in `K` stays in `K`.

Thesis gap: the thesis routes this through Thm 4.4 (skew-adjointness of the restriction) and
Hille–Yosida, which needs the density of `D(A) ∩ K` in `K` that Props 4.16/4.17/4.19 only
"conjecture". Neither density nor skew-adjointness nor semigroup theory is needed. -/
theorem propagate (A : E →ₗ.[ℝ] E) (hA : IsSkewSymm A) (K : Submodule ℝ E) (P : E →L[ℝ] E)
    (hPK : ∀ x, P x ∈ K) (hPo : ∀ x, x - P x ∈ Kᗮ) (hPD : ∀ x ∈ A.domain, P x ∈ A.domain)
    (hAK : ∀ x : A.domain, (x : E) ∈ K → A x ∈ K)
    {T : ℝ} {U₀ : E} {U : ℝ → E} (hU : IsStrongSolution A T U₀ 0 U) (hU₀ : U₀ ∈ K) :
    ∀ t ∈ Icc 0 T, U t ∈ K := by
  classical
  set e : ℝ → E := fun t => U t - P (U t) with he_def
  set e' : ℝ → E := fun t =>
    if h : t ∈ Icc 0 T then A ⟨U t, hU.mem t h⟩ - P (A ⟨U t, hU.mem t h⟩) else 0
  have hcont : ContinuousOn U (Icc 0 T) := fun t ht => (hU.deriv t ht).continuousWithinAt
  have key := energy_zero (e := e) (e' := e') (T := T)
    (hcont.sub (P.continuous.comp_continuousOn hcont))
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      have h1 := hasDerivWithinAt_Ici (hU.deriv t ht') ht
      have h2 := h1.sub (P.hasFDerivAt.comp_hasDerivWithinAt t h1)
      rw [show e' t = _ from dite_eq_left ht']
      simp only [Pi.zero_apply, add_zero] at h2
      exact h2)
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      rw [show e' t = _ from dite_eq_left ht']
      have hPu : P (U t) ∈ A.domain := hPD _ (hU.mem t ht')
      have hVt : e t ∈ A.domain := A.domain.sub_mem (hU.mem t ht') hPu
      have hsplit : (⟨U t, hU.mem t ht'⟩ : A.domain) = ⟨P (U t), hPu⟩ + ⟨e t, hVt⟩ := by
        ext; simp [e]
      have he : e t ∈ Kᗮ := hPo (U t)
      have h1 : ⟪P (A ⟨U t, hU.mem t ht'⟩), e t⟫ = 0 :=
        (Submodule.mem_orthogonal K _).1 he _ (hPK _)
      have h2 : ⟪A ⟨P (U t), hPu⟩, e t⟫ = 0 :=
        (Submodule.mem_orthogonal K _).1 he _ (hAK _ (hPK _))
      have h3 : ⟪A ⟨e t, hVt⟩, e t⟫ = 0 := by
        have := hA ⟨e t, hVt⟩ ⟨e t, hVt⟩
        rw [real_inner_comm (A ⟨e t, hVt⟩) (e t)] at this
        linarith
      rw [inner_sub_left, h1, hsplit, LinearPMap.map_add, inner_add_left, h2, h3]; simp)
    (by
      have hm : U₀ - P U₀ ∈ K := K.sub_mem hU₀ (hPK _)
      have := (Submodule.mem_orthogonal K _).1 (hPo U₀) _ hm
      simpa [e, hU.init] using this)
  intro t ht
  have h0 : U t = P (U t) := sub_eq_zero.1 (key t ht)
  rw [h0]; exact hPK _

/-- Uniqueness of strong solutions for a skew-symmetric operator (energy identity). -/
theorem strong_unique (A : E →ₗ.[ℝ] E) (hA : IsSkewSymm A) {T : ℝ} {U₀ : E} {F U U' : ℝ → E}
    (hU : IsStrongSolution A T U₀ F U) (hU' : IsStrongSolution A T U₀ F U') :
    EqOn U U' (Icc 0 T) := by
  classical
  set e' : ℝ → E := fun t =>
    if h : t ∈ Icc 0 T then A ⟨U t, hU.mem t h⟩ - A ⟨U' t, hU'.mem t h⟩ else 0
  have hc : ∀ {V : ℝ → E} {G}, IsStrongSolution A T U₀ G V → ContinuousOn V (Icc 0 T) :=
    fun h t ht => (h.deriv t ht).continuousWithinAt
  have key := energy_zero (e := fun t => U t - U' t) (e' := e') (T := T)
    ((hc hU).sub (hc hU'))
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      have := (hasDerivWithinAt_Ici (hU.deriv t ht') ht).sub
        (hasDerivWithinAt_Ici (hU'.deriv t ht') ht)
      rw [show e' t = _ from dite_eq_left ht']
      simp only [add_sub_add_right_eq_sub] at this
      exact this)
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      rw [show e' t = _ from dite_eq_left ht']
      have hd : U t - U' t ∈ A.domain := A.domain.sub_mem (hU.mem t ht') (hU'.mem t ht')
      have hs : A ⟨U t, hU.mem t ht'⟩ - A ⟨U' t, hU'.mem t ht'⟩ = A ⟨_, hd⟩ := by
        rw [← LinearPMap.map_sub]; rfl
      have := hA ⟨_, hd⟩ ⟨_, hd⟩
      rw [real_inner_comm (A ⟨_, hd⟩) (U t - U' t)] at this
      rw [hs]; linarith)
    (by simp [hU.init, hU'.init])
  intro t ht
  exact sub_eq_zero.1 (key t ht)

/-- Skew-symmetry is preserved by negation (the thesis evolves by `ξ' = -Lξ`). -/
theorem isSkewSymm_neg {A : E →ₗ.[ℝ] E} (hA : IsSkewSymm A) : IsSkewSymm (-A) := by
  intro x y
  have := hA x y
  simp only [LinearPMap.neg_apply, inner_neg_left, inner_neg_right]
  linarith

/-- The kernel of a partial linear map lies in its domain. -/
theorem ker_le_domain {F : Type*} [AddCommGroup F] [Module ℝ F] (A : E →ₗ.[ℝ] F) :
    A.ker ≤ A.domain := by
  intro x hx
  obtain ⟨y, rfl, -⟩ := mem_ker_iff.1 hx
  exact y.2

end Generic

/-! ## The length-2 Hilbert complex: coordinates, skew-symmetry of the Hodge wave operator -/

section Complex

open HilbertComplex2

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]

/-- `tot` as a continuous linear equivalence. -/
def totL : Tot W0 W1 W2 ≃L[ℝ] W0 × W1 × W2 :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ W0 (WithLp 2 (W1 × W2))).trans
    ((ContinuousLinearEquiv.refl ℝ W0).prodCongr (WithLp.prodContinuousLinearEquiv 2 ℝ W1 W2))

/-- Coordinates of `totL`. -/
@[simp] theorem totL_apply (x : Tot W0 W1 W2) : totL x = tot W0 W1 W2 x := rfl

/-- Inverse coordinates of `totL`. -/
@[simp] theorem totL_symm_apply (p : W0 × W1 × W2) :
    (totL (W0 := W0) (W1 := W1) (W2 := W2)).symm p = (tot W0 W1 W2).symm p := rfl

/-- The `ℓ²` inner product of `Tot` in coordinates. -/
theorem inner_tot (x y : Tot W0 W1 W2) :
    ⟪x, y⟫ = ⟪(tot W0 W1 W2 x).1, (tot W0 W1 W2 y).1⟫ + ⟪(tot W0 W1 W2 x).2.1,
      (tot W0 W1 W2 y).2.1⟫ + ⟪(tot W0 W1 W2 x).2.2, (tot W0 W1 W2 y).2.2⟫ := by
  simp only [WithLp.prod_inner_apply, tot, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply]
  rw [add_assoc]; rfl

variable [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2]
variable (H : HilbertComplex2 W0 W1 W2)

/-- `D(L) = V0 × (V1 ∩ V1*) × V2*` in coordinates. -/
theorem mem_domL {x : Tot W0 W1 W2} : x ∈ H.domL ↔ (tot W0 W1 W2 x).1 ∈ H.d0.domain ∧
    (tot W0 W1 W2 x).2.1 ∈ H.midDomain ∧ (tot W0 W1 W2 x).2.2 ∈ H.d1†.domain := by
  simp [domL, Submodule.mem_prod]

/-- Coordinate projections of `D(L)` (4.5). -/
@[simp] theorem coe_pr0 (x : H.domL) : (H.pr0 x : W0) = (tot W0 W1 W2 x).1 := rfl
@[simp] theorem coe_prV1 (x : H.domL) : (H.prV1 x : W1) = (tot W0 W1 W2 x).2.1 := rfl
@[simp] theorem coe_prV1s (x : H.domL) : (H.prV1s x : W1) = (tot W0 W1 W2 x).2.1 := rfl
@[simp] theorem coe_prV2s (x : H.domL) : (H.prV2s x : W2) = (tot W0 W1 W2 x).2.2 := rfl

/-- The Hodge wave operator (4.5) in coordinates. -/
theorem tot_waveOp (x : H.waveOp.domain) :
    tot W0 W1 W2 (H.waveOp x) = (-(H.d0† (H.prV1s ⟨x.1, x.2⟩)),
      H.d0 (H.pr0 ⟨x.1, x.2⟩) + H.d1† (H.prV2s ⟨x.1, x.2⟩), -(H.d1 (H.prV1 ⟨x.1, x.2⟩))) := by
  change (tot W0 W1 W2) ((tot W0 W1 W2).symm _) = _
  rw [LinearEquiv.apply_symm_apply]; rfl

/-- The Hodge wave operator is skew-symmetric on `D(L)` (the four adjoint identities).
Proved here directly so that Props 4.16/4.18 need no skew-symmetry hypothesis; no closed range
and no `d** = d` is used (only the formal-adjoint identities enter). -/
theorem waveOp_isSkewSymm : IsSkewSymm H.waveOp := by
  intro x y
  rw [inner_tot, inner_tot, tot_waveOp, tot_waveOp]
  have a0 := adjoint_isFormalAdjoint H.dense0 (H.prV1s ⟨x.1, x.2⟩) (H.pr0 ⟨y.1, y.2⟩)
  have a0' := adjoint_isFormalAdjoint H.dense0 (H.prV1s ⟨y.1, y.2⟩) (H.pr0 ⟨x.1, x.2⟩)
  have a1 := adjoint_isFormalAdjoint H.dense1 (H.prV2s ⟨x.1, x.2⟩) (H.prV1 ⟨y.1, y.2⟩)
  have a1' := adjoint_isFormalAdjoint H.dense1 (H.prV2s ⟨y.1, y.2⟩) (H.prV1 ⟨x.1, x.2⟩)
  simp only [coe_pr0, coe_prV1, coe_prV1s, coe_prV2s] at a0 a0' a1 a1'
  simp only [inner_neg_left, inner_neg_right, inner_add_left, inner_add_right]
  have c1 := real_inner_comm (H.d0 (H.pr0 ⟨x.1, x.2⟩)) (tot W0 W1 W2 (y : Tot W0 W1 W2)).2.1
  have c3 := real_inner_comm (H.d1 (H.prV1 ⟨x.1, x.2⟩)) (tot W0 W1 W2 (y : Tot W0 W1 W2)).2.2
  have c4 := real_inner_comm (tot W0 W1 W2 (x : Tot W0 W1 W2)).1 (H.d0† (H.prV1s ⟨y.1, y.2⟩))
  have c2 := real_inner_comm (H.d1† (H.prV2s ⟨y.1, y.2⟩)) (tot W0 W1 W2 (x : Tot W0 W1 W2)).2.1
  linarith

/-- (4.1a) for `d0`: `ker d0* = (range d0)ᗮ`. -/
theorem ker_adj0_eq : H.d0†.ker = (LinearMap.range H.d0.toFun)ᗮ :=
  (orth_range_eq_ker_adjoint H.d0 H.dense0).symm

/-- (4.1a) for `d1`: `ker d1* = (range d1)ᗮ`. -/
theorem ker_adj1_eq : H.d1†.ker = (LinearMap.range H.d1.toFun)ᗮ :=
  (orth_range_eq_ker_adjoint H.d1 H.dense1).symm

/-- `ker d0*` is closed (it is an orthogonal complement). -/
theorem isClosed_ker_adj0 : IsClosed (H.d0†.ker : Set W1) := by
  rw [ker_adj0_eq H]; exact Submodule.isClosed_orthogonal _

/-- `ker d0*` admits an orthogonal projection (used for `P_K`). -/
instance : (H.d0†.ker).HasOrthogonalProjection := by
  have : CompleteSpace (H.d0†.ker) := (isClosed_ker_adj0 H).completeSpace_coe
  infer_instance

/-- `B ⊆ Z`: `range d0 ⊆ ker d1` (Def. of Hilbert complex, §4.2). -/
theorem range_d0_le_ker_d1 : LinearMap.range H.d0.toFun ≤ H.d1.ker := by
  rintro _ ⟨x, rfl⟩
  exact mem_ker_iff.2 ⟨⟨_, H.map_mem x⟩, rfl, H.comp_zero x⟩

/-- `(ker d0*)ᗮ = closure (range d0) ⊆ ker d1`: no closed range needed. -/
theorem ker_adj0_orth_le : (H.d0†.ker)ᗮ ≤ H.d1.ker := by
  rw [ker_adj0_eq H, Submodule.orthogonal_orthogonal_eq_closure]
  exact Submodule.topologicalClosure_minimal _ (range_d0_le_ker_d1 H)
    (isClosed_ker H.d1 H.closed1)

/-- `d0* d1* = 0` in the form `range d1* ⊆ ker d0*`. -/
theorem adj1_mem_ker_adj0 (ρ : H.d1†.domain) : H.d1† ρ ∈ H.d0†.ker := by
  rw [ker_adj0_eq H, Submodule.mem_orthogonal]
  rintro _ ⟨σ, rfl⟩
  have := adjoint_isFormalAdjoint H.dense1 ρ ⟨_, H.map_mem σ⟩
  change ⟪H.d0 σ, H.d1† ρ⟫ = 0
  rw [real_inner_comm, this]
  simp [H.comp_zero σ]

/-- For closed `Y ⊆ W2` the conditions `range d1 ⊆ Y` and `Yᗮ ⊆ ker d1*` agree; the second is
the form used in the blueprint, the first is the one checked in applications
(e.g. `curl` maps into divergence-free fields). -/
theorem range_d1_le_iff (Y : Submodule ℝ W2) [Y.HasOrthogonalProjection] :
    LinearMap.range H.d1.toFun ≤ Y ↔ Yᗮ ≤ H.d1†.ker := by
  rw [ker_adj1_eq H]
  constructor
  · exact Submodule.orthogonal_le
  · intro h
    calc LinearMap.range H.d1.toFun ≤ (LinearMap.range H.d1.toFun)ᗮᗮ :=
          Submodule.le_orthogonal_orthogonal _
      _ ≤ Yᗮᗮ := Submodule.orthogonal_le h
      _ = Y := Submodule.orthogonal_orthogonal Y

/-! ### The constraint subspace `K = 0 × ker d0* × Y` (critic item 12) -/

/-- The constraint subspace `K = {0} × ker d0* × Y ⊆ W0 × W1 × W2` of Prop 4.16
(`σ = 0`, "`div u = 0`", `ρ ∈ Y`). With `Y = ⊤` this is the subspace of Prop 4.18. -/
def K (Y : Submodule ℝ W2) : Submodule ℝ (Tot W0 W1 W2) :=
  ((⊥ : Submodule ℝ W0).prod ((H.d0†).ker.prod Y)).comap (tot W0 W1 W2).toLinearMap

/-- Membership in the constraint subspace `K`. -/
theorem mem_K {Y : Submodule ℝ W2} {x : Tot W0 W1 W2} :
    x ∈ K H Y ↔ (tot W0 W1 W2 x).1 = 0 ∧ (tot W0 W1 W2 x).2.1 ∈ H.d0†.ker ∧
      (tot W0 W1 W2 x).2.2 ∈ Y := by
  simp [K, Submodule.mem_prod]

variable (Y : Submodule ℝ W2) [Y.HasOrthogonalProjection]

/-- The orthogonal projection onto `K`: `P_K = 0 × P_{ker d0*} × P_Y`. -/
def projK : Tot W0 W1 W2 →L[ℝ] Tot W0 W1 W2 :=
  (totL (W0 := W0) (W1 := W1) (W2 := W2)).symm.toContinuousLinearMap ∘L
    ((0 : W0 →L[ℝ] W0).prodMap ((H.d0†.ker).starProjection.prodMap Y.starProjection)) ∘L
    (totL (W0 := W0) (W1 := W1) (W2 := W2)).toContinuousLinearMap

/-- `P_K` in coordinates. -/
theorem tot_projK (x : Tot W0 W1 W2) : tot W0 W1 W2 (projK H Y x) =
    (0, (H.d0†.ker).starProjection (tot W0 W1 W2 x).2.1, Y.starProjection (tot W0 W1 W2 x).2.2) := by
  simp [projK]; rfl

/-- `P_K` maps into `K`. -/
theorem projK_mem (x : Tot W0 W1 W2) : projK H Y x ∈ K H Y := by
  rw [mem_K, tot_projK]
  exact ⟨rfl, Submodule.starProjection_apply_mem _ _, Submodule.starProjection_apply_mem _ _⟩

/-- `x - P_K x ⊥ K`, so `P_K` is the orthogonal projection onto `K`. -/
theorem projK_orth (x : Tot W0 W1 W2) : x - projK H Y x ∈ (K H Y)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro k hk
  rw [mem_K] at hk
  rw [inner_tot, _root_.map_sub, tot_projK]
  simp only [Prod.fst_sub, Prod.snd_sub, hk.1, inner_zero_left, zero_add]
  rw [(Submodule.mem_orthogonal _ _).1 (Submodule.sub_starProjection_mem_orthogonal _) _ hk.2.1,
    (Submodule.mem_orthogonal _ _).1 (Submodule.sub_starProjection_mem_orthogonal _) _ hk.2.2,
    add_zero]

variable {H Y}

/-- `P_K` preserves `D(L)`: the "first itemized hypothesis" of Thm 4.4, proved abstractly
(no closed range, no contractibility, no exactness). Uses `(ker d0*)ᗮ = cl(range d0) ⊆ ker d1`
and `Yᗮ ⊆ ker d1* ⊆ V2*`. -/
theorem projK_mem_domL (hY : LinearMap.range H.d1.toFun ≤ Y) {x : Tot W0 W1 W2}
    (hx : x ∈ H.domL) : projK H Y x ∈ H.domL := by
  rw [mem_domL] at hx ⊢
  rw [tot_projK]
  set u := (tot W0 W1 W2 x).2.1
  set ρ := (tot W0 W1 W2 x).2.2
  refine ⟨H.d0.domain.zero_mem, ⟨?_, ker_le_domain _ (Submodule.starProjection_apply_mem _ _)⟩, ?_⟩
  · -- `P u = u - (u - P u)` with `u - P u ∈ (ker d0*)ᗮ ⊆ ker d1 ⊆ V1`
    have h1 : u - (H.d0†.ker).starProjection u ∈ H.d1.domain :=
      ker_le_domain _ (ker_adj0_orth_le H (Submodule.sub_starProjection_mem_orthogonal u))
    have := H.d1.domain.sub_mem hx.2.1.1 h1
    simpa using this
  · have hY' := (range_d1_le_iff H Y).1 hY
    have h1 : ρ - Y.starProjection ρ ∈ H.d1†.domain :=
      ker_le_domain _ (hY' (Submodule.sub_starProjection_mem_orthogonal ρ))
    have := H.d1†.domain.sub_mem hx.2.2 h1
    simpa using this

omit [Y.HasOrthogonalProjection] in
/-- `L (D(L) ∩ K) ⊆ K`: the "third itemized hypothesis" of Thm 4.4. For `(0, u, ρ)` with
`u ∈ ker d0*`: `L(0,u,ρ) = (0, d1* ρ, -d1 u)`, `d1* ρ ∈ ker d0*` since `d0* d1* = 0`, and
`d1 u ∈ Y` by hypothesis. -/
theorem waveOp_mem_K (hY : LinearMap.range H.d1.toFun ≤ Y) (x : H.waveOp.domain)
    (hx : (x : Tot W0 W1 W2) ∈ K H Y) : H.waveOp x ∈ K H Y := by
  rw [mem_K] at hx ⊢
  rw [tot_waveOp]
  have hσ : H.pr0 ⟨x.1, x.2⟩ = 0 := Subtype.ext hx.1
  have hu : H.d0† (H.prV1s ⟨x.1, x.2⟩) = 0 := by
    obtain ⟨y, hy, hy0⟩ := mem_ker_iff.1 hx.2.1
    have : H.prV1s ⟨x.1, x.2⟩ = y := Subtype.ext hy
    rw [this, hy0]
  refine ⟨by simp [hu], ?_, ?_⟩
  · simp only [hσ, LinearPMap.map_zero, zero_add]
    exact adj1_mem_ker_adj0 H _
  · exact Y.neg_mem (hY ⟨_, rfl⟩)

/-- **Thesis Prop 4.16** (abstract form, both boundary conditions): for the Hodge wave
`ξ' = -L ξ` of a length-2 Hilbert complex, data in `K = {0} × ker d0* × Y` stay in `K`, i.e.
`σ ≡ 0`, `u` stays in `ker d0*` (divergence-free) and `ρ` stays in `Y`.

Here `Y ⊆ W2` is any closed subspace containing `range d1` (equivalently `Yᗮ ⊆ ker d1*`,
`range_d1_le_iff`); for the vector wave equation (4.12)/(4.13) take `Y = H(div, 0)`, which
contains `curl H(curl)` (resp. `curl H̊(curl)`). Strong solutions are used; weak and strong
solutions coincide for `D(L)` data by Thm 4.7 (`Feec.Ch4.HodgeWave`).

Thesis gap / Correction: the thesis assumes two density "conjectures", uses the domain of the
electric complex (4.13) while stating (4.12), uses the wrong Hodge decomposition for `ρ`, and
asserts the false inclusion `P_{H(div,0)} H(curl) ⊆ H̊(curl)`. None of this is needed: the
proposition holds unconditionally, for both boundary conditions, with no closed range,
contractibility or density hypothesis. Skew-symmetry of `L` is proved (`waveOp_isSkewSymm`). -/
theorem prop_4_16 (hY : LinearMap.range H.d1.toFun ≤ Y) {T : ℝ} {U₀ : Tot W0 W1 W2}
    {U : ℝ → Tot W0 W1 W2} (hU : IsStrongSolution (-H.waveOp) T U₀ 0 U) (hU₀ : U₀ ∈ K H Y) :
    ∀ t ∈ Icc 0 T, U t ∈ K H Y :=
  propagate (-H.waveOp) (isSkewSymm_neg (waveOp_isSkewSymm H)) (K H Y) (projK H Y) (projK_mem H Y)
    (projK_orth H Y) (fun _ hx => projK_mem_domL hY hx)
    (fun x hx => by
      rw [LinearPMap.neg_apply]
      exact (K H Y).neg_mem (waveOp_mem_K hY x hx)) hU hU₀

/-- Prop 4.16 with existence: under the well-posedness hypothesis of Thm 4.6
(`WellPosedHom`, standing for Stone's theorem), data in `D(L) ∩ K` have a unique strong
solution, and it stays in `K`. -/
theorem prop_4_16_exists (hY : LinearMap.range H.d1.toFun ≤ Y) {T : ℝ}
    (hHY : WellPosedHom (-H.waveOp) T) {U₀ : Tot W0 W1 W2} (hD : U₀ ∈ H.domL)
    (hU₀ : U₀ ∈ K H Y) :
    ∃ U, IsStrongSolution (-H.waveOp) T U₀ 0 U ∧ (∀ t ∈ Icc 0 T, U t ∈ K H Y) ∧
      ∀ U', IsStrongSolution (-H.waveOp) T U₀ 0 U' → EqOn U U' (Icc 0 T) := by
  obtain ⟨U, hU⟩ := hHY U₀ hD
  exact ⟨U, hU, prop_4_16 hY hU hU₀, fun U' hU' =>
    strong_unique _ (isSkewSymm_neg (waveOp_isSkewSymm H)) hU hU'⟩

/-- Prop 4.16 for the opposite sign convention `ξ' = L ξ` (time reversal). -/
theorem prop_4_16' (hY : LinearMap.range H.d1.toFun ≤ Y) {T : ℝ} {U₀ : Tot W0 W1 W2}
    {U : ℝ → Tot W0 W1 W2} (hU : IsStrongSolution H.waveOp T U₀ 0 U) (hU₀ : U₀ ∈ K H Y) :
    ∀ t ∈ Icc 0 T, U t ∈ K H Y :=
  propagate H.waveOp (waveOp_isSkewSymm H) (K H Y) (projK H Y) (projK_mem H Y)
    (projK_orth H Y) (fun _ hx => projK_mem_domL hY hx) (waveOp_mem_K hY) hU hU₀

/-! ### Prop 4.18: equivalence with the reduced two-field system (4.15) -/

variable (H) in
/-- Strong solution of the reduced system (4.15), `E' = -d1* B`, `B' = d1 E` (for the
linearized EB complex: `Ė = -curl B`, `Ḃ = curl E`), with `E ∈ V1`, `B ∈ V2*`. -/
structure IsReducedSolution (T : ℝ) (E₀ : W1) (B₀ : W2) (E : ℝ → W1) (B : ℝ → W2) : Prop where
  memE : ∀ t ∈ Icc 0 T, E t ∈ H.d1.domain
  memB : ∀ t ∈ Icc 0 T, B t ∈ H.d1†.domain
  derivE : ∀ t (ht : t ∈ Icc 0 T), HasDerivWithinAt E (-(H.d1† ⟨B t, memB t ht⟩)) (Icc 0 T) t
  derivB : ∀ t (ht : t ∈ Icc 0 T), HasDerivWithinAt B (H.d1 ⟨E t, memE t ht⟩) (Icc 0 T) t
  initE : E 0 = E₀
  initB : B 0 = B₀

variable (W0) in
/-- The initial datum `(0, E₀, B₀)` of (4.14). -/
def ini (E₀ : W1) (B₀ : W2) : Tot W0 W1 W2 := (tot W0 W1 W2).symm (0, E₀, B₀)

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2] in
/-- Coordinates of the initial datum. -/
@[simp] theorem tot_ini (E₀ : W1) (B₀ : W2) : tot W0 W1 W2 (ini W0 E₀ B₀) = (0, E₀, B₀) :=
  LinearEquiv.apply_symm_apply _ _

/-- The divergence constraint `E ∈ ker d0*` is propagated by the reduced system (4.15):
`d/dt ⟪d0 σ, E⟫ = -⟪d0 σ, d1* B⟫ = 0`. In particular `E(t) ∈ V1 ∩ V1*`, the regularity
required by the thesis for (4.15). -/
theorem reduced_mem_ker {T : ℝ} {E₀ : W1} {B₀ : W2} {E : ℝ → W1} {B : ℝ → W2}
    (hR : IsReducedSolution H T E₀ B₀ E B) (hE₀ : E₀ ∈ H.d0†.ker) :
    ∀ t ∈ Icc 0 T, E t ∈ H.d0†.ker := by
  intro t ht
  rw [ker_adj0_eq H] at hE₀ ⊢
  rw [Submodule.mem_orthogonal] at hE₀ ⊢
  rintro _ ⟨σ, rfl⟩
  have hc := const_of_hasDerivWithinAt_zero (T := T) (f := fun s => ⟪H.d0.toFun σ, E s⟫)
    (fun s hs => by
      have := (innerSL ℝ (H.d0.toFun σ)).hasFDerivAt.comp_hasDerivWithinAt s (hR.derivE s hs)
      refine this.congr_deriv ?_
      have h0 := (Submodule.mem_orthogonal _ _).1
        ((ker_adj0_eq H) ▸ adj1_mem_ker_adj0 H ⟨B s, hR.memB s hs⟩) _
          (LinearMap.mem_range_self _ σ)
      simp only [innerSL_apply_apply, inner_neg_right, neg_eq_zero]
      exact h0) t ht
  rw [hc, hR.initE]
  exact hE₀ _ (LinearMap.mem_range_self _ σ)

/-- **Thesis Prop 4.18 (i)**: if `(σ, E, B)` solves (4.14) (`ξ' = -L ξ`) with data
`(0, E₀, B₀)`, `E₀ ∈ ker d0*` ("`div E₀ = 0`"), then `σ ≡ 0`, `E` stays in `ker d0*`, and
`(E, B)` solves the reduced system (4.15).

Thesis gap: the thesis gives no proof. Here (i) is Prop 4.16 with `Y = W2`, followed by
reading off the components. -/
theorem prop_4_18_i {T : ℝ} {E₀ : W1} {B₀ : W2} {U : ℝ → Tot W0 W1 W2}
    (hE₀ : E₀ ∈ H.d0†.ker) (hU : IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0 U) :
    (∀ t ∈ Icc 0 T, (tot W0 W1 W2 (U t)).1 = 0 ∧ (tot W0 W1 W2 (U t)).2.1 ∈ H.d0†.ker) ∧
      IsReducedSolution H T E₀ B₀ (fun t => (tot W0 W1 W2 (U t)).2.1)
        (fun t => (tot W0 W1 W2 (U t)).2.2) := by
  have hK := prop_4_16 (Y := ⊤) le_top hU (by rw [mem_K, tot_ini]; exact ⟨rfl, hE₀, trivial⟩)
  refine ⟨fun t ht => ⟨((mem_K H).1 (hK t ht)).1, ((mem_K H).1 (hK t ht)).2.1⟩, ?_⟩
  have hmem := fun t ht => (mem_domL H).1 (hU.mem t ht)
  let f1 : Tot W0 W1 W2 →L[ℝ] W1 := (ContinuousLinearMap.fst ℝ W1 W2) ∘L
    (ContinuousLinearMap.snd ℝ W0 (W1 × W2)) ∘L (totL (W0 := W0) (W1 := W1) (W2 := W2))
  let f2 : Tot W0 W1 W2 →L[ℝ] W2 := (ContinuousLinearMap.snd ℝ W1 W2) ∘L
    (ContinuousLinearMap.snd ℝ W0 (W1 × W2)) ∘L (totL (W0 := W0) (W1 := W1) (W2 := W2))
  refine ⟨fun t ht => (hmem t ht).2.1.1, fun t ht => (hmem t ht).2.2, fun t ht => ?_,
    fun t ht => ?_, by simp [hU.init], by simp [hU.init]⟩
  · have := f1.hasFDerivAt.comp_hasDerivWithinAt t (hU.deriv t ht)
    refine this.congr_deriv ?_
    have hσ : H.pr0 ⟨U t, hU.mem t ht⟩ = 0 := Subtype.ext ((mem_K H).1 (hK t ht)).1
    simp only [f1, ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      totL_apply, Pi.zero_apply, add_zero, LinearPMap.neg_apply, _root_.map_neg]
    rw [tot_waveOp]
    simp only [hσ, LinearPMap.map_zero, zero_add, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
    rfl
  · have := f2.hasFDerivAt.comp_hasDerivWithinAt t (hU.deriv t ht)
    refine this.congr_deriv ?_
    simp only [f2, ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      totL_apply, Pi.zero_apply, add_zero, LinearPMap.neg_apply, _root_.map_neg]
    rw [tot_waveOp]
    simp only [ContinuousLinearMap.coe_snd', neg_neg]
    rfl

/-- **Thesis Prop 4.18 (ii)**: if `(E, B)` solves the reduced system (4.15) with
`E₀ ∈ ker d0*`, then `(0, E, B)` solves (4.14) with data `(0, E₀, B₀)`. -/
theorem prop_4_18_ii {T : ℝ} {E₀ : W1} {B₀ : W2} {E : ℝ → W1} {B : ℝ → W2}
    (hE₀ : E₀ ∈ H.d0†.ker) (hR : IsReducedSolution H T E₀ B₀ E B) :
    IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0
      (fun t => (tot W0 W1 W2).symm (0, E t, B t)) := by
  have hk := reduced_mem_ker hR hE₀
  have hmem : ∀ t ∈ Icc 0 T, (tot W0 W1 W2).symm (0, E t, B t) ∈ H.domL := fun t ht => by
    rw [mem_domL, LinearEquiv.apply_symm_apply]
    exact ⟨H.d0.domain.zero_mem, ⟨hR.memE t ht, ker_le_domain _ (hk t ht)⟩, hR.memB t ht⟩
  refine ⟨hmem, fun t ht => ?_, by simp [ini, hR.initE, hR.initB]⟩
  have hd := ((hasDerivWithinAt_const t (Icc 0 T) (0 : W0)).prodMk
    ((hR.derivE t ht).prodMk (hR.derivB t ht)))
  have := (totL (W0 := W0) (W1 := W1) (W2 := W2)).symm.hasFDerivAt.comp_hasDerivWithinAt t hd
  refine this.congr_deriv ?_
  apply (tot W0 W1 W2).injective
  simp only [Pi.zero_apply, add_zero, LinearPMap.neg_apply, _root_.map_neg]
  rw [tot_waveOp]
  have hu : H.d0† (H.prV1s ⟨_, hmem t ht⟩) = 0 := by
    obtain ⟨y, hy, hy0⟩ := mem_ker_iff.1 (hk t ht)
    have : H.prV1s ⟨_, hmem t ht⟩ = y := Subtype.ext (by
      rw [coe_prV1s, LinearEquiv.apply_symm_apply]; exact hy)
    rw [this, hy0]
  have hσ : H.pr0 ⟨_, hmem t ht⟩ = 0 := Subtype.ext (by
    rw [coe_pr0, LinearEquiv.apply_symm_apply]; rfl)
  rw [hu, hσ]
  simp only [LinearPMap.map_zero, zero_add, neg_zero, ContinuousLinearEquiv.coe_coe,
    totL_symm_apply, LinearEquiv.apply_symm_apply, Prod.neg_mk, neg_neg]
  rfl

/-- Uniqueness for the reduced system (4.15) (the thesis says "the solution" without proof):
via Prop 4.18 (ii) and the energy uniqueness for the skew-symmetric `-L`. -/
theorem reduced_unique {T : ℝ} {E₀ : W1} {B₀ : W2} {E E' : ℝ → W1} {B B' : ℝ → W2}
    (hE₀ : E₀ ∈ H.d0†.ker) (h : IsReducedSolution H T E₀ B₀ E B)
    (h' : IsReducedSolution H T E₀ B₀ E' B') : EqOn E E' (Icc 0 T) ∧ EqOn B B' (Icc 0 T) := by
  have := strong_unique _ (isSkewSymm_neg (waveOp_isSkewSymm H)) (prop_4_18_ii hE₀ h)
    (prop_4_18_ii hE₀ h')
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simpa using congrArg (fun z => (tot W0 W1 W2 z).2.1) (this ht)
  · simpa using congrArg (fun z => (tot W0 W1 W2 z).2.2) (this ht)

/-- **Thesis Prop 4.18** (corrected statement, existence and uniqueness): given the
well-posedness of (4.14) (Thm 4.6; `WellPosedHom` stands for Stone's theorem), for
`E₀ ∈ V1` with `E₀ ∈ ker d0*` ("`div E₀ = 0`") and `B₀ ∈ V2*`, the reduced system (4.15) has a
unique solution, it keeps `E ∈ ker d0*`, and `(0, E, B)` is the solution of (4.14).

Thesis gap: "the solution to (4.15)" presupposed uniqueness, which was not established, and
`V¹ × V²` was undefined (it is `(V1 ∩ V1*) × V2*`). -/
theorem prop_4_18 {T : ℝ} (hHY : WellPosedHom (-H.waveOp) T) {E₀ : W1} {B₀ : W2}
    (hE₀ : E₀ ∈ H.d1.domain) (hE₀k : E₀ ∈ H.d0†.ker) (hB₀ : B₀ ∈ H.d1†.domain) :
    ∃ E B, IsReducedSolution H T E₀ B₀ E B ∧ (∀ t ∈ Icc 0 T, E t ∈ H.d0†.ker) ∧
      IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0
        (fun t => (tot W0 W1 W2).symm (0, E t, B t)) ∧
      ∀ E' B', IsReducedSolution H T E₀ B₀ E' B' → EqOn E E' (Icc 0 T) ∧ EqOn B B' (Icc 0 T) := by
  have hdom : ini W0 E₀ B₀ ∈ (-H.waveOp).domain := by
    change ini W0 E₀ B₀ ∈ H.domL
    rw [mem_domL, tot_ini]
    exact ⟨H.d0.domain.zero_mem, ⟨hE₀, ker_le_domain _ hE₀k⟩, hB₀⟩
  obtain ⟨U, hU⟩ := hHY _ hdom
  obtain ⟨-, hR⟩ := prop_4_18_i hE₀k hU
  exact ⟨_, _, hR, reduced_mem_ker hR hE₀k, prop_4_18_ii hE₀k hR,
    fun E' B' h' => reduced_unique hE₀k hR h'⟩

end Complex

/-! ## §4.8: the scalar wave equation as a two-space Hodge wave (critic item 14)

Segment `0 → V0 --d--> W1` (`W⁻¹ = 0`), e.g. `d = grad` on `H¹` (natural BCs) or on `H̊¹`
(essential BCs). Time-dependent elements of `V0 = D(d)` are modeled as `w : ℝ → D(d)`, so that
`d (w t)` needs no membership proof; `u' t ∈ W0` is the `W0`-derivative of `u = w`. -/

section ScalarWave

variable {W0 W1 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1]

/-- Mixed weak form of the §4.8 Hodge wave: `u ∈ C⁰(V0) ∩ C¹(W0)`, `ρ ∈ C¹(W1)`,
`(u̇, v) = -(ρ, d v)` for `v ∈ V0` and `(ρ̇, μ) = (d u, μ)` for `μ ∈ W1`. -/
structure IsMixedWeak (d : W0 →ₗ.[ℝ] W1) (T : ℝ) (w : ℝ → d.domain) (u' : ℝ → W0)
    (ρ ρ' : ℝ → W1) : Prop where
  du : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (w s : W0)) (u' t) (Icc 0 T) t
  cont : ContinuousOn (fun s => d (w s)) (Icc 0 T)
  dρ : ∀ t ∈ Icc 0 T, HasDerivWithinAt ρ (ρ' t) (Icc 0 T) t
  eq_u : ∀ t ∈ Icc 0 T, ∀ v : d.domain, ⟪u' t, (v : W0)⟫ = -⟪ρ t, d v⟫
  eq_ρ : ∀ t ∈ Icc 0 T, ∀ μ : W1, ⟪ρ' t, μ⟫ = ⟪d (w t), μ⟫

/-- Second-order weak form `(ü, v) = -(d u, d v)`: `u ∈ C⁰(V0) ∩ C¹(W0)` and, for each test
`v ∈ V0`, `t ↦ (u̇, v)` is differentiable with derivative `-(d u, d v)` (the thesis' `ü` only
exists in `V0'`, so it is read as this duality pairing). -/
structure IsSecondOrderWeak (d : W0 →ₗ.[ℝ] W1) (T : ℝ) (w : ℝ → d.domain) (u' : ℝ → W0) :
    Prop where
  du : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (w s : W0)) (u' t) (Icc 0 T) t
  cont : ContinuousOn (fun s => d (w s)) (Icc 0 T)
  eq : ∀ t ∈ Icc 0 T, ∀ v : d.domain,
    HasDerivWithinAt (fun s => ⟪u' s, (v : W0)⟫) (-⟪d (w t), d v⟫) (Icc 0 T) t

variable {d : W0 →ₗ.[ℝ] W1} {T : ℝ} {w : ℝ → d.domain} {u' : ℝ → W0}

/-- **§4.8, mixed ⇒ second order**: a mixed weak solution has `ρ̇ = d u`, its `u` solves the
second-order weak form, and `u̇(t) ⊥ ker d` for all `t` (for `d = grad` on `H¹`:
`∫ u̇ = 0`). -/
theorem mixed_imp_secondOrder {ρ ρ' : ℝ → W1} (h : IsMixedWeak d T w u' ρ ρ') :
    IsSecondOrderWeak d T w u' ∧ (∀ t ∈ Icc 0 T, ρ' t = d (w t)) ∧
      ∀ t ∈ Icc 0 T, ∀ z : d.domain, d z = 0 → ⟪u' t, (z : W0)⟫ = 0 := by
  refine ⟨⟨h.du, h.cont, fun t ht v => ?_⟩, fun t ht => ?_, fun t ht z hz => ?_⟩
  · have h1 := (innerSL ℝ (d v)).hasFDerivAt.comp_hasDerivWithinAt t (h.dρ t ht)
    have h2 := h1.neg
    refine (h2.congr_of_mem (fun s hs => ?_) ht).congr_deriv ?_
    · rw [h.eq_u s hs v]; simp [real_inner_comm]
    · simp [real_inner_comm, h.eq_ρ t ht]
  · have := h.eq_ρ t ht (ρ' t - d (w t))
    rw [← sub_eq_zero, ← inner_sub_left] at this
    exact sub_eq_zero.1 (inner_self_eq_zero.1 this)
  · rw [h.eq_u t ht z, hz, inner_zero_right, neg_zero]

/-- **§4.8, second order ⇒ mixed** (converse, under the compatibility condition): if `u` solves
the second-order weak form and `u̇(0) = -d* ρ₀` weakly for some `ρ₀ ∈ W1`, then
`ρ(t) = ρ₀ + ∫₀ᵗ d u` makes `(u, ρ)` a mixed weak solution. -/
theorem secondOrder_imp_mixed [CompleteSpace W1] (hT : 0 ≤ T) (h : IsSecondOrderWeak d T w u')
    (ρ₀ : W1) (hρ₀ : ∀ v : d.domain, ⟪u' 0, (v : W0)⟫ = -⟪ρ₀, d v⟫) :
    ∃ ρ ρ' : ℝ → W1, IsMixedWeak d T w u' ρ ρ' ∧ ρ 0 = ρ₀ := by
  set g : ℝ → W1 := fun s => d (w (projIcc 0 T hT s)) with hg
  have hgc : Continuous g := h.cont.comp_continuous (continuous_subtype_val.comp
    continuous_projIcc) (fun s => (projIcc 0 T hT s).2)
  have hgt : ∀ t ∈ Icc 0 T, g t = d (w t) := fun t ht => by simp [g, projIcc_of_mem hT ht]
  set ρ : ℝ → W1 := fun t => ρ₀ + ∫ s in (0 : ℝ)..t, g s
  have hρd : ∀ t ∈ Icc 0 T, HasDerivWithinAt ρ (d (w t)) (Icc 0 T) t := fun t ht => by
    rw [← hgt t ht]
    exact ((hgc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add ρ₀).hasDerivWithinAt
  refine ⟨ρ, fun t => d (w t), ⟨h.du, h.cont, hρd, fun t ht v => ?_, fun t ht μ => rfl⟩,
    by simp [ρ]⟩
  have hc := const_of_hasDerivWithinAt_zero (T := T)
    (f := fun s => ⟪u' s, (v : W0)⟫ + innerSL ℝ (d v) (ρ s)) (fun s hs => by
      have h1 := (innerSL ℝ (d v)).hasFDerivAt.comp_hasDerivWithinAt s (hρd s hs)
      refine ((h.eq s hs v).add h1).congr_deriv ?_
      simp only [innerSL_apply_apply]
      linarith [real_inner_comm (d v) (d (w s))]) t ht
  have h0 : ⟪u' 0, (v : W0)⟫ + ⟪ρ 0, d v⟫ = 0 := by simp [ρ, hρ₀ v]
  simp only [innerSL_apply_apply] at hc
  linarith [real_inner_comm (d v) (ρ t), real_inner_comm (d v) (ρ 0)]

/-- The compatibility condition is necessary: if `u̇(0)` is not orthogonal to `ker d`, no
mixed weak solution has this `u`. -/
theorem not_mixed_of_harmonic (hT : 0 ≤ T) (z : d.domain) (hz : d z = 0)
    (hu : ⟪u' 0, (z : W0)⟫ ≠ 0) : ¬ ∃ ρ ρ', IsMixedWeak d T w u' ρ ρ' := by
  rintro ⟨ρ, ρ', h⟩
  exact hu ((mixed_imp_secondOrder h).2.2 0 ⟨le_rfl, hT⟩ z hz)

/-- **§4.8 gap: the claimed equivalence of the mixed and second-order scalar wave fails under
natural boundary conditions.** Whenever `ker d ≠ 0` (for `d = grad` on `H¹`: the constants),
`u(t) = t z` with `0 ≠ z ∈ ker d` solves the second-order weak form but is not the `u` of any
mixed weak solution.

Correction: the bijection holds onto second-order solutions with `u̇(0) ∈ range(-d*)`
(`secondOrder_imp_mixed`), which under closed range is `u̇(0) ⊥ ker d`, i.e. `∫ u̇(0) = 0`. -/
theorem secondOrder_not_mixed (hT : 0 ≤ T) (z : d.domain) (hz : d z = 0) (hz0 : (z : W0) ≠ 0) :
    IsSecondOrderWeak d T (fun t => t • z) (fun _ => (z : W0)) ∧
      ¬ ∃ ρ ρ', IsMixedWeak d T (fun t => t • z) (fun _ => (z : W0)) ρ ρ' := by
  refine ⟨⟨fun t _ => ?_, ?_, fun t _ v => ?_⟩, not_mixed_of_harmonic hT z hz ?_⟩
  · simpa using ((hasDerivAt_id t).smul_const (z : W0)).hasDerivWithinAt
  · simp only [LinearPMap.map_smul, hz, smul_zero]; exact continuousOn_const
  · simp only [LinearPMap.map_smul, hz, smul_zero, inner_zero_left, neg_zero]
    exact hasDerivWithinAt_const _ _ _
  · simpa using hz0

end ScalarWave

/-! ## §4.7: Koszul operator algebra -/

section Koszul

open Finset

/-- **§4.7 Koszul homotopy formula, operator-algebraic core** (AFW 2006, (3.9); stated without
proof or citation in the thesis): with `d = ∑ eᵢ ∂ᵢ` and `κ = ∑ xⱼ ιⱼ`,
`dκ + κd = ∑ xᵢ ∂ᵢ + ∑ eᵢ ιᵢ` (Euler operator plus form-degree operator), from the Weyl
relations `[∂ᵢ, xⱼ] = δᵢⱼ`, the CAR `ιⱼ eᵢ + eᵢ ιⱼ = δᵢⱼ`, and commutation of the polynomial
and exterior factors. On `H_r Λ^k` the right side acts by `r + k`. -/
theorem koszul_homotopy_core {A : Type*} [Ring A] {n : ℕ} (D X e ι : Fin n → A)
    (hDX : ∀ i j, D i * X j = X j * D i + if i = j then 1 else 0)
    (hDι : ∀ i j, D i * ι j = ι j * D i)
    (hXe : ∀ i j, e i * X j = X j * e i)
    (hCAR : ∀ i j, ι j * e i + e i * ι j = if i = j then 1 else 0) :
    (∑ i, e i * D i) * (∑ j, X j * ι j) + (∑ j, X j * ι j) * (∑ i, e i * D i)
      = ∑ i, X i * D i + ∑ i, e i * ι i := by
  simp only [sum_mul, mul_sum]
  rw [sum_comm (f := fun j i => e i * D i * (X j * ι j)), ← sum_add_distrib]
  have key : ∀ i j, e i * D i * (X j * ι j) + X j * ι j * (e i * D i)
      = X j * (if i = j then 1 else 0) * D i + e i * (if i = j then 1 else 0) * ι j := by
    intro i j
    have h1 : e i * D i * (X j * ι j) = X j * (e i * ι j) * D i
        + e i * (if i = j then 1 else 0) * ι j := by
      calc e i * D i * (X j * ι j) = e i * (D i * X j) * ι j := by noncomm_ring
        _ = e i * (X j * D i) * ι j + e i * (if i = j then 1 else 0) * ι j := by
            rw [hDX]; noncomm_ring
        _ = (e i * X j) * (D i * ι j) + e i * (if i = j then 1 else 0) * ι j := by noncomm_ring
        _ = X j * (e i * ι j) * D i + e i * (if i = j then 1 else 0) * ι j := by
            rw [hXe, hDι]; noncomm_ring
    have h2 : X j * ι j * (e i * D i) = X j * (ι j * e i) * D i := by noncomm_ring
    rw [h1, h2, ← (hCAR i j)]; noncomm_ring
  simp_rw [← sum_add_distrib, key]
  refine sum_congr rfl fun i _ => ?_
  simp [mul_ite, sum_add_distrib]

variable {𝕜 M : Type*} [Field 𝕜] [AddCommGroup M] [Module 𝕜 M]

/-- **§4.7(d), spanning part**, abstractly: if `(dκ + κd) ω = c ω` with `c ≠ 0` (on
`H_r Λ^k`, `c = r + k`), then `ω = κ (c⁻¹ dω) + d (c⁻¹ κω)`, so
`H_r Λ^k ⊆ κ H_{r-1} Λ^{k+1} + d H_{r+1} Λ^{k-1}`.

Correction: the thesis states `H_r Λ^k = κ H_{r-1}Λ^{k+1} ⊕ d H_{r+1}Λ^{k-1}` without the
hypothesis `r + k > 0` (i.e. `c ≠ 0`); it fails for `r = k = 0` (the constants). -/
theorem koszul_decomp (d κ : M →ₗ[𝕜] M) {c : 𝕜} (hc : c ≠ 0) {ω : M}
    (hω : d (κ ω) + κ (d ω) = c • ω) : ω = κ (c⁻¹ • d ω) + d (c⁻¹ • κ ω) := by
  rw [_root_.map_smul, _root_.map_smul, ← smul_add, add_comm, hω, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **§4.7(d), directness**: if `d² = 0`, `κ² = 0`, and `ω = κ α = d β` is an eigenvector of
`dκ + κd` with eigenvalue `c ≠ 0`, then `ω = 0`. (Uses `κ ∘ κ = 0`, which the thesis does not
mention.) -/
theorem koszul_direct (d κ : M →ₗ[𝕜] M) (hdd : ∀ x, d (d x) = 0) (hκκ : ∀ x, κ (κ x) = 0)
    {c : 𝕜} (hc : c ≠ 0) {ω α β : M} (hω : d (κ ω) + κ (d ω) = c • ω) (hα : ω = κ α)
    (hβ : ω = d β) : ω = 0 := by
  have h1 : κ ω = 0 := by rw [hα, hκκ]
  have h2 : d ω = 0 := by rw [hβ, hdd]
  rw [h1, h2, _root_.map_zero, _root_.map_zero, add_zero] at hω
  exact (smul_eq_zero.1 hω.symm).resolve_left hc

end Koszul

/-! ## §4.10: which pairs `P Λ⁰ × P⁻Λ¹` form subcomplexes (critic item 14)

Polynomial vector fields on `ℝ³` are `Fin 3 → MvPolynomial (Fin 3) ℝ`; the first-kind Nédélec
space is `P_r⁻Λ¹ = P_{r-1}³ ⊕ x × H_{r-1}³` (the 3D form of `P_{r-1}Λ¹ ⊕ κ H_{r-1}Λ²`). -/

section Nedelec

open MvPolynomial

/-- Polynomials in three variables. -/
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- `x × q` for a polynomial vector field `q`. -/
def xCross (q : Fin 3 → Poly3) : Fin 3 → Poly3 :=
  ![X 1 * q 2 - X 2 * q 1, X 2 * q 0 - X 0 * q 2, X 0 * q 1 - X 1 * q 0]

/-- Gradient of a polynomial. -/
def pgrad (f : Poly3) : Fin 3 → Poly3 := fun i => pderiv i f

/-- `P_r Λ⁰(ℝ³)`: polynomials of degree `≤ r`. -/
def PLambda0 (r : ℕ) : Set Poly3 := {f | f.totalDegree ≤ r}

/-- `P_r⁻ Λ¹(ℝ³) = P_{r-1}(ℝ³)³ ⊕ x × H_{r-1}(ℝ³)³` (Nédélec edge elements of the first kind),
for `r ≥ 1`. -/
def PminusLambda1 (r : ℕ) : Set (Fin 3 → Poly3) :=
  {v | ∃ p q : Fin 3 → Poly3, (∀ i, (p i).totalDegree ≤ r - 1) ∧
    (∀ i, (q i).IsHomogeneous (r - 1)) ∧ v = p + xCross q}

/-- `∂ᵢ` lowers the total degree (§4.7(a): `d P_r Λ^k ⊆ P_{r-1} Λ^{k+1}`). -/
theorem totalDegree_pderiv_le (i : Fin 3) (f : Poly3) :
    (pderiv i f).totalDegree ≤ f.totalDegree - 1 := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun k hk => ?_)
  have := ((homogeneousComponent_isHomogeneous k f).pderiv (i := i)).totalDegree_le
  have hk' := Finset.mem_range.1 hk
  omega

/-- The valid pairing of §4.10 (corrected list): `grad P_r Λ⁰ ⊆ P_r⁻ Λ¹`, since
`grad P_r ⊆ P_{r-1}³`. -/
theorem pgrad_mem_PminusLambda1 {r : ℕ} {f : Poly3} (hf : f ∈ PLambda0 r) :
    pgrad f ∈ PminusLambda1 r :=
  ⟨pgrad f, 0, fun i => (totalDegree_pderiv_le i f).trans (Nat.sub_le_sub_right hf 1),
    fun _ => isHomogeneous_zero _ _ _, by ext i : 1; fin_cases i <;> simp [xCross]⟩

/-- `grad x₀^{r+1} = ((r+1) x₀^r, 0, 0)`. -/
theorem pgrad_X0_pow (r : ℕ) :
    pgrad (X 0 ^ (r + 1)) = ![C ((r : ℝ) + 1) * X 0 ^ r, 0, 0] := by
  ext i : 1
  fin_cases i <;> simp [pgrad, Derivation.leibniz_pow, pderiv_X, Algebra.smul_def]

/-- **Thesis §4.10 error** (general `r ≥ 1`): `grad (x₀^{r+1}) ∉ P_r⁻Λ¹` although
`x₀^{r+1} ∈ P_{r+1}Λ⁰`. Hence `P_{r+1}Λ⁰ ⊗ V × P_r⁻Λ¹ ⊗ V × …` (the last two discretizations
listed for the matrix wave equation (4.14)) are not subcomplexes.

Correction: use `P_r Λ⁰` with `P_r⁻ Λ¹` (`pgrad_mem_PminusLambda1`). Proof: `x · (x × q) = 0`,
so `x · v` has degree `≤ r` for `v ∈ P_r⁻Λ¹`, while `x · grad x₀^{r+1} = (r+1) x₀^{r+1}`. -/
theorem pgrad_not_mem_PminusLambda1 {r : ℕ} (hr : 1 ≤ r) :
    X 0 ^ (r + 1) ∈ PLambda0 (r + 1) ∧ pgrad (X 0 ^ (r + 1)) ∉ PminusLambda1 r := by
  refine ⟨by simp [PLambda0, totalDegree_X_pow], ?_⟩
  rintro ⟨p, q, hp, -, h⟩
  rw [pgrad_X0_pow] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.add_apply,
    xCross, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have key : C ((r : ℝ) + 1) * X 0 ^ (r + 1) = X 0 * p 0 + X 1 * p 1 + X 2 * p 2 := by
    linear_combination X 0 * h0 + X 1 * h1 + X 2 * h2
  have hdeg : (X 0 * p 0 + X 1 * p 1 + X 2 * p 2 : Poly3).totalDegree ≤ r := by
    have hm : ∀ i, (X i * p i : Poly3).totalDegree ≤ r := fun i =>
      (totalDegree_mul _ _).trans (by rw [totalDegree_X]; have := hp i; omega)
    exact (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
      (max_le (hm 0) (hm 1))) (hm 2))
  rw [← key, C_mul_X_pow_eq_monomial, totalDegree_monomial _ (by positivity)] at hdeg
  simp [Finsupp.sum_add_index'] at hdeg

/-- The `r = 1` instance in function form (lowest-order Whitney/Nédélec fields `a + b × x`):
`grad x₀² = (2x₀, 0, 0)` is not of this form. -/
theorem grad_sq_not_whitney :
    ¬ ∃ a b : Fin 3 → ℝ, ∀ x : Fin 3 → ℝ, 2 * x 0 = a 0 + (b 1 * x 2 - b 2 * x 1) := by
  rintro ⟨a, b, h⟩
  have h0 := h 0
  have h1 := h (Pi.single 0 1)
  simp at h0 h1
  linarith

end Nedelec

/-! ## Lemma 3.5 (pointwise), as used in Props 4.17 and 4.19

`dA c = ∂_c A` is the first jet of a matrix field (`Feec.Jet1`), `curl` the row-wise curl
`(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}`. The identities are linear with constant coefficients, so
they hold distributionally as well (the form needed for `A ∈ H(curl)`). -/

section Curl

open Finset
open scoped Matrix

/-- Values of the Levi-Civita symbol `Feec.eps3`. -/
theorem eps3_apply (i j k : Fin 3) : eps3 i j k =
    if (i, j, k) = (0, 1, 2) ∨ (i, j, k) = (1, 2, 0) ∨ (i, j, k) = (2, 0, 1) then 1
    else if (i, j, k) = (0, 2, 1) ∨ (i, j, k) = (2, 1, 0) ∨ (i, j, k) = (1, 0, 2) then -1
    else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [eps3, Matrix.det_fin_three]

/-- **Lemma 3.5**: `tr curl A = -2 div vskw A`. -/
theorem trace_curl (dA : Jet1) : (curl dA).trace = -2 * ∑ a, vskw (dA a) a := by
  simp [Matrix.trace, curl, vskw, eps3_apply, Fin.sum_univ_three]; ring

/-- **Lemma 3.5**: `2 vskw curl A = grad tr A - div Aᵀ`. -/
theorem two_vskw_curl (dA : Jet1) (a : Fin 3) :
    2 * vskw (curl dA) a = ∑ b, dA a b b - ∑ b, dA b b a := by
  fin_cases a <;> simp [curl, vskw, eps3_apply, Fin.sum_univ_three] <;> ring

/-- **Lemma 3.5**: `div curl A = 0` (second jet `d2A b = ∂_b (dA)`, symmetric). -/
theorem div_curl (d2A : Fin 3 → Jet1) (hsym : ∀ b c, d2A b c = d2A c b) (a : Fin 3) :
    ∑ b, curl (d2A b) a b = 0 := by
  fin_cases a <;> simp [curl, eps3_apply, Fin.sum_univ_three, hsym 1 0, hsym 2 0, hsym 2 1] <;> ring

/-- Consequence of Lemma 3.5 used in Props 4.17/4.19 (the invariance `L(D ∩ K) ⊆ K` for
`K = 0 × TSD × TSD`): if `A` is symmetric, traceless and divergence-free (at the level of
first derivatives), then `curl A` is symmetric and traceless.

Note (Props 4.17, 4.19): this is the only part of the thesis' TSD argument that survives. The
remaining hypothesis `P_{L²(TSD)} D(L) ⊆ D(L)` fails (critic item 4: e.g. `A = e₁ (∇f)ᵀ` with
`f = f(x₂) ∈ H¹ \ H²`), so the thesis' conditional statements are vacuous; the unconditional
parts (`σ ≡ 0`, divergence constraints) are `prop_4_16`/`prop_4_18_i`, and
`reducing_of_invariant` shows the projection hypothesis is necessary for TSD propagation. -/
theorem curl_TSD (dA : Jet1) (hsym : ∀ c, (dA c)ᵀ = dA c) (htr : ∀ c, (dA c).trace = 0)
    (hdiv : div dA = 0) : (curl dA)ᵀ = curl dA ∧ (curl dA).trace = 0 := by
  have hs : ∀ c i j, dA c i j = dA c j i := fun c i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hsym c) j) i
  have h0 := htr 0; have h1 := htr 1; have h2 := htr 2
  have d0 := congrFun hdiv 0; have d1 := congrFun hdiv 1; have d2 := congrFun hdiv 2
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three] at h0 h1 h2
  simp only [div, Fin.sum_univ_three, Pi.zero_apply] at d0 d1 d2
  refine ⟨?_, ?_⟩
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [curl, eps3_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
      simp only [hs _ 1 0, hs _ 2 0, hs _ 2 1] at * <;> linarith
  · rw [trace_curl]
    simp [vskw, eps3_apply, Fin.sum_univ_three]
    simp only [hs _ 1 0, hs _ 2 0, hs _ 2 1]
    ring

end Curl

/-! ## Necessity of `P_K D(L) ⊆ D(L)` (time-reversal / reducing-subspace argument)

Not in the thesis. It shows that the "first itemized hypothesis" of Thm 4.4 is necessary for
constraint propagation (given density of `D(L) ∩ K` in `K`), so Props 4.17/4.19 cannot be
rescued on domains where that hypothesis fails. -/

section Group

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Explicit stand-in for Stone's theorem** (absent from Mathlib): a strongly continuous
group of isometries `U t` whose generator is `L` (`x ∈ D(L)` iff `t ↦ U t x` is
differentiable at `0`, with derivative `L x`). Every skew-adjoint `L` on a Hilbert space has
one (Stone); it is only ever used as a hypothesis. -/
structure UnitaryGroupGenerator (L : E →ₗ.[ℝ] E) where
  /-- the group `e^{tL}` -/
  U : ℝ → E →L[ℝ] E
  map_zero : U 0 = ContinuousLinearMap.id ℝ E
  map_add : ∀ s t, U (s + t) = (U s).comp (U t)
  norm_map : ∀ t x, ‖U t x‖ = ‖x‖
  cont : ∀ x, Continuous fun t => U t x
  mem_domain : ∀ x, x ∈ L.domain ↔ ∃ y, HasDerivAt (fun t => U t x) y 0
  hasDerivAt : ∀ x : L.domain, HasDerivAt (fun t => U t (x : E)) (L x) 0

namespace UnitaryGroupGenerator

variable {L : E →ₗ.[ℝ] E} (G : UnitaryGroupGenerator L)

/-- `U t ∘ U (-t) = id`. -/
theorem apply_neg_apply (t : ℝ) (x : E) : G.U t (G.U (-t) x) = x := by
  have := congrArg (fun A : E →L[ℝ] E => A x) (G.map_add t (-t))
  simp only [add_neg_cancel, G.map_zero, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply] at this
  exact this.symm

/-- The group is commutative. -/
theorem comm (s t : ℝ) (x : E) : G.U s (G.U t x) = G.U t (G.U s x) := by
  have h1 := congrArg (fun A : E →L[ℝ] E => A x) (G.map_add s t)
  have h2 := congrArg (fun A : E →L[ℝ] E => A x) (G.map_add t s)
  simp only [ContinuousLinearMap.comp_apply] at h1 h2
  rw [← h1, ← h2, add_comm]

/-- Each `U t` preserves inner products (polarization). -/
theorem inner_map_map (t : ℝ) (x y : E) : ⟪G.U t x, G.U t y⟫ = ⟪x, y⟫ :=
  (⟨(G.U t).toLinearMap, G.norm_map t⟩ : E →ₗᵢ[ℝ] E).inner_map_map x y

/-- `U t D(L) ⊆ D(L)` and `L U t = U t L` on `D(L)`. -/
theorem hasDerivAt_shift (t : ℝ) (x : L.domain) :
    HasDerivAt (fun s => G.U s (G.U t x)) (G.U t (L x)) 0 := by
  have := (G.U t).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (G.hasDerivAt x)
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp [G.comm s t]

/-- **Non-vacuity of `WellPosedHom`** (critic item 6): a generator of a unitary group is
well posed; `t ↦ U t x` is the strong solution of `U' = L U` for `x ∈ D(L)`. -/
theorem isStrongSolution (T : ℝ) (x : L.domain) :
    IsStrongSolution L T x 0 (fun t => G.U t x) := by
  have hmem : ∀ t, G.U t (x : E) ∈ L.domain := fun t =>
    (G.mem_domain _).2 ⟨_, G.hasDerivAt_shift t x⟩
  refine ⟨fun t _ => hmem t, fun t _ => ?_, by simp [G.map_zero]⟩
  have hL : L ⟨_, hmem t⟩ = G.U t (L x) :=
    (G.hasDerivAt ⟨_, hmem t⟩).unique (G.hasDerivAt_shift t x)
  have h1 : HasDerivAt (fun s => G.U (s - t) (x : E)) (L x) t := by
    have := G.hasDerivAt x
    rw [show (0 : ℝ) = t - t from (sub_self t).symm] at this
    exact this.comp_sub_const t t
  have h2 := (G.U t).hasFDerivAt.comp_hasDerivAt t h1
  rw [Pi.zero_apply, add_zero, hL]
  refine (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).hasDerivWithinAt
  have := congrArg (fun A : E →L[ℝ] E => A x) (G.map_add t (s - t))
  simp only [ContinuousLinearMap.comp_apply, add_sub_cancel] at this
  simp [this]

include G in
theorem wellPosedHom (T : ℝ) : WellPosedHom L T :=
  fun x hx => ⟨_, G.isStrongSolution T ⟨x, hx⟩⟩

/-- **Reducing subspace**: if a closed subspace `K` is invariant under the whole group
(`t ∈ ℝ`), then `P_K D(L) ⊆ D(L)` and `L P_K = P_K L` on `D(L)`. -/
theorem reducing_of_invariant (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (hK : ∀ t, ∀ x ∈ K, G.U t x ∈ K) :
    ∀ x : L.domain, ∃ h : K.starProjection (x : E) ∈ L.domain,
      L ⟨_, h⟩ = K.starProjection (L x) := by
  have hcomm : ∀ t x, K.starProjection (G.U t x) = G.U t (K.starProjection x) := by
    intro t x
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hK t _
      (K.starProjection_apply_mem x)) fun k hk => ?_
    rw [← _root_.map_sub, ← G.apply_neg_apply t k, G.inner_map_map]
    exact (Submodule.mem_orthogonal' K _).1 (K.sub_starProjection_mem_orthogonal x) _
      (hK _ _ hk)
  intro x
  have hd : HasDerivAt (fun t => G.U t (K.starProjection x)) (K.starProjection (L x)) 0 := by
    have := K.starProjection.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (G.hasDerivAt x)
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp [hcomm])
  have hmem : K.starProjection (x : E) ∈ L.domain := (G.mem_domain _).2 ⟨_, hd⟩
  exact ⟨hmem, (G.hasDerivAt ⟨_, hmem⟩).unique hd⟩

/-- **Necessity of the projection hypothesis** for constraint propagation: if every group
trajectory starting in `D(L) ∩ K` stays in `K` for all `t ∈ ℝ` and `D(L) ∩ K` is dense in `K`,
then `P_K D(L) ⊆ D(L)`. For the matrix wave (4.14) with `K = 0 × TSD × TSD`, this applies
via the time reversal `R(σ, E, B) = (-σ, E, -B)` (`invariant_of_reversal`), so where
`P_K D(L) ⊄ D(L)` the TSD constraints of Props 4.17/4.19 are not propagated for some data. -/
theorem projection_hyp_necessary (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (hdense : ∀ k ∈ K, k ∈ closure ((L.domain : Set E) ∩ K))
    (hprop : ∀ t, ∀ x ∈ L.domain, x ∈ K → G.U t x ∈ K) :
    ∀ x ∈ L.domain, K.starProjection x ∈ L.domain := by
  have hKc : IsClosed (K : Set E) := by
    rw [← Submodule.orthogonal_orthogonal K]; exact Submodule.isClosed_orthogonal _
  have hK : ∀ t, ∀ x ∈ K, G.U t x ∈ K := by
    intro t k hk
    have : G.U t k ∈ closure (G.U t '' ((L.domain : Set E) ∩ K)) :=
      mem_closure_image (G.U t).continuous.continuousAt (hdense k hk)
    refine closure_minimal ?_ hKc this
    rintro _ ⟨x, ⟨hxD, hxK⟩, rfl⟩
    exact hprop t x hxD hxK
  intro x hx
  exact (G.reducing_of_invariant K hK ⟨x, hx⟩).1

/-- Time reversal: forward invariance plus an involution `R` with `R U t = U (-t) R` and
`R K ⊆ K` gives invariance for all `t ∈ ℝ`. -/
theorem invariant_of_reversal (K : Submodule ℝ E) (R : E →L[ℝ] E) (hRR : ∀ x, R (R x) = x)
    (hRU : ∀ t x, R (G.U t x) = G.U (-t) (R x)) (hRK : ∀ x ∈ K, R x ∈ K)
    (hfwd : ∀ t, 0 ≤ t → ∀ x ∈ K, G.U t x ∈ K) : ∀ t, ∀ x ∈ K, G.U t x ∈ K := by
  intro t x hx
  rcases le_total 0 t with ht | ht
  · exact hfwd t ht x hx
  · have h := hRK _ (hfwd (-t) (neg_nonneg.2 ht) _ (hRK x hx))
    rwa [hRU, neg_neg, hRR] at h

end UnitaryGroupGenerator

end Group

end Feec.Constraints
