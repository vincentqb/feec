module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Feec.Ch4.Existence
public import Feec.Foundation.Complex
public import Feec.Foundation.Tensor

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
* **Props 4.17, 4.19** (critic item 4), abstract conditional form `prop_4_17` for
  `K = {0} × S1 × S2` under the thesis' projection hypothesis `P_K D(L) ⊆ D(L)`, with no
  density hypothesis; `prop_4_17_necessary`/`prop_4_17_iff` show that, given a Stone group and
  density of `D(L) ∩ K` in `K`, the projection hypothesis is also necessary. The time reversal
  `R(σ, E, B) = (-σ, E, -B)` of (4.14) is `revT`/`waveOp_revT`. The hypothesis holds for the
  periodic complex on `𝕋³` (`Feec.Torus.projKc_mem_domL`, giving `Feec.Torus.prop_4_17_torus`);
  its failure (the `H̊(curl)` part) on smooth bounded domains is not formalized (see the
  docstring of `prop_4_17`).
* **Lemma 3.5 (pointwise)**: `trace_curl`, `two_vskw_curl`, `div_curl`, `trace_curl_of_symm`,
  `curl_TSD`, `curl_TSD_div` (the operator hypotheses of `prop_4_17` in the TSD case).
* **§4.8** (critic item 14): mixed weak scalar wave ⇔ second-order weak form under the
  compatibility condition `u̇(0) ∈ range(-d*)` (`secondOrder_imp_mixed`, `mixed_rho_unique`);
  `secondOrder_not_mixed` refutes the claimed unconditional equivalence under natural boundary
  conditions. With `d = d1` the same statements cover the §4.9 elimination
  `(ü, v) = -(curl u, curl v)` of the reduced Maxwell system.
* **§4.9** (critic item 14): `mixed3_eliminate` eliminates `ρ` from the three-field system
  (4.12), in the corrected form `d/dt[(u̇, v) + (d0 σ, v)] = -(d1 u, d1 v)`.
* **§4.7** Koszul algebra, as abstract operator identities: `koszul_homotopy_core`,
  `koszul_decomp`, `koszul_direct` (the decomposition needs `r + k > 0`).
* **§4.10** (corrected list of discretizations): `pgrad_mem_PminusLambda1` (`P_r Λ⁰ × P_r⁻Λ¹`
  is valid) and `pgrad_not_mem_PminusLambda1` (`P_{r+1}Λ⁰ × P_r⁻Λ¹` is not a subcomplex, all
  `r ≥ 1`; critic item 14), `grad_sq_not_whitney`.
* **Existence hypotheses** (critic item 6): the Stone stand-in `Feec.UnitaryGroupGenerator`
  of `Feec.Ch4.Existence` is used throughout. `boundedComplex`, `boundedGroup`,
  `wellPosedHom_boundedComplex` and `exists_nontrivial_wellPosed` show that `WellPosedHom (-L)`
  and the group hypothesis of `prop_4_17_iff` hold for a nontrivial `HilbertComplex2`.

Solutions are strong solutions in the sense of `Feec.IsStrongSolution` (pointwise derivatives
within `[0,T]`; graph-norm continuity is not required). This makes the uniqueness and
propagation statements stronger than the thesis', but the existence conclusions
(`prop_4_16_exists`, `prop_4_18`) weaker than the thesis' `C⁰([0,T]; D(L)) ∩ C¹([0,T]; W)`
(critic item 5): they give a strong solution, not its graph-norm continuity.

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3, Thm 4.4, Cor 4.5: well-posedness and constraint
  propagation), §4.4 ((4.4)/(4.5), Thm 4.6), §4.7 (polynomial de Rham complex, Koszul
  decomposition), §4.8 (scalar wave), §4.9 ((4.12), Prop 4.16), §4.10 ((4.14)/(4.15),
  Props 4.17 and 4.18, discretizations), §4.11 ((4.16)–(4.18), Prop 4.19), and §3.4 (Lemma 3.5)
* [Arnold2018] (the FEEC framework: Hilbert complexes, dual complexes, the Hodge wave equation)
* [AFW2010], §3 (abstract Hilbert complexes, `ker d* = (range d)ᗮ`, Hodge decomposition)
* [BruningLesch1992] (Hilbert complexes)
* [AFW2006], §3 (polynomial differential forms, the Koszul complex and homotopy formula, the
  spaces `P_rΛ^k` and `P_r⁻Λ^k`)
* [Arnold2013] (spaces of finite element differential forms; cited in
  [QuennevilleBelair2015, §4.7])
* [Hiptmair2002] (Nédélec edge elements, Maxwell's equations)
* [Geveci1988], [GilletteHolstZhu2017] (mixed formulation of the wave equation; cited in
  [QuennevilleBelair2015, §4.8])
* [Baker1976], [Dupont1973] (second-order Galerkin formulation of the wave equation; cited in
  [QuennevilleBelair2015, §4.8])
* [CazenaveHaraux1998], Prop 4.1.6 and Cor 2.4.9 (as cited in [QuennevilleBelair2015, §4.3]
  for Thm 4.3)
* [Pazy1983], §1.1 and §1.10 (groups `exp(tA)` of bounded operators; unitary groups and
  Stone's theorem, the existence input behind `Feec.UnitaryGroupGenerator`)
* [ACBY1997] (the Einstein–Bianchi system behind Props 4.17/4.19)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open Set LinearPMap

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
Correction of thesis §4.1/§4.3: "the kernel of an unbounded operator is closed" needs closedness.

Cf. [QuennevilleBelair2015, §4.1]. -/
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
"conjecture". Neither density nor skew-adjointness nor semigroup theory is needed.

See [QuennevilleBelair2015, Thm 4.4 and Cor 4.5] (§4.3). -/
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

/-- **Thesis Thm 4.3/4.6 (uniqueness part)**: strong solutions of `U' = A U + F` for a
skew-symmetric `A` are unique (energy identity; no skew-adjointness or semigroup needed).

See [QuennevilleBelair2015, Thm 4.3 and Thm 4.6] (Thm 4.3 is cited there from
[CazenaveHaraux1998, Prop 4.1.6 and Cor 2.4.9]). -/
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

/-- The Hodge wave operator (4.5) in coordinates.

See [QuennevilleBelair2015, §4.4, (4.5)]. -/
theorem tot_waveOp (x : H.waveOp.domain) :
    tot W0 W1 W2 (H.waveOp x) = (-(H.d0† (H.prV1s ⟨x.1, x.2⟩)),
      H.d0 (H.pr0 ⟨x.1, x.2⟩) + H.d1† (H.prV2s ⟨x.1, x.2⟩), -(H.d1 (H.prV1 ⟨x.1, x.2⟩))) := by
  change (tot W0 W1 W2) ((tot W0 W1 W2).symm _) = _
  rw [LinearEquiv.apply_symm_apply]; rfl

/-- The Hodge wave operator is skew-symmetric on `D(L)` (the four adjoint identities).
Proved here directly so that Props 4.16/4.18 need no skew-symmetry hypothesis; no closed range
and no `d** = d` is used (only the formal-adjoint identities enter).

See [QuennevilleBelair2015, Thm 4.6] (proof, first display). -/
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

/-- Thesis (4.1a) for `d0`: `ker d0* = (range d0)ᗮ`.

See [QuennevilleBelair2015, §4.1, (4.1a)]; cf. [AFW2010, §3], [BruningLesch1992]. -/
theorem ker_adj0_eq : H.d0†.ker = (LinearMap.range H.d0.toFun)ᗮ :=
  (orth_range_eq_ker_adjoint H.d0 H.dense0).symm

/-- Thesis (4.1a) for `d1`: `ker d1* = (range d1)ᗮ`.

See [QuennevilleBelair2015, §4.1, (4.1a)]; cf. [AFW2010, §3], [BruningLesch1992]. -/
theorem ker_adj1_eq : H.d1†.ker = (LinearMap.range H.d1.toFun)ᗮ :=
  (orth_range_eq_ker_adjoint H.d1 H.dense1).symm

/-- `ker d0*` is closed (it is an orthogonal complement). -/
theorem isClosed_ker_adj0 : IsClosed (H.d0†.ker : Set W1) := by
  rw [ker_adj0_eq H]; exact Submodule.isClosed_orthogonal _

/-- `ker d0*` admits an orthogonal projection (used for `P_K`). -/
instance : (H.d0†.ker).HasOrthogonalProjection := by
  have : CompleteSpace (H.d0†.ker) := (isClosed_ker_adj0 H).completeSpace_coe
  infer_instance

/-- `B ⊆ Z`: `range d0 ⊆ ker d1` (Def. of Hilbert complex, §4.2).

See [QuennevilleBelair2015, §4.2]; cf. [AFW2010, §3], [Arnold2018]. -/
theorem range_d0_le_ker_d1 : LinearMap.range H.d0.toFun ≤ H.d1.ker := by
  rintro _ ⟨x, rfl⟩
  exact mem_ker_iff.2 ⟨⟨_, H.map_mem x⟩, rfl, H.comp_zero x⟩

/-- `(ker d0*)ᗮ = closure (range d0) ⊆ ker d1`: no closed range needed.

Cf. the Hodge decomposition [QuennevilleBelair2015, Thm 4.1] and [AFW2010, §3]. -/
theorem ker_adj0_orth_le : (H.d0†.ker)ᗮ ≤ H.d1.ker := by
  rw [ker_adj0_eq H, Submodule.orthogonal_orthogonal_eq_closure]
  exact Submodule.topologicalClosure_minimal _ (range_d0_le_ker_d1 H)
    (isClosed_ker H.d1 H.closed1)

/-- `d0* d1* = 0` in the form `range d1* ⊆ ker d0*`.

Cf. the dual complex of a Hilbert complex in [AFW2010, §3] and [Arnold2018]. -/
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

/-! ### Constraint subspaces `K = 0 × S1 × S2` (critic item 12) -/

section Kc

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2]

variable (W0) in
/-- A constraint subspace `{0} × S1 × S2 ⊆ W0 × W1 × W2` (the shape of `K` in Props 4.16–4.19). -/
def Kc (S1 : Submodule ℝ W1) (S2 : Submodule ℝ W2) : Submodule ℝ (Tot W0 W1 W2) :=
  ((⊥ : Submodule ℝ W0).prod (S1.prod S2)).comap (tot W0 W1 W2).toLinearMap

/-- Membership in `{0} × S1 × S2`. -/
theorem mem_Kc {S1 : Submodule ℝ W1} {S2 : Submodule ℝ W2} {x : Tot W0 W1 W2} :
    x ∈ Kc W0 S1 S2 ↔ (tot W0 W1 W2 x).1 = 0 ∧ (tot W0 W1 W2 x).2.1 ∈ S1 ∧
      (tot W0 W1 W2 x).2.2 ∈ S2 := by
  simp [Kc, Submodule.mem_prod]

variable (W0) (S1 : Submodule ℝ W1) (S2 : Submodule ℝ W2)
  [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection]

/-- The orthogonal projection onto `{0} × S1 × S2`: `0 × P_{S1} × P_{S2}`. -/
def projKc : Tot W0 W1 W2 →L[ℝ] Tot W0 W1 W2 :=
  (totL (W0 := W0) (W1 := W1) (W2 := W2)).symm.toContinuousLinearMap ∘L
    ((0 : W0 →L[ℝ] W0).prodMap (S1.starProjection.prodMap S2.starProjection)) ∘L
    (totL (W0 := W0) (W1 := W1) (W2 := W2)).toContinuousLinearMap

/-- `projKc` in coordinates. -/
theorem tot_projKc (x : Tot W0 W1 W2) : tot W0 W1 W2 (projKc W0 S1 S2 x) =
    (0, S1.starProjection (tot W0 W1 W2 x).2.1, S2.starProjection (tot W0 W1 W2 x).2.2) := by
  simp [projKc]; rfl

/-- `projKc` maps into `Kc`. -/
theorem projKc_mem (x : Tot W0 W1 W2) : projKc W0 S1 S2 x ∈ Kc W0 S1 S2 := by
  rw [mem_Kc, tot_projKc]
  exact ⟨rfl, Submodule.starProjection_apply_mem _ _, Submodule.starProjection_apply_mem _ _⟩

/-- `x - projKc x ⊥ Kc`. -/
theorem projKc_orth (x : Tot W0 W1 W2) : x - projKc W0 S1 S2 x ∈ (Kc W0 S1 S2)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro k hk
  rw [mem_Kc] at hk
  rw [inner_tot, _root_.map_sub, tot_projKc]
  simp only [Prod.fst_sub, Prod.snd_sub, hk.1, inner_zero_left, zero_add]
  rw [(Submodule.mem_orthogonal _ _).1 (Submodule.sub_starProjection_mem_orthogonal _) _ hk.2.1,
    (Submodule.mem_orthogonal _ _).1 (Submodule.sub_starProjection_mem_orthogonal _) _ hk.2.2,
    add_zero]

/-- `{0} × S1 × S2` has an orthogonal projection. -/
instance : (Kc W0 S1 S2).HasOrthogonalProjection :=
  ⟨fun x => ⟨_, projKc_mem W0 S1 S2 x, projKc_orth W0 S1 S2 x⟩⟩

/-- `projKc` is the orthogonal projection onto `Kc`. -/
theorem starProjection_Kc (x : Tot W0 W1 W2) :
    (Kc W0 S1 S2).starProjection x = projKc W0 S1 S2 x :=
  Submodule.eq_starProjection_of_mem_of_inner_eq_zero (projKc_mem W0 S1 S2 x) fun _ hw =>
    (Submodule.mem_orthogonal _ _).1 (projKc_orth W0 S1 S2 x) _ hw ▸ real_inner_comm _ _

end Kc

/-- The constraint subspace `K = {0} × ker d0* × Y ⊆ W0 × W1 × W2` of Prop 4.16
(`σ = 0`, "`div u = 0`", `ρ ∈ Y`). With `Y = ⊤` this is the subspace of Prop 4.18.

See [QuennevilleBelair2015, §4.9, Prop 4.16]. -/
def K (Y : Submodule ℝ W2) : Submodule ℝ (Tot W0 W1 W2) := Kc W0 (H.d0†.ker) Y

/-- Membership in the constraint subspace `K`. -/
theorem mem_K {Y : Submodule ℝ W2} {x : Tot W0 W1 W2} :
    x ∈ K H Y ↔ (tot W0 W1 W2 x).1 = 0 ∧ (tot W0 W1 W2 x).2.1 ∈ H.d0†.ker ∧
      (tot W0 W1 W2 x).2.2 ∈ Y :=
  mem_Kc

variable (Y : Submodule ℝ W2) [Y.HasOrthogonalProjection]

/-- The orthogonal projection onto `K`: `P_K = 0 × P_{ker d0*} × P_Y`. -/
def projK : Tot W0 W1 W2 →L[ℝ] Tot W0 W1 W2 := projKc W0 (H.d0†.ker) Y

/-- `P_K` in coordinates. -/
theorem tot_projK (x : Tot W0 W1 W2) : tot W0 W1 W2 (projK H Y x) =
    (0, (H.d0†.ker).starProjection (tot W0 W1 W2 x).2.1, Y.starProjection (tot W0 W1 W2 x).2.2) :=
  tot_projKc _ _ _ x

/-- `P_K` maps into `K`. -/
theorem projK_mem (x : Tot W0 W1 W2) : projK H Y x ∈ K H Y := projKc_mem _ _ _ x

/-- `x - P_K x ⊥ K`, so `P_K` is the orthogonal projection onto `K`. -/
theorem projK_orth (x : Tot W0 W1 W2) : x - projK H Y x ∈ (K H Y)ᗮ := projKc_orth _ _ _ x

variable {H Y}

/-- `P_K` preserves `D(L)`: the "first itemized hypothesis" of Thm 4.4, proved abstractly
(no closed range, no contractibility, no exactness). Uses `(ker d0*)ᗮ = cl(range d0) ⊆ ker d1`
and `Yᗮ ⊆ ker d1* ⊆ V2*`.

See [QuennevilleBelair2015, Thm 4.4] (first itemized hypothesis) and the proof of Prop 4.16
(§4.9). -/
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
`d1 u ∈ Y` by hypothesis.

See [QuennevilleBelair2015, Thm 4.4] (third itemized hypothesis) and the proof of Prop 4.16
(§4.9). -/
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
contractibility or density hypothesis. Skew-symmetry of `L` is proved (`waveOp_isSkewSymm`).

See [QuennevilleBelair2015, §4.9, Prop 4.16] (via Cor 4.5); cf. [Hiptmair2002] for the Maxwell
setting. -/
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
solution, and it stays in `K`.

See [QuennevilleBelair2015, Prop 4.16 and Thm 4.6]; cf. Stone's theorem, [Pazy1983, §1.10]. -/
theorem prop_4_16_exists (hY : LinearMap.range H.d1.toFun ≤ Y) {T : ℝ}
    (hHY : WellPosedHom (-H.waveOp) T) {U₀ : Tot W0 W1 W2} (hD : U₀ ∈ H.domL)
    (hU₀ : U₀ ∈ K H Y) :
    ∃ U, IsStrongSolution (-H.waveOp) T U₀ 0 U ∧ (∀ t ∈ Icc 0 T, U t ∈ K H Y) ∧
      ∀ U', IsStrongSolution (-H.waveOp) T U₀ 0 U' → EqOn U U' (Icc 0 T) := by
  obtain ⟨U, hU⟩ := hHY U₀ hD
  exact ⟨U, hU, prop_4_16 hY hU hU₀, fun U' hU' =>
    strong_unique _ (isSkewSymm_neg (waveOp_isSkewSymm H)) hU hU'⟩

/-- Prop 4.16 for the opposite sign convention `ξ' = L ξ` (time reversal).

See [QuennevilleBelair2015, Prop 4.16]. -/
theorem prop_4_16' (hY : LinearMap.range H.d1.toFun ≤ Y) {T : ℝ} {U₀ : Tot W0 W1 W2}
    {U : ℝ → Tot W0 W1 W2} (hU : IsStrongSolution H.waveOp T U₀ 0 U) (hU₀ : U₀ ∈ K H Y) :
    ∀ t ∈ Icc 0 T, U t ∈ K H Y :=
  propagate H.waveOp (waveOp_isSkewSymm H) (K H Y) (projK H Y) (projK_mem H Y)
    (projK_orth H Y) (fun _ hx => projK_mem_domL hY hx) (waveOp_mem_K hY) hU hU₀

/-! ### Prop 4.18: equivalence with the reduced two-field system (4.15) -/

variable (H) in
/-- Strong solution of the reduced system (4.15), `E' = -d1* B`, `B' = d1 E` (for the
linearized EB complex: `Ė = -curl B`, `Ḃ = curl E`), with `E ∈ V1`, `B ∈ V2*`.

See [QuennevilleBelair2015, §4.10, (4.15)]. -/
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
required by the thesis for (4.15).

See [QuennevilleBelair2015, §4.10, Prop 4.18]. -/
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
reading off the components.

See [QuennevilleBelair2015, §4.10, Prop 4.18]. -/
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
`E₀ ∈ ker d0*`, then `(0, E, B)` solves (4.14) with data `(0, E₀, B₀)`.

See [QuennevilleBelair2015, §4.10, Prop 4.18]. -/
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
via Prop 4.18 (ii) and the energy uniqueness for the skew-symmetric `-L`.

See [QuennevilleBelair2015, §4.10, Prop 4.18]. -/
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
the data space `V¹ × V²` is too weak for strong solutions of (4.14): `B₀` must lie in
`V2* = D(d1*)`, not merely in `W2`, and `E₀` in `V1 ∩ ker d0*`.

See [QuennevilleBelair2015, §4.10, Prop 4.18 and Thm 4.6]; cf. Stone's theorem,
[Pazy1983, §1.10]. -/
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
`(u̇, v) = -(ρ, d v)` for `v ∈ V0` and `(ρ̇, μ) = (d u, μ)` for `μ ∈ W1`. With `d = d1`
(`curl`) this is also the reduced Maxwell system of §4.9 (`σ ≡ 0`), whose elimination
`(ü, v) = -(curl u, curl v)` is `mixed_imp_secondOrder`.

See [QuennevilleBelair2015, §4.8]; cf. [Geveci1988], [GilletteHolstZhu2017]. -/
structure IsMixedWeak (d : W0 →ₗ.[ℝ] W1) (T : ℝ) (w : ℝ → d.domain) (u' : ℝ → W0)
    (ρ ρ' : ℝ → W1) : Prop where
  du : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (w s : W0)) (u' t) (Icc 0 T) t
  cont : ContinuousOn (fun s => d (w s)) (Icc 0 T)
  dρ : ∀ t ∈ Icc 0 T, HasDerivWithinAt ρ (ρ' t) (Icc 0 T) t
  eq_u : ∀ t ∈ Icc 0 T, ∀ v : d.domain, ⟪u' t, (v : W0)⟫ = -⟪ρ t, d v⟫
  eq_ρ : ∀ t ∈ Icc 0 T, ∀ μ : W1, ⟪ρ' t, μ⟫ = ⟪d (w t), μ⟫

/-- Second-order weak form `(ü, v) = -(d u, d v)`: `u ∈ C⁰(V0) ∩ C¹(W0)` and, for each test
`v ∈ V0`, `t ↦ (u̇, v)` is differentiable with derivative `-(d u, d v)` (the thesis' `ü` only
exists in `V0'`, so it is read as this duality pairing).

See [QuennevilleBelair2015, §4.8]; cf. [Baker1976], [Dupont1973]. -/
structure IsSecondOrderWeak (d : W0 →ₗ.[ℝ] W1) (T : ℝ) (w : ℝ → d.domain) (u' : ℝ → W0) :
    Prop where
  du : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (w s : W0)) (u' t) (Icc 0 T) t
  cont : ContinuousOn (fun s => d (w s)) (Icc 0 T)
  eq : ∀ t ∈ Icc 0 T, ∀ v : d.domain,
    HasDerivWithinAt (fun s => ⟪u' s, (v : W0)⟫) (-⟪d (w t), d v⟫) (Icc 0 T) t

variable {d : W0 →ₗ.[ℝ] W1} {T : ℝ} {w : ℝ → d.domain} {u' : ℝ → W0}

/-- **§4.8, mixed ⇒ second order**: a mixed weak solution has `ρ̇ = d u`, its `u` solves the
second-order weak form, and `u̇(t) ⊥ ker d` for all `t` (for `d = grad` on `H¹`:
`∫ u̇ = 0`).

See [QuennevilleBelair2015, §4.8]; cf. [Geveci1988]. -/
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
`ρ(t) = ρ₀ + ∫₀ᵗ d u` makes `(u, ρ)` a mixed weak solution.

See [QuennevilleBelair2015, §4.8]; cf. [Geveci1988]. -/
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

Correction: the correspondence holds onto second-order solutions with `u̇(0) ∈ range(-d*)`
(`secondOrder_imp_mixed`; `ρ` is then determined by `ρ₀`, `mixed_rho_unique`), which under closed range is `u̇(0) ⊥ ker d`, i.e. `∫ u̇(0) = 0`.

See [QuennevilleBelair2015, §4.8]. -/
theorem secondOrder_not_mixed (hT : 0 ≤ T) (z : d.domain) (hz : d z = 0) (hz0 : (z : W0) ≠ 0) :
    IsSecondOrderWeak d T (fun t => t • z) (fun _ => (z : W0)) ∧
      ¬ ∃ ρ ρ', IsMixedWeak d T (fun t => t • z) (fun _ => (z : W0)) ρ ρ' := by
  refine ⟨⟨fun t _ => ?_, ?_, fun t _ v => ?_⟩, not_mixed_of_harmonic hT z hz ?_⟩
  · simpa using ((hasDerivAt_id t).smul_const (z : W0)).hasDerivWithinAt
  · simp only [LinearPMap.map_smul, hz, smul_zero]; exact continuousOn_const
  · simp only [LinearPMap.map_smul, hz, smul_zero, inner_zero_left, neg_zero]
    exact hasDerivWithinAt_const _ _ _
  · simpa using hz0

/-- Given `u` and `ρ(0)`, the `ρ` of a mixed weak solution is unique (`ρ̇ = d u`), so the
correspondence of `secondOrder_imp_mixed` is one-to-one once `ρ₀` is fixed. -/
theorem mixed_rho_unique {ρ₁ ρ₁' ρ₂ ρ₂' : ℝ → W1} (h1 : IsMixedWeak d T w u' ρ₁ ρ₁')
    (h2 : IsMixedWeak d T w u' ρ₂ ρ₂') (h0 : ρ₁ 0 = ρ₂ 0) : EqOn ρ₁ ρ₂ (Icc 0 T) := by
  intro t ht
  have hd : ∀ s ∈ Icc 0 T, HasDerivWithinAt (fun s => ρ₁ s - ρ₂ s) 0 (Icc 0 T) s := by
    intro s hs
    have := (h1.dρ s hs).sub (h2.dρ s hs)
    rwa [(mixed_imp_secondOrder h1).2.1 s hs, (mixed_imp_secondOrder h2).2.1 s hs,
      sub_self] at this
  have := constant_of_has_deriv_right_zero (fun s hs => (hd s hs).continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici (hd s (Ico_subset_Icc_self hs)) hs) t ht
  rw [h0, sub_self] at this
  exact sub_eq_zero.1 this

end ScalarWave

/-! ## §4.9: eliminating `ρ` from the three-field vector wave (4.12) (critic item 14) -/

section VectorWave

variable {W0 W1 W2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
    [InnerProductSpace ℝ W2]

/-- Mixed weak form (4.12) of the Hodge wave on `V0 --d0--> V1 --d1--> W2` (for the vector
wave: `d0 = grad`, `d1 = curl`): `(σ̇, τ) = (u, d0 τ)`, `(u̇, v) = -(ρ, d1 v) - (d0 σ, v)`,
`(ρ̇, μ) = (d1 u, μ)` for `τ ∈ V0`, `v ∈ V1`, `μ ∈ W2`; `σ = sg`, `u = w` as in §4.8.

See [QuennevilleBelair2015, §4.9, (4.12)]. -/
structure IsMixedWeak3 (d0 : W0 →ₗ.[ℝ] W1) (d1 : W1 →ₗ.[ℝ] W2) (T : ℝ) (sg : ℝ → d0.domain)
    (σ' : ℝ → W0) (w : ℝ → d1.domain) (u' : ℝ → W1) (ρ ρ' : ℝ → W2) : Prop where
  dσ : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (sg s : W0)) (σ' t) (Icc 0 T) t
  du : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (w s : W1)) (u' t) (Icc 0 T) t
  dρ : ∀ t ∈ Icc 0 T, HasDerivWithinAt ρ (ρ' t) (Icc 0 T) t
  eq_σ : ∀ t ∈ Icc 0 T, ∀ τ : d0.domain, ⟪σ' t, (τ : W0)⟫ = ⟪(w t : W1), d0 τ⟫
  eq_u : ∀ t ∈ Icc 0 T, ∀ v : d1.domain,
    ⟪u' t, (v : W1)⟫ = -⟪ρ t, d1 v⟫ - ⟪d0 (sg t), (v : W1)⟫
  eq_ρ : ∀ t ∈ Icc 0 T, ∀ μ : W2, ⟪ρ' t, μ⟫ = ⟪d1 (w t), μ⟫

variable {d0 : W0 →ₗ.[ℝ] W1} {d1 : W1 →ₗ.[ℝ] W2} {T : ℝ} {sg : ℝ → d0.domain} {σ' : ℝ → W0}
  {w : ℝ → d1.domain} {u' : ℝ → W1} {ρ ρ' : ℝ → W2}

/-- **§4.9, elimination of `ρ`** (corrected form): a solution of (4.12) satisfies
`(σ̇, τ) = (u, d0 τ)` and `d/dt [(u̇, v) + (d0 σ, v)] = -(d1 u, d1 v)` for `v ∈ V1`.

Thesis gap: the thesis writes `(ü, v) = -(curl u, curl v) - (grad σ̇, v)`, but `σ ∈ C¹(W0)`
only, so `grad σ̇` need not exist; the `d0 σ` term must stay under the time derivative
(see `mixed3_eliminate_of_reg` for the thesis' form under extra regularity).

See [QuennevilleBelair2015, §4.9]. -/
theorem mixed3_eliminate (h : IsMixedWeak3 d0 d1 T sg σ' w u' ρ ρ') :
    (∀ t ∈ Icc 0 T, ∀ τ : d0.domain, ⟪σ' t, (τ : W0)⟫ = ⟪(w t : W1), d0 τ⟫) ∧
      ∀ t ∈ Icc 0 T, ∀ v : d1.domain, HasDerivWithinAt
        (fun s => ⟪u' s, (v : W1)⟫ + ⟪d0 (sg s), (v : W1)⟫) (-⟪d1 (w t), d1 v⟫) (Icc 0 T) t := by
  refine ⟨h.eq_σ, fun t ht v => ?_⟩
  have h1 := ((innerSL ℝ (d1 v)).hasFDerivAt.comp_hasDerivWithinAt t (h.dρ t ht)).neg
  refine (h1.congr_of_mem (fun s hs => ?_) ht).congr_deriv ?_
  · rw [h.eq_u s hs v]
    simp only [Function.comp_apply, Pi.neg_apply, innerSL_apply_apply]
    rw [real_inner_comm (ρ s) (d1 v)]
    ring
  · simp [real_inner_comm, h.eq_ρ t ht]

/-- §4.9 elimination in the thesis' form `(ü, v) = -(d1 u, d1 v) - (d0 σ̇, v)`, valid when
`t ↦ d0 σ(t)` is differentiable in `W1` with derivative `g` (`g = d0 σ̇` for `σ ∈ C¹(V0)`,
since `d0` is closed).

See [QuennevilleBelair2015, §4.9]. -/
theorem mixed3_eliminate_of_reg (h : IsMixedWeak3 d0 d1 T sg σ' w u' ρ ρ') {g : ℝ → W1}
    (hg : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => d0 (sg s)) (g t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, ∀ v : d1.domain, HasDerivWithinAt (fun s => ⟪u' s, (v : W1)⟫)
      (-⟪d1 (w t), d1 v⟫ - ⟪g t, (v : W1)⟫) (Icc 0 T) t := by
  intro t ht v
  have h2 := (hg t ht).inner ℝ (hasDerivWithinAt_const t (Icc 0 T) (v : W1))
  have := ((mixed3_eliminate h).2 t ht v).sub h2
  convert this using 1
  · funext s; simp
  · simp

end VectorWave

/-! ## §4.7: Koszul operator algebra -/

section Koszul

open Finset

/-- **§4.7 Koszul homotopy formula, operator-algebraic core** (AFW 2006, (3.9); stated without
proof or citation in the thesis): with `d = ∑ eᵢ ∂ᵢ` and `κ = ∑ xⱼ ιⱼ`,
`dκ + κd = ∑ xᵢ ∂ᵢ + ∑ eᵢ ιᵢ` (Euler operator plus form-degree operator), from the Weyl
relations `[∂ᵢ, xⱼ] = δᵢⱼ`, the CAR `ιⱼ eᵢ + eᵢ ιⱼ = δᵢⱼ`, and commutation of the polynomial
and exterior factors. On `H_r Λ^k` the right side acts by `r + k`.

See [QuennevilleBelair2015, §4.7] and [AFW2006, §3]; cf. [AFW2010], [Arnold2013]. -/
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
`H_r Λ^k`, `c = r + k` by `koszul_homotopy_core`), then `ω = κ (c⁻¹ dω) + d (c⁻¹ κω)`.
Combined with the degree bookkeeping `d : H_r Λ^k → H_{r-1} Λ^{k+1}`,
`κ : H_r Λ^k → H_{r+1} Λ^{k-1}` this gives `H_r Λ^k ⊆ κ H_{r-1} Λ^{k+1} + d H_{r+1} Λ^{k-1}`;
that bookkeeping and the polynomial-forms model are not formalized here (only this abstract
operator identity is), and the eigen-relation is a hypothesis.

Correction: the thesis states `H_r Λ^k = κ H_{r-1}Λ^{k+1} ⊕ d H_{r+1}Λ^{k-1}` without the
hypothesis `r + k > 0` (i.e. `c ≠ 0`); it fails for `r = k = 0` (the constants).

See [QuennevilleBelair2015, §4.7]; cf. [AFW2006, §3], [Arnold2013]. -/
theorem koszul_decomp (d κ : M →ₗ[𝕜] M) {c : 𝕜} (hc : c ≠ 0) {ω : M}
    (hω : d (κ ω) + κ (d ω) = c • ω) : ω = κ (c⁻¹ • d ω) + d (c⁻¹ • κ ω) := by
  rw [_root_.map_smul, _root_.map_smul, ← smul_add, add_comm, hω, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **§4.7(d), directness**, abstractly: if `d² = 0`, `κ² = 0`, and `ω = κ α = d β` is an
eigenvector of `dκ + κd` with eigenvalue `c ≠ 0`, then `ω = 0`. (Uses `κ ∘ κ = 0`, which the
thesis does not mention; as for `koszul_decomp`, the eigen-relation is a hypothesis.)

See [QuennevilleBelair2015, §4.7]; cf. [AFW2006, §3], [Arnold2013]. -/
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
for `r ≥ 1`. For `r = 0` natural-number subtraction gives `PminusLambda1 0 = PminusLambda1 1`
(a junk value, never used: the results below assume `1 ≤ r` or only use the `P_{r-1}` part).

See [QuennevilleBelair2015, §4.7]; cf. [AFW2006], [AFW2010], [Arnold2013], [Hiptmair2002]. -/
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
`grad P_r ⊆ P_{r-1}³`.

See [QuennevilleBelair2015, §4.10]; cf. the subcomplex property of `P_r⁻Λ` in [AFW2006],
[AFW2010]. -/
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
so `x · v` has degree `≤ r` for `v ∈ P_r⁻Λ¹`, while `x · grad x₀^{r+1} = (r+1) x₀^{r+1}`.

See [QuennevilleBelair2015, §4.10]; cf. the admissible pairings of `PΛ`/`P⁻Λ` spaces in [AFW2006],
[AFW2010]. -/
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
`grad x₀² = (2x₀, 0, 0)` is not of this form.

See [QuennevilleBelair2015, §4.10]; cf. [Hiptmair2002]. -/
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

/-- **Lemma 3.5**: `tr curl A = -2 div vskw A`.

See [QuennevilleBelair2015, §3.4, Lemma 3.5]. -/
theorem trace_curl (dA : Jet1) : (curl dA).trace = -2 * ∑ a, vskw (dA a) a := by
  simp [Matrix.trace, curl, vskw, eps3_apply, Fin.sum_univ_three]; ring

/-- **Lemma 3.5**: `2 vskw curl A = grad tr A - div Aᵀ`.

See [QuennevilleBelair2015, §3.4, Lemma 3.5]. -/
theorem two_vskw_curl (dA : Jet1) (a : Fin 3) :
    2 * vskw (curl dA) a = ∑ b, dA a b b - ∑ b, dA b b a := by
  fin_cases a <;> simp [curl, vskw, eps3_apply, Fin.sum_univ_three] <;> ring

/-- **Lemma 3.5**: `div curl A = 0` (second jet `d2A b = ∂_b (dA)`, symmetric).

See [QuennevilleBelair2015, §3.4, Lemma 3.5]. -/
theorem div_curl (d2A : Fin 3 → Jet1) (hsym : ∀ b c, d2A b c = d2A c b) (a : Fin 3) :
    ∑ b, curl (d2A b) a b = 0 := by
  fin_cases a <;> simp [curl, eps3_apply, Fin.sum_univ_three, hsym 1 0, hsym 2 0, hsym 2 1] <;> ring

/-- **Lemma 3.5, second bullet**: if `A` is symmetric, then `tr curl A = 0`.

See [QuennevilleBelair2015, §3.4, Lemma 3.5]. -/
theorem trace_curl_of_symm (dA : Jet1) (hsym : ∀ c, (dA c)ᵀ = dA c) : (curl dA).trace = 0 := by
  have hs : ∀ c i j, dA c i j = dA c j i := fun c i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hsym c) j) i
  rw [trace_curl]
  simp [vskw, eps3_apply, Fin.sum_univ_three]
  simp only [hs _ 1 0, hs _ 2 0, hs _ 2 1]
  ring

/-- **Lemma 3.5, third bullet (first-jet part)**, as used in Props 4.17/4.19: if `A` is
symmetric, traceless and divergence-free (at the level of first derivatives), then `curl A`
is symmetric and traceless. This is the pointwise content of the hypotheses `hd1`, `hd1s` of
`prop_4_17` for `S1 = S2 = L²(TSD)`; the divergence part is `div_curl`, and the combination
is `curl_TSD_div`.

See [QuennevilleBelair2015, §3.4, Lemma 3.5]. -/
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

/-- **Lemma 3.5, third bullet**: if `A` is TSD, then `curl A` is TSD. `dA` is the first jet of
`A` and `d2A b = ∂_b (dA)` its (symmetric) second jet; `∑_b ∂_b (curl A)_{ab} = 0` is
`div curl A = 0`. Linear with constant coefficients, hence valid distributionally.

See [QuennevilleBelair2015, §3.4, Lemma 3.5]. -/
theorem curl_TSD_div (dA : Jet1) (d2A : Fin 3 → Jet1) (hsym2 : ∀ b c, d2A b c = d2A c b)
    (hsym : ∀ c, (dA c)ᵀ = dA c) (htr : ∀ c, (dA c).trace = 0) (hdiv : div dA = 0) :
    (curl dA)ᵀ = curl dA ∧ (curl dA).trace = 0 ∧ ∀ a, ∑ b, curl (d2A b) a b = 0 :=
  ⟨(curl_TSD dA hsym htr hdiv).1, (curl_TSD dA hsym htr hdiv).2, div_curl d2A hsym2⟩

end Curl

/-! ## Orthogonal groups: reducing subspaces and time reversal

Built on the Stone stand-in `Feec.UnitaryGroupGenerator` of `Feec.Ch4.Existence`. Not in the
thesis: these results show that the "first itemized hypothesis" `P_K D(L) ⊆ D(L)` of Thm 4.4
is *necessary* for constraint propagation once `D(L) ∩ K` is dense in `K`
(`projection_hyp_necessary`; applied to (4.14) in `prop_4_17_necessary`). -/

section Group

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : E →ₗ.[ℝ] E} (G : UnitaryGroupGenerator L)

/-- `S t ∘ S (-t) = id`. -/
theorem group_apply_neg_apply (t : ℝ) (x : E) : G.S t (G.S (-t) x) = x := by
  have := congrArg (fun A : E →L[ℝ] E => A x) (G.map_add t (-t))
  simp only [add_neg_cancel, G.map_zero, one_apply_eq_self, mul_apply_eq_comp] at this
  exact this.symm

/-- Each `S t` preserves inner products (polarization). -/
theorem group_inner_map_map (t : ℝ) (x y : E) : ⟪G.S t x, G.S t y⟫ = ⟪x, y⟫ :=
  (LinearMap.norm_map_iff_inner_map_map (G.S t)).mp (G.norm_map t) x y

/-- The orbit `t ↦ S t x` of `x ∈ D(L)` is the strong solution of `U' = L U`, `U 0 = x`
(the existence half of Thesis Thm 4.3, homogeneous case, from the Stone stand-in).

See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, §1.10]. -/
theorem isStrongSolution_orbit (T : ℝ) (x : L.domain) :
    IsStrongSolution L T x 0 (fun t => G.S t x) := by
  refine ⟨fun t _ => G.mem_domain_apply x t, fun t _ => ?_, by simp [G.map_zero]⟩
  simp only [Pi.zero_apply, add_zero]
  rw [G.apply_comm x t]
  exact (G.hasDerivAt_apply x t).hasDerivWithinAt

/-- **Reducing subspace**: if a closed subspace `K` is invariant under the whole group
(`t ∈ ℝ`), then `P_K D(L) ⊆ D(L)` and `L P_K = P_K L` on `D(L)`.

Cf. unitary groups and Stone's theorem in [Pazy1983, §1.10]. -/
theorem reducing_of_invariant (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (hK : ∀ t, ∀ x ∈ K, G.S t x ∈ K) :
    ∀ x : L.domain, ∃ h : K.starProjection (x : E) ∈ L.domain,
      L ⟨_, h⟩ = K.starProjection (L x) := by
  have hcomm : ∀ t x, K.starProjection (G.S t x) = G.S t (K.starProjection x) := by
    intro t x
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hK t _
      (K.starProjection_apply_mem x)) fun k hk => ?_
    rw [← _root_.map_sub, ← group_apply_neg_apply G t k, group_inner_map_map]
    exact (Submodule.mem_orthogonal' K _).1 (K.sub_starProjection_mem_orthogonal x) _
      (hK _ _ hk)
  intro x
  have hd : HasDerivAt (fun t => G.S t (K.starProjection x)) (K.starProjection (L x)) 0 := by
    have := K.starProjection.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (G.hasDerivAt_zero x)
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp [hcomm])
  have hmem : K.starProjection (x : E) ∈ L.domain := (G.mem_domain_iff _).2 hd.differentiableAt
  exact ⟨hmem, (G.hasDerivAt_zero ⟨_, hmem⟩).unique hd⟩

/-- **Necessity of the projection hypothesis** for constraint propagation: if every group
trajectory starting in `D(L) ∩ K` stays in `K` for all `t ∈ ℝ` and `D(L) ∩ K` is dense in `K`,
then `P_K D(L) ⊆ D(L)`.

Cf. [QuennevilleBelair2015, Thm 4.4] (first itemized hypothesis) and [Pazy1983, §1.10]. -/
theorem projection_hyp_necessary (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (hdense : ∀ k ∈ K, k ∈ closure ((L.domain : Set E) ∩ K))
    (hprop : ∀ t, ∀ x ∈ L.domain, x ∈ K → G.S t x ∈ K) :
    ∀ x ∈ L.domain, K.starProjection x ∈ L.domain := by
  have hKc : IsClosed (K : Set E) := by
    rw [← Submodule.orthogonal_orthogonal K]; exact Submodule.isClosed_orthogonal _
  have hK : ∀ t, ∀ x ∈ K, G.S t x ∈ K := by
    intro t k hk
    have : G.S t k ∈ closure (G.S t '' ((L.domain : Set E) ∩ K)) :=
      mem_closure_image (G.S t).continuous.continuousAt (hdense k hk)
    refine closure_minimal ?_ hKc this
    rintro _ ⟨x, ⟨hxD, hxK⟩, rfl⟩
    exact hprop t x hxD hxK
  intro x hx
  exact (reducing_of_invariant G K hK ⟨x, hx⟩).1

/-- **Time reversal**: if `R` is a continuous involution with `R D(L) ⊆ D(L)` and
`L R = -R L` on `D(L)`, then `R S t = S (-t) R` on `D(L)` (both sides solve `U' = L U`;
energy uniqueness, using that a generator is skew-symmetric).

Cf. [Pazy1983, §1.10]. -/
theorem group_reversal (R : E →L[ℝ] E) (hRR : ∀ x, R (R x) = x)
    (hRD : ∀ x ∈ L.domain, R x ∈ L.domain)
    (hRL : ∀ x : L.domain, L ⟨R x, hRD x x.2⟩ = -R (L x)) :
    ∀ t, ∀ x ∈ L.domain, R (G.S t x) = G.S (-t) (R x) := by
  have fwd : ∀ t, 0 ≤ t → ∀ x ∈ L.domain, G.S t x = R (G.S (-t) (R x)) := by
    intro t ht x hx
    let y : L.domain := ⟨R x, hRD x hx⟩
    have hf : IsStrongSolution L t x 0 (fun s => R (G.S (-s) (R x))) := by
      refine ⟨fun s _ => hRD _ (G.mem_domain_apply y (-s)), fun s _ => ?_, by
        simp [G.map_zero, hRR]⟩
      have h1 := (G.hasDerivAt_apply y (-s)).scomp s (hasDerivAt_neg s)
      have h2 := R.hasFDerivAt.comp_hasDerivAt s h1
      have e := hRL ⟨_, G.mem_domain_apply y (-s)⟩
      rw [G.apply_comm y (-s)] at e
      simp only [Pi.zero_apply, add_zero]
      rw [e]
      refine h2.hasDerivWithinAt.congr_deriv ?_
      simp
    exact strong_unique L G.isSkewSymm (isStrongSolution_orbit G t ⟨x, hx⟩) hf ⟨ht, le_rfl⟩
  intro t x hx
  rcases le_total 0 t with ht | ht
  · rw [fwd t ht x hx, hRR]
  · rw [fwd (-t) (by linarith) (R x) (hRD x hx), neg_neg, hRR]

/-- Time reversal turns forward invariance of `D(L) ∩ K` into invariance for all `t ∈ ℝ`. -/
theorem invariant_of_reversal (K : Submodule ℝ E) (R : E →L[ℝ] E) (hRR : ∀ x, R (R x) = x)
    (hRD : ∀ x ∈ L.domain, R x ∈ L.domain)
    (hRU : ∀ t, ∀ x ∈ L.domain, R (G.S t x) = G.S (-t) (R x)) (hRK : ∀ x ∈ K, R x ∈ K)
    (hfwd : ∀ t, 0 ≤ t → ∀ x ∈ L.domain, x ∈ K → G.S t x ∈ K) :
    ∀ t, ∀ x ∈ L.domain, x ∈ K → G.S t x ∈ K := by
  intro t x hx hxK
  rcases le_total 0 t with ht | ht
  · exact hfwd t ht x hx hxK
  · have h := hRK _ (hfwd (-t) (neg_nonneg.2 ht) _ (hRD x hx) (hRK x hxK))
    rwa [hRU _ _ (hRD x hx), neg_neg, hRR] at h

end Group


/-! ## Props 4.17/4.19 (abstract TSD form), time reversal of (4.14), bounded witnesses

Props 4.17 and 4.19 propagate the constraint `K = {0} × L²(TSD) × L²(TSD)` for the matrix
Hodge waves (4.14) and (4.18). Abstractly, `K = {0} × S1 × S2` with closed `S1 ⊆ ker d0*`,
`d1 (V1 ∩ S1) ⊆ S2`, `d1* (V2* ∩ S2) ⊆ S1` (for TSD: the distributional Lemma 3.5,
`curl_TSD`/`div_curl`), and the thesis' projection hypothesis `P_K D(L) ⊆ D(L)`. -/

section TSD

open HilbertComplex2

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]

variable (W0 W1 W2) in
/-- The time reversal `R(σ, u, ρ) = (-σ, u, -ρ)` of the Hodge wave (4.14).

See [QuennevilleBelair2015, §4.10, (4.14)]. -/
def revT : Tot W0 W1 W2 →L[ℝ] Tot W0 W1 W2 :=
  (totL (W0 := W0) (W1 := W1) (W2 := W2)).symm.toContinuousLinearMap ∘L
    ((-ContinuousLinearMap.id ℝ W0).prodMap
      ((ContinuousLinearMap.id ℝ W1).prodMap (-ContinuousLinearMap.id ℝ W2))) ∘L
    (totL (W0 := W0) (W1 := W1) (W2 := W2)).toContinuousLinearMap

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2] in
/-- `R` in coordinates. -/
theorem tot_revT (x : Tot W0 W1 W2) :
    tot W0 W1 W2 (revT W0 W1 W2 x) = (-(tot W0 W1 W2 x).1, (tot W0 W1 W2 x).2.1,
      -(tot W0 W1 W2 x).2.2) := by
  simp [revT]; rfl

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2] in
/-- `R` is an involution. -/
theorem revT_revT (x : Tot W0 W1 W2) : revT W0 W1 W2 (revT W0 W1 W2 x) = x :=
  (tot W0 W1 W2).injective (by rw [tot_revT, tot_revT]; simp)

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2] in
/-- `R` preserves `{0} × S1 × S2`. -/
theorem revT_mem_Kc {S1 : Submodule ℝ W1} {S2 : Submodule ℝ W2} {x : Tot W0 W1 W2}
    (hx : x ∈ Kc W0 S1 S2) : revT W0 W1 W2 x ∈ Kc W0 S1 S2 := by
  rw [mem_Kc] at hx ⊢
  rw [tot_revT]
  exact ⟨by simp [hx.1], hx.2.1, S2.neg_mem hx.2.2⟩

variable (H : HilbertComplex2 W0 W1 W2)

/-- `R` preserves `D(L)`. -/
theorem revT_mem_domL {x : Tot W0 W1 W2} (hx : x ∈ H.domL) : revT W0 W1 W2 x ∈ H.domL := by
  rw [mem_domL] at hx ⊢
  rw [tot_revT]
  exact ⟨H.d0.domain.neg_mem hx.1, hx.2.1, H.d1†.domain.neg_mem hx.2.2⟩

/-- Time-reversal symmetry of (4.14): `L R = -R L` on `D(L)`.

See [QuennevilleBelair2015, §4.10, (4.14)]. -/
theorem waveOp_revT (x : H.waveOp.domain) :
    H.waveOp ⟨revT W0 W1 W2 x, revT_mem_domL H x.2⟩ = -revT W0 W1 W2 (H.waveOp x) := by
  apply (tot W0 W1 W2).injective
  rw [_root_.map_neg, tot_revT, tot_waveOp, tot_waveOp]
  have h0 : H.pr0 ⟨revT W0 W1 W2 x, revT_mem_domL H x.2⟩ = -H.pr0 ⟨x.1, x.2⟩ :=
    Subtype.ext (by simp [tot_revT])
  have h1 : H.prV1 ⟨revT W0 W1 W2 x, revT_mem_domL H x.2⟩ = H.prV1 ⟨x.1, x.2⟩ :=
    Subtype.ext (by simp [tot_revT])
  have h1s : H.prV1s ⟨revT W0 W1 W2 x, revT_mem_domL H x.2⟩ = H.prV1s ⟨x.1, x.2⟩ :=
    Subtype.ext (by simp [tot_revT])
  have h2s : H.prV2s ⟨revT W0 W1 W2 x, revT_mem_domL H x.2⟩ = -H.prV2s ⟨x.1, x.2⟩ :=
    Subtype.ext (by simp [tot_revT])
  simp only [h0, h1, h1s, h2s, LinearPMap.map_neg, Prod.neg_mk, neg_neg, neg_add]

variable {H} {S1 : Submodule ℝ W1} {S2 : Submodule ℝ W2}

/-- `L (D(L) ∩ K) ⊆ K` for `K = {0} × S1 × S2` (the "third itemized hypothesis" of Thm 4.4,
as checked in Props 4.17/4.19 via Lemma 3.5).

See [QuennevilleBelair2015, Thm 4.4] and the proofs of Props 4.17 and 4.19 (§4.10, §4.11). -/
theorem waveOp_mem_Kc (hS1 : S1 ≤ H.d0†.ker) (hd1 : ∀ u : H.d1.domain, (u : W1) ∈ S1 → H.d1 u ∈ S2)
    (hd1s : ∀ ρ : H.d1†.domain, (ρ : W2) ∈ S2 → H.d1† ρ ∈ S1) (x : H.waveOp.domain)
    (hx : (x : Tot W0 W1 W2) ∈ Kc W0 S1 S2) : H.waveOp x ∈ Kc W0 S1 S2 := by
  rw [mem_Kc] at hx ⊢
  rw [tot_waveOp]
  have hσ : H.pr0 ⟨x.1, x.2⟩ = 0 := Subtype.ext hx.1
  have hu : H.d0† (H.prV1s ⟨x.1, x.2⟩) = 0 := by
    obtain ⟨y, hy, hy0⟩ := mem_ker_iff.1 (hS1 hx.2.1)
    have : H.prV1s ⟨x.1, x.2⟩ = y := Subtype.ext hy
    rw [this, hy0]
  refine ⟨by simp [hu], ?_, S2.neg_mem (hd1 _ hx.2.1)⟩
  simp only [hσ, LinearPMap.map_zero, zero_add]
  exact hd1s _ hx.2.2

variable [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection]

/-- Sufficiency: under the projection hypothesis `P_K D(L) ⊆ D(L)` and invariance, strong
solutions of (4.14) starting in `K = {0} × S1 × S2` stay in `K`.

See [QuennevilleBelair2015, Thm 4.4 and Cor 4.5]. -/
theorem Kc_propagate (hS1 : S1 ≤ H.d0†.ker)
    (hPD : ∀ x ∈ H.domL, projKc W0 S1 S2 x ∈ H.domL)
    (hd1 : ∀ u : H.d1.domain, (u : W1) ∈ S1 → H.d1 u ∈ S2)
    (hd1s : ∀ ρ : H.d1†.domain, (ρ : W2) ∈ S2 → H.d1† ρ ∈ S1) {T : ℝ} {U₀ : Tot W0 W1 W2}
    {U : ℝ → Tot W0 W1 W2} (hU : IsStrongSolution (-H.waveOp) T U₀ 0 U)
    (hU₀ : U₀ ∈ Kc W0 S1 S2) : ∀ t ∈ Icc 0 T, U t ∈ Kc W0 S1 S2 :=
  propagate (-H.waveOp) (isSkewSymm_neg (waveOp_isSkewSymm H)) _ (projKc W0 S1 S2)
    (projKc_mem W0 S1 S2) (projKc_orth W0 S1 S2) hPD
    (fun x hx => by
      rw [LinearPMap.neg_apply]
      exact neg_mem (waveOp_mem_Kc hS1 hd1 hd1s x hx)) hU hU₀

/-- **Thesis Props 4.17 and 4.19** (abstract, conditional form). For the Hodge wave (4.14)
(`ξ' = -L ξ`) and `K = {0} × S1 × S2` with closed `S1 ⊆ ker d0*`, `d1 (V1 ∩ S1) ⊆ S2` and
`d1* (V2* ∩ S2) ⊆ S1`, assume the projection hypothesis `P_K D(L) ⊆ D(L)`. Then for data
`(0, E₀, B₀) ∈ D(L)` with `E₀ ∈ S1`, `B₀ ∈ S2`, the solution stays in `K` (`σ ≡ 0`, `E, B`
stay in `S1, S2`), and `(E, B)` solves the reduced system (4.15) ("the equations of Prop 3.4").

Instances: Prop 4.17 is the linearized EB complex (`d0 = grad`, `d1 = curl` on matrix fields),
Prop 4.19 the strong-symmetry complex (4.16)/(4.17) (`d0 = grad grad`, `d1 = curl` on `S`);
in both `S1 = S2 = L²(TSD)`, and `hd1`, `hd1s` are the distributional Lemma 3.5
(`curl_TSD`, `div_curl`: curl maps TSD fields with `L²` curl into TSD), while
`L²(TSD) ⊆ ker d0*` holds because TSD fields are divergence-free (resp. `div div`-free).

Thesis gap / Correction: the density "conjectures" of the thesis are not needed, and the
projection hypothesis cannot be dropped (`prop_4_17_iff`). Whether it holds depends on the
domain:
* it holds for the periodic complex on the flat torus `𝕋³`, and Prop 4.17 holds there
  unconditionally: this is formalized in `Feec.Ch4.Torus` on the Fourier side (`ℓ²(ℤ³)`,
  isometric to `L²(𝕋³)` by `Feec.Torus.fieldFourier`). At frequency `ξ` the TSD fibre
  `{M symmetric, tr M = 0, M ξ = 0}` is orthogonal to every `c ξᵀ`
  (`Feec.Torus.inner_outer_tsd`), the fibre projection commutes with the curl symbol, and
  `|ξ| |(P_TSD A)^(ξ)| = |P_ξ(ξ × rows(Â(ξ)))| ≤ |ξ × rows(Â(ξ))|`
  (`Feec.Torus.norm_freq_mul_norm_proj`); hence `P_TSD H(curl) ⊆ H¹ ⊆ H(curl)`
  (`Feec.Torus.projTSD_mem_H1`, `Feec.Torus.H1M_le_Hcurl`). All hypotheses of this theorem are
  discharged for the periodic complex `Feec.Torus.periodicComplex` with `S1 = S2 = L²(TSD)`,
  giving `Feec.Torus.prop_4_17_torus`. The review's claim that the hypothesis fails on every
  domain via `A = e₁ (∇f)ᵀ` confuses `P_TSD` with the pointwise `dev sym`: that `A` is
  orthogonal to `L²(TSD)` on `𝕋³` (`Feec.Torus.projTSD_eq_zero_of_outer`);
* its `H̊(curl)` part (electric boundary condition) fails on every smooth bounded domain `Ω`
  (not formalized; it needs traces and elliptic regularity):
  a symmetric traceless matrix whose rows have zero tangential trace vanishes, so
  `P_TSD E ∈ H̊(curl)` would force `P_TSD E = 0` on `∂Ω`; but for `E = φ A` with
  `φ ∈ C_c^∞(Ω)`, `∫ φ ≠ 0`, `dev sym A ≠ 0`, the Dirichlet Lamé-type problem defining
  `P_TSD E = dev sym (E - grad w)` gives a nonzero boundary flux of `dev sym grad w`.
So the statement is a genuine theorem (its hypotheses are satisfiable) but does not apply to
bounded domains with the `H̊(curl)` condition, where by `prop_4_17_iff` TSD propagation fails
for some data unless `D(L) ∩ K` is not dense in `K`.

See [QuennevilleBelair2015, §4.10, Prop 4.17 and §4.11, Prop 4.19]; for the EB system cf.
[ACBY1997]. -/
theorem prop_4_17 (hS1 : S1 ≤ H.d0†.ker) (hPD : ∀ x ∈ H.domL, projKc W0 S1 S2 x ∈ H.domL)
    (hd1 : ∀ u : H.d1.domain, (u : W1) ∈ S1 → H.d1 u ∈ S2)
    (hd1s : ∀ ρ : H.d1†.domain, (ρ : W2) ∈ S2 → H.d1† ρ ∈ S1) {T : ℝ} {E₀ : W1} {B₀ : W2}
    {U : ℝ → Tot W0 W1 W2} (hE₀ : E₀ ∈ S1) (hB₀ : B₀ ∈ S2)
    (hU : IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0 U) :
    (∀ t ∈ Icc 0 T, U t ∈ Kc W0 S1 S2) ∧
      IsReducedSolution H T E₀ B₀ (fun t => (tot W0 W1 W2 (U t)).2.1)
        (fun t => (tot W0 W1 W2 (U t)).2.2) :=
  ⟨Kc_propagate hS1 hPD hd1 hd1s hU (by rw [mem_Kc, tot_ini]; exact ⟨rfl, hE₀, hB₀⟩),
    (prop_4_18_i (hS1 hE₀) hU).2⟩

/-- **Necessity of the projection hypothesis in Props 4.17/4.19** (not in the thesis). If
`-L` generates an orthogonal group (Stone stand-in), `D(L) ∩ K` is dense in `K`, and every
strong solution of (4.14) starting in `D(L) ∩ K` stays in `K`, then `P_K D(L) ⊆ D(L)`.
Proof: forward invariance, the time reversal `R(σ, E, B) = (-σ, E, -B)` (`waveOp_revT`,
`group_reversal`) for backward invariance, then the reducing-subspace argument.

Cf. [QuennevilleBelair2015, Props 4.17 and 4.19] and [Pazy1983, §1.10]. -/
theorem prop_4_17_necessary (G : UnitaryGroupGenerator (-H.waveOp))
    (hdense : ∀ k ∈ Kc W0 S1 S2, k ∈ closure ((H.domL : Set (Tot W0 W1 W2)) ∩ Kc W0 S1 S2))
    (hprop : ∀ (T : ℝ) (U₀ : Tot W0 W1 W2) (U : ℝ → Tot W0 W1 W2), U₀ ∈ Kc W0 S1 S2 →
      IsStrongSolution (-H.waveOp) T U₀ 0 U → ∀ t ∈ Icc 0 T, U t ∈ Kc W0 S1 S2) :
    ∀ x ∈ H.domL, projKc W0 S1 S2 x ∈ H.domL := by
  intro x hx
  rw [← starProjection_Kc]
  have hRL : ∀ y : (-H.waveOp).domain, (-H.waveOp) ⟨revT W0 W1 W2 y, revT_mem_domL H y.2⟩ =
      -revT W0 W1 W2 ((-H.waveOp) y) := fun y => by
    rw [LinearPMap.neg_apply, LinearPMap.neg_apply, _root_.map_neg, neg_neg]
    exact neg_eq_iff_eq_neg.2 (waveOp_revT H y)
  refine projection_hyp_necessary G _ hdense ?_ x hx
  refine invariant_of_reversal G _ (revT W0 W1 W2) revT_revT (fun y hy => revT_mem_domL H hy)
    (group_reversal G _ revT_revT (fun y hy => revT_mem_domL H hy) hRL)
    (fun y hy => revT_mem_Kc hy) ?_
  intro t ht y hy hyK
  exact hprop t y _ hyK (isStrongSolution_orbit G t ⟨y, hy⟩) t ⟨ht, le_rfl⟩

/-- **Props 4.17/4.19, characterization**: with a Stone group for `-L` and `D(L) ∩ K` dense in
`K`, TSD-type constraints propagate for all data iff `P_K D(L) ⊆ D(L)`.

Cf. [QuennevilleBelair2015, Props 4.17 and 4.19] and [Pazy1983, §1.10]. -/
theorem prop_4_17_iff (G : UnitaryGroupGenerator (-H.waveOp)) (hS1 : S1 ≤ H.d0†.ker)
    (hd1 : ∀ u : H.d1.domain, (u : W1) ∈ S1 → H.d1 u ∈ S2)
    (hd1s : ∀ ρ : H.d1†.domain, (ρ : W2) ∈ S2 → H.d1† ρ ∈ S1)
    (hdense : ∀ k ∈ Kc W0 S1 S2, k ∈ closure ((H.domL : Set (Tot W0 W1 W2)) ∩ Kc W0 S1 S2)) :
    (∀ (T : ℝ) (U₀ : Tot W0 W1 W2) (U : ℝ → Tot W0 W1 W2), U₀ ∈ Kc W0 S1 S2 →
      IsStrongSolution (-H.waveOp) T U₀ 0 U → ∀ t ∈ Icc 0 T, U t ∈ Kc W0 S1 S2) ↔
      ∀ x ∈ H.domL, projKc W0 S1 S2 x ∈ H.domL :=
  ⟨prop_4_17_necessary G hdense, fun hPD _ _ _ hU₀ hU => Kc_propagate hS1 hPD hd1 hd1s hU hU₀⟩

end TSD

/-! ## Non-vacuity: bounded Hilbert complexes (critic item 6)

For bounded, everywhere defined `d0 = A0`, `d1 = A1` with `A1 A0 = 0`, `-L` is bounded and
generates an orthogonal group, so `WellPosedHom (-L)` and the group hypothesis of
`prop_4_17_iff` are satisfiable for nontrivial complexes. -/

section Bounded

open HilbertComplex2

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]

/-- An everywhere defined bounded operator is closed. -/
theorem isClosed_toPMap_top {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (A : F →L[ℝ] G) :
    ((A : F →ₗ[ℝ] G).toPMap ⊤).IsClosed := by
  have : (((A : F →ₗ[ℝ] G).toPMap ⊤).graph : Set (F × G)) = {p | A p.1 = p.2} := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearPMap.mem_graph_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨z, hz, hy⟩ => by rw [← hz, ← hy]; rfl, fun h => ⟨⟨x, trivial⟩, rfl, h⟩⟩
  change IsClosed (((A : F →ₗ[ℝ] G).toPMap ⊤).graph : Set (F × G))
  rw [this]
  exact isClosed_eq (A.continuous.comp continuous_fst) continuous_snd

/-- The Hilbert complex of bounded operators `A0 : W0 → W1`, `A1 : W1 → W2`, `A1 A0 = 0`.

Cf. Hilbert complexes in [BruningLesch1992], [AFW2010, §3]. -/
def boundedComplex (A0 : W0 →L[ℝ] W1) (A1 : W1 →L[ℝ] W2) (h : ∀ x, A1 (A0 x) = 0) :
    HilbertComplex2 W0 W1 W2 where
  d0 := (A0 : W0 →ₗ[ℝ] W1).toPMap ⊤
  d1 := (A1 : W1 →ₗ[ℝ] W2).toPMap ⊤
  dense0 := by simp
  dense1 := by simp
  closed0 := isClosed_toPMap_top A0
  closed1 := isClosed_toPMap_top A1
  map_mem _ := trivial
  comp_zero x := h x

variable (A0 : W0 →L[ℝ] W1) (A1 : W1 →L[ℝ] W2) (h : ∀ x, A1 (A0 x) = 0)

/-- `d0 = A0`. -/
@[simp] theorem boundedComplex_d0_apply (y : (boundedComplex A0 A1 h).d0.domain) :
    (boundedComplex A0 A1 h).d0 y = A0 y := rfl

/-- `d1 = A1`. -/
@[simp] theorem boundedComplex_d1_apply (y : (boundedComplex A0 A1 h).d1.domain) :
    (boundedComplex A0 A1 h).d1 y = A1 y := rfl

/-- `d0* = A0*` (Hilbert adjoint). -/
theorem boundedComplex_adj0 : (boundedComplex A0 A1 h).d0† = A0.adjoint.toPMap ⊤ :=
  A0.toPMap_adjoint_eq_adjoint_toPMap_of_dense (by simp)

/-- `d1* = A1*` (Hilbert adjoint). -/
theorem boundedComplex_adj1 : (boundedComplex A0 A1 h).d1† = A1.adjoint.toPMap ⊤ :=
  A1.toPMap_adjoint_eq_adjoint_toPMap_of_dense (by simp)

/-- `d0* y = A0* y`. -/
theorem boundedComplex_adj0_apply (y : (boundedComplex A0 A1 h).d0†.domain) :
    (boundedComplex A0 A1 h).d0† y = A0.adjoint y :=
  ((boundedComplex_adj0 A0 A1 h).ge.2 (x := ⟨(y : W1), trivial⟩) rfl).symm

/-- `d1* y = A1* y`. -/
theorem boundedComplex_adj1_apply (y : (boundedComplex A0 A1 h).d1†.domain) :
    (boundedComplex A0 A1 h).d1† y = A1.adjoint y :=
  ((boundedComplex_adj1 A0 A1 h).ge.2 (x := ⟨(y : W2), trivial⟩) rfl).symm

/-- `D(L) = W` for a bounded complex. -/
theorem boundedComplex_domL : (boundedComplex A0 A1 h).domL = ⊤ := by
  have h0 : (boundedComplex A0 A1 h).d0†.domain = ⊤ := by rw [boundedComplex_adj0]; rfl
  have h1 : (boundedComplex A0 A1 h).d1†.domain = ⊤ := by rw [boundedComplex_adj1]; rfl
  ext x
  simp only [mem_domL, midDomain, h0, h1, Submodule.mem_top, Submodule.mem_inf, and_true,
    iff_true]
  exact ⟨trivial, trivial⟩

/-- `-L` of the bounded complex as a bounded operator:
`-L(σ, u, ρ) = (A0* u, -A0 σ - A1* ρ, A1 u)`. -/
def boundedWave : Tot W0 W1 W2 →L[ℝ] Tot W0 W1 W2 :=
  (totL (W0 := W0) (W1 := W1) (W2 := W2)).symm.toContinuousLinearMap ∘L
    ((A0.adjoint ∘L ContinuousLinearMap.fst ℝ W1 W2 ∘L ContinuousLinearMap.snd ℝ W0 (W1 × W2)).prod
      ((-(A0 ∘L ContinuousLinearMap.fst ℝ W0 (W1 × W2)) - A1.adjoint ∘L
          ContinuousLinearMap.snd ℝ W1 W2 ∘L ContinuousLinearMap.snd ℝ W0 (W1 × W2)).prod
        (A1 ∘L ContinuousLinearMap.fst ℝ W1 W2 ∘L ContinuousLinearMap.snd ℝ W0 (W1 × W2)))) ∘L
    (totL (W0 := W0) (W1 := W1) (W2 := W2)).toContinuousLinearMap

/-- `-L = boundedWave` as partial maps (Hodge wave operator (4.5) of a bounded complex). -/
theorem neg_waveOp_boundedComplex :
    -(boundedComplex A0 A1 h).waveOp = Feec.bddOp (boundedWave A0 A1) := by
  refine LinearPMap.ext (by rw [LinearPMap.neg_domain]; exact boundedComplex_domL A0 A1 h)
    fun x hx _ => ?_
  rw [LinearPMap.neg_apply, Feec.bddOp_apply]
  apply (tot W0 W1 W2).injective
  rw [_root_.map_neg, tot_waveOp]
  simp only [boundedComplex_adj0_apply, boundedComplex_adj1_apply]
  simp only [boundedComplex_d0_apply, boundedComplex_d1_apply, coe_pr0, coe_prV1, coe_prV1s,
    coe_prV2s]
  simp [boundedWave]
  abel

include h in
/-- `-L` of a bounded complex is skew-symmetric as a bounded operator. -/
theorem boundedWave_skew (x y : Tot W0 W1 W2) :
    ⟪boundedWave A0 A1 x, y⟫ = -⟪x, boundedWave A0 A1 y⟫ := by
  have hs := isSkewSymm_neg (waveOp_isSkewSymm (boundedComplex A0 A1 h))
  rw [neg_waveOp_boundedComplex A0 A1 h] at hs
  exact hs ⟨x, trivial⟩ ⟨y, trivial⟩

/-- **Stone group for (4.14) on a bounded complex**: `-L` generates `t ↦ exp(t(-L))`.

Cf. [Pazy1983, §1.1] (uniformly continuous groups `exp(tA)` of bounded operators). -/
def boundedGroup : UnitaryGroupGenerator (-(boundedComplex A0 A1 h).waveOp) :=
  (neg_waveOp_boundedComplex A0 A1 h).symm ▸ expGroup _ (boundedWave_skew A0 A1 h)

/-- **Non-vacuity of `WellPosedHom (-L)`** (critic item 6) for every bounded complex.

Cf. [QuennevilleBelair2015, Thm 4.6]. -/
theorem wellPosedHom_boundedComplex (T : ℝ) :
    WellPosedHom (-(boundedComplex A0 A1 h).waveOp) T :=
  (boundedGroup A0 A1 h).wellPosedHom T

/-- A concrete nontrivial instance: `ℝ --id--> ℝ --0--> ℝ`, whose Hodge wave operator is
nonzero (`L(1, 0, 0) = (0, 1, 0)`), satisfies `WellPosedHom (-L)` and has a Stone group. -/
theorem exists_nontrivial_wellPosed (T : ℝ) :
    ∃ H : HilbertComplex2 ℝ ℝ ℝ, (∃ x : H.waveOp.domain, H.waveOp x ≠ 0) ∧
      WellPosedHom (-H.waveOp) T ∧ Nonempty (UnitaryGroupGenerator (-H.waveOp)) := by
  let H := boundedComplex (ContinuousLinearMap.id ℝ ℝ) (0 : ℝ →L[ℝ] ℝ) (fun _ => rfl)
  refine ⟨H, ⟨⟨(tot ℝ ℝ ℝ).symm (1, 0, 0), ?_⟩, fun h0 => ?_⟩,
    wellPosedHom_boundedComplex _ _ _ T, ⟨boundedGroup _ _ _⟩⟩
  · change _ ∈ H.domL
    rw [boundedComplex_domL]; trivial
  · have := congrArg (fun z => (tot ℝ ℝ ℝ z).2.1) h0
    simp only [tot_waveOp, _root_.map_zero] at this
    simp only [H, boundedComplex_d0_apply, boundedComplex_adj1_apply, coe_pr0, coe_prV2s,
      LinearEquiv.apply_symm_apply] at this
    simp at this

end Bounded

end Feec.Constraints
