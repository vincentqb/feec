module

public import Feec.HilbertComplex.Approximation.DissipFEEC
public import Feec.Semigroup.Impedance
public import Feec.ForMathlib.LinearPMap.Bounded

/-!
# Trotter–Kato from resolvent consistency, and conforming Galerkin schemes for impedance problems

## The Trotter–Kato core

For a dissipative FEEC discretization `F` (`Feec.HilbertComplex.DissipFEEC`) of an m-dissipative
`A`, the discrete resolvents `(1 - Lₕ)⁻¹` exist and are contractions (`discreteRes`,
`norm_discreteRes_apply_le`: `1 - Lₕ` is bounded below and its range has trivial orthogonal
complement). **`DissipFEEC.Core.ofResolvent`**: if the discrete resolvents are consistent,
`ιₕ (1 - Lₕ)⁻¹ πₕ z → (1 - A)⁻¹ z`, and `ιₕ πₕ z → z`, for every `z`, then `(1 - A)⁻¹ D(A)` is a
core, dense in `E` (`DissipFEEC.resData_closure`): the comparison trajectories are
`pₕ(t) = (1 - Lₕ)⁻¹ πₕ (1 - A) S(t) x`, whose consistency defect is
`πₕ y - (1 - Lₕ)⁻¹ πₕ (1 - A) y` at `y = (1 - A) S(t) x`. This is the Trotter–Kato theorem
(resolvent form) for contraction semigroups, in the orbit form used by `dissipFEEC`.

## Conforming Galerkin schemes for impedance triples

For an impedance triple `T` (`Feec.ImpedanceTriple`: energy space `V`, field `ι`, differential `c`,
boundary trace `γ`), finite-dimensional `Vₕ ⊆ V` and closed `Wₕ ⊆ H₂` with `c Vₕ ⊆ Wₕ`
(`Feec.ImpedanceTriple.GalerkinData`) give the **Galerkin scheme** (`galerkin`, generator `Lh`)
on `Xₕ = ι Vₕ ⊕₂ Wₕ`:

  `⟪Ėₕ, ι v'⟫ = -⟪Pₕ, c v'⟫ - ⟪γ vₕ, γ v'⟫` for `v' ∈ Vₕ`, `Ṗₕ = c vₕ`, `Eₕ = ι vₕ`,

whose bilinear form carries the boundary term `⟪γ vₕ, γ v'⟫`: the discrete generator is
dissipative, `⟪Lₕ x, x⟫ = -‖γ vₕ‖²` (`inner_Lh`), so the discrete energy decreases by twice the
integrated discrete outgoing flux (`norm_sq_galerkin_sol`). Its discrete resolvent is the Galerkin solution
built on the `V`-orthogonal projection of the exact one (Céa's lemma with constant `1`,
`discreteRes_galerkin`, `norm_incl_galerkinRes_sub_le`), so under the approximation property
(`Approximates`: `Vₕ` approximates `V`, `Wₕ` approximates `H₂`) the scheme is consistent and
**`galerkin_verdict`** gives the full `dissipFEEC` verdict with a dense core: convergence for
every datum, the rate bound for every rate class, the constraint residual in both directions. For separable `V`, `H₂`,
dense-sequence spaces (`ofDenseSeq`) are an approximating family (`approximates_ofDenseSeq`).

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.4 (Thm 4.2, Trotter–Kato, single-space form; here with variable spaces `Xₕ`)
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003], §4.6 (the impedance
  problem)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

/-! ### Discrete resolvents -/

section Res

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [CompleteSpace X]

/-- A bounded operator as an operator with full domain. -/
abbrev boundedPMap (L : X →L[𝕜] X) : X →ₗ.[𝕜] X := (L : X →ₗ[𝕜] X).toPMap ⊤

/-- **A bounded dissipative operator is m-dissipative**: `1 - L` is bounded below, and a vector
orthogonal to its range is `0` (test against itself). -/
theorem isMDissipative_boundedPMap {L : X →L[𝕜] X} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) :
    (boundedPMap L).IsMDissipative := by
  refine LinearPMap.IsDissipative.isMDissipative_of_orthogonal (fun x => hL x)
    (ContinuousLinearMap.isClosed_toPMap_top L) fun y hy => ?_
  have h := hy ⟨y, trivial⟩
  change ⟪y - L y, y⟫_𝕜 = 0 at h
  rw [inner_sub_left, sub_eq_zero] at h
  have h1 : ‖y‖ ^ 2 ≤ 0 := by
    have := hL y
    rw [← h, inner_self_eq_norm_sq] at this
    exact this
  exact norm_eq_zero.1 (by nlinarith [norm_nonneg y])

/-- **The discrete resolvent** `(1 - L)⁻¹` of a bounded dissipative operator. -/
def boundedRes (L : X →L[𝕜] X) : X →L[𝕜] X := Operator.resolvent (boundedPMap L) 1

theorem boundedRes_sub {L : X →L[𝕜] X} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) (y : X) :
    boundedRes L y - L (boundedRes L y) = y := by
  have h := ((isMDissipative_boundedPMap hL).isResolvent_one).sub_apply y
  simpa [boundedRes] using h

theorem boundedRes_apply_sub {L : X →L[𝕜] X} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) (x : X) :
    boundedRes L (x - L x) = x := by
  have h := ((isMDissipative_boundedPMap hL).isResolvent_one).apply_sub ⟨x, trivial⟩
  simpa [boundedRes] using h

theorem norm_boundedRes_apply_le {L : X →L[𝕜] X} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) (y : X) :
    ‖boundedRes L y‖ ≤ ‖y‖ := by
  have := (isMDissipative_boundedPMap hL).norm_resolvent_apply_le one_pos y
  simpa [boundedRes] using this

end Res

/-! ### The Trotter–Kato core -/

section TrotterKato

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  {A : E →ₗ.[𝕜] E} {hA : A.IsMDissipative} {κ : Type*}

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- `R(1) (y - A y) = y` and `R(1) y - A R(1) y = y`, with `R(1) = (1 - A)⁻¹`. -/
theorem resolvent_one_apply_sub (hA : A.IsMDissipative) (x : A.domain) :
    Operator.resolvent A 1 ((x : E) - A x) = x := by
  simpa using hA.isResolvent_one.apply_sub x

/-- **The resolvent commutes with the semigroup**: `R(1) S(t) = S(t) R(1)` for `t ≥ 0`. -/
theorem resolvent_semigroup_comm (hA : A.IsMDissipative) {t : ℝ} (ht : 0 ≤ t) (y : E) :
    Operator.resolvent A 1 (hA.semigroup.S t y) = hA.semigroup.S t (Operator.resolvent A 1 y) := by
  have hR := hA.isResolvent_one
  set x : A.domain := hR.toDomain y
  have hx : (x : E) - A x = y := by
    have h := hR.sub_apply_toDomain y
    rw [one_smul] at h
    exact h
  have hSx := hA.semigroup_mem_domain x ht
  have h1 : hA.semigroup.S t (x : E) - A ⟨_, hSx⟩ = hA.semigroup.S t y := by
    rw [hA.apply_semigroup x ht, ← _root_.map_sub, hx]
  rw [← h1, resolvent_one_apply_sub hA ⟨_, hSx⟩]
  rfl

namespace DissipFEEC

variable (F : DissipFEEC.{u} hA κ)

/-- The discrete resolvent `(1 - Lₕ)⁻¹`. -/
def discreteRes (h : κ) : F.X h →L[𝕜] F.X h := boundedRes (F.L h)

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem norm_discreteRes_apply_le (h : κ) (y : F.X h) : ‖F.discreteRes h y‖ ≤ ‖y‖ :=
  norm_boundedRes_apply_le (F.dissipative h) y

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem discreteRes_sub (h : κ) (y : F.X h) :
    F.discreteRes h y - F.L h (F.discreteRes h y) = y :=
  boundedRes_sub (F.dissipative h) y

/-- The data of the resolvent core: `R(1) D(A) = D(A²)`. -/
def resData : Submodule 𝕜 E := A.domain.map (Operator.resolvent A 1).toLinearMap

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem mem_domain_of_mem_resData (hA : A.IsMDissipative) {x : E} (hx : x ∈ resData (A := A)) :
    x ∈ A.domain := by
  obtain ⟨u, -, rfl⟩ := hx
  exact hA.isResolvent_one.mem_domain u

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- For `x = R(1) u`, `u = x - A x ∈ D(A)`. -/
theorem sub_genExt_mem_domain (hA : A.IsMDissipative) {x : E} (hx : x ∈ resData (A := A)) :
    x - genExt A x ∈ A.domain := by
  obtain ⟨u, hu, rfl⟩ := hx
  have hR := hA.isResolvent_one
  have e : Operator.resolvent A 1 u - genExt A (Operator.resolvent A 1 u) = u := by
    rw [genExt_of_mem (hR.mem_domain u)]
    have h := hR.sub_apply u
    rw [one_smul] at h
    exact h
  have e' : ((Operator.resolvent A 1 : E →L[𝕜] E) : E →ₗ[𝕜] E) u -
      genExt A (((Operator.resolvent A 1 : E →L[𝕜] E) : E →ₗ[𝕜] E) u) = u := e
  rw [e']; exact hu

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem resolvent_sub_genExt (hA : A.IsMDissipative) {x : E} (hx : x ∈ resData (A := A)) :
    Operator.resolvent A 1 (x - genExt A x) = x := by
  have hd := mem_domain_of_mem_resData (hA := hA) hx
  rw [genExt_of_mem hd]
  exact resolvent_one_apply_sub hA ⟨x, hd⟩

/-- The comparison trajectories `pₕ(t) = (1 - Lₕ)⁻¹ πₕ (1 - A) S(t) x` of the resolvent core. -/
def Comparison.ofResolvent (T : ℝ) : F.Comparison T where
  Data := resData (A := A)
  p x h t := F.discreteRes h (F.proj h (hA.semigroup.S t (x - genExt A x)))
  p' x h t := F.discreteRes h (F.proj h (hA.semigroup.S t (genExt A (x - genExt A x))))
  continuousOn _ _ h := ((F.discreteRes h).continuous.comp (F.proj h).continuous).comp_continuousOn
    ((hA.semigroup.strongCont _).mono Icc_subset_Ici_self)
  continuousOn' _ _ h := ((F.discreteRes h).continuous.comp (F.proj h).continuous).comp_continuousOn
    ((hA.semigroup.strongCont _).mono Icc_subset_Ici_self)
  hasDerivWithinAt x hx h t ht := by
    have hu := sub_genExt_mem_domain (hA := hA) hx
    have hd := hA.hasDerivWithinAt_semigroup ⟨_, hu⟩ ht.1
    rw [← genExt_of_mem hu] at hd
    exact (((F.discreteRes h).comp (F.proj h)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt
      t hd

/-- **The Trotter–Kato core** (resolvent form): consistent discrete resolvents,
`ιₕ (1 - Lₕ)⁻¹ πₕ z → (1 - A)⁻¹ z`, and `ιₕ πₕ z → z` give the core `R(1) D(A) = D(A²)`.
[Pazy1983], §3.4 (Thm 4.2) -/
def Core.ofResolvent
    (hres : ∀ z, Tendsto (fun h => F.incl h (F.discreteRes h (F.proj h z))) F.l
      (𝓝 (Operator.resolvent A 1 z)))
    (happ : ∀ z, Tendsto (fun h => F.incl h (F.proj h z)) F.l (𝓝 z)) : F.Core where
  Data := resData (A := A)
  cmp T := Comparison.ofResolvent F T
  data_eq _ := rfl
  tendsto_approx T x hx := by
    set u := x - genExt A x
    set R := Operator.resolvent A (1 : 𝕜)
    set C := F.boundConst
    have hC := F.boundConst_nonneg
    set B : ∀ _ : κ, E →L[𝕜] E := fun h => F.incl h ∘L F.discreteRes h ∘L F.proj h - R
    have hB : ∀ h y, ‖B h y‖ ≤ (C * C + 1) * ‖y‖ := fun h y => by
      have h1 : ‖F.incl h (F.discreteRes h (F.proj h y))‖ ≤ C * C * ‖y‖ := by
        calc _ ≤ C * ‖F.discreteRes h (F.proj h y)‖ := F.norm_incl_apply_le h _
          _ ≤ C * ‖F.proj h y‖ := mul_le_mul_of_nonneg_left (F.norm_discreteRes_apply_le h _) hC
          _ ≤ C * (C * ‖y‖) := mul_le_mul_of_nonneg_left (((F.proj h).le_opNorm y).trans
              (mul_le_mul_of_nonneg_right (F.norm_proj_le h) (norm_nonneg _))) hC
          _ = _ := by ring
      have h2 : ‖R y‖ ≤ ‖y‖ := by
        have := hA.norm_resolvent_apply_le one_pos y; simpa using this
      calc ‖B h y‖ ≤ ‖F.incl h (F.discreteRes h (F.proj h y))‖ + ‖R y‖ := norm_sub_le _ _
        _ ≤ _ := by nlinarith
    have hlim : ∀ y, Tendsto (fun h => ‖B h y‖) F.l (𝓝 0) := fun y => by
      have := tendsto_iff_norm_sub_tendsto_zero.1 (hres y)
      exact this.congr fun h => rfl
    have hcpt : IsCompact ((fun t => hA.semigroup.S t u) '' Icc 0 T) :=
      isCompact_Icc.image_of_continuousOn ((hA.semigroup.strongCont u).mono Icc_subset_Ici_self)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [eventually_forall_norm_lt_of_tendsto hB hlim hcpt hε] with h hh t ht
    have := hh _ (mem_image_of_mem _ ht)
    have e : hA.semigroup.S t x = R (hA.semigroup.S t u) := by
      rw [resolvent_semigroup_comm hA ht.1, resolvent_sub_genExt (hA := hA) hx]
    rw [dist_eq_norm, F.S_def, e, norm_sub_rev]
    change ‖F.incl h (F.discreteRes h (F.proj h (hA.semigroup.S t u))) -
      R (hA.semigroup.S t u)‖ < ε
    simpa only [B, sub_apply, ContinuousLinearMap.comp_apply] using this
  tendsto_defect T x hx := by
    have hu := sub_genExt_mem_domain (hA := hA) hx
    set u := x - genExt A x
    set R := Operator.resolvent A (1 : 𝕜)
    set C := F.boundConst
    have hC := F.boundConst_nonneg
    have hR1 : ∀ y, ‖R y‖ ≤ ‖y‖ := fun y => by
      have := hA.norm_resolvent_apply_le one_pos y; simpa using this
    set w : ℝ → E := fun t => hA.semigroup.S t (u - genExt A u)
    -- the defect is `πₕ R w - Gₕ w`
    have hdef : ∀ h, ∀ t ∈ Icc 0 T, (Comparison.ofResolvent F T).defect x h t =
        F.proj h (R (w t)) - F.discreteRes h (F.proj h (w t)) := fun h t ht => by
      have hRw : R (w t) = hA.semigroup.S t u := by
        simp only [w]
        rw [resolvent_semigroup_comm hA ht.1, genExt_of_mem hu, resolvent_one_apply_sub hA ⟨u, hu⟩]
      have hs := F.discreteRes_sub h (F.proj h (hA.semigroup.S t u))
      have hL : F.L h (F.discreteRes h (F.proj h (hA.semigroup.S t u))) =
          F.discreteRes h (F.proj h (hA.semigroup.S t u)) - F.proj h (hA.semigroup.S t u) := by
        generalize F.discreteRes h (F.proj h (hA.semigroup.S t u)) = g at hs ⊢
        rw [← hs, sub_sub_cancel]
      have hw : w t = hA.semigroup.S t u - hA.semigroup.S t (genExt A u) := _root_.map_sub _ _ _
      change F.discreteRes h (F.proj h (hA.semigroup.S t (genExt A u))) -
        F.L h (F.discreteRes h (F.proj h (hA.semigroup.S t u))) = _
      rw [hRw, hw, _root_.map_sub (F.proj h), _root_.map_sub (F.discreteRes h), hL]
      abel
    set D1 : ∀ _ : κ, E →L[𝕜] E := fun h => F.incl h ∘L F.proj h ∘L R - R
    set D2 : ∀ _ : κ, E →L[𝕜] E := fun h => R - F.incl h ∘L F.discreteRes h ∘L F.proj h
    have hD1 : ∀ h y, ‖D1 h y‖ ≤ (C * C + 1) * ‖y‖ := fun h y => by
      have h1 : ‖F.incl h (F.proj h (R y))‖ ≤ C * C * ‖y‖ := by
        calc _ ≤ C ^ 2 * ‖R y‖ := F.norm_incl_proj_le h _
          _ ≤ C ^ 2 * ‖y‖ := mul_le_mul_of_nonneg_left (hR1 y) (sq_nonneg _)
          _ = _ := by ring
      calc ‖D1 h y‖ ≤ ‖F.incl h (F.proj h (R y))‖ + ‖R y‖ := norm_sub_le _ _
        _ ≤ _ := by nlinarith [hR1 y]
    have hD2 : ∀ h y, ‖D2 h y‖ ≤ (C * C + 1) * ‖y‖ := fun h y => by
      have h1 : ‖F.incl h (F.discreteRes h (F.proj h y))‖ ≤ C * C * ‖y‖ := by
        calc _ ≤ C * ‖F.discreteRes h (F.proj h y)‖ := F.norm_incl_apply_le h _
          _ ≤ C * ‖F.proj h y‖ := mul_le_mul_of_nonneg_left (F.norm_discreteRes_apply_le h _) hC
          _ ≤ C * (C * ‖y‖) := mul_le_mul_of_nonneg_left (((F.proj h).le_opNorm y).trans
              (mul_le_mul_of_nonneg_right (F.norm_proj_le h) (norm_nonneg _))) hC
          _ = _ := by ring
      calc ‖D2 h y‖ ≤ ‖R y‖ + ‖F.incl h (F.discreteRes h (F.proj h y))‖ := norm_sub_le _ _
        _ ≤ _ := by nlinarith [hR1 y]
    have hl1 : ∀ y, Tendsto (fun h => ‖D1 h y‖) F.l (𝓝 0) := fun y =>
      (tendsto_iff_norm_sub_tendsto_zero.1 (happ (R y))).congr fun h => rfl
    have hl2 : ∀ y, Tendsto (fun h => ‖D2 h y‖) F.l (𝓝 0) := fun y => by
      have := tendsto_iff_norm_sub_tendsto_zero.1 (hres y)
      refine this.congr fun h => ?_
      rw [norm_sub_rev]; rfl
    have hcpt : IsCompact (w '' Icc 0 T) :=
      isCompact_Icc.image_of_continuousOn ((hA.semigroup.strongCont _).mono Icc_subset_Ici_self)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set δ := ε / (2 * (C + 1))
    have hδ : 0 < δ := by positivity
    filter_upwards [eventually_forall_norm_lt_of_tendsto hD1 hl1 hcpt hδ,
      eventually_forall_norm_lt_of_tendsto hD2 hl2 hcpt hδ] with h h1 h2 t ht
    rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg (norm_nonneg _), hdef h t ht]
    have e : F.incl h (F.proj h (R (w t)) - F.discreteRes h (F.proj h (w t))) =
        D1 h (w t) + D2 h (w t) := by
      simp only [D1, D2, _root_.map_sub, sub_apply,
        ContinuousLinearMap.comp_apply]
      abel
    have hb := F.norm_le_norm_incl h (F.proj h (R (w t)) - F.discreteRes h (F.proj h (w t)))
    rw [e] at hb
    have a1 := h1 _ (mem_image_of_mem _ ht)
    have a2 := h2 _ (mem_image_of_mem _ ht)
    calc _ ≤ C * ‖D1 h (w t) + D2 h (w t)‖ := hb
      _ ≤ C * (‖D1 h (w t)‖ + ‖D2 h (w t)‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hC
      _ ≤ C * (2 * δ) := mul_le_mul_of_nonneg_left (by linarith) hC
      _ < ε := by
        have : C * (2 * δ) = ε * (C / (C + 1)) := by simp only [δ]; field_simp
        rw [this]
        have : C / (C + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
        nlinarith

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **The resolvent core is dense**: `R(1) D(A)` is dense, `R(1)` being continuous with range
`D(A)` and `D(A)` dense. -/
theorem resData_closure (hA : A.IsMDissipative) : (resData (A := A)).topologicalClosure = ⊤ := by
  rw [← Submodule.dense_iff_topologicalClosure_eq_top]
  have hR := hA.isResolvent_one
  have hD := hA.dense_domain
  have hsub : (A.domain : Set E) ⊆ closure (resData (A := A) : Set E) := by
    intro x hx
    have e : x = Operator.resolvent A 1 (x - A ⟨x, hx⟩) :=
      (resolvent_one_apply_sub hA ⟨x, hx⟩).symm
    rw [e]
    refine map_mem_closure (Operator.resolvent A 1).continuous (hD _) fun z hz => ⟨z, hz, rfl⟩
  intro y
  exact closure_minimal hsub isClosed_closure (hD y)

end DissipFEEC

end TrotterKato

end Feec.HilbertComplex

/-! ### Conforming Galerkin schemes for impedance triples -/

namespace Feec.ImpedanceTriple

open Feec.HilbertComplex

variable {V H₁ H₂ Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  (T : ImpedanceTriple ℝ V H₁ H₂ Y)

/-- **Galerkin data** for an impedance triple: finite-dimensional `Vₕ ⊆ V` and closed `Wₕ ⊆ H₂`
with `c Vₕ ⊆ Wₕ`, along a filter. -/
structure GalerkinData (κ : Type*) where
  /-- the filter along which the spaces are refined -/
  l : Filter κ
  /-- the discrete energy spaces -/
  Vh : κ → Submodule ℝ V
  [finiteDimensional : ∀ h, FiniteDimensional ℝ (Vh h)]
  /-- the discrete spaces of the second field -/
  Wh : κ → Submodule ℝ H₂
  isClosed_Wh : ∀ h, IsClosed (Wh h : Set H₂)
  c_mem : ∀ h, ∀ v ∈ Vh h, T.c v ∈ Wh h

attribute [instance] GalerkinData.finiteDimensional

variable {T} {κ : Type*} (G : GalerkinData T κ)

namespace GalerkinData

/-- The discrete field space `Eₕ = ι Vₕ`. -/
def Eh (h : κ) : Submodule ℝ H₁ := (G.Vh h).map T.ι.toLinearMap

instance (h : κ) : FiniteDimensional ℝ (G.Eh h) := by unfold Eh; infer_instance

instance (h : κ) : CompleteSpace (G.Wh h) := (G.isClosed_Wh h).completeSpace_coe

/-- `ι : Vₕ ≃ Eₕ`. -/
def ιh (h : κ) : G.Vh h ≃L[ℝ] G.Eh h :=
  (Submodule.equivMapOfInjective T.ι.toLinearMap T.injective (G.Vh h)).toContinuousLinearEquiv

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
@[simp] theorem coe_ιh (h : κ) (v : G.Vh h) : ((G.ιh h v : G.Eh h) : H₁) = T.ι v := rfl

/-- The discrete differential `Cₕ : Eₕ → Wₕ`, `ι v ↦ c v`. -/
def Ch (h : κ) : G.Eh h →L[ℝ] G.Wh h :=
  (T.c ∘L (G.Vh h).subtypeL ∘L (G.ιh h).symm.toContinuousLinearMap).codRestrict (G.Wh h)
    fun e => G.c_mem h _ ((G.ιh h).symm e).2

/-- The discrete trace `Γₕ : Eₕ → Y`, `ι v ↦ γ v`. -/
def Γh (h : κ) : G.Eh h →L[ℝ] Y :=
  T.γ ∘L (G.Vh h).subtypeL ∘L (G.ιh h).symm.toContinuousLinearMap

/-- The discrete state space `Xₕ = Eₕ ⊕₂ Wₕ`. -/
abbrev Xh (h : κ) := WithLp 2 (G.Eh h × G.Wh h)

/-- **The Galerkin generator** `Lₕ (e, P) = (-Cₕ* P - Γₕ* Γₕ e, Cₕ e)`. -/
def Lh (h : κ) : G.Xh h →L[ℝ] G.Xh h :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (G.Eh h) (G.Wh h)).symm.toContinuousLinearMap ∘L
    ((-((ContinuousLinearMap.adjoint (G.Ch h)) ∘L WithLp.sndL 2 ℝ (G.Eh h) (G.Wh h)) -
      (ContinuousLinearMap.adjoint (G.Γh h) ∘L G.Γh h) ∘L WithLp.fstL 2 ℝ (G.Eh h) (G.Wh h)).prod
      (G.Ch h ∘L WithLp.fstL 2 ℝ (G.Eh h) (G.Wh h)))

omit [CompleteSpace V] [CompleteSpace H₁] in
/-- **The discrete energy flux**: `⟪Lₕ x, x⟫ = -‖Γₕ e‖²`, the boundary term of the bilinear form. -/
theorem inner_Lh (h : κ) (x : G.Xh h) : ⟪G.Lh h x, x⟫_ℝ = -‖G.Γh h x.fst‖ ^ 2 := by
  rw [WithLp.prod_inner_apply]
  simp only [Lh, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    WithLp.prodContinuousLinearEquiv_symm_apply, ContinuousLinearMap.prod_apply,
    sub_apply, neg_apply, WithLp.sndL_apply,
    WithLp.fstL_apply]
  simp only [inner_sub_left, inner_neg_left, ContinuousLinearMap.adjoint_inner_left]
  change -⟪x.snd, G.Ch h x.fst⟫_ℝ - ⟪G.Γh h x.fst, G.Γh h x.fst⟫_ℝ +
    ⟪G.Ch h x.fst, x.snd⟫_ℝ = _
  rw [real_inner_self_eq_norm_sq, real_inner_comm x.snd]
  ring

omit [CompleteSpace V] [CompleteSpace H₁] in
theorem Lh_dissipative (h : κ) (x : G.Xh h) : RCLike.re ⟪G.Lh h x, x⟫_ℝ ≤ 0 := by
  rw [RCLike.re_to_real, G.inner_Lh]; exact neg_nonpos.2 (sq_nonneg _)

omit [CompleteSpace V] [CompleteSpace H₁] in
theorem Lh_fst (h : κ) (x : G.Xh h) :
    (G.Lh h x).fst = -(ContinuousLinearMap.adjoint (G.Ch h) x.snd) -
      ContinuousLinearMap.adjoint (G.Γh h) (G.Γh h x.fst) := rfl

omit [CompleteSpace V] [CompleteSpace H₁] in
theorem Lh_snd (h : κ) (x : G.Xh h) : (G.Lh h x).snd = G.Ch h x.fst := rfl

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
@[simp] theorem coe_Ch_ιh (h : κ) (v : G.Vh h) : ((G.Ch h (G.ιh h v) : G.Wh h) : H₂) = T.c v := by
  change T.c ((G.ιh h).symm (G.ιh h v) : V) = T.c v
  rw [ContinuousLinearEquiv.symm_apply_apply]

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
@[simp] theorem Γh_ιh (h : κ) (v : G.Vh h) : G.Γh h (G.ιh h v) = T.γ v := by
  simp [Γh]

/-! #### Reading and projection maps -/

/-- **The reading map** `ιₕ : Eₕ ⊕₂ Wₕ → H₁ ⊕₂ H₂`, the inclusion. -/
def incl (h : κ) : G.Xh h →L[ℝ] WithLp 2 (H₁ × H₂) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ H₁ H₂).symm.toContinuousLinearMap ∘L
    (((G.Eh h).subtypeL ∘L WithLp.fstL 2 ℝ (G.Eh h) (G.Wh h)).prod
      ((G.Wh h).subtypeL ∘L WithLp.sndL 2 ℝ (G.Eh h) (G.Wh h)))

/-- **The projection** `πₕ = (P_{Eₕ}, P_{Wₕ})`, componentwise orthogonal projections. -/
def proj (h : κ) : WithLp 2 (H₁ × H₂) →L[ℝ] G.Xh h :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (G.Eh h) (G.Wh h)).symm.toContinuousLinearMap ∘L
    (((G.Eh h).orthogonalProjectionOnto ∘L WithLp.fstL 2 ℝ H₁ H₂).prod
      ((G.Wh h).orthogonalProjectionOnto ∘L WithLp.sndL 2 ℝ H₁ H₂))

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
@[simp] theorem incl_fst (h : κ) (x : G.Xh h) : (G.incl h x).fst = x.fst := rfl
omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
@[simp] theorem incl_snd (h : κ) (x : G.Xh h) : (G.incl h x).snd = x.snd := rfl
omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace Y] in
@[simp] theorem proj_fst (h : κ) (z : WithLp 2 (H₁ × H₂)) :
    (G.proj h z).fst = (G.Eh h).orthogonalProjectionOnto z.fst := rfl
omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace Y] in
@[simp] theorem proj_snd (h : κ) (z : WithLp 2 (H₁ × H₂)) :
    (G.proj h z).snd = (G.Wh h).orthogonalProjectionOnto z.snd := rfl

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace Y] in
theorem proj_incl (h : κ) (x : G.Xh h) : G.proj h (G.incl h x) = x :=
  withLp_prod_ext (by simp) (by simp)

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
theorem norm_incl_apply (h : κ) (x : G.Xh h) : ‖G.incl h x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2]
  simp

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace Y] in
theorem norm_proj_apply_le (h : κ) (z : WithLp 2 (H₁ × H₂)) : ‖G.proj h z‖ ≤ ‖z‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2, proj_fst, proj_snd]
  have h1 := (G.Eh h).norm_orthogonalProjectionOnto_apply_le z.fst
  have h2 := (G.Wh h).norm_orthogonalProjectionOnto_apply_le z.snd
  gcongr

variable (K : Submodule ℝ (WithLp 2 (H₁ × H₂))) (hK : IsClosed (K : Set (WithLp 2 (H₁ × H₂))))

/-- **The conforming Galerkin scheme as a dissipative FEEC discretization** of the impedance
operator, for a closed constraint subspace `K`. -/
def galerkin : DissipFEEC T.isMDissipative_op κ where
  K := K
  isClosed_K := hK
  l := G.l
  X := G.Xh
  L := G.Lh
  dissipative := G.Lh_dissipative
  incl := G.incl
  proj := G.proj
  proj_incl := G.proj_incl
  bound := ⟨1, fun h => ⟨ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [G.norm_incl_apply, one_mul], ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [one_mul]; exact G.norm_proj_apply_le h z⟩⟩

/-! #### The discrete resolvent is the Galerkin projection of the exact one -/

variable (T) in
/-- The energy-space element of `(1 - A)⁻¹ z`. -/
def resWitness (z : WithLp 2 (H₁ × H₂)) : V :=
  T.witness (T.isMDissipative_op.isResolvent_one.toDomain z)

/-- **The Galerkin solution** of `(1 - Lₕ) xₕ = πₕ z`: `eₕ = ι vₕ` with `vₕ` the `V`-orthogonal
projection of the exact energy-space solution `v`, and `Pₕ = P_{Wₕ} g + c vₕ`. -/
def galerkinRes (h : κ) (z : WithLp 2 (H₁ × H₂)) : G.Xh h :=
  WithLp.toLp 2 (G.ιh h ((G.Vh h).orthogonalProjectionOnto (resWitness T z)),
    (G.Wh h).orthogonalProjectionOnto z.snd +
      G.Ch h (G.ιh h ((G.Vh h).orthogonalProjectionOnto (resWitness T z))))

omit [CompleteSpace Y] in
/-- The exact resolvent in terms of its witness: `R z = (ι v, g + c v)` and the weak equation. -/
theorem res_eq (z : WithLp 2 (H₁ × H₂)) :
    (Operator.resolvent T.op 1 z).fst = T.ι (resWitness T z) ∧
    (Operator.resolvent T.op 1 z).snd = z.snd + T.c (resWitness T z) ∧
    ∀ v' : V, ⟪z.fst, T.ι v'⟫_ℝ = ⟪resWitness T z, v'⟫_ℝ + ⟪z.snd, T.c v'⟫_ℝ := by
  have hR := T.isMDissipative_op.isResolvent_one
  set u := hR.toDomain z
  have hsub : (u : WithLp 2 (H₁ × H₂)) - T.op u = z := by
    have := hR.sub_apply_toDomain z; rwa [one_smul] at this
  have h1 : (u : WithLp 2 (H₁ × H₂)).fst - (T.op u).fst = z.fst := by rw [← hsub]; rfl
  have h2 : (u : WithLp 2 (H₁ × H₂)).snd - (T.op u).snd = z.snd := by rw [← hsub]; rfl
  have hι := T.ι_witness u
  have hc := T.c_witness u
  have hw := T.isWeak_witness u
  refine ⟨hι.symm, ?_, fun v' => ?_⟩
  · change (u : WithLp 2 (H₁ × H₂)).snd = _
    rw [resWitness, hc, ← h2]; abel
  · rw [← h1, inner_sub_left, hw v', ← hι, T.inner_eq, resWitness, ← h2, inner_sub_left, ← hc]
    ring

theorem galerkinRes_sub (h : κ) (z : WithLp 2 (H₁ × H₂)) :
    G.galerkinRes h z - G.Lh h (G.galerkinRes h z) = G.proj h z := by
  set vh := (G.Vh h).orthogonalProjectionOnto (resWitness T z)
  obtain ⟨-, -, hz⟩ := res_eq (T := T) z
  refine withLp_prod_ext ?_ ?_
  · rw [WithLp.sub_fst, Lh_fst, proj_fst]
    refine ext_inner_right ℝ fun e' => ?_
    obtain ⟨v', rfl⟩ := (G.ιh h).surjective e'
    have hP : ⟪(G.Wh h).orthogonalProjectionOnto z.snd, G.Ch h (G.ιh h v')⟫_ℝ =
        ⟪z.snd, T.c v'⟫_ℝ := by
      rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, coe_Ch_ιh]
    have hV : ⟪(vh : V), (v' : V)⟫_ℝ = ⟪resWitness T z, v'⟫_ℝ := by
      rw [← Submodule.coe_inner, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, coe_ιh, hz v', ← hV, ← hP,
      T.inner_eq, inner_sub_left, inner_sub_left, inner_neg_left,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    change ⟪G.ιh h vh, G.ιh h v'⟫_ℝ - (-⟪(G.Wh h).orthogonalProjectionOnto z.snd +
      G.Ch h (G.ιh h vh), G.Ch h (G.ιh h v')⟫_ℝ - ⟪G.Γh h (G.ιh h vh), G.Γh h (G.ιh h v')⟫_ℝ) = _
    rw [Γh_ιh, Γh_ιh, inner_add_left, Submodule.coe_inner (G.Eh h), coe_ιh, coe_ιh,
      Submodule.coe_inner (G.Wh h) (G.Ch h (G.ιh h vh)), coe_Ch_ιh, coe_Ch_ιh]
    ring
  · rw [WithLp.sub_snd, Lh_snd, proj_snd]
    change (G.Wh h).orthogonalProjectionOnto z.snd + G.Ch h (G.ιh h vh) - G.Ch h (G.ιh h vh) = _
    abel


/-- **The discrete resolvent is the Galerkin solution** (Céa: `vₕ = P_{Vₕ} v` in `V`). -/
theorem discreteRes_galerkin (h : κ) (z : WithLp 2 (H₁ × H₂)) :
    (G.galerkin K hK).discreteRes h (G.proj h z) = G.galerkinRes h z := by
  rw [← G.galerkinRes_sub h z]
  exact boundedRes_apply_sub (G.Lh_dissipative h) _

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
theorem norm_ι_le_and_norm_c_le (v : V) : ‖T.ι v‖ ≤ ‖v‖ ∧ ‖T.c v‖ ≤ ‖v‖ := by
  have e := T.inner_eq v v
  simp only [real_inner_self_eq_norm_sq] at e
  have h1 : 0 ≤ ‖T.γ v‖ ^ 2 := sq_nonneg _
  exact ⟨(sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith [sq_nonneg ‖T.c v‖]),
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith [sq_nonneg ‖T.ι v‖])⟩

omit [InnerProductSpace ℝ H₁] [InnerProductSpace ℝ H₂] [CompleteSpace H₁] [CompleteSpace H₂] in
theorem norm_withLp_le (x : WithLp 2 (H₁ × H₂)) : ‖x‖ ≤ ‖x.fst‖ + ‖x.snd‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), WithLp.prod_norm_sq_eq_of_L2]
  nlinarith [norm_nonneg x.fst, norm_nonneg x.snd]

omit [CompleteSpace Y] in
/-- **Galerkin error of the resolvent**: `‖ιₕ (1 - Lₕ)⁻¹ πₕ z - (1 - A)⁻¹ z‖ ≤
2 ‖P_{Vₕ} v - v‖_V + ‖P_{Wₕ} g - g‖`. -/
theorem norm_incl_galerkinRes_sub_le (h : κ) (z : WithLp 2 (H₁ × H₂)) :
    ‖G.incl h (G.galerkinRes h z) - Operator.resolvent T.op 1 z‖ ≤
      2 * ‖((G.Vh h).starProjection (resWitness T z)) - resWitness T z‖ +
        ‖(G.Wh h).starProjection z.snd - z.snd‖ := by
  obtain ⟨h1, h2, -⟩ := res_eq (T := T) z
  set v := resWitness T z
  set w := (G.Vh h).starProjection v - v
  refine (norm_withLp_le _).trans ?_
  have ef : (G.incl h (G.galerkinRes h z) - Operator.resolvent T.op 1 z).fst = T.ι w := by
    rw [WithLp.sub_fst, h1, incl_fst]
    change T.ι ((G.Vh h).orthogonalProjectionOnto v : V) - T.ι v = _
    rw [← _root_.map_sub]; rfl
  have es : (G.incl h (G.galerkinRes h z) - Operator.resolvent T.op 1 z).snd =
      ((G.Wh h).starProjection z.snd - z.snd) + T.c w := by
    rw [WithLp.sub_snd, h2, incl_snd]
    change ((G.Wh h).orthogonalProjectionOnto z.snd : H₂) +
      ((G.Ch h (G.ιh h ((G.Vh h).orthogonalProjectionOnto v)) : G.Wh h) : H₂) - _ = _
    rw [coe_Ch_ιh, _root_.map_sub]
    simp only [Submodule.starProjection_apply]
    abel
  rw [ef, es]
  have a := (norm_ι_le_and_norm_c_le (T := T) w)
  have b := norm_add_le ((G.Wh h).starProjection z.snd - z.snd) (T.c w)
  linarith [a.1, a.2]

/-- **Approximation property** of the Galerkin spaces: `Vₕ` approximates every `v ∈ V` in the
energy norm and `Wₕ` every `g ∈ H₂`. -/
def Approximates : Prop :=
  (∀ v : V, Tendsto (fun h => infDist v (G.Vh h : Set V)) G.l (𝓝 0)) ∧
    ∀ g : H₂, Tendsto (fun h => infDist g (G.Wh h : Set H₂)) G.l (𝓝 0)

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] in
theorem tendsto_starProjection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {U : κ → Submodule ℝ E} [∀ h, (U h).HasOrthogonalProjection] {l : Filter κ} {x : E}
    (hU : Tendsto (fun h => infDist x (U h : Set E)) l (𝓝 0)) :
    Tendsto (fun h => (U h).starProjection x) l (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine hU.congr fun h => ?_
  rw [dist_comm, Submodule.dist_starProjection_eq_infDist]

variable {G} in
omit [CompleteSpace Y] in
/-- **Consistency of the Galerkin resolvents** from the approximation property. -/
theorem tendsto_incl_galerkinRes (hG : G.Approximates) (z : WithLp 2 (H₁ × H₂)) :
    Tendsto (fun h => G.incl h (G.galerkinRes h z)) G.l
      (𝓝 (Operator.resolvent T.op 1 z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_starProjection (hG.1 (resWitness T z)))
  have h2 := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_starProjection (hG.2 z.snd))
  have h3 : Tendsto (fun h => 2 * ‖(G.Vh h).starProjection (resWitness T z) - resWitness T z‖ +
      ‖(G.Wh h).starProjection z.snd - z.snd‖) G.l (𝓝 0) := by
    simpa using (h1.const_mul 2).add h2
  exact squeeze_zero (fun _ => norm_nonneg _) (fun h => G.norm_incl_galerkinRes_sub_le h z) h3

variable {G} in
omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace Y] in
/-- **The projections converge**: `ιₕ πₕ z → z` (`ι V` is dense in `H₁` and approximated by
`ι Vₕ`). -/
theorem tendsto_incl_proj (hG : G.Approximates) (z : WithLp 2 (H₁ × H₂)) :
    Tendsto (fun h => G.incl h (G.proj h z)) G.l (𝓝 z) := by
  have hE : Tendsto (fun h => (G.Eh h).starProjection z.fst) G.l (𝓝 z.fst) := by
    refine tendsto_starProjection (Metric.tendsto_nhds.2 fun ε hε => ?_)
    obtain ⟨v, hv⟩ : ∃ v, dist z.fst (T.ι v) < ε / 2 :=
      (Metric.denseRange_iff.1 T.denseRange) z.fst _ (half_pos hε)
    have hc := Metric.tendsto_nhds.1 (tendsto_starProjection (hG.1 v)) _ (half_pos hε)
    filter_upwards [hc] with h hh
    rw [Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg]
    have hmem : T.ι ((G.Vh h).starProjection v) ∈ (G.Eh h : Set H₁) :=
      ⟨_, (G.Vh h).starProjection_apply_mem v, rfl⟩
    calc infDist z.fst (G.Eh h : Set H₁) ≤ dist z.fst (T.ι ((G.Vh h).starProjection v)) :=
          infDist_le_dist_of_mem hmem
      _ ≤ dist z.fst (T.ι v) + dist (T.ι v) (T.ι ((G.Vh h).starProjection v)) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add hv (lt_of_le_of_lt ?_ hh)
          rw [dist_eq_norm, dist_eq_norm, ← _root_.map_sub, norm_sub_rev]
          exact (norm_ι_le_and_norm_c_le (T := T) _).1
      _ = ε := add_halves ε
  have hW := tendsto_starProjection (hG.2 z.snd)
  rw [tendsto_iff_norm_sub_tendsto_zero] at hE hW ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun h => (norm_withLp_le _).trans le_rfl) ?_
  simpa using hE.add hW

variable {G} in
/-- **The Galerkin core** (Trotter–Kato, resolvent form): `R(1) D(A)`. -/
def galerkinCore (hG : G.Approximates) : (G.galerkin K hK).Core :=
  DissipFEEC.Core.ofResolvent (G.galerkin K hK)
    (fun z => (tendsto_incl_galerkinRes hG z).congr fun h =>
      (congrArg (G.incl h) (G.discreteRes_galerkin K hK h z)).symm)
    (fun z => tendsto_incl_proj hG z)


/-- **The Galerkin verdict**: under the approximation property, the core `R(1) D(A)` is dense
and the conforming Galerkin scheme has the full `dissipFEEC` verdict (well-posedness,
propagation criteria, convergence for every datum, the rate bound for every rate class (none is
constructed here), constraint residual in both directions). [Pazy1983], §3.4 (Thm 4.2, the
single-space form) -/
theorem galerkin_verdict (hG : G.Approximates) :
    (G.galerkinCore K hK hG).Data.topologicalClosure = ⊤ ∧
      (G.galerkin K hK).Verdict (G.galerkinCore K hK hG) :=
  ⟨DissipFEEC.resData_closure T.isMDissipative_op, dissipFEEC _ _⟩

theorem galerkin_sol (h : κ) (x : G.Xh h) (t : ℝ) :
    (G.galerkin K hK).sol h x t = G.incl h ((C0Group.ofBounded (G.Lh h)).S t x) := rfl

omit [CompleteSpace V] [CompleteSpace H₁] in
/-- **The discrete energy identity**: the semi-discrete Galerkin solution
`ιₕ e^{t Lₕ} x = (G.galerkin K hK).sol h x t` (`galerkin_sol`) loses exactly the discrete
outgoing flux twice, `‖xₕ(t)‖² = ‖xₕ(0)‖² - 2 ∫₀ᵗ ‖γ vₕ(s)‖² ds` (`Γₕ eₕ = γ vₕ`). -/
theorem norm_sq_galerkin_sol (h : κ) (x : G.Xh h) {t : ℝ} (ht : 0 ≤ t) :
    ‖G.incl h ((C0Group.ofBounded (G.Lh h)).S t x)‖ ^ 2 = ‖G.incl h x‖ ^ 2 -
      2 * ∫ s in (0 : ℝ)..t, ‖G.Γh h ((C0Group.ofBounded (G.Lh h)).S s x).fst‖ ^ 2 := by
  set S := (C0Group.ofBounded (G.Lh h)).toC0Semigroup
  have hx : x ∈ S.generator.domain := C0Group.mem_domain_generator_ofBounded (G.Lh h) x
  have e := S.norm_sq_S_apply ⟨x, hx⟩ ht
  have hint : ∫ s in (0 : ℝ)..t, 2 * RCLike.re ⟪S.S s (S.generator ⟨x, hx⟩), S.S s x⟫_ℝ =
      ∫ s in (0 : ℝ)..t, -(2 * ‖G.Γh h ((C0Group.ofBounded (G.Lh h)).S s x).fst‖ ^ 2) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hg : S.generator ⟨x, hx⟩ = G.Lh h x :=
      C0Group.generator_ofBounded_apply (G.Lh h) ⟨x, hx⟩
    have hc : S.S s (G.Lh h x) = G.Lh h (S.S s x) :=
      (congrArg (fun M : G.Xh h →L[ℝ] G.Xh h => M x)
        (C0Group.commute_exp_ofReal_smul (G.Lh h) s).eq).symm
    have hi := G.inner_Lh h (S.S s x)
    rw [hg, hc, RCLike.re_to_real, hi, mul_neg]
    rfl
  rw [G.norm_incl_apply, G.norm_incl_apply]
  change ‖S.S t x‖ ^ 2 = _
  rw [e, hint, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  ring


/-! #### Existence: Galerkin spaces from dense sequences -/

section DenseSeq

open TopologicalSpace

variable [SeparableSpace V] [SeparableSpace H₂]

variable (T) in
/-- **Galerkin spaces from dense sequences** (separable `V`, `H₂`): `Vₙ` spanned by the first `n`
terms of a dense sequence of `V`, `Wₙ = c Vₙ + span` of the first `n` terms of a dense sequence of
`H₂`; finite-dimensional, along `atTop`. -/
def ofDenseSeq : GalerkinData T ℕ where
  l := atTop
  Vh n := Submodule.span ℝ (Set.range fun i : Fin n => denseSeq V i)
  finiteDimensional n := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  Wh n := (Submodule.span ℝ (Set.range fun i : Fin n => denseSeq H₂ i)) ⊔
    (Submodule.span ℝ (Set.range fun i : Fin n => denseSeq V i)).map T.c.toLinearMap
  isClosed_Wh n := by
    have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range fun i : Fin n => denseSeq V i)) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range fun i : Fin n => denseSeq H₂ i)) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    exact Submodule.closed_of_finiteDimensional _
  c_mem n v hv := Submodule.mem_sup_right ⟨v, hv, rfl⟩

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] in
theorem tendsto_infDist_span_denseSeq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SeparableSpace E] {U : ℕ → Submodule ℝ E}
    (hU : ∀ n, ∀ i : Fin n, denseSeq E i ∈ U n) (x : E) :
    Tendsto (fun n => infDist x (U n : Set E)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨i, hi⟩ : ∃ i, dist x (denseSeq E i) < ε :=
    (Metric.denseRange_iff.1 (denseRange_denseSeq E)) x ε hε
  refine ⟨i + 1, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg]
  exact (infDist_le_dist_of_mem (hU n ⟨i, by omega⟩)).trans_lt hi

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
/-- **Dense-sequence Galerkin spaces approximate** `V` and `H₂`. -/
theorem approximates_ofDenseSeq : (ofDenseSeq T).Approximates :=
  ⟨tendsto_infDist_span_denseSeq fun _ i => Submodule.subset_span ⟨i, rfl⟩,
    tendsto_infDist_span_denseSeq fun _ i =>
      Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)⟩

end DenseSeq


end GalerkinData

end Feec.ImpedanceTriple
