module

public import Feec.HilbertComplex.Approximation.Ritz
public import Feec.ForMathlib.LinearPMap.Bounded
public import Feec.Semigroup.DomainSq

/-!
# Trotter–Kato from resolvent consistency: the discrete resolvent as a Ritz projection

The discrete resolvent `(1 - Lₕ)⁻¹ πₕ` is a Ritz projection for the lift `ℓ = 1 - A` of `D(A²)`;
consistent discrete resolvents with `ιₕ πₕ → 1` give its core.

## Main definitions

* `DissipFEEC.discreteRes`: the discrete resolvent `(1 - Lₕ)⁻¹`.
* `DissipFEEC.Lift.resolvent`, `Ritz.ofResolvent`: the resolvent lift and its Ritz projection.
* `DissipFEEC.Core.ofResolvent`: the Trotter–Kato core.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983]

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
  {A : E →ₗ.[𝕜] E} {κ : Type*}

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem resolvent_one_apply_sub (hA : A.IsMDissipative) (x : A.domain) :
    Operator.resolvent A 1 ((x : E) - A x) = x := by
  simpa using hA.isResolvent_one.apply_sub x

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

variable (F : DissipFEEC.{u} A κ)

/-- The discrete resolvent `(1 - Lₕ)⁻¹`. -/
def discreteRes (h : κ) : F.X h →L[𝕜] F.X h := boundedRes (F.L h)

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem norm_discreteRes_apply_le (h : κ) (y : F.X h) : ‖F.discreteRes h y‖ ≤ ‖y‖ :=
  norm_boundedRes_apply_le (F.dissipative h) y

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem discreteRes_sub (h : κ) (y : F.X h) :
    F.discreteRes h y - F.L h (F.discreteRes h y) = y :=
  boundedRes_sub (F.dissipative h) y

theorem resolvent_S {t : ℝ} (ht : 0 ≤ t) (y : E) :
    Operator.resolvent A 1 (F.S t y) = F.S t (Operator.resolvent A 1 y) :=
  resolvent_semigroup_comm F.isMDissipative ht y

/-- The data of the resolvent core: `R(1) D(A) = D(A²)`. -/
def resData : Submodule 𝕜 E := A.domain.map (Operator.resolvent A 1).toLinearMap

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem mem_domain_of_mem_resData (hA : A.IsMDissipative) {x : E} (hx : x ∈ resData (A := A)) :
    x ∈ A.domain := by
  obtain ⟨u, -, rfl⟩ := hx
  exact hA.isResolvent_one.mem_domain u

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
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
  have hd := mem_domain_of_mem_resData hA hx
  rw [genExt_of_mem hd]
  exact resolvent_one_apply_sub hA ⟨x, hd⟩

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
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

namespace Feec.HilbertComplex.DissipFEEC

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  {A : E →ₗ.[𝕜] E} {κ : Type*} (F : DissipFEEC.{u} A κ)

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem genExt_sub {y z : E} (hy : y ∈ A.domain) (hz : z ∈ A.domain) :
    genExt A (y - z) = genExt A y - genExt A z := by
  rw [genExt_of_mem (A.domain.sub_mem hy hz), genExt_of_mem hy, genExt_of_mem hz]
  exact A.toFun.map_sub ⟨y, hy⟩ ⟨z, hz⟩

theorem S_sub_genExt {z : E} (hz : z ∈ A.domain) {t : ℝ} (ht : 0 ≤ t) :
    F.S t z - genExt A (F.S t z) = F.S t (z - genExt A z) := by
  rw [_root_.map_sub, F.S_genExt hz ht]

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem genExt_mem_domain_of_mem_resData {x : E} (hx : x ∈ resData (A := A))
    (hA : A.IsMDissipative) : genExt A x ∈ A.domain := by
  have h := A.domain.sub_mem (mem_domain_of_mem_resData hA hx) (sub_genExt_mem_domain hA hx)
  rwa [sub_sub_cancel] at h

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem domainSq_le_resData (hA : A.IsMDissipative) : A.domainSq ≤ resData (A := A) :=
  fun x hx => by
    obtain ⟨hx1, hx2⟩ := LinearPMap.mem_domainSq.1 hx
    exact ⟨x - A ⟨x, hx1⟩, A.domain.sub_mem hx1 hx2, resolvent_one_apply_sub hA ⟨x, hx1⟩⟩

/-- The resolvent lift: data `D(A²)`, `ℓ = 1 - A`, read back by `ρ = (1 - A)⁻¹`. -/
def Lift.resolvent : F.Lift E where
  Data := resData (A := A)
  le_domain _ hx := mem_domain_of_mem_resData F.isMDissipative hx
  S_mem x hx t ht := by
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨_, F.isMDissipative.semigroup_mem_domain ⟨u, hu⟩ ht, F.resolvent_S ht u⟩
  lift y := y - genExt A y
  read := Operator.resolvent A 1
  read_lift _ hy := resolvent_sub_genExt F.isMDissipative hy
  continuousOn x hx := (F.isMDissipative.semigroup.strongCont (x - genExt A x)).congr fun _ ht =>
    F.S_sub_genExt (mem_domain_of_mem_resData F.isMDissipative hx) ht
  continuousOn' x hx := (F.isMDissipative.semigroup.strongCont
    (genExt A x - genExt A (genExt A x))).congr fun _ ht =>
      F.S_sub_genExt (genExt_mem_domain_of_mem_resData hx F.isMDissipative) ht
  hasDerivWithinAt x hx t ht := by
    have hxd := mem_domain_of_mem_resData F.isMDissipative hx
    have hAx := genExt_mem_domain_of_mem_resData hx F.isMDissipative
    have hu := sub_genExt_mem_domain F.isMDissipative hx
    have hd : HasDerivWithinAt (fun s => F.S s (x - genExt A x))
        (F.S t (A ⟨_, hu⟩)) (Ici t) t := F.isMDissipative.hasDerivWithinAt_semigroup ⟨_, hu⟩ ht
    rw [← genExt_of_mem hu, genExt_sub hxd hAx, ← F.S_sub_genExt hAx ht] at hd
    exact hd.congr (fun s hs => F.S_sub_genExt hxd (ht.trans hs)) (F.S_sub_genExt hxd ht)

/-- The consistency defect `Dₕ = πₕ (1 - A)⁻¹ - (1 - Lₕ)⁻¹ πₕ` of the discrete resolvent. -/
def resDefect (h : κ) : E →L[𝕜] F.X h :=
  F.proj h ∘L Operator.resolvent A 1 - F.discreteRes h ∘L F.proj h

/-- The discrete resolvent as a Ritz projection: `Rₕ = (1 - Lₕ)⁻¹ πₕ`. [Pazy1983], §3.4 -/
def Ritz.ofResolvent : F.Ritz (Lift.resolvent F) where
  R h := F.discreteRes h ∘L F.proj h
  Δ h := -F.resDefect h
  Δ' := F.resDefect
  defect_eq h y hy := by
    have hyd : y ∈ A.domain := mem_domain_of_mem_resData F.isMDissipative hy
    have hAy := genExt_mem_domain_of_mem_resData hy F.isMDissipative
    have hb := sub_genExt_mem_domain F.isMDissipative hy
    set R1 := Operator.resolvent A (1 : 𝕜)
    set a := genExt A y - genExt A (genExt A y)
    set b := y - genExt A y
    -- `(1 - A)⁻¹ (b - a) = b`, since `a = A b`
    have key : R1 b = b + R1 a := by
      have e : R1 (b - genExt A b) = b := by
        rw [genExt_of_mem hb]; exact resolvent_one_apply_sub F.isMDissipative ⟨b, hb⟩
      rw [genExt_sub hyd hAy, _root_.map_sub] at e
      exact sub_eq_iff_eq_add.1 e
    have hL : F.L h (F.discreteRes h (F.proj h b)) =
        F.discreteRes h (F.proj h b) - F.proj h b := by
      rw [eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq]
      exact (F.discreteRes_sub h _).symm
    change F.discreteRes h (F.proj h a) - F.L h (F.discreteRes h (F.proj h b)) =
      -(F.proj h (R1 a) - F.discreteRes h (F.proj h a)) +
        (F.proj h (R1 b) - F.discreteRes h (F.proj h b))
    rw [hL, key, _root_.map_add]
    abel
  bound := by
    set C := F.boundConst
    have hC := F.boundConst_nonneg
    have hG : ∀ h, ‖F.discreteRes h ∘L F.proj h‖ ≤ C := fun h =>
      ContinuousLinearMap.opNorm_le_bound _ hC fun y =>
        (F.norm_discreteRes_apply_le h _).trans
          (((F.proj h).le_opNorm y).trans (mul_le_mul_of_nonneg_right (F.norm_proj_le h)
            (norm_nonneg _)))
    have hP : ∀ h, ‖F.proj h ∘L Operator.resolvent A 1‖ ≤ C := fun h =>
      ContinuousLinearMap.opNorm_le_bound _ hC fun y => by
        have h1 : ‖Operator.resolvent A (1 : 𝕜) y‖ ≤ ‖y‖ := by
          simpa using F.isMDissipative.norm_resolvent_apply_le one_pos y
        exact ((F.proj h).le_opNorm _).trans (mul_le_mul (F.norm_proj_le h) h1 (norm_nonneg _) hC)
    have hD : ∀ h, ‖F.resDefect h‖ ≤ 2 * C := fun h =>
      (norm_sub_le _ _).trans (by linarith [hG h, hP h])
    exact ⟨2 * C, fun h => ⟨(hG h).trans (by linarith), (norm_neg (F.resDefect h)).symm ▸ hD h,
      hD h⟩⟩

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem tendsto_norm_resDefect
    (hres : ∀ z, Tendsto (fun h => F.incl h (F.discreteRes h (F.proj h z))) F.l
      (𝓝 (Operator.resolvent A 1 z)))
    (happ : ∀ z, Tendsto (fun h => F.incl h (F.proj h z)) F.l (𝓝 z)) (g : E) :
    Tendsto (fun h => ‖F.resDefect h g‖) F.l (𝓝 0) := by
  have hι : Tendsto (fun h => ‖F.incl h (F.resDefect h g)‖) F.l (𝓝 0) := by
    have := ((happ (Operator.resolvent A 1 g)).sub (hres g)).norm
    rw [sub_self, norm_zero] at this
    refine this.congr fun h => ?_
    simp only [resDefect, sub_apply, ContinuousLinearMap.comp_apply,
      _root_.map_sub]
  have h0 := hι.const_mul F.boundConst
  rw [mul_zero] at h0
  exact squeeze_zero (fun _ => norm_nonneg _) (fun h => F.norm_le_norm_incl h _) h0

theorem Ritz.tendsto_ofResolvent
    (hres : ∀ z, Tendsto (fun h => F.incl h (F.discreteRes h (F.proj h z))) F.l
      (𝓝 (Operator.resolvent A 1 z)))
    (happ : ∀ z, Tendsto (fun h => F.incl h (F.proj h z)) F.l (𝓝 z)) :
    (∀ g, Tendsto (fun h => ‖(Ritz.ofResolvent F).Δ h g‖) F.l (𝓝 0)) ∧
      ∀ g, Tendsto (fun h => ‖(Ritz.ofResolvent F).Δ' h g‖) F.l (𝓝 0) :=
  ⟨fun g => (F.tendsto_norm_resDefect hres happ g).congr fun h => (norm_neg (F.resDefect h g)).symm,
    F.tendsto_norm_resDefect hres happ⟩

/-- The Trotter–Kato core, from `ιₕ (1 - Lₕ)⁻¹ πₕ → (1 - A)⁻¹` and `ιₕ πₕ → 1`. [Pazy1983], §3.4 -/
def Core.ofResolvent
    (hres : ∀ z, Tendsto (fun h => F.incl h (F.discreteRes h (F.proj h z))) F.l
      (𝓝 (Operator.resolvent A 1 z)))
    (happ : ∀ z, Tendsto (fun h => F.incl h (F.proj h z)) F.l (𝓝 z)) : F.Core :=
  (Ritz.ofResolvent F).toCore hres (Ritz.tendsto_ofResolvent F hres happ).1
    (Ritz.tendsto_ofResolvent F hres happ).2

@[simp] theorem Core.ofResolvent_data (hres happ) :
    (Core.ofResolvent F hres happ).Data = resData (A := A) :=
  rfl

end Feec.HilbertComplex.DissipFEEC
