module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Feec.HilbertComplex.Reducing
public import Feec.HilbertComplex.HodgeWave

/-!
# The reduced two-field system of a short Hilbert complex

For a short Hilbert complex `W₀ --d₀--> W₁ --d₁--> W₂` the Hodge wave equation `U' = L U` reads
`σ' = -d₀† u`, `u' = d₀ σ - d₁† ρ`, `ρ' = d₁ u`. On data with `σ = 0` and `u ∈ N(d₀†)`
("`div u = 0`") it reduces to the two-field system

  `E' = -d₁† B`, `B' = d₁ E`,

the linearized Einstein–Bianchi system `Ė = -curl B`, `Ḃ = curl E` of the thesis (and the
reduced Maxwell system). The reduced system is itself the Hodge wave equation of the one-operator
complex `W₁ --d₁--> W₂ → 0` (`ShortHilbertComplex.reduced`), so Stone's theorem gives existence
and the energy method uniqueness, for every datum `(E₀, B₀) ∈ D(d₁) × D(d₁†)`, with no
divergence condition. With `E₀ ∈ N(d₀†)` the divergence constraint propagates and `(0, E, B)` is
the solution of the full system.

## Main definitions

* `Feec.ShortHilbertComplex.mk3 x₀ x₁ x₂`: the point `(x₀, x₁, x₂)` of `PiLp 2 (W3 W₀ W₁ W₂)`.
* `Feec.ShortHilbertComplex.IsReducedSolution S I E B`: `(E, B)` solves the reduced system on
  the time set `I`.
* `Feec.ShortHilbertComplex.reduced S`: the short complex `W₁ --d₁--> W₂ → 0`.

## Main results

* `ShortHilbertComplex.isReducedSolution_iff`: reduced solutions are the strong solutions of
  `U' = L U` for the complex `reduced S`.
* `ShortHilbertComplex.IsReducedSolution.unique`,
  `ShortHilbertComplex.existsUnique_reducedSolution`:
  existence (classical regularity) and uniqueness for every datum in `D(d₁) × D(d₁†)`.
* `ShortHilbertComplex.IsReducedSolution.mem_ker_adjoint`: the divergence constraint
  `E ∈ N(d₀†)` propagates.
* `ShortHilbertComplex.isReducedSolution_of_isStrongSolution` (Prop 4.18 (i)) and
  `ShortHilbertComplex.isStrongSolution_of_isReducedSolution` (Prop 4.18 (ii)).
* `ShortHilbertComplex.existsUnique_reducedSolution_divFree`: Prop 4.18 with existence and
  uniqueness; `ShortHilbertComplex.reducedSolution_of_exists` derives the same conclusion from any
  existence statement for the full system.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop. 4.18 (§4.10, (4.14), (4.15)), Thm 4.6
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.10 (Stone's theorem)
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

universe u

namespace Feec

/-! ### A closed subspace containing all derivatives contains the trajectory -/

section Trajectory

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- If `f` has a derivative in `K` within `[a, b]` at every `t ∈ [a, b]` and `f a ∈ K`, with `K`
a subspace with an orthogonal projection, then `f t ∈ K` on `[a, b]`. -/
theorem Evolution.mem_of_hasDerivWithinAt_mem {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    {f : ℝ → E} {a b : ℝ} (hd : ∀ t ∈ Icc a b, ∃ v ∈ K, HasDerivWithinAt f v (Icc a b) t)
    (ha : f a ∈ K) : ∀ t ∈ Icc a b, f t ∈ K := by
  choose! f' hK hd using hd
  let P : E →L[ℝ] E := (Kᗮ.starProjection : E →L[𝕜] E).restrictScalars ℝ
  have hP : ∀ v, P v = 0 ↔ v ∈ K := fun v => by
    change Kᗮ.starProjection v = 0 ↔ v ∈ K
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
  have hc := constant_of_has_deriv_right_zero (f := fun t => P (f t)) (a := a) (b := b)
    (P.continuous.comp_continuousOn fun t ht => (hd t ht).continuousWithinAt) fun t ht => by
      have h := (P.hasFDerivAt.comp_hasDerivWithinAt t (hd t (Ico_subset_Icc_self ht)))
      rw [(hP _).2 (hK t (Ico_subset_Icc_self ht))] at h
      exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  intro t ht
  rw [← hP]
  exact (hc t ht).trans ((hP _).2 ha)

end Trajectory

namespace ShortHilbertComplex

/-! ### Points of the total space -/

section Mk3

variable {W₀ W₁ W₂ : Type u}

/-- The point `(x₀, x₁, x₂)` of the total space `PiLp 2 (W3 W₀ W₁ W₂)`. -/
def mk3 (x₀ : W₀) (x₁ : W₁) (x₂ : W₂) : PiLp 2 (W3 W₀ W₁ W₂) :=
  WithLp.toLp 2 fun
    | 0 => x₀
    | 1 => x₁
    | 2 => x₂

@[simp] theorem mk3_apply_zero (x₀ : W₀) (x₁ : W₁) (x₂ : W₂) :
    (mk3 x₀ x₁ x₂ : PiLp 2 (W3 W₀ W₁ W₂)) 0 = x₀ := rfl

@[simp] theorem mk3_apply_one (x₀ : W₀) (x₁ : W₁) (x₂ : W₂) :
    (mk3 x₀ x₁ x₂ : PiLp 2 (W3 W₀ W₁ W₂)) 1 = x₁ := rfl

@[simp] theorem mk3_apply_two (x₀ : W₀) (x₁ : W₁) (x₂ : W₂) :
    (mk3 x₀ x₁ x₂ : PiLp 2 (W3 W₀ W₁ W₂)) 2 = x₂ := rfl

theorem mk3_eta (x : PiLp 2 (W3 W₀ W₁ W₂)) : mk3 (x 0) (x 1) (x 2) = x := by
  ext i; fin_cases i <;> rfl

theorem mk3_injective {x₀ y₀ : W₀} {x₁ y₁ : W₁} {x₂ y₂ : W₂}
    (h : mk3 x₀ x₁ x₂ = mk3 y₀ y₁ y₂) : x₀ = y₀ ∧ x₁ = y₁ ∧ x₂ = y₂ :=
  ⟨congrArg (fun z : PiLp 2 (W3 W₀ W₁ W₂) => (z 0 : W₀)) h,
    congrArg (fun z : PiLp 2 (W3 W₀ W₁ W₂) => (z 1 : W₁)) h,
    congrArg (fun z : PiLp 2 (W3 W₀ W₁ W₂) => (z 2 : W₂)) h⟩

theorem norm_sq_mk3 {𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀]
    [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [NormedAddCommGroup W₂]
    [InnerProductSpace 𝕜 W₂] (x₀ : W₀) (x₁ : W₁) (x₂ : W₂) :
    ‖(mk3 x₀ x₁ x₂ : PiLp 2 (W3 W₀ W₁ W₂))‖ ^ 2 = ‖x₀‖ ^ 2 + ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]; rfl

end Mk3

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]

section Deriv

variable [NormedSpace ℝ W₀] [NormedSpace ℝ W₁] [NormedSpace ℝ W₂]
omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂]

/-- Derivatives of the three components give the derivative of the point. -/
theorem hasDerivWithinAt_mk3 {f₀ : ℝ → W₀} {f₁ : ℝ → W₁} {f₂ : ℝ → W₂} {f₀' : W₀} {f₁' : W₁}
    {f₂' : W₂} {s : Set ℝ} {t : ℝ} (h₀ : HasDerivWithinAt f₀ f₀' s t)
    (h₁ : HasDerivWithinAt f₁ f₁' s t) (h₂ : HasDerivWithinAt f₂ f₂' s t) :
    HasDerivWithinAt (fun t => mk3 (f₀ t) (f₁ t) (f₂ t)) (mk3 f₀' f₁' f₂') s t := by
  have h : HasDerivWithinAt (fun t => WithLp.ofLp (mk3 (f₀ t) (f₁ t) (f₂ t)))
      (WithLp.ofLp (mk3 f₀' f₁' f₂')) s t := by
    rw [hasDerivWithinAt_pi]
    intro i; fin_cases i
    exacts [h₀, h₁, h₂]
  have := (PiLp.continuousLinearEquiv 2 ℝ (W3 W₀ W₁ W₂)).symm.hasFDerivAt.comp_hasDerivWithinAt
    t h
  simpa [Function.comp_def] using this

/-- A component of a differentiable path in the total space is differentiable. -/
theorem hasDerivWithinAt_apply {U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)} {U' : PiLp 2 (W3 W₀ W₁ W₂)}
    {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt U U' s t) (i : Fin 3) :
    HasDerivWithinAt (fun t => U t i) (U' i) s t :=
  (PiLp.proj 2 (𝕜 := ℝ) (W3 W₀ W₁ W₂) i).hasFDerivAt.comp_hasDerivWithinAt t h

end Deriv

variable (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂)

/-- Membership in the constraint subspace `{0} × N(d₀†) × Y` of Prop 4.16, in coordinates. -/
theorem mem_totalSub_divFreeSub {Y : Submodule 𝕜 W₂} [Y.HasOrthogonalProjection]
    {x : PiLp 2 (W3 W₀ W₁ W₂)} : x ∈ HilbertComplex.totalSub (S.divFreeSub Y) ↔
      (x 0 : W₀) = 0 ∧ (x 1 : W₁) ∈ (S.d₀†).ker ∧ (x 2 : W₂) ∈ Y := by
  rw [HilbertComplex.mem_totalSub]
  refine ⟨fun h => ⟨(Submodule.mem_bot 𝕜 (x := (x 0 : W₀))).1 (h 0), h 1, h 2⟩,
    fun ⟨h0, h1, h2⟩ i => ?_⟩
  fin_cases i
  exacts [(Submodule.mem_bot 𝕜 (x := (x 0 : W₀))).2 h0, h1, h2]

/-- The one-operator complex `W₁ --d₁--> W₂ → 0` whose Hodge wave equation is the reduced
system (4.15). -/
def reduced : ShortHilbertComplex 𝕜 W₁ W₂ PUnit.{u + 1} := ofOp S.d₁ S.dense₁ S.closed₁

@[simp] theorem reduced_d₀ : S.reduced.d₀ = S.d₁ := rfl

theorem reduced_adjoint_d₁_apply (y : (S.reduced.d₁†).domain) : S.reduced.d₁† y = 0 :=
  apply_eq_zero_of_eq_zero (show (0 : W₂ →ₗ.[𝕜] PUnit.{u + 1})† = 0 from adjoint_zero) y

/-- `(E, B, 0) ∈ D(L)` for the reduced complex iff `E ∈ D(d₁)` and `B ∈ D(d₁†)`. -/
theorem mk3_mem_reduced_wave_domain {E : W₁} {B : W₂} {z : PUnit.{u + 1}} :
    mk3 E B z ∈ S.reduced.wave.domain ↔ E ∈ S.d₁.domain ∧ B ∈ (S.d₁†).domain := by
  rw [mem_wave_domain]
  refine ⟨fun h => ⟨h.1, h.2.2.1⟩, fun h => ⟨h.1, (show B ∈ (0 : W₂ →ₗ.[𝕜] PUnit.{u + 1}).domain
    from Submodule.mem_top), h.2, ?_⟩⟩
  change z ∈ ((0 : W₂ →ₗ.[𝕜] PUnit.{u + 1})†).domain
  rw [adjoint_zero]; exact Submodule.mem_top

variable [NormedSpace ℝ W₁] [IsScalarTower ℝ 𝕜 W₁] [NormedSpace ℝ W₂] [IsScalarTower ℝ 𝕜 W₂]

/-! ### The reduced system -/

/-- `(E, B)` is a **strong solution of the reduced system** `E' = -d₁† B`, `B' = d₁ E` on the time
set `I` (for the linearized Einstein–Bianchi complex: `Ė = -curl B`, `Ḃ = curl E`), with
`E ∈ D(d₁)` and `B ∈ D(d₁†)`. See [QuennevilleBelair2015], (4.15) (§4.10). -/
structure IsReducedSolution (I : Set ℝ) (E : ℝ → W₁) (B : ℝ → W₂) : Prop where
  memE : ∀ t ∈ I, E t ∈ S.d₁.domain
  memB : ∀ t ∈ I, B t ∈ (S.d₁†).domain
  derivE : ∀ t (ht : t ∈ I), HasDerivWithinAt E (-(S.d₁† ⟨B t, memB t ht⟩)) I t
  derivB : ∀ t (ht : t ∈ I), HasDerivWithinAt B (S.d₁ ⟨E t, memE t ht⟩) I t

omit [IsScalarTower ℝ 𝕜 W₁] [IsScalarTower ℝ 𝕜 W₂] in
/-- **The reduced system is a Hodge wave equation**: `(E, B)` solves the reduced system on `I`
iff `(E, B, 0)` is a strong solution of `U' = L U` for the complex `W₁ --d₁--> W₂ → 0`. -/
theorem isReducedSolution_iff {I : Set ℝ} {E : ℝ → W₁} {B : ℝ → W₂} :
    S.IsReducedSolution I E B ↔
      Evolution.IsStrongSolution S.reduced.wave I 0 (fun t => mk3 (E t) (B t) PUnit.unit) := by
  constructor
  · intro h
    have hmem : ∀ t ∈ I, mk3 (E t) (B t) PUnit.unit ∈ S.reduced.wave.domain := fun t ht =>
      (S.mk3_mem_reduced_wave_domain).2 ⟨h.memE t ht, h.memB t ht⟩
    refine Evolution.IsStrongSolution.of_hasDerivWithinAt hmem fun t ht => ?_
    have e : S.reduced.wave ⟨_, hmem t ht⟩ + (0 : ℝ → PiLp 2 _) t =
        mk3 (-(S.d₁† ⟨B t, h.memB t ht⟩)) (S.d₁ ⟨E t, h.memE t ht⟩) PUnit.unit := by
      rw [Pi.zero_apply, add_zero]
      ext i; fin_cases i
      · exact S.reduced.wave_apply_zero _
      · refine (S.reduced.wave_apply_one _).trans ?_
        rw [S.reduced_adjoint_d₁_apply, sub_zero]; rfl
      · exact Subsingleton.elim (α := PUnit.{u + 1}) _ _
    rw [e]
    exact hasDerivWithinAt_mk3 (h.derivE t ht) (h.derivB t ht) (hasDerivWithinAt_const _ _ _)
  · intro h
    have hmem := fun t (ht : t ∈ I) => (S.mk3_mem_reduced_wave_domain).1 (h.mem_domain ht)
    refine ⟨fun t ht => (hmem t ht).1, fun t ht => (hmem t ht).2, fun t ht => ?_, fun t ht => ?_⟩
    · have := hasDerivWithinAt_apply (h.hasDerivWithinAt ht) 0
      rw [Pi.zero_apply, add_zero, wave_apply_zero] at this
      exact this
    · have := hasDerivWithinAt_apply (h.hasDerivWithinAt ht) 1
      rw [Pi.zero_apply, add_zero, wave_apply_one] at this
      exact this.congr_deriv (by rw [S.reduced_adjoint_d₁_apply, sub_zero]; rfl)

variable {S}

omit [IsScalarTower ℝ 𝕜 W₁] [IsScalarTower ℝ 𝕜 W₂] in
/-- **Uniqueness for the reduced system**: two solutions on `[a, b]` with the same data agree.
No divergence condition is needed (energy method for the reduced wave operator). -/
theorem IsReducedSolution.unique {a b : ℝ} {E E' : ℝ → W₁} {B B' : ℝ → W₂}
    (h : S.IsReducedSolution (Icc a b) E B) (h' : S.IsReducedSolution (Icc a b) E' B')
    (hE : E a = E' a) (hB : B a = B' a) : EqOn E E' (Icc a b) ∧ EqOn B B' (Icc a b) := by
  have := ((S.isReducedSolution_iff).1 h).unique S.reduced.isSkewAdjoint_wave.isDissipative
    ((S.isReducedSolution_iff).1 h') (by rw [hE, hB])
  exact ⟨fun t ht => (mk3_injective (this ht)).1, fun t ht => (mk3_injective (this ht)).2.1⟩

/-- **Existence and uniqueness for the reduced system** (Stone's theorem for the reduced wave
operator): for `E₀ ∈ D(d₁)` and `B₀ ∈ D(d₁†)` there is a solution on `[a, b]` in
`C⁰([a, b]; D(d₁) × D(d₁†)) ∩ C¹([a, b]; W₁ × W₂)`, unique among strong solutions, conserving
the energy `‖E‖² + ‖B‖²`. No divergence condition is needed.
See [QuennevilleBelair2015], Prop. 4.18 (§4.10). -/
theorem existsUnique_reducedSolution {E₀ : W₁} {B₀ : W₂} (hE₀ : E₀ ∈ S.d₁.domain)
    (hB₀ : B₀ ∈ (S.d₁†).domain) (a b : ℝ) :
    ∃ E B, E a = E₀ ∧ B a = B₀ ∧ S.IsReducedSolution (Icc a b) E B ∧
      Evolution.IsClassicalSolution S.reduced.wave (Icc a b) 0
        (fun t => mk3 (E t) (B t) PUnit.unit) ∧
      (∀ t ∈ Icc a b, ‖E t‖ ^ 2 + ‖B t‖ ^ 2 = ‖E₀‖ ^ 2 + ‖B₀‖ ^ 2) ∧
      ∀ E' B', E' a = E₀ → B' a = B₀ → S.IsReducedSolution (Icc a b) E' B' →
        EqOn E' E (Icc a b) ∧ EqOn B' B (Icc a b) := by
  obtain ⟨U, hU0, hU, -, -, hnorm⟩ := HilbertComplex.HodgeWave.existsUnique_hom
    S.reduced.toHilbertComplex ((S.mk3_mem_reduced_wave_domain (z := PUnit.unit)).2 ⟨hE₀, hB₀⟩)
    a b
  set E : ℝ → W₁ := fun t => U t 0 with hE
  set B : ℝ → W₂ := fun t => U t 1 with hB
  have hUe : ∀ t, U t = mk3 (E t) (B t) PUnit.unit := fun t => by
    rw [← mk3_eta (U t)]; rfl
  have hS : Evolution.IsStrongSolution S.reduced.wave (Icc a b) 0
      (fun t => mk3 (E t) (B t) PUnit.unit) :=
    hU.toIsStrongSolution.congr (fun t _ => hUe t) fun _ _ => rfl
  have hR : S.IsReducedSolution (Icc a b) E B := (S.isReducedSolution_iff).2 hS
  have h0 : mk3 (E a) (B a) PUnit.unit = mk3 E₀ B₀ PUnit.unit := (hUe a).symm.trans hU0
  refine ⟨E, B, (mk3_injective h0).1, (mk3_injective h0).2.1, hR,
    ⟨hS, hU.deriv_cont.imp fun V hV => ⟨hV.1, fun t ht => hUe t ▸ hV.2 t ht⟩⟩,
    fun t ht => ?_, fun E' B' hE' hB' h' => h'.unique hR (hE'.trans (mk3_injective h0).1.symm)
      (hB'.trans (mk3_injective h0).2.1.symm)⟩
  have h1 := hnorm t ht
  rw [hUe t] at h1
  have h2 : ‖(mk3 (E t) (B t) PUnit.unit : PiLp 2 (W3 W₁ W₂ PUnit.{u + 1}))‖ ^ 2 =
      ‖(mk3 E₀ B₀ PUnit.unit : PiLp 2 (W3 W₁ W₂ PUnit.{u + 1}))‖ ^ 2 := by rw [h1]
  rw [norm_sq_mk3 (𝕜 := 𝕜), norm_sq_mk3 (𝕜 := 𝕜)] at h2
  simpa using h2

omit [IsScalarTower ℝ 𝕜 W₂] in
/-- **The divergence constraint propagates** along the reduced system: if `E a ∈ N(d₀†)` then
`E t ∈ N(d₀†)` on `[a, b]` (`d₀† d₁† = 0`). In particular `E t ∈ D(d₁) ∩ D(d₀†)`.
See [QuennevilleBelair2015], Prop. 4.18 (§4.10). -/
theorem IsReducedSolution.mem_ker_adjoint {a b : ℝ} {E : ℝ → W₁} {B : ℝ → W₂}
    (h : S.IsReducedSolution (Icc a b) E B) (ha : E a ∈ (S.d₀†).ker) :
    ∀ t ∈ Icc a b, E t ∈ (S.d₀†).ker := by
  have := hasOrthogonalProjection_ker S.d₀† (adjoint_isClosed S.dense₀)
  refine Evolution.mem_of_hasDerivWithinAt_mem (fun t ht => ⟨_, ?_, h.derivE t ht⟩) ha
  refine (S.d₀†).ker.neg_mem (mem_ker_iff.2 ⟨⟨_, S.toHilbertComplex.adjoint_mapsTo 0 1 2
    ⟨B t, h.memB t ht⟩⟩, rfl, S.toHilbertComplex.adjoint_comp_eq_zero 0 1 2 ⟨B t, h.memB t ht⟩⟩)

/-! ### Equivalence with the full system (Prop 4.18) -/

variable [NormedSpace ℝ W₀] [IsScalarTower ℝ 𝕜 W₀]

/-- **Prop 4.18 (i)**: a strong solution `(σ, E, B)` of the Hodge wave equation `U' = L U` on
`[a, b]` with data `(0, E₀, B₀)`, `E₀ ∈ N(d₀†)`, keeps `σ ≡ 0` and `E ∈ N(d₀†)`, and `(E, B)`
solves the reduced system (4.15). See [QuennevilleBelair2015], Prop. 4.18 (§4.10, (4.14)). -/
theorem isReducedSolution_of_isStrongSolution {a b : ℝ} {U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)}
    (hU : Evolution.IsStrongSolution S.wave (Icc a b) 0 U) (h0 : (U a 0 : W₀) = 0)
    (h1 : (U a 1 : W₁) ∈ (S.d₀†).ker) :
    (∀ t ∈ Icc a b, (U t 0 : W₀) = 0 ∧ (U t 1 : W₁) ∈ (S.d₀†).ker) ∧
      S.IsReducedSolution (Icc a b) (fun t => U t 1 : ℝ → W₁) (fun t => U t 2 : ℝ → W₂) := by
  have ha : U a ∈ HilbertComplex.totalSub (S.divFreeSub ⊤) :=
    (S.mem_totalSub_divFreeSub (Y := ⊤)).2 ⟨h0, h1, Submodule.mem_top (x := (U a 2 : W₂))⟩
  have hF : ∀ t ∈ Icc a b, (0 : ℝ → PiLp 2 (W3 W₀ W₁ W₂)) t ∈
      HilbertComplex.totalSub (S.divFreeSub ⊤) := fun _ _ => Submodule.zero_mem _
  have hK := S.divFree_propagates ⊤ (fun _ => Submodule.mem_top) hU ha hF
  have hσ : ∀ t ∈ Icc a b, (U t 0 : W₀) = 0 := fun t ht =>
    ((S.mem_totalSub_divFreeSub).1 (hK t ht)).1
  refine ⟨fun t ht => ⟨hσ t ht, ((S.mem_totalSub_divFreeSub).1 (hK t ht)).2.1⟩,
    ⟨fun t ht => (S.mem_wave_domain.1 (hU.mem_domain ht)).2.1, fun t ht => (S.mem_wave_domain.1 (hU.mem_domain ht)).2.2.2, fun t ht => ?_, fun t ht => ?_⟩⟩
  · have := hasDerivWithinAt_apply (hU.hasDerivWithinAt ht) 1
    rw [Pi.zero_apply, add_zero, wave_apply_one] at this
    refine this.congr_deriv ?_
    erw [LinearPMap.apply_mk_eq_zero S.d₀ _ (hσ t ht), zero_sub]
  · have := hasDerivWithinAt_apply (hU.hasDerivWithinAt ht) 2
    rw [Pi.zero_apply, add_zero, wave_apply_two] at this
    exact this

omit [IsScalarTower ℝ 𝕜 W₀] [IsScalarTower ℝ 𝕜 W₂] in
/-- **Prop 4.18 (ii)**: if `(E, B)` solves the reduced system (4.15) on `[a, b]` with
`E a ∈ N(d₀†)`, then `(0, E, B)` is a strong solution of the Hodge wave equation `U' = L U`.
See [QuennevilleBelair2015], Prop. 4.18 (§4.10, (4.14)). -/
theorem isStrongSolution_of_isReducedSolution {a b : ℝ} {E : ℝ → W₁} {B : ℝ → W₂}
    (h : S.IsReducedSolution (Icc a b) E B) (ha : E a ∈ (S.d₀†).ker) :
    Evolution.IsStrongSolution S.wave (Icc a b) 0 (fun t => mk3 0 (E t) (B t)) := by
  have hk := h.mem_ker_adjoint ha
  have hmem : ∀ t ∈ Icc a b, mk3 0 (E t) (B t) ∈ S.wave.domain := fun t ht =>
    S.mem_wave_domain.2 ⟨S.d₀.domain.zero_mem, h.memE t ht,
      (show E t ∈ (S.d₀†).domain from ker_le_domain (hk t ht)), h.memB t ht⟩
  refine Evolution.IsStrongSolution.of_hasDerivWithinAt hmem fun t ht => ?_
  have e : S.wave ⟨_, hmem t ht⟩ + (0 : ℝ → PiLp 2 _) t =
      mk3 0 (-(S.d₁† ⟨B t, h.memB t ht⟩)) (S.d₁ ⟨E t, h.memE t ht⟩) := by
    rw [Pi.zero_apply, add_zero]
    obtain ⟨y, hy, hy0⟩ := mem_ker_iff.1 (hk t ht)
    ext i; fin_cases i
    · refine (S.wave_apply_zero _).trans ?_
      change -(S.d₀† ⟨E t, _⟩) = (0 : W₀)
      have : (⟨E t, ker_le_domain (hk t ht)⟩ : (S.d₀†).domain) = y := Subtype.ext hy
      rw [neg_eq_zero, this, hy0]
    · refine (S.wave_apply_one _).trans ?_
      change S.d₀ ⟨0, _⟩ - S.d₁† ⟨B t, _⟩ = -(S.d₁† ⟨B t, h.memB t ht⟩)
      erw [LinearPMap.apply_mk_eq_zero S.d₀ _ rfl, zero_sub]
    · exact S.wave_apply_two _
  rw [e]
  exact hasDerivWithinAt_mk3 (hasDerivWithinAt_const _ _ _) (h.derivE t ht) (h.derivB t ht)

omit [IsScalarTower ℝ 𝕜 W₀] in
/-- **Prop 4.18** (existence, uniqueness, constraint propagation): for `E₀ ∈ D(d₁) ∩ N(d₀†)`
("`div E₀ = 0`") and `B₀ ∈ D(d₁†)`, the reduced system (4.15) has a solution on `[a, b]`, unique
among strong solutions; `E` stays in `N(d₀†)`, and `(0, E, B)` is the strong solution of the
Hodge wave equation (4.14) with data `(0, E₀, B₀)`. Existence is Stone's theorem; no
well-posedness hypothesis.

Correction: the data space `V¹ × V²` of the thesis is too weak; `B₀` must lie in `D(d₁†)`.
See [QuennevilleBelair2015], Prop. 4.18 (§4.10, (4.14), (4.15)). -/
theorem existsUnique_reducedSolution_divFree {E₀ : W₁} {B₀ : W₂} (hE₀ : E₀ ∈ S.d₁.domain)
    (hE₀k : E₀ ∈ (S.d₀†).ker) (hB₀ : B₀ ∈ (S.d₁†).domain) (a b : ℝ) :
    ∃ E B, E a = E₀ ∧ B a = B₀ ∧ S.IsReducedSolution (Icc a b) E B ∧
      (∀ t ∈ Icc a b, E t ∈ (S.d₀†).ker) ∧
      Evolution.IsStrongSolution S.wave (Icc a b) 0 (fun t => mk3 0 (E t) (B t)) ∧
      ∀ E' B', E' a = E₀ → B' a = B₀ → S.IsReducedSolution (Icc a b) E' B' →
        EqOn E' E (Icc a b) ∧ EqOn B' B (Icc a b) := by
  obtain ⟨E, B, hE, hB, hR, -, -, huniq⟩ := existsUnique_reducedSolution hE₀ hB₀ a b
  exact ⟨E, B, hE, hB, hR, hR.mem_ker_adjoint (hE ▸ hE₀k),
    isStrongSolution_of_isReducedSolution hR (hE ▸ hE₀k), huniq⟩

/-- Prop 4.18 from an existence statement for the full system (the form of the thesis, which
derives (4.15) from the well-posedness of (4.14), Thm 4.6): the reduced solution is read off from
the solution of (4.14). Corollary of `isReducedSolution_of_isStrongSolution`; see
`existsUnique_reducedSolution_divFree` for the unconditional statement.
See [QuennevilleBelair2015], Prop. 4.18 (§4.10). -/
theorem reducedSolution_of_exists {a b : ℝ}
    (hex : ∀ U₀ ∈ S.wave.domain, ∃ U, U a = U₀ ∧ Evolution.IsStrongSolution S.wave (Icc a b) 0 U)
    {E₀ : W₁} {B₀ : W₂} (hE₀ : E₀ ∈ S.d₁.domain) (hE₀k : E₀ ∈ (S.d₀†).ker)
    (hB₀ : B₀ ∈ (S.d₁†).domain) :
    ∃ E B, E a = E₀ ∧ B a = B₀ ∧ S.IsReducedSolution (Icc a b) E B ∧
      (∀ t ∈ Icc a b, E t ∈ (S.d₀†).ker) ∧
      Evolution.IsStrongSolution S.wave (Icc a b) 0 (fun t => mk3 0 (E t) (B t)) ∧
      ∀ E' B', E' a = E₀ → B' a = B₀ → S.IsReducedSolution (Icc a b) E' B' →
        EqOn E' E (Icc a b) ∧ EqOn B' B (Icc a b) := by
  obtain ⟨U, hU0, hU⟩ := hex (mk3 0 E₀ B₀)
    (S.mem_wave_domain.2 ⟨S.d₀.domain.zero_mem, hE₀,
      (show E₀ ∈ (S.d₀†).domain from ker_le_domain hE₀k), hB₀⟩)
  obtain ⟨-, hR⟩ := isReducedSolution_of_isStrongSolution hU (by rw [hU0]; rfl)
    (by rw [hU0]; exact hE₀k)
  have hE : (U a 1 : W₁) = E₀ := by rw [hU0]; rfl
  have hB : (U a 2 : W₂) = B₀ := by rw [hU0]; rfl
  exact ⟨_, _, hE, hB, hR, hR.mem_ker_adjoint (hE ▸ hE₀k),
    isStrongSolution_of_isReducedSolution hR (hE ▸ hE₀k), fun E' B' hE' hB' h' =>
      h'.unique hR (hE'.trans hE.symm) (hB'.trans hB.symm)⟩

end ShortHilbertComplex

end Feec
