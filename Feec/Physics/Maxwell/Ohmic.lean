module

public import Feec.Physics.Maxwell.Media
public import Feec.Semigroup.Perturbation
public import Feec.Evolution.WellPosed

/-!
# Maxwell's equations with Ohmic loss

In a conducting medium the current is `J = σ E` (Ohm's law) for a conductivity `σ`: a bounded
operator on the electric `L²` space with `re ⟪σ E, E⟫ ≥ 0` (e.g. self-adjoint and `σ ≥ 0`, a
multiplication by a measurable nonnegative matrix field). Maxwell's equations become

  `ε E' = −d₁† H − σ E`,  `μ H' = d₁ E`

on the field complex `0 → W₁ --d₁--> W₂` (`Maxwell.fields S`: the short complex `S` with its
first space replaced by `0`; with `H ↦ −H` this is `ε E' = curl H − σ E`, `μ H' = −curl E`).
The gauge variable of the Hodge wave formulation is dropped on purpose: with loss the charge
`d₀† (ε E)` no longer vanishes, and in the window formulation `σ' = −d₀† (ε E)` it would feed
back into `E` through `ε d₀ σ`, which is not Maxwell's system.

In the variables `(e E, m H)` of the medium the generator is `L' − Σ`, with `L'` the
skew-adjoint wave operator of the conjugated complex and `Σ = diag(0, e⁻† σ e⁻¹, 0)` bounded
with `re ⟪Σ x, x⟫ ≥ 0`.

## Main definitions

* `Maxwell.fields S`: the field complex `0 → W₁ → W₂` of a short complex `S`.
* `Medium.loss σ`: `Σ = diag(0, e⁻† σ e⁻¹, 0)`; `Medium.ohmicGen S σ = L' − Σ`;
  `Medium.ohmic S σ`: the physical operator `(E, H) ↦ (−ε⁻¹ (d₁† H + σ E), μ⁻¹ d₁ E)`
  (`ε_electric_ohmic_apply`, `μ_magnetic_ohmic_apply`).
* `Medium.ohmicSemigroup S σ`: the bounded perturbation (Dyson–Phillips) `C0Semigroup.perturb`
  of Stone's group of `L'` by `−Σ`.

## Main results

* `Medium.generator_ohmicSemigroup`: its generator is `L' − Σ` (`C0Semigroup.generator_perturb`).
* `Medium.ohmic_existsUnique`: existence and uniqueness of classical solutions.
* `Medium.hasDerivWithinAt_energy`: **energy decay**,
  `d/dt ½ (⟪ε E, E⟫ + ⟪μ H, H⟫) = −re ⟪σ E, E⟫`.
* `Medium.ohmic_magnetic_gauss_propagates`: the magnetic Gauss law `μ H ∈ Y`
  (`div (μ H) = 0`) propagates, for every bounded `σ` (no sign condition).

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 8 (evolution problems)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.1 (bounded perturbations), §1.4 (dissipative operators and contraction semigroups)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.3 (classical solutions of semigroup evolution equations)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.Maxwell

universe u

open ShortHilbertComplex HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]

/-- The **field complex** `0 → W₁ --d₁--> W₂` of a short complex: Maxwell's equations without
the gauge variable. -/
def fields (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂) : ShortHilbertComplex 𝕜 PUnit.{u + 1} W₁ W₂ where
  d₀ := 0
  d₁ := S.d₁
  dense₀ := by simp [zero_domain]
  dense₁ := S.dense₁
  closed₀ := LinearPMap.isClosed_zero
  closed₁ := S.closed₁
  mapsTo x := (apply_eq_zero_of_eq_zero rfl x).symm ▸ S.d₁.domain.zero_mem
  comp x := LinearPMap.apply_mk_eq_zero _ _ (apply_eq_zero_of_eq_zero rfl x)

namespace Medium

variable (M : Medium 𝕜 W₁ W₂) (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂) (σ : W₁ →L[𝕜] W₁)

/-! ### The loss operator and the Ohmic generator -/

/-- The diagonal entries of the conjugated loss `Σ = diag(0, e⁻† σ e⁻¹, 0)`. -/
def lossW : ∀ i : Fin 3, W3 PUnit.{u + 1} W₁ W₂ i →L[𝕜] W3 PUnit.{u + 1} W₁ W₂ i
  | 0 => 0
  | 1 => (M.e.adjoint.symm : W₁ →L[𝕜] W₁) ∘L σ ∘L (M.e.symm : W₁ →L[𝕜] W₁)
  | 2 => 0

/-- The conjugated **loss operator** `Σ = diag(0, e⁻† σ e⁻¹, 0)`. -/
def loss : PiLp 2 (W3 PUnit.{u + 1} W₁ W₂) →L[𝕜] PiLp 2 (W3 PUnit.{u + 1} W₁ W₂) :=
  ((PiLp.continuousLinearEquiv 2 𝕜 (W3 PUnit.{u + 1} W₁ W₂)).symm :
      (∀ i, W3 PUnit.{u + 1} W₁ W₂ i) →L[𝕜] PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)).comp
    ((ContinuousLinearMap.pi fun i => (M.lossW σ i).comp (ContinuousLinearMap.proj i)).comp
      (PiLp.continuousLinearEquiv 2 𝕜 (W3 PUnit.{u + 1} W₁ W₂) :
        PiLp 2 (W3 PUnit.{u + 1} W₁ W₂) →L[𝕜] ∀ i, W3 PUnit.{u + 1} W₁ W₂ i))

omit [CompleteSpace W₀] [CompleteSpace W₂] in
theorem electric_loss (x : PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)) :
    electric (M.loss σ x) = M.e.adjoint.symm (σ (M.e.symm (electric x))) := rfl

omit [CompleteSpace W₀] [CompleteSpace W₂] in
theorem magnetic_loss (x : PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)) :
    magnetic (M.loss σ x) = 0 := rfl

omit [CompleteSpace W₀] [CompleteSpace W₂] in
/-- `⟪Σ x, x⟫ = ⟪σ E, E⟫` for `x = (0, e E, ·)`. -/
theorem inner_loss_apply (x : PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)) :
    ⟪M.loss σ x, x⟫_𝕜 = ⟪σ (M.e.symm (electric x)), M.e.symm (electric x)⟫_𝕜 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  change ⟪(0 : PUnit.{u + 1}), gauge x⟫_𝕜 + ⟪electric (M.loss σ x), electric x⟫_𝕜 +
    ⟪(0 : W₂), magnetic x⟫_𝕜 = _
  rw [inner_zero_left, inner_zero_left, zero_add, add_zero, electric_loss,
    ContinuousLinearEquiv.inner_adjoint_symm_apply]

/-- The conjugated **Ohmic generator** `L' − Σ` on `0 × W₁ × W₂`. -/
def ohmicGen : PiLp 2 (W3 PUnit.{u + 1} W₁ W₂) →ₗ.[𝕜] PiLp 2 (W3 PUnit.{u + 1} W₁ W₂) :=
  ((-M.loss σ : PiLp 2 (W3 PUnit.{u + 1} W₁ W₂) →L[𝕜] PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)) :
    PiLp 2 (W3 PUnit.{u + 1} W₁ W₂) →ₗ[𝕜] PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)) +ᵥ
      (M.complex (fields S)).wave

/-- The **Ohmic Maxwell operator** in the physical variables `(E, H)`:
`(E, H) ↦ (−ε⁻¹ (d₁† H + σ E), μ⁻¹ d₁ E)`. -/
def ohmic : PiLp 2 (W3 PUnit.{u + 1} W₁ W₂) →ₗ.[𝕜] PiLp 2 (W3 PUnit.{u + 1} W₁ W₂) :=
  (M.ohmicGen S σ).conj (M.state PUnit.{u + 1}).symm (M.state PUnit.{u + 1}).symm

/-- `D(ohmic) = {(E, H) | E ∈ D(d₁), H ∈ D(d₁†)}`. -/
theorem mem_ohmic_domain {U : PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)} :
    U ∈ (M.ohmic S σ).domain ↔ electric U ∈ S.d₁.domain ∧ magnetic U ∈ S.d₁†.domain := by
  change U ∈ (M.maxwell (fields S)).domain ↔ _
  rw [mem_maxwell_domain]
  constructor
  · rintro ⟨-, h1, -, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨Submodule.mem_top, h1, ?_, h3⟩
    change M.ε (electric U) ∈ ((0 : PUnit.{u + 1} →ₗ.[𝕜] W₁)†).domain
    rw [adjoint_zero]
    exact Submodule.mem_top

variable {M S σ}

theorem ohmic_apply (x : (M.ohmic S σ).domain) :
    M.ohmic S σ x = M.maxwell (fields S) ⟨x, x.2⟩ -
      (M.state PUnit.{u + 1}).symm (M.loss σ (M.state PUnit.{u + 1} x)) := by
  change (M.state PUnit.{u + 1}).symm (-M.loss σ (M.state PUnit.{u + 1} x) +
    (M.complex (fields S)).wave ⟨M.state PUnit.{u + 1} x, x.2⟩) = _
  rw [_root_.map_add, _root_.map_neg, neg_add_eq_sub]
  rfl

/-- `ε (ohmic U)_E = −d₁† H − σ E`: Ampère's law with Ohm's current, `ε E' = −d₁† H − σ E`. -/
theorem ε_electric_ohmic_apply (x : (M.ohmic S σ).domain) :
    M.ε (electric (M.ohmic S σ x)) =
      -S.d₁† ⟨magnetic x.1, (M.mem_ohmic_domain S σ |>.1 x.2).2⟩ - σ (electric x.1) := by
  rw [ohmic_apply]
  change M.ε (electric (M.maxwell (fields S) ⟨x, x.2⟩) -
    M.e.symm (electric (M.loss σ (M.state PUnit.{u + 1} x)))) = _
  rw [_root_.map_sub, ε_electric_maxwell_apply, ε_e_symm_apply, electric_loss,
    ContinuousLinearEquiv.apply_symm_apply]
  change M.ε ((0 : PUnit.{u + 1} →ₗ.[𝕜] W₁) ⟨gauge x.1, _⟩) - _ - σ (M.e.symm (M.e (electric x.1)))
    = _
  rw [apply_eq_zero_of_eq_zero rfl, _root_.map_zero, zero_sub,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- `μ (ohmic U)_H = d₁ E`: Faraday's law `μ H' = d₁ E`. -/
theorem μ_magnetic_ohmic_apply (x : (M.ohmic S σ).domain) :
    M.μ (magnetic (M.ohmic S σ x)) = S.d₁ ⟨electric x.1, (M.mem_ohmic_domain S σ |>.1 x.2).1⟩ := by
  rw [ohmic_apply]
  change M.μ (magnetic (M.maxwell (fields S) ⟨x, x.2⟩) -
    M.m.symm (magnetic (M.loss σ (M.state PUnit.{u + 1} x)))) = _
  rw [magnetic_loss, _root_.map_zero, sub_zero, μ_magnetic_maxwell_apply]
  rfl

/-! ### The contraction semigroup -/

variable [NormedSpace ℝ W₁] [IsScalarTower ℝ 𝕜 W₁] [NormedSpace ℝ W₂] [IsScalarTower ℝ 𝕜 W₂]

variable (M S σ)

/-- The **Ohmic semigroup**: the bounded perturbation by `−Σ` (Dyson–Phillips) of Stone's
isometric group of the skew-adjoint wave operator `L'` of the conjugated complex. -/
def ohmicSemigroup : C0Semigroup 𝕜 (PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)) :=
  (M.isSkewAdjoint_wave_complex (fields S)).group.toC0Semigroup.perturb (-M.loss σ)

/-- **The generator of the Ohmic semigroup is `L' − Σ`.** -/
theorem generator_ohmicSemigroup : (M.ohmicSemigroup S σ).generator = M.ohmicGen S σ := by
  rw [ohmicSemigroup, C0Semigroup.generator_perturb]
  change _ +ᵥ (M.isSkewAdjoint_wave_complex (fields S)).group.generator = _
  rw [LinearPMap.IsSkewAdjoint.generator_group]
  rfl

/-! ### Well-posedness, energy decay, magnetic Gauss law -/

/-- Strong solutions of the Ohmic Maxwell equations are, in the variables `(e E, m H)`, the
strong solutions of `V' = (L' − Σ) V + Φ F`. -/
theorem isStrongSolution_ohmic_iff {I : Set ℝ} {F U : ℝ → PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)} :
    Evolution.IsStrongSolution (M.ohmic S σ) I F U ↔
      Evolution.IsStrongSolution (M.ohmicGen S σ) I (fun t => M.state PUnit.{u + 1} (F t))
        (fun t => M.state PUnit.{u + 1} (U t)) :=
  Evolution.isStrongSolution_conj_symm_iff (M.state PUnit.{u + 1})

/-- **Maxwell's equations with Ohmic loss**: a strong solution `U = (E, H)` of `U' = A U + F`
satisfies, at every `t ∈ I`, `(ε E)' = −d₁† H − σ E + ε F_E` and `(μ H)' = d₁ E + μ F_H`. -/
theorem ohmic_equations {I : Set ℝ} {F U : ℝ → PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)}
    (hU : Evolution.IsStrongSolution (M.ohmic S σ) I F U) (t : ℝ) (ht : t ∈ I) :
    HasDerivWithinAt (fun s => M.ε (electric (U s)))
        (-S.d₁† ⟨magnetic (U t), (M.mem_ohmic_domain S σ |>.1 (hU.mem_domain ht)).2⟩ -
          σ (electric (U t)) + M.ε (electric (F t))) I t ∧
      HasDerivWithinAt (fun s => M.μ (magnetic (U s)))
        (S.d₁ ⟨electric (U t), (M.mem_ohmic_domain S σ |>.1 (hU.mem_domain ht)).1⟩ +
          M.μ (magnetic (F t))) I t := by
  have hd := hU.hasDerivWithinAt ht
  set x : (M.ohmic S σ).domain := ⟨U t, hU.mem_domain ht⟩
  let p₁ : PiLp 2 (W3 PUnit.{u + 1} W₁ W₂) →L[𝕜] W₁ :=
    M.ε ∘L PiLp.proj 2 (W3 PUnit.{u + 1} W₁ W₂) 1
  let p₂ : PiLp 2 (W3 PUnit.{u + 1} W₁ W₂) →L[𝕜] W₂ :=
    M.μ ∘L PiLp.proj 2 (W3 PUnit.{u + 1} W₁ W₂) 2
  have h₁ : HasDerivWithinAt (fun s => M.ε (electric (U s))) (p₁ (M.ohmic S σ x + F t)) I t :=
    (p₁.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hd
  have h₂ : HasDerivWithinAt (fun s => M.μ (magnetic (U s))) (p₂ (M.ohmic S σ x + F t)) I t :=
    (p₂.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hd
  refine ⟨?_, ?_⟩
  · convert h₁ using 1
    change _ = M.ε (electric (M.ohmic S σ x) + electric (F t))
    rw [_root_.map_add, ε_electric_ohmic_apply]
  · convert h₂ using 1
    change _ = M.μ (magnetic (M.ohmic S σ x) + magnetic (F t))
    rw [_root_.map_add, μ_magnetic_ohmic_apply]

/-- **Existence and uniqueness of classical solutions** of the Ohmic Maxwell equations, for
data in the domain and admissible forcing (the perturbed semigroup; [QuennevilleBelair2015], Thm 4.3
for semigroup generators). -/
theorem ohmic_existsUnique {U₀ : PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)}
    (hU₀ : U₀ ∈ (M.ohmic S σ).domain) {F : ℝ → PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible (M.ohmic S σ) a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (M.ohmic S σ) (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (M.ohmic S σ) (Icc a b) F V →
        EqOn V U (Icc a b) := by
  refine Evolution.existsUnique_conj_symm (M.state PUnit.{u + 1}) (fun U₀ hU₀ F hF => ?_) hU₀ hF
  rw [← generator_ohmicSemigroup] at hU₀ hF ⊢
  exact (M.ohmicSemigroup S σ).existsUnique_classicalSolution hU₀ hF

/-- **Energy decay**: along a strong solution of the free Ohmic Maxwell equations,
`d/dt ½ (⟪ε E, E⟫ + ⟪μ H, H⟫) = −re ⟪σ E, E⟫`. -/
theorem hasDerivWithinAt_energy {a b : ℝ} {U : ℝ → PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)}
    (hU : Evolution.IsStrongSolution (M.ohmic S σ) (Icc a b) 0 U) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => M.energy (U s))
      (-RCLike.re ⟪σ (electric (U t)), electric (U t)⟫_𝕜) (Icc a b) t := by
  have h := (M.isStrongSolution_ohmic_iff S σ).1 hU
  have hV : Evolution.IsStrongSolution (M.ohmicGen S σ) (Icc a b) 0
      (fun s => M.state PUnit.{u + 1} (U s)) := by
    convert h using 1
    funext s; simp
  have hd := (hV.hasDerivWithinAt_norm_sq ht).div_const 2
  have e : (fun s => M.energy (U s)) = fun s => ‖M.state PUnit.{u + 1} (U s)‖ ^ 2 / 2 :=
    funext fun s => M.energy_eq_norm_state (U s)
  rw [e]
  convert hd using 1
  have hdom := hV.mem_domain ht
  have hsk := (M.isSkewAdjoint_wave_complex (fields S)).isSkewSymmetric.re_inner_self
    ⟨M.state PUnit.{u + 1} (U t), hdom⟩
  change _ = 2 * RCLike.re ⟪-M.loss σ (M.state PUnit.{u + 1} (U t)) +
    (M.complex (fields S)).wave ⟨M.state PUnit.{u + 1} (U t), hdom⟩ + 0,
      M.state PUnit.{u + 1} (U t)⟫_𝕜 / 2
  rw [add_zero, inner_add_left, _root_.map_add, hsk, add_zero, inner_neg_left, _root_.map_neg,
    inner_loss_apply]
  change _ = 2 * -RCLike.re ⟪σ (M.e.symm (M.e (electric (U t)))),
    M.e.symm (M.e (electric (U t)))⟫_𝕜 / 2
  rw [ContinuousLinearEquiv.symm_apply_apply]
  ring

variable {σ}

/-- **The magnetic Gauss law propagates** under Ohmic loss, for every bounded `σ` (no sign
condition): for closed `Y ⊇ R(d₁)` (e.g. `Y = N(d₂)`, `div (μ H) = 0`), strong solutions with
`μ H(t₀) ∈ Y` and forcing with `μ F_H ∈ Y` keep `μ H(t) ∈ Y`. Indeed `(μ H)' = d₁ E + μ F_H ∈ Y`,
so `⟪w, μ H⟫` is constant for every `w ∈ Yᗮ`. -/
theorem ohmic_magnetic_gauss_propagates
    {Y : Submodule 𝕜 W₂} [Y.HasOrthogonalProjection] (hY : ∀ x : S.d₁.domain, S.d₁ x ∈ Y)
    {t₀ t₁ : ℝ} {F U : ℝ → PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)}
    (hU : Evolution.IsStrongSolution (M.ohmic S σ) (Icc t₀ t₁) F U)
    (h0 : M.μ (magnetic (U t₀)) ∈ Y) (hF : ∀ t ∈ Icc t₀ t₁, M.μ (magnetic (F t)) ∈ Y) :
    ∀ t ∈ Icc t₀ t₁, M.μ (magnetic (U t)) ∈ Y := by
  intro t ht
  rw [← Submodule.orthogonal_orthogonal Y, Submodule.mem_orthogonal]
  intro w hw
  -- `q(s) = ⟪w, μ H(s)⟫` has derivative `⟪w, d₁ E + μ F_H⟫ = 0`
  set q : ℝ → 𝕜 := fun s => ⟪w, M.μ (magnetic (U s))⟫_𝕜
  have hq : ∀ s ∈ Icc t₀ t₁, HasDerivWithinAt q 0 (Icc t₀ t₁) s := fun s hs => by
    have h2 := (M.ohmic_equations S σ hU s hs).2
    have := ((innerSL 𝕜 w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt s h2
    refine HasDerivWithinAt.congr_deriv (f := q) this ?_
    change ⟪w, _⟫_𝕜 = 0
    rw [inner_eq_zero_symm]
    exact Submodule.inner_right_of_mem_orthogonal (Y.add_mem (hY _) (hF s hs)) hw
  have hqc : ContinuousOn q (Icc t₀ t₁) := fun s hs => (hq s hs).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hqc fun s hs =>
    ((hq s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs))
  have h1 : q t = q t₀ := hconst t ht
  change q t = 0
  rw [h1, inner_eq_zero_symm]
  exact Submodule.inner_right_of_mem_orthogonal h0 hw

end Medium

end Feec.Maxwell
