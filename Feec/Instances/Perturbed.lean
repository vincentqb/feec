module

public import Feec.Instances.Maxwell
public import Feec.Instances.EinsteinBianchiAbsorbing
public import Feec.Physics.Maxwell.Ohmic

/-!
# Perturbed instances of the FEEC theorem: damping, Ohmic loss, damped absorbing problems

Corollaries of the perturbed FEEC theorem for bounded dissipative perturbations `B` of a
generator, discretized by `Lₕ + Pₕ B ιₕ`.

## Main results

* `damped`: damped waves and damped heat flow.
* `ohmic`: Maxwell's equations with Ohmic loss.
* `absorbing_perturbed`: the damped absorbing problem.
-/

open scoped InnerProductSpace
open Set Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.Instances.Perturbed

open Feec.HilbertComplex

/-! ### Damping and Ohmic loss on the windows of a conforming family -/

section Family

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α] [CharZero α]
  {V : α → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]
  {H : HilbertComplex 𝕜 (ComplexShape.up α) V} {κ : Type*}

theorem re_inner_damping_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {γ : ℝ}
    (hγ : 0 ≤ γ) (x : E) :
    RCLike.re ⟪(-(γ : 𝕜) • ContinuousLinearMap.id 𝕜 E) x, x⟫_𝕜 ≤ 0 := by
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, inner_smul_left,
    inner_self_eq_norm_sq_to_K, map_neg, RCLike.conj_ofReal]
  rw [neg_mul, map_neg, neg_nonpos, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  positivity

/-- **Damped waves and damped heat flow**: on every window of a conforming family, the perturbed
verdict of `ξ' = (L - γ) ξ` and `u' = (-Δ - γ) u`, `γ ≥ 0`. -/
theorem damped (F : ConformingFamily H κ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) {γ : ℝ} (hγ : 0 ≤ γ) :
    (F.windowFEEC a m K hK).PerturbedVerdict
      (-(γ : 𝕜) • ContinuousLinearMap.id 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
      (re_inner_damping_le hγ) :=
  F.feec.perturbed a m K hK _ _

/-- **Ohm's loss** `(E, H) ↦ (-σ E, 0)` on the window `Vᵃ → V^{a+1}`, for a conductivity `σ`. -/
def ohmicLoss (a : α) (σ : V (a + ((0 : Fin 2) : ℕ)) →L[𝕜] V (a + ((0 : Fin 2) : ℕ))) :
    (PiLp 2 fun i : Fin 2 => V (a + i)) →L[𝕜] PiLp 2 fun i : Fin 2 => V (a + i) :=
  PiLp.diagOp (Pi.single 0 (-σ))

omit [IsCancelAdd α] [CharZero α] [∀ i, CompleteSpace (V i)] [∀ i, NormedSpace ℝ (V i)]
  [∀ i, IsScalarTower ℝ 𝕜 (V i)] in
theorem re_inner_ohmicLoss_le {a : α}
    {σ : V (a + ((0 : Fin 2) : ℕ)) →L[𝕜] V (a + ((0 : Fin 2) : ℕ))} (hσ : ∀ E, 0 ≤ RCLike.re ⟪σ E, E⟫_𝕜) (x : PiLp 2 fun i : Fin 2 => V (a + i)) :
    RCLike.re ⟪ohmicLoss a σ x, x⟫_𝕜 ≤ 0 :=
  PiLp.re_inner_diagOp_le (fun i y => by
    fin_cases i
    · simpa [inner_neg_left] using hσ y
    · simp) x

/-- **Maxwell's equations with Ohmic loss** `E' = -d† H - σ E`, `H' = d E`, `re ⟪σ E, E⟫ ≥ 0`, on
every window `Vᵃ → V^{a+1}` of a conforming family: the perturbed verdict. -/
theorem ohmic (F : ConformingFamily H κ) (a : α)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin 2 => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin 2 => V (a + i))))
    {σ : V (a + ((0 : Fin 2) : ℕ)) →L[𝕜] V (a + ((0 : Fin 2) : ℕ))}
    (hσ : ∀ E, 0 ≤ RCLike.re ⟪σ E, E⟫_𝕜) :
    (F.windowFEEC a 2 K hK).PerturbedVerdict (ohmicLoss a σ) (re_inner_ohmicLoss_le hσ) :=
  F.feec.perturbed a 2 K hK _ _

end Family

section Cube

open Models.Cube

variable (n : ℕ) [NeZero n]

/-- **Maxwell's equations with Ohmic loss on the cube**, `⟪σ E, E⟫ ≥ 0`, with the Whitney forms. -/
theorem cube_ohmic (a : ℤ)
    {σ : Domain.L2F ℝ (FEM.cubeDomain n) (Domain.formIdx n (a + ((0 : Fin 2) : ℕ))) →L[ℝ]
      Domain.L2F ℝ (FEM.cubeDomain n) (Domain.formIdx n (a + ((0 : Fin 2) : ℕ)))}
    (hσ : ∀ E, 0 ≤ ⟪σ E, E⟫_ℝ) :
    ((FEM.whitneyFamily n).windowFEEC a 2 ⊤ (by simp)).PerturbedVerdict
      (ohmicLoss (V := fun k => Domain.L2F ℝ (FEM.cubeDomain n) (Domain.formIdx n k)) a σ)
      (re_inner_ohmicLoss_le (V := fun k => Domain.L2F ℝ (FEM.cubeDomain n) (Domain.formIdx n k))
        hσ) :=
  ohmic (FEM.whitneyFamily n) a ⊤ _ hσ

end Cube

/-! ### Ohmic loss in a medium -/

section Medium

open Feec.Maxwell ShortHilbertComplex

universe u

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]
  [NormedSpace ℝ W₁] [IsScalarTower ℝ 𝕜 W₁] [NormedSpace ℝ W₂] [IsScalarTower ℝ 𝕜 W₂]
  (M : Medium 𝕜 W₁ W₂) (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂) {σ : W₁ →L[𝕜] W₁}
  {κ : Type*}

omit [CompleteSpace W₂] [NormedSpace ℝ W₁] [IsScalarTower ℝ 𝕜 W₁] [NormedSpace ℝ W₂]
  [IsScalarTower ℝ 𝕜 W₂] in
theorem re_inner_neg_loss_le (hσ : ∀ E, 0 ≤ RCLike.re ⟪σ E, E⟫_𝕜)
    (x : PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)) : RCLike.re ⟪(-M.loss σ) x, x⟫_𝕜 ≤ 0 := by
  rw [_root_.neg_apply, inner_neg_left, map_neg, neg_nonpos, M.inner_loss_apply]
  exact hσ _

/-- **The Ohmic semigroup is the flow of the perturbed wave discretization** of every constrained
FEEC discretization of the field complex of a medium, for `re ⟪σ E, E⟫ ≥ 0`. -/
theorem _root_.Feec.Maxwell.Medium.ohmicSemigroup_eq_perturb
    (G : ConstrainedFEEC (M.complex (fields S)).toHilbertComplex κ)
    (hσ : ∀ E, 0 ≤ RCLike.re ⟪σ E, E⟫_𝕜) {t : ℝ} (ht : 0 ≤ t) :
    (M.ohmicSemigroup S σ).S t =
      (G.toApprox.perturb (G.wavePerturbation (-M.loss σ) (re_inner_neg_loss_le M hσ))).S t :=
  (C0Semigroup.eqOn_of_generator_eq (G := M.ohmicSemigroup S σ) (by
    rw [LinearPMap.IsMDissipative.generator_semigroup, M.generator_ohmicSemigroup]; rfl) ht).symm

end Medium

/-! ### The damped absorbing problem -/

section Absorbing

open Feec.Models.Cube.Absorbing Feec.Models.Cube.Geometry

variable (B : State →L[ℝ] State) (hB : ∀ x, RCLike.re ⟪B x, x⟫_ℝ ≤ 0)

/-- The perturbation `Lₙ + Pₙ B ιₙ` of the Galerkin scheme of the absorbing problem. -/
abbrev absorbingPerturbation : absorbingGalerkin.Perturbation :=
  ImpedanceTriple.GalerkinData.perturbation tsdPair isClosed_tsdPair approximates_galerkinData B hB

/-- **The damped absorbing problem**: the perturbed verdict for a bounded dissipative term `B`. -/
theorem absorbing_perturbed :
    (absorbingPerturbation B hB).Verdict
      ((absorbingPerturbation B hB).core absorbingGalerkinCore absorbingGalerkin_verdict.1) :=
  ImpedanceTriple.GalerkinData.perturbed_verdict _ _ _ _ _

/-- **With `B = 0`, finite speed of propagation**: the exact flow agrees on the domain of
dependence with every weak solution with the same data. -/
theorem absorbing_perturbed_zero {T : ℝ} {u₀ : State} {W : ℝ → State} (hW : IsWeakRowEB T W)
    (hW0 : W 0 = u₀) {t : ℝ} (ht : t ∈ Icc 0 T) (j : FIdx) :
    ∀ᵐ y ∂MeasureTheory.volume.restrict (Models.BoundedDomain.depDomain (Q (Fin 3)) t),
      toField ((absorbingGalerkin.perturb
        (absorbingPerturbation 0 fun x => by simp)).S t u₀) j y = toField (W t) j y := by
  have e : (absorbingGalerkin.perturb (absorbingPerturbation 0 fun x => by simp)).S t =
      absorbingSemigroup.S t :=
    C0Semigroup.eqOn_of_generator_eq (G := absorbingSemigroup) (by
      rw [LinearPMap.IsMDissipative.generator_semigroup]
      change ((0 : State →L[ℝ] State) : State →ₗ[ℝ] State) +ᵥ Models.Cube.Absorbing.absorbing = _
      rw [ContinuousLinearMap.toLinearMap_zero, zero_vadd]
      exact isMDissipative_absorbing.generator_semigroup.symm) ht.1
  rw [e]
  exact absorbingSemigroup_eq_depDomain hW hW0 ht j

end Absorbing

end Feec.Instances.Perturbed
