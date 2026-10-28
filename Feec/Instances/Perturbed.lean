module

public import Feec.Instances.Maxwell
public import Feec.Instances.EinsteinBianchiAbsorbing
public import Feec.Physics.Maxwell.Ohmic

/-!
# Perturbed instances of the FEEC theorem: damping, Ohmic loss, damped absorbing problems

Corollaries of the field `perturbed` of the FEEC theorem
(`Feec.HilbertComplex.ConformingFamily.Verdict.perturbed`) and of the perturbed FEEC theorem
`Feec.HilbertComplex.perturbFEEC` (bounded dissipative perturbations `B` of a generator, discretized
by `Lₕ + Pₕ B ιₕ`):

* **damped waves** (`damped`): `ξ' = (L - γ) ξ`, `γ ≥ 0`, on every window of every conforming
  family, and the damped heat equation `u' = (-Δ - γ) u`;
* **Maxwell's equations with Ohmic loss** (`ohmic`): on the two-term window `Vᵃ → V^{a+1}` of
  every conforming family, with fields `(E, H)`, the generator `(E, H) ↦ (-d† H - σ E, d E)`
  for a conductivity `σ` on `Vᵃ` with `re ⟪σ E, E⟫ ≥ 0` (`ohmicLoss`); on the de Rham complex
  of a domain of `ℝ³`, `a = 1` is `E' = curl H - σ E`, `H' = -curl E` up to the sign of `H`
  (`Feec.Physics.Maxwell.Ohmic`). The cube with Whitney forms (`cube_ohmic`) is an instance;
* **Ohmic loss in a medium** (`Maxwell.Medium.ohmicSemigroup_eq_perturb`): for every constrained
  FEEC discretization `G` of the field complex of a medium (`Maxwell.Medium.complex`,
  `Maxwell.fields`), the Galerkin perturbation `Lₕ - Pₕ Σ ιₕ`, which has the perturbed verdict
  (`constrainedFEEC_perturbed`), discretizes the Ohmic semigroup `Maxwell.Medium.ohmicSemigroup`
  (generator `L' - Σ`, `Maxwell.Medium.ohmicGen`). The library has no constrained FEEC
  discretization of that field complex yet, so this is a bridge without an instance;
* **the damped absorbing problem** (`absorbing_perturbed`): the linearized Einstein–Bianchi
  system on the cube with the absorbing boundary condition (`Feec.Instances.EinsteinBianchi`) and
  a bounded dissipative lower-order term `B` (e.g. damping), with the dense-sequence Galerkin
  scheme `Lₙ + Pₙ B ιₙ`: the perturbed verdict, whose exact flow is the Dyson–Phillips
  perturbation of the absorbing semigroup (`Feec.Models.Cube.Absorbing.absorbingSemigroup`). With
  `B = 0` the flow is the absorbing semigroup itself, which has finite speed of propagation
  (`absorbing_perturbed_zero`, `Feec.Models.Cube.Absorbing.absorbingSemigroup_eq_depDomain`);
  finite speed of propagation for `B ≠ 0` (a local `B`) is not formalized.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.1 (bounded perturbations), §3.3 (dissipative perturbations), §3.4 (Trotter–Kato)

Bibliography: [references.bib](../../docs/references.bib)
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

/-- The damping `-γ` (`γ ≥ 0`) is dissipative. -/
theorem re_inner_damping_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {γ : ℝ}
    (hγ : 0 ≤ γ) (x : E) :
    RCLike.re ⟪(-(γ : 𝕜) • ContinuousLinearMap.id 𝕜 E) x, x⟫_𝕜 ≤ 0 := by
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, inner_smul_left,
    inner_self_eq_norm_sq_to_K, map_neg, RCLike.conj_ofReal]
  rw [neg_mul, map_neg, neg_nonpos, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  positivity

/-- **Damped waves and damped heat flow**: on every window of a conforming family, with every
closed constraint, `ξ' = (L - γ) ξ` and `u' = (-Δ - γ) u` (`γ ≥ 0`) satisfy the perturbed verdict
with the Galerkin discretizations `Lₕ + Pₕ (-γ) ιₕ`, `-Δₕ + Pₕ (-γ) ιₕ`; these are `Lₕ - γ`,
`-Δₕ - γ`, as `Pₕ ιₕ = ιₕ* ιₕ = 1` for the isometric `ιₕ`. -/
theorem damped (F : ConformingFamily H κ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) {γ : ℝ} (hγ : 0 ≤ γ) :
    (F.windowFEEC a m K hK).PerturbedVerdict
      (-(γ : 𝕜) • ContinuousLinearMap.id 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
      (re_inner_damping_le hγ) :=
  F.feec.perturbed a m K hK _ _

/-- **Ohm's loss** on the two-term window `Vᵃ → V^{a+1}`: `(E, H) ↦ (-σ E, 0)` for a conductivity
`σ` on the electric space `Vᵃ`. -/
def ohmicLoss (a : α) (σ : V (a + ((0 : Fin 2) : ℕ)) →L[𝕜] V (a + ((0 : Fin 2) : ℕ))) :
    (PiLp 2 fun i : Fin 2 => V (a + i)) →L[𝕜] PiLp 2 fun i : Fin 2 => V (a + i) :=
  PiLp.diagOp (Pi.single 0 (-σ))

omit [IsCancelAdd α] [CharZero α] [∀ i, CompleteSpace (V i)] [∀ i, NormedSpace ℝ (V i)]
  [∀ i, IsScalarTower ℝ 𝕜 (V i)] in
/-- Ohm's loss is dissipative for `re ⟪σ E, E⟫ ≥ 0`. -/
theorem re_inner_ohmicLoss_le {a : α}
    {σ : V (a + ((0 : Fin 2) : ℕ)) →L[𝕜] V (a + ((0 : Fin 2) : ℕ))} (hσ : ∀ E, 0 ≤ RCLike.re ⟪σ E, E⟫_𝕜) (x : PiLp 2 fun i : Fin 2 => V (a + i)) :
    RCLike.re ⟪ohmicLoss a σ x, x⟫_𝕜 ≤ 0 :=
  PiLp.re_inner_diagOp_le (fun i y => by
    fin_cases i
    · simpa [inner_neg_left] using hσ y
    · simp) x

/-- **Maxwell's equations with Ohmic loss**: on the two-term window `Vᵃ → V^{a+1}` of a conforming
family, with every closed constraint, the system `E' = -d† H - σ E`, `H' = d E` for a conductivity
with `re ⟪σ E, E⟫ ≥ 0`, discretized by `Lₕ + Pₕ (ohmicLoss σ) ιₕ`, satisfies the perturbed verdict:
the exact flow is the Dyson–Phillips perturbation of the wave group, the discrete flows converge
for every datum, semidiscretely and with every time scheme. -/
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

/-- **Maxwell's equations with Ohmic loss on the cube** `Q = (0, ½)ⁿ` (perfect magnetic
conductor, `n = 3`, `a = 1`: `E ∈ HΛ¹(Q)`, `H ∈ L²Λ²(Q)` in the domain `D(d₁*)`, as the window
drops `d₂`), discretized by the lowest-order Whitney
forms of the Freudenthal meshes (`FEM.whitneyFamily`): the perturbed verdict for every
conductivity `σ` with `⟪σ E, E⟫ ≥ 0` (`ohmic`). -/
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
/-- The conjugated loss `-Σ` of a conductivity with `re ⟪σ E, E⟫ ≥ 0` is dissipative. -/
theorem re_inner_neg_loss_le (hσ : ∀ E, 0 ≤ RCLike.re ⟪σ E, E⟫_𝕜)
    (x : PiLp 2 (W3 PUnit.{u + 1} W₁ W₂)) : RCLike.re ⟪(-M.loss σ) x, x⟫_𝕜 ≤ 0 := by
  rw [_root_.neg_apply, inner_neg_left, map_neg, neg_nonpos, M.inner_loss_apply]
  exact hσ _

/-- **The Ohmic semigroup is the flow of the perturbed wave discretization**: for every
constrained FEEC discretization `G` of the field complex of the medium (`0 → W₁ → W₂`, conjugated
by `ε`, `μ`), the Galerkin perturbation `Lₕ - Pₕ Σ ιₕ` of its wave discretization, which has the
perturbed verdict (`constrainedFEEC_perturbed`), is a discretization of the Ohmic semigroup
(`Maxwell.Medium.ohmicSemigroup`, generated by `L' - Σ`, `Maxwell.Medium.ohmicGen`). -/
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

/-- **The perturbed absorbing scheme**: the Galerkin perturbation `Lₙ + Pₙ B ιₙ` of the
dense-sequence Galerkin scheme of the absorbing problem by a bounded dissipative `B`. -/
abbrev absorbingPerturbation : absorbingGalerkin.Perturbation :=
  ImpedanceTriple.GalerkinData.perturbation tsdPair isClosed_tsdPair approximates_galerkinData B hB

/-- **The damped absorbing problem**: the linearized Einstein–Bianchi system on the cube with the
absorbing boundary condition and a bounded dissipative term `B`, discretized by `Lₙ + Pₙ B ιₙ`,
satisfies the perturbed verdict: its exact flow is the Dyson–Phillips perturbation
`absorbingSemigroup.perturb B` of the absorbing semigroup (`eq_perturb`), with convergence for
every datum, semidiscrete and with every time scheme. -/
theorem absorbing_perturbed :
    (absorbingPerturbation B hB).Verdict
      ((absorbingPerturbation B hB).core absorbingGalerkinCore absorbingGalerkin_verdict.1) :=
  ImpedanceTriple.GalerkinData.perturbed_verdict _ _ _ _ _

/-- **With `B = 0`, finite speed of propagation**: the exact flow of the perturbed absorbing
problem with `B = 0` is the absorbing semigroup, which equals every weak solution of the system
with the same data on the domain of dependence (`absorbingSemigroup_eq_depDomain`). -/
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
