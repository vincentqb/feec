module

public import Feec.HilbertComplex.BGG.Discrete
public import Feec.HilbertComplex.BGG.TimeDependent

/-!
# The elliptic projection (6.4) of the discrete BGG wave system

The thesis defines (§6.2, (6.4)) an elliptic projection of the exact solution of (6.2) onto the
finite element spaces of (6.3): the shifted form "mass + skew form `a` + multiplier `b`",
including the `L²` (mass) term, tested on the discrete spaces. The thesis' formula is garbled
and the projection is never shown to exist or to approximate. This file defines it for
finite-dimensional discrete BGG data (`Feec.BGG.Segment` on the FE spaces, as in
`Feec.BGG.DiscreteSolution`), proves unique solvability, Galerkin orthogonality and, for
discretizations `Feec.BGG.Discrete` of a continuous complex, uniform stability and a Strang
bound.

Correction: (6.4b) as printed, `b(Π − I; ζ) = 0`, prescribes `dΠσ − Sₕ Π̃φ = P_{Vₕ¹}(S − Sₕ)φ`,
which is nonzero in general, so the projected pair would not lie in `Γₕ`. The energy argument of
the convergence proof (`Feec.BGG.norm_sub_le_of_ellipticProjection_L2`) needs it in `Γₕ`; we
impose the homogeneous constraint `dΠσ = Sₕ Π̃φ` (`IsEllipticProjection` allows any right-hand
side `g`).

## Main definitions

* `Feec.BGG.energyInner`: the energy inner product `(σ,τ) + (u,v) + (M,N) + (ρ,μ)`.
* `Feec.BGG.IsEllipticProjection D G g x`: `x = ((σ,u,M,ρ), φ, λ)` solves the shifted system
  with right-hand side `G` and constraint `dσ − S₀φ = g`.
* `Feec.BGG.ellipticForm`, `Feec.BGG.ellipticRhs`, `Feec.BGG.ellipticProjection`: the system
  operator, its right-hand side, and its inverse.
* `Feec.BGG.ellipticData`: the data functional of the exact solution, `⟪ξ, ·⟫ + A(ξ,χ) − ℓ`.
* `Feec.BGG.Discrete.toSegmentH`: the discrete BGG data of a discretization `Q : Discrete D`.
* `Feec.BGG.Discrete.shiftedFormH`, `Feec.BGG.Discrete.shiftedNormSq`: the discrete shifted
  form and the `h`-dependent graph norm `‖σ‖² + ‖u‖² + ‖M‖² + ‖ρ‖² + ‖dφ‖² + ‖Sₕu‖² + ‖du‖²`.

## Main results

* `Feec.BGG.existsUnique_isEllipticProjection`: unique solvability of (6.4) when `d` is
  injective on `Ṽₕ⁰` and `dVₕ⁰ + S₀,ₕṼₕ⁰ = Vₕ¹` (energy argument); in particular under the
  hypotheses `Function.Injective D.dt0`, `Function.Surjective D.S0` of corrected Prop 6.2.
* `Feec.BGG.IsEllipticProjection.galerkin`: Galerkin orthogonality, in the form of the
  hypothesis `hproj` (with `L²` term) of the Ch. 6 convergence theorems.
* `Feec.BGG.hasDerivWithinAt_ellipticProjection`: the projection of time-dependent data is
  differentiable when the data are (weakly) differentiable.
* `Feec.BGG.Discrete.infSup_shiftedForm_h`: the uniform (in `h`) inf-sup condition of the
  discrete shifted form on `Γₕ × Ṽₕ¹ × Vₕ² × Ṽₕ²`, constant `(1/2)/√3`, via the test map
  `x ↦ x + (0, 0, dφ, −Sₕu, −du)`; `Discrete.graphNormSq_le_shiftedNormSq`: it controls the full
  graph norms of `σ, φ`.
* `Feec.BGG.Discrete.strang_shiftedForm_h`, `Feec.BGG.Discrete.strang_ellipticProjection`:
  the Strang bound `‖e‖² ≤ C (interpolation errors + consistency functionals)`, `C` depending on
  the Poincaré constant only; `Discrete.norm_sub_ellipticProjection_le_rate`: the `O(h)` rate.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2 ((6.3), (6.4), Prop 6.2, Prop 6.3), Prop 4.13 (inf-sup by a test map), Thm 5.5
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
  (stability of discrete Hodge Laplacians)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002] (Strang lemma)
* [D. Boffi, F. Brezzi, M. Fortin, *Mixed Finite Element Methods and Applications*][BoffiBrezziFortin2013]
  (saddle-point problems)
* [M. F. Wheeler, *A priori L₂ error estimates for Galerkin approximations to parabolic partial differential equations*][Wheeler1973]
  (elliptic projections in evolution problems)
-/

open scoped RealInnerProductSpace
open Set

@[expose] public noncomputable section

namespace Feec.BGG

/-! ## The elliptic projection for finite-dimensional discrete data -/

section Projection

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]

/-- The energy inner product `(σ,τ) + (u,v) + (M,N) + (ρ,μ)` on `Vₕ⁰ × Ṽₕ¹ × Vₕ² × Ṽₕ²` (the
form `(·;·)` of thesis §6.2). -/
def energyInner (a b : P0 × Pt1 × P2 × Pt2) : ℝ :=
  ⟪a.1, b.1⟫ + ⟪a.2.1, b.2.1⟫ + ⟪a.2.2.1, b.2.2.1⟫ + ⟪a.2.2.2, b.2.2.2⟫

/-- `energyInner a a` is the squared energy norm. -/
theorem energyInner_self (a : P0 × Pt1 × P2 × Pt2) :
    energyInner a a = ‖a.1‖ ^ 2 + ‖a.2.1‖ ^ 2 + ‖a.2.2.1‖ ^ 2 + ‖a.2.2.2‖ ^ 2 := by
  simp only [energyInner, real_inner_self_eq_norm_sq]

/-- The energy inner product is definite. -/
theorem eq_zero_of_energyInner_self {a : P0 × Pt1 × P2 × Pt2} (h : energyInner a a = 0) :
    a = 0 := by
  rw [energyInner_self] at h
  have h1 := sq_nonneg ‖a.1‖; have h2 := sq_nonneg ‖a.2.1‖
  have h3 := sq_nonneg ‖a.2.2.1‖; have h4 := sq_nonneg ‖a.2.2.2‖
  obtain ⟨a1, a2, a3, a4⟩ := a
  simp only [Prod.mk_eq_zero]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 ?_) <;>
    simp only at h1 h2 h3 h4 h <;> linarith

variable (D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2)

/-- **The elliptic projection (6.4)**, corrected: `x = ((σ, u, M, ρ), φ, λ)` solves
`(ξₓ, η) + aₕ(x, y) − (λ, dτ − S₀,ₕψ) = G(y)` for all `y = ((τ, v, N, μ), ψ)`, and
`dσ − S₀,ₕφ = g`. For the projection of an exact solution, `G` is `ellipticData` and `g = 0`.
Correction: the thesis' (6.4) is garbled; its constraint (6.4b) gives a nonzero `g`, which takes
`(σ, φ)` out of `Γₕ` (see the module docstring). See [QuennevilleBelair2015], §6.2, (6.4). -/
def IsEllipticProjection (G : Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0)) (g : P1)
    (x : ((P0 × Pt1 × P2 × Pt2) × Pt0) × P1) : Prop :=
  (∀ y, energyInner x.1.1 y.1 + discreteSkewForm D x.1 y - ⟪x.2, D.d0 y.1.1 - D.S0 y.2⟫ = G y) ∧
    D.d0 x.1.1.1 - D.S0 x.1.2 = g

/-- The system operator of (6.4), as a map to the dual (the last component tests the
constraint). -/
def ellipticForm :
    (((P0 × Pt1 × P2 × Pt2) × Pt0) × P1) →ₗ[ℝ] Module.Dual ℝ (((P0 × Pt1 × P2 × Pt2) × Pt0) × P1) :=
  LinearMap.mk₂ ℝ (fun x y => energyInner x.1.1 y.1.1 + discreteSkewForm D x.1 y.1
      - ⟪x.2, D.d0 y.1.1.1 - D.S0 y.1.2⟫ + ⟪D.d0 x.1.1.1 - D.S0 x.1.2, y.2⟫)
    (by intros; simp only [energyInner, discreteSkewForm, Prod.fst_add, Prod.snd_add, map_add,
          inner_add_left, inner_sub_left, inner_sub_right]; ring)
    (by intros; simp only [energyInner, discreteSkewForm, Prod.smul_fst, Prod.smul_snd, map_smul,
          inner_sub_left, inner_sub_right, real_inner_smul_left, smul_eq_mul]; ring)
    (by intros; simp only [energyInner, discreteSkewForm, Prod.fst_add, Prod.snd_add, map_add,
          inner_add_right, inner_sub_left, inner_sub_right]; ring)
    (by intros; simp only [energyInner, discreteSkewForm, Prod.smul_fst, Prod.smul_snd, map_smul,
          inner_sub_left, inner_sub_right, real_inner_smul_right, smul_eq_mul]; ring)

theorem ellipticForm_apply (x y : ((P0 × Pt1 × P2 × Pt2) × Pt0) × P1) :
    ellipticForm D x y = energyInner x.1.1 y.1.1 + discreteSkewForm D x.1 y.1
      - ⟪x.2, D.d0 y.1.1.1 - D.S0 y.1.2⟫ + ⟪D.d0 x.1.1.1 - D.S0 x.1.2, y.2⟫ := rfl

variable {D}

/-- The right-hand side `y ↦ G(y₁) + (g, ζ)` of (6.4). -/
def ellipticRhs (G : Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0)) (g : P1) :
    Module.Dual ℝ (((P0 × Pt1 × P2 × Pt2) × Pt0) × P1) :=
  G ∘ₗ LinearMap.fst ℝ _ _ + (innerₛₗ ℝ g) ∘ₗ LinearMap.snd ℝ _ _

theorem ellipticRhs_apply (G : Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0)) (g : P1)
    (y : ((P0 × Pt1 × P2 × Pt2) × Pt0) × P1) : ellipticRhs G g y = G y.1 + ⟪g, y.2⟫ := rfl

/-- (6.4) holds iff the system operator maps `x` to the right-hand side. -/
theorem isEllipticProjection_iff {G : Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0)} {g : P1}
    {x : ((P0 × Pt1 × P2 × Pt2) × Pt0) × P1} :
    IsEllipticProjection D G g x ↔ ellipticForm D x = ellipticRhs G g := by
  constructor
  · rintro ⟨h1, h2⟩
    refine LinearMap.ext fun y => ?_
    rw [ellipticForm_apply, ellipticRhs_apply, h1, h2]
  · intro h
    have key := fun y => LinearMap.congr_fun h y
    simp only [ellipticForm_apply, ellipticRhs_apply] at key
    refine ⟨fun y => ?_, ?_⟩
    · simpa using key (y, 0)
    · refine ext_inner_right ℝ fun ζ => ?_
      have := key (0, ζ)
      simpa [energyInner, discreteSkewForm] using this

/-- **Uniqueness for (6.4)** (energy argument, as for the uniqueness in Prop 6.2): with `d`
injective on `Ṽₕ⁰` and `dVₕ⁰ + S₀,ₕṼₕ⁰ = Vₕ¹`, the homogeneous system has only the trivial
solution. Testing with `x` itself gives `(σ, u, M, ρ) = 0` (the skew form vanishes on the
diagonal and the constraint is homogeneous); testing with `v = dφ` gives `dφ = 0`; the
multiplier is then orthogonal to `dVₕ⁰ + S₀,ₕṼₕ⁰`. See [QuennevilleBelair2015], §6.2, Prop 6.2. -/
theorem eq_zero_of_isEllipticProjection (hdinj : Function.Injective D.dt0)
    (hB : ∀ μ : P1, ∃ τ ψ, D.d0 τ - D.S0 ψ = μ)
    {x : ((P0 × Pt1 × P2 × Pt2) × Pt0) × P1} (hx : IsEllipticProjection D 0 0 x) : x = 0 := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨⟨a, q⟩, μ⟩ := x
  simp only [LinearMap.zero_apply] at h1 h2
  have ha : a = 0 := by
    have e := h1 (a, q)
    rw [discreteSkewForm_self, h2, inner_zero_right, add_zero, sub_zero] at e
    exact eq_zero_of_energyInner_self e
  subst ha
  have hq0 : D.S0 q = 0 := by simpa using h2
  have hq : q = 0 := by
    have e := h1 ((0, D.dt0 q, 0, 0), 0)
    simp [energyInner, discreteSkewForm] at e
    exact hdinj (by rw [map_zero]; exact e)
  subst hq
  have hμ : μ = 0 := by
    obtain ⟨τ, ψ, hτψ⟩ := hB μ
    have e := h1 ((τ, 0, 0, 0), ψ)
    simp only [energyInner, discreteSkewForm, hτψ] at e
    simp only [Prod.fst_zero, Prod.snd_zero, inner_zero_left, map_zero, inner_zero_right,
      add_zero, neg_zero, sub_zero, zero_sub, neg_eq_zero] at e
    exact inner_self_eq_zero.1 e
  subst hμ
  rfl

/-- `dVₕ⁰ + S₀,ₕṼₕ⁰ = Vₕ¹` holds when `S₀,ₕ` is onto (thesis hypothesis (5.4)). -/
theorem exists_sub_eq_of_surjective (hS : Function.Surjective D.S0) (μ : P1) :
    ∃ τ ψ, D.d0 τ - D.S0 ψ = μ := by
  obtain ⟨ψ, hψ⟩ := hS (-μ)
  exact ⟨0, ψ, by rw [map_zero, hψ, zero_sub, neg_neg]⟩

variable [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P1] [FiniteDimensional ℝ P2]
  [FiniteDimensional ℝ Pt0] [FiniteDimensional ℝ Pt1] [FiniteDimensional ℝ Pt2]

variable (D) in
/-- The system (6.4) is square: its operator is bijective onto the dual. -/
theorem ellipticForm_bijective (hdinj : Function.Injective D.dt0)
    (hB : ∀ μ : P1, ∃ τ ψ, D.d0 τ - D.S0 ψ = μ) : Function.Bijective (ellipticForm D) := by
  have hinj : Function.Injective (ellipticForm D) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine eq_zero_of_isEllipticProjection hdinj hB (isEllipticProjection_iff.2 ?_)
    rw [hx]; exact LinearMap.ext fun y => by simp [ellipticRhs_apply]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    Subspace.dual_finrank_eq.symm).1 hinj⟩

variable (D) in
/-- **The elliptic projection** `Π : (Eₕ × Vₕ¹)* → Eₕ × Vₕ¹`, the inverse of the system
operator of (6.4). See [QuennevilleBelair2015], §6.2, (6.4). -/
def ellipticProjection (hdinj : Function.Injective D.dt0)
    (hB : ∀ μ : P1, ∃ τ ψ, D.d0 τ - D.S0 ψ = μ) :
    Module.Dual ℝ (((P0 × Pt1 × P2 × Pt2) × Pt0) × P1) ≃ₗ[ℝ]
      (((P0 × Pt1 × P2 × Pt2) × Pt0) × P1) :=
  (LinearEquiv.ofBijective (ellipticForm D) (ellipticForm_bijective D hdinj hB)).symm

/-- The elliptic projection solves (6.4). -/
theorem isEllipticProjection_ellipticProjection (hdinj : Function.Injective D.dt0)
    (hB : ∀ μ : P1, ∃ τ ψ, D.d0 τ - D.S0 ψ = μ)
    (G : Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0)) (g : P1) :
    IsEllipticProjection D G g (ellipticProjection D hdinj hB (ellipticRhs G g)) := by
  rw [isEllipticProjection_iff]
  exact (LinearEquiv.ofBijective (ellipticForm D) (ellipticForm_bijective D hdinj hB)).apply_symm_apply _

/-- Every solution of (6.4) is the elliptic projection. -/
theorem IsEllipticProjection.eq_ellipticProjection (hdinj : Function.Injective D.dt0)
    (hB : ∀ μ : P1, ∃ τ ψ, D.d0 τ - D.S0 ψ = μ)
    {G : Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0)} {g : P1}
    {x : ((P0 × Pt1 × P2 × Pt2) × Pt0) × P1} (hx : IsEllipticProjection D G g x) :
    x = ellipticProjection D hdinj hB (ellipticRhs G g) := by
  rw [isEllipticProjection_iff] at hx
  rw [← hx]
  exact ((LinearEquiv.ofBijective (ellipticForm D)
    (ellipticForm_bijective D hdinj hB)).symm_apply_apply x).symm

/-- **Unique solvability of the elliptic projection (6.4)** (new: the thesis never shows it
well posed). For finite-dimensional discrete data with `d` injective on `Ṽₕ⁰` and
`dVₕ⁰ + S₀,ₕṼₕ⁰ = Vₕ¹`, (6.4) has exactly one solution `((σ, u, M, ρ), φ, λ)` for every
right-hand side `(G, g)`. See [QuennevilleBelair2015], §6.2, (6.4). -/
theorem existsUnique_isEllipticProjection (hdinj : Function.Injective D.dt0)
    (hB : ∀ μ : P1, ∃ τ ψ, D.d0 τ - D.S0 ψ = μ)
    (G : Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0)) (g : P1) :
    ∃! x, IsEllipticProjection D G g x :=
  ⟨_, isEllipticProjection_ellipticProjection hdinj hB G g,
    fun _ hx => hx.eq_ellipticProjection hdinj hB⟩

/-- Unique solvability of (6.4) under the hypotheses of the corrected Prop 6.2
(`d` injective on `Ṽₕ⁰`, `S₀,ₕ` onto). -/
theorem existsUnique_isEllipticProjection_of_surjective (hdinj : Function.Injective D.dt0)
    (hS : Function.Surjective D.S0) (G : Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0)) (g : P1) :
    ∃! x, IsEllipticProjection D G g x :=
  existsUnique_isEllipticProjection hdinj (exists_sub_eq_of_surjective hS) G g

/-- Time derivative of the elliptic projection: if the data `G(s)` are differentiable when
evaluated on every test function, then so is `Π(G(s), 0)`, with derivative `Π(G'(t), 0)`
(finite dimensions: expand `G(s)` in a dual basis). -/
theorem hasDerivWithinAt_ellipticProjection (hdinj : Function.Injective D.dt0)
    (hB : ∀ μ : P1, ∃ τ ψ, D.d0 τ - D.S0 ψ = μ)
    {G G' : ℝ → Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0)} {s : Set ℝ} {t : ℝ}
    (hG : ∀ y, HasDerivWithinAt (fun r => G r y) (G' t y) s t) :
    HasDerivWithinAt (fun r => ellipticProjection D hdinj hB (ellipticRhs (G r) 0))
      (ellipticProjection D hdinj hB (ellipticRhs (G' t) 0)) s t := by
  classical
  set b := Module.finBasis ℝ (((P0 × Pt1 × P2 × Pt2) × Pt0) × P1)
  have hexp : ∀ H : Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0),
      ellipticProjection D hdinj hB (ellipticRhs H 0) =
        ∑ i, ellipticRhs H 0 (b i) • ellipticProjection D hdinj hB (b.coord i) := by
    intro H
    conv_lhs => rw [← b.sum_dual_apply_smul_coord (ellipticRhs H 0)]
    simp only [map_sum, map_smul]
  simp only [hexp]
  refine HasDerivWithinAt.fun_sum fun i _ => (HasDerivWithinAt.smul_const ?_ _)
  simpa [ellipticRhs_apply] using hG (b i).1

/-- Continuity of the elliptic projection of continuous data. -/
theorem continuousOn_ellipticProjection (hdinj : Function.Injective D.dt0)
    (hB : ∀ μ : P1, ∃ τ ψ, D.d0 τ - D.S0 ψ = μ)
    {G : ℝ → Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0)} {s : Set ℝ}
    (hG : ∀ y, ContinuousOn (fun r => G r y) s) :
    ContinuousOn (fun r => ellipticProjection D hdinj hB (ellipticRhs (G r) 0)) s := by
  classical
  set b := Module.finBasis ℝ (((P0 × Pt1 × P2 × Pt2) × Pt0) × P1)
  have hexp : ∀ H : Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0),
      ellipticProjection D hdinj hB (ellipticRhs H 0) =
        ∑ i, ellipticRhs H 0 (b i) • ellipticProjection D hdinj hB (b.coord i) := by
    intro H
    conv_lhs => rw [← b.sum_dual_apply_smul_coord (ellipticRhs H 0)]
    simp only [map_sum, map_smul]
  simp only [hexp]
  refine continuousOn_finsetSum _ fun i _ => ContinuousOn.fun_smul ?_ continuousOn_const
  simpa [ellipticRhs_apply] using hG (b i).1

end Projection

/-! ## Galerkin orthogonality in the setting of the Ch. 6 convergence theorems -/

section Galerkin

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [AddCommGroup Z] [Module ℝ Z]

/-- **The data functional of the elliptic projection of an exact state** `(ξ, χ)` with
multiplier functional `ℓ`: `G(b, ψ) = ⟪ξ, ι b⟫ + A(ξ, χ)(ι b, j ψ) − ℓ(ι b, j ψ)`, i.e. the
continuous shifted form (mass + skew + multiplier) tested on discrete functions, in the setting
of `DiscreteSolution.norm_sub_le_of_ellipticProjection`. -/
def ellipticData (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X) (j : Pt0 →ₗ[ℝ] Z)
    (A : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (ξ : X) (χ : Z) (ℓ : (X × Z) →ₗ[ℝ] ℝ) :
    Module.Dual ℝ ((P0 × Pt1 × P2 × Pt2) × Pt0) :=
  (innerₛₗ ℝ ξ) ∘ₗ (ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X) ∘ₗ LinearMap.fst ℝ _ _ +
    (A (ξ, χ) - ℓ) ∘ₗ ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j)

theorem ellipticData_apply (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X) (j : Pt0 →ₗ[ℝ] Z)
    (A : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (ξ : X) (χ : Z) (ℓ : (X × Z) →ₗ[ℝ] ℝ)
    (y : (P0 × Pt1 × P2 × Pt2) × Pt0) :
    ellipticData ι j A ξ χ ℓ y = ⟪ξ, ι y.1⟫ + A (ξ, χ) (ι y.1, j y.2) - ℓ (ι y.1, j y.2) := by
  simp [ellipticData]; ring

/-- **Galerkin orthogonality of the elliptic projection (6.4).** In the setting of
`DiscreteSolution.norm_sub_le_of_ellipticProjection` (energy-preserving embedding `ι`, discrete
forms `hAh`, `hBh`), a solution `((a, q), μ)` of (6.4) with data `ellipticData … ξ χ ℓ` and
homogeneous constraint satisfies `Bₕ(ι a, j q) = 0` and, for every discrete `η`,
`⟪ι a, η₁⟫ + Aₕ((ι a, j q), η) − ⟪μ, Bₕη⟫ = ⟪ξ, η₁⟫ + A((ξ, χ), η) − ℓ η`
(the shifted error form vanishes on the discrete space): these are the hypotheses `hPB`, `hproj`
of `norm_sub_le_of_ellipticProjection_L2`. See [QuennevilleBelair2015], §6.2, (6.4). -/
theorem IsEllipticProjection.galerkin {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X)
    (hι : ∀ a b, ⟪ι a, ι b⟫ = ⟪a.1, b.1⟫ + ⟪a.2.1, b.2.1⟫ + ⟪a.2.2.1, b.2.2.1⟫ +
      ⟪a.2.2.2, b.2.2.2⟫)
    (j : Pt0 →ₗ[ℝ] Z) (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] P1)
    (hAh : ∀ a φ b ψ, Ah (ι a, j φ) (ι b, j ψ) = discreteSkewForm D (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (ι a, j ψ) = D.d0 a.1 - D.S0 ψ) (ξ : X) (χ : Z) (ℓ : (X × Z) →ₗ[ℝ] ℝ)
    {x : ((P0 × Pt1 × P2 × Pt2) × Pt0) × P1}
    (hx : IsEllipticProjection D (ellipticData ι j A ξ χ ℓ) 0 x) :
    Bh (ι x.1.1, j x.1.2) = 0 ∧
      ∀ η ∈ LinearMap.range ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
        ⟪ι x.1.1, η.1⟫ + Ah (ι x.1.1, j x.1.2) η - ⟪x.2, Bh η⟫ =
          ⟪ξ, η.1⟫ + A (ξ, χ) η - ℓ η := by
  refine ⟨by rw [hBh]; exact hx.2, ?_⟩
  rintro η ⟨⟨b, ψ⟩, rfl⟩
  have h := hx.1 (b, ψ)
  rw [ellipticData_apply] at h
  simp only [LinearMap.prodMap_apply, ContinuousLinearMap.coe_coe, hι, hAh, hBh]
  rw [← h, energyInner]

end Galerkin

/-! ## Uniform stability and a Strang bound for discretizations `Q : Discrete D` -/

namespace Discrete

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} (Q : Discrete D)

/-- The discrete shifted form of (6.4) on `Γₕ`-tests (the multiplier term drops out):
mass `(σ,τ) + (u,v) + (M,N) + (ρ,μ)` plus the skew form `aₕ` of §6.2 with `S₁,ₕ`. -/
def shiftedFormH (σ : V0) (φ : Vt0) (u : Vt1) (M : W2) (ρ : Wt2)
    (τ : V0) (ψ : Vt0) (v : Vt1) (N : W2) (μ : Wt2) : ℝ :=
  ⟪σ, τ⟫ + ⟪u, v⟫ + ⟪M, N⟫ + ⟪ρ, μ⟫ - ⟪u, D.dt0 ψ⟫ + ⟪D.dt0 φ, v⟫ + ⟪M, Q.S1h v⟫
    + ⟪ρ, D.dt1 v⟫ - ⟪Q.S1h u, N⟫ - ⟪D.dt1 u, μ⟫

variable (D) in
/-- The continuous shifted form (mass plus the skew form `a` of §6.2, with `S₁`). -/
def shiftedFormC (σ : V0) (φ : Vt0) (u : Vt1) (M : W2) (ρ : Wt2)
    (τ : V0) (ψ : Vt0) (v : Vt1) (N : W2) (μ : Wt2) : ℝ :=
  ⟪σ, τ⟫ + ⟪u, v⟫ + ⟪M, N⟫ + ⟪ρ, μ⟫ - ⟪u, D.dt0 ψ⟫ + ⟪D.dt0 φ, v⟫ + ⟪M, D.S1 v⟫
    + ⟪ρ, D.dt1 v⟫ - ⟪D.S1 u, N⟫ - ⟪D.dt1 u, μ⟫

/-- The `h`-dependent graph norm (squared) of the discrete shifted form:
`‖σ‖² + ‖u‖² + ‖M‖² + ‖ρ‖² + ‖dφ‖² + ‖S₁,ₕu‖² + ‖du‖²`. On `Γₕ` it controls the full graph
norms (`graphNormSq_le_shiftedNormSq`). -/
def shiftedNormSq (σ : V0) (φ : Vt0) (u : Vt1) (M : W2) (ρ : Wt2) : ℝ :=
  ‖σ‖ ^ 2 + ‖u‖ ^ 2 + ‖M‖ ^ 2 + ‖ρ‖ ^ 2 + ‖D.dt0 φ‖ ^ 2 + ‖Q.S1h u‖ ^ 2 + ‖D.dt1 u‖ ^ 2

theorem shiftedNormSq_nonneg (σ : V0) (φ : Vt0) (u : Vt1) (M : W2) (ρ : Wt2) :
    0 ≤ Q.shiftedNormSq σ φ u M ρ := by unfold shiftedNormSq; positivity

variable {Q}

/-- `S₁,ₕ dφ = 0` on `Γₕ`. -/
theorem S1h_dt0_eq_zero {σ : V0} {φ : Vt0} (hΓ : D.d0 σ = Q.S0h φ) : Q.S1h (D.dt0 φ) = 0 := by
  have := Q.anticomm_h φ
  rw [← hΓ, D.d1_d0] at this
  exact neg_eq_zero.1 this.symm

/-- The coercivity identity of the test map `x ↦ x + (0, 0, dφ, −S₁,ₕu, −du)` on `Γₕ`. -/
theorem shiftedFormH_test {σ : V0} {φ : Vt0} (u : Vt1) (M : W2) (ρ : Wt2)
    (hΓ : D.d0 σ = Q.S0h φ) :
    Q.shiftedFormH σ φ u M ρ σ φ (u + D.dt0 φ) (M - Q.S1h u) (ρ - D.dt1 u) =
      Q.shiftedNormSq σ φ u M ρ + ⟪D.dt0 φ, u⟫ - ⟪Q.S1h u, M⟫ - ⟪D.dt1 u, ρ⟫ := by
  have hS := S1h_dt0_eq_zero hΓ
  simp only [shiftedFormH, shiftedNormSq, map_add, hS, D.dt1_dt0, add_zero, inner_add_right,
    inner_sub_right, real_inner_self_eq_norm_sq]
  have c1 := real_inner_comm u (D.dt0 φ)
  have c2 := real_inner_comm M (Q.S1h u)
  have c3 := real_inner_comm ρ (D.dt1 u)
  linarith

/-- The test map is bounded: `‖x + (0, 0, dφ, −S₁,ₕu, −du)‖² ≤ 3 ‖x‖²` (shifted norm). -/
theorem shiftedNormSq_test_le {σ : V0} {φ : Vt0} (u : Vt1) (M : W2) (ρ : Wt2)
    (hΓ : D.d0 σ = Q.S0h φ) :
    Q.shiftedNormSq σ φ (u + D.dt0 φ) (M - Q.S1h u) (ρ - D.dt1 u) ≤
      3 * Q.shiftedNormSq σ φ u M ρ := by
  have hS := S1h_dt0_eq_zero hΓ
  simp only [shiftedNormSq, map_add, hS, D.dt1_dt0, add_zero]
  nlinarith [norm_add_sq_le_two_mul u (D.dt0 φ), norm_sub_sq_le_two_mul M (Q.S1h u),
    norm_sub_sq_le_two_mul ρ (D.dt1 u), sq_nonneg ‖σ‖, sq_nonneg ‖u‖, sq_nonneg ‖M‖,
    sq_nonneg ‖ρ‖, sq_nonneg ‖D.dt0 φ‖, sq_nonneg ‖Q.S1h u‖, sq_nonneg ‖D.dt1 u‖]

/-- The coercivity bound `‖x‖²/2 ≤ Aₕ(x, x + (0, 0, dφ, −S₁,ₕu, −du))` on `Γₕ`. -/
theorem shiftedNormSq_le_shiftedFormH_test {σ : V0} {φ : Vt0} (u : Vt1) (M : W2) (ρ : Wt2)
    (hΓ : D.d0 σ = Q.S0h φ) :
    Q.shiftedNormSq σ φ u M ρ / 2 ≤
      Q.shiftedFormH σ φ u M ρ σ φ (u + D.dt0 φ) (M - Q.S1h u) (ρ - D.dt1 u) := by
  rw [shiftedFormH_test u M ρ hΓ]
  have e1 : -⟪D.dt0 φ, u⟫ ≤ ‖D.dt0 φ‖ * ‖u‖ := (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have e2 := real_inner_le_norm (Q.S1h u) M
  have e3 := real_inner_le_norm (D.dt1 u) ρ
  unfold shiftedNormSq
  nlinarith [sq_nonneg (‖D.dt0 φ‖ - ‖u‖), sq_nonneg (‖Q.S1h u‖ - ‖M‖),
    sq_nonneg (‖D.dt1 u‖ - ‖ρ‖), sq_nonneg ‖σ‖]

/-- **Uniform (in `h`) inf-sup condition of the discrete shifted form** on
`Kₕ = Γₕ × Ṽₕ¹ × Vₕ² × Ṽₕ²` in the `h`-dependent graph norm `shiftedNormSq`: every
`x ∈ Kₕ` has a test `y ∈ Kₕ` with `‖y‖ ≤ √3 ‖x‖` and `Aₕ(x, y) ≥ ((1/2)/√3) ‖x‖ ‖y‖`
(and `Aₕ(x, y) ≥ ‖x‖²/2`). The constant `(1/2)/√3` is that of `HodgeWave.infSup_shiftedForm`
(thesis Prop 4.13); the test map `x ↦ x + (0, 0, dφ, −S₁,ₕu, −du)` stays in `Kₕ` because `Kₕ` is
a subcomplex and `S₁,ₕ dφ = 0` on `Γₕ`. No uniform bound on the projections is needed.
See [QuennevilleBelair2015], Prop 4.13 and §6.2; cf. [AFW2010]. -/
theorem infSup_shiftedForm_h {σ : V0} {φ : Vt0} {u : Vt1} {M : W2} {ρ : Wt2}
    (hσ : σ ∈ Q.V0h) (hφ : φ ∈ Q.Vt0h) (hΓ : D.d0 σ = Q.S0h φ) (hu : u ∈ Q.Vt1h)
    (hM : M ∈ Q.W2h) (hρ : ρ ∈ Q.Wt2h) :
    ∃ τ ∈ Q.V0h, ∃ ψ ∈ Q.Vt0h, D.d0 τ = Q.S0h ψ ∧ ∃ v ∈ Q.Vt1h, ∃ N ∈ Q.W2h, ∃ μ ∈ Q.Wt2h,
      Q.shiftedNormSq τ ψ v N μ ≤ 3 * Q.shiftedNormSq σ φ u M ρ ∧
      Q.shiftedNormSq σ φ u M ρ / 2 ≤ Q.shiftedFormH σ φ u M ρ τ ψ v N μ ∧
      (1 / 2) / √3 * √(Q.shiftedNormSq σ φ u M ρ) * √(Q.shiftedNormSq τ ψ v N μ) ≤
        Q.shiftedFormH σ φ u M ρ τ ψ v N μ := by
  refine ⟨σ, hσ, φ, hφ, hΓ, u + D.dt0 φ, Submodule.add_mem _ hu (Q.dt0_mem _ hφ),
    M - Q.S1h u, Submodule.sub_mem _ hM (Q.S1h_mem u), ρ - D.dt1 u,
    Submodule.sub_mem _ hρ (Q.dt1_mem _ hu), shiftedNormSq_test_le u M ρ hΓ,
    shiftedNormSq_le_shiftedFormH_test u M ρ hΓ, ?_⟩
  refine le_trans ?_ (shiftedNormSq_le_shiftedFormH_test u M ρ hΓ)
  set a := Q.shiftedNormSq σ φ u M ρ
  have ha := Q.shiftedNormSq_nonneg σ φ u M ρ
  have hy : √(Q.shiftedNormSq σ φ (u + D.dt0 φ) (M - Q.S1h u) (ρ - D.dt1 u)) ≤ √3 * √a := by
    rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt (shiftedNormSq_test_le u M ρ hΓ)
  have h3 : (0 : ℝ) < √3 := by positivity
  calc (1 / 2) / √3 * √a * √(Q.shiftedNormSq σ φ (u + D.dt0 φ) (M - Q.S1h u) (ρ - D.dt1 u))
      ≤ (1 / 2) / √3 * √a * (√3 * √a) := by gcongr
    _ = a / 2 := by
        rw [show (1 / 2) / √3 * √a * (√3 * √a) = (1 / 2) * (√a * √a) * (√3 / √3) by ring,
          div_self h3.ne', Real.mul_self_sqrt ha]; ring

/-- On `Γₕ` the shifted norm controls the full `h`-dependent graph norm
`‖σ‖_V² + ‖φ‖_V² + ‖u‖_{Γₕ}² + ‖M‖² + ‖ρ‖²`, uniformly in `h` (discrete Poincaré inequality
`poincare_Γh`, thesis Prop 5.3(a), and `poinct0`). -/
theorem graphNormSq_le_shiftedNormSq {Cp CR CS CP : ℝ} (H : Stability D Cp CR CS)
    (B : Q.Bounded CP) {σ : V0} {φ : Vt0} (u : Vt1) (M : W2) (ρ : Wt2)
    (hΓ : D.d0 σ = Q.S0h φ) :
    graphSq D.d0 σ + graphSq D.dt0 φ + Q.gnSq u + ‖M‖ ^ 2 + ‖ρ‖ ^ 2 ≤
      (Ca Cp CS CP ^ 2 + Cp ^ 2 + 2) * Q.shiftedNormSq σ φ u M ρ := by
  have h1 := poincare_Γh H B hΓ
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (H.poinct0 φ) 2
  rw [mul_pow] at h2
  have hn := Q.shiftedNormSq_nonneg σ φ u M ρ
  have hd : ‖D.dt0 φ‖ ^ 2 ≤ Q.shiftedNormSq σ φ u M ρ := by
    unfold shiftedNormSq; nlinarith [sq_nonneg ‖σ‖, sq_nonneg ‖u‖, sq_nonneg ‖M‖, sq_nonneg ‖ρ‖,
      sq_nonneg ‖Q.S1h u‖, sq_nonneg ‖D.dt1 u‖]
  have hca := mul_le_mul_of_nonneg_left hd (sq_nonneg (Ca Cp CS CP))
  have hcp := mul_le_mul_of_nonneg_left hd (sq_nonneg Cp)
  unfold graphSq gnSq
  unfold graphSq at h1
  unfold shiftedNormSq at hn hd hca hcp ⊢
  nlinarith [sq_nonneg ‖σ‖, sq_nonneg ‖u‖, sq_nonneg ‖M‖, sq_nonneg ‖ρ‖,
      sq_nonneg ‖Q.S1h u‖, sq_nonneg ‖D.dt1 u‖, sq_nonneg ‖D.dt0 φ‖]

/-- The constant of the Strang bound, depending on the Poincaré constant only. -/
def strangConst (Cp : ℝ) : ℝ := 112 * (2 + Cp ^ 2)

/-- The data of the Strang bound: interpolation errors of the exact state by the cochain
projections (in the graph norms that the shifted form sees), the consistency constants
`K₀, K₁` of the functionals `ψ ↦ ℓ((S₀ − S₀,ₕ)ψ)`, `v ↦ ⟪M, (S₁ − S₁,ₕ)v⟫`, and
`‖(S₁ − S₁,ₕ)u‖`. -/
def strangData (σ : V0) (φ : Vt0) (u : Vt1) (M : W2) (ρ : Wt2) (K0 K1 : ℝ) : ℝ :=
  ‖Q.P0 σ - σ‖ ^ 2 + ‖D.dt0 (Q.Pt0 φ - φ)‖ ^ 2 + Q.gnSq (Q.Pt1 u - u) + ‖Q.P2 M - M‖ ^ 2
    + ‖Q.Pt2 ρ - ρ‖ ^ 2 + K0 ^ 2 + K1 ^ 2 + ‖D.S1 u - Q.S1h u‖ ^ 2

variable (Q) in
theorem strangData_nonneg (σ : V0) (φ : Vt0) (u : Vt1) (M : W2) (ρ : Wt2) (K0 K1 : ℝ) :
    0 ≤ Q.strangData σ φ u M ρ K0 K1 := by
  unfold strangData; have := Q.gnSq_nonneg (Q.Pt1 u - u); positivity

/-- **Strang bound for the elliptic projection (6.4)** of a discretization `Q : Discrete D`
(new: the thesis states no approximation property of (6.4)). Let `(σ, φ, u, M, ρ)` be an exact
state with `dσ = S₀φ`, `ℓ` its multiplier functional, and `(σₚ, φₚ, uₚ, Mₚ, ρₚ)` discrete with
`dσₚ = S₀,ₕφₚ` and `Aₕ(xₚ, y) = A(x, y) − ℓ(dτ − S₀ψ)` for all `y ∈ Kₕ` (this is what (6.4)
gives on `Γₕ`-tests, where the discrete multiplier drops out). With the consistency bounds
`|ℓ((S₀ − S₀,ₕ)ψ)| ≤ K₀ ‖ψ‖_V`, `|⟪M, (S₁ − S₁,ₕ)v⟫| ≤ K₁ ‖v‖_{Γₕ}`, the discrete error
`e = xₚ − Πx` satisfies `‖e‖²_shifted ≤ strangConst C_p · strangData`, with a constant that
depends on the Poincaré constant only. Uses the inf-sup test map of `infSup_shiftedForm_h`
and (5.4) (`Compatible`) to place `Πx` in `Kₕ`.
See [QuennevilleBelair2015], §6.2, (6.4), Prop 6.3; cf. Strang's lemma [Ciarlet2002]. -/
theorem strang_shiftedForm_h {Cp CR CS : ℝ} (H : Stability D Cp CR CS) (h54 : Q.Compatible)
    {σ : V0} {φ : Vt0} {u : Vt1} {M : W2} {ρ : Wt2} (c3 : D.d0 σ = D.S0 φ)
    (ℓ : V1 →ₗ[ℝ] ℝ) {K0 K1 : ℝ}
    (hK0 : ∀ ψ ∈ Q.Vt0h, |ℓ ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ v ∈ Q.Vt1h, |⟪M, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    {σP : V0} {φP : Vt0} {uP : Vt1} {MP : W2} {ρP : Wt2}
    (hσP : σP ∈ Q.V0h) (hφP : φP ∈ Q.Vt0h) (huP : uP ∈ Q.Vt1h) (hMP : MP ∈ Q.W2h)
    (hρP : ρP ∈ Q.Wt2h) (hcons : D.d0 σP = Q.S0h φP)
    (heq : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, D.d0 τ = Q.S0h ψ → ∀ v ∈ Q.Vt1h, ∀ N ∈ Q.W2h,
      ∀ μ ∈ Q.Wt2h, Q.shiftedFormH σP φP uP MP ρP τ ψ v N μ =
        shiftedFormC D σ φ u M ρ τ ψ v N μ - ℓ (D.d0 τ - D.S0 ψ)) :
    Q.shiftedNormSq (σP - Q.P0 σ) (φP - Q.Pt0 φ) (uP - Q.Pt1 u) (MP - Q.P2 M) (ρP - Q.Pt2 ρ)
      ≤ strangConst Cp * Q.strangData σ φ u M ρ K0 K1 := by
  have hp := H.Cp_nonneg
  -- the discrete error `e = xₚ − Πx ∈ Kₕ`
  set eσ := σP - Q.P0 σ with heσ
  set eφ := φP - Q.Pt0 φ with heφ
  set eu := uP - Q.Pt1 u with heu
  set eM := MP - Q.P2 M with heM
  set eρ := ρP - Q.Pt2 ρ with heρ
  have heσm : eσ ∈ Q.V0h := Submodule.sub_mem _ hσP (Q.P0_mem σ)
  have heφm : eφ ∈ Q.Vt0h := Submodule.sub_mem _ hφP (Q.Pt0_mem φ)
  have heum : eu ∈ Q.Vt1h := Submodule.sub_mem _ huP (Q.Pt1_mem u)
  have heMm : eM ∈ Q.W2h := Submodule.sub_mem _ hMP (Q.P2_mem M)
  have heρm : eρ ∈ Q.Wt2h := Submodule.sub_mem _ hρP (Q.Pt2_mem ρ)
  have hΓe : D.d0 eσ = Q.S0h eφ := by
    rw [heσ, heφ, map_sub, map_sub, Q.comm0, c3, hcons, S0h_apply, S0h_apply, h54]
  have hSe := S1h_dt0_eq_zero hΓe
  -- the test function
  set v := eu + D.dt0 eφ with hv
  set N := eM - Q.S1h eu with hN
  set μ := eρ - D.dt1 eu with hμ
  have hvm : v ∈ Q.Vt1h := Submodule.add_mem _ heum (Q.dt0_mem _ heφm)
  have hNm : N ∈ Q.W2h := Submodule.sub_mem _ heMm (Q.S1h_mem eu)
  have hμm : μ ∈ Q.Wt2h := Submodule.sub_mem _ heρm (Q.dt1_mem _ heum)
  have hSv : Q.S1h v = Q.S1h eu := by rw [hv, map_add, hSe, add_zero]
  have hdv : D.dt1 v = D.dt1 eu := by rw [hv, map_add, D.dt1_dt0, add_zero]
  -- the residual
  have hE := heq eσ heσm eφ heφm hΓe v hvm N hNm μ hμm
  have hres : Q.shiftedFormH eσ eφ eu eM eρ eσ eφ v N μ =
      ⟪σ - Q.P0 σ, eσ⟫ + ⟪u - Q.Pt1 u, v⟫ - ⟪u - Q.Pt1 u, D.dt0 eφ⟫ + ⟪M - Q.P2 M, N⟫
      + ⟪M - Q.P2 M, Q.S1h v⟫ + ⟪ρ - Q.Pt2 ρ, μ⟫ + ⟪ρ - Q.Pt2 ρ, D.dt1 v⟫
      + ⟪D.dt0 (φ - Q.Pt0 φ), v⟫ + ⟪M, (D.S1 - Q.S1h) v⟫ - ⟪(D.S1 - Q.S1h) u, N⟫
      - ⟪Q.S1h (u - Q.Pt1 u), N⟫ - ⟪D.dt1 (u - Q.Pt1 u), μ⟫ + ℓ ((D.S0 - Q.S0h) eφ) := by
    have hlin : Q.shiftedFormH eσ eφ eu eM eρ eσ eφ v N μ =
        Q.shiftedFormH σP φP uP MP ρP eσ eφ v N μ -
          Q.shiftedFormH (Q.P0 σ) (Q.Pt0 φ) (Q.Pt1 u) (Q.P2 M) (Q.Pt2 ρ) eσ eφ v N μ := by
      simp only [shiftedFormH, heσ, heφ, heu, heM, heρ, map_sub, inner_sub_left]; ring
    rw [hlin, hE, hΓe]
    simp only [shiftedFormC, shiftedFormH, map_sub, LinearMap.sub_apply, inner_sub_left,
      inner_sub_right]
    ring
  -- coercivity
  have hcoer := shiftedNormSq_le_shiftedFormH_test eu eM eρ hΓe
  -- term-by-term bounds
  set n2 := Q.shiftedNormSq eσ eφ eu eM eρ with hn2
  have hn0 : 0 ≤ n2 := Q.shiftedNormSq_nonneg _ _ _ _ _
  have hns : ‖eσ‖ ^ 2 + ‖eu‖ ^ 2 + ‖eM‖ ^ 2 + ‖eρ‖ ^ 2 + ‖D.dt0 eφ‖ ^ 2 + ‖Q.S1h eu‖ ^ 2
      + ‖D.dt1 eu‖ ^ 2 = n2 := rfl
  have s1 := sq_nonneg ‖eσ‖; have s2 := sq_nonneg ‖eu‖; have s3 := sq_nonneg ‖eM‖
  have s4 := sq_nonneg ‖eρ‖; have s5 := sq_nonneg ‖D.dt0 eφ‖; have s6 := sq_nonneg ‖Q.S1h eu‖
  have s7 := sq_nonneg ‖D.dt1 eu‖
  set K := 2 + Cp ^ 2 with hK
  have hK0' : 0 < K := by positivity
  have hKn : ∀ {a : ℝ}, a ≤ 2 * n2 → a ≤ K * n2 := fun h =>
    h.trans (mul_le_mul_of_nonneg_right (by nlinarith) hn0)
  have hv2 : ‖v‖ ^ 2 ≤ K * n2 := hKn (by
    have := norm_add_sq_le_two_mul eu (D.dt0 eφ); linarith)
  have hN2 : ‖N‖ ^ 2 ≤ K * n2 := hKn (by
    have := norm_sub_sq_le_two_mul eM (Q.S1h eu); linarith)
  have hμ2 : ‖μ‖ ^ 2 ≤ K * n2 := hKn (by
    have := norm_sub_sq_le_two_mul eρ (D.dt1 eu); linarith)
  have hτ2 : ‖eσ‖ ^ 2 ≤ K * n2 := hKn (by linarith)
  have hdψ2 : ‖D.dt0 eφ‖ ^ 2 ≤ K * n2 := hKn (by linarith)
  have hSv2 : ‖Q.S1h v‖ ^ 2 ≤ K * n2 := hKn (by rw [hSv]; linarith)
  have hdv2 : ‖D.dt1 v‖ ^ 2 ≤ K * n2 := hKn (by rw [hdv]; linarith)
  have hgv2 : √(Q.gnSq v) ^ 2 ≤ K * n2 := by
    rw [Real.sq_sqrt (Q.gnSq_nonneg v)]
    refine hKn ?_
    unfold gnSq; rw [hSv, hdv]
    have := norm_add_sq_le_two_mul eu (D.dt0 eφ); linarith
  have hgψ2 : √(graphSq D.dt0 eφ) ^ 2 ≤ K * n2 := by
    rw [Real.sq_sqrt (graphSq_nonneg _ _)]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (H.poinct0 eφ) 2
    rw [mul_pow] at h2
    have := mul_le_mul_of_nonneg_left (show ‖D.dt0 eφ‖ ^ 2 ≤ n2 by linarith) (sq_nonneg Cp)
    unfold graphSq; nlinarith
  -- the data
  set rσ := ‖Q.P0 σ - σ‖
  set ru := ‖Q.Pt1 u - u‖
  set rM := ‖Q.P2 M - M‖
  set rρ := ‖Q.Pt2 ρ - ρ‖
  set rφ := ‖D.dt0 (Q.Pt0 φ - φ)‖
  set rS := ‖D.S1 u - Q.S1h u‖
  set rSu := ‖Q.S1h (Q.Pt1 u - u)‖
  set rdu := ‖D.dt1 (Q.Pt1 u - u)‖
  have b1 : ⟪σ - Q.P0 σ, eσ⟫ ≤ rσ * ‖eσ‖ := (real_inner_le_norm _ _).trans_eq (by rw [norm_sub_rev])
  have b2 : ⟪u - Q.Pt1 u, v⟫ ≤ ru * ‖v‖ := (real_inner_le_norm _ _).trans_eq (by rw [norm_sub_rev])
  have b3 : -⟪u - Q.Pt1 u, D.dt0 eφ⟫ ≤ ru * ‖D.dt0 eφ‖ :=
    ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans_eq (by rw [norm_sub_rev])
  have b4 : ⟪M - Q.P2 M, N⟫ ≤ rM * ‖N‖ := (real_inner_le_norm _ _).trans_eq (by rw [norm_sub_rev])
  have b5 : ⟪M - Q.P2 M, Q.S1h v⟫ ≤ rM * ‖Q.S1h v‖ :=
    (real_inner_le_norm _ _).trans_eq (by rw [norm_sub_rev])
  have b6 : ⟪ρ - Q.Pt2 ρ, μ⟫ ≤ rρ * ‖μ‖ := (real_inner_le_norm _ _).trans_eq (by rw [norm_sub_rev])
  have b7 : ⟪ρ - Q.Pt2 ρ, D.dt1 v⟫ ≤ rρ * ‖D.dt1 v‖ :=
    (real_inner_le_norm _ _).trans_eq (by rw [norm_sub_rev])
  have b8 : ⟪D.dt0 (φ - Q.Pt0 φ), v⟫ ≤ rφ * ‖v‖ :=
    (real_inner_le_norm _ _).trans_eq (by rw [← norm_neg, ← map_neg, neg_sub])
  have b9 : ⟪M, (D.S1 - Q.S1h) v⟫ ≤ K1 * √(Q.gnSq v) := (le_abs_self _).trans (hK1 v hvm)
  have b10 : -⟪(D.S1 - Q.S1h) u, N⟫ ≤ rS * ‖N‖ :=
    ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans_eq (by rw [LinearMap.sub_apply])
  have b11 : -⟪Q.S1h (u - Q.Pt1 u), N⟫ ≤ rSu * ‖N‖ :=
    ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans_eq
      (by rw [← norm_neg, ← map_neg, neg_sub])
  have b12 : -⟪D.dt1 (u - Q.Pt1 u), μ⟫ ≤ rdu * ‖μ‖ :=
    ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans_eq
      (by rw [← norm_neg, ← map_neg, neg_sub])
  have b13 : ℓ ((D.S0 - Q.S0h) eφ) ≤ K0 * √(graphSq D.dt0 eφ) :=
    (le_abs_self _).trans (hK0 eφ heφm)
  have hsum : (1 / 2 : ℝ) * n2 ≤ ∑ i : Fin 13,
      (![rσ, ru, ru, rM, rM, rρ, rρ, rφ, K1, rS, rSu, rdu, K0] i) *
      (![‖eσ‖, ‖v‖, ‖D.dt0 eφ‖, ‖N‖, ‖Q.S1h v‖, ‖μ‖, ‖D.dt1 v‖, ‖v‖, √(Q.gnSq v), ‖N‖, ‖N‖,
        ‖μ‖, √(graphSq D.dt0 eφ)] i) := by
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    have := hres ▸ hcoer
    linarith only [this, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13]
  have hNb := Finset.univ.le_mul_sum_sq_of_mul_le_sum_mul _ _ (by norm_num : (0 : ℝ) < 1 / 2)
    hK0' (fun i _ => by
      fin_cases i
      · exact hτ2
      · exact hv2
      · exact hdψ2
      · exact hN2
      · exact hSv2
      · exact hμ2
      · exact hdv2
      · exact hv2
      · exact hgv2
      · exact hN2
      · exact hN2
      · exact hμ2
      · exact hgψ2) hsum
  have hcard : ((Finset.univ : Finset (Fin 13)).card : ℝ) + 1 = 14 := by
    rw [Finset.card_univ, Fintype.card_fin]; norm_num
  rw [hcard] at hNb
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero] at hNb
  have hdata : Q.strangData σ φ u M ρ K0 K1 = rσ ^ 2 + rφ ^ 2 + (ru ^ 2 + rSu ^ 2 + rdu ^ 2)
      + rM ^ 2 + rρ ^ 2 + K0 ^ 2 + K1 ^ 2 + rS ^ 2 := rfl
  rw [strangConst, hdata, ← hK]
  have hDD : rσ ^ 2 + ru ^ 2 + ru ^ 2 + rM ^ 2 + rM ^ 2 + rρ ^ 2
      + rρ ^ 2 + rφ ^ 2 + K1 ^ 2 + rS ^ 2 + rSu ^ 2 + rdu ^ 2 + K0 ^ 2 ≤
      2 * (rσ ^ 2 + rφ ^ 2 + (ru ^ 2 + rSu ^ 2 + rdu ^ 2) + rM ^ 2 + rρ ^ 2 + K0 ^ 2 + K1 ^ 2
        + rS ^ 2) := by
    have := sq_nonneg rσ; have := sq_nonneg rφ; have := sq_nonneg rSu; have := sq_nonneg rdu
    have := sq_nonneg K0; have := sq_nonneg K1; have := sq_nonneg rS
    linarith
  have hKD := mul_le_mul_of_nonneg_left hDD (by positivity : (0 : ℝ) ≤ 14 * K / (1 / 2) ^ 2)
  have : (14 : ℝ) * K / (1 / 2) ^ 2 = 56 * K := by norm_num; ring
  rw [this] at hNb hKD
  nlinarith only [hNb, hKD]

/-- `‖x − xₚ‖² ≤ 2‖xₚ − Πx‖² + 2‖Πx − x‖²`. -/
theorem norm_sub_sq_le_split {E : Type*} [SeminormedAddCommGroup E] (x xP Px : E) :
    ‖x - xP‖ ^ 2 ≤ 2 * ‖xP - Px‖ ^ 2 + 2 * ‖Px - x‖ ^ 2 := by
  have : x - xP = -((xP - Px) + (Px - x)) := by abel
  rw [this, norm_neg]; exact norm_add_sq_le_two_mul _ _

/-- **Strang bound in the energy norm**: `‖σ − σₚ‖² + ‖u − uₚ‖² + ‖M − Mₚ‖² + ‖ρ − ρₚ‖² ≤
2 (strangConst C_p + 1) · strangData` (the quantity `‖Pξ − ξ‖²` of the Ch. 6 convergence
theorems), under the hypotheses of `strang_shiftedForm_h`. -/
theorem strang_energy {Cp CR CS : ℝ} (H : Stability D Cp CR CS) (h54 : Q.Compatible)
    {σ : V0} {φ : Vt0} {u : Vt1} {M : W2} {ρ : Wt2} (c3 : D.d0 σ = D.S0 φ)
    (ℓ : V1 →ₗ[ℝ] ℝ) {K0 K1 : ℝ}
    (hK0 : ∀ ψ ∈ Q.Vt0h, |ℓ ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ v ∈ Q.Vt1h, |⟪M, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    {σP : V0} {φP : Vt0} {uP : Vt1} {MP : W2} {ρP : Wt2}
    (hσP : σP ∈ Q.V0h) (hφP : φP ∈ Q.Vt0h) (huP : uP ∈ Q.Vt1h) (hMP : MP ∈ Q.W2h)
    (hρP : ρP ∈ Q.Wt2h) (hcons : D.d0 σP = Q.S0h φP)
    (heq : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, D.d0 τ = Q.S0h ψ → ∀ v ∈ Q.Vt1h, ∀ N ∈ Q.W2h,
      ∀ μ ∈ Q.Wt2h, Q.shiftedFormH σP φP uP MP ρP τ ψ v N μ =
        shiftedFormC D σ φ u M ρ τ ψ v N μ - ℓ (D.d0 τ - D.S0 ψ)) :
    ‖σ - σP‖ ^ 2 + ‖u - uP‖ ^ 2 + ‖M - MP‖ ^ 2 + ‖ρ - ρP‖ ^ 2 ≤
      2 * (strangConst Cp + 1) * Q.strangData σ φ u M ρ K0 K1 := by
  have hS := strang_shiftedForm_h H h54 c3 ℓ hK0 hK1 hσP hφP huP hMP hρP hcons heq
  have e1 := norm_sub_sq_le_split σ σP (Q.P0 σ)
  have e2 := norm_sub_sq_le_split u uP (Q.Pt1 u)
  have e3 := norm_sub_sq_le_split M MP (Q.P2 M)
  have e4 := norm_sub_sq_le_split ρ ρP (Q.Pt2 ρ)
  have hgn := Q.gnSq_nonneg (Q.Pt1 u - u)
  have hgn' : ‖Q.Pt1 u - u‖ ^ 2 ≤ Q.gnSq (Q.Pt1 u - u) := by
    unfold gnSq; nlinarith [sq_nonneg ‖Q.S1h (Q.Pt1 u - u)‖, sq_nonneg ‖D.dt1 (Q.Pt1 u - u)‖]
  have hD : ‖Q.P0 σ - σ‖ ^ 2 + ‖Q.Pt1 u - u‖ ^ 2 + ‖Q.P2 M - M‖ ^ 2 + ‖Q.Pt2 ρ - ρ‖ ^ 2 ≤
      Q.strangData σ φ u M ρ K0 K1 := by
    unfold strangData
    nlinarith [sq_nonneg ‖D.dt0 (Q.Pt0 φ - φ)‖, sq_nonneg K0, sq_nonneg K1,
      sq_nonneg ‖D.S1 u - Q.S1h u‖]
  have hn : ‖σP - Q.P0 σ‖ ^ 2 + ‖uP - Q.Pt1 u‖ ^ 2 + ‖MP - Q.P2 M‖ ^ 2 + ‖ρP - Q.Pt2 ρ‖ ^ 2 ≤
      Q.shiftedNormSq (σP - Q.P0 σ) (φP - Q.Pt0 φ) (uP - Q.Pt1 u) (MP - Q.P2 M)
        (ρP - Q.Pt2 ρ) := by
    unfold shiftedNormSq
    nlinarith [sq_nonneg ‖D.dt0 (φP - Q.Pt0 φ)‖, sq_nonneg ‖Q.S1h (uP - Q.Pt1 u)‖,
      sq_nonneg ‖D.dt1 (uP - Q.Pt1 u)‖]
  nlinarith only [hS, hD, hn, e1, e2, e3, e4]

/-- **`O(h)` rate of the elliptic projection**: if the Strang data are `O(h²)`
(interpolation errors and consistency constants `O(h)`), so is the energy error. -/
theorem strang_energy_rate {Cp CR CS : ℝ} (H : Stability D Cp CR CS) (h54 : Q.Compatible)
    {σ : V0} {φ : Vt0} {u : Vt1} {M : W2} {ρ : Wt2} (c3 : D.d0 σ = D.S0 φ)
    (ℓ : V1 →ₗ[ℝ] ℝ) {K0 K1 c h : ℝ}
    (hK0 : ∀ ψ ∈ Q.Vt0h, |ℓ ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ v ∈ Q.Vt1h, |⟪M, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hdata : Q.strangData σ φ u M ρ K0 K1 ≤ (c * h) ^ 2)
    {σP : V0} {φP : Vt0} {uP : Vt1} {MP : W2} {ρP : Wt2}
    (hσP : σP ∈ Q.V0h) (hφP : φP ∈ Q.Vt0h) (huP : uP ∈ Q.Vt1h) (hMP : MP ∈ Q.W2h)
    (hρP : ρP ∈ Q.Wt2h) (hcons : D.d0 σP = Q.S0h φP)
    (heq : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, D.d0 τ = Q.S0h ψ → ∀ v ∈ Q.Vt1h, ∀ N ∈ Q.W2h,
      ∀ μ ∈ Q.Wt2h, Q.shiftedFormH σP φP uP MP ρP τ ψ v N μ =
        shiftedFormC D σ φ u M ρ τ ψ v N μ - ℓ (D.d0 τ - D.S0 ψ)) :
    √(‖σ - σP‖ ^ 2 + ‖u - uP‖ ^ 2 + ‖M - MP‖ ^ 2 + ‖ρ - ρP‖ ^ 2) ≤
      √(2 * (strangConst Cp + 1)) * |c| * |h| := by
  have hS := strang_energy H h54 c3 ℓ hK0 hK1 hσP hφP huP hMP hρP hcons heq
  have hC : 0 ≤ 2 * (strangConst Cp + 1) := by unfold strangConst; positivity
  rw [mul_assoc, ← abs_mul, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hC]
  exact Real.sqrt_le_sqrt (hS.trans (mul_le_mul_of_nonneg_left hdata hC))

/-! ### The elliptic projection of a discretization -/

variable (Q) in
/-- The discrete BGG data of a discretization `Q`: the FE spaces with `d`, `S₀,ₕ = Π¹S₀`,
`S₁,ₕ = Π²S₁` (anticommutation from the commuting projections). This is the data `D` of
`DiscreteSolution` and of the elliptic projection (6.4) for `Q`. -/
def toSegmentH : Segment ℝ Q.V0h Q.V1h Q.W2h Q.Vt0h Q.Vt1h Q.Wt2h where
  d0 := D.d0.restrict Q.d0_mem
  d1 := D.d1.restrict Q.d1_mem
  dt0 := D.dt0.restrict Q.dt0_mem
  dt1 := D.dt1.restrict Q.dt1_mem
  S0 := Q.S0h.restrict fun x _ => Q.S0h_mem x
  S1 := Q.S1h.restrict fun x _ => Q.S1h_mem x
  d1_d0 x := Subtype.ext (by simp [D.d1_d0])
  dt1_dt0 x := Subtype.ext (by simp [D.dt1_dt0])
  anticomm x := Subtype.ext (by simp [Q.anticomm_h])

/-- `d` is injective on `Ṽₕ⁰`. -/
theorem toSegmentH_dt0_injective {Cp CR CS : ℝ} (H : Stability D Cp CR CS) :
    Function.Injective Q.toSegmentH.dt0 := fun a b hab =>
  Subtype.ext (dt0_injective H (by simpa [toSegmentH, Subtype.ext_iff] using hab))

/-- `dVₕ⁰ + S₀,ₕṼₕ⁰ = Vₕ¹` (from `exists_sub_S0h_eq`): the hypothesis of
`existsUnique_isEllipticProjection`, weaker than the surjectivity of `S₀,ₕ`. -/
theorem toSegmentH_exists_sub {Cp CR CS : ℝ} (H : Stability D Cp CR CS) (h54 : Q.Compatible)
    (μ : Q.V1h) : ∃ τ ψ, Q.toSegmentH.d0 τ - Q.toSegmentH.S0 ψ = μ := by
  obtain ⟨τ, hτ, ψ, hψ, h⟩ := exists_sub_S0h_eq H h54 μ.2
  exact ⟨⟨τ, hτ⟩, ⟨ψ, hψ⟩, Subtype.ext (by simpa [toSegmentH] using h)⟩

/-- The left side of (6.4) for `toSegmentH` is the discrete shifted form. -/
theorem energyInner_add_discreteSkewForm_toSegmentH
    (a b : Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) (q ψ : Q.Vt0h) :
    energyInner a b + discreteSkewForm Q.toSegmentH (a, q) (b, ψ) =
      Q.shiftedFormH a.1 q a.2.1 a.2.2.1 a.2.2.2 b.1 ψ b.2.1 b.2.2.1 b.2.2.2 := by
  simp only [energyInner, discreteSkewForm, shiftedFormH, toSegmentH, Submodule.coe_inner,
    LinearMap.coe_restrict_apply]
  ring

/-- The data functional of the elliptic projection (6.4) of an exact state `(σ, φ, u, M, ρ)`
with multiplier functional `ℓ`: the continuous shifted form `A(x, y) − ℓ(dτ − S₀ψ)` tested on
discrete `y`. -/
def ellipticDataH (σ : V0) (φ : Vt0) (u : Vt1) (M : W2) (ρ : Wt2) (ℓ : V1 →ₗ[ℝ] ℝ) :
    Module.Dual ℝ ((Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h) where
  toFun y := shiftedFormC D σ φ u M ρ y.1.1 y.2 y.1.2.1 y.1.2.2.1 y.1.2.2.2
    - ℓ (D.d0 y.1.1 - D.S0 y.2)
  map_add' y y' := by
    simp only [shiftedFormC, Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add, map_sub,
      inner_add_right]; ring
  map_smul' c y := by
    simp only [shiftedFormC, Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul, map_sub,
      real_inner_smul_right, smul_eq_mul, RingHom.id_apply]; ring

/-- **Strang bound for the elliptic projection (6.4) of a discretization.** Every solution
`x = ((σₚ, uₚ, Mₚ, ρₚ), φₚ, λₚ)` of (6.4) for the discrete data `toSegmentH` with the data
`ellipticDataH` of an exact state (`dσ = S₀φ`) satisfies the bounds of `strang_shiftedForm_h`
and `strang_energy`; such a solution exists and is unique
(`existsUnique_isEllipticProjection` with `toSegmentH_dt0_injective`, `toSegmentH_exists_sub`).
See [QuennevilleBelair2015], §6.2, (6.4); cf. [Ciarlet2002]. -/
theorem strang_of_isEllipticProjection {Cp CR CS : ℝ} (H : Stability D Cp CR CS)
    (h54 : Q.Compatible) {σ : V0} {φ : Vt0} {u : Vt1} {M : W2} {ρ : Wt2}
    (c3 : D.d0 σ = D.S0 φ) (ℓ : V1 →ₗ[ℝ] ℝ) {K0 K1 : ℝ}
    (hK0 : ∀ ψ ∈ Q.Vt0h, |ℓ ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ v ∈ Q.Vt1h, |⟪M, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    {x : ((Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h) × Q.V1h}
    (hx : IsEllipticProjection Q.toSegmentH (Q.ellipticDataH σ φ u M ρ ℓ) 0 x) :
    Q.shiftedNormSq ((x.1.1.1 : V0) - Q.P0 σ) ((x.1.2 : Vt0) - Q.Pt0 φ)
        ((x.1.1.2.1 : Vt1) - Q.Pt1 u) ((x.1.1.2.2.1 : W2) - Q.P2 M)
        ((x.1.1.2.2.2 : Wt2) - Q.Pt2 ρ) ≤ strangConst Cp * Q.strangData σ φ u M ρ K0 K1 ∧
      ‖σ - x.1.1.1‖ ^ 2 + ‖u - x.1.1.2.1‖ ^ 2 + ‖M - x.1.1.2.2.1‖ ^ 2 + ‖ρ - x.1.1.2.2.2‖ ^ 2 ≤
        2 * (strangConst Cp + 1) * Q.strangData σ φ u M ρ K0 K1 := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨⟨⟨σP, uP, MP, ρP⟩, φP⟩, lP⟩ := x
  have hcons : D.d0 σP = Q.S0h φP := by
    have := congrArg Subtype.val h2
    simpa [toSegmentH, sub_eq_zero] using this
  have heq : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, D.d0 τ = Q.S0h ψ → ∀ v ∈ Q.Vt1h, ∀ N ∈ Q.W2h,
      ∀ μ ∈ Q.Wt2h, Q.shiftedFormH σP φP uP MP ρP τ ψ v N μ =
        shiftedFormC D σ φ u M ρ τ ψ v N μ - ℓ (D.d0 τ - D.S0 ψ) := by
    intro τ hτ ψ hψ hτψ v hv N hN μ hμ
    have e := h1 ((⟨τ, hτ⟩, ⟨v, hv⟩, ⟨N, hN⟩, ⟨μ, hμ⟩), ⟨ψ, hψ⟩)
    have h0 : Q.toSegmentH.d0 ⟨τ, hτ⟩ - Q.toSegmentH.S0 ⟨ψ, hψ⟩ = 0 :=
      Subtype.ext (by simp [toSegmentH, hτψ])
    rw [h0, inner_zero_right, sub_zero, energyInner_add_discreteSkewForm_toSegmentH] at e
    exact e
  exact ⟨strang_shiftedForm_h H h54 c3 ℓ hK0 hK1 σP.2 φP.2 uP.2 MP.2 ρP.2 hcons heq,
    strang_energy H h54 c3 ℓ hK0 hK1 σP.2 φP.2 uP.2 MP.2 ρP.2 hcons heq⟩

/-- **Uniform well-posedness of (6.4) for a discretization**: for finite-dimensional FE spaces,
the elliptic projection of every exact state exists and is unique, under the continuous
hypotheses `Stability` and (5.4) only (no surjectivity of `S₀,ₕ` is needed). -/
theorem existsUnique_isEllipticProjection_toSegmentH {Cp CR CS : ℝ} (H : Stability D Cp CR CS)
    (h54 : Q.Compatible) [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.V1h]
    [FiniteDimensional ℝ Q.W2h] [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h]
    [FiniteDimensional ℝ Q.Wt2h]
    (G : Module.Dual ℝ ((Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h)) (g : Q.V1h) :
    ∃! x, IsEllipticProjection Q.toSegmentH G g x :=
  existsUnique_isEllipticProjection (toSegmentH_dt0_injective H) (toSegmentH_exists_sub H h54)
    G g

/-- **Non-vacuity of the hypotheses of the Strang bound** (`strang_of_isEllipticProjection`):
on the identity discretization of `Discrete.exampleSegment` (`S₀, S₁ ≠ 0`), `Stability`,
`Compatible`, the solvability hypotheses of (6.4) for `toSegmentH`, and the consistency bounds
(with `K₀ = K₁ = 0`) hold simultaneously. -/
theorem exists_strang_nonvacuous :
    ∃ (D : Segment ℝ (EuclideanSpace ℝ (Fin 0)) ℝ ℝ ℝ ℝ ℝ) (Q : Discrete D),
      Stability D 1 1 1 ∧ Q.Compatible ∧ D.S0 ≠ 0 ∧ D.S1 ≠ 0 ∧
      Function.Injective Q.toSegmentH.dt0 ∧
      (∀ μ, ∃ τ ψ, Q.toSegmentH.d0 τ - Q.toSegmentH.S0 ψ = μ) ∧
      (∀ ℓ : ℝ →ₗ[ℝ] ℝ, ∀ ψ ∈ Q.Vt0h, |ℓ ((D.S0 - Q.S0h) ψ)| ≤ 0 * √(graphSq D.dt0 ψ)) ∧
      ∀ M : ℝ, ∀ v ∈ Q.Vt1h, |⟪M, (D.S1 - Q.S1h) v⟫| ≤ 0 * √(Q.gnSq v) := by
  have H : Stability exampleSegment 1 1 1 :=
    { Cp_nonneg := zero_le_one, CR_nonneg := zero_le_one, CS_nonneg := zero_le_one,
      poinc0 := fun σ => by simp [Subsingleton.elim σ 0],
      poinct0 := fun φ => by simp [exampleSegment],
      exact1 := fun μ hμ => ⟨0, by simpa [exampleSegment, eq_comm] using hμ⟩,
      hodget1 := fun v => ⟨v, 0, by simp [exampleSegment]⟩,
      reg := fun x => ⟨x, by simp [exampleSegment]⟩,
      boundS0 := fun ψ => by simp [exampleSegment, graphSq],
      boundS1 := fun v => by simp [exampleSegment, graphSq] }
  refine ⟨exampleSegment, Discrete.top _, H, Discrete.top_compatible _, ?_, ?_,
    toSegmentH_dt0_injective H, toSegmentH_exists_sub H (Discrete.top_compatible _),
    fun ℓ ψ _ => by simp [Discrete.top, S0h], fun M v _ => by simp [Discrete.top, S1h]⟩
  · intro h; have := LinearMap.congr_fun h 1; simp [exampleSegment] at this
  · intro h; have := LinearMap.congr_fun h 1; simp [exampleSegment] at this

end Discrete

end Feec.BGG
