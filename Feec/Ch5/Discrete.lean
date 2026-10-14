module

public import Feec.Foundation.BGG
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Chapter 5.2: discretization of the BGG (weak-symmetry) complex

Formalizes thesis §5.2 (Props 5.3, 5.4, 5.6, Thm 5.5) and the abstract core of Prop 5.7,
filling the gaps found in the audit (`docs/BLUEPRINT.md` §4, M10; critic item 3).

**Part 1 (pure finite-dimensional algebra, on arbitrary inner product spaces).**
* `discrete_anticomm`, `surj_of_54`: the unlabeled claims after the setup (line 3304ff).
* `exact_55`: exactness of the discrete complex (5.5) at `Ṽ_h¹` (the discrete Hodge
  decomposition without harmonic part), used in Prop 5.4 and Thm 5.5 but never derived from
  the two exact discrete complexes assumed in Prop 5.3.
* `prop54_unique`, `prop54_existsUnique` (via `sysForm_bijective`): **Prop 5.4** with minimal
  hypotheses; `prop54_hB_necessary` shows the condition `dV_h⁰ + S₀,hṼ_h⁰ = V_h¹` is needed,
  and `prop54_counterexample_noTopExact` shows that the exactness at `V_h¹` assumed in Prop 5.3
  (but never invoked in the thesis' proof of Prop 5.4) cannot be dropped.
* `cons_of_56c`, `complex_55`, `decomp_55`: (5.6c) forces `dσ_h = S₀,hφ_h`; (5.5) is a
  complex; `Ṽ_h¹ = dpr₂Γ_h ⊕ Z_hᗮ` (reusable forms of steps inlined in Thm 5.5).
* `prop_5_6`: **Prop 5.6** (error equation), with the multiplier as a functional.
* `thm55_lhs_identity`: the coercivity identity of the proof of Thm 5.5 (lost `ε`'s restored).
* `minNorm_bound`, `norm_le_of_sub_mem`: the min-norm step missing from Prop 5.3(b).
* `dof_commute`, `dof_hS_of_span`, `dof_commute_of_span`: the degree-of-freedom argument
  behind **Prop 5.7** ((5.4) for canonical projections), without the invalid density step. The
  concrete Lagrange-P2 → Nédélec computation (5.8) is *not* formalized: it enters as the
  hypothesis that each `ℓ_k ∘ S₀` lies in the span of the `m_i`.

**Part 2 (the discretization of a `BGGData`).** `ContHyp` collects the *continuous*,
`h`-independent hypotheses (Poincaré, exactness, Hodge, regular decomposition with its
open-mapping constant, boundedness of `S₀, S₁`); `Disc` the finite element subcomplexes with
total cochain projections; `Disc.Bounded` the uniform projection bounds; `Disc.Hyp54` is (5.4).
* `Disc.exact_t1`, `Disc.exact_1`, `Disc.exact_55_h`, `Disc.hB`: discrete exactness and the
  Prop 5.4 condition, **derived** from the continuous hypotheses.
* `Disc.prop_5_3_a`, `Disc.prop_5_3_b`: **Prop 5.3**, the discrete Poincaré inequalities, with
  constants `Ca`, `Cb` **derived** from continuous constants and projection bounds (AFW-type
  argument `Disc.preimage_bound` plus min-norm), not assumed.
* `Disc.prop_5_4`: **Prop 5.4** (unique solvability of (5.6)) in the discretization.
* `Disc.thm_5_5`: **Thm 5.5**, the quantitative a priori estimate, with full signature and the
  explicit `h`-independent constant `C55`.
* `nonvacuous`: a concrete instance of `ContHyp + Disc + Bounded + Hyp54` with nonzero spaces
  and `S₁ ≠ 0` (identity discretization of a finite-dimensional complex).

Caveat on the hypotheses (inherited from the thesis): `Disc.Bounded` asks for uniformly bounded
total cochain projections, `Disc.Hyp54` asks the *same* projections to satisfy (5.4). The thesis
verifies (5.4) only for canonical projections (Prop 5.7), which are not bounded on `H(curl)`;
whether some bounded (e.g. smoothed) commuting projections satisfy (5.4) in the elasticity /
Einstein–Bianchi application is not known to us and is not addressed by the thesis.

Modeling: "type = domain with `W`-inner product" (foundation §E/§F); graph norms are explicit
(`gr2`, `Disc.gn2`). Missing analytic facts (Sobolev spaces, finite element spaces, the open
mapping constant of the concrete complex) enter only as fields of `ContHyp` / `Disc`.

## References

* [QuennevilleBelair2015], Ch. 5: §5.1 (abstract framework, complex (5.1), Props 5.1–5.2),
  §5.2 (discretization: Props 5.3, 5.4, 5.6, Thm 5.5), §5.3 (Props 5.7–5.8, application to
  the time-independent EB system)
* [Arnold2018] (FEEC framework: Hilbert complexes, subcomplexes, cochain projections, discrete
  Poincaré inequalities, mixed Hodge Laplacian)
* [AFW2010], Thm 3.6 (discrete Poincaré inequality via bounded cochain projections); also the
  stability and error analysis of the discrete mixed Hodge Laplacian
* [AFW2006] (canonical and smoothed cochain projections, finite element differential forms)
* [Arnold2013] (degrees of freedom and canonical projections of finite element forms)
* [ArnoldHu2021] (BGG construction: complexes from complexes via connecting maps `S`)
* [AFW2007] (weakly imposed symmetry for elasticity, the model for the `S₁ = skw` coupling)
* [DuranLiberman1992], [Falk2008] (multiplier formulation replacing `H²` by `H¹ × H¹`, from
  Reissner–Mindlin plates)
* [Brezzi1974], [Babuska1971], [BoffiBrezziFortin2013] (saddle-point well-posedness and
  Galerkin error estimates)
* [HiptmairXu2007], §3 and [Hiptmair2002], Lemma 2.4, as cited by the thesis (§5.3) for the
  regular decomposition behind `ContHyp.reg`; [Hiptmair2002] also for Nédélec elements and
  their canonical interpolants -/

open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace Feec.Ch5.Discrete

/-! ## Part 1: finite-dimensional algebra of the discrete system -/

section Generic

variable {X0 X1 X2 Y0 Y1 Y2 : Type*}
  [NormedAddCommGroup X0] [InnerProductSpace ℝ X0]
  [NormedAddCommGroup X1] [InnerProductSpace ℝ X1]
  [NormedAddCommGroup X2] [InnerProductSpace ℝ X2]
  [NormedAddCommGroup Y0] [InnerProductSpace ℝ Y0]
  [NormedAddCommGroup Y1] [InnerProductSpace ℝ Y1]
  [NormedAddCommGroup Y2] [InnerProductSpace ℝ Y2]

/-- Minimum-norm principle: if `u ⊥ K` and `u' - u ∈ K` then `‖u‖ ≤ ‖u'‖`. -/
theorem norm_le_of_sub_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Submodule ℝ E} {u u' : E} (hu : u ∈ Kᗮ) (h : u' - u ∈ K) : ‖u‖ ≤ ‖u'‖ := by
  have h0 : ⟪u, u' - u⟫ = 0 := Submodule.inner_left_of_mem_orthogonal h hu
  have hsq : ‖u'‖ ^ 2 = ‖u‖ ^ 2 + ‖u' - u‖ ^ 2 := by
    have := norm_add_sq_real u (u' - u)
    rw [h0, add_sub_cancel] at this; linarith
  nlinarith [norm_nonneg u, norm_nonneg u', sq_nonneg ‖u' - u‖]

/-- **Min-norm step of Prop 5.3(b)** (missing in the thesis): a uniform preimage bound for `T`
gives the bound for every `x ⊥ ker T`.
This is the min-norm step of the classical proof of the discrete Poincaré inequality,
[AFW2010, Thm 3.6]; cf. [Arnold2018]. -/
theorem minNorm_bound {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →ₗ[ℝ] F) (C : ℝ)
    (hpre : ∀ x : E, ∃ x' : E, T x' = T x ∧ ‖x'‖ ≤ C * ‖T x‖)
    {x : E} (hx : x ∈ (LinearMap.ker T)ᗮ) : ‖x‖ ≤ C * ‖T x‖ := by
  obtain ⟨x', hTx', hx'⟩ := hpre x
  exact (norm_le_of_sub_mem hx (by simp [hTx'])).trans hx'

/-- Thesis §5.2 (line 3304, unlabeled): `d S₀,h = -S₁,h d` for `S₀,h = Π¹S₀`, `S₁,h = Π²S₁`.
Thesis gap: the commuting property `dΠ¹ = Π²d` is used but not stated.
See [QuennevilleBelair2015, §5.2]; cochain projections as in [AFW2010], [Arnold2018]. -/
theorem discrete_anticomm (dX1 : X1 →ₗ[ℝ] X2) (dY0 : Y0 →ₗ[ℝ] Y1)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2) (P1 : X1 →ₗ[ℝ] X1) (P2 : X2 →ₗ[ℝ] X2)
    (hcomm : ∀ x, dX1 (P1 x) = P2 (dX1 x)) (hanti : ∀ ψ, dX1 (S0 ψ) = -S1 (dY0 ψ)) (ψ : Y0) :
    dX1 (P1 (S0 ψ)) = -(P2 (S1 (dY0 ψ))) := by
  rw [hcomm, hanti, map_neg]

/-- Thesis §5.2 (lines 3305–3314): (5.4) makes `S₀,h` onto `V_h¹`.
Thesis gap: the needed surjectivity of `Π¹S₀` is asserted, not proved; here it is a hypothesis.
(In the discretization below we instead *derive* the weaker condition `dV_h⁰ + S₀,hṼ_h⁰ = V_h¹`,
see `Disc.hB`.) See [QuennevilleBelair2015, §5.2, (5.4)]. -/
theorem surj_of_54 {Dm X1h Y0h : Type*} [AddCommGroup Dm] [Module ℝ Dm] [AddCommGroup X1h]
    [Module ℝ X1h] [AddCommGroup Y0h] [Module ℝ Y0h]
    (P1S0 : Dm →ₗ[ℝ] X1h) (S0h : Y0h →ₗ[ℝ] X1h) (Pt0 : Dm →ₗ[ℝ] Y0h)
    (h54 : S0h ∘ₗ Pt0 = P1S0) (hs : Function.Surjective P1S0) : Function.Surjective S0h :=
  fun y => let ⟨ψ, hψ⟩ := hs y; ⟨Pt0 ψ, by rw [← LinearMap.comp_apply, h54, hψ]⟩

/-- Thesis §5.2, complex (5.5) is exact at `Ṽ_h¹` (the discrete Hodge decomposition without
harmonic part).
Thesis gap: the proofs of Prop 5.4 and Thm 5.5 use this exactness without deriving it. It
follows from the exactness of the two discrete complexes assumed in Prop 5.3, at `Ṽ_h¹` *and*
at `V_h¹`, plus `dS₀ = -S₁d`.
See [QuennevilleBelair2015, §5.2, (5.5)]; cf. the BGG diagram chase in [ArnoldHu2021]. -/
theorem exact_55 (dX0 : X0 →ₗ[ℝ] X1) (dX1 : X1 →ₗ[ℝ] X2) (dY0 : Y0 →ₗ[ℝ] Y1)
    (dY1 : Y1 →ₗ[ℝ] Y2) (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2)
    (hanti : ∀ ψ, dX1 (S0 ψ) = -S1 (dY0 ψ))
    (hY1 : ∀ u, dY1 u = 0 → ∃ χ, dY0 χ = u) (hX1 : ∀ μ, dX1 μ = 0 → ∃ ρ, dX0 ρ = μ)
    (u : Y1) (hS : S1 u = 0) (hd : dY1 u = 0) : ∃ ρ χ, dX0 ρ = S0 χ ∧ dY0 χ = u := by
  obtain ⟨χ, hχ⟩ := hY1 u hd
  obtain ⟨ρ, hρ⟩ := hX1 (S0 χ) (by rw [hanti, hχ, hS, neg_zero])
  exact ⟨ρ, χ, hρ, hχ⟩

/-- **Thesis Prop 5.4 (uniqueness), minimal hypotheses.** The homogeneous discrete system (5.6)
has only the trivial solution.
Correction: none of the uniform-in-`h` bounds of Prop 5.3 are needed. What is used is
`dS₀ = -S₁d`, injectivity of `d` on `Ṽ_h⁰`, exactness at `Ṽ_h¹` and at `V_h¹` (both part of the
"two exact complexes" assumed in Prop 5.3) and `dV_h⁰ + S₀Ṽ_h⁰ = V_h¹` (weaker than
surjectivity of `S₀,h`).
Thesis gap: the "discrete Hodge decomposition" without harmonic part, i.e. exactness of (5.5)
at `Ṽ_h¹`, is used but never derived from those assumptions; it is `exact_55`.
See [QuennevilleBelair2015, Prop 5.4]; cf. [AFW2007] for the analogous weak-symmetry
elasticity argument. -/
theorem prop54_unique
    (dX0 : X0 →ₗ[ℝ] X1) (dX1 : X1 →ₗ[ℝ] X2) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2)
    (hanti : ∀ ψ, dX1 (S0 ψ) = -S1 (dY0 ψ))
    (hY0 : Function.Injective dY0)
    (hY1 : ∀ u, dY1 u = 0 → ∃ χ, dY0 χ = u)
    (hX1 : ∀ μ, dX1 μ = 0 → ∃ ρ, dX0 ρ = μ)
    (hB : ∀ μ : X1, ∃ τ ψ, dX0 τ - S0 ψ = μ)
    {σ : X0} {φ : Y0} {u : Y1} {l : X1}
    (h1 : ∀ τ ψ, ⟪σ, τ⟫ - ⟪u, dY0 ψ⟫ - ⟪l, dX0 τ - S0 ψ⟫ = 0)
    (h2 : ∀ v, ⟪dY0 φ, v⟫ + ⟪S1 u, S1 v⟫ + ⟪dY1 u, dY1 v⟫ = 0)
    (h3 : ∀ μ, ⟪dX0 σ - S0 φ, μ⟫ = 0) :
    σ = 0 ∧ φ = 0 ∧ u = 0 ∧ l = 0 := by
  have hc : dX0 σ - S0 φ = 0 := inner_self_eq_zero.1 (h3 _)
  have e1 := h1 σ φ
  have e2 := h2 u
  rw [hc, inner_zero_right, sub_zero] at e1
  have hsum : ⟪σ, σ⟫ + ⟪S1 u, S1 u⟫ + ⟪dY1 u, dY1 u⟫ = 0 := by
    rw [real_inner_comm (dY0 φ) u] at e1; linarith
  have n1 := real_inner_self_nonneg (x := σ)
  have n2 := real_inner_self_nonneg (x := S1 u)
  have n3 := real_inner_self_nonneg (x := dY1 u)
  have hσ : σ = 0 := inner_self_eq_zero.1 (le_antisymm (by linarith) n1)
  have hSu : S1 u = 0 := inner_self_eq_zero.1 (le_antisymm (by linarith) n2)
  have hdu : dY1 u = 0 := inner_self_eq_zero.1 (le_antisymm (by linarith) n3)
  have hφ : φ = 0 := by
    have := h2 (dY0 φ)
    rw [hSu, hdu, inner_zero_left, inner_zero_left, add_zero, add_zero] at this
    exact hY0 (by rw [inner_self_eq_zero.1 this, map_zero])
  obtain ⟨ρ, χ, hρ, hχ⟩ := exact_55 dX0 dX1 dY0 dY1 S0 S1 hanti hY1 hX1 u hSu hdu
  have hu : u = 0 := by
    have := h1 ρ χ
    rw [hρ, sub_self, inner_zero_right, sub_zero, hσ, inner_zero_left, hχ] at this
    exact (inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith)
  refine ⟨hσ, hφ, hu, ?_⟩
  obtain ⟨τ, ψ, hτψ⟩ := hB l
  have := h1 τ ψ
  rw [hσ, hu, inner_zero_left, inner_zero_left, hτψ] at this
  exact (inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith)

/-- Thesis Prop 5.4: necessity of `dV_h⁰ + S₀,hṼ_h⁰ = V_h¹`. If some `l ≠ 0` is orthogonal to
`dX0 τ - S0 ψ` for all `τ, ψ`, then `(0,0,0,l)` is a nonzero homogeneous solution.
See [QuennevilleBelair2015, Prop 5.4]. -/
theorem prop54_hB_necessary
    (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2) {l : X1} (hl : l ≠ 0)
    (hperp : ∀ τ ψ, ⟪l, dX0 τ - S0 ψ⟫ = 0) :
    ∃ (σ : X0) (φ : Y0) (u : Y1) (m : X1), m ≠ 0 ∧
      (∀ τ ψ, ⟪σ, τ⟫ - ⟪u, dY0 ψ⟫ - ⟪m, dX0 τ - S0 ψ⟫ = 0) ∧
      (∀ v, ⟪dY0 φ, v⟫ + ⟪S1 u, S1 v⟫ + ⟪dY1 u, dY1 v⟫ = 0) ∧
      (∀ μ, ⟪dX0 σ - S0 φ, μ⟫ = 0) :=
  ⟨0, 0, 0, l, hl, fun τ ψ => by simp [hperp], fun v => by simp, fun μ => by simp⟩

/-- **Thesis Prop 5.4: the exactness at `V_h¹` assumed in Prop 5.3 cannot be dropped.** (It is
an assumed hypothesis that the thesis' proof never invokes; it enters through `exact_55`.)
All spaces `ℝ`,
`dX0 = dX1 = dY1 = S1 = 0`, `dY0 = S0 = id`. Every other hypothesis of `prop54_unique` holds
(even `S₀,h` is onto), exactness at `V_h¹` fails, and `(σ,φ,u,λ) = (0,0,1,1)` solves the
homogeneous system. See [QuennevilleBelair2015, Props 5.3–5.4]. -/
theorem prop54_counterexample_noTopExact :
    let dX0 : ℝ →ₗ[ℝ] ℝ := 0
    let dX1 : ℝ →ₗ[ℝ] ℝ := 0
    let dY0 : ℝ →ₗ[ℝ] ℝ := LinearMap.id
    let dY1 : ℝ →ₗ[ℝ] ℝ := 0
    let S0 : ℝ →ₗ[ℝ] ℝ := LinearMap.id
    let S1 : ℝ →ₗ[ℝ] ℝ := 0
    ((∀ ψ, dX1 (S0 ψ) = -S1 (dY0 ψ)) ∧ Function.Injective dY0 ∧
      (∀ u, dY1 u = 0 → ∃ χ, dY0 χ = u) ∧ Function.Surjective S0 ∧
      (∀ μ : ℝ, ∃ τ ψ, dX0 τ - S0 ψ = μ)) ∧
    ¬ (∀ μ, dX1 μ = 0 → ∃ ρ, dX0 ρ = μ) ∧
    ((∀ τ ψ : ℝ, ⟪(0 : ℝ), τ⟫ - ⟪(1 : ℝ), dY0 ψ⟫ - ⟪(1 : ℝ), dX0 τ - S0 ψ⟫ = 0) ∧
      (∀ v, ⟪dY0 0, v⟫ + ⟪S1 1, S1 v⟫ + ⟪dY1 1, dY1 v⟫ = 0) ∧
      (∀ μ, ⟪dX0 0 - S0 0, μ⟫ = 0) ∧ (1 : ℝ) ≠ 0) := by
  intro dX0 dX1 dY0 dY1 S0 S1
  refine ⟨⟨fun ψ => by simp [dX1, S1], fun a b h => h, fun u _ => ⟨u, rfl⟩,
    fun y => ⟨y, rfl⟩, fun μ => ⟨0, -μ, by simp [dX0, S0]⟩⟩, ?_, ?_⟩
  · intro h
    obtain ⟨ρ, hρ⟩ := h 1 rfl
    simp [dX0] at hρ
  · refine ⟨fun τ ψ => ?_, fun v => by simp [dY0, S1, dY1], fun μ => by simp [dX0, S0], one_ne_zero⟩
    simp [dX0, dY0, S0]

/-- The discrete system (5.6) with right-hand side `F`, unknown `x = (σ, φ, u, λ)`.
See [QuennevilleBelair2015, §5.2, (5.6)]. -/
def Sys56 (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2) (F : Y1 →ₗ[ℝ] ℝ) (x : X0 × Y0 × Y1 × X1) : Prop :=
  (∀ τ ψ, ⟪x.1, τ⟫ - ⟪x.2.2.1, dY0 ψ⟫ - ⟪x.2.2.2, dX0 τ - S0 ψ⟫ = 0) ∧
  (∀ v, ⟪dY0 x.2.1, v⟫ + ⟪S1 x.2.2.1, S1 v⟫ + ⟪dY1 x.2.2.1, dY1 v⟫ = F v) ∧
  (∀ μ, ⟪dX0 x.1 - S0 x.2.1, μ⟫ = 0)

/-- The bilinear form of the discrete system (5.6), as a map `E_h → E_h^*`. -/
def sysForm (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2) :
    (X0 × Y0 × Y1 × X1) →ₗ[ℝ] Module.Dual ℝ (X0 × Y0 × Y1 × X1) :=
  LinearMap.mk₂ ℝ (fun x y =>
      ⟪x.1, y.1⟫ - ⟪x.2.2.1, dY0 y.2.1⟫ - ⟪x.2.2.2, dX0 y.1 - S0 y.2.1⟫
      + (⟪dY0 x.2.1, y.2.2.1⟫ + ⟪S1 x.2.2.1, S1 y.2.2.1⟫ + ⟪dY1 x.2.2.1, dY1 y.2.2.1⟫)
      + ⟪dX0 x.1 - S0 x.2.1, y.2.2.2⟫)
    (by intros; simp only [Prod.fst_add, Prod.snd_add, map_add, inner_add_left,
          inner_sub_left, inner_sub_right]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, map_smul, inner_sub_left,
          inner_sub_right, real_inner_smul_left, smul_eq_mul]; ring)
    (by intros; simp only [Prod.fst_add, Prod.snd_add, map_add, inner_add_right,
          inner_sub_left, inner_sub_right]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, map_smul, inner_sub_left,
          inner_sub_right, real_inner_smul_right, smul_eq_mul]; ring)

/-- (5.6) holds iff the system operator maps `x` to the functional `y ↦ F y_u`. -/
theorem sys56_iff (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2) (F : Y1 →ₗ[ℝ] ℝ) (x : X0 × Y0 × Y1 × X1) :
    Sys56 dX0 dY0 dY1 S0 S1 F x ↔
      sysForm dX0 dY0 dY1 S0 S1 x =
        F ∘ₗ (LinearMap.fst ℝ Y1 X1) ∘ₗ (LinearMap.snd ℝ Y0 (Y1 × X1)) ∘ₗ
          (LinearMap.snd ℝ X0 (Y0 × Y1 × X1)) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine LinearMap.ext fun y => ?_
    simp only [sysForm, LinearMap.mk₂_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply]
    rw [h1, h2, h3]; ring
  · intro h
    have key := fun y => LinearMap.congr_fun h y
    simp only [sysForm, LinearMap.mk₂_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply] at key
    refine ⟨fun τ ψ => ?_, fun v => ?_, fun μ => ?_⟩
    · simpa using key (τ, ψ, 0, 0)
    · simpa using key (0, 0, v, 0)
    · simpa using key (0, 0, 0, μ)

/-- Thesis §5.2 ("the system is square"): the system operator `E_h → E_h^*` is injective iff
bijective, since `dim E_h^* = dim E_h`. See [QuennevilleBelair2015, §5.2]. -/
theorem sysForm_bijective (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1)
    (dY1 : Y1 →ₗ[ℝ] Y2) (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2)
    [FiniteDimensional ℝ X0] [FiniteDimensional ℝ X1] [FiniteDimensional ℝ Y0]
    [FiniteDimensional ℝ Y1]
    (huniq : ∀ x, sysForm dX0 dY0 dY1 S0 S1 x = 0 → x = 0) :
    Function.Bijective (sysForm dX0 dY0 dY1 S0 S1) := by
  have hinj : Function.Injective (sysForm dX0 dY0 dY1 S0 S1) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']; exact huniq
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    Subspace.dual_finrank_eq.symm).1 hinj⟩

/-- **Thesis Prop 5.4 (invertibility), minimal hypotheses.** For every right-hand side `F`
the discrete system (5.6) has exactly one solution.
See [QuennevilleBelair2015, Prop 5.4]; cf. discrete well-posedness of saddle-point systems,
[Brezzi1974], [BoffiBrezziFortin2013], and of the discrete mixed Hodge Laplacian, [AFW2010]. -/
theorem prop54_existsUnique
    [FiniteDimensional ℝ X0] [FiniteDimensional ℝ X1] [FiniteDimensional ℝ Y0]
    [FiniteDimensional ℝ Y1]
    (dX0 : X0 →ₗ[ℝ] X1) (dX1 : X1 →ₗ[ℝ] X2) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 : Y0 →ₗ[ℝ] X1) (S1 : Y1 →ₗ[ℝ] X2)
    (hanti : ∀ ψ, dX1 (S0 ψ) = -S1 (dY0 ψ))
    (hY0 : Function.Injective dY0)
    (hY1 : ∀ u, dY1 u = 0 → ∃ χ, dY0 χ = u)
    (hX1 : ∀ μ, dX1 μ = 0 → ∃ ρ, dX0 ρ = μ)
    (hB : ∀ μ : X1, ∃ τ ψ, dX0 τ - S0 ψ = μ) (F : Y1 →ₗ[ℝ] ℝ) :
    ∃! x, Sys56 dX0 dY0 dY1 S0 S1 F x := by
  have hbij := sysForm_bijective dX0 dY0 dY1 S0 S1 (fun x hx => by
    have h0 := (sys56_iff dX0 dY0 dY1 S0 S1 0 x).2 (by rw [hx]; exact LinearMap.ext fun y => by simp)
    obtain ⟨h1, h2, h3⟩ := h0
    obtain ⟨e1, e2, e3, e4⟩ := prop54_unique dX0 dX1 dY0 dY1 S0 S1 hanti hY0 hY1 hX1 hB h1
      (fun v => by simpa using h2 v) h3
    ext <;> simp [e1, e2, e3, e4])
  obtain ⟨x, hx⟩ := hbij.2 (F ∘ₗ (LinearMap.fst ℝ Y1 X1) ∘ₗ (LinearMap.snd ℝ Y0 (Y1 × X1)) ∘ₗ
    (LinearMap.snd ℝ X0 (Y0 × Y1 × X1)))
  refine ⟨x, (sys56_iff _ _ _ _ _ F x).2 hx, fun y hy => hbij.1 ?_⟩
  rw [hx, ← (sys56_iff _ _ _ _ _ F y).1 hy]

/-- **Thesis Prop 5.6 (error equation).** An algebraic identity: `Pσ, Pφ, Pu` are arbitrary.
Here `ℓ` is the functional `μ ↦ (λ, μ)` of the continuous multiplier, `σh, uh, lh` the discrete
solution, and `(τ, ψ, v)` discrete test functions.
Correction: the thesis needs `λ ∈ W¹` for `(λ, (S - S_h)ψ)` to make sense; only `λ ∈ W̌¹` is
available from Prop 5.2. We take `ℓ` an arbitrary linear functional (its `W`-boundedness, i.e.
`λ ∈ W¹`, enters only in Thm 5.5). The hypothesis "Prop 5.3 holds" is unnecessary.
See [QuennevilleBelair2015, Prop 5.6]. -/
theorem prop_5_6
    (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0 S0h : Y0 →ₗ[ℝ] X1) (S1 S1h : Y1 →ₗ[ℝ] X2) (ℓ : X1 →ₗ[ℝ] ℝ) (F : Y1 →ₗ[ℝ] ℝ)
    (σ Pσ σh τ : X0) (φ Pφ φh ψ : Y0) (u Pu uh v : Y1) (lh : X1)
    (c1 : ⟪σ, τ⟫ - ⟪u, dY0 ψ⟫ - ℓ (dX0 τ - S0 ψ) = 0)
    (c2 : ⟪dY0 φ, v⟫ + ⟪S1 u, S1 v⟫ + ⟪dY1 u, dY1 v⟫ = F v)
    (h1 : ⟪σh, τ⟫ - ⟪uh, dY0 ψ⟫ - ⟪lh, dX0 τ - S0h ψ⟫ = 0)
    (h2 : ⟪dY0 φh, v⟫ + ⟪S1h uh, S1h v⟫ + ⟪dY1 uh, dY1 v⟫ = F v) :
    ⟪Pσ - σh, τ⟫ - ⟪Pu - uh, dY0 ψ⟫ - (ℓ (dX0 τ - S0h ψ) - ⟪lh, dX0 τ - S0h ψ⟫)
      + ⟪dY0 (Pφ - φh), v⟫ + ⟪S1h (Pu - uh), S1h v⟫ + ⟪dY1 (Pu - uh), dY1 v⟫
    = ⟪Pσ - σ, τ⟫ - ⟪Pu - u, dY0 ψ⟫ - ℓ ((S0 - S0h) ψ)
      + ⟪dY0 (Pφ - φ), v⟫ - ⟪S1 u, (S1 - S1h) v⟫ - ⟪(S1 - S1h) u, S1h v⟫
      + ⟪S1h (Pu - u), S1h v⟫ + ⟪dY1 (Pu - u), dY1 v⟫ := by
  simp only [map_sub, LinearMap.sub_apply, inner_sub_left, inner_sub_right] at *
  linear_combination c1 - h1 + c2 - h2

/-- Thesis Thm 5.5, proof (lines 3541–3598): the coercivity identity for the test functions
`τ = e_σ - ε ρ`, `ψ = e_φ - ε χ`, `v = d e_φ + d χ + ω`, where `e_u = dχ + ω`.
Thesis gap: the `ε`'s (lost in the text) can be placed consistently only on `τ` and `ψ`;
`S_h v = S_h ω` needs `(e_σ, e_φ) ∈ Γ_h`, never stated.
See [QuennevilleBelair2015, Thm 5.5, proof]; the test-function choice is the standard
inf-sup argument for the mixed Hodge Laplacian, cf. [AFW2010], [Arnold2018]. -/
theorem thm55_lhs_identity
    (dX0 : X0 →ₗ[ℝ] X1) (dY0 : Y0 →ₗ[ℝ] Y1) (dY1 : Y1 →ₗ[ℝ] Y2)
    (S0h : Y0 →ₗ[ℝ] X1) (S1h : Y1 →ₗ[ℝ] X2)
    (hdd : ∀ x, dY1 (dY0 x) = 0)
    (eσ ρ : X0) (eφ χ : Y0) (ω : Y1) (eL : X1) (ε : ℝ)
    (hΓe : dX0 eσ = S0h eφ) (hΓ : dX0 ρ = S0h χ)
    (hSdχ : S1h (dY0 χ) = 0) (hSdeφ : S1h (dY0 eφ) = 0)
    (hωχ : ⟪ω, dY0 χ⟫ = 0) :
    ⟪eσ, eσ - ε • ρ⟫ - ⟪dY0 χ + ω, dY0 (eφ - ε • χ)⟫
      - ⟪eL, dX0 (eσ - ε • ρ) - S0h (eφ - ε • χ)⟫
      + ⟪dY0 eφ, dY0 eφ + dY0 χ + ω⟫ + ⟪S1h (dY0 χ + ω), S1h (dY0 eφ + dY0 χ + ω)⟫
      + ⟪dY1 (dY0 χ + ω), dY1 (dY0 eφ + dY0 χ + ω)⟫
    = ‖eσ‖ ^ 2 - ε * ⟪eσ, ρ⟫ + ε * ‖dY0 χ‖ ^ 2 + ‖dY0 eφ‖ ^ 2 + ‖S1h ω‖ ^ 2
      + ‖dY1 ω‖ ^ 2 := by
  simp only [map_add, map_sub, map_smul, hdd,
    hSdχ, hSdeφ, zero_add, inner_add_left, inner_add_right,
    inner_sub_right, real_inner_smul_right, ← real_inner_self_eq_norm_sq]
  rw [hΓe, hΓ, hωχ, real_inner_comm (dY0 χ) (dY0 eφ), real_inner_comm ω (dY0 eφ)]
  ring

/-- **Abstract core of Thesis Prop 5.7** (`(5.4)` for canonical projections).
`Π¹` depends only on the degrees of freedom `ℓ_k`; `Π̃⁰` preserves the degrees of freedom `m_i`;
and every `ℓ_k ∘ S₀` vanishes on the joint kernel of the `m_i` (the thesis' Leibniz-rule
computation (5.8)). Then `Π¹S₀Π̃⁰ = Π¹S₀`.
Correction: the thesis' "by density" step is invalid (canonical projections are not continuous
on `Ṽ⁰`) and unnecessary: the degree-of-freedom argument applies to every `ψ` directly.
Not formalized: the real content of Prop 5.7, the Leibniz/edge-moment computation (5.8)
establishing `hS` for Lagrange-P2 → Nédélec, is assumed here as `hS` (see `dof_hS_of_span`
for the usual sufficient condition).
See [QuennevilleBelair2015, Prop 5.7 (§5.3)]; canonical projections defined by degrees of
freedom as in [AFW2006], [Arnold2013]. -/
theorem dof_commute {Y X ι κ : Type*} [AddCommGroup Y] [Module ℝ Y] [AddCommGroup X]
    [Module ℝ X] (m : ι → Y →ₗ[ℝ] ℝ) (ℓ : κ → X →ₗ[ℝ] ℝ) (S0 : Y →ₗ[ℝ] X)
    (Pt0 : Y →ₗ[ℝ] Y) (P1 : X →ₗ[ℝ] X)
    (hP1 : ∀ x y, (∀ k, ℓ k x = ℓ k y) → P1 x = P1 y)
    (hPt0 : ∀ i ψ, m i (Pt0 ψ) = m i ψ)
    (hS : ∀ ω, (∀ i, m i ω = 0) → ∀ k, ℓ k (S0 ω) = 0) (ψ : Y) :
    P1 (S0 (Pt0 ψ)) = P1 (S0 ψ) := by
  refine hP1 _ _ fun k => ?_
  have := hS (Pt0 ψ - ψ) (fun i => by simp [hPt0]) k
  rwa [map_sub, map_sub, sub_eq_zero] at this

/-- Thesis Prop 5.7, the usual sufficient condition for `hS` of `dof_commute`: every degree of
freedom `ℓ_k ∘ S₀` of `S₀ψ` is a linear combination of the degrees of freedom `m_i` of `ψ`.
(For `S₀ = I` and Lagrange-P2 → Nédélec, each edge moment of `Iω` is `τ_e ·` a P2 edge moment
of `ω`; that concrete computation is not formalized.)
See [QuennevilleBelair2015, Prop 5.7, (5.8)]; cf. [Arnold2013], [Hiptmair2002]. -/
theorem dof_hS_of_span {Y X ι κ : Type*} [AddCommGroup Y] [Module ℝ Y] [AddCommGroup X]
    [Module ℝ X] (m : ι → Y →ₗ[ℝ] ℝ) (ℓ : κ → X →ₗ[ℝ] ℝ) (S0 : Y →ₗ[ℝ] X)
    (hspan : ∀ k, ℓ k ∘ₗ S0 ∈ Submodule.span ℝ (Set.range m)) :
    ∀ ω, (∀ i, m i ω = 0) → ∀ k, ℓ k (S0 ω) = 0 := by
  intro ω hω k
  have key : ∀ f ∈ Submodule.span ℝ (Set.range m), f ω = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hω i
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  exact key _ (hspan k)

/-- **Thesis Prop 5.7 (abstract form)**: if `Π¹` depends only on the `ℓ_k`, `Π̃⁰` preserves the
`m_i`, and each `ℓ_k ∘ S₀` lies in the span of the `m_i`, then (5.4) `Π¹S₀Π̃⁰ = Π¹S₀` holds for
every `ψ` (no density argument). See [QuennevilleBelair2015, Prop 5.7]. -/
theorem dof_commute_of_span {Y X ι κ : Type*} [AddCommGroup Y] [Module ℝ Y] [AddCommGroup X]
    [Module ℝ X] (m : ι → Y →ₗ[ℝ] ℝ) (ℓ : κ → X →ₗ[ℝ] ℝ) (S0 : Y →ₗ[ℝ] X)
    (Pt0 : Y →ₗ[ℝ] Y) (P1 : X →ₗ[ℝ] X)
    (hP1 : ∀ x y, (∀ k, ℓ k x = ℓ k y) → P1 x = P1 y)
    (hPt0 : ∀ i ψ, m i (Pt0 ψ) = m i ψ)
    (hspan : ∀ k, ℓ k ∘ₗ S0 ∈ Submodule.span ℝ (Set.range m)) (ψ : Y) :
    P1 (S0 (Pt0 ψ)) = P1 (S0 ψ) :=
  dof_commute m ℓ S0 Pt0 P1 hP1 hPt0 (dof_hS_of_span m ℓ S0 hspan) ψ

end Generic

/-! ## Part 2: the discretization of the BGG complex -/

/-- Squared graph norm `‖x‖² + ‖d x‖²` (the `V`-norm squared). -/
def gr2 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (d : E →ₗ[ℝ] F) (x : E) : ℝ :=
  ‖x‖ ^ 2 + ‖d x‖ ^ 2

/-- The squared graph norm is nonnegative. -/
theorem gr2_nonneg {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (d : E →ₗ[ℝ] F) (x : E) : 0 ≤ gr2 d x := by
  unfold gr2; positivity

/-- From `a² ≤ c²` and `c ≥ 0` to `a ≤ c`. -/
theorem le_of_sq_le {a c : ℝ} (hc : 0 ≤ c) (h : a ^ 2 ≤ c ^ 2) : a ≤ c := by
  nlinarith

/-- Squaring preserves `≤` on nonnegative reals. -/
theorem sq_le_of_le {a c : ℝ} (ha : 0 ≤ a) (h : a ≤ c) : a ^ 2 ≤ c ^ 2 := by
  nlinarith

/-- Young's inequality `xy ≤ x²/(2θ) + θy²/2`. -/
theorem young (x y : ℝ) {θ : ℝ} (hθ : 0 < θ) : x * y ≤ x ^ 2 / (2 * θ) + θ * y ^ 2 / 2 := by
  have h := sq_nonneg (x - θ * y)
  have : x * y = (x ^ 2 + θ ^ 2 * y ^ 2 - (x - θ * y) ^ 2) / (2 * θ) := by
    rw [eq_div_iff (by positivity)]; ring
  rw [this, div_le_iff₀ (by positivity)]
  have : (x ^ 2 / (2 * θ) + θ * y ^ 2 / 2) * (2 * θ) = x ^ 2 + θ ^ 2 * y ^ 2 := by
    rw [add_mul, div_mul_cancel₀ _ (by positivity)]; ring
  rw [this]; linarith

/-- Absorption step of the proof of Thm 5.5: if `κN ≤ Σ Dᵢ Lᵢ` with `Lᵢ² ≤ K N`, then
`N ≤ (#terms + 1) K / κ² · Σ Dᵢ²`. -/
theorem absorb {ι : Type*} (s : Finset ι) (Dd L : ι → ℝ) {κ K N : ℝ} (hκ : 0 < κ) (hK : 0 < K)
    (hL : ∀ i ∈ s, L i ^ 2 ≤ K * N) (h : κ * N ≤ ∑ i ∈ s, Dd i * L i) :
    N ≤ (s.card + 1) * K / κ ^ 2 * ∑ i ∈ s, Dd i ^ 2 := by
  rcases lt_or_ge N 0 with hN | hN
  · refine hN.le.trans ?_
    have := Finset.sum_nonneg (fun i (_ : i ∈ s) => sq_nonneg (Dd i))
    positivity
  set m : ℝ := s.card + 1 with hm_def
  have hm : 0 < m := by positivity
  set θ := κ / (m * K) with hθ_def
  have hθ : 0 < θ := by positivity
  have hterm : ∀ i ∈ s, Dd i * L i ≤ Dd i ^ 2 / (2 * θ) + θ * (K * N) / 2 := fun i hi => by
    have h1 := young (Dd i) (L i) hθ
    have h2 := mul_le_mul_of_nonneg_left (hL i hi) hθ.le
    linarith
  have hsum := (h.trans (Finset.sum_le_sum hterm))
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div] at hsum
  set S := ∑ i ∈ s, Dd i ^ 2
  have hθK : θ * K = κ / m := by rw [hθ_def]; field_simp
  have hcard : (s.card : ℝ) * (θ * (K * N) / 2) ≤ κ * N / 2 := by
    have : (s.card : ℝ) * (θ * (K * N) / 2) = (s.card / m) * (κ * N / 2) := by
      rw [← mul_assoc θ, hθK]; field_simp
    rw [this]
    have hc : (s.card : ℝ) / m ≤ 1 := by rw [div_le_one hm]; linarith
    have := mul_nonneg hκ.le hN
    nlinarith
  have h3 : κ * N / 2 ≤ S / (2 * θ) := by linarith
  have h4 : S / (2 * θ) = m * K / κ * S / 2 := by rw [hθ_def]; field_simp
  rw [h4] at h3
  rw [show m * K / κ ^ 2 * S = (m * K / κ * S / 2) * 2 / κ by field_simp]
  rw [le_div_iff₀ hκ]
  linarith

/-- `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
theorem sq_norm_add_le {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have := norm_add_le x y
  nlinarith [norm_nonneg (x + y), sq_nonneg (‖x‖ - ‖y‖)]

/-- `‖x - y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
theorem sq_norm_sub_le {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  simpa [sub_eq_add_neg] using sq_norm_add_le x (-y)

/-- `‖x + y + z‖² ≤ 3(‖x‖² + ‖y‖² + ‖z‖²)`. -/
theorem sq_norm_add3_le {E : Type*} [NormedAddCommGroup E] (x y z : E) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h1 := norm_add_le (x + y) z
  have h2 := norm_add_le x y
  nlinarith [norm_nonneg (x + y + z), sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖),
    sq_nonneg (‖y‖ - ‖z‖), norm_nonneg x, norm_nonneg y, norm_nonneg z, norm_nonneg (x + y)]

/-- Triangle inequality for the squared graph norm. -/
theorem gr2_sub_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (d : E →ₗ[ℝ] F) (x y : E) :
    gr2 d (x - y) ≤ 2 * gr2 d x + 2 * gr2 d y := by
  unfold gr2; rw [map_sub]
  nlinarith [sq_norm_sub_le x y, sq_norm_sub_le (d x) (d y)]

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]

/-- **Continuous (`h`-independent) hypotheses of Prop 5.3** for the BGG data `D`, in the
"type = domain with `W`-inner product" model. Each field is a property of the *continuous*
complexes (5.1) only:
* `poinc0`, `poinct0`: Poincaré inequalities on `V⁰`, `Ṽ⁰` (exactness at `V⁰`, `Ṽ⁰`);
* `exact1`: exactness of the top complex at `V¹`;
* `hodget1`: Hodge decomposition plus Poincaré on `Ṽ¹`: `v = dψ + w`, `‖w‖ ≤ C_p ‖dv‖`
  (contains exactness at `Ṽ¹`; see `hodget1_of_poincare`);
* `reg`: the regularity hypothesis `dS₀Ṽ⁰ = dV¹` *with its open-mapping constant* `C_R`
  (Banach's theorem for `dS₀ : Ṽ⁰ → dV¹`; thesis gap: the constant is used, never derived);
* `boundS0`, `boundS1`: boundedness of `S₀ : Ṽ⁰ → V¹` and `S₁ : Ṽ¹ → W²` in graph norms.

See [QuennevilleBelair2015, §5.1 (Prop 5.1), Prop 5.3]; for the concrete regular decomposition
the thesis cites [HiptmairXu2007, §3] and [Hiptmair2002, Lemma 2.4]. Poincaré inequalities and
Hodge decompositions of closed Hilbert complexes: [AFW2010], [Arnold2018], [BruningLesch1992]. -/
structure ContHyp (D : BGGData V0 V1 W2 Vt0 Vt1 Wt2) (Cp CR CS : ℝ) : Prop where
  Cp_nonneg : 0 ≤ Cp
  CR_nonneg : 0 ≤ CR
  CS_nonneg : 0 ≤ CS
  poinc0 : ∀ σ, ‖σ‖ ≤ Cp * ‖D.d0 σ‖
  poinct0 : ∀ φ, ‖φ‖ ≤ Cp * ‖D.dt0 φ‖
  exact1 : ∀ μ, D.d1 μ = 0 → ∃ ρ, D.d0 ρ = μ
  hodget1 : ∀ v, ∃ ψ w, v = D.dt0 ψ + w ∧ ‖w‖ ≤ Cp * ‖D.dt1 v‖
  reg : ∀ x, ∃ φ, D.d1 (D.S0 φ) = D.d1 x ∧ ‖D.dt0 φ‖ ≤ CR * ‖D.d1 x‖
  boundS0 : ∀ ψ, gr2 D.d1 (D.S0 ψ) ≤ CS ^ 2 * gr2 D.dt0 ψ
  boundS1 : ∀ v, ‖D.S1 v‖ ^ 2 ≤ CS ^ 2 * gr2 D.dt1 v

/-- `hodget1` is the usual Poincaré inequality on `(ker d)ᗮ` plus exactness at `Ṽ¹`.
Cf. the Hodge decomposition of a closed Hilbert complex, [AFW2010], [Arnold2018]. -/
theorem hodget1_of_poincare (D : BGGData V0 V1 W2 Vt0 Vt1 Wt2) {Cp : ℝ}
    [(LinearMap.ker D.dt1).HasOrthogonalProjection]
    (hex : LinearMap.ker D.dt1 = LinearMap.range D.dt0)
    (hP : ∀ w ∈ (LinearMap.ker D.dt1)ᗮ, ‖w‖ ≤ Cp * ‖D.dt1 w‖) (v : Vt1) :
    ∃ ψ w, v = D.dt0 ψ + w ∧ ‖w‖ ≤ Cp * ‖D.dt1 v‖ := by
  set K := LinearMap.ker D.dt1
  have hz : K.starProjection v ∈ K := K.starProjection_apply_mem v
  obtain ⟨ψ, hψ⟩ : K.starProjection v ∈ LinearMap.range D.dt0 := hex ▸ hz
  have hw := K.sub_starProjection_mem_orthogonal v
  refine ⟨ψ, v - K.starProjection v, by rw [hψ]; abel, ?_⟩
  have : D.dt1 (v - K.starProjection v) = D.dt1 v := by
    rw [map_sub, LinearMap.mem_ker.1 hz, sub_zero]
  simpa [this] using hP _ hw

/-- **Discretization of the BGG data** (thesis §5.2): finite element subspaces forming
subcomplexes, with cochain projections.
Correction: the thesis takes *canonical* projections, yet applies them (and (5.4)) to arbitrary
elements of `Ṽ⁰, Ṽ¹` produced by continuous decompositions. Here the projections are total
linear maps (bounded cochain projections, e.g. smoothed projections), idempotent on the
discrete spaces and commuting with `d`. See the caveat at `Hyp54`.
See [QuennevilleBelair2015, §5.2]; subcomplexes with (bounded, smoothed) cochain projections as
in [AFW2006], [AFW2010], [Arnold2018]. -/
structure Disc (D : BGGData V0 V1 W2 Vt0 Vt1 Wt2) where
  V0h : Submodule ℝ V0
  V1h : Submodule ℝ V1
  W2h : Submodule ℝ W2
  Vt0h : Submodule ℝ Vt0
  Vt1h : Submodule ℝ Vt1
  Wt2h : Submodule ℝ Wt2
  d0_mem : ∀ x ∈ V0h, D.d0 x ∈ V1h
  d1_mem : ∀ x ∈ V1h, D.d1 x ∈ W2h
  dt0_mem : ∀ x ∈ Vt0h, D.dt0 x ∈ Vt1h
  dt1_mem : ∀ x ∈ Vt1h, D.dt1 x ∈ Wt2h
  P0 : V0 →ₗ[ℝ] V0
  P1 : V1 →ₗ[ℝ] V1
  P2 : W2 →ₗ[ℝ] W2
  Pt0 : Vt0 →ₗ[ℝ] Vt0
  Pt1 : Vt1 →ₗ[ℝ] Vt1
  Pt2 : Wt2 →ₗ[ℝ] Wt2
  P0_mem : ∀ x, P0 x ∈ V0h
  P1_mem : ∀ x, P1 x ∈ V1h
  P2_mem : ∀ x, P2 x ∈ W2h
  Pt0_mem : ∀ x, Pt0 x ∈ Vt0h
  Pt1_mem : ∀ x, Pt1 x ∈ Vt1h
  Pt2_mem : ∀ x, Pt2 x ∈ Wt2h
  P0_id : ∀ x ∈ V0h, P0 x = x
  P1_id : ∀ x ∈ V1h, P1 x = x
  P2_id : ∀ x ∈ W2h, P2 x = x
  Pt0_id : ∀ x ∈ Vt0h, Pt0 x = x
  Pt1_id : ∀ x ∈ Vt1h, Pt1 x = x
  Pt2_id : ∀ x ∈ Wt2h, Pt2 x = x
  comm0 : ∀ x, D.d0 (P0 x) = P1 (D.d0 x)
  comm1 : ∀ x, D.d1 (P1 x) = P2 (D.d1 x)
  commt0 : ∀ x, D.dt0 (Pt0 x) = Pt1 (D.dt0 x)
  commt1 : ∀ x, D.dt1 (Pt1 x) = Pt2 (D.dt1 x)

namespace Disc

variable {D : BGGData V0 V1 W2 Vt0 Vt1 Wt2} (Q : Disc D)

/-- `S₀,h = Π¹S₀` -/
def S0h : Vt0 →ₗ[ℝ] V1 := Q.P1 ∘ₗ D.S0
/-- `S₁,h = Π²S₁` -/
def S1h : Vt1 →ₗ[ℝ] W2 := Q.P2 ∘ₗ D.S1

/-- `Z_h = N(S₁,h) ∩ N(d) ∩ Ṽ_h¹` -/
def Zh : Submodule ℝ Vt1 := Q.Vt1h ⊓ (LinearMap.ker Q.S1h ⊓ LinearMap.ker D.dt1)

/-- `Γ_h = {(σ_h, φ_h) ∈ V_h⁰ × Ṽ_h⁰ | dσ_h = S₀,h φ_h}`. -/
def Γh : Submodule ℝ (V0 × Vt0) :=
  Q.V0h.prod Q.Vt0h ⊓
    LinearMap.ker (D.d0 ∘ₗ LinearMap.fst ℝ V0 Vt0 - Q.S0h ∘ₗ LinearMap.snd ℝ V0 Vt0)

theorem mem_Γh {x : V0 × Vt0} : x ∈ Q.Γh ↔ x.1 ∈ Q.V0h ∧ x.2 ∈ Q.Vt0h ∧ D.d0 x.1 = Q.S0h x.2 := by
  simp [Γh, sub_eq_zero, and_assoc]

/-- The `h`-dependent graph norm on `Ṽ¹` (squared), the thesis' `‖·‖_{Γ_h}`.
Correction: the thesis calls it "the graph norm of `Γ_h`", but `Γ_h` is a space of pairs; the
proof only makes sense for `‖w‖² + ‖S₁,h w‖² + ‖dw‖²`. -/
def gn2 (w : Vt1) : ℝ := ‖w‖ ^ 2 + ‖Q.S1h w‖ ^ 2 + ‖D.dt1 w‖ ^ 2

/-- The surjectivity hypothesis (5.4), for the total projections: `S₀,h Π̃⁰ = Π¹ S₀`.
Caveat: the thesis checks (5.4) only for canonical projections (Prop 5.7), which do not satisfy
`Bounded`; no projection is known to us satisfying `Disc + Bounded + Hyp54` in the
elasticity / Einstein–Bianchi application (cf. `nonvacuous` for an abstract instance).
See [QuennevilleBelair2015, §5.2, (5.4), and Prop 5.7]; cf. the analogous condition in the
weak-symmetry elasticity elements of [AFW2007]. -/
def Hyp54 : Prop := ∀ ψ, Q.P1 (D.S0 (Q.Pt0 ψ)) = Q.P1 (D.S0 ψ)

/-- **Uniform (in `h`) bounds on the projections** (thesis gap: assumed implicitly in the proof
of Prop 5.3, absent from its hypotheses). Only those that are used are listed.
Uniform boundedness of the cochain projections is the key hypothesis of the FEEC stability
theory, [AFW2010, Thm 3.6], [Arnold2018]. -/
structure Bounded (CP : ℝ) : Prop where
  CP_nonneg : 0 ≤ CP
  P1 : ∀ x, gr2 D.d1 (Q.P1 x) ≤ CP ^ 2 * gr2 D.d1 x
  P2 : ∀ z, ‖Q.P2 z‖ ≤ CP * ‖z‖
  Pt1 : ∀ v, gr2 D.dt1 (Q.Pt1 v) ≤ CP ^ 2 * gr2 D.dt1 v

/-- Unfolding `S₀,h`. -/
theorem S0h_apply (ψ : Vt0) : Q.S0h ψ = Q.P1 (D.S0 ψ) := rfl
/-- Unfolding `S₁,h`. -/
theorem S1h_apply (v : Vt1) : Q.S1h v = Q.P2 (D.S1 v) := rfl
/-- `S₀,h` maps into `V_h¹`. -/
theorem S0h_mem (ψ : Vt0) : Q.S0h ψ ∈ Q.V1h := Q.P1_mem _
/-- `S₁,h` maps into `V_h²`. -/
theorem S1h_mem (v : Vt1) : Q.S1h v ∈ Q.W2h := Q.P2_mem _

/-- Thesis §5.2 (line 3304): `d S₀,h = -S₁,h d`. -/
theorem anticomm_h (ψ : Vt0) : D.d1 (Q.S0h ψ) = -Q.S1h (D.dt0 ψ) :=
  discrete_anticomm D.d1 D.dt0 D.S0 D.S1 Q.P1 Q.P2 Q.comm1 D.anticomm ψ

variable {Q}

/-- Discrete exactness at `Ṽ_h¹`, derived from continuous exactness and the cochain projections
(thesis gap: Prop 5.3 simply assumes "two exact complexes"). See
[QuennevilleBelair2015, Prop 5.3]; cf. [AFW2010], [Arnold2018] (cochain projections preserve
cohomology). -/
theorem exact_t1 {Cp CR CS : ℝ} (H : ContHyp D Cp CR CS) {u : Vt1} (hu : u ∈ Q.Vt1h)
    (hd : D.dt1 u = 0) : ∃ χ ∈ Q.Vt0h, D.dt0 χ = u := by
  obtain ⟨ψ, w, rfl, hw⟩ := H.hodget1 u
  rw [hd, norm_zero, mul_zero] at hw
  have hw0 : w = 0 := norm_le_zero_iff.1 hw
  subst hw0
  refine ⟨Q.Pt0 ψ, Q.Pt0_mem ψ, ?_⟩
  rw [Q.commt0, add_zero] at *
  exact Q.Pt1_id _ hu

/-- Discrete exactness at `V_h¹`, derived from continuous exactness and the cochain projections
(Prop 5.3 assumes it as part of "two exact complexes"; the thesis' proof of Prop 5.4 never
invokes it, yet Prop 5.4 fails without it: `prop54_counterexample_noTopExact`). See
[QuennevilleBelair2015, Prop 5.3]; cf. [AFW2010], [Arnold2018]. -/
theorem exact_1 {Cp CR CS : ℝ} (H : ContHyp D Cp CR CS) {μ : V1} (hμ : μ ∈ Q.V1h)
    (hd : D.d1 μ = 0) : ∃ ρ ∈ Q.V0h, D.d0 ρ = μ := by
  obtain ⟨ρ, hρ⟩ := H.exact1 μ hd
  exact ⟨Q.P0 ρ, Q.P0_mem ρ, by rw [Q.comm0, hρ, Q.P1_id _ hμ]⟩

/-- `d` is injective on `Ṽ⁰` (hence on `Ṽ_h⁰`). -/
theorem dt0_injective {Cp CR CS : ℝ} (H : ContHyp D Cp CR CS) : Function.Injective D.dt0 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  have := H.poinct0 φ
  rw [hφ, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

/-- **Exactness of the discrete complex (5.5) at `Ṽ_h¹`**: every `u ∈ Z_h` is `dχ` with
`(ρ, χ) ∈ Γ_h`. See [QuennevilleBelair2015, §5.2, (5.5)]. -/
theorem exact_55_h {Cp CR CS : ℝ} (H : ContHyp D Cp CR CS) {u : Vt1} (hu : u ∈ Q.Zh) :
    ∃ ρ ∈ Q.V0h, ∃ χ ∈ Q.Vt0h, D.d0 ρ = Q.S0h χ ∧ D.dt0 χ = u := by
  obtain ⟨hu1, hu2, hu3⟩ := hu
  obtain ⟨χ, hχ, rfl⟩ := exact_t1 H hu1 hu3
  obtain ⟨ρ, hρ, hρ'⟩ := exact_1 H (Q.S0h_mem χ)
    (by rw [Q.anticomm_h, LinearMap.mem_ker.1 hu2, neg_zero])
  exact ⟨ρ, hρ, χ, hχ, hρ', rfl⟩

/-- Thesis §5.2 (unlabeled, used in Thm 5.5): equation (5.6c) forces the discrete constraint
`dσ_h = S₀,h φ_h` *exactly*, since `dσ_h - S₀,hφ_h ∈ V_h¹` (as `dV_h⁰ ⊂ V_h¹`, `S₀,hṼ_h⁰ ⊂ V_h¹`)
may be taken as test function. -/
theorem cons_of_56c {σh : V0} {φh : Vt0} (hσh : σh ∈ Q.V0h)
    (h3 : ∀ μ ∈ Q.V1h, ⟪D.d0 σh - Q.S0h φh, μ⟫ = 0) : D.d0 σh = Q.S0h φh :=
  sub_eq_zero.1 (inner_self_eq_zero.1
    (h3 _ (Submodule.sub_mem _ (Q.d0_mem σh hσh) (Q.S0h_mem φh))))

/-- Thesis §5.2: (5.5) is a complex, i.e. `(S₁,h, d) ∘ (0, d) = 0` on `Γ_h`. -/
theorem complex_55 {x : V0 × Vt0} (hx : x ∈ Q.Γh) :
    Q.S1h (D.dt0 x.2) = 0 ∧ D.dt1 (D.dt0 x.2) = 0 := by
  obtain ⟨-, -, h⟩ := Q.mem_Γh.1 hx
  refine ⟨?_, D.dt1_dt0 _⟩
  have := Q.anticomm_h x.2
  rw [← h, D.d1_d0] at this
  exact neg_eq_zero.1 this.symm

/-- `Z_h` is exactly the image `d(pr₂ Γ_h)` (exactness of (5.5) at `Ṽ_h¹` plus `complex_55`). -/
theorem Zh_eq_map {Cp CR CS : ℝ} (H : ContHyp D Cp CR CS) :
    Q.Zh = Q.Γh.map (D.dt0 ∘ₗ LinearMap.snd ℝ V0 Vt0) := by
  ext u
  constructor
  · intro hu
    obtain ⟨ρ, hρ, χ, hχ, hρχ, rfl⟩ := exact_55_h H hu
    exact ⟨(ρ, χ), Q.mem_Γh.2 ⟨hρ, hχ, hρχ⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hS, hd⟩ := complex_55 hx
    exact ⟨Q.dt0_mem _ (Q.mem_Γh.1 hx).2.1, hS, hd⟩

/-- **Discrete Hodge decomposition without harmonic part** (thesis §5.2, used in Prop 5.4 and
Thm 5.5): `Ṽ_h¹ = d(pr₂ Γ_h) ⊕ (Z_hᗮ ∩ Ṽ_h¹)`, orthogonally, with unique `d`-component.
Thesis gap: used without proof; it rests on exactness of (5.5) (`exact_55_h`).
See [QuennevilleBelair2015, proofs of Prop 5.4 and Thm 5.5]; cf. the discrete Hodge
decomposition in [AFW2010], [Arnold2018]. -/
theorem decomp_55 {Cp CR CS : ℝ} (H : ContHyp D Cp CR CS) [FiniteDimensional ℝ Q.Vt1h]
    {w : Vt1} (hw : w ∈ Q.Vt1h) :
    ∃ x ∈ Q.Γh, ∃ ω ∈ Q.Vt1h, ω ∈ Q.Zhᗮ ∧ w = D.dt0 x.2 + ω ∧
      ∀ x' ∈ Q.Γh, ∀ ω' ∈ Q.Zhᗮ, w = D.dt0 x'.2 + ω' → D.dt0 x'.2 = D.dt0 x.2 ∧ ω' = ω := by
  have : FiniteDimensional ℝ Q.Zh := Submodule.finiteDimensional_of_le inf_le_left
  set z := Q.Zh.starProjection w
  have hz : z ∈ Q.Zh := Q.Zh.starProjection_apply_mem w
  have hω : w - z ∈ Q.Zhᗮ := Q.Zh.sub_starProjection_mem_orthogonal w
  have hzm : z ∈ Q.Γh.map (D.dt0 ∘ₗ LinearMap.snd ℝ V0 Vt0) := by rw [← Zh_eq_map H]; exact hz
  obtain ⟨x, hx, hxz⟩ := hzm
  simp only [LinearMap.comp_apply, LinearMap.snd_apply] at hxz
  refine ⟨x, hx, w - z, Submodule.sub_mem _ hw hz.1, hω, by rw [hxz]; abel, ?_⟩
  intro x' hx' ω' hω' hw'
  have hz' : D.dt0 x'.2 ∈ Q.Zh := by
    rw [Zh_eq_map H]; exact ⟨x', hx', rfl⟩
  -- `a := dx'₂ - z ∈ Z_h ∩ Z_hᗮ`
  have ha1 : D.dt0 x'.2 - z ∈ Q.Zh := Submodule.sub_mem _ hz' hz
  have ha2 : D.dt0 x'.2 - z ∈ Q.Zhᗮ := by
    have : D.dt0 x'.2 - z = (w - z) - ω' := by rw [hw']; abel
    rw [this]; exact Submodule.sub_mem _ hω hω'
  have ha : D.dt0 x'.2 - z = 0 :=
    inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal ha1 ha2)
  have hxz' : D.dt0 x'.2 = z := sub_eq_zero.1 ha
  refine ⟨hxz'.trans hxz.symm, ?_⟩
  rw [hw', hxz']; abel

/-- `V_h¹ = dV_h⁰ + S₀,hṼ_h⁰`, the exact condition of Prop 5.4, **derived** from (5.4), the
regular decomposition and exactness at `V¹`.
Thesis gap: the thesis derives the stronger "S₀,h onto" from an unproved surjectivity of
`Π¹S₀`. See [QuennevilleBelair2015, §5.2 and Prop 5.4]. -/
theorem hB {Cp CR CS : ℝ} (H : ContHyp D Cp CR CS) (h54 : Q.Hyp54) {μ : V1} (hμ : μ ∈ Q.V1h) :
    ∃ τ ∈ Q.V0h, ∃ ψ ∈ Q.Vt0h, D.d0 τ - Q.S0h ψ = μ := by
  obtain ⟨φ, hφ, -⟩ := H.reg μ
  obtain ⟨ρ, hρ⟩ := H.exact1 (μ - D.S0 φ) (by rw [map_sub, hφ, sub_self])
  refine ⟨Q.P0 ρ, Q.P0_mem ρ, -Q.Pt0 φ, Submodule.neg_mem _ (Q.Pt0_mem φ), ?_⟩
  rw [Q.comm0, hρ, map_neg, sub_neg_eq_add, S0h_apply, h54, ← map_add, sub_add_cancel,
    Q.P1_id _ hμ]

/-- Thesis Prop 5.3 constant (a): `C_a = (1 + C_p²) C_Π C_S`. -/
def Ca (Cp CS CP : ℝ) : ℝ := (1 + Cp ^ 2) * CP * CS

/-- **Thesis Prop 5.3(a)** (discrete Poincaré on `Γ_h`, `V`-norm form, constant uniform in `h`):
if `dσ = S₀,h φ` then `‖σ‖_V ≤ C_a ‖dφ‖`.
Correction: the thesis states only `‖σ_h‖ ≤ C‖dφ_h‖`; the proof of Thm 5.5 needs the `V`-norm
form. The constant is derived from the continuous Poincaré constant, `‖S₀‖` and the projection
bound. The thesis hypothesis "`S₀,h` uniformly bounded" is *replaced* by the graph-norm bound on
`Π¹` over all of `V¹` (`Bounded.P1`) together with `boundS0`; this is stronger than the thesis
hypothesis, which the thesis checks (Prop 5.8) for canonical projections only.
See [QuennevilleBelair2015, Prop 5.3]; cf. the discrete Poincaré inequality
[AFW2010, Thm 3.6]. -/
theorem prop_5_3_a {Cp CR CS CP : ℝ} (H : ContHyp D Cp CR CS) (B : Q.Bounded CP)
    {σ : V0} {φ : Vt0} (h : D.d0 σ = Q.S0h φ) :
    gr2 D.d0 σ ≤ Ca Cp CS CP ^ 2 * ‖D.dt0 φ‖ ^ 2 := by
  have hp := H.Cp_nonneg
  have hφ : gr2 D.dt0 φ ≤ (1 + Cp ^ 2) * ‖D.dt0 φ‖ ^ 2 := by
    have := sq_le_of_le (norm_nonneg _) (H.poinct0 φ)
    unfold gr2; nlinarith
  have hσ := sq_le_of_le (norm_nonneg _) (H.poinc0 σ)
  have hS : ‖D.d0 σ‖ ^ 2 ≤ CP ^ 2 * CS ^ 2 * ((1 + Cp ^ 2) * ‖D.dt0 φ‖ ^ 2) := by
    have h1 : ‖D.d0 σ‖ ^ 2 ≤ gr2 D.d1 (Q.P1 (D.S0 φ)) := by
      rw [h, S0h_apply]; unfold gr2; nlinarith [sq_nonneg ‖D.d1 (Q.P1 (D.S0 φ))‖]
    have h2 := B.P1 (D.S0 φ)
    have h3 := H.boundS0 φ
    calc ‖D.d0 σ‖ ^ 2 ≤ CP ^ 2 * gr2 D.d1 (D.S0 φ) := h1.trans h2
      _ ≤ CP ^ 2 * (CS ^ 2 * gr2 D.dt0 φ) := by gcongr
      _ ≤ CP ^ 2 * (CS ^ 2 * ((1 + Cp ^ 2) * ‖D.dt0 φ‖ ^ 2)) := by gcongr
      _ = _ := by ring
  unfold gr2
  calc ‖σ‖ ^ 2 + ‖D.d0 σ‖ ^ 2 ≤ (1 + Cp ^ 2) * ‖D.d0 σ‖ ^ 2 := by nlinarith
    _ ≤ (1 + Cp ^ 2) * (CP ^ 2 * CS ^ 2 * ((1 + Cp ^ 2) * ‖D.dt0 φ‖ ^ 2)) := by gcongr
    _ = Ca Cp CS CP ^ 2 * ‖D.dt0 φ‖ ^ 2 := by unfold Ca; ring

/-- Thesis Prop 5.3 constant (b). -/
def Cb (Cp CR CS CP : ℝ) : ℝ := CP * CR + CP * (1 + Cp) * (1 + CP ^ 2 * CR * CS)

/-- Uniform preimage bound for `(S₁,h; d)` on `Ṽ_h¹` (the core of the thesis' proof of
Prop 5.3(b), lines 3365–3402).
Thesis gaps filled: the regular decomposition is used with an explicit open-mapping constant;
`Π²η' = η'` needs `η' ∈ V_h²`; the final bound is `‖u'‖ ≤ C(‖w‖_V + ‖dφ‖)`, not
`‖u'‖ = ‖dφ‖ + ‖w‖`.
See [QuennevilleBelair2015, Prop 5.3, proof]; the argument follows the proof of
[AFW2010, Thm 3.6]. -/
theorem preimage_bound {Cp CR CS CP : ℝ} (H : ContHyp D Cp CR CS) (B : Q.Bounded CP)
    (h54 : Q.Hyp54) {v : Vt1} (hv : v ∈ Q.Vt1h) :
    ∃ u' ∈ Q.Vt1h, Q.S1h u' = Q.S1h v ∧ D.dt1 u' = D.dt1 v ∧
      ‖u'‖ ≤ Cb Cp CR CS CP * (‖Q.S1h v‖ + ‖D.dt1 v‖) := by
  have hp := H.Cp_nonneg; have hR := H.CR_nonneg; have hS := H.CS_nonneg
  have hP := B.CP_nonneg
  obtain ⟨ψ, w, hvw, hw⟩ := H.hodget1 v
  set ρn := ‖D.dt1 v‖ with hρn
  have hρ0 : 0 ≤ ρn := norm_nonneg _
  have hdw : D.dt1 w = D.dt1 v := by rw [hvw, map_add, D.dt1_dt0, zero_add]
  -- `‖Π̃¹w‖ ≤ C_Π (1 + C_p) ‖dv‖`
  have hgw : gr2 D.dt1 w ≤ ((1 + Cp) * ρn) ^ 2 := by
    have := sq_le_of_le (norm_nonneg _) hw
    unfold gr2; rw [hdw]; nlinarith
  have hgPw : gr2 D.dt1 (Q.Pt1 w) ≤ (CP * ((1 + Cp) * ρn)) ^ 2 := by
    calc _ ≤ CP ^ 2 * gr2 D.dt1 w := B.Pt1 w
      _ ≤ CP ^ 2 * ((1 + Cp) * ρn) ^ 2 := by gcongr
      _ = _ := by ring
  have hPw : ‖Q.Pt1 w‖ ≤ CP * ((1 + Cp) * ρn) := by
    refine le_of_sq_le (by positivity) (le_trans ?_ hgPw)
    unfold gr2; nlinarith [sq_nonneg ‖D.dt1 (Q.Pt1 w)‖]
  have hSPw : ‖Q.S1h (Q.Pt1 w)‖ ≤ CP * (CS * (CP * ((1 + Cp) * ρn))) := by
    rw [S1h_apply]
    refine (B.P2 _).trans (mul_le_mul_of_nonneg_left ?_ hP)
    refine le_of_sq_le (by positivity) ((H.boundS1 _).trans ?_)
    calc CS ^ 2 * gr2 D.dt1 (Q.Pt1 w) ≤ CS ^ 2 * (CP * ((1 + Cp) * ρn)) ^ 2 := by gcongr
      _ = _ := by ring
  -- `η' := S₁,h v - S₁,h Π̃¹w = -d Π¹ S₀ Π̃⁰ψ`
  set η' := Q.S1h v - Q.S1h (Q.Pt1 w) with hη'
  have hvP : v = D.dt0 (Q.Pt0 ψ) + Q.Pt1 w := by
    rw [Q.commt0, ← map_add, ← hvw, Q.Pt1_id _ hv]
  have hη'd : D.d1 (-(Q.S0h (Q.Pt0 ψ))) = η' := by
    rw [map_neg, Q.anticomm_h, neg_neg, hη', hvP, map_add, add_sub_cancel_right]
  obtain ⟨φ, hφ, hφn⟩ := H.reg (-(Q.S0h (Q.Pt0 ψ)))
  rw [hη'd] at hφ hφn
  have hη'mem : η' ∈ Q.W2h := Submodule.sub_mem _ (Q.S1h_mem _) (Q.S1h_mem _)
  refine ⟨Q.Pt1 w - D.dt0 (Q.Pt0 φ),
    Submodule.sub_mem _ (Q.Pt1_mem w) (Q.dt0_mem _ (Q.Pt0_mem φ)), ?_, ?_, ?_⟩
  · -- `S₁,h u' = S₁,h Π̃w - d Π¹ S₀ Π̃⁰φ = S₁,h Π̃w + Π² η' = S₁,h v`
    have : Q.S1h (D.dt0 (Q.Pt0 φ)) = -η' := by
      rw [← neg_eq_iff_eq_neg, ← Q.anticomm_h, S0h_apply, h54, Q.comm1, hφ, Q.P2_id _ hη'mem]
    rw [map_sub, this, sub_neg_eq_add, hη', add_sub_cancel]
  · rw [map_sub, D.dt1_dt0, sub_zero, Q.commt1, hdw, Q.Pt2_id _ (Q.dt1_mem _ hv)]
  · have hdφ : ‖D.dt0 (Q.Pt0 φ)‖ ≤ CP * (CR * (‖Q.S1h v‖ + CP * (CS * (CP * ((1 + Cp) * ρn))))) := by
      rw [Q.commt0]
      have h1 : ‖Q.Pt1 (D.dt0 φ)‖ ≤ CP * ‖D.dt0 φ‖ := by
        refine le_of_sq_le (by positivity) ?_
        have := B.Pt1 (D.dt0 φ)
        unfold gr2 at this; rw [D.dt1_dt0, norm_zero] at this
        nlinarith [sq_nonneg ‖D.dt1 (Q.Pt1 (D.dt0 φ))‖]
      refine h1.trans (mul_le_mul_of_nonneg_left (hφn.trans ?_) hP)
      refine mul_le_mul_of_nonneg_left ?_ hR
      exact (norm_sub_le _ _).trans (by linarith)
    have hsum := (norm_sub_le (Q.Pt1 w) (D.dt0 (Q.Pt0 φ))).trans (add_le_add hPw hdφ)
    refine hsum.trans ?_
    unfold Cb
    have hS1v := norm_nonneg (Q.S1h v)
    nlinarith [mul_nonneg hP hR, mul_nonneg (mul_nonneg hP hR) hS1v,
      mul_nonneg (mul_nonneg (mul_nonneg hP hR) (mul_nonneg hP (mul_nonneg hS hP)))
        (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + Cp) hρ0),
      mul_nonneg (mul_nonneg hP (by linarith : (0:ℝ) ≤ 1 + Cp)) hS1v,
      mul_nonneg (mul_nonneg (mul_nonneg hP (by linarith : (0:ℝ) ≤ 1 + Cp))
        (mul_nonneg (mul_nonneg (pow_nonneg hP 2) hR) hS)) hS1v]

/-- **Thesis Prop 5.3(b)** (discrete Poincaré for `(S₁,h; d)`, constant uniform in `h`):
for `u_h ∈ Ṽ_h¹` with `u_h ⊥ Z_h`, `‖u_h‖ ≤ C_b (‖S₁,h u_h‖ + ‖d u_h‖)`.
The constant `C_b` is *derived* (AFW-type argument) from the continuous constants
`C_p, C_R, C_S` and the projection bound `C_Π` only.
Thesis gaps filled: the min-norm step (from a bounded preimage to the bound for `u_h ⊥ Z_h`) is
missing in the thesis; see `preimage_bound` for the others.
See [QuennevilleBelair2015, Prop 5.3]; cf. [AFW2010, Thm 3.6], [Arnold2018]. -/
theorem prop_5_3_b {Cp CR CS CP : ℝ} (H : ContHyp D Cp CR CS) (B : Q.Bounded CP)
    (h54 : Q.Hyp54) {u : Vt1} (hu : u ∈ Q.Vt1h) (horth : u ∈ Q.Zhᗮ) :
    ‖u‖ ≤ Cb Cp CR CS CP * (‖Q.S1h u‖ + ‖D.dt1 u‖) := by
  obtain ⟨u', hu', h1, h2, h3⟩ := preimage_bound H B h54 hu
  refine (norm_le_of_sub_mem horth ?_).trans h3
  exact ⟨Submodule.sub_mem _ hu' hu, by simp [h1], by simp [h2]⟩

/-- **Thesis Prop 5.4** in the discretization: under the (corrected) hypotheses of Prop 5.3,
the discrete system (5.6) has exactly one solution `(σ_h, φ_h, u_h, λ_h)` for every `F`.
All hypotheses of `prop54_existsUnique` are *derived*: discrete anticommutation, injectivity of
`d` on `Ṽ_h⁰`, discrete exactness at `Ṽ_h¹` and `V_h¹`, and `V_h¹ = dV_h⁰ + S₀,hṼ_h⁰`.
No uniform-in-`h` bound is used. See [QuennevilleBelair2015, Prop 5.4]. -/
theorem prop_5_4 {Cp CR CS : ℝ} (H : ContHyp D Cp CR CS) (h54 : Q.Hyp54)
    [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.V1h] [FiniteDimensional ℝ Q.Vt0h]
    [FiniteDimensional ℝ Q.Vt1h] (F : Vt1 →ₗ[ℝ] ℝ) :
    ∃! x : Q.V0h × Q.Vt0h × Q.Vt1h × Q.V1h,
      (∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, ⟪(x.1 : V0), τ⟫ - ⟪(x.2.2.1 : Vt1), D.dt0 ψ⟫
        - ⟪(x.2.2.2 : V1), D.d0 τ - Q.S0h ψ⟫ = 0) ∧
      (∀ v ∈ Q.Vt1h, ⟪D.dt0 x.2.1, v⟫ + ⟪Q.S1h x.2.2.1, Q.S1h v⟫
        + ⟪D.dt1 x.2.2.1, D.dt1 v⟫ = F v) ∧
      (∀ μ ∈ Q.V1h, ⟪D.d0 x.1 - Q.S0h x.2.1, μ⟫ = 0) := by
  let dX0 := D.d0.restrict Q.d0_mem
  let dX1 := D.d1.restrict Q.d1_mem
  let dY0 := D.dt0.restrict Q.dt0_mem
  let dY1 := D.dt1.restrict Q.dt1_mem
  let S0' : Q.Vt0h →ₗ[ℝ] Q.V1h := Q.S0h.restrict (fun x _ => Q.S0h_mem x)
  let S1' : Q.Vt1h →ₗ[ℝ] Q.W2h := Q.S1h.restrict (fun x _ => Q.S1h_mem x)
  have key := prop54_existsUnique dX0 dX1 dY0 dY1 S0' S1'
    (fun ψ => Subtype.ext (by simp [dX1, S0', S1', dY0, Q.anticomm_h]))
    (fun a b hab => Subtype.ext (dt0_injective H (by simpa [dY0, Subtype.ext_iff] using hab)))
    (fun u hu => by
      obtain ⟨χ, hχ, hχu⟩ := exact_t1 H u.2 (by simpa [dY1, Subtype.ext_iff] using hu)
      exact ⟨⟨χ, hχ⟩, Subtype.ext (by simpa [dY0] using hχu)⟩)
    (fun μ hμ => by
      obtain ⟨ρ, hρ, hρμ⟩ := exact_1 H μ.2 (by simpa [dX1, Subtype.ext_iff] using hμ)
      exact ⟨⟨ρ, hρ⟩, Subtype.ext (by simpa [dX0] using hρμ)⟩)
    (fun μ => by
      obtain ⟨τ, hτ, ψ, hψ, h⟩ := hB H h54 μ.2
      exact ⟨⟨τ, hτ⟩, ⟨ψ, hψ⟩, Subtype.ext (by simpa [dX0, S0'] using h)⟩)
    (F ∘ₗ Q.Vt1h.subtype)
  refine (existsUnique_congr fun x => ?_).1 key
  simp only [Sys56, Subtype.forall, Submodule.coe_inner, LinearMap.coe_restrict_apply,
    Submodule.coe_sub, LinearMap.comp_apply, Submodule.subtype_apply, dX0, dY0, dY1, S0', S1']

/-- Triangle inequality for the squared `‖·‖_{Γ_h}` norm. -/
theorem gn2_sub_le (x y : Vt1) : Q.gn2 (x - y) ≤ 2 * Q.gn2 x + 2 * Q.gn2 y := by
  unfold gn2; simp only [map_sub]
  nlinarith [sq_norm_sub_le x y, sq_norm_sub_le (Q.S1h x) (Q.S1h y),
    sq_norm_sub_le (D.dt1 x) (D.dt1 y)]

/-- `‖·‖_{Γ_h}²` is nonnegative. -/
theorem gn2_nonneg (x : Vt1) : 0 ≤ Q.gn2 x := by unfold gn2; positivity

/-- `1 + C_a`, a version of the Prop 5.3(a) constant that is `≥ 1`. -/
def Ca1 (Cp CS CP : ℝ) : ℝ := 1 + Ca Cp CS CP

/-- The constant `K` bounding the squared norms of the Thm 5.5 test functions. -/
def KL (Cp CR CS CP : ℝ) : ℝ := 8 * (1 + Cp ^ 2) * (1 + Cb Cp CR CS CP ^ 2)

/-- **The constant of Thm 5.5**, explicit in the `h`-independent constants only:
`C_p, C_R, C_S` (continuous complex), `C_Π` (projections), `C_app` (consistency).
See [QuennevilleBelair2015, Thm 5.5] (where the constant is not made explicit). -/
def C55 (Cp CR CS CP Capp : ℝ) : ℝ :=
  2 + (2 * Ca1 Cp CS CP ^ 2 + 2 * Cp ^ 2 + 8 * Cb Cp CR CS CP ^ 2 + 8) *
    (36 * KL Cp CR CS CP * Ca1 Cp CS CP ^ 4) * (1 + Capp ^ 2)

/-- Lower bound on `KL`. -/
theorem KL_ge (Cp CR CS CP : ℝ) : 8 * (1 + Cp ^ 2) ≤ KL Cp CR CS CP := by
  unfold KL
  nlinarith only [mul_nonneg (by positivity : (0:ℝ) ≤ 1 + Cp ^ 2) (sq_nonneg (Cb Cp CR CS CP))]

/-- Lower bound on `KL`. -/
theorem KL_ge' (Cp CR CS CP : ℝ) : 8 * (1 + Cb Cp CR CS CP ^ 2) ≤ KL Cp CR CS CP := by
  unfold KL
  nlinarith only [mul_nonneg (by positivity : (0:ℝ) ≤ 1 + Cb Cp CR CS CP ^ 2) (sq_nonneg Cp)]

/-- `KL` is positive. -/
theorem KL_pos (Cp CR CS CP : ℝ) : 0 < KL Cp CR CS CP := by
  nlinarith only [KL_ge Cp CR CS CP, sq_nonneg Cp]

/-- Real-arithmetic core of the proof of Thm 5.5 (coercivity with `ε = 1/A²`, then
absorption). `a, b, c, s, t` stand for `‖e_σ‖, ‖de_φ‖, ‖dχ_h‖, ‖S₁,hω_h‖, ‖dω_h‖`. -/
theorem thm55_absorb_real {Cp Cb A K ε : ℝ} (hA : 1 ≤ A) (hε : ε = 1 / A ^ 2)
    (hK : 8 * (1 + Cp ^ 2) ≤ K) (hK' : 8 * (1 + Cb ^ 2) ≤ K)
    {a b c s t r pφ pχ o nτ ndψ nv gψ gv ip d1 d2 d3 d4 d5 d6 d7 d8 : ℝ}
    (hgψ0 : 0 ≤ gψ) (hgv0 : 0 ≤ gv)
    (hip : ip ≤ a * r) (hrc : r ^ 2 ≤ A ^ 2 * c ^ 2) (hpφ : pφ ^ 2 ≤ Cp ^ 2 * b ^ 2)
    (hpχ : pχ ^ 2 ≤ Cp ^ 2 * c ^ 2) (ho : o ^ 2 ≤ 2 * Cb ^ 2 * (s ^ 2 + t ^ 2))
    (hτ : nτ ^ 2 ≤ 2 * a ^ 2 + 2 * (ε ^ 2 * r ^ 2))
    (hdψ : ndψ ^ 2 ≤ 2 * b ^ 2 + 2 * (ε ^ 2 * c ^ 2))
    (hgψ : gψ ≤ 2 * pφ ^ 2 + 2 * (ε ^ 2 * pχ ^ 2) + ndψ ^ 2)
    (hv : nv ^ 2 ≤ 3 * (b ^ 2 + c ^ 2 + o ^ 2)) (hgv : gv = nv ^ 2 + t ^ 2)
    (hmain : a ^ 2 - ε * ip + ε * c ^ 2 + b ^ 2 + s ^ 2 + t ^ 2 ≤
      d1 * nτ + d2 * ndψ + d3 * √gψ + d4 * nv + d5 * √gv + d6 * s + d7 * s + d8 * t) :
    a ^ 2 + b ^ 2 + c ^ 2 + s ^ 2 + t ^ 2 ≤ 36 * K * A ^ 4 *
      (d1 ^ 2 + d2 ^ 2 + d3 ^ 2 + d4 ^ 2 + d5 ^ 2 + d6 ^ 2 + d7 ^ 2 + d8 ^ 2) := by
  set N := a ^ 2 + b ^ 2 + c ^ 2 + s ^ 2 + t ^ 2 with hN_def
  have hN0 : 0 ≤ N := by positivity
  have hA0 : 0 < A := by linarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεA : ε * A ^ 2 = 1 := by rw [hε]; field_simp
  have hε1 : ε ≤ 1 := by rw [hε, div_le_one (by positivity)]; nlinarith only [hA]
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith only [hε0, hε1]
  have hεc : ε ^ 2 * r ^ 2 ≤ ε * c ^ 2 := by
    calc ε ^ 2 * r ^ 2 ≤ ε ^ 2 * (A ^ 2 * c ^ 2) := by gcongr
      _ = (ε * A ^ 2) * ε * c ^ 2 := by ring
      _ = ε * c ^ 2 := by rw [hεA]; ring
  -- coercivity
  have hlow : ε / 2 * N ≤ a ^ 2 - ε * ip + ε * c ^ 2 + b ^ 2 + s ^ 2 + t ^ 2 := by
    have h2 : ε * (a * r) ≤ a ^ 2 / 2 + ε ^ 2 * r ^ 2 / 2 := by
      nlinarith only [sq_nonneg (a - ε * r)]
    have h3 := mul_le_mul_of_nonneg_left hip hε0.le
    have e1 := mul_le_mul_of_nonneg_right hε1 (sq_nonneg a)
    have e2 := mul_le_mul_of_nonneg_right hε1 (sq_nonneg b)
    have e3 := mul_le_mul_of_nonneg_right hε1 (sq_nonneg s)
    have e4 := mul_le_mul_of_nonneg_right hε1 (sq_nonneg t)
    rw [hN_def]
    nlinarith only [h2, h3, hεc, e1, e2, e3, e4]
  -- the test functions are controlled by `N`
  have hKN1 := mul_le_mul_of_nonneg_right hK hN0
  have hKN2 := mul_le_mul_of_nonneg_right hK' hN0
  have hCpN0 := mul_nonneg (sq_nonneg Cp) hN0
  have hCbN0 := mul_nonneg (sq_nonneg Cb) hN0
  have ha2 := sq_nonneg a; have hb2 := sq_nonneg b; have hc2 := sq_nonneg c
  have hs2 := sq_nonneg s; have ht2 := sq_nonneg t
  have hCpN : Cp ^ 2 * (b ^ 2 + c ^ 2) ≤ Cp ^ 2 * N :=
    mul_le_mul_of_nonneg_left (by rw [hN_def]; linarith only [ha2, hs2, ht2]) (sq_nonneg _)
  have hCbN : Cb ^ 2 * (s ^ 2 + t ^ 2) ≤ Cb ^ 2 * N :=
    mul_le_mul_of_nonneg_left (by rw [hN_def]; linarith only [ha2, hb2, hc2]) (sq_nonneg _)
  have hεc2 := mul_le_mul_of_nonneg_right hε2 hc2
  have hεc1 := mul_le_mul_of_nonneg_right hε1 hc2
  have L1 : nτ ^ 2 ≤ K * N := by
    rw [hN_def] at hKN1 hCpN0 ⊢
    nlinarith only [hτ, hεc, hεc1, hKN1, hCpN0, hb2, hs2, ht2]
  have L2' : ndψ ^ 2 ≤ 2 * b ^ 2 + 2 * c ^ 2 := by nlinarith only [hdψ, hεc2]
  have L2 : ndψ ^ 2 ≤ K * N := by
    rw [hN_def] at hKN1 hCpN0 ⊢
    nlinarith only [L2', hKN1, hCpN0, ha2, hs2, ht2]
  have L3 : √gψ ^ 2 ≤ K * N := by
    rw [Real.sq_sqrt hgψ0]
    have h2 := mul_le_mul_of_nonneg_left hpχ (sq_nonneg ε)
    have h3 : ε ^ 2 * (Cp ^ 2 * c ^ 2) ≤ Cp ^ 2 * c ^ 2 := by
      nlinarith only [hε2, mul_nonneg (sq_nonneg Cp) hc2]
    rw [hN_def] at hKN1 hCpN hCpN0 ⊢
    nlinarith only [hgψ, h2, h3, hpφ, L2', hKN1, hCpN, hCpN0, ha2, hs2, ht2]
  have hv2 : nv ^ 2 ≤ 3 * (b ^ 2 + c ^ 2) + 6 * (Cb ^ 2 * (s ^ 2 + t ^ 2)) := by
    nlinarith only [hv, ho]
  have L4 : nv ^ 2 ≤ K * N := by
    rw [hN_def] at hCbN hKN2 hCbN0 ⊢
    nlinarith only [hv2, hCbN, hKN2, hCbN0, ha2, hb2, hc2, hs2, ht2]
  have L5 : √gv ^ 2 ≤ K * N := by
    rw [Real.sq_sqrt hgv0, hgv]
    rw [hN_def] at hCbN hKN2 hCbN0 ⊢
    nlinarith only [hv2, hCbN, hKN2, hCbN0, ha2, hb2, hc2, hs2, ht2]
  have L6 : s ^ 2 ≤ K * N := by
    rw [hN_def] at hKN1 hCpN0 ⊢; nlinarith only [hKN1, hCpN0, ha2, hb2, hc2, ht2]
  have L8 : t ^ 2 ≤ K * N := by
    rw [hN_def] at hKN1 hCpN0 ⊢; nlinarith only [hKN1, hCpN0, ha2, hb2, hc2, hs2]
  have hK0 : 0 < K := by nlinarith only [hK, sq_nonneg Cp]
  have hκ : 0 < ε / 2 := by positivity
  have hsum : ε / 2 * N ≤ ∑ i : Fin 8, (![d1, d2, d3, d4, d5, d6, d7, d8] i) *
      (![nτ, ndψ, √gψ, nv, √gv, s, s, t] i) := by
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    linarith only [hlow, hmain]
  have hNb := absorb Finset.univ _ _ hκ hK0 (fun i _ => by
    fin_cases i
    · exact L1
    · exact L2
    · exact L3
    · exact L4
    · exact L5
    · exact L6
    · exact L6
    · exact L8) hsum
  have hcard : ((Finset.univ : Finset (Fin 8)).card : ℝ) + 1 = 9 := by
    rw [Finset.card_univ, Fintype.card_fin]; norm_num
  rw [hcard] at hNb
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero] at hNb
  have hκ2 : 9 * K / (ε / 2) ^ 2 = 36 * K * A ^ 4 := by
    rw [hε]; field_simp; ring
  rw [hκ2] at hNb
  linarith only [hNb]

/-- Real-arithmetic last step of the proof of Thm 5.5 (triangle inequality). -/
theorem thm55_final_real {Cp Cb A K Capp h Λ : ℝ} (hK : 0 < K) (hA : 1 ≤ A)
    {a b c s t E1 E2 E3 G3 gσ gφ g1 g2 g3 pφ q o x1 x2 x4 x7 x8 S Su : ℝ}
    (hN : a ^ 2 + b ^ 2 + c ^ 2 + s ^ 2 + t ^ 2 ≤ 36 * K * A ^ 4 *
      (x1 ^ 2 + x2 ^ 2 + (Capp * h * Λ) ^ 2 + x4 ^ 2 + (Capp * h * S) ^ 2 + Su ^ 2 + x7 ^ 2
        + x8 ^ 2))
    (hE1 : E1 ≤ 2 * gσ + 2 * g1) (hE2 : E2 ≤ 2 * gφ + 2 * g2) (hE3 : E3 ≤ 2 * G3 + 2 * g3)
    (hgσ : gσ ≤ A ^ 2 * b ^ 2) (hgφ : gφ = pφ ^ 2 + b ^ 2) (hpφ : pφ ^ 2 ≤ Cp ^ 2 * b ^ 2)
    (hG3 : G3 = q ^ 2 + s ^ 2 + t ^ 2) (hq : q ^ 2 ≤ 2 * c ^ 2 + 2 * o ^ 2)
    (ho : o ^ 2 ≤ 2 * Cb ^ 2 * (s ^ 2 + t ^ 2))
    (hx1 : x1 ^ 2 ≤ g1) (hx4 : x4 ^ 2 ≤ g2) (hg3 : g3 = x2 ^ 2 + x7 ^ 2 + x8 ^ 2)
    (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) :
    E1 + E2 + E3 ≤ (2 + (2 * A ^ 2 + 2 * Cp ^ 2 + 8 * Cb ^ 2 + 8) *
      (36 * K * A ^ 4) * (1 + Capp ^ 2)) *
      (g1 + g2 + g3 + h ^ 2 * Λ ^ 2 + h ^ 2 * S ^ 2 + Su ^ 2) := by
  set Data := g1 + g2 + g3 + h ^ 2 * Λ ^ 2 + h ^ 2 * S ^ 2 + Su ^ 2 with hData
  set N := a ^ 2 + b ^ 2 + c ^ 2 + s ^ 2 + t ^ 2 with hN_def
  have hhΛ := mul_nonneg (sq_nonneg h) (sq_nonneg Λ)
  have hhS := mul_nonneg (sq_nonneg h) (sq_nonneg S)
  have hSu := sq_nonneg Su
  have hg3' : 0 ≤ g3 := by rw [hg3]; positivity
  have hData0 : 0 ≤ Data := by rw [hData]; positivity
  have hX : x1 ^ 2 + x2 ^ 2 + (Capp * h * Λ) ^ 2 + x4 ^ 2 + (Capp * h * S) ^ 2 + Su ^ 2
      + x7 ^ 2 + x8 ^ 2 ≤ (1 + Capp ^ 2) * Data := by
    have e4 := mul_nonneg (sq_nonneg Capp) (add_nonneg (add_nonneg hg1 hg2) hg3')
    have e5 := mul_nonneg (sq_nonneg Capp) hSu
    have hid : (1 + Capp ^ 2) * Data - (x1 ^ 2 + x2 ^ 2 + (Capp * h * Λ) ^ 2 + x4 ^ 2
        + (Capp * h * S) ^ 2 + Su ^ 2 + x7 ^ 2 + x8 ^ 2)
        = (g1 - x1 ^ 2) + (g2 - x4 ^ 2) + h ^ 2 * Λ ^ 2 + h ^ 2 * S ^ 2
          + Capp ^ 2 * (g1 + g2 + g3) + Capp ^ 2 * Su ^ 2 := by
      rw [hData, hg3]; ring
    linarith only [hid, hx1, hx4, e4, e5, hhΛ, hhS]
  have hN' : N ≤ 36 * K * A ^ 4 * ((1 + Capp ^ 2) * Data) :=
    hN.trans (mul_le_mul_of_nonneg_left hX (by positivity))
  have ha2 := sq_nonneg a; have hb2 := sq_nonneg b; have hc2 := sq_nonneg c
  have hs2 := sq_nonneg s; have ht2 := sq_nonneg t
  have hbN : b ^ 2 ≤ N := by rw [hN_def]; linarith only [ha2, hc2, hs2, ht2]
  have hstN : s ^ 2 + t ^ 2 ≤ N := by rw [hN_def]; linarith only [ha2, hb2, hc2]
  have hcN : c ^ 2 ≤ N := by rw [hN_def]; linarith only [ha2, hb2, hs2, ht2]
  have hA2 := mul_le_mul_of_nonneg_left hbN (sq_nonneg A)
  have hCp2 := mul_le_mul_of_nonneg_left hbN (sq_nonneg Cp)
  have hCb2 := mul_le_mul_of_nonneg_left hstN (sq_nonneg Cb)
  have hAb := mul_le_mul_of_nonneg_left hpφ (by norm_num : (0:ℝ) ≤ 2)
  have hErr : E1 + E2 + E3 ≤ 2 * Data + (2 * A ^ 2 + 2 * Cp ^ 2 + 8 * Cb ^ 2 + 8) * N := by
    have : 2 * gσ + 2 * gφ + 2 * G3 ≤ (2 * A ^ 2 + 2 * Cp ^ 2 + 8 * Cb ^ 2 + 8) * N := by
      rw [hgφ, hG3]
      nlinarith only [hgσ, hpφ, hq, ho, hA2, hCp2, hCb2, hbN, hstN, hcN, hb2, hs2, ht2]
    rw [hData]
    linarith only [this, hE1, hE2, hE3, hhΛ, hhS, hSu]
  have hK'0 : 0 ≤ 2 * A ^ 2 + 2 * Cp ^ 2 + 8 * Cb ^ 2 + 8 := by positivity
  have := mul_le_mul_of_nonneg_left hN' hK'0
  nlinarith only [this, hErr, hData0]

/-- **Thesis Thm 5.5 (a priori error estimate), corrected and with full proof.**

Let `(σ, φ, u, λ)` solve the continuous problem (5.3) (tested against discrete functions,
by conformity), with `λ ∈ W¹` represented by the functional `ℓ = (λ, ·)`, `|ℓ μ| ≤ Λ ‖μ‖`, and let
`(σ_h, φ_h, u_h, λ_h)` solve the discrete problem (5.6) with the same right-hand side `F`.
Assume the continuous hypotheses `H`, uniformly bounded total cochain projections `B`, (5.4),
and the consistency bounds `‖(I - Π¹)S₀ψ‖ ≤ C_app h ‖ψ‖_V` on `Ṽ_h⁰`,
`‖(I - Π²)S₁v‖ ≤ C_app h ‖v‖_V` on `Ṽ_h¹`. Then
`‖σ-σ_h‖_V² + ‖φ-φ_h‖_V² + ‖u-u_h‖_{Γ_h}² ≤ C (‖Πσ-σ‖_V² + ‖Π̃φ-φ‖_V² + ‖Π̃u-u‖_{Γ_h}²`
`+ h²‖λ‖² + h²‖S₁u‖² + ‖(I-Π²)S₁u‖²)` with `C = C55 C_p C_R C_S C_Π C_app` independent of `h`.

Thesis gaps / corrections:
* `λ ∈ W¹` is needed (Prop 5.2 only gives `λ ∈ W̌¹`); here it is the hypothesis `hℓ`.
* `‖·‖_{Γ_h}` is the `h`-dependent graph norm `gn2` on `Ṽ¹`, not a norm on `Γ_h`.
* Projections are total, uniformly bounded cochain projections (`Disc`, `Bounded`).
* The discrete decomposition `Π̃u - u_h = dχ_h + ω_h` with `(ρ_h, χ_h) ∈ Γ_h` is `exact_55_h`
  (exactness of (5.5), derived); `(e_σ, e_φ) ∈ Γ_h` follows from (5.4) and commuting.
* The `ε`'s lost in the thesis are placed on `τ, ψ` only (`thm55_lhs_identity`), with
  `ε = 1/C_a²`; Prop 5.3(a) is used in its `V`-norm form; Prop 5.3(b) supplies `‖ω_h‖`.
* The constant is explicit; it depends only on `h`-independent constants.
* `λ_h` need not lie in `V_h¹`, and the continuous equations are only needed on discrete test
  functions.
* Caveat (inherited from the thesis): `B` and `h54` are imposed on the same projections; see
  `Hyp54`.

See [QuennevilleBelair2015, Thm 5.5 and Prop 5.6]; cf. the quasi-optimal a priori estimates
for the discrete mixed Hodge Laplacian in [AFW2010], [Arnold2018], the weak-symmetry
elasticity estimates of [AFW2007], and the Babuška–Brezzi theory [Babuska1971], [Brezzi1974],
[BoffiBrezziFortin2013]. -/
theorem thm_5_5 {Cp CR CS CP : ℝ} (H : ContHyp D Cp CR CS) (B : Q.Bounded CP) (h54 : Q.Hyp54)
    [FiniteDimensional ℝ Q.Vt1h]
    {h Capp : ℝ} (hh : 0 ≤ h) (hCapp : 0 ≤ Capp)
    (happ0 : ∀ ψ ∈ Q.Vt0h, ‖D.S0 ψ - Q.S0h ψ‖ ^ 2 ≤ (Capp * h) ^ 2 * gr2 D.dt0 ψ)
    (happ1 : ∀ v ∈ Q.Vt1h, ‖D.S1 v - Q.S1h v‖ ^ 2 ≤ (Capp * h) ^ 2 * gr2 D.dt1 v)
    {σ : V0} {φ : Vt0} {u : Vt1} (ℓ : V1 →ₗ[ℝ] ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hℓ : ∀ μ, |ℓ μ| ≤ Λ * ‖μ‖) (F : Vt1 →ₗ[ℝ] ℝ)
    (c1 : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, ⟪σ, τ⟫ - ⟪u, D.dt0 ψ⟫ - ℓ (D.d0 τ - D.S0 ψ) = 0)
    (c2 : ∀ v ∈ Q.Vt1h, ⟪D.dt0 φ, v⟫ + ⟪D.S1 u, D.S1 v⟫ + ⟪D.dt1 u, D.dt1 v⟫ = F v)
    (c3 : D.d0 σ = D.S0 φ)
    {σh : V0} {φh : Vt0} {uh : Vt1} {lh : V1}
    (hσh : σh ∈ Q.V0h) (hφh : φh ∈ Q.Vt0h) (huh : uh ∈ Q.Vt1h)
    (h1 : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, ⟪σh, τ⟫ - ⟪uh, D.dt0 ψ⟫ - ⟪lh, D.d0 τ - Q.S0h ψ⟫ = 0)
    (h2 : ∀ v ∈ Q.Vt1h, ⟪D.dt0 φh, v⟫ + ⟪Q.S1h uh, Q.S1h v⟫ + ⟪D.dt1 uh, D.dt1 v⟫ = F v)
    (h3 : ∀ μ ∈ Q.V1h, ⟪D.d0 σh - Q.S0h φh, μ⟫ = 0) :
    gr2 D.d0 (σ - σh) + gr2 D.dt0 (φ - φh) + Q.gn2 (u - uh) ≤
      C55 Cp CR CS CP Capp * (gr2 D.d0 (Q.P0 σ - σ) + gr2 D.dt0 (Q.Pt0 φ - φ)
        + Q.gn2 (Q.Pt1 u - u) + h ^ 2 * Λ ^ 2 + h ^ 2 * ‖D.S1 u‖ ^ 2
        + ‖D.S1 u - Q.S1h u‖ ^ 2) := by
  -- constants
  have hp := H.Cp_nonneg; have hR := H.CR_nonneg; have hS := H.CS_nonneg
  have hP := B.CP_nonneg
  set A := Ca1 Cp CS CP with hA_def
  have hCa0 : 0 ≤ Ca Cp CS CP := by unfold Ca; positivity
  have hA1 : 1 ≤ A := by rw [hA_def, Ca1]; linarith
  have h53a : ∀ {σ' : V0} {φ' : Vt0}, D.d0 σ' = Q.S0h φ' →
      gr2 D.d0 σ' ≤ A ^ 2 * ‖D.dt0 φ'‖ ^ 2 := fun hσφ => by
    refine (prop_5_3_a H B hσφ).trans ?_
    gcongr; rw [hA_def, Ca1]; linarith
  set Cb' := Cb Cp CR CS CP with hCb_def
  have hCb0 : 0 ≤ Cb' := by rw [hCb_def, Cb]; positivity
  -- step 0: the discrete constraint and `(e_σ, e_φ) ∈ Γ_h`
  have hcons : D.d0 σh = Q.S0h φh := cons_of_56c hσh h3
  obtain ⟨eσ, heσ⟩ : ∃ e, e = Q.P0 σ - σh := ⟨_, rfl⟩
  obtain ⟨eφ, heφ⟩ : ∃ e, e = Q.Pt0 φ - φh := ⟨_, rfl⟩
  have heσm : eσ ∈ Q.V0h := heσ ▸ Submodule.sub_mem _ (Q.P0_mem σ) hσh
  have heφm : eφ ∈ Q.Vt0h := heφ ▸ Submodule.sub_mem _ (Q.Pt0_mem φ) hφh
  have heum : Q.Pt1 u - uh ∈ Q.Vt1h := Submodule.sub_mem _ (Q.Pt1_mem u) huh
  have hΓe : D.d0 eσ = Q.S0h eφ := by
    rw [heσ, heφ, map_sub, map_sub, Q.comm0, c3, hcons, S0h_apply, S0h_apply, h54]
  -- step 1: the discrete decomposition `Π̃u - u_h = dχ + ω`
  have : FiniteDimensional ℝ Q.Zh := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨z, hz_def⟩ : ∃ z, z = Q.Zh.starProjection (Q.Pt1 u - uh) := ⟨_, rfl⟩
  have hz : z ∈ Q.Zh := hz_def ▸ Q.Zh.starProjection_apply_mem _
  obtain ⟨ω, hω_def⟩ : ∃ ω, ω = Q.Pt1 u - uh - z := ⟨_, rfl⟩
  have hω : ω ∈ Q.Zhᗮ := hω_def ▸ hz_def ▸ Q.Zh.sub_starProjection_mem_orthogonal _
  obtain ⟨ρ, hρ, χ, hχ, hρχ, hχz⟩ := exact_55_h H hz
  have hωm : ω ∈ Q.Vt1h := hω_def ▸ Submodule.sub_mem _ heum hz.1
  have heu : Q.Pt1 u - uh = D.dt0 χ + ω := by rw [hχz, hω_def]; abel
  have hSdχ : Q.S1h (D.dt0 χ) = 0 := by rw [hχz]; exact hz.2.1
  have hSdeφ : Q.S1h (D.dt0 eφ) = 0 := by
    have := Q.anticomm_h eφ
    rw [← hΓe, D.d1_d0] at this
    exact neg_eq_zero.1 this.symm
  have hωχ : ⟪ω, D.dt0 χ⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (hχz ▸ hz) hω
  -- step 2: test functions
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℝ, ε = 1 / A ^ 2 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε_def]; positivity
  have hεA : ε * A ^ 2 = 1 := by rw [hε_def]; field_simp
  have hε1 : ε ≤ 1 := by
    rw [hε_def, div_le_one (by positivity)]; nlinarith
  have hτm : eσ - ε • ρ ∈ Q.V0h := Submodule.sub_mem _ heσm (Submodule.smul_mem _ _ hρ)
  have hψm : eφ - ε • χ ∈ Q.Vt0h := Submodule.sub_mem _ heφm (Submodule.smul_mem _ _ hχ)
  have hvm : D.dt0 eφ + D.dt0 χ + ω ∈ Q.Vt1h :=
    Submodule.add_mem _ (Submodule.add_mem _ (Q.dt0_mem _ heφm) (Q.dt0_mem _ hχ)) hωm
  have hτψ : D.d0 (eσ - ε • ρ) - Q.S0h (eφ - ε • χ) = 0 := by
    rw [map_sub, map_sub, map_smul, map_smul, hΓe, hρχ, sub_self]
  -- step 3: error equation and coercivity identity
  have E := prop_5_6 D.d0 D.dt0 D.dt1 D.S0 Q.S0h D.S1 Q.S1h ℓ F σ (Q.P0 σ) σh (eσ - ε • ρ)
    φ (Q.Pt0 φ) φh (eφ - ε • χ) u (Q.Pt1 u) uh (D.dt0 eφ + D.dt0 χ + ω) lh
    (c1 _ hτm _ hψm) (c2 _ hvm) (h1 _ hτm _ hψm) (h2 _ hvm)
  rw [hτψ, map_zero, inner_zero_right, sub_self, sub_zero, heu, ← heσ, ← heφ] at E
  have I := thm55_lhs_identity D.d0 D.dt0 D.dt1 Q.S0h Q.S1h D.dt1_dt0 eσ ρ eφ χ ω 0 ε
    hΓe hρχ hSdχ hSdeφ hωχ
  rw [inner_zero_left, sub_zero] at I
  have key := I.symm.trans E
  have hSv : Q.S1h (D.dt0 eφ + D.dt0 χ + ω) = Q.S1h ω := by
    rw [map_add, map_add, hSdeφ, hSdχ, zero_add, zero_add]
  have hdv : D.dt1 (D.dt0 eφ + D.dt0 χ + ω) = D.dt1 ω := by
    rw [map_add, map_add, D.dt1_dt0, D.dt1_dt0, zero_add, zero_add]
  rw [hSv, hdv] at key
  -- step 4: scalar facts (Prop 5.3 and norms of the test functions)
  have hρn : ‖ρ‖ ^ 2 ≤ A ^ 2 * ‖D.dt0 χ‖ ^ 2 :=
    le_trans (le_add_of_nonneg_right (sq_nonneg _)) (h53a hρχ)
  have heσg : gr2 D.d0 eσ ≤ A ^ 2 * ‖D.dt0 eφ‖ ^ 2 := h53a hΓe
  have heφn : ‖eφ‖ ^ 2 ≤ Cp ^ 2 * ‖D.dt0 eφ‖ ^ 2 := by
    have := sq_le_of_le (norm_nonneg _) (H.poinct0 eφ); rwa [mul_pow] at this
  have hχn : ‖χ‖ ^ 2 ≤ Cp ^ 2 * ‖D.dt0 χ‖ ^ 2 := by
    have := sq_le_of_le (norm_nonneg _) (H.poinct0 χ); rwa [mul_pow] at this
  have hωn2 : ‖ω‖ ^ 2 ≤ 2 * Cb' ^ 2 * (‖Q.S1h ω‖ ^ 2 + ‖D.dt1 ω‖ ^ 2) := by
    have := sq_le_of_le (norm_nonneg _) (prop_5_3_b H B h54 hωm hω)
    rw [← hCb_def] at this
    nlinarith only [this, mul_nonneg (sq_nonneg Cb') (sq_nonneg (‖Q.S1h ω‖ - ‖D.dt1 ω‖))]
  have hτ : ‖eσ - ε • ρ‖ ^ 2 ≤ 2 * ‖eσ‖ ^ 2 + 2 * (ε ^ 2 * ‖ρ‖ ^ 2) := by
    have h1 := sq_norm_sub_le eσ (ε • ρ)
    rwa [norm_smul, Real.norm_of_nonneg hε0.le, mul_pow] at h1
  have hdψ : ‖D.dt0 (eφ - ε • χ)‖ ^ 2 ≤ 2 * ‖D.dt0 eφ‖ ^ 2 + 2 * (ε ^ 2 * ‖D.dt0 χ‖ ^ 2) := by
    have h1 := sq_norm_sub_le (D.dt0 eφ) (ε • D.dt0 χ)
    rw [norm_smul, Real.norm_of_nonneg hε0.le, mul_pow] at h1
    rwa [map_sub, map_smul]
  have hgψ : gr2 D.dt0 (eφ - ε • χ) ≤
      2 * ‖eφ‖ ^ 2 + 2 * (ε ^ 2 * ‖χ‖ ^ 2) + ‖D.dt0 (eφ - ε • χ)‖ ^ 2 := by
    have h1 := sq_norm_sub_le eφ (ε • χ)
    rw [norm_smul, Real.norm_of_nonneg hε0.le, mul_pow] at h1
    unfold gr2; linarith only [h1]
  have hv := sq_norm_add3_le (D.dt0 eφ) (D.dt0 χ) ω
  have hgv : gr2 D.dt1 (D.dt0 eφ + D.dt0 χ + ω) = ‖D.dt0 eφ + D.dt0 χ + ω‖ ^ 2 + ‖D.dt1 ω‖ ^ 2 := by
    unfold gr2; rw [hdv]
  -- step 5: term-by-term bounds of the right-hand side of the error equation
  have hz1 : ‖(D.S0 - Q.S0h) (eφ - ε • χ)‖ ≤ Capp * h * √(gr2 D.dt0 (eφ - ε • χ)) := by
    rw [LinearMap.sub_apply]
    refine le_of_sq_le (by positivity) ?_
    rw [mul_pow, Real.sq_sqrt (gr2_nonneg _ _)]; exact happ0 _ hψm
  have hz2 : ‖(D.S1 - Q.S1h) (D.dt0 eφ + D.dt0 χ + ω)‖ ≤
      Capp * h * √(gr2 D.dt1 (D.dt0 eφ + D.dt0 χ + ω)) := by
    rw [LinearMap.sub_apply]
    refine le_of_sq_le (by positivity) ?_
    rw [mul_pow, Real.sq_sqrt (gr2_nonneg _ _)]; exact happ1 _ hvm
  have b1 := real_inner_le_norm (Q.P0 σ - σ) (eσ - ε • ρ)
  have b2 : -⟪Q.Pt1 u - u, D.dt0 (eφ - ε • χ)⟫ ≤ ‖Q.Pt1 u - u‖ * ‖D.dt0 (eφ - ε • χ)‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have b3 : -ℓ ((D.S0 - Q.S0h) (eφ - ε • χ)) ≤
      (Capp * h * Λ) * √(gr2 D.dt0 (eφ - ε • χ)) := by
    refine ((neg_le_abs _).trans (hℓ _)).trans ?_
    calc Λ * ‖(D.S0 - Q.S0h) (eφ - ε • χ)‖ ≤ Λ * (Capp * h * √(gr2 D.dt0 (eφ - ε • χ))) :=
          mul_le_mul_of_nonneg_left hz1 hΛ
      _ = _ := by ring
  have b4 := real_inner_le_norm (D.dt0 (Q.Pt0 φ - φ)) (D.dt0 eφ + D.dt0 χ + ω)
  have b5 : -⟪D.S1 u, (D.S1 - Q.S1h) (D.dt0 eφ + D.dt0 χ + ω)⟫ ≤
      (Capp * h * ‖D.S1 u‖) * √(gr2 D.dt1 (D.dt0 eφ + D.dt0 χ + ω)) := by
    refine ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans ?_
    calc ‖D.S1 u‖ * ‖(D.S1 - Q.S1h) (D.dt0 eφ + D.dt0 χ + ω)‖
        ≤ ‖D.S1 u‖ * (Capp * h * √(gr2 D.dt1 (D.dt0 eφ + D.dt0 χ + ω))) :=
          mul_le_mul_of_nonneg_left hz2 (norm_nonneg _)
      _ = _ := by ring
  have b6 : -⟪(D.S1 - Q.S1h) u, Q.S1h ω⟫ ≤ ‖D.S1 u - Q.S1h u‖ * ‖Q.S1h ω‖ := by
    rw [LinearMap.sub_apply]; exact (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have b7 := real_inner_le_norm (Q.S1h (Q.Pt1 u - u)) (Q.S1h ω)
  have b8 := real_inner_le_norm (D.dt1 (Q.Pt1 u - u)) (D.dt1 ω)
  have hmain : ‖eσ‖ ^ 2 - ε * ⟪eσ, ρ⟫ + ε * ‖D.dt0 χ‖ ^ 2 + ‖D.dt0 eφ‖ ^ 2 + ‖Q.S1h ω‖ ^ 2
      + ‖D.dt1 ω‖ ^ 2 ≤ ‖Q.P0 σ - σ‖ * ‖eσ - ε • ρ‖ + ‖Q.Pt1 u - u‖ * ‖D.dt0 (eφ - ε • χ)‖
      + (Capp * h * Λ) * √(gr2 D.dt0 (eφ - ε • χ))
      + ‖D.dt0 (Q.Pt0 φ - φ)‖ * ‖D.dt0 eφ + D.dt0 χ + ω‖
      + (Capp * h * ‖D.S1 u‖) * √(gr2 D.dt1 (D.dt0 eφ + D.dt0 χ + ω))
      + ‖D.S1 u - Q.S1h u‖ * ‖Q.S1h ω‖ + ‖Q.S1h (Q.Pt1 u - u)‖ * ‖Q.S1h ω‖
      + ‖D.dt1 (Q.Pt1 u - u)‖ * ‖D.dt1 ω‖ := by
    rw [key]; linarith only [b1, b2, b3, b4, b5, b6, b7, b8]
  -- step 6: absorption (pure real arithmetic)
  have hN := thm55_absorb_real hA1 hε_def (KL_ge Cp CR CS CP) (KL_ge' Cp CR CS CP)
    (gr2_nonneg _ _) (by rw [hgv]; positivity)
    (real_inner_le_norm eσ ρ) hρn heφn hχn hωn2 hτ hdψ hgψ hv hgv hmain
  -- step 7: back to the errors
  have hE1 : gr2 D.d0 (σ - σh) ≤ 2 * gr2 D.d0 eσ + 2 * gr2 D.d0 (Q.P0 σ - σ) := by
    have : σ - σh = eσ - (Q.P0 σ - σ) := by rw [heσ]; abel
    rw [this]; exact gr2_sub_le _ _ _
  have hE2 : gr2 D.dt0 (φ - φh) ≤ 2 * gr2 D.dt0 eφ + 2 * gr2 D.dt0 (Q.Pt0 φ - φ) := by
    have : φ - φh = eφ - (Q.Pt0 φ - φ) := by rw [heφ]; abel
    rw [this]; exact gr2_sub_le _ _ _
  have hE3 : Q.gn2 (u - uh) ≤ 2 * Q.gn2 (D.dt0 χ + ω) + 2 * Q.gn2 (Q.Pt1 u - u) := by
    have : u - uh = (D.dt0 χ + ω) - (Q.Pt1 u - u) := by rw [← heu]; abel
    rw [this]; exact Q.gn2_sub_le _ _
  have hgn : Q.gn2 (D.dt0 χ + ω) = ‖D.dt0 χ + ω‖ ^ 2 + ‖Q.S1h ω‖ ^ 2 + ‖D.dt1 ω‖ ^ 2 := by
    unfold gn2; rw [map_add, hSdχ, zero_add, map_add, D.dt1_dt0, zero_add]
  have hgφ : gr2 D.dt0 eφ = ‖eφ‖ ^ 2 + ‖D.dt0 eφ‖ ^ 2 := rfl
  have hg3 : Q.gn2 (Q.Pt1 u - u) = ‖Q.Pt1 u - u‖ ^ 2 + ‖Q.S1h (Q.Pt1 u - u)‖ ^ 2
      + ‖D.dt1 (Q.Pt1 u - u)‖ ^ 2 := rfl
  rw [C55, ← hA_def, ← hCb_def]
  exact thm55_final_real (KL_pos Cp CR CS CP) hA1 hN hE1 hE2 hE3 heσg hgφ heφn hgn
    (sq_norm_add_le _ _) hωn2
    (le_add_of_nonneg_right (sq_nonneg _)) (le_add_of_nonneg_left (sq_nonneg _)) hg3
    (gr2_nonneg _ _) (gr2_nonneg _ _)

/-- The identity discretization `V_h = V`, all projections the identity (meaningful for a
finite-dimensional continuous complex). -/
def top (D : BGGData V0 V1 W2 Vt0 Vt1 Wt2) : Disc D where
  V0h := ⊤
  V1h := ⊤
  W2h := ⊤
  Vt0h := ⊤
  Vt1h := ⊤
  Wt2h := ⊤
  d0_mem _ _ := Submodule.mem_top
  d1_mem _ _ := Submodule.mem_top
  dt0_mem _ _ := Submodule.mem_top
  dt1_mem _ _ := Submodule.mem_top
  P0 := LinearMap.id
  P1 := LinearMap.id
  P2 := LinearMap.id
  Pt0 := LinearMap.id
  Pt1 := LinearMap.id
  Pt2 := LinearMap.id
  P0_mem _ := Submodule.mem_top
  P1_mem _ := Submodule.mem_top
  P2_mem _ := Submodule.mem_top
  Pt0_mem _ := Submodule.mem_top
  Pt1_mem _ := Submodule.mem_top
  Pt2_mem _ := Submodule.mem_top
  P0_id _ _ := rfl
  P1_id _ _ := rfl
  P2_id _ _ := rfl
  Pt0_id _ _ := rfl
  Pt1_id _ _ := rfl
  Pt2_id _ _ := rfl
  comm0 _ := rfl
  comm1 _ := rfl
  commt0 _ := rfl
  commt1 _ := rfl

/-- The identity discretization has uniformly bounded projections (`C_Π = 1`). -/
theorem top_bounded (D : BGGData V0 V1 W2 Vt0 Vt1 Wt2) : (top D).Bounded 1 where
  CP_nonneg := zero_le_one
  P1 x := by simp [top]
  P2 z := by simp [top]
  Pt1 v := by simp [top]

/-- The identity discretization satisfies (5.4). -/
theorem top_hyp54 (D : BGGData V0 V1 W2 Vt0 Vt1 Wt2) : (top D).Hyp54 := fun _ => rfl

end Disc

/-- A small BGG-type complex: `V⁰ = 0`, `V¹ = W² = Ṽ⁰ = Ṽ¹ = W̃² = ℝ`, `d⁰ = 0`, `d¹ = id`,
`d̃⁰ = id`, `d̃¹ = 0`, `S₀ = id`, `S₁ = -id`. -/
def exampleBGG : BGGData (EuclideanSpace ℝ (Fin 0)) ℝ ℝ ℝ ℝ ℝ where
  d0 := 0
  d1 := LinearMap.id
  dt0 := LinearMap.id
  dt1 := 0
  S0 := LinearMap.id
  S1 := -LinearMap.id
  d1_d0 _ := by simp
  dt1_dt0 _ := by simp
  anticomm _ := by simp

/-- **Non-vacuity of the hypotheses of Props 5.3, 5.4 and Thm 5.5**: `ContHyp`, `Disc`,
`Disc.Bounded` and `Disc.Hyp54` are simultaneously satisfiable with nonzero discrete spaces
and `S₁ ≠ 0` (identity discretization of `exampleBGG`, all constants `1`).
Sanity check for the hypotheses of [QuennevilleBelair2015, Props 5.3–5.4, Thm 5.5]. -/
theorem nonvacuous :
    ∃ (D : BGGData (EuclideanSpace ℝ (Fin 0)) ℝ ℝ ℝ ℝ ℝ) (Q : Disc D),
      ContHyp D 1 1 1 ∧ Q.Bounded 1 ∧ Q.Hyp54 ∧ D.S1 ≠ 0 ∧ D.S0 ≠ 0 ∧
      Q.V1h ≠ ⊥ ∧ Q.Vt0h ≠ ⊥ ∧ Q.Vt1h ≠ ⊥ := by
  refine ⟨exampleBGG, Disc.top _, ?_, Disc.top_bounded _, Disc.top_hyp54 _, ?_, ?_, ?_, ?_, ?_⟩
  · refine
      { Cp_nonneg := zero_le_one, CR_nonneg := zero_le_one, CS_nonneg := zero_le_one,
        poinc0 := fun σ => by simp [Subsingleton.elim σ 0],
        poinct0 := fun φ => by simp [exampleBGG],
        exact1 := fun μ hμ => ⟨0, by simpa [exampleBGG, eq_comm] using hμ⟩,
        hodget1 := fun v => ⟨v, 0, by simp [exampleBGG]⟩,
        reg := fun x => ⟨x, by simp [exampleBGG]⟩,
        boundS0 := fun ψ => by simp [exampleBGG, gr2],
        boundS1 := fun v => by simp [exampleBGG, gr2] }
  · intro h
    have := LinearMap.congr_fun h 1
    simp [exampleBGG] at this
  · intro h
    have := LinearMap.congr_fun h 1
    simp [exampleBGG] at this
  all_goals exact top_ne_bot

end Feec.Ch5.Discrete
