module

public import Feec.Legacy.Tensor
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Feec.TimeStepping.BlockMatrix
public import Feec.Numerics.CrankNicolsonTable
public import Feec.Physics.LinearizedGravity.PlaneWave
public import Feec.Counterexamples.LinearizedGravity
public import Feec.Geometry.WeylDecomposition
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Feec.Physics.EinsteinBianchi.Propagation

/-!
# Chapter 7: Crank–Nicolson discretization of the linearized EB system

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

Thesis Ch 7 states no theorem. It runs the full system (4.14) and the reduced system (4.15)
with Crank–Nicolson (CN) in time, then remarks (l. 4289–4291) that "for divergence-free initial
conditions, these two formulations might give equal approximations". This file proves that
remark exactly, and fills the other gaps of Ch 7.

* §1 (operator form). For finite-dimensional real inner product spaces `V0, V1, V2` (the FE
  spaces with the `L²` inner product), `d0 = grad`, `d1 = curl` with `d1 ∘ d0 = 0`, and
  `s = Δt/2`:
  - `red_to_full`: a reduced CN step, padded with `σ = 0`, is a full CN step and keeps
    `d0* E = 0` (discrete analog of Thesis Prop 4.18);
  - `red_to_full_necessary`: the hypothesis `d0* E = 0` cannot be dropped;
  - `full_step_unique`, `fullLHS_bijective`, `full_step_existsUnique`, `red_step_existsUnique`:
    both CN steps are well defined for every `s`;
  - `full_step_energy`, `Feec.TimeStepping.IsCNStep.norm_eq`, `Feec.TimeStepping.norm_eq_of_forall_isCNStep`: exact energy conservation;
  - `Feec.TimeStepping.mem_of_forall_isCNStep`: the full and reduced CN iterates coincide for all `n`, with `σⁿ = 0`;
  - `Feec.TimeStepping.mem_of_forall_isCNStep`: a full CN sequence with `σ⁰ = 0`, `d₀* E⁰ = 0` is itself a reduced
    CN sequence with `σⁿ = 0` (discrete Prop 4.18, first bullet);
  - `div_B_invariant_*`: `d2 Bⁿ` is conserved when `d2 ∘ d1 = 0`.
* §2 (matrix form). With block mass matrix `M = diag(M0, M1, M2)` and stiffness
  `K = [[0, -Gᵀ, 0], [G, 0, Cᵀ], [0, -C, 0]]`: `K` is skew, `M + sK` is invertible when the
  `Mᵢ` are SPD, the CN map conserves the `M`-energy, and `J(M + sK)`, `J = diag(-1, 1, -1)`,
  is symmetric, which is what MINRES needs (`minres_symm`).
* §3 (plane wave). The magnetic part `B` the thesis omits; `E, B` are symmetric, trace-free,
  divergence-free and solve `Ė = -curl B`, `Ḃ = curl E` classically on `ℝ³` (`planeWave_solves`).
* §4 (Table 7.1). Step counts `⌊T/Δt⌋ = 900, 1272, 1800, 2545`, and the runs on meshes 2 and 4
  stop short of `T = 7.5`.

Not formalized: convergence rates and errors (numerical), boundary conditions (the plane wave
does not satisfy the homogeneous essential BCs of (4.14); a modelling remark), and the
hybridization/preconditioner promised in the Introduction (absent from the thesis).

## References

* [QuennevilleBelair2015], Ch. 7 (numerical experiments, Tables 7.1–7.2, Figs 7.1–7.4);
  §4.10 (the systems (4.14), (4.15) and Prop 4.18); §4.3–§4.4 (constraint propagation and the
  abstract Hodge wave equation); §3.4 (Lemma 3.5) and §3.5 (gravitational plane waves)
* [Arnold2018] (FEEC framework: Hilbert complexes and their discrete subcomplexes)
* [AFW2010] (discrete Hilbert complexes and the discrete adjoint `d₀*`)
* [GilletteHolstZhu2017] (FEEC for evolution problems)
* [Hiptmair2002] (discrete de Rham complexes for electromagnetic wave problems)
* [HiptmairXu2007] (auxiliary-space AMG preconditioning in `H(curl)`, `H(div)`)
* [Wald1984] (linearized gravitational plane waves in TT gauge)
-/

open LinearMap InnerProductSpace
open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace Feec.Legacy.CrankNicolson

/-! ## §1. Operator form of the CN schemes -/

section Operator

variable {V0 V1 V2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0] [FiniteDimensional ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1] [FiniteDimensional ℝ V1]
  [NormedAddCommGroup V2] [InnerProductSpace ℝ V2] [FiniteDimensional ℝ V2]

/-- One Crank–Nicolson step, with half step `s = Δt/2`, of the discrete full EB system (4.14):
`σ̇ = d₀* E`, `Ė = -d₀ σ - d₁* B`, `Ḃ = d₁ E` (thesis operator `L`, l. 2842).

See [QuennevilleBelair2015, §4.10, (4.14)] and [QuennevilleBelair2015, Ch. 7]. -/
def FullStep (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (s : ℝ)
    (σ σ' : V0) (E E' : V1) (B B' : V2) : Prop :=
  σ' - σ = s • adjoint d0 (E' + E) ∧
  E' - E = -(s • (d0 (σ' + σ) + adjoint d1 (B' + B))) ∧
  B' - B = s • d1 (E' + E)

/-- One Crank–Nicolson step of the discrete reduced system (4.15): `Ė = -d₁* B`, `Ḃ = d₁ E`.

See [QuennevilleBelair2015, §4.10, (4.15)] and [QuennevilleBelair2015, Ch. 7]. -/
def RedStep (d1 : V1 →ₗ[ℝ] V2) (s : ℝ) (E E' : V1) (B B' : V2) : Prop :=
  E' - E = -(s • adjoint d1 (B' + B)) ∧ B' - B = s • d1 (E' + E)

/-- Discrete analog of Thesis Prop 4.18(ii) for CN (Thesis Ch 7, l. 4289–4291): a reduced CN
step keeps `d₀* E = 0`, and padded with `σ = 0` it is a full CN step.

Thesis gap: Ch 7 only says the two schemes "might give equal approximations". The equality is
exact, but it needs the discrete divergence condition `d₀* E = 0` on the data (true for the `L²`
projection of a divergence-free field, false in general for the canonical interpolant).

See [QuennevilleBelair2015, Prop 4.18] (continuous version) and [QuennevilleBelair2015, Ch. 7];
the discrete adjoint `d₀*` is that of the discrete subcomplex, cf. [AFW2010]. -/
theorem red_to_full (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (hd : d1 ∘ₗ d0 = 0)
    (s : ℝ) (E E' : V1) (B B' : V2) (h : RedStep d1 s E E' B B')
    (hE : adjoint d0 E = 0) :
    adjoint d0 E' = 0 ∧ FullStep d0 d1 s 0 0 E E' B B' := by
  obtain ⟨h1, h2⟩ := h
  have key : adjoint d0 (adjoint d1 (B' + B)) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.adjoint_comp, hd]; simp
  have hE' : adjoint d0 E' = 0 := by
    have : adjoint d0 (E' - E) = 0 := by rw [h1, map_neg, map_smul, key]; simp
    simpa [map_sub, hE, sub_eq_zero] using this
  refine ⟨hE', ?_, ?_, h2⟩
  · simp [map_add, hE, hE']
  · simpa using h1

/-- The divergence hypothesis of `red_to_full` is necessary (Thesis Ch 7, l. 4289–4291).
If `s ≠ 0` and a reduced CN step, padded with `σ = 0`, is a full CN step, then `d₀* E = 0`.
So for data with `d₀* E⁰ ≠ 0` the full scheme moves `σ` off `0` and the schemes differ.

Converse direction to [QuennevilleBelair2015, Prop 4.18], discrete CN version. -/
theorem red_to_full_necessary (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (hd : d1 ∘ₗ d0 = 0)
    {s : ℝ} (hs : s ≠ 0) (E E' : V1) (B B' : V2) (h : RedStep d1 s E E' B B')
    (hf : FullStep d0 d1 s 0 0 E E' B B') : adjoint d0 E = 0 := by
  have key : adjoint d0 (adjoint d1 (B' + B)) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.adjoint_comp, hd]; simp
  have hdiff : adjoint d0 E' = adjoint d0 E := by
    have : adjoint d0 (E' - E) = 0 := by rw [h.1, map_neg, map_smul, key]; simp
    rwa [map_sub, sub_eq_zero] at this
  have hsum : s • adjoint d0 (E' + E) = 0 := by simpa using hf.1.symm
  rw [map_add, hdiff, smul_eq_zero] at hsum
  rcases hsum with hs0 | h2
  · exact absurd hs0 hs
  · have : (2 : ℝ) • adjoint d0 E = 0 := by rw [two_smul]; exact h2
    simpa using this

/-- Uniqueness of the full CN step (Thesis Ch 7, l. 4283–4285; used implicitly).

Thesis gap: the solvability of the CN linear system `(M + sK)xⁿ⁺¹ = (M - sK)xⁿ` is never argued.
Two steps from the same state differ by `(a, b, c)` with `‖a‖² + ‖b‖² + ‖c‖² = 0`.

See [QuennevilleBelair2015, Ch. 7]; the argument is the standard energy argument for CN applied
to a skew-adjoint Hodge-wave operator, cf. [QuennevilleBelair2015, §4.4] and
[GilletteHolstZhu2017]. -/
theorem full_step_unique (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (s : ℝ)
    (σ : V0) (E : V1) (B : V2) (σ₁ σ₂ : V0) (E₁ E₂ : V1) (B₁ B₂ : V2)
    (h₁ : FullStep d0 d1 s σ σ₁ E E₁ B B₁) (h₂ : FullStep d0 d1 s σ σ₂ E E₂ B B₂) :
    σ₁ = σ₂ ∧ E₁ = E₂ ∧ B₁ = B₂ := by
  obtain ⟨a1, b1, c1⟩ := h₁
  obtain ⟨a2, b2, c2⟩ := h₂
  set a := σ₁ - σ₂ with ha_def
  set b := E₁ - E₂ with hb_def
  set c := B₁ - B₂ with hc_def
  have ha : a = s • adjoint d0 b := by
    calc a = (σ₁ - σ) - (σ₂ - σ) := by rw [ha_def]; abel
      _ = s • adjoint d0 (E₁ + E) - s • adjoint d0 (E₂ + E) := by rw [a1, a2]
      _ = s • adjoint d0 b := by
        rw [← smul_sub, ← map_sub, hb_def, add_sub_add_right_eq_sub]
  have hb : b = -(s • (d0 a + adjoint d1 c)) := by
    calc b = (E₁ - E) - (E₂ - E) := by rw [hb_def]; abel
      _ = -(s • (d0 (σ₁ + σ) + adjoint d1 (B₁ + B)))
          - -(s • (d0 (σ₂ + σ) + adjoint d1 (B₂ + B))) := by rw [b1, b2]
      _ = -(s • (d0 a + adjoint d1 c)) := by
        rw [ha_def, hc_def, map_sub, map_sub, map_add, map_add, map_add, map_add]
        simp only [smul_add, smul_sub, neg_add]; abel
  have hc : c = s • d1 b := by
    calc c = (B₁ - B) - (B₂ - B) := by rw [hc_def]; abel
      _ = s • d1 (E₁ + E) - s • d1 (E₂ + E) := by rw [c1, c2]
      _ = s • d1 b := by
        rw [← smul_sub, ← map_sub, hb_def, add_sub_add_right_eq_sub]
  have iaa : ⟪a, a⟫ = s * ⟪b, d0 a⟫ := by
    calc ⟪a, a⟫ = ⟪s • adjoint d0 b, a⟫ := by rw [← ha]
      _ = s * ⟪b, d0 a⟫ := by rw [real_inner_smul_left, LinearMap.adjoint_inner_left]
  have icc : ⟪c, c⟫ = s * ⟪d1 b, c⟫ := by
    calc ⟪c, c⟫ = ⟪c, s • d1 b⟫ := by rw [← hc]
      _ = s * ⟪d1 b, c⟫ := by rw [real_inner_smul_right, real_inner_comm]
  have ibb : ⟪b, b⟫ = -(s * ⟪b, d0 a⟫) - s * ⟪d1 b, c⟫ := by
    calc ⟪b, b⟫ = ⟪b, -(s • (d0 a + adjoint d1 c))⟫ := by rw [← hb]
      _ = -(s * ⟪b, d0 a⟫) - s * ⟪d1 b, c⟫ := by
        rw [inner_neg_right, real_inner_smul_right, inner_add_right,
          LinearMap.adjoint_inner_right]
        ring
  have hsum : ⟪a, a⟫ + ⟪b, b⟫ + ⟪c, c⟫ = 0 := by rw [iaa, ibb, icc]; ring
  have h0a := real_inner_self_nonneg (x := a)
  have h0b := real_inner_self_nonneg (x := b)
  have h0c := real_inner_self_nonneg (x := c)
  have ea : ⟪a, a⟫ = 0 := by linarith
  have eb : ⟪b, b⟫ = 0 := by linarith
  have ec : ⟪c, c⟫ = 0 := by linarith
  rw [inner_self_eq_zero, sub_eq_zero] at ea eb ec
  exact ⟨ea, eb, ec⟩

/-- The reduced CN step (4.15) is the full CN step (4.14) for `d₀ = 0` with constant `σ`
(Thesis Ch 7). -/
theorem redStep_iff_fullStep_zero (d1 : V1 →ₗ[ℝ] V2) (s : ℝ) (σ σ' : V1) (E E' : V1)
    (B B' : V2) :
    FullStep (0 : V1 →ₗ[ℝ] V1) d1 s σ σ' E E' B B' ↔ σ' = σ ∧ RedStep d1 s E E' B B' := by
  simp [FullStep, RedStep, sub_eq_zero]

/-- Uniqueness of the reduced CN step (Thesis Ch 7, (4.15) with CN). -/
theorem red_step_unique (d1 : V1 →ₗ[ℝ] V2) (s : ℝ) (E E₁ E₂ : V1) (B B₁ B₂ : V2)
    (h₁ : RedStep d1 s E E₁ B B₁) (h₂ : RedStep d1 s E E₂ B B₂) : E₁ = E₂ ∧ B₁ = B₂ := by
  have f₁ := (redStep_iff_fullStep_zero d1 s 0 0 E E₁ B B₁).2 ⟨rfl, h₁⟩
  have f₂ := (redStep_iff_fullStep_zero d1 s 0 0 E E₂ B B₂).2 ⟨rfl, h₂⟩
  exact (full_step_unique _ d1 s 0 E B 0 0 E₁ E₂ B₁ B₂ f₁ f₂).2

private theorem inner_sub_add_eq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (x y : W) : ⟪x - y, x + y⟫ = ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
  rw [inner_sub_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_comm x y]; ring

/-- Discrete energy conservation of a full CN step (Thesis Ch 7).

The conserved quantity is the total `‖σ‖² + ‖E‖² + ‖B‖²`, not `‖E‖` alone (`E` and `B` exchange
energy). This is consistent with, but does not by itself explain, the discrete "Norm of E"
values in Table 7.1; under-resolution of the `ω = 20` wave is an equally plausible cause.

See [QuennevilleBelair2015, Ch. 7, Table 7.1]; discrete analog of the energy identity for the
abstract Hodge wave equation, [QuennevilleBelair2015, §4.4]; cf. [GilletteHolstZhu2017]. -/
theorem full_step_energy (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (s : ℝ)
    (σ σ' : V0) (E E' : V1) (B B' : V2) (h : FullStep d0 d1 s σ σ' E E' B B') :
    ‖σ'‖ ^ 2 + ‖E'‖ ^ 2 + ‖B'‖ ^ 2 = ‖σ‖ ^ 2 + ‖E‖ ^ 2 + ‖B‖ ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : ⟪σ' - σ, σ' + σ⟫ = s * ⟪E' + E, d0 (σ' + σ)⟫ := by
    rw [h1, real_inner_smul_left, LinearMap.adjoint_inner_left]
  have e3 : ⟪B' - B, B' + B⟫ = s * ⟪d1 (E' + E), B' + B⟫ := by
    rw [h3, real_inner_smul_left]
  have e2 : ⟪E' - E, E' + E⟫ =
      -(s * ⟪E' + E, d0 (σ' + σ)⟫) - s * ⟪d1 (E' + E), B' + B⟫ := by
    rw [h2, inner_neg_left, real_inner_smul_left, inner_add_left,
      LinearMap.adjoint_inner_left, real_inner_comm (d0 (σ' + σ)) (E' + E),
      real_inner_comm (B' + B) (d1 (E' + E))]
    ring
  rw [inner_sub_add_eq] at e1 e2 e3
  linarith

/-- The implicit side `x ↦ (M + sK) x` of the full CN step, in operator form:
`(σ, E, B) ↦ (σ - s d₀* E, E + s (d₀ σ + d₁* B), B - s d₁ E)`. The explicit side is
`fullLHS d0 d1 (-s)`. -/
def fullLHS (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (s : ℝ) :
    (V0 × V1 × V2) →ₗ[ℝ] (V0 × V1 × V2) where
  toFun x := (x.1 - s • adjoint d0 x.2.1, x.2.1 + s • (d0 x.1 + adjoint d1 x.2.2),
    x.2.2 - s • d1 x.2.1)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> module
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, Prod.smul_mk,
      Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> module

/-- A full CN step is the linear system `(M + sK) xⁿ⁺¹ = (M - sK) xⁿ` (Thesis Ch 7). -/
theorem fullStep_iff (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (s : ℝ) (x x' : V0 × V1 × V2) :
    FullStep d0 d1 s x.1 x'.1 x.2.1 x'.2.1 x.2.2 x'.2.2 ↔
      fullLHS d0 d1 s x' = fullLHS d0 d1 (-s) x := by
  obtain ⟨σ, E, B⟩ := x
  obtain ⟨σ', E', B'⟩ := x'
  simp only [FullStep, fullLHS, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq]
  have e1 : (σ' - s • adjoint d0 E') - (σ - -s • adjoint d0 E) =
      (σ' - σ) - s • adjoint d0 (E' + E) := by rw [map_add]; module
  have e2 : (E' + s • (d0 σ' + adjoint d1 B')) - (E + -s • (d0 σ + adjoint d1 B)) =
      (E' - E) - -(s • (d0 (σ' + σ) + adjoint d1 (B' + B))) := by
    rw [map_add, map_add]; module
  have e3 : (B' - s • d1 E') - (B - -s • d1 E) = (B' - B) - s • d1 (E' + E) := by
    rw [map_add]; module
  refine and_congr ?_ (and_congr ?_ ?_)
  · rw [← sub_eq_zero, ← e1, sub_eq_zero]
  · rw [← sub_eq_zero, ← e2, sub_eq_zero]
  · rw [← sub_eq_zero, ← e3, sub_eq_zero]

/-- The CN system matrix is invertible for every `s` (Thesis Ch 7, l. 4283–4285).

Thesis gap: never argued. Injectivity is `full_step_unique`; surjectivity follows in finite
dimension.

See [QuennevilleBelair2015, Ch. 7]. -/
theorem fullLHS_bijective (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (s : ℝ) :
    Function.Bijective (fullLHS d0 d1 s) := by
  have hinj : Function.Injective (fullLHS d0 d1 s) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := (fullStep_iff d0 d1 s 0 x).2 (by rw [hx, map_zero])
    have h2 := (fullStep_iff d0 d1 s 0 0).2 (by rw [map_zero, map_zero])
    obtain ⟨e1, e2, e3⟩ := full_step_unique d0 d1 s 0 0 0 x.1 0 x.2.1 0 x.2.2 0 h1 h2
    exact Prod.ext e1 (Prod.ext e2 e3)
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The full CN step is well defined: from every state there is exactly one next state
(Thesis Ch 7, l. 4283–4285). -/
theorem full_step_existsUnique (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (s : ℝ)
    (σ : V0) (E : V1) (B : V2) :
    ∃! x' : V0 × V1 × V2, FullStep d0 d1 s σ x'.1 E x'.2.1 B x'.2.2 := by
  obtain ⟨x', hx'⟩ := (fullLHS_bijective d0 d1 s).2 (fullLHS d0 d1 (-s) (σ, E, B))
  refine ⟨x', (fullStep_iff d0 d1 s (σ, E, B) x').2 hx', fun y hy => ?_⟩
  obtain ⟨e1, e2, e3⟩ := full_step_unique d0 d1 s σ E B y.1 x'.1 y.2.1 x'.2.1 y.2.2 x'.2.2 hy
    ((fullStep_iff d0 d1 s (σ, E, B) x').2 hx')
  exact Prod.ext e1 (Prod.ext e2 e3)

/-- The reduced CN step is well defined (Thesis Ch 7, (4.15) with CN). -/
theorem red_step_existsUnique (d1 : V1 →ₗ[ℝ] V2) (s : ℝ) (E : V1) (B : V2) :
    ∃! y : V1 × V2, RedStep d1 s E y.1 B y.2 := by
  obtain ⟨x', hx', -⟩ := full_step_existsUnique (0 : V1 →ₗ[ℝ] V1) d1 s 0 E B
  have hr := ((redStep_iff_fullStep_zero d1 s 0 x'.1 E x'.2.1 B x'.2.2).1 hx').2
  refine ⟨(x'.2.1, x'.2.2), hr, fun y hy => ?_⟩
  obtain ⟨e1, e2⟩ := red_step_unique d1 s E y.1 x'.2.1 B y.2 x'.2.2 hy hr
  exact Prod.ext e1 e2

/-- The full CN time-stepping map `xⁿ ↦ xⁿ⁺¹ = (M + sK)⁻¹ (M - sK) xⁿ`. -/
def cnStep (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (s : ℝ) :
    (V0 × V1 × V2) →ₗ[ℝ] (V0 × V1 × V2) :=
  ((LinearEquiv.ofBijective (fullLHS d0 d1 s) (fullLHS_bijective d0 d1 s)).symm :
    (V0 × V1 × V2) →ₗ[ℝ] (V0 × V1 × V2)) ∘ₗ fullLHS d0 d1 (-s)

/-- `cnStep` performs a full CN step (Thesis Ch 7, (4.14) with CN). -/
theorem fullStep_cnStep (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (s : ℝ) (x : V0 × V1 × V2) :
    FullStep d0 d1 s x.1 (cnStep d0 d1 s x).1 x.2.1 (cnStep d0 d1 s x).2.1 x.2.2
      (cnStep d0 d1 s x).2.2 := by
  rw [fullStep_iff]
  exact (LinearEquiv.ofBijective (fullLHS d0 d1 s) (fullLHS_bijective d0 d1 s)).apply_symm_apply
    (fullLHS d0 d1 (-s) x)

variable {V3 : Type*} [NormedAddCommGroup V3] [InnerProductSpace ℝ V3]

/-- Discrete divergence of `B` is conserved by a full CN step when `d₂ ∘ d₁ = 0`
(Thesis Figs 7.1–7.4 plot this divergence; the thesis gives no reason for it).

See [QuennevilleBelair2015, Ch. 7, Figs 7.1–7.4]; the mechanism is the subcomplex property
`d₂ ∘ d₁ = 0` of the discrete de Rham complex, cf. [AFW2010], [Arnold2018]. -/
theorem div_B_invariant_full (d0 : V0 →ₗ[ℝ] V1) (d1 : V1 →ₗ[ℝ] V2) (d2 : V2 →ₗ[ℝ] V3)
    (hd2 : d2 ∘ₗ d1 = 0) (s : ℝ) (σ σ' : V0) (E E' : V1) (B B' : V2)
    (h : FullStep d0 d1 s σ σ' E E' B B') : d2 B' = d2 B := by
  have : d2 (B' - B) = 0 := by
    rw [h.2.2, map_smul, ← LinearMap.comp_apply, hd2, LinearMap.zero_apply, smul_zero]
  rwa [map_sub, sub_eq_zero] at this

/-- Discrete divergence of `B` is conserved by a reduced CN step when `d₂ ∘ d₁ = 0`. -/
theorem div_B_invariant_red (d1 : V1 →ₗ[ℝ] V2) (d2 : V2 →ₗ[ℝ] V3)
    (hd2 : d2 ∘ₗ d1 = 0) (s : ℝ) (E E' : V1) (B B' : V2)
    (h : RedStep d1 s E E' B B') : d2 B' = d2 B := by
  have : d2 (B' - B) = 0 := by
    rw [h.2, map_smul, ← LinearMap.comp_apply, hd2, LinearMap.zero_apply, smul_zero]
  rwa [map_sub, sub_eq_zero] at this

end Operator

/-! ## §2. Matrix form: invertibility, energy and MINRES symmetrization -/

section Matrix

open Matrix

variable {n0 n1 n2 : Type*} [Fintype n0] [Fintype n1] [Fintype n2]
  [DecidableEq n0] [DecidableEq n1] [DecidableEq n2]

/-- Index type of the coefficient vector `(σ, E, B)`. -/
abbrev Idx (n0 n1 n2 : Type*) := n0 ⊕ (n1 ⊕ n2)

/-- Block-diagonal mass matrix `M = diag(M0, M1, M2)`. -/
def massM (M0 : Matrix n0 n0 ℝ) (M1 : Matrix n1 n1 ℝ) (M2 : Matrix n2 n2 ℝ) :
    Matrix (Idx n0 n1 n2) (Idx n0 n1 n2) ℝ :=
  Matrix.of fun i j =>
    match i, j with
    | .inl i, .inl j => M0 i j
    | .inr (.inl i), .inr (.inl j) => M1 i j
    | .inr (.inr i), .inr (.inr j) => M2 i j
    | _, _ => 0

/-- Stiffness matrix `K = [[0, -Gᵀ, 0], [G, 0, Cᵀ], [0, -C, 0]]` of `M ẋ = -K x`, where
`G` represents `grad` and `C` represents `curl` (Thesis (4.14) in coordinates). -/
def stiffK (G : Matrix n1 n0 ℝ) (C : Matrix n2 n1 ℝ) :
    Matrix (Idx n0 n1 n2) (Idx n0 n1 n2) ℝ :=
  Matrix.of fun i j =>
    match i, j with
    | .inl i, .inr (.inl j) => -G j i
    | .inr (.inl i), .inl j => G i j
    | .inr (.inl i), .inr (.inr j) => C j i
    | .inr (.inr i), .inr (.inl j) => -C i j
    | _, _ => 0

/-- Sign matrix `J = diag(-I, I, -I)` flipping the `σ` and `B` block rows. -/
def signJ : Matrix (Idx n0 n1 n2) (Idx n0 n1 n2) ℝ :=
  Matrix.diagonal fun i =>
    match i with
    | .inl _ => -1
    | .inr (.inl _) => 1
    | .inr (.inr _) => -1

omit [Fintype n0] [Fintype n1] [Fintype n2]
  [DecidableEq n0] [DecidableEq n1] [DecidableEq n2] in
/-- `K` is skew-symmetric (Thesis Ch 7, l. 4283–4285). -/
theorem stiffK_transpose (G : Matrix n1 n0 ℝ) (C : Matrix n2 n1 ℝ) :
    (stiffK (n0 := n0) G C)ᵀ = -stiffK G C := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;> simp [stiffK]

omit [Fintype n0] [Fintype n1] [Fintype n2]
  [DecidableEq n0] [DecidableEq n1] [DecidableEq n2] in
/-- The block mass matrix is symmetric (Thesis Ch 7). -/
theorem massM_isSymm {M0 : Matrix n0 n0 ℝ} {M1 : Matrix n1 n1 ℝ} {M2 : Matrix n2 n2 ℝ}
    (h0 : M0.IsSymm) (h1 : M1.IsSymm) (h2 : M2.IsSymm) : (massM M0 M1 M2).IsSymm := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [massM, h0.apply, h1.apply, h2.apply]

/-- `J² = I`, so the `J`-symmetrized system is equivalent (Thesis Ch 7, MINRES). -/
theorem signJ_mul_self : (signJ : Matrix (Idx n0 n1 n2) (Idx n0 n1 n2) ℝ) * signJ = 1 := by
  rw [signJ, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; ext i
  rcases i with i | i | i <;> simp

/-- MINRES applicability (Thesis Ch 7, l. 4284–4285).

Correction (inferred gap): the thesis only says "other matrices are inverted with MINRES" and
never assembles the CN matrix. In the natural sign convention for the test functions, `M + sK`
is not symmetric, so MINRES does not apply to it directly. Multiplying the `σ` and `B` block rows by `-1` gives
`J(M + sK) = [[-M0, sGᵀ, 0], [sG, M1, sCᵀ], [0, sC, -M2]]`, which is symmetric (indefinite).

See [QuennevilleBelair2015, Ch. 7] (solver description, l. 4284–4285). -/
theorem minres_symm {M0 : Matrix n0 n0 ℝ} {M1 : Matrix n1 n1 ℝ} {M2 : Matrix n2 n2 ℝ}
    (h0 : M0.IsSymm) (h1 : M1.IsSymm) (h2 : M2.IsSymm) (G : Matrix n1 n0 ℝ)
    (C : Matrix n2 n1 ℝ) (s : ℝ) :
    (signJ * (massM M0 M1 M2 + s • stiffK G C)).IsSymm :=
  TimeStepping.isSymm_diagonal_mul_add_smul _ (massM_isSymm h0 h1 h2) (stiffK_transpose G C)
    (fun i j hij => by
      rcases i with i | i | i <;> rcases j with j | j | j <;> simp_all [massM])
    (fun i j hij => by
      rcases i with i | i | i <;> rcases j with j | j | j <;> simp_all [stiffK]) s

/-- The symmetrized system has the same solutions as the CN system, since `J² = I`. -/
theorem minres_system_iff (A : Matrix (Idx n0 n1 n2) (Idx n0 n1 n2) ℝ)
    (x b : Idx n0 n1 n2 → ℝ) : (signJ * A) *ᵥ x = signJ *ᵥ b ↔ A *ᵥ x = b :=
  TimeStepping.mulVec_diagonal_mul_iff _ (fun i => by rcases i with i | i | i <;> norm_num) A x b

/-- `xᵀ K x = 0` for skew `K` (Thesis Ch 7, CN energy argument). -/
theorem dotProduct_mulVec_skew {ι : Type*} [Fintype ι] {K : Matrix ι ι ℝ} (hK : Kᵀ = -K)
    (x : ι → ℝ) : x ⬝ᵥ (K *ᵥ x) = 0 := by
  have h : x ⬝ᵥ (K *ᵥ x) = -(x ⬝ᵥ (K *ᵥ x)) := by
    calc x ⬝ᵥ (K *ᵥ x) = (Kᵀ *ᵥ x) ⬝ᵥ x := by rw [dotProduct_mulVec, mulVec_transpose]
      _ = -(x ⬝ᵥ (K *ᵥ x)) := by rw [hK, neg_mulVec, neg_dotProduct, dotProduct_comm]
  linarith

/-- The CN matrix `M + sK` is invertible for SPD `M`, skew `K` and every real `s`
(Thesis Ch 7, l. 4283–4285).

Thesis gap: never argued. If `(M + sK)x = 0` then `0 = xᵀMx + s xᵀKx = xᵀMx`, so `x = 0`.

See [QuennevilleBelair2015, Ch. 7]. -/
theorem cn_matrix_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {M K : Matrix ι ι ℝ}
    (hM : M.PosDef) (hK : Kᵀ = -K) (s : ℝ) : (M + s • K).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := (exists_mulVec_eq_zero_iff (M := M + s • K)).2 hdet
  have hpos := hM.dotProduct_mulVec_pos hv
  rw [star_trivial] at hpos
  have : v ⬝ᵥ ((M + s • K) *ᵥ v) = v ⬝ᵥ (M *ᵥ v) := by
    rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul,
      dotProduct_mulVec_skew hK, smul_zero, add_zero]
  rw [hMv, dotProduct_zero] at this
  linarith

/-- Energy conservation of the matrix CN step: if `(M + sK)x' = (M - sK)x` with `M` symmetric
and `K` skew, then `x'ᵀMx' = xᵀMx` (Thesis Ch 7).

See [QuennevilleBelair2015, Ch. 7]; matrix form of `full_step_energy`. -/
theorem cn_matrix_energy {ι : Type*} [Fintype ι] {M K : Matrix ι ι ℝ} (hM : M.IsSymm)
    (hK : Kᵀ = -K) (s : ℝ) (x x' : ι → ℝ) (h : (M + s • K) *ᵥ x' = (M - s • K) *ᵥ x) :
    x' ⬝ᵥ (M *ᵥ x') = x ⬝ᵥ (M *ᵥ x) := by
  have h' : M *ᵥ (x' - x) = -(s • (K *ᵥ (x' + x))) := by
    rw [add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec] at h
    rw [mulVec_sub, mulVec_add, smul_add]
    linear_combination (exp := 1) h
  have hsymm : ∀ u w : ι → ℝ, u ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (M *ᵥ u) := fun u w => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hM.eq, dotProduct_comm]
  have key : (x' + x) ⬝ᵥ (M *ᵥ (x' - x)) = 0 := by
    rw [h', dotProduct_neg, dotProduct_smul, dotProduct_mulVec_skew hK, smul_zero, neg_zero]
  rw [mulVec_sub, dotProduct_sub, add_dotProduct, add_dotProduct, hsymm x x'] at key
  linarith

omit [DecidableEq n0] [DecidableEq n1] [DecidableEq n2] in
/-- The block mass matrix is SPD when its blocks are. -/
theorem massM_posDef {M0 : Matrix n0 n0 ℝ} {M1 : Matrix n1 n1 ℝ} {M2 : Matrix n2 n2 ℝ}
    (h0 : M0.PosDef) (h1 : M1.PosDef) (h2 : M2.PosDef) : (massM M0 M1 M2).PosDef := by
  have hq : ∀ x : Idx n0 n1 n2 → ℝ, x ⬝ᵥ (massM M0 M1 M2 *ᵥ x) =
      (fun i => x (.inl i)) ⬝ᵥ (M0 *ᵥ fun i => x (.inl i)) +
      ((fun i => x (.inr (.inl i))) ⬝ᵥ (M1 *ᵥ fun i => x (.inr (.inl i))) +
      (fun i => x (.inr (.inr i))) ⬝ᵥ (M2 *ᵥ fun i => x (.inr (.inr i)))) := by
    intro x
    simp [dotProduct, mulVec, Fintype.sum_sum_type, massM]
  have hsymm : (massM M0 M1 M2).IsHermitian :=
    massM_isSymm h0.isHermitian.eq h1.isHermitian.eq h2.isHermitian.eq
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hsymm fun x hx => ?_
  rw [star_trivial, hq]
  have p0 := h0.posSemidef.dotProduct_mulVec_nonneg (fun i => x (.inl i))
  have p1 := h1.posSemidef.dotProduct_mulVec_nonneg (fun i => x (.inr (.inl i)))
  have p2 := h2.posSemidef.dotProduct_mulVec_nonneg (fun i => x (.inr (.inr i)))
  simp only [star_trivial] at p0 p1 p2
  by_cases e0 : (fun i => x (.inl i)) = 0
  · by_cases e1 : (fun i => x (.inr (.inl i))) = 0
    · have e2 : (fun i => x (.inr (.inr i))) ≠ 0 := by
        intro e2; apply hx; ext i
        rcases i with i | i | i
        · exact congrFun e0 i
        · exact congrFun e1 i
        · exact congrFun e2 i
      have := h2.dotProduct_mulVec_pos e2
      rw [star_trivial] at this
      linarith
    · have := h1.dotProduct_mulVec_pos e1
      rw [star_trivial] at this
      linarith
  · have := h0.dotProduct_mulVec_pos e0
    rw [star_trivial] at this
    linarith

/-- The CN matrix of the full EB system is invertible for every `s` (Thesis Ch 7, (4.14) with
CN and SPD mass matrices).

See [QuennevilleBelair2015, §4.10, (4.14)] and [QuennevilleBelair2015, Ch. 7]. -/
theorem cn_invertible {M0 : Matrix n0 n0 ℝ} {M1 : Matrix n1 n1 ℝ} {M2 : Matrix n2 n2 ℝ}
    (h0 : M0.PosDef) (h1 : M1.PosDef) (h2 : M2.PosDef) (G : Matrix n1 n0 ℝ)
    (C : Matrix n2 n1 ℝ) (s : ℝ) : IsUnit (massM M0 M1 M2 + s • stiffK G C) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact cn_matrix_det_ne_zero (massM_posDef h0 h1 h2) (stiffK_transpose G C) s

end Matrix

end Feec.Legacy.CrankNicolson
