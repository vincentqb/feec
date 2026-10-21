module

public import Feec.HilbertComplex.BGG.Basic
public import Feec.Variational.GalerkinEvolution
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The time-dependent BGG problem and its discretization

The Hodge wave equation of the complex with weak symmetries (5.1): the problem (6.1) with the
constraint `dσ = Sφ` imposed strongly, the multiplier problem (6.2), the semi-discrete
differential-algebraic system (6.3), and their error equations. Real scalars.

## Main definitions

* `Feec.BGG.WaveData`: continuous data ("type = domain" model with explicit inclusions);
  `WaveData.Wcheck`: the multiplier space `W̌¹ = closure J(W¹) ⊆ (V⁰ × Ṽ⁰)*`.
* `WaveData.Solution`, `WaveData.MultiplierSolution`: solutions of (6.1) and (6.2).
* `Feec.BGG.DiscreteSolution D T f`: solutions of (6.3) for discrete BGG data
  `D : Feec.BGG.Segment ℝ …`; `Feec.BGG.phiMap`: the algebraic variable `φₕ = Φ(σₕ, f)`.

## Main results

* `WaveData.Solution.exists_multiplierSolution` and its variants: every solution of (6.1) has a
  unique multiplier `Λ(t) ∈ W̌¹` (thesis Prop 6.1, corrected); `Solution.unique`,
  `MultiplierSolution.unique` by energy.
* `DiscreteSolution.compatible`: necessary compatibility conditions (C1)–(C3);
  `exists_discreteSolution_iff`: existence ⇔ (C1)–(C3) (thesis Prop 6.2, corrected);
  `exists_discreteSolution_iff_compatible_u`, `exists_discreteSolution_unique`: for dynamic
  data, existence ⇔ (C2), with the forced algebraic datum `φₕ(0) = Φ(σ₀, f(0))`;
  `DiscreteSolution.unique`.
* `Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`: thesis Prop 6.2
  as stated is false.
* `errorEq_a` … `errorEq_e`, `errorEq_c_split`: the error equations (thesis Prop 6.3, completed).
* `norm_sub_le_of_ellipticProjection`, `DiscreteSolution.norm_sub_le_of_ellipticProjection`,
  `exists_discreteSolution_norm_sub_le`: convergence through an elliptic projection, with the
  projected initial data shown admissible (`projected_compatible_u`) and the projected algebraic
  datum not admissible in general
  (`Feec.Counterexamples.ConstrainedEvolution.not_projected_compatible_phi`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 6 (§6.1 (6.1)/(6.2), Prop 6.1; §6.2 (6.3), Prop 6.2, (6.4), Prop 6.3); Ch. 5 (§5.1 the
  complex (5.1) and `|||λ|||`)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018] (Hilbert complexes and their
  approximation)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
  (Hilbert complexes and their approximation)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
  (Hilbert complexes and their approximation)
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021] (the BGG construction)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.1, Ch. 4 (variation of constants)
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]
  (FEEC for evolution problems)
* [T. Geveci, *On the application of mixed finite element methods to the wave equations*][Geveci1988]
* [G. A. Baker, *Error estimates for finite element methods for second order hyperbolic equations*][Baker1976]
* [T. Dupont, *L²-estimates for Galerkin methods for second order hyperbolic equations*][Dupont1973]
* [F. Brezzi, *On the existence, uniqueness and approximation of saddle-point problems arising from Lagrangian multipliers*][Brezzi1974]
  (Lagrange multipliers)
* [D. Boffi, F. Brezzi, M. Fortin, *Mixed Finite Element Methods and Applications*][BoffiBrezziFortin2013]
  (Lagrange multipliers)
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.BGG


/-- Auxiliary: two functions that agree on `[0,T]` have the same right derivative at every
`t ∈ [0,T)`. -/
lemma hasDerivWithinAt_Ici_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g₁ g₂ : ℝ → E} {g₁' g₂' : E} {t T : ℝ} (ht : t ∈ Ico 0 T)
    (hg : ∀ x ∈ Icc 0 T, g₁ x = g₂ x)
    (h₁ : HasDerivWithinAt g₁ g₁' (Ici t) t) (h₂ : HasDerivWithinAt g₂ g₂' (Ici t) t) :
    g₁' = g₂' := by
  have h1 : HasDerivWithinAt g₁ g₁' (Icc t T) t := h₁.mono Icc_subset_Ici_self
  have h2 : HasDerivWithinAt g₁ g₂' (Icc t T) t :=
    (h₂.mono Icc_subset_Ici_self).congr (fun x hx => hg x ⟨ht.1.trans hx.1, hx.2⟩)
      (hg t (Ico_subset_Icc_self ht))
  exact (uniqueDiffOn_Icc ht.2 t ⟨le_rfl, ht.2.le⟩).eq_deriv _ h1 h2

/-- Auxiliary: a function vanishing on `[0,T]` has zero right derivative on `[0,T)`. -/
lemma hasDerivWithinAt_Ici_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} {g' : E} {t T : ℝ} (ht : t ∈ Ico 0 T) (hg : ∀ x ∈ Icc 0 T, g x = 0)
    (h : HasDerivWithinAt g g' (Ici t) t) : g' = 0 :=
  hasDerivWithinAt_Ici_unique ht (g₂ := fun _ => (0 : E)) hg h (hasDerivWithinAt_const _ _ _)

/-! ## §1. The continuous problems (6.1) and (6.2) -/

/-- Continuous data of §6.1 ("type = domain" model with explicit inclusions).
`V0, Ṽ0` are Hilbert spaces (graph norms); the `W`'s are the ambient Hilbert spaces.
`i0 : V⁰ → W⁰` and `it1 : Ṽ¹ → W̃¹` are the inclusions, `d0, dt0, dt1` the differentials and
`S0, S1` the BGG connecting maps, all already composed with the inclusions. -/
structure WaveData (V0 Vt0 Vt1 W0 W1 W2 Wt1 Wt2 : Type*)
    [NormedAddCommGroup V0] [InnerProductSpace ℝ V0] [CompleteSpace V0]
    [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0] [CompleteSpace Vt0]
    [AddCommGroup Vt1] [Module ℝ Vt1]
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
    [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1]
    [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2] where
  i0 : V0 →L[ℝ] W0
  d0 : V0 →L[ℝ] W1
  S0 : Vt0 →L[ℝ] W1
  dt0 : Vt0 →L[ℝ] Wt1
  it1 : Vt1 →ₗ[ℝ] Wt1
  dt1 : Vt1 →ₗ[ℝ] Wt2
  S1 : Vt1 →ₗ[ℝ] W2
  i0_injective : Function.Injective i0
  it1_injective : Function.Injective it1

namespace WaveData

variable {V0 Vt0 Vt1 W0 W1 W2 Wt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0] [CompleteSpace V0]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0] [CompleteSpace Vt0]
  [AddCommGroup Vt1] [Module ℝ Vt1]
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  (D : WaveData V0 Vt0 Vt1 W0 W1 W2 Wt1 Wt2)

/-- The Hilbert space `V⁰ × Ṽ⁰` (ℓ² product of the graph norms). -/
abbrev X (V0 Vt0 : Type*) [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
    [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0] := WithLp 2 (V0 × Vt0)

/-- The constraint operator `B(τ, ψ) = dτ − Sψ : V⁰ × Ṽ⁰ → W¹`; `Γ = ker B`. -/
def B : X V0 Vt0 →L[ℝ] W1 :=
  (D.d0.comp (ContinuousLinearMap.fst ℝ V0 Vt0) - D.S0.comp (ContinuousLinearMap.snd ℝ V0 Vt0)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ V0 Vt0).toContinuousLinearMap

/-- `B(τ, ψ) = dτ − Sψ`. -/
@[simp] lemma B_toLp (τ : V0) (ψ : Vt0) : D.B (WithLp.toLp 2 (τ, ψ)) = D.d0 τ - D.S0 ψ := rfl

/-- `J λ = ⟨λ, d· − S·⟩ ∈ (V⁰ × Ṽ⁰)*`. Its dual norm `‖J λ‖` is the thesis' norm `|||λ|||`
(§5.1, with the equivalent ℓ²-product norm on `V⁰ × Ṽ⁰`). -/
def J : W1 →L[ℝ] StrongDual ℝ (X V0 Vt0) :=
  (InnerProductSpace.toDual ℝ (X V0 Vt0)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.adjoint D.B)

/-- `J λ (τ, ψ) = (λ, dτ − Sψ)`. -/
lemma J_apply (μ : W1) (x : X V0 Vt0) : D.J μ x = ⟪μ, D.B x⟫ := by
  simp [J, InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]

/-- **The multiplier space `W̌¹`**: the closure of `J(W¹)` in the (complete) dual
`(V⁰ × Ṽ⁰)*`. This is the completion of `W¹ / ker J` for the seminorm `|||·||| = ‖J ·‖`; it is the
completion of `(W¹, |||·|||)` itself exactly when `J` is injective, i.e. when `range B` is dense
in `W¹` (the thesis assumes `S Ṽ⁰` dense in `W¹`; `WaveData` does not). An element `Λ ∈ W̌¹`
pairs with `(τ, ψ)` as `Λ(τ, ψ)`, extending `(λ, dτ − Sψ)`.
See [QuennevilleBelair2015], §6.1 (`W̌¹`) and [QuennevilleBelair2015], §5.1 (`|||λ|||`). -/
def Wcheck : Submodule ℝ (StrongDual ℝ (X V0 Vt0)) := D.J.range.topologicalClosure

/-- `W¹ ⊆ W̌¹` via `J`. -/
lemma J_mem_Wcheck (μ : W1) : D.J μ ∈ D.Wcheck :=
  Submodule.le_topologicalClosure _ ⟨μ, rfl⟩

/-- Every multiplier in `W̌¹` annihilates `Γ = ker B`. -/
theorem Wcheck_vanish {Λ : StrongDual ℝ (X V0 Vt0)} (hΛ : Λ ∈ D.Wcheck) {x : X V0 Vt0}
    (hx : D.B x = 0) : Λ x = 0 := by
  have hcl : IsClosed {Λ : StrongDual ℝ (X V0 Vt0) | Λ x = 0} :=
    isClosed_eq (ContinuousLinearMap.apply ℝ ℝ x).continuous continuous_const
  refine closure_minimal (s := (D.J.range : Set _)) ?_ hcl
    (by rwa [← Submodule.topologicalClosure_coe])
  rintro _ ⟨μ, rfl⟩
  simp [J_apply, hx]

/-- **Annihilator characterisation of `W̌¹`** (the content of Prop 6.1(i)): a bounded
functional on `V⁰ × Ṽ⁰` vanishing on `Γ` lies in `W̌¹`. Proof: Riesz, then
`(ker B)ᗮ = closure (range B*)`. See [QuennevilleBelair2015], Prop 6.1; cf. the closed-range
theory of Hilbert complexes in [BruningLesch1992] and [AFW2010]. -/
theorem mem_Wcheck_of_vanish (ℓ : StrongDual ℝ (X V0 Vt0)) (hℓ : ∀ x, D.B x = 0 → ℓ x = 0) :
    ℓ ∈ D.Wcheck := by
  set g := (InnerProductSpace.toDual ℝ (X V0 Vt0)).symm ℓ
  have hg : g ∈ (D.B.ker)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    exact hℓ x hx
  rw [ContinuousLinearMap.orthogonal_ker] at hg
  have hg' : g ∈ closure ((ContinuousLinearMap.adjoint D.B).range : Set _) := by
    rwa [← Submodule.topologicalClosure_coe]
  have hcont : Continuous (InnerProductSpace.toDual ℝ (X V0 Vt0)) :=
    (InnerProductSpace.toDual ℝ (X V0 Vt0)).continuous
  have := map_mem_closure hcont hg' (t := (D.J.range : Set _)) (by
    rintro _ ⟨μ, rfl⟩
    exact ⟨μ, rfl⟩)
  have h : ℓ ∈ closure (D.J.range : Set _) := by simpa [g] using this
  rwa [Wcheck, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]

/-- Under closed range of `B = (d, −S)` the completion is not needed: `W̌¹ = J(W¹)`, i.e. every
multiplier is a genuine `λ ∈ W¹`. Cf. closed range in Hilbert complexes [BruningLesch1992],
[AFW2010]. -/
theorem Wcheck_eq_range_of_isClosed (hR : IsClosed (D.B.range : Set W1))
    {Λ : StrongDual ℝ (X V0 Vt0)} (hΛ : Λ ∈ D.Wcheck) : ∃ μ : W1, Λ = D.J μ := by
  set N := D.B.ker
  have : CompleteSpace N := (D.B.isClosed_ker).completeSpace_coe
  set f : Nᗮ →L[ℝ] W1 := D.B.comp Nᗮ.subtypeL
  have hinj : Function.Injective f := by
    intro a b hab
    have hmem : (a : X V0 Vt0) - b ∈ N := by
      simp only [N, LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr hab
    have hmem' : (a : X V0 Vt0) - b ∈ Nᗮ := Nᗮ.sub_mem a.2 b.2
    exact Subtype.ext (sub_eq_zero.mp (Submodule.inf_orthogonal_eq_bot N ▸
      (Submodule.mem_inf.mpr ⟨hmem, hmem'⟩) : (a : X V0 Vt0) - b ∈ (⊥ : Submodule ℝ _)))
  have hrange : f.range = D.B.range := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := N.exists_add_mem_mem_orthogonal x
      refine ⟨⟨z, hz⟩, ?_⟩
      have hy0 : (D.B : X V0 Vt0 →ₗ[ℝ] W1) y = 0 := hy
      rw [map_add, hy0, zero_add]
      rfl
  have hclo : IsClosed (f.range : Set W1) := by rwa [hrange]
  have : CompleteSpace (f.range) := hclo.completeSpace_coe
  set e := f.equivRange hinj hclo
  set m : StrongDual ℝ (f.range) := (Λ.comp Nᗮ.subtypeL).comp e.symm.toContinuousLinearMap
  set μ := (InnerProductSpace.toDual ℝ (f.range)).symm m
  refine ⟨(μ : W1), ?_⟩
  ext x
  obtain ⟨y, hy, z, hz, rfl⟩ := N.exists_add_mem_mem_orthogonal x
  rw [J_apply, map_add, map_add, D.Wcheck_vanish hΛ hy, show D.B y = 0 from hy, zero_add,
    zero_add]
  calc Λ z = m (e ⟨z, hz⟩) := by simp [m]
    _ = ⟪μ, e ⟨z, hz⟩⟫ := InnerProductSpace.toDual_symm_apply.symm
    _ = ⟪(μ : W1), D.B z⟫ := rfl


/-- The functional `ℓ(τ, ψ) = ⟪w, τ⟫ − ⟪v, dψ⟫` on `V⁰ × Ṽ⁰` (left side of (6.1a) with
`w = σ̇`, `v = u`). -/
def ell (w : W0) (v : Wt1) : StrongDual ℝ (X V0 Vt0) :=
  (innerSL ℝ w).comp (D.i0.comp ((ContinuousLinearMap.fst ℝ V0 Vt0).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ V0 Vt0).toContinuousLinearMap)) -
    (innerSL ℝ v).comp (D.dt0.comp ((ContinuousLinearMap.snd ℝ V0 Vt0).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ V0 Vt0).toContinuousLinearMap))

/-- `ℓ(τ, ψ) = ⟪w, τ⟫ − ⟪v, dψ⟫`. -/
@[simp] lemma ell_toLp (w : W0) (v : Wt1) (τ : V0) (ψ : Vt0) :
    D.ell w v (WithLp.toLp 2 (τ, ψ)) = ⟪w, D.i0 τ⟫ - ⟪v, D.dt0 ψ⟫ := rfl

/-- `ℓ` depends continuously on `(σ̇, u)` (dual norm). -/
lemma continuous_ell : Continuous fun p : W0 × Wt1 => D.ell p.1 p.2 := by
  have h1 : Continuous fun w : W0 => (innerSL ℝ w).comp (D.i0.comp
      ((ContinuousLinearMap.fst ℝ V0 Vt0).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ V0 Vt0).toContinuousLinearMap)) :=
    ((ContinuousLinearMap.compL ℝ (X V0 Vt0) W0 ℝ).flip _).continuous.comp (innerSL ℝ).continuous
  have h2 : Continuous fun v : Wt1 => (innerSL ℝ v).comp (D.dt0.comp
      ((ContinuousLinearMap.snd ℝ V0 Vt0).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ V0 Vt0).toContinuousLinearMap)) :=
    ((ContinuousLinearMap.compL ℝ (X V0 Vt0) Wt1 ℝ).flip _).continuous.comp (innerSL ℝ).continuous
  exact (h1.comp continuous_fst).sub (h2.comp continuous_snd)

omit [CompleteSpace V0] [CompleteSpace Vt0] in
/-- Functionals on `V⁰ × Ṽ⁰` are determined by their values on pairs. -/
lemma ext_X {ℓ₁ ℓ₂ : StrongDual ℝ (X V0 Vt0)}
    (h : ∀ τ ψ, ℓ₁ (WithLp.toLp 2 (τ, ψ)) = ℓ₂ (WithLp.toLp 2 (τ, ψ))) : ℓ₁ = ℓ₂ := by
  ext x
  exact h (WithLp.ofLp x).1 (WithLp.ofLp x).2

/-- Common part of (6.1) and (6.2): trajectories, time derivatives (right derivatives on
`[0,T)`, continuity on `[0,T]`) and equations (b)–(d). Test spaces `N ∈ W²`, `µ ∈ W̃²`
(the thesis' `V²`, `Ṽ²` are undefined). The source enters through `(f, v)`, `f(t) ∈ W̃¹`. -/
structure Trajectory (T : ℝ) (f : ℝ → Wt1) where
  σ : ℝ → V0
  φ : ℝ → Vt0
  u : ℝ → Vt1
  M : ℝ → W2
  ρ : ℝ → Wt2
  σ' : ℝ → W0
  u' : ℝ → Wt1
  M' : ℝ → W2
  ρ' : ℝ → Wt2
  cσ : ContinuousOn (fun s => D.i0 (σ s)) (Icc 0 T)
  cu : ContinuousOn (fun s => D.it1 (u s)) (Icc 0 T)
  cM : ContinuousOn M (Icc 0 T)
  cρ : ContinuousOn ρ (Icc 0 T)
  dσ : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun s => D.i0 (σ s)) (σ' t) (Ici t) t
  du : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun s => D.it1 (u s)) (u' t) (Ici t) t
  dM : ∀ t ∈ Ico 0 T, HasDerivWithinAt M (M' t) (Ici t) t
  dρ : ∀ t ∈ Ico 0 T, HasDerivWithinAt ρ (ρ' t) (Ici t) t
  eb : ∀ t ∈ Ico 0 T, ∀ v, ⟪u' t, D.it1 v⟫ + ⟪D.dt0 (φ t), D.it1 v⟫ + ⟪M t, D.S1 v⟫
      + ⟪ρ t, D.dt1 v⟫ = ⟪f t, D.it1 v⟫
  ec : ∀ t ∈ Ico 0 T, ∀ N, ⟪M' t, N⟫ - ⟪D.S1 (u t), N⟫ = 0
  ed : ∀ t ∈ Ico 0 T, ∀ μ, ⟪ρ' t, μ⟫ - ⟪D.dt1 (u t), μ⟫ = 0

/-- A solution of the Hodge wave problem (6.1) for the closed complex (5.1):
`(σ, φ) ∈ Γ` and (6.1a) tested on `Γ`. See [QuennevilleBelair2015], §6.1, (6.1); the abstract
Hodge wave problem is [QuennevilleBelair2015], §4.4. -/
structure Solution (T : ℝ) (f : ℝ → Wt1) extends D.Trajectory T f where
  mem : ∀ t ∈ Icc 0 T, D.d0 (σ t) = D.S0 (φ t)
  ea : ∀ t ∈ Ico 0 T, ∀ τ ψ, D.d0 τ = D.S0 ψ → ⟪σ' t, D.i0 τ⟫ - ⟪D.it1 (u t), D.dt0 ψ⟫ = 0

/-- A solution of the multiplier problem (6.2), with multiplier `Λ(t) ∈ W̌¹`
(Correction: `λ ∈ C⁰(W¹)` is not available in general, and no `λ(0)` is prescribed).
See [QuennevilleBelair2015], §6.1, (6.2). -/
structure MultiplierSolution (T : ℝ) (f : ℝ → Wt1) extends D.Trajectory T f where
  Λ : ℝ → D.Wcheck
  ea : ∀ t ∈ Ico 0 T, ∀ τ ψ,
    ⟪σ' t, D.i0 τ⟫ - ⟪D.it1 (u t), D.dt0 ψ⟫ - (Λ t : StrongDual ℝ (X V0 Vt0))
      (WithLp.toLp 2 (τ, ψ)) = 0
  ee : ∀ t ∈ Icc 0 T, ∀ ζ, ⟪D.d0 (σ t) - D.S0 (φ t), ζ⟫ = 0

variable {D}

/-- (6.2e) forces the constraint `dσ = Sφ` at every time. -/
theorem MultiplierSolution.constraint {T : ℝ} {f : ℝ → Wt1} (s : D.MultiplierSolution T f) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    D.d0 (s.σ t) = D.S0 (s.φ t) :=
  sub_eq_zero.mp (inner_self_eq_zero.mp (s.ee t ht _))

/-- **Thesis Prop 6.1, first bullet.** A solution of (6.2) satisfies `dσ = Sφ` and solves (6.1)
with the same data.

Correction: the thesis prescribes `λ(0) = λ₀` and silently uses `M₀ = 0`; neither is needed
(the multiplier has no time derivative and `M₀ ∈ W²` is arbitrary).
See [QuennevilleBelair2015], Prop 6.1. [QuennevilleBelair2015], Prop 6.1 -/
def MultiplierSolution.toSolution {T : ℝ} {f : ℝ → Wt1}
    (s : D.MultiplierSolution T f) : D.Solution T f where
  toTrajectory := s.toTrajectory
  mem := fun t ht => s.constraint ht
  ea := fun t ht τ ψ h => by
    have := s.ea t ht τ ψ
    rwa [D.Wcheck_vanish (s.Λ t).2 (by simp [h]), sub_zero] at this

/-- `toSolution` keeps the trajectories. -/
@[simp] lemma MultiplierSolution.toSolution_toTrajectory {T : ℝ} {f : ℝ → Wt1}
    (s : D.MultiplierSolution T f) :
    s.toSolution.toTrajectory = s.toTrajectory := rfl

/-- The multiplier of (6.2) on `[0,T)` is the functional `ℓ_t = ⟪σ̇, ·⟫ − ⟪u, d·⟫`. -/
theorem MultiplierSolution.Λ_eq {T : ℝ} {f : ℝ → Wt1} (s : D.MultiplierSolution T f) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    (s.Λ t : StrongDual ℝ (X V0 Vt0)) = D.ell (s.σ' t) (D.it1 (s.u t)) :=
  ext_X fun τ ψ => by have := s.ea t ht τ ψ; simp only [ell_toLp]; linarith

/-- **Thesis Prop 6.1, second bullet, corrected as (i) (Correction).** Every solution of (6.1)
extends to a solution of (6.2) with the same trajectories and a multiplier `Λ(t) ∈ W̌¹`; the
multiplier is unique on `[0,T)`.

Thesis gap: the thesis sets `λ := (S*)⁻¹ d* u ∈ W¹`, which needs `d* u ∈ range S*` (false in
general; in EB it needs `u ∈ H(div)`), assumes `M ≡ 0`, and prescribes an arbitrary `λ₀`.
Here `Λ(t)` is produced from the annihilator characterisation `mem_Wcheck_of_vanish`
(Riesz + `(ker B)ᗮ = closure (range B*)`), with no extra hypothesis, `M` arbitrary and no `λ₀`.
See [QuennevilleBelair2015], Prop 6.1. [QuennevilleBelair2015], Prop 6.1 (corrected) -/
theorem Solution.exists_multiplierSolution {T : ℝ} {f : ℝ → Wt1} (s : D.Solution T f) :
    ∃ s' : D.MultiplierSolution T f, s'.toTrajectory = s.toTrajectory ∧
      ∀ s'' : D.MultiplierSolution T f, s''.toTrajectory = s.toTrajectory → ∀ t ∈ Ico 0 T, s''.Λ t = s'.Λ t := by
  classical
  have hmem : ∀ t ∈ Ico 0 T, D.ell (s.σ' t) (D.it1 (s.u t)) ∈ D.Wcheck := fun t ht =>
    D.mem_Wcheck_of_vanish _ fun x hx => by
      have hx' : D.d0 (WithLp.ofLp x).1 = D.S0 (WithLp.ofLp x).2 := by
        have : D.B (WithLp.toLp 2 (WithLp.ofLp x)) = 0 := by simpa using hx
        rw [B_toLp] at this; exact sub_eq_zero.mp this
      have := s.ea t ht _ _ hx'
      rw [show x = WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2) from rfl, ell_toLp]
      exact this
  let Λ : ℝ → D.Wcheck := fun t => if ht : t ∈ Ico 0 T then ⟨_, hmem t ht⟩ else 0
  have hΛ : ∀ t ∈ Ico 0 T, (Λ t : StrongDual ℝ (X V0 Vt0)) = D.ell (s.σ' t) (D.it1 (s.u t)) :=
    fun t ht => by simp only [Λ, dite_eq_left ht]
  let s' : D.MultiplierSolution T f :=
    { toTrajectory := s.toTrajectory
      Λ := Λ
      ea := fun t ht τ ψ => by rw [hΛ t ht, ell_toLp]; ring
      ee := fun t ht ζ => by simp [s.mem t ht] }
  refine ⟨s', rfl, fun s'' h t ht => Subtype.ext ?_⟩
  rw [s''.Λ_eq ht, h]
  exact (hΛ t ht).symm

/-- The multiplier is continuous in time with values in `W̌¹` (thesis: `λ ∈ C⁰([0,T]; W̌¹)`),
as soon as `σ̇` is continuous (the thesis' `σ ∈ C¹([0,T]; W⁰)`). -/
theorem MultiplierSolution.continuousOn_Λ {T : ℝ} {f : ℝ → Wt1} (s : D.MultiplierSolution T f)
    (hσ' : ContinuousOn s.σ' (Ico 0 T)) :
    ContinuousOn (fun t => (s.Λ t : StrongDual ℝ (X V0 Vt0))) (Ico 0 T) := by
  have hp : ContinuousOn (fun t => (s.σ' t, D.it1 (s.u t))) (Ico 0 T) :=
    hσ'.prodMk (s.cu.mono Ico_subset_Icc_self)
  exact (D.continuous_ell.comp_continuousOn hp).congr fun t ht => s.Λ_eq ht

/-- **Prop 6.1(i) under closed range.** If `B = (d, −S)` has closed range, the multiplier is a
genuine `λ(t) ∈ W¹`. (Remark, not formalized: in EB the range `grad H̊¹ + H̊¹(V)` is expected
to be dense but not closed in `L²`, which is why the thesis needs `W̌¹ = H⁻¹(div, V)` there.) -/
theorem Solution.exists_multiplierSolution_of_isClosed_range (hR : IsClosed (D.B.range : Set W1))
    {T : ℝ} {f : ℝ → Wt1}
    (s : D.Solution T f) :
    ∃ s' : D.MultiplierSolution T f, s'.toTrajectory = s.toTrajectory ∧ ∃ lam : ℝ → W1,
      ∀ t, (s'.Λ t : StrongDual ℝ (X V0 Vt0)) = D.J (lam t) := by
  obtain ⟨s', hs', -⟩ := Solution.exists_multiplierSolution s
  have := fun t => D.Wcheck_eq_range_of_isClosed hR (s'.Λ t).2
  choose lam hlam using this
  exact ⟨s', hs', lam, hlam⟩

/-- **Thesis Prop 6.1, second bullet, corrected as (ii).** `W¹`-valued multiplier.
Assume (R): `(λ(t), Sψ) = (u(t), dψ)` for all `ψ`, i.e. `S* λ = d* u`, and
(D): `Γ₀ = {τ | dτ ∈ S Ṽ⁰}` is dense in `V⁰`. Then `λ` is the multiplier of (6.2).

Thesis gap: the proof computes `d S⁻¹ dτ`, undefined for general `τ ∈ V⁰` (in EB it needs
`τ ∈ H²`); density (D) replaces it. In EB, (D) holds since `H̊²` is dense in `H̊¹`, and (R)
means `u(t) ∈ H(div, M)` with `λ = −div u`. See [QuennevilleBelair2015], Prop 6.1 (whose proof
uses [QuennevilleBelair2015], Thm 4.7). -/
theorem Solution.exists_multiplierSolution_of_dense {T : ℝ} {f : ℝ → Wt1} (s : D.Solution T f)
    (lam : ℝ → W1)
    (hR : ∀ t ∈ Ico 0 T, ∀ ψ, ⟪lam t, D.S0 ψ⟫ = ⟪D.it1 (s.u t), D.dt0 ψ⟫)
    (hD : Dense {τ : V0 | ∃ ψ, D.d0 τ = D.S0 ψ}) :
    ∃ s' : D.MultiplierSolution T f, s'.toTrajectory = s.toTrajectory ∧
      ∀ t, (s'.Λ t : StrongDual ℝ (X V0 Vt0)) = D.J (lam t) := by
  have key : ∀ t ∈ Ico 0 T, ∀ τ, ⟪s.σ' t, D.i0 τ⟫ = ⟪lam t, D.d0 τ⟫ := by
    intro t ht
    have := Continuous.ext_on hD (f := fun τ => ⟪s.σ' t, D.i0 τ⟫)
      (g := fun τ => ⟪lam t, D.d0 τ⟫) (by fun_prop) (by fun_prop) (by
        rintro τ ⟨ψ, hψ⟩
        have := s.ea t ht τ ψ hψ
        simp only
        rw [hψ, hR t ht]; linarith)
    exact fun τ => congrFun this τ
  refine ⟨{ toTrajectory := s.toTrajectory
            Λ := fun t => ⟨D.J (lam t), D.J_mem_Wcheck _⟩
            ea := fun t ht τ ψ => by
              simp only [J_apply, B_toLp, inner_sub_right]
              rw [key t ht, hR t ht]; ring
            ee := fun t ht ζ => by simp [s.mem t ht] }, rfl, fun t => rfl⟩

/-! ### Energy and uniqueness for (6.1)/(6.2) -/

/-- The energy `‖σ‖² + ‖u‖² + ‖M‖² + ‖ρ‖²` (all in `W`-norms). -/
def Trajectory.energy {T : ℝ} {f : ℝ → Wt1} (s : D.Trajectory T f) (t : ℝ) : ℝ :=
  ‖D.i0 (s.σ t)‖ ^ 2 + ‖D.it1 (s.u t)‖ ^ 2 + ‖s.M t‖ ^ 2 + ‖s.ρ t‖ ^ 2

/-- **Energy identity (§6.1, "uniqueness by an energy argument", written out).**
`d/dt (‖σ‖² + ‖u‖² + ‖M‖² + ‖ρ‖²) = 2 (f, u)`.
Key step (missing in the thesis): test (6.1a) with `(σ, φ) ∈ Γ`; for (6.2) the multiplier term
vanishes by (6.2e), for `λ` in `W̌¹` as well. See [QuennevilleBelair2015], §6.1; cf. the energy
argument for the abstract Hodge wave equation [QuennevilleBelair2015], §4.4, Thm 4.6. -/
theorem Solution.hasDerivWithinAt_energy {T : ℝ} {f : ℝ → Wt1} (s : D.Solution T f) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt s.energy (2 * ⟪f t, D.it1 (s.u t)⟫) (Ici t) t := by
  have h := ((((s.dσ t ht).norm_sq).add (s.du t ht).norm_sq).add
    (s.dM t ht).norm_sq).add (s.dρ t ht).norm_sq
  have h' : HasDerivWithinAt s.energy _ (Ici t) t := h
  convert h' using 1
  have ha := s.ea t ht (s.σ t) (s.φ t) (s.mem t (Ico_subset_Icc_self ht))
  have hb := s.eb t ht (s.u t)
  have hcM := s.ec t ht (s.M t)
  have hd := s.ed t ht (s.ρ t)
  linarith [real_inner_comm (D.dt0 (s.φ t)) (D.it1 (s.u t)),
    real_inner_comm (D.S1 (s.u t)) (s.M t), real_inner_comm (D.dt1 (s.u t)) (s.ρ t),
    real_inner_comm (D.i0 (s.σ t)) (s.σ' t), real_inner_comm (D.it1 (s.u t)) (s.u' t),
    real_inner_comm (s.M t) (s.M' t), real_inner_comm (s.ρ t) (s.ρ' t)]

/-- The energy is continuous on `[0,T]`. -/
lemma Trajectory.continuousOn_energy {T : ℝ} {f : ℝ → Wt1} (s : D.Trajectory T f) :
    ContinuousOn s.energy (Icc 0 T) :=
  (((s.cσ.norm.pow 2).add (s.cu.norm.pow 2)).add (s.cM.norm.pow 2)).add (s.cρ.norm.pow 2)

/-- Energy conservation for (6.1) with `f = 0` (Thesis §6.1, energy argument). -/
theorem Solution.energy_const {T : ℝ} (s : D.Solution T 0) :
    ∀ t ∈ Icc 0 T, s.energy t = s.energy 0 :=
  constant_of_has_deriv_right_zero s.continuousOn_energy fun t ht => by
    simpa using s.hasDerivWithinAt_energy ht

/-- Energy conservation for (6.2) with `f = 0` (the thesis' "energy argument"). -/
theorem MultiplierSolution.energy_const {T : ℝ} (s : D.MultiplierSolution T 0) :
    ∀ t ∈ Icc 0 T, s.energy t = s.energy 0 :=
  s.toSolution.energy_const

/-- Difference of two solutions of (6.1) with the same source: a solution with `f = 0`
(linearity, Thesis §6.1). -/
def Solution.sub {T : ℝ} {f : ℝ → Wt1} (s₁ s₂ : D.Solution T f) : D.Solution T 0 where
  σ := s₁.σ - s₂.σ
  φ := s₁.φ - s₂.φ
  u := s₁.u - s₂.u
  M := s₁.M - s₂.M
  ρ := s₁.ρ - s₂.ρ
  σ' := s₁.σ' - s₂.σ'
  u' := s₁.u' - s₂.u'
  M' := s₁.M' - s₂.M'
  ρ' := s₁.ρ' - s₂.ρ'
  cσ := (s₁.cσ.sub s₂.cσ).congr fun x _ => by simp
  cu := (s₁.cu.sub s₂.cu).congr fun x _ => by simp
  cM := s₁.cM.sub s₂.cM
  cρ := s₁.cρ.sub s₂.cρ
  dσ := fun t ht => by
    convert (s₁.dσ t ht).sub (s₂.dσ t ht) using 1; funext x; simp
  du := fun t ht => by
    convert (s₁.du t ht).sub (s₂.du t ht) using 1; funext x; simp
  dM := fun t ht => (s₁.dM t ht).sub (s₂.dM t ht)
  dρ := fun t ht => (s₁.dρ t ht).sub (s₂.dρ t ht)
  eb := fun t ht v => by
    have h₁ := s₁.eb t ht v; have h₂ := s₂.eb t ht v
    simp only [Pi.sub_apply, map_sub, inner_sub_left, Pi.zero_apply, inner_zero_left]
    linarith
  ec := fun t ht N => by
    have h₁ := s₁.ec t ht N; have h₂ := s₂.ec t ht N
    simp only [Pi.sub_apply, map_sub, inner_sub_left]; linarith
  ed := fun t ht μ => by
    have h₁ := s₁.ed t ht μ; have h₂ := s₂.ed t ht μ
    simp only [Pi.sub_apply, map_sub, inner_sub_left]; linarith
  mem := fun t ht => by simp [s₁.mem t ht, s₂.mem t ht]
  ea := fun t ht τ ψ h => by
    have h₁ := s₁.ea t ht τ ψ h; have h₂ := s₂.ea t ht τ ψ h
    simp only [Pi.sub_apply, map_sub, inner_sub_left]; linarith

/-- **Uniqueness for (6.1)** (energy argument): two solutions with the same source and the same
data `(σ, u, M, ρ)(0)` coincide on `[0,T]`; `φ` too when `S₀` is injective (thesis
hypothesis of §5.1). See [QuennevilleBelair2015], §6.1 ("uniqueness is shown using an energy
argument"). -/
theorem Solution.unique {T : ℝ} {f : ℝ → Wt1} (s₁ s₂ : D.Solution T f)
    (h0 : s₁.σ 0 = s₂.σ 0 ∧ s₁.u 0 = s₂.u 0 ∧ s₁.M 0 = s₂.M 0 ∧ s₁.ρ 0 = s₂.ρ 0) :
    ∀ t ∈ Icc 0 T, s₁.σ t = s₂.σ t ∧ s₁.u t = s₂.u t ∧ s₁.M t = s₂.M t ∧ s₁.ρ t = s₂.ρ t ∧
      (Function.Injective D.S0 → s₁.φ t = s₂.φ t) := by
  intro t ht
  have hE := (s₁.sub s₂).energy_const t ht
  have hE0 : (s₁.sub s₂).energy 0 = 0 := by
    simp [Trajectory.energy, Solution.sub, h0.1, h0.2.1, h0.2.2.1, h0.2.2.2]
  rw [hE0] at hE
  simp only [Trajectory.energy, Solution.sub, Pi.sub_apply, map_sub] at hE
  have a := sq_nonneg ‖D.i0 (s₁.σ t) - D.i0 (s₂.σ t)‖
  have b := sq_nonneg ‖D.it1 (s₁.u t) - D.it1 (s₂.u t)‖
  have c := sq_nonneg ‖s₁.M t - s₂.M t‖
  have e := sq_nonneg ‖s₁.ρ t - s₂.ρ t‖
  have hσ : D.i0 (s₁.σ t) = D.i0 (s₂.σ t) := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith))
  have hu : D.it1 (s₁.u t) = D.it1 (s₂.u t) := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith))
  have hσ' := D.i0_injective hσ
  refine ⟨hσ', D.it1_injective hu, sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith)),
    sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith)), fun hS => hS ?_⟩
  rw [← s₁.mem t ht, ← s₂.mem t ht, hσ']

/-- **Uniqueness for (6.2)**, including the multiplier: with the same source and data, the
trajectories agree on `[0,T]` (`φ` if `S₀` is injective) and the multipliers `Λ(t) ∈ W̌¹`
agree on `[0,T)`. Thesis gap: uniqueness of `φ` and `λ` is not addressed in the thesis.
See [QuennevilleBelair2015], §6.1. -/
theorem MultiplierSolution.unique {T : ℝ} {f : ℝ → Wt1} (s₁ s₂ : D.MultiplierSolution T f)
    (h0 : s₁.σ 0 = s₂.σ 0 ∧ s₁.u 0 = s₂.u 0 ∧ s₁.M 0 = s₂.M 0 ∧ s₁.ρ 0 = s₂.ρ 0) :
    (∀ t ∈ Icc 0 T, s₁.σ t = s₂.σ t ∧ s₁.u t = s₂.u t ∧ s₁.M t = s₂.M t ∧ s₁.ρ t = s₂.ρ t ∧
      (Function.Injective D.S0 → s₁.φ t = s₂.φ t)) ∧ ∀ t ∈ Ico 0 T, s₁.Λ t = s₂.Λ t := by
  have h := Solution.unique s₁.toSolution s₂.toSolution h0
  refine ⟨h, fun t ht => Subtype.ext ?_⟩
  have hσ' : s₁.σ' t = s₂.σ' t := hasDerivWithinAt_Ici_unique ht
    (fun x hx => congrArg D.i0 (h x hx).1) (s₁.dσ t ht) (s₂.dσ t ht)
  have hu : s₁.u t = s₂.u t := (h t (Ico_subset_Icc_self ht)).2.1
  rw [s₁.Λ_eq ht, s₂.Λ_eq ht, hσ', hu]

end WaveData

/-- Existence for a linear ODE `x' = A x + F(t)` with bounded `A` and continuous `F`
(variation of constants with `NormedSpace.exp`). Proved, not assumed. Classical: [Pazy1983], §1.1
(uniformly continuous semigroups) and [Pazy1983], Ch. 4 (inhomogeneous Cauchy problem). -/
theorem exists_hasDerivAt_linearODE {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X]
    (A : X →L[ℝ] X) {F : ℝ → X} (hF : Continuous F) (x₀ : X) :
    ∃ x : ℝ → X, x 0 = x₀ ∧ ∀ t, HasDerivAt x (A (x t) + F t) t := by
  set E : ℝ → X →L[ℝ] X := fun t => NormedSpace.exp (t • A) with hE
  have hEd : ∀ t, HasDerivAt E (A * E t) t := fun t => hasDerivAt_exp_smul_const' A t
  have hEc : Continuous E := continuous_iff_continuousAt.2 fun t => (hEd t).continuousAt
  have hinv : ∀ t v, E t (E (-t) v) = v := by
    intro t v
    have : E t * E (-t) = 1 := by
      simp only [hE]
      rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
        ((Commute.refl A).smul_left t |>.smul_right (-t))
        ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
        ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)]
      simp
    simpa using congrArg (fun T : X →L[ℝ] X => T v) this
  set g : ℝ → X := fun s => E (-s) (F s)
  have hg : Continuous g := (hEc.comp continuous_neg).clm_apply hF
  set y : ℝ → X := fun t => x₀ + ∫ s in (0:ℝ)..t, g s
  have hy : ∀ t, HasDerivAt y (g t) t := fun t =>
    ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add x₀
  refine ⟨fun t => E t (y t), by simp [hE, y], fun t => ?_⟩
  have := (hEd t).clm_apply (hy t)
  convert this using 1
  simp [g, hinv]

/-! ## §2. The discrete problem (6.3) -/

section Discrete

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  (D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2)

/-- A solution of the discrete system (6.3) on `[0,T]`. All spaces are the FE spaces with
their `L²` inner products; `D.S0, D.S1` are `S₀,ₕ = Π¹ₕS₀`, `S₁,ₕ = Π²ₕS₁`; `D.anticomm` is the
discrete anticommutation `d S₀,ₕ = −S₁,ₕ d` (essential, unstated in the thesis; it follows from
commuting projections). The source is given by its representer `f(t) ∈ Ṽₕ¹`.
Derivatives are right derivatives on `[0,T)`; the trajectories are continuous on `[0,T]`.
See [QuennevilleBelair2015], §6.2, (6.3); commuting projections as in [Arnold2018], [AFW2010]. -/
structure DiscreteSolution (T : ℝ) (f : ℝ → Pt1) where
  σ : ℝ → P0
  φ : ℝ → Pt0
  u : ℝ → Pt1
  M : ℝ → P2
  ρ : ℝ → Pt2
  lam : ℝ → P1
  σ' : ℝ → P0
  u' : ℝ → Pt1
  M' : ℝ → P2
  ρ' : ℝ → Pt2
  cσ : ContinuousOn σ (Icc 0 T)
  cu : ContinuousOn u (Icc 0 T)
  cM : ContinuousOn M (Icc 0 T)
  cρ : ContinuousOn ρ (Icc 0 T)
  dσ : ∀ t ∈ Ico 0 T, HasDerivWithinAt σ (σ' t) (Ici t) t
  du : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u' t) (Ici t) t
  dM : ∀ t ∈ Ico 0 T, HasDerivWithinAt M (M' t) (Ici t) t
  dρ : ∀ t ∈ Ico 0 T, HasDerivWithinAt ρ (ρ' t) (Ici t) t
  ea : ∀ t ∈ Icc 0 T, ∀ τ ψ,
    ⟪σ' t, τ⟫ - ⟪u t, D.dt0 ψ⟫ - ⟪lam t, D.d0 τ - D.S0 ψ⟫ = 0
  eb : ∀ t ∈ Ico 0 T, ∀ v,
    ⟪u' t, v⟫ + ⟪D.dt0 (φ t), v⟫ + ⟪M t, D.S1 v⟫ + ⟪ρ t, D.dt1 v⟫ = ⟪f t, v⟫
  ec : ∀ t ∈ Ico 0 T, ∀ N, ⟪M' t, N⟫ - ⟪D.S1 (u t), N⟫ = 0
  ed : ∀ t ∈ Ico 0 T, ∀ μ, ⟪ρ' t, μ⟫ - ⟪D.dt1 (u t), μ⟫ = 0
  ee : ∀ t ∈ Icc 0 T, ∀ ζ, ⟪D.d0 (σ t) - D.S0 (φ t), ζ⟫ = 0

variable {D}

/-- Correction of the remark before Prop 6.2 ("`dσₕ − Sₕφₕ = 0` exactly if the initial
conditions satisfy this condition"): (6.3e) imposes the constraint algebraically at every time;
it is not propagated from the data. -/
theorem DiscreteSolution.constraint {T : ℝ} {f : ℝ → Pt1} (s : DiscreteSolution D T f) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    D.d0 (s.σ t) = D.S0 (s.φ t) :=
  sub_eq_zero.mp (inner_self_eq_zero.mp (s.ee t ht _))

/-- Hidden constraint: every solution has `uₕ(t) ⊥ d(ker S₀,ₕ)` (take `τ = 0` in (6.3a)). -/
theorem DiscreteSolution.hidden_constraint {T : ℝ} {f : ℝ → Pt1} (s : DiscreteSolution D T f)
    {t : ℝ}
    (ht : t ∈ Icc 0 T) {ψ : Pt0} (hψ : D.S0 ψ = 0) : ⟪s.u t, D.dt0 ψ⟫ = 0 := by
  have := s.ea t ht 0 ψ
  simp [hψ] at this
  linarith

/-- **Thesis Prop 6.2 is false as stated.** Initial data `u₀ = dψ` with `ψ ∈ ker S₀,ₕ`,
`dψ ≠ 0` admit no solution (whatever `σ₀, φ₀, M₀, ρ₀, f`). In EB, `dim ker S₀,ₕ = 3V_int + 2E_int`.
Thesis gap: (6.3) is a differential-algebraic system, so "square ⇒ uniqueness implies existence"
does not apply. Refutes [QuennevilleBelair2015], Prop 6.2. -/
theorem not_exists_discreteSolution_of_ker {T : ℝ} (hT : 0 ≤ T) {f : ℝ → Pt1} {ψ : Pt0}
    (hψ : D.S0 ψ = 0) (hdψ : D.dt0 ψ ≠ 0) :
    ¬ ∃ s : DiscreteSolution D T f, s.u 0 = D.dt0 ψ := by
  rintro ⟨s, hs⟩
  have h := s.hidden_constraint ⟨le_rfl, hT⟩ hψ
  rw [hs] at h
  exact hdψ (inner_self_eq_zero.mp h)

/-- Prop 6.2 also fails for compatible `u₀`: `φ₀` is not free. With `f = 0`, data
`(σ₀, φ₀) = (0, ψ)`, `ψ ∈ ker S₀,ₕ`, `dψ ≠ 0` (so `(σ₀, φ₀) ∈ Γₕ`), admit no solution. Refutes
[QuennevilleBelair2015], Prop 6.2. -/
theorem not_exists_discreteSolution_phi_of_ker {T : ℝ} (hT : 0 < T) {ψ : Pt0}
    (hψ : D.S0 ψ = 0) (hdψ : D.dt0 ψ ≠ 0) :
    ¬ ∃ s : DiscreteSolution D T 0, s.φ 0 = ψ := by
  rintro ⟨s, hs⟩
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hz : ∀ x ∈ Icc 0 T, ⟪s.u x, D.dt0 ψ⟫ = 0 := fun x hx => s.hidden_constraint hx hψ
  have hd : HasDerivWithinAt (fun x => ⟪s.u x, D.dt0 ψ⟫) ⟪s.u' 0, D.dt0 ψ⟫ (Ici 0) 0 := by
    simpa using HasDerivWithinAt.inner ℝ (s.du 0 h0) (hasDerivWithinAt_const (0 : ℝ) (Ici 0) (D.dt0 ψ))
  have hu' := hasDerivWithinAt_Ici_eq_zero h0 hz hd
  have hb := s.eb 0 h0 (D.dt0 ψ)
  have hS1 : D.S1 (D.dt0 ψ) = 0 := by
    have := D.anticomm ψ; rw [hψ, map_zero] at this; exact neg_eq_zero.mp this.symm
  rw [hu', hS1, D.dt1_dt0, hs] at hb
  simp only [inner_zero_right, Pi.zero_apply, inner_zero_left, add_zero, zero_add] at hb
  exact hdψ (inner_self_eq_zero.mp hb)

/-- **Corrected Prop 6.2, necessity.** Every solution satisfies (C1) `dσ₀ = S₀,ₕφ₀`,
(C2) `(u₀, dψ) = 0` and (C3) `(dφ₀, dψ) = (f(0), dψ)` for all `ψ ∈ ker S₀,ₕ`.
(C3) comes from differentiating (C2) and testing (6.3b) with `v = dψ`, using
`S₁,ₕ dψ = −d S₀,ₕ ψ = 0`. Corrects [QuennevilleBelair2015], Prop 6.2. -/
theorem DiscreteSolution.compatible {T : ℝ} (hT : 0 < T) {f : ℝ → Pt1}
    (s : DiscreteSolution D T f) :
    D.d0 (s.σ 0) = D.S0 (s.φ 0) ∧
    (∀ ψ, D.S0 ψ = 0 → ⟪s.u 0, D.dt0 ψ⟫ = 0) ∧
    (∀ ψ, D.S0 ψ = 0 → ⟪D.dt0 (s.φ 0), D.dt0 ψ⟫ = ⟪f 0, D.dt0 ψ⟫) := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  refine ⟨s.constraint h0, fun ψ hψ => s.hidden_constraint h0 hψ, fun ψ hψ => ?_⟩
  have h0' : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hz : ∀ x ∈ Icc 0 T, ⟪s.u x, D.dt0 ψ⟫ = 0 := fun x hx => s.hidden_constraint hx hψ
  have hd : HasDerivWithinAt (fun x => ⟪s.u x, D.dt0 ψ⟫) ⟪s.u' 0, D.dt0 ψ⟫ (Ici 0) 0 := by
    simpa using HasDerivWithinAt.inner ℝ (s.du 0 h0') (hasDerivWithinAt_const (0 : ℝ) (Ici 0) (D.dt0 ψ))
  have hu' := hasDerivWithinAt_Ici_eq_zero h0' hz hd
  have hb := s.eb 0 h0' (D.dt0 ψ)
  have hS1 : D.S1 (D.dt0 ψ) = 0 := by
    have := D.anticomm ψ; rw [hψ, map_zero] at this; exact neg_eq_zero.mp this.symm
  rw [hu', hS1, D.dt1_dt0] at hb
  simpa using hb

/-- Energy identity for the discrete system (6.3) (Thesis §6.2):
`d/dt (‖σₕ‖² + ‖uₕ‖² + ‖Mₕ‖² + ‖ρₕ‖²) = 2 (f, uₕ)`. -/
theorem DiscreteSolution.hasDerivWithinAt_energy {T : ℝ} {f : ℝ → Pt1} (s : DiscreteSolution D T f)
    {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun x => ‖s.σ x‖ ^ 2 + ‖s.u x‖ ^ 2 + ‖s.M x‖ ^ 2 + ‖s.ρ x‖ ^ 2)
      (2 * ⟪f t, s.u t⟫) (Ici t) t := by
  have h := ((((s.dσ t ht).norm_sq).add (s.du t ht).norm_sq).add
    (s.dM t ht).norm_sq).add (s.dρ t ht).norm_sq
  convert h using 1
  have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
  have ha := s.ea t ht' (s.σ t) (s.φ t)
  rw [s.constraint ht', sub_self, inner_zero_right, sub_zero] at ha
  have hb := s.eb t ht (s.u t)
  have hcM := s.ec t ht (s.M t)
  have hd := s.ed t ht (s.ρ t)
  linarith [real_inner_comm (s.σ t) (s.σ' t), real_inner_comm (D.dt0 (s.φ t)) (s.u t),
    real_inner_comm (s.u t) (s.u' t), real_inner_comm (D.S1 (s.u t)) (s.M t),
    real_inner_comm (D.dt1 (s.u t)) (s.ρ t), real_inner_comm (s.M t) (s.M' t),
    real_inner_comm (s.ρ t) (s.ρ' t), real_inner_comm (f t) (s.u t)]

/-- Energy conservation for the discrete system (6.3) with `f = 0` (Thesis §6.2, proof of
Prop 6.2). -/
theorem DiscreteSolution.energy_const {T : ℝ} (s : DiscreteSolution D T 0) :
    ∀ t ∈ Icc 0 T, ‖s.σ t‖ ^ 2 + ‖s.u t‖ ^ 2 + ‖s.M t‖ ^ 2 + ‖s.ρ t‖ ^ 2
        = ‖s.σ 0‖ ^ 2 + ‖s.u 0‖ ^ 2 + ‖s.M 0‖ ^ 2 + ‖s.ρ 0‖ ^ 2 :=
  constant_of_has_deriv_right_zero
    ((((s.cσ.norm.pow 2).add (s.cu.norm.pow 2)).add (s.cM.norm.pow 2)).add (s.cρ.norm.pow 2))
    fun t ht => by simpa using s.hasDerivWithinAt_energy ht

/-- **Corrected Prop 6.2, uniqueness core:** zero data and `f = 0` give the zero solution,
including `φₕ` (needs `d` injective on `Ṽₕ⁰`) and `λₕ` (needs `S₀,ₕ` surjective).
Thesis gap: the thesis never shows `φₕ = 0` (`S₀,ₕ` is not injective).
See [QuennevilleBelair2015], Prop 6.2, proof. -/
theorem DiscreteSolution.eq_zero_of_initial_eq_zero {T : ℝ} (s : DiscreteSolution D T 0)
    (hdinj : Function.Injective D.dt0)
    (hS : Function.Surjective D.S0)
    (h0 : s.σ 0 = 0 ∧ s.u 0 = 0 ∧ s.M 0 = 0 ∧ s.ρ 0 = 0) :
    (∀ t ∈ Icc 0 T, s.σ t = 0 ∧ s.u t = 0 ∧ s.M t = 0 ∧ s.ρ t = 0 ∧ s.lam t = 0) ∧
    (∀ t ∈ Ico 0 T, s.φ t = 0) := by
  obtain ⟨hσ0, hu0, hM0, hρ0⟩ := h0
  have hz : ∀ t ∈ Icc 0 T, s.σ t = 0 ∧ s.u t = 0 ∧ s.M t = 0 ∧ s.ρ t = 0 := by
    intro t ht
    have := s.energy_const t ht
    simp only [hσ0, hu0, hM0, hρ0, norm_zero] at this
    have a := sq_nonneg ‖s.σ t‖; have b := sq_nonneg ‖s.u t‖
    have c := sq_nonneg ‖s.M t‖; have e := sq_nonneg ‖s.ρ t‖
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply norm_eq_zero.mp <;> nlinarith [norm_nonneg (s.σ t),
      norm_nonneg (s.u t), norm_nonneg (s.M t), norm_nonneg (s.ρ t)]
  refine ⟨fun t ht => ⟨(hz t ht).1, (hz t ht).2.1, (hz t ht).2.2.1, (hz t ht).2.2.2, ?_⟩, ?_⟩
  · obtain ⟨ψ, hψ⟩ := hS (s.lam t)
    have := s.ea t ht 0 ψ
    rw [(hz t ht).2.1, hψ] at this
    simp only [inner_zero_left, inner_zero_right, map_zero, zero_sub, inner_neg_right, sub_zero,
      sub_neg_eq_add, zero_add] at this
    exact inner_self_eq_zero.mp this
  · intro t ht
    have ht' := Ico_subset_Icc_self ht
    have hu' : s.u' t = 0 := hasDerivWithinAt_Ici_eq_zero ht (fun x hx => (hz x hx).2.1) (s.du t ht)
    have := s.eb t ht (D.dt0 (s.φ t))
    rw [hu', (hz t ht').2.2.1, (hz t ht').2.2.2] at this
    simp only [inner_zero_left, Pi.zero_apply, zero_add, add_zero] at this
    exact hdinj (by rw [map_zero]; exact inner_self_eq_zero.mp this)

/-- Difference of two solutions of (6.3) with the same source (linearity, Thesis §6.2). -/
def DiscreteSolution.sub {T : ℝ} {f : ℝ → Pt1}
    (s₁ s₂ : DiscreteSolution D T f) : DiscreteSolution D T 0 where
  σ := s₁.σ - s₂.σ
  φ := s₁.φ - s₂.φ
  u := s₁.u - s₂.u
  M := s₁.M - s₂.M
  ρ := s₁.ρ - s₂.ρ
  lam := s₁.lam - s₂.lam
  σ' := s₁.σ' - s₂.σ'
  u' := s₁.u' - s₂.u'
  M' := s₁.M' - s₂.M'
  ρ' := s₁.ρ' - s₂.ρ'
  cσ := s₁.cσ.sub s₂.cσ
  cu := s₁.cu.sub s₂.cu
  cM := s₁.cM.sub s₂.cM
  cρ := s₁.cρ.sub s₂.cρ
  dσ := fun t ht => (s₁.dσ t ht).sub (s₂.dσ t ht)
  du := fun t ht => (s₁.du t ht).sub (s₂.du t ht)
  dM := fun t ht => (s₁.dM t ht).sub (s₂.dM t ht)
  dρ := fun t ht => (s₁.dρ t ht).sub (s₂.dρ t ht)
  ea := fun t ht τ ψ => by
    have h₁ := s₁.ea t ht τ ψ; have h₂ := s₂.ea t ht τ ψ
    simp only [Pi.sub_apply, inner_sub_left]; linarith
  eb := fun t ht v => by
    have h₁ := s₁.eb t ht v; have h₂ := s₂.eb t ht v
    simp only [Pi.sub_apply, map_sub, inner_sub_left, Pi.zero_apply, inner_zero_left]; linarith
  ec := fun t ht N => by
    have h₁ := s₁.ec t ht N; have h₂ := s₂.ec t ht N
    simp only [Pi.sub_apply, map_sub, inner_sub_left]; linarith
  ed := fun t ht μ => by
    have h₁ := s₁.ed t ht μ; have h₂ := s₂.ed t ht μ
    simp only [Pi.sub_apply, map_sub, inner_sub_left]; linarith
  ee := fun t ht ζ => by
    have h₁ := s₁.ee t ht ζ; have h₂ := s₂.ee t ht ζ
    have : D.d0 ((s₁.σ - s₂.σ) t) - D.S0 ((s₁.φ - s₂.φ) t) =
        (D.d0 (s₁.σ t) - D.S0 (s₁.φ t)) - (D.d0 (s₂.σ t) - D.S0 (s₂.φ t)) := by
      simp only [Pi.sub_apply, map_sub]; abel
    rw [this, inner_sub_left]; linarith

/-- **Corrected Prop 6.2, uniqueness.** Two solutions of (6.3) with the same source and the same
data `(σ, u, M, ρ)(0)` agree: `σₕ, uₕ, Mₕ, ρₕ, λₕ` on `[0,T]`, `φₕ` on `[0,T)`.
See [QuennevilleBelair2015], Prop 6.2. -/
theorem DiscreteSolution.unique {T : ℝ} {f : ℝ → Pt1} (s₁ s₂ : DiscreteSolution D T f)
    (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)
    (h0 : s₁.σ 0 = s₂.σ 0 ∧ s₁.u 0 = s₂.u 0 ∧ s₁.M 0 = s₂.M 0 ∧ s₁.ρ 0 = s₂.ρ 0) :
    (∀ t ∈ Icc 0 T, s₁.σ t = s₂.σ t ∧ s₁.u t = s₂.u t ∧ s₁.M t = s₂.M t ∧ s₁.ρ t = s₂.ρ t ∧
      s₁.lam t = s₂.lam t) ∧ (∀ t ∈ Ico 0 T, s₁.φ t = s₂.φ t) := by
  obtain ⟨h1, h2⟩ := (s₁.sub s₂).eq_zero_of_initial_eq_zero hdinj hS (by
    simp only [DiscreteSolution.sub, Pi.sub_apply, h0.1, h0.2.1, h0.2.2.1, h0.2.2.2, sub_self]; simp)
  refine ⟨fun t ht => ?_, fun t ht => sub_eq_zero.mp (h2 t ht)⟩
  obtain ⟨a, b, c, d, e⟩ := h1 t ht
  exact ⟨sub_eq_zero.mp a, sub_eq_zero.mp b, sub_eq_zero.mp c, sub_eq_zero.mp d,
    sub_eq_zero.mp e⟩

/-! ### Existence for (6.3) (corrected Prop 6.2) -/

section Existence

variable [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P1] [FiniteDimensional ℝ P2]
  [FiniteDimensional ℝ Pt0] [FiniteDimensional ℝ Pt1] [FiniteDimensional ℝ Pt2]

variable (D) in
/-- `Ψ φ = (S₀,ₕ φ, P_K(d* d φ))`, `K = ker S₀,ₕ`: bijective when `d` is injective and `S₀,ₕ`
surjective; it splits `φₕ` into its `Γₕ`-determined part and its `K`-part. -/
def psi : Pt0 →ₗ[ℝ] P1 × LinearMap.ker D.S0 :=
  D.S0.prod ((LinearMap.ker D.S0).orthogonalProjectionOnto.toLinearMap ∘ₗ
    (LinearMap.adjoint D.dt0 ∘ₗ D.dt0))

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P1] [FiniteDimensional ℝ P2]
  [FiniteDimensional ℝ Pt2] in
/-- Unfolding of `psi`. -/
lemma psi_apply (φ : Pt0) : psi D φ = (D.S0 φ,
    (LinearMap.ker D.S0).orthogonalProjectionOnto (LinearMap.adjoint D.dt0 (D.dt0 φ))) := rfl

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P1] [FiniteDimensional ℝ P2]
  [FiniteDimensional ℝ Pt2] in
/-- The `K`-component of `Ψ φ` tested against `ψ ∈ K` is `(dφ, dψ)`. -/
lemma inner_psi_snd (φ : Pt0) (k : LinearMap.ker D.S0) :
    ⟪k, (psi D φ).2⟫ = ⟪D.dt0 φ, D.dt0 k⟫ := by
  rw [psi_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    LinearMap.adjoint_inner_right, real_inner_comm]

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt2] in
/-- `Ψ` is injective (`d` injective) and hence bijective (`dim P1 + dim K = dim Ṽₕ⁰`). -/
lemma psi_bijective (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0) :
    Function.Bijective (psi D) := by
  have hinj : Function.Injective (psi D) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    have h1 : D.S0 φ = 0 := congrArg Prod.fst hφ
    have h3 := inner_psi_snd (D := D) φ ⟨φ, h1⟩
    rw [hφ, Prod.snd_zero, inner_zero_right] at h3
    exact hdinj (by rw [map_zero]; exact inner_self_eq_zero.mp h3.symm)
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  have := LinearMap.finrank_range_add_finrank_ker D.S0
  rw [LinearMap.range_eq_top.mpr hS, finrank_top] at this
  rw [Module.finrank_prod, this]

variable (D) in
/-- `Φ(σ, w)`: the unique `φ` with `S₀,ₕ φ = dσ` and `(dφ, dψ) = (w, dψ)` on `ker S₀,ₕ`. -/
def phiMap (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0) :
    P0 × Pt1 →ₗ[ℝ] Pt0 :=
  (LinearEquiv.ofBijective (psi D) (psi_bijective hdinj hS)).symm.toLinearMap ∘ₗ
    ((D.d0 ∘ₗ LinearMap.fst ℝ P0 Pt1).prod
      ((LinearMap.ker D.S0).orthogonalProjectionOnto.toLinearMap ∘ₗ
        (LinearMap.adjoint D.dt0 ∘ₗ LinearMap.snd ℝ P0 Pt1)))

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt2] in
/-- `Ψ ∘ Φ = (d ∘ fst, P_K d* ∘ snd)`. -/
lemma psi_phiMap (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)
    (x : P0 × Pt1) :
    psi D (phiMap D hdinj hS x) = (D.d0 x.1,
      (LinearMap.ker D.S0).orthogonalProjectionOnto (LinearMap.adjoint D.dt0 x.2)) := by
  have := (LinearEquiv.ofBijective (psi D) (psi_bijective hdinj hS)).apply_symm_apply
    (D.d0 x.1, (LinearMap.ker D.S0).orthogonalProjectionOnto (LinearMap.adjoint D.dt0 x.2))
  rw [LinearEquiv.ofBijective_apply] at this
  exact this

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt2] in
/-- `S₀,ₕ Φ(σ, w) = dσ`: `Φ` lands in the constraint `Γₕ`. -/
lemma S0_phiMap (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)
    (x : P0 × Pt1) : D.S0 (phiMap D hdinj hS x) = D.d0 x.1 :=
  congrArg Prod.fst (psi_phiMap hdinj hS x)

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt2] in
/-- The `K`-equation `(dΦ(σ, w), dψ) = (w, dψ)`, `ψ ∈ ker S₀,ₕ`. -/
lemma inner_phiMap (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)
    (x : P0 × Pt1) {ψ : Pt0} (hψ : D.S0 ψ = 0) :
    ⟪D.dt0 (phiMap D hdinj hS x), D.dt0 ψ⟫ = ⟪x.2, D.dt0 ψ⟫ := by
  have h := inner_psi_snd (D := D) (phiMap D hdinj hS x) ⟨ψ, hψ⟩
  rw [psi_phiMap, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    LinearMap.adjoint_inner_right, real_inner_comm] at h
  exact h.symm

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt2] in
/-- `Φ(σ, w)` is the only `φ` satisfying the constraint and the `K`-equation. -/
lemma phiMap_eq (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)
    {σ : P0} {w : Pt1} {φ : Pt0} (h1 : D.d0 σ = D.S0 φ)
    (h3 : ∀ ψ, D.S0 ψ = 0 → ⟪D.dt0 φ, D.dt0 ψ⟫ = ⟪w, D.dt0 ψ⟫) :
    phiMap D hdinj hS (σ, w) = φ := by
  apply (psi_bijective hdinj hS).1
  rw [psi_phiMap]
  refine Prod.ext (by rw [psi_apply]; exact h1) ?_
  apply ext_inner_left ℝ
  intro k
  rw [inner_psi_snd, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    LinearMap.adjoint_inner_right, real_inner_comm, h3 k k.2]

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt1]
  [FiniteDimensional ℝ Pt2] in
/-- `range S₀,ₕ* = (ker S₀,ₕ)ᗮ`. -/
lemma exists_adjoint_S0 {z : Pt0} (hz : ∀ ψ, D.S0 ψ = 0 → ⟪z, ψ⟫ = 0) :
    ∃ μ, LinearMap.adjoint D.S0 μ = z := by
  set R := LinearMap.range (LinearMap.adjoint D.S0)
  have hR : Rᗮ = LinearMap.ker D.S0 := by
    ext x
    rw [Submodule.mem_orthogonal', LinearMap.mem_ker]
    constructor
    · intro h
      have := h (LinearMap.adjoint D.S0 (D.S0 x)) ⟨_, rfl⟩
      rw [LinearMap.adjoint_inner_right] at this
      exact inner_self_eq_zero.mp this
    · rintro h _ ⟨μ, rfl⟩
      rw [LinearMap.adjoint_inner_right, h, inner_zero_left]
  have : z ∈ Rᗮᗮ := by
    rw [hR, Submodule.mem_orthogonal']
    intro ψ hψ; exact hz ψ hψ
  rw [Submodule.orthogonal_orthogonal] at this
  exact this

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt1]
  [FiniteDimensional ℝ Pt2] in
/-- `S₀,ₕ` surjective ⇒ `S₀,ₕ*` injective (so `λₕ` is determined). -/
lemma adjoint_S0_injective (hS : Function.Surjective D.S0) :
    Function.Injective (LinearMap.adjoint D.S0) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro μ hμ
  obtain ⟨ψ, rfl⟩ := hS μ
  have := congrArg (fun z => ⟪z, ψ⟫) hμ
  simp only [LinearMap.adjoint_inner_left, inner_zero_left] at this
  exact inner_self_eq_zero.mp this

/-- **Corrected Prop 6.2, existence.** Assume finite-dimensional FE spaces, `d : Ṽₕ⁰ → Ṽₕ¹`
injective, `S₀,ₕ` surjective (thesis hypothesis (5.4)) and `f` continuous. Data satisfying the
compatibility conditions (C1)–(C3) admit a solution of (6.3) on `[0,T]`,
with `λₕ` determined (no initial value). Regularity is exported: `σₕ, uₕ, Mₕ, ρₕ` have
two-sided derivatives at every `t ∈ ℝ` (equal to the derivative fields of the solution), those
derivatives are continuous (so the dynamic variables are `C¹`), and `φₕ`, `λₕ` are continuous
(the thesis' `φₕ ∈ C⁰`, `λₕ ∈ C⁰`; `λₕ ∈ C¹` when `f ∈ C¹` since `λₕ` is a fixed linear image of
`uₕ`).

Thesis gap: the thesis argues "the system is square, so uniqueness implies existence", which is
invalid for this differential-algebraic system (see `not_exists_discreteSolution_of_ker`). Proof
here:
eliminate `φₕ = Φ(σₕ, f)` and `λₕ = (S₀,ₕ*)⁻¹ d* uₕ`, solve the resulting linear ODE by
variation of constants (`exists_hasDerivAt_linearODE`), and show the hidden constraint (C2)
propagates.
See [QuennevilleBelair2015], Prop 6.2 and hypothesis (5.4) [QuennevilleBelair2015], §5.2;
cf. [Pazy1983], Ch. 4. -/
theorem exists_discreteSolution_regular (hdinj : Function.Injective D.dt0)
    (hS : Function.Surjective D.S0)
    {f : ℝ → Pt1} (hf : Continuous f) (T : ℝ) {σ₀ : P0} {φ₀ : Pt0} {u₀ : Pt1} {M₀ : P2}
    {ρ₀ : Pt2} (hC1 : D.d0 σ₀ = D.S0 φ₀) (hC2 : ∀ ψ, D.S0 ψ = 0 → ⟪u₀, D.dt0 ψ⟫ = 0)
    (hC3 : ∀ ψ, D.S0 ψ = 0 → ⟪D.dt0 φ₀, D.dt0 ψ⟫ = ⟪f 0, D.dt0 ψ⟫) :
    ∃ s : DiscreteSolution D T f, (s.σ 0 = σ₀ ∧ s.φ 0 = φ₀ ∧ s.u 0 = u₀ ∧ s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ∧
      (∀ t, HasDerivAt s.σ (s.σ' t) t) ∧ (∀ t, HasDerivAt s.u (s.u' t) t) ∧
      (∀ t, HasDerivAt s.M (s.M' t) t) ∧ (∀ t, HasDerivAt s.ρ (s.ρ' t) t) ∧
      Continuous s.σ' ∧ Continuous s.u' ∧ Continuous s.M' ∧ Continuous s.ρ' ∧
      Continuous s.φ ∧ Continuous s.lam := by
  classical
  set Φ := phiMap D hdinj hS
  obtain ⟨R, hR⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.adjoint D.S0)
    (LinearMap.ker_eq_bot.mpr (adjoint_S0_injective hS))
  -- the ODE operator on X = P0 × Pt1 × P2 × Pt2
  let pu : P0 × Pt1 × P2 × Pt2 →ₗ[ℝ] Pt1 := (LinearMap.fst ℝ _ _) ∘ₗ (LinearMap.snd ℝ _ _)
  let pM : P0 × Pt1 × P2 × Pt2 →ₗ[ℝ] P2 :=
    (LinearMap.fst ℝ _ _) ∘ₗ (LinearMap.snd ℝ _ _) ∘ₗ (LinearMap.snd ℝ _ _)
  let pρ : P0 × Pt1 × P2 × Pt2 →ₗ[ℝ] Pt2 :=
    (LinearMap.snd ℝ _ _) ∘ₗ (LinearMap.snd ℝ _ _) ∘ₗ (LinearMap.snd ℝ _ _)
  let 𝒜 : P0 × Pt1 × P2 × Pt2 →ₗ[ℝ] P0 × Pt1 × P2 × Pt2 :=
    (LinearMap.adjoint D.d0 ∘ₗ R ∘ₗ LinearMap.adjoint D.dt0 ∘ₗ pu).prod
      ((-(D.dt0 ∘ₗ Φ ∘ₗ LinearMap.inl ℝ P0 Pt1 ∘ₗ LinearMap.fst ℝ _ _)
          - LinearMap.adjoint D.S1 ∘ₗ pM - LinearMap.adjoint D.dt1 ∘ₗ pρ).prod
        ((D.S1 ∘ₗ pu).prod (D.dt1 ∘ₗ pu)))
  let F : ℝ → P0 × Pt1 × P2 × Pt2 := fun t => (0, f t - D.dt0 (Φ (0, f t)), 0, 0)
  have hF : Continuous F := by
    have hl : Continuous fun w : Pt1 => D.dt0 (Φ (0, w)) :=
      ((D.dt0 ∘ₗ Φ ∘ₗ LinearMap.inr ℝ P0 Pt1).continuous_of_finiteDimensional)
    exact continuous_const.prodMk ((hf.sub (hl.comp hf)).prodMk continuous_const)
  obtain ⟨x, hx0, hx⟩ := exists_hasDerivAt_linearODE (LinearMap.toContinuousLinearMap 𝒜) hF (σ₀, u₀, M₀, ρ₀)
  -- components
  set σ : ℝ → P0 := fun t => (x t).1
  set u : ℝ → Pt1 := fun t => (x t).2.1
  set M : ℝ → P2 := fun t => (x t).2.2.1
  set ρ : ℝ → Pt2 := fun t => (x t).2.2.2
  set φ : ℝ → Pt0 := fun t => Φ (σ t, f t)
  set lam : ℝ → P1 := fun t => R (LinearMap.adjoint D.dt0 (u t))
  set u' : ℝ → Pt1 := fun t => f t - D.dt0 (φ t) - LinearMap.adjoint D.S1 (M t)
    - LinearMap.adjoint D.dt1 (ρ t)
  have hσ : ∀ t, HasDerivAt σ (LinearMap.adjoint D.d0 (lam t)) t := fun t => by
    have := (ContinuousLinearMap.fst ℝ P0 (Pt1 × P2 × Pt2)).hasFDerivAt.comp_hasDerivAt t (hx t)
    refine this.congr_deriv ?_
    simp [𝒜, F, pu, lam, u, LinearMap.coe_toContinuousLinearMap']
  have hu : ∀ t, HasDerivAt u (u' t) t := fun t => by
    have := ((ContinuousLinearMap.fst ℝ Pt1 (P2 × Pt2)).comp
      (ContinuousLinearMap.snd ℝ P0 (Pt1 × P2 × Pt2))).hasFDerivAt.comp_hasDerivAt t (hx t)
    refine this.congr_deriv ?_
    have hΦ : Φ (σ t, f t) = Φ (σ t, 0) + Φ (0, f t) := by
      rw [← map_add]; simp
    simp only [u', φ, hΦ, map_add]
    simp [𝒜, F, pM, pρ, σ, M, ρ, LinearMap.coe_toContinuousLinearMap']
    abel
  have hM : ∀ t, HasDerivAt M (D.S1 (u t)) t := fun t => by
    have := ((ContinuousLinearMap.fst ℝ P2 Pt2).comp ((ContinuousLinearMap.snd ℝ Pt1 (P2 × Pt2)).comp
      (ContinuousLinearMap.snd ℝ P0 (Pt1 × P2 × Pt2)))).hasFDerivAt.comp_hasDerivAt t (hx t)
    refine this.congr_deriv ?_
    simp [𝒜, F, pu, u, LinearMap.coe_toContinuousLinearMap']
  have hρ : ∀ t, HasDerivAt ρ (D.dt1 (u t)) t := fun t => by
    have := ((ContinuousLinearMap.snd ℝ P2 Pt2).comp ((ContinuousLinearMap.snd ℝ Pt1 (P2 × Pt2)).comp
      (ContinuousLinearMap.snd ℝ P0 (Pt1 × P2 × Pt2)))).hasFDerivAt.comp_hasDerivAt t (hx t)
    refine this.congr_deriv ?_
    simp [𝒜, F, pu, u, LinearMap.coe_toContinuousLinearMap']
  -- the hidden constraint propagates
  have hhid : ∀ t ψ, D.S0 ψ = 0 → ⟪u t, D.dt0 ψ⟫ = 0 := by
    intro t ψ hψ
    have hg : ∀ t, HasDerivAt (fun t => ⟪u t, D.dt0 ψ⟫) 0 t := fun t => by
      have := HasDerivAt.inner ℝ (hu t) (hasDerivAt_const t (D.dt0 ψ))
      refine this.congr_deriv ?_
      have hS1 : D.S1 (D.dt0 ψ) = 0 := by
        have := D.anticomm ψ; rw [hψ, map_zero] at this; exact neg_eq_zero.mp this.symm
      simp only [inner_zero_right, zero_add, u', inner_sub_left, LinearMap.adjoint_inner_left,
        hS1, D.dt1_dt0, inner_zero_right, sub_zero]
      rw [inner_phiMap hdinj hS _ hψ, sub_self]
    have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt)
      (fun t => (hg t).deriv) t 0
    rw [hc]
    simpa [u, hx0] using hC2 ψ hψ
  have hlam : ∀ t, LinearMap.adjoint D.S0 (lam t) = LinearMap.adjoint D.dt0 (u t) := fun t => by
    obtain ⟨μ, hμ⟩ := exists_adjoint_S0 (D := D) (z := LinearMap.adjoint D.dt0 (u t)) (fun ψ hψ => by
      rw [LinearMap.adjoint_inner_left]; exact hhid t ψ hψ)
    simp only [lam, ← hμ]
    rw [show R (LinearMap.adjoint D.S0 μ) = μ from LinearMap.congr_fun hR μ]
  have hσc : Continuous σ := continuous_iff_continuousAt.2 fun t => (hσ t).continuousAt
  have huc : Continuous u := continuous_iff_continuousAt.2 fun t => (hu t).continuousAt
  have hφc : Continuous φ := Φ.continuous_of_finiteDimensional.comp (hσc.prodMk hf)
  have hlamc : Continuous lam := R.continuous_of_finiteDimensional.comp
    ((LinearMap.adjoint D.dt0).continuous_of_finiteDimensional.comp huc)
  have hMc : Continuous M := continuous_iff_continuousAt.2 fun t => (hM t).continuousAt
  have hρc : Continuous ρ := continuous_iff_continuousAt.2 fun t => (hρ t).continuousAt
  refine ⟨{
    σ := σ, φ := φ, u := u, M := M, ρ := ρ, lam := lam
    σ' := fun t => LinearMap.adjoint D.d0 (lam t), u' := u'
    M' := fun t => D.S1 (u t), ρ' := fun t => D.dt1 (u t)
    cσ := (continuous_iff_continuousAt.2 fun t => (hσ t).continuousAt).continuousOn, cu := (continuous_iff_continuousAt.2 fun t => (hu t).continuousAt).continuousOn, cM := (continuous_iff_continuousAt.2 fun t => (hM t).continuousAt).continuousOn, cρ := (continuous_iff_continuousAt.2 fun t => (hρ t).continuousAt).continuousOn
    dσ := fun t _ => (hσ t).hasDerivWithinAt
    du := fun t _ => (hu t).hasDerivWithinAt
    dM := fun t _ => (hM t).hasDerivWithinAt
    dρ := fun t _ => (hρ t).hasDerivWithinAt
    ea := fun t _ τ ψ => by
      rw [LinearMap.adjoint_inner_left, inner_sub_right, ← LinearMap.adjoint_inner_left D.S0,
        hlam, LinearMap.adjoint_inner_left]
      ring
    eb := fun t _ v => by
      simp only [u', inner_sub_left, LinearMap.adjoint_inner_left]; ring
    ec := fun t _ N => sub_self _
    ed := fun t _ μ => sub_self _
    ee := fun t _ ζ => by
      show ⟪D.d0 (σ t) - D.S0 (Φ (σ t, f t)), ζ⟫ = 0
      rw [show D.S0 (Φ (σ t, f t)) = D.d0 (σ t) from S0_phiMap hdinj hS _, sub_self,
        inner_zero_left] }, ⟨?_, ?_, ?_, ?_, ?_⟩, hσ, hu, hM, hρ, ?_, ?_, ?_, ?_, hφc, hlamc⟩
  · simp [σ, hx0]
  · show Φ (σ 0, f 0) = φ₀
    rw [show σ 0 = σ₀ by simp [σ, hx0]]
    exact phiMap_eq hdinj hS hC1 hC3
  · simp [u, hx0]
  · simp [M, hx0]
  · simp [ρ, hx0]
  · exact (LinearMap.adjoint D.d0).continuous_of_finiteDimensional.comp hlamc
  · exact ((hf.sub (D.dt0.continuous_of_finiteDimensional.comp hφc)).sub
      ((LinearMap.adjoint D.S1).continuous_of_finiteDimensional.comp hMc)).sub
      ((LinearMap.adjoint D.dt1).continuous_of_finiteDimensional.comp hρc)
  · exact D.S1.continuous_of_finiteDimensional.comp huc
  · exact D.dt1.continuous_of_finiteDimensional.comp huc

/-- **Corrected Prop 6.2, existence** (data form of `exists_discreteSolution_regular`). Assume
finite-dimensional FE spaces, `d : Ṽₕ⁰ → Ṽₕ¹` injective, `S₀,ₕ` surjective and `f` continuous.
Data satisfying (C1)–(C3) admit a solution of (6.3) on `[0,T]`. See
[QuennevilleBelair2015], Prop 6.2. -/
theorem exists_discreteSolution (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)
    {f : ℝ → Pt1} (hf : Continuous f) (T : ℝ) {σ₀ : P0} {φ₀ : Pt0} {u₀ : Pt1} {M₀ : P2}
    {ρ₀ : Pt2} (hC1 : D.d0 σ₀ = D.S0 φ₀) (hC2 : ∀ ψ, D.S0 ψ = 0 → ⟪u₀, D.dt0 ψ⟫ = 0)
    (hC3 : ∀ ψ, D.S0 ψ = 0 → ⟪D.dt0 φ₀, D.dt0 ψ⟫ = ⟪f 0, D.dt0 ψ⟫) :
    ∃ s : DiscreteSolution D T f, s.σ 0 = σ₀ ∧ s.φ 0 = φ₀ ∧ s.u 0 = u₀ ∧ s.M 0 = M₀ ∧ s.ρ 0 = ρ₀ :=
  let ⟨s, hs, _⟩ := exists_discreteSolution_regular (M₀ := M₀) (ρ₀ := ρ₀) hdinj hS hf T hC1 hC2 hC3
  ⟨s, hs⟩


/-- **Corrected Prop 6.2 (existence ⇔ compatibility).** For `T > 0`, `d` injective on `Ṽₕ⁰`,
`S₀,ₕ` surjective and `f` continuous, (6.3) has a solution with data `(σ₀, φ₀, u₀, M₀, ρ₀)` iff
(C1) `dσ₀ = S₀,ₕφ₀`, (C2) `u₀ ⊥ d(ker S₀,ₕ)` and (C3) `(dφ₀ − f(0), dψ) = 0` on `ker S₀,ₕ`.
The solution is unique (`DiscreteSolution.unique`). Corrects [QuennevilleBelair2015], Prop 6.2.
[QuennevilleBelair2015], Prop 6.2 (corrected) -/
theorem exists_discreteSolution_iff {T : ℝ} (hT : 0 < T) (hdinj : Function.Injective D.dt0)
    (hS : Function.Surjective D.S0) {f : ℝ → Pt1} (hf : Continuous f) (σ₀ : P0) (φ₀ : Pt0)
    (u₀ : Pt1) (M₀ : P2) (ρ₀ : Pt2) :
    (∃ s : DiscreteSolution D T f, s.σ 0 = σ₀ ∧ s.φ 0 = φ₀ ∧ s.u 0 = u₀ ∧ s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ↔
      D.d0 σ₀ = D.S0 φ₀ ∧ (∀ ψ, D.S0 ψ = 0 → ⟪u₀, D.dt0 ψ⟫ = 0) ∧
        (∀ ψ, D.S0 ψ = 0 → ⟪D.dt0 φ₀, D.dt0 ψ⟫ = ⟪f 0, D.dt0 ψ⟫) := by
  constructor
  · rintro ⟨s, hσ, hφ, hu, -, -⟩
    have := DiscreteSolution.compatible hT s
    rw [hσ, hφ, hu] at this
    exact this
  · rintro ⟨h1, h2, h3⟩
    exact exists_discreteSolution hdinj hS hf T h1 h2 h3

/-- A solution of (6.3) only sees the source on `[0,T)`. -/
def DiscreteSolution.ofEqOn {T : ℝ} {f g : ℝ → Pt1} (s : DiscreteSolution D T g)
    (h : ∀ t ∈ Ico 0 T, f t = g t) :
    DiscreteSolution D T f :=
  { s with eb := fun t ht v => by rw [h t ht]; exact s.eb t ht v }

/-- `exists_discreteSolution` for a source that is only continuous on `[0,T]` (the thesis' class
`f ∈ C⁰([0,T]; W̃¹)`), via the constant extension `f ∘ projIcc`. -/
theorem exists_discreteSolution_of_continuousOn (hdinj : Function.Injective D.dt0)
    (hS : Function.Surjective D.S0) {T : ℝ} (hT : 0 ≤ T) {f : ℝ → Pt1}
    (hf : ContinuousOn f (Icc 0 T)) {σ₀ : P0} {φ₀ : Pt0} {u₀ : Pt1} {M₀ : P2}
    {ρ₀ : Pt2} (hC1 : D.d0 σ₀ = D.S0 φ₀) (hC2 : ∀ ψ, D.S0 ψ = 0 → ⟪u₀, D.dt0 ψ⟫ = 0)
    (hC3 : ∀ ψ, D.S0 ψ = 0 → ⟪D.dt0 φ₀, D.dt0 ψ⟫ = ⟪f 0, D.dt0 ψ⟫) :
    ∃ s : DiscreteSolution D T f, s.σ 0 = σ₀ ∧ s.φ 0 = φ₀ ∧ s.u 0 = u₀ ∧ s.M 0 = M₀ ∧ s.ρ 0 = ρ₀ := by
  set g : ℝ → Pt1 := fun t => f (projIcc 0 T hT t)
  have hg : Continuous g :=
    hf.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun s => (projIcc 0 T hT s).2
  have hfg : ∀ t ∈ Icc 0 T, g t = f t := fun t ht => by simp [g, projIcc_of_mem hT ht]
  obtain ⟨s, hs⟩ := exists_discreteSolution hdinj hS hg T hC1 hC2
    (by rw [hfg 0 ⟨le_rfl, hT⟩]; exact hC3)
  exact ⟨s.ofEqOn fun t ht => (hfg t (Ico_subset_Icc_self ht)).symm, hs⟩

end Existence

end Discrete


/-! ## §3. Error equations (Prop 6.3) -/

section ErrorEquations

variable {W0 W1 W2 Wt1 Wt2 : Type*}
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]

/-- **Thesis Prop 6.3, first error equation.** Subtract (6.3a) from (6.2a) (with `λ ∈ W¹`)
and insert `Πₕσ̇`, `Π̃ₕu`. Here `Sψ = S₀ψ`, `Shψ = S₀,ₕψ`; `σd, σdh` are `σ̇, σ̇ₕ`.
Correction: the thesis writes `Πₕσ̇ₕ − σ̇ₕ` on the left; it must be `Πₕσ̇ − σ̇ₕ`. The term
`(λ, (S − Sₕ)ψ)` needs `λ ∈ W¹` (only `λ ∈ W̌¹` is automatic, `Solution.exists_multiplierSolution`).
See [QuennevilleBelair2015], Prop 6.3; cf. [QuennevilleBelair2015], Prop 5.6. [QuennevilleBelair2015], Prop 6.3 -/
theorem errorEq_a (σd σdh Pσ τ : W0) (u uh Pu dψ : Wt1) (lam lamh dτ Sψ Shψ : W1)
    (hc : ⟪σd, τ⟫ - ⟪u, dψ⟫ - ⟪lam, dτ - Sψ⟫ = 0)
    (hd : ⟪σdh, τ⟫ - ⟪uh, dψ⟫ - ⟪lamh, dτ - Shψ⟫ = 0) :
    ⟪Pσ - σdh, τ⟫ - ⟪Pu - uh, dψ⟫ - ⟪lam - lamh, dτ - Shψ⟫
      = ⟪Pσ - σd, τ⟫ - ⟪Pu - u, dψ⟫ - ⟪lam, Sψ - Shψ⟫ := by
  simp only [inner_sub_left, inner_sub_right] at *
  linarith

/-- **Thesis Prop 6.3, second error equation** (from (6.2b) − (6.3b)); `S, Sh : Ṽ¹ → W²`,
`d : Ṽ⁰ → Ṽ¹` and `d : Ṽ¹ → W̃²` are linear, so `d(Π̃φ − φₕ) = dΠ̃φ − dφₕ`.
See [QuennevilleBelair2015], Prop 6.3. -/
theorem errorEq_b {U Φ : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup Φ] [Module ℝ Φ]
    (ι : U →ₗ[ℝ] Wt1) (d0 : Φ →ₗ[ℝ] Wt1) (S Sh : U →ₗ[ℝ] W2) (d1 : U →ₗ[ℝ] Wt2)
    (ud udh Pud : Wt1) (fv : ℝ) (φ φh Pφ : Φ) (M Mh PM : W2) (ρ ρh Pρ : Wt2) (v : U)
    (hc : ⟪ud, ι v⟫ + ⟪d0 φ, ι v⟫ + ⟪M, S v⟫ + ⟪ρ, d1 v⟫ = fv)
    (hd : ⟪udh, ι v⟫ + ⟪d0 φh, ι v⟫ + ⟪Mh, Sh v⟫ + ⟪ρh, d1 v⟫ = fv) :
    ⟪Pud - udh, ι v⟫ + ⟪d0 (Pφ - φh), ι v⟫ + ⟪PM - Mh, Sh v⟫ + ⟪Pρ - ρh, d1 v⟫
      = ⟪Pud - ud, ι v⟫ + ⟪d0 (Pφ - φ), ι v⟫ + ⟪PM - M, Sh v⟫ - ⟪M, S v - Sh v⟫
        + ⟪Pρ - ρ, d1 v⟫ := by
  simp only [map_sub, inner_sub_left, inner_sub_right] at *
  linarith

/-- **Thesis Prop 6.3, third error equation** (from (6.2c) − (6.3c)), with `Sₕ` defined on the
whole space `U` (e.g. `Π²ₕ` bounded on `L²`). See [QuennevilleBelair2015], Prop 6.3. -/
theorem errorEq_c {U : Type*} [AddCommGroup U] [Module ℝ U] (S Sh : U →ₗ[ℝ] W2)
    (Md Mdh PMd N : W2) (u uh Pu : U)
    (hc : ⟪Md, N⟫ - ⟪S u, N⟫ = 0) (hd : ⟪Mdh, N⟫ - ⟪Sh uh, N⟫ = 0) :
    ⟪PMd - Mdh, N⟫ - ⟪Sh (Pu - uh), N⟫
      = ⟪PMd - Md, N⟫ - ⟪Sh (Pu - u), N⟫ + ⟪S u - Sh u, N⟫ := by
  simp only [map_sub, inner_sub_left] at *
  linarith

/-- **Prop 6.3(c), corrected.** Thesis gap: `Sₕu = Π²ₕS₁u` applies the canonical `Π²ₕ` to
`S₁u ∈ L²`, where it is undefined. Splitting `Su − Sₕuₕ = S(u − Π̃u) + (S − Sₕ)Π̃u + Sₕ(Π̃u − uₕ)`
only applies `Sₕ` to discrete functions (`Uh` the discrete subspace).
Corrects [QuennevilleBelair2015], Prop 6.3. -/
theorem errorEq_c_split {U : Type*} [AddCommGroup U] [Module ℝ U] {Uh : Submodule ℝ U}
    (S : U →ₗ[ℝ] W2) (Sh : Uh →ₗ[ℝ] W2) (Md Mdh PMd N : W2) (u : U) (uh Pu : Uh)
    (hc : ⟪Md, N⟫ - ⟪S u, N⟫ = 0) (hd : ⟪Mdh, N⟫ - ⟪Sh uh, N⟫ = 0) :
    ⟪PMd - Mdh, N⟫ - ⟪Sh (Pu - uh), N⟫
      = ⟪PMd - Md, N⟫ + ⟪S (u - Pu), N⟫ + ⟪S Pu - Sh Pu, N⟫ := by
  simp only [map_sub, inner_sub_left] at *
  linarith

/-- **Thesis Prop 6.3, fourth error equation** (from (6.2d) − (6.3d)).
See [QuennevilleBelair2015], Prop 6.3. -/
theorem errorEq_d {U : Type*} [AddCommGroup U] [Module ℝ U] (d1 : U →ₗ[ℝ] Wt2)
    (ρd ρdh Pρd μ : Wt2) (u uh Pu : U)
    (hc : ⟪ρd, μ⟫ - ⟪d1 u, μ⟫ = 0) (hd : ⟪ρdh, μ⟫ - ⟪d1 uh, μ⟫ = 0) :
    ⟪Pρd - ρdh, μ⟫ - ⟪d1 (Pu - uh), μ⟫ = ⟪Pρd - ρd, μ⟫ - ⟪d1 (Pu - u), μ⟫ := by
  simp only [map_sub, inner_sub_left] at *
  linarith

/-- **Prop 6.3, fifth (constraint) error equation**, missing from the thesis although
`ζ ∈ Vₕ¹` is listed (from (6.2e) − (6.3e)). Completes [QuennevilleBelair2015], Prop 6.3 (added). -/
theorem errorEq_e {V Φ : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup Φ] [Module ℝ Φ]
    (d0 : V →ₗ[ℝ] W1) (S Sh : Φ →ₗ[ℝ] W1) (σ σh Pσ : V) (φ φh Pφ : Φ) (ζ : W1)
    (hc : ⟪d0 σ - S φ, ζ⟫ = 0) (hd : ⟪d0 σh - Sh φh, ζ⟫ = 0) :
    ⟪d0 (Pσ - σh) - Sh (Pφ - φh), ζ⟫ = ⟪d0 (Pσ - σ) - (Sh Pφ - S φ), ζ⟫ := by
  simp only [map_sub, inner_sub_left] at *
  linarith

end ErrorEquations

/-! ## §4. Energy estimate and a conditional convergence theorem (missing from Ch 6) -/

section Convergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **New theorem: conditional convergence for Ch 6** (the thesis states none).

Abstract setting. Dynamic variables `ξ ∈ X` (σ, u, M, ρ: the energy norm), algebraic variables
in `Z` (φ), multipliers in `Y` (λ); `Xh ⊆ X × Z` the discrete space; `A, Ah` the continuous and
discrete skew spatial forms; `Bh` the discrete constraint `(dσ − Sₕφ, ·)`.
* `hcont`: the continuous solution satisfies (6.2) tested with discrete functions
  (`ℓ t` = continuous multiplier term, any functional, e.g. `Λ(t) ∈ W̌¹`);
* `hdisc`, `hBh`: the discrete solution satisfies (6.3), including the constraint (6.3e);
* `hproj`: the projection `(P ξ, Q)` with `Πλ` is the corrected elliptic projection (6.4) (the
  thesis' (6.4) is garbled and its well-posedness is open; it enters as a hypothesis);
* `hskew`: `Ah` is skew on `Xh`.
Then `‖ξ(t) − ξₕ(t)‖ ≤ ‖(I − P)ξ(t)‖ + ‖Pξ(0) − ξₕ(0)‖ + ∫₀ᵗ ‖(P − I)ξ̇‖`.
Analogue for (6.3) of [QuennevilleBelair2015], Thm 4.14 (via Lemma 4.12), with the elliptic
projection (6.4) of [QuennevilleBelair2015], §6.2; cf. the classical energy/elliptic-projection
estimates [Baker1976], [Dupont1973], [Geveci1988] and, in FEEC, [GilletteHolstZhu2017]. -/
theorem norm_sub_le_of_ellipticProjection {X Z Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X]
    [AddCommGroup Z] [Module ℝ Z] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (Xh : Submodule ℝ (X × Z)) (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ)
    (Bh : (X × Z) →ₗ[ℝ] Y) (P : X →L[ℝ] X) {T : ℝ}
    -- continuous solution
    (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hξc : ContinuousOn ξ (Icc 0 T)) (hξ'c : ContinuousOn ξ' (Icc 0 T))
    (hξd : ∀ t ∈ Ico 0 T, HasDerivWithinAt ξ (ξ' t) (Ici t) t)
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ Xh, ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    -- discrete solution
    (ξh ξh' : ℝ → X) (χh : ℝ → Z) (lamh : ℝ → Y)
    (hmem : ∀ t ∈ Icc 0 T, (ξh t, χh t) ∈ Xh) (hBh : ∀ t ∈ Icc 0 T, Bh (ξh t, χh t) = 0)
    (hξhc : ContinuousOn ξh (Icc 0 T))
    (hξhd : ∀ t ∈ Ico 0 T, HasDerivWithinAt ξh (ξh' t) (Ici t) t)
    (hdisc : ∀ t ∈ Ico 0 T, ∀ η ∈ Xh,
      ⟪ξh' t, η.1⟫ + Ah (ξh t, χh t) η - ⟪lamh t, Bh η⟫ = ⟪F t, η.1⟫)
    -- projection
    (Q : ℝ → Z) (lamP : ℝ → Y) (hPmem : ∀ t ∈ Icc 0 T, (P (ξ t), Q t) ∈ Xh)
    (hPB : ∀ t ∈ Icc 0 T, Bh (P (ξ t), Q t) = 0)
    (hproj : ∀ t ∈ Ico 0 T, ∀ η ∈ Xh,
      Ah (P (ξ t), Q t) η - ⟪lamP t, Bh η⟫ = A (ξ t, χ t) η - ℓ t η)
    (hskew : ∀ η ∈ Xh, Ah η η = 0) :
    ∀ t ∈ Icc 0 T, ‖ξ t - ξh t‖ ≤
      ‖ξ t - P (ξ t)‖ + ‖P (ξ 0) - ξh 0‖ + ∫ s in (0:ℝ)..t, ‖P (ξ' s) - ξ' s‖ := by
  set e : ℝ → X := fun t => P (ξ t) - ξh t
  set e' : ℝ → X := fun t => P (ξ' t) - ξh' t
  have hE : ∀ t ∈ Icc 0 T, (e t, Q t - χh t) ∈ Xh := fun t ht => by
    have := Xh.sub_mem (hPmem t ht) (hmem t ht); simpa [e] using this
  have hEB : ∀ t ∈ Icc 0 T, Bh (e t, Q t - χh t) = 0 := fun t ht => by
    have : ((e t, Q t - χh t) : X × Z) = (P (ξ t), Q t) - (ξh t, χh t) := by simp [e]
    rw [this, map_sub, hPB t ht, hBh t ht, sub_zero]
  have herr : ∀ t ∈ Ico 0 T, ⟪e' t, e t⟫ = ⟪P (ξ' t) - ξ' t, e t⟫ := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    set η : X × Z := (e t, Q t - χh t)
    have h1 := hcont t ht η (hE t ht')
    have h2 := hdisc t ht η (hE t ht')
    have h3 := hproj t ht η (hE t ht')
    have h4 := hskew η (hE t ht')
    have hsplit : η = (P (ξ t), Q t) - (ξh t, χh t) := by simp [η, e]
    rw [hEB t ht', inner_zero_right, sub_zero] at h2
    rw [hEB t ht', inner_zero_right, sub_zero] at h3
    have h5 : Ah η η = Ah (P (ξ t), Q t) η - Ah (ξh t, χh t) η := by
      have : Ah η = Ah (P (ξ t), Q t) - Ah (ξh t, χh t) := by rw [hsplit, map_sub]
      rw [this, LinearMap.sub_apply]
    simp only [e', inner_sub_left]
    simp only [η] at h1 h2 h3 h4 h5 ⊢
    linarith
  exact Variational.norm_sub_le_of_projected_error (𝕜 := ℝ) (u := ξ) (p := fun t => P (ξ t))
    (uh := ξh) (ε' := e') ((P.continuous.comp_continuousOn hξc).sub hξhc)
    (fun t ht => (P.hasFDerivAt.comp_hasDerivWithinAt t (hξd t ht)).sub (hξhd t ht))
    ((P.continuous.comp_continuousOn hξ'c).sub hξ'c).norm (fun _ _ => norm_nonneg _)
    fun t ht => by
      rw [RCLike.re_to_real]
      exact (herr t ht).trans_le (real_inner_le_norm _ _)

/-- Rate form of `norm_sub_le_of_ellipticProjection`: if the projection errors and the initial
discrete error are
`≤ ε` (e.g. `ε = C hʳ` from Thm 5.5-type approximation estimates, which are hypotheses here),
then `‖ξ(t) − ξₕ(t)‖ ≤ ε (2 + t)`. Cf. [QuennevilleBelair2015], Thm 5.5, Thm 4.14. -/
theorem norm_sub_le_mul_of_ellipticProjection {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X]
    {ξ ξ' ξh : ℝ → X} {P : X →L[ℝ] X} {T ε : ℝ} (hξ'c : ContinuousOn ξ' (Icc 0 T))
    (hconv : ∀ t ∈ Icc 0 T, ‖ξ t - ξh t‖ ≤
      ‖ξ t - P (ξ t)‖ + ‖P (ξ 0) - ξh 0‖ + ∫ s in (0:ℝ)..t, ‖P (ξ' s) - ξ' s‖)
    (h1 : ∀ t ∈ Icc 0 T, ‖ξ t - P (ξ t)‖ ≤ ε) (h2 : ‖P (ξ 0) - ξh 0‖ ≤ ε)
    (h3 : ∀ t ∈ Icc 0 T, ‖P (ξ' t) - ξ' t‖ ≤ ε) :
    ∀ t ∈ Icc 0 T, ‖ξ t - ξh t‖ ≤ ε * (2 + t) := by
  intro t ht
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hint : ∫ s in (0:ℝ)..t, ‖P (ξ' s) - ξ' s‖ ≤ ∫ s in (0:ℝ)..t, ε := by
    refine intervalIntegral.integral_mono_on ht.1 ?_ intervalIntegrable_const
      fun s hs => h3 s (hsub hs)
    exact (((P.continuous.comp_continuousOn hξ'c).sub hξ'c).norm.mono hsub).intervalIntegrable_of_Icc ht.1
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
  have := hconv t ht
  nlinarith [h1 t ht]

end Convergence

/-! ### Bridge: the discrete side of `norm_sub_le_of_ellipticProjection` from a solution of (6.3) -/

section Bridge

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]

variable (D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2) in
/-- The discrete skew form of (6.3): for `x = ((σ, u, M, ρ), φ)` and `y = ((τ, v, N, μ), ψ)`,
`aₕ(x, y) = −(u, dψ) + (dφ, v) + (M, S₁,ₕ v) + (ρ, dv) − (S₁,ₕ u, N) − (du, μ)`, so that (6.3a–d)
summed read `(ξ̇ₕ, η) + aₕ(ξₕ, η) − (λₕ, dτ − S₀,ₕψ) = (f, v)`. See [QuennevilleBelair2015], §6.2
(the form `a` before (6.4)). -/
def discreteSkewForm (x y : (P0 × Pt1 × P2 × Pt2) × Pt0) : ℝ :=
  -⟪x.1.2.1, D.dt0 y.2⟫ + ⟪D.dt0 x.2, y.1.2.1⟫ + ⟪x.1.2.2.1, D.S1 y.1.2.1⟫ +
    ⟪x.1.2.2.2, D.dt1 y.1.2.1⟫ - ⟪D.S1 x.1.2.1, y.1.2.2.1⟫ - ⟪D.dt1 x.1.2.1, y.1.2.2.2⟫

/-- `aₕ` is skew: `aₕ(x, x) = 0` (the energy argument of §6.2). -/
lemma discreteSkewForm_self (D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2) (x : (P0 × Pt1 × P2 × Pt2) × Pt0) :
    discreteSkewForm D x x = 0 := by
  simp only [discreteSkewForm]
  rw [real_inner_comm x.1.2.1, real_inner_comm x.1.2.2.1, real_inner_comm x.1.2.2.2]
  ring

/-- **Ch 6 convergence for the discrete scheme (6.3).** `norm_sub_le_of_ellipticProjection` with its
discrete
hypotheses (`hdisc`, `hBh`, `hmem`, `hskew`, regularity of `ξₕ`) discharged by a solution
`s : DiscreteSolution D T f`. The discrete energy space `Vₕ⁰ × Ṽₕ¹ × W²ₕ × W̃²ₕ` embeds in the
continuous
energy space `X` by `ι`, which preserves the (`L²`-sum) inner product (`hι`), and `Ṽₕ⁰` maps to the
algebraic space `Z` by `j`; `Xh = range (ι × j)`. The continuous forms `Ah`, `Bh` restrict to the
discrete ones (`hAh`, `hBh`), and `f(t)` represents `F(t)` on `ι(Ṽₕ¹)` (`hF`). The remaining
hypotheses (the continuous equation tested on `Xh` and the elliptic projection) are those of
`norm_sub_le_of_ellipticProjection`. See [QuennevilleBelair2015], §6.2; cf.
[QuennevilleBelair2015], Thm 4.14. -/
theorem DiscreteSolution.norm_sub_le_of_ellipticProjection {X Z : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X]
    [AddCommGroup Z] [Module ℝ Z] {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X)
    (hι : ∀ a b, ⟪ι a, ι b⟫ = ⟪a.1, b.1⟫ + ⟪a.2.1, b.2.1⟫ + ⟪a.2.2.1, b.2.2.1⟫ + ⟪a.2.2.2, b.2.2.2⟫)
    (j : Pt0 →ₗ[ℝ] Z) (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] P1)
    (hAh : ∀ a φ b ψ, Ah (ι a, j φ) (ι b, j ψ) = discreteSkewForm D (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (ι a, j ψ) = D.d0 a.1 - D.S0 ψ) (P : X →L[ℝ] X) {T : ℝ}
    {f : ℝ → Pt1} (s : DiscreteSolution D T f)
    (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hF : ∀ t ∈ Ico 0 T, ∀ a, ⟪F t, ι a⟫ = ⟪f t, a.2.1⟫)
    (hξc : ContinuousOn ξ (Icc 0 T)) (hξ'c : ContinuousOn ξ' (Icc 0 T))
    (hξd : ∀ t ∈ Ico 0 T, HasDerivWithinAt ξ (ξ' t) (Ici t) t)
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    (Q : ℝ → Z) (lamP : ℝ → P1)
    (hPmem : ∀ t ∈ Icc 0 T, (P (ξ t), Q t) ∈ LinearMap.range ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j))
    (hPB : ∀ t ∈ Icc 0 T, Bh (P (ξ t), Q t) = 0)
    (hproj : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      Ah (P (ξ t), Q t) η - ⟪lamP t, Bh η⟫ = A (ξ t, χ t) η - ℓ t η) :
    ∀ t ∈ Icc 0 T, ‖ξ t - ι (s.σ t, s.u t, s.M t, s.ρ t)‖ ≤
      ‖ξ t - P (ξ t)‖ + ‖P (ξ 0) - ι (s.σ 0, s.u 0, s.M 0, s.ρ 0)‖ +
        ∫ r in (0:ℝ)..t, ‖P (ξ' r) - ξ' r‖ := by
  set Xh := LinearMap.range ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j)
  have hrange : ∀ η ∈ Xh, ∃ b ψ, η = (ι b, j ψ) := by
    rintro η ⟨⟨b, ψ⟩, rfl⟩; exact ⟨b, ψ, rfl⟩
  refine Feec.BGG.norm_sub_le_of_ellipticProjection Xh A Ah Bh P ξ ξ' χ ℓ F hξc hξ'c hξd hcont
    (fun t => ι (s.σ t, s.u t, s.M t, s.ρ t)) (fun t => ι (s.σ' t, s.u' t, s.M' t, s.ρ' t))
    (fun t => j (s.φ t)) s.lam (fun t _ => ⟨((s.σ t, s.u t, s.M t, s.ρ t), s.φ t), rfl⟩)
    (fun t ht => by simp only [hBh]; exact sub_eq_zero.mpr (s.constraint ht))
    (ι.continuous.comp_continuousOn (s.cσ.prodMk (s.cu.prodMk (s.cM.prodMk s.cρ))))
    (fun t ht => ι.hasFDerivAt.comp_hasDerivWithinAt t
      ((s.dσ t ht).prodMk ((s.du t ht).prodMk ((s.dM t ht).prodMk (s.dρ t ht)))))
    (fun t ht η hη => ?_) Q lamP hPmem hPB hproj (fun η hη => ?_)
  · obtain ⟨⟨τ, v, N, μ⟩, ψ, rfl⟩ := hrange η hη
    simp only [hι, hAh, hBh, hF t ht, discreteSkewForm]
    have ha := s.ea t (Ico_subset_Icc_self ht) τ ψ
    have hb := s.eb t ht v
    have hc := s.ec t ht N
    have hd := s.ed t ht μ
    linarith
  · obtain ⟨b, ψ, rfl⟩ := hrange η hη
    rw [hAh]; exact discreteSkewForm_self D _

end Bridge


/-! ## The corrected Prop 6.2: dynamic data and projected initial data -/


section Discrete

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}

/-- (C3) at every time: every solution of (6.3) has `(dφₕ(t) − f(t), dψ) = 0` for
`ψ ∈ ker S₀,ₕ` and `t ∈ [0,T)` (differentiate the hidden constraint and test (6.3b) with
`v = dψ`). Thesis Prop 6.2, corrected: `φₕ` is not free. -/
theorem DiscreteSolution.inner_dt0_phi_eq {T : ℝ} {f : ℝ → Pt1} (s : DiscreteSolution D T f) {t : ℝ}
    (ht : t ∈ Ico 0 T)
    {ψ : Pt0} (hψ : D.S0 ψ = 0) : ⟪D.dt0 (s.φ t), D.dt0 ψ⟫ = ⟪f t, D.dt0 ψ⟫ := by
  have hz : ∀ x ∈ Icc 0 T, ⟪s.u x, D.dt0 ψ⟫ = 0 := fun x hx => s.hidden_constraint hx hψ
  have hd : HasDerivWithinAt (fun x => ⟪s.u x, D.dt0 ψ⟫) ⟪s.u' t, D.dt0 ψ⟫ (Ici t) t := by
    simpa using HasDerivWithinAt.inner ℝ (s.du t ht)
      (hasDerivWithinAt_const t (Ici t) (D.dt0 ψ))
  have hu' := hasDerivWithinAt_Ici_eq_zero ht hz hd
  have hb := s.eb t ht (D.dt0 ψ)
  rw [hu', D.S1_dt0_eq_zero hψ, D.dt1_dt0] at hb
  simpa using hb

/-- **Prop 6.2 repair: `φₕ` is determined.** For every solution of (6.3) and `t ∈ [0,T)`,
`φₕ(t) = Φ(σₕ(t), f(t))` with `Φ = phiMap`, the unique `φ` with `S₀,ₕ φ = dσ` and
`(dφ, dψ) = (f, dψ)` on `ker S₀,ₕ`. Corrects [QuennevilleBelair2015], Prop 6.2
(`φ₀,ₕ` is not free data). -/
theorem DiscreteSolution.phi_eq [FiniteDimensional ℝ P1] [FiniteDimensional ℝ Pt0]
    [FiniteDimensional ℝ Pt1]
    (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)
    {T : ℝ} {f : ℝ → Pt1} (s : DiscreteSolution D T f) {t : ℝ} (ht : t ∈ Ico 0 T) :
    s.φ t = phiMap D hdinj hS (s.σ t, f t) :=
  (phiMap_eq hdinj hS (s.constraint (Ico_subset_Icc_self ht))
    fun _ hψ => DiscreteSolution.inner_dt0_phi_eq s ht hψ).symm

/-- The initial algebraic datum is determined: `φₕ(0) = Φ(σₕ(0), f(0))` (for `T > 0`).
Corrects [QuennevilleBelair2015], Prop 6.2. -/
theorem DiscreteSolution.phi_zero [FiniteDimensional ℝ P1] [FiniteDimensional ℝ Pt0]
    [FiniteDimensional ℝ Pt1] (hdinj : Function.Injective D.dt0)
    (hS : Function.Surjective D.S0) {T : ℝ} (hT : 0 < T) {f : ℝ → Pt1}
    (s : DiscreteSolution D T f) :
    s.φ 0 = phiMap D hdinj hS (s.σ 0, f 0) :=
  DiscreteSolution.phi_eq hdinj hS s ⟨le_rfl, hT⟩

variable [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P1] [FiniteDimensional ℝ P2]
  [FiniteDimensional ℝ Pt0] [FiniteDimensional ℝ Pt1] [FiniteDimensional ℝ Pt2]

/-- **Corrected Prop 6.2, dynamic-data form (existence ⇔ (C2)).** Assume `T > 0`,
finite-dimensional FE spaces, `d : Ṽₕ⁰ → Ṽₕ¹` injective, `S₀,ₕ` surjective (thesis (5.4)) and
`f` continuous on `[0,T]`. For dynamic data `(σ₀, u₀, M₀, ρ₀)` the system (6.3) has a solution iff
`u₀ ⊥ d(ker S₀,ₕ)`. `σ₀`, `M₀`, `ρ₀` are arbitrary.

Thesis claim: data in `Γₕ` and arbitrary `u₀,ₕ` give a solution. Defect: (C2) on `u₀` is
necessary (`not_exists_discreteSolution_of_ker`), and `φ₀,ₕ` is not free
(`DiscreteSolution.phi_zero`).
Repair: once `φₕ(0) := Φ(σ₀, f(0))` (forced), (C1) and (C3) hold automatically
(`S0_phiMap`, `inner_phiMap`) and (C2) is the only condition. Corrects
[QuennevilleBelair2015], Prop 6.2. [QuennevilleBelair2015], Prop 6.2 (corrected) -/
theorem exists_discreteSolution_iff_compatible_u {T : ℝ} (hT : 0 < T)
    (hdinj : Function.Injective D.dt0)
    (hS : Function.Surjective D.S0) {f : ℝ → Pt1} (hf : ContinuousOn f (Icc 0 T))
    (σ₀ : P0) (u₀ : Pt1)
    (M₀ : P2) (ρ₀ : Pt2) :
    (∃ s : DiscreteSolution D T f, s.σ 0 = σ₀ ∧ s.u 0 = u₀ ∧ s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ↔
      ∀ ψ, D.S0 ψ = 0 → ⟪u₀, D.dt0 ψ⟫ = 0 := by
  constructor
  · rintro ⟨s, -, hu, -, -⟩ ψ hψ
    rw [← hu]; exact (DiscreteSolution.compatible hT s).2.1 ψ hψ
  · intro h2
    obtain ⟨s, hσ, -, hu, hM, hρ⟩ := exists_discreteSolution_of_continuousOn (M₀ := M₀) (ρ₀ := ρ₀)
      hdinj hS hT.le hf (S0_phiMap hdinj hS (σ₀, f 0)).symm h2
      (fun ψ hψ => inner_phiMap hdinj hS (σ₀, f 0) hψ)
    exact ⟨s, hσ, hu, hM, hρ⟩

/-- **Corrected Prop 6.2, well-posedness for dynamic data.** Under the hypotheses of
`exists_discreteSolution_iff_compatible_u` and (C2) `u₀ ⊥ d(ker S₀,ₕ)`: there is a solution of (6.3)
with data
`(σ₀, u₀, M₀, ρ₀)`, its algebraic datum is `φₕ(0) = Φ(σ₀, f(0))`, and every solution with the
same dynamic data agrees with it (`σₕ, uₕ, Mₕ, ρₕ, λₕ` on `[0,T]`, `φₕ` on `[0,T)`; the value
`φₕ(T)` is not constrained by (6.3)). This is the thesis' Prop 6.2 with the free datum
`φ₀,ₕ` replaced by the forced one and "arbitrary `u₀,ₕ`" replaced by (C2). Corrects
[QuennevilleBelair2015], Prop 6.2. [QuennevilleBelair2015], Prop 6.2 (corrected) -/
theorem exists_discreteSolution_unique {T : ℝ} (hT : 0 < T) (hdinj : Function.Injective D.dt0)
    (hS : Function.Surjective D.S0) {f : ℝ → Pt1} (hf : ContinuousOn f (Icc 0 T))
    (σ₀ : P0) (u₀ : Pt1)
    (M₀ : P2) (ρ₀ : Pt2) (hC2 : ∀ ψ, D.S0 ψ = 0 → ⟪u₀, D.dt0 ψ⟫ = 0) :
    ∃ s : DiscreteSolution D T f, (s.σ 0 = σ₀ ∧ s.u 0 = u₀ ∧ s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ∧
      s.φ 0 = phiMap D hdinj hS (σ₀, f 0) ∧
      ∀ s' : DiscreteSolution D T f, (s'.σ 0 = σ₀ ∧ s'.u 0 = u₀ ∧ s'.M 0 = M₀ ∧ s'.ρ 0 = ρ₀) →
        (∀ t ∈ Icc 0 T, s'.σ t = s.σ t ∧ s'.u t = s.u t ∧ s'.M t = s.M t ∧ s'.ρ t = s.ρ t ∧
          s'.lam t = s.lam t) ∧ (∀ t ∈ Ico 0 T, s'.φ t = s.φ t) := by
  obtain ⟨s, hσ, hu, hM, hρ⟩ := (exists_discreteSolution_iff_compatible_u hT hdinj hS hf σ₀ u₀ M₀ ρ₀).2 hC2
  refine ⟨s, ⟨hσ, hu, hM, hρ⟩, by rw [DiscreteSolution.phi_zero hdinj hS hT s, hσ], fun s' h' => ?_⟩
  exact DiscreteSolution.unique s' s hdinj hS
    ⟨h'.1.trans hσ.symm, h'.2.1.trans hu.symm, h'.2.2.1.trans hM.symm, h'.2.2.2.trans hρ.symm⟩

end Discrete

/-! ### Projected initial data for the Ch. 6 convergence theorem -/

section Projected

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [AddCommGroup Z] [Module ℝ Z]

/-- **The projected dynamic datum satisfies (C2).** In the setting of
`DiscreteSolution.norm_sub_le_of_ellipticProjection` (continuous equation `hcont` tested on
`Xh = range (ι × j)`,
elliptic projection `hproj`, discrete forms `hAh`, `hBh`) and `T > 0`: if
`(ι a, j q) = (Pξ(0), Q(0))`, then the `u`-component of `a` is orthogonal to `d(ker S₀,ₕ)`.
Proof: test with `η = (ι 0, j ψ)`, `ψ ∈ ker S₀,ₕ`; then `Bh η = −S₀,ₕψ = 0` and
`Ah((ι a, j q), η) = −(a_u, dψ)`, while `hcont` makes the right side of `hproj` vanish.
Supplies the compatibility condition missing from [QuennevilleBelair2015], §6.2 for the
natural initial data. -/
theorem projected_compatible_u {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X) (j : Pt0 →ₗ[ℝ] Z)
    (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] P1)
    (hAh : ∀ a φ b ψ, Ah (ι a, j φ) (ι b, j ψ) = discreteSkewForm D (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (ι a, j ψ) = D.d0 a.1 - D.S0 ψ) (P : X →L[ℝ] X) {T : ℝ} (hT : 0 < T)
    (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    (Q : ℝ → Z) (lamP : ℝ → P1)
    (hproj : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      Ah (P (ξ t), Q t) η - ⟪lamP t, Bh η⟫ = A (ξ t, χ t) η - ℓ t η)
    {a : P0 × Pt1 × P2 × Pt2} {q : Pt0} (ha : (ι a, j q) = (P (ξ 0), Q 0))
    {ψ : Pt0} (hψ : D.S0 ψ = 0) : ⟪a.2.1, D.dt0 ψ⟫ = 0 := by
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hη : ((ι 0, j ψ) : X × Z) ∈ LinearMap.range
      ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j) := ⟨(0, ψ), rfl⟩
  have h1 := hcont 0 h0 _ hη
  have h2 := hproj 0 h0 _ hη
  rw [← ha, hAh, hBh, hψ] at h2
  simp only [map_zero, inner_zero_right, zero_add] at h1
  simp [discreteSkewForm] at h2
  linarith

/-- **When is the projected algebraic datum admissible?** In the setting of
`projected_compatible_u`,
with `f(t)` representing `F(t)` on `ι(Ṽₕ¹)` (`hF`): if `(ι a, j q) = (Pξ(0), Q(0))`, then `q`
satisfies (C3) `(dq, dψ) = (f(0), dψ)` on `ker S₀,ₕ` iff `(ξ̇(0), ι(0, dψ, 0, 0)) = 0` for all
`ψ ∈ ker S₀,ₕ`. Proof: test with `η = (ι(0, dψ, 0, 0), 0)`, using `S₁,ₕ dψ = 0`, `d dψ = 0`.
So `φₕ(0) = Q(0)` is admissible only under a consistency condition on the exact solution
(a component of `(I − P)u̇(0)` in general); the admissible choice is `Φ(σₕ(0), f(0))`
(`exists_discreteSolution_norm_sub_le`). The condition can fail: `not_projected_compatible_phi`.
Repair of [QuennevilleBelair2015], §6.2 (initial data for (6.3)). -/
theorem projected_compatible_phi_iff {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X) (j : Pt0 →ₗ[ℝ] Z)
    (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] P1)
    (hAh : ∀ a φ b ψ, Ah (ι a, j φ) (ι b, j ψ) = discreteSkewForm D (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (ι a, j ψ) = D.d0 a.1 - D.S0 ψ) (P : X →L[ℝ] X) {T : ℝ} (hT : 0 < T)
    {f : ℝ → Pt1} (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hF : ∀ t ∈ Ico 0 T, ∀ a, ⟪F t, ι a⟫ = ⟪f t, a.2.1⟫)
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    (Q : ℝ → Z) (lamP : ℝ → P1)
    (hproj : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      Ah (P (ξ t), Q t) η - ⟪lamP t, Bh η⟫ = A (ξ t, χ t) η - ℓ t η)
    {a : P0 × Pt1 × P2 × Pt2} {q : Pt0} (ha : (ι a, j q) = (P (ξ 0), Q 0)) :
    (∀ ψ, D.S0 ψ = 0 → ⟪D.dt0 q, D.dt0 ψ⟫ = ⟪f 0, D.dt0 ψ⟫) ↔
      ∀ ψ, D.S0 ψ = 0 → ⟪ξ' 0, ι (0, D.dt0 ψ, 0, 0)⟫ = 0 := by
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have key : ∀ ψ, D.S0 ψ = 0 →
      ⟪D.dt0 q, D.dt0 ψ⟫ = ⟪f 0, D.dt0 ψ⟫ - ⟪ξ' 0, ι (0, D.dt0 ψ, 0, 0)⟫ := by
    intro ψ hψ
    have hη : ((ι (0, D.dt0 ψ, 0, 0), j 0) : X × Z) ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j) := ⟨((0, D.dt0 ψ, 0, 0), 0), rfl⟩
    have h1 := hcont 0 h0 _ hη
    have h2 := hproj 0 h0 _ hη
    rw [← ha, hAh, hBh] at h2
    rw [hF 0 h0] at h1
    simp [discreteSkewForm, D.S1_dt0_eq_zero hψ, D.dt1_dt0] at h2
    simp only [map_zero] at h1
    linarith
  constructor
  · intro h ψ hψ; have := key ψ hψ; rw [h ψ hψ] at this; linarith
  · intro h ψ hψ; rw [key ψ hψ, h ψ hψ, sub_zero]

/-- **Ch. 6 convergence from projected initial data (no solution assumed).** Hypotheses of
`DiscreteSolution.norm_sub_le_of_ellipticProjection` without the discrete solution `s`, plus
`T > 0`, `f`
continuous on `[0,T]`, finite-dimensional FE spaces, `d` injective on `Ṽₕ⁰` and `S₀,ₕ`
surjective. Then
there is a solution `s` of (6.3) whose dynamic initial datum is the projection `Pξ(0)` and whose
algebraic datum is the forced `φₕ(0) = Φ(σₕ(0), f(0))`, and for `t ∈ [0,T]`
`‖ξ(t) − ξₕ(t)‖ ≤ ‖ξ(t) − Pξ(t)‖ + ∫₀ᵗ ‖Pξ̇ − ξ̇‖`.

The thesis (§6.2–6.3) states no convergence theorem and does not address whether natural
initial data are admissible for (6.3); this closes that gap for the projected data
(`projected_compatible_u`), avoiding `φₕ(0) = Q(0)`, which is admissible only under a consistency
condition (`projected_compatible_phi_iff`) that can fail (`not_projected_compatible_phi`).
See [QuennevilleBelair2015], §6.2, Prop 6.2, (6.4); cf. [QuennevilleBelair2015], Thm 4.14. -/
theorem exists_discreteSolution_norm_sub_le [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P1]
    [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt0] [FiniteDimensional ℝ Pt1]
    [FiniteDimensional ℝ Pt2] {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}
    (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)
    (ι : (P0 × Pt1 × P2 × Pt2) →L[ℝ] X)
    (hι : ∀ a b, ⟪ι a, ι b⟫ = ⟪a.1, b.1⟫ + ⟪a.2.1, b.2.1⟫ + ⟪a.2.2.1, b.2.2.1⟫ +
      ⟪a.2.2.2, b.2.2.2⟫)
    (j : Pt0 →ₗ[ℝ] Z) (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] P1)
    (hAh : ∀ a φ b ψ, Ah (ι a, j φ) (ι b, j ψ) = discreteSkewForm D (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (ι a, j ψ) = D.d0 a.1 - D.S0 ψ) (P : X →L[ℝ] X) {T : ℝ} (hT : 0 < T)
    {f : ℝ → Pt1} (hf : ContinuousOn f (Icc 0 T))
    (ξ ξ' : ℝ → X) (χ : ℝ → Z) (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ) (F : ℝ → X)
    (hF : ∀ t ∈ Ico 0 T, ∀ a, ⟪F t, ι a⟫ = ⟪f t, a.2.1⟫)
    (hξc : ContinuousOn ξ (Icc 0 T)) (hξ'c : ContinuousOn ξ' (Icc 0 T))
    (hξd : ∀ t ∈ Ico 0 T, HasDerivWithinAt ξ (ξ' t) (Ici t) t)
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      ⟪ξ' t, η.1⟫ + A (ξ t, χ t) η - ℓ t η = ⟪F t, η.1⟫)
    (Q : ℝ → Z) (lamP : ℝ → P1)
    (hPmem : ∀ t ∈ Icc 0 T, (P (ξ t), Q t) ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j))
    (hPB : ∀ t ∈ Icc 0 T, Bh (P (ξ t), Q t) = 0)
    (hproj : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((ι : (P0 × Pt1 × P2 × Pt2) →ₗ[ℝ] X).prodMap j),
      Ah (P (ξ t), Q t) η - ⟪lamP t, Bh η⟫ = A (ξ t, χ t) η - ℓ t η) :
    ∃ s : DiscreteSolution D T f, ι (s.σ 0, s.u 0, s.M 0, s.ρ 0) = P (ξ 0) ∧
      s.φ 0 = phiMap D hdinj hS (s.σ 0, f 0) ∧
      ∀ t ∈ Icc 0 T, ‖ξ t - ι (s.σ t, s.u t, s.M t, s.ρ t)‖ ≤
        ‖ξ t - P (ξ t)‖ + ∫ r in (0:ℝ)..t, ‖P (ξ' r) - ξ' r‖ := by
  obtain ⟨⟨a, q⟩, hy⟩ := hPmem 0 ⟨le_rfl, hT.le⟩
  have ha : (ι a, j q) = (P (ξ 0), Q 0) := hy
  have hC2 : ∀ ψ, D.S0 ψ = 0 → ⟪a.2.1, D.dt0 ψ⟫ = 0 := fun ψ hψ =>
    projected_compatible_u ι j A Ah Bh hAh hBh P hT ξ ξ' χ ℓ F hcont Q lamP hproj ha hψ
  obtain ⟨s, hσ, hu, hM, hρ⟩ :=
    (exists_discreteSolution_iff_compatible_u hT hdinj hS hf a.1 a.2.1 a.2.2.1 a.2.2.2).2 hC2
  have hinit : ι (s.σ 0, s.u 0, s.M 0, s.ρ 0) = P (ξ 0) := by
    rw [hσ, hu, hM, hρ]; exact congrArg Prod.fst ha
  refine ⟨s, hinit, DiscreteSolution.phi_zero hdinj hS hT s, fun t ht => ?_⟩
  have := DiscreteSolution.norm_sub_le_of_ellipticProjection ι hι j A Ah Bh hAh hBh P s ξ ξ' χ ℓ F hF hξc hξ'c hξd hcont
    Q lamP hPmem hPB hproj t ht
  rwa [hinit, sub_self, norm_zero, add_zero] at this

end Projected

end Feec.BGG
