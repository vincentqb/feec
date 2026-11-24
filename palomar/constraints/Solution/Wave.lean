module

public import Solution.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Hodge wave operators of the challenge: linearity, skewness, uniqueness

Strong solutions of a relation `R ⊆ X × X` closed under differences and skew for an injective
bounded `ι` from `X` to a real inner product space (`⟪ι V, ι U⟫ = 0` for `(U, V) ∈ R`) are
determined by their initial value: the energy `‖ι (U - U')‖²` of the difference of two of them is
conserved (`isStrongSolution_unique_of_skew`). For any data `D`, the relation `D.IsWave` is linear
(`IsWave.sub`, `IsWave.zero`) and skew, `⟪L U, U⟫ = 0` in the `ℓ²` sum of its four slots
(`IsWave.inner_eq_zero`: the terms of the four equations cancel in pairs), so its strong
solutions are determined by their initial value (`isStrongSolution_unique`); so are those of the
Hodge wave operator `IsHodgeWave d⁰ d¹` of any two operators
(`IsHodgeWave.isStrongSolution_unique`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 ((4.14)), §6.1 ((6.1))

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace FEEC

/-- **Strong solutions of a skew linear relation are determined by their initial value**: for a
relation `R ⊆ X × X` closed under differences and skew for an injective bounded `ι` from `X` to a
real inner product space, `⟪ι V, ι U⟫ = 0` for `(U, V) ∈ R`, the energy `‖ι (U - U')‖²` of the
difference of two strong solutions on `[0, T]` is constant, and it vanishes at `0`. -/
theorem isStrongSolution_unique_of_skew {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] {R : SetRel X X} (ι : X →L[ℝ] Y)
    (hι : Function.Injective ι) (hsub : ∀ p ∈ R, ∀ q ∈ R, (p.1 - q.1, p.2 - q.2) ∈ R)
    (hskew : ∀ p ∈ R, ⟪ι p.2, ι p.1⟫_ℝ = 0) {T : ℝ} {U U' : ℝ → X}
    (hU : IsStrongSolution R (Icc 0 T) U) (hU' : IsStrongSolution R (Icc 0 T) U')
    (h0 : U 0 = U' 0) : EqOn U U' (Icc 0 T) := by
  have hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun r => ‖ι (U r - U' r)‖ ^ 2) 0 (Icc 0 T) t := by
    intro t ht
    obtain ⟨V, hV, hdV⟩ := hU.2 t ht
    obtain ⟨V', hV', hdV'⟩ := hU'.2 t ht
    have hz : ⟪ι (V - V'), ι (U t - U' t)⟫_ℝ = 0 := hskew (U t - U' t, V - V') (hsub _ hV _ hV')
    refine (ι.hasFDerivAt.comp_hasDerivWithinAt t (hdV.sub hdV')).norm_sq.congr_deriv ?_
    change 2 * ⟪ι (U t - U' t), ι (V - V')⟫_ℝ = 0
    rw [real_inner_comm, hz, mul_zero]
  have hc : ContinuousOn (fun r => ‖ι (U r - U' r)‖ ^ 2) (Icc 0 T) := fun t ht =>
    (hd t ht).continuousWithinAt
  intro t ht
  have hconst := constant_of_has_deriv_right_zero hc (fun x hx =>
    (hd x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)) t ht
  rw [h0, sub_self, map_zero, norm_zero, zero_pow two_ne_zero, sq_eq_zero_iff, norm_eq_zero]
    at hconst
  exact sub_eq_zero.1 (hι (hconst.trans (map_zero ι).symm))

end FEEC

namespace FEEC.WeakSymmetryData

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] {D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2}

theorem IsWave.zero : D.IsWave 0 0 :=
  ⟨0, 0, 0, rfl, rfl, by rw [LinearPMap.map_zero, Submodule.coe_zero, map_zero],
    fun _ _ _ => by simp, fun v => by simp,
    by simp, by simp⟩

theorem IsWave.sub {U V U' V' : W0 × Wt1 × W2 × Wt2} (h : D.IsWave U V) (h' : D.IsWave U' V') :
    D.IsWave (U - U') (V - V') := by
  obtain ⟨σ, φ, u, hσ, hu, hc, h1, h2, h3, h4⟩ := h
  obtain ⟨σ', φ', u', hσ', hu', hc', h1', h2', h3', h4'⟩ := h'
  refine ⟨σ - σ', φ - φ', u - u', by simp [hσ, hσ'], by simp [hu, hu'],
    by rw [LinearPMap.map_sub, Submodule.coe_sub, map_sub, hc, hc'], fun τ ψ hτ => ?_, fun v => ?_,
    ?_, ?_⟩
  · change ⟪V.1 - V'.1, (τ : W0)⟫ = ⟪(u : Wt1) - u', D.dt0 ψ⟫
    rw [inner_sub_left, inner_sub_left, h1 τ ψ hτ, h1' τ ψ hτ]
  · change ⟪V.2.1 - V'.2.1, (v : Wt1)⟫ = -⟪D.dt0 (φ - φ'), (v : Wt1)⟫ -
      ⟪U.2.2.1 - U'.2.2.1, D.S1 v⟫ - ⟪U.2.2.2 - U'.2.2.2, D.dt1 v⟫
    rw [inner_sub_left, h2 v, h2' v, LinearPMap.map_sub, inner_sub_left, inner_sub_left,
      inner_sub_left]
    ring
  · change V.2.2.1 - V'.2.2.1 = D.S1 ((u : Wt1) - u')
    rw [h3, h3', map_sub]
  · change V.2.2.2 - V'.2.2.2 = D.dt1 (u - u')
    rw [h4, h4', LinearPMap.map_sub]

/-- **The wave operator is skew**: `⟪L U, U⟫ = 0`. -/
theorem IsWave.inner_eq_zero {U V : W0 × Wt1 × W2 × Wt2} (h : D.IsWave U V) :
    ⟪V.1, U.1⟫ + ⟪V.2.1, U.2.1⟫ + ⟪V.2.2.1, U.2.2.1⟫ + ⟪V.2.2.2, U.2.2.2⟫ = 0 := by
  obtain ⟨σ, φ, u, hσ, hu, hc, h1, h2, h3, h4⟩ := h
  rw [← hσ, ← hu, h1 σ φ hc, h2 u, h3, h4, real_inner_comm (D.S1 u), real_inner_comm (D.dt1 u),
    real_inner_comm (D.dt0 φ)]
  ring

/-- The `ℓ²` sum `W⁰ ⊕ W̃¹ ⊕ W² ⊕ W̃²` of the four slots. -/
def l2 : (W0 × Wt1 × W2 × Wt2) ≃L[ℝ] WithLp 2 (W0 × WithLp 2 (Wt1 × WithLp 2 (W2 × Wt2))) :=
  ((ContinuousLinearEquiv.refl ℝ W0).prodCongr (((ContinuousLinearEquiv.refl ℝ Wt1).prodCongr
    (WithLp.prodContinuousLinearEquiv 2 ℝ W2 Wt2).symm).trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ Wt1 _).symm)).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ W0 _).symm

/-- **Strong solutions are determined by their initial value**: the energy of the difference is
conserved (`IsWave.inner_eq_zero`). -/
theorem isStrongSolution_unique {T : ℝ} {U U' : ℝ → W0 × Wt1 × W2 × Wt2}
    (hU : IsStrongSolution {p | D.IsWave p.1 p.2} (Icc 0 T) U)
    (hU' : IsStrongSolution {p | D.IsWave p.1 p.2} (Icc 0 T) U') (h0 : U 0 = U' 0) :
    EqOn U U' (Icc 0 T) :=
  isStrongSolution_unique_of_skew l2.toContinuousLinearMap l2.injective
    (fun _ hp _ hq => IsWave.sub hp hq) (fun p hp => by
      change ⟪p.2.1, p.1.1⟫ + (⟪p.2.2.1, p.1.2.1⟫ +
        (⟪p.2.2.2.1, p.1.2.2.1⟫ + ⟪p.2.2.2.2, p.1.2.2.2⟫)) = 0
      rw [← add_assoc, ← add_assoc]
      exact IsWave.inner_eq_zero hp) hU hU' h0

end FEEC.WeakSymmetryData

namespace FEEC.IsHodgeWave

variable {W0 W1 W2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] {d0 : W0 →ₗ.[ℝ] W1} {d1 : W1 →ₗ.[ℝ] W2}

theorem sub {U V U' V' : W0 × W1 × W2} (h : IsHodgeWave d0 d1 U V)
    (h' : IsHodgeWave d0 d1 U' V') : IsHodgeWave d0 d1 (U - U') (V - V') := by
  obtain ⟨σ, u, hσ, hu, h1, h2, h3⟩ := h
  obtain ⟨σ', u', hσ', hu', h1', h2', h3'⟩ := h'
  refine ⟨σ - σ', u - u', by simp [hσ, hσ'], by simp [hu, hu'], fun τ => ?_, fun v => ?_, ?_⟩
  · change ⟪V.1 - V'.1, (τ : W0)⟫ = ⟪(u : W1) - u', d0 τ⟫
    rw [inner_sub_left, inner_sub_left, h1 τ, h1' τ]
  · change ⟪V.2.1 - V'.2.1, (v : W1)⟫ = -⟪d0 (σ - σ'), (v : W1)⟫ - ⟪U.2.2 - U'.2.2, d1 v⟫
    rw [inner_sub_left, h2 v, h2' v, LinearPMap.map_sub, inner_sub_left, inner_sub_left]
    ring
  · change V.2.2 - V'.2.2 = d1 (u - u')
    rw [h3, h3', LinearPMap.map_sub]

/-- **The Hodge wave operator is skew**: `⟪L U, U⟫ = 0`. -/
theorem inner_eq_zero {U V : W0 × W1 × W2} (h : IsHodgeWave d0 d1 U V) :
    ⟪V.1, U.1⟫ + ⟪V.2.1, U.2.1⟫ + ⟪V.2.2, U.2.2⟫ = 0 := by
  obtain ⟨σ, u, hσ, hu, h1, h2, h3⟩ := h
  rw [← hσ, ← hu, h1 σ, h2 u, h3, real_inner_comm (d1 u), real_inner_comm (d0 σ)]
  ring

/-- The `ℓ²` sum `W⁰ ⊕ W¹ ⊕ W²` of the three slots. -/
def l2 : (W0 × W1 × W2) ≃L[ℝ] WithLp 2 (W0 × WithLp 2 (W1 × W2)) :=
  ((ContinuousLinearEquiv.refl ℝ W0).prodCongr
    (WithLp.prodContinuousLinearEquiv 2 ℝ W1 W2).symm).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ W0 _).symm

/-- **Strong solutions of the Hodge wave equation are determined by their initial value**: the
energy of the difference is conserved (`IsHodgeWave.inner_eq_zero`). -/
theorem isStrongSolution_unique {T : ℝ} {U U' : ℝ → W0 × W1 × W2}
    (hU : IsStrongSolution {p | IsHodgeWave d0 d1 p.1 p.2} (Icc 0 T) U)
    (hU' : IsStrongSolution {p | IsHodgeWave d0 d1 p.1 p.2} (Icc 0 T) U') (h0 : U 0 = U' 0) :
    EqOn U U' (Icc 0 T) :=
  isStrongSolution_unique_of_skew l2.toContinuousLinearMap l2.injective
    (fun _ hp _ hq => sub hp hq) (fun p hp => by
      change ⟪p.2.1, p.1.1⟫ + (⟪p.2.2.1, p.1.2.1⟫ + ⟪p.2.2.2, p.1.2.2⟫) = 0
      rw [← add_assoc]
      exact inner_eq_zero hp) hU hU' h0

end FEEC.IsHodgeWave
