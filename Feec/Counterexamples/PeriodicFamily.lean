module

public import Feec.Counterexamples.ClassicalRegularity
public import Feec.HilbertComplex.Approximation.StaticFEEC

/-!
# A conforming family of the periodic complex

The periodic complex `ℓ² --A--> ℓ² --0--> ℓ² --A--> ⋯` on `ComplexShape.up ℕ`,
`A = diag(1/(n+1))` (`Feec.Counterexamples.Fredholm.periodic`), has `ℌᵏ = 0` but no closed range.
It has a conforming family (`periodicFamily`): the truncations `span{e₀, …, e_{N-1}}` in every
degree, with the orthogonal projections onto them, which commute with `A` (`diag_truncSum`). So
the crown applies to it, and its static verdict fails in even degrees
(`periodic_not_staticVerdict`, `periodicFamily_not_staticVerdict`): without closed range the
uniform discrete Poincaré inequality fails, although the harmonic forms are finite-dimensional.

## Main definitions

* `periodicTrunc`, `periodicFamily`.

## Main results

* **`periodic_not_staticVerdict`**, **`periodicFamily_not_staticVerdict`**;
  `diag_truncSum`, `periodic_d_eq` (the truncations are the orthogonal projections,
  `Feec.Counterexamples.ClassicalRegularity.starProjection_trunc`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.Counterexamples

namespace Fredholm

open Ell2 (L2)
open ClassicalRegularity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `A = diag(1/(n+1))` commutes with the truncations. -/
theorem diag_truncSum (N : ℕ) (x : L2 𝕜) : diag 𝕜 (truncSum 𝕜 N x) = truncSum 𝕜 N (diag 𝕜 x) :=
  lp.ext <| funext fun m => by
    simp only [diag_apply, truncSum_apply]
    split_ifs <;> simp

/-- Every differential of the periodic complex is an everywhere-defined `g ∈ {A, 0}`, and `g`
commutes with the truncations. -/
theorem periodic_d_eq (i j : ℕ) : ∃ g : L2 𝕜 →ₗ[𝕜] L2 𝕜, (periodic 𝕜).d i j = g.toPMap ⊤ ∧
    ∀ N x, g ((trunc 𝕜 N).starProjection x) = (trunc 𝕜 N).starProjection (g x) := by
  have h0 : (0 : L2 𝕜 →ₗ.[𝕜] L2 𝕜) = (0 : L2 𝕜 →ₗ[𝕜] L2 𝕜).toPMap ⊤ := rfl
  by_cases h : i + 1 = j
  · subst h
    rw [periodic_d_succ]
    rcases Nat.even_or_odd i with hi | hi
    · exact ⟨diag 𝕜, periodicD_of_even hi, fun N x => by
        simp only [ContinuousLinearMap.coe_coe, starProjection_trunc, diag_truncSum]⟩
    · exact ⟨0, (periodicD_of_odd hi).trans h0, fun N x => by simp⟩
  · exact ⟨0, ((periodic 𝕜).shape i j h).trans h0, fun N x => by simp⟩

variable (𝕜) in
/-- The truncation subcomplexes `span{e₀, …, e_{N-1}}` in every degree of the periodic complex. -/
def periodicTrunc (N : ℕ) : (periodic 𝕜).Subcomplex where
  V _ := trunc 𝕜 N
  le_domain i j x _ := by
    obtain ⟨g, hg, -⟩ := periodic_d_eq (𝕜 := 𝕜) i j
    rw [hg]; trivial
  mapsTo i j x hx := by
    obtain ⟨g, hg, hc⟩ := periodic_d_eq (𝕜 := 𝕜) i j
    rw [LinearPMap.apply_of_eq_toPMap hg, ← (trunc 𝕜 N).starProjection_eq_self_iff.2 hx, hc]
    exact (trunc 𝕜 N).starProjection_apply_mem _

variable (𝕜) in
/-- **A conforming family of the periodic complex** `ℓ² --A--> ℓ² --0--> ℓ² --A--> ⋯`: the
truncations `span{e₀, …, e_{N-1}}`, `N → ∞`, with the orthogonal projections onto them, of norm
`1`, which commute with `A`. So the crown applies to it, although the complex has no closed
range. -/
def periodicFamily : HilbertComplex.ConformingFamily (periodic 𝕜) ℕ where
  l := atTop
  V := periodicTrunc 𝕜
  finiteDimensional N _ := inferInstanceAs (FiniteDimensional 𝕜 (trunc 𝕜 N))
  π N :=
    { π := fun _ => (trunc 𝕜 N).starProjection
      mem := fun _ x => (trunc 𝕜 N).starProjection_apply_mem x
      proj := fun _ x hx => (trunc 𝕜 N).starProjection_eq_self_iff.2 hx
      comm := fun i j x => by
        obtain ⟨g, hg, hc⟩ := periodic_d_eq (𝕜 := 𝕜) i j
        rw [LinearPMap.apply_of_eq_toPMap hg, LinearPMap.apply_of_eq_toPMap hg]
        exact hc N x }
  bound_π := ⟨1, fun N _ x => by
    simpa using (trunc 𝕜 N).norm_starProjection_apply_le x⟩
  approx _ w := by
    refine squeeze_zero (fun _ => infDist_nonneg)
      (fun N => infDist_le_dist_of_mem ((trunc 𝕜 N).starProjection_apply_mem w)) ?_
    simpa [starProjection_trunc, dist_comm] using
      (tendsto_iff_dist_tendsto_zero.1 (tendsto_truncSum (𝕜 := 𝕜) w))

/-- The truncation family is refined along `N → ∞`. -/
instance : (periodicFamily 𝕜).l.NeBot := inferInstanceAs (atTop : Filter ℕ).NeBot

/-- **Without closed range the static verdict fails, although `ℌ = 0`**: no conforming family of
the periodic complex (along a nontrivial filter) has the static verdict at an even degree, since
its uniform discrete Poincaré inequality would close `𝔅ᵏ⁺¹ = R(A)`
(`ConformingFamily.StaticVerdict.closedRangeAt`). [QuennevilleBelair2015], §4.2; [AFW2010], §3.3 -/
theorem periodic_not_staticVerdict {κ : Type*}
    (F : HilbertComplex.ConformingFamily (periodic 𝕜) κ) [F.l.NeBot] {k : ℕ} (hk : Even k) :
    ¬ F.StaticVerdict k := fun hV =>
  periodic_not_closedRangeAt hk (hV.closedRangeAt rfl)

/-- The periodic complex has `ℌ = 0` and a conforming family without the static verdict at `0`. -/
theorem periodicFamily_not_staticVerdict :
    (∀ k, (periodic 𝕜).harmonic k = ⊥) ∧ ¬ (periodicFamily 𝕜).StaticVerdict 0 :=
  ⟨periodic_harmonic_eq_bot, periodic_not_staticVerdict _ ⟨0, rfl⟩⟩

end Fredholm

end Feec.Counterexamples
