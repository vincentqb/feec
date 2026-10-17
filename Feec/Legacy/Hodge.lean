module

public import Feec.Legacy.ShortComplex
public import Feec.HilbertComplex.DomainComplex
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Bounded-model Hodge theory (Thesis §4.2: Thm 4.1, Thm 4.2)

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use.
Most of the original module was re-derived in the general layers (see
`docs/migration/map.tsv`); what remains is listed below.

## Contents

* `DomainComplex.dPerp`: `d^k` restricted to `(𝔷^k)ᗮ` (in `V`): injective with the same range as `d^k`.
* `GraphCx.G`: Graph of `D k` in `E k ×₂ E (k+1)` (the domain space `V k` with its graph norm).
* `FredholmCE.L2`: `ℓ²(ℕ, ℝ)`.
* `FredholmCE.norm_div_succ_le`: `|a/(n+1)| ≤ |a|`.
* `FredholmCE.diagₗ`: `diag(1/(n+1))` on `ℓ²`, as a linear map.
* `FredholmCE.A`: `A = diag(1/(n+1)) : ℓ² → ℓ²`: bounded, injective, dense non-closed range.
* `FredholmCE.A_apply`: `(A x)_n = x_n / (n+1)`.
* `FredholmCE.A_injective`: `A` is injective.
* `FredholmCE.A_single`: `A e_n = e_n / (n+1)`.
* `FredholmCE.eq_zero_of_inner_A_single`: `range A` is dense: anything orthogonal to every `A e_n` vanishes.

## References

* [QuennevilleBelair2015], §4.2 (Hilbert complexes, Thm 4.1, Thm 4.2, the compactness and
  Fredholm remarks); the thesis follows [BruningLesch1992] and [AFW2010] there.
* [BruningLesch1992] (Hilbert complexes; domain complex; Fredholm = finite-dimensional
  cohomology, Fredholm ⇒ closed range).
* [AFW2010], §3 (abstract Hilbert complexes: domain complex, closed and Fredholm complexes,
  Hodge decomposition, Poincaré inequality, compactness property).
* [Arnold2018] (book treatment of Hilbert complexes in finite element exterior calculus).
-/

open scoped RealInnerProductSpace Topology
open Set Filter

@[expose] public noncomputable section

namespace Feec.Legacy
namespace DomainComplex

variable {V W : ℕ → Type*}
    [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)] [∀ k, CompleteSpace (V k)]
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    (C : DomainComplex V W)

/-! ### Thm 4.2: Poincaré inequality ⇔ closed range -/

/-- `d^k` restricted to `(𝔷^k)ᗮ` (in `V`): injective with the same range as `d^k`. -/
def dPerp (k : ℕ) : (C.Z k)ᗮ →L[ℝ] V (k + 1) := (C.d k).comp (C.Z k)ᗮ.subtypeL

end DomainComplex

/-! ### Graph complexes of bounded operators

A complex of *bounded* operators `D k : E k → E (k+1)` on Hilbert spaces gives a bounded domain
complex with `V k` = graph of `D k` in `E k ×₂ E (k+1)`. Used for the counterexamples below. -/

namespace GraphCx

variable {E : ℕ → Type*}
    [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℝ (E k)] [∀ k, CompleteSpace (E k)]
    (D : ∀ k, E k →L[ℝ] E (k + 1))

/-- Graph of `D k` in `E k ×₂ E (k+1)` (the domain space `V k` with its graph norm). -/
def G (k : ℕ) : Submodule ℝ (WithLp 2 (E k × E (k + 1))) :=
  (WithLp.sndL 2 ℝ (E k) (E (k + 1)) - (D k).comp (WithLp.fstL 2 ℝ (E k) (E (k + 1)))).ker

variable {D}

end GraphCx

/-! ### Counterexample to "a Fredholm Hilbert complex is always closed" -/

namespace FredholmCE

/-- `ℓ²(ℕ, ℝ)`. -/
abbrev L2 := lp (fun _ : ℕ => ℝ) 2

/-- `|a/(n+1)| ≤ |a|`. -/
theorem norm_div_succ_le (a : ℝ) (n : ℕ) : ‖a / ((n : ℝ) + 1)‖ ≤ ‖a‖ := by
  rw [norm_div]
  exact div_le_self (norm_nonneg _) (by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; simp)

/-- `diag(1/(n+1))` on `ℓ²`, as a linear map. -/
def diagₗ : L2 →ₗ[ℝ] L2 where
  toFun x := ⟨fun n => x n / ((n : ℝ) + 1), (lp.memℓp x).mono' fun n => norm_div_succ_le _ n⟩
  map_add' x y := lp.ext <| funext fun n => by simp only [lp.coeFn_add, Pi.add_apply, add_div]
  map_smul' c x := lp.ext <| funext fun n => by simp [mul_div_assoc]

/-- `A = diag(1/(n+1)) : ℓ² → ℓ²`: bounded, injective, dense non-closed range. -/
def A : L2 →L[ℝ] L2 :=
  diagₗ.mkContinuous 1 fun x => by
    rw [one_mul]; exact lp.norm_mono two_ne_zero fun n => norm_div_succ_le _ n

/-- `(A x)_n = x_n / (n+1)`. -/
theorem A_apply (x : L2) (n : ℕ) : A x n = x n / ((n : ℝ) + 1) := rfl

/-- `A` is injective. -/
theorem A_injective : Function.Injective A := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine lp.ext <| funext fun n => ?_
  have := congrArg (fun y : L2 => y n) hx
  simp only [A_apply] at this
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simpa [div_eq_zero_iff, hn] using this

/-- `A e_n = e_n / (n+1)`. -/
theorem A_single (n : ℕ) : A (lp.single 2 n 1) = lp.single 2 n (1 / ((n : ℝ) + 1)) := by
  refine lp.ext <| funext fun m => ?_
  rw [A_apply]
  by_cases h : m = n
  · subst h; simp
  · simp [lp.single_apply, Pi.single_eq_of_ne h]

/-- `range A` is dense: anything orthogonal to every `A e_n` vanishes. -/
theorem eq_zero_of_inner_A_single {y : L2} (hy : ∀ n, ⟪A (lp.single 2 n 1), y⟫ = 0) : y = 0 := by
  refine lp.ext (funext fun n => ?_)
  have := hy n
  rw [A_single, lp.inner_single_left] at this
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simpa [hn] using this

end FredholmCE

end Feec.Legacy
