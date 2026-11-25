module

public import Solution.OfFeec
public import Solution.Bridge
public import Feec.Counterexamples.PeriodicFamily

/-!
# The sequence-space witness: closed ranges are necessary

The challenge's complex `⋯ --0--> ℓ² --A--> ℓ² --0--> ℓ² --A--> ⋯`, `A = diag(1/(n+1))`, is
`Feec`'s periodic complex `Feec.Counterexamples.Fredholm.periodic` (graded by `ℤ`), and the
challenge's family `Sharpness.family` is that of its coordinate truncations
`span{e₀, …, e_{N-1}}` (`Feec.Counterexamples.Fredholm.periodicTrunc`) with the orthogonal
projections onto them (those of `Feec.Counterexamples.Fredholm.periodicFamily`). This file reads
the clauses of the witness off `Feec`: the graph of `d` (`Feec.Counterexamples.Fredholm.periodicD`),
the harmonic forms (`Feec.Counterexamples.Fredholm.periodic_harmonic_eq_bot`), the closed ranges
(`Feec.Counterexamples.Fredholm.periodic_closedRangeAt_iff`), the truncations
(`Feec.Counterexamples.ClassicalRegularity.starProjection_trunc`), their graph-norm bound and
approximation (`Feec.Counterexamples.ClassicalRegularity.tendsto_truncSum`), and the mixed problem
of an odd degree with the datum `(1/(n+1))ₙ`, which has no solution
(`Feec.Counterexamples.Fredholm.harm_not_mem_range`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace lp
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC.Sharpness

open Feec.Counterexamples Fredholm ClassicalRegularity
open Feec.Counterexamples.Ell2 (L2)

variable {𝕜 : Type*} [RCLike 𝕜]

variable (𝕜) in
/-- **The periodic complex** `⋯ --0--> ℓ² --A--> ℓ² --0--> ℓ² --A--> ⋯`, `A = diag(1/(n+1))`
from the even degrees, as a Hilbert complex of the challenge. -/
abbrev complex : HilbertComplex 𝕜 fun _ : ℤ => ℓ²(ℕ, 𝕜) := HilbertComplex.ofFeec (periodic 𝕜)

variable (𝕜) in
/-- **The truncation family**: `span{e₀, …, e_{N-1}}` in every degree, `N → ∞`, with the
orthogonal projections onto them. -/
def family : (complex 𝕜).SubcomplexFamily ℕ where
  l := atTop
  V N := HilbertComplex.Subcomplex.ofFeec (periodicTrunc 𝕜 N)
  finiteDimensional N _ := inferInstanceAs (FiniteDimensional 𝕜 (trunc 𝕜 N))
  π N := HilbertComplex.CochainProjection.ofFeec ((periodicFamily 𝕜).π N)

instance : (family 𝕜).l.NeBot := inferInstanceAs (atTop : Filter ℕ).NeBot

/-- **The graph of `d`**: `dᵏ = A` for even `k`, `dᵏ = 0` for odd `k`. -/
theorem mem_graph_iff (k : ℤ) (u w : ℓ²(ℕ, 𝕜)) :
    (u, w) ∈ ((complex 𝕜).d k (k + 1)).graph ↔
      ∀ n, w n = if Even k then u n / ((n : 𝕜) + 1) else 0 := by
  change (u, w) ∈ ((periodic 𝕜).d k (k + 1)).graph ↔ _
  rw [periodic_d_succ]
  by_cases hk : Even k
  · rw [periodicD_of_even hk, LinearPMap.mem_graph_iff]
    simp only [hk, ite_true]
    refine ⟨?_, fun h => ⟨⟨u, Submodule.mem_top⟩, rfl, lp.ext (funext fun n => (h n).symm)⟩⟩
    rintro ⟨y, hy, rfl⟩ n
    obtain rfl : (y : L2 𝕜) = u := hy
    exact diag_apply _ n
  · rw [periodicD_of_odd (Int.not_even_iff_odd.1 hk), LinearPMap.mem_graph_iff]
    simp only [hk, ite_false]
    refine ⟨?_, fun h => ⟨⟨u, Submodule.mem_top⟩, rfl, lp.ext (funext fun n => (h n).symm)⟩⟩
    rintro ⟨y, -, rfl⟩ n
    rfl

/-- **The harmonic forms vanish** in every degree. -/
theorem harmonic_eq_bot (k : ℤ) : (complex 𝕜).harmonic k = ⊥ :=
  ((complex 𝕜).harmonic_eq k).symm.trans (periodic_harmonic_eq_bot k)

/-- **`𝔅ᵏ` is closed iff `k` is even**: `𝔅ᵏ = 0` for even `k`, `𝔅ᵏ = R(A)` for odd `k`. -/
theorem isClosed_boundaries_iff (k : ℤ) :
    IsClosed ((complex 𝕜).boundaries k : Set (ℓ²(ℕ, 𝕜))) ↔ Even k :=
  ((complex 𝕜).closedRangeAt_iff k).symm.trans (periodic_closedRangeAt_iff k)

/-- The projections are the coordinate truncations. -/
theorem π_eq (N : ℕ) (k : ℤ) (x : ((complex 𝕜).d k (k + 1)).domain) :
    (((family 𝕜).π N).π k x : ℓ²(ℕ, 𝕜)) = truncSum 𝕜 N x :=
  starProjection_trunc N (x : L2 𝕜)

theorem π_apply (N : ℕ) (k : ℤ) (x : ((complex 𝕜).d k (k + 1)).domain) (n : ℕ) :
    (((family 𝕜).π N).π k x : ℓ²(ℕ, 𝕜)) n = if n < N then (x : ℓ²(ℕ, 𝕜)) n else 0 := by
  rw [π_eq]
  exact truncSum_apply N _ n

/-- **The truncations are bounded by `1` in `ℓ²`.** -/
theorem norm_π_le (N : ℕ) (k : ℤ) (x : ((complex 𝕜).d k (k + 1)).domain) :
    ‖(((family 𝕜).π N).π k x : ℓ²(ℕ, 𝕜))‖ ≤ ‖(x : ℓ²(ℕ, 𝕜))‖ :=
  Submodule.norm_starProjection_apply_le (trunc 𝕜 N) (x : L2 𝕜)

/-- **The truncations are bounded by `1` in the graph norm**: they commute with `d`. -/
theorem isGraphBoundedBy (k : ℤ) : (family 𝕜).IsGraphBoundedBy k 1 := fun N x => by
  refine (complex 𝕜).graphNorm_le_of_sq zero_le_one ?_
  rw [((family 𝕜).π N).comm k x, one_pow, one_mul]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (norm_π_le N k x) 2)
    (pow_le_pow_left₀ (norm_nonneg _) (norm_π_le N (k + 1) _) 2)

/-- **The truncation commutes with `d`**: `d (x - π_N x) = d x - π_N (d x)`. -/
theorem d_sub_π (N : ℕ) {k : ℤ} (x : ((complex 𝕜).d k (k + 1)).domain)
    (hv : (x : ℓ²(ℕ, 𝕜)) - (((family 𝕜).π N).π k x : ℓ²(ℕ, 𝕜)) ∈
      ((complex 𝕜).d k (k + 1)).domain) :
    (complex 𝕜).d k (k + 1) ⟨_, hv⟩ = (complex 𝕜).d k (k + 1) x -
      (((family 𝕜).π N).π (k + 1)
        ⟨(complex 𝕜).d k (k + 1) x, (complex 𝕜).mapsTo k (k + 1) (k + 1 + 1) x⟩ : ℓ²(ℕ, 𝕜)) := by
  rw [← ((family 𝕜).π N).comm k x, ← LinearPMap.map_sub]
  rfl

/-- **The family approximates in the graph norm** in every degree: `π_N x → x` and
`d π_N x = π_N d x → d x`. -/
theorem approximates (k : ℤ) : (family 𝕜).Approximates k := by
  refine (complex 𝕜).approximates_of_eventually (family 𝕜) k fun x ε hε => ?_
  have h1 := (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1
    (tendsto_truncSum (x : L2 𝕜)))).2 ε hε
  have h2 := (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1
    (tendsto_truncSum ((complex 𝕜).d k (k + 1) x : L2 𝕜)))).2 ε hε
  filter_upwards [h1, h2] with N hN1 hN2
  refine ⟨_, (((family 𝕜).π N).π k x).2, by rwa [π_eq, norm_sub_rev], ?_⟩
  rw [d_sub_π, π_eq, norm_sub_rev]
  exact hN2

/-- `dⁱ = A` from an even degree. -/
theorem d_apply_of_even {i j : ℤ} (hij : i + 1 = j) (hi : Even i)
    (x : ((complex 𝕜).d i j).domain) : ((complex 𝕜).d i j x : ℓ²(ℕ, 𝕜)) = diag 𝕜 x := by
  subst hij
  refine lp.ext (funext fun n => ?_)
  have h := ((mem_graph_iff i x ((complex 𝕜).d i (i + 1) x)).1
    (((complex 𝕜).d i (i + 1)).mem_graph x)) n
  simp only [hi, ite_true] at h
  exact h

/-- `dⁱ = 0` from an odd degree. -/
theorem d_apply_of_odd {i j : ℤ} (hij : i + 1 = j) (hi : Odd i)
    (x : ((complex 𝕜).d i j).domain) : ((complex 𝕜).d i j x : ℓ²(ℕ, 𝕜)) = 0 := by
  subst hij
  refine lp.ext (funext fun n => ?_)
  have h := ((mem_graph_iff i x ((complex 𝕜).d i (i + 1) x)).1
    (((complex 𝕜).d i (i + 1)).mem_graph x)) n
  simp only [Int.not_even_iff_odd.2 hi, ite_false] at h
  exact h

theorem domain_eq_top (i : ℤ) : ((complex 𝕜).d i (i + 1)).domain = ⊤ := by
  change ((periodic 𝕜).d i (i + 1)).domain = ⊤
  rw [periodic_d_succ, periodicD_domain]

/-- **The mixed problem is not solvable in odd degrees**: for the datum `f = (1/(n+1))ₙ`, a
solution `(σ, u, p)` in degree `j` would have `A σ = f` (test with `(0, v, 0)`: `dʲ = 0` and
`ℌʲ = 0`), but `f ∉ R(A)` (`Feec.Counterexamples.Fredholm.harm_not_mem_range`). -/
theorem not_isMixedSolution_of_odd {j : ℤ} (hj : Odd j) (x : (complex 𝕜).Mixed j) :
    ¬ IsMixedSolution ((complex 𝕜).mixedSpace j) (harm : ℓ²(ℕ, 𝕜)) x := by
  rintro ⟨hx, hsol⟩
  have hp : x.2.2 = 0 := by
    have := hx.2.2
    rwa [harmonic_eq_bot, SetLike.mem_coe, Submodule.mem_bot] at this
  have key : ∀ v : ℓ²(ℕ, 𝕜),
      ⟪v, ((complex 𝕜).d (j - 1) j x.1 : ℓ²(ℕ, 𝕜))⟫_𝕜 = ⟪v, (harm : ℓ²(ℕ, 𝕜))⟫_𝕜 := fun v => by
    have hv : v ∈ ((complex 𝕜).d j (j + 1)).domain := by rw [domain_eq_top]; trivial
    have h := hsol (0, ⟨v, hv⟩, 0) ⟨trivial, trivial, zero_mem _⟩
    simp only [mixedForm, Submodule.coe_zero, inner_zero_left, LinearPMap.map_zero, hp,
      inner_zero_right, d_apply_of_odd rfl hj, sub_zero, zero_add, add_zero] at h
    exact h
  exact harm_not_mem_range (𝕜 := 𝕜) ⟨(x.1 : ℓ²(ℕ, 𝕜)), (d_apply_of_even (sub_add_cancel j 1)
    (hj.sub_odd odd_one) x.1).symm.trans (ext_inner_left 𝕜 key)⟩

/-- **No static verdict in odd degrees**, for any constant: its `existsUnique` clause fails at
`f = (1/(n+1))ₙ`. -/
theorem not_staticVerdict_of_odd {j : ℤ} (hj : Odd j) (C : ℝ) :
    ¬ (family 𝕜).StaticVerdict j C := fun hV =>
  not_isMixedSolution_of_odd hj _ ((hV.existsUnique (harm : ℓ²(ℕ, 𝕜))).1.exists.choose_spec)

end FEEC.Sharpness
