module

public import Solution.Bridge

/-!
# The static FEEC theorem (solution)

`FEEC.staticFEEC` of `Challenge.lean`, proved from `Feec.HilbertComplex.GraphFamily.staticFEEC`
through the bridge `Solution.Bridge` (`HilbertComplex.ConformingFamily.staticVerdict`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3–§3.4

Bibliography: [references.bib](../../docs/references.bib)
-/

open Filter Topology

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-- **The static FEEC theorem** ([AFW2010], Thms 3.4–3.6, 3.8, 3.9). Let `F` be a conforming
family whose cochain projections are bounded uniformly in the graph norm,
`‖πₕ x‖ + ‖d πₕ x‖ ≤ C (‖x‖ + ‖d x‖)`, and which approximates every `x ∈ D(d)` in the graph norm.
In a degree `j` where the ranges `𝔅ʲ` of `dʲ⁻¹` and `𝔅ʲ⁺¹` of `dʲ` are closed and `ℌʲ` is
finite-dimensional, `F` satisfies the static verdict (`ConformingFamily.StaticVerdict`). -/
theorem staticFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} (F : H.ConformingFamily κ)
    (hπ : ∃ C : ℝ, ∀ (h : κ) (i : ℤ) (x : (H.d i (i + 1)).domain),
      ‖(F.π h).π i x‖ +
        ‖H.d i (i + 1) ⟨(F.π h).π i x, (F.V h).le_domain i (i + 1) ((F.π h).mem i x)⟩‖ ≤
          C * (‖(x : W i)‖ + ‖H.d i (i + 1) x‖))
    (happrox : ∀ (i : ℤ) (x : (H.d i (i + 1)).domain),
      Tendsto (fun h => (F.V h).graphDist i (i + 1) x (H.d i (i + 1) x)) F.l (𝓝 0))
    (j : ℤ) (hj : IsClosed (H.boundaries j : Set (W j)))
    (hj' : IsClosed (H.boundaries (j + 1) : Set (W (j + 1)))) [FiniteDimensional 𝕜 (H.harmonic j)] :
    F.StaticVerdict j :=
  F.staticVerdict hπ happrox j hj hj'

end FEEC
