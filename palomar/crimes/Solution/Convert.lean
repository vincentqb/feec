module

public import Solution.Crime

/-!
# The verdicts of the challenge from their componentwise forms

The verdicts of `Solution.Crime` are proved for the componentwise forms of `Solution.Legacy`; with
the one-equation mixed problem of the window (`HilbertComplex.isMixedSolution_total_iff`) and the
triples of the crimes (`CrimeFamily.isSolution_iff`, `CrimeFamily.readError_eq₀`) they are the
verdicts of the challenge (`CrimeFamily.StaticVerdict₀.toStaticVerdict`,
`CrimeFamily.CochainVerdict₀.toCochainVerdict`).

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

variable {H : HilbertComplex 𝕜 W} {κ : Type*}

namespace CrimeFamily

variable {a : ℤ} {m : ℕ} (S : H.CrimeFamily a m κ)

theorem readGap_zero (h : κ) (y : Total W a m) (v : S.X h) :
    S.readGap h y 0 v = ‖y - S.incl h v‖ + ‖S.incl h (S.D h v)‖ := by
  rw [readGap, zero_sub, norm_neg]

/-- **The static verdict with crimes** from its componentwise form. -/
theorem StaticVerdict₀.toStaticVerdict {S : H.CrimeFamily a m κ} {C : ℝ} (V : S.StaticVerdict₀ C) :
    S.StaticVerdict C := by
  refine ⟨fun f => ⟨?_, fun h => ?_⟩, fun h f x hs => ?_, fun h f x hs xh hsh x' ε hε hres => ?_,
    fun hD hc f => ?_⟩
  · obtain ⟨y, hy, hu⟩ := V.existsUnique f
    exact ⟨y, isMixedSolution_total_iff.2 hy, fun z hz => hu z (isMixedSolution_total_iff.1 hz)⟩
  · obtain ⟨y, hy, hu⟩ := V.existsUnique_discrete h f
    exact ⟨y, (S.isSolution_iff).2 hy, fun z hz => hu z ((S.isSolution_iff).1 hz)⟩
  · exact V.stable h ((S.isSolution_iff).1 hs)
  · rw [S.readError_eq₀, S.readError_eq₀]
    exact V.strang h (isMixedSolution_total_iff.1 hs) ((S.isSolution_iff).1 hsh) x'.1 x'.2.1
      x'.2.2 hres.1 hε fun τ v q hq => hres.2 (τ, v, q) hq
  · refine (S.convergesAt_iff).2 fun σ u p hs σh uh ph hsh => V.converges hD (fun g hg => ?_) hs hsh
    intro σ' u' p' hs' ε hε
    filter_upwards [hc g hg (σ', u', p') (isMixedSolution_total_iff.2 hs') ε hε] with h hh
    obtain ⟨x', h1, h2⟩ := hh
    rw [S.readError_eq₀] at h1
    exact ⟨x'.1, x'.2.1, x'.2.2, h2.1, h1, fun τ v q hq => h2.2 (τ, v, q) hq⟩

/-- **The cochain verdict with crimes** from its componentwise form. -/
theorem CochainVerdict₀.toCochainVerdict {S : H.CrimeFamily a m κ} {Cπ : ℝ} {P : S.CochainProj Cπ}
    (V : S.CochainVerdict₀ P) : S.CochainVerdict P where
  poincare := V.poincare
  converges hJ hπ f := (S.convergesAt_iff).2 fun _ _ _ hs _ _ _ hsh => V.converges hJ hπ hs hsh
  cohomology hπ := V.cohomology hπ
  rate := by
    obtain ⟨K, hK⟩ := V.rate
    refine ⟨K, fun h f x hs xh hsh ε hσ hu hp hb hJ => ?_⟩
    rw [S.readError_eq₀]
    refine hK h (isMixedSolution_total_iff.1 hs) ((S.isSolution_iff).1 hsh) hσ hu ?_ ?_ hJ
    · obtain ⟨v, hv⟩ := hp; exact ⟨v, by rwa [S.readGap_zero] at hv⟩
    · obtain ⟨v, hv⟩ := hb; exact ⟨v, by rwa [S.readGap_zero] at hv⟩

end CrimeFamily

end HilbertComplex

end FEEC
