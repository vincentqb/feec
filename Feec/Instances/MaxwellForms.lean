module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.Physics.Maxwell.Forms

/-!
# Maxwell's equations for differential forms as instances of the FEEC theorem

Maxwell's equations for `(k + 1)`-form electric fields on an open `Ω ⊆ ℝⁿ` with a perfect
electric conductor, `σ' = -d†E`, `E' = dσ - d†B`, `B' = dE`, are the Hodge wave equation of the
short complex `H̊Λᵏ(Ω) → H̊Λᵏ⁺¹(Ω) → L²Λᵏ⁺²(Ω)` of the minimal realizations of the exterior
derivative (`Feec.Maxwell.pecForms`; `d = d_min`, `d† = (dᵗ)_max = -δ`, the weak codifferential,
`Feec.Domain.deRham_dual_minimalComplex_d`), with the Gauss laws `σ = 0`, `d†E = 0`, `d_min B = 0`
as constraint (complex fields). For every constrained FEEC discretization of this complex with the
Gauss laws as constraint, the verdict of the constrained FEEC theorem holds, the Gauss laws reduce
`L` (`ShortHilbertComplex.reducingSubcomplex_divFreeSub`), propagate along strong solutions with
forcing in them (`Feec.Maxwell.pecForms_gauss_propagates`), and the Gauss residual of the discrete
solutions tends to `0` (`formsFEEC`).

**Scope.** No discretization of `pecForms` is constructed here, so `formsFEEC` is a statement
about every one that will be. The constructed discretizations of PEC Maxwell,
`Feec.Instances.Maxwell.cubePEC` and `cubePolyPEC` on the cube, are of a window of `H̊Λ(Q)` whose
degrees are indexed `k + ↑i`; its identification with `pecForms` on `Q` is open.

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6, Ch. 8
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.9 (Prop. 4.16), Thms 4.6, 4.14

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.Instances.MaxwellForms

open Feec.HilbertComplex Feec.ShortHilbertComplex Feec.Maxwell _root_.Feec.HodgeWave
open Feec.Domain (L2F formIdx)

variable {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) [Fact (IsOpen Ω)] (k : ℤ) {κ : Type*}

/-- **The Gauss laws** `σ = 0`, `d†E = 0`, `d_min B = 0` of Maxwell's equations for forms with a
perfect electric conductor. -/
abbrev gauss : Submodule ℂ (FormSpace ℂ Ω k) :=
  totalSub ((pecForms ℂ hΩ k).divFreeSub (magneticPECForms ℂ Ω k))

/-- **The FEEC theorem for Maxwell's equations for forms** with a perfect electric conductor on an
open `Ω ⊆ ℝⁿ`, in degree `k`, for a constrained FEEC discretization `G` with the Gauss laws: the
verdict of the constrained FEEC theorem, the Gauss laws reduce `L`, propagate along strong solutions
with forcing in them, and the Gauss residual of the discrete solutions from `D(L)` data satisfying
them tends to `0` uniformly on `[0, T]`. [QuennevilleBelair2015], Thms 4.6, 4.14, Prop. 4.16 -/
structure Verdict (G : ConstrainedFEEC (pecForms ℂ hΩ k).toHilbertComplex κ) : Prop
    extends G.Verdict where
  /-- the Gauss laws reduce `L` -/
  isReducing : (pecForms ℂ hΩ k).wave.IsReducing G.K
  /-- they propagate along strong solutions with forcing in them -/
  gauss_propagates {t₀ t₁ : ℝ} {F U : ℝ → FormSpace ℂ Ω k}
    (hU : Evolution.IsStrongSolution (pecForms ℂ hΩ k).wave (Icc t₀ t₁) F U) (h0 : U t₀ ∈ G.K)
    (hF : ∀ t ∈ Icc t₀ t₁, F t ∈ G.K) : ∀ t ∈ Icc t₀ t₁, U t ∈ G.K
  /-- the Gauss residual of the discrete solutions tends to `0` uniformly on `[0, T]` -/
  gauss_residual_tendsto (x : (pecForms ℂ hΩ k).toHilbertComplex.wave.domain)
    (hxK : (x : FormSpace ℂ Ω k) ∈ G.K) (T : ℝ) :
    TendstoUniformlyOn
      (fun h t => infDist ((pecForms ℂ hΩ k).toHilbertComplex.totalD.graphFst
        (G.discrete h (waveLift _ x) t)) (G.K : Set (FormSpace ℂ Ω k))) (fun _ => 0) G.l (Icc 0 T)

/-- **The FEEC theorem for Maxwell's equations for forms**: `constrainedFEEC` for every
discretization with the Gauss laws (none is constructed yet), which reduce `L`
(`ShortHilbertComplex.reducingSubcomplex_divFreeSub`) and propagate
(`Feec.Maxwell.pecForms_gauss_propagates`). [QuennevilleBelair2015], Thms 4.6, 4.14, Prop. 4.16 -/
theorem formsFEEC (G : ConstrainedFEEC (pecForms ℂ hΩ k).toHilbertComplex κ)
    (hK : G.K = gauss hΩ k) : Verdict hΩ k G :=
  have hr : (pecForms ℂ hΩ k).wave.IsReducing G.K := by
    convert ((pecForms ℂ hΩ k).reducingSubcomplex_divFreeSub _
      (d_mem_magneticPECForms hΩ k)).isReducing_wave
  have V := constrainedFEEC G
  { V with
    isReducing := hr
    gauss_propagates := fun hU h0 hF => by
      rw [hK] at h0 hF ⊢
      exact pecForms_gauss_propagates hΩ k hU h0 hF
    gauss_residual_tendsto := V.residual_tendsto hr }

end Feec.Instances.MaxwellForms
