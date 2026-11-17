module

public import Solution.MirrorFEM
public import Solution.CubeWave
public import Feec.Models.Cube.MirrorWaveRegularity

/-!
# The rate of the mirror scheme (6.5) for TSD data of `D(L³)`

A solution of `Feec`'s semi-discrete system for `mirrorWave` without source is a solution of the
challenge's (6.5) for `mirrorQ` with source `0` (`isDiscreteWave_of_mirror`), so the `O(h)` rate
`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain` for every TSD datum with
`L²U₀ ∈ D(L)` is a rate of (6.5) (`mirrorQ_rate`): the errors are measured against the rows
`Re E`, `Re B` of the exact solution of the Einstein–Bianchi system on the cube.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.3, (6.5), Table 6.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set

@[expose] public noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM
  Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)

section Rate

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) (N : ℕ)

set_option maxHeartbeats 4000000 in
/-- **`Feec`'s semi-discrete solutions without source are solutions of (6.5) for `mirrorQ`.** -/
theorem isDiscreteWave_of_mirror {T : ℝ}
    (sh : @Feec.BGG.DiscreteSolution (mirrorFEM hT hB N).V0h (mirrorFEM hT hB N).V1h
      (mirrorFEM hT hB N).W2h (mirrorFEM hT hB N).Vt0h (mirrorFEM hT hB N).Vt1h
      (mirrorFEM hT hB N).Wt2h _ _ _ _ _ _ _ _ _ _ _ _ (mirrorWave hT hB N) T
      (mirrorSource hT hB N 0)) :
    (mirrorQ hT hB N).IsDiscreteWave T 0 (fun t => ((sh.σ t : TU0) : 𝒟m.d0.domain))
      (fun t => e0m.symm (sh.φ t : BU0)) (fun t => e1m.symm (sh.u t : BU1))
      (fun t => (sh.M t : W2)) (fun t => (sh.ρ t : Wv W2)) (fun t => ((sh.lam t : TU1) : W1)) := by
  refine ⟨?_, ?_, ?_, ?_, fun t ht => ?_, fun t => ((sh.σ' t : TU0) : W0),
    fun t => bIncl1 (sh.u' t : BU1), fun t => (sh.M' t : W2), fun t => (sh.ρ' t : Wv W2),
    fun t ht => ?_⟩
  · exact continuous_subtype_val.comp_continuousOn (continuous_subtype_val.comp_continuousOn sh.cσ)
  · exact bIncl1CLM.continuous.comp_continuousOn (continuous_subtype_val.comp_continuousOn sh.cu)
  · exact continuous_subtype_val.comp_continuousOn sh.cM
  · exact continuous_subtype_val.comp_continuousOn sh.cρ
  · have hc := sh.constraint ht
    exact ⟨(sh.σ t).2, fun a => (sh.φ t).2 a, fun a => (sh.u t).2 a, (sh.M t).2,
      fun a => (sh.ρ t).2 a, (sh.lam t).2,
      (congrArg (fun x : (mirrorFEM hT hB N).V1h => ((x : TU1) : W1)) hc :)⟩
  · have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
    have hu := bIncl1CLM.hasFDerivAt.comp_hasDerivWithinAt t
      (hasDerivWithinAt_coe _ (sh.du t ht))
    refine ⟨hasDerivWithinAt_coe _ (hasDerivWithinAt_coe _ (sh.dσ t ht)), hu,
      hasDerivWithinAt_coe _ (sh.dM t ht), hasDerivWithinAt_coe _ (sh.dρ t ht),
      fun τ ψ hτ hψ => ?_, fun v hv => ?_, fun z hz => ?_, fun z hz => ?_⟩
    · exact sh.ea t ht' ⟨τ, hτ⟩ ⟨e0m ψ, e0m_mem hT hB N hψ⟩
    · have := sh.eb t ht ⟨e1m v, e1m_mem hT hB N hv⟩
      have hs := inner_mirrorSource hT hB N 0 t ⟨e1m v, e1m_mem hT hB N hv⟩
      exact this.trans hs
    · exact sub_eq_zero.1 (sh.ec t ht ⟨z, hz⟩)
    · exact sub_eq_zero.1 (sh.ed t ht ⟨z, fun a => hz a⟩)

set_option maxHeartbeats 4000000 in
/-- **The `O(h)` rate of (6.5) for TSD data of `D(L³)`**
(`mirror_waveFEM_rate_of_mem_domain`). -/
theorem mirrorQ_rate : ∃ K, 0 ≤ K ∧ ∀ N (D : TSDDatum)
    (h3 : D.LLU₀ ∈ Feec.Models.Cube.MirrorBGG.complexQ.wave.domain) (T : ℝ), 0 < T →
    ∀ U : ℝ → PiLp 2 Feec.Models.Cube.MirrorBGG.SpaceQ, U 0 = D.U₀ →
      Feec.Evolution.IsStrongSolution Feec.Models.Cube.MirrorBGG.complexQ.wave (Icc 0 T) 0 U →
    ∃ σh φh uh Mh ρh lamh, (mirrorQ hT hB N).IsDiscreteWave T 0 σh φh uh Mh ρh lamh ∧
      ∀ t ∈ Icc 0 T, √(‖(σh t : W0)‖ ^ 2 + ‖rowsW1L (stEL (U t)) - (uh t : Wv W1)‖ ^ 2 +
        ‖Mh t‖ ^ 2 + ‖rowsW2L (stBL (U t)) - ρh t‖ ^ 2) ≤
        K * (‖D.U₀‖ + ‖D.LU₀‖ + ‖D.LLU₀‖ +
          ‖Feec.Models.Cube.MirrorBGG.complexQ.wave ⟨D.LLU₀, h3⟩‖) * (1 + t) *
            Feec.Models.Cube.FEM.meshSize N := by
  obtain ⟨K, hK0, hK⟩ := mirror_waveFEM_rate_of_mem_domain hT hB
  refine ⟨K, hK0, fun N D h3 T hT0 U hU0 hU => ?_⟩
  obtain ⟨sh, -, hsh⟩ := hK N D h3 hT0 hU0 hU
  exact ⟨_, _, _, _, _, _, isDiscreteWave_of_mirror hT hB N sh, fun t ht => hsh t ht⟩

end Rate

end FEEC
