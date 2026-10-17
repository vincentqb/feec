module

public import Feec.Models.Cube.MirrorSym
public import Feec.Legacy.MirrorCube.BggCube

/-!
# The BGG complex (5.1) on the cube with mirror boundary conditions

The method of Thesis Ch. 6 solves the linearized Einstein–Bianchi system through the Hodge wave
equation of the BGG complex (5.1), `grad grad → (S₁, curl)`, imposing the symmetry of `E` weakly
through a multiplier `M`. On the torus the constraint `{0} × L²(TSD) × ({0} × L²(TSD))` (no
multiplier, `B` TSD) reduces the complex (`reducingSubcomplex_tsd_torusBGG`). On the cube
`Q = (0, ½)³` with mirror boundary conditions (`u` even, `E` with the tensor parities, the
multiplier with the pseudo-vector parities `M(R_i x) = -D_i M(x)`, `B` with the pseudo-tensor
parities) the complex of genuine fields (`MirrorBGG.complexQ`, `Feec.Legacy.MirrorCube.bggCxQ`) is a
compression of the torus complex, and the constraint pulls back
(`MirrorBGG.reducingSubcomplexQ`): TSD data give solutions with `σ ≡ 0`, `u` TSD (the weakly
imposed symmetry holds strongly), `M ≡ 0` and `B` TSD, in particular symmetric
(`MirrorBGG.mem_tsdQ_iff`). This is the repair of the Ch. 6 claim; with the boundary conditions of
Thesis §6.3 it fails on every bounded domain (`Feec.Legacy.BoundedBGG.bggComplex_verdict`).

## Main results

* `reducingSubcomplex_tsd_torusBGG`.
* **`MirrorBGG.reducingSubcomplexQ`**, `MirrorBGG.propagatesQ`, `MirrorBGG.existsUnique_memQ`,
  `MirrorBGG.invariantCore_eqQ`, `MirrorBGG.exists_nonstationaryQ`, `MirrorBGG.mem_tsdQ_iff`.

## References

* [QuennevilleBelair2015], Ch. 5 (§5.1), Ch. 6 (§6.1, §6.3)
* [ArnoldHu2021] (BGG), [AFW2007] (weak symmetry)
-/

open Feec.Legacy

open scoped RealInnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.Models.Cube

open Feec.Legacy.HilbertComplex2 Feec.ShortHilbertComplex Feec.Legacy.Constraints Feec.Legacy.Torus Feec.Legacy.Box
open Feec.HilbertComplex (ScaledEmbedding totalSub ReducingSubcomplex)
open Feec.Legacy.MirrorCube

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

/-- The torus BGG complex (5.1) `L²(𝕋³; ℂ) → L²(𝕋³; ℂ³ˣ³) → L²(𝕋³; ℂ³ × ℂ³ˣ³)`
(`Feec.Legacy.MirrorCube.bggTorus`) as a window complex. -/
abbrev torusBGG := bggTorus.toShort.toHilbertComplex

theorem isReducingPair_hess_bgg :
    bggTorus.d0.IsReducingPair (⊥ : Submodule ℝ L2RT) L2TSD := by
  refine isReducingPair_of_le_ker bot_le fun x => ?_
  rw [Submodule.mem_orthogonal]
  intro y hy
  obtain ⟨z, hz, hz0⟩ := mem_ker_iff.1 (L2TSD_le_ker_bggT hy)
  have h := adjoint_isFormalAdjoint bggTorus.dense0 z x
  rw [hz0, inner_zero_left] at h
  rw [hz]; exact h.symm

/-- On the fibres, `(S₁, curl) P_TSD = P_{0 × TSD} (S₁, curl)`. -/
theorem bggSym_starProjection (ζ : Freq) (M : Mat3) :
    Feec.Legacy.WholeBGG.bggSym ζ ((tsd ζ).starProjection M) =
      (Feec.Legacy.WholeBGG.tsdB ζ).starProjection (Feec.Legacy.WholeBGG.bggSym ζ M) := by
  have hP := Submodule.starProjection_apply_mem (tsd ζ) M
  rw [Feec.Legacy.WholeBGG.bggSym_apply, Feec.Legacy.WholeBGG.skwSym_eq_zero_of_symm hP.1, ← proj_curlSym,
    Feec.Legacy.WholeBGG.starProjection_tsdB, Feec.Legacy.WholeBGG.bggSym_apply, WithLp.ofLp_toLp]
  rfl

theorem isReducingPair_bgg_tsd : bggTorus.d1.IsReducingPair L2TSD L2TSDBT := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have hx : (x : L2M) ∈ Hcurl := bggT_domain_iff.1 x.2
    exact bggT_domain_iff.2 (projTSD_mem_Hcurl hx)
  · refine lp.ext (funext fun k => ?_)
    change Feec.Legacy.WholeBGG.bggSym (freq k) (L2TSD.starProjection x k) =
      L2TSDBT.starProjection (bggT x) k
    rw [projTSD_apply, projTSDBT_apply, bggSym_starProjection]
    rfl

/-- **`{0} × L²(TSD) × ({0} × L²(TSD))` reduces the torus BGG complex.**
Thesis: Prop 4.17, Ch. 6 -/
theorem reducingSubcomplex_tsd_torusBGG :
    torusBGG.ReducingSubcomplex (sub3 (⊥ : Submodule ℝ L2RT) L2TSD L2TSDBT) :=
  reducingSubcomplex_sub3 _ isReducingPair_hess_bgg isReducingPair_bgg_tsd

namespace MirrorBGG

/-- **The BGG complex (5.1) of genuine fields on `Q` with mirror boundary conditions**
(`Feec.Legacy.MirrorCube.bggCxQ`). -/
abbrev complexQ := bggCxQ.toShort.toHilbertComplex

/-- The mirror extensions embed the BGG complex on `Q` in the torus BGG complex. -/
def embeddingQ : ScaledEmbedding complexQ torusBGG :=
  comprEmbedding bggTorus comprR (comprM 1 one_mul_one) comprW comprComm_hessTT comprComm_bggT
    eight_pos'

/-- The constraint on `Q`: `σ = 0`, `u ∈ TSDmE`, `(M, B) ∈ {0} × TSDmB`. -/
abbrev tsdQ : ∀ i : Fin 3, Submodule ℝ (W3 RQ MQ W2Q i) := sub3 (⊥ : Submodule ℝ RQ) TSDmE TSDBm

theorem mem_tsdQ_iff {x : PiLp 2 (W3 RQ MQ W2Q)} :
    x ∈ totalSub tsdQ ↔ slot0 x = 0 ∧ slot1 x ∈ TSDmE ∧
      (WithLp.ofLp (slot2 x)).1 = 0 ∧ (WithLp.ofLp (slot2 x)).2 ∈ TSDmB := by
  rw [mem_totalSub_sub3]
  exact and_congr (Submodule.mem_bot ℝ (M := RQ)) (and_congr Iff.rfl mem_TSDBm)

/-- **TSD reduces the BGG complex on `Q`.**
Thesis: Prop 4.17 (corrected), Ch. 6 -/
theorem reducingSubcomplexQ : complexQ.ReducingSubcomplex tsdQ :=
  reducingSubcomplex_compr bggTorus comprR (comprM 1 one_mul_one) comprW comprComm_hessTT
    comprComm_bggT eight_pos' reducingSubcomplex_tsd_torusBGG (starProjection_Pm 1 one_mul_one)
    starProjection_comprW

/-- **The Ch. 6 method on `Q` with mirror boundary conditions keeps TSD data TSD**: strong
solutions of the BGG Hodge wave equation with data and forcing in the constraint stay there, so
`σ ≡ 0`, `u` is TSD, the multiplier vanishes and `B` is TSD.
Thesis: Ch. 6 (corrected) -/
theorem propagatesQ {a b : ℝ} {F U : ℝ → PiLp 2 (W3 RQ MQ W2Q)}
    (hU : Evolution.IsStrongSolution complexQ.wave (Icc a b) F U) (h0 : U a ∈ totalSub tsdQ)
    (hF : ∀ t ∈ Icc a b, F t ∈ totalSub tsdQ) : ∀ t ∈ Icc a b, U t ∈ totalSub tsdQ :=
  reducingSubcomplexQ.propagates hU h0 hF

/-- The Ch. 6 system on `Q` with existence and uniqueness.
Thesis: Ch. 6 (corrected) -/
theorem existsUnique_memQ {U₀ : PiLp 2 (W3 RQ MQ W2Q)} (hU₀ : U₀ ∈ complexQ.wave.domain)
    (hU₀S : U₀ ∈ totalSub tsdQ) {F : ℝ → PiLp 2 (W3 RQ MQ W2Q)} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complexQ.wave a b F)
    (hFS : ∀ t ∈ Icc a b, F t ∈ totalSub tsdQ) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complexQ.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ totalSub tsdQ) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complexQ.wave (Icc a b) F V → EqOn V U (Icc a b) :=
  reducingSubcomplexQ.existsUnique_mem hU₀ hU₀S hF hFS

/-- `K* = K` for the Ch. 6 system on `Q`.
Thesis: Ch. 6 (corrected) -/
theorem invariantCore_eqQ : complexQ.waveGroup.invariantCore (totalSub tsdQ) = totalSub tsdQ :=
  reducingSubcomplexQ.invariantCore_eq

/-- A non-stationary TSD datum for the Ch. 6 system on `Q`.
Thesis: Ch. 6 (corrected) -/
theorem exists_nonstationaryQ :
    ∃ y ∈ complexQ.wave.domain, y ∈ totalSub tsdQ ∧ y ∉ complexQ.waveGroup.stationary :=
  ⟨totEquiv cosStateB, (mem_domL_iff bggCxQ).1 cosStateB_mem_domL,
    (mem_Kc_iff TSDmE TSDBm cosStateB).1 cosStateB_mem_Kc,
    totEquiv_not_mem_stationary bggCxQ cosStateB_mem_domL cosStateB_waveOp_ne⟩

end MirrorBGG

end Feec.Models.Cube
