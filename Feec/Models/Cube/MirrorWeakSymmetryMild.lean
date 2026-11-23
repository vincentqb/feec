module

public import Feec.Models.Cube.MirrorWeakSymmetryTSD
public import Feec.Semigroup.DomainSq
public import Mathlib.Analysis.Complex.OperatorNorm

/-!
# The mirror scheme (6.5) converges from every datum of the constraint

`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM` proves that the mirror scheme (6.5) of
[QuennevilleBelair2015], §6.3, on the cube `Q = (0, ½)³` converges to the real part of the TSD
solution `e^{tL} U₀` of the Ch. 6 system for data `U₀ ∈ D(L²)` in the constraint
`{0} × L²(TSD) × ({0} × L²(TSD))`. This file removes the regularity: for every `x` in the
constraint, with no domain hypothesis, the real part of the orbit `e^{tL} x` (a mild solution, a
strong one when `x ∈ D(L)`) is the uniform limit on `[0, T]` of solutions of (6.5) without
source (`mirror_waveFEM_of_mem_tsd`).

The constraint reduces the wave operator (`Feec.Models.Cube.MirrorBGG.reducingSubcomplexQ`), so
`D(L²)` is dense in it (`LinearPMap.IsSkewAdjoint.subset_closure_domainSq_inf`). At a datum `y`
of `D(L²)` in the constraint close to `x` the scheme converges (`mirrorWave_converges` through
`TSDDatum.exactWave`), and the real parts of the two orbits stay within `‖x - y‖` on `[0, T]`:
the wave group is unitary, and the real parts of the fields are no larger than the state
(`sq_norm_rowsW1L_add_sq_norm_rowsW2L_le`).

## Main results

* `Feec.Models.Cube.RowWise.norm_reL_le`, `sq_norm_rowsW1L_le`, `sq_norm_rowsW2L_le`,
  `sq_norm_rowsW1L_add_sq_norm_rowsW2L_le`.
* **`mirror_waveFEM_of_mem_tsd`**.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 6 (§6.3 (6.5))
* [K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*][EngelNagel2000],
  §II.1 (cores and powers of generators)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set MeasureTheory Filter

@[expose] public noncomputable section

namespace Feec.Models.Cube.RowWise

/-- **The real part is a contraction of `L²`**: `‖Re f‖ ≤ ‖f‖`. -/
theorem norm_reL_le {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℂ 2 μ) :
    ‖reL μ f‖ ≤ ‖f‖ := by
  have h := Complex.reCLM.norm_compLp_le f
  rwa [Complex.reCLM_norm, one_mul] at h

end Feec.Models.Cube.RowWise

namespace Feec.Models.Cube.MirrorWeakSymmetry

open Feec.Models.Cube.Mirror (MQ)
open Feec.Domain (formIdx)
open Feec.Models.Cube.RowWise (reL norm_reL_le)
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)
open Feec.HilbertComplex (totalSub)

/-! ### The real fields of a state -/

theorem abs_sg2 (i : Fin 3) : |sg2 i| = 1 := by
  unfold sg2; split_ifs <;> norm_num

/-- The real rows of a matrix field are no larger than the field: `‖Re E‖ ≤ ‖E‖`. -/
theorem sq_norm_rowsW1L_le (E : MQ) : ‖rowsW1L E‖ ^ 2 ≤ ‖E‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [rowsW1L_apply, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2,
    ← Fintype.sum_equiv (κ := formIdx 3 ((1 : ℕ) : ℤ)) eq1 (fun b => ‖rowRe E a (eq1 b)‖ ^ 2) _
      fun _ => rfl]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [rowRe_eq1]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_reL_le _) 2

/-- The real rows of a matrix field through the Hodge star are no larger than the field. -/
theorem sq_norm_rowsW2L_le (B : MQ) : ‖rowsW2L B‖ ^ 2 ≤ ‖B‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [rowsW2L_apply, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2,
    ← Fintype.sum_equiv (κ := formIdx 3 ((2 : ℕ) : ℤ)) eq2 (fun i => ‖rowRe2 B a (eq2 i)‖ ^ 2) _
      fun _ => rfl]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [rowRe2_eq2, norm_smul, Real.norm_eq_abs, abs_sg2, one_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_reL_le _) 2

/-- **The real fields of a state are no larger than the state**: for `x = (σ, E, (M, B))`,
`‖Re E‖² + ‖Re B‖² ≤ ‖x‖²` (rows as forms, `B` through the Hodge star). -/
theorem sq_norm_rowsW1L_add_sq_norm_rowsW2L_le (x : PiLp 2 MirrorBGG.SpaceQ) :
    ‖rowsW1L (stEL x)‖ ^ 2 + ‖rowsW2L (stBL x)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h1 : ‖rowsW1L (stEL x)‖ ^ 2 ≤ ‖(x 1 : MQ)‖ ^ 2 := sq_norm_rowsW1L_le _
  have h2 : ‖rowsW2L (stBL x)‖ ^ 2 ≤ ‖(WithLp.ofLp (x 2 : MirrorBGG.W2Q)).2‖ ^ 2 :=
    sq_norm_rowsW2L_le _
  have h3 : ‖(x 2 : MirrorBGG.W2Q)‖ ^ 2 = ‖(WithLp.ofLp (x 2 : MirrorBGG.W2Q)).1‖ ^ 2 +
      ‖(WithLp.ofLp (x 2 : MirrorBGG.W2Q)).2‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 _
  have h4 : ‖x‖ ^ 2 = ‖(x 0 : Feec.Models.Cube.MirrorSym.RQ)‖ ^ 2 + ‖(x 1 : MQ)‖ ^ 2 +
      ‖(x 2 : MirrorBGG.W2Q)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  linarith [sq_nonneg ‖(x 0 : Feec.Models.Cube.MirrorSym.RQ)‖,
    sq_nonneg ‖(WithLp.ofLp (x 2 : MirrorBGG.W2Q)).1‖]

/-! ### Convergence from every datum of the constraint -/

section Main

open Feec.Models.Cube.FEM Feec.FiniteElement

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

set_option maxHeartbeats 4000000 in
/-- **The mirror scheme (6.5) converges to the real part of every solution from the constraint,
with no regularity** ([QuennevilleBelair2015], Ch. 6, §6.3, (6.5)). Let `x` lie in the constraint
`{0} × L²(TSD) × ({0} × L²(TSD))` of `Feec.Models.Cube.MirrorBGG.complexQ` (no domain hypothesis)
and `T > 0`, and write `(0, E, (0, B))(t) = e^{tL} x`. For every `ε > 0` and all large `N`, the
scheme (6.5) without source has a solution with
`(‖σₕ‖² + ‖Re E − uₕ‖² + ‖Mₕ‖² + ‖Re B − ρₕ‖²)^{1/2}(t) ≤ ε` on `[0,T]` (the rows of the matrix
fields as forms, `B` through the Hodge star). At a datum `y` of `D(L²)` in the constraint within
`ε / 2` of `x` (`D(L²)` is dense in the constraint, which reduces `L`) the scheme converges as in
`mirror_waveFEM`, and `e^{tL}` is unitary while `Re` is a contraction
(`sq_norm_rowsW1L_add_sq_norm_rowsW2L_le`). -/
theorem mirror_waveFEM_of_mem_tsd {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : x ∈ totalSub MirrorBGG.tsdQ) {T : ℝ} (hT0 : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop,
      ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0),
        ∀ t ∈ Icc 0 T, √(‖(sh.σ t : TU0)‖ ^ 2 +
          ‖rowsW1L (stEL (MirrorBGG.complexQ.waveGroup.S t x)) - bIncl1 (sh.u t : BU1)‖ ^ 2 +
          ‖(sh.M t : W2)‖ ^ 2 +
          ‖rowsW2L (stBL (MirrorBGG.complexQ.waveGroup.S t x)) - (sh.ρ t : Wv W2)‖ ^ 2) ≤ ε := by
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1
    (MirrorBGG.complexQ.isSkewAdjoint_wave.subset_closure_domainSq_inf
      MirrorBGG.reducingSubcomplexQ.isReducing_wave hx) (ε / 2) (half_pos hε)
  obtain ⟨hy1, hy2⟩ := LinearPMap.mem_domainSq.1 hy.1
  set D : TSDDatum := ⟨y, hy1, hy2, hy.2⟩
  have hmult : ∀ t ∈ Icc 0 T, ∀ μ : TU1, |(D.exactWave T).ℓ t μ| ≤ 0 * ‖μ‖ ∧
      |(D.exactWave T).ℓ' t μ| ≤ 0 * ‖μ‖ := fun t _ μ =>
    ⟨by simp [TSDDatum.exactWave], by simp [TSDDatum.exactWave]⟩
  filter_upwards [mirrorWave_converges hT hB hT0 continuousOn_const (D.exactWave T) le_rfl
    hmult (half_pos hε)] with N hN
  obtain ⟨sh, -, hsh⟩ := hN
  refine ⟨sh, fun t ht => ?_⟩
  -- the states as energy vectors
  set ι := Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2)
  have hι : ∀ a b, ‖ι a - ι b‖ = √(‖a.1 - b.1‖ ^ 2 + ‖a.2.1 - b.2.1‖ ^ 2 +
      ‖a.2.2.1 - b.2.2.1‖ ^ 2 + ‖a.2.2.2 - b.2.2.2‖ ^ 2) :=
    Feec.BGG.Discrete.norm_sub_of_isEnergyEmbedding Feec.BGG.isEnergyEmbedding_energyEmb
  set S := MirrorBGG.complexQ.waveGroup.S t
  have hH : ∀ z : PiLp 2 MirrorBGG.SpaceQ,
      ‖ι (0, rowsW1L (stEL z), 0, rowsW2L (stBL z)) - ι (((sh.σ t : TU0) : W0),
        bIncl1 (sh.u t : BU1), (sh.M t : W2), (sh.ρ t : Wv W2))‖ =
      √(‖(sh.σ t : TU0)‖ ^ 2 + ‖rowsW1L (stEL z) - bIncl1 (sh.u t : BU1)‖ ^ 2 +
        ‖(sh.M t : W2)‖ ^ 2 + ‖rowsW2L (stBL z) - (sh.ρ t : Wv W2)‖ ^ 2) := fun z => by
    rw [hι]
    simp only [zero_sub, norm_neg]
    rfl
  have ey : √(‖(sh.σ t : TU0)‖ ^ 2 + ‖rowsW1L (stEL (S y)) - bIncl1 (sh.u t : BU1)‖ ^ 2 +
      ‖(sh.M t : W2)‖ ^ 2 + ‖rowsW2L (stBL (S y)) - (sh.ρ t : Wv W2)‖ ^ 2) ≤ ε / 2 :=
    sqrt_four_congr (hsh t ht) (norm_zero_sub' _)
      (D.norm_exactWave_u_sub (fun _ _ => rfl) ht _) (norm_zero_sub' _)
      (D.norm_exactWave_ρ_sub (fun _ _ => rfl) ht _)
  have exy : ‖ι (0, rowsW1L (stEL (S x)), 0, rowsW2L (stBL (S x))) -
      ι (0, rowsW1L (stEL (S y)), 0, rowsW2L (stBL (S y)))‖ ≤ ‖x - y‖ := by
    have e1 : rowsW1L (stEL (S x)) - rowsW1L (stEL (S y)) = rowsW1L (stEL (S (x - y))) := by
      rw [map_sub S, map_sub stEL, map_sub rowsW1L]
    have e2 : rowsW2L (stBL (S x)) - rowsW2L (stBL (S y)) = rowsW2L (stBL (S (x - y))) := by
      rw [map_sub S, map_sub stBL, map_sub rowsW2L]
    rw [hι, ← MirrorBGG.complexQ.isIsometric_waveGroup t (x - y)]
    simp only [sub_self, norm_zero, e1, e2]
    calc _ ≤ √(‖S (x - y)‖ ^ 2) := Real.sqrt_le_sqrt (by
          nlinarith [sq_norm_rowsW1L_add_sq_norm_rowsW2L_le (S (x - y))])
      _ = ‖S (x - y)‖ := Real.sqrt_sq (norm_nonneg _)
  rw [← hH] at ey ⊢
  calc _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub _
        (ι (0, rowsW1L (stEL (S y)), 0, rowsW2L (stBL (S y)))) _
    _ ≤ ‖x - y‖ + ε / 2 := add_le_add exy ey
    _ ≤ ε := by rw [← dist_eq_norm]; linarith

end Main

end Feec.Models.Cube.MirrorWeakSymmetry
